// Copyright 2026 The Fuchsia Authors
//
// Licensed under a BSD-style license <LICENSE-BSD>, Apache License, Version 2.0
// <LICENSE-APACHE or https://www.apache.org/licenses/LICENSE-2.0>, or the MIT
// license <LICENSE-MIT or https://opensource.org/licenses/MIT>, at your option.
// This file may not be copied, modified, or distributed except according to
// those terms.

//! Bundled resource and theory parity, the precompiled inspector, prebuilt
//! `.olean` admission, and parallel DAG compilation.

use super::*;

#[test]
fn precompiled_inspector_cache_keys_on_inspector_source_digest() {
    let mut fix = TempFixture::isolated(Some(&format!("{HEADER}def ok : Nat := 1\n")));

    // 1. First run compiles `TrustedBoundary.lean` into `.olean` and populates
    // the in-process cache.
    fix.check_expected(None, None, None).unwrap();

    let orig_inspector = fs::read_to_string(fix.root.join("trusted/audit/TrustedBoundary.lean"))
        .expect("read staged TrustedBoundary.lean");

    // 2. A syntactically or type-invalid edit to `TrustedBoundary.lean` must
    // miss the cache and fail closed in `compile-inspector` rather than
    // reusing the cached `.olean`.
    fs::write(
        fix.root.join("trusted/audit/TrustedBoundary.lean"),
        format!("{orig_inspector}\ndef brokenInspectorType : Nat := \"not a nat\"\n"),
    )
    .unwrap();
    let err_compile =
        fix.check_expected(Some(2), Some("compile-inspector"), Some(false)).unwrap_err();
    assert!(
        err_compile.message.contains("Lean exited"),
        "expected compile-inspector failure, got: {err_compile}"
    );

    // 3. A valid edit to `TrustedBoundary.lean` that changes policy behavior
    // must recompile and execute the modified inspector rather than serving
    // stale cached `.olean` bytes.
    let needle = "  | \"preflight\" =>";
    let replacement =
        "  | \"preflight\" =>\n    throw <| IO.userError \"policy: mutated inspector sentinel\"";
    assert!(
        orig_inspector.contains(needle),
        "expected preflight dispatch arm in TrustedBoundary.lean"
    );
    fs::write(
        fix.root.join("trusted/audit/TrustedBoundary.lean"),
        orig_inspector.replacen(needle, replacement, 1),
    )
    .unwrap();
    let err_policy = fix.check_expected(Some(1), Some("preflight"), Some(false)).unwrap_err();
    assert!(
        err_policy.message.contains("mutated inspector sentinel"),
        "expected modified inspector policy error, got: {err_policy}"
    );
}

#[cfg(unix)]
#[test]
fn precompiled_inspector_handles_colon_in_tmpdir_and_drops_lean_path() {
    let fix = TempFixture::isolated(Some(&format!("{HEADER}def ok : Nat := 1\n")));

    // Construct a `TMPDIR` containing the Unix `LEAN_PATH` delimiter (`:`) and
    // place a corrupt decoy `TrustedBoundary.olean` at the split prefix so any
    // non-relative `LEAN_PATH` serialization fails immediately.
    let outer = tempfile::Builder::new().prefix("anneal-colon-tmp-").tempdir().unwrap();
    let split_prefix = outer.path().join("evil");
    fs::create_dir_all(&split_prefix).unwrap();
    fs::write(split_prefix.join("TrustedBoundary.olean"), b"corrupt-decoy").unwrap();
    let colon_tmpdir = outer.path().join("evil:sub");
    fs::create_dir_all(&colon_tmpdir).unwrap();

    // Run `anneal-audit` in a child process with `TMPDIR=<outer>/evil:sub`
    // (avoiding mutating the test binary's global `TMPDIR`) and verify the
    // relative `LEAN_PATH="control"` succeeds without touching the decoy.
    // Note: `TempFixture` omits `Trusted.MirAst`/`Anneal.MirWp`, so the binary
    // executes `"preflight"`, compiles `Trusted.lean`, and reaches `"audit"`
    // cleanly before `require_mir_wp` checks MIR modules; reaching the
    // `"audit"` phase proves both preflight and audit inspector runs succeeded
    // under the colon-containing `TMPDIR`.
    let lean = default_lean_path();
    let output = Command::new(env!("CARGO_BIN_EXE_anneal-audit-test-bin"))
        .arg("--anneal-root")
        .arg(&fix.root)
        .arg("--lean")
        .arg(&lean)
        .env("TMPDIR", &colon_tmpdir)
        .output()
        .expect("run anneal-audit with colon TMPDIR");
    let combined = format!(
        "{}\n{}",
        String::from_utf8_lossy(&output.stdout),
        String::from_utf8_lossy(&output.stderr)
    );
    assert!(
        combined.contains("Trusted check failed (audit):") || output.status.success(),
        "expected inspector preflight+audit to run under colon TMPDIR, got {:?}: {combined}",
        output.status.code()
    );
    assert!(
        !combined.contains("unknown module prefix 'TrustedBoundary'")
            && !combined.contains("corrupt-decoy"),
        "colon TMPDIR must not split LEAN_PATH or read decoy prefix: {combined}"
    );

    // Part 2: verify `TrustedBoundary.initHermeticSearchPath` drops the
    // bootstrap `LEAN_PATH="control"` from `Lean.searchPathRef` before
    // `importCorrEnv` loads modules, so `control/TrustedBoundary.olean` is
    // never visible as an importable module.
    let mut checker = fix.checker_with_lean(Some(&lean));
    checker.set_require_mir_wp(false);
    checker.run().unwrap();
    let sysroot = checker.admitted().unwrap().prefix.clone();
    let req_path = checker.stage().join("drop-lean-path-req.json");
    let res_path = checker.stage().join("drop-lean-path-res.json");
    let req = json!({
        "mode": "correspondence-preflight",
        "sysroot": sysroot.to_string_lossy(),
        "searchPath": [],
        "foundation": ["TrustedBoundary"],
        "sysrootFoundation": [],
        "trusted": [],
        "theory": [],
        "vendorMiri": [],
        "moduleTiers": [],
        "sources": [],
    });
    fs::write(&req_path, serde_json::to_vec(&req).unwrap()).unwrap();
    let drop_out = Command::new(&lean)
        .current_dir(checker.stage())
        .env_clear()
        .env("LEAN_PATH", "control")
        .args([
            "-j1",
            "-M2048",
            "--run",
            checker.stage().join("control/TrustedBoundaryEntry.lean").to_str().unwrap(),
            req_path.to_str().unwrap(),
            res_path.to_str().unwrap(),
        ])
        .output()
        .expect("run precompiled inspector for initHermeticSearchPath check");
    assert_eq!(
        drop_out.status.code(),
        Some(2),
        "expected exit code 2 when initHermeticSearchPath drops LEAN_PATH: stdout={} stderr={}",
        String::from_utf8_lossy(&drop_out.stdout),
        String::from_utf8_lossy(&drop_out.stderr),
    );
    let drop_res = fs::read_to_string(&res_path).expect("read inspector result json");
    assert!(
        drop_res.contains("unknown module prefix 'TrustedBoundary'"),
        "initHermeticSearchPath must drop LEAN_PATH before importCorrEnv, got: {drop_res}"
    );
}

/// `verify_bundled_resources` accepts the real repository checkout and rejects
/// reintroduced legacy `bundled_resources.rs` or `bundled_theory.json`, any
/// checked-in `packaged/` staging directory, missing/symlinked `build.rs`,
/// `trusted_bundle.rs`, or `theory_bundle.rs`, drifted or symlinked
/// `theory/bundle-manifest.json` / `theory/` files, missing or symlinked
/// `TRUSTED_BUNDLE_SOURCES`, `THEORY_BUNDLE_MANIFEST`, and `PROVENANCE_SOURCES`
/// files and parent directories, invalid, tampered, duplicate, unsorted, or
/// out-of-tree theory manifest entries, and untracked `.lean` files under
/// `correspondence/` or `trusted/correspondence/` with policy exit code `1`.
/// Each symlink fixture points at byte-identical content, so only the
/// regular-file checks can reject it.
#[test]
fn enforces_bundled_resources_parity_and_regular_files() {
    use anneal_audit::{
        bundle::{
            LEGACY_BUNDLE_DESTINATION, LEGACY_THEORY_BUNDLE_DESTINATION,
            PACKAGED_BUNDLE_DESTINATION, PROVENANCE_SOURCES, THEORY_BUNDLE_MANIFEST,
            TRUSTED_BUNDLE_SOURCES, TheoryBundleManifest, load_theory_bundle_manifest,
            render_bundled_resources, render_bundled_theory,
        },
        verify_bundled_resources,
    };

    let checkout = repo_root();
    verify_bundled_resources(&checkout).unwrap();

    let tmp = tempfile::tempdir().unwrap();
    let root = tmp.path().join("repo");
    let (_, manifest) = load_theory_bundle_manifest(&checkout).unwrap();
    for rel in TRUSTED_BUNDLE_SOURCES
        .iter()
        .copied()
        .chain(PROVENANCE_SOURCES.iter().copied())
        .chain(std::iter::once(THEORY_BUNDLE_MANIFEST))
        .chain(manifest.modules.iter().map(|entry| entry.path.as_str()))
        .chain([
            "trusted/cargo-anneal/build.rs",
            "trusted/cargo-anneal/src/trusted_bundle.rs",
            "trusted/cargo-anneal/src/theory_bundle.rs",
        ])
    {
        let dst = root.join(rel);
        fs::create_dir_all(dst.parent().unwrap()).unwrap();
        fs::copy(checkout.join(rel), dst).unwrap();
    }
    let canonical = render_bundled_resources(&root).unwrap();
    let canonical_theory = render_bundled_theory(&root).unwrap();
    verify_bundled_resources(&root).unwrap();

    let expect_policy = |needle: &str| {
        let err = verify_bundled_resources(&root).unwrap_err();
        assert_eq!(err.code, 1, "{err}");
        assert_eq!(err.phase, "bundle-manifest", "{err}");
        assert!(err.message.contains(needle), "expected {needle:?}: {err}");
    };

    // 1. Reintroduced legacy `src/bundled_resources.rs` or
    // `src/bundled_theory.json` -> policy error.
    let legacy_dest = root.join(LEGACY_BUNDLE_DESTINATION);
    fs::write(&legacy_dest, canonical.as_bytes()).unwrap();
    expect_policy("legacy checked-in bundled_resources.rs must be absent");
    fs::remove_file(&legacy_dest).unwrap();
    let legacy_theory_dest = root.join(LEGACY_THEORY_BUNDLE_DESTINATION);
    fs::write(&legacy_theory_dest, canonical_theory.as_bytes()).unwrap();
    expect_policy("legacy checked-in bundled_theory.json must be absent");
    fs::remove_file(&legacy_theory_dest).unwrap();
    verify_bundled_resources(&root).unwrap();

    // 2. Missing or symlinked `trusted/cargo-anneal/build.rs` -> policy error.
    let build_rs = root.join("trusted/cargo-anneal/build.rs");
    let outside_build_rs = tmp.path().join("outside-build.rs");
    fs::rename(&build_rs, &outside_build_rs).unwrap();
    expect_policy("missing canonical bundle source: trusted/cargo-anneal/build.rs");
    symlink(&outside_build_rs, &build_rs).unwrap();
    expect_policy("bundle source must be a regular file");
    fs::remove_file(&build_rs).unwrap();
    fs::rename(&outside_build_rs, &build_rs).unwrap();
    verify_bundled_resources(&root).unwrap();

    // 3. Missing or symlinked `src/trusted_bundle.rs` or `src/theory_bundle.rs`
    // -> policy error.
    let trusted_bundle_rs = root.join("trusted/cargo-anneal/src/trusted_bundle.rs");
    let outside_tb_rs = tmp.path().join("outside-trusted_bundle.rs");
    fs::rename(&trusted_bundle_rs, &outside_tb_rs).unwrap();
    expect_policy("missing canonical bundle source: trusted/cargo-anneal/src/trusted_bundle.rs");
    symlink(&outside_tb_rs, &trusted_bundle_rs).unwrap();
    expect_policy("bundle source must be a regular file");
    fs::remove_file(&trusted_bundle_rs).unwrap();
    fs::rename(&outside_tb_rs, &trusted_bundle_rs).unwrap();
    let theory_bundle_rs = root.join("trusted/cargo-anneal/src/theory_bundle.rs");
    let outside_thb_rs = tmp.path().join("outside-theory_bundle.rs");
    fs::rename(&theory_bundle_rs, &outside_thb_rs).unwrap();
    expect_policy("missing canonical bundle source: trusted/cargo-anneal/src/theory_bundle.rs");
    symlink(&outside_thb_rs, &theory_bundle_rs).unwrap();
    expect_policy("bundle source must be a regular file");
    fs::remove_file(&theory_bundle_rs).unwrap();
    fs::rename(&outside_thb_rs, &theory_bundle_rs).unwrap();
    verify_bundled_resources(&root).unwrap();

    // 4. Checked-in transient `packaged/` staging dir -> policy error.
    let pkg_dest = root.join(PACKAGED_BUNDLE_DESTINATION);
    let pkg_dir = pkg_dest.parent().unwrap().to_path_buf();
    fs::create_dir_all(&pkg_dir).unwrap();
    fs::write(&pkg_dest, canonical.as_bytes()).unwrap();
    expect_policy("transient packaged/ staging directory must not be checked in");
    fs::remove_dir_all(&pkg_dir).unwrap();
    let outside_pkg_dir = tmp.path().join("outside-packaged");
    fs::create_dir_all(&outside_pkg_dir).unwrap();
    fs::write(outside_pkg_dir.join("bundled_resources.rs"), canonical.as_bytes()).unwrap();
    symlink(&outside_pkg_dir, &pkg_dir).unwrap();
    expect_policy("transient packaged/ staging directory must not be checked in");
    fs::remove_file(&pkg_dir).unwrap();
    verify_bundled_resources(&root).unwrap();

    // 5. Symlinked theory source file -> policy rejection (code 1).
    let source = root.join("theory/Anneal/MirWp.lean");
    let outside_source = tmp.path().join("outside-MirWp.lean");
    fs::rename(&source, &outside_source).unwrap();
    symlink(&outside_source, &source).unwrap();
    expect_policy("bundle source must be a regular file");
    fs::remove_file(&source).unwrap();
    fs::rename(&outside_source, &source).unwrap();
    verify_bundled_resources(&root).unwrap();

    // 6. Symlinked parent directory of a theory source file -> policy
    // rejection (code 1).
    let source_dir = root.join("theory/Anneal");
    let outside_source_dir = tmp.path().join("outside-Anneal");
    fs::rename(&source_dir, &outside_source_dir).unwrap();
    symlink(&outside_source_dir, &source_dir).unwrap();
    expect_policy("bundle source parent must be a regular directory");
    fs::remove_file(&source_dir).unwrap();
    fs::rename(&outside_source_dir, &source_dir).unwrap();
    verify_bundled_resources(&root).unwrap();

    // 7. Missing theory source file -> policy rejection (code 1).
    fs::remove_file(&source).unwrap();
    expect_policy("missing canonical bundle source: theory/Anneal/MirWp.lean");
    fs::copy(checkout.join("theory/Anneal/MirWp.lean"), &source).unwrap();
    verify_bundled_resources(&root).unwrap();

    // 8. Symlinked `PROVENANCE_SOURCES` file -> policy rejection (code 1).
    let prov = root.join("trusted/correspondence/Trusted/Correspondence.lean");
    let outside_prov = tmp.path().join("outside-Correspondence.lean");
    fs::rename(&prov, &outside_prov).unwrap();
    symlink(&outside_prov, &prov).unwrap();
    expect_policy("bundle source must be a regular file");
    fs::remove_file(&prov).unwrap();
    fs::rename(&outside_prov, &prov).unwrap();
    verify_bundled_resources(&root).unwrap();

    // 9. Extra untracked `.lean` file in `correspondence/` -> policy rejection
    // (code 1) so Pass 2 certified files cannot silently drift out of the
    // provenance inventory.
    let extra_corr = root.join("correspondence/Anneal/ExtraProof.lean");
    fs::write(&extra_corr, b"prelude\n").unwrap();
    expect_policy("correspondence provenance inventory mismatch");
    fs::remove_file(&extra_corr).unwrap();
    verify_bundled_resources(&root).unwrap();

    // 10. Extra untracked `.lean` file in `trusted/correspondence/` -> policy
    // rejection (code 1).
    let extra_trusted_corr = root.join("trusted/correspondence/Trusted/ExtraAdapter.lean");
    fs::write(&extra_trusted_corr, b"prelude\n").unwrap();
    expect_policy("correspondence provenance inventory mismatch");
    fs::remove_file(&extra_trusted_corr).unwrap();
    verify_bundled_resources(&root).unwrap();

    // 11. Drifted theory source + manifest vs compiled-in
    // `EMBEDDED_THEORY_BUNDLE_JSON` -> policy rejection (code 1).
    let manifest_path = root.join(THEORY_BUNDLE_MANIFEST);
    let original_manifest_bytes = fs::read(&manifest_path).unwrap();
    let orig_mir_wp = fs::read(&source).unwrap();
    let drifted_mir_wp = format!("{}\n-- drifted\n", String::from_utf8_lossy(&orig_mir_wp));
    fs::write(&source, drifted_mir_wp.as_bytes()).unwrap();
    let mut drifted_manifest = manifest.clone();
    drifted_manifest
        .modules
        .iter_mut()
        .find(|m| m.path == "theory/Anneal/MirWp.lean")
        .unwrap()
        .sha256 = sha256_bytes(drifted_mir_wp.as_bytes());
    fs::write(
        &manifest_path,
        format!("{}\n", serde_json::to_string_pretty(&drifted_manifest).unwrap()),
    )
    .unwrap();
    expect_policy("embedded cargo-anneal EMBEDDED_THEORY_BUNDLE_JSON differs");
    fs::write(&source, &orig_mir_wp).unwrap();
    fs::write(&manifest_path, &original_manifest_bytes).unwrap();
    verify_bundled_resources(&root).unwrap();

    // 12. Theory manifest fail-closed rejections: tampered hash, duplicate
    // entry, unsorted entry, out-of-tree / path-traversal / umbrella paths,
    // missing required `MirWp.lean`, unknown JSON field, wrong schema, symlink,
    // and missing manifest.
    let write_manifest = |m: &TheoryBundleManifest| {
        fs::write(&manifest_path, format!("{}\n", serde_json::to_string_pretty(m).unwrap()))
            .unwrap();
    };

    let mut bad_hash = manifest.clone();
    bad_hash.modules[0].sha256 = "0".repeat(64);
    write_manifest(&bad_hash);
    expect_policy("theory bundle manifest SHA-256 mismatch");

    let mut dup = manifest.clone();
    let first = dup.modules[0].clone();
    dup.modules.push(first);
    write_manifest(&dup);
    expect_policy("duplicate theory bundle path");

    let mut unsorted = manifest.clone();
    unsorted.modules.swap(0, 1);
    write_manifest(&unsorted);
    expect_policy("unsorted theory bundle entry");

    let mut out_of_tree = manifest.clone();
    out_of_tree.modules[0].path = "trusted/lean/Trusted.lean".to_owned();
    write_manifest(&out_of_tree);
    expect_policy("must reside under theory/Anneal/");

    let mut traversal = manifest.clone();
    traversal.modules[0].path = "theory/Anneal/../Trusted.lean".to_owned();
    write_manifest(&traversal);
    expect_policy("invalid relative theory bundle path");

    let mut umbrella = manifest.clone();
    umbrella.modules[0].path = "theory/Anneal.lean".to_owned();
    write_manifest(&umbrella);
    expect_policy("must name a module under theory/Anneal/");

    let mut missing_mir_wp = manifest.clone();
    missing_mir_wp.modules.retain(|entry| entry.path != "theory/Anneal/MirWp.lean");
    write_manifest(&missing_mir_wp);
    expect_policy("missing required theory module: theory/Anneal/MirWp.lean");

    let mut wrong_schema = manifest.clone();
    wrong_schema.schema_version = 2;
    write_manifest(&wrong_schema);
    expect_policy("unsupported schema_version 2");

    fs::write(&manifest_path, b"{\"schema_version\": 1, \"modules\": [], \"extra\": true}\n")
        .unwrap();
    expect_policy("malformed theory/bundle-manifest.json");

    fs::remove_file(&manifest_path).unwrap();
    expect_policy("missing canonical bundle source: theory/bundle-manifest.json");

    let outside_manifest = tmp.path().join("outside-manifest.json");
    fs::write(&outside_manifest, &original_manifest_bytes).unwrap();
    symlink(&outside_manifest, &manifest_path).unwrap();
    expect_policy("bundle source must be a regular file");
    fs::remove_file(&manifest_path).unwrap();
    fs::write(&manifest_path, &original_manifest_bytes).unwrap();
    verify_bundled_resources(&root).unwrap();

    // 13. Drifted canonical trusted source vs compiled-in `cargo_anneal`
    // bundle -> policy rejection (code 1). Pass 2 provenance sources are not
    // compiled into `cargo-anneal`, so editing them does not.
    let trusted_entry = root.join("trusted/lean/Trusted.lean");
    let orig_trusted_entry = fs::read(&trusted_entry).unwrap();
    let drifted_entry = format!("{}\n-- drifted\n", String::from_utf8_lossy(&orig_trusted_entry));
    fs::write(&trusted_entry, drifted_entry).unwrap();
    expect_policy("embedded cargo-anneal BUNDLE entry trusted/lean/Trusted.lean differs");
    fs::write(&trusted_entry, &orig_trusted_entry).unwrap();
    verify_bundled_resources(&root).unwrap();

    let orig_prov = fs::read(&prov).unwrap();
    fs::write(&prov, format!("{}\n-- drifted\n", String::from_utf8_lossy(&orig_prov))).unwrap();
    verify_bundled_resources(&root).unwrap();
    fs::write(&prov, &orig_prov).unwrap();
    verify_bundled_resources(&root).unwrap();

    // 14. Missing `PROVENANCE_SOURCES` file -> policy rejection (code 1).
    fs::remove_file(&prov).unwrap();
    expect_policy(
        "missing canonical bundle source: trusted/correspondence/Trusted/Correspondence.lean",
    );
}

/// `anneal-audit` rejects a checkout from which `trusted/cargo-anneal/build.rs`
/// was deleted, and `check_cargo_boundary` still rejects `package.build` in
/// `trusted/cargo-anneal` and `build.rs` in all other workspace members.
#[test]
fn rejects_deleted_build_generator_and_disallowed_build_scripts() {
    use anneal_audit::check_cargo_boundary;

    let checkout = repo_root();
    let fix = TempFixture::new(None);
    copy_cargo_workspace(&fix.root);
    copy_dir_all(&checkout.join("vendor/lean-miri"), &fix.root.join("vendor/lean-miri")).unwrap();

    // Deleting `trusted/cargo-anneal/build.rs` fails `Checker::run`.
    let build_rs_path = fix.root.join("trusted/cargo-anneal/build.rs");
    let outside_dir = tempfile::tempdir().unwrap();
    let outside_build_rs = outside_dir.path().join("build.rs");
    fs::copy(&build_rs_path, &outside_build_rs).unwrap();
    fs::remove_file(&build_rs_path).unwrap();
    let mut checker = fix.checker();
    let err = checker.run().unwrap_err();
    assert_eq!(err.code, 1, "unexpected code: {err}");
    assert_eq!(err.phase, "cargo-boundary", "unexpected phase: {err}");
    assert!(
        err.message.contains("missing required build script trusted/cargo-anneal/build.rs"),
        "unexpected error: {err}"
    );
    assert!(!checker.execution_began());

    // Symlinked or directory `trusted/cargo-anneal/build.rs` also fails with
    // policy code 1 in `check_cargo_boundary`.
    symlink(&outside_build_rs, &build_rs_path).unwrap();
    let err_symlink = check_cargo_boundary(&fix.root).unwrap_err();
    assert_eq!(err_symlink.code, 1, "{err_symlink}");
    assert!(
        err_symlink.message.contains("build script must be a regular file"),
        "{err_symlink}"
    );
    fs::remove_file(&build_rs_path).unwrap();

    fs::create_dir(&build_rs_path).unwrap();
    let err_dir = check_cargo_boundary(&fix.root).unwrap_err();
    assert_eq!(err_dir.code, 1, "{err_dir}");
    assert!(
        err_dir.message.contains("build script must be a regular file"),
        "{err_dir}"
    );
    fs::remove_dir(&build_rs_path).unwrap();

    // Restore `build.rs`, then confirm `package.build` in `cargo-anneal` and
    // `build.rs` in `trusted/audit` are still rejected.
    fs::copy(&outside_build_rs, &build_rs_path).unwrap();
    check_cargo_boundary(&fix.root).unwrap();

    let cargo_anneal_toml = fix.root.join("trusted/cargo-anneal/Cargo.toml");
    let orig_toml = fs::read_to_string(&cargo_anneal_toml).unwrap();
    fs::write(
        &cargo_anneal_toml,
        orig_toml.replace("edition = \"2024\"\n", "edition = \"2024\"\nbuild = \"build.rs\"\n"),
    )
    .unwrap();
    let err_pkg_build = check_cargo_boundary(&fix.root).unwrap_err();
    assert_eq!(err_pkg_build.code, 1);
    assert!(err_pkg_build.message.contains("disallowed package.build"), "{err_pkg_build}");
    fs::write(&cargo_anneal_toml, orig_toml).unwrap();

    fs::write(fix.root.join("trusted/audit/build.rs"), b"fn main() {}\n").unwrap();
    let err_audit_build = check_cargo_boundary(&fix.root).unwrap_err();
    assert_eq!(err_audit_build.code, 1);
    assert!(
        err_audit_build.message.contains("disallowed build script trusted/audit/build.rs"),
        "{err_audit_build}"
    );
    fs::remove_file(fix.root.join("trusted/audit/build.rs")).unwrap();
}

/// `scan_lean_tree` admits `theory/bundle-manifest.json` without requiring a
/// monolithic `theory/Anneal.lean` umbrella (while still admitting synthetic
/// `theory/Anneal.lean` fixtures, rejecting any other non-Lean file in
/// `theory/` or `bundle-manifest.json` in `trusted/lean/`, and requiring
/// `Trusted.lean` in `trusted/lean/`), while `Checker::run` fails closed if
/// `theory/bundle-manifest.json` is deleted or legacy `src/bundled_theory.json`
/// is reintroduced.
#[test]
fn admits_only_theory_bundle_manifest_and_rejects_deleted_theory_bundle() {
    use anneal_audit::scan_lean_tree;

    let checkout = repo_root();
    let theory_mods = scan_lean_tree(&checkout.join("theory"), "Anneal").unwrap();
    assert!(!theory_mods.contains_key("Anneal"));
    assert!(theory_mods.contains_key("Anneal.Scalar"));
    assert!(theory_mods.contains_key("Anneal.Wp"));
    assert!(theory_mods.contains_key("Anneal.MirWp"));

    let tmp = tempfile::tempdir().unwrap();
    let theory_root = tmp.path().join("theory");
    fs::create_dir_all(theory_root.join("Anneal")).unwrap();
    fs::write(theory_root.join("Anneal/Scalar.lean"), b"prelude\n").unwrap();
    fs::write(theory_root.join("bundle-manifest.json"), b"{}\n").unwrap();
    let no_umbrella_mods = scan_lean_tree(&theory_root, "Anneal").unwrap();
    assert!(!no_umbrella_mods.contains_key("Anneal"));
    assert!(no_umbrella_mods.contains_key("Anneal.Scalar"));
    fs::write(theory_root.join("Anneal.lean"), b"prelude\n").unwrap();
    let with_umbrella_mods = scan_lean_tree(&theory_root, "Anneal").unwrap();
    assert!(with_umbrella_mods.contains_key("Anneal"));

    fs::write(theory_root.join("other.json"), b"{}\n").unwrap();
    let err = scan_lean_tree(&theory_root, "Anneal").unwrap_err();
    assert_eq!(err.code, 1, "{err}");
    assert_eq!(err.phase, "snapshot", "{err}");
    assert!(err.message.contains("unexpected non-Lean file in source tree: other.json"), "{err}");

    let trusted_root = tmp.path().join("trusted_lean");
    fs::create_dir_all(&trusted_root).unwrap();
    fs::write(trusted_root.join("Trusted.lean"), HEADER).unwrap();
    fs::write(trusted_root.join("bundle-manifest.json"), b"{}\n").unwrap();
    let err = scan_lean_tree(&trusted_root, "Trusted").unwrap_err();
    assert_eq!(err.code, 1, "{err}");
    assert_eq!(err.phase, "snapshot", "{err}");
    assert!(
        err.message.contains("unexpected non-Lean file in source tree: bundle-manifest.json"),
        "{err}"
    );

    let no_trusted_umbrella = tmp.path().join("trusted_lean_no_umbrella");
    fs::create_dir_all(no_trusted_umbrella.join("Trusted")).unwrap();
    fs::write(no_trusted_umbrella.join("Trusted/MirAst.lean"), HEADER).unwrap();
    let err = scan_lean_tree(&no_trusted_umbrella, "Trusted").unwrap_err();
    assert_eq!(err.code, 1, "{err}");
    assert_eq!(err.phase, "snapshot", "{err}");
    assert!(err.message.contains("missing Trusted.lean umbrella"), "{err}");

    let fix = TempFixture::new(None);
    copy_cargo_workspace(&fix.root);
    copy_dir_all(&checkout.join("vendor/lean-miri"), &fix.root.join("vendor/lean-miri")).unwrap();
    for rel in anneal_audit::bundle::TRUSTED_BUNDLE_SOURCES
        .iter()
        .copied()
        .chain(anneal_audit::bundle::PROVENANCE_SOURCES.iter().copied())
    {
        let dst = fix.root.join(rel);
        fs::create_dir_all(dst.parent().unwrap()).unwrap();
        fs::copy(checkout.join(rel), dst).unwrap();
    }
    fs::create_dir_all(fix.root.join("theory")).unwrap();

    let mut checker = fix.checker();
    let err = checker.run().unwrap_err();
    assert_eq!(err.code, 1, "unexpected code: {err}");
    assert_eq!(err.phase, "bundle-manifest", "unexpected phase: {err}");
    assert!(
        err.message.contains("missing canonical bundle source: theory/bundle-manifest.json"),
        "unexpected error: {err}"
    );
    assert!(!checker.execution_began());

    fs::write(
        fix.root.join(anneal_audit::bundle::LEGACY_THEORY_BUNDLE_DESTINATION),
        b"{}\n",
    )
    .unwrap();
    let mut checker_legacy = Checker::new(&fix.root, None).unwrap();
    let err_legacy = checker_legacy.run().unwrap_err();
    assert_eq!(err_legacy.code, 1, "unexpected code: {err_legacy}");
    assert_eq!(err_legacy.phase, "bundle-manifest", "unexpected phase: {err_legacy}");
    assert!(
        err_legacy.message.contains("legacy checked-in bundled_theory.json must be absent"),
        "unexpected error: {err_legacy}"
    );
    assert!(!checker_legacy.execution_began());
}

/// Verifies multi-module parallel DAG compilation in
/// [`Checker::verify_and_stage_miri_entries`]:
/// 1. A 4-module diamond DAG (`Miri.DagRoot -> {Miri.DagLeft, Miri.DagRight}
///    -> Miri.DagTop`) compiles cold across workers, verifies digests, stages
///    into `miri-lib`, populates `miri_cache_dir`, and preserves transitive
///    ordering when an intermediate module (`Miri.DagLeft`/`Miri.DagRight`)
///    hits the cache while `Miri.DagRoot` and `Miri.DagTop` miss.
/// 2. When multiple modules fail concurrently (a dependent module at index 1
///    and an independent root at index 2), the earliest closure index's failure
///    is reported deterministically and dependent indices (`Miri.DagTop`) are
///    neither staged nor cached.
/// 3. Cyclic `Miri.*` imports (including cycles traversing a cached module) and
///    duplicate closure modules fail closed with policy exit code `1` before
///    compiling.
#[cfg(target_os = "linux")]
#[test]
fn compiles_cold_miri_closure_dag_in_parallel_and_preserves_failure_order() {
    let fix = TempFixture::new(None);
    let vendor_dir = fix.root.join("dag-vendor");
    fs::create_dir_all(vendor_dir.join("Miri")).unwrap();

    let dag_sources_raw = [
        (
            "Miri.DagRoot",
            "Miri/DagRoot.lean",
            "prelude\nimport Init.Prelude\nnamespace Miri.DagRoot\ndef r : Nat := 1\nend Miri.DagRoot\n",
        ),
        (
            "Miri.DagLeft",
            "Miri/DagLeft.lean",
            "prelude\nimport Miri.DagRoot\nnamespace Miri.DagLeft\ndef l : Nat := Miri.DagRoot.r\nend Miri.DagLeft\n",
        ),
        (
            "Miri.DagRight",
            "Miri/DagRight.lean",
            "prelude\nimport Miri.DagRoot\nnamespace Miri.DagRight\ndef rg : Nat := Miri.DagRoot.r\nend Miri.DagRight\n",
        ),
        (
            "Miri.DagTop",
            "Miri/DagTop.lean",
            "prelude\nimport Miri.DagLeft\nimport Miri.DagRight\nnamespace Miri.DagTop\ndef t : Nat := Miri.DagLeft.l\nend Miri.DagTop\n",
        ),
    ];

    let mut expected_sources = BTreeMap::new();
    for (_, rel, src) in &dag_sources_raw {
        fs::write(vendor_dir.join(rel), src).unwrap();
        expected_sources.insert((*rel).to_string(), sha256_bytes(src.as_bytes()));
    }

    let mut probe = fix.checker();
    probe.set_require_mir_wp(false);
    probe.run().unwrap();
    let probe_lib = probe.stage().join("dag-probe-lib");
    fs::create_dir_all(probe_lib.join("Miri")).unwrap();
    let mut entries = Vec::new();
    for (module, rel, _) in &dag_sources_raw {
        let out_olean = probe_lib.join(format!("{}.olean", module.replace('.', "/")));
        probe
            .process_with_path(
                &format!("probe-{module}"),
                &[
                    "-j1".to_string(),
                    "-M2048".to_string(),
                    "-t0".to_string(),
                    "-DElab.async=false".to_string(),
                    "-Ddebug.skipKernelTC=false".to_string(),
                    "-R".to_string(),
                    vendor_dir.to_string_lossy().into_owned(),
                    "-o".to_string(),
                    out_olean.to_string_lossy().into_owned(),
                    vendor_dir.join(rel).to_string_lossy().into_owned(),
                ],
                Some(probe_lib.as_os_str()),
            )
            .unwrap();
        entries.push(MiriClosureEntry {
            module: (*module).to_string(),
            path: (*rel).to_string(),
            olean_sha256: sha256_file(&out_olean, "test").unwrap(),
            olean_server_sha256: None,
            olean_private_sha256: None,
        });
    }

    // 1. Cold parallel DAG compilation succeeds and populates the cache.
    let cache_tmp = tempfile::Builder::new().prefix("anneal-dag-cache-").tempdir().unwrap();
    let cache_dir = cache_tmp.path().join("miri-cache");
    let mut c1 = fix.checker();
    c1.set_require_mir_wp(false);
    c1.set_miri_cache_dir(Some(cache_dir.clone()));
    c1.run().unwrap();
    let miri_lib =
        c1.verify_and_stage_miri_entries(&vendor_dir, &entries, &expected_sources).unwrap();
    for entry in &entries {
        let rel_olean = format!("{}.olean", entry.module.replace('.', "/"));
        assert_eq!(sha256_file(&miri_lib.join(&rel_olean), "test").unwrap(), entry.olean_sha256);
        assert_eq!(sha256_file(&cache_dir.join(&rel_olean), "test").unwrap(), entry.olean_sha256);
    }

    // 1b. Partial cache hit where intermediate modules (`Miri.DagLeft` and
    // `Miri.DagRight`) hit `cache_dir` while `Miri.DagRoot` and `Miri.DagTop`
    // (which does NOT directly import `Miri.DagRoot`) miss: `Miri.DagTop` must
    // still wait for `Miri.DagRoot` to compile and stage into `miri-lib`.
    fs::remove_file(cache_dir.join("Miri/DagRoot.olean")).unwrap();
    fs::remove_file(cache_dir.join("Miri/DagTop.olean")).unwrap();
    let mut c1_partial = fix.checker();
    c1_partial.set_require_mir_wp(false);
    c1_partial.set_miri_cache_dir(Some(cache_dir.clone()));
    c1_partial.run().unwrap();
    let partial_lib =
        c1_partial.verify_and_stage_miri_entries(&vendor_dir, &entries, &expected_sources).unwrap();
    for entry in &entries {
        let rel_olean = format!("{}.olean", entry.module.replace('.', "/"));
        assert_eq!(sha256_file(&partial_lib.join(&rel_olean), "test").unwrap(), entry.olean_sha256);
        assert_eq!(sha256_file(&cache_dir.join(&rel_olean), "test").unwrap(), entry.olean_sha256);
    }

    // 2. Concurrent multi-failure preserves deterministic earliest-index order:
    // index 1 (`Miri.DagLeft`, blocked behind `Miri.DagRoot`) and index 2 (an
    // independent root with a bad digest that finishes immediately) both fail;
    // index 1's failure must win and index 3 (`Miri.DagTop`) must not stage.
    let mut race_entries = vec![
        entries[0].clone(),
        MiriClosureEntry { olean_sha256: "0".repeat(64), ..entries[1].clone() },
        MiriClosureEntry { olean_sha256: "f".repeat(64), ..entries[2].clone() },
        entries[3].clone(),
    ];
    let ind_src = "prelude\nimport Init.Prelude\nnamespace Miri.DagRight\ndef rg : Nat := 1\nend Miri.DagRight\n";
    let race_vendor = fix.root.join("dag-race-vendor");
    copy_dir_all(&vendor_dir, &race_vendor).unwrap();
    fs::write(race_vendor.join("Miri/DagRight.lean"), ind_src).unwrap();
    let mut race_sources = expected_sources.clone();
    race_sources.insert("Miri/DagRight.lean".to_string(), sha256_bytes(ind_src.as_bytes()));
    let race_cache = cache_tmp.path().join("race-cache");
    let mut c2 = fix.checker();
    c2.set_require_mir_wp(false);
    c2.set_miri_cache_dir(Some(race_cache.clone()));
    c2.run().unwrap();
    let err_race =
        c2.verify_and_stage_miri_entries(&race_vendor, &race_entries, &race_sources).unwrap_err();
    assert_eq!(err_race.code, 1, "expected policy mismatch: {err_race}");
    assert!(
        err_race.message.contains("compiled Miri .olean SHA-256 mismatch for Miri.DagLeft"),
        "expected earliest index failure (Miri.DagLeft), got: {err_race}"
    );
    assert!(!race_cache.join("Miri/DagTop.olean").exists());

    // 2b. Non-topological `entries` slice (`Miri.DagLeft` at index 0 depending
    // on valid `Miri.DagRoot` at index 2, with independent failing root
    // `Miri.DagRight` at index 1): `min_cold_descendant` ensures `Miri.DagRoot`
    // is never pruned as "beaten" by index 1, so index 0's failure still wins.
    let non_topo_entries = [
        MiriClosureEntry { olean_sha256: "0".repeat(64), ..entries[1].clone() },
        MiriClosureEntry { olean_sha256: "f".repeat(64), ..entries[2].clone() },
        entries[0].clone(),
    ];
    let mut c2_nontopo = fix.checker();
    c2_nontopo.set_require_mir_wp(false);
    c2_nontopo.run().unwrap();
    let err_nontopo = c2_nontopo
        .verify_and_stage_miri_entries(&race_vendor, &non_topo_entries, &race_sources)
        .unwrap_err();
    assert_eq!(err_nontopo.code, 1, "expected policy mismatch: {err_nontopo}");
    assert!(
        err_nontopo.message.contains("compiled Miri .olean SHA-256 mismatch for Miri.DagLeft"),
        "expected index 0 failure (Miri.DagLeft) on non-topological slice, got: {err_nontopo}"
    );

    // Duplicate module entries fail closed with policy exit code `1`.
    race_entries[2] = race_entries[0].clone();
    let mut c_dup = fix.checker();
    c_dup.set_require_mir_wp(false);
    c_dup.run().unwrap();
    let err_dup = c_dup
        .verify_and_stage_miri_entries(&race_vendor, &race_entries, &race_sources)
        .unwrap_err();
    assert_eq!(err_dup.code, 1);
    assert!(err_dup.message.contains("duplicate Miri closure module Miri.DagRoot"));

    // 3. Cold `Miri.*` import cycles fail closed with policy exit code `1`.
    let cyc_vendor = fix.root.join("dag-cycle-vendor");
    fs::create_dir_all(cyc_vendor.join("Miri")).unwrap();
    let cyc_a = "prelude\nimport Miri.CycB\n";
    let cyc_b = "prelude\nimport Miri.CycA\n";
    fs::write(cyc_vendor.join("Miri/CycA.lean"), cyc_a).unwrap();
    fs::write(cyc_vendor.join("Miri/CycB.lean"), cyc_b).unwrap();
    let cyc_sources = BTreeMap::from([
        ("Miri/CycA.lean".to_string(), sha256_bytes(cyc_a.as_bytes())),
        ("Miri/CycB.lean".to_string(), sha256_bytes(cyc_b.as_bytes())),
    ]);
    let cyc_entries = [
        MiriClosureEntry {
            module: "Miri.CycA".to_string(),
            path: "Miri/CycA.lean".to_string(),
            olean_sha256: "0".repeat(64),
            olean_server_sha256: None,
            olean_private_sha256: None,
        },
        MiriClosureEntry {
            module: "Miri.CycB".to_string(),
            path: "Miri/CycB.lean".to_string(),
            olean_sha256: "0".repeat(64),
            olean_server_sha256: None,
            olean_private_sha256: None,
        },
    ];
    let mut c3 = fix.checker();
    c3.set_require_mir_wp(false);
    c3.run().unwrap();
    let err_cyc =
        c3.verify_and_stage_miri_entries(&cyc_vendor, &cyc_entries, &cyc_sources).unwrap_err();
    assert_eq!(err_cyc.code, 1, "expected policy cycle rejection: {err_cyc}");
    assert!(
        err_cyc.message.contains("import cycle in Miri closure modules"),
        "unexpected cycle error: {err_cyc}"
    );

    // 3b. Import cycle traversing cached intermediate modules even when only a
    // single module (`Miri.DagRoot`, rewritten to import `Miri.DagTop`) misses
    // `cache_dir` (`cold_indices.len() == 1`) fails closed with policy exit
    // code `1` before compiling.
    let cyc_cached_vendor = fix.root.join("dag-cycle-cached-vendor");
    copy_dir_all(&vendor_dir, &cyc_cached_vendor).unwrap();
    let cyc_root_src = "prelude\nimport Miri.DagTop\n";
    fs::write(cyc_cached_vendor.join("Miri/DagRoot.lean"), cyc_root_src).unwrap();
    let mut cyc_cached_sources = expected_sources.clone();
    cyc_cached_sources
        .insert("Miri/DagRoot.lean".to_string(), sha256_bytes(cyc_root_src.as_bytes()));
    fs::remove_file(cache_dir.join("Miri/DagRoot.olean")).unwrap();
    let mut c3_cached = fix.checker();
    c3_cached.set_require_mir_wp(false);
    c3_cached.set_miri_cache_dir(Some(cache_dir));
    c3_cached.run().unwrap();
    let err_cyc_cached = c3_cached
        .verify_and_stage_miri_entries(&cyc_cached_vendor, &entries, &cyc_cached_sources)
        .unwrap_err();
    assert_eq!(err_cyc_cached.code, 1, "expected policy cycle rejection: {err_cyc_cached}");
    assert!(
        err_cyc_cached.message.contains("import cycle in Miri closure modules"),
        "unexpected 1-cold cached-node cycle error: {err_cyc_cached}"
    );
}

/// Verifies Pass 1 parallel DAG compilation on a multi-branch `theory/`
/// diamond (`Anneal.Root` -> `{Anneal.Left, Anneal.Right}` -> `Anneal`) and
/// confirms deterministic earliest-order failure reporting when concurrent
/// sibling modules both fail compilation.
#[test]
fn compiles_pass1_diamond_dag_in_parallel_and_preserves_failure_order() {
    let fix = TempFixture::new(None);
    let theory_dir = fix.root.join("theory/Anneal");
    fs::create_dir_all(&theory_dir).unwrap();
    fs::write(
        theory_dir.join("Root.lean"),
        "prelude\nimport Init.Core\nimport Trusted\nnamespace Anneal.Root\ndef base : Nat := 1\nend Anneal.Root\n",
    )
    .unwrap();
    fs::write(
        theory_dir.join("Left.lean"),
        "prelude\nimport Init.Core\nimport Anneal.Root\nnamespace Anneal.Left\ndef l : Nat := Anneal.Root.base\nend Anneal.Left\n",
    )
    .unwrap();
    fs::write(
        theory_dir.join("Right.lean"),
        "prelude\nimport Init.Core\nimport Anneal.Root\nnamespace Anneal.Right\ndef r : Nat := Anneal.Root.base\nend Anneal.Right\n",
    )
    .unwrap();
    fs::write(
        fix.root.join("theory/Anneal.lean"),
        "prelude\nimport Init.Core\nimport Anneal.Left\nimport Anneal.Right\nnamespace Anneal\ndef top : Nat := Anneal.Left.l\nend Anneal\n",
    )
    .unwrap();

    let mut ok_checker = fix.checker();
    ok_checker.set_require_mir_wp(false);
    let report = ok_checker.run().unwrap();
    assert_eq!(report.get("replay"), Some(&json!(true)));

    // Both sibling leaves fail typechecking; `Anneal.Left` precedes
    // `Anneal.Right` in sorted topological order so its failure must win.
    fs::write(
        theory_dir.join("Left.lean"),
        "prelude\nimport Init.Core\nimport Anneal.Root\nnamespace Anneal.Left\ndef l : Nat := true\nend Anneal.Left\n",
    )
    .unwrap();
    fs::write(
        theory_dir.join("Right.lean"),
        "prelude\nimport Init.Core\nimport Anneal.Root\nnamespace Anneal.Right\ndef r : Nat := false\nend Anneal.Right\n",
    )
    .unwrap();
    let mut err_checker = fix.checker();
    err_checker.set_require_mir_wp(false);
    let err = err_checker.run().unwrap_err();
    assert_eq!(err.code, 2, "expected compile failure: {err}");
    assert_eq!(err.phase, "compile-Anneal.Left", "expected earliest sibling failure, got: {err}");
}

/// Negative and compatibility regressions at the `cargo_anneal::Checker`
/// boundary for prebuilt `.olean` `manifest.json` admission: malformed JSON,
/// unknown fields on `schema_version: 1`, and `schema_version: 2` entries
/// omitting `transitive_sha256` must all fail closed with exit code `2`
/// (`olean-cache`), whereas well-formed `schema_version: 1` manifests skip
/// cleanly by default and fail closed (`code = 2`) under
/// `--no-rebuild-bundled`.
#[test]
fn prebuilt_olean_manifest_admission_rejects_malformed_and_missing_transitive_sha256() {
    use std::os::unix::fs::PermissionsExt;

    let dir = tempfile::tempdir().unwrap();
    let base = fs::canonicalize(dir.path()).unwrap();
    let root = base.join("bundle");
    let prefix = base.join("sysroot");
    let prebuilt = base.join("prebuilt");
    let cache_home = base.join("xdg-cache");
    fs::create_dir_all(prefix.join("lib/lean/Init")).unwrap();
    fs::create_dir_all(&prebuilt).unwrap();
    fs::create_dir_all(&cache_home).unwrap();

    let inspector_src = root.join("trusted/audit/TrustedBoundary.lean");
    fs::create_dir_all(inspector_src.parent().unwrap()).unwrap();
    fs::write(&inspector_src, "-- synthetic inspector\n").unwrap();

    let lean = base.join("lean");
    fs::write(
        &lean,
        format!(
            r#"#!/bin/sh
case "$1" in
    --version) printf 'Lean 4.34.1\n'; exit ;;
    --print-prefix) printf '%s\n' '{}'; exit ;;
esac
out=""
while [ "$#" -gt 0 ]; do
    case "$1" in
        -o) out="$2"; shift 2 ;;
        *) shift ;;
    esac
done
if [ -n "$out" ]; then
    printf 'olean\0024.34.1\000synthetic' > "$out"
    exit 0
fi
exit 1
"#,
            prefix.display()
        ),
    )
    .unwrap();
    fs::set_permissions(&lean, fs::Permissions::from_mode(0o755)).unwrap();

    let mod_src = base.join("MirAst.lean");
    fs::write(&mod_src, "prelude\n").unwrap();
    let order = vec!["Trusted.MirAst".to_owned()];
    let sources = BTreeMap::from([("Trusted.MirAst".to_owned(), mod_src)]);
    let imports = BTreeMap::from([("Trusted.MirAst".to_owned(), Vec::new())]);
    let is_module = BTreeMap::from([("Trusted.MirAst".to_owned(), false)]);

    let env_vars = [
        ("HOME".to_owned(), base.to_string_lossy().into_owned()),
        ("XDG_CACHE_HOME".to_owned(), cache_home.to_string_lossy().into_owned()),
    ];

    // 1. Malformed JSON, unknown top-level fields on `schema_version: 1`, and
    //    `schema_version: 2` entries omitting `transitive_sha256` must all fail
    //    closed with exit code `2` in phase `olean-cache`.
    for (case, bad_manifest) in [
        ("malformed-json", br#"{not json"#.as_slice()),
        ("v1-unknown-field", br#"{"schema_version":1,"entries":[],"bogus":1}"#.as_slice()),
        (
            "v2-missing-transitive-sha",
            br#"{"schema_version":2,"entries":[{"kind":"module","module":"M","lean_sha256":"a","sysroot_manifest_sha256":"b","source_sha256":"c","is_module":false,"flags":[],"imports":[{"module":"I","is_exported":true,"import_all":false,"is_meta":false,"part_sha256s":[]}],"parts":[]}]}"#.as_slice(),
        ),
    ] {
        fs::write(prebuilt.join("manifest.json"), bad_manifest).unwrap();
        let mut checker =
            cargo_anneal::Checker::new_with_env(&root, Some(&lean), env_vars.clone()).unwrap();
        checker.set_allow_unpinned_lean(true);
        checker.set_sandbox_mode(cargo_anneal::SandboxMode::Unsandboxed);
        checker.set_prebuilt_olean_dir(Some(prebuilt.clone()));
        checker.tool_admission().unwrap();
        let err = checker
            .compile_lean_modules_parallel(
                &order, &sources, &imports, &is_module, "lib", false, false, 1,
            )
            .unwrap_err();
        assert_eq!(err.code, 2, "{case}: expected exit code 2, got {err}");
        assert_eq!(err.phase, "olean-cache", "{case}: {err}");
        assert!(err.message.contains("invalid prebuilt olean manifest"), "{case}: {err}");
    }

    // 2. Well-formed `schema_version: 1` prebuilt manifest skips cleanly by
    //    default (falls back to compiling `Trusted.MirAst`) and fails closed
    //    with exit code `2` when `--no-rebuild-bundled` is active against an
    //    empty disk cache.
    let valid_v1 = json!({
        "schema_version": 1,
        "entries": [{
            "kind": "module",
            "module": "Trusted.MirAst",
            "lean_sha256": "a".repeat(64),
            "sysroot_manifest_sha256": "b".repeat(64),
            "source_sha256": "c".repeat(64),
            "is_module": false,
            "flags": [],
            "imports": [{
                "module": "Init.Core",
                "is_exported": true,
                "import_all": false,
                "is_meta": false,
                "part_sha256s": ["d".repeat(64)],
            }],
            "parts": [{
                "suffix": "olean",
                "path": "lib/Trusted/MirAst.olean",
                "sha256": "0".repeat(64),
            }],
        }],
    });
    fs::write(prebuilt.join("manifest.json"), serde_json::to_vec(&valid_v1).unwrap()).unwrap();

    let mut no_rebuild =
        cargo_anneal::Checker::new_with_env(&root, Some(&lean), env_vars.clone()).unwrap();
    no_rebuild.set_allow_unpinned_lean(true);
    no_rebuild.set_sandbox_mode(cargo_anneal::SandboxMode::Unsandboxed);
    no_rebuild.set_prebuilt_olean_dir(Some(prebuilt.clone()));
    no_rebuild.set_no_rebuild_bundled(true);
    no_rebuild.tool_admission().unwrap();
    let err = no_rebuild
        .compile_lean_modules_parallel(
            &order, &sources, &imports, &is_module, "lib", false, false, 1,
        )
        .unwrap_err();
    assert_eq!(err.code, 2, "{err}");
    assert_eq!(err.phase, "olean-cache", "{err}");
    assert!(err.message.contains("--no-rebuild-bundled"), "{err}");
    assert!(err.message.contains("schema_version 1 != 2"), "{err}");

    let mut default_checker =
        cargo_anneal::Checker::new_with_env(&root, Some(&lean), env_vars).unwrap();
    default_checker.set_allow_unpinned_lean(true);
    default_checker.set_sandbox_mode(cargo_anneal::SandboxMode::Unsandboxed);
    default_checker.set_prebuilt_olean_dir(Some(prebuilt));
    default_checker.tool_admission().unwrap();
    default_checker
        .compile_lean_modules_parallel(
            &order, &sources, &imports, &is_module, "lib", false, false, 1,
        )
        .unwrap();
}
