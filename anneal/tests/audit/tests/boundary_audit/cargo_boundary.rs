// Copyright 2026 The Fuchsia Authors
//
// Licensed under a BSD-style license <LICENSE-BSD>, Apache License, Version 2.0
// <LICENSE-APACHE or https://www.apache.org/licenses/LICENSE-2.0>, or the MIT
// license <LICENSE-MIT or https://opensource.org/licenses/MIT>, at your option.
// This file may not be copied, modified, or distributed except according to
// those terms.

//! `check_cargo_boundary`: workspace members, path dependencies, and the
//! two- and three-zone Cargo boundary lattices.

use super::*;

/// Verifies that `check_cargo_boundary` rejects Cargo workspace members
/// outside `trusted/` and `tests/`, rejects reverse `trusted/` -> `tests/` and
/// out-of-`trusted/` `path` dependencies, and enforces `publish = false` and
/// build-script prohibition on `tests/` crates.
#[test]
fn rejects_cargo_workspace_members_and_path_deps_outside_trusted() {
    let checkout = repo_root();
    let mut fix = TempFixture::new(None);
    fs::copy(checkout.join("Cargo.toml"), fix.root.join("Cargo.toml")).unwrap();
    for rel in [
        "trusted/audit/Cargo.toml",
        "tests/testkit/Cargo.toml",
        "tests/audit/Cargo.toml",
        "tests/cargo-anneal/Cargo.toml",
        "tests/itree_diff/Cargo.toml",
        "tests/rustc-capture/Cargo.toml",
        "tests/differential/Cargo.toml",
        "tools/anneal-scaffold/Cargo.toml",
        "tools/anneal-scaffold/Cargo.lock",
        "tools/anneal-scaffold/scaffold/Cargo.toml",
        "tools/anneal-spec/Cargo.toml",
        "tools/anneal-spec/Cargo.lock",
        "tools/anneal-spec/obligations/Cargo.toml",
        "tools/anneal-spec/lower/Cargo.toml",
        "tools/anneal-spec/macros/Cargo.toml",
    ] {
        let dest = fix.root.join(rel);
        fs::create_dir_all(dest.parent().unwrap()).unwrap();
        fs::copy(checkout.join(rel), dest).unwrap();
    }
    copy_dir_all(&checkout.join("trusted/rustc-capture"), &fix.root.join("trusted/rustc-capture"))
        .unwrap();
    copy_dir_all(&checkout.join("trusted/cargo-anneal"), &fix.root.join("trusted/cargo-anneal"))
        .unwrap();
    check_cargo_boundary(&fix.root).unwrap();

    fs::create_dir_all(fix.root.join("crates/untrusted-helper/src")).unwrap();
    fs::write(
        fix.root.join("crates/untrusted-helper/Cargo.toml"),
        b"[package]\nname = \"untrusted-helper\"\nversion = \"0.1.0\"\nedition = \"2024\"\n",
    )
    .unwrap();
    fs::write(fix.root.join("crates/untrusted-helper/src/lib.rs"), b"").unwrap();
    fs::write(
        fix.root.join("Cargo.toml"),
        b"[workspace]\nresolver = \"2\"\nmembers = [\n    \"trusted/rustc-capture\",\n    \"trusted/cargo-anneal\",\n    \"crates/untrusted-helper\",\n]\n",
    )
    .unwrap();
    let err_member = fix.check_expected(Some(1), Some("cargo-boundary"), Some(false)).unwrap_err();
    assert!(
        err_member
            .message
            .contains("workspace member outside trusted/, tests/, or tools/: crates/untrusted-helper"),
        "unexpected error: {err_member}"
    );

    // Reverse edge `trusted/` -> `tests/` must be rejected in both
    // `[dependencies]` and `[dev-dependencies]`.
    fs::copy(checkout.join("Cargo.toml"), fix.root.join("Cargo.toml")).unwrap();
    for section in ["dependencies", "dev-dependencies"] {
        fs::write(
            fix.root.join("trusted/rustc-capture/Cargo.toml"),
            format!(
                "[package]\nname = \"anneal-rustc-capture\"\nversion = \"0.1.0\"\nedition = \"2024\"\n[{section}]\nanneal-audit-tests = {{ path = \"../../tests/audit\" }}\n"
            ),
        )
        .unwrap();
        let err_rev = fix.check_expected(Some(1), Some("cargo-boundary"), Some(false)).unwrap_err();
        assert!(
            err_rev
                .message
                .contains("trusted/rustc-capture (Trusted) path dependency violates monotonic boundary targeting tests/audit (Tests)"),
            "unexpected error for {section}: {err_rev}"
        );
    }

    fs::write(
        fix.root.join("trusted/rustc-capture/Cargo.toml"),
        b"[package]\nname = \"anneal-rustc-capture\"\nversion = \"0.1.0\"\nedition = \"2024\"\n[dependencies]\nuntrusted-helper = { path = \"../../crates/untrusted-helper\" }\n",
    )
    .unwrap();
    let err_dep = fix.check_expected(Some(1), Some("cargo-boundary"), Some(false)).unwrap_err();
    assert!(err_dep.message.contains(
        "trusted/rustc-capture path dependency points outside trusted/, tests/, or tools/: crates/untrusted-helper"
    ));

    fs::copy(
        checkout.join("trusted/rustc-capture/Cargo.toml"),
        fix.root.join("trusted/rustc-capture/Cargo.toml"),
    )
    .unwrap();

    // Test crates under `tests/` must declare `publish = false`, forbid
    // `build.rs`, and reject path dependencies outside `trusted/` and `tests/`.
    fs::write(
        fix.root.join("tests/audit/Cargo.toml"),
        b"[package]\nname = \"anneal-audit-tests\"\nversion = \"0.1.0\"\nedition = \"2024\"\n",
    )
    .unwrap();
    let err_publish = fix.check_expected(Some(1), Some("cargo-boundary"), Some(false)).unwrap_err();
    assert!(
        err_publish
            .message
            .contains("non-trusted test crate must set publish = false in tests/audit/Cargo.toml"),
        "unexpected error: {err_publish}"
    );
    fs::write(
        fix.root.join("tests/audit/Cargo.toml"),
        b"[package]\nname = \"anneal-audit-tests\"\nversion = \"0.1.0\"\nedition = \"2024\"\npublish = false\n[dependencies]\nuntrusted-helper = { path = \"../../crates/untrusted-helper\" }\n",
    )
    .unwrap();
    let err_test_dep =
        fix.check_expected(Some(1), Some("cargo-boundary"), Some(false)).unwrap_err();
    assert!(
        err_test_dep.message.contains(
            "tests/audit path dependency points outside trusted/, tests/, or tools/: crates/untrusted-helper"
        ),
        "unexpected error: {err_test_dep}"
    );
    fs::copy(checkout.join("tests/audit/Cargo.toml"), fix.root.join("tests/audit/Cargo.toml"))
        .unwrap();
    fs::write(fix.root.join("tests/audit/build.rs"), b"fn main() {}\n").unwrap();
    let err_test_build =
        fix.check_expected(Some(1), Some("cargo-boundary"), Some(false)).unwrap_err();
    assert!(
        err_test_build.message.contains("disallowed build script tests/audit/build.rs"),
        "unexpected error: {err_test_build}"
    );
    fs::remove_file(fix.root.join("tests/audit/build.rs")).unwrap();
    fs::create_dir_all(fix.root.join(".cargo")).unwrap();
    fs::write(fix.root.join(".cargo/config.toml"), b"[build]\nrustc-wrapper = \"evil\"\n").unwrap();
    let err_cargo_cfg =
        fix.check_expected(Some(1), Some("cargo-boundary"), Some(false)).unwrap_err();
    assert!(
        err_cargo_cfg
            .message
            .contains("forbidden Cargo/toolchain override at repository root: .cargo")
    );
    fs::remove_dir_all(fix.root.join(".cargo")).unwrap();

    fs::write(fix.root.join("rust-toolchain.toml"), b"[toolchain]\nchannel = \"nightly\"\n")
        .unwrap();
    let err_toolchain =
        fix.check_expected(Some(1), Some("cargo-boundary"), Some(false)).unwrap_err();
    assert!(
        err_toolchain
            .message
            .contains("forbidden Cargo/toolchain override at repository root: rust-toolchain.toml")
    );
    fs::remove_file(fix.root.join("rust-toolchain.toml")).unwrap();

    fs::write(
        fix.root.join("Cargo.toml"),
        b"[workspace]\nresolver = \"2\"\nmembers = [\"trusted/rustc-capture\"]\n[patch.crates-io]\nserde = { path = \"crates/untrusted-helper\" }\n",
    )
    .unwrap();
    let err_patch = fix.check_expected(Some(1), Some("cargo-boundary"), Some(false)).unwrap_err();
    assert!(
        err_patch.message.contains("root Cargo.toml may contain only [workspace]"),
        "unexpected error: {err_patch}"
    );
    fs::copy(checkout.join("Cargo.toml"), fix.root.join("Cargo.toml")).unwrap();

    fs::write(
        fix.root.join("Cargo.lock"),
        b"version = 4\n[[package]]\nname = \"evil\"\nversion = \"0.1.0\"\nsource = \"git+https://example.com/evil.git#deadbeef\"\n",
    )
    .unwrap();
    let err_lock = fix.check_expected(Some(1), Some("cargo-boundary"), Some(false)).unwrap_err();
    assert!(err_lock.message.contains("untrusted dependency source in Cargo.lock for evil"));
    fs::remove_file(fix.root.join("Cargo.lock")).unwrap();

    fs::write(
        fix.root.join("Cargo.lock"),
        b"version = 4\n[[package]]\nname = \"rogue-local\"\nversion = \"0.1.0\"\n",
    )
    .unwrap();
    let err_rogue_lock =
        fix.check_expected(Some(1), Some("cargo-boundary"), Some(false)).unwrap_err();
    assert!(
        err_rogue_lock
            .message
            .contains("untrusted local package without source in Cargo.lock: rogue-local"),
        "unexpected error: {err_rogue_lock}"
    );
    fs::remove_file(fix.root.join("Cargo.lock")).unwrap();

    fs::copy(checkout.join("Cargo.lock"), fix.root.join("Cargo.lock")).unwrap();
    fs::copy(checkout.join("flake.nix"), fix.root.join("flake.nix")).unwrap();
    fs::copy(checkout.join("flake.lock"), fix.root.join("flake.lock")).unwrap();
    fs::copy(
        checkout.join("trusted/root-manifest.sha256"),
        fix.root.join("trusted/root-manifest.sha256"),
    )
    .unwrap();
    check_cargo_boundary(&fix.root).unwrap();

    fs::write(fix.root.join("flake.nix"), b"{ }\n").unwrap();
    let err_manifest =
        fix.check_expected(Some(1), Some("cargo-boundary"), Some(false)).unwrap_err();
    assert!(
        err_manifest.message.contains("root TCB manifest digest mismatch for flake.nix"),
        "unexpected error: {err_manifest}"
    );

    // Symlinked, oversized, or unreadable root-manifest.sha256 / Cargo.lock
    // must fail closed rather than silently skipping verification.
    fs::copy(checkout.join("flake.nix"), fix.root.join("flake.nix")).unwrap();

    // 1. Symlinked trusted/root-manifest.sha256 fails closed (`code == 1`)
    // inside `verify_root_manifest_sha256`.
    fs::remove_file(fix.root.join("trusted/root-manifest.sha256")).unwrap();
    symlink(
        checkout.join("trusted/root-manifest.sha256"),
        fix.root.join("trusted/root-manifest.sha256"),
    )
    .unwrap();
    let err_sym_manifest = check_cargo_boundary(&fix.root).unwrap_err();
    assert_eq!(err_sym_manifest.code, 1, "expected policy error: {err_sym_manifest}");
    assert!(
        (err_sym_manifest.message.contains("symbolic links")
            || err_sym_manifest.message.contains("expected a regular file"))
            && err_sym_manifest.message.contains("root-manifest.sha256"),
        "expected O_NOFOLLOW/regular-file guard for root-manifest.sha256, got: {err_sym_manifest}"
    );

    // 2. Oversized `trusted/root-manifest.sha256` (> 4 MiB) hits the size cap
    // (`code == 1`).
    fs::remove_file(fix.root.join("trusted/root-manifest.sha256")).unwrap();
    {
        let oversized = fs::File::create(fix.root.join("trusted/root-manifest.sha256")).unwrap();
        oversized.set_len(4 * 1024 * 1024 + 1).unwrap();
    }
    let err_cap_manifest = check_cargo_boundary(&fix.root).unwrap_err();
    assert_eq!(err_cap_manifest.code, 1, "expected policy error: {err_cap_manifest}");
    assert!(
        err_cap_manifest.message.contains("byte limit")
            && err_cap_manifest.message.contains("root-manifest.sha256"),
        "expected byte-limit guard for root-manifest.sha256, got: {err_cap_manifest}"
    );

    // 3. With `trusted/root-manifest.sha256` absent, `verify_cargo_lock` is
    // reached: symlinked `Cargo.lock` must be rejected by `verify_cargo_lock`
    // (`code == 1`).
    fs::remove_file(fix.root.join("trusted/root-manifest.sha256")).unwrap();
    fs::remove_file(fix.root.join("Cargo.lock")).unwrap();
    symlink(checkout.join("Cargo.lock"), fix.root.join("Cargo.lock")).unwrap();
    let err_sym_lock = check_cargo_boundary(&fix.root).unwrap_err();
    assert_eq!(err_sym_lock.code, 1, "expected policy error: {err_sym_lock}");
    assert!(
        (err_sym_lock.message.contains("symbolic links")
            || err_sym_lock.message.contains("expected a regular file"))
            && err_sym_lock.message.contains("Cargo.lock"),
        "expected O_NOFOLLOW/regular-file guard for Cargo.lock, got: {err_sym_lock}"
    );

    // 4. Oversized `Cargo.lock` (> 16 MiB) hits `verify_cargo_lock`'s 16 MiB
    // cap (`code == 1`).
    fs::remove_file(fix.root.join("Cargo.lock")).unwrap();
    {
        let oversized = fs::File::create(fix.root.join("Cargo.lock")).unwrap();
        oversized.set_len(16 * 1024 * 1024 + 1).unwrap();
    }
    let err_cap_lock = check_cargo_boundary(&fix.root).unwrap_err();
    assert_eq!(err_cap_lock.code, 1, "expected policy error: {err_cap_lock}");
    assert!(
        err_cap_lock.message.contains("byte limit") && err_cap_lock.message.contains("Cargo.lock"),
        "expected byte-limit guard for Cargo.lock, got: {err_cap_lock}"
    );
}

/// Verifies that the root-manifest check reads binary-mode (` *`) entries,
/// which `ci/update_root_manifest.py` and `sha256sum --check` also accept,
/// rejects uppercase digests, non-canonical paths, and whitespace-only lines
/// that the updater also rejects, and that a repository audit fails closed
/// (`code == 1`) when `trusted/root-manifest.sha256` is absent instead of
/// skipping the root build-file check.
#[test]
fn root_manifest_follows_updater_grammar_and_is_required_for_repository_audits() {
    let mut fix = TempFixture::new(None);
    copy_cargo_workspace(&fix.root);
    let manifest_path = fix.root.join("trusted/root-manifest.sha256");
    let text_mode = fs::read_to_string(&manifest_path).unwrap();
    let entries = |rewrite: &dyn Fn(&str) -> String| -> String {
        text_mode
            .lines()
            .map(|l| if l.is_empty() || l.starts_with('#') { format!("{l}\n") } else { rewrite(l) })
            .collect()
    };

    // 1. Binary-mode entries verify like text-mode entries.
    fs::write(&manifest_path, entries(&|l| format!("{} *{}\n", &l[..64], &l[66..]))).unwrap();
    check_cargo_boundary(&fix.root).unwrap();

    // 2. Uppercase digests are malformed, as in the updater.
    fs::write(
        &manifest_path,
        entries(&|l| format!("{}{}\n", l[..64].to_ascii_uppercase(), &l[64..])),
    )
    .unwrap();
    let err_upper = check_cargo_boundary(&fix.root).unwrap_err();
    assert_eq!(err_upper.code, 1, "expected policy error: {err_upper}");
    assert!(
        err_upper.message.contains("malformed line in root-manifest.sha256"),
        "unexpected error: {err_upper}"
    );

    // 3. A non-canonical path is malformed even when its digest matches, as
    // is a whitespace-only line, which `sha256sum --check --strict` rejects.
    let capture_toml = "trusted/rustc-capture/Cargo.toml";
    let capture_digest = sha256_file(&fix.root.join(capture_toml), "test").unwrap();
    for extra in [
        format!("{capture_digest}  trusted//rustc-capture/Cargo.toml\n"),
        "   \n".into(),
        format!("# note\r{capture_digest}  {capture_toml}\n"),
    ] {
        fs::write(&manifest_path, format!("{text_mode}{extra}")).unwrap();
        let err = check_cargo_boundary(&fix.root).unwrap_err();
        assert_eq!(err.code, 1, "expected policy error for {extra:?}: {err}");
        assert!(
            err.message.contains("malformed line in root-manifest.sha256"),
            "unexpected error for {extra:?}: {err}"
        );
    }
    fs::write(&manifest_path, format!("{text_mode}{capture_digest}  {capture_toml}\n")).unwrap();
    check_cargo_boundary(&fix.root).unwrap();

    // 4. Without the manifest, the library check still passes for synthetic
    // workspaces, but the repository audit fails closed.
    fs::remove_file(&manifest_path).unwrap();
    check_cargo_boundary(&fix.root).unwrap();
    let err_missing = fix.check_expected(Some(1), Some("cargo-boundary"), Some(false)).unwrap_err();
    assert!(
        err_missing.message.contains("requires trusted/root-manifest.sha256"),
        "unexpected error: {err_missing}"
    );
}

/// Exhaustively exercises all 12 positive and negative cases of the two-zone
/// monotonic Cargo workspace lattice (`WorkspaceZone::Trusted = 0 <
/// WorkspaceZone::Tests = 1`) inside a `anneal-testkit` `WorkspaceBuilder`.
#[test]
fn enforces_two_zone_monotonic_cargo_boundary_lattice() {
    use std::time::Duration;

    let checkout = repo_root();
    let mut ws =
        anneal_testkit::WorkspaceBuilder::new("anneal-lattice-audit-", Duration::from_secs(10))
            .unwrap();
    ws.seed_minimal_audit_locks(&checkout).unwrap();

    let base_root_toml = "\
[workspace]
resolver = \"2\"
members = [
    \"trusted/rustc-capture\",
    \"trusted/cargo-anneal\",
    \"trusted/audit\",
    \"tests/testkit\",
    \"tests/audit\",
]
";
    let reset_manifests = |ws: &mut anneal_testkit::WorkspaceBuilder| {
        ws.write_work_file("Cargo.toml", base_root_toml.as_bytes()).unwrap();
        ws.write_work_file(
            "trusted/rustc-capture/Cargo.toml",
            b"[package]\nname = \"anneal-rustc-capture\"\nversion = \"0.1.0\"\nedition = \"2024\"\n",
        )
        .unwrap();
        ws.write_work_file(
            "trusted/cargo-anneal/Cargo.toml",
            b"[package]\nname = \"cargo-anneal\"\nversion = \"0.1.0\"\nedition = \"2024\"\n",
        )
        .unwrap();
        ws.write_work_file(
            "trusted/audit/Cargo.toml",
            b"[package]\nname = \"anneal-audit\"\nversion = \"0.1.0\"\nedition = \"2024\"\n[dependencies]\ncargo-anneal = { path = \"../cargo-anneal\" }\n",
        )
        .unwrap();
        ws.write_work_file(
            "tests/testkit/Cargo.toml",
            b"[package]\nname = \"anneal-testkit\"\nversion = \"0.1.0\"\nedition = \"2024\"\npublish = false\n",
        )
        .unwrap();
        ws.write_work_file(
            "tests/audit/Cargo.toml",
            b"[package]\nname = \"anneal-audit-tests\"\nversion = \"0.1.0\"\nedition = \"2024\"\npublish = false\n[dependencies]\nanneal-audit = { path = \"../../trusted/audit\" }\nanneal-testkit = { path = \"../testkit\" }\n",
        )
        .unwrap();
        ws.write_work_file("trusted/cargo-anneal/build.rs", b"fn main() {}\n").unwrap();
    };

    // Cases 1–3: `trusted/* -> trusted/*` (`0 <= 0`), `tests/* -> trusted/*`
    // (`0 <= 1`), and `tests/* -> tests/testkit` (`1 <= 1`) in `[dependencies]`
    // all pass.
    reset_manifests(&mut ws);
    check_cargo_boundary(ws.work_dir()).unwrap();

    // Case 4: `tests/* -> tests/testkit` across `[dev-dependencies]`,
    // `[dev_dependencies]`, and `[target.'cfg(unix)'.dev-dependencies]` passes.
    for section in ["dev-dependencies", "dev_dependencies", "target.'cfg(unix)'.dev-dependencies"] {
        reset_manifests(&mut ws);
        ws.write_work_file(
            "tests/audit/Cargo.toml",
            format!(
                "[package]\nname = \"anneal-audit-tests\"\nversion = \"0.1.0\"\nedition = \"2024\"\npublish = false\n[{section}]\nanneal-testkit = {{ path = \"../testkit\" }}\n"
            )
            .as_bytes(),
        )
        .unwrap();
        check_cargo_boundary(ws.work_dir()).unwrap();
    }

    // Cases 5–7: `trusted/* -> tests/testkit` (`1 <= 0` violated) fails across
    // every dependency table spelling (`dependencies`, `dev-dependencies`,
    // `dev_dependencies`, `build-dependencies`, `build_dependencies`, and
    // `[target.<cfg>.*]`).
    for section in [
        "dependencies",
        "dev-dependencies",
        "dev_dependencies",
        "build-dependencies",
        "build_dependencies",
        "target.'cfg(unix)'.dependencies",
        "target.'cfg(unix)'.dev-dependencies",
    ] {
        reset_manifests(&mut ws);
        ws.write_work_file(
            "trusted/cargo-anneal/Cargo.toml",
            format!(
                "[package]\nname = \"cargo-anneal\"\nversion = \"0.1.0\"\nedition = \"2024\"\n[{section}]\nanneal-testkit = {{ path = \"../../tests/testkit\" }}\n"
            )
            .as_bytes(),
        )
        .unwrap();
        let err = check_cargo_boundary(ws.work_dir()).unwrap_err();
        assert_eq!(err.code, 1, "{section}: {err}");
        assert_eq!(err.phase, "cargo-boundary", "{section}: {err}");
        assert!(
            err.message.contains("violates monotonic boundary targeting tests/testkit"),
            "{section}: {err}"
        );
    }

    // Case 8: `tests/*` crates omitting `publish = false`, setting
    // `publish = true`,
    // or setting `publish = ["crates-io"]` are rejected.
    for publish_line in ["", "publish = true\n", "publish = [\"crates-io\"]\n"] {
        reset_manifests(&mut ws);
        ws.write_work_file(
            "tests/testkit/Cargo.toml",
            format!(
                "[package]\nname = \"anneal-testkit\"\nversion = \"0.1.0\"\nedition = \"2024\"\n{publish_line}"
            )
            .as_bytes(),
        )
        .unwrap();
        let err = check_cargo_boundary(ws.work_dir()).unwrap_err();
        assert_eq!(err.code, 1);
        assert!(err.message.contains("publish = false"), "{publish_line:?}: {err}");
    }

    // Case 9: `package.build`, `build.rs`, `proc-macro` targets (both
    // `proc-macro`/`proc_macro` and `crate-type`/`crate_type`), and target path
    // escapes (`../escape.rs`) fail closed in `tests/` (while explicit
    // `proc-macro = false` + `crate-type = ["rlib"]` is permitted).
    reset_manifests(&mut ws);
    ws.write_work_file(
        "tests/testkit/Cargo.toml",
        b"[package]\nname = \"anneal-testkit\"\nversion = \"0.1.0\"\nedition = \"2024\"\npublish = false\n[lib]\nproc-macro = false\ncrate-type = [\"rlib\"]\n",
    )
    .unwrap();
    check_cargo_boundary(ws.work_dir()).unwrap();

    for (lib_lines, expected_err) in [
        ("proc-macro = true", "disallowed proc-macro target (lib.proc-macro)"),
        ("proc_macro = true", "disallowed proc-macro target (lib.proc_macro)"),
        ("proc-macro = \"false\"", "disallowed proc-macro target (lib.proc-macro)"),
        ("crate-type = [\"proc-macro\"]", "disallowed proc-macro crate-type (lib.crate-type)"),
        (
            "crate_type = [\"rlib\", \"proc-macro\"]",
            "disallowed proc-macro crate-type (lib.crate_type)",
        ),
        ("crate-type = \"rlib\"", "invalid lib.crate-type"),
    ] {
        reset_manifests(&mut ws);
        ws.write_work_file(
            "tests/testkit/Cargo.toml",
            format!(
                "[package]\nname = \"anneal-testkit\"\nversion = \"0.1.0\"\nedition = \"2024\"\npublish = false\n[lib]\n{lib_lines}\n"
            )
            .as_bytes(),
        )
        .unwrap();
        let err = check_cargo_boundary(ws.work_dir()).unwrap_err();
        assert_eq!(err.code, 1, "{lib_lines}: {err}");
        assert!(err.message.contains(expected_err), "{lib_lines}: {err}");
    }

    reset_manifests(&mut ws);
    ws.write_work_file(
        "tests/testkit/Cargo.toml",
        b"[package]\nname = \"anneal-testkit\"\nversion = \"0.1.0\"\nedition = \"2024\"\npublish = false\nbuild = \"build.rs\"\n",
    )
    .unwrap();
    assert!(
        check_cargo_boundary(ws.work_dir())
            .unwrap_err()
            .message
            .contains("disallowed package.build")
    );

    reset_manifests(&mut ws);
    ws.write_work_file("tests/testkit/build.rs", b"fn main() {}\n").unwrap();
    assert!(
        check_cargo_boundary(ws.work_dir())
            .unwrap_err()
            .message
            .contains("disallowed build script tests/testkit/build.rs")
    );
    fs::remove_file(ws.work_dir().join("tests/testkit/build.rs")).unwrap();

    reset_manifests(&mut ws);
    ws.write_work_file(
        "tests/testkit/Cargo.toml",
        b"[package]\nname = \"anneal-testkit\"\nversion = \"0.1.0\"\nedition = \"2024\"\npublish = false\n[lib]\npath = \"../escape.rs\"\n",
    )
    .unwrap();
    assert!(
        check_cargo_boundary(ws.work_dir())
            .unwrap_err()
            .message
            .contains("escapes member directory")
    );

    // Case 10: `git` and custom `registry` dependencies are rejected.
    for dep_spec in [
        "evil = { git = \"https://example.com/repo.git\" }",
        "evil = { version = \"0.1\", registry = \"custom\" }",
    ] {
        reset_manifests(&mut ws);
        ws.write_work_file(
            "tests/testkit/Cargo.toml",
            format!(
                "[package]\nname = \"anneal-testkit\"\nversion = \"0.1.0\"\nedition = \"2024\"\npublish = false\n[dependencies]\n{dep_spec}\n"
            )
            .as_bytes(),
        )
        .unwrap();
        let err = check_cargo_boundary(ws.work_dir()).unwrap_err();
        assert!(err.message.contains("disallowed git or custom-registry"), "{err}");
    }

    // Case 11: Path dependencies pointing to non-member crates inside `tests/`,
    // outside `trusted/` & `tests/`, or escaping the checkout all fail closed.
    ws.write_work_file(
        "tests/unlisted/Cargo.toml",
        b"[package]\nname = \"unlisted\"\nversion = \"0.1.0\"\nedition = \"2024\"\npublish = false\n",
    )
    .unwrap();
    reset_manifests(&mut ws);
    ws.write_work_file(
        "tests/audit/Cargo.toml",
        b"[package]\nname = \"anneal-audit-tests\"\nversion = \"0.1.0\"\nedition = \"2024\"\npublish = false\n[dependencies]\nunlisted = { path = \"../unlisted\" }\n",
    )
    .unwrap();
    let err_nonmember = check_cargo_boundary(ws.work_dir()).unwrap_err();
    assert!(
        err_nonmember.message.contains("points to non-member crate: tests/unlisted"),
        "{err_nonmember}"
    );

    // Create an actual directory outside `ws.work_dir()` so canonicalization
    // succeeds and exercises the `strip_prefix(checkout_canon)` escape guard.
    let outside_dir = ws.root_dir().join("outside");
    fs::create_dir_all(&outside_dir).unwrap();
    fs::write(
        outside_dir.join("Cargo.toml"),
        b"[package]\nname = \"outside\"\nversion = \"0.1.0\"\nedition = \"2024\"\npublish = false\n",
    )
    .unwrap();
    reset_manifests(&mut ws);
    ws.write_work_file(
        "tests/audit/Cargo.toml",
        b"[package]\nname = \"anneal-audit-tests\"\nversion = \"0.1.0\"\nedition = \"2024\"\npublish = false\n[dependencies]\nescape = { path = \"../../../outside\" }\n",
    )
    .unwrap();
    let err_escape = check_cargo_boundary(ws.work_dir()).unwrap_err();
    assert_eq!(err_escape.code, 1, "{err_escape}");
    assert!(
        err_escape.message.contains("escapes checkout"),
        "expected checkout-escape diagnostic, got: {err_escape}"
    );

    // Case 12: Unclean member paths (bare `trusted`, `tests`, trailing `/`,
    // or non-compliant `workspace.exclude` crates) are rejected.
    for (bad_member, expected_diag) in [
        ("trusted", "outside trusted/, tests/, or tools/: trusted"),
        ("tests", "outside trusted/, tests/, or tools/: tests"),
        ("tools", "outside trusted/, tests/, or tools/: tools"),
        ("trusted/", "unclean member path: trusted/"),
        ("tests/../trusted/audit", "unclean member path: tests/../trusted/audit"),
    ] {
        reset_manifests(&mut ws);
        ws.write_work_file(
            "Cargo.toml",
            format!(
                "[workspace]\nresolver = \"2\"\nmembers = [\"trusted/rustc-capture\", \"{bad_member}\"]\n"
            )
            .as_bytes(),
        )
        .unwrap();
        let err = check_cargo_boundary(ws.work_dir()).unwrap_err();
        assert_eq!(err.code, 1, "{bad_member}: {err}");
        assert!(err.message.contains(expected_diag), "{bad_member}: {err}");
    }

    reset_manifests(&mut ws);
    ws.write_work_file(
        "Cargo.toml",
        format!("{base_root_toml}exclude = [\"tests/unlisted\"]\n").as_bytes(),
    )
    .unwrap();
    ws.write_work_file(
        "tests/unlisted/Cargo.toml",
        b"[package]\nname = \"unlisted\"\nversion = \"0.1.0\"\nedition = \"2024\"\n",
    )
    .unwrap();
    let err_excl = check_cargo_boundary(ws.work_dir()).unwrap_err();
    assert!(err_excl.message.contains("publish = false"), "{err_excl}");

    ws.stage().unwrap().finish(Ok(())).unwrap();
}

/// Asserts that `check_cargo_boundary(dir)` fails as a `"cargo-boundary"`
/// policy rejection (`code == 1`) whose message contains `needle`.
fn assert_cargo_boundary_rejects(dir: &Path, needle: &str) {
    let err = check_cargo_boundary(dir).unwrap_err();
    assert_eq!(err.code, 1, "{needle}: {err}");
    assert_eq!(err.phase, "cargo-boundary", "{needle}: {err}");
    assert!(err.message.contains(needle), "expected {needle:?}, got: {err}");
}

/// Verifies the untrusted `tools/` zone (`WorkspaceZone::Tools = 2`):
/// - `tools/` crates may not be root `workspace.members` and must instead be
///   excluded standalone crates or workspaces;
/// - `trusted/` -> `tools/` and `tests/` -> `tools/` dependencies are rejected;
/// - `tools/` crates must set `publish = false` and forbid `build.rs`;
/// - `proc-macro = true` is allowed in `tools/` only;
/// - excluded standalone `[workspace]` tools under `tools/` require resolver
///   `"2"`, no `workspace.exclude`, and clean member paths, and validate
///   members and `Cargo.lock` provenance;
/// - `tools/` must be a regular directory free of symlinks and of
///   unregistered `Cargo.toml` / `Cargo.lock` files in any letter case;
/// - `[patch]` / `[replace]` are rejected in every member and excluded
///   manifest, and each `Cargo.lock` may list without a `source` only the
///   crates it resolves and their transitive `path` dependencies.
#[test]
fn enforces_three_zone_tools_cargo_boundary() {
    use std::time::Duration;

    let checkout = repo_root();
    let mut ws =
        anneal_testkit::WorkspaceBuilder::new("anneal-tools-zone-audit-", Duration::from_secs(10))
            .unwrap();
    ws.seed_minimal_audit_locks(&checkout).unwrap();

    let write_base = |ws: &mut anneal_testkit::WorkspaceBuilder,
                      members_extra: &str,
                      exclude: &str| {
        ws.write_work_file(
            "Cargo.toml",
            format!(
                "[workspace]\nresolver = \"2\"\nmembers = [\n    \"trusted/rustc-capture\",\n    \"tests/audit\",\n{members_extra}]\n{exclude}"
            )
            .as_bytes(),
        )
        .unwrap();
        ws.write_work_file(
            "trusted/rustc-capture/Cargo.toml",
            b"[package]\nname = \"anneal-rustc-capture\"\nversion = \"0.1.0\"\nedition = \"2024\"\n",
        )
        .unwrap();
        ws.write_work_file(
            "tests/audit/Cargo.toml",
            b"[package]\nname = \"anneal-audit-tests\"\nversion = \"0.1.0\"\nedition = \"2024\"\npublish = false\n",
        )
        .unwrap();
    };

    // Standalone excluded `[workspace]` under `tools/mytool` with
    // `proc-macro = true` passes.
    let mytool_ws_toml: &[u8] =
        b"[workspace]\nresolver = \"2\"\nmembers = [\"core\", \"macros\"]\n";
    let mytool_lock: &[u8] = b"version = 4\n[[package]]\nname = \"mytool-core\"\nversion = \"0.1.0\"\n[[package]]\nname = \"mytool-macros\"\nversion = \"0.1.0\"\n";
    let mytool_core_toml: &[u8] = b"[package]\nname = \"mytool-core\"\nversion = \"0.1.0\"\nedition = \"2021\"\npublish = false\n";
    write_base(&mut ws, "", "exclude = [\"tools/mytool\"]\n");
    ws.write_work_file("tools/mytool/Cargo.toml", mytool_ws_toml).unwrap();
    ws.write_work_file("tools/mytool/Cargo.lock", mytool_lock).unwrap();
    ws.write_work_file("tools/mytool/core/Cargo.toml", mytool_core_toml).unwrap();
    ws.write_work_file(
        "tools/mytool/macros/Cargo.toml",
        b"[package]\nname = \"mytool-macros\"\nversion = \"0.1.0\"\nedition = \"2021\"\npublish = false\n[lib]\nproc-macro = true\n[dependencies]\nmytool-core = { path = \"../core\" }\n",
    )
    .unwrap();
    check_cargo_boundary(ws.work_dir()).unwrap();

    // Unregistered `Cargo.toml` under `tools/` is rejected, in any letter
    // case.
    for name in ["Cargo.toml", "cargo.toml", "CARGO.TOML"] {
        ws.write_work_file(
            format!("tools/rogue/{name}"),
            b"[package]\nname = \"rogue\"\nversion = \"0.1.0\"\nedition = \"2021\"\npublish = false\n",
        )
        .unwrap();
        assert_cargo_boundary_rejects(
            ws.work_dir(),
            &format!("unregistered Cargo manifest under tools/: tools/rogue/{name}"),
        );
        fs::remove_dir_all(ws.work_dir().join("tools/rogue")).unwrap();
    }

    // A case variant next to a registered manifest is not the registered
    // path, so it is rejected too.
    ws.write_work_file("tools/mytool/core/cargo.toml", mytool_core_toml).unwrap();
    assert_cargo_boundary_rejects(
        ws.work_dir(),
        "unregistered Cargo manifest under tools/: tools/mytool/core/cargo.toml",
    );
    fs::remove_file(ws.work_dir().join("tools/mytool/core/cargo.toml")).unwrap();

    // Unregistered `Cargo.lock` under `tools/` is rejected, in any letter
    // case, including a case variant beside the registered lockfile.
    for rel in [
        "tools/mytool/core/Cargo.lock",
        "tools/mytool/core/cargo.lock",
        "tools/mytool/core/CARGO.LOCK",
        "tools/mytool/Cargo.LOCK",
    ] {
        ws.write_work_file(rel, mytool_lock).unwrap();
        assert_cargo_boundary_rejects(
            ws.work_dir(),
            &format!("unregistered Cargo.lock under tools/: {rel}"),
        );
        fs::remove_file(ws.work_dir().join(rel)).unwrap();
    }

    // Symlinks under `tools/` are rejected, whether they point at a file or
    // at a directory that would otherwise hide an unregistered manifest.
    let hidden_dir = ws.root_dir().join("hidden-tool");
    fs::create_dir_all(&hidden_dir).unwrap();
    fs::write(
        hidden_dir.join("Cargo.toml"),
        b"[package]\nname = \"hidden\"\nversion = \"0.1.0\"\npublish = false\n",
    )
    .unwrap();
    for (link, target) in [
        ("tools/mytool/linked-dir", hidden_dir.clone()),
        ("tools/mytool/core/linked.rs", hidden_dir.join("Cargo.toml")),
    ] {
        symlink(&target, ws.work_dir().join(link)).unwrap();
        assert_cargo_boundary_rejects(ws.work_dir(), "disallowed symlink under tools/");
        fs::remove_file(ws.work_dir().join(link)).unwrap();
    }
    check_cargo_boundary(ws.work_dir()).unwrap();

    // Untrusted `Cargo.lock` inside `tools/mytool` is rejected.
    ws.write_work_file(
        "tools/mytool/Cargo.lock",
        b"version = 4\n[[package]]\nname = \"rogue-local\"\nversion = \"0.1.0\"\n",
    )
    .unwrap();
    assert_cargo_boundary_rejects(
        ws.work_dir(),
        "untrusted local package without source in Cargo.lock: rogue-local",
    );
    ws.write_work_file("tools/mytool/Cargo.lock", mytool_lock).unwrap();

    // `tools/` member missing `publish = false` is rejected.
    ws.write_work_file(
        "tools/mytool/core/Cargo.toml",
        b"[package]\nname = \"mytool-core\"\nversion = \"0.1.0\"\nedition = \"2021\"\n",
    )
    .unwrap();
    assert_cargo_boundary_rejects(ws.work_dir(), "publish = false");
    ws.write_work_file("tools/mytool/core/Cargo.toml", mytool_core_toml).unwrap();

    // `[patch]` and `[replace]` (in any spelling) in an excluded workspace's
    // member are rejected.
    for (table, label) in [
        ("[patch.crates-io]\nrogue = { path = \"../../../outside\" }\n", "[patch]"),
        ("[replace]\n\"rogue:0.1.0\" = { path = \"../../../outside\" }\n", "[replace]"),
        ("[Patch.crates-io]\nrogue = { path = \"../../../outside\" }\n", "[Patch]"),
    ] {
        ws.write_work_file(
            "tools/mytool/core/Cargo.toml",
            format!(
                "[package]\nname = \"mytool-core\"\nversion = \"0.1.0\"\nedition = \"2021\"\npublish = false\n{table}"
            )
            .as_bytes(),
        )
        .unwrap();
        assert_cargo_boundary_rejects(
            ws.work_dir(),
            &format!("disallowed {label} section in tools/mytool/core/Cargo.toml"),
        );
    }
    ws.write_work_file("tools/mytool/core/Cargo.toml", mytool_core_toml).unwrap();

    // `tools/` member with `build.rs` is rejected.
    ws.write_work_file("tools/mytool/core/build.rs", b"fn main() {}\n").unwrap();
    assert_cargo_boundary_rejects(
        ws.work_dir(),
        "disallowed build script tools/mytool/core/build.rs",
    );
    fs::remove_file(ws.work_dir().join("tools/mytool/core/build.rs")).unwrap();

    // Missing `Cargo.lock` in an excluded `tools/` workspace fails closed.
    fs::remove_file(ws.work_dir().join("tools/mytool/Cargo.lock")).unwrap();
    assert_cargo_boundary_rejects(ws.work_dir(), "missing required Cargo.lock");
    ws.write_work_file("tools/mytool/Cargo.lock", mytool_lock).unwrap();

    // Nested `.cargo/` and `rust-toolchain*` overrides under `tools/` are
    // rejected.
    ws.write_work_file("tools/mytool/core/.cargo/config.toml", b"[build]\n").unwrap();
    assert_cargo_boundary_rejects(ws.work_dir(), "forbidden Cargo/toolchain override under tools/");
    fs::remove_dir_all(ws.work_dir().join("tools/mytool/core/.cargo")).unwrap();

    ws.write_work_file("tools/mytool/core/rust-toolchain.toml", b"[toolchain]\n").unwrap();
    assert_cargo_boundary_rejects(ws.work_dir(), "forbidden Cargo/toolchain override under tools/");
    fs::remove_file(ws.work_dir().join("tools/mytool/core/rust-toolchain.toml")).unwrap();

    // The excluded `tools/` `[workspace]` must use resolver `"2"`, must not
    // declare `workspace.exclude`, and must list only clean member paths.
    // A member cannot escape `tools/` once its path is clean, so the clean
    // check is the containment check.
    for (ws_toml, expected) in [
        (
            "[workspace]\nresolver = \"1\"\nmembers = [\"core\", \"macros\"]\n".to_string(),
            "tools/mytool/Cargo.toml [workspace] resolver must be \"2\"".to_string(),
        ),
        (
            "[workspace]\nmembers = [\"core\", \"macros\"]\n".to_string(),
            "tools/mytool/Cargo.toml [workspace] resolver must be \"2\"".to_string(),
        ),
        (
            "[workspace]\nresolver = \"2\"\nmembers = [\"core\", \"macros\"]\nexclude = [\"core\"]\n"
                .to_string(),
            "tools/mytool/Cargo.toml must not declare workspace.exclude".to_string(),
        ),
    ]
    .into_iter()
    .chain(["../../trusted/rustc-capture", "./core", "core/", "core\\\\x", "/abs"].map(|bad| {
        (
            format!("[workspace]\nresolver = \"2\"\nmembers = [\"macros\", \"{bad}\"]\n"),
            format!("unclean member path in tools/mytool/Cargo.toml: {}", bad.replace("\\\\", "\\")),
        )
    })) {
        ws.write_work_file("tools/mytool/Cargo.toml", ws_toml.as_bytes()).unwrap();
        assert_cargo_boundary_rejects(ws.work_dir(), &expected);
    }
    ws.write_work_file("tools/mytool/Cargo.toml", mytool_ws_toml).unwrap();
    check_cargo_boundary(ws.work_dir()).unwrap();

    // Hybrid `[workspace]` + `[package]` or `[patch]` in excluded `tools/`
    // fails closed.
    for extra in [
        "[package]\nname = \"hybrid\"\nversion = \"0.1.0\"\npublish = false\n",
        "[patch.crates-io]\nrogue = { path = \"../../outside\" }\n",
    ] {
        ws.write_work_file(
            "tools/mytool/Cargo.toml",
            format!("[workspace]\nresolver = \"2\"\nmembers = [\"core\", \"macros\"]\n{extra}")
                .as_bytes(),
        )
        .unwrap();
        assert_cargo_boundary_rejects(ws.work_dir(), "may contain only [workspace]");
    }

    // Excluded single-crate `tools/single` requires `Cargo.lock` and rejects
    // `.cargo/`.
    fs::remove_dir_all(ws.work_dir().join("tools/mytool")).unwrap();
    let single_toml = |extra: &str| {
        format!(
            "[package]\nname = \"tools-single\"\nversion = \"0.1.0\"\nedition = \"2021\"\npublish = false\n{extra}"
        )
    };
    write_base(&mut ws, "", "exclude = [\"tools/single\"]\n");
    ws.write_work_file("tools/single/Cargo.toml", single_toml("").as_bytes()).unwrap();
    assert_cargo_boundary_rejects(ws.work_dir(), "missing required Cargo.lock");
    let single_lock: &[u8] =
        b"version = 4\n[[package]]\nname = \"tools-single\"\nversion = \"0.1.0\"\n";
    ws.write_work_file("tools/single/Cargo.lock", single_lock).unwrap();
    check_cargo_boundary(ws.work_dir()).unwrap();
    ws.write_work_file("tools/single/.cargo/config.toml", b"[build]\n").unwrap();
    assert_cargo_boundary_rejects(ws.work_dir(), "forbidden Cargo/toolchain override");
    fs::remove_dir_all(ws.work_dir().join("tools/single/.cargo")).unwrap();

    // An excluded single crate is its own Cargo root, so `[patch]` and
    // `[replace]` in it are rejected.
    for (table, label) in [
        ("[patch.crates-io]\nanneal-testkit = { path = \"../../../outside\" }\n", "[patch]"),
        ("[replace]\n\"anneal-testkit:0.1.0\" = { path = \"../../../outside\" }\n", "[replace]"),
        ("[PATCH.crates-io]\nanneal-testkit = { path = \"../../../outside\" }\n", "[PATCH]"),
    ] {
        ws.write_work_file(
            "tools/single/Cargo.toml",
            single_toml(&format!("[dependencies]\nanneal-testkit = \"0.1.0\"\n{table}")).as_bytes(),
        )
        .unwrap();
        assert_cargo_boundary_rejects(
            ws.work_dir(),
            &format!("disallowed {label} section in tools/single/Cargo.toml"),
        );
    }
    ws.write_work_file("tools/single/Cargo.toml", single_toml("").as_bytes()).unwrap();

    // Its `Cargo.lock` may name without a `source` only itself and its
    // transitive `path` dependencies, not other root workspace members.
    let single_lock_with = |extra: &[&str]| {
        let mut lock = String::from_utf8(single_lock.to_vec()).unwrap();
        for name in extra {
            lock.push_str(&format!("[[package]]\nname = \"{name}\"\nversion = \"0.1.0\"\n"));
        }
        lock
    };
    ws.write_work_file(
        "tools/single/Cargo.lock",
        single_lock_with(&["anneal-audit-tests"]).as_bytes(),
    )
    .unwrap();
    assert_cargo_boundary_rejects(
        ws.work_dir(),
        "untrusted local package without source in Cargo.lock: anneal-audit-tests",
    );
    ws.write_work_file(
        "tools/single/Cargo.toml",
        single_toml("[dependencies]\nanneal-audit-tests = { path = \"../../tests/audit\" }\n")
            .as_bytes(),
    )
    .unwrap();
    check_cargo_boundary(ws.work_dir()).unwrap();
    ws.write_work_file(
        "tests/audit/Cargo.toml",
        b"[package]\nname = \"anneal-audit-tests\"\nversion = \"0.1.0\"\nedition = \"2024\"\npublish = false\n[dependencies]\nanneal-rustc-capture = { path = \"../../trusted/rustc-capture\" }\n",
    )
    .unwrap();
    ws.write_work_file(
        "tools/single/Cargo.lock",
        single_lock_with(&["anneal-audit-tests", "anneal-rustc-capture"]).as_bytes(),
    )
    .unwrap();
    check_cargo_boundary(ws.work_dir()).unwrap();

    // The root `Cargo.lock` may not name an excluded `tools/` crate.
    let root_lock = "version = 4\n[[package]]\nname = \"anneal-rustc-capture\"\nversion = \"0.1.0\"\n[[package]]\nname = \"anneal-audit-tests\"\nversion = \"0.1.0\"\n";
    ws.write_work_file("Cargo.lock", root_lock.as_bytes()).unwrap();
    check_cargo_boundary(ws.work_dir()).unwrap();
    ws.write_work_file(
        "Cargo.lock",
        format!("{root_lock}[[package]]\nname = \"tools-single\"\nversion = \"0.1.0\"\n")
            .as_bytes(),
    )
    .unwrap();
    assert_cargo_boundary_rejects(
        ws.work_dir(),
        "untrusted local package without source in Cargo.lock: tools-single",
    );
    fs::remove_file(ws.work_dir().join("Cargo.lock")).unwrap();
    write_base(&mut ws, "", "exclude = [\"tools/single\"]\n");
    ws.write_work_file("tools/single/Cargo.toml", single_toml("").as_bytes()).unwrap();
    ws.write_work_file("tools/single/Cargo.lock", single_lock).unwrap();
    check_cargo_boundary(ws.work_dir()).unwrap();

    // `[patch]` and `[replace]` are rejected in root members too, and in an
    // excluded `tests/` crate, whose `Cargo.lock` is optional.
    ws.write_work_file(
        "tests/audit/Cargo.toml",
        b"[package]\nname = \"anneal-audit-tests\"\nversion = \"0.1.0\"\nedition = \"2024\"\npublish = false\n[patch.crates-io]\nrogue = { path = \"../../../outside\" }\n",
    )
    .unwrap();
    assert_cargo_boundary_rejects(
        ws.work_dir(),
        "disallowed [patch] section in tests/audit/Cargo.toml",
    );
    write_base(&mut ws, "", "exclude = [\"tools/single\", \"tests/excl\"]\n");
    ws.write_work_file(
        "tests/excl/Cargo.toml",
        b"[package]\nname = \"tests-excl\"\nversion = \"0.1.0\"\nedition = \"2024\"\npublish = false\n",
    )
    .unwrap();
    check_cargo_boundary(ws.work_dir()).unwrap();
    ws.write_work_file(
        "tests/excl/Cargo.toml",
        b"[package]\nname = \"tests-excl\"\nversion = \"0.1.0\"\nedition = \"2024\"\npublish = false\n[replace]\n\"rogue:0.1.0\" = { git = \"https://example.com/rogue.git\" }\n",
    )
    .unwrap();
    assert_cargo_boundary_rejects(
        ws.work_dir(),
        "disallowed [replace] section in tests/excl/Cargo.toml",
    );

    // `[workspace]` in an excluded crate outside `tools/` is rejected.
    ws.write_work_file("tests/excl/Cargo.toml", b"[workspace]\nresolver = \"2\"\nmembers = []\n")
        .unwrap();
    assert_cargo_boundary_rejects(
        ws.work_dir(),
        "disallowed [workspace] in excluded crate outside tools/: tests/excl",
    );
    fs::remove_dir_all(ws.work_dir().join("tests/excl")).unwrap();
    write_base(&mut ws, "", "exclude = [\"tools/single\"]\n");
    check_cargo_boundary(ws.work_dir()).unwrap();

    // A `tools/` crate may not be a root workspace member, because its
    // proc-macros would then build in the root workspace.
    write_base(&mut ws, "    \"tools/single\",\n", "");
    assert_cargo_boundary_rejects(
        ws.work_dir(),
        "tools/ crate must be in workspace.exclude, not workspace.members: tools/single",
    );

    // `trusted/` -> `tools/` and `tests/` -> `tools/` are rejected.
    write_base(&mut ws, "", "exclude = [\"tools/single\"]\n");
    ws.write_work_file(
        "trusted/rustc-capture/Cargo.toml",
        b"[package]\nname = \"anneal-rustc-capture\"\nversion = \"0.1.0\"\nedition = \"2024\"\n[dependencies]\ntools-single = { path = \"../../tools/single\" }\n",
    )
    .unwrap();
    assert_cargo_boundary_rejects(
        ws.work_dir(),
        "trusted/rustc-capture (Trusted) path dependency violates monotonic boundary targeting tools/single (Tools)",
    );
    write_base(&mut ws, "", "exclude = [\"tools/single\"]\n");

    ws.write_work_file(
        "tests/audit/Cargo.toml",
        b"[package]\nname = \"anneal-audit-tests\"\nversion = \"0.1.0\"\nedition = \"2024\"\npublish = false\n[dependencies]\ntools-single = { path = \"../../tools/single\" }\n",
    )
    .unwrap();
    assert_cargo_boundary_rejects(
        ws.work_dir(),
        "tests/audit (Tests) path dependency violates monotonic boundary targeting tools/single (Tools)",
    );

    // `tools/` itself must be a regular directory: a file or a symlink to a
    // directory is rejected.
    write_base(&mut ws, "", "");
    fs::remove_dir_all(ws.work_dir().join("tools")).unwrap();
    check_cargo_boundary(ws.work_dir()).unwrap();
    ws.write_work_file("tools", b"not a directory\n").unwrap();
    assert_cargo_boundary_rejects(ws.work_dir(), "tools/ must be a regular directory");
    fs::remove_file(ws.work_dir().join("tools")).unwrap();
    symlink(&hidden_dir, ws.work_dir().join("tools")).unwrap();
    assert_cargo_boundary_rejects(ws.work_dir(), "tools/ must be a regular directory");
    fs::remove_file(ws.work_dir().join("tools")).unwrap();

    ws.stage().unwrap().finish(Ok(())).unwrap();
}
