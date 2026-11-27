// Copyright 2026 The Fuchsia Authors
//
// Licensed under a BSD-style license <LICENSE-BSD>, Apache License, Version 2.0
// <LICENSE-APACHE or https://www.apache.org/licenses/LICENSE-2.0>, or the MIT
// license <LICENSE-MIT or https://opensource.org/licenses/MIT>, at your option.
// This file may not be copied, modified, or distributed except according to
// those terms.

//! Parallel DAG compilation and prebuilt `.olean` manifest admission.

use super::*;

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
