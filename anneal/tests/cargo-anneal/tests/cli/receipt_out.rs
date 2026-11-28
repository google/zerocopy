// Copyright 2026 The Fuchsia Authors
//
// Licensed under a BSD-style license <LICENSE-BSD>, Apache License, Version 2.0
// <LICENSE-APACHE or https://www.apache.org/licenses/LICENSE-2.0>, or the MIT
// license <LICENSE-MIT or https://opensource.org/licenses/MIT>, at your option.
// This file may not be copied, modified, or distributed except according to
// those terms.

//! `--receipt-out` persistence, destination guards, and stale-receipt
//! invalidation.

use super::*;

#[cfg(unix)]
#[path = "receipt_out/olean_cache.rs"]
mod olean_cache;
#[path = "receipt_out/stale_receipt.rs"]
mod stale_receipt;

#[cfg(unix)]
#[test]
fn receipt_out_persists_valid_v3_json_and_rejects_symlinks_dirs_and_input_aliases() {
    use std::{
        fs,
        os::unix::fs::{PermissionsExt as _, symlink},
    };

    let project = tempfile::tempdir().unwrap();
    let request = project.path().join("request.json");
    let precious_bytes = b"precious caller source bytes\n";
    fs::write(&request, precious_bytes).unwrap();

    // 1. Valid `--receipt-out` alongside default `--format human` writes atomic
    //    `0o600` Receipt v3 JSON while rendering the human card on stdout.
    let receipt_file = project.path().join("out-receipt.json");
    let mut ok_cmd = command(Route::Direct, project.path());
    ok_cmd.args(["verify", "--request"]).arg(&request).arg("--receipt-out").arg(&receipt_file);
    #[cfg(not(feature = "setup"))]
    ok_cmd.args(["--capture", "cap", "--sysroot", "sys", "--lean", "lean"]);
    let out = ok_cmd.output().unwrap();
    assert_result(&out, 1, "[FAIL]", "");
    assert_result(&out, 1, &format!("Receipt    : {}", receipt_file.display()), "");
    let meta = fs::symlink_metadata(&receipt_file).unwrap();
    assert!(meta.file_type().is_file() && !meta.file_type().is_symlink());
    assert_eq!(meta.permissions().mode() & 0o777, 0o600);
    let saved: serde_json::Value =
        serde_json::from_slice(&fs::read(&receipt_file).unwrap()).unwrap();
    assert_eq!(saved["schema_version"], 3);
    assert_eq!(saved["status"], "unsupported");
    assert_eq!(saved["phase"], "request");

    // 2. Accepts destinations beneath a symlinked ancestor directory (matching
    //    `--artifacts` and symlinked `TMPDIR` / macOS `/var` setups) while
    //    rejecting input aliasing (including through the symlinked ancestor),
    //    symlinked leaf destinations, directory destinations, and `--artifacts`
    //    collisions with exit 2 (`phase == "receipt-out"`), never clobbering
    //    caller files.
    let target_file = project.path().join("target.json");
    fs::write(&target_file, b"untouched\n").unwrap();
    let sym_dest = project.path().join("sym-receipt.json");
    symlink(&target_file, &sym_dest).unwrap();

    let real_dir = project.path().join("real-dir");
    fs::create_dir(&real_dir).unwrap();
    let real_sub = real_dir.join("sub");
    fs::create_dir(&real_sub).unwrap();
    let sym_dir = project.path().join("sym-dir");
    symlink(&real_dir, &sym_dir).unwrap();

    // Symlinked ancestor destination is accepted and writes `0o600` JSON into
    // the canonical target directory.
    let sym_ancestor_dest = sym_dir.join("sub").join("nested.json");
    let mut sym_ok_cmd = command(Route::Direct, project.path());
    sym_ok_cmd
        .args(["verify", "--format", "json", "--request"])
        .arg(&request)
        .arg("--receipt-out")
        .arg(&sym_ancestor_dest);
    #[cfg(not(feature = "setup"))]
    sym_ok_cmd.args(["--capture", "cap", "--sysroot", "sys", "--lean", "lean"]);
    let sym_ok_out = sym_ok_cmd.output().unwrap();
    assert_eq!(sym_ok_out.status.code(), Some(1), "{sym_ok_out:?}");
    let sym_ok_meta = fs::symlink_metadata(real_sub.join("nested.json")).unwrap();
    assert!(sym_ok_meta.file_type().is_file() && !sym_ok_meta.file_type().is_symlink());
    assert_eq!(sym_ok_meta.permissions().mode() & 0o777, 0o600);
    let sym_ok_saved: serde_json::Value =
        serde_json::from_slice(&fs::read(real_sub.join("nested.json")).unwrap()).unwrap();
    assert_eq!(sym_ok_saved["schema_version"], 3);
    assert_eq!(sym_ok_saved["phase"], "request");

    // A symlinked-ancestor path that aliases `--request` is still rejected.
    let real_req_in_dir = real_dir.join("aliased-req.json");
    fs::write(&real_req_in_dir, precious_bytes).unwrap();
    let mut sym_alias_cmd = command(Route::Direct, project.path());
    sym_alias_cmd
        .args(["verify", "--format", "json", "--request"])
        .arg(&real_req_in_dir)
        .arg("--receipt-out")
        .arg(sym_dir.join("aliased-req.json"));
    #[cfg(not(feature = "setup"))]
    sym_alias_cmd.args(["--capture", "cap", "--sysroot", "sys", "--lean", "lean"]);
    let sym_alias_out = sym_alias_cmd.output().unwrap();
    assert_eq!(sym_alias_out.status.code(), Some(2), "{sym_alias_out:?}");
    let sym_alias_rec: serde_json::Value = serde_json::from_slice(&sym_alias_out.stdout).unwrap();
    assert_eq!(sym_alias_rec["phase"], "receipt-out", "{sym_alias_rec}");
    assert_eq!(fs::read(&real_req_in_dir).unwrap(), precious_bytes);

    let artifacts_dir = project.path().join("ev");
    for bad_dest in [request.clone(), sym_dest.clone(), real_dir.clone(), artifacts_dir.clone()] {
        let mut bad_cmd = command(Route::Direct, project.path());
        bad_cmd
            .args(["verify", "--format", "json", "--request"])
            .arg(&request)
            .arg("--artifacts")
            .arg(&artifacts_dir)
            .arg("--receipt-out")
            .arg(&bad_dest);
        #[cfg(not(feature = "setup"))]
        bad_cmd.args(["--capture", "cap", "--sysroot", "sys", "--lean", "lean"]);
        let bad_out = bad_cmd.output().unwrap();
        assert_eq!(bad_out.status.code(), Some(2), "{bad_dest:?}: {bad_out:?}");
        let fail_rec: serde_json::Value = serde_json::from_slice(&bad_out.stdout).unwrap();
        assert_eq!(fail_rec["status"], "tool_failed", "{fail_rec}");
        assert_eq!(fail_rec["phase"], "receipt-out", "{fail_rec}");
    }
    assert_eq!(fs::read(&request).unwrap(), precious_bytes);
    assert_eq!(fs::read(&target_file).unwrap(), b"untouched\n");
    assert!(!artifacts_dir.exists());

    // 3. Request-declared proof/source files and explicit tool paths cannot be
    //    clobbered by `--receipt-out` even when capture fails early.
    let valid_dir = project.path().join("valid-req");
    fs::create_dir_all(valid_dir.join("src")).unwrap();
    fs::create_dir_all(valid_dir.join("proof")).unwrap();
    let src_bytes = b"pub fn bad_ref(x: &u64) -> u64 { *x }\n";
    let spec_bytes = b"prelude\n-- keep spec\n";
    let proof_bytes = b"prelude\n-- keep proof\n";
    fs::write(valid_dir.join("src/lib.rs"), src_bytes).unwrap();
    fs::write(valid_dir.join("proof/Spec.lean"), spec_bytes).unwrap();
    fs::write(valid_dir.join("proof/Proof.lean"), proof_bytes).unwrap();
    let valid_req = valid_dir.join("request.json");
    fs::write(
        &valid_req,
        r#"{
  "schema_version": 1,
  "compilation": {
    "source_root": "src",
    "crate_root": "lib.rs",
    "crate_name": "fixture",
    "edition": "2024",
    "target": "x86_64-unknown-linux-gnu",
    "source_files": ["lib.rs"]
  },
  "scope": { "kind": "crate" },
  "proof": {
    "source_root": "proof",
    "sources": [
      { "module": "Spec", "path": "Spec.lean", "role": "specification" },
      { "module": "Proof", "path": "Proof.lean", "role": "proof" }
    ]
  }
}"#,
    )
    .unwrap();
    let fake_sysroot = project.path().join("fake-sysroot");
    fs::create_dir(&fake_sysroot).unwrap();
    let fake_lean = project.path().join("fake-lean");
    fs::write(&fake_lean, b"#!/bin/sh\nexit 0\n").unwrap();
    fs::set_permissions(&fake_lean, fs::Permissions::from_mode(0o755)).unwrap();
    let fake_cap = project.path().join("fake-cap");
    fs::write(
        &fake_cap,
        "#!/bin/sh\nprintf '{\"status\":\"unsupported\",\"diagnostics\":[\"ref\"]}\\n'\nexit 1\n",
    )
    .unwrap();
    fs::set_permissions(&fake_cap, fs::Permissions::from_mode(0o755)).unwrap();

    for alias_dest in [
        valid_dir.join("proof/Proof.lean"),
        valid_dir.join("src/lib.rs"),
        fake_cap.clone(),
        fake_lean.clone(),
    ] {
        let mut alias_cmd = command(Route::Direct, project.path());
        alias_cmd
            .args(["verify", "--format", "json", "--capture"])
            .arg(&fake_cap)
            .arg("--sysroot")
            .arg(&fake_sysroot)
            .arg("--lean")
            .arg(&fake_lean)
            .arg("--request")
            .arg(&valid_req)
            .arg("--receipt-out")
            .arg(&alias_dest);
        let alias_out = alias_cmd.output().unwrap();
        assert_eq!(alias_out.status.code(), Some(2), "{alias_dest:?}: {alias_out:?}");
        let alias_rec: serde_json::Value = serde_json::from_slice(&alias_out.stdout).unwrap();
        assert_eq!(alias_rec["status"], "tool_failed", "{alias_rec}");
        assert_eq!(alias_rec["phase"], "receipt-out", "{alias_rec}");
    }

    // Also test manifest mode failing in `cargo` phase with `--receipt-out`
    // targeting both `proof/Spec.lean` and `src/lib.rs` / `Cargo.lock`.
    fs::write(
        valid_dir.join("Cargo.toml"),
        "[package]\nname = \"pm\"\nversion = \"0.1.0\"\nedition = \"2024\"\n\n[lib]\nproc-macro = true\n",
    )
    .unwrap();
    for manifest_alias in [
        valid_dir.join("proof/Spec.lean"),
        valid_dir.join("src/lib.rs"),
        valid_dir.join("Cargo.lock"),
    ] {
        let manifest_out = command(Route::Direct, project.path())
            .args(["verify", "--format", "json", "--capture"])
            .arg(&fake_cap)
            .arg("--sysroot")
            .arg(&fake_sysroot)
            .arg("--lean")
            .arg(&fake_lean)
            .arg("--manifest-path")
            .arg(valid_dir.join("Cargo.toml"))
            .arg("--proof-dir")
            .arg(valid_dir.join("proof"))
            .arg("--receipt-out")
            .arg(&manifest_alias)
            .output()
            .unwrap();
        assert_eq!(manifest_out.status.code(), Some(2), "{manifest_alias:?}: {manifest_out:?}");
        let manifest_rec: serde_json::Value = serde_json::from_slice(&manifest_out.stdout).unwrap();
        assert_eq!(manifest_rec["status"], "tool_failed", "{manifest_rec}");
        assert_eq!(manifest_rec["phase"], "receipt-out", "{manifest_rec}");
    }

    assert_eq!(fs::read(valid_dir.join("src/lib.rs")).unwrap(), src_bytes);
    assert_eq!(fs::read(valid_dir.join("proof/Spec.lean")).unwrap(), spec_bytes);
    assert_eq!(fs::read(valid_dir.join("proof/Proof.lean")).unwrap(), proof_bytes);
    assert!(fs::read_to_string(&fake_cap).unwrap().contains("unsupported"));
    assert_eq!(fs::read(&fake_lean).unwrap(), b"#!/bin/sh\nexit 0\n");

    // 4. Bare relative `--request request.json` still guards `.rs` and `.lean`
    //    files under the working directory before `load_request` runs.
    let bare_spec = project.path().join("Spec.lean");
    let bare_spec_bytes = b"prelude\n-- keep bare spec\n";
    fs::write(&bare_spec, bare_spec_bytes).unwrap();
    let mut bare_cmd = command(Route::Direct, project.path());
    bare_cmd.args([
        "verify",
        "--format",
        "json",
        "--request",
        "request.json",
        "--receipt-out",
        "Spec.lean",
    ]);
    #[cfg(not(feature = "setup"))]
    bare_cmd.args(["--capture", "cap", "--sysroot", "sys", "--lean", "lean"]);
    let bare_out = bare_cmd.output().unwrap();
    assert_eq!(bare_out.status.code(), Some(2), "{bare_out:?}");
    let bare_rec: serde_json::Value = serde_json::from_slice(&bare_out.stdout).unwrap();
    assert_eq!(bare_rec["status"], "tool_failed", "{bare_rec}");
    assert_eq!(bare_rec["phase"], "receipt-out", "{bare_rec}");
    assert_eq!(fs::read(&bare_spec).unwrap(), bare_spec_bytes);

    // 4b-4e. `.olean` cache roots and `--prebuilt-dir` bundles.
    olean_cache::olean_cache_and_prebuilt_dir_guards(
        &project,
        fake_cap,
        fake_sysroot,
        fake_lean,
        valid_req,
    );

    // 5. Unwritable `--receipt-out` parent fails before retaining `--artifacts`
    //    so `--artifacts` is never published on a `tool_failed`/`receipt-out`
    //    exit 2.
    let ro_dir = project.path().join("readonly-receipt-dir");
    fs::create_dir(&ro_dir).unwrap();
    fs::set_permissions(&ro_dir, fs::Permissions::from_mode(0o555)).unwrap();
    let probe_file = ro_dir.join("probe-write");
    match fs::write(&probe_file, b"") {
        Ok(()) => {
            let _ = fs::remove_file(&probe_file);
        }
        Err(_) => {
            let skipped_artifacts = project.path().join("unretained-artifacts");
            let mut ro_cmd = command(Route::Direct, project.path());
            ro_cmd
                .args(["verify", "--format", "json", "--request"])
                .arg(&request)
                .arg("--artifacts")
                .arg(&skipped_artifacts)
                .arg("--receipt-out")
                .arg(ro_dir.join("receipt.json"));
            #[cfg(not(feature = "setup"))]
            ro_cmd.args(["--capture", "cap", "--sysroot", "sys", "--lean", "lean"]);
            let ro_out = ro_cmd.output().unwrap();
            assert_eq!(ro_out.status.code(), Some(2), "{ro_out:?}");
            let ro_rec: serde_json::Value = serde_json::from_slice(&ro_out.stdout).unwrap();
            assert_eq!(ro_rec["status"], "tool_failed", "{ro_rec}");
            assert_eq!(ro_rec["phase"], "receipt-out", "{ro_rec}");
            assert!(ro_rec.get("artifacts").is_none(), "{ro_rec}");
            assert!(!skipped_artifacts.exists());
        }
    }
    let _ = fs::set_permissions(&ro_dir, fs::Permissions::from_mode(0o700));

    // 6. Out-of-tree `--request` input and workspace-root `Cargo.lock` cannot
    //    be overwritten even when `--artifacts` preflight fails before
    //    `load_request`, and a late aliasing failure suppresses `--artifacts`
    //    retention.
    let out_of_tree = project.path().join("oot-src");
    fs::create_dir_all(&out_of_tree).unwrap();
    let oot_data = out_of_tree.join("data.txt");
    fs::write(&oot_data, b"keep out-of-tree input\n").unwrap();
    let oot_lib = out_of_tree.join("lib.rs");
    fs::write(&oot_lib, b"pub fn keep() {}\n").unwrap();
    let oot_req_dir = project.path().join("proofs/unit");
    fs::create_dir_all(&oot_req_dir).unwrap();
    let oot_req = oot_req_dir.join("request.json");
    fs::write(
        &oot_req,
        r#"{
  "schema_version": 1,
  "compilation": {
    "source_root": "../../oot-src",
    "crate_root": "lib.rs",
    "crate_name": "oot",
    "edition": "2024",
    "target": "x86_64-unknown-linux-gnu",
    "source_files": ["lib.rs", "data.txt"]
  },
  "scope": { "kind": "crate" },
  "proof": { "source_root": ".", "sources": [] }
}"#,
    )
    .unwrap();
    let oot_fresh_art = project.path().join("oot-never-created");
    for target in [&oot_data, &oot_lib] {
        let mut oot_cmd = command(Route::Direct, project.path());
        oot_cmd
            .args(["verify", "--format", "json", "--request"])
            .arg(&oot_req)
            .arg("--artifacts")
            .arg(&oot_fresh_art)
            .arg("--receipt-out")
            .arg(target);
        #[cfg(not(feature = "setup"))]
        oot_cmd.args(["--capture", "cap", "--sysroot", "sys", "--lean", "lean"]);
        let oot_out = oot_cmd.output().unwrap();
        assert_eq!(oot_out.status.code(), Some(2), "{target:?}: {oot_out:?}");
        let oot_rec: serde_json::Value = serde_json::from_slice(&oot_out.stdout).unwrap();
        assert_eq!(oot_rec["phase"], "receipt-out", "{oot_rec}");
        assert!(oot_rec.get("artifacts").is_none(), "{oot_rec}");
    }
    assert_eq!(fs::read(&oot_data).unwrap(), b"keep out-of-tree input\n");
    assert_eq!(fs::read(&oot_lib).unwrap(), b"pub fn keep() {}\n");
    assert!(!oot_fresh_art.exists());

    // 7. Cross-directory symlinked `--request` resolves relative inputs
    //    against the canonical request target's parent (matching
    //    `load_request`), so an early `--artifacts` preflight failure cannot
    //    overwrite a declared non-`.rs`/`.lean` input.
    #[cfg(unix)]
    {
        use std::os::unix::fs::symlink;

        let link_dir = project.path().join("req-link-dir");
        fs::create_dir(&link_dir).unwrap();
        let linked_req = link_dir.join("request.json");
        symlink(&oot_req, &linked_req).unwrap();
        let existing_art = project.path().join("existing-artifacts-dir");
        fs::create_dir(&existing_art).unwrap();

        let mut sym_req_cmd = command(Route::Direct, project.path());
        sym_req_cmd
            .args(["verify", "--format", "json", "--request"])
            .arg(&linked_req)
            .arg("--artifacts")
            .arg(&existing_art)
            .arg("--receipt-out")
            .arg(&oot_data);
        #[cfg(not(feature = "setup"))]
        sym_req_cmd.args(["--capture", "cap", "--sysroot", "sys", "--lean", "lean"]);
        let sym_req_out = sym_req_cmd.output().unwrap();
        assert_eq!(sym_req_out.status.code(), Some(2), "{sym_req_out:?}");
        let sym_req_rec: serde_json::Value = serde_json::from_slice(&sym_req_out.stdout).unwrap();
        assert_eq!(sym_req_rec["phase"], "receipt-out", "{sym_req_rec}");
        assert_eq!(fs::read(&oot_data).unwrap(), b"keep out-of-tree input\n");

        // 8. `--artifacts` containing `<symlink>/..` resolves symlinks before
        //    applying `..`, blocking `--receipt-out` inside existing or
        //    aliasing non-existent `--artifacts` destinations pre-stage.
        let dir_a = project.path().join("art-dir-a");
        let dir_b_sub = project.path().join("art-dir-b/sub");
        let dir_b_ev = project.path().join("art-dir-b/ev");
        fs::create_dir_all(&dir_a).unwrap();
        fs::create_dir_all(&dir_b_sub).unwrap();
        fs::create_dir_all(&dir_b_ev).unwrap();
        symlink(&dir_b_sub, dir_a.join("link_b")).unwrap();

        let existing_sentinel = dir_b_ev.join("receipt.json");
        fs::write(&existing_sentinel, b"preserve inside artifacts\n").unwrap();
        let sym_existing_art = dir_a.join("link_b/../ev");
        let mut sym_art_cmd = command(Route::Direct, project.path());
        sym_art_cmd
            .args(["verify", "--format", "json", "--request"])
            .arg(&request)
            .arg("--artifacts")
            .arg(&sym_existing_art)
            .arg("--receipt-out")
            .arg(&existing_sentinel);
        #[cfg(not(feature = "setup"))]
        sym_art_cmd.args(["--capture", "cap", "--sysroot", "sys", "--lean", "lean"]);
        let sym_art_out = sym_art_cmd.output().unwrap();
        assert_eq!(sym_art_out.status.code(), Some(2), "{sym_art_out:?}");
        let sym_art_rec: serde_json::Value = serde_json::from_slice(&sym_art_out.stdout).unwrap();
        assert_eq!(sym_art_rec["phase"], "receipt-out", "{sym_art_rec}");
        assert_eq!(fs::read(&existing_sentinel).unwrap(), b"preserve inside artifacts\n");

        let new_ev_alias = project.path().join("art-dir-b/new-ev");
        let sym_new_art = dir_a.join("link_b/../new-ev");
        let mut sym_new_cmd = command(Route::Direct, project.path());
        sym_new_cmd
            .args(["verify", "--format", "json", "--request"])
            .arg(&request)
            .arg("--artifacts")
            .arg(&sym_new_art)
            .arg("--receipt-out")
            .arg(&new_ev_alias);
        #[cfg(not(feature = "setup"))]
        sym_new_cmd.args(["--capture", "cap", "--sysroot", "sys", "--lean", "lean"]);
        let sym_new_out = sym_new_cmd.output().unwrap();
        assert_eq!(sym_new_out.status.code(), Some(2), "{sym_new_out:?}");
        let sym_new_rec: serde_json::Value = serde_json::from_slice(&sym_new_out.stdout).unwrap();
        assert_eq!(sym_new_rec["phase"], "receipt-out", "{sym_new_rec}");
        assert!(!new_ev_alias.exists());
    }
}
