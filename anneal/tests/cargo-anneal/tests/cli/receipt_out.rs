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

    // 4b. `--receipt-out` must not land inside the shared `.olean` cache that
    //     verification will use, whether it is named by `--olean-cache-dir`,
    //     by `ANNEAL_OLEAN_CACHE_DIR`, or by a `<symlink>/..` spelling that
    //     the filesystem would resolve elsewhere. `--olean-cache-dir`
    //     conflicts with `--no-cache` and must not be empty.
    let olean_cache = project.path().join("shared-olean-cache");
    fs::create_dir(&olean_cache).unwrap();
    let inside_cache = olean_cache.join("receipt.json");
    let decoy_target = project.path().join("decoy/sub");
    fs::create_dir_all(&decoy_target).unwrap();
    std::os::unix::fs::symlink(&decoy_target, project.path().join("cache-link")).unwrap();
    let dotdot_cache = project.path().join("cache-link/../shared-olean-cache");
    let verify_with_fakes = |extra: &[&std::ffi::OsStr]| {
        let mut cmd = command(Route::Direct, project.path());
        cmd.args(["verify", "--format", "json", "--capture"])
            .arg(&fake_cap)
            .arg("--sysroot")
            .arg(&fake_sysroot)
            .arg("--lean")
            .arg(&fake_lean)
            .arg("--request")
            .arg(&valid_req)
            .args(extra)
            .env_remove("ANNEAL_OLEAN_CACHE_DIR");
        cmd
    };
    for (first, second) in
        [("--no-cache", "--olean-cache-dir"), ("--olean-cache-dir", "--no-cache")]
    {
        let mut conflict_cmd = verify_with_fakes(&[]);
        for flag in [first, second] {
            conflict_cmd.arg(flag);
            if flag == "--olean-cache-dir" {
                conflict_cmd.arg(&olean_cache);
            }
        }
        let conflict = conflict_cmd.output().unwrap();
        let stderr = String::from_utf8_lossy(&conflict.stderr);
        assert_eq!(conflict.status.code(), Some(2), "{conflict:?}");
        assert!(conflict.stdout.is_empty(), "{conflict:?}");
        assert!(
            stderr.contains(&format!("the argument '{first}"))
                && stderr.contains(&format!("cannot be used with '{second}")),
            "{stderr}"
        );
    }
    let empty = verify_with_fakes(&["--olean-cache-dir".as_ref(), "".as_ref()]).output().unwrap();
    assert_eq!(empty.status.code(), Some(2), "{empty:?}");
    assert!(empty.stdout.is_empty(), "{empty:?}");
    assert!(
        String::from_utf8_lossy(&empty.stderr)
            .contains("a value is required for '--olean-cache-dir <DIR>'"),
        "{empty:?}"
    );
    for (case, flag, env) in [
        ("flag", Some(&olean_cache), None),
        ("env", None, Some(&olean_cache)),
        ("dotdot", Some(&dotdot_cache), None),
    ] {
        let mut cache_cmd = verify_with_fakes(&["--receipt-out".as_ref(), inside_cache.as_ref()]);
        if let Some(flag) = flag {
            cache_cmd.arg("--olean-cache-dir").arg(flag);
        }
        if let Some(env) = env {
            cache_cmd.env("ANNEAL_OLEAN_CACHE_DIR", env);
        }
        let cache_out = cache_cmd.output().unwrap();
        assert_eq!(cache_out.status.code(), Some(2), "{case}: {cache_out:?}");
        let cache_rec: serde_json::Value = serde_json::from_slice(&cache_out.stdout).unwrap();
        assert_eq!(cache_rec["phase"], "receipt-out", "{case}: {cache_rec}");
        assert!(
            cache_rec["detail"].as_str().unwrap_or("").contains(".olean cache directory"),
            "{case}: {cache_rec}"
        );
        assert!(!inside_cache.exists(), "{case}");
    }
    // An `ANNEAL_OLEAN_CACHE_DIR` that verification ignores, because
    // `--olean-cache-dir` overrides it or `--no-cache` disables the disk
    // cache, is not protected.
    let other_cache = project.path().join("other-olean-cache");
    for (case, extra) in [
        ("overridden", vec!["--olean-cache-dir".as_ref(), other_cache.as_os_str()]),
        ("no-cache", vec!["--no-cache".as_ref()]),
    ] {
        let mut ignored_cmd = verify_with_fakes(&extra);
        ignored_cmd
            .arg("--receipt-out")
            .arg(&inside_cache)
            .env("ANNEAL_OLEAN_CACHE_DIR", &olean_cache);
        let ignored_out = ignored_cmd.output().unwrap();
        let ignored_rec: serde_json::Value = serde_json::from_slice(&ignored_out.stdout).unwrap();
        assert!(
            !ignored_rec["detail"].as_str().unwrap_or("").contains(".olean cache directory"),
            "{case}: {ignored_rec}"
        );
        assert_ne!(ignored_rec["phase"], "receipt-out", "{case}: {ignored_rec}");
        let _ = fs::remove_file(&inside_cache);
    }

    // 4c. An overriding cache root that the checkout could populate (here,
    //     inside the working directory, which also holds the request) is
    //     refused before staging, whether it comes from the flag or the
    //     environment; a root outside the checkout passes this check. The
    //     refusal also replaces a stale passing `--receipt-out` receipt.
    let receipt_dir = tempfile::tempdir().unwrap();
    let stale_receipt = receipt_dir.path().join("receipt.json");
    for (case, flag, env) in [("flag", Some(&olean_cache), None), ("env", None, Some(&olean_cache))]
    {
        fs::write(&stale_receipt, br#"{"schema_version":3,"status":"crate_verified"}"#).unwrap();
        let mut root_cmd =
            verify_with_fakes(&["--receipt-out".as_ref(), stale_receipt.as_os_str()]);
        if let Some(flag) = flag {
            root_cmd.arg("--olean-cache-dir").arg(flag);
        }
        if let Some(env) = env {
            root_cmd.env("ANNEAL_OLEAN_CACHE_DIR", env);
        }
        let root_out = root_cmd.output().unwrap();
        assert_eq!(root_out.status.code(), Some(2), "{case}: {root_out:?}");
        let root_rec: serde_json::Value = serde_json::from_slice(&root_out.stdout).unwrap();
        assert_eq!(root_rec["phase"], "olean-cache", "{case}: {root_rec}");
        assert!(
            root_rec["detail"].as_str().unwrap_or("").contains("must not be inside or contain"),
            "{case}: {root_rec}"
        );
        let written: serde_json::Value =
            serde_json::from_slice(&fs::read(&stale_receipt).unwrap()).unwrap();
        assert_eq!(written["phase"], "olean-cache", "{case}: {written}");
    }
    let outside_root = tempfile::tempdir().unwrap();
    let outside_out = verify_with_fakes(&[
        "--olean-cache-dir".as_ref(),
        outside_root.path().join("cache").as_os_str(),
    ])
    .output()
    .unwrap();
    let outside_rec: serde_json::Value = serde_json::from_slice(&outside_out.stdout).unwrap();
    assert_ne!(outside_rec["phase"], "olean-cache", "{outside_rec}");

    // 4d. Without an override, `--receipt-out` must not land inside the
    //     per-user default cache either.
    #[cfg(target_os = "linux")]
    {
        let home = tempfile::tempdir().unwrap();
        let default_cache = home.path().join(".cache/anneal/olean-cache");
        fs::create_dir_all(&default_cache).unwrap();
        let default_receipt = default_cache.join("receipt.json");
        let default_out = verify_with_fakes(&["--receipt-out".as_ref(), default_receipt.as_ref()])
            .env("HOME", home.path())
            .env_remove("XDG_CACHE_HOME")
            .output()
            .unwrap();
        assert_eq!(default_out.status.code(), Some(2), "{default_out:?}");
        let default_rec: serde_json::Value = serde_json::from_slice(&default_out.stdout).unwrap();
        assert_eq!(default_rec["phase"], "receipt-out", "{default_rec}");
        assert!(
            default_rec["detail"].as_str().unwrap_or("").contains(".olean cache directory"),
            "{default_rec}"
        );
        assert!(!default_receipt.exists());

        // Run from `HOME`, which contains the per-user cache base, the
        // default cache passes the checkout-overlap check, and so does an
        // explicit root (flag or environment) anywhere under that base. A
        // root elsewhere under `HOME` or containing the working directory is
        // still refused, as is a root inside the working directory when the
        // working directory is, or lies inside, the cache base rather than
        // strictly above it.
        let from_home = |root: Option<&Path>, env: Option<&Path>, xdg: Option<&Path>| {
            let mut cmd = command(Route::Direct, home.path());
            cmd.args(["verify", "--format", "json", "--capture"])
                .arg(&fake_cap)
                .arg("--sysroot")
                .arg(&fake_sysroot)
                .arg("--lean")
                .arg(&fake_lean)
                .arg("--request")
                .arg(&valid_req)
                .env("HOME", home.path())
                .env_remove("ANNEAL_OLEAN_CACHE_DIR")
                .env_remove("XDG_CACHE_HOME");
            if let Some(root) = root {
                cmd.arg("--olean-cache-dir").arg(root);
            }
            if let Some(env) = env {
                cmd.env("ANNEAL_OLEAN_CACHE_DIR", env);
            }
            if let Some(xdg) = xdg {
                cmd.env("XDG_CACHE_HOME", xdg);
            }
            let out = cmd.output().unwrap();
            serde_json::from_slice::<serde_json::Value>(&out.stdout).unwrap()
        };
        let h = |rel: &str| home.path().join(rel);
        let xdg = h("xdg-cache");
        let above_home = home.path().parent().unwrap();
        fs::create_dir(h("xdg-real")).unwrap();
        std::os::unix::fs::symlink(h("xdg-real"), h("xdg-link")).unwrap();
        let xdg_link = h("xdg-link");
        for (case, root, env, xdg) in [
            ("default", None, None, None),
            ("flag naming the default", Some(default_cache.clone()), None, None),
            ("flag beside the default", Some(h(".cache/shared-olean")), None, None),
            ("env beside the default", None, Some(h(".cache/shared-olean")), None),
            ("flag under XDG base", Some(xdg.join("shared-olean")), None, Some(xdg.as_path())),
            ("flag under symlinked base", Some(xdg_link.join("c")), None, Some(xdg_link.as_path())),
        ] {
            let rec = from_home(root.as_deref(), env.as_deref(), xdg);
            assert_ne!(rec["phase"], "olean-cache", "{case}: {rec}");
        }
        fs::create_dir_all(h(".cache")).unwrap();
        fs::create_dir_all(h("checkout-sub")).unwrap();
        std::os::unix::fs::symlink(h("checkout-sub"), h(".cache/escape")).unwrap();
        for (case, root, xdg) in [
            ("elsewhere under HOME", h("olean-cache"), None),
            ("HOME itself", home.path().to_path_buf(), None),
            ("symlink under cache base escaping into HOME", h(".cache/escape/c"), None),
            ("outside XDG_CACHE_HOME", h(".cache/shared-olean"), Some(xdg.as_path())),
            ("working directory inside the base", h("olean-cache"), Some(above_home)),
            ("base at the working directory", h("olean-cache"), Some(home.path())),
        ] {
            let rec = from_home(Some(&root), None, xdg);
            assert_eq!(rec["phase"], "olean-cache", "{case}: {rec}");
            assert!(
                rec["detail"].as_str().unwrap_or("").contains("must not be inside or contain"),
                "{case}: {rec}"
            );
        }
        // A real input directory (`--proof-dir`) at `HOME` strictly contains
        // `.cache`, yet still refuses an `.olean` cache root under `.cache`;
        // likewise `--prebuilt-dir` under `.cache` receives no cache-base
        // exception when run from `HOME`.
        let mut proof_at_home = command(Route::Direct, home.path());
        proof_at_home
            .args(["verify", "--format", "json", "--capture"])
            .arg(&fake_cap)
            .arg("--sysroot")
            .arg(&fake_sysroot)
            .arg("--lean")
            .arg(&fake_lean)
            .arg("--manifest-path")
            .arg(project.path().join("Cargo.toml"))
            .arg("--proof-dir")
            .arg(home.path())
            .arg("--olean-cache-dir")
            .arg(h(".cache/shared-olean"))
            .env("HOME", home.path())
            .env_remove("ANNEAL_OLEAN_CACHE_DIR")
            .env_remove("XDG_CACHE_HOME");
        let proof_rec: serde_json::Value =
            serde_json::from_slice(&proof_at_home.output().unwrap().stdout).unwrap();
        assert_eq!(proof_rec["phase"], "olean-cache", "{proof_rec}");
        assert!(
            proof_rec["detail"].as_str().unwrap_or("").contains("--proof-dir"),
            "{proof_rec}"
        );
        fs::create_dir_all(h(".cache/prebuilt")).unwrap();
        fs::write(h(".cache/prebuilt/manifest.json"), br#"{"schema_version":2,"entries":[]}"#)
            .unwrap();
        let mut prebuilt_in_home_cache = command(Route::Direct, home.path());
        prebuilt_in_home_cache
            .args(["verify", "--format", "json", "--capture"])
            .arg(&fake_cap)
            .arg("--sysroot")
            .arg(&fake_sysroot)
            .arg("--lean")
            .arg(&fake_lean)
            .arg("--request")
            .arg(&valid_req)
            .arg("--prebuilt-dir")
            .arg(h(".cache/prebuilt"))
            .env("HOME", home.path())
            .env_remove("ANNEAL_OLEAN_CACHE_DIR")
            .env_remove("XDG_CACHE_HOME");
        let prebuilt_rec: serde_json::Value =
            serde_json::from_slice(&prebuilt_in_home_cache.output().unwrap().stdout).unwrap();
        assert_eq!(prebuilt_rec["phase"], "olean-cache", "{prebuilt_rec}");
        let prebuilt_detail = prebuilt_rec["detail"].as_str().unwrap_or("");
        assert!(
            prebuilt_detail.contains("prebuilt .olean directory")
                && prebuilt_detail.contains("working directory"),
            "{prebuilt_rec}"
        );
    }

    // 4e. An explicit `--prebuilt-dir` conflicts with `--no-cache`, must lie
    //     outside the checkout, and must already be a real directory holding
    //     a regular `manifest.json`; otherwise verification fails before
    //     staging rather than compiling the modules the bundle should
    //     provide. The refusal replaces a stale passing receipt, and
    //     `--receipt-out` must not land inside the bundle.
    for (first, second) in [("--no-cache", "--prebuilt-dir"), ("--prebuilt-dir", "--no-cache")] {
        let mut conflict_cmd = verify_with_fakes(&[]);
        for flag in [first, second] {
            conflict_cmd.arg(flag);
            if flag == "--prebuilt-dir" {
                conflict_cmd.arg(&olean_cache);
            }
        }
        let conflict = conflict_cmd.output().unwrap();
        let stderr = String::from_utf8_lossy(&conflict.stderr);
        assert_eq!(conflict.status.code(), Some(2), "{conflict:?}");
        assert!(conflict.stdout.is_empty(), "{conflict:?}");
        assert!(
            stderr.contains(&format!("the argument '{first}"))
                && stderr.contains(&format!("cannot be used with '{second}")),
            "{stderr}"
        );
    }
    let empty = verify_with_fakes(&["--prebuilt-dir".as_ref(), "".as_ref()]).output().unwrap();
    assert_eq!(empty.status.code(), Some(2), "{empty:?}");
    assert!(empty.stdout.is_empty(), "{empty:?}");
    assert!(
        String::from_utf8_lossy(&empty.stderr)
            .contains("a value is required for '--prebuilt-dir <DIR>'"),
        "{empty:?}"
    );
    let bundles = tempfile::tempdir().unwrap();
    let b = |rel: &str| bundles.path().join(rel);
    fs::create_dir_all(b("good")).unwrap();
    fs::write(b("good/manifest.json"), br#"{"schema_version":2,"entries":[]}"#).unwrap();
    fs::create_dir_all(b("empty")).unwrap();
    fs::write(b("file"), b"").unwrap();
    std::os::unix::fs::symlink(b("good"), b("link")).unwrap();
    let in_checkout = project.path().join("prebuilt-in-checkout");
    fs::create_dir_all(&in_checkout).unwrap();
    fs::write(in_checkout.join("manifest.json"), br#"{"schema_version":2,"entries":[]}"#).unwrap();
    for (case, dir, needle) in [
        ("missing", b("missing"), "does not exist"),
        ("file", b("file"), "is not a directory"),
        ("symlink", b("link"), "must not be a symlink"),
        ("no-manifest", b("empty"), "manifest.json does not exist"),
        ("in-checkout", in_checkout.clone(), "must not be inside or contain"),
    ] {
        fs::write(&stale_receipt, br#"{"schema_version":3,"status":"crate_verified"}"#).unwrap();
        let out = verify_with_fakes(&[
            "--prebuilt-dir".as_ref(),
            dir.as_os_str(),
            "--receipt-out".as_ref(),
            stale_receipt.as_os_str(),
        ])
        .output()
        .unwrap();
        assert_eq!(out.status.code(), Some(2), "{case}: {out:?}");
        let rec: serde_json::Value = serde_json::from_slice(&out.stdout).unwrap();
        assert_eq!(rec["phase"], "olean-cache", "{case}: {rec}");
        assert!(rec["detail"].as_str().unwrap_or("").contains(needle), "{case}: {rec}");
        let written: serde_json::Value =
            serde_json::from_slice(&fs::read(&stale_receipt).unwrap()).unwrap();
        assert_eq!(written["phase"], "olean-cache", "{case}: {written}");
    }
    let inside_bundle = b("good/receipt.json");
    let bundle_receipt = verify_with_fakes(&[
        "--prebuilt-dir".as_ref(),
        b("good").as_os_str(),
        "--receipt-out".as_ref(),
        inside_bundle.as_os_str(),
    ])
    .output()
    .unwrap();
    assert_eq!(bundle_receipt.status.code(), Some(2), "{bundle_receipt:?}");
    let bundle_rec: serde_json::Value = serde_json::from_slice(&bundle_receipt.stdout).unwrap();
    assert_eq!(bundle_rec["phase"], "receipt-out", "{bundle_rec}");
    assert!(
        bundle_rec["detail"].as_str().unwrap_or("").contains(".olean cache directory"),
        "{bundle_rec}"
    );
    assert!(!inside_bundle.exists());
    let good_out =
        verify_with_fakes(&["--prebuilt-dir".as_ref(), b("good").as_os_str()]).output().unwrap();
    let good_rec: serde_json::Value = serde_json::from_slice(&good_out.stdout).unwrap();
    assert_ne!(good_rec["phase"], "olean-cache", "{good_rec}");

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
