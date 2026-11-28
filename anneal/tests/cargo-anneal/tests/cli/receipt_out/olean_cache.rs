// Copyright 2026 The Fuchsia Authors
//
// Licensed under a BSD-style license <LICENSE-BSD>, Apache License, Version 2.0
// <LICENSE-APACHE or https://www.apache.org/licenses/LICENSE-2.0>, or the MIT
// license <LICENSE-MIT or https://opensource.org/licenses/MIT>, at your option.
// This file may not be copied, modified, or distributed except according to
// those terms.

//! `--receipt-out` and `.olean` cache-root guards: the shared cache named by
//! `--olean-cache-dir`, `ANNEAL_OLEAN_CACHE_DIR`, or the per-user default,
//! and explicit `--prebuilt-dir` bundles.

use super::*;

/// Sections 4b-4e of
/// `receipt_out_persists_valid_v3_json_and_rejects_symlinks_dirs_and_input_aliases`,
/// run against the fake capture, sysroot, and Lean tools and the valid request
/// that section 3 writes under `project`.
pub(super) fn olean_cache_and_prebuilt_dir_guards(
    project: &tempfile::TempDir,
    fake_cap: std::path::PathBuf,
    fake_sysroot: std::path::PathBuf,
    fake_lean: std::path::PathBuf,
    valid_req: std::path::PathBuf,
) {
    use std::fs;

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
}
