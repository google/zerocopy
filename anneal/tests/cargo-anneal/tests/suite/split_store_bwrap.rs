// Copyright 2026 The Fuchsia Authors
//
// Licensed under a BSD-style license <LICENSE-BSD>, Apache License, Version 2.0
// <LICENSE-APACHE or https://www.apache.org/licenses/LICENSE-2.0>, or the MIT
// license <LICENSE-MIT or https://opensource.org/licenses/MIT>, at your option.
// This file may not be copied, modified, or distributed except according to
// those terms.

//! Hermetic split-store `bwrap --ro-bind <store> /nix/store` integration tests.
//!
//! Exercises real `cargo-anneal verify` against a simulated Nix `symlinkJoin`
//! Lean 4.34.1 installation under `/nix/store` backed by `0o555` packages and
//! `ReadOnlyTreeGuard`, proving cross-package symlinks resolve cleanly while
//! any symlink escaping `/nix/store` fails closed inside the sandbox boundary.

use std::{
    ffi::OsStr,
    fs,
    os::unix::fs::symlink,
    path::{Path, PathBuf},
};

use anneal_testkit::{
    VerifyReceipt,
    assertions::{assert_outcome_exit, assert_rejected, assert_verified_untainted},
    store_sim::{SimulatedStoreConfig, run_in_simulated_nix_store},
};

use crate::helpers::{
    SCALAR_PROOF, SCALAR_SOURCE, SCALAR_SPEC, new_workspace, subcrate_request_json,
    workspace_tools, write_json_file,
};

fn populate_symlink_join_lean(host_lean_root: &Path, pkg: &Path) -> Result<(), String> {
    let bin_dir = pkg.join("bin");
    let lib_dir = pkg.join("lib");
    let lean_lib_dir = lib_dir.join("lean");
    fs::create_dir_all(&bin_dir).map_err(|e| e.to_string())?;
    fs::create_dir_all(&lean_lib_dir).map_err(|e| e.to_string())?;

    for entry in fs::read_dir(host_lean_root.join("bin")).map_err(|e| e.to_string())? {
        let entry = entry.map_err(|e| e.to_string())?;
        let name = entry.file_name();
        let target = Path::new("../../0001-lean-unwrapped/bin").join(&name);
        symlink(&target, bin_dir.join(&name)).map_err(|e| e.to_string())?;
    }

    for entry in fs::read_dir(host_lean_root.join("lib")).map_err(|e| e.to_string())? {
        let entry = entry.map_err(|e| e.to_string())?;
        let name = entry.file_name();
        if name == OsStr::new("lean") {
            continue;
        }
        let target = Path::new("../../0001-lean-unwrapped/lib").join(&name);
        symlink(&target, lib_dir.join(&name)).map_err(|e| e.to_string())?;
    }

    for entry in fs::read_dir(host_lean_root).map_err(|e| e.to_string())? {
        let entry = entry.map_err(|e| e.to_string())?;
        let name = entry.file_name();
        if name == OsStr::new("bin") || name == OsStr::new("lib") {
            continue;
        }
        let target = Path::new("../0001-lean-unwrapped").join(&name);
        symlink(&target, pkg.join(&name)).map_err(|e| e.to_string())?;
    }

    for entry in fs::read_dir(host_lean_root.join("lib/lean")).map_err(|e| e.to_string())? {
        let entry = entry.map_err(|e| e.to_string())?;
        let name = entry.file_name();
        let target = Path::new("../../../0001-lean-unwrapped/lib/lean").join(&name);
        symlink(&target, lean_lib_dir.join(&name)).map_err(|e| e.to_string())?;
    }
    Ok(())
}

#[cfg(target_os = "linux")]
#[test]
fn simulated_nix_store_cross_package_symlink_join_verifies_and_escape_fails_closed() {
    let tools = workspace_tools();
    let cli = tools.cli.as_deref().expect("workspace cargo-anneal binary");
    let capture = tools.capture.as_deref().expect("workspace capture binary");
    let host_lean_root = tools
        .lean
        .parent()
        .and_then(Path::parent)
        .expect("tools.lean must live under <root>/bin/lean")
        .to_path_buf();

    let mut ws = new_workspace("anneal-nix-split-");
    // Mountpoint package overmounted read-only at `0001-lean-unwrapped`.
    ws.add_store_package("0001-lean-unwrapped", true, |_| Ok(())).unwrap();
    // Valid Nix `symlinkJoin` Lean 4.34.1 tree frozen read-only (`0o555`).
    ws.add_store_package("0002-lean-joined", true, |pkg| {
        populate_symlink_join_lean(&host_lean_root, pkg)
    })
    .unwrap();
    // Symlink tree escaping `/nix/store` into `/opt/outside-escape`.
    ws.add_store_package("0003-lean-escaping", true, |pkg| {
        populate_symlink_join_lean(&host_lean_root, pkg)?;
        symlink(
            "/opt/outside-escape/Escape.olean",
            pkg.join("lib/lean/Escape.olean"),
        )
        .map_err(|e| e.to_string())
    })
    .unwrap();

    ws.write_work_file("rust/lib.rs", SCALAR_SOURCE.as_bytes()).unwrap();
    ws.write_work_file("lean/Spec.lean", SCALAR_SPEC.as_bytes()).unwrap();
    ws.write_work_file("lean/Proof.lean", SCALAR_PROOF.as_bytes()).unwrap();
    ws.write_work_file("outside-escape/Escape.olean", b"escaped olean").unwrap();

    let staged = ws.stage().unwrap();
    let work = staged.work_dir();
    for dir in ["home", "cache", "tmp"] {
        fs::create_dir_all(work.join(dir)).unwrap();
    }

    // Use in-namespace `/work/...` paths in `request.json`.
    let sandbox_work = Path::new("/work");
    let req = subcrate_request_json(
        &sandbox_work.join("rust"),
        "lib.rs",
        "scalar",
        &sandbox_work.join("lean"),
    );
    write_json_file(&work.join("request.json"), &req);

    let mut extra_ro_binds = vec![
        (host_lean_root.clone(), PathBuf::from("/nix/store/0001-lean-unwrapped")),
        (work.join("outside-escape"), PathBuf::from("/opt/outside-escape")),
        (capture.to_path_buf(), capture.to_path_buf()),
    ];
    let auto_bound = ["/usr", "/bin", "/lib", "/lib64", "/nix/store"];
    if !auto_bound.iter().any(|prefix| tools.sysroot.starts_with(prefix)) {
        extra_ro_binds.push((tools.sysroot.clone(), tools.sysroot.clone()));
    }

    let config = SimulatedStoreConfig {
        extra_ro_binds,
        environment: vec![
            ("PATH".into(), "/usr/bin:/bin".into()),
            ("HOME".into(), "/work/home".into()),
            ("XDG_CACHE_HOME".into(), "/work/cache".into()),
            ("TMPDIR".into(), "/work/tmp".into()),
            ("LD_LIBRARY_PATH".into(), tools.sysroot.join("lib").to_string_lossy().into_owned()),
        ],
    };

    fn make_verify_args<'a>(
        allow_unpinned: bool,
        lean_bin: &'a OsStr,
        artifacts: &'a OsStr,
        capture: &'a OsStr,
        sysroot: &'a OsStr,
    ) -> Vec<&'a OsStr> {
        let mut args = vec![OsStr::new("verify"), OsStr::new("--format"), OsStr::new("json")];
        if allow_unpinned {
            args.push(OsStr::new("--allow-unpinned-lean"));
        }
        args.extend([
            OsStr::new("--request"),
            OsStr::new("/work/request.json"),
            OsStr::new("--artifacts"),
            artifacts,
            OsStr::new("--capture"),
            capture,
            OsStr::new("--lean"),
            lean_bin,
            OsStr::new("--sysroot"),
            sysroot,
        ]);
        args
    }

    // 1. Pinned Nix-store package (`0001-lean-unwrapped`) verifies untainted.
    let pinned_args = make_verify_args(
        false,
        OsStr::new("/nix/store/0001-lean-unwrapped/bin/lean"),
        OsStr::new("/work/art-pinned"),
        capture.as_os_str(),
        tools.sysroot.as_os_str(),
    );
    let pinned_out = run_in_simulated_nix_store(&staged, cli, &pinned_args, &config).unwrap();
    assert_outcome_exit(&pinned_out, 0).unwrap();
    let pinned_receipt = VerifyReceipt::from_json_slice(&pinned_out.stdout)
        .unwrap_or_else(|e| panic!("parse pinned receipt: {e}\n{}", pinned_out.describe()));
    let pinned_ok = assert_verified_untainted(&pinned_receipt).unwrap();
    assert_eq!(pinned_ok.status, "crate_verified");
    assert!(
        matches!(
            pinned_ok.elaboration_sandbox.as_deref(),
            Some("linux_bwrap" | "linux_landlock_seccomp")
        ),
        "expected active sandbox inside split store, got {:?}",
        pinned_ok.elaboration_sandbox
    );

    // 2. Strict pinned mode refuses symlinked sysroots in `0002-lean-joined`.
    let strict_sym_args = make_verify_args(
        false,
        OsStr::new("/nix/store/0002-lean-joined/bin/lean"),
        OsStr::new("/work/art-strict-sym"),
        capture.as_os_str(),
        tools.sysroot.as_os_str(),
    );
    let strict_sym_out =
        run_in_simulated_nix_store(&staged, cli, &strict_sym_args, &config).unwrap();
    assert_outcome_exit(&strict_sym_out, 1).unwrap();
    let strict_sym_receipt = VerifyReceipt::from_json_slice(&strict_sym_out.stdout)
        .unwrap_or_else(|e| panic!("parse strict receipt: {e}\n{}", strict_sym_out.describe()));
    assert_rejected(
        &strict_sym_receipt,
        "proof_failed",
        Some("audit"),
        "symlink forbidden in sysroot",
    )
    .unwrap();

    // 3. Cross-package Nix `symlinkJoin` under `--allow-unpinned-lean` verifies
    //    inside the containment sandbox with `/nix/store -> /nix/store` links.
    let joined_args = make_verify_args(
        true,
        OsStr::new("/nix/store/0002-lean-joined/bin/lean"),
        OsStr::new("/work/art-joined"),
        capture.as_os_str(),
        tools.sysroot.as_os_str(),
    );
    let joined_out = run_in_simulated_nix_store(&staged, cli, &joined_args, &config).unwrap();
    assert_outcome_exit(&joined_out, 0).unwrap();
    let joined_receipt = VerifyReceipt::from_json_slice(&joined_out.stdout)
        .unwrap_or_else(|e| panic!("parse joined receipt: {e}\n{}", joined_out.describe()));
    let VerifyReceipt::Verified(joined_ok) = &joined_receipt else {
        panic!("expected verified receipt for symlinkJoin store, got {joined_receipt:?}");
    };
    assert_eq!(joined_ok.status, "tainted_crate_verified");
    assert_eq!(joined_ok.taint_reasons, vec!["unpinned_lean"]);
    assert_eq!(joined_ok.audit.get("replay").and_then(serde_json::Value::as_bool), Some(true));
    assert!(
        matches!(
            joined_ok.elaboration_sandbox.as_deref(),
            Some("linux_bwrap" | "linux_landlock_seccomp")
        ),
        "expected active sandbox for symlinkJoin, got {:?}",
        joined_ok.elaboration_sandbox
    );

    // 4. Symlink escaping `/nix/store` fails closed before executing Lean.
    let esc_args = make_verify_args(
        true,
        OsStr::new("/nix/store/0003-lean-escaping/bin/lean"),
        OsStr::new("/work/art-escape"),
        capture.as_os_str(),
        tools.sysroot.as_os_str(),
    );
    let esc_out = run_in_simulated_nix_store(&staged, cli, &esc_args, &config).unwrap();
    assert_outcome_exit(&esc_out, 2).unwrap();
    let esc_receipt = VerifyReceipt::from_json_slice(&esc_out.stdout)
        .unwrap_or_else(|e| panic!("parse escape receipt: {e}\n{}", esc_out.describe()));
    assert_rejected(&esc_receipt, "tool_failed", Some("audit"), "refusing escaping symlink")
        .unwrap();
}
