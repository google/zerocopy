// Copyright 2026 The Fuchsia Authors
//
// Licensed under a BSD-style license <LICENSE-BSD>, Apache License, Version 2.0
// <LICENSE-APACHE or https://www.apache.org/licenses/LICENSE-2.0>, or the MIT
// license <LICENSE-MIT or https://opensource.org/licenses/MIT>, at your option.
// This file may not be copied, modified, or distributed except according to
// those terms.

//! Stale passing `--receipt-out` receipts are invalidated before capture
//! and when the receipt write fails.

use super::*;

#[cfg(unix)]
#[test]
fn receipt_out_invalidates_stale_passing_receipt_before_capture_and_on_write_failure() {
    use std::{fs, os::unix::fs::PermissionsExt as _};

    let project = tempfile::tempdir().unwrap();
    let src_dir = project.path().join("src");
    let proof_dir = project.path().join("proof");
    let out_dir = project.path().join("out");
    fs::create_dir_all(&src_dir).unwrap();
    fs::create_dir_all(&proof_dir).unwrap();
    fs::create_dir_all(&out_dir).unwrap();
    fs::write(src_dir.join("lib.rs"), b"pub fn zero() -> u64 { 0 }\n").unwrap();
    fs::write(proof_dir.join("Spec.lean"), b"prelude\n").unwrap();
    fs::write(proof_dir.join("Proof.lean"), b"prelude\n").unwrap();
    let req_path = project.path().join("request.json");
    fs::write(
        &req_path,
        r#"{
  "schema_version": 1,
  "compilation": {
    "source_root": "src",
    "crate_root": "lib.rs",
    "crate_name": "stale_demo",
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
    let fake_sysroot = project.path().join("sysroot");
    fs::create_dir(&fake_sysroot).unwrap();
    let fake_lean = project.path().join("fake-lean");
    fs::write(&fake_lean, b"#!/bin/sh\nexit 0\n").unwrap();
    fs::set_permissions(&fake_lean, fs::Permissions::from_mode(0o755)).unwrap();

    // 1. Pre-existing passing receipt is unlinked BEFORE capture runs; even if
    //    capture subsequently fails and the destination parent becomes
    //    unwritable (simulating ENOSPC/EACCES on failure-receipt write), no
    //    stale `crate_verified` receipt remains on disk.
    let stale_receipt = out_dir.join("receipt.json");
    let stale_pass = br#"{"schema_version":3,"status":"crate_verified"}"#;
    fs::write(&stale_receipt, stale_pass).unwrap();
    let seen_absent_marker = project.path().join("capture-saw-absent");
    let fake_cap = project.path().join("fake-cap");
    fs::write(
        &fake_cap,
        format!(
            "#!/bin/sh\n\
             if [ ! -e '{}' ]; then printf 'absent' > '{}'; fi\n\
             chmod 0555 '{}'\n\
             printf '{{\"status\":\"unsupported\",\"diagnostics\":[\"ref\"]}}\\n'\n\
             exit 1\n",
            stale_receipt.display(),
            seen_absent_marker.display(),
            out_dir.display(),
        ),
    )
    .unwrap();
    fs::set_permissions(&fake_cap, fs::Permissions::from_mode(0o755)).unwrap();

    let out = command(Route::Direct, project.path())
        .args(["verify", "--format", "json", "--capture"])
        .arg(&fake_cap)
        .arg("--sysroot")
        .arg(&fake_sysroot)
        .arg("--lean")
        .arg(&fake_lean)
        .arg("--request")
        .arg(&req_path)
        .arg("--receipt-out")
        .arg(&stale_receipt)
        .output()
        .unwrap();
    let _ = fs::set_permissions(&out_dir, fs::Permissions::from_mode(0o700));
    assert_eq!(
        fs::read_to_string(&seen_absent_marker).unwrap_or_default(),
        "absent",
        "stale receipt must be unlinked before capture begins"
    );
    // Non-root users get exit 2 (`receipt-out`) with `stale_receipt` absent;
    // root ignores `0555` and writes the new `unsupported` failure receipt.
    // Either way, the stale `crate_verified` payload is NEVER preserved.
    assert_ne!(out.status.code(), Some(0), "{out:?}");
    if stale_receipt.exists() {
        let written: serde_json::Value =
            serde_json::from_slice(&fs::read(&stale_receipt).unwrap()).unwrap();
        assert_ne!(written["status"], "crate_verified", "{written}");
        assert_eq!(written["status"], "unsupported", "{written}");
    } else {
        assert_eq!(out.status.code(), Some(2), "{out:?}");
        let rec: serde_json::Value = serde_json::from_slice(&out.stdout).unwrap();
        assert_eq!(rec["status"], "tool_failed", "{rec}");
        assert_eq!(rec["phase"], "receipt-out", "{rec}");
    }

    // 2. If `--receipt-out` starts as a stale file inside an already-unwritable
    //    directory, invalidation fails closed BEFORE capture is invoked.
    let ro_dir = project.path().join("ro-stale-dir");
    fs::create_dir(&ro_dir).unwrap();
    let ro_stale = ro_dir.join("receipt.json");
    fs::write(&ro_stale, stale_pass).unwrap();
    fs::set_permissions(&ro_dir, fs::Permissions::from_mode(0o555)).unwrap();
    let probe = ro_dir.join("probe");
    match fs::write(&probe, b"") {
        Ok(()) => {
            let _ = fs::remove_file(&probe);
        }
        Err(_) => {
            let cap_ran_marker = project.path().join("ro-cap-ran");
            let fake_cap2 = project.path().join("fake-cap-2");
            fs::write(
                &fake_cap2,
                format!("#!/bin/sh\nprintf 'ran' > '{}'\nexit 1\n", cap_ran_marker.display()),
            )
            .unwrap();
            fs::set_permissions(&fake_cap2, fs::Permissions::from_mode(0o755)).unwrap();
            let ro_out = command(Route::Direct, project.path())
                .args(["verify", "--format", "json", "--capture"])
                .arg(&fake_cap2)
                .arg("--sysroot")
                .arg(&fake_sysroot)
                .arg("--lean")
                .arg(&fake_lean)
                .arg("--request")
                .arg(&req_path)
                .arg("--receipt-out")
                .arg(&ro_stale)
                .output()
                .unwrap();
            assert_eq!(ro_out.status.code(), Some(2), "{ro_out:?}");
            let ro_rec: serde_json::Value = serde_json::from_slice(&ro_out.stdout).unwrap();
            assert_eq!(ro_rec["status"], "tool_failed", "{ro_rec}");
            assert_eq!(ro_rec["phase"], "receipt-out", "{ro_rec}");
            assert!(!cap_ran_marker.exists(), "capture must not run when stale unlink fails");
        }
    }
    let _ = fs::set_permissions(&ro_dir, fs::Permissions::from_mode(0o700));
}
