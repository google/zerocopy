// Copyright 2026 The Fuchsia Authors
//
// Licensed under a BSD-style license <LICENSE-BSD>, Apache License, Version 2.0
// <LICENSE-APACHE or https://www.apache.org/licenses/LICENSE-2.0>, or the MIT
// license <LICENSE-MIT or https://opensource.org/licenses/MIT>, at your option.
// This file may not be copied, modified, or distributed except according to
// those terms.

//! End-to-end verification + `cargo anneal inspect` integration check.

use std::{fs, process::Command};

use crate::helpers::{
    expect_verified, new_workspace, run_verify_strs, workspace_tools, write_json_file,
    write_scalar_baseline,
};

#[test]
fn real_verify_receipt_and_artifacts_pass_strict_inspect() {
    let staged = new_workspace("anneal-inspect-e2e-").stage().unwrap();
    let request = write_scalar_baseline(staged.work_dir());
    write_json_file(&staged.work_dir().join("request.json"), &request);
    let artifacts_dir = staged.work_dir().join("retained_artifacts");

    let run = run_verify_strs(
        &staged,
        &["--request", "request.json", "--artifacts", "retained_artifacts"],
    );
    let _receipt = expect_verified(&run, "crate_verified", true);

    let receipt_file = staged.work_dir().join("receipt.json");
    fs::write(&receipt_file, &run.process.stdout).unwrap();

    let cli = workspace_tools().cli.as_deref().expect("cargo-anneal binary");
    // Bare default invocation must pass on a clean, untainted receipt.
    let bare = Command::new(cli)
        .args(["inspect", receipt_file.to_str().unwrap(), "--unknown-fields", "deny"])
        .output()
        .expect("run bare cargo anneal inspect on real receipt");
    assert!(
        bare.status.success(),
        "bare inspect failed: code={:?}\nstdout={}\nstderr={}",
        bare.status.code(),
        String::from_utf8_lossy(&bare.stdout),
        String::from_utf8_lossy(&bare.stderr)
    );
    for fmt in ["json", "human", "ledger", "markdown"] {
        let out = Command::new(cli)
            .args([
                "inspect",
                receipt_file.to_str().unwrap(),
                "--verify-artifacts",
                artifacts_dir.to_str().unwrap(),
                "--require-exact-artifacts",
                "--unknown-fields",
                "deny",
                "--check",
                "--require-untainted",
                "--require-crate-scope",
                "--format",
                fmt,
                "--color",
                "never",
            ])
            .output()
            .expect("run cargo anneal inspect on real receipt");
        assert!(
            out.status.success(),
            "inspect ({fmt}) failed: code={:?}\nstdout={}\nstderr={}",
            out.status.code(),
            String::from_utf8_lossy(&out.stdout),
            String::from_utf8_lossy(&out.stderr)
        );
    }
}
