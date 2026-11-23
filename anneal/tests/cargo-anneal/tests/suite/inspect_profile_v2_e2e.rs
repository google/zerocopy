// Copyright 2026 The Fuchsia Authors
//
// Licensed under a BSD-style license <LICENSE-BSD>, Apache License, Version 2.0
// <LICENSE-APACHE or https://www.apache.org/licenses/LICENSE-2.0>, or the MIT
// license <LICENSE-MIT or https://opensource.org/licenses/MIT>, at your option.
// This file may not be copied, modified, or distributed except according to
// those terms.

//! End-to-end Profile v2 `cargo anneal verify` + `inspect` on real `zerocopy`.

use std::{ffi::OsStr, fs, path::Path, process::Command};

use serde_json::{Value, json};

use crate::helpers::{
    expect_verified, new_workspace, run_verify_inv, verify_invocation, workspace_tools,
    write_json_file,
};

const ZEROCOPY_PROFILE_V2_SPEC: &str = include_str!("../fixtures/profile_v2_zerocopy/Spec.lean");
const ZEROCOPY_PROFILE_V2_PROOF: &str = include_str!("../fixtures/profile_v2_zerocopy/Proof.lean");

const ZEROCOPY_SOURCE_FILES: &[&str] = &[
    "byte_slice.rs",
    "byteorder.rs",
    "deprecated.rs",
    "error.rs",
    "impls.rs",
    "layout.rs",
    "lib.rs",
    "macros.rs",
    "pointer/inner.rs",
    "pointer/invariant.rs",
    "pointer/mod.rs",
    "pointer/ptr.rs",
    "pointer/transmute.rs",
    "ref.rs",
    "split_at.rs",
    "util/macro_util.rs",
    "util/macros.rs",
    "util/mod.rs",
    "wrappers.rs",
];

#[test]
fn real_profile_v2_zerocopy_receipt_and_artifacts_pass_strict_inspect_e2e() {
    let staged = new_workspace("anneal-inspect-v2-e2e-").stage().unwrap();
    let work = staged.work_dir();
    let lean_dir = work.join("lean");
    let art_dir = work.join("artifacts");
    fs::create_dir_all(&lean_dir).unwrap();
    fs::write(lean_dir.join("Spec.lean"), ZEROCOPY_PROFILE_V2_SPEC).unwrap();
    fs::write(lean_dir.join("Proof.lean"), ZEROCOPY_PROFILE_V2_PROOF).unwrap();

    let zerocopy_src =
        fs::canonicalize(Path::new(env!("CARGO_MANIFEST_DIR")).join("../../../zerocopy/src"))
            .expect("resolve zerocopy/src");
    let request = json!({
        "schema_version": 1,
        "compilation": {
            "source_root": zerocopy_src,
            "crate_root": "lib.rs",
            "crate_name": "zerocopy",
            "crate_type": "lib",
            "edition": "2021",
            "target": "x86_64-unknown-linux-gnu",
            "cfg": ["no_zerocopy_allocator_api_1_100_0"],
            "env": {"CARGO_PKG_VERSION": "0.8.64"},
            "source_files": ZEROCOPY_SOURCE_FILES
        },
        "scope": {
            "kind": "selected_unit",
            "roots": ["<&[u8] as byte_slice::SplitByteSlice>::split_at_unchecked"]
        },
        "proof": {
            "source_root": lean_dir,
            "specification": "Spec.specs",
            "theorem": "Proof.verify",
            "sources": [
                {"module": "Spec", "path": "Spec.lean", "role": "specification"},
                {"module": "Proof", "path": "Proof.lean", "role": "proof"}
            ]
        }
    });
    let req_path = write_json_file(&work.join("request.json"), &request);
    let inv = verify_invocation(&[
        OsStr::new("--request"),
        req_path.as_os_str(),
        OsStr::new("--artifacts"),
        art_dir.as_os_str(),
    ]);
    let run = run_verify_inv(&staged, &inv);
    let verified = expect_verified(&run, "selected_unit_verified", true);
    assert_eq!(verified.audit["canonicalRoot"], "Trusted.MirSemantics.UnitTheoremV2");

    let receipt_path = work.join("verify_receipt.json");
    fs::write(&receipt_path, &run.process.stdout).unwrap();

    let cli = workspace_tools().cli.as_deref().expect("workspace cli binary");
    let json_out = Command::new(cli)
        .args([
            OsStr::new("inspect"),
            receipt_path.as_os_str(),
            OsStr::new("--verify-artifacts"),
            art_dir.as_os_str(),
            OsStr::new("--require-exact-artifacts"),
            OsStr::new("--check"),
            OsStr::new("--require-untainted"),
            OsStr::new("--unknown-fields"),
            OsStr::new("deny"),
            OsStr::new("--format"),
            OsStr::new("json"),
        ])
        .output()
        .expect("run cargo-anneal inspect json");
    assert_eq!(
        json_out.status.code(),
        Some(0),
        "stdout: {}\nstderr: {}",
        String::from_utf8_lossy(&json_out.stdout),
        String::from_utf8_lossy(&json_out.stderr)
    );
    assert!(json_out.stderr.is_empty());

    let parsed: Value = serde_json::from_slice(&json_out.stdout).unwrap();
    assert_eq!(parsed["status"], "selected_unit_verified");
    assert_eq!(parsed["tainted"], false);
    assert_eq!(parsed["unrecognized_fields"], json!([]));
    assert_eq!(parsed["invariant_violations"], json!([]));
    assert_eq!(parsed["policy_violations"], json!([]));
    assert_eq!(parsed["artifact_verification"]["exact_match"], true);
    assert_eq!(parsed["artifact_verification"]["failures"], json!([]));
    assert_eq!(parsed["receipt"]["correspondence_applicable"], false);
    assert_eq!(parsed["receipt"]["canonical_root"], "Trusted.MirSemantics.UnitTheoremV2");

    for (fmt, expected_substr) in [
        ("human", "Trusted.MirSemantics.UnitTheoremV2"),
        ("ledger", "audit.canonical_root=Trusted.MirSemantics.UnitTheoremV2\n"),
        ("markdown", "selected_unit_verified"),
    ] {
        let out = Command::new(cli)
            .args([
                OsStr::new("inspect"),
                receipt_path.as_os_str(),
                OsStr::new("--verify-artifacts"),
                art_dir.as_os_str(),
                OsStr::new("--require-exact-artifacts"),
                OsStr::new("--check"),
                OsStr::new("--require-untainted"),
                OsStr::new("--unknown-fields"),
                OsStr::new("deny"),
                OsStr::new("--format"),
                OsStr::new(fmt),
            ])
            .output()
            .expect("run cargo-anneal inspect formatted");
        assert_eq!(
            out.status.code(),
            Some(0),
            "format={fmt}\nstdout: {}\nstderr: {}",
            String::from_utf8_lossy(&out.stdout),
            String::from_utf8_lossy(&out.stderr)
        );
        assert!(out.stderr.is_empty(), "format={fmt}");
        let stdout = String::from_utf8_lossy(&out.stdout);
        assert!(stdout.contains(expected_substr), "format={fmt}\n{stdout}");
    }

    // Tampering the retained Lean specification must fail `--verify-artifacts`.
    fs::write(art_dir.join("authored/Spec.lean"), b"-- tampered spec\n").unwrap();
    let tamper_out = Command::new(cli)
        .args([
            OsStr::new("inspect"),
            receipt_path.as_os_str(),
            OsStr::new("--verify-artifacts"),
            art_dir.as_os_str(),
            OsStr::new("--require-exact-artifacts"),
            OsStr::new("--check"),
            OsStr::new("--require-untainted"),
            OsStr::new("--unknown-fields"),
            OsStr::new("deny"),
            OsStr::new("--format"),
            OsStr::new("json"),
        ])
        .output()
        .expect("run cargo-anneal inspect tampered spec");
    assert_eq!(
        tamper_out.status.code(),
        Some(1),
        "stdout: {}\nstderr: {}",
        String::from_utf8_lossy(&tamper_out.stdout),
        String::from_utf8_lossy(&tamper_out.stderr)
    );
    let tamper_parsed: Value = serde_json::from_slice(&tamper_out.stdout).unwrap();
    assert_eq!(tamper_parsed["artifact_verification"]["exact_match"], false);
    assert!(
        tamper_parsed["artifact_verification"]["failures"]
            .as_array()
            .unwrap()
            .iter()
            .any(|f| f.as_str().is_some_and(|s| s.contains("authored/Spec.lean"))),
        "{tamper_parsed}"
    );

    staged.finish(Ok(())).unwrap();
}
