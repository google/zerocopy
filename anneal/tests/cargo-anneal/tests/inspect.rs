// Copyright 2026 The Fuchsia Authors
//
// Licensed under a BSD-style license <LICENSE-BSD>, Apache License, Version 2.0
// <LICENSE-APACHE or https://www.apache.org/licenses/LICENSE-2.0>, or the MIT
// license <LICENSE-MIT or https://opensource.org/licenses/MIT>, at your option.
// This file may not be copied, modified, or distributed except according to
// those terms.

//! Offline CLI tests for `cargo anneal inspect` and the pure-core I/O guard.
//!
//! The tests live in domain submodules under `tests/inspect/`, which share
//! this file's helpers and imports through `use super::*`. They stay in this
//! one `inspect` test target, which CI builds and lints by name.

use std::{
    env, fs,
    io::Write as _,
    os::unix::fs::symlink,
    path::{Path, PathBuf},
    process::{Command, Output, Stdio},
};

use serde_json::{Value, json};
use sha2::{Digest as _, Sha256};

fn anneal_root() -> PathBuf {
    PathBuf::from(env!("CARGO_MANIFEST_DIR")).join("../..").canonicalize().unwrap()
}

fn sha256_hex(bytes: &[u8]) -> String {
    let mut h = Sha256::new();
    h.update(bytes);
    format!("{:x}", h.finalize())
}

fn cli_bin() -> PathBuf {
    for key in ["ANNEAL_CLI", "ANNEAL_TEST_CARGO_ANNEAL"] {
        if let Some(val) = env::var_os(key).filter(|v| !v.is_empty()) {
            return PathBuf::from(val);
        }
    }
    PathBuf::from(env!("CARGO_BIN_EXE_cargo-anneal-test-bin"))
}

fn run_inspect(args: &[&str], stdin_bytes: Option<&[u8]>) -> Output {
    let bin = cli_bin();
    let mut cmd = Command::new(bin);
    cmd.arg("inspect").args(args);
    if stdin_bytes.is_some() {
        cmd.stdin(Stdio::piped());
    } else {
        cmd.stdin(Stdio::null());
    }
    cmd.stdout(Stdio::piped()).stderr(Stdio::piped());
    let mut child = cmd.spawn().expect("spawn cargo-anneal inspect");
    if let Some(bytes) = stdin_bytes {
        child.stdin.take().unwrap().write_all(bytes).unwrap();
    }
    child.wait_with_output().expect("wait for cargo-anneal inspect")
}

fn run_cargo_subcommand_inspect(args: &[&str]) -> Output {
    let bin = cli_bin();
    Command::new(bin)
        .arg("anneal")
        .arg("inspect")
        .args(args)
        .stdin(Stdio::null())
        .output()
        .expect("run cargo-anneal anneal inspect")
}

fn sample_receipt_bundle(dir: &Path) -> (Value, String, String, String, String) {
    let req_bytes = br#"{"schema_version":1}"#;
    let cap_bytes = br#"{"schema_version":1,"crate_name":"demo"}"#;
    let src_bytes = b"pub fn zero() -> u32 { 0 }\n";
    let res_bytes = br#"{"ok":true}"#;
    let model_lean = b"-- stub model\n";
    let spec_lean = b"-- stub spec\n";
    let proof_lean = b"-- stub proof\n";
    let cap_lean = b"-- stub capture\n";
    let exp_lean = b"-- stub expected\n";

    let req_sha = sha256_hex(req_bytes);
    let cap_sha = sha256_hex(cap_bytes);
    let src_sha = sha256_hex(src_bytes);
    let mod_sha = "c".repeat(64);
    let model_lean_sha = sha256_hex(model_lean);
    let spec_lean_sha = sha256_hex(spec_lean);
    let proof_lean_sha = sha256_hex(proof_lean);
    let cap_lean_sha = sha256_hex(cap_lean);
    let exp_lean_sha = sha256_hex(exp_lean);
    let spec_sha =
        sha256_hex(&serde_json::to_vec_pretty(&[("Spec", spec_lean_sha.as_str())]).unwrap());

    fs::create_dir_all(dir.join("capture")).unwrap();
    fs::create_dir_all(dir.join("rust/src")).unwrap();
    fs::create_dir_all(dir.join("authored")).unwrap();
    fs::create_dir_all(dir.join("generated")).unwrap();
    fs::create_dir_all(dir.join("anneal/trusted/lean/Trusted")).unwrap();
    fs::write(dir.join("request.json"), req_bytes).unwrap();
    fs::write(dir.join("capture/capture.json"), cap_bytes).unwrap();
    fs::write(dir.join("rust/src/lib.rs"), src_bytes).unwrap();
    fs::write(dir.join("result.json"), res_bytes).unwrap();
    fs::write(dir.join("anneal/trusted/lean/Trusted/MirSemantics.lean"), model_lean).unwrap();
    fs::write(dir.join("authored/Spec.lean"), spec_lean).unwrap();
    fs::write(dir.join("authored/Proof.lean"), proof_lean).unwrap();
    fs::write(dir.join("capture/Captured.lean"), cap_lean).unwrap();
    fs::write(dir.join("generated/Expected.lean"), exp_lean).unwrap();

    let mut receipt = json!({
        "schema_version": 3,
        "status": "crate_verified",
        "taint_reasons": [],
        "elaboration_sandbox": "linux_bwrap",
        "experimental": false,
        "candidate_features": [],
        "request_sha256": req_sha,
        "capture_sha256": cap_sha,
        "capture_binary_sha256": "e".repeat(64),
        "model_manifest_sha256": mod_sha,
        "specification_manifest_sha256": spec_sha,
        "toolchain_identity": {
            "sha256_locked": ["Trusted.MirAst"],
            "sha256_recorded": ["Init.Core"],
            "unhashed": []
        },
        "correspondence_provenance": {
            "schema_version": 1,
            "upstream_repository": "https://github.com/proofs-rs/lean-miri",
            "upstream_commit": "c92d1d97",
            "upstream_lean_toolchain": "leanprover/lean4:v4.34.1",
            "build_lean_toolchain": "leanprover/lean4:v4.34.1",
            "upstream_pin_sha256": "f".repeat(64),
            "sysroot_foundation_manifest_sha256": "f".repeat(64),
            "minirust_upstream": {
                "upstream_repository": "https://github.com/minirust/minirust",
                "upstream_commit": "d821c6e3a3d358fa8a556774dc12b4aa5d0d65ed",
                "upstream_pin_sha256": "f".repeat(64),
                "tarball_sha256": "f".repeat(64),
                "manifest_sha256": "f".repeat(64),
                "file_count": 1,
                "files": {
                    "README.md": "f".repeat(64)
                }
            }
        },
        "scope": { "kind": "crate" },
        "selected": [{ "def_id": 1, "path": "demo::zero", "body_index": 0 }],
        "census": [{
            "def_id": 1,
            "path": "demo::zero",
            "kind": "fn",
            "has_body": true,
            "selected": true,
            "required": true
        }],
        "sources": [{ "relative_path": "src/lib.rs", "sha256": src_sha }],
        "configuration": {
            "crate_name": "demo",
            "crate_type": "rlib",
            "panic": "unwind",
            "edition": "2024",
            "target": "x86_64-unknown-linux-gnu"
        },
        "timing_ms": { "capture": 12, "proof_and_audit": 34, "total": 46 },
        "assumptions": ["Rust MIR semantics"],
        "deferred": [],
        "spec_warnings": []
    });
    receipt["audit"] = json!({
        "theorem": "Spec.zero_ok",
        "canonicalRoot": "Trusted.MirSemantics.CrateTheorem",
        "subject": "Captured.zero",
        "specification": "Spec.zero",
        "expected": "Trusted.MirSemantics.CrateTheorem",
        "graph": { "nodes": [] },
        "axioms": ["propext", "Classical.choice", "Quot.sound"],
        "sorryDeclarations": [],
        "replay": true,
        "exactType": true,
        "replayedDeclarations": 5,
        "checkedAlternateProofs": 0,
        "auditMode": "strict",
        "kernelsPassed": ["lean4"],
        "kernelsSkipped": [],
        "paranoidQuorum": false,
        "subjectClosure": [{ "name": "Captured.zero", "module": "Captured" }],
        "modelClosure": [{ "name": "Trusted.MirSemantics.CrateTheorem", "module": "Trusted.MirSemantics" }],
        "specificationClosure": [{ "name": "Spec.zero", "module": "Spec" }],
        "sources": [
            {
                "module": "Trusted.MirSemantics",
                "role": "model",
                "sourceSha256": model_lean_sha,
                "artifacts": [{ "sha256": "1".repeat(64) }]
            },
            {
                "module": "Captured",
                "role": "capture",
                "sourceSha256": cap_lean_sha,
                "artifacts": [{ "sha256": "2".repeat(64) }]
            },
            {
                "module": "Spec",
                "role": "specification",
                "sourceSha256": spec_lean_sha,
                "artifacts": [{ "sha256": "3".repeat(64) }]
            },
            {
                "module": "Proof",
                "role": "proof",
                "sourceSha256": proof_lean_sha,
                "artifacts": [{ "sha256": "4".repeat(64) }]
            },
            {
                "module": "Expected",
                "role": "expected",
                "sourceSha256": exp_lean_sha,
                "artifacts": [{ "sha256": "5".repeat(64) }]
            }
        ],
        "bindings": {
            "requestSha256": req_sha,
            "captureSha256": cap_sha,
            "modelManifestSha256": mod_sha,
            "specificationManifestSha256": spec_sha
        }
    });
    (receipt, req_sha, cap_sha, mod_sha, spec_sha)
}

#[path = "inspect/artifacts_and_three_tier_diff.rs"]
mod artifacts_and_three_tier_diff;
#[path = "inspect/cli_and_policy_gates.rs"]
mod cli_and_policy_gates;
#[path = "inspect/correspondence_provenance.rs"]
mod correspondence_provenance;
#[path = "inspect/pure_core_io_audit.rs"]
mod pure_core_io_audit;
#[path = "inspect/sharded_proof.rs"]
mod sharded_proof;
#[path = "inspect/unstable_features_and_limits.rs"]
mod unstable_features_and_limits;
