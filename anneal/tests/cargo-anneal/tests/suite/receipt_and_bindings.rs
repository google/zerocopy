// Copyright 2026 The Fuchsia Authors
//
// Licensed under a BSD-style license <LICENSE-BSD>, Apache License, Version 2.0
// <LICENSE-APACHE or https://www.apache.org/licenses/LICENSE-2.0>, or the MIT
// license <LICENSE-MIT or https://opensource.org/licenses/MIT>, at your option.
// This file may not be copied, modified, or distributed except according to
// those terms.

//! Schema v3 receipts, boundary mutation rejection, `rustc` mode, and taint.

use std::{env, ffi::OsStr, fs, os::unix::fs::symlink, path::PathBuf};

use anneal_testkit::{Invocation, assertions::assert_outcome_exit};
use serde_json::{Value, json};

use crate::helpers::{
    SCALAR_DEPENDENCY, SCALAR_PROOF, SCALAR_SOURCE, SCALAR_SPEC, SCALAR_UNSUPPORTED, anneal_root,
    corpus_path, expect_failed, expect_verified, lean_module_source, lean_source, new_workspace,
    run_verify_inv, run_verify_strs, sha256_hex, verify_invocation, with_host_cargo_env,
    workspace_tools, write_json_file, write_scalar_baseline,
};

mod rustc_mode_and_verdicts;
mod selected_units;

#[test]
fn canonicalizes_symlinked_temporary_directory_source_bindings() {
    let staged = new_workspace("anneal-canon-root-").stage().unwrap();
    let work = staged.work_dir();
    let temporary = work.join("temporary-physical");
    fs::create_dir(&temporary).unwrap();
    let alias = work.join("temporary-alias");
    symlink(&temporary, &alias).unwrap();
    let real_parent = work.join("real");
    fs::create_dir(&real_parent).unwrap();
    let alias_parent = work.join("alias");
    symlink(&real_parent, &alias_parent).unwrap();

    let rust = real_parent.join("rust");
    let lean = real_parent.join("lean");
    fs::create_dir(&rust).unwrap();
    fs::create_dir(&lean).unwrap();
    fs::write(rust.join("lib.rs"), SCALAR_SOURCE).unwrap();
    fs::write(lean.join("Spec.lean"), SCALAR_SPEC).unwrap();
    fs::write(lean.join("Proof.lean"), SCALAR_PROOF).unwrap();

    // Canonicalize symlinked `TMPDIR` and `source_root` without leaking temp
    // artifacts or widening `include!` reads to undeclared files.
    let req = json!({
        "schema_version": 1,
        "compilation": {
            "source_root": alias_parent.join("rust"),
            "crate_root": "lib.rs",
            "crate_name": "scalar",
            "edition": "2024",
            "target": "x86_64-unknown-linux-gnu",
            "cfg": [],
            "source_files": ["lib.rs"]
        },
        "scope": {"kind": "crate"},
        "proof": {
            "source_root": alias_parent.join("lean"),
            "sources": [
                {"module": "Spec", "path": "Spec.lean", "role": "specification"},
                {"module": "Proof", "path": "Proof.lean", "role": "proof"}
            ]
        }
    });
    let req_path = write_json_file(&work.join("alias-req.json"), &req);
    let art = work.join("canon-run");
    let inv = verify_invocation(&[
        OsStr::new("--request"),
        req_path.as_os_str(),
        OsStr::new("--artifacts"),
        art.as_os_str(),
    ])
    .env("TMPDIR", &alias);
    let run = run_verify_inv(&staged, &inv);
    let ok = expect_verified(&run, "crate_verified", true);
    assert_eq!(ok.audit["exactType"], true);
    assert_eq!(ok.audit["replay"], true);
    let bytes = fs::read(art.join("capture/capture.json")).unwrap();
    let captured: Value = serde_json::from_slice(&bytes).unwrap();
    assert_eq!(captured["source_files"].as_array().unwrap().len(), 1);
    let input = &captured["source_files"][0];
    let input_path = PathBuf::from(input["path"].as_str().unwrap());
    assert_eq!(input_path, PathBuf::from("lib.rs"));
    assert!(!input_path.is_absolute());
    assert_eq!(input["path"], captured["configuration"]["crate_root"]);
    assert_eq!(captured["configuration"]["declared_source_files"], json!(["lib.rs"]));
    assert_eq!(input["sha256"], sha256_hex(SCALAR_SOURCE.as_bytes()));
    assert_eq!(input["sha256"], ok.sources[0]["sha256"]);
    assert_eq!(ok.capture_sha256, sha256_hex(&bytes));
    assert!(art.join("capture/Captured.lean").is_file());
    assert!(fs::read_dir(&temporary).unwrap().next().is_none());

    let undeclared = work.join("undeclared.rs");
    fs::write(&undeclared, "0").unwrap();
    fs::write(
        rust.join("lib.rs"),
        format!(
            "pub fn zero() -> u64 {{ include!({}) }}\n",
            serde_json::to_string(&undeclared).unwrap()
        ),
    )
    .unwrap();
    let undec_art = work.join("undeclared-run");
    let undec_inv = verify_invocation(&[
        OsStr::new("--request"),
        req_path.as_os_str(),
        OsStr::new("--artifacts"),
        undec_art.as_os_str(),
    ])
    .env("TMPDIR", &alias);
    let undec_run = run_verify_inv(&staged, &undec_inv);
    expect_failed(&undec_run, 1, "unsupported", Some("capture"), "undeclared compiler read");
    assert!(!undec_art.join("capture/capture.json").exists());
    assert!(fs::read_dir(&temporary).unwrap().next().is_none());
}

fn check_provenance_and_toolchain(ok: &anneal_testkit::VerifySuccessReceipt) {
    let expected_identity = if cfg!(target_os = "linux") {
        json!({
            "sha256_locked": [
                "Lean executable in foundation-lock.json",
                "Lean runtime shared libraries in LOCKED_LEAN_X86_64_LINUX_RUNTIME_LIBS",
                "foundation-lock.json modules",
                "Lean sysroot Init/Std/Lean .olean/.ir artifacts in LOCKED_SYSROOT_FOUNDATION_MANIFEST_SHA256",
                "imported library-lock.json modules"
            ],
            "sha256_recorded": ["capture executable as capture_binary_sha256"],
            "unhashed": [
                "Rust compiler and sysroot, identified by their reported commit"
            ]
        })
    } else {
        json!({
            "sha256_locked": [
                "Lean executable in foundation-lock.json",
                "foundation-lock.json modules",
                "Lean sysroot Init/Std/Lean .olean/.ir artifacts in LOCKED_SYSROOT_FOUNDATION_MANIFEST_SHA256",
                "imported library-lock.json modules"
            ],
            "sha256_recorded": ["capture executable as capture_binary_sha256"],
            "unhashed": [
                "Lean shared libraries, identified by lean --version",
                "Rust compiler and sysroot, identified by their reported commit"
            ]
        })
    };
    assert_eq!(ok.toolchain_identity, expected_identity);

    // Pinned Profile v1 receipts carry only the exact decoupled sentinel.
    assert_eq!(
        ok.correspondence_provenance,
        json!({
            "applicable": false,
            "reason": cargo_anneal::bundle::DECOUPLED_CORRESPONDENCE_PROVENANCE_REASON,
        })
    );

    // The repository record renders from the checkout (as `anneal-audit` and
    // CI do) and matches the Python renderer and any packaged archive copy.
    let checkout_prov_json =
        cargo_anneal::bundle::render_correspondence_provenance_from_checkout(&anneal_root())
            .unwrap();
    let checkout_prov: Value = serde_json::from_str(&checkout_prov_json).unwrap();
    let prov = &checkout_prov;
    assert_eq!(prov["schema_version"], 1);
    assert_eq!(prov["upstream_repository"], "https://github.com/proofs-rs/lean-miri.git");
    assert_eq!(prov["upstream_commit"], "c92d1d9754c9dd585b6b9d6949ae67e5e4665d6a");
    assert_eq!(prov["build_lean_toolchain"], "leanprover/lean4:v4.34.1");
    assert_eq!(
        prov["sysroot_foundation_manifest_sha256"],
        cargo_anneal::LOCKED_SYSROOT_FOUNDATION_MANIFEST_SHA256
    );
    assert_eq!(prov["upstream_pin_sha256"].as_str().unwrap().len(), 64);
    assert_eq!(prov["correspondence_adapters"].as_object().unwrap().len(), 7);
    assert_eq!(
        prov["correspondence_adapters"]["trusted/correspondence/Trusted/Correspondence.lean"]
            .as_str()
            .unwrap()
            .len(),
        64
    );
    assert_eq!(prov["patched_files"].as_array().unwrap().len(), 13);
    let minirust = &prov["minirust_upstream"];
    assert_eq!(minirust["upstream_repository"], "https://github.com/minirust/minirust");
    assert_eq!(minirust["upstream_commit"], "d821c6e3a3d358fa8a556774dc12b4aa5d0d65ed");
    assert_eq!(minirust["file_count"], 30);
    for sha_field in ["upstream_pin_sha256", "tarball_sha256", "manifest_sha256"] {
        let digest = minirust[sha_field].as_str().unwrap();
        assert_eq!(digest.len(), 64, "{sha_field}");
        assert!(digest.bytes().all(|b| b.is_ascii_hexdigit()), "{sha_field}");
    }
    assert_eq!(minirust["files"].as_object().unwrap().len(), 30);
    assert_eq!(prov["correspondence_proofs"].as_object().unwrap().len(), 29);
    for proof_key in [
        "correspondence/Anneal/MiniRustProof.lean",
        "correspondence/Anneal/MirCorrespondence/InitAndSim.lean",
        "correspondence/Anneal/MirCorrespondence/LayoutAndAlign.lean",
        "correspondence/Anneal/MirCorrespondence/MiriMemoryBridge.lean",
        "correspondence/Anneal/MirCorrespondence/RefinementBundles.lean",
        "correspondence/Anneal/MirCorrespondenceProof.lean",
    ] {
        assert_eq!(prov["correspondence_proofs"][proof_key].as_str().unwrap().len(), 64);
    }
    for lean_key in [
        "trusted/lean/Trusted.lean",
        "trusted/lean/Trusted/MirAst.lean",
        "trusted/lean/Trusted/MirSemantics.lean",
        "trusted/lean/foundation-lock.json",
        "trusted/lean/lean-toolchain",
    ] {
        assert_eq!(prov["trusted_lean"][lean_key].as_str().unwrap().len(), 64);
    }
    assert!(prov["note"].as_str().unwrap().contains("anneal-audit --require-correspondence"));

    let rendered_py = std::process::Command::new("python3")
        .arg("-B")
        .arg(anneal_root().join("ci/render_correspondence_provenance.py"))
        .arg("--anneal-root")
        .arg(anneal_root())
        .output()
        .unwrap();
    assert!(
        rendered_py.status.success(),
        "render_correspondence_provenance.py failed: {}",
        String::from_utf8_lossy(&rendered_py.stderr)
    );
    assert_eq!(String::from_utf8(rendered_py.stdout).unwrap(), checkout_prov_json);

    if let Ok(install_root) = env::var("ANNEAL_TEST_INSTALL_ROOT")
        && !install_root.is_empty()
    {
        let archive_path =
            PathBuf::from(install_root).join("share/anneal/correspondence-provenance.json");
        let archive_prov: Value =
            serde_json::from_slice(&fs::read(&archive_path).unwrap()).unwrap();
        assert_eq!(&archive_prov, prov);
    }
}

#[test]
fn verifies_real_source_and_rejects_boundary_mutations() {
    let staged = new_workspace("anneal-boundary-").stage().unwrap();
    let work = staged.work_dir();
    let request = write_scalar_baseline(work);
    let req_path = write_json_file(&work.join("whole-crate.json"), &request);
    let whole_art = work.join("whole-crate");

    let run = run_verify_strs(
        &staged,
        &["--request", req_path.to_str().unwrap(), "--artifacts", whole_art.to_str().unwrap()],
    );
    let ok = expect_verified(&run, "crate_verified", true);
    assert!(ok.experimental, "{ok:?}");
    assert_eq!(ok.candidate_features, vec!["mir_ast", "mir_semantics"]);
    check_provenance_and_toolchain(ok);
    assert!(whole_art.join("capture/Captured.lean").is_file());
    assert!(whole_art.join("generated/Expected.lean").is_file());
    assert!(whole_art.join("audit-request.json").is_file());
    assert!(whole_art.join("result.json").is_file());

    // Changing Rust source body while keeping spec/proof fixed must fail audit.
    fs::write(work.join("rust/lib.rs"), SCALAR_SOURCE.replace("    0\n", "    1\n")).unwrap();
    let changed_art = work.join("changed-source");
    let changed = run_verify_strs(
        &staged,
        &["--request", req_path.to_str().unwrap(), "--artifacts", changed_art.to_str().unwrap()],
    );
    expect_failed(&changed, 1, "proof_failed", Some("audit"), "Proof.lean");
    let changed_cap: Value =
        serde_json::from_slice(&fs::read(changed_art.join("capture/capture.json")).unwrap())
            .unwrap();
    assert_ne!(ok.sources[0]["sha256"], changed_cap["source_files"][0]["sha256"]);
    fs::write(work.join("rust/lib.rs"), SCALAR_SOURCE).unwrap();

    // Negative shortcuts around the canonical closed theorem hit exact guards.
    for (name, decls, rejection) in [
        (
            "wrong-root",
            "public theorem Proof.verify : True := True.intro",
            "policy:target theorem type differs from Expected",
        ),
        (
            "axiom",
            "public axiom fabricated : Expected.claim\npublic theorem Proof.verify : Expected.claim := fabricated",
            "policy:unapproved axiom fabricated from Proof",
        ),
        (
            "sorry",
            "public theorem Proof.verify : Expected.claim := by sorry",
            "policy:unapproved axiom sorryAx from Init.Prelude",
        ),
        (
            "extra-hypothesis",
            "public theorem Proof.verify (assumed : Expected.claim) : Expected.claim := assumed",
            "policy:target theorem type differs from Expected",
        ),
    ] {
        fs::write(work.join("lean/Proof.lean"), lean_module_source("public import Expected", decls)).unwrap();
        let art = work.join(name);
        let res = run_verify_strs(
            &staged,
            &["--request", req_path.to_str().unwrap(), "--artifacts", art.to_str().unwrap()],
        );
        expect_failed(&res, 1, "proof_failed", Some("audit"), rejection);
    }
    fs::write(work.join("lean/Proof.lean"), SCALAR_PROOF).unwrap();

    let mut wrong_role = request.clone();
    wrong_role["proof"]["sources"][0]["role"] = json!("proof");
    let wrong_role_path = write_json_file(&work.join("wrong-role.json"), &wrong_role);
    let r = run_verify_strs(&staged, &["--request", wrong_role_path.to_str().unwrap()]);
    expect_failed(
        &r,
        1,
        "unsupported",
        Some("proof"),
        "specification and theorem must have their declared source roles",
    );

    let shadowed = SCALAR_PROOF
        .replace(
            "public import Expected\n",
            "public import Expected\npublic import Trusted.MirSemantics\npublic import Captured\n",
        )
        .replace(
            "public theorem verify : Expected.claim := by",
            "public def Spec.specs : Specs := ⟨fun _ _ => False, fun _ => True⟩\n\n\
             public theorem verify : CrateTheorem ⟨Captured.program, Spec.specs⟩ := by",
        )
        .replace(", totalCorrectness⟩", ", True.intro⟩");
    fs::write(work.join("lean/Proof.lean"), shadowed).unwrap();
    let r = run_verify_strs(&staged, &["--request", req_path.to_str().unwrap()]);
    expect_failed(
        &r,
        1,
        "proof_failed",
        Some("audit"),
        "policy:target theorem type differs from Expected",
    );
    fs::write(work.join("lean/Proof.lean"), SCALAR_PROOF).unwrap();

    // Hidden specification helper macro inside a proof-role module.
    fs::write(
        work.join("lean/Extra.lean"),
        lean_source("import Trusted.MirSemantics", "macro \"hiddenProperty\" : term => `(True)"),
    )
    .unwrap();
    fs::write(
        work.join("lean/Spec.lean"),
        lean_source(
            "import Trusted.MirSemantics\nimport Extra",
            "namespace Spec\ndef specs : Trusted.MirSemantics.Specs :=\n  \
             ⟨fun _ _ => False, fun _ => hiddenProperty⟩\nend Spec",
        ),
    )
    .unwrap();
    let mut hidden_spec = request.clone();
    hidden_spec["proof"]["sources"]
        .as_array_mut()
        .unwrap()
        .push(json!({"module": "Extra", "path": "Extra.lean", "role": "proof"}));
    let hidden_path = write_json_file(&work.join("hidden.json"), &hidden_spec);
    let hidden = run_verify_strs(&staged, &["--request", hidden_path.to_str().unwrap()]);
    let hidden_fail = expect_failed(&hidden, 1, "proof_failed", Some("audit"), "");
    assert!(
        hidden_fail.detail.contains("specification")
            || hidden_fail.detail.contains("role")
            || hidden_fail.detail.contains("Spec cannot import Extra"),
        "macro must fail at specification origin boundary: {}",
        hidden_fail.detail
    );
    fs::write(work.join("lean/Spec.lean"), SCALAR_SPEC).unwrap();
    fs::remove_file(work.join("lean/Extra.lean")).unwrap();
}

#[test]
fn capture_sha256_is_invariant_across_distinct_staging_directories() {
    let staged_a = new_workspace("anneal-cap-det-a-").stage().unwrap();
    let staged_b = new_workspace("anneal-cap-det-b-").stage().unwrap();

    let run_in = |staged: &anneal_testkit::StagedWorkspace, tag: &str| {
        let work = staged.work_dir();
        let rust = work.join(format!("rust-{tag}"));
        let lean = work.join(format!("lean-{tag}"));
        let tmp = work.join(format!("tmp-{tag}"));
        fs::create_dir_all(rust.join("sub")).unwrap();
        fs::create_dir_all(&lean).unwrap();
        fs::create_dir_all(&tmp).unwrap();

        fs::write(rust.join("lib.rs"), format!("mod sub;\n{SCALAR_SOURCE}")).unwrap();
        fs::write(rust.join("sub/mod.rs"), "pub fn helper() -> u64 { 0 }\n").unwrap();
        fs::write(lean.join("Spec.lean"), SCALAR_SPEC).unwrap();
        fs::write(lean.join("Proof.lean"), SCALAR_PROOF).unwrap();

        let req = json!({
            "schema_version": 1,
            "compilation": {
                "source_root": rust,
                "crate_root": "lib.rs",
                "crate_name": "scalar",
                "edition": "2024",
                "target": "x86_64-unknown-linux-gnu",
                "cfg": [],
                "source_files": ["lib.rs", "sub/mod.rs"]
            },
            "scope": { "kind": "selected_unit", "roots": ["zero"] },
            "proof": {
                "source_root": lean,
                "sources": [
                    { "module": "Spec", "path": "Spec.lean", "role": "specification" },
                    { "module": "Proof", "path": "Proof.lean", "role": "proof" }
                ]
            }
        });
        let req_path = write_json_file(&work.join("req.json"), &req);
        let art = work.join(format!("art-{tag}"));
        let inv = verify_invocation(&[
            OsStr::new("--request"),
            req_path.as_os_str(),
            OsStr::new("--artifacts"),
            art.as_os_str(),
        ])
        .env("TMPDIR", &tmp);
        let run = run_verify_inv(staged, &inv);
        let ok = expect_verified(&run, "selected_unit_verified", true);
        let capture_bytes = fs::read(art.join("capture/capture.json")).unwrap();
        (ok.capture_sha256.clone(), capture_bytes, tmp)
    };

    let (sha_a, bytes_a, tmp_a) = run_in(&staged_a, "alpha");
    let (sha_b, bytes_b, tmp_b) = run_in(&staged_b, "beta");

    assert_eq!(sha_a, sha_b, "captureSha256 must be invariant across distinct staging dirs");
    assert_eq!(bytes_a, bytes_b, "capture.json must be byte-identical across staging dirs");

    let captured: Value = serde_json::from_slice(&bytes_a).unwrap();
    assert_eq!(captured["configuration"]["crate_root"], "lib.rs");
    assert_eq!(captured["configuration"]["declared_source_files"], json!(["lib.rs", "sub/mod.rs"]));
    let recorded_paths: Vec<&str> = captured["source_files"]
        .as_array()
        .unwrap()
        .iter()
        .map(|entry| entry["path"].as_str().unwrap())
        .collect();
    assert_eq!(recorded_paths, vec!["lib.rs", "sub/mod.rs"]);

    let raw_json = String::from_utf8(bytes_a).unwrap();
    assert!(!raw_json.contains(tmp_a.to_str().unwrap()), "staging TMPDIR leaked into capture.json");
    assert!(!raw_json.contains(tmp_b.to_str().unwrap()), "staging TMPDIR leaked into capture.json");
}
