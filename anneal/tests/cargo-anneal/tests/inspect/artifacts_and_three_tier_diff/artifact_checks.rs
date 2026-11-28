// Copyright 2026 The Fuchsia Authors
//
// Licensed under a BSD-style license <LICENSE-BSD>, Apache License, Version 2.0
// <LICENSE-APACHE or https://www.apache.org/licenses/LICENSE-2.0>, or the MIT
// license <LICENSE-MIT or https://opensource.org/licenses/MIT>, at your option.
// This file may not be copied, modified, or distributed except according to
// those terms.

//! `--verify-artifacts`, exact-artifact and stdout-receipt checks, failure
//! and tainted receipts, crate scope, S-3 GUTNS reconciliation, and symlink
//! and digest tampering.

use super::*;

/// Runs the sections of `verify_artifacts_and_three_tier_diff_enforced`
/// that the module documentation lists.
pub(super) fn verifies_artifacts_and_receipt_gates(
    tmp: &tempfile::TempDir,
    art_dir: PathBuf,
    clean: Value,
    clean_path: PathBuf,
) -> (Value, PathBuf, Value, String) {
    // Valid artifacts dir passes --verify-artifacts + exact artifacts check
    // only when result.json SHA-256 matches the inspected receipt bytes.
    fs::write(art_dir.join("result.json"), fs::read(&clean_path).unwrap()).unwrap();
    let ok = run_inspect(
        &[
            clean_path.to_str().unwrap(),
            "--verify-artifacts",
            art_dir.to_str().unwrap(),
            "--require-exact-artifacts",
            "--check",
        ],
        None,
    );
    assert_eq!(ok.status.code(), Some(0), "stderr={}", String::from_utf8_lossy(&ok.stderr));

    // Mismatched result.json fails --require-exact-artifacts.
    fs::write(art_dir.join("result.json"), b"{}").unwrap();
    let bad_res = run_inspect(
        &[
            clean_path.to_str().unwrap(),
            "--verify-artifacts",
            art_dir.to_str().unwrap(),
            "--require-exact-artifacts",
        ],
        None,
    );
    assert_eq!(bad_res.status.code(), Some(1));

    // Stdout-captured receipt (with `artifacts` + trailing newline) matches
    // pre-retention `result.json` (no `artifacts`), while a field tamper in
    // `result.json` still fails `--require-exact-artifacts`.
    let mut stage_result = clean.clone();
    stage_result.as_object_mut().unwrap().remove("artifacts");
    let mut stdout_receipt = clean.clone();
    stdout_receipt["artifacts"] = json!(art_dir.to_str().unwrap());
    let stdout_path = tmp.path().join("stdout_receipt.json");
    let mut stdout_bytes = serde_json::to_vec_pretty(&stdout_receipt).unwrap();
    stdout_bytes.push(b'\n');
    fs::write(&stdout_path, &stdout_bytes).unwrap();
    fs::write(art_dir.join("result.json"), serde_json::to_vec_pretty(&stage_result).unwrap())
        .unwrap();
    let stdout_ok = run_inspect(
        &[
            stdout_path.to_str().unwrap(),
            "--verify-artifacts",
            art_dir.to_str().unwrap(),
            "--require-exact-artifacts",
            "--check",
        ],
        None,
    );
    assert_eq!(
        stdout_ok.status.code(),
        Some(0),
        "stdout={}\nstderr={}",
        String::from_utf8_lossy(&stdout_ok.stdout),
        String::from_utf8_lossy(&stdout_ok.stderr)
    );
    let mut tampered_stage = stage_result;
    tampered_stage["timing_ms"]["total"] = json!(999);
    fs::write(art_dir.join("result.json"), serde_json::to_vec_pretty(&tampered_stage).unwrap())
        .unwrap();
    let stdout_tamper = run_inspect(
        &[
            stdout_path.to_str().unwrap(),
            "--verify-artifacts",
            art_dir.to_str().unwrap(),
            "--require-exact-artifacts",
        ],
        None,
    );
    assert_eq!(stdout_tamper.status.code(), Some(1));
    fs::write(art_dir.join("result.json"), fs::read(&clean_path).unwrap()).unwrap();

    // Tampering or deleting any retained Lean artifact (spec, capture,
    // expected, model) or omitting `audit.sources` fails `--verify-artifacts`.
    for rel in [
        "authored/Spec.lean",
        "capture/Captured.lean",
        "generated/Expected.lean",
        "anneal/trusted/lean/Trusted/MirSemantics.lean",
    ] {
        let p = art_dir.join(rel);
        let orig = fs::read(&p).unwrap();
        fs::write(&p, b"-- tampered\n").unwrap();
        let out = run_inspect(
            &[
                clean_path.to_str().unwrap(),
                "--verify-artifacts",
                art_dir.to_str().unwrap(),
                "--require-exact-artifacts",
                "--format",
                "json",
            ],
            None,
        );
        assert_eq!(out.status.code(), Some(1), "tampered {rel} must fail");
        let parsed: Value = serde_json::from_slice(&out.stdout).unwrap();
        assert_eq!(parsed["artifact_verification"]["exact_match"], false);
        fs::remove_file(&p).unwrap();
        let del_out = run_inspect(
            &[
                clean_path.to_str().unwrap(),
                "--verify-artifacts",
                art_dir.to_str().unwrap(),
                "--require-exact-artifacts",
            ],
            None,
        );
        assert_eq!(del_out.status.code(), Some(1), "deleted {rel} must fail");
        fs::write(&p, orig).unwrap();
    }
    let mut no_audit_src = clean.clone();
    no_audit_src["audit"].as_object_mut().unwrap().remove("sources");
    let no_audit_src_path = tmp.path().join("no_audit_src.json");
    fs::write(&no_audit_src_path, serde_json::to_vec(&no_audit_src).unwrap()).unwrap();
    let no_src_out = run_inspect(
        &[no_audit_src_path.to_str().unwrap(), "--verify-artifacts", art_dir.to_str().unwrap()],
        None,
    );
    assert_eq!(no_src_out.status.code(), Some(1));

    // Failure receipt without result.json: bare inspect fails closed (`exit 1`
    // per D1-A) while still rendering JSON, whereas `--passive` exits `0` and
    // must NOT report VerifiedLocal.
    let fail_json = json!({
        "schema_version": 3,
        "status": "proof_failed",
        "taint_reasons": [],
        "phase": "audit",
        "detail": "proof failed",
        "artifacts": "missing_dir"
    });
    let fail_path = tmp.path().join("fail.json");
    fs::write(&fail_path, serde_json::to_vec(&fail_json).unwrap()).unwrap();
    let empty_art = tmp.path().join("empty_art");
    fs::create_dir(&empty_art).unwrap();
    let fail_default = run_inspect(
        &[
            fail_path.to_str().unwrap(),
            "--verify-artifacts",
            empty_art.to_str().unwrap(),
            "--format",
            "json",
        ],
        None,
    );
    assert_eq!(fail_default.status.code(), Some(1));
    let fail_art = run_inspect(
        &[
            fail_path.to_str().unwrap(),
            "--verify-artifacts",
            empty_art.to_str().unwrap(),
            "--format",
            "json",
            "--passive",
        ],
        None,
    );
    assert_eq!(fail_art.status.code(), Some(0));
    let fail_art_out: Value = serde_json::from_slice(&fail_art.stdout).unwrap();
    assert_ne!(fail_art_out["profile"]["artifacts"]["kind"], "verified_local");

    // Bare inspect on sorry-tainted receipt fails closed (`exit 1`), whereas
    // `--passive` exits `0`.
    let (mut sorry_tainted, ..) = sample_receipt_bundle(&tmp.path().join("art_sorry"));
    sorry_tainted["status"] = json!("tainted_crate_verified");
    sorry_tainted["taint_reasons"] = json!(["sorry_in_proof"]);
    sorry_tainted["sorry_declarations"] = json!(["Proof.hole"]);
    sorry_tainted["audit"]["axioms"] = json!(["propext", "sorryAx"]);
    sorry_tainted["audit"]["sorryDeclarations"] = json!(["Proof.hole"]);
    let sorry_path = tmp.path().join("sorry_tainted.json");
    fs::write(&sorry_path, serde_json::to_vec(&sorry_tainted).unwrap()).unwrap();
    assert_eq!(run_inspect(&[sorry_path.to_str().unwrap()], None).status.code(), Some(1));
    assert_eq!(
        run_inspect(&[sorry_path.to_str().unwrap(), "--passive"], None).status.code(),
        Some(0)
    );
    assert_eq!(
        run_inspect(&[sorry_path.to_str().unwrap(), "--passive", "--check"], None).status.code(),
        Some(2)
    );

    // Untainted `selected_unit_verified` exits `0` by default and `1` with
    // `--require-crate-scope`.
    let (mut scoped, ..) = sample_receipt_bundle(&tmp.path().join("art_scoped"));
    scoped["status"] = json!("selected_unit_verified");
    scoped["scope"] = json!({ "kind": "selected_unit", "roots": ["demo::zero"] });
    scoped["audit"]["canonicalRoot"] = json!("Trusted.MirSemantics.UnitTheorem");
    let scoped_path = tmp.path().join("scoped.json");
    fs::write(&scoped_path, serde_json::to_vec(&scoped).unwrap()).unwrap();
    assert_eq!(run_inspect(&[scoped_path.to_str().unwrap()], None).status.code(), Some(0));
    assert_eq!(
        run_inspect(&[scoped_path.to_str().unwrap(), "--require-crate-scope"], None).status.code(),
        Some(1)
    );

    // S-3 GUTNS v3 receipt + CorrespondenceProvenanceV3 reconciles cleanly
    // under strict `--unknown-fields deny` (`exit 0`, zero unrecognized fields)
    // and surfaces bounded/qualified assurance in `--format markdown`.
    let (mut s3_gutns, ..) = sample_receipt_bundle(&tmp.path().join("art_s3"));
    let h = "b".repeat(64);
    let cap_bin_sha = s3_gutns["capture_binary_sha256"].as_str().unwrap().to_owned();
    s3_gutns["assurance_stage"] = json!("stage0_alpha");
    s3_gutns["horizon"] = json!({"kind": "bounded", "k": 8});
    s3_gutns["permitted_axioms"] = json!(["Classical.choice", "Quot.sound", "propext"]);
    s3_gutns["tcb_shims"] = json!([{
        "id": "rustc_post_cleanup_capture",
        "kind": "capture_driver",
        "commit": "pinned-commit",
        "sha256": cap_bin_sha,
        "status": "assumed",
        "guards": ["mir_preserve_ub"]
    }]);
    s3_gutns["model_system_relation"] = json!({
        "kind": "simulation",
        "qualifier": "wf_stutter",
        "direction": "forward",
        "anchored_at": "post_cleanup_mir",
        "licensed_claim_shapes": ["forall_safety"],
        "unmodeled_downstream": ["rustc_mir_opt", "llvm_codegen"]
    });
    s3_gutns["correspondence_provenance"]["schema_version"] = json!(3);
    s3_gutns["correspondence_provenance"]["claim_kind"] = json!("exact_refines");
    s3_gutns["correspondence_provenance"]["permitted_axioms"] =
        json!(["Classical.choice", "Quot.sound", "propext"]);
    s3_gutns["correspondence_provenance"]["model_system_relation"] = json!({
        "kind": "simulation",
        "qualifier": "wf_stutter",
        "direction": "bidirectional",
        "licensed_claim_shapes": ["forall_safety"]
    });
    s3_gutns["correspondence_provenance"]["patched_files"] = json!([{
        "path": "foo.lean",
        "upstream_sha256": cap_bin_sha,
        "patched_sha256": h
    }]);
    s3_gutns["correspondence_provenance"]["tcb_shims"] = json!([{
        "id": "lean-miri:foo.lean",
        "kind": "upstream_bugfix_patch",
        "sha256": h,
        "status": "assumed"
    }]);
    s3_gutns["correspondence_provenance"]["taint_reasons"] =
        json!(["vendor_upstream_patches_present"]);
    s3_gutns["correspondence_provenance"]["qualifiers"] = json!({
        "choice_total": true,
        "assumed_seams": [],
        "scope_kind": "full_gate"
    });
    let s3_path = tmp.path().join("s3_gutns.json");
    fs::write(&s3_path, serde_json::to_vec(&s3_gutns).unwrap()).unwrap();
    let s3_out = run_inspect(
        &[s3_path.to_str().unwrap(), "--unknown-fields", "deny", "--format", "markdown"],
        None,
    );
    assert_eq!(
        s3_out.status.code(),
        Some(0),
        "stdout={}\nstderr={}",
        String::from_utf8_lossy(&s3_out.stdout),
        String::from_utf8_lossy(&s3_out.stderr)
    );
    let s3_md = String::from_utf8(s3_out.stdout).unwrap();
    assert!(s3_md.contains("QUALIFIED ASSURANCE"), "{s3_md}");
    assert!(s3_md.contains("bounded(k=8)"), "{s3_md}");
    assert!(s3_md.contains("stage0_alpha"), "{s3_md}");
    assert!(s3_md.contains("rustc_post_cleanup_capture"), "{s3_md}");
    assert!(s3_md.contains("lean-miri:foo.lean"), "{s3_md}");
    assert!(s3_md.contains("Provenance Relation"), "{s3_md}");
    let s3_human_out = run_inspect(&[s3_path.to_str().unwrap(), "--unknown-fields", "deny"], None);
    assert_eq!(s3_human_out.status.code(), Some(0));
    let s3_human = String::from_utf8(s3_human_out.stdout).unwrap();
    assert!(s3_human.contains("[QUALIFIED]"), "{s3_human}");
    assert!(s3_human.contains("qualified_assurance:"), "{s3_human}");
    assert!(s3_human.contains("anchor=post_cleanup_mir"), "{s3_human}");
    assert!(s3_human.contains("unmodeled=[rustc_mir_opt,llvm_codegen]"), "{s3_human}");
    assert!(s3_human.contains("scope:full_gate"), "{s3_human}");

    // Symlinked intermediate `rust` directory must be rejected.
    let outside = tmp.path().join("outside");
    fs::create_dir_all(outside.join("src")).unwrap();
    fs::write(outside.join("src/lib.rs"), b"pub fn zero() -> u32 { 0 }\n").unwrap();
    let sym_art = tmp.path().join("sym_artifacts");
    fs::create_dir_all(sym_art.join("capture")).unwrap();
    fs::copy(art_dir.join("request.json"), sym_art.join("request.json")).unwrap();
    fs::copy(art_dir.join("capture/capture.json"), sym_art.join("capture/capture.json")).unwrap();
    fs::copy(art_dir.join("result.json"), sym_art.join("result.json")).unwrap();
    symlink(&outside, sym_art.join("rust")).unwrap();
    let sym_fail = run_inspect(
        &[clean_path.to_str().unwrap(), "--verify-artifacts", sym_art.to_str().unwrap()],
        None,
    );
    assert_eq!(sym_fail.status.code(), Some(1));

    // Tampered source digest fails verification.
    fs::write(art_dir.join("rust/src/lib.rs"), b"pub fn zero() -> u32 { 1 }\n").unwrap();
    let tamper_fail = run_inspect(
        &[clean_path.to_str().unwrap(), "--verify-artifacts", art_dir.to_str().unwrap()],
        None,
    );
    assert_eq!(tamper_fail.status.code(), Some(1));

    (sorry_tainted, sorry_path, s3_gutns, cap_bin_sha)
}
