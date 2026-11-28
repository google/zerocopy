// Copyright 2026 The Fuchsia Authors
//
// Licensed under a BSD-style license <LICENSE-BSD>, Apache License, Version 2.0
// <LICENSE-APACHE or https://www.apache.org/licenses/LICENSE-2.0>, or the MIT
// license <LICENSE-MIT or https://opensource.org/licenses/MIT>, at your option.
// This file may not be copied, modified, or distributed except according to
// those terms.

//! `inspect --verify-artifacts` and the three-tier receipt diff.

use super::*;

#[test]
fn verify_artifacts_and_three_tier_diff_enforced() {
    let tmp = tempfile::tempdir().unwrap();
    let art_dir = tmp.path().join("artifacts");
    let (clean, ..) = sample_receipt_bundle(&art_dir);
    let clean_path = tmp.path().join("clean.json");
    fs::write(&clean_path, serde_json::to_vec(&clean).unwrap()).unwrap();

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

    // 3-tier --diff: Tier A downgrade fails --no-regressions; Tier C passes.
    let mut head_downgrade = clean.clone();
    head_downgrade["status"] = json!("tainted_crate_verified");
    head_downgrade["taint_reasons"] = json!(["unsandboxed_elaboration"]);
    head_downgrade["elaboration_sandbox"] = json!("none");
    head_downgrade["deferred"] = json!(["hostile Lean elaborator effects"]);
    let head_down_path = tmp.path().join("head_down.json");
    fs::write(&head_down_path, serde_json::to_vec(&head_downgrade).unwrap()).unwrap();

    let reg_fail = run_inspect(
        &[
            "--diff",
            clean_path.to_str().unwrap(),
            head_down_path.to_str().unwrap(),
            "--no-regressions",
            "--format",
            "json",
        ],
        None,
    );
    assert_eq!(reg_fail.status.code(), Some(1));
    let diff_json: Value = serde_json::from_slice(&reg_fail.stdout).unwrap();
    assert_eq!(diff_json["has_regressions"], true);

    let mut head_timing = clean.clone();
    head_timing["timing_ms"]["total"] = json!(99);
    let head_timing_path = tmp.path().join("head_timing.json");
    fs::write(&head_timing_path, serde_json::to_vec(&head_timing).unwrap()).unwrap();
    let timing_ok = run_inspect(
        &[
            "--diff",
            clean_path.to_str().unwrap(),
            head_timing_path.to_str().unwrap(),
            "--no-regressions",
        ],
        None,
    );
    assert_eq!(timing_ok.status.code(), Some(0));

    // Added assumption / deferred / newly-experimental regressions fail
    // `--no-regressions`, whereas taint removal (improvement) exits 0.
    let mut head_assump = clean.clone();
    head_assump["assumptions"] = json!(["Rust MIR semantics", "extra"]);
    let head_assump_path = tmp.path().join("head_assump.json");
    fs::write(&head_assump_path, serde_json::to_vec(&head_assump).unwrap()).unwrap();
    assert_eq!(
        run_inspect(
            &[
                "--diff",
                clean_path.to_str().unwrap(),
                head_assump_path.to_str().unwrap(),
                "--no-regressions"
            ],
            None,
        )
        .status
        .code(),
        Some(1)
    );
    assert_eq!(
        run_inspect(
            &[
                "--diff",
                head_down_path.to_str().unwrap(),
                clean_path.to_str().unwrap(),
                "--no-regressions"
            ],
            None,
        )
        .status
        .code(),
        Some(0)
    );

    // Missing base `horizon` (unbounded) followed by bounded head fails
    // `--no-regressions`.
    let mut head_bounded = clean.clone();
    head_bounded["horizon"] = json!({"kind": "bounded", "k": 8});
    let head_bounded_path = tmp.path().join("head_bounded.json");
    fs::write(&head_bounded_path, serde_json::to_vec(&head_bounded).unwrap()).unwrap();
    assert_eq!(
        run_inspect(
            &[
                "--diff",
                clean_path.to_str().unwrap(),
                head_bounded_path.to_str().unwrap(),
                "--no-regressions"
            ],
            None,
        )
        .status
        .code(),
        Some(1)
    );

    // Multibyte UTF-8 at byte 12 + ANSI/bidi in digest must never panic.
    let mut bad_digest = clean.clone();
    bad_digest["request_sha256"] = json!("0123456789\u{00E9}\x1b[31m\u{206A}\u{3164}");
    let bad_digest_path = tmp.path().join("bad_digest.json");
    fs::write(&bad_digest_path, serde_json::to_vec(&bad_digest).unwrap()).unwrap();
    for fmt in ["human", "ledger", "markdown"] {
        let out =
            run_inspect(&[bad_digest_path.to_str().unwrap(), "--format", fmt, "--passive"], None);
        assert_eq!(out.status.code(), Some(1), "fmt={fmt}");
        let s = String::from_utf8(out.stdout).unwrap();
        assert!(!s.contains('\x1b'));
        assert!(!s.contains('\u{206A}'));
        assert!(!s.contains('\u{3164}'));
    }

    // `configuration.stdlib_crate` ("core") passes `--unknown-fields deny`.
    let mut stdlib_core = clean.clone();
    stdlib_core["configuration"]["stdlib_crate"] = json!("core");
    let stdlib_core_path = tmp.path().join("stdlib_core.json");
    fs::write(&stdlib_core_path, serde_json::to_vec(&stdlib_core).unwrap()).unwrap();
    let stdlib_ok =
        run_inspect(&[stdlib_core_path.to_str().unwrap(), "--unknown-fields", "deny"], None);
    assert_eq!(
        stdlib_ok.status.code(),
        Some(0),
        "stderr={}",
        String::from_utf8_lossy(&stdlib_ok.stderr)
    );

    // Symlinked artifacts root with trailing `/`, `///`, `/.`, or `/..` must
    // be rejected.
    let sym_root = tmp.path().join("sym_root");
    symlink(&art_dir, &sym_root).unwrap();
    for (suffix, expected_err) in [
        ("/", "regular non-symlink directory"),
        ("///", "regular non-symlink directory"),
        ("/.", "concrete non-dot directory"),
        ("/..", "concrete non-dot directory"),
    ] {
        let trailing = format!("{}{suffix}", sym_root.display());
        let sym_root_fail =
            run_inspect(&[clean_path.to_str().unwrap(), "--verify-artifacts", &trailing], None);
        assert_eq!(sym_root_fail.status.code(), Some(2), "suffix={suffix}");
        let stderr = String::from_utf8_lossy(&sym_root_fail.stderr);
        assert!(stderr.contains(expected_err), "suffix={suffix}, stderr={stderr}");
    }

    // `--diff` fails closed (`exit 1`) on warn-mode unrecognized fields unless
    // `--passive` is supplied.
    let mut ext_head = clean.clone();
    ext_head["future_extension"] = json!("hello");
    let ext_head_path = tmp.path().join("ext_head.json");
    fs::write(&ext_head_path, serde_json::to_vec(&ext_head).unwrap()).unwrap();
    let ext_warn_fail = run_inspect(
        &["--diff", clean_path.to_str().unwrap(), ext_head_path.to_str().unwrap()],
        None,
    );
    assert_eq!(ext_warn_fail.status.code(), Some(1));
    assert!(String::from_utf8_lossy(&ext_warn_fail.stderr).contains("unrecognized"));
    let ext_passive_ok = run_inspect(
        &["--diff", clean_path.to_str().unwrap(), ext_head_path.to_str().unwrap(), "--passive"],
        None,
    );
    assert_eq!(ext_passive_ok.status.code(), Some(0));
    let ext_passive_stdout = String::from_utf8_lossy(&ext_passive_ok.stdout);
    assert!(ext_passive_stdout.contains("[UNVERIFIED EXTENSIONS]"), "{ext_passive_stdout}");
    assert!(ext_passive_stdout.contains("/future_extension"), "{ext_passive_stdout}");
    let ext_passive_md = run_inspect(
        &[
            "--diff",
            clean_path.to_str().unwrap(),
            ext_head_path.to_str().unwrap(),
            "--passive",
            "--format",
            "markdown",
        ],
        None,
    );
    assert_eq!(ext_passive_md.status.code(), Some(0));
    let ext_md_out = String::from_utf8_lossy(&ext_passive_md.stdout);
    assert!(ext_md_out.contains("UNVERIFIED EXTENSIONS"), "{ext_md_out}");
    assert!(ext_md_out.contains("`/future_extension`"), "{ext_md_out}");

    // `--diff` surfaces invariant violations instead of `NO REGRESSIONS`.
    let invalid_diff = run_inspect(
        &["--diff", clean_path.to_str().unwrap(), bad_digest_path.to_str().unwrap()],
        None,
    );
    assert_eq!(invalid_diff.status.code(), Some(1));
    let invalid_stdout = String::from_utf8_lossy(&invalid_diff.stdout);
    assert!(invalid_stdout.contains("INVALID ENVELOPE(S)"), "{invalid_stdout}");
    assert!(!invalid_stdout.contains("NO REGRESSIONS"), "{invalid_stdout}");
    assert!(
        String::from_utf8_lossy(&invalid_diff.stderr).contains("invariant violation"),
        "stderr={}",
        String::from_utf8_lossy(&invalid_diff.stderr)
    );

    // Swapped `scope.instantiations`, `sorry` growth, `forward <-> backward`,
    // and new `spec_warnings` all fail `--diff --no-regressions`; shim
    // upgrades (`assumed` -> `proved`) pass.
    let mut inst_a = clean.clone();
    inst_a["status"] = json!("selected_unit_verified");
    inst_a["scope"] = json!({
        "kind": "selected_unit",
        "roots": ["foo"],
        "instantiations": [{"path": "foo", "args": ["u8"]}]
    });
    inst_a["audit"]["canonicalRoot"] = json!("Trusted.MirSemantics.UnitTheorem");
    let mut inst_b = inst_a.clone();
    inst_b["scope"]["instantiations"] = json!([{"path": "foo", "args": ["u16"]}]);
    let inst_a_path = tmp.path().join("inst_a.json");
    let inst_b_path = tmp.path().join("inst_b.json");
    fs::write(&inst_a_path, serde_json::to_vec(&inst_a).unwrap()).unwrap();
    fs::write(&inst_b_path, serde_json::to_vec(&inst_b).unwrap()).unwrap();
    let inst_reg_out = run_inspect(
        &[
            "--diff",
            inst_a_path.to_str().unwrap(),
            inst_b_path.to_str().unwrap(),
            "--no-regressions",
        ],
        None,
    );
    assert_eq!(inst_reg_out.status.code(), Some(1));
    let inst_reg_stdout = String::from_utf8_lossy(&inst_reg_out.stdout);
    assert!(inst_reg_stdout.contains("REGRESSIONS DETECTED"), "{inst_reg_stdout}");
    assert!(!inst_reg_stdout.contains("INVALID ENVELOPE(S)"), "{inst_reg_stdout}");
    assert!(inst_reg_stdout.contains("scope.instantiations"), "{inst_reg_stdout}");
    assert!(
        inst_reg_out.stderr.is_empty(),
        "stderr={}",
        String::from_utf8_lossy(&inst_reg_out.stderr)
    );
    let inst_diff_only = run_inspect(
        &[
            "--diff",
            inst_a_path.to_str().unwrap(),
            inst_b_path.to_str().unwrap(),
            "--format",
            "json",
        ],
        None,
    );
    assert_eq!(inst_diff_only.status.code(), Some(0));
    let inst_diff_json: Value = serde_json::from_slice(&inst_diff_only.stdout).unwrap();
    assert_eq!(inst_diff_json["has_regressions"], true);
    assert!(inst_diff_json.get("base_invariant_violations").is_none());
    assert!(inst_diff_json.get("head_invariant_violations").is_none());
    assert!(
        inst_diff_json["changes"]
            .as_array()
            .unwrap()
            .iter()
            .any(|c| c["field"] == "scope.instantiations" && c["tier"] == "tier_a")
    );

    let mut sorry_mismatch = sorry_tainted.clone();
    sorry_mismatch["sorry_declarations"] = json!(["Proof.other"]);
    let sorry_mismatch_path = tmp.path().join("sorry_mismatch.json");
    fs::write(&sorry_mismatch_path, serde_json::to_vec(&sorry_mismatch).unwrap()).unwrap();
    assert_eq!(
        run_inspect(&[sorry_mismatch_path.to_str().unwrap(), "--passive"], None).status.code(),
        Some(1)
    );

    let mut sorry_two = sorry_tainted.clone();
    sorry_two["sorry_declarations"] = json!(["Proof.hole", "Proof.two"]);
    sorry_two["audit"]["sorryDeclarations"] = json!(["Proof.hole", "Proof.two"]);
    let sorry_two_path = tmp.path().join("sorry_two.json");
    fs::write(&sorry_two_path, serde_json::to_vec(&sorry_two).unwrap()).unwrap();
    assert_eq!(
        run_inspect(
            &[
                "--diff",
                sorry_path.to_str().unwrap(),
                sorry_two_path.to_str().unwrap(),
                "--no-regressions"
            ],
            None
        )
        .status
        .code(),
        Some(1)
    );

    let mut dir_fwd = clean.clone();
    dir_fwd["model_system_relation"] = json!({
        "kind": "simulation",
        "qualifier": "wf_stutter",
        "direction": "forward",
        "licensed_claim_shapes": ["forall_safety"]
    });
    let mut dir_bwd = dir_fwd.clone();
    dir_bwd["model_system_relation"]["direction"] = json!("backward");
    let dir_fwd_path = tmp.path().join("dir_fwd.json");
    let dir_bwd_path = tmp.path().join("dir_bwd.json");
    fs::write(&dir_fwd_path, serde_json::to_vec(&dir_fwd).unwrap()).unwrap();
    fs::write(&dir_bwd_path, serde_json::to_vec(&dir_bwd).unwrap()).unwrap();
    assert_eq!(
        run_inspect(
            &[
                "--diff",
                dir_fwd_path.to_str().unwrap(),
                dir_bwd_path.to_str().unwrap(),
                "--no-regressions"
            ],
            None
        )
        .status
        .code(),
        Some(1)
    );

    let mut shim_assumed = clean.clone();
    shim_assumed["tcb_shims"] = json!([{
        "id": "seam_upgrade",
        "kind": "capture_driver",
        "sha256": cap_bin_sha,
        "status": "assumed"
    }]);
    let mut shim_proved = shim_assumed.clone();
    shim_proved["tcb_shims"][0]["status"] = json!("proved");
    let shim_a_path = tmp.path().join("shim_assumed.json");
    let shim_p_path = tmp.path().join("shim_proved.json");
    fs::write(&shim_a_path, serde_json::to_vec(&shim_assumed).unwrap()).unwrap();
    fs::write(&shim_p_path, serde_json::to_vec(&shim_proved).unwrap()).unwrap();
    assert_eq!(
        run_inspect(
            &[
                "--diff",
                shim_a_path.to_str().unwrap(),
                shim_p_path.to_str().unwrap(),
                "--no-regressions"
            ],
            None
        )
        .status
        .code(),
        Some(0)
    );

    let mut head_warn = clean.clone();
    let warn_entries = json!([{
        "code": "unsatisfiable_safety",
        "declaration": "Spec.bad",
        "message": "ensures is unsatisfiable"
    }]);
    head_warn["spec_warnings"] = warn_entries.clone();
    head_warn["audit"]["specWarnings"] = warn_entries.clone();
    let head_warn_path = tmp.path().join("head_warn.json");
    fs::write(&head_warn_path, serde_json::to_vec(&head_warn).unwrap()).unwrap();
    let warn_reg_out = run_inspect(
        &[
            "--diff",
            clean_path.to_str().unwrap(),
            head_warn_path.to_str().unwrap(),
            "--no-regressions",
        ],
        None,
    );
    assert_eq!(warn_reg_out.status.code(), Some(1));
    let warn_reg_stdout = String::from_utf8_lossy(&warn_reg_out.stdout);
    assert!(warn_reg_stdout.contains("REGRESSIONS DETECTED"), "{warn_reg_stdout}");
    assert!(!warn_reg_stdout.contains("INVALID ENVELOPE(S)"), "{warn_reg_stdout}");

    // Stripped top-level `spec_warnings` vs `audit.specWarnings`, malformed
    // `audit.specWarnings`, and extra keys inside `audit.specWarnings` fail
    // closed.
    let mut stripped_warn = clean.clone();
    stripped_warn["audit"]["specWarnings"] = warn_entries.clone();
    let stripped_warn_path = tmp.path().join("stripped_warn.json");
    fs::write(&stripped_warn_path, serde_json::to_vec(&stripped_warn).unwrap()).unwrap();
    let stripped_out = run_inspect(&[stripped_warn_path.to_str().unwrap(), "--passive"], None);
    assert_eq!(stripped_out.status.code(), Some(1));
    assert!(
        String::from_utf8_lossy(&stripped_out.stdout).contains("differs from `audit.specWarnings`")
    );
    let mut extra_audit_warn = clean.clone();
    extra_audit_warn["spec_warnings"] = warn_entries;
    extra_audit_warn["audit"]["specWarnings"] = json!([{
        "code": "unsatisfiable_safety",
        "declaration": "Spec.bad",
        "message": "ensures is unsatisfiable",
        "extra_audit_key": true
    }]);
    let extra_audit_warn_path = tmp.path().join("extra_audit_warn.json");
    fs::write(&extra_audit_warn_path, serde_json::to_vec(&extra_audit_warn).unwrap()).unwrap();
    assert_eq!(
        run_inspect(&[extra_audit_warn_path.to_str().unwrap(), "--unknown-fields", "deny"], None)
            .status
            .code(),
        Some(2)
    );
    let mut bad_audit_warn = clean.clone();
    bad_audit_warn["audit"]["specWarnings"] = json!("not-an-array");
    let bad_audit_warn_path = tmp.path().join("bad_audit_warn.json");
    fs::write(&bad_audit_warn_path, serde_json::to_vec(&bad_audit_warn).unwrap()).unwrap();
    assert_eq!(run_inspect(&[bad_audit_warn_path.to_str().unwrap()], None).status.code(), Some(2));

    let mut orphan_seam = s3_gutns.clone();
    orphan_seam["correspondence_provenance"]["tcb_shims"].as_array_mut().unwrap().push(json!({
        "id": "orphan_seam",
        "kind": "assumed_seam",
        "sha256": cap_bin_sha,
        "status": "assumed"
    }));
    let orphan_seam_path = tmp.path().join("orphan_seam.json");
    fs::write(&orphan_seam_path, serde_json::to_vec(&orphan_seam).unwrap()).unwrap();
    assert_eq!(
        run_inspect(&[orphan_seam_path.to_str().unwrap(), "--passive"], None).status.code(),
        Some(1)
    );

    // Omitting `minirust_upstream` on an applicable Profile v1 receipt fails
    // closed operationally (exit 2).
    let mut missing_minirust = clean.clone();
    missing_minirust["correspondence_provenance"]
        .as_object_mut()
        .unwrap()
        .remove("minirust_upstream");
    let missing_minirust_path = tmp.path().join("missing_minirust.json");
    fs::write(&missing_minirust_path, serde_json::to_vec(&missing_minirust).unwrap()).unwrap();
    let missing_minirust_out = run_inspect(&[missing_minirust_path.to_str().unwrap()], None);
    assert_eq!(missing_minirust_out.status.code(), Some(2));
    assert!(
        String::from_utf8_lossy(&missing_minirust_out.stderr)
            .contains("/correspondence_provenance/minirust_upstream"),
        "{}",
        String::from_utf8_lossy(&missing_minirust_out.stderr)
    );

    // Profile v2 receipts (`*TheoremV2`, Profile v2 MIR assumption, and
    // pinned `correspondence_provenance.applicable == false`) pass strict
    // validation across CLI formats and diffing, while mismatches fail closed.
    let mut v2_unit = clean.clone();
    v2_unit["status"] = json!("selected_unit_verified");
    v2_unit["scope"] = json!({
        "kind": "selected_unit",
        "roots": ["scalar::zero"],
        "instantiations": [{ "path": "scalar::zero", "args": [] }]
    });
    v2_unit["audit"]["canonicalRoot"] = json!("Trusted.MirSemantics.UnitTheoremV2");
    v2_unit["audit"]["modelClosure"] = json!([{
        "name": "Trusted.MirSemantics.UnitTheoremV2",
        "module": "Trusted.MirSemantics"
    }]);
    v2_unit["assumptions"] = json!([
        "faithful pinned compiler capture",
        "experimental Profile v2 MIR semantics: bounded caller memory"
    ]);
    v2_unit["correspondence_provenance"] = json!({
        "applicable": false,
        "reason": "bundled Pass 2 correspondence covers Profile v1 semantics only"
    });
    let v2_unit_path = tmp.path().join("v2_unit.json");
    fs::write(&v2_unit_path, serde_json::to_vec(&v2_unit).unwrap()).unwrap();

    let v2_json = run_inspect(
        &[
            v2_unit_path.to_str().unwrap(),
            "--require-untainted",
            "--unknown-fields",
            "deny",
            "--format",
            "json",
        ],
        None,
    );
    assert_eq!(v2_json.status.code(), Some(0), "{}", String::from_utf8_lossy(&v2_json.stderr));
    assert!(v2_json.stderr.is_empty());
    let v2_parsed: Value = serde_json::from_slice(&v2_json.stdout).unwrap();
    assert_eq!(v2_parsed["status"], "selected_unit_verified");
    assert_eq!(v2_parsed["tainted"], false);
    assert_eq!(v2_parsed["unrecognized_fields"], json!([]));
    assert_eq!(v2_parsed["invariant_violations"], json!([]));
    assert_eq!(v2_parsed["policy_violations"], json!([]));
    let receipt_str = serde_json::to_string(&v2_parsed["receipt"]).unwrap();
    assert!(receipt_str.contains("\"correspondence_applicable\":false"), "{receipt_str}");
    assert!(receipt_str.contains("Trusted.MirSemantics.UnitTheoremV2"), "{receipt_str}");

    let v2_ledger = run_inspect(&[v2_unit_path.to_str().unwrap(), "--format", "ledger"], None);
    assert_eq!(v2_ledger.status.code(), Some(0));
    assert!(
        String::from_utf8_lossy(&v2_ledger.stdout)
            .contains("audit.canonical_root=Trusted.MirSemantics.UnitTheoremV2\n")
    );
    let v2_human = run_inspect(&[v2_unit_path.to_str().unwrap(), "--format", "human"], None);
    assert_eq!(v2_human.status.code(), Some(0));
    let v2_human_out = String::from_utf8_lossy(&v2_human.stdout);
    assert!(v2_human_out.contains("Trusted.MirSemantics.UnitTheoremV2"), "{v2_human_out}");
    // Pass 2 does not certify Profile v2, so the success is qualified.
    assert!(v2_human_out.contains(" [QUALIFIED]\n"), "{v2_human_out}");
    assert!(v2_human_out.contains("correspondence=inapplicable"), "{v2_human_out}");
    assert!(v2_human_out.contains("  correspondence: inapplicable ("), "{v2_human_out}");
    let v2_md = run_inspect(&[v2_unit_path.to_str().unwrap(), "--format", "markdown"], None);
    assert_eq!(v2_md.status.code(), Some(0));
    let v2_md_out = String::from_utf8_lossy(&v2_md.stdout);
    assert!(v2_md_out.contains("selected_unit_verified"), "{v2_md_out}");
    assert!(v2_md_out.contains("`untainted`"), "{v2_md_out}");
    assert!(v2_md_out.contains("`correspondence=inapplicable`"), "{v2_md_out}");

    let v1_to_v2_diff = run_inspect(
        &[
            "--diff",
            clean_path.to_str().unwrap(),
            v2_unit_path.to_str().unwrap(),
            "--format",
            "json",
        ],
        None,
    );
    assert_eq!(v1_to_v2_diff.status.code(), Some(0));
    let diff_json: Value = serde_json::from_slice(&v1_to_v2_diff.stdout).unwrap();
    assert!(
        diff_json["changes"]
            .as_array()
            .unwrap()
            .iter()
            .any(|c| c["field"] == "audit.canonicalRoot"),
        "{diff_json}"
    );

    let mut v2_missing_assump = v2_unit.clone();
    v2_missing_assump["assumptions"] = json!(["faithful pinned compiler capture"]);
    let v2_missing_assump_path = tmp.path().join("v2_missing_assump.json");
    fs::write(&v2_missing_assump_path, serde_json::to_vec(&v2_missing_assump).unwrap()).unwrap();
    let v2_missing_out =
        run_inspect(&[v2_missing_assump_path.to_str().unwrap(), "--passive"], None);
    assert_eq!(v2_missing_out.status.code(), Some(1));
    assert!(
        String::from_utf8_lossy(&v2_missing_out.stdout)
            .contains("disagrees with Profile v2 `assumptions`")
    );

    let mut v2_v1_prov = v2_unit;
    v2_v1_prov["correspondence_provenance"] = clean["correspondence_provenance"].clone();
    let v2_v1_prov_path = tmp.path().join("v2_v1_prov.json");
    fs::write(&v2_v1_prov_path, serde_json::to_vec(&v2_v1_prov).unwrap()).unwrap();
    let v2_v1_prov_out = run_inspect(&[v2_v1_prov_path.to_str().unwrap(), "--passive"], None);
    assert_eq!(v2_v1_prov_out.status.code(), Some(1));
    assert!(
        String::from_utf8_lossy(&v2_v1_prov_out.stdout)
            .contains("correspondence_provenance.applicable == false")
    );

    // Multi-kernel replay downgrades, spec symbol swaps, tcb_shims order
    // invariance, and `anchored_at` regressions in `--diff`.
    let mut base_mk = clean.clone();
    base_mk["audit"]["auditMode"] = json!("paranoid");
    base_mk["audit"]["kernelsPassed"] = json!(["lean4", "nanoda"]);
    base_mk["audit"]["paranoidQuorum"] = json!(true);
    let base_mk_path = tmp.path().join("base_mk.json");
    fs::write(&base_mk_path, serde_json::to_vec(&base_mk).unwrap()).unwrap();
    let mut head_mk = base_mk.clone();
    head_mk["audit"]["auditMode"] = json!("strict");
    head_mk["audit"]["kernelsPassed"] = json!(["lean4"]);
    head_mk["audit"]["kernelsSkipped"] = json!(["nanoda"]);
    head_mk["audit"]["paranoidQuorum"] = json!(false);
    let head_mk_path = tmp.path().join("head_mk.json");
    fs::write(&head_mk_path, serde_json::to_vec(&head_mk).unwrap()).unwrap();
    let mk_diff = run_inspect(
        &[
            "--diff",
            base_mk_path.to_str().unwrap(),
            head_mk_path.to_str().unwrap(),
            "--no-regressions",
            "--format",
            "json",
        ],
        None,
    );
    assert_eq!(mk_diff.status.code(), Some(1));
    let mk_diff_json: Value = serde_json::from_slice(&mk_diff.stdout).unwrap();
    let mk_fields: Vec<&str> = mk_diff_json["changes"]
        .as_array()
        .unwrap()
        .iter()
        .filter(|c| c["tier"] == "tier_a")
        .map(|c| c["field"].as_str().unwrap())
        .collect();
    for expected in
        ["audit.kernelsPassed", "audit.auditMode", "audit.kernelsSkipped", "audit.paranoidQuorum"]
    {
        assert!(mk_fields.contains(&expected), "missing Tier A `{expected}` in {mk_fields:?}");
    }

    // `--require-unchanged-specs` catches `audit.specification` symbol change
    // and exits `1` even without `--no-regressions`.
    let mut spec_swap = clean.clone();
    spec_swap["audit"]["specification"] = json!("Spec.zero_alt");
    let spec_swap_path = tmp.path().join("spec_swap.json");
    fs::write(&spec_swap_path, serde_json::to_vec(&spec_swap).unwrap()).unwrap();
    let spec_swap_standalone = run_inspect(
        &[
            "--diff",
            clean_path.to_str().unwrap(),
            spec_swap_path.to_str().unwrap(),
            "--require-unchanged-specs",
        ],
        None,
    );
    assert_eq!(spec_swap_standalone.status.code(), Some(1));
    let spec_swap_diff = run_inspect(
        &[
            "--diff",
            clean_path.to_str().unwrap(),
            spec_swap_path.to_str().unwrap(),
            "--require-unchanged-specs",
            "--no-regressions",
        ],
        None,
    );
    assert_eq!(spec_swap_diff.status.code(), Some(1));

    // Reordering `tcb_shims` and nested `guards` produces zero diff changes.
    let mut shims_a = clean.clone();
    shims_a["tcb_shims"] = json!([
        {
            "id": "s1",
            "kind": "append_only_spec_lemma",
            "sha256": "1".repeat(64),
            "status": "proved",
            "guards": ["g1", "g2"]
        },
        {
            "id": "s2",
            "kind": "capture_driver",
            "sha256": "e".repeat(64),
            "status": "tested",
            "guards": ["g3"]
        }
    ]);
    let mut shims_b = clean.clone();
    shims_b["tcb_shims"] = json!([
        {
            "id": "s2",
            "kind": "capture_driver",
            "sha256": "e".repeat(64),
            "status": "tested",
            "guards": ["g3"]
        },
        {
            "id": "s1",
            "kind": "append_only_spec_lemma",
            "sha256": "1".repeat(64),
            "status": "proved",
            "guards": ["g2", "g1"]
        }
    ]);
    let shims_a_path = tmp.path().join("shims_a.json");
    let shims_b_path = tmp.path().join("shims_b.json");
    fs::write(&shims_a_path, serde_json::to_vec(&shims_a).unwrap()).unwrap();
    fs::write(&shims_b_path, serde_json::to_vec(&shims_b).unwrap()).unwrap();
    let shims_diff = run_inspect(
        &[
            "--diff",
            shims_a_path.to_str().unwrap(),
            shims_b_path.to_str().unwrap(),
            "--no-regressions",
            "--format",
            "json",
        ],
        None,
    );
    assert_eq!(shims_diff.status.code(), Some(0));
    let shims_json: Value = serde_json::from_slice(&shims_diff.stdout).unwrap();
    assert_eq!(shims_json["changes"], json!([]));

    // Dropping `anchored_at` on `model_system_relation` is a Tier A regression.
    let mut rel_a = clean.clone();
    rel_a["model_system_relation"] = json!({
        "kind": "simulation",
        "qualifier": "lock_step",
        "direction": "forward",
        "anchored_at": "mir_op",
        "licensed_claim_shapes": ["forall_safety"]
    });
    let mut rel_b = rel_a.clone();
    rel_b["model_system_relation"].as_object_mut().unwrap().remove("anchored_at");
    let rel_a_path = tmp.path().join("rel_a.json");
    let rel_b_path = tmp.path().join("rel_b.json");
    fs::write(&rel_a_path, serde_json::to_vec(&rel_a).unwrap()).unwrap();
    fs::write(&rel_b_path, serde_json::to_vec(&rel_b).unwrap()).unwrap();
    let rel_diff = run_inspect(
        &[
            "--diff",
            rel_a_path.to_str().unwrap(),
            rel_b_path.to_str().unwrap(),
            "--no-regressions",
            "--format",
            "json",
        ],
        None,
    );
    assert_eq!(rel_diff.status.code(), Some(1));
    let rel_json: Value = serde_json::from_slice(&rel_diff.stdout).unwrap();
    assert!(
        rel_json["changes"][0]["base"].as_str().unwrap().contains("anchor=mir_op"),
        "{rel_json}"
    );

    // `candidate_features` mismatch fails validation and newly added candidate
    // features fail `--diff --no-regressions`.
    let mut bad_cf = clean.clone();
    bad_cf["experimental"] = json!(false);
    bad_cf["candidate_features"] = json!(["mir_semantics"]);
    let bad_cf_path = tmp.path().join("bad_cf.json");
    fs::write(&bad_cf_path, serde_json::to_vec(&bad_cf).unwrap()).unwrap();
    let bad_cf_out = run_inspect(&[bad_cf_path.to_str().unwrap(), "--passive"], None);
    assert_eq!(bad_cf_out.status.code(), Some(1));
    assert!(String::from_utf8_lossy(&bad_cf_out.stdout).contains("candidate_features"));

    let mut head_cf = clean.clone();
    head_cf["experimental"] = json!(true);
    head_cf["candidate_features"] = json!(["mir_semantics"]);
    let head_cf_path = tmp.path().join("head_cf.json");
    fs::write(&head_cf_path, serde_json::to_vec(&head_cf).unwrap()).unwrap();
    let cf_diff = run_inspect(
        &[
            "--diff",
            clean_path.to_str().unwrap(),
            head_cf_path.to_str().unwrap(),
            "--no-regressions",
            "--format",
            "json",
        ],
        None,
    );
    assert_eq!(cf_diff.status.code(), Some(1));
    let cf_diff_json: Value = serde_json::from_slice(&cf_diff.stdout).unwrap();
    assert!(
        cf_diff_json["changes"]
            .as_array()
            .unwrap()
            .iter()
            .any(|c| c["field"] == "candidate_features" && c["tier"] == "tier_a"),
        "{cf_diff_json}"
    );
}
