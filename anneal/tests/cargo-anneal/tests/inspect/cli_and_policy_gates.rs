// Copyright 2026 The Fuchsia Authors
//
// Licensed under a BSD-style license <LICENSE-BSD>, Apache License, Version 2.0
// <LICENSE-APACHE or https://www.apache.org/licenses/LICENSE-2.0>, or the MIT
// license <LICENSE-MIT or https://opensource.org/licenses/MIT>, at your option.
// This file may not be copied, modified, or distributed except according to
// those terms.

//! `inspect` argument handling, strict JSON errors, and policy gates.

use super::*;

#[test]
fn cli_help_argument_conflicts_and_strict_json_errors() {
    let help = run_inspect(&["--help"], None);
    assert!(help.status.success(), "{help:?}");
    let cargo_help = run_cargo_subcommand_inspect(&["--help"]);
    assert!(cargo_help.status.success(), "{cargo_help:?}");
    assert_eq!(help.stdout, cargo_help.stdout);

    let tmp = tempfile::tempdir().unwrap();
    let r_path = tmp.path().join("r.json");
    let (valid, ..) = sample_receipt_bundle(&tmp.path().join("art"));
    fs::write(&r_path, serde_json::to_vec(&valid).unwrap()).unwrap();

    // Parse-time argument conflicts exit 2.
    for bad_args in [
        vec!["--diff", "-", "-"],
        vec!["--diff", r_path.to_str().unwrap(), r_path.to_str().unwrap(), "--check"],
        vec![r_path.to_str().unwrap(), "--require-exact-artifacts"],
    ] {
        let out = run_inspect(&bad_args, None);
        assert_eq!(out.status.code(), Some(2), "{bad_args:?}: {out:?}");
    }

    // Duplicate keys (even nested) must fail cleanly with exit 2.
    let dup_path = tmp.path().join("dup.json");
    fs::write(&dup_path, br#"{"schema_version":3,"schema_version":3,"status":"crate_verified"}"#)
        .unwrap();
    let dup_out = run_inspect(&[dup_path.to_str().unwrap()], None);
    assert_eq!(dup_out.status.code(), Some(2), "{dup_out:?}");
    assert!(String::from_utf8_lossy(&dup_out.stderr).contains("duplicate"));

    // Symlink receipt must fail closed via O_NOFOLLOW with exit 2.
    let sym_receipt = tmp.path().join("sym.json");
    symlink(&r_path, &sym_receipt).unwrap();
    let sym_out = run_inspect(&[sym_receipt.to_str().unwrap()], None);
    assert_eq!(sym_out.status.code(), Some(2), "{sym_out:?}");
}

#[test]
fn policy_gates_cross_checks_unknown_fields_and_sanitization() {
    let tmp = tempfile::tempdir().unwrap();
    let art_dir = tmp.path().join("artifacts");
    let (mut clean, ..) = sample_receipt_bundle(&art_dir);
    let clean_bytes = serde_json::to_vec(&clean).unwrap();
    let clean_path = tmp.path().join("clean.json");
    fs::write(&clean_path, &clean_bytes).unwrap();

    // Clean verified crate passes all strict gates, stdin, and JSON rendering.
    let ok = run_inspect(
        &[
            "-",
            "--check",
            "--require-untainted",
            "--require-crate-scope",
            "--require-containment",
            "--require-kernel-replay",
            "1",
            "--allowed-axioms",
            "propext,Classical.choice,Quot.sound",
            "--unknown-fields",
            "deny",
            "--format",
            "json",
        ],
        Some(&clean_bytes),
    );
    assert_eq!(ok.status.code(), Some(0), "stderr={}", String::from_utf8_lossy(&ok.stderr));
    let parsed_out: Value = serde_json::from_slice(&ok.stdout).unwrap();
    assert_eq!(parsed_out["profile"]["scope"]["kind"], "whole_crate");
    assert_eq!(parsed_out["invariant_violations"].as_array().unwrap().len(), 0);

    // Unknown fields: default `warn` renders UNVERIFIED EXTENSIONS, warns on
    // stderr, and fails validator mode (`exit 1`) while passing under
    // `--passive` (`exit 0`); `deny` exits `2`.
    clean["future_ext_field"] = json!({"k": 1});
    clean["unknown_test_field"] = json!(["fake"]);
    clean["census"][0]["extra_census"] = json!(true);
    let ext_path = tmp.path().join("ext.json");
    fs::write(&ext_path, serde_json::to_vec(&clean).unwrap()).unwrap();
    let warn_out = run_inspect(&[ext_path.to_str().unwrap(), "--unknown-fields", "warn"], None);
    assert_eq!(warn_out.status.code(), Some(1), "{}", String::from_utf8_lossy(&warn_out.stdout));
    let warn_stdout = String::from_utf8_lossy(&warn_out.stdout);
    assert!(warn_stdout.contains("UNVERIFIED EXTENSIONS"), "{warn_stdout}");
    let warn_err = String::from_utf8_lossy(&warn_out.stderr);
    assert!(warn_err.contains("/future_ext_field"), "{warn_err}");
    assert!(warn_err.contains("/unknown_test_field"), "{warn_err}");
    assert!(warn_err.contains("/census/0/extra_census"), "{warn_err}");
    let passive_warn_out =
        run_inspect(&[ext_path.to_str().unwrap(), "--unknown-fields", "warn", "--passive"], None);
    assert_eq!(passive_warn_out.status.code(), Some(0));
    let deny_out = run_inspect(&[ext_path.to_str().unwrap(), "--unknown-fields", "deny"], None);
    assert_eq!(deny_out.status.code(), Some(2));

    // Nonzero `checkedAlternateProofs` (kernel-checked alternate proof bodies
    // of realized theorems) is accepted and diffs as Tier C (not a regression).
    let (mut nonzero_alt, ..) = sample_receipt_bundle(&tmp.path().join("art_alt"));
    nonzero_alt["audit"]["checkedAlternateProofs"] = json!(2);
    let nonzero_alt_path = tmp.path().join("nonzero_alt.json");
    fs::write(&nonzero_alt_path, serde_json::to_vec(&nonzero_alt).unwrap()).unwrap();
    let alt_out = run_inspect(&[nonzero_alt_path.to_str().unwrap()], None);
    assert_eq!(alt_out.status.code(), Some(0), "{}", String::from_utf8_lossy(&alt_out.stdout));
    let alt_diff = run_inspect(
        &[
            "--diff",
            clean_path.to_str().unwrap(),
            nonzero_alt_path.to_str().unwrap(),
            "--no-regressions",
            "--format",
            "json",
        ],
        None,
    );
    assert_eq!(alt_diff.status.code(), Some(0), "{}", String::from_utf8_lossy(&alt_diff.stdout));
    let alt_diff_json: Value = serde_json::from_slice(&alt_diff.stdout).unwrap();
    assert!(
        alt_diff_json["changes"]
            .as_array()
            .unwrap()
            .iter()
            .any(|c| { c["field"] == "audit.checkedAlternateProofs" && c["tier"] == "tier_c" }),
        "{alt_diff_json}"
    );

    // Envelope invariant violation: replayedDeclarations == 0 exits 1.
    let (mut zero_decls, ..) = sample_receipt_bundle(&tmp.path().join("art_zero_decls"));
    zero_decls["audit"]["replayedDeclarations"] = json!(0);
    let zero_decls_path = tmp.path().join("zero_decls.json");
    fs::write(&zero_decls_path, serde_json::to_vec(&zero_decls).unwrap()).unwrap();
    assert_eq!(run_inspect(&[zero_decls_path.to_str().unwrap()], None).status.code(), Some(1));

    // Multi-kernel replay policy fails closed on 0 passing kernels even under
    // bare default `--check`, and on blank/duplicate kernel names.
    let (mut empty_kernels, ..) = sample_receipt_bundle(&tmp.path().join("art_empty_k"));
    let empty_audit = empty_kernels["audit"].as_object_mut().unwrap();
    empty_audit.remove("auditMode");
    empty_audit.remove("kernelsSkipped");
    empty_audit.remove("paranoidQuorum");
    empty_audit.insert("kernelsPassed".into(), json!([]));
    let empty_k_path = tmp.path().join("empty_k.json");
    fs::write(&empty_k_path, serde_json::to_vec(&empty_kernels).unwrap()).unwrap();
    assert_eq!(run_inspect(&[empty_k_path.to_str().unwrap()], None).status.code(), Some(1));
    assert_eq!(
        run_inspect(&[empty_k_path.to_str().unwrap(), "--passive"], None).status.code(),
        Some(0)
    );
    assert_eq!(
        run_inspect(&[empty_k_path.to_str().unwrap(), "--require-kernel-replay", "1"], None)
            .status
            .code(),
        Some(1)
    );

    let (mut skipped_only, ..) = sample_receipt_bundle(&tmp.path().join("art_skip_k"));
    let skip_audit = skipped_only["audit"].as_object_mut().unwrap();
    skip_audit.remove("kernelsPassed");
    skip_audit.insert("auditMode".into(), json!("strict"));
    skip_audit.insert("kernelsSkipped".into(), json!(["lean4"]));
    let skip_k_path = tmp.path().join("skip_k.json");
    fs::write(&skip_k_path, serde_json::to_vec(&skipped_only).unwrap()).unwrap();
    assert_eq!(run_inspect(&[skip_k_path.to_str().unwrap()], None).status.code(), Some(1));
    assert_eq!(
        run_inspect(&[skip_k_path.to_str().unwrap(), "--passive"], None).status.code(),
        Some(0)
    );
    assert_eq!(
        run_inspect(&[skip_k_path.to_str().unwrap(), "--require-kernel-replay", "1"], None)
            .status
            .code(),
        Some(1)
    );

    // `embedding` must not license `general_hyper`.
    let (mut bad_emb, ..) = sample_receipt_bundle(&tmp.path().join("art_bad_emb"));
    bad_emb["model_system_relation"] = json!({
        "kind": "embedding",
        "direction": "bidirectional",
        "licensed_claim_shapes": ["general_hyper"]
    });
    let bad_emb_path = tmp.path().join("bad_emb.json");
    fs::write(&bad_emb_path, serde_json::to_vec(&bad_emb).unwrap()).unwrap();
    let bad_emb_out = run_inspect(&[bad_emb_path.to_str().unwrap(), "--passive"], None);
    assert_eq!(bad_emb_out.status.code(), Some(1));
    assert!(String::from_utf8_lossy(&bad_emb_out.stdout).contains("general_hyper"));

    let (mut blank_kernels, ..) = sample_receipt_bundle(&tmp.path().join("art_blank_k"));
    blank_kernels["audit"]["kernelsPassed"] = json!(["", " "]);
    let blank_k_path = tmp.path().join("blank_k.json");
    fs::write(&blank_k_path, serde_json::to_vec(&blank_kernels).unwrap()).unwrap();
    assert_eq!(
        run_inspect(&[blank_k_path.to_str().unwrap(), "--require-kernel-replay", "2"], None)
            .status
            .code(),
        Some(1)
    );
    assert_eq!(
        run_inspect(&[blank_k_path.to_str().unwrap(), "--passive"], None).status.code(),
        Some(1)
    );

    let (mut dup_kernels, ..) = sample_receipt_bundle(&tmp.path().join("art_dup_k"));
    dup_kernels["audit"]["kernelsPassed"] = json!(["lean4", " lean4 "]);
    let dup_k_path = tmp.path().join("dup_k.json");
    fs::write(&dup_k_path, serde_json::to_vec(&dup_kernels).unwrap()).unwrap();
    assert_eq!(
        run_inspect(&[dup_k_path.to_str().unwrap(), "--require-kernel-replay", "2"], None)
            .status
            .code(),
        Some(1)
    );
    assert_eq!(
        run_inspect(&[dup_k_path.to_str().unwrap(), "--require-kernel-replay", "1"], None)
            .status
            .code(),
        Some(0)
    );

    // Adversarial terminal/Bidi/Tag/GFM injection must be sanitized cleanly.
    let (mut evil, ..) = sample_receipt_bundle(&tmp.path().join("art_evil"));
    evil["audit"]["theorem"] = json!("bad\x1b[31m|`<x>\u{202E}\u{E0001}\u{0085}\r\n## FakeHeading");
    let evil_path = tmp.path().join("evil.json");
    fs::write(&evil_path, serde_json::to_vec(&evil).unwrap()).unwrap();
    for fmt in ["human", "ledger", "markdown"] {
        let out = run_inspect(&[evil_path.to_str().unwrap(), "--format", fmt, "--passive"], None);
        assert_eq!(out.status.code(), Some(0), "fmt={fmt}");
        let s = String::from_utf8(out.stdout).unwrap();
        assert!(!s.contains('\x1b'), "raw ESC in {fmt}");
        assert!(!s.contains('\r'), "raw CR in {fmt}");
        assert!(!s.contains('\u{202E}'), "raw RLO in {fmt}");
        assert!(!s.contains('\u{E0001}'), "raw TAG in {fmt}");
        assert!(!s.contains('\u{0085}'), "raw NEL in {fmt}");
        assert!(s.lines().all(|l| !l.trim_start().starts_with("## FakeHeading")));
    }

    // --output atomic write & --compare-ledger round-trip.
    let ledger_path = tmp.path().join("golden.ledger");
    let gen_ledger = run_inspect(
        &[
            clean_path.to_str().unwrap(),
            "--format",
            "ledger",
            "--output",
            ledger_path.to_str().unwrap(),
        ],
        None,
    );
    assert_eq!(gen_ledger.status.code(), Some(0));
    let match_ledger = run_inspect(
        &[clean_path.to_str().unwrap(), "--compare-ledger", ledger_path.to_str().unwrap()],
        None,
    );
    assert_eq!(match_ledger.status.code(), Some(0));
    fs::write(&ledger_path, b"stale=true\n").unwrap();
    let mismatch_ledger = run_inspect(
        &[clean_path.to_str().unwrap(), "--compare-ledger", ledger_path.to_str().unwrap()],
        None,
    );
    assert_eq!(mismatch_ledger.status.code(), Some(1));
}
