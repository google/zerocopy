// Copyright 2026 The Fuchsia Authors
//
// Licensed under a BSD-style license <LICENSE-BSD>, Apache License, Version 2.0
// <LICENSE-APACHE or https://www.apache.org/licenses/LICENSE-2.0>, or the MIT
// license <LICENSE-MIT or https://opensource.org/licenses/MIT>, at your option.
// This file may not be copied, modified, or distributed except according to
// those terms.

//! Synthetic `nanoda_bin` and `con-ron` stubs that exercise the full NDJSON
//! comparator pipeline without a `v4.35.0` install (Unix only).

use super::*;
use std::process::Command;

#[path = "synthetic_comparator/harness.rs"]
mod harness;
#[path = "synthetic_comparator/stubs.rs"]
mod stubs;

use harness::*;
use stubs::*;

#[test]
fn synthetic_ndjson_comparator_runs_full_target_audit_pipeline_without_v435_install() {
    let (harness, res) =
        run_synthetic_ndjson_pipeline(StubBehavior::Accept, StubBehavior::Accept);
    let report = res.expect("synthetic NDJSON comparator run_target must succeed");
    assert_eq!(report["auditMode"], json!("ndjson_comparator"));
    assert_eq!(report["replay"], json!(true));
    assert_eq!(report["kernelsPassed"], json!(["nanoda_bin", "con-ron"]));
    for key in ["leanexportSha256", "nanodaBinSha256", "conRonSha256"] {
        assert!(cargo_anneal::is_sha256_hex(report[key].as_str().unwrap()));
    }

    // The report carries the admitted import graph, and each closure lists
    // exactly the declarations it reaches, attributed to their modules, so
    // the unreached `Trusted.Unused` model module appears in no closure and
    // receives no `moduleIdentities` entry.
    let graph = report["graph"].as_object().expect("audit.graph must be an object");
    for module in [
        "Trusted.MirSemantics",
        "Trusted.Unused",
        "Captured",
        "Spec",
        "Expected",
        "Init.Prelude",
        "Init.Core",
    ] {
        assert!(graph.contains_key(module), "audit.graph lacks {module}: {graph:?}");
    }
    let closure = |key: &str| -> Vec<(String, String)> {
        report[key]
            .as_array()
            .unwrap_or_else(|| panic!("missing {key}"))
            .iter()
            .map(|e| {
                (
                    e["name"].as_str().unwrap().to_owned(),
                    e["module"].as_str().unwrap().to_owned(),
                )
            })
            .collect()
    };
    let model = closure("modelClosure");
    assert!(model.contains(&(
        "Trusted.MirSemantics.UnitTheorem".to_owned(),
        "Trusted.MirSemantics".to_owned()
    )));
    assert!(model.iter().all(|(_, m)| m == "Trusted.MirSemantics" || m.starts_with("Init.")));
    assert!(
        closure("subjectClosure")
            .contains(&("Captured.program".to_owned(), "Captured".to_owned()))
    );
    assert!(
        closure("specificationClosure")
            .contains(&("Spec.specs".to_owned(), "Spec".to_owned()))
    );
    for key in ["subjectClosure", "modelClosure", "specificationClosure"] {
        assert!(
            closure(key)
                .iter()
                .all(|(n, m)| n != m && m != "Trusted.Unused" && graph.contains_key(m)),
            "{key}"
        );
    }
    let identities = report["moduleIdentities"].as_object().expect("moduleIdentities");
    assert!(identities.contains_key("Trusted.MirSemantics"), "{identities:?}");
    assert!(!identities.contains_key("Trusted.Unused"), "{identities:?}");

    // Confirm both inspecting kernel stubs actually ran in order and
    // validated exact CLI flags, config JSON, and NDJSON declarations.
    let calls = harness.invocations();
    let tools: Vec<&str> = calls.iter().map(|c| c["tool"].as_str().unwrap()).collect();
    assert_eq!(tools, vec!["nanoda_bin", "con-ron"]);
    assert_eq!(calls[0]["config"]["unpermitted_axiom_hard_error"], json!(true));
    assert_eq!(calls[0]["config"]["nat_extension"], json!(true));
    assert_eq!(calls[0]["config"]["string_extension"], json!(true));
    assert_eq!(calls[1]["argv"][0], json!("--verified"));
    assert!(calls[0]["stats"]["decl_count"].as_u64().is_some_and(|n| n >= 6));
    assert!(calls[1]["stats"]["decl_count"].as_u64().is_some_and(|n| n >= 6));
}

/// The comparator route fails closed whenever either required kernel
/// rejects the export, by a nonzero exit or by a Lean panic marker on
/// stderr despite exit code 0, without a `v4.35.0` install.
#[test]
fn synthetic_ndjson_comparator_fails_closed_when_a_stub_kernel_rejects() {
    let rejecting = StubBehavior::Fail { exit_code: 1, diagnostic: "type mismatch" };
    let panicking = StubBehavior::PanicAtExitZero { diagnostic: "PANIC at Lean.Kernel" };
    for (label, nanoda_bin, con_ron, code, needle) in [
        (
            "nanoda_bin exit 1",
            rejecting,
            StubBehavior::Accept,
            1,
            "nanoda_bin rejected proof export",
        ),
        (
            "con-ron exit 1",
            StubBehavior::Accept,
            rejecting,
            1,
            "con-ron rejected proof export",
        ),
        ("nanoda_bin panic", panicking, StubBehavior::Accept, 2, "Lean runtime panic marker"),
        ("con-ron panic", StubBehavior::Accept, panicking, 2, "Lean runtime panic marker"),
    ] {
        let (harness, res) = run_synthetic_ndjson_pipeline(nanoda_bin, con_ron);
        let err = res.expect_err(label);
        assert_eq!(err.code, code, "{label}: {err}");
        assert!(err.message.contains(needle), "{label}: {err}");
        let (phase, expected_tools): (&str, &[&str]) = if nanoda_bin == StubBehavior::Accept {
            ("con-ron", &["nanoda_bin", "con-ron"])
        } else {
            ("nanoda", &["nanoda_bin"])
        };
        assert!(err.phase.contains(phase), "{label}: {err}");
        let calls = harness.invocations();
        let tools: Vec<&str> = calls.iter().map(|c| c["tool"].as_str().unwrap()).collect();
        assert_eq!(tools, expected_tools, "{label}");
    }
}

#[test]
fn synthetic_ndjson_comparator_rejects_nanoda_nonzero_exit() {
    let (harness, res) = run_synthetic_ndjson_pipeline(
        StubBehavior::Fail {
            exit_code: 1,
            diagnostic: "injected nanoda_bin kernel rejection",
        },
        StubBehavior::Accept,
    );
    let err = res.unwrap_err();
    assert_eq!(err.code, 1, "nanoda_bin failure must fail with policy code 1: {err}");
    assert_eq!(err.phase, "ndjson-nanoda", "{err}");
    assert!(err.message.contains("injected nanoda_bin kernel rejection"), "{err}");

    // Must fail closed before invoking `con-ron`.
    let calls = harness.invocations();
    let tools: Vec<&str> = calls.iter().map(|c| c["tool"].as_str().unwrap()).collect();
    assert_eq!(tools, vec!["nanoda_bin"]);
}

#[test]
fn synthetic_ndjson_comparator_rejects_con_ron_nonzero_exit() {
    let (harness, res) = run_synthetic_ndjson_pipeline(
        StubBehavior::Accept,
        StubBehavior::Fail { exit_code: 1, diagnostic: "injected con-ron kernel rejection" },
    );
    let err = res.unwrap_err();
    assert_eq!(err.code, 1, "con-ron failure must fail with policy code 1: {err}");
    assert_eq!(err.phase, "ndjson-con-ron", "{err}");
    assert!(err.message.contains("injected con-ron kernel rejection"), "{err}");

    let calls = harness.invocations();
    let tools: Vec<&str> = calls.iter().map(|c| c["tool"].as_str().unwrap()).collect();
    assert_eq!(tools, vec!["nanoda_bin", "con-ron"]);
}

#[test]
fn synthetic_ndjson_comparator_rejects_tampered_expected_claim() {
    // 1. Tampering `Expected.claim` in the untrusted proof export diverges
    // from trusted `expected_cone.ndjson`.
    let proof_tamper = SyntheticComparatorHarness::new(SyntheticHarnessConfig {
        tamper_expected_claim_in_proof: true,
        ..Default::default()
    });
    let mut checker = proof_tamper.checker();
    let err = checker.run_target(&proof_tamper.request).unwrap_err();
    assert_eq!(err.code, 1, "proof-side Expected.claim tamper must fail with code 1: {err}");
    assert_eq!(err.phase, "ndjson-comparator", "{err}");
    assert!(
        err.message.contains("Expected.claim")
            && err.message.contains("differs between trusted expected export and proof export"),
        "{err}"
    );
    assert!(proof_tamper.invocations().is_empty());

    // 2. Tampering `Expected.claim` identically in BOTH exports still fails
    // canonical claim-body verification.
    let both_tamper = SyntheticComparatorHarness::new(SyntheticHarnessConfig {
        tamper_expected_claim_in_expected: true,
        tamper_expected_claim_in_proof: true,
        ..Default::default()
    });
    let mut checker = both_tamper.checker();
    let err = checker.run_target(&both_tamper.request).unwrap_err();
    assert_eq!(err.code, 1, "canonical Expected.claim tamper must fail with code 1: {err}");
    assert_eq!(err.phase, "ndjson-comparator", "{err}");
    assert!(
        err.message.contains("Expected.claim")
            && err.message.contains("differs from canonical root application"),
        "{err}"
    );
    assert!(both_tamper.invocations().is_empty());
}

#[test]
fn synthetic_ndjson_comparator_rejects_missing_init_primitive_and_custom_axiom() {
    // 1. Missing pinned `Init` primitive (`Nat.gcd`) fails closed.
    let missing_prim = SyntheticComparatorHarness::new(SyntheticHarnessConfig {
        omit_init_primitive: Some("Nat.gcd"),
        ..Default::default()
    });
    let mut checker = missing_prim.checker();
    let err = checker.run_target(&missing_prim.request).unwrap_err();
    assert_eq!(err.code, 2, "missing Init primitive must fail with operational code 2: {err}");
    assert_eq!(err.phase, "ndjson-comparator", "{err}");
    assert!(err.message.contains("Nat.gcd"), "{err}");
    assert!(missing_prim.invocations().is_empty());

    // 2. Unexpected custom axiom (`Proof.cheat`) in exported NDJSON fails
    // closed with policy code 1.
    let custom_ax = SyntheticComparatorHarness::new(SyntheticHarnessConfig {
        inject_custom_axiom_in_proof: Some("cheat"),
        ..Default::default()
    });
    let mut checker = custom_ax.checker();
    let err = checker.run_target(&custom_ax.request).unwrap_err();
    assert_eq!(err.code, 1, "custom axiom must fail with policy code 1: {err}");
    assert_eq!(err.phase, "ndjson-comparator", "{err}");
    assert!(
        err.message.contains("unpermitted axiom `Proof.cheat` in proof export"),
        "{err}"
    );
    assert!(custom_ax.invocations().is_empty());
}

#[test]
fn synthetic_inspecting_stubs_reject_malformed_cli_and_ndjson_directly() {
    let harness = SyntheticComparatorHarness::new(SyntheticHarnessConfig::default());
    let scratch = harness.tmp.path().join("direct_stub_cases");
    fs::create_dir_all(&scratch).unwrap();
    let valid_proof = harness.fixtures_dir.join("proof.ndjson");
    let staged_valid = scratch.join("proof_full.ndjson");
    fs::copy(&valid_proof, &staged_valid).unwrap();

    let write_nanoda_cfg = |name: &str, ndjson: &Path, hard_err: bool| -> PathBuf {
        let dir = scratch.join(name);
        fs::create_dir_all(&dir).unwrap();
        let cfg_path = dir.join("nanoda_config.json");
        let cfg = json!({
            "use_stdin": false,
            "export_file_path": ndjson.to_string_lossy(),
            "permitted_axioms": STANDARD_PERMITTED_AXIOMS,
            "unpermitted_axiom_hard_error": hard_err,
            "num_threads": 2,
            "nat_extension": true,
            "string_extension": true,
        });
        fs::write(&cfg_path, serde_json::to_vec(&cfg).unwrap()).unwrap();
        cfg_path
    };

    // 1. `nanoda_bin` rejects weakened config
    // (`unpermitted_axiom_hard_error: false`).
    let weak_cfg = write_nanoda_cfg("weak_cfg", &staged_valid, false);
    let out = Command::new(&harness.nanoda_bin).arg(&weak_cfg).output().unwrap();
    assert!(!out.status.success(), "nanoda_bin stub must reject hard_error=false");
    assert!(
        String::from_utf8_lossy(&out.stderr).contains("unpermitted_axiom_hard_error"),
        "{}",
        String::from_utf8_lossy(&out.stderr)
    );

    // 2. `con-ron` rejects wrong flag where `--verified` is required.
    let out = Command::new(&harness.con_ron_bin)
        .args(["--unverified", "--jobs=2", staged_valid.to_str().unwrap()])
        .output()
        .unwrap();
    assert!(!out.status.success(), "con-ron stub must reject --unverified");
    let stderr = String::from_utf8_lossy(&out.stderr);
    assert!(stderr.contains("must be --verified"), "{stderr}");

    // 3. Both stubs reject tampered `Expected.claim`, custom axioms,
    // forbidden markers, and malformed JSON.
    let tampered_dir = scratch.join("tampered");
    fs::create_dir_all(&tampered_dir).unwrap();
    let tampered_ndjson = tampered_dir.join("proof_full.ndjson");
    fs::write(&tampered_ndjson, build_proof_ndjson(true, None)).unwrap();

    let axiom_dir = scratch.join("custom_axiom");
    fs::create_dir_all(&axiom_dir).unwrap();
    let axiom_ndjson = axiom_dir.join("proof_full.ndjson");
    fs::write(&axiom_ndjson, build_proof_ndjson(false, Some("cheat"))).unwrap();

    let marker_dir = scratch.join("forbidden_marker");
    fs::create_dir_all(&marker_dir).unwrap();
    let marker_ndjson = marker_dir.join("proof_full.ndjson");
    let mut with_marker = build_proof_ndjson(false, None);
    with_marker.push_str(r#"{"in":99,"str":{"pre":0,"str":"ANNEAL_FORBIDDEN_MARKER"}}"#);
    with_marker.push('\n');
    fs::write(&marker_ndjson, with_marker).unwrap();

    let malformed_dir = scratch.join("malformed");
    fs::create_dir_all(&malformed_dir).unwrap();
    let malformed_ndjson = malformed_dir.join("proof_full.ndjson");
    fs::write(&malformed_ndjson, format!("{SYNTHETIC_META}\n{{not-json\n")).unwrap();

    for (label, bad_ndjson, expected_substr) in [
        ("tampered-claim", &tampered_ndjson, "tampered Expected.claim"),
        ("custom-axiom", &axiom_ndjson, "unpermitted axiom Proof.cheat"),
        ("forbidden-marker", &marker_ndjson, "ANNEAL_FORBIDDEN_MARKER"),
        ("malformed-json", &malformed_ndjson, "invalid JSON"),
    ] {
        let cfg = write_nanoda_cfg(label, bad_ndjson, true);
        let nanoda_out = Command::new(&harness.nanoda_bin).arg(&cfg).output().unwrap();
        assert!(
            !nanoda_out.status.success(),
            "nanoda_bin stub must reject {label}"
        );
        let nanoda_err = String::from_utf8_lossy(&nanoda_out.stderr);
        assert!(
            nanoda_err.contains(expected_substr),
            "nanoda_bin {label}: expected `{expected_substr}` in `{nanoda_err}`"
        );

        let con_ron_out = Command::new(&harness.con_ron_bin)
            .args(["--verified", "--jobs=2", bad_ndjson.to_str().unwrap()])
            .output()
            .unwrap();
        assert!(
            !con_ron_out.status.success(),
            "con-ron stub must reject {label}"
        );
        let con_ron_err = String::from_utf8_lossy(&con_ron_out.stderr);
        assert!(
            con_ron_err.contains(expected_substr),
            "con-ron {label}: expected `{expected_substr}` in `{con_ron_err}`"
        );
    }

    // 4. Fault-injection env vars work on direct stub invocations.
    let valid_cfg = write_nanoda_cfg("valid_fault_inject", &staged_valid, true);
    let out = Command::new(&harness.nanoda_bin)
        .arg(&valid_cfg)
        .env("ANNEAL_STUB_NANODA_EXIT", "1")
        .output()
        .unwrap();
    assert_eq!(out.status.code(), Some(1));

    let out = Command::new(&harness.con_ron_bin)
        .args(["--verified", "--jobs=2", staged_valid.to_str().unwrap()])
        .env("ANNEAL_STUB_CON_RON_EXIT", "1")
        .output()
        .unwrap();
    assert_eq!(out.status.code(), Some(1));
}
