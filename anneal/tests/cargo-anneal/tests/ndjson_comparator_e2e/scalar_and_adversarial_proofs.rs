// Copyright 2026 The Fuchsia Authors
//
// Licensed under a BSD-style license <LICENSE-BSD>, Apache License, Version 2.0
// <LICENSE-APACHE or https://www.apache.org/licenses/LICENSE-2.0>, or the MIT
// license <LICENSE-MIT or https://opensource.org/licenses/MIT>, at your option.
// This file may not be copied, modified, or distributed except according to
// those terms.

//! Real `v4.35.0` comparator runs on the scalar target: the default dual
//! kernels, paranoid quorum, ill-typed exports, and adversarial proofs.

use super::*;

#[test]
fn scalar_ndjson_comparator_default_dual_kernels_and_paranoid_quorum() {
    let Some(lean) =
        require_or_skip_v435_lean("scalar_ndjson_comparator_default_dual_kernels_and_paranoid_quorum")
    else {
        return;
    };
    let tmp = TempDir::new().unwrap();
    let req = build_scalar_target_request(tmp.path(), SCALAR_SPEC, SCALAR_PROOF, false);

    // 1. Default run: 5a + 5b + 5c (`nanoda_bin` + `con-ron`), zero
    // `TrustedBoundary.lean` execution.
    let mut checker = new_v435_checker(&lean);
    let t0 = Instant::now();
    let report = checker.run_target(&req).expect("scalar NDJSON comparator must pass");
    let elapsed_ms = t0.elapsed().as_millis();
    eprintln!(
        "[real measurement] scalar full compile+audit: {elapsed_ms} ms | 5a+5b+5c breakdown: {}",
        report["timingMs"]
    );

    assert_eq!(report["auditMode"], json!("ndjson_comparator"));
    #[cfg(target_os = "linux")]
    assert_eq!(
        checker.active_sandbox(),
        Some(ActiveSandbox::LinuxBwrap),
        "must execute v4.35.0 NDJSON comparator under Tier-1 bwrap + seccomp"
    );
    assert_eq!(report["replay"], json!(true));
    assert_eq!(report["exactType"], json!(true));
    assert_eq!(report["pinnedPrimitivesCount"], json!(PINNED_INIT_PRIMITIVES.len()));
    assert_eq!(report["kernelsPassed"], json!(["nanoda_bin", "con-ron"]));
    assert_eq!(report["paranoidQuorum"], json!(false));
    assert!(report.get("kernelsSkipped").is_none());
    assert_eq!(report["sorryDeclarations"], json!([]));

    // `cargo anneal verify` accepts the audit metadata rather than failing
    // with `tool_failed`: the report carries the admitted import graph its
    // bundled-model trust-tier check requires. The scalar proof reaches the
    // `candidate:mir_ast` and `candidate:mir_semantics` model modules.
    assert_eq!(
        cargo_anneal::check_bundled_model_audit(&report),
        Ok(vec!["mir_ast", "mir_semantics"])
    );
    // Closures list only reached declarations: the imported but unreached
    // `Trusted.MirSemantics.CanaryFixtures` model module is in the graph but
    // in no closure, so `moduleIdentities` does not bind it either.
    const UNREACHED_MODEL: &str = "Trusted.MirSemantics.CanaryFixtures";
    assert!(report["graph"].get(UNREACHED_MODEL).is_some());
    for key in ["subjectClosure", "modelClosure", "specificationClosure"] {
        for entry in report[key].as_array().expect("closure array") {
            assert_ne!(entry["module"], json!(UNREACHED_MODEL), "{key}: {entry}");
        }
    }
    assert!(report["moduleIdentities"].get(UNREACHED_MODEL).is_none());
    for key in [
        "expectedToolchain",
        "observedVersion",
        "leanBinarySha256",
        "foundationModules",
        "sysrootModulesSha256",
        "admittedSysrootModuleCount",
    ] {
        assert!(report["unpinnedLean"].get(key).is_some(), "missing unpinnedLean.{key}");
    }

    // Verify export, primitive, and comparator binary SHA-256 digests are
    // 64-char hex strings.
    for key in [
        "expectedConeSha256",
        "proofNdjsonSha256",
        "initPrimitivesSha256",
        "sysrootPinsSha256",
        "leanexportSha256",
        "nanodaBinSha256",
        "conRonSha256",
    ] {
        let hex = report[key].as_str().expect("missing digest");
        assert!(cargo_anneal::is_sha256_hex(hex), "invalid digest for {key}: {hex}");
    }

    // Every sysroot-named constant either export uses is content-pinned to
    // the clean sysroot re-export (`5-pin`).
    assert!(
        report["sysrootPinnedDeclarations"].as_u64().is_some_and(|n| n > 0),
        "{}",
        report["sysrootPinnedDeclarations"]
    );

    // 2. Unfolded canonical theorem type
    // (`UnitTheorem ⟨Captured.program, Spec.specs⟩`, without importing
    // `Expected`, matching `spin/Proof.lean`).
    let unfolded_proof = SCALAR_PROOF.replace(
        "theorem verify : Expected.claim := by",
        "theorem verify : UnitTheorem ⟨Captured.program, Spec.specs⟩ := by",
    );
    let tmp_unfolded = TempDir::new().unwrap();
    let req_unfolded =
        build_scalar_target_request(tmp_unfolded.path(), SCALAR_SPEC, &unfolded_proof, false);
    let rep_unfolded = checker
        .run_target(&req_unfolded)
        .expect("unfolded canonical theorem type must pass");
    assert_eq!(rep_unfolded["auditMode"], json!("ndjson_comparator"));
    assert_eq!(rep_unfolded["kernelsPassed"], json!(["nanoda_bin", "con-ron"]));

    // 3. Optional `--paranoid-quorum` runs all four independent non-Replay
    // bundled Lean v4.35.0 NDJSON kernels (`nanoda_bin`, `con-ron`,
    // `con-leche`, `lean4lean`) directly inside `ExecSeal`.
    checker.set_paranoid_quorum(true);
    let t_paranoid = Instant::now();
    let rep_paranoid = checker
        .run_target(&req)
        .expect("scalar --paranoid-quorum must pass");
    eprintln!(
        "[real measurement] scalar --paranoid-quorum (4 kernels) full: {} ms | breakdown: {}",
        t_paranoid.elapsed().as_millis(),
        rep_paranoid["timingMs"]
    );
    for key in ["conLecheSha256", "lean4leanSha256"] {
        let hex = rep_paranoid[key].as_str().expect("missing quorum kernel digest");
        assert!(cargo_anneal::is_sha256_hex(hex), "invalid digest for {key}: {hex}");
    }
    assert_eq!(rep_paranoid["paranoidQuorum"], json!(true));
    assert_eq!(
        rep_paranoid["kernelsPassed"],
        json!(["nanoda_bin", "con-ron", "con-leche", "lean4lean"])
    );
    assert!(rep_paranoid.get("kernelsSkipped").is_none());
}

/// Rewrite `proof_full.ndjson` so `theorem_name`'s value is its own type: the
/// export stays structurally valid (every referenced name and expression
/// exists, and the declaration's type and dependencies are unchanged), but
/// the theorem is ill-typed, so only a type-checking kernel can reject it.
fn ill_typed_theorem_export(ndjson: &str, theorem_name: &str) -> String {
    let mut names: std::collections::HashMap<u64, String> =
        std::collections::HashMap::from([(0, String::new())]);
    let mut lines: Vec<Value> =
        ndjson.lines().map(|l| serde_json::from_str(l).expect("ndjson line")).collect();
    for v in &lines {
        let Some(id) = v["in"].as_u64() else { continue };
        // Numeric components (`"num"`) only occur in names the target
        // theorem's own name does not use; any name under one stays unnamed.
        let (Some(s), Some(pre)) =
            (v.get("str"), v["str"]["pre"].as_u64().and_then(|p| names.get(&p)))
        else {
            continue;
        };
        let seg = s["str"].as_str().unwrap();
        let full = if pre.is_empty() { seg.to_owned() } else { format!("{pre}.{seg}") };
        names.insert(id, full);
    }
    let name_id =
        names.iter().find(|(_, n)| n.as_str() == theorem_name).map(|(id, _)| *id).unwrap();
    let mut rewritten = 0;
    for v in &mut lines {
        if let Some(thm) = v.get_mut("thm").filter(|t| t["name"].as_u64() == Some(name_id)) {
            assert_ne!(thm["value"], thm["type"]);
            thm["value"] = thm["type"].clone();
            rewritten += 1;
        }
    }
    assert_eq!(rewritten, 1, "{theorem_name} theorem record");
    lines.iter().map(|v| format!("{v}\n")).collect()
}

/// Every kernel the comparator route relies on (`nanoda_bin` and `con-ron`
/// by default, plus `con-leche` and `lean4lean` under `--paranoid-quorum`)
/// rejects an ill-typed export in its configured invocation and accepts the
/// well-typed export it came from, so no kernel can be a no-op.
#[test]
fn ndjson_kernels_reject_ill_typed_proof_export() {
    let Some(lean) = require_or_skip_v435_lean("ndjson_kernels_reject_ill_typed_proof_export")
    else {
        return;
    };
    let tmp = TempDir::new().unwrap();
    let req = build_scalar_target_request(tmp.path(), SCALAR_SPEC, SCALAR_PROOF, false);
    let mut checker = new_v435_checker(&lean);
    checker.set_paranoid_quorum(true);
    checker.run_target(&req).expect("scalar NDJSON comparator must pass");
    let exported = fs::read_to_string(checker.stage().join("ndjson/proof_full.ndjson")).unwrap();

    let kernels = ["nanoda_bin", "con-ron", "con-leche", "lean4lean"];
    let good = tmp.path().join("good.ndjson");
    fs::write(&good, &exported).unwrap();
    let verdicts = checker.run_ndjson_kernels(&good).unwrap();
    assert_eq!(verdicts.iter().map(|(k, _)| *k).collect::<Vec<_>>(), kernels);
    for (kernel, verdict) in &verdicts {
        assert!(verdict.is_ok(), "{kernel} must accept the well-typed export: {verdict:?}");
    }

    let bad = tmp.path().join("bad.ndjson");
    fs::write(&bad, ill_typed_theorem_export(&exported, "Proof.verify")).unwrap();
    let verdicts = checker.run_ndjson_kernels(&bad).unwrap();
    assert_eq!(verdicts.iter().map(|(k, _)| *k).collect::<Vec<_>>(), kernels);
    // `nanoda_bin`, `con-ron`, and `con-leche` report the failed definitional
    // equality check; `lean4lean` currently fails while reporting the error,
    // which the kernel runner's panic-marker check turns into a rejection.
    for (kernel, verdict) in verdicts {
        let err = verdict.expect_err(kernel);
        eprintln!("{kernel} rejected the ill-typed export: {err}");
        let reason = match kernel {
            "nanoda_bin" => "def_eq",
            "con-ron" | "con-leche" => "type mismatch in theorem",
            _ => continue,
        };
        assert_eq!(err.code, 1, "{kernel}: {err}");
        assert!(err.message.contains(reason), "{kernel}: {err}");
    }
}

#[test]
fn scalar_ndjson_comparator_rejects_adversarial_proofs() {
    let Some(lean) = require_or_skip_v435_lean("scalar_ndjson_comparator_rejects_adversarial_proofs")
    else {
        return;
    };
    let mut checker = new_v435_checker(&lean);

    // 1. Wrong theorem statement (`theorem verify : True := True.intro`).
    {
        let tmp = TempDir::new().unwrap();
        let bad_proof = "prelude\nimport Expected\nnamespace Proof\ntheorem verify : True := True.intro\nend Proof\n";
        let req = build_scalar_target_request(tmp.path(), SCALAR_SPEC, bad_proof, false);
        let err = checker.run_target(&req).unwrap_err();
        assert_eq!(err.code, 1, "wrong theorem statement must fail with policy code 1: {err}");
    }

    // 2. Unpermitted custom axiom in `Proof.lean`.
    {
        let tmp = TempDir::new().unwrap();
        let bad_proof = "prelude\nimport Expected\nnamespace Proof\naxiom cheat : Expected.claim\ntheorem verify : Expected.claim := cheat\nend Proof\n";
        let req = build_scalar_target_request(tmp.path(), SCALAR_SPEC, bad_proof, false);
        let err = checker.run_target(&req).unwrap_err();
        assert_eq!(err.code, 1, "custom axiom must fail with policy code 1: {err}");
        assert!(err.message.contains("Proof.cheat"), "{err}");
    }

    // 3. Constructive `opaque` stub in `Proof.lean` (closed `.opaqueInfo` ban).
    {
        let tmp = TempDir::new().unwrap();
        let bad_proof = SCALAR_PROOF.replace(
            "public theorem verify : Expected.claim := by",
            "opaque stubNat : Nat := 0\ntheorem useStub : stubNat = stubNat := rfl\npublic theorem verify : Expected.claim := by\n  have _ := useStub",
        );
        let req = build_scalar_target_request(tmp.path(), SCALAR_SPEC, &bad_proof, false);
        let err = checker.run_target(&req).unwrap_err();
        assert_eq!(err.code, 1, "opaque stub must fail with policy code 1: {err}");
        assert!(err.message.contains("opaque"), "{err}");
    }

    // 4. `partial def` in `Proof.lean` (exported as opaque/partial and rejected
    // by the closed `.opaqueInfo` / `partial` ban).
    {
        let tmp = TempDir::new().unwrap();
        let bad_proof = SCALAR_PROOF.replace(
            "public theorem verify : Expected.claim := by",
            "partial def loopNat (n : Nat) : Nat := loopNat (n + 1)\ntheorem usePartial : loopNat 0 = loopNat 0 := rfl\npublic theorem verify : Expected.claim := by\n  have _ := usePartial",
        );
        let req = build_scalar_target_request(tmp.path(), SCALAR_SPEC, &bad_proof, false);
        let err = checker.run_target(&req).unwrap_err();
        assert_eq!(err.code, 1, "partial def must fail with policy code 1: {err}");
        assert!(
            err.message.contains("opaque") || err.message.contains("partial"),
            "{err}"
        );
    }

    // 5. `sorryAx` rejected by default, admitted only when
    // `allow_sorry_in_proof = true` (reporting `sorryDeclarations` and honest
    // `con-ron` skip).
    {
        let tmp = TempDir::new().unwrap();
        let sorry_proof = "prelude\nimport Expected\nnamespace Proof\ntheorem verify : Expected.claim := sorry\nend Proof\n";
        let req_strict = build_scalar_target_request(tmp.path(), SCALAR_SPEC, sorry_proof, false);
        let err = checker.run_target(&req_strict).unwrap_err();
        assert_eq!(err.code, 1, "sorry must be rejected when allow_sorry_in_proof=false: {err}");
        assert!(err.message.contains("sorryAx"), "{err}");

        let req_tainted = build_scalar_target_request(tmp.path(), SCALAR_SPEC, sorry_proof, true);
        let rep = checker
            .run_target(&req_tainted)
            .expect("sorry must pass when allow_sorry_in_proof=true");
        assert_eq!(rep["auditMode"], json!("ndjson_comparator"));
        assert_eq!(rep["sorryDeclarations"], json!(["Proof.verify"]));
        assert_eq!(rep["kernelsPassed"], json!(["nanoda_bin"]));
        assert_eq!(
            rep["kernelsSkipped"],
            json!([{"kernel": "con-ron", "reason": "sorryAx_present_under_allow_sorry_in_proof"}])
        );
    }

    // 6. A proof-module constant beneath `Trusted` fails closed even though
    // the umbrella `Trusted` module is a retained model module.
    {
        let tmp = TempDir::new().unwrap();
        let bad_proof = SCALAR_PROOF.replace(
            "public theorem verify : Expected.claim := by",
            "def _root_.Trusted.MirSemantics.evil : Nat := 0\ntheorem useEvil : Trusted.MirSemantics.evil = 0 := rfl\npublic theorem verify : Expected.claim := by\n  have _ := useEvil",
        );
        let req = build_scalar_target_request(tmp.path(), SCALAR_SPEC, &bad_proof, false);
        assert!(req.modules.iter().any(|m| m.module == "Trusted" && m.role == TargetRole::Model));
        let err = checker.run_target(&req).unwrap_err();
        assert_eq!(err.code, 1, "Trusted.* in Proof must fail with policy code 1: {err}");
        assert_eq!(err.phase, "ndjson-comparator", "{err}");
        assert!(
            err.message.contains("Trusted.MirSemantics.evil")
                && err.message.contains("outside model modules"),
            "{err}"
        );
    }
}
