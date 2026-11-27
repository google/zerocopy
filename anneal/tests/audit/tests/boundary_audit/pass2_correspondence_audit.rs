// Copyright 2026 The Fuchsia Authors
//
// Licensed under a BSD-style license <LICENSE-BSD>, Apache License, Version 2.0
// <LICENSE-APACHE or https://www.apache.org/licenses/LICENSE-2.0>, or the MIT
// license <LICENSE-MIT or https://opensource.org/licenses/MIT>, at your option.
// This file may not be copied, modified, or distributed except according to
// those terms.

//! Correspondence non-backsliding and correspondence audit violations.

use super::*;

/// Verifies Pass 2 non-backsliding enforcement (`--require-correspondence`):
/// missing correspondence directories, `verifyCorrespondenceClaims` across all
/// 38 required claims (including `CorrespondenceAtChoicesClaim`,
/// `FaultEquivalenceAtChoicesClaim`, `OperandMachine.evalOperand` wiring,
/// `RefStepSoundForAllowedStepClaim`, `BytesCodecMatchesMiriClaim`, and the
/// `D14`–`D17` `char`/`cmp`, cast, overflow, and call canaries), and
/// `verifyRefEvaluatorIndependence`
/// (all 39 required live `ExecutionMachine` Miri primitives on
/// `[evalRefStep, initRefState]` unmasked by `RefAllowedStep`,
/// `ExecutionMachine.AllowedStep` on `RefAllowedStep`, module-level import
/// isolation and modular placement checks on isolated
/// `Trusted.Correspondence.*` evaluator submodules, and rejection of
/// disallowed `Trusted` declarations).
#[test]
fn enforces_correspondence_non_backsliding() {
    // 1. When `require_correspondence` is enabled and correspondence
    // directories are absent, `Checker::run` rejects in `"correspondence"`.
    let fix_missing_corr = TempFixture::new(None);
    let mut checker = fix_missing_corr.checker();
    checker.set_require_mir_wp(false);
    checker.set_require_correspondence(true);
    assert_policy_rejection(
        checker.run(),
        "correspondence",
        "missing required correspondence directories",
    );

    // 2. Pass 2 (`InspectorRequest::CorrespondenceAudit`) enforces
    // `verifyCorrespondenceClaims` (required constant references across all 38
    // claims and exact claim-type proof checking) and
    // `verifyRefEvaluatorIndependence` (39 live `ExecutionMachine` Miri
    // primitives on `[evalRefStep, initRefState]` without `RefAllowedStep`
    // masking, `AllowedStep` on `RefAllowedStep`, fail-closed module-level
    // import isolation and modular placement checks on isolated
    // `Trusted.Correspondence.*` evaluator submodules, and closed
    // module-origin isolation across both cones).
    let mut harness = CorrespondenceHarness::new();

    // 2a. Weakened `CorrespondenceClaim` (drops `WellFormed`).
    harness.compile_trusted(
        &[],
        "Trusted.Correspondence",
        "prelude\nimport Init.Core\n\
         namespace Trusted.Correspondence\n\
         def CorrespondenceClaim : Prop := True\n\
         end Trusted.Correspondence\n",
    );
    harness.compile_corr_proof(
        &["Trusted.Correspondence"],
        "Anneal.MirCorrespondenceProof",
        "prelude\nimport Trusted.Correspondence\n\
         namespace Anneal.MirCorrespondenceProof\n\
         theorem correspondence_claim_holds : Trusted.Correspondence.CorrespondenceClaim := True.intro\n\
         end Anneal.MirCorrespondenceProof\n",
    );
    harness.assert_default_rejected(
        "claim Trusted.Correspondence.CorrespondenceClaim body must reference Trusted.MirSemantics.WellFormed",
    );

    // 2a-ii. Weakened choices, wiring, canary, and codec claims fail closed.
    let valid_claims_text = ClaimsSpec::valid().render();
    let valid_proofs = ProofsSpec::valid();
    let claim_weakenings: Vec<(ClaimsSpec, ProofsSpec, &str)> = vec![
        (
            ClaimsSpec { corr_choices: Some("True".to_string()), ..ClaimsSpec::valid() },
            ProofsSpec { corr_choices: "True.intro".to_string(), ..valid_proofs.clone() },
            "claim Trusted.Correspondence.CorrespondenceAtChoicesClaim body must reference Trusted.MirSemantics.WellFormed",
        ),
        (
            ClaimsSpec { fault_choices: Some("True".to_string()), ..ClaimsSpec::valid() },
            ProofsSpec { fault_choices: "True.intro".to_string(), ..valid_proofs.clone() },
            "claim Trusted.Correspondence.FaultEquivalenceAtChoicesClaim body must reference Trusted.MirSemantics.ReachesResultAtChoices",
        ),
        (
            ClaimsSpec {
                wiring: Some(
                    "Miri.Interpreter.ExecutionMachine.step = Miri.Interpreter.ExecutionMachine.stepHooks ∧\n\
                     Miri.Interpreter.Step.step = Miri.Interpreter.ExecutionMachine.withValidation ∧\n\
                     Miri.Interpreter.ExecutionMachine.operandHooks = Miri.Interpreter.evalOperand ∧\n\
                     Miri.Interpreter.MachineHooks.takeLastPendingMoveDeinit = Miri.Interpreter.MachineHooks.recordPendingMoveDeinit ∧\n\
                     Miri.Interpreter.FnArg.copyFnArg = Miri.Interpreter.Call.deinitInPlaceArg"
                        .to_string(),
                ),
                ..ClaimsSpec::valid()
            },
            ProofsSpec {
                wiring: "⟨Eq.refl _, Eq.refl _, Eq.refl _, Eq.refl _, Eq.refl _⟩".to_string(),
                ..valid_proofs.clone()
            },
            "claim Trusted.Correspondence.MiriMoveDeinitWiringClaim body must reference Miri.Interpreter.OperandMachine.evalOperand",
        ),
        (
            ClaimsSpec { d6: Some("True".to_string()), ..ClaimsSpec::valid() },
            ProofsSpec { d6: "True.intro".to_string(), ..valid_proofs.clone() },
            "claim Trusted.Correspondence.CanaryD6UseAfterMoveUbClaim body must reference Trusted.Correspondence.progUseAfterMoveD6",
        ),
        (
            ClaimsSpec { ref_step_allowed: Some("True".to_string()), ..ClaimsSpec::valid() },
            ProofsSpec { ref_step_allowed: "True.intro".to_string(), ..valid_proofs.clone() },
            "claim Trusted.Correspondence.RefStepSoundForAllowedStepClaim body must reference Trusted.Correspondence.RefStep",
        ),
        (
            ClaimsSpec::valid().with_replace(
                VALID_BYTES_CODEC_DEF,
                "def BytesCodecMatchesMiriClaim : Prop :=\n\
                 Miri.Memory.Allocation.writeScalar = Miri.Memory.Allocation.readScalar\n",
            ),
            ProofsSpec { bytes_codec: "Eq.refl _".to_string(), ..valid_proofs.clone() },
            "claim Trusted.Correspondence.BytesCodecMatchesMiriClaim body must reference Trusted.MirSemantics.encodeVal",
        ),
    ];
    for (claims, proofs, expected) in claim_weakenings {
        harness.publish(&claims, &proofs);
        harness.assert_default_rejected(expected);
    }

    // Weakening D11–D13 canary claims by dropping required fixtures/predicates.
    for (claim, valid_def, old_tok, replacement_tok, dropped) in [
        (
            "CanaryD11EnumDiscriminantAndConstOkClaim",
            VALID_D11_DEF,
            "Trusted.MirSemantics.progEnumExplicitReprU8",
            "Trusted.MirSemantics.progEnumSignedTagIsize",
            "Trusted.MirSemantics.progEnumExplicitReprU8",
        ),
        (
            "CanaryD11EnumDiscriminantAndConstOkClaim",
            VALID_D11_DEF,
            "Trusted.MirSemantics.progEnumSignedTagIsize",
            "Trusted.MirSemantics.progEnumExplicitReprU8",
            "Trusted.MirSemantics.progEnumSignedTagIsize",
        ),
        (
            "CanaryD11EnumDiscriminantAndConstOkClaim",
            VALID_D11_DEF,
            "Trusted.MirSemantics.WellFormed",
            "Trusted.MirSemantics.Behavior",
            "Trusted.MirSemantics.WellFormed",
        ),
        (
            "CanaryD11EnumDiscriminantAndConstOkClaim",
            VALID_D11_DEF,
            "Trusted.MirSemantics.Behavior",
            "Trusted.MirSemantics.WellFormed",
            "Trusted.MirSemantics.Behavior",
        ),
        (
            "CanaryD11EnumDiscriminantAndConstOkClaim",
            VALID_D11_DEF,
            "RefWellFormed",
            "RefBehavior",
            "Trusted.Correspondence.RefWellFormed",
        ),
        (
            "CanaryD11EnumDiscriminantAndConstOkClaim",
            VALID_D11_DEF,
            "RefBehavior",
            "RefWellFormed",
            "Trusted.Correspondence.RefBehavior",
        ),
        (
            "CanaryD11EnumDiscriminantAndConstOkClaim",
            VALID_D11_DEF,
            "encodeProg = encodeProg",
            "Trusted.MirSemantics.progEnumExplicitReprU8 = Trusted.MirSemantics.progEnumExplicitReprU8",
            "Trusted.Correspondence.encodeProg",
        ),
        (
            "CanaryD12ZstEnumMoveAndDiscrOkClaim",
            VALID_D12_DEF,
            "Trusted.MirSemantics.progZstSingleEnumImplicitRet",
            "Trusted.MirSemantics.progZstSingleEnumMoveAndDiscr",
            "Trusted.MirSemantics.progZstSingleEnumImplicitRet",
        ),
        (
            "CanaryD12ZstEnumMoveAndDiscrOkClaim",
            VALID_D12_DEF,
            "Trusted.MirSemantics.progZstSingleEnumMoveAndDiscr",
            "Trusted.MirSemantics.progZstSingleEnumImplicitRet",
            "Trusted.MirSemantics.progZstSingleEnumMoveAndDiscr",
        ),
        (
            "CanaryD12ZstEnumMoveAndDiscrOkClaim",
            VALID_D12_DEF,
            "Trusted.MirSemantics.WellFormed",
            "Trusted.MirSemantics.Behavior",
            "Trusted.MirSemantics.WellFormed",
        ),
        (
            "CanaryD12ZstEnumMoveAndDiscrOkClaim",
            VALID_D12_DEF,
            "Trusted.MirSemantics.Behavior",
            "Trusted.MirSemantics.WellFormed",
            "Trusted.MirSemantics.Behavior",
        ),
        (
            "CanaryD12ZstEnumMoveAndDiscrOkClaim",
            VALID_D12_DEF,
            "RefWellFormed",
            "RefBehavior",
            "Trusted.Correspondence.RefWellFormed",
        ),
        (
            "CanaryD12ZstEnumMoveAndDiscrOkClaim",
            VALID_D12_DEF,
            "RefBehavior",
            "RefWellFormed",
            "Trusted.Correspondence.RefBehavior",
        ),
        (
            "CanaryD12ZstEnumMoveAndDiscrOkClaim",
            VALID_D12_DEF,
            "encodeProg = encodeProg",
            "Trusted.MirSemantics.progZstSingleEnumImplicitRet = Trusted.MirSemantics.progZstSingleEnumImplicitRet",
            "Trusted.Correspondence.encodeProg",
        ),
        (
            "CanaryD13EnumInvalidTagAndUninitUbClaim",
            VALID_D13_DEF,
            "Trusted.MirSemantics.progEnumInvalidTagConstUb",
            "Trusted.MirSemantics.progEnumUninitDiscrUb",
            "Trusted.MirSemantics.progEnumInvalidTagConstUb",
        ),
        (
            "CanaryD13EnumInvalidTagAndUninitUbClaim",
            VALID_D13_DEF,
            "Trusted.MirSemantics.progEnumUninitDiscrUb",
            "Trusted.MirSemantics.progEnumInvalidTagConstUb",
            "Trusted.MirSemantics.progEnumUninitDiscrUb",
        ),
        (
            "CanaryD13EnumInvalidTagAndUninitUbClaim",
            VALID_D13_DEF,
            "Trusted.MirSemantics.ReachesResult",
            "Trusted.MirSemantics.WellFormed",
            "Trusted.MirSemantics.ReachesResult",
        ),
        (
            "CanaryD13EnumInvalidTagAndUninitUbClaim",
            VALID_D13_DEF,
            "Trusted.MirSemantics.WellFormed",
            "Trusted.MirSemantics.ReachesResult",
            "Trusted.MirSemantics.WellFormed",
        ),
        (
            "CanaryD13EnumInvalidTagAndUninitUbClaim",
            VALID_D13_DEF,
            "RefReachesOutcome",
            "Trusted.MirSemantics.WellFormed",
            "Trusted.Correspondence.RefReachesOutcome",
        ),
        (
            "CanaryD13EnumInvalidTagAndUninitUbClaim",
            VALID_D13_DEF,
            "encodeProg = encodeProg",
            "Trusted.MirSemantics.progEnumInvalidTagConstUb = Trusted.MirSemantics.progEnumInvalidTagConstUb",
            "Trusted.Correspondence.encodeProg",
        ),
    ] {
        assert_eq!(valid_claims_text.matches(valid_def).count(), 1, "synthetic {claim} drifted");
        assert_eq!(valid_def.matches(old_tok).count(), 1, "expected unique {old_tok} in {claim}");
        let weakened_def = valid_def.replace(old_tok, replacement_tok);
        harness.publish(&ClaimsSpec::valid().with_replace(valid_def, weakened_def), &valid_proofs);
        harness.assert_default_rejected(&format!(
            "claim Trusted.Correspondence.{claim} body must reference {dropped}"
        ));
    }

    // Weakening D14–D17 canary claims fails closed.
    for (claim, valid_conjunct, weakened_conjunct, dropped) in [
        (
            "CanaryD14CharCmpAndSwitchOkClaim",
            "Trusted.MirAst.BinOp.cmp = Trusted.MirAst.MirTy.char ∧",
            "Trusted.MirAst.MirTy.char = Trusted.MirAst.MirTy.char ∧",
            "Trusted.MirAst.BinOp.cmp",
        ),
        (
            "CanaryD15IntToIntCastClaim",
            "Trusted.MirSemantics.mkIntToIntCastProg = Trusted.MirAst.MirTy.char ∧",
            "Trusted.MirAst.MirTy.char = Trusted.MirAst.MirTy.char ∧",
            "Trusted.MirSemantics.mkIntToIntCastProg",
        ),
        (
            "CanaryD16WithOverflowOkClaim",
            "Trusted.MirAst.BinOp.addWithOverflow = Trusted.MirAst.BinOp.subWithOverflow ∧",
            "Trusted.MirAst.BinOp.subWithOverflow = Trusted.MirAst.BinOp.subWithOverflow ∧",
            "Trusted.MirAst.BinOp.addWithOverflow",
        ),
        (
            "CanaryD17CallAndSysrootCallClaim",
            "progDirectCallD17 = progSysrootUncheckedAddOkD17 ∧",
            "progSysrootUncheckedAddOkD17 = progSysrootUncheckedAddOkD17 ∧",
            "Trusted.Correspondence.progDirectCallD17",
        ),
        (
            "CanaryD17CallAndSysrootCallClaim",
            "queryU16_19 = Trusted.MirSemantics.queryEmpty ∧",
            "queryU16_19 = queryU16_19 ∧",
            "Trusted.MirSemantics.queryEmpty",
        ),
        (
            "CanaryD17AssertPanicAbortClaim",
            "Trusted.MirAst.PanicStrategy.abort = Trusted.MirAst.PanicStrategy.unwind ∧",
            "Trusted.MirAst.PanicStrategy.unwind = Trusted.MirAst.PanicStrategy.unwind ∧",
            "Trusted.MirAst.PanicStrategy.abort",
        ),
    ] {
        harness.publish(
            &ClaimsSpec::valid().with_replace(valid_conjunct, weakened_conjunct),
            &valid_proofs,
        );
        harness.assert_default_rejected(&format!(
            "claim Trusted.Correspondence.{claim} body must reference {dropped}"
        ));
    }

    // 2b. `verifyRefEvaluatorIndependence` requires all 39 Miri primitives.
    harness.publish(&ClaimsSpec::valid(), &valid_proofs);
    harness.assert_default_rejected(
        "reference evaluator cone is missing required Miri primitive Miri.Interpreter.ExecutionMachine.step",
    );

    for missing_miri in [
        "Miri.Interpreter.ExecutionMachine.step",
        "Miri.Interpreter.OperandMachine.evalOperand",
        "Miri.Interpreter.ValidityVisitor.validatePlace",
        "Miri.Interpreter.Discriminant.readDiscriminant",
        "Miri.Interpreter.Discriminant.discriminantForVariant",
        "Miri.Interpreter.IntegerOps.binaryChar",
        "Miri.Interpreter.Cast.cast",
        "Miri.Interpreter.IntegerCast.cast",
        "Miri.Memory.ScalarInt.toChar",
        "Miri.Memory.ScalarInt.ofChar",
    ] {
        let kept = REQUIRED_MIRI_PRIMITIVES
            .iter()
            .copied()
            .filter(|prim| *prim != missing_miri)
            .collect::<Vec<_>>()
            .join(", ");
        harness.publish(
            &ClaimsSpec::valid().with_eval_ref_step(format!("let _ := ({kept}); 0")),
            &valid_proofs,
        );
        harness.assert_default_rejected(&format!(
            "reference evaluator cone is missing required Miri primitive {missing_miri}"
        ));
    }

    let all_miri_tuple = REQUIRED_MIRI_PRIMITIVES.join(", ");

    // 2b-ii. `RefAllowedStep` cannot mask omitting `ExecutionMachine.step`.
    harness.publish(
        &ClaimsSpec::valid().with_ref_allowed_step(format!(
            "let _ := ({all_miri_tuple}, Miri.Interpreter.ExecutionMachine.AllowedStep); 0"
        )),
        &valid_proofs,
    );
    harness.assert_default_rejected(
        "reference evaluator cone is missing required Miri primitive Miri.Interpreter.ExecutionMachine.step",
    );

    // 2b-iii. `RefAllowedStep` itself must reach `AllowedStep`.
    harness.publish(
        &ClaimsSpec::valid()
            .with_eval_ref_step(format!("let _ := ({all_miri_tuple}); 0"))
            .with_ref_allowed_step("0"),
        &valid_proofs,
    );
    harness.assert_default_rejected(
        "RefAllowedStep cone is missing required Miri primitive Miri.Interpreter.ExecutionMachine.AllowedStep",
    );

    // Reference evaluator cone must not reference disallowed `Trusted` decls.
    for (init_expr, step_expr, expected_const, expected_mod) in [
        (
            "0",
            "Trusted.MirSemantics.evalStep",
            "Trusted.MirSemantics.evalStep",
            "Trusted.MirSemantics",
        ),
        (
            "0",
            "Trusted.MirSemantics.evalArithOp",
            "Trusted.MirSemantics.evalArithOp",
            "Trusted.MirSemantics",
        ),
        (
            "0",
            "Trusted.MirSemantics.evalShiftOp",
            "Trusted.MirSemantics.evalShiftOp",
            "Trusted.MirSemantics",
        ),
        (
            "0",
            "Trusted.MirSemantics.jumpToBlock",
            "Trusted.MirSemantics.jumpToBlock",
            "Trusted.MirSemantics",
        ),
        (
            "0",
            "Trusted.MirSemantics.enumAdmitted",
            "Trusted.MirSemantics.enumAdmitted",
            "Trusted.MirSemantics",
        ),
        (
            "0",
            "Trusted.MirSemantics.tagBitsToDiscrBits",
            "Trusted.MirSemantics.tagBitsToDiscrBits",
            "Trusted.MirSemantics",
        ),
        (
            "0",
            "Trusted.MirSemantics.isZstEnumTy",
            "Trusted.MirSemantics.isZstEnumTy",
            "Trusted.MirSemantics",
        ),
        (
            "0",
            "Trusted.MirSemantics.findDiscrVariant?",
            "Trusted.MirSemantics.findDiscrVariant?",
            "Trusted.MirSemantics",
        ),
        (
            "0",
            "Trusted.MirSemantics.unlistedAnnealHelper",
            "Trusted.MirSemantics.unlistedAnnealHelper",
            "Trusted.MirSemantics",
        ),
        (
            "0",
            "Trusted.MirSemantics.subEvalHelper",
            "Trusted.MirSemantics.subEvalHelper",
            "Trusted.MirSemantics.SubHelper",
        ),
        (
            "0",
            "Trusted.MirHelper.siblingHelper",
            "Trusted.MirHelper.siblingHelper",
            "Trusted.MirHelper",
        ),
        (
            "Trusted.MirSemantics.initState",
            "0",
            "Trusted.MirSemantics.initState",
            "Trusted.MirSemantics",
        ),
        (
            "0",
            "transitiveSubHelper",
            "Trusted.MirSemantics.subEvalHelper",
            "Trusted.MirSemantics.SubHelper",
        ),
    ] {
        harness.publish(
            &ClaimsSpec::valid()
                .with_init_ref_state(init_expr)
                .with_eval_ref_step(format!("let _ := ({all_miri_tuple}); {step_expr}")),
            &valid_proofs,
        );
        harness.assert_default_rejected(&format!(
            "reference evaluator cone illegally references disallowed Trusted declaration {expected_const} (defined in {expected_mod})"
        ));
    }

    // Referencing shared boundary data in `Trusted.MirModel` is admitted.
    harness.publish(
        &ClaimsSpec::valid().with_eval_ref_step(format!(
            "let _ := ({all_miri_tuple}); Trusted.MirSemantics.sharedModelData"
        )),
        &valid_proofs,
    );
    let ok_req = harness.base_request().build();
    harness
        .run_audit(ok_req)
        .expect("Trusted.MirModel boundary data should be admitted in reference evaluator cone");

    // 2c. Module import isolation: dead import in `Correspondence.Eval` fails.
    harness.compile_trusted(
        &["Trusted.MirSemantics"],
        "Trusted.Correspondence.Eval",
        "prelude\nimport Init.Core\nimport Trusted.MirSemantics\n\
         namespace Trusted.Correspondence\ndef deadImportMarker : Nat := 0\nend Trusted.Correspondence\n",
    );
    let dead_req = CorrAuditRequestBuilder::empty(harness.search_paths.clone())
        .with_trusted_vetted("Trusted")
        .with_trusted_candidate("Trusted.MirModel")
        .with_trusted_candidate("Trusted.MirHelper")
        .with_trusted_candidate("Trusted.MirSemantics")
        .with_trusted_candidate("Trusted.MirSemantics.SubHelper")
        .with_corr_trusted_candidate("Trusted.Correspondence.Eval")
        .with_corr_trusted_candidate("Trusted.Correspondence")
        .with_corr_theory("Anneal.MirCorrespondenceProof")
        .with_vendor_miri("Miri.FakeStubs")
        .build();
    assert_policy_rejection(
        harness.run_audit(dead_req),
        "correspondence-audit",
        "reference evaluator module Trusted.Correspondence.Eval illegally imports disallowed module Trusted.MirSemantics",
    );

    // 2d. Transitive module import isolation via allowlisted module fails.
    harness.compile_trusted(
        &["Trusted.MirHelper"],
        "Trusted.MirAst.Decoy",
        "prelude\nimport Init.Core\nimport Trusted.MirHelper\n\
         namespace Trusted.MirAst\ndef decoyMarker : Nat := 0\nend Trusted.MirAst\n",
    );
    harness.compile_trusted(
        &["Trusted.MirAst.Decoy"],
        "Trusted.Correspondence.Eval",
        "prelude\nimport Init.Core\nimport Trusted.MirAst.Decoy\n\
         namespace Trusted.Correspondence\ndef transitiveDeadImportMarker : Nat := 0\nend Trusted.Correspondence\n",
    );
    let trans_req = CorrAuditRequestBuilder::empty(harness.search_paths.clone())
        .with_trusted_vetted("Trusted")
        .with_trusted_candidate("Trusted.MirModel")
        .with_trusted_candidate("Trusted.MirHelper")
        .with_trusted_candidate("Trusted.MirAst.Decoy")
        .with_trusted_candidate("Trusted.MirSemantics")
        .with_trusted_candidate("Trusted.MirSemantics.SubHelper")
        .with_corr_trusted_candidate("Trusted.Correspondence.Eval")
        .with_corr_trusted_candidate("Trusted.Correspondence")
        .with_corr_theory("Anneal.MirCorrespondenceProof")
        .with_vendor_miri("Miri.FakeStubs")
        .build();
    assert_policy_rejection(
        harness.run_audit(trans_req),
        "correspondence-audit",
        "reference evaluator module Trusted.Correspondence.Eval illegally imports disallowed module Trusted.MirHelper (via Trusted.MirAst.Decoy)",
    );

    // 2e. Placement check rejects `evalRefStep` in `Trusted.Correspondence`.
    harness.compile_trusted(
        &[],
        "Trusted.Correspondence.Eval",
        "prelude\nimport Init.Core\n\
         namespace Trusted.Correspondence\ndef cleanEvalMarker : Nat := 0\nend Trusted.Correspondence\n",
    );
    let misplaced_req = CorrAuditRequestBuilder::empty(harness.search_paths.clone())
        .with_trusted_vetted("Trusted")
        .with_trusted_candidate("Trusted.MirModel")
        .with_trusted_candidate("Trusted.MirHelper")
        .with_trusted_candidate("Trusted.MirSemantics")
        .with_trusted_candidate("Trusted.MirSemantics.SubHelper")
        .with_corr_trusted_candidate("Trusted.Correspondence.Eval")
        .with_corr_trusted_candidate("Trusted.Correspondence")
        .with_corr_theory("Anneal.MirCorrespondenceProof")
        .with_vendor_miri("Miri.FakeStubs")
        .build();
    assert_policy_rejection(
        harness.run_audit(misplaced_req),
        "correspondence-audit",
        "modular correspondence layout requires reference evaluator symbol Trusted.Correspondence.evalRefStep to be defined in an isolated evaluator module, found Trusted.Correspondence",
    );
}

/// Verifies negative cases for correspondence-audit rules in
/// `TrustedBoundary.lean` (`classifyCorrModules`,
/// `CorrOrigin.importViolation?`, `CorrOrigin.edgeViolation?`, and
/// `closureCorr` unapproved-axiom rejection) and for toolchain sysroot
/// manifest authentication (`verify_sysroot_foundation_dir`).
#[test]
fn rejects_correspondence_audit_violations_and_sysroot_mismatch() {
    let fix = TempFixture::new(None);

    // 1. Sysroot manifest mismatch & symlink rejection.
    let fake_lib = fix.root.join("fake-sysroot-lib");
    for pkg in ["Init", "Std", "Lean"] {
        fs::create_dir_all(fake_lib.join(pkg)).unwrap();
    }
    fs::write(fake_lib.join("Init/Dummy.olean"), b"dummy-olean").unwrap();
    let err_sysroot =
        verify_sysroot_foundation_dir(&fake_lib, &BTreeSet::new(), &"0".repeat(64)).unwrap_err();
    assert_eq!(err_sysroot.phase, "sysroot-foundation");
    assert!(
        err_sysroot.message.contains("sysroot Init/Std/Lean .olean/.ir manifest SHA-256 mismatch"),
        "unexpected sysroot mismatch error: {err_sysroot}"
    );
    symlink(fake_lib.join("Init/Dummy.olean"), fake_lib.join("Std/Link.olean")).unwrap();
    let err_sym =
        verify_sysroot_foundation_dir(&fake_lib, &BTreeSet::new(), &"0".repeat(64)).unwrap_err();
    assert!(
        err_sym.message.contains("symlink forbidden in sysroot"),
        "unexpected sysroot symlink error: {err_sym}"
    );

    // Prepare compiled synthetic modules for `TrustedBoundary.lean`
    // `"correspondence-audit"` negative cases.
    let mut checker = fix.checker();
    checker.set_require_mir_wp(false);
    checker.run().unwrap();
    let trusted_lib = checker.stage().join("lib");
    let aux_src = checker.stage().join("src/corr-neg");
    let aux_path = env::join_paths([&trusted_lib]).unwrap();

    let compile_aux = |chk: &mut Checker, module: &str, body: &str| {
        let rel = module.replace('.', "/");
        let src = aux_src.join(format!("{rel}.lean"));
        fs::create_dir_all(src.parent().unwrap()).unwrap();
        fs::write(&src, body).unwrap();
        let out = trusted_lib.join(format!("{rel}.olean"));
        fs::create_dir_all(out.parent().unwrap()).unwrap();
        chk.process_with_path(
            &format!("compile-{module}"),
            &[
                "-j1".to_string(),
                "-M2048".to_string(),
                "-t0".to_string(),
                "-R".to_string(),
                aux_src.to_string_lossy().into_owned(),
                "-o".to_string(),
                out.to_string_lossy().into_owned(),
                src.to_string_lossy().into_owned(),
            ],
            Some(&aux_path),
        )
        .unwrap();
    };

    compile_aux(
        &mut checker,
        "Miri.Child",
        "prelude\nimport Init.Core\nnamespace Miri.Child\ndef c : Nat := 1\nend Miri.Child\n",
    );
    compile_aux(
        &mut checker,
        "Miri.Parent",
        "prelude\nimport Init.Core\nimport Miri.Child\n\
         namespace Miri.Parent\ndef p : Nat := Miri.Child.c\nend Miri.Parent\n",
    );
    compile_aux(
        &mut checker,
        "Trusted.CandHelper",
        "-- anneal-trust-tier: candidate:mir_semantics\n\
         prelude\nimport Init.Core\nnamespace Trusted.CandHelper\ndef h : Nat := 1\nend Trusted.CandHelper\n",
    );
    compile_aux(
        &mut checker,
        "Trusted.VettedRefsCand",
        "prelude\nimport Init.Core\nimport Trusted.CandHelper\n\
         namespace Trusted.VettedRefsCand\ndef x : Nat := Trusted.CandHelper.h\nend Trusted.VettedRefsCand\n",
    );
    compile_aux(
        &mut checker,
        "Trusted.VettedRefsMiri",
        "prelude\nimport Init.Core\nimport Miri.Child\n\
         namespace Trusted.VettedRefsMiri\ndef x : Nat := Miri.Child.c\nend Trusted.VettedRefsMiri\n",
    );
    compile_aux(
        &mut checker,
        "Anneal.Helper",
        "prelude\nimport Init.Core\nnamespace Anneal.Helper\ndef t : Nat := 2\nend Anneal.Helper\n",
    );
    compile_aux(
        &mut checker,
        "Trusted.CandRefsTheory",
        "prelude\nimport Init.Core\nimport Anneal.Helper\n\
         namespace Trusted.CandRefsTheory\ndef x : Nat := Anneal.Helper.t\nend Trusted.CandRefsTheory\n",
    );
    compile_aux(
        &mut checker,
        "Miri.Interpreter.ExecutionMachine",
        "prelude\nimport Init.Core\n\
         namespace Miri.Interpreter.ExecutionMachine\n\
         theorem step : (True ↔ True) → True = True := propext\n\
         end Miri.Interpreter.ExecutionMachine\n",
    );

    let search = vec![trusted_lib];

    // 2a. `classifyCorrModules`: overlapping module role.
    let err_overlap = checker
        .inspect(InspectorRequest::CorrespondenceAudit {
            search_path: search.clone(),
            trusted: vec!["Trusted".to_string()],
            corr_trusted: Vec::new(),
            theory: Vec::new(),
            corr_theory: Vec::new(),
            vendor_miri: vec!["Trusted".to_string()],
            module_tiers: BTreeMap::from([("Trusted".to_string(), TrustTier::Vetted)]),
        })
        .unwrap_err();
    assert!(
        err_overlap.message.contains("overlapping module role for Trusted"),
        "unexpected overlap error: {err_overlap}"
    );

    // 2b. `classifyCorrModules`: missing trust tier for Trusted module.
    let err_missing_tier = checker
        .inspect(InspectorRequest::CorrespondenceAudit {
            search_path: search.clone(),
            trusted: vec!["Trusted".to_string()],
            corr_trusted: Vec::new(),
            theory: Vec::new(),
            corr_theory: Vec::new(),
            vendor_miri: vec!["Miri.Child".to_string()],
            module_tiers: BTreeMap::new(),
        })
        .unwrap_err();
    assert!(
        err_missing_tier.message.contains("missing trust tier for Trusted module Trusted"),
        "unexpected missing-tier error: {err_missing_tier}"
    );

    // 2c. `classifyCorrModules`: trust tier declared for non-Trusted module.
    let err_non_trusted_tier = checker
        .inspect(InspectorRequest::CorrespondenceAudit {
            search_path: search.clone(),
            trusted: vec!["Trusted".to_string()],
            corr_trusted: Vec::new(),
            theory: Vec::new(),
            corr_theory: Vec::new(),
            vendor_miri: vec!["Miri.Child".to_string()],
            module_tiers: BTreeMap::from([
                ("Trusted".to_string(), TrustTier::Vetted),
                ("Miri.Child".to_string(), TrustTier::Vetted),
            ]),
        })
        .unwrap_err();
    assert!(
        err_non_trusted_tier
            .message
            .contains("trust tier declared for non-Trusted module Miri.Child"),
        "unexpected non-trusted-tier error: {err_non_trusted_tier}"
    );

    // 2d. `classifyCorrModules`: foreign module in correspondence environment
    // (`Miri.Parent` imports unlisted `Miri.Child`).
    let err_foreign = checker
        .inspect(InspectorRequest::CorrespondenceAudit {
            search_path: search.clone(),
            trusted: vec!["Trusted".to_string()],
            corr_trusted: Vec::new(),
            theory: Vec::new(),
            corr_theory: Vec::new(),
            vendor_miri: vec!["Miri.Parent".to_string()],
            module_tiers: BTreeMap::from([("Trusted".to_string(), TrustTier::Vetted)]),
        })
        .unwrap_err();
    assert!(
        err_foreign.message.contains("foreign module Miri.Child in correspondence environment"),
        "unexpected foreign-module error: {err_foreign}"
    );

    // 3a. `CorrOrigin.importViolation?`: vetted -> candidate (rejected before
    // `checkDeclarationEdges` inspects the constant reference).
    let err_vetted_cand = checker
        .inspect(InspectorRequest::CorrespondenceAudit {
            search_path: search.clone(),
            trusted: vec![
                "Trusted".to_string(),
                "Trusted.CandHelper".to_string(),
                "Trusted.VettedRefsCand".to_string(),
            ],
            corr_trusted: Vec::new(),
            theory: Vec::new(),
            corr_theory: Vec::new(),
            vendor_miri: vec!["Miri.Child".to_string()],
            module_tiers: BTreeMap::from([
                ("Trusted".to_string(), TrustTier::Vetted),
                (
                    "Trusted.CandHelper".to_string(),
                    TrustTier::Candidate(CandidateFeature::MirSemantics),
                ),
                ("Trusted.VettedRefsCand".to_string(), TrustTier::Vetted),
            ]),
        })
        .unwrap_err();
    assert_eq!(err_vetted_cand.code, 1, "unexpected vetted->cand code: {err_vetted_cand}");
    assert!(
        err_vetted_cand.message.contains(
            "vetted module Trusted.VettedRefsCand cannot import candidate:mir_semantics module Trusted.CandHelper"
        ),
        "unexpected vetted->cand error: {err_vetted_cand}"
    );

    // 3b. `CorrOrigin.importViolation?`: vetted -> vendorMiri (rejected before
    // `checkDeclarationEdges` inspects the constant reference).
    let err_vetted_miri = checker
        .inspect(InspectorRequest::CorrespondenceAudit {
            search_path: search.clone(),
            trusted: vec!["Trusted".to_string(), "Trusted.VettedRefsMiri".to_string()],
            corr_trusted: Vec::new(),
            theory: Vec::new(),
            corr_theory: Vec::new(),
            vendor_miri: vec!["Miri.Child".to_string()],
            module_tiers: BTreeMap::from([
                ("Trusted".to_string(), TrustTier::Vetted),
                ("Trusted.VettedRefsMiri".to_string(), TrustTier::Vetted),
            ]),
        })
        .unwrap_err();
    assert_eq!(err_vetted_miri.code, 1, "unexpected vetted->miri code: {err_vetted_miri}");
    assert!(
        err_vetted_miri.message.contains(
            "vetted module Trusted.VettedRefsMiri cannot import non-foundation module Miri.Child"
        ),
        "unexpected vetted->miri error: {err_vetted_miri}"
    );

    // 3a-edge & 3b-edge. `CorrOrigin.edgeViolation?` defense in depth: forged
    // `vetted` `.olean` headers importing only `Init.Core` while referencing
    // `Trusted.CandHelper.h` or `Miri.Child.c` remain rejected by
    // `checkDeclarationEdges`.
    let stage = checker.stage().to_path_buf();
    for (forged_mod, ref_const, extra_trusted, expected_msg) in [
        (
            "Trusted.ForgedCorrVettedCand",
            "Trusted.CandHelper.h",
            true,
            "vetted constant Trusted.ForgedCorrVettedCand.x references candidate:mir_semantics constant Trusted.CandHelper.h",
        ),
        (
            "Trusted.ForgedCorrVettedMiri",
            "Miri.Child.c",
            false,
            "vetted constant Trusted.ForgedCorrVettedMiri.x references non-foundation constant Miri.Child.c",
        ),
    ] {
        let out = search[0].join(format!("{}.olean", forged_mod.replace('.', "/")));
        fs::create_dir_all(out.parent().unwrap()).unwrap();
        run_lean_script(
            &mut checker,
            &format!("gen-{forged_mod}"),
            &stage.join(format!("gen_{}.lean", forged_mod.replace('.', "_"))),
            &format!(
                "import Lean.Environment\n\
                 open Lean\n\
                 def main : IO Unit := do\n\
                   let ci : ConstantInfo := .defnInfo {{\n\
                     name := `{forged_mod}.x\n\
                     levelParams := []\n\
                     type := .const `Nat []\n\
                     value := .const `{ref_const} []\n\
                     hints := .abbrev\n\
                     safety := .safe\n\
                     all := [`{forged_mod}.x]\n\
                   }}\n\
                   let md : ModuleData := {{\n\
                     isModule := false\n\
                     imports := #[{{ module := `Init.Core }}]\n\
                     constNames := #[`{forged_mod}.x]\n\
                     constants := #[ci]\n\
                     extraConstNames := #[]\n\
                     entries := #[]\n\
                   }}\n\
                   saveModuleData (System.FilePath.mk {:?}) `{forged_mod} md\n",
                out.to_string_lossy()
            ),
        );
        let mut trusted_mods = vec!["Trusted".to_string(), forged_mod.to_string()];
        let mut tiers = BTreeMap::from([
            ("Trusted".to_string(), TrustTier::Vetted),
            (forged_mod.to_string(), TrustTier::Vetted),
        ]);
        if extra_trusted {
            trusted_mods.push("Trusted.CandHelper".to_string());
            tiers.insert(
                "Trusted.CandHelper".to_string(),
                TrustTier::Candidate(CandidateFeature::MirSemantics),
            );
        }
        let err_edge = checker
            .inspect(InspectorRequest::CorrespondenceAudit {
                search_path: search.clone(),
                trusted: trusted_mods,
                corr_trusted: Vec::new(),
                theory: Vec::new(),
                corr_theory: Vec::new(),
                vendor_miri: vec!["Miri.Child".to_string()],
                module_tiers: tiers,
            })
            .unwrap_err();
        assert_eq!(err_edge.code, 1, "unexpected forged edge code for {forged_mod}: {err_edge}");
        assert!(
            err_edge.message.contains(expected_msg),
            "unexpected forged edge error for {forged_mod}: {err_edge}"
        );
    }

    // 3d. `"correspondence-preflight"` rejects a declaration-free `vetted`
    // Pass 2 source importing a Pass 1 `candidate:mir_semantics` module, a
    // `vendor/lean-miri` module, or a Pass 1 `.repo .theory` module
    // (`Anneal.Helper`) before compilation, deriving Pass 1 base tiers
    // directly from staged `"baseSources"` rather than a caller map.
    let trusted_base_src = checker.modules()["Trusted"].clone();
    let cand_helper_src = aux_src.join("Trusted/CandHelper.lean");
    let corr_pf_dir = stage.join("src/corr-pf-tier");
    fs::create_dir_all(&corr_pf_dir).unwrap();
    let corr_vetted_cand_src = corr_pf_dir.join("CorrVettedCand.lean");
    fs::write(
        &corr_vetted_cand_src,
        "-- anneal-trust-tier: vetted\nprelude\nimport Init.Core\nimport Trusted.CandHelper\n",
    )
    .unwrap();
    let err_pf_cand = checker
        .inspect(InspectorRequest::CorrespondencePreflight {
            search_path: search.clone(),
            trusted: vec!["Trusted".to_string(), "Trusted.CandHelper".to_string()],
            theory: Vec::new(),
            vendor_miri: vec!["Miri.Child".to_string()],
            base_trusted_sources: vec![
                ("Trusted".to_string(), trusted_base_src.clone()),
                ("Trusted.CandHelper".to_string(), cand_helper_src.clone()),
            ],
            sources: vec![("Trusted.CorrVettedCand".to_string(), corr_vetted_cand_src.clone())],
        })
        .unwrap_err();
    assert_eq!(err_pf_cand.code, 1, "unexpected corr-pf cand code: {err_pf_cand}");
    assert_eq!(err_pf_cand.phase, "correspondence-preflight");
    assert!(
        err_pf_cand.message.contains(
            "vetted module Trusted.CorrVettedCand cannot import candidate:mir_semantics module Trusted.CandHelper"
        ),
        "unexpected corr-pf cand error: {err_pf_cand}"
    );

    let corr_vetted_miri_src = corr_pf_dir.join("CorrVettedMiri.lean");
    fs::write(
        &corr_vetted_miri_src,
        "-- anneal-trust-tier: vetted\nprelude\nimport Init.Core\nimport Miri.Child\n",
    )
    .unwrap();
    let err_pf_miri = checker
        .inspect(InspectorRequest::CorrespondencePreflight {
            search_path: search.clone(),
            trusted: vec!["Trusted".to_string()],
            theory: Vec::new(),
            vendor_miri: vec!["Miri.Child".to_string()],
            base_trusted_sources: vec![("Trusted".to_string(), trusted_base_src.clone())],
            sources: vec![("Trusted.CorrVettedMiri".to_string(), corr_vetted_miri_src)],
        })
        .unwrap_err();
    assert_eq!(err_pf_miri.code, 1, "unexpected corr-pf miri code: {err_pf_miri}");
    assert_eq!(err_pf_miri.phase, "correspondence-preflight");
    assert!(
        err_pf_miri.message.contains(
            "vetted module Trusted.CorrVettedMiri cannot import non-foundation module Miri.Child"
        ),
        "unexpected corr-pf miri error: {err_pf_miri}"
    );

    let corr_vetted_theory_src = corr_pf_dir.join("CorrVettedTheory.lean");
    fs::write(
        &corr_vetted_theory_src,
        "-- anneal-trust-tier: vetted\nprelude\nimport Init.Core\nimport Anneal.Helper\n",
    )
    .unwrap();
    let err_pf_theory = checker
        .inspect(InspectorRequest::CorrespondencePreflight {
            search_path: search.clone(),
            trusted: vec!["Trusted".to_string()],
            theory: vec!["Anneal.Helper".to_string()],
            vendor_miri: vec!["Miri.Child".to_string()],
            base_trusted_sources: vec![("Trusted".to_string(), trusted_base_src.clone())],
            sources: vec![("Trusted.CorrVettedTheory".to_string(), corr_vetted_theory_src)],
        })
        .unwrap_err();
    assert_eq!(err_pf_theory.code, 1, "unexpected corr-pf theory code: {err_pf_theory}");
    assert_eq!(err_pf_theory.phase, "correspondence-preflight");
    assert!(
        err_pf_theory.message.contains(
            "vetted module Trusted.CorrVettedTheory cannot import non-foundation module Anneal.Helper"
        ),
        "unexpected corr-pf theory error: {err_pf_theory}"
    );

    // Reject a direct `"correspondence-preflight"` caller that submits a
    // vetted source colliding with an already-loaded Pass 1 `candidate`
    // module (`Trusted.CandHelper`), or submits missing, extra, duplicate,
    // non-`Trusted`, or tactic-contaminated `base_trusted_sources`.
    let corr_fake_cand_src = corr_pf_dir.join("FakeCandHelper.lean");
    fs::write(&corr_fake_cand_src, b"-- anneal-trust-tier: vetted\nprelude\nimport Init.Core\n")
        .unwrap();
    let corr_vetted_cand_src2 = corr_pf_dir.join("CorrVettedCand2.lean");
    fs::write(
        &corr_vetted_cand_src2,
        b"-- anneal-trust-tier: vetted\nprelude\nimport Init.Core\nimport Trusted.CandHelper\n",
    )
    .unwrap();
    let err_pf_cand_collision = checker
        .inspect(InspectorRequest::CorrespondencePreflight {
            search_path: search.clone(),
            trusted: vec!["Trusted".to_string(), "Trusted.CandHelper".to_string()],
            theory: Vec::new(),
            vendor_miri: vec!["Miri.Child".to_string()],
            base_trusted_sources: vec![
                ("Trusted".to_string(), trusted_base_src.clone()),
                ("Trusted.CandHelper".to_string(), cand_helper_src.clone()),
            ],
            sources: vec![
                ("Trusted.CandHelper".to_string(), corr_fake_cand_src),
                ("Trusted.CorrVettedCand".to_string(), corr_vetted_cand_src2),
            ],
        })
        .unwrap_err();
    assert_eq!(err_pf_cand_collision.code, 1, "unexpected collision code: {err_pf_cand_collision}");
    assert_eq!(err_pf_cand_collision.phase, "correspondence-preflight");
    assert!(
        err_pf_cand_collision
            .message
            .contains("preflight source module Trusted.CandHelper collides with base module"),
        "unexpected corr-pf collision error: {err_pf_cand_collision}"
    );

    let err_pf_missing_base = checker
        .inspect(InspectorRequest::CorrespondencePreflight {
            search_path: search.clone(),
            trusted: vec!["Trusted".to_string(), "Trusted.CandHelper".to_string()],
            theory: Vec::new(),
            vendor_miri: vec!["Miri.Child".to_string()],
            base_trusted_sources: vec![("Trusted".to_string(), trusted_base_src.clone())],
            sources: vec![("Trusted.CorrVettedCand".to_string(), corr_vetted_cand_src.clone())],
        })
        .unwrap_err();
    assert_eq!(err_pf_missing_base.code, 1);
    assert_eq!(err_pf_missing_base.phase, "correspondence-preflight");
    assert!(
        err_pf_missing_base
            .message
            .contains("missing base preflight source for Trusted module Trusted.CandHelper"),
        "unexpected corr-pf missing base error: {err_pf_missing_base}"
    );

    let err_pf_extra_base = checker
        .inspect(InspectorRequest::CorrespondencePreflight {
            search_path: search.clone(),
            trusted: vec!["Trusted".to_string()],
            theory: Vec::new(),
            vendor_miri: vec!["Miri.Child".to_string()],
            base_trusted_sources: vec![
                ("Trusted".to_string(), trusted_base_src.clone()),
                ("Trusted.CandHelper".to_string(), cand_helper_src),
            ],
            sources: vec![("Trusted.CorrVettedCand".to_string(), corr_vetted_cand_src.clone())],
        })
        .unwrap_err();
    assert_eq!(err_pf_extra_base.code, 1);
    assert_eq!(err_pf_extra_base.phase, "correspondence-preflight");
    assert!(
        err_pf_extra_base.message.contains(
            "extra base preflight source Trusted.CandHelper missing from trusted inventory"
        ),
        "unexpected corr-pf extra base error: {err_pf_extra_base}"
    );

    let err_pf_dup_base = checker
        .inspect(InspectorRequest::CorrespondencePreflight {
            search_path: search.clone(),
            trusted: vec!["Trusted".to_string()],
            theory: Vec::new(),
            vendor_miri: vec!["Miri.Child".to_string()],
            base_trusted_sources: vec![
                ("Trusted".to_string(), trusted_base_src.clone()),
                ("Trusted".to_string(), trusted_base_src.clone()),
            ],
            sources: vec![("Trusted.CorrVettedCand".to_string(), corr_vetted_cand_src.clone())],
        })
        .unwrap_err();
    assert_eq!(err_pf_dup_base.code, 1);
    assert_eq!(err_pf_dup_base.phase, "correspondence-preflight");
    assert!(
        err_pf_dup_base.message.contains("duplicate base preflight source module Trusted"),
        "unexpected corr-pf duplicate base error: {err_pf_dup_base}"
    );

    let err_pf_non_trusted_base = checker
        .inspect(InspectorRequest::CorrespondencePreflight {
            search_path: search.clone(),
            trusted: vec!["Trusted".to_string()],
            theory: Vec::new(),
            vendor_miri: vec!["Miri.Child".to_string()],
            base_trusted_sources: vec![
                ("Trusted".to_string(), trusted_base_src),
                ("Anneal.Helper".to_string(), aux_src.join("Anneal/Helper.lean")),
            ],
            sources: vec![("Trusted.CorrVettedCand".to_string(), corr_vetted_cand_src.clone())],
        })
        .unwrap_err();
    assert_eq!(err_pf_non_trusted_base.code, 1);
    assert_eq!(err_pf_non_trusted_base.phase, "correspondence-preflight");
    assert!(
        err_pf_non_trusted_base.message.contains("non-Trusted base preflight source Anneal.Helper"),
        "unexpected corr-pf non-Trusted base error: {err_pf_non_trusted_base}"
    );

    let bad_base_tactic_src = corr_pf_dir.join("BadBaseTactic.lean");
    fs::write(
        &bad_base_tactic_src,
        b"-- anneal-trust-tier: vetted\nprelude\nimport Init.Core\ntheorem bad : Eq 0 0 := by rfl\n",
    )
    .unwrap();
    let err_pf_tactic_base = checker
        .inspect(InspectorRequest::CorrespondencePreflight {
            search_path: search.clone(),
            trusted: vec!["Trusted".to_string()],
            theory: Vec::new(),
            vendor_miri: vec!["Miri.Child".to_string()],
            base_trusted_sources: vec![("Trusted".to_string(), bad_base_tactic_src)],
            sources: vec![("Trusted.CorrVettedCand".to_string(), corr_vetted_cand_src)],
        })
        .unwrap_err();
    assert_eq!(err_pf_tactic_base.code, 1);
    assert_eq!(err_pf_tactic_base.phase, "correspondence-preflight");

    // 3c. `CorrOrigin.importViolation?`: candidate Trusted -> theory. The
    // compiled `.olean` header import of `Anneal.Helper` is rejected before
    // `checkDeclarationEdges` inspects the constant reference;
    // `rejects_forged_trusted_constant_referencing_theory` covers that
    // constant-edge rule with a forged header that omits the import.
    let err_cand_theory = checker
        .inspect(InspectorRequest::CorrespondenceAudit {
            search_path: search.clone(),
            trusted: vec!["Trusted".to_string(), "Trusted.CandRefsTheory".to_string()],
            corr_trusted: Vec::new(),
            theory: vec!["Anneal.Helper".to_string()],
            corr_theory: Vec::new(),
            vendor_miri: vec!["Miri.Child".to_string()],
            module_tiers: BTreeMap::from([
                ("Trusted".to_string(), TrustTier::Vetted),
                (
                    "Trusted.CandRefsTheory".to_string(),
                    TrustTier::Candidate(CandidateFeature::MirSemantics),
                ),
            ]),
        })
        .unwrap_err();
    assert_eq!(err_cand_theory.code, 1, "unexpected cand->theory code: {err_cand_theory}");
    assert!(
        err_cand_theory.message.contains(
            "Trusted module Trusted.CandRefsTheory cannot import non-Trusted module Anneal.Helper"
        ),
        "unexpected cand->theory error: {err_cand_theory}"
    );

    // 4. `closureCorr`: reachable unapproved axiom (`propext` from `Init.Core`
    // when omitted from the axiom allowlist) rejected after passing
    // `verifyAndCollectCorrLocals` and standalone kernel replay.
    checker.admitted_mut().unwrap().axioms.retain(|(ax, _)| ax != "propext");
    let err_axiom = checker
        .inspect(InspectorRequest::CorrespondenceAudit {
            search_path: search,
            trusted: vec!["Trusted".to_string()],
            corr_trusted: Vec::new(),
            theory: Vec::new(),
            corr_theory: Vec::new(),
            vendor_miri: vec!["Miri.Interpreter.ExecutionMachine".to_string()],
            module_tiers: BTreeMap::from([("Trusted".to_string(), TrustTier::Vetted)]),
        })
        .unwrap_err();
    assert!(
        err_axiom.message.contains("unapproved axiom propext from Init.Core"),
        "unexpected unapproved-axiom error: {err_axiom}"
    );
}
