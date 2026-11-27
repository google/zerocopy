// Copyright 2026 The Fuchsia Authors
//
// Licensed under a BSD-style license <LICENSE-BSD>, Apache License, Version 2.0
// <LICENSE-APACHE or https://www.apache.org/licenses/LICENSE-2.0>, or the MIT
// license <LICENSE-MIT or https://opensource.org/licenses/MIT>, at your option.
// This file may not be copied, modified, or distributed except according to
// those terms.

//! Correspondence non-backsliding.

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
