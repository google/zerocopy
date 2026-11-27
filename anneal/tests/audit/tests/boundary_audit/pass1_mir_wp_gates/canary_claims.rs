// Copyright 2026 The Fuchsia Authors
//
// Licensed under a BSD-style license <LICENSE-BSD>, Apache License, Version 2.0
// <LICENSE-APACHE or https://www.apache.org/licenses/LICENSE-2.0>, or the MIT
// license <LICENSE-MIT or https://opensource.org/licenses/MIT>, at your option.
// This file may not be copied, modified, or distributed except according to
// those terms.

//! `MirWp` claim/proof rules for canaries and contract canaries.

use super::*;

/// Verifies every rejection branch of `requireClaimProof` (exact-claim mode,
/// `argName? = none`) in `TrustedBoundary.lean` across the 26 canary claims
/// (missing claim, non-definition claim, wrong-module claim, non-`Prop` claim,
/// claim body missing required constant, missing canary theorem, non-theorem
/// proof, wrong-module proof, and weakened/wrong-type canary theorem).
#[test]
fn enforces_mir_wp_canary_claim_proof_rules() {
    // Missing canary claim from `Trusted.MirSemantics`.
    let mut missing_claim = MirWpFixtureSpec::valid();
    missing_claim.canary_claim_overrides.insert("CanaryPositiveAddAnnealClaim".to_string(), None);
    missing_claim.canary_proof_overrides.insert("canary_positive_add_anneal".to_string(), None);
    expect_mir_wp_audit_policy_err(
        &missing_claim,
        "missing required claim Trusted.MirSemantics.CanaryPositiveAddAnnealClaim",
    );

    // Non-definition canary claim (`inductive` instead of `def`).
    let mut non_def_claim = MirWpFixtureSpec::valid();
    non_def_claim.canary_claim_overrides.insert(
        "CanaryPositiveAddAnnealClaim".to_string(),
        Some("inductive CanaryPositiveAddAnnealClaim : Prop where\n  | intro".to_string()),
    );
    non_def_claim.canary_proof_overrides.insert(
        "canary_positive_add_anneal".to_string(),
        Some(
            "theorem canary_positive_add_anneal : \
             Trusted.MirSemantics.CanaryPositiveAddAnnealClaim := \
             Trusted.MirSemantics.CanaryPositiveAddAnnealClaim.intro"
                .to_string(),
        ),
    );
    expect_mir_wp_audit_policy_err(
        &non_def_claim,
        "expected Trusted.MirSemantics.CanaryPositiveAddAnnealClaim to be a definition",
    );

    // Canary claim defined in `Trusted.MirAst` instead of
    // `Trusted.MirSemantics`.
    let mut wrong_claim_mod = MirWpFixtureSpec::valid();
    wrong_claim_mod.canary_claim_overrides.insert("CanaryPositiveAddAnnealClaim".to_string(), None);
    wrong_claim_mod.mir_ast_extra = "\
        namespace Trusted.MirSemantics\n\
        def CanaryPositiveAddAnnealClaim : Prop := True\n\
        end Trusted.MirSemantics"
        .to_string();
    expect_mir_wp_audit_policy_err(
        &wrong_claim_mod,
        "expected Trusted.MirSemantics.CanaryPositiveAddAnnealClaim to be defined in \
         Trusted.MirSemantics, found Trusted.MirAst",
    );

    // Canary claim declared inside decoupled `Anneal.MirWp.Canaries`
    // (rejected fail-closed by `Trusted` namespace isolation in
    // `validateRepoConstant`).
    let mut claim_in_theory = MirWpFixtureSpec::valid();
    claim_in_theory.canary_claim_overrides.insert("CanaryPositiveAddAnnealClaim".to_string(), None);
    claim_in_theory.canary_proof_overrides.insert("canary_positive_add_anneal".to_string(), None);
    claim_in_theory.canaries_extra = "\
        namespace Trusted.MirSemantics\n\
        def CanaryPositiveAddAnnealClaim : Prop := True\n\
        end Trusted.MirSemantics\n\
        namespace Anneal.MirWp\n\
        theorem canary_positive_add_anneal : \
            Trusted.MirSemantics.CanaryPositiveAddAnnealClaim := True.intro\n\
        end Anneal.MirWp"
        .to_string();
    expect_mir_wp_audit_policy_err(
        &claim_in_theory,
        "non-Trusted module Anneal.MirWp.Canaries cannot declare constant \
         Trusted.MirSemantics.CanaryPositiveAddAnnealClaim in Trusted namespace",
    );

    // Non-`Prop` canary claim (`Nat` instead of `Prop`).
    let mut non_prop_claim = MirWpFixtureSpec::valid();
    non_prop_claim.canary_claim_overrides.insert(
        "CanaryPositiveAddAnnealClaim".to_string(),
        Some("def CanaryPositiveAddAnnealClaim : Nat := 0".to_string()),
    );
    non_prop_claim.canary_proof_overrides.insert("canary_positive_add_anneal".to_string(), None);
    expect_mir_wp_audit_policy_err(
        &non_prop_claim,
        "expected Trusted.MirSemantics.CanaryPositiveAddAnnealClaim to have type Prop",
    );

    // Canary claim body missing required `PositiveCanaryClaim` constant
    // (`TrustedBoundary.lean` `requireClaimProof` `reqConsts` check).
    let mut missing_req_const = MirWpFixtureSpec::valid();
    missing_req_const.canary_claim_overrides.insert(
        "CanaryPositiveAddAnnealClaim".to_string(),
        Some("def CanaryPositiveAddAnnealClaim : Prop := True".to_string()),
    );
    expect_mir_wp_audit_policy_err(
        &missing_req_const,
        "claim Trusted.MirSemantics.CanaryPositiveAddAnnealClaim body must reference \
         Trusted.MirSemantics.PositiveCanaryClaim",
    );

    // Missing canary theorem (first canary and last canary).
    let mut missing_first_canary = MirWpFixtureSpec::valid();
    missing_first_canary
        .canary_proof_overrides
        .insert("canary_positive_add_anneal".to_string(), None);
    expect_mir_wp_audit_policy_err(
        &missing_first_canary,
        "missing required theorem Anneal.MirWp.canary_positive_add_anneal",
    );

    let mut missing_last_canary = MirWpFixtureSpec::valid();
    missing_last_canary
        .canary_proof_overrides
        .insert("canary_contract_anneal".to_string(), None);
    expect_mir_wp_audit_policy_err(
        &missing_last_canary,
        "missing required theorem Anneal.MirWp.canary_contract_anneal",
    );

    // Non-theorem canary proof (`def` instead of `theorem`).
    let mut def_canary = MirWpFixtureSpec::valid();
    def_canary.canary_proof_overrides.insert(
        "canary_positive_add_anneal".to_string(),
        Some("def canary_positive_add_anneal : Nat := 0".to_string()),
    );
    expect_mir_wp_audit_policy_err(
        &def_canary,
        "expected Anneal.MirWp.canary_positive_add_anneal to be a theorem",
    );

    // Canary theorem defined in `Anneal.Wp` instead of `Anneal.MirWp.Canaries`.
    let mut wrong_proof_mod = MirWpFixtureSpec::valid();
    wrong_proof_mod.canary_proof_overrides.insert("canary_positive_add_anneal".to_string(), None);
    wrong_proof_mod.anneal_extra = "\
        namespace Anneal.MirWp\n\
        theorem canary_positive_add_anneal : \
            Trusted.MirSemantics.CanaryPositiveAddAnnealClaim := True.intro\n\
        end Anneal.MirWp"
        .to_string();
    expect_mir_wp_audit_policy_err(
        &wrong_proof_mod,
        "expected Anneal.MirWp.canary_positive_add_anneal to be defined in \
         Anneal.MirWp.Canaries, found Anneal.Wp",
    );

    // Weakened / wrong-type canary theorem (`True` instead of the pinned
    // `CanaryPositiveAddAnnealClaim`).
    let mut weakened_canary = MirWpFixtureSpec::valid();
    weakened_canary.canary_proof_overrides.insert(
        "canary_positive_add_anneal".to_string(),
        Some("theorem canary_positive_add_anneal : True := True.intro".to_string()),
    );
    expect_mir_wp_audit_policy_err(
        &weakened_canary,
        "theorem Anneal.MirWp.canary_positive_add_anneal must prove \
         Trusted.MirSemantics.CanaryPositiveAddAnnealClaim directly",
    );

    // Memory-lifecycle canary claim that drops `forceAllocation` (so the
    // `.indirect`-local path is no longer exercised).
    let mut weak_memory_canary = MirWpFixtureSpec::valid();
    weak_memory_canary.canary_claim_overrides.insert(
        "CanaryMemoryLifecycleAnnealClaim".to_string(),
        Some(
            "def CanaryMemoryLifecycleAnnealClaim : Prop := \
             And PositiveCanaryClaim (And initState (And evalStep (And readBytes readBytes)))"
                .to_string(),
        ),
    );
    expect_mir_wp_audit_policy_err(
        &weak_memory_canary,
        "claim Trusted.MirSemantics.CanaryMemoryLifecycleAnnealClaim body must reference \
         Trusted.MirSemantics.forceAllocation",
    );

    // Crate/unit/body-verified, `char`, `BinOp.cmp`, overflow-pair, and
    // `IntToInt` cast canary claims that each replace one pinned constant with
    // a duplicate of another (so the operation, fixture, contract symbol, or UB
    // path is no longer exercised while the synthetic proof still type-checks).
    // Each weakened body keeps every other required constant, so the
    // rejection names exactly the dropped one.
    for (claim, weakened_body, dropped) in [
        (
            "CanaryCrateAndBodyVerifiedAnnealClaim",
            "And UnitTheorem (And UnitTheorem BodyVerified)",
            "Trusted.MirSemantics.CrateTheorem",
        ),
        (
            "CanaryCrateAndBodyVerifiedAnnealClaim",
            "And CrateTheorem (And CrateTheorem BodyVerified)",
            "Trusted.MirSemantics.UnitTheorem",
        ),
        (
            "CanaryCrateAndBodyVerifiedAnnealClaim",
            "And CrateTheorem (And UnitTheorem CrateTheorem)",
            "Trusted.MirSemantics.BodyVerified",
        ),
        (
            "CanaryPositiveCharAndCmpAnnealClaim",
            "And PositiveCanaryClaim (And mkBinOpProg (And mkBinOpProg \
             (And Trusted.MirAst.MirTy.char (And charVal \
             (And mkCmpDiscriminantProg progCharSwitch)))))",
            "Trusted.MirAst.BinOp.cmp",
        ),
        (
            "CanaryNegativeCharAndCmpAnnealClaim",
            "And NegativeCanaryClaim (And progInvalidCharConstUb \
             (And progInvalidCharConstUb (And mkBinOpProg \
             (And Trusted.MirAst.BinOp.cmp mkUnOpProg))))",
            "Trusted.MirSemantics.progInvalidCharSwitchCaseUb",
        ),
        (
            "CanaryPositiveOverflowOpsAnnealClaim",
            "And PositiveCanaryClaim (And mkBinOpProg (And overflowPairTy \
             (And Trusted.MirAst.BinOp.addWithOverflow \
             (And Trusted.MirAst.BinOp.subWithOverflow \
             Trusted.MirAst.BinOp.subWithOverflow))))",
            "Trusted.MirAst.BinOp.mulWithOverflow",
        ),
        (
            "CanaryPositiveIntToIntCastAnnealClaim",
            "And PositiveCanaryClaim (And charVal (And Trusted.MirAst.MirTy.char charVal))",
            "Trusted.MirSemantics.mkIntToIntCastProg",
        ),
        (
            "CanaryNegativeIntToIntCastAnnealClaim",
            "And NegativeCanaryClaim (And mkIntToIntCastProg \
             (And Trusted.MirAst.MirTy.char mkIntToIntCastProg))",
            "Trusted.MirSemantics.progCastUninitSourceUb",
        ),
    ] {
        let mut weak_canary = MirWpFixtureSpec::valid();
        weak_canary.canary_claim_overrides.insert(
            claim.to_string(),
            Some(format!("def {claim} : Prop := {weakened_body}")),
        );
        expect_mir_wp_audit_policy_err(
            &weak_canary,
            &format!("claim Trusted.MirSemantics.{claim} body must reference {dropped}"),
        );
    }

    // Missing, non-definition, non-abbrev, wrong-module, universe-polymorphic,
    // or un-wired `Trusted.{Crate, CrateTheorem, UnitTheorem}` public aliases
    // and their Profile v2 counterparts are rejected fail-closed by
    // `verifyMirWpCoreTheorems`.
    for alias in [
        "Crate",
        "CrateTheorem",
        "UnitTheorem",
        "CrateV2",
        "CrateTheoremV2",
        "UnitTheoremV2",
    ] {
        let mut missing_alias = MirWpFixtureSpec::valid();
        missing_alias.public_alias_overrides.insert(alias.to_string(), None);
        expect_mir_wp_audit_policy_err(
            &missing_alias,
            &format!("missing required MIR public alias Trusted.{alias}"),
        );

        let mut non_abbrev_alias = MirWpFixtureSpec::valid();
        non_abbrev_alias.public_alias_overrides.insert(
            alias.to_string(),
            Some(format!("def {alias} := Trusted.MirSemantics.{alias}")),
        );
        expect_mir_wp_audit_policy_err(
            &non_abbrev_alias,
            &format!("alias Trusted.{alias} must be an abbrev (ReducibilityHints.abbrev)"),
        );

        let mut rewired_alias = MirWpFixtureSpec::valid();
        rewired_alias
            .public_alias_overrides
            .insert(alias.to_string(), Some(format!("abbrev {alias} : Prop := True")));
        expect_mir_wp_audit_policy_err(
            &rewired_alias,
            &format!("alias Trusted.{alias} must directly alias Trusted.MirSemantics.{alias}"),
        );

        let mut non_def_alias = MirWpFixtureSpec::valid();
        non_def_alias
            .public_alias_overrides
            .insert(alias.to_string(), Some(format!("theorem {alias} : True := True.intro")));
        expect_mir_wp_audit_policy_err(
            &non_def_alias,
            &format!("expected Trusted.{alias} to be a definition"),
        );

        let mut poly_alias = MirWpFixtureSpec::valid();
        poly_alias.public_alias_overrides.insert(
            alias.to_string(),
            Some(format!("abbrev {alias}.{{u}} : Type u → Prop := fun _ => True")),
        );
        expect_mir_wp_audit_policy_err(
            &poly_alias,
            &format!("alias Trusted.{alias} must have no universe parameters"),
        );
    }

    let mut wrong_mod_alias = MirWpFixtureSpec::valid();
    wrong_mod_alias.public_alias_overrides.insert("UnitTheorem".to_string(), None);
    wrong_mod_alias.mir_ast_extra = "\
        namespace Trusted\n\
        abbrev UnitTheorem : Prop := True\n\
        end Trusted"
        .to_string();
    expect_mir_wp_audit_policy_err(
        &wrong_mod_alias,
        "expected Trusted.UnitTheorem to be defined in Trusted.MirSemantics, found Trusted.MirAst",
    );

    let mut cross_wired_alias = MirWpFixtureSpec::valid();
    cross_wired_alias.public_alias_overrides.insert(
        "UnitTheorem".to_string(),
        Some("noncomputable abbrev UnitTheorem := Trusted.MirSemantics.CrateTheorem".to_string()),
    );
    expect_mir_wp_audit_policy_err(
        &cross_wired_alias,
        "alias Trusted.UnitTheorem must directly alias Trusted.MirSemantics.UnitTheorem",
    );

    // A Profile v2 alias wired to its Profile v1 counterpart is rejected.
    for (alias, v1_target) in [
        ("CrateV2", "Crate"),
        ("CrateTheoremV2", "CrateTheorem"),
        ("UnitTheoremV2", "UnitTheorem"),
    ] {
        let mut v1_wired_alias = MirWpFixtureSpec::valid();
        v1_wired_alias.public_alias_overrides.insert(
            alias.to_string(),
            Some(format!(
                "noncomputable abbrev {alias} := Trusted.MirSemantics.{v1_target}"
            )),
        );
        expect_mir_wp_audit_policy_err(
            &v1_wired_alias,
            &format!("alias Trusted.{alias} must directly alias Trusted.MirSemantics.{alias}"),
        );
    }
}

fn assert_drop_one_contract_req_consts(cases: &[(&str, &str)]) {
    for &(weakened_body, dropped) in cases {
        let mut weak_canary = MirWpFixtureSpec::valid();
        weak_canary.canary_claim_overrides.insert(
            "CanaryContractAnnealClaim".to_string(),
            Some(format!("def CanaryContractAnnealClaim : Prop := {weakened_body}")),
        );
        expect_mir_wp_audit_policy_err(
            &weak_canary,
            &format!(
                "claim Trusted.MirSemantics.CanaryContractAnnealClaim body must reference {dropped}"
            ),
        );
    }
}

/// Verifies missing/weakened `CanaryContractAnnealClaim` and
/// `canary_contract_anneal` rejection plus the first contract constants slice.
#[test]
fn enforces_mir_wp_contract_canary_claim_proof_rules() {
    let mut missing_contract_claim = MirWpFixtureSpec::valid();
    missing_contract_claim
        .canary_claim_overrides
        .insert("CanaryContractAnnealClaim".to_string(), None);
    missing_contract_claim
        .canary_proof_overrides
        .insert("canary_contract_anneal".to_string(), None);
    expect_mir_wp_audit_policy_err(
        &missing_contract_claim,
        "missing required claim Trusted.MirSemantics.CanaryContractAnnealClaim",
    );

    let mut weakened_contract_canary = MirWpFixtureSpec::valid();
    weakened_contract_canary.canary_proof_overrides.insert(
        "canary_contract_anneal".to_string(),
        Some("theorem canary_contract_anneal : True := True.intro".to_string()),
    );
    expect_mir_wp_audit_policy_err(
        &weakened_contract_canary,
        "theorem Anneal.MirWp.canary_contract_anneal must prove \
         Trusted.MirSemantics.CanaryContractAnnealClaim directly",
    );

    assert_drop_one_contract_req_consts(&[
        (
            "And EffectMask.partialAnyExit (And EffectMask.partialAnyExit \
             (And FnContract (And decodeScalar (And scalarAsInt \
             (And BodyContractSatisfied (And ContractPreInhabited \
             (And ContractSignature (And bodyMatchesContractSignature \
             (And ContractEntry (And ContractSpecs \
             (And contractEntryRbLookup UnitTheorem)))))))))))",
            "Trusted.MirSemantics.EffectMask.totalNormal",
        ),
        (
            "And EffectMask.totalNormal (And EffectMask.totalNormal \
             (And FnContract (And decodeScalar (And scalarAsInt \
             (And BodyContractSatisfied (And ContractPreInhabited \
             (And ContractSignature (And bodyMatchesContractSignature \
             (And ContractEntry (And ContractSpecs \
             (And contractEntryRbLookup UnitTheorem)))))))))))",
            "Trusted.MirSemantics.EffectMask.partialAnyExit",
        ),
        (
            "And EffectMask.totalNormal (And EffectMask.partialAnyExit \
             (And UnitTheorem (And decodeScalar (And scalarAsInt \
             (And BodyContractSatisfied (And ContractPreInhabited \
             (And ContractSignature (And bodyMatchesContractSignature \
             (And ContractEntry (And ContractSpecs \
             (And contractEntryRbLookup UnitTheorem)))))))))))",
            "Trusted.MirSemantics.FnContract",
        ),
        (
            "And EffectMask.totalNormal (And EffectMask.partialAnyExit \
             (And FnContract (And scalarAsInt (And scalarAsInt \
             (And BodyContractSatisfied (And ContractPreInhabited \
             (And ContractSignature (And bodyMatchesContractSignature \
             (And ContractEntry (And ContractSpecs \
             (And contractEntryRbLookup UnitTheorem)))))))))))",
            "Trusted.MirSemantics.decodeScalar",
        ),
        (
            "And EffectMask.totalNormal (And EffectMask.partialAnyExit \
             (And FnContract (And decodeScalar (And decodeScalar \
             (And BodyContractSatisfied (And ContractPreInhabited \
             (And ContractSignature (And bodyMatchesContractSignature \
             (And ContractEntry (And ContractSpecs \
             (And contractEntryRbLookup UnitTheorem)))))))))))",
            "Trusted.MirSemantics.scalarAsInt",
        ),
        (
            "And EffectMask.totalNormal (And EffectMask.partialAnyExit \
             (And FnContract (And decodeScalar (And scalarAsInt \
             (And ContractPreInhabited (And ContractPreInhabited \
             (And ContractSignature (And bodyMatchesContractSignature \
             (And ContractEntry (And ContractSpecs \
             (And contractEntryRbLookup UnitTheorem)))))))))))",
            "Trusted.MirSemantics.BodyContractSatisfied",
        ),
    ]);
}

/// Verifies the remaining required constants in `CanaryContractAnnealClaim`.
#[test]
fn enforces_mir_wp_contract_canary_req_consts() {
    assert_drop_one_contract_req_consts(&[
        (
            "And EffectMask.totalNormal (And EffectMask.partialAnyExit \
             (And FnContract (And decodeScalar (And scalarAsInt \
             (And BodyContractSatisfied (And BodyContractSatisfied \
             (And ContractSignature (And bodyMatchesContractSignature \
             (And ContractEntry (And ContractSpecs \
             (And contractEntryRbLookup UnitTheorem)))))))))))",
            "Trusted.MirSemantics.ContractPreInhabited",
        ),
        (
            "And EffectMask.totalNormal (And EffectMask.partialAnyExit \
             (And FnContract (And decodeScalar (And scalarAsInt \
             (And BodyContractSatisfied (And ContractPreInhabited \
             (And bodyMatchesContractSignature (And bodyMatchesContractSignature \
             (And ContractEntry (And ContractSpecs \
             (And contractEntryRbLookup UnitTheorem)))))))))))",
            "Trusted.MirSemantics.ContractSignature",
        ),
        (
            "And EffectMask.totalNormal (And EffectMask.partialAnyExit \
             (And FnContract (And decodeScalar (And scalarAsInt \
             (And BodyContractSatisfied (And ContractPreInhabited \
             (And ContractSignature (And ContractSignature \
             (And ContractEntry (And ContractSpecs \
             (And contractEntryRbLookup UnitTheorem)))))))))))",
            "Trusted.MirSemantics.bodyMatchesContractSignature",
        ),
        (
            "And EffectMask.totalNormal (And EffectMask.partialAnyExit \
             (And FnContract (And decodeScalar (And scalarAsInt \
             (And BodyContractSatisfied (And ContractPreInhabited \
             (And ContractSignature (And bodyMatchesContractSignature \
             (And ContractSpecs (And ContractSpecs \
             (And contractEntryRbLookup UnitTheorem)))))))))))",
            "Trusted.MirSemantics.ContractEntry",
        ),
        (
            "And EffectMask.totalNormal (And EffectMask.partialAnyExit \
             (And FnContract (And decodeScalar (And scalarAsInt \
             (And BodyContractSatisfied (And ContractPreInhabited \
             (And ContractSignature (And bodyMatchesContractSignature \
             (And ContractEntry (And ContractEntry \
             (And contractEntryRbLookup UnitTheorem)))))))))))",
            "Trusted.MirSemantics.ContractSpecs",
        ),
        (
            "And EffectMask.totalNormal (And EffectMask.partialAnyExit \
             (And FnContract (And decodeScalar (And scalarAsInt \
             (And BodyContractSatisfied (And ContractPreInhabited \
             (And ContractSignature (And bodyMatchesContractSignature \
             (And ContractEntry (And ContractSpecs \
             (And ContractSpecs UnitTheorem)))))))))))",
            "Trusted.MirSemantics.contractEntryRbLookup",
        ),
        (
            "And EffectMask.totalNormal (And EffectMask.partialAnyExit \
             (And FnContract (And decodeScalar (And scalarAsInt \
             (And BodyContractSatisfied (And ContractPreInhabited \
             (And ContractSignature (And bodyMatchesContractSignature \
             (And ContractEntry (And ContractSpecs \
             (And contractEntryRbLookup ContractEntry)))))))))))",
            "Trusted.MirSemantics.UnitTheorem",
        ),
    ]);
}
