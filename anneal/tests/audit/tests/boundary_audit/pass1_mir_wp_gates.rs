// Copyright 2026 The Fuchsia Authors
//
// Licensed under a BSD-style license <LICENSE-BSD>, Apache License, Version 2.0
// <LICENSE-APACHE or https://www.apache.org/licenses/LICENSE-2.0>, or the MIT
// license <LICENSE-MIT or https://opensource.org/licenses/MIT>, at your option.
// This file may not be copied, modified, or distributed except according to
// those terms.

//! `MirWp` non-backsliding and claim/proof rules for parameters, canaries,
//! and contract canaries.

use super::*;

fn expect_mir_wp_audit_policy_err(spec: &MirWpFixtureSpec, expected_substring: &str) {
    let fix = materialize_mir_wp(spec);
    let mut checker = fix.checker();
    let err = checker.run().unwrap_err();
    assert_eq!(err.code, 1, "expected exit code 1, got: {err}");
    assert_eq!(err.phase, "audit", "expected audit phase, got: {err}");
    assert!(checker.execution_began(), "expected Lean execution before audit failure: {err}");
    assert!(
        err.message.contains(expected_substring),
        "expected error containing {expected_substring:?}, got: {err}"
    );
}

/// Verifies every trigger and missing-module rejection branch of
/// `verifyMirWpCoreTheorems` (`TrustedBoundary.lean`): default
/// `require_mir_wp == true` on bare/partial checkouts, plus every individual
/// module trigger (`Anneal.PureLift`, `Anneal.MirWp`, `Trusted.MirSemantics`,
/// `Trusted.MirAst`) when `require_mir_wp == false`.
#[test]
fn enforces_mir_wp_non_backsliding() {
    // 0. With default `Checker::new` (`require_mir_wp == true`), even a
    // checkout with NONE of `Trusted.MirAst`, `Trusted.MirSemantics`,
    // `Anneal.MirWp`, or `Anneal.PureLift` is rejected fail-closed.
    let fix_missing_all = TempFixture::new(Some(HEADER));
    let mut checker_missing_all = fix_missing_all.checker();
    let err_missing_all = checker_missing_all.run().unwrap_err();
    assert_eq!(err_missing_all.code, 1);
    assert_eq!(err_missing_all.phase, "audit");
    assert!(
        err_missing_all.message.contains("missing required trusted module Trusted.MirAst"),
        "unexpected error: {err_missing_all}"
    );

    // 1. With default `Checker::new` (`require_mir_wp == true`), deleting both
    // `Trusted/MirSemantics.lean` and `Anneal/MirWp.lean` (even when
    // `Trusted/MirAst.lean` is present) is rejected fail-closed.
    let fix_missing_both = TempFixture::new(Some(HEADER));
    fs::create_dir_all(fix_missing_both.root.join("trusted/lean/Trusted")).unwrap();
    fs::write(
        fix_missing_both.root.join("trusted/lean/Trusted/MirAst.lean"),
        b"-- anneal-trust-tier: candidate:mir_ast\nprelude\nimport Init.NotationExtra\nnamespace Trusted.MirAst\ndef placeholder : Nat := 0\nend Trusted.MirAst\n",
    )
    .unwrap();
    let mut checker_missing_both = fix_missing_both.checker();
    let err_missing_both = checker_missing_both.run().unwrap_err();
    assert_eq!(err_missing_both.code, 1);
    assert_eq!(err_missing_both.phase, "audit");
    assert!(
        err_missing_both.message.contains("missing required trusted module Trusted.MirSemantics"),
        "unexpected error: {err_missing_both}"
    );

    // 2. With `require_mir_wp == false`, presence of `Anneal.PureLift` alone
    // triggers `verifyMirWpCoreTheorems` and rejects with exit code 1.
    let mut fix_pure_lift_only = TempFixture::new(Some(HEADER));
    fs::create_dir_all(fix_pure_lift_only.root.join("theory/Anneal")).unwrap();
    fs::write(
        fix_pure_lift_only.root.join("theory/Anneal.lean"),
        b"prelude\nimport Trusted\nimport Anneal.PureLift\n",
    )
    .unwrap();
    fs::write(
        fix_pure_lift_only.root.join("theory/Anneal/PureLift.lean"),
        b"prelude\nimport Init.NotationExtra\nnamespace Anneal.PureLift\ndef marker : Nat := 0\nend Anneal.PureLift\n",
    )
    .unwrap();
    let err_pure_lift =
        fix_pure_lift_only.check_expected(Some(1), Some("audit"), Some(true)).unwrap_err();
    assert!(
        err_pure_lift.message.contains("missing required trusted module Trusted.MirAst"),
        "unexpected error: {err_pure_lift}"
    );

    // 3. With `require_mir_wp == false`, presence of `Anneal.MirWp` alone
    // triggers `verifyMirWpCoreTheorems` and rejects with exit code 1.
    let mut fix_mir_wp_only = TempFixture::new(Some(HEADER));
    fs::create_dir_all(fix_mir_wp_only.root.join("theory/Anneal")).unwrap();
    fs::write(
        fix_mir_wp_only.root.join("theory/Anneal.lean"),
        b"prelude\nimport Trusted\nimport Anneal.MirWp\n",
    )
    .unwrap();
    fs::write(
        fix_mir_wp_only.root.join("theory/Anneal/MirWp.lean"),
        b"prelude\nimport Init.NotationExtra\nnamespace Anneal.MirWp\ndef marker : Nat := 0\nend Anneal.MirWp\n",
    )
    .unwrap();
    let err_mir_wp_only =
        fix_mir_wp_only.check_expected(Some(1), Some("audit"), Some(true)).unwrap_err();
    assert!(
        err_mir_wp_only.message.contains("missing required trusted module Trusted.MirAst"),
        "unexpected error: {err_mir_wp_only}"
    );

    // 4. With `require_mir_wp == false`, presence of `Trusted.MirSemantics`
    // alone triggers `verifyMirWpCoreTheorems` and rejects with exit code 1.
    let mut fix_sem_only = TempFixture::new(Some(HEADER));
    fs::create_dir_all(fix_sem_only.root.join("trusted/lean/Trusted")).unwrap();
    fs::write(
        fix_sem_only
            .root
            .join("trusted/lean/Trusted/MirSemantics.lean"),
        b"-- anneal-trust-tier: candidate:mir_semantics\nprelude\nimport Init.NotationExtra\nnamespace Trusted.MirSemantics\ndef placeholder : Nat := 0\nend Trusted.MirSemantics\n",
    )
    .unwrap();
    let err_sem_only = fix_sem_only.check_expected(Some(1), Some("audit"), Some(true)).unwrap_err();
    assert!(
        err_sem_only.message.contains("missing required trusted module Trusted.MirAst"),
        "unexpected error: {err_sem_only}"
    );

    // 5. With `require_mir_wp == false`, presence of `Trusted.MirAst` alone
    // triggers `verifyMirWpCoreTheorems` and rejects missing
    // `Trusted.MirSemantics`.
    let mut fix_ast_only = TempFixture::new(Some(HEADER));
    fs::create_dir_all(fix_ast_only.root.join("trusted/lean/Trusted")).unwrap();
    fs::write(
        fix_ast_only.root.join("trusted/lean/Trusted/MirAst.lean"),
        b"-- anneal-trust-tier: candidate:mir_ast\nprelude\nimport Init.NotationExtra\nnamespace Trusted.MirAst\ndef placeholder : Nat := 0\nend Trusted.MirAst\n",
    )
    .unwrap();
    let err_ast_only = fix_ast_only.check_expected(Some(1), Some("audit"), Some(true)).unwrap_err();
    assert!(
        err_ast_only.message.contains("missing required trusted module Trusted.MirSemantics"),
        "unexpected error: {err_ast_only}"
    );

    // 6. With `require_mir_wp == false`, `Trusted.MirAst` and
    // `Trusted.MirSemantics` without `Anneal.MirWp` are rejected in `"audit"`.
    let mut fix_no_wp = TempFixture::new(Some(HEADER));
    fs::create_dir_all(fix_no_wp.root.join("trusted/lean/Trusted")).unwrap();
    fs::write(
        fix_no_wp.root.join("trusted/lean/Trusted/MirAst.lean"),
        b"-- anneal-trust-tier: candidate:mir_ast\nprelude\nimport Init.NotationExtra\nnamespace Trusted.MirAst\ndef placeholder : Nat := 0\nend Trusted.MirAst\n",
    )
    .unwrap();
    fs::write(
        fix_no_wp.root.join("trusted/lean/Trusted/MirSemantics.lean"),
        b"-- anneal-trust-tier: candidate:mir_semantics\nprelude\nimport Init.NotationExtra\nimport Trusted.MirAst\nnamespace Trusted.MirSemantics\ndef placeholder : Nat := 0\nend Trusted.MirSemantics\n",
    )
    .unwrap();
    let err_no_wp = fix_no_wp.check_expected(Some(1), Some("audit"), Some(true)).unwrap_err();
    assert!(
        err_no_wp.message.contains("missing required theory module Anneal.MirWp"),
        "unexpected error: {err_no_wp}"
    );

    // 7. Missing decoupled `Anneal.MirWp.Canaries` is rejected fail-closed even
    // when `Anneal` and `Anneal.MirWp` are present and neither imports it.
    let mut missing_canaries = MirWpFixtureSpec::valid();
    missing_canaries.include_canaries_module = false;
    expect_mir_wp_audit_policy_err(
        &missing_canaries,
        "missing required theory module Anneal.MirWp.Canaries",
    );

    // 8. With `require_mir_wp == false`, presence of `Anneal.MirWp.Canaries`
    // alone triggers `verifyMirWpCoreTheorems` and rejects fail-closed.
    let mut fix_canaries_only = TempFixture::new(Some(HEADER));
    fs::create_dir_all(fix_canaries_only.root.join("theory/Anneal/MirWp")).unwrap();
    fs::write(
        fix_canaries_only.root.join("theory/Anneal.lean"),
        b"prelude\nimport Trusted\n",
    )
    .unwrap();
    fs::write(
        fix_canaries_only.root.join("theory/Anneal/MirWp/Canaries.lean"),
        b"prelude\nimport Init.NotationExtra\nnamespace Anneal.MirWp\ndef marker : Nat := 0\nend Anneal.MirWp\n",
    )
    .unwrap();
    let err_canaries_only =
        fix_canaries_only.check_expected(Some(1), Some("audit"), Some(true)).unwrap_err();
    assert!(
        err_canaries_only.message.contains("missing required trusted module Trusted.MirAst"),
        "unexpected error: {err_canaries_only}"
    );
}

/// Verifies every rejection branch of `requireClaimProof` (parameterized mode,
/// `argName? = some _`) in `TrustedBoundary.lean` (missing claim, missing
/// theorem, non-theorem proof, wrong-module proof, weakened/wrong-type proof,
/// non-definition claim, wrong-module claim, and claim bodies missing required
/// semantic constants) against a passing synthetic baseline.
#[test]
fn enforces_mir_wp_param_claim_proof_rules() {
    // Baseline: the unmutated synthetic fixture passes with default
    // `require_mir_wp == true`.
    let baseline = materialize_mir_wp(&MirWpFixtureSpec::valid());
    let mut checker = baseline.checker();
    let report = checker.run().unwrap();
    assert_eq!(report.get("replay"), Some(&json!(true)));

    // Missing `WpSoundnessClaim` from `Trusted.MirSemantics`.
    let mut missing_wp_claim = MirWpFixtureSpec::valid();
    missing_wp_claim.wp_soundness_claim = None;
    missing_wp_claim.wp_soundness_proof = None;
    expect_mir_wp_audit_policy_err(
        &missing_wp_claim,
        "missing required claim Trusted.MirSemantics.WpSoundnessClaim",
    );

    // Missing `wellFormed_and_spec_of_wp`.
    let mut missing_wp_thm = MirWpFixtureSpec::valid();
    missing_wp_thm.wp_soundness_proof = None;
    expect_mir_wp_audit_policy_err(
        &missing_wp_thm,
        "missing required theorem Anneal.MirWp.wellFormed_and_spec_of_wp",
    );

    // Missing `reaches_fault_and_exclusive_of_wpFault`.
    let mut missing_fault_thm = MirWpFixtureSpec::valid();
    missing_fault_thm.wp_fault_soundness_proof = None;
    expect_mir_wp_audit_policy_err(
        &missing_fault_thm,
        "missing required theorem Anneal.MirWp.reaches_fault_and_exclusive_of_wpFault",
    );

    // Non-theorem proof (`def` instead of `theorem`).
    let mut def_instead_of_thm = MirWpFixtureSpec::valid();
    def_instead_of_thm.wp_soundness_proof =
        Some("def wellFormed_and_spec_of_wp : Nat := 0".to_string());
    expect_mir_wp_audit_policy_err(
        &def_instead_of_thm,
        "expected Anneal.MirWp.wellFormed_and_spec_of_wp to be a theorem",
    );

    // Proof defined in `Anneal.Wp` instead of `Anneal.MirWp`.
    let mut wrong_proof_mod = MirWpFixtureSpec::valid();
    wrong_proof_mod.wp_soundness_proof = None;
    wrong_proof_mod.anneal_extra = "\
        namespace Anneal.MirWp\n\
        theorem wellFormed_and_spec_of_wp : \
            Trusted.MirSemantics.WpSoundnessClaim Anneal.MirWp.wpProg := \
          And.intro True.intro (And.intro True.intro True.intro)\n\
        end Anneal.MirWp"
        .to_string();
    expect_mir_wp_audit_policy_err(
        &wrong_proof_mod,
        "expected Anneal.MirWp.wellFormed_and_spec_of_wp to be defined in \
         Anneal.MirWp, found Anneal.Wp",
    );

    // Weakened / wrong-type proof (`True` instead of
    // `WpSoundnessClaim wpProg`).
    let mut weakened_wp_thm = MirWpFixtureSpec::valid();
    weakened_wp_thm.wp_soundness_proof =
        Some("theorem wellFormed_and_spec_of_wp : True := True.intro".to_string());
    expect_mir_wp_audit_policy_err(
        &weakened_wp_thm,
        "theorem Anneal.MirWp.wellFormed_and_spec_of_wp must prove \
         Trusted.MirSemantics.WpSoundnessClaim Anneal.MirWp.wpProg directly",
    );

    // Non-definition claim (`inductive` instead of `def`).
    let mut non_def_claim = MirWpFixtureSpec::valid();
    non_def_claim.wp_soundness_claim =
        Some("inductive WpSoundnessClaim (_f : Nat) : Prop where\n  | intro".to_string());
    non_def_claim.wp_soundness_proof = Some(
        "theorem wellFormed_and_spec_of_wp : \
         Trusted.MirSemantics.WpSoundnessClaim Anneal.MirWp.wpProg := \
         Trusted.MirSemantics.WpSoundnessClaim.intro"
            .to_string(),
    );
    expect_mir_wp_audit_policy_err(
        &non_def_claim,
        "expected Trusted.MirSemantics.WpSoundnessClaim to be a definition",
    );

    // Claim defined in `Trusted.MirAst` instead of `Trusted.MirSemantics`.
    let mut wrong_claim_mod = MirWpFixtureSpec::valid();
    wrong_claim_mod.wp_soundness_claim = None;
    wrong_claim_mod.mir_ast_extra = "\
        namespace Trusted.MirSemantics\n\
        def WpSoundnessClaim (_f : Nat) : Prop := True\n\
        end Trusted.MirSemantics"
        .to_string();
    wrong_claim_mod.wp_soundness_proof = Some(
        "theorem wellFormed_and_spec_of_wp : \
         Trusted.MirSemantics.WpSoundnessClaim Anneal.MirWp.wpProg := True.intro"
            .to_string(),
    );
    expect_mir_wp_audit_policy_err(
        &wrong_claim_mod,
        "expected Trusted.MirSemantics.WpSoundnessClaim to be defined in \
         Trusted.MirSemantics, found Trusted.MirAst",
    );

    // Claim body missing required `SatisfiesPost` reference
    // (`TrustedBoundary.lean` `requireClaimProof` `reqConsts` check).
    let mut missing_req_const = MirWpFixtureSpec::valid();
    missing_req_const.wp_soundness_claim =
        Some("def WpSoundnessClaim (_f : Nat) : Prop := And Diverges Behavior".to_string());
    missing_req_const.wp_soundness_proof = Some(
        "theorem wellFormed_and_spec_of_wp : \
         Trusted.MirSemantics.WpSoundnessClaim Anneal.MirWp.wpProg := \
         And.intro True.intro True.intro"
            .to_string(),
    );
    expect_mir_wp_audit_policy_err(
        &missing_req_const,
        "claim Trusted.MirSemantics.WpSoundnessClaim body must reference \
         Trusted.MirSemantics.SatisfiesPost",
    );

    // Claim body missing required `Diverges` reference (prevents silently
    // weakening the audited WP claim to partial correctness).
    let mut missing_diverges_const = MirWpFixtureSpec::valid();
    missing_diverges_const.wp_soundness_claim =
        Some("def WpSoundnessClaim (_f : Nat) : Prop := And SatisfiesPost Behavior".to_string());
    missing_diverges_const.wp_soundness_proof = Some(
        "theorem wellFormed_and_spec_of_wp : \
         Trusted.MirSemantics.WpSoundnessClaim Anneal.MirWp.wpProg := \
         And.intro True.intro True.intro"
            .to_string(),
    );
    expect_mir_wp_audit_policy_err(
        &missing_diverges_const,
        "claim Trusted.MirSemantics.WpSoundnessClaim body must reference \
         Trusted.MirSemantics.Diverges",
    );

    // Fault claim body missing required `Diverges` reference.
    let mut missing_fault_diverges_const = MirWpFixtureSpec::valid();
    missing_fault_diverges_const.wp_fault_soundness_claim = Some(
        "def WpFaultSoundnessClaim (_f : Nat) : Prop := And ReachesResult WellFormed".to_string(),
    );
    missing_fault_diverges_const.wp_fault_soundness_proof = Some(
        "theorem reaches_fault_and_exclusive_of_wpFault : \
         Trusted.MirSemantics.WpFaultSoundnessClaim Anneal.MirWp.wpFaultProg := \
         And.intro True.intro True.intro"
            .to_string(),
    );
    expect_mir_wp_audit_policy_err(
        &missing_fault_diverges_const,
        "claim Trusted.MirSemantics.WpFaultSoundnessClaim body must reference \
         Trusted.MirSemantics.Diverges",
    );

    // Fault claim body missing required `WellFormed` reference.
    let mut missing_fault_req_const = MirWpFixtureSpec::valid();
    missing_fault_req_const.wp_fault_soundness_claim = Some(
        "def WpFaultSoundnessClaim (_f : Nat) : Prop := And ReachesResult Diverges".to_string(),
    );
    missing_fault_req_const.wp_fault_soundness_proof = Some(
        "theorem reaches_fault_and_exclusive_of_wpFault : \
         Trusted.MirSemantics.WpFaultSoundnessClaim Anneal.MirWp.wpFaultProg := \
         And.intro True.intro True.intro"
            .to_string(),
    );
    expect_mir_wp_audit_policy_err(
        &missing_fault_req_const,
        "claim Trusted.MirSemantics.WpFaultSoundnessClaim body must reference \
         Trusted.MirSemantics.WellFormed",
    );

    // Missing Profile v2 `ExecSoundnessClaimV2` from `Trusted.MirSemantics`.
    let mut missing_v2_claim = MirWpFixtureSpec::valid();
    missing_v2_claim.exec_soundness_claim_v2 = None;
    missing_v2_claim.exec_soundness_proof_v2 = None;
    expect_mir_wp_audit_policy_err(
        &missing_v2_claim,
        "missing required claim Trusted.MirSemantics.ExecSoundnessClaimV2",
    );

    // Missing `wellFormed_and_spec_of_execV2`.
    let mut missing_v2_thm = MirWpFixtureSpec::valid();
    missing_v2_thm.exec_soundness_proof_v2 = None;
    expect_mir_wp_audit_policy_err(
        &missing_v2_thm,
        "missing required theorem Anneal.MirWp.wellFormed_and_spec_of_execV2",
    );

    // Weakened Profile v2 proof (`True` instead of
    // `ExecSoundnessClaimV2 execProgV2`).
    let mut weakened_v2_thm = MirWpFixtureSpec::valid();
    weakened_v2_thm.exec_soundness_proof_v2 =
        Some("theorem wellFormed_and_spec_of_execV2 : True := True.intro".to_string());
    expect_mir_wp_audit_policy_err(
        &weakened_v2_thm,
        "theorem Anneal.MirWp.wellFormed_and_spec_of_execV2 must prove \
         Trusted.MirSemantics.ExecSoundnessClaimV2 Anneal.MirWp.execProgV2 directly",
    );

    // Profile v2 claim bodies each missing one required semantic constant.
    for (body, dropped) in [
        ("And DivergesV2 BehaviorV2", "SatisfiesPostV2"),
        ("And SatisfiesPostV2 BehaviorV2", "DivergesV2"),
        ("And SatisfiesPostV2 DivergesV2", "BehaviorV2"),
    ] {
        let mut missing_v2_const = MirWpFixtureSpec::valid();
        missing_v2_const.exec_soundness_claim_v2 =
            Some(format!("def ExecSoundnessClaimV2 (_f : Nat) : Prop := {body}"));
        missing_v2_const.exec_soundness_proof_v2 = Some(
            "theorem wellFormed_and_spec_of_execV2 : \
             Trusted.MirSemantics.ExecSoundnessClaimV2 Anneal.MirWp.execProgV2 := \
             And.intro True.intro True.intro"
                .to_string(),
        );
        expect_mir_wp_audit_policy_err(
            &missing_v2_const,
            &format!(
                "claim Trusted.MirSemantics.ExecSoundnessClaimV2 body must reference \
                 Trusted.MirSemantics.{dropped}"
            ),
        );
    }

    // Missing Profile v2 `SafeContractSoundnessClaimV2`.
    let mut missing_sc_claim = MirWpFixtureSpec::valid();
    missing_sc_claim.safe_contract_soundness_claim_v2 = None;
    missing_sc_claim.safe_contract_soundness_proof_v2 = None;
    expect_mir_wp_audit_policy_err(
        &missing_sc_claim,
        "missing required claim Trusted.MirSemantics.SafeContractSoundnessClaimV2",
    );

    // Missing `safeContract_soundness_of_execV2`.
    let mut missing_sc_thm = MirWpFixtureSpec::valid();
    missing_sc_thm.safe_contract_soundness_proof_v2 = None;
    expect_mir_wp_audit_policy_err(
        &missing_sc_thm,
        "missing required theorem Anneal.MirWp.safeContract_soundness_of_execV2",
    );

    // `SafeContractSoundnessClaimV2` body missing one required constant.
    let mut missing_sc_const = MirWpFixtureSpec::valid();
    missing_sc_const.safe_contract_soundness_claim_v2 = Some(
        "def SafeContractSoundnessClaimV2 (_f : Nat) : Prop := \
         And EffectMaskV2 (And SafeContractV2 (And SafeContractV2.post \
         (And SatisfiesSafeContractV2 BodySatisfiesSafeContractV2)))"
            .to_string(),
    );
    missing_sc_const.safe_contract_soundness_proof_v2 = Some(
        "theorem safeContract_soundness_of_execV2 : \
         Trusted.MirSemantics.SafeContractSoundnessClaimV2 Anneal.MirWp.execProgV2 := \
         And.intro True.intro (And.intro True.intro (And.intro True.intro \
         (And.intro True.intro True.intro)))"
            .to_string(),
    );
    expect_mir_wp_audit_policy_err(
        &missing_sc_const,
        "claim Trusted.MirSemantics.SafeContractSoundnessClaimV2 body must reference \
         Trusted.MirSemantics.EffectMaskV2.noAbort",
    );
}

/// Default `Checker::new` (`require_mir_wp == true`) rejects Pass 1 fail-closed
/// even if *every* MIR and PureLift module (`Trusted.MirAst`,
/// `Trusted.MirSemantics`, `Anneal.MirWp`, `Anneal.PureLift`) is deleted at
/// once, leaving only `Trusted.lean`.
#[test]
fn default_checker_rejects_complete_mir_wp_deletion() {
    let fix = TempFixture::new(None);
    let mut checker = fix.checker();
    let err = checker.run().unwrap_err();
    assert_eq!(err.code, 1, "unexpected code: {err}");
    assert_eq!(err.phase, "audit", "unexpected phase: {err}");
    assert!(
        err.message.contains("missing required trusted module Trusted.MirAst"),
        "unexpected error: {err}"
    );
}

/// Ensures Pass 1 `anneal-audit` discovers, compiles, and fails closed on
/// policy violations in decoupled `*Canaries.lean` modules even when neither
/// `Anneal.lean` nor any runtime umbrella imports them.
#[test]
fn rejects_decoupled_unimported_canary_module_violations() {
    // 0. Positive control: a clean standalone unimported canary module is
    // discovered, compiled, audited, and recorded in the audit graph.
    let fix_ok = materialize_mir_wp(&MirWpFixtureSpec::valid());
    fs::create_dir_all(fix_ok.root.join("theory/Anneal/Subsys")).unwrap();
    fs::write(
        fix_ok.root.join("theory/Anneal/Subsys/Canaries.lean"),
        b"prelude\nimport Init.NotationExtra\ntheorem unimported_ok : True := True.intro\n",
    )
    .unwrap();
    let mut checker_ok = fix_ok.checker();
    let report = checker_ok.run().expect("clean decoupled canary must pass");
    assert!(
        report["graph"]
            .as_object()
            .expect("audit report graph object")
            .contains_key("Anneal.Subsys.Canaries"),
        "clean decoupled canary must appear in Pass-1 audit graph"
    );

    // 1. Standalone unimported canary with forbidden `sorry` syntax fails
    // preflight before Lean compilation.
    let fix_sorry = materialize_mir_wp(&MirWpFixtureSpec::valid());
    fs::create_dir_all(fix_sorry.root.join("theory/Anneal/Subsys")).unwrap();
    fs::write(
        fix_sorry.root.join("theory/Anneal/Subsys/Canaries.lean"),
        b"prelude\nimport Init.NotationExtra\ntheorem unimported_bad : False := by sorry\n",
    )
    .unwrap();
    let mut checker_sorry = fix_sorry.checker();
    let err_sorry = checker_sorry.run().unwrap_err();
    assert_eq!(err_sorry.code, 1, "expected policy exit 1: {err_sorry}");
    assert_eq!(err_sorry.phase, "preflight", "expected preflight rejection: {err_sorry}");
    assert!(
        !checker_sorry.execution_began(),
        "preflight must fail before compilation: {err_sorry}"
    );
    assert!(
        err_sorry.message.contains("tacticSorry"),
        "expected diagnostic to cite disallowed tacticSorry syntax: {err_sorry}"
    );

    // 2. Standalone unimported canary using `sorryAx` passes preflight and
    // fails closed during compilation (`-DwarningAsError=true`).
    let fix_sorry_ax = materialize_mir_wp(&MirWpFixtureSpec::valid());
    fs::create_dir_all(fix_sorry_ax.root.join("theory/Anneal/Subsys")).unwrap();
    fs::write(
        fix_sorry_ax.root.join("theory/Anneal/Subsys/Canaries.lean"),
        b"prelude\nimport Init.NotationExtra\n\
          theorem unimported_sorry_ax : False := sorryAx False true\n",
    )
    .unwrap();
    let mut checker_sorry_ax = fix_sorry_ax.checker();
    let err_sorry_ax = checker_sorry_ax.run().unwrap_err();
    assert_eq!(err_sorry_ax.code, 2, "expected compile exit 2: {err_sorry_ax}");
    assert_eq!(
        err_sorry_ax.phase, "compile-Anneal.Subsys.Canaries",
        "expected compilation of unimported canary: {err_sorry_ax}"
    );
    assert!(checker_sorry_ax.execution_began(), "expected compilation to run: {err_sorry_ax}");
    assert!(
        err_sorry_ax.message.contains("declaration uses `sorry`"),
        "expected Lean sorry diagnostic: {err_sorry_ax}"
    );

    // 3. Even if a standalone unimported canary `.olean` is compiled without
    // `-DwarningAsError=true`, Phase-2 `"audit"` independently rejects
    // `sorryAx`.
    let stage = checker_ok.stage().to_path_buf();
    let src = stage.join("src/decoupled-canary-audit");
    let theory_lib = stage.join("theory-lib");
    compile_forged_module(
        &mut checker_ok,
        &src,
        &theory_lib,
        &[],
        "Anneal.Subsys.Canaries",
        "prelude\nimport Init.NotationExtra\n\
         theorem unimported_sorry_ax : False := sorryAx False true\n",
    );
    let err_audit = checker_ok
        .inspect(InspectorRequest::Audit {
            trusted: vec![
                "Trusted".to_string(),
                "Trusted.MirAst".to_string(),
                "Trusted.MirSemantics".to_string(),
            ],
            theory: vec![
                "Anneal.Wp".to_string(),
                "Anneal.MirWp".to_string(),
                "Anneal.MirWp.Canaries".to_string(),
                "Anneal.Subsys.Canaries".to_string(),
            ],
            module_tiers: BTreeMap::from([
                ("Trusted".to_string(), TrustTier::Vetted),
                ("Trusted.MirAst".to_string(), TrustTier::Candidate(CandidateFeature::MirAst)),
                (
                    "Trusted.MirSemantics".to_string(),
                    TrustTier::Candidate(CandidateFeature::MirSemantics),
                ),
            ]),
        })
        .unwrap_err();
    assert_eq!(err_audit.code, 1, "expected policy exit 1: {err_audit}");
    assert_eq!(err_audit.phase, "audit", "expected Phase-2 audit rejection: {err_audit}");
    assert!(
        err_audit.message.contains("sorryAx"),
        "expected diagnostic to cite disallowed axiom sorryAx: {err_audit}"
    );
}

#[path = "pass1_mir_wp_gates/canary_claims.rs"]
mod canary_claims;
