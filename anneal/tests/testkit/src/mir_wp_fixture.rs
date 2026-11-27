// Copyright 2026 The Fuchsia Authors
//
// Licensed under a BSD-style license <LICENSE-BSD>, Apache License, Version 2.0
// <LICENSE-APACHE or https://www.apache.org/licenses/LICENSE-2.0>, or the MIT
// license <LICENSE-MIT or https://opensource.org/licenses/MIT>, at your option.
// This file may not be copied, modified, or distributed except according to
// those terms.

//! Canonical synthetic `Trusted.MirAst` / `Trusted.MirSemantics` /
//! `Anneal.MirWp` / `Anneal.MirWp.Canaries` fixture matching
//! `anneal/trusted/audit/TrustedBoundary.lean`'s `verifyMirWpCoreTheorems`.
//!
//! Centralizes the synthetic canary table and module renderer so negative
//! `boundary_audit` tests can mutate a single admission check in isolation
//! without duplicating 25+ canary declarations across test files.

use std::{
    collections::BTreeMap,
    path::{Path, PathBuf},
};

use crate::{
    TestResult,
    audit_fixture::{DEFAULT_VETTED_HEADER, LeanAuditFixture, OleanCachePolicy},
};

/// One required canary pair enforced by `verifyMirWpCoreTheorems`.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub struct SyntheticCanary {
    /// Claim name under `Trusted.MirSemantics`.
    pub claim: &'static str,
    /// Proof theorem name under `Anneal.MirWp` (defined in
    /// `Anneal.MirWp.Canaries`).
    pub proof: &'static str,
    /// Minimal `Prop` body referencing every required constant for `claim`.
    pub body: &'static str,
    /// Minimal Lean proof term witnessing `body`.
    pub proof_term: &'static str,
}

/// Core WP and Profile v2 soundness claims `(claim_name, param, proof_name)`
/// enforced by `verifyMirWpCoreTheorems`.
pub const CORE_WP_CLAIMS: &[(&str, &str, &str)] = &[
    ("WpSoundnessClaim", "wpProg", "wellFormed_and_spec_of_wp"),
    ("WpFaultSoundnessClaim", "wpFaultProg", "reaches_fault_and_exclusive_of_wpFault"),
    ("ExecSoundnessClaimV2", "execProgV2", "wellFormed_and_spec_of_execV2"),
    ("SafeContractSoundnessClaimV2", "execProgV2", "safeContract_soundness_of_execV2"),
];

/// Required public aliases `(alias_under_Trusted, target_under_MirSemantics)`
/// enforced by `verifyMirWpCoreTheorems`.
pub const PUBLIC_MIR_ALIASES: &[(&str, &str)] = &[
    ("Crate", "Crate"),
    ("CrateTheorem", "CrateTheorem"),
    ("UnitTheorem", "UnitTheorem"),
    ("CrateV2", "CrateV2"),
    ("CrateTheoremV2", "CrateTheoremV2"),
    ("UnitTheoremV2", "UnitTheoremV2"),
];

/// Complete synthetic canary catalog matching `verifyMirWpCoreTheorems` in
/// `anneal/trusted/audit/TrustedBoundary.lean`.
pub const SYNTHETIC_CANARIES: &[SyntheticCanary] = &[
    SyntheticCanary {
        claim: "CanaryPositiveAddAnnealClaim",
        proof: "canary_positive_add_anneal",
        body: "PositiveCanaryClaim",
        proof_term: "True.intro",
    },
    SyntheticCanary {
        claim: "CanaryPositiveEmptyUnitFnClaim",
        proof: "canary_positive_empty_unit_fn",
        body: "PositiveCanaryClaim",
        proof_term: "True.intro",
    },
    SyntheticCanary {
        claim: "CanaryPositiveStmtsAndCfAnnealClaim",
        proof: "canary_positive_stmts_and_cf_anneal",
        body: "PositiveCanaryClaim",
        proof_term: "True.intro",
    },
    SyntheticCanary {
        claim: "CanaryPositiveUnopAnnealClaim",
        proof: "canary_positive_unop_anneal",
        body: "PositiveCanaryClaim",
        proof_term: "True.intro",
    },
    SyntheticCanary {
        claim: "CanaryPositiveAllBinopsAnnealClaim",
        proof: "canary_positive_all_binops_anneal",
        body: "PositiveCanaryClaim",
        proof_term: "True.intro",
    },
    SyntheticCanary {
        claim: "CanaryPositiveAllIntWidthsAnnealClaim",
        proof: "canary_positive_all_int_widths_anneal",
        body: "IntWidthBoundaryCanary",
        proof_term: "True.intro",
    },
    SyntheticCanary {
        claim: "CanaryNegativeUbDivZeroAnnealClaim",
        proof: "canary_negative_ub_div_zero_anneal",
        body: "NegativeCanaryClaim",
        proof_term: "True.intro",
    },
    SyntheticCanary {
        claim: "CanaryNegativeUbSignedRemOverflowI8Claim",
        proof: "canary_negative_ub_signed_rem_overflow_i8",
        body: "NegativeCanaryClaim",
        proof_term: "True.intro",
    },
    SyntheticCanary {
        claim: "CanaryNegativeUnsupportedAnnealClaim",
        proof: "canary_negative_unsupported_anneal",
        body: "NegativeCanaryClaim",
        proof_term: "True.intro",
    },
    SyntheticCanary {
        claim: "CanaryNegativeUbAddUncheckedOverflowU32Claim",
        proof: "canary_negative_ub_add_unchecked_overflow_u32",
        body: "And NegativeCanaryClaim PositiveCanaryClaim",
        proof_term: "And.intro True.intro True.intro",
    },
    SyntheticCanary {
        claim: "CanaryNegativeUbShiftUncheckedAtBitwidthAnnealClaim",
        proof: "canary_negative_ub_shift_unchecked_at_bitwidth_anneal",
        body: "NegativeCanaryClaim",
        proof_term: "True.intro",
    },
    SyntheticCanary {
        claim: "CanaryNegativeUbStorageDeadReadAnnealClaim",
        proof: "canary_negative_ub_storage_dead_read_anneal",
        body: "NegativeCanaryClaim",
        proof_term: "True.intro",
    },
    SyntheticCanary {
        claim: "CanaryNegativeUbStorageDeadReturnPlaceAnnealClaim",
        proof: "canary_negative_ub_storage_dead_return_place_anneal",
        body: "NegativeCanaryClaim",
        proof_term: "True.intro",
    },
    SyntheticCanary {
        claim: "CanaryNegativeUbUnreachableAnnealClaim",
        proof: "canary_negative_ub_unreachable_anneal",
        body: "NegativeCanaryClaim",
        proof_term: "True.intro",
    },
    SyntheticCanary {
        claim: "CanaryNegativeUnsupportedUnsignedNegAnnealClaim",
        proof: "canary_negative_unsupported_unsigned_neg_anneal",
        body: "NegativeCanaryClaim",
        proof_term: "True.intro",
    },
    SyntheticCanary {
        claim: "CanaryPositiveEnumExplicitReprAnnealClaim",
        proof: "canary_positive_enum_explicit_repr_anneal",
        body: "PositiveCanaryClaim",
        proof_term: "True.intro",
    },
    SyntheticCanary {
        claim: "CanaryPositiveZstSingleEnumAnnealClaim",
        proof: "canary_positive_zst_single_enum_anneal",
        body: "PositiveCanaryClaim",
        proof_term: "True.intro",
    },
    SyntheticCanary {
        claim: "CanaryNegativeUbEnumInvalidTagAndUninitAnnealClaim",
        proof: "canary_negative_ub_enum_invalid_tag_and_uninit_anneal",
        body: "NegativeCanaryClaim",
        proof_term: "True.intro",
    },
    SyntheticCanary {
        claim: "CanaryCrateAndBodyVerifiedAnnealClaim",
        proof: "canary_crate_and_body_verified_anneal",
        body: "And CrateTheorem (And UnitTheorem BodyVerified)",
        proof_term: "And.intro True.intro (And.intro True.intro True.intro)",
    },
    SyntheticCanary {
        claim: "CanaryMemoryLifecycleAnnealClaim",
        proof: "canary_memory_lifecycle_anneal",
        body: "And PositiveCanaryClaim (And initState (And evalStep \
               (And forceAllocation readBytes)))",
        proof_term: "And.intro True.intro (And.intro True.intro \
                     (And.intro True.intro (And.intro True.intro True.intro)))",
    },
    SyntheticCanary {
        claim: "CanaryPositiveCharAndCmpAnnealClaim",
        proof: "canary_positive_char_and_cmp_anneal",
        body: "And PositiveCanaryClaim (And mkBinOpProg \
               (And Trusted.MirAst.BinOp.cmp (And Trusted.MirAst.MirTy.char \
               (And charVal (And mkCmpDiscriminantProg progCharSwitch)))))",
        proof_term: "And.intro True.intro (And.intro True.intro \
                     (And.intro True.intro (And.intro True.intro \
                     (And.intro True.intro (And.intro True.intro True.intro)))))",
    },
    SyntheticCanary {
        claim: "CanaryNegativeCharAndCmpAnnealClaim",
        proof: "canary_negative_char_and_cmp_anneal",
        body: "And NegativeCanaryClaim (And progInvalidCharConstUb \
               (And progInvalidCharSwitchCaseUb (And mkBinOpProg \
               (And Trusted.MirAst.BinOp.cmp mkUnOpProg))))",
        proof_term: "And.intro True.intro (And.intro True.intro \
                     (And.intro True.intro (And.intro True.intro \
                     (And.intro True.intro True.intro))))",
    },
    SyntheticCanary {
        claim: "CanaryPositiveOverflowOpsAnnealClaim",
        proof: "canary_positive_overflow_ops_anneal",
        body: "And PositiveCanaryClaim (And mkBinOpProg (And overflowPairTy \
               (And Trusted.MirAst.BinOp.addWithOverflow \
               (And Trusted.MirAst.BinOp.subWithOverflow \
               Trusted.MirAst.BinOp.mulWithOverflow))))",
        proof_term: "And.intro True.intro (And.intro True.intro \
                     (And.intro True.intro (And.intro True.intro \
                     (And.intro True.intro True.intro))))",
    },
    SyntheticCanary {
        claim: "CanaryPositiveIntToIntCastAnnealClaim",
        proof: "canary_positive_int_to_int_cast_anneal",
        body: "And PositiveCanaryClaim (And mkIntToIntCastProg \
               (And Trusted.MirAst.MirTy.char charVal))",
        proof_term: "And.intro True.intro (And.intro True.intro \
                     (And.intro True.intro True.intro))",
    },
    SyntheticCanary {
        claim: "CanaryNegativeIntToIntCastAnnealClaim",
        proof: "canary_negative_int_to_int_cast_anneal",
        body: "And NegativeCanaryClaim (And mkIntToIntCastProg \
               (And Trusted.MirAst.MirTy.char progCastUninitSourceUb))",
        proof_term: "And.intro True.intro (And.intro True.intro \
                     (And.intro True.intro True.intro))",
    },
    SyntheticCanary {
        claim: "CanaryContractAnnealClaim",
        proof: "canary_contract_anneal",
        body: "And EffectMask.totalNormal (And EffectMask.partialAnyExit \
               (And FnContract (And decodeScalar (And scalarAsInt \
               (And BodyContractSatisfied (And ContractPreInhabited \
               (And ContractSignature (And bodyMatchesContractSignature \
               (And ContractEntry (And ContractSpecs \
               (And contractEntryRbLookup UnitTheorem)))))))))))",
        proof_term: "And.intro True.intro (And.intro True.intro \
                     (And.intro True.intro (And.intro True.intro \
                     (And.intro True.intro (And.intro True.intro \
                     (And.intro True.intro (And.intro True.intro \
                     (And.intro True.intro (And.intro True.intro \
                     (And.intro True.intro (And.intro True.intro \
                     True.intro)))))))))))",
    },
];

/// Configurable synthetic fixture containing minimal `Trusted.MirAst`,
/// `Trusted.MirSemantics`, `Anneal.Wp` (or a configured `Anneal.*` umbrella),
/// `Anneal.MirWp`, and decoupled `Anneal.MirWp.Canaries` modules that pass
/// `verifyMirWpCoreTheorems` out of the box. Individual negative tests can
/// override or omit any single claim, proof, or alias in isolation.
#[derive(Clone, Debug)]
pub struct MirWpFixtureSpec {
    pub mir_ast_extra: String,
    pub wp_soundness_claim: Option<String>,
    pub wp_fault_soundness_claim: Option<String>,
    pub exec_soundness_claim_v2: Option<String>,
    pub safe_contract_soundness_claim_v2: Option<String>,
    pub canary_claim_overrides: BTreeMap<String, Option<String>>,
    pub public_alias_overrides: BTreeMap<String, Option<String>>,
    /// Dotted Lean module name of the synthetic theory umbrella file under
    /// `theory/` (defaults to `"Anneal.Wp"` -> `theory/Anneal/Wp.lean`; e.g.,
    /// `"Anneal"` -> `theory/Anneal.lean` for synthetic legacy fixtures).
    pub theory_umbrella_module: String,
    pub anneal_extra: String,
    pub wp_soundness_proof: Option<String>,
    pub wp_fault_soundness_proof: Option<String>,
    pub exec_soundness_proof_v2: Option<String>,
    pub safe_contract_soundness_proof_v2: Option<String>,
    pub canary_proof_overrides: BTreeMap<String, Option<String>>,
    pub mir_wp_extra: String,
    pub include_canaries_module: bool,
    pub canaries_extra: String,
    /// When `true`, render Lean 4 `module` / `public import` /
    /// `@[expose] public section` headers matching
    /// `fixtures/audit-positive.lean`.
    pub module_syntax: bool,
}

fn is_valid_lean_ident_segment(segment: &str) -> bool {
    let mut chars = segment.chars();
    let Some(first) = chars.next() else {
        return false;
    };
    (first.is_ascii_alphabetic() || first == '_')
        && chars.all(|ch| ch.is_ascii_alphanumeric() || ch == '_')
}

impl MirWpFixtureSpec {
    /// Construct a valid baseline spec passing `verifyMirWpCoreTheorems`.
    pub fn valid() -> Self {
        Self {
            mir_ast_extra: String::new(),
            wp_soundness_claim: Some(
                "def WpSoundnessClaim (_f : Nat) : Prop := \
                 And SatisfiesPost (And Diverges Behavior)"
                    .to_string(),
            ),
            wp_fault_soundness_claim: Some(
                "def WpFaultSoundnessClaim (_f : Nat) : Prop := \
                 And ReachesResult (And Diverges WellFormed)"
                    .to_string(),
            ),
            exec_soundness_claim_v2: Some(
                "def ExecSoundnessClaimV2 (_f : Nat) : Prop := \
                 And SatisfiesPostV2 (And DivergesV2 BehaviorV2)"
                    .to_string(),
            ),
            safe_contract_soundness_claim_v2: Some(
                "def SafeContractSoundnessClaimV2 (_f : Nat) : Prop := \
                 And EffectMaskV2 (And EffectMaskV2.noAbort \
                 (And SafeContractV2 (And SafeContractV2.post \
                 (And SatisfiesSafeContractV2 BodySatisfiesSafeContractV2))))"
                    .to_string(),
            ),
            canary_claim_overrides: BTreeMap::new(),
            public_alias_overrides: BTreeMap::new(),
            theory_umbrella_module: "Anneal.Wp".to_string(),
            anneal_extra: String::new(),
            wp_soundness_proof: Some(
                "theorem wellFormed_and_spec_of_wp : \
                 Trusted.MirSemantics.WpSoundnessClaim Anneal.MirWp.wpProg := \
                 And.intro True.intro (And.intro True.intro True.intro)"
                    .to_string(),
            ),
            wp_fault_soundness_proof: Some(
                "theorem reaches_fault_and_exclusive_of_wpFault : \
                 Trusted.MirSemantics.WpFaultSoundnessClaim \
                 Anneal.MirWp.wpFaultProg := \
                 And.intro True.intro (And.intro True.intro True.intro)"
                    .to_string(),
            ),
            exec_soundness_proof_v2: Some(
                "theorem wellFormed_and_spec_of_execV2 : \
                 Trusted.MirSemantics.ExecSoundnessClaimV2 \
                 Anneal.MirWp.execProgV2 := \
                 And.intro True.intro (And.intro True.intro True.intro)"
                    .to_string(),
            ),
            safe_contract_soundness_proof_v2: Some(
                "theorem safeContract_soundness_of_execV2 : \
                 Trusted.MirSemantics.SafeContractSoundnessClaimV2 \
                 Anneal.MirWp.execProgV2 := \
                 And.intro True.intro (And.intro True.intro \
                 (And.intro True.intro (And.intro True.intro \
                 (And.intro True.intro True.intro))))"
                    .to_string(),
            ),
            canary_proof_overrides: BTreeMap::new(),
            mir_wp_extra: String::new(),
            include_canaries_module: true,
            canaries_extra: String::new(),
            module_syntax: false,
        }
    }

    /// Construct a valid baseline spec rendered with Lean 4 `module` /
    /// `public import` / `@[expose] public section` headers.
    pub fn valid_module_style() -> Self {
        let mut spec = Self::valid();
        spec.module_syntax = true;
        spec
    }

    /// Render `trusted/lean/Trusted/MirAst.lean`.
    pub fn render_mir_ast(&self) -> String {
        let header = if self.module_syntax {
            "-- anneal-trust-tier: candidate:mir_ast\n\
             module\n\
             prelude\n\
             public import Init.NotationExtra\n\
             @[expose] public section\n"
        } else {
            "-- anneal-trust-tier: candidate:mir_ast\n\
             prelude\n\
             import Init.NotationExtra\n"
        };
        let placeholder = if self.module_syntax { "" } else { "def placeholder : Nat := 0\n" };
        let footer = if self.module_syntax { "end\n" } else { "" };
        format!(
            "{header}\
             namespace Trusted.MirAst\n\
             {placeholder}\
             def BinOp.cmp : Prop := True\n\
             def BinOp.addWithOverflow : Prop := True\n\
             def BinOp.subWithOverflow : Prop := True\n\
             def BinOp.mulWithOverflow : Prop := True\n\
             def MirTy.char : Prop := True\n\
             end Trusted.MirAst\n\
             {}\n\
             {footer}",
            self.mir_ast_extra
        )
    }

    /// Render `trusted/lean/Trusted/MirSemantics.lean`.
    pub fn render_mir_semantics(&self) -> String {
        let mut sem = String::from(if self.module_syntax {
            "-- anneal-trust-tier: candidate:mir_semantics\n\
             module\n\
             prelude\n\
             public import Init.NotationExtra\n\
             public import Trusted.MirAst\n\
             @[expose] public section\n"
        } else {
            "-- anneal-trust-tier: candidate:mir_semantics\n\
             prelude\n\
             import Init.NotationExtra\n\
             import Trusted.MirAst\n"
        });
        sem.push_str(
            "namespace Trusted.MirSemantics\n\
             def SatisfiesPost : Prop := True\n\
             def Diverges : Prop := True\n\
             def Behavior : Prop := True\n\
             def ReachesResult : Prop := True\n\
             def WellFormed : Prop := True\n\
             def SatisfiesPostV2 : Prop := True\n\
             def DivergesV2 : Prop := True\n\
             def BehaviorV2 : Prop := True\n\
             def EffectMaskV2 : Prop := True\n\
             def EffectMaskV2.noAbort : Prop := True\n\
             def SafeContractV2 : Prop := True\n\
             def SafeContractV2.post : Prop := True\n\
             def SatisfiesSafeContractV2 : Prop := True\n\
             def BodySatisfiesSafeContractV2 : Prop := True\n\
             def PositiveCanaryClaim : Prop := True\n\
             def NegativeCanaryClaim : Prop := True\n\
             def IntWidthBoundaryCanary : Prop := True\n\
             def Crate : Prop := True\n\
             def CrateTheorem : Prop := True\n\
             def UnitTheorem : Prop := True\n\
             def CrateV2 : Prop := True\n\
             def CrateTheoremV2 : Prop := True\n\
             def UnitTheoremV2 : Prop := True\n\
             def BodyVerified : Prop := True\n\
             def initState : Prop := True\n\
             def evalStep : Prop := True\n\
             def forceAllocation : Prop := True\n\
             def readBytes : Prop := True\n\
             def mkBinOpProg : Prop := True\n\
             def mkUnOpProg : Prop := True\n\
             def charVal : Prop := True\n\
             def mkCmpDiscriminantProg : Prop := True\n\
             def progCharSwitch : Prop := True\n\
             def progInvalidCharConstUb : Prop := True\n\
             def progInvalidCharSwitchCaseUb : Prop := True\n\
             def overflowPairTy : Prop := True\n\
             def mkIntToIntCastProg : Prop := True\n\
             def progCastUninitSourceUb : Prop := True\n\
             def EffectMask.totalNormal : Prop := True\n\
             def EffectMask.partialAnyExit : Prop := True\n\
             def FnContract : Prop := True\n\
             def decodeScalar : Prop := True\n\
             def scalarAsInt : Prop := True\n\
             def BodyContractSatisfied : Prop := True\n\
             def ContractPreInhabited : Prop := True\n\
             def ContractSignature : Prop := True\n\
             def bodyMatchesContractSignature : Prop := True\n\
             def ContractEntry : Prop := True\n\
             def ContractSpecs : Prop := True\n\
             def contractEntryRbLookup : Prop := True\n",
        );
        if let Some(decl) = &self.wp_soundness_claim {
            sem.push_str(decl);
            sem.push('\n');
        }
        if let Some(decl) = &self.wp_fault_soundness_claim {
            sem.push_str(decl);
            sem.push('\n');
        }
        if let Some(decl) = &self.exec_soundness_claim_v2 {
            sem.push_str(decl);
            sem.push('\n');
        }
        if let Some(decl) = &self.safe_contract_soundness_claim_v2 {
            sem.push_str(decl);
            sem.push('\n');
        }
        for canary in SYNTHETIC_CANARIES {
            match self.canary_claim_overrides.get(canary.claim) {
                Some(None) => {}
                Some(Some(custom)) => {
                    sem.push_str(custom);
                    sem.push('\n');
                }
                None => {
                    sem.push_str(&format!("def {} : Prop := {}\n", canary.claim, canary.body));
                }
            }
        }
        sem.push_str("end Trusted.MirSemantics\n");
        sem.push_str("namespace Trusted\n");
        for (alias_name, default_decl) in [
            ("Crate", "abbrev Crate := Trusted.MirSemantics.Crate"),
            (
                "CrateTheorem",
                "noncomputable abbrev CrateTheorem := \
                 Trusted.MirSemantics.CrateTheorem",
            ),
            (
                "UnitTheorem",
                "noncomputable abbrev UnitTheorem := \
                 Trusted.MirSemantics.UnitTheorem",
            ),
            ("CrateV2", "abbrev CrateV2 := Trusted.MirSemantics.CrateV2"),
            (
                "CrateTheoremV2",
                "noncomputable abbrev CrateTheoremV2 := \
                 Trusted.MirSemantics.CrateTheoremV2",
            ),
            (
                "UnitTheoremV2",
                "noncomputable abbrev UnitTheoremV2 := \
                 Trusted.MirSemantics.UnitTheoremV2",
            ),
        ] {
            match self.public_alias_overrides.get(alias_name) {
                Some(None) => {}
                Some(Some(custom)) => {
                    sem.push_str(custom);
                    sem.push('\n');
                }
                None => {
                    sem.push_str(default_decl);
                    sem.push('\n');
                }
            }
        }
        sem.push_str("end Trusted\n");
        if self.module_syntax {
            sem.push_str("end\n");
        }
        sem
    }

    /// Render `theory/Anneal/MirWp.lean`.
    pub fn render_mir_wp(&self) -> String {
        let mut wp = String::from(if self.module_syntax {
            "module\n\
             prelude\n\
             public import Init.NotationExtra\n\
             public import Trusted\n\
             public import Trusted.MirAst\n\
             public import Trusted.MirSemantics\n\
             public section\n\
             namespace Anneal.MirWp\n\
             @[expose] def wpProg : Nat := 0\n\
             @[expose] def wpFaultProg : Nat := 0\n\
             @[expose] def execProgV2 : Nat := 0\n"
        } else {
            "prelude\n\
             import Init.NotationExtra\n\
             import Trusted\n\
             import Trusted.MirAst\n\
             import Trusted.MirSemantics\n\
             namespace Anneal.MirWp\n\
             def wpProg : Nat := 0\n\
             def wpFaultProg : Nat := 0\n\
             def execProgV2 : Nat := 0\n"
        });
        if let Some(decl) = &self.wp_soundness_proof {
            wp.push_str(decl);
            wp.push('\n');
        }
        if let Some(decl) = &self.wp_fault_soundness_proof {
            wp.push_str(decl);
            wp.push('\n');
        }
        if let Some(decl) = &self.exec_soundness_proof_v2 {
            wp.push_str(decl);
            wp.push('\n');
        }
        if let Some(decl) = &self.safe_contract_soundness_proof_v2 {
            wp.push_str(decl);
            wp.push('\n');
        }
        wp.push_str("end Anneal.MirWp\n");
        if !self.mir_wp_extra.is_empty() {
            wp.push_str(&self.mir_wp_extra);
            wp.push('\n');
        }
        if self.module_syntax {
            wp.push_str("end\n");
        }
        wp
    }

    /// Render `theory/Anneal/MirWp/Canaries.lean` when
    /// `self.include_canaries_module` is `true`.
    pub fn render_canaries(&self) -> Option<String> {
        if !self.include_canaries_module {
            return None;
        }
        let mut canaries = String::from(if self.module_syntax {
            "module\n\
             prelude\n\
             public import Init.NotationExtra\n\
             public import Trusted\n\
             public import Trusted.MirAst\n\
             public import Trusted.MirSemantics\n\
             public section\n\
             namespace Anneal.MirWp\n"
        } else {
            "prelude\n\
             import Init.NotationExtra\n\
             import Trusted\n\
             import Trusted.MirAst\n\
             import Trusted.MirSemantics\n\
             namespace Anneal.MirWp\n"
        });
        for canary in SYNTHETIC_CANARIES {
            match self.canary_proof_overrides.get(canary.proof) {
                Some(None) => {}
                Some(Some(custom)) => {
                    canaries.push_str(custom);
                    canaries.push('\n');
                }
                None => {
                    canaries.push_str(&format!(
                        "theorem {} : Trusted.MirSemantics.{} := {}\n",
                        canary.proof, canary.claim, canary.proof_term
                    ));
                }
            }
        }
        canaries.push_str("end Anneal.MirWp\n");
        if !self.canaries_extra.is_empty() {
            canaries.push_str(&self.canaries_extra);
            canaries.push('\n');
        }
        if self.module_syntax {
            canaries.push_str("end\n");
        }
        Some(canaries)
    }

    /// Validate `self.theory_umbrella_module` as `"Anneal"` or an
    /// `"Anneal.<Sub>..."` dotted Lean module name and return its relative path
    /// under an Anneal root (e.g., `"theory/Anneal.lean"` or
    /// `"theory/Anneal/Wp.lean"`).
    pub fn theory_umbrella_rel_path(&self) -> TestResult<PathBuf> {
        let module = self.theory_umbrella_module.as_str();
        let segments: Vec<&str> = module.split('.').collect();
        if segments.first().copied() != Some("Anneal")
            || !segments.iter().copied().all(is_valid_lean_ident_segment)
        {
            return Err(format!(
                "theory_umbrella_module must be `Anneal` or `Anneal.<Sub>...` with valid Lean \
                 identifier segments, got {module:?}"
            ));
        }
        if matches!(module, "Anneal.MirWp" | "Anneal.MirWp.Canaries") {
            return Err(format!(
                "theory_umbrella_module must not collide with reserved generated module {module:?}"
            ));
        }
        Ok(PathBuf::from(format!("theory/{}.lean", segments.join("/"))))
    }

    /// Render the `import` (or `public import` when `self.module_syntax` is
    /// `true`) line targeting `self.theory_umbrella_module`.
    pub fn render_theory_umbrella_import(&self) -> TestResult<String> {
        self.theory_umbrella_rel_path()?;
        if self.module_syntax {
            Ok(format!("public import {}\n", self.theory_umbrella_module))
        } else {
            Ok(format!("import {}\n", self.theory_umbrella_module))
        }
    }

    /// Render the synthetic theory umbrella module configured by
    /// `self.theory_umbrella_module` (defaults to `theory/Anneal/Wp.lean`).
    pub fn render_anneal(&self) -> String {
        let header = if self.module_syntax {
            if self.theory_umbrella_module == "Anneal" {
                "module\n\
                 prelude\n\
                 public import Init.NotationExtra\n\
                 public import Trusted\n\
                 public import Trusted.MirAst\n\
                 public import Trusted.MirSemantics\n\
                 public import Anneal.MirWp\n"
            } else {
                "module\n\
                 prelude\n\
                 public import Init.NotationExtra\n\
                 public import Trusted\n\
                 public import Anneal.MirWp\n"
            }
        } else {
            "prelude\n\
             import Init.NotationExtra\n\
             import Trusted\n\
             import Trusted.MirAst\n\
             import Trusted.MirSemantics\n\
             import Anneal.MirWp\n"
        };
        if self.anneal_extra.is_empty() {
            header.to_string()
        } else {
            format!("{header}{}\n", self.anneal_extra)
        }
    }

    /// Write all rendered synthetic modules into an existing
    /// [`LeanAuditFixture`].
    pub fn materialize_into(&self, fixture: &LeanAuditFixture) -> TestResult {
        let umbrella_rel = self.theory_umbrella_rel_path()?;
        fixture.write_rel("trusted/lean/Trusted/MirAst.lean", self.render_mir_ast().as_bytes())?;
        fixture.write_rel(
            "trusted/lean/Trusted/MirSemantics.lean",
            self.render_mir_semantics().as_bytes(),
        )?;
        fixture.write_rel("theory/Anneal/MirWp.lean", self.render_mir_wp().as_bytes())?;
        if let Some(canaries) = self.render_canaries() {
            fixture.write_rel("theory/Anneal/MirWp/Canaries.lean", canaries.as_bytes())?;
        }
        fixture.write_rel(&umbrella_rel, self.render_anneal().as_bytes())?;
        Ok(())
    }

    /// Allocate a fresh [`LeanAuditFixture`] from `checkout` and materialize
    /// this synthetic MIR WP module set inside it.
    pub fn materialize(
        &self,
        checkout: &Path,
        prefix: &str,
        cache_policy: OleanCachePolicy,
    ) -> TestResult<LeanAuditFixture> {
        let fixture = LeanAuditFixture::with_cache_policy(
            checkout,
            prefix,
            Some(DEFAULT_VETTED_HEADER),
            false,
            cache_policy,
        )?;
        self.materialize_into(&fixture)?;
        Ok(fixture)
    }
}

#[cfg(test)]
mod tests;
