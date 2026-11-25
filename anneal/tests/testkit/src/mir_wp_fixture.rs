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

use std::{collections::BTreeMap, path::Path};

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
];

/// Configurable synthetic fixture containing minimal `Trusted.MirAst`,
/// `Trusted.MirSemantics`, `Anneal`, `Anneal.MirWp`, and decoupled
/// `Anneal.MirWp.Canaries` modules that pass `verifyMirWpCoreTheorems` out of
/// the box. Individual negative tests can override or omit any single claim,
/// proof, or alias in isolation.
#[derive(Clone, Debug)]
pub struct MirWpFixtureSpec {
    pub mir_ast_extra: String,
    pub wp_soundness_claim: Option<String>,
    pub wp_fault_soundness_claim: Option<String>,
    pub exec_soundness_claim_v2: Option<String>,
    pub canary_claim_overrides: BTreeMap<String, Option<String>>,
    pub public_alias_overrides: BTreeMap<String, Option<String>>,
    pub anneal_extra: String,
    pub wp_soundness_proof: Option<String>,
    pub wp_fault_soundness_proof: Option<String>,
    pub exec_soundness_proof_v2: Option<String>,
    pub canary_proof_overrides: BTreeMap<String, Option<String>>,
    pub mir_wp_extra: String,
    pub include_canaries_module: bool,
    pub canaries_extra: String,
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
            canary_claim_overrides: BTreeMap::new(),
            public_alias_overrides: BTreeMap::new(),
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
            canary_proof_overrides: BTreeMap::new(),
            mir_wp_extra: String::new(),
            include_canaries_module: true,
            canaries_extra: String::new(),
        }
    }

    /// Render `trusted/lean/Trusted/MirAst.lean`.
    pub fn render_mir_ast(&self) -> String {
        format!(
            "-- anneal-trust-tier: candidate:mir_ast\n\
             prelude\n\
             import Init.NotationExtra\n\
             namespace Trusted.MirAst\n\
             def placeholder : Nat := 0\n\
             def BinOp.cmp : Prop := True\n\
             def BinOp.addWithOverflow : Prop := True\n\
             def BinOp.subWithOverflow : Prop := True\n\
             def BinOp.mulWithOverflow : Prop := True\n\
             def MirTy.char : Prop := True\n\
             end Trusted.MirAst\n\
             {}\n",
            self.mir_ast_extra
        )
    }

    /// Render `trusted/lean/Trusted/MirSemantics.lean`.
    pub fn render_mir_semantics(&self) -> String {
        let mut sem = String::from(
            "-- anneal-trust-tier: candidate:mir_semantics\n\
             prelude\n\
             import Init.NotationExtra\n\
             import Trusted.MirAst\n\
             namespace Trusted.MirSemantics\n\
             def SatisfiesPost : Prop := True\n\
             def Diverges : Prop := True\n\
             def Behavior : Prop := True\n\
             def ReachesResult : Prop := True\n\
             def WellFormed : Prop := True\n\
             def SatisfiesPostV2 : Prop := True\n\
             def DivergesV2 : Prop := True\n\
             def BehaviorV2 : Prop := True\n\
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
             def progCastUninitSourceUb : Prop := True\n",
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
        sem
    }

    /// Render `theory/Anneal/MirWp.lean`.
    pub fn render_mir_wp(&self) -> String {
        let mut wp = String::from(
            "prelude\n\
             import Init.NotationExtra\n\
             import Trusted\n\
             import Trusted.MirAst\n\
             import Trusted.MirSemantics\n\
             namespace Anneal.MirWp\n\
             def wpProg : Nat := 0\n\
             def wpFaultProg : Nat := 0\n\
             def execProgV2 : Nat := 0\n",
        );
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
        wp.push_str("end Anneal.MirWp\n");
        if !self.mir_wp_extra.is_empty() {
            wp.push_str(&self.mir_wp_extra);
            wp.push('\n');
        }
        wp
    }

    /// Render `theory/Anneal/MirWp/Canaries.lean` when
    /// `self.include_canaries_module` is `true`.
    pub fn render_canaries(&self) -> Option<String> {
        if !self.include_canaries_module {
            return None;
        }
        let mut canaries = String::from(
            "prelude\n\
             import Init.NotationExtra\n\
             import Trusted\n\
             import Trusted.MirAst\n\
             import Trusted.MirSemantics\n\
             namespace Anneal.MirWp\n",
        );
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
        Some(canaries)
    }

    /// Render `theory/Anneal.lean`.
    pub fn render_anneal(&self) -> String {
        format!(
            "prelude\n\
             import Init.NotationExtra\n\
             import Trusted\n\
             import Trusted.MirAst\n\
             import Trusted.MirSemantics\n\
             import Anneal.MirWp\n\
             {}\n",
            self.anneal_extra
        )
    }

    /// Write all rendered synthetic modules into an existing
    /// [`LeanAuditFixture`].
    pub fn materialize_into(&self, fixture: &LeanAuditFixture) -> TestResult {
        fixture.write_rel("trusted/lean/Trusted/MirAst.lean", self.render_mir_ast().as_bytes())?;
        fixture.write_rel(
            "trusted/lean/Trusted/MirSemantics.lean",
            self.render_mir_semantics().as_bytes(),
        )?;
        fixture.write_rel("theory/Anneal/MirWp.lean", self.render_mir_wp().as_bytes())?;
        if let Some(canaries) = self.render_canaries() {
            fixture.write_rel("theory/Anneal/MirWp/Canaries.lean", canaries.as_bytes())?;
        }
        fixture.write_rel("theory/Anneal.lean", self.render_anneal().as_bytes())?;
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
mod tests {
    use std::{fs, path::Path};

    use super::*;
    use crate::toolchain::ToolchainEnv;

    /// Extract the `def verifyMirWpCoreTheorems` function body from
    /// `TrustedBoundary.lean`.
    fn extract_verify_mir_wp_body(source: &str) -> &str {
        let start = source
            .find("def verifyMirWpCoreTheorems")
            .expect("verifyMirWpCoreTheorems must exist in TrustedBoundary.lean");
        let tail = &source[start..];
        let end = tail[1..]
            .find("\n/-- ")
            .or_else(|| tail[1..].find("\ndef "))
            .map(|offset| offset + 1)
            .unwrap_or(tail.len());
        &tail[..end]
    }

    /// Scan every backtick-quoted Lean name (`Foo.Bar.baz`) inside `text`.
    fn backtick_names(text: &str) -> Vec<&str> {
        let bytes = text.as_bytes();
        let mut names = Vec::new();
        let mut i = 0;
        while i < bytes.len() {
            if bytes[i] == b'`' {
                let start = i + 1;
                let mut end = start;
                while end < bytes.len()
                    && (bytes[end].is_ascii_alphanumeric() || matches!(bytes[end], b'.' | b'_'))
                {
                    end += 1;
                }
                if end > start {
                    names.push(&text[start..end]);
                }
                i = end;
            } else {
                i += 1;
            }
        }
        names
    }

    /// Return `true` iff `expr` contains `ident` as a whole Lean identifier
    /// token (delimited by non-identifier characters, not a mere substring).
    fn contains_lean_ident_token(expr: &str, ident: &str) -> bool {
        expr.split(|c: char| !(c.is_ascii_alphanumeric() || matches!(c, '_' | '.')))
            .any(|tok| tok == ident)
    }

    /// Parse every core `requireClaimProof` call preceding the canary loop in
    /// `body`, returning `(claim, wp_param, proof, reqs)`.
    fn parse_core_require_claim_proofs(body: &str) -> Vec<(String, String, String, Vec<String>)> {
        let core_end = body.find("let posClaim").expect("canary section marker `let posClaim`");
        let core = &body[..core_end];
        let mut results = Vec::new();
        let mut idx = 0;
        while let Some(rel) = core[idx..].find("requireClaimProof ") {
            let start = idx + rel;
            let tail = &core[start..];
            let next_stmt =
                tail[1..].find("requireClaimProof ").map(|off| off + 1).unwrap_or(tail.len());
            let call = &tail[..next_stmt];
            let open_b =
                call.find('[').unwrap_or_else(|| panic!("missing reqConsts `[` in {call}"));
            let close_b =
                call.find(']').unwrap_or_else(|| panic!("missing reqConsts `]` in {call}"));
            let header = &call[..open_b];
            let header_names = backtick_names(header);
            assert_eq!(
                header_names.len(),
                3,
                "expected (claim, wp_param, proof) before reqConsts: {call}"
            );
            let claim = header_names[0]
                .strip_prefix("Trusted.MirSemantics.")
                .unwrap_or_else(|| panic!("unexpected core claim: {}", header_names[0]))
                .to_string();
            let wp_param = header_names[1]
                .strip_prefix("Anneal.MirWp.")
                .unwrap_or_else(|| panic!("unexpected core param: {}", header_names[1]))
                .to_string();
            let proof = header_names[2]
                .strip_prefix("Anneal.MirWp.")
                .unwrap_or_else(|| panic!("unexpected core proof: {}", header_names[2]))
                .to_string();
            let reqs = backtick_names(&call[open_b + 1..close_b])
                .into_iter()
                .map(|name| name.strip_prefix("Trusted.MirSemantics.").unwrap_or(name).to_string())
                .collect();
            results.push((claim, wp_param, proof, reqs));
            idx = start + next_stmt;
        }
        results
    }

    #[test]
    fn synthetic_mir_wp_fixture_matches_trusted_boundary_lean_100_percent() {
        let repo_root =
            ToolchainEnv::repo_root_from_manifest(Path::new(env!("CARGO_MANIFEST_DIR")))
                .expect("resolve anneal repo root");
        let tb_path = repo_root.join("trusted/audit/TrustedBoundary.lean");
        let source = fs::read_to_string(&tb_path)
            .unwrap_or_else(|e| panic!("read {}: {e}", tb_path.display()));
        let body = extract_verify_mir_wp_body(&source);

        // 1. Parse the canary `(claim, proof, reqConsts)` list inside
        //    `for (claimName, proofName, reqConsts) in [ ... ] do`.
        let list_marker = "for (claimName, proofName, reqConsts) in [";
        let list_start = body.find(list_marker).expect("canary loop in verifyMirWpCoreTheorems")
            + list_marker.len();
        let list_end = body[list_start..].find("] do").expect("closing `] do` for canary loop");
        let canary_block = &body[list_start..list_start + list_end];

        let mut parsed_canaries: Vec<(String, String, Vec<String>)> = Vec::new();
        let mut idx = 0;
        while let Some(open_rel) = canary_block[idx..].find('(') {
            let start = idx + open_rel;
            let mut depth = 0usize;
            let mut end = None;
            for (off, ch) in canary_block[start..].char_indices() {
                match ch {
                    '(' => depth += 1,
                    ')' => {
                        depth -= 1;
                        if depth == 0 {
                            end = Some(start + off + 1);
                            break;
                        }
                    }
                    _ => {}
                }
            }
            let end = end.expect("balanced tuple in canary list");
            let tuple = &canary_block[start..end];
            let names = backtick_names(tuple);
            assert!(names.len() >= 2, "expected (claim, proof, reqConsts) tuple, got: {tuple}");
            let claim = names[0]
                .strip_prefix("Trusted.MirSemantics.")
                .unwrap_or_else(|| panic!("unexpected claim name: {}", names[0]))
                .to_string();
            let proof = names[1]
                .strip_prefix("Anneal.MirWp.")
                .unwrap_or_else(|| panic!("unexpected proof name: {}", names[1]))
                .to_string();

            // Collect required constants (expanding `posClaim`/`negClaim`/
            // `widthClaim` shorthands).
            let bracket_start =
                tuple.find('[').unwrap_or_else(|| panic!("missing reqConsts in {tuple}"));
            let bracket_end =
                tuple.rfind(']').unwrap_or_else(|| panic!("missing closing `]` in {tuple}"));
            let req_slice = &tuple[bracket_start + 1..bracket_end];
            let mut reqs = Vec::new();
            for token in req_slice.split(',') {
                let tok = token.trim();
                if tok.is_empty() {
                    continue;
                }
                let mapped = match tok {
                    "posClaim" => "PositiveCanaryClaim".to_string(),
                    "negClaim" => "NegativeCanaryClaim".to_string(),
                    "widthClaim" => "IntWidthBoundaryCanary".to_string(),
                    other => {
                        let stripped = other
                            .strip_prefix('`')
                            .unwrap_or_else(|| panic!("unexpected reqConst token: {other}"));
                        stripped
                            .strip_prefix("Trusted.MirSemantics.")
                            .unwrap_or(stripped)
                            .to_string()
                    }
                };
                reqs.push(mapped);
            }
            parsed_canaries.push((claim, proof, reqs));
            idx = end;
        }

        // Exact 1:1 parity on canary count, order, claim names, proof names,
        // and whole-token required constant references in every synthetic body.
        assert_eq!(
            parsed_canaries.len(),
            SYNTHETIC_CANARIES.len(),
            "SYNTHETIC_CANARIES count drifted from TrustedBoundary.lean"
        );
        for ((tb_claim, tb_proof, tb_reqs), fixture_canary) in
            parsed_canaries.iter().zip(SYNTHETIC_CANARIES.iter())
        {
            assert_eq!(
                tb_claim.as_str(),
                fixture_canary.claim,
                "canary claim mismatch against TrustedBoundary.lean"
            );
            assert_eq!(
                tb_proof.as_str(),
                fixture_canary.proof,
                "canary proof mismatch for {tb_claim}"
            );
            for req in tb_reqs {
                assert!(
                    contains_lean_ident_token(fixture_canary.body, req),
                    "synthetic body for {tb_claim} missing required constant \
                     token {req:?}: {}",
                    fixture_canary.body
                );
            }
        }

        // 2. Verify all three core WP / Profile v2 soundness
        //    `requireClaimProof` calls and their required constants against
        //    `MirWpFixtureSpec::valid()`.
        let spec = MirWpFixtureSpec::valid();
        let parsed_core = parse_core_require_claim_proofs(body);
        assert_eq!(
            parsed_core.len(),
            CORE_WP_CLAIMS.len(),
            "CORE_WP_CLAIMS count drifted from TrustedBoundary.lean"
        );
        let core_claim_bodies = [
            spec.wp_soundness_claim.as_deref().unwrap(),
            spec.wp_fault_soundness_claim.as_deref().unwrap(),
            spec.exec_soundness_claim_v2.as_deref().unwrap(),
        ];
        let core_proof_bodies = [
            spec.wp_soundness_proof.as_deref().unwrap(),
            spec.wp_fault_soundness_proof.as_deref().unwrap(),
            spec.exec_soundness_proof_v2.as_deref().unwrap(),
        ];
        for (((tb_claim, tb_param, tb_proof, tb_reqs), &(c, p, pr)), idx) in
            parsed_core.iter().zip(CORE_WP_CLAIMS.iter()).zip(0usize..)
        {
            assert_eq!((tb_claim.as_str(), tb_param.as_str(), tb_proof.as_str()), (c, p, pr));
            assert!(
                contains_lean_ident_token(core_claim_bodies[idx], c),
                "core claim decl missing {c}: {}",
                core_claim_bodies[idx]
            );
            for req in tb_reqs {
                assert!(
                    contains_lean_ident_token(core_claim_bodies[idx], req),
                    "core claim {c} missing required constant token {req:?}: {}",
                    core_claim_bodies[idx]
                );
            }
            assert!(
                contains_lean_ident_token(core_proof_bodies[idx], pr),
                "core proof decl missing {pr}: {}",
                core_proof_bodies[idx]
            );
            assert!(
                contains_lean_ident_token(core_proof_bodies[idx], &format!("Anneal.MirWp.{p}")),
                "core proof decl missing Anneal.MirWp.{p}: {}",
                core_proof_bodies[idx]
            );
        }

        // 3. Verify public aliases (`Trusted.Crate`, `Trusted.CrateTheorem`,
        //    `Trusted.UnitTheorem`, `Trusted.CrateV2`,
        //    `Trusted.CrateTheoremV2`, `Trusted.UnitTheoremV2`).
        let alias_marker = "for (aliasName, targetName) in [";
        let alias_start = body.find(alias_marker).expect("alias loop in verifyMirWpCoreTheorems")
            + alias_marker.len();
        let alias_end = body[alias_start..].find("] do").expect("closing `] do` for alias loop");
        let alias_names = backtick_names(&body[alias_start..alias_start + alias_end]);
        let parsed_aliases: Vec<(&str, &str)> = alias_names
            .chunks_exact(2)
            .map(|pair| {
                (
                    pair[0].strip_prefix("Trusted.").unwrap(),
                    pair[1].strip_prefix("Trusted.MirSemantics.").unwrap(),
                )
            })
            .collect();
        assert_eq!(
            parsed_aliases, PUBLIC_MIR_ALIASES,
            "PUBLIC_MIR_ALIASES drifted from TrustedBoundary.lean"
        );

        // 4. Smoke-check rendering and materialization of the baseline spec.
        assert!(spec.render_mir_semantics().contains("ExecSoundnessClaimV2"));
        assert!(spec.render_mir_semantics().contains("CrateTheoremV2"));
        assert!(spec.render_mir_wp().contains("def execProgV2 : Nat := 0"));
        let fix = spec.materialize(&repo_root, "test-mir-wp-", OleanCachePolicy::Isolated).unwrap();
        assert!(fix.root().join("trusted/lean/Trusted/MirAst.lean").is_file());
        assert!(fix.root().join("trusted/lean/Trusted/MirSemantics.lean").is_file());
        assert!(fix.root().join("theory/Anneal/MirWp.lean").is_file());
        assert!(fix.root().join("theory/Anneal/MirWp/Canaries.lean").is_file());
        assert!(fix.root().join("theory/Anneal.lean").is_file());
    }
}
