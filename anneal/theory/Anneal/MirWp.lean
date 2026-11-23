-- Copyright 2026 The Fuchsia Authors
--
-- Licensed under a BSD-style license <LICENSE-BSD>, Apache License, Version 2.0
-- <LICENSE-APACHE or https://www.apache.org/licenses/LICENSE-2.0>, or the MIT
-- license <LICENSE-MIT or https://opensource.org/licenses/MIT>, at your option.
-- This file may not be copied, modified, or distributed except according to
-- those terms.

module
prelude
public import Init.NotationExtra
public import Trusted
public import Trusted.MirAst
public import Trusted.MirSemantics
public import Anneal.MirWp.Core
public import Anneal.MirWp.Scalars
public import Anneal.MirWp.Reflection
public import Anneal.MirWp.Execution
public import Anneal.MirWp.Canaries

public section

namespace Anneal.MirWp

open Trusted.MirAst Trusted.MirSemantics

/-!
# Fuel-Bounded Weakest Precondition, Adequacy, and Type/Scalar Theory (`MirWp`)

This untrusted `theory/` module provides the program-logic and inversion
machinery over `Trusted.MirAst` and `Trusted.MirSemantics`:

1. **Unified Fuel-Bounded Weakest Precondition (`wpOutcomeState`, `wpState`,
   `wpFaultState`, `wpProg`, `wpFaultProg`) and Deterministic Fast Path
   (`execOutcomeState`, `execState`, `execFaultState`, `execProg`,
   `execFaultProg`):** `@Nat.rec` outcome predicates into `Prop` (no codegen
   exemptions or `_unsafe_rec`), preserving the `ValidChoice`-quantified shape
   of `wpOutcomeState`/`wpProg`/`wpFaultProg` while bridging deterministic
   `c = 0` `rfl`-reducible execution via `wpProg_of_execProg` and
   `wpFaultProg_of_execFaultProg`, together with rule of consequence, fuel
   weakening, non-divergence, and the audited adequacy theorems
   (`wellFormed_and_spec_of_wp : WpSoundnessClaim wpProg` and
   `reaches_fault_and_exclusive_of_wpFault : WpFaultSoundnessClaim
   wpFaultProg`).
2. **Width-Parametric Bitvector, Scalar, and Operator Adequacy:** Exact modular
   characterization and idempotence of `truncateBits`, totality and
   well-formedness of `truncateScalar`, all 25 Pass 1 non-vacuity and
   parameter-boundary canaries, and width/signedness-parametric operator
   totality across all six `IntWidth` variants.
3. **Lawful Type Equality and `checkVal` / `ValidEntryArgs` Inversion:**
   Complete `MirTy.beq t₁ t₂ = true ↔ t₁ = t₂` reflection, constructor-level
   `checkVal` characterizations (including fieldless enums of arbitrary variant
   count and uninhabited `MirTy.never`), arity-generic `checkArgsMatch`
   inversion, the `initState` entry equation (`initState_eq_ok`), and
   compositional `BodiesVerified` dispatch.
4. **Single-Body Execution, Productive Divergence, and Multi-Body Retagging:**
   Single-body `Reach`, `SafeFrom`, `ReturnsFrom`, `Executes`, and the
   fuel-bounded run certificate `RunsFrom` (`Runs` from the entry state),
   stated as propositions over the trusted transition
   `evalStep (bodyProg body) 0` and bridged to `execState`/`wpState`
   (`executes_iff_wpState`), `Classical.choice`-free `ProductiveInvariant`
   divergence proofs, and single-pass `retagDefId` simulation to
   `entryProgForBody p defId`.
-/

/-! ## Locked Pass 1 Adequacy and Non-Vacuity Canary Theorems -/

/-- Audited WP adequacy theorem forwarding to
`wellFormed_and_spec_of_wp_base`. -/
theorem wellFormed_and_spec_of_wp : WpSoundnessClaim wpProg :=
  wellFormed_and_spec_of_wp_base

/-- Audited WP fault-soundness theorem forwarding to
`reaches_fault_and_exclusive_of_wpFault_base`. -/
theorem reaches_fault_and_exclusive_of_wpFault :
    WpFaultSoundnessClaim wpFaultProg :=
  reaches_fault_and_exclusive_of_wpFault_base

theorem canary_positive_add_anneal : CanaryPositiveAddAnnealClaim :=
  canary_positive_add_anneal_base

theorem canary_positive_empty_unit_fn : CanaryPositiveEmptyUnitFnClaim :=
  canary_positive_empty_unit_fn_base

theorem canary_positive_stmts_and_cf_anneal : CanaryPositiveStmtsAndCfAnnealClaim :=
  canary_positive_stmts_and_cf_anneal_base

theorem canary_positive_unop_anneal : CanaryPositiveUnopAnnealClaim :=
  canary_positive_unop_anneal_base

theorem canary_positive_all_binops_anneal : CanaryPositiveAllBinopsAnnealClaim :=
  canary_positive_all_binops_anneal_base

theorem canary_positive_all_int_widths_anneal : CanaryPositiveAllIntWidthsAnnealClaim :=
  canary_positive_all_int_widths_anneal_base

theorem canary_negative_ub_div_zero_anneal : CanaryNegativeUbDivZeroAnnealClaim :=
  canary_negative_ub_div_zero_anneal_base

theorem canary_negative_ub_signed_rem_overflow_i8 : CanaryNegativeUbSignedRemOverflowI8Claim :=
  canary_negative_ub_signed_rem_overflow_i8_base

theorem canary_negative_unsupported_anneal : CanaryNegativeUnsupportedAnnealClaim :=
  canary_negative_unsupported_anneal_base

theorem canary_negative_ub_add_unchecked_overflow_u32 : CanaryNegativeUbAddUncheckedOverflowU32Claim :=
  canary_negative_ub_add_unchecked_overflow_u32_base

theorem canary_negative_ub_shift_unchecked_at_bitwidth_anneal : CanaryNegativeUbShiftUncheckedAtBitwidthAnnealClaim :=
  canary_negative_ub_shift_unchecked_at_bitwidth_anneal_base

theorem canary_negative_ub_storage_dead_read_anneal : CanaryNegativeUbStorageDeadReadAnnealClaim :=
  canary_negative_ub_storage_dead_read_anneal_base

theorem canary_negative_ub_storage_dead_return_place_anneal : CanaryNegativeUbStorageDeadReturnPlaceAnnealClaim :=
  canary_negative_ub_storage_dead_return_place_anneal_base

theorem canary_negative_ub_unreachable_anneal : CanaryNegativeUbUnreachableAnnealClaim :=
  canary_negative_ub_unreachable_anneal_base

theorem canary_negative_unsupported_unsigned_neg_anneal : CanaryNegativeUnsupportedUnsignedNegAnnealClaim :=
  canary_negative_unsupported_unsigned_neg_anneal_base

theorem canary_positive_enum_explicit_repr_anneal : CanaryPositiveEnumExplicitReprAnnealClaim :=
  canary_positive_enum_explicit_repr_anneal_base

theorem canary_positive_zst_single_enum_anneal : CanaryPositiveZstSingleEnumAnnealClaim :=
  canary_positive_zst_single_enum_anneal_base

theorem canary_negative_ub_enum_invalid_tag_and_uninit_anneal : CanaryNegativeUbEnumInvalidTagAndUninitAnnealClaim :=
  canary_negative_ub_enum_invalid_tag_and_uninit_anneal_base

theorem canary_crate_and_body_verified_anneal : CanaryCrateAndBodyVerifiedAnnealClaim :=
  canary_crate_and_body_verified_anneal_base

theorem canary_memory_lifecycle_anneal : CanaryMemoryLifecycleAnnealClaim :=
  canary_memory_lifecycle_anneal_base

theorem canary_positive_char_and_cmp_anneal :
    CanaryPositiveCharAndCmpAnnealClaim :=
  canary_positive_char_and_cmp_anneal_base

theorem canary_negative_char_and_cmp_anneal :
    CanaryNegativeCharAndCmpAnnealClaim :=
  canary_negative_char_and_cmp_anneal_base

theorem canary_positive_overflow_ops_anneal :
    CanaryPositiveOverflowOpsAnnealClaim :=
  canary_positive_overflow_ops_anneal_base

theorem canary_positive_int_to_int_cast_anneal :
    CanaryPositiveIntToIntCastAnnealClaim :=
  canary_positive_int_to_int_cast_anneal_base

theorem canary_negative_int_to_int_cast_anneal :
    CanaryNegativeIntToIntCastAnnealClaim :=
  canary_negative_int_to_int_cast_anneal_base

end Anneal.MirWp

end
