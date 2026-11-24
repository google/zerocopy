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
   (`wellFormed_and_spec_of_wp : WpSoundnessClaim wpProg`,
   `reaches_fault_and_exclusive_of_wpFault : WpFaultSoundnessClaim
   wpFaultProg`, and the Profile v2
   `wellFormed_and_spec_of_execV2 : ExecSoundnessClaimV2 execProgV2` and
   `safeContract_soundness_of_execV2` (`SafeContractSoundnessClaimV2` for
   `execProgV2`)).
2. **Width-Parametric Bitvector, Scalar, and Operator Adequacy:** Exact modular
   characterization and idempotence of `truncateBits`, totality and
   well-formedness of `truncateScalar`, and width/signedness-parametric operator
   totality across all six `IntWidth` variants (with the 26 Pass 1 non-vacuity
   and parameter-boundary canaries audited separately in `Anneal.MirWp.Canaries`
   without bloating user runtime imports).
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

/-! ## Locked Pass 1 Adequacy Theorems -/

/-- Audited WP adequacy theorem forwarding to
`wellFormed_and_spec_of_wp_base`. -/
theorem wellFormed_and_spec_of_wp : WpSoundnessClaim wpProg :=
  wellFormed_and_spec_of_wp_base

/-- Audited WP fault-soundness theorem forwarding to
`reaches_fault_and_exclusive_of_wpFault_base`. -/
theorem reaches_fault_and_exclusive_of_wpFault :
    WpFaultSoundnessClaim wpFaultProg :=
  reaches_fault_and_exclusive_of_wpFault_base

/-- Audited Profile v2 execution adequacy theorem forwarding to
`wellFormed_and_spec_of_execV2_base`. -/
theorem wellFormed_and_spec_of_execV2 : ExecSoundnessClaimV2 execProgV2 :=
  wellFormed_and_spec_of_execV2_base

/-- Audited Profile v2 `SafeContractV2` soundness theorem forwarding to
`safeContract_soundness_of_execV2_base`. -/
theorem safeContract_soundness_of_execV2 :
    SafeContractSoundnessClaimV2 execProgV2 :=
  safeContract_soundness_of_execV2_base

end Anneal.MirWp

end
