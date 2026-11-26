-- Copyright 2026 The Fuchsia Authors
--
-- Licensed under a BSD-style license <LICENSE-BSD>, Apache License, Version 2.0
-- <LICENSE-APACHE or https://www.apache.org/licenses/LICENSE-2.0>, or the MIT
-- license <LICENSE-MIT or https://opensource.org/licenses/MIT>, at your option.
-- This file may not be copied, modified, or distributed except according to
-- those terms.

prelude
import Init.NotationExtra
import Anneal.MiniRust.Anchors
import Anneal.MiniRust.OracleCert

namespace Anneal.MiniRustProof

open Trusted.MirAst
open Trusted.MirSemantics
open Anneal.MiniRust

/-!
# MiniRust Operational Authority & Correspondence Hub (`Anneal.MiniRustProof`)

Thin top-level entry module exporting the MiniRust (`minirust_v1`) operational
correspondence theorems directly targeting `Trusted.MirAst` and
`Trusted.MirSemantics`, completely independent of `vendor/lean-miri`,
`Trusted.Correspondence`, `Anneal.MirCorrespondence*`, and `Anneal.MirWp`.

Every exported theorem is 100% constructive
(`#print axioms ⊆ {propext, Quot.sound}`, zero `Classical.choice`, zero
`sorryAx`, zero `Lean.ofReduceBool`).
-/

/-- Top-level forward simulation theorem over `MiniRustAdmitted`
(`.forwardSim "minirust_v1"`). -/
theorem minirust_forward_sim_holds : MiniRustForwardSimClaim :=
  minirust_forward_sim_base

/-- Top-level bidirectional fault-equivalence theorem over
`MiniRustExactAdmitted` (`.biFaultEquiv "minirust_v1"`). -/
theorem minirust_bi_fault_equiv_holds : MiniRustBiFaultEquivClaim :=
  minirust_bi_fault_equiv_base

/-- Structural well-formedness (`spec/lang/well-formed.md`) of every translated
`MiniRustAdmitted` program (`0`-arg, `1`-ZST `start` function in `functions`,
no `StorageDead` on return or argument locals, and unique `Switch` keys). -/
theorem minirust_admitted_prog_wellFormed (p : Program) (q : Query)
    (hadm : MiniRustAdmitted p q) :
    mrProgWellFormed (translateProg p) p.entryDefId = true :=
  Anneal.MiniRust.minirust_admitted_prog_wellFormed hadm

/-- Runtime freedom from `StepOutcome.illFormed` across all reachable MiniRust
machine states for every `MiniRustAdmitted` input. -/
theorem minirust_admitted_never_illFormed (p : Program) (q : Query)
    (hadm : MiniRustAdmitted p q) :
    ∀ m₀, initMrMachine p q = .ok m₀ →
      ¬ MrIllFormed m₀ ∧ (∀ m r, MrReaches m₀ m → mrStep m ≠ .illFormed r) := by
  intro m₀ hinit
  have hnoIF := Anneal.MiniRust.minirust_admitted_never_illFormed p q hadm m₀
    hinit
  exact ⟨hnoIF, fun m r hr hs => hnoIF ⟨m, r, hr, hs⟩⟩

/-- Admission completeness: no `MiniRustAdmitted` execution in Anneal ever
faults `.unsupported`. -/
theorem minirust_forward_no_unsupported (p : Program) (q : Query)
    (hadm : MiniRustAdmitted p q) :
    ¬ ReachesResult p q (.fault .unsupported) :=
  forward_no_unsupported p q hadm

/-- Forward return behavior simulation over `MiniRustAdmitted`. -/
theorem minirust_forward_behavior (p : Program) (q : Query)
    (hadm : MiniRustAdmitted p q) :
    ∀ m₀, initMrMachine p q = .ok m₀ →
      ∀ v, Behavior p q (.returned ⟨v, ⟨[]⟩⟩) →
        MrBehavior m₀ (translateVal v) :=
  forward_behavior p q hadm

/-- Contrapositive UB soundness over `MiniRustAdmitted`. -/
theorem minirust_forward_ub_contrapositive (p : Program) (q : Query)
    (hadm : MiniRustAdmitted p q) :
    ∀ m₀, initMrMachine p q = .ok m₀ →
      MrFaultsUB m₀ → ReachesResult p q (.fault .undefined) :=
  forward_ub_contrapositive p q hadm

/-- `WellFormed` implies MiniRust UB-freedom over `MiniRustAdmitted`. -/
theorem minirust_forward_wellFormed_no_ub (p : Program) (q : Query)
    (hadm : MiniRustAdmitted p q) :
    ∀ m₀, initMrMachine p q = .ok m₀ →
      WellFormed p q → ¬ MrFaultsUB m₀ :=
  forward_wellFormed_no_ub p q hadm

/-- Forward divergence simulation over `MiniRustAdmitted`. -/
theorem minirust_forward_diverges (p : Program) (q : Query)
    (hadm : MiniRustAdmitted p q) :
    ∀ m₀, initMrMachine p q = .ok m₀ →
      Diverges p q → MrDiverges m₀ :=
  forward_diverges p q hadm

/-- Exact bidirectional UB equivalence over `MiniRustExactAdmitted`. -/
theorem minirust_exact_ub_iff (p : Program) (q : Query)
    (hadm : MiniRustExactAdmitted p q) :
    ∀ m₀, initMrMachine p q = .ok m₀ →
      (ReachesResult p q (.fault .undefined) ↔ MrFaultsUB m₀) :=
  exact_ub_iff p q hadm

/-- Exact bidirectional return equivalence over `MiniRustExactAdmitted`. -/
theorem minirust_exact_behavior_iff (p : Program) (q : Query)
    (hadm : MiniRustExactAdmitted p q) :
    ∀ m₀, initMrMachine p q = .ok m₀ →
      (∀ v, Behavior p q (.returned ⟨v, ⟨[]⟩⟩) →
        MrBehavior m₀ (translateVal v)) ∧
      (∀ v', MrBehavior m₀ v' →
        ∃ v, v' = translateVal v ∧ Behavior p q (.returned ⟨v, ⟨[]⟩⟩)) :=
  exact_behavior_iff p q hadm

/-- Exact bidirectional divergence equivalence over `MiniRustExactAdmitted`. -/
theorem minirust_exact_diverges_iff (p : Program) (q : Query)
    (hadm : MiniRustExactAdmitted p q) :
    ∀ m₀, initMrMachine p q = .ok m₀ →
      (Diverges p q ↔ MrDiverges m₀) :=
  exact_diverges_iff p q hadm

/-- Value encode/decode round-trip for every supported Anneal type and value. -/
theorem minirust_encode_decode_roundtrip (ty : MirTy) (v : Val)
    (hsupp : isSupportedScalarOrUnitTy ty = true)
    (hcv : checkVal v ty = true) :
    ∃ bs, mrEncode (translateTy ty) (translateVal v) = some bs ∧
      bs.length = (translateTy ty).size.bytes ∧
      mrDecode (translateTy ty) bs = some (translateVal v) :=
  mrEncode_mrDecode_roundtrip ty v hsupp hcv

/-- Non-emptiness of the verified upstream MiniRust spec anchor table. -/
theorem minirust_spec_anchors_nonempty : specAnchors.isEmpty = false :=
  specAnchors_nonempty

/-- Exact count lock (`58`) on the curated upstream MiniRust spec anchors. -/
theorem minirust_spec_anchors_count : specAnchors.length = 58 :=
  specAnchors_count

/-! ## Re-Exported Constructive Non-Vacuity Witnesses -/

theorem witness_arith_holds :
    ∃ m₀, initMrMachine progArith queryArith = .ok m₀ ∧
      MiniRustExactAdmitted progArith queryArith ∧
      Behavior progArith queryArith
        (.returned ⟨mkScalarVal .i32 false 22, ⟨[]⟩⟩) ∧
      mrRunFuel 24 m₀ = .returned (translateVal (mkScalarVal .i32 false 22)) ∧
      MrBehavior m₀ (translateVal (mkScalarVal .i32 false 22)) :=
  witness_arith_exact

theorem witness_bitwise_shift_holds :
    ∃ m₀, initMrMachine progBitwiseShift queryBitwiseShift = .ok m₀ ∧
      MiniRustExactAdmitted progBitwiseShift queryBitwiseShift ∧
      Behavior progBitwiseShift queryBitwiseShift
        (.returned ⟨mkScalarVal .i8 false 27, ⟨[]⟩⟩) ∧
      mrRunFuel 24 m₀ = .returned (translateVal (mkScalarVal .i8 false 27)) ∧
      MrBehavior m₀ (translateVal (mkScalarVal .i8 false 27)) :=
  witness_bitwise_shift_exact

theorem witness_cmp_discr_holds :
    ∃ m₀, initMrMachine progCmpDiscr queryCmpDiscr = .ok m₀ ∧
      MiniRustExactAdmitted progCmpDiscr queryCmpDiscr ∧
      Behavior progCmpDiscr queryCmpDiscr
        (.returned ⟨mkScalarVal .i8 true 255, ⟨[]⟩⟩) ∧
      mrRunFuel 16 m₀ = .returned (translateVal (mkScalarVal .i8 true 255)) ∧
      MrBehavior m₀ (translateVal (mkScalarVal .i8 true 255)) :=
  witness_cmp_discr_exact

theorem witness_overflow_pair_holds :
    ∃ m₀, initMrMachine progOverflowPair queryOverflowPair = .ok m₀ ∧
      MiniRustExactAdmitted progOverflowPair queryOverflowPair ∧
      Behavior progOverflowPair queryOverflowPair
        (.returned ⟨expectedOverflowVal, ⟨[]⟩⟩) ∧
      mrRunFuel 16 m₀ = .returned (translateVal expectedOverflowVal) ∧
      MrBehavior m₀ (translateVal expectedOverflowVal) :=
  witness_overflow_pair_exact

theorem witness_switchInt_matched_holds :
    let q := mkWitnessQuery [mkScalarVal .i8 false 2]
    ∃ m₀, initMrMachine progSwitchInt q = .ok m₀ ∧
      MiniRustExactAdmitted progSwitchInt q ∧
      Behavior progSwitchInt q (.returned ⟨mkScalarVal .i8 false 20, ⟨[]⟩⟩) ∧
      mrRunFuel 16 m₀ = .returned (translateVal (mkScalarVal .i8 false 20)) ∧
      MrBehavior m₀ (translateVal (mkScalarVal .i8 false 20)) :=
  witness_switchInt_matched_exact

theorem witness_switchInt_otherwise_holds :
    let q := mkWitnessQuery [mkScalarVal .i8 false 7]
    ∃ m₀, initMrMachine progSwitchInt q = .ok m₀ ∧
      MiniRustExactAdmitted progSwitchInt q ∧
      Behavior progSwitchInt q (.returned ⟨mkScalarVal .i8 false 99, ⟨[]⟩⟩) ∧
      mrRunFuel 16 m₀ = .returned (translateVal (mkScalarVal .i8 false 99)) ∧
      MrBehavior m₀ (translateVal (mkScalarVal .i8 false 99)) :=
  witness_switchInt_otherwise_exact

theorem witness_storage_lifecycle_holds :
    let q := mkWitnessQuery []
    ∃ m₀, initMrMachine progStorageLifecycle q = .ok m₀ ∧
      MiniRustExactAdmitted progStorageLifecycle q ∧
      Behavior progStorageLifecycle q
        (.returned ⟨mkScalarVal .i32 false 42, ⟨[]⟩⟩) ∧
      mrRunFuel 16 m₀ = .returned (translateVal (mkScalarVal .i32 false 42)) ∧
      MrBehavior m₀ (translateVal (mkScalarVal .i32 false 42)) :=
  witness_storage_lifecycle_exact

theorem witness_cast_i8_to_i32_holds :
    let q := mkWitnessQuery [mkScalarVal .i8 true 255]
    ∃ m₀, initMrMachine progCastI8ToI32 q = .ok m₀ ∧
      MiniRustExactAdmitted progCastI8ToI32 q ∧
      Behavior progCastI8ToI32 q
        (.returned ⟨mkScalarVal .i32 true 4294967295, ⟨[]⟩⟩) ∧
      mrRunFuel 16 m₀ =
        .returned (translateVal (mkScalarVal .i32 true 4294967295)) ∧
      MrBehavior m₀ (translateVal (mkScalarVal .i32 true 4294967295)) :=
  witness_cast_i8_to_i32_exact

theorem witness_cast_u32_to_u8_holds :
    let q := mkWitnessQuery [mkScalarVal .i32 false 298]
    ∃ m₀, initMrMachine progCastU32ToU8 q = .ok m₀ ∧
      MiniRustExactAdmitted progCastU32ToU8 q ∧
      Behavior progCastU32ToU8 q (.returned ⟨mkScalarVal .i8 false 42, ⟨[]⟩⟩) ∧
      mrRunFuel 16 m₀ = .returned (translateVal (mkScalarVal .i8 false 42)) ∧
      MrBehavior m₀ (translateVal (mkScalarVal .i8 false 42)) :=
  witness_cast_u32_to_u8_exact

theorem witness_cast_i32_to_u64_holds :
    let q := mkWitnessQuery [mkScalarVal .i32 true 4294967294]
    let outV := mkScalarVal .i64 false 18446744073709551614
    ∃ m₀, initMrMachine progCastI32ToU64 q = .ok m₀ ∧
      MiniRustExactAdmitted progCastI32ToU64 q ∧
      Behavior progCastI32ToU64 q (.returned ⟨outV, ⟨[]⟩⟩) ∧
      mrRunFuel 16 m₀ = .returned (translateVal outV) ∧
      MrBehavior m₀ (translateVal outV) :=
  witness_cast_i32_to_u64_exact

theorem witness_cast_bool_to_u32_holds :
    let q := mkWitnessQuery [.bool true]
    ∃ m₀, initMrMachine progCastBoolToU32 q = .ok m₀ ∧
      MiniRustExactAdmitted progCastBoolToU32 q ∧
      Behavior progCastBoolToU32 q
        (.returned ⟨mkScalarVal .i32 false 1, ⟨[]⟩⟩) ∧
      mrRunFuel 16 m₀ = .returned (translateVal (mkScalarVal .i32 false 1)) ∧
      MrBehavior m₀ (translateVal (mkScalarVal .i32 false 1)) :=
  witness_cast_bool_to_u32_exact

theorem witness_enum_scalar_discr_holds :
    let q := mkWitnessQuery []
    ∃ m₀, initMrMachine progEnumScalarDiscr q = .ok m₀ ∧
      MiniRustExactAdmitted progEnumScalarDiscr q ∧
      Behavior progEnumScalarDiscr q
        (.returned ⟨mkScalarVal .i8 false 2, ⟨[]⟩⟩) ∧
      mrRunFuel 16 m₀ = .returned (translateVal (mkScalarVal .i8 false 2)) ∧
      MrBehavior m₀ (translateVal (mkScalarVal .i8 false 2)) :=
  witness_enum_scalar_discr_exact

theorem witness_enum_zst_discr_holds :
    let q := mkWitnessQuery []
    ∃ m₀, initMrMachine progEnumZstDiscr q = .ok m₀ ∧
      MiniRustExactAdmitted progEnumZstDiscr q ∧
      Behavior progEnumZstDiscr q (.returned ⟨mkScalarVal .i8 false 7, ⟨[]⟩⟩) ∧
      mrRunFuel 16 m₀ = .returned (translateVal (mkScalarVal .i8 false 7)) ∧
      MrBehavior m₀ (translateVal (mkScalarVal .i8 false 7)) :=
  witness_enum_zst_discr_exact

theorem witness_cast_u8_to_char_holds :
    let q := mkWitnessQuery [mkScalarVal .i8 false 65]
    ∃ m₀, initMrMachine progCastU8ToChar q = .ok m₀ ∧
      MiniRustAdmitted progCastU8ToChar q ∧
      ¬ MiniRustExactAdmitted progCastU8ToChar q ∧
      Behavior progCastU8ToChar q (.returned ⟨.char 'A', ⟨[]⟩⟩) ∧
      mrRunFuel 16 m₀ = .returned (translateVal (.char 'A')) ∧
      MrBehavior m₀ (translateVal (.char 'A')) :=
  witness_cast_u8_to_char_admitted

theorem witness_char_niche_strictness_holds :
    let q := mkWitnessQuery []
    ∃ m₀, initMrMachine progCharSurrogate q = .ok m₀ ∧
      MiniRustAdmitted progCharSurrogate q ∧
      ¬ MiniRustExactAdmitted progCharSurrogate q ∧
      ReachesResult progCharSurrogate q (.fault .undefined) ∧
      mrRunFuel 12 m₀ = .returned (.int 0xD800) ∧
      MrBehavior m₀ (.int 0xD800) :=
  witness_char_niche_strictness

theorem witness_strict_move_inclusion_holds :
    ∃ m₀, initMrMachine progMoveSimple queryMoveSimple = .ok m₀ ∧
      MiniRustAdmitted progMoveSimple queryMoveSimple ∧
      ¬ MiniRustExactAdmitted progMoveSimple queryMoveSimple ∧
      Behavior progMoveSimple queryMoveSimple
        (.returned ⟨mkScalarVal .i32 false 42, ⟨[]⟩⟩) ∧
      mrRunFuel 12 m₀ = .returned (translateVal (mkScalarVal .i32 false 42)) ∧
      MrBehavior m₀ (translateVal (mkScalarVal .i32 false 42)) :=
  witness_strict_move_inclusion

theorem witness_move_semantic_strictness_holds :
    ∃ m₀, initMrMachine progMoveThenRead queryMoveSimple = .ok m₀ ∧
      MiniRustAdmitted progMoveThenRead queryMoveSimple ∧
      ¬ MiniRustExactAdmitted progMoveThenRead queryMoveSimple ∧
      ReachesResult progMoveThenRead queryMoveSimple (.fault .undefined) ∧
      mrRunFuel 12 m₀ = .returned (translateVal (mkScalarVal .i32 false 42)) ∧
      MrBehavior m₀ (translateVal (mkScalarVal .i32 false 42)) :=
  witness_move_semantic_strictness

theorem witness_ub_div_by_zero_holds :
    let q := mkWitnessQuery []
    ∃ m₀, initMrMachine progUbDivByZero q = .ok m₀ ∧
      MiniRustExactAdmitted progUbDivByZero q ∧
      ReachesResult progUbDivByZero q (.fault .undefined) ∧
      mrRunFuel 12 m₀ = .ub "division by zero" ∧
      MrFaultsUB m₀ :=
  witness_ub_div_by_zero

theorem witness_ub_int_min_div_neg_one_holds :
    let q := mkWitnessQuery []
    ∃ m₀, initMrMachine progUbIntMinDivNegOne q = .ok m₀ ∧
      MiniRustExactAdmitted progUbIntMinDivNegOne q ∧
      ReachesResult progUbIntMinDivNegOne q (.fault .undefined) ∧
      mrRunFuel 12 m₀ = .ub "overflow in division" ∧
      MrFaultsUB m₀ :=
  witness_ub_int_min_div_neg_one

theorem witness_ub_unchecked_overflow_holds :
    let q := mkWitnessQuery []
    ∃ m₀, initMrMachine progUbUncheckedOverflow q = .ok m₀ ∧
      MiniRustExactAdmitted progUbUncheckedOverflow q ∧
      ReachesResult progUbUncheckedOverflow q (.fault .undefined) ∧
      mrRunFuel 12 m₀ = .ub "overflow in unchecked add" ∧
      MrFaultsUB m₀ :=
  witness_ub_unchecked_overflow

theorem witness_ub_bad_shift_holds :
    let q := mkWitnessQuery []
    ∃ m₀, initMrMachine progUbBadShift q = .ok m₀ ∧
      MiniRustExactAdmitted progUbBadShift q ∧
      ReachesResult progUbBadShift q (.fault .undefined) ∧
      mrRunFuel 12 m₀ = .ub "overflow in unchecked shift" ∧
      MrFaultsUB m₀ :=
  witness_ub_bad_shift

theorem witness_ub_uninit_read_holds :
    let q := mkWitnessQuery []
    ∃ m₀, initMrMachine progUbUninitRead q = .ok m₀ ∧
      MiniRustExactAdmitted progUbUninitRead q ∧
      ReachesResult progUbUninitRead q (.fault .undefined) ∧
      mrRunFuel 12 m₀ = .ub
        "load at type but the data in memory violates the language invariant" ∧
      MrFaultsUB m₀ :=
  witness_ub_uninit_read

theorem witness_ub_unreachable_holds :
    let q := mkWitnessQuery []
    ∃ m₀, initMrMachine progUbUnreachable q = .ok m₀ ∧
      MiniRustExactAdmitted progUbUnreachable q ∧
      ReachesResult progUbUnreachable q (.fault .undefined) ∧
      mrRunFuel 12 m₀ = .ub "reached unreachable code" ∧
      MrFaultsUB m₀ :=
  witness_ub_unreachable

/-- Standalone MiniRust machine witness (outside `translateProg`) confirming
that `MrTerminator.return_` on a `StackPopAction.bottomOfStack` frame faults UB
(`"the start function must not return"`). -/
theorem witness_mr_bottom_of_stack_return_ub_holds :
    mrStep mrBottomOfStackReturnMachine =
      .ub "the start function must not return" ∧
    MrFaultsUB mrBottomOfStackReturnMachine :=
  witness_mr_bottom_of_stack_return_ub

end Anneal.MiniRustProof
