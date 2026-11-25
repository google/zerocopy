-- Copyright 2026 The Fuchsia Authors
--
-- Licensed under a BSD-style license <LICENSE-BSD>, Apache License, Version 2.0
-- <LICENSE-APACHE or https://www.apache.org/licenses/LICENSE-2.0>, or the MIT
-- license <LICENSE-MIT or https://opensource.org/licenses/MIT>, at your option.
-- This file may not be copied, modified, or distributed except according to
-- those terms.

module
prelude
public import Init.Core
public import Init.NotationExtra
public import Init.Data.Nat.Basic
public import Init.Data.List.Basic
public import Init.SimpLemmas
public import Init.Control.Except
public import Trusted.MirAst
public import Trusted.MirModel
public import Trusted.MirSemantics.Memory
public import Anneal.PTree
public import Anneal.Core.SepPCM
public import Anneal.PureLift.LoanGraph
public import Anneal.PureLift.SpatialPin
public import Anneal.MirMemComp.Memory
public import Anneal.SepAC.Normalize
public import Anneal.SepAC.RangeSpan

public section

/-!
# Reflective `SepAC`, Lithium `PTree` Framing, & `ByteRange` Canaries

Concrete positive witnesses and single-cause counterexamples exercising the
core contracts and laws in `Anneal.SepAC`:

1. **Canary 1 (`canary1_reflective_acu_and_spatialProp_cancel`):**
   - Discharges both a 6-atom scrambled separating-conjunction bientailment
     (with nested `SepExpr.emp`) and a 16-atom reversed balanced `SepExpr`
     bientailment by `rfl` via `sepAC_bientails_of_norm_eq` on
     `PermSpatialProp Nat` (and bridges `Anneal.Core.SepProp` via
     `coreSepProp_sepACULaws`).
   - Exercises linear framing (`sepAC_entails_of_cancelAtoms`) on
     `PermSpatialProp Nat`, cancelling 3 shared atoms down to 1 residual
     entailment, and verifies `not_affineEntails_permSpatialProp` plus
     `permSpatialSepConj_of_spatialSepConj`.
   - Exercises affine weakening (`sepAC_affine_entails_of_cancel_nil`) by `rfl`
     on an explicit affine `Nat`-additive model (`x ≥ y`).
2. **Canary 2 (`canary2_cancelAtoms_converse_and_mono_counterexamples`):**
   - Proves `sepAC_entails_of_cancelAtoms` has no converse in a genuine
     non-cancellative `SepACULaws` model (`Bool`, `Bool.or`, `false`, `(=)`):
     `(true || true) = (true || false)` holds, pairwise `cancelAtoms` cancels
     the shared dominant atom `0` (`true`), and the resulting residuals `[0]`
     and `[1]` do not entail each other (`true ≠ false`).
   - Proves `SepMonoRight` is indispensable for `sepAC_entails_of_cancelAtoms`
     using `(Nat, Nat.add, 0, badNonMonoEntails)`, proving all five remaining
     `SepACULaws` fields (`EntailsRefl`, `EntailsTrans`, `SepAssocBientails`,
     `SepCommBientails`, `RightUnitBientails`) while refuting `SepMonoRight`
     (`0 ⊢ 1` yet `1 + 0 ⊬ 1 + 1`).
3. **Canary 3 (`canary3_lithium_ptree_framing_and_diamond_join`):**
   - Instantiates `pheapProp_sepACULaws` + `sepAC_bientails_of_norm_eq` on
     canonical `PTree Nat` heaps (`not_affineEntails_pheapProp`).
   - Constructs a concrete non-trivial 2-key `LithiumTriple`
     (`canary3_lithiumTriple_exists`, via `ptree_set_lithiumTriple_exists` +
     `lithiumTriple_union_disjoint`) updating keys `3` and `11` in place, lifts
     it across a 16-entry `ptreeTabulate` context via
     `lithiumFrame_of_diffWith`, verifies `lithiumFrame_diamond_comm` over a
     mutually disjoint 13-key remainder (`canary3Rem13`), and verifies
     fail-closed `none` regressions.
4. **Canary 4 (`canary4_rangeSplit_one_million_bytes_O1`):**
   - Splits a `1_000_000`-byte `ByteRange` at `k₁ = 345_678` and splits its
     right half again at `k₂ = 400_000` in $O(1)$ without materializing byte
     lists, proving all 3 sub-ranges are pairwise `RangeDisjoint` (via
     `rangeDisjointBool_iff` and `rangeSplit_disjoint`), cover
     `[0, 1_000_000)` identically (`rangeSplit_covers_iff`), re-merge to the
     original range (`rangeMerge_split`), and round-trip through
     `toCoreByteRange` / `ofCoreByteRange`.
5. **Canary 5 (`canary5_memoryState_sameAlloc_split_write_frame`):**
   - Splits a live 16-byte `MemoryState` allocation `1` (`[0..16)`) via
     `ownRange_split_iff` into `[0..6)`, `[6..10)`, and `[10..16)`, writes 4
     fresh bytes into `[6..10)` via `Anneal.MirMemComp.execWriteBytes`, and
     proves both same-allocation siblings (`[0..6)` and `[10..16)`) and an
     immutable sibling allocation `0` (`[0..4)`) remain untouched via
     `allocBytesAt_frame_of_execWriteBytes_disjoint`.

All authored definitions are computable (`0` `noncomputable`, `0`
`._unsafe_rec`, `0` `omega`, `0` `decide`) and every authored declaration
compiles using at most `[propext]` (`0` `Classical.choice`, `0` `Quot.sound`).
-/

namespace Anneal.SepAC

open Trusted.MirAst Trusted.MirSemantics
open Anneal.PTree Anneal.PureLift Anneal.MirMemComp

/-! ## Canary 1: Reflective ACU Normalization & Linear/Affine Cancellation -/

/-- Left scrambled 6-atom `SepExpr` with nested `.emp` units. -/
@[expose] def canary1ExprLhs : SepExpr :=
  .sep (.sep (.atom 4) (.sep .emp (.atom 1)))
    (.sep (.sep (.atom 5) (.atom 0)) (.sep (.atom 2) (.sep (.atom 3) .emp)))

/-- Right scrambled 6-atom `SepExpr` denoting the same multiset `{0..5}`. -/
@[expose] def canary1ExprRhs : SepExpr :=
  .sep (.atom 0)
    (.sep (.sep (.atom 3) (.atom 5))
      (.sep (.atom 1) (.sep (.atom 4) (.atom 2))))

/-- Affine `Nat`-additive model (`x ⊢ y ↔ y ≤ x`, `sep := (· + ·)`,
`emp := 0`): satisfies `SepACULaws` and `AffineEntails 0`. -/
theorem canary1_natGe_affine_laws :
    SepACULaws (fun a b : Nat => a + b) 0 (fun x y : Nat => y ≤ x) ∧
    AffineEntails 0 (fun x y : Nat => y ≤ x) := by
  refine ⟨⟨Nat.le_refl, fun _ _ _ h12 h23 => Nat.le_trans h23 h12,
    fun f _ _ h => Nat.add_le_add_left h f,
    fun x y z => by
      rw [Nat.add_assoc]
      exact ⟨Nat.le_refl _, Nat.le_refl _⟩,
    fun x y => by
      rw [Nat.add_comm]
      exact ⟨Nat.le_refl _, Nat.le_refl _⟩,
    fun x => by
      rw [Nat.add_zero]
      exact ⟨Nat.le_refl _, Nat.le_refl _⟩⟩,
    fun x => Nat.zero_le x⟩

/-- Balanced 16-atom forward `SepExpr` (`0..15`) for medium-size `rfl`
normalization canary. -/
@[expose] def canary1Rev16Lhs : SepExpr :=
  .sep
    (.sep (.sep (.sep (.atom 0) (.atom 1)) (.sep (.atom 2) (.atom 3)))
      (.sep (.sep (.atom 4) (.atom 5)) (.sep (.atom 6) (.atom 7))))
    (.sep (.sep (.sep (.atom 8) (.atom 9)) (.sep (.atom 10) (.atom 11)))
      (.sep (.sep (.atom 12) (.atom 13)) (.sep (.atom 14) (.atom 15))))

/-- Balanced 16-atom reversed `SepExpr` (`15..0`) for medium-size `rfl`
normalization canary. -/
@[expose] def canary1Rev16Rhs : SepExpr :=
  .sep
    (.sep (.sep (.sep (.atom 15) (.atom 14)) (.sep (.atom 13) (.atom 12)))
      (.sep (.sep (.atom 11) (.atom 10)) (.sep (.atom 9) (.atom 8))))
    (.sep (.sep (.sep (.atom 7) (.atom 6)) (.sep (.atom 5) (.atom 4)))
      (.sep (.sep (.atom 3) (.atom 2)) (.sep (.atom 1) (.atom 0))))

/-- Canary 1 (`[propext]` only): proves 6-atom scrambled and 16-atom reversed
ACU bientailments on `PermSpatialProp Nat` (plus `coreSepProp_sepACULaws`) by
`rfl`, linear 3-atom cancellation down to a 1-atom residual entailment, strict
linearity (`¬ AffineEntails`), `spatialSepConj` lifting, and affine weakening by
`rfl`. -/
theorem canary1_reflective_acu_and_spatialProp_cancel
    (env : Nat → PermSpatialProp Nat)
    (hRes03 : PermSpatialEntails (env 0) (env 3))
    {M : Type} (pcm : Anneal.Core.ExplPCM M)
    (envCore : Nat → Anneal.Core.SepProp M) :
    Bientails (@PermSpatialEntails Nat)
      (evalSepExprFuel permSpatialSepConj permSpatialEmp env 8 canary1ExprLhs)
      (evalSepExprFuel permSpatialSepConj permSpatialEmp env 8 canary1ExprRhs) ∧
    Bientails (@PermSpatialEntails Nat)
      (evalSepExprFuel permSpatialSepConj permSpatialEmp env 6 canary1Rev16Lhs)
      (evalSepExprFuel permSpatialSepConj permSpatialEmp env 6
        canary1Rev16Rhs) ∧
    Bientails (@Anneal.Core.SepEntails M)
      (evalSepExprFuel (Anneal.Core.sepConj pcm) (Anneal.Core.sepEmp pcm)
        envCore 8 canary1ExprLhs)
      (evalSepExprFuel (Anneal.Core.sepConj pcm) (Anneal.Core.sepEmp pcm)
        envCore 8 canary1ExprRhs) ∧
    PermSpatialEntails
      (evalSepExprFuel permSpatialSepConj permSpatialEmp env 8
        (.sep (.atom 2) (.sep (.atom 0) (.sep (.atom 5) (.atom 1)))))
      (evalSepExprFuel permSpatialSepConj permSpatialEmp env 8
        (.sep (.atom 1) (.sep (.atom 3) (.sep (.atom 2) (.atom 5))))) ∧
    ¬ AffineEntails (@permSpatialEmp Nat) (@PermSpatialEntails Nat) ∧
    (∀ h, spatialSepConj (env 0).pred (env 1).pred h →
      (permSpatialSepConj (env 0) (env 1)).pred h) ∧
    (∀ (envN : Nat → Nat),
      evalSepExprFuel (fun a b : Nat => a + b) 0 envN 8
          (.sep (.atom 2) (.atom 0)) ≤
        evalSepExprFuel (fun a b : Nat => a + b) 0 envN 8
          (.sep (.atom 0) (.sep (.atom 1) (.sep (.atom 2) (.atom 3))))) := by
  have hL := permSpatialProp_sepACULaws Nat
  have hC := coreSepProp_sepACULaws pcm
  have hAff := canary1_natGe_affine_laws
  refine ⟨sepAC_bientails_of_norm_eq hL env (fuel := 8) rfl,
    sepAC_bientails_of_norm_eq hL env (fuel := 6) rfl,
    sepAC_bientails_of_norm_eq hC envCore (fuel := 8) rfl, ?_,
    not_affineEntails_permSpatialProp Nat,
    fun _ h => permSpatialSepConj_of_spatialSepConj h,
    fun envN =>
      sepAC_affine_entails_of_cancel_nil hAff.1 hAff.2 envN (fuel := 8)
        (lhs := .sep (.atom 0) (.sep (.atom 1) (.sep (.atom 2) (.atom 3))))
        (rhs := .sep (.atom 2) (.atom 0)) rfl⟩
  apply sepAC_entails_of_cancelAtoms hL env (fuel := 8)
  change PermSpatialEntails
    (permSpatialSepConj (env 0) permSpatialEmp)
    (permSpatialSepConj (env 3) permSpatialEmp)
  exact hL.trans _ (env 0) _ (hL.rightUnit (env 0)).1
    (hL.trans _ (env 3) _ hRes03 (hL.rightUnit (env 3)).2)

/-! ## Canary 2: Non-Cancellative Converse & `SepMonoRight` Counterexamples -/

/-- Genuine non-cancellative `SepACULaws` model `(Bool, Bool.or, false, (=))`
(`[]` zero axioms) used to disprove the converse of
`sepAC_entails_of_cancelAtoms`. -/
theorem canary2_boolOr_sepACULaws : SepACULaws Bool.or false Eq where
  refl _ := rfl
  trans _ _ _ h1 h2 := Eq.trans h1 h2
  monoRight _ _ _ h := congrArg _ h
  assoc a b c := by
    cases a <;> cases b <;> cases c <;> exact ⟨rfl, rfl⟩
  comm a b := by
    cases a <;> cases b <;> exact ⟨rfl, rfl⟩
  rightUnit a := by
    cases a <;> exact ⟨rfl, rfl⟩

/-- Non-monotonic preorder on `Nat` (`x ⊢ y ↔ x = y ∨ (x = 0 ∧ y = 1)`):
satisfies `EntailsRefl`, `EntailsTrans`, `SepAssocBientails`,
`SepCommBientails`, and `RightUnitBientails` under `(Nat.add, 0)`, yet violates
`SepMonoRight` because `0 ⊢ 1` while `1 + 0 = 1 ⊬ 2 = 1 + 1`. -/
@[expose] def badNonMonoEntails (x y : Nat) : Prop :=
  x = y ∨ (x = 0 ∧ y = 1)

/-- Canary 2 (`[]` zero axioms): proves (1) in the genuine `SepACULaws` model
`(Bool, Bool.or, false, (=))`, `(true || true) = (true || false)` holds while
cancelling shared atom `0` yields non-entailing residuals `true ≠ false`
(disproving the converse of `sepAC_entails_of_cancelAtoms`), and (2)
`(Nat, Nat.add, 0, badNonMonoEntails)` satisfies all five remaining
`SepACULaws` obligations while violating `SepMonoRight`. -/
theorem canary2_cancelAtoms_converse_and_mono_counterexamples :
    let envOr := fun i : Nat => if Nat.beq i 0 then true else false
    let lhsOr := SepExpr.sep (.atom 0) (.atom 0)
    let rhsOr := SepExpr.sep (.atom 0) (.atom 1)
    let resOr := cancelAtoms (normSepFuel 4 lhsOr) (normSepFuel 4 rhsOr)
    (evalSepExprFuel Bool.or false envOr 4 lhsOr =
      evalSepExprFuel Bool.or false envOr 4 rhsOr) ∧
    resOr = ([0], [1]) ∧
    (evalAtomList Bool.or false envOr resOr.1 ≠
      evalAtomList Bool.or false envOr resOr.2) ∧
    EntailsRefl badNonMonoEntails ∧
    EntailsTrans badNonMonoEntails ∧
    SepAssocBientails Nat.add badNonMonoEntails ∧
    SepCommBientails Nat.add badNonMonoEntails ∧
    RightUnitBientails Nat.add 0 badNonMonoEntails ∧
    ¬ SepMonoRight Nat.add badNonMonoEntails ∧
    (badNonMonoEntails 0 1 ∧
      ¬ badNonMonoEntails (Nat.add 1 0) (Nat.add 1 1)) := by
  intro envOr lhsOr rhsOr resOr
  refine ⟨rfl, rfl, ?_, fun _ => Or.inl rfl, ?_, ?_, ?_, ?_, ?_,
    Or.inr ⟨rfl, rfl⟩, ?_⟩
  · intro hEq
    exact Bool.noConfusion hEq
  · intro x y z hxy hyz
    cases hxy with
    | inl heq =>
      rw [heq]
      exact hyz
    | inr h01 =>
      cases hyz with
      | inl heq =>
        rw [← heq]
        exact Or.inr h01
      | inr h01' =>
        have hBad : (1 : Nat) = 0 := Eq.trans h01.2.symm h01'.1
        nomatch hBad
  · intro x y z
    exact ⟨Or.inl (Nat.add_assoc x y z), Or.inl (Nat.add_assoc x y z).symm⟩
  · intro x y
    exact ⟨Or.inl (Nat.add_comm x y), Or.inl (Nat.add_comm y x)⟩
  · intro x
    exact ⟨Or.inl (Nat.add_zero x), Or.inl (Nat.add_zero x).symm⟩
  · intro hMono
    have hBad := hMono 1 0 1 (Or.inr ⟨rfl, rfl⟩)
    cases hBad with
    | inl hEq => exact Nat.noConfusion (Nat.succ.inj hEq)
    | inr h01 => exact Nat.noConfusion h01.1
  · intro hBad
    cases hBad with
    | inl hEq => exact Nat.noConfusion (Nat.succ.inj hEq)
    | inr h01 => exact Nat.noConfusion h01.1

/-! ## Canary 3: Lithium `PTree` Keyed Framing & Canonical Diamond Join -/

/-- 16-entry `PTree Nat` built lazily via computable `ptreeTabulate` (keys
`0..15` mapped to `i * 10 + 1`). -/
@[expose] def canary3Ctx16 : PTree Nat :=
  ptreeTabulate 5 (fun i => cond (Nat.blt i 16) (some (i * 10 + 1)) none)

/-- 2-key required footprint (`key 3 ↦ 31`, `key 11 ↦ 111`) built via
computable `ptreeTabulate`. -/
@[expose] def canary3Req2 : PTree Nat :=
  ptreeTabulate 5 (fun i =>
    if Nat.beq i 3 then some 31
    else if Nat.beq i 11 then some 111
    else none)

/-- 2-key updated postcondition (`key 3 ↦ 300`, `key 11 ↦ 1100`) on the exact
same footprint as `canary3Req2`. -/
@[expose] def canary3Post2 : PTree Nat :=
  ptreeTabulate 5 (fun i =>
    if Nat.beq i 3 then some 300
    else if Nat.beq i 11 then some 1100
    else none)

/-- Disjoint 1-key second footprint (`key 7 ↦ 700`) for diamond-join
commutativity. -/
@[expose] def canary3PostOther : PTree Nat :=
  ptreeTabulate 5 (fun i => if Nat.beq i 7 then some 700 else none)

/-- Expected 14-key remainder after subtracting `canary3Req2` from
`canary3Ctx16`. -/
@[expose] def canary3Rem14 : PTree Nat :=
  ptreeTabulate 5 (fun i =>
    if Nat.beq i 3 || Nat.beq i 11 then none
    else cond (Nat.blt i 16) (some (i * 10 + 1)) none)

/-- Mutually disjoint 13-key remainder (excluding keys `3`, `7`, and `11`) for
diamond-join commutativity between `canary3Post2` and `canary3PostOther`. -/
@[expose] def canary3Rem13 : PTree Nat :=
  ptreeTabulate 5 (fun i =>
    if Nat.beq i 3 || Nat.beq i 7 || Nat.beq i 11 then none
    else cond (Nat.blt i 16) (some (i * 10 + 1)) none)

/-- Missing-key requirement (`key 20 ↦ 1`) for fail-closed regression. -/
@[expose] def canary3BadMissing : PTree Nat :=
  ptreeTabulate 6 (fun i => if Nat.beq i 20 then some 1 else none)

/-- Mismatched-value requirement (`key 3 ↦ 999`) for fail-closed regression. -/
@[expose] def canary3BadValue : PTree Nat :=
  ptreeTabulate 5 (fun i => if Nat.beq i 3 then some 999 else none)

private theorem canary3_diff_ok :
    PTree.diffWith Nat.beq canary3Ctx16 canary3Req2 = some canary3Rem14 := rfl

private theorem canary3_disjoint_post2_other :
    PTree.DisjointProp canary3Post2 canary3PostOther := by
  have hDiff :
      PTree.diffWith Nat.beq
        (PTree.union canary3Post2 canary3PostOther) canary3Post2 =
          some canary3PostOther := rfl
  exact (ptree_diffWith_sound Nat.beq Nat.eq_of_beq_eq_true hDiff).1

private theorem canary3_disjoint_post2_rem13 :
    PTree.DisjointProp canary3Post2 canary3Rem13 := by
  have hDiff :
      PTree.diffWith Nat.beq
        (PTree.union canary3Post2 canary3Rem13) canary3Post2 =
          some canary3Rem13 := rfl
  exact (ptree_diffWith_sound Nat.beq Nat.eq_of_beq_eq_true hDiff).1

private theorem canary3_disjoint_other_rem13 :
    PTree.DisjointProp canary3PostOther canary3Rem13 := by
  have hDiff :
      PTree.diffWith Nat.beq
        (PTree.union canary3PostOther canary3Rem13) canary3PostOther =
          some canary3Rem13 := rfl
  exact (ptree_diffWith_sound Nat.beq Nat.eq_of_beq_eq_true hDiff).1

private theorem natBeq_refl_cn : ∀ n : Nat, Nat.beq n n = true
  | 0 => rfl
  | k + 1 => natBeq_refl_cn k

/-- Concrete non-trivial `LithiumTriple` inhabitation witness (`[propext]`
only) updating keys `3` (`31 → 300`) and `11` (`111 → 1100`) in place. -/
theorem canary3_lithiumTriple_exists :
    ∃ step : PTree Nat → Option (PTree Nat),
      LithiumTriple canary3Req2 canary3Post2 step := by
  have hReqEq :
      canary3Req2 =
        PTree.union (PTree.singleton (natToPosAt 5 3) 31)
          (PTree.singleton (natToPosAt 5 11) 111) := rfl
  have hPostEq :
      canary3Post2 =
        PTree.union (PTree.singleton (natToPosAt 5 3) 300)
          (PTree.singleton (natToPosAt 5 11) 1100) := rfl
  have hD311 :
      PTree.DisjointProp (PTree.singleton (natToPosAt 5 3) 31)
        (PTree.singleton (natToPosAt 5 11) 111) := by
    have hDiff :
        PTree.diffWith Nat.beq canary3Req2
          (PTree.singleton (natToPosAt 5 3) 31) =
            some (PTree.singleton (natToPosAt 5 11) 111) := rfl
    exact (ptree_diffWith_sound Nat.beq Nat.eq_of_beq_eq_true hDiff).1
  cases ptree_set_lithiumTriple_exists Nat.beq natBeq_refl_cn
      (natToPosAt 5 3) 31 300 with
  | intro s1 hs1 =>
    cases ptree_set_lithiumTriple_exists Nat.beq natBeq_refl_cn
        (natToPosAt 5 11) 111 1100 with
    | intro s2 hs2 =>
      refine ⟨ptreeBindStep s1 s2, ?_⟩
      rw [hReqEq, hPostEq]
      exact lithiumTriple_union_disjoint hD311 hs1 hs2

/-- Canary 3 (`[propext]` only): exercises `pheapProp_sepACULaws` reflective
ACU normalization, `not_affineEntails_pheapProp`, deterministic 16-entry
`lithiumFrame_of_diffWith` lifting the concrete `canary3_lithiumTriple_exists`
witness + post-state lookup, canonical `=` diamond join
(`lithiumFrame_diamond_comm`) over the mutually disjoint 13-key remainder
`canary3Rem13`, and 2 fail-closed `none` regressions. -/
theorem canary3_lithium_ptree_framing_and_diamond_join
    (envP : Nat → PHeapProp Nat) :
    Bientails (@PHeapEntails Nat)
      (evalSepExprFuel pheapSepConj pheapEmp envP 8 canary1ExprLhs)
      (evalSepExprFuel pheapSepConj pheapEmp envP 8 canary1ExprRhs) ∧
    ¬ AffineEntails (@pheapEmp Nat) (@PHeapEntails Nat) ∧
    (∃ step : PTree Nat → Option (PTree Nat),
      LithiumTriple canary3Req2 canary3Post2 step ∧
      PTree.DisjointProp canary3Req2 canary3Rem14 ∧
      PTree.DisjointProp canary3Post2 canary3Rem14 ∧
      step canary3Ctx16 = some (PTree.union canary3Post2 canary3Rem14)) ∧
    ((PTree.union canary3Post2 canary3Rem14).get (natToPosAt 5 3) = some 300 ∧
      (PTree.union canary3Post2 canary3Rem14).get (natToPosAt 5 11) =
        some 1100 ∧
      (PTree.union canary3Post2 canary3Rem14).get (natToPosAt 5 7) = some 71) ∧
    (PTree.DisjointProp canary3Post2 canary3Rem13 ∧
      PTree.DisjointProp canary3PostOther canary3Rem13 ∧
      PTree.union canary3Post2 (PTree.union canary3PostOther canary3Rem13) =
        PTree.union canary3PostOther
          (PTree.union canary3Post2 canary3Rem13)) ∧
    PTree.diffWith Nat.beq canary3Ctx16 canary3BadMissing = none ∧
    PTree.diffWith Nat.beq canary3Ctx16 canary3BadValue = none := by
  have hL := pheapProp_sepACULaws Nat
  cases canary3_lithiumTriple_exists with
  | intro step hTr =>
    have hFrame :=
      lithiumFrame_of_diffWith Nat.beq Nat.eq_of_beq_eq_true canary3_diff_ok
        hTr
    exact ⟨sepAC_bientails_of_norm_eq hL envP (fuel := 8) rfl,
      not_affineEntails_pheapProp 0,
      ⟨step, hTr, hFrame.1, hFrame.2.1, hFrame.2.2⟩,
      ⟨rfl, rfl, rfl⟩,
      ⟨canary3_disjoint_post2_rem13, canary3_disjoint_other_rem13,
        lithiumFrame_diamond_comm canary3_disjoint_post2_other⟩,
      rfl, rfl⟩

/-! ## Canary 4: $O(1)$ `1_000_000`-Byte `ByteRange` 3-Way `split_at_mut` -/

private theorem canary4_k1_le : 345678 ≤ 1000000 :=
  Nat.le_of_ble_eq_true rfl

private theorem canary4_k2_le : 400000 ≤ 1000000 - 345678 :=
  Nat.le_of_ble_eq_true rfl

/-- Canary 4 (`[]` zero axioms): splits a `1_000_000`-byte `ByteRange` in $O(1)$
at `345_678` and again at `400_000` into 3 pairwise-disjoint sub-ranges
covering `[0, 1_000_000)` identically and re-merging to the exact original
range without constructing a byte list. -/
theorem canary4_rangeSplit_one_million_bytes_O1 :
    let rAll : ByteRange := ⟨7, 0, 1000000⟩
    let sp1 := rangeSplit rAll 345678
    let sp2 := rangeSplit sp1.2 400000
    RangeDisjoint sp1.1 sp2.1 ∧
    RangeDisjoint sp1.1 sp2.2 ∧
    RangeDisjoint sp2.1 sp2.2 ∧
    rangeMerge sp1.1 (rangeMerge sp2.1 sp2.2) = rAll ∧
    ofCoreByteRange (toCoreByteRange rAll) = rAll ∧
    (∀ aid off,
      InRange rAll aid off ↔
        InRange sp1.1 aid off ∨ InRange sp2.1 aid off ∨ InRange sp2.2 aid off) ∧
    (∀ aid off, InRange sp1.1 aid off → ¬ InRange sp2.2 aid off) := by
  intro rAll sp1 sp2
  have hD1BoolEq : rangeDisjointBool sp1.1 sp2.1 = true := by
    dsimp only [rAll, sp1, sp2, rangeSplit, rangeDisjointBool]
    rfl
  have hD1Bool : RangeDisjoint sp1.1 sp2.1 :=
    (rangeDisjointBool_iff sp1.1 sp2.1).mp hD1BoolEq
  have hD1 : RangeDisjoint sp1.1 sp1.2 := rangeSplit_disjoint rAll 345678
  have hD1Sym : RangeDisjoint sp1.2 sp1.1 := rangeDisjoint_symm hD1
  have hSub := rangeDisjoint_of_subrange canary4_k2_le hD1Sym
  have hD2 : RangeDisjoint sp2.1 sp2.2 := rangeSplit_disjoint sp1.2 400000
  have hMerge2 : rangeMerge sp2.1 sp2.2 = sp1.2 :=
    rangeMerge_split sp1.2 canary4_k2_le
  have hMergeAll : rangeMerge sp1.1 (rangeMerge sp2.1 sp2.2) = rAll := by
    rw [hMerge2]
    exact rangeMerge_split rAll canary4_k1_le
  have hCov :
      ∀ aid off,
        InRange rAll aid off ↔
          InRange sp1.1 aid off ∨
            InRange sp2.1 aid off ∨ InRange sp2.2 aid off := by
    intro aid off
    have hC1 := rangeSplit_covers_iff rAll canary4_k1_le aid off
    have hC2 := rangeSplit_covers_iff sp1.2 canary4_k2_le aid off
    refine ⟨fun h => ?_, fun h => ?_⟩
    · cases hC1.mp h with
      | inl hL => exact Or.inl hL
      | inr hR => exact Or.inr (hC2.mp hR)
    · cases h with
      | inl hL => exact hC1.mpr (Or.inl hL)
      | inr hR => exact hC1.mpr (Or.inr (hC2.mpr hR))
  exact ⟨hD1Bool, rangeDisjoint_symm hSub.2, hD2, hMergeAll,
    ofCoreByteRange_toCore rAll, hCov, fun _ _ h1 h2 =>
      rangeDisjoint_no_shared_offset (rangeDisjoint_symm hSub.2) h1 h2⟩

/-! ## Canary 5: `MemoryState` Same-Allocation `split_at_mut` Frame -/

/-- Concrete 2-allocation `MemoryState`: immutable sibling allocation `0`
(`4` bytes of `0xCC`) and mutable 16-byte target allocation `1` (`alignLog2 =
2`, initialized to `0x11`). -/
@[expose] def canary5InitMem : MemoryState :=
  { nextAllocId := 2
    allocations :=
      [{ allocId := 0
         alignLog2 := 0
         mutability := .shared
         bytes := List.replicate 4 (.init 0xCC none)
         live := true },
       { allocId := 1
         alignLog2 := 2
         mutability := .mut
         bytes := List.replicate 16 (.init 0x11 none)
         live := true }] }

/-- 4-byte payload written into middle sub-slice `[6..10)` of allocation `1`. -/
@[expose] def canary5WritePayload : List AllocByte :=
  [.init 0xA0 none, .init 0xA1 none, .init 0xA2 none, .init 0xA3 none]

/-- Canary 5 (`[propext]` only): splits allocation `1`'s `[0..16)` into
`[0..6)`, `[6..10)`, and `[10..16)` via `ownRange_split_iff`, writes
`canary5WritePayload` at `⟨1, 6⟩` (`alignLog2 = 1`), and proves via
`allocBytesAt_frame_of_execWriteBytes_disjoint` that:
1. Same-allocation prefix `[0..6)` retains `6` bytes of `0x11`,
2. Same-allocation suffix `[10..16)` retains `6` bytes of `0x11`,
3. Sibling allocation `0` (`[0..4)`) retains `4` bytes of `0xCC`, and
4. Middle slice `[6..10)` reads back `canary5WritePayload`. -/
theorem canary5_memoryState_sameAlloc_split_write_frame :
    let rAlloc0 : ByteRange := ⟨0, 0, 4⟩
    let rAll1 : ByteRange := ⟨1, 0, 16⟩
    let rPre : ByteRange := (rangeSplit rAll1 6).1
    let rTail := (rangeSplit rAll1 6).2
    let rMid : ByteRange := (rangeSplit rTail 4).1
    let rPost : ByteRange := (rangeSplit rTail 4).2
    ∃ m' : MemoryState,
      execWriteBytes canary5InitMem ⟨rMid.allocId, rMid.start⟩ 1
          canary5WritePayload = .ok m' ∧
      AllocBytesAt m' rPre (List.replicate 6 (.init 0x11 none)) ∧
      AllocBytesAt m' rPost (List.replicate 6 (.init 0x11 none)) ∧
      AllocBytesAt m' rAlloc0 (List.replicate 4 (.init 0xCC none)) ∧
      AllocBytesAt m' rMid canary5WritePayload := by
  intro rAlloc0 rAll1 rPre rTail rMid rPost
  have hInit1 : AllocBytesAt canary5InitMem rAll1
      (List.replicate 16 (.init 0x11 none)) :=
    ⟨{ allocId := 1
       alignLog2 := 2
       mutability := .mut
       bytes := List.replicate 16 (.init 0x11 none)
       live := true },
     rfl, rfl, Nat.le_refl 16, rfl, rfl⟩
  have hInit0 : AllocBytesAt canary5InitMem rAlloc0
      (List.replicate 4 (.init 0xCC none)) :=
    ⟨{ allocId := 0
       alignLog2 := 0
       mutability := .shared
       bytes := List.replicate 4 (.init 0xCC none)
       live := true },
     rfl, rfl, Nat.le_refl 4, rfl, rfl⟩
  have hSp1 :=
    (ownRange_split_iff canary5InitMem rAll1
      (List.replicate 16 (.init 0x11 none))
      (k := 6) (Nat.le_of_ble_eq_true rfl)).mp hInit1
  have hSp2 :=
    (ownRange_split_iff canary5InitMem rTail
      ((List.replicate 16 (.init 0x11 none)).drop 6)
      (k := 4) (Nat.le_of_ble_eq_true rfl)).mp hSp1.2
  cases hW : execWriteBytes canary5InitMem ⟨1, 6⟩ 1 canary5WritePayload with
  | error _ => nomatch hW
  | ok m' =>
    have hDPre : RangeDisjoint rMid rPre :=
      (rangeDisjointBool_iff rMid rPre).mp rfl
    have hDPost : RangeDisjoint rMid rPost :=
      (rangeDisjointBool_iff rMid rPost).mp rfl
    have hD0 : RangeDisjoint rMid rAlloc0 :=
      (rangeDisjointBool_iff rMid rAlloc0).mp rfl
    have hFrPre :=
      allocBytesAt_frame_of_execWriteBytes_disjoint rfl hDPre hW hSp1.1
    have hFrPost :=
      allocBytesAt_frame_of_execWriteBytes_disjoint rfl hDPost hW hSp2.2
    have hFr0 :=
      allocBytesAt_frame_of_execWriteBytes_disjoint rfl hD0 hW hInit0
    have hMid : AllocBytesAt m' rMid canary5WritePayload := by
      injection hW with hMeq
      rw [← hMeq]
      exact ⟨{ allocId := 1
               alignLog2 := 2
               mutability := .mut
               bytes :=
                 ((List.replicate 16 (.init 0x11 none)).take 6 ++
                   canary5WritePayload) ++
                 (List.replicate 16 (.init 0x11 none)).drop 10
               live := true },
        rfl, rfl, Nat.le_of_ble_eq_true rfl, rfl, rfl⟩
    exact ⟨m', hW, hFrPre, hFrPost, hFr0, hMid⟩

end Anneal.SepAC

end
