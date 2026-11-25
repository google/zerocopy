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
public import Trusted.MirAst
public import Trusted.MirSemantics
public import Anneal.CnfOrd.Ord
public import Anneal.CnfOrd.Worklist
public import Anneal.ByteSubLens.Lens
public import Anneal.MirMemComp.Codecs
public import Anneal.WavefrontReclaim.SpatialPcm

public section

/-!
# Ordinal-Bounded Wavefront Drain & Universal Loan Reclamation
(`Anneal.WavefrontReclaim.Wavefront`)

Constructive, zero-TCB weakest-precondition logic (`VSepWpOrdRel`) over the
`SpatialPcm` resource trie, `< ω^ω` Cantor Normal Form ordinal measures
(`Anneal.CnfOrd`), and `Trusted.MirSemantics.MemoryState` byte sub-lenses
(`Anneal.ByteSubLens`, `Anneal.MirMemComp`):

- `WfLoanEntry`, `LoansSyncedWithMem`, and `QueueMatchesLoans` couple
  mod-`2^32` pure-lifted loans with `Trusted.MirSemantics.MemoryState` via
  big-endian `wfEncodeU32BeSlice` (bridged to
  `Trusted.MirSemantics.encodeUInt`).
- `evalHybridCmd` provides a fail-closed hybrid command semantics covering
  pure-lifted writes, spatial cell updates, exclusive loan checkout,
  amortized burst submission, and strict rank-descending wavefront steps
  (`.faultLoanViolation` on stale/missing/unmatched leaves and
  `.faultInvalidSpawn` on inadmissible rank spawns).
- `multiRank_wavefront_terminates_arbitrary_depth`,
  `universal_post_drain_activeMut_reclaim`, `vsepWpOrdRel_wavefrontDrain`, and
  `vsepWpOrdRel_fiveStage_chained_lifecycle` prove arbitrary-depth `< ω^ω`
  convergence, universal `.activeMut` reclamation with exact mod-`2^32` delta
  sums in `Trusted.MirSemantics.MemoryState`, and full 5-stage compositional
  frame-preserving lifecycles.

All definitions are computable (`0` `noncomputable`, `0` `._unsafe_rec`,
`0` `omega`, `0` `decide`). Pure definitions and arithmetic/trie/ordinal
lemmas use zero axioms (`[]`); lemmas invoking `Nat.mod` / `BitVec` /
`Trusted.MirSemantics.encodeUInt` use at most `[propext]` (`0`
`Classical.choice`, `0` `Quot.sound`).
-/

namespace Anneal.WavefrontReclaim

open Trusted.MirAst Trusted.MirSemantics
open Anneal.CnfOrd Anneal.ByteSubLens Anneal.MirMemComp

/-! ## 1. Internal Arithmetic, List, and `CnfOrd` Helpers -/

private theorem boolFalseNeTrue (h : false = true) : False :=
  Bool.noConfusion h

private theorem boolTrueNeFalse (h : true = false) : False :=
  Bool.noConfusion h

private theorem bandIntro {a b : Bool} (ha : a = true) (hb : b = true) :
    (a && b) = true := by
  rw [ha, hb]; rfl

private theorem bandLeft {a b : Bool} (h : (a && b) = true) : a = true := by
  cases a with
  | false => exact False.elim (boolFalseNeTrue h)
  | true => rfl

private theorem bandRight {a b : Bool} (h : (a && b) = true) : b = true := by
  cases a with
  | false => exact False.elim (boolFalseNeTrue h)
  | true => exact h

private theorem borFalseElim {a b : Bool} (h : (a || b) = false) :
    a = false ∧ b = false := by
  cases a with
  | false => exact ⟨rfl, h⟩
  | true => exact False.elim (boolTrueNeFalse h)

private theorem trueOfBnotTrue {b : Bool} (h : (!b) = true) : b = false := by
  cases b with
  | false => rfl
  | true => exact False.elim (boolFalseNeTrue h)

private theorem natBeq_refl (a : Nat) : Nat.beq a a = true := by
  induction a with
  | zero => rfl
  | succ _ ih => exact ih

private theorem natBeq_symm (a b : Nat) : Nat.beq a b = Nat.beq b a := by
  revert b
  induction a with
  | zero => intro b; cases b <;> rfl
  | succ _ ih => intro b; cases b with | zero => rfl | succ b' => exact ih b'

private theorem natEq_of_beq (a b : Nat) (h : Nat.beq a b = true) : a = b := by
  revert b
  induction a with
  | zero =>
    intro b h
    cases b with
    | zero => rfl
    | succ _ => exact False.elim (boolFalseNeTrue h)
  | succ _ ih =>
    intro b h
    cases b with
    | zero => exact False.elim (boolFalseNeTrue h)
    | succ b' => exact congrArg Nat.succ (ih b' h)

private theorem natBle_refl (a : Nat) : Nat.ble a a = true := by
  induction a with
  | zero => rfl
  | succ _ ih => exact ih

private theorem natBle_zero_left (a : Nat) : Nat.ble 0 a = true := by
  cases a <;> rfl

private theorem natBle_succ_right (a b : Nat) (h : Nat.ble a b = true) :
    Nat.ble a (b + 1) = true := by
  revert b h
  induction a with
  | zero => intro _ _; rfl
  | succ _ ih =>
    intro b h
    cases b with
    | zero => exact False.elim (boolFalseNeTrue h)
    | succ b' => exact ih b' h

private theorem natBle_trans (a b c : Nat)
    (h1 : Nat.ble a b = true) (h2 : Nat.ble b c = true) :
    Nat.ble a c = true := by
  revert b c
  induction a with
  | zero => intro _ c _ _; exact natBle_zero_left c
  | succ _ ih =>
    intro b c h1 h2
    cases b with
    | zero => exact False.elim (boolFalseNeTrue h1)
    | succ b' =>
      cases c with
      | zero => exact False.elim (boolFalseNeTrue h2)
      | succ c' => exact ih b' c' h1 h2

private theorem natAdd_zero_left (a : Nat) : 0 + a = a := by
  induction a with
  | zero => rfl
  | succ _ ih => exact congrArg Nat.succ ih

private theorem natAdd_succ_left (a b : Nat) : (a + 1) + b = (a + b) + 1 := by
  induction b with
  | zero => rfl
  | succ _ ih => exact congrArg Nat.succ ih

private theorem natAdd_comm (a b : Nat) : a + b = b + a := by
  induction a with
  | zero => exact natAdd_zero_left b
  | succ a' ih =>
    exact Eq.trans (natAdd_succ_left a' b) (congrArg Nat.succ ih)

private theorem natAdd_assoc (a b c : Nat) : (a + b) + c = a + (b + c) := by
  induction c with
  | zero => rfl
  | succ _ ih => exact congrArg Nat.succ ih

private theorem natBle_add_mono_right (a b c : Nat) (h : Nat.ble a b = true) :
    Nat.ble (a + c) (b + c) = true := by
  induction c with
  | zero => exact h
  | succ _ ih => exact ih

private theorem natBle_add_mono_left (c a b : Nat) (h : Nat.ble a b = true) :
    Nat.ble (c + a) (c + b) = true := by
  rw [natAdd_comm c a, natAdd_comm c b]
  exact natBle_add_mono_right a b c h

private theorem natLtSuccSelf (a : Nat) : natLt a (a + 1) = true :=
  natBle_refl (a + 1)

private theorem natLtTrans (a b c : Nat)
    (h1 : natLt a b = true) (h2 : natLt b c = true) :
    natLt a c = true :=
  natBle_trans (a + 1) b c h1
    (natBle_trans b (b + 1) c (natBle_succ_right b b (natBle_refl b)) h2)

private theorem natLtOfLtOfBle (a b c : Nat)
    (h1 : natLt a b = true) (h2 : Nat.ble b c = true) :
    natLt a c = true :=
  natBle_trans (a + 1) b c h1 h2

private theorem natLt_add_left_of_lt (a b c : Nat) (h : natLt a b = true) :
    natLt (a + c) (b + c) = true := by
  dsimp only [natLt] at h
  dsimp only [natLt]
  rw [← natAdd_succ_left a c]
  exact natBle_add_mono_right (a + 1) b c h

private theorem natBeqFalseOfLt {a b : Nat} (h : natLt a b = true) :
    Nat.beq a b = false := by
  revert b h
  induction a with
  | zero =>
    intro b h
    cases b with
    | zero => exact False.elim (boolFalseNeTrue h)
    | succ _ => rfl
  | succ a' ih =>
    intro b h
    cases b with
    | zero => exact False.elim (boolFalseNeTrue h)
    | succ b' => exact ih h

private theorem natBleOfLtFalse (a b : Nat) (h : natLt a b = false) :
    Nat.ble b a = true := by
  revert b h
  induction a with
  | zero =>
    intro b h
    cases b with
    | zero => rfl
    | succ _ => exact False.elim (boolTrueNeFalse h)
  | succ a' ih =>
    intro b h
    cases b with
    | zero => rfl
    | succ b' => exact ih b' h

private theorem natBleAntisymm (a b : Nat)
    (h1 : Nat.ble a b = true) (h2 : Nat.ble b a = true) : a = b := by
  revert b
  induction a with
  | zero =>
    intro b _ h2
    cases b with
    | zero => rfl
    | succ _ => exact False.elim (boolFalseNeTrue h2)
  | succ a' ih =>
    intro b h1 h2
    cases b with
    | zero => exact False.elim (boolFalseNeTrue h1)
    | succ b' => exact congrArg Nat.succ (ih b' h1 h2)

private theorem natCmpLtToLt {a b : Nat} (h : natCmp a b = .lt) :
    natLt a b = true := by
  dsimp only [natCmp] at h
  cases hLt : natLt a b with
  | true => rfl
  | false =>
    rw [hLt] at h
    cases hGt : natLt b a with
    | true => rw [hGt] at h; cases h
    | false => rw [hGt] at h; cases h

private theorem natCmpEqEq {a b : Nat} (h : natCmp a b = .eq) : a = b := by
  dsimp only [natCmp] at h
  cases hLt : natLt a b with
  | true => rw [hLt] at h; cases h
  | false =>
    rw [hLt] at h
    cases hGt : natLt b a with
    | true => rw [hGt] at h; cases h
    | false =>
      exact natBleAntisymm a b (natBleOfLtFalse b a hGt) (natBleOfLtFalse a b
        hLt)

/-- Tail-preserving `List.foldr` helper (`0` `noncomputable`). -/
@[expose] def listFoldAux {α β : Type} (nil : β) (cons : α → List α → β → β)
    (xs : List α) : List α × β :=
  List.foldr (fun x acc => (x :: acc.1, cons x acc.1 acc.2)) ([], nil) xs

private theorem listFoldAux_fst {α β : Type} (nil : β)
    (cons : α → List α → β → β) (xs : List α) :
    (listFoldAux nil cons xs).1 = xs := by
  induction xs with
  | nil => rfl
  | cons x _ ih => exact congrArg (List.cons x) ih

/-- Tail-aware right fold over `xs` (`0` `noncomputable`). -/
@[expose] def listFold {α β : Type} (nil : β) (cons : α → List α → β → β)
    (xs : List α) : β :=
  (listFoldAux nil cons xs).2

private theorem listFold_cons {α β : Type} (nil : β)
    (cons : α → List α → β → β) (x : α) (tl : List α) :
    listFold nil cons (x :: tl) = cons x tl (listFold nil cons tl) := by
  dsimp only [listFold]
  change (cons x (listFoldAux nil cons tl).1 (listFoldAux nil cons tl).2) = _
  rw [listFoldAux_fst]

private theorem natMod_eq_of_lt (a b : Nat) (h : a < b) : Nat.mod a b = a :=
  Nat.mod_eq_of_lt h

private theorem cnfBle_of_lt (xs ys : CnfOrd) (h : cnfLt xs ys = true) :
    cnfBle xs ys = true := by
  dsimp only [cnfLt] at h
  dsimp only [cnfBle]
  cases hc : cnfCmp xs ys with
  | lt => rfl
  | eq => rfl
  | gt => rw [hc] at h; exact False.elim (boolFalseNeTrue h)

private theorem cnfLt_exists_coeff_drop (xs ys : CnfOrd)
    (hX : isCanonicalCnf xs = true) (hY : isCanonicalCnf ys = true)
    (hLt : cnfLt xs ys = true) :
    ∃ q0 : Nat,
      natLt (cnfCoeffAt q0 xs) (cnfCoeffAt q0 ys) = true ∧
      (∀ (q : Nat), natLt q0 q = true → cnfCoeffAt q xs = cnfCoeffAt q ys) := by
  revert ys hY hLt
  induction xs with
  | nil =>
    intro ys hY hLt
    cases ys with
    | nil => exact False.elim (boolFalseNeTrue hLt)
    | cons b ytl =>
      rw [isCanonicalCnf_cons] at hY
      have hbPos := bandLeft (bandLeft hY)
      have hbBel := bandRight (bandLeft hY)
      refine ⟨b.1, ?_, ?_⟩
      · rw [cnfCoeffAt_cons_head b ytl hbBel]
        exact hbPos
      · intro q hGt
        have hLe : Nat.ble b.1 q = true :=
          natBle_trans b.1 (b.1 + 1) q (natBle_succ_right _ _ (natBle_refl _))
            hGt
        rw [cnfCoeffAt_zero_of_allBelow q (b :: ytl) (bandIntro hGt
          (cnfAllBelow_mono b.1 q ytl hLe hbBel))]
        rfl
  | cons a xtl ih =>
    intro ys hY hLt
    rw [isCanonicalCnf_cons] at hX
    have haBel := bandRight (bandLeft hX)
    have hXtl := bandRight hX
    cases ys with
    | nil => exact False.elim (boolFalseNeTrue hLt)
    | cons b ytl =>
      rw [isCanonicalCnf_cons] at hY
      have hbPos := bandLeft (bandLeft hY)
      have hbBel := bandRight (bandLeft hY)
      have hYtl := bandRight hY
      dsimp only [cnfLt, cnfCmp, List.foldr, termCmp] at hLt
      cases hCmp1 : natCmp a.1 b.1 with
      | gt => rw [hCmp1] at hLt; exact False.elim (boolFalseNeTrue hLt)
      | lt =>
        have hab := natCmpLtToLt hCmp1
        have hLeAb : Nat.ble a.1 b.1 = true :=
          natBle_trans a.1 (a.1 + 1) b.1 (natBle_succ_right _ _ (natBle_refl
            _)) hab
        refine ⟨b.1, ?_, ?_⟩
        · rw [cnfCoeffAt_zero_of_allBelow b.1 (a :: xtl) (bandIntro hab
            (cnfAllBelow_mono a.1 b.1 xtl hLeAb haBel)),
            cnfCoeffAt_cons_head b ytl hbBel]
          exact hbPos
        · intro q hGt
          have hLeBq : Nat.ble b.1 q = true :=
            natBle_trans b.1 (b.1 +
              1) q (natBle_succ_right _ _ (natBle_refl _)) hGt
          have hAq : natLt a.1 q = true := natLtTrans a.1 b.1 q hab hGt
          have hLeAq : Nat.ble a.1 q = true :=
            natBle_trans a.1 b.1 q hLeAb hLeBq
          rw [cnfCoeffAt_zero_of_allBelow q (a :: xtl) (bandIntro hAq
            (cnfAllBelow_mono a.1 q xtl hLeAq haBel)),
            cnfCoeffAt_zero_of_allBelow q (b :: ytl) (bandIntro hGt
              (cnfAllBelow_mono b.1 q ytl hLeBq hbBel))]
      | eq =>
        rw [hCmp1] at hLt
        dsimp only at hLt
        have hab1 := natCmpEqEq hCmp1
        cases hCmp2 : natCmp a.2 b.2 with
        | gt => rw [hCmp2] at hLt; exact False.elim (boolFalseNeTrue hLt)
        | lt =>
          refine ⟨a.1, ?_, ?_⟩
          · rw [cnfCoeffAt_cons_head a xtl haBel, hab1,
              cnfCoeffAt_cons_head b ytl hbBel]
            exact natCmpLtToLt hCmp2
          · intro q hGt
            have hLeAq : Nat.ble a.1 q = true :=
              natBle_trans a.1 (a.1 +
                1) q (natBle_succ_right _ _ (natBle_refl _)) hGt
            have hBq : natLt b.1 q = true := by rw [← hab1]; exact hGt
            have hLeBq : Nat.ble b.1 q = true := by rw [← hab1]; exact hLeAq
            rw [cnfCoeffAt_zero_of_allBelow q (a :: xtl) (bandIntro hGt
              (cnfAllBelow_mono a.1 q xtl hLeAq haBel)),
              cnfCoeffAt_zero_of_allBelow q (b :: ytl) (bandIntro hBq
                (cnfAllBelow_mono b.1 q ytl hLeBq hbBel))]
        | eq =>
          rw [hCmp2] at hLt
          dsimp only at hLt
          have hab2 := natCmpEqEq hCmp2
          cases ih hXtl ytl hYtl (by dsimp only [cnfLt]; exact hLt) with
          | intro q0 hSub =>
            have hQ0LtA : natLt q0 a.1 = true := by
              cases hGe : natLt q0 a.1 with
              | true => rfl
              | false =>
                have hLeAq0 := natBleOfLtFalse q0 a.1 hGe
                have hLeBq0 : Nat.ble b.1 q0 = true := by
                  rw [← hab1]; exact hLeAq0
                have hZx := cnfCoeffAt_zero_of_allBelow q0 xtl
                  (cnfAllBelow_mono a.1 q0 xtl hLeAq0 haBel)
                have hZy := cnfCoeffAt_zero_of_allBelow q0 ytl
                  (cnfAllBelow_mono b.1 q0 ytl hLeBq0 hbBel)
                have hD := hSub.1
                rw [hZx, hZy] at hD
                exact False.elim (boolFalseNeTrue hD)
            have hNeA : Nat.beq a.1 q0 = false := by
              rw [natBeq_symm]
              exact natBeqFalseOfLt hQ0LtA
            refine ⟨q0, ?_, ?_⟩
            · change natLt
                (match Nat.beq a.1 q0 with
                 | true => a.2 + cnfCoeffAt q0 xtl
                 | false => cnfCoeffAt q0 xtl)
                (match Nat.beq b.1 q0 with
                 | true => b.2 + cnfCoeffAt q0 ytl
                 | false => cnfCoeffAt q0 ytl) = true
              rw [← hab1, hNeA]
              exact hSub.1
            · intro q hGt
              change
                (match Nat.beq a.1 q with
                 | true => a.2 + cnfCoeffAt q xtl
                 | false => cnfCoeffAt q xtl) =
                (match Nat.beq b.1 q with
                 | true => b.2 + cnfCoeffAt q ytl
                 | false => cnfCoeffAt q ytl)
              rw [← hab1, hab2, hSub.2 q hGt]

private theorem cnfLt_cnfNatAdd_left (a b c : CnfOrd)
    (hA : isCanonicalCnf a = true) (hB : isCanonicalCnf b = true)
    (hLt : cnfLt a b = true) :
    cnfLt (cnfNatAdd a c) (cnfNatAdd b c) = true := by
  cases cnfLt_exists_coeff_drop a b hA hB hLt with
  | intro q0 hQ0 =>
    apply cnfLt_of_coeff_drop _ _
      (isCanonicalCnf_cnfNatAdd a c) (isCanonicalCnf_cnfNatAdd b c) q0
    · rw [cnfCoeffAt_cnfNatAdd, cnfCoeffAt_cnfNatAdd]
      exact natLt_add_left_of_lt _ _ _ hQ0.1
    · intro q hGt
      rw [cnfCoeffAt_cnfNatAdd, cnfCoeffAt_cnfNatAdd, hQ0.2 q hGt]

private theorem cnfBle_cnfNatAdd_left (a b c : CnfOrd)
    (hA : isCanonicalCnf a = true) (hB : isCanonicalCnf b = true)
    (hLe : cnfBle a b = true) :
    cnfBle (cnfNatAdd a c) (cnfNatAdd b c) = true := by
  dsimp only [cnfBle] at hLe
  cases hc : cnfCmp a b with
  | gt => rw [hc] at hLe; exact False.elim (boolFalseNeTrue hLe)
  | eq =>
    rw [cnfCmp_eq_imp_eq a b hc]
    exact cnfBle_refl (cnfNatAdd b c)
  | lt =>
    exact cnfBle_of_lt _ _
      (cnfLt_cnfNatAdd_left a b c hA hB (by dsimp only [cnfLt]; rw [hc]))

private theorem cnfBle_cnfNatAdd_right (u a b : CnfOrd)
    (hA : isCanonicalCnf a = true) (hB : isCanonicalCnf b = true)
    (hLe : cnfBle a b = true) :
    cnfBle (cnfNatAdd u a) (cnfNatAdd u b) = true := by
  rw [cnfNatAdd_comm u a, cnfNatAdd_comm u b]
  exact cnfBle_cnfNatAdd_left a b u hA hB hLe

/-- Big-endian 4-byte `u32` allocation-byte slice via `Anneal.MirMemComp`. -/
@[expose] def wfEncodeU32BeSlice (v : Nat) : List AllocByte :=
  (execEncodeUInt .big 4 v).map (fun b => AllocByte.init b none)

/-- `wfEncodeU32BeSlice` always produces 4 bytes (`[]`). -/
theorem wfEncodeU32BeSlice_length (v : Nat) :
    (wfEncodeU32BeSlice v).length = 4 := rfl

/-- Exact bridge from `wfEncodeU32BeSlice` to `Trusted.MirSemantics.encodeUInt`
(`[]`). -/
theorem wfEncodeU32BeSlice_eq_trusted (v : Nat) :
    wfEncodeU32BeSlice v =
      (encodeUInt .big 4 v).map (fun b => AllocByte.init b none) := by
  unfold wfEncodeU32BeSlice
  rw [execEncodeUInt_eq]

/-- Modulus `2^32` (`4294967296`) for wrapping `u32` loan accumulation. -/
@[expose] def u32Modulus : Nat := 4294967296

/-- Reduces `v` modulo `u32Modulus` (`2^32`). -/
@[expose] def wrapU32 (v : Nat) : Nat := Nat.mod v u32Modulus

/-- Idempotence of `wrapU32`. -/
theorem wrapU32_idem (v : Nat) : wrapU32 (wrapU32 v) = wrapU32 v :=
  natMod_eq_of_lt (wrapU32 v) u32Modulus (Nat.mod_lt v (Nat.le_of_ble_eq_true
    rfl))

/-- Left modular-addition absorption `wrapU32 (wrapU32 a + b) = wrapU32 (a +
b)`. -/
theorem wrapU32_add_left (a b : Nat) : wrapU32 (wrapU32 a + b) =
    wrapU32 (a + b) := by
  dsimp only [wrapU32]
  have hDivMod : u32Modulus * Nat.div a u32Modulus + Nat.mod a u32Modulus = a :=
    Nat.div_add_mod a u32Modulus
  have h1 : Nat.mod (u32Modulus * Nat.div a u32Modulus + (Nat.mod a u32Modulus +
    b)) u32Modulus =
      Nat.mod (Nat.mod a u32Modulus + b) u32Modulus :=
    Nat.mul_add_mod_self_left u32Modulus (Nat.div a u32Modulus) (Nat.mod a
      u32Modulus + b)
  rw [← natAdd_assoc (u32Modulus * Nat.div a u32Modulus) (Nat.mod a u32Modulus)
    b, hDivMod] at h1
  exact h1.symm

/-- Lifecycle phase of a tracked sub-slice loan (`.activeMut`, `.frozen`,
`.spatialCheckedOut scopeId`, or `.ended`). -/
inductive WfLoanPhase where
  | activeMut
  | frozen
  | spatialCheckedOut (scopeId : Nat)
  | ended

/-- Returns `true` iff the loan phase is not `.ended`. -/
@[expose] def loanPhaseIsLive (ph : WfLoanPhase) : Bool :=
  match ph with
  | .ended => false
  | .activeMut | .frozen | .spatialCheckedOut _ => true

/-- Returns `true` iff `ph = .spatialCheckedOut sc`. -/
@[expose] def loanPhaseMatchesScope (ph : WfLoanPhase) (sc : Nat) : Bool :=
  match ph with
  | .spatialCheckedOut s => Nat.beq s sc
  | .activeMut | .frozen | .ended => false

/-- Tracked `&mut` 4-byte loan entry coupling slot `id`, `phase`, `ByteSubLens`,
and `u32` value `val`. -/
structure WfLoanEntry where
  id : Pos4
  phase : WfLoanPhase
  lens : ByteSubLens
  val : Nat

/-- Looks up the first loan entry with identifier `lid` in `loans`. -/
@[expose] def wfFindLoan (lid : Pos4) (loans : List WfLoanEntry) : Option
    WfLoanEntry :=
  loans.foldr
    (fun e acc =>
      match Pos4.beq e.id lid with
      | true => some e
      | false => acc)
    none

/-- Pure-lifted access check on a loan table (reads allow `.activeMut` and
`.frozen`;
writes require `.activeMut`). -/
@[expose] def wfCanPureAccessLoan (loans : List WfLoanEntry) (lid : Pos4)
    (isWrite : Bool) : Bool :=
  match wfFindLoan lid loans with
  | none => false
  | some e =>
    match e.phase with
    | .activeMut => true
    | .frozen => !isWrite
    | .spatialCheckedOut _ | .ended => false

/-- Updates the `phase` and `val` of loan `lid` in `loans`. -/
@[expose] def wfSetLoanEntryAt (loans : List WfLoanEntry) (lid : Pos4) (ph :
    WfLoanPhase)
    (newVal : Nat) : List WfLoanEntry :=
  loans.map (fun e =>
    match Pos4.beq e.id lid with
    | true => ⟨e.id, ph, e.lens, newVal⟩
    | false => e)

private theorem wfFindLoan_wfSetLoanEntryAt_same (loans : List WfLoanEntry)
    (lid : Pos4)
    (ph : WfLoanPhase) (newVal : Nat) (e : WfLoanEntry)
    (hFind : wfFindLoan lid loans = some e) :
    wfFindLoan lid (wfSetLoanEntryAt loans lid ph newVal) =
      some ⟨e.id, ph, e.lens, newVal⟩ := by
  induction loans with
  | nil => nomatch hFind
  | cons hd tl ih =>
    dsimp only [wfFindLoan, List.foldr] at hFind
    dsimp only [wfSetLoanEntryAt, List.map, wfFindLoan, List.foldr]
    cases hEq : Pos4.beq hd.id lid with
    | true =>
      rw [hEq] at hFind
      injection hFind with hSame
      rw [← hSame]
      dsimp only
      rw [hEq]
    | false =>
      rw [hEq] at hFind
      dsimp only
      rw [hEq]
      exact ih hFind

private theorem wfFindLoan_wfSetLoanEntryAt_ne (loans : List WfLoanEntry) (lid
    lid2 : Pos4)
    (ph : WfLoanPhase) (newVal : Nat) (hNe : Pos4.beq lid lid2 = false) :
    wfFindLoan lid2 (wfSetLoanEntryAt loans lid ph newVal) =
      wfFindLoan lid2 loans := by
  induction loans with
  | nil => rfl
  | cons hd tl ih =>
    dsimp only [wfSetLoanEntryAt, List.map, wfFindLoan, List.foldr]
    cases hEq1 : Pos4.beq hd.id lid with
    | true =>
      dsimp only
      have hSame := pos4_eq_of_beq hd.id lid hEq1
      rw [hSame, hNe]
      exact ih
    | false =>
      dsimp only
      cases Pos4.beq hd.id lid2 with
      | true => rfl
      | false => exact ih

private theorem wfFindLoan_wfSetLoanEntryAt_preserves_none (loans : List
    WfLoanEntry) (q lid : Pos4)
    (ph : WfLoanPhase) (newVal : Nat) (hNone : wfFindLoan q loans = none) :
    wfFindLoan q (wfSetLoanEntryAt loans lid ph newVal) = none := by
  induction loans with
  | nil => rfl
  | cons hd tl ih =>
    dsimp only [wfFindLoan, List.foldr] at hNone
    dsimp only [wfSetLoanEntryAt, List.map, wfFindLoan, List.foldr]
    cases hEqQ : Pos4.beq hd.id q with
    | true => rw [hEqQ] at hNone; nomatch hNone
    | false =>
      rw [hEqQ] at hNone
      cases Pos4.beq hd.id lid with
      | true => dsimp only; rw [hEqQ]; exact ih hNone
      | false => dsimp only; rw [hEqQ]; exact ih hNone

private theorem wfSetLoanEntryAt_of_wfFindLoan_none (loans : List WfLoanEntry)
    (lid : Pos4)
    (ph : WfLoanPhase) (newVal : Nat) (hNone : wfFindLoan lid loans = none) :
    wfSetLoanEntryAt loans lid ph newVal = loans := by
  induction loans with
  | nil => rfl
  | cons hd tl ih =>
    dsimp only [wfFindLoan, List.foldr] at hNone
    dsimp only [wfSetLoanEntryAt, List.map]
    cases hEq : Pos4.beq hd.id lid with
    | true => rw [hEq] at hNone; nomatch hNone
    | false =>
      rw [hEq] at hNone
      exact congrArg (List.cons hd) (ih hNone)

/-- Asserts that `L` is byte-disjoint from every loan lens in `tl`. -/
@[expose] def allDisjointFromLens (L : ByteSubLens) (tl : List WfLoanEntry) :
    Prop :=
  tl.foldr (fun e' acc => byteLensDisjoint L e'.lens = true ∧ acc) True

private theorem allDisjointFromLens_wfSetLoanEntryAt (L : ByteSubLens) (tl :
    List WfLoanEntry)
    (lid : Pos4) (ph : WfLoanPhase) (newVal : Nat)
    (hDisj : allDisjointFromLens L tl) :
    allDisjointFromLens L (wfSetLoanEntryAt tl lid ph newVal) := by
  induction tl with
  | nil => exact True.intro
  | cons hd rest ih =>
    dsimp only [allDisjointFromLens, List.foldr] at hDisj
    dsimp only [wfSetLoanEntryAt, List.map, allDisjointFromLens, List.foldr]
    cases Pos4.beq hd.id lid with
    | true => exact ⟨hDisj.1, ih hDisj.2⟩
    | false => exact ⟨hDisj.1, ih hDisj.2⟩

private theorem allDisjointFromLens_wfFindLoan (L : ByteSubLens) (tl : List
    WfLoanEntry)
    (lid : Pos4) (e : WfLoanEntry)
    (hDisj : allDisjointFromLens L tl) (hFind : wfFindLoan lid tl = some e) :
    byteLensDisjoint L e.lens = true := by
  induction tl with
  | nil => nomatch hFind
  | cons hd rest ih =>
    dsimp only [allDisjointFromLens, List.foldr] at hDisj
    dsimp only [wfFindLoan, List.foldr] at hFind
    cases hEq : Pos4.beq hd.id lid with
    | true =>
      rw [hEq] at hFind
      injection hFind with hSame
      rw [← hSame]
      exact hDisj.1
    | false =>
      rw [hEq] at hFind
      exact ih hDisj.2 hFind

/-- Couples `loans` to `MemoryState`: unique `Pos4` IDs, pairwise-disjoint
4-byte `ByteSubLens` slices, `val < 2^32`, and exact big-endian byte agreement
in `m` for live (non-`.ended`) loans. -/
@[expose] def LoansSyncedWithMem (loans : List WfLoanEntry) (m : MemoryState) :
    Prop :=
  listFold True
    (fun e tl acc =>
      wfFindLoan e.id tl = none ∧
      allDisjointFromLens e.lens tl ∧
      e.lens.size = 4 ∧
      e.val = wrapU32 e.val ∧
      (match loanPhaseIsLive e.phase with
       | false => True
       | true => byteSubLensGet e.lens m = some (wfEncodeU32BeSlice e.val)) ∧
      acc)
    loans

private theorem loansSyncedWithMem_cons (e : WfLoanEntry) (tl : List
    WfLoanEntry) (m : MemoryState) :
    LoansSyncedWithMem (e :: tl) m =
      (wfFindLoan e.id tl = none ∧
       allDisjointFromLens e.lens tl ∧
       e.lens.size = 4 ∧
       e.val = wrapU32 e.val ∧
       (match loanPhaseIsLive e.phase with
        | false => True
        | true => byteSubLensGet e.lens m = some (wfEncodeU32BeSlice e.val)) ∧
       LoansSyncedWithMem tl m) :=
  listFold_cons _ _ e tl

private theorem wfFindLoan_synced_live_props (loans : List WfLoanEntry) (m :
    MemoryState)
    (lid : Pos4) (e : WfLoanEntry)
    (hSync : LoansSyncedWithMem loans m)
    (hFind : wfFindLoan lid loans = some e)
    (hLive : loanPhaseIsLive e.phase = true) :
    e.id = lid ∧
    e.lens.size = 4 ∧
    e.val = wrapU32 e.val ∧
    byteSubLensGet e.lens m = some (wfEncodeU32BeSlice e.val) := by
  induction loans with
  | nil => nomatch hFind
  | cons hd tl ih =>
    rw [loansSyncedWithMem_cons] at hSync
    dsimp only [wfFindLoan, List.foldr] at hFind
    cases hEq : Pos4.beq hd.id lid with
    | true =>
      rw [hEq] at hFind
      injection hFind with hSame
      rw [← hSame]
      have hMem := hSync.2.2.2.2.1
      rw [← hSame] at hLive
      rw [hLive] at hMem
      exact ⟨pos4_eq_of_beq hd.id lid hEq, hSync.2.2.1, hSync.2.2.2.1, hMem⟩
    | false =>
      rw [hEq] at hFind
      exact ih hSync.2.2.2.2.2 hFind

private theorem loansSyncedWithMem_put_disjoint (L : ByteSubLens) (loans : List
    WfLoanEntry)
    (m mOut : MemoryState) (bs : List AllocByte)
    (hDisj : allDisjointFromLens L loans)
    (hPut : byteSubLensPut L m bs = some mOut)
    (hSync : LoansSyncedWithMem loans m) :
    LoansSyncedWithMem loans mOut := by
  induction loans with
  | nil => exact True.intro
  | cons hd tl ih =>
    dsimp only [allDisjointFromLens, List.foldr] at hDisj
    rw [loansSyncedWithMem_cons] at hSync
    rw [loansSyncedWithMem_cons]
    refine ⟨hSync.1, hSync.2.1, hSync.2.2.1, hSync.2.2.2.1, ?_,
      ih hDisj.2 hSync.2.2.2.2.2⟩
    cases hLv : loanPhaseIsLive hd.phase with
    | false => exact True.intro
    | true =>
      have hM := hSync.2.2.2.2.1
      rw [hLv] at hM
      rw [byteSubLens_get_put_disjoint L hd.lens m mOut bs hDisj.1 hPut]
      exact hM

private theorem loansSyncedWithMem_setPhase_sameVal (loans : List WfLoanEntry)
    (m : MemoryState)
    (lid : Pos4) (e : WfLoanEntry) (newPh : WfLoanPhase)
    (hSync : LoansSyncedWithMem loans m)
    (hFind : wfFindLoan lid loans = some e)
    (hOldLive : loanPhaseIsLive e.phase = true)
    (hNewLive : loanPhaseIsLive newPh = true) :
    LoansSyncedWithMem (wfSetLoanEntryAt loans lid newPh e.val) m := by
  induction loans with
  | nil => nomatch hFind
  | cons hd tl ih =>
    rw [loansSyncedWithMem_cons] at hSync
    dsimp only [wfFindLoan, List.foldr] at hFind
    dsimp only [wfSetLoanEntryAt, List.map]
    cases hEq : Pos4.beq hd.id lid with
    | true =>
      rw [hEq] at hFind
      injection hFind with hSame
      have hIdEq := pos4_eq_of_beq hd.id lid hEq
      have hNoneLid : wfFindLoan lid tl = none := by rw [← hIdEq]; exact hSync.1
      have hTlEq : wfSetLoanEntryAt tl lid newPh e.val = tl :=
        wfSetLoanEntryAt_of_wfFindLoan_none tl lid newPh e.val hNoneLid
      change LoansSyncedWithMem (⟨hd.id, newPh, hd.lens,
        e.val⟩ :: wfSetLoanEntryAt tl lid newPh e.val) m
      rw [hTlEq, loansSyncedWithMem_cons]
      have hMem := hSync.2.2.2.2.1
      rw [hSame, hOldLive] at hMem
      rw [← hSame] at hMem
      refine ⟨hSync.1, hSync.2.1, hSync.2.2.1, ?_, ?_, hSync.2.2.2.2.2⟩
      · rw [← hSame]; exact hSync.2.2.2.1
      · dsimp only; rw [hNewLive, ← hSame]; exact hMem
    | false =>
      rw [hEq] at hFind
      change LoansSyncedWithMem (hd :: wfSetLoanEntryAt tl lid newPh e.val) m
      rw [loansSyncedWithMem_cons]
      exact ⟨wfFindLoan_wfSetLoanEntryAt_preserves_none tl hd.id lid newPh
        e.val hSync.1,
        allDisjointFromLens_wfSetLoanEntryAt hd.lens tl lid newPh e.val
          hSync.2.1,
        hSync.2.2.1, hSync.2.2.2.1, hSync.2.2.2.2.1, ih hSync.2.2.2.2.2 hFind⟩

private theorem loansSyncedWithMem_set_and_put (loans : List WfLoanEntry) (m
    mOut : MemoryState)
    (lid : Pos4) (e : WfLoanEntry) (newPh : WfLoanPhase) (newVal : Nat)
    (hSync : LoansSyncedWithMem loans m)
    (hFind : wfFindLoan lid loans = some e)
    (hNewLive : loanPhaseIsLive newPh = true)
    (hWrap : newVal = wrapU32 newVal)
    (hPut : byteSubLensPut e.lens m (wfEncodeU32BeSlice newVal) = some mOut) :
    LoansSyncedWithMem (wfSetLoanEntryAt loans lid newPh newVal) mOut := by
  induction loans with
  | nil => nomatch hFind
  | cons hd tl ih =>
    rw [loansSyncedWithMem_cons] at hSync
    dsimp only [wfFindLoan, List.foldr] at hFind
    dsimp only [wfSetLoanEntryAt, List.map]
    cases hEq : Pos4.beq hd.id lid with
    | true =>
      rw [hEq] at hFind
      injection hFind with hSame
      have hIdEq := pos4_eq_of_beq hd.id lid hEq
      have hNoneLid : wfFindLoan lid tl = none := by rw [← hIdEq]; exact hSync.1
      have hTlEq : wfSetLoanEntryAt tl lid newPh newVal = tl :=
        wfSetLoanEntryAt_of_wfFindLoan_none tl lid newPh newVal hNoneLid
      change LoansSyncedWithMem (⟨hd.id, newPh, hd.lens,
        newVal⟩ :: wfSetLoanEntryAt tl lid newPh newVal) mOut
      rw [hTlEq, loansSyncedWithMem_cons]
      rw [← hSame] at hPut
      refine ⟨hSync.1, hSync.2.1, hSync.2.2.1, hWrap, ?_,
        loansSyncedWithMem_put_disjoint hd.lens tl m mOut _ hSync.2.1 hPut
          hSync.2.2.2.2.2⟩
      dsimp only
      rw [hNewLive]
      exact byteSubLens_put_get hd.lens m mOut (wfEncodeU32BeSlice newVal) hPut
    | false =>
      rw [hEq] at hFind
      change LoansSyncedWithMem (hd :: wfSetLoanEntryAt tl lid newPh newVal)
        mOut
      rw [loansSyncedWithMem_cons]
      have hDisjHdE : byteLensDisjoint hd.lens e.lens = true :=
        allDisjointFromLens_wfFindLoan hd.lens tl lid e hSync.2.1 hFind
      have hDisjEHd : byteLensDisjoint e.lens hd.lens = true := by
        rw [byteLensDisjoint_symm]; exact hDisjHdE
      refine ⟨wfFindLoan_wfSetLoanEntryAt_preserves_none tl hd.id lid newPh
        newVal hSync.1,
        allDisjointFromLens_wfSetLoanEntryAt hd.lens tl lid newPh newVal
          hSync.2.1,
        hSync.2.2.1, hSync.2.2.2.1, ?_, ih hSync.2.2.2.2.2 hFind⟩
      cases hLv : loanPhaseIsLive hd.phase with
      | false => exact True.intro
      | true =>
        have hM := hSync.2.2.2.2.1
        rw [hLv] at hM
        rw [byteSubLens_get_put_disjoint e.lens hd.lens m mOut _ hDisjEHd hPut]
        exact hM

/-! ## 2. Coupled `WavefrontWorld`, `WorldMatches`, and `HybridCmd` -/

/-- Queued wavefront worker task carrying `taskId`, `rank`, remaining yields
`remYields`, target `loanId`, `scopeId`, and leaf `writeDelta`. -/
structure WorkerTask where
  taskId : Nat
  rank : Nat
  remYields : Nat
  loanId : Pos4
  scopeId : Nat
  writeDelta : Nat

/-- Concrete machine state coupling `mem`, `loans`, spatial `cells`,
`fifoQueue`, `stealDeque`, `nextTaskId`, `completedCount`, and `stepCount`. -/
structure WavefrontWorld where
  mem : MemoryState
  loans : List WfLoanEntry
  cells : ResTrie Nat
  fifoQueue : List WorkerTask
  stealDeque : List WorkerTask
  nextTaskId : Nat
  completedCount : Nat
  stepCount : Nat

/-- Returns `true` if any task in `qs` targets `lid`. -/
@[expose] def anyTaskHasLoan (lid : Pos4) (qs : List WorkerTask) : Bool :=
  qs.foldr (fun t acc => Pos4.beq t.loanId lid || acc) false

/-- Returns `true` if any task in `qs` targets `(lid, sc)`. -/
@[expose] def anyTaskHasLoanScope (lid : Pos4) (sc : Nat) (qs : List WorkerTask)
    : Bool :=
  qs.foldr (fun t acc => (Pos4.beq t.loanId lid && Nat.beq t.scopeId sc) ||
    acc) false

private theorem anyTaskHasLoan_append (lid : Pos4) (xs ys : List WorkerTask) :
    anyTaskHasLoan lid (xs ++ ys) = (anyTaskHasLoan lid xs ||
      anyTaskHasLoan lid ys) := by
  induction xs with
  | nil => rfl
  | cons hd tl ih =>
    change (Pos4.beq hd.loanId lid || anyTaskHasLoan lid (tl ++ ys)) =
      ((Pos4.beq hd.loanId lid || anyTaskHasLoan lid tl) ||
        anyTaskHasLoan lid ys)
    rw [ih]
    cases Pos4.beq hd.loanId lid <;> rfl

/-- Every queued task in `qs` targets a live loan in `loans` whose phase is
`.spatialCheckedOut t.scopeId`. -/
@[expose] def queueMatchesLoansBool (qs : List WorkerTask) (loans : List
    WfLoanEntry) :
    Bool :=
  qs.foldr
    (fun t acc =>
      (match wfFindLoan t.loanId loans with
       | none => false
       | some e => loanPhaseMatchesScope e.phase t.scopeId) && acc)
    true

/-- Checks that every queued task in `fifoQueue` and `stealDeque` references a
live `.spatialCheckedOut` loan with matching `scopeId`. -/
@[expose] def checkQueueMatchesLoansBool (w : WavefrontWorld) : Bool :=
  queueMatchesLoansBool w.fifoQueue w.loans &&
    queueMatchesLoansBool w.stealDeque w.loans

/-- Propositional wrapper `checkQueueMatchesLoansBool w = true`. -/
@[expose] def QueueMatchesLoans (w : WavefrontWorld) : Prop :=
  checkQueueMatchesLoansBool w = true

private theorem queueMatchesLoansBool_append (xs ys : List WorkerTask) (loans :
    List WfLoanEntry) :
    queueMatchesLoansBool (xs ++ ys) loans =
      (queueMatchesLoansBool xs loans && queueMatchesLoansBool ys loans) := by
  induction xs with
  | nil => rfl
  | cons hd tl ih =>
    change (_ && queueMatchesLoansBool (tl ++ ys) loans) =
      ((_ && queueMatchesLoansBool tl loans) && queueMatchesLoansBool ys loans)
    rw [ih]
    cases
      (match wfFindLoan hd.loanId loans with
       | none => false
       | some e => loanPhaseMatchesScope e.phase hd.scopeId) <;> rfl

private theorem not_anyTaskHasLoan_of_activeMut (lid : Pos4) (e : WfLoanEntry)
    (qs : List WorkerTask) (loans : List WfLoanEntry)
    (hFind : wfFindLoan lid loans = some e)
    (hPh : e.phase = .activeMut)
    (hQ : queueMatchesLoansBool qs loans = true) :
    anyTaskHasLoan lid qs = false := by
  induction qs with
  | nil => rfl
  | cons t tl ih =>
    dsimp only [queueMatchesLoansBool, List.foldr] at hQ
    dsimp only [anyTaskHasLoan, List.foldr]
    cases hEq : Pos4.beq t.loanId lid with
    | false => exact ih (bandRight hQ)
    | true =>
      have hSame := pos4_eq_of_beq t.loanId lid hEq
      have hHd := bandLeft hQ
      rw [hSame, hFind] at hHd
      dsimp only at hHd
      rw [hPh] at hHd
      exact False.elim (boolFalseNeTrue hHd)

private theorem queueMatchesLoansBool_wfSetLoanEntryAt_of_not_hasLoan
    (qs : List WorkerTask) (loans : List WfLoanEntry)
    (lid : Pos4) (ph : WfLoanPhase) (newVal : Nat)
    (hNo : anyTaskHasLoan lid qs = false)
    (hQ : queueMatchesLoansBool qs loans = true) :
    queueMatchesLoansBool qs (wfSetLoanEntryAt loans lid ph newVal) = true := by
  induction qs with
  | nil => rfl
  | cons t tl ih =>
    dsimp only [anyTaskHasLoan, List.foldr] at hNo
    have hSp := borFalseElim hNo
    dsimp only [queueMatchesLoansBool, List.foldr] at hQ
    dsimp only [queueMatchesLoansBool, List.foldr]
    have hNeSymm : Pos4.beq lid t.loanId = false := by
      rw [pos4_beq_symm]; exact hSp.1
    rw [wfFindLoan_wfSetLoanEntryAt_ne loans lid t.loanId ph newVal hNeSymm]
    exact bandIntro (bandLeft hQ) (ih hSp.2 (bandRight hQ))

private theorem queueMatchesLoansBool_wfSetLoanEntryAt_samePhase
    (qs : List WorkerTask) (loans : List WfLoanEntry)
    (lid : Pos4) (e : WfLoanEntry) (newVal : Nat)
    (hFind : wfFindLoan lid loans = some e)
    (hQ : queueMatchesLoansBool qs loans = true) :
    queueMatchesLoansBool qs (wfSetLoanEntryAt loans lid e.phase newVal) =
      true := by
  induction qs with
  | nil => rfl
  | cons t tl ih =>
    dsimp only [queueMatchesLoansBool, List.foldr] at hQ
    dsimp only [queueMatchesLoansBool, List.foldr]
    cases hEq : Pos4.beq lid t.loanId with
    | true =>
      have hSame := pos4_eq_of_beq lid t.loanId hEq
      rw [← hSame, wfFindLoan_wfSetLoanEntryAt_same loans lid e.phase newVal e
        hFind]
      have hHd := bandLeft hQ
      rw [← hSame, hFind] at hHd
      exact bandIntro hHd (ih (bandRight hQ))
    | false =>
      rw [wfFindLoan_wfSetLoanEntryAt_ne loans lid t.loanId e.phase newVal hEq]
      exact bandIntro (bandLeft hQ) (ih (bandRight hQ))

private theorem anyTaskHasLoanScope_eq_anyTaskHasLoan_of_queueMatches
    (lid : Pos4) (sc : Nat) (e : WfLoanEntry) (qs : List WorkerTask) (loans :
      List WfLoanEntry)
    (hFind : wfFindLoan lid loans = some e)
    (hPh : e.phase = .spatialCheckedOut sc)
    (hQ : queueMatchesLoansBool qs loans = true) :
    anyTaskHasLoanScope lid sc qs = anyTaskHasLoan lid qs := by
  induction qs with
  | nil => rfl
  | cons t tl ih =>
    dsimp only [queueMatchesLoansBool, List.foldr] at hQ
    change ((Pos4.beq t.loanId lid && Nat.beq t.scopeId sc) ||
      anyTaskHasLoanScope lid sc tl) =
      (Pos4.beq t.loanId lid || anyTaskHasLoan lid tl)
    rw [ih (bandRight hQ)]
    cases hEq : Pos4.beq t.loanId lid with
    | false => rfl
    | true =>
      have hSame := pos4_eq_of_beq t.loanId lid hEq
      have hHd := bandLeft hQ
      rw [hSame, hFind] at hHd
      dsimp only at hHd
      rw [hPh] at hHd
      dsimp only [loanPhaseMatchesScope] at hHd
      have hScSymm : Nat.beq t.scopeId sc = true := by
        rw [natBeq_symm]; exact hHd
      rw [hScSymm]
      rfl

/-- Coefficient contributed by task `t` at Cantor Normal Form exponent `q` (`1`
at `2*rank + 1` plus `remYields` at `2*rank`). -/
@[expose] def wfTaskWeightAt (q : Nat) (t : WorkerTask) : Nat :=
  (match Nat.beq (t.rank + t.rank + 1) q with | true => 1 | false => 0) +
  (match Nat.beq (t.rank + t.rank) q with | true => t.remYields | false => 0)

/-- Total coefficient summed across `qs` at exponent `q`. -/
@[expose] def wfTasksWeightAt (q : Nat) (qs : List WorkerTask) : Nat :=
  qs.foldr (fun t acc => wfTaskWeightAt q t + acc) 0

/-- Adds task `t`'s ordinal weight `ω^(2*rank + 1) + ω^(2*rank) * remYields`
into canonical CNF accumulator `acc`. -/
@[expose] def wfTaskMeasure (t : WorkerTask) (acc : CnfOrd) : CnfOrd :=
  cnfAddTerm (t.rank + t.rank + 1) 1 (cnfAddTerm (t.rank +
    t.rank) t.remYields acc)

/-- Single-task `< ω^ω` ordinal weight `ω^(2*rank + 1) + ω^(2*rank) *
remYields`. -/
@[expose] def burstTaskDelta (rank remYields : Nat) : CnfOrd :=
  cnfAddTerm (rank + rank + 1) 1 (cnfAddTerm (rank + rank) remYields [])

/-- Folds `wfTaskMeasure` across `qs` onto `init`. -/
@[expose] def wfQueueMeasure (qs : List WorkerTask) (init : CnfOrd) : CnfOrd :=
  qs.foldr wfTaskMeasure init

/-- Total `< ω^ω` Cantor Normal Form ordinal measure of `w.fifoQueue` and
`w.stealDeque`. -/
@[expose] def worldMeasure (w : WavefrontWorld) : CnfOrd :=
  wfQueueMeasure w.fifoQueue (wfQueueMeasure w.stealDeque [])

private theorem wfTasksWeightAt_append (q : Nat) (xs ys : List WorkerTask) :
    wfTasksWeightAt q (xs ++ ys) = wfTasksWeightAt q xs +
      wfTasksWeightAt q ys := by
  induction xs with
  | nil => exact Eq.symm (natAdd_zero_left (wfTasksWeightAt q ys))
  | cons hd _ ih =>
    change wfTaskWeightAt q hd + wfTasksWeightAt q (_ ++ ys) =
      (wfTaskWeightAt q hd + wfTasksWeightAt q _) + wfTasksWeightAt q ys
    rw [ih, natAdd_assoc]

private theorem wfQueueMeasure_canonical_and_coeff (q : Nat) (qs : List
    WorkerTask)
    (init : CnfOrd) (hInit : isCanonicalCnf init = true) :
    isCanonicalCnf (wfQueueMeasure qs init) = true ∧
    cnfCoeffAt q (wfQueueMeasure qs init) =
      wfTasksWeightAt q qs + cnfCoeffAt q init := by
  induction qs with
  | nil => exact ⟨hInit, Eq.symm (natAdd_zero_left (cnfCoeffAt q init))⟩
  | cons t _ ih =>
    exact ⟨isCanonicalCnf_cnfAddTerm (t.rank + t.rank + 1) 1 _
      (isCanonicalCnf_cnfAddTerm (t.rank + t.rank) t.remYields _ ih.1),
      Eq.trans (cnfCoeffAt_cnfAddTerm q (t.rank + t.rank + 1) 1 _)
        (Eq.trans (congrArg (Nat.add _) (cnfCoeffAt_cnfAddTerm q (t.rank +
          t.rank) t.remYields _))
          (Eq.trans (Eq.symm (natAdd_assoc _ _ _))
            (Eq.trans (congrArg (Nat.add (wfTaskWeightAt q t)) ih.2)
              (Eq.symm (natAdd_assoc _ _ _)))))⟩

/-- Every `worldMeasure w` is in canonical Cantor Normal Form (`isCanonicalCnf =
true`). -/
theorem worldMeasure_canonical (w : WavefrontWorld) :
    isCanonicalCnf (worldMeasure w) = true :=
  (wfQueueMeasure_canonical_and_coeff 0 w.fifoQueue _
    (wfQueueMeasure_canonical_and_coeff 0 w.stealDeque [] rfl).1).1

private theorem cnfCoeffAt_worldMeasure (q : Nat) (w : WavefrontWorld) :
    cnfCoeffAt q (worldMeasure w) =
      wfTasksWeightAt q w.fifoQueue + wfTasksWeightAt q w.stealDeque := by
  have hS := wfQueueMeasure_canonical_and_coeff q w.stealDeque [] rfl
  exact Eq.trans (wfQueueMeasure_canonical_and_coeff q w.fifoQueue _ hS.1).2
    (congrArg (Nat.add (wfTasksWeightAt q w.fifoQueue)) hS.2)

private theorem burstTaskDelta_canonical (rank remYields : Nat) :
    isCanonicalCnf (burstTaskDelta rank remYields) = true :=
  isCanonicalCnf_cnfAddTerm (rank + rank + 1) 1 _
    (isCanonicalCnf_cnfAddTerm (rank + rank) remYields [] rfl)

private theorem burstTaskDelta_pos (rank remYields : Nat) :
    cnfLt [] (burstTaskDelta rank remYields) = true := by
  apply cnfLt_of_coeff_drop [] (burstTaskDelta rank remYields) rfl
    (burstTaskDelta_canonical rank remYields) (rank + rank + 1)
  · dsimp only [burstTaskDelta]
    rw [cnfCoeffAt_cnfAddTerm, cnfCoeffAt_cnfAddTerm,
      natBeq_refl (rank + rank + 1)]
    have hNe : Nat.beq (rank + rank) (rank + rank + 1) = false :=
      natBeqFalseOfLt (natLtSuccSelf (rank + rank))
    rw [hNe]
    rfl
  · intro q hGt
    dsimp only [burstTaskDelta]
    rw [cnfCoeffAt_cnfAddTerm, cnfCoeffAt_cnfAddTerm, natBeqFalseOfLt hGt,
      natBeqFalseOfLt (natLtTrans (rank + rank) (rank + rank +
        1) q (natLtSuccSelf _) hGt)]
    rfl

private theorem wfTaskMeasure_eq_cnfAddOrd_burstTaskDelta (t : WorkerTask) (acc
    : CnfOrd)
    (hAcc : isCanonicalCnf acc = true) :
    wfTaskMeasure t acc = cnfAddOrd (burstTaskDelta t.rank t.remYields) acc :=
      by
  apply cnf_eq_of_coeff_eq _ _
    (isCanonicalCnf_cnfAddTerm _ _ _ (isCanonicalCnf_cnfAddTerm _ _ _ hAcc))
    (isCanonicalCnf_cnfNatAdd _ acc)
  intro q
  dsimp only [wfTaskMeasure, burstTaskDelta, cnfAddOrd]
  rw [cnfCoeffAt_cnfNatAdd, cnfCoeffAt_cnfAddTerm, cnfCoeffAt_cnfAddTerm,
    cnfCoeffAt_cnfAddTerm, cnfCoeffAt_cnfAddTerm]
  have hZ : cnfCoeffAt q [] = 0 := rfl
  rw [hZ]
  exact Eq.symm (natAdd_assoc _ _ _)

/-- Reads the `.pool` ordinal capacity from `poolPath` (defaulting absent
`poolPath` to zero `some []` and rejecting non-pool tags). -/
@[expose] def extractPoolCap (r : ResTrie ResElem) : Option CnfOrd :=
  match ResTrie.getBits poolPath r with
  | none => some []
  | some (.pool p) => some (cnfNorm p)
  | some (.debt _) | some (.checkedOutLoan _ _) | some (.cell _) => none

/-- Reads the `.debt` ordinal budget from `debtPath` (defaulting absent
`debtPath` to zero `some []` and rejecting non-debt tags). -/
@[expose] def extractDebtCap (r : ResTrie ResElem) : Option CnfOrd :=
  match ResTrie.getBits debtPath r with
  | none => some []
  | some (.debt d) => some (cnfNorm d)
  | some (.pool _) | some (.checkedOutLoan _ _) | some (.cell _) => none

/-- Boolean pool and debt `< ω^ω` capacity check for `WorldMatches`. -/
@[expose] def checkWorldMatchesPoolBool (r : ResTrie ResElem) (w :
    WavefrontWorld) :
    Bool :=
  match extractPoolCap r with
  | none => false
  | some poolCap =>
    match extractDebtCap r with
    | none => false
    | some debtCap =>
      cnfBle (worldMeasure w) poolCap &&
      cnfBle (cnfAddOrd debtCap (worldMeasure w)) poolCap

/-- Full spatial and pure-lifted world coupling invariant:
1. `viewOk`: monotonic `stepCount` lower bound on `View`.
2. `loansMemOk`: `LoansSyncedWithMem w.loans w.mem` (`mod 2^32` +
   `byteSubLensGet` synchronization).
3. `queueLoansOk`: `QueueMatchesLoans w` (every queued task targets a live
   `.spatialCheckedOut` loan).
4. `poolDebtOk`: `< ω^ω` pool/debt capacity coupling.
5. `cellOk` & `checkedLoanOk`: spatial `cellCapProp`/`cellAuthProp` and
   `checkedOutLoanProp` coupling. -/
structure WorldMatches (v : View) (r : ResTrie ResElem)
    (w : WavefrontWorld) : Prop where
  viewOk : Nat.ble (viewGet v 0) w.stepCount = true
  loansMemOk : LoansSyncedWithMem w.loans w.mem
  queueLoansOk : QueueMatchesLoans w
  poolDebtOk : checkWorldMatchesPoolBool r w = true
  cellOk : ∀ (cid : Pos4),
    match ResTrie.getBits (cellPath cid) r with
    | none => True
    | some (.pool _) | some (.debt _) | some (.checkedOutLoan _ _) => False
    | some (.cell cf) =>
      match cf with
      | .capOnly =>
        match ResTrie.getBits (pos4ToList cid) w.cells with
        | none => False | some _ => True
      | .authOnly cv | .capAndAuth cv =>
        ResTrie.getBits (pos4ToList cid) w.cells = some cv
  checkedLoanOk : ∀ (lid : Pos4),
    match ResTrie.getBits (checkedLoanPath lid) r with
    | none => True
    | some (.pool _) | some (.debt _) | some (.cell _) => False
    | some (.checkedOutLoan sid lv) =>
      (!anyTaskHasLoan lid w.fifoQueue && !anyTaskHasLoan lid w.stealDeque) =
        true ∧
      ∃ e : WfLoanEntry,
        wfFindLoan lid w.loans = some e ∧
        e.phase = .spatialCheckedOut sid ∧ e.val = lv

/-- Generates `count` sequential `WorkerTask`s starting at `baseId` with `(rank,
yields, lid, sc, writeDelta)`. -/
@[expose] def mkWorkers (baseId count rank yields : Nat) (lid : Pos4) (sc
    writeDelta :
    Nat) :
    List WorkerTask :=
  @Nat.rec (fun _ => Nat → List WorkerTask)
    (fun _ => [])
    (fun _ ih tid => WorkerTask.mk tid rank yields lid sc writeDelta :: ih (tid
      + 1))
    count baseId

private theorem mkWorkers_not_hasLoan (lid1 lid2 : Pos4) (baseId k rc cy sc wd
    : Nat)
    (hNe : Pos4.beq lid1 lid2 = false) :
    anyTaskHasLoan lid2 (mkWorkers baseId k rc cy lid1 sc wd) = false := by
  revert baseId
  induction k with
  | zero => intro _; rfl
  | succ m ih =>
    intro baseId
    change (Pos4.beq lid1 lid2 || anyTaskHasLoan lid2 (mkWorkers (baseId +
      1) m rc cy lid1 sc wd)) = false
    rw [hNe, ih (baseId + 1)]
    rfl

private theorem queueMatchesLoansBool_mkWorkers (baseId k rc cy : Nat)
    (lid : Pos4) (sc wd : Nat) (loans : List WfLoanEntry)
    (hMatch :
      (match wfFindLoan lid loans with
       | none => false
       | some e => loanPhaseMatchesScope e.phase sc) = true) :
    queueMatchesLoansBool (mkWorkers baseId k rc cy lid sc wd) loans =
      true := by
  revert baseId
  induction k with
  | zero => intro _; rfl
  | succ m ih =>
    intro baseId
    change
      ((match wfFindLoan lid loans with
        | none => false
        | some e => loanPhaseMatchesScope e.phase sc) &&
        queueMatchesLoansBool (mkWorkers (baseId + 1) m rc cy lid sc wd)
          loans) = true
    rw [hMatch]
    exact ih (baseId + 1)

/-- Hybrid commands coupling pure-lifted writes, spatial cells, loan checkout,
amortized task-burst submission, and `< ω^ω`-bounded wavefront steps. -/
inductive HybridCmd where
  | pureLiftSafe (lid : Pos4) (delta : Nat)
  | updateSpatialCell (cid : Pos4) (newVal : Nat)
  | checkoutLoan (lid : Pos4) (scopeId : Nat)
  | submitTaskBurst (rank remYields : Nat) (lid : Pos4)
      (scopeId writeDelta : Nat)
  | poolWavefrontStep (pol : SpawnPolicy)

/-- Outcome of evaluating a `HybridCmd` against a `WavefrontWorld`. -/
inductive HybridOut where
  | returned (wOut : WavefrontWorld)
  | faultInvalidSpawn
  | faultLoanViolation

/-- Fail-closed pure-lifted write on an `.activeMut` loan. -/
@[expose] def execPureLiftSafe (lid : Pos4) (delta : Nat) (w : WavefrontWorld) :
    HybridOut :=
  match wfCanPureAccessLoan w.loans lid true with
  | false => .faultLoanViolation
  | true =>
    match wfFindLoan lid w.loans with
    | none => .faultLoanViolation
    | some e =>
      let newVal := wrapU32 (e.val + delta)
      match byteSubLensPut e.lens w.mem (wfEncodeU32BeSlice newVal) with
      | none => .faultLoanViolation
      | some memOut =>
        .returned {
          mem := memOut
          loans := wfSetLoanEntryAt w.loans lid .activeMut newVal
          cells := w.cells
          fifoQueue := w.fifoQueue
          stealDeque := w.stealDeque
          nextTaskId := w.nextTaskId
          completedCount := w.completedCount
          stepCount := w.stepCount
        }

/-- Fail-closed spatial cell update. -/
@[expose] def execUpdateSpatialCell (cid : Pos4) (newVal : Nat) (w :
    WavefrontWorld) :
    HybridOut :=
  match ResTrie.getBits (pos4ToList cid) w.cells with
  | none => .faultLoanViolation
  | some _ =>
    .returned {
      mem := w.mem
      loans := w.loans
      cells :=
        ResTrie.modifyBits (pos4ToList cid) (fun _ => some newVal) w.cells
      fifoQueue := w.fifoQueue
      stealDeque := w.stealDeque
      nextTaskId := w.nextTaskId
      completedCount := w.completedCount
      stepCount := w.stepCount
    }

/-- Fail-closed checkout transitioning an `.activeMut` loan with no queued
tasks into `.spatialCheckedOut scopeId`. -/
@[expose] def execCheckoutLoan (lid : Pos4) (scopeId : Nat) (w : WavefrontWorld)
    :
    HybridOut :=
  match (!anyTaskHasLoan lid w.fifoQueue &&
    !anyTaskHasLoan lid w.stealDeque) with
  | false => .faultLoanViolation
  | true =>
    match wfFindLoan lid w.loans with
    | none => .faultLoanViolation
    | some e =>
      match e.phase with
      | .activeMut =>
        .returned {
          mem := w.mem
          loans := wfSetLoanEntryAt w.loans lid (.spatialCheckedOut scopeId)
            e.val
          cells := w.cells
          fifoQueue := w.fifoQueue
          stealDeque := w.stealDeque
          nextTaskId := w.nextTaskId
          completedCount := w.completedCount
          stepCount := w.stepCount
        }
      | .frozen | .spatialCheckedOut _ | .ended => .faultLoanViolation

/-- Fail-closed task-burst submission targeting a checked-out loan. -/
@[expose] def execSubmitTaskBurst (rank remYields : Nat) (lid : Pos4)
    (scopeId writeDelta : Nat) (w : WavefrontWorld) : HybridOut :=
  match wfFindLoan lid w.loans with
  | none => .faultLoanViolation
  | some e =>
    match loanPhaseMatchesScope e.phase scopeId with
    | false => .faultLoanViolation
    | true =>
      let newTask :=
        WorkerTask.mk w.nextTaskId rank remYields lid scopeId writeDelta
      .returned {
        mem := w.mem
        loans := w.loans
        cells := w.cells
        fifoQueue := newTask :: w.fifoQueue
        stealDeque := w.stealDeque
        nextTaskId := w.nextTaskId + 1
        completedCount := w.completedCount
        stepCount := w.stepCount + 1
      }

/-- Fail-closed execution of one popped wavefront task: verifies strict
rank-drop spawn admissibility (`spawnAdmissible`), yields or spawns lower-rank
children, and at leaf completion (`remYields = 0`, `k = 0`) fails closed with
`.faultLoanViolation` unless the loan exists, matches `hd.scopeId`, and accepts
`byteSubLensPut`. When no remaining queued tasks reference `(hd.loanId,
hd.scopeId)`, the loan reclaims to `.activeMut`. -/
@[expose] def execWavefrontPopped (pol : SpawnPolicy) (hd : WorkerTask)
    (remFifo remSteal : List WorkerTask) (w : WavefrontWorld) : HybridOut :=
  let polRes := pol hd.rank
  let k := polRes.1
  let childRank := polRes.2.1
  let childYields := polRes.2.2
  match spawnAdmissible hd.rank k childRank with
  | false => .faultInvalidSpawn
  | true =>
    let children :=
      mkWorkers w.nextTaskId k childRank childYields hd.loanId hd.scopeId
        hd.writeDelta
    let nextSteal := children ++ remSteal
    match hd.remYields with
    | y' + 1 =>
      let hdNext :=
        WorkerTask.mk hd.taskId hd.rank y' hd.loanId hd.scopeId hd.writeDelta
      .returned {
        mem := w.mem
        loans := w.loans
        cells := w.cells
        fifoQueue := remFifo ++ [hdNext]
        stealDeque := nextSteal
        nextTaskId := w.nextTaskId + k
        completedCount := w.completedCount
        stepCount := w.stepCount + 1
      }
    | 0 =>
      match k with
      | k' + 1 =>
        .returned {
          mem := w.mem
          loans := w.loans
          cells := w.cells
          fifoQueue := remFifo
          stealDeque := nextSteal
          nextTaskId := w.nextTaskId + (k' + 1)
          completedCount := w.completedCount + 1
          stepCount := w.stepCount + 1
        }
      | 0 =>
        match wfFindLoan hd.loanId w.loans with
        | none => .faultLoanViolation
        | some e =>
          match loanPhaseMatchesScope e.phase hd.scopeId with
          | false => .faultLoanViolation
          | true =>
            let newVal := wrapU32 (e.val + hd.writeDelta)
            match byteSubLensPut e.lens w.mem (wfEncodeU32BeSlice newVal) with
            | none => .faultLoanViolation
            | some memOut =>
              let stillInFlight :=
                anyTaskHasLoanScope hd.loanId hd.scopeId remFifo ||
                anyTaskHasLoanScope hd.loanId hd.scopeId remSteal
              let nextPh := match stillInFlight with
                | true => WfLoanPhase.spatialCheckedOut hd.scopeId
                | false => WfLoanPhase.activeMut
              .returned {
                mem := memOut
                loans := wfSetLoanEntryAt w.loans hd.loanId nextPh newVal
                cells := w.cells
                fifoQueue := remFifo
                stealDeque := remSteal
                nextTaskId := w.nextTaskId
                completedCount := w.completedCount + 1
                stepCount := w.stepCount + 1
              }

/-- Top-level fail-closed evaluator for `HybridCmd`. -/
@[expose] def evalHybridCmd (cmd : HybridCmd) (w : WavefrontWorld) : HybridOut
    :=
  match cmd with
  | .pureLiftSafe lid delta => execPureLiftSafe lid delta w
  | .updateSpatialCell cid newVal => execUpdateSpatialCell cid newVal w
  | .checkoutLoan lid scopeId => execCheckoutLoan lid scopeId w
  | .submitTaskBurst rank remYields lid scopeId writeDelta =>
    execSubmitTaskBurst rank remYields lid scopeId writeDelta w
  | .poolWavefrontStep pol =>
    match w.fifoQueue with
    | hd :: ft => execWavefrontPopped pol hd ft w.stealDeque w
    | [] =>
      match w.stealDeque with
      | [] => .faultInvalidSpawn
      | hd :: stTail => execWavefrontPopped pol hd [] stTail w

/-- Three-mode `< ω^ω` ordinal step classification:
- `.preserve`: `worldMeasure wOut = worldMeasure wIn`.
- `.strictDescent`: `cnfLt (worldMeasure wOut) (worldMeasure wIn) = true`.
- `.amortized ordSpent`: `cnfLt (worldMeasure wOut) (cnfAddOrd ordSpent
(worldMeasure wIn)) = true`. -/
inductive OrdStepKind where
  | preserve
  | strictDescent
  | amortized (ordSpent : CnfOrd)

/-- Checks that any `.amortized ordSpent` payload is a canonical CNF ordinal. -/
@[expose] def ordStepKindCanonical (k : OrdStepKind) : Bool :=
  match k with
  | .preserve | .strictDescent => true
  | .amortized ordSpent => isCanonicalCnf ordSpent

/-- Relates `worldMeasure wIn` and `worldMeasure wOut` according to
`OrdStepKind` (equality, strict `cnfLt` descent, or bounded `cnfAddOrd ordSpent`
growth). -/
@[expose] def OrdRelStep (k : OrdStepKind) (wIn wOut : WavefrontWorld) : Prop :=
  match k with
  | .preserve => worldMeasure wOut = worldMeasure wIn
  | .strictDescent => cnfLt (worldMeasure wOut) (worldMeasure wIn) = true
  | .amortized ordSpent =>
    cnfLt (worldMeasure wOut) (cnfAddOrd ordSpent (worldMeasure wIn)) = true

/-- Frame-preserving view-indexed relational weakest precondition over
`evalHybridCmd`, conserving total `extractPoolCap` and establishing `OrdRelStep`
and `WorldMatches`. -/
structure VSepWpOrdRel (cmd : HybridCmd) (ordKind : OrdStepKind)
    (worldGuard : WavefrontWorld → Prop)
    (Pre : VProp) (Post : WavefrontWorld → VProp) : Prop where
  canonKind : ordStepKindCanonical ordKind = true
  run : ∀ (v : View) (F : VProp) (rIn : ResTrie ResElem) (wIn : WavefrontWorld),
    worldGuard wIn →
    (vsep Pre F).holds v rIn →
    WorldMatches v rIn wIn →
    ∃ (wOut : WavefrontWorld) (rOut : ResTrie ResElem) (vOut : View),
      evalHybridCmd cmd wIn = .returned wOut ∧
      ViewLe v vOut ∧
      extractPoolCap rOut = extractPoolCap rIn ∧
      (vsep (Post wOut) F).holds vOut rOut ∧
      WorldMatches vOut rOut wOut ∧
      OrdRelStep ordKind wIn wOut

/-- Frame rule for `VSepWpOrdRel`: conjoining any `Frame : VProp` onto `Pre` and
`Post` preserves the triple. -/
theorem vsepWpOrdRel_frame (cmd : HybridCmd) (ordKind : OrdStepKind)
    (worldGuard : WavefrontWorld → Prop)
    (Pre Frame : VProp) (Post : WavefrontWorld → VProp)
    (hWp : VSepWpOrdRel cmd ordKind worldGuard Pre Post) :
    VSepWpOrdRel cmd ordKind worldGuard (vsep Pre Frame) (fun wOut => vsep
      (Post wOut) Frame) where
  canonKind := hWp.canonKind
  run v F rIn wIn hG hPre hMatch := by
    have hAssocIn : (vsep Pre (vsep Frame F)).holds v rIn :=
      (vsep_assoc_lr Pre Frame F).imp v rIn hPre
    cases hWp.run v (vsep Frame F) rIn wIn hG hAssocIn hMatch with
    | intro wOut hw =>
      cases hw with
      | intro rOut hr =>
        cases hr with
        | intro vOut hv =>
          exact ⟨wOut, rOut, vOut, hv.1, hv.2.1, hv.2.2.1,
            (vsep_assoc_rl (Post wOut) Frame F).imp vOut rOut hv.2.2.2.1,
            hv.2.2.2.2.1, hv.2.2.2.2.2⟩

/-- Witnesses that loan `lid` is in `.activeMut` phase at `subL` with value
`vIn`. -/
@[expose] def ActivePureLoanAt (lid : Pos4) (subL : ByteSubLens) (vIn : Nat) (w
    :
    WavefrontWorld) : Prop :=
  ∃ e : WfLoanEntry,
    wfFindLoan lid w.loans = some e ∧
    e.phase = .activeMut ∧
    e.lens = subL ∧
    e.val = vIn

private theorem pureLiftSafe_step_core
    (lid : Pos4) (subL : ByteSubLens) (vIn delta : Nat)
    (v : View) (rIn : ResTrie ResElem) (wIn : WavefrontWorld)
    (hAct : ActivePureLoanAt lid subL vIn wIn)
    (hM : WorldMatches v rIn wIn) :
    ∃ wOut : WavefrontWorld,
      evalHybridCmd (.pureLiftSafe lid delta) wIn = .returned wOut ∧
      WorldMatches v rIn wOut ∧
      OrdRelStep .preserve wIn wOut ∧
      wOut.fifoQueue = wIn.fifoQueue ∧
      wOut.stealDeque = wIn.stealDeque ∧
      byteSubLensPut subL wIn.mem (wfEncodeU32BeSlice (wrapU32 (vIn + delta))) =
        some wOut.mem := by
  cases hAct with
  | intro e he =>
    have hFind := he.1
    have hPh := he.2.1
    have hLens := he.2.2.1
    have hVal := he.2.2.2
    have hLive : loanPhaseIsLive e.phase = true := by rw [hPh]; rfl
    have hSynced := wfFindLoan_synced_live_props wIn.loans wIn.mem lid e
      hM.loansMemOk hFind hLive
    have hCan : wfCanPureAccessLoan wIn.loans lid true = true := by
      dsimp only [wfCanPureAccessLoan]
      rw [hFind]; dsimp only; rw [hPh]
    let newVal := wrapU32 (vIn + delta)
    have hLenSl : (wfEncodeU32BeSlice newVal).length = e.lens.size := by
      rw [wfEncodeU32BeSlice_length, hSynced.2.1]
    cases byteSubLens_put_succeeds_of_get e.lens wIn.mem (wfEncodeU32BeSlice
      e.val)
        (wfEncodeU32BeSlice newVal) hSynced.2.2.2 hLenSl with
    | intro memOut hPut =>
      let wOut : WavefrontWorld := {
        mem := memOut
        loans := wfSetLoanEntryAt wIn.loans lid .activeMut newVal
        cells := wIn.cells
        fifoQueue := wIn.fifoQueue
        stealDeque := wIn.stealDeque
        nextTaskId := wIn.nextTaskId
        completedCount := wIn.completedCount
        stepCount := wIn.stepCount
      }
      have hEval : evalHybridCmd (.pureLiftSafe lid delta) wIn =
        .returned wOut := by
        dsimp only [evalHybridCmd, execPureLiftSafe]
        rw [hCan, hFind]
        dsimp only
        rw [hVal]
        change (match byteSubLensPut e.lens wIn.mem (wfEncodeU32BeSlice
          newVal) with
          | none => HybridOut.faultLoanViolation
          | some m' => _) = _
        rw [hPut]
      have hSyncOut : LoansSyncedWithMem wOut.loans wOut.mem :=
        loansSyncedWithMem_set_and_put wIn.loans wIn.mem memOut lid e
          .activeMut newVal
          hM.loansMemOk hFind rfl (Eq.symm (wrapU32_idem (vIn + delta))) hPut
      have hQIn := hM.queueLoansOk
      have hNoF := not_anyTaskHasLoan_of_activeMut lid e wIn.fifoQueue
        wIn.loans hFind hPh (bandLeft hQIn)
      have hNoS := not_anyTaskHasLoan_of_activeMut lid e wIn.stealDeque
        wIn.loans hFind hPh (bandRight hQIn)
      have hQOut : QueueMatchesLoans wOut :=
        bandIntro
          (queueMatchesLoansBool_wfSetLoanEntryAt_of_not_hasLoan wIn.fifoQueue
            wIn.loans lid .activeMut newVal hNoF (bandLeft hQIn))
          (queueMatchesLoansBool_wfSetLoanEntryAt_of_not_hasLoan wIn.stealDeque
            wIn.loans lid .activeMut newVal hNoS (bandRight hQIn))
      have hMeasEq : worldMeasure wOut = worldMeasure wIn := rfl
      have hPoolOkOut : checkWorldMatchesPoolBool rIn wOut = true := by
        dsimp only [checkWorldMatchesPoolBool]
        rw [hMeasEq]
        exact hM.poolDebtOk
      have hMOut : WorldMatches v rIn wOut :=
        WorldMatches.mk hM.viewOk hSyncOut hQOut hPoolOkOut hM.cellOk (fun
          lid2 => by
          have hCk := hM.checkedLoanOk lid2
          cases hG : ResTrie.getBits (checkedLoanPath lid2) rIn with
          | none => exact True.intro
          | some elem =>
            rw [hG] at hCk
            cases elem with
            | pool _ | debt _ | cell _ => exact hCk
            | checkedOutLoan sid lv =>
              cases hCk.2 with
              | intro e2 he2 =>
                cases hEqId : Pos4.beq lid lid2 with
                | true =>
                  have hSameId := pos4_eq_of_beq lid lid2 hEqId
                  rw [← hSameId] at he2
                  rw [hFind] at he2
                  injection he2.1 with hSameE
                  rw [← hSameE] at he2
                  have hBad : WfLoanPhase.activeMut =
                    WfLoanPhase.spatialCheckedOut sid :=
                    Eq.trans hPh.symm he2.2.1
                  nomatch hBad
                | false =>
                  exact ⟨hCk.1, ⟨e2,
                    Eq.trans (wfFindLoan_wfSetLoanEntryAt_ne wIn.loans lid lid2
                      .activeMut newVal hEqId) he2.1,
                    he2.2⟩⟩)
      have hPutSub : byteSubLensPut subL wIn.mem (wfEncodeU32BeSlice newVal) =
        some wOut.mem := by
        rw [← hLens]; exact hPut
      exact ⟨wOut, hEval, hMOut, hMeasEq, rfl, rfl, hPutSub⟩

/-- Universal frame-preserving weakest precondition for `.pureLiftSafe`
preserving the worklist measure and disjoint byte lenses (`[propext]`). -/
theorem vsepWpOrdRel_pure_fastpath
    (lid : Pos4) (subL : ByteSubLens) (vIn delta : Nat) :
    VSepWpOrdRel (.pureLiftSafe lid delta) .preserve
      (ActivePureLoanAt lid subL vIn) vemp (fun _ => vemp) ∧
    (∀ (v : View) (F : VProp) (rIn : ResTrie ResElem) (wIn : WavefrontWorld),
      ActivePureLoanAt lid subL vIn wIn →
      (vsep vemp F).holds v rIn →
      WorldMatches v rIn wIn →
      ∃ wOut : WavefrontWorld,
        evalHybridCmd (.pureLiftSafe lid delta) wIn = .returned wOut ∧
        WorldMatches v rIn wOut ∧
        OrdRelStep .preserve wIn wOut ∧
        wOut.fifoQueue = wIn.fifoQueue ∧
        wOut.stealDeque = wIn.stealDeque ∧
        byteSubLensGet subL wOut.mem =
          some (wfEncodeU32BeSlice (wrapU32 (vIn + delta))) ∧
        (∀ otherL : ByteSubLens,
          byteLensDisjoint subL otherL = true →
          byteSubLensGet otherL wOut.mem = byteSubLensGet otherL wIn.mem)) := by
  let wpInst :
      VSepWpOrdRel (.pureLiftSafe lid delta) .preserve
        (ActivePureLoanAt lid subL vIn) vemp (fun _ => vemp) :=
    VSepWpOrdRel.mk rfl (fun v F rIn wIn hG hPre hM => by
      cases pureLiftSafe_step_core lid subL vIn delta v rIn wIn hG hM with
      | intro wOut hw =>
        exact ⟨wOut, rIn, v, hw.1, viewLe_refl v, rfl, hPre, hw.2.1,
          hw.2.2.1⟩)
  refine ⟨wpInst, ?_⟩
  intro v F rIn wIn hAct _ hM
  cases pureLiftSafe_step_core lid subL vIn delta v rIn wIn hAct hM with
  | intro wOut hw =>
    exact ⟨wOut, hw.1, hw.2.1, hw.2.2.1, hw.2.2.2.1, hw.2.2.2.2.1,
      byteSubLens_put_get subL wIn.mem wOut.mem _ hw.2.2.2.2.2,
      fun otherL hDisj =>
        byteSubLens_get_put_disjoint subL otherL wIn.mem wOut.mem _ hDisj
          hw.2.2.2.2.2⟩

/-- Updates spatial cell `cid` from `oldVal` to `newVal` under `cellCapProp cid
∗ cellAuthProp cid oldVal` with `.preserve` ordinal relation. -/
theorem vsepWpOrdRel_updateSpatialCell (cid : Pos4) (oldVal newVal : Nat) :
    VSepWpOrdRel (.updateSpatialCell cid newVal) .preserve (fun _ => True)
      (vsep (cellCapProp cid) (cellAuthProp cid oldVal))
      (fun _ => vsep (cellCapProp cid) (cellAuthProp cid newVal)) :=
  VSepWpOrdRel.mk rfl (fun v F rIn wIn _ hPre hM => by
    cases hPre with
    | intro rPre hrP =>
      cases hrP with
      | intro rF hPF =>
        cases hPF.2.1 with
        | intro rCap hrC =>
          cases hrC with
          | intro rAuth hCA =>
            cases hCA.2.1.holds with
            | intro fC hfC =>
              cases hCA.2.2.holds with
            | intro fA hfA =>
                let tCap := singleRes (cellPath cid) (.cell .capOnly)
                let tAuthOld := singleRes (cellPath cid) (.cell (.authOnly
                  oldVal))
                let tFullOld := singleRes (cellPath cid) (.cell (.capAndAuth
                  oldVal))
                let tAuthNew := singleRes (cellPath cid) (.cell (.authOnly
                  newVal))
                let tFullNew := singleRes (cellPath cid) (.cell (.capAndAuth
                  newVal))
                cases resTrieMerge_assoc tCap fC rAuth rCap rPre hfC hCA.1 with
                | intro x1 hx1 =>
                  have hx1Comm : resTrieMerge rAuth fC = some x1 :=
                    Eq.trans (resTrieMerge_comm rAuth fC) hx1.1
                  cases resTrieMerge_assoc tAuthOld fA fC rAuth x1 hfA
                    hx1Comm with
                  | intro fCA hfCA =>
                    cases resTrieMerge_assoc_rl tCap tAuthOld fCA x1 rPre
                      hfCA.2 hx1.2 with
                    | intro rComb hrComb =>
                      rw [singleRes_cell_cap_auth_merge cid oldVal] at hrComb
                      injection hrComb.1 with hCombEq
                      rw [← hCombEq] at hrComb
                      cases resTrieMerge_assoc tFullOld fCA rF rPre rIn
                        hrComb.2 hPF.1 with
                      | intro rRest hrRest =>
                        have hGIn :=
                          resTrie_getBits_resTrieMerge (cellPath cid) tFullOld
                          rRest rIn rfl hrRest.2
                        rw [singleRes_getBits_same] at hGIn
                        have hCellInOk := hM.cellOk cid
                        have hCellRIn : ResTrie.getBits (cellPath cid) rIn =
                          some (.cell (.capAndAuth oldVal)) := by
                          cases hGr : ResTrie.getBits (cellPath cid) rRest with
                          | none =>
                            rw [hGr] at hGIn
                            dsimp only [optOp] at hGIn
                            injection hGIn with hEqG
                            exact Eq.symm hEqG
                          | some er =>
                            rw [hGr] at hGIn
                            cases er with
                            | pool _ | debt _ | checkedOutLoan _ _ =>
                              dsimp only [optOp, resMerge] at hGIn; nomatch hGIn
                            | cell cf =>
                              cases cf with
                              | authOnly _ | capAndAuth _ =>
                                dsimp only [optOp, resMerge,
                                  cellFragMerge] at hGIn
                                nomatch hGIn
                              | capOnly =>
                                dsimp only [optOp, resMerge,
                                  cellFragMerge] at hGIn
                                injection hGIn with hEqG
                                exact Eq.symm hEqG
                        rw [hCellRIn] at hCellInOk
                        dsimp only at hCellInOk
                        let wOut : WavefrontWorld := {
                          mem := wIn.mem
                          loans := wIn.loans
                          cells := ResTrie.modifyBits (pos4ToList cid) (fun
                            _ => some newVal) wIn.cells
                          fifoQueue := wIn.fifoQueue
                          stealDeque := wIn.stealDeque
                          nextTaskId := wIn.nextTaskId
                          completedCount := wIn.completedCount
                          stepCount := wIn.stepCount
                        }
                        have hEval : evalHybridCmd (.updateSpatialCell cid
                          newVal) wIn = .returned wOut := by
                          dsimp only [evalHybridCmd, execUpdateSpatialCell]
                          rw [hCellInOk]
                        let rOut :=
                          ResTrie.modifyBits (cellPath cid) (fun _ => some
                          (.cell (.capAndAuth newVal))) rIn
                        have hMergeNew : resTrieMerge tFullNew rRest =
                          some rOut :=
                          resTrieMergeFuel_singleRes_capAndAuth_swap resFuel
                            (cellPath cid) oldVal newVal rRest rIn rfl hrRest.2
                        cases resTrieMerge_assoc_rl tFullNew fCA rF rRest rOut
                          hrRest.1 hMergeNew with
                        | intro rPreNew hrPreNew =>
                          have hSplitNew :=
                            singleRes_cell_cap_auth_merge cid newVal
                          have hPostOut : (vsep (vsep (cellCapProp cid)
                            (cellAuthProp cid newVal)) F).holds v rOut :=
                            ⟨rPreNew, rF, hrPreNew.2,
                              ⟨tCap, rPreNew, ?_, resTrieSub_refl tCap, ?_⟩,
                              hPF.2.2⟩
                          · have hPoolOut : checkWorldMatchesPoolBool rOut wOut
                              = true := by
                              dsimp only [checkWorldMatchesPoolBool,
                                extractPoolCap, extractDebtCap]
                              rw [resTrie_getBits_modifyBits_ne (cellPath cid)
                                poolPath rfl rfl,
                                resTrie_getBits_modifyBits_ne (cellPath cid)
                                  debtPath rfl rfl]
                              exact hM.poolDebtOk
                            have hMOut : WorldMatches v rOut wOut :=
                              WorldMatches.mk hM.viewOk hM.loansMemOk
                                hM.queueLoansOk hPoolOut
                                (fun cid2 => by
                                  cases hEqC : Pos4.beq cid cid2 with
                                  | true =>
                                    have hSameC := pos4_eq_of_beq cid cid2 hEqC
                                    rw [← hSameC]
                                    dsimp only [rOut, wOut]
                                    rw [resTrie_getBits_modifyBits_same,
                                      resTrie_getBits_modifyBits_same]
                                  | false =>
                                    have hNeCellPath : listBoolBeq (cellPath
                                      cid) (cellPath cid2) = false := by
                                      dsimp only [cellPath, listBoolBeq,
                                        Bool.and]
                                      exact hEqC
                                    dsimp only [rOut, wOut]
                                    rw [resTrie_getBits_modifyBits_ne (cellPath
                                      cid) (cellPath cid2) rfl hNeCellPath]
                                    have hPrev := hM.cellOk cid2
                                    cases hGc2 : ResTrie.getBits (cellPath
                                      cid2) rIn with
                                    | none => exact True.intro
                                    | some elem2 =>
                                      rw [hGc2] at hPrev
                                      cases elem2 with
                                      | pool _ | debt _ | checkedOutLoan _ _ =>
                                        exact hPrev
                                      | cell cf2 =>
                                        dsimp only
                                        rw [resTrie_getBits_modifyBits_ne
                                          (pos4ToList cid) (pos4ToList cid2)
                                          rfl hEqC]
                                        exact hPrev)
                                (fun lid2 => by
                                  have hNeChk : listBoolBeq (cellPath cid)
                                    (checkedLoanPath lid2) = false := rfl
                                  dsimp only [rOut, wOut]
                                  rw [resTrie_getBits_modifyBits_ne (cellPath
                                    cid) (checkedLoanPath lid2) rfl hNeChk]
                                  exact hM.checkedLoanOk lid2)
                            have hPoolCapEq : extractPoolCap rOut =
                              extractPoolCap rIn := by
                              dsimp only [extractPoolCap, rOut]
                              rw [resTrie_getBits_modifyBits_ne (cellPath cid)
                                poolPath rfl rfl]
                            exact ⟨wOut, rOut, v, hEval, viewLe_refl v,
                              hPoolCapEq, hPostOut, hMOut, rfl⟩
                          · have hIdemCap : resTrieMerge tCap tFullNew =
                              some tFullNew := by
                              cases cid with
                              | mk b0 r1 =>
                                cases r1 with
                                | mk b1 r2 =>
                                  cases r2 with
                                  | mk b2 b3 =>
                                    cases b0 <;> cases b1 <;> cases b2 <;>
                                      cases b3 <;> rfl
                            cases resTrieMerge_assoc tCap tFullNew fCA tFullNew
                              rPreNew hIdemCap hrPreNew.1 with
                            | intro z hz =>
                              rw [hrPreNew.1] at hz
                              injection hz.1 with hzEq
                              rw [← hzEq] at hz
                              exact hz.2
                          · cases resTrieMerge_assoc tAuthNew tCap fCA tFullNew
                              rPreNew
                                (Eq.trans (resTrieMerge_comm tAuthNew tCap)
                                  hSplitNew) hrPreNew.1 with
                            | intro fRest hfRest =>
                              exact ResTrieSub.mk ⟨fRest, hfRest.2⟩)

/-! ## 3. Exclusive Loan Checkout (`checkoutLoan`) -/

/-- Precondition for `.checkoutLoan`: `ActivePureLoanAt lid subL vIn w` with
zero queued tasks referencing `lid`. -/
@[expose] def CheckoutLoanGuard (lid : Pos4) (subL : ByteSubLens) (vIn : Nat) (w
    :
    WavefrontWorld) : Prop :=
  ActivePureLoanAt lid subL vIn w ∧
  (!anyTaskHasLoan lid w.fifoQueue && !anyTaskHasLoan lid w.stealDeque) = true

/-- Checks out `.activeMut` loan `lid` into `.spatialCheckedOut scopeId`,
minting `checkedOutLoanProp lid scopeId vIn`. -/
theorem vsepWpOrdRel_checkoutLoan (lid : Pos4) (subL : ByteSubLens) (vIn
    scopeId : Nat) :
    VSepWpOrdRel (.checkoutLoan lid scopeId) .preserve (CheckoutLoanGuard lid
      subL vIn)
      vemp (fun _ => checkedOutLoanProp lid scopeId vIn) :=
  VSepWpOrdRel.mk rfl (fun v F rIn wIn hG hPre hM => by
    have hF : F.holds v rIn := vsep_vemp_elim v F rIn hPre
    cases hG.1 with
    | intro e he =>
      have hFind := he.1
      have hPh := he.2.1
      have hVal := he.2.2.2
      have hRNone : ResTrie.getBits (checkedLoanPath lid) rIn = none := by
        have hCk := hM.checkedLoanOk lid
        cases hGr : ResTrie.getBits (checkedLoanPath lid) rIn with
        | none => rfl
        | some elem =>
          rw [hGr] at hCk
          cases elem with
          | pool _ | debt _ | cell _ => exact False.elim hCk
          | checkedOutLoan sid _ =>
            cases hCk.2 with
            | intro e2 he2 =>
              rw [hFind] at he2
              injection he2.1 with hSame
              rw [← hSame] at he2
              have hBad : WfLoanPhase.activeMut =
                WfLoanPhase.spatialCheckedOut sid :=
                Eq.trans hPh.symm he2.2.1
              nomatch hBad
      let tLoan := singleRes (checkedLoanPath lid) (.checkedOutLoan scopeId vIn)
      let rOut := ResTrie.modifyBits (checkedLoanPath lid) (fun _ => some
        (.checkedOutLoan scopeId vIn)) rIn
      have hMergeOut : resTrieMerge tLoan rIn = some rOut :=
        resTrieMergeFuel_singleRes_of_getBits_none resFuel (checkedLoanPath lid)
          (.checkedOutLoan scopeId vIn) rIn rfl hRNone
      let wOut : WavefrontWorld := {
        mem := wIn.mem
        loans := wfSetLoanEntryAt wIn.loans lid (.spatialCheckedOut scopeId)
          e.val
        cells := wIn.cells
        fifoQueue := wIn.fifoQueue
        stealDeque := wIn.stealDeque
        nextTaskId := wIn.nextTaskId
        completedCount := wIn.completedCount
        stepCount := wIn.stepCount
      }
      have hEval : evalHybridCmd (.checkoutLoan lid scopeId) wIn =
        .returned wOut := by
        dsimp only [evalHybridCmd, execCheckoutLoan]
        rw [hG.2, hFind]
        dsimp only
        rw [hPh]
      have hLiveOld : loanPhaseIsLive e.phase = true := by rw [hPh]; rfl
      have hSyncOut : LoansSyncedWithMem wOut.loans wOut.mem :=
        loansSyncedWithMem_setPhase_sameVal wIn.loans wIn.mem lid e
          (.spatialCheckedOut scopeId)
          hM.loansMemOk hFind hLiveOld rfl
      have hQIn := hM.queueLoansOk
      have hQOut : QueueMatchesLoans wOut :=
        bandIntro
          (queueMatchesLoansBool_wfSetLoanEntryAt_of_not_hasLoan wIn.fifoQueue
            wIn.loans
            lid (.spatialCheckedOut scopeId) e.val (trueOfBnotTrue (bandLeft
              hG.2)) (bandLeft hQIn))
          (queueMatchesLoansBool_wfSetLoanEntryAt_of_not_hasLoan wIn.stealDeque
            wIn.loans
            lid (.spatialCheckedOut scopeId) e.val (trueOfBnotTrue (bandRight
              hG.2)) (bandRight hQIn))
      have hPoolOut : checkWorldMatchesPoolBool rOut wOut = true := by
        dsimp only [checkWorldMatchesPoolBool, extractPoolCap, extractDebtCap,
          rOut, wOut]
        rw [resTrie_getBits_modifyBits_ne (checkedLoanPath lid) poolPath rfl
          rfl,
          resTrie_getBits_modifyBits_ne (checkedLoanPath lid) debtPath rfl rfl]
        exact hM.poolDebtOk
      have hMOut : WorldMatches v rOut wOut :=
        WorldMatches.mk hM.viewOk hSyncOut hQOut hPoolOut
          (fun cid => by
            dsimp only [rOut, wOut]
            rw [resTrie_getBits_modifyBits_ne (checkedLoanPath lid) (cellPath
              cid) rfl rfl]
            exact hM.cellOk cid)
          (fun lid2 => by
            cases hEqId : Pos4.beq lid lid2 with
            | true =>
              have hSameId := pos4_eq_of_beq lid lid2 hEqId
              rw [← hSameId]
              dsimp only [rOut, wOut]
              rw [resTrie_getBits_modifyBits_same]
              exact ⟨hG.2, ⟨⟨e.id, .spatialCheckedOut scopeId, e.lens, e.val⟩,
                wfFindLoan_wfSetLoanEntryAt_same wIn.loans lid
                  (.spatialCheckedOut scopeId) e.val e hFind,
                rfl, hVal⟩⟩
            | false =>
              have hNePath : listBoolBeq (checkedLoanPath lid) (checkedLoanPath
                lid2) = false := by
                dsimp only [checkedLoanPath, listBoolBeq, Bool.and]
                exact hEqId
              dsimp only [rOut, wOut]
              rw [resTrie_getBits_modifyBits_ne (checkedLoanPath lid)
                (checkedLoanPath lid2) rfl hNePath]
              have hPrev := hM.checkedLoanOk lid2
              cases hGl2 : ResTrie.getBits (checkedLoanPath lid2) rIn with
              | none => exact True.intro
              | some elem2 =>
                rw [hGl2] at hPrev
                cases elem2 with
                | pool _ | debt _ | cell _ => exact hPrev
                | checkedOutLoan sid2 lv2 =>
                  cases hPrev.2 with
                  | intro e2 he2 =>
                    exact ⟨hPrev.1, ⟨e2,
                      Eq.trans (wfFindLoan_wfSetLoanEntryAt_ne wIn.loans lid
                        lid2 (.spatialCheckedOut scopeId) e.val hEqId) he2.1,
                      he2.2⟩⟩)
      have hPoolCapEq : extractPoolCap rOut = extractPoolCap rIn := by
        dsimp only [extractPoolCap, rOut]
        rw [resTrie_getBits_modifyBits_ne (checkedLoanPath lid) poolPath rfl
          rfl]
      exact ⟨wOut, rOut, v, hEval, viewLe_refl v, hPoolCapEq,
        ⟨tLoan, rIn, hMergeOut, resTrieSub_refl tLoan, hF⟩, hMOut, rfl⟩)

/-! ## 4. Amortized Ordinal-Debt Burst Submission (`submitTaskBurst`) -/

private theorem cnfNatAdd_cnfNorm_right (xs ys : CnfOrd) :
    cnfNatAdd xs (cnfNorm ys) = cnfNatAdd xs ys :=
  cnf_eq_of_coeff_eq _ _ (isCanonicalCnf_cnfNatAdd xs (cnfNorm ys))
    (isCanonicalCnf_cnfNatAdd xs ys)
    (fun q => Eq.trans (cnfCoeffAt_cnfNatAdd q xs (cnfNorm ys))
      (Eq.trans (congrArg (Nat.add (cnfCoeffAt q xs)) (cnfCoeffAt_cnfNorm q ys))
        (Eq.symm (cnfCoeffAt_cnfNatAdd q xs ys))))

/-- Universal amortized `< ω^ω` ordinal-debt spending law for
`.submitTaskBurst` (`[]`). -/
theorem vsepWpOrdRel_submitTaskBurst_amortized_growth
    (rank remYields : Nat) (lid : Pos4) (scopeId writeDelta lv : Nat)
    (ordSpent : CnfOrd)
    (hCanSpent : isCanonicalCnf ordSpent = true)
    (hBudget : cnfLt (burstTaskDelta rank remYields) ordSpent = true) :
    VSepWpOrdRel (.submitTaskBurst rank remYields lid scopeId writeDelta)
      (.amortized ordSpent)
      (fun _ => True)
      (vsep (ordDebtProp ordSpent) (checkedOutLoanProp lid scopeId lv))
      (fun _ => vemp) ∧
    (∀ (wIn wOut : WavefrontWorld),
      evalHybridCmd (.submitTaskBurst rank remYields lid scopeId writeDelta)
        wIn = .returned wOut →
      cnfLt (worldMeasure wIn) (worldMeasure wOut) = true ∧
      cnfLt (worldMeasure wOut)
        (cnfAddOrd ordSpent (worldMeasure wIn)) = true) := by
  have hGrowthOfEval : ∀ (wIn wOut : WavefrontWorld),
      evalHybridCmd (.submitTaskBurst rank remYields lid scopeId writeDelta)
        wIn = .returned wOut →
      cnfLt (worldMeasure wIn) (worldMeasure wOut) = true ∧
      cnfLt (worldMeasure wOut) (cnfAddOrd ordSpent (worldMeasure wIn)) =
        true := by
    intro wIn wOut hEv
    dsimp only [evalHybridCmd, execSubmitTaskBurst] at hEv
    cases hFl : wfFindLoan lid wIn.loans with
    | none => rw [hFl] at hEv; nomatch hEv
    | some e =>
      rw [hFl] at hEv; dsimp only at hEv
      cases hSc : loanPhaseMatchesScope e.phase scopeId with
      | false => rw [hSc] at hEv; nomatch hEv
      | true =>
        rw [hSc] at hEv
        injection hEv with hwOut
        have hMeasOut : worldMeasure wOut =
          cnfAddOrd (burstTaskDelta rank remYields) (worldMeasure wIn) := by
          rw [← hwOut]
          exact wfTaskMeasure_eq_cnfAddOrd_burstTaskDelta
            (WorkerTask.mk wIn.nextTaskId rank remYields lid scopeId writeDelta)
            (worldMeasure wIn) (worldMeasure_canonical wIn)
        rw [hMeasOut]
        have hNilAdd : cnfNatAdd [] (worldMeasure wIn) = worldMeasure wIn :=
          cnfNorm_eq_of_canonical (worldMeasure wIn) (worldMeasure_canonical
            wIn)
        have hStrictGrow : cnfLt (worldMeasure wIn) (cnfAddOrd (burstTaskDelta
          rank remYields) (worldMeasure wIn)) = true := by
          have hStep := cnfLt_cnfNatAdd_left [] (burstTaskDelta rank remYields)
            (worldMeasure wIn)
            rfl (burstTaskDelta_canonical rank remYields) (burstTaskDelta_pos
              rank remYields)
          rw [hNilAdd] at hStep
          exact hStep
        have hAmort := cnfLt_cnfNatAdd_left (burstTaskDelta rank remYields)
          ordSpent (worldMeasure wIn)
          (burstTaskDelta_canonical rank remYields) hCanSpent hBudget
        exact ⟨hStrictGrow, hAmort⟩
  let wpBurst : VSepWpOrdRel (.submitTaskBurst rank remYields lid scopeId
    writeDelta) (.amortized ordSpent)
      (fun _ => True)
      (vsep (ordDebtProp ordSpent) (checkedOutLoanProp lid scopeId lv))
      (fun _ => vemp) :=
    VSepWpOrdRel.mk hCanSpent (fun v F rIn wIn _ hPre hM => by
      cases hPre with
      | intro r12 hr12 =>
        cases hr12 with
        | intro rF h12F =>
          cases h12F.2.1 with
          | intro rD hrD =>
            cases hrD with
            | intro rL hDL =>
              cases hDL.2.1.holds with
              | intro fD hfD =>
                cases hDL.2.2.holds with
                | intro fL hfL =>
                  let tDebt := singleRes debtPath (.debt ordSpent)
                  let tPool := singleRes poolPath (.pool ordSpent)
                  let tLoan := singleRes (checkedLoanPath lid) (.checkedOutLoan
                    scopeId lv)
                  cases resTrieMerge_assoc tDebt tPool fD (ordDebtTree
                    ordSpent) rD (ordDebtTree_decomp ordSpent) hfD with
                  | intro pfD hpfD =>
                    cases resTrieMerge_assoc tDebt pfD rL rD r12 hpfD.2
                      hDL.1 with
                    | intro x1 hx1 =>
                      have hx1Comm : resTrieMerge rL pfD = some x1 :=
                        Eq.trans (resTrieMerge_comm rL pfD) hx1.1
                      cases resTrieMerge_assoc tLoan fL pfD rL x1 hfL
                        hx1Comm with
                      | intro x2 hx2 =>
                        cases resTrieMerge_assoc tDebt x1 rF r12 rIn hx1.2
                          h12F.1 with
                        | intro rMid hrMid =>
                          cases resTrieMerge_assoc tLoan x2 rF x1 rMid hx2.2
                            hrMid.1 with
                          | intro rOut hrOut =>
                            have hGLMid :=
                              resTrie_getBits_resTrieMerge (checkedLoanPath
                              lid) tLoan rOut rMid rfl hrOut.2
                            rw [singleRes_getBits_same] at hGLMid
                            have hGLIn :=
                              resTrie_getBits_resTrieMerge (checkedLoanPath
                              lid) tDebt rMid rIn rfl hrMid.2
                            rw [singleRes_getBits_ne debtPath (checkedLoanPath
                              lid) _ rfl rfl] at hGLIn
                            dsimp only [optOp] at hGLIn
                            injection hGLIn with hMidEqIn
                            have hROutLoanNone : ResTrie.getBits
                              (checkedLoanPath lid) rOut = none := by
                              cases hGo : ResTrie.getBits (checkedLoanPath lid)
                                rOut with
                              | none => rfl
                              | some eo =>
                                rw [hGo] at hGLMid
                                dsimp only [optOp, resMerge] at hGLMid
                                nomatch hGLMid
                            rw [hROutLoanNone] at hGLMid
                            dsimp only [optOp] at hGLMid
                            injection hGLMid with hMidSome
                            have hRInLoan : ResTrie.getBits (checkedLoanPath
                              lid) rIn = some (.checkedOutLoan scopeId lv) :=
                              Eq.trans (Eq.symm hMidEqIn) (Eq.symm hMidSome)
                            have hCkIn := hM.checkedLoanOk lid
                            rw [hRInLoan] at hCkIn
                            dsimp only at hCkIn
                            cases hCkIn.2 with
                            | intro e he =>
                              have hMatchSc : loanPhaseMatchesScope e.phase
                                scopeId = true := by
                                rw [he.2.1]
                                dsimp only [loanPhaseMatchesScope]
                                exact natBeq_refl scopeId
                              let newTask :=
                                WorkerTask.mk wIn.nextTaskId rank remYields lid
                                scopeId writeDelta
                              let wOut : WavefrontWorld := {
                                mem := wIn.mem
                                loans := wIn.loans
                                cells := wIn.cells
                                fifoQueue := newTask :: wIn.fifoQueue
                                stealDeque := wIn.stealDeque
                                nextTaskId := wIn.nextTaskId + 1
                                completedCount := wIn.completedCount
                                stepCount := wIn.stepCount + 1
                              }
                              have hEval : evalHybridCmd (.submitTaskBurst rank
                                remYields lid scopeId writeDelta) wIn =
                                .returned wOut := by
                                dsimp only [evalHybridCmd, execSubmitTaskBurst]
                                rw [he.1]; dsimp only; rw [hMatchSc]
                              have hGrow := hGrowthOfEval wIn wOut hEval
                              let vOut := bumpView0 v wOut.stepCount
                              have hVLe : ViewLe v vOut :=
                                viewLe_bumpView0 v wOut.stepCount
                                  (natBle_succ_right (viewGet v 0)
                                    wIn.stepCount hM.viewOk)
                              have hSubFRout : ResTrieSub rF rOut :=
                                ResTrieSub.mk ⟨x2,
                                  Eq.trans (resTrieMerge_comm rF x2) hrOut.1⟩
                              have hPostHold : (vsep vemp F).holds vOut rOut :=
                                vsep_vemp_intro vOut F rOut (F.upClosed v vOut
                                  rF rOut hVLe hSubFRout h12F.2.2)
                              have hPresOther : ∀ (p : List Bool),
                                  p.length = 6 →
                                  listBoolBeq debtPath p = false →
                                  listBoolBeq (checkedLoanPath lid) p = false →
                                  ResTrie.getBits p rOut =
                                    ResTrie.getBits p rIn := by
                                intro p hLp hNeD hNeL
                                have h1 :=
                                  resTrie_getBits_resTrieMerge p tLoan rOut rMid
                                  (by rw [hLp]; rfl) hrOut.2
                                rw [singleRes_getBits_ne (checkedLoanPath lid)
                                  p _ (Eq.symm hLp) hNeL] at h1
                                dsimp only [optOp] at h1
                                injection h1 with e1
                                have h2 :=
                                  resTrie_getBits_resTrieMerge p tDebt rMid rIn
                                  (by rw [hLp]; rfl) hrMid.2
                                rw [singleRes_getBits_ne debtPath p _ (Eq.symm
                                  hLp) hNeD] at h2
                                dsimp only [optOp] at h2
                                injection h2 with e2
                                exact Eq.trans e1 e2
                              have hPoolEq : ResTrie.getBits poolPath rOut =
                                ResTrie.getBits poolPath rIn :=
                                hPresOther poolPath rfl rfl rfl
                              have hDebtRel :=
                                resTrie_getBits_resTrieMerge debtPath tDebt
                                rMid rIn rfl hrMid.2
                              rw [singleRes_getBits_same] at hDebtRel
                              have hDebtMid :=
                                resTrie_getBits_resTrieMerge debtPath tLoan
                                rOut rMid rfl hrOut.2
                              rw [singleRes_getBits_ne (checkedLoanPath lid)
                                debtPath _ rfl rfl] at hDebtMid
                              dsimp only [optOp] at hDebtMid
                              injection hDebtMid with hDebtOutEqMid
                              rw [← hDebtOutEqMid] at hDebtRel
                              have hPcEq : extractPoolCap rOut =
                                extractPoolCap rIn := by
                                dsimp only [extractPoolCap]
                                rw [hPoolEq]
                              have hPoolDebtIn := hM.poolDebtOk
                              dsimp only [checkWorldMatchesPoolBool]
                                at hPoolDebtIn
                              have hPoolDebtOut : checkWorldMatchesPoolBool
                                rOut wOut = true := by
                                dsimp only [checkWorldMatchesPoolBool]
                                rw [hPcEq]
                                cases hPc : extractPoolCap rIn with
                                | none =>
                                  rw [hPc] at hPoolDebtIn
                                  exact False.elim (boolFalseNeTrue hPoolDebtIn)
                                | some poolCap =>
                                  rw [hPc] at hPoolDebtIn
                                  dsimp only at hPoolDebtIn
                                  dsimp only
                                  have hLeGrow : cnfBle (worldMeasure wOut)
                                    (cnfAddOrd ordSpent (worldMeasure wIn)) =
                                    true :=
                                    cnfBle_of_lt _ _ hGrow.2
                                  dsimp only [extractDebtCap]
                                  cases hGdOut : ResTrie.getBits debtPath
                                    rOut with
                                  | none =>
                                    rw [hGdOut] at hDebtRel
                                    dsimp only [optOp] at hDebtRel
                                    injection hDebtRel with hGdInEq
                                    dsimp only [extractDebtCap] at hPoolDebtIn
                                    rw [← hGdInEq] at hPoolDebtIn
                                    dsimp only at hPoolDebtIn
                                    rw [cnfNorm_eq_of_canonical ordSpent
                                      hCanSpent] at hPoolDebtIn
                                    have hBoundIn := bandRight hPoolDebtIn
                                    have hOutLePool : cnfBle (worldMeasure
                                      wOut) poolCap = true :=
                                      cnfBle_trans _ _ _ hLeGrow hBoundIn
                                    have hNilAddOut : cnfAddOrd []
                                      (worldMeasure wOut) = worldMeasure wOut :=
                                      cnfNorm_eq_of_canonical _
                                        (worldMeasure_canonical wOut)
                                    dsimp only
                                    rw [hNilAddOut]
                                    exact bandIntro hOutLePool hOutLePool
                                  | some eOut =>
                                    rw [hGdOut] at hDebtRel
                                    cases eOut with
                                    | pool _ | checkedOutLoan _ _ | cell _ =>
                                      dsimp only [optOp, resMerge] at hDebtRel
                                      nomatch hDebtRel
                                    | debt dOut =>
                                      dsimp only [optOp, resMerge] at hDebtRel
                                      injection hDebtRel with hGdInEq
                                      dsimp only [extractDebtCap] at hPoolDebtIn
                                      rw [← hGdInEq] at hPoolDebtIn
                                      dsimp only at hPoolDebtIn
                                      rw [cnfNorm_eq_of_canonical _
                                        (isCanonicalCnf_cnfNatAdd ordSpent
                                        dOut)] at hPoolDebtIn
                                      have hBoundIn := bandRight hPoolDebtIn
                                      have hRewriteDebt : cnfAddOrd (cnfNatAdd
                                        ordSpent dOut) (worldMeasure wIn) =
                                          cnfAddOrd (cnfNorm dOut) (cnfAddOrd
                                            ordSpent (worldMeasure wIn)) := by
                                        dsimp only [cnfAddOrd]
                                        rw [← cnfNatAdd_cnfNorm_right ordSpent
                                          dOut,
                                          cnfNatAdd_comm ordSpent (cnfNorm
                                            dOut),
                                          cnfNatAdd_assoc (cnfNorm dOut)
                                            ordSpent (worldMeasure wIn)]
                                      rw [hRewriteDebt] at hBoundIn
                                      have hMonoDebt : cnfBle (cnfAddOrd
                                        (cnfNorm dOut) (worldMeasure wOut))
                                          (cnfAddOrd (cnfNorm dOut) (cnfAddOrd
                                            ordSpent (worldMeasure wIn))) =
                                            true :=
                                        cnfBle_cnfNatAdd_right (cnfNorm dOut)
                                          (worldMeasure wOut)
                                          (cnfAddOrd ordSpent (worldMeasure
                                            wIn))
                                          (worldMeasure_canonical wOut)
                                          (isCanonicalCnf_cnfNatAdd ordSpent
                                            (worldMeasure wIn))
                                          hLeGrow
                                      have hSplitOut : cnfBle (cnfAddOrd
                                        (cnfNorm dOut) (worldMeasure wOut))
                                        poolCap = true :=
                                        cnfBle_trans _ _ _ hMonoDebt hBoundIn
                                      have hMeasLeSplit : cnfBle (worldMeasure
                                        wOut) (cnfAddOrd (cnfNorm dOut)
                                        (worldMeasure wOut)) = true :=
                                        cnfBle_cnfAddOrd_right (cnfNorm dOut)
                                          (worldMeasure wOut)
                                          (worldMeasure_canonical wOut)
                                      have hOutLePool : cnfBle (worldMeasure
                                        wOut) poolCap = true :=
                                        cnfBle_trans _ _ _ hMeasLeSplit
                                          hSplitOut
                                      dsimp only
                                      exact bandIntro hOutLePool hSplitOut
                              have hViewOut : Nat.ble (viewGet vOut 0)
                                wOut.stepCount = true := by
                                dsimp only [vOut]
                                rw [viewGet_bumpView0_zero]
                                exact natBle_refl wOut.stepCount
                              have hQIn := hM.queueLoansOk
                              have hQOut : QueueMatchesLoans wOut := by
                                refine bandIntro ?_ (bandRight hQIn)
                                dsimp only [wOut, newTask,
                                  queueMatchesLoansBool, List.foldr]
                                rw [he.1]
                                dsimp only
                                rw [hMatchSc]
                                exact bandLeft hQIn
                              have hMOut : WorldMatches vOut rOut wOut :=
                                WorldMatches.mk hViewOut hM.loansMemOk hQOut
                                  hPoolDebtOut
                                  (fun cid => by
                                    rw [hPresOther (cellPath cid) rfl rfl rfl]
                                    exact hM.cellOk cid)
                                  (fun lid2 => by
                                    cases hEqL : Pos4.beq lid lid2 with
                                    | true =>
                                      rw [← pos4_eq_of_beq lid lid2 hEqL,
                                        hROutLoanNone]
                                      exact True.intro
                                    | false =>
                                      have hNeL : listBoolBeq (checkedLoanPath
                                        lid) (checkedLoanPath lid2) = false :=
                                        by
                                        dsimp only [checkedLoanPath,
                                          listBoolBeq, Bool.and]
                                        exact hEqL
                                      rw [hPresOther (checkedLoanPath lid2) rfl
                                        rfl hNeL]
                                      have hPrev := hM.checkedLoanOk lid2
                                      cases hGl2 : ResTrie.getBits
                                        (checkedLoanPath lid2) rIn with
                                      | none => exact True.intro
                                      | some elem2 =>
                                        rw [hGl2] at hPrev
                                        cases elem2 with
                                        | pool _ | debt _ | cell _ =>
                                          exact hPrev
                                        | checkedOutLoan sid2 lv2 =>
                                          have hNoNew : (!anyTaskHasLoan lid2
                                            (newTask :: wIn.fifoQueue) &&
                                              !anyTaskHasLoan lid2
                                                wIn.stealDeque) = true := by
                                            change (!(Pos4.beq lid lid2 ||
                                              anyTaskHasLoan lid2
                                              wIn.fifoQueue) &&
                                              !anyTaskHasLoan lid2
                                                wIn.stealDeque) = true
                                            rw [hEqL]
                                            exact hPrev.1
                                          exact ⟨hNoNew, hPrev.2⟩)
                              have hPoolCapEq : extractPoolCap rOut =
                                extractPoolCap rIn := by
                                dsimp only [extractPoolCap]
                                rw [hPoolEq]
                              exact ⟨wOut, rOut, vOut, hEval, hVLe, hPoolCapEq,
                                hPostHold, hMOut, hGrow.2⟩)
  exact ⟨wpBurst, hGrowthOfEval⟩

/-! ## 5. Strict `< ω^ω` Wavefront Step Descent (`poolWavefrontStep`) -/

private theorem childRank_double_plus1_lt (rc rp : Nat) (hLt : natLt rc rp =
    true) :
    natLt (rc + rc + 1) (rp + rp) = true := by
  dsimp only [natLt] at hLt
  dsimp only [natLt]
  have hSum : (rc + rc + 1) + 1 = (rc + 1) + (rc + 1) := by
    rw [natAdd_assoc (rc + rc) 1 1, natAdd_assoc rc rc 2,
      natAdd_comm rc 2, ← natAdd_assoc rc 2 rc]
    have h2 : rc + 2 = (rc + 1) + 1 := rfl
    rw [h2, natAdd_assoc (rc + 1) 1 rc, natAdd_comm 1 rc]
  rw [hSum]
  exact natBle_trans ((rc + 1) + (rc + 1)) (rp + (rc + 1)) (rp + rp)
    (natBle_add_mono_right (rc + 1) rp (rc + 1) hLt)
    (natBle_add_mono_left rp (rc + 1) rp hLt)

private theorem wfTasksWeightAt_mkWorkers_zero_above (q baseId k rc cy : Nat)
    (lid : Pos4) (sc wd : Nat)
    (rp : Nat) (hAdm : spawnAdmissible rp k rc = true)
    (hGe : Nat.ble (rp + rp) q = true) :
    wfTasksWeightAt q (mkWorkers baseId k rc cy lid sc wd) = 0 := by
  cases k with
  | zero => rfl
  | succ k' =>
    dsimp only [spawnAdmissible] at hAdm
    have hOddLt : natLt (rc + rc + 1) q = true :=
      natLtOfLtOfBle (rc + rc + 1) (rp +
        rp) q (childRank_double_plus1_lt rc rp hAdm) hGe
    have hEvenLt : natLt (rc + rc) q = true :=
      natLtTrans (rc + rc) (rc + rc + 1) q (natLtSuccSelf (rc + rc)) hOddLt
    have hB1 : Nat.beq (rc + rc + 1) q = false := natBeqFalseOfLt hOddLt
    have hB0 : Nat.beq (rc + rc) q = false := natBeqFalseOfLt hEvenLt
    revert baseId
    induction k' with
    | zero =>
      intro baseId
      dsimp only [mkWorkers, wfTasksWeightAt, List.foldr, wfTaskWeightAt]
      rw [hB1, hB0]
      rfl
    | succ m ih =>
      intro baseId
      change wfTaskWeightAt q (WorkerTask.mk baseId rc cy lid sc wd) +
        wfTasksWeightAt q (mkWorkers (baseId + 1) (m + 1) rc cy lid sc wd) = 0
      dsimp only [wfTaskWeightAt]
      rw [hB1, hB0, ih (baseId + 1)]
      rfl

private theorem wfTaskWeightAt_self_even (t : WorkerTask) :
    wfTaskWeightAt (t.rank + t.rank) t = t.remYields := by
  dsimp only [wfTaskWeightAt]
  have hNe : Nat.beq (t.rank + t.rank + 1) (t.rank + t.rank) = false := by
    rw [natBeq_symm]
    exact natBeqFalseOfLt (natLtSuccSelf (t.rank + t.rank))
  rw [hNe, natBeq_refl (t.rank + t.rank), natAdd_zero_left]

private theorem wfTaskWeightAt_self_odd (t : WorkerTask) :
    wfTaskWeightAt (t.rank + t.rank + 1) t = 1 := by
  dsimp only [wfTaskWeightAt]
  have hNe : Nat.beq (t.rank + t.rank) (t.rank + t.rank + 1) = false :=
    natBeqFalseOfLt (natLtSuccSelf (t.rank + t.rank))
  rw [natBeq_refl (t.rank + t.rank + 1), hNe]
  rfl

private theorem wfTaskWeightAt_zero_above_odd (t : WorkerTask) (q : Nat)
    (hGt : natLt (t.rank + t.rank + 1) q = true) :
    wfTaskWeightAt q t = 0 := by
  dsimp only [wfTaskWeightAt]
  have hEvenGt : natLt (t.rank + t.rank) q = true :=
    natLtTrans (t.rank + t.rank) (t.rank + t.rank +
      1) q (natLtSuccSelf (t.rank + t.rank)) hGt
  rw [natBeqFalseOfLt hGt, natBeqFalseOfLt hEvenGt]
  rfl

private theorem execWavefrontPopped_queues (pol : SpawnPolicy) (hd : WorkerTask)
    (remFifo remSteal : List WorkerTask) (w wOut : WavefrontWorld)
    (hStep : execWavefrontPopped pol hd remFifo remSteal w = .returned wOut) :
    spawnAdmissible hd.rank (pol hd.rank).1 (pol hd.rank).2.1 = true ∧
    ((∃ y' : Nat,
        hd.remYields = y' + 1 ∧
        wOut.fifoQueue = remFifo ++
          [WorkerTask.mk hd.taskId hd.rank y' hd.loanId hd.scopeId
          hd.writeDelta] ∧
        wOut.stealDeque =
          mkWorkers w.nextTaskId (pol hd.rank).1 (pol hd.rank).2.1 (pol
            hd.rank).2.2 hd.loanId hd.scopeId hd.writeDelta ++ remSteal) ∨
     (hd.remYields = 0 ∧
      wOut.fifoQueue = remFifo ∧
      wOut.stealDeque =
        mkWorkers w.nextTaskId (pol hd.rank).1 (pol hd.rank).2.1 (pol
          hd.rank).2.2 hd.loanId hd.scopeId hd.writeDelta ++ remSteal)) := by
  dsimp only [execWavefrontPopped] at hStep
  change (match spawnAdmissible hd.rank (pol hd.rank).1 (pol hd.rank).2.1 with
    | false => HybridOut.faultInvalidSpawn
    | true => _) = _ at hStep
  cases hAdm : spawnAdmissible hd.rank (pol hd.rank).1 (pol hd.rank).2.1 with
  | false => rw [hAdm] at hStep; nomatch hStep
  | true =>
    rw [hAdm] at hStep
    dsimp only at hStep
    refine ⟨rfl, ?_⟩
    cases hy : hd.remYields with
    | succ y' =>
      rw [hy] at hStep
      injection hStep with hw
      rw [← hw]
      exact Or.inl ⟨y', rfl, rfl, rfl⟩
    | zero =>
      rw [hy] at hStep
      dsimp only at hStep
      cases hk : (pol hd.rank).1 with
      | succ k' =>
        rw [hk] at hStep
        injection hStep with hw
        rw [← hw]
        exact Or.inr ⟨rfl, rfl, rfl⟩
      | zero =>
        rw [hk] at hStep
        dsimp only at hStep
        cases hFl : wfFindLoan hd.loanId w.loans with
        | none => rw [hFl] at hStep; nomatch hStep
        | some e =>
          rw [hFl] at hStep
          dsimp only at hStep
          cases hSc : loanPhaseMatchesScope e.phase hd.scopeId with
          | false => rw [hSc] at hStep; nomatch hStep
          | true =>
            rw [hSc] at hStep
            dsimp only at hStep
            cases hPut : byteSubLensPut e.lens w.mem (wfEncodeU32BeSlice
              (wrapU32 (e.val + hd.writeDelta))) with
            | none => rw [hPut] at hStep; nomatch hStep
            | some memOut =>
              rw [hPut] at hStep
              injection hStep with hw
              rw [← hw]
              exact Or.inr ⟨rfl, rfl, rfl⟩

private theorem execWavefrontPopped_strict_cnf_descent (pol : SpawnPolicy) (hd
    : WorkerTask)
    (remFifo remSteal : List WorkerTask) (w wOut : WavefrontWorld)
    (hQueueSum : ∀ (q : Nat),
      cnfCoeffAt q (worldMeasure w) =
        wfTaskWeightAt q hd + (wfTasksWeightAt q remFifo +
          wfTasksWeightAt q remSteal))
    (hStep : execWavefrontPopped pol hd remFifo remSteal w = .returned wOut) :
    cnfLt (worldMeasure wOut) (worldMeasure w) = true := by
  have hQ := execWavefrontPopped_queues pol hd remFifo remSteal w wOut hStep
  have hAdm := hQ.1
  cases hQ.2 with
  | inl hYield =>
    cases hYield with
    | intro y' hy =>
      let q0 := hd.rank + hd.rank
      apply cnfLt_of_coeff_drop _ _ (worldMeasure_canonical wOut)
        (worldMeasure_canonical w) q0
      · rw [cnfCoeffAt_worldMeasure, hQueueSum q0, hy.2.1, hy.2.2,
          wfTasksWeightAt_append, wfTasksWeightAt_append]
        have hCh0 := wfTasksWeightAt_mkWorkers_zero_above q0 w.nextTaskId
          (pol hd.rank).1 (pol hd.rank).2.1 (pol hd.rank).2.2 hd.loanId
            hd.scopeId hd.writeDelta
          hd.rank hAdm (natBle_refl q0)
        rw [hCh0, natAdd_zero_left]
        have hSingle : wfTasksWeightAt q0 [WorkerTask.mk hd.taskId hd.rank y'
          hd.loanId hd.scopeId hd.writeDelta] = y' := by
          dsimp only [q0, wfTasksWeightAt, List.foldr]
          rw [wfTaskWeightAt_self_even (WorkerTask.mk hd.taskId hd.rank y'
            hd.loanId hd.scopeId hd.writeDelta)]
          rfl
        rw [hSingle]
        dsimp only [q0]
        rw [wfTaskWeightAt_self_even hd, hy.1,
          natAdd_comm (wfTasksWeightAt (hd.rank + hd.rank) remFifo) y',
          natAdd_assoc y' (wfTasksWeightAt (hd.rank +
            hd.rank) remFifo) (wfTasksWeightAt (hd.rank + hd.rank) remSteal)]
        exact natLt_add_left_of_lt y' (y' + 1) _ (natLtSuccSelf y')
      · intro q hGt
        rw [cnfCoeffAt_worldMeasure, hQueueSum q, hy.2.1, hy.2.2,
          wfTasksWeightAt_append, wfTasksWeightAt_append]
        have hGe : Nat.ble (hd.rank + hd.rank) q = true :=
          natBle_trans (hd.rank + hd.rank) (hd.rank + hd.rank + 1) q
            (natBle_succ_right _ _ (natBle_refl _)) hGt
        have hCh0 := wfTasksWeightAt_mkWorkers_zero_above q w.nextTaskId
          (pol hd.rank).1 (pol hd.rank).2.1 (pol hd.rank).2.2 hd.loanId
            hd.scopeId hd.writeDelta
          hd.rank hAdm hGe
        rw [hCh0, natAdd_zero_left]
        have hSameHd : wfTasksWeightAt q [WorkerTask.mk hd.taskId hd.rank y'
          hd.loanId hd.scopeId hd.writeDelta] =
            wfTaskWeightAt q hd := by
          dsimp only [wfTasksWeightAt, List.foldr, wfTaskWeightAt]
          rw [natBeqFalseOfLt hGt]
          cases Nat.beq (hd.rank + hd.rank + 1) q <;> rfl
        rw [hSameHd, natAdd_comm (wfTasksWeightAt q remFifo) (wfTaskWeightAt q
          hd),
          natAdd_assoc (wfTaskWeightAt q hd) (wfTasksWeightAt q remFifo)
            (wfTasksWeightAt q remSteal)]
  | inr hDone =>
    let q0 := hd.rank + hd.rank + 1
    apply cnfLt_of_coeff_drop _ _ (worldMeasure_canonical wOut)
      (worldMeasure_canonical w) q0
    · rw [cnfCoeffAt_worldMeasure, hQueueSum q0, hDone.2.1, hDone.2.2,
        wfTasksWeightAt_append]
      have hGe : Nat.ble (hd.rank + hd.rank) q0 = true :=
        natBle_succ_right (hd.rank + hd.rank) (hd.rank +
          hd.rank) (natBle_refl _)
      have hCh0 := wfTasksWeightAt_mkWorkers_zero_above q0 w.nextTaskId
        (pol hd.rank).1 (pol hd.rank).2.1 (pol hd.rank).2.2 hd.loanId
          hd.scopeId hd.writeDelta
        hd.rank hAdm hGe
      rw [hCh0, natAdd_zero_left]
      dsimp only [q0]
      rw [wfTaskWeightAt_self_odd hd]
      let R := wfTasksWeightAt (hd.rank + hd.rank + 1) remFifo +
        wfTasksWeightAt (hd.rank + hd.rank + 1) remSteal
      change natLt R (1 + R) = true
      rw [natAdd_comm 1 R]
      exact natLtSuccSelf R
    · intro q hGt
      rw [cnfCoeffAt_worldMeasure, hQueueSum q, hDone.2.1, hDone.2.2,
        wfTasksWeightAt_append]
      have hGe : Nat.ble (hd.rank + hd.rank) q = true :=
        natBle_trans (hd.rank + hd.rank) q0 q
          (natBle_succ_right _ _ (natBle_refl _))
          (natBle_trans q0 (q0 + 1) q (natBle_succ_right _ _ (natBle_refl _))
            hGt)
      have hCh0 := wfTasksWeightAt_mkWorkers_zero_above q w.nextTaskId
        (pol hd.rank).1 (pol hd.rank).2.1 (pol hd.rank).2.2 hd.loanId
          hd.scopeId hd.writeDelta
        hd.rank hAdm hGe
      rw [hCh0, natAdd_zero_left, wfTaskWeightAt_zero_above_odd hd q hGt,
        natAdd_zero_left]

/-- Under an admissible `SpawnPolicy`, popping one task and appending its
spawned children strictly decreases `worldMeasure` under `cnfLt`. -/
theorem wavefrontStep_strict_cnf_descent (pol : SpawnPolicy) (w wOut :
    WavefrontWorld)
    (hEval : evalHybridCmd (.poolWavefrontStep pol) w = .returned wOut) :
    cnfLt (worldMeasure wOut) (worldMeasure w) = true := by
  dsimp only [evalHybridCmd] at hEval
  cases hF : w.fifoQueue with
  | cons hd ft =>
    rw [hF] at hEval
    apply execWavefrontPopped_strict_cnf_descent pol hd ft w.stealDeque w wOut
      _ hEval
    intro q
    rw [cnfCoeffAt_worldMeasure, hF]
    dsimp only [wfTasksWeightAt, List.foldr]
    rw [natAdd_assoc]
  | nil =>
    rw [hF] at hEval
    cases hS : w.stealDeque with
    | nil => rw [hS] at hEval; nomatch hEval
    | cons hd stTail =>
      rw [hS] at hEval
      apply execWavefrontPopped_strict_cnf_descent pol hd [] stTail w wOut _
        hEval
      intro q
      rw [cnfCoeffAt_worldMeasure, hF, hS]
      dsimp only [wfTasksWeightAt, List.foldr]
      rw [natAdd_zero_left, natAdd_zero_left]

/-- Returns `true` iff either `fifoQueue` or `stealDeque` is non-empty. -/
@[expose] def wfPoolIsNonEmpty (w : WavefrontWorld) : Bool :=
  match w.fifoQueue with
  | _ :: _ => true
  | [] =>
    match w.stealDeque with
    | _ :: _ => true
    | [] => false

/-- Under `LoansSyncedWithMem` and `QueueMatchesLoans`, `execWavefrontPopped`
succeeds without loan faults and preserves both invariants. -/
theorem execWavefrontPopped_returns_and_preserves (pol : SpawnPolicy)
    (hd : WorkerTask) (remFifo remSteal : List WorkerTask) (w : WavefrontWorld)
    (hAdm : spawnAdmissible hd.rank (pol hd.rank).1 (pol hd.rank).2.1 = true)
    (hSync : LoansSyncedWithMem w.loans w.mem)
    (hHdLoan : (match wfFindLoan hd.loanId w.loans with
      | none => false
      | some e => loanPhaseMatchesScope e.phase hd.scopeId) = true)
    (hRemFifo : queueMatchesLoansBool remFifo w.loans = true)
    (hRemSteal : queueMatchesLoansBool remSteal w.loans = true) :
    ∃ wOut : WavefrontWorld,
      execWavefrontPopped pol hd remFifo remSteal w = .returned wOut ∧
      LoansSyncedWithMem wOut.loans wOut.mem ∧
      QueueMatchesLoans wOut ∧
      wOut.cells = w.cells ∧
      wOut.stepCount = w.stepCount + 1 ∧
      (∀ (lid2 : Pos4),
        Pos4.beq hd.loanId lid2 = false →
        (!anyTaskHasLoan lid2 remFifo && !anyTaskHasLoan lid2 remSteal) = true →
        wfFindLoan lid2 wOut.loans = wfFindLoan lid2 w.loans ∧
        (!anyTaskHasLoan lid2 wOut.fifoQueue &&
          !anyTaskHasLoan lid2 wOut.stealDeque) = true) := by
  dsimp only [execWavefrontPopped]
  rw [hAdm]
  dsimp only
  cases hy : hd.remYields with
  | succ y' =>
    have hQOut : QueueMatchesLoans {
        mem := w.mem, loans := w.loans, cells := w.cells,
        fifoQueue := remFifo ++ [WorkerTask.mk hd.taskId hd.rank y' hd.loanId
          hd.scopeId hd.writeDelta],
        stealDeque := mkWorkers w.nextTaskId (pol hd.rank).1 (pol hd.rank).2.1
          (pol hd.rank).2.2 hd.loanId hd.scopeId hd.writeDelta ++ remSteal,
        nextTaskId := w.nextTaskId + (pol hd.rank).1,
        completedCount := w.completedCount, stepCount := w.stepCount + 1 } := by
      refine bandIntro ?_ ?_
      · dsimp only
        rw [queueMatchesLoansBool_append]
        exact bandIntro hRemFifo (bandIntro hHdLoan rfl)
      · dsimp only
        rw [queueMatchesLoansBool_append]
        exact bandIntro (queueMatchesLoansBool_mkWorkers _ _ _ _ _ _ _ w.loans
          hHdLoan) hRemSteal
    refine ⟨_, rfl, hSync, hQOut, rfl, rfl, ?_⟩
    intro lid2 hNe hRemOk
    refine ⟨rfl, ?_⟩
    dsimp only
    rw [anyTaskHasLoan_append, anyTaskHasLoan_append,
      mkWorkers_not_hasLoan hd.loanId lid2 _ _ _ _ _ _ hNe]
    have hSingle : anyTaskHasLoan lid2 [WorkerTask.mk hd.taskId hd.rank y'
      hd.loanId hd.scopeId hd.writeDelta] = false := by
      dsimp only [anyTaskHasLoan, List.foldr]
      rw [hNe]
      rfl
    rw [hSingle, trueOfBnotTrue (bandLeft hRemOk),
      trueOfBnotTrue (bandRight hRemOk)]
    rfl
  | zero =>
    dsimp only
    cases hk : (pol hd.rank).1 with
    | succ k' =>
      have hQOut : QueueMatchesLoans {
          mem := w.mem, loans := w.loans, cells := w.cells,
          fifoQueue := remFifo,
          stealDeque := mkWorkers w.nextTaskId (k' +
            1) (pol hd.rank).2.1 (pol hd.rank).2.2 hd.loanId hd.scopeId
            hd.writeDelta ++ remSteal,
          nextTaskId := w.nextTaskId + (k' + 1),
          completedCount := w.completedCount + 1, stepCount :=
            w.stepCount + 1 } := by
        refine bandIntro hRemFifo ?_
        dsimp only
        rw [queueMatchesLoansBool_append]
        exact bandIntro (queueMatchesLoansBool_mkWorkers _ _ _ _ _ _ _ w.loans
          hHdLoan) hRemSteal
      refine ⟨_, rfl, hSync, hQOut, rfl, rfl, ?_⟩
      intro lid2 hNe hRemOk
      refine ⟨rfl, ?_⟩
      dsimp only
      rw [anyTaskHasLoan_append, mkWorkers_not_hasLoan hd.loanId lid2 _ _ _ _ _
        _ hNe,
        trueOfBnotTrue (bandLeft hRemOk), trueOfBnotTrue (bandRight hRemOk)]
      rfl
    | zero =>
      dsimp only
      cases hFl : wfFindLoan hd.loanId w.loans with
      | none => rw [hFl] at hHdLoan; exact False.elim (boolFalseNeTrue hHdLoan)
      | some e =>
        rw [hFl] at hHdLoan
        dsimp only at hHdLoan
        dsimp only
        rw [hHdLoan]
        dsimp only
        have hPhEq : e.phase = .spatialCheckedOut hd.scopeId := by
          cases hp : e.phase with
          | spatialCheckedOut s =>
            rw [hp] at hHdLoan
            dsimp only [loanPhaseMatchesScope] at hHdLoan
            exact congrArg WfLoanPhase.spatialCheckedOut (natEq_of_beq s
              hd.scopeId hHdLoan)
          | activeMut | frozen | ended =>
            rw [hp] at hHdLoan; exact False.elim (boolFalseNeTrue hHdLoan)
        have hLiveE : loanPhaseIsLive e.phase = true := by rw [hPhEq]; rfl
        have hProps := wfFindLoan_synced_live_props w.loans w.mem hd.loanId e
          hSync hFl hLiveE
        let newVal := wrapU32 (e.val + hd.writeDelta)
        have hLenSl : (wfEncodeU32BeSlice newVal).length = e.lens.size := by
          rw [wfEncodeU32BeSlice_length, hProps.2.1]
        cases byteSubLens_put_succeeds_of_get e.lens w.mem (wfEncodeU32BeSlice
          e.val)
            (wfEncodeU32BeSlice newVal) hProps.2.2.2 hLenSl with
        | intro memOut hPut =>
          dsimp only [newVal] at hPut
          rw [hPut]
          dsimp only
          let stillInFlight :=
            anyTaskHasLoanScope hd.loanId hd.scopeId remFifo ||
            anyTaskHasLoanScope hd.loanId hd.scopeId remSteal
          let nextPh := match stillInFlight with
            | true => WfLoanPhase.spatialCheckedOut hd.scopeId
            | false => WfLoanPhase.activeMut
          have hNextLive : loanPhaseIsLive nextPh = true := by
            dsimp only [nextPh]
            cases stillInFlight <;> rfl
          have hSyncNext : LoansSyncedWithMem (wfSetLoanEntryAt w.loans
            hd.loanId nextPh newVal) memOut :=
            loansSyncedWithMem_set_and_put w.loans w.mem memOut hd.loanId e
              nextPh newVal
              hSync hFl hNextLive (Eq.symm (wrapU32_idem (e.val +
                hd.writeDelta))) hPut
          have hQNext : QueueMatchesLoans {
              mem := memOut, loans :=
                wfSetLoanEntryAt w.loans hd.loanId nextPh newVal,
              cells := w.cells, fifoQueue := remFifo, stealDeque := remSteal,
              nextTaskId := w.nextTaskId, completedCount :=
                w.completedCount + 1,
              stepCount := w.stepCount + 1 } := by
            have hScF := anyTaskHasLoanScope_eq_anyTaskHasLoan_of_queueMatches
              hd.loanId hd.scopeId e remFifo w.loans hFl hPhEq hRemFifo
            have hScS := anyTaskHasLoanScope_eq_anyTaskHasLoan_of_queueMatches
              hd.loanId hd.scopeId e remSteal w.loans hFl hPhEq hRemSteal
            dsimp only [QueueMatchesLoans, checkQueueMatchesLoansBool, nextPh,
              stillInFlight]
            cases hAny : (anyTaskHasLoanScope hd.loanId hd.scopeId remFifo ||
                anyTaskHasLoanScope hd.loanId hd.scopeId remSteal) with
            | true =>
              dsimp only
              rw [← hPhEq]
              exact bandIntro
                (queueMatchesLoansBool_wfSetLoanEntryAt_samePhase remFifo
                  w.loans hd.loanId e newVal hFl hRemFifo)
                (queueMatchesLoansBool_wfSetLoanEntryAt_samePhase remSteal
                  w.loans hd.loanId e newVal hFl hRemSteal)
            | false =>
              dsimp only
              rw [hScF, hScS] at hAny
              have hNoBoth := borFalseElim hAny
              exact bandIntro
                (queueMatchesLoansBool_wfSetLoanEntryAt_of_not_hasLoan remFifo
                  w.loans hd.loanId .activeMut newVal hNoBoth.1 hRemFifo)
                (queueMatchesLoansBool_wfSetLoanEntryAt_of_not_hasLoan remSteal
                  w.loans hd.loanId .activeMut newVal hNoBoth.2 hRemSteal)
          exact ⟨_, rfl, hSyncNext, hQNext, rfl, rfl, fun lid2 hNe hRemOk =>
            ⟨wfFindLoan_wfSetLoanEntryAt_ne w.loans hd.loanId lid2 nextPh
              newVal hNe, hRemOk⟩⟩

private theorem nonEmptyPool_wavefrontStep_returns (pol : SpawnPolicy) (hPol :
    PolicyAdmissible pol)
    (w : WavefrontWorld) (hNonEmpty : wfPoolIsNonEmpty w = true)
    (hSync : LoansSyncedWithMem w.loans w.mem)
    (hQ : QueueMatchesLoans w) :
    ∃ wOut : WavefrontWorld,
      evalHybridCmd (.poolWavefrontStep pol) w = .returned wOut ∧
      LoansSyncedWithMem wOut.loans wOut.mem ∧
      QueueMatchesLoans wOut ∧
      wOut.cells = w.cells ∧
      wOut.stepCount = w.stepCount + 1 ∧
      (∀ (lid2 : Pos4),
        (!anyTaskHasLoan lid2 w.fifoQueue &&
          !anyTaskHasLoan lid2 w.stealDeque) = true →
        wfFindLoan lid2 wOut.loans = wfFindLoan lid2 w.loans ∧
        (!anyTaskHasLoan lid2 wOut.fifoQueue &&
          !anyTaskHasLoan lid2 wOut.stealDeque) = true) := by
  dsimp only [evalHybridCmd]
  dsimp only [wfPoolIsNonEmpty] at hNonEmpty
  have hQF := bandLeft hQ
  have hQS := bandRight hQ
  cases hF : w.fifoQueue with
  | cons hd ft =>
    rw [hF] at hQF
    dsimp only [queueMatchesLoansBool, List.foldr] at hQF
    cases execWavefrontPopped_returns_and_preserves pol hd ft w.stealDeque w
      (hPol hd.rank)
        hSync (bandLeft hQF) (bandRight hQF) hQS with
    | intro wOut hw =>
      refine ⟨wOut, hw.1, hw.2.1, hw.2.2.1, hw.2.2.2.1, hw.2.2.2.2.1, ?_⟩
      intro lid2 hNoIn
      have hNotF := trueOfBnotTrue (bandLeft hNoIn)
      change (Pos4.beq hd.loanId lid2 ||
        anyTaskHasLoan lid2 ft) = false at hNotF
      have hSplitF := borFalseElim hNotF
      exact hw.2.2.2.2.2 lid2 hSplitF.1
        (bandIntro (by rw [hSplitF.2]; rfl) (bandRight hNoIn))
  | nil =>
    rw [hF] at hNonEmpty hQF
    cases hS : w.stealDeque with
    | nil => rw [hS] at hNonEmpty; exact False.elim (boolFalseNeTrue hNonEmpty)
    | cons hd stTail =>
      rw [hS] at hQS
      dsimp only [queueMatchesLoansBool, List.foldr] at hQS
      cases execWavefrontPopped_returns_and_preserves pol hd [] stTail w (hPol
        hd.rank)
          hSync (bandLeft hQS) rfl (bandRight hQS) with
      | intro wOut hw =>
        refine ⟨wOut, hw.1, hw.2.1, hw.2.2.1, hw.2.2.2.1, hw.2.2.2.2.1, ?_⟩
        intro lid2 hNoIn
        have hNotS := trueOfBnotTrue (bandRight hNoIn)
        change (Pos4.beq hd.loanId lid2 ||
          anyTaskHasLoan lid2 stTail) = false at hNotS
        have hSplitS := borFalseElim hNotS
        exact hw.2.2.2.2.2 lid2 hSplitS.1
          (bandIntro rfl (by rw [hSplitS.2]; rfl))

/-- `VSepWpOrdRel` rule for `.poolWavefrontStep pol`: establishes
`.strictDescent` (`cnfLt (worldMeasure wOut) (worldMeasure wIn) = true`) while
preserving `WorldMatches`. -/
theorem vsepWpOrdRel_wavefrontStep_strict_descent
    (pol : SpawnPolicy) (hPol : PolicyAdmissible pol) :
    VSepWpOrdRel (.poolWavefrontStep pol) .strictDescent
      (fun w => wfPoolIsNonEmpty w = true)
      vemp (fun wOut => vMinStep wOut.stepCount) :=
  VSepWpOrdRel.mk rfl (fun v F rIn wIn hNe hPre hM => by
    have hFIn : F.holds v rIn := vsep_vemp_elim v F rIn hPre
    cases nonEmptyPool_wavefrontStep_returns pol hPol wIn hNe hM.loansMemOk
      hM.queueLoansOk with
    | intro wOut hw =>
      have hLt := wavefrontStep_strict_cnf_descent pol wIn wOut hw.1
      have hLe := cnfBle_of_lt (worldMeasure wOut) (worldMeasure wIn) hLt
      let vOut := bumpView0 v wOut.stepCount
      have hVLe : ViewLe v vOut :=
        viewLe_bumpView0 v wOut.stepCount
          (by
            rw [hw.2.2.2.2.1]
            exact natBle_succ_right (viewGet v 0) wIn.stepCount hM.viewOk)
      have hFOut : F.holds vOut rIn :=
        F.upClosed v vOut rIn rIn hVLe (resTrieSub_refl rIn) hFIn
      have hMinStepHold : (vMinStep wOut.stepCount).holds vOut .empty := by
        dsimp only [vMinStep, vOut]
        rw [viewGet_bumpView0_zero]
        exact natBle_refl wOut.stepCount
      have hPostHold : (vsep (vMinStep wOut.stepCount) F).holds vOut rIn :=
        ⟨.empty, rIn, resTrieMerge_empty_left_fuel resFuel rIn, hMinStepHold,
          hFOut⟩
      have hPoolDebtOut : checkWorldMatchesPoolBool rIn wOut = true := by
        have hInOk := hM.poolDebtOk
        dsimp only [checkWorldMatchesPoolBool] at hInOk
        dsimp only [checkWorldMatchesPoolBool]
        cases hPc : extractPoolCap rIn with
        | none => rw [hPc] at hInOk; exact False.elim (boolFalseNeTrue hInOk)
        | some poolCap =>
          rw [hPc] at hInOk; dsimp only at hInOk; dsimp only
          cases hDc : extractDebtCap rIn with
          | none => rw [hDc] at hInOk; exact False.elim (boolFalseNeTrue hInOk)
          | some debtCap =>
            rw [hDc] at hInOk; dsimp only at hInOk; dsimp only
            have h1 : cnfBle (worldMeasure wOut) poolCap = true :=
              cnfBle_trans _ _ _ hLe (bandLeft hInOk)
            have hMonoD : cnfBle (cnfAddOrd debtCap (worldMeasure wOut))
                (cnfAddOrd debtCap (worldMeasure wIn)) = true :=
              cnfBle_cnfNatAdd_right debtCap (worldMeasure wOut) (worldMeasure
                wIn)
                (worldMeasure_canonical wOut) (worldMeasure_canonical wIn) hLe
            have h2 : cnfBle (cnfAddOrd debtCap (worldMeasure wOut)) poolCap =
              true :=
              cnfBle_trans _ _ _ hMonoD (bandRight hInOk)
            exact bandIntro h1 h2
      have hViewOut : Nat.ble (viewGet vOut 0) wOut.stepCount = true := by
        dsimp only [vOut]
        rw [viewGet_bumpView0_zero]
        exact natBle_refl wOut.stepCount
      have hMOut : WorldMatches vOut rIn wOut :=
        WorldMatches.mk hViewOut hw.2.1 hw.2.2.1 hPoolDebtOut
          (fun cid => by rw [hw.2.2.2.1]; exact hM.cellOk cid)
          (fun lid2 => by
            have hPrev := hM.checkedLoanOk lid2
            cases hGl2 : ResTrie.getBits (checkedLoanPath lid2) rIn with
            | none => exact True.intro
            | some elem2 =>
              rw [hGl2] at hPrev
              cases elem2 with
              | pool _ | debt _ | cell _ => exact hPrev
              | checkedOutLoan sid2 lv2 =>
                have hPres := hw.2.2.2.2.2 lid2 hPrev.1
                cases hPrev.2 with
                | intro e2 he2 =>
                  exact ⟨hPres.2, ⟨e2, Eq.trans hPres.1 he2.1, he2.2⟩⟩)
      exact ⟨wOut, rIn, vOut, hw.1, hVLe, rfl, hPostHold, hMOut, hLt⟩)

/-! ## 6. Arbitrary-Depth `< ω^ω` Convergence (`WavefrontConverges`) -/

/-- Multi-step reflexive-transitive wavefront drain relation terminating at an
empty-queue quiescent world. -/
inductive WavefrontConverges (pol : SpawnPolicy) : WavefrontWorld →
    WavefrontWorld → Prop where
  | quiescent (w : WavefrontWorld) (hEmpty : wfPoolIsNonEmpty w = false) :
      WavefrontConverges pol w w
  | step (w wNext wFinal : WavefrontWorld)
      (hNonEmpty : wfPoolIsNonEmpty w = true)
      (hStep : evalHybridCmd (.poolWavefrontStep pol) w = .returned wNext)
      (hLt : cnfLt (worldMeasure wNext) (worldMeasure w) = true)
      (hRest : WavefrontConverges pol wNext wFinal) :
      WavefrontConverges pol w wFinal

/-- Computable fuel-bounded wavefront step runner returning `some wFinal` upon
reaching quiescence. -/
@[expose] def runWavefrontSteps (fuel : Nat) (pol : SpawnPolicy) (w :
    WavefrontWorld) :
    Option WavefrontWorld :=
  @Nat.rec (fun _ => WavefrontWorld → Option WavefrontWorld)
    (fun _ => none)
    (fun _ ih cur =>
      match wfPoolIsNonEmpty cur with
      | false => some cur
      | true =>
        match evalHybridCmd (.poolWavefrontStep pol) cur with
        | .returned next => ih next
        | .faultInvalidSpawn | .faultLoanViolation => none)
    fuel w

/-- Extracts a concrete fuel bound at which `runWavefrontSteps` reproduces
`WavefrontConverges`. -/
theorem wavefrontConverges_extract_fuel (pol : SpawnPolicy) (w wFinal :
    WavefrontWorld)
    (hConv : WavefrontConverges pol w wFinal) :
    wFinal.fifoQueue = [] ∧
    wFinal.stealDeque = [] ∧
    worldMeasure wFinal = [] ∧
    ∃ fuel : Nat, runWavefrontSteps fuel pol w = some wFinal := by
  induction hConv with
  | quiescent w0 hEmp =>
    dsimp only [wfPoolIsNonEmpty] at hEmp
    cases hF : w0.fifoQueue with
    | cons _ _ => rw [hF] at hEmp; exact False.elim (boolTrueNeFalse hEmp)
    | nil =>
      rw [hF] at hEmp
      cases hS : w0.stealDeque with
      | cons _ _ => rw [hS] at hEmp; exact False.elim (boolTrueNeFalse hEmp)
      | nil =>
        refine ⟨rfl, rfl, ?_, ⟨1, ?_⟩⟩
        · dsimp only [worldMeasure]; rw [hF, hS]; rfl
        · change
            (match wfPoolIsNonEmpty w0 with
             | false => some w0
             | true => _) = some w0
          dsimp only [wfPoolIsNonEmpty]; rw [hF, hS]
  | step w0 w1 wf hNe hSt _ _ ih =>
    cases ih.2.2.2 with
    | intro f hf =>
      refine ⟨ih.1, ih.2.1, ih.2.2.1, ⟨f + 1, ?_⟩⟩
      change (match wfPoolIsNonEmpty w0 with
        | false => some w0
        | true =>
          match evalHybridCmd (.poolWavefrontStep pol) w0 with
          | .returned next => runWavefrontSteps f pol next
          | .faultInvalidSpawn | .faultLoanViolation => none) = some wf
      rw [hNe, hSt]
      exact hf

/-- Arbitrary-depth `< ω^ω` convergence for every admissible spawn policy and
every strictly descending rank tower (`[propext]`). -/
theorem multiRank_wavefront_terminates_arbitrary_depth :
    (∀ (pol : SpawnPolicy), PolicyAdmissible pol →
      ∀ (w0 : WavefrontWorld),
        LoansSyncedWithMem w0.loans w0.mem →
        QueueMatchesLoans w0 →
        ∃ wFinal : WavefrontWorld,
          WavefrontConverges pol w0 wFinal ∧
          LoansSyncedWithMem wFinal.loans wFinal.mem ∧
          QueueMatchesLoans wFinal ∧
          wFinal.fifoQueue = [] ∧
          wFinal.stealDeque = [] ∧
          worldMeasure wFinal = [] ∧
          (∃ fuel : Nat, runWavefrontSteps fuel pol w0 = some wFinal)) ∧
    (∀ (ranks : List Nat) (fanout childYields : Nat) (w0 : WavefrontWorld),
      isStrictlyDescendingTower ranks = true →
      LoansSyncedWithMem w0.loans w0.mem →
      QueueMatchesLoans w0 →
      ∃ wFinal : WavefrontWorld,
        WavefrontConverges (towerLookupNext ranks fanout childYields) w0
          wFinal ∧
        LoansSyncedWithMem wFinal.loans wFinal.mem ∧
        QueueMatchesLoans wFinal ∧
        worldMeasure wFinal = []) := by
  have hUniv : ∀ (pol : SpawnPolicy), PolicyAdmissible pol →
      ∀ (ord : CnfOrd), isCanonicalCnf ord = true →
      ∀ (w0 : WavefrontWorld), worldMeasure w0 = ord →
      LoansSyncedWithMem w0.loans w0.mem →
      QueueMatchesLoans w0 →
      ∃ wFinal : WavefrontWorld,
        WavefrontConverges pol w0 wFinal ∧
        LoansSyncedWithMem wFinal.loans wFinal.mem ∧
        QueueMatchesLoans wFinal := by
    intro pol hPol ord hCan
    induction cnfAcc_all ord hCan with
    | intro x _ ih =>
      intro w0 hMeas hSync0 hQ0
      cases hNe : wfPoolIsNonEmpty w0 with
      | false => exact ⟨w0, WavefrontConverges.quiescent w0 hNe, hSync0, hQ0⟩
      | true =>
        cases nonEmptyPool_wavefrontStep_returns pol hPol w0 hNe hSync0 hQ0 with
        | intro wNext hwNext =>
          have hStep := hwNext.1
          have hLt0 : cnfLt (worldMeasure wNext) (worldMeasure w0) = true :=
            wavefrontStep_strict_cnf_descent pol w0 wNext hStep
          have hLtX : cnfLt (worldMeasure wNext) x = true := by
            rw [← hMeas]; exact hLt0
          have hCanNext : isCanonicalCnf (worldMeasure wNext) = true :=
            worldMeasure_canonical wNext
          cases ih (worldMeasure wNext) hCanNext hLtX hCanNext wNext rfl
              hwNext.2.1 hwNext.2.2.1 with
          | intro wFinal hRest =>
            exact ⟨wFinal,
              WavefrontConverges.step w0 wNext wFinal hNe hStep hLt0 hRest.1,
              hRest.2⟩
  refine ⟨?_, ?_⟩
  · intro pol hPol w0 hSync0 hQ0
    cases hUniv pol hPol (worldMeasure w0) (worldMeasure_canonical w0) w0 rfl
        hSync0 hQ0 with
    | intro wFinal hRes =>
      have hEx := wavefrontConverges_extract_fuel pol w0 wFinal hRes.1
      exact ⟨wFinal, hRes.1, hRes.2.1, hRes.2.2, hEx.1, hEx.2.1, hEx.2.2.1,
        hEx.2.2.2⟩
  · intro ranks fanout childYields w0 hDesc hSync0 hQ0
    have hPol := towerLookupNext_admissible ranks fanout childYields hDesc
    cases hUniv (towerLookupNext ranks fanout childYields) hPol
        (worldMeasure w0) (worldMeasure_canonical w0) w0 rfl hSync0 hQ0 with
    | intro wFinal hRes =>
      exact ⟨wFinal, hRes.1, hRes.2.1, hRes.2.2,
        (wavefrontConverges_extract_fuel _ w0 wFinal hRes.1).2.2.1⟩

/-! ## 7. Leaf-Count Multiplier and Universal `.activeMut` Reclamation -/

private theorem natZeroMul (n : Nat) : 0 * n = 0 := by
  induction n with
  | zero => rfl
  | succ _ ih => exact ih

private theorem natSuccMul (a b : Nat) : (a + 1) * b = a * b + b := by
  induction b with
  | zero => rfl
  | succ k ih =>
    change (a + 1) * k + (a + 1) = (a * k + a) + (k + 1)
    rw [ih, natAdd_assoc (a * k) k (a + 1), ← natAdd_assoc k a 1,
      natAdd_comm k a, natAdd_assoc a k 1, ← natAdd_assoc (a * k) a (k + 1)]

private theorem natOneMul (n : Nat) : 1 * n = n := by
  have h := natSuccMul 0 n
  rw [natZeroMul n, natAdd_zero_left n] at h
  exact h

private theorem natAddMul (a b c : Nat) : (a + b) * c = a * c + b * c := by
  induction a with
  | zero => rw [natZeroMul, natAdd_zero_left, natAdd_zero_left]
  | succ a' ih =>
    have h1 : (a' + 1) + b = (a' + b) + 1 := by
      rw [natAdd_assoc a' 1 b, natAdd_comm 1 b, ← natAdd_assoc a' b 1]
    rw [h1, natSuccMul, ih, natSuccMul, natAdd_assoc (a' * c) (b * c) c,
      natAdd_comm (b * c) c, ← natAdd_assoc (a' * c) c (b * c)]

/-- Bounded `@Nat.rec` helper computing transitive zero-fanout leaf writebacks.
-/
@[expose] def rankLeafMultAt (pol : SpawnPolicy) (fuel : Nat) : Nat → Nat → Nat
    :=
  @Nat.rec (fun _ => Nat → Nat → Nat)
    (fun _ _ => 0)
    (fun _ ih r y =>
      let p := pol r
      let childOne := ih p.2.1 p.2.2
      let zeroYield := match p.1 with
        | 0 => 1
        | k' + 1 => (k' + 1) * childOne
      y * (p.1 * childOne) + zeroYield)
    fuel

private theorem rankLeafMultAt_succ (pol : SpawnPolicy) (n r y : Nat) :
    rankLeafMultAt pol (n + 1) r y =
      let p := pol r
      let childOne := rankLeafMultAt pol n p.2.1 p.2.2
      y * (p.1 * childOne) + (match p.1 with | 0 => 1 | k' + 1 => (k' +
        1) * childOne) := rfl

private theorem rankLeafMultAt_fuel_irrel (pol : SpawnPolicy) (hPol :
    PolicyAdmissible pol)
    (f1 : Nat) :
    ∀ (f2 r y : Nat),
      natLt r f1 = true →
      natLt r f2 = true →
      rankLeafMultAt pol f1 r y = rankLeafMultAt pol f2 r y := by
  induction f1 with
  | zero =>
    intro _ r _ h1 _
    exact False.elim (boolFalseNeTrue h1)
  | succ n1 ih =>
    intro f2 r y h1 h2
    cases f2 with
    | zero => exact False.elim (boolFalseNeTrue h2)
    | succ n2 =>
      rw [rankLeafMultAt_succ, rankLeafMultAt_succ]
      dsimp only
      have hAdm := hPol r
      dsimp only [spawnAdmissible] at hAdm
      cases hk : (pol r).1 with
      | zero =>
        rw [natZeroMul, natZeroMul]
      | succ k' =>
        rw [hk] at hAdm
        have hLe1 : Nat.ble r n1 = true := h1
        have hLe2 : Nat.ble r n2 = true := h2
        have hCh1 : natLt (pol r).2.1 n1 = true :=
          natLtOfLtOfBle _ r n1 hAdm hLe1
        have hCh2 : natLt (pol r).2.1 n2 = true :=
          natLtOfLtOfBle _ r n2 hAdm hLe2
        rw [ih n2 (pol r).2.1 (pol r).2.2 hCh1 hCh2]

/-- Total number of zero-fanout leaf writebacks transitively generated by one
task at `(rank, remYields)` under `pol`. -/
@[expose] def taskLeafMult (pol : SpawnPolicy) (rank remYields : Nat) : Nat :=
  rankLeafMultAt pol (rank + 1) rank remYields

private theorem taskLeafMult_unfold (pol : SpawnPolicy) (hPol :
    PolicyAdmissible pol) (r y : Nat) :
    taskLeafMult pol r y =
      y * ((pol r).1 * taskLeafMult pol (pol r).2.1 (pol r).2.2) +
      (match (pol r).1 with
       | 0 => 1
       | k' + 1 => (k' + 1) * taskLeafMult pol (pol r).2.1 (pol r).2.2) := by
  dsimp only [taskLeafMult]
  rw [rankLeafMultAt_succ]
  dsimp only
  have hAdm := hPol r
  dsimp only [spawnAdmissible] at hAdm
  cases hk : (pol r).1 with
  | zero =>
    rw [natZeroMul, natZeroMul]
  | succ k' =>
    rw [hk] at hAdm
    have hEq := rankLeafMultAt_fuel_irrel pol hPol r ((pol r).2.1 +
      1) (pol r).2.1 (pol r).2.2
      hAdm (natLtSuccSelf _)
    rw [hEq]

/-- Total `u32` write delta contributed to loan `lid` by task `t` (`taskLeafMult
* writeDelta` if `t.loanId == lid`, else `0`). -/
@[expose] def taskLoanDelta (pol : SpawnPolicy) (lid : Pos4) (t : WorkerTask) :
    Nat :=
  match Pos4.beq t.loanId lid with
  | true => taskLeafMult pol t.rank t.remYields * t.writeDelta
  | false => 0

/-- Sums `taskLoanDelta pol lid` across task list `qs`. -/
@[expose] def queueLoanDeltaSum (pol : SpawnPolicy) (lid : Pos4) (qs : List
    WorkerTask) :
    Nat :=
  qs.foldr (fun t acc => taskLoanDelta pol lid t + acc) 0

/-- Total pending `u32` write delta for loan `lid` across `w.fifoQueue` and
`w.stealDeque`. -/
@[expose] def worldLoanDeltaSum (pol : SpawnPolicy) (lid : Pos4) (w :
    WavefrontWorld) :
    Nat :=
  queueLoanDeltaSum pol lid w.fifoQueue + queueLoanDeltaSum pol lid w.stealDeque

private theorem queueLoanDeltaSum_append (pol : SpawnPolicy) (lid : Pos4) (xs
    ys : List WorkerTask) :
    queueLoanDeltaSum pol lid (xs ++ ys) =
      queueLoanDeltaSum pol lid xs + queueLoanDeltaSum pol lid ys := by
  induction xs with
  | nil => exact Eq.symm (natAdd_zero_left _)
  | cons hd _ ih =>
    change taskLoanDelta pol lid hd + queueLoanDeltaSum pol lid (_ ++ ys) =
      (taskLoanDelta pol lid hd + queueLoanDeltaSum pol lid _) +
        queueLoanDeltaSum pol lid ys
    rw [ih, natAdd_assoc]

private theorem queueLoanDeltaSum_zero_of_not_hasLoan (pol : SpawnPolicy) (lid
    : Pos4) (qs : List WorkerTask)
    (hNo : anyTaskHasLoan lid qs = false) :
    queueLoanDeltaSum pol lid qs = 0 := by
  induction qs with
  | nil => rfl
  | cons t tl ih =>
    dsimp only [anyTaskHasLoan, List.foldr] at hNo
    have hSp := borFalseElim hNo
    change taskLoanDelta pol lid t + queueLoanDeltaSum pol lid tl = 0
    dsimp only [taskLoanDelta]
    rw [hSp.1, natAdd_zero_left]
    exact ih hSp.2

private theorem queueLoanDeltaSum_mkWorkers_same (pol : SpawnPolicy) (baseId k
    rc cy : Nat)
    (lid : Pos4) (sc wd : Nat) :
    queueLoanDeltaSum pol lid (mkWorkers baseId k rc cy lid sc wd) =
      (k * taskLeafMult pol rc cy) * wd := by
  revert baseId
  induction k with
  | zero =>
    intro _
    rw [natZeroMul, natZeroMul]
    rfl
  | succ m ih =>
    intro baseId
    change taskLoanDelta pol lid (WorkerTask.mk baseId rc cy lid sc wd) +
      queueLoanDeltaSum pol lid (mkWorkers (baseId + 1) m rc cy lid sc wd) =
      ((m + 1) * taskLeafMult pol rc cy) * wd
    dsimp only [taskLoanDelta]
    rw [pos4_beq_refl lid, ih (baseId + 1),
      natSuccMul m (taskLeafMult pol rc cy),
      natAddMul (m * taskLeafMult pol rc cy) (taskLeafMult pol rc cy) wd,
      natAdd_comm (taskLeafMult pol rc cy * wd) _]

private theorem mkWorkers_hasLoan_succ (baseId m rc cy : Nat) (lid : Pos4) (sc
    wd : Nat) :
    anyTaskHasLoan lid (mkWorkers baseId (m + 1) rc cy lid sc wd) = true := by
  change (Pos4.beq lid lid || anyTaskHasLoan lid (mkWorkers (baseId +
    1) m rc cy lid sc wd)) = true
  rw [pos4_beq_refl lid]
  rfl

/-- Two-phase tracking invariant for loan `lid` across `WavefrontConverges`:
while tasks for `lid` remain queued, `wrapU32 (e.val + worldLoanDeltaSum pol lid
w) = targetVal`; once the last task for `lid` completes, `e.phase = .activeMut`
and `e.val = targetVal` across all subsequent steps. -/
@[expose] def LoanTrackInv (pol : SpawnPolicy) (lid id0 : Pos4) (lens0 :
    ByteSubLens)
    (targetVal : Nat) (w : WavefrontWorld) : Prop :=
  ∃ e : WfLoanEntry,
    wfFindLoan lid w.loans = some e ∧
    e.id = id0 ∧
    e.lens = lens0 ∧
    wrapU32 (e.val + worldLoanDeltaSum pol lid w) = targetVal ∧
    match anyTaskHasLoan lid w.fifoQueue || anyTaskHasLoan lid w.stealDeque with
    | true => True
    | false => e.phase = .activeMut ∧ e.val = targetVal

private theorem execWavefrontPopped_preserves_loanTrackInv (pol : SpawnPolicy)
    (hPol : PolicyAdmissible pol)
    (lid id0 : Pos4) (lens0 : ByteSubLens) (targetVal : Nat)
    (hd : WorkerTask) (remFifo remSteal : List WorkerTask) (w wOut :
      WavefrontWorld)
    (hRemFifo : queueMatchesLoansBool remFifo w.loans = true)
    (hRemSteal : queueMatchesLoansBool remSteal w.loans = true)
    (hAnyDecomp : (anyTaskHasLoan lid w.fifoQueue ||
      anyTaskHasLoan lid w.stealDeque) =
      (Pos4.beq hd.loanId lid || (anyTaskHasLoan lid remFifo ||
        anyTaskHasLoan lid remSteal)))
    (hSumDecomp : worldLoanDeltaSum pol lid w =
      taskLoanDelta pol lid hd + (queueLoanDeltaSum pol lid remFifo +
        queueLoanDeltaSum pol lid remSteal))
    (hInv : LoanTrackInv pol lid id0 lens0 targetVal w)
    (hStep : execWavefrontPopped pol hd remFifo remSteal w = .returned wOut) :
    LoanTrackInv pol lid id0 lens0 targetVal wOut := by
  cases hInv with
  | intro e he =>
    have hFindL := he.1
    have hId0 := he.2.1
    have hLens0 := he.2.2.1
    have hWrapTarget := he.2.2.2.1
    have hTailInv := he.2.2.2.2
    dsimp only [execWavefrontPopped] at hStep
    have hAdm : spawnAdmissible hd.rank (pol hd.rank).1 (pol hd.rank).2.1 =
      true := hPol hd.rank
    rw [hAdm] at hStep
    dsimp only at hStep
    cases hEqHd : Pos4.beq hd.loanId lid with
    | false =>
      have hNeSymm : Pos4.beq lid hd.loanId = false := by
        rw [pos4_beq_symm]; exact hEqHd
      have hHdZero : taskLoanDelta pol lid hd = 0 := by
        dsimp only [taskLoanDelta]; rw [hEqHd]
      have hSumRem : worldLoanDeltaSum pol lid w =
          queueLoanDeltaSum pol lid remFifo +
            queueLoanDeltaSum pol lid remSteal := by
        rw [hSumDecomp, hHdZero, natAdd_zero_left]
      have hAnyRem : (anyTaskHasLoan lid w.fifoQueue ||
        anyTaskHasLoan lid w.stealDeque) =
          (anyTaskHasLoan lid remFifo || anyTaskHasLoan lid remSteal) := by
        rw [hAnyDecomp, hEqHd]; rfl
      rw [hAnyRem] at hTailInv
      cases hy : hd.remYields with
      | succ y' =>
        rw [hy] at hStep
        injection hStep with hw
        rw [← hw]
        refine ⟨e, hFindL, hId0, hLens0, ?_, ?_⟩
        · dsimp only [worldLoanDeltaSum]
          rw [queueLoanDeltaSum_append, queueLoanDeltaSum_append,
            queueLoanDeltaSum_zero_of_not_hasLoan pol lid _
              (mkWorkers_not_hasLoan hd.loanId lid _ _ _ _ _ _ hEqHd),
            natAdd_zero_left]
          have hS0 : queueLoanDeltaSum pol lid [WorkerTask.mk hd.taskId hd.rank
            y' hd.loanId hd.scopeId hd.writeDelta] = 0 := by
            dsimp only [queueLoanDeltaSum, List.foldr, taskLoanDelta]
            rw [hEqHd]
          rw [hS0]
          change wrapU32 (e.val + (queueLoanDeltaSum pol lid remFifo +
            queueLoanDeltaSum pol lid remSteal)) = targetVal
          rw [← hSumRem]
          exact hWrapTarget
        · dsimp only
          rw [anyTaskHasLoan_append, anyTaskHasLoan_append,
            mkWorkers_not_hasLoan hd.loanId lid _ _ _ _ _ _ hEqHd]
          have hA0 : anyTaskHasLoan lid [WorkerTask.mk hd.taskId hd.rank y'
            hd.loanId hd.scopeId hd.writeDelta] = false := by
            dsimp only [anyTaskHasLoan, List.foldr]; rw [hEqHd]; rfl
          rw [hA0]
          have hOrF : (anyTaskHasLoan lid remFifo ||
            false) = anyTaskHasLoan lid remFifo := by
            cases anyTaskHasLoan lid remFifo <;> rfl
          have hOrS : (false || anyTaskHasLoan lid remSteal) =
            anyTaskHasLoan lid remSteal := rfl
          rw [hOrF, hOrS]
          exact hTailInv
      | zero =>
        rw [hy] at hStep
        dsimp only at hStep
        cases hk : (pol hd.rank).1 with
        | succ k' =>
          rw [hk] at hStep
          injection hStep with hw
          rw [← hw]
          refine ⟨e, hFindL, hId0, hLens0, ?_, ?_⟩
          · dsimp only [worldLoanDeltaSum]
            rw [queueLoanDeltaSum_append,
              queueLoanDeltaSum_zero_of_not_hasLoan pol lid _
                (mkWorkers_not_hasLoan hd.loanId lid _ _ _ _ _ _ hEqHd),
              natAdd_zero_left, ← hSumRem]
            exact hWrapTarget
          · dsimp only
            rw [anyTaskHasLoan_append,
              mkWorkers_not_hasLoan hd.loanId lid _ _ _ _ _ _ hEqHd]
            exact hTailInv
        | zero =>
          rw [hk] at hStep
          dsimp only at hStep
          cases hFlHd : wfFindLoan hd.loanId w.loans with
          | none => rw [hFlHd] at hStep; nomatch hStep
          | some eHd =>
            rw [hFlHd] at hStep; dsimp only at hStep
            cases hScHd : loanPhaseMatchesScope eHd.phase hd.scopeId with
            | false => rw [hScHd] at hStep; nomatch hStep
            | true =>
              rw [hScHd] at hStep; dsimp only at hStep
              cases hPut : byteSubLensPut eHd.lens w.mem (wfEncodeU32BeSlice
                (wrapU32 (eHd.val + hd.writeDelta))) with
              | none => rw [hPut] at hStep; nomatch hStep
              | some memOut =>
                rw [hPut] at hStep
                injection hStep with hw
                rw [← hw]
                refine ⟨e, ?_, hId0, hLens0, ?_, hTailInv⟩
                · dsimp only
                  rw [wfFindLoan_wfSetLoanEntryAt_ne w.loans hd.loanId lid _ _
                    hEqHd]
                  exact hFindL
                · dsimp only [worldLoanDeltaSum]
                  rw [← hSumRem]
                  exact hWrapTarget
    | true =>
      have hSameId := pos4_eq_of_beq hd.loanId lid hEqHd
      cases hy : hd.remYields with
      | succ y' =>
        rw [hy] at hStep
        injection hStep with hw
        rw [← hw]
        refine ⟨e, hFindL, hId0, hLens0, ?_, ?_⟩
        · dsimp only [worldLoanDeltaSum]
          rw [queueLoanDeltaSum_append, queueLoanDeltaSum_append, hSameId,
            queueLoanDeltaSum_mkWorkers_same]
          have hSingle : queueLoanDeltaSum pol lid [WorkerTask.mk hd.taskId
            hd.rank y' lid hd.scopeId hd.writeDelta] =
              taskLeafMult pol hd.rank y' * hd.writeDelta := by
            dsimp only [queueLoanDeltaSum, List.foldr, taskLoanDelta]
            rw [pos4_beq_refl lid]
            rfl
          rw [hSingle]
          have hHdVal : taskLoanDelta pol lid hd =
              taskLeafMult pol hd.rank (y' + 1) * hd.writeDelta := by
            dsimp only [taskLoanDelta]; rw [hEqHd, hy]
          have hUnf1 := taskLeafMult_unfold pol hPol hd.rank (y' + 1)
          have hUnf0 := taskLeafMult_unfold pol hPol hd.rank y'
          let C := (pol hd.rank).1 * taskLeafMult pol (pol hd.rank).2.1 (pol
            hd.rank).2.2
          let Z :=
            match (pol hd.rank).1 with
            | 0 => 1
            | k' + 1 =>
              (k' + 1) * taskLeafMult pol (pol hd.rank).2.1 (pol hd.rank).2.2
          have hMultSplit : taskLeafMult pol hd.rank (y' + 1) * hd.writeDelta =
              C * hd.writeDelta + taskLeafMult pol hd.rank y' * hd.writeDelta :=
                by
            rw [hUnf1, hUnf0, natSuccMul y' C, natAdd_comm (y' * C) C,
              natAdd_assoc C (y' * C) Z, natAddMul C (y' * C + Z) hd.writeDelta]
          let F := queueLoanDeltaSum pol lid remFifo
          let S := queueLoanDeltaSum pol lid remSteal
          let Y := taskLeafMult pol hd.rank y' * hd.writeDelta
          let W := C * hd.writeDelta
          have hRearr : (F + Y) + (W + S) = (W + Y) + (F + S) := by
            rw [natAdd_comm F Y, natAdd_assoc Y F (W + S), ← natAdd_assoc F W S,
              natAdd_comm F W, natAdd_assoc W F S, ← natAdd_assoc Y W (F + S),
              natAdd_comm Y W]
          change wrapU32 (e.val + ((F + Y) + (W + S))) = targetVal
          rw [hRearr, ← hMultSplit, ← hHdVal, ← hSumDecomp]
          exact hWrapTarget
        · dsimp only
          rw [anyTaskHasLoan_append, hSameId]
          have hA1 : anyTaskHasLoan lid [WorkerTask.mk hd.taskId hd.rank y' lid
            hd.scopeId hd.writeDelta] = true := by
            dsimp only [anyTaskHasLoan, List.foldr]; rw [pos4_beq_refl lid]; rfl
          rw [hA1]
          have hT1 : (anyTaskHasLoan lid remFifo || true) = true := by
            cases anyTaskHasLoan lid remFifo <;> rfl
          rw [hT1]
          exact True.intro
      | zero =>
        rw [hy] at hStep
        dsimp only at hStep
        cases hk : (pol hd.rank).1 with
        | succ k' =>
          rw [hk] at hStep
          injection hStep with hw
          rw [← hw]
          refine ⟨e, hFindL, hId0, hLens0, ?_, ?_⟩
          · dsimp only [worldLoanDeltaSum]
            rw [queueLoanDeltaSum_append, hSameId,
              queueLoanDeltaSum_mkWorkers_same]
            have hHdVal : taskLoanDelta pol lid hd =
                ((k' + 1) * taskLeafMult pol (pol hd.rank).2.1 (pol
                  hd.rank).2.2) * hd.writeDelta := by
              dsimp only [taskLoanDelta]
              rw [hEqHd, hy, taskLeafMult_unfold pol hPol hd.rank 0, hk,
                natZeroMul, natAdd_zero_left]
            let F := queueLoanDeltaSum pol lid remFifo
            let S := queueLoanDeltaSum pol lid remSteal
            let W := ((k' + 1) * taskLeafMult pol (pol hd.rank).2.1 (pol
              hd.rank).2.2) * hd.writeDelta
            have hRearr : F + (W + S) = W + (F + S) := by
              rw [← natAdd_assoc F W S, natAdd_comm F W, natAdd_assoc W F S]
            change wrapU32 (e.val + (F + (W + S))) = targetVal
            rw [hRearr]
            dsimp only [W, F, S]
            rw [← hHdVal, ← hSumDecomp]
            exact hWrapTarget
          · dsimp only
            rw [anyTaskHasLoan_append, hSameId, mkWorkers_hasLoan_succ]
            dsimp only [Bool.or]
            cases anyTaskHasLoan lid remFifo <;> exact True.intro
        | zero =>
          rw [hk] at hStep
          dsimp only at hStep
          rw [hSameId, hFindL] at hStep
          dsimp only at hStep
          cases hSc : loanPhaseMatchesScope e.phase hd.scopeId with
          | false => rw [hSc] at hStep; nomatch hStep
          | true =>
            rw [hSc] at hStep
            dsimp only at hStep
            have hPhEq : e.phase = .spatialCheckedOut hd.scopeId := by
              cases hp : e.phase with
              | spatialCheckedOut s =>
                rw [hp] at hSc
                dsimp only [loanPhaseMatchesScope] at hSc
                exact congrArg WfLoanPhase.spatialCheckedOut (natEq_of_beq s
                  hd.scopeId hSc)
              | activeMut | frozen | ended =>
                rw [hp] at hSc; exact False.elim (boolFalseNeTrue hSc)
            cases hPut : byteSubLensPut e.lens w.mem (wfEncodeU32BeSlice
              (wrapU32 (e.val + hd.writeDelta))) with
            | none => rw [hPut] at hStep; nomatch hStep
            | some memOut =>
              rw [hPut] at hStep
              injection hStep with hw
              rw [← hw]
              have hScF := anyTaskHasLoanScope_eq_anyTaskHasLoan_of_queueMatches
                lid hd.scopeId e remFifo w.loans hFindL hPhEq hRemFifo
              have hScS := anyTaskHasLoanScope_eq_anyTaskHasLoan_of_queueMatches
                lid hd.scopeId e remSteal w.loans hFindL hPhEq hRemSteal
              have hHdOne : taskLoanDelta pol lid hd = hd.writeDelta := by
                dsimp only [taskLoanDelta]
                rw [hEqHd, hy, taskLeafMult_unfold pol hPol hd.rank 0, hk,
                  natZeroMul, natAdd_zero_left, natOneMul]
              let remSum := queueLoanDeltaSum pol lid remFifo +
                queueLoanDeltaSum pol lid remSteal
              have hWrapStep : wrapU32 (wrapU32 (e.val + hd.writeDelta) +
                remSum) = targetVal := by
                rw [wrapU32_add_left, natAdd_assoc e.val hd.writeDelta remSum,
                  ← hHdOne, ← hSumDecomp]
                exact hWrapTarget
              let stillInFlight :=
                anyTaskHasLoanScope lid hd.scopeId remFifo ||
                anyTaskHasLoanScope lid hd.scopeId remSteal
              let nextPh := match stillInFlight with
                | true => WfLoanPhase.spatialCheckedOut hd.scopeId
                | false => WfLoanPhase.activeMut
              refine ⟨⟨e.id, nextPh, e.lens, wrapU32 (e.val + hd.writeDelta)⟩,
                wfFindLoan_wfSetLoanEntryAt_same w.loans lid nextPh _ e hFindL,
                hId0, hLens0, hWrapStep, ?_⟩
              dsimp only [nextPh, stillInFlight]
              rw [hScF, hScS]
              cases hRemAny : (anyTaskHasLoan lid remFifo ||
                anyTaskHasLoan lid remSteal) with
              | true => exact True.intro
              | false =>
                have hNoBoth := borFalseElim hRemAny
                have hRemSum0 : remSum = 0 := by
                  dsimp only [remSum]
                  rw [queueLoanDeltaSum_zero_of_not_hasLoan pol lid remFifo
                    hNoBoth.1,
                    queueLoanDeltaSum_zero_of_not_hasLoan pol lid remSteal
                      hNoBoth.2]
                refine ⟨rfl, ?_⟩
                rw [hRemSum0, ← natAdd_comm 0 _, natAdd_zero_left,
                  wrapU32_idem] at hWrapStep
                exact hWrapStep

private theorem wavefrontStep_preserves_loanTrackInv (pol : SpawnPolicy) (hPol
    : PolicyAdmissible pol)
    (lid id0 : Pos4) (lens0 : ByteSubLens) (targetVal : Nat)
    (w wNext : WavefrontWorld)
    (hQ : QueueMatchesLoans w)
    (hInv : LoanTrackInv pol lid id0 lens0 targetVal w)
    (hStep : evalHybridCmd (.poolWavefrontStep pol) w = .returned wNext) :
    LoanTrackInv pol lid id0 lens0 targetVal wNext := by
  dsimp only [evalHybridCmd] at hStep
  have hQF := bandLeft hQ
  have hQS := bandRight hQ
  cases hF : w.fifoQueue with
  | cons hd ft =>
    rw [hF] at hStep hQF
    dsimp only [queueMatchesLoansBool, List.foldr] at hQF
    apply execWavefrontPopped_preserves_loanTrackInv pol hPol lid id0 lens0
      targetVal
      hd ft w.stealDeque w wNext (bandRight hQF) hQS _ _ hInv hStep
    · rw [hF]; dsimp only [anyTaskHasLoan, List.foldr]
      cases Pos4.beq hd.loanId lid <;> rfl
    · dsimp only [worldLoanDeltaSum]; rw [hF]
      dsimp only [queueLoanDeltaSum, List.foldr]; rw [natAdd_assoc]
  | nil =>
    rw [hF] at hStep
    cases hS : w.stealDeque with
    | nil => rw [hS] at hStep; nomatch hStep
    | cons hd stTail =>
      rw [hS] at hStep hQS
      dsimp only [queueMatchesLoansBool, List.foldr] at hQS
      apply execWavefrontPopped_preserves_loanTrackInv pol hPol lid id0 lens0
        targetVal
        hd [] stTail w wNext rfl (bandRight hQS) _ _ hInv hStep
      · rw [hF, hS]; rfl
      · dsimp only [worldLoanDeltaSum]; rw [hF, hS]
        dsimp only [queueLoanDeltaSum, List.foldr]
        rw [natAdd_zero_left, natAdd_zero_left]

private theorem wfFindLoan_some_of_hasLoan_queueMatches (lid : Pos4) (qs : List
    WorkerTask)
    (loans : List WfLoanEntry)
    (hAny : anyTaskHasLoan lid qs = true)
    (hQ : queueMatchesLoansBool qs loans = true) :
    ∃ e0 : WfLoanEntry, wfFindLoan lid loans = some e0 ∧
      loanPhaseIsLive e0.phase = true := by
  induction qs with
  | nil => exact False.elim (boolFalseNeTrue hAny)
  | cons t tl ih =>
    dsimp only [anyTaskHasLoan, List.foldr] at hAny
    dsimp only [queueMatchesLoansBool, List.foldr] at hQ
    cases hEq : Pos4.beq t.loanId lid with
    | false =>
      rw [hEq] at hAny
      exact ih hAny (bandRight hQ)
    | true =>
      have hSame := pos4_eq_of_beq t.loanId lid hEq
      have hHd := bandLeft hQ
      rw [hSame] at hHd
      cases hFl : wfFindLoan lid loans with
      | none => rw [hFl] at hHd; exact False.elim (boolFalseNeTrue hHd)
      | some e0 =>
        rw [hFl] at hHd
        dsimp only at hHd
        refine ⟨e0, rfl, ?_⟩
        cases hp : e0.phase with
        | spatialCheckedOut _ => rfl
        | activeMut | frozen | ended =>
          rw [hp] at hHd; exact False.elim (boolFalseNeTrue hHd)

/-- Across any `WavefrontConverges pol w0 wFinal` from a world satisfying
`LoansSyncedWithMem` and `QueueMatchesLoans`, every loan `lid` with at least one
queued task in `w0` finishes in `.activeMut` phase in `wFinal` with `wrapU32
(e0.val + worldLoanDeltaSum pol lid w0)` in `wFinal.mem`. -/
theorem universal_post_drain_activeMut_reclaim
    (pol : SpawnPolicy) (hPol : PolicyAdmissible pol)
    (w0 wFinal : WavefrontWorld)
    (hSync0 : LoansSyncedWithMem w0.loans w0.mem)
    (hQ0 : QueueMatchesLoans w0)
    (hConv : WavefrontConverges pol w0 wFinal)
    (lid : Pos4)
    (hQueued : (anyTaskHasLoan lid w0.fifoQueue ||
      anyTaskHasLoan lid w0.stealDeque) = true) :
    ∃ e0 : WfLoanEntry,
      wfFindLoan lid w0.loans = some e0 ∧
      wfFindLoan lid wFinal.loans =
        some ⟨e0.id, .activeMut, e0.lens,
          wrapU32 (e0.val + worldLoanDeltaSum pol lid w0)⟩ ∧
      ActivePureLoanAt lid e0.lens (wrapU32 (e0.val +
        worldLoanDeltaSum pol lid w0)) wFinal ∧
      byteSubLensGet e0.lens wFinal.mem =
        some (wfEncodeU32BeSlice (wrapU32 (e0.val +
          worldLoanDeltaSum pol lid w0))) := by
  have hExE0 : ∃ e0 : WfLoanEntry, wfFindLoan lid w0.loans = some e0 ∧
    loanPhaseIsLive e0.phase = true := by
    cases hAF : anyTaskHasLoan lid w0.fifoQueue with
    | true =>
      exact wfFindLoan_some_of_hasLoan_queueMatches lid w0.fifoQueue w0.loans
        hAF (bandLeft hQ0)
    | false =>
      rw [hAF] at hQueued
      exact wfFindLoan_some_of_hasLoan_queueMatches lid w0.stealDeque w0.loans
        hQueued (bandRight hQ0)
  cases hExE0 with
  | intro e0 he0 =>
    let targetVal := wrapU32 (e0.val + worldLoanDeltaSum pol lid w0)
    have hInitInv : LoanTrackInv pol lid e0.id e0.lens targetVal w0 := by
      refine ⟨e0, he0.1, rfl, rfl, rfl, ?_⟩
      rw [hQueued]
      exact True.intro
    have hWalk : ∀ (u uF : WavefrontWorld),
        WavefrontConverges pol u uF →
        LoansSyncedWithMem u.loans u.mem →
        QueueMatchesLoans u →
        LoanTrackInv pol lid e0.id e0.lens targetVal u →
        LoansSyncedWithMem uF.loans uF.mem ∧
        LoanTrackInv pol lid e0.id e0.lens targetVal uF := by
      intro u uF hC
      induction hC with
      | quiescent u0 _ =>
        intro hs _ hi
        exact ⟨hs, hi⟩
      | step u0 u1 uf hNe hSt _ _ ih =>
        intro hs hq hi
        cases nonEmptyPool_wavefrontStep_returns pol hPol u0 hNe hs hq with
        | intro u1' hu1' =>
          have hEq1 : u1' = u1 := by
            rw [hSt] at hu1'
            injection hu1'.1 with hSame
            exact hSame.symm
          rw [hEq1] at hu1'
          have hi1 := wavefrontStep_preserves_loanTrackInv pol hPol lid e0.id
            e0.lens targetVal
            u0 u1 hq hi hSt
          exact ih hu1'.2.1 hu1'.2.2.1 hi1
    have hEnd := hWalk w0 wFinal hConv hSync0 hQ0 hInitInv
    have hExEmp := wavefrontConverges_extract_fuel pol w0 wFinal hConv
    cases hEnd.2 with
    | intro eF heF =>
      have hNoF : (anyTaskHasLoan lid wFinal.fifoQueue ||
        anyTaskHasLoan lid wFinal.stealDeque) = false := by
        rw [hExEmp.1, hExEmp.2.1]; rfl
      have hTailF := heF.2.2.2.2
      rw [hNoF] at hTailF
      have hEfEq : eF = ⟨e0.id, .activeMut, e0.lens, targetVal⟩ := by
        cases eF with
        | mk i p l v =>
          dsimp only at heF hTailF
          rw [heF.2.1, hTailF.1, heF.2.2.1, hTailF.2]
      have hFindFinal : wfFindLoan lid wFinal.loans =
        some ⟨e0.id, .activeMut, e0.lens, targetVal⟩ := by
        rw [← hEfEq]; exact heF.1
      have hSyncedF := wfFindLoan_synced_live_props wFinal.loans wFinal.mem lid
        ⟨e0.id, .activeMut, e0.lens, targetVal⟩ hEnd.1 hFindFinal rfl
      exact ⟨e0, he0.1, hFindFinal,
        ⟨⟨e0.id, .activeMut, e0.lens, targetVal⟩, hFindFinal, rfl, rfl, rfl⟩,
        hSyncedF.2.2.2⟩

/-- Drains any wavefront world to quiescence while advancing `vMinStep`
and preserving any spatial frame `F` and `WorldMatches`. -/
theorem vsepWpOrdRel_wavefrontDrain
    (pol : SpawnPolicy) (hPol : PolicyAdmissible pol)
    (vIn : View) (F : VProp) (rIn : ResTrie ResElem) (wIn : WavefrontWorld)
    (hPre : (vsep vemp F).holds vIn rIn)
    (hM : WorldMatches vIn rIn wIn) :
    ∃ (wDrained : WavefrontWorld) (rOut : ResTrie ResElem) (vOut : View),
      WavefrontConverges pol wIn wDrained ∧
      ViewLe vIn vOut ∧
      extractPoolCap rOut = extractPoolCap rIn ∧
      (vsep (vMinStep wDrained.stepCount) F).holds vOut rOut ∧
      WorldMatches vOut rOut wDrained := by
  have hStepWp := vsepWpOrdRel_wavefrontStep_strict_descent pol hPol
  have hInd : ∀ (ord : CnfOrd), isCanonicalCnf ord = true →
      ∀ (vCur : View) (rCur : ResTrie ResElem) (wCur : WavefrontWorld),
        worldMeasure wCur = ord →
        (vsep vemp F).holds vCur rCur →
        WorldMatches vCur rCur wCur →
        ∃ (wDrained : WavefrontWorld) (rOut : ResTrie ResElem) (vOut : View),
          WavefrontConverges pol wCur wDrained ∧
          ViewLe vCur vOut ∧
          extractPoolCap rOut = extractPoolCap rCur ∧
          (vsep (vMinStep wDrained.stepCount) F).holds vOut rOut ∧
          WorldMatches vOut rOut wDrained := by
    intro ord hCan
    induction cnfAcc_all ord hCan with
    | intro x _ ih =>
      intro vCur rCur wCur hMeas hPreCur hMCur
      cases hNe : wfPoolIsNonEmpty wCur with
      | false =>
        let vOut := bumpView0 vCur wCur.stepCount
        have hVLe : ViewLe vCur vOut :=
          viewLe_bumpView0 vCur wCur.stepCount hMCur.viewOk
        have hFOut : F.holds vOut rCur :=
          F.upClosed vCur vOut rCur rCur hVLe (resTrieSub_refl rCur)
            (vsep_vemp_elim vCur F rCur hPreCur)
        have hMinHold : (vMinStep wCur.stepCount).holds vOut .empty := by
          dsimp only [vMinStep, vOut]
          rw [viewGet_bumpView0_zero]
          exact natBle_refl wCur.stepCount
        have hViewOut : Nat.ble (viewGet vOut 0) wCur.stepCount = true := by
          dsimp only [vOut]
          rw [viewGet_bumpView0_zero]
          exact natBle_refl wCur.stepCount
        have hMOut : WorldMatches vOut rCur wCur :=
          WorldMatches.mk hViewOut hMCur.loansMemOk hMCur.queueLoansOk
            hMCur.poolDebtOk
            hMCur.cellOk hMCur.checkedLoanOk
        exact ⟨wCur, rCur, vOut, WavefrontConverges.quiescent wCur hNe, hVLe,
          rfl,
          ⟨.empty, rCur, resTrieMerge_empty_left_fuel resFuel rCur, hMinHold,
            hFOut⟩,
          hMOut⟩
      | true =>
        cases hStepWp.run vCur F rCur wCur hNe hPreCur hMCur with
        | intro wNext hw =>
          cases hw with
          | intro rMid hr =>
            cases hr with
            | intro vMid hv =>
              have hStepEv := hv.1
              have hVLe1 := hv.2.1
              have hPc1 := hv.2.2.1
              have hPost1 := hv.2.2.2.1
              have hM1 := hv.2.2.2.2.1
              have hLtOrig : cnfLt (worldMeasure wNext) (worldMeasure wCur) =
                true := hv.2.2.2.2.2
              have hLtX : cnfLt (worldMeasure wNext) x = true := by
                rw [← hMeas]; exact hLtOrig
              have hFMid : F.holds vMid rMid :=
                vsep_drop_left (vMinStep wNext.stepCount) F vMid rMid hPost1
              have hPreMid : (vsep vemp F).holds vMid rMid :=
                vsep_vemp_intro vMid F rMid hFMid
              have hCanNext : isCanonicalCnf (worldMeasure wNext) = true :=
                worldMeasure_canonical wNext
              cases ih (worldMeasure wNext) hCanNext hLtX hCanNext
                  vMid rMid wNext rfl hPreMid hM1 with
              | intro wDrained hD =>
                cases hD with
                | intro rOut hrD =>
                  cases hrD with
                  | intro vOut hvD =>
                    exact ⟨wDrained, rOut, vOut,
                      WavefrontConverges.step wCur wNext wDrained hNe hStepEv
                        hLtOrig hvD.1,
                      viewLe_trans vCur vMid vOut hVLe1 hvD.2.1,
                      Eq.trans hvD.2.2.1 hPc1,
                      hvD.2.2.2.1,
                      hvD.2.2.2.2⟩
  exact hInd (worldMeasure wIn) (worldMeasure_canonical wIn) vIn rIn wIn rfl
    hPre hM

/-- Composes all five wavefront lifecycle stages across a single `(View, ResTrie
ResElem, WavefrontWorld)` chain preserving `WorldMatches` and spatial frame `F`:
(1) `.checkoutLoan`, (2) `.submitTaskBurst` consuming `ordDebtProp`, (3)
`WavefrontConverges` drain, (4) `.activeMut` reclamation with accumulated `u32`
delta, and (5) `.pureLiftSafe` direct mutation. -/
theorem vsepWpOrdRel_fiveStage_chained_lifecycle
    (pol : SpawnPolicy) (hPol : PolicyAdmissible pol)
    (lid : Pos4) (subL : ByteSubLens)
    (vInit scopeId rank remYields writeDelta pureDelta : Nat)
    (ordSpent : CnfOrd)
    (hCanSpent : isCanonicalCnf ordSpent = true)
    (hBudget : cnfLt (burstTaskDelta rank remYields) ordSpent = true)
    (v0 : View) (F : VProp) (r0 : ResTrie ResElem) (w0 : WavefrontWorld)
    (hChkG : CheckoutLoanGuard lid subL vInit w0)
    (hPre0 : (vsep (ordDebtProp ordSpent) F).holds v0 r0)
    (hM0 : WorldMatches v0 r0 w0) :
    let vDrained := wrapU32 (vInit +
      taskLeafMult pol rank remYields * writeDelta)
    let vFinal := wrapU32 (vDrained + pureDelta)
    ∃ (w1 w2 w3 w4 : WavefrontWorld) (r1 r2 r3 r4 : ResTrie ResElem) (v1 v2 v3
      v4 : View),
      evalHybridCmd (.checkoutLoan lid scopeId) w0 = .returned w1 ∧
      WorldMatches v1 r1 w1 ∧
      OrdRelStep .preserve w0 w1 ∧
      evalHybridCmd (.submitTaskBurst rank remYields lid scopeId writeDelta) w1
        = .returned w2 ∧
      WorldMatches v2 r2 w2 ∧
      OrdRelStep (.amortized ordSpent) w1 w2 ∧
      WavefrontConverges pol w2 w3 ∧
      WorldMatches v3 r3 w3 ∧
      ActivePureLoanAt lid subL vDrained w3 ∧
      byteSubLensGet subL w3.mem = some (wfEncodeU32BeSlice vDrained) ∧
      evalHybridCmd (.pureLiftSafe lid pureDelta) w3 = .returned w4 ∧
      WorldMatches v4 r4 w4 ∧
      OrdRelStep .preserve w3 w4 ∧
      ViewLe v0 v4 ∧
      extractPoolCap r4 = extractPoolCap r0 ∧
      (vsep (vMinStep w3.stepCount) F).holds v4 r4 ∧
      byteSubLensGet subL w4.mem = some (wfEncodeU32BeSlice vFinal) ∧
      (∀ otherL : ByteSubLens,
        byteLensDisjoint subL otherL = true →
        byteSubLensGet otherL w4.mem = byteSubLensGet otherL w3.mem) := by
  intro vDrained vFinal
  cases hChkG.1 with
  | intro e0 he0 =>
    have hNoTasks0 := hChkG.2
    have hNoF0 : anyTaskHasLoan lid w0.fifoQueue = false :=
      trueOfBnotTrue (bandLeft hNoTasks0)
    have hNoS0 : anyTaskHasLoan lid w0.stealDeque = false :=
      trueOfBnotTrue (bandRight hNoTasks0)
    let wpChk := vsepWpOrdRel_frame (.checkoutLoan lid scopeId) .preserve
      (CheckoutLoanGuard lid subL vInit) vemp (ordDebtProp ordSpent)
      (fun _ => checkedOutLoanProp lid scopeId vInit)
      (vsepWpOrdRel_checkoutLoan lid subL vInit scopeId)
    have hPreChk : (vsep (vsep vemp (ordDebtProp ordSpent)) F).holds v0 r0 :=
      (vsep_assoc_rl vemp (ordDebtProp ordSpent) F).imp v0 r0
        (vsep_vemp_intro v0 (vsep (ordDebtProp ordSpent) F) r0 hPre0)
    cases wpChk.run v0 F r0 w0 hChkG hPreChk hM0 with
    | intro w1 hw1Ex =>
      cases hw1Ex with
      | intro r1 hr1Ex =>
        cases hr1Ex with
        | intro v1 hv1 =>
          have hEv1 := hv1.1
          have hV01 := hv1.2.1
          have hPc01 := hv1.2.2.1
          have hPost1 := hv1.2.2.2.1
          have hM1 := hv1.2.2.2.2.1
          have hOrd1 := hv1.2.2.2.2.2
          have hEv1Unf := hEv1
          dsimp only [evalHybridCmd, execCheckoutLoan] at hEv1Unf
          rw [hNoTasks0, he0.1] at hEv1Unf
          dsimp only at hEv1Unf
          rw [he0.2.1] at hEv1Unf
          injection hEv1Unf with hw1Eq
          have hFind1 : wfFindLoan lid w1.loans =
            some ⟨e0.id, .spatialCheckedOut scopeId, e0.lens, e0.val⟩ := by
            rw [← hw1Eq]
            exact wfFindLoan_wfSetLoanEntryAt_same w0.loans lid
              (.spatialCheckedOut scopeId) e0.val e0 he0.1
          have hPre2 : (vsep (vsep (ordDebtProp ordSpent) (checkedOutLoanProp
            lid scopeId vInit)) F).holds v1 r1 := by
            cases hPost1 with
            | intro ra hra =>
              cases hra with
              | intro rb hcab =>
                exact ⟨ra, rb, hcab.1,
                  (vsep_comm (checkedOutLoanProp lid scopeId vInit)
                    (ordDebtProp ordSpent)).imp v1 ra hcab.2.1,
                  hcab.2.2⟩
          let wpBurst := (vsepWpOrdRel_submitTaskBurst_amortized_growth
            rank remYields lid scopeId writeDelta vInit ordSpent hCanSpent
              hBudget).1
          cases wpBurst.run v1 F r1 w1 True.intro hPre2 hM1 with
          | intro w2 hw2Ex =>
            cases hw2Ex with
            | intro r2 hr2Ex =>
              cases hr2Ex with
              | intro v2 hv2 =>
                have hEv2 := hv2.1
                have hV12 := hv2.2.1
                have hPc12 := hv2.2.2.1
                have hPost2 := hv2.2.2.2.1
                have hM2 := hv2.2.2.2.2.1
                have hOrd2 := hv2.2.2.2.2.2
                have hEv2Unf := hEv2
                dsimp only [evalHybridCmd, execSubmitTaskBurst] at hEv2Unf
                rw [hFind1] at hEv2Unf
                dsimp only [loanPhaseMatchesScope] at hEv2Unf
                rw [natBeq_refl scopeId] at hEv2Unf
                injection hEv2Unf with hw2Eq
                have hFind2 : wfFindLoan lid w2.loans =
                  some ⟨e0.id, .spatialCheckedOut scopeId, e0.lens, e0.val⟩ :=
                  by
                  rw [← hw2Eq]; exact hFind1
                have hQueued2 : (anyTaskHasLoan lid w2.fifoQueue ||
                  anyTaskHasLoan lid w2.stealDeque) = true := by
                  rw [← hw2Eq]
                  dsimp only [anyTaskHasLoan, List.foldr]
                  rw [pos4_beq_refl lid]
                  rfl
                have hDeltaSum2 : worldLoanDeltaSum pol lid w2 =
                  taskLeafMult pol rank remYields * writeDelta := by
                  dsimp only [worldLoanDeltaSum]
                  rw [← hw2Eq]
                  change (taskLoanDelta pol lid (WorkerTask.mk w1.nextTaskId
                    rank remYields lid scopeId writeDelta) +
                    queueLoanDeltaSum pol lid w1.fifoQueue) +
                      queueLoanDeltaSum pol lid w1.stealDeque = _
                  dsimp only [taskLoanDelta]
                  rw [pos4_beq_refl lid, ← hw1Eq]
                  dsimp only
                  rw [queueLoanDeltaSum_zero_of_not_hasLoan pol lid
                    w0.fifoQueue hNoF0,
                    queueLoanDeltaSum_zero_of_not_hasLoan pol lid w0.stealDeque
                      hNoS0]
                  rfl
                cases vsepWpOrdRel_wavefrontDrain pol hPol v2 F r2 w2 hPost2
                  hM2 with
                | intro w3 hw3Ex =>
                  cases hw3Ex with
                  | intro r3 hr3Ex =>
                    cases hr3Ex with
                    | intro v3 hv3 =>
                      have hConv := hv3.1
                      have hV23 := hv3.2.1
                      have hPc23 := hv3.2.2.1
                      have hPost3 := hv3.2.2.2.1
                      have hM3 := hv3.2.2.2.2
                      cases universal_post_drain_activeMut_reclaim pol hPol w2
                        w3
                          hM2.loansMemOk hM2.queueLoansOk hConv lid
                            hQueued2 with
                      | intro e2 he2 =>
                        rw [hFind2] at he2
                        injection he2.1 with hSameE2
                        rw [← hSameE2] at he2
                        dsimp only at he2
                        rw [hDeltaSum2, he0.2.2.1, he0.2.2.2] at he2
                        have hAct3 : ActivePureLoanAt lid subL vDrained w3 :=
                          he2.2.2.1
                        have hGet3 : byteSubLensGet subL w3.mem =
                          some (wfEncodeU32BeSlice vDrained) := he2.2.2.2
                        let F3 := vsep (vMinStep w3.stepCount) F
                        let wpPurePair :=
                          vsepWpOrdRel_pure_fastpath lid subL vDrained pureDelta
                        have hPre4 : (vsep vemp F3).holds v3 r3 :=
                          vsep_vemp_intro v3 F3 r3 hPost3
                        cases wpPurePair.1.run v3 F3 r3 w3 hAct3 hPre4 hM3 with
                        | intro w4 hw4Ex =>
                          cases hw4Ex with
                          | intro r4 hr4Ex =>
                            cases hr4Ex with
                            | intro v4 hv4 =>
                              have hEv4 := hv4.1
                              have hV34 := hv4.2.1
                              have hPc34 := hv4.2.2.1
                              have hPost4 : F3.holds v4 r4 :=
                                vsep_vemp_elim v4 F3 r4 hv4.2.2.2.1
                              have hM4 := hv4.2.2.2.2.1
                              have hOrd4 := hv4.2.2.2.2.2
                              cases wpPurePair.2 v3 F3 r3 w3 hAct3 hPre4
                                hM3 with
                              | intro w4' hw4' =>
                                have hSameW4 : w4' = w4 := by
                                  rw [hEv4] at hw4'
                                  injection hw4'.1 with hEqW4
                                  exact hEqW4.symm
                                rw [hSameW4] at hw4'
                                have hV04 : ViewLe v0 v4 :=
                                  viewLe_trans v0 v3 v4
                                    (viewLe_trans v0 v2 v3 (viewLe_trans v0 v1
                                      v2 hV01 hV12) hV23)
                                    hV34
                                have hPc04 : extractPoolCap r4 =
                                  extractPoolCap r0 :=
                                  Eq.trans hPc34 (Eq.trans hPc23 (Eq.trans
                                    hPc12 hPc01))
                                exact ⟨w1, w2, w3, w4, r1, r2, r3, r4, v1, v2,
                                  v3, v4,
                                  hEv1, hM1, hOrd1,
                                  hEv2, hM2, hOrd2,
                                  hConv, hM3, hAct3, hGet3,
                                  hEv4, hM4, hOrd4,
                                  hV04, hPc04, hPost4,
                                  hw4'.2.2.2.2.2.1, hw4'.2.2.2.2.2.2⟩

end Anneal.WavefrontReclaim

end
