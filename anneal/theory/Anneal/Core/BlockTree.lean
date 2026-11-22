-- Copyright 2026 The Fuchsia Authors
--
-- Licensed under a BSD-style license <LICENSE-BSD>, Apache License, Version 2.0
-- <LICENSE-APACHE or https://www.apache.org/licenses/LICENSE-2.0>, or the MIT
-- license <LICENSE-MIT or https://opensource.org/licenses/MIT>, at your option.
-- This file may not be copied, modified, or distributed except according to
-- those terms.

prelude
import Init.Core
import Init.NotationExtra
import Init.Data.Nat.Basic
import Init.Data.Nat.Div.Basic
import Init.Data.List.Basic
import Init.Control.Except
import Trusted
import Trusted.MirAst
import Trusted.MirModel
import Trusted.MirSemantics
import Anneal.MirWp
import Anneal.MirTotal.Ops
import Anneal.MirTotal.StepCore

namespace Anneal.Core

open Trusted.MirAst Trusted.MirSemantics Anneal.MirTotal

/-!
# Logarithmic Radix-2 Basic-Block Trees (`Core.BlockTree`)

Provides a total, LCNF-computable (`0` `noncomputable`, `0` `._unsafe_rec`)
radix-2 binary trie (`PTree α` and `BlockTree α`) supporting `O(log N)` trie
lookup and single-pass functional update (`ptreeModifyAt`), `O(N log N)`
direct list splitting (`ptreeFromListAt`) with `O(log N)` depth computation
(`compLog2Depth`), unconditional equivalence to `Trusted.MirSemantics.getElem?`
across both in-bounds and out-of-bounds indices, and a `BlockTree`-indexed
single-body MIR step evaluator (`evalMirStepBlockTreeBy`).
-/

/-! ## Constructive Binary Arithmetic Helpers -/

private theorem boolFalseNeTrue (h : false = true) : False :=
  Bool.noConfusion h

private theorem ite_bool_true {α : Type} {b : Bool} {t e : α} (hb : b = true) :
    (if b then t else e) = t := by
  subst hb
  rfl

private theorem ite_bool_false {α : Type} {b : Bool} {t e : α}
    (hb : b = false) :
    (if b then t else e) = e := by
  subst hb
  rfl

/-- Computable `2^n` via `@Nat.rec` (`0` `noncomputable`). -/
def pow2 (n : Nat) : Nat :=
  @Nat.rec (fun _ => Nat) 1 (fun _ ih => 2 * ih) n

/-- Base equation `pow2 0 = 1`. -/
theorem pow2_zero : pow2 0 = 1 := rfl

/-- Step equation `pow2 (n + 1) = 2 * pow2 n`. -/
theorem pow2_succ (n : Nat) : pow2 (n + 1) = 2 * pow2 n := rfl

/-- Strict positivity `0 < pow2 n`. -/
theorem pow2_pos (n : Nat) : 0 < pow2 n := by
  induction n with
  | zero => exact Nat.zero_lt_one
  | succ _ ih =>
    rw [pow2_succ]
    exact Nat.mul_pos (Nat.succ_pos 1) ih

/-- Exponential dominance `n < pow2 n`. -/
theorem id_lt_pow2 (n : Nat) : n < pow2 n := by
  induction n with
  | zero => exact Nat.zero_lt_one
  | succ k ih =>
    rw [pow2_succ]
    have h1 : k + 1 ≤ pow2 k := ih
    have h2 : pow2 k + pow2 k = 2 * pow2 k := by
      have hm : (1 + 1) * pow2 k = 1 * pow2 k + 1 * pow2 k :=
        Nat.add_mul 1 1 (pow2 k)
      rw [Nat.one_mul] at hm
      exact hm.symm
    rw [← h2]
    have ha : (k + 1) + 0 < (k + 1) + pow2 k :=
      Nat.add_lt_add_left (pow2_pos k) (k + 1)
    rw [Nat.add_zero] at ha
    exact Nat.lt_of_lt_of_le ha (Nat.add_le_add_right h1 (pow2 k))

/-- Parity decomposition of `n` into `2 * (n / 2)` or `2 * (n / 2) + 1`. -/
theorem nat_div2_decomp (n : Nat) :
    if Nat.beq (Nat.mod n 2) 0 = true then
      2 * Nat.div n 2 = n
    else
      2 * Nat.div n 2 + 1 = n := by
  have hlt : Nat.mod n 2 < 2 := Nat.mod_lt n (Nat.succ_pos 1)
  have hdiv : 2 * Nat.div n 2 + Nat.mod n 2 = n := Nat.div_add_mod n 2
  cases hm : Nat.mod n 2 with
  | zero =>
    rw [hm] at hdiv
    rw [Nat.add_zero] at hdiv
    exact hdiv
  | succ r =>
    rw [hm] at hlt
    cases r with
    | zero =>
      rw [hm] at hdiv
      exact hdiv
    | succ r2 =>
      have hbad : ¬ (r2 + 2 < 2) := Nat.not_lt_of_ge (Nat.le_add_left 2 r2)
      exact False.elim (hbad hlt)

private theorem getElem?_eq_none_of_le {α : Type} :
    ∀ (xs : List α) (idx : Nat),
      xs.length ≤ idx → Trusted.MirSemantics.getElem? xs idx = none
  | [], _, _ => rfl
  | _ :: _, 0, h => False.elim (Nat.not_succ_le_zero _ h)
  | _ :: tl, k + 1, h =>
    getElem?_eq_none_of_le tl k (Nat.le_of_succ_le_succ h)

private theorem setElem?_lt_and_length {α : Type} :
    ∀ {xs xs' : List α} {idx : Nat} {val : α},
      Trusted.MirSemantics.setElem? xs idx val = some xs' →
      idx < xs.length ∧ xs'.length = xs.length
  | [], _, _, _, hSet => by cases hSet
  | _ :: _, _, 0, _, hSet => by
    injection hSet with hEq
    subst hEq
    exact ⟨Nat.succ_pos _, rfl⟩
  | _ :: tl, _, k + 1, val, hSet => by
    dsimp only [Trusted.MirSemantics.setElem?] at hSet
    cases hSub : Trusted.MirSemantics.setElem? tl k val with
    | none => rw [hSub] at hSet; cases hSet
    | some tl' =>
      rw [hSub] at hSet
      injection hSet with hEq
      subst hEq
      have ih := @setElem?_lt_and_length α tl tl' k val hSub
      exact ⟨Nat.succ_lt_succ ih.1, congrArg Nat.succ ih.2⟩

private theorem bt_getElem?_setElem?_same {α : Type} :
    ∀ {xs xs' : List α} {idx : Nat} {val : α},
      Trusted.MirSemantics.setElem? xs idx val = some xs' →
      Trusted.MirSemantics.getElem? xs' idx = some val
  | [], _, _, _, hSet => by cases hSet
  | _ :: _, _, 0, _, hSet => by
    injection hSet with hEq
    subst hEq
    rfl
  | _ :: tl, _, k + 1, val, hSet => by
    dsimp only [Trusted.MirSemantics.setElem?] at hSet
    cases hSub : Trusted.MirSemantics.setElem? tl k val with
    | none => rw [hSub] at hSet; cases hSet
    | some tl' =>
      rw [hSub] at hSet
      injection hSet with hEq
      subst hEq
      exact @bt_getElem?_setElem?_same α tl tl' k val hSub

private theorem bt_getElem?_setElem?_ne {α : Type} :
    ∀ {xs xs' : List α} {idx j : Nat} {val : α},
      j ≠ idx →
      Trusted.MirSemantics.setElem? xs idx val = some xs' →
      Trusted.MirSemantics.getElem? xs' j =
        Trusted.MirSemantics.getElem? xs j
  | [], _, _, _, _, _, hSet => by cases hSet
  | _ :: _, _, 0, 0, _, hNe, _ => False.elim (hNe rfl)
  | _ :: _, _, 0, _ + 1, _, _, hSet => by
    injection hSet with hEq
    subst hEq
    rfl
  | _ :: tl, _, k + 1, 0, val, _, hSet => by
    dsimp only [Trusted.MirSemantics.setElem?] at hSet
    cases hSub : Trusted.MirSemantics.setElem? tl k val with
    | none => rw [hSub] at hSet; cases hSet
    | some tl' =>
      rw [hSub] at hSet
      injection hSet with hEq
      subst hEq
      rfl
  | _ :: tl, _, k + 1, m + 1, val, hNe, hSet => by
    dsimp only [Trusted.MirSemantics.setElem?] at hSet
    cases hSub : Trusted.MirSemantics.setElem? tl k val with
    | none => rw [hSub] at hSet; cases hSet
    | some tl' =>
      rw [hSub] at hSet
      injection hSet with hEq
      subst hEq
      exact @bt_getElem?_setElem?_ne α tl tl' k m val
        (fun he => hNe (congrArg Nat.succ he)) hSub

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

private theorem natBeq_refl (a : Nat) : Nat.beq a a = true := by
  induction a with
  | zero => rfl
  | succ _ ih => exact ih

private theorem natBeq_false_of_ne {a b : Nat} (h : a ≠ b) :
    Nat.beq a b = false := by
  cases hb : Nat.beq a b with
  | false => rfl
  | true => exact False.elim (h (natEq_of_beq a b hb))

/-! ## Radix-2 Binary Trie (`PTree`) -/

/-- Radix-2 binary trie storing optional elements at leaves of a fixed depth. -/
inductive PTree (α : Type) : Type where
  | empty : PTree α
  | leaf : Option α → PTree α
  | node : PTree α → PTree α → PTree α

/-- Top-down strided radix-2 tabulation helper (`0` `noncomputable`). -/
def ptreeTabulateAt {α : Type} (depth : Nat) :
    Nat → Nat → (Nat → Option α) → PTree α :=
  @Nat.rec (fun _ => Nat → Nat → (Nat → Option α) → PTree α)
    (fun offset _ f => PTree.leaf (f offset))
    (fun _ ih offset step f =>
      PTree.node (ih offset (2 * step) f) (ih (offset + step) (2 * step) f))
    depth

/-- Tabulates `f 0 .. f (2^depth - 1)` into a balanced radix-2 `PTree α`. -/
def ptreeTabulate {α : Type} (f : Nat → Option α) (depth : Nat) : PTree α :=
  ptreeTabulateAt depth 0 1 f

/-- Looks up `idx` in a depth-`depth` `PTree α` in `O(depth)` bit steps. -/
def ptreeGetAt {α : Type} (depth : Nat) : PTree α → Nat → Option α :=
  @Nat.rec (fun _ => PTree α → Nat → Option α)
    (fun t idx =>
      match t with
      | .empty => none
      | .leaf v => if Nat.beq idx 0 then v else none
      | .node _ _ => none)
    (fun _ ih t idx =>
      match t with
      | .empty => none
      | .leaf _ => none
      | .node l r =>
        if Nat.beq (Nat.mod idx 2) 0 then
          ih l (Nat.div idx 2)
        else
          ih r (Nat.div idx 2))
    depth

/-- Single-pass `O(depth)` functional update at `idx` in `PTree α`, allocating
missing interior spines on demand. -/
def ptreeModifyAt {α : Type} (depth : Nat) :
    PTree α → Nat → Option α → PTree α :=
  @Nat.rec (fun _ => PTree α → Nat → Option α → PTree α)
    (fun t idx v =>
      if Nat.beq idx 0 then .leaf v else t)
    (fun _ ih t idx v =>
      let (l, r) : PTree α × PTree α :=
        match t with
        | .node l0 r0 => (l0, r0)
        | .empty | .leaf _ => (.empty, .empty)
      if Nat.beq (Nat.mod idx 2) 0 then
        .node (ih l (Nat.div idx 2) v) r
      else
        .node l (ih r (Nat.div idx 2) v))
    depth

/-- In-bounds lookup on `ptreeTabulateAt` (`idx < pow2 depth`). -/
theorem ptreeGetAt_ptreeTabulateAt_in {α : Type}
    (depth idx offset step : Nat) (f : Nat → Option α)
    (hidx : idx < pow2 depth) :
    ptreeGetAt depth (ptreeTabulateAt depth offset step f) idx =
      f (offset + step * idx) := by
  revert idx offset step
  induction depth with
  | zero =>
    intro idx offset step hidx
    rw [pow2_zero] at hidx
    have h0 : idx = 0 := Nat.eq_zero_of_le_zero (Nat.le_of_lt_succ hidx)
    rw [h0, Nat.mul_zero, Nat.add_zero]
    rfl
  | succ d ih =>
    intro idx offset step hidx
    change (if Nat.beq (Nat.mod idx 2) 0 then
        ptreeGetAt d (ptreeTabulateAt d offset (2 * step) f) (Nat.div idx 2)
      else
        ptreeGetAt d (ptreeTabulateAt d (offset + step) (2 * step) f)
          (Nat.div idx 2)) =
      f (offset + step * idx)
    rw [pow2_succ, Nat.mul_comm 2 (pow2 d)] at hidx
    have hhalf : Nat.div idx 2 < pow2 d :=
      (Nat.div_lt_iff_lt_mul (Nat.succ_pos 1)).mpr hidx
    have hde := nat_div2_decomp idx
    cases hbeq : Nat.beq (Nat.mod idx 2) 0 with
    | true =>
      rw [hbeq] at hde
      change 2 * Nat.div idx 2 = idx at hde
      rw [ite_bool_true rfl, ih (Nat.div idx 2) offset (2 * step) hhalf]
      have hmul : (2 * step) * Nat.div idx 2 = step * idx := by
        rw [Nat.mul_comm 2 step, Nat.mul_assoc step 2 (Nat.div idx 2), hde]
      rw [hmul]
    | false =>
      rw [hbeq] at hde
      change 2 * Nat.div idx 2 + 1 = idx at hde
      rw [ite_bool_false rfl,
        ih (Nat.div idx 2) (offset + step) (2 * step) hhalf]
      have harith :
          (offset + step) + (2 * step) * Nat.div idx 2 =
            offset + step * idx := by
        rw [Nat.mul_comm 2 step, Nat.mul_assoc step 2 (Nat.div idx 2),
          Nat.add_assoc offset step (step * (2 * Nat.div idx 2))]
        have hs1 :
            step + step * (2 * Nat.div idx 2) =
              step * (2 * Nat.div idx 2 + 1) := by
          rw [Nat.mul_add, Nat.mul_one, Nat.add_comm]
        rw [hs1, hde]
      rw [harith]

/-- Out-of-bounds lookup on `ptreeTabulateAt` (`pow2 depth ≤ idx`). -/
theorem ptreeGetAt_ptreeTabulateAt_oob {α : Type}
    (depth idx offset step : Nat) (f : Nat → Option α)
    (hoob : pow2 depth ≤ idx) :
    ptreeGetAt depth (ptreeTabulateAt depth offset step f) idx = none := by
  revert idx offset step
  induction depth with
  | zero =>
    intro idx _ _ hoob
    rw [pow2_zero] at hoob
    cases idx with
    | zero => exact False.elim (Nat.not_lt_of_ge hoob Nat.zero_lt_one)
    | succ _ => rfl
  | succ d ih =>
    intro idx offset step hoob
    change (if Nat.beq (Nat.mod idx 2) 0 then
        ptreeGetAt d (ptreeTabulateAt d offset (2 * step) f) (Nat.div idx 2)
      else
        ptreeGetAt d (ptreeTabulateAt d (offset + step) (2 * step) f)
          (Nat.div idx 2)) = none
    rw [pow2_succ, Nat.mul_comm 2 (pow2 d)] at hoob
    have hhalf : pow2 d ≤ Nat.div idx 2 :=
      (Nat.le_div_iff_mul_le (Nat.succ_pos 1)).mpr hoob
    cases Nat.beq (Nat.mod idx 2) 0 with
    | true =>
      rw [ite_bool_true rfl]
      exact ih (Nat.div idx 2) offset (2 * step) hhalf
    | false =>
      rw [ite_bool_false rfl]
      exact ih (Nat.div idx 2) (offset + step) (2 * step) hhalf

private theorem ptreeGetAt_empty {α : Type} (depth idx : Nat) :
    ptreeGetAt depth (.empty : PTree α) idx = none := by
  cases depth <;> rfl

/-- Same-index read-after-modify law for `ptreeModifyAt` (`idx < pow2 depth`).
-/
theorem ptreeGetAt_ptreeModifyAt_same {α : Type}
    (depth : Nat) (t : PTree α) (idx : Nat) (v : Option α)
    (hidx : idx < pow2 depth) :
    ptreeGetAt depth (ptreeModifyAt depth t idx v) idx = v := by
  revert t idx
  induction depth with
  | zero =>
    intro t idx hidx
    rw [pow2_zero] at hidx
    have h0 : idx = 0 := Nat.eq_zero_of_le_zero (Nat.le_of_lt_succ hidx)
    subst h0
    rfl
  | succ d ih =>
    intro t idx hidx
    rw [pow2_succ, Nat.mul_comm 2 (pow2 d)] at hidx
    have hhalf : Nat.div idx 2 < pow2 d :=
      (Nat.div_lt_iff_lt_mul (Nat.succ_pos 1)).mpr hidx
    cases t with
    | empty | leaf _ =>
      change ptreeGetAt (d + 1)
          (if Nat.beq (Nat.mod idx 2) 0 then
             PTree.node (ptreeModifyAt d .empty (Nat.div idx 2) v) .empty
           else
             PTree.node .empty (ptreeModifyAt d .empty (Nat.div idx 2) v))
          idx = v
      cases hpar : Nat.beq (Nat.mod idx 2) 0 with
      | true =>
        rw [ite_bool_true rfl]
        change (if Nat.beq (Nat.mod idx 2) 0 then
            ptreeGetAt d (ptreeModifyAt d .empty (Nat.div idx 2) v) (Nat.div idx 2)
          else ptreeGetAt d .empty (Nat.div idx 2)) = v
        rw [hpar, ite_bool_true rfl]
        exact ih .empty (Nat.div idx 2) hhalf
      | false =>
        rw [ite_bool_false rfl]
        change (if Nat.beq (Nat.mod idx 2) 0 then
            ptreeGetAt d .empty (Nat.div idx 2)
          else
            ptreeGetAt d (ptreeModifyAt d .empty (Nat.div idx 2) v)
              (Nat.div idx 2)) = v
        rw [hpar, ite_bool_false rfl]
        exact ih .empty (Nat.div idx 2) hhalf
    | node l r =>
      change ptreeGetAt (d + 1)
          (if Nat.beq (Nat.mod idx 2) 0 then
             PTree.node (ptreeModifyAt d l (Nat.div idx 2) v) r
           else
             PTree.node l (ptreeModifyAt d r (Nat.div idx 2) v))
          idx = v
      cases hpar : Nat.beq (Nat.mod idx 2) 0 with
      | true =>
        rw [ite_bool_true rfl]
        change (if Nat.beq (Nat.mod idx 2) 0 then
            ptreeGetAt d (ptreeModifyAt d l (Nat.div idx 2) v) (Nat.div idx 2)
          else ptreeGetAt d r (Nat.div idx 2)) = v
        rw [hpar, ite_bool_true rfl]
        exact ih l (Nat.div idx 2) hhalf
      | false =>
        rw [ite_bool_false rfl]
        change (if Nat.beq (Nat.mod idx 2) 0 then
            ptreeGetAt d l (Nat.div idx 2)
          else
            ptreeGetAt d (ptreeModifyAt d r (Nat.div idx 2) v)
              (Nat.div idx 2)) = v
        rw [hpar, ite_bool_false rfl]
        exact ih r (Nat.div idx 2) hhalf

/-- Frame law for `ptreeModifyAt` at any distinct index `j ≠ idx`. -/
theorem ptreeGetAt_ptreeModifyAt_ne {α : Type}
    (depth : Nat) (t : PTree α) (idx j : Nat) (v : Option α)
    (hNe : j ≠ idx) :
    ptreeGetAt depth (ptreeModifyAt depth t idx v) j =
      ptreeGetAt depth t j := by
  revert t idx j
  induction depth with
  | zero =>
    intro t idx j hNe
    change ptreeGetAt 0 (if Nat.beq idx 0 then PTree.leaf v else t) j =
      ptreeGetAt 0 t j
    cases hIdx : Nat.beq idx 0 with
    | false => rw [ite_bool_false rfl]
    | true =>
      have h0 : idx = 0 := natEq_of_beq idx 0 hIdx
      subst h0
      have hj0 : Nat.beq j 0 = false := natBeq_false_of_ne hNe
      rw [ite_bool_true rfl]
      cases t with
      | empty =>
        change (if Nat.beq j 0 then v else none) = none
        rw [hj0, ite_bool_false rfl]
      | leaf w =>
        change (if Nat.beq j 0 then v else none) =
          (if Nat.beq j 0 then w else none)
        rw [hj0, ite_bool_false rfl, ite_bool_false rfl]
      | node _ _ =>
        change (if Nat.beq j 0 then v else none) = none
        rw [hj0, ite_bool_false rfl]
  | succ d ih =>
    intro t idx j hNe
    have hDivNe :
        Nat.beq (Nat.mod j 2) 0 = Nat.beq (Nat.mod idx 2) 0 →
        Nat.div j 2 ≠ Nat.div idx 2 := by
      intro hParEq hDivEq
      have hdj := nat_div2_decomp j
      have hdi := nat_div2_decomp idx
      cases hp : Nat.beq (Nat.mod idx 2) 0 with
      | true =>
        rw [hp] at hParEq hdi
        rw [hParEq] at hdj
        change 2 * Nat.div j 2 = j at hdj
        change 2 * Nat.div idx 2 = idx at hdi
        rw [hDivEq, hdi] at hdj
        exact hNe hdj.symm
      | false =>
        rw [hp] at hParEq hdi
        rw [hParEq] at hdj
        change 2 * Nat.div j 2 + 1 = j at hdj
        change 2 * Nat.div idx 2 + 1 = idx at hdi
        rw [hDivEq, hdi] at hdj
        exact hNe hdj.symm
    cases t with
    | empty | leaf _ =>
      change ptreeGetAt (d + 1)
          (if Nat.beq (Nat.mod idx 2) 0 then
             PTree.node (ptreeModifyAt d .empty (Nat.div idx 2) v) .empty
           else
             PTree.node .empty (ptreeModifyAt d .empty (Nat.div idx 2) v))
          j = none
      cases hpi : Nat.beq (Nat.mod idx 2) 0 with
      | true =>
        rw [ite_bool_true rfl]
        change (if Nat.beq (Nat.mod j 2) 0 then
            ptreeGetAt d (ptreeModifyAt d .empty (Nat.div idx 2) v) (Nat.div j 2)
          else ptreeGetAt d .empty (Nat.div j 2)) = none
        cases hpj : Nat.beq (Nat.mod j 2) 0 with
        | true =>
          rw [ite_bool_true rfl,
            ih .empty (Nat.div idx 2) (Nat.div j 2)
              (hDivNe (hpj.trans hpi.symm))]
          exact ptreeGetAt_empty d (Nat.div j 2)
        | false =>
          rw [ite_bool_false rfl]
          exact ptreeGetAt_empty d (Nat.div j 2)
      | false =>
        rw [ite_bool_false rfl]
        change (if Nat.beq (Nat.mod j 2) 0 then
            ptreeGetAt d .empty (Nat.div j 2)
          else
            ptreeGetAt d (ptreeModifyAt d .empty (Nat.div idx 2) v)
              (Nat.div j 2)) = none
        cases hpj : Nat.beq (Nat.mod j 2) 0 with
        | true =>
          rw [ite_bool_true rfl]
          exact ptreeGetAt_empty d (Nat.div j 2)
        | false =>
          rw [ite_bool_false rfl,
            ih .empty (Nat.div idx 2) (Nat.div j 2)
              (hDivNe (hpj.trans hpi.symm))]
          exact ptreeGetAt_empty d (Nat.div j 2)
    | node l r =>
      change ptreeGetAt (d + 1)
          (if Nat.beq (Nat.mod idx 2) 0 then
             PTree.node (ptreeModifyAt d l (Nat.div idx 2) v) r
           else
             PTree.node l (ptreeModifyAt d r (Nat.div idx 2) v))
          j =
        (if Nat.beq (Nat.mod j 2) 0 then
           ptreeGetAt d l (Nat.div j 2)
         else
           ptreeGetAt d r (Nat.div j 2))
      cases hpi : Nat.beq (Nat.mod idx 2) 0 with
      | true =>
        rw [ite_bool_true rfl]
        change (if Nat.beq (Nat.mod j 2) 0 then
            ptreeGetAt d (ptreeModifyAt d l (Nat.div idx 2) v) (Nat.div j 2)
          else ptreeGetAt d r (Nat.div j 2)) =
          (if Nat.beq (Nat.mod j 2) 0 then
            ptreeGetAt d l (Nat.div j 2)
          else ptreeGetAt d r (Nat.div j 2))
        cases hpj : Nat.beq (Nat.mod j 2) 0 with
        | true =>
          rw [ite_bool_true rfl, ite_bool_true rfl]
          exact ih l (Nat.div idx 2) (Nat.div j 2) (hDivNe (hpj.trans hpi.symm))
        | false =>
          rw [ite_bool_false rfl, ite_bool_false rfl]
      | false =>
        rw [ite_bool_false rfl]
        change (if Nat.beq (Nat.mod j 2) 0 then
            ptreeGetAt d l (Nat.div j 2)
          else
            ptreeGetAt d (ptreeModifyAt d r (Nat.div idx 2) v) (Nat.div j 2)) =
          (if Nat.beq (Nat.mod j 2) 0 then
            ptreeGetAt d l (Nat.div j 2)
          else ptreeGetAt d r (Nat.div j 2))
        cases hpj : Nat.beq (Nat.mod j 2) 0 with
        | true =>
          rw [ite_bool_true rfl, ite_bool_true rfl]
        | false =>
          rw [ite_bool_false rfl, ite_bool_false rfl]
          exact ih r (Nat.div idx 2) (Nat.div j 2) (hDivNe (hpj.trans hpi.symm))

/-! ## Logarithmic Depth Bound, Direct List Splitting, and `BlockTree` -/

/-- Accumulator-passing logarithmic ceiling loop via `@Nat.rec`, terminating
reduction as soon as `n ≤ cap` (`O(log n)` reduction depth). -/
def compLog2DepthGo (n : Nat) : Nat → Nat → Nat → Nat :=
  @Nat.rec (fun _ => Nat → Nat → Nat)
    (fun depth _ => depth)
    (fun _ ih depth cap =>
      if Nat.ble n cap then depth
      else ih (depth + 1) (2 * cap))

/-- Smallest radix-2 tree depth covering `n` elements (`compLog2Depth 26 = 5`,
`compLog2Depth 64 = 6`). -/
def compLog2Depth (n : Nat) : Nat := compLog2DepthGo n n 0 1

private theorem compLog2DepthGo_bound (n : Nat) :
    ∀ (fuel depth cap : Nat),
      cap = pow2 depth →
      n ≤ depth + fuel →
      n ≤ pow2 (compLog2DepthGo n fuel depth cap)
  | 0, depth, _, _, hSum => by
    rw [Nat.add_zero] at hSum
    exact Nat.le_trans hSum (Nat.le_of_lt (id_lt_pow2 depth))
  | k + 1, depth, cap, hCap, hSum => by
    change n ≤ pow2
      (if Nat.ble n cap then depth
       else compLog2DepthGo n k (depth + 1) (2 * cap))
    cases hble : Nat.ble n cap with
    | true =>
      rw [ite_bool_true rfl, ← hCap]
      exact Nat.le_of_ble_eq_true hble
    | false =>
      rw [ite_bool_false rfl]
      have hCap' : 2 * cap = pow2 (depth + 1) := by
        rw [pow2_succ, hCap]
      have hSum' : n ≤ (depth + 1) + k := by
        rw [Nat.succ_add, ← Nat.add_succ]
        exact hSum
      exact compLog2DepthGo_bound n k (depth + 1) (2 * cap) hCap' hSum'

/-- `n ≤ pow2 (compLog2Depth n)` holds for all `n : Nat`. -/
theorem le_pow2_compLog2Depth (n : Nat) : n ≤ pow2 (compLog2Depth n) := by
  have hSum : n ≤ 0 + n := by
    rw [Nat.zero_add]
    exact Nat.le_refl n
  exact compLog2DepthGo_bound n n 0 1 rfl hSum

/-- Splits `xs` in one pass into `(evens, odds)` (`evens[k] = xs[2*k]`,
`odds[k] = xs[2*k + 1]`). -/
def unzipEvenOdd {α : Type} (xs : List α) : List α × List α :=
  List.foldr (fun x eo => (x :: eo.2, eo.1)) ([], []) xs

private theorem getElem?_unzipEvenOdd {α : Type} :
    ∀ (xs : List α) (k : Nat),
      (Trusted.MirSemantics.getElem? (unzipEvenOdd xs).1 k =
         Trusted.MirSemantics.getElem? xs (2 * k)) ∧
      (Trusted.MirSemantics.getElem? (unzipEvenOdd xs).2 k =
         Trusted.MirSemantics.getElem? xs (2 * k + 1))
  | [], k => by
    cases k <;> exact ⟨rfl, rfl⟩
  | x :: xs, k => by
    refine ⟨?_, (getElem?_unzipEvenOdd xs k).1⟩
    cases k with
    | zero => rfl
    | succ k' =>
      have hMul : 2 * (k' + 1) = (2 * k' + 1) + 1 := by
        rw [Nat.mul_succ]
      rw [hMul]
      exact (getElem?_unzipEvenOdd xs k').2

private theorem length_unzipEvenOdd_bounds {α : Type} :
    ∀ (xs : List α),
      2 * (unzipEvenOdd xs).1.length ≤ xs.length + 1 ∧
      2 * (unzipEvenOdd xs).2.length ≤ xs.length
  | [] => ⟨Nat.zero_le 1, Nat.le_refl 0⟩
  | x :: xs => by
    have ih := length_unzipEvenOdd_bounds xs
    change 2 * ((unzipEvenOdd xs).2.length + 1) ≤ (xs.length + 1) + 1 ∧
      2 * (unzipEvenOdd xs).1.length ≤ xs.length + 1
    refine ⟨?_, ih.1⟩
    rw [Nat.mul_succ]
    exact Nat.add_le_add_right ih.2 2

/-- Builds a radix-2 `PTree α` of height `depth` directly from `xs` by
splitting even and odd indices at each level (`O(|xs| log |xs|)` total work,
pruning empty subtrees to `.empty` without per-leaf list rescans). -/
def ptreeFromListAt {α : Type} (depth : Nat) : List α → PTree α :=
  @Nat.rec (fun _ => List α → PTree α)
    (fun xs =>
      match xs with
      | [] => .empty
      | x :: _ => .leaf (some x))
    (fun _ ih xs =>
      match xs with
      | [] => .empty
      | _ :: _ =>
        let eo := unzipEvenOdd xs
        .node (ih eo.1) (ih eo.2))
    depth

/-- Lookup equivalence for `ptreeFromListAt` across all `idx : Nat` whenever
`xs.length ≤ pow2 depth`. -/
theorem ptreeGetAt_ptreeFromListAt {α : Type} :
    ∀ (depth : Nat) (xs : List α),
      xs.length ≤ pow2 depth →
      ∀ idx : Nat,
        ptreeGetAt depth (ptreeFromListAt depth xs) idx =
          Trusted.MirSemantics.getElem? xs idx
  | 0, [], _, idx => by
    cases idx <;> rfl
  | 0, [x], _, idx => by
    cases idx <;> rfl
  | 0, _ :: _ :: tl, hBound, _ => by
    rw [pow2_zero] at hBound
    exact False.elim
      (Nat.not_lt_of_ge hBound (Nat.succ_lt_succ (Nat.succ_pos tl.length)))
  | d + 1, [], _, idx => by
    change (none : Option α) = Trusted.MirSemantics.getElem? [] idx
    cases idx <;> rfl
  | d + 1, x :: tl, hBound, idx => by
    let xs := x :: tl
    have hLen := length_unzipEvenOdd_bounds xs
    rw [pow2_succ] at hBound
    have hSub2 : (unzipEvenOdd xs).2.length ≤ pow2 d := by
      have h2 : 2 * (unzipEvenOdd xs).2.length ≤ 2 * pow2 d :=
        Nat.le_trans hLen.2 hBound
      exact Nat.le_of_mul_le_mul_left h2 (Nat.succ_pos 1)
    have hSub1 : (unzipEvenOdd xs).1.length ≤ pow2 d := by
      cases Nat.lt_or_ge (pow2 d) (unzipEvenOdd xs).1.length with
      | inr hle => exact hle
      | inl hgt =>
        have hGe1 : pow2 d + 1 ≤ (unzipEvenOdd xs).1.length := hgt
        have hMulGe : 2 * (pow2 d + 1) ≤ 2 * (unzipEvenOdd xs).1.length :=
          Nat.mul_le_mul_left 2 hGe1
        rw [Nat.mul_succ] at hMulGe
        have hUpper : 2 * (unzipEvenOdd xs).1.length ≤ 2 * pow2 d + 1 :=
          Nat.le_trans hLen.1 (Nat.succ_le_succ hBound)
        have hContra : 2 * pow2 d + 2 ≤ 2 * pow2 d + 1 :=
          Nat.le_trans hMulGe hUpper
        exact False.elim
          (Nat.not_lt_of_ge hContra (Nat.lt_succ_self (2 * pow2 d + 1)))
    change
      (if Nat.beq (Nat.mod idx 2) 0 then
         ptreeGetAt d (ptreeFromListAt d (unzipEvenOdd xs).1) (Nat.div idx 2)
       else
         ptreeGetAt d (ptreeFromListAt d (unzipEvenOdd xs).2)
           (Nat.div idx 2)) =
      Trusted.MirSemantics.getElem? xs idx
    have hde := nat_div2_decomp idx
    cases hbeq : Nat.beq (Nat.mod idx 2) 0 with
    | true =>
      rw [hbeq] at hde
      change 2 * Nat.div idx 2 = idx at hde
      rw [ite_bool_true rfl,
        ptreeGetAt_ptreeFromListAt d (unzipEvenOdd xs).1 hSub1 (Nat.div idx 2),
        (getElem?_unzipEvenOdd xs (Nat.div idx 2)).1, hde]
    | false =>
      rw [hbeq] at hde
      change 2 * Nat.div idx 2 + 1 = idx at hde
      rw [ite_bool_false rfl,
        ptreeGetAt_ptreeFromListAt d (unzipEvenOdd xs).2 hSub2 (Nat.div idx 2),
        (getElem?_unzipEvenOdd xs (Nat.div idx 2)).2, hde]

/-- Pure-data logarithmic lookup table over elements of type `α` (`0` `Prop`
fields so `BlockTree` reduces freely in computational positions). -/
structure BlockTree (α : Type) where
  depth : Nat
  tree : PTree α

/-- Lazy right-fold list length (`O(k)` WHNF prefix inspection under `Nat.ble`,
avoiding `List.length`'s strict tail-recursive full-list scan during
elaboration). -/
def compListLength {α : Type} (xs : List α) : Nat :=
  List.foldr (fun _ k => Nat.succ k) 0 xs

/-- Exact agreement between `compListLength` and `List.length`. -/
theorem compListLength_eq {α : Type} :
    ∀ (xs : List α), compListLength xs = xs.length
  | [] => rfl
  | _ :: tl => congrArg Nat.succ (compListLength_eq tl)

/-- Tabulates `xs` into a `BlockTree α` at explicit depth `depth` via
single-pass even/odd list splitting (`ptreeFromListAt`). -/
def BlockTree.ofListAt {α : Type} (xs : List α) (depth : Nat) : BlockTree α :=
  { depth := depth, tree := ptreeFromListAt depth xs }

/-- Tabulates `xs` into a `BlockTree α` at depth
`compLog2Depth (compListLength xs)`. -/
def BlockTree.ofList {α : Type} (xs : List α) : BlockTree α :=
  BlockTree.ofListAt xs (compLog2Depth (compListLength xs))

/-- Looks up index `idx` in `bt` in `O(bt.depth)` trie steps. -/
def BlockTree.lookup {α : Type} (bt : BlockTree α) (idx : Nat) : Option α :=
  ptreeGetAt bt.depth bt.tree idx

/-- Functionally updates index `idx` in `bt` in `O(bt.depth)` trie steps. -/
def BlockTree.modify {α : Type} (bt : BlockTree α) (idx : Nat) (v : Option α) :
    BlockTree α :=
  { depth := bt.depth, tree := ptreeModifyAt bt.depth bt.tree idx v }

/-- Validity predicate tying a pure-data `BlockTree α` back to `xs`. -/
def ValidBlockTree {α : Type} (xs : List α) (bt : BlockTree α) : Prop :=
  xs.length ≤ pow2 bt.depth ∧
  ∀ idx : Nat, bt.lookup idx = Trusted.MirSemantics.getElem? xs idx

/-- `BlockTree.ofListAt xs depth` is valid whenever `xs.length ≤ pow2 depth`. -/
theorem valid_blockTree_ofListAt {α : Type} (xs : List α) (depth : Nat)
    (hBound : xs.length ≤ pow2 depth) :
    ValidBlockTree xs (BlockTree.ofListAt xs depth) :=
  ⟨hBound, ptreeGetAt_ptreeFromListAt depth xs hBound⟩

/-- `BlockTree.ofList xs` is unconditionally valid for every `xs : List α`. -/
theorem valid_blockTree_ofList {α : Type} (xs : List α) :
    ValidBlockTree xs (BlockTree.ofList xs) := by
  have hBound : xs.length ≤ pow2 (compLog2Depth (compListLength xs)) := by
    rw [compListLength_eq xs]
    exact le_pow2_compLog2Depth xs.length
  exact valid_blockTree_ofListAt xs (compLog2Depth (compListLength xs)) hBound

/-- Exact equivalence between `BlockTree.lookup` and
`Trusted.MirSemantics.getElem?` across both in-bounds and out-of-bounds indices.
-/
theorem BlockTree.lookup_eq_getElem? {α : Type} {xs : List α}
    {bt : BlockTree α} (hValid : ValidBlockTree xs bt) (idx : Nat) :
    bt.lookup idx = Trusted.MirSemantics.getElem? xs idx :=
  hValid.2 idx

/-- Exact equivalence between `BlockTree.lookup` and `compGetElem?`. -/
theorem BlockTree.lookup_eq_compGetElem? {α : Type} {xs : List α}
    {bt : BlockTree α} (hValid : ValidBlockTree xs bt) (idx : Nat) :
    bt.lookup idx = compGetElem? xs idx := by
  rw [BlockTree.lookup_eq_getElem? hValid idx, ← compGetElem?_eq]

/-- Premise-free lookup equivalence for `BlockTree.ofList xs`. -/
theorem BlockTree.ofList_lookup_eq {α : Type} (xs : List α) (idx : Nat) :
    (BlockTree.ofList xs).lookup idx = Trusted.MirSemantics.getElem? xs idx :=
  BlockTree.lookup_eq_getElem? (valid_blockTree_ofList xs) idx

/-- Same-index read-after-modify law for `BlockTree.modify` (`idx < pow2
bt.depth`). -/
theorem BlockTree.lookup_modify_same {α : Type} (bt : BlockTree α)
    (idx : Nat) (v : Option α) (hidx : idx < pow2 bt.depth) :
    (bt.modify idx v).lookup idx = v :=
  ptreeGetAt_ptreeModifyAt_same bt.depth bt.tree idx v hidx

/-- Frame law for `BlockTree.modify` at any distinct index `j ≠ idx`. -/
theorem BlockTree.lookup_modify_ne {α : Type} (bt : BlockTree α)
    (idx j : Nat) (v : Option α) (hNe : j ≠ idx) :
    (bt.modify idx v).lookup j = bt.lookup j :=
  ptreeGetAt_ptreeModifyAt_ne bt.depth bt.tree idx j v hNe

/-- `BlockTree.modify idx (some val)` preserves `ValidBlockTree` across
`Trusted.MirSemantics.setElem?`. -/
theorem BlockTree.valid_modify_of_setElem? {α : Type} {xs xs' : List α}
    {bt : BlockTree α} {idx : Nat} {val : α}
    (hValid : ValidBlockTree xs bt)
    (hSet : Trusted.MirSemantics.setElem? xs idx val = some xs') :
    ValidBlockTree xs' (bt.modify idx (some val)) := by
  have hLtLen := setElem?_lt_and_length hSet
  have hIdxPow2 : idx < pow2 bt.depth := Nat.lt_of_lt_of_le hLtLen.1 hValid.1
  refine ⟨?_, fun j => ?_⟩
  · unfold BlockTree.modify
    dsimp only
    rw [hLtLen.2]
    exact hValid.1
  · cases hBeq : Nat.beq j idx with
    | true =>
      have hEq : j = idx := natEq_of_beq j idx hBeq
      subst hEq
      rw [BlockTree.lookup_modify_same bt j (some val) hIdxPow2,
        bt_getElem?_setElem?_same hSet]
    | false =>
      have hNe : j ≠ idx := fun hEq => by
        subst hEq
        rw [natBeq_refl j] at hBeq
        exact boolFalseNeTrue hBeq.symm
      rw [BlockTree.lookup_modify_ne bt idx j (some val) hNe,
        hValid.2 j, bt_getElem?_setElem?_ne hNe hSet]

/-! ## `BlockTree`-Accelerated Single-Body MIR Step Evaluator -/

/-- Single-body MIR step evaluator (`0` `noncomputable`) indexing basic blocks
via `bt.lookup` (`O(bt.depth)` trie steps on a normalized `BlockTree`). -/
def evalMirStepBlockTreeBy (tyEq : MirTy → MirTy → Bool)
    (bt : BlockTree BasicBlock) (body : Body) (s : State) :
    StepResult State TerminalOut :=
  match s.frames with
  | [frame] =>
    if !Nat.beq frame.defId 0 then .fault .unsupported
    else
      match bt.lookup frame.blockIdx with
      | none => .fault .unsupported
      | some bb =>
        match compGetElem? bb.statements frame.stmtIdx with
        | some stmt => evalStatementBy tyEq body frame s.mem s.callerMem stmt
        | none =>
          if Nat.beq frame.stmtIdx bb.statements.length then
            evalTerminatorComp body bb frame s.mem s.callerMem
          else
            .fault .unsupported
  | _ => .fault .unsupported

/-- Fuel-bounded `BlockTree`-accelerated single-body MIR evaluator. -/
def evalMirFuelBlockTreeBy (tyEq : MirTy → MirTy → Bool)
    (bt : BlockTree BasicBlock) (body : Body) (fuel : Nat) (s : State) :
    StepResult State TerminalOut :=
  @Nat.rec (fun _ => State → StepResult State TerminalOut)
    (fun st => .step st)
    (fun _ ih st =>
      match evalMirStepBlockTreeBy tyEq bt body st with
      | .step st' => ih st'
      | .done out => .done out
      | .fault k => .fault k)
    fuel s

/-- Agreement between `evalMirStepBlockTreeBy` and `evalMirStepBy` on
`Anneal.MirWp.bodyProg body` for any valid `BlockTree BasicBlock`. -/
theorem evalMirStepBlockTreeBy_eq_evalMirStepBy (tyEq : MirTy → MirTy → Bool)
    {body : Body} {bt : BlockTree BasicBlock}
    (hValid : ValidBlockTree body.basicBlocks bt) (s : State) :
    evalMirStepBlockTreeBy tyEq bt body s =
      evalMirStepBy tyEq (Anneal.MirWp.bodyProg body) 0 s := by
  unfold evalMirStepBlockTreeBy evalMirStepBy Anneal.MirWp.bodyProg
  cases s with
  | mk frames callerMem mem =>
    cases frames with
    | nil => rfl
    | cons frame tail =>
      cases tail with
      | cons _ _ => rfl
      | nil =>
        cases frame with
        | mk defId blkIdx stmtIdx locs =>
          cases defId with
          | zero =>
            dsimp only
            change (match bt.lookup blkIdx with
                | none => StepResult.fault FaultKind.unsupported
                | some bb =>
                  match compGetElem? bb.statements stmtIdx with
                  | some stmt =>
                    evalStatementBy tyEq body ⟨0, blkIdx, stmtIdx, locs⟩
                      mem callerMem stmt
                  | none =>
                    if Nat.beq stmtIdx bb.statements.length then
                      evalTerminatorComp body bb ⟨0, blkIdx, stmtIdx, locs⟩
                        mem callerMem
                    else StepResult.fault FaultKind.unsupported) =
              (match compGetElem? body.basicBlocks blkIdx with
                | none => StepResult.fault FaultKind.unsupported
                | some bb =>
                  match compGetElem? bb.statements stmtIdx with
                  | some stmt =>
                    evalStatementBy tyEq body ⟨0, blkIdx, stmtIdx, locs⟩
                      mem callerMem stmt
                  | none =>
                    if Nat.beq stmtIdx bb.statements.length then
                      evalTerminatorComp body bb ⟨0, blkIdx, stmtIdx, locs⟩
                        mem callerMem
                    else StepResult.fault FaultKind.unsupported)
            rw [BlockTree.lookup_eq_compGetElem? hValid blkIdx]
          | succ _ => rfl

/-- Agreement between `evalMirStepBlockTreeBy` and
`Trusted.MirSemantics.evalStep (Anneal.MirWp.bodyProg body) 0` when `tyEq`
agrees with `MirTy.beq`. -/
theorem evalMirStepBlockTreeBy_eq_evalStep (tyEq : MirTy → MirTy → Bool)
    (hTyEq : ∀ a b, tyEq a b = MirTy.beq a b)
    {body : Body} {bt : BlockTree BasicBlock}
    (hValid : ValidBlockTree body.basicBlocks bt) (s : State) :
    evalMirStepBlockTreeBy tyEq bt body s =
      evalStep (Anneal.MirWp.bodyProg body) 0 s := by
  rw [evalMirStepBlockTreeBy_eq_evalMirStepBy tyEq hValid s]
  exact evalMirStepBy_eq tyEq hTyEq (Anneal.MirWp.bodyProg body) 0 s

/-- Agreement between `evalMirFuelBlockTreeBy` and `evalMirFuelBy` on
`Anneal.MirWp.bodyProg body` for any valid `BlockTree BasicBlock`. -/
theorem evalMirFuelBlockTreeBy_eq_evalMirFuelBy (tyEq : MirTy → MirTy → Bool)
    {body : Body} {bt : BlockTree BasicBlock}
    (hValid : ValidBlockTree body.basicBlocks bt) :
    ∀ (fuel : Nat) (s : State),
      evalMirFuelBlockTreeBy tyEq bt body fuel s =
        evalMirFuelBy tyEq (Anneal.MirWp.bodyProg body) fuel s
  | 0, _ => rfl
  | k + 1, s => by
    change (match evalMirStepBlockTreeBy tyEq bt body s with
        | .step st' => evalMirFuelBlockTreeBy tyEq bt body k st'
        | .done out => .done out
        | .fault fk => .fault fk) =
      (match evalMirStepBy tyEq (Anneal.MirWp.bodyProg body) 0 s with
        | .step st' => evalMirFuelBy tyEq (Anneal.MirWp.bodyProg body) k st'
        | .done out => .done out
        | .fault fk => .fault fk)
    rw [evalMirStepBlockTreeBy_eq_evalMirStepBy tyEq hValid s]
    cases evalMirStepBy tyEq (Anneal.MirWp.bodyProg body) 0 s with
    | step st' =>
      exact evalMirFuelBlockTreeBy_eq_evalMirFuelBy tyEq hValid k st'
    | done _ => rfl
    | fault _ => rfl

/-- Lifts fuel-bounded `evalMirFuelBlockTreeBy` outcomes into
`Anneal.MirWp.wpOutcomeState` when `tyEq` agrees with `MirTy.beq`. -/
theorem wpOutcomeState_of_evalMirFuelBlockTreeBy {tyEq : MirTy → MirTy → Bool}
    (hTyEq : ∀ a b, tyEq a b = MirTy.beq a b)
    {body : Body} {bt : BlockTree BasicBlock}
    (hValid : ValidBlockTree body.basicBlocks bt)
    {onDone : TerminalOut → Prop} {onFault : FaultKind → Prop}
    {fuel : Nat} {s : State}
    (h : match evalMirFuelBlockTreeBy tyEq bt body fuel s with
         | .done out => onDone out
         | .fault fk => onFault fk
         | .step _ => False) :
    Anneal.MirWp.wpOutcomeState (Anneal.MirWp.bodyProg body)
      onDone onFault fuel s := by
  rw [evalMirFuelBlockTreeBy_eq_evalMirFuelBy tyEq hValid fuel s] at h
  exact wpOutcomeState_of_evalMirFuelBy hTyEq h

end Anneal.Core
