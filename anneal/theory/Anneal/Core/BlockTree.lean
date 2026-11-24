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
public import Init.Data.Nat.Div.Basic
public import Init.Data.List.Basic
public import Init.Control.Except
public import Trusted
public import Trusted.MirAst
public import Trusted.MirModel
public import Trusted.MirSemantics
public import Anneal.MirWp
public import Anneal.MirTotal.Ops
public import Anneal.MirTotal.StepCore

public section

namespace Anneal.Core

open Trusted.MirAst Trusted.MirSemantics Anneal.MirTotal

/-!
# Logarithmic Radix-2 and Dense `Chunk8` Basic-Block Trees (`Core.BlockTree`)

Provides total, LCNF-computable (`0` `noncomputable`, `0` `._unsafe_rec`)
indexed lookup tables:

1. Radix-2 binary trie (`PTree α` and `BlockTree α`) supporting `O(log N)` trie
   lookup and single-pass functional update (`ptreeModifyAt`), `O(N log N)`
   direct list splitting (`ptreeFromListAt`) with `O(log N)` depth
   (`compLog2Depth`), unconditional equivalence to
   `Trusted.MirSemantics.getElem?` across both in-bounds and out-of-bounds
   indices, and a `BlockTree`-indexed single-body MIR step evaluator
   (`evalMirStepBlockTreeBy`).
2. Dense 8-wide balanced spine (`Chunk8 α`, `Chunk8Tree α`,
   `Chunk8BlockTree α`, and `MaskTree := Chunk8BlockTree Bool`), unifying dense
   block tables, chunked binary trees, and boolean live-local masks. Packing 8
   contiguous elements per `Chunk8` leaf keeps spine depth `≤ 9` and tree height
   `≤ 10` (`≤ 11` including the leaf chunk) at `N = 4,096` elements, uses
   zero-`Decidable` `cond` dispatch on the spine, supports `O(1)` 8-element
   batch chunk lookup (`lookupChunk`), and matches
   `Trusted.MirSemantics.getElem?` unconditionally.
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
@[expose] def pow2 (n : Nat) : Nat :=
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
@[expose] def ptreeTabulateAt {α : Type} (depth : Nat) :
    Nat → Nat → (Nat → Option α) → PTree α :=
  @Nat.rec (fun _ => Nat → Nat → (Nat → Option α) → PTree α)
    (fun offset _ f => PTree.leaf (f offset))
    (fun _ ih offset step f =>
      PTree.node (ih offset (2 * step) f) (ih (offset + step) (2 * step) f))
    depth

/-- Tabulates `f 0 .. f (2^depth - 1)` into a balanced radix-2 `PTree α`. -/
@[expose] def ptreeTabulate {α : Type} (f : Nat → Option α) (depth : Nat) : PTree α :=
  ptreeTabulateAt depth 0 1 f

/-- Looks up `idx` in a depth-`depth` `PTree α` in `O(depth)` bit steps. -/
@[expose] def ptreeGetAt {α : Type} (depth : Nat) : PTree α → Nat → Option α :=
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
@[expose] def ptreeModifyAt {α : Type} (depth : Nat) :
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
@[expose] def compLog2DepthGo (n : Nat) : Nat → Nat → Nat → Nat :=
  @Nat.rec (fun _ => Nat → Nat → Nat)
    (fun depth _ => depth)
    (fun _ ih depth cap =>
      if Nat.ble n cap then depth
      else ih (depth + 1) (2 * cap))

/-- Smallest radix-2 tree depth covering `n` elements (`compLog2Depth 26 = 5`,
`compLog2Depth 64 = 6`). -/
@[expose] def compLog2Depth (n : Nat) : Nat := compLog2DepthGo n n 0 1

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
@[expose] def unzipEvenOdd {α : Type} (xs : List α) : List α × List α :=
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
@[expose] def ptreeFromListAt {α : Type} (depth : Nat) : List α → PTree α :=
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
@[expose] def compListLength {α : Type} (xs : List α) : Nat :=
  List.foldr (fun _ k => Nat.succ k) 0 xs

/-- Exact agreement between `compListLength` and `List.length`. -/
theorem compListLength_eq {α : Type} :
    ∀ (xs : List α), compListLength xs = xs.length
  | [] => rfl
  | _ :: tl => congrArg Nat.succ (compListLength_eq tl)

/-- Tabulates `xs` into a `BlockTree α` at explicit depth `depth` via
single-pass even/odd list splitting (`ptreeFromListAt`). -/
@[expose] def BlockTree.ofListAt {α : Type} (xs : List α) (depth : Nat) : BlockTree α :=
  { depth := depth, tree := ptreeFromListAt depth xs }

/-- Tabulates `xs` into a `BlockTree α` at depth
`compLog2Depth (compListLength xs)`. -/
@[expose] def BlockTree.ofList {α : Type} (xs : List α) : BlockTree α :=
  BlockTree.ofListAt xs (compLog2Depth (compListLength xs))

/-- Looks up index `idx` in `bt` in `O(bt.depth)` trie steps. -/
@[expose] def BlockTree.lookup {α : Type} (bt : BlockTree α) (idx : Nat) : Option α :=
  ptreeGetAt bt.depth bt.tree idx

/-- Functionally updates index `idx` in `bt` in `O(bt.depth)` trie steps. -/
@[expose] def BlockTree.modify {α : Type} (bt : BlockTree α) (idx : Nat) (v : Option α) :
    BlockTree α :=
  { depth := bt.depth, tree := ptreeModifyAt bt.depth bt.tree idx v }

/-- Validity predicate tying a pure-data `BlockTree α` back to `xs`. -/
@[expose] def ValidBlockTree {α : Type} (xs : List α) (bt : BlockTree α) : Prop :=
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

private theorem attachCallersComp_nil_evalStatementBy
    (tyEq : MirTy → MirTy → Bool) (body : Body) (frame : FrameState)
    (mem : MemoryState) (callerMem : CallerMemory) (stmt : StatementKind) :
    Anneal.MirTotal.attachCallersComp []
        (Anneal.MirTotal.evalStatementBy tyEq body frame mem callerMem stmt) =
      Anneal.MirTotal.evalStatementBy tyEq body frame mem callerMem stmt := by
  unfold Anneal.MirTotal.evalStatementBy
  cases stmt with
  | nop | unsupported => rfl
  | storageLive lid =>
    dsimp only
    cases Anneal.MirTotal.compGetElem? body.locals lid with
    | none => rfl
    | some _ =>
      dsimp only
      cases Anneal.MirTotal.compGetElem? frame.locals lid with
      | none => rfl
      | some old =>
        dsimp only
        cases Anneal.MirTotal.compSetElem? frame.locals lid _ with
        | none => rfl
        | some _ =>
          dsimp only
          cases Anneal.MirTotal.deallocateLocalComp mem old <;> rfl
  | storageDead lid =>
    dsimp only
    cases Nat.beq lid 0 with
    | true => rfl
    | false =>
      cases Anneal.MirTotal.compGetElem? frame.locals lid with
      | none => rfl
      | some old =>
        dsimp only
        cases Anneal.MirTotal.compSetElem? frame.locals lid .dead with
        | none => rfl
        | some _ =>
          dsimp only
          cases Anneal.MirTotal.deallocateLocalComp mem old <;> rfl
  | assign dst rv =>
    dsimp only
    cases (!dst.projection.isEmpty) with
    | true => rfl
    | false =>
      cases Anneal.MirTotal.compGetElem? body.locals dst.localId with
      | none => rfl
      | some dstTy =>
        dsimp only
        cases Anneal.MirTotal.evalRvalueBy tyEq body.locals frame.locals mem
            dstTy rv with
        | error _ => rfl
        | ok triple =>
          dsimp only
          cases triple with
          | mk v rest =>
            cases rest with
            | mk ls₁ m₁ =>
              dsimp only
              cases Anneal.MirTotal.writePlaceBy tyEq ls₁ m₁ dst.localId dstTy
                  v with
              | error _ => rfl
              | ok pair => cases pair; rfl

private theorem attachCallersComp_nil_evalTerminatorComp (body : Body)
    (bb : BasicBlock) (frame : FrameState) (mem : MemoryState)
    (callerMem : CallerMemory) :
    Anneal.MirTotal.attachCallersComp []
        (Anneal.MirTotal.evalTerminatorComp body bb frame mem callerMem) =
      Anneal.MirTotal.evalTerminatorComp body bb frame mem callerMem := by
  unfold Anneal.MirTotal.evalTerminatorComp
  cases bb.terminator with
  | goto _ | unreachable | unwindResume | assert _ _ _ _ _ | call _ _ _ _ _
  | sysrootCall _ _ _ _ _ | coreCall _ _ _ _ _ | unsupported => rfl
  | return_ =>
    dsimp only
    cases bb.cleanup with
    | true => rfl
    | false =>
      cases Anneal.MirTotal.compGetElem? frame.locals 0 with
      | none => rfl
      | some slot =>
        cases slot with
        | dead => rfl
        | partialTuple _ => rfl
        | immediate opt => cases opt <;> rfl
        | indirect mplace =>
          dsimp only
          cases Anneal.MirTotal.compGetElem? body.locals 0 with
          | none => rfl
          | some retTy =>
            dsimp only
            cases Anneal.MirTotal.loadIndirectComp mem retTy mplace with
            | error _ => rfl
            | ok opt => cases opt <;> rfl
  | switchInt discr targets =>
    dsimp only
    cases Anneal.MirTotal.evalPrimitiveOperandComp body.locals frame.locals mem
        discr with
    | error _ => rfl
    | ok triple =>
      dsimp only
      cases triple with
      | mk dv rest =>
        cases rest with
        | mk ls₁ m₁ =>
          dsimp only
          cases dv with
          | scalar sv =>
            dsimp only
            cases Anneal.MirTotal.evalSwitchBranchesComp sv.width sv.bits
                targets.otherwise targets.branches <;> rfl
          | bool b =>
            dsimp only
            cases Anneal.MirTotal.evalBoolSwitchBranchesComp b targets.otherwise
                targets.branches <;> rfl
          | char c =>
            dsimp only
            cases Anneal.MirTotal.evalCharSwitchBranchesComp c targets.otherwise
                targets.branches <;> rfl
          | ptr _ | ordering _ | unit | tuple _ | bytes _ | enumVal _ _
          | slicePtr _ _ | rangeTo _ | rangeFrom _ =>
            dsimp only
            cases targets.branches <;> rfl

/-- Shared proof equating any indexed single-body step evaluator (such as
`evalMirStepBlockTreeBy` or `evalMirStepChunk8By`) with `evalMirStepBy` on
`Anneal.MirWp.bodyProg body` for every `s : State`. -/
private theorem evalMirStepIndexed_eq_evalMirStepBy
    (tyEq : MirTy → MirTy → Bool) (body : Body)
    (lookupFn : Nat → Option BasicBlock)
    (hLookup : ∀ idx, lookupFn idx = Anneal.MirTotal.compGetElem?
      body.basicBlocks idx)
    (s : State) :
    (match s.frames with
     | [frame] =>
       match frame.sysrootOp? with
       | some _ => evalMirStepBy tyEq (Anneal.MirWp.bodyProg body) 0 s
       | none =>
         if !Nat.beq frame.defId 0 then .fault .unsupported
         else
           match lookupFn frame.blockIdx with
           | none => .fault .unsupported
           | some bb =>
             match compGetElem? bb.statements frame.stmtIdx with
             | some stmt => evalStatementBy tyEq body frame s.mem s.callerMem stmt
             | none =>
               if Nat.beq frame.stmtIdx bb.statements.length then
                 match bb.terminator with
                 | .call _ _ _ _ _ | .sysrootCall _ _ _ _ _ =>
                   evalMirStepBy tyEq (Anneal.MirWp.bodyProg body) 0 s
                 | _ => evalTerminatorComp body bb frame s.mem s.callerMem
               else
                 .fault .unsupported
     | _ :: _ :: _ => evalMirStepBy tyEq (Anneal.MirWp.bodyProg body) 0 s
     | [] => .fault .unsupported) =
      evalMirStepBy tyEq (Anneal.MirWp.bodyProg body) 0 s := by
  cases s with
  | mk frames callerMem mem =>
    cases frames with
    | nil => rfl
    | cons frame tail =>
      cases tail with
      | cons _ _ => rfl
      | nil =>
        cases frame with
        | mk defId blockIdx stmtIdx locals sysrootOp? retDst? retTarget? =>
          cases sysrootOp? with
          | some _ => rfl
          | none =>
            cases defId with
            | succ _ => rfl
            | zero =>
              dsimp only
              unfold evalMirStepBy Anneal.MirWp.bodyProg
              dsimp only [activeFrameBodyComp]
              rw [show compGetElem? [body] 0 = some body from rfl]
              dsimp only
              rw [hLookup blockIdx]
              cases hBB : compGetElem? body.basicBlocks blockIdx with
              | none => rfl
              | some bb =>
                dsimp only
                cases hSt : compGetElem? bb.statements stmtIdx with
                | some stmt =>
                  exact (attachCallersComp_nil_evalStatementBy tyEq body
                    ⟨0, blockIdx, stmtIdx, locals, none, retDst?, retTarget?⟩ mem
                    callerMem stmt).symm
                | none =>
                  dsimp only
                  cases hLen : Nat.beq stmtIdx bb.statements.length with
                  | false => rfl
                  | true =>
                    cases hT : bb.terminator with
                    | return_ => rfl
                    | call _ _ _ _ _ | sysrootCall _ _ _ _ _ =>
                      rw [ite_bool_false (rfl : (!Nat.zero.beq 0) = false)]
                      rw [ite_bool_true rfl]
                    | goto _ | switchInt _ _ | unreachable | unwindResume
                    | assert _ _ _ _ _ | coreCall _ _ _ _ _ | unsupported =>
                      exact (attachCallersComp_nil_evalTerminatorComp body bb
                        ⟨0, blockIdx, stmtIdx, locals, none, retDst?, retTarget?⟩
                        mem callerMem).symm

/-- Single-body MIR step evaluator (`0` `noncomputable`) indexing basic blocks
via `bt.lookup` (`O(bt.depth)` trie steps on a normalized `BlockTree`). -/
@[expose] def evalMirStepBlockTreeBy (tyEq : MirTy → MirTy → Bool)
    (bt : BlockTree BasicBlock) (body : Body) (s : State) :
    StepResult State TerminalOut :=
  match s.frames with
  | [frame] =>
    match frame.sysrootOp? with
    | some _ => evalMirStepBy tyEq (Anneal.MirWp.bodyProg body) 0 s
    | none =>
      if !Nat.beq frame.defId 0 then .fault .unsupported
      else
        match bt.lookup frame.blockIdx with
        | none => .fault .unsupported
        | some bb =>
          match compGetElem? bb.statements frame.stmtIdx with
          | some stmt => evalStatementBy tyEq body frame s.mem s.callerMem stmt
          | none =>
            if Nat.beq frame.stmtIdx bb.statements.length then
              match bb.terminator with
              | .call _ _ _ _ _ | .sysrootCall _ _ _ _ _ =>
                evalMirStepBy tyEq (Anneal.MirWp.bodyProg body) 0 s
              | _ => evalTerminatorComp body bb frame s.mem s.callerMem
            else
              .fault .unsupported
  | _ :: _ :: _ => evalMirStepBy tyEq (Anneal.MirWp.bodyProg body) 0 s
  | [] => .fault .unsupported

/-- Fuel-bounded `BlockTree`-accelerated single-body MIR evaluator. -/
@[expose] def evalMirFuelBlockTreeBy (tyEq : MirTy → MirTy → Bool)
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
      evalMirStepBy tyEq (Anneal.MirWp.bodyProg body) 0 s :=
  evalMirStepIndexed_eq_evalMirStepBy tyEq body bt.lookup
    (BlockTree.lookup_eq_compGetElem? hValid) s

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

/-! ## Dense 8-Wide Balanced Spine (`Chunk8`, `Chunk8BlockTree`, `MaskTree`) -/

/-- Fixed-width 8-slot leaf chunk storing `Option α` entries at offsets `0..7`.

Grouping 8 contiguous indices per leaf shrinks the binary spine by 3 levels so
`N = 4,096` elements fit in `512 = 2^9` chunks (spine depth `9`, tree height
`≤ 10`, total constructor depth `≤ 11` vs. `4,097` for `List.cons`). -/
structure Chunk8 (α : Type) where
  e0 : Option α
  e1 : Option α
  e2 : Option α
  e3 : Option α
  e4 : Option α
  e5 : Option α
  e6 : Option α
  e7 : Option α

/-- All-`none` `Chunk8 α`. -/
@[expose] def Chunk8.empty {α : Type} : Chunk8 α :=
  ⟨none, none, none, none, none, none, none, none⟩

/-- Constant-time `O(1)` slot lookup in `Chunk8 α` (returns `none` for
`r ≥ 8`). -/
@[expose] def Chunk8.get {α : Type} (c : Chunk8 α) (r : Nat) : Option α :=
  match r with
  | 0 => c.e0
  | 1 => c.e1
  | 2 => c.e2
  | 3 => c.e3
  | 4 => c.e4
  | 5 => c.e5
  | 6 => c.e6
  | 7 => c.e7
  | _ => none

/-- Constant-time `O(1)` slot update in `Chunk8 α`.

Destructures `c` once into flat constructor fields instead of using record
update projections so repeated updates do not build nested projection chains in
kernel WHNF. -/
@[expose] def Chunk8.set {α : Type} (c : Chunk8 α) (r : Nat) (v : Option α) : Chunk8 α :=
  match c with
  | ⟨e0, e1, e2, e3, e4, e5, e6, e7⟩ =>
    match r with
    | 0 => ⟨v, e1, e2, e3, e4, e5, e6, e7⟩
    | 1 => ⟨e0, v, e2, e3, e4, e5, e6, e7⟩
    | 2 => ⟨e0, e1, v, e3, e4, e5, e6, e7⟩
    | 3 => ⟨e0, e1, e2, v, e4, e5, e6, e7⟩
    | 4 => ⟨e0, e1, e2, e3, v, e5, e6, e7⟩
    | 5 => ⟨e0, e1, e2, e3, e4, v, e6, e7⟩
    | 6 => ⟨e0, e1, e2, e3, e4, e5, v, e7⟩
    | 7 => ⟨e0, e1, e2, e3, e4, e5, e6, v⟩
    | _ => ⟨e0, e1, e2, e3, e4, e5, e6, e7⟩

/-- Lookup on `Chunk8.empty` is always `none`. -/
theorem Chunk8.get_empty {α : Type} (r : Nat) :
    (Chunk8.empty : Chunk8 α).get r = none := by
  cases r with
  | zero => rfl
  | succ r1 =>
    cases r1 with
    | zero => rfl
    | succ r2 =>
      cases r2 with
      | zero => rfl
      | succ r3 =>
        cases r3 with
        | zero => rfl
        | succ r4 =>
          cases r4 with
          | zero => rfl
          | succ r5 =>
            cases r5 with
            | zero => rfl
            | succ r6 =>
              cases r6 with
              | zero => rfl
              | succ r7 =>
                cases r7 <;> rfl

private theorem nat_ge8_contra {r : Nat} (h : r + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 < 8) :
    False :=
  Nat.not_lt_of_ge (Nat.le_add_left 8 r) h

private theorem chunk8_get_ge8 {α : Type} (c : Chunk8 α) (r : Nat) :
    c.get (r + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1) = none := rfl

private theorem chunk8_get_set_ge8 {α : Type} (c : Chunk8 α) (r j : Nat)
    (v : Option α) :
    (c.set r v).get (j + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1) =
      c.get (j + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1) := by
  rw [chunk8_get_ge8, chunk8_get_ge8]

/-- Same-slot read-after-write law for `Chunk8.set` (`r < 8`). -/
theorem Chunk8.get_set_same {α : Type} (c : Chunk8 α) {r : Nat}
    (v : Option α) (hr : r < 8) :
    (c.set r v).get r = v := by
  cases c with
  | mk e0 e1 e2 e3 e4 e5 e6 e7 =>
    cases r with
    | zero => rfl
    | succ r1 =>
      cases r1 with
      | zero => rfl
      | succ r2 =>
        cases r2 with
        | zero => rfl
        | succ r3 =>
          cases r3 with
          | zero => rfl
          | succ r4 =>
            cases r4 with
            | zero => rfl
            | succ r5 =>
              cases r5 with
              | zero => rfl
              | succ r6 =>
                cases r6 with
                | zero => rfl
                | succ r7 =>
                  cases r7 with
                  | zero => rfl
                  | succ r8 => exact False.elim (nat_ge8_contra hr)

private theorem chunk8_get_set_ne_lt8 {α : Type} (c : Chunk8 α) {r j : Nat}
    (v : Option α) (hNe : j ≠ r) :
    (c.set r v).get j = c.get j := by
  cases j with
  | zero =>
    cases r with
    | zero => exact False.elim (hNe rfl)
    | succ r1 =>
      cases r1 with
      | zero => cases c; rfl
      | succ r2 =>
        cases r2 with
        | zero => cases c; rfl
        | succ r3 =>
          cases r3 with
          | zero => cases c; rfl
          | succ r4 =>
            cases r4 with
            | zero => cases c; rfl
            | succ r5 =>
              cases r5 with
              | zero => cases c; rfl
              | succ r6 =>
                cases r6 with
                | zero => cases c; rfl
                | succ r7 =>
                  cases r7 with
                  | zero => cases c; rfl
                  | succ _ => cases c; rfl
  | succ j1 =>
    cases j1 with
    | zero =>
      cases r with
      | zero => cases c; rfl
      | succ r1 =>
        cases r1 with
        | zero => exact False.elim (hNe rfl)
        | succ r2 =>
          cases r2 with
          | zero => cases c; rfl
          | succ r3 =>
            cases r3 with
            | zero => cases c; rfl
            | succ r4 =>
              cases r4 with
              | zero => cases c; rfl
              | succ r5 =>
                cases r5 with
                | zero => cases c; rfl
                | succ r6 =>
                  cases r6 with
                  | zero => cases c; rfl
                  | succ r7 =>
                    cases r7 with
                    | zero => cases c; rfl
                    | succ _ => cases c; rfl
    | succ j2 =>
      cases j2 with
      | zero =>
        cases r with
        | zero => cases c; rfl
        | succ r1 =>
          cases r1 with
          | zero => cases c; rfl
          | succ r2 =>
            cases r2 with
            | zero => exact False.elim (hNe rfl)
            | succ r3 =>
              cases r3 with
              | zero => cases c; rfl
              | succ r4 =>
                cases r4 with
                | zero => cases c; rfl
                | succ r5 =>
                  cases r5 with
                  | zero => cases c; rfl
                  | succ r6 =>
                    cases r6 with
                    | zero => cases c; rfl
                    | succ r7 =>
                      cases r7 with
                      | zero => cases c; rfl
                      | succ _ => cases c; rfl
      | succ j3 =>
        cases j3 with
        | zero =>
          cases r with
          | zero => cases c; rfl
          | succ r1 =>
            cases r1 with
            | zero => cases c; rfl
            | succ r2 =>
              cases r2 with
              | zero => cases c; rfl
              | succ r3 =>
                cases r3 with
                | zero => exact False.elim (hNe rfl)
                | succ r4 =>
                  cases r4 with
                  | zero => cases c; rfl
                  | succ r5 =>
                    cases r5 with
                    | zero => cases c; rfl
                    | succ r6 =>
                      cases r6 with
                      | zero => cases c; rfl
                      | succ r7 =>
                        cases r7 with
                        | zero => cases c; rfl
                        | succ _ => cases c; rfl
        | succ j4 =>
          cases j4 with
          | zero =>
            cases r with
            | zero => cases c; rfl
            | succ r1 =>
              cases r1 with
              | zero => cases c; rfl
              | succ r2 =>
                cases r2 with
                | zero => cases c; rfl
                | succ r3 =>
                  cases r3 with
                  | zero => cases c; rfl
                  | succ r4 =>
                    cases r4 with
                    | zero => exact False.elim (hNe rfl)
                    | succ r5 =>
                      cases r5 with
                      | zero => cases c; rfl
                      | succ r6 =>
                        cases r6 with
                        | zero => cases c; rfl
                        | succ r7 =>
                          cases r7 with
                          | zero => cases c; rfl
                          | succ _ => cases c; rfl
          | succ j5 =>
            cases j5 with
            | zero =>
              cases r with
              | zero => cases c; rfl
              | succ r1 =>
                cases r1 with
                | zero => cases c; rfl
                | succ r2 =>
                  cases r2 with
                  | zero => cases c; rfl
                  | succ r3 =>
                    cases r3 with
                    | zero => cases c; rfl
                    | succ r4 =>
                      cases r4 with
                      | zero => cases c; rfl
                      | succ r5 =>
                        cases r5 with
                        | zero => exact False.elim (hNe rfl)
                        | succ r6 =>
                          cases r6 with
                          | zero => cases c; rfl
                          | succ r7 =>
                            cases r7 with
                            | zero => cases c; rfl
                            | succ _ => cases c; rfl
            | succ j6 =>
              cases j6 with
              | zero =>
                cases r with
                | zero => cases c; rfl
                | succ r1 =>
                  cases r1 with
                  | zero => cases c; rfl
                  | succ r2 =>
                    cases r2 with
                    | zero => cases c; rfl
                    | succ r3 =>
                      cases r3 with
                      | zero => cases c; rfl
                      | succ r4 =>
                        cases r4 with
                        | zero => cases c; rfl
                        | succ r5 =>
                          cases r5 with
                          | zero => cases c; rfl
                          | succ r6 =>
                            cases r6 with
                            | zero => exact False.elim (hNe rfl)
                            | succ r7 =>
                              cases r7 with
                              | zero => cases c; rfl
                              | succ _ => cases c; rfl
              | succ j7 =>
                cases j7 with
                | zero =>
                  cases r with
                  | zero => cases c; rfl
                  | succ r1 =>
                    cases r1 with
                    | zero => cases c; rfl
                    | succ r2 =>
                      cases r2 with
                      | zero => cases c; rfl
                      | succ r3 =>
                        cases r3 with
                        | zero => cases c; rfl
                        | succ r4 =>
                          cases r4 with
                          | zero => cases c; rfl
                          | succ r5 =>
                            cases r5 with
                            | zero => cases c; rfl
                            | succ r6 =>
                              cases r6 with
                              | zero => cases c; rfl
                              | succ r7 =>
                                cases r7 with
                                | zero => exact False.elim (hNe rfl)
                                | succ _ => cases c; rfl
                | succ j8 => exact chunk8_get_set_ge8 c r j8 v

/-- Distinct-slot frame law for `Chunk8.set` (`j ≠ r`). -/
theorem Chunk8.get_set_ne {α : Type} (c : Chunk8 α) {r j : Nat}
    (v : Option α) (hNe : j ≠ r) :
    (c.set r v).get j = c.get j :=
  chunk8_get_set_ne_lt8 c v hNe

/-- Extracts the leading up-to-8 elements of `xs` into a `Chunk8 α` and returns
the remaining suffix (`0` `noncomputable`). -/
@[expose] def takeChunk8 {α : Type} (xs : List α) : Chunk8 α × List α :=
  match xs with
  | [] => (Chunk8.empty, [])
  | [x0] => (⟨some x0, none, none, none, none, none, none, none⟩, [])
  | [x0, x1] => (⟨some x0, some x1, none, none, none, none, none, none⟩, [])
  | [x0, x1, x2] =>
    (⟨some x0, some x1, some x2, none, none, none, none, none⟩, [])
  | [x0, x1, x2, x3] =>
    (⟨some x0, some x1, some x2, some x3, none, none, none, none⟩, [])
  | [x0, x1, x2, x3, x4] =>
    (⟨some x0, some x1, some x2, some x3, some x4, none, none, none⟩, [])
  | [x0, x1, x2, x3, x4, x5] =>
    (⟨some x0, some x1, some x2, some x3, some x4, some x5, none, none⟩, [])
  | [x0, x1, x2, x3, x4, x5, x6] =>
    (⟨some x0, some x1, some x2, some x3, some x4, some x5, some x6, none⟩, [])
  | x0 :: x1 :: x2 :: x3 :: x4 :: x5 :: x6 :: x7 :: rest =>
    (⟨some x0, some x1, some x2, some x3, some x4, some x5, some x6, some x7⟩,
      rest)

/-- Fuel-bounded single-pass chunk packer via `@Nat.rec` (`0` `noncomputable`,
`0` `brecOn`), terminating immediately on `[]`. -/
@[expose] def packChunk8Fuel {α : Type} (fuel : Nat) : List α → List (Chunk8 α) :=
  @Nat.rec (fun _ => List α → List (Chunk8 α))
    (fun _ => [])
    (fun _ ih xs =>
      match xs with
      | [] => []
      | _ :: _ =>
        let p := takeChunk8 xs
        p.1 :: ih p.2)
    fuel

/-- Packs `xs` into `⌈xs.length / 8⌉` `Chunk8 α` leaves in one linear pass. -/
@[expose] def packChunk8 {α : Type} (xs : List α) : List (Chunk8 α) :=
  packChunk8Fuel (Nat.div (compListLength xs + 7) 8) xs

private theorem nat_le_eight_mul_div_add7 (n : Nat) :
    n ≤ 8 * Nat.div (n + 7) 8 := by
  have hdiv : 8 * Nat.div (n + 7) 8 + Nat.mod (n + 7) 8 = n + 7 :=
    Nat.div_add_mod (n + 7) 8
  have hmod : Nat.mod (n + 7) 8 ≤ 7 :=
    Nat.le_of_lt_succ (Nat.mod_lt (n + 7) (Nat.succ_pos 7))
  have hle : 8 * Nat.div (n + 7) 8 + Nat.mod (n + 7) 8 ≤
      8 * Nat.div (n + 7) 8 + 7 :=
    Nat.add_le_add_left hmod (8 * Nat.div (n + 7) 8)
  rw [hdiv] at hle
  exact Nat.le_of_add_le_add_right hle

private theorem packChunk8Fuel_nil {α : Type} (k : Nat) :
    packChunk8Fuel k ([] : List α) = [] := by
  cases k <;> rfl

private theorem packChunk8Fuel_length_le {α : Type} :
    ∀ (fuel : Nat) (xs : List α), (packChunk8Fuel fuel xs).length ≤ fuel
  | 0, _ => Nat.le_refl 0
  | _ + 1, [] => Nat.zero_le _
  | k + 1, x :: tl =>
    Nat.succ_le_succ (packChunk8Fuel_length_le k (takeChunk8 (x :: tl)).2)

private theorem nat_div8_eq_zero_iff (idx : Nat) :
    Nat.div idx 8 = 0 → idx = Nat.mod idx 8 := by
  intro hq
  have h : 8 * Nat.div idx 8 + Nat.mod idx 8 = idx := Nat.div_add_mod idx 8
  rw [hq, Nat.mul_zero, Nat.zero_add] at h
  exact h.symm

private theorem nat_div8_succ_decomp (idx q : Nat)
    (hq : Nat.div idx 8 = q + 1) :
    idx = (8 * q + Nat.mod idx 8) + 8 ∧
    Nat.div (8 * q + Nat.mod idx 8) 8 = q ∧
    Nat.mod (8 * q + Nat.mod idx 8) 8 = Nat.mod idx 8 := by
  have h : 8 * Nat.div idx 8 + Nat.mod idx 8 = idx := Nat.div_add_mod idx 8
  rw [hq, Nat.mul_succ] at h
  have hmod : Nat.mod idx 8 < 8 := Nat.mod_lt idx (Nat.succ_pos 7)
  have hEq : idx = (8 * q + Nat.mod idx 8) + 8 := by
    have hSwap : (8 * q + Nat.mod idx 8) + 8 = 8 * q + 8 + Nat.mod idx 8 := by
      rw [Nat.add_assoc, Nat.add_comm (Nat.mod idx 8) 8, ← Nat.add_assoc]
    exact h.symm.trans hSwap.symm
  have hq' : Nat.div (8 * q + Nat.mod idx 8) 8 = q := by
    have h1 : Nat.div (Nat.mod idx 8 + 8 * q) 8 =
        Nat.div (Nat.mod idx 8) 8 + q := by
      rw [Nat.mul_comm 8 q]
      exact Nat.add_mul_div_right (Nat.mod idx 8) q (Nat.succ_pos 7)
    have hDivZero : Nat.div (Nat.mod idx 8) 8 = 0 := Nat.div_eq_of_lt hmod
    rw [Nat.add_comm (8 * q) (Nat.mod idx 8), h1, hDivZero, Nat.zero_add]
  have hr' : Nat.mod (8 * q + Nat.mod idx 8) 8 = Nat.mod idx 8 := by
    have hdm :
        8 * Nat.div (8 * q + Nat.mod idx 8) 8 +
          Nat.mod (8 * q + Nat.mod idx 8) 8 =
        8 * q + Nat.mod idx 8 :=
      Nat.div_add_mod (8 * q + Nat.mod idx 8) 8
    rw [hq'] at hdm
    exact Nat.add_left_cancel hdm
  exact ⟨hEq, hq', hr'⟩

private theorem takeChunk8_get_lt8 {α : Type} (xs : List α) (r : Nat)
    (hr : r < 8) :
    (takeChunk8 xs).1.get r = Trusted.MirSemantics.getElem? xs r := by
  cases r with
  | zero =>
    cases xs with
    | nil => rfl
    | cons _ tl =>
      cases tl with
      | nil => rfl
      | cons _ tl2 =>
        cases tl2 with
        | nil => rfl
        | cons _ tl3 =>
          cases tl3 with
          | nil => rfl
          | cons _ tl4 =>
            cases tl4 with
            | nil => rfl
            | cons _ tl5 =>
              cases tl5 with
              | nil => rfl
              | cons _ tl6 =>
                cases tl6 with
                | nil => rfl
                | cons _ tl7 =>
                  cases tl7 <;> rfl
  | succ r1 =>
    cases r1 with
    | zero =>
      cases xs with
      | nil => rfl
      | cons _ tl =>
        cases tl with
        | nil => rfl
        | cons _ tl2 =>
          cases tl2 with
          | nil => rfl
          | cons _ tl3 =>
            cases tl3 with
            | nil => rfl
            | cons _ tl4 =>
              cases tl4 with
              | nil => rfl
              | cons _ tl5 =>
                cases tl5 with
                | nil => rfl
                | cons _ tl6 =>
                  cases tl6 with
                  | nil => rfl
                  | cons _ tl7 => cases tl7 <;> rfl
    | succ r2 =>
      cases r2 with
      | zero =>
        cases xs with
        | nil => rfl
        | cons _ tl =>
          cases tl with
          | nil => rfl
          | cons _ tl2 =>
            cases tl2 with
            | nil => rfl
            | cons _ tl3 =>
              cases tl3 with
              | nil => rfl
              | cons _ tl4 =>
                cases tl4 with
                | nil => rfl
                | cons _ tl5 =>
                  cases tl5 with
                  | nil => rfl
                  | cons _ tl6 =>
                    cases tl6 with
                    | nil => rfl
                    | cons _ tl7 => cases tl7 <;> rfl
      | succ r3 =>
        cases r3 with
        | zero =>
          cases xs with
          | nil => rfl
          | cons _ tl =>
            cases tl with
            | nil => rfl
            | cons _ tl2 =>
              cases tl2 with
              | nil => rfl
              | cons _ tl3 =>
                cases tl3 with
                | nil => rfl
                | cons _ tl4 =>
                  cases tl4 with
                  | nil => rfl
                  | cons _ tl5 =>
                    cases tl5 with
                    | nil => rfl
                    | cons _ tl6 =>
                      cases tl6 with
                      | nil => rfl
                      | cons _ tl7 => cases tl7 <;> rfl
        | succ r4 =>
          cases r4 with
          | zero =>
            cases xs with
            | nil => rfl
            | cons _ tl =>
              cases tl with
              | nil => rfl
              | cons _ tl2 =>
                cases tl2 with
                | nil => rfl
                | cons _ tl3 =>
                  cases tl3 with
                  | nil => rfl
                  | cons _ tl4 =>
                    cases tl4 with
                    | nil => rfl
                    | cons _ tl5 =>
                      cases tl5 with
                      | nil => rfl
                      | cons _ tl6 =>
                        cases tl6 with
                        | nil => rfl
                        | cons _ tl7 => cases tl7 <;> rfl
          | succ r5 =>
            cases r5 with
            | zero =>
              cases xs with
              | nil => rfl
              | cons _ tl =>
                cases tl with
                | nil => rfl
                | cons _ tl2 =>
                  cases tl2 with
                  | nil => rfl
                  | cons _ tl3 =>
                    cases tl3 with
                    | nil => rfl
                    | cons _ tl4 =>
                      cases tl4 with
                      | nil => rfl
                      | cons _ tl5 =>
                        cases tl5 with
                        | nil => rfl
                        | cons _ tl6 =>
                          cases tl6 with
                          | nil => rfl
                          | cons _ tl7 => cases tl7 <;> rfl
            | succ r6 =>
              cases r6 with
              | zero =>
                cases xs with
                | nil => rfl
                | cons _ tl =>
                  cases tl with
                  | nil => rfl
                  | cons _ tl2 =>
                    cases tl2 with
                    | nil => rfl
                    | cons _ tl3 =>
                      cases tl3 with
                      | nil => rfl
                      | cons _ tl4 =>
                        cases tl4 with
                        | nil => rfl
                        | cons _ tl5 =>
                          cases tl5 with
                          | nil => rfl
                          | cons _ tl6 =>
                            cases tl6 with
                            | nil => rfl
                            | cons _ tl7 => cases tl7 <;> rfl
              | succ r7 =>
                cases r7 with
                | zero =>
                  cases xs with
                  | nil => rfl
                  | cons _ tl =>
                    cases tl with
                    | nil => rfl
                    | cons _ tl2 =>
                      cases tl2 with
                      | nil => rfl
                      | cons _ tl3 =>
                        cases tl3 with
                        | nil => rfl
                        | cons _ tl4 =>
                          cases tl4 with
                          | nil => rfl
                          | cons _ tl5 =>
                            cases tl5 with
                            | nil => rfl
                            | cons _ tl6 =>
                              cases tl6 with
                              | nil => rfl
                              | cons _ tl7 => cases tl7 <;> rfl
                | succ r8 => exact False.elim (nat_ge8_contra hr)

private theorem getElem?_packChunk8Fuel {α : Type} :
    ∀ (fuel : Nat) (xs : List α),
      xs.length ≤ 8 * fuel →
      ∀ idx : Nat,
        (match Trusted.MirSemantics.getElem? (packChunk8Fuel fuel xs)
            (Nat.div idx 8) with
         | some c => c.get (Nat.mod idx 8)
         | none => none) =
        Trusted.MirSemantics.getElem? xs idx
  | 0, [], _, idx => by
    cases idx <;> rfl
  | 0, _ :: _, hBound, _ =>
    False.elim (Nat.not_lt_of_ge hBound (Nat.succ_pos _))
  | k + 1, [], _, idx => by
    cases idx <;> rfl
  | k + 1, x :: tl, hBound, idx => by
    let xs := x :: tl
    cases hq : Nat.div idx 8 with
    | zero =>
      have hidx := nat_div8_eq_zero_iff idx hq
      have hr : Nat.mod idx 8 < 8 := Nat.mod_lt idx (Nat.succ_pos 7)
      change (takeChunk8 xs).1.get (Nat.mod idx 8) =
        Trusted.MirSemantics.getElem? xs idx
      rw [takeChunk8_get_lt8 xs (Nat.mod idx 8) hr, ← hidx]
    | succ q' =>
      have hd := nat_div8_succ_decomp idx q' hq
      cases tl with
      | nil =>
        change (match Trusted.MirSemantics.getElem? (packChunk8Fuel k []) q' with
            | some c => c.get (Nat.mod idx 8)
            | none => none) = Trusted.MirSemantics.getElem? [x] idx
        rw [packChunk8Fuel_nil k, hd.1]; rfl
      | cons x1 tl1 =>
        cases tl1 with
        | nil =>
          change (match Trusted.MirSemantics.getElem? (packChunk8Fuel k []) q' with
              | some c => c.get (Nat.mod idx 8)
              | none => none) = Trusted.MirSemantics.getElem? [x, x1] idx
          rw [packChunk8Fuel_nil k, hd.1]; rfl
        | cons x2 tl2 =>
          cases tl2 with
          | nil =>
            change (match Trusted.MirSemantics.getElem? (packChunk8Fuel k []) q' with
                | some c => c.get (Nat.mod idx 8)
                | none => none) =
              Trusted.MirSemantics.getElem? [x, x1, x2] idx
            rw [packChunk8Fuel_nil k, hd.1]; rfl
          | cons x3 tl3 =>
            cases tl3 with
            | nil =>
              change (match Trusted.MirSemantics.getElem? (packChunk8Fuel k []) q' with
                  | some c => c.get (Nat.mod idx 8)
                  | none => none) =
                Trusted.MirSemantics.getElem? [x, x1, x2, x3] idx
              rw [packChunk8Fuel_nil k, hd.1]; rfl
            | cons x4 tl4 =>
              cases tl4 with
              | nil =>
                change (match Trusted.MirSemantics.getElem? (packChunk8Fuel k []) q' with
                    | some c => c.get (Nat.mod idx 8)
                    | none => none) =
                  Trusted.MirSemantics.getElem? [x, x1, x2, x3, x4] idx
                rw [packChunk8Fuel_nil k, hd.1]; rfl
              | cons x5 tl5 =>
                cases tl5 with
                | nil =>
                  change (match Trusted.MirSemantics.getElem? (packChunk8Fuel k []) q' with
                      | some c => c.get (Nat.mod idx 8)
                      | none => none) =
                    Trusted.MirSemantics.getElem? [x, x1, x2, x3, x4, x5] idx
                  rw [packChunk8Fuel_nil k, hd.1]; rfl
                | cons x6 tl6 =>
                  cases tl6 with
                  | nil =>
                    change (match Trusted.MirSemantics.getElem? (packChunk8Fuel k []) q' with
                        | some c => c.get (Nat.mod idx 8)
                        | none => none) =
                      Trusted.MirSemantics.getElem?
                        [x, x1, x2, x3, x4, x5, x6] idx
                    rw [packChunk8Fuel_nil k, hd.1]; rfl
                  | cons x7 rest =>
                    have hRestBound : rest.length ≤ 8 * k := by
                      have hLen :
                          (x :: x1 :: x2 :: x3 :: x4 :: x5 :: x6 :: x7 :: rest).length =
                            rest.length + 8 := rfl
                      rw [hLen, Nat.mul_succ] at hBound
                      exact Nat.le_of_add_le_add_right hBound
                    have ih := getElem?_packChunk8Fuel k rest hRestBound
                      (8 * q' + Nat.mod idx 8)
                    rw [hd.2.1, hd.2.2] at ih
                    change (match Trusted.MirSemantics.getElem?
                        (packChunk8Fuel k rest) q' with
                        | some c => c.get (Nat.mod idx 8)
                        | none => none) =
                      Trusted.MirSemantics.getElem?
                        (x :: x1 :: x2 :: x3 :: x4 :: x5 :: x6 :: x7 :: rest) idx
                    have hStep8 :
                        Trusted.MirSemantics.getElem?
                          (x :: x1 :: x2 :: x3 :: x4 :: x5 :: x6 :: x7 :: rest)
                          ((8 * q' + Nat.mod idx 8) + 8) =
                        Trusted.MirSemantics.getElem? rest
                          (8 * q' + Nat.mod idx 8) := rfl
                    have hRhs :
                        Trusted.MirSemantics.getElem?
                          (x :: x1 :: x2 :: x3 :: x4 :: x5 :: x6 :: x7 :: rest)
                          idx =
                        Trusted.MirSemantics.getElem? rest
                          (8 * q' + Nat.mod idx 8) :=
                      (congrArg
                        (Trusted.MirSemantics.getElem?
                          (x :: x1 :: x2 :: x3 :: x4 :: x5 :: x6 :: x7 :: rest))
                        hd.1).trans hStep8
                    rw [hRhs]
                    exact ih

/-- Balanced dense binary spine storing `Chunk8 α` leaves (`0` `Option` leaf
wrapper overhead). -/
inductive Chunk8Tree (α : Type) : Type where
  | empty : Chunk8Tree α
  | leaf : Chunk8 α → Chunk8Tree α
  | node : Chunk8Tree α → Chunk8Tree α → Chunk8Tree α

@[expose] def natMax2 (a b : Nat) : Nat :=
  cond (Nat.ble a b) b a

private theorem natMax2_le {a b c : Nat} (ha : a ≤ c) (hb : b ≤ c) :
    natMax2 a b ≤ c := by
  unfold natMax2
  cases Nat.ble a b with
  | true => exact hb
  | false => exact ha

/-- Fuel-bounded constructor height of a `Chunk8Tree α` via `@Nat.rec` (`0`
`noncomputable`, `0` `._unsafe_rec`, `hasIR = true`). -/
@[expose] def Chunk8Tree.heightAt {α : Type} (fuel : Nat) : Chunk8Tree α → Nat :=
  @Nat.rec (fun _ => Chunk8Tree α → Nat)
    (fun _ => 0)
    (fun _ ih t =>
      match t with
      | .empty => 0
      | .leaf _ => 1
      | .node l r => natMax2 (ih l) (ih r) + 1)
    fuel

/-- Builds a balanced `Chunk8Tree α` of spine depth `depth` directly from a
packed `List (Chunk8 α)` via single-pass even/odd splitting (`0`
`noncomputable`, `0` `._unsafe_rec`, `hasIR = true`). -/
@[expose] def chunk8TreeFromChunksAt {α : Type} (depth : Nat) :
    List (Chunk8 α) → Chunk8Tree α :=
  @Nat.rec (fun _ => List (Chunk8 α) → Chunk8Tree α)
    (fun cs =>
      match cs with
      | [] => .empty
      | c :: _ => .leaf c)
    (fun _ ih cs =>
      match cs with
      | [] => .empty
      | _ :: _ =>
        let eo := unzipEvenOdd cs
        .node (ih eo.1) (ih eo.2))
    depth

/-- Height of `chunk8TreeFromChunksAt depth cs` is bounded unconditionally by
`depth + 1` at every fuel budget `fuel`. -/
theorem chunk8TreeFromChunksAt_height_le {α : Type} :
    ∀ (fuel depth : Nat) (cs : List (Chunk8 α)),
      (chunk8TreeFromChunksAt depth cs).heightAt fuel ≤ depth + 1
  | 0, depth, _ => Nat.zero_le (depth + 1)
  | _ + 1, 0, [] => Nat.zero_le 1
  | _ + 1, 0, _ :: _ => Nat.le_refl 1
  | _ + 1, d + 1, [] => Nat.zero_le (d + 2)
  | f + 1, d + 1, c :: tl => by
    change natMax2
        ((chunk8TreeFromChunksAt d (unzipEvenOdd (c :: tl)).1).heightAt f)
        ((chunk8TreeFromChunksAt d (unzipEvenOdd (c :: tl)).2).heightAt f) + 1 ≤
      (d + 1) + 1
    exact Nat.succ_le_succ
      (natMax2_le
        (chunk8TreeFromChunksAt_height_le f d (unzipEvenOdd (c :: tl)).1)
        (chunk8TreeFromChunksAt_height_le f d (unzipEvenOdd (c :: tl)).2))

/-- Looks up an entire `Chunk8 α` leaf at `chunkIdx` in `O(depth)` spine steps
using `cond` (zero `@ite`/`Decidable` overhead). -/
@[expose] def chunk8TreeLookupChunkAt {α : Type} (depth : Nat) :
    Chunk8Tree α → Nat → Option (Chunk8 α) :=
  @Nat.rec (fun _ => Chunk8Tree α → Nat → Option (Chunk8 α))
    (fun t chunkIdx =>
      match t with
      | .empty => none
      | .leaf c => cond (Nat.beq chunkIdx 0) (some c) none
      | .node _ _ => none)
    (fun _ ih t chunkIdx =>
      match t with
      | .empty => none
      | .leaf _ => none
      | .node l r =>
        cond (Nat.beq (Nat.mod chunkIdx 2) 0)
          (ih l (Nat.div chunkIdx 2))
          (ih r (Nat.div chunkIdx 2)))
    depth

private theorem chunk8TreeLookupChunkAt_empty {α : Type} (depth chunkIdx : Nat) :
    chunk8TreeLookupChunkAt depth (.empty : Chunk8Tree α) chunkIdx = none := by
  cases depth <;> rfl

/-- Exact chunk lookup equivalence between `chunk8TreeLookupChunkAt` and
`Trusted.MirSemantics.getElem? cs chunkIdx` whenever `cs.length ≤ pow2 depth`.
-/
theorem chunk8TreeLookupChunkAt_fromChunksAt {α : Type} :
    ∀ (depth : Nat) (cs : List (Chunk8 α)),
      cs.length ≤ pow2 depth →
      ∀ chunkIdx : Nat,
        chunk8TreeLookupChunkAt depth (chunk8TreeFromChunksAt depth cs)
            chunkIdx =
          Trusted.MirSemantics.getElem? cs chunkIdx
  | 0, [], _, chunkIdx => by
    cases chunkIdx <;> rfl
  | 0, [c], _, chunkIdx => by
    cases chunkIdx <;> rfl
  | 0, _ :: _ :: tl, hBound, _ => by
    rw [pow2_zero] at hBound
    exact False.elim
      (Nat.not_lt_of_ge hBound (Nat.succ_lt_succ (Nat.succ_pos tl.length)))
  | d + 1, [], _, chunkIdx => by
    change (none : Option (Chunk8 α)) =
      Trusted.MirSemantics.getElem? [] chunkIdx
    cases chunkIdx <;> rfl
  | d + 1, c :: tl, hBound, chunkIdx => by
    let cs := c :: tl
    have hLen := length_unzipEvenOdd_bounds cs
    rw [pow2_succ] at hBound
    have hSub2 : (unzipEvenOdd cs).2.length ≤ pow2 d := by
      have h2 : 2 * (unzipEvenOdd cs).2.length ≤ 2 * pow2 d :=
        Nat.le_trans hLen.2 hBound
      exact Nat.le_of_mul_le_mul_left h2 (Nat.succ_pos 1)
    have hSub1 : (unzipEvenOdd cs).1.length ≤ pow2 d := by
      cases Nat.lt_or_ge (pow2 d) (unzipEvenOdd cs).1.length with
      | inr hle => exact hle
      | inl hgt =>
        have hMulGe : 2 * (pow2 d + 1) ≤ 2 * (unzipEvenOdd cs).1.length :=
          Nat.mul_le_mul_left 2 hgt
        rw [Nat.mul_succ] at hMulGe
        have hUpper : 2 * (unzipEvenOdd cs).1.length ≤ 2 * pow2 d + 1 :=
          Nat.le_trans hLen.1 (Nat.succ_le_succ hBound)
        have hContra : 2 * pow2 d + 2 ≤ 2 * pow2 d + 1 :=
          Nat.le_trans hMulGe hUpper
        exact False.elim
          (Nat.not_lt_of_ge hContra (Nat.lt_succ_self (2 * pow2 d + 1)))
    change
      cond (Nat.beq (Nat.mod chunkIdx 2) 0)
        (chunk8TreeLookupChunkAt d
          (chunk8TreeFromChunksAt d (unzipEvenOdd cs).1) (Nat.div chunkIdx 2))
        (chunk8TreeLookupChunkAt d
          (chunk8TreeFromChunksAt d (unzipEvenOdd cs).2) (Nat.div chunkIdx 2)) =
      Trusted.MirSemantics.getElem? cs chunkIdx
    have hde := nat_div2_decomp chunkIdx
    cases hbeq : Nat.beq (Nat.mod chunkIdx 2) 0 with
    | true =>
      rw [hbeq] at hde
      change 2 * Nat.div chunkIdx 2 = chunkIdx at hde
      dsimp only [cond]
      rw [chunk8TreeLookupChunkAt_fromChunksAt d (unzipEvenOdd cs).1 hSub1
            (Nat.div chunkIdx 2),
          (getElem?_unzipEvenOdd cs (Nat.div chunkIdx 2)).1, hde]
    | false =>
      rw [hbeq] at hde
      change 2 * Nat.div chunkIdx 2 + 1 = chunkIdx at hde
      dsimp only [cond]
      rw [chunk8TreeLookupChunkAt_fromChunksAt d (unzipEvenOdd cs).2 hSub2
            (Nat.div chunkIdx 2),
          (getElem?_unzipEvenOdd cs (Nat.div chunkIdx 2)).2, hde]

/-- Single-pass `O(depth)` functional update of slot `(chunkIdx, rem)` in a
`Chunk8Tree α`, allocating missing spine nodes and `Chunk8.empty` leaves on
demand (`0` `noncomputable`). -/
@[expose] def chunk8TreeModifyAt {α : Type} (depth : Nat) :
    Chunk8Tree α → Nat → Nat → Option α → Chunk8Tree α :=
  @Nat.rec (fun _ => Chunk8Tree α → Nat → Nat → Option α → Chunk8Tree α)
    (fun t chunkIdx rem v =>
      cond (Nat.beq chunkIdx 0)
        (let c := match t with | .leaf c0 => c0 | .empty | .node _ _ => Chunk8.empty
         .leaf (c.set rem v))
        t)
    (fun _ ih t chunkIdx rem v =>
      let (l, r) : Chunk8Tree α × Chunk8Tree α :=
        match t with
        | .node l0 r0 => (l0, r0)
        | .empty | .leaf _ => (.empty, .empty)
      cond (Nat.beq (Nat.mod chunkIdx 2) 0)
        (.node (ih l (Nat.div chunkIdx 2) rem v) r)
        (.node l (ih r (Nat.div chunkIdx 2) rem v)))
    depth

/-- Looks up element `idx` inside a depth-`depth` `Chunk8Tree α` in
`O(depth)` spine steps plus one `O(1)` `Chunk8.get` dispatch. -/
@[expose] def chunk8TreeGetAt {α : Type} (depth : Nat) (t : Chunk8Tree α) (idx : Nat) :
    Option α :=
  match chunk8TreeLookupChunkAt depth t (Nat.div idx 8) with
  | some c => c.get (Nat.mod idx 8)
  | none => none

private theorem chunk8TreeLookupChunkAt_modify_same {α : Type}
    (depth : Nat) (t : Chunk8Tree α) (chunkIdx rem : Nat) (v : Option α)
    (hc : chunkIdx < pow2 depth) :
    chunk8TreeLookupChunkAt depth
        (chunk8TreeModifyAt depth t chunkIdx rem v) chunkIdx =
      some ((match chunk8TreeLookupChunkAt depth t chunkIdx with
             | some c0 => c0
             | none => Chunk8.empty).set rem v) := by
  revert t chunkIdx
  induction depth with
  | zero =>
    intro t chunkIdx hc
    rw [pow2_zero] at hc
    have h0 : chunkIdx = 0 := Nat.eq_zero_of_le_zero (Nat.le_of_lt_succ hc)
    subst h0
    cases t <;> rfl
  | succ d ih =>
    intro t chunkIdx hc
    rw [pow2_succ, Nat.mul_comm 2 (pow2 d)] at hc
    have hhalf : Nat.div chunkIdx 2 < pow2 d :=
      (Nat.div_lt_iff_lt_mul (Nat.succ_pos 1)).mpr hc
    cases t with
    | empty | leaf _ =>
      change chunk8TreeLookupChunkAt (d + 1)
          (cond (Nat.beq (Nat.mod chunkIdx 2) 0)
            (.node (chunk8TreeModifyAt d .empty (Nat.div chunkIdx 2) rem v)
              .empty)
            (.node .empty
              (chunk8TreeModifyAt d .empty (Nat.div chunkIdx 2) rem v)))
          chunkIdx = some (Chunk8.empty.set rem v)
      cases hpar : Nat.beq (Nat.mod chunkIdx 2) 0 with
      | true =>
        dsimp only [cond]
        change cond (Nat.beq (Nat.mod chunkIdx 2) 0)
            (chunk8TreeLookupChunkAt d
              (chunk8TreeModifyAt d .empty (Nat.div chunkIdx 2) rem v)
              (Nat.div chunkIdx 2))
            (chunk8TreeLookupChunkAt d .empty (Nat.div chunkIdx 2)) =
          some (Chunk8.empty.set rem v)
        rw [hpar]
        dsimp only [cond]
        rw [ih .empty (Nat.div chunkIdx 2) hhalf,
          chunk8TreeLookupChunkAt_empty d (Nat.div chunkIdx 2)]
      | false =>
        dsimp only [cond]
        change cond (Nat.beq (Nat.mod chunkIdx 2) 0)
            (chunk8TreeLookupChunkAt d .empty (Nat.div chunkIdx 2))
            (chunk8TreeLookupChunkAt d
              (chunk8TreeModifyAt d .empty (Nat.div chunkIdx 2) rem v)
              (Nat.div chunkIdx 2)) =
          some (Chunk8.empty.set rem v)
        rw [hpar]
        dsimp only [cond]
        rw [ih .empty (Nat.div chunkIdx 2) hhalf,
          chunk8TreeLookupChunkAt_empty d (Nat.div chunkIdx 2)]
    | node l r =>
      change chunk8TreeLookupChunkAt (d + 1)
          (cond (Nat.beq (Nat.mod chunkIdx 2) 0)
            (.node (chunk8TreeModifyAt d l (Nat.div chunkIdx 2) rem v) r)
            (.node l (chunk8TreeModifyAt d r (Nat.div chunkIdx 2) rem v)))
          chunkIdx =
        some ((match cond (Nat.beq (Nat.mod chunkIdx 2) 0)
                  (chunk8TreeLookupChunkAt d l (Nat.div chunkIdx 2))
                  (chunk8TreeLookupChunkAt d r (Nat.div chunkIdx 2)) with
               | some c0 => c0
               | none => Chunk8.empty).set rem v)
      cases hpar : Nat.beq (Nat.mod chunkIdx 2) 0 with
      | true =>
        dsimp only [cond]
        change cond (Nat.beq (Nat.mod chunkIdx 2) 0)
            (chunk8TreeLookupChunkAt d
              (chunk8TreeModifyAt d l (Nat.div chunkIdx 2) rem v)
              (Nat.div chunkIdx 2))
            (chunk8TreeLookupChunkAt d r (Nat.div chunkIdx 2)) = _
        rw [hpar]
        dsimp only [cond]
        exact ih l (Nat.div chunkIdx 2) hhalf
      | false =>
        dsimp only [cond]
        change cond (Nat.beq (Nat.mod chunkIdx 2) 0)
            (chunk8TreeLookupChunkAt d l (Nat.div chunkIdx 2))
            (chunk8TreeLookupChunkAt d
              (chunk8TreeModifyAt d r (Nat.div chunkIdx 2) rem v)
              (Nat.div chunkIdx 2)) = _
        rw [hpar]
        dsimp only [cond]
        exact ih r (Nat.div chunkIdx 2) hhalf

private theorem chunk8TreeLookupChunkAt_modify_ne {α : Type}
    (depth : Nat) (t : Chunk8Tree α) (chunkIdx q rem : Nat) (v : Option α)
    (hNe : q ≠ chunkIdx) :
    chunk8TreeLookupChunkAt depth
        (chunk8TreeModifyAt depth t chunkIdx rem v) q =
      chunk8TreeLookupChunkAt depth t q := by
  revert t chunkIdx q
  induction depth with
  | zero =>
    intro t chunkIdx q hNe
    change chunk8TreeLookupChunkAt 0
        (cond (Nat.beq chunkIdx 0)
          (.leaf ((match t with | .leaf c0 => c0 | .empty | .node _ _ => Chunk8.empty).set rem v))
          t) q =
      chunk8TreeLookupChunkAt 0 t q
    cases hIdx : Nat.beq chunkIdx 0 with
    | false => rfl
    | true =>
      have h0 : chunkIdx = 0 := natEq_of_beq chunkIdx 0 hIdx
      subst h0
      have hq0 : Nat.beq q 0 = false := natBeq_false_of_ne hNe
      dsimp only [cond]
      cases t with
      | empty =>
        change cond (Nat.beq q 0) _ none = none
        rw [hq0]; rfl
      | leaf c0 =>
        change cond (Nat.beq q 0) _ none = cond (Nat.beq q 0) (some c0) none
        rw [hq0]; rfl
      | node _ _ =>
        change cond (Nat.beq q 0) _ none = none
        rw [hq0]; rfl
  | succ d ih =>
    intro t chunkIdx q hNe
    have hDivNe :
        Nat.beq (Nat.mod q 2) 0 = Nat.beq (Nat.mod chunkIdx 2) 0 →
        Nat.div q 2 ≠ Nat.div chunkIdx 2 := by
      intro hParEq hDivEq
      have hdq := nat_div2_decomp q
      have hdc := nat_div2_decomp chunkIdx
      cases hp : Nat.beq (Nat.mod chunkIdx 2) 0 with
      | true =>
        rw [hp] at hParEq hdc
        rw [hParEq] at hdq
        change 2 * Nat.div q 2 = q at hdq
        change 2 * Nat.div chunkIdx 2 = chunkIdx at hdc
        rw [hDivEq, hdc] at hdq
        exact hNe hdq.symm
      | false =>
        rw [hp] at hParEq hdc
        rw [hParEq] at hdq
        change 2 * Nat.div q 2 + 1 = q at hdq
        change 2 * Nat.div chunkIdx 2 + 1 = chunkIdx at hdc
        rw [hDivEq, hdc] at hdq
        exact hNe hdq.symm
    cases t with
    | empty | leaf _ =>
      change chunk8TreeLookupChunkAt (d + 1)
          (cond (Nat.beq (Nat.mod chunkIdx 2) 0)
            (.node (chunk8TreeModifyAt d .empty (Nat.div chunkIdx 2) rem v)
              .empty)
            (.node .empty
              (chunk8TreeModifyAt d .empty (Nat.div chunkIdx 2) rem v))) q =
        none
      cases hpi : Nat.beq (Nat.mod chunkIdx 2) 0 with
      | true =>
        dsimp only [cond]
        change cond (Nat.beq (Nat.mod q 2) 0)
            (chunk8TreeLookupChunkAt d
              (chunk8TreeModifyAt d .empty (Nat.div chunkIdx 2) rem v)
              (Nat.div q 2))
            (chunk8TreeLookupChunkAt d .empty (Nat.div q 2)) = none
        cases hpq : Nat.beq (Nat.mod q 2) 0 with
        | true =>
          dsimp only [cond]
          rw [ih .empty (Nat.div chunkIdx 2) (Nat.div q 2)
                (hDivNe (hpq.trans hpi.symm)),
              chunk8TreeLookupChunkAt_empty]
        | false =>
          dsimp only [cond]
          exact chunk8TreeLookupChunkAt_empty d (Nat.div q 2)
      | false =>
        dsimp only [cond]
        change cond (Nat.beq (Nat.mod q 2) 0)
            (chunk8TreeLookupChunkAt d .empty (Nat.div q 2))
            (chunk8TreeLookupChunkAt d
              (chunk8TreeModifyAt d .empty (Nat.div chunkIdx 2) rem v)
              (Nat.div q 2)) = none
        cases hpq : Nat.beq (Nat.mod q 2) 0 with
        | true =>
          dsimp only [cond]
          exact chunk8TreeLookupChunkAt_empty d (Nat.div q 2)
        | false =>
          dsimp only [cond]
          rw [ih .empty (Nat.div chunkIdx 2) (Nat.div q 2)
                (hDivNe (hpq.trans hpi.symm)),
              chunk8TreeLookupChunkAt_empty]
    | node l r =>
      change chunk8TreeLookupChunkAt (d + 1)
          (cond (Nat.beq (Nat.mod chunkIdx 2) 0)
            (.node (chunk8TreeModifyAt d l (Nat.div chunkIdx 2) rem v) r)
            (.node l (chunk8TreeModifyAt d r (Nat.div chunkIdx 2) rem v))) q =
        cond (Nat.beq (Nat.mod q 2) 0)
          (chunk8TreeLookupChunkAt d l (Nat.div q 2))
          (chunk8TreeLookupChunkAt d r (Nat.div q 2))
      cases hpi : Nat.beq (Nat.mod chunkIdx 2) 0 with
      | true =>
        dsimp only [cond]
        change cond (Nat.beq (Nat.mod q 2) 0)
            (chunk8TreeLookupChunkAt d
              (chunk8TreeModifyAt d l (Nat.div chunkIdx 2) rem v)
              (Nat.div q 2))
            (chunk8TreeLookupChunkAt d r (Nat.div q 2)) = _
        cases hpq : Nat.beq (Nat.mod q 2) 0 with
        | true =>
          dsimp only [cond]
          exact ih l (Nat.div chunkIdx 2) (Nat.div q 2)
            (hDivNe (hpq.trans hpi.symm))
        | false => rfl
      | false =>
        dsimp only [cond]
        change cond (Nat.beq (Nat.mod q 2) 0)
            (chunk8TreeLookupChunkAt d l (Nat.div q 2))
            (chunk8TreeLookupChunkAt d
              (chunk8TreeModifyAt d r (Nat.div chunkIdx 2) rem v)
              (Nat.div q 2)) = _
        cases hpq : Nat.beq (Nat.mod q 2) 0 with
        | true => rfl
        | false =>
          dsimp only [cond]
          exact ih r (Nat.div chunkIdx 2) (Nat.div q 2)
            (hDivNe (hpq.trans hpi.symm))

/-- Pure-data dense `Chunk8` balanced lookup table (`0` `Prop` fields) unifying
dense block tables, chunked binary trees, and boolean live-local masks. -/
structure Chunk8BlockTree (α : Type) where
  depth : Nat
  tree : Chunk8Tree α

/-- Tabulates `xs` into a `Chunk8BlockTree α` at explicit spine depth `depth`.
-/
@[expose] def Chunk8BlockTree.ofListAt {α : Type} (xs : List α) (depth : Nat) :
    Chunk8BlockTree α :=
  { depth := depth, tree := chunk8TreeFromChunksAt depth (packChunk8 xs) }

/-- Tabulates `xs` into a `Chunk8BlockTree α` at minimal logarithmic spine
depth `compLog2Depth (Nat.div (compListLength xs + 7) 8)`. -/
@[expose] def Chunk8BlockTree.ofList {α : Type} (xs : List α) : Chunk8BlockTree α :=
  let chunks := packChunk8 xs
  { depth := compLog2Depth (compListLength chunks)
    tree := chunk8TreeFromChunksAt (compLog2Depth (compListLength chunks))
      chunks }

/-- Looks up an entire 8-element `Chunk8 α` leaf at `chunkIdx` in one spine
traversal (`O(bt.depth)`), enabling stride-8 batch inspection. -/
@[expose] def Chunk8BlockTree.lookupChunk {α : Type} (bt : Chunk8BlockTree α)
    (chunkIdx : Nat) : Option (Chunk8 α) :=
  chunk8TreeLookupChunkAt bt.depth bt.tree chunkIdx

/-- Looks up element `idx` in `bt` in `O(bt.depth)` spine steps plus one `O(1)`
`Chunk8.get` dispatch. -/
@[expose] def Chunk8BlockTree.lookup {α : Type} (bt : Chunk8BlockTree α) (idx : Nat) :
    Option α :=
  chunk8TreeGetAt bt.depth bt.tree idx

/-- Functionally updates element `idx` in `bt` in `O(bt.depth)` spine steps. -/
@[expose] def Chunk8BlockTree.modify {α : Type} (bt : Chunk8BlockTree α) (idx : Nat)
    (v : Option α) : Chunk8BlockTree α :=
  { depth := bt.depth
    tree := chunk8TreeModifyAt bt.depth bt.tree (Nat.div idx 8)
      (Nat.mod idx 8) v }

/-- Validity predicate tying a pure-data `Chunk8BlockTree α` back to `xs`. -/
@[expose] def ValidChunk8BlockTree {α : Type} (xs : List α) (bt : Chunk8BlockTree α) :
    Prop :=
  xs.length ≤ 8 * pow2 bt.depth ∧
  ∀ idx : Nat, bt.lookup idx = Trusted.MirSemantics.getElem? xs idx

private theorem getElem?_ne_none_of_lt {α : Type} :
    ∀ (xs : List α) (k : Nat),
      k < xs.length → Trusted.MirSemantics.getElem? xs k ≠ none
  | [], _, h => False.elim (Nat.not_lt_zero _ h)
  | _ :: _, 0, _ => fun h => by cases h
  | _ :: tl, k + 1, h => getElem?_ne_none_of_lt tl k (Nat.lt_of_succ_lt_succ h)

/-- `Chunk8BlockTree.ofListAt xs depth` is valid whenever
`(packChunk8 xs).length ≤ pow2 depth`. -/
theorem valid_chunk8BlockTree_ofListAt {α : Type} (xs : List α) (depth : Nat)
    (hChunks : (packChunk8 xs).length ≤ pow2 depth) :
    ValidChunk8BlockTree xs (Chunk8BlockTree.ofListAt xs depth) := by
  have hFuelBound : xs.length ≤ 8 * Nat.div (compListLength xs + 7) 8 := by
    rw [compListLength_eq xs]
    exact nat_le_eight_mul_div_add7 xs.length
  have hLen : xs.length ≤ 8 * pow2 depth := by
    have hPackLe : xs.length ≤ 8 * (packChunk8 xs).length := by
      cases Nat.lt_or_ge (8 * (packChunk8 xs).length) xs.length with
      | inr hle => exact hle
      | inl hlt =>
        have hGet := getElem?_packChunk8Fuel (Nat.div (compListLength xs + 7) 8)
          xs hFuelBound (8 * (packChunk8 xs).length)
        have hDiv : Nat.div (8 * (packChunk8 xs).length) 8 =
            (packChunk8 xs).length := by
          have hMul : Nat.div ((packChunk8 xs).length * 8) 8 =
              (packChunk8 xs).length :=
            Nat.mul_div_cancel (packChunk8 xs).length (Nat.succ_pos 7)
          rw [Nat.mul_comm 8 _]
          exact hMul
        change (match Trusted.MirSemantics.getElem? (packChunk8 xs)
            (Nat.div (8 * (packChunk8 xs).length) 8) with
          | some c => c.get (Nat.mod (8 * (packChunk8 xs).length) 8)
          | none => none) =
          Trusted.MirSemantics.getElem? xs (8 * (packChunk8 xs).length) at hGet
        rw [hDiv, getElem?_eq_none_of_le (packChunk8 xs) _ (Nat.le_refl _)]
          at hGet
        exact False.elim (getElem?_ne_none_of_lt xs _ hlt hGet.symm)
    exact Nat.le_trans hPackLe (Nat.mul_le_mul_left 8 hChunks)
  refine ⟨hLen, fun idx => ?_⟩
  unfold Chunk8BlockTree.lookup Chunk8BlockTree.ofListAt chunk8TreeGetAt
  dsimp only
  rw [chunk8TreeLookupChunkAt_fromChunksAt depth (packChunk8 xs) hChunks
    (Nat.div idx 8)]
  exact getElem?_packChunk8Fuel (Nat.div (compListLength xs + 7) 8) xs
    hFuelBound idx

/-- `Chunk8BlockTree.ofList xs` is unconditionally valid for every `xs`. -/
theorem valid_chunk8BlockTree_ofList {α : Type} (xs : List α) :
    ValidChunk8BlockTree xs (Chunk8BlockTree.ofList xs) := by
  have hChunks :
      (packChunk8 xs).length ≤ pow2 (compLog2Depth (compListLength (packChunk8 xs))) := by
    rw [compListLength_eq (packChunk8 xs)]
    exact le_pow2_compLog2Depth (packChunk8 xs).length
  exact valid_chunk8BlockTree_ofListAt xs
    (compLog2Depth (compListLength (packChunk8 xs))) hChunks

/-- Premise-free lookup equivalence for `Chunk8BlockTree.ofList xs`. -/
theorem Chunk8BlockTree.ofList_lookup_eq {α : Type} (xs : List α) (idx : Nat) :
    (Chunk8BlockTree.ofList xs).lookup idx =
      Trusted.MirSemantics.getElem? xs idx :=
  (valid_chunk8BlockTree_ofList xs).2 idx

/-- Spine height bound for `Chunk8BlockTree.ofList xs`:
`(Chunk8BlockTree.ofList xs).tree.heightAt fuel ≤ depth + 1` for every `fuel`.
-/
theorem Chunk8BlockTree.ofList_height_le {α : Type} (xs : List α) (fuel : Nat) :
    (Chunk8BlockTree.ofList xs).tree.heightAt fuel ≤
      (Chunk8BlockTree.ofList xs).depth + 1 :=
  chunk8TreeFromChunksAt_height_le fuel _ (packChunk8 xs)

/-- Same-index read-after-modify law for `Chunk8BlockTree.modify`
(`idx < 8 * pow2 bt.depth`). -/
theorem Chunk8BlockTree.lookup_modify_same {α : Type}
    (bt : Chunk8BlockTree α) (idx : Nat) (v : Option α)
    (hidx : idx < 8 * pow2 bt.depth) :
    (bt.modify idx v).lookup idx = v := by
  have hc : Nat.div idx 8 < pow2 bt.depth := by
    rw [Nat.mul_comm 8 (pow2 bt.depth)] at hidx
    exact (Nat.div_lt_iff_lt_mul (Nat.succ_pos 7)).mpr hidx
  unfold Chunk8BlockTree.lookup Chunk8BlockTree.modify chunk8TreeGetAt
  dsimp only
  rw [chunk8TreeLookupChunkAt_modify_same bt.depth bt.tree (Nat.div idx 8)
    (Nat.mod idx 8) v hc]
  exact Chunk8.get_set_same _ v (Nat.mod_lt idx (Nat.succ_pos 7))

/-- Distinct-index frame law for `Chunk8BlockTree.modify` (`j ≠ idx`). -/
theorem Chunk8BlockTree.lookup_modify_ne {α : Type}
    (bt : Chunk8BlockTree α) (idx j : Nat) (v : Option α) (hNe : j ≠ idx) :
    (bt.modify idx v).lookup j = bt.lookup j := by
  unfold Chunk8BlockTree.lookup Chunk8BlockTree.modify chunk8TreeGetAt
  dsimp only
  cases hq : Nat.beq (Nat.div j 8) (Nat.div idx 8) with
  | false =>
    have hqNe : Nat.div j 8 ≠ Nat.div idx 8 := fun hEq => by
      rw [hEq, natBeq_refl] at hq
      exact boolFalseNeTrue hq.symm
    rw [chunk8TreeLookupChunkAt_modify_ne bt.depth bt.tree (Nat.div idx 8)
      (Nat.div j 8) (Nat.mod idx 8) v hqNe]
  | true =>
    have hqEq : Nat.div j 8 = Nat.div idx 8 := natEq_of_beq _ _ hq
    have hrNe : Nat.mod j 8 ≠ Nat.mod idx 8 := fun hrEq => by
      have hj : 8 * Nat.div j 8 + Nat.mod j 8 = j := Nat.div_add_mod j 8
      have hi : 8 * Nat.div idx 8 + Nat.mod idx 8 = idx := Nat.div_add_mod idx 8
      rw [hqEq, hrEq, hi] at hj
      exact hNe hj.symm
    cases Nat.lt_or_ge (Nat.div idx 8) (pow2 bt.depth) with
    | inl hc =>
      rw [hqEq,
        chunk8TreeLookupChunkAt_modify_same bt.depth bt.tree (Nat.div idx 8)
          (Nat.mod idx 8) v hc]
      dsimp only
      rw [Chunk8.get_set_ne _ v hrNe]
      cases chunk8TreeLookupChunkAt bt.depth bt.tree (Nat.div idx 8) with
      | some _ => rfl
      | none => exact Chunk8.get_empty (Nat.mod j 8)
    | inr hge =>
      -- Out-of-bounds chunks beyond `pow2 bt.depth` evaluate to `none`.
      have hModOob :
          ∀ (d : Nat) (t : Chunk8Tree α) (ci r : Nat),
            pow2 d ≤ ci →
            chunk8TreeLookupChunkAt d (chunk8TreeModifyAt d t ci r v) ci =
              chunk8TreeLookupChunkAt d t ci := by
        intro d
        induction d with
        | zero =>
          intro t ci r hOob
          rw [pow2_zero] at hOob
          cases ci with
          | zero => exact False.elim (Nat.not_lt_of_ge hOob Nat.zero_lt_one)
          | succ _ => rfl
        | succ d' ih =>
          intro t ci r hOob
          rw [pow2_succ, Nat.mul_comm 2 (pow2 d')] at hOob
          have hhalf : pow2 d' ≤ Nat.div ci 2 :=
            (Nat.le_div_iff_mul_le (Nat.succ_pos 1)).mpr hOob
          cases t with
          | empty | leaf _ =>
            change chunk8TreeLookupChunkAt (d' + 1)
                (cond (Nat.beq (Nat.mod ci 2) 0)
                  (.node (chunk8TreeModifyAt d' .empty (Nat.div ci 2) r v)
                    .empty)
                  (.node .empty
                    (chunk8TreeModifyAt d' .empty (Nat.div ci 2) r v))) ci =
              none
            cases hpar : Nat.beq (Nat.mod ci 2) 0 with
            | true =>
              dsimp only [cond]
              change cond (Nat.beq (Nat.mod ci 2) 0)
                  (chunk8TreeLookupChunkAt d'
                    (chunk8TreeModifyAt d' .empty (Nat.div ci 2) r v)
                    (Nat.div ci 2))
                  (chunk8TreeLookupChunkAt d' .empty (Nat.div ci 2)) = none
              rw [hpar]
              dsimp only [cond]
              rw [ih .empty (Nat.div ci 2) r hhalf,
                chunk8TreeLookupChunkAt_empty]
            | false =>
              dsimp only [cond]
              change cond (Nat.beq (Nat.mod ci 2) 0)
                  (chunk8TreeLookupChunkAt d' .empty (Nat.div ci 2))
                  (chunk8TreeLookupChunkAt d'
                    (chunk8TreeModifyAt d' .empty (Nat.div ci 2) r v)
                    (Nat.div ci 2)) = none
              rw [hpar]
              dsimp only [cond]
              rw [ih .empty (Nat.div ci 2) r hhalf,
                chunk8TreeLookupChunkAt_empty]
          | node l r0 =>
            change chunk8TreeLookupChunkAt (d' + 1)
                (cond (Nat.beq (Nat.mod ci 2) 0)
                  (.node (chunk8TreeModifyAt d' l (Nat.div ci 2) r v) r0)
                  (.node l (chunk8TreeModifyAt d' r0 (Nat.div ci 2) r v))) ci =
              cond (Nat.beq (Nat.mod ci 2) 0)
                (chunk8TreeLookupChunkAt d' l (Nat.div ci 2))
                (chunk8TreeLookupChunkAt d' r0 (Nat.div ci 2))
            cases hpar : Nat.beq (Nat.mod ci 2) 0 with
            | true =>
              dsimp only [cond]
              change cond (Nat.beq (Nat.mod ci 2) 0)
                  (chunk8TreeLookupChunkAt d'
                    (chunk8TreeModifyAt d' l (Nat.div ci 2) r v) (Nat.div ci 2))
                  (chunk8TreeLookupChunkAt d' r0 (Nat.div ci 2)) = _
              rw [hpar]
              dsimp only [cond]
              exact ih l (Nat.div ci 2) r hhalf
            | false =>
              dsimp only [cond]
              change cond (Nat.beq (Nat.mod ci 2) 0)
                  (chunk8TreeLookupChunkAt d' l (Nat.div ci 2))
                  (chunk8TreeLookupChunkAt d'
                    (chunk8TreeModifyAt d' r0 (Nat.div ci 2) r v) (Nat.div ci 2)) = _
              rw [hpar]
              dsimp only [cond]
              exact ih r0 (Nat.div ci 2) r hhalf
      rw [hqEq, hModOob bt.depth bt.tree (Nat.div idx 8) (Nat.mod idx 8) hge]

/-- `Chunk8BlockTree.modify idx (some val)` preserves `ValidChunk8BlockTree`
across `Trusted.MirSemantics.setElem?`. -/
theorem Chunk8BlockTree.valid_modify_of_setElem? {α : Type} {xs xs' : List α}
    {bt : Chunk8BlockTree α} {idx : Nat} {val : α}
    (hValid : ValidChunk8BlockTree xs bt)
    (hSet : Trusted.MirSemantics.setElem? xs idx val = some xs') :
    ValidChunk8BlockTree xs' (bt.modify idx (some val)) := by
  have hLtLen := setElem?_lt_and_length hSet
  have hIdxBound : idx < 8 * pow2 bt.depth :=
    Nat.lt_of_lt_of_le hLtLen.1 hValid.1
  refine ⟨?_, fun j => ?_⟩
  · unfold Chunk8BlockTree.modify
    dsimp only
    rw [hLtLen.2]
    exact hValid.1
  · cases hBeq : Nat.beq j idx with
    | true =>
      have hEq : j = idx := natEq_of_beq j idx hBeq
      subst hEq
      rw [Chunk8BlockTree.lookup_modify_same bt j (some val) hIdxBound,
        bt_getElem?_setElem?_same hSet]
    | false =>
      have hNe : j ≠ idx := fun hEq => by
        subst hEq
        rw [natBeq_refl j] at hBeq
        exact boolFalseNeTrue hBeq.symm
      rw [Chunk8BlockTree.lookup_modify_ne bt idx j (some val) hNe,
        hValid.2 j, bt_getElem?_setElem?_ne hNe hSet]

/-- Dense boolean mask table unified onto `Chunk8BlockTree Bool` (subsuming
standalone radix-8 `MaskTree` implementations). -/
abbrev MaskTree : Type := Chunk8BlockTree Bool

/-- Builds a `MaskTree` from a boolean list. -/
@[expose] def MaskTree.ofList (xs : List Bool) : MaskTree :=
  Chunk8BlockTree.ofList xs

/-- Looks up boolean mask bit `idx` (`false` when out of bounds). -/
@[expose] def MaskTree.get (mt : MaskTree) (idx : Nat) : Bool :=
  match mt.lookup idx with
  | some b => b
  | none => false

/-- Exact lookup equivalence for `MaskTree.ofList`. -/
theorem MaskTree.get_ofList (xs : List Bool) (idx : Nat) :
    (MaskTree.ofList xs).get idx =
      match Trusted.MirSemantics.getElem? xs idx with
      | some b => b
      | none => false := by
  unfold MaskTree.get MaskTree.ofList
  rw [Chunk8BlockTree.ofList_lookup_eq xs idx]

/-- Single-body MIR step evaluator (`0` `noncomputable`) indexing basic blocks
via `Chunk8BlockTree BasicBlock`. -/
@[expose] def evalMirStepChunk8By (tyEq : MirTy → MirTy → Bool)
    (bt : Chunk8BlockTree BasicBlock) (body : Body) (s : State) :
    StepResult State TerminalOut :=
  match s.frames with
  | [frame] =>
    match frame.sysrootOp? with
    | some _ => evalMirStepBy tyEq (Anneal.MirWp.bodyProg body) 0 s
    | none =>
      if !Nat.beq frame.defId 0 then .fault .unsupported
      else
        match bt.lookup frame.blockIdx with
        | none => .fault .unsupported
        | some bb =>
          match compGetElem? bb.statements frame.stmtIdx with
          | some stmt => evalStatementBy tyEq body frame s.mem s.callerMem stmt
          | none =>
            if Nat.beq frame.stmtIdx bb.statements.length then
              match bb.terminator with
              | .call _ _ _ _ _ | .sysrootCall _ _ _ _ _ =>
                evalMirStepBy tyEq (Anneal.MirWp.bodyProg body) 0 s
              | _ => evalTerminatorComp body bb frame s.mem s.callerMem
            else
              .fault .unsupported
  | _ :: _ :: _ => evalMirStepBy tyEq (Anneal.MirWp.bodyProg body) 0 s
  | [] => .fault .unsupported

/-- Agreement between `evalMirStepChunk8By` and
`Trusted.MirSemantics.evalStep (Anneal.MirWp.bodyProg body) 0` for any valid
`Chunk8BlockTree BasicBlock`. -/
theorem evalMirStepChunk8By_eq_evalStep (tyEq : MirTy → MirTy → Bool)
    (hTyEq : ∀ a b, tyEq a b = MirTy.beq a b)
    {body : Body} {bt : Chunk8BlockTree BasicBlock}
    (hValid : ValidChunk8BlockTree body.basicBlocks bt) (s : State) :
    evalMirStepChunk8By tyEq bt body s =
      evalStep (Anneal.MirWp.bodyProg body) 0 s := by
  have hMir : evalMirStepChunk8By tyEq bt body s =
      evalMirStepBy tyEq (Anneal.MirWp.bodyProg body) 0 s :=
    evalMirStepIndexed_eq_evalMirStepBy tyEq body bt.lookup
      (fun idx => (hValid.2 idx).trans (compGetElem?_eq _ _).symm) s
  rw [hMir]
  exact evalMirStepBy_eq tyEq hTyEq (Anneal.MirWp.bodyProg body) 0 s

private theorem compLog2DepthGo_le_of_le (n : Nat) :
    ∀ (fuel depth cap bound : Nat),
      n ≤ cap * pow2 bound →
      compLog2DepthGo n fuel depth cap ≤ depth + bound
  | 0, depth, _, bound, _ => Nat.le_add_right depth bound
  | k + 1, depth, cap, 0, hCap => by
    rw [pow2_zero, Nat.mul_one] at hCap
    change (if Nat.ble n cap then depth
      else compLog2DepthGo n k (depth + 1) (2 * cap)) ≤ depth + 0
    rw [Nat.ble_eq_true_of_le hCap, ite_bool_true rfl, Nat.add_zero]
    exact Nat.le_refl depth
  | k + 1, depth, cap, bound + 1, hCap => by
    change (if Nat.ble n cap then depth
      else compLog2DepthGo n k (depth + 1) (2 * cap)) ≤ depth + (bound + 1)
    cases hble : Nat.ble n cap with
    | true =>
      rw [ite_bool_true rfl]
      exact Nat.le_add_right depth (bound + 1)
    | false =>
      rw [ite_bool_false rfl]
      have hCap' : n ≤ (2 * cap) * pow2 bound := by
        rw [pow2_succ] at hCap
        rw [Nat.mul_comm 2 cap, Nat.mul_assoc cap 2 (pow2 bound)]
        exact hCap
      have hRec := compLog2DepthGo_le_of_le n k (depth + 1) (2 * cap) bound hCap'
      rw [Nat.succ_add, ← Nat.add_succ] at hRec
      exact hRec

/-- Logarithmic upper bound: `n ≤ pow2 bound → compLog2Depth n ≤ bound`. -/
theorem compLog2Depth_le_of_le_pow2 {n bound : Nat} (h : n ≤ pow2 bound) :
    compLog2Depth n ≤ bound := by
  have h1 : n ≤ 1 * pow2 bound := by
    rw [Nat.one_mul]
    exact h
  have h0 := compLog2DepthGo_le_of_le n n 0 1 bound h1
  rw [Nat.zero_add] at h0
  exact h0

/-- For any list of length `≤ 4,096`, `Chunk8BlockTree.ofList xs` has spine
depth `≤ 9` and tree height `≤ 10` (`≤ 11` including the `Chunk8` leaf payload)
at every fuel budget `fuel`. -/
theorem Chunk8BlockTree.ofList_height_le_10_of_le_4096 {α : Type}
    (xs : List α) (hLen : xs.length ≤ 4096) (fuel : Nat) :
    (Chunk8BlockTree.ofList xs).depth ≤ 9 ∧
    (Chunk8BlockTree.ofList xs).tree.heightAt fuel ≤ 10 := by
  have hDiv : Nat.div (xs.length + 7) 8 ≤ 512 := by
    have hLt : xs.length + 7 < 513 * 8 :=
      Nat.lt_of_le_of_lt (Nat.add_le_add_right hLen 7) (by decide)
    have hDivLt : Nat.div (xs.length + 7) 8 < 513 :=
      (Nat.div_lt_iff_lt_mul (Nat.succ_pos 7)).mpr hLt
    exact Nat.le_of_lt_succ hDivLt
  have hChunks : (packChunk8 xs).length ≤ pow2 9 := by
    unfold packChunk8
    have hp := packChunk8Fuel_length_le (Nat.div (compListLength xs + 7) 8) xs
    rw [compListLength_eq xs] at hp
    rw [compListLength_eq xs]
    exact Nat.le_trans hp hDiv
  have hDepth : (Chunk8BlockTree.ofList xs).depth ≤ 9 := by
    unfold Chunk8BlockTree.ofList
    dsimp only
    rw [compListLength_eq (packChunk8 xs)]
    exact compLog2Depth_le_of_le_pow2 hChunks
  have hHeight : (Chunk8BlockTree.ofList xs).tree.heightAt fuel ≤ 10 :=
    Nat.le_trans (Chunk8BlockTree.ofList_height_le xs fuel)
      (Nat.succ_le_succ hDepth)
  exact ⟨hDepth, hHeight⟩

/-- Concrete spine-depth check at `N = 4,096` (`depth = 9`) and `N = 256`
(`depth = 5`). -/
theorem chunk8_depth_4096_canary :
    compLog2Depth (Nat.div (4096 + 7) 8) = 9 ∧
    compLog2Depth (Nat.div (256 + 7) 8) = 5 :=
  ⟨rfl, rfl⟩

@[expose] def mkChunk8Range : Nat → Nat → List Nat :=
  @Nat.rec (fun _ => Nat → List Nat)
    (fun _ => [])
    (fun _ ih start => start :: ih (start + 1))

/-- Top-down strided tabulation directly into a `Chunk8Tree α` (`O(depth)` WHNF
path forcing on surgical lookups, avoiding intermediate `List` construction). -/
@[expose] def chunk8TreeTabulateAt {α : Type} (depth : Nat) :
    Nat → Nat → (Nat → Option α) → Chunk8Tree α :=
  @Nat.rec (fun _ => Nat → Nat → (Nat → Option α) → Chunk8Tree α)
    (fun chunkOff _ f =>
      let b := 8 * chunkOff
      .leaf ⟨f b, f (b + 1), f (b + 2), f (b + 3),
             f (b + 4), f (b + 5), f (b + 6), f (b + 7)⟩)
    (fun _ ih chunkOff step f =>
      .node (ih chunkOff (2 * step) f) (ih (chunkOff + step) (2 * step) f))
    depth

/-- Top-down `Chunk8BlockTree α` tabulation covering indices `0 .. 8*2^depth-1`
in spine depth `depth` (`depth = 5` covers `256` elements; `depth = 9` covers
`4,096` elements with tree height `10 ≤ 11`). -/
@[expose] def Chunk8BlockTree.tabulate {α : Type} (depth : Nat) (f : Nat → Option α) :
    Chunk8BlockTree α :=
  { depth := depth, tree := chunk8TreeTabulateAt depth 0 1 f }

private theorem chunk8TreeLookupChunkAt_tabulateAt_in {α : Type}
    (depth chunkIdx chunkOff step : Nat) (f : Nat → Option α)
    (hc : chunkIdx < pow2 depth) :
    chunk8TreeLookupChunkAt depth
        (chunk8TreeTabulateAt depth chunkOff step f) chunkIdx =
      let b := 8 * (chunkOff + step * chunkIdx)
      some ⟨f b, f (b + 1), f (b + 2), f (b + 3),
            f (b + 4), f (b + 5), f (b + 6), f (b + 7)⟩ := by
  revert chunkIdx chunkOff step
  induction depth with
  | zero =>
    intro chunkIdx chunkOff step hc
    rw [pow2_zero] at hc
    have h0 : chunkIdx = 0 := Nat.eq_zero_of_le_zero (Nat.le_of_lt_succ hc)
    rw [h0, Nat.mul_zero, Nat.add_zero]
    rfl
  | succ d ih =>
    intro chunkIdx chunkOff step hc
    rw [pow2_succ, Nat.mul_comm 2 (pow2 d)] at hc
    have hhalf : Nat.div chunkIdx 2 < pow2 d :=
      (Nat.div_lt_iff_lt_mul (Nat.succ_pos 1)).mpr hc
    change cond (Nat.beq (Nat.mod chunkIdx 2) 0)
        (chunk8TreeLookupChunkAt d
          (chunk8TreeTabulateAt d chunkOff (2 * step) f) (Nat.div chunkIdx 2))
        (chunk8TreeLookupChunkAt d
          (chunk8TreeTabulateAt d (chunkOff + step) (2 * step) f)
          (Nat.div chunkIdx 2)) = _
    have hde := nat_div2_decomp chunkIdx
    cases hbeq : Nat.beq (Nat.mod chunkIdx 2) 0 with
    | true =>
      rw [hbeq] at hde
      change 2 * Nat.div chunkIdx 2 = chunkIdx at hde
      dsimp only [cond]
      rw [ih (Nat.div chunkIdx 2) chunkOff (2 * step) hhalf]
      have hmul : (2 * step) * Nat.div chunkIdx 2 = step * chunkIdx := by
        rw [Nat.mul_comm 2 step, Nat.mul_assoc step 2 (Nat.div chunkIdx 2), hde]
      rw [hmul]
    | false =>
      rw [hbeq] at hde
      change 2 * Nat.div chunkIdx 2 + 1 = chunkIdx at hde
      dsimp only [cond]
      rw [ih (Nat.div chunkIdx 2) (chunkOff + step) (2 * step) hhalf]
      have harith :
          (chunkOff + step) + (2 * step) * Nat.div chunkIdx 2 =
            chunkOff + step * chunkIdx := by
        rw [Nat.mul_comm 2 step, Nat.mul_assoc step 2 (Nat.div chunkIdx 2),
          Nat.add_assoc chunkOff step (step * (2 * Nat.div chunkIdx 2))]
        have hs1 :
            step + step * (2 * Nat.div chunkIdx 2) =
              step * (2 * Nat.div chunkIdx 2 + 1) := by
          rw [Nat.mul_add, Nat.mul_one, Nat.add_comm]
        rw [hs1, hde]
      rw [harith]

private theorem chunk8TreeLookupChunkAt_tabulateAt_oob {α : Type}
    (depth chunkIdx chunkOff step : Nat) (f : Nat → Option α)
    (hoob : pow2 depth ≤ chunkIdx) :
    chunk8TreeLookupChunkAt depth
        (chunk8TreeTabulateAt depth chunkOff step f) chunkIdx = none := by
  revert chunkIdx chunkOff step
  induction depth with
  | zero =>
    intro chunkIdx _ _ hoob
    rw [pow2_zero] at hoob
    cases chunkIdx with
    | zero => exact False.elim (Nat.not_lt_of_ge hoob Nat.zero_lt_one)
    | succ _ => rfl
  | succ d ih =>
    intro chunkIdx chunkOff step hoob
    rw [pow2_succ, Nat.mul_comm 2 (pow2 d)] at hoob
    have hhalf : pow2 d ≤ Nat.div chunkIdx 2 :=
      (Nat.le_div_iff_mul_le (Nat.succ_pos 1)).mpr hoob
    change cond (Nat.beq (Nat.mod chunkIdx 2) 0)
        (chunk8TreeLookupChunkAt d
          (chunk8TreeTabulateAt d chunkOff (2 * step) f) (Nat.div chunkIdx 2))
        (chunk8TreeLookupChunkAt d
          (chunk8TreeTabulateAt d (chunkOff + step) (2 * step) f)
          (Nat.div chunkIdx 2)) = none
    cases Nat.beq (Nat.mod chunkIdx 2) 0 with
    | true =>
      dsimp only [cond]
      exact ih (Nat.div chunkIdx 2) chunkOff (2 * step) hhalf
    | false =>
      dsimp only [cond]
      exact ih (Nat.div chunkIdx 2) (chunkOff + step) (2 * step) hhalf

/-- Exact in-bounds lookup law for `Chunk8BlockTree.tabulate depth f`
(`idx < 8 * pow2 depth`). -/
theorem Chunk8BlockTree.lookup_tabulate_in {α : Type} (depth : Nat)
    (f : Nat → Option α) {idx : Nat} (hidx : idx < 8 * pow2 depth) :
    (Chunk8BlockTree.tabulate depth f).lookup idx = f idx := by
  have hc : Nat.div idx 8 < pow2 depth := by
    rw [Nat.mul_comm 8 (pow2 depth)] at hidx
    exact (Nat.div_lt_iff_lt_mul (Nat.succ_pos 7)).mpr hidx
  unfold Chunk8BlockTree.lookup Chunk8BlockTree.tabulate chunk8TreeGetAt
  dsimp only
  rw [chunk8TreeLookupChunkAt_tabulateAt_in depth (Nat.div idx 8) 0 1 f hc]
  dsimp only
  rw [Nat.one_mul, Nat.zero_add]
  have hde : 8 * Nat.div idx 8 + Nat.mod idx 8 = idx := Nat.div_add_mod idx 8
  have hr : Nat.mod idx 8 < 8 := Nat.mod_lt idx (Nat.succ_pos 7)
  cases hm : Nat.mod idx 8 with
  | zero =>
    rw [hm, Nat.add_zero] at hde
    dsimp only [Chunk8.get]
    exact congrArg f hde
  | succ r1 =>
    cases r1 with
    | zero =>
      rw [hm] at hde
      dsimp only [Chunk8.get]
      exact congrArg f hde
    | succ r2 =>
      cases r2 with
      | zero =>
        rw [hm] at hde
        dsimp only [Chunk8.get]
        exact congrArg f hde
      | succ r3 =>
        cases r3 with
        | zero =>
          rw [hm] at hde
          dsimp only [Chunk8.get]
          exact congrArg f hde
        | succ r4 =>
          cases r4 with
          | zero =>
            rw [hm] at hde
            dsimp only [Chunk8.get]
            exact congrArg f hde
          | succ r5 =>
            cases r5 with
            | zero =>
              rw [hm] at hde
              dsimp only [Chunk8.get]
              exact congrArg f hde
            | succ r6 =>
              cases r6 with
              | zero =>
                rw [hm] at hde
                dsimp only [Chunk8.get]
                exact congrArg f hde
              | succ r7 =>
                cases r7 with
                | zero =>
                  rw [hm] at hde
                  dsimp only [Chunk8.get]
                  exact congrArg f hde
                | succ r8 =>
                  rw [hm] at hr
                  exact False.elim (nat_ge8_contra hr)

/-- Exact out-of-bounds lookup law for `Chunk8BlockTree.tabulate depth f`
(`8 * pow2 depth ≤ idx`). -/
theorem Chunk8BlockTree.lookup_tabulate_oob {α : Type} (depth : Nat)
    (f : Nat → Option α) {idx : Nat} (hoob : 8 * pow2 depth ≤ idx) :
    (Chunk8BlockTree.tabulate depth f).lookup idx = none := by
  have hc : pow2 depth ≤ Nat.div idx 8 := by
    rw [Nat.mul_comm 8 (pow2 depth)] at hoob
    exact (Nat.le_div_iff_mul_le (Nat.succ_pos 7)).mpr hoob
  unfold Chunk8BlockTree.lookup Chunk8BlockTree.tabulate chunk8TreeGetAt
  dsimp only
  rw [chunk8TreeLookupChunkAt_tabulateAt_oob depth (Nat.div idx 8) 0 1 f hc]

/-- Exact height of `Chunk8BlockTree.tabulate depth f` at fuel `depth + 1`
equals `depth + 1` (so `depth = 9` for `4,096` elements has height `10 ≤ 11`).
-/
theorem Chunk8BlockTree.tabulate_height {α : Type} (depth : Nat)
    (f : Nat → Option α) :
    (Chunk8BlockTree.tabulate depth f).tree.heightAt (depth + 1) = depth + 1 := by
  unfold Chunk8BlockTree.tabulate
  dsimp only
  have hAt :
      ∀ (d off step : Nat),
        (chunk8TreeTabulateAt d off step f).heightAt (d + 1) = d + 1 := by
    intro d
    induction d with
    | zero => intro _ _; rfl
    | succ d' ih =>
      intro off step
      change natMax2
          ((chunk8TreeTabulateAt d' off (2 * step) f).heightAt (d' + 1))
          ((chunk8TreeTabulateAt d' (off + step) (2 * step) f).heightAt (d' + 1)) + 1 =
        (d' + 1) + 1
      rw [ih off (2 * step), ih (off + step) (2 * step)]
      unfold natMax2
      cases Nat.ble (d' + 1) (d' + 1) <;> rfl
  exact hAt depth 0 1

/-- 256-element and 4,096-element `Chunk8BlockTree.tabulate` plus 128-element
`Chunk8BlockTree.ofList` and `MaskTree` scaling canaries discharged by `rfl`
under default elaborator options. -/
theorem chunk8BlockTree_scaling_canary :
    let bt256 := Chunk8BlockTree.tabulate 5 (fun i => some i)
    let bt4096 := Chunk8BlockTree.tabulate 9 (fun i => some i)
    let bt128 := Chunk8BlockTree.ofList (mkChunk8Range 128 0)
    let mt := MaskTree.ofList [true, false, true, true, false, false, false, false, true]
    bt256.depth = 5 ∧
    bt256.lookup 0 = some 0 ∧
    bt256.lookup 127 = some 127 ∧
    bt256.lookup 255 = some 255 ∧
    bt256.lookup 256 = none ∧
    (bt256.modify 200 (some 999)).lookup 200 = some 999 ∧
    (bt256.modify 200 (some 999)).lookup 199 = some 199 ∧
    bt4096.depth = 9 ∧
    bt4096.lookup 0 = some 0 ∧
    bt4096.lookup 2048 = some 2048 ∧
    bt4096.lookup 4095 = some 4095 ∧
    bt4096.lookup 4096 = none ∧
    bt128.depth = 4 ∧
    bt128.lookup 0 = some 0 ∧
    bt128.lookup 127 = some 127 ∧
    bt128.lookup 128 = none ∧
    mt.get 0 = true ∧
    mt.get 1 = false ∧
    mt.get 8 = true ∧
    mt.get 9 = false :=
  ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl,
   rfl, rfl, rfl, rfl, rfl⟩

end Anneal.Core

end
