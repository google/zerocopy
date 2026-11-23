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
public import Anneal.MirTotal.Ops

public section
namespace Anneal.ByteSubLens

open Trusted.MirAst Trusted.MirSemantics Anneal.MirTotal

/-!
# Lawful Sub-Allocation Byte Lenses Over `MemoryState` (`ByteSubLens.Lens`)

Provides an LCNF-computable (`0` `noncomputable`, `0` `._unsafe_rec`),
zero-axiom (`[]`) partial byte-slice lens algebra directly over
`Trusted.MirSemantics.MemoryState`:

1. **`ByteSubLens` (`byteSubLensGet`, `byteSubLensPut`):** Focuses on a positive
   mutable aligned sub-slice `[offset, offset + size)` inside `allocId` via
   `Anneal.MirTotal` mirrors (`findAllocationComp`, `readBytesComp`,
   `writeBytesComp`), with unconditional equational bridges
   (`byteSubLensGet_eq_mir`, `byteSubLensPut_eq_mir`) to
   `Trusted.MirSemantics.{findAllocation, readBytes, writeBytes}`.
2. **`LawfulByteSubLens` (`byteSubLens_lawful`):** Proves `get_put`, `put_get`,
   `put_put`, and `get_put_disjoint` across all `MemoryState`s with zero axioms
   (`[]`) and without requiring duplicate-free allocation lists.
3. **Hierarchical containment & split-borrow disjointness (`subLensContained`,
   `byteLensDisjoint_of_contained`):** Proves reflexivity, transitivity,
   symmetry, and disjointness inheritance for nested struct/array sub-slices.
4. **Fail-closed boundary rejections:** Proves `= none` on zero-sized,
   `.shared`, deallocated (`live = false`), out-of-bounds, unaligned, and
   length-mismatched operations.
-/

/-! ## 1. Constructive `Bool`, `Nat`, `List` Slice, and Allocation Helpers -/

private theorem boolFalseNeTrue (h : false = true) : False :=
  Bool.noConfusion h

private theorem boolTrueNeFalse (h : true = false) : False :=
  Bool.noConfusion h

private theorem bandLeft {a b : Bool} (h : (a && b) = true) : a = true := by
  cases a with
  | false => exact False.elim (boolFalseNeTrue h)
  | true => rfl

private theorem bandRight {a b : Bool} (h : (a && b) = true) : b = true := by
  cases a with
  | false => exact False.elim (boolFalseNeTrue h)
  | true => exact h

private theorem bandIntro {a b : Bool} (ha : a = true) (hb : b = true) :
    (a && b) = true := by
  rw [ha, hb]
  rfl

private theorem borComm (a b : Bool) : (a || b) = (b || a) := by
  cases a <;> cases b <;> rfl

private theorem borFalseElim {a b : Bool} (h : (a || b) = false) :
    a = false ∧ b = false := by
  cases a with
  | true => exact False.elim (boolTrueNeFalse h)
  | false => exact ⟨rfl, h⟩

private theorem ite_bool_true {α : Type} {b : Bool} {t e : α}
    (hb : b = true) : (if b then t else e) = t := by
  subst hb
  rfl

private theorem ite_bool_false {α : Type} {b : Bool} {t e : α}
    (hb : b = false) : (if b then t else e) = e := by
  subst hb
  rfl

private theorem natBeq_refl (a : Nat) : Nat.beq a a = true := by
  induction a with
  | zero => rfl
  | succ _ ih => exact ih

private theorem natBeq_symm (a b : Nat) : Nat.beq a b = Nat.beq b a := by
  revert b
  induction a with
  | zero =>
    intro b
    cases b <;> rfl
  | succ _ ih =>
    intro b
    cases b with
    | zero => rfl
    | succ b' => exact ih b'

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

private theorem natBeq_of_eq (a b : Nat) (h : a = b) : Nat.beq a b = true := by
  subst h
  exact natBeq_refl a

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

private theorem natBle_trans (a b c : Nat) (h1 : Nat.ble a b = true)
    (h2 : Nat.ble b c = true) : Nat.ble a c = true := by
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

private theorem natBle_add_right (a b : Nat) : Nat.ble a (a + b) = true := by
  induction b with
  | zero => exact natBle_refl a
  | succ _ ih => exact natBle_succ_right a _ ih

private theorem natBeq_zero_false_of_blt_zero (n : Nat)
    (h : Nat.blt 0 n = true) : Nat.beq n 0 = false := by
  cases n with
  | zero => exact False.elim (boolFalseNeTrue h)
  | succ _ => rfl

private theorem listAppend_assoc {α : Type} (xs ys zs : List α) :
    (xs ++ ys) ++ zs = xs ++ (ys ++ zs) := by
  induction xs with
  | nil => rfl
  | cons hd _ ih => exact congrArg (List.cons hd) ih

private theorem listLength_append {α : Type} (xs ys : List α) :
    (xs ++ ys).length = xs.length + ys.length := by
  induction xs with
  | nil => exact (natAdd_zero_left ys.length).symm
  | cons _ tl ih =>
    change (tl ++ ys).length + 1 = (tl.length + 1) + ys.length
    rw [ih, natAdd_succ_left]

private theorem listDrop_nil {α : Type} (n : Nat) :
    List.drop n ([] : List α) = [] := by
  cases n <;> rfl

private theorem listTake_length_of_ble {α : Type} (n : Nat) (xs : List α)
    (h : Nat.ble n xs.length = true) : (xs.take n).length = n := by
  revert xs
  induction n with
  | zero => intro _ _; rfl
  | succ n' ih =>
    intro xs h
    cases xs with
    | nil => exact False.elim (boolFalseNeTrue h)
    | cons _ tl =>
      change (tl.take n').length + 1 = n' + 1
      exact congrArg Nat.succ (ih tl h)

private theorem listDrop_add {α : Type} (a b : Nat) (xs : List α) :
    xs.drop (a + b) = (xs.drop a).drop b := by
  rw [natAdd_comm a b]
  revert xs
  induction a with
  | zero => intro _; rfl
  | succ a' ih =>
    intro xs
    cases xs with
    | nil =>
      rw [listDrop_nil (b + (a' + 1)), listDrop_nil (a' + 1), listDrop_nil b]
    | cons _ tl =>
      change tl.drop (b + a') = (tl.drop a').drop b
      exact ih tl

private theorem listTake_append_drop {α : Type} (n : Nat) (xs : List α) :
    xs.take n ++ xs.drop n = xs := by
  revert xs
  induction n with
  | zero => intro _; rfl
  | succ n' ih =>
    intro xs
    cases xs with
    | nil => rfl
    | cons hd tl =>
      change hd :: (tl.take n' ++ tl.drop n') = hd :: tl
      exact congrArg (List.cons hd) (ih tl)

private theorem listSplice_self {α : Type} (off sz : Nat) (xs : List α) :
    xs.take off ++ (xs.drop off).take sz ++ xs.drop (off + sz) = xs := by
  rw [listAppend_assoc, listDrop_add off sz xs,
      listTake_append_drop sz (xs.drop off)]
  exact listTake_append_drop off xs

private theorem listDrop_take_length_of_ble {α : Type} (off sz : Nat)
    (xs : List α) (h : Nat.ble (off + sz) xs.length = true) :
    ((xs.drop off).take sz).length = sz := by
  revert xs
  induction off with
  | zero =>
    intro xs h
    rw [natAdd_zero_left] at h
    exact listTake_length_of_ble sz xs h
  | succ off' ih =>
    intro xs h
    cases xs with
    | nil =>
      rw [natAdd_succ_left] at h
      exact False.elim (boolFalseNeTrue h)
    | cons _ tl =>
      rw [natAdd_succ_left] at h
      exact ih tl h

private theorem listSplice_length {α : Type} (off : Nat) (mid xs : List α)
    (h : Nat.ble (off + mid.length) xs.length = true) :
    (xs.take off ++ mid ++ xs.drop (off + mid.length)).length = xs.length := by
  revert xs
  induction off with
  | zero =>
    intro xs h
    rw [natAdd_zero_left] at h
    rw [natAdd_zero_left]
    change (mid ++ xs.drop mid.length).length = xs.length
    rw [listLength_append]
    have hEq := listTake_append_drop mid.length xs
    have hLen := congrArg List.length hEq
    rw [listLength_append, listTake_length_of_ble mid.length xs h] at hLen
    exact hLen
  | succ off' ih =>
    intro xs h
    cases xs with
    | nil =>
      rw [natAdd_succ_left] at h
      exact False.elim (boolFalseNeTrue h)
    | cons hd tl =>
      rw [natAdd_succ_left] at h
      rw [natAdd_succ_left]
      change (hd :: (tl.take off' ++ mid ++
        tl.drop (off' + mid.length))).length = tl.length + 1
      exact congrArg Nat.succ (ih tl h)

private theorem listDrop_append_exact {α : Type} (xs ys : List α) :
    (xs ++ ys).drop xs.length = ys := by
  induction xs with
  | nil => rfl
  | cons _ tl ih => exact ih

private theorem listDrop_append_ge {α : Type} (n : Nat) (xs ys : List α)
    (h : Nat.ble xs.length n = true) :
    (xs ++ ys).drop n = ys.drop (n - xs.length) := by
  revert n
  induction xs with
  | nil => intro _ _; rfl
  | cons _ tl ih =>
    intro n h
    cases n with
    | zero => exact False.elim (boolFalseNeTrue h)
    | succ n' =>
      change (tl ++ ys).drop n' = ys.drop ((n' + 1) - (tl.length + 1))
      rw [Nat.succ_sub_succ]
      exact ih n' h

private theorem listTake_append_exact {α : Type} (xs ys : List α) :
    (xs ++ ys).take xs.length = xs := by
  induction xs with
  | nil => rfl
  | cons hd tl ih => exact congrArg (List.cons hd) ih

private theorem listDrop_append_of_len {α : Type} (n : Nat) (xs ys : List α)
    (h : xs.length = n) : (xs ++ ys).drop n = ys := by
  subst h
  exact listDrop_append_exact xs ys

private theorem listTake_append_of_len {α : Type} (n : Nat) (xs ys : List α)
    (h : xs.length = n) : (xs ++ ys).take n = xs := by
  subst h
  exact listTake_append_exact xs ys

private theorem listDrop_take_splice_same {α : Type} (off : Nat)
    (mid xs : List α) (h : Nat.ble (off + mid.length) xs.length = true) :
    ((xs.take off ++ mid ++ xs.drop (off + mid.length)).drop off).take
      mid.length = mid := by
  have hOffLe : Nat.ble off xs.length = true :=
    natBle_trans off (off + mid.length) xs.length
      (natBle_add_right off mid.length) h
  have hTakeLen : (xs.take off).length = off :=
    listTake_length_of_ble off xs hOffLe
  rw [listAppend_assoc, listDrop_append_of_len off (xs.take off) _ hTakeLen]
  exact listTake_append_exact mid (xs.drop (off + mid.length))

private theorem listTake_splice_same_prefix {α : Type} (off : Nat)
    (mid xs : List α) (h : Nat.ble (off + mid.length) xs.length = true) :
    (xs.take off ++ mid ++ xs.drop (off + mid.length)).take off =
      xs.take off := by
  have hOffLe : Nat.ble off xs.length = true :=
    natBle_trans off (off + mid.length) xs.length
      (natBle_add_right off mid.length) h
  have hTakeLen : (xs.take off).length = off :=
    listTake_length_of_ble off xs hOffLe
  rw [listAppend_assoc]
  exact listTake_append_of_len off (xs.take off) _ hTakeLen

private theorem listDrop_splice_same_suffix {α : Type} (off : Nat)
    (mid xs : List α) (h : Nat.ble (off + mid.length) xs.length = true) :
    (xs.take off ++ mid ++ xs.drop (off + mid.length)).drop
      (off + mid.length) = xs.drop (off + mid.length) := by
  have hOffLe : Nat.ble off xs.length = true :=
    natBle_trans off (off + mid.length) xs.length
      (natBle_add_right off mid.length) h
  have hPreLen : (xs.take off ++ mid).length = off + mid.length := by
    rw [listLength_append, listTake_length_of_ble off xs hOffLe]
  exact listDrop_append_of_len (off + mid.length) (xs.take off ++ mid)
    (xs.drop (off + mid.length)) hPreLen

private theorem listSplice_overwrite_same {α : Type} (off : Nat)
    (mid1 mid2 xs : List α) (h1 : Nat.ble (off + mid1.length) xs.length = true)
    (hLenEq : mid2.length = mid1.length) :
    let xs1 := xs.take off ++ mid1 ++ xs.drop (off + mid1.length)
    xs1.take off ++ mid2 ++ xs1.drop (off + mid2.length) =
      xs.take off ++ mid2 ++ xs.drop (off + mid2.length) := by
  dsimp only
  rw [hLenEq, listTake_splice_same_prefix off mid1 xs h1,
    listDrop_splice_same_suffix off mid1 xs h1]

private theorem natSub_add_cancel_of_ble (a b : Nat)
    (h : Nat.ble a b = true) : a + (b - a) = b := by
  revert b
  induction a with
  | zero => intro b _; exact natAdd_zero_left b
  | succ a' ih =>
    intro b h
    cases b with
    | zero => exact False.elim (boolFalseNeTrue h)
    | succ b' =>
      rw [Nat.succ_sub_succ, natAdd_succ_left]
      exact congrArg Nat.succ (ih b' h)

private theorem listDrop_take_comm_le {α : Type} (off sz n : Nat)
    (xs : List α) (h : Nat.ble (off + sz) n = true) :
    ((xs.take n).drop off).take sz = (xs.drop off).take sz := by
  revert n xs
  induction off with
  | zero =>
    intro n xs h
    rw [natAdd_zero_left] at h
    change ((xs.take n).take sz) = xs.take sz
    revert n xs
    induction sz with
    | zero => intro _ _ _; rfl
    | succ sz' ihSz =>
      intro n xs hLe
      cases n with
      | zero => exact False.elim (boolFalseNeTrue hLe)
      | succ n' =>
        cases xs with
        | nil => rfl
        | cons hd tl =>
          change hd :: ((tl.take n').take sz') = hd :: tl.take sz'
          exact congrArg (List.cons hd) (ihSz n' tl hLe)
  | succ off' ih =>
    intro n xs h
    rw [natAdd_succ_left] at h
    cases n with
    | zero => exact False.elim (boolFalseNeTrue h)
    | succ n' =>
      cases xs with
      | nil => rfl
      | cons _ tl =>
        change ((tl.take n').drop off').take sz = (tl.drop off').take sz
        exact ih n' tl h

private theorem listDrop_take_splice_disjoint {α : Type}
    (off1 off2 sz2 : Nat) (mid1 xs : List α)
    (h1 : Nat.ble (off1 + mid1.length) xs.length = true)
    (hDisj : (Nat.ble (off1 + mid1.length) off2 ||
      Nat.ble (off2 + sz2) off1) = true) :
    ((xs.take off1 ++ mid1 ++ xs.drop (off1 + mid1.length)).drop off2).take
      sz2 = (xs.drop off2).take sz2 := by
  have hOff1Le : Nat.ble off1 xs.length = true :=
    natBle_trans off1 (off1 + mid1.length) xs.length
      (natBle_add_right off1 mid1.length) h1
  have hPreLen : (xs.take off1 ++ mid1).length = off1 + mid1.length := by
    rw [listLength_append, listTake_length_of_ble off1 xs hOff1Le]
  cases hLeft : Nat.ble (off1 + mid1.length) off2 with
  | true =>
    have hGePre : Nat.ble (xs.take off1 ++ mid1).length off2 = true := by
      rw [hPreLen]; exact hLeft
    rw [listDrop_append_ge off2 (xs.take off1 ++ mid1)
          (xs.drop (off1 + mid1.length)) hGePre,
        hPreLen, ← listDrop_add (off1 + mid1.length) _ xs,
        natSub_add_cancel_of_ble (off1 + mid1.length) off2 hLeft]
  | false =>
    have hDisj2 : Nat.ble (off2 + sz2) off1 = true := by
      rw [hLeft] at hDisj; exact hDisj
    have hTakeLen : (xs.take off1).length = off1 :=
      listTake_length_of_ble off1 xs hOff1Le
    rw [listAppend_assoc]
    have hSubTake :
        ((xs.take off1 ++ (mid1 ++ xs.drop (off1 + mid1.length))).take off1) =
        xs.take off1 :=
      listTake_append_of_len off1 (xs.take off1) _ hTakeLen
    rw [← listDrop_take_comm_le off2 sz2 off1
          (xs.take off1 ++ (mid1 ++ xs.drop (off1 + mid1.length))) hDisj2,
        hSubTake]
    exact listDrop_take_comm_le off2 sz2 off1 xs hDisj2

/-! ## 2. `findAllocationComp` & `replaceAllocationComp` Algebra -/

/-- `findAllocationComp id allocs = some a` implies `a.allocId = id`. -/
theorem findAllocationComp_allocId (id : AllocId) (allocs : List Allocation)
    (a : Allocation) (h : findAllocationComp id allocs = some a) :
    a.allocId = id := by
  rw [findAllocationComp_eq] at h
  induction allocs with
  | nil => nomatch h
  | cons hd rest ih =>
    dsimp only [findAllocation] at h
    cases hEq : Nat.beq hd.allocId id with
    | true =>
      rw [ite_bool_true hEq] at h
      injection h with hA
      subst hA
      exact natEq_of_beq hd.allocId id hEq
    | false =>
      rw [ite_bool_false hEq] at h
      exact ih h

/-- Writing back the exact first-matching allocation is the identity on
`allocs` (`[]` zero axioms, no duplicate-free invariant needed). -/
theorem replaceAllocationComp_self (id : AllocId) (allocs : List Allocation)
    (a : Allocation) (h : findAllocationComp id allocs = some a) :
    replaceAllocationComp a allocs = allocs := by
  have hId := findAllocationComp_allocId id allocs a h
  rw [findAllocationComp_eq] at h
  rw [replaceAllocationComp_eq]
  induction allocs with
  | nil => nomatch h
  | cons hd rest ih =>
    dsimp only [findAllocation] at h
    dsimp only [replaceAllocation]
    cases hEq : Nat.beq hd.allocId id with
    | true =>
      rw [ite_bool_true hEq] at h
      injection h with hA
      subst hA
      rw [natBeq_refl hd.allocId, ite_bool_true rfl]
    | false =>
      rw [ite_bool_false hEq] at h
      rw [hId, hEq, ite_bool_false rfl]
      exact congrArg (List.cons hd) (ih h)

/-- Looking up `aOld.allocId` after `replaceAllocationComp aNew allocs` returns
`some aNew` whenever `aNew.allocId = aOld.allocId`. -/
theorem findAllocationComp_replace_same (allocs : List Allocation)
    (aOld aNew : Allocation)
    (hFind : findAllocationComp aOld.allocId allocs = some aOld)
    (hSameId : aNew.allocId = aOld.allocId) :
    findAllocationComp aOld.allocId (replaceAllocationComp aNew allocs) =
      some aNew := by
  rw [findAllocationComp_eq] at hFind
  rw [replaceAllocationComp_eq, findAllocationComp_eq]
  induction allocs with
  | nil => nomatch hFind
  | cons hd rest ih =>
    dsimp only [findAllocation] at hFind
    dsimp only [replaceAllocation]
    rw [hSameId]
    cases hEq : Nat.beq hd.allocId aOld.allocId with
    | true =>
      rw [ite_bool_true rfl]
      dsimp only [findAllocation]
      rw [hSameId, natBeq_refl aOld.allocId, ite_bool_true rfl]
    | false =>
      rw [ite_bool_false hEq] at hFind
      rw [ite_bool_false rfl]
      dsimp only [findAllocation]
      rw [hEq, ite_bool_false rfl]
      exact ih hFind

/-- Updating `aNew.allocId` preserves lookups at every distinct `otherId`. -/
theorem findAllocationComp_replace_ne (otherId : AllocId)
    (allocs : List Allocation) (aNew : Allocation)
    (hNe : Nat.beq aNew.allocId otherId = false) :
    findAllocationComp otherId (replaceAllocationComp aNew allocs) =
      findAllocationComp otherId allocs := by
  rw [replaceAllocationComp_eq, findAllocationComp_eq, findAllocationComp_eq]
  induction allocs with
  | nil => rfl
  | cons hd rest ih =>
    dsimp only [replaceAllocation]
    cases hEq : Nat.beq hd.allocId aNew.allocId with
    | true =>
      rw [ite_bool_true rfl]
      have hHdEq := natEq_of_beq hd.allocId aNew.allocId hEq
      dsimp only [findAllocation]
      rw [hHdEq, hNe, ite_bool_false rfl, ite_bool_false rfl]
    | false =>
      rw [ite_bool_false rfl]
      dsimp only [findAllocation]
      cases hOther : Nat.beq hd.allocId otherId with
      | true => rw [ite_bool_true rfl, ite_bool_true rfl]
      | false =>
        rw [ite_bool_false rfl, ite_bool_false rfl]
        exact ih

/-- Overwriting `a1` then `a2` at the same `allocId` collapses to overwriting
`a2` directly. -/
theorem replaceAllocationComp_replace_same (allocs : List Allocation)
    (a1 a2 : Allocation) (hSame : a2.allocId = a1.allocId) :
    replaceAllocationComp a2 (replaceAllocationComp a1 allocs) =
      replaceAllocationComp a2 allocs := by
  rw [replaceAllocationComp_eq, replaceAllocationComp_eq,
      replaceAllocationComp_eq]
  induction allocs with
  | nil => rfl
  | cons hd rest ih =>
    dsimp only [replaceAllocation]
    rw [hSame]
    cases hEq : Nat.beq hd.allocId a1.allocId with
    | true =>
      rw [ite_bool_true rfl]
      dsimp only [replaceAllocation]
      rw [hSame, natBeq_refl a1.allocId]
      rfl
    | false =>
      rw [ite_bool_false rfl]
      dsimp only [replaceAllocation]
      rw [hSame, hEq, ite_bool_false rfl]
      exact congrArg (List.cons hd) ih

/-! ## 3. `ByteSubLens` Geometry, Ops, & `Trusted.MirSemantics` Bridges -/

/-- Byte-level sub-allocation lens focusing on `[offset, offset + size)` inside
`allocId` in `Trusted.MirSemantics.MemoryState` with alignment exponent
`alignLog2`. -/
structure ByteSubLens where
  allocId : AllocId
  offset : Nat
  size : Nat
  alignLog2 : Nat

/-- Decidable interval disjointness `[off1, off1 + sz1) ∩ [off2, off2 + sz2) =
∅` on non-empty slices. -/
@[expose] def rangesDisjoint (off1 sz1 off2 sz2 : Nat) : Bool :=
  Nat.ble (off1 + sz1) off2 || Nat.ble (off2 + sz2) off1

/-- Symmetry of `rangesDisjoint`. -/
theorem rangesDisjoint_symm (off1 sz1 off2 sz2 : Nat) :
    rangesDisjoint off1 sz1 off2 sz2 = rangesDisjoint off2 sz2 off1 sz1 :=
  borComm _ _

/-- Decidable disjointness of two `ByteSubLens`es (distinct `allocId`s or
disjoint byte intervals). -/
@[expose] def byteLensDisjoint (L1 L2 : ByteSubLens) : Bool :=
  !Nat.beq L1.allocId L2.allocId ||
    rangesDisjoint L1.offset L1.size L2.offset L2.size

/-- Symmetry of `byteLensDisjoint`. -/
theorem byteLensDisjoint_symm (L1 L2 : ByteSubLens) :
    byteLensDisjoint L1 L2 = byteLensDisjoint L2 L1 := by
  dsimp only [byteLensDisjoint]
  rw [natBeq_symm L1.allocId L2.allocId,
      rangesDisjoint_symm L1.offset L1.size L2.offset L2.size]

/-- Decidable hierarchical sub-slice containment `child ⊆ parent` (same
`allocId`, `0 < child.size`, and `[child.offset, child.offset + child.size) ⊆
[parent.offset, parent.offset + parent.size)`). -/
@[expose] def subLensContained (child parent : ByteSubLens) : Bool :=
  Nat.beq child.allocId parent.allocId &&
  Nat.blt 0 child.size &&
  Nat.ble parent.offset child.offset &&
  Nat.ble (child.offset + child.size) (parent.offset + parent.size)

/-- Reflexivity of `subLensContained` on positive-size lenses. -/
theorem subLensContained_refl (L : ByteSubLens)
    (hPos : Nat.blt 0 L.size = true) :
    subLensContained L L = true := by
  dsimp only [subLensContained]
  rw [natBeq_refl L.allocId, hPos, natBle_refl L.offset,
      natBle_refl (L.offset + L.size)]
  rfl

/-- Transitivity of `subLensContained` across nested projections. -/
theorem subLensContained_trans {a b c : ByteSubLens}
    (hab : subLensContained a b = true)
    (hbc : subLensContained b c = true) :
    subLensContained a c = true := by
  dsimp only [subLensContained] at hab hbc
  have hab123 := bandLeft hab
  have habEnd := bandRight hab
  have hab12 := bandLeft hab123
  have habOff := bandRight hab123
  have habId := bandLeft hab12
  have habPos := bandRight hab12
  have hbc123 := bandLeft hbc
  have hbcEnd := bandRight hbc
  have hbc12 := bandLeft hbc123
  have hbcOff := bandRight hbc123
  have hbcId := bandLeft hbc12
  have hacId : Nat.beq a.allocId c.allocId = true := by
    rw [natEq_of_beq a.allocId b.allocId habId]
    exact hbcId
  have hacOff : Nat.ble c.offset a.offset = true :=
    natBle_trans c.offset b.offset a.offset hbcOff habOff
  have hacEnd : Nat.ble (a.offset + a.size) (c.offset + c.size) = true :=
    natBle_trans _ _ _ habEnd hbcEnd
  dsimp only [subLensContained]
  rw [hacId, habPos, hacOff, hacEnd]
  rfl

/-- Disjointness inheritance: sub-lenses of disjoint parent lenses are
themselves disjoint (enabling hierarchical struct/slice borrow splitting). -/
theorem byteLensDisjoint_of_contained {c1 p1 c2 p2 : ByteSubLens}
    (hc1 : subLensContained c1 p1 = true)
    (hc2 : subLensContained c2 p2 = true)
    (hDisj : byteLensDisjoint p1 p2 = true) :
    byteLensDisjoint c1 c2 = true := by
  dsimp only [subLensContained] at hc1 hc2
  have hId1 := natEq_of_beq _ _ (bandLeft (bandLeft (bandLeft hc1)))
  have hOff1 := bandRight (bandLeft hc1)
  have hEnd1 := bandRight hc1
  have hId2 := natEq_of_beq _ _ (bandLeft (bandLeft (bandLeft hc2)))
  have hOff2 := bandRight (bandLeft hc2)
  have hEnd2 := bandRight hc2
  dsimp only [byteLensDisjoint] at hDisj
  dsimp only [byteLensDisjoint]
  rw [hId1, hId2]
  cases hSame : Nat.beq p1.allocId p2.allocId with
  | false => rfl
  | true =>
    rw [hSame] at hDisj
    dsimp only [Bool.not, Bool.or, rangesDisjoint] at hDisj
    dsimp only [rangesDisjoint]
    cases hL : Nat.ble (p1.offset + p1.size) p2.offset with
    | true =>
      have hStep1 := natBle_trans _ _ _ hEnd1 hL
      have hStep2 := natBle_trans _ _ _ hStep1 hOff2
      rw [hStep2]
      rfl
    | false =>
      rw [hL] at hDisj
      have hStep1 := natBle_trans _ _ _ hEnd2 hDisj
      have hStep2 := natBle_trans _ _ _ hStep1 hOff1
      rw [hStep2]
      exact borComm _ true

/-- Computable boolean test for `Mutability.mut`. -/
@[expose] def mutabilityIsMut (m : Mutability) : Bool :=
  match m with
  | .mut => true
  | .shared => false

private theorem mutability_eq_mut_of_isMut (m : Mutability)
    (h : mutabilityIsMut m = true) : m = .mut :=
  @Mutability.casesOn (fun x => mutabilityIsMut x = true → x = .mut) m
    (fun hS => False.elim (boolFalseNeTrue hS))
    (fun _ => rfl) h

/-- Computable sub-allocation byte-slice read (`0` `noncomputable`), enforcing
`0 < L.size`, `mutability = .mut`, `live = true`, `isInBounds`, and
`isAligned`. -/
@[expose] def byteSubLensGet (L : ByteSubLens) (m : MemoryState) :
    Option (List AllocByte) :=
  match Nat.blt 0 L.size with
  | false => none
  | true =>
    match findAllocationComp L.allocId m.allocations with
    | none => none
    | some a =>
      match mutabilityIsMut a.mutability with
      | false => none
      | true =>
        match readBytesComp m ⟨L.allocId, L.offset⟩ L.size L.alignLog2 with
        | .ok bs => some bs
        | .error _ => none

/-- Computable sub-allocation byte-slice write (`0` `noncomputable`), enforcing
`0 < L.size`, `bs.length = L.size`, `mutability = .mut`, `live = true`,
`isInBounds`, and `isAligned`. -/
@[expose] def byteSubLensPut (L : ByteSubLens) (m : MemoryState)
    (bs : List AllocByte) : Option MemoryState :=
  match Nat.blt 0 L.size && Nat.beq bs.length L.size with
  | false => none
  | true =>
    match writeBytesComp m ⟨L.allocId, L.offset⟩ L.alignLog2 bs with
    | .ok m' => some m'
    | .error _ => none

/-- Exact agreement between computable `byteSubLensGet` and
`Trusted.MirSemantics.{findAllocation, readBytes}`. -/
theorem byteSubLensGet_eq_mir (L : ByteSubLens) (m : MemoryState) :
    byteSubLensGet L m =
      match Nat.blt 0 L.size with
      | false => none
      | true =>
        match findAllocation L.allocId m.allocations with
        | none => none
        | some a =>
          match mutabilityIsMut a.mutability with
          | false => none
          | true =>
            match readBytes m ⟨L.allocId, L.offset⟩ L.size L.alignLog2 with
            | .ok bs => some bs
            | .error _ => none := by
  dsimp only [byteSubLensGet]
  cases Nat.blt 0 L.size with
  | false => rfl
  | true =>
    rw [findAllocationComp_eq, readBytesComp_eq]

/-- Exact agreement between computable `byteSubLensPut` and
`Trusted.MirSemantics.writeBytes`. -/
theorem byteSubLensPut_eq_mir (L : ByteSubLens) (m : MemoryState)
    (bs : List AllocByte) :
    byteSubLensPut L m bs =
      match Nat.blt 0 L.size && Nat.beq bs.length L.size with
      | false => none
      | true =>
        match writeBytes m ⟨L.allocId, L.offset⟩ L.alignLog2 bs with
        | .ok m' => some m'
        | .error _ => none := by
  dsimp only [byteSubLensPut]
  cases (Nat.blt 0 L.size && Nat.beq bs.length L.size) with
  | false => rfl
  | true => rw [writeBytesComp_eq]

/-! ## 4. All Four Partial Lens & Disjoint-Frame Laws (`[]` Zero Axioms) -/

/-- Full 3-law + disjoint-frame partial lens contract over
`Trusted.MirSemantics.MemoryState`. -/
structure LawfulByteSubLens (L : ByteSubLens) : Prop where
  get_put : ∀ (m : MemoryState) (bs : List AllocByte),
    byteSubLensGet L m = some bs → byteSubLensPut L m bs = some m
  put_get : ∀ (m m' : MemoryState) (bs : List AllocByte),
    byteSubLensPut L m bs = some m' → byteSubLensGet L m' = some bs
  put_put : ∀ (m m1 : MemoryState) (bs1 bs2 : List AllocByte),
    byteSubLensPut L m bs1 = some m1 →
    byteSubLensPut L m1 bs2 = byteSubLensPut L m bs2
  get_put_disjoint : ∀ (L2 : ByteSubLens) (m m' : MemoryState)
      (bs : List AllocByte),
    byteLensDisjoint L L2 = true →
    byteSubLensPut L m bs = some m' →
    byteSubLensGet L2 m' = byteSubLensGet L2 m

private inductive GetInvData (L : ByteSubLens) (m : MemoryState)
    (bs : List AllocByte) : Prop where
  | mk
      (pos : Nat.blt 0 L.size = true)
      (alloc : Allocation)
      (found : findAllocationComp L.allocId m.allocations = some alloc)
      (isMut : alloc.mutability = .mut)
      (live : alloc.live = true)
      (inBounds : isInBoundsComp alloc L.offset L.size = true)
      (aligned : isAlignedComp alloc L.offset L.alignLog2 = true)
      (sliceEq : bs = (alloc.bytes.drop L.offset).take L.size)
      (lenEq : bs.length = L.size) : GetInvData L m bs

private inductive PutInvData (L : ByteSubLens) (m m' : MemoryState)
    (bs : List AllocByte) : Prop where
  | mk
      (pos : Nat.blt 0 L.size = true)
      (lenEq : bs.length = L.size)
      (alloc : Allocation)
      (found : findAllocationComp L.allocId m.allocations = some alloc)
      (isMut : alloc.mutability = .mut)
      (live : alloc.live = true)
      (inBounds : isInBoundsComp alloc L.offset L.size = true)
      (aligned : isAlignedComp alloc L.offset L.alignLog2 = true)
      (memEq : m' = MemoryState.mk m.nextAllocId
        (replaceAllocationComp
          (Allocation.mk alloc.allocId alloc.alignLog2 alloc.mutability
            (alloc.bytes.take L.offset ++ bs ++
              alloc.bytes.drop (L.offset + bs.length))
            alloc.live)
          m.allocations)) : PutInvData L m m' bs

private theorem byteSubLens_get_inversion (L : ByteSubLens) (m : MemoryState)
    (bs : List AllocByte) (hGet : byteSubLensGet L m = some bs) :
    GetInvData L m bs := by
  dsimp only [byteSubLensGet] at hGet
  cases hPos : Nat.blt 0 L.size with
  | false => rw [hPos] at hGet; nomatch hGet
  | true =>
    rw [hPos] at hGet
    dsimp only at hGet
    cases hFind : findAllocationComp L.allocId m.allocations with
    | none => rw [hFind] at hGet; nomatch hGet
    | some a =>
      rw [hFind] at hGet
      dsimp only at hGet
      cases hMutB : mutabilityIsMut a.mutability with
      | false => rw [hMutB] at hGet; nomatch hGet
      | true =>
        rw [hMutB] at hGet
        have hMut := mutability_eq_mut_of_isMut a.mutability hMutB
        dsimp only [readBytesComp] at hGet
        rw [natBeq_zero_false_of_blt_zero L.size hPos,
            ite_bool_false rfl, hFind] at hGet
        dsimp only at hGet
        cases hGuard : (!a.live || !isInBoundsComp a L.offset L.size ||
            !isAlignedComp a L.offset L.alignLog2) with
        | true => rw [ite_bool_true hGuard] at hGet; nomatch hGet
        | false =>
          rw [ite_bool_false hGuard] at hGet
          injection hGet with hBs
          have hG1 := borFalseElim hGuard
          have hG2 := borFalseElim hG1.1
          have hLive : a.live = true := by
            cases hl : a.live with
            | true => rfl
            | false => rw [hl] at hG2; exact False.elim (boolTrueNeFalse hG2.1)
          have hBounds : isInBoundsComp a L.offset L.size = true := by
            cases hb : isInBoundsComp a L.offset L.size with
            | true => rfl
            | false => rw [hb] at hG2; exact False.elim (boolTrueNeFalse hG2.2)
          have hAlign : isAlignedComp a L.offset L.alignLog2 = true := by
            cases ha : isAlignedComp a L.offset L.alignLog2 with
            | true => rfl
            | false => rw [ha] at hG1; exact False.elim (boolTrueNeFalse hG1.2)
          have hLen : bs.length = L.size := by
            rw [← hBs]
            exact listDrop_take_length_of_ble L.offset L.size a.bytes hBounds
          exact ⟨hPos, a, hFind, hMut, hLive, hBounds, hAlign, hBs.symm, hLen⟩

private theorem byteSubLens_put_inversion (L : ByteSubLens)
    (m m' : MemoryState) (bs : List AllocByte)
    (hPut : byteSubLensPut L m bs = some m') : PutInvData L m m' bs := by
  dsimp only [byteSubLensPut] at hPut
  cases hConj : (Nat.blt 0 L.size && Nat.beq bs.length L.size) with
  | false => rw [hConj] at hPut; nomatch hPut
  | true =>
    rw [hConj] at hPut
    dsimp only at hPut
    have hPos := bandLeft hConj
    have hLenEq := natEq_of_beq bs.length L.size (bandRight hConj)
    dsimp only [writeBytesComp] at hPut
    have hBsNz : Nat.beq bs.length 0 = false := by
      rw [hLenEq]
      exact natBeq_zero_false_of_blt_zero L.size hPos
    rw [hBsNz, ite_bool_false rfl] at hPut
    cases hFind : findAllocationComp L.allocId m.allocations with
    | none => rw [hFind] at hPut; nomatch hPut
    | some a =>
      rw [hFind] at hPut
      dsimp only at hPut
      cases hGuard : (!a.live || !isInBoundsComp a L.offset bs.length ||
          !isAlignedComp a L.offset L.alignLog2) with
      | true => rw [ite_bool_true hGuard] at hPut; nomatch hPut
      | false =>
        rw [ite_bool_false hGuard] at hPut
        have hMutCase : a.mutability = .mut ∧
            m' = MemoryState.mk m.nextAllocId
              (replaceAllocationComp
                (Allocation.mk a.allocId a.alignLog2 a.mutability
                  (a.bytes.take L.offset ++ bs ++
                    a.bytes.drop (L.offset + bs.length))
                  a.live)
                m.allocations) :=
          @Mutability.casesOn
            (fun mu =>
              (match match mu with
                | .shared => Except.error FaultKind.undefined
                | .mut =>
                  Except.ok (MemoryState.mk m.nextAllocId
                    (replaceAllocationComp
                      (Allocation.mk a.allocId a.alignLog2 mu
                        (a.bytes.take L.offset ++ bs ++
                          a.bytes.drop (L.offset + bs.length))
                        a.live)
                      m.allocations)) with
                | .ok mx => some mx
                | .error _ => none) = some m' →
              mu = .mut ∧
              m' = MemoryState.mk m.nextAllocId
                (replaceAllocationComp
                  (Allocation.mk a.allocId a.alignLog2 mu
                    (a.bytes.take L.offset ++ bs ++
                      a.bytes.drop (L.offset + bs.length))
                    a.live)
                  m.allocations))
            a.mutability
            (fun hBad => by nomatch hBad)
            (fun hOk => by injection hOk with hM; exact ⟨rfl, hM.symm⟩)
            hPut
        have hG1 := borFalseElim hGuard
        have hG2 := borFalseElim hG1.1
        have hLive : a.live = true := by
          cases hl : a.live with
          | true => rfl
          | false => rw [hl] at hG2; exact False.elim (boolTrueNeFalse hG2.1)
        have hBounds : isInBoundsComp a L.offset L.size = true := by
          rw [← hLenEq]
          cases hb : isInBoundsComp a L.offset bs.length with
          | true => rfl
          | false => rw [hb] at hG2; exact False.elim (boolTrueNeFalse hG2.2)
        have hAlign : isAlignedComp a L.offset L.alignLog2 = true := by
          cases ha : isAlignedComp a L.offset L.alignLog2 with
          | true => rfl
          | false => rw [ha] at hG1; exact False.elim (boolTrueNeFalse hG1.2)
        exact ⟨hPos, hLenEq, a, hFind, hMutCase.1, hLive, hBounds, hAlign,
          hMutCase.2⟩

/-- GetPut law: writing back a slice read via `byteSubLensGet` returns the
exact original `MemoryState`. -/
theorem byteSubLens_get_put (L : ByteSubLens) (m : MemoryState)
    (bs : List AllocByte) (hGet : byteSubLensGet L m = some bs) :
    byteSubLensPut L m bs = some m := by
  cases byteSubLens_get_inversion L m bs hGet with
  | mk hPos a hFind hMut hLive hBounds hAlign hBs hLen =>
    dsimp only [byteSubLensPut, writeBytesComp]
    rw [hPos, natBeq_of_eq bs.length L.size hLen, bandIntro rfl rfl]
    dsimp only
    rw [hLen, natBeq_zero_false_of_blt_zero L.size hPos,
        ite_bool_false rfl, hFind]
    dsimp only
    have hGuardFalse :
        (!a.live || !isInBoundsComp a L.offset L.size ||
          !isAlignedComp a L.offset L.alignLog2) = false := by
      rw [hLive, hBounds, hAlign]; rfl
    rw [ite_bool_false hGuardFalse, hMut]
    dsimp only
    have hBytesId :
        a.bytes.take L.offset ++ bs ++ a.bytes.drop (L.offset + L.size) =
        a.bytes := by
      rw [hBs]
      exact listSplice_self L.offset L.size a.bytes
    rw [hBytesId]
    have hAId : Allocation.mk a.allocId a.alignLog2 .mut a.bytes a.live = a := by
      cases a with
      | mk id al mu bys lv =>
        dsimp only at hMut
        subst hMut
        rfl
    change some (MemoryState.mk m.nextAllocId
      (replaceAllocationComp
        (Allocation.mk a.allocId a.alignLog2 .mut a.bytes a.live)
        m.allocations)) = some m
    rw [hAId, replaceAllocationComp_self L.allocId m.allocations a hFind]

/-- PutGet law: reading after a successful `byteSubLensPut` yields the exact
written slice `bs`. -/
theorem byteSubLens_put_get (L : ByteSubLens) (m m' : MemoryState)
    (bs : List AllocByte) (hPut : byteSubLensPut L m bs = some m') :
    byteSubLensGet L m' = some bs := by
  cases byteSubLens_put_inversion L m m' bs hPut with
  | mk hPos hLenEq a hFind hMut hLive hBounds hAlign hM' =>
    have hAllocId : a.allocId = L.allocId :=
      findAllocationComp_allocId L.allocId m.allocations a hFind
    let bytes' :=
      a.bytes.take L.offset ++ bs ++ a.bytes.drop (L.offset + bs.length)
    let a' : Allocation :=
      Allocation.mk a.allocId a.alignLog2 a.mutability bytes' a.live
    have hBoundsBs : Nat.ble (L.offset + bs.length) a.bytes.length = true := by
      rw [hLenEq]; exact hBounds
    have hLenBytes' : bytes'.length = a.bytes.length :=
      listSplice_length L.offset bs a.bytes hBoundsBs
    have hFind' : findAllocationComp L.allocId m'.allocations = some a' := by
      rw [hM']
      dsimp only
      rw [← hAllocId]
      exact findAllocationComp_replace_same m.allocations a a'
        (by rw [hAllocId]; exact hFind) rfl
    have hBounds' : isInBoundsComp a' L.offset L.size = true := by
      dsimp only [isInBoundsComp, a']
      rw [hLenBytes']
      exact hBounds
    have hAlign' : isAlignedComp a' L.offset L.alignLog2 = true := hAlign
    dsimp only [byteSubLensGet, readBytesComp]
    rw [hPos]
    dsimp only
    rw [hFind']
    dsimp only
    have hMut' : mutabilityIsMut a'.mutability = true := by
      dsimp only [a']; rw [hMut]; rfl
    rw [hMut']
    dsimp only
    rw [natBeq_zero_false_of_blt_zero L.size hPos, ite_bool_false rfl]
    have hGuardFalse :
        (!a.live || !isInBoundsComp a' L.offset L.size ||
          !isAlignedComp a' L.offset L.alignLog2) = false := by
      rw [hLive, hBounds', hAlign']; rfl
    rw [ite_bool_false hGuardFalse]
    have hReadSlice : (bytes'.drop L.offset).take L.size = bs := by
      rw [← hLenEq]
      exact listDrop_take_splice_same L.offset bs a.bytes hBoundsBs
    exact congrArg some hReadSlice

/-- PutPut law: a second `byteSubLensPut` at `L` overwrites the first (and
agrees even when `bs2.length ≠ L.size`, where both sides return `none`). -/
theorem byteSubLens_put_put (L : ByteSubLens) (m m1 : MemoryState)
    (bs1 bs2 : List AllocByte) (hPut1 : byteSubLensPut L m bs1 = some m1) :
    byteSubLensPut L m1 bs2 = byteSubLensPut L m bs2 := by
  cases byteSubLens_put_inversion L m m1 bs1 hPut1 with
  | mk hPos hLen1 a hFind hMut hLive hBounds hAlign hM1 =>
    have hAllocId : a.allocId = L.allocId :=
      findAllocationComp_allocId L.allocId m.allocations a hFind
    dsimp only [byteSubLensPut]
    cases hConj2 : (Nat.blt 0 L.size && Nat.beq bs2.length L.size) with
    | false => rfl
    | true =>
      dsimp only [writeBytesComp]
      have hLen2 := natEq_of_beq bs2.length L.size (bandRight hConj2)
      have hBs2Nz : Nat.beq bs2.length 0 = false := by
        rw [hLen2]; exact natBeq_zero_false_of_blt_zero L.size hPos
      rw [hBs2Nz, ite_bool_false rfl]
      let bytes1 :=
        a.bytes.take L.offset ++ bs1 ++ a.bytes.drop (L.offset + bs1.length)
      let a1 : Allocation :=
        Allocation.mk a.allocId a.alignLog2 a.mutability bytes1 a.live
      have hFind1 : findAllocationComp L.allocId m1.allocations = some a1 := by
        rw [hM1]; dsimp only; rw [← hAllocId]
        exact findAllocationComp_replace_same m.allocations a a1
          (by rw [hAllocId]; exact hFind) rfl
      rw [hFind1, hFind]
      dsimp only
      have hBoundsBs1 :
          Nat.ble (L.offset + bs1.length) a.bytes.length = true := by
        rw [hLen1]; exact hBounds
      have hLenBytes1 : bytes1.length = a.bytes.length :=
        listSplice_length L.offset bs1 a.bytes hBoundsBs1
      have hBounds2In1 : isInBoundsComp a1 L.offset bs2.length = true := by
        dsimp only [isInBoundsComp, a1]; rw [hLenBytes1, hLen2]; exact hBounds
      have hBounds2In0 : isInBoundsComp a L.offset bs2.length = true := by
        dsimp only [isInBoundsComp]; rw [hLen2]; exact hBounds
      have hAlign1 : isAlignedComp a1 L.offset L.alignLog2 = true := hAlign
      have hG1 : (!a.live || !isInBoundsComp a1 L.offset bs2.length ||
          !isAlignedComp a1 L.offset L.alignLog2) = false := by
        rw [hLive, hBounds2In1, hAlign1]; rfl
      have hG0 : (!a.live || !isInBoundsComp a L.offset bs2.length ||
          !isAlignedComp a L.offset L.alignLog2) = false := by
        rw [hLive, hBounds2In0, hAlign]; rfl
      rw [ite_bool_false hG1, ite_bool_false hG0]
      dsimp only [a1]
      rw [hMut]
      dsimp only
      have hSpliceEq := listSplice_overwrite_same L.offset bs1 bs2 a.bytes
        hBoundsBs1 (Eq.trans hLen2 hLen1.symm)
      dsimp only at hSpliceEq
      rw [hSpliceEq, hM1]
      dsimp only
      have hA1Mut :
          Allocation.mk a.allocId a.alignLog2 a.mutability bytes1 a.live =
          Allocation.mk a.allocId a.alignLog2 .mut bytes1 a.live := by
        rw [hMut]
      rw [hA1Mut]
      rw [replaceAllocationComp_replace_same m.allocations
        (Allocation.mk a.allocId a.alignLog2 .mut bytes1 a.live)
        (Allocation.mk a.allocId a.alignLog2 .mut
          (a.bytes.take L.offset ++ bs2 ++
            a.bytes.drop (L.offset + bs2.length)) a.live)
        rfl]
      rfl

/-- Disjoint-frame law: writing through `L1` preserves `byteSubLensGet L2` for
every disjoint `L2` (`byteLensDisjoint L1 L2 = true`). -/
theorem byteSubLens_get_put_disjoint (L1 L2 : ByteSubLens)
    (m m' : MemoryState) (bs : List AllocByte)
    (hDisj : byteLensDisjoint L1 L2 = true)
    (hPut : byteSubLensPut L1 m bs = some m') :
    byteSubLensGet L2 m' = byteSubLensGet L2 m := by
  cases byteSubLens_put_inversion L1 m m' bs hPut with
  | mk _ hLen1 a hFind1 _ _ hBounds1 _ hM' =>
    have hAllocId1 : a.allocId = L1.allocId :=
      findAllocationComp_allocId L1.allocId m.allocations a hFind1
    dsimp only [byteSubLensGet]
    cases hPos2 : Nat.blt 0 L2.size with
    | false => rfl
    | true =>
      dsimp only
      dsimp only [byteLensDisjoint] at hDisj
      let bytes1 :=
        a.bytes.take L1.offset ++ bs ++ a.bytes.drop (L1.offset + bs.length)
      let a1 : Allocation :=
        Allocation.mk a.allocId a.alignLog2 a.mutability bytes1 a.live
      cases hIdEq : Nat.beq L1.allocId L2.allocId with
      | false =>
        have hNeId : Nat.beq a1.allocId L2.allocId = false := by
          dsimp only [a1]; rw [hAllocId1]; exact hIdEq
        have hFind2Eq : findAllocationComp L2.allocId m'.allocations =
            findAllocationComp L2.allocId m.allocations := by
          rw [hM']; dsimp only
          exact findAllocationComp_replace_ne L2.allocId m.allocations a1 hNeId
        rw [hFind2Eq]
        cases findAllocationComp L2.allocId m.allocations with
        | none => rfl
        | some a2 =>
          dsimp only
          cases mutabilityIsMut a2.mutability with
          | false => rfl
          | true =>
            dsimp only [readBytesComp]
            rw [natBeq_zero_false_of_blt_zero L2.size hPos2,
                ite_bool_false rfl, hFind2Eq]
            rfl
      | true =>
        have hDisjRange :
            rangesDisjoint L1.offset L1.size L2.offset L2.size = true := by
          rw [hIdEq] at hDisj; exact hDisj
        have hId12 := natEq_of_beq L1.allocId L2.allocId hIdEq
        have hFind1' : findAllocationComp L2.allocId m'.allocations =
            some a1 := by
          rw [← hId12, hM']; dsimp only; rw [← hAllocId1]
          exact findAllocationComp_replace_same m.allocations a a1
            (by rw [hAllocId1]; exact hFind1) rfl
        have hFind1Orig : findAllocationComp L2.allocId m.allocations =
            some a := by
          rw [← hId12]; exact hFind1
        rw [hFind1', hFind1Orig]
        dsimp only
        have hMutEq :
            mutabilityIsMut a1.mutability = mutabilityIsMut a.mutability := rfl
        rw [hMutEq]
        cases mutabilityIsMut a.mutability with
        | false => rfl
        | true =>
          dsimp only [readBytesComp]
          rw [natBeq_zero_false_of_blt_zero L2.size hPos2,
              ite_bool_false rfl, hFind1', hFind1Orig]
          dsimp only
          have hBoundsBs :
              Nat.ble (L1.offset + bs.length) a.bytes.length = true := by
            rw [hLen1]; exact hBounds1
          have hLenBytes1 : bytes1.length = a.bytes.length :=
            listSplice_length L1.offset bs a.bytes hBoundsBs
          have hInB2Eq :
              isInBoundsComp a1 L2.offset L2.size =
              isInBoundsComp a L2.offset L2.size := by
            dsimp only [isInBoundsComp, a1]; rw [hLenBytes1]
          rw [hInB2Eq]
          have hGuardEq :
              (!a1.live || !isInBoundsComp a L2.offset L2.size ||
                !isAlignedComp a1 L2.offset L2.alignLog2) =
              (!a.live || !isInBoundsComp a L2.offset L2.size ||
                !isAlignedComp a L2.offset L2.alignLog2) := rfl
          rw [hGuardEq]
          cases (!a.live || !isInBoundsComp a L2.offset L2.size ||
              !isAlignedComp a L2.offset L2.alignLog2) with
          | true => rfl
          | false =>
            have hDisjBs : (Nat.ble (L1.offset + bs.length) L2.offset ||
                Nat.ble (L2.offset + L2.size) L1.offset) = true := by
              rw [hLen1]; exact hDisjRange
            have hSliceEq := listDrop_take_splice_disjoint L1.offset L2.offset
              L2.size bs a.bytes hBoundsBs hDisjBs
            exact congrArg some hSliceEq

/-- Every `ByteSubLens` satisfies all 4 partial lens and disjoint-frame laws
over `Trusted.MirSemantics.MemoryState` (`[]` zero axioms). -/
theorem byteSubLens_lawful (L : ByteSubLens) : LawfulByteSubLens L where
  get_put := byteSubLens_get_put L
  put_get := byteSubLens_put_get L
  put_put := byteSubLens_put_put L
  get_put_disjoint := byteSubLens_get_put_disjoint L

/-- Whenever `byteSubLensGet L m = some oldSlice`, writing any `newSlice` of
length `L.size` succeeds. -/
theorem byteSubLens_put_succeeds_of_get (L : ByteSubLens) (m : MemoryState)
    (oldSlice newSlice : List AllocByte)
    (hGet : byteSubLensGet L m = some oldSlice)
    (hLen : newSlice.length = L.size) :
    ∃ m' : MemoryState, byteSubLensPut L m newSlice = some m' := by
  cases byteSubLens_get_inversion L m oldSlice hGet with
  | mk hPos a hFind hMut hLive hBounds hAlign _ _ =>
    let mOut : MemoryState := {
      nextAllocId := m.nextAllocId
      allocations := replaceAllocationComp
        (Allocation.mk a.allocId a.alignLog2 .mut
          (a.bytes.take L.offset ++ newSlice ++
            a.bytes.drop (L.offset + newSlice.length)) a.live)
        m.allocations
    }
    have hWB : writeBytesComp m ⟨L.allocId, L.offset⟩ L.alignLog2 newSlice =
        .ok mOut := by
      dsimp only [writeBytesComp]
      rw [hLen, natBeq_zero_false_of_blt_zero L.size hPos,
          ite_bool_false rfl, hFind]
      dsimp only
      have hGuard : (!a.live || !isInBoundsComp a L.offset L.size ||
          !isAlignedComp a L.offset L.alignLog2) = false := by
        rw [hLive, hBounds, hAlign]; rfl
      rw [ite_bool_false hGuard, hMut, ← hLen]
    refine ⟨mOut, ?_⟩
    dsimp only [byteSubLensPut]
    rw [hPos, hLen, natBeq_refl L.size]
    dsimp only [Bool.and]
    rw [hWB]

/-! ## 5. Fail-Closed Boundary Rejection Theorems -/

/-- Zero-size lenses (`size = 0`) are rejected by `byteSubLensGet`. -/
theorem zeroSizeByteLensRejected (allocId off alignLog2 : Nat)
    (m : MemoryState) :
    byteSubLensGet ⟨allocId, off, 0, alignLog2⟩ m = none := rfl

/-- Zero-size lenses (`size = 0`) are rejected by `byteSubLensPut`. -/
theorem zeroSizeByteLensPutRejected (allocId off alignLog2 : Nat)
    (m : MemoryState) (bs : List AllocByte) :
    byteSubLensPut ⟨allocId, off, 0, alignLog2⟩ m bs = none := rfl

/-- Read-only (`.shared`) allocations are rejected by `byteSubLensGet`. -/
theorem readonlyAllocByteLensRejected (L : ByteSubLens) (m : MemoryState)
    (a : Allocation)
    (hFind : findAllocationComp L.allocId m.allocations = some a)
    (hShared : a.mutability = .shared) :
    byteSubLensGet L m = none := by
  dsimp only [byteSubLensGet]
  cases Nat.blt 0 L.size with
  | false => rfl
  | true =>
    dsimp only
    rw [hFind]
    dsimp only
    rw [hShared]
    rfl

/-- Read-only (`.shared`) allocations are rejected by `byteSubLensPut`. -/
theorem readonlyAllocByteLensPutRejected (L : ByteSubLens) (m : MemoryState)
    (bs : List AllocByte) (a : Allocation)
    (hFind : findAllocationComp L.allocId m.allocations = some a)
    (hShared : a.mutability = .shared) :
    byteSubLensPut L m bs = none := by
  dsimp only [byteSubLensPut]
  cases hConj : (Nat.blt 0 L.size && Nat.beq bs.length L.size) with
  | false => rfl
  | true =>
    have hPos := bandLeft hConj
    have hLen := natEq_of_beq _ _ (bandRight hConj)
    dsimp only [writeBytesComp]
    rw [hLen, natBeq_zero_false_of_blt_zero L.size hPos,
        ite_bool_false rfl, hFind]
    dsimp only
    cases (!a.live || !isInBoundsComp a L.offset L.size ||
        !isAlignedComp a L.offset L.alignLog2) with
    | true => rfl
    | false =>
      rw [hShared]
      rfl

/-- Deallocated (`live = false`) allocations fail closed in `byteSubLensGet`. -/
theorem deadAllocByteLensRejected (L : ByteSubLens) (m : MemoryState)
    (a : Allocation)
    (hFind : findAllocationComp L.allocId m.allocations = some a)
    (hDead : a.live = false) :
    byteSubLensGet L m = none := by
  dsimp only [byteSubLensGet]
  cases hPos : Nat.blt 0 L.size with
  | false => rfl
  | true =>
    dsimp only
    rw [hFind]
    dsimp only
    cases mutabilityIsMut a.mutability with
    | false => rfl
    | true =>
      dsimp only [readBytesComp]
      rw [natBeq_zero_false_of_blt_zero L.size hPos,
          ite_bool_false rfl, hFind]
      dsimp only
      rw [hDead]
      rfl

/-- Out-of-bounds slices (`isInBoundsComp = false`) are rejected by
`byteSubLensGet`. -/
theorem outOfBoundsByteLensRejected (L : ByteSubLens) (m : MemoryState)
    (a : Allocation)
    (hFind : findAllocationComp L.allocId m.allocations = some a)
    (hOob : isInBoundsComp a L.offset L.size = false) :
    byteSubLensGet L m = none := by
  dsimp only [byteSubLensGet]
  cases hPos : Nat.blt 0 L.size with
  | false => rfl
  | true =>
    dsimp only
    rw [hFind]
    dsimp only
    cases mutabilityIsMut a.mutability with
    | false => rfl
    | true =>
      dsimp only [readBytesComp]
      rw [natBeq_zero_false_of_blt_zero L.size hPos,
          ite_bool_false rfl, hFind]
      dsimp only
      rw [hOob]
      cases a.live <;> rfl

/-- Misaligned slices (`isAlignedComp = false`) are rejected by
`byteSubLensGet`. -/
theorem unalignedByteLensRejected (L : ByteSubLens) (m : MemoryState)
    (a : Allocation)
    (hFind : findAllocationComp L.allocId m.allocations = some a)
    (hUnalign : isAlignedComp a L.offset L.alignLog2 = false) :
    byteSubLensGet L m = none := by
  dsimp only [byteSubLensGet]
  cases hPos : Nat.blt 0 L.size with
  | false => rfl
  | true =>
    dsimp only
    rw [hFind]
    dsimp only
    cases mutabilityIsMut a.mutability with
    | false => rfl
    | true =>
      dsimp only [readBytesComp]
      rw [natBeq_zero_false_of_blt_zero L.size hPos,
          ite_bool_false rfl, hFind]
      dsimp only
      rw [hUnalign]
      cases a.live <;> cases isInBoundsComp a L.offset L.size <;> rfl

/-- Length-mismatched writes (`Nat.beq bs.length L.size = false`) are rejected
by `byteSubLensPut`. -/
theorem wrongLengthByteLensPutRejected (L : ByteSubLens) (m : MemoryState)
    (bs : List AllocByte) (hLen : Nat.beq bs.length L.size = false) :
    byteSubLensPut L m bs = none := by
  dsimp only [byteSubLensPut]
  rw [hLen]
  cases Nat.blt 0 L.size <;> rfl

end Anneal.ByteSubLens

end
