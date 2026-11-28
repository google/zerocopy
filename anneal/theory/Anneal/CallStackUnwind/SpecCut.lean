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
public import Trusted
public import Trusted.MirAst
public import Trusted.MirModel
public import Trusted.MirSemantics
public import Anneal.Framework.StepWp
public import Anneal.MirWp
public import Anneal.ByteSubLens.Lens
public import Anneal.ByteRun.Copy
public import Anneal.RefFrame.Frame

public section

/-!
# Modular Call-Stack & Unwind Cleanup Framing (`Anneal.CallStackUnwind.SpecCut`)

Zero-`Prop`-argument `@[irreducible] CallSpecCut` contract boundaries,
`UpdatesOnly` sub-lens framing algebra over `Anneal.ByteSubLens`, and a
theory-layer multi-frame call-stack and unwind cleanup overlay over single-frame
`Trusted.MirSemantics.evalStep` and `Anneal.RefFrame.CallCont4`.

Scope note: `Trusted.MirSemantics.evalStep` is single-frame and its
`evalTerminator` faults `.unsupported` on `.call`, `.assert`, and
`.unwindResume` (while `evalStep_never_unwound` shows `evalStep` never produces
`.done (.unwound _)`). `StackStep` and `wpFrameOutcome` form a theory-layer
lens-scoped call/unwind overlay above `evalStep`: `StackStep.call_push` binds
callee locals through `CallImplBundle.mkLocals` (`.indirect` slices into the
caller's allocation) rather than `Val.ptr` dereferences; `StackStep.assert_*`
abstracts failed assertions directly to unwind/abort rather than invoking panic
lang items; `StackStep.unwind_root` models unwind propagation exiting the
modeled subtree to an outer enclosing boundary rather than whole-program root
unwind UB; intra-body edges assume `rustc` cleanup-edge validity without
tracking per-frame unwinding state; and frame exit omits stack-local
deallocation, unwind `_0` liveness checks, and Tree Borrows protector release.

All definitions are computable (`0` `noncomputable`, `0` `._unsafe_rec`). The
pure `UpdatesOnly`, `CallSpec`, and `evalCallExitStep` definitions and lemmas
use zero axioms (`[]`); declarations depending on `evalStep` or
`evalPrimitiveOperand` in `Trusted.MirSemantics` use at most `[propext]` (`0`
`Classical.choice`, `0` `Quot.sound`).
-/

namespace Anneal.CallStackUnwind

open Trusted.MirAst Trusted.MirSemantics
open Anneal.ByteSubLens Anneal.ByteRun Anneal.RefFrame

/-! ## 1. Internal Arithmetic, List-Splice, and Allocation Helpers -/

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

private theorem if_prop_true {b : Bool} (h : b = true) (x y : Prop) :
    (if b then x else y) = x := by
  cases h
  rfl

private theorem if_prop_false {b : Bool} (h : b = false) (x y : Prop) :
    (if b then x else y) = y := by
  cases h
  rfl

private theorem natBeq_refl (a : Nat) : Nat.beq a a = true := by
  induction a with
  | zero => rfl
  | succ _ ih => exact ih

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

private theorem natBeq_zero_false_of_blt_zero (n : Nat)
    (h : Nat.blt 0 n = true) : Nat.beq n 0 = false := by
  cases n with
  | zero => exact False.elim (boolFalseNeTrue h)
  | succ _ => rfl

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

private theorem natAdd_assoc (a b c : Nat) : (a + b) + c = a + (b + c) := by
  induction c with
  | zero => rfl
  | succ _ ih => exact congrArg Nat.succ ih

private theorem natBle_add_right (a b : Nat) : Nat.ble a (a + b) = true := by
  induction b with
  | zero => exact natBle_refl a
  | succ _ ih => exact natBle_succ_right a _ ih

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

private theorem listDrop_nil {α : Type} (n : Nat) :
    List.drop n ([] : List α) = [] := by
  cases n <;> rfl

private theorem listDrop_add {α : Type} (a b : Nat) (xs : List α) :
    xs.drop (a + b) = (xs.drop a).drop b := by
  revert xs
  induction a with
  | zero =>
    intro xs
    rw [natAdd_zero_left]
    rfl
  | succ a' ih =>
    intro xs
    rw [natAdd_succ_left]
    cases xs with
    | nil =>
      rw [listDrop_nil (a' + b + 1), listDrop_nil (a' + 1), listDrop_nil b]
    | cons _ tl =>
      change tl.drop (a' + b) = (tl.drop a').drop b
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
    have hLen := congrArg List.length (listTake_append_drop mid.length xs)
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
      change
        (hd :: (tl.take off' ++ mid ++ tl.drop (off' + mid.length))).length =
        tl.length + 1
      exact congrArg Nat.succ (ih tl h)

private theorem listTake_append_of_ge {α : Type} (n : Nat) (xs ys : List α)
    (h : Nat.ble xs.length n = true) :
    (xs ++ ys).take n = xs ++ ys.take (n - xs.length) := by
  revert n
  induction xs with
  | nil =>
    intro n _
    rfl
  | cons hd tl ih =>
    intro n h
    cases n with
    | zero => exact False.elim (boolFalseNeTrue h)
    | succ n' =>
      change hd :: ((tl ++ ys).take n') =
        hd :: (tl ++ ys.take ((n' + 1) - (tl.length + 1)))
      rw [Nat.succ_sub_succ]
      exact congrArg (List.cons hd) (ih n' h)

private theorem listTake_append_of_le {α : Type} (n : Nat) (xs ys : List α)
    (h : Nat.ble n xs.length = true) :
    (xs ++ ys).take n = xs.take n := by
  revert n
  induction xs with
  | nil =>
    intro n h
    cases n with
    | zero => rfl
    | succ _ => exact False.elim (boolFalseNeTrue h)
  | cons hd tl ih =>
    intro n h
    cases n with
    | zero => rfl
    | succ n' => exact congrArg (List.cons hd) (ih n' h)

private theorem listDrop_append_of_le {α : Type} (n : Nat) (xs ys : List α)
    (h : Nat.ble n xs.length = true) :
    (xs ++ ys).drop n = xs.drop n ++ ys := by
  revert n
  induction xs with
  | nil =>
    intro n h
    cases n with
    | zero => rfl
    | succ _ => exact False.elim (boolFalseNeTrue h)
  | cons _ tl ih =>
    intro n h
    cases n with
    | zero => rfl
    | succ n' => exact ih n' h

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

private theorem listSplice_take_drop_self {α : Type} (off sz : Nat)
    (xs : List α) :
    xs.take off ++ ((xs.drop off).take sz) ++ xs.drop (off + sz) = xs := by
  rw [listAppend_assoc, listDrop_add off sz xs]
  rw [listTake_append_drop sz (xs.drop off)]
  exact listTake_append_drop off xs

private theorem listSplice_nested {α : Type} (off1 off2 : Nat)
    (bs1 bs2 xs : List α)
    (h1 : Nat.ble (off1 + bs1.length) xs.length = true)
    (hOff : Nat.ble off1 off2 = true)
    (hSub : Nat.ble ((off2 - off1) + bs2.length) bs1.length = true) :
    let xs1 := xs.take off1 ++ bs1 ++ xs.drop (off1 + bs1.length)
    let d := off2 - off1
    let bs1' := bs1.take d ++ bs2 ++ bs1.drop (d + bs2.length)
    xs1.take off2 ++ bs2 ++ xs1.drop (off2 + bs2.length) =
      xs.take off1 ++ bs1' ++ xs.drop (off1 + bs1.length) := by
  dsimp only
  have hOff1Le : Nat.ble off1 xs.length = true :=
    natBle_trans off1 (off1 + bs1.length) xs.length
      (natBle_add_right off1 bs1.length) h1
  have hTake1Len : (xs.take off1).length = off1 :=
    listTake_length_of_ble off1 xs hOff1Le
  have hOff2Eq : off1 + (off2 - off1) = off2 :=
    natSub_add_cancel_of_ble off1 off2 hOff
  have hDLe : Nat.ble (off2 - off1) bs1.length = true :=
    natBle_trans (off2 - off1) ((off2 - off1) + bs2.length) bs1.length
      (natBle_add_right (off2 - off1) bs2.length) hSub
  have hPreLen : (xs.take off1 ++ bs1).length = off1 + bs1.length := by
    rw [listLength_append, hTake1Len]
  have hOff2LePre : Nat.ble off2 (xs.take off1 ++ bs1).length = true := by
    rw [hPreLen, ← hOff2Eq]
    have hMono : ∀ (k a b : Nat), Nat.ble a b = true →
        Nat.ble (k + a) (k + b) = true := by
      intro k
      induction k with
      | zero =>
        intro a b h
        rw [natAdd_zero_left, natAdd_zero_left]
        exact h
      | succ k' ih =>
        intro a b h
        rw [natAdd_succ_left, natAdd_succ_left]
        exact ih a b h
    exact hMono off1 (off2 - off1) bs1.length hDLe
  have hTakeAt2 :
      (xs.take off1 ++ bs1 ++ xs.drop (off1 + bs1.length)).take off2 =
      xs.take off1 ++ bs1.take (off2 - off1) := by
    rw [listTake_append_of_le off2 (xs.take off1 ++ bs1) _ hOff2LePre]
    have hGe1 : Nat.ble (xs.take off1).length off2 = true := by
      rw [hTake1Len]
      exact hOff
    rw [listTake_append_of_ge off2 (xs.take off1) bs1 hGe1, hTake1Len]
  have hEnd2LePre :
      Nat.ble (off2 + bs2.length) (xs.take off1 ++ bs1).length = true := by
    rw [hPreLen, ← hOff2Eq, natAdd_assoc]
    have hMono : ∀ (k a b : Nat), Nat.ble a b = true →
        Nat.ble (k + a) (k + b) = true := by
      intro k
      induction k with
      | zero =>
        intro a b h
        rw [natAdd_zero_left, natAdd_zero_left]
        exact h
      | succ k' ih =>
        intro a b h
        rw [natAdd_succ_left, natAdd_succ_left]
        exact ih a b h
    exact hMono off1 ((off2 - off1) + bs2.length) bs1.length hSub
  have hDropAt2 :
      (xs.take off1 ++ bs1 ++ xs.drop (off1 + bs1.length)).drop
        (off2 + bs2.length) =
      bs1.drop ((off2 - off1) + bs2.length) ++ xs.drop (off1 + bs1.length) := by
    rw [listDrop_append_of_le (off2 + bs2.length) (xs.take off1 ++ bs1) _
      hEnd2LePre]
    have hGe1 : Nat.ble (xs.take off1).length (off2 + bs2.length) = true := by
      rw [hTake1Len]
      exact natBle_trans off1 off2 (off2 + bs2.length) hOff
        (natBle_add_right off2 bs2.length)
    rw [listDrop_append_ge (off2 + bs2.length) (xs.take off1) bs1 hGe1,
      hTake1Len]
    have hSubEq : (off2 + bs2.length) - off1 = (off2 - off1) + bs2.length := by
      have hSubAdd : ∀ (k y : Nat), (k + y) - k = y := by
        intro k
        induction k with
        | zero =>
          intro y
          rw [natAdd_zero_left]
          rfl
        | succ k' ih =>
          intro y
          rw [natAdd_succ_left, Nat.succ_sub_succ]
          exact ih y
      have hL : off2 + bs2.length = off1 + ((off2 - off1) + bs2.length) := by
        rw [← natAdd_assoc, hOff2Eq]
      rw [hL]
      exact hSubAdd off1 ((off2 - off1) + bs2.length)
    rw [hSubEq]
  rw [hTakeAt2, hDropAt2]
  rw [listAppend_assoc, listAppend_assoc, listAppend_assoc, listAppend_assoc,
    listAppend_assoc]

private theorem findAllocation_allocId (id : AllocId)
    (allocs : List Allocation) (a : Allocation)
    (hFind : findAllocation id allocs = some a) : a.allocId = id := by
  induction allocs with
  | nil => cases hFind
  | cons hd tl ih =>
    dsimp only [findAllocation] at hFind
    cases hEq : Nat.beq hd.allocId id with
    | true =>
      rw [ite_bool_true hEq] at hFind
      injection hFind with hA
      rw [← hA]
      exact natEq_of_beq hd.allocId id hEq
    | false =>
      rw [ite_bool_false hEq] at hFind
      exact ih hFind

private theorem findAllocation_replaceAllocation_ne (otherId : AllocId)
    (allocs : List Allocation) (a' : Allocation)
    (hNe : Nat.beq a'.allocId otherId = false) :
    findAllocation otherId (replaceAllocation a' allocs) =
      findAllocation otherId allocs := by
  induction allocs with
  | nil => rfl
  | cons hd tl ih =>
    dsimp only [replaceAllocation]
    cases hEq : Nat.beq hd.allocId a'.allocId with
    | true =>
      rw [ite_bool_true rfl]
      have hHdEq : hd.allocId = a'.allocId := natEq_of_beq _ _ hEq
      have hHdNe : Nat.beq hd.allocId otherId = false := by
        rw [hHdEq]
        exact hNe
      dsimp only [findAllocation]
      rw [ite_bool_false hNe, ite_bool_false hHdNe]
    | false =>
      rw [ite_bool_false rfl]
      dsimp only [findAllocation]
      cases hOther : Nat.beq hd.allocId otherId with
      | true => rfl
      | false =>
        rw [ite_bool_false rfl, ite_bool_false rfl]
        exact ih

private theorem writeBytes_ok_inversion (m m' : MemoryState) (place : MemPlace)
    (alignLog2 : Nat) (bs : List AllocByte)
    (hPos : Nat.blt 0 bs.length = true)
    (hWrite : writeBytes m place alignLog2 bs = .ok m') :
    ∃ a : Allocation,
      findAllocation place.allocId m.allocations = some a ∧
      a.mutability = .mut ∧
      a.live = true ∧
      isInBounds a place.offset bs.length = true ∧
      isAligned a place.offset alignLog2 = true ∧
      m' = MemoryState.mk m.nextAllocId
        (replaceAllocation
          (Allocation.mk a.allocId a.alignLog2 .mut
            (a.bytes.take place.offset ++ bs ++
              a.bytes.drop (place.offset + bs.length))
            true)
          m.allocations) := by
  dsimp only [writeBytes] at hWrite
  cases hFind : findAllocation place.allocId m.allocations with
  | none => rw [hFind] at hWrite; cases hWrite
  | some a =>
    rw [hFind] at hWrite
    dsimp only at hWrite
    rw [natBeq_zero_false_of_blt_zero bs.length hPos,
      ite_bool_false rfl] at hWrite
    cases hGuard :
        (!a.live || !isInBounds a place.offset bs.length ||
          !isAligned a place.offset alignLog2) with
    | true => rw [ite_bool_true hGuard] at hWrite; cases hWrite
    | false =>
      rw [ite_bool_false hGuard] at hWrite
      have hG1 := borFalseElim hGuard
      have hG2 := borFalseElim hG1.1
      have hLive : a.live = true := by
        cases hl : a.live with
        | true => rfl
        | false => rw [hl] at hG2; exact False.elim (boolTrueNeFalse hG2.1)
      have hBounds : isInBounds a place.offset bs.length = true := by
        cases hb : isInBounds a place.offset bs.length with
        | true => rfl
        | false => rw [hb] at hG2; exact False.elim (boolTrueNeFalse hG2.2)
      have hAlign : isAligned a place.offset alignLog2 = true := by
        cases ha : isAligned a place.offset alignLog2 with
        | true => rfl
        | false => rw [ha] at hG1; exact False.elim (boolTrueNeFalse hG1.2)
      have hMutCase : a.mutability = .mut ∧
          m' = MemoryState.mk m.nextAllocId
            (replaceAllocation
              (Allocation.mk a.allocId a.alignLog2 a.mutability
                (a.bytes.take place.offset ++ bs ++
                  a.bytes.drop (place.offset + bs.length))
                a.live)
              m.allocations) :=
        @Mutability.casesOn
          (fun mu =>
            (match mu with
              | .shared => Except.error FaultKind.undefined
              | .mut =>
                Except.ok (MemoryState.mk m.nextAllocId
                  (replaceAllocation
                    (Allocation.mk a.allocId a.alignLog2 mu
                      (a.bytes.take place.offset ++ bs ++
                        a.bytes.drop (place.offset + bs.length))
                      a.live)
                    m.allocations))) = Except.ok m' →
            mu = .mut ∧
            m' = MemoryState.mk m.nextAllocId
              (replaceAllocation
                (Allocation.mk a.allocId a.alignLog2 mu
                  (a.bytes.take place.offset ++ bs ++
                    a.bytes.drop (place.offset + bs.length))
                  a.live)
                m.allocations))
          a.mutability
          (fun hBad => by cases hBad)
          (fun hOk => by injection hOk with hM; exact ⟨rfl, hM.symm⟩)
          hWrite
      have hM' : m' = MemoryState.mk m.nextAllocId
          (replaceAllocation
            (Allocation.mk a.allocId a.alignLog2 .mut
              (a.bytes.take place.offset ++ bs ++
                a.bytes.drop (place.offset + bs.length))
              true)
            m.allocations) := by
        have hTmp := hMutCase.2
        rw [hMutCase.1, hLive] at hTmp
        exact hTmp
      exact ⟨a, rfl, hMutCase.1, hLive, hBounds, hAlign, hM'⟩

private theorem byteSubLensGet_inversion_mir (L : ByteSubLens)
    (m : MemoryState) (bs : List AllocByte)
    (hGet : byteSubLensGet L m = some bs) :
    Nat.blt 0 L.size = true ∧
    bs.length = L.size ∧
    ∃ a : Allocation,
      findAllocation L.allocId m.allocations = some a ∧
      a.mutability = .mut ∧
      a.live = true ∧
      isInBounds a L.offset L.size = true ∧
      isAligned a L.offset L.alignLog2 = true ∧
      bs = (a.bytes.drop L.offset).take L.size := by
  rw [byteSubLensGet_eq_mir] at hGet
  cases hPos : Nat.blt 0 L.size with
  | false => rw [hPos] at hGet; cases hGet
  | true =>
    rw [hPos] at hGet
    dsimp only at hGet
    cases hFind : findAllocation L.allocId m.allocations with
    | none => rw [hFind] at hGet; cases hGet
    | some a =>
      rw [hFind] at hGet
      dsimp only at hGet
      have hMutCase : a.mutability = .mut ∧
          (match readBytes m ⟨L.allocId, L.offset⟩ L.size L.alignLog2 with
           | .ok bs' => some bs'
           | .error _ => none) = some bs :=
        @Mutability.casesOn
          (fun mu =>
            (match mutabilityIsMut mu with
             | false => none
             | true =>
               match readBytes m ⟨L.allocId, L.offset⟩ L.size L.alignLog2 with
               | .ok bs' => some bs'
               | .error _ => none) = some bs →
            mu = .mut ∧
            (match readBytes m ⟨L.allocId, L.offset⟩ L.size L.alignLog2 with
             | .ok bs' => some bs'
             | .error _ => none) = some bs)
          a.mutability
          (fun hBad => by cases hBad)
          (fun hOk => ⟨rfl, hOk⟩)
          hGet
      have hReadSome := hMutCase.2
      dsimp only [readBytes] at hReadSome
      rw [hFind] at hReadSome
      dsimp only at hReadSome
      rw [natBeq_zero_false_of_blt_zero L.size hPos,
        ite_bool_false rfl] at hReadSome
      cases hGuard :
          (!a.live || !isInBounds a L.offset L.size ||
            !isAligned a L.offset L.alignLog2) with
      | true => rw [ite_bool_true hGuard] at hReadSome; cases hReadSome
      | false =>
        rw [ite_bool_false hGuard] at hReadSome
        injection hReadSome with hEq
        have hG1 := borFalseElim hGuard
        have hG2 := borFalseElim hG1.1
        have hLive : a.live = true := by
          cases hl : a.live with
          | true => rfl
          | false => rw [hl] at hG2; exact False.elim (boolTrueNeFalse hG2.1)
        have hBounds : isInBounds a L.offset L.size = true := by
          cases hb : isInBounds a L.offset L.size with
          | true => rfl
          | false => rw [hb] at hG2; exact False.elim (boolTrueNeFalse hG2.2)
        have hAlign : isAligned a L.offset L.alignLog2 = true := by
          cases ha : isAligned a L.offset L.alignLog2 with
          | true => rfl
          | false => rw [ha] at hG1; exact False.elim (boolTrueNeFalse hG1.2)
        have hLen : bs.length = L.size := by
          rw [← hEq]
          exact listDrop_take_length_of_ble L.offset L.size a.bytes hBounds
        exact ⟨rfl, hLen, a, rfl, hMutCase.1, hLive, hBounds, hAlign, hEq.symm⟩

private theorem byteSubLensPut_inversion_mir (L : ByteSubLens)
    (m m' : MemoryState) (bs : List AllocByte)
    (hPut : byteSubLensPut L m bs = some m') :
    Nat.blt 0 L.size = true ∧
    bs.length = L.size ∧
    writeBytes m ⟨L.allocId, L.offset⟩ L.alignLog2 bs = .ok m' := by
  rw [byteSubLensPut_eq_mir] at hPut
  cases hPos : Nat.blt 0 L.size with
  | false => rw [hPos] at hPut; cases hPut
  | true =>
    cases hLen : Nat.beq bs.length L.size with
    | false => rw [hPos, hLen] at hPut; cases hPut
    | true =>
      rw [hPos, hLen] at hPut
      dsimp only [Bool.and] at hPut
      cases hW : writeBytes m ⟨L.allocId, L.offset⟩ L.alignLog2 bs with
      | error _ => rw [hW] at hPut; cases hPut
      | ok res =>
        rw [hW] at hPut
        injection hPut with hM
        subst hM
        exact ⟨rfl, natEq_of_beq bs.length L.size hLen, rfl⟩

private theorem findAllocation_after_writeBytes_external (m m' : MemoryState)
    (place : MemPlace) (alignLog2 : Nat) (bs : List AllocByte)
    (extId : AllocId) (hPos : Nat.blt 0 bs.length = true)
    (hNe : Nat.beq place.allocId extId = false)
    (hWrite : writeBytes m place alignLog2 bs = .ok m') :
    findAllocation extId m'.allocations = findAllocation extId m.allocations :=
  by
  cases writeBytes_ok_inversion m m' place alignLog2 bs hPos hWrite with
  | intro a hA =>
    have hAllocId := findAllocation_allocId place.allocId m.allocations a hA.1
    rw [hA.2.2.2.2.2]
    dsimp only
    exact findAllocation_replaceAllocation_ne extId m.allocations _
      (by rw [hAllocId]; exact hNe)

/-- Total structural `List.foldr` indexing (`0` `noncomputable`). -/
@[expose] def getElemComp? {α : Type} (xs : List α) (idx : Nat) : Option α :=
  xs.foldr
    (fun x ih k =>
      match k with
      | 0 => some x
      | k' + 1 => ih k')
    (fun _ => none) idx

private theorem getElem_self_length_none {α : Type} :
    ∀ (xs : List α), Trusted.MirSemantics.getElem? xs xs.length = none
  | [] => rfl
  | _ :: xs => getElem_self_length_none xs

/-! ## 2. Exact Sub-Lens Modification Framing (`UpdatesOnly`) -/

/-- Exact byte-lens framing predicate: `mOut` is obtained from `mIn` solely by
writing a valid slice of length `L.size` through `byteSubLensPut L`. -/
@[expose] def UpdatesOnly (L : ByteSubLens) (mIn mOut : MemoryState) : Prop :=
  ∃ bs : List AllocByte, byteSubLensPut L mIn bs = some mOut

/-- Reflexivity of `UpdatesOnly` on any memory state where `byteSubLensGet L`
succeeds. -/
theorem updatesOnly_refl (L : ByteSubLens) (m : MemoryState)
    (pre : List AllocByte) (hGet : byteSubLensGet L m = some pre) :
    UpdatesOnly L m m :=
  ⟨pre, byteSubLens_get_put L m pre hGet⟩

/-- Introduction of `UpdatesOnly` from a single `byteSubLensPut`. -/
theorem updatesOnly_of_put (L : ByteSubLens) (m m' : MemoryState)
    (bs : List AllocByte) (hPut : byteSubLensPut L m bs = some m') :
    UpdatesOnly L m m' :=
  ⟨bs, hPut⟩

/-- Transitivity of `UpdatesOnly` via the `byteSubLens_put_put` law. -/
theorem updatesOnly_trans (L : ByteSubLens) (m0 m1 m2 : MemoryState)
    (h1 : UpdatesOnly L m0 m1) (h2 : UpdatesOnly L m1 m2) :
    UpdatesOnly L m0 m2 := by
  cases h1 with
  | intro bs1 hPut1 =>
    cases h2 with
    | intro bs2 hPut2 =>
      exact ⟨bs2, Eq.trans (byteSubLens_put_put L m0 m1 bs1 bs2 hPut1).symm
        hPut2⟩

/-- Hierarchical sub-lens monotonicity: any update confined to a contained
sub-lens `subL ⊆ bigL` is confined to `bigL`. -/
theorem updatesOnly_mono_sublens (subL bigL : ByteSubLens)
    (m0 m1 : MemoryState)
    (hSub : subLensContained subL bigL = true)
    (hGetBig : ∃ preBig, byteSubLensGet bigL m0 = some preBig)
    (hUpdSub : UpdatesOnly subL m0 m1) :
    UpdatesOnly bigL m0 m1 := by
  cases hGetBig with
  | intro preBig hGetBigEq =>
    cases hUpdSub with
    | intro bsSub hPutSub =>
      have hBigInv := byteSubLensGet_inversion_mir bigL m0 preBig hGetBigEq
      have hSubInv := byteSubLensPut_inversion_mir subL m0 m1 bsSub hPutSub
      dsimp only [subLensContained] at hSub
      have hS1 := bandLeft hSub
      have hS2 := bandLeft hS1
      have hIdEq : subL.allocId = bigL.allocId :=
        natEq_of_beq subL.allocId bigL.allocId (bandLeft hS2)
      have hOffLe : Nat.ble bigL.offset subL.offset = true := bandRight hS1
      have hEndLe :
          Nat.ble (subL.offset + subL.size) (bigL.offset + bigL.size) = true :=
        bandRight hSub
      have hBigPos := hBigInv.1
      have hBigLen := hBigInv.2.1
      have hSubPos := hSubInv.1
      have hSubLen := hSubInv.2.1
      cases hBigInv.2.2 with
      | intro aBig hABig =>
        have hFindBig := hABig.1
        have hMutBig := hABig.2.1
        have hLiveBig := hABig.2.2.1
        have hBoundsBig := hABig.2.2.2.1
        have hAlignBig := hABig.2.2.2.2.1
        have hPreEq := hABig.2.2.2.2.2
        have hBsSubPos : Nat.blt 0 bsSub.length = true := by
          rw [hSubLen]; exact hSubPos
        cases writeBytes_ok_inversion m0 m1 ⟨subL.allocId, subL.offset⟩
            subL.alignLog2 bsSub hBsSubPos hSubInv.2.2 with
        | intro aSub hASub =>
          have hFindSub : findAllocation bigL.allocId m0.allocations =
              some aSub := by
            rw [← hIdEq]; exact hASub.1
          have hEqAlloc : aSub = aBig := by
            have hTmp := Eq.trans hFindSub.symm hFindBig
            injection hTmp
          let d := subL.offset - bigL.offset
          let newBig := preBig.take d ++ bsSub ++ preBig.drop (d + bsSub.length)
          have hDSubLe :
              Nat.ble (d + bsSub.length) preBig.length = true := by
            rw [hBigLen, hSubLen]
            have hSum : bigL.offset + (d + subL.size) =
                subL.offset + subL.size := by
              rw [← natAdd_assoc,
                natSub_add_cancel_of_ble bigL.offset subL.offset hOffLe]
            have hTmp := hEndLe
            rw [← hSum] at hTmp
            have hCancel : ∀ (k x y : Nat),
                Nat.ble (k + x) (k + y) = true → Nat.ble x y = true := by
              intro k
              induction k with
              | zero =>
                intro x y hk
                rw [natAdd_zero_left, natAdd_zero_left] at hk
                exact hk
              | succ k' ih =>
                intro x y hk
                rw [natAdd_succ_left, natAdd_succ_left] at hk
                exact ih x y hk
            exact hCancel bigL.offset (d + subL.size) bigL.size hTmp
          have hNewLen : newBig.length = bigL.size := by
            dsimp only [newBig]
            rw [listSplice_length d bsSub preBig hDSubLe, hBigLen]
          have hBsBigBounds :
              isInBounds aBig bigL.offset preBig.length = true := by
            dsimp only [isInBounds]; rw [hBigLen]; exact hBoundsBig
          have hPreSplice := listSplice_nested bigL.offset subL.offset preBig
            bsSub aBig.bytes hBsBigBounds hOffLe hDSubLe
          dsimp only at hPreSplice
          have hIdentity :
              aBig.bytes.take bigL.offset ++ preBig ++
                aBig.bytes.drop (bigL.offset + preBig.length) = aBig.bytes := by
            rw [hBigLen, hPreEq]
            exact listSplice_take_drop_self bigL.offset bigL.size aBig.bytes
          rw [hIdentity] at hPreSplice
          have hM1Eq : m1 = MemoryState.mk m0.nextAllocId
              (replaceAllocation
                (Allocation.mk aBig.allocId aBig.alignLog2 .mut
                  (aBig.bytes.take bigL.offset ++ newBig ++
                    aBig.bytes.drop (bigL.offset + newBig.length)) true)
                m0.allocations) := by
            rw [hASub.2.2.2.2.2, hEqAlloc, hNewLen, ← hBigLen]
            dsimp only [newBig]
            rw [← hPreSplice]
          cases byteSubLensPut_eq_some_of_valid bigL m0 newBig aBig hBigPos
              hNewLen hFindBig hMutBig hLiveBig hBoundsBig hAlignBig with
          | intro m1' hPutBig' =>
            have hInvBig' :=
              byteSubLensPut_inversion_mir bigL m0 m1' newBig hPutBig'.1
            have hNewBigPos : Nat.blt 0 newBig.length = true := by
              rw [hNewLen]; exact hBigPos
            cases writeBytes_ok_inversion m0 m1' ⟨bigL.allocId, bigL.offset⟩
                bigL.alignLog2 newBig hNewBigPos hInvBig'.2.2 with
            | intro aBig' hABig' =>
              have hEqA' : aBig' = aBig := by
                have hTmp := Eq.trans hABig'.1.symm hFindBig
                injection hTmp
              have hEqM : m1 = m1' := by
                rw [hM1Eq, hABig'.2.2.2.2.2, hEqA']
              rw [hEqM]
              exact ⟨newBig, hPutBig'.1⟩

/-- Frame preservation outside `L`: an `UpdatesOnly L mIn mOut` transition
preserves `byteSubLensGet` and `readBytes` on every disjoint lens `otherL` and
preserves `findAllocation` on every external `allocId ≠ L.allocId`. -/
theorem updatesOnly_preserves_outside (L : ByteSubLens)
    (mIn mOut : MemoryState) (hUpd : UpdatesOnly L mIn mOut) :
    (∀ otherL : ByteSubLens, byteLensDisjoint L otherL = true →
      byteSubLensGet otherL mOut = byteSubLensGet otherL mIn ∧
      readBytes mOut ⟨otherL.allocId, otherL.offset⟩ otherL.size
          otherL.alignLog2 =
        readBytes mIn ⟨otherL.allocId, otherL.offset⟩ otherL.size
          otherL.alignLog2) ∧
    (∀ extId : AllocId, Nat.beq extId L.allocId = false →
      findAllocation extId mOut.allocations =
        findAllocation extId mIn.allocations) := by
  cases hUpd with
  | intro bs hPut =>
    have hInv := byteSubLensPut_inversion_mir L mIn mOut bs hPut
    have hBsPos : Nat.blt 0 bs.length = true := by
      rw [hInv.2.1]; exact hInv.1
    refine ⟨?_, ?_⟩
    · intro otherL hDisj
      have hDisjBs :
          (!Nat.beq L.allocId otherL.allocId ||
            Anneal.ByteRun.rangesDisjoint L.offset bs.length otherL.offset
              otherL.size) = true := by
        rw [hInv.2.1]; exact hDisj
      exact ⟨byteSubLens_get_put_disjoint L otherL mIn mOut bs hDisj hPut,
        readBytes_after_writeBytes_disjoint mIn mOut ⟨L.allocId, L.offset⟩
          ⟨otherL.allocId, otherL.offset⟩ L.alignLog2 otherL.size
          otherL.alignLog2 bs hBsPos hDisjBs hInv.2.2⟩
    · intro extId hExtNe
      have hNe' : Nat.beq L.allocId extId = false := by
        cases hEq : Nat.beq L.allocId extId with
        | false => rfl
        | true =>
          have hIdEq := natEq_of_beq L.allocId extId hEq
          rw [hIdEq, natBeq_refl extId] at hExtNe
          exact hExtNe
      exact findAllocation_after_writeBytes_external mIn mOut
        ⟨L.allocId, L.offset⟩ L.alignLog2 bs extId hBsPos hNe' hInv.2.2

/-- Validity witness after an `UpdatesOnly` transition: `bigL` remains readable
via both `byteSubLensGet` and `readBytes`, backed by a live mutable in-bounds
aligned allocation `a1` in `m1`. -/
theorem lens_valid_after_updatesOnly (bigL : ByteSubLens)
    (m0 m1 : MemoryState) (hUpd : UpdatesOnly bigL m0 m1) :
    ∃ (bs1 : List AllocByte) (a1 : Allocation),
      byteSubLensGet bigL m1 = some bs1 ∧
      readBytes m1 ⟨bigL.allocId, bigL.offset⟩ bigL.size bigL.alignLog2 =
        .ok bs1 ∧
      findAllocation bigL.allocId m1.allocations = some a1 ∧
      a1.mutability = .mut ∧
      a1.live = true ∧
      isInBounds a1 bigL.offset bigL.size = true ∧
      isAligned a1 bigL.offset bigL.alignLog2 = true := by
  cases hUpd with
  | intro bs hPut =>
    have hInv := byteSubLensPut_inversion_mir bigL m0 m1 bs hPut
    have hBsPos : Nat.blt 0 bs.length = true := by
      rw [hInv.2.1]; exact hInv.1
    have hRead := readBytes_after_writeBytes_same m0 m1
      ⟨bigL.allocId, bigL.offset⟩ bigL.alignLog2 bs hBsPos hInv.2.2
    rw [hInv.2.1] at hRead
    have hGet : byteSubLensGet bigL m1 = some bs :=
      byteSubLens_put_get bigL m0 m1 bs hPut
    have hGetInv := byteSubLensGet_inversion_mir bigL m1 bs hGet
    cases hGetInv.2.2 with
    | intro a1 hA1 =>
      exact ⟨bs, a1, hGet, hRead, hA1.1, hA1.2.1, hA1.2.2.1,
        hA1.2.2.2.1, hA1.2.2.2.2.1⟩

/-! ## 3. Pure-Data `CallSpec`, `CallCont4` Dispatch, and `wpFrameOutcome` -/

/-- Pure-data callee contract over `Trusted.MirSemantics.MemoryState` byte
slices (`0` `Prop` fields). -/
structure CallSpec where
  /-- Callee MIR definition identifier. -/
  calleeDefId : DefId
  /-- Mutable sub-allocation byte slice owned by the callee. -/
  mutLens : ByteSubLens
  /-- Computable entry precondition over `(preBytes, argVals)`. -/
  precondBool : List AllocByte → List Val → Bool
  /-- Computable normal-return postcondition over
  `(preBytes, retVal, postBytes, argVals)`. -/
  ensuresNormalBool : List AllocByte → Val → List AllocByte → List Val → Bool
  /-- Computable unwind postcondition over
  `(preBytes, postPartialBytes, argVals)`. -/
  ensuresUnwindBool : List AllocByte → List AllocByte → List Val → Bool
  /-- Whether normal return is permitted by this contract. -/
  canNormal : Bool
  /-- Whether panic unwind is permitted by this contract. -/
  canUnwind : Bool

/-- Pure-data callee implementation bundle (`0` `Prop` fields). -/
structure CallImplBundle where
  /-- Callee MIR `Body`. -/
  body : Body
  /-- Intra-frame fuel bound for verifying `body`. -/
  fuel : Nat
  /-- Entry frame local initializer from `(mutLens, argVals)`. -/
  mkLocals : ByteSubLens → List Val → List LocalSlot

/-- Computable `DefId`-keyed lookup over a callee specification list. -/
@[expose] def calleeLookup (specs : List CallSpec) (id : DefId) : Option
    CallSpec :=
  specs.foldr
    (fun spec acc => if Nat.beq spec.calleeDefId id then some spec else acc)
    none

/-- Computable `DefId`-keyed lookup over a callee implementation table. -/
@[expose] def implLookup (entries : List (DefId × CallImplBundle × List
    CallSpec))
    (targetId : DefId) : Option (CallImplBundle × List CallSpec) :=
  entries.foldr
    (fun entry acc =>
      if Nat.beq entry.1 targetId then some (entry.2.1, entry.2.2) else acc)
    none

/-- Callee exit kind entering the caller's `CallCont4` boundary. -/
inductive CalleeOutcome where
  | normal (retVal : Val) (memAfterCallee : MemoryState)
  | unwind (memAfterCallee : MemoryState)

/-- Caller continuation step across all `(onRet, onUnwind)` call regimes. -/
inductive CallContStep where
  | stepNormal (targetBb : BasicBlockId) (retVal : Val) (mem : MemoryState)
  | stepCleanup (cleanupBb : BasicBlockId) (mem : MemoryState)
  | exitUnwind (mem : MemoryState)
  | exitTerminate (mem : MemoryState)
  | fault (kind : FaultKind)

/-- Checks that `bbIdx` refers to an existing basic block in `body` with
`cleanup = true`. -/
@[expose] def checkCleanupBlock (body : Body) (bbIdx : BasicBlockId) : Bool :=
  match getElemComp? body.basicBlocks bbIdx with
  | none => false
  | some bb => bb.cleanup

/-- Evaluates the caller-side continuation of a call or assert exit across all
4 `CallCont4` regimes, failing closed on non-cleanup targets. -/
@[expose] def evalCallExitStep (body : Body) (cont : CallCont4) (out :
    CalleeOutcome) :
    CallContStep :=
  match out with
  | .normal retVal mem' =>
    match cont.onRet with
    | none => .fault .undefined
    | some retBb => .stepNormal retBb retVal mem'
  | .unwind mem' =>
    match cont.onUnwind with
    | .unreachable => .fault .undefined
    | .terminate => .exitTerminate mem'
    | .continue_ => .exitUnwind mem'
    | .cleanup cleanupBb =>
      if checkCleanupBlock body cleanupBb then
        .stepCleanup cleanupBb mem'
      else
        .fault .undefined

/-- Evaluates call argument operands left-to-right using
`Trusted.MirSemantics.evalPrimitiveOperand`. -/
inductive EvalCallArgs (bodyLocals : List MirTy) :
    List LocalSlot → MemoryState → List Operand →
      List Val → List LocalSlot → MemoryState → Prop where
  | nil {locals : List LocalSlot} {mem : MemoryState} :
      EvalCallArgs bodyLocals locals mem [] [] locals mem
  | cons {op : Operand} {rest : List Operand}
      {locals locals₁ locals₂ : List LocalSlot}
      {mem mem₁ mem₂ : MemoryState} {v : Val} {vs : List Val} :
      evalPrimitiveOperand bodyLocals locals mem op =
        .ok (v, locals₁, mem₁) →
      EvalCallArgs bodyLocals locals₁ mem₁ rest vs locals₂ mem₂ →
      EvalCallArgs bodyLocals locals mem (op :: rest) (v :: vs) locals₂ mem₂

/-- Frame terminal outcome covering normal return, panic unwind, and abort
termination. -/
inductive FrameTermOut where
  | returned (retVal : Val) (mem : MemoryState)
  | unwound (mem : MemoryState)
  | abortTerminate (mem : MemoryState)

/-- Theory-layer intra-frame and modular call/assert/unwind weakest precondition
wrapping `Trusted.MirSemantics.evalStep (Anneal.MirWp.bodyProg body) 0 st` for
all intra-frame steps and sealing nested calls via `env : DefId → Option
CallSpec` with `subLensContained` framing. On `.call` terminators, static
destination typing is checked unconditionally and runtime `writePlace` is
checked on normal-return paths (`canNormal = true`); unwind-only calls
(`canNormal = false`) do not write to `dst`. -/
@[expose] def wpFrameOutcome (callerLens : ByteSubLens)
    (env : DefId → Option CallSpec) (body : Body)
    (fuel : Nat) (s : State) (onDone : FrameTermOut → Prop) : Prop :=
  @Nat.rec (fun _ => State → Prop)
    (fun _ => False)
    (fun _ ih st =>
      match st.frames with
      | [] => False
      | frame :: restFrames =>
      match restFrames with
      | _ :: _ => False
      | [] =>
        match frame.sysrootOp? with
        | some _ =>
          match evalStep (Anneal.MirWp.bodyProg body) 0 st with
          | .step st' => ih st'
          | .done (.returned rv) => onDone (.returned rv.ret st.mem)
          | .done (.unwound _) => False
          | .done (.aborted _) => False
          | .fault _ => False
        | none =>
        match Trusted.MirSemantics.getElem? body.basicBlocks
            frame.blockIdx with
        | none => False
        | some bb =>
          if Nat.beq frame.stmtIdx bb.statements.length then
            match bb.terminator with
            | .call callee args dst onRet onUnwind =>
              if !dst.projection.isEmpty then
                False
              else
                match Trusted.MirSemantics.getElem? body.locals dst.localId with
                | none => False
                | some dstTy =>
                  match env callee with
                  | none => False
                  | some cSpec =>
                    subLensContained cSpec.mutLens callerLens = true ∧
                    ∃ argVals localsArgs memArgs,
                      EvalCallArgs body.locals frame.locals st.mem args
                        argVals localsArgs memArgs ∧
                      ∃ preBytes,
                        byteSubLensGet cSpec.mutLens memArgs = some preBytes ∧
                        cSpec.precondBool preBytes argVals = true ∧
                        (cSpec.canNormal = true →
                          ∀ retVal memAfter,
                            UpdatesOnly cSpec.mutLens memArgs memAfter →
                            (∃ postBytes,
                              byteSubLensGet cSpec.mutLens memAfter =
                                some postBytes ∧
                              cSpec.ensuresNormalBool preBytes retVal
                                postBytes argVals = true) →
                            match evalCallExitStep body ⟨onRet, onUnwind⟩
                                (.normal retVal memAfter) with
                            | .stepNormal retBb rv memC =>
                              match writePlace localsArgs memC dst.localId
                                  dstTy rv with
                              | .ok (locs', memW) =>
                                ih { frames := [⟨frame.defId, retBb, 0, locs',
                                       none, none, none⟩],
                                     callerMem := st.callerMem, mem := memW }
                              | .error _ => False
                            | .stepCleanup _ _ => False
                            | .exitUnwind _ => False
                            | .exitTerminate _ => False
                            | .fault _ => False) ∧
                        (cSpec.canUnwind = true →
                          ∀ memAfter,
                            UpdatesOnly cSpec.mutLens memArgs memAfter →
                            (∃ postPartialBytes,
                              byteSubLensGet cSpec.mutLens memAfter =
                                some postPartialBytes ∧
                              cSpec.ensuresUnwindBool preBytes postPartialBytes
                                argVals = true) →
                            match evalCallExitStep body ⟨onRet, onUnwind⟩
                                (.unwind memAfter) with
                            | .stepCleanup cleanupBb memC =>
                              ih { frames := [⟨frame.defId, cleanupBb, 0,
                                     localsArgs, none, none, none⟩],
                                   callerMem := st.callerMem, mem := memC }
                            | .exitUnwind memC => onDone (.unwound memC)
                            | .exitTerminate memC =>
                              onDone (.abortTerminate memC)
                            | .stepNormal _ _ _ => False
                            | .fault _ => False)
            | .assert cond expected _msg target unwind =>
              match evalPrimitiveOperand body.locals frame.locals st.mem
                  cond with
              | .error _ => False
              | .ok (v, locals', mem') =>
                match v with
                | .bool b =>
                  if b == expected then
                    ih { frames := [{ frame with
                           blockIdx := target, stmtIdx := 0,
                           locals := locals', sysrootOp? := none }],
                         callerMem := st.callerMem, mem := mem' }
                  else
                    match evalCallExitStep body ⟨none, unwind⟩
                        (.unwind mem') with
                    | .stepCleanup cleanupBb memC =>
                      ih { frames := [⟨frame.defId, cleanupBb, 0, locals',
                             none, none, none⟩],
                           callerMem := st.callerMem, mem := memC }
                    | .exitUnwind memC => onDone (.unwound memC)
                    | .exitTerminate memC => onDone (.abortTerminate memC)
                    | .stepNormal _ _ _ => False
                    | .fault _ => False
                | .scalar _ => False
                | .ptr _ => False
                | .char _ => False
                | .ordering _ => False
                | .unit => False
                | .enumVal _ _ => False
                | .tuple _ => False
                | .bytes _ => False
                | .slicePtr _ _ => False
                | .rangeTo _ => False
                | .rangeFrom _ => False
                | .array _ => False
                | .range _ _ => False
                | .optionVal _ => False
                | .vec _ _ _ => False
                | .boxPtr _ _ => False
            | .unwindResume =>
              checkCleanupBlock body frame.blockIdx = true ∧
              onDone (.unwound st.mem)
            | .goto _ =>
              match evalStep (Anneal.MirWp.bodyProg body) 0 st with
              | .step st' => ih st'
              | .done (.returned rv) => onDone (.returned rv.ret st.mem)
              | .done (.unwound _) => False
              | .done (.aborted _) => False
              | .fault _ => False
            | .switchInt _ _ =>
              match evalStep (Anneal.MirWp.bodyProg body) 0 st with
              | .step st' => ih st'
              | .done (.returned rv) => onDone (.returned rv.ret st.mem)
              | .done (.unwound _) => False
              | .done (.aborted _) => False
              | .fault _ => False
            | .return_ =>
              match evalStep (Anneal.MirWp.bodyProg body) 0 st with
              | .step st' => ih st'
              | .done (.returned rv) => onDone (.returned rv.ret st.mem)
              | .done (.unwound _) => False
              | .done (.aborted _) => False
              | .fault _ => False
            | .unreachable =>
              match evalStep (Anneal.MirWp.bodyProg body) 0 st with
              | .step st' => ih st'
              | .done (.returned rv) => onDone (.returned rv.ret st.mem)
              | .done (.unwound _) => False
              | .done (.aborted _) => False
              | .fault _ => False
            | .sysrootCall _ _ _ _ _ => False
            | .unsupported => False
            | .coreCall _ _ _ _ _ => False
          else
            match evalStep (Anneal.MirWp.bodyProg body) 0 st with
            | .step st' => ih st'
            | .done (.returned rv) => onDone (.returned rv.ret st.mem)
            | .done (.unwound _) => False
            | .done (.aborted _) => False
            | .fault _ => False)
    fuel s

private theorem evalCallTerminator_cases (callerBody : Body) (bb : BasicBlock)
    (caller : FrameState) (callers : List FrameState) (mem : MemoryState)
    (callerMem : CallerMemory) (calleeDefId : DefId)
    (sysrootOp? : Option SysrootNumOp) (calleeBody : Body)
    (args : List Operand) (dst : Place) (target : Option BasicBlockId)
    (unwind : UnwindAction) :
    (∃ k, evalCallTerminator callerBody bb caller callers mem callerMem
        calleeDefId sysrootOp? calleeBody args dst target unwind = .fault k) ∨
      (∃ s', evalCallTerminator callerBody bb caller callers mem callerMem
          calleeDefId sysrootOp? calleeBody args dst target unwind = .step s' ∧
        s'.callerMem = callerMem) := by
  cases hGate : (!callTargetAdmitted callerBody bb calleeBody args dst target
      unwind || calleeBody.basicBlocks.isEmpty ||
      !storageAnnotationsInBounds calleeBody ||
      !discriminantTypesValid calleeBody ||
      !castTypesValid calleeBody ||
      !assignTypesValid calleeBody ||
      !calleeBody.locals.all isSupportedScalarOrUnitTy) with
  | true =>
    unfold evalCallTerminator; rw [ite_bool_true hGate]
    exact Or.inl ⟨.unsupported, rfl⟩
  | false =>
    let hasMove : Bool :=
      args.any (fun a => match a with | .move _ => true | _ => false)
    let paramTys := (calleeBody.locals.drop 1).take calleeBody.argumentCount
    have hEq :
        evalCallTerminator callerBody bb caller callers mem callerMem
          calleeDefId sysrootOp? calleeBody args dst target unwind =
        (match evalCallArgs callerBody.locals caller.locals mem hasMove args
            paramTys with
         | .error k => StepResult.fault k
         | .ok (argVals, callerLocals', mem') =>
           match Trusted.MirSemantics.getElem? callerLocals' dst.localId with
           | none => StepResult.fault .unsupported
           | some .dead => StepResult.fault .undefined
           | some (.indirect _) => StepResult.fault .unsupported
           | some (.partialTuple _) => StepResult.fault .unsupported
           | some (.immediate _) =>
             StepResult.step {
               frames := {
                 defId := calleeDefId
                 blockIdx := 0
                 stmtIdx := 0
                 locals :=
                   initLocalsLoop calleeBody argVals 0 calleeBody.locals
                 sysrootOp? := sysrootOp?
                 retDst? := some dst
                 retTarget? := target
               } :: { caller with locals := callerLocals' } :: callers
               callerMem := callerMem
               mem := mem'
             }) := by
      unfold evalCallTerminator; rw [ite_bool_false hGate]; rfl
    rw [hEq]
    cases evalCallArgs callerBody.locals caller.locals mem hasMove args
        paramTys with
    | error k => exact Or.inl ⟨k, rfl⟩
    | ok triple =>
      dsimp only
      cases Trusted.MirSemantics.getElem? triple.2.1 dst.localId with
      | none => exact Or.inl ⟨.unsupported, rfl⟩
      | some slot =>
        cases slot with
        | dead => exact Or.inl ⟨.undefined, rfl⟩
        | indirect _ => exact Or.inl ⟨.unsupported, rfl⟩
        | partialTuple _ => exact Or.inl ⟨.unsupported, rfl⟩
        | immediate _ => exact Or.inr ⟨_, rfl, rfl⟩

private theorem evalCallTerminator_never_done (callerBody : Body)
    (bb : BasicBlock) (caller : FrameState) (callers : List FrameState)
    (mem : MemoryState) (callerMem : CallerMemory) (calleeDefId : DefId)
    (sysrootOp? : Option SysrootNumOp) (calleeBody : Body)
    (args : List Operand) (dst : Place) (target : Option BasicBlockId)
    (unwind : UnwindAction) (out : TerminalOut) :
    evalCallTerminator callerBody bb caller callers mem callerMem calleeDefId
        sysrootOp? calleeBody args dst target unwind ≠ .done out := by
  intro hDone
  cases evalCallTerminator_cases callerBody bb caller callers mem callerMem
      calleeDefId sysrootOp? calleeBody args dst target unwind with
  | inl h =>
    cases h with
    | intro k hk => rw [hk] at hDone; cases hDone
  | inr h =>
    cases h with
    | intro s' hs' => rw [hs'.1] at hDone; cases hDone

private theorem attachCallers_done_inv {callers : List FrameState}
    {res : StepResult State TerminalOut} {out : TerminalOut}
    (h : attachCallers callers res = .done out) : res = .done out := by
  cases callers with
  | nil => exact h
  | cons _ _ =>
    unfold attachCallers at h
    cases res with
    | step _ => cases h
    | done _ => exact h
    | fault _ => cases h

private theorem evalNonRootReturn_cont_never_done (p : Program)
    (callee caller : FrameState) (restCallers : List FrameState)
    (mem : MemoryState) (callerMem : CallerMemory) (out : TerminalOut)
    (retRead : Except FaultKind Val)
    (h :
      ((match retRead with
        | .error k => StepResult.fault k
        | .ok retVal =>
          match callee.retDst? with
          | none => StepResult.fault .unsupported
          | some dst =>
            if !dst.projection.isEmpty then
              StepResult.fault .unsupported
            else
              match activeFrameBody p caller with
              | none => StepResult.fault .unsupported
              | some callerBody =>
                match Trusted.MirSemantics.getElem?
                    callerBody.locals dst.localId with
                | none => StepResult.fault .unsupported
                | some dstTy =>
                  match writePlace caller.locals mem dst.localId dstTy retVal
                      with
                  | .error k => StepResult.fault k
                  | .ok (callerLocals', mem') =>
                    match callee.retTarget? with
                    | none => StepResult.fault .undefined
                    | some tgt =>
                      StepResult.step {
                        frames := {
                          caller with
                          blockIdx := tgt
                          stmtIdx := 0
                          locals := callerLocals'
                        } :: restCallers
                        callerMem := callerMem
                        mem := mem'
                      }) : StepResult State TerminalOut) =
        .done out) : False := by
  cases retRead with
  | error _ => cases h
  | ok retVal =>
    dsimp only at h
    cases hDst : callee.retDst? with
    | none => rw [hDst] at h; cases h
    | some dst =>
      rw [hDst] at h; dsimp only at h
      cases hProj : !dst.projection.isEmpty with
      | true => rw [ite_bool_true hProj] at h; cases h
      | false =>
        rw [ite_bool_false hProj] at h
        cases hBody : activeFrameBody p caller with
        | none => rw [hBody] at h; cases h
        | some callerBody =>
          rw [hBody] at h; dsimp only at h
          cases hTy : Trusted.MirSemantics.getElem?
              callerBody.locals dst.localId with
          | none => rw [hTy] at h; cases h
          | some dstTy =>
            rw [hTy] at h; dsimp only at h
            cases hWr : writePlace caller.locals mem dst.localId dstTy retVal
                with
            | error _ => rw [hWr] at h; cases h
            | ok wr =>
              rw [hWr] at h; dsimp only at h
              cases hTg : callee.retTarget? with
              | none => rw [hTg] at h; cases h
              | some _ => rw [hTg] at h; cases h

private theorem evalNonRootReturn_never_done (p : Program)
    (calleeBody : Body) (bb : BasicBlock) (callee caller : FrameState)
    (restCallers : List FrameState) (mem : MemoryState)
    (callerMem : CallerMemory) (out : TerminalOut) :
    evalNonRootReturn p calleeBody bb callee caller restCallers mem callerMem ≠
      .done out := by
  intro hDone
  unfold evalNonRootReturn at hDone
  cases hClean : (bb.cleanup || localsHaveIndirect callee.locals) with
  | true => rw [ite_bool_true hClean] at hDone; cases hDone
  | false =>
    rw [ite_bool_false hClean] at hDone
    dsimp only at hDone
    exact evalNonRootReturn_cont_never_done p callee caller restCallers mem
      callerMem out
      (match Trusted.MirSemantics.getElem? callee.locals 0 with
       | some (.immediate (some retVal)) => .ok retVal
       | some (.immediate none) | some .dead => .error .undefined
       | some (.partialTuple _) => .error .unsupported
       | some (.indirect mplace) =>
         match Trusted.MirSemantics.getElem? calleeBody.locals 0 with
         | none => .error .unsupported
         | some retTy =>
           match loadIndirect mem retTy mplace with
           | .ok (some retVal) => .ok retVal
           | .ok none => .error .undefined
           | .error k => .error k
       | none => .error .unsupported)
      hDone

private theorem evalAssertFailure_unwind_fault (msg : AssertKind)
    (unwind : UnwindAction) (cm : CallerMemory) (lh : Bool) :
    ∃ k, evalAssertFailure msg .unwind unwind cm lh = .fault k := by
  unfold evalAssertFailure
  cases msg with
  | overflow op => cases op <;> cases lh <;> exact ⟨.unsupported, rfl⟩
  | overflowNeg => exact ⟨.unsupported, rfl⟩
  | divByZero => cases lh <;> exact ⟨.unsupported, rfl⟩
  | remByZero => cases lh <;> exact ⟨.unsupported, rfl⟩
  | boundsCheck => cases lh <;> exact ⟨.unsupported, rfl⟩
  | misalignedPtrDeref => exact ⟨.undefined, rfl⟩
  | nullPtrDeref => exact ⟨.undefined, rfl⟩
  | unsupported => exact ⟨.unsupported, rfl⟩

private theorem evalAssertFailure_done_cases (msg : AssertKind)
    (strat : PanicStrategy) (unwind : UnwindAction) (cm : CallerMemory)
    (lh : Bool) (out : TerminalOut)
    (hDone : evalAssertFailure msg strat unwind cm lh = .done out) :
    strat = .abort ∧ ∃ cm', out = .aborted cm' := by
  cases strat with
  | unwind =>
    let ⟨_, hFault⟩ := evalAssertFailure_unwind_fault msg unwind cm lh
    rw [hFault] at hDone
    cases hDone
  | abort =>
    unfold evalAssertFailure at hDone
    cases msg with
    | overflow op =>
      cases op <;> cases lh <;> cases unwind <;> cases hDone <;> exact ⟨rfl, cm, rfl⟩
    | boundsCheck =>
      cases lh <;> cases unwind <;> cases hDone <;> exact ⟨rfl, cm, rfl⟩
    | divByZero =>
      cases lh <;> cases unwind <;> cases hDone <;> exact ⟨rfl, cm, rfl⟩
    | remByZero =>
      cases lh <;> cases unwind <;> cases hDone <;> exact ⟨rfl, cm, rfl⟩
    | overflowNeg => cases hDone
    | misalignedPtrDeref => cases hDone
    | nullPtrDeref => cases hDone
    | unsupported => cases hDone

private theorem evalStep_single_done_cases (p : Program) (c : Choice)
    (s : State) (fr : FrameState) (hFrames : s.frames = [fr])
    (out : TerminalOut) (hUnw : evalStep p c s = .done out) :
    (∃ rv, out = .returned rv) ∨
      (p.panicStrategy = .abort ∧ ∃ cm, out = .aborted cm) := by
  unfold evalStep at hUnw
  cases hFr : s.frames with
  | nil => rw [hFr] at hFrames; cases hFrames
  | cons fr' rest =>
    cases rest with
    | cons _ _ => rw [hFr] at hFrames; cases hFrames
    | nil =>
      rw [hFr] at hFrames hUnw; cases hFrames
      dsimp only at hUnw
      cases hBody : activeFrameBody p fr with
      | none => rw [hBody] at hUnw; cases hUnw
      | some b =>
        rw [hBody] at hUnw
        dsimp only at hUnw
        cases hBb : Trusted.MirSemantics.getElem? b.basicBlocks fr.blockIdx with
        | none => rw [hBb] at hUnw; cases hUnw
        | some bb =>
          rw [hBb] at hUnw
          dsimp only at hUnw
          cases hStmt :
              Trusted.MirSemantics.getElem? bb.statements fr.stmtIdx with
          | some stmt =>
            rw [hStmt] at hUnw
            dsimp only at hUnw
            cases stmt with
            | nop => unfold evalStatement at hUnw; cases hUnw
            | unsupported => unfold evalStatement at hUnw; cases hUnw
            | storageLive id =>
              unfold evalStatement at hUnw
              dsimp only at hUnw
              cases hTy : Trusted.MirSemantics.getElem? b.locals id with
              | none => rw [hTy] at hUnw; cases hUnw
              | some _ =>
                rw [hTy] at hUnw
                dsimp only at hUnw
                cases hLoc : Trusted.MirSemantics.getElem? fr.locals id with
                | none => rw [hLoc] at hUnw; cases hUnw
                | some _ =>
                  rw [hLoc] at hUnw
                  dsimp only at hUnw
                  cases hSet : Trusted.MirSemantics.setElem? fr.locals id _ with
                  | none => rw [hSet] at hUnw; cases hUnw
                  | some _ =>
                    rw [hSet] at hUnw
                    dsimp only at hUnw
                    cases hDe : deallocateLocal s.mem _ with
                    | error _ => rw [hDe] at hUnw; cases hUnw
                    | ok _ => rw [hDe] at hUnw; cases hUnw
            | storageDead id =>
              unfold evalStatement at hUnw
              dsimp only at hUnw
              cases hZero : Nat.beq id 0 with
              | true => rw [ite_bool_true hZero] at hUnw; cases hUnw
              | false =>
                rw [ite_bool_false hZero] at hUnw
                cases hLoc : Trusted.MirSemantics.getElem? fr.locals id with
                | none => rw [hLoc] at hUnw; cases hUnw
                | some _ =>
                  rw [hLoc] at hUnw
                  dsimp only at hUnw
                  cases hSet :
                      Trusted.MirSemantics.setElem? fr.locals id .dead with
                  | none => rw [hSet] at hUnw; cases hUnw
                  | some _ =>
                    rw [hSet] at hUnw
                    dsimp only at hUnw
                    cases hDe : deallocateLocal s.mem _ with
                    | error _ => rw [hDe] at hUnw; cases hUnw
                    | ok _ => rw [hDe] at hUnw; cases hUnw
            | assign dst rv =>
              unfold evalStatement at hUnw
              dsimp only at hUnw
              cases hProj : !dst.projection.isEmpty with
              | true => rw [ite_bool_true hProj] at hUnw; cases hUnw
              | false =>
                rw [ite_bool_false hProj] at hUnw
                cases hTy :
                    Trusted.MirSemantics.getElem? b.locals dst.localId with
                | none => rw [hTy] at hUnw; cases hUnw
                | some _ =>
                  rw [hTy] at hUnw
                  dsimp only at hUnw
                  cases hRv : evalRvalue b.locals fr.locals s.mem _ rv with
                  | error _ => rw [hRv] at hUnw; cases hUnw
                  | ok _ =>
                    rw [hRv] at hUnw
                    dsimp only at hUnw
                    cases hWr : writePlace _ _ dst.localId _ _ with
                    | error _ => rw [hWr] at hUnw; cases hUnw
                    | ok _ => rw [hWr] at hUnw; cases hUnw
          | none =>
            rw [hStmt] at hUnw
            dsimp only at hUnw
            cases hIdx : Nat.beq fr.stmtIdx bb.statements.length with
            | false => rw [ite_bool_false hIdx] at hUnw; cases hUnw
            | true =>
              rw [ite_bool_true hIdx] at hUnw
              cases hTerm : bb.terminator with
              | goto _ =>
                unfold evalTerminator jumpToBlock at hUnw
                rw [hTerm] at hUnw
                cases hUnw
              | unreachable =>
                unfold evalTerminator at hUnw; rw [hTerm] at hUnw; cases hUnw
              | unwindResume =>
                unfold evalTerminator at hUnw; rw [hTerm] at hUnw; cases hUnw
              | assert cond expected msg target unwind =>
                unfold evalTerminator at hUnw
                rw [hTerm] at hUnw
                dsimp only [attachCallers] at hUnw
                cases hCond : evalPrimitiveOperand b.locals fr.locals s.mem cond with
                | error _ => rw [hCond] at hUnw; cases hUnw
                | ok res =>
                  rw [hCond] at hUnw
                  dsimp only at hUnw
                  cases hVal : res.1 with
                  | bool bVal =>
                    rw [hVal] at hUnw
                    dsimp only at hUnw
                    cases hEq : (bVal == expected) with
                    | true =>
                      rw [ite_bool_true hEq] at hUnw
                      unfold jumpToBlock at hUnw
                      cases hUnw
                    | false =>
                      rw [ite_bool_false hEq] at hUnw
                      exact .inr (evalAssertFailure_done_cases msg
                        p.panicStrategy unwind s.callerMem
                        p.hasLocalPanicHandler out hUnw)
                  | scalar _ | optionVal _ | range _ _
                  | boxPtr _ _ | vec _ _ _ =>
                    rw [hVal] at hUnw; cases hUnw
                  | ptr _ => rw [hVal] at hUnw; cases hUnw
                  | char _ => rw [hVal] at hUnw; cases hUnw
                  | ordering _ => rw [hVal] at hUnw; cases hUnw
                  | unit => rw [hVal] at hUnw; cases hUnw
                  | enumVal _ _ => rw [hVal] at hUnw; cases hUnw
                  | tuple _ => rw [hVal] at hUnw; cases hUnw
                  | bytes _ => rw [hVal] at hUnw; cases hUnw
                  | array _ => rw [hVal] at hUnw; cases hUnw
                  | slicePtr _ _ => rw [hVal] at hUnw; cases hUnw
                  | rangeTo _ => rw [hVal] at hUnw; cases hUnw
                  | rangeFrom _ => rw [hVal] at hUnw; cases hUnw
              | unsupported =>
                unfold evalTerminator at hUnw; rw [hTerm] at hUnw; cases hUnw
              | coreCall _ _ _ _ _ =>
                unfold evalTerminator at hUnw; rw [hTerm] at hUnw; cases hUnw
              | call callee args dst target unwind =>
                rw [hTerm] at hUnw
                dsimp only at hUnw
                cases hCb : Trusted.MirSemantics.getElem? p.bodies callee with
                | none => rw [hCb] at hUnw; cases hUnw
                | some cbody =>
                  rw [hCb] at hUnw
                  exact False.elim (evalCallTerminator_never_done b bb fr [] s.mem
                    s.callerMem callee none cbody args dst target unwind out hUnw)
              | sysrootCall op args dst target unwind =>
                rw [hTerm] at hUnw
                exact False.elim (evalCallTerminator_never_done b bb fr [] s.mem
                  s.callerMem 0 (some op) (sysrootNumBody op) args dst
                  target unwind out hUnw)
              | return_ =>
                unfold evalTerminator at hUnw
                rw [hTerm] at hUnw
                dsimp only at hUnw
                cases hCl : bb.cleanup with
                | true => rw [ite_bool_true hCl] at hUnw; cases hUnw
                | false =>
                  rw [ite_bool_false hCl] at hUnw
                  cases hLoc0 : Trusted.MirSemantics.getElem? fr.locals 0 with
                  | none => rw [hLoc0] at hUnw; cases hUnw
                  | some sl0 =>
                    rw [hLoc0] at hUnw
                    cases sl0 with
                    | dead | partialTuple _ => cases hUnw
                    | immediate ov =>
                      cases ov with
                      | none => cases hUnw
                      | some rv =>
                        cases hUnw
                        exact .inl ⟨⟨rv, s.callerMem⟩, rfl⟩
                    | indirect mp =>
                      cases hTy0 : Trusted.MirSemantics.getElem? b.locals 0 with
                      | none => rw [hTy0] at hUnw; cases hUnw
                      | some t0 =>
                        rw [hTy0] at hUnw
                        dsimp only at hUnw
                        cases hLoad : loadIndirect s.mem t0 mp with
                        | error _ => rw [hLoad] at hUnw; cases hUnw
                        | ok ov =>
                          rw [hLoad] at hUnw
                          cases ov with
                          | none => cases hUnw
                          | some rv =>
                            cases hUnw
                            exact .inl ⟨⟨rv, s.callerMem⟩, rfl⟩
              | switchInt discr tgts =>
                unfold evalTerminator at hUnw
                rw [hTerm] at hUnw
                dsimp only at hUnw
                cases hDiscr :
                    evalPrimitiveOperand b.locals fr.locals s.mem discr with
                | error _ => rw [hDiscr] at hUnw; cases hUnw
                | ok res =>
                  rw [hDiscr] at hUnw
                  dsimp only at hUnw
                  cases hRes : res.1 with
                  | scalar sv =>
                    rw [hRes] at hUnw; dsimp only at hUnw
                    cases hTg : evalSwitchBranches sv.width sv.bits
                        tgts.otherwise tgts.branches with
                    | error _ => rw [hTg] at hUnw; cases hUnw
                    | ok _ =>
                      rw [hTg] at hUnw; unfold jumpToBlock at hUnw; cases hUnw
                  | bool bVal =>
                    rw [hRes] at hUnw; dsimp only at hUnw
                    cases hTg : evalBoolSwitchBranches bVal tgts.otherwise
                        tgts.branches with
                    | error _ => rw [hTg] at hUnw; cases hUnw
                    | ok _ =>
                      rw [hTg] at hUnw; unfold jumpToBlock at hUnw; cases hUnw
                  | char cVal =>
                    rw [hRes] at hUnw; dsimp only at hUnw
                    cases hTg : evalCharSwitchBranches cVal tgts.otherwise
                        tgts.branches with
                    | error _ => rw [hTg] at hUnw; cases hUnw
                    | ok _ =>
                      rw [hTg] at hUnw; unfold jumpToBlock at hUnw; cases hUnw
                  | ptr _ =>
                    rw [hRes] at hUnw; dsimp only at hUnw
                    cases hBr : tgts.branches with
                    | cons _ _ => rw [hBr] at hUnw; cases hUnw
                    | nil =>
                      rw [hBr] at hUnw; unfold jumpToBlock at hUnw; cases hUnw
                  | ordering _ =>
                    rw [hRes] at hUnw; dsimp only at hUnw
                    cases hBr : tgts.branches with
                    | cons _ _ => rw [hBr] at hUnw; cases hUnw
                    | nil =>
                      rw [hBr] at hUnw; unfold jumpToBlock at hUnw; cases hUnw
                  | unit =>
                    rw [hRes] at hUnw; dsimp only at hUnw
                    cases hBr : tgts.branches with
                    | cons _ _ => rw [hBr] at hUnw; cases hUnw
                    | nil =>
                      rw [hBr] at hUnw; unfold jumpToBlock at hUnw; cases hUnw
                  | enumVal _ _ =>
                    rw [hRes] at hUnw; dsimp only at hUnw
                    cases hBr : tgts.branches with
                    | cons _ _ => rw [hBr] at hUnw; cases hUnw
                    | nil =>
                      rw [hBr] at hUnw; unfold jumpToBlock at hUnw; cases hUnw
                  | tuple _ =>
                    rw [hRes] at hUnw; dsimp only at hUnw
                    cases hBr : tgts.branches with
                    | cons _ _ => rw [hBr] at hUnw; cases hUnw
                    | nil =>
                      rw [hBr] at hUnw; unfold jumpToBlock at hUnw; cases hUnw
                  | bytes _ =>
                    rw [hRes] at hUnw; dsimp only at hUnw
                    cases hBr : tgts.branches with
                    | cons _ _ => rw [hBr] at hUnw; cases hUnw
                    | nil =>
                      rw [hBr] at hUnw; unfold jumpToBlock at hUnw; cases hUnw
                  | slicePtr _ _ =>
                    rw [hRes] at hUnw; dsimp only at hUnw
                    cases hBr : tgts.branches with
                    | cons _ _ => rw [hBr] at hUnw; cases hUnw
                    | nil =>
                      rw [hBr] at hUnw; unfold jumpToBlock at hUnw; cases hUnw
                  | rangeTo _ =>
                    rw [hRes] at hUnw; dsimp only at hUnw
                    cases hBr : tgts.branches with
                    | cons _ _ => rw [hBr] at hUnw; cases hUnw
                    | nil =>
                      rw [hBr] at hUnw; unfold jumpToBlock at hUnw; cases hUnw
                  | rangeFrom _ =>
                    rw [hRes] at hUnw; dsimp only at hUnw
                    cases hBr : tgts.branches with
                    | cons _ _ => rw [hBr] at hUnw; cases hUnw
                    | nil =>
                      rw [hBr] at hUnw; unfold jumpToBlock at hUnw; cases hUnw
                  | array _ =>
                    rw [hRes] at hUnw; dsimp only at hUnw
                    cases hBr : tgts.branches with
                    | cons _ _ => rw [hBr] at hUnw; cases hUnw
                    | nil =>
                      rw [hBr] at hUnw; unfold jumpToBlock at hUnw; cases hUnw
                  | range _ _ =>
                    rw [hRes] at hUnw; dsimp only at hUnw
                    cases hBr : tgts.branches with
                    | cons _ _ => rw [hBr] at hUnw; cases hUnw
                    | nil =>
                      rw [hBr] at hUnw; unfold jumpToBlock at hUnw; cases hUnw
                  | optionVal _ =>
                    rw [hRes] at hUnw; dsimp only at hUnw
                    cases hBr : tgts.branches with
                    | cons _ _ => rw [hBr] at hUnw; cases hUnw
                    | nil =>
                      rw [hBr] at hUnw; unfold jumpToBlock at hUnw; cases hUnw
                  | vec _ _ _ =>
                    rw [hRes] at hUnw; dsimp only at hUnw
                    cases hBr : tgts.branches with
                    | cons _ _ => rw [hBr] at hUnw; cases hUnw
                    | nil =>
                      rw [hBr] at hUnw; unfold jumpToBlock at hUnw; cases hUnw
                  | boxPtr _ _ =>
                    rw [hRes] at hUnw; dsimp only at hUnw
                    cases hBr : tgts.branches with
                    | cons _ _ => rw [hBr] at hUnw; cases hUnw
                    | nil =>
                      rw [hBr] at hUnw; unfold jumpToBlock at hUnw; cases hUnw

private theorem evalStep_done_cases (p : Program) (c : Choice) (s : State)
    (out : TerminalOut) (hDone : evalStep p c s = .done out) :
    (∃ rv, out = .returned rv) ∨
      (p.panicStrategy = .abort ∧ ∃ cm, out = .aborted cm) := by
  cases hFrames : s.frames with
  | nil =>
    unfold evalStep at hDone
    rw [hFrames] at hDone
    cases hDone
  | cons fr frRest =>
    cases frRest with
    | nil => exact evalStep_single_done_cases p c s fr hFrames out hDone
    | cons caller rest =>
      unfold evalStep at hDone
      rw [hFrames] at hDone
      dsimp only at hDone
      cases hBody : activeFrameBody p fr with
      | none => rw [hBody] at hDone; cases hDone
      | some body =>
        rw [hBody] at hDone; dsimp only at hDone
        cases hBb : Trusted.MirSemantics.getElem? body.basicBlocks fr.blockIdx
            with
        | none => rw [hBb] at hDone; cases hDone
        | some bb =>
          rw [hBb] at hDone; dsimp only at hDone
          cases hStmt : Trusted.MirSemantics.getElem? bb.statements fr.stmtIdx
              with
          | some stmt =>
            rw [hStmt] at hDone; dsimp only at hDone
            have hSub := attachCallers_done_inv hDone
            have hSingle :
                evalStep p c { s with frames := [fr] } = .done out := by
              unfold evalStep; dsimp only
              rw [hBody]; dsimp only
              rw [hBb]; dsimp only
              rw [hStmt]; exact hSub
            exact evalStep_single_done_cases p c { s with frames := [fr] } fr
              rfl out hSingle
          | none =>
            rw [hStmt] at hDone; dsimp only at hDone
            cases hLen : Nat.beq fr.stmtIdx bb.statements.length with
            | false => rw [ite_bool_false hLen] at hDone; cases hDone
            | true =>
              rw [ite_bool_true hLen] at hDone
              cases hTerm : bb.terminator with
              | call callee args dst target unwind =>
                rw [hTerm] at hDone; dsimp only at hDone
                cases hCallee : Trusted.MirSemantics.getElem? p.bodies callee
                    with
                | none => rw [hCallee] at hDone; cases hDone
                | some calleeBody =>
                  rw [hCallee] at hDone; dsimp only at hDone
                  exact False.elim (evalCallTerminator_never_done body bb fr
                    (caller :: rest) s.mem s.callerMem callee none
                    calleeBody args dst target unwind out hDone)
              | sysrootCall op args dst target unwind =>
                rw [hTerm] at hDone; dsimp only at hDone
                exact False.elim (evalCallTerminator_never_done body bb fr
                  (caller :: rest) s.mem s.callerMem 0 (some op)
                  (sysrootNumBody op) args dst target unwind out hDone)
              | return_ =>
                rw [hTerm] at hDone; dsimp only at hDone
                exact False.elim (evalNonRootReturn_never_done p body bb fr
                  caller rest s.mem s.callerMem out hDone)
              | goto _ | switchInt _ _ | unreachable | assert _ _ _ _ _
              | unwindResume | coreCall _ _ _ _ _ | unsupported =>
                rw [hTerm] at hDone; dsimp only at hDone
                have hSub := attachCallers_done_inv hDone
                have hSingle :
                    evalStep p c { s with frames := [fr] } = .done out := by
                  unfold evalStep; dsimp only
                  rw [hBody]; dsimp only
                  rw [hBb]; dsimp only
                  rw [hStmt]; dsimp only
                  rw [ite_bool_true hLen]
                  rw [hTerm]; exact hSub
                exact evalStep_single_done_cases p c
                  { s with frames := [fr] } fr rfl out hSingle

private theorem evalStep_never_unwound (p : Program) (c : Choice) (s : State)
    (cm : CallerMemory) : evalStep p c s ≠ .done (.unwound cm) := by
  intro hUnw
  cases evalStep_done_cases p c s (.unwound cm) hUnw with
  | inl h =>
    let ⟨_, hEq⟩ := h
    cases hEq
  | inr h =>
    let ⟨_, _, hEq⟩ := h
    cases hEq

private theorem evalStep_bodyProg_never_aborted (body : Body) (c : Choice)
    (s : State) (cm : CallerMemory) :
    evalStep (Anneal.MirWp.bodyProg body) c s ≠ .done (.aborted cm) := by
  intro hAb
  cases evalStep_done_cases (Anneal.MirWp.bodyProg body) c s
      (.aborted cm) hAb with
  | inl h =>
    let ⟨_, hEq⟩ := h
    cases hEq
  | inr h => cases h.1

private theorem basicBlocks_getElem_hasCall_false_cut
    {bbs : List BasicBlock} {blk : BasicBlockId} {bb : BasicBlock}
    (hNoCall : bbs.any (fun b =>
      match b.terminator with
      | .call _ _ _ _ _ | .sysrootCall _ _ _ _ _ => true
      | _ => false) = false)
    (hBb : Trusted.MirSemantics.getElem? bbs blk = some bb) :
    (match bb.terminator with
     | .call _ _ _ _ _ | .sysrootCall _ _ _ _ _ => true
     | _ => false) = false := by
  induction bbs generalizing blk with
  | nil => cases hBb
  | cons b rest ih =>
    unfold List.any at hNoCall
    dsimp only at hNoCall
    cases hOr : (match b.terminator with
      | .call _ _ _ _ _ | .sysrootCall _ _ _ _ _ => true
      | _ => false)
    · rw [hOr, Bool.false_or] at hNoCall
      cases blk with
      | zero => injection hBb with hEq; subst hEq; exact hOr
      | succ blk' => exact ih hNoCall hBb
    · rw [hOr, Bool.true_or] at hNoCall; cases hNoCall

private theorem evalStatement_single_frame {body : Body} {fr : FrameState}
    {mem : MemoryState} {cm : CallerMemory} {stmt : StatementKind}
    {st' : State}
    (hStmt : evalStatement body fr mem cm stmt = .step st') :
    st'.frames.length = 1 := by
  cases stmt with
  | nop =>
    unfold evalStatement at hStmt; injection hStmt with hEq; rw [← hEq]; rfl
  | unsupported => unfold evalStatement at hStmt; cases hStmt
  | storageLive id =>
    unfold evalStatement at hStmt; dsimp only at hStmt
    cases hTy : Trusted.MirSemantics.getElem? body.locals id with
    | none => rw [hTy] at hStmt; cases hStmt
    | some _ =>
      rw [hTy] at hStmt; dsimp only at hStmt
      cases hLoc : Trusted.MirSemantics.getElem? fr.locals id with
      | none => rw [hLoc] at hStmt; cases hStmt
      | some _ =>
        rw [hLoc] at hStmt; dsimp only at hStmt
        cases hSet : Trusted.MirSemantics.setElem? fr.locals id _ with
        | none => rw [hSet] at hStmt; cases hStmt
        | some _ =>
          rw [hSet] at hStmt; dsimp only at hStmt
          cases hDe : deallocateLocal mem _ with
          | error _ => rw [hDe] at hStmt; cases hStmt
          | ok _ => rw [hDe] at hStmt; cases hStmt; rfl
  | storageDead id =>
    unfold evalStatement at hStmt; dsimp only at hStmt
    cases hZero : Nat.beq id 0 with
    | true => rw [ite_bool_true hZero] at hStmt; cases hStmt
    | false =>
      rw [ite_bool_false hZero] at hStmt
      cases hLoc : Trusted.MirSemantics.getElem? fr.locals id with
      | none => rw [hLoc] at hStmt; cases hStmt
      | some _ =>
        rw [hLoc] at hStmt; dsimp only at hStmt
        cases hSet : Trusted.MirSemantics.setElem? fr.locals id .dead with
        | none => rw [hSet] at hStmt; cases hStmt
        | some _ =>
          rw [hSet] at hStmt; dsimp only at hStmt
          cases hDe : deallocateLocal mem _ with
          | error _ => rw [hDe] at hStmt; cases hStmt
          | ok _ => rw [hDe] at hStmt; cases hStmt; rfl
  | assign dst rv =>
    unfold evalStatement at hStmt; dsimp only at hStmt
    cases hProj : !dst.projection.isEmpty with
    | true => rw [ite_bool_true hProj] at hStmt; cases hStmt
    | false =>
      rw [ite_bool_false hProj] at hStmt
      cases hTy : Trusted.MirSemantics.getElem? body.locals dst.localId with
      | none => rw [hTy] at hStmt; cases hStmt
      | some _ =>
        rw [hTy] at hStmt; dsimp only at hStmt
        cases hRv : evalRvalue body.locals fr.locals mem _ rv with
        | error _ => rw [hRv] at hStmt; cases hStmt
        | ok _ =>
          rw [hRv] at hStmt; dsimp only at hStmt
          cases hWr : writePlace _ _ dst.localId _ _ with
          | error _ => rw [hWr] at hStmt; cases hStmt
          | ok _ => rw [hWr] at hStmt; cases hStmt; rfl

private theorem evalTerminator_single_frame {body : Body} {bb : BasicBlock}
    {fr : FrameState} {mem : MemoryState} {cm : CallerMemory} {st' : State}
    (hTerm : evalTerminator body bb fr mem cm = .step st') :
    st'.frames.length = 1 := by
  unfold evalTerminator at hTerm
  cases hKind : bb.terminator with
  | goto _ => rw [hKind] at hTerm; unfold jumpToBlock at hTerm; cases hTerm; rfl
  | assert cond expected msg target unwind =>
    rw [hKind] at hTerm; dsimp only at hTerm
    cases hCond : evalPrimitiveOperand body.locals fr.locals mem cond with
    | error _ => rw [hCond] at hTerm; cases hTerm
    | ok res =>
      rw [hCond] at hTerm; dsimp only at hTerm
      cases hVal : res.1 with
      | bool condB =>
        rw [hVal] at hTerm; dsimp only at hTerm
        cases hEq : (condB == expected) with
        | true =>
          rw [ite_bool_true hEq] at hTerm
          unfold jumpToBlock at hTerm
          cases hTerm
          rfl
        | false =>
          rw [ite_bool_false hEq] at hTerm
          let ⟨_, hFault⟩ :=
            evalAssertFailure_unwind_fault msg unwind cm true
          rw [hFault] at hTerm
          cases hTerm
      | scalar _ | ptr _ | char _ | ordering _ | unit | enumVal _ _ | tuple _
      | bytes _ | array _ | slicePtr _ _ | rangeTo _ | rangeFrom _
      | optionVal _ | range _ _ | boxPtr _ _ | vec _ _ _ =>
        rw [hVal] at hTerm; cases hTerm
  | unreachable | unwindResume | call _ _ _ _ _
  | sysrootCall _ _ _ _ _ | coreCall _ _ _ _ _ | unsupported => rw [hKind] at hTerm; cases hTerm
  | return_ =>
    rw [hKind] at hTerm; dsimp only at hTerm
    cases hCl : bb.cleanup with
    | true => rw [ite_bool_true hCl] at hTerm; cases hTerm
    | false =>
      rw [ite_bool_false hCl] at hTerm
      cases hLoc0 : Trusted.MirSemantics.getElem? fr.locals 0 with
      | none => rw [hLoc0] at hTerm; cases hTerm
      | some sl0 =>
        rw [hLoc0] at hTerm
        cases sl0 with
        | dead => cases hTerm
        | partialTuple _ => cases hTerm
        | immediate ov =>
          cases ov with | none => cases hTerm | some _ => cases hTerm
        | indirect mp =>
          cases hTy0 : Trusted.MirSemantics.getElem? body.locals 0 with
          | none => rw [hTy0] at hTerm; cases hTerm
          | some _ =>
            rw [hTy0] at hTerm; dsimp only at hTerm
            cases hLd : loadIndirect mem _ mp with
            | error _ => rw [hLd] at hTerm; cases hTerm
            | ok ov =>
              rw [hLd] at hTerm
              cases ov with | none => cases hTerm | some _ => cases hTerm
  | switchInt discr tgts =>
    rw [hKind] at hTerm; dsimp only at hTerm
    cases hEv : evalPrimitiveOperand body.locals fr.locals mem discr with
    | error _ => rw [hEv] at hTerm; cases hTerm
    | ok res =>
      rw [hEv] at hTerm; dsimp only at hTerm
      cases hRes : res.1 with
      | scalar sv =>
        rw [hRes] at hTerm; dsimp only at hTerm
        cases hTg : evalSwitchBranches sv.width sv.bits tgts.otherwise
            tgts.branches with
        | error _ => rw [hTg] at hTerm; cases hTerm
        | ok _ =>
          rw [hTg] at hTerm; unfold jumpToBlock at hTerm; cases hTerm; rfl
      | bool bVal =>
        rw [hRes] at hTerm; dsimp only at hTerm
        cases hTg : evalBoolSwitchBranches bVal tgts.otherwise
            tgts.branches with
        | error _ => rw [hTg] at hTerm; cases hTerm
        | ok _ =>
          rw [hTg] at hTerm; unfold jumpToBlock at hTerm; cases hTerm; rfl
      | char cVal =>
        rw [hRes] at hTerm; dsimp only at hTerm
        cases hTg : evalCharSwitchBranches cVal tgts.otherwise
            tgts.branches with
        | error _ => rw [hTg] at hTerm; cases hTerm
        | ok _ =>
          rw [hTg] at hTerm; unfold jumpToBlock at hTerm; cases hTerm; rfl
      | ptr _ | ordering _ | unit | enumVal _ _ | tuple _ | bytes _
      | slicePtr _ _ | rangeTo _ | rangeFrom _ | array _
      | range _ _ | optionVal _ | boxPtr _ _ | vec _ _ _ =>
        rw [hRes] at hTerm; dsimp only at hTerm
        cases hBr : tgts.branches with
        | cons _ _ => rw [hBr] at hTerm; cases hTerm
        | nil =>
          rw [hBr] at hTerm; unfold jumpToBlock at hTerm; cases hTerm; rfl

private theorem sysrootNumBody_hasNoCall (op : SysrootNumOp) :
    (sysrootNumBody op).basicBlocks.any (fun b =>
      match b.terminator with
      | .call _ _ _ _ _ | .sysrootCall _ _ _ _ _ => true
      | _ => false) = false := by
  cases op with
  | mk kind _ _ => cases kind <;> rfl

private theorem evalStep_bodyProg_single_frame {body : Body} {s st' : State}
    (hSingle : s.frames.length = 1)
    (hNoCall : body.basicBlocks.any (fun b =>
      match b.terminator with
      | .call _ _ _ _ _ | .sysrootCall _ _ _ _ _ => true
      | _ => false) = false)
    (hStep : evalStep (Anneal.MirWp.bodyProg body) 0 s = .step st') :
    st'.frames.length = 1 := by
  unfold evalStep at hStep
  cases hFr : s.frames with
  | nil => rw [hFr] at hSingle; cases hSingle
  | cons fr rest =>
    cases rest with
    | cons _ _ => rw [hFr] at hSingle; cases hSingle
    | nil =>
      rw [hFr] at hStep; dsimp only at hStep
      cases hBody : activeFrameBody (Anneal.MirWp.bodyProg body) fr with
      | none => rw [hBody] at hStep; cases hStep
      | some b =>
        rw [hBody] at hStep; dsimp only at hStep
        have hBNoCall : b.basicBlocks.any (fun blk =>
            match blk.terminator with
            | .call _ _ _ _ _ | .sysrootCall _ _ _ _ _ => true
            | _ => false) = false := by
          unfold activeFrameBody at hBody
          cases hSys : fr.sysrootOp? with
          | some op =>
            rw [hSys] at hBody; injection hBody with hBEq; rw [← hBEq]
            exact sysrootNumBody_hasNoCall op
          | none =>
            rw [hSys] at hBody
            cases hDef : fr.defId with
            | zero =>
              rw [hDef] at hBody; injection hBody with hBEq; rw [← hBEq]
              exact hNoCall
            | succ n =>
              have hNone :
                  Trusted.MirSemantics.getElem?
                    (Anneal.MirWp.bodyProg body).bodies (n + 1) = none := rfl
              rw [hDef, hNone] at hBody; cases hBody
        cases hBb : Trusted.MirSemantics.getElem? b.basicBlocks fr.blockIdx with
        | none => rw [hBb] at hStep; cases hStep
        | some bb =>
          rw [hBb] at hStep; dsimp only at hStep
          cases hStmt : Trusted.MirSemantics.getElem? bb.statements fr.stmtIdx
              with
          | some stmt =>
            rw [hStmt] at hStep; dsimp only at hStep
            exact evalStatement_single_frame hStep
          | none =>
            rw [hStmt] at hStep; dsimp only at hStep
            cases hIdx : Nat.beq fr.stmtIdx bb.statements.length with
            | false => rw [ite_bool_false hIdx] at hStep; cases hStep
            | true =>
              rw [ite_bool_true hIdx] at hStep
              have hNoCallBb :=
                basicBlocks_getElem_hasCall_false_cut hBNoCall hBb
              cases hKind : bb.terminator with
              | call _ _ _ _ _ => rw [hKind] at hNoCallBb; cases hNoCallBb
              | sysrootCall _ _ _ _ _ =>
                rw [hKind] at hNoCallBb; cases hNoCallBb
              | goto _ | switchInt _ _ | return_ | unreachable
              | assert _ _ _ _ _ | unwindResume | coreCall _ _ _ _ _ | unsupported =>
                rw [hKind] at hStep
                dsimp only [attachCallers] at hStep
                exact evalTerminator_single_frame hStep
/-- Any pure intra-frame execution certified by `Anneal.MirWp.wpState` over a
normal-return postcondition lifts directly into `wpFrameOutcome`. -/
theorem wpFrameOutcome_of_mirWpState (callerLens : ByteSubLens)
    (env : DefId → Option CallSpec) (body : Body)
    (fuel : Nat) (s : State) (post : TerminalOut → Prop)
    (onDone : FrameTermOut → Prop)
    (hPost : ∀ rv mem cm, post (.returned ⟨rv, cm⟩) → onDone (.returned rv mem))
    (hWp : Anneal.MirWp.wpState (Anneal.MirWp.bodyProg body) fuel s post)
    (hSingle : s.frames.length = 1 := by rfl)
    (hNoCall : body.basicBlocks.any (fun b =>
      match b.terminator with
      | .call _ _ _ _ _ | .sysrootCall _ _ _ _ _ => true
      | _ => false) = false := by rfl) :
    wpFrameOutcome callerLens env body fuel s onDone := by
  induction fuel generalizing s post onDone with
  | zero =>
    exact False.elim hWp
  | succ fuel ih =>
    dsimp only [Anneal.MirWp.wpState, Anneal.MirWp.wpOutcomeState,
      Anneal.Framework.StepWp.wpStepOutcome] at hWp
    rw [Anneal.Framework.StepWp.wpStepPred_succ_iff] at hWp
    have h0 := hWp.2 0 rfl
    have hEval :
        match evalStep (Anneal.MirWp.bodyProg body) 0 s with
        | .step st' => wpFrameOutcome callerLens env body fuel st' onDone
        | .done (.returned rv) => onDone (.returned rv.ret s.mem)
        | .done (.unwound _) => False
        | .done (.aborted _) => False
        | .fault _ => False := by
      cases hSt : evalStep (Anneal.MirWp.bodyProg body) 0 s with
      | step st' =>
        rw [hSt] at h0
        exact ih st' post onDone hPost h0
          (evalStep_bodyProg_single_frame hSingle hNoCall hSt)
      | done out =>
        rw [hSt] at h0
        cases out with
        | returned retOut => exact hPost retOut.ret s.mem retOut.callerMem h0
        | unwound cm =>
          exact False.elim
            (evalStep_never_unwound (Anneal.MirWp.bodyProg body) 0 s cm hSt)
        | aborted cm =>
          exact False.elim
            (evalStep_bodyProg_never_aborted body 0 s cm hSt)
      | fault _ =>
        rw [hSt] at h0
        exact False.elim h0
    cases hFr : s.frames with
    | nil =>
      rw [hFr] at hSingle
      cases hSingle
    | cons frame rest =>
      cases rest with
      | cons _ _ =>
        rw [hFr] at hSingle
        cases hSingle
      | nil =>
        cases hSys : frame.sysrootOp? with
        | some _ =>
          unfold wpFrameOutcome
          dsimp only
          rw [hFr]
          dsimp only
          rw [hSys]
          exact hEval
        | none =>
          cases hDef : Nat.beq frame.defId 0 with
          | false =>
            unfold evalStep at hEval
            rw [hFr] at hEval
            dsimp only at hEval
            cases hDef0 : frame.defId with
            | zero => rw [hDef0] at hDef; cases hDef
            | succ n =>
              have hNone :
                  activeFrameBody (Anneal.MirWp.bodyProg body) frame =
                    none := by
                unfold activeFrameBody
                rw [hSys, hDef0]
                rfl
              rw [hNone] at hEval
              exact False.elim hEval
          | true =>
            have hDefEq : frame.defId = 0 := natEq_of_beq frame.defId 0 hDef
            have hSomeB :
                activeFrameBody (Anneal.MirWp.bodyProg body) frame =
                  some body := by
              unfold activeFrameBody
              rw [hSys, hDefEq]
              rfl
            cases hBb :
                Trusted.MirSemantics.getElem? body.basicBlocks frame.blockIdx
                with
            | none =>
              unfold evalStep at hEval
              rw [hFr] at hEval
              dsimp only at hEval
              rw [hSomeB] at hEval
              dsimp only at hEval
              rw [hBb] at hEval
              exact False.elim hEval
            | some bb =>
              unfold wpFrameOutcome
              dsimp only
              rw [hFr]
              dsimp only
              rw [hSys]
              dsimp only
              rw [hBb]
              dsimp only
              cases hIdx : Nat.beq frame.stmtIdx bb.statements.length with
              | false =>
                rw [if_prop_false (rfl : false = false)]
                exact hEval
              | true =>
                rw [if_prop_true (rfl : true = true)]
                have hNoneStmt :
                    Trusted.MirSemantics.getElem? bb.statements frame.stmtIdx =
                      none := by
                  have hEqLen :=
                    natEq_of_beq frame.stmtIdx bb.statements.length hIdx
                  rw [hEqLen]
                  exact getElem_self_length_none bb.statements
                have hNoCallBb :=
                  basicBlocks_getElem_hasCall_false_cut hNoCall hBb
                cases hTerm : bb.terminator with
                | call _ _ _ _ _ =>
                  rw [hTerm] at hNoCallBb; cases hNoCallBb
                | sysrootCall _ _ _ _ _ =>
                  rw [hTerm] at hNoCallBb; cases hNoCallBb
                | goto _ => exact hEval
                | switchInt _ _ => exact hEval
                | return_ => exact hEval
                | unreachable => exact hEval
                | assert cond expected msg target unwind =>
                  unfold evalStep at hEval
                  rw [hFr] at hEval; dsimp only at hEval
                  rw [hSomeB] at hEval; dsimp only at hEval
                  rw [hBb] at hEval; dsimp only at hEval
                  rw [hNoneStmt] at hEval; dsimp only at hEval
                  rw [ite_bool_true hIdx, hTerm] at hEval
                  dsimp only [attachCallers] at hEval
                  unfold evalTerminator at hEval
                  rw [hTerm] at hEval
                  dsimp only at hEval
                  cases hCond :
                      evalPrimitiveOperand body.locals frame.locals s.mem
                        cond with
                  | error _ => rw [hCond] at hEval; exact False.elim hEval
                  | ok res =>
                    rw [hCond] at hEval
                    dsimp only at hEval
                    cases hVal : res.1 with
                    | bool condB =>
                      rw [hVal] at hEval
                      dsimp only at hEval
                      cases hEq : (condB == expected) with
                      | true =>
                        rw [ite_bool_true hEq] at hEval
                        unfold jumpToBlock at hEval
                        dsimp only at hEval
                        dsimp only
                        rw [hCond]
                        dsimp only
                        rw [hVal]
                        dsimp only
                        rw [ite_bool_true hEq]
                        rw [hSys] at hEval
                        exact hEval
                      | false =>
                        rw [ite_bool_false hEq] at hEval
                        dsimp only [Anneal.MirWp.bodyProg] at hEval
                        let ⟨_, hFault⟩ :=
                          evalAssertFailure_unwind_fault msg unwind s.callerMem
                            true
                        rw [hFault] at hEval
                        exact False.elim hEval
                    | scalar _ | optionVal _ | range _ _ | boxPtr _ _ | vec _ _ _ => rw [hVal] at hEval; exact False.elim hEval
                    | ptr _ => rw [hVal] at hEval; exact False.elim hEval
                    | char _ => rw [hVal] at hEval; exact False.elim hEval
                    | ordering _ => rw [hVal] at hEval; exact False.elim hEval
                    | unit => rw [hVal] at hEval; exact False.elim hEval
                    | enumVal _ _ => rw [hVal] at hEval; exact False.elim hEval
                    | tuple _ => rw [hVal] at hEval; exact False.elim hEval
                    | bytes _ => rw [hVal] at hEval; exact False.elim hEval
                    | array _ => rw [hVal] at hEval; exact False.elim hEval
                    | slicePtr _ _ => rw [hVal] at hEval; exact False.elim hEval
                    | rangeTo _ => rw [hVal] at hEval; exact False.elim hEval
                    | rangeFrom _ => rw [hVal] at hEval; exact False.elim hEval
                | unwindResume =>
                  unfold evalStep at hEval
                  rw [hFr] at hEval; dsimp only at hEval
                  rw [hSomeB] at hEval; dsimp only at hEval
                  rw [hBb] at hEval; dsimp only at hEval
                  rw [hNoneStmt] at hEval; dsimp only at hEval
                  rw [ite_bool_true hIdx, hTerm] at hEval
                  unfold evalTerminator at hEval
                  rw [hTerm] at hEval
                  exact False.elim hEval
                | unsupported =>
                  unfold evalStep at hEval
                  rw [hFr] at hEval; dsimp only at hEval
                  rw [hSomeB] at hEval; dsimp only at hEval
                  rw [hBb] at hEval; dsimp only at hEval
                  rw [hNoneStmt] at hEval; dsimp only at hEval
                  rw [ite_bool_true hIdx, hTerm] at hEval
                  unfold evalTerminator at hEval
                  rw [hTerm] at hEval
                  exact False.elim hEval
                | coreCall _ _ _ _ _ =>
                  unfold evalStep at hEval
                  rw [hFr] at hEval; dsimp only at hEval
                  rw [hSomeB] at hEval; dsimp only at hEval
                  rw [hBb] at hEval; dsimp only at hEval
                  rw [hNoneStmt] at hEval; dsimp only at hEval
                  rw [ite_bool_true hIdx, hTerm] at hEval
                  unfold evalTerminator at hEval
                  rw [hTerm] at hEval
                  exact False.elim hEval

/-! ## 4. Zero-`Prop`-Arg `@[irreducible] CallSpecCut` and `CallCutTree` -/

/-- Unsealed denotation of a modular callee contract (`0` `Prop` arguments). -/
@[expose] def denoteCallSpecCut (callees : List CallSpec) (impl :
    CallImplBundle)
    (spec : CallSpec) : Prop :=
  ∀ (m0 : MemoryState) (cm0 : CallerMemory) (args : List Val),
    match byteSubLensGet spec.mutLens m0 with
    | none => True
    | some preBytes =>
      spec.precondBool preBytes args = true →
      wpFrameOutcome spec.mutLens (calleeLookup callees) impl.body impl.fuel
        { frames := [{ defId := 0, blockIdx := 0, stmtIdx := 0,
                       locals := impl.mkLocals spec.mutLens args }]
          callerMem := cm0
          mem := m0 }
        (fun out =>
          match out with
          | .returned retVal mOut =>
            spec.canNormal = true ∧
            UpdatesOnly spec.mutLens m0 mOut ∧
            ∃ postBytes,
              byteSubLensGet spec.mutLens mOut = some postBytes ∧
              spec.ensuresNormalBool preBytes retVal postBytes args = true
          | .unwound mOut =>
            spec.canUnwind = true ∧
            UpdatesOnly spec.mutLens m0 mOut ∧
            ∃ postPartialBytes,
              byteSubLensGet spec.mutLens mOut = some postPartialBytes ∧
              spec.ensuresUnwindBool preBytes postPartialBytes args = true
          | .abortTerminate _ => False)

/-- Zero-`Prop`-arg sealed callee contract boundary (`@[irreducible]` so outer
callers never unfold inner callee bodies during modular verification). -/
@[irreducible] def CallSpecCut (callees : List CallSpec)
    (impl : CallImplBundle) (spec : CallSpec) : Prop :=
  denoteCallSpecCut callees impl spec

/-- Seals a callee contract proof behind `@[irreducible] CallSpecCut`. -/
theorem seal_callSpecCut (callees : List CallSpec) (impl : CallImplBundle)
    (spec : CallSpec) (h : denoteCallSpecCut callees impl spec) :
    CallSpecCut callees impl spec := by
  unfold CallSpecCut
  exact h

/-- Opens a sealed `CallSpecCut` strictly inside generic composition
combinators. -/
theorem open_callSpecCut (callees : List CallSpec) (impl : CallImplBundle)
    (spec : CallSpec) (h : CallSpecCut callees impl spec) :
    denoteCallSpecCut callees impl spec := by
  unfold CallSpecCut at h
  exact h

/-- Acyclic modular certificate tree sealing arbitrary call depths `depth`,
defined via `@Nat.rec`. -/
@[expose] def CallCutTree (implOf : DefId → Option (CallImplBundle × List
    CallSpec))
    (depth : Nat) (callees : List CallSpec) : Prop :=
  @Nat.rec (fun _ => List CallSpec → Prop)
    (fun cs => cs = [])
    (fun _ ih cs =>
      ∀ (defId : DefId) (cSpec : CallSpec),
        calleeLookup cs defId = some cSpec →
        cSpec.calleeDefId = defId ∧
        ∃ impl subCallees,
          implOf defId = some (impl, subCallees) ∧
          CallSpecCut subCallees impl cSpec ∧
          ih subCallees)
    depth callees

/-! ## 5. Multi-Frame Stack Semantics and Compositional Soundness -/

/-- Saved caller continuation frame pushed on `.call`. -/
structure SavedCaller where
  callerLens : ByteSubLens
  callees : List CallSpec
  body : Body
  frameDefId : DefId
  frameLocals : List LocalSlot
  dstLocalId : LocalId
  dstTy : MirTy
  onRet : Option BasicBlockId
  onUnwind : UnwindAction

/-- Active top frame during concrete multi-frame stack execution. -/
structure ExecStackFrame where
  callerLens : ByteSubLens
  callees : List CallSpec
  body : Body
  frame : FrameState

/-- Concrete multi-frame execution machine state. -/
inductive StackMode where
  | running (top : ExecStackFrame) (callers : List SavedCaller)
      (mem : MemoryState) (cm : CallerMemory)
  | unwinding (callers : List SavedCaller) (mem : MemoryState)
      (cm : CallerMemory)
  | terminated (out : FrameTermOut)

/-- Theory-layer small-step multi-frame stack overlay uniting single-frame
`Trusted.MirSemantics.evalStep` for intra-frame steps with
`subLensContained`-checked call push/pop (`CallImplBundle.mkLocals`), abstract
assertion panic transitions, and unwind cleanup propagation. `unwind_root`
models an unwind exiting the modeled call subtree to an outer enclosing
boundary (`.terminated (.unwound mem)`), omitting whole-program root-unwind UB,
frame-pop stack-local deallocation, unwind `_0` checks, and protector release.
-/
inductive StackStep
    (implOf : DefId → Option (CallImplBundle × List CallSpec)) :
    StackMode → StackMode → Prop where
  | intra {top : ExecStackFrame} {callers : List SavedCaller}
      {mem : MemoryState} {cm : CallerMemory} {st' : State} {fr' : FrameState} :
      evalStep (Anneal.MirWp.bodyProg top.body) 0 ⟨[top.frame], cm, mem⟩ =
        .step st' →
      st'.frames = [fr'] →
      StackStep implOf
        (.running top callers mem cm)
        (.running { top with frame := fr' } callers st'.mem st'.callerMem)
  | ret_root {top : ExecStackFrame} {mem : MemoryState} {cm : CallerMemory}
      {rv : Val} {cm' : CallerMemory} :
      evalStep (Anneal.MirWp.bodyProg top.body) 0 ⟨[top.frame], cm, mem⟩ =
        .done (.returned ⟨rv, cm'⟩) →
      StackStep implOf
        (.running top [] mem cm)
        (.terminated (.returned rv mem))
  | ret_pop {top : ExecStackFrame} {saved : SavedCaller}
      {rest : List SavedCaller} {mem memC memW : MemoryState}
      {cm cm' : CallerMemory} {rv rvC : Val} {retBb : BasicBlockId}
      {locs' : List LocalSlot} :
      evalStep (Anneal.MirWp.bodyProg top.body) 0 ⟨[top.frame], cm, mem⟩ =
        .done (.returned ⟨rv, cm'⟩) →
      evalCallExitStep saved.body ⟨saved.onRet, saved.onUnwind⟩
          (.normal rv mem) = .stepNormal retBb rvC memC →
      writePlace saved.frameLocals memC saved.dstLocalId saved.dstTy rvC =
        .ok (locs', memW) →
      StackStep implOf
        (.running top (saved :: rest) mem cm)
        (.running ⟨saved.callerLens, saved.callees, saved.body,
          ⟨saved.frameDefId, retBb, 0, locs', none, none, none⟩⟩ rest memW cm)
  | call_push {top : ExecStackFrame} {callers : List SavedCaller}
      {mem memArgs : MemoryState} {cm : CallerMemory}
      {bb : BasicBlock} {callee : DefId} {args : List Operand}
      {dst : Place} {dstTy : MirTy} {onRet : Option BasicBlockId}
      {onUnwind : UnwindAction} {cSpec : CallSpec} {cImpl : CallImplBundle}
      {subCallees : List CallSpec} {argVals : List Val}
      {localsArgs : List LocalSlot} :
      Trusted.MirSemantics.getElem? top.body.basicBlocks top.frame.blockIdx =
        some bb →
      top.frame.stmtIdx = bb.statements.length →
      bb.terminator = .call callee args dst onRet onUnwind →
      dst.projection = [] →
      Trusted.MirSemantics.getElem? top.body.locals dst.localId = some dstTy →
      calleeLookup top.callees callee = some cSpec →
      subLensContained cSpec.mutLens top.callerLens = true →
      EvalCallArgs top.body.locals top.frame.locals mem args argVals
        localsArgs memArgs →
      implOf callee = some (cImpl, subCallees) →
      StackStep implOf
        (.running top callers mem cm)
        (.running
          ⟨cSpec.mutLens, subCallees, cImpl.body,
            ⟨0, 0, 0, cImpl.mkLocals cSpec.mutLens argVals, none, none, none⟩⟩
          (⟨top.callerLens, top.callees, top.body, top.frame.defId, localsArgs,
            dst.localId, dstTy, onRet, onUnwind⟩ :: callers)
          memArgs cm)
  | assert_pass {top : ExecStackFrame} {callers : List SavedCaller}
      {mem mem' : MemoryState} {cm : CallerMemory}
      {bb : BasicBlock} {cond : Operand} {expected : Bool} {msg : AssertKind}
      {target : BasicBlockId} {unwind : UnwindAction}
      {locals' : List LocalSlot} :
      Trusted.MirSemantics.getElem? top.body.basicBlocks top.frame.blockIdx =
        some bb →
      top.frame.stmtIdx = bb.statements.length →
      bb.terminator = .assert cond expected msg target unwind →
      evalPrimitiveOperand top.body.locals top.frame.locals mem cond =
        .ok (.bool expected, locals', mem') →
      StackStep implOf
        (.running top callers mem cm)
        (.running { top with
          frame := { top.frame with
            blockIdx := target, stmtIdx := 0, locals := locals',
            sysrootOp? := none } }
          callers mem' cm)
  | assert_unwind_cleanup {top : ExecStackFrame} {callers : List SavedCaller}
      {mem mem' memC : MemoryState} {cm : CallerMemory}
      {bb : BasicBlock} {cond : Operand} {expected : Bool} {msg : AssertKind}
      {target cleanupBb : BasicBlockId} {unwind : UnwindAction}
      {locals' : List LocalSlot} :
      Trusted.MirSemantics.getElem? top.body.basicBlocks top.frame.blockIdx =
        some bb →
      top.frame.stmtIdx = bb.statements.length →
      bb.terminator = .assert cond expected msg target unwind →
      evalPrimitiveOperand top.body.locals top.frame.locals mem cond =
        .ok (.bool (!expected), locals', mem') →
      evalCallExitStep top.body ⟨none, unwind⟩ (.unwind mem') =
        .stepCleanup cleanupBb memC →
      StackStep implOf
        (.running top callers mem cm)
        (.running { top with
          frame := ⟨top.frame.defId, cleanupBb, 0, locals', none, none, none⟩ }
          callers memC cm)
  | assert_unwind_exit {top : ExecStackFrame} {callers : List SavedCaller}
      {mem mem' memC : MemoryState} {cm : CallerMemory}
      {bb : BasicBlock} {cond : Operand} {expected : Bool} {msg : AssertKind}
      {target : BasicBlockId} {unwind : UnwindAction}
      {locals' : List LocalSlot} :
      Trusted.MirSemantics.getElem? top.body.basicBlocks top.frame.blockIdx =
        some bb →
      top.frame.stmtIdx = bb.statements.length →
      bb.terminator = .assert cond expected msg target unwind →
      evalPrimitiveOperand top.body.locals top.frame.locals mem cond =
        .ok (.bool (!expected), locals', mem') →
      evalCallExitStep top.body ⟨none, unwind⟩ (.unwind mem') =
        .exitUnwind memC →
      StackStep implOf
        (.running top callers mem cm)
        (.unwinding callers memC cm)
  | assert_abort_terminate {top : ExecStackFrame} {callers : List SavedCaller}
      {mem mem' memC : MemoryState} {cm : CallerMemory}
      {bb : BasicBlock} {cond : Operand} {expected : Bool} {msg : AssertKind}
      {target : BasicBlockId} {unwind : UnwindAction}
      {locals' : List LocalSlot} :
      Trusted.MirSemantics.getElem? top.body.basicBlocks top.frame.blockIdx =
        some bb →
      top.frame.stmtIdx = bb.statements.length →
      bb.terminator = .assert cond expected msg target unwind →
      evalPrimitiveOperand top.body.locals top.frame.locals mem cond =
        .ok (.bool (!expected), locals', mem') →
      evalCallExitStep top.body ⟨none, unwind⟩ (.unwind mem') =
        .exitTerminate memC →
      StackStep implOf
        (.running top callers mem cm)
        (.terminated (.abortTerminate memC))
  | unwind_resume {top : ExecStackFrame} {callers : List SavedCaller}
      {mem : MemoryState} {cm : CallerMemory} {bb : BasicBlock} :
      Trusted.MirSemantics.getElem? top.body.basicBlocks top.frame.blockIdx =
        some bb →
      top.frame.stmtIdx = bb.statements.length →
      bb.terminator = .unwindResume →
      checkCleanupBlock top.body top.frame.blockIdx = true →
      StackStep implOf
        (.running top callers mem cm)
        (.unwinding callers mem cm)
  | unwind_root {mem : MemoryState} {cm : CallerMemory} :
      StackStep implOf
        (.unwinding [] mem cm)
        (.terminated (.unwound mem))
  | unwind_pop_cleanup {saved : SavedCaller} {rest : List SavedCaller}
      {mem memC : MemoryState} {cm : CallerMemory} {cleanupBb : BasicBlockId} :
      evalCallExitStep saved.body ⟨saved.onRet, saved.onUnwind⟩ (.unwind mem) =
        .stepCleanup cleanupBb memC →
      StackStep implOf
        (.unwinding (saved :: rest) mem cm)
        (.running ⟨saved.callerLens, saved.callees, saved.body,
          ⟨saved.frameDefId, cleanupBb, 0, saved.frameLocals,
            none, none, none⟩⟩ rest memC cm)
  | unwind_pop_continue {saved : SavedCaller} {rest : List SavedCaller}
      {mem memC : MemoryState} {cm : CallerMemory} :
      evalCallExitStep saved.body ⟨saved.onRet, saved.onUnwind⟩ (.unwind mem) =
        .exitUnwind memC →
      StackStep implOf
        (.unwinding (saved :: rest) mem cm)
        (.unwinding rest memC cm)
  | unwind_pop_terminate {saved : SavedCaller} {rest : List SavedCaller}
      {mem memC : MemoryState} {cm : CallerMemory} :
      evalCallExitStep saved.body ⟨saved.onRet, saved.onUnwind⟩ (.unwind mem) =
        .exitTerminate memC →
      StackStep implOf
        (.unwinding (saved :: rest) mem cm)
        (.terminated (.abortTerminate memC))

/-- Reflexive-transitive closure of multi-frame stack transitions. -/
inductive StackReaches
    (implOf : DefId → Option (CallImplBundle × List CallSpec)) :
    StackMode → StackMode → Prop where
  | refl {s : StackMode} : StackReaches implOf s s
  | tail {s₁ s₂ s₃ : StackMode} :
      StackReaches implOf s₁ s₂ →
      StackStep implOf s₂ s₃ →
      StackReaches implOf s₁ s₃

/-- Transitivity of `StackReaches`. -/
theorem stackReaches_trans
    {implOf : DefId → Option (CallImplBundle × List CallSpec)}
    {s₁ s₂ s₃ : StackMode}
    (h₁ : StackReaches implOf s₁ s₂) (h₂ : StackReaches implOf s₂ s₃) :
    StackReaches implOf s₁ s₃ := by
  induction h₂ with
  | refl => exact h₁
  | tail _ hStep ih => exact .tail ih hStep

/-- Appends an outer caller stack suffix beneath a `StackMode`. -/
@[expose] def appendOuterCallers (outer : List SavedCaller) : StackMode →
    StackMode
  | .running top inner mem cm => .running top (inner ++ outer) mem cm
  | .unwinding inner mem cm => .unwinding (inner ++ outer) mem cm
  | .terminated out => .terminated out

private theorem stackStep_lift_outer
    {implOf : DefId → Option (CallImplBundle × List CallSpec)}
    {outer : List SavedCaller} {s₁ s₂ : StackMode}
    (hStep : StackStep implOf s₁ s₂) :
    match s₂ with
    | .running _ _ _ _ =>
      StackStep implOf (appendOuterCallers outer s₁)
        (appendOuterCallers outer s₂)
    | .unwinding _ _ _ =>
      StackStep implOf (appendOuterCallers outer s₁)
        (appendOuterCallers outer s₂)
    | .terminated (.abortTerminate _) =>
      StackStep implOf (appendOuterCallers outer s₁)
        (appendOuterCallers outer s₂)
    | .terminated (.returned rv mem) =>
      ∃ top cm,
        s₁ = .running top [] mem cm ∧
        ∀ saved rest retBb rvC memC locs' memW,
          outer = saved :: rest →
          evalCallExitStep saved.body ⟨saved.onRet, saved.onUnwind⟩
              (.normal rv mem) = .stepNormal retBb rvC memC →
          writePlace saved.frameLocals memC saved.dstLocalId saved.dstTy rvC =
            .ok (locs', memW) →
          StackStep implOf
            (appendOuterCallers outer s₁)
            (.running ⟨saved.callerLens, saved.callees, saved.body,
              ⟨saved.frameDefId, retBb, 0, locs', none, none, none⟩⟩
              rest memW cm)
    | .terminated (.unwound mem) =>
      ∃ cm, s₁ = .unwinding [] mem cm ∧
        appendOuterCallers outer s₁ = .unwinding outer mem cm := by
  cases hStep with
  | intra hEv hFr => exact .intra hEv hFr
  | @ret_root top mem cm rv cm' hEv =>
    refine ⟨top, cm, rfl, ?_⟩
    intro saved rest retBb rvC memC locs' memW hOuter hCont hWr
    subst hOuter
    exact .ret_pop hEv hCont hWr
  | ret_pop hEv hCont hWr => exact .ret_pop hEv hCont hWr
  | call_push hBb hIdx hTerm hProj hTy hLook hLens hArgs hImpl =>
    exact .call_push hBb hIdx hTerm hProj hTy hLook hLens hArgs hImpl
  | assert_pass hBb hIdx hTerm hOp => exact .assert_pass hBb hIdx hTerm hOp
  | assert_unwind_cleanup hBb hIdx hTerm hOp hCont =>
    exact .assert_unwind_cleanup hBb hIdx hTerm hOp hCont
  | assert_unwind_exit hBb hIdx hTerm hOp hCont =>
    exact .assert_unwind_exit hBb hIdx hTerm hOp hCont
  | assert_abort_terminate hBb hIdx hTerm hOp hCont =>
    exact .assert_abort_terminate hBb hIdx hTerm hOp hCont
  | unwind_resume hBb hIdx hTerm hCl => exact .unwind_resume hBb hIdx hTerm hCl
  | @unwind_root mem cm => exact ⟨cm, rfl, rfl⟩
  | unwind_pop_cleanup hCont => exact .unwind_pop_cleanup hCont
  | unwind_pop_continue hCont => exact .unwind_pop_continue hCont
  | unwind_pop_terminate hCont => exact .unwind_pop_terminate hCont

private theorem evalCallTerminator_step_preserves_callerMem (callerBody : Body)
    (bb : BasicBlock) (caller : FrameState) (callers : List FrameState)
    (mem : MemoryState) (callerMem : CallerMemory) (calleeDefId : DefId)
    (sysrootOp? : Option SysrootNumOp) (calleeBody : Body)
    (args : List Operand) (dst : Place) (target : Option BasicBlockId)
    (unwind : UnwindAction) (st' : State)
    (hCall : evalCallTerminator callerBody bb caller callers mem callerMem
      calleeDefId sysrootOp? calleeBody args dst target unwind = .step st') :
    st'.callerMem = callerMem := by
  cases evalCallTerminator_cases callerBody bb caller callers mem callerMem
      calleeDefId sysrootOp? calleeBody args dst target unwind with
  | inl h =>
    cases h with
    | intro k hk => rw [hk] at hCall; cases hCall
  | inr h =>
    cases h with
    | intro s' hs' =>
      rw [hs'.1] at hCall; injection hCall with hEq; rw [← hEq]; exact hs'.2

private theorem evalStep_step_preserves_callerMem (b : Body) (fr : FrameState)
    (cm : CallerMemory) (mem : MemoryState) (st' : State)
    (hStep : evalStep (Anneal.MirWp.bodyProg b) 0 ⟨[fr], cm, mem⟩ = .step st') :
    st'.callerMem = cm := by
  unfold evalStep at hStep
  dsimp only at hStep
  cases hBody : activeFrameBody (Anneal.MirWp.bodyProg b) fr with
  | none => rw [hBody] at hStep; cases hStep
  | some body =>
    rw [hBody] at hStep
    dsimp only at hStep
    cases hBb :
        Trusted.MirSemantics.getElem? body.basicBlocks fr.blockIdx with
    | none => rw [hBb] at hStep; cases hStep
    | some bb =>
      rw [hBb] at hStep
      dsimp only at hStep
      cases hStmt :
          Trusted.MirSemantics.getElem? bb.statements fr.stmtIdx with
      | some stmt =>
        rw [hStmt] at hStep
        dsimp only at hStep
        cases stmt with
        | nop => unfold evalStatement at hStep; cases hStep; rfl
        | unsupported => unfold evalStatement at hStep; cases hStep
        | storageLive id =>
          unfold evalStatement at hStep
          dsimp only at hStep
          cases hTy : Trusted.MirSemantics.getElem? body.locals id with
          | none => rw [hTy] at hStep; cases hStep
          | some _ =>
            rw [hTy] at hStep
            dsimp only at hStep
            cases hLoc : Trusted.MirSemantics.getElem? fr.locals id with
            | none => rw [hLoc] at hStep; cases hStep
            | some _ =>
              rw [hLoc] at hStep
              dsimp only at hStep
              cases hSet : Trusted.MirSemantics.setElem? fr.locals id _ with
              | none => rw [hSet] at hStep; cases hStep
              | some _ =>
                rw [hSet] at hStep
                dsimp only at hStep
                cases hDe : deallocateLocal mem _ with
                | error _ => rw [hDe] at hStep; cases hStep
                | ok _ => rw [hDe] at hStep; cases hStep; rfl
        | storageDead id =>
          unfold evalStatement at hStep
          dsimp only at hStep
          cases hZero : Nat.beq id 0 with
          | true => rw [ite_bool_true hZero] at hStep; cases hStep
          | false =>
            rw [ite_bool_false hZero] at hStep
            cases hLoc : Trusted.MirSemantics.getElem? fr.locals id with
            | none => rw [hLoc] at hStep; cases hStep
            | some _ =>
              rw [hLoc] at hStep
              dsimp only at hStep
              cases hSet :
                  Trusted.MirSemantics.setElem? fr.locals id .dead with
              | none => rw [hSet] at hStep; cases hStep
              | some _ =>
                rw [hSet] at hStep
                dsimp only at hStep
                cases hDe : deallocateLocal mem _ with
                | error _ => rw [hDe] at hStep; cases hStep
                | ok _ => rw [hDe] at hStep; cases hStep; rfl
        | assign dst rv =>
          unfold evalStatement at hStep
          dsimp only at hStep
          cases hProj : !dst.projection.isEmpty with
          | true => rw [ite_bool_true hProj] at hStep; cases hStep
          | false =>
            rw [ite_bool_false hProj] at hStep
            cases hTy :
                Trusted.MirSemantics.getElem? body.locals dst.localId with
            | none => rw [hTy] at hStep; cases hStep
            | some _ =>
              rw [hTy] at hStep
              dsimp only at hStep
              cases hRv : evalRvalue body.locals fr.locals mem _ rv with
              | error _ => rw [hRv] at hStep; cases hStep
              | ok _ =>
                rw [hRv] at hStep
                dsimp only at hStep
                cases hWr : writePlace _ _ dst.localId _ _ with
                | error _ => rw [hWr] at hStep; cases hStep
                | ok _ => rw [hWr] at hStep; cases hStep; rfl
      | none =>
        rw [hStmt] at hStep
        dsimp only at hStep
        cases hIdx : Nat.beq fr.stmtIdx bb.statements.length with
        | false => rw [ite_bool_false hIdx] at hStep; cases hStep
        | true =>
          rw [ite_bool_true hIdx] at hStep
          cases hTerm : bb.terminator with
          | goto _ =>
            unfold evalTerminator jumpToBlock at hStep
            rw [hTerm] at hStep
            cases hStep
            rfl
          | unreachable =>
            unfold evalTerminator at hStep; rw [hTerm] at hStep; cases hStep
          | unwindResume =>
            unfold evalTerminator at hStep; rw [hTerm] at hStep; cases hStep
          | assert cond expected msg target unwind =>
            unfold evalTerminator at hStep
            rw [hTerm] at hStep
            dsimp only [attachCallers] at hStep
            cases hCond :
                evalPrimitiveOperand body.locals fr.locals mem cond with
            | error _ => rw [hCond] at hStep; cases hStep
            | ok res =>
              rw [hCond] at hStep
              dsimp only at hStep
              cases hVal : res.1 with
              | bool condB =>
                rw [hVal] at hStep
                dsimp only at hStep
                cases hEq : (condB == expected) with
                | true =>
                  rw [ite_bool_true hEq] at hStep
                  unfold jumpToBlock at hStep
                  cases hStep
                  rfl
                | false =>
                  rw [ite_bool_false hEq] at hStep
                  dsimp only [Anneal.MirWp.bodyProg] at hStep
                  let ⟨_, hFault⟩ :=
                    evalAssertFailure_unwind_fault msg unwind cm true
                  rw [hFault] at hStep
                  cases hStep
              | scalar _ | optionVal _ | range _ _ | boxPtr _ _ | vec _ _ _ => rw [hVal] at hStep; cases hStep
              | ptr _ => rw [hVal] at hStep; cases hStep
              | char _ => rw [hVal] at hStep; cases hStep
              | ordering _ => rw [hVal] at hStep; cases hStep
              | unit => rw [hVal] at hStep; cases hStep
              | enumVal _ _ => rw [hVal] at hStep; cases hStep
              | tuple _ => rw [hVal] at hStep; cases hStep
              | bytes _ => rw [hVal] at hStep; cases hStep
              | array _ => rw [hVal] at hStep; cases hStep
              | slicePtr _ _ => rw [hVal] at hStep; cases hStep
              | rangeTo _ => rw [hVal] at hStep; cases hStep
              | rangeFrom _ => rw [hVal] at hStep; cases hStep
          | unsupported =>
            unfold evalTerminator at hStep; rw [hTerm] at hStep; cases hStep
          | coreCall _ _ _ _ _ =>
            unfold evalTerminator at hStep; rw [hTerm] at hStep; cases hStep
          | call callee args dst target unwind =>
            rw [hTerm] at hStep
            dsimp only at hStep
            cases hCb :
                Trusted.MirSemantics.getElem? (Anneal.MirWp.bodyProg b).bodies
                  callee with
            | none => rw [hCb] at hStep; cases hStep
            | some cbody =>
              rw [hCb] at hStep
              exact evalCallTerminator_step_preserves_callerMem body bb fr []
                mem cm callee none cbody args dst target unwind st' hStep
          | sysrootCall op args dst target unwind =>
            rw [hTerm] at hStep
            exact evalCallTerminator_step_preserves_callerMem body bb fr [] mem
              cm 0 (some op) (sysrootNumBody op) args dst target unwind st'
              hStep
          | return_ =>
            unfold evalTerminator at hStep
            rw [hTerm] at hStep
            dsimp only at hStep
            cases hCl : bb.cleanup with
            | true => rw [ite_bool_true hCl] at hStep; cases hStep
            | false =>
              rw [ite_bool_false hCl] at hStep
              cases hLoc0 : Trusted.MirSemantics.getElem? fr.locals 0 with
              | none => rw [hLoc0] at hStep; cases hStep
              | some sl0 =>
                rw [hLoc0] at hStep
                cases sl0 with
                | dead | partialTuple _ => cases hStep
                | immediate ov =>
                  cases ov with
                  | none => cases hStep
                  | some _ => cases hStep
                | indirect mp =>
                  cases hTy0 : Trusted.MirSemantics.getElem? body.locals 0 with
                  | none => rw [hTy0] at hStep; cases hStep
                  | some _ =>
                    rw [hTy0] at hStep
                    dsimp only at hStep
                    cases hLd : loadIndirect mem _ mp with
                    | error _ => rw [hLd] at hStep; cases hStep
                    | ok ov =>
                      rw [hLd] at hStep
                      cases ov with
                      | none => cases hStep
                      | some _ => cases hStep
          | switchInt discr tgts =>
            unfold evalTerminator at hStep
            rw [hTerm] at hStep
            dsimp only at hStep
            cases hEv :
                evalPrimitiveOperand body.locals fr.locals mem discr with
            | error _ => rw [hEv] at hStep; cases hStep
            | ok res =>
              rw [hEv] at hStep
              dsimp only at hStep
              cases hRes : res.1 with
              | scalar sv =>
                rw [hRes] at hStep; dsimp only at hStep
                cases hTg : evalSwitchBranches sv.width sv.bits
                    tgts.otherwise tgts.branches with
                | error _ => rw [hTg] at hStep; cases hStep
                | ok _ =>
                  rw [hTg] at hStep; unfold jumpToBlock at hStep
                  cases hStep; rfl
              | bool bVal =>
                rw [hRes] at hStep; dsimp only at hStep
                cases hTg : evalBoolSwitchBranches bVal tgts.otherwise
                    tgts.branches with
                | error _ => rw [hTg] at hStep; cases hStep
                | ok _ =>
                  rw [hTg] at hStep; unfold jumpToBlock at hStep
                  cases hStep; rfl
              | char cVal =>
                rw [hRes] at hStep; dsimp only at hStep
                cases hTg : evalCharSwitchBranches cVal tgts.otherwise
                    tgts.branches with
                | error _ => rw [hTg] at hStep; cases hStep
                | ok _ =>
                  rw [hTg] at hStep; unfold jumpToBlock at hStep
                  cases hStep; rfl
              | ptr _ =>
                rw [hRes] at hStep; dsimp only at hStep
                cases hBr : tgts.branches with
                | cons _ _ => rw [hBr] at hStep; cases hStep
                | nil =>
                  rw [hBr] at hStep; unfold jumpToBlock at hStep
                  cases hStep; rfl
              | ordering _ =>
                rw [hRes] at hStep; dsimp only at hStep
                cases hBr : tgts.branches with
                | cons _ _ => rw [hBr] at hStep; cases hStep
                | nil =>
                  rw [hBr] at hStep; unfold jumpToBlock at hStep
                  cases hStep; rfl
              | unit =>
                rw [hRes] at hStep; dsimp only at hStep
                cases hBr : tgts.branches with
                | cons _ _ => rw [hBr] at hStep; cases hStep
                | nil =>
                  rw [hBr] at hStep; unfold jumpToBlock at hStep
                  cases hStep; rfl
              | enumVal _ _ =>
                rw [hRes] at hStep; dsimp only at hStep
                cases hBr : tgts.branches with
                | cons _ _ => rw [hBr] at hStep; cases hStep
                | nil =>
                  rw [hBr] at hStep; unfold jumpToBlock at hStep
                  cases hStep; rfl
              | tuple _ =>
                rw [hRes] at hStep; dsimp only at hStep
                cases hBr : tgts.branches with
                | cons _ _ => rw [hBr] at hStep; cases hStep
                | nil =>
                  rw [hBr] at hStep; unfold jumpToBlock at hStep
                  cases hStep; rfl
              | bytes _ =>
                rw [hRes] at hStep; dsimp only at hStep
                cases hBr : tgts.branches with
                | cons _ _ => rw [hBr] at hStep; cases hStep
                | nil =>
                  rw [hBr] at hStep; unfold jumpToBlock at hStep
                  cases hStep; rfl
              | slicePtr _ _ =>
                rw [hRes] at hStep; dsimp only at hStep
                cases hBr : tgts.branches with
                | cons _ _ => rw [hBr] at hStep; cases hStep
                | nil =>
                  rw [hBr] at hStep; unfold jumpToBlock at hStep
                  cases hStep; rfl
              | rangeTo _ =>
                rw [hRes] at hStep; dsimp only at hStep
                cases hBr : tgts.branches with
                | cons _ _ => rw [hBr] at hStep; cases hStep
                | nil =>
                  rw [hBr] at hStep; unfold jumpToBlock at hStep
                  cases hStep; rfl
              | rangeFrom _ =>
                rw [hRes] at hStep; dsimp only at hStep
                cases hBr : tgts.branches with
                | cons _ _ => rw [hBr] at hStep; cases hStep
                | nil =>
                  rw [hBr] at hStep; unfold jumpToBlock at hStep
                  cases hStep; rfl
              | array _ =>
                rw [hRes] at hStep; dsimp only at hStep
                cases hBr : tgts.branches with
                | cons _ _ => rw [hBr] at hStep; cases hStep
                | nil =>
                  rw [hBr] at hStep; unfold jumpToBlock at hStep
                  cases hStep; rfl
              | range _ _ =>
                rw [hRes] at hStep; dsimp only at hStep
                cases hBr : tgts.branches with
                | cons _ _ => rw [hBr] at hStep; cases hStep
                | nil =>
                  rw [hBr] at hStep; unfold jumpToBlock at hStep
                  cases hStep; rfl
              | optionVal _ =>
                rw [hRes] at hStep; dsimp only at hStep
                cases hBr : tgts.branches with
                | cons _ _ => rw [hBr] at hStep; cases hStep
                | nil =>
                  rw [hBr] at hStep; unfold jumpToBlock at hStep
                  cases hStep; rfl
              | vec _ _ _ =>
                rw [hRes] at hStep; dsimp only at hStep
                cases hBr : tgts.branches with
                | cons _ _ => rw [hBr] at hStep; cases hStep
                | nil =>
                  rw [hBr] at hStep; unfold jumpToBlock at hStep
                  cases hStep; rfl
              | boxPtr _ _ =>
                rw [hRes] at hStep; dsimp only at hStep
                cases hBr : tgts.branches with
                | cons _ _ => rw [hBr] at hStep; cases hStep
                | nil =>
                  rw [hBr] at hStep; unfold jumpToBlock at hStep
                  cases hStep; rfl

private def stackModeCm? : StackMode → Option CallerMemory
  | .running _ _ _ cm => some cm
  | .unwinding _ _ cm => some cm
  | .terminated _ => none

private theorem stackStep_source_cmSome
    {implOf : DefId → Option (CallImplBundle × List CallSpec)}
    {sB sC : StackMode} {cmC : CallerMemory}
    (hStep : StackStep implOf sB sC) (hC : stackModeCm? sC = some cmC) :
    stackModeCm? sB = some cmC := by
  cases hStep with
  | @intra top _ _ _ st' _ hEv _ =>
    dsimp only [stackModeCm?] at hC
    injection hC with hCEq
    rw [← hCEq]
    dsimp only [stackModeCm?]
    rw [evalStep_step_preserves_callerMem top.body top.frame _ _ st' hEv]
  | ret_root => cases hC
  | ret_pop => exact hC
  | call_push => exact hC
  | assert_pass => exact hC
  | assert_unwind_cleanup => exact hC
  | assert_unwind_exit => exact hC
  | assert_abort_terminate => cases hC
  | unwind_resume => exact hC
  | unwind_root => cases hC
  | unwind_pop_cleanup => exact hC
  | unwind_pop_continue => exact hC
  | unwind_pop_terminate => cases hC

private theorem stackReaches_preserves_cm
    {implOf : DefId → Option (CallImplBundle × List CallSpec)}
    {s₁ s₂ : StackMode} (hReach : StackReaches implOf s₁ s₂) :
    ∀ cm1 cm2,
      stackModeCm? s₁ = some cm1 →
      stackModeCm? s₂ = some cm2 →
      cm2 = cm1 := by
  induction hReach with
  | refl =>
    intro cm1 cm2 h1 h2
    have hEq := Eq.trans h2.symm h1
    injection hEq
  | tail _ hStepBC ih =>
    intro cm1 cm3 h1 h3
    exact ih cm1 cm3 h1 (stackStep_source_cmSome hStepBC h3)

private theorem stackStep_source_not_terminated
    {implOf : DefId → Option (CallImplBundle × List CallSpec)}
    {sB sC : StackMode} (hStep : StackStep implOf sB sC) :
    ∀ out, sB ≠ .terminated out := by
  intro out hEq
  rw [hEq] at hStep
  cases hStep

/-- General stack-frame suffix lifting: any non-terminating execution prefix
runs unchanged atop an arbitrary outer caller stack `outer`. -/
theorem stackReaches_frame_outer
    {implOf : DefId → Option (CallImplBundle × List CallSpec)}
    {outer : List SavedCaller} :
    ∀ {s₁ s₂ : StackMode},
      StackReaches implOf s₁ s₂ →
      (∀ out, s₂ ≠ .terminated out) →
      StackReaches implOf (appendOuterCallers outer s₁)
        (appendOuterCallers outer s₂) := by
  intro s₁ s₂ hReach
  induction hReach with
  | refl => intro _; exact .refl
  | tail _ hStepBC ih =>
    intro hNotTermC
    have hPrefix := ih (stackStep_source_not_terminated hStepBC)
    have hLift := stackStep_lift_outer (outer := outer) hStepBC
    cases hStepBC with
    | intra => exact .tail hPrefix hLift
    | ret_pop => exact .tail hPrefix hLift
    | call_push => exact .tail hPrefix hLift
    | assert_pass => exact .tail hPrefix hLift
    | assert_unwind_cleanup => exact .tail hPrefix hLift
    | assert_unwind_exit => exact .tail hPrefix hLift
    | unwind_resume => exact .tail hPrefix hLift
    | unwind_pop_cleanup => exact .tail hPrefix hLift
    | unwind_pop_continue => exact .tail hPrefix hLift
    | ret_root => exact False.elim (hNotTermC (.returned _ _) rfl)
    | unwind_root => exact False.elim (hNotTermC (.unwound _) rfl)
    | assert_abort_terminate =>
      exact False.elim (hNotTermC (.abortTerminate _) rfl)
    | unwind_pop_terminate =>
      exact False.elim (hNotTermC (.abortTerminate _) rfl)

private theorem stackReaches_in_outer_of_terminated
    {implOf : DefId → Option (CallImplBundle × List CallSpec)}
    {outer : List SavedCaller}
    {top0 : ExecStackFrame} {mem0 : MemoryState} {cm0 : CallerMemory}
    {out : FrameTermOut}
    (hReach : StackReaches implOf (.running top0 [] mem0 cm0)
      (.terminated out)) :
    match out with
    | .returned rv mem =>
      ∀ saved rest retBb rvC memC locs' memW,
        outer = saved :: rest →
        evalCallExitStep saved.body ⟨saved.onRet, saved.onUnwind⟩
            (.normal rv mem) = .stepNormal retBb rvC memC →
        writePlace saved.frameLocals memC saved.dstLocalId saved.dstTy rvC =
          .ok (locs', memW) →
        StackReaches implOf
          (.running top0 outer mem0 cm0)
          (.running ⟨saved.callerLens, saved.callees, saved.body,
            ⟨saved.frameDefId, retBb, 0, locs', none, none, none⟩⟩
            rest memW cm0)
    | .unwound mem =>
      StackReaches implOf
        (.running top0 outer mem0 cm0)
        (.unwinding outer mem cm0)
    | .abortTerminate mem =>
      StackReaches implOf
        (.running top0 outer mem0 cm0)
        (.terminated (.abortTerminate mem)) := by
  cases hReach with
  | tail hAB hStepBC =>
    have hPrefix := stackReaches_frame_outer (outer := outer) hAB
      (stackStep_source_not_terminated hStepBC)
    have hOuter0 : appendOuterCallers outer (.running top0 [] mem0 cm0) =
        .running top0 outer mem0 cm0 := rfl
    rw [hOuter0] at hPrefix
    have hLift := stackStep_lift_outer (outer := outer) hStepBC
    cases out with
    | returned rv mem =>
      dsimp only at hLift
      cases hLift with
      | intro topB hTop =>
        cases hTop with
        | intro cmB hRest =>
          have hCmEq : cmB = cm0 := by
            have hS : stackModeCm? (.running topB [] mem cmB) = some cmB := rfl
            rw [← hRest.1] at hS
            exact stackReaches_preserves_cm hAB cm0 cmB rfl hS
          intro saved rest retBb rvC memC locs' memW hOutEq hCont hWr
          have hStepPop :=
            hRest.2 saved rest retBb rvC memC locs' memW hOutEq hCont hWr
          rw [hCmEq] at hStepPop
          exact .tail hPrefix hStepPop
    | unwound mem =>
      dsimp only at hLift
      cases hLift with
      | intro cmB hRest =>
        have hCmEq : cmB = cm0 := by
          have hS : stackModeCm? (.unwinding [] mem cmB) = some cmB := rfl
          rw [← hRest.1] at hS
          exact stackReaches_preserves_cm hAB cm0 cmB rfl hS
        rw [hRest.2, hCmEq] at hPrefix
        exact hPrefix
    | abortTerminate mem =>
      dsimp only at hLift
      exact .tail hPrefix hLift

private theorem wpEvalStep_implies_stackExecutes
    {implOf : DefId → Option (CallImplBundle × List CallSpec)}
    {callerLens : ByteSubLens} {callees : List CallSpec} {body : Body}
    {fuel : Nat} {frame : FrameState} {mem : MemoryState} {cm : CallerMemory}
    {onDone : FrameTermOut → Prop}
    (ihFuel : ∀ frame' mem' cm' onDone',
      wpFrameOutcome callerLens (calleeLookup callees) body fuel
        ⟨[frame'], cm', mem'⟩ onDone' →
      ∃ out, StackReaches implOf
        (.running ⟨callerLens, callees, body, frame'⟩ [] mem' cm')
        (.terminated out) ∧ onDone' out)
    (hEval :
      match evalStep (Anneal.MirWp.bodyProg body) 0 ⟨[frame], cm, mem⟩ with
      | .step st' =>
        wpFrameOutcome callerLens (calleeLookup callees) body fuel st' onDone
      | .done (.returned rv) => onDone (.returned rv.ret mem)
      | .done (.unwound _) => False
      | .done (.aborted _) => False
      | .fault _ => False) :
    ∃ out,
      StackReaches implOf
        (.running ⟨callerLens, callees, body, frame⟩ [] mem cm)
        (.terminated out) ∧ onDone out := by
  cases hStep : evalStep (Anneal.MirWp.bodyProg body) 0 ⟨[frame], cm, mem⟩ with
  | fault _ => rw [hStep] at hEval; exact False.elim hEval
  | done out =>
    rw [hStep] at hEval
    cases out with
    | unwound _ => exact False.elim hEval
    | aborted cm' =>
      exact False.elim
        (evalStep_bodyProg_never_aborted body 0 ⟨[frame], cm, mem⟩ cm' hStep)
    | returned retOut =>
      refine ⟨.returned retOut.ret mem, .tail .refl (.ret_root hStep), hEval⟩
  | step st' =>
    rw [hStep] at hEval
    dsimp only at hEval
    cases hFr : st'.frames with
    | nil =>
      have hFalse : wpFrameOutcome callerLens (calleeLookup callees) body fuel
          st' onDone = False := by
        unfold wpFrameOutcome
        cases fuel with
        | zero => rfl
        | succ _ => dsimp only; rw [hFr]
      rw [hFalse] at hEval
      exact False.elim hEval
    | cons fr' restFr =>
      cases restFr with
      | cons _ _ =>
        have hFalse : wpFrameOutcome callerLens (calleeLookup callees) body fuel
            st' onDone = False := by
          unfold wpFrameOutcome
          cases fuel with
          | zero => rfl
          | succ _ => dsimp only; rw [hFr]
        rw [hFalse] at hEval
        exact False.elim hEval
      | nil =>
        have hCm :=
          evalStep_step_preserves_callerMem body frame cm mem st' hStep
        have hStEq : st' = ⟨[fr'], cm, st'.mem⟩ := by
          cases st'
          dsimp only at hFr hCm
          subst hFr hCm
          rfl
        rw [hStEq] at hEval
        cases ihFuel fr' st'.mem cm onDone hEval with
        | intro out hOut =>
          have hIntra : StackStep implOf
              (.running ⟨callerLens, callees, body, frame⟩ [] mem cm)
              (.running ⟨callerLens, callees, body, fr'⟩ [] st'.mem cm) := by
            have hRaw := StackStep.intra (implOf := implOf)
              (top := ⟨callerLens, callees, body, frame⟩) (callers := [])
              hStep hFr
            rw [hCm] at hRaw
            exact hRaw
          refine ⟨out, stackReaches_trans (.tail .refl hIntra) hOut.1, hOut.2⟩

private theorem wpAssert_implies_stackExecutes
    {implOf : DefId → Option (CallImplBundle × List CallSpec)}
    {callerLens : ByteSubLens} {callees : List CallSpec} {body : Body}
    {bb : BasicBlock} {cond : Operand} {expected : Bool} {msg : AssertKind}
    {target : BasicBlockId} {unwind : UnwindAction}
    {fuel : Nat} {frame : FrameState} {mem : MemoryState} {cm : CallerMemory}
    {onDone : FrameTermOut → Prop}
    (hBb : Trusted.MirSemantics.getElem? body.basicBlocks frame.blockIdx =
      some bb)
    (hIdxEq : frame.stmtIdx = bb.statements.length)
    (hTerm : bb.terminator = .assert cond expected msg target unwind)
    (ihFuel : ∀ frame' mem' cm' onDone',
      wpFrameOutcome callerLens (calleeLookup callees) body fuel
        ⟨[frame'], cm', mem'⟩ onDone' →
      ∃ out, StackReaches implOf
        (.running ⟨callerLens, callees, body, frame'⟩ [] mem' cm')
        (.terminated out) ∧ onDone' out)
    (hWp :
      match evalPrimitiveOperand body.locals frame.locals mem cond with
      | .error _ => False
      | .ok (v, locals', mem') =>
        match v with
        | .bool b =>
          if b == expected then
            wpFrameOutcome callerLens (calleeLookup callees) body fuel
              { frames := [{ frame with
                  blockIdx := target, stmtIdx := 0, locals := locals',
                  sysrootOp? := none }],
                callerMem := cm, mem := mem' } onDone
          else
            match evalCallExitStep body ⟨none, unwind⟩ (.unwind mem') with
            | .stepCleanup cleanupBb memC =>
              wpFrameOutcome callerLens (calleeLookup callees) body fuel
                { frames := [⟨frame.defId, cleanupBb, 0, locals',
                    none, none, none⟩],
                  callerMem := cm, mem := memC } onDone
            | .exitUnwind memC => onDone (.unwound memC)
            | .exitTerminate memC => onDone (.abortTerminate memC)
            | .stepNormal _ _ _ => False
            | .fault _ => False
        | .scalar _ => False
        | .ptr _ => False
        | .char _ => False
        | .ordering _ => False
        | .unit => False
        | .enumVal _ _ => False
        | .tuple _ => False
        | .bytes _ => False
        | .slicePtr _ _ => False
        | .rangeTo _ => False
        | .rangeFrom _ => False
        | .array _ => False
        | .range _ _ => False
        | .optionVal _ => False
        | .vec _ _ _ => False
        | .boxPtr _ _ => False) :
    ∃ out,
      StackReaches implOf
        (.running ⟨callerLens, callees, body, frame⟩ [] mem cm)
        (.terminated out) ∧ onDone out := by
  cases hOp : evalPrimitiveOperand body.locals frame.locals mem cond with
  | error _ => rw [hOp] at hWp; exact False.elim hWp
  | ok res =>
    rw [hOp] at hWp
    dsimp only at hWp
    cases hRes : res.1 with
    | scalar _ => rw [hRes] at hWp; exact False.elim hWp
    | ptr _ => rw [hRes] at hWp; exact False.elim hWp
    | char _ => rw [hRes] at hWp; exact False.elim hWp
    | ordering _ => rw [hRes] at hWp; exact False.elim hWp
    | unit => rw [hRes] at hWp; exact False.elim hWp
    | enumVal _ _ => rw [hRes] at hWp; exact False.elim hWp
    | tuple _ => rw [hRes] at hWp; exact False.elim hWp
    | bytes _ => rw [hRes] at hWp; exact False.elim hWp
    | slicePtr _ _ => rw [hRes] at hWp; exact False.elim hWp
    | rangeTo _ => rw [hRes] at hWp; exact False.elim hWp
    | rangeFrom _ => rw [hRes] at hWp; exact False.elim hWp
    | array _ => rw [hRes] at hWp; exact False.elim hWp
    | range _ _ => rw [hRes] at hWp; exact False.elim hWp
    | optionVal _ => rw [hRes] at hWp; exact False.elim hWp
    | vec _ _ _ => rw [hRes] at hWp; exact False.elim hWp
    | boxPtr _ _ => rw [hRes] at hWp; exact False.elim hWp
    | bool b =>
      rw [hRes] at hWp
      dsimp only at hWp
      cases hMatch : b == expected with
      | true =>
        rw [if_prop_true hMatch] at hWp
        have hBEq : b = expected := by
          cases b <;> cases expected <;> first | rfl | cases hMatch
        have hOpBool : evalPrimitiveOperand body.locals frame.locals mem cond =
            .ok (.bool expected, res.2.1, res.2.2) := by
          rw [hOp, ← hBEq, ← hRes]
        cases ihFuel
            { frame with
              blockIdx := target, stmtIdx := 0, locals := res.2.1,
              sysrootOp? := none }
            res.2.2 cm onDone hWp with
        | intro out hOut =>
          refine ⟨out,
            stackReaches_trans (.tail .refl
              (.assert_pass hBb hIdxEq hTerm hOpBool)) hOut.1,
            hOut.2⟩
      | false =>
        rw [if_prop_false hMatch] at hWp
        have hBNeg : b = !expected := by
          cases b <;> cases expected <;> first | rfl | cases hMatch
        have hOpBool : evalPrimitiveOperand body.locals frame.locals mem cond =
            .ok (.bool (!expected), res.2.1, res.2.2) := by
          rw [hOp, ← hBNeg, ← hRes]
        cases hCont : evalCallExitStep body ⟨none, unwind⟩
            (.unwind res.2.2) with
        | stepNormal _ _ _ => rw [hCont] at hWp; exact False.elim hWp
        | fault _ => rw [hCont] at hWp; exact False.elim hWp
        | exitUnwind memC =>
          rw [hCont] at hWp
          exact ⟨.unwound memC,
            .tail (.tail .refl
              (.assert_unwind_exit hBb hIdxEq hTerm hOpBool hCont))
              .unwind_root,
            hWp⟩
        | exitTerminate memC =>
          rw [hCont] at hWp
          exact ⟨.abortTerminate memC,
            .tail .refl
              (.assert_abort_terminate hBb hIdxEq hTerm hOpBool hCont),
            hWp⟩
        | stepCleanup cleanupBb memC =>
          rw [hCont] at hWp
          cases ihFuel
              ⟨frame.defId, cleanupBb, 0, res.2.1, none, none, none⟩
              memC cm onDone hWp with
          | intro out hOut =>
            refine ⟨out,
              stackReaches_trans (.tail .refl
                (.assert_unwind_cleanup hBb hIdxEq hTerm hOpBool hCont))
                hOut.1,
              hOut.2⟩

/-- General compositional multi-frame soundness theorem (`[propext]`): opens
`@[irreducible] CallSpecCut` strictly inside this generic combinator, composing
arbitrary acyclic call trees of depth `d` into concrete `StackReaches`
executions satisfying `onDone`. -/
theorem wpFrameOutcome_implies_stackExecutes
    (implOf : DefId → Option (CallImplBundle × List CallSpec)) :
    ∀ (d : Nat) (callees : List CallSpec),
      CallCutTree implOf d callees →
      ∀ (callerLens : ByteSubLens) (body : Body) (fuel : Nat)
        (frame : FrameState) (mem : MemoryState) (cm : CallerMemory)
        (onDone : FrameTermOut → Prop),
        wpFrameOutcome callerLens (calleeLookup callees) body fuel
          ⟨[frame], cm, mem⟩ onDone →
        ∃ out,
          StackReaches implOf
            (.running ⟨callerLens, callees, body, frame⟩ [] mem cm)
            (.terminated out) ∧
          onDone out := by
  intro d
  induction d with
  | zero =>
    intro callees hTree callerLens body fuel
    have hEmpty : callees = [] := hTree
    subst hEmpty
    induction fuel with
    | zero =>
      intro _ _ _ _ hWp
      exact False.elim hWp
    | succ fuel ihFuel =>
      intro frame mem cm onDone hWp
      unfold wpFrameOutcome at hWp
      dsimp only at hWp
      cases hSys : frame.sysrootOp? with
      | some _ =>
        rw [hSys] at hWp
        exact wpEvalStep_implies_stackExecutes ihFuel hWp
      | none =>
        rw [hSys] at hWp
        dsimp only at hWp
        cases hBb :
            Trusted.MirSemantics.getElem? body.basicBlocks frame.blockIdx with
        | none => rw [hBb] at hWp; exact False.elim hWp
        | some bb =>
          rw [hBb] at hWp
          dsimp only at hWp
          cases hIdx : Nat.beq frame.stmtIdx bb.statements.length with
          | false =>
            rw [if_prop_false hIdx] at hWp
            exact wpEvalStep_implies_stackExecutes ihFuel hWp
          | true =>
            rw [if_prop_true hIdx] at hWp
            have hIdxEq := natEq_of_beq frame.stmtIdx bb.statements.length hIdx
            cases hTerm : bb.terminator with
            | unsupported => rw [hTerm] at hWp; exact False.elim hWp
            | coreCall _ _ _ _ _ => rw [hTerm] at hWp; exact False.elim hWp
            | sysrootCall _ _ _ _ _ => rw [hTerm] at hWp; exact False.elim hWp
            | call callee args dst onRet onUnwind =>
              rw [hTerm] at hWp
              dsimp only at hWp
              cases hProj : (!dst.projection.isEmpty) with
              | true => rw [if_prop_true hProj] at hWp; exact False.elim hWp
              | false =>
                rw [if_prop_false hProj] at hWp
                cases hTy :
                    Trusted.MirSemantics.getElem? body.locals dst.localId with
                | none => rw [hTy] at hWp; exact False.elim hWp
                | some _ => rw [hTy] at hWp; exact False.elim hWp
            | unwindResume =>
              rw [hTerm] at hWp
              exact ⟨.unwound mem,
                .tail (.tail .refl (.unwind_resume hBb hIdxEq hTerm hWp.1))
                  .unwind_root,
                hWp.2⟩
            | assert cond expected msg target unwind =>
              rw [hTerm] at hWp
              dsimp only at hWp
              exact wpAssert_implies_stackExecutes hBb hIdxEq hTerm ihFuel hWp
            | goto _ =>
              rw [hTerm] at hWp
              exact wpEvalStep_implies_stackExecutes ihFuel hWp
            | switchInt _ _ =>
              rw [hTerm] at hWp
              exact wpEvalStep_implies_stackExecutes ihFuel hWp
            | return_ =>
              rw [hTerm] at hWp
              exact wpEvalStep_implies_stackExecutes ihFuel hWp
            | unreachable =>
              rw [hTerm] at hWp
              exact wpEvalStep_implies_stackExecutes ihFuel hWp
  | succ d ihNode =>
    intro callees hTree callerLens body fuel
    induction fuel with
    | zero =>
      intro _ _ _ _ hWp
      exact False.elim hWp
    | succ fuel ihFuel =>
      intro frame mem cm onDone hWp
      unfold wpFrameOutcome at hWp
      dsimp only at hWp
      cases hSys : frame.sysrootOp? with
      | some _ =>
        rw [hSys] at hWp
        exact wpEvalStep_implies_stackExecutes ihFuel hWp
      | none =>
        rw [hSys] at hWp
        dsimp only at hWp
        cases hBb :
            Trusted.MirSemantics.getElem? body.basicBlocks frame.blockIdx with
        | none => rw [hBb] at hWp; exact False.elim hWp
        | some bb =>
          rw [hBb] at hWp
          dsimp only at hWp
          cases hIdx : Nat.beq frame.stmtIdx bb.statements.length with
          | false =>
            rw [if_prop_false hIdx] at hWp
            exact wpEvalStep_implies_stackExecutes ihFuel hWp
          | true =>
            rw [if_prop_true hIdx] at hWp
            have hIdxEq := natEq_of_beq frame.stmtIdx bb.statements.length hIdx
            cases hTerm : bb.terminator with
            | unsupported => rw [hTerm] at hWp; exact False.elim hWp
            | coreCall _ _ _ _ _ => rw [hTerm] at hWp; exact False.elim hWp
            | sysrootCall _ _ _ _ _ => rw [hTerm] at hWp; exact False.elim hWp
            | unwindResume =>
              rw [hTerm] at hWp
              exact ⟨.unwound mem,
                .tail (.tail .refl (.unwind_resume hBb hIdxEq hTerm hWp.1))
                  .unwind_root,
                hWp.2⟩
            | assert cond expected msg target unwind =>
              rw [hTerm] at hWp
              dsimp only at hWp
              exact wpAssert_implies_stackExecutes hBb hIdxEq hTerm ihFuel hWp
            | goto _ =>
              rw [hTerm] at hWp
              exact wpEvalStep_implies_stackExecutes ihFuel hWp
            | switchInt _ _ =>
              rw [hTerm] at hWp
              exact wpEvalStep_implies_stackExecutes ihFuel hWp
            | return_ =>
              rw [hTerm] at hWp
              exact wpEvalStep_implies_stackExecutes ihFuel hWp
            | unreachable =>
              rw [hTerm] at hWp
              exact wpEvalStep_implies_stackExecutes ihFuel hWp
            | call callee args dst onRet onUnwind =>
            rw [hTerm] at hWp
            dsimp only at hWp
            cases hProj : dst.projection with
            | cons _ _ =>
              have hPTrue : (!dst.projection.isEmpty) = true := by
                rw [hProj]; rfl
              rw [if_prop_true hPTrue] at hWp
              exact False.elim hWp
            | nil =>
              have hPFalse : (!dst.projection.isEmpty) = false := by
                rw [hProj]; rfl
              rw [if_prop_false hPFalse] at hWp
              cases hTy :
                  Trusted.MirSemantics.getElem? body.locals dst.localId with
              | none => rw [hTy] at hWp; exact False.elim hWp
              | some dstTy =>
                rw [hTy] at hWp
                dsimp only at hWp
                cases hLook : calleeLookup callees callee with
                | none => rw [hLook] at hWp; exact False.elim hWp
                | some cSpec =>
                  rw [hLook] at hWp
                  dsimp only at hWp
                  have hLens := hWp.1
                  cases hWp.2 with
                  | intro argVals h1 =>
                    cases h1 with
                    | intro localsArgs h2 =>
                      cases h2 with
                      | intro memArgs h3 =>
                        have hArgs := h3.1
                        cases h3.2 with
                        | intro preBytes h4 =>
                          have hGetPre := h4.1
                          have hPre := h4.2.1
                          have hNorm := h4.2.2.1
                          have hUnw := h4.2.2.2
                          have hNodeSpec := hTree callee cSpec hLook
                          cases hNodeSpec with
                          | intro _ hNodeEx =>
                            cases hNodeEx with
                            | intro cImpl hCImplEx =>
                              cases hCImplEx with
                              | intro subCallees hSub =>
                                have hImplEq := hSub.1
                                have hCut := hSub.2.1
                                have hSubTree := hSub.2.2
                                have hDenote :=
                                  open_callSpecCut subCallees cImpl cSpec hCut
                                    memArgs cm argVals
                                rw [hGetPre] at hDenote
                                dsimp only at hDenote
                                have hCalleeWp := hDenote hPre
                                have ihCallee := ihNode subCallees hSubTree
                                  cSpec.mutLens cImpl.body cImpl.fuel
                                  ⟨0, 0, 0,
                                    cImpl.mkLocals cSpec.mutLens argVals,
                                    none, none, none⟩
                                  memArgs cm _ hCalleeWp
                                cases ihCallee with
                                | intro outCallee hCalleeOut =>
                                  have hPush : StackStep implOf
                                      (.running ⟨callerLens, callees, body,
                                        frame⟩ [] mem cm)
                                      (.running ⟨cSpec.mutLens, subCallees,
                                        cImpl.body,
                                        ⟨0, 0, 0,
                                          cImpl.mkLocals cSpec.mutLens
                                            argVals, none, none, none⟩⟩
                                        [⟨callerLens, callees, body,
                                          frame.defId, localsArgs, dst.localId,
                                          dstTy, onRet, onUnwind⟩]
                                        memArgs cm) :=
                                    .call_push hBb hIdxEq hTerm hProj hTy hLook
                                      hLens hArgs hImplEq
                                  have hReachC := hCalleeOut.1
                                  have hPostC := hCalleeOut.2
                                  cases outCallee with
                                  | abortTerminate _ => exact False.elim hPostC
                                  | returned rv memAfter =>
                                    have hBranch := hNorm hPostC.1 rv memAfter
                                      hPostC.2.1 hPostC.2.2
                                    cases hCont :
                                        evalCallExitStep body ⟨onRet, onUnwind⟩
                                          (.normal rv memAfter) with
                                    | stepCleanup _ _ =>
                                      rw [hCont] at hBranch
                                      exact False.elim hBranch
                                    | exitUnwind _ =>
                                      rw [hCont] at hBranch
                                      exact False.elim hBranch
                                    | exitTerminate _ =>
                                      rw [hCont] at hBranch
                                      exact False.elim hBranch
                                    | fault _ =>
                                      rw [hCont] at hBranch
                                      exact False.elim hBranch
                                    | stepNormal retBb rvC memC =>
                                      rw [hCont] at hBranch
                                      dsimp only at hBranch
                                      cases hWr :
                                          writePlace localsArgs memC dst.localId
                                            dstTy rvC with
                                      | error _ =>
                                        rw [hWr] at hBranch
                                        exact False.elim hBranch
                                      | ok wrRes =>
                                        rw [hWr] at hBranch
                                        dsimp only at hBranch
                                        have hWrEq :
                                            writePlace localsArgs memC
                                              dst.localId dstTy rvC =
                                              .ok (wrRes.1, wrRes.2) := hWr
                                        have hLiftRet :=
                                          stackReaches_in_outer_of_terminated
                                            (outer := [⟨callerLens, callees,
                                              body, frame.defId, localsArgs,
                                              dst.localId, dstTy, onRet,
                                              onUnwind⟩])
                                            hReachC
                                            ⟨callerLens, callees, body,
                                              frame.defId, localsArgs,
                                              dst.localId, dstTy, onRet,
                                              onUnwind⟩
                                            [] retBb rvC memC wrRes.1 wrRes.2
                                            rfl hCont hWrEq
                                        have hInner := ihFuel
                                          ⟨frame.defId, retBb, 0, wrRes.1,
                                            none, none, none⟩
                                          wrRes.2 cm onDone hBranch
                                        cases hInner with
                                        | intro outOuter hOuter =>
                                          refine ⟨outOuter, ?_, hOuter.2⟩
                                          have hMid := stackReaches_trans
                                            (.tail .refl hPush) hLiftRet
                                          exact stackReaches_trans hMid hOuter.1
                                  | unwound memAfter =>
                                    have hBranch := hUnw hPostC.1 memAfter
                                      hPostC.2.1 hPostC.2.2
                                    have hLiftUnw :=
                                      stackReaches_in_outer_of_terminated
                                        (outer := [⟨callerLens, callees, body,
                                          frame.defId, localsArgs, dst.localId,
                                          dstTy, onRet, onUnwind⟩])
                                        hReachC
                                    cases hCont :
                                        evalCallExitStep body ⟨onRet, onUnwind⟩
                                          (.unwind memAfter) with
                                    | stepNormal _ _ _ =>
                                      rw [hCont] at hBranch
                                      exact False.elim hBranch
                                    | fault _ =>
                                      rw [hCont] at hBranch
                                      exact False.elim hBranch
                                    | exitUnwind memC =>
                                      rw [hCont] at hBranch
                                      refine ⟨.unwound memC, ?_, hBranch⟩
                                      exact .tail
                                        (.tail
                                          (stackReaches_trans
                                            (.tail .refl hPush) hLiftUnw)
                                          (.unwind_pop_continue hCont))
                                        .unwind_root
                                    | exitTerminate memC =>
                                      rw [hCont] at hBranch
                                      refine ⟨.abortTerminate memC, ?_, hBranch⟩
                                      exact .tail
                                        (stackReaches_trans
                                          (.tail .refl hPush) hLiftUnw)
                                        (.unwind_pop_terminate hCont)
                                    | stepCleanup cleanupBb memC =>
                                      rw [hCont] at hBranch
                                      dsimp only at hBranch
                                      have hInner := ihFuel
                                        ⟨frame.defId, cleanupBb, 0, localsArgs,
                                          none, none, none⟩
                                        memC cm onDone hBranch
                                      cases hInner with
                                      | intro outOuter hOuter =>
                                        refine ⟨outOuter, ?_, hOuter.2⟩
                                        have hMid : StackReaches implOf
                                            (.running ⟨callerLens, callees,
                                              body, frame⟩ [] mem cm)
                                            (.running ⟨callerLens, callees,
                                              body, ⟨frame.defId, cleanupBb, 0,
                                                localsArgs, none, none, none⟩⟩
                                              [] memC cm) :=
                                          .tail
                                            (stackReaches_trans
                                              (.tail .refl hPush) hLiftUnw)
                                            (.unwind_pop_cleanup hCont)
                                        exact stackReaches_trans hMid hOuter.1

/-! ## 6. Stepping Combinators for `wpFrameOutcome` -/

/-- Steps `wpFrameOutcome` across an intra-frame statement `evalStep`. -/
theorem wpFrameOutcome_stmt_step (callerLens : ByteSubLens)
    (env : DefId → Option CallSpec) (body : Body) (fuel : Nat)
    (frame : FrameState) (cm : CallerMemory) (mem : MemoryState)
    (bb : BasicBlock) (st' : State) (onDone : FrameTermOut → Prop)
    (hBb : Trusted.MirSemantics.getElem? body.basicBlocks frame.blockIdx =
      some bb)
    (hNotEnd : Nat.beq frame.stmtIdx bb.statements.length = false)
    (hStep : evalStep (Anneal.MirWp.bodyProg body) 0 ⟨[frame], cm, mem⟩ =
      .step st')
    (hNext : wpFrameOutcome callerLens env body fuel st' onDone)
    (hSys : frame.sysrootOp? = none := by rfl) :
    wpFrameOutcome callerLens env body (fuel + 1) ⟨[frame], cm, mem⟩ onDone :=
  by
  unfold wpFrameOutcome
  dsimp only
  rw [hSys]
  dsimp only
  rw [hBb]
  dsimp only
  rw [if_prop_false hNotEnd, hStep]
  exact hNext

/-- Discharges `wpFrameOutcome` at a normal `.return_` terminator. -/
theorem wpFrameOutcome_return_step (callerLens : ByteSubLens)
    (env : DefId → Option CallSpec) (body : Body) (fuel : Nat)
    (frame : FrameState) (cm : CallerMemory) (mem : MemoryState)
    (bb : BasicBlock) (rv : Out) (onDone : FrameTermOut → Prop)
    (hBb : Trusted.MirSemantics.getElem? body.basicBlocks frame.blockIdx =
      some bb)
    (hAtEnd : Nat.beq frame.stmtIdx bb.statements.length = true)
    (hTerm : bb.terminator = .return_)
    (hStep : evalStep (Anneal.MirWp.bodyProg body) 0 ⟨[frame], cm, mem⟩ =
      .done (.returned rv))
    (hDone : onDone (.returned rv.ret mem))
    (hSys : frame.sysrootOp? = none := by rfl) :
    wpFrameOutcome callerLens env body (fuel + 1) ⟨[frame], cm, mem⟩ onDone :=
  by
  unfold wpFrameOutcome
  dsimp only
  rw [hSys]
  dsimp only
  rw [hBb]
  dsimp only
  rw [if_prop_true hAtEnd, hTerm]
  dsimp only
  rw [hStep]
  exact hDone

/-- Steps `wpFrameOutcome` across a sealed `.call` terminator. -/
theorem wpFrameOutcome_call_step (callerLens : ByteSubLens)
    (env : DefId → Option CallSpec) (body : Body) (fuel : Nat)
    (frame : FrameState) (cm : CallerMemory) (mem : MemoryState)
    (bb : BasicBlock) (callee : DefId) (args : List Operand) (dst : Place)
    (onRet : Option BasicBlockId) (onUnwind : UnwindAction)
    (dstTy : MirTy) (cSpec : CallSpec)
    (argVals : List Val) (localsArgs : List LocalSlot) (memArgs : MemoryState)
    (preBytes : List AllocByte) (onDone : FrameTermOut → Prop)
    (hBb : Trusted.MirSemantics.getElem? body.basicBlocks frame.blockIdx =
      some bb)
    (hAtEnd : Nat.beq frame.stmtIdx bb.statements.length = true)
    (hTerm : bb.terminator = .call callee args dst onRet onUnwind)
    (hProj : (!dst.projection.isEmpty) = false)
    (hDstTy : Trusted.MirSemantics.getElem? body.locals dst.localId =
      some dstTy)
    (hEnv : env callee = some cSpec)
    (hSub : subLensContained cSpec.mutLens callerLens = true)
    (hArgs : EvalCallArgs body.locals frame.locals mem args argVals localsArgs
      memArgs)
    (hGetPre : byteSubLensGet cSpec.mutLens memArgs = some preBytes)
    (hPre : cSpec.precondBool preBytes argVals = true)
    (hNormal : cSpec.canNormal = true →
      ∀ retVal memAfter,
        UpdatesOnly cSpec.mutLens memArgs memAfter →
        (∃ postBytes,
          byteSubLensGet cSpec.mutLens memAfter = some postBytes ∧
          cSpec.ensuresNormalBool preBytes retVal postBytes argVals = true) →
        match evalCallExitStep body ⟨onRet, onUnwind⟩
            (.normal retVal memAfter) with
        | .stepNormal retBb rv memC =>
          match writePlace localsArgs memC dst.localId dstTy rv with
          | .ok (locs', memW) =>
            wpFrameOutcome callerLens env body fuel
              { frames := [⟨frame.defId, retBb, 0, locs', none, none, none⟩],
                callerMem := cm, mem := memW } onDone
          | .error _ => False
        | .stepCleanup _ _ => False
        | .exitUnwind _ => False
        | .exitTerminate _ => False
        | .fault _ => False)
    (hUnwind : cSpec.canUnwind = true →
      ∀ memAfter,
        UpdatesOnly cSpec.mutLens memArgs memAfter →
        (∃ postPartialBytes,
          byteSubLensGet cSpec.mutLens memAfter = some postPartialBytes ∧
          cSpec.ensuresUnwindBool preBytes postPartialBytes argVals = true) →
        match evalCallExitStep body ⟨onRet, onUnwind⟩ (.unwind memAfter) with
        | .stepCleanup cleanupBb memC =>
          wpFrameOutcome callerLens env body fuel
            { frames := [⟨frame.defId, cleanupBb, 0, localsArgs,
                none, none, none⟩],
              callerMem := cm, mem := memC } onDone
        | .exitUnwind memC => onDone (.unwound memC)
        | .exitTerminate memC => onDone (.abortTerminate memC)
        | .stepNormal _ _ _ => False
        | .fault _ => False)
    (hSys : frame.sysrootOp? = none := by rfl) :
    wpFrameOutcome callerLens env body (fuel + 1) ⟨[frame], cm, mem⟩ onDone :=
  by
  unfold wpFrameOutcome
  dsimp only
  rw [hSys]
  dsimp only
  rw [hBb]
  dsimp only
  rw [if_prop_true hAtEnd, hTerm]
  dsimp only
  rw [if_prop_false hProj, hDstTy]
  dsimp only
  rw [hEnv]
  dsimp only
  exact ⟨hSub, argVals, localsArgs, memArgs, hArgs, preBytes, hGetPre, hPre,
    hNormal, hUnwind⟩

/-- Steps `wpFrameOutcome` across a failing `.assert` unwind terminator. -/
theorem wpFrameOutcome_assert_false_unwind_step (callerLens : ByteSubLens)
    (env : DefId → Option CallSpec) (body : Body) (fuel : Nat)
    (frame : FrameState) (cm : CallerMemory) (mem : MemoryState)
    (bb : BasicBlock) (cond : Operand) (expected : Bool) (msg : AssertKind)
    (target : BasicBlockId) (unwind : UnwindAction)
    (locals' : List LocalSlot) (mem' : MemoryState)
    (onDone : FrameTermOut → Prop)
    (hBb : Trusted.MirSemantics.getElem? body.basicBlocks frame.blockIdx =
      some bb)
    (hAtEnd : Nat.beq frame.stmtIdx bb.statements.length = true)
    (hTerm : bb.terminator = .assert cond expected msg target unwind)
    (hCond : evalPrimitiveOperand body.locals frame.locals mem cond =
      .ok (.bool (!expected), locals', mem'))
    (hNext : match evalCallExitStep body ⟨none, unwind⟩ (.unwind mem') with
      | .stepCleanup cleanupBb memC =>
        wpFrameOutcome callerLens env body fuel
          { frames := [⟨frame.defId, cleanupBb, 0, locals',
              none, none, none⟩],
            callerMem := cm, mem := memC } onDone
      | .exitUnwind memC => onDone (.unwound memC)
      | .exitTerminate memC => onDone (.abortTerminate memC)
      | .stepNormal _ _ _ => False
      | .fault _ => False)
    (hSys : frame.sysrootOp? = none := by rfl) :
    wpFrameOutcome callerLens env body (fuel + 1) ⟨[frame], cm, mem⟩ onDone :=
  by
  unfold wpFrameOutcome
  dsimp only
  rw [hSys]
  dsimp only
  rw [hBb]
  dsimp only
  rw [if_prop_true hAtEnd, hTerm]
  dsimp only
  rw [hCond]
  dsimp only
  have hNeq : ((!expected) == expected) = false := by
    cases expected <;> rfl
  rw [if_prop_false hNeq]
  exact hNext

/-- Steps `wpFrameOutcome` across a passing `.assert` terminator. -/
theorem wpFrameOutcome_assert_true_pass_step (callerLens : ByteSubLens)
    (env : DefId → Option CallSpec) (body : Body) (fuel : Nat)
    (frame : FrameState) (cm : CallerMemory) (mem : MemoryState)
    (bb : BasicBlock) (cond : Operand) (expected : Bool) (msg : AssertKind)
    (target : BasicBlockId) (unwind : UnwindAction)
    (locals' : List LocalSlot) (mem' : MemoryState)
    (onDone : FrameTermOut → Prop)
    (hBb : Trusted.MirSemantics.getElem? body.basicBlocks frame.blockIdx =
      some bb)
    (hAtEnd : Nat.beq frame.stmtIdx bb.statements.length = true)
    (hTerm : bb.terminator = .assert cond expected msg target unwind)
    (hCond : evalPrimitiveOperand body.locals frame.locals mem cond =
      .ok (.bool expected, locals', mem'))
    (hNext : wpFrameOutcome callerLens env body fuel
      { frames := [{ frame with
          blockIdx := target, stmtIdx := 0, locals := locals',
          sysrootOp? := none }],
        callerMem := cm, mem := mem' } onDone)
    (hSys : frame.sysrootOp? = none := by rfl) :
    wpFrameOutcome callerLens env body (fuel + 1) ⟨[frame], cm, mem⟩ onDone :=
  by
  unfold wpFrameOutcome
  dsimp only
  rw [hSys]
  dsimp only
  rw [hBb]
  dsimp only
  rw [if_prop_true hAtEnd, hTerm]
  dsimp only
  rw [hCond]
  dsimp only
  have hEq : (expected == expected) = true := by
    cases expected <;> rfl
  rw [if_prop_true hEq]
  exact hNext

/-- Discharges `wpFrameOutcome` at a `.unwindResume` terminator in a cleanup
block. -/
theorem wpFrameOutcome_unwindResume_step (callerLens : ByteSubLens)
    (env : DefId → Option CallSpec) (body : Body) (fuel : Nat)
    (frame : FrameState) (cm : CallerMemory) (mem : MemoryState)
    (bb : BasicBlock) (onDone : FrameTermOut → Prop)
    (hBb : Trusted.MirSemantics.getElem? body.basicBlocks frame.blockIdx =
      some bb)
    (hAtEnd : Nat.beq frame.stmtIdx bb.statements.length = true)
    (hTerm : bb.terminator = .unwindResume)
    (hClean : checkCleanupBlock body frame.blockIdx = true)
    (hDone : onDone (.unwound mem))
    (hSys : frame.sysrootOp? = none := by rfl) :
    wpFrameOutcome callerLens env body (fuel + 1) ⟨[frame], cm, mem⟩ onDone :=
  by
  unfold wpFrameOutcome
  dsimp only
  rw [hSys]
  dsimp only
  rw [hBb]
  dsimp only
  rw [if_prop_true hAtEnd, hTerm]
  dsimp only
  exact ⟨hClean, hDone⟩

/-- Inversion of `wpFrameOutcome` across an intra-frame statement step. -/
theorem wpFrameOutcome_stmt_step_inv (callerLens : ByteSubLens)
    (env : DefId → Option CallSpec) (body : Body) (fuel : Nat)
    (frame : FrameState) (cm : CallerMemory) (mem : MemoryState)
    (bb : BasicBlock) (st' : State) (onDone : FrameTermOut → Prop)
    (hBb : Trusted.MirSemantics.getElem? body.basicBlocks frame.blockIdx =
      some bb)
    (hNotEnd : Nat.beq frame.stmtIdx bb.statements.length = false)
    (hStep : evalStep (Anneal.MirWp.bodyProg body) 0 ⟨[frame], cm, mem⟩ =
      .step st')
    (hWp : wpFrameOutcome callerLens env body (fuel + 1) ⟨[frame], cm, mem⟩
      onDone)
    (hSys : frame.sysrootOp? = none := by rfl) :
    wpFrameOutcome callerLens env body fuel st' onDone := by
  unfold wpFrameOutcome at hWp
  dsimp only at hWp
  rw [hSys] at hWp
  dsimp only at hWp
  rw [hBb] at hWp
  dsimp only at hWp
  rw [if_prop_false hNotEnd, hStep] at hWp
  exact hWp

/-- Inversion of `wpFrameOutcome` across a failing `.assert` terminator. -/
theorem wpFrameOutcome_assert_false_unwind_inv (callerLens : ByteSubLens)
    (env : DefId → Option CallSpec) (body : Body) (fuel : Nat)
    (frame : FrameState) (cm : CallerMemory) (mem : MemoryState)
    (bb : BasicBlock) (cond : Operand) (expected : Bool) (msg : AssertKind)
    (target : BasicBlockId) (unwind : UnwindAction)
    (locals' : List LocalSlot) (mem' : MemoryState)
    (onDone : FrameTermOut → Prop)
    (hBb : Trusted.MirSemantics.getElem? body.basicBlocks frame.blockIdx =
      some bb)
    (hAtEnd : Nat.beq frame.stmtIdx bb.statements.length = true)
    (hTerm : bb.terminator = .assert cond expected msg target unwind)
    (hCond : evalPrimitiveOperand body.locals frame.locals mem cond =
      .ok (.bool (!expected), locals', mem'))
    (hWp : wpFrameOutcome callerLens env body (fuel + 1) ⟨[frame], cm, mem⟩
      onDone)
    (hSys : frame.sysrootOp? = none := by rfl) :
    match evalCallExitStep body ⟨none, unwind⟩ (.unwind mem') with
    | .stepCleanup cleanupBb memC =>
      wpFrameOutcome callerLens env body fuel
        { frames := [⟨frame.defId, cleanupBb, 0, locals', none, none, none⟩],
          callerMem := cm, mem := memC } onDone
    | .exitUnwind memC => onDone (.unwound memC)
    | .exitTerminate memC => onDone (.abortTerminate memC)
    | .stepNormal _ _ _ => False
    | .fault _ => False := by
  unfold wpFrameOutcome at hWp
  dsimp only at hWp
  rw [hSys] at hWp
  dsimp only at hWp
  rw [hBb] at hWp
  dsimp only at hWp
  rw [if_prop_true hAtEnd, hTerm] at hWp
  dsimp only at hWp
  rw [hCond] at hWp
  dsimp only at hWp
  have hNeq : ((!expected) == expected) = false := by
    cases expected <;> rfl
  rw [if_prop_false hNeq] at hWp
  exact hWp

end Anneal.CallStackUnwind

end
