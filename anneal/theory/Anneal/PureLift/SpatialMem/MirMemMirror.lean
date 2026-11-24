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
public import Init.Data.BitVec.BasicAux
public import Init.Data.List.Basic
public import Init.Data.UInt.BasicAux
public import Init.SimpLemmas
public import Init.Control.Except
public import Trusted
public import Trusted.MirAst
public import Trusted.MirModel
public import Trusted.MirSemantics
public import Anneal.MirWp
public import Anneal.PureLift.BlockCfg
public import Anneal.PureLift.MirBridge

public section

namespace Anneal.PureLift

open Trusted.MirAst Trusted.MirSemantics

/-!
# Computable `Trusted.MirSemantics.MemoryState` Mirrors (`MirMemMirror`)

Defines total, `noncomputable`-free mirrors (`execAllocateStack`,
`execDeallocateStack`, `execReadBytes`, `execWriteBytes`, `execWriteUninit`,
`execLayoutOfTy`, `execEncodeUInt`, `execDecodeUInt`, `execInitBytes?`,
`execEncodeVal`, `execDecodeVal`, `execLoadIndirect`, `execStoreIndirect`, and
`execDeinitIndirect`) together with unconditional equational equivalence
theorems against `Trusted.MirSemantics`.

Like `Anneal.PureLift.MirBridge`, this module builds its executable mirrors via
`natFold` (`Nat.recCompiled`) over `Anneal.MirWp` and `Trusted.*` without
importing `Anneal.MirTotal`, keeping the `PureLift` pure-lifting layer
dependency-DAG independent of the small-step `MirTotal` layer.
-/

/-! ## Constructive Arithmetic, BitVec, and List Lemmas -/

/-- Eliminates an impossible `false = true` hypothesis. -/
theorem boolFalseNeTrue (h : false = true) : False := Bool.noConfusion h

/-- Rewrites `if b then t else e` to `t` when `b = true`. -/
theorem ite_bool_true {α : Type} {b : Bool} {t e : α} (hb : b = true) :
    (if b then t else e) = t := by
  subst hb
  rfl

/-- Rewrites `if b then t else e` to `e` when `b = false`. -/
theorem ite_bool_false {α : Type} {b : Bool} {t e : α} (hb : b = false) :
    (if b then t else e) = e := by
  subst hb
  rfl

private theorem ite_prop_false {α : Type} {P : Prop} {d : Decidable P} (h : ¬ P) (t e : α) :
    @ite α P d t e = e := by
  cases d with
  | isTrue hp => exact False.elim (h hp)
  | isFalse _ => rfl

private theorem ite_prop_true {α : Type} {P : Prop} {d : Decidable P} (h : P) (t e : α) :
    @ite α P d t e = t := by
  cases d with
  | isTrue _ => rfl
  | isFalse hnp => exact False.elim (hnp h)

private theorem dite_pos_eq {α : Type} {P : Prop} {d : Decidable P}
    (hp : P) (t : P → α) (e : ¬ P → α) :
    @dite α P d t e = t hp := by
  cases d with
  | isFalse hn => exact False.elim (hn hp)
  | isTrue _ => rfl

private theorem dite_neg_eq {α : Type} {P : Prop} {d : Decidable P}
    (hnp : ¬ P) (t : P → α) (e : ¬ P → α) :
    @dite α P d t e = e hnp := by
  cases d with
  | isTrue hp => exact False.elim (hnp hp)
  | isFalse _ => rfl

/-- Soundness of `Nat.beq`: `Nat.beq a b = true` implies `a = b`. -/
theorem natEq_of_beq (a b : Nat) (h : Nat.beq a b = true) : a = b := by
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

/-- Reflexivity of `Nat.beq`. -/
theorem natBeq_refl (a : Nat) : Nat.beq a a = true := by
  induction a with
  | zero => rfl
  | succ _ ih => exact ih

/-- Completeness of `Nat.ble`: `a ≤ b` implies `Nat.ble a b = true`. -/
theorem natBle_of_le (a b : Nat) (h : a ≤ b) : Nat.ble a b = true := by
  revert b h
  induction a with
  | zero => intro _ _; rfl
  | succ a' ih =>
    intro b h
    cases b with
    | zero => exact False.elim (Nat.not_succ_le_zero a' h)
    | succ b' => exact ih b' (Nat.le_of_succ_le_succ h)

/-- Soundness of `Nat.ble`: `Nat.ble a b = true` implies `a ≤ b`. -/
theorem natLe_of_ble (a b : Nat) (h : Nat.ble a b = true) : a ≤ b := by
  revert b h
  induction a with
  | zero => intro b _; exact Nat.zero_le b
  | succ a' ih =>
    intro b h
    cases b with
    | zero => exact False.elim (boolFalseNeTrue h)
    | succ b' => exact Nat.succ_le_succ (ih b' h)

/-- Soundness of `Nat.blt`: `Nat.blt a b = true` implies `a < b`. -/
theorem natLt_of_blt (a b : Nat) (h : Nat.blt a b = true) : a < b :=
  natLe_of_ble (a + 1) b h

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

private theorem natSub_add_cancel_of_le {a b : Nat} (h : a ≤ b) : (b - a) + a = b := by
  revert b h
  induction a with
  | zero => intro b _; rfl
  | succ a' ih =>
    intro b h
    cases b with
    | zero => exact False.elim (Nat.not_succ_le_zero a' h)
    | succ b' =>
      rw [Nat.succ_sub_succ, Nat.add_succ]
      exact congrArg Nat.succ (ih (Nat.le_of_succ_le_succ h))

/-- `Nat.mod x y = x` whenever `x < y`. -/
theorem natMod_eq_of_lt {x y : Nat} (h : x < y) : Nat.mod x y = x := by
  cases x with
  | zero => rfl
  | succ x' =>
    change ite (y ≤ x' + 1) (Nat.modCore (x' + 1) y) (x' + 1) = x' + 1
    exact ite_prop_false (Nat.not_le_of_gt h) _ _

/-- `(UInt8.ofNat r).toNat = r` whenever `r < 256`. -/
theorem uint8_toNat_ofNat_lt {r : Nat} (hr : r < 256) :
    (UInt8.ofNat r).toNat = r := by
  change Nat.mod r 256 = r
  exact natMod_eq_of_lt hr

private theorem natModCoreGo_add_divGo {y : Nat} (hy : 0 < y) :
    ∀ (fuel x : Nat) (hf : x < fuel),
      Nat.modCore.go y hy fuel x hf + y * Nat.div.go y hy fuel x hf = x
  | 0, _, hf => False.elim (Nat.not_lt_zero _ hf)
  | fuel + 1, x, hf => by
    change
      dite (y ≤ x)
        (fun hle => Nat.modCore.go y hy fuel (x - y) (Nat.div_rec_fuel_lemma hy hle hf))
        (fun _ => x) +
      y * dite (y ≤ x)
        (fun hle => Nat.div.go y hy fuel (x - y) (Nat.div_rec_fuel_lemma hy hle hf) + 1)
        (fun _ => 0) = x
    cases Nat.decLe y x with
    | isFalse hNot =>
      rw [dite_neg_eq hNot, dite_neg_eq hNot, Nat.mul_zero, Nat.add_zero]
    | isTrue hLe =>
      rw [dite_pos_eq hLe, dite_pos_eq hLe, Nat.mul_succ, ← natAdd_assoc,
        natModCoreGo_add_divGo hy fuel (x - y) (Nat.div_rec_fuel_lemma hy hLe hf)]
      exact natSub_add_cancel_of_le hLe

private theorem natMod_add_div_pos (x y : Nat) (hy : 0 < y) :
    Nat.mod x y + y * Nat.div x y = x := by
  cases x with
  | zero =>
    have hDivZero : Nat.div 0 y = 0 := by
      unfold Nat.div
      rw [dite_pos_eq hy]
      change dite (y ≤ 0) _ _ = 0
      exact dite_neg_eq (Nat.not_le_of_gt hy) _ _
    rw [hDivZero, Nat.mul_zero]
    rfl
  | succ x' =>
    change
      ite (y ≤ x' + 1) (Nat.modCore (x' + 1) y) (x' + 1) + y * Nat.div (x' + 1) y = x' + 1
    have hDivUnfold :
        Nat.div (x' + 1) y =
          dite (y ≤ x' + 1)
            (fun hle =>
              Nat.div.go y hy (x' + 1) ((x' + 1) - y)
                (Nat.div_rec_fuel_lemma hy hle (Nat.lt_succ_self (x' + 1))) + 1)
            (fun _ => 0) := by
      unfold Nat.div
      rw [dite_pos_eq hy]
      rfl
    cases Nat.decLe y (x' + 1) with
    | isFalse hNot =>
      rw [ite_prop_false hNot, hDivUnfold, dite_neg_eq hNot, Nat.mul_zero, Nat.add_zero]
    | isTrue hLe =>
      rw [ite_prop_true hLe]
      have hModUnfold :
          Nat.modCore (x' + 1) y =
            Nat.modCore.go y hy (x' + 1) ((x' + 1) - y)
              (Nat.div_rec_fuel_lemma hy hLe (Nat.lt_succ_self (x' + 1))) := by
        unfold Nat.modCore
        rw [dite_pos_eq hy]
        change dite (y ≤ x' + 1) _ _ = _
        exact dite_pos_eq hLe _ _
      rw [hModUnfold, hDivUnfold, dite_pos_eq hLe, Nat.mul_succ, ← natAdd_assoc,
        natModCoreGo_add_divGo hy (x' + 1) ((x' + 1) - y)
          (Nat.div_rec_fuel_lemma hy hLe (Nat.lt_succ_self (x' + 1)))]
      exact natSub_add_cancel_of_le hLe

private theorem natDiv_lt_of_lt_mul_pos {x y b : Nat} (hy : 0 < y) (h : x < y * b) :
    Nat.div x y < b := by
  cases Nat.decLt (Nat.div x y) b with
  | isTrue hlt => exact hlt
  | isFalse hnot =>
    have hGe : b ≤ Nat.div x y := Nat.le_of_not_lt hnot
    have hMul : y * b ≤ y * Nat.div x y := Nat.mul_le_mul_left y hGe
    have hSum : y * Nat.div x y ≤ Nat.mod x y + y * Nat.div x y :=
      Nat.le_add_left (y * Nat.div x y) (Nat.mod x y)
    have hEq : Nat.mod x y + y * Nat.div x y = x := natMod_add_div_pos x y hy
    rw [hEq] at hSum
    exact False.elim (Nat.not_lt_of_ge (Nat.le_trans hMul hSum) h)

/-- Right-identity law `xs ++ [] = xs` proved constructively without `simp`. -/
theorem listAppend_nil_right {α : Type} (xs : List α) : xs ++ [] = xs := by
  induction xs with
  | nil => rfl
  | cons hd _ ih => exact congrArg (List.cons hd) ih

private theorem listAppend_assoc {α : Type} (xs ys zs : List α) :
    (xs ++ ys) ++ zs = xs ++ (ys ++ zs) := by
  induction xs with
  | nil => rfl
  | cons hd _ ih => exact congrArg (List.cons hd) ih

/-- Length of `xs ++ ys` proved constructively without `simp`. -/
theorem listLength_append {α : Type} (xs ys : List α) :
    (xs ++ ys).length = xs.length + ys.length := by
  induction xs with
  | nil => exact (natAdd_zero_left ys.length).symm
  | cons _ tl ih =>
    change (tl ++ ys).length + 1 = (tl.length + 1) + ys.length
    rw [ih, natAdd_succ_left]

/-- Length preservation under `List.map`. -/
theorem listLength_map {α β : Type} (f : α → β) (xs : List α) :
    (xs.map f).length = xs.length := by
  induction xs with
  | nil => rfl
  | cons _ _ ih => exact congrArg Nat.succ ih

private theorem listDrop_append_exact {α : Type} (p q : List α) :
    (p ++ q).drop p.length = q := by
  induction p with
  | nil => rfl
  | cons _ _ ih => exact ih

/-- Taking `p.length` elements from `p ++ q` recovers `p`. -/
theorem listTake_append_exact {α : Type} (p q : List α) :
    (p ++ q).take p.length = p := by
  induction p with
  | nil => rfl
  | cons hd _ ih => exact congrArg (List.cons hd) ih

/-- Dropping `n = p.length` elements from `p ++ q` recovers `q`. -/
theorem listDrop_append_of_len {α : Type} (p q : List α) (n : Nat) (h : p.length = n) :
    (p ++ q).drop n = q := by
  subst h
  exact listDrop_append_exact p q

private theorem listReverseAux_length {α : Type} :
    ∀ (xs acc : List α), (List.reverseAux xs acc).length = xs.length + acc.length
  | [], acc => (natAdd_zero_left acc.length).symm
  | x :: xs, acc => by
    change (List.reverseAux xs (x :: acc)).length = (xs.length + 1) + acc.length
    rw [listReverseAux_length xs (x :: acc)]
    change xs.length + (acc.length + 1) = (xs.length + 1) + acc.length
    rw [natAdd_succ_left, natAdd_assoc]

private theorem listReverse_length {α : Type} (xs : List α) : xs.reverse.length = xs.length :=
  listReverseAux_length xs []

private theorem listReverseAux_eq_append {α : Type} :
    ∀ (xs acc : List α), List.reverseAux xs acc = xs.reverse ++ acc
  | [], acc => rfl
  | x :: xs, acc => by
    change List.reverseAux xs (x :: acc) = (List.reverseAux xs [x]) ++ acc
    rw [listReverseAux_eq_append xs (x :: acc), listReverseAux_eq_append xs [x],
      listAppend_assoc]
    rfl

private theorem listReverse_append {α : Type} (xs ys : List α) :
    (xs ++ ys).reverse = ys.reverse ++ xs.reverse := by
  induction xs with
  | nil => exact (listAppend_nil_right ys.reverse).symm
  | cons x xs ih =>
    change List.reverseAux (xs ++ ys) [x] = ys.reverse ++ List.reverseAux xs [x]
    rw [listReverseAux_eq_append (xs ++ ys) [x], ih,
      listReverseAux_eq_append xs [x], listAppend_assoc]

private theorem listReverse_reverse {α : Type} (xs : List α) : xs.reverse.reverse = xs := by
  induction xs with
  | nil => rfl
  | cons x xs ih =>
    change (List.reverseAux xs [x]).reverse = x :: xs
    rw [listReverseAux_eq_append xs [x], listReverse_append, ih]
    rfl

/-! ## Computable Byte-Codec and Indirect-Memory Mirrors -/

/-- Computable mirror of `Trusted.MirSemantics.findAllocation`. -/
@[expose] def execFindAllocation (id : AllocId) (allocs : List Allocation) :
    Option Allocation :=
  allocs.foldr (fun a acc => if Nat.beq a.allocId id then some a else acc) none

/-- Computable mirror of `Trusted.MirSemantics.replaceAllocation`. -/
@[expose] def execReplaceAllocation (a' : Allocation) (allocs : List Allocation)
    : List Allocation :=
  (allocs.foldr
    (fun a (tailPair : List Allocation × List Allocation) =>
      if Nat.beq a.allocId a'.allocId then
        (a' :: tailPair.2, a :: tailPair.2)
      else
        (a :: tailPair.1, a :: tailPair.2))
    ([], [])).1

/-- Computable mirror of `Trusted.MirSemantics.MemoryState.reserveAllocId`. -/
@[expose] def execReserveAllocId (m : MemoryState) : MemoryState × AllocId :=
  ({ m with nextAllocId := m.nextAllocId + 1 }, m.nextAllocId)

/-- Computable mirror of `Trusted.MirSemantics.allocateStack`. -/
@[expose] def execAllocateStack (m : MemoryState) (layout : LayoutData) :
    MemoryState × MemPlace :=
  let (m1, id) := execReserveAllocId m
  let alloc : Allocation := {
    allocId := id
    alignLog2 := layout.alignLog2
    mutability := .mut
    bytes := List.replicate layout.size .uninit
    live := true
  }
  ({ m1 with allocations := m1.allocations ++ [alloc] }, ⟨id, 0⟩)

/-- Computable mirror of `Trusted.MirSemantics.deallocateStack`. -/
@[expose] def execDeallocateStack (m : MemoryState) (place : MemPlace) :
    Except FaultKind MemoryState :=
  if !Nat.beq place.offset 0 then
    .error .undefined
  else
    match execFindAllocation place.allocId m.allocations with
    | none => .error .undefined
    | some a =>
      if !a.live then
        .error .undefined
      else
        match a.mutability with
        | .shared => .error .undefined
        | .mut =>
          .ok { m with
            allocations :=
              execReplaceAllocation { a with live := false } m.allocations }

/-- Computable mirror of `Trusted.MirSemantics.isInBounds`. -/
abbrev execIsInBounds (a : Allocation) (offset size : Nat) : Bool :=
  Nat.ble (offset + size) a.bytes.length

/-- Computable mirror of `Trusted.MirSemantics.isAligned`. -/
abbrev execIsAligned (a : Allocation) (offset alignLog2 : Nat) : Bool :=
  Nat.ble alignLog2 a.alignLog2 &&
    Nat.beq (Nat.mod offset (Nat.pow 2 alignLog2)) 0

/-- Computable mirror of `Trusted.MirSemantics.readBytes`. -/
@[expose] def execReadBytes (m : MemoryState) (place : MemPlace)
    (size alignLog2 : Nat) : Except FaultKind (List AllocByte) :=
  match execFindAllocation place.allocId m.allocations with
  | none => .error .undefined
  | some a =>
    if Nat.beq size 0 then
      if !execIsAligned a place.offset alignLog2 then
        .error .undefined
      else
        .ok []
    else if !a.live || !execIsInBounds a place.offset size ||
        !execIsAligned a place.offset alignLog2 then
      .error .undefined
    else
      .ok ((a.bytes.drop place.offset).take size)

/-- Computable mirror of `Trusted.MirSemantics.writeBytes`. -/
@[expose] def execWriteBytes (m : MemoryState) (place : MemPlace)
    (alignLog2 : Nat) (bytes : List AllocByte) :
    Except FaultKind MemoryState :=
  match execFindAllocation place.allocId m.allocations with
  | none => .error .undefined
  | some a =>
    if Nat.beq bytes.length 0 then
      if !execIsAligned a place.offset alignLog2 then
        .error .undefined
      else
        .ok m
    else if !a.live || !execIsInBounds a place.offset bytes.length ||
        !execIsAligned a place.offset alignLog2 then
      .error .undefined
    else
      match a.mutability with
      | .shared => .error .undefined
      | .mut =>
        let bytes' := a.bytes.take place.offset ++ bytes ++
          a.bytes.drop (place.offset + bytes.length)
        .ok { m with
          allocations :=
            execReplaceAllocation { a with bytes := bytes' } m.allocations }

/-- Computable mirror of `Trusted.MirSemantics.writeUninit`. -/
@[expose] def execWriteUninit (m : MemoryState) (place : MemPlace)
    (size alignLog2 : Nat) : Except FaultKind MemoryState :=
  execWriteBytes m place alignLog2 (List.replicate size .uninit)

/-- Computable mirror of `Trusted.MirSemantics.profileTargetEndian` (`.big`). -/
@[expose] def execProfileTargetEndian : TargetEndian := .big

/-- Computable mirror of `Trusted.MirAst.IntWidth.byteSize`. -/
@[expose] def execByteSize : IntWidth → Nat
  | .i8 => 1
  | .i16 => 2
  | .i32 => 4
  | .i64 | .isize => 8
  | .i128 => 16

/-- Computable mirror of `Trusted.MirSemantics.intLayout`. -/
@[expose] def execIntLayout (w : IntWidth) : LayoutData :=
  match w with
  | .i8 => ⟨1, 0⟩
  | .i16 => ⟨2, 1⟩
  | .i32 => ⟨4, 2⟩
  | .i64 | .isize => ⟨8, 3⟩
  | .i128 => ⟨16, 4⟩

/-- Computable mirror of `Trusted.MirSemantics.overflowPairLayout`. -/
@[expose] def execOverflowPairLayout (w : IntWidth) : LayoutData :=
  ⟨2 * (execIntLayout w).size, (execIntLayout w).alignLog2⟩

/-- Computable mirror of `Trusted.MirSemantics.layoutOfTy`. -/
@[expose] def execLayoutOfTy : MirTy → Option LayoutData
  | .bool => some ⟨1, 0⟩
  | .int w _ => some (execIntLayout w)
  | .char => some ⟨4, 2⟩
  | .ordering => some ⟨1, 0⟩
  | .unit | .never => some ⟨0, 0⟩
  | .enum ety =>
    if !mirEnumAdmitted ety then
      none
    else
      match ety.tagRepr with
      | .zeroSized => some ⟨0, 0⟩
      | .scalar tagW _ => some (execIntLayout tagW)
  | .tuple fs =>
    match fs with
    | [t1, t2] =>
      match t1 with
      | .int w _ =>
        match t2 with
        | .bool => some (execOverflowPairLayout w)
        | .int _ _ | .unit | .never | .char | .ordering | .enum _ | .tuple _
        | .ref _ _ | .rawPtr _ _ | .slice _ | .array _ _ | .rangeTo _
        | .rangeFrom _ | .unsupported => none
      | .bool | .unit | .never | .char | .ordering | .enum _ | .tuple _
      | .ref _ _ | .rawPtr _ _ | .slice _ | .array _ _ | .rangeTo _
      | .rangeFrom _ | .unsupported => none
    | [] | [_] | _ :: _ :: _ :: _ => none
  | .ref _ _ | .rawPtr _ _ | .slice _ | .array _ _ | .rangeTo _ | .rangeFrom _
  | .unsupported => none

/-- Computable mirror of `Trusted.MirSemantics.leBytesOfNat`. -/
@[expose] def execLeBytesOfNat (n value : Nat) : List UInt8 :=
  (natFold
    (fun (_ : Nat) => ([] : List UInt8))
    (fun _ ih v => UInt8.ofNat (Nat.mod v 256) :: ih (Nat.div v 256))
    n)
    value

/-- Computable mirror of `Trusted.MirSemantics.encodeUInt`. -/
@[expose] def execEncodeUInt (endian : TargetEndian) (n value : Nat) : List
    UInt8 :=
  match endian with
  | .little => execLeBytesOfNat n value
  | .big => (execLeBytesOfNat n value).reverse

/-- Computable mirror of `Trusted.MirSemantics.natOfLeBytes`. -/
@[expose] def execNatOfLeBytes (bytes : List UInt8) : Nat :=
  bytes.foldr (fun b ih => b.toNat + 256 * ih) 0

/-- Computable mirror of `Trusted.MirSemantics.decodeUInt`. -/
@[expose] def execDecodeUInt (endian : TargetEndian) (bytes : List UInt8) : Nat
    :=
  match endian with
  | .little => execNatOfLeBytes bytes
  | .big => execNatOfLeBytes bytes.reverse

/-- Computable mirror of `Trusted.MirSemantics.initBytes?`. -/
@[expose] def execInitBytes? (bytes : List AllocByte) : Option (List UInt8) :=
  bytes.foldr
    (fun ab ih =>
      match ab with
      | .uninit => none
      | .init b _ =>
        match ih with
        | some bs => some (b :: bs)
        | none => none)
    (some [])

/-- Computable mirror of `Trusted.MirSemantics.encodeVal`. -/
@[expose] def execEncodeVal (endian : TargetEndian) (ty : MirTy) (v : Val) :
    Except FaultKind (List AllocByte) :=
  if !mirCheckVal v ty then
    .error .unsupported
  else
    match ty with
    | .int w _ =>
      match v with
      | .scalar sv =>
        .ok ((execEncodeUInt endian (execByteSize w) sv.bits.toNat).map
          (fun b => AllocByte.init b none))
      | .ptr _ | .bool _ | .char _ | .ordering _ | .unit | .enumVal _ _ | .tuple _
      | .array _ | .slicePtr _ _ | .rangeTo _ | .rangeFrom _ | .bytes _ =>
        .error .unsupported
    | .bool =>
      match v with
      | .bool b => .ok [AllocByte.init (if b then 1 else 0) none]
      | .scalar _ | .ptr _ | .char _ | .ordering _ | .unit | .enumVal _ _ | .tuple _
      | .array _ | .slicePtr _ _ | .rangeTo _ | .rangeFrom _ | .bytes _ =>
        .error .unsupported
    | .char =>
      match v with
      | .char c => .ok ((execEncodeUInt endian 4 c.toNat).map (fun b => AllocByte.init b none))
      | .scalar _ | .ptr _ | .bool _ | .ordering _ | .unit | .enumVal _ _ | .tuple _
      | .array _ | .slicePtr _ _ | .rangeTo _ | .rangeFrom _ | .bytes _ =>
        .error .unsupported
    | .ordering =>
      match v with
      | .ordering ord =>
        .ok ((execEncodeUInt endian 1 (mirOrderingTagBits ord)).map
          (fun b => AllocByte.init b none))
      | .scalar _ | .ptr _ | .bool _ | .char _ | .unit | .enumVal _ _ | .tuple _
      | .array _ | .slicePtr _ _ | .rangeTo _ | .rangeFrom _ | .bytes _ =>
        .error .unsupported
    | .unit =>
      match v with
      | .unit => .ok []
      | .scalar _ | .ptr _ | .bool _ | .char _ | .ordering _ | .enumVal _ _ | .tuple _
      | .array _ | .slicePtr _ _ | .rangeTo _ | .rangeFrom _ | .bytes _ =>
        .error .unsupported
    | .enum ety =>
      match v with
      | .enumVal _ variant =>
        match ety.tagRepr with
        | .zeroSized => .ok []
        | .scalar tagW _ =>
          match mirListGet? ety.discriminants variant with
          | some disc =>
            .ok ((execEncodeUInt endian (execByteSize tagW) disc).map
              (fun b => AllocByte.init b none))
          | none => .error .unsupported
      | .scalar _ | .ptr _ | .bool _ | .char _ | .ordering _ | .unit | .tuple _
      | .array _ | .slicePtr _ _ | .rangeTo _ | .rangeFrom _ | .bytes _ =>
        .error .unsupported
    | .tuple fs =>
      match fs with
      | [t1, t2] =>
        match t1 with
        | .int w _ =>
          match t2 with
          | .bool =>
            match v with
            | .tuple vfs =>
              match vfs with
              | [v1, v2] =>
                match v1 with
                | .scalar sv =>
                  match v2 with
                  | .bool b =>
                    .ok ((execEncodeUInt endian (execByteSize w) sv.bits.toNat).map
                        (fun byte => AllocByte.init byte none) ++
                      [AllocByte.init (if b then 1 else 0) none] ++
                      List.replicate (execByteSize w - 1) AllocByte.uninit)
                  | .scalar _ | .ptr _ | .char _ | .ordering _ | .unit | .enumVal _ _
                  | .tuple _ | .array _ | .slicePtr _ _ | .rangeTo _ | .rangeFrom _
                  | .bytes _ =>
                    .error .unsupported
                | .ptr _ | .bool _ | .char _ | .ordering _ | .unit | .enumVal _ _ | .tuple _
                | .array _ | .slicePtr _ _ | .rangeTo _ | .rangeFrom _ | .bytes _ =>
                  .error .unsupported
              | [] | [_] | _ :: _ :: _ :: _ => .error .unsupported
            | .scalar _ | .ptr _ | .bool _ | .char _ | .ordering _ | .unit | .enumVal _ _
            | .array _ | .slicePtr _ _ | .rangeTo _ | .rangeFrom _ | .bytes _ =>
              .error .unsupported
          | .int _ _ | .unit | .never | .char | .ordering | .enum _ | .tuple _
          | .ref _ _ | .rawPtr _ _ | .slice _ | .array _ _ | .rangeTo _
          | .rangeFrom _ | .unsupported => .error .unsupported
        | .bool | .unit | .never | .char | .ordering | .enum _ | .tuple _
        | .ref _ _ | .rawPtr _ _ | .slice _ | .array _ _ | .rangeTo _
        | .rangeFrom _ | .unsupported => .error .unsupported
      | [] | [_] | _ :: _ :: _ :: _ => .error .unsupported
    | .never | .ref _ _ | .rawPtr _ _ | .slice _ | .array _ _ | .rangeTo _
    | .rangeFrom _ | .unsupported => .error .unsupported

/-- Non-overflow-pair layout arm of `execDecodeVal`. -/
@[expose] def execDecodeValFallback (endian : TargetEndian) (ty : MirTy)
    (bytes : List AllocByte) : Except FaultKind (Option Val) :=
  match execLayoutOfTy ty with
  | none => .error .unsupported
  | some layout =>
    if !Nat.beq bytes.length layout.size then
      .error .unsupported
    else if Nat.beq layout.size 0 then
      match mirEvalConstLit ty .zeroSized with
      | .ok v => .ok (some v)
      | .error k => .error k
    else
      match execInitBytes? bytes with
      | none => .ok none
      | some raw =>
        match mirEvalConstLit ty
            (.scalar (BitVec.ofNat 128 (execDecodeUInt endian raw))) with
        | .ok v => .ok (some v)
        | .error k => .error k

/-- Computable mirror of `Trusted.MirSemantics.decodeVal`. -/
@[expose] def execDecodeVal (endian : TargetEndian) (ty : MirTy)
    (bytes : List AllocByte) : Except FaultKind (Option Val) :=
  match ty with
  | .never => .ok none
  | .tuple fs =>
    match fs with
    | [t1, t2] =>
      match t1 with
      | .int w s =>
        match t2 with
        | .bool =>
          if !Nat.beq bytes.length (execOverflowPairLayout w).size then
            .error .unsupported
          else
            match execInitBytes? (bytes.take (execByteSize w)) with
            | none => .ok none
            | some intRaw =>
              match execInitBytes? ((bytes.drop (execByteSize w)).take 1) with
              | none => .ok none
              | some boolRaw =>
                match mirEvalConstLit (.int w s)
                    (.scalar (BitVec.ofNat 128 (execDecodeUInt endian intRaw))) with
                | .error k => .error k
                | .ok intVal =>
                  match mirEvalConstLit .bool
                      (.scalar (BitVec.ofNat 128 (execDecodeUInt endian boolRaw))) with
                  | .error k => .error k
                  | .ok boolVal => .ok (some (.tuple [intVal, boolVal]))
        | .int _ _ | .unit | .never | .char | .ordering | .enum _ | .tuple _
        | .ref _ _ | .rawPtr _ _ | .slice _ | .array _ _ | .rangeTo _
        | .rangeFrom _ | .unsupported =>
          execDecodeValFallback endian ty bytes
      | .bool | .unit | .never | .char | .ordering | .enum _ | .tuple _
      | .ref _ _ | .rawPtr _ _ | .slice _ | .array _ _ | .rangeTo _
      | .rangeFrom _ | .unsupported =>
        execDecodeValFallback endian ty bytes
    | [] | [_] | _ :: _ :: _ :: _ => execDecodeValFallback endian ty bytes
  | .bool | .int _ _ | .unit | .char | .ordering | .enum _
  | .ref _ _ | .rawPtr _ _ | .slice _ | .array _ _ | .rangeTo _
  | .rangeFrom _ | .unsupported =>
    execDecodeValFallback endian ty bytes

/-- Computable mirror of `Trusted.MirSemantics.loadIndirect`. -/
@[expose] def execLoadIndirect (mem : MemoryState) (ty : MirTy)
    (place : MemPlace) : Except FaultKind (Option Val) :=
  match execLayoutOfTy ty with
  | none => .error .unsupported
  | some layout =>
    match execReadBytes mem place layout.size layout.alignLog2 with
    | .error k => .error k
    | .ok bytes => execDecodeVal execProfileTargetEndian ty bytes

/-- Computable mirror of `Trusted.MirSemantics.storeIndirect`. -/
@[expose] def execStoreIndirect (mem : MemoryState) (ty : MirTy)
    (place : MemPlace) (v : Val) : Except FaultKind MemoryState :=
  match execLayoutOfTy ty with
  | none => .error .unsupported
  | some layout =>
    match execEncodeVal execProfileTargetEndian ty v with
    | .error k => .error k
    | .ok bytes => execWriteBytes mem place layout.alignLog2 bytes

/-- Computable mirror of `Trusted.MirSemantics.deinitIndirect`. -/
@[expose] def execDeinitIndirect (mem : MemoryState) (ty : MirTy)
    (place : MemPlace) : Except FaultKind MemoryState :=
  match execLayoutOfTy ty with
  | none => .error .unsupported
  | some layout => execWriteUninit mem place layout.size layout.alignLog2

/-- Computable mirror of `Trusted.MirSemantics.evalOperandToSlot` specialized to
`mirIsPrimitiveReadableTy`. -/
@[expose] def execEvalPrimitiveOperandToSlot (bodyLocals : List MirTy)
    (locals : List LocalSlot) (mem : MemoryState) :
    Operand →
      Except FaultKind (MirTy × Option Val × List LocalSlot × MemoryState)
  | .copy place =>
    match mirListGet? bodyLocals place.localId,
        mirListGet? locals place.localId with
    | some _, some .dead => .error .undefined
    | some ty, some (.immediate optVal) =>
      if !place.projection.isEmpty then .error .unsupported
      else .ok (ty, optVal, locals, mem)
    | some ty, some (.indirect mplace) =>
      if !place.projection.isEmpty then .error .unsupported
      else if !mirIsPrimitiveReadableTy ty then .error .unsupported
      else
        match execLoadIndirect mem ty mplace with
        | .ok optVal => .ok (ty, optVal, locals, mem)
        | .error k => .error k
    | _, _ => .error .unsupported
  | .move place =>
    match mirListGet? bodyLocals place.localId,
        mirListGet? locals place.localId with
    | some _, some .dead => .error .undefined
    | some ty, some (.immediate optVal) =>
      if !place.projection.isEmpty then .error .unsupported
      else
        match mirListSet? locals place.localId (mirLiveUninitSlot ty) with
        | some locals' => .ok (ty, optVal, locals', mem)
        | none => .error .unsupported
    | some ty, some (.indirect mplace) =>
      if !place.projection.isEmpty then .error .unsupported
      else if !mirIsPrimitiveReadableTy ty then .error .unsupported
      else
        match execLoadIndirect mem ty mplace with
        | .error k => .error k
        | .ok optVal =>
          match execDeinitIndirect mem ty mplace with
          | .ok mem' => .ok (ty, optVal, locals, mem')
          | .error k => .error k
    | _, _ => .error .unsupported
  | .constant c =>
    match mirEvalConstLit c.ty c.lit with
    | .ok v => .ok (c.ty, some v, locals, mem)
    | .error k => .error k

/-- Computable mirror of `Trusted.MirSemantics.evalPrimitiveOperand`. -/
@[expose] def execEvalPrimitiveOperand (bodyLocals : List MirTy)
    (locals : List LocalSlot) (mem : MemoryState) (opnd : Operand) :
    Except FaultKind (Val × List LocalSlot × MemoryState) :=
  match execEvalPrimitiveOperandToSlot bodyLocals locals mem opnd with
  | .error k => .error k
  | .ok (ty, optVal, locals', mem') =>
    if !mirIsPrimitiveReadableTy ty then .error .unsupported
    else
      match optVal with
      | some v => .ok (v, locals', mem')
      | none => .error .undefined

/-! ### Equational Equivalence Against `Trusted.MirSemantics` -/

/-- Agreement between `execFindAllocation` and `findAllocation`. -/
theorem execFindAllocation_eq (id : AllocId) (allocs : List Allocation) :
    execFindAllocation id allocs = findAllocation id allocs := by
  induction allocs with
  | nil => rfl
  | cons a rest ih =>
    dsimp only [execFindAllocation, findAllocation, List.foldr]
    rw [← ih]
    rfl

private theorem execReplaceAllocation_pair_snd (a' : Allocation) (allocs : List Allocation) :
    (allocs.foldr
      (fun a (tailPair : List Allocation × List Allocation) =>
        if Nat.beq a.allocId a'.allocId then
          (a' :: tailPair.2, a :: tailPair.2)
        else
          (a :: tailPair.1, a :: tailPair.2))
      ([], [])).2 = allocs := by
  induction allocs with
  | nil => rfl
  | cons a rest ih =>
    dsimp only [List.foldr]
    cases Nat.beq a.allocId a'.allocId with
    | true =>
      rw [ite_bool_true rfl]
      exact congrArg (List.cons a) ih
    | false =>
      rw [ite_bool_false rfl]
      exact congrArg (List.cons a) ih

/-- Agreement between `execReplaceAllocation` and `replaceAllocation`. -/
theorem execReplaceAllocation_eq (a' : Allocation) (allocs : List Allocation) :
    execReplaceAllocation a' allocs = replaceAllocation a' allocs := by
  induction allocs with
  | nil => rfl
  | cons a rest ih =>
    dsimp only [execReplaceAllocation, replaceAllocation, List.foldr]
    cases Nat.beq a.allocId a'.allocId with
    | true =>
      rw [ite_bool_true rfl]
      exact congrArg (List.cons a') (execReplaceAllocation_pair_snd a' rest)
    | false =>
      rw [ite_bool_false rfl]
      exact congrArg (List.cons a) ih

/-- Unconditional agreement between `execAllocateStack` and `allocateStack`. -/
theorem execAllocateStack_eq (m : MemoryState) (layout : LayoutData) :
    execAllocateStack m layout = allocateStack m layout := rfl

/-- Agreement between `execDeallocateStack` and `deallocateStack`. -/
theorem execDeallocateStack_eq (m : MemoryState) (place : MemPlace) :
    execDeallocateStack m place = deallocateStack m place := by
  unfold execDeallocateStack deallocateStack
  rw [execFindAllocation_eq]
  cases Nat.beq place.offset 0 with
  | false => rfl
  | true =>
    cases findAllocation place.allocId m.allocations with
    | none => rfl
    | some a =>
      dsimp only
      cases a.live with
      | false => rfl
      | true =>
        cases a.mutability <;>
          first
          | rfl
          | (dsimp only
             rw [execReplaceAllocation_eq])

/-- Unconditional agreement between `execReadBytes` and `readBytes`. -/
theorem execReadBytes_eq (m : MemoryState) (place : MemPlace) (size alignLog2 : Nat) :
    execReadBytes m place size alignLog2 = readBytes m place size alignLog2 := by
  unfold execReadBytes readBytes
  rw [execFindAllocation_eq]
  cases findAllocation place.allocId m.allocations <;> rfl

/-- Unconditional agreement between `execWriteBytes` and `writeBytes`. -/
theorem execWriteBytes_eq (m : MemoryState) (place : MemPlace)
    (alignLog2 : Nat) (bytes : List AllocByte) :
    execWriteBytes m place alignLog2 bytes = writeBytes m place alignLog2 bytes := by
  unfold execWriteBytes writeBytes
  rw [execFindAllocation_eq]
  cases findAllocation place.allocId m.allocations with
  | none => rfl
  | some a =>
    let bytes' := a.bytes.take place.offset ++ bytes ++
      a.bytes.drop (place.offset + bytes.length)
    change
      (if Nat.beq bytes.length 0 then
        if !isAligned a place.offset alignLog2 then
          Except.error FaultKind.undefined
        else
          Except.ok m
      else if !a.live || !isInBounds a place.offset bytes.length ||
          !isAligned a place.offset alignLog2 then
        Except.error FaultKind.undefined
      else
        match a.mutability with
        | .shared => Except.error FaultKind.undefined
        | .mut =>
          Except.ok { m with
            allocations := execReplaceAllocation { a with bytes := bytes' } m.allocations }) =
      (if Nat.beq bytes.length 0 then
        if !isAligned a place.offset alignLog2 then
          Except.error FaultKind.undefined
        else
          Except.ok m
      else if !a.live || !isInBounds a place.offset bytes.length ||
          !isAligned a place.offset alignLog2 then
        Except.error FaultKind.undefined
      else
        match a.mutability with
        | .shared => Except.error FaultKind.undefined
        | .mut =>
          Except.ok { m with
            allocations := replaceAllocation { a with bytes := bytes' } m.allocations })
    cases a.mutability <;>
      first | rfl | (dsimp only; rw [execReplaceAllocation_eq]) | rw [execReplaceAllocation_eq]

/-- Unconditional agreement between `execWriteUninit` and `writeUninit`. -/
theorem execWriteUninit_eq (m : MemoryState) (place : MemPlace) (size alignLog2 : Nat) :
    execWriteUninit m place size alignLog2 = writeUninit m place size alignLog2 :=
  execWriteBytes_eq m place alignLog2 (List.replicate size .uninit)

/-- Unconditional agreement between `execByteSize` and `IntWidth.byteSize`. -/
theorem execByteSize_eq (w : IntWidth) : execByteSize w = w.byteSize := by
  cases w <;> rfl

/-- Unconditional agreement between `execIntLayout` and `intLayout`. -/
theorem execIntLayout_eq (w : IntWidth) : execIntLayout w = intLayout w := by
  cases w <;> rfl

/-- Agreement between `execOverflowPairLayout` and `overflowPairLayout`. -/
theorem execOverflowPairLayout_eq (w : IntWidth) :
    execOverflowPairLayout w = overflowPairLayout w := by
  dsimp only [execOverflowPairLayout, overflowPairLayout]
  rw [execIntLayout_eq w]

/-- Unconditional agreement between `execLayoutOfTy` and `layoutOfTy`. -/
theorem execLayoutOfTy_eq (ty : MirTy) : execLayoutOfTy ty = layoutOfTy ty := by
  cases ty with
  | bool | unit | never | char | ordering | ref _ _ | rawPtr _ _ | slice _
  | array _ _ | rangeTo _ | rangeFrom _ | unsupported => rfl
  | int w _ =>
    dsimp only [execLayoutOfTy, layoutOfTy]
    rw [execIntLayout_eq w]
  | enum ety =>
    dsimp only [execLayoutOfTy, layoutOfTy]
    rw [mirEnumAdmitted_eq ety]
    cases enumAdmitted ety with
    | false => rfl
    | true =>
      cases ety.tagRepr with
      | zeroSized => rfl
      | scalar tagW _ =>
        dsimp only
        rw [execIntLayout_eq tagW]
  | tuple fs =>
    cases fs with
    | nil => rfl
    | cons t1 r =>
      cases t1 with
      | int w _ =>
        cases r with
        | nil => rfl
        | cons t2 r' =>
          cases t2 with
          | bool =>
            cases r' with
            | nil => exact congrArg some (execOverflowPairLayout_eq w)
            | cons _ _ => rfl
          | int _ _ | unit | never | char | ordering | enum _ | tuple _
          | ref _ _ | rawPtr _ _ | slice _ | array _ _ | rangeTo _ | rangeFrom _
          | unsupported => cases r' <;> rfl
      | bool | unit | never | char | ordering | enum _ | tuple _
      | ref _ _ | rawPtr _ _ | slice _ | array _ _ | rangeTo _ | rangeFrom _
      | unsupported =>
        cases r with
        | nil => rfl
        | cons _ r' => cases r' <;> rfl

/-- Unconditional agreement between `execLeBytesOfNat` and `leBytesOfNat`. -/
theorem execLeBytesOfNat_eq (n value : Nat) :
    execLeBytesOfNat n value = leBytesOfNat n value := by
  revert value
  induction n with
  | zero => intro _; rfl
  | succ n' ih =>
    intro value
    change UInt8.ofNat (Nat.mod value 256) :: execLeBytesOfNat n' (Nat.div value 256) =
      UInt8.ofNat (Nat.mod value 256) :: leBytesOfNat n' (Nat.div value 256)
    rw [ih (Nat.div value 256)]

/-- Unconditional agreement between `execEncodeUInt` and `encodeUInt`. -/
theorem execEncodeUInt_eq (endian : TargetEndian) (n value : Nat) :
    execEncodeUInt endian n value = encodeUInt endian n value := by
  cases endian with
  | little => exact execLeBytesOfNat_eq n value
  | big => exact congrArg List.reverse (execLeBytesOfNat_eq n value)

/-- Unconditional agreement between `execNatOfLeBytes` and `natOfLeBytes`. -/
theorem execNatOfLeBytes_eq (bytes : List UInt8) :
    execNatOfLeBytes bytes = natOfLeBytes bytes := by
  induction bytes with
  | nil => rfl
  | cons b rest ih =>
    dsimp only [execNatOfLeBytes, List.foldr, natOfLeBytes]
    rw [← ih]
    rfl

/-- Unconditional agreement between `execDecodeUInt` and `decodeUInt`. -/
theorem execDecodeUInt_eq (endian : TargetEndian) (bytes : List UInt8) :
    execDecodeUInt endian bytes = decodeUInt endian bytes := by
  cases endian with
  | little => exact execNatOfLeBytes_eq bytes
  | big => exact execNatOfLeBytes_eq bytes.reverse

/-- Unconditional agreement between `execInitBytes?` and `initBytes?`. -/
theorem execInitBytes?_eq (bytes : List AllocByte) :
    execInitBytes? bytes = initBytes? bytes := by
  induction bytes with
  | nil => rfl
  | cons ab rest ih =>
    cases ab with
    | uninit => rfl
    | init b prov =>
      dsimp only [execInitBytes?, List.foldr, initBytes?]
      rw [← ih]
      rfl

/-- Unconditional agreement between `execEncodeVal` and `encodeVal`. -/
theorem execEncodeVal_eq (endian : TargetEndian) (ty : MirTy) (v : Val) :
    execEncodeVal endian ty v = encodeVal endian ty v := by
  unfold execEncodeVal encodeVal
  rw [mirCheckVal_eq v ty]
  cases !checkVal v ty with
  | true => rfl
  | false =>
    cases ty with
    | int w _ =>
      cases v with
      | scalar sv =>
        dsimp only
        rw [execByteSize_eq w, execEncodeUInt_eq endian w.byteSize sv.bits.toNat]
      | ptr _ | bool _ | char _ | ordering _ | unit | enumVal _ _ | tuple _
      | array _ | slicePtr _ _ | rangeTo _ | rangeFrom _ | bytes _ => rfl
    | bool =>
      cases v <;> rfl
    | char =>
      cases v with
      | char c =>
        dsimp only
        rw [execEncodeUInt_eq endian 4 c.toNat]
      | scalar _ | ptr _ | bool _ | ordering _ | unit | enumVal _ _ | tuple _
      | array _ | slicePtr _ _ | rangeTo _ | rangeFrom _ | bytes _ => rfl
    | ordering =>
      cases v with
      | ordering ord =>
        dsimp only
        rw [mirOrderingTagBits_eq ord,
          execEncodeUInt_eq endian 1 (orderingTagBits ord)]
      | scalar _ | ptr _ | bool _ | char _ | unit | enumVal _ _ | tuple _
      | array _ | slicePtr _ _ | rangeTo _ | rangeFrom _ | bytes _ => rfl
    | unit =>
      cases v <;> rfl
    | enum ety =>
      cases v with
      | enumVal ety2 variant =>
        cases hTag : ety.tagRepr with
        | zeroSized =>
          dsimp only
          rw [hTag]
        | scalar tagW tagS =>
          dsimp only
          rw [hTag]
          dsimp only
          rw [mirListGet?_eq_getElem? ety.discriminants variant]
          cases Trusted.MirSemantics.getElem? ety.discriminants variant with
          | none => rfl
          | some disc =>
            dsimp only
            rw [execByteSize_eq tagW, execEncodeUInt_eq endian tagW.byteSize disc]
      | scalar _ | ptr _ | bool _ | char _ | ordering _ | unit | tuple _
      | array _ | slicePtr _ _ | rangeTo _ | rangeFrom _ | bytes _ => rfl
    | tuple fs =>
      cases fs with
      | nil => cases v <;> rfl
      | cons t1 r =>
        cases t1 with
        | int w _ =>
          cases r with
          | nil => cases v <;> rfl
          | cons t2 r' =>
            cases t2 with
            | bool =>
              cases r' with
              | nil =>
                cases v with
                | tuple vfs =>
                  cases vfs with
                  | nil => rfl
                  | cons v1 vr =>
                    cases v1 with
                    | scalar sv =>
                      cases vr with
                      | nil => rfl
                      | cons v2 vr' =>
                        cases v2 with
                        | bool b =>
                          cases vr' with
                          | nil =>
                            dsimp only
                            rw [execByteSize_eq w, execEncodeUInt_eq endian w.byteSize sv.bits.toNat]
                          | cons _ _ => rfl
                        | scalar _ | ptr _ | char _ | ordering _ | unit | enumVal _ _
                        | tuple _ | array _ | slicePtr _ _ | rangeTo _
                        | rangeFrom _ | bytes _ =>
                          cases vr' <;> rfl
                    | ptr _ | bool _ | char _ | ordering _ | unit | enumVal _ _ | tuple _
                    | array _ | slicePtr _ _ | rangeTo _ | rangeFrom _ | bytes _ =>
                      cases vr with
                      | nil => rfl
                      | cons _ vr' => cases vr' <;> rfl
                | scalar _ | ptr _ | bool _ | char _ | ordering _ | unit | enumVal _ _
                | array _ | slicePtr _ _ | rangeTo _ | rangeFrom _ | bytes _ => rfl
              | cons _ _ => cases v <;> rfl
            | int _ _ | unit | never | char | ordering | enum _ | tuple _
            | ref _ _ | rawPtr _ _ | slice _ | array _ _ | rangeTo _ | rangeFrom _
            | unsupported => cases r' <;> cases v <;> rfl
        | bool | unit | never | char | ordering | enum _ | tuple _
        | ref _ _ | rawPtr _ _ | slice _ | array _ _ | rangeTo _ | rangeFrom _
        | unsupported =>
          cases r with
          | nil => cases v <;> rfl
          | cons _ r' => cases r' <;> cases v <;> rfl
    | never | ref _ _ | rawPtr _ _ | slice _ | array _ _ | rangeTo _ | rangeFrom _
    | unsupported =>
      cases v <;> rfl

private theorem execDecodeVal_layout_arm_eq (endian : TargetEndian) (ty : MirTy)
    (bytes : List AllocByte) :
    execDecodeValFallback endian ty bytes =
    (match layoutOfTy ty with
     | none => Except.error FaultKind.unsupported
     | some layout =>
       if !Nat.beq bytes.length layout.size then Except.error FaultKind.unsupported
       else if Nat.beq layout.size 0 then
         match evalConstLit ty .zeroSized with
         | Except.ok v => Except.ok (some v)
         | Except.error k => Except.error k
       else
         match initBytes? bytes with
         | none => Except.ok none
         | some raw =>
           match evalConstLit ty
               (.scalar (BitVec.ofNat 128 (decodeUInt endian raw))) with
           | Except.ok v => Except.ok (some v)
           | Except.error k => Except.error k) := by
  dsimp only [execDecodeValFallback]
  rw [execLayoutOfTy_eq ty]
  cases layoutOfTy ty with
  | none => rfl
  | some layout =>
    dsimp only
    cases !Nat.beq bytes.length layout.size with
    | true => rfl
    | false =>
      rw [ite_bool_false rfl, ite_bool_false rfl]
      cases Nat.beq layout.size 0 with
      | true =>
        rw [ite_bool_true rfl, ite_bool_true rfl, mirEvalConstLit_eq]
      | false =>
        rw [ite_bool_false rfl, ite_bool_false rfl, execInitBytes?_eq bytes]
        cases initBytes? bytes with
        | none => rfl
        | some raw =>
          dsimp only
          rw [execDecodeUInt_eq endian raw, mirEvalConstLit_eq]

/-- Unconditional agreement between `execDecodeVal` and `decodeVal`. -/
theorem execDecodeVal_eq (endian : TargetEndian) (ty : MirTy) (bytes : List AllocByte) :
    execDecodeVal endian ty bytes = decodeVal endian ty bytes := by
  cases ty with
  | never => rfl
  | bool | int _ _ | unit | char | ordering | enum _ | ref _ _ | rawPtr _ _ | slice _
  | array _ _ | rangeTo _ | rangeFrom _ | unsupported =>
    dsimp only [execDecodeVal, decodeVal]
    apply execDecodeVal_layout_arm_eq
  | tuple fs =>
    cases fs with
    | nil =>
      dsimp only [execDecodeVal, decodeVal]
      apply execDecodeVal_layout_arm_eq
    | cons t1 r =>
      cases t1 with
      | int w s =>
        cases r with
        | nil =>
          dsimp only [execDecodeVal, decodeVal]
          apply execDecodeVal_layout_arm_eq
        | cons t2 r' =>
          cases t2 with
          | bool =>
            cases r' with
            | nil =>
              dsimp only [execDecodeVal, decodeVal]
              rw [execOverflowPairLayout_eq w, execByteSize_eq w]
              cases !Nat.beq bytes.length (overflowPairLayout w).size with
              | true => rfl
              | false =>
                rw [ite_bool_false rfl,
                  execInitBytes?_eq (bytes.take w.byteSize),
                  execInitBytes?_eq ((bytes.drop w.byteSize).take 1)]
                cases initBytes? (bytes.take w.byteSize) with
                | none => rfl
                | some intRaw =>
                  cases initBytes? ((bytes.drop w.byteSize).take 1) with
                  | none => rfl
                  | some boolRaw =>
                    dsimp only
                    rw [execDecodeUInt_eq endian intRaw, execDecodeUInt_eq endian boolRaw,
                      mirEvalConstLit_eq (.int w s),
                      mirEvalConstLit_eq .bool]
                    cases evalConstLit (.int w s) (.scalar (BitVec.ofNat 128 (decodeUInt endian intRaw))) with
                    | error _ => rfl
                    | ok intVal =>
                      dsimp only
                      cases evalConstLit .bool (.scalar (BitVec.ofNat 128 (decodeUInt endian boolRaw))) with
                      | error _ => rfl
                      | ok boolVal => rfl
            | cons t3 r'' =>
              dsimp only [execDecodeVal, decodeVal]
              apply execDecodeVal_layout_arm_eq
          | int _ _ | unit | never | char | ordering | enum _ | tuple _
          | ref _ _ | rawPtr _ _ | slice _ | array _ _ | rangeTo _ | rangeFrom _
          | unsupported =>
            cases r' with
            | nil =>
              dsimp only [execDecodeVal, decodeVal]
              apply execDecodeVal_layout_arm_eq
            | cons _ _ =>
              dsimp only [execDecodeVal, decodeVal]
              apply execDecodeVal_layout_arm_eq
      | bool | unit | never | char | ordering | enum _ | tuple _
      | ref _ _ | rawPtr _ _ | slice _ | array _ _ | rangeTo _ | rangeFrom _
      | unsupported =>
        cases r with
        | nil =>
          dsimp only [execDecodeVal, decodeVal]
          apply execDecodeVal_layout_arm_eq
        | cons _ r' =>
          cases r' with
          | nil =>
            dsimp only [execDecodeVal, decodeVal]
            apply execDecodeVal_layout_arm_eq
          | cons _ _ =>
            dsimp only [execDecodeVal, decodeVal]
            apply execDecodeVal_layout_arm_eq

/-- Unconditional agreement between `execLoadIndirect` and `loadIndirect`. -/
theorem execLoadIndirect_eq (mem : MemoryState) (ty : MirTy) (place : MemPlace) :
    execLoadIndirect mem ty place = loadIndirect mem ty place := by
  unfold execLoadIndirect loadIndirect
  rw [execLayoutOfTy_eq ty]
  cases layoutOfTy ty with
  | none => rfl
  | some layout =>
    dsimp only
    rw [execReadBytes_eq mem place layout.size layout.alignLog2]
    cases readBytes mem place layout.size layout.alignLog2 with
    | error _ => rfl
    | ok bytes =>
      have hEnd : execProfileTargetEndian = profileTargetEndian := rfl
      rw [hEnd]
      exact execDecodeVal_eq profileTargetEndian ty bytes

/-- Unconditional agreement between `execStoreIndirect` and `storeIndirect`. -/
theorem execStoreIndirect_eq (mem : MemoryState) (ty : MirTy) (place : MemPlace) (v : Val) :
    execStoreIndirect mem ty place v = storeIndirect mem ty place v := by
  unfold execStoreIndirect storeIndirect
  rw [execLayoutOfTy_eq ty]
  cases layoutOfTy ty with
  | none => rfl
  | some layout =>
    dsimp only
    have hEnd : execProfileTargetEndian = profileTargetEndian := rfl
    rw [hEnd, execEncodeVal_eq profileTargetEndian ty v]
    cases encodeVal profileTargetEndian ty v with
    | error _ => rfl
    | ok bytes => exact execWriteBytes_eq mem place layout.alignLog2 bytes

/-- Agreement between `execDeinitIndirect` and `deinitIndirect`. -/
theorem execDeinitIndirect_eq (mem : MemoryState) (ty : MirTy) (place : MemPlace) :
    execDeinitIndirect mem ty place = deinitIndirect mem ty place := by
  unfold execDeinitIndirect deinitIndirect
  rw [execLayoutOfTy_eq ty]
  cases layoutOfTy ty with
  | none => rfl
  | some layout => exact execWriteUninit_eq mem place layout.size layout.alignLog2

private theorem mirListSet?_eq_setElem? {α : Type} :
    ∀ (idx : Nat) (xs : List α) (v : α),
      mirListSet? xs idx v = Trusted.MirSemantics.setElem? xs idx v
  | 0, [], _ => rfl
  | 0, _ :: _, _ => rfl
  | n + 1, [], _ => rfl
  | n + 1, y :: ys, v => by
    change (match mirListSet? ys n v with
        | some rest' => some (y :: rest')
        | none => none) =
      (match Trusted.MirSemantics.setElem? ys n v with
        | some rest' => some (y :: rest')
        | none => none)
    rw [mirListSet?_eq_setElem? n ys v]

private theorem mirIsPrimitiveReadableTy_eq (ty : MirTy) :
    mirIsPrimitiveReadableTy ty = isPrimitiveReadableTy ty := by
  cases ty <;> rfl

private theorem execEvalPrimitiveOperandToSlot_eq (bodyLocals : List MirTy)
    (locals : List LocalSlot) (mem : MemoryState) (opnd : Operand) :
    execEvalPrimitiveOperandToSlot bodyLocals locals mem opnd =
      evalOperandToSlot bodyLocals locals mem isPrimitiveReadableTy opnd := by
  cases opnd with
  | copy place =>
    dsimp only [execEvalPrimitiveOperandToSlot, evalOperandToSlot]
    rw [mirListGet?_eq_getElem? bodyLocals place.localId,
      mirListGet?_eq_getElem? locals place.localId]
    cases Trusted.MirSemantics.getElem? bodyLocals place.localId with
    | none => rfl
    | some ty =>
      cases Trusted.MirSemantics.getElem? locals place.localId with
      | none => rfl
      | some slot =>
        cases slot with
        | dead => rfl
        | immediate _ | partialTuple _ => rfl
        | indirect mplace =>
          dsimp only
          rw [mirIsPrimitiveReadableTy_eq ty, execLoadIndirect_eq mem ty mplace]
          rfl
  | move place =>
    dsimp only [execEvalPrimitiveOperandToSlot, evalOperandToSlot]
    rw [mirListGet?_eq_getElem? bodyLocals place.localId,
      mirListGet?_eq_getElem? locals place.localId]
    cases Trusted.MirSemantics.getElem? bodyLocals place.localId with
    | none => rfl
    | some ty =>
      cases Trusted.MirSemantics.getElem? locals place.localId with
      | none => rfl
      | some slot =>
        cases slot with
        | dead | partialTuple _ => rfl
        | immediate _ =>
          dsimp only
          rw [mirLiveUninitSlot_eq ty,
            mirListSet?_eq_setElem? place.localId locals (liveUninitSlot ty)]
          rfl
        | indirect mplace =>
          dsimp only
          rw [mirIsPrimitiveReadableTy_eq ty, execLoadIndirect_eq mem ty mplace,
            execDeinitIndirect_eq mem ty mplace]
          rfl
  | constant c =>
    dsimp only [execEvalPrimitiveOperandToSlot, evalOperandToSlot]
    rw [mirEvalConstLit_eq c.ty c.lit]
    rfl

/-- Agreement between `execEvalPrimitiveOperand` and
`Trusted.MirSemantics.evalPrimitiveOperand`. -/
theorem execEvalPrimitiveOperand_eq (bodyLocals : List MirTy)
    (locals : List LocalSlot) (mem : MemoryState) (opnd : Operand) :
    execEvalPrimitiveOperand bodyLocals locals mem opnd =
      evalPrimitiveOperand bodyLocals locals mem opnd := by
  unfold execEvalPrimitiveOperand evalPrimitiveOperand
  rw [execEvalPrimitiveOperandToSlot_eq bodyLocals locals mem opnd]
  cases evalOperandToSlot bodyLocals locals mem isPrimitiveReadableTy opnd with
  | error _ => rfl
  | ok res =>
    cases res with
    | mk ty rest1 =>
      cases rest1 with
      | mk optVal rest2 =>
        dsimp only
        rw [mirIsPrimitiveReadableTy_eq ty]
        rfl

private theorem execLeBytesOfNat_length (k val : Nat) :
    (execLeBytesOfNat k val).length = k := by
  revert val
  induction k with
  | zero => intro _; rfl
  | succ k' ih =>
    intro val
    change (execLeBytesOfNat k' (Nat.div val 256)).length + 1 = k' + 1
    exact congrArg Nat.succ (ih (Nat.div val 256))

/-- Length law for `execEncodeUInt` across both endiannesses. -/
theorem execEncodeUInt_length (endian : TargetEndian) (k val : Nat) :
    (execEncodeUInt endian k val).length = k := by
  cases endian with
  | little => exact execLeBytesOfNat_length k val
  | big =>
    change (execLeBytesOfNat k val).reverse.length = k
    rw [listReverse_length]
    exact execLeBytesOfNat_length k val

private theorem leBytes_roundtrip_of_lt :
    ∀ (k val : Nat), val < Nat.pow 256 k →
      execNatOfLeBytes (execLeBytesOfNat k val) = val
  | 0, val, hLt => by
    cases val with
    | zero => rfl
    | succ _ =>
      have hOne : Nat.pow 256 0 = 1 := rfl
      rw [hOne] at hLt
      exact False.elim (Nat.not_lt_zero _ (Nat.lt_of_succ_lt_succ hLt))
  | k + 1, val, hLt => by
    have h256 : 0 < 256 := Nat.zero_lt_succ 255
    have hPowMul : Nat.pow 256 (k + 1) = 256 * Nat.pow 256 k :=
      Nat.mul_comm (Nat.pow 256 k) 256
    rw [hPowMul] at hLt
    have hDivLt : Nat.div val 256 < Nat.pow 256 k :=
      natDiv_lt_of_lt_mul_pos h256 hLt
    have hModLt : Nat.mod val 256 < 256 := Nat.mod_lt val h256
    change (UInt8.ofNat (Nat.mod val 256)).toNat +
        256 * execNatOfLeBytes (execLeBytesOfNat k (Nat.div val 256)) = val
    rw [uint8_toNat_ofNat_lt hModLt,
      leBytes_roundtrip_of_lt k (Nat.div val 256) hDivLt]
    exact natMod_add_div_pos val 256 h256

/-- Round-trip law for bounded unsigned integer byte encoding and decoding. -/
theorem decodeUInt_encodeUInt_of_lt (endian : TargetEndian) (k val : Nat)
    (hLt : val < Nat.pow 256 k) :
    execDecodeUInt endian (execEncodeUInt endian k val) = val := by
  cases endian with
  | little => exact leBytes_roundtrip_of_lt k val hLt
  | big =>
    change execNatOfLeBytes (execLeBytesOfNat k val).reverse.reverse = val
    rw [listReverse_reverse]
    exact leBytes_roundtrip_of_lt k val hLt

end Anneal.PureLift

end
