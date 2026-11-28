-- Copyright 2026 The Fuchsia Authors
--
-- Licensed under a BSD-style license <LICENSE-BSD>, Apache License, Version 2.0
-- <LICENSE-APACHE or https://www.apache.org/licenses/LICENSE-2.0>, or the MIT
-- license <LICENSE-MIT or https://opensource.org/licenses/MIT>, at your option.
-- This file may not be copied, modified, or distributed except according to
-- those terms.

prelude
import Init.NotationExtra
import Init.Data.BitVec.BasicAux
import Init.Data.Int.Basic
import Init.Data.Nat.Div.Basic
import Init.Data.Nat.Bitwise.Basic
import Init.Control.Except
import Trusted
import Trusted.Correspondence
import Anneal.MirCorrespondence.SimHelpers
import Anneal.MirCorrespondence.MemAlloc
import Anneal.MirCorrespondence.ByteCodec

namespace Anneal.MirCorrespondence

open Trusted Trusted.MirAst Trusted.MirSemantics Trusted.Correspondence
open Miri.ABI Miri.Memory Miri.Interpreter

/-!
# Layout, Pointer Alignment, Zero-Size Access, and Memory Framing Laws

Foundational slice-algebra, layout, pointer-alignment, zero-size access, and
`Trusted.MirSemantics.MemoryState` frame-preservation lemmas
(`Anneal.MirCorrespondence.LayoutAndAlign`) supporting
`Anneal.MirCorrespondence.MiriMemoryBridge`:

1. **Arithmetic, `UInt64`, `List`, and `Array.extract` slice algebra:**
   write-then-read and disjoint left/right subrange frame preservation.
2. **Layout, pointer alignment, and zero-size access characterization:**
   - `layoutOfTy` bounds, size-divisible-by-alignment, `Size.alignTo` on
     overflow pairs, and `Align.{bytes, fromBytes}` up to `Align.MAX = 2^29`.
   - Direct `Miri.Memory.Provenance` specs for `checkPtrAlign` across disabled
     (`Miri.Interpreter.AlignmentCheck.None`), address-only
     (`Miri.Interpreter.AlignmentCheck.Int`, plus an explicit counterexample
     showing divergence from `MirSemantics.isAligned` when `a.alignLog2 < k`),
     and symbolic allocation-alignment modes
     (`Miri.Interpreter.AlignmentCheck.Symbolic` via
     `PointerMachine.symbolicAlignment` and aligned base addresses), alongside
     relative `CtfeProvenance`.
   - Explicit characterization of `MirSemantics.Memory.{readBytes, writeBytes}`
     on `size = 0` (which resolves the allocation record and checks only
     `isAligned`, skipping liveness and bounds) paired with
     `zst_day1_alignLog2_zero` and
     `zst_day1_indirect_and_miri_align_agree` (every zero-sized layout admitted
     by `layoutOfTy` has `alignLog2 = 0`, where both `MirSemantics.isAligned`
     and `checkPtrAlign` at `Align.ONE` succeed unconditionally and
     `loadIndirect`/`storeIndirect`/`deinitIndirect` cannot diverge on
     alignment).
3. **`Trusted.MirSemantics.MemoryState` framing & `MemoryAllIdsLt` invariants:**
   `allocateStack`, `deallocateStack` use-after-free laws, `MemoryAllIdsLt`
   preservation across `replaceAllocation`, `writeBytes`, and
   `deallocateStack`, intra/inter-allocation `readBytes`/`writeBytes` framing,
   and indirect scalar round-trips.
-/

/-! ## Section 1: Arithmetic, `UInt64`, `List`, and `Array` Slice Algebra -/

theorem ite_pos_eq {α : Type} {c : Prop} [Decidable c] {a b : α}
    (h : c) : (if c then a else b) = a :=
  ite_eq_left_of_eq_true a b (eq_true h)

theorem ite_neg_eq {α : Type} {c : Prop} [Decidable c] {a b : α}
    (h : ¬ c) : (if c then a else b) = b :=
  ite_eq_right_of_eq_false a b (eq_false h)

theorem dite_pos_eq {α : Type} {c : Prop} [Decidable c]
    {a : c → α} {b : ¬ c → α} (h : c) :
    (if hc : c then a hc else b hc) = a h :=
  dite_eq_left_of_eq_true (eq_true h)

theorem u64_ofNat_toNat_of_lt {n : Nat} (h : n < Nat.pow 2 64) :
    (UInt64.ofNat n).toNat = n := by
  rw [UInt64.toNat_ofNat', Nat.mod_eq_of_lt h]

theorem u64_toNat_lt_pow64 (x : UInt64) : x.toNat < Nat.pow 2 64 :=
  x.toBitVec.isLt

theorem u64_add_toNat_of_lt {a b : UInt64}
    (h : a.toNat + b.toNat < Nat.pow 2 64) :
    (a + b).toNat = a.toNat + b.toNat := by
  rw [UInt64.toNat_add, Nat.mod_eq_of_lt h]

theorem u64_not_lt_of_le {a b : UInt64} (h : b.toNat ≤ a.toNat) :
    ¬ (a < b) := by
  rw [UInt64.lt_iff_toNat_lt]
  exact Nat.not_lt.mpr h

theorem u64_le_of_toNat_le {a b : UInt64} (h : a.toNat ≤ b.toNat) :
    a ≤ b := by
  rw [UInt64.le_iff_toNat_le]
  exact h

theorem u64_eq_of_toNat_eq {a b : UInt64} (h : a.toNat = b.toNat) :
    a = b :=
  UInt64.eq_of_toBitVec_eq (BitVec.eq_of_toNat_eq h)

theorem nat_ble_true_iff (a b : Nat) : Nat.ble a b = true ↔ a ≤ b :=
  Iff.of_eq Nat.ble_eq

theorem nat_beq_true_iff (a b : Nat) : Nat.beq a b = true ↔ a = b :=
  Iff.of_eq Nat.beq_eq

/-- Reading back the exact subslice overwritten in a list recovers the written
bytes. -/
theorem list_read_after_write {α : Type} (xs bs : List α) (off : Nat)
    (h_in : off + bs.length ≤ xs.length) :
    ((xs.take off ++ bs ++ xs.drop (off + bs.length)).drop off).take
        bs.length = bs := by
  have h_off_le : off ≤ xs.length :=
    Nat.le_trans (Nat.le_add_right off bs.length) h_in
  have h_take_len : (xs.take off).length = off := by
    rw [List.length_take]
    exact Nat.min_eq_left h_off_le
  rw [List.append_assoc, List.drop_append]
  have h_drop_nil : (xs.take off).drop off = [] :=
    List.drop_eq_nil_of_le (Nat.le_of_eq h_take_len)
  rw [h_drop_nil, h_take_len, Nat.sub_self, List.drop_zero, List.nil_append,
    List.take_left]

/-- Reading a subslice strictly to the left of an in-bounds overwritten range
is unchanged. -/
theorem list_read_after_write_left_inbounds {α : Type} (xs bs : List α)
    (off1 off2 sz2 : Nat)
    (h_off1_le : off1 ≤ xs.length)
    (h_disj : off2 + sz2 ≤ off1) :
    ((xs.take off1 ++ bs ++ xs.drop (off1 + bs.length)).drop off2).take sz2 =
      (xs.drop off2).take sz2 := by
  have h_le1 : off2 ≤ off1 := Nat.le_trans (Nat.le_add_right off2 sz2) h_disj
  have h_take_len : (xs.take off1).length = off1 := by
    rw [List.length_take]
    exact Nat.min_eq_left h_off1_le
  rw [List.append_assoc]
  rw [List.drop_append_of_le_length (by rw [h_take_len]; exact h_le1)]
  have h_sz2_le : sz2 ≤ ((xs.take off1).drop off2).length := by
    rw [List.length_drop, h_take_len]
    exact Nat.le_sub_of_add_le' h_disj
  rw [List.take_append_of_le_length h_sz2_le]
  rw [List.drop_take, List.take_take,
    Nat.min_eq_left (Nat.le_sub_of_add_le' h_disj)]

/-- Reading a subslice strictly to the right of an overwritten range is
unchanged. -/
theorem list_read_after_write_right {α : Type} (xs bs : List α)
    (off1 off2 sz2 : Nat)
    (h_in1 : off1 + bs.length ≤ xs.length)
    (h_disj : off1 + bs.length ≤ off2) :
    ((xs.take off1 ++ bs ++ xs.drop (off1 + bs.length)).drop off2).take sz2 =
      (xs.drop off2).take sz2 := by
  have h_off1_le : off1 ≤ xs.length :=
    Nat.le_trans (Nat.le_add_right off1 bs.length) h_in1
  have h_pref_len : (xs.take off1 ++ bs).length = off1 + bs.length := by
    rw [List.length_append, List.length_take, Nat.min_eq_left h_off1_le]
  rw [List.drop_append]
  have h_drop_pref : (xs.take off1 ++ bs).drop off2 = [] :=
    List.drop_eq_nil_of_le (by rw [h_pref_len]; exact h_disj)
  rw [h_drop_pref, List.nil_append, h_pref_len, List.drop_drop,
    Nat.add_sub_of_le h_disj]

/-- Overwriting an in-bounds subslice preserves total list length. -/
theorem list_write_length {α : Type} (xs bs : List α) (off : Nat)
    (h_in : off + bs.length ≤ xs.length) :
    (xs.take off ++ bs ++ xs.drop (off + bs.length)).length = xs.length := by
  have h_off_le : off ≤ xs.length :=
    Nat.le_trans (Nat.le_add_right off bs.length) h_in
  rw [List.length_append, List.length_append, List.length_take,
    List.length_drop, Nat.min_eq_left h_off_le]
  exact Nat.add_sub_of_le h_in

/-- Helper relating `Array.extract` to `List.take` / `List.drop`. -/
theorem array_extract_toList {α : Type} (a : Array α) (start stop : Nat) :
    (a.extract start stop).toList =
      (a.toList.drop start).take (stop - start) := by
  rw [Array.toList_extract, List.extract_eq_take_drop]

/-- Helper relating spliced `Array.extract` write to list splice. -/
theorem array_splice_toList {α : Type} (raw mid : Array α) (s : Nat)
    (_h_in : s + mid.size ≤ raw.size) :
    (raw.extract 0 s ++ mid ++ raw.extract (s + mid.size) raw.size).toList =
      raw.toList.take s ++ mid.toList ++ raw.toList.drop (s + mid.size) := by
  rw [Array.toList_append, Array.toList_append, array_extract_toList,
    array_extract_toList, List.drop_zero, Nat.sub_zero]
  have h_tail :
      (raw.toList.drop (s + mid.size)).take (raw.size - (s + mid.size)) =
        raw.toList.drop (s + mid.size) := by
    apply List.take_of_length_le
    rw [List.length_drop, Array.length_toList]
    exact Nat.le_refl _
  rw [h_tail]

/-- Splicing `mid` into `raw` at `[s, s + mid.size)` preserves array size. -/
theorem array_splice_size {α : Type} (raw mid : Array α) (s : Nat)
    (h_in : s + mid.size ≤ raw.size) :
    (raw.extract 0 s ++ mid ++ raw.extract (s + mid.size) raw.size).size =
      raw.size := by
  rw [← Array.length_toList, array_splice_toList raw mid s h_in]
  have h_in' : s + mid.toList.length ≤ raw.toList.length := by
    rw [Array.length_toList, Array.length_toList]
    exact h_in
  have h_w := list_write_length raw.toList mid.toList s h_in'
  rw [Array.length_toList (xs := mid)] at h_w
  rw [h_w, Array.length_toList]

/-- Extracting the exact overwritten range after an array splice returns `mid`.
-/
theorem array_extract_write_self {α : Type} (raw mid : Array α) (s : Nat)
    (h_in : s + mid.size ≤ raw.size) :
    (raw.extract 0 s ++ mid ++ raw.extract (s + mid.size) raw.size).extract
        s (s + mid.size) = mid := by
  apply Array.toList_inj.mp
  rw [array_extract_toList, array_splice_toList raw mid s h_in,
    Nat.add_sub_cancel_left]
  have h_in' : s + mid.toList.length ≤ raw.toList.length := by
    rw [Array.length_toList, Array.length_toList]
    exact h_in
  have h_r := list_read_after_write raw.toList mid.toList s h_in'
  rw [Array.length_toList (xs := mid)] at h_r
  exact h_r

/-- Extracting a range strictly to the left of an array splice is unchanged. -/
theorem array_extract_write_left {α : Type} (raw mid : Array α)
    (s o osz : Nat)
    (h_in : s + mid.size ≤ raw.size)
    (h_disj : o + osz ≤ s) :
    (raw.extract 0 s ++ mid ++ raw.extract (s + mid.size) raw.size).extract
        o (o + osz) = raw.extract o (o + osz) := by
  apply Array.toList_inj.mp
  rw [array_extract_toList, array_extract_toList,
    array_splice_toList raw mid s h_in, Nat.add_sub_cancel_left]
  have h_sle : s ≤ raw.toList.length := by
    rw [Array.length_toList]
    exact Nat.le_trans (Nat.le_add_right s mid.size) h_in
  have h_r := list_read_after_write_left_inbounds
    raw.toList mid.toList s o osz h_sle h_disj
  rw [Array.length_toList (xs := mid)] at h_r
  exact h_r

/-- Extracting a range strictly to the right of an array splice is unchanged. -/
theorem array_extract_write_right {α : Type} (raw mid : Array α)
    (s o osz : Nat)
    (h_in : s + mid.size ≤ raw.size)
    (h_disj : s + mid.size ≤ o) :
    (raw.extract 0 s ++ mid ++ raw.extract (s + mid.size) raw.size).extract
        o (o + osz) = raw.extract o (o + osz) := by
  apply Array.toList_inj.mp
  rw [array_extract_toList, array_extract_toList,
    array_splice_toList raw mid s h_in, Nat.add_sub_cancel_left]
  have h_in' : s + mid.toList.length ≤ raw.toList.length := by
    rw [Array.length_toList, Array.length_toList]
    exact h_in
  have h_disj' : s + mid.toList.length ≤ o := by
    rw [Array.length_toList]
    exact h_disj
  have h_r := list_read_after_write_right
    raw.toList mid.toList s o osz h_in' h_disj'
  rw [Array.length_toList (xs := mid)] at h_r
  exact h_r

/-! ## Section 2: Layout, Pointer Alignment, and Zero-Size Access Laws -/

/-- Every integer layout has `alignLog2 ≤ 4`, `size = 2 ^ alignLog2 ≤ 16`, and
size divisible by alignment. -/
theorem intLayout_props (w : IntWidth) :
    (intLayout w).alignLog2 ≤ 4 ∧
    (intLayout w).size = w.byteSize ∧
    (intLayout w).size = Nat.pow 2 (intLayout w).alignLog2 ∧
    (intLayout w).size ≤ 16 ∧
    Nat.mod (intLayout w).size (Nat.pow 2 (intLayout w).alignLog2) = 0 := by
  cases w <;> decide

/-- Every `layoutOfTy ty = some lay` satisfies `alignLog2 ≤ 4`, `size ≤ 32`,
`size < PointerWidth.w64.objSizeBound`, and Rust's size-multiple-of-alignment
invariant. -/
theorem layoutOfTy_props (ty : MirTy) (lay : MirSemantics.LayoutData)
    (h : layoutOfTy ty = some lay) :
    lay.alignLog2 ≤ 4 ∧
    lay.size ≤ 32 ∧
    lay.size < PointerWidth.w64.objSizeBound.toNat ∧
    Nat.mod lay.size (Nat.pow 2 lay.alignLog2) = 0 := by
  cases ty with
  | bool => dsimp only [layoutOfTy] at h; injection h with h; subst h; decide
  | int w _ =>
    dsimp only [layoutOfTy] at h
    injection h with h; subst h; cases w <;> decide
  | char => dsimp only [layoutOfTy] at h; injection h with h; subst h; decide
  | ordering =>
    dsimp only [layoutOfTy] at h; injection h with h; subst h; decide
  | unit => dsimp only [layoutOfTy] at h; injection h with h; subst h; decide
  | never => dsimp only [layoutOfTy] at h; injection h with h; subst h; decide
  | enum ety =>
    dsimp only [layoutOfTy] at h
    cases h_adm : enumAdmitted ety with
    | false => rw [h_adm] at h; cases h
    | true =>
      rw [h_adm] at h
      cases h_tr : ety.tagRepr with
      | zeroSized => rw [h_tr] at h; injection h with h; subst h; decide
      | scalar tagW _ =>
        rw [h_tr] at h; injection h with h; subst h; cases tagW <;> decide
  | tuple fs =>
    cases fs with
    | nil => dsimp only [layoutOfTy] at h; cases h
    | cons f1 rest =>
      cases f1 with
      | int w _ =>
        cases rest with
        | nil => dsimp only [layoutOfTy] at h; cases h
        | cons f2 tail =>
          cases f2 with
          | bool =>
            cases tail with
            | nil =>
              dsimp only [layoutOfTy] at h; injection h with h; subst h
              cases w <;> decide
            | cons _ _ => dsimp only [layoutOfTy] at h; cases h
          | _ => dsimp only [layoutOfTy] at h; cases h
      | _ => dsimp only [layoutOfTy] at h; cases h
  | ref _ _ | rawPtr _ _ | slice _ | str | array _ _ | vec _ | box _ | rangeTo _ | rangeFrom _
  | range _ | option _ | unsupported =>
    dsimp only [layoutOfTy] at h; cases h

/-- Every zero-sized `MirTy` layout admitted by `layoutOfTy` (`.unit`,
`.never`, and zero-sized enums) has `alignLog2 = 0` (`Align.ONE`). -/
theorem zst_day1_alignLog2_zero (ty : MirTy) (lay : MirSemantics.LayoutData)
    (h : layoutOfTy ty = some lay) (h_sz : lay.size = 0) :
    lay.alignLog2 = 0 := by
  cases ty with
  | bool =>
    dsimp only [layoutOfTy] at h; injection h with h; subst h; cases h_sz
  | int w _ =>
    dsimp only [layoutOfTy] at h; injection h with h; subst h
    cases w <;> cases h_sz
  | char =>
    dsimp only [layoutOfTy] at h; injection h with h; subst h; cases h_sz
  | ordering =>
    dsimp only [layoutOfTy] at h; injection h with h; subst h; cases h_sz
  | unit => dsimp only [layoutOfTy] at h; injection h with h; subst h; rfl
  | never => dsimp only [layoutOfTy] at h; injection h with h; subst h; rfl
  | enum ety =>
    dsimp only [layoutOfTy] at h
    cases h_adm : enumAdmitted ety with
    | false => rw [h_adm] at h; cases h
    | true =>
      rw [h_adm] at h
      cases h_tr : ety.tagRepr with
      | zeroSized => rw [h_tr] at h; injection h with h; subst h; rfl
      | scalar tagW _ =>
        rw [h_tr] at h; injection h with h; subst h
        cases tagW <;> cases h_sz
  | tuple fs =>
    cases fs with
    | nil => dsimp only [layoutOfTy] at h; cases h
    | cons f1 rest =>
      cases f1 with
      | int w _ =>
        cases rest with
        | nil => dsimp only [layoutOfTy] at h; cases h
        | cons f2 tail =>
          cases f2 with
          | bool =>
            cases tail with
            | nil =>
              dsimp only [layoutOfTy] at h; injection h with h; subst h
              cases w <;> cases h_sz
            | cons _ _ => dsimp only [layoutOfTy] at h; cases h
          | _ => dsimp only [layoutOfTy] at h; cases h
      | _ => dsimp only [layoutOfTy] at h; cases h
  | ref _ _ | rawPtr _ _ | slice _ | str | array _ _ | vec _ | box _ | rangeTo _ | rangeFrom _
  | range _ | option _ | unsupported =>
    dsimp only [layoutOfTy] at h; cases h

/-- `Trusted.MirSemantics.readBytes` at `size = 0` resolves the allocation
record and checks only `isAligned` (skipping liveness and bounds), returning
`.ok []` when the allocation exists and the place is aligned. -/
theorem readBytes_zero_size (m : MirSemantics.MemoryState) (place : MemPlace)
    (alignLog2 : Nat) (a : MirSemantics.Allocation)
    (h_fa : findAllocation place.allocId m.allocations = some a)
    (h_al : isAligned a place.offset alignLog2 = true) :
    readBytes m place 0 alignLog2 = .ok [] := by
  dsimp only [readBytes]
  rw [h_fa]
  dsimp only
  rw [h_al]
  rfl

/-- `Trusted.MirSemantics.readBytes` at `size = 0` faults with `.undefined` on
a misaligned place, even when the allocation is dead or the offset is out of
bounds. -/
theorem readBytes_zero_size_misaligned (m : MirSemantics.MemoryState)
    (place : MemPlace) (alignLog2 : Nat) (a : MirSemantics.Allocation)
    (h_fa : findAllocation place.allocId m.allocations = some a)
    (h_al : isAligned a place.offset alignLog2 = false) :
    readBytes m place 0 alignLog2 = .error .undefined := by
  dsimp only [readBytes]
  rw [h_fa]
  dsimp only
  rw [h_al]
  rfl

/-- `Trusted.MirSemantics.writeBytes` with empty `bytes` resolves the
allocation record and checks only `isAligned` (skipping liveness, bounds, and
mutability), returning `.ok m` when the allocation exists and the place is
aligned. -/
theorem writeBytes_zero_size (m : MirSemantics.MemoryState) (place : MemPlace)
    (alignLog2 : Nat) (a : MirSemantics.Allocation)
    (h_fa : findAllocation place.allocId m.allocations = some a)
    (h_al : isAligned a place.offset alignLog2 = true) :
    writeBytes m place alignLog2 [] = .ok m := by
  dsimp only [writeBytes]
  rw [h_fa]
  dsimp only
  rw [h_al]
  rfl

/-- `Miri.ABI.Size.alignTo` on `w.byteSize + 1` rounded to `intLayout w`'s
alignment agrees with `Trusted.MirSemantics.overflowPairLayout w`. -/
theorem overflowPairLayout_alignTo_eq (w : IntWidth) :
    Miri.ABI.Size.alignTo
      (Size.ofBytes (UInt64.ofNat (w.byteSize + 1)))
      ⟨(intLayout w).alignLog2⟩ =
      .ok (Size.ofBytes (UInt64.ofNat (overflowPairLayout w).size)) := by
  cases w <;> decide

/-- Exact `Align.bytes` and `Align.fromBytes` round-trip for every alignment
exponent `k ≤ 29` (`Align.MAX.pow2 = 29`). -/
theorem align_bytes_and_fromBytes_of_le_29 (k : Nat) (hk : k ≤ 29) :
    Align.bytes ⟨k⟩ = .ok (UInt64.ofNat (Nat.pow 2 k)) ∧
    Align.fromBytes (UInt64.ofNat (Nat.pow 2 k)) = .ok ⟨k⟩ := by
  cases k with
  | zero => decide
  | succ k => cases k with | zero => decide | succ k =>
    cases k with | zero => decide | succ k =>
    cases k with | zero => decide | succ k =>
    cases k with | zero => decide | succ k =>
    cases k with | zero => decide | succ k =>
    cases k with | zero => decide | succ k =>
    cases k with | zero => decide | succ k =>
    cases k with | zero => decide | succ k =>
    cases k with | zero => decide | succ k =>
    cases k with | zero => decide | succ k =>
    cases k with | zero => decide | succ k =>
    cases k with | zero => decide | succ k =>
    cases k with | zero => decide | succ k =>
    cases k with | zero => decide | succ k =>
    cases k with | zero => decide | succ k =>
    cases k with | zero => decide | succ k =>
    cases k with | zero => decide | succ k =>
    cases k with | zero => decide | succ k =>
    cases k with | zero => decide | succ k =>
    cases k with | zero => decide | succ k =>
    cases k with | zero => decide | succ k =>
    cases k with | zero => decide | succ k =>
    cases k with | zero => decide | succ k =>
    cases k with | zero => decide | succ k =>
    cases k with | zero => decide | succ k =>
    cases k with | zero => decide | succ k =>
    cases k with | zero => decide | succ k =>
    cases k with | zero => decide | succ k =>
    cases k with | zero => decide | succ k =>
      exact False.elim (Nat.not_lt.mpr hk
        (Nat.lt_of_lt_of_le (by decide) (Nat.le_add_left 30 k)))

theorem align_pow2_lt_pow64 {k : Nat} (hk : k ≤ 29) :
    Nat.pow 2 k < Nat.pow 2 64 :=
  Nat.lt_of_le_of_lt (Nat.pow_le_pow_right (by decide) hk) (by decide)

theorem align_pow2_pos (k : Nat) : 0 < Nat.pow 2 k :=
  Nat.pow_pos (by decide)

/-- Bitwise mask identity: `(UInt64.land x (2^k - 1)).toNat = x.toNat % 2^k`
for any `k ≤ 29`. -/
theorem u64_land_pow2_sub_one_eq_mod (x : UInt64) (k : Nat) (hk : k ≤ 29) :
    (UInt64.land x (UInt64.ofNat (Nat.pow 2 k) - 1)).toNat =
      Nat.mod x.toNat (Nat.pow 2 k) := by
  have h_pos : 1 ≤ Nat.pow 2 k := align_pow2_pos k
  have h_lt : Nat.pow 2 k < Nat.pow 2 64 := align_pow2_lt_pow64 hk
  have h_sub_toNat :
      (UInt64.ofNat (Nat.pow 2 k) - 1).toNat = Nat.pow 2 k - 1 := by
    have h_a : (UInt64.ofNat (Nat.pow 2 k)).toNat = Nat.pow 2 k :=
      u64_ofNat_toNat_of_lt h_lt
    have h_1 : (1 : UInt64).toNat = 1 := rfl
    have h_le : (1 : UInt64) ≤ UInt64.ofNat (Nat.pow 2 k) :=
      u64_le_of_toNat_le (by rw [h_a, h_1]; exact h_pos)
    rw [UInt64.toNat_sub_of_le (UInt64.ofNat (Nat.pow 2 k)) 1 h_le, h_a, h_1]
  have h_and : (UInt64.land x (UInt64.ofNat (Nat.pow 2 k) - 1)).toNat =
      Nat.land x.toNat (UInt64.ofNat (Nat.pow 2 k) - 1).toNat :=
    BitVec.toNat_and x.toBitVec (UInt64.ofNat (Nat.pow 2 k) - 1).toBitVec
  rw [h_and, h_sub_toNat]
  exact Nat.and_two_pow_sub_one_eq_mod x.toNat k

/-- Exact bridge between `Miri.ABI.Size.isAligned` and `Nat.mod` alignment
used by `Trusted.MirSemantics.isAligned` for every `k ≤ 29`. -/
theorem miriSize_isAligned_eq_natMod (off : Size) (k : Nat) (hk : k ≤ 29) :
    Miri.ABI.Size.isAligned off ⟨k⟩ =
      .ok (Nat.beq (Nat.mod off.bytes.toNat (Nat.pow 2 k)) 0) := by
  dsimp only [Miri.ABI.Size.isAligned, bind, Bind.bind, Except.bind, pure,
    Pure.pure, Except.pure]
  rw [(align_bytes_and_fromBytes_of_le_29 k hk).1]
  dsimp only
  apply congrArg Except.ok
  have h_land := u64_land_pow2_sub_one_eq_mod off.bytes k hk
  cases h_z : Nat.beq (Nat.mod off.bytes.toNat (Nat.pow 2 k)) 0 with
  | true =>
    have h_eq0 : Nat.mod off.bytes.toNat (Nat.pow 2 k) = 0 :=
      (nat_beq_true_iff _ _).1 h_z
    have h_u0 : UInt64.land off.bytes (UInt64.ofNat (Nat.pow 2 k) - 1) = 0 :=
      u64_eq_of_toNat_eq (h_land.trans h_eq0)
    rw [h_u0]
    rfl
  | false =>
    cases h_eq :
        (UInt64.land off.bytes (UInt64.ofNat (Nat.pow 2 k) - 1) == 0) with
    | false => rfl
    | true =>
      have h_u0 : UInt64.land off.bytes (UInt64.ofNat (Nat.pow 2 k) - 1) = 0 :=
        eq_of_beq h_eq
      have h_m0 : Nat.mod off.bytes.toNat (Nat.pow 2 k) = 0 := by
        rw [← h_land, h_u0]
        rfl
      rw [(nat_beq_true_iff _ _).2 h_m0] at h_z
      cases h_z

/-- `UInt64.mod` for `2^k` (`k ≤ 29`) matches `Nat.mod`. -/
theorem u64_mod_pow2_toNat (x : UInt64) (k : Nat) (hk : k ≤ 29) :
    (UInt64.mod x (UInt64.ofNat (Nat.pow 2 k))).toNat =
      Nat.mod x.toNat (Nat.pow 2 k) := by
  change (HMod.hMod x (UInt64.ofNat (Nat.pow 2 k))).toNat =
    Nat.mod x.toNat (Nat.pow 2 k)
  rw [UInt64.toNat_mod, u64_ofNat_toNat_of_lt (align_pow2_lt_pow64 hk)]
  rfl

/-- Mirror of `Miri.Memory.Access`'s private `checkedAlign` (`Align.pow2 ≤ 29`).
-/
private def accessCheckedAlignMirror (align : Align) :
    Except AccessError Align :=
  Except.bind
    (Except.mapError AccessError.malformedAlignment (Align.bytes align))
    fun bytes =>
  Except.bind
    (Except.mapError AccessError.malformedAlignment (Align.fromBytes bytes))
    fun norm =>
  if (norm == align) = true then Except.ok align
  else Except.error (AccessError.malformedAlignment (AlignError.tooLarge bytes))

private theorem accessCheckedAlignMirror_ok (align : Align)
    (h : align.pow2 ≤ 29) :
    accessCheckedAlignMirror align = .ok align := by
  have h_ab := align_bytes_and_fromBytes_of_le_29 align.pow2 h
  dsimp only [accessCheckedAlignMirror]
  have h_ab1 :
      Align.bytes align = .ok (UInt64.ofNat (Nat.pow 2 align.pow2)) := h_ab.1
  rw [h_ab1]
  dsimp only [Except.mapError, Except.bind]
  rw [h_ab.2]
  dsimp only [Except.mapError, Except.bind]
  have h_beq : (({ pow2 := align.pow2 } : Align) == align) = true := by
    cases align
    exact beq_self_eq_true _
  rw [h_beq, ite_true_eq]

/-- Alignment 1 (`Align.ONE`) never reports misalignment in `Miri.Memory`,
regardless of pointer address, allocation liveness, or enforcement flag. -/
theorem isPtrMisaligned_alignOne {Prov ProvExtra : Type}
    [PointerProvenance Prov]
    (ptr : Miri.Memory.Pointer (Option Prov)) (enforce : Bool)
    (resolve : PointerResolver Prov ProvExtra)
    (lookup : Miri.Memory.AllocId → Except AllocationLookupError AllocationInfo)
    (hook :
      Miri.Memory.AllocId → Align → AllocationKind → Size → Align →
        Option Misalignment) :
    isPtrMisaligned ptr Align.ONE enforce resolve lookup hook = .ok none := by
  cases enforce <;> rfl

theorem checkPtrAlign_alignOne {Prov ProvExtra : Type} [PointerProvenance Prov]
    (ptr : Miri.Memory.Pointer (Option Prov)) (enforce : Bool)
    (resolve : PointerResolver Prov ProvExtra)
    (lookup : Miri.Memory.AllocId → Except AllocationLookupError AllocationInfo)
    (hook :
      Miri.Memory.AllocId → Align → AllocationKind → Size → Align →
        Option Misalignment) :
    checkPtrAlign ptr Align.ONE enforce resolve lookup hook = .ok () := by
  dsimp only [checkPtrAlign, bind, Bind.bind, Except.bind, pure, Pure.pure,
    Except.pure]
  rw [isPtrMisaligned_alignOne]

/-- Mechanized Day-1 zero-size indirect access and Miri alignment agreement:
every `MirTy` with `layoutOfTy ty = some lay` and `lay.size = 0` carries
`lay.alignLog2 = 0` (`Align.ONE`), so both `MirSemantics.isAligned` and
`Miri.Memory.checkPtrAlign` succeed unconditionally at `⟨lay.alignLog2⟩`, while
`loadIndirect`, `storeIndirect`, and `deinitIndirect` on a place whose
allocation record exists reduce without alignment divergence. -/
theorem zst_day1_indirect_and_miri_align_agree {Prov ProvExtra : Type}
    [PointerProvenance Prov]
    (ty : MirTy) (lay : MirSemantics.LayoutData)
    (h_lay : layoutOfTy ty = some lay) (h_sz : lay.size = 0)
    (m : MirSemantics.MemoryState) (place : MemPlace)
    (a : MirSemantics.Allocation) (off : Nat)
    (h_fa : findAllocation place.allocId m.allocations = some a)
    (ptr : Miri.Memory.Pointer (Option Prov)) (enforce : Bool)
    (resolve : PointerResolver Prov ProvExtra)
    (lookup : Miri.Memory.AllocId → Except AllocationLookupError AllocationInfo)
    (hook :
      Miri.Memory.AllocId → Align → AllocationKind → Size → Align →
        Option Misalignment) :
    lay.alignLog2 = 0 ∧
    MirSemantics.isAligned a off lay.alignLog2 = true ∧
    checkPtrAlign ptr ⟨lay.alignLog2⟩ enforce resolve lookup hook = .ok () ∧
    loadIndirect m ty place = decodeVal profileTargetEndian ty [] ∧
    deinitIndirect m ty place = .ok m ∧
    (∀ v : Val,
      encodeVal profileTargetEndian ty v = .ok [] →
      storeIndirect m ty place v = .ok m) := by
  have h_al : lay.alignLog2 = 0 := zst_day1_alignLog2_zero ty lay h_lay h_sz
  have h_isal : ∀ o : Nat, MirSemantics.isAligned a o lay.alignLog2 = true := by
    intro o
    rw [h_al]
    dsimp only [MirSemantics.isAligned]
    rw [(nat_ble_true_iff 0 a.alignLog2).2 (Nat.zero_le _), Bool.true_and,
      show Nat.pow 2 0 = 1 from rfl]
    change Nat.beq (HMod.hMod o 1) 0 = true
    rw [Nat.mod_one]
    rfl
  have h_rd : readBytes m place 0 lay.alignLog2 = .ok [] :=
    readBytes_zero_size m place lay.alignLog2 a h_fa (h_isal place.offset)
  have h_wr : writeBytes m place lay.alignLog2 [] = .ok m :=
    writeBytes_zero_size m place lay.alignLog2 a h_fa (h_isal place.offset)
  refine ⟨h_al, h_isal off, ?_, ?_, ?_, ?_⟩
  · rw [h_al]
    exact checkPtrAlign_alignOne ptr enforce resolve lookup hook
  · dsimp only [loadIndirect]
    rw [h_lay]
    dsimp only
    rw [h_sz, h_rd]
  · dsimp only [deinitIndirect, writeUninit]
    rw [h_lay]
    dsimp only
    rw [h_sz]
    exact h_wr
  · intro v h_enc
    dsimp only [storeIndirect]
    rw [h_lay]
    dsimp only
    rw [h_enc]
    exact h_wr

/-- With `enforceAlignment = false` (corresponding to
`Miri.Interpreter.AlignmentCheck.None`), `checkPtrAlign` succeeds for every
valid alignment exponent `k ≤ 29`. -/
theorem checkPtrAlign_provenance_disabled {ProvExtra : Type}
    (ptr : Miri.Memory.Pointer (Option Miri.Memory.Provenance))
    (k : Nat) (hk_le : k ≤ 29)
    (resolve : PointerResolver Miri.Memory.Provenance ProvExtra)
    (lookup : Miri.Memory.AllocId → Except AllocationLookupError AllocationInfo)
    (hook :
      Miri.Memory.AllocId → Align → AllocationKind → Size → Align →
        Option Misalignment) :
    checkPtrAlign ptr ⟨k⟩ false resolve lookup hook = .ok () := by
  have h_req := align_bytes_and_fromBytes_of_le_29 k hk_le
  have h_mis :
      isPtrMisaligned ptr ⟨k⟩ false resolve lookup hook = .ok none := by
    change
      (Except.bind (accessCheckedAlignMirror ⟨k⟩) fun req =>
        Except.bind (Except.mapError AccessError.malformedAlignment req.bytes)
          fun reqBytes =>
        if (!false || reqBytes == 1) = true then Except.ok none else _) =
      .ok none
    rw [accessCheckedAlignMirror_ok ⟨k⟩ hk_le]
    dsimp only [Except.bind]
    rw [h_req.1]
    rfl
  dsimp only [checkPtrAlign, bind, Bind.bind, Except.bind, pure, Pure.pure,
    Except.pure]
  rw [h_mis]

private theorem pow2_u64_ne1 {k : Nat} (hk_pos : 0 < k) (hk_le : k ≤ 29) :
    (UInt64.ofNat (Nat.pow 2 k) == 1) = false := by
  have h_pow_gt1 : 1 < Nat.pow 2 k :=
    Nat.lt_of_lt_of_le (by decide) (Nat.pow_le_pow_right (by decide) hk_pos)
  cases h_eq : (UInt64.ofNat (Nat.pow 2 k) == 1) with
  | false => rfl
  | true =>
    have h_n : Nat.pow 2 k = 1 := by
      rw [← u64_ofNat_toNat_of_lt (align_pow2_lt_pow64 hk_le), eq_of_beq h_eq]
      rfl
    exact False.elim (Nat.ne_of_gt h_pow_gt1 h_n)

private theorem pow2_u64_ne0 {k : Nat} (hk_le : k ≤ 29) :
    (UInt64.ofNat (Nat.pow 2 k) == 0) = false := by
  cases h_eq : (UInt64.ofNat (Nat.pow 2 k) == 0) with
  | false => rfl
  | true =>
    have h_n : Nat.pow 2 k = 0 := by
      rw [← u64_ofNat_toNat_of_lt (align_pow2_lt_pow64 hk_le), eq_of_beq h_eq]
      rfl
    exact False.elim (Nat.ne_of_gt (align_pow2_pos k) h_n)

/-- Mirror of `Miri.Memory.Access`'s private `offsetMisalignment`. -/
private def accessOffsetMisalignmentMirror (offset : Size) (required : Align) :
    Except AccessError (Option Misalignment) :=
  Except.bind (accessCheckedAlignMirror required) fun req =>
  Except.bind (Except.mapError AccessError.malformedAlignment req.bytes)
    fun reqBytes =>
  if (reqBytes == 0 || HMod.hMod offset.bytes reqBytes == 0) = true then
    Except.ok none
  else
    Except.ok (some (Misalignment.mk (Align.maxAlignedFactor offset) req))

private theorem accessOffsetMisalignmentMirror_eq (offset : Size) (k : Nat)
    (hk_le : k ≤ 29) :
    accessOffsetMisalignmentMirror offset ⟨k⟩ =
      Except.ok
        (if (UInt64.mod offset.bytes (UInt64.ofNat (Nat.pow 2 k)) == 0) = true
        then none
        else some (Misalignment.mk (Align.maxAlignedFactor offset) ⟨k⟩)) := by
  dsimp only [accessOffsetMisalignmentMirror]
  rw [accessCheckedAlignMirror_ok ⟨k⟩ hk_le]
  dsimp only [Except.bind]
  rw [(align_bytes_and_fromBytes_of_le_29 k hk_le).1]
  dsimp only [Except.mapError, Except.bind]
  rw [pow2_u64_ne0 hk_le, Bool.false_or]
  cases (UInt64.mod offset.bytes (UInt64.ofNat (Nat.pow 2 k)) == 0) <;> rfl

/-- Exact mirror of `Miri.Memory.isPtrMisaligned` (with `hook = none`) so
`checkedAlign` and `offsetMisalignment` unfold by `rfl`. -/
private def isPtrMisalignedMirror {Prov ProvExtra : Type}
    [PointerProvenance Prov]
    (ptr : Miri.Memory.Pointer (Option Prov)) (required : Align)
    (enforce : Bool)
    (resolve : PointerResolver Prov ProvExtra)
    (lookup : Miri.Memory.AllocId → Except AllocationLookupError AllocationInfo)
    : Except AccessError (Option Misalignment) :=
  Except.bind (accessCheckedAlignMirror required) fun req =>
  Except.bind (Except.mapError AccessError.malformedAlignment req.bytes)
    fun reqBytes =>
  if (!enforce || reqBytes == 1) = true then Except.ok none
  else
    match resolve ptr 0 with
    | Except.error address =>
      accessOffsetMisalignmentMirror (Size.ofBytes address) req
    | Except.ok resolved =>
      match lookup resolved.allocId with
      | Except.ok info =>
        Except.bind (accessCheckedAlignMirror info.align) fun allocAl =>
        if PointerProvenance.offsetIsAddr (Prov := Prov) = true then
          accessOffsetMisalignmentMirror ptr.offset req
        else
          Except.bind
            (Except.mapError AccessError.malformedAlignment allocAl.bytes)
            fun allocAlBytes =>
          if allocAlBytes < reqBytes then
            Except.ok (some (Misalignment.mk allocAl req))
          else
            accessOffsetMisalignmentMirror resolved.offset req
      | Except.error reason =>
        Except.error (AccessError.allocationLookup reason)

private theorem isPtrMisaligned_eq_mirror {Prov ProvExtra : Type}
    [PointerProvenance Prov]
    (ptr : Miri.Memory.Pointer (Option Prov)) (required : Align)
    (enforce : Bool)
    (resolve : PointerResolver Prov ProvExtra)
    (lookup : Miri.Memory.AllocId → Except AllocationLookupError AllocationInfo)
    : isPtrMisaligned ptr required enforce resolve lookup
        (fun _ _ _ _ _ => none) =
      isPtrMisalignedMirror ptr required enforce resolve lookup := rfl

/-- Exact mirror of `Miri.Memory.isPtrMisaligned` when the precomputed override
from `PointerMachine.symbolicAlignment` is `some mis`, so `checkedAlign`
unfolds by `rfl`. -/
private def isPtrMisalignedSomeMirror {Prov ProvExtra : Type}
    [PointerProvenance Prov]
    (ptr : Miri.Memory.Pointer (Option Prov)) (required : Align)
    (enforce : Bool)
    (resolve : PointerResolver Prov ProvExtra)
    (lookup : Miri.Memory.AllocId → Except AllocationLookupError AllocationInfo)
    (mis : Misalignment) : Except AccessError (Option Misalignment) :=
  Except.bind (accessCheckedAlignMirror required) fun req =>
  Except.bind (Except.mapError AccessError.malformedAlignment req.bytes)
    fun reqBytes =>
  if (!enforce || reqBytes == 1) = true then Except.ok none
  else
    match resolve ptr 0 with
    | Except.error address =>
      accessOffsetMisalignmentMirror (Size.ofBytes address) req
    | Except.ok resolved =>
      match lookup resolved.allocId with
      | Except.ok info =>
        Except.bind (accessCheckedAlignMirror info.align) fun _ =>
        Except.ok (some mis)
      | Except.error reason =>
        Except.error (AccessError.allocationLookup reason)

private theorem isPtrMisaligned_eq_someMirror {Prov ProvExtra : Type}
    [PointerProvenance Prov]
    (ptr : Miri.Memory.Pointer (Option Prov)) (required : Align)
    (enforce : Bool)
    (resolve : PointerResolver Prov ProvExtra)
    (lookup : Miri.Memory.AllocId → Except AllocationLookupError AllocationInfo)
    (mis : Misalignment) :
    isPtrMisaligned ptr required enforce resolve lookup
        (fun _ _ _ _ _ => some mis) =
      isPtrMisalignedSomeMirror ptr required enforce resolve lookup mis := rfl

/-- Address-only `checkPtrAlign` characterization on `Miri.Memory.Provenance`
(`offsetIsAddr = true`, `hook = none`, matching
`Miri.Interpreter.AlignmentCheck.Int`) for nonzero alignment exponents
`0 < k ≤ 29`. -/
theorem checkPtrAlign_addrProv_of_resolved
    {ProvExtra : Type}
    (ptr : Miri.Memory.Pointer (Option Miri.Memory.Provenance))
    (k : Nat) (hk_pos : 0 < k) (hk_le : k ≤ 29)
    (resolve : PointerResolver Miri.Memory.Provenance ProvExtra)
    (lookup : Miri.Memory.AllocId → Except AllocationLookupError AllocationInfo)
    (resolved : ResolvedPointer ProvExtra)
    (info : AllocationInfo)
    (h_res : resolve ptr 0 = .ok resolved)
    (h_lk : lookup resolved.allocId = .ok info)
    (h_al : info.align.pow2 ≤ 29) :
    (Nat.mod ptr.offset.bytes.toNat (Nat.pow 2 k) = 0 →
      checkPtrAlign ptr ⟨k⟩ true resolve lookup (fun _ _ _ _ _ => none) =
        .ok ()) ∧
    (Nat.mod ptr.offset.bytes.toNat (Nat.pow 2 k) ≠ 0 →
      checkPtrAlign ptr ⟨k⟩ true resolve lookup (fun _ _ _ _ _ => none) =
        .error (.alignmentCheckFailed
          ⟨Align.maxAlignedFactor ptr.offset, ⟨k⟩⟩)) := by
  have h_req := align_bytes_and_fromBytes_of_le_29 k hk_le
  have h_step :
      isPtrMisaligned ptr ⟨k⟩ true resolve lookup (fun _ _ _ _ _ => none) =
        .ok
          (if (UInt64.mod ptr.offset.bytes (UInt64.ofNat (Nat.pow 2 k)) == 0) =
              true then
            none
          else
            some ⟨Align.maxAlignedFactor ptr.offset, ⟨k⟩⟩) := by
    rw [isPtrMisaligned_eq_mirror]
    dsimp only [isPtrMisalignedMirror]
    rw [accessCheckedAlignMirror_ok ⟨k⟩ hk_le]
    dsimp only [Except.bind]
    rw [h_req.1]
    dsimp only [Except.mapError, Except.bind]
    rw [pow2_u64_ne1 hk_pos hk_le]
    rw [show (!true || false) = false from rfl, ite_false_eq, h_res]
    dsimp only
    rw [h_lk]
    dsimp only [Except.bind]
    rw [accessCheckedAlignMirror_ok info.align h_al]
    dsimp only [Except.bind, PointerProvenance.offsetIsAddr]
    rw [accessOffsetMisalignmentMirror_eq ptr.offset k hk_le]
    rfl
  constructor
  · intro h_mod0
    dsimp only [checkPtrAlign, bind, Bind.bind, Except.bind, pure, Pure.pure,
      Except.pure]
    rw [h_step]
    have h_um0 : UInt64.mod ptr.offset.bytes (UInt64.ofNat (Nat.pow 2 k)) = 0 :=
      u64_eq_of_toNat_eq
        ((u64_mod_pow2_toNat ptr.offset.bytes k hk_le).trans h_mod0)
    rw [h_um0]
    rfl
  · intro h_mod_ne0
    dsimp only [checkPtrAlign, bind, Bind.bind, Except.bind, pure, Pure.pure,
      Except.pure]
    rw [h_step]
    have h_um_ne :
        (UInt64.mod ptr.offset.bytes (UInt64.ofNat (Nat.pow 2 k)) == 0) =
          false := by
      cases h_eq :
          (UInt64.mod ptr.offset.bytes (UInt64.ofNat (Nat.pow 2 k)) == 0) with
      | false => rfl
      | true =>
        have h_m : Nat.mod ptr.offset.bytes.toNat (Nat.pow 2 k) = 0 := by
          rw [← u64_mod_pow2_toNat ptr.offset.bytes k hk_le, eq_of_beq h_eq]
          rfl
        exact False.elim (h_mod_ne0 h_m)
    rw [h_um_ne, ite_false_eq]
    rfl

/-- Bidirectional `↔` for address-only `checkPtrAlign` on
`Miri.Memory.Provenance` across all valid alignment exponents `k ≤ 29`
(including `k = 0`). -/
theorem checkPtrAlign_provenance_addr_ok_iff
    {ProvExtra : Type}
    (ptr : Miri.Memory.Pointer (Option Miri.Memory.Provenance))
    (k : Nat) (hk_le : k ≤ 29)
    (resolve : PointerResolver Miri.Memory.Provenance ProvExtra)
    (lookup : Miri.Memory.AllocId → Except AllocationLookupError AllocationInfo)
    (resolved : ResolvedPointer ProvExtra)
    (info : AllocationInfo)
    (h_res : resolve ptr 0 = .ok resolved)
    (h_lk : lookup resolved.allocId = .ok info)
    (h_al : info.align.pow2 ≤ 29) :
    checkPtrAlign ptr ⟨k⟩ true resolve lookup (fun _ _ _ _ _ => none) = .ok () ↔
      Nat.mod ptr.offset.bytes.toNat (Nat.pow 2 k) = 0 := by
  cases k with
  | zero =>
    constructor
    · intro _
      exact Nat.mod_one _
    · intro _
      exact checkPtrAlign_alignOne ptr true resolve lookup _
  | succ k' =>
    have h_spec := checkPtrAlign_addrProv_of_resolved ptr (k' + 1)
      (Nat.succ_pos k') hk_le resolve lookup resolved info h_res h_lk h_al
    constructor
    · intro h_ok
      cases h_z : Nat.beq (Nat.mod ptr.offset.bytes.toNat (Nat.pow 2 (k' + 1)))
          0 with
      | true => exact (nat_beq_true_iff _ _).1 h_z
      | false =>
        have h_ne : Nat.mod ptr.offset.bytes.toNat (Nat.pow 2 (k' + 1)) ≠ 0 :=
          fun h0 => by rw [(nat_beq_true_iff _ _).2 h0] at h_z; cases h_z
        rw [h_spec.2 h_ne] at h_ok
        cases h_ok
    · exact h_spec.1

/-- Explicit counterexample demonstrating why address-only `checkPtrAlign`
(`hook = none`, `Miri.Interpreter.AlignmentCheck.Int`) diverges from
`MirSemantics.isAligned` when an under-aligned allocation (`alignLog2 = 0`) sits
at an accidentally 4-byte-aligned address (`0`): `checkPtrAlign` returns
`.ok ()` for `k = 2` while `MirSemantics.isAligned` returns `false`. -/
theorem checkPtrAlign_provenance_addr_diverges_when_underaligned :
    let allocId : Miri.Memory.AllocId := ⟨1, by decide⟩
    let ptr : Miri.Memory.Pointer (Option Miri.Memory.Provenance) :=
      ⟨Size.ZERO, some (.concrete allocId Miri.Memory.BorTag.one)⟩
    let info : AllocationInfo := ⟨Size.ofBytes 4, Align.ONE, .liveData, .Mut⟩
    let lookup :
        Miri.Memory.AllocId → Except AllocationLookupError AllocationInfo :=
      fun _ => .ok info
    let a : MirSemantics.Allocation :=
      ⟨1, 0, .mut, List.replicate 4 .uninit, true⟩
    checkPtrAlign ptr ⟨2⟩ true refResolvePointerPure lookup
      (fun _ _ _ _ _ => none) = .ok () ∧
    MirSemantics.isAligned a 0 2 = false := by
  decide

/-- Bidirectional `↔` between upstream
`Miri.Interpreter.PointerMachine.symbolicAlignment`
(`Miri.Interpreter.AlignmentCheck.Symbolic` without dynamic alignment promises)
and `Trusted.MirSemantics.isAligned` for all valid alignment exponents
`k ≤ 29`. -/
theorem symbolicAlignment_ok_none_iff_mirIsAligned
    (a : MirSemantics.Allocation) (offset : Size) (k : Nat) (hk_le : k ≤ 29) :
    Miri.Interpreter.PointerMachine.symbolicAlignment true .liveData
        ⟨a.alignLog2⟩ none offset ⟨k⟩ = .ok none ↔
      MirSemantics.isAligned a offset.bytes.toNat k = true := by
  have h_req := (align_bytes_and_fromBytes_of_le_29 k hk_le).1
  have h_dist : offset.bytes - Size.ZERO.bytes = offset.bytes :=
    UInt64.sub_zero offset.bytes
  dsimp only [Miri.Interpreter.PointerMachine.symbolicAlignment,
    Option.getD, MirSemantics.isAligned]
  change
    (if a.alignLog2 < k then
       Except.ok (some (Misalignment.mk ⟨a.alignLog2⟩ ⟨k⟩))
     else
       Except.bind (Align.bytes ⟨k⟩) fun bytes =>
       if (HMod.hMod (offset.bytes - Size.ZERO.bytes) bytes == 0) = true then
         Except.ok none
       else
         Except.bind (Align.maxAlignedFactor
           (Size.ofBytes (offset.bytes - Size.ZERO.bytes))).bytes fun _ =>
           Except.ok (some (Misalignment.mk
             (Align.maxAlignedFactor
               (Size.ofBytes (offset.bytes - Size.ZERO.bytes))) ⟨k⟩))) =
      .ok none ↔
    (Nat.ble k a.alignLog2 &&
      Nat.beq (Nat.mod offset.bytes.toNat (Nat.pow 2 k)) 0) = true
  rw [h_req, h_dist]
  dsimp only [Except.bind]
  cases h_ble : Nat.ble k a.alignLog2 with
  | false =>
    have h_lt : a.alignLog2 < k := Nat.lt_of_not_le (fun h => by
      rw [(nat_ble_true_iff _ _).2 h] at h_ble; cases h_ble)
    rw [ite_pos_eq h_lt, Bool.false_and]
    constructor
    · intro h_ok
      cases h_ok
    · intro h_tr
      cases h_tr
  | true =>
    have h_kle : k ≤ a.alignLog2 := (nat_ble_true_iff _ _).1 h_ble
    have h_nlt : ¬ (a.alignLog2 < k) := Nat.not_lt.mpr h_kle
    rw [ite_neg_eq h_nlt, Bool.true_and]
    constructor
    · intro h_ok
      cases h_mod :
          (HMod.hMod offset.bytes (UInt64.ofNat (Nat.pow 2 k)) == 0) with
      | true =>
        have h_u0 : UInt64.mod offset.bytes (UInt64.ofNat (Nat.pow 2 k)) = 0 :=
          eq_of_beq h_mod
        have h_m0 : Nat.mod offset.bytes.toNat (Nat.pow 2 k) = 0 := by
          rw [← u64_mod_pow2_toNat offset.bytes k hk_le, h_u0]
          rfl
        exact (nat_beq_true_iff _ _).2 h_m0
      | false =>
        rw [h_mod, ite_false_eq] at h_ok
        cases h_ab :
            (Align.maxAlignedFactor (Size.ofBytes offset.bytes)).bytes with
        | error _ => rw [h_ab] at h_ok; cases h_ok
        | ok _ => rw [h_ab] at h_ok; cases h_ok
    · intro h_beq
      have h_m0 : Nat.mod offset.bytes.toNat (Nat.pow 2 k) = 0 :=
        (nat_beq_true_iff _ _).1 h_beq
      have h_u0 : UInt64.mod offset.bytes (UInt64.ofNat (Nat.pow 2 k)) = 0 :=
        u64_eq_of_toNat_eq
          ((u64_mod_pow2_toNat offset.bytes k hk_le).trans h_m0)
      change
        (if (UInt64.mod offset.bytes (UInt64.ofNat (Nat.pow 2 k)) == 0) = true
        then Except.ok none else _) = .ok none
      rw [h_u0]
      rfl

private theorem add_mod_pow2_of_aligned_base {base off aLog k : Nat}
    (hk_le : k ≤ aLog)
    (h_base : Nat.mod base (Nat.pow 2 aLog) = 0) :
    Nat.mod (base + off) (Nat.pow 2 k) = Nat.mod off (Nat.pow 2 k) := by
  have h_split : aLog = k + (aLog - k) := (Nat.add_sub_of_le hk_le).symm
  have h_base' : HMod.hMod base (Nat.pow 2 aLog) = 0 := h_base
  have h_div := (Nat.div_add_mod base (Nat.pow 2 aLog)).symm
  rw [h_base', Nat.add_zero] at h_div
  have h_pow : Nat.pow 2 aLog = Nat.pow 2 k * Nat.pow 2 (aLog - k) := by
    have h_p := Nat.pow_add 2 k (aLog - k)
    rw [← h_split] at h_p
    exact h_p
  rw [h_pow, Nat.mul_assoc] at h_div
  change HMod.hMod (base + off) (Nat.pow 2 k) = HMod.hMod off (Nat.pow 2 k)
  rw [h_div, Nat.mul_add_mod]

/-- Exact `↔` between `Miri.Memory.checkPtrAlign` on `Miri.Memory.Provenance`
with the `override` computed by `PointerMachine.symbolicAlignment true`
(matching `PointerPlaceMachine.misalignmentWith`'s `(fun _ _ _ _ _ => override)`
call) and `Trusted.MirSemantics.isAligned` whenever the allocation's base
address `baseAddr` is aligned to `2 ^ a.alignLog2` and
`ptr.offset.bytes.toNat = baseAddr + resolved.offset.bytes.toNat` (which holds
with `baseAddr = 0` under `Trusted.Correspondence.refResolvePointerPure`). -/
theorem checkPtrAlign_provenance_symbolic_ok_iff_mirIsAligned
    {ProvExtra : Type}
    (ptr : Miri.Memory.Pointer (Option Miri.Memory.Provenance))
    (a : MirSemantics.Allocation)
    (baseAddr k : Nat) (hk_le : k ≤ 29) (ha_le : a.alignLog2 ≤ 29)
    (resolve : PointerResolver Miri.Memory.Provenance ProvExtra)
    (lookup : Miri.Memory.AllocId → Except AllocationLookupError AllocationInfo)
    (resolved : ResolvedPointer ProvExtra)
    (info : AllocationInfo)
    (override : Option Misalignment)
    (h_res : resolve ptr 0 = .ok resolved)
    (h_lk : lookup resolved.allocId = .ok info)
    (h_kind : info.kind = .liveData)
    (h_align_eq : info.align = ⟨a.alignLog2⟩)
    (h_sym :
      Miri.Interpreter.PointerMachine.symbolicAlignment true info.kind
        info.align none resolved.offset ⟨k⟩ = .ok override)
    (h_base : Nat.mod baseAddr (Nat.pow 2 a.alignLog2) = 0)
    (h_addr : ptr.offset.bytes.toNat = baseAddr + resolved.offset.bytes.toNat) :
    checkPtrAlign ptr ⟨k⟩ true resolve lookup (fun _ _ _ _ _ => override) =
        .ok () ↔
      MirSemantics.isAligned a resolved.offset.bytes.toNat k = true := by
  rw [h_kind, h_align_eq] at h_sym
  have h_al : info.align.pow2 ≤ 29 := by rw [h_align_eq]; exact ha_le
  cases override with
  | none =>
    have h_is :
        MirSemantics.isAligned a resolved.offset.bytes.toNat k = true :=
      (symbolicAlignment_ok_none_iff_mirIsAligned
        a resolved.offset k hk_le).1 h_sym
    rw [h_is]
    have h_kle : k ≤ a.alignLog2 := by
      dsimp only [MirSemantics.isAligned] at h_is
      cases hb : Nat.ble k a.alignLog2 with
      | false => rw [hb] at h_is; cases h_is
      | true => exact (nat_ble_true_iff _ _).1 hb
    have h_rmod : Nat.mod resolved.offset.bytes.toNat (Nat.pow 2 k) = 0 := by
      dsimp only [MirSemantics.isAligned] at h_is
      rw [(nat_ble_true_iff _ _).2 h_kle, Bool.true_and] at h_is
      exact (nat_beq_true_iff _ _).1 h_is
    have h_pmod : Nat.mod ptr.offset.bytes.toNat (Nat.pow 2 k) = 0 := by
      rw [h_addr, add_mod_pow2_of_aligned_base h_kle h_base]
      exact h_rmod
    have h_ok :
        checkPtrAlign ptr ⟨k⟩ true resolve lookup (fun _ _ _ _ _ => none) =
          .ok () :=
      (checkPtrAlign_provenance_addr_ok_iff ptr k hk_le resolve lookup
        resolved info h_res h_lk h_al).2 h_pmod
    rw [h_ok]
    exact ⟨fun _ => rfl, fun _ => rfl⟩
  | some mis =>
    have h_nis :
        MirSemantics.isAligned a resolved.offset.bytes.toNat k = false := by
      cases hi : MirSemantics.isAligned a resolved.offset.bytes.toNat k with
      | false => rfl
      | true =>
        have h_none := (symbolicAlignment_ok_none_iff_mirIsAligned
          a resolved.offset k hk_le).2 hi
        rw [h_none] at h_sym
        cases h_sym
    rw [h_nis]
    cases k with
    | zero =>
      have h_z :
          MirSemantics.isAligned a resolved.offset.bytes.toNat 0 = true := by
        dsimp only [MirSemantics.isAligned]
        rw [(nat_ble_true_iff 0 a.alignLog2).2 (Nat.zero_le _), Bool.true_and]
        exact (nat_beq_true_iff _ _).2 (Nat.mod_one _)
      rw [h_z] at h_nis
      cases h_nis
    | succ k' =>
      have hk_pos : 0 < k' + 1 := Nat.succ_pos k'
      have h_req := align_bytes_and_fromBytes_of_le_29 (k' + 1) hk_le
      have h_err :
          checkPtrAlign ptr ⟨k' + 1⟩ true resolve lookup
              (fun _ _ _ _ _ => some mis) =
            .error (.alignmentCheckFailed mis) := by
        dsimp only [checkPtrAlign, bind, Bind.bind, Except.bind, pure,
          Pure.pure, Except.pure]
        rw [isPtrMisaligned_eq_someMirror]
        dsimp only [isPtrMisalignedSomeMirror]
        rw [accessCheckedAlignMirror_ok ⟨k' + 1⟩ hk_le]
        dsimp only [Except.bind]
        rw [h_req.1]
        dsimp only [Except.mapError, Except.bind]
        rw [pow2_u64_ne1 hk_pos hk_le]
        rw [show (!true || false) = false from rfl, ite_false_eq, h_res]
        dsimp only
        rw [h_lk]
        dsimp only [Except.bind]
        rw [accessCheckedAlignMirror_ok info.align h_al]
        rfl
      rw [h_err]
      exact ⟨fun h => (by cases h), fun h => (by cases h)⟩

/-- Relative-provenance (`CtfeProvenance`, `offsetIsAddr = false`)
characterization of `Miri.Memory.checkPtrAlign` against
`Trusted.MirSemantics.isAligned` for `0 < k ≤ 29` and `a.alignLog2 ≤ 29`. -/
theorem checkPtrAlign_ctfe_spec
    {ProvExtra : Type}
    (ptr : Miri.Memory.Pointer (Option CtfeProvenance))
    (a : MirSemantics.Allocation)
    (k : Nat) (hk_pos : 0 < k) (hk_le : k ≤ 29) (ha_le : a.alignLog2 ≤ 29)
    (resolve : PointerResolver CtfeProvenance ProvExtra)
    (lookup : Miri.Memory.AllocId → Except AllocationLookupError AllocationInfo)
    (resolved : ResolvedPointer ProvExtra)
    (info : AllocationInfo)
    (h_res : resolve ptr 0 = .ok resolved)
    (h_lk : lookup resolved.allocId = .ok info)
    (h_align_eq : info.align = ⟨a.alignLog2⟩) :
    (MirSemantics.isAligned a resolved.offset.bytes.toNat k = true →
      checkPtrAlign ptr ⟨k⟩ true resolve lookup (fun _ _ _ _ _ => none) =
        .ok ()) ∧
    (MirSemantics.isAligned a resolved.offset.bytes.toNat k = false →
      ∃ mis : Misalignment,
        checkPtrAlign ptr ⟨k⟩ true resolve lookup (fun _ _ _ _ _ => none) =
          .error (.alignmentCheckFailed mis)) := by
  have h_req := align_bytes_and_fromBytes_of_le_29 k hk_le
  have h_inf := align_bytes_and_fromBytes_of_le_29 a.alignLog2 ha_le
  have h_step :
      isPtrMisaligned ptr ⟨k⟩ true resolve lookup (fun _ _ _ _ _ => none) =
        if UInt64.ofNat (Nat.pow 2 a.alignLog2) <
            UInt64.ofNat (Nat.pow 2 k) then
          .ok (some ⟨⟨a.alignLog2⟩, ⟨k⟩⟩)
        else
          .ok
            (if (UInt64.mod resolved.offset.bytes
                  (UInt64.ofNat (Nat.pow 2 k)) == 0) = true then
              none
            else
              some ⟨Align.maxAlignedFactor resolved.offset, ⟨k⟩⟩) := by
    rw [isPtrMisaligned_eq_mirror]
    dsimp only [isPtrMisalignedMirror]
    rw [accessCheckedAlignMirror_ok ⟨k⟩ hk_le]
    dsimp only [Except.bind]
    rw [h_req.1]
    dsimp only [Except.mapError, Except.bind]
    rw [pow2_u64_ne1 hk_pos hk_le]
    rw [show (!true || false) = false from rfl, ite_false_eq, h_res]
    dsimp only
    rw [h_lk]
    dsimp only [Except.bind]
    rw [h_align_eq, accessCheckedAlignMirror_ok ⟨a.alignLog2⟩ ha_le]
    dsimp only [Except.bind, PointerProvenance.offsetIsAddr]
    rw [ite_false_eq, h_inf.1]
    dsimp only [Except.mapError, Except.bind]
    cases h_lt : decide
        (UInt64.ofNat (Nat.pow 2 a.alignLog2) < UInt64.ofNat (Nat.pow 2 k)) with
    | true =>
      have h_lt' := of_decide_eq_true h_lt
      rw [ite_pos_eq h_lt', ite_pos_eq h_lt']
    | false =>
      have h_nlt := of_decide_eq_false h_lt
      rw [ite_neg_eq h_nlt, ite_neg_eq h_nlt]
      exact accessOffsetMisalignmentMirror_eq resolved.offset k hk_le
  have h_pow_lt_iff :
      (UInt64.ofNat (Nat.pow 2 a.alignLog2) < UInt64.ofNat (Nat.pow 2 k)) ↔
        a.alignLog2 < k := by
    rw [UInt64.lt_iff_toNat_lt,
      u64_ofNat_toNat_of_lt (align_pow2_lt_pow64 ha_le),
      u64_ofNat_toNat_of_lt (align_pow2_lt_pow64 hk_le)]
    constructor
    · intro h_plt
      cases Nat.lt_or_ge a.alignLog2 k with
      | inl h => exact h
      | inr h =>
        exact False.elim
          (Nat.not_lt.mpr (Nat.pow_le_pow_right (by decide) h) h_plt)
    · intro h_lt
      exact Nat.pow_lt_pow_right (by decide) h_lt
  constructor
  · intro h_aligned
    dsimp only [MirSemantics.isAligned] at h_aligned
    cases h_ble : Nat.ble k a.alignLog2 with
    | false => rw [h_ble] at h_aligned; cases h_aligned
    | true =>
      rw [h_ble, Bool.true_and] at h_aligned
      have h_kle : k ≤ a.alignLog2 := (nat_ble_true_iff _ _).1 h_ble
      have h_mod0 : Nat.mod resolved.offset.bytes.toNat (Nat.pow 2 k) = 0 :=
        (nat_beq_true_iff _ _).1 h_aligned
      have h_nlt :
          ¬ (UInt64.ofNat (Nat.pow 2 a.alignLog2) <
              UInt64.ofNat (Nat.pow 2 k)) :=
        fun h => Nat.not_lt.mpr h_kle (h_pow_lt_iff.1 h)
      dsimp only [checkPtrAlign, bind, Bind.bind, Except.bind, pure, Pure.pure,
        Except.pure]
      rw [h_step, ite_neg_eq h_nlt]
      have h_um0 :
          UInt64.mod resolved.offset.bytes (UInt64.ofNat (Nat.pow 2 k)) = 0 :=
        u64_eq_of_toNat_eq
          ((u64_mod_pow2_toNat resolved.offset.bytes k hk_le).trans h_mod0)
      rw [h_um0]
      rfl
  · intro h_mis
    dsimp only [MirSemantics.isAligned] at h_mis
    dsimp only [checkPtrAlign, bind, Bind.bind, Except.bind, pure, Pure.pure,
      Except.pure]
    rw [h_step]
    cases h_ble : Nat.ble k a.alignLog2 with
    | false =>
      have h_lt : a.alignLog2 < k := Nat.lt_of_not_le (fun h => by
        rw [(nat_ble_true_iff _ _).2 h] at h_ble; cases h_ble)
      rw [ite_pos_eq (h_pow_lt_iff.2 h_lt)]
      exact ⟨⟨⟨a.alignLog2⟩, ⟨k⟩⟩, rfl⟩
    | true =>
      rw [h_ble, Bool.true_and] at h_mis
      have h_kle : k ≤ a.alignLog2 := (nat_ble_true_iff _ _).1 h_ble
      have h_nlt :
          ¬ (UInt64.ofNat (Nat.pow 2 a.alignLog2) <
              UInt64.ofNat (Nat.pow 2 k)) :=
        fun h => Nat.not_lt.mpr h_kle (h_pow_lt_iff.1 h)
      rw [ite_neg_eq h_nlt]
      have h_um_ne :
          (UInt64.mod resolved.offset.bytes (UInt64.ofNat (Nat.pow 2 k)) ==
              0) = false := by
        cases h_eq :
            (UInt64.mod resolved.offset.bytes (UInt64.ofNat (Nat.pow 2 k)) ==
              0) with
        | false => rfl
        | true =>
          have h_m : Nat.mod resolved.offset.bytes.toNat (Nat.pow 2 k) = 0 := by
            rw [← u64_mod_pow2_toNat resolved.offset.bytes k hk_le,
              eq_of_beq h_eq]
            rfl
          rw [(nat_beq_true_iff _ _).2 h_m] at h_mis
          cases h_mis
      rw [h_um_ne, ite_false_eq]
      exact ⟨⟨Align.maxAlignedFactor resolved.offset, ⟨k⟩⟩, rfl⟩

/-- Genuine bidirectional `↔` between `Miri.Memory.checkPtrAlign` on
`CtfeProvenance` and `Trusted.MirSemantics.isAligned` for all `k ≤ 29` and
`a.alignLog2 ≤ 29`. -/
theorem checkPtrAlign_ctfe_ok_iff_mirIsAligned
    {ProvExtra : Type}
    (ptr : Miri.Memory.Pointer (Option CtfeProvenance))
    (a : MirSemantics.Allocation)
    (k : Nat) (hk_le : k ≤ 29) (ha_le : a.alignLog2 ≤ 29)
    (resolve : PointerResolver CtfeProvenance ProvExtra)
    (lookup : Miri.Memory.AllocId → Except AllocationLookupError AllocationInfo)
    (resolved : ResolvedPointer ProvExtra)
    (info : AllocationInfo)
    (h_res : resolve ptr 0 = .ok resolved)
    (h_lk : lookup resolved.allocId = .ok info)
    (h_align_eq : info.align = ⟨a.alignLog2⟩) :
    checkPtrAlign ptr ⟨k⟩ true resolve lookup (fun _ _ _ _ _ => none) = .ok () ↔
      MirSemantics.isAligned a resolved.offset.bytes.toNat k = true := by
  cases k with
  | zero =>
    constructor
    · intro _
      dsimp only [MirSemantics.isAligned]
      rw [(nat_ble_true_iff 0 a.alignLog2).2 (Nat.zero_le _), Bool.true_and]
      exact (nat_beq_true_iff _ _).2 (Nat.mod_one _)
    · intro _
      exact checkPtrAlign_alignOne ptr true resolve lookup _
  | succ k' =>
    have h_sp := checkPtrAlign_ctfe_spec ptr a (k' + 1) (Nat.succ_pos k') hk_le
      ha_le resolve lookup resolved info h_res h_lk h_align_eq
    constructor
    · intro h_ok
      cases h_is : MirSemantics.isAligned a resolved.offset.bytes.toNat
          (k' + 1) with
      | true => rfl
      | false =>
        let ⟨_, h_err⟩ := h_sp.2 h_is
        rw [h_err] at h_ok
        cases h_ok
    · exact h_sp.1

/-! ## Section 3: `MirSemantics.MemoryState` Framing & Indirect Laws -/

/-- `findAllocation` after `replaceAllocation` for the same id finds the new
allocation whenever an entry with `a'.allocId` existed. -/
theorem findAllocation_replaceAllocation_eq (a' : MirSemantics.Allocation) :
    ∀ (allocs : List MirSemantics.Allocation) (old : MirSemantics.Allocation),
      findAllocation a'.allocId allocs = some old →
      findAllocation a'.allocId (replaceAllocation a' allocs) = some a'
  | [], _, h => by cases h
  | a :: rest, old, h => by
    dsimp only [findAllocation] at h
    dsimp only [replaceAllocation]
    cases h_eq : Nat.beq a.allocId a'.allocId with
    | true =>
      change
        (if Nat.beq a'.allocId a'.allocId then some a'
         else findAllocation a'.allocId rest) = some a'
      rw [(nat_beq_true_iff _ _).2 rfl]
      rfl
    | false =>
      rw [h_eq] at h
      change
        (if Nat.beq a.allocId a'.allocId then some a
         else findAllocation a'.allocId (replaceAllocation a' rest)) = some a'
      rw [h_eq]
      exact findAllocation_replaceAllocation_eq a' rest old h

/-- `findAllocation` after `replaceAllocation` for any distinct id
`id ≠ a'.allocId` is completely unchanged. -/
theorem findAllocation_replaceAllocation_ne (a' : MirSemantics.Allocation)
    (id : MirAst.AllocId) (h_ne : id ≠ a'.allocId) :
    ∀ (allocs : List MirSemantics.Allocation),
      findAllocation id (replaceAllocation a' allocs) =
        findAllocation id allocs
  | [] => rfl
  | a :: rest => by
    dsimp only [replaceAllocation, findAllocation]
    cases h_eq : Nat.beq a.allocId a'.allocId with
    | true =>
      have h_aid : a.allocId = a'.allocId := (nat_beq_true_iff _ _).1 h_eq
      have h_id_ne_a' : Nat.beq a'.allocId id = false := by
        cases h_b : Nat.beq a'.allocId id with
        | false => rfl
        | true => exact False.elim (h_ne ((nat_beq_true_iff _ _).1 h_b).symm)
      have h_id_ne_a : Nat.beq a.allocId id = false := by
        rw [h_aid]
        exact h_id_ne_a'
      change
        (if Nat.beq a'.allocId id then some a' else findAllocation id rest) =
        (if Nat.beq a.allocId id then some a else findAllocation id rest)
      rw [h_id_ne_a', h_id_ne_a]
      rfl
    | false =>
      change
        (if Nat.beq a.allocId id then some a
         else findAllocation id (replaceAllocation a' rest)) =
        (if Nat.beq a.allocId id then some a else findAllocation id rest)
      cases Nat.beq a.allocId id with
      | true => rfl
      | false => exact findAllocation_replaceAllocation_ne a' id h_ne rest

/-- Every element of `replaceAllocation a' allocs` is either `a'` or an element
of `allocs`. -/
theorem mem_replaceAllocation {a' b : MirSemantics.Allocation} :
    ∀ {allocs : List MirSemantics.Allocation},
      b ∈ replaceAllocation a' allocs → b = a' ∨ b ∈ allocs
  | [], h => by cases h
  | a :: rest, h => by
    dsimp only [replaceAllocation] at h
    cases h_eq : Nat.beq a.allocId a'.allocId with
    | true =>
      rw [h_eq, ite_true_eq] at h
      cases h with
      | head => exact Or.inl rfl
      | tail _ h_mem => exact Or.inr (List.Mem.tail a h_mem)
    | false =>
      rw [h_eq, ite_false_eq] at h
      cases h with
      | head => exact Or.inr (List.Mem.head rest)
      | tail _ h_mem =>
        cases mem_replaceAllocation h_mem with
        | inl h_a' => exact Or.inl h_a'
        | inr h_rest => exact Or.inr (List.Mem.tail a h_rest)

/-- `findAllocation` over `allocs ++ extra` returns the existing entry when
already present in `allocs`. -/
theorem findAllocation_append_some {id : MirAst.AllocId}
    {allocs extra : List MirSemantics.Allocation} {a : MirSemantics.Allocation}
    (h : findAllocation id allocs = some a) :
    findAllocation id (allocs ++ extra) = some a := by
  induction allocs with
  | nil => cases h
  | cons hd tl ih =>
    dsimp only [findAllocation] at h
    dsimp only [List.cons_append, findAllocation]
    cases h_eq : Nat.beq hd.allocId id with
    | true => rw [h_eq] at h; exact h
    | false => rw [h_eq] at h; exact ih h

/-- `findAllocation` on `allocs ++ [fresh]` finds `fresh` when `fresh.allocId`
is absent from `allocs`. -/
theorem findAllocation_append_fresh {allocs : List MirSemantics.Allocation}
    {fresh : MirSemantics.Allocation}
    (h_absent : findAllocation fresh.allocId allocs = none) :
    findAllocation fresh.allocId (allocs ++ [fresh]) = some fresh := by
  induction allocs with
  | nil =>
    dsimp only [List.nil_append, findAllocation]
    rw [(nat_beq_true_iff _ _).2 rfl]
    rfl
  | cons hd tl ih =>
    dsimp only [findAllocation] at h_absent
    dsimp only [List.cons_append, findAllocation]
    cases h_eq : Nat.beq hd.allocId fresh.allocId with
    | true => rw [h_eq] at h_absent; cases h_absent
    | false => rw [h_eq] at h_absent; exact ih h_absent

/-- Direct list-membership freshness predicate for `MemoryState`
allocations (`∀ a ∈ m.allocations, a.allocId < m.nextAllocId`). -/
def MemoryAllIdsLt (m : MirSemantics.MemoryState) : Prop :=
  ∀ a : MirSemantics.Allocation, a ∈ m.allocations → a.allocId < m.nextAllocId

/-- `replaceAllocation` preserves `MemoryAllIdsLt` whenever `a'.allocId <
m.nextAllocId`. -/
theorem memoryAllIdsLt_replaceAllocation {m : MirSemantics.MemoryState}
    {a' : MirSemantics.Allocation}
    (h_fresh : MemoryAllIdsLt m)
    (h_lt : a'.allocId < m.nextAllocId) :
    MemoryAllIdsLt { m with allocations := replaceAllocation a' m.allocations }
    := by
  intro b h_mem
  cases mem_replaceAllocation h_mem with
  | inl h_eq => rw [h_eq]; exact h_lt
  | inr h_old => exact h_fresh b h_old

theorem findAllocation_mem {id : MirAst.AllocId}
    {allocs : List MirSemantics.Allocation} {a : MirSemantics.Allocation}
    (h : findAllocation id allocs = some a) :
    a ∈ allocs ∧ a.allocId = id := by
  induction allocs with
  | nil => cases h
  | cons hd tl ih =>
    dsimp only [findAllocation] at h
    cases h_eq : Nat.beq hd.allocId id with
    | true =>
      rw [h_eq] at h
      injection h with h_a
      subst h_a
      exact ⟨List.Mem.head tl, (nat_beq_true_iff _ _).1 h_eq⟩
    | false =>
      rw [h_eq] at h
      let ⟨h_mem, h_id⟩ := ih h
      exact ⟨List.Mem.tail hd h_mem, h_id⟩

theorem findAllocation_none_of_allIdsLt {m : MirSemantics.MemoryState}
    (h_fresh : MemoryAllIdsLt m) {id : MirAst.AllocId}
    (h_ge : m.nextAllocId ≤ id) :
    findAllocation id m.allocations = none := by
  cases h_f : findAllocation id m.allocations with
  | none => rfl
  | some a =>
    let ⟨h_mem, h_id⟩ := findAllocation_mem h_f
    have h_lt := h_fresh a h_mem
    rw [h_id] at h_lt
    exact False.elim (Nat.not_lt.mpr h_ge h_lt)

/-- `allocateStack` creates a fresh live mutable uninitialized allocation at
`m.nextAllocId`, preserves `MemoryAllIdsLt`, and preserves `findAllocation` for
every pre-existing allocation. -/
theorem allocateStack_spec (m : MirSemantics.MemoryState)
    (layout : MirSemantics.LayoutData) (h_fresh : MemoryAllIdsLt m) :
    let res := allocateStack m layout
    res.2 = ⟨m.nextAllocId, 0⟩ ∧
    res.1.nextAllocId = m.nextAllocId + 1 ∧
    MemoryAllIdsLt res.1 ∧
    findAllocation m.nextAllocId res.1.allocations = some {
      allocId := m.nextAllocId
      alignLog2 := layout.alignLog2
      mutability := .mut
      bytes := List.replicate layout.size .uninit
      live := true
    } ∧
    (∀ (id : MirAst.AllocId) a, findAllocation id m.allocations = some a →
      findAllocation id res.1.allocations = some a) := by
  dsimp only [allocateStack, MirSemantics.MemoryState.reserveAllocId]
  refine ⟨rfl, rfl, ?_, ?_, ?_⟩
  · intro a h_mem
    cases List.mem_append.1 h_mem with
    | inl h_old => exact Nat.lt_succ_of_lt (h_fresh a h_old)
    | inr h_new =>
      cases h_new with
      | head => exact Nat.lt_succ_self m.nextAllocId
      | tail _ h_nil => cases h_nil
  · exact findAllocation_append_fresh
      (fresh := {
        allocId := m.nextAllocId
        alignLog2 := layout.alignLog2
        mutability := .mut
        bytes := List.replicate layout.size .uninit
        live := true
      })
      (findAllocation_none_of_allIdsLt (m := m) h_fresh
        (Nat.le_refl m.nextAllocId))
  · intro id a h_old
    exact findAllocation_append_some h_old

/-- Helper eliminating a successful `writeBytes` call into either empty `bs`
(`m' = m`, with an existing allocation record aligned at `place`) or a
concrete updated allocation in `m.allocations`. -/
private theorem writeBytes_ok_elim {m m' : MirSemantics.MemoryState}
    {place : MemPlace} {alignLog2 : Nat} {bs : List AllocByte}
    (h_w : writeBytes m place alignLog2 bs = .ok m') :
    (bs = [] ∧ m' = m ∧
      ∃ a : MirSemantics.Allocation,
        findAllocation place.allocId m.allocations = some a ∧
        isAligned a place.offset alignLog2 = true) ∨
    ∃ a : MirSemantics.Allocation,
      bs ≠ [] ∧
      findAllocation place.allocId m.allocations = some a ∧
      a.live = true ∧
      isInBounds a place.offset bs.length = true ∧
      isAligned a place.offset alignLog2 = true ∧
      a.mutability = .mut ∧
      m' = { m with
        allocations := replaceAllocation
          { a with
            bytes := a.bytes.take place.offset ++ bs ++
              a.bytes.drop (place.offset + bs.length) }
          m.allocations } := by
  dsimp only [writeBytes] at h_w
  cases h_fa : findAllocation place.allocId m.allocations with
  | none => rw [h_fa] at h_w; dsimp only at h_w; cases h_w
  | some a =>
    rw [h_fa] at h_w
    dsimp only at h_w
    cases h_len0 : Nat.beq bs.length 0 with
    | true =>
      rw [h_len0] at h_w
      cases h_al0 : isAligned a place.offset alignLog2 with
      | false => rw [h_al0] at h_w; cases h_w
      | true =>
        rw [h_al0] at h_w
        injection h_w with h_m'
        exact Or.inl
          ⟨List.eq_nil_of_length_eq_zero ((nat_beq_true_iff _ _).1 h_len0),
            h_m'.symm, a, rfl, h_al0⟩
    | false =>
      rw [h_len0] at h_w
      have h_ne : bs ≠ [] := fun h => by rw [h] at h_len0; cases h_len0
      cases h_live : a.live with
      | false => rw [h_live] at h_w; cases h_w
      | true =>
        cases h_ib : isInBounds a place.offset bs.length with
        | false => rw [h_live, h_ib] at h_w; cases h_w
        | true =>
          cases h_al : isAligned a place.offset alignLog2 with
          | false => rw [h_live, h_ib, h_al] at h_w; cases h_w
          | true =>
            rw [h_live, h_ib, h_al] at h_w
            cases h_mut : a.mutability with
            | shared => rw [h_mut] at h_w; dsimp only at h_w; cases h_w
            | _ =>
              rw [h_mut] at h_w
              dsimp only at h_w
              injection h_w with h_m'
              rw [← h_mut, ← h_live] at h_m'
              exact Or.inr ⟨a, h_ne, rfl, h_live, h_ib, h_al, h_mut, h_m'.symm⟩

/-- `writeBytes` preserves `MemoryAllIdsLt` and leaves `nextAllocId` unchanged.
-/
theorem memoryAllIdsLt_writeBytes {m m' : MirSemantics.MemoryState}
    {place : MemPlace} {alignLog2 : Nat} {bs : List AllocByte}
    (h_fresh : MemoryAllIdsLt m)
    (h_w : writeBytes m place alignLog2 bs = .ok m') :
    MemoryAllIdsLt m' ∧ m'.nextAllocId = m.nextAllocId := by
  cases writeBytes_ok_elim h_w with
  | inl h =>
    rw [h.2.1]
    exact ⟨h_fresh, rfl⟩
  | inr h =>
    let ⟨a, _, h_fa, _, _, _, _, h_m'⟩ := h
    subst h_m'
    let ⟨h_mem, _⟩ := findAllocation_mem h_fa
    exact ⟨memoryAllIdsLt_replaceAllocation h_fresh (h_fresh a h_mem), rfl⟩

/-- Writing `bs` to `place` and reading `bs.length` bytes back at `place`
recovers `bs` verbatim. -/
theorem readBytes_after_writeBytes_self (m m' : MirSemantics.MemoryState)
    (place : MemPlace) (alignLog2 : Nat) (bs : List AllocByte)
    (h_w : writeBytes m place alignLog2 bs = .ok m') :
    readBytes m' place bs.length alignLog2 = .ok bs := by
  cases writeBytes_ok_elim h_w with
  | inl h =>
    let ⟨h_nil, h_m', a, h_fa, h_al⟩ := h
    subst h_nil
    rw [h_m']
    exact readBytes_zero_size m place alignLog2 a h_fa h_al
  | inr h =>
    let ⟨a, h_ne, h_fa, h_live, h_ib, h_al, _, h_m'⟩ := h
    subst h_m'
    have h_l0 : Nat.beq bs.length 0 = false := by
      cases bs with
      | nil => exact False.elim (h_ne rfl)
      | cons _ _ => rfl
    let a' : MirSemantics.Allocation := {
      a with
      bytes := a.bytes.take place.offset ++ bs ++
        a.bytes.drop (place.offset + bs.length)
    }
    have h_aid : a'.allocId = place.allocId := (findAllocation_mem h_fa).2
    have h_fa' :
        findAllocation place.allocId (replaceAllocation a' m.allocations) =
          some a' := by
      rw [← h_aid]
      exact findAllocation_replaceAllocation_eq a' m.allocations a
        (by rw [h_aid]; exact h_fa)
    dsimp only [readBytes]
    rw [h_fa']
    dsimp only
    rw [h_l0]
    have h_in : place.offset + bs.length ≤ a.bytes.length :=
      (nat_ble_true_iff _ _).1 h_ib
    have h_ib' : isInBounds a' place.offset bs.length = true := by
      dsimp only [isInBounds]
      rw [list_write_length a.bytes bs place.offset h_in]
      exact h_ib
    have h_live' : a'.live = true := h_live
    have h_al' : isAligned a' place.offset alignLog2 = true := h_al
    change
      (if (!a'.live || !isInBounds a' place.offset bs.length ||
          !isAligned a' place.offset alignLog2) = true then
        Except.error FaultKind.undefined
       else Except.ok ((a'.bytes.drop place.offset).take bs.length)) =
      Except.ok bs
    rw [h_live', h_ib', h_al']
    dsimp only [a']
    rw [list_read_after_write a.bytes bs place.offset h_in]
    rfl

/-- Disjoint intra-allocation frame preservation: writing `bs` at `place1`
preserves `readBytes` at any disjoint subrange `[off2, off2 + sz2)` within the
same allocation. -/
theorem readBytes_after_writeBytes_disjoint_offset
    (m m' : MirSemantics.MemoryState) (allocId : MirAst.AllocId)
    (off1 align1 off2 sz2 align2 : Nat) (bs : List AllocByte)
    (h_w : writeBytes m ⟨allocId, off1⟩ align1 bs = .ok m')
    (h_disj : off1 + bs.length ≤ off2 ∨ off2 + sz2 ≤ off1) :
    readBytes m' ⟨allocId, off2⟩ sz2 align2 =
      readBytes m ⟨allocId, off2⟩ sz2 align2 := by
  cases writeBytes_ok_elim h_w with
  | inl h => rw [h.2.1]
  | inr h =>
    let ⟨a, _, h_fa, _, h_ib, _, _, h_m'⟩ := h
    subst h_m'
    let a' : MirSemantics.Allocation := {
      a with
      bytes := a.bytes.take off1 ++ bs ++ a.bytes.drop (off1 + bs.length)
    }
    have h_aid : a'.allocId = allocId := (findAllocation_mem h_fa).2
    have h_fa' :
        findAllocation allocId (replaceAllocation a' m.allocations) =
          some a' := by
      rw [← h_aid]
      exact findAllocation_replaceAllocation_eq a' m.allocations a
        (by rw [h_aid]; exact h_fa)
    dsimp only [readBytes]
    rw [h_fa', h_fa]
    dsimp only
    cases Nat.beq sz2 0 with
    | true => rfl
    | false =>
      have h_in1 : off1 + bs.length ≤ a.bytes.length :=
        (nat_ble_true_iff _ _).1 h_ib
      have h_off1_le : off1 ≤ a.bytes.length :=
        Nat.le_trans (Nat.le_add_right off1 bs.length) h_in1
      have h_ib2 : isInBounds a' off2 sz2 = isInBounds a off2 sz2 := by
        dsimp only [isInBounds]
        rw [list_write_length a.bytes bs off1 h_in1]
      have h_al2 : isAligned a' off2 align2 = isAligned a off2 align2 := rfl
      have h_live' : a'.live = a.live := rfl
      change
        (if (!a'.live || !isInBounds a' off2 sz2 ||
            !isAligned a' off2 align2) = true then
          Except.error FaultKind.undefined
         else Except.ok ((a'.bytes.drop off2).take sz2)) =
        (if (!a.live || !isInBounds a off2 sz2 ||
            !isAligned a off2 align2) = true then
          Except.error FaultKind.undefined
         else Except.ok ((a.bytes.drop off2).take sz2))
      rw [h_live', h_ib2, h_al2]
      cases (!a.live || !isInBounds a off2 sz2 || !isAligned a off2 align2) with
      | true => rfl
      | false =>
        dsimp only [a']
        cases h_disj with
        | inl h_r =>
          rw [list_read_after_write_right a.bytes bs off1 off2 sz2 h_in1 h_r]
        | inr h_l =>
          rw [list_read_after_write_left_inbounds
            a.bytes bs off1 off2 sz2 h_off1_le h_l]

/-- Disjoint inter-allocation frame preservation: `writeBytes` to `place1`
preserves `findAllocation` and `readBytes` on every distinct allocation
`id2 ≠ place1.allocId`. -/
theorem writeBytes_preserves_other_alloc (m m' : MirSemantics.MemoryState)
    (place1 : MemPlace) (align1 : Nat) (bs : List AllocByte)
    (h_w : writeBytes m place1 align1 bs = .ok m')
    (id2 : MirAst.AllocId) (h_ne : id2 ≠ place1.allocId) :
    findAllocation id2 m'.allocations = findAllocation id2 m.allocations ∧
    ∀ (off2 sz2 align2 : Nat),
      readBytes m' ⟨id2, off2⟩ sz2 align2 =
        readBytes m ⟨id2, off2⟩ sz2 align2 := by
  have h_find :
      findAllocation id2 m'.allocations = findAllocation id2 m.allocations := by
    cases writeBytes_ok_elim h_w with
    | inl h => rw [h.2.1]
    | inr h =>
      let ⟨a, _, h_fa, _, _, _, _, h_m'⟩ := h
      subst h_m'
      have h_aid : a.allocId = place1.allocId := (findAllocation_mem h_fa).2
      exact findAllocation_replaceAllocation_ne _ id2
        (by rw [h_aid]; exact h_ne) m.allocations
  refine ⟨h_find, fun off2 sz2 align2 => ?_⟩
  dsimp only [readBytes]
  rw [h_find]

/-- Non-empty `writeBytes` to a `.shared` allocation faults with `.undefined`.
-/
theorem writeBytes_shared_fault (m : MirSemantics.MemoryState)
    (place : MemPlace) (alignLog2 : Nat) (bs : List AllocByte)
    (a : MirSemantics.Allocation)
    (h_ne : bs ≠ [])
    (h_fa : findAllocation place.allocId m.allocations = some a)
    (h_sh : a.mutability = .shared) :
    writeBytes m place alignLog2 bs = .error .undefined := by
  dsimp only [writeBytes]
  rw [h_fa]
  dsimp only
  cases bs with
  | nil => exact False.elim (h_ne rfl)
  | cons b rest =>
    dsimp only [List.length, Nat.beq]
    change
      (if (!a.live || !isInBounds a place.offset (rest.length + 1) ||
          !isAligned a place.offset alignLog2) = true then
        Except.error FaultKind.undefined
       else match a.mutability with
         | .shared => Except.error FaultKind.undefined
         | .mut => _) = _
    cases (!a.live || !isInBounds a place.offset (rest.length + 1) ||
        !isAligned a place.offset alignLog2) with
    | true => rfl
    | false => rw [h_sh]; rfl

/-- `deallocateStack` marks `place.allocId` dead (so subsequent non-empty
reads/writes/deallocations fault with `.undefined`) while preserving every
distinct allocation `id2 ≠ place.allocId`. -/
theorem deallocateStack_spec (m m' : MirSemantics.MemoryState)
    (place : MemPlace)
    (h_d : deallocateStack m place = .ok m') :
    place.offset = 0 ∧
    (∀ (off sz al : Nat), 0 < sz →
      readBytes m' ⟨place.allocId, off⟩ sz al = .error .undefined) ∧
    (∀ (off al : Nat) (bs : List AllocByte), bs ≠ [] →
      writeBytes m' ⟨place.allocId, off⟩ al bs = .error .undefined) ∧
    deallocateStack m' place = .error .undefined ∧
    (∀ id2, id2 ≠ place.allocId →
      findAllocation id2 m'.allocations =
        findAllocation id2 m.allocations) := by
  dsimp only [deallocateStack] at h_d
  cases h_off0 : Nat.beq place.offset 0 with
  | false => rw [h_off0] at h_d; cases h_d
  | true =>
    rw [h_off0] at h_d
    have h_off : place.offset = 0 := (nat_beq_true_iff _ _).1 h_off0
    cases h_fa : findAllocation place.allocId m.allocations with
    | none => rw [h_fa] at h_d; dsimp only at h_d; cases h_d
    | some a =>
      rw [h_fa] at h_d
      dsimp only at h_d
      cases h_live : a.live with
      | false => rw [h_live] at h_d; cases h_d
      | true =>
        rw [h_live] at h_d
        cases h_mut : a.mutability with
        | shared => rw [h_mut] at h_d; dsimp only at h_d; cases h_d
        | _ =>
          rw [h_mut] at h_d
          dsimp only at h_d
          injection h_d with h_m'
          rw [← h_mut] at h_m'
          subst h_m'
          have h_aid : a.allocId = place.allocId := (findAllocation_mem h_fa).2
          have h_dead : findAllocation place.allocId
              (replaceAllocation { a with live := false } m.allocations) =
                some { a with live := false } := by
            rw [← h_aid]
            exact findAllocation_replaceAllocation_eq { a with live := false }
              m.allocations a (by rw [h_aid]; exact h_fa)
          refine ⟨h_off, ?_, ?_, ?_, ?_⟩
          · intro off sz al h_pos
            cases sz with
            | zero => exact False.elim (Nat.lt_irrefl 0 h_pos)
            | succ k =>
              dsimp only [readBytes]
              rw [h_dead]
              rfl
          · intro off al bs h_ne
            cases bs with
            | nil => exact False.elim (h_ne rfl)
            | cons b rest =>
              dsimp only [writeBytes]
              rw [h_dead]
              rfl
          · dsimp only [deallocateStack]; rw [h_off0, h_dead]; rfl
          · intro id2 h_ne
            exact findAllocation_replaceAllocation_ne _ id2
              (by rw [h_aid]; exact h_ne) m.allocations

/-- `deallocateStack` preserves `MemoryAllIdsLt` and leaves `nextAllocId`
unchanged. -/
theorem memoryAllIdsLt_deallocateStack {m m' : MirSemantics.MemoryState}
    {place : MemPlace}
    (h_fresh : MemoryAllIdsLt m)
    (h_d : deallocateStack m place = .ok m') :
    MemoryAllIdsLt m' ∧ m'.nextAllocId = m.nextAllocId := by
  dsimp only [deallocateStack] at h_d
  cases h_off0 : Nat.beq place.offset 0 with
  | false => rw [h_off0] at h_d; cases h_d
  | true =>
    rw [h_off0] at h_d
    cases h_fa : findAllocation place.allocId m.allocations with
    | none => rw [h_fa] at h_d; dsimp only at h_d; cases h_d
    | some a =>
      rw [h_fa] at h_d
      dsimp only at h_d
      cases h_live : a.live with
      | false => rw [h_live] at h_d; cases h_d
      | true =>
        rw [h_live] at h_d
        cases h_mut : a.mutability with
        | shared => rw [h_mut] at h_d; dsimp only at h_d; cases h_d
        | _ =>
          rw [h_mut] at h_d
          dsimp only at h_d
          injection h_d with h_m'
          rw [← h_mut] at h_m'
          subst h_m'
          let ⟨h_mem, _⟩ := findAllocation_mem h_fa
          exact
            ⟨memoryAllIdsLt_replaceAllocation h_fresh (h_fresh a h_mem), rfl⟩

/-- `encodeUInt` produces exactly `n` bytes in both little- and big-endian. -/
theorem encodeUInt_length (endian : TargetEndian) (n x : Nat) :
    (encodeUInt endian n x).length = n := by
  cases endian with
  | little => exact leBytesOfNat_length n x
  | big =>
    dsimp only [encodeUInt]
    rw [List.length_reverse]
    exact leBytesOfNat_length n x

/-- `decodeUInt` is a left inverse to `encodeUInt` modulo `256 ^ n` in both
little-endian and big-endian byte orders. -/
theorem decodeUInt_encodeUInt (endian : TargetEndian) (n x : Nat) :
    decodeUInt endian (encodeUInt endian n x) = Nat.mod x (Nat.pow 256 n) := by
  cases endian with
  | little => exact natOfLeBytes_leBytesOfNat n x
  | big =>
    dsimp only [decodeUInt, encodeUInt]
    rw [List.reverse_reverse]
    exact natOfLeBytes_leBytesOfNat n x

/-- `encodeVal` followed by `decodeVal` recovers the original scalar value for
every integer width, signedness, and endianness. -/
theorem decodeVal_encodeVal_int (endian : TargetEndian) (w : IntWidth)
    (s : Bool) (bits : BitVec 128) :
    let v := Val.scalar ⟨w, s, truncateBits w bits⟩
    ∃ bs : List AllocByte,
      encodeVal endian (.int w s) v = .ok bs ∧
      bs.length = (intLayout w).size ∧
      decodeVal endian (.int w s) bs = .ok (some v) := by
  intro v
  have h_wf : (ScalarVal.mk w s (truncateBits w bits)).wf = true := by
    dsimp only [ScalarVal.wf]
    rw [truncateBits_idem]
    exact beq_self_eq_true _
  have h_cv : checkVal v (.int w s) = true := by
    dsimp only [v, checkVal, Val.ty?]
    rw [h_wf, mem_ite_true_eq]
    dsimp only [MirTy.beq]
    rw [IntWidth.beq_refl, beq_self_eq_true]
    rfl
  let raw := encodeUInt endian w.byteSize (truncateBits w bits).toNat
  refine ⟨raw.map (fun b => AllocByte.init b none), ?_, ?_, ?_⟩
  · dsimp only [encodeVal, v]
    rw [h_cv]
    rfl
  · rw [List.length_map, encodeUInt_length]
    exact (intLayout_props w).2.1.symm
  · dsimp only [decodeVal, layoutOfTy]
    have h_len :
        (raw.map (fun b => AllocByte.init b none)).length =
          (intLayout w).size := by
      rw [List.length_map, encodeUInt_length]
      exact (intLayout_props w).2.1.symm
    rw [h_len, (nat_beq_true_iff _ _).2 rfl]
    have h_sz_ne0 : Nat.beq (intLayout w).size 0 = false := by
      cases w <;> rfl
    rw [h_sz_ne0]
    change
      (match initBytes? (raw.map (fun b => AllocByte.init b none)) with
       | none => Except.ok none
       | some raw' =>
         match evalConstLit (.int w s)
             (.scalar (BitVec.ofNat 128 (decodeUInt endian raw'))) with
         | Except.ok v' => Except.ok (some v')
         | Except.error k => Except.error k) = Except.ok (some v)
    rw [initBytes?_map_init]
    dsimp only [raw]
    rw [decodeUInt_encodeUInt]
    have h_mod :
        Nat.mod (truncateBits w bits).toNat (Nat.pow 256 w.byteSize) =
          (truncateBits w bits).toNat := by
      apply Nat.mod_eq_of_lt
      have h_pow : Nat.pow 2 w.bitWidth = Nat.pow 256 w.byteSize := by
        cases w <;> rfl
      rw [toNat_truncateBits, ← h_pow]
      exact Nat.mod_lt _ (intWidth_modulus_pos w)
    rw [h_mod, bitVec128_ofNat_toNat]
    dsimp only [evalConstLit]
    rw [truncateBits_idem, bne_self_eq_false]
    rfl

/-- Typed indirect store-then-load round-trip for every integer type:
`storeIndirect` followed by `loadIndirect` at the same place recovers
`.ok (some v)`. -/
theorem storeIndirect_loadIndirect_int (m m' : MirSemantics.MemoryState)
    (place : MemPlace) (w : IntWidth) (s : Bool) (bits : BitVec 128)
    (h_st : storeIndirect m (.int w s) place
      (.scalar ⟨w, s, truncateBits w bits⟩) = .ok m') :
    loadIndirect m' (.int w s) place =
      .ok (some (.scalar ⟨w, s, truncateBits w bits⟩)) := by
  let ⟨bs, h_enc, h_len, h_dec⟩ :=
    decodeVal_encodeVal_int profileTargetEndian w s bits
  dsimp only [storeIndirect, layoutOfTy] at h_st
  rw [h_enc] at h_st
  dsimp only at h_st
  dsimp only [loadIndirect, layoutOfTy]
  have h_rd := readBytes_after_writeBytes_self m m' place
    (intLayout w).alignLog2 bs h_st
  rw [h_len] at h_rd
  rw [h_rd]
  exact h_dec

/-- `deinitIndirect` followed by `loadIndirect` on any integer type returns
`.ok none` (uninitialized). -/
theorem deinitIndirect_loadIndirect_int (m m' : MirSemantics.MemoryState)
    (place : MemPlace) (w : IntWidth) (s : Bool)
    (h_di : deinitIndirect m (.int w s) place = .ok m') :
    loadIndirect m' (.int w s) place = .ok none := by
  dsimp only [deinitIndirect, layoutOfTy, writeUninit] at h_di
  have h_rd := readBytes_after_writeBytes_self m m' place
    (intLayout w).alignLog2 (List.replicate (intLayout w).size .uninit) h_di
  rw [List.length_replicate] at h_rd
  dsimp only [loadIndirect, layoutOfTy]
  rw [h_rd]
  dsimp only [decodeVal, layoutOfTy]
  rw [List.length_replicate, (nat_beq_true_iff _ _).2 rfl]
  have h_sz_ne0 : Nat.beq (intLayout w).size 0 = false := by cases w <;> rfl
  rw [h_sz_ne0]
  cases w <;> rfl

/-! ## Section 8: Profile v2 Memory, Pointer/Slice, Non-Escalation, and Return
Invariants -/

private theorem nat_blt_zero_false_eq_zero {n : Nat}
    (h : Nat.blt 0 n = false) : n = 0 := by
  cases n with
  | zero => rfl
  | succ k =>
    have h_true : Nat.blt 0 (Nat.succ k) = true :=
      (nat_ble_true_iff 1 (Nat.succ k)).2 (Nat.succ_le_succ (Nat.zero_le k))
    rw [h_true] at h
    cases h

private theorem nat_blt_true_lt {a b : Nat} (h : Nat.blt a b = true) :
    a < b :=
  (nat_ble_true_iff (a + 1) b).1 h

private theorem nat_beq_false_ne {a b : Nat} (h : Nat.beq a b = false) :
    a ≠ b := by
  intro h_eq
  rw [h_eq] at h
  have h_true : Nat.beq b b = true := (nat_beq_true_iff b b).2 rfl
  rw [h_true] at h
  cases h

/-- Any successful `readBytes` call resolves `place.allocId` and passes
`isAligned`—even at `size = 0`—while `0 < size` additionally requires `a.live`
and `isInBounds`. -/
theorem readBytes_requires_alloc_and_alignment (m : MirSemantics.MemoryState)
    (place : MemPlace) (size alignLog2 : Nat) (bs : List AllocByte)
    (h_r : readBytes m place size alignLog2 = .ok bs) :
    ∃ a : MirSemantics.Allocation,
      findAllocation place.allocId m.allocations = some a ∧
      isAligned a place.offset alignLog2 = true ∧
      (size = 0 → bs = []) ∧
      (0 < size →
        a.live = true ∧
        isInBounds a place.offset size = true ∧
        bs = (a.bytes.drop place.offset).take size) := by
  dsimp only [readBytes] at h_r
  cases h_fa : findAllocation place.allocId m.allocations with
  | none => rw [h_fa] at h_r; dsimp only at h_r; cases h_r
  | some a =>
    rw [h_fa] at h_r
    dsimp only at h_r
    cases h_sz0 : Nat.beq size 0 with
    | true =>
      rw [h_sz0] at h_r
      cases h_al : isAligned a place.offset alignLog2 with
      | false => rw [h_al] at h_r; cases h_r
      | true =>
        rw [h_al] at h_r
        injection h_r with h_bs
        have h_sz_eq : size = 0 := (nat_beq_true_iff size 0).1 h_sz0
        refine ⟨a, rfl, h_al, fun _ => h_bs.symm, fun h_pos => ?_⟩
        rw [h_sz_eq] at h_pos
        exact False.elim (Nat.not_lt_zero 0 h_pos)
    | false =>
      rw [h_sz0] at h_r
      have h_ne0 : size ≠ 0 := nat_beq_false_ne h_sz0
      cases h_live : a.live with
      | false => rw [h_live] at h_r; cases h_r
      | true =>
        cases h_ib : isInBounds a place.offset size with
        | false => rw [h_live, h_ib] at h_r; cases h_r
        | true =>
          cases h_al : isAligned a place.offset alignLog2 with
          | false => rw [h_live, h_ib, h_al] at h_r; cases h_r
          | true =>
            rw [h_live, h_ib, h_al] at h_r
            injection h_r with h_bs
            refine ⟨a, rfl, h_al, fun hz => False.elim (h_ne0 hz),
              fun _ => ⟨h_live, h_ib, h_bs.symm⟩⟩

/-- Any successful `writeBytes` call resolves `place.allocId` and passes
`isAligned`—even when `bs = []`—while non-empty `bs` additionally requires
`a.live`, `isInBounds`, and `a.mutability = .mut`. -/
theorem writeBytes_requires_alloc_and_alignment
    (m m' : MirSemantics.MemoryState)
    (place : MemPlace) (alignLog2 : Nat) (bs : List AllocByte)
    (h_w : writeBytes m place alignLog2 bs = .ok m') :
    ∃ a : MirSemantics.Allocation,
      findAllocation place.allocId m.allocations = some a ∧
      isAligned a place.offset alignLog2 = true ∧
      (bs = [] → m' = m) ∧
      (bs ≠ [] →
        a.live = true ∧
        isInBounds a place.offset bs.length = true ∧
        a.mutability = .mut) := by
  cases writeBytes_ok_elim h_w with
  | inl h =>
    let ⟨h_nil, h_meq, a, h_fa, h_al⟩ := h
    exact ⟨a, h_fa, h_al, fun _ => h_meq, fun h_ne => False.elim (h_ne h_nil)⟩
  | inr h =>
    let ⟨a, h_ne, h_fa, h_live, h_ib, h_al, h_mut, _⟩ := h
    exact ⟨a, h_fa, h_al, fun h_nil => False.elim (h_ne h_nil),
      fun _ => ⟨h_live, h_ib, h_mut⟩⟩

/-- `writeUninit` inherits `writeBytes`'s allocation and alignment preconditions
for all sizes, leaves memory unchanged at `size = 0`, and requires liveness,
bounds, and `.mut` mutability when `0 < size`. -/
theorem writeUninit_requires_alloc_and_alignment
    (m m' : MirSemantics.MemoryState)
    (place : MemPlace) (size alignLog2 : Nat)
    (h_w : writeUninit m place size alignLog2 = .ok m') :
    ∃ a : MirSemantics.Allocation,
      findAllocation place.allocId m.allocations = some a ∧
      isAligned a place.offset alignLog2 = true ∧
      (size = 0 → m' = m) ∧
      (0 < size →
        a.live = true ∧
        isInBounds a place.offset size = true ∧
        a.mutability = .mut) := by
  dsimp only [writeUninit] at h_w
  let ⟨a, h_fa, h_al, h_nil, h_pos⟩ :=
    writeBytes_requires_alloc_and_alignment m m' place alignLog2
      (List.replicate size AllocByte.uninit) h_w
  refine ⟨a, h_fa, h_al, ?_, ?_⟩
  · intro h_sz
    apply h_nil
    rw [h_sz]
    rfl
  · intro h_gt
    have h_ne : List.replicate size AllocByte.uninit ≠ [] := by
      intro h_eq
      have h_len := congrArg List.length h_eq
      rw [List.length_replicate] at h_len
      rw [h_len] at h_gt
      exact Nat.not_lt_zero 0 h_gt
    let ⟨h_live, h_ib, h_mut⟩ := h_pos h_ne
    rw [List.length_replicate] at h_ib
    exact ⟨h_live, h_ib, h_mut⟩

/-- Any successful `loadIndirectV2` resolves a Profile v2 layout and an aligned
allocation record in `m`, even for zero-sized types. -/
theorem loadIndirectV2_requires_alloc_and_alignment
    (m : MirSemantics.MemoryState) (ty : MirTy) (place : MemPlace)
    (optVal : Option Val)
    (h_ld : loadIndirectV2 m ty place = .ok optVal) :
    ∃ lay bs,
      layoutOfTyV2 ty = some lay ∧
      readBytes m place lay.size lay.alignLog2 = .ok bs ∧
      decodeValV2 profileV2TargetEndian ty bs = .ok optVal ∧
      ∃ a : MirSemantics.Allocation,
        findAllocation place.allocId m.allocations = some a ∧
        isAligned a place.offset lay.alignLog2 = true := by
  dsimp only [loadIndirectV2] at h_ld
  cases h_lay : layoutOfTyV2 ty with
  | none => rw [h_lay] at h_ld; dsimp only at h_ld; cases h_ld
  | some lay =>
    rw [h_lay] at h_ld
    dsimp only at h_ld
    cases h_rb : readBytes m place lay.size lay.alignLog2 with
    | error k => rw [h_rb] at h_ld; dsimp only at h_ld; cases h_ld
    | ok bs =>
      rw [h_rb] at h_ld
      dsimp only at h_ld
      let ⟨a, h_fa, h_al, _, _⟩ :=
        readBytes_requires_alloc_and_alignment m place lay.size lay.alignLog2 bs
          h_rb
      exact ⟨lay, bs, rfl, h_rb, h_ld, a, h_fa, h_al⟩

/-- Any successful `storeIndirectV2` resolves a Profile v2 layout and an aligned
allocation record in `m`, even for zero-sized types. -/
theorem storeIndirectV2_requires_alloc_and_alignment
    (m m' : MirSemantics.MemoryState) (ty : MirTy) (place : MemPlace) (v : Val)
    (h_st : storeIndirectV2 m ty place v = .ok m') :
    ∃ lay bs,
      layoutOfTyV2 ty = some lay ∧
      encodeValV2 profileV2TargetEndian ty v = .ok bs ∧
      writeBytes m place lay.alignLog2 bs = .ok m' ∧
      ∃ a : MirSemantics.Allocation,
        findAllocation place.allocId m.allocations = some a ∧
        isAligned a place.offset lay.alignLog2 = true := by
  dsimp only [storeIndirectV2] at h_st
  cases h_lay : layoutOfTyV2 ty with
  | none => rw [h_lay] at h_st; dsimp only at h_st; cases h_st
  | some lay =>
    rw [h_lay] at h_st
    dsimp only at h_st
    cases h_enc : encodeValV2 profileV2TargetEndian ty v with
    | error k => rw [h_enc] at h_st; dsimp only at h_st; cases h_st
    | ok bs =>
      rw [h_enc] at h_st
      dsimp only at h_st
      let ⟨a, h_fa, h_al, _, _⟩ :=
        writeBytes_requires_alloc_and_alignment m m' place lay.alignLog2 bs h_st
      exact ⟨lay, bs, rfl, rfl, h_st, a, h_fa, h_al⟩

/-- Any successful `sliceRefRawCheck` enforces the `isize::MAX` byte-size bound,
non-nullness and alignment on provenance-free pointers (returning `none` only
when `len * es = 0`), and live, in-bounds, aligned, mutable-when-`isMut`
allocation invariants on provenance-bearing pointers (without requiring
whole-span `isSliceAllInit`, so padded or tagged elements can validate active
fields individually). -/
theorem sliceRefRawCheck_requires_nonnull_bounds_and_alignment
    (m : MirSemantics.MemoryState) (isMut : Bool) (es eal : Nat)
    (p : PtrVal) (len : UInt64) (optAlloc : Option MirSemantics.Allocation)
    (h_s : sliceRefRawCheck m isMut es eal p len = .ok optAlloc) :
    len.toNat * es < isizeMaxBytes ∧
    (p.allocId = none →
      optAlloc = none ∧
      p.offsetBytes.toNat ≠ 0 ∧
      len.toNat * es = 0 ∧
      Nat.mod p.offsetBytes.toNat (Nat.pow 2 eal) = 0) ∧
    (∀ aid, p.allocId = some aid →
      ∃ a : MirSemantics.Allocation,
        optAlloc = some a ∧
        findAllocation aid m.allocations = some a ∧
        a.live = true ∧
        isInBounds a p.offsetBytes.toNat (len.toNat * es) = true ∧
        isAligned a p.offsetBytes.toNat eal = true ∧
        (isMut = true → a.mutability = .mut)) := by
  dsimp only [sliceRefRawCheck] at h_s
  cases h_tb : Nat.blt (len.toNat * es) isizeMaxBytes with
  | false => rw [h_tb] at h_s; cases h_s
  | true =>
    rw [h_tb] at h_s
    have h_lt : len.toNat * es < isizeMaxBytes := nat_blt_true_lt h_tb
    cases h_aid : p.allocId with
    | none =>
      rw [h_aid] at h_s
      dsimp only at h_s
      cases h_off0 : Nat.beq p.offsetBytes.toNat 0 with
      | true => rw [h_off0] at h_s; cases h_s
      | false =>
        cases h_pos : Nat.blt 0 (len.toNat * es) with
        | true => rw [h_off0, h_pos] at h_s; cases h_s
        | false =>
          rw [h_off0, h_pos] at h_s
          cases h_mod :
              Nat.beq (Nat.mod p.offsetBytes.toNat (Nat.pow 2 eal)) 0 with
          | false => rw [h_mod] at h_s; cases h_s
          | true =>
            rw [h_mod] at h_s
            injection h_s with h_opt
            refine ⟨h_lt, ?_, fun aid h_eq => by cases h_eq⟩
            intro _
            exact ⟨h_opt.symm, nat_beq_false_ne h_off0,
              nat_blt_zero_false_eq_zero h_pos,
              (nat_beq_true_iff _ 0).1 h_mod⟩
    | some aid =>
      rw [h_aid] at h_s
      dsimp only at h_s
      cases h_fa : findAllocation aid m.allocations with
      | none => rw [h_fa] at h_s; dsimp only at h_s; cases h_s
      | some a =>
        rw [h_fa] at h_s
        dsimp only at h_s
        cases h_live : a.live with
        | false => rw [h_live] at h_s; cases h_s
        | true =>
          cases h_ib :
              isInBounds a p.offsetBytes.toNat (len.toNat * es) with
          | false => rw [h_live, h_ib] at h_s; cases h_s
          | true =>
            cases h_al : isAligned a p.offsetBytes.toNat eal with
            | false => rw [h_live, h_ib, h_al] at h_s; cases h_s
            | true =>
              rw [h_live, h_ib, h_al] at h_s
              cases h_mut_ok :
                  (isMut && !Mutability.beq a.mutability .mut) with
              | true => rw [h_mut_ok] at h_s; cases h_s
              | false =>
                rw [h_mut_ok] at h_s
                injection h_s with h_opt
                refine ⟨h_lt, (fun h_none => by cases h_none), ?_⟩
                intro aid' h_eq
                injection h_eq with h_aid_eq
                subst h_aid_eq
                refine ⟨a, h_opt.symm, h_fa, h_live, h_ib, h_al, ?_⟩
                intro h_ismut
                rw [h_ismut, Bool.true_and] at h_mut_ok
                cases h_mb : Mutability.beq a.mutability .mut with
                | false => rw [h_mb] at h_mut_ok; cases h_mut_ok
                | true => exact Mutability.eq_of_beq h_mb

/-- Any successful `sliceFromRawPartsCheck` enforces the `isize::MAX` byte-size
bound, non-nullness and alignment on provenance-free pointers (only when
`len * es = 0`), and live, in-bounds, aligned, initialized (plus mutable when
`isMut = true`) allocation invariants on provenance-bearing pointers. -/
theorem sliceFromRawPartsCheck_requires_nonnull_bounds_and_alignment
    (m : MirSemantics.MemoryState) (isMut : Bool) (es eal : Nat)
    (p : PtrVal) (len : UInt64) (v : Val)
    (h_s : sliceFromRawPartsCheck m isMut es eal p len = .ok v) :
    v = .slicePtr p len ∧
    len.toNat * es < isizeMaxBytes ∧
    (p.allocId = none →
      p.offsetBytes.toNat ≠ 0 ∧
      len.toNat * es = 0 ∧
      Nat.mod p.offsetBytes.toNat (Nat.pow 2 eal) = 0) ∧
    (∀ aid, p.allocId = some aid →
      ∃ a : MirSemantics.Allocation,
        findAllocation aid m.allocations = some a ∧
        a.live = true ∧
        isInBounds a p.offsetBytes.toNat (len.toNat * es) = true ∧
        isAligned a p.offsetBytes.toNat eal = true ∧
        (isMut = true → a.mutability = .mut) ∧
        isSliceAllInit
          ((a.bytes.drop p.offsetBytes.toNat).take
            (len.toNat * es)) = true) := by
  dsimp only [sliceFromRawPartsCheck] at h_s
  cases h_raw : sliceRefRawCheck m isMut es eal p len with
  | error k => rw [h_raw] at h_s; dsimp only at h_s; cases h_s
  | ok optAlloc =>
    rw [h_raw] at h_s
    have ⟨h_lt, h_none, h_some⟩ :=
      sliceRefRawCheck_requires_nonnull_bounds_and_alignment
        m isMut es eal p len optAlloc h_raw
    cases optAlloc with
    | none =>
      dsimp only at h_s
      injection h_s with h_v
      refine ⟨h_v.symm, h_lt, ?_, ?_⟩
      · intro h_aid
        let ⟨_, h1, h2, h3⟩ := h_none h_aid
        exact ⟨h1, h2, h3⟩
      · intro aid h_aid
        let ⟨_, h_opt, _⟩ := h_some aid h_aid
        cases h_opt
    | some a =>
      dsimp only at h_s
      cases h_init :
          isSliceAllInit
            ((a.bytes.drop p.offsetBytes.toNat).take (len.toNat * es)) with
      | false => rw [h_init] at h_s; cases h_s
      | true =>
        rw [h_init] at h_s
        injection h_s with h_v
        refine ⟨h_v.symm, h_lt, ?_, ?_⟩
        · intro h_aid
          let ⟨h_opt, _⟩ := h_none h_aid
          cases h_opt
        · intro aid h_aid
          let ⟨a', h_opt, h_fa, h_live, h_ib, h_al, h_mut⟩ := h_some aid h_aid
          injection h_opt with h_aeq
          subst h_aeq
          exact ⟨a, h_fa, h_live, h_ib, h_al, h_mut, h_init⟩

/-- Any successful `ptrAddInMem` enforces `count * elemSize < isizeMaxBytes`,
zero-delta invariance for provenance-free pointers, and live in-bounds
offsets for provenance-bearing pointers. -/
theorem ptrAddInMem_requires_bounds_and_no_wrap
    (m : MirSemantics.MemoryState) (elemSize : Nat) (p : PtrVal) (count : Nat)
    (p' : PtrVal)
    (h_pa : ptrAddInMem m elemSize p count = .ok p') :
    count * elemSize < isizeMaxBytes ∧
    (p.allocId = none → count * elemSize = 0 ∧ p' = p) ∧
    (∀ aid, p.allocId = some aid →
      ∃ a : MirSemantics.Allocation,
        findAllocation aid m.allocations = some a ∧
        a.live = true ∧
        p.offsetBytes.toNat + count * elemSize ≤ a.bytes.length ∧
        p' = { p with
          offsetBytes :=
            UInt64.ofNat (p.offsetBytes.toNat + count * elemSize) }) := by
  dsimp only [ptrAddInMem] at h_pa
  cases h_ltb : Nat.blt (count * elemSize) isizeMaxBytes with
  | false => rw [h_ltb] at h_pa; cases h_pa
  | true =>
    rw [h_ltb] at h_pa
    have h_lt : count * elemSize < isizeMaxBytes := nat_blt_true_lt h_ltb
    cases h_aid : p.allocId with
    | none =>
      rw [h_aid] at h_pa
      dsimp only at h_pa
      cases h_z : Nat.beq (count * elemSize) 0 with
      | false => rw [h_z] at h_pa; cases h_pa
      | true =>
        rw [h_z] at h_pa
        injection h_pa with h_p'
        exact ⟨h_lt, fun _ => ⟨(nat_beq_true_iff _ 0).1 h_z, h_p'.symm⟩,
          fun aid h_eq => by cases h_eq⟩
    | some aid =>
      rw [h_aid] at h_pa
      dsimp only at h_pa
      cases h_fa : findAllocation aid m.allocations with
      | none => rw [h_fa] at h_pa; dsimp only at h_pa; cases h_pa
      | some a =>
        rw [h_fa] at h_pa
        dsimp only at h_pa
        cases h_live : a.live with
        | false => rw [h_live] at h_pa; cases h_pa
        | true =>
          cases h_le :
              Nat.ble (p.offsetBytes.toNat + count * elemSize)
                a.bytes.length with
          | false => rw [h_live, h_le] at h_pa; cases h_pa
          | true =>
            rw [h_live, h_le] at h_pa
            injection h_pa with h_p'
            refine ⟨h_lt, (fun h_none => by cases h_none), ?_⟩
            intro aid' h_eq
            injection h_eq with h_aid_eq
            subst h_aid_eq
            exact ⟨a, h_fa, h_live, (nat_ble_true_iff _ _).1 h_le, h_p'.symm⟩

/-- `refValidInMem` on any integer slice reference reduces to
`sliceFromRawPartsCheck` with the element integer layout. -/
theorem refValidInMem_slice_requires_sliceFromRawParts
    (m : MirSemantics.MemoryState) (reqMut : MirAst.Mutability) (w : IntWidth)
    (s : Bool) (p : PtrVal) (len : UInt64)
    (h_rv :
      refValidInMem m reqMut (.slice (.int w s)) (.slicePtr p len) = .ok ()) :
    ∃ v, sliceFromRawPartsCheck m (Mutability.beq reqMut .mut)
      (intLayout w).size (intLayout w).alignLog2 p len = .ok v := by
  dsimp only [refValidInMem] at h_rv
  have h_sz : (!isSizedNoRefV2Ty (.int w s)) = false := rfl
  have h_lay : layoutOfTyV2 (.int w s) = some (intLayout w) := rfl
  rw [h_sz, ite_eq_right Bool.false_ne_true, h_lay] at h_rv
  dsimp only at h_rv
  cases h_sc : sliceFromRawPartsCheck m (Mutability.beq reqMut .mut)
      (intLayout w).size (intLayout w).alignLog2 p len with
  | error k => rw [h_sc] at h_rv; dsimp only at h_rv; cases h_rv
  | ok v => exact ⟨v, rfl⟩

/-- General slice-reference validity specification across all admitted element
types `elem`: any `refValidInMem` success on `.slice elem` enforces
`isSizedNoRefV2Ty elem = true`, element inhabitance whenever `0 < len.toNat`,
and raw non-null, alignment, bounds, and mutability invariants at the element's
`layoutOfTyV2` layout. -/
theorem refValidInMem_slice_general_spec
    (m : MirSemantics.MemoryState) (reqMut : MirAst.Mutability) (elem : MirTy)
    (p : PtrVal) (len : UInt64)
    (h_rv : refValidInMem m reqMut (.slice elem) (.slicePtr p len) = .ok ()) :
    isSizedNoRefV2Ty elem = true ∧
    (0 < len.toNat → isInhabitedV2Ty elem = true) ∧
    ∃ lay,
      layoutOfTyV2 elem = some lay ∧
      len.toNat * lay.size < isizeMaxBytes ∧
      (p.allocId = none →
        p.offsetBytes.toNat ≠ 0 ∧
        len.toNat * lay.size = 0 ∧
        Nat.mod p.offsetBytes.toNat (Nat.pow 2 lay.alignLog2) = 0) ∧
      (∀ aid, p.allocId = some aid →
        ∃ a : MirSemantics.Allocation,
          findAllocation aid m.allocations = some a ∧
          a.live = true ∧
          isInBounds a p.offsetBytes.toNat (len.toNat * lay.size) = true ∧
          isAligned a p.offsetBytes.toNat lay.alignLog2 = true ∧
          (Mutability.beq reqMut .mut = true → a.mutability = .mut)) := by
  dsimp only [refValidInMem] at h_rv
  cases h_sz : (!isSizedNoRefV2Ty elem) with
  | true => rw [h_sz] at h_rv; cases h_rv
  | false =>
    rw [h_sz, ite_eq_right Bool.false_ne_true] at h_rv
    have h_sz_true : isSizedNoRefV2Ty elem = true := by
      cases h_s : isSizedNoRefV2Ty elem with
      | true => rfl
      | false => rw [h_s] at h_sz; cases h_sz
    cases h_lay : layoutOfTyV2 elem with
    | none => rw [h_lay] at h_rv; dsimp only at h_rv; cases h_rv
    | some lay =>
      rw [h_lay] at h_rv
      dsimp only at h_rv
      have h_other :
          ∀ {elem' : MirTy},
            (if (Nat.blt 0 len.toNat && !isInhabitedV2Ty elem') = true then
              Except.error FaultKind.undefined
            else
              match sliceRefRawCheck m (Mutability.beq reqMut .mut)
                  lay.size lay.alignLog2 p len with
              | .error k => .error k
              | .ok optAlloc =>
                if (Nat.beq len.toNat 0 || Nat.beq lay.size 0) = true then
                  .ok ()
                else
                  match optAlloc with
                  | none => .error .undefined
                  | some a =>
                    validateSliceElemsV2 elem' a.bytes lay.size
                      p.offsetBytes.toNat len.toNat) = .ok () →
            (0 < len.toNat → isInhabitedV2Ty elem' = true) ∧
            len.toNat * lay.size < isizeMaxBytes ∧
            (p.allocId = none →
              p.offsetBytes.toNat ≠ 0 ∧
              len.toNat * lay.size = 0 ∧
              Nat.mod p.offsetBytes.toNat (Nat.pow 2 lay.alignLog2) = 0) ∧
            (∀ aid, p.allocId = some aid →
              ∃ a : MirSemantics.Allocation,
                findAllocation aid m.allocations = some a ∧
                a.live = true ∧
                isInBounds a p.offsetBytes.toNat
                  (len.toNat * lay.size) = true ∧
                isAligned a p.offsetBytes.toNat lay.alignLog2 = true ∧
                (Mutability.beq reqMut .mut = true →
                  a.mutability = .mut)) := by
        intro elem' h_branch_rv
        cases h_inh_guard :
            (Nat.blt 0 len.toNat && !isInhabitedV2Ty elem') with
        | true => rw [h_inh_guard] at h_branch_rv; cases h_branch_rv
        | false =>
          rw [h_inh_guard, ite_eq_right Bool.false_ne_true] at h_branch_rv
          have h_inh : 0 < len.toNat → isInhabitedV2Ty elem' = true := by
            intro h_pos
            have h_blt : Nat.blt 0 len.toNat = true :=
              Nat.ble_eq_true_of_le h_pos
            rw [h_blt, Bool.true_and] at h_inh_guard
            cases h_i : isInhabitedV2Ty elem' with
            | true => rfl
            | false => rw [h_i] at h_inh_guard; cases h_inh_guard
          cases h_raw : sliceRefRawCheck m (Mutability.beq reqMut .mut)
              lay.size lay.alignLog2 p len with
          | error k =>
            rw [h_raw] at h_branch_rv; dsimp only at h_branch_rv
            cases h_branch_rv
          | ok optAlloc =>
            have ⟨h_lt, h_none, h_some⟩ :=
              sliceRefRawCheck_requires_nonnull_bounds_and_alignment
                m (Mutability.beq reqMut .mut) lay.size lay.alignLog2 p len
                optAlloc h_raw
            refine ⟨h_inh, h_lt, ?_, ?_⟩
            · intro h_aid
              let ⟨_, h1, h2, h3⟩ := h_none h_aid
              exact ⟨h1, h2, h3⟩
            · intro aid h_aid
              let ⟨a, _, h_fa, h_live, h_ib, h_al, h_mut⟩ := h_some aid h_aid
              exact ⟨a, h_fa, h_live, h_ib, h_al, h_mut⟩
      cases elem with
      | int w s =>
        dsimp only at h_rv
        cases h_sc : sliceFromRawPartsCheck m (Mutability.beq reqMut .mut)
            lay.size lay.alignLog2 p len with
        | error k => rw [h_sc] at h_rv; dsimp only at h_rv; cases h_rv
        | ok sv =>
          have ⟨_, h_lt, h_none, h_some⟩ :=
            sliceFromRawPartsCheck_requires_nonnull_bounds_and_alignment
              m (Mutability.beq reqMut .mut) lay.size lay.alignLog2 p len sv
              h_sc
          refine ⟨h_sz_true, fun _ => rfl, lay, rfl, h_lt, h_none, ?_⟩
          intro aid h_aid
          let ⟨a, h_fa, h_live, h_ib, h_al, h_mut, _⟩ := h_some aid h_aid
          exact ⟨a, h_fa, h_live, h_ib, h_al, h_mut⟩
      | bool | unit | never | char | ordering | enum _ | tuple _ | ref _ _
      | rawPtr _ _ | slice _ | str | array _ _ | rangeTo _ | rangeFrom _
      | option _ | range _ | unsupported | box _ | vec _ =>
        dsimp only at h_rv
        let ⟨h_inh, h_lt, h_none, h_some⟩ := h_other h_rv
        exact ⟨h_sz_true, h_inh, lay, rfl, h_lt, h_none, h_some⟩

/-- `sliceGetUncheckedCheck` always checks `startOff ≤ endOff ≤ len` and
advances `p` via `ptrAddInMem` with the new length `endOff - startOff`. -/
theorem sliceGetUncheckedCheck_bounds_and_offset
    (m : MirSemantics.MemoryState) (p : PtrVal) (len startOff endOff : Nat)
    (v : Val)
    (h_sg : sliceGetUncheckedCheck m p len startOff endOff = .ok v) :
    startOff ≤ endOff ∧
    endOff ≤ len ∧
    ∃ p',
      ptrAddInMem m 1 p startOff = .ok p' ∧
      v = .slicePtr p' (UInt64.ofNat (endOff - startOff)) := by
  dsimp only [sliceGetUncheckedCheck] at h_sg
  cases h_se : Nat.ble startOff endOff with
  | false => rw [h_se] at h_sg; cases h_sg
  | true =>
    cases h_el : Nat.ble endOff len with
    | false => rw [h_se, h_el] at h_sg; cases h_sg
    | true =>
      rw [h_se, h_el] at h_sg
      cases h_pa : ptrAddInMem m 1 p startOff with
      | error k => rw [h_pa] at h_sg; dsimp only at h_sg; cases h_sg
      | ok p' =>
        rw [h_pa] at h_sg
        dsimp only at h_sg
        injection h_sg with h_v
        exact ⟨(nat_ble_true_iff _ _).1 h_se, (nat_ble_true_iff _ _).1 h_el,
          p', rfl, h_v.symm⟩

/-- `evalRefRvalueV2` on `.deref` never escalates a `.shared` reference to
`.mut`. -/
theorem evalRefRvalueV2_deref_no_shared_to_mut
    (bodyLocals : List MirTy) (locals : List LocalSlot)
    (m : MirSemantics.MemoryState) (dstTy : MirTy) (place : Place) (pt : MirTy)
    (h_proj : place.projection = [.deref])
    (h_ty : MirSemantics.getElem? bodyLocals place.localId =
      some (.ref .shared pt))
    (res : Val × List LocalSlot × MirSemantics.MemoryState) :
    evalRefRvalueV2 bodyLocals locals m dstTy .mut place ≠ .ok res := by
  intro h_ok
  dsimp only [evalRefRvalueV2] at h_ok
  rw [h_proj, h_ty] at h_ok
  dsimp only at h_ok
  cases h_slot : MirSemantics.getElem? locals place.localId with
  | none => rw [h_slot] at h_ok; dsimp only at h_ok; cases h_ok
  | some slot =>
    rw [h_slot] at h_ok
    cases slot <;> cases h_ok

/-- Every successful `evalRefRvalueV2` produces a reference valid against the
resulting memory (`refValidInMem`) at `reqMut`. -/
theorem evalRefRvalueV2_requires_refValidInMem
    (bodyLocals : List MirTy) (locals : List LocalSlot)
    (m : MirSemantics.MemoryState) (dstTy : MirTy) (reqMut : MirAst.Mutability)
    (place : Place) (rv : Val) (locals' : List LocalSlot)
    (m' : MirSemantics.MemoryState)
    (h_ref : evalRefRvalueV2 bodyLocals locals m dstTy reqMut place =
      .ok (rv, locals', m')) :
    ∃ pt,
      dstTy = .ref reqMut pt ∧
      refValidInMem m' reqMut pt rv = .ok () := by
  dsimp only [evalRefRvalueV2] at h_ref
  cases h_proj : place.projection with
  | nil =>
    rw [h_proj] at h_ref
    dsimp only at h_ref
    cases h_prom : promoteLocalToMemory bodyLocals locals m place.localId with
    | error k => rw [h_prom] at h_ref; dsimp only at h_ref; cases h_ref
    | ok res =>
      cases res with | mk localTy res =>
      cases res with | mk mplace res =>
      cases res with | mk locals1 m1 =>
      rw [h_prom] at h_ref
      dsimp only at h_ref
      cases h_ty : MirTy.beq dstTy (.ref reqMut localTy) with
      | false => rw [h_ty] at h_ref; cases h_ref
      | true =>
        rw [h_ty] at h_ref
        let cand : Val :=
          .ptr ⟨some mplace.allocId, UInt64.ofNat mplace.offset, .isize⟩
        cases h_rv : refValidInMem m1 reqMut localTy cand with
        | error k => rw [h_rv] at h_ref; dsimp only at h_ref; cases h_ref
        | ok u =>
          cases u
          rw [h_rv] at h_ref
          dsimp only at h_ref
          injection h_ref with h_eq
          have h_rv_eq : rv = cand := (congrArg Prod.fst h_eq).symm
          have h_m_eq : m' = m1 :=
            (congrArg (fun p => p.2.2) h_eq).symm
          rw [h_rv_eq, h_m_eq]
          exact ⟨localTy, MirTy.eq_of_beq h_ty, h_rv⟩
  | cons hd tl =>
    cases hd with
    | deref =>
      cases tl with
      | cons _ _ => rw [h_proj] at h_ref; cases h_ref
      | nil =>
        rw [h_proj] at h_ref
        dsimp only at h_ref
        cases h_ty : MirSemantics.getElem? bodyLocals place.localId with
        | none =>
          rw [h_ty] at h_ref
          cases h_sl : MirSemantics.getElem? locals place.localId <;>
            (rw [h_sl] at h_ref; dsimp only at h_ref; cases h_ref)
        | some baseTy =>
          rw [h_ty] at h_ref
          cases h_sl : MirSemantics.getElem? locals place.localId with
          | none => rw [h_sl] at h_ref; dsimp only at h_ref; cases h_ref
          | some slot =>
            cases slot with
            | dead => rw [h_sl] at h_ref; dsimp only at h_ref; cases h_ref
            | partialTuple _ =>
              rw [h_sl] at h_ref
              dsimp only at h_ref
              cases baseTy with
              | ref srcMut pt =>
                dsimp only at h_ref
                cases h_esc :
                    (Mutability.beq srcMut .shared &&
                      Mutability.beq reqMut .mut) with
                | true => rw [h_esc] at h_ref; cases h_ref
                | false =>
                  cases h_beq : MirTy.beq dstTy (.ref reqMut pt) with
                  | false => rw [h_esc, h_beq] at h_ref; cases h_ref
                  | true => rw [h_esc, h_beq] at h_ref; cases h_ref
              | bool | int _ _ | unit | never | char | ordering | enum _
              | tuple _ | rawPtr _ _ | slice _ | str | array _ _ | rangeTo _
              | rangeFrom _ | unsupported | option _ | range _ | box _
              | vec _ =>
                dsimp only at h_ref; cases h_ref
            | immediate optVal =>
              rw [h_sl] at h_ref
              dsimp only at h_ref
              cases baseTy with
              | ref srcMut pt =>
                dsimp only at h_ref
                cases h_esc :
                    (Mutability.beq srcMut .shared &&
                      Mutability.beq reqMut .mut) with
                | true => rw [h_esc] at h_ref; cases h_ref
                | false =>
                  cases h_beq : MirTy.beq dstTy (.ref reqMut pt) with
                  | false => rw [h_esc, h_beq] at h_ref; cases h_ref
                  | true =>
                    rw [h_esc, h_beq] at h_ref
                    cases optVal with
                    | none => cases h_ref
                    | some v =>
                      dsimp only at h_ref
                      cases h_rv : refValidInMem m reqMut pt v with
                      | error k =>
                        rw [h_rv] at h_ref; dsimp only at h_ref; cases h_ref
                      | ok u =>
                        cases u
                        rw [h_rv] at h_ref
                        dsimp only at h_ref
                        injection h_ref with h_eq
                        have h_rv_eq : rv = v :=
                          (congrArg Prod.fst h_eq).symm
                        have h_m_eq : m' = m :=
                          (congrArg (fun p => p.2.2) h_eq).symm
                        rw [h_rv_eq, h_m_eq]
                        exact ⟨pt, MirTy.eq_of_beq h_beq, h_rv⟩
              | bool | int _ _ | unit | never | char | ordering | enum _
              | tuple _ | rawPtr _ _ | slice _ | str | array _ _ | rangeTo _
              | rangeFrom _ | unsupported | option _ | range _ | box _
              | vec _ =>
                dsimp only at h_ref; cases h_ref
            | indirect mplace =>
              rw [h_sl] at h_ref
              dsimp only at h_ref
              cases baseTy with
              | ref srcMut pt =>
                dsimp only at h_ref
                cases h_esc :
                    (Mutability.beq srcMut .shared &&
                      Mutability.beq reqMut .mut) with
                | true => rw [h_esc] at h_ref; cases h_ref
                | false =>
                  cases h_beq : MirTy.beq dstTy (.ref reqMut pt) with
                  | false => rw [h_esc, h_beq] at h_ref; cases h_ref
                  | true =>
                    rw [h_esc, h_beq] at h_ref
                    cases h_ld : loadIndirectV2 m (.ref srcMut pt) mplace with
                    | error k =>
                      rw [h_ld] at h_ref; dsimp only at h_ref; cases h_ref
                    | ok optVal =>
                      rw [h_ld] at h_ref
                      cases optVal with
                      | none => cases h_ref
                      | some v =>
                        dsimp only at h_ref
                        cases h_rv : refValidInMem m reqMut pt v with
                        | error k =>
                          rw [h_rv] at h_ref; dsimp only at h_ref; cases h_ref
                        | ok u =>
                          cases u
                          rw [h_rv] at h_ref
                          dsimp only at h_ref
                          injection h_ref with h_eq
                          have h_rv_eq : rv = v :=
                            (congrArg Prod.fst h_eq).symm
                          have h_m_eq : m' = m :=
                            (congrArg (fun p => p.2.2) h_eq).symm
                          rw [h_rv_eq, h_m_eq]
                          exact ⟨pt, MirTy.eq_of_beq h_beq, h_rv⟩
              | bool | int _ _ | unit | never | char | ordering | enum _
              | tuple _ | rawPtr _ _ | slice _ | str | array _ _ | rangeTo _
              | rangeFrom _ | unsupported | option _ | range _ | box _
              | vec _ =>
                dsimp only at h_ref; cases h_ref
    | field _ _ | constantIndex _ _ _ | unsupported | downcast _ =>
      rw [h_proj] at h_ref; cases h_ref

/-- `execCoreCallOp .sliceGetUncheckedRangeTo` rejects `.shared -> .mut`
escalation, validates the input slice against `inMut`, and checks `[0..endOff]`
bounds via `sliceGetUncheckedCheck`. -/
theorem execCoreCallOp_sliceGetUncheckedRangeTo_spec
    (m : MirSemantics.MemoryState) (inMut : MirAst.Mutability) (p : PtrVal)
    (len endOff : UInt64) (dstTy : MirTy) (v : Val)
    (h_op : execCoreCallOp m .sliceGetUncheckedRangeTo
      [(.ref inMut (.slice (.int .i8 false)), .slicePtr p len),
       (.rangeTo (.int .isize false), .rangeTo endOff)] dstTy = .ok v) :
    ∃ outMut,
      dstTy = .ref outMut (.slice (.int .i8 false)) ∧
      (inMut = .shared → outMut = .shared) ∧
      refValidInMem m inMut (.slice (.int .i8 false)) (.slicePtr p len) =
        .ok () ∧
      sliceGetUncheckedCheck m p len.toNat 0 endOff.toNat = .ok v := by
  dsimp only [execCoreCallOp] at h_op
  cases dstTy with
  | ref outMut pt =>
    cases pt with
    | slice elem =>
      cases elem with
      | int w s =>
        cases w with
        | i8 =>
          cases s with
          | false =>
            dsimp only at h_op
            have hW : (!IntWidth.beq .i8 .i8 || !(false == false)) = false :=
              rfl
            rw [hW, if_neg Bool.false_ne_true] at h_op
            cases h_esc : (Mutability.beq inMut .shared &&
                Mutability.beq outMut .mut) with
            | true => rw [h_esc] at h_op; cases h_op
            | false =>
              rw [h_esc] at h_op
              cases h_rv : refValidInMem m inMut (.slice (.int .i8 false))
                  (.slicePtr p len) with
              | error k => rw [h_rv] at h_op; dsimp only at h_op; cases h_op
              | ok u =>
                cases u
                rw [h_rv] at h_op
                dsimp only at h_op
                refine ⟨outMut, rfl, ?_, rfl, h_op⟩
                intro h_in
                rw [h_in] at h_esc
                cases outMut with
                | shared => rfl
                | «mut» => cases h_esc
          | true => dsimp only at h_op; cases h_op
        | i16 | i32 | i64 | i128 | isize => dsimp only at h_op; cases h_op
      | bool | unit | never | char | ordering | enum _ | tuple _ | ref _ _
      | rawPtr _ _ | slice _ | str | array _ _ | rangeTo _ | rangeFrom _
      | unsupported | option _ | range _ | box _ | vec _ =>
        dsimp only at h_op; cases h_op
    | bool | int _ _ | unit | never | char | ordering | enum _ | tuple _
    | ref _ _ | rawPtr _ _ | str | array _ _ | rangeTo _ | rangeFrom _
    | unsupported | option _ | range _ | box _ | vec _ =>
      dsimp only at h_op; cases h_op
  | bool | int _ _ | unit | never | char | ordering | enum _ | tuple _
  | rawPtr _ _ | slice _ | str | array _ _ | rangeTo _ | rangeFrom _
  | unsupported | option _ | range _ | box _ | vec _ =>
    dsimp only at h_op; cases h_op

/-- `execCoreCallOp .sliceGetUncheckedRangeFrom` rejects `.shared -> .mut`
escalation, validates the input slice against `inMut`, and checks
`[startOff..len]` bounds via `sliceGetUncheckedCheck`. -/
theorem execCoreCallOp_sliceGetUncheckedRangeFrom_spec
    (m : MirSemantics.MemoryState) (inMut : MirAst.Mutability) (p : PtrVal)
    (len startOff : UInt64) (dstTy : MirTy) (v : Val)
    (h_op : execCoreCallOp m .sliceGetUncheckedRangeFrom
      [(.ref inMut (.slice (.int .i8 false)), .slicePtr p len),
       (.rangeFrom (.int .isize false), .rangeFrom startOff)] dstTy = .ok v) :
    ∃ outMut,
      dstTy = .ref outMut (.slice (.int .i8 false)) ∧
      (inMut = .shared → outMut = .shared) ∧
      refValidInMem m inMut (.slice (.int .i8 false)) (.slicePtr p len) =
        .ok () ∧
      sliceGetUncheckedCheck m p len.toNat startOff.toNat len.toNat =
        .ok v := by
  dsimp only [execCoreCallOp] at h_op
  cases dstTy with
  | ref outMut pt =>
    cases pt with
    | slice elem =>
      cases elem with
      | int w s =>
        cases w with
        | i8 =>
          cases s with
          | false =>
            dsimp only at h_op
            have hW : (!IntWidth.beq .i8 .i8 || !(false == false)) = false :=
              rfl
            rw [hW, if_neg Bool.false_ne_true] at h_op
            cases h_esc : (Mutability.beq inMut .shared &&
                Mutability.beq outMut .mut) with
            | true => rw [h_esc] at h_op; cases h_op
            | false =>
              rw [h_esc] at h_op
              cases h_rv : refValidInMem m inMut (.slice (.int .i8 false))
                  (.slicePtr p len) with
              | error k => rw [h_rv] at h_op; dsimp only at h_op; cases h_op
              | ok u =>
                cases u
                rw [h_rv] at h_op
                dsimp only at h_op
                refine ⟨outMut, rfl, ?_, rfl, h_op⟩
                intro h_in
                rw [h_in] at h_esc
                cases outMut with
                | shared => rfl
                | «mut» => cases h_esc
          | true => dsimp only at h_op; cases h_op
        | i16 | i32 | i64 | i128 | isize => dsimp only at h_op; cases h_op
      | bool | unit | never | char | ordering | enum _ | tuple _ | ref _ _
      | rawPtr _ _ | slice _ | str | array _ _ | rangeTo _ | rangeFrom _
      | unsupported | option _ | range _ | box _ | vec _ =>
        dsimp only at h_op; cases h_op
    | bool | int _ _ | unit | never | char | ordering | enum _ | tuple _
    | ref _ _ | rawPtr _ _ | str | array _ _ | rangeTo _ | rangeFrom _
    | unsupported | option _ | range _ | box _ | vec _ =>
      dsimp only at h_op; cases h_op
  | bool | int _ _ | unit | never | char | ordering | enum _ | tuple _
  | rawPtr _ _ | slice _ | str | array _ _ | rangeTo _ | rangeFrom _
  | unsupported | option _ | range _ | box _ | vec _ =>
    dsimp only at h_op; cases h_op

/-- `execCoreCallOp .sliceLen` validates the slice reference via
`refValidInMem` and constrains the destination type to `usize`. -/
theorem execCoreCallOp_sliceLen_spec (m : MirSemantics.MemoryState)
    (reqMut : MirAst.Mutability) (w : IntWidth) (s : Bool) (p : PtrVal)
    (len : UInt64) (dstTy : MirTy) (v : Val)
    (h_op : execCoreCallOp m .sliceLen
      [(.ref reqMut (.slice (.int w s)), .slicePtr p len)] dstTy = .ok v) :
    dstTy = .int .isize false ∧
    refValidInMem m reqMut (.slice (.int w s)) (.slicePtr p len) = .ok () := by
  dsimp only [execCoreCallOp] at h_op
  cases h_ty : MirTy.beq dstTy (.int .isize false) with
  | false => rw [h_ty] at h_op; cases h_op
  | true =>
    rw [h_ty] at h_op
    cases h_rv :
        refValidInMem m reqMut (.slice (.int w s)) (.slicePtr p len) with
    | error k => rw [h_rv] at h_op; dsimp only at h_op; cases h_op
    | ok u =>
      cases u
      exact ⟨MirTy.eq_of_beq h_ty, rfl⟩

/-- `execCoreCallOp (.ptrAdd reqMut pointee)` requires matching mutability and
pointee type, sized `pointee`, and checked `ptrAddInMem`. -/
theorem execCoreCallOp_ptrAdd_spec (m : MirSemantics.MemoryState)
    (reqMut argMut : MirAst.Mutability) (pointee argPt : MirTy) (p : PtrVal)
    (countSv : ScalarVal) (dstTy : MirTy) (v : Val)
    (h_op : execCoreCallOp m (.ptrAdd reqMut pointee)
      [(.rawPtr argMut argPt, .ptr p), (.int .isize false, .scalar countSv)]
      dstTy = .ok v) :
    reqMut = argMut ∧
    pointee = argPt ∧
    dstTy = .rawPtr reqMut pointee ∧
    isUnsizedTy pointee = false ∧
    ∃ lay p',
      layoutOfTyV2 pointee = some lay ∧
      ptrAddInMem m lay.size p countSv.bits.toNat = .ok p' ∧
      v = .ptr p' := by
  dsimp only [execCoreCallOp] at h_op
  cases h_m : Mutability.beq reqMut argMut with
  | false => rw [h_m] at h_op; cases h_op
  | true =>
    cases h_p : MirTy.beq pointee argPt with
    | false => rw [h_m, h_p] at h_op; cases h_op
    | true =>
      cases h_d : MirTy.beq dstTy (.rawPtr reqMut pointee) with
      | false => rw [h_m, h_p, h_d] at h_op; cases h_op
      | true =>
        cases h_u : isUnsizedTy pointee with
        | true => rw [h_m, h_p, h_d, h_u] at h_op; cases h_op
        | false =>
          rw [h_m, h_p, h_d, h_u] at h_op
          cases h_lay : layoutOfTyV2 pointee with
          | none => rw [h_lay] at h_op; dsimp only at h_op; cases h_op
          | some lay =>
            rw [h_lay] at h_op
            dsimp only at h_op
            cases h_pa : ptrAddInMem m lay.size p countSv.bits.toNat with
            | error k => rw [h_pa] at h_op; dsimp only at h_op; cases h_op
            | ok p' =>
              rw [h_pa] at h_op
              dsimp only at h_op
              injection h_op with h_v
              exact ⟨Mutability.eq_of_beq h_m, MirTy.eq_of_beq h_p,
                MirTy.eq_of_beq h_d, rfl, lay, p', rfl, h_pa, h_v.symm⟩

/-- `evalPtrToPtrCastV2` accepts only raw-pointer inputs, forbids const-to-mut
and wide-to-thin pointer casts, rejects unsized thin pointees, and requires
identical slice element types on wide casts. -/
theorem evalPtrToPtrCastV2_rejects_unsized_thin_and_preserves_shape
    (srcTy : MirTy) (srcVal : Val) (castMut : MirAst.Mutability)
    (castPt : MirTy) (res : Val)
    (h_c : evalPtrToPtrCastV2 srcTy srcVal (.rawPtr castMut castPt) = .ok res) :
    (∃ srcMut srcPt p,
      srcTy = .rawPtr srcMut srcPt ∧
      srcVal = .ptr p ∧
      res = .ptr p ∧
      (srcMut = .shared → castMut = .shared) ∧
      isUnsizedTy srcPt = false ∧
      isUnsizedTy castPt = false) ∨
    (∃ srcMut elem p len,
      srcTy = .rawPtr srcMut (.slice elem) ∧
      castPt = .slice elem ∧
      srcVal = .slicePtr p len ∧
      (srcMut = .shared → castMut = .shared) ∧
      res = .slicePtr p len) := by
  dsimp only [evalPtrToPtrCastV2] at h_c
  cases srcTy with
  | rawPtr srcMut srcPt =>
    cases h_cm :
        isConstRawPtrTy (.rawPtr srcMut srcPt) &&
          MirAst.Mutability.beq castMut .mut with
    | true => rw [h_cm] at h_c; cases h_c
    | false =>
      rw [h_cm] at h_c
      have h_mut : srcMut = .shared → castMut = .shared := by
        intro h_sh
        subst h_sh
        cases castMut with
        | shared => rfl
        | «mut» =>
          dsimp only [isConstRawPtrTy, MirAst.Mutability.beq] at h_cm
          cases h_cm
      cases srcVal with
      | ptr p =>
        dsimp only at h_c
        cases h_us : isUnsizedTy srcPt with
        | true => rw [h_us] at h_c; cases h_c
        | false =>
          cases h_uc : isUnsizedTy castPt with
          | true => rw [h_us, h_uc] at h_c; cases h_c
          | false =>
            rw [h_us, h_uc] at h_c
            injection h_c with h_r
            exact Or.inl
              ⟨srcMut, srcPt, p, rfl, rfl, h_r.symm, h_mut, h_us, rfl⟩
      | slicePtr p len =>
        cases srcPt with
        | slice srcElem =>
          cases castPt with
          | slice castElem =>
            dsimp only at h_c
            cases h_el : MirTy.beq srcElem castElem with
            | false => rw [h_el] at h_c; cases h_c
            | true =>
              rw [h_el] at h_c
              injection h_c with h_r
              exact Or.inr ⟨srcMut, srcElem, p, len, rfl,
                congrArg MirTy.slice (MirTy.eq_of_beq h_el).symm,
                rfl, h_mut, h_r.symm⟩
          | _ => dsimp only at h_c; cases h_c
        | _ => dsimp only at h_c; cases h_c
      | _ => dsimp only at h_c; cases h_c
  | _ => dsimp only [isConstRawPtrTy] at h_c; cases h_c

/-- Tuple aggregation in `evalRvalueV2` enforces `checkValV2` on its result at
`dstTy`. -/
theorem aggregateTuple_evalRvalueV2_preserves_checkValV2
    (bodyLocals : List MirTy) (locals : List LocalSlot)
    (m : MirSemantics.MemoryState) (dstTy : MirTy) (fields : List Operand)
    (v : Val) (locals' : List LocalSlot) (m' : MirSemantics.MemoryState)
    (h_ev : evalRvalueV2 bodyLocals locals m dstTy (.aggregateTuple fields) =
      .ok (v, locals', m')) :
    ∃ fieldTys vs,
      dstTy = .tuple fieldTys ∧
      v = .tuple vs ∧
      checkValV2 v dstTy = true := by
  dsimp only [evalRvalueV2] at h_ev
  cases dstTy with
  | tuple fieldTys =>
    dsimp only at h_ev
    cases h_args : evalArgOperandsV2 bodyLocals locals m fields with
    | error k => rw [h_args] at h_ev; dsimp only at h_ev; cases h_ev
    | ok res =>
      cases res with | mk typedVals res =>
      cases res with | mk locals1 mem1 =>
      rw [h_args] at h_ev
      dsimp only at h_ev
      cases h_cv : checkValV2List (argValues typedVals) fieldTys with
      | false => rw [h_cv] at h_ev; cases h_ev
      | true =>
        rw [h_cv] at h_ev
        injection h_ev with h_eq
        have h_veq : v = .tuple (argValues typedVals) :=
          (congrArg Prod.fst h_eq).symm
        rw [h_veq]
        exact ⟨fieldTys, argValues typedVals, rfl, rfl, h_cv⟩
  | bool | int _ _ | unit | never | char | ordering | enum _ | ref _ _
  | rawPtr _ _ | slice _ | str | array _ _ | rangeTo _ | rangeFrom _
  | unsupported | option _ | range _ | box _ | vec _ =>
    dsimp only at h_ev; cases h_ev

/-- Every successful `writePlaceDestV2` (used by both `evalStatementV2 .assign`
and `writePlaceV2`) guarantees `checkValV2 val dstTy = true`. -/
theorem writePlaceDestV2_requires_checkValV2 (locals : List LocalSlot)
    (m : MirSemantics.MemoryState) (dest : PlaceDestV2) (dstTy : MirTy)
    (val : Val) (locals' : List LocalSlot) (m' : MirSemantics.MemoryState)
    (h_wp : writePlaceDestV2 locals m dest dstTy val = .ok (locals', m')) :
    checkValV2 val dstTy = true := by
  dsimp only [writePlaceDestV2] at h_wp
  cases h_cv : checkValV2 val dstTy with
  | false => rw [h_cv] at h_wp; cases h_wp
  | true => rfl

/-- Every successful `writePlaceV2` guarantees `checkValV2 val dstTy = true`. -/
theorem writePlaceV2_requires_checkValV2 (bodyLocals : List MirTy)
    (locals : List LocalSlot) (m : MirSemantics.MemoryState) (dst : Place)
    (dstTy : MirTy) (val : Val) (locals' : List LocalSlot)
    (m' : MirSemantics.MemoryState)
    (h_wp : writePlaceV2 bodyLocals locals m dst dstTy val =
      .ok (locals', m')) :
    checkValV2 val dstTy = true := by
  dsimp only [writePlaceV2] at h_wp
  cases h_res : resolvePlaceDestV2 bodyLocals locals m dst dstTy with
  | error k => rw [h_res] at h_wp; cases h_wp
  | ok dest =>
    rw [h_res] at h_wp
    exact writePlaceDestV2_requires_checkValV2 locals m dest dstTy val locals'
      m' h_wp

private theorem resolvePlaceDestV2_deref_branch (pt dstTy : MirTy)
    (ptrMut : MirAst.Mutability) (ptrRes : Except FaultKind (Option Val))
    (dest : PlaceDestV2)
    (h_match :
      (if isUnsizedTy pt || !MirTy.beq pt dstTy then .error .unsupported
       else if !MirAst.Mutability.beq ptrMut .mut then .error .undefined
       else
         match layoutOfTyV2 pt with
         | none => .error .unsupported
         | some lay =>
           match ptrRes with
           | .error k => .error k
           | .ok none => .error .undefined
           | .ok (some (.ptr pv)) => .ok (.deref pt lay pv)
           | .ok (some _) => .error .unsupported :
          Except FaultKind PlaceDestV2) = .ok dest) :
    ptrMut = .mut ∧
    isUnsizedTy pt = false ∧
    pt = dstTy ∧
    ∃ lay pv, layoutOfTyV2 pt = some lay ∧ dest = .deref pt lay pv := by
  cases h_us : isUnsizedTy pt with
  | true => rw [h_us] at h_match; cases h_match
  | false =>
    cases h_beq : MirTy.beq pt dstTy with
    | false => rw [h_us, h_beq] at h_match; cases h_match
    | true =>
      rw [h_us, h_beq] at h_match
      cases ptrMut with
      | shared => cases h_match
      | «mut» =>
        dsimp only [MirAst.Mutability.beq] at h_match
        cases h_lay : layoutOfTyV2 pt with
        | none => rw [h_lay] at h_match; cases h_match
        | some lay =>
          rw [h_lay] at h_match
          cases ptrRes with
          | error _ => cases h_match
          | ok optVal =>
            cases optVal with
            | none => cases h_match
            | some v =>
              cases v with
              | ptr pv =>
                injection h_match with h_d
                exact ⟨rfl, rfl, MirTy.eq_of_beq h_beq,
                  ⟨lay, pv, rfl, h_d.symm⟩⟩
              | scalar _ | slicePtr _ _ | rangeTo _ | rangeFrom _ | bool _
              | char _ | ordering _ | unit | enumVal _ _ | tuple _ | array _
              | bytes _ | optionVal _ | range _ _ | boxPtr _ _ | vec _ _ _ =>
                cases h_match

/-- Any `.deref` destination resolved by `resolvePlaceDestV2` (used by both
`evalStatementV2 .assign` and `writePlaceV2`) must originate from a `.mut`
reference or `.mut` raw pointer local whose pointee is sized and matches
`dstTy`, producing `.deref pt lay pv` with `layoutOfTyV2 pt = some lay`. -/
theorem resolvePlaceDestV2_deref_requires_mut_ptr
    (bodyLocals : List MirTy) (locals : List LocalSlot)
    (m : MirSemantics.MemoryState) (dst : Place) (dstTy : MirTy)
    (dest : PlaceDestV2) (h_proj : dst.projection = [.deref])
    (h_res : resolvePlaceDestV2 bodyLocals locals m dst dstTy = .ok dest) :
    ∃ ptrTy pt lay pv,
      MirSemantics.getElem? bodyLocals dst.localId = some ptrTy ∧
      (ptrTy = .ref .mut pt ∨ ptrTy = .rawPtr .mut pt) ∧
      isUnsizedTy pt = false ∧
      pt = dstTy ∧
      layoutOfTyV2 pt = some lay ∧
      dest = .deref pt lay pv := by
  dsimp only [resolvePlaceDestV2] at h_res
  rw [h_proj] at h_res
  dsimp only at h_res
  cases h_ty : MirSemantics.getElem? bodyLocals dst.localId with
  | none =>
    rw [h_ty] at h_res
    cases h_sl : MirSemantics.getElem? locals dst.localId <;>
      (rw [h_sl] at h_res; dsimp only at h_res; cases h_res)
  | some ptrTy =>
    rw [h_ty] at h_res
    cases h_sl : MirSemantics.getElem? locals dst.localId with
    | none => rw [h_sl] at h_res; dsimp only at h_res; cases h_res
    | some slot =>
      cases slot with
      | dead => rw [h_sl] at h_res; dsimp only at h_res; cases h_res
      | immediate _ | indirect _ =>
        rw [h_sl] at h_res
        cases ptrTy with
        | ref ptrMut pt =>
          dsimp only at h_res
          let ⟨h_m, h_us, h_eq, lay, pv, h_lay, h_d⟩ :=
            resolvePlaceDestV2_deref_branch pt dstTy ptrMut _ dest h_res
          subst h_m
          exact ⟨.ref .mut pt, pt, lay, pv, rfl, Or.inl rfl, h_us, h_eq,
            h_lay, h_d⟩
        | rawPtr ptrMut pt =>
          dsimp only at h_res
          let ⟨h_m, h_us, h_eq, lay, pv, h_lay, h_d⟩ :=
            resolvePlaceDestV2_deref_branch pt dstTy ptrMut _ dest h_res
          subst h_m
          exact ⟨.rawPtr .mut pt, pt, lay, pv, rfl, Or.inr rfl, h_us, h_eq,
            h_lay, h_d⟩
        | bool | int _ _ | unit | never | char | ordering | enum _
        | tuple _ | slice _ | str | array _ _ | rangeTo _ | rangeFrom _
        | unsupported | option _ | range _ | box _ | vec _ =>
          cases h_res
      | partialTuple _ =>
        rw [h_sl] at h_res
        cases ptrTy with
        | ref ptrMut pt =>
          dsimp only at h_res
          let ⟨h_m, h_us, h_eq, lay, pv, h_lay, h_d⟩ :=
            resolvePlaceDestV2_deref_branch pt dstTy ptrMut (.error .undefined)
              dest h_res
          subst h_m
          exact ⟨.ref .mut pt, pt, lay, pv, rfl, Or.inl rfl, h_us, h_eq,
            h_lay, h_d⟩
        | rawPtr ptrMut pt =>
          dsimp only at h_res
          let ⟨h_m, h_us, h_eq, lay, pv, h_lay, h_d⟩ :=
            resolvePlaceDestV2_deref_branch pt dstTy ptrMut (.error .undefined)
              dest h_res
          subst h_m
          exact ⟨.rawPtr .mut pt, pt, lay, pv, rfl, Or.inr rfl, h_us, h_eq,
            h_lay, h_d⟩
        | bool | int _ _ | unit | never | char | ordering | enum _
        | tuple _ | slice _ | str | array _ _ | rangeTo _ | rangeFrom _
        | unsupported | option _ | range _ | box _ | vec _ =>
          cases h_res

/-- Any `.deref` store accepted by `writePlaceV2` must originate from a
`.mut` reference or `.mut` raw pointer local whose pointee is sized and matches
`dstTy`. -/
theorem writePlaceV2_deref_requires_mut_ptr (bodyLocals : List MirTy)
    (locals : List LocalSlot) (m : MirSemantics.MemoryState) (dst : Place)
    (dstTy : MirTy) (val : Val) (locals' : List LocalSlot)
    (m' : MirSemantics.MemoryState)
    (h_proj : dst.projection = [.deref])
    (h_wp : writePlaceV2 bodyLocals locals m dst dstTy val =
      .ok (locals', m')) :
    ∃ ptrTy pt,
      MirSemantics.getElem? bodyLocals dst.localId = some ptrTy ∧
      (ptrTy = .ref .mut pt ∨ ptrTy = .rawPtr .mut pt) ∧
      isUnsizedTy pt = false ∧
      pt = dstTy := by
  dsimp only [writePlaceV2] at h_wp
  cases h_res : resolvePlaceDestV2 bodyLocals locals m dst dstTy with
  | error k => rw [h_res] at h_wp; cases h_wp
  | ok dest =>
    let ⟨ptrTy, pt, _, _, h_l, h_m, h_us, h_eq, _, _⟩ :=
      resolvePlaceDestV2_deref_requires_mut_ptr bodyLocals locals m dst dstTy
        dest h_proj h_res
    exact ⟨ptrTy, pt, h_l, h_m, h_us, h_eq⟩

/-- Every successful `evalStatementV2 .assign` targeting a `.deref` place
resolves a `.mut` reference or `.mut` raw pointer local matching sized `dstTy`,
evaluates `rv` to `val` satisfying `checkValV2 val dstTy = true`, stores into
`.deref pt lay pv`, and updates `st.mem` to the resulting memory `mem2`. -/
theorem evalStatementV2_assign_deref_requires_mut_ptr_and_checkVal
    (body : Body) (frame : FrameState) (m : MirSemantics.MemoryState)
    (callerMem : CallerMemory) (dst : Place) (rv : Rvalue)
    (st : MirSemantics.State)
    (h_proj : dst.projection = [.deref])
    (h_st : evalStatementV2 body frame m callerMem (.assign dst rv) =
      .step st) :
    ∃ dstTy ptrTy pt lay pv val locals1 mem1 locals2 mem2,
      placeStaticTyV2 body.locals dst = some dstTy ∧
      MirSemantics.getElem? body.locals dst.localId = some ptrTy ∧
      (ptrTy = .ref .mut pt ∨ ptrTy = .rawPtr .mut pt) ∧
      isUnsizedTy pt = false ∧
      pt = dstTy ∧
      layoutOfTyV2 pt = some lay ∧
      resolvePlaceDestV2 body.locals frame.locals m dst dstTy =
        .ok (.deref pt lay pv) ∧
      evalRvalueV2 body.locals frame.locals m dstTy rv =
        .ok (val, locals1, mem1) ∧
      writePlaceDestV2 locals1 mem1 (.deref pt lay pv) dstTy val =
        .ok (locals2, mem2) ∧
      checkValV2 val dstTy = true ∧
      st.mem = mem2 := by
  dsimp only [evalStatementV2] at h_st
  cases h_ty : placeStaticTyV2 body.locals dst with
  | none => rw [h_ty] at h_st; cases h_st
  | some dstTy =>
    rw [h_ty] at h_st
    dsimp only at h_st
    cases h_res : resolvePlaceDestV2 body.locals frame.locals m dst dstTy with
    | error k => rw [h_res] at h_st; cases h_st
    | ok dest =>
      rw [h_res] at h_st
      dsimp only at h_st
      cases h_ev : evalRvalueV2 body.locals frame.locals m dstTy rv with
      | error k => rw [h_ev] at h_st; cases h_st
      | ok res =>
        cases res with | mk val res =>
        cases res with | mk locals1 mem1 =>
        rw [h_ev] at h_st
        dsimp only at h_st
        cases h_wp : writePlaceDestV2 locals1 mem1 dest dstTy val with
        | error k => rw [h_wp] at h_st; cases h_st
        | ok res2 =>
          cases res2 with | mk locals2 mem2 =>
          rw [h_wp] at h_st
          dsimp only at h_st
          cases h_ov : checkAssignCopyHazardV2 body.locals frame.locals m dest
              dstTy rv with
          | error k => rw [h_ov] at h_st; cases h_st
          | ok u =>
            cases u
            rw [h_ov] at h_st
            dsimp only at h_st
            injection h_st with h_st_eq
            subst h_st_eq
            let ⟨ptrTy, pt, lay, pv, h_l, h_m, h_us, h_eq, h_lay, h_d⟩ :=
              resolvePlaceDestV2_deref_requires_mut_ptr body.locals frame.locals
                m dst dstTy dest h_proj h_res
            subst h_d
            exact ⟨dstTy, ptrTy, pt, lay, pv, val, locals1, mem1, locals2, mem2,
              rfl, h_l, h_m, h_us, h_eq, h_lay, h_res, h_ev, h_wp,
              writePlaceDestV2_requires_checkValV2 locals1 mem1
                (.deref pt lay pv) dstTy val locals2 mem2 h_wp, rfl⟩

/-- Lean-side operational invariant for Profile v2 `Assign` `.use` non-overlap
(matching `Miri/Interpreter/Place.lean:348-380`, `copyRuntimePlaceNoValidate` ->
`Allocation.copyRepeatedly` `nonoverlapping = true`): every successful
`evalStatementV2 .assign` copying a `BackendRepr::Memory` or padded type
(`isMemoryCopyReprTyV2 dstTy = true`) via `.use (.copy src)` guarantees that
whenever destination and source resolve to storage spans `dSpan` and `sSpan`,
`copySpansOverlapV2 dSpan sSpan = false`. -/
theorem evalStatementV2_assign_use_copy_nonoverlapping
    (body : Body) (frame : FrameState) (m : MirSemantics.MemoryState)
    (callerMem : CallerMemory) (dst src : Place) (st : MirSemantics.State)
    (dstTy : MirTy) (dest : PlaceDestV2) (dSpan sSpan : CopyPlaceSpanV2)
    (h_ty : placeStaticTyV2 body.locals dst = some dstTy)
    (h_memRepr : isMemoryCopyReprTyV2 dstTy = true)
    (h_res : resolvePlaceDestV2 body.locals frame.locals m dst dstTy = .ok dest)
    (h_dSpan : destCopySpanV2 frame.locals dest dstTy = some dSpan)
    (h_sSpan : srcPlaceCopySpanV2 body.locals frame.locals m src = some sSpan)
    (h_st : evalStatementV2 body frame m callerMem
      (.assign dst (.use (.copy src))) = .step st) :
    copySpansOverlapV2 dSpan sSpan = false := by
  dsimp only [evalStatementV2] at h_st
  rw [h_ty] at h_st
  dsimp only at h_st
  rw [h_res] at h_st
  dsimp only at h_st
  cases h_ev : evalRvalueV2 body.locals frame.locals m dstTy (.use (.copy src)) with
  | error k => rw [h_ev] at h_st; cases h_st
  | ok res =>
    cases res with | mk val res =>
    cases res with | mk locals1 mem1 =>
    rw [h_ev] at h_st
    dsimp only at h_st
    cases h_wp : writePlaceDestV2 locals1 mem1 dest dstTy val with
    | error k => rw [h_wp] at h_st; cases h_st
    | ok res2 =>
      cases res2 with | mk locals2 mem2 =>
      rw [h_wp] at h_st
      dsimp only [checkAssignCopyHazardV2] at h_st
      rw [h_memRepr, Bool.not_true, h_dSpan, h_sSpan] at h_st
      dsimp only at h_st
      cases h_ov : copySpansOverlapV2 dSpan sSpan with
      | true => rw [h_ov] at h_st; cases h_st
      | false => rfl

/-- Overflow pairs `(T, bool)` are rejected as Profile v2 pointees behind both
raw pointers and references (`isSupportedV2LocalTy`). -/
theorem overflowPair_not_addressable_v2 (mu : MirAst.Mutability)
    (w : IntWidth) (s : Bool) :
    isSupportedV2LocalTy (.rawPtr mu (.tuple [.int w s, .bool])) = false ∧
    isSupportedV2LocalTy (.ref mu (.tuple [.int w s, .bool])) = false :=
  ⟨rfl, rfl⟩

/-- Every normal Profile v2 return from `evalTerminatorV2` comes from a
non-cleanup `.return_` block, enforces caller-memory provenance containment,
pointee validity (`refsValidInMem`), mutable borrow disjointness, and snapshots
caller-visible memory. -/
theorem evalTerminatorV2_return_enforces_callerMem_validity_and_disjoint_spans
    (body : Body) (bb : BasicBlock) (frame : FrameState)
    (m : MirSemantics.MemoryState) (callerMem : CallerMemory) (rv : Out)
    (h_t : evalTerminatorV2 body bb frame m callerMem = .done (.returned rv)) :
    bb.terminator = .return_ ∧
    bb.cleanup = false ∧
    ∃ retTy,
      MirSemantics.getElem? body.locals 0 = some retTy ∧
      refsStayInCallerMem callerMem retTy rv.ret = true ∧
      refsValidInMem m retTy rv.ret = true ∧
      spansPairwiseDisjoint (refAccessSpans retTy rv.ret) = true ∧
      rv.callerMem = extractReturnMemoryV2 callerMem m frame.locals := by
  dsimp only [evalTerminatorV2] at h_t
  cases h_term : bb.terminator with
  | goto _ => rw [h_term] at h_t; cases h_t
  | unreachable => rw [h_term] at h_t; cases h_t
  | switchInt discr targets =>
    rw [h_term] at h_t
    dsimp only at h_t
    cases h_op : evalPrimitiveOperandV2 body.locals frame.locals m discr with
    | error k => rw [h_op] at h_t; dsimp only at h_t; cases h_t
    | ok res =>
      cases res with | mk discrVal res =>
      cases res with | mk localsAfterDiscr memAfterDiscr =>
      rw [h_op] at h_t
      dsimp only at h_t
      have h_tr_ne :
          ∀ tr : Except FaultKind BasicBlockId,
            (match tr with
             | .error k => StepResult.fault k
             | .ok target =>
               jumpToBlock { frame with locals := localsAfterDiscr }
                 memAfterDiscr callerMem target) =
              .done (.returned rv) → False := by
        intro tr h_eq
        cases tr with
        | error _ => cases h_eq
        | ok _ => cases h_eq
      exact False.elim (h_tr_ne _ h_t)
  | assert cond expected msg target _ =>
    rw [h_term] at h_t
    dsimp only at h_t
    cases h_op : evalPrimitiveOperandV2 body.locals frame.locals m cond with
    | error k => rw [h_op] at h_t; dsimp only at h_t; cases h_t
    | ok res =>
      cases res with | mk condVal res =>
      cases res with | mk locals1 mem1 =>
      rw [h_op] at h_t
      dsimp only at h_t
      cases condVal with
      | bool b =>
        dsimp only at h_t
        cases h_eq : (b == expected) with
        | true => rw [h_eq] at h_t; cases h_t
        | false =>
          rw [h_eq] at h_t
          cases msg with
          | overflow op => cases op <;> cases h_t
          | _ => cases h_t
      | scalar _ | char _ | ordering _ | unit | enumVal _ _ | ptr _
      | slicePtr _ _ | rangeTo _ | rangeFrom _ | tuple _ | array _
      | bytes _ | optionVal _ | range _ _ | boxPtr _ _ | vec _ _ _ =>
        dsimp only at h_t; cases h_t
  | coreCall op args dst cont unwind =>
    rw [h_term] at h_t
    cases cont with
    | none =>
      cases op with
      | panicAbort =>
        dsimp only at h_t
        cases h_emp : dst.projection.isEmpty with
        | false => rw [h_emp] at h_t; cases h_t
        | true =>
          rw [h_emp] at h_t
          cases h_dt : MirSemantics.getElem? body.locals dst.localId with
          | none =>
            rw [h_dt] at h_t
            cases h_sl : MirSemantics.getElem? frame.locals dst.localId <;>
              (rw [h_sl] at h_t; cases h_t)
          | some dt =>
            rw [h_dt] at h_t
            cases dt with
            | never =>
              cases h_sl : MirSemantics.getElem? frame.locals dst.localId with
              | none => rw [h_sl] at h_t; cases h_t
              | some slot =>
                rw [h_sl] at h_t
                cases slot with
                | dead | partialTuple _ => cases h_t
                | immediate _ | indirect _ =>
                  cases h_args :
                      evalArgOperandsV2 body.locals frame.locals m args with
                  | error k => rw [h_args] at h_t; cases h_t
                  | ok res =>
                    cases res with | mk typedArgs res =>
                    cases res with | mk locals1 mem1 =>
                    rw [h_args] at h_t
                    dsimp only at h_t
                    cases h_va : validatePanicAbortArgs mem1 typedArgs with
                    | error k => rw [h_va] at h_t; cases h_t
                    | ok u =>
                      cases u
                      rw [h_va] at h_t
                      cases h_t
            | int _ _ | bool | char | ordering | unit | enum _
            | ref _ _ | rawPtr _ _ | slice _ | str | array _ _
            | rangeTo _ | rangeFrom _ | tuple _ | option _ | range _
            | vec _ | box _ | unsupported =>
              cases h_sl : MirSemantics.getElem? frame.locals dst.localId <;>
                (rw [h_sl] at h_t; cases h_t)
      | _ => cases h_t
    | some target =>
      dsimp only at h_t
      cases h_emp : dst.projection.isEmpty with
      | false => rw [h_emp] at h_t; cases h_t
      | true =>
        rw [h_emp] at h_t
        cases h_dt : MirSemantics.getElem? body.locals dst.localId with
        | none => rw [h_dt] at h_t; dsimp only at h_t; cases h_t
        | some dstTy =>
          rw [h_dt] at h_t
          dsimp only at h_t
          cases h_args : evalArgOperandsV2 body.locals frame.locals m args with
          | error k => rw [h_args] at h_t; dsimp only at h_t; cases h_t
          | ok res =>
            cases res with | mk typedArgs res =>
            cases res with | mk locals1 mem1 =>
            rw [h_args] at h_t
            dsimp only at h_t
            have h_non_split :
                (match execCoreCallOpWithMem mem1 op typedArgs dstTy with
                 | .error k => MirSemantics.StepResult.fault k
                 | .ok (resVal, mem1') =>
                   match writePlaceV2 body.locals locals1 mem1' dst
                       dstTy resVal with
                   | .error k => .fault k
                   | .ok (locals2, mem2) =>
                     jumpToBlock { frame with locals := locals2 } mem2
                       callerMem target) ≠
                .done (.returned rv) := by
              intro h_eq
              cases h_op : execCoreCallOpWithMem mem1 op typedArgs dstTy with
              | error k => rw [h_op] at h_eq; dsimp only at h_eq; cases h_eq
              | ok resPair =>
                cases resPair with | mk resVal mem1' =>
                rw [h_op] at h_eq; dsimp only at h_eq
                cases h_wp :
                    writePlaceV2 body.locals locals1 mem1' dst dstTy resVal with
                | error k => rw [h_wp] at h_eq; dsimp only at h_eq; cases h_eq
                | ok res2 =>
                  cases res2 with | mk locals2 mem2 =>
                  rw [h_wp] at h_eq; cases h_eq
            cases op with
            | sliceSplitAt reqMut elem =>
              dsimp only at h_t
              cases h_sp :
                  execSliceSplitAtCall mem1 reqMut elem typedArgs dstTy with
              | ok resVal mem1' =>
                rw [h_sp] at h_t; dsimp only at h_t
                cases h_wp :
                    writePlaceV2 body.locals locals1 mem1' dst dstTy resVal with
                | error k => rw [h_wp] at h_t; dsimp only at h_t; cases h_t
                | ok res2 =>
                  cases res2 with | mk locals2 mem2 =>
                  rw [h_wp] at h_t; cases h_t
              | panic =>
                rw [h_sp] at h_t
                dsimp only [evalCorePanicAbort] at h_t
                cases h_t
              | fault k => rw [h_sp] at h_t; cases h_t
            | _ => exact False.elim (h_non_split h_t)
  | unwindResume | call _ _ _ _ _ | sysrootCall _ _ _ _ _ | unsupported =>
    rw [h_term] at h_t; cases h_t
  | return_ =>
    rw [h_term] at h_t
    dsimp only at h_t
    cases h_cl : bb.cleanup with
    | true => rw [h_cl] at h_t; cases h_t
    | false =>
      rw [h_cl] at h_t
      cases h_rt : MirSemantics.getElem? body.locals 0 with
      | none => rw [h_rt] at h_t; dsimp only at h_t; cases h_t
      | some retTy =>
        rw [h_rt] at h_t
        dsimp only at h_t
        have h_ret_ok :
            ∀ retRes : Except FaultKind Val,
              (match retRes with
               | .error k => MirSemantics.StepResult.fault k
               | .ok retVal =>
                 if hasEscapingRodataPtr callerMem m retTy retVal then
                   .fault .unsupported
                 else if !refsStayInCallerMem callerMem retTy retVal ||
                     !refsValidInMem m retTy retVal ||
                     !spansPairwiseDisjoint
                       (refAccessSpans retTy retVal) then
                   .fault .undefined
                 else
                   .done (TerminalOut.returned
                     ⟨retVal,
                       extractReturnMemoryV2 callerMem m frame.locals⟩) :
                 MirSemantics.StepResult MirSemantics.State TerminalOut) =
                (@MirSemantics.StepResult.done MirSemantics.State TerminalOut
                  (TerminalOut.returned rv)) →
              refsStayInCallerMem callerMem retTy rv.ret = true ∧
              refsValidInMem m retTy rv.ret = true ∧
              spansPairwiseDisjoint (refAccessSpans retTy rv.ret) = true ∧
              rv.callerMem =
                extractReturnMemoryV2 callerMem m frame.locals := by
          intro retRes h_match
          cases retRes with
          | error k => cases h_match
          | ok retVal =>
            dsimp only at h_match
            cases h0 : hasEscapingRodataPtr callerMem m retTy retVal with
            | true =>
              rw [h0, ite_eq_left rfl] at h_match; cases h_match
            | false =>
              rw [h0, ite_eq_right (fun h => by cases h)] at h_match
              cases h1 : refsStayInCallerMem callerMem retTy retVal with
              | false => rw [h1] at h_match; cases h_match
              | true =>
                cases h2 : refsValidInMem m retTy retVal with
                | false => rw [h1, h2] at h_match; cases h_match
                | true =>
                  cases h3 :
                      spansPairwiseDisjoint (refAccessSpans retTy retVal) with
                  | false => rw [h1, h2, h3] at h_match; cases h_match
                  | true =>
                    rw [h1, h2, h3] at h_match
                    injection h_match with h_out
                    injection h_out with h_rv
                    subst h_rv
                    exact ⟨h1, h2, h3, rfl⟩
        let ⟨h1, h2, h3, h4⟩ := h_ret_ok _ h_t
        exact ⟨rfl, rfl, retTy, rfl, h1, h2, h3, h4⟩

/-- Non-vacuity witness: `evalPtrToPtrCastV2` succeeds on `.mut -> .shared`. -/
theorem evalPtrToPtrCastV2_mut_to_shared_witness (pv : PtrVal) :
    evalPtrToPtrCastV2 (.rawPtr .mut .bool) (.ptr pv) (.rawPtr .shared .bool) =
      .ok (.ptr pv) := by
  dsimp only [evalPtrToPtrCastV2, isConstRawPtrTy, MirAst.Mutability.beq,
    isUnsizedTy]
  rfl

/-- Non-vacuity witness: `resolvePlaceDestV2` succeeds on `.deref` for a `.mut`
pointer. -/
theorem resolvePlaceDestV2_deref_bool_witness
    (m : MirSemantics.MemoryState) (pv : PtrVal) :
    ∃ lay,
      resolvePlaceDestV2 [.rawPtr .mut .bool] [.immediate (some (.ptr pv))] m
        { localId := 0, projection := [.deref] } .bool =
          .ok (.deref .bool lay pv) := by
  refine ⟨⟨1, 0⟩, ?_⟩
  dsimp only [resolvePlaceDestV2, MirSemantics.getElem?, isUnsizedTy,
    MirTy.beq, MirAst.Mutability.beq, layoutOfTyV2, layoutOfTy]
  rfl

/-- Non-vacuity witness: `writePlaceDestV2` succeeds on `.local`. -/
theorem writePlaceDestV2_local_bool_witness (m : MirSemantics.MemoryState) :
    writePlaceDestV2 [.immediate (some (.bool false))] m (.local 0) .bool
        (.bool true) =
      .ok ([.immediate (some (.bool true))], m) := by
  dsimp only [writePlaceDestV2, checkValV2, MirSemantics.getElem?,
    MirSemantics.setElem?]
  rfl

end Anneal.MirCorrespondence
