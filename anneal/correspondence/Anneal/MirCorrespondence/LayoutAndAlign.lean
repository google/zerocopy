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
     on `size = 0` (which short-circuits before checking `isAligned` or
     liveness) paired with `zst_day1_alignLog2_zero` and
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
  | ref _ _ | rawPtr _ _ | unsupported => dsimp only [layoutOfTy] at h; cases h

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
  | ref _ _ | rawPtr _ _ | unsupported => dsimp only [layoutOfTy] at h; cases h

/-- `Trusted.MirSemantics.readBytes` short-circuits `size = 0` to `.ok []`
before inspecting `findAllocation`, allocation liveness, bounds, or
`isAligned`. -/
theorem readBytes_zero_size (m : MirSemantics.MemoryState) (place : MemPlace)
    (alignLog2 : Nat) :
    readBytes m place 0 alignLog2 = .ok [] :=
  rfl

/-- `Trusted.MirSemantics.writeBytes` short-circuits empty writes (`bytes = []`)
to `.ok m` before inspecting `findAllocation`, allocation liveness, bounds,
`isAligned`, or mutability. -/
theorem writeBytes_zero_size (m : MirSemantics.MemoryState) (place : MemPlace)
    (alignLog2 : Nat) :
    writeBytes m place alignLog2 [] = .ok m :=
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
`loadIndirect`, `storeIndirect`, and `deinitIndirect` reduce without alignment
divergence. -/
theorem zst_day1_indirect_and_miri_align_agree {Prov ProvExtra : Type}
    [PointerProvenance Prov]
    (ty : MirTy) (lay : MirSemantics.LayoutData)
    (h_lay : layoutOfTy ty = some lay) (h_sz : lay.size = 0)
    (m : MirSemantics.MemoryState) (place : MemPlace)
    (a : MirSemantics.Allocation) (off : Nat)
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
  refine ⟨h_al, ?_, ?_, ?_, ?_, ?_⟩
  · rw [h_al]
    dsimp only [MirSemantics.isAligned]
    rw [(nat_ble_true_iff 0 a.alignLog2).2 (Nat.zero_le _), Bool.true_and,
      show Nat.pow 2 0 = 1 from rfl]
    change Nat.beq (HMod.hMod off 1) 0 = true
    rw [Nat.mod_one]
    rfl
  · rw [h_al]
    exact checkPtrAlign_alignOne ptr enforce resolve lookup hook
  · dsimp only [loadIndirect]
    rw [h_lay]
    dsimp only
    rw [h_sz]
    rfl
  · dsimp only [deinitIndirect, writeUninit]
    rw [h_lay]
    dsimp only
    rw [h_sz]
    rfl
  · intro v h_enc
    dsimp only [storeIndirect]
    rw [h_lay]
    dsimp only
    rw [h_enc]
    rfl

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
(`m' = m`) or a concrete updated allocation in `m.allocations`. -/
private theorem writeBytes_ok_elim {m m' : MirSemantics.MemoryState}
    {place : MemPlace} {alignLog2 : Nat} {bs : List AllocByte}
    (h_w : writeBytes m place alignLog2 bs = .ok m') :
    (bs = [] ∧ m' = m) ∨
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
  cases h_len0 : Nat.beq bs.length 0 with
  | true =>
    rw [h_len0] at h_w
    injection h_w with h_m'
    exact Or.inl
      ⟨List.eq_nil_of_length_eq_zero ((nat_beq_true_iff _ _).1 h_len0),
        h_m'.symm⟩
  | false =>
    rw [h_len0] at h_w
    have h_ne : bs ≠ [] := fun h => by rw [h] at h_len0; cases h_len0
    cases h_fa : findAllocation place.allocId m.allocations with
    | none => rw [h_fa] at h_w; dsimp only at h_w; cases h_w
    | some a =>
      rw [h_fa] at h_w
      dsimp only at h_w
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
    rw [h.2]
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
  | inl h => rw [h.1]; rfl
  | inr h =>
    let ⟨a, h_ne, h_fa, h_live, h_ib, h_al, _, h_m'⟩ := h
    subst h_m'
    dsimp only [readBytes]
    have h_l0 : Nat.beq bs.length 0 = false := by
      cases bs with
      | nil => exact False.elim (h_ne rfl)
      | cons _ _ => rfl
    rw [h_l0]
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
    rw [h_fa']
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
  | inl h => rw [h.2]
  | inr h =>
    let ⟨a, _, h_fa, _, h_ib, _, _, h_m'⟩ := h
    subst h_m'
    dsimp only [readBytes]
    cases Nat.beq sz2 0 with
    | true => rfl
    | false =>
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
      rw [h_fa', h_fa]
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
    | inl h => rw [h.2]
    | inr h =>
      let ⟨a, _, h_fa, _, _, _, _, h_m'⟩ := h
      subst h_m'
      have h_aid : a.allocId = place1.allocId := (findAllocation_mem h_fa).2
      exact findAllocation_replaceAllocation_ne _ id2
        (by rw [h_aid]; exact h_ne) m.allocations
  refine ⟨h_find, fun off2 sz2 align2 => ?_⟩
  dsimp only [readBytes]
  cases Nat.beq sz2 0 with
  | true => rfl
  | false => rw [h_find]

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
  cases bs with
  | nil => exact False.elim (h_ne rfl)
  | cons b rest =>
    dsimp only [List.length, Nat.beq]
    rw [h_fa]
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
              rw [show Nat.beq (k + 1) 0 = false from rfl, ite_false_eq, h_dead]
              rfl
          · intro off al bs h_ne
            cases bs with
            | nil => exact False.elim (h_ne rfl)
            | cons b rest =>
              dsimp only [writeBytes]
              rw [show Nat.beq (b :: rest).length 0 = false from rfl,
                ite_false_eq, h_dead]
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

end Anneal.MirCorrespondence
