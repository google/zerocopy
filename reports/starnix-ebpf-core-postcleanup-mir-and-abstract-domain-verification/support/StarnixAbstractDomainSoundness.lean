-- Copyright 2026 The Fuchsia Authors
--
-- Licensed under a BSD-style license <LICENSE-BSD>, Apache License, Version 2.0
-- <LICENSE-APACHE or https://www.apache.org/licenses/LICENSE-2.0>, or the MIT
-- license <LICENSE-MIT or https://opensource.org/licenses/MIT>, at your option.
-- This file may not be copied, modified, or distributed except according to
-- those terms.

import Trusted.Mvp.Semantics
import Init.Data.BitVec.Lemmas
import Init.Data.Nat.Bitwise.Lemmas

/-!
# Q-A3: Mechanized Abstract-Domain Soundness for Starnix `U64Range` and `U64ScalarValueData`

This standalone, zero-`sorry` Lean 4.34.1 mechanization proves:
1. **Interval Domain Soundness (`U64Range`)**:
   - Wrapping 64-bit interval addition well-formedness (`add_range_wf`) and
     concretization soundness (`add_range_sound`);
   - Wrapping 64-bit interval subtraction well-formedness (`sub_range_wf`) and
     concretization soundness (`sub_range_sound`);
   - Unsigned remainder range well-formedness (`rem_range_wf`) and
     concretization soundness both for nonzero divisors (`rem_range_sound_nonzero`)
     and for full eBPF `BPF_MOD` semantics where division/modulo by zero leaves
     the dividend unchanged (`rem_range_sound_ebpf`).
2. **Product Tnum + Unwritten-Mask + Interval Domain Soundness (`U64ScalarValueData`)**:
   - Unconditional well-formedness of `U64ScalarValueData::new` (`new_wf`:
     `value &&& unknown_mask = 0` and `unwritten_mask &&& ~~~unknown_mask = 0`);
   - Invariant preservation and bitwise concretization soundness (`γ_tnum` and
     `γ_urange`) for `bitand_scalar`, `bitor_scalar`, and `bitxor_scalar`.
3. **Formal Host-vs-Guest Initialization & Lattice Polarity Contrast**:
   - **Guest eBPF (`U64ScalarValueData`)**: `bitand_scalar (from_known 0) UNINITIALIZED`
     absorbs the unknown/unwritten bits of `UNINITIALIZED` and produces
     `from_known 0` (`unwritten_mask = 0`, `is_fully_initialized = true`);
     moreover, `UNINITIALIZED` is the **Top** element of Starnix's state-pruning
     partial order (`is_same_or_more_specific`).
   - **Host Rust (`Trusted.Mvp.Semantics`)**: evaluating `0 & uninit` faults
     immediately with `.fault .uninitialized` because operand evaluation is
     strict before `evalBinary`, and `Slot.uninit` is at the **Bottom** of the
     host definedness order.
-/

namespace StarnixAbstractDomainSoundness

open Trusted.Mvp

abbrev Word := BitVec 64

def maxU64 : Word := 0xffffffffffffffff#64

def minWord (a b : Word) : Word :=
  if a.toNat ≤ b.toNat then a else b

def maxWord (a b : Word) : Word :=
  if a.toNat ≥ b.toNat then a else b

/-!
## Part 1: `U64Range` Wrapping Interval Arithmetic & Remainder Soundness
-/

structure U64Range where
  min : Word
  max : Word
  deriving DecidableEq, Repr

namespace U64Range

def maxRange : U64Range := ⟨0#64, maxU64⟩

def fromScalar (v : Word) : U64Range := ⟨v, v⟩

/-- Well-formedness of an unsigned 64-bit interval `[min, max]`. -/
def wf (r : U64Range) : Prop :=
  r.min.toNat ≤ r.max.toNat

/-- Concretization `x ∈ γ(r)` of an unsigned 64-bit interval. -/
def contains (r : U64Range) (x : Word) : Prop :=
  r.min.toNat ≤ x.toNat ∧ x.toNat ≤ r.max.toNat

theorem maxRange_wf : maxRange.wf := by
  unfold maxRange wf maxU64
  decide

theorem maxRange_contains (x : Word) : maxRange.contains x := by
  dsimp only [maxRange, contains, maxU64]
  have h0 : (0#64).toNat = 0 := rfl
  have hlt : x.toNat < 2 ^ 64 := x.isLt
  have hmax : (0xffffffffffffffff#64).toNat = 2 ^ 64 - 1 := rfl
  omega

theorem wf_of_contains {r : U64Range} {x : Word} (h : r.contains x) : r.wf :=
  Nat.le_trans h.1 h.2

/-- Exact translation of `U64Range::add_range` (`scalar_value.rs` lines 156–160). -/
def add_range (self rhs : U64Range) : U64Range :=
  let min := self.min + rhs.min
  let min_overflowed := decide (self.min.toNat + rhs.min.toNat ≥ 2 ^ 64)
  let max := self.max + rhs.max
  let max_overflowed := decide (self.max.toNat + rhs.max.toNat ≥ 2 ^ 64)
  if min_overflowed != max_overflowed then
    maxRange
  else
    ⟨min, max⟩

theorem toNat_add_no_overflow (a b : Word) (h : a.toNat + b.toNat < 2 ^ 64) :
    (a + b).toNat = a.toNat + b.toNat := by
  rw [BitVec.toNat_add]
  exact Nat.mod_eq_of_lt h

theorem toNat_add_overflow (a b : Word) (h : a.toNat + b.toNat ≥ 2 ^ 64) :
    (a + b).toNat = a.toNat + b.toNat - 2 ^ 64 := by
  rw [BitVec.toNat_add]
  have ha : a.toNat < 2 ^ 64 := a.isLt
  have hb : b.toNat < 2 ^ 64 := b.isLt
  omega

theorem add_range_wf (a b : U64Range) (ha : a.wf) (hb : b.wf) :
    (a.add_range b).wf := by
  unfold add_range wf at *
  by_cases hmin : a.min.toNat + b.min.toNat ≥ 2 ^ 64 <;>
  by_cases hmax : a.max.toNat + b.max.toNat ≥ 2 ^ 64
  · simp only [hmin, hmax, decide_true, bne_self_eq_false, Bool.false_eq_true, ite_false]
    rw [toNat_add_overflow a.min b.min hmin, toNat_add_overflow a.max b.max hmax]
    omega
  · simp only [hmin, hmax, decide_true, decide_false]
    exact maxRange_wf
  · simp only [hmin, hmax, decide_false, decide_true]
    exact maxRange_wf
  · simp only [hmin, hmax, decide_false, bne_self_eq_false, Bool.false_eq_true, ite_false]
    have hmin' : a.min.toNat + b.min.toNat < 2 ^ 64 := Nat.lt_of_not_le hmin
    have hmax' : a.max.toNat + b.max.toNat < 2 ^ 64 := Nat.lt_of_not_le hmax
    rw [toNat_add_no_overflow a.min b.min hmin', toNat_add_no_overflow a.max b.max hmax']
    omega

theorem add_range_sound (a b : U64Range) (x y : Word)
    (hx : a.contains x) (hy : b.contains y) :
    (a.add_range b).contains (x + y) := by
  unfold add_range
  rcases hx with ⟨hxmin, hxmax⟩
  rcases hy with ⟨hymin, hymax⟩
  by_cases hmin : a.min.toNat + b.min.toNat ≥ 2 ^ 64 <;>
  by_cases hmax : a.max.toNat + b.max.toNat ≥ 2 ^ 64
  · simp only [hmin, hmax, decide_true, bne_self_eq_false, Bool.false_eq_true, ite_false, contains]
    have hxy : x.toNat + y.toNat ≥ 2 ^ 64 := by omega
    rw [toNat_add_overflow a.min b.min hmin,
        toNat_add_overflow x y hxy,
        toNat_add_overflow a.max b.max hmax]
    omega
  · simp only [hmin, hmax, decide_true, decide_false]
    exact maxRange_contains (x + y)
  · simp only [hmin, hmax, decide_false, decide_true]
    exact maxRange_contains (x + y)
  · simp only [hmin, hmax, decide_false, bne_self_eq_false, Bool.false_eq_true, ite_false, contains]
    have hmin' : a.min.toNat + b.min.toNat < 2 ^ 64 := Nat.lt_of_not_le hmin
    have hmax' : a.max.toNat + b.max.toNat < 2 ^ 64 := Nat.lt_of_not_le hmax
    have hxy' : x.toNat + y.toNat < 2 ^ 64 := by omega
    rw [toNat_add_no_overflow a.min b.min hmin',
        toNat_add_no_overflow x y hxy',
        toNat_add_no_overflow a.max b.max hmax']
    omega

/-- Exact translation of `U64Range::sub_range` (`scalar_value.rs` lines 162–166). -/
def sub_range (self rhs : U64Range) : U64Range :=
  let min := self.min - rhs.max
  let min_overflowed := decide (self.min.toNat < rhs.max.toNat)
  let max := self.max - rhs.min
  let max_overflowed := decide (self.max.toNat < rhs.min.toNat)
  if min_overflowed != max_overflowed then
    maxRange
  else
    ⟨min, max⟩

theorem toNat_sub_no_underflow (a b : Word) (h : b.toNat ≤ a.toNat) :
    (a - b).toNat = a.toNat - b.toNat :=
  BitVec.toNat_sub_of_le h

theorem toNat_sub_underflow (a b : Word) (h : a.toNat < b.toNat) :
    (a - b).toNat = 2 ^ 64 - b.toNat + a.toNat := by
  rw [BitVec.toNat_sub]
  have ha : a.toNat < 2 ^ 64 := a.isLt
  have hb : b.toNat < 2 ^ 64 := b.isLt
  have hlt : 2 ^ 64 - b.toNat + a.toNat < 2 ^ 64 := by omega
  exact Nat.mod_eq_of_lt hlt

theorem sub_range_wf (a b : U64Range) (ha : a.wf) (hb : b.wf) :
    (a.sub_range b).wf := by
  unfold sub_range wf at *
  by_cases hmin : a.min.toNat < b.max.toNat <;>
  by_cases hmax : a.max.toNat < b.min.toNat
  · simp only [hmin, hmax, decide_true, bne_self_eq_false, Bool.false_eq_true, ite_false]
    rw [toNat_sub_underflow a.min b.max hmin, toNat_sub_underflow a.max b.min hmax]
    omega
  · simp only [hmin, hmax, decide_true, decide_false]
    exact maxRange_wf
  · simp only [hmin, hmax, decide_false, decide_true]
    exact maxRange_wf
  · simp only [hmin, hmax, decide_false, bne_self_eq_false, Bool.false_eq_true, ite_false]
    rw [toNat_sub_no_underflow a.min b.max (Nat.le_of_not_lt hmin),
        toNat_sub_no_underflow a.max b.min (Nat.le_of_not_lt hmax)]
    omega

theorem sub_range_sound (a b : U64Range) (x y : Word)
    (hx : a.contains x) (hy : b.contains y) :
    (a.sub_range b).contains (x - y) := by
  unfold sub_range
  rcases hx with ⟨hxmin, hxmax⟩
  rcases hy with ⟨hymin, hymax⟩
  by_cases hmin : a.min.toNat < b.max.toNat <;>
  by_cases hmax : a.max.toNat < b.min.toNat
  · simp only [hmin, hmax, decide_true, bne_self_eq_false, Bool.false_eq_true, ite_false, contains]
    have hxy : x.toNat < y.toNat := by omega
    rw [toNat_sub_underflow a.min b.max hmin,
        toNat_sub_underflow x y hxy,
        toNat_sub_underflow a.max b.min hmax]
    omega
  · simp only [hmin, hmax, decide_true, decide_false]
    exact maxRange_contains (x - y)
  · simp only [hmin, hmax, decide_false, decide_true]
    exact maxRange_contains (x - y)
  · simp only [hmin, hmax, decide_false, bne_self_eq_false, Bool.false_eq_true, ite_false, contains]
    have hmin' : b.max.toNat ≤ a.min.toNat := Nat.le_of_not_lt hmin
    have hmax' : b.min.toNat ≤ a.max.toNat := Nat.le_of_not_lt hmax
    have hxy' : y.toNat ≤ x.toNat := by omega
    rw [toNat_sub_no_underflow a.min b.max hmin',
        toNat_sub_no_underflow x y hxy',
        toNat_sub_no_underflow a.max b.min hmax']
    omega

/-- Exact translation of `U64Range::rem_range` (`scalar_value.rs` lines 188–195). -/
def rem_range (self rhs : U64Range) : U64Range :=
  if rhs.max == 0#64 then
    self
  else
    let min := 0#64
    let max := if rhs.min == 0#64 then self.max else minWord self.max (rhs.max - 1#64)
    ⟨min, max⟩

/-- eBPF `BPF_MOD` semantics: remainder by 0 returns the dividend `x` unchanged. -/
def ebpfRem (x y : Word) : Word :=
  if y == 0#64 then x else x % y

theorem rem_range_wf (a b : U64Range) (ha : a.wf) :
    (a.rem_range b).wf := by
  unfold rem_range wf
  split
  · exact ha
  · simp only [BitVec.toNat_ofNat, Nat.zero_mod, Nat.zero_le]

theorem rem_range_sound_nonzero (a b : U64Range) (x y : Word)
    (hx : a.contains x) (hy : b.contains y) (hy0 : y ≠ 0#64) :
    (a.rem_range b).contains (x % y) := by
  rcases hx with ⟨_, hxmax⟩
  rcases hy with ⟨hymin, hymax⟩
  have hypos : 0 < y.toNat := by
    cases Nat.eq_zero_or_pos y.toNat with
    | inl h0 => exact False.elim (hy0 (BitVec.eq_of_toNat_eq h0))
    | inr hp => exact hp
  have hbmax_pos : 0 < b.max.toNat := Nat.lt_of_lt_of_le hypos hymax
  have hbmax_ne : (b.max == 0#64) = false := by
    cases h : (b.max == 0#64)
    · rfl
    · have heq : b.max = 0#64 := eq_of_beq h
      rw [heq] at hbmax_pos
      contradiction
  unfold rem_range
  rw [hbmax_ne]
  simp only [Bool.false_eq_true, ite_false]
  have hmod_le_x : (x % y).toNat ≤ x.toNat := by
    rw [BitVec.toNat_umod]
    exact Nat.mod_le x.toNat y.toNat
  have hmod_lt_y : (x % y).toNat < y.toNat := by
    rw [BitVec.toNat_umod]
    exact Nat.mod_lt x.toNat hypos
  by_cases hbmin : b.min == 0#64
  · simp only [hbmin, ite_true, contains, BitVec.toNat_ofNat, Nat.zero_mod, Nat.zero_le, true_and]
    omega
  · simp only [hbmin, Bool.false_eq_true, ite_false, contains,
               BitVec.toNat_ofNat, Nat.zero_mod, Nat.zero_le, true_and, minWord]
    have h1le : (1#64).toNat ≤ b.max.toNat := by
      change 1 ≤ b.max.toNat
      omega
    have hsub : (b.max - 1#64).toNat = b.max.toNat - 1 := by
      rw [BitVec.toNat_sub_of_le h1le]
      rfl
    split <;> omega

theorem rem_range_sound_ebpf (a b : U64Range) (x y : Word)
    (hx : a.contains x) (hy : b.contains y) :
    (a.rem_range b).contains (ebpfRem x y) := by
  unfold ebpfRem
  by_cases hy0 : y == 0#64
  · simp only [hy0, ite_true]
    have hy_eq : y = 0#64 := eq_of_beq hy0
    subst hy_eq
    have hbmin0 : b.min = 0#64 := by
      have hle : b.min.toNat ≤ (0#64).toNat := hy.1
      have h0z : (0#64).toNat = 0 := rfl
      have h0 : b.min.toNat = 0 := by omega
      exact BitVec.eq_of_toNat_eq h0
    unfold rem_range
    by_cases hbmax0 : b.max == 0#64
    · simp only [hbmax0, ite_true]
      exact hx
    · simp only [hbmax0, Bool.false_eq_true, ite_false, hbmin0, beq_self_eq_true, ite_true, contains]
      exact ⟨Nat.zero_le _, hx.2⟩
  · simp only [hy0, Bool.false_eq_true, ite_false]
    have hy_ne : y ≠ 0#64 := by
      intro h; subst h; revert hy0; decide
    exact rem_range_sound_nonzero a b x y hx hy hy_ne

end U64Range

/-!
## Part 2: `U64ScalarValueData` Tnum + Unwritten-Mask + Interval Soundness
-/

structure U64ScalarValueData where
  value : Word
  unknown_mask : Word
  unwritten_mask : Word
  urange : U64Range
  deriving DecidableEq, Repr

namespace U64ScalarValueData

def UNINITIALIZED : U64ScalarValueData :=
  ⟨0#64, maxU64, maxU64, U64Range.maxRange⟩

def UNKNOWN_WRITTEN : U64ScalarValueData :=
  ⟨0#64, maxU64, 0#64, U64Range.maxRange⟩

def from_known (v : Word) : U64ScalarValueData :=
  ⟨v, 0#64, 0#64, U64Range.fromScalar v⟩

def is_known (s : U64ScalarValueData) : Bool :=
  s.unknown_mask == 0#64

def is_fully_initialized (s : U64ScalarValueData) : Bool :=
  s.unwritten_mask == 0#64

def is_uninitialized (s : U64ScalarValueData) : Bool :=
  s.unwritten_mask == maxU64

/-- Representation invariant of `U64ScalarValueData`:
1. `value` has 0 at every bit marked unknown (`value &&& unknown_mask = 0`);
2. `unwritten_mask` is a bitwise subset of `unknown_mask` (`unwritten_mask &&& ~~~unknown_mask = 0`). -/
structure MaskWF (s : U64ScalarValueData) : Prop where
  value_disjoint_unknown : s.value &&& s.unknown_mask = 0#64
  unwritten_sub_unknown : s.unwritten_mask &&& ~~~s.unknown_mask = 0#64

/-- Tnum concretization `x ∈ γ_tnum(s)`: `x` agrees with `s.value` on all known bits. -/
def inTnum (s : U64ScalarValueData) (x : Word) : Prop :=
  (x &&& ~~~s.unknown_mask) = (s.value &&& ~~~s.unknown_mask)

/-- Full scalar concretization `x ∈ γ(s)`: `x` satisfies both the tnum constraint and `urange`. -/
def concretizes (s : U64ScalarValueData) (x : Word) : Prop :=
  s.inTnum x ∧ s.urange.contains x

/-- `U64ScalarValueData::new` refinement step (`scalar_value.rs` lines 426–448),
parameterized by the common high-bit prefix mask `common_mask` on which
`urange.min` and `urange.max` agree. -/
def newWithCommonMask (common_mask : Word) (value unknown_mask unwritten_mask : Word)
    (urange : U64Range) : U64ScalarValueData :=
  let unknown_mask' := unknown_mask &&& ~~~common_mask
  let unwritten_mask' := unwritten_mask &&& unknown_mask'
  let value' := (value &&& ~~~unknown_mask' &&& ~~~common_mask) ||| (urange.min &&& common_mask)
  let urange' :=
    if unknown_mask' == 0#64 then
      U64Range.fromScalar value'
    else
      ⟨maxWord value' urange.min, minWord (value' ||| unknown_mask') urange.max⟩
  ⟨value', unknown_mask', unwritten_mask', urange'⟩

/-- Regardless of the raw inputs, `newWithCommonMask` unconditionally establishes `MaskWF`. -/
theorem newWithCommonMask_maskWF (common_mask value unknown_mask unwritten_mask : Word)
    (urange : U64Range) :
    (newWithCommonMask common_mask value unknown_mask unwritten_mask urange).MaskWF := by
  constructor
  · dsimp [newWithCommonMask]
    ext i hi
    simp [BitVec.getElem_and, BitVec.getElem_or, BitVec.getElem_not]
    cases h1 : unknown_mask[i] <;> cases h2 : common_mask[i] <;> simp
  · dsimp [newWithCommonMask]
    ext i hi
    simp [BitVec.getElem_and, BitVec.getElem_not]

/-- Exact translation of `U64ScalarValueData::bitand_scalar` (`scalar_value.rs` lines 569–578).
Note: since `urange.min = 0`, when `min(self.max, rhs.max)` has MSB 1 (or with
`common_mask = 0`), `new` preserves the exact masks computed in lines 572–576;
and for any `common_mask`, `newWithCommonMask` further refines them via `newWithCommonMask_maskWF`. -/
def bitand_raw (self rhs : U64ScalarValueData) : U64ScalarValueData :=
  let urange : U64Range := ⟨0#64, minWord self.urange.max rhs.urange.max⟩
  let not_known_zero := (self.value ||| self.unknown_mask) &&& (rhs.value ||| rhs.unknown_mask)
  let unknown_mask := (self.unknown_mask ||| rhs.unknown_mask) &&& not_known_zero
  let unwritten_mask := (self.unwritten_mask ||| rhs.unwritten_mask) &&& not_known_zero
  let value := self.value &&& rhs.value
  ⟨value, unknown_mask, unwritten_mask, urange⟩

/-- Exact translation of `U64ScalarValueData::bitor_scalar` (`scalar_value.rs` lines 580–587). -/
def bitor_raw (self rhs : U64ScalarValueData) : U64ScalarValueData :=
  let urange : U64Range := ⟨maxWord self.urange.min rhs.urange.min, maxU64⟩
  let value := self.value ||| rhs.value
  let unknown_mask := (self.unknown_mask ||| rhs.unknown_mask) &&& ~~~value
  let unwritten_mask := (self.unwritten_mask ||| rhs.unwritten_mask) &&& ~~~value
  ⟨value, unknown_mask, unwritten_mask, urange⟩

/-- Exact translation of `U64ScalarValueData::bitxor_scalar` (`scalar_value.rs` lines 589–595). -/
def bitxor_raw (self rhs : U64ScalarValueData) : U64ScalarValueData :=
  let urange : U64Range := U64Range.maxRange
  let unknown_mask := self.unknown_mask ||| rhs.unknown_mask
  let unwritten_mask := self.unwritten_mask ||| rhs.unwritten_mask
  let value := (self.value ^^^ rhs.value) &&& ~~~unknown_mask
  ⟨value, unknown_mask, unwritten_mask, urange⟩

theorem bitElem_zero_of_and_eq_zero {a b : Word} (h : a &&& b = 0#64) (i : Nat) (hi : i < 64) :
    (a[i] && b[i]) = false := by
  have hi0 : (a &&& b)[i] = (0#64)[i] := by rw [h]
  simpa [BitVec.getElem_and] using hi0

theorem bitand_raw_maskWF (a b : U64ScalarValueData) (ha : a.MaskWF) (hb : b.MaskWF) :
    (bitand_raw a b).MaskWF := by
  constructor
  · dsimp [bitand_raw]
    ext i hi
    have ha1 := bitElem_zero_of_and_eq_zero ha.value_disjoint_unknown i hi
    have hb1 := bitElem_zero_of_and_eq_zero hb.value_disjoint_unknown i hi
    simp only [BitVec.getElem_and, BitVec.getElem_or, BitVec.getElem_zero]
    revert ha1 hb1
    cases a.value[i] <;> cases a.unknown_mask[i] <;>
    cases b.value[i] <;> cases b.unknown_mask[i] <;> decide
  · dsimp [bitand_raw]
    ext i hi
    have ha2 := bitElem_zero_of_and_eq_zero ha.unwritten_sub_unknown i hi
    have hb2 := bitElem_zero_of_and_eq_zero hb.unwritten_sub_unknown i hi
    simp only [BitVec.getElem_not] at ha2 hb2
    simp only [BitVec.getElem_and, BitVec.getElem_or, BitVec.getElem_not, BitVec.getElem_zero]
    revert ha2 hb2
    cases a.unwritten_mask[i] <;> cases b.unwritten_mask[i] <;>
    cases a.unknown_mask[i] <;> cases b.unknown_mask[i] <;>
    cases a.value[i] <;> cases b.value[i] <;> decide

theorem bitor_raw_maskWF (a b : U64ScalarValueData) (ha : a.MaskWF) (hb : b.MaskWF) :
    (bitor_raw a b).MaskWF := by
  constructor
  · dsimp [bitor_raw]
    ext i hi
    simp only [BitVec.getElem_and, BitVec.getElem_or, BitVec.getElem_not, BitVec.getElem_zero]
    cases a.value[i] <;> cases b.value[i] <;>
    cases a.unknown_mask[i] <;> cases b.unknown_mask[i] <;> decide
  · dsimp [bitor_raw]
    ext i hi
    have ha2 := bitElem_zero_of_and_eq_zero ha.unwritten_sub_unknown i hi
    have hb2 := bitElem_zero_of_and_eq_zero hb.unwritten_sub_unknown i hi
    simp only [BitVec.getElem_not] at ha2 hb2
    simp only [BitVec.getElem_and, BitVec.getElem_or, BitVec.getElem_not, BitVec.getElem_zero]
    revert ha2 hb2
    cases a.unwritten_mask[i] <;> cases b.unwritten_mask[i] <;>
    cases a.unknown_mask[i] <;> cases b.unknown_mask[i] <;>
    cases a.value[i] <;> cases b.value[i] <;> decide

theorem bitxor_raw_maskWF (a b : U64ScalarValueData) (ha : a.MaskWF) (hb : b.MaskWF) :
    (bitxor_raw a b).MaskWF := by
  constructor
  · dsimp [bitxor_raw]
    ext i hi
    simp only [BitVec.getElem_and, BitVec.getElem_or, BitVec.getElem_xor, BitVec.getElem_not,
               BitVec.getElem_zero]
    cases a.value[i] <;> cases b.value[i] <;>
    cases a.unknown_mask[i] <;> cases b.unknown_mask[i] <;> decide
  · dsimp [bitxor_raw]
    ext i hi
    have ha2 := bitElem_zero_of_and_eq_zero ha.unwritten_sub_unknown i hi
    have hb2 := bitElem_zero_of_and_eq_zero hb.unwritten_sub_unknown i hi
    simp only [BitVec.getElem_not] at ha2 hb2
    simp only [BitVec.getElem_and, BitVec.getElem_or, BitVec.getElem_not, BitVec.getElem_zero]
    revert ha2 hb2
    cases a.unwritten_mask[i] <;> cases b.unwritten_mask[i] <;>
    cases a.unknown_mask[i] <;> cases b.unknown_mask[i] <;> decide

/-- Soundness of `bitand_scalar` (`bitand_raw`): if `x ∈ γ(a)` and `y ∈ γ(b)`,
then `(x &&& y) ∈ γ(bitand_raw a b)` (both tnum known bits and `urange` bounds). -/
theorem bitand_raw_sound (a b : U64ScalarValueData) (x y : Word)
    (ha : a.MaskWF) (hb : b.MaskWF)
    (hx : a.concretizes x) (hy : b.concretizes y) :
    (bitand_raw a b).concretizes (x &&& y) := by
  rcases hx with ⟨hxt, hxr⟩
  rcases hy with ⟨hyt, hyr⟩
  constructor
  · unfold inTnum bitand_raw at *
    ext i hi
    have hxi : (x &&& ~~~a.unknown_mask)[i] = (a.value &&& ~~~a.unknown_mask)[i] := by rw [hxt]
    have hyi : (y &&& ~~~b.unknown_mask)[i] = (b.value &&& ~~~b.unknown_mask)[i] := by rw [hyt]
    have ha1 := bitElem_zero_of_and_eq_zero ha.value_disjoint_unknown i hi
    have hb1 := bitElem_zero_of_and_eq_zero hb.value_disjoint_unknown i hi
    simp only [BitVec.getElem_and, BitVec.getElem_not] at hxi hyi
    simp only [BitVec.getElem_and, BitVec.getElem_or, BitVec.getElem_not]
    revert hxi hyi ha1 hb1
    cases x[i] <;> cases y[i] <;>
    cases a.value[i] <;> cases b.value[i] <;>
    cases a.unknown_mask[i] <;> cases b.unknown_mask[i] <;> decide
  · unfold bitand_raw U64Range.contains minWord at *
    simp only [BitVec.toNat_ofNat, Nat.zero_mod, Nat.zero_le, true_and]
    have hand_x : (x &&& y).toNat ≤ x.toNat := by
      rw [BitVec.toNat_and]; exact Nat.and_le_left
    have hand_y : (x &&& y).toNat ≤ y.toNat := by
      rw [BitVec.toNat_and]; exact Nat.and_le_right
    split <;> omega

/-- Soundness of `bitor_scalar` (`bitor_raw`): if `x ∈ γ(a)` and `y ∈ γ(b)`,
then `(x ||| y) ∈ γ(bitor_raw a b)` (both tnum known bits and `urange` bounds). -/
theorem bitor_raw_sound (a b : U64ScalarValueData) (x y : Word)
    (ha : a.MaskWF) (hb : b.MaskWF)
    (hx : a.concretizes x) (hy : b.concretizes y) :
    (bitor_raw a b).concretizes (x ||| y) := by
  rcases hx with ⟨hxt, hxr⟩
  rcases hy with ⟨hyt, hyr⟩
  constructor
  · unfold inTnum bitor_raw at *
    ext i hi
    have hxi : (x &&& ~~~a.unknown_mask)[i] = (a.value &&& ~~~a.unknown_mask)[i] := by rw [hxt]
    have hyi : (y &&& ~~~b.unknown_mask)[i] = (b.value &&& ~~~b.unknown_mask)[i] := by rw [hyt]
    have ha1 := bitElem_zero_of_and_eq_zero ha.value_disjoint_unknown i hi
    have hb1 := bitElem_zero_of_and_eq_zero hb.value_disjoint_unknown i hi
    simp only [BitVec.getElem_and, BitVec.getElem_not] at hxi hyi
    simp only [BitVec.getElem_and, BitVec.getElem_or, BitVec.getElem_not]
    revert hxi hyi ha1 hb1
    cases x[i] <;> cases y[i] <;>
    cases a.value[i] <;> cases b.value[i] <;>
    cases a.unknown_mask[i] <;> cases b.unknown_mask[i] <;> decide
  · dsimp only [bitor_raw, U64Range.contains, maxWord] at *
    have hor_x : x.toNat ≤ (x ||| y).toNat := by
      rw [BitVec.toNat_or]; exact Nat.left_le_or
    have hor_y : y.toNat ≤ (x ||| y).toNat := by
      rw [BitVec.toNat_or]; exact Nat.right_le_or
    have hlt : (x ||| y).toNat < 2 ^ 64 := (x ||| y).isLt
    have hmax : maxU64.toNat = 2 ^ 64 - 1 := rfl
    split <;> omega

/-- Soundness of `bitxor_scalar` (`bitxor_raw`): if `x ∈ γ(a)` and `y ∈ γ(b)`,
then `(x ^^^ y) ∈ γ(bitxor_raw a b)` (both tnum known bits and `urange` bounds). -/
theorem bitxor_raw_sound (a b : U64ScalarValueData) (x y : Word)
    (hx : a.concretizes x) (hy : b.concretizes y) :
    (bitxor_raw a b).concretizes (x ^^^ y) := by
  rcases hx with ⟨hxt, _⟩
  rcases hy with ⟨hyt, _⟩
  constructor
  · unfold inTnum bitxor_raw at *
    ext i hi
    have hxi : (x &&& ~~~a.unknown_mask)[i] = (a.value &&& ~~~a.unknown_mask)[i] := by rw [hxt]
    have hyi : (y &&& ~~~b.unknown_mask)[i] = (b.value &&& ~~~b.unknown_mask)[i] := by rw [hyt]
    simp only [BitVec.getElem_and, BitVec.getElem_not] at hxi hyi
    simp only [BitVec.getElem_and, BitVec.getElem_or, BitVec.getElem_xor, BitVec.getElem_not]
    revert hxi hyi
    cases x[i] <;> cases y[i] <;>
    cases a.value[i] <;> cases b.value[i] <;>
    cases a.unknown_mask[i] <;> cases b.unknown_mask[i] <;> decide
  · exact U64Range.maxRange_contains (x ^^^ y)

/-!
## Part 3: Formal Host-vs-Guest Initialization & Lattice Polarity Contrast

### 3A. Guest eBPF (`U64ScalarValueData`):
- `bitand_scalar (from_known 0) UNINITIALIZED` clears `unwritten_mask` to `0`
  (`is_fully_initialized = true`, `is_known = true`, `value = 0`), whereas
  `bitxor_scalar UNINITIALIZED UNINITIALIZED` leaves `unwritten_mask = MAX`
  because `bitxor_scalar` operates on two independent abstract scalars without
  relational equality tracking (`r == r`).
- In Starnix's state-pruning order (`PartialOrd for U64ScalarValueData`,
  `scalar_value.rs` lines 394–420), `UNINITIALIZED` is the **Top** (most general)
  element: every well-formed scalar state `s` is a specialization of `UNINITIALIZED`.
-/

/-- In guest eBPF (`U64ScalarValueData`), `0 & UNINITIALIZED` clears
`unwritten_mask` to `0` (`from_known 0`), making the register fully initialized. -/
theorem guest_bitand_zero_uninitialized_initializes :
    bitand_raw (from_known 0#64) UNINITIALIZED = from_known 0#64 ∧
    (bitand_raw (from_known 0#64) UNINITIALIZED).is_fully_initialized = true ∧
    (bitand_raw (from_known 0#64) UNINITIALIZED).is_known = true := by
  decide

/-- Commutative counterpart: `UNINITIALIZED & 0` also clears `unwritten_mask` to `0`. -/
theorem guest_bitand_uninitialized_zero_initializes :
    bitand_raw UNINITIALIZED (from_known 0#64) = from_known 0#64 ∧
    (bitand_raw UNINITIALIZED (from_known 0#64)).is_fully_initialized = true := by
  decide

/-- Dual mask absorption for `bitor`: `MAX | UNINITIALIZED` clears `unwritten_mask` to `0`. -/
theorem guest_bitor_allOnes_uninitialized_initializes :
    bitor_raw (from_known maxU64) UNINITIALIZED = from_known maxU64 ∧
    (bitor_raw (from_known maxU64) UNINITIALIZED).is_fully_initialized = true := by
  decide

/-- By contrast, non-relational `bitxor_raw UNINITIALIZED UNINITIALIZED` does NOT
clear `unwritten_mask` (Starnix handles same-register `BPF_XOR dst, dst` via a
separate relational special case in `verifier.rs`). -/
theorem guest_bitxor_uninitialized_remains_uninitialized :
    (bitxor_raw UNINITIALIZED UNINITIALIZED).is_uninitialized = true ∧
    (bitxor_raw UNINITIALIZED UNINITIALIZED).is_fully_initialized = false := by
  decide

/-- Starnix's state-pruning specificity preorder (`scalar_value.rs` lines 398–406):
`moreGeneralOrEqual general specific` holds iff `general >= specific` in Starnix's
`PartialOrd` (a proof that an eBPF program is safe from `general` implies safety
from `specific`). -/
def moreGeneralOrEqual (general specific : U64ScalarValueData) : Prop :=
  (general.unwritten_mask &&& specific.unwritten_mask) = specific.unwritten_mask ∧
  (general.unknown_mask &&& specific.unknown_mask) = specific.unknown_mask ∧
  (general.value &&& ~~~general.unknown_mask) = (specific.value &&& ~~~general.unknown_mask) ∧
  general.urange.min.toNat ≤ specific.urange.min.toNat ∧
  specific.urange.max.toNat ≤ general.urange.max.toNat

/-- Theorem: `UNINITIALIZED` is the **Top** (maximum) element of Starnix's
state-pruning preorder over all `U64ScalarValueData` states! -/
theorem guest_uninitialized_is_top (s : U64ScalarValueData) :
    moreGeneralOrEqual UNINITIALIZED s := by
  dsimp only [moreGeneralOrEqual, UNINITIALIZED, U64Range.maxRange, maxU64]
  have h1 : 0xffffffffffffffff#64 &&& s.unwritten_mask = s.unwritten_mask :=
    BitVec.allOnes_and
  have h2 : 0xffffffffffffffff#64 &&& s.unknown_mask = s.unknown_mask :=
    BitVec.allOnes_and
  have hnot : ~~~0xffffffffffffffff#64 = 0#64 := rfl
  have h0 : (0#64).toNat = 0 := rfl
  have hmax : (0xffffffffffffffff#64).toNat = 2 ^ 64 - 1 := rfl
  have hlt : s.urange.max.toNat < 2 ^ 64 := s.urange.max.isLt
  refine ⟨h1, h2, ?_, by omega, by omega⟩
  rw [hnot, BitVec.and_zero, BitVec.and_zero]

/-!
### 3B. Host Rust (`Trusted.Mvp.Semantics`):
- In host Rust (`Trusted.Mvp.Semantics`), reading an uninitialized local in
  `0 & uninit` faults immediately with `.fault .uninitialized` because
  `evalRvalue` evaluates both operands strictly via `readLocal` before
  invoking `evalBinary`.
- In the host definedness order (`Slot.le`), `Slot.uninit` is at the **Bottom**
  (no read succeeds on `Slot.uninit`), whereas `Slot.value w` is maximal—the
  exact order-theoretic dual of guest eBPF's state-pruning lattice!
-/

def hostBitAndZeroBody : Body :=
  {
    argCount := 0
    isUnsafe := false
    localTys := [.int 64 false, .int 64 false]
    blocks := [
      {
        statements := [
          .assign 0 (.binary .bitAnd (.constant (.int 64 false) 0) (.copy 1))
        ]
        terminator := .ret
      }
    ]
  }

/-- In host Rust (`Trusted.Mvp.Semantics`), `0 & uninit` faults immediately with
`StepResult.fault .uninitialized`. -/
theorem host_bitand_zero_uninit_faults :
    step hostBitAndZeroBody (initial hostBitAndZeroBody []) = .fault .uninitialized :=
  rfl

/-- Host definedness preorder on `Trusted.Mvp.Slot`: `s1 ≤ s2` iff every
`readLocal` that succeeds on `s1` also succeeds with the same value on `s2`. -/
def hostSlotDefinedLe (s1 s2 : Slot) : Prop :=
  ∀ (w : Word), s1 = .value w → s2 = .value w

/-- In host Rust (`Trusted.Mvp.Semantics`), `Slot.uninit` is a **Bottom** element
of the definedness preorder (`hostSlotDefinedLe .uninit s` for all `s`). -/
theorem host_uninit_is_bottom (s : Slot) :
    hostSlotDefinedLe .uninit s := by
  intro w h
  cases h

/-- Conversely, no `Slot.value w` is below `Slot.uninit` in the host definedness
order (`¬ hostSlotDefinedLe (.value w) .uninit`). -/
theorem host_value_not_le_uninit (w : Word) :
    ¬ hostSlotDefinedLe (.value w) .uninit := by
  intro h
  have heq := h w rfl
  cases heq

end U64ScalarValueData

end StarnixAbstractDomainSoundness
