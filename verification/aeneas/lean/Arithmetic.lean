/- Copyright 2026 The Fuchsia Authors

Licensed under a BSD-style license <LICENSE-BSD>, Apache License, Version 2.0
<LICENSE-APACHE or https://www.apache.org/licenses/LICENSE-2.0>, or the MIT
license <LICENSE-MIT or https://opensource.org/licenses/MIT>, at your option.
This file may not be copied, modified, or distributed except according to
those terms. -/

module
public import Aeneas
import all Init.Data.Nat.Power2.Basic
@[expose] public section
open Aeneas Aeneas.Std
namespace Zerocopy.Arithmetic

/-- Scalar minimum agrees with mathematical minimum. -/
theorem coe_min (a b : Usize) :
    ((min a b : Usize) : Nat) = Nat.min (a : Nat) (b : Nat) := by
  by_cases h : a ≤ b
  · rw [min_eq_left h]
    exact (Nat.min_eq_left ((UScalar.le_equiv _ _).mp h)).symm
  · have hba : b ≤ a := le_of_not_ge h
    rw [min_eq_right hba]
    exact (Nat.min_eq_right ((UScalar.le_equiv _ _).mp hba)).symm

/-- The unique bounded padding that makes the sum divisible by alignment. -/
theorem padding_unique (len align p : Nat) (hpos : 0 < align)
    (hlt : p < align) (haligned : (len + p) % align = 0) :
    p = (align - len % align) % align := by
  have hr := Nat.mod_lt len hpos
  have hsum : (len % align + p) % align = 0 := by
    rw [Nat.add_mod, Nat.mod_eq_of_lt hlt] at haligned
    exact haligned
  by_cases hzero : len % align = 0
  · simpa only [hzero, Nat.zero_add, Nat.mod_eq_of_lt hlt,
      Nat.sub_zero, Nat.mod_self] using hsum
  · have hge : align ≤ len % align + p := by
      by_contra h
      rw [Nat.mod_eq_of_lt (by omega)] at hsum
      omega
    rw [Nat.mod_eq_sub_mod hge, Nat.mod_eq_of_lt (by omega)] at hsum
    rw [Nat.mod_eq_of_lt (by omega)]
    omega

/-- Exact padding also gives minimality and the zero-padding criterion. -/
theorem padding_properties (len align p : Nat) (hpos : 0 < align)
    (hlt : p < align) (haligned : (len + p) % align = 0) :
    p = (align - len % align) % align ∧
    (∀ q : Nat, (len + q) % align = 0 → p ≤ q) ∧
    (p = 0 ↔ len % align = 0) := by
  refine ⟨padding_unique len align p hpos hlt haligned, ?_, ?_⟩
  · intro q hq
    have hqm : (len + q % align) % align = 0 := by
      rw [Nat.add_mod] at hq
      rw [Nat.add_mod, Nat.mod_mod]
      exact hq
    have heq := padding_unique len align (q % align) hpos
      (Nat.mod_lt q hpos) hqm
    have hp := padding_unique len align p hpos hlt haligned
    have := Nat.mod_le q align
    omega
  · constructor
    · intro hp
      simpa only [hp, Nat.add_zero] using haligned
    · intro hl
      have hp := padding_unique len align p hpos hlt haligned
      simpa only [hl, Nat.sub_zero, Nat.mod_self] using hp

/-- Clearing and retaining a bit mask partition the original word exactly. -/
theorem mask_partition (n mask : Usize) :
    (n &&& ~~~mask).val + (n &&& mask).val = n.val := by
  have hdisjoint : (n.bv &&& ~~~mask.bv) &&& (n.bv &&& mask.bv) = 0 := by
    ext i
    simp only [BitVec.getElem_and, BitVec.getElem_not]
    cases n.bv[i] <;> cases mask.bv[i] <;> simp
  have hjoin : (n.bv &&& ~~~mask.bv) ||| (n.bv &&& mask.bv) = n.bv := by
    ext i
    simp only [BitVec.getElem_or, BitVec.getElem_and, BitVec.getElem_not]
    cases n.bv[i] <;> cases mask.bv[i] <;> decide
  have hsum := BitVec.add_eq_or_of_and_eq_zero _ _ hdisjoint
  rw [hjoin] at hsum
  have := congrArg BitVec.toNat hsum
  rw [BitVec.toNat_add_of_and_eq_zero hdisjoint] at this
  exact this

/-- A power-of-two alignment divides the word modulus. -/
theorem alignment_dvd_size (align : Usize) (h : align.val.isPowerOfTwo) :
    align.val ∣ UScalar.size .Usize := by
  obtain ⟨k, hk⟩ := h
  have hsize := UScalar.hSize align
  rw [UScalar.size, hk] at hsize ⊢
  exact Nat.pow_dvd_pow 2 ((Nat.pow_le_pow_iff_right (a := 2) (by decide)).mp (by omega))

/-- Complementing the wrapping predecessor produces modular negation. -/
theorem complement_predecessor (len : Usize) :
    (~~~(core.num.Usize.wrapping_sub len 1#usize)).val =
      if len.val = 0 then 0 else UScalar.size .Usize - len.val := by
  change (~~~(len.bv - (1#usize).bv)).toNat = _
  rw [BitVec.toNat_not]
  have hsize := UScalar.hSize len
  have hone : (1#usize).val = 1 := by simp
  by_cases hz : len.val = 0
  · simp only [hz, if_true]
    rw [BitVec.toNat_sub, UScalar.bv_toNat, UScalar.bv_toNat]
    change 2 ^ System.Platform.numBits - 1 -
      ((2 ^ System.Platform.numBits - (1#usize).val) + len.val) % 2 ^ System.Platform.numBits = 0
    rw [hz, hone, Nat.add_zero, Nat.mod_eq_of_lt (by have := Nat.two_pow_pos System.Platform.numBits; omega)]
    omega
  · simp only [hz, if_false]
    rw [BitVec.toNat_sub_of_le (by simpa only [BitVec.le_def, UScalar.bv_toNat, hone] using (show 1 ≤ len.val by omega)), UScalar.bv_toNat, UScalar.bv_toNat, hone]
    change 2 ^ System.Platform.numBits - 1 - (len.val - 1) = UScalar.size .Usize - len.val
    rw [UScalar.size] at hsize ⊢
    change len.val < 2 ^ System.Platform.numBits at hsize
    change 2 ^ System.Platform.numBits - 1 - (len.val - 1) =
      2 ^ System.Platform.numBits - len.val
    omega

/-- The padding bit mask aligns the unbounded sum, including wrapping at zero. -/
theorem padding_mask_aligned (len align mask : Usize)
    (h : align.val.isPowerOfTwo) (hm : mask.val = align.val - 1) :
    (len.val + (~~~(core.num.Usize.wrapping_sub len 1#usize) &&& mask).val)
      % align.val = 0 := by
  have hmod := Nat.mod_eq_zero_of_dvd (alignment_dvd_size align h)
  have hsum : (len.val + (~~~(core.num.Usize.wrapping_sub len 1#usize)).val)
      % align.val = 0 := by
    rw [complement_predecessor]
    split
    · rename_i hz
      simp only [hz, Nat.zero_add, Nat.zero_mod]
    · have hsize := UScalar.hSize len
      rw [Nat.add_sub_of_le (by omega)]
      exact hmod
  obtain ⟨k, hk⟩ := h
  rw [UScalar.val_and, hm, hk, Nat.and_two_pow_sub_one_eq_mod]
  rw [hk, Nat.add_mod] at hsum
  rw [Nat.add_mod, Nat.mod_mod]
  exact hsum

/-- The exact arithmetic result of clearing the low alignment bits. -/
theorem round_down_exact (n align mask : Usize)
    (h : align.val.isPowerOfTwo) (hm : mask.val = align.val - 1) :
    (n &&& ~~~mask).val = n.val - n.val % align.val := by
  have hp := mask_partition n mask
  have hlow : (n &&& mask).val = n.val % align.val := by
    obtain ⟨k, hk⟩ := h
    rw [UScalar.val_and, hm, hk, Nat.and_two_pow_sub_one_eq_mod]
  rw [hlow] at hp
  omega

/-- An exact round-down result is aligned and the greatest such lower bound. -/
theorem round_down_properties (n align m : Nat) (hpos : 0 < align)
    (hm : m = n - n % align) :
    m ≤ n ∧ m % align = 0 ∧ n < m + align ∧
    (∀ q : Nat, q ≤ n → q % align = 0 → q ≤ m) := by
  have hr := Nat.mod_lt n hpos
  have hrle := Nat.mod_le n align
  have hmul : m = (n / align) * align := by
    rw [Nat.div_mul_self_eq_mod_sub_self, hm]
  refine ⟨by omega, ?_, by omega, ?_⟩
  · rw [hmul, Nat.mul_mod_left]
  · intro q hqn hqa
    have hdiv := Nat.div_le_div_right (c := align) hqn
    have hle := Nat.mul_le_mul_right align hdiv
    rw [Nat.div_mul_self_eq_mod_sub_self, Nat.div_mul_self_eq_mod_sub_self,
      hqa, Nat.sub_zero, ← hm] at hle
    exact hle

end Zerocopy.Arithmetic
