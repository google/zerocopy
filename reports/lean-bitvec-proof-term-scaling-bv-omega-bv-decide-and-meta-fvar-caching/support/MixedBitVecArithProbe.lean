-- Copyright 2026 The Fuchsia Authors
--
-- Licensed under a BSD-style license <LICENSE-BSD>, Apache License, Version 2.0
-- <LICENSE-APACHE or https://www.apache.org/licenses/LICENSE-2.0>, or the MIT
-- license <LICENSE-MIT or https://opensource.org/licenses/MIT>, at your option.
-- This file may not be copied, modified, or distributed except according to
-- those terms.

import Std.Tactic.BVDecide

namespace MixedBitVecArithProbe

/-!
## Family 1: Bitwise Known-Bits Abstract Domain (`U64ScalarValueData::bitand_scalar`)
No shifts: pure bitwise Boolean algebra over 64-bit words.
-/

-- Strategy 1A: `BitVec.eq_of_getLsbD_eq` + `Bool.casesOn` on the 4 bit atoms at index `i`.
-- Works for any width `w` (even symbolic `w`), 0 native axioms, tiny DAG.
theorem bitand_wf_cases (v1 m1 v2 m2 : BitVec 64)
    (h1 : v1 &&& m1 = 0#64) (h2 : v2 &&& m2 = 0#64) :
    (v1 &&& v2) &&& ~~~((~~~m1 &&& ~~~m2) ||| (~~~v1 &&& ~~~m1) ||| (~~~v2 &&& ~~~m2)) = 0#64 := by
  apply BitVec.eq_of_getLsbD_eq
  intro i hi
  have hb1 : (v1 &&& m1).getLsbD i = false := by rw [h1, BitVec.getLsbD_zero]
  have hb2 : (v2 &&& m2).getLsbD i = false := by rw [h2, BitVec.getLsbD_zero]
  rw [BitVec.getLsbD_and] at hb1 hb2
  simp only [BitVec.getLsbD_and, BitVec.getLsbD_not, BitVec.getLsbD_or,
    BitVec.getLsbD_zero, hi, decide_true, Bool.true_and]
  revert hb1 hb2
  cases v1.getLsbD i <;> cases m1.getLsbD i <;> cases v2.getLsbD i <;> cases m2.getLsbD i <;> decide

-- Strategy 1B: `bv_decide` on the same 4-variable 64-bit known-bits obligation.
theorem bitand_wf_bv_decide (v1 m1 v2 m2 : BitVec 64)
    (h1 : v1 &&& m1 = 0#64) (h2 : v2 &&& m2 = 0#64) :
    (v1 &&& v2) &&& ~~~((~~~m1 &&& ~~~m2) ||| (~~~v1 &&& ~~~m1) ||| (~~~v2 &&& ~~~m2)) = 0#64 := by
  bv_decide

/-!
## Family 2: `EbpfInstruction` 64-Bit Packed Bitfield Lens & `< 16` Register Bound
Combines shifts (`<<<`, `>>>`), masks (`&&&`), bitwise OR (`|||`), and `< 16` `Nat` bounds.
-/

def getDstReg (raw : BitVec 64) : BitVec 64 := (raw >>> 8) &&& 0x0f#64

def setDstReg (raw val : BitVec 64) : BitVec 64 :=
  (raw &&& 0xffff_ffff_ffff_f0ff#64) ||| ((val &&& 0x0f#64) <<< 8)

-- Strategy 2A: Algebraic `Nat.and_lt_two_pow` bridge for `(getDstReg raw).toNat < 16`.
theorem dstReg_lt_16_algebraic (raw : BitVec 64) : (getDstReg raw).toNat < 16 := by
  unfold getDstReg
  rw [BitVec.toNat_and]
  exact Nat.lt_of_le_of_lt Nat.and_le_right (by decide)

-- Strategy 2B: `bv_decide` on BitVec inequality + `BitVec.lt_def` bridge to `Nat`.
theorem dstReg_lt_16_bv_decide (raw : BitVec 64) : (getDstReg raw).toNat < 16 := by
  have h : getDstReg raw < 16#64 := by unfold getDstReg; bv_decide
  exact BitVec.lt_def.mp h

noncomputable def checkNatPred (n : Nat) (p : Nat → Bool) : Bool :=
  Nat.rec true (fun k ih => p k && ih) n

theorem checkNatPred_sound (n : Nat) (p : Nat → Bool) (h : checkNatPred n p = true) :
    ∀ i, i < n → p i = true := by
  induction n with
  | zero => intro i hi; exact False.elim (Nat.not_lt_zero i hi)
  | succ k ih =>
    have h12 := Bool.and_eq_true_iff.mp h
    intro i hi
    rcases Nat.lt_succ_iff_lt_or_eq.mp hi with hlt | rfl
    · exact ih h12.2 i hlt
    · exact h12.1

noncomputable def checkAllBool2 (f : Bool → Bool → Bool) : Bool :=
  f false false && f false true && f true false && f true true

theorem checkAllBool2_sound (f : Bool → Bool → Bool) (h : checkAllBool2 f = true) (b1 b2 : Bool) :
    f b1 b2 = true := by
  change (f false false && f false true && f true false && f true true) = true at h
  rcases Bool.and_eq_true_iff.mp h with ⟨h123, h4⟩
  rcases Bool.and_eq_true_iff.mp h123 with ⟨h12, h3⟩
  rcases Bool.and_eq_true_iff.mp h12 with ⟨h1, h2⟩
  cases b1 <;> cases b2 <;> assumption

-- Strategy 2C: `setDstReg` / `getDstReg` round-trip via parameter-free closed `Bool` reflection (0 SAT axioms!).
theorem getDstReg_setDstReg_reflect (raw val : BitVec 64) :
    getDstReg (setDstReg raw val) = val &&& 0x0f#64 := by
  apply BitVec.eq_of_getLsbD_eq
  intro i hi
  unfold getDstReg setDstReg
  rw [BitVec.getLsbD_and, BitVec.getLsbD_ushiftRight, BitVec.getLsbD_or,
    BitVec.getLsbD_and, BitVec.getLsbD_shiftLeft, BitVec.getLsbD_and, BitVec.getLsbD_and]
  have hp := checkNatPred_sound 64
    (fun j =>
      ((8 + j) - 8 == j) &&
      checkAllBool2 (fun b1 b2 =>
        (((b1 && (0xffff_ffff_ffff_f0ff#64).getLsbD (8 + j)) ||
          (decide (8 + j < 64) && !decide (8 + j < 8) && (b2 && (0x0f#64).getLsbD j))) &&
          (0x0f#64).getLsbD j) == (b2 && (0x0f#64).getLsbD j)))
    rfl i hi
  rcases Bool.and_eq_true_iff.mp hp with ⟨hsub, hbool⟩
  rw [beq_iff_eq.mp hsub]
  exact beq_iff_eq.mp (checkAllBool2_sound _ hbool (raw.getLsbD (8 + i)) (val.getLsbD i))

-- Strategy 2D: `setDstReg` / `getDstReg` round-trip via `bv_decide`.
theorem getDstReg_setDstReg_bv_decide (raw val : BitVec 64) :
    getDstReg (setDstReg raw val) = val &&& 0x0f#64 := by
  unfold getDstReg setDstReg
  bv_decide

/-!
## Family 3: `U64Range::add_range` Wrapping Addition vs. No-Overflow Bounds
Combines `BitVec 64` wrapping addition (`+`) and `≤` (`BitVec.ule`) with `Nat` linear arithmetic.
-/

-- Strategy 3A: `bv_omega` directly on `BitVec 64` inequalities (triggers `toNat_add` modulo `% 2^64` case splits in `omega`).
theorem u64_add_range_bv_omega (lo1 x1 hi1 lo2 x2 hi2 : BitVec 64)
    (hx1 : lo1 ≤ x1 ∧ x1 ≤ hi1)
    (hx2 : lo2 ≤ x2 ∧ x2 ≤ hi2)
    (hno_ovf : hi1.toNat + hi2.toNat < 18446744073709551616) :
    lo1 + lo2 ≤ x1 + x2 ∧ x1 + x2 ≤ hi1 + hi2 := by
  bv_omega

-- Strategy 3B: Pre-eliminating `% 2^64` via `Nat.mod_eq_of_lt` before calling `omega` (avoids modulo case splits).
theorem u64_add_range_mod_elim (lo1 x1 hi1 lo2 x2 hi2 : BitVec 64)
    (hx1 : lo1 ≤ x1 ∧ x1 ≤ hi1)
    (hx2 : lo2 ≤ x2 ∧ x2 ≤ hi2)
    (hno_ovf : hi1.toNat + hi2.toNat < 18446744073709551616) :
    lo1 + lo2 ≤ x1 + x2 ∧ x1 + x2 ≤ hi1 + hi2 := by
  rw [BitVec.le_def, BitVec.le_def] at hx1 hx2 ⊢
  rw [BitVec.toNat_add, BitVec.toNat_add, BitVec.toNat_add]
  have h1 : lo1.toNat + lo2.toNat < 18446744073709551616 :=
    Nat.lt_of_le_of_lt (Nat.add_le_add (Nat.le_trans hx1.1 hx1.2) (Nat.le_trans hx2.1 hx2.2)) hno_ovf
  have h2 : x1.toNat + x2.toNat < 18446744073709551616 :=
    Nat.lt_of_le_of_lt (Nat.add_le_add hx1.2 hx2.2) hno_ovf
  rw [Nat.mod_eq_of_lt h1, Nat.mod_eq_of_lt h2, Nat.mod_eq_of_lt hno_ovf]
  exact ⟨Nat.add_le_add hx1.1 hx2.1, Nat.add_le_add hx1.2 hx2.2⟩

/-!
## Family 4: Euclidean Div/Mod Index Arithmetic (`reverseByteIndex_involutive`)
-/

def reverseByteIndex (bits i : Nat) : Nat :=
  8 * (bits / 8 - 1 - i / 8) + i % 8

-- Strategy 4A: Raw `omega` on `reverseByteIndex 64 (reverseByteIndex 64 i) = i`.
theorem revIdx64_omega (i : Nat) (hi : i < 64) :
    reverseByteIndex 64 (reverseByteIndex 64 i) = i ∧ reverseByteIndex 64 i < 64 := by
  unfold reverseByteIndex
  omega

-- Strategy 4B: Closed `Bool` reflection (`checkNatPred 64` + `rfl`).
theorem revIdx64_reflect (i : Nat) (hi : i < 64) :
    reverseByteIndex 64 (reverseByteIndex 64 i) = i ∧ reverseByteIndex 64 i < 64 := by
  have hp := checkNatPred_sound 64
    (fun j => (reverseByteIndex 64 (reverseByteIndex 64 j) == j) &&
      decide (reverseByteIndex 64 j < 64))
    rfl i hi
  have h12 := Bool.and_eq_true_iff.mp hp
  exact ⟨beq_iff_eq.mp h12.1, of_decide_eq_true h12.2⟩

end MixedBitVecArithProbe
