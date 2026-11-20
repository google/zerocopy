import Toy.MachInt.Defs
import Toy.MachInt.Examples
import Toy.MachInt.Statements
import Toy.MachInt.Counterexamples
import Toy.MachInt.Witnesses

/-!
# Supplementary results (`Toy.MachInt`)

Fully proved companions to the main results:
1. `castFromUnsigned_widened_toNat_eq_mod_of_source_le`: the composed unsigned cast identity
   `(x as u<m>) as u<k> = x mod 2^m` also holds when the *source* width fits in the final width
   (`n ≤ k`), so `WidthLe m k` is sufficient but not necessary; for all `x` the exact condition
   is `m ≤ k ∨ n ≤ k` (`castFromUnsigned_widened_toNat_eq_mod_forall_iff`).
   `widened_identity_holds_without_widthLe` is a concrete instance.
2. `mod_eq_and_mask_forall_iff_isPowerOfTwo`: the model's shift-count reduction `k % n` agrees
   with the bitmask `k &&& (n - 1)` used by Rust's `wrapping_shl`/`wrapping_shr` for every `k`
   if and only if `n` is a power of two.
3. Canonical-form tightness counterexamples ("all other hypotheses hold and the conclusion
   fails") for the `PosWidth` hypotheses of `tdiv_not_inSignedRange_iff_intMin_negOne` and
   `checkedSRem_intMin_negOne_eq_none`.
4. Additional non-vacuity witnesses for `tdiv_not_inSignedRange_iff_intMin_negOne` exercising the
   both-sides-false direction and the width-one edge case.
-/

namespace Toy.MachInt

/-! ## Composed unsigned casts: a second sufficient width condition -/

/-- The composed cast identity holds whenever the source width fits in the final width
    (`n ≤ k`), with no relation required between `m` and `k`. -/
theorem castFromUnsigned_widened_toNat_eq_mod_of_source_le {n m k : Nat} (x : BitVec n)
    (hnk : n ≤ k) :
    (castFromUnsigned k (castFromUnsigned m x)).toNat = x.toNat % 2 ^ m := by
  unfold castFromUnsigned
  rw [BitVec.toNat_setWidth, BitVec.toNat_setWidth]
  have hx : x.toNat < 2 ^ n := x.isLt
  have hpow : 2 ^ n ≤ 2 ^ k := Nat.pow_le_pow_right (by decide) hnk
  have hlt : x.toNat % 2 ^ m < 2 ^ k :=
    Nat.lt_of_le_of_lt (Nat.mod_le _ _) (Nat.lt_of_lt_of_le hx hpow)
  exact Nat.mod_eq_of_lt hlt

/-- Concrete instance: `u8 -> u32 -> u16` violates `WidthLe 32 16` yet satisfies the composed
    cast identity for every `x`. -/
theorem widened_identity_holds_without_widthLe :
    ¬ WidthLe 32 16 ∧
    ∀ x : BitVec 8, (castFromUnsigned 16 (castFromUnsigned 32 x)).toNat = x.toNat % 2 ^ 32 :=
  ⟨by decide, fun x => castFromUnsigned_widened_toNat_eq_mod_of_source_le x (by decide)⟩

/-- Exact for-all-`x` width condition for the composed unsigned cast identity: it holds for
    every `x : BitVec n` if and only if `m ≤ k` or `n ≤ k`. (When `k < m` and `k < n`, the
    value `x = 2^k` is a counterexample.) -/
theorem castFromUnsigned_widened_toNat_eq_mod_forall_iff (n m k : Nat) :
    (∀ x : BitVec n, (castFromUnsigned k (castFromUnsigned m x)).toNat = x.toNat % 2 ^ m) ↔
      (m ≤ k ∨ n ≤ k) := by
  constructor
  · intro h
    refine Classical.byContradiction fun hne => ?_
    have hkm : k < m := by omega
    have hkn : k < n := by omega
    have hx := h (BitVec.ofNat n (2 ^ k))
    unfold castFromUnsigned at hx
    rw [BitVec.toNat_setWidth, BitVec.toNat_setWidth, BitVec.toNat_ofNat] at hx
    have h1 : 2 ^ k < 2 ^ n := Nat.pow_lt_pow_right (by decide) hkn
    have h2 : 2 ^ k < 2 ^ m := Nat.pow_lt_pow_right (by decide) hkm
    rw [Nat.mod_eq_of_lt h1, Nat.mod_eq_of_lt h2, Nat.mod_self] at hx
    have := Nat.two_pow_pos k
    omega
  · rintro (h | h) x
    · exact castFromUnsigned_widened_toNat_eq_mod x h
    · exact castFromUnsigned_widened_toNat_eq_mod_of_source_le x h

/-! ## Shift-count masking: exact power-of-two characterization -/

/-- The model's shift-count reduction `k % n` agrees with the bitmask `k &&& (n - 1)` for every
    shift count `k` if and only if `n` is a power of two. (At `n = 0`, `k = 1` separates them;
    at any other non-power-of-two width, `k = n` does.) -/
theorem mod_eq_and_mask_forall_iff_isPowerOfTwo (n : Nat) :
    (∀ k : Nat, k % n = k &&& (n - 1)) ↔ ∃ m : Nat, n = 2 ^ m := by
  constructor
  · intro h
    have h0 : n ≠ 0 := by
      intro hn
      subst hn
      have h1 := h 1
      simp at h1
    have hn := h n
    rw [Nat.mod_self] at hn
    exact Nat.ne_zero_and_sub_one_eq_zero_iff_isPowerOfTwo.1 ⟨h0, hn.symm⟩
  · rintro ⟨m, rfl⟩ k
    exact mod_twoPow_eq_and_mask m k

/-! ## Canonical-form tightness counterexamples for `PosWidth` -/

/-- Canonical tightness counterexample for `tdiv_not_inSignedRange_iff_intMin_negOne`
    (hypothesis `hn : PosWidth n`): at width `0` the hypothesis fails and the stated
    equivalence is false. -/
theorem ce_tdiv_overflow_iff_drop_posWidth_canonical :
    ¬ PosWidth 0 ∧
    ¬ (¬ InSignedRange 0 ((0#0).toInt.tdiv (0#0).toInt) ↔
        ((0#0) = BitVec.intMin 0 ∧ (0#0) = -1#0)) := by
  decide

/-- Canonical tightness counterexample for `checkedSRem_intMin_negOne_eq_none`
    (hypothesis `hn : PosWidth n`): at width `0` the hypothesis fails and the stated
    conjunction is false (its first conjunct `NonZeroDiv (-1#0)` fails). -/
theorem ce_checkedSRem_intMin_drop_posWidth_canonical :
    ¬ PosWidth 0 ∧
    ¬ (NonZeroDiv (-1#0) ∧
        InSignedRange 0 ((BitVec.intMin 0).toInt.tmod (-1#0).toInt) ∧
        checkedSRem (BitVec.intMin 0) (-1#0) = none ∧
        checkedSRemEuclid (BitVec.intMin 0) (-1#0) = none) := by
  decide

/-! ## Canonical-form tightness counterexamples for `ShiftInBounds` and `WidthLe` -/

/-- Canonical tightness counterexample for `wrappingShl_eq_mul_twoPow_of_shiftInBounds`
    (hypothesis `hk : ShiftInBounds n k`): at `n = 8`, `k = 8`, `x = 1#8` the hypothesis fails
    and the stated three-part conclusion is false (`checkedShl (1#8) 8 = none`). -/
theorem ce_wrappingShl_drop_shiftInBounds_canonical :
    ¬ ShiftInBounds 8 8 ∧
    ¬ (checkedShl (1#8) 8 = some (wrappingShl (1#8) 8) ∧
        (wrappingShl (1#8) 8).toNat = (1#8).toNat * 2 ^ 8 % 2 ^ 8 ∧
        (wrappingShl (1#8) 8).toInt = ((1#8).toInt * ((2 ^ 8 : Nat) : Int)).bmod (2 ^ 8)) := by
  decide

/-- Canonical tightness counterexample for `wrappingUShr_and_wrappingSShr_of_shiftInBounds`
    (hypothesis `hk : ShiftInBounds n k`): at `n = 8`, `k = 8`, `x = 128#8` the hypothesis fails
    and the stated four-part conclusion is false (`checkedUShr (128#8) 8 = none`). -/
theorem ce_wrappingShr_drop_shiftInBounds_canonical :
    ¬ ShiftInBounds 8 8 ∧
    ¬ (checkedUShr (128#8) 8 = some (wrappingUShr (128#8) 8) ∧
        (wrappingUShr (128#8) 8).toNat = (128#8).toNat / 2 ^ 8 ∧
        checkedSShr (128#8) 8 = some (wrappingSShr (128#8) 8) ∧
        (wrappingSShr (128#8) 8).toInt = (128#8).toInt.fdiv ((2 ^ 8 : Nat) : Int)) := by
  decide

/-- Canonical tightness counterexample for `cast_roundTrip_widen_then_narrow_of_widthLe`
    (hypothesis `hle : WidthLe n m`): at `n = 16`, `m = 8`, `x = 256#16` the hypothesis fails
    and the stated two-part conclusion is false (the unsigned round trip yields `0#16`). -/
theorem ce_cast_roundTrip_drop_widthLe_canonical :
    ¬ WidthLe 16 8 ∧
    ¬ (castFromUnsigned 16 (castFromUnsigned 8 (256#16)) = 256#16 ∧
        castFromSigned 16 (castFromSigned 8 (256#16)) = 256#16) := by
  decide

/-! ## Additional non-vacuity witnesses -/

/-- `tdiv_not_inSignedRange_iff_intMin_negOne` at `n = 8` with both sides false:
    `5 / -1 = -5` is in range and `(5, -1)` is not `(MIN, -1)`. -/
theorem nv_tdiv_iff_both_false :
    PosWidth 8 ∧ InSignedRange 8 ((5#8).toInt.tdiv (-1#8).toInt) ∧
    ¬ ((5#8) = BitVec.intMin 8 ∧ (-1#8) = -1#8) := by
  decide

/-- `tdiv_not_inSignedRange_iff_intMin_negOne` at `n = 1`, where `-1#1 = intMin 1`:
    `MIN / -1 = 1` is outside the width-one signed range `[-1, 0]`. -/
theorem nv_tdiv_iff_width_one :
    PosWidth 1 ∧ (-1#1) = BitVec.intMin 1 ∧
    ¬ InSignedRange 1 ((BitVec.intMin 1).toInt.tdiv (-1#1).toInt) := by
  decide

end Toy.MachInt
