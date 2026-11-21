/-
Toy.MagicDiv.Witnesses
======================

Non-vacuity theorems: for every result card, a concrete intended instance on
which all of the hypotheses of every Lean statement on the card hold
(including the input-range and sign hypotheses inside the conclusion's
quantifiers). Every proof is by kernel evaluation.
-/
import Toy.MagicDiv.Defs

namespace Toy.MagicDiv

/-- `mulShiftCorrect_of_sandwich` and `directRem_eq_mod_of_sandwich`: 32-bit
division by 7 with `ℓ = 3`, `m = ⌈2^35/7⌉ = 4908534053`
(`m * 7 - 2^35 = 3 ≤ 2^3`), and the input `x = 200 < 2^32`. -/
theorem nv_sandwich_u32_div7 :
    2 ^ (32 + 3) ≤ 4908534053 * 7 ∧ 4908534053 * 7 ≤ 2 ^ (32 + 3) + 2 ^ 3 ∧
      200 < 2 ^ 32 := by decide

/-- `unsignedMagic_sandwich`: the divisor `7` is positive; the multiplier is
`unsignedMagic 32 7 = 2^32 + 613566757`. -/
theorem nv_unsignedMagic_sandwich_div7 :
    (0 : Nat) < 7 ∧ unsignedMagic 32 7 = 2 ^ 32 + 613566757 := by decide

/-- `unsignedMagic_ge_two_pow_of_pos`, `unsignedMagic_lt_two_pow_succ_of_le`,
`unsignedMagic_eq_two_pow_add_low`: `N = 32`, `d = 7` (`0 < 7 ≤ 2^33`). -/
theorem nv_unsignedMagic_bounds : (0 : Nat) < 7 ∧ 7 ≤ 2 ^ (32 + 1) := by decide

/-- `singleWordMagic_lt_two_pow`: `N = 8`, `d = 7` (`1 ≤ 8`, `7 ≤ 2^8`).
`single_word_multiplier_exists_iff` has no hypotheses. -/
theorem nv_single_word_u8_div7 : 1 ≤ 8 ∧ 7 ≤ 2 ^ 8 := by decide

/-- `fixupQuot_eq_wide`, `fixupQuot_correct`: 8-bit division by 7 with
`ℓ = 3`, `m' = 37` (multiplier `2^8 + 37 = 293`), and `x = 200 < 2^8`. -/
theorem nv_fixupQuot_correct_u8_div7 :
    1 ≤ 3 ∧ 37 ≤ 2 ^ 8 ∧ MulShiftCorrect 8 7 (2 ^ 8 + 37) (8 + 3) ∧ 200 < 2 ^ 8 := by
  decide +kernel

/-- `fixupQuot_unsignedMagic_correct`: `d = 7 ≥ 2`, `x = 200 < 2^8`. -/
theorem nv_fixupQuot_unsignedMagic : 2 ≤ 7 ∧ 200 < 2 ^ 8 := by decide

/-- `no_single_word_multiplier_u8_div7`, `minimal_shift_u8_div7`: `m = 147 < 2^8`,
`s = 10 ≤ 10`. -/
theorem nv_no_single_word_u8_div7 : 147 < 2 ^ 8 ∧ 10 ≤ 10 := by decide

/-- `mulShiftCorrect_iff_exactCriterion` (`N = 8`, `d = 7`: `0 < 7 < 2^8`) and
`mulShiftCorrect_iff_of_two_pow_le` (`N = 8`, `d = 300 ≥ 2^8`). -/
theorem nv_exact_u8 : 0 < 7 ∧ 7 < 2 ^ 8 ∧ 2 ^ 8 ≤ 300 := by decide

/-- `exists_mulShiftCorrect_iff_ceilDiv`: `N = 8`, `d = 7`. -/
theorem nv_exact_u8_div7 : 0 < 7 ∧ 7 < 2 ^ 8 := by decide

/-- `mulShiftCorrect_ceilDiv_succ`: the premise holds at `N = 8, d = 7, s = 11`. -/
theorem nv_ceilDiv_succ_u8_div7 : MulShiftCorrect 8 7 (ceilDiv (2 ^ 11) 7) 11 := by
  decide +kernel

/-- `sdivMagic_eq_tdiv_of_sandwich`: 32-bit signed division by 7 with `ℓ = 3`,
`m = signedMagic 32 7 = 2454267027` (`m * 7 - 2^34 = 5 ≤ 2^3`), and the
signed 32-bit input `x = -7`. -/
theorem nv_signed_sandwich_i32_div7 :
    signedMagic 32 7 = 2454267027 ∧
      2 ^ (32 - 1 + 3) < 2454267027 * 7 ∧ 2454267027 * 7 ≤ 2 ^ (32 - 1 + 3) + 2 ^ 3 ∧
      SignedRange 32 (-7) := by
  decide

/-- `sdivMagicUncorrected_eq_tdiv_sub_one_of_neg`: as above, with `x = -7 < 0`. -/
theorem nv_sdivMagicUncorrected :
    2 ^ (32 - 1 + 3) < 2454267027 * 7 ∧ 2454267027 * 7 ≤ 2 ^ (32 - 1 + 3) + 2 ^ 3 ∧
      SignedRange 32 (-7) ∧ (-7 : Int) < 0 := by
  decide

/-- `tdiv_signedRange_iff`: `-128` is a signed 8-bit value. -/
theorem nv_tdiv_signedRange : SignedRange 8 (-128) := by decide

/-- `signedMagic_sandwich`: the divisor `7` is positive; the multiplier is
`signedMagic 32 7 = 2454267027`. -/
theorem nv_signedMagic_sandwich_div7 :
    (0 : Nat) < 7 ∧ signedMagic 32 7 = 2454267027 := by decide

/-- `int_shiftRight_eq_tdiv_iff` has no hypotheses; both truth values of the
equivalence occur (`-1 >>> 1 = -1 ≠ 0 = tdiv (-1) 2`, `-8 >>> 2 = tdiv (-8) 4`). -/
theorem nv_int_shiftRight :
    (-1 : Int) >>> 1 ≠ Int.tdiv (-1) (2 ^ 1) ∧ (-8 : Int) >>> 2 = Int.tdiv (-8) (2 ^ 2) := by
  decide

/-- `biasDiv_eq_tdiv_of_lt`, `biasDivMasked_eq_tdiv_of_pos_of_lt`: `N = 8`,
`k = 2` (`1 ≤ 2 < 8`), `x = -7`. -/
theorem nv_biasDiv : 1 ≤ 2 ∧ 2 < 8 ∧ SignedRange 8 (-7) := by decide

/-- `biasDivBV_u8`, `biasDivBVMasked_u8`: `k = 2` (`1 ≤ 2`, `2 < 8`, `2 ≤ 6`). -/
theorem nv_biasDivBV_u8 : 1 ≤ 2 ∧ 2 < 8 ∧ 2 ≤ 6 := by decide

/-- `mulShift_rem_eq_mod_of_correct`: `(m, s) = (293, 11)` is correct for 8-bit
division by 7, and `x = 200 < 2^8`. -/
theorem nv_mulShift_rem : MulShiftCorrect 8 7 293 11 ∧ 200 < 2 ^ 8 := by decide +kernel

/-- `sremMagic_eq_tmod_and_sign`: the signed bounds for 32-bit division by 7,
and in-range dividends of both signs (`7` and `-7`). -/
theorem nv_sremMagic_both_signs :
    2 ^ (32 - 1 + 3) < 2454267027 * 7 ∧ 2454267027 * 7 ≤ 2 ^ (32 - 1 + 3) + 2 ^ 3 ∧
      (SignedRange 32 7 ∧ (0 : Int) ≤ 7) ∧ (SignedRange 32 (-7) ∧ (-7 : Int) < 0) := by
  decide

/-- Evaluated instances `fixupQuot_unsignedMagic_u8`,
`fixupQuot_unsignedMagic_u16_div7`, `mulShiftCorrect_iff_exactCriterion_u8`:
`d = 7`, `x = 200`, `s = 11`. -/
theorem nv_evaluated_instances :
    (2 ≤ 7 ∧ 7 < 2 ^ 8 ∧ 200 < 2 ^ 8) ∧ 200 < 2 ^ 16 ∧ (0 < 7 ∧ 7 < 2 ^ 8 ∧ 11 ≤ 16) := by
  decide

end Toy.MagicDiv
