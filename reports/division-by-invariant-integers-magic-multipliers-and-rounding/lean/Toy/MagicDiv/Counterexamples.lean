/-
Toy.MagicDiv.Counterexamples
============================

Tightness counterexamples in canonical form: a concrete instance satisfying
all the *other* hypotheses of a result, on which the conclusion fails. Also
the positive controls of the impossibility results, the escape-hatch facts
cited in non-claims, and standalone counterexamples. Most proofs are by kernel
evaluation; a few instantiate proved results of `Toy.MagicDiv.Statements`.
-/
import Toy.MagicDiv.Bounded

namespace Toy.MagicDiv

/-! ### `mulShiftCorrect_of_sandwich` -/

/-- Lower bound dropped (`N = 1, ℓ = 0, d = 1, m = 1`): the upper bound holds
but the multiply-shift is wrong (at `x = 1`). -/
theorem ce_sandwich_hlo :
    1 * 1 ≤ 2 ^ (1 + 0) + 2 ^ 0 ∧ ¬ MulShiftCorrect 1 1 1 (1 + 0) :=
  ⟨by decide, fun h => absurd (h 1 (by decide)) (by decide)⟩

/-- Upper bound dropped (`N = 8, ℓ = 2, d = 7, m = ⌈2^10/7⌉ = 147`): the lower
bound holds (`147 * 7 - 2^10 = 5 > 2^2`) but the multiply-shift is wrong (at
`x = 209`). -/
theorem ce_sandwich_hhi :
    2 ^ (8 + 2) ≤ 147 * 7 ∧ ¬ MulShiftCorrect 8 7 147 (8 + 2) :=
  ⟨by decide, fun h => absurd (h 209 (by decide)) (by decide)⟩

/-- The input range `x < 2^N` is tight (`N = 1, ℓ = 0, d = 3, m = 1`): both
bounds hold, and the equation fails at the first out-of-range input
`x = 2^N = 2`. -/
theorem ce_sandwich_input_range :
    (2 ^ (1 + 0) ≤ 1 * 3 ∧ 1 * 3 ≤ 2 ^ (1 + 0) + 2 ^ 0) ∧
      (2 ^ 1 * 1) >>> (1 + 0) ≠ 2 ^ 1 / 3 := by decide

/-- The sandwich is sufficient, not necessary: for 8-bit division by 35 with
`ℓ = 5`, the multiplier `235` exceeds the upper bound
(`235 * 35 - 2^13 = 33 > 2^5`) and is nevertheless correct. -/
theorem sandwich_not_necessary_u8_div35 :
    2 ^ (8 + 5) + 2 ^ 5 < 235 * 35 ∧ MulShiftCorrect 8 35 235 (8 + 5) := by decide +kernel

/-! ### `unsignedMagic_sandwich`, `unsignedMagic_ge_two_pow_of_pos`,
`unsignedMagic_lt_two_pow_succ_of_le`, `unsignedMagic_eq_two_pow_add_low` -/

/-- `0 < d` dropped: at `d = 0` the lower bound fails. -/
theorem ce_unsignedMagic_sandwich_d_zero :
    ¬ (2 ^ (0 + clog2 0) ≤ unsignedMagic 0 0 * 0 ∧
        unsignedMagic 0 0 * 0 ≤ 2 ^ (0 + clog2 0) + 2 ^ clog2 0) := by decide

/-- `0 < d` dropped: `unsignedMagic 8 0 = 0 < 2^8`. -/
theorem ce_unsignedMagic_ge_two_pow_d_zero : ¬ 2 ^ 8 ≤ unsignedMagic 8 0 := by decide

/-- Positive control for `unsignedMagic_ge_two_pow_of_pos`: lowering the shift
by one (the single-word candidate) can give a multiplier below `2^N` that is
correct (`N = 8, d = 3`: `(171, 9)`). -/
theorem pc_single_word_shift_fits :
    singleWordMagic 8 3 < 2 ^ 8 ∧
      MulShiftCorrect 8 3 (singleWordMagic 8 3) (singleWordShift 8 3) := by
  decide +kernel

/-- `d ≤ 2^(N+1)` dropped (`N = 0, d = 3`): `unsignedMagic 0 3 = 2 = 2^(0+1)`. -/
theorem ce_unsignedMagic_lt_two_pow_succ : ¬ unsignedMagic 0 3 < 2 ^ (0 + 1) := by decide

/-- `0 < d` dropped from `unsignedMagic_eq_two_pow_add_low` (`N = 0, d = 0`):
`d ≤ 2^(N+1)` holds, but `unsignedMagic 0 0 = 0` is not `2^0 + (0 - 2^0) = 1`. -/
theorem ce_unsignedMagic_low_d_zero :
    0 ≤ 2 ^ (0 + 1) ∧
      ¬ (unsignedMagic 0 0 = 2 ^ 0 + (unsignedMagic 0 0 - 2 ^ 0) ∧
          unsignedMagic 0 0 - 2 ^ 0 < 2 ^ 0) := by decide

/-- `d ≤ 2^(N+1)` dropped from `unsignedMagic_eq_two_pow_add_low`
(`N = 0, d = 3`): `0 < d` holds, but the low part `2 - 1 = 1` is not below `2^0`. -/
theorem ce_unsignedMagic_low_hd :
    0 < 3 ∧
      ¬ (unsignedMagic 0 3 = 2 ^ 0 + (unsignedMagic 0 3 - 2 ^ 0) ∧
          unsignedMagic 0 3 - 2 ^ 0 < 2 ^ 0) := by decide

/-! ### `singleWordMagic_lt_two_pow`, `single_word_multiplier_exists_iff` -/

/-- `1 ≤ N` dropped from `singleWordMagic_lt_two_pow` (`N = 0, d = 1`):
`d ≤ 2^N` holds, but the candidate `singleWordMagic 0 1 = 1` is not below `2^0`. -/
theorem ce_single_word_hN : 1 ≤ 2 ^ 0 ∧ ¬ singleWordMagic 0 1 < 2 ^ 0 := by decide

/-- `d ≤ 2^N` dropped from `singleWordMagic_lt_two_pow` (`N = 1, d = 3`):
`1 ≤ N` holds, but the candidate `singleWordMagic 1 3 = 2` is not below `2^1`. -/
theorem ce_single_word_hdN : 1 ≤ 1 ∧ ¬ singleWordMagic 1 3 < 2 ^ 1 := by decide

/-- `singleWordShift N d` is the largest shift whose ceiling multiplier is below
`2^N`, not the smallest correct shift: for `N = 8, d = 9` it is `11`, while
`(57, 9)` is already correct. -/
theorem singleWordShift_not_minimal_u8_div9 :
    singleWordShift 8 9 = 11 ∧ singleWordMagic 8 9 = 228 ∧ MulShiftCorrect 8 9 57 9 := by
  decide +kernel

/-- For `N = 32, d = 641`, shift `32` (no post-shift after a multiply-high)
already works with the multiplier `6700417` (`641 * 6700417 = 2^32 + 1`),
while `singleWordShift 32 641 = 41`. -/
theorem mulShiftCorrect_u32_div641_shift32 :
    singleWordShift 32 641 = 41 ∧ 6700417 < 2 ^ 32 ∧ MulShiftCorrect 32 641 6700417 32 :=
  ⟨by decide, by decide, mulShiftCorrect_of_sandwich 32 0 641 6700417 (by decide) (by decide)⟩

/-! ### `fixupQuot_eq_wide`, `fixupQuot_correct`, `fixupQuot_unsignedMagic_correct` -/

/-- `1 ≤ ℓ` dropped (`N = 1, m' = 0, ℓ = 0, x = 1`). -/
theorem ce_fixupQuot_eq_wide_hl :
    0 ≤ 2 ^ 1 ∧ fixupQuot 1 0 0 1 ≠ (1 * (2 ^ 1 + 0)) >>> (1 + 0) := by decide

/-- `m' ≤ 2^N` dropped (`N = 0, m' = 2, ℓ = 1, x = 1`). -/
theorem ce_fixupQuot_eq_wide_hm :
    1 ≤ 1 ∧ fixupQuot 0 2 1 1 ≠ (1 * (2 ^ 0 + 2)) >>> (0 + 1) := by decide

/-- `1 ≤ ℓ` dropped (`N = 1, d = 1, m' = 0, ℓ = 0`): the wide multiply-shift
is correct, the fixup is not (at `x = 1`). -/
theorem ce_fixupQuot_correct_hl :
    0 ≤ 2 ^ 1 ∧ MulShiftCorrect 1 1 (2 ^ 1 + 0) (1 + 0) ∧
      ¬ (∀ x, x < 2 ^ 1 → fixupQuot 1 0 0 x = x / 1) :=
  ⟨by decide, by decide +kernel, fun h => absurd (h 1 (by decide)) (by decide)⟩

/-- `m' ≤ 2^N` dropped (`N = 1, d = 1, m' = 4, ℓ = 1`): the wide multiply-shift
by `2 + 4 = 6` with shift 2 is correct, the fixup is not (at `x = 1`). -/
theorem ce_fixupQuot_correct_hm :
    1 ≤ 1 ∧ MulShiftCorrect 1 1 (2 ^ 1 + 4) (1 + 1) ∧
      ¬ (∀ x, x < 2 ^ 1 → fixupQuot 1 4 1 x = x / 1) :=
  ⟨by decide, by decide +kernel, fun h => absurd (h 1 (by decide)) (by decide)⟩

/-- Correctness of the wide multiply-shift dropped
(`N = 1, d = 1, m' = 0, ℓ = 1`). -/
theorem ce_fixupQuot_correct_h :
    1 ≤ 1 ∧ 0 ≤ 2 ^ 1 ∧ ¬ (∀ x, x < 2 ^ 1 → fixupQuot 1 0 1 x = x / 1) :=
  ⟨by decide, by decide, fun h => absurd (h 1 (by decide)) (by decide)⟩

/-- The input range `x < 2^N` of `fixupQuot_correct` is tight
(`N = 1, d = 3, m' = 1, ℓ = 2`): the other hypotheses hold, and the equation
fails at `x = 8`. -/
theorem ce_fixupQuot_correct_input_range :
    1 ≤ 2 ∧ 1 ≤ 2 ^ 1 ∧ MulShiftCorrect 1 3 (2 ^ 1 + 1) (1 + 2) ∧
      fixupQuot 1 1 2 8 ≠ 8 / 3 :=
  ⟨by decide, by decide, by decide +kernel, by decide⟩

/-- `2 ≤ d` dropped (`N = 1, d = 1`, so `ℓ = clog2 1 = 0`). -/
theorem ce_fixupQuot_unsignedMagic_d_one :
    ¬ (∀ x, x < 2 ^ 1 → fixupQuot 1 (unsignedMagic 1 1 - 2 ^ 1) (clog2 1) x = x / 1) :=
  fun h => absurd (h 1 (by decide)) (by decide)

/-- The input range `x < 2^N` of `fixupQuot_unsignedMagic_correct` is tight
(`N = 0, d = 3`): `2 ≤ d` holds, and the equation fails at `x = 2`. -/
theorem ce_fixupQuot_unsignedMagic_input_range :
    2 ≤ 3 ∧ fixupQuot 0 (unsignedMagic 0 3 - 2 ^ 0) (clog2 3) 2 ≠ 2 / 3 := by
  decide

/-- For `2^N < d ≤ 2^(N+1)` the fixup's final shift is the full width:
at `N = 8, d = 300`, `clog2 300 - 1 = 8`. -/
theorem fixupQuot_shift_width_u8_d300 : 2 ^ 8 < 300 ∧ 300 ≤ 2 ^ 9 ∧ clog2 300 - 1 = 8 := by
  decide

/-! ### `no_single_word_multiplier_u8_div7` -/

/-- Positive control: allowing a 9-bit multiplier, `(293, 11)` divides 8-bit
inputs by 7. -/
theorem pc_div7_u8_nine_bit_multiplier : 293 < 2 ^ 9 ∧ MulShiftCorrect 8 7 293 11 := by
  decide +kernel

/-- `m < 2^8` dropped from `no_single_word_multiplier_u8_div7` (canonical form):
for the 9-bit multiplier `293` some shift is correct. -/
theorem ce_no_single_word_u8_div7_m_bound : ¬ (∀ s, ¬ MulShiftCorrect 8 7 293 s) :=
  fun h => h 11 pc_div7_u8_nine_bit_multiplier.2

/-- `s ≤ 10` dropped from the first conjunct of `minimal_shift_u8_div7`
(canonical form): at `s = 11` some multiplier (`293`) is correct. -/
theorem ce_minimal_shift_u8_div7_s_bound : ¬ (∀ m, ¬ MulShiftCorrect 8 7 m 11) :=
  fun h => h 293 pc_div7_u8_nine_bit_multiplier.2

/-! ### `mulShiftCorrect_iff_exactCriterion`, `mulShiftCorrect_iff_of_two_pow_le`,
`exists_mulShiftCorrect_iff_ceilDiv`, `mulShiftCorrect_ceilDiv_succ` -/

/-- `0 < d` dropped (`N = 1, d = 0, m = 0, s = 0`): the multiply-shift is
(junk-)correct but the criterion's lower bound fails. -/
theorem ce_exactCriterion_d_zero :
    0 < 2 ^ 1 ∧ ¬ (MulShiftCorrect 1 0 0 0 ↔ ExactCriterion 1 0 0 0) := by decide +kernel

/-- `d < 2^N` dropped (`N = 1, d = 2, m = 0, s = 0`): every 1-bit quotient by
2 is 0, so `m = 0` is correct, but the criterion's lower bound fails. -/
theorem ce_exactCriterion_hdN :
    0 < 2 ∧ ¬ (MulShiftCorrect 1 2 0 0 ↔ ExactCriterion 1 2 0 0) := by decide +kernel

/-- `2^N ≤ d` dropped (`N = 1, d = 1, m = 2, s = 1`). -/
theorem ce_two_pow_le :
    ¬ (MulShiftCorrect 1 1 2 1 ↔ (2 ^ 1 - 1) * 2 < 2 ^ 1) := by decide +kernel

/-- `d < 2^N` dropped (`N = 1, d = 2, s = 0`): `m = 0` is correct, the
ceiling multiplier `1` is not. -/
theorem ce_exists_ceilDiv_hdN :
    0 < 2 ∧ ¬ ((∃ m, MulShiftCorrect 1 2 m 0) ↔ MulShiftCorrect 1 2 (ceilDiv (2 ^ 0) 2) 0) :=
  ⟨by decide, fun h => absurd (h.mp ⟨0, by decide +kernel⟩) (by decide +kernel)⟩

/-- The premise of `mulShiftCorrect_ceilDiv_succ` is not vacuous to drop:
the conclusion fails at `N = 8, d = 7, s = 9`. -/
theorem ce_ceilDiv_succ_premise :
    ¬ MulShiftCorrect 8 7 (ceilDiv (2 ^ (9 + 1)) 7) (9 + 1) :=
  fun h => absurd (h 209 (by decide)) (by decide)

/-! ### `sdivMagic_eq_tdiv_of_sandwich` -/

/-- Strict lower bound dropped (`N = 8, ℓ = 1, d = 2, m = 128`, so
`m * d = 2^8` exactly): wrong at `x = -2`. -/
theorem ce_sdiv_hlo :
    128 * 2 ≤ 2 ^ (8 - 1 + 1) + 2 ^ 1 ∧
      ¬ (∀ x, SignedRange 8 x → sdivMagic 128 (8 - 1 + 1) x = Int.tdiv x ((2 : Nat) : Int)) :=
  ⟨by decide, fun h => absurd (h (-2) (by decide)) (by decide)⟩

/-- Upper bound dropped (`N = 8, ℓ = 2, d = 7, m = 74`, so
`m * d - 2^9 = 6 > 2^2`): wrong at `x = -125`. -/
theorem ce_sdiv_hhi :
    2 ^ (8 - 1 + 2) < 74 * 7 ∧
      ¬ (∀ x, SignedRange 8 x → sdivMagic 74 (8 - 1 + 2) x = Int.tdiv x ((7 : Nat) : Int)) :=
  ⟨by decide, fun h => absurd (h (-125) (by decide)) (by decide)⟩

/-- The signed input range is tight above and below (`N = 1, ℓ = 0, d = 1,
m = 2`): both bounds hold and the equation fails at `x = 2^(N-1) = 1` and at
`x = -2^(N-1) - 1 = -2`. -/
theorem ce_sdiv_range :
    (2 ^ (1 - 1 + 0) < 2 * 1 ∧ 2 * 1 ≤ 2 ^ (1 - 1 + 0) + 2 ^ 0) ∧
      sdivMagic 2 (1 - 1 + 0) 1 ≠ Int.tdiv 1 ((1 : Nat) : Int) ∧
      sdivMagic 2 (1 - 1 + 0) (-2) ≠ Int.tdiv (-2) ((1 : Nat) : Int) := by decide

/-! ### `sdivMagicUncorrected_eq_tdiv_sub_one_of_neg` -/

/-- Strict lower bound dropped (`N = 8, ℓ = 1, d = 2, m = 128`): wrong at
`x = -2`. -/
theorem ce_uncorr_hlo :
    128 * 2 ≤ 2 ^ (8 - 1 + 1) + 2 ^ 1 ∧
      ¬ (∀ x, SignedRange 8 x → x < 0 →
        sdivMagicUncorrected 128 (8 - 1 + 1) x = Int.tdiv x ((2 : Nat) : Int) - 1) :=
  ⟨by decide, fun h => absurd (h (-2) (by decide) (by decide)) (by decide)⟩

/-- Upper bound dropped (`N = 8, ℓ = 2, d = 7, m = 74`): wrong at `x = -125`. -/
theorem ce_uncorr_hhi :
    2 ^ (8 - 1 + 2) < 74 * 7 ∧
      ¬ (∀ x, SignedRange 8 x → x < 0 →
        sdivMagicUncorrected 74 (8 - 1 + 2) x = Int.tdiv x ((7 : Nat) : Int) - 1) :=
  ⟨by decide, fun h => absurd (h (-125) (by decide) (by decide)) (by decide)⟩

/-- `x < 0` dropped (`N = 8, ℓ = 2, d = 3, m = 171`, `x = 0`). -/
theorem ce_uncorr_neg :
    (2 ^ (8 - 1 + 2) < 171 * 3 ∧ 171 * 3 ≤ 2 ^ (8 - 1 + 2) + 2 ^ 2) ∧ SignedRange 8 0 ∧
      sdivMagicUncorrected 171 (8 - 1 + 2) 0 ≠ Int.tdiv 0 ((3 : Nat) : Int) - 1 := by decide

/-- **The uncorrected sequence does not round toward negative infinity.** With
the valid 8-bit signed multiplier for `d = 3` (`m = 171`, shift `9`), the
uncorrected sequence maps `-3` to `-2`, while both truncating and floor
division give `-1`; at `-1` it gives `-1` while truncating division gives
`0` (and floor division gives `-1`). -/
theorem uncorrected_ne_fdiv_at_negative_multiple :
    (2 ^ (8 - 1 + 2) < 171 * 3 ∧ 171 * 3 ≤ 2 ^ (8 - 1 + 2) + 2 ^ 2) ∧
      SignedRange 8 (-3) ∧
      sdivMagicUncorrected 171 (8 - 1 + 2) (-3) = -2 ∧
      Int.fdiv (-3) 3 = -1 ∧ Int.tdiv (-3) 3 = -1 ∧
      sdivMagicUncorrected 171 (8 - 1 + 2) (-1) = Int.fdiv (-1) 3 ∧
      sdivMagicUncorrected 171 (8 - 1 + 2) (-1) ≠ Int.tdiv (-1) 3 := by decide

/-! ### `tdiv_signedRange_iff`, `signedMagic_sandwich` -/

/-- `SignedRange N x` dropped (`N = 8, x = 128, d = 1`). -/
theorem ce_tdiv_signedRange_hx :
    ¬ (SignedRange 8 (Int.tdiv 128 1) ↔ ¬ ((128 : Int) = -(2 : Int) ^ (8 - 1) ∧ (1 : Int) = -1)) := by
  decide

/-- `0 < d` dropped: at `d = 0` the strict lower bound fails. -/
theorem ce_signedMagic_d_zero :
    ¬ (2 ^ (8 - 1 + clog2 0) < signedMagic 8 0 * 0 ∧
        signedMagic 8 0 * 0 ≤ 2 ^ (8 - 1 + clog2 0) + 2 ^ clog2 0) := by decide

/-- Core `BitVec.sdiv` wraps in the overflow case: `(-128) / (-1) = -128` on
`BitVec 8`, whereas `Int.tdiv (-128) (-1) = 128` is out of the signed 8-bit
range. -/
theorem bitvec_sdiv_intMin_negOne_wraps :
    BitVec.sdiv (BitVec.ofInt 8 (-128)) (BitVec.ofInt 8 (-1)) = BitVec.ofInt 8 (-128) ∧
      Int.tdiv (-128) (-1) = 128 ∧ ¬ SignedRange 8 (Int.tdiv (-128) (-1)) := by decide

/-! ### `int_shiftRight_eq_tdiv_iff` -/

/-- The arithmetic shift is not truncating division for negative inputs in
general: `-1 >>> 1 = -1` but `Int.tdiv (-1) 2 = 0`. It does agree on negative
multiples of the power of two (`-8 >>> 2 = -2 = Int.tdiv (-8) 4`). -/
theorem int_shiftRight_tdiv_examples :
    (-1 : Int) >>> 1 = -1 ∧ Int.tdiv (-1) (2 ^ 1) = 0 ∧
      (-8 : Int) >>> 2 = Int.tdiv (-8) (2 ^ 2) := by decide

/-! ### `biasDiv_eq_tdiv_of_lt` -/

/-- `k < N` dropped (`N = 2, k = 2, x = -1`): the biased dividend `2` leaves
the signed 2-bit range (it would wrap on a 2-bit machine). -/
theorem ce_biasDiv_hk :
    SignedRange 2 (-1) ∧
      ¬ (SignedRange 2 (biasSum 2 2 (-1)) ∧ biasDiv 2 2 (-1) = Int.tdiv (-1) (2 ^ 2)) :=
  ⟨by decide, fun h => absurd h.1 (by decide)⟩

/-- `SignedRange N x` dropped (`N = 8, k = 1, x = 128`). -/
theorem ce_biasDiv_hx :
    1 < 8 ∧ ¬ (SignedRange 8 (biasSum 8 1 128) ∧ biasDiv 8 1 128 = Int.tdiv 128 (2 ^ 1)) :=
  ⟨by decide, fun h => absurd h.1 (by decide)⟩

/-- On `BitVec 8` with wrapping addition, the shift `k = 8 = N` fails at
`x = -1` (the bias `255` wraps the sum to `-2`). -/
theorem ce_biasDivBV_width :
    (biasDivBV 8 (BitVec.ofInt 8 (-1))).toInt ≠ Int.tdiv (BitVec.ofInt 8 (-1)).toInt (2 ^ 8) := by
  decide

/-! ### `mulShift_rem_eq_mod_of_correct` -/

/-- Quotient correctness dropped (`N = 1, d = 1, m = 0, s = 0`): wrong at
`x = 1`. -/
theorem ce_rem_correct :
    ¬ (∀ x, x < 2 ^ 1 → x - 1 * ((x * 0) >>> 0) = x % 1) :=
  fun h => absurd (h 1 (by decide)) (by decide)

/-! ### `sremMagic_eq_tmod_and_sign` -/

/-- Strict lower bound dropped (`N = 8, ℓ = 1, d = 2, m = 128`): at `x = -2`
the remainder is `-2`, not `Int.tmod (-2) 2 = 0`. -/
theorem ce_srem_hlo :
    128 * 2 ≤ 2 ^ (8 - 1 + 1) + 2 ^ 1 ∧ SignedRange 8 (-2) ∧
      sremMagic 2 128 (8 - 1 + 1) (-2) ≠ Int.tmod (-2) ((2 : Nat) : Int) := by decide

/-- Upper bound dropped (`N = 8, ℓ = 2, d = 7, m = 74`): wrong at `x = -125`. -/
theorem ce_srem_hhi :
    2 ^ (8 - 1 + 2) < 74 * 7 ∧ SignedRange 8 (-125) ∧
      sremMagic 7 74 (8 - 1 + 2) (-125) ≠ Int.tmod (-125) ((7 : Nat) : Int) := by decide

/-- Using the uncorrected quotient instead gives a positive remainder for a
negative dividend (`x = -1`, `d = 3`: remainder `2`). -/
theorem ce_srem_uncorrected_sign :
    (-1 : Int) - 3 * sdivMagicUncorrected 171 (8 - 1 + 2) (-1) = 2 := by decide

/-! ### `directRem_eq_mod_of_sandwich` -/

/-- **A quotient-correct multiplier can fail the direct remainder.** For
`N = 8, d = 35`, the single-word pair `(235, 13)` is correct for the quotient
on every 8-bit input, yet `directRem 13 35 235 255 = 11 ≠ 10 = 255 % 35`. -/
theorem ce_directRem_quotient_valid_multiplier :
    singleWordMagic 8 35 = 235 ∧ singleWordShift 8 35 = 13 ∧
      MulShiftCorrect 8 35 235 13 ∧ directRem 13 35 235 255 = 11 ∧ 255 % 35 = 10 := by
  decide +kernel

/-- Lower bound dropped (`N = 2, ℓ = 0, d = 2, m = 1`). -/
theorem ce_directRem_hlo :
    1 * 2 ≤ 2 ^ (2 + 0) + 2 ^ 0 ∧ ¬ (∀ x, x < 2 ^ 2 → directRem (2 + 0) 2 1 x = x % 2) :=
  ⟨by decide, fun h => absurd (h 1 (by decide)) (by decide)⟩

/-- Upper bound dropped (`N = 8, ℓ = 2, d = 7, m = 147`): wrong at `x = 205`. -/
theorem ce_directRem_hhi :
    2 ^ (8 + 2) ≤ 147 * 7 ∧ ¬ (∀ x, x < 2 ^ 8 → directRem (8 + 2) 7 147 x = x % 7) :=
  ⟨by decide, fun h => absurd (h 205 (by decide)) (by decide)⟩

/-! ### Scope bounds of the bounded checks and remaining range bounds -/

/-- `fixupQuot_unsignedMagic_u8` with `d = 1` (so `ℓ = clog2 1 = 0`) fails at
`x = 1`. -/
theorem ce_fixupQuot_unsignedMagic_u8_d_one :
    ¬ (∀ x, x < 2 ^ 8 → fixupQuot 8 (unsignedMagic 8 1 - 2 ^ 8) (clog2 1) x = x / 1) :=
  fun h => absurd (h 1 (by decide)) (by decide)

/-- `mulShiftCorrect_iff_exactCriterion_u8` with `d = 0` fails (`m = 0`,
`s = 0`): junk-correct, but the criterion's lower bound fails. -/
theorem ce_exactCriterion_u8_d_zero :
    0 < 2 ^ 8 ∧ 0 ≤ 16 ∧ ¬ (MulShiftCorrect 8 0 0 0 ↔ ExactCriterion 8 0 0 0) := by decide +kernel

/-- `mulShiftCorrect_iff_exactCriterion_u8` with `d = 2^8` fails (`m = 0`,
`s = 0`): every 8-bit quotient by 256 is 0. -/
theorem ce_exactCriterion_u8_d_256 :
    0 < 256 ∧ 0 ≤ 16 ∧ ¬ (MulShiftCorrect 8 256 0 0 ↔ ExactCriterion 8 256 0 0) := by
  decide +kernel

/-- The signed input range of `sdivMagicUncorrected_eq_tdiv_sub_one_of_neg` is
tight below (`N = 1, ℓ = 0, d = 1, m = 2`, `x = -2`). -/
theorem ce_uncorr_range :
    (2 ^ (1 - 1 + 0) < 2 * 1 ∧ 2 * 1 ≤ 2 ^ (1 - 1 + 0) + 2 ^ 0) ∧ (-2 : Int) < 0 ∧
      sdivMagicUncorrected 2 (1 - 1 + 0) (-2) ≠ Int.tdiv (-2) ((1 : Nat) : Int) - 1 := by decide

/-- The `BitVec.sdiv` form of `biasDivBV_u8` fails at `k = 7`, where
`BitVec.ofNat 8 128` is the signed value `-128`: at `x = -128` the sequence
gives `-1` while `BitVec.sdiv` gives `1`. -/
theorem ce_biasDivBV_sdiv_k7 :
    biasDivBV 7 (BitVec.ofInt 8 (-128)) ≠
      (BitVec.ofInt 8 (-128)).sdiv (BitVec.ofNat 8 (2 ^ 7)) := by decide

/-- The input range of `mulShift_rem_eq_mod_of_correct` is tight
(`N = 1, d = 3, m = 1, s = 1`): the multiply-shift is correct on 1-bit inputs,
and the remainder equation fails at `x = 2^N = 2`. -/
theorem ce_rem_input_range :
    MulShiftCorrect 1 3 1 1 ∧ 2 - 3 * ((2 * 1) >>> 1) ≠ 2 % 3 := by decide +kernel

/-- The signed input range of `sremMagic_eq_tmod_and_sign` is tight
(`N = 1, ℓ = 0, d = 1, m = 2`, `x = 1`). -/
theorem ce_srem_range :
    (2 ^ (1 - 1 + 0) < 2 * 1 ∧ 2 * 1 ≤ 2 ^ (1 - 1 + 0) + 2 ^ 0) ∧
      sremMagic 1 2 (1 - 1 + 0) 1 ≠ Int.tmod 1 ((1 : Nat) : Int) := by decide

/-- The input range of `directRem_eq_mod_of_sandwich` is tight
(`N = 1, ℓ = 0, d = 3, m = 1`, `x = 2^N = 2`). -/
theorem ce_directRem_input_range :
    (2 ^ (1 + 0) ≤ 1 * 3 ∧ 1 * 3 ≤ 2 ^ (1 + 0) + 2 ^ 0) ∧
      directRem (1 + 0) 3 1 2 ≠ 2 % 3 := by decide


/-! ### Evaluated instances (`fixupQuot_unsignedMagic_u8`,
`fixupQuot_unsignedMagic_u16_div7`) -/

/-- `x < 2^8` is tight in `fixupQuot_unsignedMagic_u8`: at `d = 15` the other
hypotheses `2 ≤ 15`, `15 < 2^8` hold, and at `x = 299` the fixup gives
`20 ≠ 19 = 299 / 15`. -/
theorem ce_fixupQuot_unsignedMagic_u8_x_range :
    2 ≤ 15 ∧ 15 < 2 ^ 8 ∧
      fixupQuot 8 (unsignedMagic 8 15 - 2 ^ 8) (clog2 15) 299 ≠ 299 / 15 := by
  decide

/-- `x < 2^16` is tight in `fixupQuot_unsignedMagic_u16_div7`: at
`x = 104859` the fixup gives `14980 ≠ 14979 = 104859 / 7`. -/
theorem ce_fixupQuot_unsignedMagic_u16_div7_x_range :
    fixupQuot 16 (unsignedMagic 16 7 - 2 ^ 16) (clog2 7) 104859 ≠ 104859 / 7 := by
  decide

/-- `2 ≤ d` is tight in `fixupQuot_unsignedMagic_u8` (canonical form): at
`d = 1` the other hypothesis `1 < 2^8` holds and the equation fails. -/
theorem ce_fixupQuot_unsignedMagic_u8_d_one_canonical :
    1 < 2 ^ 8 ∧
      ¬ (∀ x, x < 2 ^ 8 → fixupQuot 8 (unsignedMagic 8 1 - 2 ^ 8) (clog2 1) x = x / 1) :=
  ⟨by decide, ce_fixupQuot_unsignedMagic_u8_d_one⟩

/-! ### Upward closure does not preserve the single-word size -/

/-- For `N = 8, d = 3`, `⌈2^9/3⌉ = 171 < 2^8` is correct at shift `9`, but the
ceiling multiplier at shift `10` is `342 ≥ 2^8`. -/
theorem ceilDiv_succ_leaves_single_word_u8_div3 :
    ceilDiv (2 ^ 9) 3 = 171 ∧ 171 < 2 ^ 8 ∧ MulShiftCorrect 8 3 171 9 ∧
      ceilDiv (2 ^ 10) 3 = 342 ∧ ¬ 342 < 2 ^ 8 := by
  decide +kernel

/-! ### Signed sandwich: non-necessity and non-minimality -/

/-- **The signed sandwich is sufficient, not necessary.** For `N = 8, d = 35`,
`m = 59` with shift `11 = (8 - 1) + 4` violates the upper bound
(`59 * 35 = 2065 > 2^11 + 2^4 = 2064`) and is nevertheless correct for every
signed 8-bit `x`. -/
theorem signed_sandwich_not_necessary_i8_div35 :
    2 ^ (8 - 1 + 4) < 59 * 35 ∧ ¬ 59 * 35 ≤ 2 ^ (8 - 1 + 4) + 2 ^ 4 ∧
      ∀ x, SignedRange 8 x → sdivMagic 59 (8 - 1 + 4) x = Int.tdiv x ((35 : Nat) : Int) := by
  refine ⟨by decide, by decide, ?_⟩
  have h : allBelow 256 (fun i =>
      sdivMagic 59 (8 - 1 + 4) ((i : Int) - 128) == Int.tdiv ((i : Int) - 128) ((35 : Nat) : Int)) =
        true := by decide +kernel
  rw [allBelow_iff] at h
  intro x hx
  rw [signedRange_iff_of_pos (by decide)] at hx
  have hx' : -128 ≤ x ∧ x < 128 := by simpa using hx
  have e := h (x + 128).toNat (by omega)
  have hc : (((x + 128).toNat : Nat) : Int) - 128 = x := by omega
  rw [hc] at e
  simpa using e

/-- **`signedMagic` is not minimal.** For `N = 8, d = 3`, `signedMagic 8 3 = 171`
(shift `9`, not below `2^7`), whereas `m = 86 < 2^7` satisfies the signed
sandwich at shift `8 = (8 - 1) + 1`. -/
theorem signedMagic_not_minimal_i8_div3 :
    signedMagic 8 3 = 171 ∧ ¬ 171 < 2 ^ (8 - 1) ∧
      2 ^ (8 - 1 + 1) < 86 * 3 ∧ 86 * 3 ≤ 2 ^ (8 - 1 + 1) + 2 ^ 1 ∧ 86 < 2 ^ (8 - 1) := by
  decide

/-! ### Bias-and-shift with shift counts reduced modulo `N` -/

/-- **`1 ≤ k` is tight once shift counts are reduced modulo `N`.** For every
`N ≥ 1`, at `k = 0` and `x = -1` the other hypotheses (`k < N`,
`SignedRange N x`) hold, and the count-masked sequence returns `2^N - 2`
(the whole mask is added) instead of `Int.tdiv (-1) 1 = -1`. -/
theorem ce_biasDivMasked_k_zero (N : Nat) (hN : 1 ≤ N) :
    0 < N ∧ SignedRange N (-1) ∧
      ¬ (SignedRange N (biasSumMasked N 0 (-1)) ∧ biasDivMasked N 0 (-1) = Int.tdiv (-1) (2 ^ 0)) := by
  have h2N : (2 : Int) ≤ 2 ^ N := by
    have h : 2 ≤ 2 ^ N := by simpa using Nat.pow_le_pow_right (by decide : 2 > 0) hN
    rw [← intCast_two_pow]
    exact_mod_cast h
  have hsr : SignedRange N (-1) := by
    unfold SignedRange; omega
  refine ⟨by omega, hsr, ?_⟩
  have h1 : (N - 1) % N = N - 1 := Nat.mod_eq_of_lt (by omega)
  have h2 : (N - 0) % N = 0 := by simp
  have hm := shiftRight_pred_of_signedRange hN hsr
  simp only [show ((-1 : Int) < 0) = True from by simp, ite_true] at hm
  have hl : lsrN N (-1) 0 = (2 : Int) ^ N - 1 := by
    have := lsrN_neg_one (N := N) (k := N) (Nat.le_refl N)
    rwa [Nat.sub_self] at this
  have hsum : biasSumMasked N 0 (-1) = 2 ^ N - 2 := by
    unfold biasSumMasked; rw [h1, h2, hm, hl]; omega
  intro ⟨_, hv⟩
  unfold biasDivMasked at hv
  rw [hsum, Nat.zero_mod, Int.shiftRight_eq_div_pow] at hv
  simp at hv
  omega

/-- `k < N` is tight for the count-masked sequence (`N = 2, k = 2, x = -1`). -/
theorem ce_biasDivMasked_hk :
    1 ≤ 2 ∧ SignedRange 2 (-1) ∧
      ¬ (SignedRange 2 (biasSumMasked 2 2 (-1)) ∧ biasDivMasked 2 2 (-1) = Int.tdiv (-1) (2 ^ 2)) := by
  decide

/-- `SignedRange N x` is tight for the count-masked sequence
(`N = 8, k = 1, x = 128`). -/
theorem ce_biasDivMasked_hx :
    1 ≤ 1 ∧ 1 < 8 ∧
      ¬ (SignedRange 8 (biasSumMasked 8 1 128) ∧ biasDivMasked 8 1 128 = Int.tdiv 128 (2 ^ 1)) := by
  decide

/-- At `k = 0` on `BitVec 8` with shift counts reduced modulo 8, `x = -1` is
mapped to `-2` instead of `Int.tdiv (-1) 1 = -1`. -/
theorem ce_biasDivBVMasked_u8_k_zero :
    0 < 8 ∧ (biasDivBVMasked 0 (BitVec.ofInt 8 (-1))).toInt ≠
      Int.tdiv (BitVec.ofInt 8 (-1)).toInt (2 ^ 0) := by
  decide


/-- `k < 8` is tight for `biasDivBVMasked_u8`: at `k = 8` (counts `7`, `0`, `0`
after reduction modulo 8), `x = -1` is mapped to `-2`, not `tdiv (-1) 256 = 0`. -/
theorem ce_biasDivBVMasked_u8_k_eight :
    1 ≤ 8 ∧ (biasDivBVMasked 8 (BitVec.ofInt 8 (-1))).toInt ≠
      Int.tdiv (BitVec.ofInt 8 (-1)).toInt (2 ^ 8) := by
  decide

/-- At `N = 1, d = 1` the signed multiplier is `2 = 2^N`, and at `d = 1` its
shift `(N - 1) + clog2 1` is `N - 1`. -/
theorem signedMagic_one_one : signedMagic 1 1 = 2 ^ 1 ∧ clog2 1 = 0 := by decide

/-- At `d = 0` the conclusion of `exists_mulShiftCorrect_iff_ceilDiv` holds as
well (both sides reduce to Lean's `x / 0 = 0` convention), so its hypothesis
`0 < d` is `harmless`. -/
theorem exists_mulShiftCorrect_iff_ceilDiv_d_zero (N s : Nat) :
    (∃ m, MulShiftCorrect N 0 m s) ↔ MulShiftCorrect N 0 (ceilDiv (2 ^ s) 0) s := by
  have h0 : ceilDiv (2 ^ s) 0 = 0 := by simp [ceilDiv]
  have hc : MulShiftCorrect N 0 0 s := fun x _ => by simp
  rw [h0]
  exact iff_of_true ⟨0, hc⟩ hc

/-- **What fails at `k = 0` in the count-masked sequence.** At `x = -1`: for
every `N ≥ 1` the quotient equation fails; for every `N ≥ 2` the biased sum also
leaves the signed range; at `N = 1` the biased sum stays in the signed range for
every signed 1-bit `x`. (`ce_biasDivMasked_k_zero` is the conjunction form.) -/
theorem biasDivMasked_k_zero_failures :
    (∀ N : Nat, 1 ≤ N → biasDivMasked N 0 (-1) ≠ Int.tdiv (-1) (2 ^ 0)) ∧
    (∀ N : Nat, 2 ≤ N → ¬ SignedRange N (biasSumMasked N 0 (-1))) ∧
    (∀ x : Int, SignedRange 1 x → SignedRange 1 (biasSumMasked 1 0 x)) := by
  have hsum : ∀ N : Nat, 1 ≤ N → biasSumMasked N 0 (-1) = (2 : Int) ^ N - 2 := by
    intro N hN
    have hsr : SignedRange N (-1) := (ce_biasDivMasked_k_zero N hN).2.1
    have h1 : (N - 1) % N = N - 1 := Nat.mod_eq_of_lt (by omega)
    have h2 : (N - 0) % N = 0 := by simp
    have hm := shiftRight_pred_of_signedRange hN hsr
    simp only [show ((-1 : Int) < 0) = True from by simp, ite_true] at hm
    have hl : lsrN N (-1) 0 = (2 : Int) ^ N - 1 := by
      have := lsrN_neg_one (N := N) (k := N) (Nat.le_refl N)
      rwa [Nat.sub_self] at this
    unfold biasSumMasked; rw [h1, h2, hm, hl]; omega
  have h2N : ∀ N : Nat, 1 ≤ N → (2 : Int) ≤ 2 ^ N := by
    intro N hN
    have h : 2 ≤ 2 ^ N := by simpa using Nat.pow_le_pow_right (by decide : 2 > 0) hN
    rw [← intCast_two_pow]
    exact_mod_cast h
  refine ⟨?_, ?_, ?_⟩
  · intro N hN hv
    have := h2N N hN
    unfold biasDivMasked at hv
    rw [hsum N hN, Nat.zero_mod, Int.shiftRight_eq_div_pow] at hv
    simp at hv
    omega
  · intro N hN2
    rw [hsum N (by omega)]
    unfold SignedRange
    have h4 : (4 : Int) ≤ 2 ^ N := by
      have : 4 ≤ 2 ^ N := by
        have := Nat.pow_le_pow_right (by decide : 0 < 2) hN2
        simpa using this
      rw [← intCast_two_pow]
      exact_mod_cast this
    omega
  · intro x hx
    rw [signedRange_iff_of_pos (by decide : 1 ≤ 1)] at hx
    have hx_cases : x = -1 ∨ x = 0 := by omega
    rcases hx_cases with rfl | rfl <;> decide

end Toy.MagicDiv
