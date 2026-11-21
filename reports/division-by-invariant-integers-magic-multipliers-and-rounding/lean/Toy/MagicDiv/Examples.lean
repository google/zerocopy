/-
Toy.MagicDiv.Examples
=====================

Proved positive examples (intended instances a definition must admit) and
negative examples (instances it must reject) for every definition in
`Toy.MagicDiv.Defs`. All proofs are by kernel evaluation (`decide`).
-/
import Toy.MagicDiv.Defs

namespace Toy.MagicDiv

/-! ### `ceilDiv` -/

/-- Positive: `⌈7/2⌉ = 4`, `⌈8/2⌉ = 4`, `⌈2^35/7⌉ = 4908534053`. -/
theorem ceilDiv_pos_examples :
    ceilDiv 7 2 = 4 ∧ ceilDiv 8 2 = 4 ∧ ceilDiv (2 ^ 35) 7 = 4908534053 := by decide

/-- Negative: `ceilDiv` is not floor division (`⌊7/2⌋ = 3`). -/
theorem ceilDiv_neg_example : ceilDiv 7 2 ≠ 7 / 2 := by decide

/-! ### `clog2` -/

/-- Positive: `clog2 1 = 0`, `clog2 7 = 3`, `clog2 8 = 3`, `clog2 9 = 4`, and
`3` is the least `ℓ` with `7 ≤ 2^ℓ`. -/
theorem clog2_pos_examples :
    clog2 1 = 0 ∧ clog2 2 = 1 ∧ clog2 7 = 3 ∧ clog2 8 = 3 ∧ clog2 9 = 4 ∧
      7 ≤ 2 ^ clog2 7 ∧ ¬ 7 ≤ 2 ^ (clog2 7 - 1) := by decide

/-- Negative: `clog2` is neither the floor logarithm (`⌊log₂ 7⌋ = 2`) nor
"floor logarithm plus one" (which would give `4` at `8`). -/
theorem clog2_neg_examples : clog2 7 ≠ Nat.log2 7 ∧ clog2 8 ≠ Nat.log2 8 + 1 := by decide

/-! ### `MulShiftCorrect` -/

/-- Positive: `x / 3 = (x * 171) >>> 9` and `x / 7 = (x * 293) >>> 11` for all
8-bit `x`. -/
theorem mulShiftCorrect_pos_examples :
    MulShiftCorrect 8 3 171 9 ∧ MulShiftCorrect 8 7 293 11 := by decide +kernel

/-- Negative: the truncated reciprocal `⌊2^8/3⌋ = 85` with shift 8 is wrong
(at `x = 3`), and the single-word candidate `147 = ⌈2^10/7⌉` with shift 10 is
wrong (at `x = 209`). -/
theorem mulShiftCorrect_neg_examples :
    ¬ MulShiftCorrect 8 3 85 8 ∧ ¬ MulShiftCorrect 8 7 147 10 := by
  refine ⟨fun h => absurd (h 3 (by decide)) (by decide),
    fun h => absurd (h 209 (by decide)) (by decide)⟩

/-! ### `lastFullBlockEnd` -/

/-- Positive: for `N = 8`, `d = 7` the critical input is `251`: it is `< 256`,
it is `≡ 6 (mod 7)`, and no larger 8-bit input is `≡ 6 (mod 7)`. -/
theorem lastFullBlockEnd_pos_example :
    lastFullBlockEnd 8 7 = 251 ∧ 251 % 7 = 6 ∧
      ∀ y, y < 2 ^ 8 → y % 7 = 6 → y ≤ lastFullBlockEnd 8 7 := by decide +kernel

/-- Negative: the critical input is not simply the largest input `2^N - 1`. -/
theorem lastFullBlockEnd_neg_example : lastFullBlockEnd 8 7 ≠ 2 ^ 8 - 1 := by decide

/-! ### `ExactCriterion` -/

/-- Positive: `(m, s) = (171, 9)` for `d = 3` and `(293, 11)` for `d = 7`
(8-bit inputs) satisfy the criterion. -/
theorem exactCriterion_pos_examples :
    ExactCriterion 8 3 171 9 ∧ ExactCriterion 8 7 293 11 := by decide

/-- Negative: `(147, 10)` for `d = 7` violates the upper bound
(`251 * 5 ≥ 1024`), and `(85, 8)` for `d = 3` violates the lower bound. -/
theorem exactCriterion_neg_examples :
    ¬ ExactCriterion 8 7 147 10 ∧ ¬ ExactCriterion 8 3 85 8 := by decide

/-! ### `unsignedMagic`, `singleWordShift`, `singleWordMagic` -/

/-- Positive: for 32-bit division by 7 the textbook multiplier is
`⌈2^35/7⌉ = 2^32 + 613566757`; for 8-bit division by 3 the single-word
candidate is `(m, s) = (171, 9)`. -/
theorem magic_pos_examples :
    unsignedMagic 32 7 = 2 ^ 32 + 613566757 ∧ unsignedMagic 8 7 = 293 ∧
      singleWordShift 8 3 = 9 ∧ singleWordMagic 8 3 = 171 := by decide

/-- Negative: the textbook multiplier for a non-power-of-two divisor does not
fit in `N` bits, and the single-word candidate is not the textbook one. -/
theorem magic_neg_examples :
    ¬ unsignedMagic 32 7 < 2 ^ 32 ∧ singleWordMagic 8 7 ≠ unsignedMagic 8 7 := by decide

/-- Negative: `singleWordShift` uses the ceiling logarithm, not the floor
logarithm (`singleWordShift 8 8 = 10`, whereas `8 + ⌊log₂ 8⌋ = 11`). -/
theorem singleWordShift_neg_example : singleWordShift 8 8 ≠ 8 + Nat.log2 8 := by decide

/-! ### `fixupQuot` -/

/-- Positive: with `m' = 37` (multiplier `2^8 + 37 = 293`) and `ℓ = 3`, the
fixup sequence computes `200 / 7 = 28` and `255 / 7 = 36`. -/
theorem fixupQuot_pos_examples :
    fixupQuot 8 37 3 200 = 200 / 7 ∧ fixupQuot 8 37 3 255 = 255 / 7 := by decide

/-- Negative: the fixup sequence is not the naive `(x + t) >>> ℓ` evaluated
with 8-bit wrap-around (which overflows at `x = 255`, `t = 36`). -/
theorem fixupQuot_neg_example :
    fixupQuot 8 37 3 255 ≠ ((255 + (255 * 37) >>> 8) % 2 ^ 8) >>> 3 := by decide

/-! ### `SignedRange` -/

/-- Positive: `-128` and `127` are signed 8-bit values. -/
theorem signedRange_pos_examples : SignedRange 8 (-128) ∧ SignedRange 8 127 := by decide

/-- Negative: `128` and `-129` are not signed 8-bit values. -/
theorem signedRange_neg_examples : ¬ SignedRange 8 128 ∧ ¬ SignedRange 8 (-129) := by decide

/-- Width `0`: the only signed `0`-bit value is `0` (as for core `BitVec 0`);
`-1` is not one. -/
theorem signedRange_zero_examples : SignedRange 0 0 ∧ ¬ SignedRange 0 (-1) := by decide

/-! ### Core arithmetic shift on `Int` (sanity of the model) -/

/-- Core `Int` right shift floors: `-1 >>> 1 = -1`, `-7 >>> 1 = -4`,
`7 >>> 1 = 3`. -/
theorem int_shiftRight_examples :
    (-1 : Int) >>> 1 = -1 ∧ (-7 : Int) >>> 1 = -4 ∧ (7 : Int) >>> 1 = 3 := by decide

/-! ### `sdivMagic`, `sdivMagicUncorrected` -/

/-- Positive: with `(m, k) = (171, 9)` (8-bit signed division by 3),
`sdivMagic` gives `tdiv (-7) 3 = -2` and `tdiv 7 3 = 2`. -/
theorem sdivMagic_pos_examples :
    sdivMagic 171 9 (-7) = Int.tdiv (-7) 3 ∧ sdivMagic 171 9 7 = Int.tdiv 7 3 := by decide

/-- Negative: `sdivMagic` is not floor division (`fdiv (-7) 3 = -3`), and the
uncorrected sequence is not truncating division. -/
theorem sdivMagic_neg_examples :
    sdivMagic 171 9 (-7) ≠ Int.fdiv (-7) 3 ∧
      sdivMagicUncorrected 171 9 (-7) ≠ Int.tdiv (-7) 3 := by decide

/-- Positive: the uncorrected sequence agrees with truncating division on a
nonnegative dividend and is one below it on a negative one. -/
theorem sdivMagicUncorrected_pos_examples :
    sdivMagicUncorrected 171 9 7 = Int.tdiv 7 3 ∧
      sdivMagicUncorrected 171 9 (-7) = Int.tdiv (-7) 3 - 1 := by decide

/-! ### `sremMagic` -/

/-- Positive: with `(d, m, k) = (3, 171, 9)`, `sremMagic` gives
`tmod (-7) 3 = -1` and `tmod 7 3 = 1`. -/
theorem sremMagic_pos_examples :
    sremMagic 3 171 9 (-7) = Int.tmod (-7) 3 ∧ sremMagic 3 171 9 7 = Int.tmod 7 3 := by decide

/-- Negative: `sremMagic` is not the Euclidean/floor remainder
(`(-7) % 3 = 2` for `Int.emod`). -/
theorem sremMagic_neg_example : sremMagic 3 171 9 (-7) ≠ Int.emod (-7) 3 := by decide

/-! ### `signedMagic` -/

/-- Positive: `signedMagic 8 3 = 171` and `signedMagic 32 7 = 2454267027`. -/
theorem signedMagic_pos_examples :
    signedMagic 8 3 = 171 ∧ signedMagic 32 7 = 2454267027 := by decide

/-- Negative: for a power-of-two divisor the signed multiplier is not the exact
reciprocal (`2^9 / 4 = 128`); it is one larger. -/
theorem signedMagic_neg_example : signedMagic 8 4 ≠ 2 ^ 9 / 4 := by decide

/-! ### `lsrN` -/

/-- Positive: the 8-bit pattern of `-1` is `255`, and `255 >>> 5 = 7`;
`lsrN 8 0 5 = 0`. -/
theorem lsrN_pos_examples : lsrN 8 (-1) 5 = 7 ∧ lsrN 8 0 5 = 0 := by decide

/-- Negative: `lsrN` is a logical, not an arithmetic, shift. -/
theorem lsrN_neg_example : lsrN 8 (-1) 5 ≠ (-1 : Int) >>> 5 := by decide

/-! ### `biasSum`, `biasDiv` -/

/-- Positive: 8-bit, `k = 2`: the bias for `-7` is `3`, and
`biasDiv 8 2 (-7) = tdiv (-7) 4 = -1`; for `7` the bias is `0`. -/
theorem biasDiv_pos_examples :
    biasSum 8 2 (-7) = -4 ∧ biasDiv 8 2 (-7) = Int.tdiv (-7) 4 ∧
      biasDiv 8 2 7 = Int.tdiv 7 4 := by decide

/-- Negative: `biasDiv` is not the plain arithmetic shift (`-7 >>> 2 = -2`). -/
theorem biasDiv_neg_example : biasDiv 8 2 (-7) ≠ (-7 : Int) >>> 2 := by decide

/-- Negative: the bias is not added to a nonnegative dividend
(`biasSum 8 2 7 = 7`, not `7 + 3`). -/
theorem biasSum_neg_example : biasSum 8 2 7 ≠ 7 + (2 ^ 2 - 1) := by decide

/-! ### `biasSumMasked`, `biasDivMasked`, `biasDivBVMasked` -/

/-- Positive: with `1 ≤ k < N` the count-masked sequence is the same
computation (`k = 2`, `N = 8`: `tdiv (-7) 4 = -1`). -/
theorem biasDivMasked_pos_examples :
    biasSumMasked 8 2 (-7) = -4 ∧ biasDivMasked 8 2 (-7) = Int.tdiv (-7) 4 ∧
      (biasDivBVMasked 2 (BitVec.ofInt 8 (-7))).toInt = -1 := by decide

/-- Negative: at `k = 0` the logical shift count `N - 0 = N` is reduced to `0`,
so the whole mask `2^N - 1` is added and `-1` is not mapped to
`tdiv (-1) 1 = -1` (exact sum: `254`; wrapping `BitVec 8`: `-2`). -/
theorem biasDivMasked_neg_examples :
    biasDivMasked 8 0 (-1) = 254 ∧
      (biasDivBVMasked 0 (BitVec.ofInt 8 (-1))).toInt = -2 := by decide

/-! ### `biasDivBV` -/

/-- Positive: on `BitVec 8`, `biasDivBV 2 (-7) = -1`. -/
theorem biasDivBV_pos_example : (biasDivBV 2 (BitVec.ofInt 8 (-7))).toInt = -1 := by decide

/-- Negative: with `k = 8` (shift equal to the width) the wrapping addition
overflows and `-1` is mapped to `-1` instead of `tdiv (-1) 256 = 0`. -/
theorem biasDivBV_neg_example : (biasDivBV 8 (BitVec.ofInt 8 (-1))).toInt ≠ 0 := by decide

/-! ### `directRem` -/

/-- Positive: with `(m, F) = (293, 11)`, `directRem` gives `200 % 7 = 4`. -/
theorem directRem_pos_example : directRem 11 7 293 200 = 200 % 7 := by decide

/-- Negative: with the floor multiplier `292` it is wrong at `200`. -/
theorem directRem_neg_example : directRem 11 7 292 200 ≠ 200 % 7 := by decide

end Toy.MagicDiv
