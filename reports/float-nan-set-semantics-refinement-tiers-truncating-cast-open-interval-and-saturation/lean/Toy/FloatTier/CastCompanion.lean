/-
Toy.FloatTier.CastCompanion
===========================

A companion instance for `naiveCheckU_not_exact_small`: in `F33`, the bound
`2^2 - 1 as float` used by the guard `naiveCheckU 2` is exact.
-/
import Toy.FloatTier.CastExamples

namespace Toy.FloatTier

/-- **`3 as float` is exact in `F33`.** `roundNat F33 (2^2 - 1)` (natural-number
subtraction, `2^2 - 1 = 3`, no truncation since `2^2 ≥ 1`) is the finite value
with biased exponent `4` and trailing significand `2`; its exact scaled value
`uval` is `3 * 2^qneg`, so the value is exactly `3.0`. This is the bound against
which the guard `naiveCheckU 2` compares `x = 3.5` in `naiveCheckU_not_exact_small`. -/
theorem roundNat_F33_three_exact :
    roundNat F33 (2 ^ 2 - 1) = FP.mk' F33 false 4 2 ∧
      (roundNat F33 (2 ^ 2 - 1)).uval = 3 * 2 ^ F33.qneg := by decide

end Toy.FloatTier
