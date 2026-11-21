/-
Toy.Float.Instances
===================

Concrete formats used for bounded (exhaustively checked) results,
counterexamples and non-vacuity witnesses, and a constructor for writing
values as `m * 2^k`.
-/
import Toy.Float.Lemmas

namespace Toy.Float

/-- The `(3,3)` toy format: bias 3, `emin = -2`, `emax = 3`; 59 values (one
NaN, `±∞`, 56 finite values including `±0` and 6 positive subnormals);
largest finite value 14, smallest positive normal 1/4, smallest positive
subnormal 1/16. -/
def F33 : Fmt := ⟨3, 3, by decide, by decide⟩

/-- The `(2,2)` toy format: bias 1; 15 values; largest finite value 3,
smallest positive subnormal 1/2. -/
def F22 : Fmt := ⟨2, 2, by decide, by decide⟩

/-- The `(2,3)` toy format: bias 1; 27 values; largest finite value 3.5. -/
def F23 : Fmt := ⟨2, 3, by decide, by decide⟩

/-- The `(3,2)` toy format: bias 3; 31 values; largest finite value 12. -/
def F32 : Fmt := ⟨3, 2, by decide, by decide⟩

/-- The `(3,4)` toy format: bias 3; 115 values; largest finite value 15. -/
def F34 : Fmt := ⟨3, 4, by decide, by decide⟩

/-- Wide formats for double rounding: `W<e><p>` has exponent width `e` and
precision `p`. -/
def W29 : Fmt := ⟨2, 9, by decide, by decide⟩
def W34 : Fmt := ⟨3, 4, by decide, by decide⟩
def W36 : Fmt := ⟨3, 6, by decide, by decide⟩
def W37 : Fmt := ⟨3, 7, by decide, by decide⟩
def W38 : Fmt := ⟨3, 8, by decide, by decide⟩
def W46 : Fmt := ⟨4, 6, by decide, by decide⟩
def W57 : Fmt := ⟨5, 7, by decide, by decide⟩
def W58 : Fmt := ⟨5, 8, by decide, by decide⟩

/-- The value nearest to `m * 2^k` for an integer `m` (RNE); exact whenever
`m * 2^k` is representable, e.g. `dy F33 5 (-4) = 0.3125`. -/
def dy (f : Fmt) (m : Int) (k : Int) : FP f := ofDyadic f (decide (m < 0)) m.natAbs k

end Toy.Float
