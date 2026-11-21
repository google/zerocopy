/-
Toy.Float.Examples
==================

Positive examples (instances a definition must admit / values it must
produce) and negative examples (instances it must reject / values it must
not produce) for every core definition. All are fully proved by kernel
evaluation in the `(3,3)` toy format `F33` (largest finite value 14,
smallest positive subnormal 1/16).
-/
import Toy.Float.Rewrites

namespace Toy.Float

/-! ### `Fmt` -/

/-- Positive: the parameters of `F33`. One unit is `2^-4`, so the largest
finite magnitude `224` units is `14`. -/
theorem ex_fmt_pos_F33 :
    F33.bias = 3 ∧ F33.expCount = 7 ∧ F33.fracCount = 4 ∧ F33.qneg = 4 ∧ F33.maxUnits = 224 := by
  decide

/-- Negative: no format has a one-bit exponent field (such a format would have
no normal numbers). -/
theorem ex_fmt_neg_no_one_bit_exponent (f : Fmt) : f.e ≠ 1 := by
  have := f.two_le_e; omega

/-! ### `FP` and its encoding -/

/-- Positive: IEEE bit patterns in `F33` (1 sign, 3 exponent, 2 trailing bits):
`1.0 = 0 011 00`, `-0.0 = 1 000 00`, `+∞ = 0 111 00`, NaN `= 0 111 10`. -/
theorem ex_bits_pos_F33 :
    (one F33).bits = 12 ∧ (negZero F33).bits = 32 ∧ (FP.inf false : FP F33).bits = 28 ∧
    (FP.nan : FP F33).bits = 30 := by
  decide +kernel

/-- Equality on `FP F33` is identity of encodings: distinct values have
distinct bit patterns. -/
theorem ex_bits_injective_F33 : ∀ x y : FP F33, x.bits = y.bits → x = y := by
  decide +kernel

/-- Negative: `+0` and `-0` are distinct values (distinct encodings). -/
theorem ex_fp_neg_zeros_distinct_F33 : posZero F33 ≠ negZero F33 := by
  decide

/-! ### `unitsOf` -/

/-- Positive: `1.0` is `2^qneg = 16` units; the smallest normal `1/4` is 4 units. -/
theorem ex_units_pos_F33 : (one F33).units = 16 ∧ unitsOf F33 1 0 = 4 := by
  decide +kernel

/-- Negative: a subnormal has no hidden bit: fields `E = 0, M = 1` give 1 unit,
not `2^(p-1) + 1 = 5`. -/
theorem ex_units_neg_F33 : unitsOf F33 0 1 = 1 ∧ unitsOf F33 0 1 ≠ 5 := by
  decide

/-! ### `round` (via `ofDyadic`/`dy`) -/

/-- Positive: ties go to even (`2.25 → 2`, `2.75 → 3`, `3/32 → 1/8`,
`1/32 → +0`); the overflow threshold `15` rounds to `+∞`; `14.5` rounds to
`14`. -/
theorem ex_round_pos_F33 :
    dy F33 9 (-2) = dy F33 2 0 ∧ dy F33 11 (-2) = dy F33 3 0 ∧
    dy F33 3 (-5) = dy F33 1 (-3) ∧ dy F33 1 (-5) = posZero F33 ∧
    dy F33 15 0 = .inf false ∧ dy F33 29 (-1) = dy F33 14 0 := by
  decide +kernel

/-- Negative: `2.25` does not round up to `2.5`, and `14.5` does not
overflow. -/
theorem ex_round_neg_F33 : dy F33 9 (-2) ≠ dy F33 5 (-1) ∧ dy F33 29 (-1) ≠ .inf false := by
  decide +kernel

/-- Adequacy of the field decoding: rebuilding a finite value from its sign
and magnitude returns it. -/
theorem ex_mkFin_units_F33 :
    ∀ x : FP F33, x.isFinite = true → mkFin F33 x.signBit x.units = x := by
  decide +kernel

/-! ### `add`, `sub` -/

/-- Positive: `1 + 1 = 2`; `(-0) + (-0) = -0`; `(+0) + (-0) = +0`;
`1 + (-1) = +0`; `∞ + (-∞) = NaN`; `2 + 0.25 = 2` (tie to even). -/
theorem ex_add_pos_F33 :
    add (one F33) (one F33) = dy F33 2 0 ∧ add (negZero F33) (negZero F33) = negZero F33 ∧
    add (posZero F33) (negZero F33) = posZero F33 ∧ add (one F33) (one F33).neg = posZero F33 ∧
    add (.inf false : FP F33) (.inf true) = .nan ∧ add (dy F33 2 0) (dy F33 1 (-2)) = dy F33 2 0 := by
  decide +kernel

/-- Negative: `(+0) + (-0)` is not `-0`; `2 + 0.25` is not `2.5`. -/
theorem ex_add_neg_F33 :
    add (posZero F33) (negZero F33) ≠ negZero F33 ∧ add (dy F33 2 0) (dy F33 1 (-2)) ≠ dy F33 5 (-1) := by
  decide +kernel

/-- Positive: `1 - 1 = +0`; `(-0) - (+0) = -0`. Negative: `(-0) - (-0)` is
not `-0`. -/
theorem ex_sub_F33 :
    sub (one F33) (one F33) = posZero F33 ∧ sub (negZero F33) (posZero F33) = negZero F33 ∧
    sub (negZero F33) (negZero F33) ≠ negZero F33 := by
  decide +kernel

/-! ### `mul` -/

/-- Positive: `(-1) * (+0) = -0`; `∞ * 0 = NaN`; `1.25 * 1.25 = 1.5`
(`1.5625` rounded); `(1/16) * (1/2) = +0` and `(1/16) * (-1/2) = -0`
(underflow keeps the sign). -/
theorem ex_mul_pos_F33 :
    mul (one F33).neg (posZero F33) = negZero F33 ∧ mul (.inf false) (posZero F33) = .nan ∧
    mul (dy F33 5 (-2)) (dy F33 5 (-2)) = dy F33 3 (-1) ∧
    mul (dy F33 1 (-4)) (dy F33 1 (-1)) = posZero F33 ∧
    mul (dy F33 1 (-4)) (dy F33 (-1) (-1)) = negZero F33 := by
  decide +kernel

/-- Negative: `(-1) * (+0)` is not `+0`. -/
theorem ex_mul_neg_F33 : mul (one F33).neg (posZero F33) ≠ posZero F33 := by
  decide +kernel

/-! ### `fma` and `exactMulAdd` -/

/-- Positive: `fma 1.25 1.25 (-1.5) = 1/16` (exact `0.0625`), while the
two-step `1.25 * 1.25 + (-1.5)` is `+0`; `fma ∞ 0 1 = NaN`;
`fma (+0) 1 (-0) = +0`; `fma (-1) (+0) (-0) = -0`; the exact value of
`1.25 * 1.25 - 1.5` is 16 in units of `2^-8`. -/
theorem ex_fma_pos_F33 :
    fma (dy F33 5 (-2)) (dy F33 5 (-2)) (dy F33 (-3) (-1)) = dy F33 1 (-4) ∧
    add (mul (dy F33 5 (-2)) (dy F33 5 (-2))) (dy F33 (-3) (-1)) = posZero F33 ∧
    fma (.inf false) (posZero F33) (one F33) = .nan ∧
    fma (posZero F33) (one F33) (negZero F33) = posZero F33 ∧
    fma (one F33).neg (posZero F33) (negZero F33) = negZero F33 ∧
    exactMulAdd (dy F33 5 (-2)) (dy F33 5 (-2)) (dy F33 (-3) (-1)) = 16 := by
  decide +kernel

/-- Negative: `fma 1.25 1.25 (-1.5)` is not `+0`. -/
theorem ex_fma_neg_F33 : fma (dy F33 5 (-2)) (dy F33 5 (-2)) (dy F33 (-3) (-1)) ≠ posZero F33 := by
  decide +kernel

/-! ### `errOf`, `ErrLe` -/

/-- Positive: `1.0` approximates the exact value `1` (256 units of `2^-8`)
with error 0; any finite error is below the infinite error. Negative: an
infinite value has infinite error, which is not below a finite one. -/
theorem ex_err_F33 :
    errOf (one F33) 256 = some 0 ∧ ErrLe (some 1) none ∧ errOf (.inf false : FP F33) 256 = none ∧
    ¬ ErrLe none (some 0) := by
  decide +kernel

/-! ### Comparisons -/

/-- Positive: `+0 == -0`; `-1 < +0`. Negative: `NaN == NaN` is false; both
`NaN < 1` and `NaN >= 1` are false; `NaN <= NaN` is false. -/
theorem ex_cmp_F33 :
    feq (posZero F33) (negZero F33) = true ∧ lt (one F33).neg (posZero F33) = true ∧
    feq (.nan : FP F33) .nan = false ∧ lt .nan (one F33) = false ∧ ge .nan (one F33) = false ∧
    le (.nan : FP F33) .nan = false := by
  decide +kernel

/-! ### `minLt`, `maxLt`, `minimum`, `maximum` -/

/-- Positive: `minLt 1 2 = 1`; `minLt (+0) (-0) = -0` (the second operand).
Negative: `minLt NaN 1 = 1` but `minLt 1 NaN = NaN`. -/
theorem ex_minLt_F33 :
    minLt (one F33) (dy F33 2 0) = one F33 ∧ minLt (posZero F33) (negZero F33) = negZero F33 ∧
    minLt .nan (one F33) = one F33 ∧ minLt (one F33) .nan = .nan := by
  decide +kernel

/-- Positive: `minimum` orders `-0 < +0` in both argument orders and
propagates NaN; `maximum (+0) (-0) = +0`. Negative: `minimum 1 NaN` is not
`1`. -/
theorem ex_minimum_F33 :
    minimum (posZero F33) (negZero F33) = negZero F33 ∧
    minimum (negZero F33) (posZero F33) = negZero F33 ∧
    maximum (posZero F33) (negZero F33) = posZero F33 ∧
    minimum .nan (one F33) = .nan ∧ minimum (one F33) .nan ≠ one F33 := by
  decide +kernel

/-! ### `zeroBlind`, `EqNsz`, `Rel` -/

/-- Positive: `+0` and `-0` are equal up to the sign of zero. Negative: `1`
and `-1` are not; NaN and `+0` are not. -/
theorem ex_eqNsz_F33 :
    EqNsz (posZero F33) (negZero F33) ∧ ¬ EqNsz (one F33) (one F33).neg ∧
    ¬ EqNsz (.nan : FP F33) (posZero F33) := by
  decide +kernel

/-- Positive: under `nsz` the result relation identifies `+0` and `-0`.
Negative: without `nsz` it does not. -/
theorem ex_rel_F33 : Rel fNsz (posZero F33) (negZero F33) ∧ ¬ Rel {} (posZero F33) (negZero F33) := by
  decide +kernel

/-! ### `cvt`, `addVia` -/

/-- Positive: widening `F33 → W38` and narrowing back is the identity;
`2.75` in `W34` narrows to `3` (tie to even); `1 + 1` via `W38` is `2`.
Negative: `2.6875` in `W38` narrows to `2.5`, not `3`. -/
theorem ex_cvt_F33 :
    (∀ x : FP F33, cvt W38 F33 (cvt F33 W38 x) = x) ∧
    cvt W34 F33 (dy W34 11 (-2)) = dy F33 3 0 ∧ addVia W38 (one F33) (one F33) = dy F33 2 0 ∧
    cvt W38 F33 (dy W38 43 (-4)) ≠ dy F33 3 0 := by
  decide +kernel

/-! ### `Flags.Sub`, `Expr.variants`, `Admissible`, `ValidMod` -/

/-- Positive: `{nsz} ⊆ all`. Negative: `{nnan} ⊄ {nsz}`. -/
theorem ex_flagsSub : Flags.Sub fNsz Flags.all ∧ ¬ Flags.Sub fNnan fNsz := by
  decide

/-- Positive: `contract` permits `fma x y z` for `x * y + z`, and `reassoc`
permits `x + (y + z)` for `(x + y) + z`. Negative: `reassoc` does not permit
`fma x y z` for `x * y + z`, and without permissions the only form of
`(x + y) + z` is itself. -/
theorem ex_variants_F33 :
    (rwContract F33).rhs ∈ (rwContract F33).lhs.variants fContract ∧
    (rwAddAssoc F33).rhs ∈ (rwAddAssoc F33).lhs.variants fReassoc ∧
    (rwContract F33).rhs ∉ (rwContract F33).lhs.variants fReassoc ∧
    (rwAddAssoc F33).lhs.variants {} = [(rwAddAssoc F33).lhs] := by
  decide +kernel

/-- Positive: `x - x` at `x = 1` is admissible under `nnan`. Negative: at
`x = +∞` it is not, because the result `∞ - ∞` is NaN (the restriction covers
results, not only inputs); `x + x` at the largest finite value is not
admissible under `ninf`, because the result overflows. -/
theorem ex_admissible_F33 :
    Admissible fNnan (rwSubSelf F33).lhs (env1 (one F33)) ∧
    ¬ Admissible fNnan (rwSubSelf F33).lhs (env1 (.inf false)) ∧
    ¬ Admissible { ninf := true } (Expr.add (.var 0) (.var 0)) (env1 (maxFinite F33 false)) := by
  decide +kernel

/-- Positive: `x + (-0) → x` is valid in `F33`. Negative: `x + (+0) → x` is
not (it fails at `x = -0`). -/
theorem ex_validMod_F33 : Valid (rwAddNegZero F33) ∧ ¬ Valid (rwAddPosZero F33) := by
  decide +kernel

end Toy.Float
