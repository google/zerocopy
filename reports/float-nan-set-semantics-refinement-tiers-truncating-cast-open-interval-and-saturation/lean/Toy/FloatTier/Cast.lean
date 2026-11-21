/-
Toy.FloatTier.Cast
==================

Float-to-integer conversions on the NaN-collapsed values `FP f` (the result of
a conversion never depends on a NaN's sign, quiet bit or payload).

* `FP.uval x`: the exact value of a finite `x`, scaled by `2^qneg` (so `x`
  equals `uval x / 2^qneg`); `0` for NaN and infinities.
* `trunc x`: truncation toward zero, `sign * floor(|x|)`, computed as floor
  division of the magnitude in units by `2^qneg`; `0` for NaN and infinities.
* `InOpenU W x`: `x` is finite and `-1 < x < 2^W`; `InOpenS k x`: `x` is finite
  and `-2^k - 1 < x < 2^k` (signed width `k + 1`), both as exact comparisons of
  `uval`. Both are false on NaN and on `±∞`.
* `cvtU W x` / `cvtS k x`: `to_int_unchecked`-style conversion to the unsigned
  width `W` / signed width `k + 1`. `none` models undefined behaviour: the
  input is NaN, infinite, or truncates to a value outside the target range.
* `satU W x` / `satS k x`: saturating conversion (Rust `as`): NaN gives `0`,
  `±∞` and out-of-range values clamp to the nearest bound.
* `negOne f`: the value `-1.0`; `twoPowRound f W`: `2^W` correctly rounded to
  the format (RNE, overflow to `+∞`); `roundNat f n`: the integer `n` correctly
  rounded to the format ("`n as float`").
* `rangeCheckU c x`: the guard `x > -1.0 && x < c`; `naiveCheckU W x`: the guard
  `x > -1.0 && x <= (2^W - 1 as float)`.
-/
import Toy.FloatTier.Arith

namespace Toy.FloatTier

variable {f : Fmt}

theorem Fmt.bias_lt_expCount (f : Fmt) : f.bias < f.expCount := by
  have := f.expCount_eq; omega

/-- The exact value of `x` in units of `2^(-qneg)`; `0` for NaN and infinities. -/
def FP.uval (x : FP f) : Int := sval x.signBit x.units

/-- Truncation toward zero: sign applied to the floor division of the magnitude
in units by `2^qneg`. `0` for NaN and infinities. -/
def trunc (x : FP f) : Int := sval x.signBit (x.units / 2 ^ f.qneg)

/-- `x` is finite and `-1 < x < 2^W` (exact comparison). False on NaN and
`±∞`. -/
def InOpenU (W : Nat) (x : FP f) : Prop :=
  x.isFinite = true ∧
    -((2 : Int) ^ f.qneg) < x.uval ∧ x.uval < (2 : Int) ^ W * 2 ^ f.qneg

/-- `x` is finite and `-2^k - 1 < x < 2^k` (exact comparison); signed width
`k + 1`. False on NaN and `±∞`. -/
def InOpenS (k : Nat) (x : FP f) : Prop :=
  x.isFinite = true ∧
    -(((2 : Int) ^ k + 1) * 2 ^ f.qneg) < x.uval ∧ x.uval < (2 : Int) ^ k * 2 ^ f.qneg

instance (W : Nat) (x : FP f) : Decidable (InOpenU W x) := by unfold InOpenU; infer_instance
instance (k : Nat) (x : FP f) : Decidable (InOpenS k x) := by unfold InOpenS; infer_instance

/-- Unchecked conversion to unsigned width `W`: `some (trunc x)` if `x` is
finite and `trunc x ∈ [0, 2^W - 1]`, otherwise `none` (undefined behaviour). -/
def cvtU (W : Nat) (x : FP f) : Option Int :=
  if x.isFinite = true ∧ 0 ≤ trunc x ∧ trunc x ≤ 2 ^ W - 1 then some (trunc x) else none

/-- Unchecked conversion to signed width `k + 1`: `some (trunc x)` if `x` is
finite and `trunc x ∈ [-2^k, 2^k - 1]`, otherwise `none`. -/
def cvtS (k : Nat) (x : FP f) : Option Int :=
  if x.isFinite = true ∧ -(2 ^ k) ≤ trunc x ∧ trunc x ≤ 2 ^ k - 1 then some (trunc x) else none

/-- Saturating conversion to unsigned width `W`: NaN ↦ 0, `-∞` ↦ 0,
`+∞` ↦ `2^W - 1`, finite `x` ↦ `trunc x` clamped to `[0, 2^W - 1]`. -/
def satU (W : Nat) (x : FP f) : Int :=
  match x with
  | .nan => 0
  | .inf s => if s then 0 else 2 ^ W - 1
  | .fin .. => max 0 (min (trunc x) (2 ^ W - 1))

/-- Saturating conversion to signed width `k + 1`: NaN ↦ 0, `-∞` ↦ `-2^k`,
`+∞` ↦ `2^k - 1`, finite `x` ↦ `trunc x` clamped to `[-2^k, 2^k - 1]`. -/
def satS (k : Nat) (x : FP f) : Int :=
  match x with
  | .nan => 0
  | .inf s => if s then -(2 ^ k) else 2 ^ k - 1
  | .fin .. => max (-(2 ^ k)) (min (trunc x) (2 ^ k - 1))

/-- `-1.0`: sign set, biased exponent `bias` (exponent `0`), trailing
significand `0`. -/
def negOne (f : Fmt) : FP f := .fin true ⟨f.bias, f.bias_lt_expCount⟩ ⟨0, f.fracCount_pos⟩

/-- `2^W` correctly rounded (RNE) to the format, overflowing to `+∞`. -/
def twoPowRound (f : Fmt) (W : Nat) : FP f := round f false (2 ^ (W + f.qneg)) 0

/-- The integer `n` correctly rounded (RNE) to the format ("`n as float`"). -/
def roundNat (f : Fmt) (n : Nat) : FP f := round f false (n * 2 ^ f.qneg) 0

/-- `2^W` does not exceed the largest finite value. For a power of two this is
the same as being representable in the format (`twoPowRound_of_fits`,
`twoPowRound_of_not_fits`). -/
def TwoPowFits (f : Fmt) (W : Nat) : Prop := 2 ^ (W + f.qneg) ≤ f.maxUnits

instance (W : Nat) : Decidable (TwoPowFits f W) := by unfold TwoPowFits; infer_instance

/-- The range guard `x > -1.0 && x < c`. -/
def rangeCheckU (c x : FP f) : Bool := lt (negOne f) x && lt x c

/-- The guard `x > -1.0 && x <= (2^W - 1 as float)`. -/
def naiveCheckU (W : Nat) (x : FP f) : Bool := lt (negOne f) x && le x (roundNat f (2 ^ W - 1))

/-- IEEE 754 binary32: exponent field width 8, precision 24. -/
def Fbin32 : Fmt := ⟨8, 24, by decide, by decide⟩

end Toy.FloatTier
