/-
Toy.FloatTier.Base
==================

A small decidable model of IEEE 754-style binary floating-point arithmetic with
round-to-nearest-ties-to-even (RNE) and a single collapsed NaN.

Provenance: this file is a verbatim copy, with the namespace renamed from
`Toy.Float` to `Toy.FloatTier`, of lines 29-242 (formats, values, rounding,
`add`, `sub`, `mul`) and lines 303-344 (comparisons, `zeroBlind`, `EqNsz`) of
`lean/Toy/Float/Defs.lean` in the published package
`floating-point-algebraic-laws-reassociation-contraction-signed-zero-and-nan`
(sha256 of that file:
`cde6a65729768940710224a3aa69ed4e45c80a505d896ee091ce82af09d62564`).
Nothing was changed except the namespace lines.

In this package `FP f` is the *NaN-collapsed* view of a value: the
payload-carrying values are `V f` (`Toy.FloatTier.NaNVal`), and `V.toFP`
forgets the sign, quiet bit and payload of a NaN.
-/

namespace Toy.FloatTier

/-! ## Formats -/

/-- A binary floating-point format with exponent-field width `e` and precision
`p` (significand bits including the hidden bit). The bounds `2 ≤ e` and
`2 ≤ p` exclude degenerate formats without normal numbers or without a
fractional significand bit. Captures: the parameters `(w, p)` of an IEEE 754
binary interchange format (binary32 is `e = 8`, `p = 24`). -/
structure Fmt where
  e : Nat
  p : Nat
  two_le_e : 2 ≤ e
  two_le_p : 2 ≤ p

namespace Fmt

variable (f : Fmt)

/-- Exponent bias `2^(e-1) - 1`; `emax = bias`, `emin = 1 - bias`. -/
def bias : Nat := 2 ^ (f.e - 1) - 1

/-- Number of biased-exponent field values used by finite numbers:
`E ∈ [0, 2^e - 2]` (the all-ones field encodes infinities and NaN). -/
def expCount : Nat := 2 ^ f.e - 1

/-- Number of trailing-significand field values, `2^(p-1)`. -/
def fracCount : Nat := 2 ^ (f.p - 1)

/-- One unit (the smallest positive subnormal) is `2^(-qneg)`, where
`qneg = bias + p - 2 = -(emin - p + 1)`. -/
def qneg : Nat := f.bias + f.p - 2

/-- The largest finite magnitude, in units: `(2^p - 1) * 2^(2^e - 3)`. -/
def maxUnits : Nat := (2 ^ f.p - 1) * 2 ^ (2 ^ f.e - 3)

theorem four_le_two_pow_e : 4 ≤ 2 ^ f.e :=
  calc 4 = 2 ^ 2 := rfl
    _ ≤ 2 ^ f.e := Nat.pow_le_pow_right (by decide) f.two_le_e

theorem expCount_pos : 0 < f.expCount := by
  unfold expCount; have := f.four_le_two_pow_e; omega

theorem fracCount_pos : 0 < f.fracCount := Nat.two_pow_pos _

end Fmt

/-! ## Values -/

/-- The values of format `f`, by IEEE fields. `fin neg E M` is the finite value
with sign `neg`, biased exponent `E` (`E = 0`: zero or subnormal) and trailing
significand `M`. There is exactly one NaN (payload and sign collapsed). -/
inductive FP (f : Fmt) where
  | nan : FP f
  | inf (neg : Bool) : FP f
  | fin (neg : Bool) (E : Fin f.expCount) (M : Fin f.fracCount) : FP f
  deriving DecidableEq, Repr

variable {f : Fmt}

/-- Magnitude in units of the finite value with fields `E`, `M`:
`M` if `E = 0`, else `(2^(p-1) + M) * 2^(E-1)`. -/
def unitsOf (f : Fmt) (E M : Nat) : Nat :=
  if E = 0 then M else (f.fracCount + M) * 2 ^ (E - 1)

namespace FP

/-- Magnitude in units (0 for NaN and infinities). -/
def units : FP f → Nat
  | .fin _ E M => unitsOf f E.val M.val
  | _ => 0

/-- Sign bit (`false` for the collapsed NaN). -/
def signBit : FP f → Bool
  | .nan => false
  | .inf s => s
  | .fin s _ _ => s

def isNaN : FP f → Bool
  | .nan => true
  | _ => false

def isInf : FP f → Bool
  | .inf _ => true
  | _ => false

def isFinite : FP f → Bool
  | .fin .. => true
  | _ => false

/-- `±0`. -/
def isZero : FP f → Bool
  | .fin _ E M => E.val == 0 && M.val == 0
  | _ => false

/-- Normal numbers: finite with `E ≠ 0`. -/
def isNormal : FP f → Bool
  | .fin _ E _ => E.val != 0
  | _ => false

/-- IEEE bit pattern (sign, exponent field, trailing significand), with the
collapsed NaN encoded as the canonical positive quiet NaN. -/
def bits : FP f → Nat
  | .nan => (2 ^ f.e - 1) * 2 ^ (f.p - 1) + 2 ^ (f.p - 2)
  | .inf s => (if s then 2 ^ (f.e + f.p - 1) else 0) + (2 ^ f.e - 1) * 2 ^ (f.p - 1)
  | .fin s E M => (if s then 2 ^ (f.e + f.p - 1) else 0) + E.val * 2 ^ (f.p - 1) + M.val

/-- Negation: flips the sign bit (NaN is collapsed, so `neg nan = nan`). -/
def neg : FP f → FP f
  | .nan => .nan
  | .inf s => .inf (!s)
  | .fin s E M => .fin (!s) E M

end FP

/-- Signed zero. -/
def zero (f : Fmt) (neg : Bool) : FP f :=
  .fin neg ⟨0, f.expCount_pos⟩ ⟨0, f.fracCount_pos⟩

/-- `+0.0`. -/
abbrev posZero (f : Fmt) : FP f := zero f false
/-- `-0.0`. -/
abbrev negZero (f : Fmt) : FP f := zero f true

/-! ## Rounding -/

/-- `bitLenAux k n` = number of binary digits of `n`, computed with fuel `k`. -/
def bitLenAux : Nat → Nat → Nat
  | 0, _ => 0
  | k + 1, n => if n = 0 then 0 else bitLenAux k (n / 2) + 1

/-- Number of binary digits of `n` (`bitLen 0 = 0`, `bitLen 5 = 3`). -/
def bitLen (n : Nat) : Nat := bitLenAux n n

/-- Round-to-nearest-ties-to-even of the nonnegative rational `m / 2^d` to an
integer. -/
def rneDiv (m d : Nat) : Nat :=
  let q := m / 2 ^ d
  let r := m % 2 ^ d
  if 2 * r > 2 ^ d ∨ (2 * r = 2 ^ d ∧ q % 2 = 1) then q + 1 else q

/-- RNE of the nonnegative rational `m / 2^d` (in units) to the grid of
magnitudes representable with precision `p` and unbounded exponent above:
every integer below `2^p`, and above that every multiple of `2^t` in the
binade `[2^(t+p-1), 2^(t+p))`. -/
def roundUnits (f : Fmt) (m d : Nat) : Nat :=
  let t := bitLen (m / 2 ^ d) - f.p
  rneDiv m (d + t) * 2 ^ t

/-- Biased exponent field of a representable magnitude `n` (in units). -/
def decodeE (f : Fmt) (n : Nat) : Nat :=
  if n < f.fracCount then 0 else bitLen n - f.p + 1

/-- Trailing significand field of a representable magnitude `n` (in units). -/
def decodeM (f : Fmt) (n : Nat) : Nat :=
  if n < f.fracCount then n else n / 2 ^ (bitLen n - f.p) - f.fracCount

/-- The value with sign `neg` and representable magnitude `n` units; `±∞` if
`n` exceeds the largest finite magnitude. (The `%` are no-ops on
representable inputs; they only make the fields well-typed.) -/
def mkFin (f : Fmt) (neg : Bool) (n : Nat) : FP f :=
  if f.maxUnits < n then .inf neg
  else .fin neg ⟨decodeE f n % f.expCount, Nat.mod_lt _ f.expCount_pos⟩
                ⟨decodeM f n % f.fracCount, Nat.mod_lt _ f.fracCount_pos⟩

/-- Correct rounding (RNE, overflow to `±∞`) of the exact value
`±(m / 2^d)` units; the sign `neg` is kept also when the result is zero. -/
def round (f : Fmt) (neg : Bool) (m d : Nat) : FP f :=
  mkFin f neg (roundUnits f m d)

/-- The value nearest to `±m * 2^k` (RNE), e.g. `ofDyadic f false 3 (-1) = 1.5`. -/
def ofDyadic (f : Fmt) (neg : Bool) (m : Nat) (k : Int) : FP f :=
  if 0 ≤ k + f.qneg then round f neg (m * 2 ^ (k + f.qneg).toNat) 0
  else round f neg m (-(k + f.qneg)).toNat

/-- `1.0`. -/
def one (f : Fmt) : FP f := ofDyadic f false 1 0

/-- The largest finite value `(2 - 2^(1-p)) * 2^emax`. -/
def maxFinite (f : Fmt) (neg : Bool) : FP f := mkFin f neg f.maxUnits

/-- Signed integer value in units. -/
def sval (neg : Bool) (u : Nat) : Int := if neg then -(u : Int) else (u : Int)

/-! ## Arithmetic -/

/-- IEEE addition with RNE. NaN in, NaN out; `∞ + (-∞) = NaN`; an exact zero
sum is `+0` unless both operands are `-0` (IEEE 754-2019 §6.3, RNE). -/
def add : FP f → FP f → FP f
  | .nan, _ => .nan
  | .inf _, .nan => .nan
  | .fin .., .nan => .nan
  | .inf s, .inf t => if s = t then .inf s else .nan
  | .inf s, .fin .. => .inf s
  | .fin .., .inf t => .inf t
  | .fin s E M, .fin t E' M' =>
    let v := sval s (unitsOf f E.val M.val) + sval t (unitsOf f E'.val M'.val)
    if v = 0 then zero f (s && t) else round f (decide (v < 0)) v.natAbs 0

/-- IEEE subtraction, `x - y = x + (-y)`. -/
def sub (x y : FP f) : FP f := add x y.neg

/-- IEEE multiplication with RNE. The sign of a non-NaN product is the
exclusive or of the operand signs, also when the result is zero;
`∞ * 0 = NaN`. -/
def mul : FP f → FP f → FP f
  | .nan, _ => .nan
  | .inf _, .nan => .nan
  | .fin .., .nan => .nan
  | .inf s, .inf t => .inf (s != t)
  | .inf s, .fin t E M => if unitsOf f E.val M.val = 0 then .nan else .inf (s != t)
  | .fin s E M, .inf t => if unitsOf f E.val M.val = 0 then .nan else .inf (s != t)
  | .fin s E M, .fin t E' M' =>
    round f (s != t) (unitsOf f E.val M.val * unitsOf f E'.val M'.val) f.qneg

/-! ## Comparisons -/

/-- Order key for non-NaN values: `-∞ < negatives < ±0 < positives < +∞`,
with `key (-0) = key (+0) = 0`. -/
def key : FP f → Int
  | .nan => 0
  | .inf s => sval s (f.maxUnits + 1)
  | .fin s E M => sval s (unitsOf f E.val M.val)

/-- IEEE quiet `<`: false if either operand is NaN. -/
def lt (x y : FP f) : Bool := !x.isNaN && !y.isNaN && decide (key x < key y)
/-- IEEE quiet `≤`: false if either operand is NaN. -/
def le (x y : FP f) : Bool := !x.isNaN && !y.isNaN && decide (key x ≤ key y)
/-- IEEE quiet `>=`. -/
def ge (x y : FP f) : Bool := le y x
/-- IEEE `==`: false if either operand is NaN; `-0 == +0`. -/
def feq (x y : FP f) : Bool := !x.isNaN && !y.isNaN && decide (key x = key y)

/-- `min` defined by `<` as in `x < y ? x : y`. -/
def minLt (x y : FP f) : FP f := if lt x y then x else y
/-- `max` defined by `<` as in `x > y ? x : y`. -/
def maxLt (x y : FP f) : FP f := if lt y x then x else y

/-- Key refining `key` by `-0 < +0` (injective on non-NaN values). -/
def totalKey (x : FP f) : Int := 2 * key x + (if x = posZero f then 1 else 0)

/-- IEEE 754-2019 `minimum`: NaN if either operand is NaN, otherwise the
smaller operand, where `-0` is less than `+0`. -/
def minimum (x y : FP f) : FP f :=
  if x.isNaN || y.isNaN then .nan else if totalKey x ≤ totalKey y then x else y
/-- IEEE 754-2019 `maximum`: NaN if either operand is NaN, otherwise the
larger operand, where `-0` is less than `+0`. -/
def maximum (x y : FP f) : FP f :=
  if x.isNaN || y.isNaN then .nan else if totalKey y ≤ totalKey x then x else y

/-- Identifies `-0` with `+0` and leaves every other value unchanged. -/
def zeroBlind (x : FP f) : FP f := if x.isZero then posZero f else x

/-- Equality up to the sign of zero (the result relation under `nsz`). -/
def EqNsz (x y : FP f) : Prop := zeroBlind x = zeroBlind y

instance (x y : FP f) : Decidable (EqNsz x y) := inferInstanceAs (Decidable (_ = _))

end Toy.FloatTier
