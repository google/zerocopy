import Miri.ABI.Size
import Miri.MIR.Operators

/-! Exact binary IEEE encodings and rational arithmetic for the four MIR float
widths. No Lean/host Float is used. Finite rounding is nearest, ties to even,
as used by pinned rustc_apfloat's default MIR operations. -/
namespace Miri.Interpreter
open Miri.ABI Miri.MIR

inductive FloatFormat where
  | binary16 | binary32 | binary64 | binary128
  deriving DecidableEq, Repr
namespace FloatFormat
 def width : FloatFormat → Nat | .binary16 => 16 | .binary32 => 32 | .binary64 => 64 | .binary128 => 128
 def exponentBits : FloatFormat → Nat | .binary16 => 5 | .binary32 => 8 | .binary64 => 11 | .binary128 => 15
 def fractionBits (f : FloatFormat) : Nat := f.width - f.exponentBits - 1
 def bias (f : FloatFormat) : Nat := 2^(f.exponentBits-1)-1
 def minExponent (f : FloatFormat) : Int := 1 - Int.ofNat f.bias
 def maxExponent (f : FloatFormat) : Int := Int.ofNat f.bias
 def size (f : FloatFormat) : Size := Size.ofBytes (UInt64.ofNat (f.width / 8))
end FloatFormat

structure FloatBits where
  format : FloatFormat
  bits : U128
  deriving DecidableEq, Repr
inductive FloatClass where
  | finite (numerator denominator : Nat)
  | infinite
  | nan (payload : Nat)
  deriving DecidableEq, Repr
structure FloatDecoded where
  negative : Bool
  value : FloatClass
  deriving DecidableEq, Repr
inductive FloatError where
  | encodingExceedsWidth
  | zeroDenominator
  | formatMismatch
  | invalidBinaryOperator (op : BinOp)
  | invalidIntegerWidth (width : Nat)
  | inconsistentRounding
  | invalidNaNChoice
  deriving DecidableEq, Repr

namespace FloatBits
private def powScale (n d : Nat) (exponent : Int) : Nat × Nat :=
  if exponent >= 0 then (n * 2^exponent.toNat, d)
  else (n, d * 2^(-exponent).toNat)
private def encode (f : FloatFormat) (negative : Bool) (exponent fraction : Nat) : FloatBits :=
  ⟨f, BitVec.ofNat 128 ((if negative then 2^(f.width-1) else 0) + exponent * 2^f.fractionBits + fraction)⟩

def zero (f : FloatFormat) (negative := false) : FloatBits := encode f negative 0 0
def infinity (f : FloatFormat) (negative := false) : FloatBits := encode f negative (2^f.exponentBits-1) 0
def preferredNaN (f : FloatFormat) : FloatBits := encode f false (2^f.exponentBits-1) (2^(f.fractionBits-1))

def decode (x : FloatBits) : Except FloatError FloatDecoded := do
  let f := x.format
  let bits := x.bits.toNat
  if bits >= 2^f.width then throw .encodingExceedsWidth
  let negative := bits / 2^(f.width-1) != 0
  let exponent := (bits / 2^f.fractionBits) % 2^f.exponentBits
  let fraction := bits % 2^f.fractionBits
  if exponent == 2^f.exponentBits-1 then
    return ⟨negative, if fraction == 0 then .infinite else .nan fraction⟩
  let significand := if exponent == 0 then fraction else 2^f.fractionBits + fraction
  let unbiased := if exponent == 0 then f.minExponent else Int.ofNat exponent - Int.ofNat f.bias
  let (n, d) := powScale significand 1 (unbiased - Int.ofNat f.fractionBits)
  return ⟨negative, .finite n d⟩

def negate (x : FloatBits) : Except FloatError FloatBits := do
  let decoded ← x.decode
  let sign := 2^(x.format.width-1)
  return ⟨x.format, BitVec.ofNat 128 (if decoded.negative then x.bits.toNat - sign else x.bits.toNat + sign)⟩

def isNaN (x : FloatBits) : Except FloatError Bool := do
  return match (← x.decode).value with | .nan _ => true | _ => false

def isSignaling (x : FloatBits) : Except FloatError Bool := do
  return match (← x.decode).value with
    | .nan payload => payload < 2^(x.format.fractionBits-1)
    | _ => false

/-- floor(log2(n/d)), for nonzero positive n,d. -/
private def ratioExponent (n d : Nat) : Int :=
  if n >= d then Int.ofNat (n / d).log2
  else
    let k := (d / n).log2
    if n * 2^k >= d then -(Int.ofNat k) else -(Int.ofNat k + 1)
private def roundQuotientEven (n d : Nat) : Nat :=
  let q := n / d
  let remainder := n % d
  if remainder * 2 > d || (remainder * 2 == d && q % 2 == 1) then q+1 else q

/-- Round an exact nonnegative rational with a separate sign. Clamping the
working exponent to MIN_EXP gives gradual subnormal underflow, including ties
at signed zero. Overflow after rounding produces infinity. -/
def roundRatio (f : FloatFormat) (negative : Bool) (n d : Nat) : Except FloatError FloatBits := do
  if d == 0 then throw .zeroDenominator
  if n == 0 then return zero f negative
  let exponent := max (ratioExponent n d) f.minExponent
  if exponent > f.maxExponent then return infinity f negative
  let (scaledN, scaledD) := powScale n d (Int.ofNat f.fractionBits - exponent)
  let significand := roundQuotientEven scaledN scaledD
  let (significand, exponent) := if significand >= 2^(f.fractionBits+1)
    then (significand / 2, exponent+1) else (significand, exponent)
  if exponent > f.maxExponent then return infinity f negative
  if significand < 2^f.fractionBits then
    if exponent != f.minExponent then throw .inconsistentRounding
    return encode f negative 0 significand
  if significand >= 2^(f.fractionBits+1) then throw .inconsistentRounding
  return encode f negative (exponent + Int.ofNat f.bias).toNat (significand - 2^f.fractionBits)

/-- Cast finite values with correct rounding. NaN payload conversion first
quiets, shifts to the target precision, and forces the target quiet bit, as
pinned ieee.rs::convert_r does. Miri's adjust_nan is applied separately. -/
def convert (x : FloatBits) (target : FloatFormat) : Except FloatError FloatBits := do
  let decoded ← x.decode
  match decoded.value with
  | .finite n d => roundRatio target decoded.negative n d
  | .infinite => return infinity target decoded.negative
  | .nan payload =>
    let quiet := Nat.lor payload (2^(x.format.fractionBits-1))
    let payload := if target.fractionBits >= x.format.fractionBits
      then quiet * 2^(target.fractionBits-x.format.fractionBits)
      else quiet / 2^(x.format.fractionBits-target.fractionBits)
    return encode target decoded.negative (2^target.exponentBits-1)
      (Nat.lor payload (2^(target.fractionBits-1)))

/-- All outcomes generated by pinned Miri operator.rs::generate_nan. Sign
choice is independent of candidate choice. A fixed seed is not a safety model. -/
def nanChoices (target : FloatFormat) (inputs : List FloatBits) (nondeterministic : Bool) :
    Except FloatError (List FloatBits) := do
  if !nondeterministic then return [preferredNaN target]
  let mut quieted := []
  let mut signaling := []
  for input in inputs do
    if ← input.isNaN then quieted := quieted ++ [← input.convert target]
    if ← input.isSignaling then
      let converted ← input.convert target
      let decoded ← converted.decode
      match decoded.value with
      | .nan payload =>
        let lower := payload % 2^(target.fractionBits-1)
        if lower != 0 then
          signaling := signaling ++ [encode target decoded.negative (2^target.exponentBits-1) lower]
      | _ => throw .inconsistentRounding
  let candidates := preferredNaN target :: (quieted ++ signaling)
  let mut signed := []
  for candidate in candidates do signed := signed ++ [candidate, ← candidate.negate]
  return signed

private def signedNumerator (negative : Bool) (n : Nat) : Int :=
  if negative then -(Int.ofNat n) else Int.ofNat n
private def exactSum (f : FloatFormat) (l r : FloatDecoded) : Except FloatError FloatBits := do
  match l.value, r.value with
  | .nan _, _ | _, .nan _ => return preferredNaN f
  | .infinite, .infinite =>
    return if l.negative != r.negative then preferredNaN f else infinity f l.negative
  | .infinite, _ => return infinity f l.negative
  | _, .infinite => return infinity f r.negative
  | .finite ln ld, .finite rn rd =>
    let n := signedNumerator l.negative ln * Int.ofNat rd + signedNumerator r.negative rn * Int.ofNat ld
    let sign := if n == 0 then ln == 0 && rn == 0 && l.negative && r.negative else n < 0
    roundRatio f sign n.natAbs (ld*rd)

/-- MIR arithmetic's base result. NaN payload/sign selection is subsequently
performed by nanChoices/adjust_nan; finite arithmetic never calls a host float. -/
def arithmetic (op : BinOp) (left right : FloatBits) : Except FloatError FloatBits := do
  if left.format != right.format then throw .formatMismatch
  let l ← left.decode
  let r ← right.decode
  let f := left.format
  match op with
  | .Add => exactSum f l r
  | .Sub => exactSum f l { r with negative := !r.negative }
  | .Mul =>
    let sign := xor l.negative r.negative
    match l.value, r.value with
    | .nan _, _ | _, .nan _ => return preferredNaN f
    | .infinite, .finite 0 _ | .finite 0 _, .infinite => return preferredNaN f
    | .infinite, _ | _, .infinite => return infinity f sign
    | .finite ln ld, .finite rn rd => roundRatio f sign (ln*rn) (ld*rd)
  | .Div =>
    let sign := xor l.negative r.negative
    match l.value, r.value with
    | .nan _, _ | _, .nan _ | .infinite, .infinite | .finite 0 _, .finite 0 _ => return preferredNaN f
    | .infinite, _ | _, .finite 0 _ => return infinity f sign
    | _, .infinite => return zero f sign
    | .finite ln ld, .finite rn rd => roundRatio f sign (ln*rd) (ld*rn)
  | .Rem =>
    match l.value, r.value with
    | .nan _, _ | _, .nan _ | .infinite, _ | _, .finite 0 _ => return preferredNaN f
    | .finite _ _, .infinite => return left
    | .finite ln ld, .finite rn rd =>
      let quotient := (ln*rd) / (ld*rn)
      let remainder := ln*rd - quotient*(ld*rn)
      roundRatio f l.negative remainder (ld*rd)
  | _ => throw (.invalidBinaryOperator op)

/-- IEEE partial ordering: both signs of zero compare equal; all NaNs are
unordered. Infinities are ordered without rational approximation. -/
def partialCompare (left right : FloatBits) : Except FloatError (Option Ordering) := do
  if left.format != right.format then throw .formatMismatch
  let l ← left.decode
  let r ← right.decode
  match l.value, r.value with
  | .nan _, _ | _, .nan _ => return none
  | .infinite, .infinite => return some (compare (!l.negative) (!r.negative))
  | .infinite, _ => return some (if l.negative then .lt else .gt)
  | _, .infinite => return some (if r.negative then .gt else .lt)
  | .finite ln ld, .finite rn rd =>
    return some (compare (signedNumerator l.negative ln * Int.ofNat rd)
      (signedNumerator r.negative rn * Int.ofNat ld))

def comparison (op : BinOp) (left right : FloatBits) : Except FloatError Bool := do
  let order ← partialCompare left right
  match op with
  | .Eq => return order == some .eq
  | .Ne => return order != some .eq
  | .Lt => return order == some .lt
  | .Le => return order == some .lt || order == some .eq
  | .Gt => return order == some .gt
  | .Ge => return order == some .gt || order == some .eq
  | _ => throw (.invalidBinaryOperator op)

def fromInteger (format : FloatFormat) (value : Int) : Except FloatError FloatBits :=
  roundRatio format (value < 0) value.natAbs 1

/-- Rust `as` float-to-int conversion saturates and truncates toward zero;
NaNs map to zero. Width and signedness are from the target compiler layout. -/
def toInteger (value : FloatBits) (width : Nat) (isSigned : Bool) : Except FloatError Int := do
  if width == 0 || width > 128 then throw (.invalidIntegerWidth width)
  let decoded ← value.decode
  let minValue : Int := if isSigned then -(2^(width-1)) else 0
  let maxValue : Int := if isSigned then 2^(width-1)-1 else 2^width-1
  match decoded.value with
  | .nan _ => return 0
  | .infinite => return if decoded.negative then minValue else maxValue
  | .finite n d => return max minValue (min maxValue (signedNumerator decoded.negative (n/d)))

/-- Every exact zero retains its input sign under nearest-even conversion. -/
theorem roundRatio_zero (format : FloatFormat) (negative : Bool) (denominator : Nat)
    (nonzero : denominator ≠ 0) :
    roundRatio format negative 0 denominator = .ok (zero format negative) := by
  simp [roundRatio, nonzero]
  rfl

/-- Saturating integer casts of any decoded NaN are exactly zero. -/
theorem nan_toInteger (value : FloatBits) (negative : Bool) (payload width : Nat)
    (decoded : value.decode = .ok ⟨negative, .nan payload⟩)
    (nonzero : width ≠ 0) (bounded : width ≤ 128) (isSigned : Bool) :
    value.toInteger width isSigned = .ok 0 := by
  simp [toInteger, decoded, nonzero, show ¬width > 128 from Nat.not_lt.mpr bounded]
  rfl

end FloatBits
end Miri.Interpreter
