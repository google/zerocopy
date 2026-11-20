import Miri.Interpreter.IntrinsicFloat

/-! Source math.rs portable bit operations and digit-by-digit square root.
IEEE encodings/rational rounding use the existing exact FloatBits engine. -/
namespace Miri.Interpreter.Math
open Miri.ABI Miri.Memory Miri.MIR

private def exponent (n d : Nat) : Int :=
  if n >= d then Int.ofNat (n/d).log2 else
    let k := (d/n).log2
    if n*2^k >= d then -(Int.ofNat k) else -(Int.ofNat k+1)
private def scaleRatio (n d : Nat) (power : Int) : Nat × Nat :=
  if power >= 0 then (n*2^power.toNat,d) else (n,d*2^(-power).toNat)

def scalbn (value : FloatBits) (power : Int) : Except FloatError FloatBits := do
  let decoded ← value.decode
  match decoded.value with
  | .nan _ => value.convert value.format
  | .infinite => pure value
  | .finite n d =>
    let maxChange := value.format.maxExponent - (value.format.minExponent - Int.ofNat value.format.fractionBits)+1
    let power := max (-maxChange-1) (min maxChange power)
    let (n,d) := scaleRatio n d power
    FloatBits.roundRatio value.format decoded.negative n d

/-- Source software square root: zero/NaN signs are preserved before the
wrapper's separate NaN adjustment; finite values run the actual bit-by-bit loop. -/
def sqrt (value : FloatBits) : Except FloatError FloatBits := do
  let decoded ← value.decode
  match decoded.value with
  | .nan _ => pure value
  | .finite 0 _ => pure value
  | _ =>
    if decoded.negative then return FloatBits.preferredNaN value.format
    match decoded.value with
    | .infinite => pure (FloatBits.infinity value.format)
    | .nan _ => pure value
    | .finite n d =>
      let precision := value.format.fractionBits
      let mut exp := exponent n d
      let (mn,md) := scaleRatio n d (Int.ofNat precision-exp)
      if mn % md != 0 then throw .inconsistentRounding
      let mut mantissa := mn/md
      if exp % 2 != 0 then
        exp := exp-1
        mantissa := mantissa*2
      let mut result := 0
      let mut remainder := mantissa*2
      let mut s := 0
      for bit in (List.range (precision+2)).reverse do
        let digit := 2^bit
        let t := s+digit
        if remainder >= t then
          result := result+digit
          s := s+digit+digit
          remainder := remainder-t
        remainder := remainder*2
      result := (result+1)/2
      let rounded ← FloatBits.fromInteger value.format (Int.ofNat result)
      scalbn rounded (exp/2-Int.ofNat precision)

def isZero (value : FloatBits) : Except FloatError Bool := do
  pure (match (← value.decode).value with | .finite n _ => n == 0 | _ => false)
def isInfinite (value : FloatBits) : Except FloatError Bool := do
  pure (match (← value.decode).value with | .infinite => true | _ => false)
def isFinite (value : FloatBits) : Except FloatError Bool := do
  pure (match (← value.decode).value with | .finite .. => true | _ => false)
def negative (value : FloatBits) : Except FloatError Bool := do pure (← value.decode).negative

/-- IEEE nextUp, including source signaling-NaN default result. -/
def nextUp (value : FloatBits) : Except FloatError FloatBits := do
  let decoded ← value.decode
  match decoded.value with
  | .nan _ =>
    if ← value.isSignaling then
      IntrinsicFloat.copySign (FloatBits.preferredNaN value.format) value
    else pure value
  | .infinite =>
    if !decoded.negative then pure value
    else pure ⟨value.format, value.bits-1⟩
  | .finite 0 _ => pure ⟨value.format,1⟩
  | .finite .. => pure ⟨value.format, if decoded.negative then value.bits-1 else value.bits+1⟩

def nextDown (value : FloatBits) : Except FloatError FloatBits := do
  let negated ← value.negate
  (← nextUp negated).negate

/-- Source rustc_apfloat maximum/minimum preserve the selected NaN payload,
with -0 less than +0. NaN nondeterminism belongs to the outer machine wrapper. -/
def extremum (left right : FloatBits) (maximum : Bool) : Except FloatError FloatBits := do
  if ← left.isNaN then return left
  if ← right.isNaN then return right
  if ← isZero left then
    if ← isZero right then
      let ln ← negative left
      let rn ← negative right
      if ln != rn then return if maximum == ln then right else left
  let compared ← left.partialCompare right
  if maximum then pure (if compared == some .lt then right else left)
  else pure (if compared == some .gt then right else left)

/-- Source uses these exact core float PI bit patterns, not a real-number π. -/
def pi (format : FloatFormat) : Except StepError FloatBits :=
  match format with
  | .binary16 => pure ⟨format,0x4248⟩
  | .binary32 => pure ⟨format,0x40490fdb⟩
  | .binary64 => pure ⟨format,0x400921fb54442d18⟩
  | .binary128 => throw (.unsupported "source host math f128 is unimplemented")

def stripSuffix (name : String) : String :=
  let name := (["f16","f32","f64","f128"].findSome? fun suffix =>
    if name.endsWith suffix then some ((name.dropEnd suffix.length).toString) else none).getD name
  if name == "erf" then name else if name.endsWith "f" then (name.dropEnd 1).toString else name

end Miri.Interpreter.Math
