import Miri.Interpreter.FloatOps

/-! Portable scalar float helpers from pinned interpret/intrinsics.rs.
Finite FMA computes the exact product-plus-addend before its single rounding. -/
namespace Miri.Interpreter
open Miri.MIR
inductive FloatIntegralRound where
  | floor | ceil | trunc | away | even
  deriving DecidableEq, Repr
inductive FloatMinMax where
  | minimum | maximum | minimumNumber | maximumNumber
  deriving DecidableEq, Repr
namespace IntrinsicFloat
private def signed (negative : Bool) (n : Nat) : Int := if negative then -(Int.ofNat n) else Int.ofNat n

def abs (value : FloatBits) : Except FloatError FloatBits := do
  let _ ← value.decode
  pure ⟨value.format, BitVec.ofNat 128 (value.bits.toNat % 2^(value.format.width-1))⟩
def copySign (left right : FloatBits) : Except FloatError FloatBits := do
  if left.format != right.format then throw .formatMismatch
  let left ← abs left
  if (← right.decode).negative then left.negate else pure left

def roundIntegral (value : FloatBits) (mode : FloatIntegralRound) : Except FloatError FloatBits := do
  let decoded ← value.decode
  match decoded.value with
  | .nan _ => pure (FloatBits.preferredNaN value.format)
  | .infinite => pure value
  | .finite n d =>
    let quotient := n/d
    let remainder := n%d
    let increment := match mode with
      | .floor => decoded.negative && remainder != 0
      | .ceil => !decoded.negative && remainder != 0
      | .trunc => false
      | .away => remainder*2 >= d
      | .even => remainder*2 > d || (remainder*2 == d && quotient%2 == 1)
    FloatBits.roundRatio value.format decoded.negative (quotient + if increment then 1 else 0) 1

def minMax (left right : FloatBits) (op : FloatMinMax) (chooseRightEqual : Bool) : Except FloatError FloatBits := do
  let comparison ← left.partialCompare right
  let number := op == .minimumNumber || op == .maximumNumber
  let minimum := op == .minimum || op == .minimumNumber
  if number && comparison == some .eq then return if chooseRightEqual then right else left
  if ← left.isNaN then
    if number then
      if !(← right.isNaN) then return right
    return FloatBits.preferredNaN left.format
  if ← right.isNaN then
    if number then return left
    return FloatBits.preferredNaN left.format
  match comparison with
  | some .lt => pure (if minimum then left else right)
  | some .gt => pure (if minimum then right else left)
  | some .eq =>
    let negative := (← left.decode).negative
    pure (if minimum == negative then left else right)
  | none => throw .inconsistentRounding

def fusedMulAdd (a b c : FloatBits) : Except FloatError FloatBits := do
  if a.format != b.format || a.format != c.format then throw .formatMismatch
  let da ← a.decode
  let db ← b.decode
  let dc ← c.decode
  let productNegative := xor da.negative db.negative
  let nan := FloatBits.preferredNaN a.format
  match da.value, db.value, dc.value with
  | .nan _, _, _ | _, .nan _, _ | _, _, .nan _ => pure nan
  | .infinite, .finite 0 _, _ | .finite 0 _, .infinite, _ => pure nan
  | .infinite, _, .infinite | _, .infinite, .infinite =>
    pure (if productNegative != dc.negative then nan else FloatBits.infinity a.format productNegative)
  | .infinite, _, _ | _, .infinite, _ => pure (FloatBits.infinity a.format productNegative)
  | _, _, .infinite => pure c
  | .finite an ad, .finite bn bd, .finite cn cd =>
    let pn := an*bn
    let pd := ad*bd
    let result := signed productNegative pn * Int.ofNat cd + signed dc.negative cn * Int.ofNat pd
    let negative := if result == 0 then pn == 0 && cn == 0 && productNegative && dc.negative else result < 0
    FloatBits.roundRatio a.format negative result.natAbs (pd*cd)

/-- Checked float-to-int before source saturation: compare the truncated exact
integer against bounds; NaNs and infinities cannot be represented. -/
def toIntegerChecked (value : FloatBits) (width : Nat) (isSigned : Bool) : Except FloatError (Option Int) := do
  if width == 0 || width > 128 then throw (.invalidIntegerWidth width)
  let decoded ← value.decode
  match decoded.value with
  | .nan _ | .infinite => pure none
  | .finite n d =>
    let result := signed decoded.negative (n/d)
    let minimum : Int := if isSigned then -(2^(width-1)) else 0
    let maximum : Int := if isSigned then 2^(width-1)-1 else 2^width-1
    pure (if minimum <= result && result <= maximum then some result else none)
end IntrinsicFloat
end Miri.Interpreter
