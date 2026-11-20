import Miri.Interpreter.IntegerOps

/-!
Integer-like casts and integer numeric intrinsics from the pinned
`rustc_const_eval::interpret::{cast,intrinsics}` sources. The caller supplies
the compiler-resolved layouts. This module does not represent floating point,
raw/function pointers, or pointer provenance, so those casts cannot be routed
through these operations.
-/
namespace Miri.Interpreter

open Miri.ABI Miri.Memory Miri.MIR

inductive IntegerCastSource where
  | integer (type : IntegerType)
  | boolean
  | character
  deriving DecidableEq, Repr

inductive IntegerCastTarget where
  | integer (type : IntegerType)
  | character
  deriving DecidableEq, Repr

inductive IntegerCastError where
  | scalar (reason : ScalarIntError)
  | integerToCharTryFromPanicked (value : Nat)
  deriving DecidableEq, Repr

namespace IntegerCast

private def sourceValue (source : IntegerCastSource) (value : ScalarInt) :
    Except IntegerCastError Nat := do
  match source with
  | .integer type =>
      if type.signed then
        let signedValue ← value.toInt type.size |>.mapError .scalar
        return (BitVec.ofInt 128 signedValue).toNat
      else
        return (← value.toUInt type.size |>.mapError .scalar).toNat
  | .boolean =>
      return if (← value.tryToBool |>.mapError .scalar) then 1 else 0
  | .character =>
      return (← value.toChar |>.mapError .scalar).toNat

/-- Pinned `cast_from_int_like` behavior for integer, bool, and char inputs.
Signed integer sources are sign-extended to the source's `u128` intermediate
before destination truncation. The char target follows `u8::try_from(v).unwrap()`
and records that unwrap's panic when conversion fails. -/
def cast (source : IntegerCastSource) (value : ScalarInt)
    (target : IntegerCastTarget) : Except IntegerCastError ScalarInt := do
  let decoded ← sourceValue source value
  match target with
  | .integer type =>
      let (result, _) ← ScalarInt.truncateFromUInt (BitVec.ofNat 128 decoded) type.size
        |>.mapError .scalar
      return result
  | .character =>
      if decoded > 255 then
        throw (.integerToCharTryFromPanicked decoded)
      return ScalarInt.ofChar (Char.ofNat decoded)

end IntegerCast

inductive IntegerIntrinsic where
  | ctpop | cttz | cttzNonzero | ctlz | ctlzNonzero | bswap | bitreverse
  deriving DecidableEq, Repr

inductive IntegerIntrinsicError where
  | scalar (reason : ScalarIntError)
  | undefinedBehaviorOnZero (intrinsic : IntegerIntrinsic)
  | layoutMismatch (input output : IntegerType)
  deriving DecidableEq, Repr

namespace IntegerIntrinsic

private def countTrailingZeros (bits : Nat) (width : Nat) : Nat := Id.run do
  for index in [:width] do
    if Nat.testBit bits index then return index
  return width

private def reverseBytes (bits : Nat) (byteCount : Nat) : Nat := Id.run do
  let mut result := 0
  for index in [:byteCount] do
    let byte := (bits / (2 ^ (index * 8))) % 256
    result := result + byte * (2 ^ ((byteCount - index - 1) * 8))
  return result

/-- The pinned `numeric_intrinsic` branches. Counting ignores signedness and
uses the input width; byte swap and bit reversal require matching layouts. -/
def run (intrinsic : IntegerIntrinsic) (value : ScalarInt)
    (inputType outputType : IntegerType) : Except IntegerIntrinsicError ScalarInt := do
  let bits ← value.toBits inputType.size |>.mapError .scalar
  let width ← inputType.size.bits |>.mapError (fun e => .scalar (.sizeError e))
  let width := width.toNat
  let raw := bits.toNat
  if (intrinsic == .cttzNonzero || intrinsic == .ctlzNonzero) && raw == 0 then
    throw (.undefinedBehaviorOnZero intrinsic)
  let result ← match intrinsic with
    | .ctpop => pure bits.cpop.toNat
    | .cttz | .cttzNonzero => pure (countTrailingZeros raw width)
    | .ctlz | .ctlzNonzero =>
        if raw == 0 then pure width
        else pure (width - (Nat.log2 raw + 1))
    | .bswap =>
        if inputType != outputType then throw (.layoutMismatch inputType outputType)
        pure (reverseBytes raw inputType.size.bytes.toNat)
    | .bitreverse =>
        if inputType != outputType then throw (.layoutMismatch inputType outputType)
        let extra := 128 - width
        let aligned : U128 := bits <<< extra
        pure aligned.reverse.toNat
  let (out, _) ← ScalarInt.truncateFromUInt (BitVec.ofNat 128 result) outputType.size
    |>.mapError .scalar
  return out

end IntegerIntrinsic

inductive IntegerArithmeticIntrinsicError where
  | integerOperation (reason : IntegerOpError)
  | scalar (reason : ScalarIntError)
  | exactDivisionHasRemainder (remainder : ScalarInt)
  | unexpectedOverflowResult (result : IntegerResult)
  | unexpectedDivisionResult (result : IntegerResult)
  deriving DecidableEq, Repr

inductive IntegerSaturatingOp where
  | add | sub
  deriving DecidableEq, Repr

namespace IntegerArithmeticIntrinsic

/-- Pinned `saturating_arith`: use the source overflowing operation, then
select the signed bound using the first operand's sign or the unsigned bound
from the operation direction. -/
def saturatingArith (op : IntegerSaturatingOp) (left right : IntegerValue) :
    Except IntegerArithmeticIntrinsicError ScalarInt := do
  let mirOp := match op with
    | .add => BinOp.AddWithOverflow
    | .sub => BinOp.SubWithOverflow
  let result ← IntegerOps.binary mirOp left right |>.mapError .integerOperation
  match result with
  | .withOverflow value false => return value
  | .withOverflow _ true =>
      if left.type.signed then
        let first ← IntegerOps.decode left |>.mapError .integerOperation
        if first ≥ 0 then
          let maximum ← left.type.size.signedIntMax
            |>.mapError (fun error => .scalar (.sizeError error))
          return (← ScalarInt.truncateFromInt maximum left.type.size |>.mapError .scalar).1
        else
          let minimum ← left.type.size.signedIntMin
            |>.mapError (fun error => .scalar (.sizeError error))
          return (← ScalarInt.truncateFromInt minimum left.type.size |>.mapError .scalar).1
      else if op == .add then
        let maximum ← left.type.size.unsignedIntMax
          |>.mapError (fun error => .scalar (.sizeError error))
        return (← ScalarInt.truncateFromUInt maximum left.type.size |>.mapError .scalar).1
      else
        return (← ScalarInt.null left.type.size |>.mapError .scalar)
  | other => throw (.unexpectedOverflowResult other)

/-- Pinned `exact_div`: the ordinary remainder operation supplies division by
zero and signed MIN / -1 UB checks; a nonzero remainder is the intrinsic's own
UB branch; only then is ordinary division evaluated. -/
def exactDiv (left right : IntegerValue) :
    Except IntegerArithmeticIntrinsicError ScalarInt := do
  if left.type != right.type then
    throw (.integerOperation (.asymmetricTypes left.type right.type))
  let remainder ← IntegerOps.binary BinOp.Rem left right |>.mapError .integerOperation
  let remainder ← match remainder with
    | .scalar value => pure value
    | other => throw (.unexpectedDivisionResult other)
  if !remainder.isNull then
    throw (.exactDivisionHasRemainder remainder)
  let result ← IntegerOps.binary BinOp.Div left right |>.mapError .integerOperation
  match result with
  | .scalar value => return value
  | other => throw (.unexpectedDivisionResult other)

end IntegerArithmeticIntrinsic

end Miri.Interpreter
