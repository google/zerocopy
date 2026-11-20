import Miri.MIR.Operators
import Miri.Memory.ScalarInt

/-!
Integer branches of pinned rustc_const_eval `interpret/operator.rs`.
Layout acquisition and scalar extraction are separate interpreter operations.
These entry points take their checked scalar payload and integer layout;
they do not assert that an arbitrary MIR operand has either property.
-/
namespace Miri.Interpreter

open Miri.ABI Miri.Memory Miri.MIR

structure IntegerType where
  size : Size
  kind : IntegerKind
  deriving DecidableEq, Repr

def IntegerType.signed (type : IntegerType) : Bool := type.kind.signed

structure IntegerValue where
  scalar : ScalarInt
  type : IntegerType
  deriving DecidableEq, Repr

inductive IntegerUB where
  | divisionByZero | remainderByZero | divisionOverflow | remainderOverflow
  | arithmeticOverflow (op : BinOp)
  | shiftOverflow (op : BinOp) (amount : Int) (signed : Bool)
  deriving DecidableEq, Repr

inductive IntegerOpError where
  | scalar (reason : ScalarIntError)
  | undefinedBehavior (reason : IntegerUB)
  | asymmetricTypes (left right : IntegerType)
  | invalidBinaryOperator (op : BinOp)
  | invalidUnaryOperator (op : UnOp) (signed : Bool)
  deriving DecidableEq, Repr

inductive IntegerResult where
  | scalar (value : ScalarInt)
  | withOverflow (value : ScalarInt) (overflow : Bool)
  | boolean (value : Bool)
  | ordering (value : Ordering)
  deriving DecidableEq, Repr

namespace IntegerOps

def binaryBool (op : BinOp) (l r : Bool) : Except IntegerOpError IntegerResult := do
  let result ← match op with
    | .Eq => pure (l == r) | .Ne => pure (l != r)
    | .Lt => pure (l < r) | .Le => pure (l ≤ r)
    | .Gt => pure (l > r) | .Ge => pure (l ≥ r)
    | .BitAnd => pure (l && r) | .BitOr => pure (l || r) | .BitXor => pure (xor l r)
    | _ => throw (.invalidBinaryOperator op)
  return .boolean result

def binaryChar (op : BinOp) (l r : Char) : Except IntegerOpError IntegerResult := do
  if op == .Cmp then return .ordering (compare l r)
  let result ← match op with
    | .Eq => pure (l == r) | .Ne => pure (l != r)
    | .Lt => pure (l < r) | .Le => pure (l ≤ r)
    | .Gt => pure (l > r) | .Ge => pure (l ≥ r)
    | _ => throw (.invalidBinaryOperator op)
  return .boolean result

private def scalarResult (op : BinOp) (value : ScalarInt) (overflow : Bool) :
    Except IntegerOpError IntegerResult := do
  if overflow && op.isUnchecked then throw (.undefinedBehavior (.arithmeticOverflow op))
  return if op.isOverflowing then .withOverflow value overflow else .scalar value

/-- Size-checked extraction using the source layout's signedness. -/
def decode (value : IntegerValue) : Except IntegerOpError Int :=
  if value.type.signed then value.scalar.toInt value.type.size |>.mapError .scalar
  else return Int.ofNat (← value.scalar.toUInt value.type.size |>.mapError .scalar).toNat

private def truncate (value : Int) (type : IntegerType) :
    Except IntegerOpError (ScalarInt × Bool) :=
  if type.signed then
    let wrapped := (BitVec.ofInt 128 value).toInt
    (ScalarInt.truncateFromInt wrapped type.size).mapError .scalar
  else
    (ScalarInt.truncateFromUInt (BitVec.ofInt 128 value) type.size).mapError .scalar

private def arithmetic (op : BinOp) (l r : Int) (type : IntegerType) :
    Except IntegerOpError IntegerResult := do
  if r == 0 then
    if op == .Div then throw (.undefinedBehavior .divisionByZero)
    if op == .Rem then throw (.undefinedBehavior .remainderByZero)
  if type.signed && (op == .Div || op == .Rem) then
    let min ← type.size.signedIntMin |>.mapError (IntegerOpError.scalar ∘ ScalarIntError.sizeError)
    if l == min && r == -1 then
      throw (.undefinedBehavior (if op == .Div then .divisionOverflow else .remainderOverflow))
  let result ← match op with
    | .Add | .AddUnchecked | .AddWithOverflow => pure (l + r)
    | .Sub | .SubUnchecked | .SubWithOverflow => pure (l - r)
    | .Mul | .MulUnchecked | .MulWithOverflow => pure (l * r)
    | .Div => pure (Int.tdiv l r)
    | .Rem => pure (Int.tmod l r)
    | _ => throw (.invalidBinaryOperator op)
  let hostOverflow := if type.signed then
      result < -(2 ^ 127 : Int) || result ≥ (2 ^ 127 : Int)
    else result < 0 || result ≥ (2 ^ 128 : Int)
  let (value, lossy) ← truncate result type
  scalarResult op value (hostOverflow || lossy)

/-- Shifts reduce the amount modulo the LHS width, including negative signed
RHS values. Unchecked shifts diagnose the original amount after computing
the wrapped result, as the source does. -/
private def shift (op : BinOp) (left right : IntegerValue) (l r : Int) :
    Except IntegerOpError IntegerResult := do
  let bits ← left.type.size.bits |>.mapError (IntegerOpError.scalar ∘ ScalarIntError.sizeError)
  let amount := r % Int.ofNat bits.toNat
  let overflow := amount != r
  let result := match op with
    | .Shl | .ShlUnchecked => l <<< amount.toNat
    | _ => l >>> amount.toNat
  let (value, _) ← truncate result left.type
  if overflow && op.isUnchecked then
    throw (.undefinedBehavior (.shiftOverflow op r right.type.signed))
  return .scalar value

def binary (op : BinOp) (left right : IntegerValue) : Except IntegerOpError IntegerResult := do
  -- Source checks both scalar sizes before choosing an operator branch.
  let l ← decode left
  let r ← decode right
  if op == .Shl || op == .ShlUnchecked || op == .Shr || op == .ShrUnchecked then
    return ← shift op left right l r
  if left.type != right.type then throw (.asymmetricTypes left.type right.type)
  match op with
  | .Eq => return .boolean (l == r)
  | .Ne => return .boolean (l != r)
  | .Lt => return .boolean (l < r)
  | .Le => return .boolean (l ≤ r)
  | .Gt => return .boolean (l > r)
  | .Ge => return .boolean (l ≥ r)
  | .Cmp => return .ordering (compare l r)
  | .BitAnd | .BitOr | .BitXor =>
      let lb ← left.scalar.toUInt left.type.size |>.mapError .scalar
      let rb ← right.scalar.toUInt right.type.size |>.mapError .scalar
      let bits := match op with
        | .BitAnd => lb &&& rb
        | .BitOr => lb ||| rb
        | _ => lb ^^^ rb
      let (value, _) ← ScalarInt.truncateFromUInt bits left.type.size |>.mapError .scalar
      return .scalar value
  | _ => arithmetic op l r left.type

def unary (op : UnOp) (value : IntegerValue) : Except IntegerOpError ScalarInt := do
  let integer ← decode value
  let result ← match op with
    | .Not => pure (~~~integer)
    | .Neg =>
        if value.type.signed then pure (-integer)
        else throw (.invalidUnaryOperator op value.type.signed)
    | .PtrMetadata => throw (.invalidUnaryOperator op value.type.signed)
  return (← truncate result value.type).1

/-- Source `compute_size_in_bytes` checks u64 multiplication and an inclusive
`max_size_of_val`, which differs from `Size.checkedMul`'s object-size bound. -/
def computeSizeInBytes (elementSize : Size) (count : UInt64) (maxSizeOfVal : Size) : Option Size :=
  let total := elementSize.bytes.toNat * count.toNat
  if total < 2 ^ 64 && total ≤ maxSizeOfVal.bytes.toNat then
    some (Size.ofBytes (UInt64.ofNat total))
  else none

/-- Once operand extraction and type agreement have succeeded, division by
zero is always UB; wrapping arithmetic never turns it into a successful result. -/
theorem binary_division_by_zero (left right : IntegerValue) (l : Int)
    (hl : decode left = .ok l) (hr : decode right = .ok 0)
    (ht : left.type = right.type) :
    binary .Div left right = .error (.undefinedBehavior .divisionByZero) := by
  simp [binary, hl, hr, ht, arithmetic, bind, Except.bind]
  rfl

theorem binary_remainder_by_zero (left right : IntegerValue) (l : Int)
    (hl : decode left = .ok l) (hr : decode right = .ok 0)
    (ht : left.type = right.type) :
    binary .Rem left right = .error (.undefinedBehavior .remainderByZero) := by
  simp [binary, hl, hr, ht, arithmetic, bind, Except.bind]
  rfl

theorem division_success_nonzero (left right : IntegerValue) (l r : Int)
    (hl : decode left = .ok l) (hr : decode right = .ok r)
    (ht : left.type = right.type) (value : IntegerResult)
    (success : binary .Div left right = .ok value) : r ≠ 0 := by
  intro zero
  subst r
  rw [binary_division_by_zero left right l hl hr ht] at success
  contradiction

end IntegerOps
end Miri.Interpreter
