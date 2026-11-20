import Miri.ABI.Size

/-!
The bounded integer payload from `rustc_middle::ty::consts::int::ScalarInt`.
The packed Rust layout is not semantically relevant here; construction keeps
the payload truncated to its nonzero 1–16 byte width. Invalid sizes and
source panics are returned explicitly.
-/

namespace Miri.Memory

open Miri.ABI

inductive ScalarIntError where
  | sizeError (reason : SizeError)
  | zeroSize
  | sizeTooLarge (size : Size)
  | sizeMismatch (expected actual : Size)
  | integerOutsideI128 (value : Int)
  | integerConversionOverflow (value : Int)
  | invalidBool (value : UInt8)
  | invalidChar (value : UInt32)
  | invalidAtomicOrdering (value : UInt32)
  | invalidSimdAlignment (value : UInt32)
  deriving DecidableEq, Repr

instance : ToString ScalarIntError where
  toString
    | .sizeError reason => toString reason
    | .zeroSize => "ScalarInt requires a nonzero byte size"
    | .sizeTooLarge size => s!"ScalarInt size {size.bytes} exceeds 16 bytes"
    | .sizeMismatch expected actual =>
        s!"ScalarInt has {actual.bytes} bytes but {expected.bytes} were requested"
    | .integerOutsideI128 value => s!"{value} does not fit in source i128"
    | .integerConversionOverflow value => s!"{value} does not fit in the requested host integer"
    | .invalidBool value => s!"{value} is not a valid bool representation"
    | .invalidChar value => s!"{value} is not a Unicode scalar value"
    | .invalidAtomicOrdering value => s!"{value} is not a valid atomic ordering"
    | .invalidSimdAlignment value => s!"{value} is not a valid SIMD alignment"

inductive AtomicOrdering where
  | relaxed
  | release
  | acquire
  | acqRel
  | seqCst
  deriving DecidableEq, Repr

inductive SimdAlignment where
  | unaligned
  | element
  | vector
  deriving DecidableEq, Repr

structure ScalarInt where
  private mk ::
  private rawData : U128
  private byteSize : Size
  deriving DecidableEq, Repr

namespace ScalarInt

private def checkedWidth (size : Size) : Except ScalarIntError Nat := do
  let bits ← size.bits |>.mapError ScalarIntError.sizeError
  if size.bytes == 0 then throw .zeroSize
  if size.bytes > 16 then throw (.sizeTooLarge size)
  return bits.toNat

private def truncated (data : U128) (size : Size) : Except ScalarIntError (ScalarInt × Bool) := do
  let _ ← checkedWidth size
  let bits ← size.truncate data |>.mapError ScalarIntError.sizeError
  return (⟨bits, size⟩, bits != data)

def size (self : ScalarInt) : Size := self.byteSize

def data (self : ScalarInt) : U128 := self.rawData

def null (size : Size) : Except ScalarIntError ScalarInt := do
  let _ ← checkedWidth size
  return ⟨0, size⟩

def isNull (self : ScalarInt) : Bool := self.rawData == 0

def trueValue : ScalarInt := ⟨1, Size.ofBytes 1⟩

def falseValue : ScalarInt := ⟨0, Size.ofBytes 1⟩

/-- Return low bits plus the source truncation flag. `size` remains a checked
source domain: zero and widths above 128 bits cannot become valid scalars. -/
def truncateFromUInt (value : U128) (size : Size) :
    Except ScalarIntError (ScalarInt × Bool) :=
  truncated value size

def tryFromUInt (value : U128) (size : Size) :
    Except ScalarIntError (Option ScalarInt) := do
  let (result, overflow) ← truncated value size
  if overflow then return none
  return some result

/-- Signed input is an arbitrary Lean integer; first enforce Rust's i128
domain, then preserve its two's-complement bits before truncating. -/
def truncateFromInt (value : Int) (size : Size) :
    Except ScalarIntError (ScalarInt × Bool) := do
  if value < -(2 ^ 127 : Int) || value ≥ (2 ^ 127 : Int) then
    throw (.integerOutsideI128 value)
  let (result, _) ← truncated (BitVec.ofInt 128 value) size
  let decoded ← size.signExtend result.rawData |>.mapError ScalarIntError.sizeError
  return (result, decoded != value)

def tryFromInt (value : Int) (size : Size) :
    Except ScalarIntError (Option ScalarInt) := do
  let (result, overflow) ← truncateFromInt value size
  if overflow then return none
  return some result

def ofUInt8 (value : UInt8) : ScalarInt := ⟨BitVec.ofNat 128 value.toNat, Size.ofBytes 1⟩
def ofUInt16 (value : UInt16) : ScalarInt := ⟨BitVec.ofNat 128 value.toNat, Size.ofBytes 2⟩
def ofUInt32 (value : UInt32) : ScalarInt := ⟨BitVec.ofNat 128 value.toNat, Size.ofBytes 4⟩
def ofUInt64 (value : UInt64) : ScalarInt := ⟨BitVec.ofNat 128 value.toNat, Size.ofBytes 8⟩
def ofUInt128 (value : U128) : ScalarInt := ⟨value, Size.ofBytes 16⟩

def ofInt8 (value : Int8) : ScalarInt := ⟨BitVec.ofNat 128 value.toUInt8.toNat, Size.ofBytes 1⟩
def ofInt16 (value : Int16) : ScalarInt := ⟨BitVec.ofNat 128 value.toUInt16.toNat, Size.ofBytes 2⟩
def ofInt32 (value : Int32) : ScalarInt := ⟨BitVec.ofNat 128 value.toUInt32.toNat, Size.ofBytes 4⟩
def ofInt64 (value : Int64) : ScalarInt := ⟨BitVec.ofNat 128 value.toUInt64.toNat, Size.ofBytes 8⟩
def ofInt128 (value : BitVec 128) : ScalarInt := ⟨value, Size.ofBytes 16⟩

def ofBool (value : Bool) : ScalarInt := if value then trueValue else falseValue

def ofChar (value : Char) : ScalarInt := ofUInt32 (UInt32.ofNat value.toNat)

/-- The source's exact-size check is explicit instead of a Lean panic. -/
def toBits (self : ScalarInt) (expectedSize : Size) : Except ScalarIntError U128 := do
  if expectedSize != self.byteSize then
    throw (.sizeMismatch expectedSize self.byteSize)
  return self.rawData

def toBitsUnchecked (self : ScalarInt) : U128 := self.rawData

def toUInt (self : ScalarInt) (expectedSize : Size) : Except ScalarIntError U128 :=
  self.toBits expectedSize

def toInt (self : ScalarInt) (expectedSize : Size) : Except ScalarIntError Int := do
  let bits ← self.toBits expectedSize
  (expectedSize.signExtend bits).mapError ScalarIntError.sizeError

def toUInt8 (self : ScalarInt) : Except ScalarIntError UInt8 := do
  return UInt8.ofNat (← self.toUInt (Size.ofBytes 1)).toNat

def toUInt16 (self : ScalarInt) : Except ScalarIntError UInt16 := do
  return UInt16.ofNat (← self.toUInt (Size.ofBytes 2)).toNat

def toUInt32 (self : ScalarInt) : Except ScalarIntError UInt32 := do
  return UInt32.ofNat (← self.toUInt (Size.ofBytes 4)).toNat

def toUInt64 (self : ScalarInt) : Except ScalarIntError UInt64 := do
  return UInt64.ofNat (← self.toUInt (Size.ofBytes 8)).toNat

def toUInt128 (self : ScalarInt) : Except ScalarIntError U128 :=
  self.toUInt (Size.ofBytes 16)

def toInt8 (self : ScalarInt) : Except ScalarIntError Int8 := do
  return Int8.ofInt (← self.toInt (Size.ofBytes 1))

def toInt16 (self : ScalarInt) : Except ScalarIntError Int16 := do
  return Int16.ofInt (← self.toInt (Size.ofBytes 2))

def toInt32 (self : ScalarInt) : Except ScalarIntError Int32 := do
  return Int32.ofInt (← self.toInt (Size.ofBytes 4))

def toInt64 (self : ScalarInt) : Except ScalarIntError Int64 := do
  return Int64.ofInt (← self.toInt (Size.ofBytes 8))

def toInt128 (self : ScalarInt) : Except ScalarIntError Int :=
  self.toInt (Size.ofBytes 16)

def toTargetUsize (self : ScalarInt) (targetSize : Size) :
    Except ScalarIntError UInt64 := do
  let value ← self.toUInt targetSize
  if value.toNat > 18446744073709551615 then
    throw (.integerConversionOverflow value.toNat)
  return UInt64.ofNat value.toNat

def toTargetIsize (self : ScalarInt) (targetSize : Size) :
    Except ScalarIntError Int64 := do
  let value ← self.toInt targetSize
  if value < -(2 ^ 63 : Int) || value ≥ (2 ^ 63 : Int) then
    throw (.integerConversionOverflow value)
  return Int64.ofInt value

def tryToBool (self : ScalarInt) : Except ScalarIntError Bool := do
  let value ← self.toUInt8
  if value == 0 then return false
  if value == 1 then return true
  throw (.invalidBool value)

private def isUnicodeScalar (value : Nat) : Bool :=
  value ≤ 0x10ffff && !(0xd800 ≤ value && value ≤ 0xdfff)

def toChar (self : ScalarInt) : Except ScalarIntError Char := do
  let value ← self.toUInt32
  if !isUnicodeScalar value.toNat then throw (.invalidChar value)
  return Char.ofNat value.toNat

def toAtomicOrdering (self : ScalarInt) : Except ScalarIntError AtomicOrdering := do
  let value ← self.toUInt32
  match value.toNat with
  | 0 => return .relaxed
  | 1 => return .release
  | 2 => return .acquire
  | 3 => return .acqRel
  | 4 => return .seqCst
  | _ => throw (.invalidAtomicOrdering value)

def toSimdAlignment (self : ScalarInt) : Except ScalarIntError SimdAlignment := do
  let value ← self.toUInt32
  match value.toNat with
  | 0 => return .unaligned
  | 1 => return .element
  | 2 => return .vector
  | _ => throw (.invalidSimdAlignment value)

theorem trueValue_is_one : trueValue.data.toNat = 1 := by rfl

theorem falseValue_is_zero : falseValue.data = 0 := by rfl

end ScalarInt

end Miri.Memory
