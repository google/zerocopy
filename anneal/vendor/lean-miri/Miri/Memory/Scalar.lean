import Miri.Memory.ScalarInt
import Miri.Memory.Pointer
import Miri.Memory.CtfeProvenance

/-!
The integer-or-pointer scalar core from `mir/interpret/value.rs`. Floating
point wrappers are intentionally absent until the pinned apfloat conversion
semantics are available; no host-float approximation is used.
-/

namespace Miri.Memory

open Miri.ABI

inductive ScalarError where
  | scalarInt (reason : ScalarIntError)
  | pointerSizeMismatch (expected actual : Size)
  | pointerOffsetDoesNotFit (offset : Size) (targetSize : Size)
  | integerConversionOverflow (bits : U128)
  | provenanceHasNoAllocationId
  | readPointerAsInt
  | zeroSizedBits
  deriving DecidableEq, Repr

instance : ToString ScalarError where
  toString
    | .scalarInt reason => toString reason
    | .pointerSizeMismatch expected actual =>
        s!"scalar pointer has {actual.bytes} bytes but {expected.bytes} were requested"
    | .pointerOffsetDoesNotFit offset targetSize =>
        s!"pointer offset {offset.bytes} does not fit in {targetSize.bytes} target bytes"
    | .integerConversionOverflow bits => s!"scalar bits {bits.toNat} do not fit in u64"
    | .provenanceHasNoAllocationId => "relative pointer provenance has no allocation ID"
    | .readPointerAsInt => "relative pointer provenance cannot be converted to integer bits"
    | .zeroSizedBits => "bits cannot be read from a zero-sized scalar"

inductive ScalarPayload (Prov : Type) where
  | integer (value : ScalarInt)
  | pointer (value : Pointer Prov)
  deriving DecidableEq, Repr

inductive ScalarBitsOrPointer (Prov : Type) where
  | bits (value : U128)
  | pointer (value : Pointer Prov)
  deriving DecidableEq, Repr

inductive ScalarIntCastResult where
  | integer (value : ScalarInt)
  | erasedPointer (value : Pointer AllocId) (size : Size)
  deriving DecidableEq, Repr

structure Scalar (Prov : Type := CtfeProvenance) where
  private mk ::
  private payload : ScalarPayload Prov
  private scalarSize : Size
  deriving DecidableEq, Repr

namespace Scalar

private def targetPointerSize (layout : TargetDataLayout) : Size :=
  Size.fromBits layout.pointerWidth.bits

private def wrapIntError (reason : ScalarIntError) : ScalarError := .scalarInt reason

def size (self : Scalar Prov) : Size := self.scalarSize

def fromScalarInt (value : ScalarInt) : Scalar Prov :=
  ⟨.integer value, value.size⟩

def fromPointer (layout : TargetDataLayout) (value : Pointer Prov) : Scalar Prov :=
  ⟨.pointer value, targetPointerSize layout⟩

def fromMaybePointer (layout : TargetDataLayout) (value : Pointer (Option Prov)) :
    Except ScalarError (Scalar Prov) := do
  match value.provenance with
  | some provenance => return fromPointer layout ⟨value.offset, provenance⟩
  | none =>
    let scalar ← ScalarInt.tryFromUInt (BitVec.ofNat 128 value.offset.bytes.toNat)
      (targetPointerSize layout) |>.mapError wrapIntError
    match scalar with
    | some scalar => return fromScalarInt scalar
    | none => throw (.pointerOffsetDoesNotFit value.offset (targetPointerSize layout))

def nullPointer (layout : TargetDataLayout) : Except ScalarError (Scalar Prov) := do
  return fromScalarInt (← ScalarInt.null (targetPointerSize layout) |>.mapError wrapIntError)

def fromBool (value : Bool) : Scalar Prov := fromScalarInt (ScalarInt.ofBool value)

def fromChar (value : Char) : Scalar Prov := fromScalarInt (ScalarInt.ofChar value)

def fromUInt (value : U128) (size : Size) : Except ScalarError (Scalar Prov) := do
  let scalar ← ScalarInt.tryFromUInt value size |>.mapError wrapIntError
  match scalar with
  | some scalar => return fromScalarInt scalar
  | none => throw (.scalarInt (.integerConversionOverflow value.toNat))

def fromInt (value : Int) (size : Size) : Except ScalarError (Scalar Prov) := do
  let scalar ← ScalarInt.tryFromInt value size |>.mapError wrapIntError
  match scalar with
  | some scalar => return fromScalarInt scalar
  | none => throw (.scalarInt (.integerConversionOverflow value))

def isPointer (self : Scalar Prov) : Bool :=
  match self.payload with
  | .integer _ => false
  | .pointer _ => true

def toBitsOrPtrInternal (self : Scalar Prov) (expectedSize : Size) :
    Except ScalarError (ScalarBitsOrPointer Prov) := do
  match self.payload with
  | .integer scalar =>
    return .bits (← scalar.toBits expectedSize |>.mapError wrapIntError)
  | .pointer pointer =>
    if self.scalarSize != expectedSize then
      throw (.pointerSizeMismatch expectedSize self.scalarSize)
    return .pointer pointer

def tryToScalarInt [PointerProvenance Prov] (self : Scalar Prov) :
    Except ScalarError ScalarIntCastResult := do
  match self.payload with
  | .integer scalar => return .integer scalar
  | .pointer pointer =>
    if PointerProvenance.offsetIsAddr (Prov := Prov) then
      let scalar ← ScalarInt.tryFromUInt (BitVec.ofNat 128 pointer.offset.bytes.toNat)
        self.scalarSize |>.mapError wrapIntError
      match scalar with
      | some scalar => return .integer scalar
      | none => throw (.pointerOffsetDoesNotFit pointer.offset self.scalarSize)
    else
      match PointerProvenance.getAllocId (Prov := Prov) pointer.provenance with
      | some id => return .erasedPointer ⟨pointer.offset, id⟩ self.scalarSize
      | none => throw .provenanceHasNoAllocationId

def clearProvenance [PointerProvenance Prov] (self : Scalar Prov) :
    Except ScalarError (Scalar Prov) := do
  match ← self.tryToScalarInt with
  | .integer value => return fromScalarInt value
  | .erasedPointer _ _ => throw .readPointerAsInt

def toScalarInt [PointerProvenance Prov] (self : Scalar Prov) :
    Except ScalarError ScalarInt := do
  match ← self.tryToScalarInt with
  | .integer value => return value
  | .erasedPointer _ _ => throw .readPointerAsInt

def assertScalarInt [PointerProvenance Prov] (self : Scalar Prov) :
    Except ScalarError ScalarInt := self.toScalarInt

def toBits [PointerProvenance Prov] (self : Scalar Prov) (targetSize : Size) :
    Except ScalarError U128 := do
  if targetSize.bytes == 0 then throw .zeroSizedBits
  let scalar ← self.toScalarInt
  scalar.toBits targetSize |>.mapError wrapIntError

def toUInt [PointerProvenance Prov] (self : Scalar Prov) (size : Size) :
    Except ScalarError U128 := self.toBits size

def toUInt8 [PointerProvenance Prov] (self : Scalar Prov) :
    Except ScalarError UInt8 := do
  return UInt8.ofNat (← self.toUInt (Size.ofBytes 1)).toNat

def toUInt16 [PointerProvenance Prov] (self : Scalar Prov) :
    Except ScalarError UInt16 := do
  return UInt16.ofNat (← self.toUInt (Size.ofBytes 2)).toNat

def toUInt32 [PointerProvenance Prov] (self : Scalar Prov) :
    Except ScalarError UInt32 := do
  return UInt32.ofNat (← self.toUInt (Size.ofBytes 4)).toNat

def toUInt64 [PointerProvenance Prov] (self : Scalar Prov) :
    Except ScalarError UInt64 := do
  return UInt64.ofNat (← self.toUInt (Size.ofBytes 8)).toNat

def toUInt128 [PointerProvenance Prov] (self : Scalar Prov) :
    Except ScalarError U128 := self.toUInt (Size.ofBytes 16)

def toInt [PointerProvenance Prov] (self : Scalar Prov) (size : Size) :
    Except ScalarError Int := do
  let bits ← self.toBits size
  (size.signExtend bits).mapError (ScalarError.scalarInt ∘ ScalarIntError.sizeError)

def toInt8 [PointerProvenance Prov] (self : Scalar Prov) :
    Except ScalarError Int8 := do
  return Int8.ofInt (← self.toInt (Size.ofBytes 1))

def toInt16 [PointerProvenance Prov] (self : Scalar Prov) :
    Except ScalarError Int16 := do
  return Int16.ofInt (← self.toInt (Size.ofBytes 2))

def toInt32 [PointerProvenance Prov] (self : Scalar Prov) :
    Except ScalarError Int32 := do
  return Int32.ofInt (← self.toInt (Size.ofBytes 4))

def toInt64 [PointerProvenance Prov] (self : Scalar Prov) :
    Except ScalarError Int64 := do
  return Int64.ofInt (← self.toInt (Size.ofBytes 8))

def toInt128 [PointerProvenance Prov] (self : Scalar Prov) :
    Except ScalarError Int := self.toInt (Size.ofBytes 16)

def toTargetUsize [PointerProvenance Prov] (self : Scalar Prov) (targetSize : Size) :
    Except ScalarError UInt64 := do
  let bits ← self.toUInt targetSize
  if bits.toNat > 18446744073709551615 then
    throw (.integerConversionOverflow bits)
  return UInt64.ofNat bits.toNat

def toTargetIsize [PointerProvenance Prov] (self : Scalar Prov) (targetSize : Size) :
    Except ScalarError Int64 := do
  let value ← self.toInt targetSize
  if value < -(2 ^ 63 : Int) || value ≥ (2 ^ 63 : Int) then
    throw (.scalarInt (.integerConversionOverflow value))
  return Int64.ofInt value

def toBool [PointerProvenance Prov] (self : Scalar Prov) : Except ScalarError Bool := do
  let value ← self.toUInt8
  if value == 0 then return false
  if value == 1 then return true
  throw (.scalarInt (.invalidBool value))

def toChar [PointerProvenance Prov] (self : Scalar Prov) : Except ScalarError Char := do
  let scalarInt ← self.toScalarInt
  scalarInt.toChar |>.mapError wrapIntError

def toPointer [PointerProvenance Prov] (self : Scalar Prov) (layout : TargetDataLayout) :
    Except ScalarError (Pointer (Option Prov)) := do
  match ← self.toBitsOrPtrInternal (targetPointerSize layout) with
  | .pointer pointer => return pointer.withOptionalProvenance
  | .bits bits =>
    if bits.toNat > 18446744073709551615 then throw (.integerConversionOverflow bits)
    return Pointer.withoutProvenance (UInt64.ofNat bits.toNat)

theorem fromScalarInt_size (value : ScalarInt) :
    (fromScalarInt (Prov := Prov) value).size = value.size := rfl

theorem fromPointer_size (layout : TargetDataLayout) (pointer : Pointer Prov) :
    (fromPointer layout pointer).size = targetPointerSize layout := rfl

end Scalar

end Miri.Memory
