import Miri.ABI.Align
import Miri.ABI.WrappingRange

/-!
Source-shaped scalar and backend runtime-layout representations from pinned
rustc_abi. RuntimeTargetDataLayout is a complete extension of the existing
arithmetic TargetDataLayout: it stores that view once and requires the source
alignment and pointer-space details used by these APIs. Unknown address spaces
and malformed Lean alignments are explicit errors.
-/

namespace Miri.ABI

structure AddressSpace where
  value : UInt32
  deriving DecidableEq, Repr, Inhabited

namespace AddressSpace

def ZERO : AddressSpace := ⟨0⟩
def GPU_CONSTANT : AddressSpace := ⟨4⟩
def GPU_WORKGROUP : AddressSpace := ⟨3⟩

end AddressSpace

inductive Integer where
  | I8
  | I16
  | I32
  | I64
  | I128
  deriving DecidableEq, Repr, Inhabited

inductive Float where
  | F16
  | F16B
  | F32
  | F64
  | F128
  | PpcF128
  deriving DecidableEq, Repr, Inhabited

/-- Pointer representation for one data address space, matching the source.
pointerOffset can differ from the stored pointer size. -/
structure PointerSpec where
  pointerSize : Size
  pointerAlign : Align
  pointerOffset : Size
  isFat : Bool := false
  deriving DecidableEq, Repr

/-- Data needed by scalar runtime-layout methods in rustc_abi. base retains
the existing target endian and object-size bound. Every alignment is supplied
by the caller, and address spaces are explicit. -/
structure RuntimeTargetDataLayout where
  base : TargetDataLayout
  i1Align : Align
  i8Align : Align
  i16Align : Align
  i32Align : Align
  i64Align : Align
  i128Align : Align
  f16Align : Align
  f32Align : Align
  f64Align : Align
  f128Align : Align
  aggregateAlign : Align
  vectorAlign : Array (Size × Align)
  defaultAddressSpace : AddressSpace
  defaultAddressSpacePointerSpec : PointerSpec
  addressSpaceInfo : Array (AddressSpace × PointerSpec)
  instructionAddressSpace : AddressSpace
  cEnumMinSize : Integer
  deriving DecidableEq, Repr

inductive RuntimeLayoutError where
  | invalidAlignment (where_ : String) (error : AlignError)
  | unknownAddressSpace (addressSpace : AddressSpace)
  | sizeFailure (error : SizeError)
  | unsupportedPointerOffsetWidth (size : Size)
  | unsupportedObjectSizePointerWidth (size : Size)
  | targetPointerWidthMismatch (configured : PointerWidth) (size : Size)
  | duplicateAddressSpace (addressSpace : AddressSpace)
  | missingInstructionAddressSpace (addressSpace : AddressSpace)
  | duplicateVectorSize (size : Size)
  | vectorAlignmentOverflow (size : Size)
  deriving DecidableEq, Repr

instance : ToString RuntimeLayoutError where
  toString
    | .invalidAlignment where_ error =>
        s!"invalid {where_} alignment: {error}"
    | .unknownAddressSpace addressSpace =>
        s!"unknown address space {addressSpace.value}"
    | .sizeFailure error => toString error
    | .unsupportedPointerOffsetWidth size =>
        s!"unsupported pointer offset width {size.bytes} bytes"
    | .unsupportedObjectSizePointerWidth size =>
        s!"unsupported object-size pointer width {size.bytes} bytes"
    | .targetPointerWidthMismatch configured size =>
        s!"base target width {configured.bits} disagrees with default pointer size {size.bytes} bytes"
    | .duplicateAddressSpace addressSpace =>
        s!"duplicate or default address space entry {addressSpace.value}"
    | .missingInstructionAddressSpace addressSpace =>
        s!"instruction address space {addressSpace.value} has no pointer specification"
    | .duplicateVectorSize size =>
        s!"duplicate vector alignment entry for {size.bytes} bytes"
    | .vectorAlignmentOverflow size =>
        s!"next power-of-two vector alignment overflows for {size.bytes} bytes"

/-- The actual rustc_abi default layout, represented with the existing 64-bit
arithmetic view. This is an explicit fixture, not a fallback for missing target
alignment or address-space data. -/
def RuntimeTargetDataLayout.default : RuntimeTargetDataLayout := {
  base := ⟨.big, .w64⟩
  i1Align := Align.ONE
  i8Align := Align.ONE
  i16Align := ⟨1⟩
  i32Align := ⟨2⟩
  i64Align := ⟨2⟩
  i128Align := ⟨2⟩
  f16Align := ⟨1⟩
  f32Align := ⟨2⟩
  f64Align := Align.EIGHT
  f128Align := ⟨4⟩
  aggregateAlign := Align.ONE
  vectorAlign := #[(Size.ofBytes 8, Align.EIGHT), (Size.ofBytes 16, ⟨4⟩)]
  defaultAddressSpace := AddressSpace.ZERO
  defaultAddressSpacePointerSpec := ⟨Size.ofBytes 8, Align.EIGHT, Size.ofBytes 8, false⟩
  addressSpaceInfo := #[]
  instructionAddressSpace := AddressSpace.ZERO
  cEnumMinSize := .I32
}

namespace RuntimeTargetDataLayout

def validateAlign (where_ : String) (align : Align) :
    Except RuntimeLayoutError Unit := do
  if align.pow2 > Align.MAX.pow2 then
    if align.pow2 >= 64 then
      throw (.invalidAlignment where_ (.shiftOverflow align.pow2))
    else
      throw (.invalidAlignment where_
        (.tooLarge (UInt64.shiftLeft 1 (UInt64.ofNat align.pow2))))
  match Align.bytes align with
  | .ok _ => pure ()
  | .error error => throw (.invalidAlignment where_ error)

def validate (layout : RuntimeTargetDataLayout) : Except RuntimeLayoutError Unit := do
  let pointerBits ← (Size.bits layout.defaultAddressSpacePointerSpec.pointerSize)
    |>.mapError RuntimeLayoutError.sizeFailure
  let expectedWidth ← match pointerBits with
    | 16 => pure .w16
    | 32 => pure .w32
    | 64 => pure .w64
    | _ => throw (.unsupportedObjectSizePointerWidth
      layout.defaultAddressSpacePointerSpec.pointerSize)
  if layout.base.pointerWidth != expectedWidth then
    throw (.targetPointerWidthMismatch layout.base.pointerWidth
      layout.defaultAddressSpacePointerSpec.pointerSize)
  validateAlign "i1" layout.i1Align
  validateAlign "i8" layout.i8Align
  validateAlign "i16" layout.i16Align
  validateAlign "i32" layout.i32Align
  validateAlign "i64" layout.i64Align
  validateAlign "i128" layout.i128Align
  validateAlign "f16" layout.f16Align
  validateAlign "f32" layout.f32Align
  validateAlign "f64" layout.f64Align
  validateAlign "f128" layout.f128Align
  validateAlign "aggregate" layout.aggregateAlign
  validateAlign "default pointer" layout.defaultAddressSpacePointerSpec.pointerAlign
  let mut vectorSizes : Array Size := #[]
  for entry in layout.vectorAlign do
    validateAlign "vector" entry.2
    if vectorSizes.contains entry.1 then
      throw (.duplicateVectorSize entry.1)
    vectorSizes := vectorSizes.push entry.1
  for entry in layout.addressSpaceInfo do
    validateAlign s!"pointer address space {entry.1.value}" entry.2.pointerAlign
  let mut seen : Array AddressSpace := #[]
  for entry in layout.addressSpaceInfo do
    if entry.1 == layout.defaultAddressSpace || seen.contains entry.1 then
      throw (.duplicateAddressSpace entry.1)
    seen := seen.push entry.1
  if layout.instructionAddressSpace != layout.defaultAddressSpace &&
      !seen.contains layout.instructionAddressSpace then
    throw (.missingInstructionAddressSpace layout.instructionAddressSpace)

def cVectorAlign (layout : RuntimeTargetDataLayout) (vecSize : Size) : Option Align :=
  (layout.vectorAlign.find? fun entry => entry.1 == vecSize).map Prod.snd

/-- Rust's source fallback is `bytes.next_power_of_two()` followed by an
alignment unwrap. The Lean result makes both source panic points explicit. -/
def rustVectorAlign (layout : RuntimeTargetDataLayout) (vecSize : Size) :
    Except RuntimeLayoutError Align := do
  match layout.cVectorAlign vecSize with
  | some align =>
      validateAlign "vector" align
      return align
  | none =>
      let bytes := vecSize.bytes
      let nextPower ← if bytes == 0 then
        pure 1
      else if bytes > UInt64.shiftLeft 1 63 then
        throw (.vectorAlignmentOverflow vecSize)
      else if bytes == UInt64.shiftLeft 1 63 then
        pure bytes
      else
        let raw := bytes.toNat
        let lowerPower := 2 ^ Nat.log2 raw
        let next := if lowerPower == raw then lowerPower else 2 * lowerPower
        pure (UInt64.ofNat next)
      match Align.fromBytes nextPower with
      | .ok align => return align
      | .error error => throw (.invalidAlignment "vector" error)

def pointerSpecIn (layout : RuntimeTargetDataLayout) (space : AddressSpace) :
    Except RuntimeLayoutError PointerSpec := do
  if space == layout.defaultAddressSpace then
    return layout.defaultAddressSpacePointerSpec
  match layout.addressSpaceInfo.find? fun entry => entry.1 == space with
  | some entry => return entry.2
  | none => throw (.unknownAddressSpace space)

def pointerSizeIn (layout : RuntimeTargetDataLayout) (space : AddressSpace) :
    Except RuntimeLayoutError Size := do
  return (← layout.pointerSpecIn space).pointerSize

def pointerSize (layout : RuntimeTargetDataLayout) : Size :=
  layout.defaultAddressSpacePointerSpec.pointerSize

def pointerOffsetIn (layout : RuntimeTargetDataLayout) (space : AddressSpace) :
    Except RuntimeLayoutError Size := do
  return (← layout.pointerSpecIn space).pointerOffset

def pointerOffset (layout : RuntimeTargetDataLayout) : Size :=
  layout.defaultAddressSpacePointerSpec.pointerOffset

def pointerAlignIn (layout : RuntimeTargetDataLayout) (space : AddressSpace) :
    Except RuntimeLayoutError AbiAlign := do
  let spec ← layout.pointerSpecIn space
  validateAlign "pointer" spec.pointerAlign
  return .new spec.pointerAlign

def pointerAlign (layout : RuntimeTargetDataLayout) : Except RuntimeLayoutError AbiAlign := do
  let align := layout.defaultAddressSpacePointerSpec.pointerAlign
  validateAlign "default pointer" align
  return .new align

def objSizeBound (layout : RuntimeTargetDataLayout) : UInt64 :=
  layout.base.objSizeBound

def ptrSizedIntegerIn (layout : RuntimeTargetDataLayout) (space : AddressSpace) :
    Except RuntimeLayoutError Integer := do
  let offset ← layout.pointerOffsetIn space
  let bits ← (Size.bits offset).mapError RuntimeLayoutError.sizeFailure
  match bits with
  | 16 => return .I16
  | 32 => return .I32
  | 64 => return .I64
  | _ => throw (.unsupportedPointerOffsetWidth offset)

def ptrSizedInteger (layout : RuntimeTargetDataLayout) :
    Except RuntimeLayoutError Integer :=
  layout.ptrSizedIntegerIn layout.defaultAddressSpace

end RuntimeTargetDataLayout

/-! Full runtime-layout contexts extend, rather than replace, the target view
already used by Size's target-dependent arithmetic. -/
class HasRuntimeDataLayout (α : Type) extends HasDataLayout α where
  runtimeDataLayout : α → RuntimeTargetDataLayout

instance : HasRuntimeDataLayout RuntimeTargetDataLayout where
  dataLayout := RuntimeTargetDataLayout.base
  runtimeDataLayout := id

inductive IntegerType where
  | Pointer (signed : Bool)
  | Fixed (integer : Integer) (signed : Bool)
  deriving DecidableEq, Repr

namespace IntegerType

def isSigned : IntegerType → Bool
  | .Pointer signed | .Fixed _ signed => signed

end IntegerType

inductive IntegerError where
  | layout (error : RuntimeLayoutError)
  | size (error : SizeError)
  | unsupportedBitWidth (bits : UInt64)
  deriving DecidableEq, Repr

instance : ToString IntegerError where
  toString
    | .layout error => toString error
    | .size error => toString error
    | .unsupportedBitWidth bits => s!"rust does not support integers with {bits} bits"

namespace Integer

def intTyStr : Integer → String
  | .I8 => "i8"
  | .I16 => "i16"
  | .I32 => "i32"
  | .I64 => "i64"
  | .I128 => "i128"

def uintTyStr : Integer → String
  | .I8 => "u8"
  | .I16 => "u16"
  | .I32 => "u32"
  | .I64 => "u64"
  | .I128 => "u128"

def size : Integer → Size
  | .I8 => Size.ofBytes 1
  | .I16 => Size.ofBytes 2
  | .I32 => Size.ofBytes 4
  | .I64 => Size.ofBytes 8
  | .I128 => Size.ofBytes 16

def align {α : Type} [HasRuntimeDataLayout α] (integer : Integer) (cx : α) :
    Except RuntimeLayoutError AbiAlign := do
  let layout := HasRuntimeDataLayout.runtimeDataLayout cx
  let align := match integer with
    | .I8 => layout.i8Align
    | .I16 => layout.i16Align
    | .I32 => layout.i32Align
    | .I64 => layout.i64Align
    | .I128 => layout.i128Align
  RuntimeTargetDataLayout.validateAlign s!"{integer.intTyStr}" align
  return .new align

def fromAttr {α : Type} [HasRuntimeDataLayout α] (cx : α) (ity : IntegerType) :
    Except IntegerError Integer :=
  match ity with
  | .Pointer _ =>
      (HasRuntimeDataLayout.runtimeDataLayout cx).ptrSizedInteger
        |>.mapError IntegerError.layout
  | .Fixed integer _ => .ok integer

def signedMax : Integer → Int
  | .I8 => 127
  | .I16 => 32767
  | .I32 => 2147483647
  | .I64 => 9223372036854775807
  | .I128 => 170141183460469231731687303715884105727

def signedMin : Integer → Int
  | .I8 => -128
  | .I16 => -32768
  | .I32 => -2147483648
  | .I64 => -9223372036854775808
  | .I128 => -170141183460469231731687303715884105728

def fitSigned (value : Int) : Integer :=
  if value >= signedMin .I8 && value <= signedMax .I8 then .I8
  else if value >= signedMin .I16 && value <= signedMax .I16 then .I16
  else if value >= signedMin .I32 && value <= signedMax .I32 then .I32
  else if value >= signedMin .I64 && value <= signedMax .I64 then .I64
  else .I128

def fitUnsigned (value : U128) : Integer :=
  if value.toNat <= 255 then .I8
  else if value.toNat <= 65535 then .I16
  else if value.toNat <= 4294967295 then .I32
  else if value.toNat <= 18446744073709551615 then .I64
  else .I128

def forAlign {α : Type} [HasRuntimeDataLayout α] (cx : α) (wanted : Align) :
    Except RuntimeLayoutError (Option Integer) := do
  let wantedBytes ← (Align.bytes wanted).mapError
    (RuntimeLayoutError.invalidAlignment "requested integer")
  let candidates : Array Integer := #[.I8, .I16, .I32, .I64, .I128]
  for candidate in candidates do
    let candidateAlign ← candidate.align cx
    if candidateAlign.abi == wanted && wantedBytes == candidate.size.bytes then
      return some candidate
  return none

def approximateAlign {α : Type} [HasRuntimeDataLayout α] (cx : α) (wanted : Align) :
    Except RuntimeLayoutError Integer := do
  let wantedBytes ← (Align.bytes wanted).mapError
    (RuntimeLayoutError.invalidAlignment "requested integer")
  let candidates : Array Integer := #[.I64, .I32, .I16]
  for candidate in candidates do
    let candidateAlign ← candidate.align cx
    if wanted.pow2 >= candidateAlign.abi.pow2 &&
        wantedBytes >= candidate.size.bytes then
      return candidate
  return .I8

def fromSize (size : Size) : Except IntegerError Integer := do
  let bits ← (Size.bits size).mapError IntegerError.size
  match bits with
  | 8 => return .I8
  | 16 => return .I16
  | 32 => return .I32
  | 64 => return .I64
  | 128 => return .I128
  | _ => throw (.unsupportedBitWidth bits)

end Integer

namespace Float

def size : Float → Size
  | .F16 | .F16B => Size.ofBytes 2
  | .F32 => Size.ofBytes 4
  | .F64 => Size.ofBytes 8
  | .F128 | .PpcF128 => Size.ofBytes 16

def align {α : Type} [HasRuntimeDataLayout α] (float : Float) (cx : α) :
    Except RuntimeLayoutError AbiAlign := do
  let layout := HasRuntimeDataLayout.runtimeDataLayout cx
  let align := match float with
    | .F16 | .F16B => layout.f16Align
    | .F32 => layout.f32Align
    | .F64 => layout.f64Align
    | .F128 | .PpcF128 => layout.f128Align
  let label := match float with
    | .F16 => "f16"
    | .F16B => "f16b"
    | .F32 => "f32"
    | .F64 => "f64"
    | .F128 => "f128"
    | .PpcF128 => "ppcf128"
  RuntimeTargetDataLayout.validateAlign label align
  return .new align

def tyStr : Float → String
  | .F16 => "f16"
  | .F16B => "f16b"
  | .F32 => "f32"
  | .F64 => "f64"
  | .F128 => "f128"
  | .PpcF128 => "ppcf128"

end Float

inductive Primitive where
  | Int (integer : Integer) (signed : Bool)
  | Float (float : Float)
  | Pointer (addressSpace : AddressSpace)
  deriving DecidableEq, Repr

inductive RegKind where
  | Integer
  | Float
  | PpcF128
  | Vector { hintVectorElem : Primitive }
  deriving DecidableEq, Repr

namespace RegKind

def fromPrimitive : Primitive → RegKind
  | .Int .. | .Pointer _ => .Integer
  | .Float .PpcF128 => .PpcF128
  | .Float _ => .Float

end RegKind

inductive Numeric where
  | Int (integer : Integer) (signed : Bool)
  | Float (float : Float)
  deriving DecidableEq, Repr

namespace Numeric

def size : Numeric → Size
  | .Int integer _ => integer.size
  | .Float float => float.size

def regKind : Numeric → RegKind
  | .Int _ _ => .Integer
  | .Float .PpcF128 => .PpcF128
  | .Float _ => .Float

end Numeric

structure Reg where
  kind : RegKind
  size : Size
  deriving DecidableEq, Repr

inductive RegLayoutError where
  | size (error : SizeError)
  | runtime (error : RuntimeLayoutError)
  | unsupportedIntegerWidth (bits : UInt64)
  | unsupportedFloatWidth (bits : UInt64)
  deriving DecidableEq, Repr

namespace Reg

private def numeric (kind : RegKind) (bits : UInt64) : Reg :=
  ⟨kind, Size.fromBits bits⟩

def i8 : Reg := numeric .Integer 8
def i16 : Reg := numeric .Integer 16
def i32 : Reg := numeric .Integer 32
def i64 : Reg := numeric .Integer 64
def i128 : Reg := numeric .Integer 128
def f16 : Reg := numeric .Float 16
def f32 : Reg := numeric .Float 32
def f64 : Reg := numeric .Float 64
def f128 : Reg := numeric .Float 128
def opaqueVector (size : Size) : Reg :=
  ⟨.Vector (hintVectorElem := .Int .I8 true), size⟩

def align {α : Type} [HasRuntimeDataLayout α] (reg : Reg) (cx : α) :
    Except RegLayoutError Align := do
  let layout := HasRuntimeDataLayout.runtimeDataLayout cx
  match reg.kind with
  | .Integer =>
      let bits ← (Size.bits reg.size).mapError RegLayoutError.size
      if bits == 1 then
        let _ ← (RuntimeTargetDataLayout.validateAlign "integer register" layout.i1Align).mapError
          RegLayoutError.runtime
        return layout.i1Align
      else if 2 ≤ bits && bits ≤ 8 then
        let _ ← (RuntimeTargetDataLayout.validateAlign "integer register" layout.i8Align).mapError
          RegLayoutError.runtime
        return layout.i8Align
      else if 9 ≤ bits && bits ≤ 16 then
        let _ ← (RuntimeTargetDataLayout.validateAlign "integer register" layout.i16Align).mapError
          RegLayoutError.runtime
        return layout.i16Align
      else if 17 ≤ bits && bits ≤ 32 then
        let _ ← (RuntimeTargetDataLayout.validateAlign "integer register" layout.i32Align).mapError
          RegLayoutError.runtime
        return layout.i32Align
      else if 33 ≤ bits && bits ≤ 64 then
        let _ ← (RuntimeTargetDataLayout.validateAlign "integer register" layout.i64Align).mapError
          RegLayoutError.runtime
        return layout.i64Align
      else if 65 ≤ bits && bits ≤ 128 then
        let _ ← (RuntimeTargetDataLayout.validateAlign "integer register" layout.i128Align).mapError
          RegLayoutError.runtime
        return layout.i128Align
      else
        throw (.unsupportedIntegerWidth bits)
  | .Float =>
      let bits ← (Size.bits reg.size).mapError RegLayoutError.size
      if bits == 16 then
        let _ ← (RuntimeTargetDataLayout.validateAlign "float register" layout.f16Align).mapError
          RegLayoutError.runtime
        return layout.f16Align
      else if bits == 32 then
        let _ ← (RuntimeTargetDataLayout.validateAlign "float register" layout.f32Align).mapError
          RegLayoutError.runtime
        return layout.f32Align
      else if bits == 64 then
        let _ ← (RuntimeTargetDataLayout.validateAlign "float register" layout.f64Align).mapError
          RegLayoutError.runtime
        return layout.f64Align
      else if bits == 128 then
        let _ ← (RuntimeTargetDataLayout.validateAlign "float register" layout.f128Align).mapError
          RegLayoutError.runtime
        return layout.f128Align
      else
        throw (.unsupportedFloatWidth bits)
  | .PpcF128 =>
      let _ ← (RuntimeTargetDataLayout.validateAlign "ppcf128 register" layout.f128Align).mapError
        RegLayoutError.runtime
      return layout.f128Align
  | .Vector =>
      (RuntimeTargetDataLayout.rustVectorAlign layout reg.size).mapError
        RegLayoutError.runtime

end Reg

namespace Primitive

def size {α : Type} [HasRuntimeDataLayout α] (primitive : Primitive) (cx : α) :
    Except RuntimeLayoutError Size := do
  match primitive with
  | .Int integer _ => return integer.size
  | .Float float => return float.size
  | .Pointer addressSpace =>
      (HasRuntimeDataLayout.runtimeDataLayout cx).pointerSizeIn addressSpace

def defaultAlign {α : Type} [HasRuntimeDataLayout α] (primitive : Primitive) (cx : α) :
    Except RuntimeLayoutError AbiAlign := do
  match primitive with
  | .Int integer _ => integer.align cx
  | .Float float => float.align cx
  | .Pointer addressSpace =>
      (HasRuntimeDataLayout.runtimeDataLayout cx).pointerAlignIn addressSpace

def regKind : Primitive → RegKind
  := RegKind.fromPrimitive

end Primitive

inductive Scalar where
  | Initialized { value : Primitive } { validRange : WrappingRange }
  | Union { value : Primitive }
  deriving DecidableEq, Repr

inductive ScalarLayoutError where
  | runtimeLayout (error : RuntimeLayoutError)
  | wrappingRange (error : WrappingRangeError)
  | cannotChangeUnionValidRange
  deriving DecidableEq, Repr

namespace Scalar

def isBool : Scalar → Bool
  | .Initialized (value := .Int .I8 false) (validRange := range) =>
      range.start == 0 && range.«end» == 1
  | _ => false

def primitive : Scalar → Primitive
  | .Initialized (value := value) | .Union (value := value) => value

def defaultAlign {α : Type} [HasRuntimeDataLayout α] (scalar : Scalar) (cx : α) :
    Except ScalarLayoutError AbiAlign :=
  (scalar.primitive.defaultAlign cx).mapError ScalarLayoutError.runtimeLayout

def size {α : Type} [HasRuntimeDataLayout α] (scalar : Scalar) (cx : α) :
    Except ScalarLayoutError Size :=
  (scalar.primitive.size cx).mapError ScalarLayoutError.runtimeLayout

def toUnion : Scalar → Scalar
  | .Initialized (value := value) | .Union (value := value) => .Union (value := value)

def validRange {α : Type} [HasRuntimeDataLayout α] (scalar : Scalar) (cx : α) :
    Except ScalarLayoutError WrappingRange := do
  match scalar with
  | .Initialized (validRange := range) => return range
  | .Union (value := value) =>
      let size ← (value.size cx).mapError ScalarLayoutError.runtimeLayout
      (WrappingRange.full size).mapError ScalarLayoutError.wrappingRange

def setValidRange (scalar : Scalar) (range : WrappingRange) :
    Except ScalarLayoutError Scalar :=
  match scalar with
  | .Initialized (value := value) => .ok (.Initialized (value := value) (validRange := range))
  | .Union => .error .cannotChangeUnionValidRange

def isAlwaysValid {α : Type} [HasRuntimeDataLayout α] (scalar : Scalar) (cx : α) :
    Except ScalarLayoutError Bool := do
  match scalar with
  | .Initialized (validRange := range) =>
      let size ← scalar.size cx
      (range.isFullFor size).mapError ScalarLayoutError.wrappingRange
  | .Union => return true

def isUninitValid : Scalar → Bool
  | .Initialized => false
  | .Union => true

def isSigned : Scalar → Bool
  | .Initialized (value := .Int _ signed) | .Union (value := .Int _ signed) => signed
  | _ => false

end Scalar

structure BackendLaneCount where
  private value : UInt16
  deriving DecidableEq, Repr

def MAX_SIMD_LANES : UInt16 := 32768

inductive BackendLaneCountError where
  | zeroLength
  | oversized (maxLanes : UInt16)
  deriving DecidableEq, Repr

namespace BackendLaneCount

def new (count : UInt64) : Except BackendLaneCountError BackendLaneCount :=
  if count > MAX_SIMD_LANES.toUInt64 then
    .error (.oversized MAX_SIMD_LANES)
  else if count == 0 then
    .error .zeroLength
  else
    .ok ⟨count.toUInt16⟩

def isPowerOfTwo (count : BackendLaneCount) : Bool :=
  count.value.toNat &&& (count.value.toNat - 1) == 0

def asU64 (count : BackendLaneCount) : UInt64 := count.value.toUInt64
def asU32 (count : BackendLaneCount) : UInt32 := count.value.toUInt32

end BackendLaneCount

structure NumScalableVectors where
  value : UInt8
  deriving DecidableEq, Repr

namespace NumScalableVectors

def forNonTuple : NumScalableVectors := ⟨1⟩

def fromFieldCount (count : Nat) : Option NumScalableVectors :=
  if 2 ≤ count && count < 8 then some ⟨UInt8.ofNat count⟩ else none

end NumScalableVectors

inductive BackendRepr where
  | Scalar (scalar : Scalar)
  | ScalarPair { a b : Scalar } { bOffset : Size }
  | SimdScalableVector { element : Scalar } { count : BackendLaneCount }
      { numberOfVectors : NumScalableVectors }
  | SimdVector { element : Scalar } { count : BackendLaneCount }
  | Memory { sized : Bool }
  deriving DecidableEq, Repr

inductive BackendReprError where
  | scalar (error : ScalarLayoutError)
  | size (error : SizeError)
  | alignment (error : AlignError)
  | alignmentUnavailableForPair
  | isSignedOnNonScalar
  deriving DecidableEq, Repr

namespace BackendRepr

def isUnsized : BackendRepr → Bool
  | .Memory (sized := sized) => !sized
  | .Scalar _ | .ScalarPair | .SimdScalableVector | .SimdVector => false

def isSized (repr : BackendRepr) : Bool := !repr.isUnsized

def isSigned : BackendRepr → Except BackendReprError Bool
  | .Scalar scalar => .ok scalar.isSigned
  | _ => .error .isSignedOnNonScalar

def isScalar : BackendRepr → Bool
  | .Scalar _ => true
  | _ => false

def isScalarOrSimd : BackendRepr → Bool
  | .Scalar _ | .SimdVector | .SimdScalableVector => true
  | _ => false

def isBool : BackendRepr → Bool
  | .Scalar scalar => scalar.isBool
  | _ => false

def scalarPlatformAlign {α : Type} [HasRuntimeDataLayout α] (repr : BackendRepr)
    (cx : α) : Except BackendReprError (Option Align) := do
  match repr with
  | .Scalar scalar =>
      let align ← (scalar.defaultAlign cx).mapError BackendReprError.scalar
      return some align.abi
  | .ScalarPair (a := a) (b := b) =>
      let aAlign ← (a.defaultAlign cx).mapError BackendReprError.scalar
      let bAlign ← (b.defaultAlign cx).mapError BackendReprError.scalar
      return some (Align.max aAlign.abi bAlign.abi)
  | .SimdVector | .Memory | .SimdScalableVector => return none

def scalarSize {α : Type} [HasRuntimeDataLayout α] (repr : BackendRepr) (cx : α) :
    Except BackendReprError (Option Size) := do
  match repr with
  | .Scalar scalar =>
      return some (← (scalar.size cx).mapError BackendReprError.scalar)
  | .ScalarPair (b := b) (bOffset := bOffset) =>
      let bSize ← (b.size cx).mapError BackendReprError.scalar
      let endOffset ← (Size.add bOffset bSize).mapError BackendReprError.size
      let align ← (repr.scalarPlatformAlign cx).mapError fun
        | .scalar error => BackendReprError.scalar error
        | error => error
      let some align := align
        | throw .alignmentUnavailableForPair
      return some (← (Size.alignTo endOffset align).mapError BackendReprError.alignment)
  | .SimdVector | .Memory | .SimdScalableVector => return none

def toUnion : BackendRepr → BackendRepr
  | .Scalar scalar => .Scalar scalar.toUnion
  | .ScalarPair (a := a) (b := b) (bOffset := bOffset) =>
      .ScalarPair (a := a.toUnion) (b := b.toUnion) (bOffset := bOffset)
  | .SimdVector (element := element) (count := count) =>
      .SimdVector (element := element.toUnion) (count := count)
  | .Memory => .Memory (sized := true)
  | .SimdScalableVector (element := element) (count := count)
      (numberOfVectors := numberOfVectors) =>
      .SimdScalableVector (element := element.toUnion) (count := count)
        (numberOfVectors := numberOfVectors)

def eqUpToValidity : BackendRepr → BackendRepr → Bool
  | .Scalar left, .Scalar right => left.primitive == right.primitive
  | .SimdVector (element := leftElement) (count := leftCount),
      .SimdVector (element := rightElement) (count := rightCount) =>
      leftElement.primitive == rightElement.primitive && leftCount == rightCount
  | .ScalarPair (a := leftA) (b := leftB) (bOffset := leftOffset),
      .ScalarPair (a := rightA) (b := rightB) (bOffset := rightOffset) =>
      leftA.primitive == rightA.primitive &&
        leftB.primitive == rightB.primitive && leftOffset == rightOffset
  | left, right => left == right

end BackendRepr

end Miri.ABI
