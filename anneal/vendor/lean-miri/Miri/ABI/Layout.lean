import Miri.ABI.RuntimeLayout

/-! Source-shaped rustc_abi layout records and checked observation methods.
No type layout computation or type-system metadata is inferred here. -/
namespace Miri.ABI

inductive LayoutError where
  | fieldOutOfBounds (index count : Nat)
  | invalidUnionCount
  | invalidMemoryOrder
  | size (error : SizeError)
  | expectedArbitraryVariant
  | missingField (index : Nat)
  | missingVariant (index : Nat)
  | missingPointee
  deriving DecidableEq, Repr

inductive FieldsShape where
  | Primitive
  | Union (count : Nat)
  | Array (stride : Size) (count : UInt64)
  | Arbitrary (offsets : Array Size) (inMemoryOrder : Array Nat)
  deriving DecidableEq, Repr

namespace FieldsShape

def count : FieldsShape → Nat
  | .Primitive => 0
  | .Union count => count
  | .Array _ count => count.toNat
  | .Arbitrary offsets _ => offsets.size

def offset (fields : FieldsShape) (index : Nat) : Except LayoutError Size := do
  if index >= fields.count then throw (.fieldOutOfBounds index fields.count)
  match fields with
  | .Primitive => throw (.fieldOutOfBounds index 0)
  | .Union _ => return Size.ZERO
  | .Array stride _ => (stride.mul (UInt64.ofNat index)).mapError LayoutError.size
  | .Arbitrary offsets _ =>
      match offsets[index]? with
      | some offset => return offset
      | none => throw (.fieldOutOfBounds index offsets.size)

def validate : FieldsShape → Except LayoutError Unit
  | .Union 0 => .error .invalidUnionCount
  | .Arbitrary offsets order => do
      if order.size != offsets.size then throw .invalidMemoryOrder
      let mut seen : _root_.Array Nat := #[]
      for index in order do
        if index >= offsets.size || seen.contains index then throw .invalidMemoryOrder
        seen := seen.push index
      -- The source promises an increasing-offset permutation.
      let mut previous : UInt64 := 0
      for index in order do
        match offsets[index]? with
        | none => throw .invalidMemoryOrder
        | some offset =>
            if offset.bytes < previous then throw .invalidMemoryOrder
            previous := offset.bytes
  | _ => .ok ()

/-- Primitive deliberately yields the source's single pseudo-field. -/
def indexByIncreasingOffset (fields : FieldsShape) : Except LayoutError (_root_.Array Nat) := do
  fields.validate
  match fields with
  | .Primitive => return #[0]
  | .Arbitrary _ order => return order
  | _ => return (List.range fields.count).toArray

end FieldsShape

inductive TagEncoding where
  | Direct
  | Niche (untaggedVariant nicheVariantsStart nicheVariantsEnd : Nat) (nicheStart : U128)
  deriving DecidableEq, Repr

structure Niche where
  offset : Size
  value : Primitive
  validRange : WrappingRange
  deriving DecidableEq, Repr

structure VariantLayout where
  size : Size
  backendRepr : BackendRepr
  fieldOffsets : Array Size
  fieldsInMemoryOrder : Array Nat
  largestNiche : Option Niche
  uninhabited : Bool
  deriving DecidableEq, Repr

namespace VariantLayout

def isUninhabited (variant : VariantLayout) : Bool := variant.uninhabited
def hasFields (variant : VariantLayout) : Bool := !variant.fieldOffsets.isEmpty

end VariantLayout

inductive Variants where
  | Empty
  | Single (index : Nat)
  | Multiple (tag : Scalar) (tagEncoding : TagEncoding) (tagField : Nat)
      (variants : Array VariantLayout)
  deriving DecidableEq, Repr

structure LayoutData where
  fields : FieldsShape
  variants : Variants
  backendRepr : BackendRepr
  largestNiche : Option Niche
  uninhabited : Bool
  align : AbiAlign
  size : Size
  maxReprAlign : Option Align
  unadjustedAbiAlign : Align
  reprC : Bool
  randomizationSeed : UInt64
  deriving DecidableEq, Repr

abbrev Layout := LayoutData

namespace LayoutData

def isAggregate (layout : LayoutData) : Bool := !layout.backendRepr.isScalarOrSimd
def isUninhabited (layout : LayoutData) : Bool := layout.uninhabited
def isVariantUninhabited (layout : LayoutData) (index : Nat) : Bool :=
  match layout.variants with
  | .Empty => true
  | .Single actual => index != actual || layout.uninhabited
  | .Multiple _ _ _ variants => (variants[index]?).map VariantLayout.uninhabited |>.getD true

def isReprC (layout : LayoutData) : Bool := layout.reprC
def isUnsized (layout : LayoutData) : Bool := layout.backendRepr.isUnsized
def isSized (layout : LayoutData) : Bool := layout.backendRepr.isSized
def is1zst (layout : LayoutData) : Bool :=
  layout.isSized && layout.size.bytes == 0 && layout.align.abi.pow2 == 0

def isScalableVector (layout : LayoutData) : Bool :=
  match layout.backendRepr with | .SimdScalableVector => true | _ => false

def scalableVectorElementCount (layout : LayoutData) : Option BackendLaneCount :=
  match layout.backendRepr with
  | .SimdScalableVector (count := count) => some count
  | _ => none

def isZst (layout : LayoutData) : Bool :=
  match layout.backendRepr with
  | .Memory (sized := sized) => sized && layout.size.bytes == 0
  | _ => false

def isSsaStandalone (layout : LayoutData) : Bool :=
  match layout.backendRepr with | .Memory => layout.isZst | _ => true

def eqAbi (layout other : LayoutData) : Bool :=
  layout.size == other.size && layout.isSized == other.isSized &&
  layout.backendRepr.eqUpToValidity other.backendRepr &&
  layout.backendRepr.isBool == other.backendRepr.isBool &&
  layout.align.abi == other.align.abi && layout.maxReprAlign == other.maxReprAlign &&
  layout.unadjustedAbiAlign == other.unadjustedAbiAlign

end LayoutData

namespace VariantLayout

def fromLayout (layout : LayoutData) : Except LayoutError VariantLayout :=
  match layout.fields with
  | .Arbitrary offsets order => .ok {
      size := layout.size, backendRepr := layout.backendRepr, fieldOffsets := offsets,
      fieldsInMemoryOrder := order, largestNiche := layout.largestNiche,
      uninhabited := layout.uninhabited }
  | _ => .error .expectedArbitraryVariant

end VariantLayout

structure TyAndLayout (Ty : Type) where
  ty : Ty
  layout : LayoutData
  deriving DecidableEq, Repr

/-- Required compiler/type-system queries: callers supply evidence; this module
never fabricates the type of a field, variant, or pointee. -/
structure LayoutQueries (Ty : Type) where
  field : TyAndLayout Ty → Nat → Except LayoutError (TyAndLayout Ty)
  variant : TyAndLayout Ty → Nat → Except LayoutError (TyAndLayout Ty)
  pointee : TyAndLayout Ty → Except LayoutError (TyAndLayout Ty)

end Miri.ABI
