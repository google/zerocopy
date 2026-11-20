import Miri.Interpreter.Step
import Miri.Interpreter.IntegerOps
import Miri.Interpreter.Operand
import Miri.ABI.Layout
import Miri.MIR.Syntax

/-! Executable projection rules from pinned rustc `interpret/projection.rs`.
Compiler queries and machine-owned operations are required fallible callbacks.
No projection reads memory, validates a discriminant, or erases provenance. -/
namespace Miri.Interpreter
open Miri.ABI Miri.Memory

structure OpTy (Prov : Type) where
  op : Operand Prov
  layout : TyAndLayout MIR.TyId
  deriving Repr

inductive ProjectionError where
  | machineError (error : StepError)
  | obligation (operation : String)
  | invariant (message : String)
  | bounds (len index : UInt64)
  | pointerArithOverflow
  | layout (reason : LayoutError)
  | size (reason : SizeError)
  | align (reason : AlignError)
  | offset (reason : MemPlaceOffsetError)
  | immediate (reason : ImmediateError)
  | scalar (reason : ScalarError)
  deriving DecidableEq, Repr

/-- Compiler/machine dependencies are explicit, including ABI checking of
immediates and dynamic alignment computation (which may execute custom DST code).
`subsliceLayout` must construct the array type or retain the slice type and run
layout_of; `sliceMetadata` must use the target usize representation. -/
structure ProjectionCx (Prov : Type) where
  target : TargetDataLayout
  maxSizeOfVal : Size
  isSliceOrStr : MIR.TyId → Except ProjectionError Bool
  field : TyAndLayout MIR.TyId → Nat → Except ProjectionError (TyAndLayout MIR.TyId)
  variant : TyAndLayout MIR.TyId → Nat → Except ProjectionError (TyAndLayout MIR.TyId)
  dynamicAlign : MemPlaceMeta Prov → TyAndLayout MIR.TyId → Except ProjectionError (Option Align)
  packedAlign : MIR.TyId → Except ProjectionError (Option Align)
  immediateOffset : Immediate Prov → TyAndLayout MIR.TyId → Size → TyAndLayout MIR.TyId →
    Except ProjectionError (Immediate Prov)
  memoryOffset : MemPlace Prov → Size → OffsetMode → MemPlaceMeta Prov →
    Except ProjectionError (MemPlace Prov)
  subsliceLayout : TyAndLayout MIR.TyId → UInt64 → Except ProjectionError (TyAndLayout MIR.TyId × MemPlaceMeta Prov)
  layoutOf : MIR.TyId → Except ProjectionError (TyAndLayout MIR.TyId)
  deref : OpTy Prov → Except ProjectionError (OpTy Prov)
  localIndex : MIR.LocalId → Except ProjectionError UInt64

/-- The actual memory adapter delegates to the existing pointer arithmetic
semantics, retaining allocation identity, provenance and misalignment. -/
def projectionMemoryOffset (target : PointerArithmetic)
    (resolve : PointerResolver Prov ProvExtra) (lookup : LiveAllocationLookup)
    (place : MemPlace Prov) (offset : Size) (mode : OffsetMode)
    (metadata : MemPlaceMeta Prov) : Except ProjectionError (MemPlace Prov) :=
  place.offsetWithMeta offset mode metadata target resolve lookup |>.mapError .offset

/-- Source `ImmTy::offset_`. ABI validation is required before extraction and
on the resulting immediate, even for uninitialized/uninhabited/ZST values. -/
def projectionImmediateOffset
    (validate : Immediate Prov → LayoutData → Except ProjectionError Unit)
    (value : Immediate Prov) (source : TyAndLayout MIR.TyId) (offset : Size)
    (target : TyAndLayout MIR.TyId) (debugAssertions : Bool := true) : Except ProjectionError (Immediate Prov) := do
  if debugAssertions then validate value source.layout
  let limit ← offset.add target.layout.size |>.mapError .size
  if limit.bytes > source.layout.size.bytes then throw (.invariant "immediate projection out of bounds")
  let result ← match value with
    | .uninit => pure .uninit
    | _ => do
      let forget := target.layout.isUninhabited || target.layout.isZst ||
        (match target.layout.backendRepr, target.layout.variants, target.layout.fields with
         | .Memory, .Single _, .Arbitrary offsets _ => offsets.isEmpty
         | _, _, _ => false)
      if forget then pure .uninit
      else if target.layout.size == source.layout.size then do
        if offset != Size.ZERO then throw (.invariant "whole immediate at nonzero offset")
        pure value
      else
        match value, source.layout.backendRepr with
        | .scalarPair first second, .ScalarPair (bOffset := secondOffset) =>
          if offset == Size.ZERO then pure (.scalar first)
          else if offset == secondOffset then pure (.scalar second)
          else throw (.invariant "invalid scalar pair field offset")
        | _, _ => throw (.invariant "invalid immediate field access")
  validate result target.layout
  return result

namespace OpTy

def metadata (self : OpTy Prov) : MemPlaceMeta Prov :=
  match self.op with
  | .indirect place => place.metadata
  | .immediate _ => .none

def offsetWithMeta (cx : ProjectionCx Prov) (base : OpTy Prov) (offset : Size)
    (mode : OffsetMode) (metadata : MemPlaceMeta Prov) (layout : TyAndLayout MIR.TyId) :
    Except ProjectionError (OpTy Prov) := do
  let op : Operand Prov ← match base.op with
    | .indirect place => pure (.indirect (← cx.memoryOffset place offset mode metadata))
    | .immediate value => do
      if metadata.hasMeta then throw (.invariant "metadata on immediate")
      pure (.immediate (← cx.immediateOffset value base.layout offset layout))
  return ⟨op, layout⟩

def offset (cx : ProjectionCx Prov) (base : OpTy Prov) (offset : Size)
    (layout : TyAndLayout MIR.TyId) : Except ProjectionError (OpTy Prov) := do
  if !layout.layout.isSized then throw (.invariant "offset requires sized output")
  base.offsetWithMeta cx offset .inbounds .none layout

def transmute (cx : ProjectionCx Prov) (base : OpTy Prov)
    (layout : TyAndLayout MIR.TyId) : Except ProjectionError (OpTy Prov) := do
  if !base.layout.layout.isSized || !layout.layout.isSized || base.layout.layout.size != layout.layout.size then
    throw (.invariant "transmute requires equally sized layouts")
  base.offsetWithMeta cx .ZERO .wrapping .none layout

def len [PointerProvenance Prov] (cx : ProjectionCx Prov) (base : OpTy Prov) :
    Except ProjectionError UInt64 := do
  if !base.layout.layout.isSized then
    if !(← cx.isSliceOrStr base.layout.ty) then throw (.invariant "len on unsized non-slice")
    let scalar ← base.metadata.unwrapMeta |>.mapError .immediate
    scalar.toTargetUsize (Size.fromBits cx.target.pointerWidth.bits) |>.mapError .scalar
  else
    match base.layout.layout.fields with
    | .Array _ count => return count
    | _ => throw (.invariant "len on non-array")

end OpTy

def projectField (cx : ProjectionCx Prov) (base : OpTy Prov) (field : Nat) :
    Except ProjectionError (OpTy Prov) := do
  let offset ← base.layout.layout.fields.offset field |>.mapError .layout
  let layout ← cx.field base.layout field
  let (metadata, offset) ← if !layout.layout.isSized then do
    if base.layout.layout.isSized then throw (.invariant "unsized field in sized parent")
    let metadata := base.metadata
    match ← cx.dynamicAlign metadata layout with
    | some align =>
      let packed ← cx.packedAlign base.layout.ty
      let align := match packed with | some p => align.min p | none => align
      let offset ← offset.alignTo align |>.mapError .align
      pure (metadata, offset)
    | none =>
      if offset != Size.ZERO then throw (.obligation "ExternTypeField")
      pure (metadata, offset)
    else pure (.none, offset)
  base.offsetWithMeta cx offset .inbounds metadata layout

def projectDowncast (cx : ProjectionCx Prov) (base : OpTy Prov) (variant : Nat) :
    Except ProjectionError (OpTy Prov) := do
  if base.metadata.hasMeta then throw (.invariant "downcast requires thin place")
  let layout ← cx.variant base.layout variant
  base.offset cx .ZERO layout

def projectIndex [PointerProvenance Prov] (cx : ProjectionCx Prov) (base : OpTy Prov)
    (index : UInt64) : Except ProjectionError (OpTy Prov) := do
  match base.layout.layout.fields with
  | .Array stride _ =>
    let len ← base.len cx
    if index >= len then throw (.bounds len index)
    let some offset := IntegerOps.computeSizeInBytes stride index cx.maxSizeOfVal | throw .pointerArithOverflow
    let layout ← cx.field base.layout 0
    base.offset cx offset layout
  | _ => throw (.invariant "index on non-array")

def projectConstantIndex [PointerProvenance Prov] (cx : ProjectionCx Prov) (base : OpTy Prov)
    (offset minLength : UInt64) (fromEnd : Bool) : Except ProjectionError (OpTy Prov) := do
  let n ← base.len cx
  if n < minLength then throw (.bounds minLength n)
  let index ← if fromEnd then do
    if offset == 0 || offset > minLength then throw (.invariant "invalid from-end constant index")
    pure (n - offset)
    else do
      if offset >= minLength then throw (.invariant "invalid constant index")
      pure offset
  projectIndex cx base index

def prepareSubslice [PointerProvenance Prov] (cx : ProjectionCx Prov) (base : OpTy Prov)
    (fromIndex to : UInt64) (fromEnd : Bool) : Except ProjectionError (Size × UInt64) := do
  let len ← base.len cx
  let actualTo ← if fromEnd then do
    let sum := fromIndex.toNat + to.toNat
    if sum >= 2^64 || sum > len.toNat then
      throw (.bounds len (UInt64.ofNat (min sum (2^64-1))))
    pure (len - to)
    else pure to
  let offset ← match base.layout.layout.fields with
    | .Array stride _ => stride.mul fromIndex |>.mapError .size
    | _ => throw (.invariant "subslice on non-array")
  if actualTo < fromIndex then throw (.invariant "subslice length underflow")
  return (offset, actualTo - fromIndex)

def projectSubslice [PointerProvenance Prov] (cx : ProjectionCx Prov) (base : OpTy Prov)
    (fromIndex to : UInt64) (fromEnd : Bool) : Except ProjectionError (OpTy Prov) := do
  let (offset,count) ← prepareSubslice cx base fromIndex to fromEnd
  let (layout, metadata) ← cx.subsliceLayout base.layout count
  base.offsetWithMeta cx offset .inbounds metadata layout

/-- Iterator range state is advanced before projecting the element, even when
that projection fails, matching `Range::next` followed by fallible offset. -/
structure ProjectionArrayIterator (Prov : Type) where
  base : OpTy Prov
  nextIndex : UInt64
  endIndex : UInt64
  stride : Size
  fieldLayout : TyAndLayout MIR.TyId

def projectArrayFields [PointerProvenance Prov] (cx : ProjectionCx Prov)
    (base : OpTy Prov) (unitLayout : TyAndLayout MIR.TyId) :
    Except ProjectionError (ProjectionArrayIterator Prov) := do
  let stride ← match base.layout.layout.fields with
    | .Array stride _ => pure stride
    | _ => throw (.invariant "array iterator on non-array")
  let len ← base.len cx
  let fieldLayout ← cx.field base.layout 0
  let endOffset ← stride.mul len |>.mapError .size
  let _ ← base.offset cx endOffset unitLayout
  return ⟨base, 0, len, stride, fieldLayout⟩

def ProjectionArrayIterator.next (cx : ProjectionCx Prov) :
    EStateM ProjectionError (ProjectionArrayIterator Prov) (Option (UInt64 × OpTy Prov)) := do
  let self ← EStateM.get
  if self.nextIndex >= self.endIndex then return none
  let index := self.nextIndex
  EStateM.set { self with nextIndex := index + 1 }
  let offset ← match self.stride.mul index with
    | .ok value => pure value
    | .error reason => throw (.size reason)
  let value ← match self.base.offsetWithMeta cx offset .wrapping .none self.fieldLayout with
    | .ok value => pure value
    | .error reason => throw reason
  return some (index, value)

/-- Consume the existing source MIR projection syntax; oversized imported Nat
indices fail explicitly rather than silently truncating to upstream u64. -/
def project [PointerProvenance Prov] (cx : ProjectionCx Prov) (base : OpTy Prov)
    (elem : MIR.ProjectionElem) : Except ProjectionError (OpTy Prov) := do
  match elem with
  | .Field field _ => projectField cx base field
  | .Downcast _ variant => projectDowncast cx base variant
  | .Deref => cx.deref base
  | .Index localId => projectIndex cx base (← cx.localIndex localId)
  | .UnwrapUnsafeBinder ty => base.transmute cx (← cx.layoutOf ty)
  | .ConstantIndex offset minLength fromEnd =>
    if offset >= 2^64 || minLength >= 2^64 then throw (.invariant "MIR index exceeds u64")
    projectConstantIndex cx base (UInt64.ofNat offset) (UInt64.ofNat minLength) fromEnd
  | .Subslice fromIndex to fromEnd =>
    if fromIndex >= 2^64 || to >= 2^64 then throw (.invariant "MIR subslice exceeds u64")
    projectSubslice cx base (UInt64.ofNat fromIndex) (UInt64.ofNat to) fromEnd
  | .OpaqueCast _ => throw (.invariant "OpaqueCast after borrowck")
  | .PhantomDeref => throw (.invariant "PhantomDeref after borrowck")

end Miri.Interpreter
