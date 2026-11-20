import Miri.Interpreter.VTable
import Miri.Interpreter.MemoryOperand

/-! Source `eval_context.rs::size_and_align_from_meta/size_and_align_of_val`.
Recursive compiler type traversal has explicit execution fuel; exhaustion is
an error and never a fabricated dynamic size. -/
namespace Miri.Interpreter
open Miri.ABI Miri.Memory

inductive DynamicTypeKind where
  | adt (isSimd : Bool)
  | tuple (isSimd : Bool)
  | dynamic (expectedTrait : Nat)
  | slice | str | foreign
  deriving DecidableEq, Repr

structure DynamicLayoutHooks (P S C : Type) where
  target : TargetDataLayout
  maxSizeOfVal : Size
  classify : C → MIR.TyId → RvalueM S DynamicTypeKind
  field : C → TyAndLayout MIR.TyId → Nat → RvalueM S (TyAndLayout MIR.TyId)
  packedAlign : C → MIR.TyId → RvalueM S (Option Align)
  vtableSizeAndAlign : C → Pointer (Option P) → Option Nat → RvalueM S (Size × Align)

namespace DynamicLayout
private def liftResult (result : Except StepError A) : RvalueM S A :=
  match result with | .ok result => pure result | .error error => throw error
private def invalid (message : String) : RvalueM S A := throw (.invalidProgram message)
private def alignTo (size : Size) (align : Align) : RvalueM S Size :=
  liftResult (size.alignTo align |>.mapError fun e => .invalidProgram (toString e))
private def addSize (left right : Size) : RvalueM S Size :=
  liftResult (left.add right |>.mapError fun e => .invalidProgram (toString e))
private def metadataScalar (metadata : MemPlaceMeta P) : RvalueM S (Memory.Scalar P) :=
  match metadata.unwrapMeta with
  | .ok scalar => pure scalar
  | .error _ => invalid "unsized type requires metadata"

/-- Exact sized fast path and all selected source unsized arms. Type IDs and
canonical layouts remain paired through recursive field queries. -/
def sizeAndAlignFromMeta [PointerProvenance P] (h : DynamicLayoutHooks P S C)
    (choice : C) (fuel : Nat) (metadata : MemPlaceMeta P)
    (layout : TyAndLayout MIR.TyId) : RvalueM S (Option (Size × Align)) := do
  if layout.layout.isSized then return some (layout.layout.size, layout.layout.align.abi)
  match fuel with
  | 0 => throw (.resourceExhaustion "dynamic layout recursion fuel")
  | fuel + 1 =>
    let kind ← h.classify choice layout.ty
    match kind with
    | .adt simd | .tuple simd =>
      if simd then invalid "unsized aggregate cannot be SIMD"
      let count := layout.layout.fields.count
      if count == 0 then invalid "unsized aggregate requires a tail field"
      let offset ← liftResult (layout.layout.fields.offset (count - 1) |>.mapError
        fun e => .invalidProgram s!"{repr e}")
      let sizedAlign := layout.layout.align.abi
      let field ← h.field choice layout (count - 1)
      let some (tailSize, tailAlign) ← sizeAndAlignFromMeta h choice fuel metadata field
        | return none
      let tailAlign ← match kind with
        | .adt _ => do
          match ← h.packedAlign choice layout.ty with
          | some packed => pure (tailAlign.min packed)
          | none => pure tailAlign
        | _ => pure tailAlign
      let fullAlign := sizedAlign.max tailAlign
      let adjusted ← alignTo offset tailAlign
      let fullSize ← alignTo (← addSize adjusted tailSize) fullAlign
      let codegenSize ← alignTo (← addSize offset tailSize) fullAlign
      if fullSize != codegenSize then invalid "DST layout disagrees with codegen size"
      if fullSize.bytes > h.maxSizeOfVal.bytes then throw (.undefinedBehavior "InvalidMeta(TooBig)")
      return some (fullSize, fullAlign)
    | .dynamic expected =>
      let scalar ← metadataScalar metadata
      let ptr ← liftResult (scalar.toPointer h.target |>.mapError ScalarOps.scalarError)
      return some (← h.vtableSizeAndAlign choice ptr (some expected))
    | .slice | .str =>
      let scalar ← metadataScalar metadata
      let len ← liftResult (scalar.toTargetUsize (Size.fromBits h.target.pointerWidth.bits)
        |>.mapError ScalarOps.scalarError)
      let elem ← h.field choice layout 0
      let product := elem.layout.size.bytes.toNat * len.toNat
      let size := Size.ofBytes (UInt64.ofNat (min product (2^64 - 1)))
      if size.bytes > h.maxSizeOfVal.bytes then throw (.undefinedBehavior "InvalidMeta(SliceTooBig)")
      return some (size, elem.layout.align.abi)
    | .foreign => return none

def sizeAndAlignOfVal [PointerProvenance P] (h : DynamicLayoutHooks P S C) (choice : C)
    (fuel : Nat) (value : OpTy P) : RvalueM S (Option (Size × Align)) :=
  sizeAndAlignFromMeta h choice fuel value.metadata value.layout

/-- Concrete adapter for ProjectionCx.dynamicAlign. The effectful state is
retained in RvalueM; callers should not erase effects to fabricate a pure query. -/
def alignmentFromMeta [PointerProvenance P] (h : DynamicLayoutHooks P S C) (choice : C)
    (fuel : Nat) (metadata : MemPlaceMeta P) (layout : TyAndLayout MIR.TyId) : RvalueM S (Option Align) := do
  return (← sizeAndAlignFromMeta h choice fuel metadata layout).map Prod.snd

/-- Recovering canonical type identity is mandatory because the memory operand
view intentionally stores only size/alignment/ABI. Resolver errors preserve the
updated memory and hook state; none is the genuine Foreign result. -/
def memoryResolver [PointerProvenance P]
    (h : DynamicLayoutHooks P (MemoryState P E K × H) C) (choice : C) (fuel : Nat)
    (recoverLayout : MemoryOperandPlace P → Except StepError (TyAndLayout MIR.TyId)) :
    DynamicLayoutResolver P E K H := fun memory hooks place =>
  let action : RvalueM (MemoryState P E K × H) (Option (Size × Align)) := do
    let layout ← liftResult (recoverLayout place)
    if localMemoryLayout layout != place.layout then invalid "recovered dynamic layout disagrees with memory view"
    sizeAndAlignFromMeta h choice fuel place.mplace.metadata layout
  match action (memory, hooks) with
  | .ok result state => ⟨state.1, state.2, .ok result⟩
  | .error error state => ⟨state.1, state.2, .error s!"{repr error}"⟩

end DynamicLayout
end Miri.Interpreter
