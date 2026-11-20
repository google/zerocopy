import Miri.Interpreter.OperandPath
import Miri.Interpreter.Rvalue
import Miri.Interpreter.LocalAccess

/-! Pinned step.rs write_aggregate and write_repeat. The same MIR operands and
canonical layouts flow through RvalueHooks; stateful obligations retain effects
on failure. No field write is treated as initialization of aggregate padding. -/
namespace Miri.Interpreter
open Miri.ABI Miri.Memory

structure AggregateHooks (Prov S C V : Type) where
  target : TargetDataLayout
  placeLayout : V → LocalLayout
  evalOperand : C → MIR.Operand → Option LocalLayout → RvalueM S (OpTy Prov)
  evalOperandAt : C → OperandPath → MIR.Operand → Option LocalLayout → RvalueM S (OpTy Prov) := fun c _ => evalOperand c
  readPointer : C → OpTy Prov → RvalueM S (Pointer (Option Prov))
  readScalar : C → OpTy Prov → RvalueM S (Scalar Prov)
  projectDowncast : C → V → MIR.VariantIndex → RvalueM S V
  projectField : C → V → MIR.FieldIndex → RvalueM S V
  copyOp : C → OpTy Prov → V → RvalueM S Unit
  copyOpNoValidate : C → OpTy Prov → V → Bool → RvalueM S Unit
  writeDiscriminant : C → MIR.VariantIndex → V → RvalueM S Unit
  enforceValidity : C → LocalLayout → RvalueM S Bool
  /-- Includes recursive validity policy and reset_provenance_and_padding=true. -/
  validate : C → V → RvalueM S Unit
  forceAllocation : C → V → RvalueM S V
  length : C → V → RvalueM S UInt64
  getPlaceAllocMut : C → V → RvalueM S Unit
  projectIndex : C → V → UInt64 → RvalueM S V
  placePointer : V → Except StepError (Pointer (Option Prov))
  wrappingOffset : Pointer (Option Prov) → Size → Except StepError (Pointer (Option Prov))
  /-- No alignment requirement: first-element copy already checked it.
  Must retain nonoverlapping checks, memory hooks and partial mutations. -/
  memCopyRepeatedly : C → Pointer (Option Prov) → Pointer (Option Prov) →
    Size → UInt64 → Bool → RvalueM S Unit

private def aggregateLift (value : Except StepError A) : RvalueM S A :=
  match value with
  | .ok value => pure value
  | .error error => throw error

def writeAggregate (h : AggregateHooks P S C V) (choice : C)
    (kind : MIR.AggregateKind) (operands : Array MIR.Operand) (dest : V) :
    RvalueM S Unit := do
  let (variant, variantDest, activeField) ← match kind with
    | .Adt _ variant _ _ activeField => do
      let variantDest ← h.projectDowncast choice dest variant
      pure (variant, variantDest, activeField)
    | .RawPtr .. => do
      if operands.size != 2 then throw (.invalidProgram "raw pointer aggregate requires two operands")
      let some data := operands[0]? | throw (.invalidProgram "missing raw pointer data")
      let some metadataOperand := operands[1]? | throw (.invalidProgram "missing raw pointer metadata")
      let data ← h.evalOperandAt choice (OperandPath.aggregate 0) data none
      let data ← h.readPointer choice data
      let metadataOperand ← h.evalOperandAt choice (OperandPath.aggregate 1) metadataOperand none
      let metadata ← if metadataOperand.layout.layout.isZst then pure MemPlaceMeta.none
        else do pure (.metadata (← h.readScalar choice metadataOperand))
      let pointer ← match Immediate.newPointerWithMeta data metadata h.target with
        | .error error => throw (.invalidProgram s!"raw pointer aggregate representation failure: {repr error}")
        | .ok pointer => pure pointer
      h.copyOp choice ⟨.immediate pointer, h.placeLayout dest⟩ dest
      return
    | .Array _ | .Tuple | .Closure .. | .Coroutine .. | .CoroutineClosure .. =>
      pure (0, dest, none)
  if activeField.isSome && operands.size != 1 then
    throw (.invalidProgram "union aggregate requires exactly one operand")
  for index in [:operands.size] do
    let some operand := operands[index]? | throw (.invalidProgram "aggregate operand index")
    let field ← h.projectField choice variantDest (activeField.getD index)
    let operand ← h.evalOperandAt choice (OperandPath.aggregate index) operand (some (h.placeLayout field))
    h.copyOpNoValidate choice operand field false
  h.writeDiscriminant choice variant dest
  if ← h.enforceValidity choice (h.placeLayout dest) then
    h.validate choice dest

/-- The repeat count is the destination array length. Even zero-length repeats
first evaluate the operand and force allocation, then validate mutable access.
Positive lengths copy once and replicate the resulting bytes; the source can
alias the destination, so evaluating/copying every element would be incorrect. -/
def writeRepeat (h : AggregateHooks P S C V) (choice : C)
    (operand : MIR.Operand) (dest : V) : RvalueM S Unit := do
  let source ← h.evalOperandAt choice (OperandPath.rvalue "operand") operand none
  if !source.layout.layout.isSized then throw (.invalidProgram "repeat source is unsized")
  let dest ← h.forceAllocation choice dest
  let length ← h.length choice dest
  if length == 0 then
    h.getPlaceAllocMut choice dest
  else
    let first ← h.projectIndex choice dest 0
    h.copyOp choice source first
    let elemSize := (h.placeLayout first).layout.size
    let firstPtr ← aggregateLift (h.placePointer first)
    let restPtr ← aggregateLift (h.wrappingOffset firstPtr elemSize)
    h.memCopyRepeatedly choice firstPtr restPtr elemSize (length - 1) true

/-- Install the aggregate/repeat source ports into the existing rvalue dispatch. -/
def RvalueHooks.withAggregate (base : RvalueHooks P S C V)
    (aggregate : AggregateHooks P S C V) : RvalueHooks P S C V :=
  { base with
    writeAggregate := fun c k os d => Miri.Interpreter.writeAggregate aggregate c k os d
    writeRepeat := fun c o d => Miri.Interpreter.writeRepeat aggregate c o d }

/-- Actual pointer wrapping arithmetic, retaining provenance and target width. -/
def aggregateWrappingOffset (target : PointerArithmetic)
    (pointer : Pointer (Option Prov)) (size : Size) :
    Except StepError (Pointer (Option Prov)) :=
  (pointer.wrappingOffset size target).mapError fun error =>
    .invalidProgram s!"repeat wrapping offset: {repr error}"

/-- Concrete repeated-copy adapter to existing allocation/memory semantics.
The supplied state embedding must preserve unrelated execution state. -/
def aggregateMemoryCopyRepeatedly [DecidableEq Kind]
    (pointerSize : Size)
    (hooks : MemoryCopyHooks Prov Extra Kind HookState ProvExtra)
    (getMemory : S → MemoryState Prov Extra Kind) (getHooks : S → HookState)
    (putMemoryHooks : S → MemoryState Prov Extra Kind → HookState → S)
    (mapError : MemoryLifecycleError → StepError)
    (source dest : Pointer (Option Prov)) (size : Size) (count : UInt64)
    (nonoverlapping : Bool) : RvalueM S Unit := do
  let state ← EStateM.get
  let result := MemoryLifecycle.memCopyRepeatedly (getMemory state) (getHooks state)
    source dest size count nonoverlapping pointerSize hooks
  EStateM.set (putMemoryHooks state result.memory result.hooks)
  match result.outcome with
  | .error error => throw (mapError error)
  | .ok () => pure ()

end Miri.Interpreter
