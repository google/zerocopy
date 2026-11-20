import Miri.Interpreter.ValidityVisitor

/-! Concrete validity byte/provenance/padding operations. Allocation access is
explicitly ghost, as validate_place_internal requires; retagging remains a
separate actual machine effect in ValidityVisitor. All memory, hook-state and
touched-extra effects are committed before propagating failures. -/
namespace Miri.Interpreter.ValidityMemory
open Miri.ABI Miri.Memory
open Miri.Memory.Validity
abbrev M (S A : Type) := EStateM StepError S A

structure Environment (P Extra Kind H ProvExtra S : Type) where
  context : LocalReadContext P Extra Kind H ProvExtra
  memory : S → MemoryState P Extra Kind
  hooks : S → H
  putMemoryHooks : S → MemoryState P Extra Kind → H → S
  putTouched : S → Option (AllocationAccessRef P Extra) → S
  memoryError : H → MemoryOperandError → StepError
  pointerError : H → PtrAllocationError → StepError
  allocationError : AllocError → StepError

private def liftResult (result : Except StepError A) : M S A :=
  match result with | .ok value => pure value | .error error => throw error
private def commit (env : Environment P E K H X S) (memory : MemoryState P E K)
    (hooks : H) (touched : Option (AllocationAccessRef P E)) : M S Unit :=
  modify fun state => env.putTouched (env.putMemoryHooks state memory hooks) touched

private def readError (env : Environment P E K H X S) (expected : ExpectedValue) (error : AllocError) : StepError :=
  match Validity.classifyReadError expected error with
  | some failure => .undefinedBehavior s!"validation: {repr failure}"
  | none => env.allocationError error

/-- Actual primitive scalar/scalar-pair decoding, retaining full type identity.
Known initialization/provenance failures are mapped to validity categories. -/
def readImmediate [DecidableEq K] [DecidableEq P] [PointerProvenance P]
    (env : Environment P E K H X S) (operand : OpTy P) (expected : ExpectedValue) : M S (RvalueImmTy P) := do
  let state ← get
  let context := env.context
  let result := Miri.Interpreter.readImmediate (env.memory state) (env.hooks state) operand.op
    (localMemoryLayout operand.layout) context.runtime true context.globalKind
    context.globalHooks context.accessHooks context.dynamicLayout
  commit env result.memory result.hooks result.touched
  match result.outcome with
  | .ok value => return ⟨value.value,operand.layout⟩
  | .error (.allocation error) => throw (readError env expected error)
  | .error .invalidUninitBytes => throw (.undefinedBehavior s!"validation: {repr (ValidityFailure.uninitialized expected none)}")
  | .error error => throw (env.memoryError result.hooks error)

private def pointerAccess [DecidableEq K] (env : Environment P E K H X S)
    (place : MPlaceTy P) (size : Size) (write : Bool) : M S (Option (AllocationAccessRef P E)) := do
  let state ← get
  let context := env.context
  let access := if write then
      AllocationAccess.getPtrAllocMut (env.memory state) (env.hooks state)
        ⟨context.runtime.pointerSize⟩ place.mplace.ptr size true context.globalKind context.globalHooks context.accessHooks
    else
      AllocationAccess.getPtrAlloc (env.memory state) (env.hooks state)
        ⟨context.runtime.pointerSize⟩ place.mplace.ptr size true context.globalKind context.globalHooks context.accessHooks
  commit env access.memory access.hooks access.touched
  match access.outcome with
  | .ok reference => return reference
  | .error error => throw (env.pointerError access.hooks error)

/-- Numeric arrays and str validate initialized bytes while stripping pointer
provenance according to the actual provenance representation. No extra
alignment check is introduced: source uses get_ptr_alloc, not place access. -/
def readBytes [DecidableEq K] [PointerProvenance P] (env : Environment P E K H X S)
    (place : MPlaceTy P) (size : Size) (expected : ExpectedValue) : M S Unit := do
  let reference ← pointerAccess env place size false
  let some reference := reference | return
  match reference.allocation.getBytesStripProvenance env.context.runtime.base reference.range with
  | .ok _ => pure ()
  | .error error => throw (readError env expected error)

/-- A padding handle names the one mutable allocation reference obtained by
reset_padding. Later gap writes re-read its current allocation, preserving
all earlier gap writes and partial mutations on error. -/
structure PaddingHandle where
  allocId : AllocId
  range : AllocRange
  deriving DecidableEq, Repr

def beginPadding [DecidableEq K] (env : Environment P E K H X S)
    (place : MPlaceTy P) (size : Size) : M S (Option PaddingHandle) := do
  return (← pointerAccess env place size true).map fun reference => ⟨reference.allocId,reference.range⟩

/-- A zero-sized padding region obtains no allocation reference. The lens
identity states that committing the unchanged view has no effect. -/
theorem beginPadding_zero [DecidableEq K] (env : Environment P E K H X S)
    (place : MPlaceTy P) (state : S)
    (identity : env.putTouched (env.putMemoryHooks state (env.memory state) (env.hooks state)) none = state) :
    beginPadding env place Size.ZERO state = .ok none state := by
  have zero : AllocationAccess.getPtrAllocMut (env.memory state) (env.hooks state)
      ⟨env.context.runtime.pointerSize⟩ place.mplace.ptr Size.ZERO true
      env.context.globalKind env.context.globalHooks env.context.accessHooks =
      ⟨env.memory state, env.hooks state, none, .ok none⟩ := by
    with_unfolding_all rfl
  simp [beginPadding, pointerAccess, zero, commit, identity,
    get, getThe, MonadStateOf.get, EStateM.get, modify, modifyGet, MonadStateOf.modifyGet,
    EStateM.modifyGet, bind, Bind.bind, EStateM.bind, pure, Pure.pure, EStateM.pure]

private def mutate [DecidableEq K] (env : Environment P E K H X S) (handle : PaddingHandle)
    (action : Allocation P E → EStateM.Result AllocError (Allocation P E) Unit) : M S Unit := do
  let state ← get
  let some entry := (env.memory state).live.find? (fun entry => entry.1 == handle.allocId)
    | throw (.invalidProgram "validity mutable allocation disappeared")
  let result := action entry.2.allocation
  let allocation := match result with | .ok _ allocation | .error _ allocation => allocation
  let memory ← liftResult (((env.memory state).setLiveAllocation handle.allocId allocation).mapError
    fun error => .invalidProgram s!"validity allocation update: {repr error}")
  commit env memory (env.hooks state) (some ⟨handle.allocId,handle.range,allocation⟩)
  match result with
  | .ok () _ => pure ()
  | .error error _ => throw (env.allocationError error)

def writePadding [DecidableEq K] (env : Environment P E K H X S)
    (handle : PaddingHandle) (relative : AllocRange) : M S Unit := do
  let range ← liftResult ((handle.range.subrange relative).mapError fun error =>
    .invalidProgram s!"padding subrange: {repr error}")
  mutate env handle (Allocation.writeUninit range env.context.runtime.pointerSize)

def clearBytesProvenance [DecidableEq K] (env : Environment P E K H X S)
    (place : MPlaceTy P) (size : Size) : M S Unit := do
  let some reference ← pointerAccess env place size true | return
  let handle : PaddingHandle := ⟨reference.allocId,reference.range⟩
  mutate env handle (Allocation.clearProvenance reference.range env.context.runtime.pointerSize)

private def clearMemoryPlace [DecidableEq K] (env : Environment P E K H X S) (place : MPlaceTy P) : M S Unit := do
  let state ← get
  let context := env.context
  let accessed := getPlaceAllocMut (env.memory state) (env.hooks state)
    ⟨place.mplace,localMemoryLayout place.layout⟩ context.runtime true context.globalKind
    context.globalHooks context.accessHooks context.dynamicLayout
  commit env accessed.memory accessed.hooks accessed.touched
  let reference ← match accessed.outcome with
    | .ok reference => pure reference
    | .error error => throw (env.memoryError accessed.hooks error)
  let some reference := reference | return
  mutate env ⟨reference.allocId,reference.range⟩
    (Allocation.clearProvenance reference.range context.runtime.pointerSize)

/-- Source place.rs clear_provenance, including the no-provenance immediate
fast path and partial ScalarPair conversion. Under validation the local write
hook is suppressed; outside that scope its actual callback remains required. -/
def clearPlaceProvenance [DecidableEq K] [PointerProvenance P]
    (env : Environment P E K H X S) (placeHooks : PlaceHooks P S C Extra) (choice : C)
    (validationInProgress : M S Bool) (afterLocalWrite : MIR.LocalId → Bool → M S Unit)
    (place : RuntimePlace P) : M S Unit := do
  let value ← placeToOp placeHooks choice place
  if let .immediate immediate := value.op then
    unless immediate.hasProvenance do return
  match ← asMplaceOrMutableLocal placeHooks choice place with
  | .memory memory => clearMemoryPlace env memory
  | .immediateLocal id _ =>
    let frame ← placeHooks.getFrame
    let value ← match frame.getLocalOperand id with
      | .ok (.immediate value) => pure value
      | .ok (.indirect _) => throw (.invalidProgram "mutable local became indirect during clear")
      | .error error => throw (.stack error)
    let result := Immediate.clearProvenance value
    let value := match result with | .ok _ value | .error _ value => value
    let frame ← match frame.setLocalOperand id (.immediate value) with
      | .ok frame => pure frame | .error error => throw (.stack error)
    placeHooks.setFrame frame
    match result with
    | .error error _ => throw (ScalarOps.scalarError error)
    | .ok () _ => unless ← validationInProgress do afterLocalWrite id false

/-- Typed writes performed by provenance resetting explicitly use ghost
allocation access; optimized-local handling remains source's mutable-local
selection and scoped local-write policy. -/
def writeNoValidate [DecidableEq K] [DecidableEq P] [PointerProvenance P]
    (env : Environment P E K H X S) (placeHooks : PlaceHooks P S C Extra) (choice : C)
    (willValidate : MemoryOperandLayout → Bool) (value : Immediate P) (place : RuntimePlace P) : M S Unit := do
  if !place.layout.layout.isSized then throw (.invalidProgram "unsized validity immediate write")
  match ← asMplaceOrMutableLocal placeHooks choice place with
  | .immediateLocal id layout => placeHooks.writeLocalImmediate choice id layout value
  | .memory memory =>
    let state ← get
    let context := env.context
    let result := writeImmediateToMplaceNoValidate (env.memory state) (env.hooks state) value
      ⟨memory.mplace,localMemoryLayout memory.layout⟩ context.runtime true context.globalKind
      context.globalHooks context.accessHooks context.dynamicLayout willValidate
    commit env result.memory result.hooks result.touched
    match result.outcome with
    | .ok () => pure ()
    | .error error => throw (env.memoryError result.hooks error)

/-- Install the concrete allocation operations without replacing compiler,
reference, vtable or machine-retag queries with successful stubs. -/
def bind [DecidableEq K] [DecidableEq P] [PointerProvenance P]
    (base : ValidityVisitor.Hooks P S C Extra F A PaddingHandle)
    (env : Environment P E K H X S) (validationInProgress : M S Bool)
    (afterLocalWrite : MIR.LocalId → Bool → M S Unit)
    (willValidate : MemoryOperandLayout → Bool) : ValidityVisitor.Hooks P S C Extra F A PaddingHandle :=
  {base with
    readImmediate := fun c place expected => do readImmediate env (← base.toOp c place) expected
    clearProvenance := fun c place => clearPlaceProvenance env base.projection.place c validationInProgress afterLocalWrite place
    writeNoValidate := fun c value place => writeNoValidate env base.projection.place c willValidate value place
    readBytes := fun _ => readBytes env
    clearBytesProvenance := fun _ => clearBytesProvenance env
    beginPadding := fun _ => beginPadding env
    writePadding := fun _ => writePadding env }

end Miri.Interpreter.ValidityMemory
