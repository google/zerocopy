import Miri.Interpreter.TypedMachineBindings
import Miri.Interpreter.ValidityMemory
import Miri.Interpreter.PointerMachine

/-! Miri machine validation defaults and scoped validity execution.
Source machine.rs ValidationMode/enforce_validity/cached_union_data_range and
interpret/memory.rs ghost_run_mut. Actual validation/retag/memory ports are
bound here; only compiler/pointer/trait queries remain supplied dictionaries.
-/
namespace Miri.Interpreter.ValidityMachine
open Miri.ABI Miri.Memory
open Miri.Memory.Validity

inductive ValidationMode where
  | No | Shallow | Deep
  deriving DecidableEq, Repr

inductive AlignmentCheck where
  | None | Symbolic | Int
  deriving DecidableEq, Repr

/-- Concrete additional fields for the canonical machine's User payload. This
extends machine state; it is not a second program representation or value IR. -/
structure Control (User : Type) where
  payload : User
  validation : ValidationMode
  alignment : AlignmentCheck
  ghost : Bool := false
  unionDataRanges : Array (MIR.TyId × DataRangeSet) := #[]

abbrev UserState (User : Type) := PointerMachine.User (Control User)

abbrev State (K User : Type) := MachineHooks.State K (UserState User)
abbrev M (K User A : Type) := MachineHooks.M K (UserState User) A
abbrev Access (K User : Type) := PlaceMachine.AccessConfig K (UserState User)
abbrev Compiler (K User C : Type) := PlaceMachine.CompilerHooks K (UserState User) C

def enforceValidity : M K User Bool := return (← get).machine.user.payload.validation != .No

def enforceValidityRecursively : M K User Bool := return (← get).machine.user.payload.validation == .Deep

def validationInProgress : M K User Bool := return (← get).machine.user.payload.ghost

/-- Exact non-nesting ghost scope. Ordinary allocation/local read/write hooks
observe this flag and are suppressed; borrow/race trackers remain installed
because source retagging during validity still executes their actual reborrow
operations. Both normal and error results restore the flag while retaining
all memory, clocks, borrow state, payload and cache mutations. -/
def withGhostValidation (action : M K User A) : M K User A := fun state =>
  if state.machine.user.payload.ghost then .error (.invalidProgram "ghost_mode was already set") state
  else
    let active := {state with machine := {state.machine with user := {state.machine.user with payload := {state.machine.user.payload with ghost := true}}}}
    let finish := fun (after : State K User) =>
      let flag := after.machine.user.payload.ghost
      let restored := {after with machine := {after.machine with user := {after.machine.user with payload := {after.machine.user.payload with ghost := false}}}}
      (flag,restored)
    match action active with
    | .ok value after =>
      let (flag,restored) := finish after
      if flag then .ok value restored
      else .error (.invalidProgram "ghost_mode was unset by someone else") restored
    | .error error after =>
      let (flag,restored) := finish after
      if flag then .error error restored
      else .error (.invalidProgram "ghost_mode was unset by someone else") restored

/-- Source machine.rs caches union data ranges by canonical compiler type ID.
The computation runs only on a miss and inserts only after success; queries
and partial effects of a failing computation are retained without a cache hit. -/
def cachedUnionRanges (layout : LocalLayout) (compute : M K User DataRangeSet) : M K User DataRangeSet := do
  let state ← get
  if let some entry := state.machine.user.payload.unionDataRanges.find? (fun entry => entry.1 == layout.ty) then
    return entry.2
  let ranges ← compute
  modify fun state => {state with machine := {state.machine with user := {state.machine.user with payload := {state.machine.user.payload with
    unionDataRanges := state.machine.user.payload.unionDataRanges.push (layout.ty,ranges)}}}}
  return ranges

/-- Capture the actual current ghost flag at each memory operation, rather
than when an interpreter hook dictionary is created. -/
def scopedAccess (access : Access K User) : M K User (Access K User) := do
  return {access with ghostMode := ← validationInProgress}

def readImmediate [DecidableEq K] (access : Access K User) (value : OpTy Provenance) :
    M K User (RvalueImmTy Provenance) := do
  PlaceMachine.readImmediate (← scopedAccess access) value

def compilerPolicy (compiler : Compiler K User C) : Compiler K User C :=
  {compiler with
    validationInProgress := validationInProgress
    enforceValidity := fun _ _ => enforceValidity }

/-- Scoped optimized-local hooks and memory writes share the same canonical
state flag. The write's enforce-validity decision is sampled at its source
call, including padding-clearing policy inside the memory writer. -/
def placeHooks [DecidableEq K] (access : Access K User)
    (allocation : PlaceMachine.AllocationConfig K (UserState User)) (compiler : Compiler K User C) :
    PlaceHooks Provenance (State K User) C MachineHooks.FrameExtra :=
  let compiler := compilerPolicy compiler
  let base := PlaceMachine.placeHooks access allocation compiler
  {base with
    writeMemoryNoValidate := fun _ value place => do
      let access ← scopedAccess access
      let validate ← enforceValidity
      PlaceMachine.writeMemory access (fun _ => validate) value place }

/-- Actual byte/provenance/padding environment. Typed machine errors pass
through the legacy allocation access boundary without being flattened into an
unclassified string, and touched borrowed-global extras remain retained. -/
def memoryEnvironment (access : Access K User) :
    ValidityMemory.Environment Provenance Miri.TreeBorrows.BorrowTree K
      (PlaceMachine.AccessState K (UserState User)) ProvenanceExtra (State K User) := {
  context := {
    runtime := access.runtime, ghostMode := true, globalKind := access.globalKind
    globalHooks := access.globalHooks, accessHooks := PlaceMachine.accessHooks access
    dynamicLayout := access.dynamicLayout }
  memory := fun state => state.machine.memory
  hooks := fun state => ⟨state.machine,none⟩
  putMemoryHooks := fun state memory hooks => {state with machine := {hooks.machine with memory}}
  putTouched := fun state touched => {state with machine := access.retainTouched state.machine touched}
  memoryError := fun hooks error => hooks.pendingError.getD (access.memoryError error)
  pointerError := fun hooks error => hooks.pendingError.getD (access.memoryError (.pointerAccess error))
  allocationError := fun error => access.memoryError (.allocation error) }

private def resolve (access : Access K User) (pointer : Pointer (Option Provenance)) (size : Int) :
    M K User (Except UInt64 (ResolvedPointer ProvenanceExtra)) := do
  let state ← get
  match access.resolvePointer state.machine.memory pointer size state.machine with
  | .ok value machine => set {state with machine}; return value
  | .error error machine => set {state with machine}; throw error

private def accessError (error : AccessError) : StepError :=
  match error with
  | .allocationLookup (.unavailable id) => .callback s!"missing allocation metadata: {repr id}"
  | .malformedAlignment error => .invalidProgram s!"{repr error}"
  | .pointerArithmetic error => .invalidProgram s!"{repr error}"
  | .signedSizeOutsideI64 size => .invalidProgram s!"signed access size outside i64: {size}"
  | _ => .undefinedBehavior s!"validity pointer access: {repr error}"

/-- Typed form used by validity.rs, which remaps pointer access errors into
path-qualified validation failures. Zero-sized validity retains the source
no-resolve fast path. -/
def checkPointerAccessResult (access : Access K User) (pointer : Pointer (Option Provenance))
    (size : Size) : M K User (Except AccessError Unit) := do
  let signed ← match sizeAsI64 size with
    | .ok size => pure size | .error error => return .error error
  if signed == 0 then return .ok ()
  let resolved ← resolve access pointer signed
  let memory := (← get).machine.memory
  match checkPtrAccess ⟨access.runtime.pointerSize⟩ pointer size (.dereferenceable "pointer")
      (fun _ _ => resolved) memory.getAllocInfo with
  | .ok () => return .ok ()
  | .error error => return .error error

/-- General machine users retain the ordinary typed access-error mapping;
validity alone consumes `checkPointerAccessResult` to add its path context. -/
def checkPointerAccess (access : Access K User) (pointer : Pointer (Option Provenance))
    (size : Size) : M K User Unit := do
  match ← checkPointerAccessResult access pointer size with
  | .ok () => pure ()
  | .error error => throw (accessError error)

/-- Run the canonical alignment check while keeping its typed failure for
validity.rs to classify with the active validation path. Resolution failures
still use the ordinary machine error channel, and retain their state prefix. -/
def checkPointerAlignResult (access : Access K User) (pointer : Pointer (Option Provenance))
    (required : Align) : M K User (Except Misalignment Unit) := do
  if required.pow2 > Align.MAX.pow2 then throw (.invalidProgram "malformed validity alignment")
  let state ← get
  if state.machine.user.payload.alignment == .None || required.pow2 == 0 then return .ok ()
  let resolved ← resolve access pointer 0
  let state ← get
  let mut override : Option Misalignment := none
  if let .ok resolved := resolved then
    let info ← match state.machine.memory.getAllocInfo resolved.allocId with
      | .ok info => pure info
      | .error error => throw (.invalidProgram s!"alignment allocation metadata: {repr error}")
    let promise := (state.machine.user.symbolicAlignment.find? (fun entry => entry.1 == resolved.allocId)).map
      (fun entry => (entry.2.1,entry.2.2))
    override ← match PointerMachine.symbolicAlignment (state.machine.user.payload.alignment == .Symbolic)
        info.kind info.align promise resolved.offset required with
      | .ok result => pure result
      | .error error => throw (.invalidProgram s!"symbolic alignment: {repr error}")
  match checkPtrAlign pointer required true (fun _ _ => resolved) state.machine.memory.getAllocInfo
      (fun _ _ _ _ _ => override) with
  | .ok () => return .ok ()
  | .error (.alignmentCheckFailed misalignment) => return .error misalignment
  | .error error => throw (accessError error)

/-- General machine users retain the ordinary alignment error mapping. The
validity visitor consumes `checkPointerAlignResult` to apply validity.rs's
path-qualified error message without changing the underlying UB category. -/
def checkPointerAlign (access : Access K User) (pointer : Pointer (Option Provenance))
    (required : Align) : M K User Unit := do
  match ← checkPointerAlignResult access pointer required with
  | .ok () => pure ()
  | .error misalignment => throw (accessError (.alignmentCheckFailed misalignment))

/-- Miri provenance has absolute addresses, so scalar_may_be_null uses exactly
ScalarInt::is_null without CTFE allocation guesses. Malformed scalar widths
remain an explicit error. -/
def scalarMayBeNull (scalar : Scalar Provenance) : M K User Bool :=
  match scalar.tryToScalarInt with
  | .ok (.integer integer) => pure integer.isNull
  | .ok (.erasedPointer ..) => throw (.invalidProgram "absolute Miri pointer erased its address")
  | .error error => throw (ScalarOps.scalarError error)

/-- Source CTFE mutability check: locals are mutable, memory must be interned,
and any local cache of that global must agree with compiler mutability. -/
def inMutableMemory (place : RuntimePlace Provenance) : M K User Bool := do
  match place.ref with
  | .local .. => return true
  | .memory place =>
    let some (.concrete id _) := place.ptr.provenance | return false
    let memory := (← get).machine.memory
    let some global := memory.findGlobal? id | throw (.invalidProgram "validity memory was not interned")
    if let some cached := memory.live.find? (fun entry => entry.1 == id) then
      if cached.2.allocation.mutability != global.mutability then
        throw (.invalidProgram "interned allocation mutability disagrees with local cache")
    return global.mutability == .Mut

/-- Close portable validity leaves with concrete typed places, scalar/byte
memory operations, dynamic layout/vtable drivers, local index reads, source
union cache and real scoped TypedRetag. Pointer dereference/access/alignment,
compiler classification/path/layout facts and CTFE allocation-kind queries
remain explicit in the supplied base dictionary. -/
def visitor [DecidableEq K]
    (base : ValidityVisitor.Hooks Provenance (State K User) C MachineHooks.FrameExtra F A ValidityMemory.PaddingHandle)
    (access : Access K User) (allocation : PlaceMachine.AllocationConfig K (UserState User))
    (compiler : Compiler K User C) (retag : TypedRetag.Hooks K (UserState User))
    (retagBudget : Nat) :
    ValidityVisitor.Hooks Provenance (State K User) C MachineHooks.FrameExtra F A ValidityMemory.PaddingHandle :=
  let compiler := compilerPolicy compiler
  let place := placeHooks access allocation compiler
  let dynamic := PlaceDynamic.withVTable base.projection.dynamic base.vtable
  let projection := {base.projection with
    place, dynamic
    localIndex := fun c id => do
      let value ← PlaceMachine.localToOp compiler c id
      let value ← readImmediate access value
      let scalar ← match value.imm.toScalar with
        | .ok scalar => pure scalar | .error error => throw (.invalidProgram s!"index immediate: {repr error}")
      match scalar.toTargetUsize access.runtime.pointerSize with
      | .ok index => pure index | .error error => throw (ScalarOps.scalarError error) }
  let discriminant := {base.discriminant with
    readImmediate := fun _ value => readImmediate access value
    toOp := fun c value => placeToOp place c value }
  let base := {base with
    projection, discriminant
    toOp := fun c value => placeToOp place c value
    sizeAndAlign := fun c value => DynamicLayout.sizeAndAlignFromMeta dynamic c projection.dynamicFuel
      value.mplace.metadata value.layout
    cachedUnionRanges := fun _ layout compute => cachedUnionRanges layout compute
    withGhostValidation := withGhostValidation
    checkPointerAccess := fun _ => checkPointerAccessResult access
    checkPointerAlign := fun _ => checkPointerAlign access
    checkPointerAlignResult := fun _ => checkPointerAlignResult access
    scalarMayBeNull := fun _ => scalarMayBeNull
    inMutableMemory := fun _ => inMutableMemory
    ptrToPlace := fun _ => retag.immPtrToMPlace }
  let environment := memoryEnvironment access
  let base := {base with
    readImmediate := fun c value expected => do
      ValidityMemory.readImmediate environment (← placeToOp place c value) expected
    clearProvenance := fun c value => ValidityMemory.clearPlaceProvenance environment place c
      validationInProgress MachineHooks.afterLocalWrite value
    writeNoValidate := fun c value destination => do
      let validate ← enforceValidity
      ValidityMemory.writeNoValidate environment place c (fun _ => validate) value destination
    readBytes := fun _ => ValidityMemory.readBytes environment
    clearBytesProvenance := fun _ => ValidityMemory.clearBytesProvenance environment
    beginPadding := fun _ => ValidityMemory.beginPadding environment
    writePadding := fun _ => ValidityMemory.writePadding environment }
  {base with retagPointer := fun c value ty => do
    let dynamicSize := fun (place : MPlaceTy Provenance) =>
      DynamicLayout.sizeAndAlignFromMeta dynamic c projection.dynamicFuel place.mplace.metadata place.layout
    let memoryPlace := fun (place : RuntimePlace Provenance) =>
      match place.ref with
      | .memory memory => pure (MPlaceTy.mk memory place.layout)
      | .local .. => throw (.invalidProgram "memory-only freeze projection returned local")
    let freeze := {retag.freeze with
      sizeAndAlign := dynamicSize
      projectField := fun place index => do
        memoryPlace (← PlaceDynamic.field projection c ⟨.memory place.mplace,place.layout⟩ index)
      arrayLength := fun place => PlaceDynamic.length projection c ⟨.memory place.mplace,place.layout⟩
      projectIndex := fun place index => do
        memoryPlace (← PlaceDynamic.index projection c ⟨.memory place.mplace,place.layout⟩ index)
      projectBox := fun place => do
        let (pointer,allocator) ← base.projectBox c ⟨.memory place.mplace,place.layout⟩
        return (← memoryPlace pointer,← memoryPlace allocator)
      unpackDynTrait := fun place => do
        let .dynamic expected ← base.classify c place.layout.ty
          | throw (.invalidProgram "freeze dyn unpack on non-dynamic type")
        let inner ← VTable.unpackDynTrait base.vtable c ⟨.indirect place.mplace,place.layout⟩ expected
        let .indirect memory := inner.op | throw (.invalidProgram "dyn unpack returned immediate")
        return ⟨memory,inner.layout⟩ }
    let retag := {TypedMachineBindings.retagHooks access retag with
      checkPtrAccess := checkPointerAccess access
      sizeAndAlign := dynamicSize
      freeze }
    TypedRetag.machineRetagPtrValue retag retagBudget value ty }

/-- Ordinary write/copy validation defaults: reset=true; recursive iff Deep.
Mode No is handled by enforceValidity at the source caller. Explicit direct
validatePlace requests still validate, as the interpreter source does. -/
def validateRuntime [DecidableEq K]
    (h : ValidityVisitor.Hooks Provenance (State K User) C MachineHooks.FrameExtra F A Pad)
    (choice : C) (budget : Nat) (place : RuntimePlace Provenance) (reset : Bool) : M K User Unit := do
  ValidityVisitor.validatePlace h choice budget place (← enforceValidityRecursively) reset

def bindValidation [DecidableEq K]
    (compiler : Compiler K User C) (copy : PlaceCopyHooks Provenance (State K User) C)
    (h : ValidityVisitor.Hooks Provenance (State K User) C MachineHooks.FrameExtra F A Pad)
    (budget : Nat) : Compiler K User C × PlaceCopyHooks Provenance (State K User) C :=
  let compiler := compilerPolicy compiler
  ({compiler with validate := fun c place => validateRuntime h c budget place true},
   {copy with validateSource := fun c source destination => do
    if !source.layout.isSized || !destination.layout.layout.isSized || source.layout.size != destination.layout.layout.size then
      throw (.invalidProgram "source validation transmute requires equally sized layouts")
    let sourcePlace ← PlaceDynamic.offsetWithMeta h.projection c destination .ZERO .wrapping .none source
    validateRuntime h c budget sourcePlace true })

/-- Stateful default rvalue binding. Every place memory write samples the
current ghost/validation flags; reference/raw-pointer retag triggers and modes
remain exactly those chosen by the existing Rvalue dispatcher. Arithmetic,
casts, constants and operand evaluation remain in the supplied base driver. -/
def bindRvalue [DecidableEq K]
    (base : RvalueHooks Provenance (State K User) C (RuntimePlace Provenance))
    (access : Access K User) (allocation : PlaceMachine.AllocationConfig K (UserState User))
    (compiler : Compiler K User C) (copy : PlaceCopyHooks Provenance (State K User) C)
    (h : ValidityVisitor.Hooks Provenance (State K User) C MachineHooks.FrameExtra F A Pad) :
    RvalueHooks Provenance (State K User) C (RuntimePlace Provenance) :=
  let place := placeHooks access allocation compiler
  {base with
    placeLayout := RuntimePlace.layout
    evalPlace := PlaceDynamic.evalPlace h.projection
    readImmediate := fun _ => readImmediate access
    writeImmediate := fun c value dest => writePlaceImmediate place c value dest
    writePointer := fun c pointer dest => do
      let value ← match Scalar.fromMaybePointer access.runtime.base pointer with
        | .ok value => pure value
        | .error error => throw (.invalidProgram s!"pointer immediate: {repr error}")
      writePlaceImmediate place c (.scalar value) dest
    forceAllocation := fun c dest => return (← forceAllocation place c dest).mplace
    toRef := fun _ memory =>
      match memory.toRef access.runtime.base with
      | .ok value => pure value
      | .error error => throw (.invalidProgram s!"place reference: {repr error}")
    withRetagMode := fun _ mode action => MachineHooks.withRetagMode mode action
    retagPtrValue := h.retagPointer
    enforceValidity := fun _ _ => enforceValidity
    copyOp := fun c source dest => copyRuntimePlace place copy c source dest false
    copyOpAllowTransmute := fun c source dest => copyRuntimePlace place copy c source dest true }

end Miri.Interpreter.ValidityMachine
