import Miri.Interpreter.FrameRelevance
import Miri.Interpreter.TypedRetag
import Miri.Interpreter.PlaceMachine
import Miri.Interpreter.ValidityVisitor

/-! Production-shaped typed retag bindings. No precomputed RetagPipeline
request is constructed: all leaves execute inside TypedRetag's source driver. -/
namespace Miri.Interpreter.TypedMachineBindings
open Miri.ABI Miri.Memory Miri.MIR
open MachineHooks (State M)

/-- Install actual machine writes and source reference reconstruction. The
remaining required dictionary contains genuine compiler/pointer queries. -/
def retagHooks [DecidableEq K] (access : PlaceMachine.AccessConfig K User)
    (queries : TypedRetag.Hooks K User) : TypedRetag.Hooks K User :=
  { queries with
    writeUninit := PlaceMachine.writeMemory access (fun _ => false) .uninit
    reconstruct := fun value place => do
      let immediate ← match place.mplace.toRef access.runtime.base with
        | .ok value => pure value
        | .error error => throw (.invalidProgram s!"retagged reference: {reprStr error}")
      return ⟨immediate, value.layout⟩ }

/-- Copies retag through the actual validity visitor only when its source
resetProvenanceAndPadding policy requests it. FnEntry/None/Default modes are
read here at the source event, rather than captured while constructing hooks. -/
def bindValidity [DecidableEq K]
    (base : ValidityVisitor.Hooks Provenance (State K User) C MachineHooks.FrameExtra F A Padding)
    (retag : TypedRetag.Hooks K User) (budget : Nat) :
    ValidityVisitor.Hooks Provenance (State K User) C MachineHooks.FrameExtra F A Padding :=
  { base with retagPointer := fun _ value ty => TypedRetag.machineRetagPtrValue retag budget value ty }

/-- place.rs write_immediate/copy_op_inner validation policies: destination
reset is true; a transmute validates at the source layout first, including a
wrapping zero-offset projection, then the destination's validation pass. The
recursive machine policy remains an explicit source query. -/
def bindValidation [DecidableEq K]
    (compiler : PlaceMachine.CompilerHooks K User C)
    (copy : PlaceCopyHooks Provenance (State K User) C)
    (visitor : ValidityVisitor.Hooks Provenance (State K User) C MachineHooks.FrameExtra F A Padding)
    (retag : TypedRetag.Hooks K User) (retagBudget validationBudget : Nat)
    (recursive : C → LocalLayout → M K User Bool) :
    PlaceMachine.CompilerHooks K User C × PlaceCopyHooks Provenance (State K User) C :=
  let visitor := bindValidity visitor retag retagBudget
  let validate := fun c (place : RuntimePlace Provenance) => do
    let recursively ← recursive c place.layout
    ValidityVisitor.validatePlace visitor c validationBudget place recursively true
  ({ compiler with validate },
   { copy with validateSource := fun c source dest => do
      if !source.layout.isSized || !dest.layout.layout.isSized || source.layout.size != dest.layout.layout.size then
        throw (.invalidProgram "copy source-layout validation requires equally sized layouts")
      let transmuted ← PlaceDynamic.offsetWithMeta visitor.projection c dest .ZERO .wrapping .none source
      validate c transmuted })

/-- Bind typed places and source retag events to rvalue execution. The compiler
validation dictionary must use bindValidity so copy/reset paths share this
same stateful retag driver. Raw pointer and integer copies gain no extra retag. -/
def bindRvalue [DecidableEq K]
    (base : RvalueHooks Provenance (State K User) C (RuntimePlace Provenance))
    (access : PlaceMachine.AccessConfig K User) (allocation : PlaceMachine.AllocationConfig K User)
    (compiler : PlaceMachine.CompilerHooks K User C) (queries : TypedRetag.Hooks K User)
    (budget : Nat) (copy : PlaceCopyHooks Provenance (State K User) C)
    (evaluatePlace : C → MIR.Place → Bool → M K User (RuntimePlace Provenance)) :
    RvalueHooks Provenance (State K User) C (RuntimePlace Provenance) :=
  let place := PlaceMachine.placeHooks access allocation compiler
  let retag := retagHooks access queries
  { base with
    placeLayout := RuntimePlace.layout
    evalPlace := evaluatePlace
    readImmediate := fun _ => PlaceMachine.readImmediate access
    writeImmediate := fun c value dest => writePlaceImmediate place c value dest
    writePointer := fun c pointer dest => do
      let value ← match Scalar.fromMaybePointer access.runtime.base pointer with
        | .ok value => pure value
        | .error error => throw (.invalidProgram s!"pointer immediate: {reprStr error}")
      writePlaceImmediate place c (.scalar value) dest
    forceAllocation := fun c dest => return (← forceAllocation place c dest).mplace
    toRef := fun _ memory =>
      match memory.toRef access.runtime.base with
      | .ok value => pure value
      | .error error => throw (.invalidProgram s!"place reference: {reprStr error}")
    withRetagMode := fun _ mode action => MachineHooks.withRetagMode mode action
    retagPtrValue := fun _ value ty => TypedRetag.machineRetagPtrValue retag budget value ty
    enforceValidity := compiler.enforceValidity
    copyOp := fun c source dest => copyRuntimePlace place copy c source dest false
    copyOpAllowTransmute := fun c source dest => copyRuntimePlace place copy c source dest true }

/-- Source pop_stack_frame_raw: release protectors while the frame remains
current, before removing it and before return-value copying. -/
def popRaw [DecidableEq K] (retag : TypedRetag.Hooks K User) :
    M K User (Frame Provenance LocalLayout MachineHooks.FrameExtra) := do
  MachineHooks.beforeStackPopWithEnsure retag.ensureTreeExtra
  FrameRelevance.beforeStackPop
  let state ← get
  let (stack, frame) ← match state.stack.popFrame with
    | .ok result => pure result
    | .error error => throw (.stack error)
  set { state with stack }
  return frame

/-- Call argument and return-slot copies use the canonical place copy path;
FnEntry scope comes from Call.initStackFrame, not from dictionary construction.
In-place protection is performed after each source copy. -/
def bindCall [DecidableEq K]
    (base : CallHooks Provenance (State K User) C MachineHooks.FrameExtra Other Extern FnABI ArgABI)
    (access : PlaceMachine.AccessConfig K User) (allocation : PlaceMachine.AllocationConfig K User)
    (compiler : PlaceMachine.CompilerHooks K User C) (storage : MachineHooks.StorageHooks K User)
    (queries : TypedRetag.Hooks K User) (budget : Nat)
    (copy : PlaceCopyHooks Provenance (State K User) C)
    (evaluatePlace : C → MIR.Place → Bool → M K User (RuntimePlace Provenance)) :
    CallHooks Provenance (State K User) C MachineHooks.FrameExtra Other Extern FnABI ArgABI :=
  let place := PlaceMachine.placeHooks access allocation compiler
  let retag := retagHooks access queries
  { base with
    debugAssertions := compiler.debugAssertions
    getFrame := MachineHooks.currentFrame
    setFrame := MachineHooks.setCurrentFrame
    frameIndex := do
      match (← get).stack.frameIndex with
      | .ok index => pure index
      | .error error => throw (.stack error)
    evalPlace := fun c p skip => return (← evaluatePlace c p skip).stackView
    placeToOp := fun c view => do placeToOp place c view.toRuntimePlace
    forceAllocation := fun c view => do forceAllocation place c view.toRuntimePlace
    localLayout := PlaceMachine.layoutLocal compiler
    localSpan := compiler.localSpan
    storageLiveDyn := fun _ id metadata => MachineHooks.storageLiveDyn storage id metadata
    copyAllowTransmute := fun c source view => do
      copyRuntimePlace place copy c source view.toRuntimePlace true
    popRaw := fun _ => popRaw retag
    protectArgument := fun _ p => TypedRetag.protectInPlaceFunctionArgument retag budget p
    withRetagMode := fun _ mode action => MachineHooks.withRetagMode mode action
    allocateStack := fun _ layout => PlaceMachine.allocateStack allocation layout
    copyToMemory := fun c source dest =>
      copyRuntimePlace place copy c source ⟨.memory dest.mplace, dest.layout⟩ false }

/-- Return reads local zero before pop, copies after protector release/pop,
and invokes the same transmute-copy/validity path as argument passing. Cleanup
and unwind policy stay the required source lifecycle dictionary fields. -/
def bindControl [DecidableEq K]
    (base : ControlHooks Provenance LocalLayout MachineHooks.FrameExtra (MachineHooks.MachineState K User)
      C (OpTy Provenance))
    (access : PlaceMachine.AccessConfig K User) (allocation : PlaceMachine.AllocationConfig K User)
    (compiler : PlaceMachine.CompilerHooks K User C)
    (copy : PlaceCopyHooks Provenance (State K User) C)
    (queries : TypedRetag.Hooks K User) :
    ControlHooks Provenance LocalLayout MachineHooks.FrameExtra (MachineHooks.MachineState K User)
      C (OpTy Provenance) :=
  let place := PlaceMachine.placeHooks access allocation compiler
  { base with
    popFrame := fun _ state => MachineHooks.run (popRaw (retagHooks access queries)) state
    returnOperand := fun c state => MachineHooks.run (PlaceMachine.localToOp compiler c 0) state
    copyReturn := fun c value view state => MachineHooks.run
      (do copyRuntimePlace place copy c value view.toRuntimePlace true) state }

end Miri.Interpreter.TypedMachineBindings
