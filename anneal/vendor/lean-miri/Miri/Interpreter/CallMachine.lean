import Miri.Interpreter.FrameMetadata
import Miri.Interpreter.TypedMachineBindings
import Miri.Interpreter.ThreadStacks
import Miri.Interpreter.Unwind

/-! Whole-state stack lifecycle for real calls. Unlike the generic StackEffect
adapter, local-storage hooks operate on the actual current frame, retaining
FrameExtra clock mutations and exact StepError classifications. -/
namespace Miri.Interpreter.CallMachine
open Miri.ABI Miri.Memory Miri.MIR
open MachineHooks (State M FrameExtra)

structure Lifecycle (K User C : Type) where
  compiler : FrameMetadata.CompilerHooks K User
  storage : MachineHooks.StorageHooks K User
  /-- Ghost label for the actual new locals buffer; no guessed zero token. -/
  freshLocalsIdentity : MachineHooks.MachineState K User →
    MachineHooks.MachineState K User × LocalsIdentity
  /-- tcx.def_span(body.source.def_id()), not the caller's location. -/
  preambleSpan : LoadedBody → M K User SpanRef
  /-- Instantiate/normalize/evaluate every required_const in source order. -/
  requiredConstants : LoadedBody → M K User Unit
  afterPop : C → Frame Provenance LocalLayout FrameExtra → Bool → M K User ReturnAction

/-- Source push_stack_frame_raw. Initialization fails before insertion;
required-constant failure retains the inserted frame and untouched cache. -/
def pushRaw (h : Lifecycle K User C) (debugAssertions : Bool)
    (fnInstance : CallInstance) (body : LoadedBody) (destination : RuntimeStackPlace Provenance)
    (continuation : ReturnContinuation) : M K User Unit := do
  let state ← get
  let isStop := match continuation with | .stop _ => true | .goto .. => false
  if debugAssertions && state.stack.frames.isEmpty != isStop then
    throw (.stack (.rootFrameCondition state.stack.frames.isEmpty isStop))
  let (machine,identity) := h.freshLocalsIdentity state.machine
  set {state with machine}
  let span ← h.preambleSpan body
  let frame := Frame.create body fnInstance () continuation destination span identity
  let frame ← MachineHooks.initFrame (FrameMetadata.userRelevance h.compiler) frame
  modify fun state => {state with stack := ⟨state.stack.frames.push frame⟩}
  h.requiredConstants body
  FrameRelevance.afterStackPush debugAssertions

/-- Source mir/syntax.rs StorageLive contract and Body::vars_and_temps_iter:
only variables/temporaries with no StorageLive or StorageDead anywhere in the
body are implicitly live. Argument and return slots are excluded here. -/
def alwaysLiveVarsAndTemps (body : Body) : Except StepError (Array LocalId) := do
  let mut annotated := #[]
  for block in body.basicBlocks do
    for statement in block.statements do
      let localId := match statement.kind with
        | .StorageLive id | .StorageDead id => some id
        | _ => none
      if let some id := localId then
        if id >= body.locals.size then throw (.invalidProgram "storage annotation local out of bounds")
        annotated := annotated.push id
  return ((List.range body.locals.size).filter fun id =>
    id > body.argumentCount && !annotated.contains id).toArray

/-- Source push_stack_frame_done with actual local clocks retained after each
storage-live event, including failure prefixes. -/
def pushDone (h : Lifecycle K User C) : M K User Unit := do
  MachineHooks.storageLiveDyn h.storage 0 .none
  let frame ← MachineHooks.currentFrame
  let locals ← match alwaysLiveVarsAndTemps frame.body with
    | .ok locals => pure locals
    | .error error => throw error
  for localId in locals do MachineHooks.storageLiveDyn h.storage localId .none
  let state ← get
  match state.stack.updateCurrentLocation (.mir .start) with
  | .error error => throw (.stack error)
  | .ok stack => set {state with stack}

/-- Source cleanup_stack_frame; detached locals/varargs retain allocation
identity and deallocate in source order. NoCleanup skips the machine hook. -/
def cleanup (h : Lifecycle K User C) (choice : C) (unwinding : Bool)
    (frame : Frame Provenance LocalLayout FrameExtra) : M K User ReturnAction := do
  let cleanup := match frame.returnContinuation with
    | .goto .. => true | .stop cleanup => cleanup
  if !cleanup then return .noCleanup
  for slot in frame.locals do
    if let .live (.indirect place) := slot.value then h.storage.deallocateStack place.ptr
  for arg in frame.vaList do h.storage.deallocateStack arg.mplace.ptr
  let result ← h.afterPop choice frame unwinding
  if result == .noCleanup then
    throw (.invalidProgram "after_stack_pop returned NoCleanup during cleanup")
  return result

/-- Bind the machine after_stack_pop implementation, including real caught
unwind payload/call transitions, instead of an external success hook. -/
def withUnwind (h : Lifecycle K User C) (unwind : Unwind.Hooks K User C Other) :
    Lifecycle K User C :=
  {h with afterPop := fun c frame unwinding => Unwind.afterStackPop unwind c frame.extra unwinding}

/-- Compiler/ABI/foreign dispatch stays in base; all frame, place, storage and
retag actions below are actual canonical machine actions. Miri does not override
rustc Machine::after_stack_frame_init, whose pinned implementation returns (). -/
def hooks [DecidableEq K]
    (base : CallHooks Provenance (State K User) C FrameExtra Other Extern FnABI ArgABI)
    (lifecycle : Lifecycle K User C)
    (access : PlaceMachine.AccessConfig K User) (allocation : PlaceMachine.AllocationConfig K User)
    (compiler : PlaceMachine.CompilerHooks K User C)
    (queries : TypedRetag.Hooks K User) (retagBudget : Nat)
    (copy : PlaceCopyHooks Provenance (State K User) C)
    (evaluatePlace : C → MIR.Place → Bool → M K User (RuntimePlace Provenance)) :
    CallHooks Provenance (State K User) C FrameExtra Other Extern FnABI ArgABI :=
  let bound := TypedMachineBindings.bindCall base access allocation compiler lifecycle.storage
    queries retagBudget copy evaluatePlace
  {bound with
    pushRaw := fun _ => pushRaw lifecycle compiler.debugAssertions
    pushDone := fun _ => pushDone lifecycle
    cleanup := cleanup lifecycle
    afterFrameInit := fun _ => pure () }

/-- Return and unwind terminators use the same raw-pop and detached cleanup
pipeline as calls/tail calls, with actual typed return copying. -/
def controlHooks [DecidableEq K]
    (base : ControlHooks Provenance LocalLayout FrameExtra (MachineHooks.MachineState K User)
      C (OpTy Provenance))
    (lifecycle : Lifecycle K User C)
    (access : PlaceMachine.AccessConfig K User) (allocation : PlaceMachine.AllocationConfig K User)
    (compiler : PlaceMachine.CompilerHooks K User C)
    (copy : PlaceCopyHooks Provenance (State K User) C)
    (queries : TypedRetag.Hooks K User) :
    ControlHooks Provenance LocalLayout FrameExtra (MachineHooks.MachineState K User)
      C (OpTy Provenance) :=
  let bound := TypedMachineBindings.bindControl base access allocation compiler copy queries
  {bound with cleanupFrame := fun c unwinding frame =>
    MachineHooks.run (cleanup lifecycle c unwinding frame)}

/-- Threaded factory uses the actual process-wide locals-buffer identity supply
and synchronizes every success/error prefix with saved per-thread real stacks. -/
def threadedHooks [DecidableEq K]
    (base : CallHooks Provenance (ThreadStacks.State K User) C FrameExtra Other Extern FnABI ArgABI)
    (lifecycle : Lifecycle K (ThreadStacks.Storage User) C)
    (access : PlaceMachine.AccessConfig K (ThreadStacks.Storage User))
    (allocation : PlaceMachine.AllocationConfig K (ThreadStacks.Storage User))
    (compiler : PlaceMachine.CompilerHooks K (ThreadStacks.Storage User) C)
    (queries : TypedRetag.Hooks K (ThreadStacks.Storage User)) (retagBudget : Nat)
    (copy : PlaceCopyHooks Provenance (ThreadStacks.State K User) C)
    (evaluatePlace : C → MIR.Place → Bool → ThreadStacks.M K User (RuntimePlace Provenance)) :
    CallHooks Provenance (ThreadStacks.State K User) C FrameExtra Other Extern FnABI ArgABI :=
  ThreadStacks.bindCall (hooks base {lifecycle with freshLocalsIdentity := ThreadStacks.freshLocalsIdentity}
    access allocation compiler queries retagBudget copy evaluatePlace)
/-- Threaded return/unwind factory keeps the registry coherent on every
protector-release, deallocation and catch-unwind failure prefix. -/
def threadedControlHooks [DecidableEq K]
    (base : ControlHooks Provenance LocalLayout FrameExtra
      (MachineHooks.MachineState K (ThreadStacks.Storage User)) C (OpTy Provenance))
    (lifecycle : Lifecycle K (ThreadStacks.Storage User) C)
    (access : PlaceMachine.AccessConfig K (ThreadStacks.Storage User))
    (allocation : PlaceMachine.AllocationConfig K (ThreadStacks.Storage User))
    (compiler : PlaceMachine.CompilerHooks K (ThreadStacks.Storage User) C)
    (copy : PlaceCopyHooks Provenance (ThreadStacks.State K User) C)
    (queries : TypedRetag.Hooks K (ThreadStacks.Storage User)) :
    ControlHooks Provenance LocalLayout FrameExtra
      (MachineHooks.MachineState K (ThreadStacks.Storage User)) C (OpTy Provenance) :=
  ThreadStacks.bindControl (controlHooks base lifecycle access allocation compiler copy queries)

end Miri.Interpreter.CallMachine
