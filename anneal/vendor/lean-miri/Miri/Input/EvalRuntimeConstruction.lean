import Miri.Input.EvalEntryMachine
import Miri.Input.EvalBootstrap
import Miri.Input.EvalExecutable

namespace Miri.Input.EvalRuntimeConstruction
open Miri.ABI Miri.Memory Miri.MIR Miri.Interpreter
abbrev W := EvalEntryMachine.W
abbrev EntryUser Os R P H D O Aff B Host := EvalExecutable.U Os R P H D O Aff B Host
abbrev EntryOuter Os R P H D O Aff B Host := ExecutionStateTransport.Outer (W Os R P H D O Aff B Host)
abbrev EntryState Os R P H D O Aff B Host :=
  MachineHooks.State MiriMemoryKind (EntryOuter Os R P H D O Aff B Host)

/-- Internal source-platform bridge preserving every place operation. -/
def outerPlaceHooks (hooks : PlaceHooks Provenance
    (MachineHooks.State MiriMemoryKind (ExecutionStateTransport.Inner (W Os R P H D O Aff B Host)))
    C MachineHooks.FrameExtra) :
    PlaceHooks Provenance (MachineHooks.State MiriMemoryKind
      (ExecutionStateTransport.Outer (W Os R P H D O Aff B Host))) C MachineHooks.FrameExtra :=
  { getFrame := ExecutionStateTransport.action hooks.getFrame
    setFrame := fun frame => ExecutionStateTransport.action (hooks.setFrame frame)
    debugAssertions := hooks.debugAssertions
    frameIndex := ExecutionStateTransport.action hooks.frameIndex
    resolveLayout := fun choice sourceLocal => ExecutionStateTransport.action (hooks.resolveLayout choice sourceLocal)
    localToOp := fun choice sourceLocal => ExecutionStateTransport.action (hooks.localToOp choice sourceLocal)
    projection := fun choice => ExecutionStateTransport.action (hooks.projection choice)
    deref := fun choice place skip => ExecutionStateTransport.action (hooks.deref choice place skip)
    checkPlaceType := fun choice place value => ExecutionStateTransport.action (hooks.checkPlaceType choice place value)
    allocateStack := fun choice layout => ExecutionStateTransport.action (hooks.allocateStack choice layout)
    writeMemoryNoValidate := fun choice value place => ExecutionStateTransport.action (hooks.writeMemoryNoValidate choice value place)
    afterLocalMovedToMemory := fun choice sourceLocal place => ExecutionStateTransport.action (hooks.afterLocalMovedToMemory choice sourceLocal place)
    memoryOffset := fun choice place amount mode metadata => ExecutionStateTransport.action (hooks.memoryOffset choice place amount mode metadata)
    writeLocalImmediate := fun choice sourceLocal layout value => ExecutionStateTransport.action (hooks.writeLocalImmediate choice sourceLocal layout value)
    enforceValidity := fun choice layout => ExecutionStateTransport.action (hooks.enforceValidity choice layout)
    validate := fun choice place => ExecutionStateTransport.action (hooks.validate choice place) }

/-- Internal source-platform bridge on the same live runtime world. -/
def outerProjection (hooks : PlaceProjectionHooks Provenance
    (MachineHooks.State MiriMemoryKind (ExecutionStateTransport.Inner (W Os R P H D O Aff B Host)))
    C MachineHooks.FrameExtra) :
    PlaceProjectionHooks Provenance (EntryState Os R P H D O Aff B Host) C MachineHooks.FrameExtra :=
  { place := outerPlaceHooks hooks.place
    target := hooks.target
    maxSizeOfVal := hooks.maxSizeOfVal
    dynamic := {
      target := hooks.dynamic.target
      maxSizeOfVal := hooks.dynamic.maxSizeOfVal
      classify := fun choice ty => ExecutionStateTransport.action (hooks.dynamic.classify choice ty)
      field := fun choice layout index => ExecutionStateTransport.action (hooks.dynamic.field choice layout index)
      packedAlign := fun choice ty => ExecutionStateTransport.action (hooks.dynamic.packedAlign choice ty)
      vtableSizeAndAlign := fun choice pointer metadata => ExecutionStateTransport.action (hooks.dynamic.vtableSizeAndAlign choice pointer metadata) }
    dynamicFuel := hooks.dynamicFuel
    isSliceOrStr := fun choice ty => ExecutionStateTransport.action (hooks.isSliceOrStr choice ty)
    field := fun choice layout index => ExecutionStateTransport.action (hooks.field choice layout index)
    variant := fun choice layout index => ExecutionStateTransport.action (hooks.variant choice layout index)
    packedAlign := fun choice ty => ExecutionStateTransport.action (hooks.packedAlign choice ty)
    subsliceLayout := fun choice layout index => ExecutionStateTransport.action (hooks.subsliceLayout choice layout index)
    layoutOf := fun choice ty => ExecutionStateTransport.action (hooks.layoutOf choice ty)
    localIndex := fun choice sourceLocal => ExecutionStateTransport.action (hooks.localIndex choice sourceLocal) }

/-! Build argv allocation and projection from the same fixed source Config.
Only the sysroot sentinel query remains a concrete compiler capability; its
failure is demanded only when the actual target is not no_core. -/
def argumentsFromExecution
    (compiler : CompilerProviders.Prepared)
    (execution : EvalExecutable.Core Os R P H D O Aff B Host C ClockHost)
    (noCore : Bool)
    (coreSentinelMirAvailable : MachineHooks.M MiriMemoryKind
      (EntryOuter Os R P H D O Aff B Host) Bool) :
    Except String (EntryArguments.Hooks MiriMemoryKind
      (ThreadStacks.Storage (EvalExecutable.U Os R P H D O Aff B Host))
      (ValidityMachine.Control (ThreadStacks.Storage (W Os R P H D O Aff B Host)))
      P C) := do
  let layout ← EvalEntryMachine.layouts compiler
  let targetTriple := compiler.program.input.producer.targetTriple
  let windows := (targetTriple.splitOn "-").contains "windows"
  let arrays := fun choice element count => ExecutionStateTransport.action
    (RuntimeArrayQueries.arrayLayout EvalProjectionMachine.arrays element count)
  let addresses : FunctionPointers.AddressLens
      (ThreadStacks.Storage (EvalExecutable.U Os R P H D O Aff B Host))
      (ValidityMachine.Control (ThreadStacks.Storage (W Os R P H D O Aff B Host))) := {
    get := ExecutionStateTransport.toInner
    put := fun _ inner => ExecutionStateTransport.toOuter inner
    getPut := by intros; rfl
    putGet := by intros; rfl
    putPut := by intros; rfl }
  pure {
    addresses
    allocation := execution.allocation
    arithmetic := execution.arithmetic
    access := ExecutionMemoryTransport.access execution.access
    place := outerProjection execution.projection
    layouts := layout.arguments
    arrayLayout := arrays
    entryPointers := EvalWorld.roots.entry
    putEntryPointers := fun user entry =>
      let control := user.user.payload
      let world := control.payload
      let world := {world with runtime := {world.runtime with entry}}
      {user with user := {user.user with payload := {control with payload := world}}}
    windows
    isNoCore := pure noCore
    coreSentinelMirAvailable
  }

/-- Collect the separately source-built startup components into the exact
late-init record. This keeps compiler registries and platform/host effects
visible as distinct capabilities while avoiding caller replacement of the
main callback with a baseline dictionary. -/
def bootstrapHooks
    (arguments : EntryArguments.Hooks MiriMemoryKind (ThreadStacks.Storage U)
      AddressPayload Payload C)
    (main : MainMachine.Hooks U C O X F A Aff Payload)
    (environment : EnvVars.Hooks (Option Provenance) Os (MainMachine.State U))
    (externStatics : ExternStatic.InitHooks (MainMachine.State U))
    (compiler : CompilerProviders.Prepared)
    (symbols : IntrinsicSymbolsMachine.Access (ThreadStacks.Storage U))
    (image : AllocationImage.Imported)
    (vtableRuntime : VTableMachine.Hooks MiriMemoryKind (ThreadStacks.Storage U) O) :
    EvalBootstrap.Hooks U C O X F A Aff Payload AddressPayload Os :=
  ⟨arguments,main,environment,externStatics,compiler,symbols,image,vtableRuntime⟩

/-- Run a real initialized frame through the fixed execution Config and actual
local thread-stack scheduler. Stack-empty callbacks remain explicit in `base`;
the stop predicate lets a harness capture a completed call frame before a later
iteration asks for a main/TLS callback it did not initialize. -/
def runReadyConfiguredPrefixUntil [DecidableEq Os]
    (configs : C → EvalExecutable.Core Os R P H D O Aff B Host C ClockHost)
    (limits : ExecutionMachine.Limits)
    (base : RunLoopHooks (EntryState Os R P H D O Aff B Host) C MainMachine.Callback)
    (scheduler : C → ThreadStacks.LocalSchedulerHooks MiriMemoryKind
      (EntryUser Os R P H D O Aff B Host))
    (stop : EntryState Os R P H D O Aff B Host → Bool)
    (choices : List C) (initial : EntryState Os R P H D O Aff B Host) :
    StepResult (EntryState Os R P H D O Aff B Host) Unit := Id.run do
  let loop := EvalExecutable.fixedCorePrefixLoop configs limits base scheduler
  let rec execute (state : EntryState Os R P H D O Aff B Host) : List C →
      StepResult (EntryState Os R P H D O Aff B Host) Unit
    | [] => (state,.ok ())
    | choice::rest =>
      if stop state then (state,.ok ())
      else match RunLoop.iteration loop choice state with
        | (state,.error error) => (state,.error error)
        | (state,.ok ()) => execute state rest
  return execute initial choices

/-- A bounded ready-state source prefix without a caller-defined MIR step. -/
def runReadyConfiguredPrefix [DecidableEq Os]
    (configs : C → EvalExecutable.Core Os R P H D O Aff B Host C ClockHost)
    (limits : ExecutionMachine.Limits)
    (base : RunLoopHooks (EntryState Os R P H D O Aff B Host) C MainMachine.Callback)
    (scheduler : C → ThreadStacks.LocalSchedulerHooks MiriMemoryKind
      (EntryUser Os R P H D O Aff B Host))
    (choices : List C) (initial : EntryState Os R P H D O Aff B Host) :
    StepResult (EntryState Os R P H D O Aff B Host) Unit :=
  runReadyConfiguredPrefixUntil configs limits base scheduler (fun _ => false) choices initial

/-- Run real `late_init` and then a caller-bounded finite run-loop prefix.
Initialization errors return the exact state after their source prefix; a
successful prefix returns the actual state without claiming process completion. -/
def startAndRunPrefix [DecidableEq Os]
    (hooks : EvalBootstrap.Hooks U C O X F A Aff Payload AddressPayload Os)
    (configuration : EvalBootstrap.Configuration Os) (initialChoice : C)
    (base : RunLoopHooks (MainMachine.State U) C MainMachine.Callback)
    (scheduler : C → ThreadStacks.LocalSchedulerHooks MiriMemoryKind U)
    (choices : List C) (initial : MainMachine.State U) :
    StepResult (MainMachine.State U) Unit :=
  let (state,result) := MachineHooks.run
    (EvalBootstrap.createContextWithBytes hooks configuration initialChoice) initial
  match result with
  | .error error => (state,.error error)
  | .ok _ => EvalBootstrap.executePrefix hooks.main base scheduler choices state

/-- Executable form: late-init and every scheduled step share the fixed
EvalExecutable coreStep. The main hook is expected to come from
`EvalEntryMachine.mainFromExecution` (and may be assembled with
`bootstrapHooks` above); no caller-supplied RunLoop coreStep is used. -/
def runConfiguredPrefixUntil [DecidableEq Os]
    (main : MainMachine.Hooks
      (EvalExecutable.U Os R P H D O Aff B Host) C O ABI.ExternAbi
      (FnAbi TyId) (ArgAbi TyId) Aff P)
    (configs : C → EvalExecutable.Core Os R P H D O Aff B Host C ClockHost)
    (limits : ExecutionMachine.Limits)
    (base : RunLoopHooks (EntryState Os R P H D O Aff B Host) C MainMachine.Callback)
    (scheduler : C → ThreadStacks.LocalSchedulerHooks MiriMemoryKind
      (EntryUser Os R P H D O Aff B Host))
    (stop : EntryState Os R P H D O Aff B Host → Bool)
    (choices : List C) (initial : EntryState Os R P H D O Aff B Host) :
    StepResult (EntryState Os R P H D O Aff B Host) Unit := Id.run do
  let loop := EvalExecutable.loop configs limits main base scheduler
  -- A bounded source prefix may end on the exact MIR operation that empties
  -- the stack. The production loop would invoke its stack-empty callback in
  -- that same scheduler iteration. Observe `stop` immediately after the core
  -- operation so callers can inspect a genuine return boundary before that
  -- later callback reads or mutates main-thread state.
  let prefixCoreStep : C → EntryState Os R P H D O Aff B Host → StepResult
      (EntryState Os R P H D O Aff B Host) Bool := fun choice state =>
    match loop.coreStep choice state with
    | (after,.ok stepped) => if stop after then (after,.ok true) else (after,.ok stepped)
    | result => result
  let prefixLoop : RunLoopHooks (EntryState Os R P H D O Aff B Host) C MainMachine.Callback :=
    {loop with coreStep := prefixCoreStep}
  let rec execute (state : EntryState Os R P H D O Aff B Host) : List C →
      StepResult (EntryState Os R P H D O Aff B Host) Unit
    | [] => (state,.ok ())
    | choice::rest =>
      if stop state then (state,.ok ())
      else match RunLoop.iteration prefixLoop choice state with
        | (state,.error error) => (state,.error error)
        | (state,.ok ()) => execute state rest
  return execute initial choices

/-- Run a finite list of scheduler choices from an already initialized source
state. This is useful for observing an exact call/return prefix without asking
the main callback to run after the target frame has returned. -/
def runConfiguredPrefix [DecidableEq Os]
    (main : MainMachine.Hooks
      (EvalExecutable.U Os R P H D O Aff B Host) C O ABI.ExternAbi
      (FnAbi TyId) (ArgAbi TyId) Aff P)
    (configs : C → EvalExecutable.Core Os R P H D O Aff B Host C ClockHost)
    (limits : ExecutionMachine.Limits)
    (base : RunLoopHooks (EntryState Os R P H D O Aff B Host) C MainMachine.Callback)
    (scheduler : C → ThreadStacks.LocalSchedulerHooks MiriMemoryKind
      (EntryUser Os R P H D O Aff B Host))
    (choices : List C) (initial : EntryState Os R P H D O Aff B Host) :
    StepResult (EntryState Os R P H D O Aff B Host) Unit :=
  runConfiguredPrefixUntil main configs limits base scheduler (fun _ => false) choices initial

def startAndRunConfiguredPrefixUntil [DecidableEq Os]
    (hooks : EvalBootstrap.Hooks
      (EvalExecutable.U Os R P H D O Aff B Host) C O ABI.ExternAbi
      (FnAbi TyId) (ArgAbi TyId) Aff P AddressPayload Os)
    (configuration : EvalBootstrap.Configuration Os) (initialChoice : C)
    (configs : C → EvalExecutable.Core Os R P H D O Aff B Host C ClockHost)
    (limits : ExecutionMachine.Limits)
    (base : RunLoopHooks (EntryState Os R P H D O Aff B Host) C MainMachine.Callback)
    (scheduler : C → ThreadStacks.LocalSchedulerHooks MiriMemoryKind
      (EntryUser Os R P H D O Aff B Host))
    (stop : EntryState Os R P H D O Aff B Host → Bool)
    (choices : List C) (initial : EntryState Os R P H D O Aff B Host) :
    StepResult (EntryState Os R P H D O Aff B Host) Unit := Id.run do
  let (state,result) := MachineHooks.run
    (EvalBootstrap.createContextWithBytes hooks configuration initialChoice) initial
  match result with
  | .error error => return (state,.error error)
  | .ok _ =>
    let main : MainMachine.Hooks (EvalExecutable.U Os R P H D O Aff B Host)
        C O ABI.ExternAbi (FnAbi TyId) (ArgAbi TyId) Aff P := hooks.main
    return runConfiguredPrefixUntil main configs limits base scheduler stop choices state

def startFromExecutionPrefix [DecidableEq Os]
    (compiler : CompilerProviders.Prepared)
    (execution : EvalExecutable.Core Os R P H D O Aff B Host C ClockHost)
    (configs : C → EvalExecutable.Core Os R P H D O Aff B Host C ClockHost)
    (limits : ExecutionMachine.Limits)
    (deallocationError : MemoryLifecycleError → StepError)
    (deallocate : Pointer (Option Provenance) → Option (Size × Align) →
      MemoryKind MiriMemoryKind → MachineHooks.M MiriMemoryKind
        (EvalEntryMachine.InnerUser Os R P H D O Aff B Host) Unit)
    (choice : C) (layout : EvalEntryMachine.Layouts)
    (spans : AllocationDriver.SpanHooks) (platform : TlsPlatform)
    (format : ConstructorBinaryFormat)
    (externStatic : DefId → MachineHooks.M MiriMemoryKind
      (EntryOuter Os R P H D O Aff B Host) (Pointer Provenance))
    (evalWindows : String → String → MachineHooks.M MiriMemoryKind
      (EntryOuter Os R P H D O Aff B Host) (Scalar Provenance))
    (arguments : EntryArguments.Hooks MiriMemoryKind
      (ThreadStacks.Storage (EntryUser Os R P H D O Aff B Host))
      (ValidityMachine.Control (ThreadStacks.Storage
        (W Os R P H D O Aff B Host))) P C)
    (environment : EnvVars.Hooks (Option Provenance) Os
      (EntryState Os R P H D O Aff B Host))
    (externStatics : ExternStatic.InitHooks (EntryState Os R P H D O Aff B Host))
    (symbols : IntrinsicSymbolsMachine.Access
      (ThreadStacks.Storage (EntryUser Os R P H D O Aff B Host)))
    (image : AllocationImage.Imported)
    (vtableRuntime : VTableMachine.Hooks MiriMemoryKind
      (ThreadStacks.Storage (EntryUser Os R P H D O Aff B Host)) O)
    (configuration : EvalBootstrap.Configuration Os)
    (base : RunLoopHooks (EntryState Os R P H D O Aff B Host) C MainMachine.Callback)
    (scheduler : C → ThreadStacks.LocalSchedulerHooks MiriMemoryKind
      (EntryUser Os R P H D O Aff B Host))
    (stop : EntryState Os R P H D O Aff B Host → Bool)
    (choices : List C)
    (initial : EntryState Os R P H D O Aff B Host) :
    StepResult (EntryState Os R P H D O Aff B Host) Unit :=
  match EvalEntryMachine.mainFromExecution compiler execution limits deallocationError deallocate
      choice layout spans platform format externStatic evalWindows initial with
  | .error error => (initial,.error error)
  | .ok main =>
    let main : MainMachine.Hooks (EvalExecutable.U Os R P H D O Aff B Host)
        C O ABI.ExternAbi (FnAbi TyId) (ArgAbi TyId) Aff P := main
    let hooks : EvalBootstrap.Hooks (EvalExecutable.U Os R P H D O Aff B Host)
        C O ABI.ExternAbi (FnAbi TyId) (ArgAbi TyId) Aff P
        (ValidityMachine.Control (ThreadStacks.Storage
          (W Os R P H D O Aff B Host))) Os :=
      bootstrapHooks arguments main environment externStatics compiler symbols image vtableRuntime
    startAndRunConfiguredPrefixUntil hooks configuration choice configs
      limits base scheduler stop choices initial

end Miri.Input.EvalRuntimeConstruction
