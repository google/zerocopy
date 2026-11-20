import Miri.Input.CompilerCallConstruction
import Miri.Input.CompilerForeignSymbols
import Miri.Input.CompilerNamedFields
import Miri.Input.CompilerNamedShimAbi
import Miri.Input.CompilerProviders
import Miri.Input.CompilerWindowsConstants
import Miri.Input.CompilerWindowsTypeLayouts
import Miri.Input.EvalCoreMachine
import Miri.Input.EvalHostRuntimeConstruction
import Miri.Input.EvalStartupAssembly
import Miri.Input.EvalWindowsEnvironmentConstruction
import Miri.Interpreter.ExecutionStateTransport
import Miri.Interpreter.MainMachine
import Miri.Interpreter.PointerPlaceMachine
import Miri.Interpreter.RawMemoryMachine
import Miri.Interpreter.ReallocationDriver
import Miri.Interpreter.Unwind
import Miri.Interpreter.WindowsPlatformDispatch

/-! Source construction for the remaining Windows platform shims. Compiler
ABI/layout, guest reads and writes, allocation identity, dynamic function
identity, process exit and unwind are attached to the same prepared target and
Main state. Host path and error text plus configured machine facts remain
explicit leaves; the command line comes from the initialized Main entry root. -/
namespace Miri.Input.EvalWindowsPlatformConstruction
open Miri.ABI Miri.Memory Miri.MIR Miri.Interpreter

abbrev Payload Os R P H D O Aff B Host := EvalRuntimeConstruction.EntryUser Os R P H D O Aff B Host
abbrev State Os R P H D O Aff B Host := EvalStartupAssembly.State Os R P H D O Aff B Host
abbrev Inner Os R P H D O Aff B Host := EvalStartupAssembly.InnerControl Os R P H D O Aff B Host
abbrev InnerState Os R P H D O Aff B Host := EvalStartupAssembly.InnerState Os R P H D O Aff B Host
abbrev M S A := EStateM StepError S A

set_option autoImplicit false in
structure HostEffects (S Os E : Type) where
  currentExe : M S (Option Os)
  hostErrorDisplay : IoError.HostError E → M S Os
  unknownMessageDisplay : Scalar Provenance → M S Os
  pageSize : UInt64
  numCpus : UInt32

private def lift (value : Except StepError A) : M S A :=
  match value with | .ok result => pure result | .error error => throw error

private def namedLayout (p : CompilerProviders.Prepared) (name : String) : M S LocalLayout := do
  match CompilerWindowsTypeLayouts.layout p.runtime name with
  | .ok value => pure ⟨value.ty,value.layout⟩
  | .error reason => throw (.unsupported s!"compiler Windows layout `{name}`: {reason}")

private def field (p : CompilerProviders.Prepared)
    (projection : PlaceProjectionHooks Provenance S C MachineHooks.FrameExtra)
    (choice : C) (parent : MPlaceTy Provenance) (name : String) : M S (MPlaceTy Provenance) := do
  let index ← match CompilerNamedFields.fieldIndex p.runtime parent.layout name with
    | .ok index => pure index
    | .error error => throw error
  let projected ← PlaceDynamic.field projection choice
    ⟨.memory parent.mplace,parent.layout⟩ index
  match projected.ref with
  | .memory memory => pure ⟨memory,projected.layout⟩
  | .local .. => throw (.invalidProgram "Windows SYSTEM_INFO field projected to a local")

private def sourceKind : WindowsPlatform.HeapKind → MiriMemoryKind
  | .heap => .winHeap
  | .local => .winLocal

/-- Preserve the operation-local span cut from the common source allocator
while retaining the already-bound allocation tail and its single extras-init
pass. -/
private def allocationForKind
    (memory : EvalWindowsEnvironmentConstruction.Memory Os R P H D O Aff B Host C)
    (spans : AllocationDriver.SpanHooks) (kind : MiriMemoryKind) :
    M (InnerState Os R P H D O Aff B Host)
      (PlaceMachine.AllocationConfig MiriMemoryKind
        (PointerMachine.User (Inner Os R P H D O Aff B Host))) := do
  let context ← get
  let config := memory.allocation
  let tail := fun id size align => do
    config.allocationTail id size align
    if kind.shouldSaveAllocationSpan then
      let machine ← get
      let span ← match AllocationDriver.currentUserRelevantSpan spans {context with machine} with
        | .ok span state => set state.machine; pure span
        | .error error state => set state.machine; throw error
      modify fun state => {state with allocationSpans :=
        (state.allocationSpans.filter fun entry => entry.1 != id).push (id,span,none)}
  pure {config with allocationTail := tail}

def fromSource [DecidableEq MiriMemoryKind]
    {Os R P H D O Aff B Host C Error F : Type}
    (p : CompilerProviders.Prepared)
    (main : MainMachine.Hooks (Payload Os R P H D O Aff B Host) C O ABI.ExternAbi
      (FnAbi TyId) (ArgAbi TyId) Aff ProgramExitPoll)
    (environment : WindowsEnvironment.Hooks (State Os R P H D O Aff B Host)
      Os Error EnvVars.Kind)
    (memory : EvalWindowsEnvironmentConstruction.Memory Os R P H D O Aff B Host C)
    (extras : MemoryExtras.Hooks MiriMemoryKind
      (PointerMachine.User (Inner Os R P H D O Aff B Host))
      P)
    (spans : AllocationDriver.SpanHooks)
    (handles : WindowsHandles.Hooks (State Os R P H D O Aff B Host) F)
    (embed : WindowsPlatform.DynamicSymbol → O)
    (place : PlaceHooks Provenance (State Os R P H D O Aff B Host)
      C MachineHooks.FrameExtra)
    (projection : PlaceProjectionHooks Provenance
      (State Os R P H D O Aff B Host) C MachineHooks.FrameExtra)
    (choice : C) (host : HostEffects (State Os R P H D O Aff B Host) Os Error)
    (startExit : Int32 → M (State Os R P H D O Aff B Host) Unit)
    (unwind : Unwind.Hooks MiriMemoryKind
      (ThreadStacks.Storage (Payload Os R P H D O Aff B Host)) C O)
    (compatibilityBudget : Nat) :
    Except StepError (WindowsPlatformDispatch.Hooks
      (State Os R P H D O Aff B Host) Os Error EnvVars.Kind F) := do
  let target ← p.externStatics.targetFacts |>.mapError StepError.unsupported
  unless target.os == "windows" || target.families.contains "windows" do
    throw (.invalidProgram s!"Windows platform source requested for `{target.os}`")
  unless environment.env.family == .windows && environment.process.family == .windows do
    throw (.invalidProgram "Windows platform environment has a mismatched target family")
  let symbols ← p.foreignSymbols
    |>.mapError StepError.unsupported
  let calls := CompilerCallConstruction.compiler p compatibilityBudget
  let access := main.access
  let readScalar := fun (operand : OpTy Provenance) => do
    let immediate ← PlaceMachine.readImmediate access operand
    lift (immediate.imm.toScalar |>.mapError ScalarOps.immediateError)
  let readPointer := fun operand => do
    lift ((← readScalar operand).toPointer access.runtime.base
      |>.mapError ScalarOps.scalarError)
  let readUsize := fun operand => do
    lift ((← readScalar operand).toTargetUsize access.runtime.pointerSize
      |>.mapError ScalarOps.scalarError)
  let writeScalar := fun (value : Scalar Provenance)
      (destination : MPlaceTy Provenance) =>
    writePlaceImmediate place choice (.scalar value)
      ⟨.memory destination.mplace,destination.layout⟩
  let writeInt := fun (value : Int) (destination : MPlaceTy Provenance) => do
    let scalar ← lift (Scalar.fromInt value destination.layout.layout.size
      |>.mapError ScalarOps.scalarError)
    writeScalar scalar destination
  let writePointer := fun (value : Pointer (Option Provenance))
      (destination : MPlaceTy Provenance) => do
    let scalar ← lift (Scalar.fromMaybePointer access.runtime.base value
      |>.mapError ScalarOps.scalarError)
    writeScalar scalar destination
  let transmute := fun (operand : OpTy Provenance)
      (layout : TyAndLayout TyId) => do
    let placeHooks ← place.projection choice
    match operand.transmute placeHooks layout |>.mapError
        IntrinsicVectorMachine.projectionError with
    | .ok value => pure value
    | .error error => throw error
  let allocation : WindowsPlatform.Hooks (State Os R P H D O Aff B Host)
      Os Error EnvVars.Kind F := {
    environment
    handles
    pointerSize := access.runtime.pointerSize
    readUsize
    readScalar
    allocate := fun size align init heapKind => ExecutionStateTransport.action do
      let config ← allocationForKind memory spans (sourceKind heapKind)
      let pointer ← ReallocationDriver.allocateConfigured config size align
        (.machine (sourceKind heapKind)) init
      return pointer.withOptionalProvenance
    deallocate := fun pointer heapKind => ExecutionStateTransport.action
      (memory.deallocate pointer none (.machine (sourceKind heapKind)))
    reallocate := fun pointer size align heapKind => ExecutionStateTransport.action do
      let kind := sourceKind heapKind
      let config ← allocationForKind memory spans kind
      let pointer ← ReallocationDriver.reallocateConfiguredFrom memory.access extras
        memory.pointers.arithmetic config memory.deallocate pointer none size align
        (.machine kind) .Uninit
      return pointer.withOptionalProvenance
    nullPointer := Pointer.null
    functionPointer := fun symbol => do
      let value ← FunctionPointers.functionPointer main.functions (.Other (embed symbol))
      pure value.withOptionalProvenance
    readCString := environment.strings.readCString
    commandLine := do
      let some pointer := (main.entry (← get).machine.user.user).commandLine |
        return none
      return some pointer.withOptionalProvenance
    currentExe := host.currentExe
    derefSystemInfo := fun operand => do
      let pointer ← readPointer operand
      let layout ← namedLayout p "SYSTEM_INFO"
      let alignment : PointerPlaceMachine.AlignmentContext
          (ThreadStacks.Storage (Payload Os R P H D O Aff B Host)) := {
        policy := fun storage => storage.user.payload.alignment
        promises := fun storage => storage.user.symbolicAlignment }
      let mismatch ← PointerPlaceMachine.misalignmentWith access alignment pointer layout.layout.align.abi
      pure ⟨⟨pointer,.none,mismatch⟩,layout⟩
    derefPointer := fun operand => do
      let pointer ← readPointer operand
      let alignment : PointerPlaceMachine.AlignmentContext
          (ThreadStacks.Storage (Payload Os R P H D O Aff B Host)) := {
        policy := fun storage => storage.user.payload.alignment
        promises := fun storage => storage.user.symbolicAlignment }
      let _ ← PointerPlaceMachine.misalignmentWith access alignment pointer
        operand.layout.layout.align.abi
      pure ()
    projectNamed := fun parent name => field p projection choice parent name
    zeroBytes := fun pointer count => ExecutionStateTransport.action
      (RawMemoryMachine.writeRepeatedByte memory.access memory.pointers.arithmetic pointer 0 count)
    writeInt
    hostErrorDisplay := host.hostErrorDisplay
    unknownMessageDisplay := host.unknownMessageDisplay
    pageSize := host.pageSize
    numCpus := host.numCpus }
  let expectedAbi := fun name request => do
    let some operation := WindowsPlatformDispatch.parse name |
      throw (.unsupported s!"Windows platform ABI requested for unknown `{name}`")
    let expected := WindowsPlatformDispatch.signature operation
    unless expected.args == request.args && expected.ret == request.ret do
      throw (.invalidProgram s!"Windows platform ABI recipe disagrees with `{name}`")
    CompilerNamedShimAbi.query p.namedAbi name
  pure {
    platform := allocation
    systemConvention := do return (← CompilerNamedShimAbi.query p.namedAbi "HeapAlloc").conv
    expectedAbi
    argumentCompat := calls.checkArgumentCompat choice
    checkSymbolClash := fun name =>
      match CompilerForeignSymbols.checkSymbolClash symbols name with
      | .ok () => pure () | .error error => throw error
    transmute
    writeScalar
    writeInt
    writePointer
    startExit
    targetEnv := target.env
    handleStartUnwind := Unwind.handleStartUnwind unwind choice }

end Miri.Input.EvalWindowsPlatformConstruction
