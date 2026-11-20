import Miri.Input.EvalWindowsConfigurationCore
import Miri.Input.EvalWindowsIoSourceConstruction
import Miri.Input.EvalWindowsCallbackAssembly
import Miri.Input.EvalWindowsCallDispatchConstruction
import Miri.Input.EvalWindowsSyncTimeConstruction
import Miri.Input.CompilerNamedShimAbi
import Miri.Interpreter.TimeShimDispatch
import Miri.Interpreter.ExecutionStateTransport
import Miri.Interpreter.ExecutionForeignTransport
import Miri.Input.EvalRuntimeConstruction

/-! Attach the Main-dependent Windows source capabilities to the same
configuration, Main hooks, source host leaves, and live state. No completed
Windows guest dispatch dictionaries enter this connector. -/
namespace Miri.Input.EvalWindowsConnectedSourceAssembly
open Miri.ABI Miri.Memory Miri.MIR Miri.Interpreter

abbrev Other Raw Listener TcpStream Error :=
  EvalWindowsCallDispatchConstruction.Other Raw Listener TcpStream Error
abbrev Host Poll Instant System H D Raw Listener TcpStream Error Native Profiler :=
  EvalWindowsCallDispatchConstruction.Host Poll Instant System H D Raw Listener TcpStream Error Native Profiler
abbrev State Os R H D Aff B Poll Instant System Native Profiler Raw Listener TcpStream Error :=
  EvalWindowsCallDispatchConstruction.State Os R H D Aff B Poll Instant System Native Profiler Raw Listener TcpStream Error
abbrev CoreState Os R H D Aff B Poll Instant System Native Profiler Raw Listener TcpStream Error :=
  EvalWindowsCallDispatchConstruction.CoreState Os R H D Aff B Poll Instant System Native Profiler Raw Listener TcpStream Error

private def lift (value : Except StepError A) : EStateM StepError S A :=
  match value with | .ok result => pure result | .error error => throw error

private def outerAtomicAccess
    (hooks : AtomicAccessHooks Provenance
      (MachineHooks.State MiriMemoryKind (ExecutionStateTransport.Inner U)) C V) :
    AtomicAccessHooks Provenance
      (MachineHooks.State MiriMemoryKind (ExecutionStateTransport.Outer U)) C V := {
  target := hooks.target
  getGlobal := fun state => hooks.getGlobal (ExecutionStateTransport.inward state)
  setGlobal := fun state value => ExecutionStateTransport.outward
    (hooks.setGlobal (ExecutionStateTransport.inward state) value)
  threads := fun state => hooks.threads (ExecutionStateTransport.inward state)
  getAtomic := fun state id => hooks.getAtomic (ExecutionStateTransport.inward state) id
  setAtomic := fun id value => ExecutionStateTransport.action (hooks.setAtomic id value)

  placeLayout := hooks.placeLayout
  placePointer := hooks.placePointer
  physicalRead := fun choice place => ExecutionStateTransport.action (hooks.physicalRead choice place)
  physicalWrite := fun choice value place => ExecutionStateTransport.action
    (hooks.physicalWrite choice value place)
  ghostRead := fun choice place => ExecutionStateTransport.action (hooks.ghostRead choice place)
  checkPointerAlign := fun choice pointer align => ExecutionStateTransport.action
    (hooks.checkPointerAlign choice pointer align)
  resolveAllocation := fun choice pointer => ExecutionStateTransport.action
    (hooks.resolveAllocation choice pointer)
  mutability := fun choice id => ExecutionStateTransport.action (hooks.mutability choice id)
  scalarOps := ExecutionStateTransport.scalar hooks.scalarOps
  loadChoiceRank := fun choice rank => ExecutionStateTransport.action (hooks.loadChoiceRank choice rank)
  weakPolicy := hooks.weakPolicy
  weakSuccessChoice := fun choice => ExecutionStateTransport.action (hooks.weakSuccessChoice choice)
  diagnostic := fun choice diagnostic => ExecutionStateTransport.action
    (hooks.diagnostic choice diagnostic)
  classifyDispatchError := hooks.classifyDispatchError
  classifyGlobalError := hooks.classifyGlobalError }

private def errorsToInner
    (errors : IoError.Hooks
      (State Os R H D Aff B Poll Instant System Native Profiler Raw Listener TcpStream Error)
      Error) : IoError.Hooks
      (CoreState Os R H D Aff B Poll Instant System Native Profiler Raw Listener TcpStream Error)
      Error := {
  family := errors.family
  os := errors.os
  hostUnix := errors.hostUnix
  hostErrno := fun name => ExecutionStateTransport.reverseAction (errors.hostErrno name)
  libc := fun name => ExecutionStateTransport.reverseAction (errors.libc name)
  windows := fun name => ExecutionStateTransport.reverseAction (errors.windows name)
  scalarI32 := fun value => ExecutionStateTransport.reverseAction (errors.scalarI32 value)
  scalarU32 := fun value => ExecutionStateTransport.reverseAction (errors.scalarU32 value)
  hostFromRaw := fun value => ExecutionStateTransport.reverseAction (errors.hostFromRaw value)
  hostFromKind := fun value => ExecutionStateTransport.reverseAction (errors.hostFromKind value)
  getLastErrorPlace := ExecutionStateTransport.reverseAction errors.getLastErrorPlace
  setLastErrorPlace := fun place => ExecutionStateTransport.reverseAction (errors.setLastErrorPlace place)
  allocateU32Machine := ExecutionStateTransport.reverseAction errors.allocateU32Machine
  writeScalar := fun value place => ExecutionStateTransport.reverseAction (errors.writeScalar value place)
  readScalar := fun place => ExecutionStateTransport.reverseAction (errors.readScalar place)
  writeInt := fun value place => ExecutionStateTransport.reverseAction (errors.writeInt value place) }

private def timeDispatch
    [DecidableEq Os]
    (p : CompilerProviders.Prepared)
    (callbacks : EvalWindowsCallbackAssembly.Product Os R H D Aff B Poll Instant
      System Native Profiler Raw Listener TcpStream Error C ABI.ExternAbi
      (FnAbi TyId) (ArgAbi TyId))
    (context : EvalWindowsConfigurationCore.Context Os R H D B Poll Instant System
      Native Profiler C Raw Listener TcpStream Error Meta Path callbacks.Zone callbacks.Timestamp)
    (assembly : EvalWindowsCallDispatchConstruction.Assembly Os R H D Aff B Poll Instant System
      Native Profiler Raw Listener TcpStream Error C Meta Path callbacks.Zone callbacks.Timestamp)
    :
    Except StepError (TimeShimDispatch.Hooks
      (State Os R H D Aff B Poll Instant System Native Profiler Raw Listener TcpStream Error)
      Instant System callbacks.Zone callbacks.Timestamp) := do
  let time := callbacks.time
  pure {
    time
    expectedAbi := fun name _ => CompilerNamedShimAbi.query p.namedAbi name
    systemConvention := (CompilerNamedShimAbi.query p.namedAbi "GetSystemTimeAsFileTime").map (·.conv)
    argumentCompat := fun caller callee => ExecutionStateTransport.action do
      let compiler : ExecutionCallLeaves.Compiler
          (CoreState Os R H D Aff B Poll Instant System Native Profiler Raw Listener TcpStream Error)
          C ABI.ExternAbi :=
        CompilerCallConstruction.compiler p assembly.compatibilityBudget
      compiler.checkArgumentCompat context.choice caller callee
    checkSymbolClash := fun name =>
      ExecutionStateTransport.action (assembly.foreign.checkSymbolClash name)
    transmute := fun operand target => do
      let projection ← assembly.sourceSeed.place.projection context.choice
      match operand.transmute projection target
          |>.mapError IntrinsicVectorMachine.projectionError with
      | .ok value => pure value
      | .error error => throw error }

set_option autoImplicit false in
def connectFromSource
    {Os R H D B Poll Instant System Native Profiler C Raw Listener TcpStream Error
      ErrorHost Meta Path AddrIter Zone Timestamp : Type}
    [DecidableEq Os] [DecidableEq MiriMemoryKind]
    (p : CompilerProviders.Prepared)
    (options : EvalConfigurationCore.Options)
    (sourceLeaves : EvalConfigurationCore.SourceLeaves Os R EvalSyncPayload.Payload H D
      CpuAffinity.Mask B Poll Instant System Native Profiler Raw Listener TcpStream Error
      ErrorHost Meta Path Miri.MIR.Place C Instant CallInstance AddrIter)
    (main : MainMachine.Hooks
      (EvalWindowsFileConstruction.Payload Os R EvalSyncPayload.Payload H D
        (Other Raw Listener TcpStream Error) CpuAffinity.Mask B
        (Host Poll Instant System H D Raw Listener TcpStream Error Native Profiler))
      C (Other Raw Listener TcpStream Error) ABI.ExternAbi (FnAbi TyId) (ArgAbi TyId)
      CpuAffinity.Mask ProgramExitPoll)
    (callbacks : EvalWindowsCallbackAssembly.Product Os R H D CpuAffinity.Mask B Poll
      Instant System Native Profiler Raw Listener TcpStream Error C ABI.ExternAbi
      (FnAbi TyId) (ArgAbi TyId))
    (pathToOs : Path → Os)
    (outerUnwind : Unwind.Hooks MiriMemoryKind
      (ThreadStacks.Storage
        (EvalWindowsFileConstruction.Payload Os R EvalSyncPayload.Payload H D
          (Other Raw Listener TcpStream Error) CpuAffinity.Mask B
          (Host Poll Instant System H D Raw Listener TcpStream Error Native Profiler)))
      C (Other Raw Listener TcpStream Error))
    (context : EvalWindowsConfigurationCore.Context Os R H D B Poll Instant System
      Native Profiler C Raw Listener TcpStream Error Meta Path callbacks.Zone callbacks.Timestamp)
    (assembly : EvalWindowsConfigurationCore.Assembly Os R H D CpuAffinity.Mask B Poll
      Instant System Native Profiler Raw Listener TcpStream Error C Meta Path
      callbacks.Zone callbacks.Timestamp) :
    EStateM StepError
      (CoreState Os R H D CpuAffinity.Mask B Poll Instant System Native Profiler
        Raw Listener TcpStream Error)
      (EvalWindowsConfigurationCore.Assembly Os R H D CpuAffinity.Mask B Poll Instant
        System Native Profiler Raw Listener TcpStream Error C Meta Path
        callbacks.Zone callbacks.Timestamp) := do
  let host := sourceLeaves.foreignSource.host
  let io ← lift (EvalWindowsIoSourceConstruction.fromInnerSource p assembly.sourceSeed main
    assembly.errors host.openFiles host.hostFiles host.fileResources host.fileLocks
    host.positional host.filesystem sourceLeaves.foreignSource.fileReferenceBudget
    sourceLeaves.foreignSource.watcherReferenceBudget sourceLeaves.hostConfiguration.hostUsizeBits
    (UInt64.ofNat (2 ^ (context.validityAccess.runtime.pointerSize.bytes.toNat * 8 - 1) - 1))
    (UInt64.ofNat (2 ^ (sourceLeaves.hostConfiguration.hostUsizeBits - 1) - 1))
    pathToOs assembly.sourceSeed.memory.pointers.arithmetic)
  let time ← lift (timeDispatch p callbacks context assembly)
  let errors : IoError.Hooks
      (State Os R H D CpuAffinity.Mask B Poll Instant System Native Profiler
        Raw Listener TcpStream Error) Error := assembly.errors
  let outerProjection := EvalRuntimeConstruction.outerProjection context.projection
  let outerAtomic := outerAtomicAccess context.atomics
  let components ← lift (EvalWindowsCallDispatchConstruction.connectComponents p assembly main io.fileRegistry io.readiness
    io.sharedOpen io.prepareDirectory io.otherMetadata callbacks.time io.hostFiles io.checkPointerAccess
    outerProjection (fun error => .invalidProgram s!"Windows thread source error: {reprStr error}"))
  let sync ← lift (EvalWindowsSyncTimeConstruction.syncFromSource p main callbacks.objects
        outerAtomic outerProjection context.choice callbacks.deadline
        errors assembly.compatibilityBudget)
  let assembly := {components with
    time := some time
    sync := some sync}
  let currentExe := do
    match host.filesystem with
    | none => throw (.unsupported "Windows current-executable path capability is unavailable")
    | some filesystem =>
      return ((← ExecutionStateTransport.action filesystem.effects.currentExe).map pathToOs)
  let platformHost : EvalWindowsPlatformConstruction.HostEffects
      (EvalWindowsCallDispatchConstruction.State Os R H D CpuAffinity.Mask B Poll Instant System Native Profiler
        Raw Listener TcpStream Error) Os Error := {
    currentExe
    hostErrorDisplay := fun error => ExecutionStateTransport.action
      (host.unixConfig.hostErrorDisplay error)
    unknownMessageDisplay := fun scalar => ExecutionStateTransport.action
      (host.unixConfig.unknownErrorDisplay scalar)
    pageSize := host.unixConfig.pageSize
    numCpus := host.unixConfig.numCpus }
  let platform ← lift (EvalWindowsCallDispatchConstruction.connectPlatformFromSource p assembly main context.extras
    sourceLeaves.spans SourceOther.windowsSymbol outerProjection platformHost outerUnwind)
  pure platform

end Miri.Input.EvalWindowsConnectedSourceAssembly
