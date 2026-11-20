import Miri.Input.EvalForeignConstruction
import Miri.Input.EvalWindowsSourceConstruction
import Miri.Input.EvalWindowsIoErrorConstruction
import Miri.Input.CompilerForeignSymbols
import Miri.Input.CompilerProviders
import Miri.Input.EvalCoreMachine
import Miri.Input.EvalHostRuntimeConstruction
import Miri.Input.EvalSyncPayload
import Miri.Input.EvalSocketStorage
import Miri.Input.EvalSyncMachine
import Miri.Input.EvalOwnedIoMachine
import Miri.Input.EvalWindowsSyncTimeConstruction
import Miri.Input.EvalTimeConstruction
import Miri.Input.EvalTypedSyncMachine
import Miri.Interpreter.TimeShimDispatch
import Miri.Interpreter.WindowsSyncDispatch
import Miri.Concurrency.TypedSyncRuntime
import Miri.Interpreter.DeadlineMachine
import Miri.Interpreter.IntrinsicAtomic
import Miri.Input.CompilerCallConstruction
import Miri.Input.CompilerNamedShimAbi
import Miri.Interpreter.Math.Dispatch
import Miri.Interpreter.ForeignItems
import Miri.Interpreter.MainMachine
import Miri.Interpreter.ExecutionForeignTransport
import Miri.Interpreter.ExecutionMemoryTransport
import Miri.Input.EvalWindowsRandomConstruction
import Miri.Input.EvalWindowsStdOnlyConstruction
import Miri.Input.EvalWindowsPlatformConstruction
import Miri.Input.EvalWindowsCallbackSourceConstruction

/-! Windows-specific source call assembly. It constructs Common and Windows
environment/error state from compiler facts and the live machine providers;
Unix host configuration and Unix callback records are deliberately absent.
Windows operation components can then be attached against this exact Main
state by `connectComponents`. -/
namespace Miri.Input.EvalWindowsCallDispatchConstruction
open Miri.ABI Miri.Memory Miri.MIR Miri.Interpreter

private def lift {S : Type} (result : Except StepError A) : EStateM StepError S A :=
  match result with | .ok value => pure value | .error error => throw error

abbrev Other Raw Listener TcpStream Error :=
  EvalSocketStorage.Other Raw Listener TcpStream Error
abbrev Host Poll Instant System H D Raw Listener TcpStream Error Native Profiler :=
  HostRuntime.Storage Poll Instant System H D
    (Other Raw Listener TcpStream Error) Native Profiler
abbrev Payload := EvalSyncPayload.Payload
abbrev State Os R H D Aff B Poll Instant System Native Profiler Raw Listener TcpStream Error :=
  EvalWindowsFileConstruction.State Os R Payload H D
    (Other Raw Listener TcpStream Error) Aff B
    (Host Poll Instant System H D Raw Listener TcpStream Error Native Profiler)
abbrev CoreState Os R H D Aff B Poll Instant System Native Profiler Raw Listener TcpStream Error :=
  EvalForeignConstruction.State Os R Payload H D
    (Other Raw Listener TcpStream Error) Aff B
    (Host Poll Instant System H D Raw Listener TcpStream Error Native Profiler)

private def ioErrorsToInner
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

set_option autoImplicit false in
structure SourceSeed
    (Os R H D Aff B Poll Instant System Native Profiler Raw Listener TcpStream Error
      C : Type) where
  osHost : EvalHostRuntimeConstruction.OsHostEffects Os
  environmentHost : EvalHostRuntimeConstruction.EnvironmentHostEffects
    (EvalWindowsEnvironmentConstruction.InnerControl Os R Payload H D
      (Other Raw Listener TcpStream Error) Aff B
      (Host Poll Instant System H D Raw Listener TcpStream Error Native Profiler))
  environmentHostConfig : EvalWindowsEnvironmentConstruction.HostEffects
    (State Os R H D Aff B Poll Instant System Native Profiler Raw Listener TcpStream Error)
    Os Error
  ioHost : EvalUnixConstruction.IoHostEffects
    (State Os R H D Aff B Poll Instant System Native Profiler Raw Listener TcpStream Error) Error
  memory : EvalWindowsEnvironmentConstruction.Memory Os R Payload H D
    (Other Raw Listener TcpStream Error) Aff B
    (Host Poll Instant System H D Raw Listener TcpStream Error Native Profiler) C
  place : PlaceHooks Provenance
    (State Os R H D Aff B Poll Instant System Native Profiler Raw Listener TcpStream Error)
    C MachineHooks.FrameExtra
  choice : C
  compatibilityBudget : Nat
  userRelevantCrates : Array Nat

set_option autoImplicit false in
structure Assembly
    (Os R H D Aff B Poll Instant System Native Profiler Raw Listener TcpStream Error
      C Meta Path Zone Timestamp : Type) where
  common : EvalForeignConstruction.Common
    (CoreState Os R H D Aff B Poll Instant System Native Profiler Raw Listener TcpStream Error)
  foreign : ForeignItems.Core Provenance
    (CoreState Os R H D Aff B Poll Instant System Native Profiler Raw Listener TcpStream Error)
    (RuntimePlace Provenance) (RuntimePlace Provenance)
    (Pointer (Option Provenance)) LoadedBody CallInstance
  environment : WindowsEnvironmentDispatch.Hooks
    (State Os R H D Aff B Poll Instant System Native Profiler Raw Listener TcpStream Error)
    Os Error EnvVars.Kind
  errors : IoError.Hooks
    (State Os R H D Aff B Poll Instant System Native Profiler Raw Listener TcpStream Error)
    Error
  osHost : EvalHostRuntimeConstruction.OsHostEffects Os
  environmentHost : EvalHostRuntimeConstruction.EnvironmentHostEffects
    (EvalWindowsEnvironmentConstruction.InnerControl Os R Payload H D
      (Other Raw Listener TcpStream Error) Aff B
      (Host Poll Instant System H D Raw Listener TcpStream Error Native Profiler))
  environmentHostConfig : EvalWindowsEnvironmentConstruction.HostEffects
    (State Os R H D Aff B Poll Instant System Native Profiler Raw Listener TcpStream Error)
    Os Error
  place : PlaceHooks Provenance
    (State Os R H D Aff B Poll Instant System Native Profiler Raw Listener TcpStream Error)
    C MachineHooks.FrameExtra
  choice : C
  compatibilityBudget : Nat
  userRelevantCrates : Array Nat
  sourceSeed : SourceSeed Os R H D Aff B Poll Instant System Native Profiler
    Raw Listener TcpStream Error C
  memory : EvalWindowsEnvironmentConstruction.Memory Os R Payload H D
    (Other Raw Listener TcpStream Error) Aff B
    (Host Poll Instant System H D Raw Listener TcpStream Error Native Profiler) C
  components : Option (EvalWindowsSourceConstruction.Components Os R Payload H D
    (Other Raw Listener TcpStream Error) Aff B
    (Host Poll Instant System H D Raw Listener TcpStream Error Native Profiler)
    C Error Meta Path System)
  time : Option (TimeShimDispatch.Hooks
    (State Os R H D Aff B Poll Instant System Native Profiler Raw Listener TcpStream Error)
    Instant System Zone Timestamp)
  sync : Option (WindowsSyncDispatch.Hooks
    (State Os R H D Aff B Poll Instant System Native Profiler Raw Listener TcpStream Error)
    Miri.Concurrency.TypedSyncRuntime.Ref)
  platform : Option (WindowsPlatformDispatch.Hooks
    (State Os R H D Aff B Poll Instant System Native Profiler Raw Listener TcpStream Error)
    Os Error EnvVars.Kind (EvalWindowsFileConstruction.Ref H D
      (Other Raw Listener TcpStream Error)))

/-- Build the Windows Core and canonical environment from source-owned
compiler, memory, ABI, and host leaves. `components` starts empty because the
remaining Windows file/thread callbacks require the live Main hooks; callers
attach them with `connectComponents`, which checks that same prepared target. -/
def fromSource [DecidableEq MiriMemoryKind] [DecidableEq Os]
    (p : CompilerProviders.Prepared)
    (nativeLibraryPaths : CoreState Os R H D Aff B Poll Instant System Native Profiler Raw Listener TcpStream Error → Array String)
    (callNative : String → MPlaceTy Provenance → Array (OpTy Provenance) →
      EStateM StepError (CoreState Os R H D Aff B Poll Instant System Native Profiler Raw Listener TcpStream Error) Bool)
    (access : ValidityMachine.Access MiriMemoryKind
      (EvalForeignConstruction.Stored Os R Payload H D
        (Other Raw Listener TcpStream Error) Aff B
        (HostRuntime.Storage Poll Instant System H D
          (Other Raw Listener TcpStream Error) Native Profiler)))
    (allocation : PlaceMachine.AllocationConfig MiriMemoryKind
      (EvalForeignConstruction.User Os R Payload H D
        (Other Raw Listener TcpStream Error) Aff B
        (HostRuntime.Storage Poll Instant System H D
          (Other Raw Listener TcpStream Error) Native Profiler)))
    (extras : MemoryExtras.Hooks MiriMemoryKind
      (EvalForeignConstruction.User Os R Payload H D
        (Other Raw Listener TcpStream Error) Aff B
        (HostRuntime.Storage Poll Instant System H D
          (Other Raw Listener TcpStream Error) Native Profiler)) EvalSyncPayload.Payload)
    (deallocationDiagnostic : AllocId → PlaceMachine.MachineM MiriMemoryKind
      (EvalForeignConstruction.User Os R Payload H D
        (Other Raw Listener TcpStream Error) Aff B
        (HostRuntime.Storage Poll Instant System H D
          (Other Raw Listener TcpStream Error) Native Profiler)) Unit)
    (nativeDrop : Option (Allocation Provenance Miri.TreeBorrows.BorrowTree →
      MachineHooks.M MiriMemoryKind
        (EvalForeignConstruction.User Os R Payload H D
          (Other Raw Listener TcpStream Error) Aff B
          (HostRuntime.Storage Poll Instant System H D
            (Other Raw Listener TcpStream Error) Native Profiler)) Unit))
    (pointer : PointerMachine.Hooks MiriMemoryKind
      (ValidityMachine.Control (EvalForeignConstruction.Stored Os R Payload H D
        (Other Raw Listener TcpStream Error) Aff B
        (HostRuntime.Storage Poll Instant System H D
          (Other Raw Listener TcpStream Error) Native Profiler))))
    (spans : AllocationDriver.SpanHooks)
    (corePlace : PlaceHooks Provenance
      (CoreState Os R H D Aff B Poll Instant System Native Profiler Raw Listener TcpStream Error)
      C MachineHooks.FrameExtra)
    (place : PlaceHooks Provenance
      (State Os R H D Aff B Poll Instant System Native Profiler Raw Listener TcpStream Error)
      C MachineHooks.FrameExtra)
    (callFunction : C → CallInstance → Array (RvalueImmTy Provenance) → ReturnContinuation →
      EStateM StepError
        (CoreState Os R H D Aff B Poll Instant System Native Profiler Raw Listener TcpStream Error) Unit)
    (choice : C)
    (osHost : EvalHostRuntimeConstruction.OsHostEffects Os)
    (environmentHost : EvalHostRuntimeConstruction.EnvironmentHostEffects
      (EvalWindowsEnvironmentConstruction.InnerControl Os R Payload H D
        (Other Raw Listener TcpStream Error) Aff B
        (Host Poll Instant System H D Raw Listener TcpStream Error Native Profiler)))
    (memory : EvalWindowsEnvironmentConstruction.Memory Os R Payload H D
      (Other Raw Listener TcpStream Error) Aff B
      (Host Poll Instant System H D Raw Listener TcpStream Error Native Profiler) C)
    (environmentHostConfig : EvalWindowsEnvironmentConstruction.HostEffects
      (State Os R H D Aff B Poll Instant System Native Profiler Raw Listener TcpStream Error)
      Os Error)
    (ioHost : EvalUnixConstruction.IoHostEffects
      (State Os R H D Aff B Poll Instant System Native Profiler Raw Listener TcpStream Error) Error)
    (compatibilityBudget : Nat) (debugAssertions : Bool)
    (userRelevantCrates : Array Nat) :
    EStateM StepError
      (CoreState Os R H D Aff B Poll Instant System Native Profiler Raw Listener TcpStream Error)
      (Assembly Os R H D Aff B Poll Instant System Native Profiler
        Raw Listener TcpStream Error C Meta Path Zone Timestamp) := do
  let target ← match p.externStatics.targetFacts with
    | .ok facts => pure facts
    | .error reason => throw (.unsupported reason)
  unless target.os == "windows" || target.families.contains "windows" do
    throw (.invalidProgram s!"Windows source factory requested for `{target.os}`")
  let arch ← match EvalArchitectureMachine.targetArch p.intrinsics with
    | .ok arch => pure arch
    | .error reason => throw (.unsupported reason)
  let sourceSymbols ← match p.foreignSymbols with
    | .ok value => pure value
    | .error reason => throw (.unsupported reason)
  let symbols := CompilerForeignSymbols.hooks sourceSymbols p.lifecycle.calls
  let options : EvalForeignConstruction.Options := {
    family := .windows
    os := target.os
    arch
    noAllocShimSymbol := sourceSymbols.noAllocShimSymbol
    compatibilityBudget
    debugAssertions }
  let errors ← match EvalWindowsIoErrorConstruction.fromSource p osHost.hostUnix ioHost memory with
    | .ok value => pure value | .error error => throw error
  let environment ← match EvalWindowsEnvironmentDispatchConstruction.fromSource p osHost
      environmentHost memory place choice compatibilityBudget errors environmentHostConfig with
    | .ok value => pure value | .error error => throw error
  let native : EvalForeignConstruction.HostEffects
      (CoreState Os R H D Aff B Poll Instant System Native Profiler Raw Listener TcpStream Error) := {
    nativeLibraryPaths
    callNative
    setEnomem := ExecutionStateTransport.reverseAction
      (IoError.setLastError errors (.libc "ENOMEM")) }
  let common ← lift (EvalForeignConstruction.common p options symbols native access allocation extras
    deallocationDiagnostic nativeDrop pointer spans corePlace callFunction choice)
  let foreign ← EvalForeignConstruction.core common spans
  unless foreign.family == .windows && foreign.os == target.os && foreign.arch == arch do
    throw (.invalidProgram "Windows Core target differs from prepared compiler target")
  let sourceSeed : SourceSeed Os R H D Aff B Poll Instant System Native Profiler
      Raw Listener TcpStream Error C := ⟨osHost,environmentHost,
        environmentHostConfig,ioHost,memory,place,choice,compatibilityBudget,userRelevantCrates⟩
  pure ⟨common,foreign,environment,errors,osHost,environmentHost,
    environmentHostConfig,place,choice,compatibilityBudget,userRelevantCrates,
    sourceSeed,memory,none,none,none,none⟩

/-- Attach the actual Windows environment, file, and thread constructors to
the live Main callbacks and canonical registries. All inputs are raw source
capabilities or existing world components; no caller supplies completed
Windows guest hooks. -/
def connectComponents [DecidableEq MiriMemoryKind] [DecidableEq Os]
    (p : CompilerProviders.Prepared)
    (assembly : Assembly Os R H D Aff B Poll Instant System Native Profiler
      Raw Listener TcpStream Error C Meta Path Zone Timestamp)
    (main : MainMachine.Hooks (EvalWindowsFileConstruction.Payload Os R Payload H D
      (Other Raw Listener TcpStream Error) Aff B
      (Host Poll Instant System H D Raw Listener TcpStream Error Native Profiler))
      C (Other Raw Listener TcpStream Error) ABI.ExternAbi (FnAbi TyId) (ArgAbi TyId) Aff ProgramExitPoll)
    (fileRegistry : Files.Hooks
      (State Os R H D Aff B Poll Instant System Native Profiler Raw Listener TcpStream Error)
      H D (Other Raw Listener TcpStream Error) Error Meta)
    (readiness : ReadinessMachine.Hooks MiriMemoryKind
      (ThreadStacks.Storage (EvalWindowsFileConstruction.Payload Os R Payload H D
        (Other Raw Listener TcpStream Error) Aff B
        (Host Poll Instant System H D Raw Listener TcpStream Error Native Profiler)))
      H D (Other Raw Listener TcpStream Error))
    (sharedOpen : UnixOpen.Hooks
      (State Os R H D Aff B Poll Instant System Native Profiler Raw Listener TcpStream Error)
      H D (Other Raw Listener TcpStream Error) Error Meta Path)
    (prepareDirectory : D → Path → EStateM StepError
      (State Os R H D Aff B Poll Instant System Native Profiler Raw Listener TcpStream Error) D)
    (otherMetadata : Other Raw Listener TcpStream Error → EStateM StepError
      (State Os R H D Aff B Poll Instant System Native Profiler Raw Listener TcpStream Error)
      (Sum (Except (IoError.HostError Error) Meta) String))
    (timeHooks : TimeShims.Hooks
      (State Os R H D Aff B Poll Instant System Native Profiler Raw Listener TcpStream Error)
      Instant System Zone Timestamp)
    (hostFiles : EvalWindowsFileConstruction.HostEffects Os
      (State Os R H D Aff B Poll Instant System Native Profiler Raw Listener TcpStream Error)
      Path H D (Other Raw Listener TcpStream Error) Meta System Error)
    (checkPointerAccess : Pointer (Option Provenance) → Size → EStateM StepError
      (State Os R H D Aff B Poll Instant System Native Profiler Raw Listener TcpStream Error) Unit)
    (projection : PlaceProjectionHooks Provenance
      (State Os R H D Aff B Poll Instant System Native Profiler Raw Listener TcpStream Error)
      C MachineHooks.FrameExtra)
    (threadError : Concurrency.ThreadError → StepError) :
    Except StepError (Assembly Os R H D Aff B Poll Instant System Native Profiler
      Raw Listener TcpStream Error C Meta Path Zone Timestamp) := do
  let target ← p.externStatics.targetFacts |>.mapError StepError.unsupported
  unless (target.os == "windows" || target.families.contains "windows") &&
      assembly.foreign.family == .windows && assembly.foreign.os == target.os &&
      assembly.environment.env.process.family == .windows &&
      assembly.environment.env.process.os == target.os do
    throw (.invalidProgram "Windows source assembly target mismatch")
  let seed := assembly.sourceSeed
  let built ← EvalWindowsSourceConstruction.fromSource p seed.osHost
    seed.environmentHost seed.memory seed.place assembly.errors
    seed.environmentHostConfig main fileRegistry readiness sharedOpen
    prepareDirectory otherMetadata timeHooks hostFiles checkPointerAccess
    seed.choice seed.compatibilityBudget projection seed.userRelevantCrates threadError
  pure {assembly with components := some built}

/-- Canonical source connection for Windows time and synchronization. This
derives both guest hook dictionaries from the same environment/memory/Main,
typed sync objects, selected atomic backend, deadline registry, compiler facts,
and raw chrono leaves before attaching the base environment/file/thread
components. -/
def connectWithTimeSync [DecidableEq MiriMemoryKind] [DecidableEq Os]
    (p : CompilerProviders.Prepared)
    (assembly : Assembly Os R H D Aff B Poll Instant System Native Profiler
      Raw Listener TcpStream Error C Meta Path Zone Timestamp)
    (main : MainMachine.Hooks (EvalWindowsFileConstruction.Payload Os R Payload H D
      (Other Raw Listener TcpStream Error) Aff B
      (Host Poll Instant System H D Raw Listener TcpStream Error Native Profiler))
      C (Other Raw Listener TcpStream Error) ABI.ExternAbi (FnAbi TyId) (ArgAbi TyId) Aff ProgramExitPoll)
    (objects : ForeignSyncMachine.Objects
      (State Os R H D Aff B Poll Instant System Native Profiler Raw Listener TcpStream Error))
    (atomic : AtomicAccessHooks Provenance
      (State Os R H D Aff B Poll Instant System Native Profiler Raw Listener TcpStream Error)
      C (RuntimePlace Provenance))
    (projection : PlaceProjectionHooks Provenance
      (State Os R H D Aff B Poll Instant System Native Profiler Raw Listener TcpStream Error)
      C MachineHooks.FrameExtra)
    (deadline : DeadlineMachine.Hooks MiriMemoryKind
      (ExecutionStateTransport.Inner (EvalWorld.World Os R EvalSyncPayload.Payload H D
        (Other Raw Listener TcpStream Error) Aff B
        (HostRuntime.Storage Poll Instant System H D
          (Other Raw Listener TcpStream Error) Native Profiler)))
      Instant System)
    (functions : FunctionPointers.Hooks MiriMemoryKind
      (ValidityMachine.UserState (ThreadStacks.Storage (EvalWorld.World Os R EvalSyncPayload.Payload H D
        (Other Raw Listener TcpStream Error) Aff B
        (HostRuntime.Storage Poll Instant System H D
          (Other Raw Listener TcpStream Error) Native Profiler))))
      (Other Raw Listener TcpStream Error))
    (syncEffects : TypedSyncMachine.Effects
      (EvalTypedSyncMachine.State Os R Payload H D
        (Other Raw Listener TcpStream Error) Aff B Poll Instant System Native Profiler))
    (clock : Clock.HostHooks Instant System
      (EvalTimeConstruction.State Os R Payload H D
        (Other Raw Listener TcpStream Error) Aff B Poll Instant System Native Profiler))
    (systemDurationSince : System → System → EStateM StepError
      (EvalTimeConstruction.State Os R Payload H D
        (Other Raw Listener TcpStream Error) Aff B Poll Instant System Native Profiler)
      (Option Clock.Duration))
    (timezoneString : Os → Except Unit String) (communicate : Bool)
    (timeHost : EvalTimeConstruction.HostEffects
      (EvalTimeConstruction.State Os R Payload H D
        (Other Raw Listener TcpStream Error) Aff B Poll Instant System Native Profiler)
      Zone Timestamp)
    (fileRegistry : Files.Hooks
      (State Os R H D Aff B Poll Instant System Native Profiler Raw Listener TcpStream Error)
      H D (Other Raw Listener TcpStream Error) Error Meta)
    (readiness : ReadinessMachine.Hooks MiriMemoryKind
      (ThreadStacks.Storage (EvalWindowsFileConstruction.Payload Os R Payload H D
        (Other Raw Listener TcpStream Error) Aff B
        (Host Poll Instant System H D Raw Listener TcpStream Error Native Profiler)))
      H D (Other Raw Listener TcpStream Error))
    (sharedOpen : UnixOpen.Hooks
      (State Os R H D Aff B Poll Instant System Native Profiler Raw Listener TcpStream Error)
      H D (Other Raw Listener TcpStream Error) Error Meta Path)
    (prepareDirectory : D → Path → EStateM StepError
      (State Os R H D Aff B Poll Instant System Native Profiler Raw Listener TcpStream Error) D)
    (otherMetadata : Other Raw Listener TcpStream Error → EStateM StepError
      (State Os R H D Aff B Poll Instant System Native Profiler Raw Listener TcpStream Error)
      (Sum (Except (IoError.HostError Error) Meta) String))
    (hostFiles : EvalWindowsFileConstruction.HostEffects Os
      (State Os R H D Aff B Poll Instant System Native Profiler Raw Listener TcpStream Error)
      Path H D (Other Raw Listener TcpStream Error) Meta System Error)
    (checkPointerAccess : Pointer (Option Provenance) → Size → EStateM StepError
      (State Os R H D Aff B Poll Instant System Native Profiler Raw Listener TcpStream Error) Unit)
    (threadError : Concurrency.ThreadError → StepError) :
    Except StepError (Assembly Os R H D Aff B Poll Instant System Native Profiler
      Raw Listener TcpStream Error C Meta Path Zone Timestamp) := do
  let sync ← EvalWindowsSyncTimeConstruction.syncFromSource p main objects atomic
    projection assembly.sourceSeed.choice deadline assembly.errors
    assembly.sourceSeed.compatibilityBudget
  let time ← EvalWindowsSyncTimeConstruction.timeFromSource p assembly.sourceSeed.memory
    assembly.sourceSeed.environmentHost assembly.sourceSeed.osHost functions syncEffects
    (ioErrorsToInner assembly.errors) clock systemDurationSince timezoneString communicate timeHost
  let timeDispatch : TimeShimDispatch.Hooks
      (State Os R H D Aff B Poll Instant System Native Profiler Raw Listener TcpStream Error)
      Instant System Zone Timestamp := {
    time
    expectedAbi := fun name _ => CompilerNamedShimAbi.query p.namedAbi name
    systemConvention := (CompilerNamedShimAbi.query p.namedAbi "GetSystemTimeAsFileTime").map (·.conv)
    argumentCompat := fun caller callee => ExecutionStateTransport.action do
      let compiler : ExecutionCallLeaves.Compiler
          (CoreState Os R H D Aff B Poll Instant System Native Profiler Raw Listener TcpStream Error)
          C ABI.ExternAbi :=
        CompilerCallConstruction.compiler p assembly.sourceSeed.compatibilityBudget
      compiler.checkArgumentCompat assembly.sourceSeed.choice caller callee
    checkSymbolClash := fun name =>
      ExecutionStateTransport.action (assembly.foreign.checkSymbolClash name)
    transmute := fun operand target => do
      let projection ← assembly.sourceSeed.place.projection assembly.sourceSeed.choice
      match operand.transmute projection target |>.mapError IntrinsicVectorMachine.projectionError with
      | .ok value => pure value | .error error => throw error }
  let assembly ← connectComponents p assembly main fileRegistry readiness sharedOpen
    prepareDirectory otherMetadata time hostFiles checkPointerAccess projection threadError
  pure {assembly with time := some timeDispatch, sync := some sync}

/-- Attach the Main-bound Windows platform family from its raw host leaves and
the same prepared Main/environment/memory. Heap and process operations are
therefore constructed against the live Main state rather than supplied as a
completed guest dispatcher. -/
def connectPlatformFromSource [DecidableEq MiriMemoryKind] [DecidableEq Os]
    (p : CompilerProviders.Prepared)
    (assembly : Assembly Os R H D Aff B Poll Instant System Native Profiler
      Raw Listener TcpStream Error C Meta Path Zone Timestamp)
    (main : MainMachine.Hooks (EvalWindowsFileConstruction.Payload Os R Payload H D
      (Other Raw Listener TcpStream Error) Aff B
      (Host Poll Instant System H D Raw Listener TcpStream Error Native Profiler))
      C (Other Raw Listener TcpStream Error) ABI.ExternAbi (FnAbi TyId) (ArgAbi TyId) Aff ProgramExitPoll)
    (extras : MemoryExtras.Hooks MiriMemoryKind
      (PointerMachine.User (EvalWindowsEnvironmentConstruction.InnerControl Os R Payload H D
        (Other Raw Listener TcpStream Error) Aff B
        (Host Poll Instant System H D Raw Listener TcpStream Error Native Profiler))) Payload)
    (spans : AllocationDriver.SpanHooks)
    (embed : WindowsPlatform.DynamicSymbol → Other Raw Listener TcpStream Error)
    (projection : PlaceProjectionHooks Provenance
      (State Os R H D Aff B Poll Instant System Native Profiler Raw Listener TcpStream Error)
      C MachineHooks.FrameExtra)
    (host : EvalWindowsPlatformConstruction.HostEffects
      (State Os R H D Aff B Poll Instant System Native Profiler Raw Listener TcpStream Error) Os Error)
    (unwind : Unwind.Hooks MiriMemoryKind
      (ThreadStacks.Storage (EvalWindowsFileConstruction.Payload Os R Payload H D
        (Other Raw Listener TcpStream Error) Aff B
        (Host Poll Instant System H D Raw Listener TcpStream Error Native Profiler)))
      C (Other Raw Listener TcpStream Error)) :
    Except StepError (Assembly Os R H D Aff B Poll Instant System Native Profiler
      Raw Listener TcpStream Error C Meta Path Zone Timestamp) := do
  let some components := assembly.components |
    throw (.invalidProgram "Windows platform construction requires the live source file/handle registry")
  let platform ← EvalWindowsPlatformConstruction.fromSource p main
    assembly.environment.env assembly.memory extras spans components.files.paths.files.handles
    embed assembly.place projection assembly.choice host
    (fun code => ExecutionStateTransport.action (assembly.foreign.startExit code))
    unwind assembly.compatibilityBudget
  pure {assembly with platform := some platform}

def callbackProductFromSource [DecidableEq Os]
    (main : MainMachine.Hooks (EvalWindowsFileConstruction.Payload Os R Payload H D
      (Other Raw Listener TcpStream Error) Aff B
      (Host Poll Instant System H D Raw Listener TcpStream Error Native Profiler))
      C (Other Raw Listener TcpStream Error) ABI.ExternAbi (FnAbi TyId) (ArgAbi TyId) Aff ProgramExitPoll)
    (effects : TypedSyncMachine.Effects
      (EvalTypedSyncMachine.State Os R Payload H D
        (Other Raw Listener TcpStream Error) Aff B Poll Instant System Native Profiler))
     :
    Except StepError (EvalWindowsCallbackSourceConstruction.Product
      Os R Payload H D (Other Raw Listener TcpStream Error) Aff B
      Poll Instant System Native Profiler C ABI.ExternAbi (FnAbi TyId) (ArgAbi TyId)) :=
  EvalWindowsCallbackSourceConstruction.fromSource main effects

private def memoryDestination
    (destination : RuntimePlace Provenance) :
    EStateM StepError S (MPlaceTy Provenance) := do
  match destination.ref with
  | .memory memory => pure ⟨memory,destination.layout⟩
  | .local .. => throw (.invalidProgram "Windows foreign destination was not materialized")

/-- Adapt a source Core whose public destinations are RuntimePlaces to the
materialized MPlace interface required by Windows shim implementations. This
is the same force-allocation boundary used by the Unix source dispatcher. -/
private def materializedCore
    (core : ForeignItems.Core Provenance
      (State Os R H D Aff B Poll Instant System Native Profiler Raw Listener TcpStream Error)
      (RuntimePlace Provenance) (RuntimePlace Provenance)
      (Pointer (Option Provenance)) LoadedBody CallInstance) :
    ForeignItems.Core Provenance
      (State Os R H D Aff B Poll Instant System Native Profiler Raw Listener TcpStream Error)
      (RuntimePlace Provenance) (MPlaceTy Provenance)
      (Pointer (Option Provenance)) LoadedBody CallInstance := {
  core with
  forceAllocation := fun destination => do
    memoryDestination (← core.forceAllocation destination)
  callNative := fun name destination args =>
    core.callNative name ⟨.memory destination.mplace,destination.layout⟩ args
  writePointer := fun pointer destination =>
    core.writePointer pointer ⟨.memory destination.mplace,destination.layout⟩
  writeNull := fun destination =>
    core.writeNull ⟨.memory destination.mplace,destination.layout⟩
  specialDestination := fun destination => do
    memoryDestination (← core.specialDestination destination) }

/-- Produce the Windows foreign interpreter on CoreState from the prepared
Common/Core and the source-built Windows components. The Core dictionary is
transported losslessly to the Main/thread state so environment, file and TLS
operations mutate the same world, then returned to the interpreter state.
Calls for unfinished families remain demand-local Unsupported through the
Windows source resolver. -/
def foreignFromAssembly [DecidableEq Os]
    (p : CompilerProviders.Prepared)
    (assembly : Assembly Os R H D Aff B Poll Instant System Native Profiler
      Raw Listener TcpStream Error C Meta Path Zone Timestamp)
    (mathHooks : Math.Hooks Provenance
      (CoreState Os R H D Aff B Poll Instant System Native Profiler Raw Listener TcpStream Error)
      C (RuntimePlace Provenance))
    (configuration : HostRuntime.Configuration)
    (hostFill : Option (Nat → EStateM StepError
      (State Os R H D Aff B Poll Instant System Native Profiler Raw Listener TcpStream Error)
      (Except String ByteArray))) :
    Except StepError (ForeignItems.Hooks Provenance
      (CoreState Os R H D Aff B Poll Instant System Native Profiler Raw Listener TcpStream Error)
      (RuntimePlace Provenance) (RuntimePlace Provenance)
      (Pointer (Option Provenance)) LoadedBody CallInstance) := do
  let components := assembly.components
  let foreign := assembly.foreign
  unless foreign.family == .windows && foreign.os == assembly.foreign.os &&
      foreign.arch == assembly.foreign.arch do
    throw (.invalidProgram "Windows foreign Core does not match its source Common")
  let baseInner := EvalForeignConstruction.assemble foreign
    (fun name abi args dest => EvalForeignConstruction.math mathHooks foreign
      assembly.choice name abi args dest)
    (fun name _ _ _ => throw (.unsupported s!"Unix shim `{name}` reached Windows source hooks"))
    (fun _ _ _ _ => pure .NotSupported)
    (fun name _ _ _ => throw (.unsupported s!"portable foreign shim `{name}` has no connected Windows source arm"))
  let baseOuter := ExecutionForeignTransport.hooks baseInner
  let coreOuter := materializedCore baseOuter.toCore
  let tape : ExecutionChoices.Access
      (State Os R H D Aff B Poll Instant System Native Profiler Raw Listener TcpStream Error) := {
    get := fun state => EvalCoreMachine.tape.get (ExecutionStateTransport.inward state)
    put := fun state choices => ExecutionStateTransport.outward
      (EvalCoreMachine.tape.put (ExecutionStateTransport.inward state) choices) }
  let access := ExecutionMemoryTransport.access assembly.memory.access
  let random ← EvalWindowsRandomConstruction.fromAccess p access coreOuter
    assembly.place tape assembly.choice configuration.communicate
    configuration.hostUsizeBits hostFill
  let stdOnly ← EvalWindowsStdOnlyConstruction.fromSource p assembly.userRelevantCrates
    coreOuter assembly.place assembly.errors assembly.choice
  let materialized : ForeignItems.Hooks Provenance
      (State Os R H D Aff B Poll Instant System Native Profiler Raw Listener TcpStream Error)
      (RuntimePlace Provenance) (MPlaceTy Provenance)
      (Pointer (Option Provenance)) LoadedBody CallInstance := {
    toCore := coreOuter
    math := fun name abi args dest => baseOuter.math name abi args
      ⟨.memory dest.mplace,dest.layout⟩
    unix := fun name abi args dest => baseOuter.unix name abi args
      ⟨.memory dest.mplace,dest.layout⟩
    windows := fun _ _ _ _ => pure .NotSupported
    otherPortable := fun name abi args dest => baseOuter.otherPortable name abi args
      ⟨.memory dest.mplace,dest.layout⟩ }
  let installed := {baseOuter with
    windows := fun name abi args dest => do
      let dest ← memoryDestination dest
      match components with
      | some components =>
        EvalWindowsSourceConstruction.dispatch (ForeignBody := LoadedBody)
          (Destination := RuntimePlace Provenance) (I := CallInstance)
          components assembly.time assembly.sync
          (some random) assembly.platform (some stdOnly) materialized name abi args dest
      | none =>
        EvalWindowsSourceConstruction.dispatchInitial (ForeignBody := LoadedBody)
          (Destination := RuntimePlace Provenance) (I := CallInstance)
          assembly.environment assembly.time assembly.sync
          (some random) assembly.platform (some stdOnly) materialized name abi args dest }
  pure (ExecutionForeignTransport.reverseHooks installed)

end Miri.Input.EvalWindowsCallDispatchConstruction
