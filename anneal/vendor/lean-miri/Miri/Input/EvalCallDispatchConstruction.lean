import Miri.Input.EvalForeignConstruction
import Miri.Input.EvalUnixSourceConstruction
import Miri.Interpreter.Math.Dispatch
import Miri.Interpreter.ForeignItems
import Miri.Interpreter.UnixForeign
import Miri.Interpreter.LinuxForeign
import Miri.Interpreter.AndroidForeign
import Miri.Input.EvalSourceHostEffects
import Miri.Input.EvalSyncPayload
import Miri.Input.InitialMachine
import Miri.Input.EvalCallbackSocketRegistry
import Miri.Input.EvalUnixLinuxMemoryDispatchConstruction
import Miri.Input.EvalUnixLinuxConstruction
import Miri.Input.EvalUnixNativeFdConstruction
import Miri.Input.CompilerShimSignatures
import Miri.Input.CompilerNamedConstants
import Miri.Input.CompilerCallConstruction
import Miri.Input.EvalCallbackSocketConstruction
import Miri.Interpreter.OsStrings
import Miri.Concurrency.SyncRuntime
import Miri.Interpreter.UnixFdChoices

/-! Final source-owned call-foreign assembly for the currently constructed
Unix chain. The callback is an effectful factory, so the canonical Core is
created from the live state at the call boundary. No caller supplies a
completed `ForeignItems.Hooks` record. Unsupported portable arms remain
demand-local; the Unix dispatcher retains its exact source order/fallback. -/
namespace Miri.Input.EvalCallDispatchConstruction
open Miri.ABI Miri.Memory Miri.MIR Miri.Interpreter

abbrev Other Raw Listener TcpStream Error :=
  EvalUnixSourceConstruction.Other Raw Listener TcpStream Error
abbrev User Os R P H D Aff B Poll Instant System Native Profiler Raw Listener TcpStream Error :=
  EvalUnixSourceConstruction.User Os R P H D Aff B Poll Instant System Native Profiler Raw Listener TcpStream Error
abbrev State Os R P H D Aff B Poll Instant System Native Profiler Raw Listener TcpStream Error :=
  EvalUnixSourceConstruction.State Os R P H D Aff B Poll Instant System Native Profiler Raw Listener TcpStream Error
abbrev SourceUser Os R H D Aff B Poll Instant System Native Profiler Raw Listener TcpStream Error :=
  EvalUnixSourceConstruction.User Os R EvalSyncPayload.Payload H D Aff B Poll Instant System Native Profiler Raw Listener TcpStream Error
abbrev M Os R P H D Aff B Poll Instant System Native Profiler Raw Listener TcpStream Error A :=
  MachineHooks.M MiriMemoryKind
    (User Os R P H D Aff B Poll Instant System Native Profiler Raw Listener TcpStream Error) A

/-- Typed subsystem source input for EvalConfigurationCore. The platform
components are already source-built component records, never a completed
ForeignItems/UnixForeign hook. Core constructs Common and the ordered final
resolver at the actual call state. -/
abbrev HostSeed Os R H D Aff B Poll Instant System Native Profiler Raw Listener TcpStream Error ErrorHost Meta Path AddrIter :=
  EvalSourceHostEffects.Seed Os R
    (EvalUnixSourceConstruction.Control Os R EvalSyncPayload.Payload H D Aff B Poll Instant System Native Profiler
      Raw Listener TcpStream Error)
    (State Os R EvalSyncPayload.Payload H D Aff B Poll Instant System Native Profiler
      Raw Listener TcpStream Error)
    H D (Other Raw Listener TcpStream Error) Aff B Raw Listener TcpStream Error ErrorHost
    Meta Path Poll AddrIter Instant System Native Profiler
    (State Os R EvalSyncPayload.Payload H D Aff B Poll Instant System Native Profiler
      Raw Listener TcpStream Error)

structure SourceInput
    (Os R H D Aff B Poll Instant System Native Profiler Raw Listener TcpStream Error
      ErrorHost Meta Path AddrIter : Type) where
  /-- Raw host capabilities only. Compiler-derived dispatch and state-owned
  Unix components are assembled at the live Core call boundary. -/
  host : HostSeed Os R H D Aff B Poll Instant System Native Profiler
    Raw Listener TcpStream Error ErrorHost Meta Path AddrIter
  geometry : InitialMachine.Geometry
  alignment : ValidityMachine.AlignmentCheck
  stringScanBudget : Nat
  pollBudget : Nat
  fileReferenceBudget : Nat
  watcherReferenceBudget : Nat
  /-- Selected Miri setting; this controls source short-I/O behavior and is
  not inferred from compiler target facts. -/
  shortFdOperations : Bool
  varArgsBudget : Nat

private def memoryDestination (destination : RuntimePlace Provenance) :
    M Os R P H D Aff B Poll Instant System Native Profiler Raw Listener TcpStream Error
      (MPlaceTy Provenance) := do
  match destination.ref with
  | .memory memory => pure ⟨memory,destination.layout⟩
  | .local .. => throw (.invalidProgram "foreign source destination was not materialized")

private def sourceReadScalar
    (access : ValidityMachine.Access MiriMemoryKind
      (EvalCoreMachine.Stored Os R P H D (Other Raw Listener TcpStream Error) Aff B
        (HostRuntime.Storage Poll Instant System H D (Other Raw Listener TcpStream Error) Native Profiler)))
    (operand : OpTy Provenance) : M Os R P H D Aff B Poll Instant System Native Profiler Raw Listener TcpStream Error
      (Scalar Provenance) := do
  let immediate ← ValidityMachine.readImmediate access operand
  match immediate.imm.toScalar with
  | .ok value => pure value
  | .error error => throw (ScalarOps.immediateError error)

private def sourceReadI32
    (access : ValidityMachine.Access MiriMemoryKind
      (EvalCoreMachine.Stored Os R P H D (Other Raw Listener TcpStream Error) Aff B
        (HostRuntime.Storage Poll Instant System H D (Other Raw Listener TcpStream Error) Native Profiler)))
    (operand : OpTy Provenance) : M Os R P H D Aff B Poll Instant System Native Profiler Raw Listener TcpStream Error Int32 := do
  match (← sourceReadScalar access operand).toInt32 with
  | .ok value => pure value
  | .error error => throw (ScalarOps.scalarError error)

private def sourceReadUsize
    (access : ValidityMachine.Access MiriMemoryKind
      (EvalCoreMachine.Stored Os R P H D (Other Raw Listener TcpStream Error) Aff B
        (HostRuntime.Storage Poll Instant System H D (Other Raw Listener TcpStream Error) Native Profiler)))
    (operand : OpTy Provenance) : M Os R P H D Aff B Poll Instant System Native Profiler Raw Listener TcpStream Error UInt64 := do
  match (← sourceReadScalar access operand).toTargetUsize access.runtime.pointerSize with
  | .ok value => pure value
  | .error error => throw (ScalarOps.scalarError error)

private def sourceReadOffset
    (access : ValidityMachine.Access MiriMemoryKind
      (EvalCoreMachine.Stored Os R P H D (Other Raw Listener TcpStream Error) Aff B
        (HostRuntime.Storage Poll Instant System H D (Other Raw Listener TcpStream Error) Native Profiler)))
    (operand : OpTy Provenance) : M Os R P H D Aff B Poll Instant System Native Profiler Raw Listener TcpStream Error Int := do
  match (← sourceReadScalar access operand).toInt operand.layout.layout.size with
  | .ok value => pure value
  | .error error => throw (ScalarOps.scalarError error)

private def sourceReadPointer
    (access : ValidityMachine.Access MiriMemoryKind
      (EvalCoreMachine.Stored Os R P H D (Other Raw Listener TcpStream Error) Aff B
        (HostRuntime.Storage Poll Instant System H D (Other Raw Listener TcpStream Error) Native Profiler)))
    (operand : OpTy Provenance) : M Os R P H D Aff B Poll Instant System Native Profiler Raw Listener TcpStream Error
      (Pointer (Option Provenance)) := do
  match (← sourceReadScalar access operand).toPointer access.runtime.base with
  | .ok value => pure value
  | .error error => throw (ScalarOps.scalarError error)

set_option autoImplicit false in structure SourceCallbackSeed
    (Os R H D Aff B Poll Instant System Native Profiler Raw Listener TcpStream Error
      Meta Path Place C ClockHost I AddrIter : Type) where
  /-- The final source-built descriptor/files/readiness operations used by
  both foreign dispatch and the ordinary callback runtime. -/
  nativeFd : EvalUnixNativeFdConstruction.Components Os R EvalSyncPayload.Payload H D Aff B
    Poll Instant System Native Profiler Raw Listener TcpStream Error Meta Path Place C
    ClockHost I LoadedBody
  registry : EvalCallbackSocketConstruction.RegistrySeed Os R EvalSyncPayload.Payload H D Aff B
    Poll Instant System Native Profiler Raw Listener TcpStream Error
  virtual : VirtualSocket.Hooks
    (State Os R EvalSyncPayload.Payload H D Aff B Poll Instant System Native Profiler Raw Listener TcpStream Error)
    (Files.Ref (Files.Description H D (Other Raw Listener TcpStream Error))) Error
  tcp : TcpSocket.Hooks
    (State Os R EvalSyncPayload.Payload H D Aff B Poll Instant System Native Profiler Raw Listener TcpStream Error)
    (Files.Ref (Files.Description H D (Other Raw Listener TcpStream Error)))
    Raw Listener TcpStream Error Poll Error
  syncEffects : TypedSyncMachine.Effects
    (State Os R EvalSyncPayload.Payload H D Aff B Poll Instant System Native Profiler Raw Listener TcpStream Error)
  errors : IoError.Hooks
    (State Os R EvalSyncPayload.Payload H D Aff B Poll Instant System Native Profiler Raw Listener TcpStream Error)
    Error
  readinessRoute : EvalUnixFdConstruction.ReadinessRoute
    (State Os R EvalSyncPayload.Payload H D Aff B Poll Instant System Native Profiler Raw Listener TcpStream Error)

structure SourceAssembly
    (Os R P H D Aff B Poll Instant System Native Profiler Raw Listener TcpStream Error C : Type)
    (CallbackSeed : Type := Unit) where
  foreign : ForeignItems.Hooks Provenance
    (State Os R P H D Aff B Poll Instant System Native Profiler Raw Listener TcpStream Error)
    (RuntimePlace Provenance) (RuntimePlace Provenance)
    (Pointer (Option Provenance)) LoadedBody CallInstance
  dispatchers : UnixForeign.SourceDispatchers
    (State Os R P H D Aff B Poll Instant System Native Profiler Raw Listener TcpStream Error)
  environment : Option (UnixEnvironmentDispatch.Hooks
    (State Os R P H D Aff B Poll Instant System Native Profiler Raw Listener TcpStream Error)
    Os Error EnvVars.Kind)
  memory : Option (EvalHostRuntimeConstruction.EnvironmentMemory
    (ValidityMachine.Control (EvalCoreMachine.Stored Os R P H D
      (Other Raw Listener TcpStream Error) Aff B
      (HostRuntime.Storage Poll Instant System H D
        (Other Raw Listener TcpStream Error) Native Profiler))) C P)
  registry : Option (EvalCallbackSocketConstruction.RegistrySeed
    Os R P H D Aff B Poll Instant System Native Profiler Raw Listener TcpStream Error)
  threadTls : Option (EvalUnixThreadTlsConstruction.Components
    (State Os R P H D Aff B Poll Instant System Native Profiler Raw Listener TcpStream Error)
    (MPlaceTy Provenance) B CallInstance)
  callbackSeed : Option CallbackSeed

private def assembleSourceOrder
    (p : CompilerProviders.Prepared)
    (common : EvalForeignConstruction.Common
      (State Os R P H D Aff B Poll Instant System Native Profiler Raw Listener TcpStream Error))
    (spans : AllocationDriver.SpanHooks)
    (mathHooks : Math.Hooks Provenance
      (State Os R P H D Aff B Poll Instant System Native Profiler Raw Listener TcpStream Error)
      C (RuntimePlace Provenance))
    (dispatchers : UnixForeign.SourceDispatchers
      (State Os R P H D Aff B Poll Instant System Native Profiler Raw Listener TcpStream Error))
    (choice : C) (CallbackSeed : Type := Unit) :
    M Os R P H D Aff B Poll Instant System Native Profiler Raw Listener TcpStream Error
      (SourceAssembly Os R P H D Aff B Poll Instant System Native Profiler Raw Listener TcpStream Error C CallbackSeed) := do
  let target ← match p.externStatics.targetFacts with
    | .ok facts => pure facts
    | .error reason => throw (.unsupported s!"foreign source target facts: {reason}")
  let arch ← match EvalArchitectureMachine.targetArch p.intrinsics with
    | .ok arch => pure arch
    | .error reason => throw (.unsupported s!"foreign source target architecture: {reason}")
  unless target.families.contains "unix" && common.options.family == .unix &&
      common.options.os == target.os && common.options.arch == arch do
    throw (.invalidProgram "foreign Core target differs from prepared Unix compiler target")
  let core ← EvalForeignConstruction.core common spans
  unless core.family == .unix && core.os == target.os && core.arch == arch do
    throw (.invalidProgram "foreign Core and Unix source dispatcher differ")
  let unixCore : ForeignItems.Core Provenance
      (State Os R P H D Aff B Poll Instant System Native Profiler Raw Listener TcpStream Error)
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
      memoryDestination (← core.forceAllocation destination)
  }
  let unix := fun name abi args destination => do
    let destination ← memoryDestination destination
    UnixForeign.dispatchSource dispatchers unixCore name abi args destination
  let mathHandler := fun name abi args destination =>
    EvalForeignConstruction.math mathHooks core choice name abi args destination
  let windows := fun _ _ _ _ =>
    throw (.invalidProgram "Windows foreign arm reached from Unix source factory")
  let otherPortable := fun name _ _ _ =>
    throw (.unsupported s!"portable foreign shim `{name}` has no connected source constructor")
  pure ⟨EvalForeignConstruction.assemble core mathHandler unix windows otherPortable,
    dispatchers, none, none, none, none, none⟩

/-- Connect only the source environment and std-only components while the
remaining Unix subsystems are under construction. The dispatcher itself keeps
the pinned order and uses exact target-aware demand-local Unsupported arms. -/
def fromEnvironmentStdOnlyPackage
    (p : CompilerProviders.Prepared)
    (common : EvalForeignConstruction.Common
      (State Os R P H D Aff B Poll Instant System Native Profiler Raw Listener TcpStream Error))
    (spans : AllocationDriver.SpanHooks)
    (mathHooks : Math.Hooks Provenance
      (State Os R P H D Aff B Poll Instant System Native Profiler Raw Listener TcpStream Error)
      C (RuntimePlace Provenance))
    (environment : UnixEnvironmentDispatch.Hooks
      (State Os R P H D Aff B Poll Instant System Native Profiler Raw Listener TcpStream Error)
      Os Error EnvVars.Kind)
    (stdOnly : StdOnlyShims.Hooks Provenance
      (State Os R P H D Aff B Poll Instant System Native Profiler Raw Listener TcpStream Error)
      Place (MPlaceTy Provenance) LoadedBody CallInstance)
    (communicate : Bool)
    (choice : C) (CallbackSeed : Type := Unit) :
    M Os R P H D Aff B Poll Instant System Native Profiler Raw Listener TcpStream Error
      (SourceAssembly Os R P H D Aff B Poll Instant System Native Profiler Raw Listener TcpStream Error C CallbackSeed) := do
  let target ← match p.externStatics.targetFacts with
    | .ok facts => pure facts
    | .error reason => throw (.unsupported s!"foreign source target facts: {reason}")
  unless target.families.contains "unix" && environment.env.os == target.os &&
      environment.env.targetEnv == target.env && stdOnly.foreign.family == .unix &&
      stdOnly.foreign.os == target.os && stdOnly.targetEnv == target.env &&
      environment.env.process.communicate == communicate do
    throw (.invalidProgram "source environment/std-only target or communication mismatch")
  let dispatchers := UnixForeign.environmentStdOnlySource target.os target.env
    communicate
    (fun name abi args dest => UnixEnvironmentDispatch.dispatch environment name abi args dest)
    (fun name abi args dest => StdOnlyShims.unix stdOnly name abi args dest)
  assembleSourceOrder p common spans mathHooks dispatchers choice CallbackSeed

/-- Compatibility projection for code that only needs ForeignItems hooks. -/
def fromEnvironmentStdOnlySource
    (p : CompilerProviders.Prepared)
    (common : EvalForeignConstruction.Common
      (State Os R P H D Aff B Poll Instant System Native Profiler Raw Listener TcpStream Error))
    (spans : AllocationDriver.SpanHooks)
    (mathHooks : Math.Hooks Provenance
      (State Os R P H D Aff B Poll Instant System Native Profiler Raw Listener TcpStream Error)
      C (RuntimePlace Provenance))
    (environment : UnixEnvironmentDispatch.Hooks
      (State Os R P H D Aff B Poll Instant System Native Profiler Raw Listener TcpStream Error)
      Os Error EnvVars.Kind)
    (stdOnly : StdOnlyShims.Hooks Provenance
      (State Os R P H D Aff B Poll Instant System Native Profiler Raw Listener TcpStream Error)
      Place (MPlaceTy Provenance) LoadedBody CallInstance)
    (communicate : Bool) (choice : C) :
    M Os R P H D Aff B Poll Instant System Native Profiler Raw Listener TcpStream Error
      (ForeignItems.Hooks Provenance
        (State Os R P H D Aff B Poll Instant System Native Profiler Raw Listener TcpStream Error)
        (RuntimePlace Provenance) (RuntimePlace Provenance)
        (Pointer (Option Provenance)) LoadedBody CallInstance) := do
  return (← fromEnvironmentStdOnlyPackage p common spans mathHooks environment stdOnly communicate choice).foreign

/-- Build the ordered Unix call resolver around the actual nonrecursive
foreign Core and the source dispatcher components. The exact Unix source
resolver is shared with `UnixForeign.dispatch`; the only currently unported
outer portable category is explicitly Unsupported when ForeignItems selects
it. Unrecognized names still continue through Unix source fallback and then
the compiler symbol resolver. -/
def unixFromSource
    (p : CompilerProviders.Prepared)
    (common : EvalForeignConstruction.Common
      (State Os R P H D Aff B Poll Instant System Native Profiler Raw Listener TcpStream Error))
    (spans : AllocationDriver.SpanHooks)
    (mathHooks : Math.Hooks Provenance
      (State Os R P H D Aff B Poll Instant System Native Profiler Raw Listener TcpStream Error)
      C (RuntimePlace Provenance))
    (components : EvalUnixSourceConstruction.DispatchComponents
      Os R P H D Aff B Poll Instant System Native Profiler Raw Listener TcpStream Error
      Meta Path Place C ClockHost I)
    (choice : C)
    (pollBudget : Nat) :
    M Os R P H D Aff B Poll Instant System Native Profiler Raw Listener TcpStream Error
      (ForeignItems.Hooks Provenance
        (State Os R P H D Aff B Poll Instant System Native Profiler Raw Listener TcpStream Error)
        (RuntimePlace Provenance) (RuntimePlace Provenance)
        (Pointer (Option Provenance)) LoadedBody CallInstance) := do
  let target ← match p.externStatics.targetFacts with
    | .ok facts => pure facts
    | .error reason => throw (.unsupported s!"foreign source target facts: {reason}")
  let arch ← match EvalArchitectureMachine.targetArch p.intrinsics with
    | .ok arch => pure arch
    | .error reason => throw (.unsupported s!"foreign source target architecture: {reason}")
  unless target.families.contains "unix" && common.options.family == .unix &&
      common.options.os == target.os && common.options.arch == arch do
    throw (.invalidProgram "foreign Core target differs from prepared Unix compiler target")
  let dispatchers ← match EvalUnixSourceConstruction.dispatchers p components pollBudget with
    | .ok value => pure value
    | .error error => throw error
  let core ← EvalForeignConstruction.core common spans
  unless core.family == .unix && core.os == target.os && core.arch == arch &&
      core.maximumSize == components.stdOnly.foreign.maximumSize &&
      core.noAllocShimSymbol == components.stdOnly.foreign.noAllocShimSymbol &&
      core.nativeEnabled == components.stdOnly.foreign.nativeEnabled do
    throw (.invalidProgram "foreign Core and Unix source dispatcher differ")
  let unixCore : ForeignItems.Core Provenance
      (State Os R P H D Aff B Poll Instant System Native Profiler Raw Listener TcpStream Error)
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
      memoryDestination (← core.forceAllocation destination)
  }
  let unix := fun name abi args destination => do
    let destination ← memoryDestination destination
    UnixForeign.dispatchSource dispatchers unixCore name abi args destination
  let mathHandler := fun name abi args destination =>
    EvalForeignConstruction.math mathHooks core choice name abi args destination
  let windows := fun _ _ _ _ =>
    throw (.invalidProgram "Windows foreign arm reached from Unix source factory")
  let otherPortable := fun name _ _ _ =>
    throw (.unsupported s!"portable foreign shim `{name}` has no connected source constructor")
  pure (EvalForeignConstruction.assemble core mathHandler unix windows otherPortable)

/-- End-to-end Unix foreign call factory. It obtains symbol tables, target
identity, allocator policy, common source bodies and ordered dispatchers from
the prepared compiler plus the actual execution machine components. The only
effects left as arguments are native-library host calls and the already
source-constructed Unix component bundle. -/
def fromSource
    (p : CompilerProviders.Prepared)
    (native : EvalForeignConstruction.HostEffects
      (State Os R P H D Aff B Poll Instant System Native Profiler Raw Listener TcpStream Error))
    (access : ValidityMachine.Access MiriMemoryKind
      (EvalForeignConstruction.Stored Os R P H D
        (EvalUnixSourceConstruction.Other Raw Listener TcpStream Error) Aff B
        (EvalSyncMachine.Host Poll Instant System H D
          (EvalUnixSourceConstruction.Other Raw Listener TcpStream Error) Native Profiler)))
    (allocation : PlaceMachine.AllocationConfig MiriMemoryKind
      (EvalForeignConstruction.User Os R P H D
        (EvalUnixSourceConstruction.Other Raw Listener TcpStream Error) Aff B
        (EvalSyncMachine.Host Poll Instant System H D
          (EvalUnixSourceConstruction.Other Raw Listener TcpStream Error) Native Profiler)))
    (extras : MemoryExtras.Hooks MiriMemoryKind
      (EvalForeignConstruction.User Os R P H D
        (EvalUnixSourceConstruction.Other Raw Listener TcpStream Error) Aff B
        (EvalSyncMachine.Host Poll Instant System H D
          (EvalUnixSourceConstruction.Other Raw Listener TcpStream Error) Native Profiler)) P)
    (deallocationDiagnostic : AllocId → PlaceMachine.MachineM MiriMemoryKind
      (EvalForeignConstruction.User Os R P H D
        (EvalUnixSourceConstruction.Other Raw Listener TcpStream Error) Aff B
        (EvalSyncMachine.Host Poll Instant System H D
          (EvalUnixSourceConstruction.Other Raw Listener TcpStream Error) Native Profiler)) Unit)
    (nativeDrop : Option (Allocation Provenance Miri.TreeBorrows.BorrowTree →
      MachineHooks.M MiriMemoryKind
        (EvalForeignConstruction.User Os R P H D
          (EvalUnixSourceConstruction.Other Raw Listener TcpStream Error) Aff B
          (EvalSyncMachine.Host Poll Instant System H D
            (EvalUnixSourceConstruction.Other Raw Listener TcpStream Error) Native Profiler)) Unit))
    (pointer : PointerMachine.Hooks MiriMemoryKind
      (ValidityMachine.Control (EvalForeignConstruction.Stored Os R P H D
        (EvalUnixSourceConstruction.Other Raw Listener TcpStream Error) Aff B
        (EvalSyncMachine.Host Poll Instant System H D
          (EvalUnixSourceConstruction.Other Raw Listener TcpStream Error) Native Profiler))))
    (spans : AllocationDriver.SpanHooks)
    (place : PlaceHooks Provenance
      (State Os R P H D Aff B Poll Instant System Native Profiler Raw Listener TcpStream Error)
      C MachineHooks.FrameExtra)
    (callFunction : C → CallInstance → Array (RvalueImmTy Provenance) → ReturnContinuation →
      M Os R P H D Aff B Poll Instant System Native Profiler Raw Listener TcpStream Error Unit)
    (choice : C) (mathHooks : Math.Hooks Provenance
      (State Os R P H D Aff B Poll Instant System Native Profiler Raw Listener TcpStream Error)
      C (RuntimePlace Provenance))
    (components : EvalUnixSourceConstruction.DispatchComponents
      Os R P H D Aff B Poll Instant System Native Profiler Raw Listener TcpStream Error
      Meta Path Place C ClockHost I)
    (compatibilityBudget pollBudget : Nat) (debugAssertions : Bool) :
    M Os R P H D Aff B Poll Instant System Native Profiler Raw Listener TcpStream Error
      (ForeignItems.Hooks Provenance
        (State Os R P H D Aff B Poll Instant System Native Profiler Raw Listener TcpStream Error)
        (RuntimePlace Provenance) (RuntimePlace Provenance)
        (Pointer (Option Provenance)) LoadedBody CallInstance) := do
  let target ← match p.externStatics.targetFacts with
    | .ok facts => pure facts
    | .error reason => throw (.unsupported s!"foreign source target facts: {reason}")
  unless target.families.contains "unix" do
    throw (.unsupported "source foreign factory currently requires a Unix compiler target")
  let arch ← match EvalArchitectureMachine.targetArch p.intrinsics with
    | .ok arch => pure arch
    | .error reason => throw (.unsupported s!"foreign source target architecture: {reason}")
  let sourceSymbols ← match p.foreignSymbols with
    | .ok symbols => pure symbols
    | .error reason => throw (.unsupported s!"compiler foreign-symbol query: {reason}")
  let symbols := CompilerForeignSymbols.hooks sourceSymbols p.lifecycle.calls
  let options : EvalForeignConstruction.Options := {
    family := .unix
    os := target.os
    arch
    noAllocShimSymbol := sourceSymbols.noAllocShimSymbol
    compatibilityBudget
    debugAssertions }
  let common ← match EvalForeignConstruction.common p options symbols native access allocation extras
      deallocationDiagnostic nativeDrop pointer spans place callFunction choice with
    | .ok common => pure common
    | .error error => throw error
  unixFromSource p common spans mathHooks components choice pollBudget

/-- Production source entry for the currently connected Unix families. It
derives environment and std-only hooks from the typed host seed and the exact
live Core memory/function providers. All other recognized Unix operations are
kept in the ordered resolver as explicit demand-local Unsupported arms. -/
def fromSeedEnvironment [DecidableEq MiriMemoryKind]
    (p : CompilerProviders.Prepared)
    (nativeLibraryPaths : (State Os R EvalSyncPayload.Payload H D Aff B Poll Instant System Native Profiler Raw Listener TcpStream Error) → Array String)
    (callNative : String → MPlaceTy Provenance → Array (OpTy Provenance) →
      M Os R EvalSyncPayload.Payload H D Aff B Poll Instant System Native Profiler Raw Listener TcpStream Error Bool)
    (access : ValidityMachine.Access MiriMemoryKind
      (EvalForeignConstruction.Stored Os R EvalSyncPayload.Payload H D
        (Other Raw Listener TcpStream Error) Aff B
        (EvalSyncMachine.Host Poll Instant System H D (Other Raw Listener TcpStream Error) Native Profiler)))
    (accessConfig : PlaceMachine.AccessConfig MiriMemoryKind
    (SourceUser Os R H D Aff B Poll Instant System Native Profiler Raw Listener TcpStream Error))
    (allocation : PlaceMachine.AllocationConfig MiriMemoryKind
    (SourceUser Os R H D Aff B Poll Instant System Native Profiler Raw Listener TcpStream Error))
    (compiler : PlaceMachine.CompilerHooks MiriMemoryKind
      (SourceUser Os R H D Aff B Poll Instant System Native Profiler Raw Listener TcpStream Error) C)
    (projection : PlaceProjectionHooks Provenance
      (State Os R EvalSyncPayload.Payload H D Aff B Poll Instant System Native Profiler Raw Listener TcpStream Error) C MachineHooks.FrameExtra)
    (extras : MemoryExtras.Hooks MiriMemoryKind
      (SourceUser Os R H D Aff B Poll Instant System Native Profiler Raw Listener TcpStream Error) EvalSyncPayload.Payload)
    (deallocationDiagnostic : AllocId → PlaceMachine.MachineM MiriMemoryKind
      (SourceUser Os R H D Aff B Poll Instant System Native Profiler Raw Listener TcpStream Error) Unit)
    (nativeDrop : Option (Allocation Provenance Miri.TreeBorrows.BorrowTree →
      MachineHooks.M MiriMemoryKind
        (SourceUser Os R H D Aff B Poll Instant System Native Profiler Raw Listener TcpStream Error) Unit))
    (pointer : PointerMachine.Hooks MiriMemoryKind
      (ValidityMachine.Control (EvalForeignConstruction.Stored Os R EvalSyncPayload.Payload H D
        (Other Raw Listener TcpStream Error) Aff B
        (EvalSyncMachine.Host Poll Instant System H D (Other Raw Listener TcpStream Error) Native Profiler))))
    (spans : AllocationDriver.SpanHooks)
    (functions : FunctionPointers.Hooks MiriMemoryKind
      (SourceUser Os R H D Aff B Poll Instant System Native Profiler Raw Listener TcpStream Error) (Other Raw Listener TcpStream Error))
    (place : PlaceHooks Provenance
      (State Os R EvalSyncPayload.Payload H D Aff B Poll Instant System Native Profiler Raw Listener TcpStream Error) C MachineHooks.FrameExtra)
    (callFunction : C → CallInstance → Array (RvalueImmTy Provenance) → ReturnContinuation →
      M Os R EvalSyncPayload.Payload H D Aff B Poll Instant System Native Profiler Raw Listener TcpStream Error Unit)
    (choice : C)
    (mathHooks : Math.Hooks Provenance
      (State Os R EvalSyncPayload.Payload H D Aff B Poll Instant System Native Profiler Raw Listener TcpStream Error) C (RuntimePlace Provenance))
    (threadFunctions : Unit → Except StepError
      (FunctionCalls.Hooks Provenance
        (MachineHooks.State MiriMemoryKind
          (ExecutionStateTransport.Outer
            (EvalCoreMachine.World Os R EvalSyncPayload.Payload H D
              (Other Raw Listener TcpStream Error) Aff B
              (EvalSyncMachine.Host Poll Instant System H D
                (Other Raw Listener TcpStream Error) Native Profiler))))
        C MachineHooks.FrameExtra (Other Raw Listener TcpStream Error)
        ABI.ExternAbi (FnAbi TyId) (ArgAbi TyId)))
    (host : HostSeed Os R H D Aff B Poll Instant System Native Profiler
      Raw Listener TcpStream Error ErrorHost Meta Path AddrIter)
    (hostConfiguration : HostRuntime.Configuration)
    (memory : EvalHostRuntimeConstruction.EnvironmentMemory
      (ValidityMachine.Control (EvalCoreMachine.Stored Os R EvalSyncPayload.Payload H D
        (Other Raw Listener TcpStream Error) Aff B
        (HostRuntime.Storage Poll Instant System H D (Other Raw Listener TcpStream Error) Native Profiler)))
      C EvalSyncPayload.Payload)
    (bytes : CompilerGlobalBytes.Prepared)
    (geometry : InitialMachine.Geometry)
    (userRelevantCrates : Array Nat)
    (compatibilityBudget : Nat)
    (fileReferenceBudget watcherReferenceBudget : Nat)
    (debugAssertions : Bool) (hostUsizeBits stringScanBudget : Nat)
    (shortFdOperations : Bool) (varArgsBudget : Nat) :
    M Os R EvalSyncPayload.Payload H D Aff B Poll Instant System Native Profiler Raw Listener TcpStream Error
      (SourceAssembly Os R EvalSyncPayload.Payload H D Aff B Poll Instant System Native Profiler Raw Listener TcpStream Error C
        (SourceCallbackSeed Os R H D Aff B Poll Instant System Native Profiler Raw Listener TcpStream Error
          Meta Path Miri.MIR.Place C
          (Clock.HostHooks Instant System (State Os R EvalSyncPayload.Payload H D Aff B Poll Instant System Native Profiler Raw Listener TcpStream Error))
          CallInstance AddrIter)) := do
  let target ← match p.externStatics.targetFacts with
    | .ok facts => pure facts
    | .error reason => throw (.unsupported s!"foreign source target facts: {reason}")
  unless target.families.contains "unix" do
    throw (.unsupported "source foreign factory currently requires a Unix compiler target")
  let arch ← match EvalArchitectureMachine.targetArch p.intrinsics with
    | .ok arch => pure arch
    | .error reason => throw (.unsupported s!"foreign source target architecture: {reason}")
  let sourceSymbols ← match p.foreignSymbols with
    | .ok symbols => pure symbols
    | .error reason => throw (.unsupported s!"compiler foreign-symbol query: {reason}")
  let symbols := CompilerForeignSymbols.hooks sourceSymbols p.lifecycle.calls
  let options : EvalForeignConstruction.Options := {
    family := .unix
    os := target.os
    arch
    noAllocShimSymbol := sourceSymbols.noAllocShimSymbol
    compatibilityBudget
    debugAssertions }
  let environment ← match EvalUnixConstruction.environmentFromRuntime p userRelevantCrates
      compatibilityBudget host.os host.environment host.unixConfig host.ioError memory with
    | .ok environment => pure environment
    | .error error => throw error
  let native : EvalForeignConstruction.HostEffects
      (State Os R EvalSyncPayload.Payload H D Aff B Poll Instant System Native Profiler Raw Listener TcpStream Error) := {
    nativeLibraryPaths
    callNative
    setEnomem := IoError.setLastError environment.env.errors (.libc "ENOMEM") }
  let common ← match EvalForeignConstruction.common p options symbols native access allocation extras
      deallocationDiagnostic nativeDrop pointer spans place callFunction choice with
    | .ok common => pure common
    | .error error => throw error
  let foreignCore ← EvalForeignConstruction.core common spans
  let stdForeignCore : ForeignItems.Core Provenance
      (State Os R EvalSyncPayload.Payload H D Aff B Poll Instant System Native Profiler Raw Listener TcpStream Error)
      Miri.MIR.Place (MPlaceTy Provenance)
      (Pointer (Option Provenance)) LoadedBody CallInstance := {
    family := foreignCore.family
    os := foreignCore.os
    arch := foreignCore.arch
    maximumSize := foreignCore.maximumSize
    noAllocShimSymbol := foreignCore.noAllocShimSymbol
    allocatorSymbol := foreignCore.allocatorSymbol
    lookupFunction := foreignCore.lookupFunction
    forceAllocation := fun _ => throw (.unsupported "std-only force-allocation adapter is not connected")
    returnToBlock := foreignCore.returnToBlock
    unwindToBlock := foreignCore.unwindToBlock
    nativeEnabled := foreignCore.nativeEnabled
    callNative := fun name destination args =>
      foreignCore.callNative name (RuntimePlace.mk (.memory destination.mplace) destination.layout) args
    expectedAbi := foreignCore.expectedAbi
    argumentCompat := foreignCore.argumentCompat
    checkSymbolClash := foreignCore.checkSymbolClash
    transmute := foreignCore.transmute
    readUsize := foreignCore.readUsize
    readPointer := foreignCore.readPointer
    readI32 := foreignCore.readI32
    isNull := foreignCore.isNull
    allocate := foreignCore.allocate
    deallocate := foreignCore.deallocate
    reallocate := foreignCore.reallocate
    writePointer := fun pointer destination =>
      foreignCore.writePointer pointer (RuntimePlace.mk (.memory destination.mplace) destination.layout)
    writeNull := fun destination =>
      foreignCore.writeNull (RuntimePlace.mk (.memory destination.mplace) destination.layout)
    setEnomem := foreignCore.setEnomem
    startExit := foreignCore.startExit
    specialDestination := fun _ => throw (.unsupported "std-only special-destination adapter is not connected") }
  let stdOnly ← match EvalUnixSourceConstruction.stdOnlyFromRuntime
      (Os := Os) (R := R) (P := EvalSyncPayload.Payload) (H := H) (D := D)
      (Aff := Aff) (MirBody := LoadedBody) (Poll := Poll) (Instant := Instant)
      (System := System) (Native := Native) (Profiler := Profiler)
      (Raw := Raw) (Listener := Listener) (TcpStream := TcpStream) (Error := Error)
      (C := C) (I := CallInstance) p userRelevantCrates
      accessConfig allocation compiler projection access choice environment bytes functions
      geometry.pageSize geometry.stackAddress geometry.stackSize stdForeignCore with
    | .ok stdOnly => pure stdOnly
    | .error error => throw error
  let assembly ← fromEnvironmentStdOnlyPackage p common spans mathHooks environment stdOnly
    host.unixConfig.communicate choice
    (SourceCallbackSeed Os R H D Aff B Poll Instant System Native Profiler Raw Listener TcpStream Error
      Meta Path Miri.MIR.Place C
      (Clock.HostHooks Instant System (State Os R EvalSyncPayload.Payload H D Aff B Poll Instant System Native Profiler Raw Listener TcpStream Error))
      CallInstance AddrIter)
  let registry := EvalCallbackSocketConstruction.registrySeed hostUsizeBits
    fileReferenceBudget watcherReferenceBudget host.fileResources
  let events : EventFdMachine.Store
      (EvalOwnedIoMachine.User Os R EvalSyncPayload.Payload H D
        (Other Raw Listener TcpStream Error) Aff B Poll Instant System Native Profiler)
      (Other Raw Listener TcpStream Error) :=
    EvalOwnedIoMachine.eventStore SourceOther.eventTag SourceOther.eventProject
  unless hostConfiguration.communicate == host.unixConfig.communicate do
    throw (.invalidProgram "Native FD source configuration disagrees with HostRuntime")
  let validateOther := fun (reference : Files.Ref
      (Files.Description H D (Other Raw Listener TcpStream Error))) => do
    let ownership := registry.files.ownership (← get).machine.user
    let entries := ownership.entries.filter (·.ref.id == reference.id)
    unless entries.size == 1 do
      throw (.invalidProgram "source OtherFile operation received absent or ambiguous descriptor")
    let some entry := entries[0]? | throw (.invalidProgram "source OtherFile ownership lookup failed")
    unless entry.strong > 0 do throw (.invalidProgram "source OtherFile operation received stale descriptor")
  let otherFiles : EvalUnixIoConstruction.OtherFileEffects
      (State Os R EvalSyncPayload.Payload H D Aff B Poll Instant System Native Profiler Raw Listener TcpStream Error)
      H D (Other Raw Listener TcpStream Error) Error := {
    read := fun reference _ _ _ _ => do
      validateOther reference
      match reference.value with
      | .other payload =>
        if (events.untag payload).isSome then
          throw (.unsupported "source eventfd operations are not attached before readiness assembly")
        else if (SourceOther.sockets.project payload).isSome then
          throw (.unsupported "source socket read operation has no attached capability")
        else throw (.invalidProgram "unrecognized source OtherFile payload")
      | _ => throw (.invalidProgram "non-Other descriptor reached OtherFile read")
    write := fun reference _ _ _ _ => do
      validateOther reference
      match reference.value with
      | .other payload =>
        if (events.untag payload).isSome then
          throw (.unsupported "source eventfd operations are not attached before readiness assembly")
        else if (SourceOther.sockets.project payload).isSome then
          throw (.unsupported "source socket write operation has no attached capability")
        else throw (.invalidProgram "unrecognized source OtherFile payload")
      | _ => throw (.invalidProgram "non-Other descriptor reached OtherFile write")
    shortOperations := fun _ => false
    readiness := fun payload => do
      if (events.untag payload).isSome then
        let some id := events.untag payload | throw (.invalidProgram "eventfd tag changed during readiness lookup")
        let entries := (events.get (← get).machine.user).filter (·.1 == id)
        unless entries.size == 1 do throw (.invalidProgram "eventfd readiness state absent or ambiguous")
        let some (_,value) := entries[0]? | throw (.invalidProgram "eventfd readiness state missing")
        pure (some (EventFd.readiness value))
      else if (SourceOther.sockets.project payload).isSome then
        throw (.unsupported "source socket readiness has no attached capability")
      else throw (.invalidProgram "unrecognized source OtherFile readiness payload")
    hasReadinessWatched := fun payload =>
      (events.untag payload).isSome ||
        (SourceOther.sockets.project payload).isSome
    isTerminal := fun _ _ => pure false }
  let files ← match EvalUnixIoConstruction.filesFromSource p memory.access memory.pointers
      host.hostFiles otherFiles with
    | .ok files => pure files
    | .error error => throw error
  let sourceEffects ← EvalCallbackSyncConstruction.sourceEffects
      p.lifecycle.calls.symbols.facts hostConfiguration place choice host.sync
  let typedRuntime ← EvalTypedSyncMachine.runtime sourceEffects
  let unsupportedRuntime {A : Type} (message : String) :
      EStateM StepError
        (State Os R EvalSyncPayload.Payload H D Aff B Poll Instant System Native Profiler Raw Listener TcpStream Error) A :=
    throw (.unsupported s!"source readiness sync operation `{message}` is not connected")
  let syncRuntime : Miri.Concurrency.SyncRuntime.Hooks
      (State Os R EvalSyncPayload.Payload H D Aff B Poll Instant System Native Profiler Raw Listener TcpStream Error)
      Nat Int32 (MPlaceTy Provenance) := {
    handler := typedRuntime.handler
    usizeBits := typedRuntime.usizeBits
    communicate := typedRuntime.communicate
    global := typedRuntime.global
    putGlobal := typedRuntime.putGlobal
    threads := typedRuntime.threads
    putThreads := typedRuntime.putThreads
    callbackBackend := .typed
      (fun _ => unsupportedRuntime "callback-register")
      (fun _ _ => unsupportedRuntime "callback-run")
      (fun _ => unsupportedRuntime "callback-cancel")
      (fun _ => pure false)
    mutex := fun _ => unsupportedRuntime "mutex"
    putMutex := fun _ _ => unsupportedRuntime "put-mutex"
    rwlock := fun _ => unsupportedRuntime "rwlock"
    putRwlock := fun _ _ => unsupportedRuntime "put-rwlock"
    condvar := fun _ => unsupportedRuntime "condvar"
    putCondvar := fun _ _ => unsupportedRuntime "put-condvar"
    futex := fun _ => unsupportedRuntime "futex"
    putFutex := fun _ _ => unsupportedRuntime "put-futex"
    semaphore := fun _ => unsupportedRuntime "semaphore"
    putSemaphore := fun _ _ => unsupportedRuntime "put-semaphore"
    writeScalar := fun _ _ => unsupportedRuntime "write-scalar"
    error := SyncMachine.sourceError }
  let readinessRoute : EvalUnixFdConstruction.ReadinessRoute
      (State Os R EvalSyncPayload.Payload H D Aff B Poll Instant System Native Profiler Raw Listener TcpStream Error) := {
    runtime := syncRuntime
    debugAssertions
    unblock := fun _ _ => throw (.unsupported "source readiness wake requires the ordinary callback router") }
  let physicalReadiness := EvalUnixFdConstruction.readinessFromFiles
      registry.readiness files readinessRoute
  let eventLibcI32 : String → EStateM StepError
      (State Os R EvalSyncPayload.Payload H D Aff B Poll Instant System Native Profiler Raw Listener TcpStream Error) Int32 :=
    fun name => do
      let scalar : Scalar Provenance ← match CompilerNamedConstants.scalar p.namedConstants name with
        | .ok value => pure value
        | .error reason => throw (.unsupported s!"compiler libc constant `{name}`: {reason}")
      match scalar.toInt32 with
      | .ok value => pure value
      | .error error => throw (ScalarOps.scalarError error)
  let eventU64Layout : EStateM StepError
      (State Os R EvalSyncPayload.Payload H D Aff B Poll Instant System Native Profiler Raw Listener TcpStream Error) LocalLayout := do
    match p.primitiveLayout "u64" with
    | .ok value => pure value
    | .error reason => throw (.unsupported s!"compiler u64 layout for eventfd: {reason}")
  let eventPhysical := EvalCallbackSocketConstruction.eventPhysicalFromSeed registry physicalReadiness
    fileReferenceBudget accessConfig memory.projection.place choice eventLibcI32 eventU64Layout
  let event : EventFd.Hooks
      (State Os R EvalSyncPayload.Payload H D Aff B Poll Instant System Native Profiler Raw Listener TcpStream Error)
      (Files.Ref (Files.Description H D (Other Raw Listener TcpStream Error))) :=
    { toPhysicalHooks := eventPhysical
      deferred := .typed
        (fun _ _ _ => throw (.unsupported "source eventfd deferred read callback is not connected"))
        (fun _ _ _ => throw (.unsupported "source eventfd deferred write callback is not connected")) }
  let errorFromKind : IoError.ErrorKind → EStateM StepError
      (State Os R EvalSyncPayload.Payload H D Aff B Poll Instant System Native Profiler Raw Listener TcpStream Error)
      (IoError.Error Error) := fun kind => do
    pure (.host (← host.ioError.hostFromKind kind))
  let blocking := EvalCallbackSocketConstruction.blockingFromSeed registry physicalReadiness host.socket
  let (virtualSocket,tcpSocket) ← match EvalCallbackSocketConstruction.protocolsFromSeed p
      registry physicalReadiness blocking host.socket environment.env.errors host.os.hostWindows
      accessConfig memory.pointers.arithmetic memory.projection.place memory.projection choice
      fileReferenceBudget with
    | .ok protocols => pure protocols
    | .error error => throw error
  /- Break the file/readiness/protocol construction cycle by making the
  socket-tag query derive from the canonical virtual/TCP stores. The
  provisional `physicalReadiness` remains the fallback for ordinary host
  descriptors and supplies only ownership/runtime operations to virtual
  readiness; socket notifications and final FileDescription queries use this
  source protocol view. -/
  let socketReadiness := SocketMachine.bindReadiness registry.readiness
      (EvalCallbackSocketConstruction.socketDescriptor Raw Listener TcpStream Error)
      EvalSocketStorage.sockets virtualSocket physicalReadiness
  let virtualSocket := {virtualSocket with readiness := socketReadiness}
  let tcpSocket := {tcpSocket with io := {tcpSocket.io with readiness := socketReadiness}}
  let socketFiles := EvalCallbackSocketConstruction.socketFileEffects
      fileReferenceBudget virtualSocket tcpSocket
  let finalEventPhysical := EvalCallbackSocketConstruction.eventPhysicalFromSeed registry
    socketReadiness fileReferenceBudget accessConfig memory.projection.place choice
    eventLibcI32 eventU64Layout
  let event : EventFd.Hooks
      (State Os R EvalSyncPayload.Payload H D Aff B Poll Instant System Native Profiler Raw Listener TcpStream Error)
      (Files.Ref (Files.Description H D (Other Raw Listener TcpStream Error))) := {
    toPhysicalHooks := finalEventPhysical
    deferred := .typed
      (fun _ _ _ => throw (.unsupported "source eventfd deferred read callback is not connected"))
      (fun _ _ _ => throw (.unsupported "source eventfd deferred write callback is not connected")) }
  let otherFiles := EvalCallbackSocketConstruction.otherFileEffects registry event
      (some socketFiles) fileReferenceBudget errorFromKind
  let files ← match EvalUnixIoConstruction.filesFromSource p memory.access memory.pointers
      host.hostFiles otherFiles with
    | .ok files => pure files
    | .error error => throw error
  let unixPollAndUnblockZero := throw
    (.unsupported "source Unix pre-dispatch poll requires the ordinary callback router")
  let choiceTape : ExecutionChoices.Access
      (State Os R EvalSyncPayload.Payload H D Aff B Poll Instant System Native Profiler Raw Listener TcpStream Error) :=
    EvalCoreMachine.tape
  let positional := EvalCallbackSocketConstruction.otherPositionalEffects registry
  let unixFd ← match EvalUnixIoConstruction.unixFdFromSource p
      hostConfiguration.communicate shortFdOperations hostUsizeBits registry.readiness
      readinessRoute files environment.env.errors memory.access
      (UnixFdChoices.randomShort choiceTape)
      memory.projection.place choice positional.read positional.write with
    | .ok fd => pure fd
    | .error error => throw error
  let openHooks : UnixOpen.Hooks
      (State Os R EvalSyncPayload.Payload H D Aff B Poll Instant System Native Profiler Raw Listener TcpStream Error)
      H D (Other Raw Listener TcpStream Error) Error Meta Path := {
    fd := unixFd
    hostWindows := host.os.hostWindows
    flag := fun flag => do
      let key := match flag with
        | .readonly => "O_RDONLY" | .writeonly => "O_WRONLY" | .readwrite => "O_RDWR"
        | .accessMode => "O_ACCMODE" | .largefile => "O_LARGEFILE" | .tmpfile => "O_TMPFILE"
        | .directory => "O_DIRECTORY" | .append => "O_APPEND" | .trunc => "O_TRUNC"
        | .create => "O_CREAT" | .exclusive => "O_EXCL" | .cloexec => "O_CLOEXEC"
        | .nofollow => "O_NOFOLLOW" | .atCwd => "AT_FDCWD"
      let constant : Except String (Scalar Provenance) := CompilerNamedConstants.scalar p.namedConstants key
      match constant with
      | .ok value => match value.toUInt32 with
        | .ok value => pure value
        | .error error => throw (ScalarOps.scalarError error)
      | .error reason => throw (.unsupported s!"compiler libc constant `{key}`: {reason}")
    hostCustomFlag := host.openFiles.hostCustomFlag
    readMode := fun _ => throw (.unsupported "open mode requires source variadic argument validation")
    isolationReject := fun name => do
      match host.unixConfig.isolatedOp with
      | .allow => pure false
      | .reject .abort => throw (.termination (.unsupportedInIsolation name))
      | .reject .noWarning | .reject .warning | .reject .warningWithoutBacktrace => pure true
    procAbsolute := host.openFiles.procAbsolute
    diagnoseProc := host.openFiles.diagnoseProc
    isAbsolute := host.openFiles.isAbsolute
    isEmpty := host.openFiles.isEmpty
    isDot := host.openFiles.isDot
    emptyPath := host.openFiles.emptyPath
    openFile := host.openFiles.openFile
    openDirectoryAsFile := host.openFiles.openDirectoryAsFile
    metadata := host.openFiles.metadata
    asDirectory := host.openFiles.asDirectory
    dropFile := host.fileResources.dropFile
    dropDirectory := host.fileResources.dropDirectory
    permissionDenied := environment.env.errors.hostFromKind .PermissionDenied
    hostUsizeBits }
  let transmuteProjection := place.projection choice
  let transmute := fun operand target => do
    let projection ← transmuteProjection
    match operand.transmute projection target |>.mapError IntrinsicVectorMachine.projectionError with
    | .ok value => pure value
    | .error error => throw error
  let callCompiler := CompilerCallConstruction.compiler p compatibilityBudget
  let fdDispatch : UnixFdDispatch.Hooks
      (State Os R EvalSyncPayload.Payload H D Aff B Poll Instant System Native Profiler Raw Listener TcpStream Error)
      H D (Other Raw Listener TcpStream Error) Error Meta Path := {
    file := openHooks
    expectedAbi := fun name request => do
      let some operation := UnixFdDispatch.parse name |
        throw (.unsupported s!"Unix FD ABI requested for unselected symbol `{name}`")
      let expected := UnixFdDispatch.signature operation
      unless expected.args == request.args && expected.ret == request.ret && expected.variadic == request.variadic do
        throw (.invalidProgram s!"Unix FD signature recipe disagrees with `{name}`")
      CompilerNamedShimAbi.query p.namedAbi name
    argumentCompat := callCompiler.checkArgumentCompat choice
    checkSymbolClash := fun name =>
      match CompilerForeignSymbols.checkSymbolClash sourceSymbols name with
      | .ok () => pure () | .error error => throw error
    transmute
    readI32 := sourceReadI32 memory.access
    readUsize := sourceReadUsize memory.access
    readOffset := sourceReadOffset memory.access
    readPointer := sourceReadPointer memory.access
    readPath := fun pointer => do
      let osPath ← OsStrings.readPath environment.env.strings pointer
      pure (host.openFiles.pathFromOs osPath)
    readMode := fun _ _ _ => throw (.unsupported "open mode requires source variadic argument validation")
    pollAndUnblockZero := unixPollAndUnblockZero }
  let fdDispatch := {fdDispatch with file :=
    {fdDispatch.file with fd := UnixFdChoices.bind choiceTape fdDispatch.file.fd}}
  let fdSignatureForeign : ForeignItems.Hooks Provenance
      (State Os R EvalSyncPayload.Payload H D Aff B Poll Instant System Native Profiler Raw Listener TcpStream Error)
      Miri.MIR.Place (MPlaceTy Provenance) (Pointer (Option Provenance)) LoadedBody CallInstance := {
    toCore := stdForeignCore
    math := fun name _ _ _ => throw (.unsupported s!"source FD signature math fallback `{name}`")
    unix := fun name _ _ _ => throw (.unsupported s!"source FD signature Unix fallback `{name}`")
    windows := fun name _ _ _ => throw (.unsupported s!"source FD signature Windows fallback `{name}`")
    otherPortable := fun name _ _ _ => throw (.unsupported s!"source FD signature portable fallback `{name}`") }
  let compilerFacts := p.lifecycle.calls.symbols.facts.context
  let fdSignatures : ShimSignatures.Hooks Provenance
      (State Os R EvalSyncPayload.Payload H D Aff B Poll Instant System Native Profiler Raw Listener TcpStream Error)
      Miri.MIR.Place (MPlaceTy Provenance) (Pointer (Option Provenance)) LoadedBody CallInstance :=
    CompilerShimSignatures.hooks compilerFacts {
      foreign := fdSignatureForeign
      types := CompilerFacts.compatibilityQueries compilerFacts
      isCVoid := fun ty => match CompilerFacts.boolean compilerFacts ty "is_c_void" with
        | .ok value => pure value
        | .error reason => throw (.unsupported s!"compiler c_void query: {reason}")
      readScalar := sourceReadScalar memory.access
      hostUsizeBits }
  let fdSource : EvalUnixNativeFdConstruction.Components Os R EvalSyncPayload.Payload H D Aff B
      Poll Instant System Native Profiler Raw Listener TcpStream Error Meta Path
      Miri.MIR.Place C
      (Clock.HostHooks Instant System
        (State Os R EvalSyncPayload.Payload H D Aff B Poll Instant System Native Profiler Raw Listener TcpStream Error))
      CallInstance LoadedBody ← match EvalUnixNativeFdConstruction.fromSourceWithLifecycle p
      userRelevantCrates compatibilityBudget varArgsBudget host.os host.openFiles memory
      environment host.fileResources host.hostFiles otherFiles
      (EvalCallbackSocketConstruction.otherPositionalEffects registry)
      host.fileLocks host.control fdSignatures readinessRoute watcherReferenceBudget
      fileReferenceBudget hostUsizeBits shortFdOperations hostUsizeBits
      (UnixFdChoices.randomShort choiceTape) hostConfiguration.communicate
      place choice host.unixConfig.isolatedOp unixPollAndUnblockZero
      (EvalCallbackSocketConstruction.socketDescriptor Raw Listener TcpStream Error)
      virtualSocket tcpSocket host.hostOverflowChecks allocation compiler
      memory.projection spans extras deallocationDiagnostic nativeDrop with
    | .ok value => pure value
    | .error error => throw error
  let unixFdHandler := UnixFdDispatch.dispatch fdDispatch
  let primitiveSignatures : ShimSignatures.PrimitiveHooks Provenance
      (State Os R EvalSyncPayload.Payload H D Aff B Poll Instant System Native Profiler Raw Listener TcpStream Error) := {
    family := assembly.foreign.family
    os := assembly.foreign.os
    checkAbi := ForeignItems.checkAbi assembly.foreign
    checkSymbolClash := assembly.foreign.checkSymbolClash
    transmute := assembly.foreign.transmute }
  let threadTls ← match EvalUnixThreadTlsConstruction.fromSource p environment primitiveSignatures
      accessConfig allocation place choice threadFunctions
      spans functions hostUsizeBits stringScanBudget with
    | .ok value => pure value
    | .error error => throw error
  let unixLinuxSource ← if target.os == "linux" || target.os == "android" then do
      let sourceResult : Except StepError
          (EvalUnixLinuxConstruction.Components
            (State Os R EvalSyncPayload.Payload H D Aff B Poll Instant System Native Profiler
              Raw Listener TcpStream Error)
            Place H D (Other Raw Listener TcpStream Error) Error Meta Path
            LoadedBody CallInstance) :=
        EvalUnixLinuxConstruction.fromSource (ShimBody := LoadedBody) (I := CallInstance)
          p userRelevantCrates environment fdSignatures fdSource.fd threadTls.thread.unixGettid place choice
          geometry.pageSize memory extras spans functions
      let source ← match sourceResult with
        | .ok value => pure value
        | .error error => throw error
      pure (some source)
    else pure none
  let dispatchers := {assembly.dispatchers with
    fd := unixFdHandler
    fdControl := fun name abi args dest => UnixFdControlDispatch.emulate fdSource.control name abi args dest
    vector := fun name abi args dest => UnixVectoredDispatch.emulate fdSource.vector name abi args dest
    pollAndUnblockZero := unixPollAndUnblockZero
    memory := match unixLinuxSource with
      | some source => fun name abi args destination =>
          UnixMemory.emulate source.linuxPlatform.memory.memory name abi args destination
      | none => assembly.dispatchers.memory
    linuxPlatform := match unixLinuxSource with
      | some source => fun name abi args destination => do
          match ← LinuxForeign.emulate source.linuxPlatform name abi args destination with
          | some result => pure (some result)
          | none => assembly.dispatchers.linuxPlatform name abi args destination
      | none => assembly.dispatchers.linuxPlatform
    androidPlatform := match unixLinuxSource with
      | some source => fun name abi args destination => do
          match ← AndroidForeign.emulate source.linuxPlatform name abi args destination with
          | some result => pure (some result)
          | none => assembly.dispatchers.androidPlatform name abi args destination
      | none => assembly.dispatchers.androidPlatform
    thread := fun name abi args destination => do
      match ← UnixThreadDispatch.emulate threadTls.thread name abi args destination with
      | some result => pure result
      | none => assembly.dispatchers.thread name abi args destination
    tls := fun name abi args destination => do
      match ← UnixTlsDispatch.emulate threadTls.tls name abi args destination with
      | some result => pure result
      | none => assembly.dispatchers.tls name abi args destination }
  let assembly := {assembly with dispatchers}
  let assembly := {assembly with environment := some environment}
  let assembly := {assembly with memory := some memory}
  let assembly := {assembly with registry := some registry}
  let callbackSeed : SourceCallbackSeed Os R H D Aff B Poll Instant System Native Profiler
      Raw Listener TcpStream Error Meta Path Miri.MIR.Place C
      (Clock.HostHooks Instant System (State Os R EvalSyncPayload.Payload H D Aff B Poll Instant System Native Profiler Raw Listener TcpStream Error))
      CallInstance AddrIter := {
    nativeFd := fdSource
    registry
    virtual := virtualSocket
    tcp := tcpSocket
    syncEffects := sourceEffects
    errors := environment.env.errors
    readinessRoute }
  pure {assembly with threadTls := some threadTls, callbackSeed := some callbackSeed}

end Miri.Input.EvalCallDispatchConstruction
