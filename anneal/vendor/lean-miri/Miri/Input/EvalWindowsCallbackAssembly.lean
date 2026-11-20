import Miri.Input.EvalCallbackSyncConstruction
import Miri.Input.EvalSyncObjectAccess
import Miri.Input.EvalWindowsCallDispatchConstruction
import Miri.Input.EvalWindowsConfigurationCore
import Miri.Input.EvalConfigurationCore
import Miri.Input.EvalWindowsSyncTimeConstruction
import Miri.Input.EvalWindowsCallbackSourceConstruction
import Miri.Input.CompilerForeignSymbols
import Miri.Input.CompilerLinkSections
import Miri.Input.CompilerPrimitiveFacts
import Miri.Input.CompilerExternStatic
import Miri.Input.EvalTypedSyncMachine
import Miri.Input.EvalSyncMachine
import Miri.Interpreter.ExecutionStateTransport

/-! Construct the Windows callback boundary from the initialized source Core,
its live foreign context, and the same Main hooks. This owns physical typed
synchronization objects and callback routing; it does not seed Unix sockets
or descriptors. Optional host time representations stay existential. -/
namespace Miri.Input.EvalWindowsCallbackAssembly
open Miri.ABI Miri.Memory Miri.MIR Miri.Interpreter Miri.Concurrency

abbrev Other Raw Listener TcpStream Error :=
  EvalWindowsCallDispatchConstruction.Other Raw Listener TcpStream Error
abbrev Host Poll Instant System H D Raw Listener TcpStream Error Native Profiler :=
  EvalWindowsCallDispatchConstruction.Host Poll Instant System H D Raw Listener TcpStream Error Native Profiler
abbrev State Os R H D Aff B Poll Instant System Native Profiler Raw Listener TcpStream Error :=
  EvalWindowsCallDispatchConstruction.State Os R H D Aff B Poll Instant System Native Profiler Raw Listener TcpStream Error
abbrev CoreState Os R H D Aff B Poll Instant System Native Profiler Raw Listener TcpStream Error :=
  EvalWindowsCallDispatchConstruction.CoreState Os R H D Aff B Poll Instant System Native Profiler Raw Listener TcpStream Error

set_option autoImplicit false in
structure Product
    (Os R H D Aff B Poll Instant System Native Profiler Raw Listener TcpStream Error
      C X F A : Type) : Type 1 where
  Zone : Type
  Timestamp : Type
  callbacks : EvalWindowsCallbackSourceConstruction.Product Os R
    EvalSyncObjectAccess.Payload H D (Other Raw Listener TcpStream Error) Aff B
    Poll Instant System Native Profiler C X F A
  objects : ForeignSyncMachine.Objects
    (EvalForeignSyncMachine.State Os R EvalSyncObjectAccess.Payload H D
      (Other Raw Listener TcpStream Error) Aff B Poll Instant System Native Profiler)
  syncEffects : TypedSyncMachine.Effects
    (EvalTypedSyncMachine.State Os R EvalSyncObjectAccess.Payload H D
      (Other Raw Listener TcpStream Error) Aff B Poll Instant System Native Profiler)
  time : TimeShims.Hooks
    (State Os R H D Aff B Poll Instant System Native Profiler Raw Listener TcpStream Error)
    Instant System Zone Timestamp
  deadline : DeadlineMachine.Hooks MiriMemoryKind
    (EvalSyncMachine.User Os R EvalSyncObjectAccess.Payload H D
      (Other Raw Listener TcpStream Error) Aff B Poll Instant System Native Profiler)
    Instant System

private def sourceObjects [DecidableEq MiriMemoryKind] [DecidableEq Os]
    (p : CompilerProviders.Prepared)
    (image : AllocationImage.Imported)
    (context : EvalConfigurationCore.ForeignContext Os R EvalSyncObjectAccess.Payload H D
      (Other Raw Listener TcpStream Error) Aff B
      (Host Poll Instant System H D Raw Listener TcpStream Error Native Profiler) C Instant
      (EvalWindowsCallDispatchConstruction.Assembly Os R H D Aff B Poll Instant System
        Native Profiler Raw Listener TcpStream Error C Meta Path Zone Timestamp))
    (effects : TypedSyncMachine.Effects
      (EvalTypedSyncMachine.State Os R EvalSyncObjectAccess.Payload H D
        (Other Raw Listener TcpStream Error) Aff B Poll Instant System Native Profiler)) :
    EStateM StepError
      (State Os R H D Aff B Poll Instant System Native Profiler Raw Listener TcpStream Error)
      (ForeignSyncMachine.Objects
        (EvalForeignSyncMachine.State Os R EvalSyncObjectAccess.Payload H D
          (Other Raw Listener TcpStream Error) Aff B Poll Instant System Native Profiler)) := do
  let facts := p.lifecycle.calls.symbols.facts
  let targetFacts ← match p.externStatics.targetFacts with
    | .ok value => pure value
    | .error reason => throw (.unsupported reason)
  let u8 ← match CompilerPrimitiveFacts.primitiveLayout p.runtime "u8" with
    | .ok value => pure value
    | .error reason => throw (.unsupported s!"compiler u8 layout for Windows callback objects: {reason}")
  let symbols ← match p.foreignSymbols with
    | .ok value => pure value
    | .error reason => throw (.unsupported s!"compiler foreign-symbol query: {reason}")
  let checkClash := fun name => do
    match CompilerForeignSymbols.checkSymbolClash symbols name with
    | .ok () => pure ()
    | .error error => throw error
  let globalMemory : CompilerLinkSections.Memory MiriMemoryKind
      (EvalSyncMachine.User Os R EvalSyncObjectAccess.Payload H D
        (Other Raw Listener TcpStream Error) Aff B Poll Instant System Native Profiler)
      (Other Raw Listener TcpStream Error) := {
    functions := context.functions
    externStatic := CompilerExternStatic.resolve p.externStatics image checkClash
      context.functions (fun user => EvalWorld.roots.externStatics
        (ExecutionStateTransport.toOuter user))
    projection := context.compiler.projection context.choice
    readImmediate := PlaceMachine.readImmediate context.access }
  let hooks := EvalCallbackSyncConstruction.objectHooksFromSource facts
    context.access context.allocation context.compiler context.dynamic context.vtable
    context.dynamicFuel context.atomics context.extras context.pointers
  EvalForeignSyncMachine.objectsFromPhysical hooks
    EvalSyncObjectAccess.typedEmbedding effects context.choice
    ⟨u8.ty,u8.layout⟩ targetFacts.os p.namedGlobals globalMemory

private def ioErrorsToInner
    (errors : IoError.Hooks
      (State Os R H D Aff B Poll Instant System Native Profiler Raw Listener TcpStream Error) Error) :
    IoError.Hooks
      (EvalTimeConstruction.State Os R EvalSyncObjectAccess.Payload H D
        (Other Raw Listener TcpStream Error) Aff B Poll Instant System Native Profiler) Error := {
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

private def build [DecidableEq MiriMemoryKind] [DecidableEq Os]
    (p : CompilerProviders.Prepared) (image : AllocationImage.Imported)
    (context : EvalConfigurationCore.ForeignContext Os R EvalSyncObjectAccess.Payload H D
      (Other Raw Listener TcpStream Error) Aff B
      (Host Poll Instant System H D Raw Listener TcpStream Error Native Profiler) C Instant
      (EvalWindowsCallDispatchConstruction.Assembly Os R H D Aff B Poll Instant System
        Native Profiler Raw Listener TcpStream Error C Meta Path Zone Timestamp))
    (assembly : EvalWindowsCallDispatchConstruction.Assembly Os R H D Aff B Poll Instant System
      Native Profiler Raw Listener TcpStream Error C Meta Path Zone Timestamp)
    (main : MainMachine.Hooks
      (EvalWindowsFileConstruction.Payload Os R EvalSyncObjectAccess.Payload H D
        (Other Raw Listener TcpStream Error) Aff B
        (Host Poll Instant System H D Raw Listener TcpStream Error Native Profiler))
      C (Other Raw Listener TcpStream Error) ABI.ExternAbi (FnAbi TyId) (ArgAbi TyId)
      Aff ProgramExitPoll)
    (sourceLeaves : EvalConfigurationCore.SourceLeaves Os R EvalSyncObjectAccess.Payload H D
      Aff B Poll Instant System Native Profiler Raw Listener TcpStream Error ErrorHost
      Meta Path Miri.MIR.Place C Instant CallInstance AddrIter)
    (world : State Os R H D Aff B Poll Instant System Native Profiler Raw Listener TcpStream Error) :
    Except (StepError × State Os R H D Aff B Poll Instant System Native Profiler Raw Listener TcpStream Error)
      (Product Os R H D Aff B Poll Instant System Native Profiler Raw Listener TcpStream Error
        C ABI.ExternAbi (FnAbi TyId) (ArgAbi TyId) ×
       State Os R H D Aff B Poll Instant System Native Profiler Raw Listener TcpStream Error) := do
  let syncAction : EStateM StepError
      (EvalSyncMachine.State Os R EvalSyncObjectAccess.Payload H D
        (Other Raw Listener TcpStream Error) Aff B Poll Instant System Native Profiler)
      (TypedSyncMachine.Effects
        (EvalTypedSyncMachine.State Os R EvalSyncObjectAccess.Payload H D
          (Other Raw Listener TcpStream Error) Aff B Poll Instant System Native Profiler)) :=
    EvalCallbackSyncConstruction.sourceEffects
    p.lifecycle.calls.symbols.facts sourceLeaves.hostConfiguration context.place
    context.choice sourceLeaves.foreignSource.host.sync
  let (afterSync,syncResult) := MachineHooks.run (ExecutionStateTransport.action syncAction) world
  match syncResult with
  | .error error => .error (error,afterSync)
  | .ok effects => do
    let objectAction := sourceObjects p image context effects
    let (afterObjects,objectsResult) := MachineHooks.run objectAction afterSync
    match objectsResult with
    | .error error => .error (error,afterObjects)
    | .ok objects => do
      let callback ← match EvalWindowsCallbackSourceConstruction.fromSource main effects with
        | .ok value => pure value
        | .error error => throw (error,afterObjects)
      let sourceHost := sourceLeaves.foreignSource.host
      let deadline := EvalSyncMachine.deadlines sourceHost.clock
        (pure sourceLeaves.hostConfiguration.communicate) sourceHost.systemDurationSince
        (fun token kind => ExecutionStateTransport.reverseAction
          (callback.invoke context.choice token kind))
      match sourceHost.time with
      | none => do
        let chronoMissing : EvalTimeConstruction.HostEffects
            (EvalTimeConstruction.State Os R EvalSyncObjectAccess.Payload H D
              (Other Raw Listener TcpStream Error) Aff B Poll Instant System Native Profiler)
            Unit Unit := {
          utc := ()
          utcTimestamp := fun _ => throw (.unsupported "Windows chrono timestamp capability is absent")
          parseTimezone := fun _ => throw (.unsupported "Windows chrono timezone database is absent")
          withTimezone := fun _ _ => throw (.unsupported "Windows chrono timezone conversion is absent") }
        let timezoneString := fun os =>
          match String.fromUTF8? (sourceHost.os.encodedBytes os) with
          | some value => Except.ok value
          | none => Except.error ()
        let timeResult : Except StepError (TimeShims.Hooks
            (State Os R H D Aff B Poll Instant System Native Profiler Raw Listener TcpStream Error)
            Instant System Unit Unit) :=
          EvalWindowsSyncTimeConstruction.timeFromSource p assembly.sourceSeed.memory
            assembly.sourceSeed.environmentHost assembly.sourceSeed.osHost context.functions
            effects (ioErrorsToInner assembly.errors) sourceHost.clock sourceHost.systemDurationSince
            timezoneString sourceLeaves.hostConfiguration.communicate chronoMissing
        match timeResult with
        | .error error => .error (error,afterObjects)
        | .ok time =>
          let product : Product Os R H D Aff B Poll Instant System Native Profiler
              Raw Listener TcpStream Error C ABI.ExternAbi (FnAbi TyId) (ArgAbi TyId) := {
            Zone := Unit
            Timestamp := Unit
            callbacks := callback
            objects
            syncEffects := effects
            time
            deadline }
          .ok (product,afterObjects)
      | some timeSource => do
        let memory := assembly.sourceSeed.memory
        let timeResult : Except StepError (TimeShims.Hooks
            (State Os R H D Aff B Poll Instant System Native Profiler Raw Listener TcpStream Error)
            Instant System timeSource.Zone timeSource.Timestamp) :=
          EvalWindowsSyncTimeConstruction.timeFromSource p memory
            assembly.sourceSeed.environmentHost assembly.sourceSeed.osHost context.functions
            effects (ioErrorsToInner assembly.errors) sourceHost.clock sourceHost.systemDurationSince
            timeSource.timezoneString sourceLeaves.hostConfiguration.communicate timeSource.effects
        match timeResult with
        | .error error => .error (error,afterObjects)
        | .ok time =>
          let product : Product Os R H D Aff B Poll Instant System Native Profiler
              Raw Listener TcpStream Error C ABI.ExternAbi (FnAbi TyId) (ArgAbi TyId) := {
            Zone := timeSource.Zone
            Timestamp := timeSource.Timestamp
            callbacks := callback
            objects
            syncEffects := effects
            time
            deadline }
          .ok (product,afterObjects)

/-- Create physical synchronization objects, backend-selected callback
effects, the Main callback router, and a Windows time shim from the same
initialized machine. If chrono data is absent its calls fail on demand while
clock and synchronization operations still use the source host clock. -/
def fromSource [DecidableEq MiriMemoryKind] [DecidableEq Os]
    (p : CompilerProviders.Prepared) (image : AllocationImage.Imported)
    (context : EvalConfigurationCore.ForeignContext Os R EvalSyncObjectAccess.Payload H D
      (Other Raw Listener TcpStream Error) Aff B
      (Host Poll Instant System H D Raw Listener TcpStream Error Native Profiler) C Instant
      (EvalWindowsCallDispatchConstruction.Assembly Os R H D Aff B Poll Instant System
        Native Profiler Raw Listener TcpStream Error C Meta Path Zone Timestamp))
    (assembly : EvalWindowsCallDispatchConstruction.Assembly Os R H D Aff B Poll Instant System
      Native Profiler Raw Listener TcpStream Error C Meta Path Zone Timestamp)
    (main : MainMachine.Hooks
      (EvalWindowsFileConstruction.Payload Os R EvalSyncObjectAccess.Payload H D
        (Other Raw Listener TcpStream Error) Aff B
        (Host Poll Instant System H D Raw Listener TcpStream Error Native Profiler))
      C (Other Raw Listener TcpStream Error) ABI.ExternAbi (FnAbi TyId) (ArgAbi TyId)
      Aff ProgramExitPoll)
    (sourceLeaves : EvalConfigurationCore.SourceLeaves Os R EvalSyncObjectAccess.Payload H D
      Aff B Poll Instant System Native Profiler Raw Listener TcpStream Error ErrorHost
      Meta Path Miri.MIR.Place C Instant CallInstance AddrIter)
    (world : State Os R H D Aff B Poll Instant System Native Profiler Raw Listener TcpStream Error) :=
  build p image context assembly main sourceLeaves world

end Miri.Input.EvalWindowsCallbackAssembly
