import Miri.Input.EvalCoreMachine
import Miri.Input.EvalSyncMachine
import Miri.Input.EvalSyncPayload

/-! Canonical source SyncObj metadata and access semantics for the actual
EvalWorld. This lower module is shared by Core and callback construction; it
does not depend on EvalConfigurationCore or startup assembly. -/
namespace Miri.Input.EvalSyncObjectAccess
open Miri.ABI Miri.Memory Miri.MIR Miri.Interpreter Miri.Concurrency

abbrev Payload := EvalSyncPayload.Payload

abbrev World Os R H D O Aff B Poll Instant System Native Profiler :=
  EvalSyncMachine.World Os R Payload H D O Aff B Poll Instant System Native Profiler
abbrev User Os R H D O Aff B Poll Instant System Native Profiler :=
  EvalSyncMachine.User Os R Payload H D O Aff B Poll Instant System Native Profiler
abbrev Machine Os R H D O Aff B Poll Instant System Native Profiler :=
  PlaceMachine.Machine MiriMemoryKind
    (User Os R H D O Aff B Poll Instant System Native Profiler)
abbrev M Os R H D O Aff B Poll Instant System Native Profiler A :=
  PlaceMachine.MachineM MiriMemoryKind
    (User Os R H D O Aff B Poll Instant System Native Profiler) A

def typedEmbedding := EvalSyncPayload.typedEmbedding

def linuxFutexEmbedding := EvalSyncPayload.linuxFutexEmbedding

private def getObject
    (machine : Machine Os R H D O Aff B Poll Instant System Native Profiler)
    (ref : TypedSyncRuntime.Ref) : M Os R H D O Aff B Poll Instant System Native Profiler TypedSyncRuntime.Object :=
  match machine.user.payload.payload.user.host.sync.objects[ref.index]? with
  | some object => pure object
  | none => throw (.invalidProgram "missing source synchronization metadata reference")

/-- Typed pthread/Windows/macOS metadata checks its live wait queue for all
access kinds. Linux futex metadata has Miri's default empty SyncObj callback;
unknown payloads cannot enter this source-owned sum. -/
def onAccess : Payload → SyncObject.AccessKind →
    M Os R H D O Aff B Poll Instant System Native Profiler Unit
  | .linuxFutex _, _ => pure ()
  | .typed payload, kind => do
    let machine ← get
    TypedSyncMetadata.guardAccess (getObject machine) payload kind

def linuxFutexOnAccess : Payload → SyncObject.AccessKind →
    M Os R H D O Aff B Poll Instant System Native Profiler Unit :=
  LinuxFutexMachine.onAccess linuxFutexEmbedding onAccess

end Miri.Input.EvalSyncObjectAccess
