import Miri.Input.EvalTypedSyncMachine
import Miri.Interpreter.UnixForeignMachine
import Miri.Interpreter.WindowsForeignMachine

/-! Final World/HostRuntime synchronization selection in the foreign-item
chain. Source handler selection and object construction precede the ordinary
Unix/Windows source dispatch; no function-valued registry enters production. -/
namespace Miri.Input.EvalForeignSyncMachine
open Miri.ABI Miri.Memory Miri.Interpreter Miri.Concurrency
abbrev World := EvalTypedSyncMachine.World
abbrev User := EvalTypedSyncMachine.User
abbrev Inner := EvalTypedSyncMachine.State
abbrev State Os R P H D O Aff B Poll Instant System Native Profiler :=
  TypedSyncTransport.Outer MiriMemoryKind (World Os R P H D O Aff B Poll Instant System Native Profiler)
private def action (a : EStateM StepError (Inner Os R P H D O Aff B Poll Instant System Native Profiler) A) :
    EStateM StepError (State Os R P H D O Aff B Poll Instant System Native Profiler) A :=
  ExecutionStateTransport.action a

def objectsFromPhysical
    (h : LinuxFutexMachine.ObjectHooks MiriMemoryKind
      (World Os R P H D O Aff B Poll Instant System Native Profiler) C P O B)
    (embedding : TypedSyncObjectMachine.Payload P)
    (e : TypedSyncMachine.Effects (Inner Os R P H D O Aff B Poll Instant System Native Profiler))
    (choice : C) (u8Layout : LocalLayout) (os : String)
    (namedGlobals : CompilerNamedGlobals.Prepared)
    (globalMemory : CompilerLinkSections.Memory MiriMemoryKind
      (User Os R P H D O Aff B Poll Instant System Native Profiler) O) :
    EStateM StepError (State Os R P H D O Aff B Poll Instant System Native Profiler)
      (ForeignSyncMachine.Objects (State Os R P H D O Aff B Poll Instant System Native Profiler)) := do
  let e ← action (EvalTypedSyncMachine.effects e)
  let objects ← action (EvalTypedSyncMachine.objectsFromPhysical h embedding e choice u8Layout os namedGlobals globalMemory)
  pure {
    runtime := TypedSyncTransport.runtime EvalTypedSyncMachine.views e
    once := TypedSyncTransport.once EvalTypedSyncMachine.views e
    pthread := TypedSyncTransport.pthread EvalTypedSyncMachine.views e objects.pthread
    metadata := TypedSyncTransport.metadata objects.metadata
    bytes := TypedSyncTransport.bytes objects.bytes
    newFutex := action objects.newFutex
    newMacFutex := fun a b => action (objects.newMacFutex a b)
    macSettings := fun a => action (objects.macSettings a)
    putMacSettings := fun a b c => action (objects.putMacSettings a b c)}

def objects
    (h : LinuxFutexMachine.Hooks MiriMemoryKind
      (World Os R P H D O Aff B Poll Instant System Native Profiler) C P O B Instant System Z T E)
    (embedding : TypedSyncObjectMachine.Payload P)
    (e : TypedSyncMachine.Effects (Inner Os R P H D O Aff B Poll Instant System Native Profiler))
    (choice : C) (u8Layout : LocalLayout) (os : String)
    (namedGlobals : CompilerNamedGlobals.Prepared)
    (globalMemory : CompilerLinkSections.Memory MiriMemoryKind
      (User Os R P H D O Aff B Poll Instant System Native Profiler) O) :
    EStateM StepError (State Os R P H D O Aff B Poll Instant System Native Profiler)
      (ForeignSyncMachine.Objects (State Os R P H D O Aff B Poll Instant System Native Profiler)) :=
  objectsFromPhysical (LinuxFutexMachine.objectHooks h) embedding e choice u8Layout os namedGlobals globalMemory

/-- This returns the actual foreign dispatch dictionary consumed by calls,
with every Unix synchronization family selected from the canonical factory. -/
def unix
    (objects : ForeignSyncMachine.Objects (State Os R P H D O Aff B Poll Instant System Native Profiler))
    (h : UnixForeign.Hooks (State Os R P H D O Aff B Poll Instant System Native Profiler)
      Place H D O Os HM Time E Kind ReadDir DirEntry TypedSyncRuntime.Ref Duration PollIter AddrIter Instant System TZ Timestamp Block Instance)
    (base : ForeignItems.Hooks Provenance (State Os R P H D O Aff B Poll Instant System Native Profiler)
      Place TypedSyncRuntime.Dest (Pointer (Option Provenance)) Block Instance) :=
  UnixForeign.bind (UnixForeignMachine.bindSynchronization objects h) base

def windows [DecidableEq Os]
    (objects : ForeignSyncMachine.Objects (State Os R P H D O Aff B Poll Instant System Native Profiler))
    (h : WindowsForeign.Hooks (State Os R P H D O Aff B Poll Instant System Native Profiler)
      Place FD H D Os HM Time E Kind TypedSyncRuntime.Ref Instant System TZ Timestamp Block Instance)
    (base : ForeignItems.Hooks Provenance (State Os R P H D O Aff B Poll Instant System Native Profiler)
      Place TypedSyncRuntime.Dest (Pointer (Option Provenance)) Block Instance) :=
  WindowsForeign.bind (WindowsForeignMachine.bindSynchronization objects h) base
end Miri.Input.EvalForeignSyncMachine
