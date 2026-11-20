import Miri.Input.EvalSyncMachine
import Miri.Interpreter.TypedSyncBytes
import Miri.Interpreter.ForeignSyncMachine
import Miri.Input.CompilerNamedGlobals
import Miri.Input.CompilerLinkSections

/-! One synchronization arena in the final HostRuntime, using the exact shared
ThreadMachine token supply. This factory allocates no mirror clocks or stacks. -/
namespace Miri.Input.EvalTypedSyncMachine
open Miri.ABI Miri.Memory Miri.Interpreter Miri.Concurrency
abbrev Host := HostRuntime.Storage
abbrev World Os R P H D O Aff B Poll Instant System Native Profiler :=
  EvalSyncMachine.World Os R P H D O Aff B Poll Instant System Native Profiler
abbrev User Os R P H D O Aff B Poll Instant System Native Profiler :=
  EvalSyncMachine.User Os R P H D O Aff B Poll Instant System Native Profiler
abbrev State Os R P H D O Aff B Poll Instant System Native Profiler :=
  EvalSyncMachine.State Os R P H D O Aff B Poll Instant System Native Profiler

def views : TypedSyncMachine.Views (World Os R P H D O Aff B Poll Instant System Native Profiler) where
  storage := fun w => w.host.sync
  putStorage := fun w sync => {w with host := {w.host with sync}}
  nextCallback := fun w => w.runtime.threads.nextCallback
  putNextCallback := fun w nextCallback => {w with runtime := {w.runtime with threads := {w.runtime.threads with nextCallback}}}

/-- Validate actual None/VClock state when selecting the source handler;
caller supplies concrete OS writes, not a registry or callback evaluator. -/
def effects
    (base : TypedSyncMachine.Effects (State Os R P H D O Aff B Poll Instant System Native Profiler)) :
    EStateM StepError (State Os R P H D O Aff B Poll Instant System Native Profiler)
      (TypedSyncMachine.Effects (State Os R P H D O Aff B Poll Instant System Native Profiler)) := do
  let selected ← match EvalBackendMachine.handler (← get).machine with
    | .ok selected => pure selected | .error error => throw error
  let handler := match selected with
    | .none => SyncClockHandler.none | .vclocks _ => .vectorClocks
  pure {base with handler}

def runtime
    (e : TypedSyncMachine.Effects (State Os R P H D O Aff B Poll Instant System Native Profiler)) :
    EStateM StepError (State Os R P H D O Aff B Poll Instant System Native Profiler)
      (SyncRuntime.Hooks (State Os R P H D O Aff B Poll Instant System Native Profiler)
        TypedSyncRuntime.Ref Int32 TypedSyncRuntime.Dest) := do
  pure (TypedSyncMachine.runtime views (← effects e))

def invoke
    (e : TypedSyncMachine.Effects (State Os R P H D O Aff B Poll Instant System Native Profiler))
    (other : Nat → UnblockKind → EStateM StepError (State Os R P H D O Aff B Poll Instant System Native Profiler) Unit)
    (token : Nat) (kind : UnblockKind) : EStateM StepError (State Os R P H D O Aff B Poll Instant System Native Profiler) Unit := do
  if ← TypedSyncMachine.owns views token then
    TypedSyncRuntime.invoke (TypedSyncMachine.typed views (← effects e)) token kind
  else other token kind
abbrev Objects := ForeignSyncMachine.Objects

/-- Final-World object factory from the actual physical memory/backend fields.
It shares HostRuntime.sync and needs no clock, deadline or host-time input, so
ordinary pthread operations do not wait for unused futex time support. -/
def objectsFromPhysical
    (h : LinuxFutexMachine.ObjectHooks MiriMemoryKind
      (World Os R P H D O Aff B Poll Instant System Native Profiler) C P O B)
    (embedding : TypedSyncObjectMachine.Payload P)
    (e : TypedSyncMachine.Effects (State Os R P H D O Aff B Poll Instant System Native Profiler))
    (choice : C) (u8Layout : LocalLayout) (os : String)
    (namedGlobals : CompilerNamedGlobals.Prepared)
    (globalMemory : CompilerLinkSections.Memory MiriMemoryKind
      (User Os R P H D O Aff B Poll Instant System Native Profiler) O) :
    EStateM StepError (State Os R P H D O Aff B Poll Instant System Native Profiler)
      (Objects (State Os R P H D O Aff B Poll Instant System Native Profiler)) := do
  let e ← effects e
  let h := TypedSyncObjectMachine.bindObjectMemory views embedding h
  let typed := TypedSyncMachine.typed views e
  let metadata := TypedSyncObjectMachine.metadataFromObjectHooks h embedding typed
  let bytes := TypedSyncBytes.bindObjectHooks h choice u8Layout
  let initializer := fun name => CompilerNamedGlobals.global namedGlobals globalMemory name
  pure {
    runtime := TypedSyncMachine.runtime views e
    once := TypedSyncMachine.initOnce views e
    pthread := TypedSyncFactories.pthread views e metadata bytes
      (TypedSyncBytes.pthreadMemoryFromObjectHooks h choice os initializer)
    metadata, bytes
    newFutex := TypedSyncMachine.newObject views (.futex {})
    newMacFutex := TypedSyncFactories.newMacFutex views
    macSettings := TypedSyncFactories.macSettings views
    putMacSettings := TypedSyncFactories.putMacSettings views}

/-- Compatibility entry for callers that already have the full futex family;
all physical object operations project to the same canonical state. -/
def objects
    (h : LinuxFutexMachine.Hooks MiriMemoryKind
      (World Os R P H D O Aff B Poll Instant System Native Profiler) C P O B Instant System Z T E)
    (embedding : TypedSyncObjectMachine.Payload P)
    (e : TypedSyncMachine.Effects (State Os R P H D O Aff B Poll Instant System Native Profiler))
    (choice : C) (u8Layout : LocalLayout) (os : String)
    (namedGlobals : CompilerNamedGlobals.Prepared)
    (globalMemory : CompilerLinkSections.Memory MiriMemoryKind
      (User Os R P H D O Aff B Poll Instant System Native Profiler) O) :
    EStateM StepError (State Os R P H D O Aff B Poll Instant System Native Profiler)
      (Objects (State Os R P H D O Aff B Poll Instant System Native Profiler)) :=
  objectsFromPhysical (LinuxFutexMachine.objectHooks h) embedding e choice u8Layout os namedGlobals globalMemory
end Miri.Input.EvalTypedSyncMachine
