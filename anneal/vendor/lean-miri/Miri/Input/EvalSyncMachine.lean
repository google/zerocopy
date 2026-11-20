import Miri.Input.EvalCoreMachine
import Miri.Input.HostRuntime
import Miri.Interpreter.SyncMachine
import Miri.Interpreter.LinuxFutexMachine
import Miri.Interpreter.TimeShims

/-! Futex/clock views into the final World.host and shared callback supply.
No callback closure arena, clock, address map or futex table is duplicated. -/
namespace Miri.Input.EvalSyncMachine
open Miri.ABI Miri.Memory Miri.MIR Miri.Interpreter Miri.Concurrency
abbrev Host := HostRuntime.Storage
abbrev World Os R P H D O Aff B Poll Instant System Native Profiler :=
  EvalWorld.World Os R P H D O Aff B (Host Poll Instant System H D O Native Profiler)
abbrev User Os R P H D O Aff B Poll Instant System Native Profiler :=
  ExecutionStateTransport.Inner (World Os R P H D O Aff B Poll Instant System Native Profiler)
abbrev State Os R P H D O Aff B Poll Instant System Native Profiler :=
  MachineHooks.State MiriMemoryKind (User Os R P H D O Aff B Poll Instant System Native Profiler)

def views : LinuxFutexMachine.Views (World Os R P H D O Aff B Poll Instant System Native Profiler) where
  storage := fun w => w.host.futex
  putStorage := fun w futex => {w with host := {w.host with futex}}
  nextCallback := fun w => w.runtime.threads.nextCallback
  putNextCallback := fun w nextCallback => {w with runtime := {w.runtime with threads := {w.runtime.threads with nextCallback}}}

def deadlines
    (host : Clock.HostHooks Instant System (State Os R P H D O Aff B Poll Instant System Native Profiler))
    (communicate : MachineHooks.M MiriMemoryKind
      (User Os R P H D O Aff B Poll Instant System Native Profiler) Bool)
    (systemDurationSince : System → System → MachineHooks.M MiriMemoryKind
      (User Os R P H D O Aff B Poll Instant System Native Profiler) (Option Clock.Duration))
    (invoke : Nat → UnblockKind → MachineHooks.M MiriMemoryKind
      (User Os R P H D O Aff B Poll Instant System Native Profiler) Unit) :
    DeadlineMachine.Hooks MiriMemoryKind
      (User Os R P H D O Aff B Poll Instant System Native Profiler) Instant System where
  registry := fun u => u.payload.payload.user.host.deadlines
  setRegistry := fun deadlines u => {u with payload := {u.payload with payload := {u.payload.payload with user :=
    {u.payload.payload.user with host := {u.payload.payload.user.host with deadlines}}}}}
  clock := fun u => u.payload.payload.user.host.clock
  host := host
  communicate := communicate
  systemDurationSince := systemDurationSince
  selectThread := fun id => ExecutionStateTransport.reverseAction (ThreadStacks.setActiveThread id)
  invokeCallback := invoke

/-- Actual per-thread errno references are held by the source thread record,
with typed pointers in the one shared runtime side table. The caller's machine
allocation provider remains required; byte reads/writes are closed by bind. -/
def errors (u32Layout : LocalLayout)
    (base : IoError.Hooks (State Os R P H D O Aff B Poll Instant System Native Profiler) E) :
    IoError.Hooks (State Os R P H D O Aff B Poll Instant System Native Profiler) E :=
  {base with
    getLastErrorPlace := do
      let s ← get
      let some thread := s.machine.threads.activeThread? | throw (.invalidProgram "errno active thread missing")
      let some token := thread.lastErrorLocation | return none
      let entries := s.machine.user.payload.payload.user.runtime.errnoPlaces.filter (fun e => e.1.value.toNat == token)
      let some (_,place) := entries[0]? | throw (.invalidProgram "errno token has no typed pointer")
      unless entries.size == 1 && place.layout == u32Layout do throw (.invalidProgram "errno pointer metadata mismatch")
      pure (some place)
    setLastErrorPlace := fun place => do
      let some provenance := place.mplace.ptr.provenance | throw (.invalidProgram "errno place has no provenance")
      let some id := PointerProvenance.getAllocId provenance | throw (.invalidProgram "errno place has no allocation provenance")
      let s ← get
      let manager := s.machine.threads
      let some thread := manager.activeThread? | throw (.invalidProgram "errno active thread missing")
      let thread := {thread with lastErrorLocation := some id.value.toNat}
      let w := s.machine.user.payload.payload.user
      let w := {w with runtime := {w.runtime with errnoPlaces :=
        (w.runtime.errnoPlaces.filter fun (e : AllocId × MPlaceTy Provenance) => e.1 != id).push (id,place)}}
      set {s with machine := {s.machine with
        threads := {manager with threads := manager.threads.set manager.activeThread.toNat thread}
        user := {s.machine.user with payload := {s.machine.user.payload with payload := {s.machine.user.payload.payload with user := w}}}}}}

/-- Install final World-owned storage and physical dictionaries from the
already closed core. Remaining arguments are typed compiler/host policies. -/
def hooks
    (prepared : CompilerFactAdapters.Prepared)
    (core : ExecutionMachine.Config MiriMemoryKind (User Os R P H D O Aff B Poll Instant System Native Profiler) C O X TermHost)
    (pointers : PointerMachine.Hooks MiriMemoryKind
      (ValidityMachine.Control (ThreadStacks.Storage (World Os R P H D O Aff B Poll Instant System Native Profiler))))
    (embedding : LinuxFutexMachine.Payload P)
    (sync : P → SyncObject.AccessKind → PlaceMachine.MachineM MiriMemoryKind
      (User Os R P H D O Aff B Poll Instant System Native Profiler) Unit)
    (weakError : StoreBufferAllocError → StepError)
    (time : TimeShims.Hooks (State Os R P H D O Aff B Poll Instant System Native Profiler) Instant System Z T)
    (deadline : DeadlineMachine.Hooks MiriMemoryKind
      (User Os R P H D O Aff B Poll Instant System Native Profiler) Instant System)
    (io : IoError.Hooks (State Os R P H D O Aff B Poll Instant System Native Profiler) E)
    (communicate : MachineHooks.M MiriMemoryKind
      (User Os R P H D O Aff B Poll Instant System Native Profiler) Bool)
    :
    MachineHooks.M MiriMemoryKind (User Os R P H D O Aff B Poll Instant System Native Profiler)
      (LinuxFutexMachine.Hooks MiriMemoryKind
        (World Os R P H D O Aff B Poll Instant System Native Profiler) C P O B Instant System Z T E) := do
  let i32Layout ← match prepared.context.runtime.integerLayout .i32 with
    | .ok layout => pure layout | .error error => throw (.callback s!"compiler i32 layout: {error}")
  let u32Layout ← match prepared.context.runtime.integerLayout .u32 with
    | .ok layout => pure layout | .error error => throw (.callback s!"compiler u32 layout: {error}")
  pure {
    views := views
    payload := embedding
    access := core.access
    allocation := core.allocation
    compiler := core.compiler
    pointers := pointers
    pointerCompiler := CompilerExecutionProviders.pointerCompiler prepared
    dynamic := core.projection.dynamic
    vtable := core.validity.vtable
    dynamicFuel := core.projection.dynamicFuel
    atomic := core.atomics
    backend := fun s => EvalBackendMachine.handler s.machine
    extras := EvalCoreMachine.extras (LinuxFutexMachine.onAccess embedding sync) weakError
    i32Layout := i32Layout
    readTimespec := TimeShims.readTimespec time
    deadline := deadline
    errors := errors u32Layout io
    communicate := communicate }

/-- The general pthread/Windows/init-once/readiness runtime uses the same
source backend sum, optional clocks and actual thread stack manager as futex. -/
def runtime (base : SyncRuntime.Hooks
    (State Os R P H D O Aff B Poll Instant System Native Profiler) Ref V Dest) :
    MachineHooks.M MiriMemoryKind
      (User Os R P H D O Aff B Poll Instant System Native Profiler)
      (SyncRuntime.Hooks (State Os R P H D O Aff B Poll Instant System Native Profiler) Ref V Dest) :=
  SyncMachine.bind (fun s => EvalBackendMachine.handler s.machine) base

/-- Called by the actual callback dispatcher after it selects the callback's
thread. Other callback families retain their source interpreter. -/
def invoke (h : LinuxFutexMachine.Hooks MiriMemoryKind
      (World Os R P H D O Aff B Poll Instant System Native Profiler) C P O B Instant System Z T E)
    (choice : C) (other : Nat → UnblockKind → MachineHooks.M MiriMemoryKind
      (User Os R P H D O Aff B Poll Instant System Native Profiler) Unit)
    (token : Nat) (kind : UnblockKind) : MachineHooks.M MiriMemoryKind
      (User Os R P H D O Aff B Poll Instant System Native Profiler) Unit := do
  if (← get).machine.user.payload.payload.user.host.futex.callbacks.any (·.1 == token) then
    FutexRuntime.invoke (LinuxFutexMachine.runtime h choice) token kind
  else other token kind
end Miri.Input.EvalSyncMachine
