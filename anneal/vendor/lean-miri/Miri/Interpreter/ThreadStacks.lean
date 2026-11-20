import Miri.Interpreter.MachineHooks
import Miri.Interpreter.RunLoop
import Miri.Concurrency.Scheduler

/-! Actual per-thread interpreter stacks behind Miri's active_thread_stack
view. The StepState stack is the active view, and every inactive thread owns
its complete saved Stack. No token-only stack is used to resume execution. -/
namespace Miri.Interpreter.ThreadStacks
open Miri.Memory Miri.MIR Miri.Concurrency

abbrev ActualStack := Stack Provenance LocalLayout MachineHooks.FrameExtra

structure SavedStack where
  thread : ThreadId
  stack : ActualStack

/-- The active stack lives in StepState.stack, never duplicated here. Thread
IDs are never reused by the source ThreadManager. -/
structure Registry where
  activeThread : ThreadId
  inactive : Array SavedStack

/-- Canonical machine User embedding. All existing MachineHooks/Place/Call
adapters remain polymorphic in this payload and operate on the active stack. -/
structure Storage (User : Type) where
  registry : Registry
  identitySupply : LocalsIdentitySupply
  user : User

abbrev State (K User : Type) := MachineHooks.State K (Storage User)
abbrev M (K User A : Type) := EStateM StepError (State K User) A

private def invariant (message : String) : Except StepError A :=
  .error (.invalidProgram s!"thread stacks: {message}")

/-- Check coverage and uniqueness instead of inventing missing stacks. The
manager's old opaque stackFrames field is not an interpreter frame source. -/
def validate (registry : Registry) (manager : ThreadManager) : Except StepError Unit := do
  if registry.activeThread != manager.activeThread then
    invariant "active manager/view identity mismatch"
  if (manager.thread? registry.activeThread).isNone then invariant "active thread missing"
  let mut seen := #[registry.activeThread]
  for entry in registry.inactive do
    if seen.contains entry.thread then invariant "duplicate saved stack"
    if (manager.thread? entry.thread).isNone then invariant "saved stack has no thread"
    seen := seen.push entry.thread
  if seen.size != manager.threads.length then invariant "thread has no actual stack"

/-- Reflect actual frame identities into ThreadRecord's compatibility token
view. Lifecycle checks now observe actual stack emptiness and frame identity;
the opaque list never creates or restores interpreter frames. -/
private def reflectStacks (registry : Registry) (active : ActualStack)
    (manager : ThreadManager) : Except StepError ThreadManager := do
  validate registry manager
  let mut records := #[]
  for index in [:manager.threads.length] do
    let id ← match ThreadId.ofNat index with
      | .ok id => pure id
      | .error _ => invariant "thread id cannot index actual stacks"
    let some thread := manager.thread? id | invariant "thread vanished during reflection"
    let stack ← if id == registry.activeThread then pure active else
      match registry.inactive.find? (fun entry => entry.thread == id) with
      | some entry => pure entry.stack
      | none => invariant "thread has no actual stack"
    records := records.push { thread with
      stackFrames := stack.frames.toList.map (fun frame => frame.localsIdentity.token) }
  return { manager with threads := records.toList }

/-- Total locals-buffer ghost allocation adapter for StackLifecycleHooks. The
supply must start above all identities assigned with the lifetime-label policy.
Explicit host-buffer-token embeddings may instead provide their own allocator. -/
def freshLocalsIdentity (machine : MachineHooks.MachineState K (Storage User)) :
    MachineHooks.MachineState K (Storage User) × LocalsIdentity :=
  let (identitySupply, identity) := machine.user.identitySupply.allocate
  ({ machine with user := { machine.user with identitySupply } }, identity)

def bindLifecycle (base : StackLifecycleHooks Provenance LocalLayout MachineHooks.FrameExtra
    (MachineHooks.MachineState K (Storage User))) :
    StackLifecycleHooks Provenance LocalLayout MachineHooks.FrameExtra
      (MachineHooks.MachineState K (Storage User)) :=
  { base with freshLocalsIdentity }

/-- Attach a preexisting active view and explicit inactive stacks. This does
not create any interpreter frame, local, layout, continuation or identity. -/
def attach (state : MachineHooks.State K User) (inactive : Array SavedStack)
    (identitySupply : LocalsIdentitySupply) :
    Except StepError (State K User) := do
  let registry : Registry := ⟨state.machine.threads.activeThread, inactive⟩
  let manager ← reflectStacks registry state.stack state.machine.threads
  return { state with machine := { state.machine with threads := manager, user := ⟨registry, identitySupply, state.machine.user⟩ } }

private def lift (value : Except StepError A) : M K User A :=
  match value with | .ok value => pure value | .error error => throw error

/-- Install a source manager transition and its active stack together. All
unrelated machine fields and actual frame contents remain unchanged. Any
missing target is an invariant failure before mutation, never an empty stack.
Existing manager updates (including callback state) come from the caller's
source transition; stack restoration adds no compiler or machine callbacks. -/
def installManager (manager : ThreadManager) : M K User Unit := do
  let state ← get
  let registry := state.machine.user.registry
  lift (validate registry state.machine.threads)
  if manager.threads.length != state.machine.threads.threads.length then
    throw (.invalidProgram "thread stacks: creation must register its actual stack")
  let mut stack := state.stack
  let mut nextRegistry := registry
  if registry.activeThread != manager.activeThread then
    let some selected := registry.inactive.find? (fun entry => entry.thread == manager.activeThread)
      | throw (.invalidProgram "thread stacks: target has no actual stack")
    stack := selected.stack
    nextRegistry := ⟨manager.activeThread,
      (registry.inactive.filter fun entry => entry.thread != manager.activeThread).push
        ⟨registry.activeThread, state.stack⟩⟩
  let manager ← lift (reflectStacks nextRegistry stack manager)
  set { state with stack, machine := { state.machine with
    threads := manager
    user := { state.machine.user with registry := nextRegistry } } }

/-- Refresh compatibility lifecycle tokens after pushes/pops or callbacks,
including failed callbacks that have already changed the current stack. -/
def synchronize : M K User Unit := do
  let state ← get
  let manager ← lift (reflectStacks state.machine.user.registry state.stack state.machine.threads)
  set { state with machine := { state.machine with threads := manager } }

/-- Keep successful and failing active-frame mutation prefixes, then refresh
the derived manager view. No source callback is invoked during reflection. -/
def synchronized (action : M K User A) : M K User A := fun state =>
  let finish (after : State K User) (outcome : Except StepError A) :=
    match synchronize after with
    | .ok () after => match outcome with
      | .ok value => EStateM.Result.ok value after
      | .error error => EStateM.Result.error error after
    | .error error after => EStateM.Result.error error after
  match action state with
  | .ok value after => finish after (.ok value)
  | .error error after => finish after (.error error)

/-- Keep ThreadRecord's lifecycle projection coherent after both successful
and partially failing call-stack operations. Use with the actual source call
binding; no frame or local state is reconstructed from compatibility tokens. -/
def bindCall (base : CallHooks Provenance (State K User) C MachineHooks.FrameExtra Other Extern FnABI ArgABI) :
    CallHooks Provenance (State K User) C MachineHooks.FrameExtra Other Extern FnABI ArgABI :=
  { base with
    pushRaw := fun c fnInstance body dest continuation =>
      synchronized (base.pushRaw c fnInstance body dest continuation)
    popRaw := fun c => synchronized (base.popRaw c)
    pushDone := fun c => synchronized (base.pushDone c)
    cleanup := fun c unwinding frame => synchronized (base.cleanup c unwinding frame) }

/-- ControlFlow also pops directly on return/unwind. Refresh the derived
thread lifecycle view even if protector release or cleanup fails midway. -/
def bindControl (base : ControlHooks Provenance LocalLayout MachineHooks.FrameExtra
    (MachineHooks.MachineState K (Storage User)) C Op) :
    ControlHooks Provenance LocalLayout MachineHooks.FrameExtra
      (MachineHooks.MachineState K (Storage User)) C Op :=
  let fromStep := fun {A : Type} (action : State K User → StepResult (State K User) A) =>
    synchronized fun state =>
      let (state, outcome) := action state
      match outcome with
      | .ok value => .ok value state
      | .error error => .error error state
  { base with
    popFrame := fun c state => MachineHooks.run (fromStep (base.popFrame c)) state
    cleanupFrame := fun c unwinding frame state => MachineHooks.run
      (fromStep (base.cleanupFrame c unwinding frame)) state }

/-- thread.rs set_active_thread returns the previous ID and accepts any
existing thread; scheduler enabled-state checks belong to the source caller. -/
def setActiveThread (id : ThreadId) : M K User ThreadId := do
  let manager := (← get).machine.threads
  let (manager, old) ← match manager.setActiveThread id with
    | .ok value => pure value
    | .error error => throw (.invalidProgram s!"set_active_thread: {reprStr error}")
  installManager manager
  return old

/-- Source callbacks restore only on normal return. A callback error keeps
its actual selected stack and all previous local/memory/machine mutations. -/
def withActiveThread (id : ThreadId) (action : M K User A) : M K User A := do
  let old ← setActiveThread id
  let value ← action
  let _ ← setActiveThread old
  return value

/-- Thread::new owns an actually empty stack. This is the sole implicit empty
stack here, created only after source create_thread allocates a new ID. -/
def createThread (onStackEmpty : Nat) : M K User ThreadId := do
  let state ← get
  lift (validate state.machine.user.registry state.machine.threads)
  let (manager, id) ← match state.machine.threads.createThread onStackEmpty with
    | .ok value => pure value
    | .error error => throw (.invalidProgram s!"create_thread: {reprStr error}")
  let registry := { state.machine.user.registry with
    inactive := state.machine.user.registry.inactive.push ⟨id, Stack.empty⟩ }
  let manager ← lift (reflectStacks registry state.stack manager)
  set { state with machine := { state.machine with
    threads := manager
    user := { state.machine.user with registry } } }
  return id

/-- unblock_thread changes the target to Enabled and selects it before the
callback. Success restores the previous thread; errors retain the callback's
current thread (which may itself have changed) and its actual stack. -/
def unblockThread (id : ThreadId) (reason : BlockReason)
    (invoke : Nat → UnblockKind → M K User Unit) : M K User Unit := do
  let (manager, obligation) ← match (← get).machine.threads.unblockThread id reason with
    | .ok value => pure value
    | .error error => throw (.invalidProgram s!"unblock_thread: {reprStr error}")
  installManager manager
  invoke obligation.callbackToken obligation.kind
  let _ ← setActiveThread obligation.previousActive
  pure ()

/-- Apply finishLocal's source scheduling policy to actual saved frames. The
service-environment callbacks must already have run in their source order. -/
def finishLocal (potentialSleepTime : Option Nat) (anyThreadBlockedOnHost : Bool)
    (rank : Nat) : M K User RunSchedulingAction := do
  let decision ← match Scheduler.finishLocal (← get).machine.threads potentialSleepTime anyThreadBlockedOnHost rank with
    | .ok value => pure value
    | .error error => throw (.invalidProgram s!"schedule: {reprStr error}")
  match decision with
  | .executeStep manager _ _ => installManager manager; return .executeStep
  | .sleepAndWaitForIo manager duration => installManager manager; return .sleepAndWaitForIo duration
  | .globalDeadlock manager =>
    installManager manager
    throw (.termination .globalDeadlock)
  | .allThreadsTerminatedInvariant manager =>
    installManager manager
    throw (.invalidProgram "scheduler invoked after all threads terminated")

/-- Required leaves for the complete local (local) scheduler branch.
Host readiness/deadlines and nondeterministic choices remain genuine effects. -/
structure LocalSchedulerHooks (K User : Type) where
  processDelayedReadiness : M K User Unit
  communicate : M K User Bool
  pollHostIoNonBlocking : M K User Unit
  unblockExpiredDeadlines : M K User (Option Nat)
  choose : List ThreadId → M K User (Option ThreadId)
  anyThreadBlockedOnHost : M K User Bool

/-- scheduler.rs schedule, local branch. Candidate selection precedes
clearing yield; host-blocked queries run only after the enabled/all-terminated
and finite-sleep branches have failed. Every callback operates on real stacks.
The nondeterministic leaf must choose only a source-eligible candidate. -/
def scheduleLocal (h : LocalSchedulerHooks K User) : M K User RunSchedulingAction := do
  let state ← get
  lift (validate state.machine.user.registry state.machine.threads)
  let some active := state.machine.threads.activeThread?
    | throw (.invalidProgram "schedule: active thread missing")
  if active.isEnabled && !state.machine.threads.yieldActiveThread then return .executeStep
  h.processDelayedReadiness
  if ← h.communicate then h.pollHostIoNonBlocking
  let potentialSleep ← h.unblockExpiredDeadlines
  let manager := (← get).machine.threads
  let candidates ← match Scheduler.eligibleThreads manager with
    | .ok value => pure value
    | .error error => throw (.invalidProgram s!"schedule candidates: {reprStr error}")
  let selected ← if manager.fixedScheduling then pure candidates.head? else h.choose candidates
  match selected with
  | some id =>
    if !candidates.contains id then throw (.invalidProgram "scheduler chose ineligible thread")
    if id != (← get).machine.threads.activeThread then
      let _ ← setActiveThread id
      pure ()
  | none =>
    if !candidates.isEmpty then throw (.invalidProgram "scheduler omitted eligible thread")
  modify fun state => { state with machine := { state.machine with
    threads := { state.machine.threads with yieldActiveThread := false } } }
  let manager := (← get).machine.threads
  let some active := manager.activeThread?
    | throw (.invalidProgram "schedule: selected active thread missing")
  if active.isEnabled then return .executeStep
  if manager.threads.all ThreadRecord.isTerminated then
    throw (.invalidProgram "scheduler invoked after all threads terminated")
  if let some duration := potentialSleep then return .sleepAndWaitForIo (some duration)
  if ← h.anyThreadBlockedOnHost then return .sleepAndWaitForIo none
  throw (.termination .globalDeadlock)

/-- Bind the actual-stack scheduler to the outer run loop. All other lifecycle
and environment callbacks remain the supplied source implementations. -/
def bindRunLoop (base : RunLoopHooks (State K User) C Callback)
    (h : C → LocalSchedulerHooks K User) : RunLoopHooks (State K User) C Callback :=
  { base with
    schedule := fun c state => MachineHooks.run (scheduleLocal (h c)) state
    coreStep := fun c state => MachineHooks.run (synchronized fun state =>
      let (state, outcome) := base.coreStep c state
      match outcome with
      | .ok value => .ok value state
      | .error error => .error error state) state
    terminateActiveThread := fun c forExit state => MachineHooks.run (do
      synchronize
      let state ← get
      let (state, outcome) := base.terminateActiveThread c forExit state
      set state
      match outcome with | .ok () => pure () | .error error => throw error) state }

/-- Observe any thread's actual stack. The active view includes all mutations
since the last switch; inactive snapshots never come from opaque frame tokens. -/
def stackFor (id : ThreadId) : M K User ActualStack := do
  let state ← get
  lift (validate state.machine.user.registry state.machine.threads)
  if id == state.machine.user.registry.activeThread then return state.stack
  let some entry := state.machine.user.registry.inactive.find? (fun entry => entry.thread == id)
    | throw (.invalidProgram "thread stacks: queried thread missing")
  return entry.stack

end Miri.Interpreter.ThreadStacks
