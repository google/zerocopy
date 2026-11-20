import Miri.Interpreter.ThreadTerminationMachine

/-! Scheduler-facing split callback protocol. The taken closure owns its
actual TLS stage; invocation stores its mutated stage only on success, and
restoration is checked in the thread selected after the callback. -/
namespace Miri.Interpreter.ThreadLoops
open Miri.ABI Miri.Memory Miri.MIR Miri.Concurrency Miri.TreeBorrows
abbrev M := ThreadTlsMachine.M
abbrev State := ThreadTlsMachine.State
structure TakenTls where
  token : Nat
  stage : TlsDtorsStage Provenance

private def changeRuntime (h : ThreadTlsMachine.Hooks U C O X F A Aff)
    (f : ThreadMachine.Runtime Aff → ThreadMachine.Runtime Aff) : M U Unit :=
  modify fun state => {state with machine := {state.machine with user := {state.machine.user with
    user := h.thread.putRuntime state.machine.user.user (f (h.thread.runtime state.machine.user.user))}}}

private def capture (h : ThreadTlsMachine.Hooks U C O X F A Aff)
    (stage : TlsDtorsStage Provenance) (state : State U) : ThreadTlsMachine.Scratch U :=
  let data := h.data state.machine.user.user
  let tls : ThreadLocalState Provenance BorrowTree (State U) := {
    memory := state.machine.memory
    hooks := state
    manager := state.machine.threads
    pointers := data.statics }
  let race := match state.machine.dataRace with
    | none => .none | some global => .vectorClocks global
  {exit := ⟨tls,data.staticRoots,race⟩, data := data.values, stage}

private def restoreView (h : ThreadTlsMachine.Hooks U C O X F A Aff)
    (scratch : ThreadTlsMachine.Scratch U) : State U :=
  let state := scratch.exit.tls.hooks
  let data : ThreadTlsMachine.Data := ⟨scratch.data,scratch.exit.tls.pointers,scratch.exit.staticRoots⟩
  let user := {state.machine.user with user := h.putData state.machine.user.user data}
  {state with machine := {state.machine with
    memory := scratch.exit.tls.memory
    threads := scratch.exit.tls.manager
    user
    dataRace := match scratch.exit.race with
      | .none => none | .vectorClocks global => some global}}

/-- Origin reset precedes callback take, including on missing callback errors.
The registry copy is moved out with the callback, preventing reentry. -/
def take (h : ThreadTlsMachine.Hooks U C O X F A Aff) : M U TakenTls := do
  unless (← get).stack.frames.isEmpty do throw (.invalidProgram "TLS callback requires actual empty stack")
  let manager := (← get).machine.threads
  let some thread := manager.activeThread? | throw (.invalidProgram "active TLS thread missing")
  let thread := {thread with originSpanToken := h.thread.spans.dummy.id}
  ThreadStacks.installManager {manager with threads := manager.threads.set manager.activeThread.toNat thread}
  let some token := thread.onStackEmptyCallback | throw (.invalidProgram "thread has no stack-empty callback")
  let manager := (← get).machine.threads
  let thread := {thread with onStackEmptyCallback := none}
  ThreadStacks.installManager {manager with threads := manager.threads.set manager.activeThread.toNat thread}
  let runtime := h.thread.runtime (← get).machine.user.user
  let some (_,stage) := runtime.tlsCallbacks.find? (fun entry => entry.1 == token) |
    throw (.unsupported "stack-empty callback is not a registered TLS closure")
  changeRuntime h fun rt => {rt with tlsCallbacks := rt.tlsCallbacks.filter fun entry => entry.1 != token}
  return ⟨token,stage⟩

/-- No callback take or thread switching occurs here. The source engine may
schedule a real destructor frame; errors retain its latest canonical state and
do not restore the closure. -/
def invoke (h : ThreadTlsMachine.Hooks U C O X F A Aff) (choice : C) (callback : TakenTls) : M U StackEmptyPoll := do
  let scratch := capture h callback.stage (← get)
  let (poll,scratch) ← match tlsOnStackEmpty h.platform h.target (ThreadTlsMachine.queries h choice) scratch with
    | .ok poll scratch => pure (poll,scratch)
    | .error error scratch =>
      set (restoreView h scratch)
      throw (h.error error)
  set (restoreView h scratch)
  changeRuntime h fun rt => {rt with tlsCallbacks := rt.tlsCallbacks.push (callback.token,scratch.stage)}
  return match poll with | .Pending => .pending | .Ready => .ready

/-- Source getter selects the thread active after callback execution. Restore
assigns Some(callback), matching the unconditional source assignment. -/
def restore (h : ThreadTlsMachine.Hooks U C O X F A Aff) (callback : TakenTls) : M U Unit := do
  let manager := (← get).machine.threads
  let some thread := manager.activeThread? | throw (.invalidProgram "TLS callback removed active thread")
  unless (h.thread.runtime (← get).machine.user.user).tlsCallbacks.any (fun entry => entry.1 == callback.token) do
    throw (.invalidProgram "TLS callback lost its updated stage")
  let thread := {thread with onStackEmptyCallback := some callback.token}
  ThreadStacks.installManager {manager with threads := manager.threads.set manager.activeThread.toNat thread}

/-- Scheduler and core-step remain the actual caller dictionaries; TLS taking,
invocation, checked restoration, and normal/for_exit termination are closed. -/
def bind (h : ThreadTerminationMachine.Hooks U C O X F A Aff Payload)
    (base : RunLoopHooks (State U) C TakenTls) : RunLoopHooks (State U) C TakenTls :=
  {base with
    takeStackEmptyCallback := fun state => MachineHooks.run (take h.tls) state
    invokeStackEmptyCallback := fun choice callback state => MachineHooks.run (invoke h.tls choice callback) state
    restoreStackEmptyCallback := fun callback state => MachineHooks.run (restore h.tls callback) state
    terminateActiveThread := fun choice forExit state => MachineHooks.run (ThreadTerminationMachine.terminate h choice forExit) state}
/-- Coherent actual scheduler/core-step/stack lifecycle composition. Host I/O,
deadline service and permitted scheduling choices remain the scheduler's real
required leaves, rather than replacement scheduling tokens. -/
def bindActual (h : ThreadTerminationMachine.Hooks U C O X F A Aff Payload)
    (base : RunLoopHooks (State U) C TakenTls)
    (scheduler : C → ThreadStacks.LocalSchedulerHooks MiriMemoryKind U) :
    RunLoopHooks (State U) C TakenTls :=
  ThreadStacks.bindRunLoop (bind h base) scheduler

/-- Execute one real source scheduler iteration with the closed TLS lifecycle. -/
def iteration (h : ThreadTerminationMachine.Hooks U C O X F A Aff Payload)
    (base : RunLoopHooks (State U) C TakenTls)
    (scheduler : C → ThreadStacks.LocalSchedulerHooks MiriMemoryKind U)
    (choice : C) (state : State U) : StepResult (State U) Unit :=
  RunLoop.iteration (bindActual h base scheduler) choice state

end Miri.Interpreter.ThreadLoops
