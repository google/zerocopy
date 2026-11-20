import Miri.Interpreter.MainMachine
import Miri.Interpreter.WindowsPlatformDispatch

/-! thread.rs replace_active_thread_stack and eval.rs ProgramExitHandler,
ExitCalled variant, connected to the same actual main/TLS scheduler callbacks. -/
namespace Miri.Interpreter.WindowsExitMachine
open Miri.ABI Miri.Memory Miri.Concurrency Miri.TreeBorrows
abbrev State := MainMachine.State
abbrev M := MainMachine.M
structure Handler where
  token : Nat
  stage : ProgramExitStage
  tls : TlsDtorsStage Provenance
  code : Int32
structure Registry where
  handlers : Array Handler := #[]
structure Hooks (U C O X F A Aff P : Type) where
  main : MainMachine.Hooks U C O X F A Aff P
  get : U → Registry
  put : U → Registry → U
private def registry (h : Hooks U C O X F A Aff P) : M U Registry :=
  return h.get (← get).machine.user.user
private def modifyRegistry (h : Hooks U C O X F A Aff P) (f : Registry → Registry) : M U Unit :=
  modify fun state => {state with machine := {state.machine with user := {state.machine.user with
    user := h.put state.machine.user.user (f (h.get state.machine.user.user))}}}
private def store (h : Hooks U C O X F A Aff P) (handler : Handler) : M U Unit :=
  modifyRegistry h fun registry => {handlers := registry.handlers.push handler}

/-- Source clears frame owners, leaking allocations without running pops,
retags, destructors, or deallocation hooks. Diagnostic origin is captured first. -/
def start (h : Hooks U C O X F A Aff P) (code : Int32) : M U Unit := do
  let threadHooks := h.main.termination.tls.thread
  let span ← AllocationDriver.currentUserRelevantSpan threadHooks.spans
  let manager := (← get).machine.threads
  let some thread := manager.activeThread? | throw (.invalidProgram "ExitProcess active thread missing")
  let rt := threadHooks.runtime (← get).machine.user.user
  if let some old := thread.onStackEmptyCallback then
    let mainOwned := (h.main.data (← get).machine.user.user).any (·.token == old)
    let exitOwned := (← registry h).handlers.any (·.token == old)
    let tlsOwned := rt.tlsCallbacks.any (·.1 == old)
    unless mainOwned || exitOwned || tlsOwned do
      throw (.unsupported "replaced stack callback ownership is unavailable")
  let token := rt.nextCallback
  let rt := {rt with nextCallback := token+1, tlsCallbacks := rt.tlsCallbacks.filter fun entry => some entry.1 != thread.onStackEmptyCallback}
  modify fun state => {state with stack := Stack.empty, machine := {state.machine with user := {state.machine.user with
    user := threadHooks.putRuntime state.machine.user.user rt}}}
  if let some main := h.main.data (← get).machine.user.user then
    if some main.token == thread.onStackEmptyCallback then
      modify fun state =>
        let payload := h.main.putData state.machine.user.user none
        let entry := h.main.entry payload
        let payload := h.main.putEntry payload {entry with mainReturn := none}
        {state with machine := {state.machine with user := {state.machine.user with user := payload}}}
  modifyRegistry h fun registry => {handlers := registry.handlers.filter fun handler => some handler.token != thread.onStackEmptyCallback}
  store h ⟨token,.tls,.initForExit,code⟩
  let thread := {thread with originSpanToken := span.id, topUserRelevantFrame := none, onStackEmptyCallback := some token}
  ThreadStacks.installManager {manager with threads := manager.threads.set manager.activeThread.toNat thread}

private def capture (h : Hooks U C O X F A Aff P) (stage : TlsDtorsStage Provenance) (state : State U) : ThreadTlsMachine.Scratch U :=
  let tls := h.main.termination.tls
  let data := tls.data state.machine.user.user
  let memory : ThreadLocalState Provenance BorrowTree (State U) :=
    ⟨state.machine.memory,state,state.machine.threads,data.statics⟩
  let race := match state.machine.dataRace with
    | none => .none | some global => .vectorClocks global
  ⟨⟨memory,data.staticRoots,race⟩,data.values,stage⟩
private def restoreView (h : Hooks U C O X F A Aff P) (view : ThreadTlsMachine.Scratch U) : State U :=
  let state := view.exit.tls.hooks
  let data : ThreadTlsMachine.Data := ⟨view.data,view.exit.tls.pointers,view.exit.staticRoots⟩
  let payload := h.main.termination.tls.putData state.machine.user.user data
  {state with machine := {state.machine with memory := view.exit.tls.memory, threads := view.exit.tls.manager, user := {state.machine.user with user := payload}, dataRace := match view.exit.race with
      | .none => none | .vectorClocks global => some global}}

/-- Invoked only after take moved the actual owned handler out of the registry. -/
def invoke (h : Hooks U C O X F A Aff P) (choice : C) (handler : Handler) : M U StackEmptyPoll := do
  match handler.stage with
  | .tls =>
    let tls := h.main.termination.tls
    let view := capture h handler.tls (← get)
    let (poll,view) ← match tlsOnStackEmpty tls.platform tls.target (ThreadTlsMachine.queries tls choice) view with
      | .ok poll view => pure (poll,view)
      | .error error view => set (restoreView h view); throw (tls.error error)
    set (restoreView h view)
    let stage := if poll == .Ready then
      .yield 256
      else .tls
    store h {handler with stage, tls := view.stage}
  | .yield remaining =>
    if remaining == 0 then store h {handler with stage := .done}
    else
      ThreadStacks.installManager (← get).machine.threads.yield
      store h {handler with stage := .yield (remaining-1)}
  | .done =>
    ThreadTerminationMachine.terminate h.main.termination choice true

    throw (.termination (.exit handler.code.toInt false))
  | .unreachable => throw (.invalidProgram "unreachable ExitCalled handler")
  return .pending

inductive Callback where
  | exitHandler (handler : Handler)
  | mainOrTls (callback : MainMachine.Callback)

def take (h : Hooks U C O X F A Aff P) : M U Callback := do
  let manager := (← get).machine.threads
  let some thread := manager.activeThread? | throw (.invalidProgram "exit callback active thread missing")
  let candidate := (← registry h).handlers.find? fun handler => some handler.token == thread.onStackEmptyCallback
  if let some handler := candidate then
    unless (← get).stack.frames.isEmpty do throw (.invalidProgram "exit callback requires empty stack")
    let thread := {thread with onStackEmptyCallback := none, originSpanToken := h.main.termination.tls.thread.spans.dummy.id}
    ThreadStacks.installManager {manager with threads := manager.threads.set manager.activeThread.toNat thread}
    modifyRegistry h fun registry => {handlers := registry.handlers.filter fun item => item.token != handler.token}
    return .exitHandler handler
  return .mainOrTls (← MainMachine.take h.main)

def restore (h : Hooks U C O X F A Aff P) : Callback → M U Unit
  | .mainOrTls callback => MainMachine.restore h.main callback
  | .exitHandler handler => do
    unless (← registry h).handlers.any (·.token == handler.token) do
      throw (.invalidProgram "exit callback lost its updated stage")
    let manager := (← get).machine.threads
    let some thread := manager.activeThread? | throw (.invalidProgram "exit callback removed active thread")
    ThreadStacks.installManager {manager with threads := manager.threads.set manager.activeThread.toNat {thread with onStackEmptyCallback := some handler.token}}

def bindLoop (h : Hooks U C O X F A Aff P) (base : RunLoopHooks (State U) C Callback)
    (scheduler : C → ThreadStacks.LocalSchedulerHooks MiriMemoryKind U) : RunLoopHooks (State U) C Callback :=
  ThreadStacks.bindRunLoop {base with
    takeStackEmptyCallback := fun state => MachineHooks.run (take h) state
    invokeStackEmptyCallback := fun choice callback state => MachineHooks.run
      (match callback with
       | .exitHandler handler => invoke h choice handler
       | .mainOrTls (.main _) => MainMachine.invoke h.main choice
       | .mainOrTls (.tls callback) => ThreadLoops.invoke h.main.termination.tls choice callback) state
    restoreStackEmptyCallback := fun callback state => MachineHooks.run (restore h callback) state
    terminateActiveThread := fun choice forExit state => MachineHooks.run (ThreadTerminationMachine.terminate h.main.termination choice forExit) state} scheduler

def bindPlatform (h : Hooks U C O X F A Aff P)
    (base : WindowsPlatformDispatch.Hooks (State U) Os E Kind FD) :
    WindowsPlatformDispatch.Hooks (State U) Os E Kind FD := {base with startExit := start h}
end Miri.Interpreter.WindowsExitMachine
