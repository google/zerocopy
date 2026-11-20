import Miri.Input.EvalWorld
import Miri.Interpreter.ExecutionStateTransport

/-! Source foreign_items.rs::exit and Windows ExitProcess share the actual
ProgramExitHandler::ExitCalled state machine. Its FnMut capture is stored in
World, separate from main/TLS and FnOnce unblock environments. -/
namespace Miri.Input.EvalForeignExit
open Miri.ABI Miri.Memory Miri.MIR Miri.Interpreter
abbrev World := EvalWorld.World
abbrev User Os R P H D O Aff B Host := ValidityMachine.UserState (World Os R P H D O Aff B Host)
abbrev State Os R P H D O Aff B Host := ThreadStacks.State MiriMemoryKind (User Os R P H D O Aff B Host)

/-- Source replace_active_thread_stack needs only current-user span metadata;
all callback/entry/runtime fields are read from their canonical World owners. -/
def startSource (spans : AllocationDriver.SpanHooks) (code : Int32) :
    EStateM StepError (State Os R P H D O Aff B Host) Unit := do
  let span ← AllocationDriver.currentUserRelevantSpan spans
  let state : State Os R P H D O Aff B Host ← get
  let manager := state.machine.threads
  let some thread := manager.activeThread? | throw (.invalidProgram "ExitCalled active thread missing")
  let world := state.machine.user.user.payload.payload
  let rt := world.runtime.threads
  if let some old := thread.onStackEmptyCallback then
    let mainOwned := world.main.any (·.token == old)
    let exitOwned := world.exit.handlers.any (·.token == old)
    let tlsOwned := rt.tlsCallbacks.any (·.1 == old)
    unless mainOwned || exitOwned || tlsOwned do
      throw (.unsupported "replaced stack callback ownership is unavailable")
  let token := rt.nextCallback
  let rt := {rt with nextCallback := token+1, tlsCallbacks := rt.tlsCallbacks.filter fun entry => some entry.1 != thread.onStackEmptyCallback}
  let clearsMain := world.main.any (fun main => some main.token == thread.onStackEmptyCallback)
  let entry := if clearsMain then {world.runtime.entry with mainReturn := none} else world.runtime.entry
  let world := {world with
    main := if clearsMain then none else world.main
    runtime := {world.runtime with threads := rt,entry}
    exit := {handlers := (world.exit.handlers.filter fun (handler : WindowsExitMachine.Handler) => some handler.token != thread.onStackEmptyCallback ).push ⟨token,.tls,.initForExit,code⟩}}
  set ({state with stack := Stack.empty, machine := {state.machine with user := {state.machine.user with user :=
    {state.machine.user.user with payload := {state.machine.user.user.payload with payload := world}}}}} : State Os R P H D O Aff B Host)
  let thread := {thread with originSpanToken := span.id, topUserRelevantFrame := none, onStackEmptyCallback := some token}
  ThreadStacks.installManager {manager with threads := manager.threads.set manager.activeThread.toNat thread}

def startInnerSource (spans : AllocationDriver.SpanHooks) (code : Int32) :
    MachineHooks.M MiriMemoryKind (ExecutionStateTransport.Inner (World Os R P H D O Aff B Host)) Unit :=
  ExecutionStateTransport.reverseAction (startSource (Os:=Os) (R:=R) (P:=P) (H:=H) (D:=D) (O:=O) (Aff:=Aff) (B:=B) (Host:=Host) spans code)

def hooks (main : MainMachine.Hooks (User Os R P H D O Aff B Host) C O X F A Aff Payload) :
    WindowsExitMachine.Hooks (User Os R P H D O Aff B Host) C O X F A Aff Payload where
  main := main
  get := fun u => u.payload.payload.exit
  put := fun u exit => {u with payload := {u.payload with payload := {u.payload.payload with exit}}}

def start (main : MainMachine.Hooks (User Os R P H D O Aff B Host) C O X F A Aff Payload)
    (code : Int32) : EStateM StepError (State Os R P H D O Aff B Host) Unit :=
  WindowsExitMachine.start (hooks main) code

def startInner (main : MainMachine.Hooks (User Os R P H D O Aff B Host) C O X F A Aff Payload)
    (code : Int32) :=
  ExecutionStateTransport.reverseAction (start main code)

def loop (main : MainMachine.Hooks (User Os R P H D O Aff B Host) C O X F A Aff Payload)
    (base : RunLoopHooks (State Os R P H D O Aff B Host) C MainMachine.Callback)
    (scheduler : C → ThreadStacks.LocalSchedulerHooks MiriMemoryKind (User Os R P H D O Aff B Host)) :=
  let exitHooks := hooks main
  let exitBase : RunLoopHooks (State Os R P H D O Aff B Host) C WindowsExitMachine.Callback := {
    base with
    takeStackEmptyCallback := fun state => MachineHooks.run (WindowsExitMachine.take exitHooks) state
    invokeStackEmptyCallback := fun choice callback state => MachineHooks.run
      (match callback with
       | .exitHandler handler => WindowsExitMachine.invoke exitHooks choice handler
       | .mainOrTls (.main _) => MainMachine.invoke main choice
       | .mainOrTls (.tls callback) => ThreadLoops.invoke main.termination.tls choice callback) state
    restoreStackEmptyCallback := fun callback state =>
      MachineHooks.run (WindowsExitMachine.restore exitHooks callback) state }
  WindowsExitMachine.bindLoop exitHooks exitBase scheduler
end Miri.Input.EvalForeignExit
