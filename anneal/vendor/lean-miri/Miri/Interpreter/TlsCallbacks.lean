import Miri.Interpreter.TlsDestructors

/-! Pinned concurrency/scheduler.rs::run_on_stack_empty (31-41),
step_current_thread (174-186), and thread.rs new-thread captured TlsDtorsState.
The closure registry supplies real mutable destructor state for opaque callback
tokens. Taking a closure removes it before invocation; errors do not restore it.
Callbacks for main/program exit remain distinct mandatory orchestration. -/
namespace Miri.Interpreter
open Miri.Memory Miri.ABI Miri.Concurrency

structure TlsCallback (P : Type) where
  token : Nat
  stage : TlsDtorsStage P
structure TlsCallbacksState (P E H : Type) where
  execution : TlsExecutionState P E H
  callbacks : Array (TlsCallback P)
inductive TlsCallbackError (Error : Type) where
  | thread (error : ThreadError)
  | missingCallback
  | duplicateCallbackToken (token : Nat)
  | unknownCallbackToken (token : Nat)
  | callback (error : TlsExecutionError Error)
  | termination (error : ThreadExitError Error)
  deriving Repr
abbrev TlsCallbackM (P E H Error A : Type) := EStateM (TlsCallbackError Error) (TlsCallbacksState P E H) A

/-- Register the closure captured for a new ordinary thread. Allocation of the
opaque callback token belongs to the caller; duplicate tokens are rejected. -/
def registerTlsCallback (state : TlsCallbacksState P E H) (token : Nat) : Except (TlsCallbackError Error) (TlsCallbacksState P E H) := do
  if state.callbacks.any (·.token == token) then throw (.duplicateCallbackToken token)
  pure { state with callbacks := state.callbacks.push ⟨token,.init⟩ }

/-- The explicit dummy-span token must name the source DUMMY_SP in the caller's
span-token representation. It is not a fabricated span for an actual MIR site. -/
def runTlsOnStackEmpty [PointerProvenance P] (dummySpanToken : Nat)
    (platform : TlsPlatform) (target : RuntimeTargetDataLayout) (queries : TlsDestructorQueries P E H Error) :
    TlsCallbackM P E H Error StackEmptyCallbackResult := do
  let before ← EStateM.get
  let manager := before.execution.exit.tls.manager
  let some thread := manager.activeThread? | throw (.thread (.activeIdOutOfBounds manager.activeThread))
  let reset := { thread with originSpanToken := dummySpanToken }
  let manager := { manager with threads := manager.threads.set manager.activeThread.toNat reset }
  let resetState := { before with execution := { before.execution with exit := { before.execution.exit with
    tls := { before.execution.exit.tls with manager := manager } } } }
  EStateM.set resetState
  let some token := reset.onStackEmptyCallback | throw .missingCallback
  -- Source takes the callback before invoking it, preventing recursive reentry.
  let manager := { manager with threads := manager.threads.set manager.activeThread.toNat { reset with onStackEmptyCallback := none } }
  let taken := { resetState with execution := { resetState.execution with exit := { resetState.execution.exit with
    tls := { resetState.execution.exit.tls with manager := manager } } } }
  EStateM.set taken
  let some callback := taken.callbacks.find? (·.token == token) | throw (.unknownCallbackToken token)
  let ready := { taken with
    callbacks := taken.callbacks.filter (fun entry => entry.token != token)
    execution := { taken.execution with stage := callback.stage } }
  EStateM.set ready
  let (result,executed) ← match tlsOnStackEmpty platform target queries ready.execution with
    | .error error executed =>
      EStateM.set { ready with execution := executed }
      throw (.callback error)
    | .ok result executed => pure (result,executed)
  EStateM.set { ready with execution := executed }
  let manager := executed.exit.tls.manager
  let some thread := manager.activeThread? | throw (.thread (.activeIdOutOfBounds manager.activeThread))
  let manager := { manager with threads := manager.threads.set manager.activeThread.toNat { thread with onStackEmptyCallback := some token } }
  EStateM.set { ready with
    execution := { executed with exit := { executed.exit with tls := { executed.exit.tls with manager := manager } } },
    callbacks := ready.callbacks.push ⟨token,executed.stage⟩ }
  pure result

/-- Invoke only after the actual interpreter step reports an empty stack.
Ready means normal thread termination; main/program-exit callbacks use their
separate handler and must not be routed through this TLS-only entrypoint. -/
def stepEmptyTlsThread [PointerProvenance P] (dummySpanToken : Nat)
    (platform : TlsPlatform) (target : RuntimeTargetDataLayout)
    (queries : TlsDestructorQueries P E H Error) (exit : ThreadExitQueries P E H ProvExtra Error) :
    TlsCallbackM P E H Error Unit := do
  match ← runTlsOnStackEmpty dummySpanToken platform target queries with
  | .Pending => pure ()
  | .Ready =>
    let state ← EStateM.get
    match terminateActiveThread exit false state.execution.exit with
    | .ok () next => EStateM.set { state with execution := { state.execution with exit := next } }
    | .error error next =>
      EStateM.set { state with execution := { state.execution with exit := next } }
      throw (.termination error)

end Miri.Interpreter
