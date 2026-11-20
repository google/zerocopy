import Miri.Interpreter.TlsDestructors

/-! Pinned eval.rs::ProgramExitHandler: run TLS cleanup, yield 256 times, then terminate with for_exit=true. Machine stop remains an explicit outcome. -/

namespace Miri.Interpreter
open Miri.ABI Miri.Memory Miri.Concurrency

inductive ProgramExitType where
  | mainThreadFinish | exitCalled
  deriving Repr, DecidableEq
inductive ProgramExitStage where
  | tls
  | yield (remaining : UInt32)
  | done
  | unreachable
  deriving Repr, DecidableEq
structure ProgramExitState (P E H : Type) where
  execution : TlsExecutionState P E H
  stage : ProgramExitStage
  exitCode : Int32
  exitType : ProgramExitType
inductive ProgramExitError (Error : Type) where
  | tls (error : TlsExecutionError Error)
  | termination (error : ThreadExitError Error)
  | leaf (error : Error)
  | unreachableHandler
  deriving Repr
inductive ProgramExitPoll where
  | pending
  | machineStop (exitCode : Int32) (leakCheck : Bool)
  deriving Repr, DecidableEq
abbrev ProgramExitM (P E H Error A : Type) := EStateM (ProgramExitError Error) (ProgramExitState P E H) A

/-- Source constructs a fresh TlsDtorsState::new_for_exit, retaining the actual
machine/TLS data. The handler is separate from normal-thread callback state. -/
def ProgramExitState.new (state : TlsExecutionState P E H) (exitCode : Int32)
    (exitType : ProgramExitType) : ProgramExitState P E H :=
  ⟨{ state with stage := .initForExit }, .tls, exitCode, exitType⟩

/-- Actual ordered stateful exit protocol, including state changes before a
failed callback. A source machine-stop outcome must stop the interpreter loop;
it is not a normal Poll::Ready return from the callback. -/
def programExitOnStackEmpty [PointerProvenance P] (platform : TlsPlatform) (target : RuntimeTargetDataLayout)
    (destructors : TlsDestructorQueries P E H Error) (termination : ThreadExitQueries P E H ProvExtra Error)
    : ProgramExitM P E H Error ProgramExitPoll := do
  let state ← EStateM.get
  match state.stage with
  | .tls =>
    let (poll,next) ← match tlsOnStackEmpty platform target destructors state.execution with
      | .ok poll next => pure (poll,next)
      | .error error next => EStateM.set { state with execution := next }; throw (.tls error)
    EStateM.set { state with execution := next }
    match poll with
    | .Pending => pure .pending
    | .Ready =>
      let stage := .yield 256
      EStateM.set { state with execution := next, stage := stage }
      pure .pending
  | .yield remaining =>
    if remaining == 0 then
      EStateM.set { state with stage := .done }
    else
      let manager := state.execution.exit.tls.manager.yield
      EStateM.set { state with stage := .yield (remaining - 1), execution := { state.execution with
        exit := { state.execution.exit with tls := { state.execution.exit.tls with manager := manager } } } }
    pure .pending
  | .done =>
    let next ← match terminateActiveThread termination true state.execution.exit with
      | .ok () next => pure next
      | .error error next =>
        EStateM.set { state with execution := { state.execution with exit := next } }
        throw (.termination error)
    let finished := { state with stage := .unreachable, execution := { state.execution with exit := next } }
    EStateM.set finished
    pure (.machineStop state.exitCode (state.exitType == .mainThreadFinish))
  | .unreachable => throw .unreachableHandler

end Miri.Interpreter
