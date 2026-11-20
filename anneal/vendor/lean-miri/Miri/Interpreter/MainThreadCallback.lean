import Miri.Interpreter.MainThread

/-! Pinned concurrency/scheduler.rs::run_on_stack_empty (31-41), instantiated
for eval.rs::MainThreadState's captured closure. Source take/reset/invoke/restore
ordering is preserved. Machine-stop exits and errors do not restore the taken
callback; successful Pending (including callback continuation) restores it. -/
namespace Miri.Interpreter
open Miri.ABI Miri.Memory Miri.Concurrency
structure MainThreadCallbackState (P E H : Type) where
  main : MainThreadState P E H
  token : Nat
  installed : Bool
inductive MainThreadCallbackError (Error : Type) where
  | thread (error : ThreadError)
  | unavailableCallback
  | wrongCallback (expected : Nat) (actual : Option Nat)
  | body (error : MainThreadError Error)
  deriving Repr
abbrev MainThreadCallbackM (P E H Error A : Type) := EStateM (MainThreadCallbackError Error) (MainThreadCallbackState P E H) A

private def MainThreadState.manager (main : MainThreadState P E H) : ThreadManager :=
  main.constructors.execution.exit.tls.manager
private def MainThreadState.withManager (main : MainThreadState P E H) (manager : ThreadManager) : MainThreadState P E H :=
  { main with constructors := { main.constructors with execution := { main.constructors.execution with
    exit := { main.constructors.execution.exit with tls := { main.constructors.execution.exit.tls with manager := manager } } } } }

/-- The dummy-span token must denote actual source DUMMY_SP in the caller's
span representation. It is deliberately supplied rather than inventing span0. -/
def runMainThreadCallback (dummySpanToken : Nat) (body : MainThreadM P E H Error ProgramExitPoll) :
    MainThreadCallbackM P E H Error ProgramExitPoll := do
  let before ← EStateM.get
  let manager := before.main.manager
  let some thread := manager.activeThread? | throw (.thread (.activeIdOutOfBounds manager.activeThread))
  let reset := { thread with originSpanToken := dummySpanToken }
  let manager := { manager with threads := manager.threads.set manager.activeThread.toNat reset }
  let resetState := { before with main := before.main.withManager manager }
  EStateM.set resetState
  unless before.installed do throw .unavailableCallback
  unless reset.onStackEmptyCallback == some before.token do throw (.wrongCallback before.token reset.onStackEmptyCallback)
  let manager := { manager with threads := manager.threads.set manager.activeThread.toNat { reset with onStackEmptyCallback := none } }
  let taken := { resetState with main := resetState.main.withManager manager, installed := false }
  EStateM.set taken
  let (poll,main) ← match body taken.main with
    | .ok poll main => pure (poll,main)
    | .error error main => EStateM.set { taken with main := main }; throw (.body error)
  EStateM.set { taken with main := main }
  match poll with
  | .machineStop _ _ => pure poll
  | .pending =>
    let manager := main.manager
    let some thread := manager.activeThread? | throw (.thread (.activeIdOutOfBounds manager.activeThread))
    let manager := { manager with threads := manager.threads.set manager.activeThread.toNat { thread with onStackEmptyCallback := some before.token } }
    EStateM.set { taken with main := main.withManager manager, installed := true }
    pure .pending

/-- Complete main/global-ctor/main-return/program-exit callback, for an actual
empty stack. Entry selection and machine initialization precede this API. -/
def runMainThreadOnStackEmpty [PointerProvenance P] (dummySpanToken : Nat)
    (format : ConstructorBinaryFormat) (platform : TlsPlatform) (target : RuntimeTargetDataLayout)
    (constructors : GlobalCtorQueries P E H Error) (main : MainThreadQueries P E H Error)
    (destructors : TlsDestructorQueries P E H Error) (termination : ThreadExitQueries P E H ProvExtra Error)
    : MainThreadCallbackM P E H Error ProgramExitPoll :=
  runMainThreadCallback dummySpanToken
    (mainThreadOnStackEmpty format platform target constructors main destructors termination)

end Miri.Interpreter
