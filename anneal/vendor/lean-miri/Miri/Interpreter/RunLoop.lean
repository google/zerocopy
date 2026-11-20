import Miri.Interpreter.Step

/-! Miri scheduler.rs `run_on_stack_empty`, `step_current_thread` and one
`run_threads` iteration. Empty MIR stack is not program termination: callbacks,
TLS destructors and termination hooks still run. Environment effects and thread
storage are required operations, not assumed successes. -/
namespace Miri.Interpreter
open Miri.Concurrency

inductive StackEmptyPoll where
  | pending
  | ready
  deriving Repr, DecidableEq

inductive RunSchedulingAction where
  | executeStep
  | sleepAndWaitForIo (duration : Option Nat)
  deriving Repr, DecidableEq

structure RunLoopHooks (S C Callback : Type) where
  coreStep : C → S → StepResult S Bool
  /-- Reset the diagnostic origin and take the active thread's callback;
  recursive invocation must observe it as absent until restoration. -/
  takeStackEmptyCallback : S → StepResult S Callback
  invokeStackEmptyCallback : C → Callback → S → StepResult S StackEmptyPoll
  /-- Restore on the thread active after the callback, matching Miri's getter. -/
  restoreStackEmptyCallback : Callback → S → StepResult S Unit
  terminateActiveThread : C → Bool → S → StepResult S Unit
  interrupted : S → Bool
  handleAbnormalTermination : S → S
  schedule : C → S → StepResult S RunSchedulingAction
  communicate : S → Bool
  pollAndUnblock : C → Option Nat → S → StepResult S Unit
  sleep : C → Nat → S → StepResult S Unit

namespace RunLoop
variable {S C Callback : Type}

def runOnStackEmpty (hooks : RunLoopHooks S C Callback) (choice : C)
    (state : S) : StepResult S StackEmptyPoll :=
  let (state, taken) := hooks.takeStackEmptyCallback state
  match taken with
  | .error error => (state, .error error)
  | .ok callback =>
    let (state, result) := hooks.invokeStackEmptyCallback choice callback state
    match result with
    | .error error => (state, .error error)
    | .ok poll =>
      let (state, restored) := hooks.restoreStackEmptyCallback callback state
      match restored with
      | .ok () => (state, .ok poll)
      | .error error => (state, .error error)

def stepCurrentThread (hooks : RunLoopHooks S C Callback) (choice : C)
    (state : S) : StepResult S Unit :=
  let (state, stepped) := hooks.coreStep choice state
  match stepped with
  | .error error => (state, .error error)
  | .ok true => (state, .ok ())
  | .ok false =>
    let (state, poll) := runOnStackEmpty hooks choice state
    match poll with
    | .error error => (state, .error error)
    | .ok .pending => (state, .ok ())
    | .ok .ready => hooks.terminateActiveThread choice false state

/-- One outer-loop iteration; success means another iteration is required.
A fuel-bound runner must report fuel exhaustion as unknown, never as a return. -/
def iteration (hooks : RunLoopHooks S C Callback) (choice : C)
    (state : S) : StepResult S Unit :=
  if hooks.interrupted state then
    (hooks.handleAbnormalTermination state, .error (.termination .interrupted))
  else
    let (state, scheduled) := hooks.schedule choice state
    match scheduled with
    | .error error => (state, .error error)
    | .ok .executeStep => stepCurrentThread hooks choice state
    | .ok (.sleepAndWaitForIo duration) =>
      if hooks.communicate state then hooks.pollAndUnblock choice duration state
      else
        match duration with
        | some duration => hooks.sleep choice duration state
        | none => (state, .error (.invalidProgram "infinite isolated sleep"))

/-- These observers classify results; they do not prove completeness of any
supplied hooks or establish a Rust safety theorem. -/
def reportsUB : StepError → Bool
  | .undefinedBehavior _ => true
  | .retagWriteToReadOnly => true
  | .termination info => info.isUbReport
  | _ => false

end RunLoop
end Miri.Interpreter
