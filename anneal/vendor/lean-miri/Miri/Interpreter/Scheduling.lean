import Miri.Interpreter.RunLoop
import Miri.Concurrency.Scheduler

/-! Stateful connection of scheduler.rs::schedule to local thread policy. Host readiness/deadline processing remains explicit; choices cover scheduling alternatives. -/

namespace Miri.Interpreter
open Miri.Concurrency

structure SchedulingHooks (S C : Type) where
  manager : S → ThreadManager
  setManager : ThreadManager → S → S
  communicate : S → Bool
  processDelayedReadiness : C → S → StepResult S Unit
  pollNonBlocking : C → S → StepResult S Unit
  unblockExpiredDeadlines : C → S → StepResult S (Option Nat)
  anyThreadBlockedOnHost : S → Bool
  threadRank : C → List ThreadId → Nat

namespace Scheduling
variable {S C : Type}

private def policyError (error : SchedulerError) : StepError :=
  .invalidProgram s!"scheduler policy: {repr error}"

private def finishLocal (hooks : SchedulingHooks S C) (state : S)
    (potentialSleep : Option Nat) (rank : Nat) : StepResult S RunSchedulingAction :=
  match Scheduler.finishLocal (hooks.manager state) potentialSleep
      (hooks.anyThreadBlockedOnHost state) rank with
  | .error error => (state, .error (policyError error))
  | .ok (.executeStep manager _ _) =>
    (hooks.setManager manager state, .ok .executeStep)
  | .ok (.sleepAndWaitForIo manager duration) =>
    (hooks.setManager manager state, .ok (.sleepAndWaitForIo duration))
  | .ok (.globalDeadlock manager) =>
    (hooks.setManager manager state, .error (.termination .globalDeadlock))
  | .ok (.allThreadsTerminatedInvariant manager) =>
    (hooks.setManager manager state, .error (.invalidProgram "all threads terminated without main termination"))

/-- Source local scheduling, with environment effects run in source order.
The communicate setting and thread manager are re-read after callbacks. -/
def localSchedule (hooks : SchedulingHooks S C) (choice : C)
    (state : S) : StepResult S RunSchedulingAction := Id.run do
  let .ok plan := Scheduler.plan (hooks.manager state) false
    | return (state, .error (.invalidProgram "invalid active scheduling thread"))
  match plan with
  | .executeCurrent _ => return (state, .ok .executeStep)
  | .serviceEnvironment _ _ _ =>
    let (state, processed) := hooks.processDelayedReadiness choice state
    let .ok () := processed | return (state, processed.map fun _ => .executeStep)
    let (state, polled) := if hooks.communicate state then hooks.pollNonBlocking choice state
      else (state, .ok ())
    let .ok () := polled | return (state, polled.map fun _ => .executeStep)
    let (state, deadlines) := hooks.unblockExpiredDeadlines choice state
    let .ok potentialSleep := deadlines
      | return (state, deadlines.map fun duration => .sleepAndWaitForIo duration)
    let candidates ← match Scheduler.eligibleThreads (hooks.manager state) with
      | .error error => return (state, .error (policyError error))
      | .ok candidates => pure candidates
    if candidates.isEmpty || (hooks.manager state).fixedScheduling then
      return finishLocal hooks state potentialSleep 0
    return finishLocal hooks state potentialSleep (hooks.threadRank choice candidates)

end Scheduling
end Miri.Interpreter
