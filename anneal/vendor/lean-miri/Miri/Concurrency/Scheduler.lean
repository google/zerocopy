import Miri.Concurrency.Thread
import Miri.Concurrency.Termination

/-! Miri's local scheduling policy: preserve the fast path, ordered readiness/I/O/deadline effects, cyclic candidate order, fixed scheduling, and sleep/deadlock outcomes. Host effects remain explicit obligations. -/

namespace Miri.Concurrency

/-- Scheduler actions that require an interpreter or host callback before
Miri can choose a local runnable thread. -/
inductive SchedulerEnvironmentAction where
  | processDelayedReadiness
  | pollHostIoNonBlocking
  | unblockExpiredDeadlines
  deriving DecidableEq, Repr

/-- Result of the scheduler's first-stage dispatch. -/
inductive SchedulerPlan where
  | executeCurrent (manager : ThreadManager)
  | serviceEnvironment (manager : ThreadManager) (communicate : Bool)
      (actions : List SchedulerEnvironmentAction)
  deriving Repr

inductive SchedulerError where
  | thread (reason : ThreadError)
  | nondeterministicChoiceOutOfBounds (rank candidateCount : Nat)
  deriving DecidableEq, Repr

/-- Final action of a local scheduling decision. -/
inductive SchedulerAction where
  | executeStep (manager : ThreadManager) (thread : ThreadId)
      (eligibleChoices : List ThreadId)
  | sleepAndWaitForIo (manager : ThreadManager) (duration : Option Nat)
  | globalDeadlock (manager : ThreadManager)
  | allThreadsTerminatedInvariant (manager : ThreadManager)
  deriving Repr

namespace Scheduler

/-- The local scheduler's terminal stop is Miri's diagnostic deadlock result,
not a UB result. Local deadlocks detected by synchronization shims enter
through `TerminationInfo.localDeadlock` directly. -/
def terminationInfo : SchedulerAction → Option TerminationInfo
  | .globalDeadlock _ => some .globalDeadlock
  | .executeStep _ _ _ | .sleepAndWaitForIo _ _
  | .allThreadsTerminatedInvariant _ => none

/-- Return Miri's exact cyclic thread visitation order: IDs after the current
thread, then IDs through the current thread. -/
def roundRobinOrder (manager : ThreadManager) : Except SchedulerError (List ThreadId) := do
  let active := manager.activeThread.toNat
  if (manager.thread? manager.activeThread).isNone then
    throw (.thread (.activeIdOutOfBounds manager.activeThread))
  let indices := List.range manager.threads.length
  let cyclic := (indices.drop (active + 1)) ++ (indices.take (active + 1))
  cyclic.mapM fun index =>
    (ThreadId.ofNat index).mapError SchedulerError.thread

/-- Enabled IDs in the source iterator's cyclic order. -/
def eligibleThreads (manager : ThreadManager) : Except SchedulerError (List ThreadId) := do
  let ordered ← roundRobinOrder manager
  ordered.filterM fun id =>
    match manager.thread? id with
    | none => throw (.thread (.activeIdOutOfBounds id))
    | some thread => pure thread.isEnabled

def plan (manager : ThreadManager) (communicate : Bool) :
    Except SchedulerError SchedulerPlan := do
  let some active := manager.activeThread?
    | throw (.thread (.activeIdOutOfBounds manager.activeThread))
  if active.isEnabled && !manager.yieldActiveThread then
    return .executeCurrent manager
  let actions := [SchedulerEnvironmentAction.processDelayedReadiness] ++
    (if communicate then [.pollHostIoNonBlocking] else []) ++
    [SchedulerEnvironmentAction.unblockExpiredDeadlines]
  return .serviceEnvironment manager communicate actions

/-- Finish the local scheduler policy after the listed environment callbacks
have returned. `rank` is an explicit choice among all enabled source
candidates when scheduling is nondeterministic; it is ignored under Miri's
fixed-scheduling mode. The caller supplies deadline and host-I/O facts from
the actual machine state. -/
def finishLocal (managerAfterEnvironment : ThreadManager)
    (potentialSleepTime : Option Nat) (anyThreadBlockedOnHost : Bool)
    (rank : Nat) : Except SchedulerError SchedulerAction := do
  let choices ← eligibleThreads managerAfterEnvironment
  let managerReady := { managerAfterEnvironment with yieldActiveThread := false }
  if !choices.isEmpty then
    let selected ← if managerAfterEnvironment.fixedScheduling then
        match choices with
        | first :: _ => pure first
        | [] => throw (.nondeterministicChoiceOutOfBounds rank 0)
      else
        match choices[rank]? with
        | some id => pure id
        | none => throw (SchedulerError.nondeterministicChoiceOutOfBounds rank choices.length)
    let switched ← (managerReady.setActiveThread selected).mapError SchedulerError.thread
    return .executeStep switched.1 selected choices

  if managerReady.threads.all ThreadRecord.isTerminated then
    return .allThreadsTerminatedInvariant managerReady
  if let some duration := potentialSleepTime then
    return .sleepAndWaitForIo managerReady (some duration)
  if anyThreadBlockedOnHost then
    return .sleepAndWaitForIo managerReady none
  return .globalDeadlock managerReady

end Scheduler

end Miri.Concurrency
