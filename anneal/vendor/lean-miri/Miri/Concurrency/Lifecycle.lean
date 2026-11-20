import Miri.Concurrency.GlobalState
import Miri.Concurrency.Thread

/-!
# Ordered thread-finish and join-wakeup protocol

This composes the source order in `thread.rs::terminate_active_thread`:
`beginTerminateActive` marks the thread terminated and removes its TLS entries;
the caller performs each TLS cleanup; this module then runs the selected
termination hook; only then are joiners unblocked one at a time, with each
callback executed in that joiner's active-thread context. Callback execution remains an external obligation. -/
namespace Miri.Concurrency

inductive ThreadFinishHandler where
  | none
  | vectorClocks
  deriving DecidableEq, Repr

inductive ThreadFinishError where
  | globalState (error : GlobalStateError)
  | globalStateRequired
  deriving Repr

inductive PostTlsFinish where
  | wakeJoiners (manager : ThreadManager) (terminated : ThreadId)
      (waiters : List ThreadId)
  | wakeJoinersWithClocks (global : GlobalState) (manager : ThreadManager)
      (terminated : ThreadId) (waiters : List ThreadId)
  deriving Repr

/-- The source's chosen termination handler runs only after
`completeTlsCleanup` has returned its continuation. -/
def afterTlsCleanup (handler : ThreadFinishHandler)
    (continuation : ThreadTerminationContinuation)
    (global : Option GlobalState := none) :
    Except ThreadFinishError PostTlsFinish := do
  let terminated := continuation.dataRaceHookThread
  match handler with
  | .none => pure (.wakeJoiners continuation.manager terminated continuation.joinWaiters)
  | .vectorClocks =>
    let some global := global | throw .globalStateRequired
    let global ← (GlobalState.threadTerminated global continuation.manager).mapError
      ThreadFinishError.globalState
    pure (.wakeJoinersWithClocks global continuation.manager terminated continuation.joinWaiters)

/-- Execute the vector-clock termination hook against an explicitly supplied
global state. The production state is not replaced by a fresh initial state. -/
def afterTlsCleanupWithGlobal (global : GlobalState)
    (continuation : ThreadTerminationContinuation) :
    Except ThreadFinishError PostTlsFinish := do
  let terminated := continuation.dataRaceHookThread
  let global ← (GlobalState.threadTerminated global continuation.manager).mapError
    ThreadFinishError.globalState
  pure (.wakeJoinersWithClocks global continuation.manager terminated continuation.joinWaiters)

/-- One wakeup iteration. Miri's `unblock_thread` invokes the callback
synchronously; Lean exposes the exact callback action and leaves its effects
to the interpreter. -/
inductive JoinWakeStep where
  | complete (manager : ThreadManager)
  | invokeCallback (manager : ThreadManager) (terminated : ThreadId)
      (unblock : UnblockCallbackObligation) (remaining : List ThreadId)
  | callbackFailed (managerAfterFailure : ThreadManager)
      (terminated : ThreadId) (unblock : UnblockCallbackObligation)
      (remaining : List ThreadId)
  deriving Repr

namespace ThreadManager

/-- Start ordered joiner wakeups after TLS and the selected termination hook
have both completed. -/
def beginJoinerWakeups (manager : ThreadManager) (terminated : ThreadId)
    (waiters : List ThreadId) : Except ThreadError JoinWakeStep := do
  match waiters with
  | [] => pure (.complete manager)
  | waiter :: remaining =>
    let (withWaiterActive, callback) ← unblockThread manager waiter (.Join terminated)
    pure (.invokeCallback withWaiterActive terminated callback remaining)

/-- Continue after actually invoking one callback. On callback failure the
source returns immediately, preserving the post-failure machine state and
leaving later joiners blocked. On success the scheduler restores the previous
active thread before issuing the next callback. -/
def continueJoinerWakeups (managerAfterCallback : ThreadManager)
    (terminated : ThreadId) (callback : UnblockCallbackObligation)
    (remaining : List ThreadId)
    (returnedNormally : Bool) : Except ThreadError JoinWakeStep := do
  if !returnedNormally then
    pure (.callbackFailed managerAfterCallback terminated callback remaining)
  else
    let restored := restoreAfterCallback managerAfterCallback callback
    beginJoinerWakeups restored terminated remaining

end ThreadManager

end Miri.Concurrency
