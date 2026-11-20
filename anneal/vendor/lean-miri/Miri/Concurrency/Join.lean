import Miri.Concurrency.GlobalState
import Miri.Concurrency.Thread

/-!
# Thread joining and completion obligations

This follows `concurrency/thread.rs::join_thread` and
`join_thread_exclusive`. It mutates the join status before waiting and leaves the
completion synchronization and return-place write as ordered obligations.
The source's actual callback and pointer write remain
external actions; this module cannot silently complete them.
-/
namespace Miri.Concurrency

/-- A join's opaque MIR scalar and destination place, preserved for the
interpreter callback that eventually writes the return value. -/
structure JoinReturn where
  scalarToken : Nat
  placeToken : Nat
  deriving DecidableEq, Repr

inductive JoinHandler where
  | none
  | vectorClocks
  deriving DecidableEq, Repr

inductive JoinError where
  | thread (error : ThreadError)
  | detachedThreadUb (thread : ThreadId)
  | alreadyJoinedExclusiveUb (thread : ThreadId)
  | selfJoinUb (thread : ThreadId)
  | exclusiveJoinHasOtherWaiter (thread : ThreadId)
  | callbackUnblockedWithTimeout
  | callbackTokenMismatch (expected actual : Nat)
  | callbackTargetMismatch (expected actual : ThreadId)
  | callbackReasonMismatch (expected actual : BlockReason)
  | wrongHandler
  deriving Repr

inductive JoinCompletionError where
  | handlerMismatch
  | callbackUnblockedWithTimeout
  | globalStateRequired
  | globalState (error : GlobalStateError)
  deriving Repr

/-- `join_thread`'s `after_join` work, in source order. The selected handler
must run before the interpreter writes the scalar to the destination. -/
structure JoinCompletionObligation where
  joiner : ThreadId
  joinee : ThreadId
  callbackToken : Nat
  returnValue : JoinReturn
  handler : JoinHandler
  deriving Repr

inductive JoinPlan where
  | completedImmediately (manager : ThreadManager)
      (completion : JoinCompletionObligation)
  | waiting (manager : ThreadManager) (callback : JoinCompletionObligation)
  deriving Repr

namespace JoinPlan

def manager : JoinPlan → ThreadManager
  | .completedImmediately manager _ => manager
  | .waiting manager _ => manager

end JoinPlan

namespace ThreadManager

private def getThread (manager : ThreadManager) (thread : ThreadId) :
    Except JoinError ThreadRecord :=
  match manager.thread? thread with
  | some record => .ok record
  | none => .error (.thread .invalidId)

private def setThreadRecord (manager : ThreadManager) (thread : ThreadId)
    (record : ThreadRecord) : Except JoinError ThreadManager :=
  if thread.toNat < manager.threads.length then
    .ok { manager with threads := manager.threads.set thread.toNat record }
  else .error (.thread .invalidId)

/-- Prepare the ordinary Miri join. The active thread is the joiner. The
caller supplies the callback token allocated by its interpreter layer. -/
def prepareJoin (manager : ThreadManager) (joinee : ThreadId)
    (returnValue : JoinReturn) (handler : JoinHandler) (callbackToken : Nat) :
    Except JoinError JoinPlan := do
  let joiner := manager.activeThread
  let target ← getThread manager joinee
  if target.joinStatus == .Detached then
    throw (.detachedThreadUb joinee)
  let marked ← setThreadRecord manager joinee { target with joinStatus := .Joined }
  let completion : JoinCompletionObligation :=
    { joiner := joiner, joinee := joinee, callbackToken := callbackToken,
      returnValue := returnValue,
      handler := handler }
  if target.isTerminated then
    return .completedImmediately marked completion
  let blocked ← match marked.blockThread (.Join joinee) none callbackToken with
    | .ok manager => .ok manager
    | .error error => .error (.thread error)
  return .waiting blocked completion

/-- Miri's exclusive join checks the existing Joined status, self-join, and
absence of other waiters before taking the ordinary path. -/
def prepareJoinExclusive (manager : ThreadManager) (joinee : ThreadId)
    (returnValue : JoinReturn) (handler : JoinHandler) (callbackToken : Nat) :
    Except JoinError JoinPlan := do
  let target ← getThread manager joinee
  if target.joinStatus == .Joined then
    throw (.alreadyJoinedExclusiveUb joinee)
  if joinee == manager.activeThread then
    throw (.selfJoinUb joinee)
  let hasWaiter := manager.threads.any fun thread =>
    thread.isBlockedOn (.Join joinee)
  if hasWaiter then throw (.exclusiveJoinHasOtherWaiter joinee)
  prepareJoin manager joinee returnValue handler callbackToken

/-- Apply the join completion callback after an actual Ready unblock. The
callback does not claim synchronization or write success; it produces a
continuation requiring those effects in the exact source order. -/
def afterJoinUnblock (callback : JoinCompletionObligation)
    (unblock : UnblockCallbackObligation) : Except JoinError JoinCompletionObligation := do
  if unblock.target != callback.joiner then
    throw (.callbackTargetMismatch callback.joiner unblock.target)
  if unblock.callbackToken != callback.callbackToken then
    throw (.callbackTokenMismatch callback.callbackToken unblock.callbackToken)
  if unblock.reason != .Join callback.joinee then
    throw (.callbackReasonMismatch (.Join callback.joinee) unblock.reason)
  if unblock.kind != .Ready then
    throw .callbackUnblockedWithTimeout
  pure callback

end ThreadManager

def completeVectorClockJoin (state : GlobalState) (threads : ThreadManager)
    (completion : JoinCompletionObligation) :
    Except JoinCompletionError (GlobalState × JoinReturn) := do
  if completion.handler != .vectorClocks then
    .error .handlerMismatch
  let synchronized ← (GlobalState.threadJoined state threads completion.joinee).mapError
    JoinCompletionError.globalState
  pure (synchronized, completion.returnValue)

end Miri.Concurrency
