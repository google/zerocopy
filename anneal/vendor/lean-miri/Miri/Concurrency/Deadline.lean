import Miri.Concurrency.Thread

/-!
# Deadline sweep and timeout callback protocol

This follows `ThreadManager::unblock_expired_deadlines` in `thread.rs`.
Host-clock reads are supplied as exact per-thread remaining durations; this
module does not invent a clock or unit. It performs the source's full sweep
before invoking timeout callbacks, keeps the minimum positive wait, and then
exposes callback execution in thread-index order. A callback failure retains
the mutated manager and stops the remaining callbacks, matching `?` before
active-thread restoration.
-/

namespace Miri.Concurrency

/-- Exact result of Miri's host clock subtraction for one blocked thread. A
zero duration means the deadline has expired. -/
structure DeadlineObservation where
  thread : ThreadId
  remaining : Nat
  deriving Repr

inductive DeadlineSweepError where
  | realTimeTimeoutInIsolation (thread : ThreadId)
  | missingObservation (thread : ThreadId)
  | duplicateObservations (thread : ThreadId)
  | threadIdOverflow (index : Nat)
  deriving Repr

private inductive ObservationLookup where
  | missing
  | unique (remaining : Nat)
  | duplicate

structure DeadlineCallback where
  thread : ThreadId
  reason : BlockReason
  callbackToken : Nat
  deriving Repr

/-- The source mutates expired thread states during the sweep, before it
starts calling any callbacks. `outcome` retains a source assertion or missing
environment fact together with those prior mutations. -/
structure DeadlineSweep where
  manager : ThreadManager
  callbacks : List DeadlineCallback
  minimumWait : Option Nat
  outcome : Option DeadlineSweepError
  deriving Repr

namespace DeadlineSweep

def initial (manager : ThreadManager) : DeadlineSweep :=
  { manager := manager, callbacks := [], minimumWait := none, outcome := none }

private def findObservation (observations : List DeadlineObservation)
    (thread : ThreadId) : ObservationLookup :=
  match (observations.filter fun observation => observation.thread == thread).map
      DeadlineObservation.remaining with
  | [] => .missing
  | [remaining] => .unique remaining
  | _ => .duplicate

private def replaceThread (manager : ThreadManager) (index : Nat)
    (record : ThreadRecord) : Option ThreadManager :=
  if index < manager.threads.length then
    some { manager with threads := manager.threads.set index record }
  else none

private def visit (state : DeadlineSweep) (observations : List DeadlineObservation)
    (communicate : Bool) (record : ThreadRecord × Nat) : DeadlineSweep := Id.run do
  if state.outcome.isSome then return state
  let (thread, rawIndex) := record
  match thread.state with
  | .Blocked reason (some deadline) callbackToken =>
    match ThreadId.ofNat rawIndex with
    | .error _ =>
      return { state with outcome := some (.threadIdOverflow rawIndex) }
    | .ok id =>
      if (match deadline with | .RealTime _ => true | .Monotonic _ => false)
          && !communicate then
        return { state with outcome := some (.realTimeTimeoutInIsolation id) }
      match findObservation observations id with
      | .missing => return { state with outcome := some (.missingObservation id) }
      | .duplicate => return { state with outcome := some (.duplicateObservations id) }
      | .unique 0 =>
        match replaceThread state.manager rawIndex { thread with state := .Enabled } with
        | none => return { state with outcome := some (.threadIdOverflow rawIndex) }
        | some manager =>
          return { state with
            manager := manager
            callbacks := state.callbacks ++ [{
              thread := id
              reason := reason
              callbackToken := callbackToken }] }
      | .unique remaining =>
        let minimumWait := match state.minimumWait with
          | none => some remaining
          | some old => some (min old remaining)
        return { state with minimumWait }
  | _ => return state

/-- Run the source's thread-index-ordered sweep. The observation list must
contain the actual clock subtraction for each blocked deadline. -/
def sweep (manager : ThreadManager) (observations : List DeadlineObservation)
    (communicate : Bool) : DeadlineSweep :=
  manager.threads.zipIdx.foldl
    (fun state indexed => visit state observations communicate indexed)
    (initial manager)

end DeadlineSweep

inductive DeadlineCallbackError where
  | sweepFailed (error : DeadlineSweepError)
  | thread (error : ThreadError)
  | wrongCallbackKind (expected actual : UnblockKind)
  deriving Repr

inductive DeadlineCallbackStep where
  | complete (manager : ThreadManager) (minimumWait : Option Nat)
  | invoke (manager : ThreadManager) (obligation : UnblockCallbackObligation)
      (remaining : List DeadlineCallback) (minimumWait : Option Nat)
  | callbackFailed (managerAfterFailure : ThreadManager)
      (obligation : UnblockCallbackObligation) (remaining : List DeadlineCallback)
      (minimumWait : Option Nat)
  deriving Repr

namespace ThreadManager

private def beginDeadlineCallback (manager : ThreadManager)
    (callbacks : List DeadlineCallback) (minimumWait : Option Nat) :
    Except ThreadError DeadlineCallbackStep := do
  match callbacks with
  | [] => pure (.complete manager minimumWait)
  | callback :: remaining =>
    let (active, previous) ← setActiveThread manager callback.thread
    let obligation : UnblockCallbackObligation := {
      target := callback.thread
      previousActive := previous
      reason := callback.reason
      callbackToken := callback.callbackToken
      kind := .TimedOut }
    pure (.invoke active obligation remaining minimumWait)

/-- Start callbacks only after a successful complete sweep. Every expired
thread has already been set to Enabled. -/
def beginDeadlineCallbacks (sweep : DeadlineSweep) :
    Except DeadlineCallbackError DeadlineCallbackStep := do
  match sweep.outcome with
  | some error => .error (.sweepFailed error)
  | none => (beginDeadlineCallback sweep.manager sweep.callbacks sweep.minimumWait)
      |>.mapError DeadlineCallbackError.thread

/-- Continue after one actual callback. A failed callback leaves its active
thread selected and prevents later callbacks from running. -/
def continueDeadlineCallbacks (managerAfterCallback : ThreadManager)
    (obligation : UnblockCallbackObligation) (remaining : List DeadlineCallback)
    (minimumWait : Option Nat) (returnedNormally : Bool) :
    Except DeadlineCallbackError DeadlineCallbackStep := do
  if obligation.kind != .TimedOut then
    throw (.wrongCallbackKind .TimedOut obligation.kind)
  if !returnedNormally then
    pure (.callbackFailed managerAfterCallback obligation remaining minimumWait)
  else
    let restored := restoreAfterCallback managerAfterCallback obligation
    (beginDeadlineCallback restored remaining minimumWait).mapError
      DeadlineCallbackError.thread

end ThreadManager

end Miri.Concurrency
