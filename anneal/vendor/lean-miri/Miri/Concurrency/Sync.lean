import Miri.Concurrency.SyncClock
import Miri.Concurrency.Deadline

/-!
# Internal synchronization state from pinned Miri

This file starts a source-shaped port of `upstream/miri-source/src/concurrency/sync.rs`
(blob `3e848a071e2a67792eada4625b1751eec119b21d`). It preserves the state fields
of Mutex, RwLock, Condvar, Semaphore, and Futex. The lock transitions below
preserve Miri's mutation order and use the existing `GlobalState` clock hooks
and `ThreadManager` blocking/wakeup state.

Unblock callbacks are returned as explicit obligations. A transition carrying
one has not completed the source operation yet. OS object lookup, shim-side
memory checks, interpreter callback execution, futex/semaphore callback bodies,
and actual memory writes remain outside this component; none is interpreted as
success here. This is not a complete Rust concurrency semantics.
-/

namespace Miri.Concurrency

inductive SyncClockHandler where
  | none
  | vectorClocks
  deriving DecidableEq, Repr

/-- The actual defaulted state held by Miri's `Mutex`. -/
structure MutexState where
  owner : Option ThreadId := none
  lockCount : Nat := 0
  queue : List ThreadId := []
  clock : VClock := .default
  deriving Repr

/-- The actual defaulted state held by Miri's `RwLock`. Reader counts use a
finite association list as a representation of the source `FxHashMap`; all
operations preserve unique thread keys and positive counts. -/
structure RwLockState where
  writer : Option ThreadId := none
  readers : List (ThreadId × Nat) := []
  writerQueue : List ThreadId := []
  readerQueue : List ThreadId := []
  clockUnlocked : VClock := .default
  clockCurrentReaders : VClock := .default
  deriving Repr

structure CondvarState where
  waiters : List ThreadId := []
  clock : VClock := .default
  deriving Repr

structure SemaphoreState where
  waiters : List ThreadId := []
  value : UInt64 := 0
  clock : VClock := .default
  deriving Repr

structure FutexWaiter where
  thread : ThreadId
  bitset : UInt32
  deriving Repr

structure FutexState where
  waiters : List FutexWaiter := []
  clock : VClock := .default
  deriving Repr

/-- Built-in callback bodies created by the generic sync layer. Pointer and
scalar destinations are opaque interpreter tokens; this file never writes
through them. -/
inductive SyncCallbackProgram where
  | mutexAcquire
  | rwlockReaderAcquire (returnValueToken destinationToken : Nat)
  | rwlockWriterAcquire (returnValueToken destinationToken : Nat)
  | mutexAcquireAndWrite (returnValueToken destinationToken : Nat)
  | writeScalar (valueToken destinationToken : Nat)
  | condvarWait (mutexToken successValueToken timeoutValueToken destinationToken : Nat)
  | futexWait (userCallbackToken : Nat)
  | semaphoreWait (userCallbackToken : Nat)
  | opaqueInterpreterCallback (callbackToken : Nat)
  deriving DecidableEq, Repr

inductive SyncError where
  | globalState (error : GlobalStateError)
  | missingGlobalClock
  | threadManager (error : ThreadError)
  | mutexSourceAssertion (message : String)
  | mutexLockCountOverflow (bits : Nat)
  | mutexLockCountUnderflow
  | rwlockSourceAssertion (message : String)
  | rwlockReaderMapInvariant
  | rwlockReaderCountOverflow (bits : Nat)
  | callbackProgramMismatch (expected actual : SyncCallbackProgram)
  | callbackUnblockedWithTimeout
  | callbackReasonMismatch (expected actual : BlockReason)
  | callbackKindMismatch (expected actual : UnblockKind)
  | callbackTargetMismatch (expected actual : ThreadId)
  | callbackReturnedError
  | blockThreadSource (error : BlockThreadSourceError)
  | condvarWaitMutexNotLocked
  | condvarWaitRecursiveMutex (lockCount : Nat)
  | condvarMutexOwnedByActiveThread (thread : ThreadId)
  | futexThreadAlreadyWaiting (thread : ThreadId)
  | semaphoreCounterOverflow
  deriving Repr

def SyncError.ofClock : SyncClockError → SyncError
  | .missingGlobal => .missingGlobalClock
  | .global error => .globalState error

private def releaseUpdating [SyncClockState G] (global : G) (threads : ThreadManager)
    (state : S) (update : VClock → S → S) : S × Except SyncError G :=
  match SyncClockState.prepareRelease global threads with
  | .error error => (state,.error (SyncError.ofClock error))
  | .ok (snapshot,finish) => (update snapshot state,finish.mapError SyncError.ofClock)

structure SyncCallbackRequest where
  unblock : UnblockCallbackObligation
  program : SyncCallbackProgram
  remainingWakeups : List ThreadId := []
  deriving Repr

/-- A callback request is a live, unresolved action in the source operation.
`outcome` records the component's return value only as a continuation value;
callers must run the request and use the corresponding completion function
before treating the enclosing operation as returned. -/
structure SyncTransition (State Value : Type) (G : Type := GlobalState) where
  syncState : State
  global : G
  threads : ThreadManager
  outcome : Except SyncError Value
  callback : Option SyncCallbackRequest := none
  callbackRegistration : Option (Nat × SyncCallbackProgram) := none
  deriving Repr

inductive MutexUnlockResult where
  | returnedNone
  | returnedSome (oldLockCount : Nat)
  deriving DecidableEq, Repr

namespace SyncTransition

def outcomeIsOk (transition : SyncTransition State Value G) : Prop :=
  match transition.outcome with
  | .ok _ => True
  | .error _ => False

def hasPendingWork (transition : SyncTransition State Value G) : Bool :=
  transition.callback.isSome || transition.callbackRegistration.isSome

end SyncTransition

variable {G : Type} [SyncClockState G]

private def maxHostUsize (bits : Nat) : Nat := 2 ^ bits - 1

private def getReaderCount (readers : List (ThreadId × Nat)) (thread : ThreadId) :
    List Nat :=
  (readers.filter fun entry => entry.1 == thread).map Prod.snd

private def replaceReaderCount (readers : List (ThreadId × Nat)) (thread : ThreadId)
    (newCount : Option Nat) : List (ThreadId × Nat) :=
  let withoutThread := readers.filter fun entry => entry.1 != thread
  match newCount with
  | none => withoutThread
  | some count => withoutThread ++ [(thread, count)]

private def callbackProgramFor (registry : List (Nat × SyncCallbackProgram))
    (token : Nat) : SyncCallbackProgram :=
  match registry.filter (fun entry => entry.1 == token) with
  | [(_, program)] => program
  | _ => .opaqueInterpreterCallback token

private def beginRwLockWake (state : RwLockState) (global : G)
    (threads : ThreadManager) (registry : List (Nat × SyncCallbackProgram))
    (waiters : List ThreadId) : SyncTransition RwLockState Unit G := Id.run do
  match waiters with
  | [] => return ⟨state, global, threads, .ok (), none, none⟩
  | waiter :: rest =>
    match threads.unblockThread waiter .RwLock with
    | .error error =>
      return ⟨state, global, threads, .error (.threadManager error), none, none⟩
    | .ok (unblocked, obligation) =>
      let program := callbackProgramFor registry obligation.callbackToken
      return ⟨state, global, unblocked, .ok (),
        some { unblock := obligation, program := program, remainingWakeups := rest }, none⟩

/-- Mutation/check queuedResult before constructing a source blocking callback. -/
structure SyncQueuePrefix (S : Type) where
  state : S
  outcome : Except SyncError Unit

def MutexState.queueForBlock (state : MutexState) (threads : ThreadManager) : SyncQueuePrefix MutexState :=
  let queued := {state with queue := state.queue ++ [threads.activeThread]}
  ⟨queued,if state.owner.isNone then .error (.mutexSourceAssertion "queuing on unlocked mutex") else .ok ()⟩
def RwLockState.queueReaderForBlock (state : RwLockState) (threads : ThreadManager) : SyncQueuePrefix RwLockState :=
  let queued := {state with readerQueue := state.readerQueue ++ [threads.activeThread]}
  ⟨queued,if state.writer.isNone then .error (.rwlockSourceAssertion "read-queueing on not write locked rwlock") else .ok ()⟩
def RwLockState.queueWriterForBlock (state : RwLockState) (threads : ThreadManager) : SyncQueuePrefix RwLockState :=
  let queued := {state with writerQueue := state.writerQueue ++ [threads.activeThread]}
  let locked := state.writer.isSome || !state.readers.isEmpty
  ⟨queued,if !locked then .error (.rwlockSourceAssertion "write-queueing on unlocked rwlock") else .ok ()⟩
def CondvarState.queueForBlock (state : CondvarState) (threads : ThreadManager)
    (unlocked : MutexUnlockResult) : SyncQueuePrefix CondvarState :=
  match unlocked with
  | .returnedNone => ⟨state,.error .condvarWaitMutexNotLocked⟩
  | .returnedSome count =>
    if count != 1 then ⟨state,.error (.condvarWaitRecursiveMutex count)⟩
    else ⟨{state with waiters := state.waiters ++ [threads.activeThread]},.ok ()⟩
def FutexState.queueForBlock (state : FutexState) (threads : ThreadManager) (bitset : UInt32) : SyncQueuePrefix FutexState :=
  if state.waiters.any (fun w => w.thread == threads.activeThread) then
    ⟨state,.error (.futexThreadAlreadyWaiting threads.activeThread)⟩
  else ⟨{state with waiters := state.waiters ++ [⟨threads.activeThread,bitset⟩]},.ok ()⟩
def SemaphoreState.queueForBlock (state : SemaphoreState) (threads : ThreadManager) : SyncQueuePrefix SemaphoreState :=
  ⟨{state with waiters := state.waiters ++ [threads.activeThread]},.ok ()⟩

namespace MutexState

def queueIsEmpty (state : MutexState) : Bool := state.queue.isEmpty

/-- Exact source operation `mutex_lock`: owner/count mutations precede
`acquire_clock`, and therefore remain visible if that hook reports an error. -/
def lock (state : MutexState) (global : G) (threads : ThreadManager)
    (handler : SyncClockHandler) (usizeBits : Nat := 64) :
    SyncTransition MutexState Unit G := Id.run do
  let thread := threads.activeThread
  let afterOwner := match state.owner with
    | none => some { state with owner := some thread }
    | some owner =>
      if owner != thread then none else some state
  let some afterOwner := afterOwner
    | return ⟨state, global, threads,
        .error (.mutexSourceAssertion "mutex already locked by another thread"), none, none⟩
  if state.owner.isSome && state.lockCount == 0 then
    return ⟨state, global, threads,
      .error (.mutexSourceAssertion "lock_count == 0 while mutex is owned"), none, none⟩
  if afterOwner.lockCount >= maxHostUsize usizeBits then
    return ⟨afterOwner, global, threads, .error (.mutexLockCountOverflow usizeBits), none, none⟩
  let locked := { afterOwner with lockCount := afterOwner.lockCount + 1 }
  match handler with
  | .none => return ⟨locked, global, threads, .ok (), none, none⟩
  | .vectorClocks =>
    match SyncClockState.acquire global threads state.clock with
    | .error error => return ⟨locked, global, threads, .error (SyncError.ofClock error), none, none⟩
    | .ok acquired => return ⟨locked, acquired, threads, .ok (), none, none⟩

/-- Exact source operation `mutex_enqueue_and_block` through
`block_thread`. Queue insertion precedes the source assertion and blocking;
the callback registration names the closure body installed by Miri. -/
def enqueueAndBlock (state : MutexState) (global : G)
    (threads : ThreadManager) (callbackToken : Nat) :
    SyncTransition MutexState Unit G := Id.run do
  let queuedResult := state.queueForBlock threads
  let queued := queuedResult.state
  match queuedResult.outcome with
  | .error error => return ⟨queued,global,threads,.error error,none,none⟩
  | .ok () => pure ()
  match threads.blockThread .Mutex none callbackToken with
  | .error error =>
    return ⟨queued, global, threads, .error (.threadManager error), none, none⟩
  | .ok blocked =>
    return ⟨queued, global, blocked, .ok (), none,
      some (callbackToken, .mutexAcquire)⟩

/-- Exact source operation `mutex_unlock`. A woken thread is enabled and made
active by `unblockThread`; the callback must then be completed with
`finishMutexAcquireCallback` before the source operation has returned. -/
def unlock (state : MutexState) (global : G) (threads : ThreadManager)
    (handler : SyncClockHandler)
    (callbackRegistry : List (Nat × SyncCallbackProgram) := []) :
    SyncTransition MutexState MutexUnlockResult G := Id.run do
  let some owner := state.owner
    | return ⟨state, global, threads, .ok .returnedNone, none, none⟩
  if owner != threads.activeThread then
    return ⟨state, global, threads, .ok .returnedNone, none, none⟩
  if state.lockCount == 0 then
    return ⟨state, global, threads, .error .mutexLockCountUnderflow, none, none⟩
  let oldLockCount := state.lockCount
  let decremented := { state with lockCount := oldLockCount - 1 }
  if decremented.lockCount != 0 then
    return ⟨decremented, global, threads, .ok (.returnedSome oldLockCount), none, none⟩
  let released := { decremented with owner := none }
  let (releasedGlobal, releasedMutex) ← match handler with
    | .none => pure (global, released)
    | .vectorClocks =>
      let (releasedState,finish) := releaseUpdating global threads released
        (fun snapshot s => {s with clock := snapshot})
      match finish with
      | .error error => return ⟨releasedState, global, threads, .error error, none, none⟩
      | .ok nextGlobal => pure (nextGlobal,releasedState)
  match releasedMutex.queue with
  | [] => return ⟨releasedMutex, releasedGlobal, threads,
      .ok (.returnedSome oldLockCount), none, none⟩
  | waiter :: rest =>
    let dequeued := { releasedMutex with queue := rest }
    match threads.unblockThread waiter .Mutex with
    | .error error =>
      return ⟨dequeued, releasedGlobal, threads,
        .error (.threadManager error), none, none⟩
    | .ok (unblocked, obligation) =>
      let program := callbackProgramFor callbackRegistry obligation.callbackToken
      return ⟨dequeued, releasedGlobal, unblocked,
        .ok (.returnedSome oldLockCount),
        some { unblock := obligation, program := program }, none⟩

end MutexState

/-- Execute the known internal callback installed by
`mutex_enqueue_and_block`: it requires a Ready unblock, asserts that ownership
was transferred to an unlocked mutex, acquires the lock/clock, and restores
the previously active thread only after normal callback return. -/
def finishMutexAcquireCallback (state : MutexState) (global : G)
    (threadsAfterUnblock : ThreadManager) (request : SyncCallbackRequest)
    (handler : SyncClockHandler) (unlockResult : MutexUnlockResult)
    (usizeBits : Nat := 64) : SyncTransition MutexState MutexUnlockResult G := Id.run do
  if request.program != .mutexAcquire then
    return ⟨state, global, threadsAfterUnblock,
      .error (.callbackProgramMismatch .mutexAcquire request.program), none, none⟩
  if request.unblock.kind != .Ready then
    return ⟨state, global, threadsAfterUnblock,
      .error .callbackUnblockedWithTimeout, none, none⟩
  if state.owner.isSome then
    return ⟨state, global, threadsAfterUnblock,
      .error (.mutexSourceAssertion "mutex callback woke while mutex still owned"), none, none⟩
  let acquired := state.lock global threadsAfterUnblock handler usizeBits
  match acquired.outcome with
  | .error error =>
    return ⟨acquired.syncState, acquired.global, threadsAfterUnblock,
      .error error, acquired.callback, acquired.callbackRegistration⟩
  | .ok _ =>
    let restored := ThreadManager.restoreAfterCallback threadsAfterUnblock request.unblock
    return ⟨acquired.syncState, acquired.global, restored,
      .ok unlockResult, none, none⟩

/-- Continuation used by `condvar_reacquire_mutex` when the mutex is still
owned. It runs Miri's installed callback through lock/clock acquisition, then
leaves the captured scalar store as an explicit interpreter obligation. -/
def finishMutexAcquireAndWriteCallback (state : MutexState) (global : G)
    (threadsAfterUnblock : ThreadManager) (request : SyncCallbackRequest)
    (handler : SyncClockHandler) : SyncTransition MutexState Unit G := Id.run do
  let .mutexAcquireAndWrite valueToken destinationToken := request.program
    | return ⟨state, global, threadsAfterUnblock,
      .error (.callbackProgramMismatch (.mutexAcquireAndWrite 0 0) request.program), none, none⟩
  if request.unblock.kind != .Ready then
    return ⟨state, global, threadsAfterUnblock,
      .error .callbackUnblockedWithTimeout, none, none⟩
  if state.owner.isSome then
    return ⟨state, global, threadsAfterUnblock,
      .error (.mutexSourceAssertion "mutex callback woke while mutex still owned"), none, none⟩
  let acquired := state.lock global threadsAfterUnblock handler
  match acquired.outcome with
  | .error error =>
    return ⟨acquired.syncState, acquired.global, threadsAfterUnblock,
      .error error, acquired.callback, acquired.callbackRegistration⟩
  | .ok _ =>
    let writeCallback : SyncCallbackRequest := {
      unblock := request.unblock
      program := .writeScalar valueToken destinationToken }
    return ⟨acquired.syncState, acquired.global, threadsAfterUnblock,
      .ok (), some writeCallback, none⟩

namespace RwLockState

def isWriteLocked (state : RwLockState) : Bool := state.writer.isSome

def isLocked (state : RwLockState) : Bool :=
  state.writer.isSome || !state.readers.isEmpty

def queueIsEmpty (state : RwLockState) : Bool :=
  state.writerQueue.isEmpty && state.readerQueue.isEmpty

/-- Exact `rwlock_reader_lock` state update and following clock acquire. -/
def readerLock (state : RwLockState) (global : G)
    (threads : ThreadManager) (handler : SyncClockHandler)
    (usizeBits : Nat := 64) : SyncTransition RwLockState Unit G := Id.run do
  if state.writer.isSome then
    return ⟨state, global, threads,
      .error (.rwlockSourceAssertion "the lock is write locked"), none, none⟩
  let thread := threads.activeThread
  let counts := getReaderCount state.readers thread
  if counts.length > 1 then
    return ⟨state, global, threads, .error .rwlockReaderMapInvariant, none, none⟩
  let current := counts.headD 0
  if current >= maxHostUsize usizeBits then
    let inserted := if counts.isEmpty then
      { state with readers := state.readers ++ [(thread, 0)] } else state
    return ⟨inserted, global, threads, .error (.rwlockReaderCountOverflow usizeBits), none, none⟩
  let locked := { state with readers :=
      (replaceReaderCount state.readers thread (some (current + 1))) }
  match handler with
  | .none => return ⟨locked, global, threads, .ok (), none, none⟩
  | .vectorClocks =>
    match SyncClockState.acquire global threads state.clockUnlocked with
    | .error error => return ⟨locked, global, threads, .error (SyncError.ofClock error), none, none⟩
    | .ok acquired => return ⟨locked, acquired, threads, .ok (), none, none⟩

/-- Exact `rwlock_writer_lock` state update and following clock acquire. -/
def writerLock (state : RwLockState) (global : G)
    (threads : ThreadManager) (handler : SyncClockHandler) :
    SyncTransition RwLockState Unit G := Id.run do
  if state.isLocked then
    return ⟨state, global, threads,
      .error (.rwlockSourceAssertion "the rwlock is already locked"), none, none⟩
  let locked := { state with writer := some threads.activeThread }
  match handler with
  | .none => return ⟨locked, global, threads, .ok (), none, none⟩
  | .vectorClocks =>
    match SyncClockState.acquire global threads state.clockUnlocked with
    | .error error => return ⟨locked, global, threads, .error (SyncError.ofClock error), none, none⟩
    | .ok acquired => return ⟨locked, acquired, threads, .ok (), none, none⟩

/-- Queue a reader behind a writer, preserving the source's push-before-assert
and `block_thread` order. The closure's scalar write is an opaque token. -/
def enqueueReaderAndBlock (state : RwLockState) (global : G)
    (threads : ThreadManager) (callbackToken returnValueToken destinationToken : Nat) :
    SyncTransition RwLockState Unit G := Id.run do
  let queuedResult := state.queueReaderForBlock threads
  let queued := queuedResult.state
  match queuedResult.outcome with
  | .error error => return ⟨queued,global,threads,.error error,none,none⟩
  | .ok () => pure ()
  match threads.blockThread .RwLock none callbackToken with
  | .error error => return ⟨queued, global, threads, .error (.threadManager error), none, none⟩
  | .ok blocked => return ⟨queued, global, blocked, .ok (), none,
      some (callbackToken, .rwlockReaderAcquire returnValueToken destinationToken)⟩

/-- Queue a writer behind an existing reader or writer, using the source's
writer queue and callback registration. -/
def enqueueWriterAndBlock (state : RwLockState) (global : G)
    (threads : ThreadManager) (callbackToken returnValueToken destinationToken : Nat) :
    SyncTransition RwLockState Unit G := Id.run do
  let queuedResult := state.queueWriterForBlock threads
  let queued := queuedResult.state
  match queuedResult.outcome with
  | .error error => return ⟨queued,global,threads,.error error,none,none⟩
  | .ok () => pure ()
  match threads.blockThread .RwLock none callbackToken with
  | .error error => return ⟨queued, global, threads, .error (.threadManager error), none, none⟩
  | .ok blocked => return ⟨queued, global, blocked, .ok (), none,
      some (callbackToken, .rwlockWriterAcquire returnValueToken destinationToken)⟩

/-- Exact `rwlock_reader_unlock` ordering. It first removes/decrements the
reader entry, then releases and joins the active clock, then transfers the
joined-reader clock and wakes one queued writer if the lock becomes free. -/
def readerUnlock (state : RwLockState) (global : G)
    (threads : ThreadManager) (handler : SyncClockHandler)
    (callbackRegistry : List (Nat × SyncCallbackProgram) := []) :
    SyncTransition RwLockState Bool G := Id.run do
  let thread := threads.activeThread
  let counts := getReaderCount state.readers thread
  if counts.length > 1 then
    return ⟨state, global, threads, .error .rwlockReaderMapInvariant, none, none⟩
  let some count := counts.head?
    | return ⟨state, global, threads, .ok false, none, none⟩
  if count == 0 then
    return ⟨state, global, threads,
      .error (.rwlockSourceAssertion "rwlock locked with count == 0"), none, none⟩
  let readers := replaceReaderCount state.readers thread
    (if count == 1 then none else some (count - 1))
  let decremented := { state with readers := readers }
  let (releasedGlobal, releasedReaders) ← match handler with
    | .none => pure (global, decremented)
    | .vectorClocks =>
      let (releasedState,finish) := releaseUpdating global threads decremented
        (fun snapshot s => {s with clockCurrentReaders := s.clockCurrentReaders.join snapshot})
      match finish with
      | .error error => return ⟨releasedState, global, threads, .error error, none, none⟩
      | .ok nextGlobal => pure (nextGlobal,releasedState)
  if releasedReaders.isLocked then
    return ⟨releasedReaders, releasedGlobal, threads, .ok true, none, none⟩
  let noReaders := { releasedReaders with
    clockUnlocked := releasedReaders.clockCurrentReaders }
  match noReaders.writerQueue with
  | [] => return ⟨noReaders, releasedGlobal, threads, .ok true, none, none⟩
  | writer :: rest =>
    let dequeued := { noReaders with writerQueue := rest }
    let wake := beginRwLockWake dequeued releasedGlobal threads callbackRegistry [writer]
    return { wake with outcome := wake.outcome.map (fun _ => true) }

/-- Exact `rwlock_writer_unlock`: the writer clears ownership before the clock
release; queued writers have priority, otherwise all waiting readers are
removed from the queue before their callbacks are invoked in FIFO order. -/
def writerUnlock (state : RwLockState) (global : G)
    (threads : ThreadManager) (handler : SyncClockHandler)
    (callbackRegistry : List (Nat × SyncCallbackProgram) := []) :
    SyncTransition RwLockState Bool G := Id.run do
  let some writer := state.writer
    | return ⟨state, global, threads, .ok false, none, none⟩
  if writer != threads.activeThread then
    return ⟨state, global, threads, .ok false, none, none⟩
  let unlocked := { state with writer := none }
  let (releasedGlobal, releasedLock) ← match handler with
    | .none => pure (global, unlocked)
    | .vectorClocks =>
      let (releasedState,finish) := releaseUpdating global threads unlocked
        (fun snapshot s => {s with clockUnlocked := snapshot})
      match finish with
      | .error error => return ⟨releasedState, global, threads, .error error, none, none⟩
      | .ok nextGlobal => pure (nextGlobal,releasedState)
  match releasedLock.writerQueue with
  | nextWriter :: rest =>
    let dequeued := { releasedLock with writerQueue := rest }
    let wake := beginRwLockWake dequeued releasedGlobal threads callbackRegistry [nextWriter]
    return { wake with outcome := wake.outcome.map (fun _ => true) }
  | [] =>
    let readers := releasedLock.readerQueue
    let drained := { releasedLock with readerQueue := [] }
    match readers with
    | [] => return ⟨drained, releasedGlobal, threads, .ok true, none, none⟩
    | _ :: _ =>
      let wake := beginRwLockWake drained releasedGlobal threads callbackRegistry readers
      return { wake with outcome := wake.outcome.map (fun _ => true) }

/-- Continue a source loop that is waking the readers drained by
`rwlock_writer_unlock`. The caller must first execute the callback in the
previous request and provide its resulting manager. -/
def continueReaderWakeups (state : RwLockState) (global : G)
    (threadsAfterCallback : ThreadManager) (request : SyncCallbackRequest)
    (returnedNormally : Bool)
    (callbackRegistry : List (Nat × SyncCallbackProgram) := []) :
    SyncTransition RwLockState Bool G := Id.run do
  let previous := request.unblock
  if previous.reason != .RwLock then
    return ⟨state, global, threadsAfterCallback,
      .error (.callbackReasonMismatch .RwLock previous.reason), none, none⟩
  if previous.kind != .Ready then
    return ⟨state, global, threadsAfterCallback,
      .error (.callbackKindMismatch .Ready previous.kind), none, none⟩
  match request.program with
  | .rwlockReaderAcquire _ _ | .opaqueInterpreterCallback _ => pure ()
  | other =>
    return ⟨state, global, threadsAfterCallback,
      .error (.callbackProgramMismatch (.rwlockReaderAcquire 0 0) other), none, none⟩
  if !returnedNormally then
    return ⟨state, global, threadsAfterCallback,
      .error (.rwlockSourceAssertion "rwlock unblock callback returned an error"), none, none⟩
  let restored := ThreadManager.restoreAfterCallback threadsAfterCallback previous
  let wake := beginRwLockWake state global restored callbackRegistry request.remainingWakeups
  return { wake with outcome := wake.outcome.map (fun _ => true) }

end RwLockState

/-- Run the internal callback body installed while a reader/writer waited for
an RwLock: acquire the appropriate lock/clock, then expose the source's
`write_scalar` as a pending interpreter action. -/
def finishRwLockAcquireCallback (state : RwLockState) (global : G)
    (threadsAfterUnblock : ThreadManager) (request : SyncCallbackRequest)
    (handler : SyncClockHandler) : SyncTransition RwLockState Unit G := Id.run do
  let (valueToken, destinationToken, isReader) ← match request.program with
    | .rwlockReaderAcquire value destination => pure (value, destination, true)
    | .rwlockWriterAcquire value destination => pure (value, destination, false)
    | other =>
      return ⟨state, global, threadsAfterUnblock,
        .error (.callbackProgramMismatch (.rwlockReaderAcquire 0 0) other), none, none⟩
  if request.unblock.kind != .Ready then
    return ⟨state, global, threadsAfterUnblock,
      .error .callbackUnblockedWithTimeout, none, none⟩
  let locked := if isReader then
      state.readerLock global threadsAfterUnblock handler
    else state.writerLock global threadsAfterUnblock handler
  match locked.outcome with
  | .error error =>
    return ⟨locked.syncState, locked.global, threadsAfterUnblock,
      .error error, locked.callback, locked.callbackRegistration⟩
  | .ok _ =>
    let writeCallback : SyncCallbackRequest := {
      unblock := request.unblock
      program := .writeScalar valueToken destinationToken }
    return ⟨locked.syncState, locked.global, threadsAfterUnblock,
      .ok (), some writeCallback, none⟩

namespace CondvarState

def queueIsEmpty (state : CondvarState) : Bool := state.waiters.isEmpty

/-- Continue `condvar_wait` only after `mutex_unlock` returned successfully
with an original count of one. The call preserves the source order: waiter
queue insertion, then checked blocking with its timeout constraints. -/
def blockAfterMutexUnlock (state : CondvarState) (global : G)
    (threads : ThreadManager) (unlockResult : MutexUnlockResult)
    (deadline : Option ThreadDeadline) (callbackToken mutexToken : Nat)
    (successValueToken timeoutValueToken destinationToken : Nat)
    (communicate : Bool) : SyncTransition CondvarState Unit G := Id.run do
  let queuedResult := state.queueForBlock threads unlockResult
  let queued := queuedResult.state
  match queuedResult.outcome with
  | .error error => return ⟨queued,global,threads,.error error,none,none⟩
  | .ok () => pure ()
  match threads.blockThreadWithRuntimeConstraints .Condvar deadline callbackToken
      communicate with
  | .error error =>
    return ⟨queued, global, threads, .error (.blockThreadSource error), none, none⟩
  | .ok blocked =>
    return ⟨queued, global, blocked, .ok (), none,
      some (callbackToken, .condvarWait mutexToken successValueToken
        timeoutValueToken destinationToken)⟩

/-- Exact `condvar_signal`: release the signal clock before popping a waiter,
then unblock at most the FIFO head. The callback stays pending until the
interpreter executes the captured condvar/mutex continuation. -/
def signal (state : CondvarState) (global : G)
    (threads : ThreadManager) (handler : SyncClockHandler)
    (callbackRegistry : List (Nat × SyncCallbackProgram) := []) :
    SyncTransition CondvarState Bool G := Id.run do
  let (releasedGlobal, releasedState) ← match handler with
    | .none => pure (global, state)
    | .vectorClocks =>
      let (releasedState,finish) := releaseUpdating global threads state
        (fun snapshot s => {s with clock := snapshot})
      match finish with
      | .error error => return ⟨releasedState, global, threads, .error error, none, none⟩
      | .ok nextGlobal => pure (nextGlobal,releasedState)
  match releasedState.waiters with
  | [] => return ⟨releasedState, releasedGlobal, threads, .ok false, none, none⟩
  | waiter :: rest =>
    let dequeued := { releasedState with waiters := rest }
    match threads.unblockThread waiter .Condvar with
    | .error error =>
      return ⟨dequeued, releasedGlobal, threads,
        .error (.threadManager error), none, none⟩
    | .ok (unblocked, obligation) =>
      let program := callbackProgramFor callbackRegistry obligation.callbackToken
      return ⟨dequeued, releasedGlobal, unblocked, .ok true,
        some { unblock := obligation, program := program }, none⟩

/-- Execute the internal condvar callback through its source effects. On Ready
it acquires the signal clock; on timeout it first removes the waiter. It then
reacquires the captured mutex. If another thread owns it, this thread blocks
on that mutex with the source lock-and-write callback registered. If the
mutex is free, it acquires it and leaves the captured scalar write pending. -/
def finishWaitCallback (state : CondvarState) (mutex : MutexState)
    (global : G) (threadsAfterUnblock : ThreadManager)
    (request : SyncCallbackRequest) (handler : SyncClockHandler)
    (mutexToken newMutexCallbackToken : Nat) :
    SyncTransition (CondvarState × MutexState) Unit G := Id.run do
  let .condvarWait capturedMutexToken successValueToken timeoutValueToken destinationToken :=
      request.program
    | return ⟨(state, mutex), global, threadsAfterUnblock,
      .error (.callbackProgramMismatch (.condvarWait mutexToken 0 0 0) request.program), none, none⟩
  if capturedMutexToken != mutexToken then
    return ⟨(state, mutex), global, threadsAfterUnblock,
      .error (.callbackProgramMismatch (.condvarWait mutexToken successValueToken
        timeoutValueToken destinationToken) request.program), none, none⟩
  if request.unblock.reason != .Condvar then
    return ⟨(state, mutex), global, threadsAfterUnblock,
      .error (.callbackReasonMismatch .Condvar request.unblock.reason), none, none⟩
  if request.unblock.target != threadsAfterUnblock.activeThread then
    return ⟨(state, mutex), global, threadsAfterUnblock,
      .error (.callbackTargetMismatch request.unblock.target threadsAfterUnblock.activeThread), none, none⟩
  let (waited, afterClock) ← match request.unblock.kind with
    | .TimedOut =>
      pure (({ state with waiters := (state.waiters.filter
        (fun waiter => waiter != threadsAfterUnblock.activeThread)) }), global)
    | .Ready =>
      match handler with
      | .none => pure (state, global)
      | .vectorClocks =>
        match SyncClockState.acquire global threadsAfterUnblock state.clock with
        | .error error =>
          return ⟨(state, mutex), global, threadsAfterUnblock,
            .error (SyncError.ofClock error), none, none⟩
        | .ok acquired => pure (state, acquired)
  let returnValueToken := match request.unblock.kind with
    | .Ready => successValueToken
    | .TimedOut => timeoutValueToken
  match mutex.owner with
  | some owner =>
    if owner == threadsAfterUnblock.activeThread then
      return ⟨(waited, mutex), afterClock, threadsAfterUnblock,
        .error (.condvarMutexOwnedByActiveThread owner), none, none⟩
    let queued := { mutex with queue := mutex.queue ++ [threadsAfterUnblock.activeThread] }
    match threadsAfterUnblock.blockThread .Mutex none newMutexCallbackToken with
    | .error error =>
      return ⟨(waited, queued), afterClock, threadsAfterUnblock,
        .error (.threadManager error), none, none⟩
    | .ok blocked =>
      let restored := ThreadManager.restoreAfterCallback blocked request.unblock
      return ⟨(waited, queued), afterClock, restored, .ok (), none,
        some (newMutexCallbackToken,
          .mutexAcquireAndWrite returnValueToken destinationToken)⟩
  | none =>
    let acquired := mutex.lock afterClock threadsAfterUnblock handler
    match acquired.outcome with
    | .error error =>
      return ⟨(waited, acquired.syncState), acquired.global, threadsAfterUnblock,
        .error error, acquired.callback, acquired.callbackRegistration⟩
    | .ok _ =>
      let writeCallback : SyncCallbackRequest := {
        unblock := request.unblock
        program := .writeScalar returnValueToken destinationToken }
      return ⟨(waited, acquired.syncState), acquired.global,
        threadsAfterUnblock, .ok (), some writeCallback, none⟩

end CondvarState

namespace FutexState

def waiterCount (state : FutexState) : Nat := state.waiters.length

private def intersectsFuel : Nat → Nat → Nat → Bool
  | 0, _, _ => false
  | fuel + 1, left, right =>
    if left % 2 == 1 && right % 2 == 1 then true
    else intersectsFuel fuel (left / 2) (right / 2)

private def intersects (left right : UInt32) : Bool :=
  intersectsFuel 32 left.toNat right.toNat

/-- Match `Vec::extract_if(.., bitset_overlap).take(count)`: scan in queue
order, remove only matching waiters up to the requested count, and retain
nonmatching entries in their original order. -/
private def extractMatching (waiters : List FutexWaiter)
    (bitset : UInt32) (count : Nat) : List FutexWaiter × List FutexWaiter :=
  match waiters with
  | [] => ([], [])
  | waiter :: rest =>
    let (selected, kept) := extractMatching rest bitset
      (if count > 0 && intersects waiter.bitset bitset then count - 1 else count)
    if count > 0 && intersects waiter.bitset bitset then
      (waiter :: selected, kept)
    else
      (selected, waiter :: kept)
termination_by waiters.length

private def beginWake (state : FutexState) (global : G)
    (threads : ThreadManager) (callbackRegistry : List (Nat × SyncCallbackProgram))
    (selected : List FutexWaiter) : SyncTransition FutexState Nat G := Id.run do
  let total := selected.length
  match selected with
  | [] => return ⟨state, global, threads, .ok 0, none, none⟩
  | waiter :: rest =>
    match threads.unblockThread waiter.thread .Futex with
    | .error error => return ⟨state, global, threads,
        .error (.threadManager error), none, none⟩
    | .ok (unblocked, obligation) =>
      let program := callbackProgramFor callbackRegistry obligation.callbackToken
      return ⟨state, global, unblocked, .ok total,
        some { unblock := obligation, program := program, remainingWakeups := rest.map FutexWaiter.thread }, none⟩

/-- Exact source `futex_wait` registration: reject a duplicate waiter, append
the thread/bitset pair, then apply Miri's timeout checks and block it. Its
callback wrapper is retained as an explicit registration for the wake path. -/
def wait (state : FutexState) (global : G) (threads : ThreadManager)
    (bitset : UInt32) (deadline : Option ThreadDeadline)
    (callbackToken userCallbackToken : Nat) (communicate : Bool) :
    SyncTransition FutexState Unit G := Id.run do
  let queuedResult := state.queueForBlock threads bitset
  let queued := queuedResult.state
  match queuedResult.outcome with
  | .error error => return ⟨queued,global,threads,.error error,none,none⟩
  | .ok () => pure ()
  match threads.blockThreadWithRuntimeConstraints .Futex deadline callbackToken
      communicate with
  | .error error =>
    return ⟨queued, global, threads, .error (.blockThreadSource error), none, none⟩
  | .ok blocked =>
    return ⟨queued, global, blocked, .ok (), none,
      some (callbackToken, .futexWait userCallbackToken)⟩

/-- Exact `futex_wake`: release the clock before filtering and removing waiters;
the first unblock callback and every continuation are returned explicitly. -/
def wake (state : FutexState) (global : G) (threads : ThreadManager)
    (bitset : UInt32) (count : Nat) (handler : SyncClockHandler)
    (callbackRegistry : List (Nat × SyncCallbackProgram) := []) :
    SyncTransition FutexState Nat G := Id.run do
  let (releasedGlobal, releasedState) ← match handler with
    | .none => pure (global, state)
    | .vectorClocks =>
      let (releasedState,finish) := releaseUpdating global threads state
        (fun snapshot s => {s with clock := snapshot})
      match finish with
      | .error error => return ⟨releasedState, global, threads, .error error, none, none⟩
      | .ok nextGlobal => pure (nextGlobal,releasedState)
  let (selected, kept) := extractMatching releasedState.waiters bitset count
  let extracted := { releasedState with waiters := kept }
  beginWake extracted releasedGlobal threads callbackRegistry selected

/-- Miri's futex wrapper acquires the futex clock on Ready, removes the active
waiter on timeout, then invokes the OS-shim callback. That last callback is
opaque here and remains pending until the caller supplies its actual result. -/
def finishWaitCallback (state : FutexState) (global : G)
    (threadsAfterUnblock : ThreadManager) (request : SyncCallbackRequest)
    (handler : SyncClockHandler) : SyncTransition FutexState Unit G := Id.run do
  let .futexWait userCallbackToken := request.program
    | return ⟨state, global, threadsAfterUnblock,
      .error (.callbackProgramMismatch (.futexWait 0) request.program), none, none⟩
  let nextState := match request.unblock.kind with
    | .TimedOut =>
      { state with waiters := (state.waiters.filter
        (fun waiter => waiter.thread != threadsAfterUnblock.activeThread)) }
    | .Ready => state
  let nextGlobal := global
  match request.unblock.kind with
  | .TimedOut =>
    let nextCallback : SyncCallbackRequest := {
      unblock := request.unblock
      program := .opaqueInterpreterCallback userCallbackToken }
    return ⟨nextState, nextGlobal, threadsAfterUnblock, .ok (),
      some nextCallback, none⟩
  | .Ready =>
    match handler with
    | .none =>
      let nextCallback : SyncCallbackRequest := {
        unblock := request.unblock
        program := .opaqueInterpreterCallback userCallbackToken }
      return ⟨nextState, nextGlobal, threadsAfterUnblock, .ok (),
        some nextCallback, none⟩
    | .vectorClocks =>
      match SyncClockState.acquire global threadsAfterUnblock state.clock with
      | .error error => return ⟨nextState, nextGlobal, threadsAfterUnblock,
          .error (SyncError.ofClock error), none, none⟩
      | .ok acquired =>
        let nextCallback : SyncCallbackRequest := {
          unblock := request.unblock
          program := .opaqueInterpreterCallback userCallbackToken }
        return ⟨nextState, acquired, threadsAfterUnblock, .ok (),
          some nextCallback, none⟩

/-- Continue the `futex_wake` source loop only after the previous outer and
OS-shim callbacks returned normally. Callback failure stops the loop before
active-thread restoration, as Miri's `?` propagation does. -/
def continueWake (state : FutexState) (global : G)
    (threadsAfterCallback : ThreadManager) (request : SyncCallbackRequest)
    (wokenCount : Nat) (returnedNormally : Bool)
    (callbackRegistry : List (Nat × SyncCallbackProgram) := []) :
    SyncTransition FutexState Nat G := Id.run do
  let previous := request.unblock
  if previous.reason != .Futex then
    return ⟨state, global, threadsAfterCallback,
      .error (.callbackReasonMismatch .Futex previous.reason), none, none⟩
  if previous.kind != .Ready then
    return ⟨state, global, threadsAfterCallback,
      .error (.callbackKindMismatch .Ready previous.kind), none, none⟩
  match request.program with
  | .futexWait _ | .opaqueInterpreterCallback _ => pure ()
  | other =>
    return ⟨state, global, threadsAfterCallback,
      .error (.callbackProgramMismatch (.futexWait 0) other), none, none⟩
  if !returnedNormally then
    return ⟨state, global, threadsAfterCallback, .error .callbackReturnedError, none, none⟩
  let restored := ThreadManager.restoreAfterCallback threadsAfterCallback previous
  if request.remainingWakeups.isEmpty then
    return ⟨state, global, restored, .ok wokenCount, none, none⟩
  let next ← match request.remainingWakeups with
    | [] => pure ⟨state, global, restored, .ok wokenCount, none, none⟩
    | waiter :: rest =>
      match restored.unblockThread waiter .Futex with
      | .error error => pure ⟨state, global, restored,
          .error (.threadManager error), none, none⟩
      | .ok (unblocked, obligation) =>
        let program := callbackProgramFor callbackRegistry obligation.callbackToken
        pure ⟨state, global, unblocked, .ok wokenCount,
          some { unblock := obligation, program := program, remainingWakeups := rest }, none⟩
  return next

end FutexState

/-- Complete the actual interpreter `write_scalar` hook at the end of a
mutex/rwlock/condvar unblock callback. A failed write preserves the callback's
state and active-thread context, matching source `?` propagation. -/
def finishScalarWriteCallback {State : Type}
    (state : State) (global : G) (threadsAfterWrite : ThreadManager)
    (request : SyncCallbackRequest) (writeSucceeded : Bool) :
    SyncTransition State Unit G := Id.run do
  let .writeScalar _ _ := request.program
    | return ⟨state, global, threadsAfterWrite,
      .error (.callbackProgramMismatch (.writeScalar 0 0) request.program), none, none⟩
  if request.unblock.kind != .Ready then
    return ⟨state, global, threadsAfterWrite,
      .error .callbackUnblockedWithTimeout, none, none⟩
  if request.unblock.target != threadsAfterWrite.activeThread then
    return ⟨state, global, threadsAfterWrite,
      .error (.callbackTargetMismatch request.unblock.target threadsAfterWrite.activeThread), none, none⟩
  if !writeSucceeded then
    return ⟨state, global, threadsAfterWrite, .error .callbackReturnedError, none, none⟩
  let restored := ThreadManager.restoreAfterCallback threadsAfterWrite request.unblock
  return ⟨state, global, restored, .ok (), none, none⟩

/-- Complete a callback body whose implementation belongs to an OS shim or
the interpreter. The caller supplies the post-callback manager and the actual
return status; errors preserve its active-thread state, while normal return
restores the previous active thread exactly once. -/
def finishOpaqueSyncCallback {State : Type}
    (syncState : State) (global : G) (threadsAfterCallback : ThreadManager)
    (request : SyncCallbackRequest) (returnedNormally : Bool) :
    SyncTransition State Unit G := Id.run do
  match request.program with
  | .opaqueInterpreterCallback _ => pure ()
  | other =>
    return ⟨syncState, global, threadsAfterCallback,
      .error (.callbackProgramMismatch (.opaqueInterpreterCallback 0) other), none, none⟩
  if !returnedNormally then
    return ⟨syncState, global, threadsAfterCallback,
      .error .callbackReturnedError, none, none⟩
  let restored := ThreadManager.restoreAfterCallback threadsAfterCallback request.unblock
  return ⟨syncState, global, restored, .ok (), none, none⟩

namespace SemaphoreState

def queueIsEmpty (state : SemaphoreState) : Bool := state.waiters.isEmpty

/-- Exact source semaphore decrement through value update, clock acquire, and
callback registration. If the counter is zero, queue insertion precedes
checked blocking and the callback remains attached to the thread. -/
def decrement (state : SemaphoreState) (global : G)
    (threads : ThreadManager) (deadline : Option ThreadDeadline)
    (blockCallbackToken userCallbackToken : Nat) (handler : SyncClockHandler)
    (communicate : Bool) : SyncTransition SemaphoreState Unit G := Id.run do
  if state.value.toNat > 0 then
    let decremented := { state with value := UInt64.ofNat (state.value.toNat - 1) }
    let acquiredGlobal ← match handler with
      | .none => pure global
      | .vectorClocks =>
        match SyncClockState.acquire global threads state.clock with
        | .error error => return ⟨decremented, global, threads,
            .error (SyncError.ofClock error), none, none⟩
        | .ok acquired => pure acquired
    return ⟨decremented, acquiredGlobal, threads, .ok (), none,
      some (userCallbackToken, .opaqueInterpreterCallback userCallbackToken)⟩
  let queued := (state.queueForBlock threads).state
  match threads.blockThreadWithRuntimeConstraints .Semaphore deadline
      blockCallbackToken communicate with
  | .error error =>
    return ⟨queued, global, threads, .error (.blockThreadSource error), none, none⟩
  | .ok blocked =>
    return ⟨queued, global, blocked, .ok (), none,
      some (blockCallbackToken, .semaphoreWait userCallbackToken)⟩

def increment (state : SemaphoreState) (global : G)
    (threads : ThreadManager) (handler : SyncClockHandler)
    (callbackRegistry : List (Nat × SyncCallbackProgram) := []) :
    SyncTransition SemaphoreState Bool G := Id.run do
  let (waiter?, popped) :=
    if state.value.toNat == 0 then
      match state.waiters with
      | [] => (none, state)
      | waiter :: rest => (some waiter, { state with waiters := rest })
    else (none, state)
  if popped.value.toNat == 18446744073709551615 then
    return ⟨popped, global, threads, .error .semaphoreCounterOverflow, none, none⟩
  let incremented := { popped with value := UInt64.ofNat (popped.value.toNat + 1) }
  let (releasedGlobal, releasedState) ← match handler with
    | .none => pure (global, incremented)
    | .vectorClocks =>
      let (releasedState,finish) := releaseUpdating global threads incremented
        (fun snapshot s => {s with clock := snapshot})
      match finish with
      | .error error => return ⟨releasedState, global, threads, .error error, none, none⟩
      | .ok nextGlobal => pure (nextGlobal,releasedState)
  match waiter? with
  | none => return ⟨releasedState, releasedGlobal, threads, .ok false, none, none⟩
  | some waiter =>
    match threads.unblockThread waiter .Semaphore with
    | .error error => return ⟨releasedState, releasedGlobal, threads,
        .error (.threadManager error), none, none⟩
    | .ok (unblocked, obligation) =>
      let program := callbackProgramFor callbackRegistry obligation.callbackToken
      return ⟨releasedState, releasedGlobal, unblocked, .ok true,
        some { unblock := obligation, program := program }, none⟩

end SemaphoreState

end Miri.Concurrency
