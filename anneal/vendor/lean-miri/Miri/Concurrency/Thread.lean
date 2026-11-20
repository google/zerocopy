import Miri.Concurrency.VectorClock

/-!
# Thread lifecycle state used by Miri's concurrency hooks

This is a source-shaped state model of `src/concurrency/thread.rs` at the
pinned revision. It keeps the manager's contiguous, never-reused thread IDs,
active ID, every thread's Enabled/Blocked/Terminated state, join status,
blocked callback token and deadline, names, stacks, origin span, stack-empty
callback, frame-cache index, unwind payloads, last-error location, TLS map,
and scheduler flags. Interpreter frames, pointers, spans, and machine callbacks
are opaque tokens here: their concrete Miri behavior is outside Lean's
concurrency state model, and callback-dependent operations return explicit
obligations rather than assuming callback success.

This module does not implement MIR execution, TLS allocation/deallocation,
stack unwinding, callback code, or Miri's scheduler.
-/

namespace Miri.Concurrency

/-- A Rust `ThreadId`, represented with the exact unsigned 32-bit bound. -/
structure ThreadId where
  private mk ::
  value : Fin 4294967296
  deriving DecidableEq, Repr

namespace ThreadId

def MAIN_THREAD : ThreadId := ⟨⟨0, by decide⟩⟩

def ofU32 (value : Nat) (bound : value < 4294967296) : ThreadId :=
  ⟨⟨value, bound⟩⟩

/-- Checked counterpart of rustc-index `Idx::new` for host vector indices. -/
def toNat (id : ThreadId) : Nat := id.value.val

end ThreadId

/-- Reasons retained verbatim by `ThreadState::Blocked`. -/
inductive BlockReason where
  | Join (thread : ThreadId)
  | Sleep | Mutex | Condvar | RwLock | Semaphore | Futex | InitOnce
  | Readiness | Eventfd | VirtualSocket | IO
  deriving DecidableEq, Repr

/-- Deadline kind and opaque clock value. Clock arithmetic is owned by Miri's
clock subsystem and is not silently approximated here. -/
inductive ThreadDeadline where
  | Monotonic (opaqueInstant : Nat)
  | RealTime (opaqueSystemTime : Nat)
  deriving DecidableEq, Repr

inductive UnblockKind where
  | Ready
  | TimedOut
  deriving DecidableEq, Repr

inductive ThreadJoinStatus where
  | Joinable
  | Detached
  | Joined
  deriving DecidableEq, Repr

/-- Callback-free view of the thread state tag and blocked payload. -/
inductive ThreadState where
  | Enabled
  | Blocked (reason : BlockReason) (deadline : Option ThreadDeadline)
      (callbackToken : Nat)
  | Terminated
  deriving DecidableEq, Repr

/-- Opaque per-thread interpreter fields, preserved by lifecycle updates.
Each field corresponds to an actual `Thread` field in pinned Miri. -/
structure ThreadRecord where
  state : ThreadState
  threadName : Option (List UInt8)
  stackFrames : List Nat
  originSpanToken : Nat
  onStackEmptyCallback : Option Nat
  topUserRelevantFrame : Option Nat
  joinStatus : ThreadJoinStatus
  unwindPayloads : List Nat
  lastErrorLocation : Option Nat
  deriving Repr

namespace ThreadRecord

def initial (name : Option (List UInt8)) (onStackEmpty : Option Nat) : ThreadRecord :=
  { state := .Enabled
    threadName := name
    stackFrames := []
    originSpanToken := 0
    onStackEmptyCallback := onStackEmpty
    topUserRelevantFrame := none
    joinStatus := .Joinable
    unwindPayloads := []
    lastErrorLocation := none }

def isEnabled (thread : ThreadRecord) : Bool :=
  match thread.state with | .Enabled => true | _ => false

def isTerminated (thread : ThreadRecord) : Bool :=
  match thread.state with | .Terminated => true | _ => false

def isBlockedOn (thread : ThreadRecord) (reason : BlockReason) : Bool :=
  match thread.state with
  | .Blocked actual _ _ => actual == reason
  | _ => false

end ThreadRecord

/-- Thread-local allocation identity; the pointer token is preserved but not
interpreted as a Rust pointer by this module. -/
structure ThreadLocalAllocation where
  definitionToken : Nat
  thread : ThreadId
  pointerToken : Nat
  deriving DecidableEq, Repr

inductive ThreadError where
  | threadIdOverflow
  | invalidId
  | terminated (thread : ThreadId)
  | activeIdOutOfBounds (thread : ThreadId)
  | activeThreadNotEnabled (thread : ThreadId)
  | stackEmptyCallbackPending (thread : ThreadId)
  | stackNotEmptyAtTermination (thread : ThreadId)
  | targetNotBlocked (thread : ThreadId)
  | wrongBlockReason (expected actual : BlockReason)
  | detachAlreadyConsumed (thread : ThreadId)
  | detachNotJoinable (thread : ThreadId)
  deriving DecidableEq, Repr

/-- Miri's `EvalContext::block_thread` restrictions, checked before mutating
the ThreadManager. These are source panics/unsupported configurations, not UB
or successful blocking outcomes. -/
inductive BlockThreadSourceError where
  | realTimeTimeoutInIsolation
  | thread (error : ThreadError)
  deriving Repr

namespace ThreadId

/-- Checked counterpart of rustc-index `Idx::new` for host vector indices. -/
def ofNat (value : Nat) : Except ThreadError ThreadId :=
  if bound : value < 4294967296 then .ok ⟨⟨value, bound⟩⟩
  else .error .threadIdOverflow

end ThreadId

/-- A callback obligation created by `unblockThread`. It records the exact
callback token and execution context. A caller must supply the actual callback
execution result and resulting machine state; this model does not assume it
returns normally. -/
structure UnblockCallbackObligation where
  target : ThreadId
  previousActive : ThreadId
  reason : BlockReason
  callbackToken : Nat
  kind : UnblockKind
  deriving Repr

/-- Outcome that the caller obtained by actually invoking the thread's
`on_stack_empty` callback. -/
inductive StackEmptyCallbackResult where
  | Ready
  | Pending
  deriving DecidableEq, Repr

/-- A source TLS allocation that must be deallocated or retained as an exit
static root before the vector-clock termination hook runs. -/
structure TlsCleanupObligation where
  thread : ThreadId
  pointerToken : Nat
  leakAsStaticRoot : Bool
  deriving Repr

/-- Ordered work emitted when Miri marks a thread terminated. TLS cleanup and
the data-race termination hook precede waking joiners in the original source. -/
structure ThreadTerminationObligation where
  thread : ThreadId
  tlsCleanup : List TlsCleanupObligation
  joinWaiters : List ThreadId
  forExit : Bool
  deriving Repr

inductive TlsCleanupResult where
  | Deallocated (pointerToken : Nat)
  | RetainedAsStaticRoot (pointerToken : Nat)
  | Failed (pointerToken : Nat)
  deriving DecidableEq, Repr

inductive ThreadTerminationError where
  | threadError (error : ThreadError)
  | callbackFailedOrIncomplete
  | cleanupResultCountMismatch
  | cleanupResultMismatch (expected actual : TlsCleanupResult)
  deriving Repr

/-- ThreadManager state from pinned Miri, with opaque TLS pointers and callback
tokens retained as data. Threads remain in the list after termination. -/
structure ThreadManager where
  activeThread : ThreadId
  threads : List ThreadRecord
  threadLocalAllocs : List ThreadLocalAllocation
  yieldActiveThread : Bool
  fixedScheduling : Bool
  deriving Repr

/-- The continuation after successful TLS work. `dataRaceHookThread` must be
passed to `GlobalState.threadTerminated` before `joinWaiters` are unblocked. -/
structure ThreadTerminationContinuation where
  manager : ThreadManager
  dataRaceHookThread : ThreadId
  joinWaiters : List ThreadId
  deriving Repr

namespace ThreadManager

private def get? (threads : List ThreadRecord) (index : Nat) : Option ThreadRecord :=
  threads[index]?

private def replaceAt? (threads : List ThreadRecord) (index : Nat)
    (value : ThreadRecord) : Option (List ThreadRecord) :=
  if index < threads.length then some (threads.set index value) else none

def initial (fixedScheduling : Bool) : ThreadManager :=
  { activeThread := ThreadId.MAIN_THREAD
    threads := [ThreadRecord.initial (some [109, 97, 105, 110]) none]
    threadLocalAllocs := []
    yieldActiveThread := false
    fixedScheduling := fixedScheduling }

/-- Miri's post-construction initialization: install the main stack callback;
on non-Windows targets the main thread is detached. -/
def initializeMainThread (manager : ThreadManager) (windowsTarget : Bool)
    (stackEmptyCallback : Nat) : Except ThreadError ThreadManager := do
  match manager.threads with
  | [] => .error .invalidId
  | main :: rest =>
    let main := { main with
      onStackEmptyCallback := some stackEmptyCallback
      joinStatus := if windowsTarget then .Joinable else .Detached }
    pure { manager with threads := main :: rest }

def totalThreadCount (manager : ThreadManager) : Nat := manager.threads.length

def liveThreadCount (manager : ThreadManager) : Nat :=
  manager.threads.countP (fun thread => !thread.isTerminated)

def activeThread? (manager : ThreadManager) : Option ThreadRecord :=
  get? manager.threads manager.activeThread.toNat

def thread? (manager : ThreadManager) (id : ThreadId) : Option ThreadRecord :=
  get? manager.threads id.toNat

def threadIdTryFrom (manager : ThreadManager) (rawId : Nat) :
    Except ThreadError ThreadId := do
  if bound : rawId < 4294967296 then
    let id := ThreadId.ofU32 rawId bound
    match thread? manager id with
    | none => .error .invalidId
    | some thread =>
      if thread.isTerminated then .error (.terminated id) else .ok id
  else .error .invalidId

def setActiveThread (manager : ThreadManager) (id : ThreadId) :
    Except ThreadError (ThreadManager × ThreadId) := do
  if (thread? manager id).isNone then .error (.activeIdOutOfBounds id)
  else .ok ({ manager with activeThread := id }, manager.activeThread)

/-- `create_thread` allocates the next never-reused ID and an enabled, joinable
thread whose stack-empty callback is retained. -/
def createThread (manager : ThreadManager) (onStackEmpty : Nat) :
    Except ThreadError (ThreadManager × ThreadId) := do
  let id ← ThreadId.ofNat manager.threads.length
  let thread := ThreadRecord.initial none (some onStackEmpty)
  pure ({ manager with threads := manager.threads ++ [thread] }, id)

def setThreadName (manager : ThreadManager) (id : ThreadId) (name : List UInt8) :
    Except ThreadError ThreadManager := do
  let thread ← match thread? manager id with
    | none => .error .invalidId
    | some thread => .ok thread
  let threads ← match replaceAt? manager.threads id.toNat { thread with threadName := some name } with
    | none => .error .invalidId
    | some threads => .ok threads
  pure { manager with threads := threads }

/-- Detach follows the two source branches, including Windows' allowance for
detaching an already-terminated joined thread exactly once. -/
def detachThread (manager : ThreadManager) (id : ThreadId)
    (allowTerminatedJoined : Bool) : Except ThreadError ThreadManager := do
  let thread ← match thread? manager id with
    | none => .error .invalidId
    | some thread => .ok thread
  let isUb :=
    if allowTerminatedJoined && thread.isTerminated then
      thread.joinStatus == .Detached
    else
      thread.joinStatus != .Joinable
  if isUb then
    if thread.joinStatus == .Detached then .error (.detachAlreadyConsumed id)
    else .error (.detachNotJoinable id)
  else
    let threads ← match replaceAt? manager.threads id.toNat
        { thread with joinStatus := .Detached } with
      | none => .error .invalidId
      | some threads => .ok threads
    pure { manager with threads := threads }

def markJoined (manager : ThreadManager) (id : ThreadId) :
    Except ThreadError ThreadManager := do
  let thread ← match thread? manager id with
    | none => .error .invalidId
    | some thread => .ok thread
  if thread.joinStatus != .Joinable then .error (.detachNotJoinable id)
  else
    let threads ← match replaceAt? manager.threads id.toNat
        { thread with joinStatus := .Joined } with
      | none => .error .invalidId
      | some threads => .ok threads
    pure { manager with threads := threads }

def blockThread (manager : ThreadManager) (reason : BlockReason)
    (deadline : Option ThreadDeadline) (callbackToken : Nat) :
    Except ThreadError ThreadManager := do
  let id := manager.activeThread
  let thread ← match activeThread? manager with
    | none => .error (.activeIdOutOfBounds id)
    | some thread => .ok thread
  if !thread.isEnabled then .error (.activeThreadNotEnabled id)
  else
    let threads ← match replaceAt? manager.threads id.toNat
        { thread with state := .Blocked reason deadline callbackToken } with
      | none => .error (.activeIdOutOfBounds id)
      | some threads => .ok threads
    pure { manager with threads := threads }

def blockThreadWithRuntimeConstraints (manager : ThreadManager)
    (reason : BlockReason) (deadline : Option ThreadDeadline)
    (callbackToken : Nat) (communicate : Bool) :
    Except BlockThreadSourceError ThreadManager := do
  if (match deadline with | some (.RealTime _) => true | _ => false) && !communicate then
    throw .realTimeTimeoutInIsolation
  (blockThread manager reason deadline callbackToken).mapError
    BlockThreadSourceError.thread

/-- Put a blocked thread back in Enabled state and switch to it for execution.
The callback is returned as an obligation, not executed or assumed successful. -/
def unblockThread (manager : ThreadManager) (id : ThreadId) (reason : BlockReason)
    (kind : UnblockKind := .Ready) :
    Except ThreadError (ThreadManager × UnblockCallbackObligation) := do
  let thread ← match thread? manager id with
    | none => .error .invalidId
    | some thread => .ok thread
  let (actualReason, _deadline, callbackToken) ← match thread.state with
    | .Blocked actual deadline callback => .ok (actual, deadline, callback)
    | _ => .error (.targetNotBlocked id)
  if actualReason != reason then .error (.wrongBlockReason reason actualReason)
  let threads ← match replaceAt? manager.threads id.toNat
      { thread with state := .Enabled } with
    | none => .error .invalidId
    | some threads => .ok threads
  let obligation : UnblockCallbackObligation :=
    { target := id, previousActive := manager.activeThread, reason := reason,
      callbackToken := callbackToken, kind := kind }
  pure ({ manager with activeThread := id, threads := threads }, obligation)

/-- Successful callback return restores the previous active thread while
preserving every state change made by the supplied callback execution. -/
def restoreAfterCallback (managerAfterCallback : ThreadManager)
    (obligation : UnblockCallbackObligation) :
    ThreadManager :=
  { managerAfterCallback with activeThread := obligation.previousActive }

/-- The callback's exceptional return preserves its post-call machine state;
the source's `?` returns before restoring the old active thread. -/
def callbackFailedState (managerAfterFailure : ThreadManager)
    (_obligation : UnblockCallbackObligation) : ThreadManager := managerAfterFailure

/-- `set_active_thread` accepts any existing ID, including blocked or
terminated IDs; callers own source-level scheduling conditions. -/
def yield (manager : ThreadManager) : ThreadManager :=
  { manager with yieldActiveThread := true }

/-- Begin Miri's termination path after the stack-empty callback has returned
`Poll::Ready`. The state is marked Terminated first and TLS entries are removed
from the manager exactly as the source's `retain` does; cleanup itself remains
an explicit ordered obligation. -/
def beginTerminateActive (manager : ThreadManager) (forExit : Bool)
    (stackEmptyResult : StackEmptyCallbackResult) :
    Except ThreadTerminationError (ThreadManager × ThreadTerminationObligation) := do
  let id := manager.activeThread
  let thread ← match activeThread? manager with
    | none => .error (.threadError (.activeIdOutOfBounds id))
    | some thread => .ok thread
  if stackEmptyResult != .Ready then .error .callbackFailedOrIncomplete
  if !forExit && !thread.stackFrames.isEmpty then
    .error (.threadError (.stackNotEmptyAtTermination id))
  let threads ← match replaceAt? manager.threads id.toNat
      { thread with state := .Terminated } with
    | none => .error (.threadError (.activeIdOutOfBounds id))
    | some threads => .ok threads
  let tlsForThread := manager.threadLocalAllocs.filter (fun entry => entry.thread == id)
  let remainingTls := manager.threadLocalAllocs.filter (fun entry => entry.thread != id)
  let waiterIndices := (List.range manager.threads.length).filter fun rawIndex =>
    match get? manager.threads rawIndex with
    | none => false
    | some candidate => candidate.isBlockedOn (.Join id)
  let joinWaiters ← waiterIndices.mapM fun rawIndex =>
    match ThreadId.ofNat rawIndex with
    | .error error => .error (.threadError error)
    | .ok waiter => .ok waiter
  let cleanup := tlsForThread.map fun entry => {
    thread := id, pointerToken := entry.pointerToken, leakAsStaticRoot := forExit }
  let obligation : ThreadTerminationObligation :=
    { thread := id, tlsCleanup := cleanup, joinWaiters := joinWaiters, forExit := forExit }
  pure ({ manager with threads := threads, threadLocalAllocs := remainingTls }, obligation)

/-- Continue only when the external interpreter reports exactly the source
TLS action for each pointer. A failed deallocation stops before the data-race
termination hook and before joiner callbacks, as in Miri's `?` propagation. -/
def completeTlsCleanup (managerAfterMarking : ThreadManager)
    (obligation : ThreadTerminationObligation) (results : List TlsCleanupResult) :
    Except ThreadTerminationError ThreadTerminationContinuation := do
  if results.length != obligation.tlsCleanup.length then
    .error .cleanupResultCountMismatch
  let expected := obligation.tlsCleanup.map fun cleanup =>
    if cleanup.leakAsStaticRoot then
      TlsCleanupResult.RetainedAsStaticRoot cleanup.pointerToken
    else TlsCleanupResult.Deallocated cleanup.pointerToken
  for (want, actual) in expected.zip results do
    if actual != want then
      match actual with
      | .Failed _ => .error (.cleanupResultMismatch want actual)
      | _ => .error (.cleanupResultMismatch want actual)
  pure {
    manager := managerAfterMarking
    dataRaceHookThread := obligation.thread
    joinWaiters := obligation.joinWaiters }

end ThreadManager

end Miri.Concurrency
