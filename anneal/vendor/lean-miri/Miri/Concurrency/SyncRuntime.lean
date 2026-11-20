import Miri.Concurrency.Sync
import Miri.Interpreter.Step
import Miri.Interpreter.MachineHooks

/-! Executable callback binding for pinned concurrency/sync.rs. Canonical
Sync transitions own lock/clock/queue rules; this layer runs real typed closures,
scalar stores and ThreadManager callbacks rather than accepting token completion. -/
namespace Miri.Concurrency.SyncRuntime
open Miri.Interpreter
abbrev M := EStateM StepError
abbrev Callback (S : Type) := UnblockKind → M S Unit
structure Registry (S : Type) where
  next : Nat := 0
  entries : Array (Nat × Callback S) := #[]
  /-- Explicit semantic Drop actions for owned captures. Plain callbacks use
  lexical cleanup (for example Files.withDrop) or contain non-owning IDs. -/
  disposers : Array (Nat × M S Unit) := #[]
def Registry.register (registry : Registry S) (callback : Callback S) : Registry S × Nat :=
  ({ registry with next := registry.next + 1, entries := registry.entries.push (registry.next,callback) },registry.next)

/-- Owned captures require an actual stateful drop, never a GC-root promise. -/
def Registry.registerOwned (registry : Registry S) (callback : Callback S)
    (dropCaptures : M S Unit) : Registry S × Nat :=
  let (registry,token) := registry.register callback
  ({registry with disposers := registry.disposers.push (token,dropCaptures)},token)

structure TakenCallback (S : Type) where
  body : Callback S
  dispose : Option (M S Unit)

/-- Source MachineCallback.call consumes Box<Self> before running its body.
Duplicate tokens are representation failures, never an arbitrary first match. -/
def Registry.take (registry : Registry S) (token : Nat) :
    Except StepError (Registry S × TakenCallback S) := do
  let entries := registry.entries.filter (·.1 == token)
  if entries.size != 1 then throw (.unsupported "missing or ambiguous typed callback")
  let some (_,body) := entries[0]? | throw (.invalidProgram "callback arena lookup failed")
  let drops := registry.disposers.filter (·.1 == token)
  if drops.size > 1 then throw (.invalidProgram "ambiguous callback capture ownership")
  let dispose := drops[0]?.map Prod.snd
  return ({registry with
    entries := registry.entries.filter (·.1 != token)
    disposers := registry.disposers.filter (·.1 != token)},⟨body,dispose⟩)

private def withDispose (action : M S A) (dispose : Option (M S Unit)) : M S A := fun state =>
  let finish (outcome : Except StepError A) (state : S) :=
    match dispose with
    | none => match outcome with | .ok value => .ok value state | .error error => .error error state
    | some cleanup =>
      match cleanup state with
      | .error error state => .error error state
      | .ok () state => match outcome with | .ok value => .ok value state | .error error => .error error state
  match action state with
  | .ok value state => finish (.ok value) state
  | .error error state => finish (.error error) state
/-- Data-only captures of source OS callbacks. -/
inductive UserCapture (R D : Type) where
  | pthreadSemaphore (timed : Bool) (dest : D)
  | futexErrno (dest : D)
  | windowsAddress (dest : D)
  | windowsInitOnce (ref : R) (pending dest : D)
  | macAddress (ref : R) (dest : D)
  | macSemaphore (dest : D)
  | sleep
inductive Capture (R V D : Type) where
  | mutex (ref : R) (result : Option (V × D))
  | reader (ref : R) (value : V) (dest : D)
  | writer (ref : R) (value : V) (dest : D)
  | condvar (ref mutex : R) (success timeout : V) (dest : D)
  | futex (ref : R) (user : UserCapture R D)
  | semaphore (ref : R) (deadline : Option ThreadDeadline) (user : UserCapture R D)
  | user (value : UserCapture R D)
/-- Production stores typed captures. Only the explicit fixture branch carries
an arbitrary function registry; a production constructor never supplies one. -/
inductive CallbackBackend (S R V D : Type) where
  | legacy (get : M S (Registry S)) (put : Registry S → M S Unit)
  | typed (register : Capture R V D → M S Nat) (run : Nat → UnblockKind → M S Unit)
      (cancel : Nat → M S Unit) (owns : Nat → M S Bool)
structure Hooks (S R V D : Type) where
  handler : SyncClockHandler
  usizeBits : Nat
  communicate : Bool
  global : M S (Option GlobalState)
  putGlobal : Option GlobalState → M S Unit
  threads : M S ThreadManager
  putThreads : ThreadManager → M S Unit
  callbackBackend : CallbackBackend S R V D
  mutex : R → M S MutexState
  putMutex : R → MutexState → M S Unit
  rwlock : R → M S RwLockState
  putRwlock : R → RwLockState → M S Unit
  condvar : R → M S CondvarState
  putCondvar : R → CondvarState → M S Unit
  futex : R → M S FutexState
  putFutex : R → FutexState → M S Unit
  semaphore : R → M S SemaphoreState
  putSemaphore : R → SemaphoreState → M S Unit
  writeScalar : V → D → M S Unit
  error : SyncError → StepError
/-- Legacy-only compatibility accessors. Production typed backends expose no
function registry; an unported caller remains an explicit callback obligation. -/
def Hooks.callbacks (h : Hooks S R V D) : M S (Registry S) :=
  match h.callbackBackend with
  | .legacy get _ => get
  | .typed .. => throw (.callback "operation requires a typed source callback capture")
def Hooks.putCallbacks (h : Hooks S R V D) (registry : Registry S) : M S Unit :=
  match h.callbackBackend with
  | .legacy _ put => put registry
  | .typed .. => throw (.callback "cannot install a function registry in the typed source backend")
def register (h : Hooks S R V D) (capture : Option (Capture R V D)) (callback : Callback S) : M S Nat := do
  match h.callbackBackend with
  | .legacy get put =>
    let (registry,token) := (← get).register callback
    put registry
    pure token
  | .typed register _ _ _ =>
    let some capture := capture | throw (.callback "source callback capture missing at typed registration")
    register capture
def ownsCallback (h : Hooks S R V D) (token : Nat) : M S Bool := do
  match h.callbackBackend with
  | .legacy get _ => pure ((← get).entries.any (·.1 == token))
  | .typed _ _ _ owns => owns token
/-- This operation is only available on the explicit legacy fixture backend. -/
def takeCallback (h : Hooks S R V D) (token : Nat) : M S (TakenCallback S) := do
  match h.callbackBackend with
  | .typed .. => throw (.invalidProgram "typed callbacks must be executed by their source interpreter")
  | .legacy get put =>
    let (registry,callback) ← match (← get).take token with
      | .ok value => pure value | .error error => throw error
    put registry
    pure callback
/-- No thread switch/restore: deadline and readiness wrappers already own it. -/
def runCallback (h : Hooks S R V D) (token : Nat) (kind : UnblockKind) : M S Unit := do
  match h.callbackBackend with
  | .typed _ run _ _ => run token kind
  | .legacy .. =>
    let callback ← takeCallback h token
    withDispose (callback.body kind) callback.dispose
/-- Cancel an unowned registration, consuming source FnOnce captures once. -/
def cancelCallback (h : Hooks S R V D) (token : Nat) : M S Unit := do
  match h.callbackBackend with
  | .typed _ _ cancel _ => cancel token
  | .legacy .. =>
    let callback ← takeCallback h token
    withDispose (pure ()) callback.dispose

/-- Source drops a newly built callback when blocking fails before ownership
moves into ThreadState::Blocked. Keep entries already owned by any thread. -/
def discardIfUnowned (h : Hooks S R V D) (token : Nat) : M S Unit := do
  if !(← ownsCallback h token) then return ()
  if (← h.threads).threads.any (fun thread => match thread.state with
      | .Blocked _ _ actual => actual == token | _ => false) then return ()
  cancelCallback h token

private def withRegistration (h : Hooks S R V D) (token : Nat) (action : M S A) : M S A :=
  withDispose action (some (discardIfUnowned h token))

def runUnblockCallback (h : Hooks S R V D) (obligation : UnblockCallbackObligation) : M S Unit := do
  if (← h.threads).activeThread != obligation.target then
    throw (.invalidProgram "unblock callback target is not the active thread")
  runCallback h obligation.callbackToken obligation.kind
  -- Restore only after callback and source capture drops succeed.
  h.putThreads (ThreadManager.restoreAfterCallback (← h.threads) obligation)
private def unblock (h : Hooks S R V D) (thread : ThreadId) (reason : BlockReason) : M S Unit := do
  match (← h.threads).unblockThread thread reason with
  | .error error => throw (h.error (.threadManager error))
  | .ok (threads,obligation) => h.putThreads threads; runUnblockCallback h obligation
private def finish (h : Hooks S R V D) (put : T → M S Unit)
    (transition : SyncTransition T A (Option GlobalState)) : M S A := do
  put transition.syncState
  h.putGlobal transition.global
  h.putThreads transition.threads
  let result ← match transition.outcome with
    | .ok value => pure value | .error error => throw (h.error error)
  if let some (token,_) := transition.callbackRegistration then
    if !(← ownsCallback h token) then
      throw (.unsupported "synchronization callback registration missing typed body")
  if let some request := transition.callback then
    runUnblockCallback h request.unblock
    for thread in request.remainingWakeups do unblock h thread request.unblock.reason
  return result
private def acquire (h : Hooks S R V D) (clock : VClock) : M S Unit := do
  match h.handler with
  | .none => pure ()
  | .vectorClocks =>
    match SyncClockState.acquire (← h.global) (← h.threads) clock with
    | .error error => throw (h.error (SyncError.ofClock error))
    | .ok global => h.putGlobal global

private def queue (h : Hooks S R V D) (put : T → M S Unit) (queuedResult : SyncQueuePrefix T) : M S Unit := do
  put queuedResult.state
  match queuedResult.outcome with | .ok () => pure () | .error error => throw (h.error error)
private def block (h : Hooks S R V D) (reason : BlockReason) (deadline : Option ThreadDeadline)
    (token : Nat) (constraints : Bool) : M S Unit := do
  let threads ← h.threads
  let blocked ← if constraints then
      match threads.blockThreadWithRuntimeConstraints reason deadline token h.communicate with
      | .ok blocked => pure blocked
      | .error error => throw (h.error (.blockThreadSource error))
    else
      match threads.blockThread reason deadline token with
      | .ok blocked => pure blocked
      | .error error => throw (h.error (.threadManager error))
  h.putThreads blocked

def mutexLock (h : Hooks S R V D) (ref : R) : M S Unit := do
  finish h (h.putMutex ref) ((← h.mutex ref).lock (← h.global) (← h.threads) h.handler h.usizeBits)
def mutexUnlock (h : Hooks S R V D) (ref : R) : M S MutexUnlockResult := do
  finish h (h.putMutex ref) ((← h.mutex ref).unlock (← h.global) (← h.threads) h.handler)
def mutexEnqueue (h : Hooks S R V D) (ref : R) (retval : Option (V × D)) : M S Unit := do
  let threads ← h.threads
  queue h (h.putMutex ref) ((← h.mutex ref).queueForBlock threads)
  let token ← register h (some (.mutex ref retval)) fun kind => do
    if kind != .Ready then throw (.invalidProgram "mutex unblock must be Ready")
    if (← h.mutex ref).owner.isSome then throw (.invalidProgram "mutex callback woke while owned")
    mutexLock h ref
    if let some (value,dest) := retval then h.writeScalar value dest
  withRegistration h token do
    block h .Mutex none token false

def readerLock (h : Hooks S R V D) (ref : R) : M S Unit := do
  finish h (h.putRwlock ref) ((← h.rwlock ref).readerLock (← h.global) (← h.threads) h.handler h.usizeBits)
def writerLock (h : Hooks S R V D) (ref : R) : M S Unit := do
  finish h (h.putRwlock ref) ((← h.rwlock ref).writerLock (← h.global) (← h.threads) h.handler)
def readerUnlock (h : Hooks S R V D) (ref : R) : M S Bool := do
  finish h (h.putRwlock ref) ((← h.rwlock ref).readerUnlock (← h.global) (← h.threads) h.handler)
def writerUnlock (h : Hooks S R V D) (ref : R) : M S Bool := do
  finish h (h.putRwlock ref) ((← h.rwlock ref).writerUnlock (← h.global) (← h.threads) h.handler)
def enqueueReader (h : Hooks S R V D) (ref : R) (value : V) (dest : D) : M S Unit := do
  let threads ← h.threads
  queue h (h.putRwlock ref) ((← h.rwlock ref).queueReaderForBlock threads)
  let token ← register h (some (.reader ref value dest)) fun kind => do
    if kind != .Ready then throw (.invalidProgram "rwlock reader unblock must be Ready")
    readerLock h ref
    h.writeScalar value dest
  withRegistration h token do
    block h .RwLock none token false
def enqueueWriter (h : Hooks S R V D) (ref : R) (value : V) (dest : D) : M S Unit := do
  let threads ← h.threads
  queue h (h.putRwlock ref) ((← h.rwlock ref).queueWriterForBlock threads)
  let token ← register h (some (.writer ref value dest)) fun kind => do
    if kind != .Ready then throw (.invalidProgram "rwlock writer unblock must be Ready")
    writerLock h ref
    h.writeScalar value dest
  withRegistration h token do
    block h .RwLock none token false

def reacquireMutex (h : Hooks S R V D) (ref : R) (value : V) (dest : D) : M S Unit := do
  if let some owner := (← h.mutex ref).owner then
    if owner == (← h.threads).activeThread then throw (.invalidProgram "condvar reacquire mutex already owned by active thread")
    mutexEnqueue h ref (some (value,dest))
  else
    mutexLock h ref
    h.writeScalar value dest

def condvarWait (h : Hooks S R V D) (ref mutex : R) (deadline : Option ThreadDeadline)
    (success timeout : V) (dest : D) : M S Unit := do
  let unlocked ← mutexUnlock h mutex
  -- Source validates old lock count only after unlock and its wake callbacks.
  match unlocked with
  | .returnedNone => throw (h.error .condvarWaitMutexNotLocked)
  | .returnedSome count =>
    if count != 1 then throw (h.error (.condvarWaitRecursiveMutex count))
  let threads ← h.threads
  queue h (h.putCondvar ref) ((← h.condvar ref).queueForBlock threads unlocked)
  let token ← register h (some (.condvar ref mutex success timeout dest)) fun kind => do
    match kind with
    | .Ready => acquire h (← h.condvar ref).clock
    | .TimedOut =>
      let state ← h.condvar ref
      let active := (← h.threads).activeThread
      h.putCondvar ref { state with waiters := state.waiters.filter (· != active) }
    reacquireMutex h mutex (if kind == .Ready then success else timeout) dest
  withRegistration h token do
    block h .Condvar deadline token true
def condvarSignal (h : Hooks S R V D) (ref : R) : M S Bool := do
  finish h (h.putCondvar ref) ((← h.condvar ref).signal (← h.global) (← h.threads) h.handler)

def futexWait (h : Hooks S R V D) (ref : R) (bitset : UInt32)
    (deadline : Option ThreadDeadline) (callback : Callback S)
    (capture : Option (UserCapture R D) := none) : M S Unit := do
  let threads ← h.threads
  queue h (h.putFutex ref) ((← h.futex ref).queueForBlock threads bitset)
  let token ← register h (capture.map (.futex ref)) fun kind => do
    match kind with
    | .Ready => acquire h (← h.futex ref).clock
    | .TimedOut =>
      let state ← h.futex ref
      let active := (← h.threads).activeThread
      h.putFutex ref { state with waiters := state.waiters.filter (·.thread != active) }
    callback kind
  withRegistration h token do
    block h .Futex deadline token true
def futexWake (h : Hooks S R V D) (ref : R) (bitset : UInt32) (count : Nat) : M S Nat := do
  finish h (h.putFutex ref) ((← h.futex ref).wake (← h.global) (← h.threads) bitset count h.handler)

/-- Each reblocking wake consumes one runner budget unit; exhaustion is explicit
and cannot establish completion of a waiting operation. -/
private def semaphoreDecrementLegacy (budget : Nat) (h : Hooks S R V D) (ref : R)
    (deadline : Option ThreadDeadline) (callback : Callback S)
    (capture : Option (UserCapture R D) := none) : M S Unit := do
  match budget with
  | 0 => throw (.resourceExhaustion "semaphore callback recursion budget exhausted")
  | budget + 1 =>
    let state ← h.semaphore ref
    if state.value != 0 then
      -- Immediate callback is source-owned on the call stack, not in the arena.
      let unused := 0
      let transition := state.decrement (← h.global) (← h.threads)
        deadline unused unused h.handler h.communicate
      finish h (h.putSemaphore ref) {transition with callbackRegistration := none}
      callback .Ready
    else
      let threads ← h.threads
      queue h (h.putSemaphore ref) (state.queueForBlock threads)
      let token ← register h (capture.map (.semaphore ref deadline)) fun kind => do
        match kind with
        | .TimedOut =>
          let state ← h.semaphore ref
          let active := (← h.threads).activeThread
          h.putSemaphore ref { state with waiters := state.waiters.filter (· != active) }
          callback .TimedOut
        | .Ready => semaphoreDecrementLegacy budget h ref deadline callback capture
      withRegistration h token do
        block h .Semaphore deadline token true

/-- Production retries are interpreted from data and need no recursive runner
budget. The legacy fixture path retains its explicit resource bound. -/
def semaphoreDecrement (budget : Nat) (h : Hooks S R V D) (ref : R)
    (deadline : Option ThreadDeadline) (callback : Callback S)
    (capture : Option (UserCapture R D) := none) : M S Unit :=
  match h.callbackBackend with
  | .legacy .. => semaphoreDecrementLegacy budget h ref deadline callback capture
  | .typed .. => semaphoreDecrementLegacy 1 h ref deadline callback capture

def semaphoreIncrement (h : Hooks S R V D) (ref : R) : M S Bool := do
  finish h (h.putSemaphore ref) ((← h.semaphore ref).increment (← h.global) (← h.threads) h.handler)

def bindMachine (base : Hooks (MachineHooks.State K U) R V D) :
    Hooks (MachineHooks.State K U) R V D := { base with
  global := do return (← get).machine.dataRace
  putGlobal := fun global => modify fun state =>
    { state with machine := { state.machine with dataRace := global } }
  threads := do return (← get).machine.threads
  putThreads := fun threads => modify fun state =>
    { state with machine := { state.machine with threads := threads } } }
end Miri.Concurrency.SyncRuntime
