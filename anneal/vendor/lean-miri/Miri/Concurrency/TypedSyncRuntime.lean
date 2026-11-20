import Miri.Concurrency.InitOnce

/-! Data-only source synchronization captures and execution. Every constructor
corresponds to a pinned sync.rs or OS-shim FnOnce capture; no MIR/program IR or
closure-valued state is introduced. Object and callback identities are source
Rc/Box identities supplied by the one owning machine arena. -/
namespace Miri.Concurrency.TypedSyncRuntime
open Miri.Interpreter Miri.Memory
abbrev M := EStateM StepError
structure Ref where
  index : Nat
  deriving DecidableEq, Repr
abbrev Dest := MPlaceTy Provenance
inductive Object where
  | mutex (value : MutexState)
  | rwlock (value : RwLockState)
  | condvar (value : CondvarState)
  | semaphore (value : SemaphoreState)
  | futex (value : FutexState)
  | initOnce (value : InitOnce.State)
/-- Exact OS callback captures. Constants and errno writes are evaluated when
source executes the callback, not eagerly while it is being registered. -/
abbrev User := SyncRuntime.UserCapture Ref Dest
abbrev Capture := SyncRuntime.Capture Ref Int32 Dest
structure Storage where
  objects : Array Object := #[]
  callbacks : Array (Nat × Capture) := #[]
  pthreadMutexSanity : Bool := false
  pthreadRwlockSanity : Bool := false
  pthreadCondvarSanity : Bool := false
  pthreadSemaphoreSanity : Bool := false
  macFutexSettings : Array (Ref × UInt64 × Bool) := #[]
structure Hooks (S : Type) where
  handler : SyncClockHandler
  usizeBits : Nat
  communicate : Bool
  global : M S (Option GlobalState)
  putGlobal : Option GlobalState → M S Unit
  threads : M S ThreadManager
  putThreads : ThreadManager → M S Unit
  get : Ref → M S Object
  put : Ref → Object → M S Unit
  register : Capture → M S Nat
  take : Nat → M S Capture
  cancel : Nat → M S Unit
  writeScalar : Int32 → Dest → M S Unit
  writeInt : Int → Dest → M S Unit
  errnoNegOne : String → Dest → M S Unit
  windowsTrue : M S Int32
  windowsFalse : M S Int32
  windowsTimeoutError : M S Unit
  error : SyncError → StepError

private def invalid (msg : String) : M S A := throw (.invalidProgram msg)
private def mutex (h : Hooks S) (ref : Ref) : M S MutexState := do
  let .mutex value ← h.get ref | invalid "synchronization reference is not a mutex"
  pure value
private def rwlock (h : Hooks S) (ref : Ref) : M S RwLockState := do
  let .rwlock value ← h.get ref | invalid "synchronization reference is not an rwlock"
  pure value
private def condvar (h : Hooks S) (ref : Ref) : M S CondvarState := do
  let .condvar value ← h.get ref | invalid "synchronization reference is not a condvar"
  pure value
private def semaphore (h : Hooks S) (ref : Ref) : M S SemaphoreState := do
  let .semaphore value ← h.get ref | invalid "synchronization reference is not a semaphore"
  pure value
private def futex (h : Hooks S) (ref : Ref) : M S FutexState := do
  let .futex value ← h.get ref | invalid "synchronization reference is not a futex"
  pure value
private def once (h : Hooks S) (ref : Ref) : M S InitOnce.State := do
  let .initOnce value ← h.get ref | invalid "synchronization reference is not init-once"
  pure value
private def acquire (h : Hooks S) (clock : VClock) : M S Unit := do
  match h.handler with
  | .none => pure ()
  | .vectorClocks =>
    match SyncClockState.acquire (← h.global) (← h.threads) clock with
    | .ok g => h.putGlobal g
    | .error e => throw (h.error (SyncError.ofClock e))
private def release (h : Hooks S) (update : VClock → M S Unit) : M S Unit := do
  match h.handler with
  | .none => pure ()
  | .vectorClocks =>
    match SyncClockState.prepareRelease (← h.global) (← h.threads) with
    | .error e => throw (h.error (SyncError.ofClock e))
    | .ok (clock,finish) =>
      update clock
      match finish with
      | .ok g => h.putGlobal g
      | .error e => throw (h.error (SyncError.ofClock e))
private def commit (h : Hooks S) (put : T → M S Unit)
    (transition : SyncTransition T A (Option GlobalState)) : M S A := do
  put transition.syncState
  h.putGlobal transition.global
  h.putThreads transition.threads
  match transition.outcome with
  | .error e => throw (h.error e)
  | .ok result => pure result
private def simple (h : Hooks S) (put : T → M S Unit)
    (transition : SyncTransition T A (Option GlobalState)) : M S A := do
  let result ← commit h put transition
  if transition.callback.isSome then invalid "unexpected immediate synchronization callback"
  if transition.callbackRegistration.isSome then invalid "unexpected immediate synchronization registration"
  pure result
private def queue (h : Hooks S) (put : T → M S Unit) (result : SyncQueuePrefix T) : M S Unit := do
  put result.state
  match result.outcome with | .ok () => pure () | .error e => throw (h.error e)
private def block (h : Hooks S) (reason : BlockReason) (deadline : Option ThreadDeadline)
    (token : Nat) (constraints : Bool) : M S Unit := do
  try
    let threads ← h.threads
    let blocked ← if constraints then
        match threads.blockThreadWithRuntimeConstraints reason deadline token h.communicate with
        | .ok blocked => pure blocked | .error e => throw (h.error (.blockThreadSource e))
      else
        match threads.blockThread reason deadline token with
        | .ok blocked => pure blocked | .error e => throw (h.error (.threadManager e))
    h.putThreads blocked
  catch e =>
    unless (← h.threads).threads.any (fun t => match t.state with | .Blocked _ _ actual => actual == token | _ => false) do
      h.cancel token
    throw e

def mutexLock (h : Hooks S) (ref : Ref) : M S Unit := do
  simple h (fun value => h.put ref (.mutex value)) ((← mutex h ref).lock (← h.global) (← h.threads) h.handler h.usizeBits)
def readerLock (h : Hooks S) (ref : Ref) : M S Unit := do
  simple h (fun value => h.put ref (.rwlock value)) ((← rwlock h ref).readerLock (← h.global) (← h.threads) h.handler h.usizeBits)
def writerLock (h : Hooks S) (ref : Ref) : M S Unit := do
  simple h (fun value => h.put ref (.rwlock value)) ((← rwlock h ref).writerLock (← h.global) (← h.threads) h.handler)
def mutexEnqueue (h : Hooks S) (ref : Ref) (result : Option (Int32 × Dest)) : M S Unit := do
  let threads ← h.threads
  queue h (fun value => h.put ref (.mutex value)) ((← mutex h ref).queueForBlock threads)
  let token ← h.register (.mutex ref result)
  block h .Mutex none token false
def enqueueReader (h : Hooks S) (ref : Ref) (value : Int32) (dest : Dest) : M S Unit := do
  let threads ← h.threads
  queue h (fun value => h.put ref (.rwlock value)) ((← rwlock h ref).queueReaderForBlock threads)
  let token ← h.register (.reader ref value dest)
  block h .RwLock none token false
def enqueueWriter (h : Hooks S) (ref : Ref) (value : Int32) (dest : Dest) : M S Unit := do
  let threads ← h.threads
  queue h (fun value => h.put ref (.rwlock value)) ((← rwlock h ref).queueWriterForBlock threads)
  let token ← h.register (.writer ref value dest)
  block h .RwLock none token false
private def reacquire (h : Hooks S) (ref : Ref) (value : Int32) (dest : Dest) : M S Unit := do
  if let some owner := (← mutex h ref).owner then
    if owner == (← h.threads).activeThread then invalid "condvar reacquire mutex already owned by active thread"
    mutexEnqueue h ref (some (value,dest))
  else
    mutexLock h ref
    h.writeScalar value dest

def tryBegin (h : Hooks S) (ref : Ref) (pending dest : Dest) : M S Bool := do
  let state ← once h ref
  match state.status with
  | .Uninitialized =>
    h.put ref (.initOnce {state with status := .Begun})
    h.writeScalar (← h.windowsTrue) pending
    h.writeScalar (← h.windowsTrue) dest
    pure true
  | .Complete =>
    acquire h state.clock
    h.writeScalar (← h.windowsFalse) pending
    h.writeScalar (← h.windowsTrue) dest
    pure true
  | .Begun => pure false

def executeUser (h : Hooks S) (user : User) (kind : UnblockKind) : M S Unit := do
  match user with
  | .sleep => unless kind == .TimedOut do invalid "sleep callback must time out"
  | .pthreadSemaphore timed dest =>
    match kind with
    | .Ready => h.writeScalar 0 dest
    | .TimedOut => if timed then h.errnoNegOne "ETIMEDOUT" dest else invalid "non-timed sem_wait callback timed out"
  | .futexErrno dest =>
    match kind with | .Ready => h.writeInt 0 dest | .TimedOut => h.errnoNegOne "ETIMEDOUT" dest
  | .windowsAddress dest =>
    match kind with
    | .Ready => h.writeScalar 1 dest
    | .TimedOut => h.windowsTimeoutError; h.writeScalar 0 dest
  | .windowsInitOnce ref pending dest =>
    unless kind == .Ready do invalid "INIT_ONCE callback must be Ready"
    unless ← tryBegin h ref pending dest do invalid "woken INIT_ONCE try_begin still failed"
  | .macAddress ref dest =>
    match kind with
    | .Ready =>
      let count := (← futex h ref).waiterCount
      if count >= 2^31 then invalid "macOS futex waiter count i32 conversion"
      h.writeInt (Int.ofNat count) dest
    | .TimedOut => h.errnoNegOne "ETIMEDOUT" dest
  | .macSemaphore dest => h.writeInt (if kind == .Ready then 0 else 1) dest

/-- A retry after Ready is a fresh blocking callback, not recursive execution
of an opaque closure. The source deadline and user captures are retained. -/
def semaphoreDecrement (h : Hooks S) (ref : Ref) (deadline : Option ThreadDeadline) (user : User) : M S Unit := do
  let state ← semaphore h ref
  if state.value != 0 then
    let transition := state.decrement (← h.global) (← h.threads) deadline 0 0 h.handler h.communicate
    simple h (fun value => h.put ref (.semaphore value)) {transition with callbackRegistration := none}
    executeUser h user .Ready
  else
    queue h (fun value => h.put ref (.semaphore value)) (state.queueForBlock (← h.threads))
    let token ← h.register (.semaphore ref deadline user)
    block h .Semaphore deadline token true

def futexWait (h : Hooks S) (ref : Ref) (bitset : UInt32) (deadline : Option ThreadDeadline) (user : User) : M S Unit := do
  let threads ← h.threads
  queue h (fun value => h.put ref (.futex value)) ((← futex h ref).queueForBlock threads bitset)
  let token ← h.register (.futex ref user)
  block h .Futex deadline token true

/-- Consume Box<Self> before the first body effect; callback failure cannot
restore that box or the previously active thread. -/
def invoke (h : Hooks S) (token : Nat) (kind : UnblockKind) : M S Unit := do
  let capture ← h.take token
  match capture with
  | .mutex ref result =>
    unless kind == .Ready do invalid "mutex unblock must be Ready"
    if (← mutex h ref).owner.isSome then invalid "mutex callback woke while owned"
    mutexLock h ref
    if let some (value,dest) := result then h.writeScalar value dest
  | .reader ref value dest =>
    unless kind == .Ready do invalid "rwlock reader unblock must be Ready"
    readerLock h ref
    h.writeScalar value dest
  | .writer ref value dest =>
    unless kind == .Ready do invalid "rwlock writer unblock must be Ready"
    writerLock h ref
    h.writeScalar value dest
  | .condvar ref mutex success timeout dest =>
    match kind with
    | .Ready => acquire h (← condvar h ref).clock
    | .TimedOut =>
      let state ← condvar h ref
      let active := (← h.threads).activeThread
      h.put ref (.condvar {state with waiters := state.waiters.filter (· != active)})
    reacquire h mutex (if kind == .Ready then success else timeout) dest
  | .futex ref user =>
    match kind with
    | .Ready => acquire h (← futex h ref).clock
    | .TimedOut =>
      let state ← futex h ref
      let active := (← h.threads).activeThread
      h.put ref (.futex {state with waiters := state.waiters.filter (·.thread != active)})
    executeUser h user kind
  | .semaphore ref deadline user =>
    match kind with
    | .Ready => semaphoreDecrement h ref deadline user
    | .TimedOut =>
      let state ← semaphore h ref
      let active := (← h.threads).activeThread
      h.put ref (.semaphore {state with waiters := state.waiters.filter (· != active)})
      executeUser h user .TimedOut
  | .user user => executeUser h user kind

private def runUnblock (h : Hooks S) (obligation : UnblockCallbackObligation) : M S Unit := do
  if (← h.threads).activeThread != obligation.target then invalid "unblock callback target is not active"
  invoke h obligation.callbackToken obligation.kind
  h.putThreads (ThreadManager.restoreAfterCallback (← h.threads) obligation)
private def unblock (h : Hooks S) (thread : ThreadId) (reason : BlockReason) : M S Unit := do
  let (manager,obligation) ← match (← h.threads).unblockThread thread reason with
    | .ok value => pure value | .error e => throw (h.error (.threadManager e))
  h.putThreads manager
  runUnblock h obligation
private def finish (h : Hooks S) (put : T → M S Unit)
    (transition : SyncTransition T A (Option GlobalState)) : M S A := do
  let result ← commit h put transition
  if let some request := transition.callback then
    runUnblock h request.unblock
    for thread in request.remainingWakeups do unblock h thread request.unblock.reason
  pure result

def mutexUnlock (h : Hooks S) (ref : Ref) : M S MutexUnlockResult := do
  finish h (fun value => h.put ref (.mutex value)) ((← mutex h ref).unlock (← h.global) (← h.threads) h.handler)
def readerUnlock (h : Hooks S) (ref : Ref) : M S Bool := do
  finish h (fun value => h.put ref (.rwlock value)) ((← rwlock h ref).readerUnlock (← h.global) (← h.threads) h.handler)
def writerUnlock (h : Hooks S) (ref : Ref) : M S Bool := do
  finish h (fun value => h.put ref (.rwlock value)) ((← rwlock h ref).writerUnlock (← h.global) (← h.threads) h.handler)
def condvarWait (h : Hooks S) (ref mutex : Ref) (deadline : Option ThreadDeadline)
    (success timeout : Int32) (dest : Dest) : M S Unit := do
  let unlocked ← mutexUnlock h mutex
  match unlocked with
  | .returnedNone => throw (h.error .condvarWaitMutexNotLocked)
  | .returnedSome count => if count != 1 then throw (h.error (.condvarWaitRecursiveMutex count))
  let threads ← h.threads
  queue h (fun value => h.put ref (.condvar value)) ((← condvar h ref).queueForBlock threads unlocked)
  let token ← h.register (.condvar ref mutex success timeout dest)
  block h .Condvar deadline token true
def condvarSignal (h : Hooks S) (ref : Ref) : M S Bool := do
  finish h (fun value => h.put ref (.condvar value)) ((← condvar h ref).signal (← h.global) (← h.threads) h.handler)
def futexWake (h : Hooks S) (ref : Ref) (bitset : UInt32) (count : Nat) : M S Nat := do
  finish h (fun value => h.put ref (.futex value)) ((← futex h ref).wake (← h.global) (← h.threads) bitset count h.handler)
def semaphoreIncrement (h : Hooks S) (ref : Ref) : M S Bool := do
  finish h (fun value => h.put ref (.semaphore value)) ((← semaphore h ref).increment (← h.global) (← h.threads) h.handler)

def begin (h : Hooks S) (ref : Ref) : M S Unit := do
  let state ← once h ref
  unless state.status == .Uninitialized do invalid "beginning already begun or complete init once"
  h.put ref (.initOnce {state with status := .Begun})
def enqueueInitOnce (h : Hooks S) (ref : Ref) (user : User) : M S Unit := do
  let state ← once h ref
  let active := (← h.threads).activeThread
  if state.status == .Complete then invalid "queueing on complete init once"
  h.put ref (.initOnce {state with waiters := state.waiters ++ [active]})
  let token ← h.register (.user user)
  block h .InitOnce none token false
def complete (h : Hooks S) (ref : Ref) : M S Unit := do
  let state ← once h ref
  unless state.status == .Begun do invalid "completing already complete or uninit init once"
  h.put ref (.initOnce {state with status := .Complete})
  release h fun clock => do h.put ref (.initOnce {(← once h ref) with clock := clock})
  let state ← once h ref
  h.put ref (.initOnce {state with waiters := []})
  for thread in state.waiters do unblock h thread .InitOnce
def fail (h : Hooks S) (ref : Ref) : M S Unit := do
  let state ← once h ref
  unless state.status == .Begun do invalid "failing already complete or uninit init once"
  h.put ref (.initOnce {state with status := .Uninitialized})
  release h fun clock => do h.put ref (.initOnce {(← once h ref) with clock := clock})
  let state ← once h ref
  if let thread::rest := state.waiters then
    h.put ref (.initOnce {state with waiters := rest})
    unblock h thread .InitOnce
end Miri.Concurrency.TypedSyncRuntime
