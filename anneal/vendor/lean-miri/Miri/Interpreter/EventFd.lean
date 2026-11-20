import Miri.Interpreter.Readiness

/-! Pinned unix/linux_like/eventfd.rs. The source read/write retry callback
re-reads the user buffer on every write retry, even though num is captured.
Concrete retry-budget exhaustion is an unresolved execution resource outcome. -/
namespace Miri.Interpreter.EventFd
open Miri.ABI Miri.Memory Miri.Concurrency
abbrev M := EStateM StepError
abbrev Finish (S : Type) := IoCompletionData.Finish S IoError.ErrorKind
structure Event where
  counter : UInt64
  nonblock : Bool
  clock : VClock := .default
  blockedReads : Array ThreadId := #[]
  blockedWrites : Array ThreadId := #[]

def maximumCounter : Nat := 2^64-2

def readiness (event : Event) : Files.Readiness :=
  {readable := event.counter != 0,writable := event.counter.toNat != maximumCounter}

inductive DeferredBackend (S F : Type) where
  | legacy
  | typed (read : F → MPlaceTy Provenance → IoCompletionData.Capture → M S Unit)
      (write : F → MPlaceTy Provenance → IoCompletionData.Capture → M S Unit)
structure PhysicalHooks (S F : Type) where
  runtime : SyncRuntime.Hooks S Nat Int32 (MPlaceTy Provenance)
  getEvent : F → M S Event
  putEvent : F → Event → M S Unit
  cloneFd : F → M S F
  dropFd : F → M S Unit
  insertNew : Event → M S Int32
  libcI32 : String → M S Int32
  readU32 : OpTy Provenance → M S UInt32
  readI32 : OpTy Provenance → M S Int32
  u64Layout : M S LocalLayout
  /-- Source ptr_to_mplace_unaligned: formation alone performs no memory access. -/
  unaligned : Pointer (Option Provenance) → LocalLayout → M S (MPlaceTy Provenance)
  readU64 : MPlaceTy Provenance → M S UInt64
  writeU64 : UInt64 → MPlaceTy Provenance → M S Unit
  /-- Actual update_fd_readiness(fd, FORCE_EDGE), including source clock effects. -/
  updateReadiness : F → M S Unit
  /-- Actual active-thread/stack switch, FnOnce callback and restore. -/
  unblockThread : ThreadId → M S Unit

structure Hooks (S F : Type) extends PhysicalHooks S F where
  deferred : DeferredBackend S F

private def acquire (h : Hooks S F) (clock : VClock) : M S Unit := do
  match h.runtime.handler with
  | .none => pure ()
  | .vectorClocks =>
    match SyncClockState.acquire (← h.runtime.global) (← h.runtime.threads) clock with
    | .error error => throw (h.runtime.error (SyncError.ofClock error))
    | .ok global => h.runtime.putGlobal global
private def release (h : Hooks S F) (fd : F) : M S Unit := do
  match h.runtime.handler with
  | .none => pure ()
  | .vectorClocks =>
    match SyncClockState.prepareRelease (← h.runtime.global) (← h.runtime.threads) with
    | .error error => throw (h.runtime.error (SyncError.ofClock error))
    | .ok (clock,finish) =>
      let event ← h.getEvent fd
      h.putEvent fd {event with clock := event.clock.join clock}
      match finish with
      | .error error => throw (h.runtime.error (SyncError.ofClock error))
      | .ok global => h.runtime.putGlobal global

/-- The arena owns one strong FD capture until callback completion/cancellation.
The caller retains its separate lexical FD ownership. -/
private def block (h : Hooks S F) (fd : F) (callback : F → SyncRuntime.Callback S) : M S Unit := do
  let retained ← h.cloneFd fd
  let (registry,token) := (← h.runtime.callbacks).registerOwned (callback retained) (h.dropFd retained)
  h.runtime.putCallbacks registry
  match (← h.runtime.threads).blockThreadWithRuntimeConstraints .Eventfd none token
      h.runtime.communicate with
  | .error error =>
    SyncRuntime.cancelCallback h.runtime token
    throw (h.runtime.error (.blockThreadSource error))
  | .ok threads => h.runtime.putThreads threads

private def readLoop (h : Hooks S F) : Nat → F → MPlaceTy Provenance → Finish S → M S Unit
  | 0,_,_,_ => throw (.resourceExhaustion "eventfd read retry budget")
  | fuel+1,fd,buffer,finish => do
    let event ← h.getEvent fd
    let counter := event.counter
    h.putEvent fd {event with counter := 0}
    if counter == 0 then
      if event.nonblock then finish (.error .WouldBlock)
      else
        let thread := (← h.runtime.threads).activeThread
        let event ← h.getEvent fd
        h.putEvent fd {event with blockedReads := event.blockedReads.push thread}
        block h fd fun retained kind => do
          if kind != .Ready then throw (.invalidProgram "eventfd read callback must be Ready")
          readLoop h fuel retained buffer finish
    else
      acquire h (← h.getEvent fd).clock
      h.writeU64 counter buffer
      let event ← h.getEvent fd
      let waiting := event.blockedWrites
      h.putEvent fd {event with blockedWrites := #[]}
      for thread in waiting do h.unblockThread thread
      h.updateReadiness fd
      finish (.ok buffer.layout.layout.size.bytes.toNat)

private def writeLoop (h : Hooks S F) : Nat → F → MPlaceTy Provenance → Finish S → M S Unit
  | 0,_,_,_ => throw (.resourceExhaustion "eventfd write retry budget")
  | fuel+1,fd,buffer,finish => do
    let num ← h.readU64 buffer
    if num.toNat == 2^64-1 then finish (.error .InvalidInput); return
    let event ← h.getEvent fd
    let total := event.counter.toNat+num.toNat
    if total <= maximumCounter then
      release h fd
      let event ← h.getEvent fd
      h.putEvent fd {event with counter := UInt64.ofNat total}
      let event ← h.getEvent fd
      let waiting := event.blockedReads
      h.putEvent fd {event with blockedReads := #[]}
      for thread in waiting do h.unblockThread thread
      h.updateReadiness fd
      finish (.ok buffer.layout.layout.size.bytes.toNat)
    else if event.nonblock then finish (.error .WouldBlock)
    else
      let thread := (← h.runtime.threads).activeThread
      let event ← h.getEvent fd
      h.putEvent fd {event with blockedWrites := event.blockedWrites.push thread}
      block h fd fun retained kind => do
        if kind != .Ready then throw (.invalidProgram "eventfd write callback must be Ready")
        writeLoop h fuel retained buffer finish

private def onError (action : M S A) (cleanup : M S Unit) : M S A := fun state =>
  match action state with
  | .ok value state => .ok value state
  | .error error state => match cleanup state with
    | .ok _ state => .error error state | .error next state => .error next state

/-- Takes one source strong self reference. Production transfers it into the
typed retry interpreter; the fixture branch retains its explicit runner bound. -/
def read (h : Hooks S F) (retryBudget : Nat) (fd : F)
    (pointer : Pointer (Option Provenance)) (length : Nat) (finish : Finish S) : M S Unit := do
  let layout ← onError h.u64Layout (h.dropFd fd)
  if length < layout.layout.size.bytes.toNat then
    Files.withDrop (finish (.error .InvalidInput)) (h.dropFd fd)
    return
  let buffer ← onError (h.unaligned pointer layout) (h.dropFd fd)
  match h.deferred with
  | .legacy => Files.withDrop (readLoop h retryBudget fd buffer finish) (h.dropFd fd)
  | .typed read _ =>
    let some capture := finish.capture |
      Files.withDrop (throw (.callback "eventfd requires source finish capture")) (h.dropFd fd)
    read fd buffer capture

def write (h : Hooks S F) (retryBudget : Nat) (fd : F)
    (pointer : Pointer (Option Provenance)) (length : Nat) (finish : Finish S) : M S Unit := do
  let layout ← onError h.u64Layout (h.dropFd fd)
  if length != layout.layout.size.bytes.toNat then
    Files.withDrop (finish (.error .InvalidInput)) (h.dropFd fd)
    return
  let buffer ← onError (h.unaligned pointer layout) (h.dropFd fd)
  match h.deferred with
  | .legacy => Files.withDrop (writeLoop h retryBudget fd buffer finish) (h.dropFd fd)
  | .typed _ write =>
    let some capture := finish.capture |
      Files.withDrop (throw (.callback "eventfd requires source finish capture")) (h.dropFd fd)
    write fd buffer capture

def create (h : Hooks S F) (value flags : OpTy Provenance) : M S Int32 := do
  let value ← h.readU32 value
  let mut flags ← h.readI32 flags
  let cloexec ← h.libcI32 "EFD_CLOEXEC"
  let nonblock ← h.libcI32 "EFD_NONBLOCK"
  let semaphore ← h.libcI32 "EFD_SEMAPHORE"
  if flags &&& semaphore == semaphore then throw (.unsupported "eventfd EFD_SEMAPHORE unsupported")
  let mut isNonblock := false
  if flags &&& cloexec == cloexec then flags := flags &&& ~~~cloexec
  if flags &&& nonblock == nonblock then
    flags := flags &&& ~~~nonblock
    isNonblock := true
  if flags != 0 then throw (.unsupported "eventfd unknown flags")
  h.insertNew {counter := value.toUInt64,nonblock := isNonblock}
end Miri.Interpreter.EventFd
