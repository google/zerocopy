import Miri.Interpreter.IoCompletion
import Miri.Interpreter.EventFd
import Miri.Interpreter.PollShims

/-! Source-owned IO FnOnce environments. This first connected unit executes
all eventfd retry bodies without recursive function-valued state or a retry
budget. Poll/epoll environments retain their exact source identities and are
reserved for their connected source adapters. -/
namespace Miri.Interpreter.OwnedIoRuntime
open Miri.ABI Miri.Memory Miri.Concurrency
abbrev M := EStateM StepError
inductive Capture (F : Type) where
  | eventRead (fd : F) (buffer : IoCompletion.Dest) (finish : IoCompletion.Capture)
  | eventWrite (num : UInt64) (fd : F) (buffer : IoCompletion.Dest) (finish : IoCompletion.Capture)
  | poll (watcher : Nat) (interests : Array (Int32 × IoCompletion.Dest)) (dest : IoCompletion.Dest)
  | epoll (fd : F) (event dest : IoCompletion.Dest)
structure Storage (F : Type) where
  callbacks : Array (Nat × Capture F) := #[]
structure Hooks (S F E : Type) where
  event : EventFd.PhysicalHooks S F
  completion : IoCompletion.Hooks S E
  errorFromKind : IoError.ErrorKind → M S (IoError.Error E)
  register : Capture F → M S Nat
  take : Nat → M S (Capture F)
  dropWatcher : Nat → M S Unit
  /-- Source write_ready_events, not an arbitrary completion callback. -/
  pollReady : Nat → Array (Int32 × IoCompletion.Dest) → M S UInt32
  writeU32 : UInt32 → IoCompletion.Dest → M S Unit
  epollReady : F → IoCompletion.Dest → IoCompletion.Dest → M S Nat
  epollRemoveBlocked : F → ThreadId → M S Unit
private def onError (action : M S A) (cleanup : M S Unit) : M S A := fun state =>
  match action state with
  | .ok value state => .ok value state
  | .error error state => match cleanup state with
    | .ok _ state => .error error state | .error next state => .error next state
private def invalid (message : String) : M S A := throw (.invalidProgram message)
private def finish (h : Hooks S F E) (capture : IoCompletion.Capture) (result : Except IoError.ErrorKind Nat) : M S Unit := do
  let result ← match result with
    | .ok count => pure (.ok count)
    | .error kind => pure (.error (← h.errorFromKind kind))
  IoCompletion.invoke h.completion capture result

def dropCapture (h : Hooks S F E) : Capture F → M S Unit
  | .eventRead fd _ _ | .eventWrite _ fd _ _ | .epoll fd _ _ => h.event.dropFd fd
  | .poll watcher _ _ => h.dropWatcher watcher
def cancel (h : Hooks S F E) (token : Nat) : M S Unit := do
  dropCapture h (← h.take token)
def block (h : Hooks S F E) (capture : Capture F) (reason : BlockReason)
    (deadline : Option ThreadDeadline) : M S Unit := do
  let token ← onError (h.register capture) (dropCapture h capture)
  try
    let manager ← h.event.runtime.threads
    let blocked ← match manager.blockThreadWithRuntimeConstraints reason deadline token h.event.runtime.communicate with
      | .ok manager => pure manager
      | .error error => throw (h.event.runtime.error (.blockThreadSource error))
    h.event.runtime.putThreads blocked
  catch error =>
    unless (← h.event.runtime.threads).threads.any (fun thread => match thread.state with
        | .Blocked _ _ actual => actual == token | _ => false) do cancel h token
    throw error
private def acquire (h : Hooks S F E) (clock : VClock) : M S Unit := do
  match h.event.runtime.handler with
  | .none => pure ()
  | .vectorClocks =>
    match SyncClockState.acquire (← h.event.runtime.global) (← h.event.runtime.threads) clock with
    | .ok global => h.event.runtime.putGlobal global
    | .error error => throw (h.event.runtime.error (SyncError.ofClock error))
private def release (h : Hooks S F E) (fd : F) : M S Unit := do
  match h.event.runtime.handler with
  | .none => pure ()
  | .vectorClocks =>
    match SyncClockState.prepareRelease (← h.event.runtime.global) (← h.event.runtime.threads) with
    | .error error => throw (h.event.runtime.error (SyncError.ofClock error))
    | .ok (clock,next) =>
      let event ← h.event.getEvent fd
      h.event.putEvent fd {event with clock := event.clock.join clock}
      match next with
      | .ok global => h.event.runtime.putGlobal global
      | .error error => throw (h.event.runtime.error (SyncError.ofClock error))

/-- Takes source ownership of fd. A deferred callback receives that ownership
without a clone/drop detour; immediate completion and failures drop it once. -/
def readStep (h : Hooks S F E) (fd : F) (buffer : IoCompletion.Dest) (completion : IoCompletion.Capture) : M S Unit := do
  let event ← onError (do
    let event ← h.event.getEvent fd
    h.event.putEvent fd {event with counter := 0}
    pure event) (h.event.dropFd fd)
  if event.counter == 0 then
    if event.nonblock then Files.withDrop (finish h completion (.error .WouldBlock)) (h.event.dropFd fd)
    else
      onError (do
        let thread := (← h.event.runtime.threads).activeThread
        let event ← h.event.getEvent fd
        h.event.putEvent fd {event with blockedReads := event.blockedReads.push thread}) (h.event.dropFd fd)
      block h (.eventRead fd buffer completion) .Eventfd none
  else Files.withDrop (do
    acquire h (← h.event.getEvent fd).clock
    h.event.writeU64 event.counter buffer
    let event ← h.event.getEvent fd
    h.event.putEvent fd {event with blockedWrites := #[]}
    for thread in event.blockedWrites do h.event.unblockThread thread
    h.event.updateReadiness fd
    finish h completion (.ok buffer.layout.layout.size.bytes.toNat)) (h.event.dropFd fd)

def writeStep (h : Hooks S F E) (fd : F) (buffer : IoCompletion.Dest) (completion : IoCompletion.Capture) : M S Unit := do
  let num ← onError (h.event.readU64 buffer) (h.event.dropFd fd)
  if num.toNat == 2^64-1 then
    Files.withDrop (finish h completion (.error .InvalidInput)) (h.event.dropFd fd)
    return
  let event ← onError (h.event.getEvent fd) (h.event.dropFd fd)
  let total := event.counter.toNat+num.toNat
  if total <= EventFd.maximumCounter then Files.withDrop (do
    release h fd
    let event ← h.event.getEvent fd
    h.event.putEvent fd {event with counter := UInt64.ofNat total}
    let event ← h.event.getEvent fd
    h.event.putEvent fd {event with blockedReads := #[]}
    for thread in event.blockedReads do h.event.unblockThread thread
    h.event.updateReadiness fd
    finish h completion (.ok buffer.layout.layout.size.bytes.toNat)) (h.event.dropFd fd)
  else if event.nonblock then Files.withDrop (finish h completion (.error .WouldBlock)) (h.event.dropFd fd)
  else
    onError (do
      let thread := (← h.event.runtime.threads).activeThread
      let event ← h.event.getEvent fd
      h.event.putEvent fd {event with blockedWrites := event.blockedWrites.push thread}) (h.event.dropFd fd)
    block h (.eventWrite num fd buffer completion) .Eventfd none

/-- Source call consumes Box<Self> first. Each arm owns its captured strong
reference, including every error path; retries transfer it into the next box. -/
def invoke (h : Hooks S F E) (token : Nat) (kind : UnblockKind) : M S Unit := do
  let capture ← h.take token
  match capture with
  | .eventRead fd buffer completion =>
    unless kind == .Ready do Files.withDrop (invalid "eventfd read callback must be Ready") (h.event.dropFd fd)
    readStep h fd buffer completion
  | .eventWrite _ fd buffer completion =>
    unless kind == .Ready do Files.withDrop (invalid "eventfd write callback must be Ready") (h.event.dropFd fd)
    writeStep h fd buffer completion
  | .poll watcher interests dest => Files.withDrop (do
    match kind with
    | .TimedOut => h.writeU32 0 dest
    | .Ready => h.writeU32 (← h.pollReady watcher interests) dest) (h.dropWatcher watcher)
  | .epoll fd event dest => Files.withDrop (do
    match kind with
    | .TimedOut =>
      h.epollRemoveBlocked fd (← h.event.runtime.threads).activeThread
      h.completion.writeInt 0 dest
    | .Ready =>
      let count ← h.epollReady fd dest event
      unless count > 0 do invalid "epoll wait woke without events") (h.event.dropFd fd)
end Miri.Interpreter.OwnedIoRuntime
