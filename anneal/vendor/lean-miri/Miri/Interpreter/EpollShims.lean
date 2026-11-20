import Miri.Interpreter.PollShims

/-! Complete pinned linux_like/epoll.rs syscall policy. Epoll descriptor creation
and downcast are required actual FileDescription operations, not integer aliases. -/
namespace Miri.Interpreter.EpollShims
open Miri.ABI Miri.Memory Miri.Concurrency
abbrev M := EStateM StepError
inductive DeferredBackend (S F : Type) where
  | legacy
  | typed (block : F → MPlaceTy Provenance → MPlaceTy Provenance → Option ThreadDeadline → M S Unit)
structure Hooks (S F Iter : Type) where
  deferred : DeferredBackend S F
  poll : PollShims.Hooks S F Iter
  libcI32 : String → M S Int32
  libcU32 : String → M S UInt32
  readImmediate : OpTy Provenance → M S (OpTy Provenance)
  derefEvent : OpTy Provenance → M S (MPlaceTy Provenance)
  indexedField : MPlaceTy Provenance → Nat → M S (MPlaceTy Provenance)
  readU32 : MPlaceTy Provenance → M S UInt32
  readU64 : MPlaceTy Provenance → M S UInt64
  arrayLength : MPlaceTy Provenance → M S Nat
  /-- Actual write_int_fields_named, preserving field projection/write order. -/
  writeEvent : MPlaceTy Provenance → UInt32 → UInt64 → M S Unit
  writeI32 : Int32 → MPlaceTy Provenance → M S Unit
  setErrno : String → M S Unit
  /-- Creates an Epoll description owning this watcher, inserts it in actual FD table.
  Source metadata is Unix S_IFREG; default unsupported operations remain unsupported. -/
  insertEpoll : Nat → M S Int32
  asEpoll : F → M S (Option Nat)
private def failure (h : Hooks S F I) (errno : String) : M S Int32 := do
  h.setErrno errno
  return -1

def create (h : Hooks S F I) (flags : OpTy Provenance) : M S Int32 := do
  let flags ← h.poll.readI32 flags
  let cloexec ← h.libcI32 "EPOLL_CLOEXEC"
  if flags != cloexec && flags != 0 then throw (.unsupported "epoll_create1: only 0 or EPOLL_CLOEXEC supported")
  let watcher ← h.poll.newWatcher
  PollShims.onError (h.insertEpoll watcher) (h.poll.readiness.dropWatcher watcher)

private def constants (h : Hooks S F I) : M S (UInt32 × UInt32 × UInt32 × UInt32 × UInt32) := do
  let input ← h.libcU32 "EPOLLIN"
  let output ← h.libcU32 "EPOLLOUT"
  let rd ← h.libcU32 "EPOLLRDHUP"
  let hup ← h.libcU32 "EPOLLHUP"
  let err ← h.libcU32 "EPOLLERR"
  return (input,output,rd,hup,err)

def fromFlags (h : Hooks S F I) (flags : UInt32) : M S Files.Readiness := do
  let (input,output,rd,hup,err) ← constants h
  return ⟨flags &&& input == input,flags &&& output == output,flags &&& rd == rd,
    flags &&& hup == hup,flags &&& err == err⟩

def toFlags (h : Hooks S F I) (ready : Files.Readiness) : M S UInt32 := do
  let (input,output,rd,hup,err) ← constants h
  let mut flags := 0
  if ready.readable then flags := flags ||| input
  if ready.writable then flags := flags ||| output
  if ready.readClosed then flags := flags ||| rd
  if ready.writeClosed then flags := flags ||| hup
  if ready.error then flags := flags ||| err
  return flags

def control (budget : Nat) (h : Hooks S F I) (epfd op fd event : OpTy Provenance) : M S Int32 := do
  let epfd ← h.poll.readI32 epfd
  let op ← h.poll.readI32 op
  let fd ← h.poll.readI32 fd
  -- Source dereferences even DEL, before all constant/FD checks.
  let event ← h.derefEvent event
  let add ← h.libcI32 "EPOLL_CTL_ADD"
  let modify ← h.libcI32 "EPOLL_CTL_MOD"
  let delete ← h.libcI32 "EPOLL_CTL_DEL"
  let input ← h.libcU32 "EPOLLIN"
  let output ← h.libcU32 "EPOLLOUT"
  let rd ← h.libcU32 "EPOLLRDHUP"
  let edge ← h.libcU32 "EPOLLET"
  let hup ← h.libcU32 "EPOLLHUP"
  let err ← h.libcU32 "EPOLLERR"
  if epfd == fd then return ← failure h "EFAULT"
  let some epoll ← h.poll.lookupFd epfd | return ← failure h "EBADF"
  Files.withDrop (do
    let some watcher ← h.asEpoll epoll | throw (.unsupported "non-epoll FD passed to epoll_ctl")
    let some target ← h.poll.lookupFd fd | return ← failure h "EBADF"
    Files.withDrop (do
      let key : Readiness.Key := ⟨h.poll.readiness.id target,fd⟩
      if op == add || op == modify then
        let original ← h.readU32 (← h.indexedField event 0)
        let data ← h.readU64 (← h.indexedField event 1)
        let isEdge := original &&& edge == edge
        let mut flags := if isEdge then original &&& ~~~edge else original
        let relevant := flags ||| hup ||| err
        for bit in #[input,output,rd,hup,err] do
          if flags &&& bit == bit then flags := flags &&& ~~~bit
        if flags != 0 then throw (.unsupported "epoll_ctl: unsupported event flags")
        let relevant ← fromFlags h relevant
        if op == add then
          if !(← Readiness.addInterest budget h.poll.readiness watcher fd relevant isEdge data) then
            return ← failure h "EEXIST"
        else
          if !(← Readiness.updateInterest budget h.poll.readiness watcher key fun interest =>
              { interest with edgeTriggered := isEdge, relevant := relevant, data := data }) then
            return ← failure h "ENOENT"
      else if op == delete then
        if !(← Readiness.removeInterest h.poll.readiness watcher key) then return ← failure h "ENOENT"
      else throw (.unsupported "unsupported epoll_ctl operation")
      return 0
    ) (h.poll.readiness.dropFd target)
  ) (h.poll.readiness.dropFd epoll)

def returnReady (budget : Nat) (h : Hooks S F I) (watcher : Nat)
    (dest events : MPlaceTy Provenance) : M S Int32 := do
  let mut iter ← h.poll.arrayFields events
  let length ← h.arrayLength events
  let ready ← Readiness.getReadyInterests budget length h.poll.readiness watcher
  let mut count : Int32 := 0
  for interest in ready do
    let some (slot,next) ← h.poll.nextField iter | throw (.invalidProgram "epoll: insufficient event slots")
    iter := next
    h.writeEvent slot (← toFlags h interest.active) interest.data
    if count == 2147483647 then throw (.invalidProgram "epoll: event count strict_add overflow")
    count := count + 1
  h.writeI32 count dest
  return count

def wait (budget : Nat) (h : Hooks S F I) (epfd events maxevents timeout : OpTy Provenance)
    (dest : MPlaceTy Provenance) : M S Unit := do
  let epfd ← h.poll.readI32 epfd
  let events ← h.readImmediate events
  let maxevents ← h.poll.readI32 maxevents
  let timeout ← h.poll.readI32 timeout
  if epfd <= 0 || maxevents <= 0 then
    h.writeI32 (← failure h "EINVAL") dest
    return
  let events ← h.poll.derefArray events "epoll_event" maxevents.toUInt32.toUInt64
  let some epoll ← h.poll.lookupFd epfd | h.writeI32 (← failure h "EBADF") dest; return
  let pending : Option (Nat × Option ThreadDeadline) ← PollShims.onError (do
    let some watcher ← h.asEpoll epoll | h.writeI32 (← failure h "EBADF") dest; return none
    let immediate : Bool ← if timeout == 0 then pure true else do pure ((← Readiness.readyCount h.poll.readiness watcher) != 0)
    if immediate then
      let _ ← returnReady budget h watcher dest events
      return none
    let deadline ← if timeout >= 0 then (h.poll.deadlineMillis timeout.toUInt32).map some
      else if timeout == -1 then pure none
      else throw (.unsupported "epoll_wait: only timeout values >= -1 supported")
    Readiness.addBlockedThread h.poll.readiness watcher (← h.poll.readiness.runtime.threads).activeThread
    pure (some (watcher,deadline))
  ) (h.poll.readiness.dropFd epoll)
  match pending with
  | none => h.poll.readiness.dropFd epoll
  | some (watcher,deadline) =>
    match h.deferred with
    | .typed block => block epoll events dest deadline
    | .legacy => PollShims.onError (PollShims.block h.poll.readiness deadline fun reason => Files.withDrop (do
        match reason with
        | .Ready =>
          let count ← returnReady budget h watcher dest events
          if count <= 0 then throw (.invalidProgram "epoll: woken with no events to deliver")
        | .TimedOut =>
          Readiness.removeBlockedThread h.poll.readiness watcher (← h.poll.readiness.runtime.threads).activeThread
          h.writeI32 0 dest
      ) (h.poll.readiness.dropFd epoll)) (h.poll.readiness.dropFd epoll)
end Miri.Interpreter.EpollShims
