import Miri.Interpreter.Readiness
import Miri.Interpreter.Clock

/-! Entire pinned concurrency/blocking_io.rs. Host mio Source/Poll and events
remain real stateful effects; all event ordering, weak ownership, readiness and
callback policy is implemented here. -/
namespace Miri.Interpreter.BlockingIo
open Miri.Memory Miri.Concurrency Files
abbrev M := EStateM StepError
inductive Interest where | read | write | readWrite deriving DecidableEq, Repr

def Interest.fulfilled (interest : Interest) (ready : Files.Readiness) : Bool :=
  match interest with
  | .read => ready.readable || ready.error
  | .write => ready.writable || ready.error
  | .readWrite => ready.readable || ready.writable || ready.error
structure Source where
  fd : Files.WeakRef
  blocked : Array (ThreadId × Interest) := #[]
structure Manager (Poll : Type) where
  poll : Option Poll
  sources : Array (FdId × Source) := #[]
structure Event where
  token : FdId
  ready : Files.Readiness
structure Hooks (S F Poll Host : Type) where
  readiness : Readiness.Hooks S F
  get : M S (Manager Poll)
  put : Manager Poll → M S Unit
  newPoll : M S (Except (IoError.HostError Host) Poll)
  dropPoll : Poll → M S Unit
  registerHostSource : Poll → F → FdId → Interest → M S (Except (IoError.HostError Host) Unit)
  pollHost : Poll → Option Clock.Duration → Nat → M S (Except (IoError.HostError Host) (Array Event))
  sourceReadiness : F → M S Files.Readiness
  setSourceReadiness : F → Files.Readiness → M S Unit
  cloneFd : F → M S F
private def source (state : Manager P) (id : FdId) : Except StepError Source :=
  match state.sources.find? (·.1 == id) with
  | some (_,source) => .ok source
  | none => .error (.invalidProgram "blocking IO source should be registered")
private def lift (r : Except StepError A) : M S A :=
  match r with | .ok value => pure value | .error error => throw error

def newManager (h : Hooks S F P H) (communicate : Bool) : M S (Except (IoError.HostError H) (Manager P)) := do
  -- Rust then_some evaluates Poll::new()? eagerly, even if communicate=false.
  match ← h.newPoll with
  | .error error => return .error error
  | .ok poll =>
    if !communicate then h.dropPoll poll
    return .ok ⟨if communicate then some poll else none,#[]⟩

def register (h : Hooks S F P H) (fd : F) : M S Unit := do
  Files.withDrop (do
    let state ← h.get
    let some poll := state.poll | throw (.invalidProgram "blocking IO called with isolation enabled")
    let id := h.readiness.id fd
    if let .error _ ← h.registerHostSource poll fd id .readWrite then
      throw (.invalidProgram "fatal host IO source registration error")
    let state ← h.get
    if state.sources.any (·.1 == id) then throw (.invalidProgram "source already registered")
    h.put { state with sources := state.sources.push (id,⟨h.readiness.downgrade fd,#[]⟩) }
  ) (h.readiness.dropFd fd)

def addBlockedThread (h : Hooks S F P H) (id : FdId) (thread : ThreadId) (interest : Interest) : M S Unit := do
  let state ← h.get
  let current ← lift (source state id)
  if current.blocked.any (·.1 == thread) then throw (.invalidProgram "thread blocked multiple times on IO source")
  let next := { current with blocked := current.blocked.push (thread,interest) }
  h.put { state with sources := state.sources.map fun (old,value) => (old,if old == id then next else value) }

def removeBlockedThread (h : Hooks S F P H) (id : FdId) (thread : ThreadId) : M S Unit := do
  let state ← h.get
  let current ← lift (source state id)
  if !(current.blocked.any (·.1 == thread)) then throw (.invalidProgram "thread should be blocked on IO source")
  let next := { current with blocked := current.blocked.filter (·.1 != thread) }
  h.put { state with sources := state.sources.map fun (old,value) => (old,if old == id then next else value) }

def runGc (h : Hooks S F P H) : M S Unit := do
  let state ← h.get
  let mut live := #[]
  for entry in state.sources do
    if !(← h.readiness.isClosed entry.2.fd) then live := live.push entry
  h.put { state with sources := live }

def blockThreadForIo (h : Hooks S F P H) (fd : F) (interest : Interest)
    (deadline : Option ThreadDeadline) (callback : SyncRuntime.Callback S) : M S Unit := do
  Files.withDrop (do
    let runtime := h.readiness.runtime
    addBlockedThread h (h.readiness.id fd) (← runtime.threads).activeThread interest
    if interest.fulfilled (← h.sourceReadiness fd) then callback .Ready
    else
      let (registry,token) := (← runtime.callbacks).register callback
      runtime.putCallbacks registry
      match (← runtime.threads).blockThreadWithRuntimeConstraints .IO deadline token runtime.communicate with
      | .error error =>
        SyncRuntime.cancelCallback runtime token
        throw (runtime.error (.blockThreadSource error))
      | .ok threads => runtime.putThreads threads
  ) (h.readiness.dropFd fd)

/-- All event-source readiness bits are OR-ed before any readiness or IO
callbacks execute, matching the source collect::<Vec<_>>() first phase. -/
def poll (budget : Nat) (h : Hooks S F P H) (timeout : Option Clock.Duration) :
    M S (Except (IoError.HostError H) Unit) := do
  let some poll := (← h.get).poll | throw (.invalidProgram "blocking IO called with isolation enabled")
  let events ← h.pollHost poll timeout 16
  let .ok events := events | return events.map (fun _ => ())
  let fds ← Readiness.collectOwned events (fun event => do
    let current ← lift (source (← h.get) event.token)
    let some fd ← h.readiness.upgrade current.fd
      | throw (.invalidProgram "readiness event for closed source description")
    -- Returned strong ref is held until its source processing iteration.
    if h.readiness.id fd != event.token then
      h.readiness.dropFd fd
      throw (.invalidProgram "host event token/FD identity mismatch")
    h.setSourceReadiness fd (Readiness.Bits.union (← h.sourceReadiness fd) event.ready)
    return fd) h.readiness.dropFd
  Readiness.consumeOwned fds.toList (fun fd => do
    Readiness.updateFd budget h.readiness (← h.cloneFd fd) { noReleaseClock := true }
    let current ← lift (source (← h.get) (h.readiness.id fd))
    let mut threads := #[]
    for (thread,interest) in current.blocked.qsort (fun a b => a.1.toNat < b.1.toNat) do
      if interest.fulfilled (← h.sourceReadiness fd) then threads := threads.push thread
    for thread in threads do h.readiness.unblock thread .IO) h.readiness.dropFd
  return .ok ()

def pollAndUnblock (budget : Nat) (h : Hooks S F P H) (timeout : Option Clock.Duration) : M S Unit := do
  match ← poll budget h timeout with
  | .ok _ => pure ()
  | .error error =>
    if error.kind != .Interrupted then throw (.invalidProgram "unexpected error while polling")

def anyThreadBlockedOnHost (h : Hooks S F P H) : M S Bool := do
  let sources := (← h.get).sources.qsort (fun a b => a.1.value < b.1.value)
  for (_,current) in sources do
    if !current.blocked.isEmpty then return true
    if let some fd ← h.readiness.upgrade current.fd then
      let found ← Files.withDrop (do
        if !h.readiness.supportsWatching fd then return false
        Readiness.hasWatcherWithBlockedThread h.readiness fd) (h.readiness.dropFd fd)
      if found then return true
  return false
end Miri.Interpreter.BlockingIo
