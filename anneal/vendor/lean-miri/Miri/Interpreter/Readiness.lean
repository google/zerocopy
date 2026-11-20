import Miri.Interpreter.Files
import Miri.Concurrency.SyncRuntime

/-! Complete state/control policy of pinned shims/readiness.rs. Watcher IDs and
FD weak refs are ownership identities, not readiness tokens or success claims. -/
namespace Miri.Interpreter.Readiness
open Miri.ABI Miri.Memory Miri.Concurrency Files
abbrev M := EStateM StepError
abbrev Bits := Files.Readiness

def Bits.empty : Bits := {}
def Bits.inter (a b : Bits) : Bits :=
  ⟨a.readable && b.readable,a.writable && b.writable,a.readClosed && b.readClosed,a.writeClosed && b.writeClosed,a.error && b.error⟩
def Bits.union (a b : Bits) : Bits :=
  ⟨a.readable || b.readable,a.writable || b.writable,a.readClosed || b.readClosed,a.writeClosed || b.writeClosed,a.error || b.error⟩
structure Key where
  id : FdId
  number : Int32
  deriving DecidableEq
private def keyLt (a b : Key) : Bool := a.id.value < b.id.value || (a.id == b.id && a.number < b.number)
structure Interest where
  fd : Files.WeakRef
  relevant : Bits
  edgeTriggered : Bool
  data : UInt64
  active : Bits := Bits.empty
structure Watcher where
  interests : Array (Key × Interest) := #[]
  ready : Array Key := #[]
  queue : Array ThreadId := #[]
structure Watched where
  /-- Weak watcher identities, in source insertion order. -/
  watchers : Array Nat := #[]
  clock : VClock := .default
structure Flags where
  forceEdge : Bool := false
  noReleaseClock : Bool := false
structure Hooks (S F : Type) where
  runtime : SyncRuntime.Hooks S Nat Int32 (MPlaceTy Provenance)
  debugAssertions : Bool
  getWatcher : Nat → M S Watcher
  putWatcher : Nat → Watcher → M S Unit
  upgradeWatcher : Nat → M S Bool
  dropWatcher : Nat → M S Unit
  watcherAlive : Nat → M S Bool
  getFd : Int32 → M S F
  id : F → FdId
  downgrade : F → Files.WeakRef
  upgrade : Files.WeakRef → M S (Option F)
  dropFd : F → M S Unit
  isClosed : Files.WeakRef → M S Bool
  supportsWatching : F → Bool
  getWatched : F → M S Watched
  putWatched : F → Watched → M S Unit
  readiness : F → M S Bits
  delayed : M S (Array F)
  putDelayed : Array F → M S Unit
  /-- Must enable/swap the full target thread view, execute its typed callback,
  and restore only on success. No callback token acknowledgment is accepted. -/
  unblock : ThreadId → BlockReason → M S Unit
private def onError (action : M S A) (cleanup : M S Unit) : M S A := fun state =>
  match action state with
  | .ok value state => .ok value state
  | .error error state =>
    match cleanup state with | .ok _ state => .error error state | .error next state => .error next state

/-- Vec-style ownership: retain all during collection, then drop each consumed
item after its iteration, and drop unconsumed items if an iteration fails. -/
def consumeOwned (items : List A) (action : A → M S Unit) (drop : A → M S Unit) : M S Unit := do
  match items with
  | [] => pure ()
  | item :: rest =>
    onError (Files.withDrop (action item) (drop item)) (do for item in rest do drop item)
    consumeOwned rest action drop

def collectOwned (items : Array A) (acquire : A → M S B) (drop : B → M S Unit) : M S (Array B) := do
  let mut result := #[]
  for item in items do
    let value ← onError (acquire item) (do for previous in result do drop previous)
    result := result.push value
  return result
private def sameId (key : Key) (id : FdId) : Bool := key.id == id && key.number >= 0
private def getInterest (watcher : Watcher) (key : Key) : Except StepError Interest :=
  match watcher.interests.find? (·.1 == key) with
  | some (_,interest) => .ok interest
  | none => .error (.invalidProgram "readiness interest key missing")
private def lift (r : Except StepError A) : M S A :=
  match r with | .ok value => pure value | .error error => throw error
private def acquire (h : Hooks S F) (clock : VClock) : M S Unit := do
  match h.runtime.handler with
  | .none => pure ()
  | .vectorClocks =>
    match SyncClockState.acquire (← h.runtime.global) (← h.runtime.threads) clock with
    | .error error => throw (h.runtime.error (SyncError.ofClock error))
    | .ok global => h.runtime.putGlobal global
private def releaseJoin (h : Hooks S F) (fd : F) : M S Unit := do
  match h.runtime.handler with
  | .none => pure ()
  | .vectorClocks =>
    match SyncClockState.prepareRelease (← h.runtime.global) (← h.runtime.threads) with
    | .error error => throw (h.runtime.error (SyncError.ofClock error))
    | .ok (snapshot,finish) =>
      let watched ← h.getWatched fd
      h.putWatched fd {watched with clock := watched.clock.join snapshot}
      match finish with
      | .error error => throw (h.runtime.error (SyncError.ofClock error))
      | .ok global => h.runtime.putGlobal global

def readyCount (h : Hooks S F) (watcher : Nat) : M S Nat := do
  return (← h.getWatcher watcher).ready.size

def addBlockedThread (h : Hooks S F) (watcher : Nat) (thread : ThreadId) : M S Unit := do
  let state ← h.getWatcher watcher
  h.putWatcher watcher { state with queue := state.queue.push thread }
def removeBlockedThread (h : Hooks S F) (watcher : Nat) (thread : ThreadId) : M S Unit := do
  let state ← h.getWatcher watcher
  h.putWatcher watcher { state with queue := state.queue.filter (· != thread) }

def wakeReady (budget : Nat) (h : Hooks S F) (watcher : Nat) : M S Unit := do
  let state ← h.getWatcher watcher
  if state.ready.isEmpty || state.queue.isEmpty then return
  match budget with
  | 0 => throw (.resourceExhaustion "readiness wake callback budget exhausted")
  | budget + 1 =>
    let some thread := state.queue[0]? | throw (.invalidProgram "readiness queue head missing")
    h.putWatcher watcher { state with queue := state.queue.extract 1 state.queue.size }
    h.unblock thread .Readiness
    wakeReady budget h watcher

def updateReadiness (budget : Nat) (h : Hooks S F) (watcher : Nat)
    (active : Bits) (forceEdge : Bool) (keys : Array Key) : M S Unit := do
  for key in keys do
    let state ← h.getWatcher watcher
    let interest ← lift (getInterest state key)
    let next := Bits.inter interest.relevant active
    let interests := state.interests.map fun (old,value) =>
      (old,if old == key then { value with active := next } else value)
    let ready := if next == Bits.empty then state.ready.filter (· != key)
      else if forceEdge || next != Bits.inter interest.active next then
        if state.ready.contains key then state.ready else state.ready.push key
      else state.ready
    h.putWatcher watcher { state with interests := interests, ready := ready }
  wakeReady budget h watcher

private def addWatched (h : Hooks S F) (fd : F) (watcher : Nat) : M S Unit := do
  let state ← h.getWatched fd
  if h.debugAssertions && state.watchers.contains watcher then throw (.invalidProgram "watcher already registered on FD")
  h.putWatched fd { state with watchers := state.watchers.push watcher }
private def removeWatched (h : Hooks S F) (fd : F) (watcher : Nat) : M S Unit := do
  let state ← h.getWatched fd
  let some index := state.watchers.findIdx? (· == watcher) | throw (.invalidProgram "watcher has no registered FD interest")
  h.putWatched fd { state with watchers := state.watchers.extract 0 index ++ state.watchers.extract (index+1) state.watchers.size }

def addInterest (budget : Nat) (h : Hooks S F) (watcher : Nat) (number : Int32)
    (relevant : Bits) (edge : Bool) (data : UInt64) : M S Bool := do
  let fd ← h.getFd number
  Files.withDrop (do
    let key := Key.mk (h.id fd) number
    let interest : Interest := ⟨h.downgrade fd,relevant,edge,data,Bits.empty⟩
    let state ← h.getWatcher watcher
    if !(state.interests.any (fun (key,_) => sameId key (h.id fd))) then
      if !h.supportsWatching fd then throw (.unsupported "I/O readiness watching unsupported for FD type")
      addWatched h fd watcher
    let state ← h.getWatcher watcher
    if state.interests.any (·.1 == key) then return false
    h.putWatcher watcher { state with interests := state.interests.push (key,interest) }
    updateReadiness budget h watcher (← h.readiness fd) true #[key]
    return true) (h.dropFd fd)

def updateInterest (budget : Nat) (h : Hooks S F) (watcher : Nat) (key : Key)
    (change : Interest → Interest) : M S Bool := do
  let state ← h.getWatcher watcher
  let some (_,interest) := state.interests.find? (·.1 == key) | return false
  h.putWatcher watcher { state with interests := state.interests.map fun (old,value) =>
    (old,if old == key then change interest else value) }
  let fd ← h.getFd key.number
  Files.withDrop (updateReadiness budget h watcher (← h.readiness fd) true #[key]) (h.dropFd fd)
  return true

def removeInterest (h : Hooks S F) (watcher : Nat) (key : Key) : M S Bool := do
  let state ← h.getWatcher watcher
  let some (_,interest) := state.interests.find? (·.1 == key) | return false
  h.putWatcher watcher { state with interests := state.interests.filter (·.1 != key) }
  let some fd ← h.upgrade interest.fd | throw (.invalidProgram "dead watched FD")
  Files.withDrop (do
    let state ← h.getWatcher watcher
    h.putWatcher watcher { state with ready := state.ready.filter (· != key) }
    let state ← h.getWatcher watcher
    if !(state.interests.any (fun (candidate,_) => sameId candidate key.id)) then
      if !h.supportsWatching fd then return false
      removeWatched h fd watcher
    return true) (h.dropFd fd)

def updateFd (budget : Nat) (h : Hooks S F) (fd : F) (flags : Flags) : M S Unit :=
  Files.withDrop (do
    if !h.supportsWatching fd then throw (.invalidProgram "update_fd_readiness requires watched FD")
    if !flags.noReleaseClock then releaseJoin h fd
    let weak := (← h.getWatched fd).watchers
    let strong ← collectOwned weak (fun watcher => do
      if !(← h.upgradeWatcher watcher) then throw (.invalidProgram "dead readiness watcher")
      return watcher) h.dropWatcher
    if strong.isEmpty then return
    let active ← onError (h.readiness fd) (do for watcher in strong do h.dropWatcher watcher)
    consumeOwned strong.toList (fun watcher => do
      let state ← h.getWatcher watcher
      let keys := (state.interests.qsort (fun a b => keyLt a.1 b.1)).filter (fun (key,_) => sameId key (h.id fd)) |>.map (·.1)
      updateReadiness budget h watcher active flags.forceEdge keys) h.dropWatcher) (h.dropFd fd)

def addDelayed (h : Hooks S F) (fd : F) : M S Unit := do h.putDelayed ((← h.delayed).push fd)
def processDelayed (budget : Nat) (h : Hooks S F) : M S Unit := do
  let queue ← h.delayed
  if queue.isEmpty then return
  match budget with
  | 0 => throw (.resourceExhaustion "delayed readiness update budget exhausted")
  | budget + 1 =>
    let some fd := queue[queue.size - 1]? | throw (.invalidProgram "delayed readiness stack missing element")
    h.putDelayed (queue.extract 0 (queue.size - 1))
    updateFd budget h fd {}
    processDelayed budget h

private def collectReady (remaining : Nat) (h : Hooks S F) (watcher : Nat)
    (result : Array Interest) (readd : Array Key) : M S (Array Interest) := do
  let state ← h.getWatcher watcher
  if remaining == 0 || state.ready.isEmpty then
    h.putWatcher watcher { state with ready := state.ready ++ readd }
    return result
  match remaining with
  | 0 => throw (.invalidProgram "ready collection bound invariant")
  | remaining + 1 =>
    let some key := state.ready[0]? | throw (.invalidProgram "ready key missing")
    h.putWatcher watcher { state with ready := state.ready.extract 1 state.ready.size }
    let interest ← lift (getInterest state key)
    let some fd ← h.upgrade interest.fd | throw (.invalidProgram "dead watched FD")
    Files.withDrop (acquire h (← h.getWatched fd).clock) (h.dropFd fd)
    collectReady remaining h watcher (result.push interest) (if interest.edgeTriggered then readd else readd.push key)

def getReadyInterests (budget max : Nat) (h : Hooks S F) (watcher : Nat) : M S (Array Interest) := do
  processDelayed budget h
  if h.debugAssertions then
    let state ← h.getWatcher watcher
    for (_,interest) in state.interests.qsort (fun a b => keyLt a.1 b.1) do
      let some fd ← h.upgrade interest.fd | throw (.invalidProgram "dead watched FD")
      Files.withDrop (do
        if interest.active != Bits.inter (← h.readiness fd) interest.relevant then
          throw (.invalidProgram "stale readiness interest active flags")) (h.dropFd fd)
  collectReady max h watcher #[] #[]

def hasWatcherWithBlockedThread (h : Hooks S F) (fd : F) : M S Bool := do
  let state ← h.getWatched fd
  for watcher in state.watchers do
    if !(← h.upgradeWatcher watcher) then throw (.invalidProgram "dead readiness watcher")
    let blocked ← Files.withDrop
      ((h.getWatcher watcher).map fun state => !state.queue.isEmpty) (h.dropWatcher watcher)
    if blocked then return true
  return false

def removeFileNumInterests (h : Hooks S F) (fd : F) (number : Int32) : M S Unit := do
  let watchers := (← h.getWatched fd).watchers
  for watcher in watchers do
    if !(← h.upgradeWatcher watcher) then throw (.invalidProgram "dead readiness watcher")
    Files.withDrop (do let _ ← removeInterest h watcher ⟨h.id fd,number⟩) (h.dropWatcher watcher)

/-- Called after the watcher loses its last strong reference. Payload remains
available to this destructor, while watcherAlive must already report false. -/
def dropWatcherMetadata (h : Hooks S F) (state : Watcher) : M S Unit := do
  let mut previous : Option FdId := none
  for (key,interest) in state.interests.qsort (fun a b => keyLt a.1 b.1) do
    if previous != some key.id then
      previous := some key.id
      if let some fd ← h.upgrade interest.fd then
        Files.withDrop (do
          let watched ← h.getWatched fd
          let mut live := #[]
          for watcher in watched.watchers do
            if ← h.watcherAlive watcher then live := live.push watcher
          h.putWatched fd { watched with watchers := live }) (h.dropFd fd)

/-- Last FD description drop removes all dead FD interests from live watchers,
not merely the descriptor number that happened to close last. -/
def dropWatchedMetadata (h : Hooks S F) (watched : Watched) : M S Unit := do
  for watcher in watched.watchers do
    if ← h.upgradeWatcher watcher then
      Files.withDrop (do
        let interests := (← h.getWatcher watcher).interests.qsort (fun a b => keyLt a.1 b.1)
        for (key,interest) in interests do
          if ← h.isClosed interest.fd then
            let state ← h.getWatcher watcher
            h.putWatcher watcher { state with
              interests := state.interests.filter (·.1 != key)
              ready := state.ready.filter (· != key) }) (h.dropWatcher watcher)
end Miri.Interpreter.Readiness
