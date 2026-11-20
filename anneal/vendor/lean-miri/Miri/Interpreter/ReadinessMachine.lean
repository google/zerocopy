import Miri.Interpreter.Readiness
import Miri.Interpreter.BlockingIo
import Miri.Interpreter.FileMachine
import Miri.Interpreter.ThreadStacks
import Miri.Interpreter.UnixFdDispatch

/-! Authoritative readiness state embedded in the existing canonical machine
User, sharing actual FileOwnership references and complete thread-stack views. -/
namespace Miri.Interpreter.ReadinessMachine
open Miri.Memory Miri.Concurrency Files
structure WatcherEntry where
  id : Nat
  strong : Nat
  value : Readiness.Watcher
structure Registry (F : Type) where
  nextWatcher : Nat := 0
  watchers : Array WatcherEntry := #[]
  watched : Array (FdId × Readiness.Watched) := #[]
  delayed : Array F := #[]
structure Hooks (K U H D O : Type) where
  files : FileMachine.Hooks K U H D O
  registry : U → Registry (Files.Ref (Description H D O))
  setRegistry : Registry (Files.Ref (Description H D O)) → U → U
  watcherReferenceBudget : Nat
  /-- Actual description destructor with ID retained. It must run watched-field
  cleanup at that source type's field-drop point, then actual host/resource
  destruction; separate FD types may have additional delayed updates. -/
  onLastDrop : Files.Ref (Description H D O) → MachineHooks.M K U Unit
private def lift (r : Except StepError A) : MachineHooks.M K U A :=
  match r with | .ok value => pure value | .error error => throw error
private def getRegistry (h : Hooks K U H D O) : MachineHooks.M K U (Registry (Files.Ref (Description H D O))) := do
  return h.registry (← get).machine.user
private def putRegistry (h : Hooks K U H D O) (value : Registry (Files.Ref (Description H D O))) : MachineHooks.M K U Unit :=
  modify fun state => { state with machine := { state.machine with user := h.setRegistry value state.machine.user } }
private def findWatcher (state : Registry F) (id : Nat) : Except StepError WatcherEntry := do
  let entries := state.watchers.filter (·.id == id)
  if entries.size != 1 then throw (.invalidProgram "readiness watcher missing/ambiguous")
  let some entry := entries[0]? | throw (.invalidProgram "readiness watcher lookup failed")
  if entry.strong == 0 then throw (.invalidProgram "closed readiness watcher")
  return entry

def newWatcher (h : Hooks K U H D O) : MachineHooks.M K U Nat := do
  let state ← getRegistry h
  if state.watchers.any (·.id == state.nextWatcher) then throw (.invalidProgram "readiness watcher ID collision")
  putRegistry h { state with nextWatcher := state.nextWatcher + 1, watchers := state.watchers.push ⟨state.nextWatcher,1,{}⟩ }
  return state.nextWatcher

def upgradeWatcher (h : Hooks K U H D O) (id : Nat) : MachineHooks.M K U Bool := do
  let state ← getRegistry h
  if !(state.watchers.any (fun entry => entry.id == id && entry.strong > 0)) then return false
  let entry ← lift (findWatcher state id)
  if entry.strong + 1 > h.watcherReferenceBudget then throw (.resourceExhaustion "readiness watcher reference budget")
  putRegistry h { state with watchers := state.watchers.map fun old =>
    if old.id == id then { old with strong := old.strong + 1 } else old }
  return true

/-- ID-aware release for source ReadinessWatched::drop. Weak liveness is
updated first, so the destructor sees this description as closed. -/
def dropFd (h : Hooks K U H D O) (ref : Files.Ref (Description H D O)) : MachineHooks.M K U Unit := do
  let (ownership,last) ← lift (FileOwnership.release (h.files.ownership (← get).machine.user) ref.id)
  modify fun state => { state with machine := { state.machine with user := h.files.setOwnership ownership state.machine.user } }
  if last.isSome then
    h.onLastDrop ref
    let state ← getRegistry h
    putRegistry h { state with watched := state.watched.filter (·.1 != ref.id) }

private def views (h : Hooks K U H D O)
    (base : Readiness.Hooks (MachineHooks.State K U) (Files.Ref (Description H D O))) :
    Readiness.Hooks (MachineHooks.State K U) (Files.Ref (Description H D O)) := {
  base with
  getWatcher := fun id => do return (← lift (findWatcher (← getRegistry h) id)).value
  putWatcher := fun id value => do
    let state ← getRegistry h
    let _ ← lift (findWatcher state id)
    putRegistry h { state with watchers := state.watchers.map fun old => if old.id == id then { old with value := value } else old }
  upgradeWatcher := upgradeWatcher h
  watcherAlive := fun id => do return (← getRegistry h).watchers.any (fun entry => entry.id == id && entry.strong > 0)
  getFd := fun number => do
    let some ref := (h.files.table (← get).machine.user).get number
      | throw (.invalidProgram "readiness file description should exist")
    FileMachine.cloneReference h.files ref
  id := Files.Ref.id
  downgrade := FileOwnership.downgrade
  upgrade := FileMachine.upgradeWeak h.files
  dropFd := dropFd h
  isClosed := fun weak => do return FileOwnership.isClosed (h.files.ownership (← get).machine.user) weak
  getWatched := fun ref => do
    let matching := (← getRegistry h).watched.filter (·.1 == ref.id)
    if matching.size != 1 then throw (.invalidProgram "missing/ambiguous watched FD metadata")
    let some (_,value) := matching[0]? | throw (.invalidProgram "watched FD lookup failed")
    return value
  putWatched := fun ref value => do
    let state ← getRegistry h
    if !(state.watched.any (·.1 == ref.id)) then throw (.invalidProgram "missing watched FD metadata")
    putRegistry h { state with watched := state.watched.map fun (id,old) => (id,if id == ref.id then value else old) }
  delayed := do return (← getRegistry h).delayed
  putDelayed := fun delayed => do
    let state ← getRegistry h
    putRegistry h { state with delayed := delayed } }

def dropWatcher (h : Hooks K U H D O)
    (base : Readiness.Hooks (MachineHooks.State K U) (Files.Ref (Description H D O)))
    (id : Nat) : MachineHooks.M K U Unit := do
  let state ← getRegistry h
  let entry ← lift (findWatcher state id)
  if entry.strong == 1 then
    putRegistry h { state with watchers := state.watchers.filter (·.id != id) }
    Readiness.dropWatcherMetadata (views h base) entry.value
  else
    putRegistry h { state with watchers := state.watchers.map fun old => if old.id == id then { old with strong := old.strong - 1 } else old }

def bind (h : Hooks K U H D O)
    (base : Readiness.Hooks (MachineHooks.State K U) (Files.Ref (Description H D O))) :
    Readiness.Hooks (MachineHooks.State K U) (Files.Ref (Description H D O)) := {
  (views h base) with dropWatcher := dropWatcher h base }

/-- Called when a description containing ReadinessWatched is constructed.
Absent metadata is never silently treated as an empty, valid watch set. -/
def initWatched (h : Hooks K U H D O) (ref : Files.Ref (Description H D O)) : MachineHooks.M K U Unit := do
  let state ← getRegistry h
  if state.watched.any (·.1 == ref.id) then throw (.invalidProgram "watched FD metadata already initialized")
  putRegistry h { state with watched := state.watched.push (ref.id,{}) }

/-- The true source ThreadStacks switch wraps actual typed callback execution;
SyncRuntime's token registry is not used as a successful acknowledgment. -/
def bindThreadStacks
    (base : Readiness.Hooks (ThreadStacks.State K U) F) : Readiness.Hooks (ThreadStacks.State K U) F := {
  base with unblock := fun thread reason =>
    ThreadStacks.unblockThread thread reason fun token kind => do
      SyncRuntime.runCallback base.runtime token kind }
structure BlockingStore (U Poll : Type) where
  get : U → BlockingIo.Manager Poll
  put : BlockingIo.Manager Poll → U → U

def bindBlocking (h : Hooks K U H D O) (store : BlockingStore U Poll)
    (base : BlockingIo.Hooks (MachineHooks.State K U) (Files.Ref (Description H D O)) Poll Host) :
    BlockingIo.Hooks (MachineHooks.State K U) (Files.Ref (Description H D O)) Poll Host := {
  base with
  readiness := bind h base.readiness
  get := do return store.get (← get).machine.user
  put := fun manager => modify fun state =>
    { state with machine := { state.machine with user := store.put manager state.machine.user } }
  cloneFd := FileMachine.cloneReference h.files }

def bindBlockingThreadStacks (base : BlockingIo.Hooks (ThreadStacks.State K U) F Poll Host) :
    BlockingIo.Hooks (ThreadStacks.State K U) F Poll Host := {
  base with readiness := bindThreadStacks base.readiness }

def bindScheduling (budget : Nat) (io : BlockingIo.Hooks (ThreadStacks.State K U) F Poll Host)
    (base : ThreadStacks.LocalSchedulerHooks K U) : ThreadStacks.LocalSchedulerHooks K U := {
  base with
  processDelayedReadiness := Readiness.processDelayed budget io.readiness
  pollHostIoNonBlocking := BlockingIo.pollAndUnblock budget io (some ⟨0,0,by decide⟩)
  anyThreadBlockedOnHost := BlockingIo.anyThreadBlockedOnHost io }
/-- Call at the actual ReadinessWatched field-drop point of a description.
The ID-aware outer release has already made weak FD upgrades fail. -/
def destroyWatched (h : Hooks K U H D O)
    (base : Readiness.Hooks (MachineHooks.State K U) (Files.Ref (Description H D O)))
    (ref : Files.Ref (Description H D O)) : MachineHooks.M K U Unit := do
  let entries := (← getRegistry h).watched.filter (·.1 == ref.id)
  if entries.size != 1 then throw (.invalidProgram "missing/ambiguous destroyed watched FD metadata")
  let some (_,watched) := entries[0]? | throw (.invalidProgram "destroyed watched FD lookup failed")
  Readiness.dropWatchedMetadata (bind h base) watched

def cloneWatcher (h : Hooks K U H D O) (id : Nat) : MachineHooks.M K U Unit := do
  if !(← upgradeWatcher h id) then throw (.invalidProgram "cloning closed readiness watcher")

def newFd (h : Hooks K U H D O) (supportsWatching : Description H D O → Bool)
    (description : Description H D O) : MachineHooks.M K U (Files.Ref (Description H D O)) := do
  let ref ← FileMachine.newReference h.files description
  if supportsWatching description then initWatched h ref
  return ref

def bindFiles (h : Hooks K U H D O)
    (readiness : Readiness.Hooks (MachineHooks.State K U) (Files.Ref (Description H D O)))
    (base : UnixFd.Hooks (MachineHooks.State K U) H D O E Meta) :
    UnixFd.Hooks (MachineHooks.State K U) H D O E Meta := {
  (FileMachine.bind h.files base) with
  newReference := newFd h (Files.hasReadinessWatched base.files)
  dropRef := dropFd h
  removeFileNumInterests := fun fd number => Readiness.removeFileNumInterests (bind h readiness) fd number }

def bindUnixDispatch (budget : Nat) (io : BlockingIo.Hooks (MachineHooks.State K U) F Poll Host)
    (base : UnixFdDispatch.Hooks (MachineHooks.State K U) H D O E Meta Path) :
    UnixFdDispatch.Hooks (MachineHooks.State K U) H D O E Meta Path := {
  base with pollAndUnblockZero := BlockingIo.pollAndUnblock budget io (some ⟨0,0,by decide⟩) }
end Miri.Interpreter.ReadinessMachine
