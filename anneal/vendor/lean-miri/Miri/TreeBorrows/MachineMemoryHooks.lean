import Miri.TreeBorrows.TreeState
import Miri.Memory.MemoryState

/-!
Tree Borrows adapters for the three Miri `Machine` memory hooks.

The caller order in pinned `machine.rs` is represented here: optional
allocation diagnostics, data-race handling, Tree Borrows, synchronization
objects, and (for deallocation) span/address-map release. The data-race,
sync-object, diagnostic, span, and allocation-ID operations remain callbacks;
this module does not pretend to implement those machine subsystems. Read and
write adapters update the live allocation's `BorrowTree` extra before
returning a Tree Borrows failure, as the source mutates `AllocExtra` in place.
-/

namespace Miri.TreeBorrows.MachineMemoryHooks

open Miri.ABI
open Miri.Memory

inductive SyncAccessKind where
  | Read
  | Write
  | Dealloc
  deriving DecidableEq, Repr, Inhabited

inductive AccessDiagnostic where
  | Read (range : AllocRange)
  | Write (range : AllocRange)
  | Freed
  deriving DecidableEq, Repr

/-- A finite ordered representation of Miri's per-allocation `BTreeMap<Size,
Box<dyn SyncObj>>`. Insertion keeps keys unique and ascending, so the access
walks below have the source map's iteration order. -/
structure SyncObjectMap (Obj : Type) where
  entries : Array (Size × Obj) := #[]

namespace SyncObjectMap

def empty : SyncObjectMap Obj := ⟨#[]⟩

def insert (map : SyncObjectMap Obj) (offset : Size) (object : Obj) :
    SyncObjectMap Obj := Id.run do
  let mut entries := #[]
  let mut inserted := false
  for old in map.entries do
    if old.1.bytes == offset.bytes then
      if !inserted then
        entries := entries.push (offset, object)
        inserted := true
    else if !inserted && offset.bytes < old.1.bytes then
      entries := entries.push (offset, object)
      entries := entries.push old
      inserted := true
    else
      entries := entries.push old
  if !inserted then entries := entries.push (offset, object)
  return ⟨entries⟩

def remove (map : SyncObjectMap Obj) (offset : Size) : SyncObjectMap Obj :=
  ⟨map.entries.filter fun entry => entry.1.bytes != offset.bytes⟩

def inRange (map : SyncObjectMap Obj) (range : AllocRange) :
    Except MemoryError (Array (Size × Obj)) := do
  let endOffset ← range.endExclusive
  return map.entries.filter fun entry =>
    range.start.bytes ≤ entry.1.bytes && entry.1.bytes < endOffset.bytes

end SyncObjectMap

/-- Allocation-indexed sync metadata. Miri stores one offset map inside each
`AllocExtra`; this outer index lets a single `mem_copy_repeatedly` context
carry the source and destination allocation maps independently. -/
structure SyncObjectStore (Obj : Type) where
  allocations : Array (AllocId × SyncObjectMap Obj) := #[]

namespace SyncObjectStore

def empty : SyncObjectStore Obj := ⟨#[]⟩

def get (store : SyncObjectStore Obj) (allocId : AllocId) : SyncObjectMap Obj :=
  (store.allocations.find? fun entry => entry.1 == allocId).map Prod.snd |>.getD .empty

def set (store : SyncObjectStore Obj) (allocId : AllocId)
    (objects : SyncObjectMap Obj) : SyncObjectStore Obj :=
  ⟨(store.allocations.filter fun entry => entry.1 != allocId).push (allocId, objects)⟩

def remove (store : SyncObjectStore Obj) (allocId : AllocId) : SyncObjectStore Obj :=
  ⟨store.allocations.filter fun entry => entry.1 != allocId⟩

end SyncObjectStore

/-- The `AllocExtra`-local sync map plus the global state threaded through
Miri's machine callbacks. The caller supplies the sync map for the allocation
currently being accessed and stores the returned map with that allocation. -/
structure Context (State Obj : Type) where
  state : State
  syncObjects : SyncObjectStore Obj
  trackAllocAccesses : Bool := false
  trackedAllocIds : Array AllocId := #[]

/-- Hooks corresponding to the portions of `machine.rs` and
`concurrency::sync::SyncObj` outside the Tree Borrows subtree. Data-race hooks
must dispatch the configured Miri handler (`None` or vector clocks),
including its per-allocation-handler invariant and weak-memory write effect. -/
structure Hooks (State Obj MachineKind : Type) where
  protectedTags : ProtectedTags
  emitDiagnostic : State → AllocId → AccessDiagnostic → State
  dataRaceRead : State → Pointer (Option Provenance) → AllocId → AllocRange →
    MachineHookResult State Unit
  dataRaceWrite : State → Pointer (Option Provenance) → AllocId → AllocRange →
    MachineHookResult State Unit
  dataRaceDeallocate : State → Pointer (Option Provenance) → AllocId →
    Size → MemoryKind MachineKind → MachineHookResult State Unit
  syncOnAccess : State → Obj → SyncAccessKind → MachineHookResult State Unit
  deleteOnWrite : Obj → Bool
  recordDeallocatedSpan : State → AllocId → State
  freeAllocId : State → AllocId → Size → Align → MemoryKind MachineKind → State

structure AccessResult (State Obj MachineKind : Type) where
  memory : MemoryState Provenance BorrowTree MachineKind
  context : Context State Obj
  outcome : Except String Unit

private def findSyncRange (context : Context State Obj) (allocId : AllocId)
    (range : AllocRange) :
    Except String (Array (Size × Obj)) :=
  (context.syncObjects.get allocId).inRange range |>.mapError fun error =>
    s!"sync-object range computation failed: {reprStr error}"

private def commitTreeAccess [DecidableEq MachineKind]
    (memory : MemoryState Provenance BorrowTree MachineKind)
    (allocId : AllocId) (allocation : Allocation Provenance BorrowTree)
    (provenance : ProvenanceExtra) (range : AllocRange) (kind : AccessKind)
    (protectedTags : ProtectedTags) :
    Except String (MemoryState Provenance BorrowTree MachineKind ×
      BorrowTree.BorrowTreeAccessStatus) := do
  let access := allocation.extra.performBorrowAccessRange provenance range.start range.size
      kind protectedTags .VisitChildrenOfAccessed
  let updatedAllocation := allocation.setExtra access.tree
  let updatedMemory ← (memory.setLiveAllocation allocId updatedAllocation).mapError fun error =>
    s!"updating allocation {allocId.value} after Tree Borrows access failed: {reprStr error}"
  return (updatedMemory, access.status)

private def runSyncRange (context : Context State Obj) (hooks : Hooks State Obj MachineKind)
    (allocId : AllocId) (range : AllocRange) (kind : SyncAccessKind) :
    Except String (Context State Obj) := do
  let entries ← findSyncRange context allocId range
  let mut current := context
  for (offset, object) in entries do
    let checked := hooks.syncOnAccess current.state object kind
    current := { current with state := checked.state }
    match checked.outcome with
    | .ok () => pure ()
    | .error message => throw s!"sync object at offset {offset.bytes}: {message}"
  return current

/-- Pinned `MiriMachine::before_memory_read` after optional diagnostic. The
data-race hook runs first. The actual live allocation extra is then updated by
the Tree Borrows access, and a Tree error prevents all sync-object callbacks. -/
def beforeMemoryRead [DecidableEq MachineKind]
    (memory : MemoryState Provenance BorrowTree MachineKind)
    (context : Context State Obj) (hooks : Hooks State Obj MachineKind)
    (allocation : Allocation Provenance BorrowTree) (pointer : Pointer (Option Provenance))
    (allocId : AllocId) (provenance : ProvenanceExtra) (range : AllocRange) :
    AccessResult State Obj MachineKind := Id.run do
  let mut current := context
  if current.trackAllocAccesses && current.trackedAllocIds.contains allocId then
    current := { current with state := hooks.emitDiagnostic current.state allocId (.Read range) }
  let race := hooks.dataRaceRead current.state pointer allocId range
  current := { current with state := race.state }
  match race.outcome with
  | .error message => return ⟨memory, current, .error s!"data-race read: {message}"⟩
  | .ok () => pure ()
  let tree ← match commitTreeAccess memory allocId allocation provenance range .Read
      hooks.protectedTags with
    | .error message => return ⟨memory, current, .error message⟩
    | .ok tree => pure tree
  let (afterTree, status) := tree
  if status != BorrowTree.BorrowTreeAccessStatus.Completed then
    return ⟨afterTree, current,
      .error s!"Tree Borrows read failed: {reprStr status}"⟩
  match runSyncRange current hooks allocId range .Read with
  | .error message => return ⟨afterTree, current, .error message⟩
  | .ok synced => return ⟨afterTree, synced, .ok ()⟩

/-- Pinned `MiriMachine::before_memory_write` after optional diagnostic. Sync
objects are deleted only after every overlapping object's write check
succeeds, matching the source's collect-then-remove loop. -/
def beforeMemoryWrite [DecidableEq MachineKind]
    (memory : MemoryState Provenance BorrowTree MachineKind)
    (context : Context State Obj) (hooks : Hooks State Obj MachineKind)
    (allocation : Allocation Provenance BorrowTree) (pointer : Pointer (Option Provenance))
    (allocId : AllocId) (provenance : ProvenanceExtra) (range : AllocRange) :
    AccessResult State Obj MachineKind := Id.run do
  let mut current := context
  if current.trackAllocAccesses && current.trackedAllocIds.contains allocId then
    current := { current with state := hooks.emitDiagnostic current.state allocId (.Write range) }
  let race := hooks.dataRaceWrite current.state pointer allocId range
  current := { current with state := race.state }
  match race.outcome with
  | .error message => return ⟨memory, current, .error s!"data-race write: {message}"⟩
  | .ok () => pure ()
  let tree ← match commitTreeAccess memory allocId allocation provenance range .Write
      hooks.protectedTags with
    | .error message => return ⟨memory, current, .error message⟩
    | .ok tree => pure tree
  let (afterTree, status) := tree
  if status != BorrowTree.BorrowTreeAccessStatus.Completed then
    return ⟨afterTree, current,
      .error s!"Tree Borrows write failed: {reprStr status}"⟩
  let entries ← match findSyncRange current allocId range with
    | .ok entries => pure entries
    | .error message => return ⟨afterTree, current, .error message⟩
  let mut checked := current
  let mut toDelete : Array Size := #[]
  for (offset, object) in entries do
    let result := hooks.syncOnAccess checked.state object .Write
    checked := { checked with state := result.state }
    match result.outcome with
    | .error message =>
        return ⟨afterTree, checked,
          .error s!"sync object at offset {offset.bytes}: {message}"⟩
    | .ok () =>
        if hooks.deleteOnWrite object then toDelete := toDelete.push offset
  let mut updatedSyncObjects := checked.syncObjects.get allocId
  for offset in toDelete do
    updatedSyncObjects := updatedSyncObjects.remove offset
  checked := { checked with syncObjects := checked.syncObjects.set allocId updatedSyncObjects }
  return ⟨afterTree, checked, .ok ()⟩

structure DeallocationResult (State Obj MachineKind : Type) where
  allocation : Allocation Provenance BorrowTree
  context : Context State Obj
  outcome : Except String Unit

/-- Pinned `MiriMachine::before_memory_deallocation`. `MemoryLifecycle.deallocatePtr`
has already removed the allocation from its live map when it invokes this
callback. The tree result is retained in `allocation` for callers that need to
inspect a failed hook; the lifecycle caller still preserves its source removal
on failure. -/
def beforeMemoryDeallocation (context : Context State Obj)
    (hooks : Hooks State Obj MachineKind)
    (allocation : Allocation Provenance BorrowTree)
    (pointer : Pointer (Option Provenance)) (allocId : AllocId)
    (provenance : ProvenanceExtra) (size : Size) (align : Align)
    (kind : MemoryKind MachineKind) : DeallocationResult State Obj MachineKind := Id.run do
  let mut current := context
  if current.trackedAllocIds.contains allocId then
    current := { current with state := hooks.emitDiagnostic current.state allocId .Freed }
  let race := hooks.dataRaceDeallocate current.state pointer allocId size kind
  current := { current with state := race.state }
  match race.outcome with
  | .error message => return ⟨allocation, current, .error s!"data-race deallocation: {message}"⟩
  | .ok () => pure ()
  let deallocated := allocation.extra.deallocateBorrowRange provenance Size.ZERO size
      hooks.protectedTags
  let updatedAllocation := allocation.setExtra deallocated.tree
  if deallocated.status != .Deallocated then
    return ⟨updatedAllocation, current,
      .error s!"Tree Borrows deallocation failed: {reprStr deallocated.status}"⟩
  for (offset, object) in (current.syncObjects.get allocId).entries do
    let checked := hooks.syncOnAccess current.state object .Dealloc
    current := { current with state := checked.state }
    match checked.outcome with
    | .ok () => pure ()
    | .error message =>
        return ⟨updatedAllocation, current,
          .error s!"sync object at offset {offset.bytes}: {message}"⟩
  current := { current with state := hooks.recordDeallocatedSpan current.state allocId }
  current := { current with
    state := hooks.freeAllocId current.state allocId size align kind }
  current := { current with syncObjects := current.syncObjects.remove allocId }
  return ⟨updatedAllocation, current, .ok ()⟩

/-- Adapt the source-ordered Tree Borrows hooks to the existing `mem_copy`
read/write callback boundary. Pointer resolution, `before_alloc_access`, and
the actual Miri data-race handler remain explicit caller inputs. -/
def asMemoryCopyHooks [DecidableEq MachineKind] (machineHooks : Hooks State Obj MachineKind)
    (pointerAccess : MemoryState Provenance BorrowTree MachineKind → Context State Obj →
      Pointer (Option Provenance) → Size →
      MemoryStateHookResult Provenance BorrowTree MachineKind (Context State Obj)
        (Option (AllocId × Size × ProvenanceExtra)))
    (tryGetAllocId : MemoryState Provenance BorrowTree MachineKind → Context State Obj →
      Pointer (Option Provenance) → UInt64 → Option AllocId)
    (beforeAllocationAccess : MemoryState Provenance BorrowTree MachineKind → Context State Obj →
      AllocId → MemoryStateHookResult Provenance BorrowTree MachineKind (Context State Obj) Unit) :
    MemoryCopyHooks Provenance BorrowTree MachineKind (Context State Obj) ProvenanceExtra :=
  { synchronizeMemory := fun _ context => context
    pointerAccess := pointerAccess
    tryGetAllocId := tryGetAllocId
    beforeAllocationAccess := beforeAllocationAccess
    beforeMemoryRead := fun context memory allocation pointer allocId provenance range =>
      let result := beforeMemoryRead memory context machineHooks allocation pointer allocId
        provenance range
      ⟨result.memory, result.context, result.outcome⟩
    beforeMemoryWrite := fun context memory allocation pointer allocId provenance range =>
      let result := beforeMemoryWrite memory context machineHooks allocation pointer allocId
        provenance range
      ⟨result.memory, result.context, result.outcome⟩ }

/-- Adapt the ordered tree/race/sync/free sequence to
`MemoryLifecycleHooks.beforeDeallocation`. The surrounding lifecycle owns
pointer resolution, live-map removal, and dead-allocation caching; the
adapter returns the explicit memory successor unchanged. -/
def asDeallocationHook (machineHooks : Hooks State Obj MachineKind) :
    MemoryState Provenance BorrowTree MachineKind → Context State Obj →
      Allocation Provenance BorrowTree →
      Pointer (Option Provenance) → AllocId → ProvenanceExtra → Size → Align →
      MemoryKind MachineKind →
      MemoryStateHookResult Provenance BorrowTree MachineKind (Context State Obj) Unit :=
  fun memory context allocation pointer allocId provenance size align kind =>
    let result := beforeMemoryDeallocation context machineHooks allocation pointer allocId
      provenance size align kind
    ⟨memory, result.context, result.outcome⟩

end Miri.TreeBorrows.MachineMemoryHooks
