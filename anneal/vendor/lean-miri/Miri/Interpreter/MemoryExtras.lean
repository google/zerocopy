import Miri.Interpreter.PlaceMachine
import Miri.Interpreter.IntrinsicAtomic
import Miri.Concurrency.SyncObject

/-! Allocation-local extras for machine.rs:1695–1838. Clocks remain in
MachineHooks: neither the registry nor atomic lenses keep a second clock copy.
Sync payloads are typed data; their required interpreter constructs real
stateful Object callbacks, avoiding a negative recursive state definition. -/
namespace Miri.Interpreter.MemoryExtras
open Miri.ABI Miri.Memory Miri.Concurrency
abbrev Machine := PlaceMachine.Machine
abbrev M := PlaceMachine.MachineM

structure Entry (Payload : Type) where
  payload : Payload
  deleteOnWrite : Bool
  /-- Captured provenance must be supplied, including references in callbacks. -/
  roots : Array Provenance

structure AllocationExtra (Payload : Type) where
  weakMemory : Option (StoreBufferAlloc (Scalar Provenance))
  sync : Array (Size × Entry Payload) := #[]

structure Registry (Payload : Type) where
  allocations : Array (AllocId × AllocationExtra Payload) := #[]

/-- A lens into the owner's shared machine User; it may be nested with pointer,
validity, threading, or pthread state without duplicating any of them. -/
structure Hooks (K User Payload : Type) where
  get : User → Registry Payload
  put : User → Registry Payload → User
  onAccess : Payload → SyncObject.AccessKind → M K User Unit
  weakError : StoreBufferAllocError → StepError

/-- Remove only records for an allocation that never became a live owner.
Callbacks may have changed other IDs while the initializer was running, so
this cleanup is deliberately keyed to the reserved ID alone. -/
def discardUninserted [DecidableEq K] (h : Hooks K User Payload)
    (id : AllocId) (machine : Machine K User) (cleanRegistry := true)
    (cleanRace := true) (cleanSpan := true) : Machine K User := Id.run do
  if machine.memory.live.any (fun entry => entry.1 == id) then return machine
  let registry := h.get machine.user
  let registry := if cleanRegistry then
    {registry with allocations := registry.allocations.filter (fun entry => entry.1 != id)}
    else registry
  return {machine with
    user := h.put machine.user registry
    raceAllocations := if cleanRace then machine.raceAllocations.filter (fun entry => entry.1 != id)
      else machine.raceAllocations
    allocationSpans := if cleanSpan then machine.allocationSpans.filter (fun entry => entry.1 != id)
      else machine.allocationSpans}

def lookup (h : Hooks K User Payload) (machine : Machine K User) (id : AllocId) :
    Except StepError (AllocationExtra Payload) :=
  match (h.get machine.user).allocations.find? (fun entry => entry.1 == id) with
  | some entry => .ok entry.2
  | none => .error (.invalidProgram "allocation extras missing for live allocation")

def putAllocation (h : Hooks K User Payload) (machine : Machine K User)
    (id : AllocId) (extra : AllocationExtra Payload) : Machine K User :=
  let registry := h.get machine.user
  let registry := {registry with allocations :=
    (registry.allocations.filter fun entry => entry.1 != id).push (id, extra)}
  {machine with user := h.put machine.user registry}

private def liftResult (result : Except StepError A) : M K User A :=
  match result with | .ok value => pure value | .error error => throw error

/-- Called in the allocation tail after the actual race allocation was installed. -/
def initAllocation [DecidableEq K] (h : Hooks K User Payload) (id : AllocId) (weak : Bool) : M K User Unit := do
  let initial ← get
  let alreadyHadExtras := (h.get initial.user).allocations.any (fun entry => entry.1 == id)
  try
    let machine ← get
    if ((h.get machine.user).allocations.any fun entry => entry.1 == id) then
      throw (.invalidProgram "allocation extras initialized twice")
    if weak then
      if machine.dataRace.isNone then throw (.invalidProgram "weak memory requires vector clocks")
      unless machine.raceAllocations.any (fun entry => entry.1 == id) do
        throw (.invalidProgram "weak memory requires allocation race clocks")
    set (putAllocation h machine id ⟨if weak then some StoreBufferAlloc.newAllocation else none, #[]⟩)
  catch error =>
    unless alreadyHadExtras do
      modify (fun machine => discardUninserted h id machine false true true)
    throw error

/-- Commit the transition before reporting failure: RangeObjectMap can mutate
before a failed check. Called only after the successful non-atomic race write. -/
def nonAtomicWrite (h : Hooks K User Payload) (id : AllocId) (range : AllocRange) : M K User Unit := do
  let machine ← get
  let extra ← liftResult (lookup h machine id)
  if let some buffer := extra.weakMemory then
    let some global := machine.dataRace |
      throw (.invalidProgram "weak allocation without global vector clocks")
    let result := buffer.nonAtomicWrite range global
    set (putAllocation h machine id {extra with weakMemory := some result.allocation})
    match result.outcome with
    | .ok _ => pure ()
    | .error error => throw (h.weakError error)

def lookupSync (h : Hooks K User Payload) (address : SyncObject.Address) :
    M K User (Option (SyncObject.Object (Machine K User) Payload)) := do
  let extra ← liftResult (lookup h (← get) address.allocation)
  return (extra.sync.find? (fun entry => entry.1 == address.offset)).map fun (_,entry) =>
    {payload := entry.payload, deleteOnWrite := entry.deleteOnWrite,
     onAccess := h.onAccess entry.payload}

/-- Insert typed payload together with its GC roots. Replacement agrees with
BTreeMap::insert, including replacement after a failed dynamic downcast. -/
def insertSync (h : Hooks K User Payload) (address : SyncObject.Address)
    (entry : Entry Payload) : M K User Unit := do
  let machine ← get
  let extra ← liftResult (lookup h machine address.allocation)
  set (putAllocation h machine address.allocation {extra with sync :=
    (extra.sync.filter fun item => item.1 != address.offset).push (address.offset, entry)})

def accessHooks (h : Hooks K User Payload) : SyncObject.AccessHooks (Machine K User) Payload where
  entries := fun id => do
    let extra ← liftResult (lookup h (← get) id)
    return extra.sync.map fun (offset,entry) => (offset,
      {payload := entry.payload, deleteOnWrite := entry.deleteOnWrite,
       onAccess := h.onAccess entry.payload})
  remove := fun id offset => do
    let machine ← get
    let extra ← liftResult (lookup h machine id)
    set (putAllocation h machine id {extra with sync := extra.sync.filter fun entry => entry.1 != offset})

/-- onMemoryAccess runs ascending callbacks and only then deletes write-sensitive
metadata. A failing callback retains all prior effects and all registry entries. -/
def syncAccess (h : Hooks K User Payload) (write : Bool) (id : AllocId)
    (range : AllocRange) : M K User Unit :=
  SyncObject.onMemoryAccess (accessHooks h) id range.start range.size (if write then .write else .read)

/-- Portable hooks replace the two former leaves in the already ordered
PlaceMachine diagnostic → race → weak → TB → sync pipeline. -/
def bindAccess (h : Hooks K User Payload) (base : PlaceMachine.AccessConfig K User) :
    PlaceMachine.AccessConfig K User :=
  {base with weakMemoryWrite := nonAtomicWrite h, syncAccess := syncAccess h}

/-- Source deallocation sync stage, after race-deallocation and TB-deallocation.
No metadata is removed here. MemoryLifecycle has already removed the live
allocation before invoking this stage, including on callback failure. -/
def beforeDeallocationSync (h : Hooks K User Payload) (id : AllocId) : M K User Unit :=
  SyncObject.onMemoryAccess (accessHooks h) id Size.ZERO Size.ZERO .deallocation

/-- Run only after successful complete deallocation, alongside race-index cleanup. -/
def removeAllocation (h : Hooks K User Payload) (id : AllocId) : M K User Unit :=
  modify fun machine =>
    let registry := h.get machine.user
    {machine with user := h.put machine.user {registry with
      allocations := registry.allocations.filter (fun entry => entry.1 != id)}}

/-- Atomic dispatch uses exactly the same global clock, allocation clocks and
weak buffer as non-atomic accesses. Missing clocks remain an explicit error. -/
def getAtomic (h : Hooks K User Payload) (machine : Machine K User) (id : AllocId) :
    Except StepError (AtomicState (Scalar Provenance)) := do
  let some global := machine.dataRace | throw (.invalidProgram "atomic vector clocks disabled")
  let some (_,allocation) := machine.raceAllocations.find? (fun entry => entry.1 == id) |
    throw (.invalidProgram "atomic allocation race clocks missing")
  let extra ← lookup h machine id
  return ⟨global, allocation, extra.weakMemory⟩

/-- This setter is used after getAtomic succeeded; it updates the latest extras,
so concurrent callback changes to the sync registry cannot be overwritten. -/
def setAtomic (h : Hooks K User Payload) (machine : Machine K User) (id : AllocId)
    (atomic : AtomicState (Scalar Provenance)) : Except StepError (Machine K User) := do
  let extra ← lookup h machine id
  return putAllocation h {machine with
    dataRace := some atomic.global
    raceAllocations := (machine.raceAllocations.filter fun entry => entry.1 != id).push (id,atomic.allocation)}
    id {extra with weakMemory := atomic.weakMemoryAllocation}

/-- Checked effectful setter for IntrinsicAtomic: absence is an error rather
than a silently ignored write. -/
def commitAtomic (h : Hooks K User Payload) (id : AllocId)
    (atomic : AtomicState (Scalar Provenance)) : M K User Unit := do
  let next ← liftResult (setAtomic h (← get) id atomic)
  set next

/-- Install the canonical machine lenses into the full atomic dispatcher. -/
def bindAtomic (h : Hooks K User Payload)
    (base : IntrinsicAtomicHooks Provenance (Machine K User) C V) :
    IntrinsicAtomicHooks Provenance (Machine K User) C V :=
  {base with getAtomic := getAtomic h, setAtomic := commitAtomic h}

/-- Stack allocation's diagnostic/tree/race initialization precedes this tail;
other compiler/machine tail effects execute after extras are installed. -/
def bindAllocation [DecidableEq K] (h : Hooks K User Payload) (weak : Bool)
    (base : PlaceMachine.AllocationConfig K User) : PlaceMachine.AllocationConfig K User :=
  {base with allocationTail := fun id size align => do
    initAllocation h id weak
    try
      base.allocationTail id size align
    catch error =>
      modify (discardUninserted h id)
      throw error}

/-- All retained store-buffer values, including old modification-order entries,
are roots. Consumers inspect scalar provenance using the canonical scalar API. -/
def weakValues (registry : Registry Payload) : Array (Scalar Provenance) := Id.run do
  let mut values := #[]
  for (_,extra) in registry.allocations do
    if let some allocation := extra.weakMemory then
      for buffer in allocation.storeBuffers.iter do
        for entry in buffer.entries do
          if let some value := entry.val then values := values.push value
  return values

def syncRoots (registry : Registry Payload) : Array Provenance :=
  registry.allocations.foldl (fun roots (_,extra) =>
    extra.sync.foldl (fun roots (_,entry) => roots ++ entry.roots) roots) #[]
end Miri.Interpreter.MemoryExtras
