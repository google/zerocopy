import Miri.Interpreter.AllocationDriver
import Miri.Interpreter.GlobalMemoryCopyMachine

/-! Source-shaped allocate/copy/deallocate from rustc memory.rs:301–337.
No resize shortcut: allocation, initialization mask, access hooks, provenance
copy and source-deallocation failures retain all preceding effects. -/
namespace Miri.Interpreter.ReallocationDriver
open Miri.ABI Miri.Memory Miri.TreeBorrows Miri.Memory.AllocAddresses
abbrev User := PointerMachine.User
abbrev M K U A := PointerMachine.M K U A

structure Hooks (K U Payload : Type) where
  driver : AllocationDriver.Hooks K U Payload
  access : PlaceMachine.AccessConfig K (User U)
  allocation : PlaceMachine.AllocationConfig K (User U)
  weakMemory : Bool
  globalKind : Option (MemoryKind K)

/-- Allocation creation requires shared extras and storage configuration, not a
pointer/deallocation interpreter. -/
structure CreationHooks (K U Payload : Type) where
  extras : MemoryExtras.Hooks K (User U) Payload
  allocation : PlaceMachine.AllocationConfig K (User U)
  weakMemory : Bool
  globalKind : Option (MemoryKind K)

def Hooks.creation (h : Hooks K U Payload) : CreationHooks K U Payload :=
  ⟨h.driver.allocation.extras,h.allocation,h.weakMemory,h.globalKind⟩

private def liftResult (result : Except StepError A) : M K U A :=
  match result with | .ok value => pure value | .error error => throw error
private def machineAction (action : PlaceMachine.MachineM K (User U) A) : M K U A := fun state =>
  match action state.machine with
  | .ok value machine => .ok value {state with machine}
  | .error error machine => .error error {state with machine}

/-- General-kind counterpart of PlaceMachine.allocateStack using the same
root/tree/race initialization and concrete shared extras. Root adjustment runs
only after the new allocation was inserted and can observe its real metadata. -/
private def allocateWithRoot [DecidableEq K] (h : CreationHooks K U Payload) (size : Size) (align : Align)
    (kind : MemoryKind K) (init : AllocInit)
    (root : AllocId → BorTag → MemoryKind K → M K U (Pointer Provenance)) : M K U (Pointer Provenance) := do
  let created ← match h.allocation.nativeStorage with
    | some create => create size align init
    | none => pure (Allocation.tryNew (Prov := Provenance) size align init h.allocation.zeroedStorage)
  let allocation ← match created with
    | .ok allocation => pure allocation
    | .error error => throw (.callback s!"allocation storage: {reprStr error}")
  try
    if size.bytes > h.allocation.maximumObjectSize.bytes then
      throw (.resourceExhaustion "allocation exceeds maximum object size")
    let state ← get
    let (memory,result) := state.machine.memory.reserveAllocId
    set {state with machine := {state.machine with memory}}
    let id ← match result with
      | .ok id => pure id
      | .error error => throw (.resourceExhaustion s!"allocation identity: {reprStr error}")
    if h.globalKind == some kind then throw (.invalidProgram "dynamically allocating global memory kind")
    machineAction (h.allocation.diagnostic id size align)
    let config := MemoryExtras.bindAllocation h.extras h.weakMemory h.allocation
    let tree ← machineAction (PlaceMachine.initStackExtra config.allocationTail id size align)
    modify fun state => {state with machine := {state.machine with memory :=
      {state.machine.memory with live := state.machine.memory.live.push (id,⟨kind,allocation.withExtra tree⟩)}}}
    let tag ← match (← get).machine.borrowTracker with
      | none => pure BorTag.one
      | some tracker =>
        match tracker.global.rootTag? id with
        | some tag => pure tag
        | none => throw (.invalidProgram "new allocation missing canonical root tag")
    root id tag kind
  catch error =>
    if allocation.nativeBuffer.isSome then
      let retained := (← get).machine.memory.live.any fun (_,entry) => entry.allocation.nativeBuffer == allocation.nativeBuffer
      unless retained do
        let some drop := h.allocation.nativeDrop | throw (.invalidProgram "native backing lacks allocation-failure drop capability")
        drop allocation
    throw error

/-- Explicit-choice adapter retained for operation-level fixtures. -/
def allocate [DecidableEq K] (h : Hooks K U Payload) (size : Size) (align : Align)
    (kind : MemoryKind K) (init : AllocInit) (choice : AddressRandomChoices) : M K U (Pointer Provenance) :=
  allocateWithRoot h.creation size align kind init fun id tag kind => do
    let kind ← liftResult (h.driver.addressKind kind)
    PointerMachine.adjustAllocRootPointer h.driver.pointer id tag Size.ZERO kind choice

/-- Production allocation samples choices in the canonical root-address
callback after insertion, never when constructing a foreign-call dictionary. -/
def allocateSource [DecidableEq K] (h : Hooks K U Payload) (size : Size) (align : Align)
    (kind : MemoryKind K) (init : AllocInit) : M K U (Pointer Provenance) :=
  allocateWithRoot h.creation size align kind init fun id tag _ => h.allocation.adjustRootAddress id tag

/-- Source allocation without unused pointer/deallocation capabilities. -/
def allocateSourceFrom [DecidableEq K] (h : CreationHooks K U Payload) (size : Size) (align : Align)
    (kind : MemoryKind K) (init : AllocInit) : M K U (Pointer Provenance) :=
  allocateWithRoot h size align kind init fun id tag _ => h.allocation.adjustRootAddress id tag

/-- Use an already source-assembled allocation config. This is for startup
allocations whose config already owns extras initialization and root-address
choice; wrapping it in CreationHooks would initialize extras twice. -/
def allocateConfigured [DecidableEq K] (config : PlaceMachine.AllocationConfig K (User U))
    (size : Size) (align : Align) (kind : MemoryKind K) (init : AllocInit) : M K U (Pointer Provenance) := do
  let created ← match config.nativeStorage with
    | some create => create size align init
    | none => pure (Allocation.tryNew (Prov := Provenance) size align init config.zeroedStorage)
  let allocation ← match created with
    | .ok allocation => pure allocation
    | .error error => throw (.callback s!"allocation storage: {reprStr error}")
  try
    if size.bytes > config.maximumObjectSize.bytes then
      throw (.resourceExhaustion "allocation exceeds maximum object size")
    let state ← get
    let (memory, reserved) := state.machine.memory.reserveAllocId
    set {state with machine := {state.machine with memory}}
    let id ← match reserved with
      | .ok id => pure id
      | .error error => throw (.resourceExhaustion s!"allocation identity: {reprStr error}")
    machineAction (config.diagnostic id size align)
    let tree ← machineAction (PlaceMachine.initStackExtra config.allocationTail id size align)
    modify fun state => {state with machine := {state.machine with memory :=
      {state.machine.memory with live := state.machine.memory.live.push (id,⟨kind,allocation.withExtra tree⟩)}}}
    let tag ← match (← get).machine.borrowTracker with
      | none => pure BorTag.one
      | some tracker => match tracker.global.rootTag? id with
        | some tag => pure tag
        | none => throw (.invalidProgram "new allocation missing canonical root tag")
    config.adjustRootAddress id tag
  catch error =>
    if allocation.nativeBuffer.isSome then
      let retained := (← get).machine.memory.live.any fun (_,entry) => entry.allocation.nativeBuffer == allocation.nativeBuffer
      unless retained do
        let some drop := config.nativeDrop | throw (.invalidProgram "native backing lacks allocation-failure drop capability")
        drop allocation
    throw error

/-- Source get_alloc_raw old-size query occurs after allocation; Cow::Owned
conversions cache, Cow::Borrowed conversions do not. No access hook is added
here: the following memcopy performs the actual source access. -/
private def oldAllocationSize [DecidableEq K] (access : PlaceMachine.AccessConfig K (User U)) (id : AllocId) : M K U Size := do
  let state ← get
  let result := MemoryLifecycle.getAllocRaw state.machine.memory ⟨state.machine,none⟩ id
    access.globalKind access.globalHooks
  modify fun state => {state with machine := {result.hooks.machine with memory := result.memory}}
  match result.outcome with
  | .ok allocation => return allocation.byteSize
  | .error error => throw (result.hooks.pendingError.getD
      (access.memoryError (.pointerAccess (.rawAccess error))))

/-- Checks original zero offset first, allocates the entire new block with
init_growth, copies min(old,new) including uninitialized/provenance state, then
frees the source. A copy/deallocation error retains the new allocation. -/
private def reallocateWith [DecidableEq K]
    (access : PlaceMachine.AccessConfig K (User U))
    (extras : MemoryExtras.Hooks K (User U) Payload) (arithmetic : PointerArithmetic)
    (pointer : Pointer (Option Provenance)) (oldLayout : Option (Size × Align))
    (newSize : Size) (newAlign : Align) (kind : MemoryKind K) (initGrowth : AllocInit)
    (create : Size → Align → MemoryKind K → AllocInit → M K U (Pointer Provenance))
    (destroy : Pointer (Option Provenance) → Option (Size × Align) → MemoryKind K → M K U Unit) :
    M K U (Pointer Provenance) := do
  let memory := (← get).machine.memory
  let resolved ← machineAction (access.resolvePointer memory pointer 0)
  let resolved ← match resolved with
    | .ok resolved => pure resolved
    | .error address => throw (.undefinedBehavior s!"dangling realloc pointer {address}")
  if resolved.offset.bytes != 0 then
    throw (.undefinedBehavior "reallocating pointer outside beginning of allocation")
  let dest ← create newSize newAlign kind initGrowth
  let oldSize ← match oldLayout with
    | some (size,_) => pure size
    | none => oldAllocationSize access resolved.allocId
  let size := if oldSize.bytes < newSize.bytes then oldSize else newSize
  let access := MemoryExtras.bindAccess extras access
  GlobalMemoryCopyMachine.copy access arithmetic pointer dest.withOptionalProvenance size 1 true
  destroy pointer oldLayout kind
  return dest
def reallocate [DecidableEq K] (h : Hooks K U Payload)
    (pointer : Pointer (Option Provenance)) (oldLayout : Option (Size × Align))
    (newSize : Size) (newAlign : Align) (kind : MemoryKind K) (initGrowth : AllocInit)
    (allocationChoice : AddressRandomChoices) (reuseChoice : Bool) : M K U (Pointer Provenance) :=
  reallocateWith h.access h.driver.allocation.extras h.driver.pointer.arithmetic pointer oldLayout newSize newAlign kind initGrowth
    (fun size align kind init => allocate h size align kind init allocationChoice)
    (AllocationDriver.deallocate h.driver reuseChoice)

/-- Persistent draws occur at actual allocation and late deallocation events. -/
def reallocateSource [DecidableEq K] (choices : ExecutionChoices.Access (PointerMachine.State K U))
    (h : Hooks K U Payload) (pointer : Pointer (Option Provenance)) (oldLayout : Option (Size × Align))
    (newSize : Size) (newAlign : Align) (kind : MemoryKind K) (initGrowth : AllocInit) : M K U (Pointer Provenance) :=
  reallocateWith h.access h.driver.allocation.extras h.driver.pointer.arithmetic pointer oldLayout newSize newAlign kind initGrowth
    (allocateSource h) (AllocationDriver.deallocateSource choices h.driver)
/-- Source reallocation with only creation/access and the actual late
source-deallocation action. It shares the ordering of both legacy adapters. -/
def reallocateFrom [DecidableEq K]
    (access : PlaceMachine.AccessConfig K (User U)) (h : CreationHooks K U Payload)
    (arithmetic : PointerArithmetic)
    (destroy : Pointer (Option Provenance) → Option (Size × Align) → MemoryKind K → M K U Unit)
    (pointer : Pointer (Option Provenance)) (oldLayout : Option (Size × Align))
    (newSize : Size) (newAlign : Align) (kind : MemoryKind K) (initGrowth : AllocInit) : M K U (Pointer Provenance) :=
  reallocateWith access h.extras arithmetic pointer oldLayout newSize newAlign kind initGrowth
    (allocateSourceFrom h) destroy

/-- Source reallocation when the allocation configuration already owns the
canonical extras initialization and root-address choice. This mirrors
`reallocateFrom` while avoiding a second `MemoryExtras.bindAllocation` pass.
The new allocation, provenance-aware copy, and late destroy retain the source
ordering and partial effects. -/
def reallocateConfiguredFrom [DecidableEq K]
    (access : PlaceMachine.AccessConfig K (User U))
    (extras : MemoryExtras.Hooks K (User U) Payload)
    (arithmetic : PointerArithmetic)
    (config : PlaceMachine.AllocationConfig K (User U))
    (destroy : Pointer (Option Provenance) → Option (Size × Align) → MemoryKind K → M K U Unit)
    (pointer : Pointer (Option Provenance)) (oldLayout : Option (Size × Align))
    (newSize : Size) (newAlign : Align) (kind : MemoryKind K) (initGrowth : AllocInit) :
    M K U (Pointer Provenance) :=
  reallocateWith access extras arithmetic pointer oldLayout newSize newAlign kind initGrowth
    (fun size align kind init => allocateConfigured config size align kind init) destroy

end Miri.Interpreter.ReallocationDriver
