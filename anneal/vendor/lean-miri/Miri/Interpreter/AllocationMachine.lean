import Miri.Interpreter.MemoryExtras

/-! Connected machine deallocation: rustc memory.rs deallocate_ptr and Miri
machine.rs:1790–1838. The live allocation is removed before machine checks,
including failures; clock, tree and synchronization failures retain effects. -/
namespace Miri.Interpreter.AllocationMachine
open Miri.ABI Miri.Memory Miri.TreeBorrows
open Miri.Interpreter.MemoryExtras

structure DeallocationHooks (K User Payload : Type) where
  extras : MemoryExtras.Hooks K User Payload
  resolvePointer : MemoryState Provenance BorrowTree K → PlaceMachine.AccessState K User →
    Pointer (Option Provenance) → Int →
    PointerResolutionResult Provenance BorrowTree K (PlaceMachine.AccessState K User) ProvenanceExtra
  diagnostic : AllocId → PlaceMachine.MachineM K User Unit
  /-- Source current_user_relevant_span; no default fabricated span. -/
  currentSpan : PlaceMachine.MachineM K User MIR.SpanRef
  /-- Source address-reuse/free_alloc_id including canonical address map. -/
  freeAllocId : AllocId → Size → Align → MemoryKind K → PlaceMachine.MachineM K User Unit
  /-- Preserve a failed detached allocation's mutated tree for diagnostics/GC. -/
  retainDetached : Allocation Provenance BorrowTree → PlaceMachine.Machine K User → PlaceMachine.Machine K User
  nativeDrop : Option (Allocation Provenance BorrowTree → MachineHooks.M K User Unit) := none
  error : MemoryLifecycleError → StepError

/-- Pinned memory.rs::deallocate_ptr failures. Machine-hook typed failures
are recovered from AccessState.pendingError before this classification. -/
def deallocationError : MemoryLifecycleError → StepError
  | .danglingPointer address => .undefinedBehavior s!"DanglingIntPointer at deallocation: {address}"
  | error@(.nonzeroAllocationOffset ..) | error@(.globalAllocationDeallocation ..)
  | error@(.useAfterFree ..) | error@(.immutableAllocation ..)
  | error@(.memoryKindMismatch ..) | error@(.layoutMismatch ..) =>
    .undefinedBehavior s!"deallocation: {reprStr error}"
  | .duplicateDeadAllocation id => .invalidProgram s!"Nothing can be deallocated twice: {reprStr id}"
  | .hookFailure hook reason => .callback s!"{hook}: {reason}"
  | error => .invalidProgram s!"unexpected deallocation source failure: {reprStr error}"

private def before (h : DeallocationHooks K User Payload)
    (allocation : Allocation Provenance BorrowTree) (id : AllocId)
    (provenance : ProvenanceExtra) (size : Size) (align : Align) (kind : MemoryKind K) :
    PlaceMachine.MachineM K User Unit := do
  -- MemoryLifecycle has already removed the allocation and synchronized that
  -- authoritative successor into this machine view before entering the hook.
  h.diagnostic id
  let (machine,result) := MachineHooks.memoryRaceAccess (← get) id ⟨Size.ZERO,size⟩ (some .Deallocate) .Read
  set machine
  match result with | .error error => throw error | .ok () => pure ()
  if let some tracker := (← get).borrowTracker then
    let result := allocation.extra.deallocateBorrowRange provenance Size.ZERO size tracker.global.protectedTags
    modify (h.retainDetached (allocation.setExtra result.tree))
    if result.status != .Deallocated then
      throw (.undefinedBehavior s!"Tree Borrows deallocation: {reprStr result.status}")
  MemoryExtras.beforeDeallocationSync h.extras id
  let span ← h.currentSpan
  modify fun machine => {machine with allocationSpans := machine.allocationSpans.map fun (old,allocated,freed) =>
    (old,allocated,if old == id then some span else freed)}
  h.freeAllocId id size align kind
  MemoryExtras.removeAllocation h.extras id
  modify fun machine => {machine with raceAllocations := machine.raceAllocations.filter fun entry => entry.1 != id}

private def callback (h : DeallocationHooks K User Payload)
    (memory : MemoryState Provenance BorrowTree K) (state : PlaceMachine.AccessState K User)
    (allocation : Allocation Provenance BorrowTree)
    (_pointer : Pointer (Option Provenance)) (id : AllocId) (provenance : ProvenanceExtra)
    (size : Size) (align : Align) (kind : MemoryKind K) :
    MemoryStateHookResult Provenance BorrowTree K (PlaceMachine.AccessState K User) Unit :=
  let state := {state with machine := {state.machine with memory}}
  match before h allocation id provenance size align kind state.machine with
  | .ok value machine => ⟨machine.memory,{state with machine},.ok value⟩
  | .error error machine => ⟨machine.memory,⟨machine,some error⟩,.error (reprStr error)⟩

/-- Actual MemoryLifecycle owns kind/layout checks and removed/dead maps; the
callback owns ordered diagnostic/race/TB/sync/address-release machine effects. -/
def deallocate [DecidableEq K] (h : DeallocationHooks K User Payload)
    (pointer : Pointer (Option Provenance)) (oldLayout : Option (Size × Align))
    (kind : MemoryKind K) : MachineHooks.M K User Unit := do
  let state ← get
  let hooks : MemoryDeallocationHooks Provenance BorrowTree K (PlaceMachine.AccessState K User) ProvenanceExtra :=
    { synchronizeMemory := fun memory access => {access with machine := {access.machine with memory}}
      resolvePointer := h.resolvePointer
      beforeDeallocation := callback h }
  let result := MemoryLifecycle.deallocatePtrWith state.machine.memory ⟨state.machine,none⟩ pointer oldLayout kind hooks
  let mut machine := {result.hooks.machine with memory := result.memory}
  if let some (id, _) := result.detached then
    let registry := h.extras.get machine.user
    machine := {machine with
      user := h.extras.put machine.user
        {registry with allocations := registry.allocations.filter fun entry => entry.1 != id}
      raceAllocations := machine.raceAllocations.filter fun entry => entry.1 != id}
  modify fun state => {state with machine}
  if let some (_, detached) := result.detached then
    if detached.allocation.nativeBuffer.isSome then
      let some drop := h.nativeDrop | throw (.invalidProgram "native detached backing lacks drop capability")
      drop detached.allocation
  match result.outcome with
  | .ok () => pure ()
  | .error error => throw (result.hooks.pendingError.getD (h.error error))
end Miri.Interpreter.AllocationMachine
