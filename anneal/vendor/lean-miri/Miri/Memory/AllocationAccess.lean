import Miri.Memory.MemoryState

/-! Bounds-checked allocation access from pinned interpreter memory.rs.
Actual global materialization precedes bounds checking. Machine access hooks
remain explicit, and retain updated allocation extras even when they fail.
These helpers do not check alignment or perform byte loads/stores. -/
namespace Miri.Memory
open Miri.ABI

structure AllocationExtraHookResult (HookState Extra : Type) where
  state : HookState
  extra : Extra
  outcome : Except String Unit

structure AllocationAccessHooks (Prov Extra MachineKind HookState ProvExtra : Type) where
  /-- Outer error means unavailable machine semantics; inner error is the
  source's integer address that could not be resolved. -/
  resolvePointer : MemoryState Prov Extra MachineKind → HookState →
    Pointer (Option Prov) → Int →
    MachineHookResult HookState (Except UInt64 (ResolvedPointer ProvExtra))
  beforeAllocationAccess : HookState → AllocId → MachineHookResult HookState Unit
  beforeMemoryRead : HookState → Extra → Pointer (Option Prov) →
    AllocId → ProvExtra → AllocRange → AllocationExtraHookResult HookState Extra
  beforeMemoryWrite : HookState → Extra → Pointer (Option Prov) →
    AllocId → ProvExtra → AllocRange → AllocationExtraHookResult HookState Extra

structure AllocationAccessRef (Prov Extra : Type) where
  allocId : AllocId
  range : AllocRange
  allocation : Allocation Prov Extra

inductive PtrAllocationError where
  | access (reason : AccessError)
  | rawAccess (reason : MemoryAccessError)
  | hookFailure (hook message : String)
  | cacheUpdate (reason : AllocationLookupError)
  deriving DecidableEq, Repr

structure PtrAllocationResult (Prov Extra MachineKind HookState α : Type) where
  memory : MemoryState Prov Extra MachineKind
  hooks : HookState
  /-- Snapshot also retained on failure for borrowed global allocation extras.
  Miri-owned allocations are simultaneously updated in `memory.live`. -/
  touched : Option (AllocationAccessRef Prov Extra)
  outcome : Except PtrAllocationError α

namespace AllocationAccess
variable {Prov Extra MachineKind HookState ProvExtra : Type}

/-- Unified implementation of source `get_ptr_alloc` and `get_ptr_alloc_mut`.
`write` selects exactly their different raw lookup and access-hook order. -/
private def getPtrAllocation [DecidableEq MachineKind]
    (initialMemory : MemoryState Prov Extra MachineKind) (initialHooks : HookState)
    (target : PointerArithmetic) (ptr : Pointer (Option Prov)) (size : Size)
    (ghostMode : Bool) (globalKind : Option MachineKind)
    (globalHooks : GlobalAllocationHooks Prov Extra MachineKind HookState)
    (accessHooks : AllocationAccessHooks Prov Extra MachineKind HookState ProvExtra)
    (write : Bool) :
    PtrAllocationResult Prov Extra MachineKind HookState
      (Option (AllocationAccessRef Prov Extra)) := Id.run do
  let mut memory := initialMemory
  let mut hookState := initialHooks
  let signedSize ← match sizeAsI64 size with
    | .ok amount => pure amount
    | .error error => return ⟨memory, hookState, none, .error (.access error)⟩
  let mut checked : Option (ResolvedPointer ProvExtra × AllocationAccessRef Prov Extra) := none
  if signedSize != 0 then
    let resolution := accessHooks.resolvePointer memory hookState ptr signedSize
    hookState := resolution.state
    let resolved ← match resolution.outcome with
      | .error message => return ⟨memory, hookState, none,
          .error (.hookFailure "ptrTryGetAllocId" message)⟩
      | .ok (.error address) => return ⟨memory, hookState, none,
          .error (.access (.danglingIntegerPointer address signedSize .memoryAccess))⟩
      | .ok (.ok resolved) => pure resolved
    let raw := if write then
        MemoryLifecycle.getAllocRawMut memory hookState resolved.allocId globalKind globalHooks
      else MemoryLifecycle.getAllocRaw memory hookState resolved.allocId globalKind globalHooks
    memory := raw.memory
    hookState := raw.hooks
    let allocation ← match raw.outcome with
      | .ok allocation => pure allocation
      | .error error => return ⟨memory, hookState, none, .error (.rawAccess error)⟩
    let reference : AllocationAccessRef Prov Extra :=
      ⟨resolved.allocId, allocRange resolved.offset size, allocation⟩
    match checkedBounds target resolved.allocId allocation.byteSize resolved.offset signedSize .memoryAccess with
    | .error error => return ⟨memory, hookState, some reference, .error (.access error)⟩
    | .ok () => checked := some (resolved, reference)
  if !ghostMode then
    let accessId ← if write then
        pure (checked.map fun (_, reference) => reference.allocId)
      else do
        -- The source deliberately resolves again, including size-zero reads.
        let resolution := accessHooks.resolvePointer memory hookState ptr signedSize
        hookState := resolution.state
        match resolution.outcome with
        | .error message => return ⟨memory, hookState, checked.map Prod.snd,
            .error (.hookFailure "ptrTryGetAllocId" message)⟩
        | .ok (.error _) => pure none
        | .ok (.ok resolved) => pure (some resolved.allocId)
    if let some accessId := accessId then
      let access := accessHooks.beforeAllocationAccess hookState accessId
      hookState := access.state
      if let .error message := access.outcome then
        return ⟨memory, hookState, checked.map Prod.snd,
          .error (.hookFailure "beforeAllocAccess" message)⟩
    if let some (resolved, reference) := checked then
      let access := if write then
          accessHooks.beforeMemoryWrite hookState reference.allocation.extra ptr
            reference.allocId resolved.extra reference.range
        else accessHooks.beforeMemoryRead hookState reference.allocation.extra ptr
            reference.allocId resolved.extra reference.range
      hookState := access.state
      let updated := { reference with allocation := reference.allocation.setExtra access.extra }
      -- Borrowed CTFE globals have no local cache entry. Miri's owned global
      -- conversions and all mutable accesses do have one.
      if memory.live.any (fun entry => entry.1 == reference.allocId) then
        match memory.setLiveAllocation reference.allocId updated.allocation with
        | .ok afterUpdate => memory := afterUpdate
        | .error error => return ⟨memory, hookState, some updated, .error (.cacheUpdate error)⟩
      checked := some (resolved, updated)
      if let .error message := access.outcome then
        return ⟨memory, hookState, some updated,
          .error (.hookFailure (if write then "beforeMemoryWrite" else "beforeMemoryRead") message)⟩
  let reference := checked.map Prod.snd
  return ⟨memory, hookState, reference, .ok reference⟩

def getPtrAlloc [DecidableEq MachineKind]
    (memory : MemoryState Prov Extra MachineKind) (hooksState : HookState)
    (target : PointerArithmetic) (ptr : Pointer (Option Prov)) (size : Size)
    (ghostMode : Bool) (globalKind : Option MachineKind)
    (globalHooks : GlobalAllocationHooks Prov Extra MachineKind HookState)
    (accessHooks : AllocationAccessHooks Prov Extra MachineKind HookState ProvExtra) :=
  getPtrAllocation memory hooksState target ptr size ghostMode globalKind globalHooks accessHooks false

def getPtrAllocMut [DecidableEq MachineKind]
    (memory : MemoryState Prov Extra MachineKind) (hooksState : HookState)
    (target : PointerArithmetic) (ptr : Pointer (Option Prov)) (size : Size)
    (ghostMode : Bool) (globalKind : Option MachineKind)
    (globalHooks : GlobalAllocationHooks Prov Extra MachineKind HookState)
    (accessHooks : AllocationAccessHooks Prov Extra MachineKind HookState ProvExtra) :=
  getPtrAllocation memory hooksState target ptr size ghostMode globalKind globalHooks accessHooks true

end AllocationAccess
end Miri.Memory

namespace Miri.Memory.AllocationAccess
open Miri.ABI
set_option autoImplicit false
set_option maxRecDepth 65536
set_option maxHeartbeats 4000000
variable {P E K H X : Type} [DecidableEq K]
/-- Internal edges compose the production positive mutable-access path. -/
theorem live_mut_of_edges (memory : MemoryState P E K) (hooks : H)
    (target : PointerArithmetic) (ptr : Pointer (Option P)) (size : Size)
    (kind : Option K) (global : GlobalAllocationHooks P E K H)
    (access : AllocationAccessHooks P E K H X) (id : AllocId)
    (entry : LocalAllocation P E K) (provenance : X) (amount : Int)
    (signed : sizeAsI64 size = .ok amount) (nonzero : amount ≠ 0)
    (resolve : access.resolvePointer memory hooks ptr amount = ⟨hooks,.ok (.ok ⟨id,Size.ZERO,provenance⟩)⟩)
    (live : memory.live.find? (fun row => row.1 == id) = some (id,entry))
    (mutable : entry.allocation.mutability = .Mut)
    (synchronize : global.synchronizeMemory memory hooks = hooks)
    (bounds : checkedBounds target id entry.allocation.byteSize Size.ZERO amount .memoryAccess = .ok ())
    (before : access.beforeAllocationAccess hooks id = ⟨hooks,.ok ()⟩)
    (write : access.beforeMemoryWrite hooks entry.allocation.extra ptr id provenance (allocRange Size.ZERO size) =
      ⟨hooks,entry.allocation.extra,.ok ()⟩)
    (last : (memory.live.filter (fun row => row.1 != id)).push (id,entry) = memory.live) :
    getPtrAllocMut memory hooks target ptr size false kind global access =
      ⟨memory,hooks,some ⟨id,allocRange Size.ZERO size,entry.allocation⟩,
        .ok (some ⟨id,allocRange Size.ZERO size,entry.allocation⟩)⟩ := by
  have sameExtra : entry.allocation.setExtra entry.allocation.extra = entry.allocation := by
    cases entry.allocation; rfl
  have cache : memory.setLiveAllocation id entry.allocation = .ok memory := by
    rw [MemoryState.setLiveAllocation_of_find memory id entry entry.allocation live]
    simp only [last]
  have raw : MemoryLifecycle.getAllocRawMut memory hooks id kind global =
      ⟨memory,hooks,.ok entry.allocation⟩ := by
    simp [MemoryLifecycle.getAllocRawMut,live,mutable,synchronize]
  unfold getPtrAllocMut getPtrAllocation
  rw [signed]
  dsimp only [Id.run,bind,Bind.bind,pure,Pure.pure]
  simp only [nonzero,bne_iff_ne,↓reduceIte]
  rw [resolve]
  dsimp only [bind,Bind.bind,pure,Pure.pure]
  rw [raw]
  dsimp only [bind,Bind.bind,pure,Pure.pure]
  rw [bounds]
  simp only [bind,Bind.bind,pure,Pure.pure]
  simp only [nonzero,↓reduceIte,Bool.not_false,Option.map_some]
  rw [before]
  dsimp only [bind,Bind.bind,pure,Pure.pure]
  rw [write]
  simp only [sameExtra]
  split <;> simp_all [cache,bind,Bind.bind,pure,Pure.pure]
end Miri.Memory.AllocationAccess
