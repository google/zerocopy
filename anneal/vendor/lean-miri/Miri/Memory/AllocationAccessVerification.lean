import Miri.Memory.AllocationAccess

/-! Narrow source-backed allocation-access contracts. These do not assert
that arbitrary supplied machine hooks implement the fixed Miri machine. -/
namespace Miri.Memory.AllocationAccess
open Miri.ABI
variable {Prov Extra MachineKind HookState ProvExtra : Type} [DecidableEq MachineKind]

theorem zero_write
    (memory : MemoryState Prov Extra MachineKind) (hooksState : HookState)
    (target : PointerArithmetic) (ptr : Pointer (Option Prov)) (ghostMode : Bool)
    (globalKind : Option MachineKind)
    (globalHooks : GlobalAllocationHooks Prov Extra MachineKind HookState)
    (accessHooks : AllocationAccessHooks Prov Extra MachineKind HookState ProvExtra) :
    getPtrAllocMut memory hooksState target ptr (Size.ofBytes 0) ghostMode
      globalKind globalHooks accessHooks = ⟨memory, hooksState, none, .ok none⟩ := by
  cases ghostMode <;> rfl

theorem zero_ghost_read
    (memory : MemoryState Prov Extra MachineKind) (hooksState : HookState)
    (target : PointerArithmetic) (ptr : Pointer (Option Prov))
    (globalKind : Option MachineKind)
    (globalHooks : GlobalAllocationHooks Prov Extra MachineKind HookState)
    (accessHooks : AllocationAccessHooks Prov Extra MachineKind HookState ProvExtra) :
    getPtrAlloc memory hooksState target ptr (Size.ofBytes 0) true
      globalKind globalHooks accessHooks = ⟨memory, hooksState, none, .ok none⟩ := by
  rfl

end Miri.Memory.AllocationAccess
