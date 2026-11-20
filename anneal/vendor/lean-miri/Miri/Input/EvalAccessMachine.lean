import Miri.Input.EvalCoreMachine
import Miri.Input.EvalGlobalAllocationMachine
import Miri.Input.EvalDynamicMemory
import Miri.Interpreter.MemoryErrors

/-! Direct memory-access capability construction. Compiler globals use the
actual lazy conversion and global-specific extra initialization. Byte backing,
root addressing, external-allocation access and diagnostic retention remain
real source capabilities; memory effects use the canonical machine.
Sources: machine.rs before_memory_read/write; memory.rs get_alloc_raw. -/
namespace Miri.Input.EvalAccessMachine
open Miri.ABI Miri.Memory Miri.Interpreter
abbrev User := EvalCoreMachine.User
abbrev State := EvalCoreMachine.State

def make (p : CompilerProviders.Prepared) (image : AllocationImage.Imported)
    (maximum : Miri.ABI.Size) (fuel : Nat)
    (globals : GlobalAllocationHooks Provenance Miri.TreeBorrows.BorrowTree MiriMemoryKind
      (PlaceMachine.AccessState MiriMemoryKind (User Os R P H D O Aff B Host)))
    (pointers : PointerMachine.Hooks MiriMemoryKind
      (ValidityMachine.Control (EvalCoreMachine.Stored Os R P H D O Aff B Host)))
    (extras : MemoryExtras.Hooks MiriMemoryKind (User Os R P H D O Aff B Host) P)
     :
    PlaceMachine.AccessConfig MiriMemoryKind (User Os R P H D O Aff B Host) :=
  EvalBackendMachine.access {
    runtime := p.runtime.target
    ghostMode := false
    globalKind := some .global
    globalHooks := globals
    dynamicLayout := EvalDynamicMemory.resolver p image maximum fuel pointers
    resolvePointer := TypedMemoryProviders.resolvePointer pointers
    -- Pinned Machine::before_alloc_access default; Miri has no override.
    beforeAllocationAccess := fun _ => pure ()
    -- AccessedAlloc emission is display-only (diagnostics.rs::emit_diagnostic).
    diagnostic := fun _ _ _ => pure ()
    weakMemoryWrite := fun id range => MemoryExtras.nonAtomicWrite extras id range
    syncAccess := fun write id range => MemoryExtras.syncAccess extras write id range
    -- AllocationAccess commits Miri-owned extras in memory.live before every
    -- success/error result; touched is a borrowed diagnostic snapshot, not a
    -- second owner or an independent state-mutating policy.
    retainTouched := fun machine _ => machine
    memoryError := MemoryErrors.operand }
end Miri.Input.EvalAccessMachine
