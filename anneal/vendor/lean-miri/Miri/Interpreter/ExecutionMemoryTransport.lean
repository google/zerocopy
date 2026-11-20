import Miri.Interpreter.ExecutionStateTransport
import Miri.Interpreter.AllocationMachine

/-! Lawful canonical state reassociation for memory/allocation capabilities.
All byte/tree/clock/global-materialization effects and failed touched prefixes
stay in the same machine. No replacement memory operations are introduced. -/
namespace Miri.Interpreter.ExecutionMemoryTransport
open Miri.Memory Miri.TreeBorrows
open ExecutionStateTransport

def machineIn (s : PlaceMachine.Machine K (Outer U)) : PlaceMachine.Machine K (Inner U) :=
  {s with user := toInner s.user}
def machineOut (s : PlaceMachine.Machine K (Inner U)) : PlaceMachine.Machine K (Outer U) :=
  {s with user := toOuter s.user}
def machineAction (a : PlaceMachine.MachineM K (Inner U) A) : PlaceMachine.MachineM K (Outer U) A := fun s =>
  match a (machineIn s) with
  | .ok v after => .ok v (machineOut after)
  | .error e after => .error e (machineOut after)
def accessIn (s : PlaceMachine.AccessState K (Outer U)) : PlaceMachine.AccessState K (Inner U) :=
  ⟨machineIn s.machine,s.pendingError⟩
def accessOut (s : PlaceMachine.AccessState K (Inner U)) : PlaceMachine.AccessState K (Outer U) :=
  ⟨machineOut s.machine,s.pendingError⟩
private def result (r : MachineHookResult (PlaceMachine.AccessState K (Inner U)) A) :
    MachineHookResult (PlaceMachine.AccessState K (Outer U)) A := ⟨accessOut r.state,r.outcome⟩

def access (h : PlaceMachine.AccessConfig K (Inner U)) : PlaceMachine.AccessConfig K (Outer U) where
  runtime := h.runtime
  ghostMode := h.ghostMode
  globalKind := h.globalKind
  globalHooks := {
    synchronizeMemory := fun memory s => accessOut (h.globalHooks.synchronizeMemory memory (accessIn s))
    evaluateStaticInitializer := fun memory s d =>
      let r := h.globalHooks.evaluateStaticInitializer memory (accessIn s) d
      ⟨r.memory,accessOut r.state,r.outcome⟩
    beforeAccessGlobal := fun memory s id a d write =>
      let r := h.globalHooks.beforeAccessGlobal memory (accessIn s) id a d write
      ⟨r.memory,accessOut r.state,r.outcome⟩
    adjustGlobalAllocation := fun memory s id a =>
      let r := h.globalHooks.adjustGlobalAllocation memory (accessIn s) id a
      ⟨r.memory,accessOut r.state,r.outcome⟩ }
  dynamicLayout := fun memory s place =>
    let r := h.dynamicLayout memory (accessIn s) place
    ⟨r.memory,accessOut r.hooks,r.outcome⟩
  resolvePointer := fun memory pointer size => machineAction (h.resolvePointer memory pointer size)
  beforeAllocationAccess := fun id => machineAction (h.beforeAllocationAccess id)
  diagnostic := fun write id range => machineAction (h.diagnostic write id range)
  weakMemoryWrite := fun id range => machineAction (h.weakMemoryWrite id range)
  syncAccess := fun write id range => machineAction (h.syncAccess write id range)
  retainTouched := fun s touched => machineOut (h.retainTouched (machineIn s) touched)
  memoryError := h.memoryError

def allocation (h : PlaceMachine.AllocationConfig K (Inner U)) : PlaceMachine.AllocationConfig K (Outer U) where
  maximumObjectSize := h.maximumObjectSize
  zeroedStorage := h.zeroedStorage
  nativeStorage := h.nativeStorage.map fun create size align init => action (create size align init)
  nativeDrop := h.nativeDrop.map fun drop allocation => action (drop allocation)
  diagnostic := fun id size align => machineAction (h.diagnostic id size align)
  allocationTail := fun id size align => machineAction (h.allocationTail id size align)
  adjustRootAddress := fun id tag => action (h.adjustRootAddress id tag)

def extras (h : MemoryExtras.Hooks K (Inner U) P) : MemoryExtras.Hooks K (Outer U) P where
  get := fun u => h.get (toInner u)
  put := fun u value => toOuter (h.put (toInner u) value)
  onAccess := fun p kind => machineAction (h.onAccess p kind)
  weakError := h.weakError

def lifecycle (h : MemoryLifecycleHooks Provenance BorrowTree K (PlaceMachine.AccessState K (Inner U)) ProvenanceExtra) :
    MemoryLifecycleHooks Provenance BorrowTree K (PlaceMachine.AccessState K (Outer U)) ProvenanceExtra where
  synchronizeMemory := fun memory s => accessOut (h.synchronizeMemory memory (accessIn s))
  initLocalAllocation := fun memory s id kind size align =>
    let r := h.initLocalAllocation memory (accessIn s) id kind size align
    ⟨r.memory,accessOut r.state,r.outcome⟩
  adjustRootPointer := fun memory s id kind =>
    let r := h.adjustRootPointer memory (accessIn s) id kind
    ⟨r.memory,accessOut r.state,r.outcome⟩
  resolvePointer := fun memory s ptr size =>
    let r := h.resolvePointer memory (accessIn s) ptr size
    ⟨r.memory,accessOut r.state,r.outcome⟩
  beforeDeallocation := fun memory s a ptr id prov size align kind =>
    let r := h.beforeDeallocation memory (accessIn s) a ptr id prov size align kind
    ⟨r.memory,accessOut r.state,r.outcome⟩
  copyMemory := fun s memory src dest size read align =>
    let r := h.copyMemory (accessIn s) memory src dest size read align
    ⟨r.memory,accessOut r.hooks,r.outcome⟩

def deallocation (h : AllocationMachine.DeallocationHooks K (Inner U) P) :
    AllocationMachine.DeallocationHooks K (Outer U) P where
  extras := extras h.extras
  nativeDrop := h.nativeDrop.map fun drop allocation => action (drop allocation)
  error := h.error
  resolvePointer := fun memory state ptr size =>
    let result := h.resolvePointer memory (accessIn state) ptr size
    ⟨result.memory,accessOut result.state,result.outcome⟩
  diagnostic := fun id => machineAction (h.diagnostic id)
  currentSpan := machineAction h.currentSpan
  freeAllocId := fun id size align kind => machineAction (h.freeAllocId id size align kind)
  retainDetached := fun a s => machineOut (h.retainDetached a (machineIn s))
end Miri.Interpreter.ExecutionMemoryTransport
