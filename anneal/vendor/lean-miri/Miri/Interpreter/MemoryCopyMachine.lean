import Miri.Interpreter.PointerMachine
import Miri.Interpreter.MemoryExtras

/-! Concrete mem_copy_repeatedly access adapter. Actual Allocation copying
retains initialization and partial provenance; PlaceMachine supplies ordered
race/weak/TB/sync callbacks, including partial failed tree mutation. -/
namespace Miri.Interpreter.MemoryCopyMachine
open Miri.ABI Miri.Memory Miri.TreeBorrows
abbrev User := PointerMachine.User
abbrev GenericState K U := PlaceMachine.AccessState K U
abbrev State K U := GenericState K (User U)

private def bridge (state : GenericState K U) (action : PlaceMachine.MachineM K U A) :
    MachineHookResult (GenericState K U) A :=
  match action state.machine with
  | .ok value machine => ⟨{state with machine},.ok value⟩
  | .error error machine => ⟨⟨machine,some error⟩,.error (reprStr error)⟩

private def bridgeMemory (memory : MemoryState Provenance BorrowTree K)
    (state : GenericState K U) (action : PlaceMachine.MachineM K U A) :
    MemoryStateHookResult Provenance BorrowTree K (GenericState K U) A :=
  match action {state.machine with memory} with
  | .ok value machine => ⟨machine.memory,{state with machine},.ok value⟩
  | .error error machine => ⟨machine.memory,⟨machine,some error⟩,.error (reprStr error)⟩

private def access (config : PlaceMachine.AccessConfig K U) (arithmetic : PointerArithmetic)
    (pointer : Pointer (Option Provenance)) (size : Size) :
    PlaceMachine.MachineM K U (Option (AllocId × Size × ProvenanceExtra)) := do
  let signed ← match sizeAsI64 size with
    | .ok value => pure value
    | .error error => throw (.undefinedBehavior (toString error))
  if signed == 0 then return none
  let memory := (← get).memory
  let resolved ← config.resolvePointer memory pointer signed
  match checkAndDerefPtr arithmetic pointer signed .memoryAccess (fun _ _ => resolved) memory.getAllocInfo with
  | .ok result => return result.map fun checked =>
      (checked.pointer.allocId,checked.pointer.offset,checked.pointer.extra)
  | .error (.allocationLookup (.unavailable id)) => throw (.callback s!"missing allocation metadata {id.value}")
  | .error error => throw (.undefinedBehavior (toString error))

/-- Probe is source's nonchecking pointer_try_get_alloc_id. Checked pointer
access has already run; probe failures do not independently diagnose UB. -/
private def probe (addresses : U → AllocAddresses.GlobalAddressState) (arithmetic : PointerArithmetic)
    (memory : MemoryState Provenance BorrowTree K) (state : GenericState K U)
    (pointer : Pointer (Option Provenance)) (size : UInt64) : Option AllocId := do
  let provenance ← pointer.provenance
  let lookup : AllocAddresses.AddressLookupHooks := {
    sizeOf := fun id => (memory.getAllocInfo id).toOption.map (·.size)
    isLive := fun id => some (memory.isAllocLive id) }
  let result ← ((addresses state.machine.user).ptrGetAlloc (Pointer.new provenance pointer.offset)
    (Int64.ofInt size.toNat) lookup arithmetic).toOption
  return (← result).1

private def memoryAccess [DecidableEq K] (config : PlaceMachine.AccessConfig K U)
    (write : Bool) (state : GenericState K U) (memory : MemoryState Provenance BorrowTree K)
    (allocation : Allocation Provenance BorrowTree) (_pointer : Pointer (Option Provenance))
    (id : AllocId) (provenance : ProvenanceExtra) (range : AllocRange) :
    MemoryCopyResult Provenance BorrowTree K (GenericState K U) := Id.run do
  let state := {state with machine := {state.machine with memory}}
  let accessed := PlaceMachine.memoryAccess config write state allocation.extra id provenance range
  match memory.setLiveAllocation id (allocation.setExtra accessed.extra) with
  | .ok memory => return ⟨memory,accessed.state,accessed.outcome⟩
  | .error error =>
    let error := StepError.invalidProgram s!"copy allocation disappeared: {reprStr error}"
    return ⟨memory,{accessed.state with pendingError := some error},.error (reprStr error)⟩

def genericHooks [DecidableEq K] (config : PlaceMachine.AccessConfig K U)
    (addresses : U → AllocAddresses.GlobalAddressState) (arithmetic : PointerArithmetic) : MemoryCopyHooks Provenance BorrowTree K (GenericState K U) ProvenanceExtra where
  synchronizeMemory := fun memory state => {state with machine := {state.machine with memory}}
  pointerAccess := fun memory state pointer size => bridgeMemory memory state (access config arithmetic pointer size)
  tryGetAllocId := probe addresses arithmetic
  beforeAllocationAccess := fun memory state id => bridgeMemory memory state (config.beforeAllocationAccess id)
  beforeMemoryRead := memoryAccess config false
  beforeMemoryWrite := memoryAccess config true

/-- Real bytes, init-mask, provenance, and overlapping-copy operation. Both
machine effects and allocation-tree mutations commit before any failure. -/
def genericCopy [DecidableEq K] (config : PlaceMachine.AccessConfig K U)
    (addresses : U → AllocAddresses.GlobalAddressState) (arithmetic : PointerArithmetic) (source dest : Pointer (Option Provenance))
    (size : Size) (repeatCount : UInt64) (nonoverlapping : Bool) :
    MachineHooks.M K U Unit := do
  let state ← get
  let result := MemoryLifecycle.memCopyRepeatedly state.machine.memory ⟨state.machine,none⟩
    source dest size repeatCount nonoverlapping arithmetic.pointerSize (genericHooks config addresses arithmetic)
  modify fun state => {state with machine := {result.hooks.machine with memory := result.memory}}
  match result.outcome with
  | .ok () => pure ()
  | .error error => throw (result.hooks.pendingError.getD (.callback s!"memory copy: {reprStr error}"))
/-- Compatibility adapter for the original PointerMachine user record. -/
def hooks [DecidableEq K] (config : PlaceMachine.AccessConfig K (User U))
    (arithmetic : PointerArithmetic) : MemoryCopyHooks Provenance BorrowTree K (State K U) ProvenanceExtra :=
  genericHooks config PointerMachine.User.addresses arithmetic

def copy [DecidableEq K] (config : PlaceMachine.AccessConfig K (User U))
    (arithmetic : PointerArithmetic) (source dest : Pointer (Option Provenance))
    (size : Size) (repeatCount : UInt64) (nonoverlapping : Bool) :
    MachineHooks.M K (User U) Unit :=
  genericCopy config PointerMachine.User.addresses arithmetic source dest size repeatCount nonoverlapping
end Miri.Interpreter.MemoryCopyMachine
