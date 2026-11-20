import Miri.Interpreter.DynamicLayout
import Miri.Interpreter.MemoryCopyMachine

/-! Complete raw global/local lookup around memory.rs:1490–1638 memcopy.
Cow::Borrowed sources remain detached; only Owned source conversions cache.
Destination globals materialize before WriteToReadOnly, preserving that cache
on UB. Source snapshots survive destination conversion and overlapping writes. -/
namespace Miri.Interpreter.GlobalMemoryCopyMachine
open Miri.ABI Miri.Memory Miri.TreeBorrows
abbrev User := PointerMachine.User
abbrev M K U A := PointerMachine.M K U A

private def hook (action : PlaceMachine.AccessState K U → MachineHookResult
    (PlaceMachine.AccessState K U) A) : MachineHooks.M K U A := do
  let state ← get
  let result := action ⟨state.machine,none⟩
  modify fun state => {state with machine := result.state.machine}
  match result.outcome with
  | .ok value => pure value
  | .error error => throw (result.state.pendingError.getD (.callback error))

private def memoryHook (action : PlaceMachine.AccessState K U →
    MemoryStateHookResult Provenance BorrowTree K (PlaceMachine.AccessState K U) A) :
    MachineHooks.M K U A := do
  let state ← get
  let result := action ⟨state.machine,none⟩
  modify fun state => {state with machine := {result.state.machine with memory := result.memory}}
  match result.outcome with
  | .ok value => pure value
  | .error error => throw (result.state.pendingError.getD (.callback error))

private def raw [DecidableEq K] (config : PlaceMachine.AccessConfig K U)
    (write : Bool) (id : AllocId) : MachineHooks.M K U (Allocation Provenance BorrowTree) := do
  let state ← get
  let result := if write then
      MemoryLifecycle.getAllocRawMut state.machine.memory ⟨state.machine,none⟩ id config.globalKind config.globalHooks
    else MemoryLifecycle.getAllocRaw state.machine.memory ⟨state.machine,none⟩ id config.globalKind config.globalHooks
  modify fun state => {state with machine := {result.hooks.machine with memory := result.memory}}
  match result.outcome with
  | .ok allocation => return allocation
  | .error error => throw (result.hooks.pendingError.getD
      (config.memoryError (.pointerAccess (.rawAccess error))))

/-- Reads may touch a borrowed global's interior extra. Keep its snapshot via
required touched-state policy, never eagerly promote it to a local allocation. -/
private def access [DecidableEq K] (config : PlaceMachine.AccessConfig K U)
    (write : Bool) (allocation : Allocation Provenance BorrowTree) (id : AllocId)
    (provenance : ProvenanceExtra) (range : AllocRange) : MachineHooks.M K U (Allocation Provenance BorrowTree) := do
  let state ← get
  let result := PlaceMachine.memoryAccess config write ⟨state.machine,none⟩ allocation.extra id provenance range
  let allocation := allocation.setExtra result.extra
  let machine := result.state.machine
  let memory ← if machine.memory.live.any (fun entry => entry.1 == id) then
      match machine.memory.setLiveAllocation id allocation with
      | .ok memory => pure memory
      | .error error => throw (config.memoryError (.memoryUpdate error))
    else pure machine.memory
  modify fun state => {state with machine := config.retainTouched {machine with memory} (some ⟨id,range,allocation⟩)}
  match result.outcome with
  | .ok () => return allocation
  | .error error => throw (result.state.pendingError.getD (.callback error))

private def snapshotChecks (config : PlaceMachine.AccessConfig K U)
    (source : Allocation Provenance BorrowTree) (range : AllocRange) (pointerSize : Size) : MachineHooks.M K U Unit := do
  let bytes ← match source.getBytesUnchecked (allocRange Size.ZERO source.byteSize) with
    | .ok bytes => pure bytes
    | .error error => throw (config.memoryError (.allocation error))
  match source.provenanceMap.prepareCopy range bytes pointerSize with
  | .ok _ => pure ()
  | .error error => throw (config.memoryError (.allocation (.provenance error)))
  match source.initializationMask.prepareCopy range with
  | .ok _ => pure ()
  | .error error => throw (config.memoryError (.allocation (.memory error)))

/-- Two pointer checks precede source probe (even size zero), source lookup,
read, destination lookup/mutability, destination before_alloc_access, write,
then actual snapshot copy. num_copies=0 still reads a nonzero source. -/
def genericCopy [DecidableEq K] (config : PlaceMachine.AccessConfig K U)
    (addresses : U → AllocAddresses.GlobalAddressState)
    (arithmetic : PointerArithmetic) (source dest : Pointer (Option Provenance))
    (size : Size) (repeatCount : UInt64) (nonoverlapping : Bool) : MachineHooks.M K U Unit := do
  let hooks := MemoryCopyMachine.genericHooks config addresses arithmetic
  let srcParts ← memoryHook (fun state => hooks.pointerAccess state.machine.memory state source size)
  let destSize ← match Size.mul size repeatCount with
    | .ok size => pure size
    | .error error => throw (config.memoryError (.allocation (.memory (.sizeError error))))
  let dstParts ← memoryHook (fun state => hooks.pointerAccess state.machine.memory state dest destSize)
  let probeState ← get
  if let some id := hooks.tryGetAllocId probeState.machine.memory ⟨probeState.machine,none⟩ source size.bytes then
    memoryHook (fun state => hooks.beforeAllocationAccess state.machine.memory state id)
  let some (srcId,srcOffset,srcProv) := srcParts | return ()
  let srcAlloc ← raw config false srcId
  if config.ghostMode then throw (.invalidProgram "cannot copy during validation")
  let range := allocRange srcOffset size
  let srcAlloc ← access config false srcAlloc srcId srcProv range
  let some (dstId,dstOffset,dstProv) := dstParts | return ()
  snapshotChecks config srcAlloc range arithmetic.pointerSize
  let dstAlloc ← raw config true dstId
  memoryHook (fun state => hooks.beforeAllocationAccess state.machine.memory state dstId)
  let dstAlloc ← access config true dstAlloc dstId dstProv (allocRange dstOffset destSize)
  let result := Allocation.copyRepeatedly srcAlloc range dstOffset repeatCount arithmetic.pointerSize
    (srcId == dstId) nonoverlapping dstAlloc
  let (outcome,allocation) := match result with
    | .ok () allocation => (Except.ok (),allocation)
    | .error error allocation => (Except.error error,allocation)
  let state ← get
  let memory ← match state.machine.memory.setLiveAllocation dstId allocation with
    | .ok memory => pure memory
    | .error error => throw (config.memoryError (.memoryUpdate error))
  set {state with machine := {state.machine with memory}}
  match outcome with
  | .ok () => pure ()
  | .error error => throw (config.memoryError (.allocation error))
/-- Source typed-copy slow path shared by intrinsic and MIR copies. Dynamic
sizes precede physical copying; misalignment is reported only after copying. -/
def typedCopy [DecidableEq K] (config : PlaceMachine.AccessConfig K U)
    (addresses : U → AllocAddresses.GlobalAddressState) (arithmetic : PointerArithmetic)
    (dynamic : DynamicLayoutHooks Provenance (MachineHooks.State K U) C)
    (fuel : Nat) (debugAssertions : Bool) (choice : C)
    (source dest : MPlaceTy Provenance) : MachineHooks.M K U Unit := do
  let some (size,_) ← DynamicLayout.sizeAndAlignFromMeta dynamic choice fuel dest.mplace.metadata dest.layout
    | throw (.invalidProgram "copy requires dynamically sized destination")
  if debugAssertions then
    let some (sourceSize,_) ← DynamicLayout.sizeAndAlignFromMeta dynamic choice fuel source.mplace.metadata source.layout
      | throw (.invalidProgram "copy requires dynamically sized source")
    if sourceSize != size then throw (.invalidProgram "copy dynamic size mismatch")
  else if source.layout.layout.size != dest.layout.layout.size then
    throw (.invalidProgram "copy fixed size mismatch")
  genericCopy config addresses arithmetic source.mplace.ptr dest.mplace.ptr size 1 true
  if let some error := source.mplace.misaligned then throw (.undefinedBehavior s!"copy source misalignment: {repr error}")
  if let some error := dest.mplace.misaligned then throw (.undefinedBehavior s!"copy destination misalignment: {repr error}")

/-- Original PointerMachine-shaped API, retaining the same implementation. -/
def copy [DecidableEq K] (config : PlaceMachine.AccessConfig K (User U))
    (arithmetic : PointerArithmetic) (source dest : Pointer (Option Provenance))
    (size : Size) (repeatCount : UInt64) (nonoverlapping : Bool) : M K U Unit :=
  genericCopy config PointerMachine.User.addresses arithmetic source dest size repeatCount nonoverlapping
end Miri.Interpreter.GlobalMemoryCopyMachine
