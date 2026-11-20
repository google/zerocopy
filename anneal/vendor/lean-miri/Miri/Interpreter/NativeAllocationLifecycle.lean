import Miri.Interpreter.NativeAllocBytes
import Miri.Memory.MemoryState
import Miri.Interpreter.Step
import Miri.Interpreter.AllocationMachine

/-! Actual native byte ownership on the canonical Allocation/MemoryState.
Backing is allocated before AllocId reservation; failed insertion drops only
uninserted backing. Deallocation drops the detached allocation on every return,
including source validation/hook failures, as Rust's local ownership requires. -/
namespace Miri.Interpreter.NativeAllocationLifecycle
open Miri.ABI Miri.Memory
structure Backing (S : Type) where
  isolated : Bool
  zeroed : Size → Align → EStateM StepError S (Option NativeAllocBytes.Buffer)
  fromBytes : Array UInt8 → Align → EStateM StepError S NativeAllocBytes.Buffer
  copyInto : NativeAllocBytes.Buffer → Array UInt8 → EStateM StepError S Unit
  snapshot : NativeAllocBytes.Buffer → EStateM StepError S (Array UInt8)
  release : NativeAllocBytes.Buffer → EStateM StepError S Unit

/-- Lift the one canonical machine-owned allocator into the full interpreter
state, retaining its current stack and all machine mutations on errors. -/
def liftMachineAction (action : EStateM StepError (MachineHooks.MachineState K U) A) :
    EStateM StepError (MachineHooks.State K U) A := fun state =>
  match action state.machine with
  | .ok value machine => .ok value {state with machine}
  | .error error machine => .error error {state with machine}

def liftBacking (backing : Backing (MachineHooks.MachineState K U)) : Backing (MachineHooks.State K U) where
  isolated := backing.isolated
  zeroed := fun size align => liftMachineAction (backing.zeroed size align)
  fromBytes := fun bytes align => liftMachineAction (backing.fromBytes bytes align)
  copyInto := fun buffer bytes => liftMachineAction (backing.copyInto buffer bytes)
  snapshot := fun buffer => liftMachineAction (backing.snapshot buffer)
  release := fun buffer => liftMachineAction (backing.release buffer)

structure Access (S Prov Extra K H : Type) where
  memory : S → MemoryState Prov Extra K
  hooks : S → H
  synchronizeMemory : MemoryState Prov Extra K → H → H
  put : S → MemoryState Prov Extra K → H → S

def buffer (allocation : Allocation Prov Extra) : Option NativeAllocBytes.Buffer := do
  let owner ← allocation.nativeBuffer
  pure ⟨owner.pointer,⟨owner.layoutSize,owner.layoutAlign⟩⟩

def address (allocation : Allocation Prov Extra) : Except String Nat := do
  let some owner := allocation.nativeBuffer | throw "allocation has no native byte owner"
  if owner.pointer == 0 then throw "allocation has null native byte owner"
  pure owner.pointer

/-- Fresh `from_bytes` ownership for ordinary cloning/global-allocator mode.
Native compiler globals must instead take their already prepared buffer from
source prepared_alloc_bytes; they must not select this fresh allocator. -/
def prepareBytes (backing : Backing S) (bytes : Array UInt8) (align : Align) :
    EStateM StepError S (Array UInt8 × Option NativeBufferOwnership) := do
  let value ← backing.fromBytes bytes align
  pure (bytes,some ⟨value.pointer,backing.isolated,value.layout.size,value.layout.align⟩)

def alignmentBytes (align : Align) : EStateM StepError S Nat := do
  match align.bytesNat with
  | .ok value => pure value
  | .error error => throw (.invalidProgram s!"native byte alignment: {reprStr error}")

def commitBytes (backing : Backing S) (owner : NativeBufferOwnership) (bytes : Array UInt8) (align : Align) :
    EStateM StepError S Unit := do
  unless owner.isolated == backing.isolated && owner.pointer != 0 do
    throw (.invalidProgram "native byte commit owner mismatch")
  let alignment ← alignmentBytes align
  unless bytes.size == owner.layoutSize && owner.pointer % alignment == 0 do
    throw (.invalidProgram "native byte commit layout mismatch")
  backing.copyInto ⟨owner.pointer,⟨owner.layoutSize,owner.layoutAlign⟩⟩ bytes

def releaseBytes (backing : Backing S) (owner : NativeBufferOwnership) (_size : Size) (_align : Align) :
    EStateM StepError S Unit := do
  unless owner.isolated == backing.isolated && owner.pointer != 0 do
    throw (.invalidProgram "native byte release owner mismatch")
  backing.release ⟨owner.pointer,⟨owner.layoutSize,owner.layoutAlign⟩⟩

private def attach (backing : Backing S) (value : NativeAllocBytes.Buffer)
    (allocation : Allocation Prov Extra) : EStateM StepError S (Allocation Prov Extra) := do
  match allocation.attachNativeBuffer ⟨value.pointer,backing.isolated,value.layout.size,value.layout.align⟩ with
  | .ok allocation => pure allocation
  | .error reason => throw (.invalidProgram reason)

/-- Actual native `Allocation::try_new`; host null leaves the ID supply intact.
The zero snapshot validates the external storage contract before reservation. -/
def createZeroed (backing : Backing S) (size : Size) (align : Align) (init : AllocInit) :
    EStateM StepError S (Except AllocError (Allocation Prov Unit)) := do
  let some value ← backing.zeroed size align | return .error .hostMemoryExhausted
  let outcome ← try
    let bytes ← backing.snapshot value
    match Allocation.tryNew (Prov := Prov) size align init (fun _ _ => some bytes) with
    | .error error => pure (.error error)
    | .ok allocation => return .ok (← attach backing value allocation)
    catch error =>
      backing.release value
      throw error
  if let .error _ := outcome then backing.release value
  pure outcome

/-- Ordinary owned-byte clone preserves mask/provenance/extras and receives
fresh ownership. Native compiler globals use source prepared buffers instead. -/
def cloneBytes (backing : Backing S) (allocation : Allocation Prov Extra) :
    EStateM StepError S (Allocation Prov Extra) := do
  let bytes ← match allocation.inspectWithUninitAndPtrOutsideInterpreter 0 allocation.len with
    | .ok bytes => pure bytes
    | .error error => throw (.invalidProgram s!"native clone byte inspection: {reprStr error}")
  let value ← backing.fromBytes bytes allocation.align
  -- clone ownership must not alias the source owner.
  let allocation := allocation.withoutNativeBuffer
  try attach backing value allocation
  catch error =>
    backing.release value
    throw error

def releaseAllocation (backing : Backing S) (allocation : Allocation Prov Extra) : EStateM StepError S Unit := do
  if let some owner := allocation.nativeBuffer then
    unless owner.isolated == backing.isolated do throw (.invalidProgram "native allocation allocator-mode mismatch")
    releaseBytes backing owner allocation.byteSize allocation.align

/-- Direct source allocation lifecycle; no FFI-time materialization. -/
def allocate [DecidableEq K] (access : Access S Prov Extra K H) (backing : Backing S)
    (size : Size) (align : Align) (kind : MemoryKind K) (init : AllocInit)
    (maximum : Size) (globalKind : Option (MemoryKind K))
    (initExtra : MemoryState Prov Extra K → H → AllocId → MemoryKind K → Size → Align →
      MemoryStateHookResult Prov Extra K H Extra)
    (adjustRoot : MemoryState Prov Extra K → H → AllocId → MemoryKind K →
      MemoryStateHookResult Prov Extra K H (Pointer Prov)) :
    EStateM StepError S (Except MemoryLifecycleError (Pointer Prov)) := do
  let allocation ← createZeroed (Prov := Prov) backing size align init
  let allocation ← match allocation with
    | .ok allocation => pure allocation
    | .error error => return .error (.allocation error)
  let state ← get
  let result := MemoryLifecycle.insertAllocation (access.memory state) (access.hooks state)
    access.synchronizeMemory
    allocation kind maximum globalKind initExtra adjustRoot
  set (access.put state result.memory result.hooks)
  let retained := result.memory.live.any fun (_,entry) => entry.allocation.nativeBuffer == allocation.nativeBuffer
  unless retained do releaseAllocation backing allocation
  pure result.outcome

def deallocate [DecidableEq K] (access : Access S Prov Extra K H) (backing : Backing S)
    (pointer : Pointer (Option Prov)) (oldLayout : Option (Size × Align)) (kind : MemoryKind K)
    (hooks : MemoryLifecycleHooks Prov Extra K H PE) : EStateM StepError S (Except MemoryLifecycleError Unit) := do
  let state ← get
  let memory := access.memory state
  let hooksState := access.synchronizeMemory memory (access.hooks state)
  let result := MemoryLifecycle.deallocatePtr memory hooksState pointer oldLayout kind hooks
  let finalHooks := access.synchronizeMemory result.memory result.hooks
  set (access.put state result.memory finalHooks)
  if let some (_, detached) := result.detached then
    releaseAllocation backing detached.allocation
  pure result.outcome
/-- Canonical stack/temporary creation selects native source storage, retaining
existing diagnostic/TB/race/address operations and their order. -/
def bindAllocation (backing : Backing (MachineHooks.State K U))
    (config : PlaceMachine.AllocationConfig K U) : PlaceMachine.AllocationConfig K U :=
  {config with
    nativeStorage := some (createZeroed backing)
    nativeDrop := some (releaseAllocation backing)}

def bindDeallocation (backing : Backing (MachineHooks.State K U))
    (hooks : AllocationMachine.DeallocationHooks K U P) : AllocationMachine.DeallocationHooks K U P :=
  {hooks with nativeDrop := some (releaseAllocation backing)}
end Miri.Interpreter.NativeAllocationLifecycle
