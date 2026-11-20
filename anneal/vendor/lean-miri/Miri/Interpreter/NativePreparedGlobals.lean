import Miri.Interpreter.NativeAllocationLifecycle
import Miri.Interpreter.GlobalAllocationMachine
import Miri.Interpreter.PointerMachine

/-! alloc_addresses/mod.rs:139–159,415–445. Real zeroed native backing is
reserved before address publication, kept in canonical alloc-address state by AllocId, removed before CTFE byte
copy, and transferred into Allocation ownership without a second allocation. -/
namespace Miri.Interpreter.NativePreparedGlobals
open Miri.ABI Miri.Memory
structure Access (S : Type) where
  get : S → Miri.Memory.AllocAddresses.GlobalAddressState
  put : S → Miri.Memory.AllocAddresses.GlobalAddressState → S
  isCompilerGlobal : S → AllocId → Bool

/-- The source store lives in alloc-address state, so raw-global materialization
cannot overwrite its ownership transfer when committing a MemoryState result. -/
def machineAccess : Access (MachineHooks.MachineState K (PointerMachine.User U)) where
  get := fun machine => machine.user.addresses
  put := fun machine addresses => {machine with user := {machine.user with addresses}}
  isCompilerGlobal := fun machine id => (machine.memory.findGlobal? id).isSome

def stateAccess : Access (MachineHooks.State K (PointerMachine.User U)) where
  get := fun state => state.machine.user.addresses
  put := fun state addresses => {state with machine := {state.machine with user := {state.machine.user with addresses}}}
  isCompilerGlobal := fun state id => (state.machine.memory.findGlobal? id).isSome

private def setAddresses (access : Access S) (memory : Miri.Memory.AllocAddresses.GlobalAddressState) : EStateM StepError S Unit :=
  modify fun state => access.put state memory

/-- Called precisely inside first native global address assignment. The source
allocates before try_insert, so even duplicate-ID failure follows allocation. -/
def reserve (access : Access S) (backing : NativeAllocationLifecycle.Backing S)
    (id : AllocId) (size : Size) (align : Align) : EStateM StepError S Nat := do
  let some value ← backing.zeroed size align
    | throw (.resourceExhaustion "Miri ran out of memory: cannot prepare global native allocation")
  let owner : NativeBufferOwnership := ⟨value.pointer,backing.isolated,value.layout.size,value.layout.align⟩
  let memory := access.get (← get)
  if memory.preparedNativeBytes.any (·.1 == id) then
    backing.release value
    throw (.invalidProgram "native prepared global allocation already exists")
  if value.pointer == 0 then
    throw (.invalidProgram "native prepared global allocation is null")
  setAddresses access {memory with preparedNativeBytes := memory.preparedNativeBytes.push (id,⟨owner,size,align⟩)}
  pure value.pointer

/-- Pinned dummy_alloc: allocate one zero byte with alignment one and leak its
real backing for a unique function/vtable/va-list identity until process exit.
No ownership entry is inserted and no host address is synthesized. -/
def dummyAddress (backing : NativeAllocationLifecycle.Backing S) : EStateM StepError S Nat := do
  let value ← backing.fromBytes #[0] Align.ONE
  if value.pointer == 0 then throw (.invalidProgram "native dummy allocation is null")
  pure value.pointer

/-- Existing prepared backing can be observed without transferring ownership.
Address caching owns first-call detection; repeated reserve is an assertion. -/
def address (access : Access S) (id : AllocId) : EStateM StepError S Nat := do
  let some (_,entry) := (access.get (← get)).preparedNativeBytes.find? (·.1 == id)
    | throw (.invalidProgram "native global allocation has no prepared backing")
  pure entry.owner.pointer

/-- The caller is the canonical address engine; it must be invoked before take,
so a self-reference sees the already cached address during pointer conversion. -/
def takeAndCopy (access : Access S) (backing : NativeAllocationLifecycle.Backing S)
    (ensureAddress : AllocId → EStateM StepError S Nat)
    (id : AllocId) (bytes : Array UInt8) (align : Align) :
    EStateM StepError S (Array UInt8 × Option NativeBufferOwnership) := do
  unless access.isCompilerGlobal (← get) id do
    throw (.invalidProgram "native get_global_alloc_bytes requires compiler global")
  let _ ← ensureAddress id
  let memory := access.get (← get)
  let some (_,entry) := memory.preparedNativeBytes.find? (·.1 == id)
    | throw (.invalidProgram "native global allocation bytes were not prepared")
  setAddresses access {memory with preparedNativeBytes := memory.preparedNativeBytes.filter (·.1 != id)}
  try
    let alignment ← NativeAllocationLifecycle.alignmentBytes align
    unless entry.owner.pointer % alignment == 0 do
      throw (.invalidProgram "native prepared global backing has wrong alignment")
    unless entry.size.bytes.toNat == bytes.size do
      throw (.invalidProgram "native prepared global backing has wrong size")
    NativeAllocationLifecycle.commitBytes backing entry.owner bytes align
    pure (bytes,some entry.owner)
  catch error =>
    NativeAllocationLifecycle.releaseBytes backing entry.owner entry.size entry.align
    throw error

/-- Direct compiler-global backing dictionary on the same machine memory. -/
def bytes (access : Access (MachineHooks.MachineState K U))
    (backing : NativeAllocationLifecycle.Backing (MachineHooks.MachineState K U))
    (ensureAddress : AllocId → PlaceMachine.MachineM K U Nat) : GlobalAllocationMachine.Bytes K U where
  prepare := takeAndCopy access backing ensureAddress
  commit := NativeAllocationLifecycle.commitBytes backing
  release := NativeAllocationLifecycle.releaseBytes backing
end Miri.Interpreter.NativePreparedGlobals
