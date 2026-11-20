import Miri.Interpreter.PointerPlaceMachine
import Miri.Interpreter.FunctionPointers

/-! Source TCX allocate_bytes_dedup and InterpCx allocate_str_dedup.
Global allocation identity and CTFE bytes are retained lazily; normal memory
access still performs the actual global conversion and Tree Borrows hooks. -/
namespace Miri.Interpreter.GlobalByteMachine
open Miri.ABI Miri.Memory Miri.MIR

/-- Reserve only after the exact imported salt-key catalog has been attached.
A missing catalog cannot be replaced with an initially empty dedup table. -/
def reserve (bytes : Array UInt8) (salt : Fin 32) : MachineHooks.M K U AllocId := do
  let allocation ← match (Allocation.fromBytesByteAlignedImmutable bytes : Except AllocError (Allocation CtfeProvenance Unit)) with
    | .ok value => pure value
    | .error error => throw (.resourceExhaustion s!"global byte allocation: {reprStr error}")
  let memory := (← get).machine.memory
  unless memory.byteGlobalKeysReady do
    throw (.unsupported "exact imported compiler-global byte salt catalog has not been attached")
  if let some entry := memory.byteGlobalKeys.find? (fun entry => entry.1 == bytes && entry.2.1 == salt) then
    return entry.2.2
  if memory.sourceAllocIdWorldActive && !memory.sourceByteImageFamilyComplete then
    throw (.unsupported "source byte-image AllocId miss is not proven by a complete prepared key catalog")
  let (memory,result) := memory.reserveAllocId
  modify fun state => {state with machine := {state.machine with memory}}
  let id ← match result with
    | .ok value => pure value
    | .error error => throw (.resourceExhaustion s!"global byte allocation identity: {reprStr error}")
  modify fun state => {state with machine := {state.machine with memory :=
    {MemoryState.pushGlobal state.machine.memory
        ⟨id,.memory,allocation.byteSize,.ONE,.Not,some (.memory allocation)⟩ with
      byteGlobalKeys := state.machine.memory.byteGlobalKeys.push (bytes,salt,id)}}}
  pure id

/-- Non-function globals always take the source random salt branch. The root
borrow tag/address is adjusted on every mention, including dedup hits. -/
def bytes (functions : FunctionPointers.Hooks K U O) (value : Array UInt8) :
    MachineHooks.M K U (Pointer Provenance) := do
  let salt ← functions.chooseSalt
  let id ← reserve value salt
  FunctionPointers.rootPointer functions id

/-- Allocation/root effects precede length construction and the str layout
query, exactly as place.rs:1156–1175. Only the resulting physical place caches
alignment; no fabricated type or integer-address pointer is constructed. -/
def string [DecidableEq K]
    (functions : FunctionPointers.Hooks K (ValidityMachine.UserState U) O)
    (access : ValidityMachine.Access K U)
    (strLayout : ValidityMachine.M K U LocalLayout) (value : String) :
    ValidityMachine.M K U (MPlaceTy Provenance) := do
  let data := value.toUTF8.data
  let pointer ← bytes functions data
  if data.size >= 2^64 then throw (.invalidProgram "string length exceeds source u64 conversion")
  let length ← match Scalar.fromUInt (BitVec.ofNat 128 data.size) access.runtime.pointerOffset with
    | .ok value => pure value | .error error => throw (ScalarOps.scalarError error)
  let layout ← strLayout
  PointerPlaceMachine.withMetadata access pointer.withOptionalProvenance (.metadata length) layout false
end Miri.Interpreter.GlobalByteMachine
