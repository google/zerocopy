import Miri.Interpreter.PlaceMachine

/-! Shared concrete raw-memory operations: rustc memory.rs:1423–1480 and
Miri helpers.rs:755–835. Reads include initialization checks and appropriate
provenance stripping; all access/touched effects commit before errors. -/
namespace Miri.Interpreter.RawMemoryMachine
open Miri.ABI Miri.Memory Miri.TreeBorrows
abbrev M := MachineHooks.M

private def liftResult (result : Except StepError A) : M K User A :=
  match result with | .ok value => pure value | .error error => throw error

def reference [DecidableEq K] (config : PlaceMachine.AccessConfig K User)
    (arithmetic : PointerArithmetic) (write : Bool) (pointer : Pointer (Option Provenance))
    (size : Size) : M K User (Option (AllocationAccessRef Provenance BorrowTree)) := do
  let state ← get
  let result := if write then
      AllocationAccess.getPtrAllocMut state.machine.memory ⟨state.machine,none⟩ arithmetic pointer size
        config.ghostMode config.globalKind config.globalHooks (PlaceMachine.accessHooks config)
    else AllocationAccess.getPtrAlloc state.machine.memory ⟨state.machine,none⟩ arithmetic pointer size
        config.ghostMode config.globalKind config.globalHooks (PlaceMachine.accessHooks config)
  modify fun state =>
    let machine := {result.hooks.machine with memory := result.memory}
    {state with machine := config.retainTouched machine result.touched}
  match result.outcome with
  | .ok value => return value
  | .error error => throw (result.hooks.pendingError.getD (config.memoryError (.pointerAccess error)))

def readBytes [DecidableEq K] (config : PlaceMachine.AccessConfig K User)
    (arithmetic : PointerArithmetic) (pointer : Pointer (Option Provenance)) (length : UInt64) : M K User ByteArray := do
  let some ref ← reference config arithmetic false pointer (Size.ofBytes length) | return ByteArray.empty
  let bytes ← liftResult (ref.allocation.getBytesStripProvenance config.runtime.base ref.range |>.mapError
    fun error => config.memoryError (.allocation error))
  return ⟨bytes⟩

def readUnsigned [DecidableEq K] (config : PlaceMachine.AccessConfig K User)
    (arithmetic : PointerArithmetic) (pointer : Pointer (Option Provenance)) (size : Size) : M K User U128 := do
  let some ref ← reference config arithmetic false pointer size |
    throw (.invalidProgram "read_integer requires nonzero scalar size")
  let value ← liftResult (ref.allocation.readScalar config.runtime.base ref.range false |>.mapError
    fun error => config.memoryError (.allocation error))
  liftResult (value.toBits size |>.mapError ScalarOps.scalarError)

def readByte [DecidableEq K] (config : PlaceMachine.AccessConfig K User)
    (arithmetic : PointerArithmetic) (pointer : Pointer (Option Provenance)) : M K User UInt8 := do
  let value ← readUnsigned config arithmetic pointer (Size.ofBytes 1)
  if value.toNat >= 256 then throw (.invalidProgram "u8 read exceeded scalar width")
  return UInt8.ofNat value.toNat

/-- Allocation.writeBytes clears overwritten provenance and initializes every
byte. A failing overwrite retains its partially mutated allocation. -/
def writeBytes [DecidableEq K] (config : PlaceMachine.AccessConfig K User)
    (arithmetic : PointerArithmetic) (pointer : Pointer (Option Provenance)) (bytes : ByteArray) : M K User Unit := do
  if bytes.size >= 2^64 then throw (.invalidProgram "byte stream length exceeds u64")
  let some ref ← reference config arithmetic true pointer (Size.ofBytes (UInt64.ofNat bytes.size)) | return ()
  let result := Allocation.writeBytes ref.range.start bytes.data arithmetic.pointerSize ref.allocation
  let (outcome,allocation) := match result with
    | .ok () allocation => (Except.ok (),allocation)
    | .error error allocation => (Except.error error,allocation)
  let state ← get
  let memory ← liftResult (state.machine.memory.setLiveAllocation ref.allocId allocation |>.mapError
    fun error => config.memoryError (.memoryUpdate error))
  let machine := config.retainTouched {state.machine with memory} (some {ref with allocation})
  set {state with machine}
  match outcome with
  | .ok () => pure ()
  | .error error => throw (config.memoryError (.allocation error))

def writeRepeatedByte [DecidableEq K] (config : PlaceMachine.AccessConfig K User)
    (arithmetic : PointerArithmetic) (pointer : Pointer (Option Provenance)) (byte : UInt8)
    (count : UInt64) : M K User Unit := do
  let some ref ← reference config arithmetic true pointer (Size.ofBytes count) | return ()
  let result := Allocation.writeRepeatedByte ref.range.start byte count arithmetic.pointerSize ref.allocation
  let (outcome,allocation) := match result with
    | .ok () allocation => (Except.ok (),allocation)
    | .error error allocation => (Except.error error,allocation)
  let state ← get
  let memory ← liftResult (state.machine.memory.setLiveAllocation ref.allocId allocation |>.mapError
    fun error => config.memoryError (.memoryUpdate error))
  let machine := config.retainTouched {state.machine with memory} (some {ref with allocation})
  set {state with machine}
  match outcome with
  | .ok () => pure ()
  | .error error => throw (config.memoryError (.allocation error))

/-- Miri helpers.rs:783–801. Insufficient caller capacity returns the needed
length without touching the pointer. Successful writes include the terminator. -/
def writeCString [DecidableEq K] (config : PlaceMachine.AccessConfig K User)
    (arithmetic : PointerArithmetic) (bytes : ByteArray) (pointer : Pointer (Option Provenance))
    (capacity : UInt64) : M K User (Bool × UInt64) := do
  if bytes.size+1 >= 2^64 then throw (.invalidProgram "C string length overflow")
  let length := UInt64.ofNat (bytes.size+1)
  if capacity < length then return (false,length)
  writeBytes config arithmetic pointer ⟨bytes.data.push 0⟩
  return (true,length)

/-- String scanning uses wrapping offsets, without an inbounds check before
its next byte read. The byte read owns the actual access bounds check. -/
def offset (arithmetic : PointerArithmetic) (pointer : Pointer (Option Provenance))
    (amount : UInt64) : Except StepError (Pointer (Option Provenance)) :=
  pointer.wrappingOffset (Size.ofBytes amount) arithmetic |>.mapError
    fun error => .invalidProgram s!"wrapping pointer offset: {reprStr error}"

/-- Explicit ptr_get_alloc_id(...,0), unlike a zero-size dereference this must
resolve pointer identity and reject integer/dangling address resolution. -/
def checkPointer (config : PlaceMachine.AccessConfig K User)
    (pointer : Pointer (Option Provenance)) : M K User Unit := do
  let state ← get
  match config.resolvePointer state.machine.memory pointer 0 state.machine with
  | .ok (.ok _) machine => set {state with machine}
  | .ok (.error address) machine =>
    set {state with machine}
    throw (.undefinedBehavior s!"dangling pointer {address}")
  | .error error machine =>
    set {state with machine}
    throw error
end Miri.Interpreter.RawMemoryMachine
