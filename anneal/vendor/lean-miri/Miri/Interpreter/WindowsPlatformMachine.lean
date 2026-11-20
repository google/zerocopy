import Miri.Interpreter.WindowsPlatform
import Miri.Interpreter.ReallocationDriver
import Miri.Interpreter.RawMemoryMachine
import Miri.Interpreter.FunctionPointers
import Miri.Memory.MiriMemoryKind

namespace Miri.Interpreter.WindowsPlatformMachine
open Miri.ABI Miri.Memory Miri.Memory.AllocAddresses
private def kind : WindowsPlatform.HeapKind → MiriMemoryKind
  | .heap => .winHeap | .local => .winLocal

/-- Actual allocation identity, initialization, copy and deallocation policies.
The supplied allocation configuration must use the requested source kind. -/
def bindMemory (allocation : MiriMemoryKind → PointerMachine.M MiriMemoryKind U (ReallocationDriver.Hooks MiriMemoryKind U Payload))
    (driver : AllocationDriver.Hooks MiriMemoryKind U Payload)
    (access : PlaceMachine.AccessConfig MiriMemoryKind (PointerMachine.User U))
    (choices : AddressRandomChoices) (reuse : Bool)
    (base : WindowsPlatform.Hooks (PointerMachine.State MiriMemoryKind U) O E K F) :
    WindowsPlatform.Hooks (PointerMachine.State MiriMemoryKind U) O E K F := {
  base with
  pointerSize := driver.pointer.arithmetic.pointerSize
  zeroBytes := fun pointer count => RawMemoryMachine.writeRepeatedByte access driver.pointer.arithmetic pointer 0 count
  allocate := fun size align init sourceKind => do
    let pointer ← ReallocationDriver.allocate (← allocation (kind sourceKind)) size align (.machine (kind sourceKind)) init choices
    return pointer.withOptionalProvenance
  deallocate := fun pointer sourceKind => AllocationDriver.deallocate driver reuse pointer none (.machine (kind sourceKind))
  reallocate := fun pointer size align sourceKind => do
    let pointer ← ReallocationDriver.reallocate (← allocation (kind sourceKind)) pointer none size align
      (.machine (kind sourceKind)) .Uninit choices reuse
    return pointer.withOptionalProvenance }

/-- Reuse the canonical extra-function registry and actual root-tag/address
path. Other may embed platform dynamic symbols alongside other machine values. -/
def bindSymbols (functions : FunctionPointers.Hooks K U Other)
    (embed : WindowsPlatform.DynamicSymbol → Other)
    (base : WindowsPlatform.Hooks (MachineHooks.State K U) O E Kind F) :
    WindowsPlatform.Hooks (MachineHooks.State K U) O E Kind F := {
  base with functionPointer := fun symbol => do
    return (← FunctionPointers.functionPointer functions (.Other (embed symbol))).withOptionalProvenance }
end Miri.Interpreter.WindowsPlatformMachine
