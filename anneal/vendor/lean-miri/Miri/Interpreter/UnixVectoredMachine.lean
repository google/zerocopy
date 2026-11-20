import Miri.Interpreter.UnixVectored
import Miri.Interpreter.PointerPlaceMachine
import Miri.Interpreter.PointerMachineBindings
import Miri.Interpreter.GlobalMemoryCopyMachine

/-! Physical vectored IO: real typed reads/projections, raw Stack allocation,
in-bounds pointer offsets and provenance-preserving nonoverlapping copies.
Only canonical compiler queries and the actual deallocation driver survive. -/
namespace Miri.Interpreter.UnixVectoredMachine
open Miri.ABI Miri.Memory Miri.MIR
abbrev State K U := ValidityMachine.State K U
abbrev M K U := ValidityMachine.M K U
private def lift (value : Except StepError A) : M K U A :=
  match value with | .ok value => pure value | .error error => throw error
private def scalar [DecidableEq K] (access : ValidityMachine.Access K U)
    (operand : OpTy Provenance) : M K U (Scalar Provenance) := do
  let value ← PlaceMachine.readImmediate access operand
  lift (value.imm.toScalar.mapError ScalarOps.immediateError)
private def memory (value : RuntimePlace Provenance) : M K U (MPlaceTy Provenance) :=
  match value.ref with
  | .memory place => pure ⟨place,value.layout⟩
  | .local .. => throw (.invalidProgram "memory-only iovec projection produced a local")

def bind [DecidableEq K] (access : ValidityMachine.Access K U)
    (allocation : PlaceMachine.AllocationConfig K (ValidityMachine.UserState U))
    (pointers : PointerMachine.Hooks K (ValidityMachine.Control U))
    (projection : PlaceProjectionHooks Provenance (State K U) C MachineHooks.FrameExtra)
    (place : PlaceHooks Provenance (State K U) C MachineHooks.FrameExtra) (choice : C)
    (unitLayout : M K U LocalLayout)
    (iovecArrayLayout : UInt64 → M K U LocalLayout)
    (fieldIndex : LocalLayout → String → M K U Nat)
    (deallocateStack : Pointer (Option Provenance) → M K U Unit)
    (base : UnixVectored.Hooks (State K U) H D O E Meta) :
    UnixVectored.Hooks (State K U) H D O E Meta :=
  {base with
    readI32 := fun value => do lift ((← scalar access value).toInt32.mapError ScalarOps.scalarError)
    readSigned := fun value => do lift ((← scalar access value).toInt value.layout.layout.size |>.mapError ScalarOps.scalarError)
    readPointer := fun value => do lift ((← scalar access value).toPointer access.runtime.base |>.mapError ScalarOps.scalarError)
    arrayPlace := fun pointer count => do PointerPlaceMachine.fromPointer access pointer (← iovecArrayLayout count) false
    startArray := ArrayProjection.prepare projection choice unitLayout
    index := ArrayProjection.get projection choice
    field := fun value name => do
      let index ← fieldIndex value.layout name
      memory (← PlaceDynamic.field projection choice ⟨.memory value.mplace,value.layout⟩ index)
    readFieldSigned := fun value => do
      let data ← scalar access ⟨.indirect value.mplace,value.layout⟩
      lift (data.toInt value.layout.layout.size |>.mapError ScalarOps.scalarError)
    readFieldPointer := fun value => do
      let data ← scalar access ⟨.indirect value.mplace,value.layout⟩
      lift (data.toPointer access.runtime.base |>.mapError ScalarOps.scalarError)
    allocateStack := fun size => PlaceMachine.allocateStackRaw allocation size Align.ONE
    deallocateStack := deallocateStack
    offsetInbounds := PointerMachine.offsetInbounds pointers
    copyNonoverlapping := fun source dest size =>
      GlobalMemoryCopyMachine.genericCopy access (·.addresses) pointers.arithmetic source dest size 1 true
    writeTargetIsize := fun size dest => do
      if size >= 2^63 then throw (.invalidProgram "source vectored result i64 conversion panic")
      let value ← lift (Scalar.fromInt (Int.ofNat size) access.runtime.pointerOffset |>.mapError ScalarOps.scalarError)
      writePlaceImmediate place choice (.scalar value) ⟨.memory dest.mplace,dest.layout⟩}
end Miri.Interpreter.UnixVectoredMachine
