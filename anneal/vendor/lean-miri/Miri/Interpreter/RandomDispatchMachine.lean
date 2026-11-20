import Miri.Interpreter.UnixRandomDispatch
import Miri.Interpreter.WindowsRandomDispatch

/-! Concrete scalar, pointer and destination effects shared by source entropy
wrappers. Both families draw through the one actual machine choice tape. -/
namespace Miri.Interpreter.RandomDispatchMachine
open Miri.ABI Miri.Memory Miri.MIR
private def lift (value : Except StepError A) : MachineHooks.M K U A :=
  match value with | .ok value => pure value | .error error => throw error
private def scalar [DecidableEq K] (access : PlaceMachine.AccessConfig K U)
    (operand : OpTy Provenance) : MachineHooks.M K U (Scalar Provenance) := do
  let value ← PlaceMachine.readImmediate access operand
  lift (value.imm.toScalar.mapError ScalarOps.immediateError)
private def write (place : PlaceHooks Provenance (MachineHooks.State K U) C MachineHooks.FrameExtra)
    (choice : C) (value : Scalar Provenance) (dest : MPlaceTy Provenance) : MachineHooks.M K U Unit :=
  writePlaceImmediate place choice (.scalar value) ⟨.memory dest.mplace,dest.layout⟩
private def writeInteger (place : PlaceHooks Provenance (MachineHooks.State K U) C MachineHooks.FrameExtra)
    (choice : C) (value : Int) (dest : MPlaceTy Provenance) : MachineHooks.M K U Unit := do
  let value ← lift (Scalar.fromInt value dest.layout.layout.size |>.mapError ScalarOps.scalarError)
  write place choice value dest
private def writeUsize (pointerOffset : Size)
    (place : PlaceHooks Provenance (MachineHooks.State K U) C MachineHooks.FrameExtra)
    (choice : C) (value : UInt64) (dest : MPlaceTy Provenance) : MachineHooks.M K U Unit := do
  let value ← lift (Scalar.fromUInt (BitVec.ofNat 128 value.toNat) pointerOffset |>.mapError ScalarOps.scalarError)
  write place choice value dest

def unix [DecidableEq K] (access : PlaceMachine.AccessConfig K U)
    (tape : ExecutionChoices.Access (MachineHooks.State K U))
    (place : PlaceHooks Provenance (MachineHooks.State K U) C MachineHooks.FrameExtra)
    (choice : C) (base : UnixRandomDispatch.Hooks (MachineHooks.State K U) D B I) :
    UnixRandomDispatch.Hooks (MachineHooks.State K U) D B I :=
  {base with
    random := RandomMemory.bind access tape base.random
    readPointer := fun operand => do lift ((← scalar access operand).toPointer access.runtime.base |>.mapError ScalarOps.scalarError)
    readUsize := fun operand => do lift ((← scalar access operand).toTargetUsize access.runtime.pointerSize |>.mapError ScalarOps.scalarError)
    readI32 := fun operand => do lift ((← scalar access operand).toInt32.mapError ScalarOps.scalarError)
    writeNull := writeInteger place choice 0
    writeTargetUsize := writeUsize access.runtime.pointerOffset place choice}

def windows [DecidableEq K] (access : PlaceMachine.AccessConfig K U)
    (tape : ExecutionChoices.Access (MachineHooks.State K U))
    (place : PlaceHooks Provenance (MachineHooks.State K U) C MachineHooks.FrameExtra)
    (choice : C) (base : WindowsRandomDispatch.Hooks (MachineHooks.State K U) D B I) :
    WindowsRandomDispatch.Hooks (MachineHooks.State K U) D B I :=
  {base with
    random := RandomMemory.bind access tape base.random
    readPointer := fun operand => do lift ((← scalar access operand).toPointer access.runtime.base |>.mapError ScalarOps.scalarError)
    readUsize := fun operand => do lift ((← scalar access operand).toTargetUsize access.runtime.pointerSize |>.mapError ScalarOps.scalarError)
    readU32 := fun operand => do lift ((← scalar access operand).toUInt32.mapError ScalarOps.scalarError)
    writeScalar := write place choice
    writeNull := writeInteger place choice 0
    writeInt := writeInteger place choice}
end Miri.Interpreter.RandomDispatchMachine
