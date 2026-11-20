import Miri.Interpreter.UnixFdControlDispatch
import Miri.Interpreter.UnixFileOperations
import Miri.Interpreter.SocketMachine
import Miri.Interpreter.PointerPlaceMachine

/-! Real FD dynamic dispatch for source flags and ioctl, using the canonical
file/socket descriptions and the actual physical scalar/memory operations. -/
namespace Miri.Interpreter.UnixFdControlMachine
open Miri.ABI Miri.Memory Miri.MIR
variable {Place : Type}
open Files
abbrev State K U := ValidityMachine.State K U
abbrev M K U := ValidityMachine.M K U
abbrev Ref H D O := Files.Ref (Description H D O)
private def lift (value : Except StepError A) : M K U A :=
  match value with | .ok value => pure value | .error error => throw error
private def scalar [DecidableEq K] (access : ValidityMachine.Access K U)
    (operand : OpTy Provenance) : M K U (Scalar Provenance) := do
  let value ← PlaceMachine.readImmediate access operand
  lift (value.imm.toScalar.mapError ScalarOps.immediateError)
private def fromI32 (value : Int32) : M K U (Scalar Provenance) :=
  lift (Scalar.fromInt value.toInt (Size.ofBytes 4) |>.mapError ScalarOps.scalarError)

def bind [DecidableEq K] (access : ValidityMachine.Access K U)
    (descriptor : SocketMachine.Descriptor O)
    (virtual : VirtualSocket.Hooks (State K U) (Ref H D O) E)
    (tcp : TcpSocket.Hooks (State K U) (Ref H D O) R L T E P Host)
    (file : UnixFileOperations.Hooks (State K U) H E)
    (i32Layout : M K U LocalLayout) (i32PointerType : M K U TyId)
    (place : PlaceHooks Provenance (State K U) C MachineHooks.FrameExtra) (choice : C)
    (base : UnixFdControlDispatch.Hooks (State K U) H D O E Meta Place B I) :
    UnixFdControlDispatch.Hooks (State K U) H D O E Meta Place B I := Id.run do
  let readArgument := fun rest => do
    let (values,_) ← ShimSignatures.take base.signatures base.typeBudget
      (do return #[← i32PointerType]) rest
    let some value := values[0]? | throw (.invalidProgram "checked ioctl pointer absent")
    pure value
  let dereference := fun value => do
    let pointer ← lift ((← scalar access value).toPointer access.runtime.base |>.mapError ScalarOps.scalarError)
    PointerPlaceMachine.fromPointer access pointer (← i32Layout) false
  let readField := fun (field : MPlaceTy Provenance) => do
    let value ← scalar access ⟨.indirect field.mplace,field.layout⟩
    lift (value.toInt32.mapError ScalarOps.scalarError)
  let control := {base.control with
    readScalar := scalar access
    readI32 := fun value => do lift ((← scalar access value).toInt32.mapError ScalarOps.scalarError)
    getFlags := fun fd => do
      match fd.value with
      | .file _ readable writable => UnixFileOperations.fileFlags file readable writable
      | .directory _ => UnixFileOperations.directoryFlags file
      | _ =>
        match SocketMachine.kind descriptor fd with
        | some .virtual => fromI32 (← VirtualSocket.getFlags virtual fd)
        | some .tcp => fromI32 (← TcpSocket.getFlags tcp fd base.control.libcI32)
        | none => throw (.unsupported "F_GETFL unsupported for this source file description")
    setFlags := fun fd flags => do
      match SocketMachine.kind descriptor fd with
      | some .virtual => fromI32 (← VirtualSocket.setFlags virtual fd flags)
      | some .tcp => fromI32 (← TcpSocket.setFlags tcp fd base.control.libcI32 flags)
      | none => throw (.unsupported "F_SETFL unsupported for this source file description")
    ioctl := fun fd op rest => do
      match SocketMachine.kind descriptor fd with
      | some .virtual =>
        VirtualSocket.ioctl {virtual with readIoctlArgument := readArgument rest, derefI32 := dereference, readFieldI32 := readField} fd op
      | some .tcp =>
        TcpSocket.ioctl tcp fd base.control.fd.communicate op base.control.libc
          (do readField (← dereference (← readArgument rest)))
      | none => throw (.unsupported "ioctl unsupported for this source file description")}
  let foreign := {base.signatures.foreign with
    readI32 := fun value => do lift ((← scalar access value).toInt32.mapError ScalarOps.scalarError)
    readUsize := fun value => do lift ((← scalar access value).toTargetUsize access.runtime.pointerSize |>.mapError ScalarOps.scalarError)
    readPointer := fun value => do lift ((← scalar access value).toPointer access.runtime.base |>.mapError ScalarOps.scalarError)}
  return {base with control, signatures := {base.signatures with foreign, readScalar := scalar access}, writeScalar := fun value dest => writePlaceImmediate place choice (.scalar value) ⟨.memory dest.mplace,dest.layout⟩}
end Miri.Interpreter.UnixFdControlMachine
