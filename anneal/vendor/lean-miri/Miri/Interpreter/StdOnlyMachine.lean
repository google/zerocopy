import Miri.Interpreter.StdOnlyShims
import Miri.Interpreter.PlaceDynamic
import Miri.Interpreter.PlaceMachine

/-! Actual pointer reads and typed memory writes for std-only source shims.
Compiler layouts/named-field lookup, host paths, constants and platform ABI
queries stay explicit; memory effects pass through canonical race/TB hooks. -/
namespace Miri.Interpreter.StdOnlyMachine
open Miri.ABI Miri.Memory Miri.MIR
private def lift (result : Except StepError A) : MachineHooks.M K User A :=
  match result with | .ok value => pure value | .error error => throw error

def hooks [DecidableEq K] (access : PlaceMachine.AccessConfig K User)
    (projection : PlaceProjectionHooks Provenance (MachineHooks.State K User) C MachineHooks.FrameExtra)
    (choice : C) (compiler : FrameMetadata.CompilerHooks K User)
    (misaligned : Pointer (Option Provenance) → Align → MachineHooks.M K User (Option Misalignment))
    (namedField : TyId → String → MachineHooks.M K User Nat)
    (base : StdOnlyShims.Hooks Provenance (MachineHooks.State K User) D (MPlaceTy Provenance) B I) :
    StdOnlyShims.Hooks Provenance (MachineHooks.State K User) D (MPlaceTy Provenance) B I :=
  let readScalar := fun operand => do
    let immediate ← PlaceMachine.readImmediate access operand
    lift (immediate.imm.toScalar.mapError ScalarOps.immediateError)
  let readPointer := fun operand => do
    lift ((← readScalar operand).toPointer access.runtime.base |>.mapError ScalarOps.scalarError)
  let writeScalar := fun scalar (dest : MPlaceTy Provenance) =>
    writePlaceImmediate projection.place choice (.scalar scalar) ⟨.memory dest.mplace,dest.layout⟩
  let writeUnsigned := fun (value : UInt64) (dest : MPlaceTy Provenance) => do
    let scalar ← lift (Scalar.fromUInt (BitVec.ofNat 128 value.toNat) dest.layout.layout.size
      |>.mapError ScalarOps.scalarError)
    writeScalar scalar dest
  { base with
    frameInStd := FrameMetadata.frameInStd compiler
    foreign := { base.foreign with
      readPointer
      readUsize := fun operand => do
        lift ((← readScalar operand).toTargetUsize access.runtime.pointerSize
          |>.mapError ScalarOps.scalarError)
      writePointer := fun pointer dest => do
        let scalar ← lift (Scalar.fromMaybePointer access.runtime.base pointer
          |>.mapError ScalarOps.scalarError)
        writeScalar scalar dest
      writeNull := writeUnsigned 0 }
    dereference := fun operand layout => do
      let pointer ← readPointer operand
      if !layout.layout.isSized then throw (.invalidProgram "ptr_to_mplace requires sized layout")
      let alignment ← misaligned pointer layout.layout.align.abi
      return ⟨⟨pointer,.none,alignment⟩,layout⟩
    pointerOf := fun place => place.mplace.ptr
    readU32 := fun operand => do
      lift ((← readScalar operand).toUInt32.mapError ScalarOps.scalarError)
    writeUnsigned
    writeScalar
    writeUninit := fun place => PlaceMachine.writeMemory access (fun _ => false) .uninit place
    projectNamed := fun place name => do
      let index ← namedField place.layout.ty name
      let projected ← PlaceDynamic.field projection choice ⟨.memory place.mplace,place.layout⟩ index
      match projected.ref with
      | .memory memory => return ⟨memory,projected.layout⟩
      | .local .. => throw (.invalidProgram "memory field projection became local") }
end Miri.Interpreter.StdOnlyMachine
