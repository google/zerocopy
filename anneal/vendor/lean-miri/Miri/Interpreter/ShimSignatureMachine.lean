import Miri.Interpreter.ShimSignatures
import Miri.Interpreter.IntrinsicVectorMachine

/-! Signature checks use the same real typed operand reads and zero-offset
wrapping transmutes as the MIR interpreter, never a type-erased argument list. -/
namespace Miri.Interpreter.ShimSignatureMachine
open Miri.ABI Miri.Memory
private def lift (value : Except StepError A) : MachineHooks.M K U A :=
  match value with | .ok value => pure value | .error error => throw error

def bind [DecidableEq K] (access : PlaceMachine.AccessConfig K U)
    (place : PlaceHooks Provenance (MachineHooks.State K U) C MachineHooks.FrameExtra)
    (choice : C) (base : ShimSignatures.Hooks Provenance (MachineHooks.State K U) D MD Ptr B I) :
    ShimSignatures.Hooks Provenance (MachineHooks.State K U) D MD Ptr B I :=
  {base with
    readScalar := fun operand => do
      let value ← PlaceMachine.readImmediate access operand
      lift (value.imm.toScalar.mapError ScalarOps.immediateError)
    foreign := {base.foreign with transmute := fun operand target => do
      lift (operand.transmute (← place.projection choice) target |>.mapError IntrinsicVectorMachine.projectionError)} }
end Miri.Interpreter.ShimSignatureMachine
