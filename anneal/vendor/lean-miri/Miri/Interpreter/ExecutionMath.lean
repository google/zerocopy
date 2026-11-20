import Miri.Interpreter.Math.Bindings
import Miri.Interpreter.PointerPlaceMachine

/-! Source-owned Math.Hooks construction. Pinned intrinsics/math.rs generic
float selection and shims/math.rs lgamma{f,}_r sign-pointer/write_int operations
use the same canonical scalar, pointer, typed-place and memory policies as MIR.
Actual host numerical functions and session choices remain explicit leaves. -/
namespace Miri.Interpreter.ExecutionMath
open Miri.ABI Miri.Memory Miri.MIR
abbrev State := ValidityMachine.State
abbrev M := ValidityMachine.M
structure Leaves (S C : Type) where
  checkCSignature : C → String → Nat → RvalueM S Unit
  hostUnary : C → Math.Unary → Math.HostBits → RvalueM S Math.HostBits
  hostBinary : C → Math.Binary → Math.HostBits → Math.HostBits → RvalueM S Math.HostBits
  hostPowi : C → Math.HostBits → Int32 → RvalueM S Math.HostBits
  hostLgamma : C → Math.HostBits → RvalueM S (Math.HostBits × Int32)
  errorMode : Math.ErrorMode
  ulpError : C → Nat → RvalueM S Int
  maxErrorPositive : C → RvalueM S Bool
  relativeMagnitude : C → Nat → RvalueM S Nat
  relativeNegative : C → RvalueM S Bool
  snanPowNaN : C → RvalueM S Bool

private def lift (value : Except StepError A) : M K U A :=
  match value with | .ok value => pure value | .error error => throw error

def hooks [DecidableEq K] (leaves : Leaves (State K U) C)
    (access : ValidityMachine.Access K U)
    (place : PlaceHooks Provenance (State K U) C MachineHooks.FrameExtra)
    (scalar : ScalarOpsHooks Provenance (State K U) C)
    (floats : FloatOpsHooks Provenance (State K U) C)
    (i32Layout : LocalLayout)
    (returnToBlock : C → Option BasicBlockId → M K U Unit) :
    Math.Hooks Provenance (State K U) C (RuntimePlace Provenance) where
  floatOps := floats
  scalarOps := scalar
  readImmediate := fun _ => PlaceMachine.readImmediate access
  writeImmediate := writePlaceImmediate place
  destLayout := RuntimePlace.layout
  genericFloat := fun choice types => do
    let some ty := types[0]? | throw (.invalidProgram "native float intrinsic requires its source type argument")
    floats.formatOf choice ty
  checkCSignature := leaves.checkCSignature
  derefI32 := fun _ operand => do
    let value ← PlaceMachine.readImmediate access operand
    let scalar ← lift (value.imm.toScalar |>.mapError ScalarOps.immediateError)
    let pointer ← lift (scalar.toPointer access.runtime.base |>.mapError ScalarOps.scalarError)
    let memory ← PointerPlaceMachine.fromPointer access pointer i32Layout false
    pure ⟨.memory memory.mplace,memory.layout⟩
  writeI32 := fun choice sign destination => do
    let value ← lift (Scalar.fromInt sign.toInt destination.layout.layout.size |>.mapError ScalarOps.scalarError)
    writePlaceImmediate place choice (.scalar value) destination
  hostUnary := leaves.hostUnary
  hostBinary := leaves.hostBinary
  hostPowi := leaves.hostPowi
  hostLgamma := leaves.hostLgamma
  errorMode := leaves.errorMode
  ulpError := leaves.ulpError
  maxErrorPositive := leaves.maxErrorPositive
  relativeMagnitude := leaves.relativeMagnitude
  relativeNegative := leaves.relativeNegative
  snanPowNaN := leaves.snanPowNaN
  returnToBlock := returnToBlock
end Miri.Interpreter.ExecutionMath
