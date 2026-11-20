import Miri.Input.CompilerFrameMetadata
import Miri.Input.CompilerNamedShimAbi
import Miri.Input.CompilerProviders
import Miri.Input.CompilerWindowsConstants
import Miri.Input.EvalCoreMachine
import Miri.Interpreter.MainMachine
import Miri.Interpreter.StdOnlyShims

/-! Construct the pinned Windows std-only startup arms from the actual frame,
compiler ABI/constants, Main memory, thread manager and last-error state. The
source's std-frame restriction is evaluated at each call. -/
namespace Miri.Input.EvalWindowsStdOnlyConstruction
open Miri.ABI Miri.Memory Miri.MIR Miri.Interpreter

abbrev Payload Os R P H D O Aff B Host :=
  ValidityMachine.UserState (EvalCoreMachine.World Os R P H D O Aff B Host)
abbrev State Os R P H D O Aff B Host :=
  MainMachine.State (Payload Os R P H D O Aff B Host)

set_option autoImplicit false in
def fromSource
    {Os R P H D O Aff B Host C Destination Body Instance Error : Type}
    (p : CompilerProviders.Prepared)
    (userRelevantCrates : Array Nat)
    (foreign : ForeignItems.Core Provenance (State Os R P H D O Aff B Host)
      Destination (MPlaceTy Provenance) (Pointer (Option Provenance)) Body Instance)
    (place : PlaceHooks Provenance (State Os R P H D O Aff B Host)
      C MachineHooks.FrameExtra)
    (errors : IoError.Hooks (State Os R P H D O Aff B Host) Error)
    (choice : C) :
    Except StepError (StdOnlyShims.WindowsHooks Provenance
      (State Os R P H D O Aff B Host) Destination (MPlaceTy Provenance) Body Instance) := do
  let target ← p.externStatics.targetFacts |>.mapError StepError.unsupported
  unless target.os == "windows" && foreign.family == .windows && foreign.os == target.os do
    throw (.invalidProgram "Windows std-only source target mismatch")
  let frames := CompilerFrameMetadata.hooks p.lifecycle.frames userRelevantCrates
  let writeScalar := fun (value : Scalar Provenance) (destination : MPlaceTy Provenance) =>
    writePlaceImmediate place choice (.scalar value)
      ⟨.memory destination.mplace,destination.layout⟩
  pure {
    foreign
    frameInStd := FrameMetadata.frameInStd frames
    windowsAbi := CompilerNamedShimAbi.query p.namedAbi
    windowsValue := fun name =>
      match CompilerWindowsConstants.scalar p.namedConstants "c" name with
      | .ok value => pure value
      | .error reason => throw (.unsupported reason)
    writeScalar
    writeUnsigned := fun value destination => do
      let scalar ← match Scalar.fromUInt (BitVec.ofNat 128 value.toNat)
          destination.layout.layout.size with
        | .ok scalar => pure scalar
        | .error error => throw (ScalarOps.scalarError error)
      writeScalar scalar destination
    yieldActiveThread := modify fun state => {state with machine := {state.machine with
      threads := Miri.Concurrency.ThreadManager.yield state.machine.threads}}
    setLastError := fun name => IoError.setLastError errors (.windows name) }

end Miri.Input.EvalWindowsStdOnlyConstruction
