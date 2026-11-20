import Miri.Input.CompilerCallConstruction
import Miri.Input.CompilerForeignSymbols
import Miri.Input.CompilerNamedShimAbi
import Miri.Input.EvalWindowsEnvironmentConstruction
import Miri.Interpreter.WindowsEnvironmentDispatch

/-! Source-owned compiler and memory binding for the Windows environment
foreign-item family. Names remain part of each ABI request because the
compiler catalog is keyed by the exact imported shim symbol. -/
namespace Miri.Input.EvalWindowsEnvironmentDispatchConstruction
open Miri.ABI Miri.Memory Miri.MIR Miri.Interpreter

set_option autoImplicit false in
private def dispatchFromEnvironment
    {Os Error Kind U C : Type}
    (p : CompilerProviders.Prepared)
    (environment : WindowsEnvironment.Hooks
      (MachineHooks.State MiriMemoryKind U) Os Error Kind)
    (targetLayout : TargetDataLayout)
    (place : PlaceHooks Provenance
      (MachineHooks.State MiriMemoryKind U) C MachineHooks.FrameExtra)
    (choice : C)
    (compatibilityBudget : Nat) :
    Except StepError (WindowsEnvironmentDispatch.Hooks
      (MachineHooks.State MiriMemoryKind U) Os Error Kind) := do
  let symbols ← p.foreignSymbols
    |>.mapError StepError.unsupported
  let calls := CompilerCallConstruction.compiler p compatibilityBudget
  let writeScalar := fun (value : Scalar Provenance)
      (destination : MPlaceTy Provenance) =>
    writePlaceImmediate place choice (.scalar value)
      ⟨.memory destination.mplace,destination.layout⟩
  let writeInt := fun (value : Int)
      (destination : MPlaceTy Provenance) => do
    let scalar ← match Scalar.fromInt value destination.layout.layout.size with
      | .ok scalar => pure scalar
      | .error error => throw (ScalarOps.scalarError error)
    writeScalar scalar destination
  let writePointer := fun (value : Pointer (Option Provenance))
      (destination : MPlaceTy Provenance) => do
    let scalar ← match Scalar.fromMaybePointer targetLayout value with
      | .ok scalar => pure scalar
      | .error error => throw (ScalarOps.scalarError error)
    writeScalar scalar destination
  let transmute := fun (operand : OpTy Provenance)
      (target : TyAndLayout TyId) => do
    let projection ← place.projection choice
    match operand.transmute projection target |>.mapError
        IntrinsicVectorMachine.projectionError with
    | .ok value => pure value
    | .error error => throw error
  let expectedAbi := fun (name : String)
      (request : WindowsEnvironmentDispatch.Signature) => do
    let some operation := WindowsEnvironmentDispatch.parse name |
      throw (.unsupported s!"Windows environment ABI requested for unknown `{name}`")
    let expected := WindowsEnvironmentDispatch.signature operation
    unless expected.args == request.args && expected.ret == request.ret do
      throw (.invalidProgram s!"Windows environment ABI recipe disagrees with `{name}`")
    CompilerNamedShimAbi.query p.namedAbi name
  pure {
    env := environment
    systemConvention := do
      return (← CompilerNamedShimAbi.query p.namedAbi "GetEnvironmentVariableW").conv
    expectedAbi
    argumentCompat := calls.checkArgumentCompat choice
    checkSymbolClash := fun name =>
      match CompilerForeignSymbols.checkSymbolClash symbols name with
      | .ok () => pure ()
      | .error error => throw error
    transmute
    writeScalar
    writeInt
    writePointer
  }

/-- Construct the complete source-owned Windows environment dispatch component
from raw OS/environment leaves and the canonical initialized memory bundle.
No caller-supplied environment Hooks or independent process/environment store
is accepted. -/
def fromSource [DecidableEq MiriMemoryKind] [DecidableEq Os]
    (p : CompilerProviders.Prepared)
    (host : EvalHostRuntimeConstruction.OsHostEffects Os)
    (hostEffects : EvalHostRuntimeConstruction.EnvironmentHostEffects
      (EvalWindowsEnvironmentConstruction.InnerControl Os R P H D O Aff B Host))
    (memory : EvalWindowsEnvironmentConstruction.Memory Os R P H D O Aff B Host C)
    (place : PlaceHooks Provenance
      (EvalWindowsEnvironmentConstruction.State Os R P H D O Aff B Host)
      C MachineHooks.FrameExtra)
    (choice : C)
    (compatibilityBudget : Nat)
    (errors : IoError.Hooks
      (EvalWindowsEnvironmentConstruction.State Os R P H D O Aff B Host) Error)
    (hostConfig : EvalWindowsEnvironmentConstruction.HostEffects
      (EvalWindowsEnvironmentConstruction.State Os R P H D O Aff B Host) Os Error) :
    Except StepError (WindowsEnvironmentDispatch.Hooks
      (EvalWindowsEnvironmentConstruction.State Os R P H D O Aff B Host)
      Os Error EnvVars.Kind) := do
  let environment ← EvalWindowsEnvironmentConstruction.fromSource
    p host hostEffects memory place errors hostConfig
  dispatchFromEnvironment p environment memory.access.runtime.base place choice
    compatibilityBudget

end Miri.Input.EvalWindowsEnvironmentDispatchConstruction
