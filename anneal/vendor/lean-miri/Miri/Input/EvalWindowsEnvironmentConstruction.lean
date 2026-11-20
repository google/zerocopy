import Miri.Input.EvalStartupAssembly
import Miri.Input.CompilerProviders
import Miri.Input.EvalHostRuntimeConstruction
import Miri.Input.EvalUnixConstruction
import Miri.Input.CompilerWindowsConstants
import Miri.Interpreter.WindowsEnvironmentDispatch

/-! Source-owned Windows environment component construction. Guest environment
storage, wide-string memory and scalar access use the existing EvalWorld and
compiler providers. Only the host path/process operations remain raw leaves.
-/
namespace Miri.Input.EvalWindowsEnvironmentConstruction
open Miri.ABI Miri.Memory Miri.MIR Miri.Interpreter

abbrev Payload Os R P H D O Aff B Host := EvalExecutable.U Os R P H D O Aff B Host
abbrev State Os R P H D O Aff B Host := EvalStartupAssembly.State Os R P H D O Aff B Host
abbrev InnerControl Os R P H D O Aff B Host :=
  EvalStartupAssembly.InnerControl Os R P H D O Aff B Host
abbrev Memory Os R P H D O Aff B Host C :=
  EvalHostRuntimeConstruction.EnvironmentMemory
    (InnerControl Os R P H D O Aff B Host) C (Payload Os R P H D O Aff B Host)

set_option autoImplicit false in
structure HostEffects (S Os E : Type) where
  communicate : Bool
  isolatedOp : EvalUnixConstruction.IsolatedOp
  hostPid : EStateM StepError S UInt32
  currentDirectory : EStateM StepError S (Except (IoError.HostError E) Os)
  setCurrentDirectory : Os → EStateM StepError S (Except (IoError.HostError E) Unit)
  userHomeDirectory : EStateM StepError S (Option Os)
  temporaryDirectory : EStateM StepError S Os

private def outerStrings
    {Os R P H D O Aff B Host C : Type}
    (host : EvalHostRuntimeConstruction.OsHostEffects Os)
    (memory : Memory Os R P H D O Aff B Host C) :
    OsStrings.Hooks Provenance (State Os R P H D O Aff B Host) Os EnvVars.Kind := by
  let inner := EvalHostRuntimeConstruction.osStringsFromMemory host memory
  exact {
    hostWindows := inner.hostWindows
    hostUnix := inner.hostUnix
    targetWindows := inner.targetWindows
    fromUnixBytes := inner.fromUnixBytes
    fromUtf8 := inner.fromUtf8
    fromWide := inner.fromWide
    toWide := inner.toWide
    encodedBytes := inner.encodedBytes
    encodedLength := inner.encodedLength
    readCString := fun pointer => ExecutionStateTransport.action (inner.readCString pointer)
    readWideString := fun pointer => ExecutionStateTransport.action (inner.readWideString pointer)
    writeCString := fun bytes pointer capacity =>
      ExecutionStateTransport.action (inner.writeCString bytes pointer capacity)
    writeWideString := fun units pointer capacity =>
      ExecutionStateTransport.action (inner.writeWideString units pointer capacity)
    arrayLayout := fun wide count =>
      ExecutionStateTransport.action (inner.arrayLayout wide count)
    allocate := fun layout kind => ExecutionStateTransport.action (inner.allocate layout kind) }

private def lift (value : Except StepError A) : EStateM StepError S A :=
  match value with | .ok result => pure result | .error error => throw error

private def innerScalar
    (memory : Memory Os R P H D O Aff B Host C)
    (operand : OpTy Provenance) :
    EStateM StepError
      (EvalHostRuntimeConstruction.RuntimeState (InnerControl Os R P H D O Aff B Host))
      (Scalar Provenance) := do
  let immediate ← PlaceMachine.readImmediate memory.access operand
  lift (immediate.imm.toScalar.mapError ScalarOps.immediateError)

/-- Assemble the exact Windows environment hooks for the already initialized
source world. Construction does not create another environment map or process
identity; guest variables live in the canonical EnvVars root. -/
def fromSource [DecidableEq MiriMemoryKind] [DecidableEq Os]
    (p : CompilerProviders.Prepared)
    (host : EvalHostRuntimeConstruction.OsHostEffects Os)
    (hostEffects : EvalHostRuntimeConstruction.EnvironmentHostEffects
      (InnerControl Os R P H D O Aff B Host))
    (memory : Memory Os R P H D O Aff B Host C)
    (place : PlaceHooks Provenance (State Os R P H D O Aff B Host)
      C MachineHooks.FrameExtra)
    (errors : IoError.Hooks (State Os R P H D O Aff B Host) Error)
    (hostConfig : HostEffects (State Os R P H D O Aff B Host) Os Error) :
    Except StepError (WindowsEnvironment.Hooks
      (State Os R P H D O Aff B Host) Os Error EnvVars.Kind) := do
  let target ← p.externStatics.targetFacts |>.mapError StepError.unsupported
  unless target.os == "windows" || target.families.contains "windows" do
    throw (.invalidProgram s!"Windows environment requested for `{target.os}`")
  let host := {host with targetWindows := true}
  let innerEnv := EvalHostRuntimeConstruction.envVarsFromSource host hostEffects
    EvalStartupAssembly.environmentLens .windows memory
  let env := EvalStartupAssembly.outerEnvironmentHooks innerEnv
  let strings := outerStrings host memory
  let u32Layout ← match CompilerPrimitiveFacts.primitiveLayout p.runtime "u32" with
    | .ok layout => pure ⟨layout.ty,layout.layout⟩
    | .error reason => throw (.unsupported s!"compiler u32 layout for Windows environment: {reason}")
  let readU32 := fun operand => ExecutionStateTransport.action do
    let value ← innerScalar memory operand
    lift (value.toUInt32.mapError ScalarOps.scalarError)
  let readPointer := fun operand => ExecutionStateTransport.action do
    let value ← innerScalar memory operand
    lift (value.toPointer memory.access.runtime.base |>.mapError ScalarOps.scalarError)
  let readIsize := fun operand => ExecutionStateTransport.action do
    let value ← innerScalar memory operand
    lift ((value.toTargetIsize memory.access.runtime.pointerSize).map Int64.toInt
      |>.mapError ScalarOps.scalarError)
  let readPlaceU32 := fun destination => ExecutionStateTransport.action do
    let value ← innerScalar memory ⟨.indirect destination.mplace,destination.layout⟩
    lift (value.toUInt32.mapError ScalarOps.scalarError)
  let derefU32 := fun operand => ExecutionStateTransport.action do
    let immediate ← PlaceMachine.readImmediate memory.access operand
    let pointer ← lift (immediate.imm.toScalar |>.mapError ScalarOps.immediateError)
    let pointer ← lift (pointer.toPointer memory.access.runtime.base |>.mapError ScalarOps.scalarError)
    PointerPlaceMachine.fromPointer memory.access pointer u32Layout false
  let writeU32 := fun value destination => do
    let value ← lift (Scalar.fromUInt (BitVec.ofNat 128 value.toNat) (Size.ofBytes 4)
      |>.mapError ScalarOps.scalarError)
    writePlaceImmediate place memory.choice (.scalar value)
      ⟨.memory destination.mplace,destination.layout⟩
  let isolationReject := fun name => do
    match hostConfig.isolatedOp with
    | .allow => pure false
    | .reject .abort => throw (.termination (.unsupportedInIsolation name))
    | .reject .noWarning | .reject .warning | .reject .warningWithoutBacktrace => pure true
  let checkNoIsolation := fun name => do
    if !hostConfig.communicate then throw (.termination (.unsupportedInIsolation name))
  let windows := fun name =>
    match CompilerWindowsConstants.scalar p.namedConstants "c" name with
    | .ok value => pure value
    | .error reason => throw (.unsupported reason)
  let process : EnvVars.ProcessHooks (State Os R P H D O Aff B Host) := {
    communicate := hostConfig.communicate
    family := .windows
    os := target.os
    hostPid := hostConfig.hostPid
    activeThread := do return UInt32.ofNat (← get).machine.threads.activeThread.toNat
    threadIdTryFrom := fun raw => do
      return ((← get).machine.threads.threadIdTryFrom raw.toNat).toOption.map
        fun id => UInt32.ofNat id.toNat }
  pure {
    env,strings,process,errors,readU32,readPointer,readIsize,readPlaceU32,derefU32,writeU32
    isolationReject,checkNoIsolation
    currentDirectory := hostConfig.currentDirectory
    setCurrentDirectory := hostConfig.setCurrentDirectory
    userHomeDirectory := hostConfig.userHomeDirectory
    temporaryDirectory := hostConfig.temporaryDirectory
    windows }

end Miri.Input.EvalWindowsEnvironmentConstruction
