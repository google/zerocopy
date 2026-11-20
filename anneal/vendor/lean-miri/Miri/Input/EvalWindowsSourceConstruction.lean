import Miri.Input.EvalWindowsEnvironmentDispatchConstruction
import Miri.Input.EvalWindowsFileConstruction
import Miri.Input.EvalWindowsThreadConstruction
import Miri.Input.CompilerFrameMetadata
import Miri.Interpreter.FrameMetadata
import Miri.Interpreter.ForeignItems
import Miri.Interpreter.TimeShimDispatch
import Miri.Interpreter.WindowsPlatformDispatch
import Miri.Interpreter.WindowsRandomDispatch
import Miri.Interpreter.WindowsSyncDispatch
import Miri.Interpreter.StdOnlyShims

/-! Assemble the canonical Windows environment, file and thread foreign-item
families over one prepared compiler target and one initialized Main machine.
The component constructors own guest memory, process/environment tables,
descriptor/handle state and TLS/thread operations. Host interaction remains
explicit at the source boundary. -/
namespace Miri.Input.EvalWindowsSourceConstruction
open Miri.ABI Miri.Memory Miri.MIR Miri.Interpreter

abbrev Payload Os R P H D O Aff B Host :=
  EvalWindowsFileConstruction.Payload Os R P H D O Aff B Host
abbrev State Os R P H D O Aff B Host :=
  EvalWindowsFileConstruction.State Os R P H D O Aff B Host
abbrev FileRef H D O := EvalWindowsFileConstruction.Ref H D O
abbrev M S A := EStateM StepError S A

set_option autoImplicit false in
structure Components
    (Os R P H D O Aff B Host C Error HM Path Time : Type) where
  environment : WindowsEnvironmentDispatch.Hooks
    (State Os R P H D O Aff B Host) Os Error EnvVars.Kind
  files : WindowsFileDispatch.Hooks
    (State Os R P H D O Aff B Host) (FileRef H D O) H D Path HM Time Error EnvVars.Kind
  thread : WindowsThreadDispatch.Hooks
    (State Os R P H D O Aff B Host) (FileRef H D O)
  frameInStd : EStateM StepError (State Os R P H D O Aff B Host) Bool

/-- Build the core Windows foreign families from narrow host capabilities and
the same source Main, EvalWorld memory and descriptor registry. `timeHooks`
contains source time policy plus the required clock/timezone effects;
filesystem calls consume `hostFiles` and `hostWindowsFiles`. -/
def fromSource
    {Os R P H D O Aff B Host C Error HM Path Instant Time Zone Timestamp : Type}
    [DecidableEq MiriMemoryKind] [DecidableEq Os]
    (p : CompilerProviders.Prepared)
    (host : EvalHostRuntimeConstruction.OsHostEffects Os)
    (environmentHost : EvalHostRuntimeConstruction.EnvironmentHostEffects
      (EvalWindowsEnvironmentConstruction.InnerControl Os R P H D O Aff B Host))
    (environmentMemory : EvalWindowsEnvironmentConstruction.Memory
      Os R P H D O Aff B Host C)
    (place : PlaceHooks Provenance
      (State Os R P H D O Aff B Host) C MachineHooks.FrameExtra)
    (errors : IoError.Hooks (State Os R P H D O Aff B Host) Error)
    (environmentHostConfig : EvalWindowsEnvironmentConstruction.HostEffects
      (State Os R P H D O Aff B Host) Os Error)
    (main : MainMachine.Hooks (Payload Os R P H D O Aff B Host) C O ABI.ExternAbi
      (FnAbi TyId) (ArgAbi TyId) Aff ProgramExitPoll)
    (fileRegistry : Files.Hooks (State Os R P H D O Aff B Host) H D O Error HM)
    (readiness : ReadinessMachine.Hooks MiriMemoryKind
      (ThreadStacks.Storage (Payload Os R P H D O Aff B Host)) H D O)
    (sharedOpen : UnixOpen.Hooks (State Os R P H D O Aff B Host) H D O Error HM Path)
    (prepareDirectory : D → Path → M (State Os R P H D O Aff B Host) D)
    (otherMetadata : O → M (State Os R P H D O Aff B Host)
      (Sum (Except (IoError.HostError Error) HM) String))
    (timeHooks : TimeShims.Hooks
      (State Os R P H D O Aff B Host) Instant Time Zone Timestamp)
    (hostWindowsFiles : EvalWindowsFileConstruction.HostEffects
      Os (State Os R P H D O Aff B Host) Path H D O HM Time Error)
    (checkPointerAccess : Pointer (Option Provenance) → Size →
      M (State Os R P H D O Aff B Host) Unit)
    (choice : C) (compatibilityBudget : Nat)
    (projection : PlaceProjectionHooks Provenance
      (State Os R P H D O Aff B Host) C MachineHooks.FrameExtra)
    (userRelevantCrates : Array Nat)
    (threadError : Concurrency.ThreadError → StepError) :
    Except StepError (Components Os R P H D O Aff B Host C Error HM Path Time) := do
  let target ← p.externStatics.targetFacts |>.mapError StepError.unsupported
  unless target.os == "windows" || target.families.contains "windows" do
    throw (.invalidProgram s!"Windows source assembly requested for `{target.os}`")
  let environment ← EvalWindowsEnvironmentDispatchConstruction.fromSource
    p host environmentHost environmentMemory place choice compatibilityBudget errors
    environmentHostConfig
  let files ← EvalWindowsFileConstruction.fromSource p main environment fileRegistry readiness
    sharedOpen prepareDirectory otherMetadata timeHooks hostWindowsFiles place
    checkPointerAccess choice compatibilityBudget projection threadError
  let thread ← EvalWindowsThreadConstruction.fromSource p main environment
    files.paths.files.handles place choice compatibilityBudget
  unless environment.env.process.os == target.os &&
      environment.env.env.family == .windows && environment.env.process.family == .windows &&
      files.paths.files.os == target.os && files.paths.files.communicate ==
        environment.env.process.communicate do
    throw (.invalidProgram "Windows source families disagree on compiler target or communication policy")
  let frames := CompilerFrameMetadata.hooks p.lifecycle.frames userRelevantCrates
  pure ⟨environment,files,thread,FrameMetadata.frameInStd frames⟩

/-- Demand-local assembly for a partially constructed Windows source closure.
Environment, files and threads are always real source components from
`fromSource`; the independently ported time/sync/random/platform/std-only
families can be attached as they become available. A recognized operation
whose family is absent returns Unsupported at the operation boundary, while
an unrelated Windows symbol continues through the canonical fallback. -/
def dispatch [DecidableEq Os] {ForeignBody Destination : Type}
    (components : Components Os R P H D O Aff B Host C Error HM Path Time)
    (time : Option (TimeShimDispatch.Hooks
      (State Os R P H D O Aff B Host) ClockInstant Time TZ Timestamp))
    (sync : Option (WindowsSyncDispatch.Hooks
      (State Os R P H D O Aff B Host) SyncRef))
    (random : Option (WindowsRandomDispatch.Hooks
      (State Os R P H D O Aff B Host) Destination ForeignBody I))
    (platform : Option (WindowsPlatformDispatch.Hooks
      (State Os R P H D O Aff B Host) Os Error EnvVars.Kind (FileRef H D O)))
    (stdOnly : Option (StdOnlyShims.WindowsHooks Provenance
      (State Os R P H D O Aff B Host) Destination (MPlaceTy Provenance) ForeignBody I))
    (base : ForeignItems.Hooks Provenance
      (State Os R P H D O Aff B Host) Destination (MPlaceTy Provenance)
      (Pointer (Option Provenance)) ForeignBody I)
    (name : String) (abi : FnAbi TyId) (args : Array (OpTy Provenance))
    (dest : MPlaceTy Provenance) :
    M (State Os R P H D O Aff B Host) ForeignItems.EmulateItemResult := do
  if base.family != .windows || base.os != "windows" ||
      components.environment.env.env.family != .windows ||
      components.environment.env.process.family != .windows then
    throw (.invalidProgram "Windows source dispatcher target mismatch")
  let result ← WindowsEnvironmentDispatch.dispatch components.environment name abi args dest
  if result != .NotSupported then return result
  let result ← WindowsFileDispatch.dispatch components.files name abi args dest
  if result != .NotSupported then return result
  let handles := components.files.paths.files.handles
  let thread := {components.thread with thread := {components.thread.thread with handles}}
  let result ← WindowsThreadDispatch.dispatch thread name abi args dest
  if result != .NotSupported then return result
  match time with
  | some time =>
    let result ← TimeShimDispatch.dispatch time name abi args dest
    if result != .NotSupported then return result
  | none =>
    if let some operation := TimeShimDispatch.parse name then
      if (TimeShimDispatch.signature operation).systemAbi then
        throw (.unsupported s!"Windows time operation `{name}` has no installed source clock capability")
  match sync with
  | some sync =>
    let result ← WindowsSyncDispatch.dispatch sync name abi args dest
    if result != .NotSupported then return result
  | none =>
    if (WindowsSyncDispatch.parse name).isSome then
      throw (.unsupported s!"Windows synchronization operation `{name}` has no installed source runtime")
  match random with
  | some random =>
    let random := {random with signatures := {random.signatures with foreign := base.toCore}}
    if let some result ← WindowsRandomDispatch.emulate random name abi args dest then return result
  | none =>
    if #["SystemFunction036", "ProcessPrng", "BCryptGenRandom"].contains name then
      throw (.unsupported s!"Windows random operation `{name}` has no installed source entropy capability")
  match platform with
  | some platform =>
    let platform := {platform with platform := {platform.platform with
      environment := components.environment.env, handles}}
    let result ← WindowsPlatformDispatch.dispatch platform name abi args dest
    if result != .NotSupported then return result
  | none =>
    if (WindowsPlatformDispatch.parse name).isSome then
      throw (.unsupported s!"Windows platform operation `{name}` has no installed source handler")
  match stdOnly with
  | some stdOnly =>
    let stdOnly := {stdOnly with foreign := base.toCore}
    let result ← StdOnlyShims.windowsCore stdOnly name abi args dest
    if result != .NotSupported then return result
  | none =>
    if #["NtQueryVolumeInformationFile", "GetProcessHeap", "GetModuleHandleA",
        "SetConsoleTextAttribute", "AddVectoredExceptionHandler", "SetThreadStackGuarantee",
        "SwitchToThread", "GetFinalPathNameByHandleW"].contains name &&
        (← components.frameInStd) then
      throw (.unsupported s!"Windows std-only operation `{name}` has no installed source frame/runtime capability")
  base.windows name abi args dest

/-- Initial Windows dispatch before Main-bound file/thread callbacks exist.
Environment, random, and std-only operations are still source-built on the
canonical startup state. File, thread, time, sync, and platform names fail
closed only when requested; unrelated names continue through the Core
fallback. -/
def dispatchInitial [DecidableEq Os] {ForeignBody Destination : Type}
    (environment : WindowsEnvironmentDispatch.Hooks
      (State Os R P H D O Aff B Host) Os Error EnvVars.Kind)
    (time : Option (TimeShimDispatch.Hooks
      (State Os R P H D O Aff B Host) ClockInstant Time TZ Timestamp))
    (sync : Option (WindowsSyncDispatch.Hooks
      (State Os R P H D O Aff B Host) SyncRef))
    (random : Option (WindowsRandomDispatch.Hooks
      (State Os R P H D O Aff B Host) Destination ForeignBody I))
    (platform : Option (WindowsPlatformDispatch.Hooks
      (State Os R P H D O Aff B Host) Os Error EnvVars.Kind (FileRef H D O)))
    (stdOnly : Option (StdOnlyShims.WindowsHooks Provenance
      (State Os R P H D O Aff B Host) Destination (MPlaceTy Provenance) ForeignBody I))
    (base : ForeignItems.Hooks Provenance
      (State Os R P H D O Aff B Host) Destination (MPlaceTy Provenance)
      (Pointer (Option Provenance)) ForeignBody I)
    (name : String) (abi : FnAbi TyId) (args : Array (OpTy Provenance))
    (dest : MPlaceTy Provenance) :
    M (State Os R P H D O Aff B Host) ForeignItems.EmulateItemResult := do
  if base.family != .windows || base.os != "windows" ||
      environment.env.process.family != .windows then
    throw (.invalidProgram "Windows initial source dispatcher target mismatch")
  let result ← WindowsEnvironmentDispatch.dispatch environment name abi args dest
  if result != .NotSupported then return result
  if (WindowsFileDispatch.parse name).isSome then
    throw (.unsupported s!"Windows file operation `{name}` requires the live Main file registry")
  if (WindowsThreadDispatch.parse name).isSome then
    throw (.unsupported s!"Windows thread operation `{name}` requires the live Main thread registry")
  match time with
  | some time =>
    let result ← TimeShimDispatch.dispatch time name abi args dest
    if result != .NotSupported then return result
  | none =>
    if let some operation := TimeShimDispatch.parse name then
      if (TimeShimDispatch.signature operation).systemAbi then
        throw (.unsupported s!"Windows time operation `{name}` has no installed source clock capability")
  match sync with
  | some sync =>
    let result ← WindowsSyncDispatch.dispatch sync name abi args dest
    if result != .NotSupported then return result
  | none =>
    if (WindowsSyncDispatch.parse name).isSome then
      throw (.unsupported s!"Windows synchronization operation `{name}` has no installed source runtime")
  match random with
  | some random =>
    let random := {random with signatures := {random.signatures with foreign := base.toCore}}
    if let some result ← WindowsRandomDispatch.emulate random name abi args dest then return result
  | none =>
    if #["SystemFunction036", "ProcessPrng", "BCryptGenRandom"].contains name then
      throw (.unsupported s!"Windows random operation `{name}` has no installed source entropy capability")
  match platform with
  | some platform =>
    let platform := {platform with platform := {platform.platform with environment := environment.env}}
    let result ← WindowsPlatformDispatch.dispatch platform name abi args dest
    if result != .NotSupported then return result
  | none =>
    if (WindowsPlatformDispatch.parse name).isSome then
      throw (.unsupported s!"Windows platform operation `{name}` has no installed source handler")
  match stdOnly with
  | some stdOnly =>
    let stdOnly := {stdOnly with foreign := base.toCore}
    let result ← StdOnlyShims.windowsCore stdOnly name abi args dest
    if result != .NotSupported then return result
  | none => pure ()
  base.windows name abi args dest

/-- Bind the demand-local source dispatcher into the common foreign-item
chain. Missing component families stay explicit and fail only after their
exact names reach the dispatcher. -/
def bind [DecidableEq Os] {ForeignBody Destination : Type}
    (components : Components Os R P H D O Aff B Host C Error HM Path Time)
    (time : Option (TimeShimDispatch.Hooks
      (State Os R P H D O Aff B Host) ClockInstant Time TZ Timestamp))
    (sync : Option (WindowsSyncDispatch.Hooks
      (State Os R P H D O Aff B Host) SyncRef))
    (random : Option (WindowsRandomDispatch.Hooks
      (State Os R P H D O Aff B Host) Destination ForeignBody I))
    (platform : Option (WindowsPlatformDispatch.Hooks
      (State Os R P H D O Aff B Host) Os Error EnvVars.Kind (FileRef H D O)))
    (stdOnly : Option (StdOnlyShims.WindowsHooks Provenance
      (State Os R P H D O Aff B Host) Destination (MPlaceTy Provenance) ForeignBody I))
    (base : ForeignItems.Hooks Provenance
      (State Os R P H D O Aff B Host) Destination (MPlaceTy Provenance)
      (Pointer (Option Provenance)) ForeignBody I) :=
  { base with
    windows := fun name abi args dest =>
      dispatch components time sync random platform stdOnly base name abi args dest }

end Miri.Input.EvalWindowsSourceConstruction
