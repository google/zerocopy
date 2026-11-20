import Miri.Input.CompilerCallConstruction
import Miri.Input.CompilerForeignSymbols
import Miri.Input.CompilerNamedShimAbi
import Miri.Input.CompilerPrimitiveFacts
import Miri.Input.CompilerProviders
import Miri.Input.CompilerWindowsConstants
import Miri.Input.CompilerWindowsTypeLayouts
import Miri.Input.EvalTimeConstruction
import Miri.Input.EvalWindowsEnvironmentConstruction
import Miri.Input.EvalWindowsFileConstruction
import Miri.Input.EvalForeignSyncMachine
import Miri.Input.EvalTypedSyncMachine
import Miri.Input.EvalBackendMachine
import Miri.Interpreter.DeadlineMachine
import Miri.Interpreter.ForeignSyncMachine
import Miri.Interpreter.IntrinsicAtomic
import Miri.Interpreter.IoError
import Miri.Interpreter.MainMachine
import Miri.Interpreter.PointerPlaceMachine
import Miri.Interpreter.WindowsSyncDispatch
import Miri.Interpreter.ExecutionStateTransport
import Miri.Interpreter.TypedSyncNat

/-! Canonical source construction for Windows time and synchronization.
Time delegates its guest memory, environment, clock and typed-runtime wiring to
the shared source time constructor. Windows INIT_ONCE/WaitOnAddress hooks are
derived here from exact compiler facts, Main memory, the shared typed sync
arena, the source atomic backend and the canonical deadline registry. -/
namespace Miri.Input.EvalWindowsSyncTimeConstruction
open Miri.ABI Miri.Memory Miri.MIR Miri.Interpreter Miri.Concurrency

abbrev Payload Os R P H D O Aff B Host :=
  EvalWindowsFileConstruction.Payload Os R P H D O Aff B Host
abbrev State Os R P H D O Aff B Host :=
  EvalWindowsFileConstruction.State Os R P H D O Aff B Host
private def lift {S : Type} (result : Except StepError A) : EStateM StepError S A :=
  match result with | .ok value => pure value | .error error => throw error

private def scalar (p : CompilerProviders.Prepared) (name : String) :
    EStateM StepError S (Scalar Provenance) :=
  match CompilerWindowsConstants.scalar p.namedConstants "c" name with
  | .ok value => pure value
  | .error reason => throw (.unsupported reason)

private def layout (p : CompilerProviders.Prepared) (name : String) :
    Except StepError LocalLayout := do
  match CompilerWindowsTypeLayouts.layout p.runtime name with
  | .ok value => pure ⟨value.ty,value.layout⟩
  | .error reason => throw (.unsupported s!"compiler Windows layout `{name}`: {reason}")

private def projectField [DecidableEq MiriMemoryKind]
    (projection : PlaceProjectionHooks Provenance
      (State Os R P H D O Aff B Host) C MachineHooks.FrameExtra)
    (choice : C) (parent : MPlaceTy Provenance) (index : Nat) :
    EStateM StepError (State Os R P H D O Aff B Host) (MPlaceTy Provenance) := do
  let value ← PlaceDynamic.field projection choice ⟨.memory parent.mplace,parent.layout⟩ index
  match value.ref with
  | .memory memory => pure ⟨memory,value.layout⟩
  | .local .. => throw (.invalidProgram "Windows INIT_ONCE field projected to a local")

/-- Build Windows synchronization behavior over the canonical Main state and
the one typed synchronization arena. The supplied atomic and deadline hooks
are the physical source leaves already selected for that Main machine; all
guest pointers, constants, layouts, ABI checks and transmutation are derived
from `main` and `p`. -/
def syncFromSource
    {Os R P H D O Aff B Host C Error Instant System : Type}
    [DecidableEq MiriMemoryKind]
    (p : CompilerProviders.Prepared)
    (main : MainMachine.Hooks (Payload Os R P H D O Aff B Host) C O ABI.ExternAbi
      (FnAbi TyId) (ArgAbi TyId) Aff ProgramExitPoll)
    (objects : ForeignSyncMachine.Objects (State Os R P H D O Aff B Host))
    (atomic : AtomicAccessHooks Provenance (State Os R P H D O Aff B Host)
      C (RuntimePlace Provenance))
    (projection : PlaceProjectionHooks Provenance
      (State Os R P H D O Aff B Host) C MachineHooks.FrameExtra)
    (choice : C)
    (deadline : DeadlineMachine.Hooks MiriMemoryKind
      (ExecutionStateTransport.Inner (EvalCoreMachine.World Os R P H D O Aff B Host))
      Instant System)
    (errors : IoError.Hooks (State Os R P H D O Aff B Host) Error)
    (compatibilityBudget : Nat) :
    Except StepError (WindowsSyncDispatch.Hooks
      (State Os R P H D O Aff B Host) TypedSyncRuntime.Ref) := do
  let target ← p.externStatics.targetFacts |>.mapError StepError.unsupported
  unless target.os == "windows" || target.families.contains "windows" do
    throw (.invalidProgram s!"Windows sync requested for `{target.os}`")
  let initLayout ← layout p "INIT_ONCE"
  let symbols ← p.foreignSymbols
    |>.mapError StepError.unsupported
  let i32Raw ← CompilerPrimitiveFacts.primitiveLayout p.runtime "i32"
    |>.mapError (fun e => StepError.unsupported s!"compiler i32 layout for Windows sync: {e}")
  let i32Layout : LocalLayout := ⟨i32Raw.ty,i32Raw.layout⟩
  let access := main.access
  let readScalar := fun (operand : OpTy Provenance) => do
    let value ← PlaceMachine.readImmediate access operand
    lift (value.imm.toScalar.mapError ScalarOps.immediateError)
  let readPointer := fun operand => do
    let value ← readScalar operand
    lift (value.toPointer access.runtime.base |>.mapError ScalarOps.scalarError)
  let readU32 := fun operand => do
    let value ← readScalar operand
    lift (value.toUInt32 |>.mapError ScalarOps.scalarError)
  let readUsize := fun operand => do
    let value ← readScalar operand
    lift (value.toTargetUsize access.runtime.pointerSize |>.mapError ScalarOps.scalarError)
  let alignment : PointerPlaceMachine.AlignmentContext
      (ThreadStacks.Storage (Payload Os R P H D O Aff B Host)) := {
    policy := fun storage => storage.user.payload.alignment
    promises := fun storage => storage.user.symbolicAlignment }
  let placeForPointer := fun (pointer : Pointer (Option Provenance)) (pointee : LocalLayout) => do
    let mismatch ← PointerPlaceMachine.misalignmentWith access alignment pointer
      pointee.layout.align.abi
    pure (⟨⟨pointer,.none,mismatch⟩,pointee⟩ : MPlaceTy Provenance)
  let deref := fun (operand : OpTy Provenance) (pointee : LocalLayout) => do
    placeForPointer (← readPointer operand) pointee
  let derefInitOnce := fun operand => deref operand initLayout
  let readFieldZero := fun (place : MPlaceTy Provenance) => do
    let field ← projectField projection choice place 0
    let value ← PlaceMachine.readImmediate access ⟨.indirect field.mplace,field.layout⟩
    let scalar ← lift (value.imm.toScalar.mapError ScalarOps.immediateError)
    lift (scalar.toTargetUsize access.runtime.pointerSize |>.mapError ScalarOps.scalarError)
  let derefPending := fun operand => deref operand i32Layout
  let atomicLoad := fun pointer size => do
    let pointee ← match size.bytes with
      | 1 => lift (layout p "u8")
      | 2 => lift (layout p "u16")
      | 4 => lift (layout p "u32")
      | 8 => lift (layout p "u64")
      | _ => throw (.invalidProgram "Windows WaitOnAddress atomic width escaped source validation")
    let place ← placeForPointer pointer pointee
    let target : RuntimePlace Provenance := ⟨.memory place.mplace,place.layout⟩
    let current ← get
    match (EvalBackendMachine.handler (ExecutionStateTransport.inward current).machine) with
    | .error error => throw error
    | .ok .none => IntrinsicAtomic.load atomic choice target .Acquire
    | .ok (.vclocks _) => IntrinsicAtomic.load atomic choice target .Acquire
  let seqCstFence := do
    let current ← get
    match EvalBackendMachine.handler (ExecutionStateTransport.inward current).machine with
    | .error error => throw error
    | .ok .none => IntrinsicAtomic.fence atomic .SeqCst false
    | .ok (.vclocks _) => IntrinsicAtomic.fence atomic .SeqCst false
  let windowsSync : WindowsSync.Hooks
      (State Os R P H D O Aff B Host) TypedSyncRuntime.Ref := {
    once := objects.once
    metadata := TypedSyncObjectMachine.full objects.metadata objects.bytes
      TypedSyncObjectMachine.windows
    constant32 := fun key => do
      let name := match key with
        | .initFailed => "INIT_ONCE_INIT_FAILED"
        | .infinite => "INFINITE"
        | .invalidParameter => "ERROR_INVALID_PARAMETER"
        | .timeout => "ERROR_TIMEOUT"
        | .trueValue => "TRUE"
        | .falseValue => "FALSE"
      let value ← scalar p name
      lift (value.toUInt32 |>.mapError ScalarOps.scalarError)
    constantBool := fun key => do
      let name := match key with | .trueValue => "TRUE" | _ => "FALSE"
      let value ← scalar p name
      lift (value.toInt32 |>.mapError ScalarOps.scalarError)
    readPointer
    isNull := fun value => pure (value.provenance.isNone && value.offset.bytes == 0)
    readU32
    readUsize
    derefInitOnce
    readInitPointerFieldZero := readFieldZero
    derefPendingBool := derefPending
    newFutex := objects.newFutex
    monotonicDeadlineMillis := fun milliseconds =>
      ExecutionStateTransport.action (DeadlineMachine.monotonicDeadlineMillis deadline milliseconds)
    seqCstFence
    readAtomicAcquire := atomicLoad
    readScalar := fun pointer size => do
      let pointee ← match size.bytes with
        | 1 => lift (layout p "u8")
        | 2 => lift (layout p "u16")
        | 4 => lift (layout p "u32")
        | 8 => lift (layout p "u64")
        | _ => throw (.invalidProgram "Windows address comparison width escaped source validation")
      let place ← placeForPointer pointer pointee
      let value ← PlaceMachine.readImmediate access ⟨.indirect place.mplace,place.layout⟩
      lift (value.imm.toScalar.mapError ScalarOps.immediateError)
    lastError := fun key =>
      let name := match key with | .timeout => "ERROR_TIMEOUT" | _ => "ERROR_INVALID_PARAMETER"
      IoError.setLastError errors (.windows name)
  }
  let base : WindowsSyncDispatch.Hooks
      (State Os R P H D O Aff B Host) TypedSyncRuntime.Ref := {
    windows := windowsSync
    systemConvention := do
      return (← CompilerNamedShimAbi.query p.namedAbi "InitOnceBeginInitialize").conv
    expectedAbi := fun name request => do
      let some operation := WindowsSyncDispatch.parse name |
        throw (.unsupported s!"Windows sync ABI requested for unknown `{name}`")
      unless WindowsSyncDispatch.signature operation == request do
        throw (.invalidProgram s!"Windows sync ABI recipe disagrees with `{name}`")
      let abi ← CompilerNamedShimAbi.query p.namedAbi name
      unless abi.args.size == request.args.size do
        throw (.unsupported s!"compiler Windows sync ABI for `{name}` has an unexpected arity")
      pure abi
    argumentCompat := (CompilerCallConstruction.compiler p compatibilityBudget).checkArgumentCompat choice
    checkSymbolClash := fun name =>
      match CompilerForeignSymbols.checkSymbolClash symbols name with
      | .ok () => pure ()
      | .error error => throw error
    transmute := fun operand expected => do
      match operand.transmute (← projection.place.projection choice) expected |>.mapError
          IntrinsicVectorMachine.projectionError with
      | .ok value => pure value
      | .error error => throw error
  }
  pure base

/-- Construct Windows time shims from the same initialized environment and
memory bundle used by the source Windows components. Only chrono's UTC/timezone
operations and host OsString conversion remain explicit leaves. -/
def timeFromSource
    {Os R P H D O Aff B Poll Instant System Native Profiler C Error TZ Timestamp : Type}
    [DecidableEq MiriMemoryKind] [DecidableEq Os]
    (p : CompilerProviders.Prepared)
    (memory : EvalWindowsEnvironmentConstruction.Memory
      Os R P H D O Aff B (EvalTimeConstruction.Host Poll Instant System H D O Native Profiler) C)
    (environmentHost : EvalHostRuntimeConstruction.EnvironmentHostEffects
      (EvalWindowsEnvironmentConstruction.InnerControl Os R P H D O Aff B
        (EvalTimeConstruction.Host Poll Instant System H D O Native Profiler)))
    (osHost : EvalHostRuntimeConstruction.OsHostEffects Os)
    (functions : FunctionPointers.Hooks MiriMemoryKind
      (ValidityMachine.UserState (EvalTimeConstruction.Stored Os R P H D O Aff B
        Poll Instant System Native Profiler)) O)
    (syncEffects : TypedSyncMachine.Effects
      (EvalTypedSyncMachine.State Os R P H D O Aff B Poll Instant System Native Profiler))
    (errors : IoError.Hooks
      (EvalTimeConstruction.State Os R P H D O Aff B Poll Instant System Native Profiler) Error)
    (clock : Clock.HostHooks Instant System
      (EvalTimeConstruction.State Os R P H D O Aff B Poll Instant System Native Profiler))
    (systemDurationSince : System → System → EStateM StepError
      (EvalTimeConstruction.State Os R P H D O Aff B Poll Instant System Native Profiler)
      (Option Clock.Duration))
    (timezoneString : Os → Except Unit String)
    (communicate : Bool)
    (host : EvalTimeConstruction.HostEffects
      (EvalTimeConstruction.State Os R P H D O Aff B Poll Instant System Native Profiler) TZ Timestamp) :
    Except StepError (TimeShims.Hooks
      (State Os R P H D O Aff B (EvalTimeConstruction.Host Poll Instant System H D O Native Profiler))
      Instant System TZ Timestamp) := do
  let timeMemory : (EvalHostRuntimeConstruction.EnvironmentMemory
      (EvalStartupAssembly.InnerControl Os R P H D O Aff B
        (EvalTimeConstruction.Host Poll Instant System H D O Native Profiler)) C P) := {
    access := memory.access
    allocation := memory.allocation
    deallocate := memory.deallocate
    pointers := memory.pointers
    projection := memory.projection
    arrays := memory.arrays
    symbolicAlignment := memory.symbolicAlignment
    enforceAlignment := memory.enforceAlignment
    stringScanBudget := memory.stringScanBudget
    choice := memory.choice
    pointerTy := memory.pointerTy
    pointerLayout := memory.pointerLayout }
  let result ← EvalTimeConstruction.fromSourceWithEnvironment p timeMemory environmentHost osHost
    functions syncEffects errors clock systemDurationSince timezoneString communicate host
  unless result.family == .windows && result.os == "windows" do
    throw (.invalidProgram "Windows time constructor did not select the canonical Windows target")
  let outer {A : Type} (action : EStateM StepError
      (EvalTimeConstruction.State Os R P H D O Aff B Poll Instant System Native Profiler) A) :=
    ExecutionStateTransport.action action
  let runtime := TypedSyncNat.outward EvalTypedSyncMachine.views syncEffects
  pure {
    family := result.family
    os := result.os
    communicate := result.communicate
    host := {
      monotonicNow := outer result.host.monotonicNow
      systemNow := outer result.host.systemNow
      unixEpoch := result.host.unixEpoch
      checkedAddMonotonic := fun now duration => outer (result.host.checkedAddMonotonic now duration)
      checkedAddSystem := fun now duration => outer (result.host.checkedAddSystem now duration)
      durationSince := fun later earlier => outer (result.host.durationSince later earlier)
      sleep := fun duration => outer (result.host.sleep duration) }
    monotonic := outer result.monotonic
    encodeDeadline := fun deadline => outer (result.encodeDeadline deadline)
    runtime
    noIsolation := fun name => outer (result.noIsolation name)
    systemDurationSinceUnix := fun time => outer (result.systemDurationSinceUnix time)
    constant := fun value => outer (result.constant value)
    readScalar := fun operand => outer (result.readScalar operand)
    scalarSigned := fun scalar size => outer (result.scalarSigned scalar size)
    clockIdSize := outer result.clockIdSize
    readI32 := fun operand => outer (result.readI32 operand)
    readU32 := fun operand => outer (result.readU32 operand)
    readU64 := fun operand => outer (result.readU64 operand)
    deref := fun operand kind => outer (result.deref operand kind)
    readPointer := fun operand => outer (result.readPointer operand)
    isNull := fun pointer => outer (result.isNull pointer)
    projectNamed := fun place name => outer (result.projectNamed place name)
    readSignedPlace := fun place => outer (result.readSignedPlace place)
    writeFields := fun values place => outer (result.writeFields values place)
    writeNamed := fun values place => outer (result.writeNamed values place)
    writeInt := fun value place => outer (result.writeInt value place)
    writePointer := fun pointer place => outer (result.writePointer pointer place)
    dedupBytes := fun bytes => outer (result.dedupBytes bytes)
    setEinvalAndReturnNeg1 := outer result.setEinvalAndReturnNeg1
    utcTimestamp := fun timestamp => outer (result.utcTimestamp timestamp)
    getTimezoneEnv := outer result.getTimezoneEnv
    utc := result.utc
    parseTimezone := fun timezone => outer (result.parseTimezone timezone)
    withTimezone := fun timestamp timezone => outer (result.withTimezone timestamp timezone) }

end Miri.Input.EvalWindowsSyncTimeConstruction
