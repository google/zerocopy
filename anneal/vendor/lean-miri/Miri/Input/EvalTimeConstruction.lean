import Miri.Input.CompilerProviders
import Miri.Input.CompilerLibcTypeLayouts
import Miri.Input.CompilerNamedFields
import Miri.Input.EvalCoreMachine
import Miri.Input.EvalTypedSyncMachine
import Miri.Input.HostRuntime
import Miri.Input.EvalStartupAssembly
import Miri.Input.EvalHostRuntimeConstruction
import Miri.Interpreter.CompilerExecutionProviders
import Miri.Interpreter.DeadlineMachine
import Miri.Interpreter.GlobalByteMachine
import Miri.Interpreter.PointerPlaceMachine
import Miri.Interpreter.TimeShims
import Miri.Interpreter.TypedSyncNat

/-! Source-owned time shim construction. The compiler/memory/synchronization
operations are bound here; host clock and chrono timezone operations remain
explicit environment effects because the current source HostRuntime does not
provide those capabilities. -/
namespace Miri.Input.EvalTimeConstruction
open Miri.ABI Miri.Memory Miri.Interpreter Miri.Concurrency

abbrev Host := HostRuntime.Storage
abbrev World Os R P H D O Aff B Poll Instant System Native Profiler :=
  EvalWorld.World Os R P H D O Aff B
    (Host Poll Instant System H D O Native Profiler)
abbrev User Os R P H D O Aff B Poll Instant System Native Profiler :=
  ExecutionStateTransport.Inner (World Os R P H D O Aff B Poll Instant System Native Profiler)
abbrev State Os R P H D O Aff B Poll Instant System Native Profiler :=
  MachineHooks.State MiriMemoryKind
    (User Os R P H D O Aff B Poll Instant System Native Profiler)
abbrev Stored Os R P H D O Aff B Poll Instant System Native Profiler :=
  EvalCoreMachine.Stored Os R P H D O Aff B
    (Host Poll Instant System H D O Native Profiler)

/-- Genuine chrono host operations. `utc` and every conversion are required
inputs; this constructor never substitutes a fixed timestamp or an identity
timezone conversion. TZ lookup itself comes from the guest EnvVars state. -/
structure HostEffects (S TZ Timestamp : Type) where
  utc : TZ
  utcTimestamp : Int64 → EStateM StepError S (Option Timestamp)
  parseTimezone : String → EStateM StepError S (Option TZ)
  withTimezone : Timestamp → TZ → EStateM StepError S TimeShims.BrokenDown

private def lift (value : Except StepError A) : EStateM StepError S A :=
  match value with | .ok result => pure result | .error error => throw error

/- Query the current guest environment on each call, then apply only the
host's `OsString::into_string` conversion. This mirrors `get_env_var("TZ")`:
no host process environment lookup is permitted here. -/
set_option autoImplicit false in
def guestTimezone {Os S : Type} [DecidableEq Os]
    (environment : EnvVars.Hooks (Option Provenance) Os
      S)
    (timezoneString : Os → Except Unit String) :
    EStateM StepError S
      (Option (Except Unit String)) := do
  let value ← EnvVars.getEnv environment (environment.asciiOs "TZ")
  pure (value.map timezoneString)

private def layoutByName (p : CompilerProviders.Prepared) (name : String) :
    EStateM StepError S LocalLayout := do
  let result := match name with
    | "i64" | "u64" => p.primitiveLayout name
    | "FILETIME" => CompilerPrimitiveFacts.namedLayout p.runtime name
    | _ => (CompilerLibcTypeLayouts.layout p.runtime name).mapError toString
  let value ← match result with
    | .ok value => pure value
    | .error reason => throw (.unsupported s!"compiler source layout {name}: {reason}")
  pure ⟨value.ty,value.layout⟩

private def fieldPlace
    (projection : PlaceProjectionHooks Provenance
      (State Os R P H D O Aff B Poll Instant System Native Profiler) C MachineHooks.FrameExtra)
    (choice : C) (parent : MPlaceTy Provenance) (index : Nat) :
    EStateM StepError (State Os R P H D O Aff B Poll Instant System Native Profiler)
      (MPlaceTy Provenance) := do
  let result ← PlaceDynamic.field projection choice ⟨.memory parent.mplace,parent.layout⟩ index
  match result.ref with
  | .memory memory => pure ⟨memory,result.layout⟩
  | .local .. => throw (.invalidProgram "time shim aggregate field became a local")

/-- Bind source time policy to actual compiler facts, validity-aware guest
memory, the single shared typed synchronization runtime, source function-byte
allocation, errno, the canonical guest environment and live HostRuntime
clock/deadline registries. Only chrono and OS-string conversion remain external. -/
def fromSource [DecidableEq MiriMemoryKind] [DecidableEq Os]
    (p : CompilerProviders.Prepared)
    (access : ValidityMachine.Access MiriMemoryKind
      (Stored Os R P H D O Aff B Poll Instant System Native Profiler))
    (projection : PlaceProjectionHooks Provenance
      (State Os R P H D O Aff B Poll Instant System Native Profiler) C MachineHooks.FrameExtra)
    (choice : C)
    (functions : FunctionPointers.Hooks MiriMemoryKind
      (ValidityMachine.UserState
        (Stored Os R P H D O Aff B Poll Instant System Native Profiler)) O)
    (syncEffects : TypedSyncMachine.Effects
      (EvalTypedSyncMachine.State Os R P H D O Aff B Poll Instant System Native Profiler))
    (errors : IoError.Hooks
      (State Os R P H D O Aff B Poll Instant System Native Profiler) Error)
    (clock : Clock.HostHooks Instant System
      (State Os R P H D O Aff B Poll Instant System Native Profiler))
    (systemDurationSince : System → System → EStateM StepError
      (State Os R P H D O Aff B Poll Instant System Native Profiler) (Option Clock.Duration))
    (environment : EnvVars.Hooks (Option Provenance) Os
      (State Os R P H D O Aff B Poll Instant System Native Profiler))
    /- Host `OsString::into_string` conversion only; the value always comes
    from the canonical guest environment hook above. -/
    (timezoneString : Os → Except Unit String)
    (communicate : Bool)
    (host : HostEffects
      (State Os R P H D O Aff B Poll Instant System Native Profiler) TZ Timestamp) :
    Except StepError (TimeShims.Hooks
      (State Os R P H D O Aff B Poll Instant System Native Profiler)
      Instant System TZ Timestamp) := do
  let target ← p.externStatics.targetFacts |>.mapError StepError.unsupported
  let runtime := TypedSyncNat.runtime EvalTypedSyncMachine.views syncEffects
  let pointerCompiler := CompilerExecutionProviders.pointerCompiler p.lifecycle.calls.symbols.facts
  let M := EStateM StepError (State Os R P H D O Aff B Poll Instant System Native Profiler)
  let readScalar : OpTy Provenance → M (Scalar Provenance) := fun operand => do
    let immediate ← ValidityMachine.readImmediate access operand
    match immediate.imm.toScalar with
    | .ok scalar => pure scalar
    | .error error => throw (ScalarOps.immediateError error)
  let writeScalar := fun (scalar : Scalar Provenance) (dest : MPlaceTy Provenance) =>
    writePlaceImmediate projection.place choice (.scalar scalar)
      ⟨.memory dest.mplace,dest.layout⟩
  let writeInt := fun (value : Int) (dest : MPlaceTy Provenance) => do
    let scalar ← lift (Scalar.fromInt value dest.layout.layout.size
      |>.mapError ScalarOps.scalarError)
    writeScalar scalar dest
  let readPlace := fun (place : MPlaceTy Provenance) => do
    readScalar ⟨.indirect place.mplace,place.layout⟩
  let deref := fun (operand : OpTy Provenance) (kind : TimeShims.Layout) => do
    let layout ← match kind with
      | .inferred => pure none
      | .timespec => some <$> layoutByName p "timespec"
      | .filetime => some <$> layoutByName p "FILETIME"
      | .i64 => some <$> layoutByName p "i64"
      | .u64 => some <$> layoutByName p "u64"
      | .machTimebase => some <$> layoutByName p "mach_timebase_info"
    let immediate ← ValidityMachine.readImmediate access operand
    match layout with
    | none => PointerPlaceMachine.fromImmediate access pointerCompiler choice immediate
    | some expected =>
      let scalar ← lift (immediate.imm.toScalar |>.mapError ScalarOps.immediateError)
      let pointer ← lift (scalar.toPointer access.runtime.base |>.mapError ScalarOps.scalarError)
      PointerPlaceMachine.fromPointer access pointer expected false
  let readPointer := fun operand => do
    let scalar ← readScalar operand
    lift (scalar.toPointer access.runtime.base |>.mapError ScalarOps.scalarError)
  let projectNamed := fun (parent : MPlaceTy Provenance) (name : String) => do
    let index ← match CompilerNamedFields.fieldIndex p.runtime parent.layout name with
      | .ok index => pure index
      | .error error => throw error
    fieldPlace projection choice parent index
  let writeFields := fun (values : Array Int) (parent : MPlaceTy Provenance) => do
    for (value,index) in values.toList.zipIdx do
      let dest ← fieldPlace projection choice parent index
      writeInt value dest
  let writeNamed := fun (values : Array (String × Int)) (parent : MPlaceTy Provenance) => do
    for (name,value) in values do
      let dest ← projectNamed parent name
      writeInt value dest
  let writePointer := fun (pointer : Pointer (Option Provenance)) (dest : MPlaceTy Provenance) => do
    let scalar ← lift (Scalar.fromMaybePointer access.runtime.base pointer
      |>.mapError ScalarOps.scalarError)
    writeScalar scalar dest
  let constants := fun (name : String) => do
    lift ((CompilerNamedConstants.scalar p.namedConstants name).mapError StepError.unsupported)
  let getTimezoneEnv := guestTimezone environment timezoneString
  let readI32 := fun operand => do
    let scalar ← readScalar operand
    lift (scalar.toInt32 |>.mapError ScalarOps.scalarError)
  let readU32 := fun operand => do
    let scalar ← readScalar operand
    lift (scalar.toUInt32 |>.mapError ScalarOps.scalarError)
  let readU64 := fun operand => do
    let scalar ← readScalar operand
    lift (scalar.toUInt64 |>.mapError ScalarOps.scalarError)
  let family : ForeignItems.Family :=
    if target.os == "windows" || target.families.contains "windows" then ForeignItems.Family.windows
    else if target.families.contains "unix" then ForeignItems.Family.unix else ForeignItems.Family.other
  pure {
    family := family, os := target.os, communicate := communicate, host := clock
    monotonic := do return (← get).machine.user.payload.payload.user.host.clock
    encodeDeadline := fun deadline => do
      let state ← get
      let user := state.machine.user
      let hostState := user.payload.payload.user.host
      let (registry,token) ← lift (hostState.deadlines.intern deadline)
      let user := {user with payload := {user.payload with payload :=
        {user.payload.payload with user := {user.payload.payload.user with
          host := {hostState with deadlines := registry}}}}}
      set {state with machine := {state.machine with user}}
      pure token
    runtime
    noIsolation := fun name => do
      unless communicate do throw (.termination (.unsupportedInIsolation name))
    systemDurationSinceUnix := fun time => systemDurationSince time clock.unixEpoch
    constant := fun constant => do
      let name := match constant with
        | .realtime => "CLOCK_REALTIME"
        | .monotonic => "CLOCK_MONOTONIC"
        | .realtimeCoarse => "CLOCK_REALTIME_COARSE"
        | .monotonicCoarse => "CLOCK_MONOTONIC_COARSE"
        | .uptimeRaw => "CLOCK_UPTIME_RAW"
        | .timerAbstime => "TIMER_ABSTIME"
      constants name
    readScalar, scalarSigned := fun scalar size =>
      lift (scalar.toInt size |>.mapError ScalarOps.scalarError)
    clockIdSize := do return (← layoutByName p "clockid_t").layout.size
    readI32, readU32, readU64, deref, readPointer
    isNull := fun pointer => pure (pointer.provenance.isNone && pointer.offset.bytes == 0)
    projectNamed, readSignedPlace := fun place => do
      lift ((← readPlace place).toInt place.layout.layout.size |>.mapError ScalarOps.scalarError)
    writeFields, writeNamed, writeInt, writePointer
    dedupBytes := fun bytes => do
      return (← GlobalByteMachine.bytes functions bytes.data).withOptionalProvenance
    setEinvalAndReturnNeg1 := IoError.setErrnoAndReturnNeg1I32 errors (.libc "EINVAL")
    utcTimestamp := host.utcTimestamp
    getTimezoneEnv
    utc := host.utc
    parseTimezone := host.parseTimezone
    withTimezone := host.withTimezone }

/-- Source entry point that constructs the guest TZ environment hook from the
same EvalWorld root and memory bundle used by startup. The chrono/timezone
database and OsString::into_string conversion remain genuine explicit host
capabilities; clock, deadline registry, errno and typed synchronization are
still derived by fromSource from the canonical runtime inputs. -/
def fromSourceWithEnvironment [DecidableEq MiriMemoryKind] [DecidableEq Os]
    (p : CompilerProviders.Prepared)
    (memory : EvalHostRuntimeConstruction.EnvironmentMemory
      (EvalStartupAssembly.InnerControl Os R P H D O Aff
        B (Host Poll Instant System H D O Native Profiler)) C P)
    (environmentHost : EvalHostRuntimeConstruction.EnvironmentHostEffects
      (EvalStartupAssembly.InnerControl Os R P H D O Aff
        B (Host Poll Instant System H D O Native Profiler)))
    (osHost : EvalHostRuntimeConstruction.OsHostEffects Os)
    (functions : FunctionPointers.Hooks MiriMemoryKind
      (ValidityMachine.UserState
        (Stored Os R P H D O Aff B Poll Instant System Native Profiler)) O)
    (syncEffects : TypedSyncMachine.Effects
      (EvalTypedSyncMachine.State Os R P H D O Aff B Poll Instant System Native Profiler))
    (errors : IoError.Hooks
      (State Os R P H D O Aff B Poll Instant System Native Profiler) Error)
    (clock : Clock.HostHooks Instant System
      (State Os R P H D O Aff B Poll Instant System Native Profiler))
    (systemDurationSince : System → System → EStateM StepError
      (State Os R P H D O Aff B Poll Instant System Native Profiler) (Option Clock.Duration))
    (timezoneString : Os → Except Unit String)
    (communicate : Bool)
    (host : HostEffects
      (State Os R P H D O Aff B Poll Instant System Native Profiler) TZ Timestamp) :
    Except StepError (TimeShims.Hooks
      (State Os R P H D O Aff B Poll Instant System Native Profiler)
      Instant System TZ Timestamp) := do
  let target ← p.externStatics.targetFacts |>.mapError StepError.unsupported
  let family :=
    if target.os == "windows" || target.families.contains "windows" then ForeignItems.Family.windows
    else if target.families.contains "unix" then ForeignItems.Family.unix
    else ForeignItems.Family.other
  let environment := EvalHostRuntimeConstruction.envVarsFromSource
    osHost environmentHost EvalStartupAssembly.environmentLens family memory
  fromSource p memory.access memory.projection memory.choice functions syncEffects
    errors clock systemDurationSince environment timezoneString communicate host

/-- Construct a futex deadline with the same actual host/virtual clock and
deadline registry used by TimeShims. Keeping this helper here prevents a
second deadline map or an elapsed-time placeholder in the futex constructor. -/
def timeoutDeadline {S Instant System TZ Timestamp : Type}
    (time : TimeShims.Hooks S Instant System TZ Timestamp)
    (clock : Clock.TimeoutClock) (style : Clock.TimeoutStyle)
    (duration : Clock.Duration) : EStateM StepError S ThreadDeadline := do
  let deadline ← Clock.timeout time.host (← time.monotonic) time.communicate clock style duration
  time.encodeDeadline deadline

end Miri.Input.EvalTimeConstruction
