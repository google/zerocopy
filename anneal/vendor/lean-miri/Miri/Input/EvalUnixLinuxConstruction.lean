import Miri.Input.CompilerProviders
import Miri.Input.CompilerNamedShimAbi
import Miri.Input.EvalUnixNativeFdConstruction
import Miri.Input.EvalUnixConstruction
import Miri.Input.EvalUnixMemoryConstruction
import Miri.Input.EvalHostRuntimeConstruction
import Miri.Input.EvalSocketStorage
import Miri.Interpreter.FunctionPointers
import Miri.Interpreter.LinuxForeign
import Miri.Interpreter.LinuxMemory
import Miri.Interpreter.ShimSignatures
import Miri.Interpreter.ThreadStacks
import Miri.Interpreter.UnixThreadDispatch
import Miri.Interpreter.ValidityMachine

/-! Source construction for Linux foreign-item runtime bindings over canonical
inner EvalWorld memory. Function identity, static lookup and TLS registration
read the one live function registry, static registry and TLS arena. -/
namespace Miri.Input.EvalUnixLinuxConstruction
open Miri.ABI Miri.Memory Miri.MIR Miri.Interpreter

structure Components (S Place H D O E HM Os B I : Type) where
  linuxPlatform : LinuxForeign.Hooks S Place H D O E HM Os B I

abbrev SourceWorld Os R P H D Aff B Poll Instant System Native Profiler Raw Listener TcpStream Error :=
  EvalSocketStorage.World Os R P H D Aff B Poll Instant System Native Profiler Raw Listener TcpStream Error
abbrev SourceControl Os R P H D Aff B Poll Instant System Native Profiler Raw Listener TcpStream Error :=
  ValidityMachine.Control (ThreadStacks.Storage
    (SourceWorld Os R P H D Aff B Poll Instant System Native Profiler Raw Listener TcpStream Error))
abbrev SourceUser Os R P H D Aff B Poll Instant System Native Profiler Raw Listener TcpStream Error :=
  EvalSocketStorage.User Os R P H D Aff B Poll Instant System Native Profiler Raw Listener TcpStream Error
abbrev SourceState Os R P H D Aff B Poll Instant System Native Profiler Raw Listener TcpStream Error :=
  EvalSocketStorage.State Os R P H D Aff B Poll Instant System Native Profiler Raw Listener TcpStream Error

private def readI64
    (signatures : ShimSignatures.Hooks Provenance
      (SourceState Os R P H D Aff B Poll Instant System Native Profiler Raw Listener TcpStream Error) Place
      (MPlaceTy Provenance) (Pointer (Option Provenance)) ShimBody I)
    (operand : OpTy Provenance) : EStateM StepError
      (SourceState Os R P H D Aff B Poll Instant System Native Profiler Raw Listener TcpStream Error) Int64 := do
  let scalar ← signatures.readScalar operand
  match scalar.toInt64 with
  | .ok value => pure value
  | .error error => throw (ScalarOps.scalarError error)

private def sourceDsoHandle :
    EStateM StepError
      (SourceState Os R P H D Aff B Poll Instant System Native Profiler Raw Listener TcpStream Error)
      (Pointer (Option Provenance)) := do
  let world := (← get).machine.user.payload.payload.user
  let entries := world.runtime.externStatics.symbols.filter (·.1 == "__dso_handle")
  unless entries.size == 1 do throw (.invalidProgram "canonical __dso_handle static missing or duplicated")
  let some (_,pointer) := entries[0]? | throw (.invalidProgram "checked __dso_handle entry missing")
  pure (Pointer.withOptionalProvenance pointer)

private def sourceAtexit
    (spans : AllocationDriver.SpanHooks)
    (fnInstance : CallInstance) (data : Scalar Provenance) :
    EStateM StepError
      (SourceState Os R P H D Aff B Poll Instant System Native Profiler Raw Listener TcpStream Error) Unit :=
  do
    let active := (← get).machine.threads.activeThread
    let span ← AllocationDriver.currentUserRelevantSpan spans
    modify fun state =>
      let pointerUser : SourceUser Os R P H D Aff B Poll Instant System Native Profiler Raw Listener TcpStream Error := state.machine.user
      let control : SourceControl Os R P H D Aff B Poll Instant System Native Profiler Raw Listener TcpStream Error := pointerUser.payload
      let storage : ThreadStacks.Storage
        (SourceWorld Os R P H D Aff B Poll Instant System Native Profiler Raw Listener TcpStream Error) := control.payload
      let world : SourceWorld Os R P H D Aff B Poll Instant System Native Profiler Raw Listener TcpStream Error := storage.user
      let tls : ThreadTlsMachine.Data := world.runtime.tls
      let values := tls.values.addThreadAtexit active ⟨fnInstance,data,span⟩
      let world := {world with runtime := {world.runtime with tls := {tls with values}}}
      let storage := {storage with user := world}
      let control := {control with payload := storage}
      {state with machine := {state.machine with user := {pointerUser with payload := control}}}

set_option autoImplicit false in
/-- Build the Linux component in the actual inner EvalWorld state. Its Unix
memory fields come from `EvalUnixMemoryConstruction.fromSource`, including
compiler-layout checked pointer-output dereference, source range validation,
and Miri's Zero-growth mmap reallocation for mremap. -/
def fromSource {Os R P H D Aff B Poll Instant System Native Profiler Raw Listener TcpStream Error
    E ShimBody I HM C Path : Type} [DecidableEq MiriMemoryKind]
    (p : CompilerProviders.Prepared)
    (userRelevantCrates : Array Nat)
    (environment : UnixEnvironmentDispatch.Hooks
      (SourceState Os R P H D Aff B Poll Instant System Native Profiler Raw Listener TcpStream Error)
      Os E EnvVars.Kind)
    (signatures : ShimSignatures.Hooks Provenance
      (SourceState Os R P H D Aff B Poll Instant System Native Profiler Raw Listener TcpStream Error) Miri.MIR.Place
      (MPlaceTy Provenance) (Pointer (Option Provenance)) ShimBody I)
    (fd : UnixFdDispatch.Hooks
      (SourceState Os R P H D Aff B Poll Instant System Native Profiler Raw Listener TcpStream Error)
      H D (EvalSocketStorage.Other Raw Listener TcpStream Error) E HM Path)
    (unixGettid : String → EStateM StepError
      (SourceState Os R P H D Aff B Poll Instant System Native Profiler Raw Listener TcpStream Error)
      (Scalar Provenance))
    (place : PlaceHooks Provenance
      (SourceState Os R P H D Aff B Poll Instant System Native Profiler Raw Listener TcpStream Error)
      C MachineHooks.FrameExtra)
    (choice : C)
    (pageSize : UInt64)
    (memory : EvalHostRuntimeConstruction.EnvironmentMemory
      (SourceControl Os R P H D Aff B Poll Instant System Native Profiler Raw Listener TcpStream Error) C P)
    (extras : MemoryExtras.Hooks MiriMemoryKind
      (SourceUser Os R P H D Aff B Poll Instant System Native Profiler Raw Listener TcpStream Error) P)
    (spans : AllocationDriver.SpanHooks)
    (functions : FunctionPointers.Hooks MiriMemoryKind
      (SourceUser Os R P H D Aff B Poll Instant System Native Profiler Raw Listener TcpStream Error)
      (EvalSocketStorage.Other Raw Listener TcpStream Error)) :
    Except StepError (Components
      (SourceState Os R P H D Aff B Poll Instant System Native Profiler Raw Listener TcpStream Error)
      Miri.MIR.Place H D (EvalSocketStorage.Other Raw Listener TcpStream Error) E HM Path ShimBody I) := do
  let target ← p.externStatics.targetFacts |>.mapError StepError.unsupported
  unless (target.os == "linux" || target.os == "android") && target.families.contains "unix" do
    throw (.invalidProgram s!"Linux foreign hooks requested on `{target.os}`")
  unless environment.env.os == target.os && fd.file.fd.os == target.os &&
      signatures.foreign.os == target.os do
    throw (.invalidProgram "Linux foreign components disagree on compiler target OS")
  let memory ← EvalUnixMemoryConstruction.fromSource p userRelevantCrates environment
    signatures memory extras spans place choice pageSize
  let getPtrFnInstance := fun pointer => do
    match ← FunctionPointers.getPtrFn functions pointer with
    | .Instance fn => pure fn
    | .Other _ => throw (.unsupported "GNU atexit destructor is not a compiler instance")
  let linuxPlatform : LinuxForeign.Hooks
      (SourceState Os R P H D Aff B Poll Instant System Native Profiler Raw Listener TcpStream Error)
      Miri.MIR.Place H D (EvalSocketStorage.Other Raw Listener TcpStream Error) E HM Path ShimBody I := {
    signatures
    signature := CompilerNamedShimAbi.query p.namedAbi
    fd
    memory
    errors := environment.env.errors
    readScalar := signatures.readScalar
    readI64 := readI64 signatures
    writeInt := fun value destination => do
      let scalar ← match Scalar.fromInt value destination.layout.layout.size with
        | .ok scalar => pure scalar
        | .error error => throw (ScalarOps.scalarError error)
      writePlaceImmediate place choice (.scalar scalar)
        ⟨.memory destination.mplace,destination.layout⟩
    unixGettid := unixGettid
    targetEnv := target.env
    dsoHandle := sourceDsoHandle
    getPtrFnInstance
    addThreadAtexit := sourceAtexit spans }
  pure ⟨linuxPlatform⟩

end Miri.Input.EvalUnixLinuxConstruction
