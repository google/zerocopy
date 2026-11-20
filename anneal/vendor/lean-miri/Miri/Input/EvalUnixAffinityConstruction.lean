import Miri.Input.CompilerProviders
import Miri.Input.CompilerPrimitiveFacts
import Miri.Input.CompilerNamedShimAbi
import Miri.Input.CompilerLibcConstants
import Miri.Input.EvalCoreMachine
import Miri.Input.EvalHostRuntimeConstruction
import Miri.Input.EvalUnixSourceConstruction
import Miri.Input.EvalSocketStorage
import Miri.Interpreter.CpuAffinityDispatch
import Miri.Interpreter.RawMemoryMachine
import Miri.Interpreter.UnixForeign

/-! Source CPU-affinity shims over the canonical thread runtime and guest
memory. The mask state is the same `MachineGCRoots.Storage.threads.affinity`
field inherited by newly created threads; no host-derived mask or shadow
thread table is introduced. -/
namespace Miri.Input.EvalUnixAffinityConstruction
open Miri.ABI Miri.Memory Miri.MIR Miri.Interpreter
open Miri.Concurrency

abbrev Other Raw Listener TcpStream Error :=
  EvalUnixSourceConstruction.Other Raw Listener TcpStream Error
abbrev World Os R P H D B Poll Instant System Native Profiler Raw Listener TcpStream Error :=
  EvalSocketStorage.World Os R P H D CpuAffinity.Mask B Poll Instant System Native Profiler Raw Listener TcpStream Error
abbrev Stored Os R P H D B Poll Instant System Native Profiler Raw Listener TcpStream Error :=
  EvalCoreMachine.Stored Os R P H D (Other Raw Listener TcpStream Error) CpuAffinity.Mask B
    (HostRuntime.Storage Poll Instant System H D (Other Raw Listener TcpStream Error) Native Profiler)
private def lift {S : Type} (result : Except StepError A) : EStateM StepError S A :=
  match result with
  | .ok value => pure value
  | .error error => throw error

private def readScalar [DecidableEq MiriMemoryKind]
    (access : PlaceMachine.AccessConfig MiriMemoryKind
      (PointerMachine.User (ValidityMachine.Control
        (Stored Os R P H D B Poll Instant System Native Profiler Raw Listener TcpStream Error))))
    (operand : OpTy Provenance) : EStateM StepError
      (EvalUnixSourceConstruction.State Os R P H D CpuAffinity.Mask B Poll Instant System Native Profiler Raw Listener TcpStream Error)
      (Scalar Provenance) := do
  let immediate ← ValidityMachine.readImmediate access operand
  lift (immediate.imm.toScalar.mapError ScalarOps.immediateError)

private def modifyAffinity
    (f : ThreadMachine.Runtime CpuAffinity.Mask → ThreadMachine.Runtime CpuAffinity.Mask) :
    EStateM StepError
      (EvalUnixSourceConstruction.State Os R P H D CpuAffinity.Mask B Poll Instant System Native Profiler Raw Listener TcpStream Error) Unit := do
  let state ← get
  let user := state.machine.user
  let world : World Os R P H D B Poll Instant System Native Profiler Raw Listener TcpStream Error :=
    user.payload.payload.user
  let sourceRuntime := world.runtime
  let runtime := f sourceRuntime.threads
  let world := {world with runtime := {sourceRuntime with threads := runtime}}
  let storage := user.payload.payload
  let storage := {storage with user := world}
  let control := {user.payload with payload := storage}
  let user := {user with payload := control}
  set {state with machine := {state.machine with user}}

/-- Build the recognized affinity handler at the final source rebind seam.
Only the canonical `EnvironmentMemory`, environment, common foreign Core,
place writer and execution choice enter. Scalar/pointer reads, guest bytes,
thread-mask storage, TID mapping, errno, compiler layouts/constants and shim
ABI are all derived here from those source owners. -/
def handlerFromSource [DecidableEq MiriMemoryKind]
    (p : CompilerProviders.Prepared)
    (memory : EvalHostRuntimeConstruction.EnvironmentMemory
      (ValidityMachine.Control
        (Stored Os R P H D B Poll Instant System Native Profiler Raw Listener TcpStream Error))
      C Payload)
    (environment : UnixEnvironmentDispatch.Hooks
      (EvalUnixSourceConstruction.State Os R P H D CpuAffinity.Mask B Poll Instant System Native Profiler Raw Listener TcpStream Error)
      Os Error EnvVars.Kind)
    (place : PlaceHooks Provenance
      (EvalUnixSourceConstruction.State Os R P H D CpuAffinity.Mask B Poll Instant System Native Profiler Raw Listener TcpStream Error)
      C MachineHooks.FrameExtra)
    (choice : C)
    (foreign : ForeignItems.Core Provenance
      (EvalUnixSourceConstruction.State Os R P H D CpuAffinity.Mask B Poll Instant System Native Profiler Raw Listener TcpStream Error)
      (RuntimePlace Provenance) (MPlaceTy Provenance)
      (Pointer (Option Provenance)) LoadedBody CallInstance) :
    UnixForeign.OptionalHandler
      (EvalUnixSourceConstruction.State Os R P H D CpuAffinity.Mask B Poll Instant System Native Profiler Raw Listener TcpStream Error) := Id.run do
  let access := memory.access
  let process := environment.env.process
  let affinity : CpuAffinity.Hooks Provenance
      (EvalUnixSourceConstruction.State Os R P H D CpuAffinity.Mask B Poll Instant System Native Profiler Raw Listener TcpStream Error)
      (MPlaceTy Provenance) := {
    os := environment.env.os
    endian := access.runtime.base.endian
    cpuCount := environment.env.numCpus
    chunkSize := do
      match CompilerPrimitiveFacts.cULongLayout p.runtime with
      | .ok layout => pure layout.layout.size.bytes.toNat
      | .error reason => throw (.unsupported s!"compiler c_ulong layout: {reason}")
    readU32 := fun operand => do
      let scalar ← readScalar access operand
      lift (scalar.toUInt32.mapError ScalarOps.scalarError)
    readI32 := fun operand => do
      let scalar ← readScalar access operand
      lift (scalar.toInt32.mapError ScalarOps.scalarError)
    readI64 := fun operand => do
      let scalar ← readScalar access operand
      lift (scalar.toInt64.mapError ScalarOps.scalarError)
    readUsize := fun operand => do
      let scalar ← readScalar access operand
      lift (scalar.toTargetUsize access.runtime.pointerSize |>.mapError ScalarOps.scalarError)
    readPointer := fun operand => do
      let scalar ← readScalar access operand
      lift (scalar.toPointer access.runtime.base |>.mapError ScalarOps.scalarError)
    isNull := fun pointer => pure (pointer.provenance.isNone && pointer.offset.bytes == 0)
    masks := do
      let user := (← get).machine.user
      let world : World Os R P H D B Poll Instant System Native Profiler Raw Listener TcpStream Error :=
        user.payload.payload.user
      pure world.runtime.threads.affinity
    putMasks := fun masks => modifyAffinity fun runtime =>
      {runtime with affinity := some masks}
    active := do return (← get).machine.threads.activeThread
    linuxTid := fun tid => do
      unless environment.env.os == "linux" || environment.env.os == "android" do
        throw (.invalidProgram "get_thread_id_from_linux_tid target assertion")
      let pid ← ForeignItems.getPid process.communicate process.hostPid
      if tid < pid then return none
      return (← get).machine.threads.threadIdTryFrom (tid - pid).toNat |>.toOption
    readBytes := RawMemoryMachine.readBytes access memory.pointers.arithmetic
    writeBytes := RawMemoryMachine.writeBytes access memory.pointers.arithmetic
    writeZero := fun destination => do
      let scalar ← lift (Scalar.fromUInt (BitVec.ofNat 128 0)
        destination.layout.layout.size |>.mapError ScalarOps.scalarError)
      writePlaceImmediate place choice (.scalar scalar)
        ⟨.memory destination.mplace,destination.layout⟩
    errnoNegOne := fun name destination =>
      IoError.setErrnoAndReturnNeg1 environment.env.errors (.libc name) destination
    libcI32 := fun name =>
      match CompilerLibcConstants.i32 p.namedConstants name with
      | .ok value => pure value
      | .error reason => throw (.unsupported s!"compiler libc constant `{name}`: {reason}") }
  let dispatch : CpuAffinityDispatch.CoreHooks Provenance
      (EvalUnixSourceConstruction.State Os R P H D CpuAffinity.Mask B Poll Instant System Native Profiler Raw Listener TcpStream Error)
      (RuntimePlace Provenance) (MPlaceTy Provenance) LoadedBody CallInstance :=
    ⟨affinity,foreign,CompilerNamedShimAbi.query p.namedAbi⟩
  return fun name abi args destination => CpuAffinityDispatch.emulateCore dispatch name abi args destination

end Miri.Input.EvalUnixAffinityConstruction
