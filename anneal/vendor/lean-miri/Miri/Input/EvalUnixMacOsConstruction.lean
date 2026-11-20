import Miri.Input.CompilerProviders
import Miri.Input.CompilerNamedShimAbi
import Miri.Input.CompilerLibcConstants
import Miri.Input.CompilerPrimitiveFacts
import Miri.Input.EvalHostRuntimeConstruction
import Miri.Input.EvalSyncMachine
import Miri.Input.EvalSyncObjectAccess
import Miri.Input.EvalTypedSyncMachine
import Miri.Input.EvalCallbackMachine
import Miri.Input.EvalUnixSourceConstruction
import Miri.Interpreter.MacOsForeignMachine
import Miri.Interpreter.UnixFd
import Miri.Interpreter.UnixForeign
import Miri.Interpreter.MainMachine
import Miri.Interpreter.TypedSyncObjectMachine
import Miri.Interpreter.ExecutionStateTransport
import Miri.Interpreter.RawMemoryMachine
import Miri.Interpreter.ReallocationDriver
import Miri.Interpreter.PointerPlaceMachine

/-! Source macOS foreign-item construction over the initialized Main state,
canonical callback sync arena, source environment and the shared native FD
registry. The sync projection below creates no new object tables. -/
namespace Miri.Input.EvalUnixMacOsConstruction
open Miri.ABI Miri.Memory Miri.MIR Miri.Interpreter Miri.Concurrency

abbrev Other Raw Listener TcpStream Error :=
  EvalUnixSourceConstruction.Other Raw Listener TcpStream Error
abbrev User Os R P H D Aff B Poll Instant System Native Profiler Raw Listener TcpStream Error :=
  EvalUnixSourceConstruction.User Os R P H D Aff B Poll Instant System Native Profiler
    Raw Listener TcpStream Error
abbrev State Os R P H D Aff B Poll Instant System Native Profiler Raw Listener TcpStream Error :=
  EvalSyncMachine.State Os R P H D (Other Raw Listener TcpStream Error) Aff B Poll Instant System Native Profiler
abbrev Control Os R P H D Aff B Poll Instant System Native Profiler Raw Listener TcpStream Error :=
  EvalUnixSourceConstruction.Control Os R P H D Aff B Poll Instant System Native Profiler
    Raw Listener TcpStream Error

private def lift {S : Type} (value : Except StepError A) : EStateM StepError S A :=
  match value with | .ok result => pure result | .error error => throw error

def syncFromSource [DecidableEq MiriMemoryKind]
    (p : CompilerProviders.Prepared)
    (memory : EvalHostRuntimeConstruction.EnvironmentMemory
      (Control Os R EvalSyncObjectAccess.Payload H D Aff B Poll Instant System Native Profiler Raw Listener TcpStream Error)
      C EvalSyncObjectAccess.Payload)
    (objects : ForeignSyncMachine.Objects
      (LinuxFutexMachine.State MiriMemoryKind
        (EvalSyncMachine.World Os R EvalSyncObjectAccess.Payload H D
          (Other Raw Listener TcpStream Error) Aff B Poll Instant System Native Profiler)))
    (futex : LinuxFutexMachine.Hooks MiriMemoryKind
      (EvalSyncMachine.World Os R EvalSyncObjectAccess.Payload H D
        (Other Raw Listener TcpStream Error) Aff B Poll Instant System Native Profiler)
      C EvalSyncObjectAccess.Payload (Other Raw Listener TcpStream Error) B Instant System Zone Timestamp ErrorHost)
    (choice : C)
    (time : Option (TimeShims.Hooks
      (LinuxFutexMachine.State MiriMemoryKind
        (EvalSyncMachine.World Os R EvalSyncObjectAccess.Payload H D
          (Other Raw Listener TcpStream Error) Aff B Poll Instant System Native Profiler))
      Instant System Zone Timestamp))
    (hostUsizeBits semaphoreBudget : Nat) :
    Except StepError (MacOsSync.Hooks
      (LinuxFutexMachine.State MiriMemoryKind
        (EvalSyncMachine.World Os R EvalSyncObjectAccess.Payload H D
          (Other Raw Listener TcpStream Error) Aff B Poll Instant System Native Profiler))
      TypedSyncRuntime.Ref) := do
  let u8 : LocalLayout ← match p.primitiveLayout "u8" with
    | .ok value => pure ⟨value.ty, value.layout⟩
    | .error reason => throw (.unsupported s!"compiler u8 layout for macOS sync: {reason}")
  let u32 : LocalLayout ← match p.primitiveLayout "u32" with
    | .ok value => pure ⟨value.ty, value.layout⟩
    | .error reason => throw (.unsupported s!"compiler u32 layout for macOS sync: {reason}")
  let u64 : LocalLayout ← match p.primitiveLayout "u64" with
    | .ok value => pure ⟨value.ty, value.layout⟩
    | .error reason => throw (.unsupported s!"compiler u64 layout for macOS sync: {reason}")
  let base : MacOsSync.Hooks
      (LinuxFutexMachine.State MiriMemoryKind
        (EvalSyncMachine.World Os R EvalSyncObjectAccess.Payload H D
          (Other Raw Listener TcpStream Error) Aff B Poll Instant System Native Profiler))
      TypedSyncRuntime.Ref := {
    endian := futex.access.runtime.base.endian
    runtime := objects.runtime
    readPointer := fun operand => do
      let immediate ← PlaceMachine.readImmediate futex.access operand
      let scalar ← lift (immediate.imm.toScalar.mapError ScalarOps.immediateError)
      lift (scalar.toPointer futex.access.runtime.base |>.mapError ScalarOps.scalarError)
    readImmediate := PlaceMachine.readImmediate futex.access
    readUsize := fun operand => do
      let immediate ← PlaceMachine.readImmediate futex.access operand
      let scalar ← lift (immediate.imm.toScalar.mapError ScalarOps.immediateError)
      lift (scalar.toTargetUsize futex.access.runtime.pointerSize |>.mapError ScalarOps.scalarError)
    readIsize := fun operand => do
      let immediate ← PlaceMachine.readImmediate futex.access operand
      let scalar ← lift (immediate.imm.toScalar.mapError ScalarOps.immediateError)
      let value ← lift (scalar.toTargetIsize futex.access.runtime.pointerSize |>.mapError ScalarOps.scalarError)
      pure value.toInt
    readU32 := fun operand => do
      let immediate ← PlaceMachine.readImmediate futex.access operand
      let scalar ← lift (immediate.imm.toScalar.mapError ScalarOps.immediateError)
      lift (scalar.toUInt32 |>.mapError ScalarOps.scalarError)
    readU64 := fun operand => do
      let immediate ← PlaceMachine.readImmediate futex.access operand
      let scalar ← lift (immediate.imm.toScalar.mapError ScalarOps.immediateError)
      lift (scalar.toUInt64 |>.mapError ScalarOps.scalarError)
    readI64 := fun operand => do
      let immediate ← PlaceMachine.readImmediate futex.access operand
      let scalar ← lift (immediate.imm.toScalar.mapError ScalarOps.immediateError)
      lift (scalar.toInt64 |>.mapError ScalarOps.scalarError)
    libcU32 := fun name => do
      let scalar : Scalar Provenance ← match CompilerLibcConstants.scalar p.namedConstants name with
        | .ok value => pure value
        | .error reason => throw (.unsupported s!"compiler libc constant `{name}`: {reason}")
      lift (scalar.toUInt32 |>.mapError ScalarOps.scalarError)
    timeout := DeadlineMachine.timeout futex.deadline .monotonic
    absoluteDeadline := fun nanos => do
      let duration ← lift (Clock.Duration.fromNanos nanos.toNat)
      DeadlineMachine.timeout futex.deadline .monotonic .absolute duration
    timeAfter := fun nanos => do
      let some time := time | throw (.unsupported "dispatch_time requires source time capability")
      let clock ← time.monotonic
      let now ← clock.now time.host
      let delta ← lift (Clock.Duration.fromNanos nanos.toNat)
      let after ← now.addLossy time.host delta
      return (← after.durationSince time.host clock.epoch).asNanos
    readAcquireBits := fun pointer size => do
      let layout := if size == 4 then u32 else u64
      let place ← PointerPlaceMachine.fromPointer futex.access pointer layout false
      let target : RuntimePlace Provenance := ⟨.memory place.mplace, place.layout⟩
      let selected ← lift (futex.backend (← get))
      let value ← match selected with
        | .none | .vclocks _ => IntrinsicAtomic.load futex.atomic choice target .Acquire
      lift (value.toBits (Size.ofBytes size) |>.mapError ScalarOps.scalarError)
    seqCstFence := do
      match ← lift (futex.backend (← get)) with
      | .none | .vclocks _ => IntrinsicAtomic.fence futex.atomic .SeqCst false
    futexMetadata := TypedSyncObjectMachine.narrow objects.metadata TypedSyncObjectMachine.macFutex
    newFutex := objects.newMacFutex
    settings := objects.macSettings
    putSettings := objects.putMacSettings
    lockMetadata := TypedSyncObjectMachine.full objects.metadata objects.bytes TypedSyncObjectMachine.macLock
    semaphoreMetadata := TypedSyncObjectMachine.full objects.metadata objects.bytes TypedSyncObjectMachine.macSemaphore
    derefLock := fun operand => do
      let pointer ← do
        let immediate ← PlaceMachine.readImmediate futex.access operand
        let scalar ← lift (immediate.imm.toScalar.mapError ScalarOps.immediateError)
        lift (scalar.toPointer futex.access.runtime.base |>.mapError ScalarOps.scalarError)
      let layout ← match CompilerLibcTypeLayouts.layout p.runtime "os_unfair_lock_s" with
        | .ok value => pure ⟨value.ty, value.layout⟩
        | .error reason => throw (.unsupported s!"compiler libc type layout: {reason}")
      PointerPlaceMachine.fromPointer futex.access pointer layout false
    derefByte := fun immediate => do
      let scalar ← lift (immediate.imm.toScalar.mapError ScalarOps.immediateError)
      let pointer ← lift (scalar.toPointer futex.access.runtime.base |>.mapError ScalarOps.scalarError)
      PointerPlaceMachine.fromPointer futex.access pointer u8 false
    readLockValue := fun place => do
      let value ← PlaceMachine.readImmediate futex.access ⟨.indirect place.mplace, place.layout⟩
      let scalar ← lift (value.imm.toScalar.mapError ScalarOps.immediateError)
      lift (scalar.toUInt32 |>.mapError ScalarOps.scalarError)
    newMutex := objects.pthread.newMutex
    newSemaphore := objects.pthread.newSemaphore
    allocateRuntimeByte := do
      let pointer ← ReallocationDriver.allocateConfigured futex.allocation u8.layout.size
        u8.layout.align.abi (.machine .runtime) .Uninit
      pure ⟨⟨pointer.withOptionalProvenance, .none, none⟩, u8⟩
    immediatePointer := fun immediate => do
      let scalar ← lift (immediate.imm.toScalar.mapError ScalarOps.immediateError)
      lift (scalar.toPointer futex.access.runtime.base |>.mapError ScalarOps.scalarError)
    deallocateRuntime := fun pointer => memory.deallocate pointer none (.machine .runtime)
    resetLockRelaxed := fun operand => do
      let place ← do
        let pointer ← do
          let immediate ← PlaceMachine.readImmediate futex.access operand
          let scalar ← lift (immediate.imm.toScalar.mapError ScalarOps.immediateError)
          lift (scalar.toPointer futex.access.runtime.base |>.mapError ScalarOps.scalarError)
        let layout ← match CompilerLibcTypeLayouts.layout p.runtime "os_unfair_lock_s" with
          | .ok value => pure ⟨value.ty, value.layout⟩
          | .error reason => throw (.unsupported s!"compiler libc type layout: {reason}")
        PointerPlaceMachine.fromPointer futex.access pointer layout false
      let zero ← lift (Scalar.fromUInt (BitVec.ofNat 128 0) place.layout.layout.size
        |>.mapError ScalarOps.scalarError)
      IntrinsicAtomic.store futex.atomic choice ⟨.memory place.mplace, place.layout⟩
        ⟨.scalar zero, place.layout⟩ .Relaxed
    writePointer := fun pointer destination => do
      let scalar ← lift (Scalar.fromMaybePointer futex.access.runtime.base pointer
        |>.mapError ScalarOps.scalarError)
      writePlaceImmediate (PlaceMachine.placeHooks futex.access futex.allocation futex.compiler) choice
        (.scalar scalar) ⟨.memory destination.mplace, destination.layout⟩
    writeInt := fun value destination => do
      let scalar ← lift (Scalar.fromInt value destination.layout.layout.size |>.mapError ScalarOps.scalarError)
      writePlaceImmediate (PlaceMachine.placeHooks futex.access futex.allocation futex.compiler) choice
        (.scalar scalar) ⟨.memory destination.mplace, destination.layout⟩
    writeBool := fun value destination => do
      let scalar := Scalar.fromBool value
      writePlaceImmediate (PlaceMachine.placeHooks futex.access futex.allocation futex.compiler) choice
        (.scalar scalar) ⟨.memory destination.mplace, destination.layout⟩
    errnoNegOne := fun name destination =>
      IoError.setErrnoAndReturnNeg1 futex.errors (.libc name) destination
    hostUsizeBits
    semaphoreBudget }
  pure (ForeignSyncMachine.mac objects base)

/-- Assemble the remaining macOS foreign-item arm from the selected source
Core, source environment/Main/TLS engines, native-FD registry, and the same
callback-owned synchronization arena. Host executable-path conversion is a
raw host result because its representation is outside the guest memory model;
if that host leaf is absent, only `_NSGetExecutablePath` fails on demand. -/
def handlerFromSource [DecidableEq MiriMemoryKind]
    (p : CompilerProviders.Prepared)
    (core : ForeignItems.Core Provenance
      (LinuxFutexMachine.State MiriMemoryKind
        (EvalSyncMachine.World Os R EvalSyncObjectAccess.Payload H D
          (Other Raw Listener TcpStream Error) Aff B Poll Instant System Native Profiler))
      (RuntimePlace Provenance) (RuntimePlace Provenance)
      (Pointer (Option Provenance)) LoadedBody CallInstance)
    (environment : UnixEnvironment.Hooks
      (LinuxFutexMachine.State MiriMemoryKind
        (EvalSyncMachine.World Os R EvalSyncObjectAccess.Payload H D
          (Other Raw Listener TcpStream Error) Aff B Poll Instant System Native Profiler))
      Os Error EnvVars.Kind)
    (main : MainMachine.Hooks
      (EvalCallbackMachine.ThreadUser Os R EvalSyncObjectAccess.Payload H D
        (Other Raw Listener TcpStream Error) Aff B Poll Instant System Native Profiler)
      C (Other Raw Listener TcpStream Error) ABI.ExternAbi
      (FnAbi TyId) (ArgAbi TyId) Aff EvalSyncObjectAccess.Payload)
    (memory : EvalHostRuntimeConstruction.EnvironmentMemory
      (Control Os R EvalSyncObjectAccess.Payload H D Aff B Poll Instant System Native Profiler Raw Listener TcpStream Error)
      C EvalSyncObjectAccess.Payload)
    (objects : ForeignSyncMachine.Objects
      (LinuxFutexMachine.State MiriMemoryKind
        (EvalSyncMachine.World Os R EvalSyncObjectAccess.Payload H D
          (Other Raw Listener TcpStream Error) Aff B Poll Instant System Native Profiler)))
    (futex : LinuxFutexMachine.Hooks MiriMemoryKind
      (EvalSyncMachine.World Os R EvalSyncObjectAccess.Payload H D
        (Other Raw Listener TcpStream Error) Aff B Poll Instant System Native Profiler)
      C EvalSyncObjectAccess.Payload (Other Raw Listener TcpStream Error) B Instant System Zone Timestamp ErrorHost)
    (time : Option (TimeShims.Hooks
      (LinuxFutexMachine.State MiriMemoryKind
        (EvalSyncMachine.World Os R EvalSyncObjectAccess.Payload H D
          (Other Raw Listener TcpStream Error) Aff B Poll Instant System Native Profiler))
      Instant System Zone Timestamp))
    (pthread : PthreadSync.Hooks
      (LinuxFutexMachine.State MiriMemoryKind
        (EvalSyncMachine.World Os R EvalSyncObjectAccess.Payload H D
          (Other Raw Listener TcpStream Error) Aff B Poll Instant System Native Profiler))
      TypedSyncRuntime.Ref Duration)
    (fd : UnixFd.Hooks
      (LinuxFutexMachine.State MiriMemoryKind
        (EvalSyncMachine.World Os R EvalSyncObjectAccess.Payload H D
          (Other Raw Listener TcpStream Error) Aff B Poll Instant System Native Profiler))
      H D (Other Raw Listener TcpStream Error) Error Meta)
    (choice : C)
    (communicate : Bool)
    (hostGetrandom : Nat → EStateM StepError
      (LinuxFutexMachine.State MiriMemoryKind
        (EvalSyncMachine.World Os R EvalSyncObjectAccess.Payload H D
          (Other Raw Listener TcpStream Error) Aff B Poll Instant System Native Profiler))
      (Except String ByteArray))
    (tape : ExecutionChoices.Access
      (LinuxFutexMachine.State MiriMemoryKind
        (EvalSyncMachine.World Os R EvalSyncObjectAccess.Payload H D
          (Other Raw Listener TcpStream Error) Aff B Poll Instant System Native Profiler)))
    (currentExe : EStateM StepError
      (LinuxFutexMachine.State MiriMemoryKind
        (EvalSyncMachine.World Os R EvalSyncObjectAccess.Payload H D
          (Other Raw Listener TcpStream Error) Aff B Poll Instant System Native Profiler))
      (Option Os))
    (hostUsizeBits semaphoreBudget : Nat)
    (stackAddress stackSize : UInt64) :
    Except StepError (UnixForeign.OptionalHandler
      (LinuxFutexMachine.State MiriMemoryKind
        (EvalSyncMachine.World Os R EvalSyncObjectAccess.Payload H D
          (Other Raw Listener TcpStream Error) Aff B Poll Instant System Native Profiler))) := do
  let sync ← syncFromSource p memory objects futex choice time hostUsizeBits semaphoreBudget
  let u32Layout : LocalLayout ← match p.primitiveLayout "u32" with
    | .ok value => pure ⟨value.ty, value.layout⟩
    | .error reason => throw (.unsupported s!"compiler u32 layout for macOS foreign items: {reason}")
  let primitive : ShimSignatures.PrimitiveHooks Provenance
      (LinuxFutexMachine.State MiriMemoryKind
        (EvalSyncMachine.World Os R EvalSyncObjectAccess.Payload H D
          (Other Raw Listener TcpStream Error) Aff B Poll Instant System Native Profiler)) := {
    family := core.family
    os := core.os
    checkAbi := ForeignItems.Core.checkAbi core
    checkSymbolClash := core.checkSymbolClash
    transmute := core.transmute }
  let base : MacOsForeign.Hooks
      (LinuxFutexMachine.State MiriMemoryKind
        (EvalSyncMachine.World Os R EvalSyncObjectAccess.Payload H D
          (Other Raw Listener TcpStream Error) Aff B Poll Instant System Native Profiler))
      TypedSyncRuntime.Ref Duration Os Error EnvVars.Kind := {
    signatures := primitive
    writePointer := fun pointer destination =>
      core.writePointer pointer ⟨.memory destination.mplace, destination.layout⟩
    signature := CompilerNamedShimAbi.query p.namedAbi
    sync, pthread, environment
    random := RandomMemory.machine futex.access tape communicate hostUsizeBits hostGetrandom
    closeFd := UnixFd.close fd
    argc := ExecutionStateTransport.reverseAction do
      return (main.entry (← get).machine.user.user).argc
    argv := ExecutionStateTransport.reverseAction do
      return (main.entry (← get).machine.user.user).argv
    currentExe
    derefU32 := fun operand => do
      let pointer ← environment.readPointer operand
      PointerPlaceMachine.fromPointer futex.access pointer u32Layout false
    readPlaceU32 := fun place => do
      let immediate ← PlaceMachine.readImmediate futex.access
        ⟨.indirect place.mplace, place.layout⟩
      let scalar ← lift (immediate.imm.toScalar.mapError ScalarOps.immediateError)
      lift (scalar.toUInt32 |>.mapError ScalarOps.scalarError)
    writeInt := fun value destination => do
      let scalar ← lift (Scalar.fromInt value destination.layout.layout.size
        |>.mapError ScalarOps.scalarError)
      writePlaceImmediate (PlaceMachine.placeHooks futex.access futex.allocation futex.compiler)
        choice (.scalar scalar) ⟨.memory destination.mplace, destination.layout⟩
    getPtrFnInstance := fun pointer => ExecutionStateTransport.reverseAction do
      match ← FunctionPointers.getPtrFn main.functions pointer with
      | .Instance fnInstance => pure fnInstance
      | .Other _ => throw (.unsupported "macOS TLV destructor is not a compiler instance")
    addThreadAtexit := fun fnInstance data => ExecutionStateTransport.reverseAction do
      let active := (← get).machine.threads.activeThread
      let span ← AllocationDriver.currentUserRelevantSpan main.termination.tls.thread.spans
      let tls := main.termination.tls
      modify fun state =>
        let store := tls.data state.machine.user.user
        let values := store.values.addThreadAtexit active ⟨fnInstance, data, span⟩
        let payload := tls.putData state.machine.user.user {store with values}
        {state with machine := {state.machine with user := {state.machine.user with user := payload}}}
    stackAddress, stackSize }
  pure fun name abi args destination => MacOsForeign.emulate base name abi args destination

end Miri.Input.EvalUnixMacOsConstruction
