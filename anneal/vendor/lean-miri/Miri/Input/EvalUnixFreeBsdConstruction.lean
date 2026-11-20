import Miri.Input.CompilerProviders
import Miri.Input.CompilerLibcConstants
import Miri.Input.CompilerLibcTypeLayouts
import Miri.Input.CompilerPrimitiveFacts
import Miri.Input.EvalCallbackFutexConstruction
import Miri.Interpreter.FreeBsdForeign
import Miri.Interpreter.FreeBsdSyncMachine
import Miri.Interpreter.ForeignSyncMachine
import Miri.Interpreter.TypedSyncObjectMachine
import Miri.Interpreter.IntrinsicAtomic
import Miri.Interpreter.PointerPlaceMachine
import Miri.Interpreter.IoError

/-! Canonical source constructor for the FreeBSD `_umtx_op` platform arm.
It consumes the already assembled Linux-futex physical projection and the
same ForeignSyncMachine arena used by pthread and other synchronization. This
does not add an object store, callback token supply, clock, or atomic backend.
-/
namespace Miri.Input.EvalUnixFreeBsdConstruction
open Miri.ABI Miri.Memory Miri.MIR Miri.Interpreter Miri.Concurrency

private def lift {S : Type} (result : Except StepError A) : EStateM StepError S A :=
  match result with
  | .ok value => pure value
  | .error error => throw error

private def query (result : Except String A) : EStateM StepError S A :=
  match result with
  | .ok value => pure value
  | .error reason => throw (.unsupported reason)

private def handlerArg (args : Array (OpTy Provenance)) (index : Nat) :
    EStateM StepError S (OpTy Provenance) :=
  match args[index]? with
  | some value => pure value
  | none => throw (.invalidProgram "checked FreeBSD operand missing")

private def readScalar [DecidableEq K]
    (futex : LinuxFutexMachine.Hooks K U C P O B Instant System Zone Timestamp ErrorHost)
    (operand : OpTy Provenance) :
    EStateM StepError (LinuxFutexMachine.State K U) (Scalar Provenance) := do
  let value ← PlaceMachine.readImmediate futex.access operand
  lift (value.imm.toScalar.mapError ScalarOps.immediateError)

private def readPointer [DecidableEq K]
    (futex : LinuxFutexMachine.Hooks K U C P O B Instant System Zone Timestamp ErrorHost)
    (operand : OpTy Provenance) :
    EStateM StepError (LinuxFutexMachine.State K U) (Pointer (Option Provenance)) := do
  let scalar ← readScalar futex operand
  lift (scalar.toPointer futex.access.runtime.base |>.mapError ScalarOps.scalarError)

private def readUsize [DecidableEq K]
    (futex : LinuxFutexMachine.Hooks K U C P O B Instant System Zone Timestamp ErrorHost)
    (operand : OpTy Provenance) :
    EStateM StepError (LinuxFutexMachine.State K U) UInt64 := do
  let scalar ← readScalar futex operand
  let value ← lift (scalar.toUInt futex.access.runtime.pointerSize |>.mapError ScalarOps.scalarError)
  return UInt64.ofNat value.toNat

private def layout (p : CompilerProviders.Prepared) (name : String) :
    EStateM StepError S LocalLayout := do
  let value ← query (CompilerLibcTypeLayouts.layout p.runtime name)
  pure ⟨value.ty,value.layout⟩

private def project [DecidableEq K]
    (projection : PlaceProjectionHooks Provenance (LinuxFutexMachine.State K U) C MachineHooks.FrameExtra)
    (choice : C) (place : MPlaceTy Provenance) (index : Nat) :
    EStateM StepError (LinuxFutexMachine.State K U) (MPlaceTy Provenance) := do
  let projected ← PlaceDynamic.field projection choice ⟨.memory place.mplace,place.layout⟩ index
  match projected.ref with
  | .memory memory => pure ⟨memory,projected.layout⟩
  | .local .. => throw (.invalidProgram "FreeBSD `_umtx_time` field projected to a local")

private def readPlaceScalar [DecidableEq K]
    (futex : LinuxFutexMachine.Hooks K U C P O B Instant System Zone Timestamp ErrorHost)
    (place : MPlaceTy Provenance) :
    EStateM StepError (LinuxFutexMachine.State K U) (Scalar Provenance) := do
  let value ← PlaceMachine.readImmediate futex.access ⟨.indirect place.mplace,place.layout⟩
  lift (value.imm.toScalar.mapError ScalarOps.immediateError)

private def atomicLoad [DecidableEq K]
    (futex : LinuxFutexMachine.Hooks K U C P O B Instant System Zone Timestamp ErrorHost)
    (choice : C) (place : MPlaceTy Provenance) :
    EStateM StepError (LinuxFutexMachine.State K U) (Scalar Provenance) := do
  let target : RuntimePlace Provenance := ⟨.memory place.mplace,place.layout⟩
  match ← lift (futex.backend (← get)) with
  | .none | .vclocks _ => IntrinsicAtomic.load futex.atomic choice target .Acquire
private def atomicFence [DecidableEq K]
    (futex : LinuxFutexMachine.Hooks K U C P O B Instant System Zone Timestamp ErrorHost) :
    EStateM StepError (LinuxFutexMachine.State K U) Unit := do
  match ← lift (futex.backend (← get)) with
  | .none | .vclocks _ => IntrinsicAtomic.fence futex.atomic .SeqCst false
/-- Construct the real FreeBSD synchronization dictionary on top of the exact
same callback-aware atomic, deadline, error, memory, and typed-sync sources as
the Linux futex constructor. `time` is the actual source time dictionary; a
caller with no time capability must leave this platform arm unavailable and
report Unsupported when `_umtx_op` is selected. -/
def syncFromSource [DecidableEq MiriMemoryKind]
    (p : CompilerProviders.Prepared)
    (objects : ForeignSyncMachine.Objects
      (LinuxFutexMachine.State MiriMemoryKind U))
    (choice : C)
    (projection : PlaceProjectionHooks Provenance
      (LinuxFutexMachine.State MiriMemoryKind U) C MachineHooks.FrameExtra)
    (communicate : Bool)
    (futex : LinuxFutexMachine.Hooks MiriMemoryKind U C P O B Instant System Zone Timestamp ErrorHost)
    :
    FreeBsdSync.Hooks (LinuxFutexMachine.State MiriMemoryKind U) TypedSyncRuntime.Ref := Id.run do
  let placePointer := fun (pointer : Pointer (Option Provenance)) (layout : LocalLayout) =>
    PointerPlaceMachine.fromPointer futex.access pointer layout false
  let base : FreeBsdSync.Hooks
      (LinuxFutexMachine.State MiriMemoryKind U) TypedSyncRuntime.Ref := {
    readPointer := readPointer futex
    readI32 := fun operand => do
      let scalar ← readScalar futex operand
      let value ← lift (scalar.toInt (Size.ofBytes 4) |>.mapError ScalarOps.scalarError)
      pure (Int32.ofInt value)
    readUsize := readUsize futex
    libcI32 := fun name => do
      let value ← query (CompilerLibcConstants.i32 p.namedConstants name)
      pure value
    libcU32 := fun name => do
      let value : Scalar Provenance ← query (CompilerLibcConstants.scalar p.namedConstants name)
      lift (value.toUInt32 |>.mapError ScalarOps.scalarError)
    layout := layout p
    place := placePointer
    project := project projection choice
    readPlaceU32 := fun place => do
      let scalar ← readPlaceScalar futex place
      let value ← lift (scalar.toUInt32 |>.mapError ScalarOps.scalarError)
      pure value
    readPlaceScalar := readPlaceScalar futex
    readTimespec := futex.readTimespec
    parseClockId := fun id => do
      let realtime ← query (CompilerLibcConstants.scalar p.namedConstants "CLOCK_REALTIME")
      if id == realtime then return some .realTime
      let monotonic ← query (CompilerLibcConstants.scalar p.namedConstants "CLOCK_MONOTONIC")
      if id == monotonic then return some .monotonic
      let realtimeCoarse ← query (CompilerLibcConstants.scalar p.namedConstants "CLOCK_REALTIME_COARSE")
      if id == realtimeCoarse then return some .realTime
      let monotonicCoarse ← query (CompilerLibcConstants.scalar p.namedConstants "CLOCK_MONOTONIC_COARSE")
      if id == monotonicCoarse then return some .monotonic
      return none
    noIsolation := fun name => do
      unless communicate do throw (.termination (.unsupportedInIsolation name))
    isNull := fun pointer => do
      let scalar ← lift (Scalar.fromMaybePointer futex.access.runtime.base pointer |>.mapError ScalarOps.scalarError)
      ValidityMachine.scalarMayBeNull scalar
    seqCstFence := atomicFence futex
    readAcquireBits := fun place => do
      let scalar ← atomicLoad futex choice place
      lift (scalar.toBits place.layout.layout.size |>.mapError ScalarOps.scalarError)
    metadata := TypedSyncObjectMachine.narrow objects.metadata TypedSyncObjectMachine.freeBsdFutex
    newFutex := objects.newFutex
    runtime := objects.runtime
    timeout := DeadlineMachine.timeout futex.deadline
    errnoNegOne := fun name destination =>
      IoError.setErrnoAndReturnNeg1 futex.errors (.libc name) destination
    writeInt := fun value destination => do
      let scalar ← lift (Scalar.fromInt value destination.layout.layout.size |>.mapError ScalarOps.scalarError)
      writePlaceImmediate (ValidityMachine.placeHooks futex.access futex.allocation futex.compiler)
        choice (.scalar scalar) ⟨.memory destination.mplace,destination.layout⟩
    hostUsizeBits := futex.access.runtime.pointerSize.bytes.toNat * 8 }
  return FreeBsdSyncMachine.bindReads futex.access base

/-- Install the FreeBSD platform arm over the exact source `ForeignItems.Core`
already selected by callback dispatch. The core is a source assembly result,
not a caller-built platform hook record. With no actual time capability the
untimed `__error` shim remains available and `_umtx_op` fails on demand. -/
def handlerFromSource
    (core : ForeignItems.Core Provenance S D (MPlaceTy Provenance)
      (Pointer (Option Provenance)) B I)
    (errors : IoError.Hooks S ErrorHost)
    (sync : FreeBsdSync.Hooks S TypedSyncRuntime.Ref) :
    String → FnAbi TyId → Array (OpTy Provenance) → MPlaceTy Provenance →
      EStateM StepError S (Option ForeignItems.EmulateItemResult) :=
  fun name abi args dest => do
    if core.os != "freebsd" || !(#["__error","_umtx_op"].contains name) then return none
    core.checkSymbolClash name
    if abi.conv != .C then throw (.undefinedBehavior "FreeBSD legacy calling convention mismatch")
    if abi.cVariadic then throw (.undefinedBehavior "FreeBSD legacy variadic signature")
    if args.size != (if name == "__error" then 0 else 5) then
      throw (.undefinedBehavior "FreeBSD legacy argument count mismatch")
    if name == "__error" then
      let place ← IoError.lastErrorPlace errors
      core.writePointer place.mplace.ptr dest
    else
      FreeBsdSync.operation sync (← handlerArg args 0) (← handlerArg args 1)
        (← handlerArg args 2) (← handlerArg args 3) (← handlerArg args 4) dest
    return some .NeedsReturn

end Miri.Input.EvalUnixFreeBsdConstruction
