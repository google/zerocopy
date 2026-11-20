import Miri.Input.CompilerProviders
import Miri.Input.CompilerLibcTypeLayouts
import Miri.Input.CompilerNamedFields
import Miri.Input.CompilerPrimitiveFacts
import Miri.Input.CompilerLibcConstants
import Miri.Input.CompilerShimAbi
import Miri.Input.CompilerCallConstruction
import Miri.Input.EvalForeignSyncMachine
import Miri.Interpreter.PthreadDispatch
import Miri.Interpreter.TimeShimMachine
import Miri.Interpreter.PointerPlaceMachine
import Miri.Interpreter.RawMemoryMachine

/-! Canonical pthread synchronization source hooks. The caller supplies the
actual shared typed-sync object bundle and narrow machine/source leaves; this
constructor derives pthread objects, memory checks, libc constants, timespec
reads, deadlines, errno handling, shim signatures, and checked transmutation.
It does not accept a completed PthreadSync or PthreadDispatch dictionary. -/
namespace Miri.Input.EvalUnixPthreadConstruction
open Miri.ABI Miri.Memory Miri.MIR Miri.Interpreter Miri.Concurrency
variable {K U C ErrorHost Instant System : Type} [DecidableEq K]

set_option autoImplicit false in structure Leaves
    (K U C ErrorHost Instant System : Type) where
  objects : ForeignSyncMachine.Objects (ValidityMachine.State K U)
  access : ValidityMachine.Access K U
  projection : PlaceProjectionHooks Provenance (ValidityMachine.State K U) C MachineHooks.FrameExtra
  place : PlaceHooks Provenance (ValidityMachine.State K U) C MachineHooks.FrameExtra
  choice : C
  deadline : DeadlineMachine.Hooks K (ValidityMachine.UserState U) Instant System
  ioError : IoError.Hooks (ValidityMachine.State K U) ErrorHost
  noIsolation : String → EStateM StepError (ValidityMachine.State K U) Unit
  checkSymbolClash : String → EStateM StepError (ValidityMachine.State K U) Unit

private def lift {S : Type} (result : Except StepError A) : EStateM StepError S A :=
  match result with | .ok value => pure value | .error error => throw error

private def constant (p : CompilerProviders.Prepared) (name : String) :
    EStateM StepError (ValidityMachine.State K U) Int32 := do
  match CompilerLibcConstants.i32 p.namedConstants name with
  | .ok value => pure value
  | .error reason => throw (.unsupported s!"compiler libc constant `{name}`: {reason}")

private def signatureType : PthreadDispatch.ArgType → ForeignItems.SignatureType
  | .pointer => .pointer
  | .i32 => .i32
  | .u32 => .u32

private def shimSignature (arguments : Array PthreadDispatch.ArgType) : ForeignItems.Signature :=
  ⟨.C, arguments.map signatureType, .i32⟩

private def readI32 (access : ValidityMachine.Access K U) (op : OpTy Provenance) :
    EStateM StepError (ValidityMachine.State K U) Int32 := do
  let immediate ← PlaceMachine.readImmediate access op
  let scalar ← lift (immediate.imm.toScalar.mapError ScalarOps.immediateError)
  lift (scalar.toInt32.mapError ScalarOps.scalarError)

private def readU32 (access : ValidityMachine.Access K U) (op : OpTy Provenance) :
    EStateM StepError (ValidityMachine.State K U) UInt32 := do
  let immediate ← PlaceMachine.readImmediate access op
  let scalar ← lift (immediate.imm.toScalar.mapError ScalarOps.immediateError)
  lift (scalar.toUInt32.mapError ScalarOps.scalarError)

private def operandPointer (access : ValidityMachine.Access K U) (op : OpTy Provenance) :
    EStateM StepError (ValidityMachine.State K U)
      (Pointer (Option Provenance) × MemPlaceMeta Provenance) := do
  let immediate ← PlaceMachine.readImmediate access op
  let (scalar,metadata) ← lift (immediate.imm.toScalarAndMeta.mapError ScalarOps.immediateError)
  let pointer ← lift (scalar.toPointer access.runtime.base |>.mapError ScalarOps.scalarError)
  pure (pointer,metadata)

private def attributeLayout (p : CompilerProviders.Prepared) (kind : PthreadSync.Attribute) :
    EStateM StepError (ValidityMachine.State K U) LocalLayout := do
  let name := match kind with
    | .mutex => "pthread_mutexattr_t"
    | .condvar => "pthread_condattr_t"
  match CompilerLibcTypeLayouts.layout p.runtime name with
  | .ok value => pure ⟨value.ty,value.layout⟩
  | .error reason => throw (.unsupported s!"compiler libc {name} layout: {reason}")

private def attributePlace (p : CompilerProviders.Prepared)
    (access : ValidityMachine.Access K U) (op : OpTy Provenance)
    (kind : PthreadSync.Attribute) :
    EStateM StepError (ValidityMachine.State K U) (MPlaceTy Provenance) := do
  let (pointer,metadata) ← operandPointer access op
  PointerPlaceMachine.withMetadata access pointer metadata (← attributeLayout p kind) false

private def attributeRead (p : CompilerProviders.Prepared)
    (access : ValidityMachine.Access K U)
    (projection : PlaceProjectionHooks Provenance (ValidityMachine.State K U) C MachineHooks.FrameExtra)
    (choice : C) (op : OpTy Provenance)
    (kind : PthreadSync.Attribute) (offset : Size) :
    EStateM StepError (ValidityMachine.State K U) Int32 := do
  unless offset == Size.ZERO do
    throw (.invalidProgram "pthread attribute source offset is not zero")
  let attrPlace ← attributePlace p access op kind
  let i32 ← match p.primitiveLayout "i32" with
    | .ok value => pure ⟨value.ty,value.layout⟩
    | .error reason => throw (.unsupported s!"compiler i32 layout for pthread attribute: {reason}")
  let field ← PlaceDynamic.field projection choice ⟨.memory attrPlace.mplace,attrPlace.layout⟩ 0
  match field.ref with
  | .memory memory => readI32 access ⟨.indirect memory,i32⟩
  | .local .. => throw (.invalidProgram "pthread attribute field projection became a local")

private def attributeWrite (p : CompilerProviders.Prepared)
    (access : ValidityMachine.Access K U) (place : PlaceHooks Provenance
      (ValidityMachine.State K U) C MachineHooks.FrameExtra)
    (projection : PlaceProjectionHooks Provenance (ValidityMachine.State K U) C MachineHooks.FrameExtra)
    (choice : C)
    (op : OpTy Provenance) (kind : PthreadSync.Attribute) (offset : Size) (value : Int32) :
    EStateM StepError (ValidityMachine.State K U) Unit := do
  unless offset == Size.ZERO do
    throw (.invalidProgram "pthread attribute source offset is not zero")
  let attrPlace ← attributePlace p access op kind
  let i32 ← match p.primitiveLayout "i32" with
    | .ok value => pure ⟨value.ty,value.layout⟩
    | .error reason => throw (.unsupported s!"compiler i32 layout for pthread attribute: {reason}")
  let scalar ← lift (Scalar.fromInt value.toInt i32.layout.size |>.mapError ScalarOps.scalarError)
  let field ← PlaceDynamic.field projection choice ⟨.memory attrPlace.mplace,attrPlace.layout⟩ 0
  match field.ref with
  | .memory memory => writePlaceImmediate place choice (.scalar scalar) ⟨.memory memory,i32⟩
  | .local .. => throw (.invalidProgram "pthread attribute field projection became a local")

private def attributeUninit (p : CompilerProviders.Prepared)
    (access : ValidityMachine.Access K U) (op : OpTy Provenance)
    (kind : PthreadSync.Attribute) : EStateM StepError (ValidityMachine.State K U) Unit := do
  let attrPlace ← attributePlace p access op kind
  PlaceMachine.writeMemory access (fun _ => false) .uninit attrPlace

private def parseClock (p : CompilerProviders.Prepared) (value : Int32) :
    EStateM StepError (ValidityMachine.State K U) (Option PthreadObjects.Clock) := do
  if value == (← constant p "CLOCK_REALTIME") then return some .realTime
  if value == (← constant p "CLOCK_MONOTONIC") then return some .monotonic
  return none

private def readTimespec (p : CompilerProviders.Prepared)
    (access : ValidityMachine.Access K U)
    (projection : PlaceProjectionHooks Provenance (ValidityMachine.State K U) C MachineHooks.FrameExtra)
    (choice : C) (op : OpTy Provenance) :
    EStateM StepError (ValidityMachine.State K U) (Option Clock.Duration) := do
  let layout ← match CompilerLibcTypeLayouts.layout p.runtime "timespec" with
    | .ok value => pure ⟨value.ty,value.layout⟩
    | .error reason => throw (.unsupported s!"compiler libc timespec layout: {reason}")
  let (pointer,metadata) ← operandPointer access op
  let parent ← PointerPlaceMachine.withMetadata access pointer metadata layout false
  let field := fun name => do
    let index ← match CompilerNamedFields.fieldIndex p.runtime parent.layout name with
      | .ok value => pure value
      | .error reason => throw reason
    let projected ← PlaceDynamic.field projection choice ⟨.memory parent.mplace,parent.layout⟩ index
    match projected.ref with
    | .memory memory => pure ⟨memory,projected.layout⟩
    | .local .. => throw (.invalidProgram "timespec field projection became local")
  let readSigned := fun (fieldPlace : MPlaceTy Provenance) => do
    let immediate ← PlaceMachine.readImmediate access ⟨.indirect fieldPlace.mplace,fieldPlace.layout⟩
    let scalar ← lift (immediate.imm.toScalar.mapError ScalarOps.immediateError)
    lift (scalar.toInt fieldPlace.layout.layout.size |>.mapError ScalarOps.scalarError)
  let seconds ← readSigned (← field "tv_sec")
  let nanos ← readSigned (← field "tv_nsec")
  if seconds < 0 then throw (.unsupported "pthread timespec with negative tv_sec is unsupported")
  if seconds >= 2^64 then throw (.invalidProgram "pthread timespec tv_sec does not fit u64")
  if nanos < 0 || nanos >= 1000000000 then return none
  match Clock.Duration.fromNanos (seconds.toNat * 1000000000 + nanos.toNat) with
  | .ok duration => return some duration
  | .error error => throw error

/-- Assemble the portable pthread sync ABI over the actual shared object arena.
Attribute/object writes use canonical guest memory, timed waits use the source
HostRuntime deadline registry, and each ABI signature comes from the exact
compiler shim table. -/
def fromSource [DecidableEq MiriMemoryKind]
    (p : CompilerProviders.Prepared) (compatibilityBudget : Nat)
    (leaves : Leaves MiriMemoryKind U C ErrorHost Instant System) :
    EStateM StepError (ValidityMachine.State MiriMemoryKind U)
      (PthreadDispatch.Hooks (ValidityMachine.State MiriMemoryKind U)
        TypedSyncRuntime.Ref Clock.Duration) := do
  let access := leaves.access
  let projection := leaves.projection
  let place := leaves.place
  let choice := leaves.choice
  let objects := leaves.objects
  let clock := leaves.deadline
  let errors := leaves.ioError
  let base : PthreadSync.Hooks (ValidityMachine.State MiriMemoryKind U)
      TypedSyncRuntime.Ref Clock.Duration := {
    objects := objects.pthread
    constant := fun kind => constant p (match kind with
      | .mutexNormal => "PTHREAD_MUTEX_NORMAL"
      | .mutexDefault => "PTHREAD_MUTEX_DEFAULT"
      | .mutexErrorCheck => "PTHREAD_MUTEX_ERRORCHECK"
      | .mutexRecursive => "PTHREAD_MUTEX_RECURSIVE"
      | .einval => "EINVAL"
      | .ebusy => "EBUSY"
      | .edeadlk => "EDEADLK"
      | .eperm => "EPERM"
      | .etimedout => "ETIMEDOUT"
      | .clockRealtime => "CLOCK_REALTIME")
    readPointer := fun op => do
      let (pointer,_) ← operandPointer access op
      pure pointer
    isNull := fun pointer => pure (pointer.provenance.isNone && pointer.offset.bytes == 0)
    attributeRead := attributeRead p access projection choice
    attributeWrite := attributeWrite p access place projection choice
    attributeUninit := attributeUninit p access
    objectUninit := fun op kind => do
      let object ← objects.pthread.deref op kind
      PlaceMachine.writeMemory access (fun _ => false) .uninit object
    parseClock := parseClock p
    readTimespec := readTimespec p access projection choice
    timeout := fun kind relative duration => do
      let kind := match kind with | .realTime => Clock.TimeoutClock.realTime | .monotonic => .monotonic
      let style := if relative then Clock.TimeoutStyle.relative else .absolute
      DeadlineMachine.timeout clock kind style duration
    noIsolation := leaves.noIsolation
    setErrnoAndReturnNeg1 := fun kind destination => do
      let name := match kind with
        | .einval => "EINVAL" | .etimedout => "ETIMEDOUT" | _ => "EINVAL"
      IoError.setErrnoAndReturnNeg1 errors (.libc name) destination
    writeClockId := fun destination value => do
      let layout ← match p.primitiveLayout "i32" with
        | .ok result => pure ⟨result.ty,result.layout⟩
        | .error reason => throw (.unsupported s!"compiler i32 layout for pthread clock id: {reason}")
      let scalar ← lift (Scalar.fromInt value.toInt layout.layout.size |>.mapError ScalarOps.scalarError)
      let (pointer,metadata) ← operandPointer access destination
      let target ← PointerPlaceMachine.withMetadata access pointer metadata layout false
      writePlaceImmediate place choice (.scalar scalar) ⟨.memory target.mplace,layout⟩ }
  let pthread := TimeShimMachine.bindPthread clock base
  let compat := CompilerCallConstruction.compiler p compatibilityBudget
  let dispatch : PthreadDispatch.Hooks (ValidityMachine.State MiriMemoryKind U)
      TypedSyncRuntime.Ref Clock.Duration := {
    pthread
    expectedAbi := fun arguments => do
      let signature := shimSignature arguments
      match CompilerShimAbi.expectedAbi p.lifecycle.shim signature with
      | .ok abi => pure abi
      | .error reason => throw (.unsupported s!"compiler pthread shim ABI: {reason}")
    argumentCompat := fun caller callee => compat.checkArgumentCompat choice caller callee
    checkSymbolClash := leaves.checkSymbolClash
    transmute := fun operand target => do
      let projection ← place.projection choice
      match operand.transmute projection target |>.mapError IntrinsicVectorMachine.projectionError with
      | .ok value => pure value
      | .error error => throw error
    readI32 := readI32 access
    readU32 := readU32 access }
  pure dispatch

end Miri.Input.EvalUnixPthreadConstruction
