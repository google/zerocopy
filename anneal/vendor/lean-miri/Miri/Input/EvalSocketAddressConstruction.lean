import Miri.Input.CompilerProviders
import Miri.Input.CompilerLibcTypeLayouts
import Miri.Input.CompilerPrimitiveFacts
import Miri.Input.CompilerNamedFields
import Miri.Input.CompilerNamedConstants
import Miri.Input.EvalHostRuntimeConstruction
import Miri.Input.EvalCoreMachine
import Miri.Input.EvalSocketStorage
import Miri.Input.EvalSyncObjectAccess
import Miri.Input.HostRuntime
import Miri.Interpreter.SocketAddress
import Miri.Interpreter.RawMemoryMachine
import Miri.Interpreter.GlobalMemoryCopyMachine
import Miri.Interpreter.PointerPlaceMachine

/-! Source construction for Unix socket address memory operations. Compiler
layouts/constants, pointer access, allocation, projection, byte IO, and
provenance-aware copies come from one canonical EnvironmentMemory bundle. The
only residual effects are host address resolution and its iterator lifecycle.
-/
namespace Miri.Input.EvalSocketAddressConstruction
open Miri.ABI Miri.Memory Miri.MIR Miri.Interpreter

abbrev RuntimeState (U : Type) := EvalHostRuntimeConstruction.RuntimeState U
abbrev RuntimeM (U A : Type) := EvalHostRuntimeConstruction.RuntimeM U A

structure HostEffects (S E Iterator : Type) where
  resolve : String → UInt16 → EStateM StepError S (Except (IoError.HostError E) Iterator)
  nextAddress : Iterator → EStateM StepError S (Option (SocketAddress.Address × Iterator))
  dropIterator : Iterator → EStateM StepError S Unit
  resolutionDiagnostic : IoError.HostError E → EStateM StepError S Unit
  listBudget : Nat

private def lift (result : Except StepError A) : RuntimeM U A :=
  match result with
  | .ok value => pure value
  | .error error => throw error

private def readScalar [DecidableEq MiriMemoryKind]
    (access : PlaceMachine.AccessConfig MiriMemoryKind (PointerMachine.User U))
    (place : MPlaceTy Provenance) : RuntimeM U (Scalar Provenance) := do
  let immediate ← PlaceMachine.readImmediate access ⟨.indirect place.mplace,place.layout⟩
  lift (immediate.imm.toScalar.mapError ScalarOps.immediateError)

private def pointerFromScalar (base : TargetDataLayout) (scalar : Scalar Provenance) :
    Except StepError (Pointer (Option Provenance)) :=
  scalar.toPointer base |>.mapError ScalarOps.scalarError

private def scanCString [DecidableEq MiriMemoryKind]
    (access : PlaceMachine.AccessConfig MiriMemoryKind (PointerMachine.User U))
    (arithmetic : PointerArithmetic) (budget : Nat)
    (base : Pointer (Option Provenance)) : RuntimeM U ByteArray := do
  let rec scan (fuel length : Nat) : RuntimeM U UInt64 := do
    match fuel with
    | 0 => throw (.resourceExhaustion "C string scan budget")
    | fuel + 1 =>
      if length >= 2^64 then throw (.invalidProgram "C string length overflow")
      let location ← lift (RawMemoryMachine.offset arithmetic base (UInt64.ofNat length))
      if (← RawMemoryMachine.readByte access arithmetic location) == 0 then
        return UInt64.ofNat length
      scan fuel (length + 1)
  let length ← scan budget 0
  let bytes ← RawMemoryMachine.readBytes access arithmetic base length
  unless bytes.size == length.toNat do
    throw (.invalidProgram "C string byte-read length mismatch")
  return bytes

private def targetMemoryKind : SocketAddress.Kind → MemoryKind MiriMemoryKind
  | .stack => .stack
  | .socketAddress => .machine .socketAddress
  | .machine => .machine .machine

/-- Build all guest-side address operations from the selected execution's
canonical memory. `errors` is the already-built errno machine belonging to the
same callback state; resolver effects are the only host-specific inputs. -/
def fromSource [DecidableEq MiriMemoryKind]
    (p : CompilerProviders.Prepared)
    (memory : EvalHostRuntimeConstruction.EnvironmentMemory
      (ValidityMachine.Control Stored) C Payload)
    (errors : IoError.Hooks (RuntimeState (ValidityMachine.Control Stored)) E)
    (host : HostEffects (RuntimeState (ValidityMachine.Control Stored)) E Iterator) :
    Except StepError (SocketAddress.Hooks (RuntimeState (ValidityMachine.Control Stored)) E Iterator) := do
  let target ← p.externStatics.targetFacts |>.mapError StepError.unsupported
  unless target.families.contains "unix" do
    throw (.invalidProgram s!"socket address hooks requested for non-Unix target `{target.os}`")
  let access := memory.access
  let arithmetic := memory.pointers.arithmetic
  let placeProjection := memory.projection
  let errors := {errors with family := ForeignItems.Family.unix, os := target.os}
  let layout := fun name => do
    let result ← match CompilerLibcTypeLayouts.layout p.runtime name with
      | .ok value => pure value
      | .error reason => throw (.unsupported s!"compiler libc layout `{name}`: {reason}")
    pure ⟨result.ty,result.layout⟩
  let u128Layout := do
    match p.primitiveLayout "u128" with
    | .ok value => pure ⟨value.ty,value.layout⟩
    | .error reason => throw (.unsupported s!"compiler u128 layout: {reason}")
  let readPointer := fun operand => do
    let immediate ← PlaceMachine.readImmediate access operand
    let scalar ← lift (immediate.imm.toScalar.mapError ScalarOps.immediateError)
    lift (pointerFromScalar access.runtime.base scalar)
  let ptrToPlace : Pointer (Option Provenance) → LocalLayout → MPlaceTy Provenance :=
    fun pointer layout => ⟨⟨pointer,.none,none⟩,layout⟩
  let readBytes := fun (pointer : Pointer (Option Provenance)) (size : Size) =>
    RawMemoryMachine.readBytes access arithmetic pointer size.bytes
  let writeBytes := fun pointer bytes => RawMemoryMachine.writeBytes access arithmetic pointer bytes
  let readCString := scanCString access arithmetic memory.stringScanBudget
  let allocate := fun layout kind => do
    unless layout.layout.isSized do throw (.invalidProgram "socket address allocation has unsized layout")
    let pointer ← ReallocationDriver.allocateConfigured memory.allocation
      layout.layout.size layout.layout.align.abi (targetMemoryKind kind) .Uninit
    pure ⟨⟨pointer.withOptionalProvenance,.none,none⟩,layout⟩
  let writeScalar := fun scalar destination =>
    writePlaceImmediate placeProjection.place memory.choice (.scalar scalar)
      ⟨.memory destination.mplace,destination.layout⟩
  let writeInt := fun value destination => do
    let scalar ← lift ((if value < 0 then
        Scalar.fromInt value destination.layout.layout.size
      else if value < 2^128 then
        Scalar.fromUInt (BitVec.ofNat 128 value.toNat) destination.layout.layout.size
      else .error (.scalarInt (.integerConversionOverflow value)))
      |>.mapError ScalarOps.scalarError)
    writeScalar scalar destination
  let field := fun parent name => do
    let index ← match CompilerNamedFields.fieldIndex p.runtime parent.layout name with
      | .ok index => pure index
      | .error error => throw error
    let projected ← PlaceDynamic.field placeProjection memory.choice
      ⟨.memory parent.mplace,parent.layout⟩ index
    match projected.ref with
    | .memory value => pure ⟨value,projected.layout⟩
    | .local .. => throw (.invalidProgram "socket address named field became a local")
  let transmute := fun source layout => do
    let cx ← placeProjection.place.projection memory.choice
    let value ← lift ((⟨.indirect source.mplace,source.layout⟩ : OpTy Provenance).transmute cx
      ⟨layout.ty,layout.layout⟩ |>.mapError IntrinsicVectorMachine.projectionError)
    match value.op with
    | .indirect place => pure ⟨place,value.layout⟩
    | .immediate .. => throw (.invalidProgram "socket address place transmute became immediate")
  let offsetZero := fun source layout => do
    let value ← PlaceDynamic.offsetWithMeta placeProjection memory.choice
      ⟨.memory source.mplace,source.layout⟩ Size.ZERO .wrapping .none layout
    match value.ref with
    | .memory place => pure ⟨place,value.layout⟩
    | .local .. => throw (.invalidProgram "socket address offset-zero became local")
  let libc := fun name =>
    match CompilerNamedConstants.scalar p.namedConstants name with
    | .ok value => pure value
    | .error reason => throw (.unsupported s!"compiler libc constant `{name}`: {reason}")
  let libcI32 := fun name => do
    let scalar ← libc name
    lift (scalar.toInt32.mapError ScalarOps.scalarError)
  let readSocklen := fun operand => do
    let immediate ← PlaceMachine.readImmediate access operand
    let scalar ← lift (immediate.imm.toScalar.mapError ScalarOps.immediateError)
    let socklen ← layout "socklen_t"
    let value ← lift (scalar.toInt socklen.layout.size |>.mapError ScalarOps.scalarError)
    if value < 0 || value > 18446744073709551615 then
      throw (.invalidProgram "socklen does not fit u64")
    pure (UInt64.ofNat value.toNat)
  let hooks : SocketAddress.Hooks (RuntimeState (ValidityMachine.Control Stored)) E Iterator := {
    errors
    gnu := target.env == "gnu"
    readPointer
    isLiteralNull := fun pointer => pointer.provenance.isNone && pointer.offset.bytes == 0
    readCString
    readScalar := readScalar access
    readSigned := fun place size => do
      lift ((← readScalar access place).toInt size |>.mapError ScalarOps.scalarError)
    readU32 := fun place => do
      lift ((← readScalar access place).toUInt32 |>.mapError ScalarOps.scalarError)
    readSocklen
    layout
    u128Layout
    pointerLayout := fun state => .ok memory.pointerLayout state
    derefAs := fun operand layout => do
      let immediate ← PlaceMachine.readImmediate access operand
      let (scalar,metadata) ← lift (immediate.imm.toScalarAndMeta |>.mapError ScalarOps.immediateError)
      let pointer ← lift (pointerFromScalar access.runtime.base scalar)
      let alignment : PointerPlaceMachine.AlignmentContext
          (PointerMachine.User (ValidityMachine.Control Stored)) := {
        policy := fun user => user.payload.alignment
        promises := fun user => user.symbolicAlignment }
      let misaligned ← PointerPlaceMachine.misalignmentWith access alignment pointer layout.layout.align.abi
      pure ⟨⟨pointer,metadata,misaligned⟩,layout⟩
    ptrToPlace
    transmute
    offsetZero
    field
    readBytes
    writeBytes
    writeZeros := fun pointer size =>
      RawMemoryMachine.writeBytes access arithmetic pointer ⟨Array.replicate size.bytes.toNat 0⟩
    pointer := fun place => place.mplace.ptr
    allocate
    deallocate := fun pointer kind =>
      memory.deallocate pointer none (targetMemoryKind kind)
    memCopy := fun source destination size nonoverlapping =>
      GlobalMemoryCopyMachine.copy access arithmetic source destination size 1 nonoverlapping
    writeInt
    writeScalar
    writePointer := fun pointer destination => do
      let scalar ← lift (Scalar.fromMaybePointer access.runtime.base pointer
        |>.mapError ScalarOps.scalarError)
      writeScalar scalar destination
    readPlacePointer := fun place => do
      lift ((← readScalar access place).toPointer access.runtime.base |>.mapError ScalarOps.scalarError)
    libc
    libcI32
    scalarSigned := fun scalar size => lift (scalar.toInt size |>.mapError ScalarOps.scalarError)
    resolve := host.resolve
    nextAddress := host.nextAddress
    dropIterator := host.dropIterator
    resolutionDiagnostic := host.resolutionDiagnostic
    listBudget := host.listBudget }
  pure hooks

/-- Build socket-address hooks for callback IO from the same EvalWorld memory
bundle used by Core.  The explicit `Stored` specialization is important:
`RuntimeState (Control (Stored ...))` reduces to the callback's canonical
inner state, so pointer provenance, allocation effects, and partially updated
error states are already in the required state representation.  No alternate
memory lens or synthetic transport state is introduced. -/
def callbackFromSource [DecidableEq MiriMemoryKind]
    (p : CompilerProviders.Prepared)
    (memory : EvalHostRuntimeConstruction.EnvironmentMemory
      (ValidityMachine.Control
        (EvalCoreMachine.Stored Os R EvalSyncObjectAccess.Payload H D
          (EvalSocketStorage.Other Raw Listener TcpStream Error) Aff B
          (HostRuntime.Storage Poll Instant System H D
            (EvalSocketStorage.Other Raw Listener TcpStream Error) Native Profiler))) C
      EvalSyncObjectAccess.Payload)
    (errors : IoError.Hooks
      (EvalSocketStorage.State Os R EvalSyncObjectAccess.Payload H D Aff B Poll Instant System
        Native Profiler Raw Listener TcpStream Error)
      Error)
    (host : HostEffects
      (EvalSocketStorage.State Os R EvalSyncObjectAccess.Payload H D Aff B Poll Instant System
        Native Profiler Raw Listener TcpStream Error)
      Error AddrIter) :
    Except StepError
      (SocketAddress.Hooks
        (EvalSocketStorage.State Os R EvalSyncObjectAccess.Payload H D Aff B Poll Instant System
          Native Profiler Raw Listener TcpStream Error)
        Error AddrIter) :=
  fromSource p memory errors host

end Miri.Input.EvalSocketAddressConstruction
