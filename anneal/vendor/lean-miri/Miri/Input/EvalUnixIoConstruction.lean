import Miri.Input.CompilerProviders
import Miri.Input.CompilerFrameMetadata
import Miri.Input.EvalCoreMachine
import Miri.Input.EvalSocketStorage
import Miri.Input.EvalUnixFdConstruction
import Miri.Input.EvalUnixConstruction
import Miri.Input.EvalAllocationMachine
import Miri.Input.EvalProjectionMachine
import Miri.Input.CompilerNamedFields
import Miri.Interpreter.RawMemoryMachine
import Miri.Interpreter.UnixFdControlMachine
import Miri.Interpreter.ShimSignatures
import Miri.Interpreter.UnixVectoredMachine

/-! Canonical Unix descriptor/file operation construction. Host file handles
and true host IO stay typed effects; descriptor identity, ownership, guest
buffer reads/writes, and scalar accesses are bound to the current EvalWorld. -/
namespace Miri.Input.EvalUnixIoConstruction
open Miri.ABI Miri.Memory Miri.MIR Miri.Interpreter

abbrev Other Raw Listener TcpStream Error :=
  EvalSocketStorage.Other Raw Listener TcpStream Error
abbrev User Os R P H D Aff B Poll Instant System Native Profiler Raw Listener TcpStream Error :=
  EvalSocketStorage.User Os R P H D Aff B Poll Instant System Native Profiler Raw Listener TcpStream Error
abbrev State Os R P H D Aff B Poll Instant System Native Profiler Raw Listener TcpStream Error :=
  EvalSocketStorage.State Os R P H D Aff B Poll Instant System Native Profiler Raw Listener TcpStream Error
abbrev FD H D O := Files.Ref (Files.Description H D O)
abbrev ExecConfig Os R P H D Aff B Poll Instant System Native Profiler Raw Listener TcpStream Error C ClockHost :=
  ExecutionMachine.Config MiriMemoryKind
    (User Os R P H D Aff B Poll Instant System Native Profiler Raw Listener TcpStream Error)
    C (Other Raw Listener TcpStream Error) ABI.ExternAbi ClockHost

private def lift (value : Except StepError A) : EStateM StepError S A :=
  match value with | .ok value => pure value | .error error => throw error

private def unresolved (name : String) : EStateM StepError S A :=
  throw (.unsupported s!"source vectored field is unavailable: {name}")

/-- Genuine host resource operations only. Guest byte access, descriptor
ownership, and FileDescription policy are supplied by the source constructor.
The `other*` callbacks are the already source-built event/socket operation
family and remain separate from the host file boundary. -/
structure HostFileEffects (S H D O E Meta : Type) where
  hostRead : Files.Description H D O → ByteArray → EStateM StepError S
    (Except (IoError.HostError E) (Nat × ByteArray))
  hostWrite : Files.Description H D O → ByteArray → EStateM StepError S
    (Except (IoError.HostError E) Nat)
  flushStdout : EStateM StepError S Unit
  hostSeek : H → Files.SeekFrom → EStateM StepError S
    (Except (IoError.HostError E) UInt64)
  hostMetadata : Files.Description H D O → EStateM StepError S
    (Except (IoError.HostError E) Meta)
  hostIsTerminal : Files.Description H D O → EStateM StepError S Bool
  permissionDenied : EStateM StepError S (IoError.HostError E)

structure OtherFileEffects (S H D O E : Type) where
  read : FD H D O → Bool → Pointer (Option Provenance) → Nat → Files.Finish S E →
    EStateM StepError S Unit
  write : FD H D O → Bool → Pointer (Option Provenance) → Nat → Files.Finish S E →
    EStateM StepError S Unit
  shortOperations : O → Bool
  readiness : O → EStateM StepError S (Option Files.Readiness)
  hasReadinessWatched : O → Bool
  isTerminal : O → Bool → EStateM StepError S Bool

structure FileLockEffects (S H E : Type) where
  tryLock : H → Bool → EStateM StepError S
    (Except (UnixFileOperations.TryLockError E) Unit)
  unlock : H → EStateM StepError S (Except (IoError.HostError E) Unit)

/-- Resource finalization at the FileMachine last-owner boundary. Host file
and directory handles have separate cleanup effects; source-owned descriptors
retain their own typed cleanup route. The four standard descriptors need no
external resource release. -/
structure FileResourceEffects (S H D O : Type) where
  dropFile : H → EStateM StepError S Unit
  dropDirectory : D → EStateM StepError S Unit
  dropOther : O → EStateM StepError S Unit

/-- Construct FileDescription behavior from the selected compiler target and
canonical physical guest memory. `other` is an operation bundle from the
source-owned EventFd/Socket adapters, not a replaceable Files hook record. -/
def filesFromSourceFor
    (family : ForeignItems.Family)
    (p : CompilerProviders.Prepared)
    (access : ValidityMachine.Access MiriMemoryKind
      (EvalCoreMachine.Stored Os R P H D (Other Raw Listener TcpStream Error) Aff B
        (HostRuntime.Storage Poll Instant System H D
          (Other Raw Listener TcpStream Error) Native Profiler)))
    (pointers : PointerMachine.Hooks MiriMemoryKind
      (ValidityMachine.Control (EvalCoreMachine.Stored Os R P H D
        (Other Raw Listener TcpStream Error) Aff B
        (HostRuntime.Storage Poll Instant System H D
          (Other Raw Listener TcpStream Error) Native Profiler))))
    (host : HostFileEffects
      (State Os R P H D Aff B Poll Instant System Native Profiler Raw Listener TcpStream Error)
      H D (Other Raw Listener TcpStream Error) Error Metadata)
    (other : OtherFileEffects
      (State Os R P H D Aff B Poll Instant System Native Profiler Raw Listener TcpStream Error)
      H D (Other Raw Listener TcpStream Error) Error) :
    Except StepError (Files.Hooks
      (State Os R P H D Aff B Poll Instant System Native Profiler Raw Listener TcpStream Error)
      H D (Other Raw Listener TcpStream Error) Error Metadata) := do
  let target ← p.externStatics.targetFacts |>.mapError fun reason => .unsupported reason
  let targetMatches := match family with
    | .unix => target.families.contains "unix"
    | .windows => target.os == "windows" || target.families.contains "windows"
    | _ => false
  unless targetMatches do
    throw (.invalidProgram s!"{reprStr family} files requested on incompatible target `{target.os}`")
  pure {
    family
    hostRead := host.hostRead
    hostWrite := host.hostWrite
    hostFlushStdout := host.flushStdout
    hostSeek := host.hostSeek
    hostMetadata := host.hostMetadata
    hostIsTerminal := host.hostIsTerminal
    readBytes := fun pointer size =>
      RawMemoryMachine.readBytes access pointers.arithmetic pointer size.bytes
    writeBytes := RawMemoryMachine.writeBytes access pointers.arithmetic
    permissionDenied := host.permissionDenied
    otherRead := other.read
    otherWrite := other.write
    otherShortOperations := other.shortOperations
    otherReadiness := other.readiness
    otherHasReadinessWatched := other.hasReadinessWatched
    otherIsTerminal := other.isTerminal }

/-- Preserve the historical Unix-only constructor and target validation. -/
def filesFromSource
    (p : CompilerProviders.Prepared)
    (access : ValidityMachine.Access MiriMemoryKind
      (EvalCoreMachine.Stored Os R P H D (Other Raw Listener TcpStream Error) Aff B
        (HostRuntime.Storage Poll Instant System H D
          (Other Raw Listener TcpStream Error) Native Profiler)))
    (pointers : PointerMachine.Hooks MiriMemoryKind
      (ValidityMachine.Control (EvalCoreMachine.Stored Os R P H D
        (Other Raw Listener TcpStream Error) Aff B
        (HostRuntime.Storage Poll Instant System H D
          (Other Raw Listener TcpStream Error) Native Profiler))))
    (host : HostFileEffects
      (State Os R P H D Aff B Poll Instant System Native Profiler Raw Listener TcpStream Error)
      H D (Other Raw Listener TcpStream Error) Error Metadata)
    (other : OtherFileEffects
      (State Os R P H D Aff B Poll Instant System Native Profiler Raw Listener TcpStream Error)
      H D (Other Raw Listener TcpStream Error) Error) :=
  filesFromSourceFor .unix p access pointers host other

/-- The descriptor registry is the one in EvalWorld runtime state. This helper
keeps table, Rc ownership, and destructor callbacks on the FileMachine path. -/
def fileRegistry
    (hostUsizeBits referenceBudget : Nat)
    (effects : FileResourceEffects
      (MachineHooks.State MiriMemoryKind
        (User Os R P H D Aff B Poll Instant System Native Profiler Raw Listener TcpStream Error))
      H D (Other Raw Listener TcpStream Error)) :=
  EvalSocketStorage.files (Os := Os) (R := R) (P := P) (H := H) (D := D)
    (Aff := Aff) (B := B) (Poll := Poll) (Instant := Instant) (System := System)
    (Native := Native) (Profiler := Profiler) (Raw := Raw) (Listener := Listener)
    (TcpStream := TcpStream) (Error := Error) hostUsizeBits referenceBudget fun description =>
      match description with
      | .stdin | .stdout | .stderr | .nullOutput => pure ()
      | .file handle _ _ => effects.dropFile handle
      | .directory handle => effects.dropDirectory handle
      | .other payload => effects.dropOther payload

def fileOperationsFromSource
    (p : CompilerProviders.Prepared)
    (errors : IoError.Hooks
      (State Os R P H D Aff B Poll Instant System Native Profiler Raw Listener TcpStream Error) Error)
    (effects : FileLockEffects
      (State Os R P H D Aff B Poll Instant System Native Profiler Raw Listener TcpStream Error)
      H Error) :
    Except StepError (UnixFileOperations.Hooks
      (State Os R P H D Aff B Poll Instant System Native Profiler Raw Listener TcpStream Error)
      H Error) := do
  pure {
    tryLock := effects.tryLock
    unlock := effects.unlock
    fromKind := errors.hostFromKind
    libc := fun name => match CompilerNamedConstants.scalar p.namedConstants name with
      | .ok value => pure value
      | .error reason => throw (.unsupported reason) }

/-- Bind exact guest access and compiler target limits to source UnixFd policy.
Random short-read selection remains a source RNG effect, and non-Unix
positional descriptions remain explicit unsupported operations. -/
def unixFdFromSource
    (p : CompilerProviders.Prepared)
    (communicate shortFdOperations : Bool)
    (hostIsizeBits : Nat)
    (registry : ReadinessMachine.Hooks MiriMemoryKind
      (User Os R P H D Aff B Poll Instant System Native Profiler Raw Listener TcpStream Error)
      H D (Other Raw Listener TcpStream Error))
    (readinessRoute : EvalUnixFdConstruction.ReadinessRoute
      (State Os R P H D Aff B Poll Instant System Native Profiler Raw Listener TcpStream Error))
    (fileHooks : Files.Hooks
      (State Os R P H D Aff B Poll Instant System Native Profiler Raw Listener TcpStream Error)
      H D (Other Raw Listener TcpStream Error) Error Metadata)
    (errors : IoError.Hooks
      (State Os R P H D Aff B Poll Instant System Native Profiler Raw Listener TcpStream Error) Error)
    (access : ValidityMachine.Access MiriMemoryKind
      (EvalCoreMachine.Stored Os R P H D (Other Raw Listener TcpStream Error) Aff B
        (HostRuntime.Storage Poll Instant System H D
          (Other Raw Listener TcpStream Error) Native Profiler)))
    (randomShort : EStateM StepError
      (State Os R P H D Aff B Poll Instant System Native Profiler Raw Listener TcpStream Error) Bool)
    (place : PlaceHooks Provenance
      (State Os R P H D Aff B Poll Instant System Native Profiler Raw Listener TcpStream Error)
      C MachineHooks.FrameExtra)
    (choice : C)
    (otherPositionalRead otherPositionalWrite : FD H D (Other Raw Listener TcpStream Error) →
      UInt64 → Pointer (Option Provenance) → Nat → Files.Finish
        (State Os R P H D Aff B Poll Instant System Native Profiler Raw Listener TcpStream Error)
        Error → EStateM StepError
        (State Os R P H D Aff B Poll Instant System Native Profiler Raw Listener TcpStream Error) Unit) :
    Except StepError (UnixFd.Hooks
      (State Os R P H D Aff B Poll Instant System Native Profiler Raw Listener TcpStream Error)
      H D (Other Raw Listener TcpStream Error) Error Metadata) := do
  let facts ← EvalUnixFdConstruction.sourceFacts p
  let pointerSize := p.runtime.target.pointerSize
  if pointerSize.bytes == 0 || pointerSize.bytes.toNat * 8 <= 1 then
    throw (.unsupported "invalid target pointer width for Unix isize")
  if hostIsizeBits < 2 || hostIsizeBits > 64 then
    throw (.unsupported "invalid host isize width for Unix FD limits")
  let targetIsizeMax := UInt64.ofNat (2^(pointerSize.bytes.toNat * 8 - 1) - 1)
  let hostIsizeMax := UInt64.ofNat (2^(hostIsizeBits - 1) - 1)
  let base : UnixFd.Hooks
      (State Os R P H D Aff B Poll Instant System Native Profiler Raw Listener TcpStream Error)
      H D (Other Raw Listener TcpStream Error) Error Metadata := {
    files := fileHooks
    errors
    os := facts.target.os
    communicate
    shortFdOperations
    targetIsizeMax
    hostIsizeMax
    table := pure {}
    putTable := fun _ => pure ()
    newReference := fun _ => throw (.invalidProgram "unbound descriptor ownership")
    cloneRef := fun _ => throw (.invalidProgram "unbound descriptor ownership")
    dropRef := fun _ => throw (.invalidProgram "unbound descriptor ownership")
    asUnix := fun _ => pure ()
    removeFileNumInterests := fun _ _ => pure ()
    checkAccess := fun pointer size => ValidityMachine.checkPointerAccess access pointer size
    randomShort
    writeInt := fun value dest => do
      let scalar ← lift (Scalar.fromInt value dest.layout.layout.size |>.mapError ScalarOps.scalarError)
      writePlaceImmediate place choice (.scalar scalar) ⟨.memory dest.mplace,dest.layout⟩
    otherPositionalRead
    otherPositionalWrite }
  let physicalReadiness := EvalUnixFdConstruction.readinessFromFiles
    registry fileHooks readinessRoute
  pure (ReadinessMachine.bindFiles registry
    (ReadinessMachine.bind registry physicalReadiness) base)

structure ControlSourceEffects (S : Type) where
  fullSync : Int32 → EStateM StepError S (Scalar Provenance)

private def readControlScalar
    (access : ValidityMachine.Access MiriMemoryKind
      (EvalCoreMachine.Stored Os R P H D (Other Raw Listener TcpStream Error) Aff B
        (HostRuntime.Storage Poll Instant System H D
          (Other Raw Listener TcpStream Error) Native Profiler)))
    (operand : OpTy Provenance) : EStateM StepError
      (State Os R P H D Aff B Poll Instant System Native Profiler Raw Listener TcpStream Error)
      (Scalar Provenance) := do
  let value ← ValidityMachine.readImmediate access operand
  match value.imm.toScalar with
  | .ok scalar => pure scalar
  | .error error => throw (ScalarOps.immediateError error)

/-- Assemble fcntl/ioctl dispatch from exact compiler ABI/constants and
canonical access. Only the shared general shim-signature provider and genuine
source policy/resource effects remain inputs. -/
def controlFromSource
    (p : CompilerProviders.Prepared)
    (userRelevantCrates : Array Nat)
    (isolatedOp : EvalUnixConstruction.IsolatedOp)
    (access : ValidityMachine.Access MiriMemoryKind
      (EvalCoreMachine.Stored Os R P H D (Other Raw Listener TcpStream Error) Aff B
        (HostRuntime.Storage Poll Instant System H D
          (Other Raw Listener TcpStream Error) Native Profiler)))
    (place : PlaceHooks Provenance
      (State Os R P H D Aff B Poll Instant System Native Profiler Raw Listener TcpStream Error)
      C MachineHooks.FrameExtra)
    (choice : C)
    (fd : UnixFd.Hooks
      (State Os R P H D Aff B Poll Instant System Native Profiler Raw Listener TcpStream Error)
      H D (Other Raw Listener TcpStream Error) Error Metadata)
    (signatures : ShimSignatures.Hooks Provenance
      (State Os R P H D Aff B Poll Instant System Native Profiler Raw Listener TcpStream Error)
      Place (MPlaceTy Provenance) (Pointer (Option Provenance)) ShimBody I)
    (typeBudget : Nat)
    (descriptor : SocketMachine.Descriptor (Other Raw Listener TcpStream Error))
    (virtual : VirtualSocket.Hooks
      (State Os R P H D Aff B Poll Instant System Native Profiler Raw Listener TcpStream Error)
      (FD H D (Other Raw Listener TcpStream Error)) Error)
    (tcp : TcpSocket.Hooks
      (State Os R P H D Aff B Poll Instant System Native Profiler Raw Listener TcpStream Error)
      (FD H D (Other Raw Listener TcpStream Error)) Raw Listener TcpStream Error Poll Host)
    (fileEffects : FileLockEffects
      (State Os R P H D Aff B Poll Instant System Native Profiler Raw Listener TcpStream Error)
      H Error)
    (effects : ControlSourceEffects
      (State Os R P H D Aff B Poll Instant System Native Profiler Raw Listener TcpStream Error)) :
    Except StepError (UnixFdControlDispatch.Hooks
      (State Os R P H D Aff B Poll Instant System Native Profiler Raw Listener TcpStream Error)
      H D (Other Raw Listener TcpStream Error) Error Metadata Place ShimBody I) := do
  unless fd.communicate == (isolatedOp == .allow) do
    throw (.invalidProgram "Unix fcntl isolation mode disagrees with Miri configuration")
  let i32Layout ← p.primitiveLayout "i32"
    |>.mapError fun error => .unsupported error
  let i32PointerType ← CompilerPrimitiveFacts.namedLayout p.runtime "i32_pointer"
    |>.mapError fun error => .unsupported error
  let libc := fun name => do
    match CompilerNamedConstants.scalar p.namedConstants name with
    | .ok scalar => pure scalar
    | .error error => throw (.unsupported error)
  let libcI32 := fun name => do
    let scalar ← libc name
    match scalar.toInt32 with
    | .ok value => pure value
    | .error error => throw (ScalarOps.scalarError error)
  let file ← fileOperationsFromSource p fd.errors fileEffects
  let control : UnixFdControl.Hooks
      (State Os R P H D Aff B Poll Instant System Native Profiler Raw Listener TcpStream Error)
      H D (Other Raw Listener TcpStream Error) Error Metadata := {
    fd
    libc
    libcI32
    readScalar := readControlScalar access
    readI32 := fun operand => do
      let scalar ← readControlScalar access operand
      match scalar.toInt32 with
      | .ok value => pure value
      | .error error => throw (ScalarOps.scalarError error)
    takeI32 := fun _ _ => throw (.unsupported "source fcntl varargs binding is unavailable")
    getFlags := fun _ => throw (.unsupported "source descriptor flag binding is unavailable")
    setFlags := fun _ _ => throw (.unsupported "source descriptor flag binding is unavailable")
    ioctl := fun _ _ _ => throw (.unsupported "source ioctl binding is unavailable")
    frameInStd := FrameMetadata.frameInStd
      (CompilerFrameMetadata.hooks p.lifecycle.frames userRelevantCrates)
    rejectIsolation := fun name => do
      match isolatedOp with
      | .allow => pure false
      | .reject .abort => throw (.termination (.unsupportedInIsolation name))
      | .reject .noWarning | .reject .warning | .reject .warningWithoutBacktrace => pure true
    fullSync := effects.fullSync }
  let base : UnixFdControlDispatch.Hooks
      (State Os R P H D Aff B Poll Instant System Native Profiler Raw Listener TcpStream Error)
      H D (Other Raw Listener TcpStream Error) Error Metadata Place ShimBody I := {
    control
    signatures
    signature := CompilerNamedShimAbi.query p.namedAbi
    i32Type := pure i32PointerType.ty
    typeBudget
    writeScalar := fun scalar dest =>
      writePlaceImmediate place choice (.scalar scalar) ⟨.memory dest.mplace,dest.layout⟩ }
  pure (UnixFdControlMachine.bind access descriptor virtual tcp file
    (pure i32Layout) (pure i32PointerType.ty) place choice base)

/-- Full source vectored field construction. The temporary iovec buffer uses
the compiler's exact element layout, EvalWorld allocation lifecycle, actual
pointer arithmetic, and provenance-preserving copy. `checkedSum` and host
usize width are native build properties, supplied as explicit host facts. -/
def vectoredFromFieldsWithLifecycle
    (p : CompilerProviders.Prepared)
    (access : ValidityMachine.Access MiriMemoryKind
      (EvalCoreMachine.Stored Os R P H D (Other Raw Listener TcpStream Error) Aff B
        (HostRuntime.Storage Poll Instant System H D
          (Other Raw Listener TcpStream Error) Native Profiler)))
    (allocation : PlaceMachine.AllocationConfig MiriMemoryKind
      (EvalCoreMachine.User Os R P H D (Other Raw Listener TcpStream Error) Aff B
        (HostRuntime.Storage Poll Instant System H D
          (Other Raw Listener TcpStream Error) Native Profiler)))
    (compiler : PlaceMachine.CompilerHooks MiriMemoryKind
      (EvalCoreMachine.User Os R P H D (Other Raw Listener TcpStream Error) Aff B
        (HostRuntime.Storage Poll Instant System H D
          (Other Raw Listener TcpStream Error) Native Profiler)) C)
    (projection : PlaceProjectionHooks Provenance
      (State Os R P H D Aff B Poll Instant System Native Profiler Raw Listener TcpStream Error)
      C MachineHooks.FrameExtra)
    (choice : C) (spans : AllocationDriver.SpanHooks)
    (pointers : PointerMachine.Hooks MiriMemoryKind
      (ValidityMachine.Control (EvalCoreMachine.Stored Os R P H D
        (Other Raw Listener TcpStream Error) Aff B
        (HostRuntime.Storage Poll Instant System H D
          (Other Raw Listener TcpStream Error) Native Profiler))))
    (extras : MemoryExtras.Hooks MiriMemoryKind
      (EvalCoreMachine.User Os R P H D (Other Raw Listener TcpStream Error) Aff B
        (HostRuntime.Storage Poll Instant System H D
          (Other Raw Listener TcpStream Error) Native Profiler)) P)
    (diagnostic : AllocId → PlaceMachine.MachineM MiriMemoryKind
      (EvalCoreMachine.User Os R P H D (Other Raw Listener TcpStream Error) Aff B
        (HostRuntime.Storage Poll Instant System H D
          (Other Raw Listener TcpStream Error) Native Profiler)) Unit)
    (nativeDrop : Option (Allocation Provenance Miri.TreeBorrows.BorrowTree →
      MachineHooks.M MiriMemoryKind
        (EvalCoreMachine.User Os R P H D (Other Raw Listener TcpStream Error) Aff B
          (HostRuntime.Storage Poll Instant System H D
            (Other Raw Listener TcpStream Error) Native Profiler)) Unit))
    (fd : UnixFd.Hooks
      (State Os R P H D Aff B Poll Instant System Native Profiler Raw Listener TcpStream Error)
      H D (Other Raw Listener TcpStream Error) Error Metadata)
    (hostUsizeBits : Nat) (checkedSum : Bool) :
    UnixVectored.Hooks
      (State Os R P H D Aff B Poll Instant System Native Profiler Raw Listener TcpStream Error)
      H D (Other Raw Listener TcpStream Error) Error Metadata := Id.run do
  let base : UnixVectored.Hooks
      (State Os R P H D Aff B Poll Instant System Native Profiler Raw Listener TcpStream Error)
      H D (Other Raw Listener TcpStream Error) Error Metadata := {
    fd
    readI32 := fun _ => unresolved "readI32"
    readPointer := fun _ => unresolved "readPointer"
    readSigned := fun _ => unresolved "readSigned"
    arrayPlace := fun _ _ => unresolved "arrayPlace"
    startArray := fun _ => unresolved "startArray"
    index := fun _ _ => unresolved "index"
    field := fun _ _ => unresolved "field"
    readFieldSigned := fun _ => unresolved "readFieldSigned"
    readFieldPointer := fun _ => unresolved "readFieldPointer"
    allocateStack := fun _ => unresolved "allocateStack"
    deallocateStack := fun _ => unresolved "deallocateStack"
    offsetInbounds := fun _ _ => unresolved "offsetInbounds"
    copyNonoverlapping := fun _ _ _ => unresolved "copyNonoverlapping"
    writeTargetIsize := fun _ _ => unresolved "writeTargetIsize"
    hostUsizeBits
    checkedSum }
  let unitLayout := do
    match p.primitiveLayout "unit" with
    | .ok value => pure value
    | .error reason => throw (.unsupported reason)
  let arrayLayout := CompilerNamedFields.iovecArrayLayout p.runtime EvalProjectionMachine.arrays
  let fieldIndex := fun parent name => do
    match CompilerNamedFields.fieldIndex p.runtime parent name with
    | .ok index => pure index
    | .error error => throw error
  let deallocateStack := fun pointer =>
    EvalAllocationMachine.deallocateWith spans pointers extras diagnostic nativeDrop pointer none .stack
  return UnixVectoredMachine.bind access allocation pointers projection
    (PlaceMachine.placeHooks access allocation compiler) choice
    unitLayout arrayLayout fieldIndex deallocateStack base

/-- Compatibility wrapper for callers which still package the genuine
diagnostic and native-drop leaves in an AllocationMachine record. The source
lifecycle itself remains constructed at the actual operation point. -/
def vectoredFromFields
    (p : CompilerProviders.Prepared)
    (access : ValidityMachine.Access MiriMemoryKind
      (EvalCoreMachine.Stored Os R P H D (Other Raw Listener TcpStream Error) Aff B
        (HostRuntime.Storage Poll Instant System H D
          (Other Raw Listener TcpStream Error) Native Profiler)))
    (allocation : PlaceMachine.AllocationConfig MiriMemoryKind
      (EvalCoreMachine.User Os R P H D (Other Raw Listener TcpStream Error) Aff B
        (HostRuntime.Storage Poll Instant System H D
          (Other Raw Listener TcpStream Error) Native Profiler)))
    (compiler : PlaceMachine.CompilerHooks MiriMemoryKind
      (EvalCoreMachine.User Os R P H D (Other Raw Listener TcpStream Error) Aff B
        (HostRuntime.Storage Poll Instant System H D
          (Other Raw Listener TcpStream Error) Native Profiler)) C)
    (projection : PlaceProjectionHooks Provenance
      (State Os R P H D Aff B Poll Instant System Native Profiler Raw Listener TcpStream Error)
      C MachineHooks.FrameExtra)
    (choice : C) (spans : AllocationDriver.SpanHooks)
    (pointers : PointerMachine.Hooks MiriMemoryKind
      (ValidityMachine.Control (EvalCoreMachine.Stored Os R P H D
        (Other Raw Listener TcpStream Error) Aff B
        (HostRuntime.Storage Poll Instant System H D
          (Other Raw Listener TcpStream Error) Native Profiler))))
    (extras : MemoryExtras.Hooks MiriMemoryKind
      (EvalCoreMachine.User Os R P H D (Other Raw Listener TcpStream Error) Aff B
        (HostRuntime.Storage Poll Instant System H D
          (Other Raw Listener TcpStream Error) Native Profiler)) P)
    (deallocation : AllocationMachine.DeallocationHooks MiriMemoryKind
      (EvalCoreMachine.User Os R P H D (Other Raw Listener TcpStream Error) Aff B
        (HostRuntime.Storage Poll Instant System H D
          (Other Raw Listener TcpStream Error) Native Profiler)) P)
    (fd : UnixFd.Hooks
      (State Os R P H D Aff B Poll Instant System Native Profiler Raw Listener TcpStream Error)
      H D (Other Raw Listener TcpStream Error) Error Metadata)
    (hostUsizeBits : Nat) (checkedSum : Bool) :
    UnixVectored.Hooks
      (State Os R P H D Aff B Poll Instant System Native Profiler Raw Listener TcpStream Error)
      H D (Other Raw Listener TcpStream Error) Error Metadata :=
  vectoredFromFieldsWithLifecycle p access allocation compiler projection choice spans pointers
    extras deallocation.diagnostic deallocation.nativeDrop fd hostUsizeBits checkedSum

/-- Compatibility wrapper for callers that already own a complete execution
configuration. The production source constructor uses `vectoredFromFields`
so Core can build the foreign component without a configuration cycle. -/
def vectoredFromSource
    (p : CompilerProviders.Prepared)
    (access : ValidityMachine.Access MiriMemoryKind
      (EvalCoreMachine.Stored Os R P H D (Other Raw Listener TcpStream Error) Aff B
        (HostRuntime.Storage Poll Instant System H D
          (Other Raw Listener TcpStream Error) Native Profiler)))
    (config : ExecConfig Os R P H D Aff B Poll Instant System Native Profiler
      Raw Listener TcpStream Error C ClockHost)
    (choice : C) (spans : AllocationDriver.SpanHooks)
    (pointers : PointerMachine.Hooks MiriMemoryKind
      (ValidityMachine.Control (EvalCoreMachine.Stored Os R P H D
        (Other Raw Listener TcpStream Error) Aff B
        (HostRuntime.Storage Poll Instant System H D
          (Other Raw Listener TcpStream Error) Native Profiler))))
    (extras : MemoryExtras.Hooks MiriMemoryKind
      (EvalCoreMachine.User Os R P H D (Other Raw Listener TcpStream Error) Aff B
        (HostRuntime.Storage Poll Instant System H D
          (Other Raw Listener TcpStream Error) Native Profiler)) P)
    (deallocation : AllocationMachine.DeallocationHooks MiriMemoryKind
      (EvalCoreMachine.User Os R P H D (Other Raw Listener TcpStream Error) Aff B
        (HostRuntime.Storage Poll Instant System H D
          (Other Raw Listener TcpStream Error) Native Profiler)) P)
    (fd : UnixFd.Hooks
      (State Os R P H D Aff B Poll Instant System Native Profiler Raw Listener TcpStream Error)
      H D (Other Raw Listener TcpStream Error) Error Metadata)
    (hostUsizeBits : Nat) (checkedSum : Bool) :
    UnixVectored.Hooks
      (State Os R P H D Aff B Poll Instant System Native Profiler Raw Listener TcpStream Error)
      H D (Other Raw Listener TcpStream Error) Error Metadata :=
  vectoredFromFields p access config.allocation config.compiler
    (ExecutionMachine.projectionHooks config) choice spans pointers extras deallocation fd
    hostUsizeBits checkedSum

end Miri.Input.EvalUnixIoConstruction
