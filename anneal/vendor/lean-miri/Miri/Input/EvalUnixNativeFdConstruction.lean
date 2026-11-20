import Miri.Input.CompilerProviders
import Miri.Input.CompilerNamedShimAbi
import Miri.Input.CompilerCallConstruction
import Miri.Input.CompilerForeignSymbols
import Miri.Input.CompilerPrimitiveFacts
import Miri.Input.CompilerNamedConstants
import Miri.Input.EvalCoreMachine
import Miri.Input.EvalSocketStorage
import Miri.Input.EvalHostRuntimeConstruction
import Miri.Input.EvalUnixConstruction
import Miri.Input.EvalUnixFdConstruction
import Miri.Input.EvalUnixIoConstruction
import Miri.Input.EvalAllocationMachine
import Miri.Input.EvalProjectionMachine
import Miri.Input.CompilerFrameMetadata
import Miri.Interpreter.UnixFdDispatch
import Miri.Interpreter.UnixFdControlDispatch
import Miri.Interpreter.UnixVectoredDispatch
import Miri.Interpreter.ShimSignatures
import Miri.Interpreter.RawMemoryMachine
import Miri.Interpreter.IntrinsicVectorMachine

/-! Source construction for the native Unix file-descriptor dispatch family.
Only actual host filesystem/path/resource effects, random choices, and source
socket/event operations remain inputs. ABI checks, path reads, descriptor
ownership/readiness, control dispatch, and vectored memory behavior use the
canonical compiler and EvalWorld components. -/
namespace Miri.Input.EvalUnixNativeFdConstruction
open Miri.ABI Miri.Memory Miri.MIR Miri.Interpreter

abbrev Other Raw Listener TcpStream Error :=
  EvalSocketStorage.Other Raw Listener TcpStream Error
abbrev User Os R P H D Aff B Poll Instant System Native Profiler Raw Listener TcpStream Error :=
  EvalSocketStorage.User Os R P H D Aff B Poll Instant System Native Profiler Raw Listener TcpStream Error
abbrev State Os R P H D Aff B Poll Instant System Native Profiler Raw Listener TcpStream Error :=
  EvalSocketStorage.State Os R P H D Aff B Poll Instant System Native Profiler Raw Listener TcpStream Error
abbrev Stored Os R P H D Aff B Poll Instant System Native Profiler Raw Listener TcpStream Error :=
  EvalCoreMachine.Stored Os R P H D (Other Raw Listener TcpStream Error) Aff B
    (HostRuntime.Storage Poll Instant System H D (Other Raw Listener TcpStream Error) Native Profiler)
abbrev InnerControl Os R P H D Aff B Poll Instant System Native Profiler Raw Listener TcpStream Error :=
  ValidityMachine.Control (Stored Os R P H D Aff B Poll Instant System Native Profiler Raw Listener TcpStream Error)
abbrev FD H D O := Files.Ref (Files.Description H D O)
abbrev M Os R P H D Aff B Poll Instant System Native Profiler Raw Listener TcpStream Error A :=
  MachineHooks.M MiriMemoryKind
    (User Os R P H D Aff B Poll Instant System Native Profiler Raw Listener TcpStream Error) A
abbrev ExecConfig Os R P H D Aff B Poll Instant System Native Profiler Raw Listener TcpStream Error C ClockHost :=
  ExecutionMachine.Config MiriMemoryKind
    (User Os R P H D Aff B Poll Instant System Native Profiler Raw Listener TcpStream Error)
    C (Other Raw Listener TcpStream Error) ABI.ExternAbi ClockHost

structure OpenHostEffects (S H D E Meta Path Os : Type) where
  /-- Conversion from the host OsString representation to this host's Path. -/
  pathFromOs : Os → Path
  isAbsolute : Path → Bool
  isEmpty : Path → Bool
  isDot : Path → Bool
  emptyPath : Path
  /-- Exact host path::absolute(...).is_ok_and(starts_with("/proc")). -/
  procAbsolute : Path → EStateM StepError S Bool
  diagnoseProc : EStateM StepError S Unit
  hostCustomFlag : UnixOpen.Flag → EStateM StepError S UInt32
  openFile : Option D → Path → UnixOpen.Options → EStateM StepError S
    (Except (IoError.HostError E) H)
  openDirectoryAsFile : Option D → Path → UnixOpen.Options → EStateM StepError S
    (Except (IoError.HostError E) H)
  metadata : H → EStateM StepError S (Except (IoError.HostError E) UnixOpen.Metadata)
  asDirectory : H → EStateM StepError S D

structure OtherPositionalEffects (S H D O E : Type) where
  read : FD H D O → UInt64 → Pointer (Option Provenance) → Nat → Files.Finish S E →
    EStateM StepError S Unit
  write : FD H D O → UInt64 → Pointer (Option Provenance) → Nat → Files.Finish S E →
    EStateM StepError S Unit

structure Components (Os R P H D Aff B Poll Instant System Native Profiler Raw Listener TcpStream Error Meta Path Place C ClockHost I : Type)
    (ShimBody : Type := B) where
  files : Files.Hooks
    (State Os R P H D Aff B Poll Instant System Native Profiler Raw Listener TcpStream Error)
    H D (Other Raw Listener TcpStream Error) Error Meta
  registry : FileMachine.Hooks MiriMemoryKind
    (User Os R P H D Aff B Poll Instant System Native Profiler Raw Listener TcpStream Error)
    H D (Other Raw Listener TcpStream Error)
  readiness : ReadinessMachine.Hooks MiriMemoryKind
    (User Os R P H D Aff B Poll Instant System Native Profiler Raw Listener TcpStream Error)
    H D (Other Raw Listener TcpStream Error)
  fd : UnixFdDispatch.Hooks
    (State Os R P H D Aff B Poll Instant System Native Profiler Raw Listener TcpStream Error)
    H D (Other Raw Listener TcpStream Error) Error Meta Path
  control : UnixFdControlDispatch.Hooks
    (State Os R P H D Aff B Poll Instant System Native Profiler Raw Listener TcpStream Error)
    H D (Other Raw Listener TcpStream Error) Error Meta Place ShimBody I
  vector : UnixVectoredDispatch.Hooks
    (State Os R P H D Aff B Poll Instant System Native Profiler Raw Listener TcpStream Error)
    H D (Other Raw Listener TcpStream Error) Error Meta Place ShimBody I

private def lift (value : Except StepError A) : M Os R P H D Aff B Poll Instant System Native Profiler Raw Listener TcpStream Error A :=
  match value with | .ok value => pure value | .error error => throw error

private def readScalar
    (access : ValidityMachine.Access MiriMemoryKind
      (Stored Os R P H D Aff B Poll Instant System Native Profiler Raw Listener TcpStream Error))
    (operand : OpTy Provenance) : M Os R P H D Aff B Poll Instant System Native Profiler Raw Listener TcpStream Error
      (Scalar Provenance) := do
  let immediate ← ValidityMachine.readImmediate access operand
  lift (immediate.imm.toScalar.mapError ScalarOps.immediateError)

private def readI32
    (access : ValidityMachine.Access MiriMemoryKind
      (Stored Os R P H D Aff B Poll Instant System Native Profiler Raw Listener TcpStream Error))
    (operand : OpTy Provenance) : M Os R P H D Aff B Poll Instant System Native Profiler Raw Listener TcpStream Error Int32 := do
  lift ((← readScalar access operand).toInt32.mapError ScalarOps.scalarError)

private def readUsize
    (access : ValidityMachine.Access MiriMemoryKind
      (Stored Os R P H D Aff B Poll Instant System Native Profiler Raw Listener TcpStream Error))
    (operand : OpTy Provenance) : M Os R P H D Aff B Poll Instant System Native Profiler Raw Listener TcpStream Error UInt64 := do
  lift ((← readScalar access operand).toTargetUsize access.runtime.pointerSize |>.mapError ScalarOps.scalarError)

private def readOffset
    (access : ValidityMachine.Access MiriMemoryKind
      (Stored Os R P H D Aff B Poll Instant System Native Profiler Raw Listener TcpStream Error))
    (operand : OpTy Provenance) : M Os R P H D Aff B Poll Instant System Native Profiler Raw Listener TcpStream Error Int := do
  lift ((← readScalar access operand).toInt operand.layout.layout.size |>.mapError ScalarOps.scalarError)

private def readPointer
    (access : ValidityMachine.Access MiriMemoryKind
      (Stored Os R P H D Aff B Poll Instant System Native Profiler Raw Listener TcpStream Error))
    (operand : OpTy Provenance) : M Os R P H D Aff B Poll Instant System Native Profiler Raw Listener TcpStream Error
      (Pointer (Option Provenance)) := do
  lift ((← readScalar access operand).toPointer access.runtime.base |>.mapError ScalarOps.scalarError)

private def readMode
    (p : CompilerProviders.Prepared)
    (signatures : ShimSignatures.Hooks Provenance
      (State Os R P H D Aff B Poll Instant System Native Profiler Raw Listener TcpStream Error)
      Place (MPlaceTy Provenance) (Pointer (Option Provenance)) ShimBody I)
    (typeBudget : Nat) (name : String)
    (tail : ShimSignatures.Varargs Provenance) (_use : UnixOpen.ModeUse) :
    M Os R P H D Aff B Poll Instant System Native Profiler Raw Listener TcpStream Error UInt32 := do
  let mode ← match CompilerPrimitiveFacts.namedLayout p.runtime "mode_t" with
    | .ok value => pure value
    | .error reason => throw (.unsupported s!"compiler mode_t layout: {reason}")
  let expected ← if mode.layout.size.bytes >= 4 then
      pure #[mode.ty]
    else do
      let i32 ← match p.primitiveLayout "i32" with
        | .ok value => pure value
        | .error reason => throw (.unsupported s!"compiler i32 layout for mode_t promotion: {reason}")
      pure #[i32.ty]
  let (values,_) ← ShimSignatures.take signatures typeBudget (pure expected) tail
  let some value := values[0]? | throw (.invalidProgram s!"{name} mode_t argument missing")
  lift ((← signatures.readScalar value).toUInt32.mapError ScalarOps.scalarError)

/-- Complete descriptor component construction over the selected compiler,
canonical EvalWorld memory and existing Files/readiness/runtime policies.
Host path/file operations, random short-I/O draws, source socket/event
positional operations, host file locks, and full-sync remain explicit typed
effects. -/
def fromSourceWithLifecycle [DecidableEq MiriMemoryKind]
    (p : CompilerProviders.Prepared)
    (userRelevantCrates : Array Nat)
    (compatibilityBudget typeBudget : Nat)
    (host : EvalHostRuntimeConstruction.OsHostEffects Os)
    (openHost : OpenHostEffects
      (State Os R P H D Aff B Poll Instant System Native Profiler Raw Listener TcpStream Error)
      H D Error Meta Path Os)
    (memory : EvalHostRuntimeConstruction.EnvironmentMemory
      (InnerControl Os R P H D Aff B Poll Instant System Native Profiler Raw Listener TcpStream Error)
      C Payload)
    (environment : UnixEnvironmentDispatch.Hooks
      (State Os R P H D Aff B Poll Instant System Native Profiler Raw Listener TcpStream Error)
      Os Error EnvVars.Kind)
    (resources : EvalUnixIoConstruction.FileResourceEffects
      (State Os R P H D Aff B Poll Instant System Native Profiler Raw Listener TcpStream Error)
      H D (Other Raw Listener TcpStream Error))
    (hostFiles : EvalUnixIoConstruction.HostFileEffects
      (State Os R P H D Aff B Poll Instant System Native Profiler Raw Listener TcpStream Error)
      H D (Other Raw Listener TcpStream Error) Error Meta)
    (otherFiles : EvalUnixIoConstruction.OtherFileEffects
      (State Os R P H D Aff B Poll Instant System Native Profiler Raw Listener TcpStream Error)
      H D (Other Raw Listener TcpStream Error) Error)
    (positional : OtherPositionalEffects
      (State Os R P H D Aff B Poll Instant System Native Profiler Raw Listener TcpStream Error)
      H D (Other Raw Listener TcpStream Error) Error)
    (fileLocks : EvalUnixIoConstruction.FileLockEffects
      (State Os R P H D Aff B Poll Instant System Native Profiler Raw Listener TcpStream Error)
      H Error)
    (controlEffects : EvalUnixIoConstruction.ControlSourceEffects
      (State Os R P H D Aff B Poll Instant System Native Profiler Raw Listener TcpStream Error))
    (signatures : ShimSignatures.Hooks Provenance
      (State Os R P H D Aff B Poll Instant System Native Profiler Raw Listener TcpStream Error)
      Place (MPlaceTy Provenance) (Pointer (Option Provenance)) ShimBody I)
    (readinessRoute : EvalUnixFdConstruction.ReadinessRoute
      (State Os R P H D Aff B Poll Instant System Native Profiler Raw Listener TcpStream Error))
    (watcherReferenceBudget fileReferenceBudget hostUsizeBits : Nat)
    (shortFdOperations : Bool) (hostIsizeBits : Nat)
    (randomShort : M Os R P H D Aff B Poll Instant System Native Profiler Raw Listener TcpStream Error Bool)
    (communicate : Bool)
    (place : PlaceHooks Provenance
      (State Os R P H D Aff B Poll Instant System Native Profiler Raw Listener TcpStream Error)
      C MachineHooks.FrameExtra)
    (choice : C)
    (isolatedOp : EvalUnixConstruction.IsolatedOp)
    (pollAndUnblockZero : M Os R P H D Aff B Poll Instant System Native Profiler Raw Listener TcpStream Error Unit)
    (descriptor : SocketMachine.Descriptor (Other Raw Listener TcpStream Error))
    (virtual : VirtualSocket.Hooks
      (State Os R P H D Aff B Poll Instant System Native Profiler Raw Listener TcpStream Error)
      (FD H D (Other Raw Listener TcpStream Error)) Error)
    (tcp : TcpSocket.Hooks
      (State Os R P H D Aff B Poll Instant System Native Profiler Raw Listener TcpStream Error)
      (FD H D (Other Raw Listener TcpStream Error)) Raw Listener TcpStream Error Poll Host)
    (checkedSum : Bool)
    (allocation : PlaceMachine.AllocationConfig MiriMemoryKind
      (EvalCoreMachine.User Os R P H D (Other Raw Listener TcpStream Error) Aff B
        (HostRuntime.Storage Poll Instant System H D (Other Raw Listener TcpStream Error) Native Profiler)))
    (compiler : PlaceMachine.CompilerHooks MiriMemoryKind
      (EvalCoreMachine.User Os R P H D (Other Raw Listener TcpStream Error) Aff B
        (HostRuntime.Storage Poll Instant System H D (Other Raw Listener TcpStream Error) Native Profiler)) C)
    (projectionHooks : PlaceProjectionHooks Provenance
      (State Os R P H D Aff B Poll Instant System Native Profiler Raw Listener TcpStream Error)
      C MachineHooks.FrameExtra)
    (spans : AllocationDriver.SpanHooks)
    (extras : MemoryExtras.Hooks MiriMemoryKind
      (EvalCoreMachine.User Os R P H D (Other Raw Listener TcpStream Error) Aff B
        (HostRuntime.Storage Poll Instant System H D (Other Raw Listener TcpStream Error) Native Profiler)) P)
    (diagnostic : AllocId → PlaceMachine.MachineM MiriMemoryKind
      (EvalCoreMachine.User Os R P H D (Other Raw Listener TcpStream Error) Aff B
        (HostRuntime.Storage Poll Instant System H D (Other Raw Listener TcpStream Error) Native Profiler)) Unit)
    (nativeDrop : Option (Allocation Provenance Miri.TreeBorrows.BorrowTree →
      MachineHooks.M MiriMemoryKind
        (EvalCoreMachine.User Os R P H D (Other Raw Listener TcpStream Error) Aff B
          (HostRuntime.Storage Poll Instant System H D
            (Other Raw Listener TcpStream Error) Native Profiler)) Unit)) : Except StepError
      (Components Os R P H D Aff B Poll Instant System Native Profiler Raw Listener TcpStream Error Meta Path Place C ClockHost I ShimBody) := do
  unless environment.env.process.communicate == communicate do
    throw (.invalidProgram "Unix FD communication policy disagrees with source environment")
  unless communicate == (isolatedOp == .allow) do
    throw (.invalidProgram "Unix FD isolation policy disagrees with Miri configuration")
  let files ← EvalUnixIoConstruction.filesFromSource p memory.access memory.pointers hostFiles otherFiles
  let fileRegistry := EvalUnixIoConstruction.fileRegistry
    (Os := Os) (R := R) (P := P) (H := H) (D := D) (Aff := Aff) (B := B)
    (Poll := Poll) (Instant := Instant) (System := System) (Native := Native)
    (Profiler := Profiler) (Raw := Raw) (Listener := Listener) (TcpStream := TcpStream)
    (Error := Error) hostUsizeBits fileReferenceBudget resources
  let dropDescription := fun (reference : FD H D (Other Raw Listener TcpStream Error)) => do
    match reference.value with
    | .stdin | .stdout | .stderr | .nullOutput => pure ()
    | .file handle _ _ => resources.dropFile handle
    | .directory handle => resources.dropDirectory handle
    | .other payload => resources.dropOther payload
  let readiness := EvalUnixFdConstruction.readiness fileRegistry watcherReferenceBudget dropDescription
  let errors := environment.env.errors
  let fd ← EvalUnixIoConstruction.unixFdFromSource p communicate shortFdOperations hostIsizeBits
    readiness readinessRoute
    files errors memory.access randomShort place choice positional.read positional.write
  let openHooks : UnixOpen.Hooks
      (State Os R P H D Aff B Poll Instant System Native Profiler Raw Listener TcpStream Error)
      H D (Other Raw Listener TcpStream Error) Error Meta Path := {
    fd
    hostWindows := host.hostWindows
    flag := fun flag => do
      let name := match flag with
        | .readonly => "O_RDONLY" | .writeonly => "O_WRONLY" | .readwrite => "O_RDWR"
        | .accessMode => "O_ACCMODE" | .largefile => "O_LARGEFILE" | .tmpfile => "O_TMPFILE"
        | .directory => "O_DIRECTORY" | .append => "O_APPEND" | .trunc => "O_TRUNC"
        | .create => "O_CREAT" | .exclusive => "O_EXCL" | .cloexec => "O_CLOEXEC"
        | .nofollow => "O_NOFOLLOW" | .atCwd => "AT_FDCWD"
      match (CompilerNamedConstants.scalar p.namedConstants name : Except String (Scalar Provenance)) with
      | .ok value => lift (value.toUInt32.mapError ScalarOps.scalarError)
      | .error reason => throw (StepError.unsupported s!"compiler libc constant `{name}`: {reason}")
    hostCustomFlag := openHost.hostCustomFlag
    readMode := fun _ => throw (.unsupported "open mode requires source variadic arguments")
    isolationReject := fun name => do
      match isolatedOp with
      | .allow => pure false
      | .reject .abort => throw (.termination (.unsupportedInIsolation name))
      | .reject .noWarning | .reject .warning | .reject .warningWithoutBacktrace => pure true
    procAbsolute := openHost.procAbsolute
    diagnoseProc := openHost.diagnoseProc
    isAbsolute := openHost.isAbsolute
    isEmpty := openHost.isEmpty
    isDot := openHost.isDot
    emptyPath := openHost.emptyPath
    openFile := openHost.openFile
    openDirectoryAsFile := openHost.openDirectoryAsFile
    metadata := openHost.metadata
    asDirectory := openHost.asDirectory
    dropFile := resources.dropFile
    dropDirectory := resources.dropDirectory
    permissionDenied := errors.hostFromKind .PermissionDenied
    hostUsizeBits }
  let symbols ← p.foreignSymbols |>.mapError StepError.unsupported
  let callCompiler := CompilerCallConstruction.compiler p compatibilityBudget
  let transmuteProjection := place.projection choice
  let transmute := fun operand target => do
    let projection ← transmuteProjection
    match operand.transmute projection target |>.mapError IntrinsicVectorMachine.projectionError with
    | .ok value => pure value
    | .error error => throw error
  let fdDispatch : UnixFdDispatch.Hooks
      (State Os R P H D Aff B Poll Instant System Native Profiler Raw Listener TcpStream Error)
      H D (Other Raw Listener TcpStream Error) Error Meta Path := {
    file := openHooks
    expectedAbi := fun name request => do
      let some operation := UnixFdDispatch.parse name |
        throw (.unsupported s!"Unix FD ABI requested for unselected symbol `{name}`")
      let expected := UnixFdDispatch.signature operation
      unless expected.args == request.args && expected.ret == request.ret && expected.variadic == request.variadic do
        throw (.invalidProgram s!"Unix FD signature recipe disagrees with `{name}`")
      CompilerNamedShimAbi.query p.namedAbi name
    argumentCompat := callCompiler.checkArgumentCompat choice
    checkSymbolClash := fun name =>
      match CompilerForeignSymbols.checkSymbolClash symbols name with
      | .ok () => pure ()
      | .error error => throw error
    transmute
    readI32 := readI32 memory.access
    readUsize := readUsize memory.access
    readOffset := readOffset memory.access
    readPointer := readPointer memory.access
    readPath := fun pointer => do
      let osPath ← OsStrings.readPath environment.env.strings pointer
      pure (openHost.pathFromOs osPath)
    readMode := fun name tail use => readMode p signatures typeBudget name tail use
    pollAndUnblockZero }
  let placeHooks := memory.projection.place
  let control ← EvalUnixIoConstruction.controlFromSource p userRelevantCrates isolatedOp
    memory.access placeHooks choice fd signatures typeBudget descriptor virtual tcp fileLocks controlEffects
  let vector := EvalUnixIoConstruction.vectoredFromFieldsWithLifecycle p memory.access allocation compiler
    projectionHooks choice spans memory.pointers extras diagnostic nativeDrop fd hostUsizeBits checkedSum
  pure ⟨files,fileRegistry,readiness,fdDispatch,control,
    ⟨vector,signatures,CompilerNamedShimAbi.query p.namedAbi⟩⟩

/-- Compatibility entry point for callers which already carry a full
deallocation hook record. New source assembly should pass the genuine
diagnostic/native-drop leaves to `fromSourceWithLifecycle` directly. -/
def fromSource [DecidableEq MiriMemoryKind]
    (p : CompilerProviders.Prepared)
    (userRelevantCrates : Array Nat)
    (compatibilityBudget typeBudget : Nat)
    (host : EvalHostRuntimeConstruction.OsHostEffects Os)
    (openHost : OpenHostEffects
      (State Os R P H D Aff B Poll Instant System Native Profiler Raw Listener TcpStream Error)
      H D Error Meta Path Os)
    (memory : EvalHostRuntimeConstruction.EnvironmentMemory
      (InnerControl Os R P H D Aff B Poll Instant System Native Profiler Raw Listener TcpStream Error)
      C Payload)
    (environment : UnixEnvironmentDispatch.Hooks
      (State Os R P H D Aff B Poll Instant System Native Profiler Raw Listener TcpStream Error)
      Os Error EnvVars.Kind)
    (resources : EvalUnixIoConstruction.FileResourceEffects
      (State Os R P H D Aff B Poll Instant System Native Profiler Raw Listener TcpStream Error)
      H D (Other Raw Listener TcpStream Error))
    (hostFiles : EvalUnixIoConstruction.HostFileEffects
      (State Os R P H D Aff B Poll Instant System Native Profiler Raw Listener TcpStream Error)
      H D (Other Raw Listener TcpStream Error) Error Meta)
    (otherFiles : EvalUnixIoConstruction.OtherFileEffects
      (State Os R P H D Aff B Poll Instant System Native Profiler Raw Listener TcpStream Error)
      H D (Other Raw Listener TcpStream Error) Error)
    (positional : OtherPositionalEffects
      (State Os R P H D Aff B Poll Instant System Native Profiler Raw Listener TcpStream Error)
      H D (Other Raw Listener TcpStream Error) Error)
    (fileLocks : EvalUnixIoConstruction.FileLockEffects
      (State Os R P H D Aff B Poll Instant System Native Profiler Raw Listener TcpStream Error)
      H Error)
    (controlEffects : EvalUnixIoConstruction.ControlSourceEffects
      (State Os R P H D Aff B Poll Instant System Native Profiler Raw Listener TcpStream Error))
    (signatures : ShimSignatures.Hooks Provenance
      (State Os R P H D Aff B Poll Instant System Native Profiler Raw Listener TcpStream Error)
      Place (MPlaceTy Provenance) (Pointer (Option Provenance)) ShimBody I)
    (readinessRoute : EvalUnixFdConstruction.ReadinessRoute
      (State Os R P H D Aff B Poll Instant System Native Profiler Raw Listener TcpStream Error))
    (watcherReferenceBudget fileReferenceBudget hostUsizeBits : Nat)
    (shortFdOperations : Bool) (hostIsizeBits : Nat)
    (randomShort : M Os R P H D Aff B Poll Instant System Native Profiler Raw Listener TcpStream Error Bool)
    (communicate : Bool)
    (place : PlaceHooks Provenance
      (State Os R P H D Aff B Poll Instant System Native Profiler Raw Listener TcpStream Error)
      C MachineHooks.FrameExtra)
    (choice : C)
    (isolatedOp : EvalUnixConstruction.IsolatedOp)
    (pollAndUnblockZero : M Os R P H D Aff B Poll Instant System Native Profiler Raw Listener TcpStream Error Unit)
    (descriptor : SocketMachine.Descriptor (Other Raw Listener TcpStream Error))
    (virtual : VirtualSocket.Hooks
      (State Os R P H D Aff B Poll Instant System Native Profiler Raw Listener TcpStream Error)
      (FD H D (Other Raw Listener TcpStream Error)) Error)
    (tcp : TcpSocket.Hooks
      (State Os R P H D Aff B Poll Instant System Native Profiler Raw Listener TcpStream Error)
      (FD H D (Other Raw Listener TcpStream Error)) Raw Listener TcpStream Error Poll Host)
    (checkedSum : Bool)
    (allocation : PlaceMachine.AllocationConfig MiriMemoryKind
      (EvalCoreMachine.User Os R P H D (Other Raw Listener TcpStream Error) Aff B
        (HostRuntime.Storage Poll Instant System H D (Other Raw Listener TcpStream Error) Native Profiler)))
    (compiler : PlaceMachine.CompilerHooks MiriMemoryKind
      (EvalCoreMachine.User Os R P H D (Other Raw Listener TcpStream Error) Aff B
        (HostRuntime.Storage Poll Instant System H D (Other Raw Listener TcpStream Error) Native Profiler)) C)
    (projectionHooks : PlaceProjectionHooks Provenance
      (State Os R P H D Aff B Poll Instant System Native Profiler Raw Listener TcpStream Error)
      C MachineHooks.FrameExtra)
    (spans : AllocationDriver.SpanHooks)
    (extras : MemoryExtras.Hooks MiriMemoryKind
      (EvalCoreMachine.User Os R P H D (Other Raw Listener TcpStream Error) Aff B
        (HostRuntime.Storage Poll Instant System H D (Other Raw Listener TcpStream Error) Native Profiler)) P)
    (deallocation : AllocationMachine.DeallocationHooks MiriMemoryKind
      (EvalCoreMachine.User Os R P H D (Other Raw Listener TcpStream Error) Aff B
        (HostRuntime.Storage Poll Instant System H D (Other Raw Listener TcpStream Error) Native Profiler)) P) : Except StepError
      (Components Os R P H D Aff B Poll Instant System Native Profiler Raw Listener TcpStream Error Meta Path Place C ClockHost I ShimBody) :=
  fromSourceWithLifecycle p userRelevantCrates compatibilityBudget typeBudget host openHost
    memory environment resources hostFiles otherFiles positional fileLocks controlEffects
    signatures readinessRoute watcherReferenceBudget fileReferenceBudget hostUsizeBits
    shortFdOperations hostIsizeBits randomShort communicate place choice isolatedOp
    pollAndUnblockZero descriptor virtual tcp checkedSum allocation compiler projectionHooks
    spans extras deallocation.diagnostic deallocation.nativeDrop

end Miri.Input.EvalUnixNativeFdConstruction
