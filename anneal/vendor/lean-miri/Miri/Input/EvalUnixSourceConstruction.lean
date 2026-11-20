import Miri.Input.EvalUnixConstruction
import Miri.Input.EvalUnixFdConstruction
import Miri.Input.EvalUnixIoConstruction
import Miri.Input.EvalUnixNativeFdConstruction
import Miri.Input.EvalUnixLinuxConstruction
import Miri.Input.EvalUnixThreadTlsConstruction
import Miri.Input.EvalSocketStorage
import Miri.Input.CompilerGlobalBytes
import Miri.Input.CompilerWindowsConstants
import Miri.Input.CompilerLibcTypeLayouts
import Miri.Input.CompilerNamedFields
import Miri.Input.CompilerPrimitiveFacts
import Miri.Input.CompilerFrameMetadata
import Miri.Input.EvalPlaceConstruction
import Miri.Interpreter.GlobalByteMachine
import Miri.Interpreter.OsStrings
import Miri.Interpreter.PlaceDynamic
import Miri.Interpreter.PlaceMachine
import Miri.Interpreter.PointerPlaceMachine
import Miri.Interpreter.StdOnlyShims
import Miri.Interpreter.UnixForeign
import Miri.Concurrency.Thread

/-! Assemble source-built Unix environment and poll fields over the actual
EvalWorld machine. This is a component bundle, not a caller-supplied
`UnixForeign.Hooks`: the environment and poll policies are constructed here,
while file/readiness and native blocking-I/O effects remain separate typed
boundaries for their own source constructors. -/
namespace Miri.Input.EvalUnixSourceConstruction
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
abbrev Control Os R P H D Aff B Poll Instant System Native Profiler Raw Listener TcpStream Error :=
  ValidityMachine.Control (Stored Os R P H D Aff B Poll Instant System Native Profiler Raw Listener TcpStream Error)
abbrev FD H D O := Files.Ref (Files.Description H D O)

structure Components (Os R P H D Aff B Poll Instant System Native Profiler Raw Listener TcpStream Error : Type) where
  environment : UnixEnvironmentDispatch.Hooks
    (State Os R P H D Aff B Poll Instant System Native Profiler Raw Listener TcpStream Error)
    Os Error EnvVars.Kind
  poll : PollDispatch.Hooks
    (State Os R P H D Aff B Poll Instant System Native Profiler Raw Listener TcpStream Error)
    (FD H D (Other Raw Listener TcpStream Error)) EvalUnixFdConstruction.ArrayCursor

/-- Source-built entry-shim fields assembled from the environment/poll and
native FD constructors. Other platform subsystems remain separate components
until their source constructors are connected. This is deliberately not a
replacement for the full `UnixForeign.Hooks` dictionary. -/
structure DispatchComponents
    (Os R P H D Aff B Poll Instant System Native Profiler Raw Listener TcpStream Error
      Meta Path Place C ClockHost I : Type) where
  environmentAndPoll : Components Os R P H D Aff B Poll Instant System Native Profiler
    Raw Listener TcpStream Error
  nativeFd : EvalUnixNativeFdConstruction.Components Os R P H D Aff B Poll Instant
    System Native Profiler Raw Listener TcpStream Error Meta Path Place C ClockHost I
  threadTls : EvalUnixThreadTlsConstruction.Components
    (State Os R P H D Aff B Poll Instant System Native Profiler Raw Listener TcpStream Error)
    (MPlaceTy Provenance) B I
  linux : Option (EvalUnixLinuxConstruction.Components
    (State Os R P H D Aff B Poll Instant System Native Profiler Raw Listener TcpStream Error)
    Place H D (Other Raw Listener TcpStream Error) Error Meta Os B I)
  stdOnly : StdOnlyShims.Hooks Provenance
    (State Os R P H D Aff B Poll Instant System Native Profiler Raw Listener TcpStream Error)
    Place (MPlaceTy Provenance) B I

def connectDispatch
    (p : CompilerProviders.Prepared)
    (environmentAndPoll : Components Os R P H D Aff B Poll Instant System Native Profiler
      Raw Listener TcpStream Error)
    (nativeFd : EvalUnixNativeFdConstruction.Components Os R P H D Aff B Poll Instant
      System Native Profiler Raw Listener TcpStream Error Meta Path Place C ClockHost I)
    (threadTls : EvalUnixThreadTlsConstruction.Components
      (State Os R P H D Aff B Poll Instant System Native Profiler Raw Listener TcpStream Error)
      (MPlaceTy Provenance) B I)
    (linux : Option (EvalUnixLinuxConstruction.Components
      (State Os R P H D Aff B Poll Instant System Native Profiler Raw Listener TcpStream Error)
      Place H D (Other Raw Listener TcpStream Error) Error Meta Os B I))
    (stdOnly : StdOnlyShims.Hooks Provenance
      (State Os R P H D Aff B Poll Instant System Native Profiler Raw Listener TcpStream Error)
      Place (MPlaceTy Provenance) B I) : Except StepError
      (DispatchComponents Os R P H D Aff B Poll Instant System Native Profiler Raw Listener TcpStream
        Error Meta Path Place C ClockHost I) := do
  let target ← p.externStatics.targetFacts |>.mapError StepError.unsupported
  let communicate := environmentAndPoll.environment.env.process.communicate
  unless environmentAndPoll.environment.env.os == target.os &&
      environmentAndPoll.environment.env.targetEnv == target.env do
    throw (.invalidProgram "Unix dispatch target differs from prepared compiler target")
  unless environmentAndPoll.poll.os == target.os &&
      environmentAndPoll.poll.communicate == communicate do
    throw (.invalidProgram "Unix dispatch poll target/policy differs from environment")
  unless nativeFd.fd.file.fd.os == target.os &&
      nativeFd.fd.file.fd.communicate == communicate do
    throw (.invalidProgram "Unix dispatch native FD target/policy differs from environment")
  if let some linux := linux then
    unless (target.os == "linux" || target.os == "android") &&
        linux.linuxPlatform.signatures.foreign.os == target.os &&
        linux.linuxPlatform.signatures.foreign.family == .unix &&
        linux.linuxPlatform.fd.file.fd.os == target.os do
      throw (.invalidProgram "Unix dispatch Linux platform component differs from compiler target")
  let arch ← EvalArchitectureMachine.targetArch p.intrinsics
    |>.mapError StepError.unsupported
  unless stdOnly.foreign.family == .unix && stdOnly.foreign.os == target.os &&
      stdOnly.foreign.arch == arch && stdOnly.targetEnv == target.env do
    throw (.invalidProgram "Unix std-only shim target differs from prepared compiler target")
  pure ⟨environmentAndPoll,nativeFd,threadTls,linux,stdOnly⟩

/-- Build the single ordered Unix dispatcher from runtime-created fields.
Environment, FD/control/vector, poll and std-only arms run their source
implementations. Every not-yet-constructed source group has an exact
target-aware matcher and fails Unsupported only when that recognized name is
requested; names outside those groups continue through the outer source
resolver. -/
def dispatchers
    (p : CompilerProviders.Prepared)
    (components : DispatchComponents Os R P H D Aff B Poll Instant System Native Profiler
      Raw Listener TcpStream Error Meta Path Place C ClockHost I)
    (pollBudget : Nat) : Except StepError
      (UnixForeign.SourceDispatchers
        (State Os R P H D Aff B Poll Instant System Native Profiler Raw Listener TcpStream Error)) := do
  let environmentAndPoll := components.environmentAndPoll
  let nativeFd := components.nativeFd
  let environment := environmentAndPoll.environment
  let poll := environmentAndPoll.poll
  let os := environment.env.os
  let targetEnv := environment.env.targetEnv
  let communicate := environment.env.process.communicate
  let target ← p.externStatics.targetFacts |>.mapError StepError.unsupported
  let arch ← EvalArchitectureMachine.targetArch p.intrinsics |>.mapError StepError.unsupported
  unless target.families.contains "unix" && target.os == os && target.env == targetEnv &&
      nativeFd.fd.file.fd.os == target.os &&
      components.stdOnly.foreign.family == .unix && components.stdOnly.foreign.os == target.os &&
      components.stdOnly.foreign.arch == arch && components.stdOnly.targetEnv == target.env do
    throw (.invalidProgram "Unix source dispatcher components disagree with compiler target facts")
  unless poll.os == os && poll.communicate == communicate &&
      nativeFd.fd.file.fd.os == os && nativeFd.fd.file.fd.communicate == communicate &&
      (match components.linux with
        | none => true
        | some linux => linux.linuxPlatform.signatures.foreign.os == os &&
            linux.linuxPlatform.fd.file.fd.os == os) &&
      components.stdOnly.foreign.family == .unix && components.stdOnly.foreign.os == os &&
      components.stdOnly.targetEnv == targetEnv do
    throw (.invalidProgram "Unix source dispatcher components disagree on target or communication policy")
  let fd := {nativeFd.fd with pollAndUnblockZero := pure ()}
  let unavailable := UnixForeign.unavailableHandler os targetEnv
  let unavailableOptional := UnixForeign.unavailableOptional os targetEnv
  let control : UnixForeign.OptionalHandler
      (State Os R P H D Aff B Poll Instant System Native Profiler Raw Listener TcpStream Error) :=
    fun name abi args dest => UnixFdControlDispatch.emulate nativeFd.control name abi args dest
  let vector : UnixForeign.OptionalHandler
      (State Os R P H D Aff B Poll Instant System Native Profiler Raw Listener TcpStream Error) :=
    fun name abi args dest => UnixVectoredDispatch.emulate nativeFd.vector name abi args dest
  let validation : EStateM StepError
      (State Os R P H D Aff B Poll Instant System Native Profiler Raw Listener TcpStream Error) Unit := do
    unless environment.env.os == os && environment.env.process.communicate == communicate &&
        poll.os == os && poll.communicate == communicate && fd.file.fd.os == os &&
        fd.file.fd.communicate == communicate do
      throw (.invalidProgram "Unix source dispatcher runtime target changed after construction")
  let memory : UnixForeign.OptionalHandler
      (State Os R P H D Aff B Poll Instant System Native Profiler Raw Listener TcpStream Error) :=
    match components.linux with
    | some linux => fun name abi args dest =>
        UnixMemory.emulate linux.linuxPlatform.memory.memory name abi args dest
    | none => unavailableOptional .memory
  let linuxPlatform : UnixForeign.OptionalHandler
      (State Os R P H D Aff B Poll Instant System Native Profiler Raw Listener TcpStream Error) :=
    match components.linux with
    | some linux => fun name abi args dest =>
        LinuxForeign.emulate linux.linuxPlatform name abi args dest
    | none => unavailableOptional .linuxPlatform
  let androidPlatform : UnixForeign.OptionalHandler
      (State Os R P H D Aff B Poll Instant System Native Profiler Raw Listener TcpStream Error) :=
    match components.linux with
    | some linux => fun name abi args dest =>
        AndroidForeign.emulate linux.linuxPlatform name abi args dest
    | none => unavailableOptional .androidPlatform
  pure {
    os, communicate, validate := validation
    pollAndUnblockZero := poll.pollAndUnblockZero
    environment := UnixEnvironmentDispatch.dispatch environment
    fd := UnixFdDispatch.dispatch fd
    fdControl := control
    vector
    fs := unavailable .fs
    poll := PollDispatch.dispatch pollBudget poll
    pthread := unavailable .pthread
    socket := unavailable .socket
    memory
    thread := fun name abi args dest =>
      UnixThreadDispatch.emulate components.threadTls.thread name abi args dest
    tls := fun name abi args dest =>
      UnixTlsDispatch.emulate components.threadTls.tls name abi args dest
    affinity := unavailableOptional .affinity
    event := unavailableOptional .event
    linux := unavailableOptional .linux
    random := unavailableOptional .random
    time := unavailable .time
    linuxPlatform
    androidPlatform
    dynamic := unavailableOptional .dynamic
    macos := unavailableOptional .macos
    freebsd := unavailableOptional .freebsd
    solarish := unavailableOptional .solarish
    netbsd := unavailableOptional .netbsd
    stdOnly := StdOnlyShims.unix components.stdOnly }

/-- Replace only the Unix arm of a source-built common foreign dispatcher.
The same Core is checked against the one used while constructing StdOnly, so
callers cannot substitute a different family/target/allocation policy at the
last boundary. Other source foreign-item arms remain owned by the enclosing
portable/platform construction. -/
def bindDispatchers
    (p : CompilerProviders.Prepared)
    (components : DispatchComponents Os R P H D Aff B Poll Instant System Native Profiler
      Raw Listener TcpStream Error Meta Path Place C ClockHost I)
    (pollBudget : Nat)
    (base : ForeignItems.Hooks Provenance
      (State Os R P H D Aff B Poll Instant System Native Profiler Raw Listener TcpStream Error)
      Place (MPlaceTy Provenance) (Pointer (Option Provenance)) B I) :
    Except StepError (ForeignItems.Hooks Provenance
      (State Os R P H D Aff B Poll Instant System Native Profiler Raw Listener TcpStream Error)
      Place (MPlaceTy Provenance) (Pointer (Option Provenance)) B I) := do
  let dispatchers ← dispatchers p components pollBudget
  let source := components.stdOnly.foreign
  let core := base.toCore
  unless core.family == source.family && core.os == source.os && core.arch == source.arch &&
      core.maximumSize == source.maximumSize && core.noAllocShimSymbol == source.noAllocShimSymbol &&
      core.nativeEnabled == source.nativeEnabled do
    throw (.invalidProgram "Unix dispatcher and common source Core differ")
  pure (UnixForeign.bindSource dispatchers base)

/-- Construct the Unix environment and outer source poll from the same
compiler provider and current EvalWorld state. File memory and descriptor
ownership are built here from the narrow host-file/other-description effects;
`readinessRoute`, `deadline`, and native blocking I/O remain their separately
constructed source components. -/
def fromRuntime [DecidableEq MiriMemoryKind]
    (p : CompilerProviders.Prepared)
    (userRelevantCrates : Array Nat)
    (compatibilityBudget : Nat)
    (host : EvalHostRuntimeConstruction.OsHostEffects Os)
    (hostEffects : EvalHostRuntimeConstruction.EnvironmentHostEffects
      (Control Os R P H D Aff B Poll Instant System Native Profiler Raw Listener TcpStream Error))
    (hostConfig : EvalUnixConstruction.HostConfigEffects
      (State Os R P H D Aff B Poll Instant System Native Profiler Raw Listener TcpStream Error)
      Os Error)
    (ioHost : EvalUnixConstruction.IoHostEffects
      (State Os R P H D Aff B Poll Instant System Native Profiler Raw Listener TcpStream Error)
      Error)
    (memory : EvalHostRuntimeConstruction.EnvironmentMemory
      (Control Os R P H D Aff B Poll Instant System Native Profiler Raw Listener TcpStream Error)
      C Payload)
    (unitLayout : LocalLayout)
    (hostUsizeBits fileReferenceBudget watcherReferenceBudget : Nat)
    (resources : EvalUnixIoConstruction.FileResourceEffects
      (State Os R P H D Aff B Poll Instant System Native Profiler Raw Listener TcpStream Error)
      H D (Other Raw Listener TcpStream Error))
    (hostFiles : EvalUnixIoConstruction.HostFileEffects
      (State Os R P H D Aff B Poll Instant System Native Profiler Raw Listener TcpStream Error)
      H D (Other Raw Listener TcpStream Error) Error Metadata)
    (otherFiles : EvalUnixIoConstruction.OtherFileEffects
      (State Os R P H D Aff B Poll Instant System Native Profiler Raw Listener TcpStream Error)
      H D (Other Raw Listener TcpStream Error) Error)
    (readinessRoute : EvalUnixFdConstruction.ReadinessRoute
      (State Os R P H D Aff B Poll Instant System Native Profiler Raw Listener TcpStream Error))
    (deadline : DeadlineMachine.Hooks MiriMemoryKind
      (User Os R P H D Aff B Poll Instant System Native Profiler Raw Listener TcpStream Error)
      Instant System)
    (descriptor : PollMachine.DescriptorHooks (Other Raw Listener TcpStream Error))
    (communicate : Bool)
    (entryPollBudget iterationBudget : Nat)
    (io : BlockingIo.Hooks
      (State Os R P H D Aff B Poll Instant System Native Profiler Raw Listener TcpStream Error)
      (FD H D (Other Raw Listener TcpStream Error)) Poll HostEffect) :
    Except StepError (Components Os R P H D Aff B Poll Instant System Native Profiler
      Raw Listener TcpStream Error) := do
  let environment ← EvalUnixConstruction.environmentFromRuntime p userRelevantCrates
    compatibilityBudget host hostEffects hostConfig ioHost memory
  unless environment.env.process.communicate == communicate do
    throw (.invalidProgram "Unix environment and poll communication policies disagree")
  let files ← EvalUnixIoConstruction.filesFromSource p memory.access memory.pointers
    hostFiles otherFiles
  let registry := EvalUnixIoConstruction.fileRegistry
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
  let readinessRegistry := EvalUnixFdConstruction.readiness registry
    watcherReferenceBudget dropDescription
  let poll ← EvalUnixFdConstruction.pollDispatch p compatibilityBudget memory.choice
    memory.projection.place memory.projection memory.access unitLayout readinessRegistry files
    readinessRoute deadline descriptor environment.env.errors communicate
    entryPollBudget iterationBudget io
  pure ⟨environment,poll⟩

/-- Source-backed std-only fields for the Unix chain. The fallback foreign
dispatcher is supplied only at the final chain boundary; compiler layouts,
frame identity, physical accesses, target constants, byte-global allocation,
isolation policy, and thread-yield state are closed over their canonical
providers here. The Unix home-directory string conversion is retained as an
explicit host capability because the current StdOnlyShims interface is
String-valued. -/
def stdOnlyFromRuntime {MirBody : Type} [DecidableEq MiriMemoryKind]
    (p : CompilerProviders.Prepared)
    (userRelevantCrates : Array Nat)
    (accessConfig : PlaceMachine.AccessConfig MiriMemoryKind
      (User Os R P H D Aff B Poll Instant System Native Profiler Raw Listener TcpStream Error))
    (allocationConfig : PlaceMachine.AllocationConfig MiriMemoryKind
      (User Os R P H D Aff B Poll Instant System Native Profiler Raw Listener TcpStream Error))
    (compilerConfig : PlaceMachine.CompilerHooks MiriMemoryKind
      (User Os R P H D Aff B Poll Instant System Native Profiler Raw Listener TcpStream Error) C)
    (projection : PlaceProjectionHooks Provenance
      (State Os R P H D Aff B Poll Instant System Native Profiler Raw Listener TcpStream Error)
      C MachineHooks.FrameExtra)
    (access : ValidityMachine.Access MiriMemoryKind
      (Stored Os R P H D Aff B Poll Instant System Native Profiler Raw Listener TcpStream Error))
    (choice : C)
    (environment : UnixEnvironmentDispatch.Hooks
      (State Os R P H D Aff B Poll Instant System Native Profiler Raw Listener TcpStream Error)
      Os Error EnvVars.Kind)
    (globalBytes : CompilerGlobalBytes.Prepared)
    (functions : FunctionPointers.Hooks MiriMemoryKind
      (ValidityMachine.UserState
        (Stored Os R P H D Aff B Poll Instant System Native Profiler Raw Listener TcpStream Error))
      (Other Raw Listener TcpStream Error))
    (pageSize stackAddress stackSize : UInt64)
    (foreign : ForeignItems.Core Provenance
      (State Os R P H D Aff B Poll Instant System Native Profiler Raw Listener TcpStream Error)
      Place (MPlaceTy Provenance) (Pointer (Option Provenance)) MirBody I) :
    Except StepError (StdOnlyShims.Hooks Provenance
      (State Os R P H D Aff B Poll Instant System Native Profiler Raw Listener TcpStream Error)
      Place (MPlaceTy Provenance) MirBody I) := do
  let target ← p.externStatics.targetFacts |>.mapError StepError.unsupported
  let frame := CompilerFrameMetadata.hooks p.lifecycle.frames userRelevantCrates
  let place := PlaceMachine.placeHooks accessConfig allocationConfig compilerConfig
  let writeScalar : Scalar Provenance → MPlaceTy Provenance →
      EStateM StepError
        (State Os R P H D Aff B Poll Instant System Native Profiler Raw Listener TcpStream Error)
        Unit := fun scalar destination =>
    writePlaceImmediate place choice (.scalar scalar)
      (RuntimePlace.mk (.memory destination.mplace) destination.layout)
  let layout : String → EStateM StepError
      (State Os R P H D Aff B Poll Instant System Native Profiler Raw Listener TcpStream Error)
      LocalLayout := fun name => do
    if name == "usize" then
      match p.primitiveLayout "usize" with
      | .ok value => pure value
      | .error reason => throw (StepError.unsupported s!"compiler std-only layout `{name}`: {reason}")
    else if name == "unit_ptr_mut" then
      match p.primitiveLayout "unit_pointer_mut" with
      | .ok value => pure value
      | .error reason => throw (StepError.unsupported s!"compiler std-only layout `{name}`: {reason}")
    else
      match CompilerLibcTypeLayouts.layout p.runtime name with
      | .ok value => pure value
      | .error reason => throw (StepError.unsupported s!"compiler std-only libc layout `{name}`: {reason}")
  let projectNamed : MPlaceTy Provenance → String →
      EStateM StepError
        (State Os R P H D Aff B Poll Instant System Native Profiler Raw Listener TcpStream Error)
        (MPlaceTy Provenance) := fun parent name => do
    let index ← match CompilerNamedFields.fieldIndex p.runtime parent.layout name with
      | .ok index => pure index
      | .error error => throw error
    let projected ← PlaceDynamic.field projection choice
      (RuntimePlace.mk (.memory parent.mplace) parent.layout) index
    match projected.ref with
    | .memory memory => pure (MPlaceTy.mk memory projected.layout)
    | .local .. => throw (StepError.invalidProgram "std-only named field projection became a local")
  let homeDirectory : EStateM StepError
      (State Os R P H D Aff B Poll Instant System Native Profiler Raw Listener TcpStream Error)
      String := do
    let some path ← environment.env.homeDirectory |
      throw (StepError.invalidProgram "host home_dir returned None")
    let bytes := environment.env.strings.encodedBytes path
    match String.fromUTF8? bytes with
    | some value => pure value
    | none => throw (StepError.unsupported "host home directory is not UTF-8 representable by StdOnlyShims")
  let fields : StdOnlyShims.Hooks Provenance
      (State Os R P H D Aff B Poll Instant System Native Profiler Raw Listener TcpStream Error)
      Place (MPlaceTy Provenance) MirBody I := {
    foreign
    frameInStd := FrameMetadata.frameInStd frame
    targetEnv := target.env
    pageSize
    stackAddress
    stackSize
    layout
    dereference := fun operand expectedLayout => do
      unless expectedLayout.layout.isSized do
        throw (.invalidProgram "std-only pointer dereference requires a sized layout")
      let immediate ← ValidityMachine.readImmediate access operand
      let (scalar,metadata) ← match immediate.imm.toScalarAndMeta with
        | .ok value => pure value
        | .error error => throw (ScalarOps.immediateError error)
      let pointer ← match scalar.toPointer access.runtime.base with
        | .ok value => pure value
        | .error error => throw (ScalarOps.scalarError error)
      PointerPlaceMachine.withMetadata access pointer metadata expectedLayout false
    pointerOf := fun place => place.mplace.ptr
    writeUnsigned := fun value destination => do
      let scalar ← match Scalar.fromUInt (BitVec.ofNat 128 value.toNat)
          destination.layout.layout.size with
        | .ok scalar => pure scalar
        | .error error => throw (ScalarOps.scalarError error)
      writeScalar scalar destination
    writeUninit := fun destination =>
      PlaceMachine.writeMemory accessConfig (fun _ => false) .uninit destination
    projectNamed
    readU32 := environment.env.readU32
    checkNoIsolation := environment.env.checkNoIsolation
    homeDirectory
    writePath := fun (path : String) (pointer : Pointer (Option Provenance)) (length : UInt64) => do
      let path ← match environment.env.strings.fromUtf8 path.toUTF8 with
        | .ok path => pure path
        | .error error => throw error
      return (← OsStrings.writePath environment.env.strings path pointer length).1
    libcValue := environment.env.libcScalar
    windowsValue := fun name =>
      match CompilerWindowsConstants.scalar p.namedConstants "c" name with
      | .ok value => pure value
      | .error reason => throw (StepError.unsupported reason)
    writeScalar
    allocateStringDedup := fun value => do
      let place ← GlobalByteMachine.string functions access
        (CompilerGlobalBytes.strLayout p.runtime globalBytes) value
      pure place.mplace.ptr
    windowsAbi := fun name => CompilerNamedShimAbi.query p.namedAbi name
    yieldActiveThread := do
      modify fun state => {state with machine := {state.machine with
        threads := Miri.Concurrency.ThreadManager.yield state.machine.threads}}
    setLastError := fun name => IoError.setLastError environment.env.errors (.windows name)}
  pure fields

end Miri.Input.EvalUnixSourceConstruction
