import Miri.Input.EvalWindowsCallDispatchConstruction
import Miri.Input.EvalUnixIoConstruction
import Miri.Input.EvalSourceHostEffects
import Miri.Input.EvalUnixNativeFdConstruction
import Miri.Input.EvalSocketStorage
import Miri.Input.CompilerNamedConstants
import Miri.Interpreter.RawMemoryMachine
import Miri.Interpreter.UnixOpen

/-! Raw host-effect wiring for the Windows file family. WindowsFiles owns the
Win32 flag parser; this module supplies the same-world byte access, descriptor
ownership, shared open-file-or-directory policy, and genuine host file leaves.
UnixOpen's embedded FD dictionary is only used by its Unix open-path entrypoint,
which WindowsFiles never calls. -/
namespace Miri.Input.EvalWindowsIoSourceConstruction
open Miri.ABI Miri.Memory Miri.MIR Miri.Interpreter

abbrev Other Raw Listener TcpStream Error :=
  EvalSocketStorage.Other Raw Listener TcpStream Error
abbrev Host Poll Instant System H D O Native Profiler :=
  HostRuntime.Storage Poll Instant System H D O Native Profiler
abbrev Payload Os R H D Aff B Poll Instant System Native Profiler Raw Listener TcpStream Error :=
  EvalWindowsFileConstruction.Payload Os R EvalSyncPayload.Payload H D
    (Other Raw Listener TcpStream Error) Aff B
    (Host Poll Instant System H D (Other Raw Listener TcpStream Error) Native Profiler)
abbrev State Os R H D Aff B Poll Instant System Native Profiler Raw Listener TcpStream Error :=
  EvalWindowsFileConstruction.State Os R
    EvalSyncPayload.Payload
    H D (Other Raw Listener TcpStream Error) Aff B
    (Host Poll Instant System H D (Other Raw Listener TcpStream Error) Native Profiler)
abbrev FD H D O := Files.Ref (Files.Description H D O)
abbrev M S A := EStateM StepError S A

set_option autoImplicit false in
structure IoComponents
    (Os R H D Aff B Poll Instant System Native Profiler Raw Listener TcpStream Error
      C Meta Path : Type) where
  fileRegistry : Files.Hooks
    (State Os R H D Aff B Poll Instant System Native Profiler Raw Listener TcpStream Error)
    H D (Other Raw Listener TcpStream Error) Error Meta
  readiness : ReadinessMachine.Hooks MiriMemoryKind
    (ThreadStacks.Storage (Payload Os R H D Aff B Poll Instant System Native Profiler Raw Listener TcpStream Error))
    H D (Other Raw Listener TcpStream Error)
  sharedOpen : UnixOpen.Hooks
    (State Os R H D Aff B Poll Instant System Native Profiler Raw Listener TcpStream Error)
    H D (Other Raw Listener TcpStream Error) Error Meta Path
  prepareDirectory : D → Path → M
    (State Os R H D Aff B Poll Instant System Native Profiler Raw Listener TcpStream Error) D
  otherMetadata : Other Raw Listener TcpStream Error → M
    (State Os R H D Aff B Poll Instant System Native Profiler Raw Listener TcpStream Error)
    (Sum (Except (IoError.HostError Error) Meta) String)
  hostFiles : EvalWindowsFileConstruction.HostEffects Os
    (State Os R H D Aff B Poll Instant System Native Profiler Raw Listener TcpStream Error)
    Path H D (Other Raw Listener TcpStream Error) Meta System Error
  checkPointerAccess : Pointer (Option Provenance) → Size → M
    (State Os R H D Aff B Poll Instant System Native Profiler Raw Listener TcpStream Error) Unit

private def unsupported (what : String) : M S A :=
  throw (.unsupported s!"Windows source IO: {what} is unavailable")

/-- Build Windows file IO over the live Main access configuration and the raw
host residuals. Path-to-OS conversion is an explicit representation codec,
separate from optional filesystem syscalls. -/
def fromSource [DecidableEq MiriMemoryKind]
    (p : CompilerProviders.Prepared)
    (sourceSeed : EvalWindowsCallDispatchConstruction.SourceSeed Os R H D Aff B Poll Instant
      System Native Profiler Raw Listener TcpStream Error C)
    (main : MainMachine.Hooks
      (Payload Os R H D Aff B Poll Instant System Native Profiler Raw Listener TcpStream Error)
      C (Other Raw Listener TcpStream Error) ABI.ExternAbi (FnAbi TyId) (ArgAbi TyId) Aff ProgramExitPoll)
    (errors : IoError.Hooks
      (State Os R H D Aff B Poll Instant System Native Profiler Raw Listener TcpStream Error) Error)
    (openHost : EvalUnixNativeFdConstruction.OpenHostEffects
      (State Os R H D Aff B Poll Instant System Native Profiler Raw Listener TcpStream Error)
      H D Error Meta Path Os)
    (hostFiles : EvalUnixIoConstruction.HostFileEffects
      (State Os R H D Aff B Poll Instant System Native Profiler Raw Listener TcpStream Error)
      H D (Other Raw Listener TcpStream Error) Error Meta)
    (resources : EvalUnixIoConstruction.FileResourceEffects
      (State Os R H D Aff B Poll Instant System Native Profiler Raw Listener TcpStream Error)
      H D (Other Raw Listener TcpStream Error))
    (_locks : EvalUnixIoConstruction.FileLockEffects
      (State Os R H D Aff B Poll Instant System Native Profiler Raw Listener TcpStream Error) H Error)
    (positional : EvalUnixNativeFdConstruction.OtherPositionalEffects
      (State Os R H D Aff B Poll Instant System Native Profiler Raw Listener TcpStream Error)
      H D (Other Raw Listener TcpStream Error) Error)
    (filesystem : Option (EvalSourceHostEffects.Filesystem Os
      (State Os R H D Aff B Poll Instant System Native Profiler Raw Listener TcpStream Error)
      H D (Other Raw Listener TcpStream Error) Path Meta System Error R))
    (resourcesBudget watcherBudget hostUsizeBits : Nat)
    (targetIsizeMax hostIsizeMax : UInt64)
    (pathToOs : Path → Os)
    (arithmetic : PointerArithmetic)
    :
    Except StepError (IoComponents Os R H D Aff B Poll Instant System Native Profiler
      Raw Listener TcpStream Error C Meta Path) := do
  let _ := sourceSeed
  let hostRead := hostFiles.hostRead
  let hostWrite := hostFiles.hostWrite
  let hostSeek := hostFiles.hostSeek
  let hostMetadata := hostFiles.hostMetadata
  let permissionDenied := hostFiles.permissionDenied
  let other : EvalUnixIoConstruction.OtherFileEffects
      (State Os R H D Aff B Poll Instant System Native Profiler Raw Listener TcpStream Error)
      H D (Other Raw Listener TcpStream Error) Error := {
    read := fun _ _ _ _ _ => unsupported "Other-description read"
    write := fun _ _ _ _ _ => unsupported "Other-description write"
    shortOperations := fun _ => true
    readiness := fun _ => unsupported "Other-description readiness"
    hasReadinessWatched := fun _ => true
    isTerminal := fun _ _ => unsupported "Other-description terminal query" }
  let files : Files.Hooks
      (State Os R H D Aff B Poll Instant System Native Profiler Raw Listener TcpStream Error)
      H D (Other Raw Listener TcpStream Error) Error Meta := {
    family := .windows
    hostRead, hostWrite, hostFlushStdout := hostFiles.flushStdout, hostSeek
    hostMetadata := fun description => match filesystem with
      | none => unsupported "filesystem metadata query"
      | some _ => hostMetadata description
    hostIsTerminal := hostFiles.hostIsTerminal
    readBytes := fun pointer size => RawMemoryMachine.readBytes main.access arithmetic pointer size.bytes
    writeBytes := RawMemoryMachine.writeBytes main.access arithmetic
    permissionDenied
    otherRead := other.read, otherWrite := other.write
    otherShortOperations := other.shortOperations
    otherReadiness := other.readiness
    otherHasReadinessWatched := other.hasReadinessWatched
    otherIsTerminal := other.isTerminal }
  let fileRegistry : FileMachine.Hooks MiriMemoryKind
      (ThreadStacks.Storage (Payload Os R H D Aff B Poll Instant System Native Profiler Raw Listener TcpStream Error))
      H D (Other Raw Listener TcpStream Error) := {
    table := fun u => u.user.payload.payload.runtime.descriptors
    setTable := fun descriptors u =>
      let control := u.user.payload
      let world := control.payload
      let world := {world with runtime := {world.runtime with descriptors}}
      {u with user := {u.user with payload := {control with payload := world}}}
    ownership := fun u => u.user.payload.payload.runtime.ownership
    setOwnership := fun ownership u =>
      let control := u.user.payload
      let world := control.payload
      let world := {world with runtime := {world.runtime with ownership}}
      {u with user := {u.user with payload := {control with payload := world}}}
    hostUsizeBits := hostUsizeBits
    referenceBudget := resourcesBudget
    onLastDrop := fun description => do
      match description with
      | .stdin | .stdout | .stderr | .nullOutput => pure ()
      | .file handle _ _ => resources.dropFile handle
      | .directory handle => resources.dropDirectory handle
      | .other value => resources.dropOther value }
  let dropRef := fun (reference : FD H D (Other Raw Listener TcpStream Error)) => do
    match reference.value with
    | .stdin | .stdout | .stderr | .nullOutput => pure ()
    | .file handle _ _ => resources.dropFile handle
    | .directory handle => resources.dropDirectory handle
    | .other value => resources.dropOther value
  let readiness : ReadinessMachine.Hooks MiriMemoryKind
      (ThreadStacks.Storage (Payload Os R H D Aff B Poll Instant System Native Profiler Raw Listener TcpStream Error))
      H D (Other Raw Listener TcpStream Error) := {
    files := fileRegistry
    registry := fun u => u.user.payload.payload.host.readiness
    setRegistry := fun registry u =>
      let control := u.user.payload
      let world := control.payload
      let world := {world with host := {world.host with readiness := registry}}
      {u with user := {u.user with payload := {control with payload := world}}}
    watcherReferenceBudget := watcherBudget
    onLastDrop := dropRef }
  let fd : UnixFd.Hooks
      (State Os R H D Aff B Poll Instant System Native Profiler Raw Listener TcpStream Error)
      H D (Other Raw Listener TcpStream Error) Error Meta := {
    files, errors, os := "windows", communicate := false, shortFdOperations := false
    targetIsizeMax, hostIsizeMax
    table := unsupported "Unix FD table operation"
    putTable := fun _ => unsupported "Unix FD table mutation"
    newReference := fun _ => unsupported "Unix FD reference creation"
    cloneRef := fun _ => unsupported "Unix FD reference clone"
    dropRef := fun _ => unsupported "Unix FD reference drop"
    asUnix := fun _ => unsupported "Unix FD cast"
    removeFileNumInterests := fun _ _ => unsupported "Unix readiness interest removal"
    checkAccess := fun _ _ => unsupported "Unix FD access check"
    randomShort := unsupported "Unix short read selection"
    writeInt := fun _ _ => unsupported "Unix FD integer write"
    otherPositionalRead := positional.read
    otherPositionalWrite := positional.write }
  let sharedOpen : UnixOpen.Hooks
      (State Os R H D Aff B Poll Instant System Native Profiler Raw Listener TcpStream Error)
      H D (Other Raw Listener TcpStream Error) Error Meta Path := {
    fd, hostWindows := true
    flag := fun flag => do
      let name := match flag with
        | .readonly => "O_RDONLY" | .writeonly => "O_WRONLY" | .readwrite => "O_RDWR"
        | .accessMode => "O_ACCMODE" | .largefile => "O_LARGEFILE" | .tmpfile => "O_TMPFILE"
        | .directory => "O_DIRECTORY" | .append => "O_APPEND" | .trunc => "O_TRUNC"
        | .create => "O_CREAT" | .exclusive => "O_EXCL" | .cloexec => "O_CLOEXEC"
        | .nofollow => "O_NOFOLLOW" | .atCwd => "AT_FDCWD"
      match (CompilerNamedConstants.scalar p.namedConstants name :
          Except String (Scalar Provenance)) with
      | .ok scalar => match scalar.toUInt32 with
        | .ok value => pure value
        | .error error => throw (ScalarOps.scalarError error)
      | .error error => throw (StepError.unsupported s!"Windows shared-open flag {name}: {error}")
    hostCustomFlag := openHost.hostCustomFlag
    readMode := fun _ => unsupported "Unix variadic open mode"
    isolationReject := fun _ => pure false
    procAbsolute := openHost.procAbsolute
    diagnoseProc := openHost.diagnoseProc
    isAbsolute := openHost.isAbsolute, isEmpty := openHost.isEmpty, isDot := openHost.isDot
    emptyPath := openHost.emptyPath, openFile := openHost.openFile
    openDirectoryAsFile := openHost.openDirectoryAsFile, metadata := openHost.metadata
    asDirectory := openHost.asDirectory, dropFile := resources.dropFile
    dropDirectory := resources.dropDirectory, permissionDenied := errors.hostFromKind .PermissionDenied
    hostUsizeBits }
  let target ← p.externStatics.targetFacts |>.mapError StepError.unsupported
  unless target.os == "windows" || target.families.contains "windows" do
    throw (.invalidProgram s!"Windows IO construction requested for `{target.os}`")
  let hostWindowsFiles : EvalWindowsFileConstruction.HostEffects Os
      (State Os R H D Aff B Poll Instant System Native Profiler Raw Listener TcpStream Error)
      Path H D (Other Raw Listener TcpStream Error) Meta System Error := {
    pathFromOs := openHost.pathFromOs, osFromPath := pathToOs
    pathExists := fun path => do
      match filesystem with
      | none => unsupported "filesystem path-existence query"
      | some fs => return (← fs.effects.pathMetadata none path true).isOk
    absolute := filesystem.bind (·.absolute)
    length := fun metadata => (filesystem.map (fun fs => fs.effects.length metadata)).getD 0
    fileType := fun metadata => (filesystem.map (fun fs => fs.effects.fileType metadata)).getD .other
    time := fun metadata field => match filesystem with
      | none => unsupported "filesystem metadata time query"
      | some fs => fs.effects.time metadata field
    fileLength := fun handle => match filesystem with
      | none => unsupported "filesystem file-length query"
      | some fs => fs.effects.fileLength handle
    setLength := fun handle size => match filesystem with
      | none => unsupported "filesystem file resize"
      | some fs => fs.effects.setLength handle size
    syncAll := fun handle => match filesystem with
      | none => unsupported "filesystem file synchronization"
      | some fs => fs.effects.sync handle false
    rename := fun source target => match filesystem with
      | none => unsupported "filesystem rename"
      | some fs => fs.effects.rename source target
    removeFile := fun path => match filesystem with
      | none => unsupported "filesystem file removal"
      | some fs => fs.effects.removeFile path }
  let checkPointerAccess := fun pointer size => do
    let _ ← RawMemoryMachine.reference main.access arithmetic false pointer size
    pure ()
  pure {
    fileRegistry := files
    readiness := readiness
    sharedOpen := sharedOpen
    prepareDirectory := fun directory _ => pure directory
    otherMetadata := fun _ => throw (.unsupported "Windows metadata for Other descriptions")
    hostFiles := hostWindowsFiles
    checkPointerAccess := checkPointerAccess }

/-- Adapt the raw source-runner host effects, whose state is the canonical
EvalCore inner state, into the outer Main state used by Windows dispatch. -/
def fromInnerSource [DecidableEq MiriMemoryKind]
    (p : CompilerProviders.Prepared)
    (sourceSeed : EvalWindowsCallDispatchConstruction.SourceSeed Os R H D Aff B Poll Instant
      System Native Profiler Raw Listener TcpStream Error C)
    (main : MainMachine.Hooks
      (Payload Os R H D Aff B Poll Instant System Native Profiler Raw Listener TcpStream Error)
      C (Other Raw Listener TcpStream Error) ABI.ExternAbi (FnAbi TyId) (ArgAbi TyId) Aff ProgramExitPoll)
    (errors : IoError.Hooks
      (State Os R H D Aff B Poll Instant System Native Profiler Raw Listener TcpStream Error) Error)
    (openHost : EvalUnixNativeFdConstruction.OpenHostEffects
      (EvalSocketStorage.State Os R EvalSyncPayload.Payload H D Aff B Poll Instant System Native Profiler Raw Listener TcpStream Error)
      H D Error Meta Path Os)
    (hostFiles : EvalUnixIoConstruction.HostFileEffects
      (EvalSocketStorage.State Os R EvalSyncPayload.Payload H D Aff B Poll Instant System Native Profiler Raw Listener TcpStream Error)
      H D (Other Raw Listener TcpStream Error) Error Meta)
    (resources : EvalUnixIoConstruction.FileResourceEffects
      (EvalSocketStorage.State Os R EvalSyncPayload.Payload H D Aff B Poll Instant System Native Profiler Raw Listener TcpStream Error)
      H D (Other Raw Listener TcpStream Error))
    (locks : EvalUnixIoConstruction.FileLockEffects
      (EvalSocketStorage.State Os R EvalSyncPayload.Payload H D Aff B Poll Instant System Native Profiler Raw Listener TcpStream Error) H Error)
    (positional : EvalUnixNativeFdConstruction.OtherPositionalEffects
      (EvalSocketStorage.State Os R EvalSyncPayload.Payload H D Aff B Poll Instant System Native Profiler Raw Listener TcpStream Error)
      H D (Other Raw Listener TcpStream Error) Error)
    (filesystem : Option (EvalSourceHostEffects.Filesystem Os
      (EvalSocketStorage.State Os R EvalSyncPayload.Payload H D Aff B Poll Instant System Native Profiler Raw Listener TcpStream Error)
      H D (Other Raw Listener TcpStream Error) Path Meta System Error R))
    (resourcesBudget watcherBudget hostUsizeBits : Nat)
    (targetIsizeMax hostIsizeMax : UInt64) (pathToOs : Path → Os)
    (arithmetic : PointerArithmetic) : Except StepError (IoComponents Os R H D Aff B Poll Instant
      System Native Profiler Raw Listener TcpStream Error C Meta Path) := do
  let adapt := @ExecutionStateTransport.action MiriMemoryKind
    (EvalSocketStorage.World Os R EvalSyncPayload.Payload H D
      Aff B Poll Instant System Native Profiler Raw Listener TcpStream Error)
  let inward := @ExecutionStateTransport.reverseAction MiriMemoryKind
    (EvalSocketStorage.World Os R EvalSyncPayload.Payload H D
      Aff B Poll Instant System Native Profiler Raw Listener TcpStream Error)
  let openHost : EvalUnixNativeFdConstruction.OpenHostEffects
      (State Os R H D Aff B Poll Instant System Native Profiler Raw Listener TcpStream Error)
      H D Error Meta Path Os := {
    pathFromOs := openHost.pathFromOs, isAbsolute := openHost.isAbsolute
    isEmpty := openHost.isEmpty, isDot := openHost.isDot, emptyPath := openHost.emptyPath
    procAbsolute := fun path => adapt (openHost.procAbsolute path)
    diagnoseProc := adapt openHost.diagnoseProc
    hostCustomFlag := fun flag => adapt (openHost.hostCustomFlag flag)
    openFile := fun dir path options => adapt (openHost.openFile dir path options)
    openDirectoryAsFile := fun dir path options => adapt (openHost.openDirectoryAsFile dir path options)
    metadata := fun handle => adapt (openHost.metadata handle)
    asDirectory := fun handle => adapt (openHost.asDirectory handle) }
  let hostFiles : EvalUnixIoConstruction.HostFileEffects
      (State Os R H D Aff B Poll Instant System Native Profiler Raw Listener TcpStream Error)
      H D (Other Raw Listener TcpStream Error) Error Meta := {
    hostRead := fun description bytes => adapt (hostFiles.hostRead description bytes)
    hostWrite := fun description bytes => adapt (hostFiles.hostWrite description bytes)
    flushStdout := adapt hostFiles.flushStdout
    hostSeek := fun handle seek => adapt (hostFiles.hostSeek handle seek)
    hostMetadata := fun description => adapt (hostFiles.hostMetadata description)
    hostIsTerminal := fun description => adapt (hostFiles.hostIsTerminal description)
    permissionDenied := adapt hostFiles.permissionDenied }
  let resources : EvalUnixIoConstruction.FileResourceEffects
      (State Os R H D Aff B Poll Instant System Native Profiler Raw Listener TcpStream Error)
      H D (Other Raw Listener TcpStream Error) := {
    dropFile := fun handle => adapt (resources.dropFile handle)
    dropDirectory := fun handle => adapt (resources.dropDirectory handle)
    dropOther := fun value => adapt (resources.dropOther value) }
  let _locks : EvalUnixIoConstruction.FileLockEffects
      (State Os R H D Aff B Poll Instant System Native Profiler Raw Listener TcpStream Error) H Error := {
    tryLock := fun handle exclusive => adapt (locks.tryLock handle exclusive)
    unlock := fun handle => adapt (locks.unlock handle) }
  let positional : EvalUnixNativeFdConstruction.OtherPositionalEffects
      (State Os R H D Aff B Poll Instant System Native Profiler Raw Listener TcpStream Error)
      H D (Other Raw Listener TcpStream Error) Error := {
    read := fun reference offset pointer count finish =>
      let finishOuter := finish
      let finishInner : Files.Finish
          (EvalSocketStorage.State Os R EvalSyncPayload.Payload H D Aff B Poll Instant System Native Profiler Raw Listener TcpStream Error) Error :=
        { capture := finishOuter.capture, body := fun result => inward (finishOuter.body result) }
      adapt (positional.read reference offset pointer count finishInner)
    write := fun reference offset pointer count finish =>
      let finishOuter := finish
      let finishInner : Files.Finish
          (EvalSocketStorage.State Os R EvalSyncPayload.Payload H D Aff B Poll Instant System Native Profiler Raw Listener TcpStream Error) Error :=
        { capture := finishOuter.capture, body := fun result => inward (finishOuter.body result) }
      adapt (positional.write reference offset pointer count finishInner) }
  let filesystem : Option (EvalSourceHostEffects.Filesystem Os
      (State Os R H D Aff B Poll Instant System Native Profiler Raw Listener TcpStream Error)
      H D (Other Raw Listener TcpStream Error) Path Meta System Error R) :=
    filesystem.map fun (fs : EvalSourceHostEffects.Filesystem Os
        (EvalSocketStorage.State Os R EvalSyncPayload.Payload H D Aff B Poll Instant System Native Profiler Raw Listener TcpStream Error)
        H D (Other Raw Listener TcpStream Error) Path Meta System Error R) => Id.run do
    let effects : EvalUnixFsConstruction.HostEffects
        (State Os R H D Aff B Poll Instant System Native Profiler Raw Listener TcpStream Error)
        H D (Other Raw Listener TcpStream Error) Path Meta System Error R fs.Entry := {
      fs.effects with
      procAbsolute := fun path => adapt (fs.effects.procAbsolute path)
      currentExe := adapt fs.effects.currentExe
      removeFile := fun path => adapt (fs.effects.removeFile path)
      removeDirectory := fun path => adapt (fs.effects.removeDirectory path)
      symlinkDirectory := fun path => adapt (fs.effects.symlinkDirectory path)
      linkTargetDirectory := fun left right => adapt (fs.effects.linkTargetDirectory left right)
      createSymlink := fun left right isDir => adapt (fs.effects.createSymlink left right isDir)
      hardLink := fun left right => adapt (fs.effects.hardLink left right)
      setPathPermissions := fun path mode => adapt (fs.effects.setPathPermissions path mode)
      rename := fun left right => adapt (fs.effects.rename left right)
      mkdir := fun path mode => adapt (fs.effects.mkdir path mode)
      readLink := fun path => adapt (fs.effects.readLink path)
      canonicalize := fun path => adapt (fs.effects.canonicalize path)
      pathMetadata := fun dir path follow => adapt (fs.effects.pathMetadata dir path follow)
      time := fun metadata field => adapt (fs.effects.time metadata field)
      sinceEpoch := fun time => adapt (fs.effects.sinceEpoch time)
      readDir := fun path => adapt (fs.effects.readDir path)
      openDirectory := fun path => adapt (fs.effects.openDirectory path)
      dropReadDir := fun directory => adapt (fs.effects.dropReadDir directory)
      nextEntry := fun directory => adapt (fs.effects.nextEntry directory)
      entryType := fun entry => adapt (fs.effects.entryType entry)
      setLength := fun handle size => adapt (fs.effects.setLength handle size)
      fileLength := fun handle => adapt (fs.effects.fileLength handle)
      setFilePermissions := fun handle mode => adapt (fs.effects.setFilePermissions handle mode)
      sync := fun handle dataOnly => adapt (fs.effects.sync handle dataOnly)
      isTty := fun reference output => adapt (fs.effects.isTty reference output)
      systemNow := adapt fs.effects.systemNow
      sinceEpochCheckedAdd := fun duration => adapt (fs.effects.sinceEpochCheckedAdd duration)
      setFileTimes := fun handle accessed modified => adapt (fs.effects.setFileTimes handle accessed modified)
      setPathTimes := fun path follow accessed modified => adapt (fs.effects.setPathTimes path follow accessed modified)
      openExclusive := fun path opts => adapt (fs.effects.openExclusive path opts) }
    let absolute := fs.absolute.map fun operation path => adapt (operation path)
    return (⟨fs.Entry, fs.pathFromOs, fs.osFromPath, effects, absolute⟩ :
      EvalSourceHostEffects.Filesystem Os
        (State Os R H D Aff B Poll Instant System Native Profiler Raw Listener TcpStream Error)
        H D (Other Raw Listener TcpStream Error) Path Meta System Error R)
  fromSource p sourceSeed main errors openHost hostFiles resources _locks positional filesystem
    resourcesBudget watcherBudget hostUsizeBits targetIsizeMax hostIsizeMax pathToOs arithmetic

end Miri.Input.EvalWindowsIoSourceConstruction
