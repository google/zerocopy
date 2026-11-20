import Miri.Input.CompilerCallConstruction
import Miri.Input.CompilerForeignSymbols
import Miri.Input.CompilerNamedFields
import Miri.Input.CompilerNamedShimAbi
import Miri.Input.CompilerProviders
import Miri.Input.CompilerWindowsConstants
import Miri.Input.CompilerWindowsTypeLayouts
import Miri.Input.EvalCoreMachine
import Miri.Input.EvalWindowsEnvironmentDispatchConstruction
import Miri.Interpreter.MainMachine
import Miri.Interpreter.PointerPlaceMachine
import Miri.Interpreter.WindowsFileMachine
import Miri.Interpreter.WindowsFileDispatch

/-! Canonical source construction for the Windows file/handle dispatch. It
reuses the source Files/Readiness tables and actual Main memory; only host path
and host file operations remain inputs. -/
namespace Miri.Input.EvalWindowsFileConstruction
open Miri.ABI Miri.Memory Miri.MIR Miri.Interpreter

abbrev Payload Os R P H D O Aff B Host :=
  ValidityMachine.UserState (EvalCoreMachine.World Os R P H D O Aff B Host)
abbrev State Os R P H D O Aff B Host :=
  MainMachine.State (Payload Os R P H D O Aff B Host)
abbrev Ref H D O := WindowsFileMachine.Ref H D O
abbrev M S A := EStateM StepError S A

set_option autoImplicit false in
structure HostEffects (Os S Path H D O HM Time E : Type) where
  pathFromOs : Os → Path
  osFromPath : Path → Os
  pathExists : Path → M S Bool
  absolute : Option (Path → M S (Except (IoError.HostError E) Path))
  length : HM → UInt64
  fileType : HM → UnixFsMetadata.FileType
  time : HM → UnixFsMetadata.TimeField → M S (Except (IoError.HostError E) Time)
  fileLength : H → M S (Except (IoError.HostError E) UInt64)
  setLength : H → UInt64 → M S (Except (IoError.HostError E) Unit)
  syncAll : H → M S (Except (IoError.HostError E) Unit)
  rename : Path → Path → M S (Except (IoError.HostError E) Unit)
  removeFile : Path → M S (Except (IoError.HostError E) Unit)

private def lift (value : Except StepError A) : M S A :=
  match value with | .ok result => pure result | .error error => throw error

private def namedLayout (p : CompilerProviders.Prepared) (name : String) :
    M S (LocalLayout) := do
  match CompilerWindowsTypeLayouts.layout p.runtime name with
  | .ok value => pure ⟨value.ty,value.layout⟩
  | .error reason => throw (.unsupported s!"compiler Windows layout `{name}`: {reason}")

private def field (p : CompilerProviders.Prepared)
    (projection : PlaceProjectionHooks Provenance S C MachineHooks.FrameExtra)
    (choice : C) (parent : MPlaceTy Provenance) (name : String) : M S (MPlaceTy Provenance) := do
  let index ← match CompilerNamedFields.fieldIndex p.runtime parent.layout name with
    | .ok index => pure index
    | .error error => throw error
  let projected ← PlaceDynamic.field projection choice
    ⟨.memory parent.mplace,parent.layout⟩ index
  match projected.ref with
  | .memory memory => pure ⟨memory,projected.layout⟩
  | .local .. => throw (.invalidProgram "Windows file field projection became local")

/-- Assemble all guest-memory, ABI and descriptor behavior for Windows files
over one initialized Main state. `files`, `readiness`, and `sharedOpen` are the
canonical source components from that same world; they are not guest hook
facades. Host filesystem observations stay in `host`. -/
def fromSource [DecidableEq MiriMemoryKind]
    {Os R P H D O Aff B Host C Error HM Path Instant Time Zone Timestamp : Type}
    (p : CompilerProviders.Prepared)
    (main : MainMachine.Hooks (Payload Os R P H D O Aff B Host) C O ABI.ExternAbi
      (FnAbi TyId) (ArgAbi TyId) Aff ProgramExitPoll)
    (environment : WindowsEnvironmentDispatch.Hooks
      (State Os R P H D O Aff B Host) Os Error EnvVars.Kind)
    (files : Files.Hooks (State Os R P H D O Aff B Host) H D O Error HM)
    (readiness : ReadinessMachine.Hooks MiriMemoryKind
      (ThreadStacks.Storage (Payload Os R P H D O Aff B Host)) H D O)
    (sharedOpen : UnixOpen.Hooks (State Os R P H D O Aff B Host) H D O Error HM Path)
    (prepareDirectory : D → Path → M (State Os R P H D O Aff B Host) D)
    (otherMetadata : O → M (State Os R P H D O Aff B Host)
      (Sum (Except (IoError.HostError Error) HM) String))
    (timeHooks : TimeShims.Hooks (State Os R P H D O Aff B Host) Instant Time Zone Timestamp)
    (host : HostEffects Os (State Os R P H D O Aff B Host) Path H D O HM Time Error)
    (place : PlaceHooks Provenance (State Os R P H D O Aff B Host)
      C MachineHooks.FrameExtra)
    (checkPointerAccess : Pointer (Option Provenance) → Size →
      M (State Os R P H D O Aff B Host) Unit)
    (choice : C) (compatibilityBudget : Nat)
    (projection : PlaceProjectionHooks Provenance
      (State Os R P H D O Aff B Host) C MachineHooks.FrameExtra)
    (threadError : Concurrency.ThreadError → StepError) :
    Except StepError (WindowsFileDispatch.Hooks
      (State Os R P H D O Aff B Host) (Ref H D O) H D Path HM Time Error EnvVars.Kind) := do
  let target ← p.externStatics.targetFacts |>.mapError StepError.unsupported
  unless target.os == "windows" || target.families.contains "windows" do
    throw (.invalidProgram s!"Windows files requested on `{target.os}`")
  unless files.family == .windows && environment.env.env.family == .windows &&
      environment.env.process.family == .windows do
    throw (.invalidProgram "Windows file components have mismatched family")
  unless environment.env.strings.targetWindows do
    throw (.invalidProgram "Windows file string codec has a non-Windows target")
  unless timeHooks.family == .windows && timeHooks.os == "windows" do
    throw (.invalidProgram "Windows file time hooks have a mismatched target")
  let strings := environment.env.strings
  let pathStrings : OsStrings.Hooks Provenance
      (State Os R P H D O Aff B Host) Path EnvVars.Kind := {
    hostWindows := strings.hostWindows
    hostUnix := strings.hostUnix
    targetWindows := strings.targetWindows
    fromUnixBytes := fun bytes => host.pathFromOs (strings.fromUnixBytes bytes)
    fromUtf8 := fun bytes => host.pathFromOs <$> strings.fromUtf8 bytes
    fromWide := fun units => host.pathFromOs <$> strings.fromWide units
    toWide := fun path => strings.toWide (host.osFromPath path)
    encodedBytes := fun path => strings.encodedBytes (host.osFromPath path)
    encodedLength := fun path => strings.encodedLength (host.osFromPath path)
    readCString := strings.readCString
    readWideString := strings.readWideString
    writeCString := strings.writeCString
    writeWideString := strings.writeWideString
    arrayLayout := strings.arrayLayout
    allocate := strings.allocate }
  let access := main.access
  let readScalar := fun (operand : OpTy Provenance) => do
    let immediate ← PlaceMachine.readImmediate access operand
    lift (immediate.imm.toScalar.mapError ScalarOps.immediateError)
  let readPointer := fun operand => do
    let scalar ← readScalar operand
    lift (scalar.toPointer access.runtime.base |>.mapError ScalarOps.scalarError)
  let readU32 := fun operand => do
    let scalar ← readScalar operand
    lift (scalar.toUInt32 |>.mapError ScalarOps.scalarError)
  let readUsize := fun operand => do
    let scalar ← readScalar operand
    lift (scalar.toTargetUsize access.runtime.pointerSize |>.mapError ScalarOps.scalarError)
  let readI64 := fun operand => do
    let scalar ← readScalar operand
    lift (scalar.toInt64 |>.mapError ScalarOps.scalarError)
  let alignment : PointerPlaceMachine.AlignmentContext
      (ThreadStacks.Storage (Payload Os R P H D O Aff B Host)) := {
    policy := fun storage => storage.user.payload.alignment
    promises := fun storage => storage.user.symbolicAlignment }
  let pointerPlace := fun pointer (layout : LocalLayout) => do
    let mismatch ← PointerPlaceMachine.misalignmentWith access alignment pointer layout.layout.align.abi
    pure ⟨⟨pointer,.none,mismatch⟩,layout⟩
  let handles : WindowsHandles.Hooks (State Os R P H D O Aff B Host) (Ref H D O) := {
    pointerSize := access.runtime.pointerSize
    readScalar
    targetIsize := fun scalar => do
      lift (scalar.toInt access.runtime.pointerSize |>.mapError ScalarOps.scalarError)
    readI32 := fun operand => do
      lift ((← readScalar operand).toInt32 |>.mapError ScalarOps.scalarError)
    readU32
    readPointer
    isNull := fun pointer => pure (pointer.provenance.isNone && pointer.offset.bytes == 0)
    windows := fun name =>
      match CompilerWindowsConstants.scalar p.namedConstants "c" name with
      | .ok value => pure value
      | .error reason => throw (.unsupported reason)
    scalarI32 := fun scalar => do
      lift (scalar.toInt32 |>.mapError ScalarOps.scalarError)
    threads := do return (← get).machine.threads
    detachThread := fun id allowTerminatedJoined => do
      let manager ← get
      let next ← lift ((manager.machine.threads.detachThread id allowTerminatedJoined)
        |>.mapError threadError)
      modify fun state => { state with machine := { state.machine with threads := next } }
    lookupFd := fun number => do
      let some ref := (readiness.files.table (← get).machine.user).get number | return none
      return some (← FileMachine.cloneReference readiness.files ref)
    insertFd := fun ref => do
      let (table,number) ← lift ((readiness.files.table (← get).machine.user).insert ref)
      modify fun state => { state with machine := { state.machine with user := readiness.files.setTable table state.machine.user } }
      return number
    removeFd := fun number => do
      let (table,ref) := (readiness.files.table (← get).machine.user).remove number
      modify fun state => { state with machine := { state.machine with user := readiness.files.setTable table state.machine.user } }
      return ref
    dropFd := ReadinessMachine.dropFd readiness
    derefUsize := fun operand => do
      pointerPlace (← readPointer operand) ⟨operand.layout.ty,operand.layout.layout⟩
    writeScalar := fun scalar destination => writePlaceImmediate place choice (.scalar scalar)
      ⟨.memory destination.mplace,destination.layout⟩ }
  let handles := WindowsFileMachine.bindHandles readiness access.runtime threadError handles
  let constants := fun name => do
    let scalar ← match CompilerWindowsConstants.scalar p.namedConstants "c" name with
      | .ok value => pure value
      | .error reason => throw (.unsupported reason)
    lift (scalar.toUInt32 |>.mapError ScalarOps.scalarError)
  let writeInt := fun (value : Int) (destination : MPlaceTy Provenance) => do
    let scalar ← lift (Scalar.fromInt value destination.layout.layout.size
      |>.mapError ScalarOps.scalarError)
    writePlaceImmediate place choice (.scalar scalar)
      ⟨.memory destination.mplace,destination.layout⟩
  let layoutPlace := fun pointer name => do
    let layout ← namedLayout p name
    pointerPlace pointer layout
  let derefAs := fun (operand : OpTy Provenance) name => do
    layoutPlace (← readPointer operand) name
  let fieldPlace := fun parent name => field p projection choice parent name
  let fileBase : WindowsFiles.Hooks (State Os R P H D O Aff B Host)
      (Ref H D O) H D Path HM Time Error := {
    handles
    errors := environment.env.errors
    os := target.os
    communicate := environment.env.process.communicate
    noIsolation := environment.env.checkNoIsolation
    constant := constants
    readUsize
    readI64
    readWidePath := fun pointer => OsStrings.readPath pathStrings pointer true
    pathExists := host.pathExists
    openFileOrDir := fun path options => UnixOpen.openFileOrDir sharedOpen none path options
    dropFile := sharedOpen.dropFile
    dropDirectory := sharedOpen.dropDirectory
    insertFile := fun handle readable writable =>
      (UnixFsMachine.insertDescription readiness (.file handle readable writable)).map Prod.fst
    insertDirectory := fun directory path => do
      let directory ← prepareDirectory directory path
      (UnixFsMachine.insertDescription readiness (.directory directory)).map Prod.fst
    asFile := fun reference => match reference.value with
      | .file handle _ writable => some ⟨handle,writable⟩
      | _ => none
    metadata := fun reference => do
      match reference.value with
      | .file .. | .directory .. => return .inl (← files.hostMetadata reference.value)
      | .other value => otherMetadata value
      | _ => throw (.unsupported "obtaining Windows file metadata requires file-backed description")
    length := host.length
    fileType := host.fileType
    time := host.time
    windowsTicks := fun value => do
      let duration ← TimeShims.systemTimeSinceWindowsEpoch timeHooks value
      match TimeShims.windowsTicksFor duration with
      | .ok ticks => pure ticks
      | .error error => throw error
    fileLength := host.fileLength
    setLength := host.setLength
    syncAll := host.syncAll
    rename := host.rename
    removeFile := host.removeFile
    derefAs
    ptrToPlace := fun pointer name => layoutPlace pointer name
    derefI64 := fun operand => do
      let layout ← match CompilerPrimitiveFacts.primitiveLayout p.runtime "i64" with
        | .ok value => pure ⟨value.ty,value.layout⟩
        | .error reason => throw (.unsupported s!"compiler i64 layout for Windows file: {reason}")
      let place ← pointerPlace (← readPointer operand) layout
      unless place.layout == operand.layout do throw (.invalidProgram "Windows i64 operand layout disagrees with compiler")
      pure place
    checkAccess := checkPointerAccess
    field := fieldPlace
    readFieldI64 := fun place => do
      let immediate ← PlaceMachine.readImmediate access ⟨.indirect place.mplace,place.layout⟩
      let scalar ← lift (immediate.imm.toScalar.mapError ScalarOps.immediateError)
      lift (scalar.toInt64 |>.mapError ScalarOps.scalarError)
    writeFields := fun values parent => do
      for (name,value) in values do writeInt value (← fieldPlace parent name)
    writeInt
    seek := fun reference communicate origin => Files.seek files communicate reference.value origin
    readWrite := fun reference communicate write pointer count finish =>
      WindowsFileMachine.readWrite readiness files reference communicate write pointer count finish }
  let fileBase := WindowsFileMachine.bindTime timeHooks fileBase
  let paths : WindowsPaths.Hooks (State Os R P H D O Aff B Host)
      (Ref H D O) H D Path HM Time Error EnvVars.Kind := {
    files := fileBase
    strings := pathStrings
    absolute := fun path => do
      match host.absolute with
      | some absolute => absolute path
      | none => throw (.unsupported "Windows GetFullPathNameW requires host std::path::absolute") }
  let paths := WindowsFileMachine.bind readiness access.runtime threadError files sharedOpen
    otherMetadata prepareDirectory paths
  let symbols ← p.foreignSymbols
    |>.mapError StepError.unsupported
  let calls := CompilerCallConstruction.compiler p compatibilityBudget
  pure {
    paths
    systemConvention := do return (← CompilerNamedShimAbi.query p.namedAbi "CreateFileW").conv
    expectedAbi := fun name request => do
      let some operation := WindowsFileDispatch.parse name |
        throw (.unsupported s!"Windows file ABI requested for unknown `{name}`")
      let expected := WindowsFileDispatch.signature operation
      unless expected.args == request.args && expected.ret == request.ret do
        throw (.invalidProgram s!"Windows file ABI recipe disagrees with `{name}`")
      CompilerNamedShimAbi.query p.namedAbi name
    argumentCompat := calls.checkArgumentCompat choice
    checkSymbolClash := fun name =>
      match CompilerForeignSymbols.checkSymbolClash symbols name with
      | .ok () => pure ()
      | .error error => throw error
    transmute := fun operand expected => do
      match operand.transmute (← place.projection choice) expected |>.mapError
          IntrinsicVectorMachine.projectionError with
      | .ok value => pure value
      | .error error => throw error }

end Miri.Input.EvalWindowsFileConstruction
