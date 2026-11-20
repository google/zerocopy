import Miri.Input.CompilerProviders
import Miri.Input.CompilerLibcTypeLayouts
import Miri.Input.CompilerNamedConstants
import Miri.Input.CompilerNamedFields
import Miri.Input.CompilerPrimitiveFacts
import Miri.Input.EvalCoreMachine
import Miri.Input.EvalHostRuntimeConstruction
import Miri.Input.EvalProjectionMachine
import Miri.Input.EvalSocketStorage
import Miri.Input.EvalUnixConstruction
import Miri.Input.CompilerPrimitiveFacts
import Miri.Interpreter.PlaceDynamic
import Miri.Interpreter.PointerPlaceMachine
import Miri.Interpreter.UnixDirectories
import Miri.Interpreter.UnixFsDispatch
import Miri.Interpreter.UnixFsMachine
import Miri.Interpreter.UnixFsMetadata
import Miri.Interpreter.UnixFsPaths
import Miri.Interpreter.OsStrings

/-! Source construction for the pinned Unix filesystem shim family. Compiler
ABI facts, guest memory, descriptors and directory storage stay in the actual
EvalWorld. This layer accepts only raw host filesystem effects; policy remains
in the existing UnixFs interpreter modules. -/
namespace Miri.Input.EvalUnixFsConstruction
open Miri.ABI Miri.Memory Miri.MIR Miri.Interpreter

abbrev M := EStateM StepError

/-- Actual host operations not represented by the current source seed. Values
are raw std::fs/path/ReadDir observations; this record has no guest-memory,
compiler-layout, errno, descriptor-table, directory-table or shim-policy
callbacks. -/
structure HostEffects (S H D O Path HM Time E ReadDir Entry : Type) where
  hostUnix : Bool
  hostWindows : Bool
  /-- Width of this host's `usize`, used by source host-boundary checks. -/
  hostUsizeBits : Nat
  isEmpty : Path → Bool
  isAbsolute : Path → Bool
  isDot : Path → Bool
  emptyPath : Path
  /-- Exact `path::absolute(path).is_ok_and(|p| p.starts_with("/proc"))`. -/
  procAbsolute : Path → M S Bool
  currentExe : M S (Option Path)
  pathToString : Path → Option String
  removeFile : Path → M S (Except (IoError.HostError E) Unit)
  removeDirectory : Path → M S (Except (IoError.HostError E) Unit)
  symlinkDirectory : Path → M S Bool
  linkTargetDirectory : Path → Path → M S Bool
  createSymlink : Path → Path → Bool → M S (Except (IoError.HostError E) Unit)
  hardLink : Path → Path → M S (Except (IoError.HostError E) Unit)
  setPathPermissions : Path → UInt32 → M S (Except (IoError.HostError E) Unit)
  rename : Path → Path → M S (Except (IoError.HostError E) Unit)
  mkdir : Path → Option UInt32 → M S (Except (IoError.HostError E) Unit)
  readLink : Path → M S (Except (IoError.HostError E) Path)
  canonicalize : Path → M S (Except (IoError.HostError E) Path)
  pathMetadata : Option D → Path → Bool → M S (Except (IoError.HostError E) HM)
  fileType : HM → UnixFsMetadata.FileType
  length : HM → UInt64
  time : HM → UnixFsMetadata.TimeField → M S (Except (IoError.HostError E) Time)
  sinceEpoch : Time → M S Clock.Duration
  unixFields : HM → UnixFsMetadata.UnixFields
  readonly : HM → Bool
  readDir : Path → M S (Except (IoError.HostError E) ReadDir)
  openDirectory : Path → M S (Except (IoError.HostError E) D)
  dropReadDir : ReadDir → M S Unit
  nextEntry : ReadDir → M S (Option (Except (IoError.HostError E) Entry))
  entryName : Entry → Path
  entryType : Entry → M S (Except (IoError.HostError E) UnixFsMetadata.FileType)
  entryInode : Entry → UInt64
  setLength : H → UInt64 → M S (Except (IoError.HostError E) Unit)
  fileLength : H → M S (Except (IoError.HostError E) UInt64)
  setFilePermissions : H → UInt32 → M S (Except (IoError.HostError E) Unit)
  sync : H → Bool → M S (Except (IoError.HostError E) Unit)
  isTty : Files.Ref (Files.Description H D O) → Bool → M S Bool
  systemNow : M S Time
  sinceEpochCheckedAdd : Clock.Duration → M S (Option Time)
  setFileTimes : H → UnixFsTimes.Update Time → UnixFsTimes.Update Time →
    M S (Except (IoError.HostError E) Unit)
  setPathTimes : Path → Bool → UnixFsTimes.Update Time → UnixFsTimes.Update Time →
    M S (Except (IoError.HostError E) Unit)
  openExclusive : Path → UnixTempFile.HostOptions → M S (Except (IoError.HostError E) H)

private def lift (value : Except StepError A) : M S A :=
  match value with | .ok result => pure result | .error error => throw error

private def namedLayout (p : CompilerProviders.Prepared) (name : String) :
    Except StepError (LocalLayout) := do
  let value ← CompilerLibcTypeLayouts.layout p.runtime name
    |>.mapError fun reason => StepError.unsupported s!"compiler libc layout {name}: {reason}"
  pure ⟨value.ty,value.layout⟩

private def namedPointerPlace [DecidableEq MiriMemoryKind]
    (p : CompilerProviders.Prepared)
    (access : ValidityMachine.Access MiriMemoryKind U)
    (pointerCompiler : PointerPlaceMachine.Compiler MiriMemoryKind U C)
    (choice : C) (operand : OpTy Provenance) (name : String) :
    M (MachineHooks.State MiriMemoryKind (ValidityMachine.UserState U))
      (MPlaceTy Provenance) := do
  let layout ← lift (namedLayout p name)
  let immediate ← ValidityMachine.readImmediate access operand
  let place ← PointerPlaceMachine.fromImmediate access pointerCompiler choice immediate
  unless place.layout == layout do
    throw (.invalidProgram s!"filesystem {name} pointer pointee differs from compiler layout")
  pure place

/-- Construct places whose source shim explicitly supplies the pointee
layout, matching `deref_pointer_as`: read only the scalar pointer operand and
use the caller's target layout directly. Keep `namedPointerPlace` above for
ordinary stat, whose source uses `deref_pointer` instead. -/
private def namedTargetPointerPlace [DecidableEq MiriMemoryKind]
    (p : CompilerProviders.Prepared)
    (access : ValidityMachine.Access MiriMemoryKind U)
    (operand : OpTy Provenance) (name : String) :
    M (MachineHooks.State MiriMemoryKind (ValidityMachine.UserState U))
      (MPlaceTy Provenance) := do
  let layout ← lift (namedLayout p name)
  let immediate ← ValidityMachine.readImmediate access operand
  let scalar ← lift (immediate.imm.toScalar |>.mapError ScalarOps.immediateError)
  let pointer ← lift (scalar.toPointer access.runtime.base |>.mapError ScalarOps.scalarError)
  PointerPlaceMachine.fromPointer access pointer layout false

/-- Canonical stat metadata access, including compiler-owned exact named
layouts/constants and FD lookups from the existing source descriptor table. -/
def metadataFromSource [DecidableEq MiriMemoryKind]
    (p : CompilerProviders.Prepared)
    (access : ValidityMachine.Access MiriMemoryKind U)
    (projection : PlaceProjectionHooks Provenance
      (MachineHooks.State MiriMemoryKind (ValidityMachine.UserState U)) C MachineHooks.FrameExtra)
    (choice : C)
    (strings : OsStrings.Hooks Provenance
      (MachineHooks.State MiriMemoryKind (ValidityMachine.UserState U)) Os Kind)
    (pathFromOs : Os → Path)
    (errors : IoError.Hooks
      (MachineHooks.State MiriMemoryKind (ValidityMachine.UserState U)) E)
    (registry : ReadinessMachine.Hooks MiriMemoryKind (ValidityMachine.UserState U) H D O)
    (files : Files.Hooks
      (MachineHooks.State MiriMemoryKind (ValidityMachine.UserState U)) H D O E HM)
    (otherMetadata : O → M (MachineHooks.State MiriMemoryKind (ValidityMachine.UserState U))
      (Sum (Except (IoError.HostError E) HM) String))
    (host : HostEffects
      (MachineHooks.State MiriMemoryKind (ValidityMachine.UserState U)) H D O Path HM Time E ReadDir Entry)
    (os : String) (isolatedOp : EvalUnixConstruction.IsolatedOp) :
    Except StepError (UnixFsMetadata.Hooks
      (MachineHooks.State MiriMemoryKind (ValidityMachine.UserState U))
      (Files.Ref (Files.Description H D O)) D Path HM Time E) := do
  let pointerCompiler := CompilerExecutionProviders.pointerCompiler p.lifecycle.calls.symbols.facts
  let errors := {errors with family := ForeignItems.Family.unix, os}
  let readScalar : OpTy Provenance → M
      (MachineHooks.State MiriMemoryKind (ValidityMachine.UserState U))
      (Scalar Provenance) := fun operand => do
    let immediate ← PlaceMachine.readImmediate access operand
    match immediate.imm.toScalar with
    | .ok value => pure value
    | .error error => throw (ScalarOps.immediateError error)
  let libc : String → M
      (MachineHooks.State MiriMemoryKind (ValidityMachine.UserState U))
      (Scalar Provenance) := fun name => do
    match CompilerNamedConstants.scalar p.namedConstants name with
    | .ok value => pure value
    | .error reason => throw (StepError.unsupported s!"compiler libc constant {name}: {reason}")
  let readI32 := fun operand => do
    let scalar ← readScalar operand
    lift (scalar.toInt32 |>.mapError ScalarOps.scalarError)
  let readU32 := fun operand => do
    let scalar ← readScalar operand
    lift (scalar.toUInt32 |>.mapError ScalarOps.scalarError)
  let readPointer := fun operand => do
    let scalar ← readScalar operand
    lift (scalar.toPointer access.runtime.base |>.mapError ScalarOps.scalarError)
  let writeScalar := fun (scalar : Scalar Provenance) (destination : MPlaceTy Provenance) =>
    writePlaceImmediate projection.place choice (.scalar scalar)
      ⟨.memory destination.mplace,destination.layout⟩
  let writeInt := fun (value : Int) (destination : MPlaceTy Provenance) => do
    let scalar ← lift (Scalar.fromInt value destination.layout.layout.size
      |>.mapError ScalarOps.scalarError)
    writeScalar scalar destination
  let project := fun (parent : MPlaceTy Provenance) (index : Nat) => do
    let place ← PlaceDynamic.field projection choice ⟨.memory parent.mplace,parent.layout⟩ index
    match place.ref with
    | .memory memory => pure (MPlaceTy.mk memory place.layout)
    | .local .. => throw (.invalidProgram "filesystem field projection became local")
  let field := fun (parent : MPlaceTy Provenance) (name : String) => do
    let index ← match CompilerNamedFields.fieldIndex p.runtime parent.layout name with
      | .ok value => pure value
      | .error error => throw error
    project parent index
  let result : UnixFsMetadata.Hooks
      (MachineHooks.State MiriMemoryKind (ValidityMachine.UserState U))
      (Files.Ref (Files.Description H D O)) D Path HM Time E := {
    os, hostUnix := host.hostUnix, hostWindows := host.hostWindows, errors
    libcI32 := fun name => do
      let scalar ← libc name
      lift (scalar.toInt32 |>.mapError ScalarOps.scalarError)
    libcU32 := fun name => do
      let scalar ← libc name
      lift (scalar.toUInt32 |>.mapError ScalarOps.scalarError)
    libcMode := fun name => do
      let scalar ← libc name
      let mode ← match CompilerLibcTypeLayouts.layout p.runtime "mode_t" with
        | .ok value => pure value
        | .error reason => throw (.unsupported s!"compiler mode_t layout: {reason}")
      let value ← lift (scalar.toTargetUsize mode.layout.size |>.mapError ScalarOps.scalarError)
      if value.toNat >= 2^32 then throw (StepError.invalidProgram "mode_t does not fit u32")
      pure (UInt32.ofNat value.toNat)
    readI32, readU32, readPointer
    isNull := fun pointer => pure (pointer.provenance.isNone && pointer.offset.bytes == 0)
    readPath := fun pointer => do
      pathFromOs <$> OsStrings.readPath strings pointer
    isolationReject := fun name => do
      match isolatedOp with
      | .allow => pure false
      | .reject .abort => throw (.termination (.unsupportedInIsolation name))
      | .reject .noWarning | .reject .warning | .reject .warningWithoutBacktrace => pure true
    lookupFd := fun number => do
      let some ref := (registry.files.table (← get).machine.user).get number | return none
      return some (← FileMachine.cloneReference registry.files ref)
    dropFd := ReadinessMachine.dropFd registry
    asDirectory := fun reference => match reference.value with
      | .directory directory => some directory | _ => none
    fdMetadata := fun reference => do
      match reference.value with
      | .file .. | .directory .. => return .inl (← files.hostMetadata reference.value)
      | .other other => otherMetadata other
      | _ => throw (.unsupported "obtaining metadata requires file-backed description")
    isEmpty := host.isEmpty -- filled below by path environment adapters
    isAbsolute := host.isAbsolute
    isDot := host.isDot
    emptyPath := host.emptyPath
    metadata := host.pathMetadata
    fileType := host.fileType, length := host.length, time := host.time
    sinceEpoch := host.sinceEpoch, unixFields := host.unixFields, readonly := host.readonly
    deref := fun operand => do
      let place ← namedPointerPlace p access pointerCompiler choice operand "stat"
      pure place
    derefAs := fun operand name => namedTargetPointerPlace p access operand name
    writeFields := fun values parent => do
      for (name,value) in values do writeInt value (← field parent name)
    field
    index := fun parent index => do
      let place ← PlaceDynamic.index projection choice
        ⟨.memory parent.mplace,parent.layout⟩ index
      match place.ref with
      | .memory memory => pure (MPlaceTy.mk memory place.layout)
      | .local .. => throw (.invalidProgram "filesystem array field projection became local")
    writeInt }
  let metadata := UnixFsMachine.bindMetadata registry files otherMetadata result
  pure metadata

/-- Build the path string codec over the same EvalWorld memory, but expose
the actual allocator kind: `realpath(NULL)` calls Miri's C allocator, while
the ordinary environment-string builder only exposes its narrower env kinds. -/
def osStringsFromSource [DecidableEq MiriMemoryKind]
    (host : EvalHostRuntimeConstruction.OsHostEffects Os)
    (memory : EvalHostRuntimeConstruction.EnvironmentMemory (ValidityMachine.Control U) C Payload) :
    OsStrings.Hooks Provenance (MachineHooks.State MiriMemoryKind
      (ValidityMachine.UserState U)) Os (MemoryKind MiriMemoryKind) := by
  let access := memory.access
  let pointer := memory.pointers
  let osPointer : OsStringMachine.Hooks MiriMemoryKind (ValidityMachine.Control U) :=
    ⟨access,pointer,memory.symbolicAlignment,memory.enforceAlignment⟩
  exact {
    hostWindows := host.hostWindows
    hostUnix := host.hostUnix
    targetWindows := host.targetWindows
    fromUnixBytes := host.fromUnixBytes
    fromUtf8 := host.fromUtf8
    fromWide := host.fromWide
    toWide := host.toWide
    encodedBytes := host.encodedBytes
    encodedLength := host.encodedLength
    readCString := fun base => do
      let rec scan (fuel length : Nat) : M
          (MachineHooks.State MiriMemoryKind (ValidityMachine.UserState U)) UInt64 := do
        match fuel with
        | 0 => throw (.resourceExhaustion "C string scan budget")
        | fuel + 1 =>
          if length >= 2^64 then throw (.invalidProgram "C string length overflow")
          let location ← match RawMemoryMachine.offset pointer.arithmetic base (UInt64.ofNat length) with
            | .ok value => pure value
            | .error error => throw error
          if (← RawMemoryMachine.readByte access pointer.arithmetic location) == 0 then
            return UInt64.ofNat length
          scan fuel (length + 1)
      let length ← scan memory.stringScanBudget 0
      let bytes ← RawMemoryMachine.readBytes access pointer.arithmetic base length
      unless bytes.size == length.toNat do throw (.invalidProgram "C string byte-read length mismatch")
      return bytes
    readWideString := OsStringMachine.readWideString osPointer memory.stringScanBudget
    writeCString := RawMemoryMachine.writeCString access pointer.arithmetic
    writeWideString := OsStringMachine.writeWideString osPointer
    arrayLayout := fun wide count => do
      let state ← get
      match RuntimeArrayTypes.osStringArray (memory.arrays.get state) wide count with
      | .error error => throw (.unsupported s!"runtime OS-string array layout: {reprStr error}")
      | .ok (layout,world) =>
        set (memory.arrays.set state world)
        pure layout
    allocate := fun layout kind => do
      unless layout.layout.isSized do throw (.invalidProgram "unsized filesystem path allocation")
      let result ← ReallocationDriver.allocateConfigured memory.allocation layout.layout.size
        layout.layout.align.abi kind .Uninit
      return Pointer.withOptionalProvenance result }

/-- Canonical pathname shim hooks. All ABI reads/writes use the existing guest
access and compiler layouts; the only supplied values are actual raw host path
operations and the same source OS-string representation. -/
def pathsFromSource [DecidableEq MiriMemoryKind]
    (p : CompilerProviders.Prepared)
    (access : ValidityMachine.Access MiriMemoryKind U)
    (memory : EvalHostRuntimeConstruction.EnvironmentMemory (ValidityMachine.Control U) C Payload)
    (metadata : UnixFsMetadata.Hooks
      (MachineHooks.State MiriMemoryKind (ValidityMachine.UserState U)) F D Path HM Time E)
    (strings : OsStrings.Hooks Provenance
      (MachineHooks.State MiriMemoryKind (ValidityMachine.UserState U)) Os
      (MemoryKind MiriMemoryKind))
    (pathFromOs : Os → Path) (osFromPath : Path → Os)
    (host : HostEffects
      (MachineHooks.State MiriMemoryKind (ValidityMachine.UserState U)) H D O Path HM Time E ReadDir Entry) :
    Except StepError (UnixFsPaths.Hooks
      (MachineHooks.State MiriMemoryKind (ValidityMachine.UserState U)) F D Path HM Time E
      (MemoryKind MiriMemoryKind)) := do
  let readScalar : OpTy Provenance → M
      (MachineHooks.State MiriMemoryKind (ValidityMachine.UserState U)) (Scalar Provenance) := fun operand => do
    let immediate ← ValidityMachine.readImmediate access operand
    match immediate.imm.toScalar with
    | .ok value => pure value
    | .error error => throw (ScalarOps.immediateError error)
  let readUsize : OpTy Provenance → M
      (MachineHooks.State MiriMemoryKind (ValidityMachine.UserState U)) UInt64 := fun operand => do
    let scalar ← readScalar operand
    match scalar.toTargetUsize access.runtime.pointerSize with
    | .ok value => pure value
    | .error error => throw (ScalarOps.scalarError error)
  let readMode : OpTy Provenance → M
      (MachineHooks.State MiriMemoryKind (ValidityMachine.UserState U)) UInt32 := fun operand => do
    let mode ← match CompilerPrimitiveFacts.namedLayout p.runtime "mode_t" with
      | .ok value => pure value
      | .error reason => throw (.unsupported s!"compiler mode_t layout: {reason}")
    let value ← match (← readScalar operand).toTargetUsize mode.layout.size with
      | .ok value => pure value
      | .error error => throw (ScalarOps.scalarError error)
    if value.toNat >= 2^32 then throw (.invalidProgram "mode_t does not fit u32")
    pure (UInt32.ofNat value.toNat)
  let readU16 : OpTy Provenance → M
      (MachineHooks.State MiriMemoryKind (ValidityMachine.UserState U)) UInt16 := fun operand => do
    let scalar ← readScalar operand
    match scalar.toUInt16 with
    | .ok value => pure value
    | .error error => throw (ScalarOps.scalarError error)
  let writeBytes := RawMemoryMachine.writeBytes access memory.pointers.arithmetic
  let pathStrings : OsStrings.Hooks Provenance
      (MachineHooks.State MiriMemoryKind (ValidityMachine.UserState U)) Path
      (MemoryKind MiriMemoryKind) := {
    hostWindows := strings.hostWindows
    hostUnix := strings.hostUnix
    targetWindows := strings.targetWindows
    fromUnixBytes := fun bytes => pathFromOs (strings.fromUnixBytes bytes)
    fromUtf8 := fun bytes => pathFromOs <$> strings.fromUtf8 bytes
    fromWide := fun units => pathFromOs <$> strings.fromWide units
    toWide := fun path => strings.toWide (osFromPath path)
    encodedBytes := fun path => strings.encodedBytes (osFromPath path)
    encodedLength := fun path => strings.encodedLength (osFromPath path)
    readCString := strings.readCString
    readWideString := strings.readWideString
    writeCString := strings.writeCString
    writeWideString := strings.writeWideString
    arrayLayout := strings.arrayLayout
    allocate := strings.allocate }
  pure {
    metadata, strings := pathStrings
    cKind := .machine .c, readMode, readU16, readUsize, writeBytes
    procAbsolute := fun path => do
      -- path::absolute may fail for reasons independent of prefix matching.
      -- The host leaf returns the exact source is_ok_and result.
      host.procAbsolute path
    pathToString := host.pathToString
    currentExe := host.currentExe
    hostUsizeBits := host.hostUsizeBits
    removeFile := host.removeFile
    removeDirectory := host.removeDirectory
    symlinkDirectory := host.symlinkDirectory
    linkTargetDirectory := host.linkTargetDirectory
    createSymlink := host.createSymlink
    hardLink := host.hardLink
    setPermissions := host.setPathPermissions
    rename := host.rename
    mkdir := host.mkdir
    readLink := host.readLink
    canonicalize := host.canonicalize }

/-- Bind file-only filesystem operations to the canonical Files implementation
and the same owned descriptor references used by readiness and close. -/
def fdFromSource
    (paths : UnixFsPaths.Hooks S (Files.Ref (Files.Description H D O)) D Path HM Time E Kind)
    (files : Files.Hooks S H D O E HM) (communicate : Bool)
    (host : HostEffects S H D O Path HM Time E ReadDir Entry) :
    UnixFsFd.Hooks S (Files.Ref (Files.Description H D O)) D Path HM Time E Kind H := {
  paths, communicate
  asFile := fun reference => match reference.value with
    | .file handle readable writable => some ⟨handle,readable,writable⟩
    | _ => none
  seek := fun reference communicate origin => Files.seek files communicate reference.value origin
  isTty := host.isTty
  setLength := host.setLength
  fileLength := host.fileLength
  setPermissions := host.setFilePermissions
  sync := host.sync }

/-- Source `timespec` input and host file-time operations. Field identities and
layouts come from the selected compiler; reads still pass through the active
borrow/race/initialization access engine. -/
def timesFromSource [DecidableEq MiriMemoryKind]
    (p : CompilerProviders.Prepared)
    (access : ValidityMachine.Access MiriMemoryKind U)
    (projection : PlaceProjectionHooks Provenance
      (MachineHooks.State MiriMemoryKind (ValidityMachine.UserState U)) C MachineHooks.FrameExtra)
    (choice : C)
    (memory : EvalHostRuntimeConstruction.EnvironmentMemory (ValidityMachine.Control U) C Payload)
    (fd : UnixFsFd.Hooks
      (MachineHooks.State MiriMemoryKind (ValidityMachine.UserState U))
      (Files.Ref (Files.Description H D O)) D Path HM Time E (MemoryKind MiriMemoryKind) H)
    (host : HostEffects
      (MachineHooks.State MiriMemoryKind (ValidityMachine.UserState U)) H D O Path HM Time E ReadDir Entry) :
    UnixFsTimes.Hooks
      (MachineHooks.State MiriMemoryKind (ValidityMachine.UserState U))
      (Files.Ref (Files.Description H D O)) D Path HM Time E (MemoryKind MiriMemoryKind) H := by
  let stateType := MachineHooks.State MiriMemoryKind (ValidityMachine.UserState U)
  let indexedField : MPlaceTy Provenance → Nat → M stateType (MPlaceTy Provenance) := fun parent index => do
    let projected ← PlaceDynamic.index projection choice ⟨.memory parent.mplace,parent.layout⟩ (UInt64.ofNat index)
    match projected.ref with
    | .memory place => return ⟨place,projected.layout⟩
    | .local .. => throw (.invalidProgram "timespec field projection became local")
  let readSigned := fun (place : MPlaceTy Provenance) => do
    let immediate ← PlaceMachine.readImmediate access ⟨.indirect place.mplace,place.layout⟩
    let scalar ← match immediate.imm.toScalar with
      | .ok value => pure value
      | .error error => throw (ScalarOps.immediateError error)
    match scalar.toInt place.layout.layout.size with
    | .ok value => pure value
    | .error error => throw (ScalarOps.scalarError error)
  let field := fun (parent : MPlaceTy Provenance) (name : String) => do
    let index ← match CompilerNamedFields.fieldIndex p.runtime parent.layout name with
      | .ok value => pure value
      | .error error => throw error
    indexedField parent index
  let layout : M stateType LocalLayout := do
    match CompilerPrimitiveFacts.namedLayout p.runtime "libc_timespec" with
    | .ok value => pure ⟨value.ty,value.layout⟩
    | .error reason => throw (.unsupported s!"compiler libc timespec layout: {reason}")
  let readTimespec := fun (place : MPlaceTy Provenance) => do
    let seconds ← readSigned (← field place "tv_sec")
    let nanos ← readSigned (← field place "tv_nsec")
    if seconds < 0 then throw (StepError.unsupported "timespec with negative tv_sec is not supported")
    if seconds >= 2^64 then throw (StepError.invalidProgram "tv_sec should fit in64bits")
    if nanos < 0 || nanos >= 1000000000 then return none
    match Clock.Duration.fromNanos (seconds.toNat * 1000000000 + nanos.toNat) with
    | .ok duration => return some duration
    | .error error => throw error
  let result : UnixFsTimes.Hooks
      (MachineHooks.State MiriMemoryKind (ValidityMachine.UserState U))
      (Files.Ref (Files.Description H D O)) D Path HM Time E (MemoryKind MiriMemoryKind) H := {
    fd
    systemNow := host.systemNow
    sinceEpoch := host.sinceEpochCheckedAdd
    indexedField
    readTargetIsize := readSigned
    libcTargetIsize := fun name => do
      let constants := p.namedConstants
      let scalar : Scalar Provenance ← match CompilerNamedConstants.scalar constants name with
        | .ok value => pure value
        | .error reason => throw (StepError.unsupported s!"compiler libc constant {name}: {reason}")
      match scalar.toInt access.runtime.pointerSize with
      | .ok value => pure value
      | .error error => throw (ScalarOps.scalarError error)
    timespecLayout := layout
    ptrToPlace := fun pointer localLayout => ⟨⟨pointer,.none,none⟩,localLayout⟩
    offsetPlace := fun parent offset localLayout => do
      let pointer ← match RawMemoryMachine.offset memory.pointers.arithmetic
          parent.mplace.ptr offset.bytes with
        | .ok value => pure value
        | .error error => throw error
      pure ⟨{parent.mplace with ptr := pointer},localLayout⟩
    readTimespec
    setFileTimes := host.setFileTimes
    setPathTimes := host.setPathTimes }
  exact result

/-- Reuse the one rooted runtime DIR table and allocate/write dirent results
through compiler-provided layouts and the active source memory access. -/
def directoriesFromSource [DecidableEq MiriMemoryKind]
    (p : CompilerProviders.Prepared)
    (access : PlaceMachine.AccessConfig MiriMemoryKind (ValidityMachine.UserState U))
    (projection : PlaceProjectionHooks Provenance
      (MachineHooks.State MiriMemoryKind (ValidityMachine.UserState U)) C MachineHooks.FrameExtra)
    (choice : C)
    (memory : EvalHostRuntimeConstruction.EnvironmentMemory (ValidityMachine.Control U) C Payload)
    (paths : UnixFsPaths.Hooks
      (MachineHooks.State MiriMemoryKind (ValidityMachine.UserState U))
      (Files.Ref (Files.Description H D O)) D Path HM Time E (MemoryKind MiriMemoryKind))
    (registry : ReadinessMachine.Hooks MiriMemoryKind (ValidityMachine.UserState U) H D O)
    (readiness : Readiness.Hooks
      (MachineHooks.State MiriMemoryKind (ValidityMachine.UserState U))
      (Files.Ref (Files.Description H D O)))
    (fd : UnixFd.Hooks
      (MachineHooks.State MiriMemoryKind (ValidityMachine.UserState U)) H D O E HM)
    (store : UnixFsMachine.DirectoryStore (ValidityMachine.UserState U) ReadDir)
    (host : HostEffects
      (MachineHooks.State MiriMemoryKind (ValidityMachine.UserState U)) H D O Path HM Time E ReadDir Entry) :
    UnixDirectories.Hooks
      (MachineHooks.State MiriMemoryKind (ValidityMachine.UserState U))
      (Files.Ref (Files.Description H D O)) D Path HM Time E (MemoryKind MiriMemoryKind) ReadDir Entry := by
  let readUsize : OpTy Provenance → M
      (MachineHooks.State MiriMemoryKind (ValidityMachine.UserState U)) UInt64 := fun operand => do
    let immediate ← PlaceMachine.readImmediate access operand
    let scalar ← match immediate.imm.toScalar with
      | .ok value => pure value
      | .error error => throw (ScalarOps.immediateError error)
    match scalar.toTargetUsize access.runtime.pointerSize with
    | .ok value => pure value
    | .error error => throw (ScalarOps.scalarError error)
  let writePointer := fun (pointer : Pointer (Option Provenance)) (dest : MPlaceTy Provenance) => do
    let scalar ← match Scalar.fromMaybePointer access.runtime.base pointer with
      | .ok value => pure value
      | .error error => throw (ScalarOps.scalarError error)
    writePlaceImmediate projection.place choice (.scalar scalar)
      ⟨.memory dest.mplace,dest.layout⟩
  let direntLayout : String → M
      (MachineHooks.State MiriMemoryKind (ValidityMachine.UserState U)) LocalLayout := fun name => do
    match CompilerLibcTypeLayouts.layout p.runtime name with
    | .ok value => pure ⟨value.ty,value.layout⟩
    | .error reason => throw (.unsupported s!"compiler libc layout {name}: {reason}")
  let optionalField : MPlaceTy Provenance → String → M
      (MachineHooks.State MiriMemoryKind (ValidityMachine.UserState U)) (Option (MPlaceTy Provenance)) :=
      fun parent name => do
    let node ← match p.runtime.node parent.layout.ty with
      | .ok value => pure value
      | .error error => throw (.unsupported s!"compiler type shape for optional dirent field: {error}")
    unless node.shapeStatus == .supported do
      throw (.unsupported "compiler type shape for optional dirent field")
    let shape ← match node.payload.getObjVal? "shape" with
      | .ok value => pure value
      | .error error => throw (.invalidProgram s!"compiler dirent shape field: {error}")
    let variants ← match shape.getObjVal? "variants" >>= Lean.Json.getArr? with
      | .ok value => pure value
      | .error error => throw (.invalidProgram s!"compiler dirent variants: {error}")
    if variants.size != 1 then throw (.unsupported "optional dirent fields require non-enum compiler ADT")
    let some variant := variants[0]? | throw (.invalidProgram "compiler dirent missing variant")
    let fields ← match variant.getObjVal? "fields" >>= Lean.Json.getArr? with
      | .ok value => pure value
      | .error error => throw (.invalidProgram s!"compiler dirent fields: {error}")
    let matching := fields.filter fun field =>
      ((field.getObjVal? "name").bind Lean.Json.getStr?).toOption == some name
    if matching.isEmpty then return none
    if matching.size != 1 then throw (.invalidProgram s!"ambiguous compiler dirent field {name}")
    let some field := matching[0]? | throw (.invalidProgram "compiler dirent field lookup failed")
    let index ← match field.getObjVal? "index" >>= Lean.Json.getNat? with
      | .ok value => pure value
      | .error error => throw (.invalidProgram s!"compiler dirent field index: {error}")
    let _ ← match p.runtime.field parent.layout index with
      | .ok value => pure value
      | .error error => throw (.unsupported s!"compiler dirent field layout: {error}")
    let place ← PlaceDynamic.field projection choice ⟨.memory parent.mplace,parent.layout⟩ index
    match place.ref with
    | .memory memory => return some ⟨memory,place.layout⟩
    | .local .. => throw (.invalidProgram "dirent optional field projection became local")
  let writeNull := fun (dest : MPlaceTy Provenance) => do
    let scalar : Scalar Provenance ← match Scalar.nullPointer access.runtime.base with
      | .ok value => pure value
      | .error error => throw (ScalarOps.scalarError error)
    writePlaceImmediate projection.place choice (.scalar scalar)
      ⟨.memory dest.mplace,dest.layout⟩
  let allocateRuntime := fun (size : Size) (align : Align) => do
    let pointer ← ReallocationDriver.allocateConfigured memory.allocation size align
      (.machine .runtime) .Uninit
    pure pointer.withOptionalProvenance
  let result : UnixDirectories.Hooks
      (MachineHooks.State MiriMemoryKind (ValidityMachine.UserState U))
      (Files.Ref (Files.Description H D O)) D Path HM Time E (MemoryKind MiriMemoryKind) ReadDir Entry := {
    paths
    get := do return store.get (← get).machine.user
    put := fun table => modify fun state => {state with machine := {state.machine with user := store.put table state.machine.user}}
    readDir := host.readDir
    openDirectory := host.openDirectory
    dropReadDir := host.dropReadDir
    insertDirectory := fun directory => UnixFsMachine.insertDescription registry (.directory directory)
    id := Files.Ref.id
    nextEntry := host.nextEntry
    entryName := host.entryName
    entryType := host.entryType
    entryInode := host.entryInode
    readUsize
    writePointer
    direntLayout
    allocateRuntime
    asPlace := fun pointer layout => ⟨⟨pointer,.none,none⟩,layout⟩
    wrappingOffset := fun pointer size => do
      match RawMemoryMachine.offset memory.pointers.arithmetic pointer size.bytes with
      | .ok value => pure value
      | .error error => throw error
    optionalField
    writeNull
    deallocateRuntime := fun pointer => memory.deallocate pointer none (.machine .runtime)
    closeFd := UnixFd.close (ReadinessMachine.bindFiles registry readiness fd)
    libcU8 := fun name => do
      let scalar : Scalar Provenance ← match CompilerNamedConstants.scalar p.namedConstants name with
        | .ok value => pure value
        | .error reason => throw (.unsupported s!"compiler libc constant {name}: {reason}")
      match scalar.toUInt8 with
      | .ok value => pure value
      | .error error => throw (ScalarOps.scalarError error) }
  exact result

/-- Source mkstemp hooks over the actual RNG selection and owned FD registry.
The random action is passed separately from host FS leaves because its state is
the interpreter's machine choice tape, not host nondeterminism. -/
def temporaryFromSource
    (paths : UnixFsPaths.Hooks (MachineHooks.State MiriMemoryKind U)
      (Files.Ref (Files.Description H D O)) D Path HM Time E Kind)
    (registry : ReadinessMachine.Hooks MiriMemoryKind U H D O)
    (choose : Nat → MachineHooks.M MiriMemoryKind U Nat)
    (host : HostEffects (MachineHooks.State MiriMemoryKind U) H D O Path HM Time E ReadDir Entry)
    (attemptBudget : Nat) :
    UnixTempFile.Hooks (MachineHooks.State MiriMemoryKind U)
      (Files.Ref (Files.Description H D O)) D Path HM Time E Kind H := {
  paths
  choose
  openExclusive := host.openExclusive
  insertFile := fun handle readable writable => do
    let (number,_) ← UnixFsMachine.insertDescription registry (.file handle readable writable)
    pure number
  attemptBudget }

end Miri.Input.EvalUnixFsConstruction
