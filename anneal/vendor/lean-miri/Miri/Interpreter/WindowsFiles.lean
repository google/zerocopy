import Miri.Interpreter.WindowsHandles
import Miri.Interpreter.UnixOpen
import Miri.Interpreter.UnixFsMetadata

/-! Complete windows/fs.rs policy. Reuses shared FileDescription and host open
infrastructure; target constants and real host resources remain mandatory. -/
namespace Miri.Interpreter.WindowsFiles
open Miri.ABI Miri.Memory Miri.Concurrency
abbrev M := EStateM StepError
inductive Disposition where | createAlways | createNew | openAlways | openExisting | truncateExisting
  deriving DecidableEq, Repr
structure Attributes where
  normal : Bool := false
  backup : Bool := false
  reparse : Bool := false
structure File (H : Type) where
  handle : H
  writable : Bool
structure Hooks (S F H D P HM Time E : Type) where
  handles : WindowsHandles.Hooks S F
  errors : IoError.Hooks S E
  os : String
  communicate : Bool
  noIsolation : String → M S Unit
  constant : String → M S UInt32
  readUsize : OpTy Provenance → M S UInt64
  readI64 : OpTy Provenance → M S Int64
  readWidePath : Pointer (Option Provenance) → M S P
  pathExists : P → M S Bool
  /-- Actual shared open_file_or_dir(None,path,options), including host workaround. -/
  openFileOrDir : P → UnixOpen.Options → M S (Except (IoError.HostError E) (UnixOpen.Opened H D))
  dropFile : H → M S Unit
  dropDirectory : D → M S Unit
  insertFile : H → Bool → Bool → M S Int32
  insertDirectory : D → P → M S Int32
  asFile : F → Option (File H)
  metadata : F → M S (Sum (Except (IoError.HostError E) HM) String)
  length : HM → UInt64
  fileType : HM → UnixFsMetadata.FileType
  time : HM → UnixFsMetadata.TimeField → M S (Except (IoError.HostError E) Time)
  /-- system_time_since_windows_epoch then windows_ticks_for (checked u64). -/
  windowsTicks : Time → M S UInt64
  fileLength : H → M S (Except (IoError.HostError E) UInt64)
  setLength : H → UInt64 → M S (Except (IoError.HostError E) Unit)
  syncAll : H → M S (Except (IoError.HostError E) Unit)
  rename : P → P → M S (Except (IoError.HostError E) Unit)
  removeFile : P → M S (Except (IoError.HostError E) Unit)
  derefAs : OpTy Provenance → String → M S (MPlaceTy Provenance)
  ptrToPlace : Pointer (Option Provenance) → String → M S (MPlaceTy Provenance)
  derefI64 : OpTy Provenance → M S (MPlaceTy Provenance)
  checkAccess : Pointer (Option Provenance) → Size → M S Unit
  field : MPlaceTy Provenance → String → M S (MPlaceTy Provenance)
  readFieldI64 : MPlaceTy Provenance → M S Int64
  writeFields : Array (String × Int) → MPlaceTy Provenance → M S Unit
  writeInt : Int → MPlaceTy Provenance → M S Unit
  seek : F → Bool → Files.SeekFrom → M S (Except (IoError.Error E) UInt64)
  /-- Consumes owned FD reference, including asynchronous completion. Real Files
  read/write provides the immediate/file route and custom typed pending callbacks. -/
  readWrite : F → Bool → Bool → Pointer (Option Provenance) → Nat → Files.Finish S E → M S Unit
private def onError (action : M S A) (cleanup : M S Unit) : M S A := fun state =>
  match action state with
  | .ok value state => .ok value state
  | .error error state => match cleanup state with
    | .ok _ state => .error error state | .error next state => .error next state
private def target (h : Hooks S F H D P HM T E) (name : String) : M S Unit := do
  if h.os != "windows" then throw (.invalidProgram s!"{name} requires Windows target")
private def boolValue (h : Hooks S F H D P HM T E) (value : Bool) : M S (Scalar Provenance) :=
  h.handles.windows (if value then "TRUE" else "FALSE")
private def finish (h : Hooks S F H D P HM T E) (result : Except (IoError.HostError E) Unit) : M S (Scalar Provenance) := do
  match result with
  | .ok _ => boolValue h true
  | .error error => IoError.setLastError h.errors (.host error); boolValue h false

def disposition (h : Hooks S F H D P HM T E) (value : UInt32) : M S Disposition := do
  let always ← h.constant "CREATE_ALWAYS"
  let new ← h.constant "CREATE_NEW"
  let openAlways ← h.constant "OPEN_ALWAYS"
  let existing ← h.constant "OPEN_EXISTING"
  let truncate ← h.constant "TRUNCATE_EXISTING"
  if value == always then return .createAlways
  if value == new then return .createNew
  if value == openAlways then return .openAlways
  if value == existing then return .openExisting
  if value == truncate then return .truncateExisting
  throw (.unsupported "CreateFileW: unsupported creation disposition")

def attributes (h : Hooks S F H D P HM T E) (value : UInt32) : M S Attributes := do
  let normal ← h.constant "FILE_ATTRIBUTE_NORMAL"
  let backup ← h.constant "FILE_FLAG_BACKUP_SEMANTICS"
  let reparse ← h.constant "FILE_FLAG_OPEN_REPARSE_POINT"
  let mut value := value
  let mut result : Attributes := {}
  if value &&& backup != 0 then
    value := value &&& ~~~backup
    result := { result with backup := true }
  if value &&& reparse != 0 then
    value := value &&& ~~~reparse
    result := { result with reparse := true }
  if value &&& normal != 0 then
    value := value &&& ~~~normal
    result := { result with normal := true }
  if value != 0 then throw (.unsupported "CreateFileW: unsupported flags_and_attributes")
  if !result.normal && !result.backup && !result.reparse then result := { normal := true }
  return result

private def createLoop (h : Hooks S F H D P HM T E) (path : P) (read write : Bool)
    (disposition : Disposition) (attributes : Attributes) (fuel : Nat) : M S WindowsHandles.Handle := do
  match fuel with
  | 0 => throw (.invalidProgram "CreateFileW stuck in source100-attempt retry loop")
  | fuel + 1 =>
    let present ← h.pathExists path
    let mut options : UnixOpen.Options := { read := read, write := write }
    match disposition with
    | .createAlways | .openAlways =>
      if !present then options := { options with createNew := true }
      if disposition == .createAlways then options := { options with truncate := true }
    | .createNew =>
      options := { options with createNew := true }
      if !write then options := { options with append := true }
    | .openExisting =>
      if !read && !write then options := { options with read := true }
    | .truncateExisting => options := { options with truncate := true }
    match ← h.openFileOrDir path options with
    | .error error =>
      if (present && error.kind == .NotFound) || (!present && error.kind == .AlreadyExists) then
        return ← createLoop h path read write disposition attributes fuel
      if error.kind == .IsADirectory && write then IoError.setLastError h.errors (.windows "ERROR_ACCESS_DENIED")
      else IoError.setLastError h.errors (.host error)
      return .invalid
    | .ok (.directory directory) =>
      if !attributes.backup then
        Files.withDrop (do
          IoError.setLastError h.errors (.windows "ERROR_ACCESS_DENIED")
          return WindowsHandles.Handle.invalid
        ) (h.dropDirectory directory)
      else
        if disposition == .createAlways || disposition == .openAlways then
          h.dropDirectory directory
          throw (.invalidProgram "CreateFileW unreachable directory creation disposition")
        return .file (← h.insertDirectory directory path)
    | .ok (.file file) =>
      onError (do
        if (disposition == .createAlways || disposition == .openAlways) && present then
          IoError.setLastError h.errors (.windows "ERROR_ALREADY_EXISTS")
      ) (h.dropFile file)
      return .file (← h.insertFile file read write)

def create (h : Hooks S F H D P HM T E) (name access share security disp flags template : OpTy Provenance) :
    M S WindowsHandles.Handle := do
  target h "CreateFileW"
  h.noIsolation "`CreateFileW`"
  let zero ← match Scalar.fromInt 0 (Size.ofBytes 4) with | .ok value => pure value | .error _ => throw (.invalidProgram "i32 zero")
  IoError.setLastError h.errors (.raw zero)
  let path ← h.readWidePath (← h.handles.readPointer name)
  let access ← h.handles.readU32 access
  let share ← h.handles.readU32 share
  let security ← h.handles.readPointer security
  let disp ← h.handles.readU32 disp
  let flags ← h.handles.readU32 flags
  let template ← h.readUsize template
  let read ← h.constant "GENERIC_READ"
  let write ← h.constant "GENERIC_WRITE"
  let deleteShare ← h.constant "FILE_SHARE_DELETE"
  let readShare ← h.constant "FILE_SHARE_READ"
  let writeShare ← h.constant "FILE_SHARE_WRITE"
  let disp ← disposition h disp
  let attr ← attributes h flags
  if share != deleteShare ||| readShare ||| writeShare then throw (.unsupported "CreateFileW: unsupported share mode")
  if !(← h.handles.isNull security) then throw (.unsupported "CreateFileW: security attributes unsupported")
  if template != 0 then throw (.unsupported "CreateFileW: template unsupported")
  let desiredRead := access &&& read != 0
  let access := if desiredRead then access &&& ~~~read else access
  let desiredWrite := access &&& write != 0
  let access := if desiredWrite then access &&& ~~~write else access
  if access != 0 then throw (.unsupported "CreateFileW: unsupported access bits")
  if attr.reparse != (disp == .createNew) then throw (.unsupported "CreateFileW: OPEN_REPARSE iff CREATE_NEW required")
  if attr.backup && disp != .openExisting then throw (.unsupported "CreateFileW: BACKUP_SEMANTICS requires OPEN_EXISTING")
  if attr.backup && desiredWrite then throw (.unsupported "CreateFileW: BACKUP_SEMANTICS with GENERIC_WRITE unsupported")
  createLoop h path desiredRead desiredWrite disp attr 100

private def timePair (h : Hooks S F H D P HM T E) (metadata : HM) (field : UnixFsMetadata.TimeField) : M S (UInt32 × UInt32) := do
  match ← h.time metadata field with
  | .error _ => return (0,0)
  | .ok time =>
    let ticks ← h.windowsTicks time
    return (ticks.toUInt32,(ticks >>> 32).toUInt32)
private def writeTime (h : Hooks S F H D P HM T E) (place : MPlaceTy Provenance) (name : String) (time : UInt32 × UInt32) : M S Unit := do
  h.writeFields #[("dwLowDateTime",time.1.toNat),("dwHighDateTime",time.2.toNat)] (← h.field place name)

def getInformation (h : Hooks S F H D P HM T E) (file info : OpTy Provenance) : M S (Scalar Provenance) := do
  target h "GetFileInformationByHandle"
  h.noIsolation "`GetFileInformationByHandle`"
  let file ← WindowsHandles.read h.handles file "GetFileInformationByHandle"
  let info ← h.derefAs info "BY_HANDLE_FILE_INFORMATION"
  let .file number := file | WindowsHandles.invalid "GetFileInformationByHandle"
  let some fd ← h.handles.lookupFd number | WindowsHandles.invalid "GetFileInformationByHandle"
  Files.withDrop (do
    let result ← h.metadata fd
    let metadata ← match result with
      | .inl (.ok value) => pure (some value)
      | .inl (.error error) => IoError.setLastError h.errors (.host error) *> pure none
      | .inr _ => throw (.unsupported "GetFileInformationByHandle: non-file-backed metadata")
    let some metadata := metadata | return ← boolValue h false
    let size := h.length metadata
    let attributes ← h.constant (if h.fileType metadata == .directory then "FILE_ATTRIBUTE_DIRECTORY"
      else if h.fileType metadata == .regular then "FILE_ATTRIBUTE_ARCHIVE" else "FILE_ATTRIBUTE_DEVICE")
    let created ← timePair h metadata .created
    let accessed ← timePair h metadata .accessed
    let written ← timePair h metadata .modified
    h.writeFields #[("dwFileAttributes",attributes.toNat)] info
    writeTime h info "ftCreationTime" created
    writeTime h info "ftLastAccessTime" accessed
    writeTime h info "ftLastWriteTime" written
    h.writeFields #[("dwVolumeSerialNumber",0),("nFileSizeHigh",(size >>> 32).toNat),
      ("nFileSizeLow",(size &&& 0xffffffff).toNat),("nNumberOfLinks",1),("nFileIndexHigh",0),("nFileIndexLow",0)] info
    boolValue h true
  ) (h.handles.dropFd fd)

def setInformation (h : Hooks S F H D P HM T E) (file infoClass info size : OpTy Provenance) : M S (Scalar Provenance) := do
  target h "SetFileInformationByHandle"
  h.noIsolation "`SetFileInformationByHandle`"
  let infoClass ← h.handles.readU32 infoClass
  let size ← h.handles.readU32 size
  let info ← h.handles.readPointer info
  h.checkAccess info (Size.ofBytes size.toUInt64)
  let file ← WindowsHandles.read h.handles file "SetFileInformationByHandle"
  let .file number := file | WindowsHandles.invalid "SetFileInformationByHandle"
  let some fd ← h.handles.lookupFd number | WindowsHandles.invalid "SetFileInformationByHandle"
  Files.withDrop (do
    let some file := h.asFile fd | throw (.unsupported "SetFileInformationByHandle requires file-backed FD")
    if infoClass == (← h.constant "FileEndOfFileInfo") then
      let place ← h.ptrToPlace info "FILE_END_OF_FILE_INFO"
      let length ← h.readFieldI64 (← h.field place "EndOfFile")
      if length < 0 then throw (.invalidProgram "FileEndOfFileInfo length cannot convert u64")
      return ← finish h (← h.setLength file.handle length.toUInt64)
    else if infoClass == (← h.constant "FileAllocationInfo") then
      let place ← h.ptrToPlace info "FILE_ALLOCATION_INFO"
      let length ← h.readFieldI64 (← h.field place "AllocationSize")
      if length < 0 then throw (.invalidProgram "FileAllocationInfo size cannot convert u64")
      match ← h.fileLength file.handle with
      | .error error => IoError.setLastError h.errors (.host error); boolValue h false
      | .ok old =>
        if length.toUInt64 < old then finish h (← h.setLength file.handle length.toUInt64)
        else boolValue h true
    else throw (.unsupported "SetFileInformationByHandle: unsupported information infoClass")
  ) (h.handles.dropFd fd)

def flush (h : Hooks S F H D P HM T E) (operand : OpTy Provenance) : M S (Scalar Provenance) := do
  target h "FlushFileBuffers"
  let handle ← WindowsHandles.read h.handles operand "FlushFileBuffers"
  let .file number := handle | WindowsHandles.invalid "FlushFileBuffers"
  let some fd ← h.handles.lookupFd number | WindowsHandles.invalid "FlushFileBuffers"
  Files.withDrop (do
    let some file := h.asFile fd | throw (.unsupported "FlushFileBuffers requires file-backed FD")
    if !file.writable then
      IoError.setLastError h.errors (.windows "ERROR_ACCESS_DENIED")
      return ← boolValue h false
    finish h (← h.syncAll file.handle)
  ) (h.handles.dropFd fd)

def moveFile (h : Hooks S F H D P HM T E) (old new flags : OpTy Provenance) : M S (Scalar Provenance) := do
  let old ← h.readWidePath (← h.handles.readPointer old)
  let new ← h.readWidePath (← h.handles.readPointer new)
  let flags ← h.handles.readU32 flags
  if flags != (← h.constant "MOVEFILE_REPLACE_EXISTING") then throw (.unsupported "MoveFileExW: unsupported flags")
  finish h (← h.rename old new)

def deleteFile (h : Hooks S F H D P HM T E) (operand : OpTy Provenance) : M S (Scalar Provenance) := do
  target h "DeleteFileW"
  h.noIsolation "`DeleteFileW`"
  let name ← h.readWidePath (← h.handles.readPointer operand)
  finish h (← h.removeFile name)

/-- Read/write intentionally differ in whether status projection precedes FD
validation, including upstream's NtWriteFile diagnostic in the read branch. -/
def ntReadWrite (h : Hooks S F H D P HM T E) (write : Bool)
    (handle event routine context status buffer count offset key : OpTy Provenance)
    (dest : MPlaceTy Provenance) : M S Unit := do
  let name := if write then "NtWriteFile" else "NtReadFile"
  let handle ← WindowsHandles.read h.handles handle name
  let event ← WindowsHandles.read h.handles event name
  let routine ← h.handles.readPointer routine
  let context ← h.handles.readPointer context
  let buffer ← h.handles.readPointer buffer
  let count ← h.handles.readU32 count
  let offset ← h.readUsize offset
  let key ← h.handles.readPointer key
  let status ← h.derefAs status "IO_STATUS_BLOCK"
  if event != .null then throw (.unsupported s!"{name}: non-null event unsupported")
  if !(← h.handles.isNull routine) then throw (.unsupported s!"{name}: non-null ApcRoutine unsupported")
  if !(← h.handles.isNull context) then throw (.unsupported s!"{name}: non-null ApcContext unsupported")
  if offset != 0 then throw (.unsupported s!"{name}: non-null ByteOffset unsupported")
  if !(← h.handles.isNull key) then throw (.unsupported s!"{name}: non-null Key unsupported")
  let projected ← if write then pure none else do
    let statusField ← h.field (← h.field status "Anonymous") "Status"
    let infoField ← h.field status "Information"
    pure (some (statusField,infoField))
  let .file number := handle | WindowsHandles.invalid "NtWriteFile"
  let some fd ← h.handles.lookupFd number | WindowsHandles.invalid name
  -- Pass ownership only once status fields have been projected successfully.
  let (statusField,infoField) ← match projected with
    | some pair => pure pair
    | none =>
      let action := do
        let statusField ← h.field (← h.field status "Anonymous") "Status"
        let infoField ← h.field status "Information"
        pure (statusField,infoField)
      fun state => match action state with
        | .ok value state => .ok value state
        | .error error state => match h.handles.dropFd fd state with
          | .ok _ state => .error error state | .error next state => .error next state
  let finish : Files.Finish S E := IoCompletionData.Finish.source (.windowsNt count statusField infoField dest) fun result => do
    match result with
    | .ok size =>
      if size > count.toNat then throw (.invalidProgram s!"{name}: host count exceeds requested count")
      h.writeInt size infoField
      h.writeInt 0 statusField
      h.writeInt 0 dest
    | .error error =>
      h.writeInt 0 infoField
      let status := IoError.intoNtstatus error
      h.writeInt status.toInt statusField
      h.writeInt status.toInt dest
  h.readWrite fd h.communicate write buffer count.toNat finish

def setPointer (h : Hooks S F H D P HM T E) (operand distance newPointer method : OpTy Provenance) : M S (Scalar Provenance) := do
  let handle ← WindowsHandles.read h.handles operand "SetFilePointerEx"
  let distance ← h.readI64 distance
  let pointer ← h.handles.readPointer newPointer
  let method ← h.handles.readU32 method
  let .file number := handle | WindowsHandles.invalid "SetFilePointerEx"
  let some fd ← h.handles.lookupFd number | throw (.unsupported "SetFilePointerEx only supported on file-backed handles")
  Files.withDrop (do
    let start ← h.constant "FILE_BEGIN"
    let current ← h.constant "FILE_CURRENT"
    let finish ← h.constant "FILE_END"
    let seek ← if method == start then do
        if distance < 0 then throw (.invalidProgram "SetFilePointerEx negative FILE_BEGIN offset")
        pure (Files.SeekFrom.start distance.toUInt64)
      else if method == current then pure (.current distance)
      else if method == finish then pure (.finish distance)
      else throw (.unsupported "SetFilePointerEx invalid move method")
    match ← h.seek fd h.communicate seek with
    | .error error => IoError.setLastError h.errors error; boolValue h false
    | .ok offset =>
      if !(← h.handles.isNull pointer) then
        if offset > 9223372036854775807 then throw (.invalidProgram "SetFilePointerEx result exceeds i64")
        h.writeInt offset.toNat (← h.derefI64 newPointer)
      boolValue h true
  ) (h.handles.dropFd fd)
end Miri.Interpreter.WindowsFiles
