import Miri.Interpreter.UnixFd

/-! Pinned unix/fs.rs::open and files.rs::open_file_or_dir. Actual host path,
metadata, varargs and filesystem effects are required; flags are target queries. -/
namespace Miri.Interpreter.UnixOpen
open Miri.ABI Miri.Memory Files
abbrev M := EStateM StepError
inductive Flag where
  | readonly | writeonly | readwrite | accessMode | largefile | tmpfile | directory
  | append | trunc | create | exclusive | cloexec | nofollow | atCwd
  deriving DecidableEq, Repr
inductive ModeUse where | tmpfile | create deriving DecidableEq, Repr
structure Options where
  read : Bool := false
  write : Bool := false
  append : Bool := false
  truncate : Bool := false
  create : Bool := false
  createNew : Bool := false
  mode : Option UInt32 := none
  customFlags : UInt32 := 0
structure Metadata where
  isDirectory : Bool
  isSymlink : Bool
inductive Opened (H D : Type) where | file (handle : H) | directory (handle : D)
structure Hooks (S H D O E Meta Path : Type) where
  fd : UnixFd.Hooks S H D O E Meta
  hostWindows : Bool
  flag : Flag → M S UInt32
  hostCustomFlag : Flag → M S UInt32
  readMode : ModeUse → M S UInt32
  isolationReject : String → M S Bool
  procAbsolute : Path → M S Bool
  diagnoseProc : M S Unit
  isAbsolute : Path → Bool
  isEmpty : Path → Bool
  isDot : Path → Bool
  emptyPath : Path
  openFile : Option D → Path → Options → M S (Except (IoError.HostError E) H)
  openDirectoryAsFile : Option D → Path → Options → M S (Except (IoError.HostError E) H)
  metadata : H → M S (Except (IoError.HostError E) Metadata)
  asDirectory : H → M S D
  dropFile : H → M S Unit
  dropDirectory : D → M S Unit
  permissionDenied : M S (IoError.HostError E)
  hostUsizeBits : Nat
private def lift (value : Except StepError A) : M S A :=
  match value with | .ok value => pure value | .error error => throw error
private def fail (h : Hooks S H D O E Meta P) (name : String) : M S Int32 :=
  IoError.setErrnoAndReturnNeg1I32 h.fd.errors (.libc name)
private def flagSet (flags bit : UInt32) : Bool := flags &&& bit == bit
private def without (flags bit : UInt32) : UInt32 := flags &&& (~~~bit)
private def mode (h : Hooks S H D O E Meta P) (use : ModeUse) (options : Options) : M S Options := do
  let mode ← h.readMode use
  if h.hostWindows then
    if mode != 438 then throw (.unsupported "non-default open mode unsupported on non-Unix host")
    return options
  return { options with mode := some mode }

def openFileOrDir (h : Hooks S H D O E Meta P) (root : Option D) (path : P)
    (options : Options) : M S (Except (IoError.HostError E) (Opened H D)) := do
  let initial ← h.openFile root path options
  let file : Except (IoError.HostError E) H ← match initial with
    | .ok file => pure (.ok file)
    | .error original => do
      if !h.hostWindows || original.kind != .PermissionDenied then pure (.error original)
      else
        match ← h.openDirectoryAsFile root path options with
        | .ok file => pure (.ok file)
        | .error error => pure (.error (if error.kind == .NotADirectory then original else error))
  match file with
  | .error error => return .error error
  | .ok file =>
    let .ok metadata ← h.metadata file
      | h.dropFile file; throw (.invalidProgram "just-opened file should have metadata")
    if metadata.isDirectory then
      if metadata.isSymlink then
        h.dropFile file
        throw (.invalidProgram "directory metadata cannot be symlink")
      return .ok (.directory (← h.asDirectory file))
    return .ok (.file file)

def openPath (h : Hooks S H D O E Meta P) (dirfd : Option Int32) (path : P) (inputFlags : UInt32) : M S Int32 := do
  if #["linux","android","illumos","solaris"].contains h.fd.os then
    if ← h.procAbsolute path then h.diagnoseProc
  let mut flags := inputFlags
  let mut options : Options := {}
  let readonly ← h.flag .readonly
  let writeonly ← h.flag .writeonly
  let readwrite ← h.flag .readwrite
  if (readonly ||| writeonly ||| readwrite) &&& (~~~(3 : UInt32)) != 0 then
    throw (.unsupported "target access-mode flags exceed low2bits")
  let access := flags &&& (← h.flag .accessMode)
  flags := without flags access
  let mut readable := true
  let mut writable := true
  if access == readonly then
    writable := false
    options := { options with read := true }
  else if access == writeonly then
    readable := false
    options := { options with write := true }
  else if access == readwrite then options := { options with read := true, write := true }
  else throw (.unsupported "unsupported open access mode")
  if h.fd.os == "linux" then
    let bit ← h.flag .largefile
    if flagSet flags bit then flags := without flags bit
    let bit ← h.flag .tmpfile
    if flagSet flags bit then
      let _ ← mode h .tmpfile options
      return ← fail h "EOPNOTSUPP"
  let bit ← h.flag .directory
  let wantDirectory := flagSet flags bit
  if wantDirectory then
    flags := without flags bit
    if !h.hostWindows then options := { options with customFlags := options.customFlags ||| (← h.hostCustomFlag .directory) }
  let bit ← h.flag .append
  if flagSet flags bit then
    flags := without flags bit
    options := { options with append := true }
  let bit ← h.flag .trunc
  if flagSet flags bit then
    flags := without flags bit
    options := { options with truncate := true }
  let bit ← h.flag .create
  if flagSet flags bit then
    flags := without flags bit
    options ← mode h .create options
    if wantDirectory then return ← fail h "EINVAL"
    let bit ← h.flag .exclusive
    if flagSet flags bit then
      flags := without flags bit
      options := { options with createNew := true }
    else options := { options with create := true }
  let bit ← h.flag .cloexec
  if flagSet flags bit then flags := without flags bit
  let bit ← h.flag .nofollow
  let nofollow := flagSet flags bit
  if nofollow then
    flags := without flags bit
    if h.hostWindows && dirfd.isSome then throw (.unsupported "openat O_NOFOLLOW unsupported on Windows host")
    options := { options with customFlags := options.customFlags ||| (← h.hostCustomFlag .nofollow) }
  if flags != 0 then throw (.unsupported "unsupported open flags")
  if ← h.isolationReject (if dirfd.isSome then "openat" else "open") then
    return ← IoError.setErrnoAndReturnNeg1I32 h.fd.errors (.host (← h.permissionDenied))
  let rootResult : Except String (Option (Files.Ref (Description H D O))) ← match dirfd with
    | none => pure (.ok none)
    | some dirfd => do
      if h.isAbsolute path then pure (.ok none)
      else if dirfd.toUInt32 == (← h.flag .atCwd) then pure (.ok none)
      else
        match (← h.fd.table).get dirfd with
        | none => pure (.error "EBADF")
        | some ref =>
          let ref ← h.fd.cloneRef ref
          match ref.value with
          | .directory _ => pure (.ok (some ref))
          | _ => h.fd.dropRef ref; pure (.error "ENOTDIR")
  let .ok rootRef := rootResult
    | match rootResult with
      | .error error => fail h error
      | .ok _ => throw (.invalidProgram "open root result mismatch")
  let root : Option D := rootRef.bind fun ref => match ref.value with | .directory handle => some handle | _ => none
  let cleanup := match rootRef with | none => pure () | some ref => h.fd.dropRef ref
  let action : M S Int32 := do
    if h.isEmpty path then return ← fail h "ENOENT"
    let path := if h.hostWindows && root.isSome && h.isDot path then h.emptyPath else path
    match ← openFileOrDir h root path options with
    | .error error => IoError.setErrnoAndReturnNeg1I32 h.fd.errors (.host error)
    | .ok (.directory handle) =>
      if writable then
        h.dropDirectory handle
        return ← fail h "EISDIR"
      let ref ← h.fd.newReference (.directory handle)
      let (table,number) ← lift ((← h.fd.table).insert ref)
      h.fd.putTable table
      return number
    | .ok (.file handle) =>
      if wantDirectory then
        h.dropFile handle
        return ← fail h "ENOTDIR"
      let .ok metadata ← h.metadata handle
        | h.dropFile handle; throw (.invalidProgram "opened file metadata unexpectedly failed")
      if metadata.isSymlink then
        h.dropFile handle
        if nofollow then return ← fail h "ELOOP"
        throw (.invalidProgram "unexpected symlink from file open")
      let ref ← h.fd.newReference (.file handle readable writable)
      let (table,number) ← lift ((← h.fd.table).insert ref)
      h.fd.putTable table
      return number
  Files.withDrop action cleanup
end Miri.Interpreter.UnixOpen
