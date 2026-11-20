import Miri.Interpreter.UnixFsPaths

/-! Remaining regular-file length/permissions/seek/sync policy in unix/fs.rs.
Strong FD lookup/drop and actual host effects are mandatory. -/
namespace Miri.Interpreter.UnixFsFd
open Miri.ABI Miri.Memory
abbrev M := EStateM StepError
structure File (H : Type) where
  handle : H
  readable : Bool
  writable : Bool
structure Hooks (S F D Path HM Time E Kind H : Type) where
  paths : UnixFsPaths.Hooks S F D Path HM Time E Kind
  communicate : Bool
  asFile : F → Option (File H)
  seek : F → Bool → Files.SeekFrom → M S (Except (IoError.Error E) UInt64)
  isTty : F → Bool → M S Bool
  setLength : H → UInt64 → M S (Except (IoError.HostError E) Unit)
  fileLength : H → M S (Except (IoError.HostError E) UInt64)
  setPermissions : H → UInt32 → M S (Except (IoError.HostError E) Unit)
  /-- False = File::sync_all, true = File::sync_data, not a success acknowledgement. -/
  sync : H → Bool → M S (Except (IoError.HostError E) Unit)
private def fail (h : Hooks S F D P HM T E K H) (name : String) : M S Int32 :=
  IoError.setErrnoAndReturnNeg1I32 h.paths.metadata.errors (.libc name)
private def communicate (h : Hooks S F D P HM T E K H) : M S Unit := do
  if !h.communicate then throw (.invalidProgram "isolation should have prevented opening host file")
private def finish (h : Hooks S F D P HM T E K H) (result : Except (IoError.HostError E) Unit) : M S Int32 :=
  IoError.tryUnwrap h.paths.metadata.errors (result.map fun _ => (0 : Int32)) (-1)

def truncate (h : Hooks S F D P HM T E K H) (number : Int32) (length : Int) : M S Int32 := do
  let some fd ← h.paths.metadata.lookupFd number | return ← fail h "EBADF"
  Files.withDrop (do
    let some file := h.asFile fd | return ← fail h "EINVAL"
    if !file.writable then return ← fail h "EINVAL"
    communicate h
    if length < 0 || length > 18446744073709551615 then return ← fail h "EINVAL"
    finish h (← h.setLength file.handle (UInt64.ofNat length.toNat))
  ) (h.paths.metadata.dropFd fd)

def chmod (h : Hooks S F D P HM T E K H) (number mode : OpTy Provenance) : M S Int32 := do
  let number ← h.paths.metadata.readI32 number
  let mode ← h.paths.readMode mode
  let some fd ← h.paths.metadata.lookupFd number | return ← fail h "EBADF"
  Files.withDrop (do
    let some file := h.asFile fd | throw (.unsupported "fchmod only supported on regular files")
    if !file.writable && !file.readable then return ← fail h "EBADF"
    communicate h
    if !h.paths.metadata.hostUnix then throw (.unsupported "setting permissions requires Unix host")
    finish h (← h.setPermissions file.handle mode)
  ) (h.paths.metadata.dropFd fd)

def seek (h : Hooks S F D P HM T E K H) (number : Int32) (offset : Int) (whence : Int32)
    (dest : MPlaceTy Provenance) : M S Unit := do
  let origin ← if whence == (← h.paths.metadata.libcI32 "SEEK_SET") then do
      if offset < 0 then pure none
      else if offset > 18446744073709551615 then throw (.invalidProgram "seek offset exceeds u64")
      else pure (some (Files.SeekFrom.start (UInt64.ofNat offset.toNat)))
    else if whence == (← h.paths.metadata.libcI32 "SEEK_CUR") then do
      if offset < -9223372036854775808 || offset > 9223372036854775807 then throw (.invalidProgram "seek offset exceeds i64")
      pure (some (.current (Int64.ofInt offset)))
    else if whence == (← h.paths.metadata.libcI32 "SEEK_END") then do
      if offset < -9223372036854775808 || offset > 9223372036854775807 then throw (.invalidProgram "seek offset exceeds i64")
      pure (some (.finish (Int64.ofInt offset)))
    else pure none
  let some origin := origin | IoError.setErrnoAndReturnNeg1 h.paths.metadata.errors (.libc "EINVAL") dest; return
  let some fd ← h.paths.metadata.lookupFd number | IoError.setErrnoAndReturnNeg1 h.paths.metadata.errors (.libc "EBADF") dest; return
  let result : Except (IoError.Error E) UInt64 ← Files.withDrop (do
    let result ← h.seek fd h.communicate origin
    match result with
    | .error error => pure (.error error)
    | .ok offset =>
      if offset > 9223372036854775807 then throw (.invalidProgram "host seek result exceeds i64")
      pure (.ok offset)
  ) (h.paths.metadata.dropFd fd)
  match result with
  | .error error => IoError.setErrnoAndReturnNeg1 h.paths.metadata.errors error dest
  | .ok offset => h.paths.metadata.writeInt offset.toNat dest

def allocateImpl (h : Hooks S F D P HM T E K H) (number : Int32) (offset length : Int64) :
    M S (Except (IoError.Error E) Unit) := do
  if offset < 0 || length <= 0 then return .error (.libc "EINVAL")
  let some fd ← h.paths.metadata.lookupFd number | return .error (.libc "EBADF")
  Files.withDrop (do
    let some file := h.asFile fd | return .error (.libc "ENODEV")
    if !file.writable then return .error (.libc "EBADF")
    let result ← h.fileLength file.handle
    let .ok current := result | match result with
      | .error error => return .error (.host error)
      | .ok _ => throw (.invalidProgram "unreachable host length pattern")
    let total := offset.toInt + length.toInt
    if total > 9223372036854775807 then return .error (.libc "EFBIG")
    let total := UInt64.ofNat total.toNat
    if current < total then return (← h.setLength file.handle total).mapError .host
    return .ok ()
  ) (h.paths.metadata.dropFd fd)

def posixAllocate (h : Hooks S F D P HM T E K H) (number : Int32) (offset length : Int64) : M S (Scalar Provenance) := do
  if ← h.paths.metadata.isolationReject "`posix_fallocate`" then return ← h.paths.metadata.errors.libc "EBADF"
  match ← allocateImpl h number offset length with
  | .error error => IoError.toErrnum h.paths.metadata.errors error
  | .ok _ =>
    match Scalar.fromInt 0 (Size.ofBytes 4) with
    | .ok scalar => return scalar
    | .error _ => throw (.invalidProgram "i32 zero scalar construction failed")

def linuxAllocate (h : Hooks S F D P HM T E K H) (number mode : Int32) (offset length : Int64) : M S Int32 := do
  if ← h.paths.metadata.isolationReject "`fallocate`" then return ← fail h "EBADF"
  if mode != 0 then throw (.unsupported "unsupported fallocate mode")
  match ← allocateImpl h number offset length with
  | .ok _ => return 0
  | .error error => IoError.setErrnoAndReturnNeg1I32 h.paths.metadata.errors error

def syncFile (h : Hooks S F D P HM T E K H) (number : Int32) (dataOnly : Bool) : M S Int32 := do
  let some fd ← h.paths.metadata.lookupFd number | return ← fail h "EBADF"
  Files.withDrop (do
    let some file := h.asFile fd | throw (.unsupported "file synchronization requires file-backed FD")
    communicate h
    if !file.writable && h.paths.metadata.hostWindows then return 0
    finish h (← h.sync file.handle dataOnly)
  ) (h.paths.metadata.dropFd fd)

def syncRange (h : Hooks S F D P HM T E K H) (number : Int32) (offset count : Int64) (flags : Int32) : M S Int32 := do
  if offset < 0 || count < 0 then return ← fail h "EINVAL"
  let before ← h.paths.metadata.libcI32 "SYNC_FILE_RANGE_WAIT_BEFORE"
  let write ← h.paths.metadata.libcI32 "SYNC_FILE_RANGE_WRITE"
  let after ← h.paths.metadata.libcI32 "SYNC_FILE_RANGE_WAIT_AFTER"
  if flags &&& (before ||| write ||| after) != flags then return ← fail h "EINVAL"
  syncFile h number true

def isatty (h : Hooks S F D P HM T E K H) (op : OpTy Provenance) : M S Int32 := do
  let number ← h.paths.metadata.readI32 op
  let error ← match ← h.paths.metadata.lookupFd number with
    | none => pure "EBADF"
    | some fd => do
      let terminal ← Files.withDrop (h.isTty fd h.communicate) (h.paths.metadata.dropFd fd)
      pure (if terminal then "" else "ENOTTY")
  if error == "" then return 1
  IoError.setLastError h.paths.metadata.errors (.libc error)
  return 0
end Miri.Interpreter.UnixFsFd
