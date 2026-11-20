import Miri.Interpreter.UnixFsMetadata
import Miri.Interpreter.OsStrings

/-! Pinned unix/fs.rs path mutations, readlink and realpath. Real filesystem
operations are typed effects; no virtual or guessed host filesystem is supplied. -/
namespace Miri.Interpreter.UnixFsPaths
open Miri.ABI Miri.Memory
abbrev M := EStateM StepError
structure Hooks (S F D Path HM Time E Kind : Type) where
  metadata : UnixFsMetadata.Hooks S F D Path HM Time E
  strings : OsStrings.Hooks Provenance S Path Kind
  cKind : Kind
  readMode : OpTy Provenance → M S UInt32
  readU16 : OpTy Provenance → M S UInt16
  readUsize : OpTy Provenance → M S UInt64
  writeBytes : Pointer (Option Provenance) → ByteArray → M S Unit
  /-- Host path::absolute(...).is_ok_and(starts_with("/proc")); errors map false. -/
  procAbsolute : Path → M S Bool
  pathToString : Path → Option String
  currentExe : M S (Option Path)
  hostUsizeBits : Nat
  removeFile : Path → M S (Except (IoError.HostError E) Unit)
  removeDirectory : Path → M S (Except (IoError.HostError E) Unit)
  symlinkDirectory : Path → M S Bool
  /-- Windows link.parent().is_some_and(parent.join(target).is_dir()). -/
  linkTargetDirectory : Path → Path → M S Bool
  createSymlink : Path → Path → Bool → M S (Except (IoError.HostError E) Unit)
  hardLink : Path → Path → M S (Except (IoError.HostError E) Unit)
  setPermissions : Path → UInt32 → M S (Except (IoError.HostError E) Unit)
  rename : Path → Path → M S (Except (IoError.HostError E) Unit)
  mkdir : Path → Option UInt32 → M S (Except (IoError.HostError E) Unit)
  readLink : Path → M S (Except (IoError.HostError E) Path)
  canonicalize : Path → M S (Except (IoError.HostError E) Path)
private def convert (h : Hooks S F D P HM T E K) (direction : OsStrings.Direction) (path : P) : M S P :=
  match OsStrings.convertPath h.strings path direction with
  | .ok path => pure path
  | .error error => throw error
private def fail (h : Hooks S F D P HM T E K) (name : String) : M S Int32 :=
  IoError.setErrnoAndReturnNeg1I32 h.metadata.errors (.libc name)
private def denied (h : Hooks S F D P HM T E K) : M S Int32 := do
  IoError.setErrnoAndReturnNeg1I32 h.metadata.errors (.host (← h.metadata.errors.hostFromKind .PermissionDenied))
private def finish (h : Hooks S F D P HM T E K) (result : Except (IoError.HostError E) Unit) : M S Int32 :=
  IoError.tryUnwrap h.metadata.errors (result.map fun _ => (0 : Int32)) (-1)
private def path (h : Hooks S F D P HM T E K) (op : OpTy Provenance) : M S P := do
  h.metadata.readPath (← h.metadata.readPointer op)

def unlink (h : Hooks S F D P HM T E K) (op : OpTy Provenance) : M S Int32 := do
  let path ← path h op
  if ← h.metadata.isolationReject "`unlink`" then return ← denied h
  if h.metadata.hostWindows then
    if ← h.symlinkDirectory path then return ← finish h (← h.removeDirectory path)
  finish h (← h.removeFile path)

def rmdir (h : Hooks S F D P HM T E K) (op : OpTy Provenance) : M S Int32 := do
  let path ← path h op
  if ← h.metadata.isolationReject "`rmdir`" then return ← denied h
  if h.metadata.hostWindows then
    if ← h.symlinkDirectory path then return ← fail h "ENOTDIR"
  finish h (← h.removeDirectory path)

def symlink (h : Hooks S F D P HM T E K) (target link : OpTy Provenance) : M S Int32 := do
  let target ← path h target
  let link ← path h link
  if ← h.metadata.isolationReject "`symlink`" then return ← denied h
  let directory ← if h.metadata.hostWindows then h.linkTargetDirectory link target else pure false
  finish h (← h.createSymlink target link directory)

def linkat (h : Hooks S F D P HM T E K) (oldfd oldpath newfd newpath flags : OpTy Provenance) : M S Int32 := do
  let flags ← h.metadata.readI32 flags
  let oldfd ← h.metadata.readI32 oldfd
  let newfd ← h.metadata.readI32 newfd
  let oldptr ← h.metadata.readPointer oldpath
  let newptr ← h.metadata.readPointer newpath
  let cwd ← h.metadata.libcI32 "AT_FDCWD"
  if ← h.metadata.isolationReject "`linkat`" then return ← denied h
  if flags != 0 then throw (.unsupported "unsupported linkat flags")
  if oldfd != cwd then throw (.unsupported "linkat olddirfd must equal AT_FDCWD")
  if ← h.metadata.isNull oldptr then return ← fail h "EFAULT"
  let oldpath ← h.metadata.readPath oldptr
  if newfd != cwd then throw (.unsupported "linkat newdirfd must equal AT_FDCWD")
  if ← h.metadata.isNull newptr then return ← fail h "EFAULT"
  let newpath ← h.metadata.readPath newptr
  finish h (← h.hardLink oldpath newpath)

def chmod (h : Hooks S F D P HM T E K) (op mode : OpTy Provenance) : M S Int32 := do
  let pointer ← h.metadata.readPointer op
  let mode ← h.readMode mode
  if ← h.metadata.isNull pointer then return ← fail h "EFAULT"
  let path ← h.metadata.readPath pointer
  if ← h.metadata.isolationReject "`chmod`" then return ← fail h "EACCES"
  if !h.metadata.hostUnix then throw (.unsupported "setting file permissions requires Unix host")
  finish h (← h.setPermissions path mode)

def rename (h : Hooks S F D P HM T E K) (oldpath newpath : OpTy Provenance) : M S Int32 := do
  let oldptr ← h.metadata.readPointer oldpath
  let newptr ← h.metadata.readPointer newpath
  let null ← if ← h.metadata.isNull oldptr then pure true else h.metadata.isNull newptr
  if null then return ← fail h "EFAULT"
  let oldpath ← h.metadata.readPath oldptr
  let newpath ← h.metadata.readPath newptr
  if ← h.metadata.isolationReject "`rename`" then return ← denied h
  finish h (← h.rename oldpath newpath)

def mkdir (h : Hooks S F D P HM T E K) (op mode : OpTy Provenance) : M S Int32 := do
  let mode ← if h.metadata.os == "macos" || h.metadata.os == "freebsd" then
    (h.readU16 mode).map UInt16.toUInt32 else h.metadata.readU32 mode
  let path ← path h op
  if ← h.metadata.isolationReject "`mkdir`" then return ← denied h
  finish h (← h.mkdir path (if h.metadata.hostUnix then some mode else none))

def readlink (h : Hooks S F D P HM T E K) (op buffer size : OpTy Provenance) : M S Int64 := do
  let pathname ← OsStrings.readOsString h.strings (← h.metadata.readPointer op)
  let buffer ← h.metadata.readPointer buffer
  let size ← h.readUsize size
  if ← h.metadata.isolationReject "`readlink`" then
    IoError.setLastError h.metadata.errors (.libc "EACCES")
    return -1
  let selfExe := if h.metadata.os == "linux" || h.metadata.os == "android" then some "/proc/self/exe"
    else if h.metadata.os == "solaris" || h.metadata.os == "illumos" then some "/proc/self/path/a.out" else none
  let result ← if selfExe.isSome && h.pathToString pathname == selfExe then do
      match ← h.currentExe with
      | some path => pure (.ok path)
      | none => pure (.error (← h.metadata.errors.hostFromKind .NotFound))
    else do
      if #["linux","android","illumos","solaris"].contains h.metadata.os then
        if ← h.procAbsolute pathname then
          pure (.error (← h.metadata.errors.hostFromKind .NotFound))
        else h.readLink (← convert h .targetToHost pathname)
      else h.readLink (← convert h .targetToHost pathname)
  match result with
  | .error error => IoError.setLastError h.metadata.errors (.host error); return -1
  | .ok resolved =>
    let resolved ← convert h .hostToTarget resolved
    let bytes := h.strings.encodedBytes resolved
    if size.toNat >= 2^h.hostUsizeBits then throw (.invalidProgram "readlink buffer size exceeds host usize")
    let bytes := bytes.extract 0 (min bytes.size size.toNat)
    h.writeBytes buffer bytes
    if bytes.size > 9223372036854775807 then throw (.invalidProgram "readlink result exceeds i64")
    return Int64.ofInt bytes.size

def realpath (h : Hooks S F D P HM T E K) (op processed : OpTy Provenance) :
    M S (Pointer (Option Provenance)) := do
  if h.metadata.errors.family != .unix then throw (.invalidProgram "realpath requires Unix target")
  let pathname ← path h op
  let processed ← h.metadata.readPointer processed
  if ← h.metadata.isolationReject "`realpath`" then
    IoError.setLastError h.metadata.errors (.libc "EACCES")
    return Pointer.null
  match ← h.canonicalize pathname with
  | .error error => IoError.setLastError h.metadata.errors (.host error); return Pointer.null
  | .ok resolved =>
    let maximum ← h.metadata.libcI32 "PATH_MAX"
    if maximum < 0 then throw (.invalidProgram "PATH_MAX does not fit u64")
    if ← h.metadata.isNull processed then
      return ← OsStrings.allocPath h.strings resolved h.cKind
    let (complete,_) ← OsStrings.writePath h.strings resolved processed maximum.toUInt32.toUInt64
    if !complete then
      IoError.setLastError h.metadata.errors (.libc "ENAMETOOLONG")
      return Pointer.null
    return processed
end Miri.Interpreter.UnixFsPaths
