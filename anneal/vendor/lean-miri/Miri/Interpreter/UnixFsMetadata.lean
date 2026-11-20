import Miri.Interpreter.Files
import Miri.Interpreter.Clock

/-! FileMetadata and stat/statx core from pinned unix/fs.rs. Optional host-only
fields represent source absence, not unknown compiler metadata. -/
namespace Miri.Interpreter.UnixFsMetadata
open Miri.ABI Miri.Memory
abbrev M := EStateM StepError
inductive FileType where | regular | directory | symlink | socket | fifo | character | block | other
  deriving DecidableEq, Repr
inductive TimeField where | created | accessed | modified deriving DecidableEq, Repr
structure UnixFields where
  dev : UInt64
  ino : UInt64
  nlink : UInt64
  uid : UInt32
  gid : UInt32
  blksize : UInt64
  blocks : UInt64
  permissions : UInt32
structure Metadata where
  mode : UInt32
  size : UInt64
  created : Option (UInt64 × UInt32)
  accessed : Option (UInt64 × UInt32)
  modified : Option (UInt64 × UInt32)
  dev : Option UInt64
  ino : Option UInt64
  nlink : Option UInt64
  uid : Option UInt32
  gid : Option UInt32
  blksize : Option UInt64
  blocks : Option UInt64
structure Hooks (S F D Path HM Time E : Type) where
  os : String
  hostUnix : Bool
  hostWindows : Bool
  errors : IoError.Hooks S E
  libcI32 : String → M S Int32
  libcU32 : String → M S UInt32
  /-- eval_libc followed by mode_t-sized unsigned conversion and checked u32. -/
  libcMode : String → M S UInt32
  readI32 : OpTy Provenance → M S Int32
  readU32 : OpTy Provenance → M S UInt32
  readPointer : OpTy Provenance → M S (Pointer (Option Provenance))
  isNull : Pointer (Option Provenance) → M S Bool
  readPath : Pointer (Option Provenance) → M S Path
  isolationReject : String → M S Bool
  lookupFd : Int32 → M S (Option F)
  dropFd : F → M S Unit
  asDirectory : F → Option D
  fdMetadata : F → M S (Sum (Except (IoError.HostError E) HM) String)
  isEmpty : Path → Bool
  isAbsolute : Path → Bool
  isDot : Path → Bool
  emptyPath : Path
  metadata : Option D → Path → Bool → M S (Except (IoError.HostError E) HM)
  fileType : HM → FileType
  length : HM → UInt64
  time : HM → TimeField → M S (Except (IoError.HostError E) Time)
  /-- Actual system_time_to_duration: before epoch remains interpreter error. -/
  sinceEpoch : Time → M S Clock.Duration
  unixFields : HM → UnixFields
  readonly : HM → Bool
  deref : OpTy Provenance → M S (MPlaceTy Provenance)
  derefAs : OpTy Provenance → String → M S (MPlaceTy Provenance)
  writeFields : Array (String × Int) → MPlaceTy Provenance → M S Unit
  field : MPlaceTy Provenance → String → M S (MPlaceTy Provenance)
  index : MPlaceTy Provenance → UInt64 → M S (MPlaceTy Provenance)
  writeInt : Int → MPlaceTy Provenance → M S Unit

def modeName (hostUnix : Bool) : FileType → String
  | .regular => "S_IFREG" | .directory => "S_IFDIR" | .symlink => "S_IFLNK"
  | .socket => if hostUnix then "S_IFSOCK" else "S_IFREG"
  | .fifo => if hostUnix then "S_IFIFO" else "S_IFREG"
  | .character => if hostUnix then "S_IFCHR" else "S_IFREG"
  | .block => if hostUnix then "S_IFBLK" else "S_IFREG"
  | .other => "S_IFREG"
private def extractTime (h : Hooks S F D P HM T E) (metadata : HM) (field : TimeField) :
    M S (Option (UInt64 × UInt32)) := do
  match ← h.time metadata field with
  | .error _ => return none
  | .ok time =>
    let duration ← h.sinceEpoch time
    return some (duration.seconds,duration.nanos)

def synthetic (h : Hooks S F D P HM T E) (mode : String) : M S Metadata := do
  return ⟨(← h.libcMode mode) ||| 438,0,none,none,none,none,none,none,none,none,none,none⟩

def fromHost (h : Hooks S F D P HM T E) (metadata : Except (IoError.HostError E) HM) :
    M S (Except (IoError.Error E) Metadata) := do
  match metadata with
  | .error error => return .error (.host error)
  | .ok metadata =>
    let mode ← h.libcMode (modeName h.hostUnix (h.fileType metadata))
    let size := h.length metadata
    let created ← extractTime h metadata .created
    let accessed ← extractTime h metadata .accessed
    let modified ← extractTime h metadata .modified
    if h.hostUnix then
      let fields := h.unixFields metadata
      return .ok ⟨mode ||| fields.permissions,size,created,accessed,modified,
        some fields.dev,some fields.ino,some fields.nlink,some fields.uid,some fields.gid,
        some fields.blksize,some fields.blocks⟩
    return .ok ⟨mode ||| (if h.readonly metadata then 73 else 219),size,created,accessed,modified,
      none,none,none,none,none,none,none⟩

def fromFd (h : Hooks S F D P HM T E) (number : Int32) : M S (Except (IoError.Error E) Metadata) := do
  let some fd ← h.lookupFd number | return .error (.libc "EBADF")
  Files.withDrop (do
    match ← h.fdMetadata fd with
    | .inl host => fromHost h host
    | .inr name => return .ok (← synthetic h name)
  ) (h.dropFd fd)

def atPath (h : Hooks S F D P HM T E) (number : Int32) (path : P)
    (nofollow empty : Bool) : M S (Except (IoError.Error E) Metadata) := do
  if h.isEmpty path then
    if !empty then return .error (.libc "ENOENT")
    return ← fromFd h number
  let direct ← if h.isAbsolute path then pure true else do pure (number == (← h.libcI32 "AT_FDCWD"))
  if direct then return ← fromHost h (← h.metadata none path nofollow)
  let some fd ← h.lookupFd number | return .error (.libc "EBADF")
  Files.withDrop (do
    let some directory := h.asDirectory fd | return .error (.libc "ENOTDIR")
    let path := if h.hostWindows && h.isDot path then h.emptyPath else path
    fromHost h (← h.metadata (some directory) path nofollow)
  ) (h.dropFd fd)
private def val64 (v : Option UInt64) : Int := (v.getD 0).toNat
private def val32 (v : Option UInt32) : Int := (v.getD 0).toNat

def writeStat (h : Hooks S F D P HM T E) (metadata : Metadata) (buf : OpTy Provenance) : M S Int32 := do
  let access := metadata.accessed.getD (0,0)
  let created := metadata.created.getD (0,0)
  let modified := metadata.modified.getD (0,0)
  let place ← h.deref buf
  h.writeFields #[("st_dev",val64 metadata.dev),("st_mode",metadata.mode.toNat),
    ("st_nlink",val64 metadata.nlink),("st_ino",val64 metadata.ino),("st_uid",val32 metadata.uid),
    ("st_gid",val32 metadata.gid),("st_rdev",0),("st_atime",access.1.toNat),
    ("st_atime_nsec",access.2.toNat),("st_mtime",modified.1.toNat),("st_mtime_nsec",modified.2.toNat),
    ("st_ctime",0),("st_ctime_nsec",0),("st_size",metadata.size.toNat),
    ("st_blocks",val64 metadata.blocks),("st_blksize",val64 metadata.blksize)] place
  if h.os == "macos" || h.os == "freebsd" then
    h.writeFields #[("st_birthtime",created.1.toNat),("st_birthtime_nsec",created.2.toNat),("st_flags",0),("st_gen",0)] place
  if h.os == "solaris" || h.os == "illumos" then
    h.writeInt 0 (← h.index (← h.field place "st_fstype") 0)
  return 0
private def supported (h : Hooks S F D P HM T E) : M S Unit := do
  if !(#["macos","freebsd","solaris","illumos","android","linux"].contains h.os) then
    throw (.invalidProgram "stat called on unsupported source target")
private def finish (h : Hooks S F D P HM T E) (metadata : Except (IoError.Error E) Metadata)
    (buf : OpTy Provenance) : M S Int32 := do
  match metadata with
  | .error error => IoError.setErrnoAndReturnNeg1I32 h.errors error
  | .ok metadata => writeStat h metadata buf

def stat (h : Hooks S F D P HM T E) (path buf : OpTy Provenance) (nofollow : Bool) : M S Int32 := do
  supported h
  let path ← h.readPath (← h.readPointer path)
  if ← h.isolationReject (if nofollow then "`lstat`" else "`stat`") then
    return ← IoError.setErrnoAndReturnNeg1I32 h.errors (.libc "EACCES")
  finish h (← fromHost h (← h.metadata none path nofollow)) buf

def fstat (h : Hooks S F D P HM T E) (fd buf : OpTy Provenance) : M S Int32 := do
  supported h
  let fd ← h.readI32 fd
  if ← h.isolationReject "`fstat`" then return ← IoError.setErrnoAndReturnNeg1I32 h.errors (.libc "EBADF")
  finish h (← fromFd h fd) buf

def fstatat (h : Hooks S F D P HM T E) (fd path buf flags : OpTy Provenance) : M S Int32 := do
  supported h
  let fd ← h.readI32 fd
  let path ← h.readPointer path
  let flags ← h.readI32 flags
  if ← h.isolationReject "`fstatat`" then return ← IoError.setErrnoAndReturnNeg1I32 h.errors (.libc "EACCES")
  let nofollow ← h.libcI32 "AT_SYMLINK_NOFOLLOW"
  let selected := flags &&& nofollow == nofollow
  if flags &&& ~~~nofollow != 0 then throw (.unsupported "unsupported flags for fstatat")
  let path ← h.readPath path
  finish h (← atPath h fd path selected false) buf

def statx (h : Hooks S F D P HM T E) (fd pathname flags mask buf : OpTy Provenance) : M S Int32 := do
  if h.os != "linux" then throw (.invalidProgram "statx requires Linux target")
  let fd ← h.readI32 fd
  let pathname ← h.readPointer pathname
  let flags ← h.readI32 flags
  let _ ← h.readU32 mask
  let buffer ← h.readPointer buf
  let null ← if ← h.isNull buffer then pure true else h.isNull pathname
  if null then return ← IoError.setErrnoAndReturnNeg1I32 h.errors (.libc "EFAULT")
  let place ← h.derefAs buf "statx"
  let path ← h.readPath pathname
  let empty ← h.libcI32 "AT_EMPTY_PATH"
  let useEmpty := flags &&& empty == empty
  let flags := flags &&& ~~~empty
  let nofollow ← h.libcI32 "AT_SYMLINK_NOFOLLOW"
  let useNofollow := flags &&& nofollow == nofollow
  if flags &&& ~~~nofollow != 0 then throw (.unsupported "unsupported flags for statx")
  if ← h.isolationReject "`statx`" then return ← IoError.setErrnoAndReturnNeg1I32 h.errors (.libc "EACCES")
  let result ← atPath h fd path useNofollow useEmpty
  let .ok metadata := result | match result with
    | .error error => return ← IoError.setErrnoAndReturnNeg1I32 h.errors error
    | .ok _ => throw (.invalidProgram "unreachable successful metadata pattern")
  let mut mask ← h.libcU32 "STATX_TYPE"
  mask := mask ||| (← h.libcU32 "STATX_MODE")
  mask := mask ||| (← h.libcU32 "STATX_SIZE")
  for (present,name) in #[(metadata.ino.isSome,"STATX_INO"),(metadata.nlink.isSome,"STATX_NLINK"),
      (metadata.uid.isSome,"STATX_UID"),(metadata.gid.isSome,"STATX_GID"),(metadata.blocks.isSome,"STATX_BLOCKS"),
      (metadata.accessed.isSome,"STATX_ATIME"),(metadata.created.isSome,"STATX_BTIME"),(metadata.modified.isSome,"STATX_MTIME")] do
    if present then mask := mask ||| (← h.libcU32 name)
  let access := metadata.accessed.getD (0,0)
  let created := metadata.created.getD (0,0)
  let modified := metadata.modified.getD (0,0)
  h.writeFields #[("stx_mask",mask.toNat),("stx_mode",metadata.mode.toNat),("stx_blksize",val64 metadata.blksize),
    ("stx_attributes",0),("stx_nlink",val64 metadata.nlink),("stx_uid",val32 metadata.uid),("stx_gid",val32 metadata.gid),
    ("stx_ino",val64 metadata.ino),("stx_size",metadata.size.toNat),("stx_blocks",val64 metadata.blocks),
    ("stx_attributes_mask",0),("stx_rdev_major",0),("stx_rdev_minor",0),("stx_dev_major",0),("stx_dev_minor",0)] place
  for (name,time) in #[("stx_atime",access),("stx_btime",created),("stx_ctime",(0,0)),("stx_mtime",modified)] do
    h.writeFields #[("tv_sec",time.1.toNat),("tv_nsec",time.2.toNat)] (← h.field place name)
  return 0
end Miri.Interpreter.UnixFsMetadata
