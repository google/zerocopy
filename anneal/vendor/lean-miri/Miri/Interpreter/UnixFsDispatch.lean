import Miri.Interpreter.UnixDirectories
import Miri.Interpreter.UnixFsTimes
import Miri.Interpreter.UnixFileOperations
import Miri.Interpreter.UnixTempFile

/-! Source Unix and selected OS filesystem dispatch. Expected ABI records come
from compiler types including mode_t/off_t/stat/stat64, never type-by-size guesses. -/
namespace Miri.Interpreter.UnixFsDispatch
open Miri.ABI Miri.Memory
abbrev M := EStateM StepError
inductive Operation where
  | unlink | symlink | linkat | stat | lstat | fstat | fstatat | statx | chmod | fchmod
  | rename | mkdir | rmdir | opendir | readdir | dirfd | closedir | seek | truncate
  | fsync | fdatasync | futimens | utimensat | readlink | advise | posixAllocate | allocate
  | syncRange | realpath | mkstemp | isatty | flock
  deriving DecidableEq, Repr
inductive ArgType where
  | pointer | i32 | usize | isize | modeT | offT | off64T | statPointer | stat64Pointer
  deriving DecidableEq, Repr
structure Signature where
  args : Array ArgType
  ret : ArgType
structure Request where
  operation : Operation
  signature : Signature
  legacy : Bool := false
  dirent : String := "dirent"
  /-- Whether offset operands use literal to_i64 rather than layout-sized to_int. -/
  directI64 : Bool := false
private def common : String → Option Request
  | "unlink" => some {operation := .unlink, signature := ⟨#[.pointer],.i32⟩}
  | "symlink" => some {operation := .symlink, signature := ⟨#[.pointer,.pointer],.i32⟩}
  | "linkat" => some {operation := .linkat, signature := ⟨#[.i32,.pointer,.i32,.pointer,.i32],.i32⟩}
  | "stat" => some {operation := .stat, signature := ⟨#[.pointer,.statPointer],.i32⟩}
  | "lstat" => some {operation := .lstat, signature := ⟨#[.pointer,.statPointer],.i32⟩}
  | "fstat" => some {operation := .fstat, signature := ⟨#[.i32,.statPointer],.i32⟩}
  | "fstatat" => some {operation := .fstatat, signature := ⟨#[.i32,.pointer,.statPointer,.i32],.i32⟩}
  | "chmod" => some {operation := .chmod, signature := ⟨#[.pointer,.modeT],.i32⟩}
  | "fchmod" => some {operation := .fchmod, signature := ⟨#[.i32,.modeT],.i32⟩}
  | "rename" => some {operation := .rename, signature := ⟨#[.pointer,.pointer],.i32⟩}
  | "mkdir" => some {operation := .mkdir, signature := ⟨#[.pointer,.modeT],.i32⟩}
  | "rmdir" => some {operation := .rmdir, signature := ⟨#[.pointer],.i32⟩}
  | "opendir" => some {operation := .opendir, signature := ⟨#[.pointer],.pointer⟩}
  | "readdir" => some {operation := .readdir, signature := ⟨#[.pointer],.pointer⟩}
  | "dirfd" => some {operation := .dirfd, signature := ⟨#[.pointer],.i32⟩}
  | "closedir" => some {operation := .closedir, signature := ⟨#[.pointer],.i32⟩}
  | "lseek" => some {operation := .seek, signature := ⟨#[.i32,.offT,.i32],.offT⟩}
  | "ftruncate" => some {operation := .truncate, signature := ⟨#[.i32,.offT],.i32⟩}
  | "fsync" => some {operation := .fsync, signature := ⟨#[.i32],.i32⟩}
  | "fdatasync" => some {operation := .fdatasync, signature := ⟨#[.i32],.i32⟩}
  | "futimens" => some {operation := .futimens, signature := ⟨#[.i32,.pointer],.i32⟩}
  | "utimensat" => some {operation := .utimensat, signature := ⟨#[.i32,.pointer,.pointer,.i32],.i32⟩}
  | "readlink" => some {operation := .readlink, signature := ⟨#[.pointer,.pointer,.usize],.isize⟩}
  | "posix_fadvise" => some {operation := .advise, signature := ⟨#[.i32,.offT,.offT,.i32],.i32⟩}
  | "posix_fallocate" => some {operation := .posixAllocate, signature := ⟨#[.i32,.offT,.offT],.i32⟩}
  | "realpath" => some {operation := .realpath, signature := ⟨#[.pointer,.pointer],.pointer⟩}
  | "mkstemp" => some {operation := .mkstemp, signature := ⟨#[.pointer],.i32⟩}
  | "flock" => some {operation := .flock, signature := ⟨#[.i32,.i32],.i32⟩}
  | "isatty" => some {operation := .isatty, signature := ⟨#[.i32],.i32⟩}
  | _ => none

def parse (os name : String) : Option Request :=
  if let some request := common name then some request
  else if os == "linux" || os == "android" then
    match name with
    | "lseek64" => some {operation := .seek, signature := ⟨#[.i32,.off64T,.i32],.off64T⟩}
    | "ftruncate64" => some {operation := .truncate, signature := ⟨#[.i32,.off64T],.i32⟩}
    | "fstat64" => if os == "linux" then some {operation := .fstat, signature := ⟨#[.i32,.stat64Pointer],.i32⟩} else none
    | "readdir64" => if os == "linux" then some {operation := .readdir, signature := ⟨#[.pointer],.pointer⟩, legacy := true, dirent := "dirent64"} else none
    | "statx" => if os == "linux" then some {operation := .statx, signature := ⟨#[.i32,.pointer,.i32,.i32,.pointer],.i32⟩, legacy := true} else none
    | "sync_file_range" => if os == "linux" then some {operation := .syncRange, signature := ⟨#[.i32,.off64T,.off64T,.i32],.i32⟩, legacy := true} else none
    | "posix_fallocate64" => if os == "linux" then some {operation := .posixAllocate, signature := ⟨#[.i32,.off64T,.off64T],.i32⟩, legacy := false, dirent := "dirent", directI64 := true} else none
    | "fallocate" => if os == "linux" then some {operation := .allocate, signature := ⟨#[.i32,.i32,.offT,.offT],.i32⟩} else none
    | "fallocate64" => if os == "linux" then some {operation := .allocate, signature := ⟨#[.i32,.i32,.off64T,.off64T],.i32⟩, legacy := false, dirent := "dirent", directI64 := true} else none
    | _ => none
  else if os == "macos" then
    match name with
    | "stat$INODE64" => some {operation := .stat, signature := ⟨#[.pointer,.statPointer],.i32⟩, legacy := true}
    | "lstat$INODE64" => some {operation := .lstat, signature := ⟨#[.pointer,.statPointer],.i32⟩, legacy := true}
    | "fstat$INODE64" => some {operation := .fstat, signature := ⟨#[.i32,.statPointer],.i32⟩}
    | "fstatat$INODE64" => some {operation := .fstatat, signature := ⟨#[.i32,.pointer,.statPointer,.i32],.i32⟩}
    | "opendir$INODE64" => some {operation := .opendir, signature := ⟨#[.pointer],.pointer⟩, legacy := true}
    | "readdir$INODE64" => some {operation := .readdir, signature := ⟨#[.pointer],.pointer⟩, legacy := true}
    | "realpath$DARWIN_EXTSN" => some {operation := .realpath, signature := ⟨#[.pointer,.pointer],.pointer⟩, legacy := true}
    | _ => none
  else none
structure Hooks (S F D Path HM Time E Kind H ReadDir Entry : Type) where
  directories : UnixDirectories.Hooks S F D Path HM Time E Kind ReadDir Entry
  times : UnixFsTimes.Hooks S F D Path HM Time E Kind H
  temporary : UnixTempFile.Hooks S F D Path HM Time E Kind H
  /-- Query the compiler ABI by the exact source symbol. The locally parsed
  Signature only supplies the source argument-shape checks; it is never used
  to guess a rustc ABI. -/
  expectedAbi : String → Signature → M S (FnAbi Miri.MIR.TyId)
  argumentCompat : ArgAbi Miri.MIR.TyId → ArgAbi Miri.MIR.TyId → M S Bool
  checkSymbolClash : String → M S Unit
  transmute : OpTy Provenance → TyAndLayout Miri.MIR.TyId → M S (OpTy Provenance)
  readSignedAtLayout : OpTy Provenance → M S Int
  readI64 : OpTy Provenance → M S Int64
  writeScalar : Scalar Provenance → MPlaceTy Provenance → M S Unit
  writeUsize : UInt64 → MPlaceTy Provenance → M S Unit
  flock : F → Bool → UnixFileOperations.LockOp → M S (Except (IoError.HostError E) Unit)
  communicate : Bool
  pollAndUnblockZero : M S Unit
private def arg (args : Array A) (index : Nat) : M S A :=
  match args[index]? with | some value => pure value | none => throw (.invalidProgram "checked filesystem argument missing")
private def checked (h : Hooks S F D P HM T E K H R Ent) (request : Request) (name : String)
    (caller : FnAbi Miri.MIR.TyId) (args : Array (OpTy Provenance)) : M S (Array (OpTy Provenance)) := do
  if request.legacy then
    h.checkSymbolClash name
    if caller.conv != .C then throw (.undefinedBehavior "filesystem calling convention mismatch")
    if caller.cVariadic then throw (.undefinedBehavior "filesystem non-variadic function called variadic")
    if args.size != request.signature.args.size then throw (.undefinedBehavior "filesystem argument count mismatch")
    return args
  let callee ← h.expectedAbi name request.signature
  if callee.conv != .C || callee.cVariadic || callee.args.size != request.signature.args.size ||
      callee.fixedCount.toNat != request.signature.args.size then throw (.invalidProgram "compiler filesystem signature mismatch")
  if caller.conv != callee.conv then throw (.undefinedBehavior "filesystem calling convention mismatch")
  if caller.cVariadic != callee.cVariadic then throw (.undefinedBehavior "filesystem variadic ABI mismatch")
  if caller.fixedCount != callee.fixedCount then throw (.undefinedBehavior "filesystem argument count mismatch")
  if !(← h.argumentCompat caller.ret callee.ret) then throw (.undefinedBehavior "filesystem return ABI mismatch")
  for (actual,expected) in caller.args.toList.zip callee.args.toList do
    if !(← h.argumentCompat actual expected) then throw (.undefinedBehavior "filesystem argument ABI mismatch")
  h.checkSymbolClash name
  if args.size != request.signature.args.size then throw (.invalidProgram "filesystem operands disagree with ABI")
  args.mapIdxM fun index op => do
    let some expected := callee.args[index]? | throw (.invalidProgram "compiler filesystem ABI argument missing")
    h.transmute op expected.layout
private def offset64 (h : Hooks S F D P HM T E K H R Ent) (direct : Bool) (op : OpTy Provenance) : M S Int64 := do
  if direct then return ← h.readI64 op
  let value ← h.readSignedAtLayout op
  if value < -9223372036854775808 || value > 9223372036854775807 then
    throw (.invalidProgram "off_t does not fit i64")
  return Int64.ofInt value

def dispatch (h : Hooks S F D P HM T E K H R Ent) (name : String) (abi : FnAbi Miri.MIR.TyId)
    (args : Array (OpTy Provenance)) (dest : MPlaceTy Provenance) : M S ForeignItems.EmulateItemResult := do
  if h.communicate != h.times.fd.communicate then throw (.invalidProgram "filesystem communication policy mismatch")
  let paths := h.directories.paths
  let metadata := paths.metadata
  let some request := parse metadata.os name | return .NotSupported
  -- Source checks this target set BEFORE signature checks.
  if name == "posix_fallocate" && !(#["linux","freebsd","solaris","illumos","android"].contains metadata.os) then
    throw (.unsupported "posix_fallocate unsupported on target OS")
  if name == "flock" && !(#["linux","android","freebsd","macos","illumos"].contains metadata.os) then
    throw (.unsupported "flock unsupported on target OS")
  let args ← checked h request name abi args
  let first ← arg args 0
  let write32 := fun (value : Int32) => metadata.writeInt value.toInt dest
  match request.operation with
  | .unlink => write32 (← UnixFsPaths.unlink paths first)
  | .rmdir => write32 (← UnixFsPaths.rmdir paths first)
  | .symlink => write32 (← UnixFsPaths.symlink paths first (← arg args 1))
  | .linkat => write32 (← UnixFsPaths.linkat paths first (← arg args 1) (← arg args 2) (← arg args 3) (← arg args 4))
  | .stat | .lstat => write32 (← UnixFsMetadata.stat metadata first (← arg args 1) (request.operation == .lstat))
  | .fstat => write32 (← UnixFsMetadata.fstat metadata first (← arg args 1))
  | .fstatat => write32 (← UnixFsMetadata.fstatat metadata first (← arg args 1) (← arg args 2) (← arg args 3))
  | .statx => write32 (← UnixFsMetadata.statx metadata first (← arg args 1) (← arg args 2) (← arg args 3) (← arg args 4))
  | .chmod => write32 (← UnixFsPaths.chmod paths first (← arg args 1))
  | .fchmod => write32 (← UnixFsFd.chmod h.times.fd first (← arg args 1))
  | .rename => write32 (← UnixFsPaths.rename paths first (← arg args 1))
  | .mkdir => write32 (← UnixFsPaths.mkdir paths first (← arg args 1))
  | .opendir => h.writeUsize (← UnixDirectories.openDir h.directories first) dest
  | .readdir => UnixDirectories.readDir h.directories first dest request.dirent
  | .dirfd => UnixDirectories.dirFd h.directories first dest
  | .closedir => write32 (← UnixDirectories.closeDir h.directories first)
  | .seek =>
    let fd ← metadata.readI32 first
    let offset ← h.readSignedAtLayout (← arg args 1)
    let whence ← metadata.readI32 (← arg args 2)
    UnixFsFd.seek h.times.fd fd offset whence dest
  | .truncate =>
    let fd ← metadata.readI32 first
    let length ← h.readSignedAtLayout (← arg args 1)
    write32 (← UnixFsFd.truncate h.times.fd fd length)
  | .fsync | .fdatasync => write32 (← UnixFsFd.syncFile h.times.fd (← metadata.readI32 first) (request.operation == .fdatasync))
  | .futimens => write32 (← UnixFsTimes.futimens h.times first (← arg args 1))
  | .utimensat => write32 (← UnixFsTimes.utimensat h.times first (← arg args 1) (← arg args 2) (← arg args 3))
  | .readlink => metadata.writeInt (← UnixFsPaths.readlink paths first (← arg args 1) (← arg args 2)).toInt dest
  | .advise =>
    let _ ← metadata.readI32 first
    let _ ← h.readSignedAtLayout (← arg args 1)
    let _ ← h.readSignedAtLayout (← arg args 2)
    let _ ← metadata.readI32 (← arg args 3)
    h.directories.writeNull dest
  | .posixAllocate =>
    let fd ← metadata.readI32 first
    let offset ← offset64 h request.directI64 (← arg args 1)
    let length ← offset64 h request.directI64 (← arg args 2)
    h.writeScalar (← UnixFsFd.posixAllocate h.times.fd fd offset length) dest
  | .allocate =>
    let fd ← metadata.readI32 first
    let mode ← metadata.readI32 (← arg args 1)
    let offset ← offset64 h request.directI64 (← arg args 2)
    let length ← offset64 h request.directI64 (← arg args 3)
    write32 (← UnixFsFd.linuxAllocate h.times.fd fd mode offset length)
  | .syncRange =>
    let fd ← metadata.readI32 first
    let offset ← h.readI64 (← arg args 1)
    let count ← h.readI64 (← arg args 2)
    let flags ← metadata.readI32 (← arg args 3)
    write32 (← UnixFsFd.syncRange h.times.fd fd offset count flags)
  | .realpath => h.directories.writePointer (← UnixFsPaths.realpath paths first (← arg args 1)) dest
  | .mkstemp => write32 (← UnixTempFile.mkstemp h.temporary first)
  | .flock =>
    let fd ← metadata.readI32 first
    let flags ← metadata.readI32 (← arg args 1)
    write32 (← UnixFileOperations.flockFd metadata h.communicate h.flock fd flags)
  | .isatty => write32 (← UnixFsFd.isatty h.times.fd first)
  return .NeedsReturn

/-- Exactly one outer Unix wrapper performs entry poll; dispatch itself does not. -/
def bindUnix (h : Hooks S F D P HM T E K H R Ent)
    (base : ForeignItems.Hooks Provenance S Place (MPlaceTy Provenance) Ptr B I) :
    ForeignItems.Hooks Provenance S Place (MPlaceTy Provenance) Ptr B I := {
  base with unix := fun name abi args dest => do
    if base.family != .unix || base.os != h.directories.paths.metadata.os then
      throw (.invalidProgram "filesystem dispatcher target mismatch")
    if h.communicate then h.pollAndUnblockZero
    let result ← dispatch h name abi args dest
    if result != .NotSupported then return result
    base.unix name abi args dest }
end Miri.Interpreter.UnixFsDispatch
