import Miri.Interpreter.EnvVars
import Miri.Interpreter.OsStrings
import Miri.Interpreter.IoError

/-! Pinned shims/unix/env.rs and the system-information helpers in
unix/foreign_items.rs. Host operations are mandatory stateful effects. -/
namespace Miri.Interpreter.UnixEnvironment
open Miri.ABI Miri.Memory
abbrev M := EStateM StepError
structure Hooks (S Os E Kind : Type) where
  os : String
  targetEnv : String
  strings : OsStrings.Hooks Provenance S Os Kind
  env : EnvVars.Hooks (Option Provenance) Os S
  process : EnvVars.ProcessHooks S
  errors : IoError.Hooks S E
  readPointer : OpTy Provenance → M S (Pointer (Option Provenance))
  readUsize : OpTy Provenance → M S UInt64
  readI32 : OpTy Provenance → M S Int32
  readU32 : OpTy Provenance → M S UInt32
  readScalar : OpTy Provenance → M S (Scalar Provenance)
  isolationReject : String → M S Bool
  checkNoIsolation : String → M S Unit
  currentDirectory : M S (Except (IoError.HostError E) Os)
  setCurrentDirectory : Os → M S (Except (IoError.HostError E) Unit)
  /-- Exact check_ptr_access over the entire requested range, without a read/write. -/
  checkAccess : Pointer (Option Provenance) → UInt64 → M S Unit
  writeBytes : Pointer (Option Provenance) → ByteArray → M S Unit
  libcI32 : String → M S Int32
  libcScalar : String → M S (Scalar Provenance)
  pageSize : UInt64
  numCpus : UInt32
  /-- Compiler target.arch.desc_symbol and pinned CARGO_PKG_VERSION. -/
  architecture : String
  miriVersion : String
  derefNamed : OpTy Provenance → String → M S (MPlaceTy Provenance)
  derefPointerCell : OpTy Provenance → M S (MPlaceTy Provenance)
  projectNamed : MPlaceTy Provenance → String → M S (MPlaceTy Provenance)
  writeUninit : MPlaceTy Provenance → M S Unit
  writePointer : Pointer (Option Provenance) → MPlaceTy Provenance → M S Unit
  homeDirectory : M S (Option Os)
  hostErrorDisplay : IoError.HostError E → M S Os
  /-- Exact Scalar Display inside the source's unknown-errnum message. -/
  unknownErrorDisplay : Scalar Provenance → M S Os
private def requireUnix (h : Hooks S O E K) : M S Unit := do
  if h.env.family != .unix || h.process.family != .unix then
    throw (.invalidProgram "Unix environment operation on non-Unix target")
private def fail (h : Hooks S O E K) (name : String) : M S Int32 :=
  IoError.setErrnoAndReturnNeg1I32 h.errors (.libc name)
private def denied (h : Hooks S O E K) : M S Unit := do
  IoError.setLastError h.errors (.host (← h.errors.hostFromKind .PermissionDenied))

def getcwd (h : Hooks S O E K) (buf size : OpTy Provenance) : M S (Pointer (Option Provenance)) := do
  requireUnix h
  let buf ← h.readPointer buf
  let size ← h.readUsize size
  if ← h.isolationReject "`getcwd`" then
    denied h
    return h.env.nullPointer
  match ← h.currentDirectory with
  | .error error => IoError.setLastError h.errors (.host error)
  | .ok path =>
    if (← OsStrings.writePath h.strings path buf size).1 then return buf
    IoError.setLastError h.errors (.libc "ERANGE")
  return h.env.nullPointer

def chdir (h : Hooks S O E K) (path : OpTy Provenance) : M S Int32 := do
  requireUnix h
  let path ← OsStrings.readPath h.strings (← h.readPointer path)
  if ← h.isolationReject "`chdir`" then
    denied h
    return -1
  IoError.tryUnwrap h.errors ((← h.setCurrentDirectory path).map fun _ => (0 : Int32)) (-1)

def gethostname (h : Hooks S O E K) (name len : OpTy Provenance) : M S Int32 := do
  requireUnix h
  let name ← h.readPointer name
  let len ← h.readUsize len
  if len == 0 then throw (.undefinedBehavior "gethostname requires nonzero buffer length")
  h.checkAccess name len
  let hostname := "Miri".toUTF8
  if len > 4 then
    if !(← h.strings.writeCString hostname name len).1 then
      throw (.invalidProgram "gethostname constant failed to fit")
    return 0
  if h.os == "android" then return ← fail h "ENAMETOOLONG"
  if (h.os == "linux" && h.targetEnv == "gnu") || h.os == "freebsd" then
    h.writeBytes name (ByteArray.mk (hostname.data.extract 0 len.toNat))
    return ← fail h "ENAMETOOLONG"
  if #["linux","macos","solaris","illumos"].contains h.os then
    h.writeBytes name (ByteArray.mk ((hostname.data.extract 0 (len.toNat - 1)).push 0))
    return 0
  throw (.unsupported "gethostname unsupported target OS")

def uname (h : Hooks S O E K) (op : OpTy Provenance) (fieldSize : Option (OpTy Provenance)) : M S Int32 := do
  requireUnix h
  let ptr ← h.readPointer op
  let size ← fieldSize.mapM h.readI32
  if ← h.env.isNull ptr then return ← fail h "EFAULT"
  let place ← h.derefNamed op "utsname"
  let values := #[("sysname","Miri"),("nodename","Miri"),("release",h.miriVersion),
    ("version","Miri " ++ h.miriVersion),("machine",h.architecture)]
  let values := if h.os == "linux" || h.os == "android" then values.push ("domainname","(none)") else values
  for (name,value) in values do
    let field ← h.projectNamed place name
    let bytes := field.layout.layout.size.bytes
    if let some size := size then
      if size.toInt < 0 || size.toUInt32.toUInt64 != bytes then
        throw (.unsupported "uname fields size disagrees with compiler libc type")
    if !(← h.strings.writeCString value.toUTF8 field.mplace.ptr bytes).1 then
      throw (.invalidProgram "uname constant failed to fit compiler field")
  return 0

def sysconf (h : Hooks S O E K) (op : OpTy Provenance) : M S Int64 := do
  let name ← h.readI32 op
  for (constant,value) in #[("_SC_PAGESIZE",h.pageSize.toNat),("_SC_PAGE_SIZE",h.pageSize.toNat),
      ("_SC_NPROCESSORS_CONF",h.numCpus.toNat),("_SC_NPROCESSORS_ONLN",h.numCpus.toNat),
      ("_SC_GETPW_R_SIZE_MAX",512),("_SC_OPEN_MAX",65536),("_SC_HOST_NAME_MAX",255)] do
    if (← h.libcI32 constant) == name then
      if value > 9223372036854775807 then throw (.invalidProgram "sysconf value does not fit i64")
      return Int64.ofInt (Int.ofNat value)
  throw (.unsupported "unimplemented sysconf name")

def strerror (h : Hooks S O E K) (errnum buf len : OpTy Provenance) : M S Int32 := do
  let error ← h.readScalar errnum
  let buf ← h.readPointer buf
  let len ← h.readUsize len
  let formatted ← match ← IoError.tryErrnumToHost h.errors error with
    | some error => h.hostErrorDisplay error
    | none => h.unknownErrorDisplay error
  if (← OsStrings.writeOsString h.strings formatted buf len).1 then return 0
  h.libcI32 "ERANGE"

/-- Source std-only adapter: all passwd fields except pw_dir stay uninitialized. -/
def getpwuid (h : Hooks S O E K) (uid pwd buf len result : OpTy Provenance) : M S (Scalar Provenance) := do
  h.checkNoIsolation "`getpwuid_r`"
  let uid ← h.readU32 uid
  let pwd ← h.derefNamed pwd "passwd"
  let buf ← h.readPointer buf
  let len ← h.readUsize len
  let result ← h.derefPointerCell result
  if uid != 1000 then throw (.unsupported "getpwuid_r on other users")
  h.writeUninit pwd
  let some home ← h.homeDirectory | throw (.invalidProgram "host home_dir returned None")
  let complete := (← OsStrings.writePath h.strings home buf len).1
  let field ← h.projectNamed pwd "pw_dir"
  h.writePointer buf field
  h.writePointer (if complete then pwd.mplace.ptr else h.env.nullPointer) result
  if complete then
    match Scalar.fromInt 0 (Size.ofBytes 4) with
    | .ok value => return value
    | .error _ => throw (.invalidProgram "zero i32 construction failed")
  h.libcScalar "ERANGE"
end Miri.Interpreter.UnixEnvironment
