import Miri.Interpreter.UnixFsFd
import Miri.Interpreter.TimeShims

/-! futimens/utimensat parsing and update policy from pinned unix/fs.rs. Host
SystemTime checked arithmetic and real set_times operations are explicit. -/
namespace Miri.Interpreter.UnixFsTimes
open Miri.ABI Miri.Memory
abbrev M := EStateM StepError
inductive Update (Time : Type) where | omit | set (time : Time)
structure Hooks (S F D Path HM Time E Kind H : Type) where
  fd : UnixFsFd.Hooks S F D Path HM Time E Kind H
  systemNow : M S Time
  /-- UNIX_EPOCH.checked_add(duration), preserving possible host overflow. -/
  sinceEpoch : Clock.Duration → M S (Option Time)
  indexedField : MPlaceTy Provenance → Nat → M S (MPlaceTy Provenance)
  readTargetIsize : MPlaceTy Provenance → M S Int
  libcTargetIsize : String → M S Int
  timespecLayout : M S LocalLayout
  ptrToPlace : Pointer (Option Provenance) → LocalLayout → MPlaceTy Provenance
  offsetPlace : MPlaceTy Provenance → Size → LocalLayout → M S (MPlaceTy Provenance)
  /-- Bind TimeShims.readTimespec, retaining its tv_sec/tv_nsec read/check order. -/
  readTimespec : MPlaceTy Provenance → M S (Option Clock.Duration)
  setFileTimes : H → Update Time → Update Time → M S (Except (IoError.HostError E) Unit)
  setPathTimes : Path → Bool → Update Time → Update Time → M S (Except (IoError.HostError E) Unit)
private def fail (h : Hooks S F D P HM T E K H) (name : String) : M S Int32 :=
  IoError.setErrnoAndReturnNeg1I32 h.fd.paths.metadata.errors (.libc name)

def parseSpec (h : Hooks S F D P HM T E K H) (place : MPlaceTy Provenance) : M S (Option (Update T)) := do
  if !h.fd.communicate then throw (.invalidProgram "isolation must prevent UTIME_NOW clock read")
  let nsec ← h.readTargetIsize (← h.indexedField place 1)
  if nsec == (← h.libcTargetIsize "UTIME_OMIT") then return some .omit
  if nsec == (← h.libcTargetIsize "UTIME_NOW") then return some (.set (← h.systemNow))
  let some duration ← h.readTimespec place | return none
  return (← h.sinceEpoch duration).map Update.set

def parseTimes (h : Hooks S F D P HM T E K H) (pointer : Pointer (Option Provenance)) :
    M S (Option (Update T × Update T)) := do
  if ← h.fd.paths.metadata.isNull pointer then
    let now ← h.systemNow
    return some (.set now,.set now)
  let layout ← h.timespecLayout
  let access := h.ptrToPlace pointer layout
  let modified ← h.offsetPlace access layout.layout.size layout
  let some access ← parseSpec h access | return none
  let some modified ← parseSpec h modified | return none
  return some (access,modified)

def futimens (h : Hooks S F D P HM T E K H) (number times : OpTy Provenance) : M S Int32 := do
  let number ← h.fd.paths.metadata.readI32 number
  let times ← h.fd.paths.metadata.readPointer times
  let some fd ← h.fd.paths.metadata.lookupFd number | return ← fail h "EBADF"
  Files.withDrop (do
    let some file := h.fd.asFile fd | throw (.unsupported "futimens requires file-backed descriptor")
    if !h.fd.communicate then throw (.invalidProgram "isolation should prevent opening file")
    let some (access,modified) ← parseTimes h times | return ← fail h "EINVAL"
    IoError.tryUnwrap h.fd.paths.metadata.errors ((← h.setFileTimes file.handle access modified).map fun _ => (0 : Int32)) (-1)
  ) (h.fd.paths.metadata.dropFd fd)

def utimensat (h : Hooks S F D P HM T E K H) (number path times flags : OpTy Provenance) : M S Int32 := do
  let number ← h.fd.paths.metadata.readI32 number
  let path ← h.fd.paths.metadata.readPointer path
  let times ← h.fd.paths.metadata.readPointer times
  let flags ← h.fd.paths.metadata.readI32 flags
  if ← h.fd.paths.metadata.isNull path then
    if number != (← h.fd.paths.metadata.libcI32 "AT_FDCWD") then
      throw (.unsupported "utimensat NULL path only supported for AT_FDCWD")
    return ← fail h "EFAULT"
  let path ← h.fd.paths.metadata.readPath path
  if ← h.fd.paths.metadata.isolationReject "`utimensat`" then return ← fail h "EACCES"
  let nofollow ← h.fd.paths.metadata.libcI32 "AT_SYMLINK_NOFOLLOW"
  let selected := flags &&& nofollow == nofollow
  if flags &&& ~~~nofollow != 0 then throw (.unsupported "unsupported flags for utimensat")
  if !h.fd.paths.metadata.isAbsolute path then
    if number != (← h.fd.paths.metadata.libcI32 "AT_FDCWD") then
      throw (.unsupported "utimensat path relative to dirfd unsupported")
  let some (access,modified) ← parseTimes h times | return ← fail h "EINVAL"
  match access,modified with
  | .omit,.omit => return 0
  | _,_ =>
    IoError.tryUnwrap h.fd.paths.metadata.errors ((← h.setPathTimes path selected access modified).map fun _ => (0 : Int32)) (-1)
end Miri.Interpreter.UnixFsTimes
