import Miri.Interpreter.UnixFd
import Miri.Interpreter.ShimSignatures

/-! Pinned unix/fd.rs fcntl and ioctl policies, preserving lazy target-constant
queries, descriptor ownership, varargs checks and platform-specific guards. -/
namespace Miri.Interpreter.UnixFdControl
open Miri.ABI Miri.Memory Miri.MIR Files
abbrev M := EStateM StepError
abbrev Ref H D O := Files.Ref (Description H D O)
structure Hooks (S H D O E Meta : Type) where
  fd : UnixFd.Hooks S H D O E Meta
  libc : String → M S (Scalar Provenance)
  libcI32 : String → M S Int32
  readScalar : OpTy Provenance → M S (Scalar Provenance)
  readI32 : OpTy Provenance → M S Int32
  takeI32 : String → ShimSignatures.Varargs Provenance → M S (OpTy Provenance)
  getFlags : Ref H D O → M S (Scalar Provenance)
  setFlags : Ref H D O → Int32 → M S (Scalar Provenance)
  ioctl : Ref H D O → Scalar Provenance → ShimSignatures.Varargs Provenance → M S Int32
  frameInStd : M S Bool
  /-- Source reject_in_isolation effect, true iff configured Reject branch. -/
  rejectIsolation : String → M S Bool
  fullSync : Int32 → M S (Scalar Provenance)
private def lift (value : Except StepError A) : M S A :=
  match value with | .ok value => pure value | .error error => throw error
private def fromI32 (value : Int32) : M S (Scalar Provenance) :=
  lift (Scalar.fromInt value.toInt (Size.ofBytes 4) |>.mapError ScalarOps.scalarError)
private def error (h : Hooks S H D O E Meta) (name : String) : M S (Scalar Provenance) := do
  fromI32 (← IoError.setErrnoAndReturnNeg1I32 h.fd.errors (.libc name))
private def getFd (h : Hooks S H D O E Meta) (number : Int32) : M S (Option (Ref H D O)) := do
  let some fd := (← h.fd.table).get number | return none
  return some (← h.fd.cloneRef fd)

def ioctl (h : Hooks S H D O E Meta) (fd op : OpTy Provenance)
    (rest : ShimSignatures.Varargs Provenance) : M S (Scalar Provenance) := do
  let number ← h.readI32 fd
  let op ← h.readScalar op
  let some fd ← getFd h number | return ← error h "EBADF"
  Files.withDrop (do
    let close ← h.libc "FIOCLEX"
    let noClose ← h.libc "FIONCLEX"
    if op == close || op == noClose then return ← fromI32 0
    h.fd.asUnix fd
    fromI32 (← h.ioctl fd op rest)
  ) (h.fd.dropRef fd)

def fcntl (h : Hooks S H D O E Meta) (fd cmd : OpTy Provenance)
    (rest : ShimSignatures.Varargs Provenance) : M S (Scalar Provenance) := do
  let number ← h.readI32 fd
  let cmd ← h.readI32 cmd
  let getfd ← h.libcI32 "F_GETFD"
  let dupfd ← h.libcI32 "F_DUPFD"
  let dupfdClose ← h.libcI32 "F_DUPFD_CLOEXEC"
  let getfl ← h.libcI32 "F_GETFL"
  let setfl ← h.libcI32 "F_SETFL"
  if cmd == getfd then
    if !(← h.fd.table).isFdNum number then return ← error h "EBADF"
    return ← h.libc "FD_CLOEXEC"
  if cmd == dupfd || cmd == dupfdClose then
    let context := if cmd == dupfd then "fcntl(fd, F_DUPFD, ...)" else "fcntl(fd, F_DUPFD_CLOEXEC, ...)"
    let start ← h.readI32 (← h.takeI32 context rest)
    let some fd ← getFd h number | return ← error h "EBADF"
    let (table,number) ← lift ((← h.fd.table).insertWithMin fd start)
    h.fd.putTable table
    return ← fromI32 number
  if cmd == getfl then
    let some fd ← getFd h number | return ← error h "EBADF"
    return ← Files.withDrop (do h.fd.asUnix fd; h.getFlags fd) (h.fd.dropRef fd)
  if cmd == setfl then
    let some fd ← getFd h number | return ← error h "EBADF"
    return ← Files.withDrop (do
      let flags ← h.readI32 (← h.takeI32 "fcntl(fd, F_SETFL, ...)" rest)
      let mut ignored : Int32 := 0
      for name in #["O_RDONLY","O_WRONLY","O_RDWR","O_CREAT","O_EXCL","O_NOCTTY","O_TRUNC"] do
        ignored := ignored ||| (← h.libcI32 name)
      h.fd.asUnix fd
      h.setFlags fd (flags &&& ~~~ignored)
    ) (h.fd.dropRef fd)
  if h.fd.os == "macos" then
    if cmd == (← h.libcI32 "F_FULLFSYNC") then
      if ← h.rejectIsolation "`fcntl`" then
        let host ← h.fd.errors.hostFromKind .PermissionDenied
        return ← fromI32 (← IoError.setErrnoAndReturnNeg1I32 h.fd.errors (.host host))
      return ← h.fullSync number
    if ← h.frameInStd then
      if cmd == (← h.libcI32 "F_GETPATH") then return ← error h "EOPNOTSUPP"
  if h.fd.os == "freebsd" then
    if ← h.frameInStd then
      if cmd == (← h.libcI32 "F_KINFO") then return ← error h "EOPNOTSUPP"
  throw (.unsupported s!"fcntl unsupported command {cmd}")
end Miri.Interpreter.UnixFdControl
