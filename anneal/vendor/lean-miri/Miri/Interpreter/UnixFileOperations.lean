import Miri.Interpreter.UnixFsFd

/-! FileHandle::{flock,get_flags} and DirHandle::get_flags, unix/fs.rs:143–190.
The blocking lock is deliberately unavailable, exactly as in pinned Miri. -/
namespace Miri.Interpreter.UnixFileOperations
open Miri.ABI Miri.Memory
abbrev M := EStateM StepError
inductive LockOp where | shared (nonblocking : Bool) | exclusive (nonblocking : Bool) | unlock
inductive TryLockError (E : Type) where | host (error : IoError.HostError E) | wouldBlock
structure Hooks (S H E : Type) where
  tryLock : H → Bool → M S (Except (TryLockError E) Unit)
  unlock : H → M S (Except (IoError.HostError E) Unit)
  fromKind : IoError.ErrorKind → M S (IoError.HostError E)
  libc : String → M S (Scalar Provenance)

def flock (h : Hooks S H E) (file : H) (communicate : Bool) (operation : LockOp) :
    M S (Except (IoError.HostError E) Unit) := do
  if !communicate then throw (.invalidProgram "isolation should prevent opening file")
  let (shared,nonblocking) ← match operation with
    | .unlock => pure (false,false)
    | .shared value => pure (true,value)
    | .exclusive value => pure (false,value)
  match operation with
  | .unlock => h.unlock file
  | _ =>
    match ← h.tryLock file shared with
    | .ok _ => return .ok ()
    | .error (.host error) => return .error error
    | .error .wouldBlock =>
      if !nonblocking then throw (.unsupported "blocking flock unsupported")
      return .error (← h.fromKind .WouldBlock)

def fileFlags (h : Hooks S H E) (readable writable : Bool) : M S (Scalar Provenance) := do
  match readable,writable with
  | true,true => h.libc "O_RDWR"
  | true,false => h.libc "O_RDONLY"
  | false,true => h.libc "O_WRONLY"
  | false,false => throw (.invalidProgram "FileHandle flags unreachable path-only access")
def directoryFlags (h : Hooks S H E) : M S (Scalar Provenance) := h.libc "O_RDONLY"
/-- unix/fd.rs::flock wrapper, including target constants after descriptor lookup. -/
def flockFd (metadata : UnixFsMetadata.Hooks S F D P HM T E)
    (communicate : Bool)
    (operation : F → Bool → LockOp → M S (Except (IoError.HostError E) Unit))
    (number flags : Int32) : M S Int32 := do
  let some fd ← metadata.lookupFd number
    | return ← IoError.setErrnoAndReturnNeg1I32 metadata.errors (.libc "EBADF")
  Files.withDrop (do
    let shared ← metadata.libcI32 "LOCK_SH"
    let exclusive ← metadata.libcI32 "LOCK_EX"
    let nonblock ← metadata.libcI32 "LOCK_NB"
    let unlock ← metadata.libcI32 "LOCK_UN"
    let parsed ← if flags == shared then pure (LockOp.shared false)
      else if flags == shared ||| nonblock then pure (.shared true)
      else if flags == exclusive then pure (.exclusive false)
      else if flags == exclusive ||| nonblock then pure (.exclusive true)
      else if flags == unlock then pure .unlock
      else throw (.unsupported "unsupported flock flags")
    IoError.tryUnwrap metadata.errors ((← operation fd communicate parsed).map fun _ => (0 : Int32)) (-1)
  ) (metadata.dropFd fd)
end Miri.Interpreter.UnixFileOperations
