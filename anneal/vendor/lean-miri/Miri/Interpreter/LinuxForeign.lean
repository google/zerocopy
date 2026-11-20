import Miri.Interpreter.LinuxMemory
import Miri.Interpreter.UnixFdDispatch
import Miri.Interpreter.ShimSignatures
import Miri.Interpreter.IoError

/-! Remaining pinned Linux/Android foreign arms; shared filesystem/statx,
thread-name/gettid, epoll/eventfd, syscall/prctl, strerror and std guards stay
in their canonical modules and are composed by UnixForeign. -/
namespace Miri.Interpreter.LinuxForeign
open Miri.ABI Miri.Memory
abbrev M := EStateM StepError
structure Hooks (S Place H D Other E HM Os B I : Type) where
  signatures : ShimSignatures.Hooks Provenance S Place (MPlaceTy Provenance) (Pointer (Option Provenance)) B I
  signature : String → M S (FnAbi Miri.MIR.TyId)
  fd : UnixFdDispatch.Hooks S H D Other E HM Os
  memory : LinuxMemory.Hooks S Place B I
  errors : IoError.Hooks S E
  readScalar : OpTy Provenance → M S (Scalar Provenance)
  readI64 : OpTy Provenance → M S Int64
  writeInt : Int → MPlaceTy Provenance → M S Unit
  unixGettid : String → M S (Scalar Provenance)
  targetEnv : String
  dsoHandle : M S (Pointer (Option Provenance))
  getPtrFnInstance : Pointer (Option Provenance) → M S CallInstance
  addThreadAtexit : CallInstance → Scalar Provenance → M S Unit
private def arg (args : Array A) (i : Nat) : M S A :=
  match args[i]? with | some value => pure value | none => throw (.invalidProgram "checked Linux operand missing")
private def legacy (h : Hooks S Place H D O E HM Os B I) (name : String)
    (abi : FnAbi Miri.MIR.TyId) (args : Array (OpTy Provenance)) (count : Nat) : M S Unit := do
  h.signatures.foreign.checkSymbolClash name
  if abi.conv != .C then throw (.undefinedBehavior "Linux legacy calling convention mismatch")
  if abi.cVariadic then throw (.undefinedBehavior "Linux legacy variadic signature")
  if args.size != count then throw (.undefinedBehavior "Linux legacy argument count mismatch")

def positional (h : Hooks S Place H D O E HM Os B I) (name : String) (abi : FnAbi Miri.MIR.TyId)
    (args : Array (OpTy Provenance)) (dest : MPlaceTy Provenance) : M S Unit := do
  let args ← ShimSignatures.fixed h.signatures name (h.signature name) 4 abi args
  let fd ← h.fd.readI32 (← arg args 0)
  let buf ← h.fd.readPointer (← arg args 1)
  let count ← h.fd.readUsize (← arg args 2)
  let offset ← h.fd.readOffset (← arg args 3)
  UnixFd.readWrite h.fd.file.fd fd buf count (some offset) (name == "pwrite64") dest

def emulate (h : Hooks S Place H D O E HM Os B I) (name : String) (abi : FnAbi Miri.MIR.TyId)
    (args : Array (OpTy Provenance)) (dest : MPlaceTy Provenance) : M S (Option ForeignItems.EmulateItemResult) := do
  if h.signatures.foreign.os != "linux" then return none
  if name == "pread64" || name == "pwrite64" then
    positional h name abi args dest
    return some .NeedsReturn
  if name == "open64" || name == "openat64" then
    let isAt :=  name == "openat64"
    let (args,rest) ← ShimSignatures.variadic h.signatures name (h.signature name) (if isAt then 3 else 2) abi args
    let directory ← if isAt then (h.fd.readI32 (← arg args 0)).map some else pure none
    let pointer ← h.fd.readPointer (← arg args (if isAt then 1 else 0))
    let flags ← h.fd.readI32 (← arg args (if isAt then 2 else 1))
    let path ← h.fd.readPath pointer
    let file := {h.fd.file with readMode := h.fd.readMode name rest}
    h.writeInt (← UnixOpen.openPath file directory path flags.toUInt32).toInt dest
    return some .NeedsReturn
  if name == "__cxa_thread_atexit_impl" then
    if h.targetEnv != "gnu" then return none
    let args ← ShimSignatures.fixed h.signatures name (h.signature name) 3 abi args
    let dtor ← h.fd.readPointer (← arg args 0)
    let data ← h.readScalar (← arg args 1)
    let dso ← h.fd.readPointer (← arg args 2)
    if dso.offset != (← h.dsoHandle).offset then
      throw (.unsupported "__cxa_thread_atexit_impl requires __dso_handle address")
    let dtor ← h.getPtrFnInstance dtor
    h.addThreadAtexit dtor data
    h.writeInt 0 dest
    return some .NeedsReturn
  if name == "mmap64" then
    legacy h name abi args 6
    let offset ← h.readI64 (← arg args 5)
    UnixMemory.mmap h.memory.memory args offset.toInt dest
    return some .NeedsReturn
  if name == "mremap" then
    let (args,_) ← ShimSignatures.variadic h.signatures name (h.signature name) 4 abi args
    LinuxMemory.remap h.memory (← arg args 0) (← arg args 1) (← arg args 2) (← arg args 3) dest
    return some .NeedsReturn
  if #["__errno_location","__libc_current_sigrtmin","__libc_current_sigrtmax"].contains name then
    legacy h name abi args 0
    if name == "__errno_location" then h.signatures.foreign.writePointer (← IoError.lastErrorPlace h.errors).mplace.ptr dest
    -- Literal Miri machine.rs SIGRTMIN=34, SIGRTMAX=42, not host signal values.
    else h.writeInt (if name == "__libc_current_sigrtmin" then 34 else 42) dest
    return some .NeedsReturn
  return none
end Miri.Interpreter.LinuxForeign
