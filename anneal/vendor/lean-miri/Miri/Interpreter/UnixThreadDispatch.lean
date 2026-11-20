import Miri.Interpreter.AppleThreadId
import Miri.Interpreter.UnixThreadMachine
import Miri.Interpreter.ShimSignatures

/-! Source unix/foreign_items.rs threading arms and Linux/FreeBSD/solarish/macOS
name wrappers. Signature construction and libc values are canonical queries. -/
namespace Miri.Interpreter.UnixThreadDispatch
open Miri.ABI Miri.Memory Miri.MIR
abbrev M := EStateM StepError
structure Hooks (S D B I : Type) where
  thread : UnixThread.Hooks S
  signatures : ShimSignatures.PrimitiveHooks Provenance S
  signature : String → M S (FnAbi TyId)
  writeScalar : Scalar Provenance → MPlaceTy Provenance → M S Unit
  writeNull : MPlaceTy Provenance → M S Unit
  libc : String → M S (Scalar Provenance)
  errnoNegOne : String → M S (Scalar Provenance)
  unixGettid : String → M S (Scalar Provenance)
  apple : AppleThreadId.Hooks S
private def arg (args : Array A) (index : Nat) : M S A :=
  match args[index]? with
  | some value => pure value
  | none => throw (.invalidProgram "checked pthread argument absent")
private def zero : M S (Scalar Provenance) :=
  match Scalar.fromUInt (BitVec.ofNat 128 0) (Size.ofBytes 4) with
  | .ok value => pure value
  | .error error => throw (ScalarOps.scalarError error)
private def legacy (h : Hooks S D B I) (name : String) (abi : FnAbi TyId)
    (args : Array (OpTy Provenance)) (count : Nat) : M S Unit := do
  h.signatures.checkSymbolClash name
  if abi.conv != .C then throw (.undefinedBehavior "pthread calling convention mismatch")
  if abi.cVariadic then throw (.undefinedBehavior "pthread unexpected variadic signature")
  if args.size != count then throw (.undefinedBehavior "pthread argument count mismatch")

def emulate (h : Hooks S D B I) (name : String) (abi : FnAbi TyId)
    (args : Array (OpTy Provenance)) (dest : MPlaceTy Provenance) :
    M S (Option ForeignItems.EmulateItemResult) := do
  if #["pthread_create","pthread_join","pthread_detach","pthread_self","sched_yield"].contains name then
    let count := if name == "pthread_create" then 4 else if name == "pthread_join" then 2
      else if name == "pthread_detach" then 1 else 0
    let args ← ShimSignatures.fixedPrimitive h.signatures name (h.signature name) count abi args
    if name == "pthread_create" then
      UnixThread.create h.thread (← arg args 0) (← arg args 1) (← arg args 2) (← arg args 3)
      h.writeNull dest
    else if name == "pthread_join" then
      UnixThread.join h.thread (← arg args 0) (← arg args 1) dest
    else if name == "pthread_detach" then
      h.writeScalar (← UnixThread.detach h.thread (← arg args 0)) dest
    else if name == "pthread_self" then
      h.writeScalar (← UnixThread.self h.thread) dest
    else
      UnixThread.schedYield h.thread
      h.writeNull dest
    return some .NeedsReturn
  let os := h.signatures.os
  if (os == "linux" && name == "gettid") ||
      (os == "freebsd" && name == "pthread_getthreadid_np") then
    legacy h name abi args 0
    h.writeScalar (← h.unixGettid name) dest
    return some .NeedsReturn
  if os == "macos" && name == "pthread_threadid_np" then
    legacy h name abi args 2
    h.writeScalar (← AppleThreadId.query h.apple (← arg args 0) (← arg args 1)) dest
    return some .NeedsReturn
  unless #["linux","freebsd","solaris","illumos","macos"].contains os do return none
  if name == "pthread_setname_np" then
    legacy h name abi args (if os == "macos" then 1 else 2)
    let (thread,nameValue,limit) ← if os == "macos" then do
        let thread ← UnixThread.self h.thread
        let nameValue ← h.thread.readScalar (← arg args 0)
        let limit ← h.thread.scalarUsize (← h.libc "MAXTHREADNAMESIZE")
        pure (thread,nameValue,limit)
      else do
        let thread ← h.thread.readScalar (← arg args 0)
        let nameValue ← h.thread.readScalar (← arg args 1)
        pure (thread,nameValue,if os == "linux" then 16 else if os == "freebsd" then UInt64.ofNat (2^64-1) else 32)
    let result ← UnixThread.setName h.thread thread nameValue limit false
    let value ← if result == .ok then zero else if os == "freebsd" then
        throw (.invalidProgram "FreeBSD thread name source unreachable length")
      else if os == "macos" then h.errnoNegOne "ENAMETOOLONG" else h.libc "ERANGE"
    h.writeScalar value dest
    return some .NeedsReturn
  if name == "pthread_getname_np" then
    legacy h name abi args 3
    let value ← if os == "linux" then do
        -- Source reads length before even touching thread/name operands.
        let length ← h.thread.readScalar (← arg args 2)
        if (← h.thread.scalarUsize length) < 16 then h.libc "ERANGE" else do
          let thread ← h.thread.readScalar (← arg args 0)
          let output ← h.thread.readScalar (← arg args 1)
          let result ← UnixThread.getName h.thread thread output length false
          unless result == .ok do throw (.invalidProgram "Linux thread name source unreachable length")
          zero
      else do
        let thread ← h.thread.readScalar (← arg args 0)
        let output ← h.thread.readScalar (← arg args 1)
        let length ← h.thread.readScalar (← arg args 2)
        let truncate := os == "freebsd" || os == "macos"
        let result ← UnixThread.getName h.thread thread output length truncate
        if result == .ok || truncate then zero else h.libc "ERANGE"
    h.writeScalar value dest
    return some .NeedsReturn
  return none

def bind (h : Hooks S D B I)
    (base : ForeignItems.Hooks Provenance S D (MPlaceTy Provenance) (Pointer (Option Provenance)) B I) :
    ForeignItems.Hooks Provenance S D (MPlaceTy Provenance) (Pointer (Option Provenance)) B I :=
  {base with unix := fun name abi args dest => do
    if let some result ← emulate h name abi args dest then return result
    base.unix name abi args dest}
end Miri.Interpreter.UnixThreadDispatch
