import Miri.Interpreter.LinuxFutex
import Miri.Interpreter.EventFd
import Miri.Interpreter.UnixThread
import Miri.Interpreter.RandomMemory

/-! Pinned linux_like/syscall.rs and thread.rs::prctl. Extra varargs may be
ignored, but every argument preceding a used one must be checked first. -/
namespace Miri.Interpreter.LinuxSyscall
open Miri.ABI Miri.Memory Miri.MIR Miri.Concurrency
abbrev M := EStateM StepError
structure Hooks (S R F D B I : Type) where
  signatures : ShimSignatures.Hooks Provenance S D (MPlaceTy Provenance) (Pointer (Option Provenance)) B I
  signature : String → M S (FnAbi TyId)
  argumentTypes : Array LinuxFutex.ArgType → M S (Array TyId)
  typeBudget : Nat
  libcUsize : String → M S UInt64
  libcI32 : String → M S Int32
  readUsize : OpTy Provenance → M S UInt64
  readI32 : OpTy Provenance → M S Int32
  readPointer : OpTy Provenance → M S (Pointer (Option Provenance))
  writeTargetUsize : UInt64 → MPlaceTy Provenance → M S Unit
  writeInt : Int → MPlaceTy Provenance → M S Unit
  writeScalar : Scalar Provenance → MPlaceTy Provenance → M S Unit
  random : RandomMemory.Hooks S
  futex : LinuxFutex.Hooks S R
  event : EventFd.Hooks S F
  unixGettid : String → M S UInt32
  accept4 : OpTy Provenance → OpTy Provenance → OpTy Provenance → OpTy Provenance → MPlaceTy Provenance → M S Unit
  thread : UnixThread.Hooks S
  checkAccess : Pointer (Option Provenance) → Size → M S Unit

/-- Common source syscall algorithm with only the futex and accept4 effects
    parameterized. The normal constructor supplies their complete semantics;
    source assemblies missing either capability can retain the same syscall
    prefix and exact branch checks before returning demand-local Unsupported. -/
structure SyscallHooks (S D MD Ptr B I F : Type) where
  signatures : ShimSignatures.Hooks Provenance S D MD Ptr B I
  signature : String → M S (FnAbi TyId)
  argumentTypes : Array LinuxFutex.ArgType → M S (Array TyId)
  typeBudget : Nat
  libcUsize : String → M S UInt64
  readUsize : OpTy Provenance → M S UInt64
  readI32 : OpTy Provenance → M S Int32
  readPointer : OpTy Provenance → M S (Pointer (Option Provenance))
  writeTargetUsize : UInt64 → MPlaceTy Provenance → M S Unit
  writeInt : Int → MPlaceTy Provenance → M S Unit
  writeScalar : Scalar Provenance → MPlaceTy Provenance → M S Unit
  random : RandomMemory.Hooks S
  event : EventFd.Hooks S F
  unixGettid : String → M S UInt32
  futex : ShimSignatures.Varargs Provenance → MPlaceTy Provenance → M S Unit
  accept4 : Array (OpTy Provenance) → MPlaceTy Provenance → M S Unit

structure PrctlHooks (S D MD Ptr B I : Type) where
  signatures : ShimSignatures.Hooks Provenance S D MD Ptr B I
  signature : String → M S (FnAbi TyId)
  argumentTypes : Array LinuxFutex.ArgType → M S (Array TyId)
  typeBudget : Nat
  libcI32 : String → M S Int32
  readI32 : OpTy Provenance → M S Int32
  writeScalar : Scalar Provenance → MPlaceTy Provenance → M S Unit
  thread : Option (UnixThread.Hooks S)
  checkAccess : Pointer (Option Provenance) → Size → M S Unit
private def arg (args : Array A) (index : Nat) : M S A :=
  match args[index]? with
  | some value => pure value
  | none => throw (.invalidProgram "checked Linux syscall argument missing")
private def checked (signatures : ShimSignatures.Hooks Provenance S D MD Ptr B I)
    (typeBudget : Nat) (argumentTypes : Array LinuxFutex.ArgType → M S (Array TyId))
    (types : Array LinuxFutex.ArgType)
    (args : ShimSignatures.Varargs Provenance) : M S (Array (OpTy Provenance)) := do
  let (values,_) ← ShimSignatures.take signatures typeBudget (argumentTypes types) args
  return values

/-- All five constant lookups precede the opcode read, regardless of branch. -/
def syscallCore (h : SyscallHooks S D MD Ptr B I F) (name : String) (abi : FnAbi TyId)
    (args : Array (OpTy Provenance)) (dest : MPlaceTy Provenance) : M S Unit := do
  let (fixed,rest) ← ShimSignatures.variadic h.signatures name (h.signature "syscall") 1 abi args
  let random ← h.libcUsize "SYS_getrandom"
  let futex ← h.libcUsize "SYS_futex"
  let event ← h.libcUsize "SYS_eventfd2"
  let tid ← h.libcUsize "SYS_gettid"
  let accept ← h.libcUsize "SYS_accept4"
  let op ← h.readUsize (← arg fixed 0)
  if op == random then
    let args ← checked h.signatures h.typeBudget h.argumentTypes #[.voidPointer,.usize,.i32] rest
    let pointer ← h.readPointer (← arg args 0)
    let length ← h.readUsize (← arg args 1)
    let _ ← h.readI32 (← arg args 2)
    -- Source reads, but does not reject, the flags on this syscall path.
    RandomMemory.generate h.random pointer length
    h.writeTargetUsize length dest
  else if op == futex then
    h.futex rest dest
  else if op == event then
    let args ← checked h.signatures h.typeBudget h.argumentTypes #[.u32,.i32] rest
    let result ← EventFd.create h.event (← arg args 0) (← arg args 1)
    h.writeInt result.toInt dest
  else if op == tid then
    let result ← h.unixGettid "SYS_gettid"
    h.writeInt (Int.ofNat result.toNat) dest
  else if op == accept then
    let args ← checked h.signatures h.typeBudget h.argumentTypes #[.i32,.sockaddrPointer,.socklenPointer,.i32] rest
    h.accept4 args dest
  else throw (.unsupported s!"unsupported syscall number {op}")

def prctlCore (h : PrctlHooks S D MD Ptr B I) (name : String) (abi : FnAbi TyId)
    (args : Array (OpTy Provenance)) (dest : MPlaceTy Provenance) : M S Unit := do
  let (fixed,rest) ← ShimSignatures.variadic h.signatures name (h.signature "prctl") 1 abi args
  let setName ← h.libcI32 "PR_SET_NAME"
  let getName ← h.libcI32 "PR_GET_NAME"
  let op ← h.readI32 (← arg fixed 0)
  if op == setName then
    let args ← checked h.signatures h.typeBudget h.argumentTypes #[.charPointer] rest
    let name ← h.signatures.readScalar (← arg args 0)
    let some threadHooks := h.thread |
      throw (.unsupported "source prctl thread-name operation lacks the Unix thread capability")
    let thread ← UnixThread.self threadHooks
    let result ← UnixThread.setName threadHooks thread name 16 true
    unless result == .ok do throw (.invalidProgram "PR_SET_NAME source ThreadNameResult assertion")
  else if op == getName then
    let args ← checked h.signatures h.typeBudget h.argumentTypes #[.charPointer] rest
    let name ← h.signatures.readScalar (← arg args 0)
    let some threadHooks := h.thread |
      throw (.unsupported "source prctl thread-name operation lacks the Unix thread capability")
    let thread ← UnixThread.self threadHooks
    let length ← match Scalar.fromUInt (BitVec.ofNat 128 16) h.signatures.types.target.pointerSize with
      | .ok length => pure length
      | .error error => throw (ScalarOps.scalarError error)
    h.checkAccess (← threadHooks.scalarPointer name) (Size.ofBytes 16)
    let result ← UnixThread.getName threadHooks thread name length false
    unless result == .ok do throw (.invalidProgram "PR_GET_NAME source ThreadNameResult assertion")
  else throw (.unsupported s!"unsupported prctl operation {op}")
  -- Source writes Scalar::from_u32(0), rather than a destination-sized integer.
  let zero ← match Scalar.fromUInt (BitVec.ofNat 128 0) (Size.ofBytes 4) with
    | .ok zero => pure zero
    | .error error => throw (ScalarOps.scalarError error)
  h.writeScalar zero dest

def prctl (h : Hooks S R F D B I) (name : String) (abi : FnAbi TyId)
    (args : Array (OpTy Provenance)) (dest : MPlaceTy Provenance) : M S Unit :=
  prctlCore {
    signatures := h.signatures
    signature := h.signature
    argumentTypes := h.argumentTypes
    typeBudget := h.typeBudget
    libcI32 := h.libcI32
    readI32 := h.readI32
    writeScalar := h.writeScalar
    thread := some h.thread
    checkAccess := h.checkAccess } name abi args dest

def syscall (h : Hooks S R F D B I) (name : String) (abi : FnAbi TyId)
    (args : Array (OpTy Provenance)) (dest : MPlaceTy Provenance) : M S Unit := do
  let core : SyscallHooks S D (MPlaceTy Provenance) (Pointer (Option Provenance)) B I F := {
    signatures := h.signatures
    signature := h.signature
    argumentTypes := h.argumentTypes
    typeBudget := h.typeBudget
    libcUsize := h.libcUsize
    readUsize := h.readUsize
    readI32 := h.readI32
    readPointer := h.readPointer
    writeTargetUsize := h.writeTargetUsize
    writeInt := h.writeInt
    writeScalar := h.writeScalar
    random := h.random
    event := h.event
    unixGettid := h.unixGettid
    futex := fun rest dest => do
      let takeArgs := fun types args =>
        checked h.signatures h.typeBudget h.argumentTypes types args
      let futexHooks := {h.futex with takeArgs := takeArgs}
      LinuxFutex.syscall futexHooks rest dest
    accept4 := fun args dest => do
      h.accept4 (← arg args 0) (← arg args 1) (← arg args 2) (← arg args 3) dest }
  syscallCore core name abi args dest

/-- Install the real source type checker for futex vararg prefixes. -/
def bindFutexArgs (h : Hooks S R F D B I) : LinuxFutex.Hooks S R :=
  let takeArgs := fun types args =>
    checked h.signatures h.typeBudget h.argumentTypes types args
  {h.futex with takeArgs := takeArgs}
end Miri.Interpreter.LinuxSyscall
