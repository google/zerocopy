import Miri.Interpreter.ThreadMachine
import Miri.Interpreter.MemoryShims

/-! Pinned unix/thread.rs, including actual create/join/detach/name policy.
The pthread ABI type is always a compiler query, never an assumed host integer. -/
namespace Miri.Interpreter.UnixThread
open Miri.ABI Miri.Memory Miri.MIR Miri.Concurrency
abbrev M := EStateM StepError
inductive NameResult where | ok | tooLong deriving DecidableEq, Repr
structure Hooks (S : Type) where
  pthreadLayout : M S LocalLayout
  unitPointerLayout : M S LocalLayout
  readScalar : OpTy Provenance → M S (Scalar Provenance)
  readPointer : OpTy Provenance → M S (Pointer (Option Provenance))
  readImmediate : OpTy Provenance → M S (RvalueImmTy Provenance)
  dereference : OpTy Provenance → LocalLayout → M S (MPlaceTy Provenance)
  isNull : Pointer (Option Provenance) → M S Bool
  scalarPointer : Scalar Provenance → M S (Pointer (Option Provenance))
  scalarUsize : Scalar Provenance → M S UInt64
  readCString : Pointer (Option Provenance) → M S ByteArray
  writeCString : ByteArray → Pointer (Option Provenance) → UInt64 → M S (Bool × UInt64)
  threads : M S ThreadManager
  putThreads : ThreadManager → M S Unit
  start : Option (MPlaceTy Provenance) → Pointer (Option Provenance) → RvalueImmTy Provenance → LocalLayout → M S Unit
  join : ThreadId → Scalar Provenance → MPlaceTy Provenance → M S Unit
  detach : ThreadId → M S Unit
  hostUsizeBits : Nat
private def lift (value : Except StepError A) : M S A :=
  match value with | .ok value => pure value | .error error => throw error
private def rawId (h : Hooks S) (raw : Int) : M S (Except ThreadError ThreadId) := do
  if raw < 0 then return .error .invalidId
  return (← h.threads).threadIdTryFrom raw.toNat
private def checkedId (h : Hooks S) (value : Scalar Provenance) (terminatedAllowed : Bool) : M S ThreadId := do
  let layout ← h.pthreadLayout
  let id ← lift (value.toInt layout.layout.size |>.mapError ScalarOps.scalarError)
  match ← rawId h id with
  | .ok id => return id
  | .error (.terminated id) =>
    if terminatedAllowed then return id
    throw (.undefinedBehavior "pthread name operation on invalid pthread_t handle")
  | .error _ => throw (.undefinedBehavior "invalid pthread_t handle")

def create (h : Hooks S) (thread _attr start argument : OpTy Provenance) : M S Unit := do
  let output ← h.dereference thread (← h.pthreadLayout)
  let start ← h.readPointer start
  let argument ← h.readImmediate argument
  h.start (some output) start argument (← h.unitPointerLayout)

def join (h : Hooks S) (thread result : OpTy Provenance) (dest : MPlaceTy Provenance) : M S Unit := do
  if !(← h.isNull (← h.readPointer result)) then
    throw (.unsupported "Miri supports pthread_join only with retval NULL")
  let id ← checkedId h (← h.readScalar thread) true
  let zero ← lift (Scalar.fromUInt (BitVec.ofNat 128 0) (Size.ofBytes 4) |>.mapError ScalarOps.scalarError)
  h.join id zero dest

def detach (h : Hooks S) (thread : OpTy Provenance) : M S (Scalar Provenance) := do
  h.detach (← checkedId h (← h.readScalar thread) true)
  lift (Scalar.fromUInt (BitVec.ofNat 128 0) (Size.ofBytes 4) |>.mapError ScalarOps.scalarError)

def self (h : Hooks S) : M S (Scalar Provenance) := do
  let id := (← h.threads).activeThread
  let layout ← h.pthreadLayout
  lift (Scalar.fromUInt (BitVec.ofNat 128 id.toNat) layout.layout.size |>.mapError ScalarOps.scalarError)

def setName (h : Hooks S) (thread name : Scalar Provenance)
    (maximum : UInt64) (truncate : Bool) : M S NameResult := do
  let thread ← checkedId h thread false
  let pointer ← h.scalarPointer name
  let mut name ← h.readCString pointer
  if name.size >= 2^64 then throw (.invalidProgram "pthread name length exceeds u64")
  if name.size >= maximum.toNat then
    if !truncate then return .tooLong
    let limit := maximum.toNat-1
    if limit >= 2^h.hostUsizeBits then throw (.invalidProgram "pthread name truncate usize conversion")
    name := name.extract 0 limit
  let manager ← match (← h.threads).setThreadName thread name.data.toList with
    | .ok manager => pure manager
    | .error error => throw (.invalidProgram s!"validated thread name target missing: {reprStr error}")
  h.putThreads manager
  return .ok

def getName (h : Hooks S) (thread output length : Scalar Provenance)
    (truncate : Bool) : M S NameResult := do
  let thread ← checkedId h thread false
  let pointer ← h.scalarPointer output
  let length ← h.scalarUsize length
  let some record := (← h.threads).thread? thread
    | throw (.invalidProgram "validated pthread name target missing")
  let name := record.threadName.getD "<unnamed>".toUTF8.data.toList
  let size := min length.toNat (2^h.hostUsizeBits-1)
  let name := if truncate then name.take (min name.length (size-1)) else name
  let (success,_) ← h.writeCString ⟨name.toArray⟩ pointer length
  return if success then .ok else .tooLong

def schedYield (h : Hooks S) : M S Unit := do
  h.putThreads (ThreadManager.yield (← h.threads))
end Miri.Interpreter.UnixThread
