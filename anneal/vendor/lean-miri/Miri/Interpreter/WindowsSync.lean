import Miri.Concurrency.InitOnce
import Miri.Concurrency.SyncObject
import Miri.Memory.Scalar

/-! Entire pinned shims/windows/sync.rs. Pinned source implements InitOnce and
address waits, not SRW/CriticalSection/ConditionVariable aliases. -/
namespace Miri.Interpreter.WindowsSync
open Miri.ABI Miri.Memory Miri.Concurrency
abbrev M := EStateM StepError
inductive Constant where
  | trueValue | falseValue | initFailed | infinite | invalidParameter | timeout
  deriving DecidableEq, Repr
inductive Payload (R : Type) where | initOnce (ref : R) | futex (ref : R)
structure Hooks (S R : Type) where
  once : InitOnce.Hooks S R Int32 (MPlaceTy Provenance)
  metadata : SyncObject.Hooks S (Payload R)
  constant32 : Constant → M S UInt32
  constantBool : Constant → M S Int32
  readPointer : OpTy Provenance → M S (Pointer (Option Provenance))
  isNull : Pointer (Option Provenance) → M S Bool
  readU32 : OpTy Provenance → M S UInt32
  readUsize : OpTy Provenance → M S UInt64
  derefInitOnce : OpTy Provenance → M S (MPlaceTy Provenance)
  readInitPointerFieldZero : MPlaceTy Provenance → M S UInt64
  derefPendingBool : OpTy Provenance → M S (MPlaceTy Provenance)
  newFutex : M S R
  monotonicDeadlineMillis : UInt32 → M S ThreadDeadline
  seqCstFence : M S Unit
  readAtomicAcquire : Pointer (Option Provenance) → Size → M S (Scalar Provenance)
  readScalar : Pointer (Option Provenance) → Size → M S (Scalar Provenance)
  lastError : Constant → M S Unit
private def rt (h : Hooks S R) := h.once.runtime
private def typed (h : Hooks S R) (once : Bool) : SyncObject.Hooks S (Payload R) := {
  h.metadata with lookup := fun address => do
    let some value ← h.metadata.lookup address | return none
    match value.payload with
    | .initOnce _ => return if once then some value else none
    | .futex _ => return if once then none else some value }
private def initOnceObject (h : Hooks S R) (ref : R) : SyncObject.Object S (Payload R) := {
  payload := .initOnce ref
  deleteOnWrite := true
  onAccess := fun _ => do
    if !(← h.once.get ref).waiters.isEmpty then
      throw (.undefinedBehavior "access of INIT_ONCE forbidden while queue non-empty") }
private def futexObject (ref : R) : SyncObject.Object S (Payload R) := {
  payload := .futex ref
  -- Exact source `impl SyncObj for WindowsFutex {}` defaults.
  deleteOnWrite := false
  onAccess := fun _ => pure () }

def initOnceData (h : Hooks S R) (op : OpTy Provenance) : M S R := do
  let object ← h.derefInitOnce op
  let value ← SyncObject.getImmovableWithStaticInit (typed h true) object Size.ZERO 0 1 do
    if (← h.readInitPointerFieldZero object) != 0 then
      throw (.undefinedBehavior "INIT_ONCE not properly initialized at this location or overwritten")
    return initOnceObject h (← h.once.new)
  let .initOnce ref := value.payload | throw (.invalidProgram "INIT_ONCE metadata type mismatch")
  return ref

def tryBegin (h : Hooks S R) (ref : R) (pending dest : MPlaceTy Provenance) : M S Bool := do
  match (← h.once.get ref).status with
  | .Uninitialized =>
    InitOnce.begin h.once ref
    (rt h).writeScalar (← h.constantBool .trueValue) pending
    (rt h).writeScalar (← h.constantBool .trueValue) dest
    return true
  | .Complete =>
    InitOnce.observeCompleted h.once ref
    (rt h).writeScalar (← h.constantBool .falseValue) pending
    (rt h).writeScalar (← h.constantBool .trueValue) dest
    return true
  | .Begun => return false

def beginInitialize (h : Hooks S R) (op flags pending context : OpTy Provenance)
    (dest : MPlaceTy Provenance) : M S Unit := do
  let ref ← initOnceData h op
  let flags ← h.readU32 flags
  let pending ← h.derefPendingBool pending
  let context ← h.readPointer context
  if flags != 0 then throw (.unsupported "unsupported dwFlags in InitOnceBeginInitialize")
  if !(← h.isNull context) then throw (.unsupported "non-null lpContext in InitOnceBeginInitialize")
  if ← tryBegin h ref pending dest then return
  InitOnce.enqueueAndBlock h.once ref (fun kind => do
    if kind != .Ready then throw (.invalidProgram "INIT_ONCE callback must be Ready")
    if !(← tryBegin h ref pending dest) then
      throw (.invalidProgram "woken INIT_ONCE try_begin still failed")) (some (.windowsInitOnce ref pending dest))

def complete (h : Hooks S R) (op flags context : OpTy Provenance) : M S Int32 := do
  let ref ← initOnceData h op
  let flags ← h.readU32 flags
  let context ← h.readPointer context
  let success ← if flags == 0 then pure true
    else if flags == (← h.constant32 .initFailed) then pure false
    else throw (.unsupported "unsupported dwFlags in InitOnceComplete")
  if !(← h.isNull context) then throw (.unsupported "non-null lpContext in InitOnceComplete")
  if (← h.once.get ref).status != .Begun then
    throw (.undefinedBehavior "InitOnceComplete called before beginning or after completion")
  if success then InitOnce.complete h.once ref else InitOnce.fail h.once ref
  h.constantBool .trueValue
private def futexData (h : Hooks S R) (pointer : Pointer (Option Provenance)) : M S (Option R) := do
  let value ← SyncObject.getOrInit (typed h false) pointer do
    return futexObject (← h.newFutex)
  match value with
  | none => return none
  | some value =>
    let .futex ref := value.payload | throw (.invalidProgram "Windows futex metadata type mismatch")
    return some ref

def waitOnAddress (h : Hooks S R) (pointer compare size timeout : OpTy Provenance)
    (dest : MPlaceTy Provenance) : M S Unit := do
  let pointer ← h.readPointer pointer
  let compare ← h.readPointer compare
  let size ← h.readUsize size
  let timeout ← h.readU32 timeout
  if size != 1 && size != 2 && size != 4 && size != 8 then
    h.lastError .invalidParameter
    (rt h).writeScalar 0 dest
    return
  let deadline ← if timeout == (← h.constant32 .infinite) then pure none
    else (h.monotonicDeadlineMillis timeout).map some
  h.seqCstFence
  let value ← h.readAtomicAcquire pointer (Size.ofBytes size)
  let comparison ← h.readScalar compare (Size.ofBytes size)
  if value == comparison then
    let some ref ← futexData h pointer | throw (.invalidProgram "atomic-readable Windows futex has no mutable data byte")
    SyncRuntime.futexWait (rt h) ref (UInt32.ofNat (2^32 - 1)) deadline (fun kind => do
      match kind with
      | .Ready => (rt h).writeScalar 1 dest
      | .TimedOut => h.lastError .timeout; (rt h).writeScalar 0 dest) (some (.windowsAddress dest))
  -- Source writes 1 even after blocking. Timeout callback overwrites it later.
  (rt h).writeScalar 1 dest

def wakeByAddress (h : Hooks S R) (pointer : OpTy Provenance) (all : Bool) : M S Unit := do
  let pointer ← h.readPointer pointer
  h.seqCstFence
  let some ref ← futexData h pointer | return
  let count := if all then 2^(rt h).usizeBits - 1 else 1
  let _ ← SyncRuntime.futexWake (rt h) ref (UInt32.ofNat (2^32 - 1)) count
end Miri.Interpreter.WindowsSync
