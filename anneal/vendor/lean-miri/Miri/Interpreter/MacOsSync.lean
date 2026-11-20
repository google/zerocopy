import Miri.Interpreter.TimeShims
import Miri.Concurrency.SyncObject

/-! Pinned unix/macos/sync.rs. Atomic operations, compiler layouts and actual
object allocation remain required effects; clock/queue/object policy is here. -/
namespace Miri.Interpreter.MacOsSync
open Miri.ABI Miri.Memory Miri.Concurrency
abbrev M := EStateM StepError
inductive Unfair (R : Type) where | active (ref : R) | permanentlyLocked
structure Semaphore (R : Type) where
  ref : R
  initial : UInt64
inductive Timeout where
  | none
  | relative (clock duration : OpTy Provenance)
  | absolute (clock duration : OpTy Provenance)
structure Hooks (S R : Type) where
  endian : Endian
  runtime : SyncRuntime.Hooks S R Int32 (MPlaceTy Provenance)
  readPointer : OpTy Provenance → M S (Pointer (Option Provenance))
  readImmediate : OpTy Provenance → M S (RvalueImmTy Provenance)
  readUsize : OpTy Provenance → M S UInt64
  readIsize : OpTy Provenance → M S Int
  readU32 : OpTy Provenance → M S UInt32
  readU64 : OpTy Provenance → M S UInt64
  readI64 : OpTy Provenance → M S Int64
  libcU32 : String → M S UInt32
  timeout : Clock.TimeoutStyle → Clock.Duration → M S ThreadDeadline
  /-- epoch().add_lossy(Duration::from_nanos(value)). -/
  absoluteDeadline : UInt64 → M S ThreadDeadline
  /-- now().add_lossy(delta).duration_since(epoch()), exact host/virtual clock. -/
  timeAfter : UInt64 → M S Nat
  readAcquireBits : Pointer (Option Provenance) → UInt64 → M S U128
  seqCstFence : M S Unit
  futexMetadata : SyncObject.MetadataHooks S R
  newFutex : UInt64 → Bool → M S R
  settings : R → M S (UInt64 × Bool)
  putSettings : R → UInt64 → Bool → M S Unit
  lockMetadata : SyncObject.Hooks S (Unfair R)
  semaphoreMetadata : SyncObject.Hooks S (Semaphore R)
  derefLock : OpTy Provenance → M S (MPlaceTy Provenance)
  derefByte : RvalueImmTy Provenance → M S (MPlaceTy Provenance)
  readLockValue : MPlaceTy Provenance → M S UInt32
  newMutex : M S R
  newSemaphore : UInt64 → M S R
  allocateRuntimeByte : M S (MPlaceTy Provenance)
  immediatePointer : RvalueImmTy Provenance → M S (Pointer (Option Provenance))
  deallocateRuntime : Pointer (Option Provenance) → M S Unit
  resetLockRelaxed : OpTy Provenance → M S Unit
  writePointer : Pointer (Option Provenance) → MPlaceTy Provenance → M S Unit
  writeInt : Int → MPlaceTy Provenance → M S Unit
  writeBool : Bool → MPlaceTy Provenance → M S Unit
  errnoNegOne : String → MPlaceTy Provenance → M S Unit
  hostUsizeBits : Nat
  semaphoreBudget : Nat
private def abort (message : String) : M S A := throw (.termination (.abort message))
private def duration (nanoseconds : UInt64) : M S Clock.Duration :=
  match Clock.Duration.fromNanos nanoseconds.toNat with
  | .ok value => pure value | .error error => throw error
private def count (h : Hooks S R) (ref : R) (dest : MPlaceTy Provenance) : M S Unit := do
  let count := (← h.runtime.futex ref).waiters.length
  if count >= 2^31 then throw (.invalidProgram "macOS futex waiter count i32 conversion")
  h.writeInt count dest
private def futex (h : Hooks S R) (ptr : Pointer (Option Provenance)) (size : UInt64) (shared : Bool) : M S (Option R) := do
  let object ← SyncObject.getOrInitMetadata h.futexMetadata ptr do
    return {payload := ← h.newFutex size shared, deleteOnWrite := false, onAccess := fun _ => pure ()}
  return object.map (·.payload)

def waitAddress (h : Hooks S R) (address value size flags : OpTy Provenance)
    (timeout : Timeout) (dest : MPlaceTy Provenance) : M S Unit := do
  let noneFlag ← h.libcU32 "OS_SYNC_WAIT_ON_ADDRESS_NONE"
  let sharedFlag ← h.libcU32 "OS_SYNC_WAIT_ON_ADDRESS_SHARED"
  let absoluteClock ← h.libcU32 "OS_CLOCK_MACH_ABSOLUTE_TIME"
  let ptr ← h.readPointer address
  let value ← h.readU64 value
  let size ← h.readUsize size
  let flags ← h.readU32 flags
  let clockTime ← match timeout with
    | .none => pure none
    | .relative clock time => do pure (some (← h.readU32 clock,Clock.TimeoutStyle.relative,← h.readU64 time))
    | .absolute clock time => do pure (some (← h.readU32 clock,Clock.TimeoutStyle.absolute,← h.readU64 time))
  let addr := ptr.offset.bytes
  if addr == 0 || (size != 4 && size != 8) || addr % size != 0 ||
      (flags != noneFlag && flags != sharedFlag) || clockTime.any (fun (clock,_,time) => clock != absoluteClock || time == 0) then
    h.errnoNegOne "EINVAL" dest
    return
  let shared := flags == sharedFlag
  let deadline ← clockTime.mapM fun (_,style,time) => do h.timeout style (← duration time)
  h.seqCstFence
  let valueAtAddress ← h.readAcquireBits ptr size
  let some ref ← futex h ptr size shared | throw (.invalidProgram "acquire-read macOS futex lost allocation")
  if (← h.runtime.futex ref).waiters.isEmpty then h.putSettings ref size shared
  else if (← h.settings ref) != (size,shared) then
    h.errnoNegOne "EINVAL" dest
    return
  if valueAtAddress.toNat == value.toNat then
    SyncRuntime.futexWait h.runtime ref 0xffffffff deadline (fun kind => do
      match kind with
      | .Ready => count h ref dest
      | .TimedOut => h.errnoNegOne "ETIMEDOUT" dest) (some (.macAddress ref dest))
  else count h ref dest

def wakeAddress (h : Hooks S R) (address size flags : OpTy Provenance) (all : Bool) (dest : MPlaceTy Provenance) : M S Unit := do
  let noneFlag ← h.libcU32 "OS_SYNC_WAKE_BY_ADDRESS_NONE"
  let sharedFlag ← h.libcU32 "OS_SYNC_WAKE_BY_ADDRESS_SHARED"
  let ptr ← h.readPointer address
  let size ← h.readUsize size
  let flags ← h.readU32 flags
  if ptr.offset.bytes == 0 || (size != 4 && size != 8) || (flags != noneFlag && flags != sharedFlag) then
    h.errnoNegOne "EINVAL" dest
    return
  let shared := flags == sharedFlag
  let some ref ← futex h ptr size shared |
    h.errnoNegOne "ENOENT" dest
    return
  if (← h.runtime.futex ref).waiters.isEmpty then
    h.errnoNegOne "ENOENT" dest
    return
  if (← h.settings ref) != (size,shared) then
    h.errnoNegOne "EINVAL" dest
    return
  h.seqCstFence
  let _ ← SyncRuntime.futexWake h.runtime ref 0xffffffff (if all then 2^h.hostUsizeBits-1 else 1)
  h.writeInt 0 dest

private def lockObject (h : Hooks S R) (value : Unfair R) : SyncObject.Object S (Unfair R) := {
  payload := value
  deleteOnWrite := true
  onAccess := fun _ => do
    if let .active ref := value then
      unless (← h.runtime.mutex ref).queue.isEmpty do
        throw (.undefinedBehavior "access of os_unfair_lock while its queue is nonempty") }
private def lockData (h : Hooks S R) (op : OpTy Provenance) : M S (Unfair R) := do
  if h.endian != .little then throw (.invalidProgram "os_unfair_lock requires little endian")
  let place ← h.derefLock op
  let object ← SyncObject.getImmovableWithStaticInit h.lockMetadata place .ZERO 0 1 do
    let value ← h.readLockValue place
    if value == 0 then return lockObject h (.active (← h.newMutex))
    if value == 1 then return lockObject h .permanentlyLocked
    throw (.undefinedBehavior "os_unfair_lock improperly initialized or overwritten")
  return object.payload

def lock (h : Hooks S R) (op : OpTy Provenance) : M S Unit := do
  let .active ref ← lockData h op | throw (.unsupported "locking a copied locked os_unfair_lock")
  if let some owner := (← h.runtime.mutex ref).owner then
    if owner == (← h.runtime.threads).activeThread then abort "reentrant os_unfair_lock locking"
    SyncRuntime.mutexEnqueue h.runtime ref none
  else SyncRuntime.mutexLock h.runtime ref

def tryLock (h : Hooks S R) (op : OpTy Provenance) (dest : MPlaceTy Provenance) : M S Unit := do
  let .active ref ← lockData h op |
    h.writeBool false dest
    return
  if (← h.runtime.mutex ref).owner.isSome then h.writeBool false dest
  else
    SyncRuntime.mutexLock h.runtime ref
    h.writeBool true dest

def unlock (h : Hooks S R) (op : OpTy Provenance) : M S Unit := do
  let .active ref ← lockData h op | throw (.unsupported "unlocking a copied locked os_unfair_lock")
  if (← SyncRuntime.mutexUnlock h.runtime ref) == .returnedNone then abort "unlocking os_unfair_lock without ownership"
  if (← h.runtime.mutex ref).owner.isNone then h.resetLockRelaxed op

def assertOwner (h : Hooks S R) (op : OpTy Provenance) (owned : Bool) : M S Unit := do
  let .active ref ← lockData h op | throw (.unsupported "asserting owner of copied locked os_unfair_lock")
  let owner := (← h.runtime.mutex ref).owner
  let active := (← h.runtime.threads).activeThread
  if owned then
    if owner != some active then abort "os_unfair_lock_assert_owner without ownership"
  else
    if owner == some active then abort "os_unfair_lock_assert_not_owner with ownership"
    if owner.isNone then h.resetLockRelaxed op

private def semaphoreObject (h : Hooks S R) (value : Semaphore R) : SyncObject.Object S (Semaphore R) := {
  payload := value
  deleteOnWrite := true
  onAccess := fun _ => do
    unless (← h.runtime.semaphore value.ref).waiters.isEmpty do
      throw (.undefinedBehavior "access of os_unfair_lock while its queue is nonempty") }
private def semaphoreData (h : Hooks S R) (immediate : RvalueImmTy Provenance) : M S (Semaphore R) := do
  let place ← h.derefByte immediate
  let object ← SyncObject.getImmovableWithStaticInit h.semaphoreMetadata place .ZERO 0 1
    (throw (.undefinedBehavior "dispatch_semaphore_t not initialized with dispatch_semaphore_create"))
  return object.payload

def semaphoreCreate (h : Hooks S R) (value : OpTy Provenance) (dest : MPlaceTy Provenance) : M S Unit := do
  let value ← h.readIsize value
  if value < 0 then abort "dispatch_semaphore_create with negative value"
  if value >= 2^64 then throw (.invalidProgram "dispatch semaphore initial value exceeds u64")
  let value := UInt64.ofNat value.toNat
  let allocation ← h.allocateRuntimeByte
  let data : Semaphore R := ⟨← h.newSemaphore value,value⟩
  let _ ← SyncObject.initImmovable h.semaphoreMetadata allocation .ZERO 1 (semaphoreObject h data)
  h.writePointer allocation.mplace.ptr dest

def semaphoreWait (h : Hooks S R) (sem timeout : OpTy Provenance) (dest : MPlaceTy Provenance) : M S Unit := do
  let sem ← h.readImmediate sem
  let timeout ← h.readU64 timeout
  let deadline ← if timeout == 0xffffffffffffffff then pure none else (h.absoluteDeadline timeout).map some
  let data ← semaphoreData h sem
  SyncRuntime.semaphoreDecrement h.semaphoreBudget h.runtime data.ref deadline (fun kind =>
    h.writeInt (if kind == .Ready then 0 else 1) dest) (some (.macSemaphore dest))

def semaphoreSignal (h : Hooks S R) (sem : OpTy Provenance) (dest : MPlaceTy Provenance) : M S Unit := do
  let sem ← h.readImmediate sem
  let data ← semaphoreData h sem
  let woke ← SyncRuntime.semaphoreIncrement h.runtime data.ref
  h.writeInt (if woke then 1 else 0) dest

def release (h : Hooks S R) (sem : OpTy Provenance) : M S Unit := do
  let sem ← h.readImmediate sem
  let data ← semaphoreData h sem
  if (← h.runtime.semaphore data.ref).value < data.initial then abort "dispatch_semaphore destroyed while in use"
  h.deallocateRuntime (← h.immediatePointer sem)

def dispatchTime (h : Hooks S R) (when delta : OpTy Provenance) (dest : MPlaceTy Provenance) : M S Unit := do
  let when ← h.readU64 when
  let delta ← h.readI64 delta
  if when != 0 then throw (.unsupported "dispatch_time requires DISPATCH_TIME_NOW")
  if delta.toInt < 0 then throw (.unsupported "dispatch_time negative delta")
  let nanos ← h.timeAfter delta.toUInt64
  if nanos >= 2^64 then throw (.unsupported "dispatch_time delta too big")
  h.writeInt nanos dest
end Miri.Interpreter.MacOsSync
