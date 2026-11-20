import Miri.Interpreter.PthreadObjects

/-! Portable pthread wrappers from pinned shims/unix/sync.rs:532–1151. -/
namespace Miri.Interpreter.PthreadSync
open Miri.ABI Miri.Memory Miri.Concurrency PthreadObjects
abbrev M := EStateM StepError
inductive Constant where
  | mutexNormal | mutexDefault | mutexErrorCheck | mutexRecursive
  | einval | ebusy | edeadlk | eperm | etimedout | clockRealtime
  deriving DecidableEq, Repr
inductive Attribute where | mutex | condvar deriving DecidableEq, Repr
structure Hooks (S R Duration : Type) where
  objects : PthreadObjects.Hooks S R
  constant : Constant → M S Int32
  readPointer : OpTy Provenance → M S (Pointer (Option Provenance))
  isNull : Pointer (Option Provenance) → M S Bool
  attributeRead : OpTy Provenance → Attribute → Size → M S Int32
  attributeWrite : OpTy Provenance → Attribute → Size → Int32 → M S Unit
  attributeUninit : OpTy Provenance → Attribute → M S Unit
  objectUninit : OpTy Provenance → PthreadObjects.Kind → M S Unit
  parseClock : Int32 → M S (Option Clock)
  readTimespec : OpTy Provenance → M S (Option Duration)
  timeout : Clock → Bool → Duration → M S ThreadDeadline
  noIsolation : String → M S Unit
  setErrnoAndReturnNeg1 : Constant → MPlaceTy Provenance → M S Unit
  writeClockId : OpTy Provenance → Int32 → M S Unit
private def rt (h : Hooks S R T) := h.objects.runtime
private def zero (h : Hooks S R T) (dest : MPlaceTy Provenance) : M S Unit :=
  (rt h).writeScalar 0 dest
private def attrOffset (h : Hooks S R T) (attr : Attribute) : M S Size := do
  let os := h.objects.os
  let supported := if attr == .mutex then
      #["linux","illumos","solaris","macos","freebsd","android","netbsd"].contains os
    else #["linux","illumos","solaris","freebsd","android"].contains os
  if !supported then throw (.unsupported "pthread attribute layout unsupported on this target")
  return Size.ZERO
private def attrRead (h : Hooks S R T) (op : OpTy Provenance) (kind : Attribute) : M S Int32 := do
  h.attributeRead op kind (← attrOffset h kind)
private def attrWrite (h : Hooks S R T) (op : OpTy Provenance) (kind : Attribute) (value : Int32) : M S Unit := do
  h.attributeWrite op kind (← attrOffset h kind) value
private def mutexData (h : Hooks S R T) (op : OpTy Provenance) : M S (R × MutexKind) := do
  let .mutex ref kind ← PthreadObjects.get h.objects .mutex op
    | throw (.invalidProgram "pthread mutex metadata dynamic type mismatch")
  return (ref,kind)
private def rwlockData (h : Hooks S R T) (op : OpTy Provenance) : M S R := do
  let .rwlock ref ← PthreadObjects.get h.objects .rwlock op
    | throw (.invalidProgram "pthread rwlock metadata dynamic type mismatch")
  return ref
private def condvarData (h : Hooks S R T) (op : OpTy Provenance) : M S (R × Clock) := do
  let .condvar ref clock ← PthreadObjects.get h.objects .condvar op
    | throw (.invalidProgram "pthread condvar metadata dynamic type mismatch")
  return (ref,clock)
private def semData (h : Hooks S R T) (op : OpTy Provenance) : M S R := do
  let .semaphore ref ← PthreadObjects.get h.objects .semaphore op
    | throw (.invalidProgram "pthread semaphore metadata dynamic type mismatch")
  return ref

def unchangedKind : Int32 := 0x8000000

def translateKind (h : Hooks S R T) (kind : Int32) : M S MutexKind := do
  if kind == (← h.constant .mutexNormal) then return .Normal
  if kind == (← h.constant .mutexErrorCheck) then return .ErrorCheck
  if kind == (← h.constant .mutexRecursive) then return .Recursive
  if kind == (← h.constant .mutexDefault) || kind == unchangedKind then return .Default
  throw (.unsupported "unsupported pthread mutex type")
def mutexattrInit (h : Hooks S R T) (attr : OpTy Provenance) : M S Unit :=
  attrWrite h attr .mutex unchangedKind
private def supportedKind (h : Hooks S R T) (kind : Int32) : M S Bool := do
  if kind == (← h.constant .mutexNormal) then return true
  if kind == (← h.constant .mutexDefault) then return true
  if kind == (← h.constant .mutexErrorCheck) then return true
  return kind == (← h.constant .mutexRecursive)
def mutexattrSettype (h : Hooks S R T) (attr : OpTy Provenance) (kind : Int32) : M S Int32 := do
  if ← supportedKind h kind then
    if kind == unchangedKind then throw (.invalidProgram "libc mutex type equals internal unchanged marker")
    attrWrite h attr .mutex kind
    return 0
  h.constant .einval

def mutexattrDestroy (h : Hooks S R T) (attr : OpTy Provenance) : M S Unit := do
  let _ ← attrRead h attr .mutex
  h.attributeUninit attr .mutex

def mutexInit (h : Hooks S R T) (op attr : OpTy Provenance) : M S Unit := do
  let pointer ← h.readPointer attr
  let kind ← if ← h.isNull pointer then pure MutexKind.Default else translateKind h (← attrRead h attr .mutex)
  -- Source dereferences the object before constructing the new reference.
  let object ← h.objects.deref op .mutex
  let ref ← h.objects.newMutex
  PthreadObjects.createAt h.objects object (.mutex ref kind)

def mutexLock (h : Hooks S R T) (op : OpTy Provenance) (dest : MPlaceTy Provenance) : M S Unit := do
  let (ref,kind) ← mutexData h op
  if let some owner := (← (rt h).mutex ref).owner then
    if owner != (← (rt h).threads).activeThread then
      SyncRuntime.mutexEnqueue (rt h) ref (some (0,dest))
      return
    match kind with
    | .Default => throw (.undefinedBehavior "acquiring default mutex already locked by current thread")
    | .Normal => throw (.machineStop "local deadlock")
    | .ErrorCheck => (rt h).writeScalar (← h.constant .edeadlk) dest
    | .Recursive => SyncRuntime.mutexLock (rt h) ref; zero h dest
  else
    SyncRuntime.mutexLock (rt h) ref
    zero h dest

def mutexTrylock (h : Hooks S R T) (op : OpTy Provenance) : M S Int32 := do
  let (ref,kind) ← mutexData h op
  if let some owner := (← (rt h).mutex ref).owner then
    if owner != (← (rt h).threads).activeThread || kind != .Recursive then return ← h.constant .ebusy
  SyncRuntime.mutexLock (rt h) ref
  return 0

def mutexUnlock (h : Hooks S R T) (op : OpTy Provenance) : M S Int32 := do
  let (ref,kind) ← mutexData h op
  match ← SyncRuntime.mutexUnlock (rt h) ref with
  | .returnedSome _ => pure 0
  | .returnedNone =>
    match kind with
    | .Default | .Normal => throw (.undefinedBehavior "unlocked mutex not owned by current thread")
    | .ErrorCheck | .Recursive => h.constant .eperm

def mutexDestroy (h : Hooks S R T) (op : OpTy Provenance) : M S Unit := do
  let (ref,_) ← mutexData h op
  if (← (rt h).mutex ref).owner.isSome then throw (.undefinedBehavior "destroyed a locked mutex")
  h.objectUninit op .mutex

def rwlockRead (h : Hooks S R T) (op : OpTy Provenance) (dest : MPlaceTy Provenance) : M S Unit := do
  let ref ← rwlockData h op
  if (← (rt h).rwlock ref).isWriteLocked then SyncRuntime.enqueueReader (rt h) ref 0 dest
  else SyncRuntime.readerLock (rt h) ref; zero h dest

def rwlockTryread (h : Hooks S R T) (op : OpTy Provenance) : M S Int32 := do
  let ref ← rwlockData h op
  if (← (rt h).rwlock ref).isWriteLocked then return ← h.constant .ebusy
  SyncRuntime.readerLock (rt h) ref
  return 0

def rwlockWrite (h : Hooks S R T) (op : OpTy Provenance) (dest : MPlaceTy Provenance) : M S Unit := do
  let ref ← rwlockData h op
  if (← (rt h).rwlock ref).isLocked then SyncRuntime.enqueueWriter (rt h) ref 0 dest
  else SyncRuntime.writerLock (rt h) ref; zero h dest

def rwlockTrywrite (h : Hooks S R T) (op : OpTy Provenance) : M S Int32 := do
  let ref ← rwlockData h op
  if (← (rt h).rwlock ref).isLocked then return ← h.constant .ebusy
  SyncRuntime.writerLock (rt h) ref
  return 0

def rwlockUnlock (h : Hooks S R T) (op : OpTy Provenance) : M S Unit := do
  let ref ← rwlockData h op
  if ← SyncRuntime.readerUnlock (rt h) ref then return
  if ← SyncRuntime.writerUnlock (rt h) ref then return
  throw (.undefinedBehavior "unlocked rwlock not owned by active thread")

def rwlockDestroy (h : Hooks S R T) (op : OpTy Provenance) : M S Unit := do
  let ref ← rwlockData h op
  if (← (rt h).rwlock ref).isLocked then throw (.undefinedBehavior "destroyed a locked rwlock")
  h.objectUninit op .rwlock

def condattrInit (h : Hooks S R T) (attr : OpTy Provenance) : M S Unit := do
  if h.objects.os != "macos" then attrWrite h attr .condvar (← h.constant .clockRealtime)
def condattrSetclock (h : Hooks S R T) (attr : OpTy Provenance) (clock : Int32) : M S Int32 := do
  if (← h.parseClock clock).isNone then return ← h.constant .einval
  attrWrite h attr .condvar clock
  return 0
def condattrGetclock (h : Hooks S R T) (attr dest : OpTy Provenance) : M S Unit := do
  h.writeClockId dest (← attrRead h attr .condvar)
def condattrDestroy (h : Hooks S R T) (attr : OpTy Provenance) : M S Unit := do
  if h.objects.os != "macos" then
    let _ ← attrRead h attr .condvar
  h.attributeUninit attr .condvar

def condInit (h : Hooks S R T) (op attr : OpTy Provenance) : M S Unit := do
  let pointer ← h.readPointer attr
  let clock ← if (← h.isNull pointer) || h.objects.os == "macos" then h.constant .clockRealtime else attrRead h attr .condvar
  let some clock ← h.parseClock clock | throw (.undefinedBehavior "pthread_cond_init invalid attributes unsupported clock")
  let object ← h.objects.deref op .condvar
  let ref ← h.objects.newCondvar
  PthreadObjects.createAt h.objects object (.condvar ref clock)

def condSignal (h : Hooks S R T) (op : OpTy Provenance) : M S Unit := do
  let (ref,_) ← condvarData h op
  let _ ← SyncRuntime.condvarSignal (rt h) ref

def broadcastRef (budget : Nat) (h : Hooks S R T) (ref : R) : M S Unit := do
  match budget with
  | 0 => throw (.resourceExhaustion "pthread condvar broadcast budget exhausted")
  | budget + 1 => if ← SyncRuntime.condvarSignal (rt h) ref then broadcastRef budget h ref

def condBroadcast (budget : Nat) (h : Hooks S R T) (op : OpTy Provenance) : M S Unit := do
  let (ref,_) ← condvarData h op
  broadcastRef budget h ref

def condWait (h : Hooks S R T) (op mutex : OpTy Provenance) (dest : MPlaceTy Provenance) : M S Unit := do
  let (ref,_) ← condvarData h op
  let (mutex,_) ← mutexData h mutex
  SyncRuntime.condvarWait (rt h) ref mutex none 0 0 dest

def condTimedwait (h : Hooks S R T) (op mutex timeout : OpTy Provenance)
    (dest : MPlaceTy Provenance) (macosRelative : Bool) : M S Unit := do
  let (ref,clock) ← condvarData h op
  let (mutex,_) ← mutexData h mutex
  let some duration ← h.readTimespec timeout
    | (rt h).writeScalar (← h.constant .einval) dest; return
  let clock := if macosRelative then Clock.monotonic else clock
  if !macosRelative && clock == .realTime then h.noIsolation "pthread_cond_timedwait with CLOCK_REALTIME"
  let deadline ← h.timeout clock macosRelative duration
  let error ← h.constant .etimedout
  SyncRuntime.condvarWait (rt h) ref mutex (some deadline) 0 error dest

def condDestroy (h : Hooks S R T) (op : OpTy Provenance) : M S Unit := do
  let (ref,_) ← condvarData h op
  if !(← (rt h).condvar ref).queueIsEmpty then throw (.undefinedBehavior "destroying awaited conditional variable")
  h.objectUninit op .condvar

def semInit (h : Hooks S R T) (op : OpTy Provenance) (_pshared : Int32)
    (value : UInt32) (dest : MPlaceTy Provenance) : M S Unit := do
  let object ← h.objects.deref op .semaphore
  let ref ← h.objects.newSemaphore (UInt64.ofNat value.toNat)
  PthreadObjects.createAt h.objects object (.semaphore ref)
  zero h dest

def semWait (budget : Nat) (h : Hooks S R T) (op : OpTy Provenance) (dest : MPlaceTy Provenance) : M S Unit := do
  let ref ← semData h op
  SyncRuntime.semaphoreDecrement budget (rt h) ref none (fun kind => do
    if kind != .Ready then throw (.invalidProgram "non-timed sem_wait callback timed out")
    zero h dest) (some (.pthreadSemaphore false dest))

def semTimedwait (budget : Nat) (h : Hooks S R T) (op timeout : OpTy Provenance)
    (dest : MPlaceTy Provenance) : M S Unit := do
  h.noIsolation "pthread_sem_timedwait"
  let some duration ← h.readTimespec timeout
    | h.setErrnoAndReturnNeg1 .einval dest; return
  let deadline ← h.timeout .realTime false duration
  let ref ← semData h op
  SyncRuntime.semaphoreDecrement budget (rt h) ref (some deadline) (fun kind =>
    match kind with
    | .Ready => zero h dest
    | .TimedOut => h.setErrnoAndReturnNeg1 .etimedout dest) (some (.pthreadSemaphore true dest))

def semPost (h : Hooks S R T) (op : OpTy Provenance) (dest : MPlaceTy Provenance) : M S Unit := do
  let ref ← semData h op
  let _ ← SyncRuntime.semaphoreIncrement (rt h) ref
  zero h dest

def semDestroy (h : Hooks S R T) (op : OpTy Provenance) (dest : MPlaceTy Provenance) : M S Unit := do
  let ref ← semData h op
  if !(← (rt h).semaphore ref).queueIsEmpty then throw (.undefinedBehavior "destroying awaited semaphore")
  h.objectUninit op .semaphore
  zero h dest
end Miri.Interpreter.PthreadSync
