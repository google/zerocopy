import Miri.Concurrency.SyncRuntime
import Miri.Concurrency.SyncObject

/-! Object lifecycle from pinned shims/unix/sync.rs:1–529. Compiler initializer
bytes/layouts and actual memory operations are mandatory queries. -/
namespace Miri.Interpreter.PthreadObjects
open Miri.ABI Miri.Memory Miri.Concurrency
abbrev M := EStateM StepError
inductive Kind where | mutex | rwlock | condvar | semaphore deriving DecidableEq, Repr
inductive MutexKind where | Normal | Default | Recursive | ErrorCheck deriving DecidableEq, Repr
inductive Clock where | realTime | monotonic deriving DecidableEq, Repr
inductive Payload (R : Type) where
  | mutex (ref : R) (kind : MutexKind)
  | rwlock (ref : R)
  | condvar (ref : R) (clock : Clock)
  | semaphore (ref : R)
def Payload.kind : Payload R → Kind
  | .mutex .. => .mutex | .rwlock .. => .rwlock | .condvar .. => .condvar | .semaphore .. => .semaphore
structure Hooks (S R : Type) where
  os : String
  sync : SyncObject.Hooks S (Payload R)
  runtime : SyncRuntime.Hooks S R Int32 (MPlaceTy Provenance)
  deref : OpTy Provenance → Kind → M S (MPlaceTy Provenance)
  initializer : String → M S (MPlaceTy Provenance)
  readBytes : MPlaceTy Provenance → Size → M S ByteArray
  readInitByte : MPlaceTy Provenance → Size → M S UInt8
  sanity : Kind → M S Bool
  putSanity : Kind → Bool → M S Unit
  newMutex : M S R
  newRwlock : M S R
  newCondvar : M S R
  newSemaphore : UInt64 → M S R

def initOffset (h : Hooks S R) (kind : Kind) : M S Size := do
  let offset ←
    if #["linux","illumos","solaris","freebsd","android"].contains h.os then pure 0
    else if h.os == "macos" && kind != .semaphore then pure 4
    else if h.os == "netbsd" && kind == .mutex then pure 4
    else throw (.unsupported "pthread synchronization type unsupported on this target")
  if kind == .semaphore then return Size.ofBytes offset
  if !(← h.sanity kind) then
    h.putSanity kind true
    let names := match kind with
      | .mutex => if h.os == "linux" then
          #["PTHREAD_MUTEX_INITIALIZER","PTHREAD_RECURSIVE_MUTEX_INITIALIZER_NP",
            "PTHREAD_ERRORCHECK_MUTEX_INITIALIZER_NP","PTHREAD_ADAPTIVE_MUTEX_INITIALIZER_NP"]
        else #["PTHREAD_MUTEX_INITIALIZER"]
      | .rwlock => #["PTHREAD_RWLOCK_INITIALIZER"]
      | .condvar => #["PTHREAD_COND_INITIALIZER"]
      | .semaphore => #[]
    for name in names do
      if (← h.readInitByte (← h.initializer name) (Size.ofBytes offset)) != 0 then
        throw (.invalidProgram "libc static initializer incompatible with pthread initialization marker")
  return Size.ofBytes offset
private def compareInitializer (h : Hooks S R) (object : MPlaceTy Provenance)
    (name : String) : M S Bool := do
  let initializer ← h.initializer name
  if initializer.layout.layout.size != object.layout.layout.size then
    throw (.invalidProgram "pthread static initializer layout size mismatch")
  let size := if h.os == "android" then Size.ofBytes 4 else object.layout.layout.size
  let left ← h.readBytes object size
  let right ← h.readBytes initializer size
  return left == right

def mutexKindFromInitializer (h : Hooks S R) (object : MPlaceTy Provenance) : M S MutexKind := do
  if ← compareInitializer h object "PTHREAD_MUTEX_INITIALIZER" then return .Default
  if h.os == "linux" then
    if ← compareInitializer h object "PTHREAD_RECURSIVE_MUTEX_INITIALIZER_NP" then return .Recursive
    if ← compareInitializer h object "PTHREAD_ERRORCHECK_MUTEX_INITIALIZER_NP" then return .ErrorCheck
  throw (.undefinedBehavior "pthread_mutex_t not properly initialized at this location or overwritten")
private def metadata (h : Hooks S R) (payload : Payload R) : SyncObject.Object S (Payload R) := {
  payload := payload
  deleteOnWrite := true
  onAccess := fun _ => do
    let empty : Bool ← match payload with
      | .mutex ref _ => (h.runtime.mutex ref).map MutexState.queueIsEmpty
      | .rwlock ref => (h.runtime.rwlock ref).map RwLockState.queueIsEmpty
      | .condvar ref _ => (h.runtime.condvar ref).map CondvarState.queueIsEmpty
      | .semaphore ref => (h.runtime.semaphore ref).map SemaphoreState.queueIsEmpty
    if !empty then throw (.undefinedBehavior "access of pthread synchronization storage forbidden while queue non-empty") }
private def typed (h : Hooks S R) (kind : Kind) : SyncObject.Hooks S (Payload R) := {
  h.sync with lookup := fun address => do
    let some value ← h.sync.lookup address | return none
    return if value.payload.kind == kind then some value else none }

def get (h : Hooks S R) (kind : Kind) (operand : OpTy Provenance) : M S (Payload R) := do
  let object ← h.deref operand kind
  let offset ← initOffset h kind
  let value ← SyncObject.getImmovableWithStaticInit (typed h kind) object offset 0 1 do
    let payload : Payload R ← match kind with
      | .mutex => do
        let mutexKind ← mutexKindFromInitializer h object
        pure (Payload.mutex (← h.newMutex) mutexKind)
      | .rwlock => do
        if !(← compareInitializer h object "PTHREAD_RWLOCK_INITIALIZER") then
          throw (.undefinedBehavior "pthread_rwlock_t not properly initialized at this location or overwritten")
        pure (Payload.rwlock (← h.newRwlock))
      | .condvar => do
        if !(← compareInitializer h object "PTHREAD_COND_INITIALIZER") then
          throw (.undefinedBehavior "pthread_cond_t not properly initialized at this location or overwritten")
        pure (Payload.condvar (← h.newCondvar) .realTime)
      | .semaphore => throw (.undefinedBehavior "sem_t not initialized with sem_init")
    return metadata h payload
  return value.payload

def createAt (h : Hooks S R) (object : MPlaceTy Provenance) (payload : Payload R) : M S Unit := do
  let offset ← initOffset h payload.kind
  let _ ← SyncObject.initImmovable (typed h payload.kind) object offset 1 (metadata h payload)
def create (h : Hooks S R) (operand : OpTy Provenance) (payload : Payload R) : M S Unit := do
  createAt h (← h.deref operand payload.kind) payload
end Miri.Interpreter.PthreadObjects
