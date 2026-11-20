import Miri.Interpreter.TypedSyncMachine
import Miri.Interpreter.PthreadObjects
import Miri.Interpreter.WindowsSync
import Miri.Interpreter.MacOsSync

/-! Source dyn SyncObj payloads are distinct even when they refer to the same
kind of host synchronization state. This sum preserves source downcast identity
without closure-valued persistent metadata. -/
namespace Miri.Interpreter.TypedSyncMetadata
open Miri.Concurrency
abbrev Ref := TypedSyncRuntime.Ref
inductive Payload where
  | pthread (value : PthreadObjects.Payload Ref)
  | windows (value : WindowsSync.Payload Ref)
  | macLock (value : MacOsSync.Unfair Ref)
  | macSemaphore (value : MacOsSync.Semaphore Ref)
  | macFutex (ref : Ref)
  | freeBsdFutex (ref : Ref)
private def invalid [Monad m] [MonadExceptOf StepError m] (message : String) : m A := throw (.invalidProgram message)
private def queued [Monad m] [MonadExceptOf StepError m]
    (getObject : Ref → m TypedSyncRuntime.Object) (ref : Ref) : m Bool := do
  match ← getObject ref with
  | .mutex value => pure (!value.queueIsEmpty)
  | .rwlock value => pure (!value.queueIsEmpty)
  | .condvar value => pure (!value.queueIsEmpty)
  | .semaphore value => pure (!value.queueIsEmpty)
  | _ => invalid "pthread metadata refers to a different source synchronization object"
/-- Source access guards reconstructed from typed persistent captures. No
allocation roots are added: sync.rs VisitProvenance for these Rc states is empty. -/
def guardAccess [Monad m] [MonadExceptOf StepError m]
    (getObject : Ref → m TypedSyncRuntime.Object) (payload : Payload) (_ : SyncObject.AccessKind) : m Unit := do
  match payload with
  | .pthread payload =>
    let ref := match payload with
      | .mutex ref _ | .rwlock ref | .condvar ref _ | .semaphore ref => ref
    if ← queued getObject ref then
      throw (.undefinedBehavior "access of pthread synchronization storage forbidden while queue non-empty")
  | .windows (.initOnce ref) =>
    let .initOnce state ← getObject ref | invalid "INIT_ONCE metadata references different source object"
    unless state.waiters.isEmpty do
      throw (.undefinedBehavior "access to INIT_ONCE while threads are waiting")
  | .macLock (.active ref) =>
    let .mutex state ← getObject ref | invalid "os_unfair_lock metadata references different source object"
    unless state.queue.isEmpty do
      throw (.undefinedBehavior "access of os_unfair_lock while its queue is nonempty")
  | .macSemaphore value =>
    let .semaphore state ← getObject value.ref | invalid "dispatch semaphore metadata references different source object"
    unless state.waiters.isEmpty do
      throw (.undefinedBehavior "access of os_unfair_lock while its queue is nonempty")
  | .windows (.futex _) | .macLock .permanentlyLocked | .macFutex _ | .freeBsdFutex _ => pure ()
def onAccess (h : TypedSyncRuntime.Hooks S) (payload : Payload) (kind : SyncObject.AccessKind) :
    EStateM StepError S Unit := guardAccess h.get payload kind
def deleteOnWrite : Payload → Bool
  | .pthread _ | .windows (.initOnce _) | .macLock _ | .macSemaphore _ => true
  | _ => false
def object (h : TypedSyncRuntime.Hooks S) (payload : Payload) : SyncObject.Object S Payload :=
  ⟨payload,onAccess h payload,deleteOnWrite payload⟩
end Miri.Interpreter.TypedSyncMetadata
