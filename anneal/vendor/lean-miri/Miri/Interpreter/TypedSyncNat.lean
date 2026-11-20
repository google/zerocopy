import Miri.Interpreter.TypedSyncMachine

/-! Existing IO hooks use Nat for source host synchronization references. This
lawful representation view uses the same arena indices, not a second object or
callback store. Dynamic source object kinds remain checked by that arena. -/
namespace Miri.Interpreter.TypedSyncNat
open Miri.Concurrency
private def user : SyncRuntime.UserCapture Nat TypedSyncRuntime.Dest → TypedSyncRuntime.User
  | .pthreadSemaphore t d => .pthreadSemaphore t d
  | .futexErrno d => .futexErrno d
  | .windowsAddress d => .windowsAddress d
  | .windowsInitOnce r p d => .windowsInitOnce ⟨r⟩ p d
  | .macAddress r d => .macAddress ⟨r⟩ d
  | .macSemaphore d => .macSemaphore d
  | .sleep => .sleep
private def capture : SyncRuntime.Capture Nat Int32 TypedSyncRuntime.Dest → TypedSyncRuntime.Capture
  | .mutex r v => .mutex ⟨r⟩ v
  | .reader r v d => .reader ⟨r⟩ v d
  | .writer r v d => .writer ⟨r⟩ v d
  | .condvar r m s t d => .condvar ⟨r⟩ ⟨m⟩ s t d
  | .futex r u => .futex ⟨r⟩ (user u)
  | .semaphore r d u => .semaphore ⟨r⟩ d (user u)
  | .user u => .user (user u)

def runtime (v : TypedSyncMachine.Views U) (e : TypedSyncMachine.Effects (TypedSyncMachine.State K U)) :
    SyncRuntime.Hooks (TypedSyncMachine.State K U) Nat Int32 TypedSyncRuntime.Dest :=
  let h := TypedSyncMachine.runtime v e
  let typed := TypedSyncMachine.typed v e
  {handler := h.handler,usizeBits := h.usizeBits,communicate := h.communicate
   global := h.global,putGlobal := h.putGlobal,threads := h.threads,putThreads := h.putThreads
   callbackBackend := .typed (fun c => TypedSyncMachine.register v (capture c))
    (TypedSyncRuntime.invoke typed) (fun token => do let _ ← TypedSyncMachine.take v token; pure ()) (TypedSyncMachine.owns v)
   mutex := fun r => h.mutex ⟨r⟩,putMutex := fun r s => h.putMutex ⟨r⟩ s
   rwlock := fun r => h.rwlock ⟨r⟩,putRwlock := fun r s => h.putRwlock ⟨r⟩ s
   condvar := fun r => h.condvar ⟨r⟩,putCondvar := fun r s => h.putCondvar ⟨r⟩ s
   futex := fun r => h.futex ⟨r⟩,putFutex := fun r s => h.putFutex ⟨r⟩ s
   semaphore := fun r => h.semaphore ⟨r⟩,putSemaphore := fun r s => h.putSemaphore ⟨r⟩ s
   writeScalar := h.writeScalar,error := h.error}
/-- Canonical Nat representation with the terminal source dispatcher installed
before any wake closure captures it. Registration/cancellation stay in the one
typed sync arena; no legacy branch is inspected or inherited. -/
def routed (v : TypedSyncMachine.Views U) (e : TypedSyncMachine.Effects (TypedSyncMachine.State K U))
    (run : Nat → UnblockKind → TypedSyncMachine.M K U Unit) :=
  let backend : SyncRuntime.CallbackBackend (TypedSyncMachine.State K U) Nat Int32 TypedSyncRuntime.Dest :=
    .typed (fun c => TypedSyncMachine.register v (capture c)) run
      (fun token => do let _ ← TypedSyncMachine.take v token; pure ())
      (TypedSyncMachine.owns v)
  {runtime v e with callbackBackend := backend}

def outward (v : TypedSyncMachine.Views U) (e : TypedSyncMachine.Effects (TypedSyncMachine.State K U)) :
    SyncRuntime.Hooks (MachineHooks.State K (ExecutionStateTransport.Outer U)) Nat Int32 TypedSyncRuntime.Dest :=
  let h := runtime v e
  let typed := TypedSyncMachine.typed v e
  {handler := h.handler,usizeBits := h.usizeBits,communicate := h.communicate
   global := ExecutionStateTransport.action h.global
   putGlobal := fun g => ExecutionStateTransport.action (h.putGlobal g)
   threads := ExecutionStateTransport.action h.threads
   putThreads := fun g => ExecutionStateTransport.action (h.putThreads g)
   callbackBackend := .typed (fun c => ExecutionStateTransport.action (TypedSyncMachine.register v (capture c)))
    (fun t k => ExecutionStateTransport.action (TypedSyncRuntime.invoke typed t k))
    (fun t => ExecutionStateTransport.action (do let _ ← TypedSyncMachine.take v t; pure ()))
    (fun t => ExecutionStateTransport.action (TypedSyncMachine.owns v t))
   mutex := fun r => ExecutionStateTransport.action (h.mutex r)
   putMutex := fun r s => ExecutionStateTransport.action (h.putMutex r s)
   rwlock := fun r => ExecutionStateTransport.action (h.rwlock r)
   putRwlock := fun r s => ExecutionStateTransport.action (h.putRwlock r s)
   condvar := fun r => ExecutionStateTransport.action (h.condvar r)
   putCondvar := fun r s => ExecutionStateTransport.action (h.putCondvar r s)
   futex := fun r => ExecutionStateTransport.action (h.futex r)
   putFutex := fun r s => ExecutionStateTransport.action (h.putFutex r s)
   semaphore := fun r => ExecutionStateTransport.action (h.semaphore r)
   putSemaphore := fun r s => ExecutionStateTransport.action (h.putSemaphore r s)
   writeScalar := fun a b => ExecutionStateTransport.action (h.writeScalar a b),error := h.error}
end Miri.Interpreter.TypedSyncNat
