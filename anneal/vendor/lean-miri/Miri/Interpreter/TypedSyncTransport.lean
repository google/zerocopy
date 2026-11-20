import Miri.Interpreter.TypedSyncFactories

/-! Lawful existing full-state reassociation for final foreign calls. Only
interpreter actions move; source object/callback identities stay unchanged. -/
namespace Miri.Interpreter.TypedSyncTransport
open Miri.ABI Miri.Memory Miri.Concurrency
abbrev Inner K U := TypedSyncMachine.State K U
abbrev Outer K U := MachineHooks.State K (ExecutionStateTransport.Outer U)
private def action (a : EStateM StepError (Inner K U) A) : EStateM StepError (Outer K U) A :=
  ExecutionStateTransport.action a

def metadata (h : SyncObject.MetadataHooks (Inner K U) A) : SyncObject.MetadataHooks (Outer K U) A where
  tryResolve := fun p => action (h.tryResolve p)
  resolve := fun p => action (h.resolve p)
  info := fun p => action (h.info p)
  lookup := fun p => do
    let some object ← action (h.lookup p) | return none
    pure (some {payload := object.payload,deleteOnWrite := object.deleteOnWrite,onAccess := fun kind => action (object.onAccess kind)})
  insert := fun p object => action (h.insert p
    {payload := object.payload,deleteOnWrite := object.deleteOnWrite,
     onAccess := fun kind => ExecutionStateTransport.reverseAction (object.onAccess kind)})

def full (h : SyncObject.Hooks (Inner K U) A) : SyncObject.Hooks (Outer K U) A :=
  let data := metadata ⟨h.tryResolve,h.resolve,h.info,h.lookup,h.insert⟩
  {tryResolve := data.tryResolve, resolve := data.resolve,info := data.info,lookup := data.lookup,insert := data.insert
   checkAccess := fun p n => action (h.checkAccess p n)
   offset := fun p n => action (h.offset p n)
   compareExchangeByteRelaxed := fun p a b => action (h.compareExchangeByteRelaxed p a b)
   writeZeros := fun p n => action (h.writeZeros p n)
   writeByte := fun p n => action (h.writeByte p n)}

def bytes (h : TypedSyncObjectMachine.Bytes (Inner K U)) : TypedSyncObjectMachine.Bytes (Outer K U) where
  checkAccess := fun p n => action (h.checkAccess p n)
  offset := fun p n => action (h.offset p n)
  compareExchangeByteRelaxed := fun p a b => action (h.compareExchangeByteRelaxed p a b)
  writeZeros := fun p n => action (h.writeZeros p n)
  writeByte := fun p n => action (h.writeByte p n)

/-- Construct the outer production backend directly from the source typed
factory. No legacy registry is transported or fabricated. -/
def runtime (v : TypedSyncMachine.Views U) (e : TypedSyncMachine.Effects (Inner K U)) :
    SyncRuntime.Hooks (Outer K U) TypedSyncRuntime.Ref Int32 TypedSyncRuntime.Dest :=
  let h := TypedSyncMachine.runtime v e
  let typed := TypedSyncMachine.typed v e
  {handler := h.handler,usizeBits := h.usizeBits,communicate := h.communicate
   global := action h.global,putGlobal := fun g => action (h.putGlobal g)
   threads := action h.threads,putThreads := fun g => action (h.putThreads g)
   callbackBackend := .typed (fun capture => action (TypedSyncMachine.register v capture))
    (fun token kind => action (TypedSyncRuntime.invoke typed token kind))
    (fun token => action (do let _ ← TypedSyncMachine.take v token; pure ()))
    (fun token => action (TypedSyncMachine.owns v token))
   mutex := fun r => action (h.mutex r),putMutex := fun r s => action (h.putMutex r s)
   rwlock := fun r => action (h.rwlock r),putRwlock := fun r s => action (h.putRwlock r s)
   condvar := fun r => action (h.condvar r),putCondvar := fun r s => action (h.putCondvar r s)
   futex := fun r => action (h.futex r),putFutex := fun r s => action (h.putFutex r s)
   semaphore := fun r => action (h.semaphore r),putSemaphore := fun r s => action (h.putSemaphore r s)
   writeScalar := fun a b => action (h.writeScalar a b),error := h.error}

def once (v : TypedSyncMachine.Views U) (e : TypedSyncMachine.Effects (Inner K U)) :
    InitOnce.Hooks (Outer K U) TypedSyncRuntime.Ref Int32 TypedSyncRuntime.Dest :=
  let h := TypedSyncMachine.initOnce v e
  {runtime := runtime v e,get := fun r => action (h.get r),put := fun r s => action (h.put r s),new := action h.new}

def pthread (v : TypedSyncMachine.Views U) (e : TypedSyncMachine.Effects (Inner K U))
    (h : PthreadObjects.Hooks (Inner K U) TypedSyncRuntime.Ref) :
    PthreadObjects.Hooks (Outer K U) TypedSyncRuntime.Ref where
  os := h.os
  sync := full h.sync
  runtime := runtime v e
  deref := fun a b => action (h.deref a b)
  initializer := fun a => action (h.initializer a)
  readBytes := fun a b => action (h.readBytes a b)
  readInitByte := fun a b => action (h.readInitByte a b)
  sanity := fun a => action (h.sanity a)
  putSanity := fun a b => action (h.putSanity a b)
  newMutex := action h.newMutex
  newRwlock := action h.newRwlock
  newCondvar := action h.newCondvar
  newSemaphore := fun a => action (h.newSemaphore a)
end Miri.Interpreter.TypedSyncTransport
