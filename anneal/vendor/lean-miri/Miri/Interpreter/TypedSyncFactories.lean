import Miri.Interpreter.TypedSyncObjectMachine

/-! Source constructors for typed synchronization state, static-initializer
sanity flags and MacOsFutex settings. No function registry is requested. -/
namespace Miri.Interpreter.TypedSyncFactories
open Miri.ABI Miri.Memory Miri.Concurrency
abbrev M := TypedSyncMachine.M
abbrev Views := TypedSyncMachine.Views
abbrev State := TypedSyncMachine.State
private def payload : M K U U := return (← get).machine.user.payload.payload.user
private def modifyPayload (f : U → U) : M K U Unit :=
  modify fun s => {s with machine := {s.machine with user := {s.machine.user with payload :=
    {s.machine.user.payload with payload := {s.machine.user.payload.payload with user := f s.machine.user.payload.payload.user}}}}}
private def storage (v : Views U) : M K U TypedSyncRuntime.Storage := return v.storage (← payload)
private def setStorage (v : Views U) (data : TypedSyncRuntime.Storage) : M K U Unit :=
  modifyPayload fun u => v.putStorage u data

def sanity (v : Views U) (kind : PthreadObjects.Kind) : M K U Bool := do
  let data ← storage v
  pure (match kind with
    | .mutex => data.pthreadMutexSanity | .rwlock => data.pthreadRwlockSanity
    | .condvar => data.pthreadCondvarSanity | .semaphore => data.pthreadSemaphoreSanity)
def putSanity (v : Views U) (kind : PthreadObjects.Kind) (value : Bool) : M K U Unit := do
  let data ← storage v
  setStorage v (match kind with
    | .mutex => {data with pthreadMutexSanity := value}
    | .rwlock => {data with pthreadRwlockSanity := value}
    | .condvar => {data with pthreadCondvarSanity := value}
    | .semaphore => {data with pthreadSemaphoreSanity := value})

structure PthreadMemory (S : Type) where
  os : String
  deref : OpTy Provenance → PthreadObjects.Kind → EStateM StepError S TypedSyncRuntime.Dest
  initializer : String → EStateM StepError S TypedSyncRuntime.Dest
  readBytes : TypedSyncRuntime.Dest → Size → EStateM StepError S ByteArray
  readInitByte : TypedSyncRuntime.Dest → Size → EStateM StepError S UInt8

def pthread (v : Views U) (e : TypedSyncMachine.Effects (State K U))
    (metadata : SyncObject.MetadataHooks (State K U) TypedSyncMetadata.Payload)
    (bytes : TypedSyncObjectMachine.Bytes (State K U)) (memory : PthreadMemory (State K U)) :
    PthreadObjects.Hooks (State K U) TypedSyncRuntime.Ref where
  os := memory.os
  sync := TypedSyncObjectMachine.full metadata bytes TypedSyncObjectMachine.pthread
  runtime := TypedSyncMachine.runtime v e
  deref := memory.deref
  initializer := memory.initializer
  readBytes := memory.readBytes
  readInitByte := memory.readInitByte
  sanity := sanity v
  putSanity := putSanity v
  newMutex := TypedSyncMachine.newObject v (.mutex {})
  newRwlock := TypedSyncMachine.newObject v (.rwlock {})
  newCondvar := TypedSyncMachine.newObject v (.condvar {})
  newSemaphore := fun value => TypedSyncMachine.newObject v (.semaphore {value})

def newMacFutex (v : Views U) (size : UInt64) (shared : Bool) : M K U TypedSyncRuntime.Ref := do
  let ref ← TypedSyncMachine.newObject v (.futex {})
  let data ← storage v
  setStorage v {data with macFutexSettings := data.macFutexSettings.push (ref,size,shared)}
  pure ref
def macSettings (v : Views U) (ref : TypedSyncRuntime.Ref) : M K U (UInt64 × Bool) := do
  let values := (← storage v).macFutexSettings.filter (·.1 == ref)
  unless values.size == 1 do throw (.invalidProgram "missing or ambiguous MacOsFutex settings")
  let some (_,value) := values[0]? | throw (.invalidProgram "MacOsFutex settings lookup invariant")
  pure value
def putMacSettings (v : Views U) (ref : TypedSyncRuntime.Ref) (size : UInt64) (shared : Bool) : M K U Unit := do
  let _ ← macSettings v ref
  let data ← storage v
  setStorage v {data with macFutexSettings := data.macFutexSettings.map fun value =>
    if value.1 == ref then (ref,size,shared) else value}
end Miri.Interpreter.TypedSyncFactories
