import Miri.Interpreter.TypedSyncMetadata
import Miri.Interpreter.LinuxFutexMachine

/-! Typed dyn SyncObj payloads inhabit the canonical allocation-local extras,
not an independent address registry. Resolution/materialization is shared with
the physical Linux futex binding. Metadata contains source host identities only. -/
namespace Miri.Interpreter.TypedSyncObjectMachine
open Miri.ABI Miri.Memory Miri.Concurrency
structure Payload (P : Type) where
  inject : TypedSyncMetadata.Payload → P
  project : P → Option TypedSyncMetadata.Payload
  projectInject : ∀ value, project (inject value) = some value
private def machineAction (action : PlaceMachine.MachineM K (LinuxFutexMachine.User U) A) :
    LinuxFutexMachine.M K U A := fun s =>
  match action s.machine with
  | .ok value machine => .ok value {s with machine}
  | .error error machine => .error error {s with machine}

/-- Source access checks run directly in the physical allocation hook state,
with no fabricated frame or duplicated callback roots. Unrelated source payloads
remain owned by the other actual metadata family. -/
def extras (v : TypedSyncMachine.Views U) (embedding : Payload P)
    (base : MemoryExtras.Hooks K (LinuxFutexMachine.User U) P) :
    MemoryExtras.Hooks K (LinuxFutexMachine.User U) P :=
  {base with onAccess := fun payload kind => do
    match embedding.project payload with
    | none => base.onAccess payload kind
    | some payload =>
      let machine ← get
      let data := v.storage machine.user.payload.payload.user
      TypedSyncMetadata.guardAccess (fun ref =>
        match data.objects[ref.index]? with
        | some object => pure object
        | none => throw (.invalidProgram "missing synchronization metadata reference")) payload kind}

def bindMemory (v : TypedSyncMachine.Views U) (embedding : Payload P)
    (h : LinuxFutexMachine.Hooks K U C P O B H Y Z T E) :
    LinuxFutexMachine.Hooks K U C P O B H Y Z T E :=
  let extras := extras v embedding h.extras
  {h with extras, access := MemoryExtras.bindAccess extras h.access}

def bindObjectMemory (v : TypedSyncMachine.Views U) (embedding : Payload P)
    (h : LinuxFutexMachine.ObjectHooks K U C P O B) :
    LinuxFutexMachine.ObjectHooks K U C P O B :=
  let extras := extras v embedding h.extras
  {h with extras, access := MemoryExtras.bindAccess extras h.access}

def metadataFromObjectHooks [DecidableEq K]
    (h : LinuxFutexMachine.ObjectHooks K U C P O B)
    (embedding : Payload P)
    (typed : TypedSyncRuntime.Hooks (LinuxFutexMachine.State K U)) :
    SyncObject.MetadataHooks (LinuxFutexMachine.State K U) TypedSyncMetadata.Payload :=
  let physical := LinuxFutexMachine.metadataFromObjectHooks h
  {tryResolve := physical.tryResolve, resolve := physical.resolve, info := physical.info
   lookup := fun address => do
    let object ← machineAction (MemoryExtras.lookupSync h.extras address)
    pure (object.bind fun object => (embedding.project object.payload).map fun payload =>
      {payload,deleteOnWrite := object.deleteOnWrite,onAccess := TypedSyncMetadata.onAccess typed payload})
   insert := fun address object =>
    machineAction (MemoryExtras.insertSync h.extras address
      ⟨embedding.inject object.payload,object.deleteOnWrite,#[]⟩)}

def metadata [DecidableEq K]
    (h : LinuxFutexMachine.Hooks K U C P O B H Y Z T E)
    (embedding : Payload P)
    (typed : TypedSyncRuntime.Hooks (LinuxFutexMachine.State K U)) :
    SyncObject.MetadataHooks (LinuxFutexMachine.State K U) TypedSyncMetadata.Payload :=
  metadataFromObjectHooks (LinuxFutexMachine.objectHooks h) embedding typed

/-- Exact dyn downcast view. A mismatch is absence and the canonical source
getOrInitMetadata then replaces that allocation-local entry. -/
structure Downcast (A : Type) where
  inject : A → TypedSyncMetadata.Payload
  project : TypedSyncMetadata.Payload → Option A
  projectInject : ∀ value, project (inject value) = some value

def narrow (base : SyncObject.MetadataHooks S TypedSyncMetadata.Payload)
    (cast : Downcast A) :
    SyncObject.MetadataHooks S A :=
  {tryResolve := base.tryResolve, resolve := base.resolve, info := base.info
   lookup := fun address => do
    let some object ← base.lookup address | return none
    pure ((cast.project object.payload).map fun payload =>
      {payload,deleteOnWrite := object.deleteOnWrite,onAccess := object.onAccess})
   insert := fun address object => base.insert address
    {payload := cast.inject object.payload,deleteOnWrite := object.deleteOnWrite,onAccess := object.onAccess}}
def pthread : Downcast (PthreadObjects.Payload TypedSyncRuntime.Ref) where
  inject := .pthread
  project := fun value => match value with | .pthread value => some value | _ => none
  projectInject := fun _ => rfl
def windows : Downcast (WindowsSync.Payload TypedSyncRuntime.Ref) where
  inject := .windows
  project := fun value => match value with | .windows value => some value | _ => none
  projectInject := fun _ => rfl
def macLock : Downcast (MacOsSync.Unfair TypedSyncRuntime.Ref) where
  inject := .macLock
  project := fun value => match value with | .macLock value => some value | _ => none
  projectInject := fun _ => rfl
def macSemaphore : Downcast (MacOsSync.Semaphore TypedSyncRuntime.Ref) where
  inject := .macSemaphore
  project := fun value => match value with | .macSemaphore value => some value | _ => none
  projectInject := fun _ => rfl
def macFutex : Downcast TypedSyncRuntime.Ref where
  inject := .macFutex
  project := fun value => match value with | .macFutex value => some value | _ => none
  projectInject := fun _ => rfl
def freeBsdFutex : Downcast TypedSyncRuntime.Ref where
  inject := .freeBsdFutex
  project := fun value => match value with | .freeBsdFutex value => some value | _ => none
  projectInject := fun _ => rfl

/-- Byte access operations are separated from typed metadata ownership. They
must be supplied by the actual allocation/atomic machine, never by an arena. -/
structure Bytes (S : Type) where
  checkAccess : Pointer (Option Provenance) → Size → EStateM StepError S Unit
  offset : MPlaceTy Provenance → Size → EStateM StepError S (MPlaceTy Provenance)
  compareExchangeByteRelaxed : MPlaceTy Provenance → UInt8 → UInt8 → EStateM StepError S (UInt8 × Bool)
  writeZeros : Pointer (Option Provenance) → Size → EStateM StepError S Unit
  writeByte : MPlaceTy Provenance → UInt8 → EStateM StepError S Unit

def full (base : SyncObject.MetadataHooks S TypedSyncMetadata.Payload)
    (bytes : Bytes S) (cast : Downcast A) : SyncObject.Hooks S A :=
  let data := narrow base cast
  {tryResolve := data.tryResolve, resolve := data.resolve, info := data.info
   lookup := data.lookup, insert := data.insert
   checkAccess := bytes.checkAccess, offset := bytes.offset
   compareExchangeByteRelaxed := bytes.compareExchangeByteRelaxed
   writeZeros := bytes.writeZeros, writeByte := bytes.writeByte}
end Miri.Interpreter.TypedSyncObjectMachine
