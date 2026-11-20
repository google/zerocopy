import Miri.Interpreter.PlaceTypes
import Miri.Interpreter.Step
import Miri.Memory.Pointer

/-! Metadata wrappers from pinned concurrency/sync.rs:18–62,302–446.
Registry payloads are typed by the caller: mismatched dynamic types must return
none, causing replacement just as dyn SyncObj::downcast_ref does in source. -/
namespace Miri.Concurrency.SyncObject
open Miri.ABI Miri.Memory Miri.Interpreter
abbrev M := EStateM StepError
inductive AccessKind where | read | write | deallocation deriving DecidableEq, Repr
structure Object (S Payload : Type) where
  payload : Payload
  onAccess : AccessKind → M S Unit
  deleteOnWrite : Bool
structure Address where
  allocation : AllocId
  offset : Size
structure Info where
  liveData : Bool
  mutable : Bool
  size : Size
structure Hooks (S T : Type) where
  tryResolve : Pointer (Option Provenance) → M S (Option Address)
  resolve : Pointer (Option Provenance) → M S Address
  info : AllocId → M S Info
  lookup : Address → M S (Option (Object S T))
  insert : Address → Object S T → M S Unit
  checkAccess : Pointer (Option Provenance) → Size → M S Unit
  offset : MPlaceTy Provenance → Size → M S (MPlaceTy Provenance)
  compareExchangeByteRelaxed : MPlaceTy Provenance → UInt8 → UInt8 → M S (UInt8 × Bool)
  writeZeros : Pointer (Option Provenance) → Size → M S Unit
  writeByte : MPlaceTy Provenance → UInt8 → M S Unit

structure MetadataHooks (S T : Type) where
  tryResolve : Pointer (Option Provenance) → M S (Option Address)
  resolve : Pointer (Option Provenance) → M S Address
  info : AllocId → M S Info
  lookup : Address → M S (Option (Object S T))
  insert : Address → Object S T → M S Unit

def getOrInitMetadata (h : MetadataHooks S T) (pointer : Pointer (Option Provenance)) (new : M S (Object S T)) :
    M S (Option (Object S T)) := do
  let some address ← h.tryResolve pointer | return none
  let info ← h.info address.allocation
  if !info.liveData || !info.mutable || address.offset.bytes >= info.size.bytes then return none
  let address ← h.resolve pointer
  if (← h.lookup address).isNone then h.insert address (← new)
  let some value ← h.lookup address | throw (.invalidProgram "inserted synchronization object missing")
  return some value

def getOrInit (h : Hooks S T) (pointer : Pointer (Option Provenance)) (new : M S (Object S T)) :
    M S (Option (Object S T)) :=
  getOrInitMetadata ⟨h.tryResolve,h.resolve,h.info,h.lookup,h.insert⟩ pointer new

def getImmovableWithStaticInit (h : Hooks S T) (obj : MPlaceTy Provenance)
    (initOffset : Size) (uninitValue initValue : UInt8) (new : M S (Object S T)) :
    M S (Object S T) := do
  if initValue == uninitValue then throw (.invalidProgram "synchronization init and uninit flags equal")
  h.checkAccess obj.mplace.ptr obj.layout.layout.size
  if initOffset.bytes >= obj.layout.layout.size.bytes then
    throw (.invalidProgram "synchronization init flag outside object")
  let field ← h.offset obj initOffset
  let address ← h.resolve field.mplace.ptr
  if (← h.lookup address).isSome then
    let some value ← h.lookup address | throw (.invalidProgram "synchronization object disappeared")
    return value
  let metadata ← new
  let (old,success) ← h.compareExchangeByteRelaxed field uninitValue initValue
  if !success && old != initValue then
    throw (.invalidProgram "new metadata must ensure synchronization CAS succeeds or already initialized")
  if !metadata.deleteOnWrite then throw (.invalidProgram "immovable synchronization metadata must delete on write")
  h.insert address metadata
  let some value ← h.lookup address | throw (.invalidProgram "inserted synchronization object missing")
  return value

def initImmovable (h : Hooks S T) (obj : MPlaceTy Provenance) (initOffset : Size)
    (initValue : UInt8) (metadata : Object S T) : M S (Option (Object S T)) := do
  h.checkAccess obj.mplace.ptr obj.layout.layout.size
  if initOffset.bytes >= obj.layout.layout.size.bytes then
    throw (.invalidProgram "synchronization init flag outside object")
  let field ← h.offset obj initOffset
  h.writeZeros obj.mplace.ptr obj.layout.layout.size
  h.writeByte field initValue
  let address ← h.resolve field.mplace.ptr
  if !metadata.deleteOnWrite then throw (.invalidProgram "immovable synchronization metadata must delete on write")
  h.insert address metadata
  let some value ← h.lookup address | throw (.invalidProgram "inserted synchronization object missing")
  return some value
structure AccessHooks (S T : Type) where
  /-- Complete live registry; access traverses ascending byte offsets, as BTreeMap. -/
  entries : AllocId → M S (Array (Size × Object S T))
  remove : AllocId → Size → M S Unit

def onMemoryAccess (h : AccessHooks S T) (allocation : AllocId)
    (start size : Size) (kind : AccessKind) : M S Unit := do
  let entries := (← h.entries allocation).qsort (fun left right => left.1.bytes < right.1.bytes)
  let mut deletions := #[]
  for (offset,obj) in entries do
    if kind == .deallocation ||
        (start.bytes.toNat <= offset.bytes.toNat && offset.bytes.toNat < start.bytes.toNat + size.bytes.toNat) then
      obj.onAccess kind
      if kind == .write && obj.deleteOnWrite then deletions := deletions.push offset
  -- Source collects deletions first: if any on_access fails, no registry
  -- entries are removed, including earlier candidates in the range.
  for offset in deletions do h.remove allocation offset
end Miri.Concurrency.SyncObject
