import Miri.Memory.Allocation
import Miri.Memory.Pointer
import Miri.Memory.CtfeProvenance
import Miri.Memory.Access
import Miri.Memory.KeyedArray

/-! Core local-allocation lifecycle transitions from rustc's interpreter
`memory.rs`. Allocation IDs, Miri machine state, pointer lookup, native
allocation bytes, memory-copy access checks, and machine deallocation hooks are
explicit inputs. State changes performed before a source error are retained. -/

namespace Miri.Memory

open Miri.ABI

inductive MemoryKind (MachineKind : Type) where
  | stack
  | callerLocation
  | machine (kind : MachineKind)
  deriving DecidableEq, Repr

inductive GlobalAllocationKind where
  | function
  | vtable
  | typeId
  | static
  | memory
  deriving DecidableEq, Repr

/-- The source-level shape of a compiler global. Memory contents use CTFE
provenance until `adjustGlobalAllocation` converts them for the selected
machine. A static stores its identity and source predicates; its initializer
is evaluated only when the source `get_global_alloc` path is taken. -/
inductive GlobalAllocationPayload where
  | memory (allocation : Allocation CtfeProvenance Unit)
  | function
  | vtable
  | typeId
  | static (definition : Nat) (isStatic threadLocal foreignItem : Bool)

structure LocalAllocation (Prov Extra MachineKind : Type) where
  kind : MemoryKind MachineKind
  allocation : Allocation Prov Extra

structure DeadAllocation where
  allocId : AllocId
  size : Size
  align : Align
  deriving DecidableEq, Repr

/-- Global allocation metadata is indexed by the runtime rustc `AllocId`.
Exporter graph IDs are canonical graph indices, so imported IDs are kept in a
separate explicit map rather than treated as runtime IDs. -/
structure GlobalAllocation where
  allocId : AllocId
  kind : GlobalAllocationKind
  size : Size
  align : Align
  mutability : Mutability := .Not
  payload : Option GlobalAllocationPayload := none

inductive AllocationIdError where
  | exhausted
  | alreadyIssued (allocId : AllocId)
  deriving DecidableEq, Repr

inductive MemoryMetadataError where
  | duplicateExportId (exportId : Nat)
  | duplicateRuntimeId (allocId : AllocId)
  | globalIdAlreadyPresent (allocId : AllocId)
  | missingExportId (exportId : Nat)
  deriving DecidableEq, Repr

inductive GlobalAccessError where
  | notFound (allocId : AllocId)
  | dereferenceFunctionPointer (allocId : AllocId)
  | dereferenceVTablePointer (allocId : AllocId)
  | dereferenceTypeIdPointer (allocId : AllocId)
  | staticNotAStatic (allocId : AllocId) (definition : Nat)
  | threadLocalStatic (allocId : AllocId) (definition : Nat)
  | unsupportedExternStatic (allocId : AllocId) (definition : Nat)
  | payloadUnavailable (allocId : AllocId)
  | payloadKindMismatch (allocId : AllocId) (kind : GlobalAllocationKind)
      (payloadKind : GlobalAllocationKind)
  | hookFailure (hook : String) (message : String)
  deriving DecidableEq, Repr

inductive MemoryAccessError where
  | globalAccess (reason : GlobalAccessError)
  | allocationLookup (reason : AllocationLookupError)
  | readOnlyAllocation (allocId : AllocId)
  | missingGlobalMachineKind (allocId : AllocId)
  deriving DecidableEq, Repr

inductive LiveAllocationInfoError where
  | lookup (reason : AllocationLookupError)
  | useAfterFree (allocId : AllocId) (message : CheckInAllocMsg)
  deriving DecidableEq, Repr

structure MemoryState (Prov Extra MachineKind : Type) where
  /-- Mirrors rustc's `AllocMap::next_id`, which starts at one and increments
  monotonically for every reserved local or imported-global allocation. -/
  nextAllocId : UInt64 := 1
  idSupplyExhausted : Bool := false
  private issuedIdTable : KeyedArray UInt64 AllocId (fun (id : AllocId) => id.value) :=
    .empty (fun (id : AllocId) => id.value)
  live : Array (AllocId × LocalAllocation Prov Extra MachineKind) := #[]
  dead : Array DeadAllocation := #[]
  private globalTable : KeyedArray UInt64 GlobalAllocation
      (fun (global : GlobalAllocation) => global.allocId.value) :=
    .empty (fun (global : GlobalAllocation) => global.allocId.value)
  /-- Canonical exporter graph ID to runtime rustc-compatible AllocId. -/
  private importedGlobalTable : KeyedArray Nat (Nat × AllocId) (@Prod.fst Nat AllocId) :=
    .empty (@Prod.fst Nat AllocId)
  /-- Reverse key for source-node lookup by runtime allocation ID. -/
  private importedGlobalRuntimeTable : KeyedArray UInt64 (UInt64 × Nat) (@Prod.fst UInt64 Nat) :=
    .empty (@Prod.fst UInt64 Nat)
  /-- Locally registered machine-specific function values. The source keeps
  these in `extra_fn_ptr_map`, independently of regular allocation bytes. -/
  private extraFnPtrTable : KeyedArray UInt64 AllocId (fun (id : AllocId) => id.value) :=
    .empty (fun (id : AllocId) => id.value)
  /-- Locally registered variable-argument-list allocations. -/
  private vaListTable : KeyedArray UInt64 AllocId (fun (id : AllocId) => id.value) :=
    .empty (fun (id : AllocId) => id.value)
  /-- TCX global byte dedup keys, sharing this allocation supply. Imported
  compiler identities are seeded only from exact salt-query evidence. -/
  byteGlobalKeys : Array (Array UInt8 × Fin 32 × AllocId) := #[]
  byteGlobalKeysReady : Bool := false
  /-- Optional exact post-export TCX source-number world. Runtime IDs remain
  dense; this crosswalk retains raw rustc identities for diagnostics. -/
  sourceAllocIdWorldActive : Bool := false
  sourceAllocIdNext : UInt64 := 1
  sourceAllocIdExhausted : Bool := false
  private sourceAllocIdByRuntimeTable : KeyedArray UInt64 (AllocId × UInt64)
      (fun (pair : AllocId × UInt64) => pair.1.value) :=
    .empty (fun (pair : AllocId × UInt64) => pair.1.value)
  private runtimeBySourceAllocIdTable : KeyedArray UInt64 (UInt64 × AllocId)
      (@Prod.fst UInt64 AllocId) :=
    .empty (@Prod.fst UInt64 AllocId)
  opaqueSourceGlobalIds : Array UInt64 := #[]
  sourceByteImageFamilyComplete : Bool := false

inductive MemoryLifecycleError where
  | allocation (error : AllocError)
  | allocationIdError (error : AllocationIdError)
  | metadataError (error : MemoryMetadataError)
  | hookFailure (hook : String) (message : String)
  | allocationTooLarge (size maximum : Size)
  | allocationNotLocal (allocId : AllocId)
  | dynamicallyAllocatingGlobal
  | danglingPointer (address : UInt64)
  | nonzeroAllocationOffset (operation : String) (allocId : AllocId) (offset : Size)
  | globalAllocationDeallocation (allocId : AllocId) (kind : GlobalAllocationKind)
  | useAfterFree (allocId : AllocId)
  | immutableAllocation (allocId : AllocId)
  | memoryKindMismatch (allocId : AllocId)
  | layoutMismatch (allocId : AllocId) (actualSize requestedSize : Size)
      (actualAlign requestedAlign : Align)
  | duplicateDeadAllocation (allocId : AllocId)
  deriving DecidableEq, Repr

instance : ToString GlobalAllocationKind where
  toString
    | .function => "function"
    | .vtable => "vtable"
    | .typeId => "type-id"
    | .static => "static"
    | .memory => "memory"

instance : ToString AllocationIdError where
  toString
    | .exhausted => "rustc AllocId supply reached the reserved zero ID"
    | .alreadyIssued id => s!"rustc AllocId supply repeated runtime ID {id.value}"

instance : ToString MemoryMetadataError where
  toString
    | .duplicateExportId id => s!"export allocation ID {id} was already mapped"
    | .duplicateRuntimeId id => s!"runtime allocation ID {id.value} was already global"
    | .globalIdAlreadyPresent id =>
        s!"runtime allocation ID {id.value} is already issued or present in memory"
    | .missingExportId id => s!"export allocation ID {id} has no runtime mapping"

namespace MemoryState

def issuedIds (state : MemoryState Prov Extra MachineKind) : Array AllocId :=
  state.issuedIdTable.toArray

def globals (state : MemoryState Prov Extra MachineKind) : Array GlobalAllocation :=
  state.globalTable.toArray

def importedGlobalIds (state : MemoryState Prov Extra MachineKind) : Array (Nat × AllocId) :=
  state.importedGlobalTable.toArray

def extraFnPtrIds (state : MemoryState Prov Extra MachineKind) : Array AllocId :=
  state.extraFnPtrTable.toArray

def vaListIds (state : MemoryState Prov Extra MachineKind) : Array AllocId :=
  state.vaListTable.toArray

def sourceAllocIdByRuntime (state : MemoryState Prov Extra MachineKind) :
    Array (AllocId × UInt64) := state.sourceAllocIdByRuntimeTable.toArray

def runtimeBySourceAllocId (state : MemoryState Prov Extra MachineKind) :
    Array (UInt64 × AllocId) := state.runtimeBySourceAllocIdTable.toArray

def pushGlobal (state : MemoryState Prov Extra MachineKind) (entry : GlobalAllocation) :
    MemoryState Prov Extra MachineKind :=
  { state with globalTable := state.globalTable.push entry }

def hasIssuedId (state : MemoryState Prov Extra MachineKind) (id : AllocId) : Bool :=
  state.issuedIdTable.contains id.value

def hasGlobalId (state : MemoryState Prov Extra MachineKind) (id : AllocId) : Bool :=
  state.globalTable.contains id.value

def hasImportedRuntimeId (state : MemoryState Prov Extra MachineKind) (id : AllocId) : Bool :=
  state.importedGlobalRuntimeTable.contains id.value

def importedGraphIdForRuntime? (state : MemoryState Prov Extra MachineKind)
    (id : AllocId) : Option Nat := (state.importedGlobalRuntimeTable.find? id.value).map Prod.snd

def hasExtraFunctionId (state : MemoryState Prov Extra MachineKind) (id : AllocId) : Bool :=
  state.extraFnPtrTable.contains id.value

def hasVaListId (state : MemoryState Prov Extra MachineKind) (id : AllocId) : Bool :=
  state.vaListTable.contains id.value

def mapGlobals (state : MemoryState Prov Extra MachineKind) (f : GlobalAllocation → GlobalAllocation) :
    MemoryState Prov Extra MachineKind :=
  { state with globalTable := state.globalTable.mapValuesChecked f }

/-- Replace payloads on every ordered row sharing a runtime allocation ID,
matching `mapGlobals` semantics while using the certified ID index. -/
def setGlobalPayload (state : MemoryState Prov Extra MachineKind)
    (id : AllocId) (payload : GlobalAllocationPayload) : MemoryState Prov Extra MachineKind :=
  { state with globalTable :=
      (state.globalTable.mapValuesForKey id.value
        (fun global => { global with payload := some payload }) (by intro global; rfl)) }

/-- Array-based metadata import for callers constructing a standalone memory
state. It preserves duplicate rows and source order while rebuilding the
certified lookup index. -/
def setGlobalEntries (state : MemoryState Prov Extra MachineKind)
    (entries : Array GlobalAllocation) : MemoryState Prov Extra MachineKind :=
  { state with globalTable :=
      (KeyedArray.ofArray (fun (global : GlobalAllocation) => global.allocId.value) entries) }

def setIssuedIds (state : MemoryState Prov Extra MachineKind) (ids : Array AllocId) :
    MemoryState Prov Extra MachineKind :=
  { state with issuedIdTable := KeyedArray.ofArray (fun (id : AllocId) => id.value) ids }

def setImportedGlobalIds (state : MemoryState Prov Extra MachineKind)
    (entries : Array (Nat × AllocId)) : MemoryState Prov Extra MachineKind :=
  { state with
    importedGlobalTable := KeyedArray.ofArray (@Prod.fst Nat AllocId) entries
    importedGlobalRuntimeTable := KeyedArray.ofArray (@Prod.fst UInt64 Nat)
      (entries.map fun pair => (pair.2.value, pair.1)) }

def setExtraFunctionIds (state : MemoryState Prov Extra MachineKind) (ids : Array AllocId) :
    MemoryState Prov Extra MachineKind :=
  { state with extraFnPtrTable := KeyedArray.ofArray (fun (id : AllocId) => id.value) ids }

def setVaListIds (state : MemoryState Prov Extra MachineKind) (ids : Array AllocId) :
    MemoryState Prov Extra MachineKind :=
  { state with vaListTable := KeyedArray.ofArray (fun (id : AllocId) => id.value) ids }

def setSourceAllocIdCrosswalks (state : MemoryState Prov Extra MachineKind)
    (byRuntime : Array (AllocId × UInt64)) (bySource : Array (UInt64 × AllocId)) :
    MemoryState Prov Extra MachineKind :=
  { state with
    sourceAllocIdByRuntimeTable :=
      (KeyedArray.ofArray (fun (pair : AllocId × UInt64) => pair.1.value) byRuntime)
    runtimeBySourceAllocIdTable := KeyedArray.ofArray (@Prod.fst UInt64 AllocId) bySource }

def empty : MemoryState Prov Extra MachineKind := {
  nextAllocId := 1
  idSupplyExhausted := false
  issuedIdTable := .empty (fun (id : AllocId) => id.value)
  live := #[]
  dead := #[]
  globalTable := .empty (fun (global : GlobalAllocation) => global.allocId.value)
  importedGlobalTable := .empty (@Prod.fst Nat AllocId)
  importedGlobalRuntimeTable := .empty (@Prod.fst UInt64 Nat)
  extraFnPtrTable := .empty (fun (id : AllocId) => id.value)
  vaListTable := .empty (fun (id : AllocId) => id.value)
  sourceAllocIdByRuntimeTable := .empty (fun (pair : AllocId × UInt64) => pair.1.value)
  runtimeBySourceAllocIdTable := .empty (@Prod.fst UInt64 AllocId)
}

private def containsId (state : MemoryState Prov Extra MachineKind) (id : AllocId) : Bool :=
  state.issuedIdTable.contains id.value || state.live.any (fun entry => entry.1 == id) ||
    state.dead.any (fun entry => entry.allocId == id) ||
  state.globalTable.contains id.value

/-- `AllocMap::reserve` uses an AtomicU64 starting at one and `fetch_add`.
The returned ID is consumed before later machine hooks run. A zero value
reifies the source's `NonZero::new(...).unwrap()` exhaustion panic; the state
is marked exhausted so a caller cannot continue after that source-fatal path. -/
def reserveAllocId (state : MemoryState Prov Extra MachineKind) :
    MemoryState Prov Extra MachineKind × Except AllocationIdError AllocId := Id.run do
  if state.idSupplyExhausted || (state.sourceAllocIdWorldActive && state.sourceAllocIdExhausted) then
    return (state, .error .exhausted)
  let rawId := state.sourceAllocIdNext
  if state.sourceAllocIdWorldActive && rawId == 0 then
    return ({ state with sourceAllocIdExhausted := true }, .error .exhausted)
  let advanced := { state with nextAllocId := state.nextAllocId + 1 }
  let advanced := if state.sourceAllocIdWorldActive then
      { advanced with sourceAllocIdNext := rawId + 1 }
    else advanced
  match AllocId.ofUInt64 state.nextAllocId with
  | none =>
      return ({ advanced with idSupplyExhausted := true }, .error .exhausted)
  | some allocId =>
      if containsId state allocId then
        return (advanced, .error (.alreadyIssued allocId))
      let advanced := { advanced with issuedIdTable := state.issuedIdTable.push allocId }
      let advanced := if state.sourceAllocIdWorldActive then
          { advanced with
            sourceAllocIdByRuntimeTable := advanced.sourceAllocIdByRuntimeTable.push (allocId, rawId)
            runtimeBySourceAllocIdTable := advanced.runtimeBySourceAllocIdTable.push (rawId, allocId) }
        else advanced
      return (advanced, .ok allocId)

def sourceAllocIdForRuntime? (state : MemoryState Prov Extra MachineKind) (id : AllocId) : Option UInt64 :=
  (state.sourceAllocIdByRuntimeTable.find? id.value).map Prod.snd

def runtimeForSourceAllocId? (state : MemoryState Prov Extra MachineKind) (sourceId : UInt64) : Option AllocId :=
  (state.runtimeBySourceAllocIdTable.find? sourceId).map Prod.snd

def findGlobal? (state : MemoryState Prov Extra MachineKind) (id : AllocId) :
    Option GlobalAllocation :=
  state.globalTable.find? id.value

def globalsForId (state : MemoryState Prov Extra MachineKind) (id : AllocId) :
    Array GlobalAllocation := state.globalTable.valuesFor id.value

def runtimeIdForExport? (state : MemoryState Prov Extra MachineKind) (exportId : Nat) :
    Option AllocId :=
  (state.importedGlobalTable.find? exportId).map Prod.snd

def hasFunctionPointer (state : MemoryState Prov Extra MachineKind) (id : AllocId) : Bool :=
  state.extraFnPtrTable.contains id.value ||
    state.globalTable.any? id.value fun entry => entry.kind == .function

def isAllocLive (state : MemoryState Prov Extra MachineKind) (id : AllocId) : Bool :=
  state.live.any (fun entry => entry.1 == id) || state.extraFnPtrTable.contains id.value ||
    state.vaListTable.contains id.value || state.globalTable.contains id.value

def registerExtraFunction (state : MemoryState Prov Extra MachineKind) (id : AllocId) :
    MemoryState Prov Extra MachineKind :=
  if state.extraFnPtrTable.contains id.value then state
  else { state with extraFnPtrTable := state.extraFnPtrTable.push id }

def registerVaList (state : MemoryState Prov Extra MachineKind) (id : AllocId) :
    MemoryState Prov Extra MachineKind :=
  if state.vaListTable.contains id.value then state
  else { state with vaListTable := state.vaListTable.push id }

/-- Source `get_alloc_info` precedence: local bytes, function values, va-lists,
compiler globals, then dead-allocation metadata. Missing metadata is an
explicit lookup error instead of an unchecked map expectation. -/
def getAllocInfo (state : MemoryState Prov Extra MachineKind) (id : AllocId) :
    Except AllocationLookupError AllocationInfo := do
  if let some localEntry := state.live.find? fun entry => entry.1 == id then
    let allocation := localEntry.2.allocation
    return ⟨allocation.byteSize, allocation.align, .liveData, allocation.mutability⟩
  if state.hasFunctionPointer id then
    return ⟨Size.ZERO, Align.ONE, .function, .Not⟩
  if state.vaListTable.contains id.value then
    return ⟨Size.ZERO, Align.ONE, .vaList, .Not⟩
  if let some global := state.findGlobal? id then
    match global.kind with
    | .function => return ⟨Size.ZERO, Align.ONE, .function, .Not⟩
    | .vtable => return ⟨Size.ZERO, global.align, .vtable, .Not⟩
    | .typeId => return ⟨Size.ZERO, Align.ONE, .typeId, .Not⟩
    | .static | .memory =>
        return ⟨global.size, global.align, .liveData, global.mutability⟩
  if let some dead := state.dead.find? fun entry => entry.allocId == id then
    return ⟨dead.size, dead.align, .dead, .Not⟩
  throw (.unavailable id)

/-- Source `get_live_alloc_size_and_align`, with both absent metadata and a
dead allocation distinguished explicitly. -/
def getLiveAllocSizeAndAlign (state : MemoryState Prov Extra MachineKind)
    (id : AllocId) (message : CheckInAllocMsg) :
    Except LiveAllocationInfoError (Size × Align) := do
  let info ← (state.getAllocInfo id).mapError LiveAllocationInfoError.lookup
  if info.kind == .dead then throw (.useAfterFree id message)
  return (info.size, info.align)

private def validateReservedGlobal (state : MemoryState Prov Extra MachineKind)
    (exportId : Nat) (entry : GlobalAllocation) : Except MemoryMetadataError Unit := do
  if state.importedGlobalTable.contains exportId then
    throw (.duplicateExportId exportId)
  if state.globalTable.contains entry.allocId.value then
    throw (.duplicateRuntimeId entry.allocId)
  if state.live.any fun old => old.1 == entry.allocId then
    throw (.globalIdAlreadyPresent entry.allocId)
  if state.dead.any fun old => old.allocId == entry.allocId then
    throw (.globalIdAlreadyPresent entry.allocId)
  if !(state.issuedIdTable.contains entry.allocId.value) then
    throw (.globalIdAlreadyPresent entry.allocId)
  pure ()

private def insertReservedGlobal (state : MemoryState Prov Extra MachineKind)
    (exportId : Nat) (entry : GlobalAllocation) : MemoryState Prov Extra MachineKind :=
  { state with
    globalTable := state.globalTable.push entry
    importedGlobalTable := state.importedGlobalTable.push (exportId, entry.allocId)
    importedGlobalRuntimeTable := state.importedGlobalRuntimeTable.push (entry.allocId.value, exportId)
  }

/-- Validate before updating any table, and return the exact input state on a
metadata failure. Returning the prefix together with its outcome lets callers
release their rollback alias before the successful indexed updates. -/
private def registerReservedGlobal (state : MemoryState Prov Extra MachineKind)
    (exportId : Nat) (entry : GlobalAllocation) :
      MemoryState Prov Extra MachineKind × Except MemoryMetadataError Unit :=
  match validateReservedGlobal state exportId entry with
  | .error error => (state, .error error)
  | .ok () => (insertReservedGlobal state exportId entry, .ok ())

/-- The former fallible helper, retained as a specification for the exact
success result and error ordering of `registerReservedGlobal`. -/
private def registerReservedGlobalLegacy (state : MemoryState Prov Extra MachineKind)
    (exportId : Nat) (entry : GlobalAllocation) :
      Except MemoryMetadataError (MemoryState Prov Extra MachineKind) :=
  match validateReservedGlobal state exportId entry with
  | .error error => .error error
  | .ok _ => .ok (insertReservedGlobal state exportId entry)

private def findLive? (state : MemoryState Prov Extra MachineKind) (id : AllocId) :
    Option (LocalAllocation Prov Extra MachineKind) :=
  (state.live.find? fun entry => entry.1 == id).map Prod.snd

private def insertLive (state : MemoryState Prov Extra MachineKind) (id : AllocId)
    (entry : LocalAllocation Prov Extra MachineKind) : MemoryState Prov Extra MachineKind :=
  { state with live := (state.live.filter fun old => old.1 != id).push (id, entry) }

def setLiveAllocation [DecidableEq MachineKind]
    (state : MemoryState Prov Extra MachineKind) (id : AllocId)
    (allocation : Allocation Prov Extra) : Except AllocationLookupError
      (MemoryState Prov Extra MachineKind) := do
  let some entry := findLive? state id | throw (.unavailable id)
  return insertLive state id { entry with allocation := allocation }

/-- Exact live write-back from a raw current lookup. This exposes the update
without requiring clients to unfold private memory-map helpers. -/
theorem setLiveAllocation_of_find [DecidableEq MachineKind]
    (state : MemoryState Prov Extra MachineKind) (id : AllocId)
    (entry : LocalAllocation Prov Extra MachineKind) (allocation : Allocation Prov Extra)
    (present : state.live.find? (fun row => row.1 == id) = some (id,entry)) :
    state.setLiveAllocation id allocation = .ok
      {state with live := ((state.live.filter fun row => row.1 != id).push (id,{entry with allocation}))} := by
  simp [setLiveAllocation,findLive?,insertLive,present]
  rfl

private def removeLive (state : MemoryState Prov Extra MachineKind) (id : AllocId) :
    MemoryState Prov Extra MachineKind × Option (LocalAllocation Prov Extra MachineKind) :=
  let found := findLive? state id
  ({ state with live := state.live.filter fun old => old.1 != id }, found)

private def insertDead (state : MemoryState Prov Extra MachineKind) (entry : DeadAllocation) :
    MemoryState Prov Extra MachineKind :=
  { state with dead := (state.dead.filter fun old => old.allocId != entry.allocId).push entry }

/-- The upstream provenance collector prunes only dead-allocation metadata in
this part of `Memory`; live-map and address-map collection have separate
owners. -/
def removeUnreachable (state : MemoryState Prov Extra MachineKind) (reachable : Array AllocId) :
    MemoryState Prov Extra MachineKind :=
  { state with dead := state.dead.filter fun entry => reachable.contains entry.allocId }

private theorem highWater_absent {V : Type} {keyFn : V → UInt64}
    (table : KeyedArray UInt64 V keyFn) (cursor : UInt64)
    (below : ∀ row ∈ table.toArray, (keyFn row).toNat < cursor.toNat) :
    table.contains cursor = false := by
  rw [KeyedArray.contains_rows]
  cases found : (table.toArray.map keyFn).contains cursor with
  | false => rfl
  | true =>
    have present : cursor ∈ table.toArray.map keyFn := by
      simpa only [Array.contains_eq_mem,decide_eq_true_eq] using found
    obtain ⟨row,member,equal⟩ := Array.mem_map.mp present
    have bound := below row member
    rw [equal] at bound
    exact False.elim (Nat.lt_irrefl _ bound)

/-- Raw high-water data and nonzero supplies suffice for the actual allocator
reservation. No future allocation/byte/choice operation succeeds by assumption. -/
theorem reserve_of_highWater (state : MemoryState Prov Extra MachineKind)
    (available : state.idSupplyExhausted = false) (nonzero : state.nextAllocId ≠ 0)
    (sourceAvailable : state.sourceAllocIdWorldActive = true → state.sourceAllocIdExhausted = false)
    (sourceNonzero : state.sourceAllocIdWorldActive = true → state.sourceAllocIdNext ≠ 0)
    (issued : ∀ id ∈ state.issuedIds, id.value.toNat < state.nextAllocId.toNat)
    (live : ∀ row ∈ state.live, row.1.value.toNat < state.nextAllocId.toNat)
    (global : ∀ row ∈ state.globals, row.allocId.value.toNat < state.nextAllocId.toNat)
    (dead : ∀ row ∈ state.dead, row.allocId.value.toNat < state.nextAllocId.toNat) :
    ∃ after, state.reserveAllocId = (after,.ok ⟨state.nextAllocId,nonzero⟩) := by
  have issuedAbsent : state.issuedIdTable.contains state.nextAllocId = false :=
    highWater_absent _ _ (by simpa only [issuedIds] using issued)
  have globalAbsent : state.globalTable.contains state.nextAllocId = false :=
    highWater_absent _ _ (by simpa only [globals] using global)
  have liveAbsent : state.live.any (fun row => row.1 == (⟨state.nextAllocId,nonzero⟩ : AllocId)) = false := by
    apply Array.any_eq_false.mpr
    intro index valid found
    have equal := beq_iff_eq.mp found
    have bound := live state.live[index] (Array.getElem_mem valid)
    rw [equal] at bound
    exact False.elim (Nat.lt_irrefl _ bound)
  have deadAbsent : state.dead.any (fun row => row.allocId == (⟨state.nextAllocId,nonzero⟩ : AllocId)) = false := by
    apply Array.any_eq_false.mpr
    intro index valid found
    have equal := beq_iff_eq.mp found
    have bound := dead state.dead[index] (Array.getElem_mem valid)
    rw [equal] at bound
    exact False.elim (Nat.lt_irrefl _ bound)
  have absent : containsId state ⟨state.nextAllocId,nonzero⟩ = false := by
    simp only [containsId,issuedAbsent,globalAbsent,liveAbsent,deadAbsent,Bool.false_or]
  cases active : state.sourceAllocIdWorldActive with
  | false =>
    simp [reserveAllocId,available,active,AllocId.ofUInt64,nonzero,absent,Id.run,pure,Pure.pure]
  | true =>
    have source := sourceAvailable active
    have sourceNZ := sourceNonzero active
    simp [reserveAllocId,available,active,source,sourceNZ,AllocId.ofUInt64,nonzero,absent,Id.run,pure,Pure.pure]

end MemoryState

structure MachineHookResult (HookState α : Type) where
  state : HookState
  outcome : Except String α

inductive AdjustedGlobalAllocation (Prov Extra : Type) where
  | borrowed (allocation : Allocation Prov Extra)
  | owned (allocation : Allocation Prov Extra)

/-- A callback receives the current memory and returns its complete successor,
including on failure. This is an ordered state transition, never a map merge
between two independently changed memory snapshots. -/
structure MemoryStateHookResult (Prov Extra MachineKind HookState α : Type) where
  memory : MemoryState Prov Extra MachineKind
  state : HookState
  outcome : Except String α

/-- Compatibility name retained for the global-allocation source interface. -/
abbrev GlobalMemoryHookResult := MemoryStateHookResult

structure GlobalAllocationHooks
    (Prov Extra MachineKind HookState : Type) where
  /-- Install the authoritative memory into any embedded machine view before
  entering callbacks and after lifecycle-owned cache insertion. Hook states
  without an embedded memory leave their independent state unchanged. -/
  synchronizeMemory : MemoryState Prov Extra MachineKind → HookState → HookState
  evaluateStaticInitializer : MemoryState Prov Extra MachineKind → HookState → Nat →
    GlobalMemoryHookResult Prov Extra MachineKind HookState (Allocation CtfeProvenance Unit)
  beforeAccessGlobal : MemoryState Prov Extra MachineKind → HookState → AllocId → Allocation CtfeProvenance Unit →
    Option Nat → Bool → GlobalMemoryHookResult Prov Extra MachineKind HookState Unit
  adjustGlobalAllocation : MemoryState Prov Extra MachineKind → HookState → AllocId → Allocation CtfeProvenance Unit →
    GlobalMemoryHookResult Prov Extra MachineKind HookState (AdjustedGlobalAllocation Prov Extra)

structure GlobalAllocationResult (Prov Extra MachineKind HookState : Type) where
  memory : MemoryState Prov Extra MachineKind
  hooks : HookState
  outcome : Except GlobalAccessError (AdjustedGlobalAllocation Prov Extra)

structure MemoryAccessResult (Prov Extra MachineKind HookState α : Type) where
  memory : MemoryState Prov Extra MachineKind
  hooks : HookState
  outcome : Except MemoryAccessError α

structure PointerResolutionResult (Prov Extra MachineKind HookState ProvExtra : Type) where
  memory : MemoryState Prov Extra MachineKind
  state : HookState
  outcome : Except UInt64 (AllocId × Size × ProvExtra)

structure MemoryLifecycleResult (Prov Extra MachineKind HookState α : Type) where
  memory : MemoryState Prov Extra MachineKind
  hooks : HookState
  outcome : Except MemoryLifecycleError α

/-- The source `Memory::deallocate_ptr` moves the removed allocation into a
local owner. Preserve that exact owner in the result so machine adapters can
run its drop effects on every post-removal return without inferring ownership
from a map difference. -/
structure MemoryDeallocationResult (Prov Extra MachineKind HookState : Type) where
  memory : MemoryState Prov Extra MachineKind
  hooks : HookState
  detached : Option (AllocId × LocalAllocation Prov Extra MachineKind)
  outcome : Except MemoryLifecycleError Unit

/-- Reallocation is allocate-copy-deallocate. When the final deallocation
removes its source before returning an error, preserve that exact owner for
adapters that must perform allocation-specific drop effects. -/
structure MemoryReallocationResult (Prov Extra MachineKind HookState : Type) where
  memory : MemoryState Prov Extra MachineKind
  hooks : HookState
  detached : Option (AllocId × LocalAllocation Prov Extra MachineKind)
  outcome : Except MemoryLifecycleError (Pointer Prov)

structure MemoryCopyResult (Prov Extra MachineKind HookState : Type) where
  memory : MemoryState Prov Extra MachineKind
  hooks : HookState
  outcome : Except String Unit

instance : ToString MemoryLifecycleError where
  toString
    | .allocation error => toString error
    | .allocationIdError error => toString error
    | .metadataError error => toString error
    | .hookFailure hook message => s!"{hook} hook failed: {message}"
    | .allocationTooLarge size maximum =>
        s!"allocation size {size.bytes} exceeds maximum object size {maximum.bytes}"
    | .allocationNotLocal id =>
        s!"allocation {id.value} is not present in the local allocation map"
    | .dynamicallyAllocatingGlobal => "attempted to create local memory with the global allocation kind"
    | .danglingPointer address => s!"pointer address {address} has no allocation provenance"
    | .nonzeroAllocationOffset operation id offset =>
        s!"{operation} of allocation {id.value} used offset {offset.bytes}, expected zero"
    | .globalAllocationDeallocation id kind =>
        s!"cannot deallocate global allocation {id.value} ({kind})"
    | .useAfterFree id => s!"allocation {id.value} was already deallocated"
    | .immutableAllocation id => s!"cannot deallocate immutable allocation {id.value}"
    | .memoryKindMismatch id => s!"deallocation kind does not match allocation {id.value}"
    | .layoutMismatch id size requestedSize align requestedAlign =>
        s!"allocation {id.value} has layout ({size.bytes}, {align.pow2}), requested " ++
          s!"({requestedSize.bytes}, {requestedAlign.pow2})"
    | .duplicateDeadAllocation id => s!"dead-allocation map already contained {id.value}"

/-! `MemoryLifecycleHooks` names the machine-dependent portions of rustc's
`Machine` trait. Every stateful hook returns its updated hook state even when
it fails, so callers can preserve source ordering and side effects. The copy
hook is required for reallocation and must implement the source `mem_copy`
checks and byte/provenance/initialization transfer; there is no default copy. -/
structure MemoryLifecycleHooks
    (Prov Extra MachineKind HookState ProvExtra : Type) where
  /-- Keep machine states that embed memory aligned with the explicit
  authoritative successor at each allocation lifecycle boundary. -/
  synchronizeMemory : MemoryState Prov Extra MachineKind → HookState → HookState
  initLocalAllocation : MemoryState Prov Extra MachineKind → HookState → AllocId →
    MemoryKind MachineKind → Size → Align →
    MemoryStateHookResult Prov Extra MachineKind HookState Extra
  adjustRootPointer : MemoryState Prov Extra MachineKind → HookState → AllocId →
    MemoryKind MachineKind →
    MemoryStateHookResult Prov Extra MachineKind HookState (Pointer Prov)
  resolvePointer : MemoryState Prov Extra MachineKind → HookState → Pointer (Option Prov) → Int →
    PointerResolutionResult Prov Extra MachineKind HookState ProvExtra
  beforeDeallocation : MemoryState Prov Extra MachineKind → HookState →
    Allocation Prov Extra → Pointer (Option Prov) → AllocId → ProvExtra → Size → Align →
    MemoryKind MachineKind →
    MemoryStateHookResult Prov Extra MachineKind HookState Unit
  copyMemory : HookState → MemoryState Prov Extra MachineKind →
    Pointer (Option Prov) → Pointer (Option Prov) → Size → Bool → Bool →
    MemoryCopyResult Prov Extra MachineKind HookState

/-! Hooks around the allocation-storage part of rustc's `mem_copy_repeatedly`.
Pointer access and machine callbacks vary between interpreter machines, so
they are explicit inputs. Read/write callbacks return the memory as well as
hook state so mutations to `Allocation.extra` remain visible if a later stage
fails. -/
structure MemoryCopyHooks
    (Prov Extra MachineKind HookState ProvExtra : Type) where
  /-- Install the authoritative successor in machine states that also contain
  a memory view before the next callback and in every returned prefix. -/
  synchronizeMemory : MemoryState Prov Extra MachineKind → HookState → HookState
  pointerAccess : MemoryState Prov Extra MachineKind → HookState →
    Pointer (Option Prov) → Size →
    MemoryStateHookResult Prov Extra MachineKind HookState (Option (AllocId × Size × ProvExtra))
  tryGetAllocId : MemoryState Prov Extra MachineKind → HookState →
    Pointer (Option Prov) → UInt64 → Option AllocId
  beforeAllocationAccess : MemoryState Prov Extra MachineKind → HookState → AllocId →
    MemoryStateHookResult Prov Extra MachineKind HookState Unit
  beforeMemoryRead : HookState → MemoryState Prov Extra MachineKind →
    Allocation Prov Extra → Pointer (Option Prov) → AllocId → ProvExtra → AllocRange →
    MemoryCopyResult Prov Extra MachineKind HookState
  beforeMemoryWrite : HookState → MemoryState Prov Extra MachineKind →
    Allocation Prov Extra → Pointer (Option Prov) → AllocId → ProvExtra → AllocRange →
    MemoryCopyResult Prov Extra MachineKind HookState

/-- The deallocation source event uses only resolution and the ordered
before-deallocation effect. Allocation/root/copy callbacks are not inputs. -/
structure MemoryDeallocationHooks (Prov Extra MachineKind HookState ProvExtra : Type) where
  synchronizeMemory : MemoryState Prov Extra MachineKind → HookState → HookState
  resolvePointer : MemoryState Prov Extra MachineKind → HookState → Pointer (Option Prov) → Int →
    PointerResolutionResult Prov Extra MachineKind HookState ProvExtra
  beforeDeallocation : MemoryState Prov Extra MachineKind → HookState → Allocation Prov Extra →
    Pointer (Option Prov) → AllocId → ProvExtra → Size → Align → MemoryKind MachineKind →
    MemoryStateHookResult Prov Extra MachineKind HookState Unit

def MemoryLifecycleHooks.deallocation (hooks : MemoryLifecycleHooks Prov Extra MachineKind HookState ProvExtra) :
    MemoryDeallocationHooks Prov Extra MachineKind HookState ProvExtra :=
  ⟨hooks.synchronizeMemory,hooks.resolvePointer,hooks.beforeDeallocation⟩

namespace MemoryLifecycle

private def globalPayloadKind : GlobalAllocationPayload → GlobalAllocationKind
  | .memory _ => .memory
  | .function => .function
  | .vtable => .vtable
  | .typeId => .typeId
  | .static .. => .static

/-- Register an imported global by separating its canonical exporter graph ID
from the fresh runtime `AllocId` assigned by rustc's monotonic supply. This
keeps imported IDs disjoint from later local allocations and makes every
export-ID lookup explicit. -/
def registerImportedGlobal [DecidableEq MachineKind]
    (memory : MemoryState Prov Extra MachineKind) (hooksState : HookState)
    (exportId : Nat) (kind : GlobalAllocationKind) (size : Size) (align : Align)
    (mutability : Mutability := .Not)
    (payload : Option GlobalAllocationPayload := none) :
    MemoryLifecycleResult Prov Extra MachineKind HookState AllocId := Id.run do
  if memory.importedGlobalTable.contains exportId then
    return ⟨memory, hooksState, .error (.metadataError (.duplicateExportId exportId))⟩
  let (advanced, reserved) := memory.reserveAllocId
  let allocId ← match reserved with
    | .ok allocId => pure allocId
    | .error error =>
        return ⟨advanced, hooksState, .error (.allocationIdError error)⟩
  let (registered, outcome) := MemoryState.registerReservedGlobal advanced exportId
      ⟨allocId, kind, size, align, mutability, payload⟩
  match outcome with
  | .ok () => return ⟨registered, hooksState, .ok allocId⟩
  | .error error =>
      return ⟨registered, hooksState, .error (.metadataError error)⟩

private def registerImportedGlobalLegacy [DecidableEq MachineKind]
    (memory : MemoryState Prov Extra MachineKind) (hooksState : HookState)
    (exportId : Nat) (kind : GlobalAllocationKind) (size : Size) (align : Align)
    (mutability : Mutability := .Not)
    (payload : Option GlobalAllocationPayload := none) :
    MemoryLifecycleResult Prov Extra MachineKind HookState AllocId := Id.run do
  if memory.importedGlobalTable.contains exportId then
    return ⟨memory, hooksState, .error (.metadataError (.duplicateExportId exportId))⟩
  let (advanced, reserved) := memory.reserveAllocId
  let allocId ← match reserved with
    | .ok allocId => pure allocId
    | .error error =>
        return ⟨advanced, hooksState, .error (.allocationIdError error)⟩
  match MemoryState.registerReservedGlobalLegacy advanced exportId
      ⟨allocId, kind, size, align, mutability, payload⟩ with
  | .ok registered => return ⟨registered, hooksState, .ok allocId⟩
  | .error error =>
      return ⟨advanced, hooksState, .error (.metadataError error)⟩

private theorem registerImportedGlobal_legacy_eq [DecidableEq MachineKind]
    (memory : MemoryState Prov Extra MachineKind) (hooksState : HookState)
    (exportId : Nat) (kind : GlobalAllocationKind) (size : Size) (align : Align)
    (mutability : Mutability) (payload : Option GlobalAllocationPayload) :
    MemoryLifecycle.registerImportedGlobal memory hooksState exportId kind size align
      mutability payload =
        registerImportedGlobalLegacy memory hooksState exportId kind size align
          mutability payload := by
  unfold MemoryLifecycle.registerImportedGlobal registerImportedGlobalLegacy
  by_cases hduplicate : memory.importedGlobalTable.contains exportId
  · simp [hduplicate]
  · simp only [hduplicate]
    cases hreserve : memory.reserveAllocId with
    | mk advanced reserved =>
      cases hresult : reserved with
      | error error => simp
      | ok allocId =>
        cases hvalidation : MemoryState.validateReservedGlobal advanced exportId
            ⟨allocId, kind, size, align, mutability, payload⟩ with
        | error error =>
          simp [MemoryState.registerReservedGlobal,
            MemoryState.registerReservedGlobalLegacy, hvalidation]
        | ok validated =>
          simp [MemoryState.registerReservedGlobal,
            MemoryState.registerReservedGlobalLegacy, hvalidation]

/-- Source `get_global_alloc`: classify the compiler global, resolve a lazy
static initializer when needed, run `before_access_global`, then let the
machine convert provenance/bytes/extras. A borrowed conversion remains marked
borrowed so immutable access does not populate the local map. -/
def getGlobalAlloc
    (memory : MemoryState Prov Extra MachineKind) (hooksState : HookState)
    (id : AllocId) (isWrite : Bool)
    (hooks : GlobalAllocationHooks Prov Extra MachineKind HookState) :
    GlobalAllocationResult Prov Extra MachineKind HookState := Id.run do
  let finish := fun memory state outcome =>
    (⟨memory,hooks.synchronizeMemory memory state,outcome⟩ : GlobalAllocationResult Prov Extra MachineKind HookState)
  let hooksState := hooks.synchronizeMemory memory hooksState
  let some global := memory.findGlobal? id
    | return finish memory hooksState (.error (.notFound id))
  let (allocation, staticDef, sourceMemory, sourceHookState) ← match global.kind, global.payload with
    | .function, _ => return finish memory hooksState (.error (.dereferenceFunctionPointer id))
    | .vtable, _ => return finish memory hooksState (.error (.dereferenceVTablePointer id))
    | .typeId, _ => return finish memory hooksState (.error (.dereferenceTypeIdPointer id))
    | .memory, some (.memory allocation) => pure (allocation, none, memory, hooksState)
    | .static, some (.static definition isStatic threadLocal foreignItem) =>
        if !isStatic then
          return finish memory hooksState (.error (.staticNotAStatic id definition))
        if threadLocal then
          return finish memory hooksState (.error (.threadLocalStatic id definition))
        if foreignItem then
          return finish memory hooksState (.error (.unsupportedExternStatic id definition))
        let evaluated := hooks.evaluateStaticInitializer memory hooksState definition
        match evaluated.outcome with
        | .ok allocation => pure (allocation, some definition, evaluated.memory,
            hooks.synchronizeMemory evaluated.memory evaluated.state)
        | .error message =>
            return finish evaluated.memory evaluated.state (.error (.hookFailure "evalStaticInitializer" message))
    | .memory, none =>
        return finish memory hooksState (.error (.payloadUnavailable id))
    | .static, none =>
        return finish memory hooksState (.error (.payloadUnavailable id))
    | kind, some payload =>
        return finish memory hooksState (.error (.payloadKindMismatch id kind (globalPayloadKind payload)))
  let before := hooks.beforeAccessGlobal sourceMemory sourceHookState id allocation staticDef isWrite
  let (beforeMemory,beforeResult) ← match before.outcome with
    | .ok () => pure (before.memory,hooks.synchronizeMemory before.memory before.state)
    | .error message =>
        return finish before.memory before.state (.error (.hookFailure "beforeAccessGlobal" message))
  let adjusted := hooks.adjustGlobalAllocation beforeMemory beforeResult id allocation
  match adjusted.outcome with
  | .ok allocation => return finish adjusted.memory adjusted.state (.ok allocation)
  | .error message =>
      return finish adjusted.memory adjusted.state (.error (.hookFailure "adjustGlobalAllocation" message))

/-- Source `get_alloc_raw`: return a local allocation directly. On a global
miss, cache only a machine-owned conversion; a borrowed conversion is returned
without inserting that allocation. All nested callback memory transitions are
retained before the outer cache insertion or any failure is returned. -/
def getAllocRaw [DecidableEq MachineKind]
    (memory : MemoryState Prov Extra MachineKind) (hooksState : HookState)
    (id : AllocId) (globalKind : Option MachineKind)
    (hooks : GlobalAllocationHooks Prov Extra MachineKind HookState) :
    MemoryAccessResult Prov Extra MachineKind HookState (Allocation Prov Extra) := Id.run do
  let finish := fun memory state outcome =>
    (⟨memory,hooks.synchronizeMemory memory state,outcome⟩ : MemoryAccessResult Prov Extra MachineKind HookState (Allocation Prov Extra))
  if let some entry := memory.live.find? fun old => old.1 == id then
    return finish memory hooksState (.ok entry.2.allocation)
  let global := getGlobalAlloc memory hooksState id false hooks
  let adjusted ← match global.outcome with
    | .ok allocation => pure allocation
    | .error error =>
        return finish global.memory global.hooks (.error (.globalAccess error))
  match adjusted with
  | .borrowed allocation => return finish global.memory global.hooks (.ok allocation)
  | .owned allocation =>
      let some machineKind := globalKind
        | return finish global.memory global.hooks (.error (.missingGlobalMachineKind id))
      let entry : LocalAllocation Prov Extra MachineKind :=
        ⟨.machine machineKind, allocation⟩
      return finish (global.memory.insertLive id entry) global.hooks (.ok allocation)

/-- Source `get_alloc_raw_mut`: missing globals are adjusted with `is_write`,
then materialized as `MemoryKind::Machine(GLOBAL_KIND)` before the mutability
check. Thus an immutable-global error retains the newly cached allocation. -/
def getAllocRawMut [DecidableEq MachineKind]
    (memory : MemoryState Prov Extra MachineKind) (hooksState : HookState)
    (id : AllocId) (globalKind : Option MachineKind)
    (hooks : GlobalAllocationHooks Prov Extra MachineKind HookState) :
    MemoryAccessResult Prov Extra MachineKind HookState (Allocation Prov Extra) := Id.run do
  let finish := fun memory state outcome =>
    (⟨memory,hooks.synchronizeMemory memory state,outcome⟩ : MemoryAccessResult Prov Extra MachineKind HookState (Allocation Prov Extra))
  let (afterMaterialize, hookState, allocation) ←
    match memory.live.find? fun old => old.1 == id with
    | some entry => pure (memory, hooksState, entry.2.allocation)
    | none =>
        let global := getGlobalAlloc memory hooksState id true hooks
        let adjusted ← match global.outcome with
          | .ok allocation => pure allocation
          | .error error =>
              return finish global.memory global.hooks (.error (.globalAccess error))
        let allocation := match adjusted with
          | .borrowed allocation => allocation
          | .owned allocation => allocation
        let some machineKind := globalKind
          | return finish global.memory global.hooks (.error (.missingGlobalMachineKind id))
        let entry : LocalAllocation Prov Extra MachineKind :=
          ⟨.machine machineKind, allocation⟩
        pure (global.memory.insertLive id entry, global.hooks, allocation)
  if allocation.mutability == .Not then
    return finish afterMaterialize hookState (.error (.readOnlyAllocation id))
  return finish afterMaterialize hookState (.ok allocation)

/-- Perform the allocation-storage part of `mem_copy_repeatedly` after its
caller has resolved pointers and run source/destination access hooks. This
uses Allocation's snapshot-based byte, initialization, and provenance copy.
The source allocation value is captured before the destination update, which
also gives same-allocation copies the source's overlap-safe byte semantics.

The caller remains responsible for the source's pointer-access checks, the
zero-size source/read-hook ordering, `before_alloc_access`, memory read/write
hooks, and global-allocation lookup. Missing local allocations are explicit
errors; this helper never treats a global or unresolved allocation as an empty
local block. Any destination mutation already made by Allocation before its
error is written back into the memory state. -/
def copyResolvedRanges [DecidableEq MachineKind]
    (memory : MemoryState Prov Extra MachineKind) (hooksState : HookState)
    (sourceId : AllocId) (sourceOffset : Size)
    (destId : AllocId) (destOffset : Size) (size : Size) (repeatCount : UInt64)
    (pointerSize : Size) (nonoverlapping : Bool) :
    MemoryLifecycleResult Prov Extra MachineKind HookState Unit := Id.run do
  let some sourceEntry := memory.live.find? fun entry => entry.1 == sourceId
    | return ⟨memory, hooksState, .error (.allocationNotLocal sourceId)⟩
  let some destEntry := memory.live.find? fun entry => entry.1 == destId
    | return ⟨memory, hooksState, .error (.allocationNotLocal destId)⟩
  let sourceRange := allocRange sourceOffset size
  let sameAllocation := sourceId == destId
  let transfer := Allocation.copyRepeatedly sourceEntry.2.allocation sourceRange destOffset
      repeatCount pointerSize sameAllocation nonoverlapping destEntry.2.allocation
  match transfer with
  | .ok () updatedDestination =>
      let updatedEntry := { destEntry.2 with allocation := updatedDestination }
      return ⟨memory.insertLive destId updatedEntry, hooksState, .ok ()⟩
  | .error error updatedDestination =>
      let updatedEntry := { destEntry.2 with allocation := updatedDestination }
      return ⟨memory.insertLive destId updatedEntry, hooksState,
        .error (.allocation error)⟩

/-- Source-ordered bridge for `Memory::mem_copy_repeatedly`. `pointerAccess`
performs the machine's pointer checks and returns `none` for a zero-sized
access. The source lookup probe is deliberately after both pointer checks and
before the source read hook; it still runs for zero-sized copies. A zero-sized
source returns after that probe, while a zero-sized destination returns after
the source read hook. The allocation read/write hooks run in source order,
including for `repeatCount = 0` when the source range is nonempty.

Once both local allocations are resolved, `Allocation.copyRepeatedly` handles
the checked destination size, snapshot, initialization/provenance transfer,
overlap assertions, and destination mutations. This method does not synthesize
global allocations: callers must use their global-allocation path or receive
an explicit `allocationNotLocal` error. -/
def memCopyRepeatedly [DecidableEq MachineKind]
    (memory : MemoryState Prov Extra MachineKind) (hooksState : HookState)
    (sourcePointer destPointer : Pointer (Option Prov)) (size : Size)
    (repeatCount : UInt64) (nonoverlapping : Bool) (pointerSize : Size)
    (hooks : MemoryCopyHooks Prov Extra MachineKind HookState ProvExtra) :
    MemoryLifecycleResult Prov Extra MachineKind HookState Unit := Id.run do
  let hooksState := hooks.synchronizeMemory memory hooksState
  let sourceAccess := hooks.pointerAccess memory hooksState sourcePointer size
  let sourceState := hooks.synchronizeMemory sourceAccess.memory sourceAccess.state
  let sourceParts ← match sourceAccess.outcome with
    | .ok parts => pure parts
    | .error message =>
        return ⟨sourceAccess.memory, sourceState,
          .error (.hookFailure "getPtrAccess(source)" message)⟩
  let destSize ← match Size.mul size repeatCount with
    | .ok totalSize => pure totalSize
    | .error error =>
        return ⟨sourceAccess.memory, sourceState,
          .error (.allocation (.memory (.sizeError error)))⟩
  let destAccess := hooks.pointerAccess sourceAccess.memory sourceState destPointer destSize
  let destState := hooks.synchronizeMemory destAccess.memory destAccess.state
  let destParts ← match destAccess.outcome with
    | .ok parts => pure parts
    | .error message =>
        return ⟨destAccess.memory, destState,
          .error (.hookFailure "getPtrAccess(destination)" message)⟩
  let sourceProbe := hooks.tryGetAllocId destAccess.memory destState sourcePointer size.bytes
  let (afterProbeMemory, afterProbeState) ← match sourceProbe with
    | none => pure (destAccess.memory, destState)
    | some allocId =>
        let checked := hooks.beforeAllocationAccess destAccess.memory destState allocId
        let checkedState := hooks.synchronizeMemory checked.memory checked.state
        match checked.outcome with
        | .ok () => pure (checked.memory, checkedState)
        | .error message =>
            return ⟨checked.memory, checkedState,
              .error (.hookFailure "beforeAllocAccess(source)" message)⟩
  let some (sourceId, sourceOffset, sourceProvExtra) := sourceParts
    | return ⟨afterProbeMemory, afterProbeState, .ok ()⟩
  let some sourceEntry := afterProbeMemory.live.find? fun entry => entry.1 == sourceId
    | return ⟨afterProbeMemory, afterProbeState, .error (.allocationNotLocal sourceId)⟩
  let sourceRange := allocRange sourceOffset size
  let read := hooks.beforeMemoryRead afterProbeState afterProbeMemory sourceEntry.2.allocation
      sourcePointer sourceId sourceProvExtra sourceRange
  let readState := hooks.synchronizeMemory read.memory read.hooks
  let afterReadMemory ← match read.outcome with
    | .ok () => pure read.memory
    | .error message =>
        return ⟨read.memory, readState, .error (.hookFailure "beforeMemoryRead" message)⟩
  let some (destId, destOffset, destProvExtra) := destParts
    | return ⟨afterReadMemory, readState, .ok ()⟩
  if !(afterReadMemory.live.any fun entry => entry.1 == destId) then
    return ⟨afterReadMemory, readState, .error (.allocationNotLocal destId)⟩
  let destAccessHook := hooks.beforeAllocationAccess afterReadMemory readState destId
  let destAccessState := hooks.synchronizeMemory destAccessHook.memory destAccessHook.state
  let afterDestAccess ← match destAccessHook.outcome with
    | .ok () => pure destAccessHook.state
    | .error message =>
        return ⟨destAccessHook.memory, destAccessState,
          .error (.hookFailure "beforeAllocAccess(destination)" message)⟩
  let afterDestAccess := hooks.synchronizeMemory destAccessHook.memory afterDestAccess
  let destRange := allocRange destOffset destSize
  let writeBaseMemory := destAccessHook.memory
  let some destEntry := writeBaseMemory.live.find? fun entry => entry.1 == destId
    | return ⟨writeBaseMemory, destAccessState, .error (.allocationNotLocal destId)⟩
  let write := hooks.beforeMemoryWrite afterDestAccess writeBaseMemory
      destEntry.2.allocation destPointer destId destProvExtra destRange
  let writeState := hooks.synchronizeMemory write.memory write.hooks
  let afterWriteMemory ← match write.outcome with
    | .ok () => pure write.memory
    | .error message =>
        return ⟨write.memory, writeState, .error (.hookFailure "beforeMemoryWrite" message)⟩
  let copied := copyResolvedRanges afterWriteMemory writeState sourceId sourceOffset
      destId destOffset size repeatCount pointerSize nonoverlapping
  return {copied with hooks := hooks.synchronizeMemory copied.memory copied.hooks}

/-- The post-reservation portion of source `Memory::insert_allocation`:
initialize machine extras, insert into the live map, then adjust the root
pointer. The caller has already checked the size and reserved the ID. A
root-pointer hook failure leaves the inserted allocation in the map. -/
private def insertAllocationWithId [DecidableEq MachineKind]
    (memory : MemoryState Prov Extra MachineKind) (hooksState : HookState)
    (synchronizeMemory : MemoryState Prov Extra MachineKind → HookState → HookState)
    (allocId : AllocId) (allocation : Allocation Prov Unit)
    (kind : MemoryKind MachineKind)
    (globalKind : Option (MemoryKind MachineKind))
    (initExtra : MemoryState Prov Extra MachineKind → HookState → AllocId →
      MemoryKind MachineKind → Size → Align →
      MemoryStateHookResult Prov Extra MachineKind HookState Extra)
    (adjustRoot : MemoryState Prov Extra MachineKind → HookState → AllocId →
      MemoryKind MachineKind →
      MemoryStateHookResult Prov Extra MachineKind HookState (Pointer Prov)) :
    MemoryLifecycleResult Prov Extra MachineKind HookState (Pointer Prov) := Id.run do
  let size := allocation.byteSize
  let hooksState := synchronizeMemory memory hooksState
  if globalKind = some kind then
    return ⟨memory, hooksState, .error .dynamicallyAllocatingGlobal⟩
  let initialized := initExtra memory hooksState allocId kind size allocation.align
  let initializedState := synchronizeMemory initialized.memory initialized.state
  let extra ← match initialized.outcome with
    | .ok extra => pure extra
    | .error message =>
        return ⟨initialized.memory, initializedState, .error (.hookFailure "initLocalAllocation" message)⟩
  let localEntry : LocalAllocation Prov Extra MachineKind :=
    ⟨kind, allocation.withExtra extra⟩
  let inserted := initialized.memory.insertLive allocId localEntry
  let root := adjustRoot inserted (synchronizeMemory inserted initializedState) allocId kind
  let rootState := synchronizeMemory root.memory root.state
  match root.outcome with
  | .error message =>
      return ⟨root.memory, rootState, .error (.hookFailure "adjustAllocRootPointer" message)⟩
  | .ok pointer => return ⟨root.memory, rootState, .ok pointer⟩

/-- Source `Memory::insert_allocation`: enforce the object-size bound, reserve
an ID, initialize machine extras, insert into the live map, then adjust the
root pointer. -/
def insertAllocation [DecidableEq MachineKind]
    (memory : MemoryState Prov Extra MachineKind) (hooksState : HookState)
    (synchronizeMemory : MemoryState Prov Extra MachineKind → HookState → HookState)
    (allocation : Allocation Prov Unit) (kind : MemoryKind MachineKind)
    (maximumObjectSize : Size) (globalKind : Option (MemoryKind MachineKind))
    (initExtra : MemoryState Prov Extra MachineKind → HookState → AllocId →
      MemoryKind MachineKind → Size → Align →
      MemoryStateHookResult Prov Extra MachineKind HookState Extra)
    (adjustRoot : MemoryState Prov Extra MachineKind → HookState → AllocId →
      MemoryKind MachineKind →
      MemoryStateHookResult Prov Extra MachineKind HookState (Pointer Prov)) :
    MemoryLifecycleResult Prov Extra MachineKind HookState (Pointer Prov) := Id.run do
  let hooksState := synchronizeMemory memory hooksState
  let size := allocation.byteSize
  if size.bytes > maximumObjectSize.bytes then
    return ⟨memory, hooksState, .error (.allocationTooLarge size maximumObjectSize)⟩
  let (reservedMemory, reserved) := memory.reserveAllocId
  let allocId ← match reserved with
    | .ok id => pure id
    | .error message =>
        return ⟨reservedMemory, synchronizeMemory reservedMemory hooksState, .error (.allocationIdError message)⟩
  if globalKind = some kind then
    return ⟨reservedMemory, synchronizeMemory reservedMemory hooksState, .error .dynamicallyAllocatingGlobal⟩
  return insertAllocationWithId reservedMemory hooksState synchronizeMemory allocId allocation kind
    globalKind initExtra adjustRoot

/-- Source `Memory::allocate_ptr`: create zeroed backing storage with the
requested initialization mask, then reserve the allocation ID and enter the
`insert_allocation` transition. The host allocator is a legal-result callback
(`none` means allocation exhaustion). -/
def allocatePtr [DecidableEq MachineKind]
    (memory : MemoryState Prov Extra MachineKind) (hooksState : HookState)
    (synchronizeMemory : MemoryState Prov Extra MachineKind → HookState → HookState)
    (size : Size) (align : Align) (kind : MemoryKind MachineKind) (init : AllocInit)
    (maximumObjectSize : Size) (globalKind : Option (MemoryKind MachineKind))
    (zeroedStorage : Size → Align → Option (Array UInt8))
    (initExtra : MemoryState Prov Extra MachineKind → HookState → AllocId →
      MemoryKind MachineKind → Size → Align →
      MemoryStateHookResult Prov Extra MachineKind HookState Extra)
    (adjustRoot : MemoryState Prov Extra MachineKind → HookState → AllocId →
      MemoryKind MachineKind →
      MemoryStateHookResult Prov Extra MachineKind HookState (Pointer Prov)) :
    MemoryLifecycleResult Prov Extra MachineKind HookState (Pointer Prov) := Id.run do
  let hooksState := synchronizeMemory memory hooksState
  let allocation ← match Allocation.tryNew (Prov := Prov) size align init zeroedStorage with
    | .ok allocation => pure allocation
    | .error error => return ⟨memory, synchronizeMemory memory hooksState, .error (.allocation error)⟩
  return insertAllocation memory hooksState synchronizeMemory allocation kind maximumObjectSize globalKind
    initExtra adjustRoot

/-- Source `Memory::deallocate_ptr`. The local allocation is removed before
mutability, kind, and layout validation. A failure in those checks or in a
machine hook therefore retains the source's already-removed live-map state.
The Miri machine's address-reuse release occurs inside its deallocation hook,
after borrow/race/synchronization checks, before dead-layout caching. -/
def deallocatePtrWith [DecidableEq MachineKind]
    (memory : MemoryState Prov Extra MachineKind) (hooksState : HookState)
    (pointer : Pointer (Option Prov)) (oldSizeAndAlign : Option (Size × Align))
    (kind : MemoryKind MachineKind)
    (hooks : MemoryDeallocationHooks Prov Extra MachineKind HookState ProvExtra) :
    MemoryDeallocationResult Prov Extra MachineKind HookState := Id.run do
  let hooksState := hooks.synchronizeMemory memory hooksState
  let resolved := hooks.resolvePointer memory hooksState pointer 0
  let resolvedState := hooks.synchronizeMemory resolved.memory resolved.state
  let allocIdOffsetProv ← match resolved.outcome with
    | .ok result => pure result
    | .error address =>
        return ⟨resolved.memory, resolvedState, none, .error (.danglingPointer address)⟩
  let (allocId, offset, provExtra) := allocIdOffsetProv
  if offset.bytes != 0 then
    return ⟨resolved.memory, resolvedState, none,
      .error (.nonzeroAllocationOffset "deallocate" allocId offset)⟩
  let (afterRemove, entry?) := resolved.memory.removeLive allocId
  let some entry := entry?
    | match resolved.memory.findGlobal? allocId with
      | some global =>
          return ⟨resolved.memory, resolvedState, none,
            .error (.globalAllocationDeallocation allocId global.kind)⟩
      | none => return ⟨resolved.memory, resolvedState, none, .error (.useAfterFree allocId)⟩
  let detached := some (allocId, entry)
  let allocation := entry.allocation
  if allocation.mutability == .Not then
    return ⟨afterRemove, hooks.synchronizeMemory afterRemove resolvedState, detached,
      .error (.immutableAllocation allocId)⟩
  if entry.kind ≠ kind then
    return ⟨afterRemove, hooks.synchronizeMemory afterRemove resolvedState, detached,
      .error (.memoryKindMismatch allocId)⟩
  if let some (requestedSize, requestedAlign) := oldSizeAndAlign then
    if requestedSize != allocation.byteSize || requestedAlign != allocation.align then
      return ⟨afterRemove, hooks.synchronizeMemory afterRemove resolvedState, detached,
        .error (.layoutMismatch allocId allocation.byteSize requestedSize
          allocation.align requestedAlign)⟩
  let before := hooks.beforeDeallocation afterRemove
      (hooks.synchronizeMemory afterRemove resolvedState) allocation pointer allocId provExtra
      allocation.byteSize allocation.align kind
  let beforeState := hooks.synchronizeMemory before.memory before.state
  match before.outcome with
    | .ok () => pure ()
    | .error message =>
        return ⟨before.memory, beforeState, detached,
          .error (.hookFailure "beforeMemoryDeallocation" message)⟩
  let deadEntry : DeadAllocation := ⟨allocId, allocation.byteSize, allocation.align⟩
  let alreadyDead := before.memory.dead.any fun old => old.allocId == allocId
  let afterDead := before.memory.insertDead deadEntry
  let finalState := hooks.synchronizeMemory afterDead beforeState
  if alreadyDead then
    return ⟨afterDead, finalState, detached, .error (.duplicateDeadAllocation allocId)⟩
  return ⟨afterDead, finalState, detached, .ok ()⟩

/-- Compatibility projection for source users that already own the complete
allocation lifecycle. Deallocation itself consumes only its two actual hooks. -/
def deallocatePtr [DecidableEq MachineKind]
    (memory : MemoryState Prov Extra MachineKind) (hooksState : HookState)
    (pointer : Pointer (Option Prov)) (oldSizeAndAlign : Option (Size × Align))
    (kind : MemoryKind MachineKind)
    (hooks : MemoryLifecycleHooks Prov Extra MachineKind HookState ProvExtra) :
    MemoryDeallocationResult Prov Extra MachineKind HookState :=
  deallocatePtrWith memory hooksState pointer oldSizeAndAlign kind hooks.deallocation

/-- Source `Memory::reallocate_ptr` is `allocate, copy, deallocate`. The
source's `mem_copy` operation is a required callback because its access,
initialization, provenance, and overlapping-copy semantics are separately
ported by the memory-access layer. Any failure keeps mutations from earlier
steps, including a newly allocated block. -/
def reallocatePtr [DecidableEq MachineKind]
    (memory : MemoryState Prov Extra MachineKind) (hooksState : HookState)
    (pointer : Pointer (Option Prov)) (oldSizeAndAlign : Option (Size × Align))
    (newSize : Size) (newAlign : Align) (kind : MemoryKind MachineKind)
    (initGrowth : AllocInit) (maximumObjectSize : Size)
    (globalKind : Option (MemoryKind MachineKind))
    (zeroedStorage : Size → Align → Option (Array UInt8))
    (hooks : MemoryLifecycleHooks Prov Extra MachineKind HookState ProvExtra) :
    MemoryReallocationResult Prov Extra MachineKind HookState := Id.run do
  let hooksState := hooks.synchronizeMemory memory hooksState
  let resolved := hooks.resolvePointer memory hooksState pointer 0
  let resolvedState := hooks.synchronizeMemory resolved.memory resolved.state
  let (oldId, oldOffset, _) ← match resolved.outcome with
    | .ok result => pure result
    | .error address =>
        return ⟨resolved.memory, resolvedState, none, .error (.danglingPointer address)⟩
  if oldOffset.bytes != 0 then
    return ⟨resolved.memory, resolvedState, none,
      .error (.nonzeroAllocationOffset "reallocate" oldId oldOffset)⟩
  let allocated := allocatePtr resolved.memory resolvedState hooks.synchronizeMemory
      newSize newAlign kind initGrowth maximumObjectSize globalKind zeroedStorage
      (fun currentMemory state id allocationKind size align =>
        hooks.initLocalAllocation currentMemory state id allocationKind size align)
      hooks.adjustRootPointer
  let newPointer ← match allocated.outcome with
    | .ok value => pure value
    | .error error => return ⟨allocated.memory, allocated.hooks, none, .error error⟩
  let oldSize ← match oldSizeAndAlign with
    | some (size, _align) => pure (some size)
    | none =>
        match allocated.memory.live.find? fun entry => entry.1 == oldId with
        | some (_, oldEntry) => pure (some oldEntry.allocation.byteSize)
        | none =>
            match allocated.memory.findGlobal? oldId with
            | some global => pure (some global.size)
            | none => pure none
  let some oldSize := oldSize
    | return ⟨allocated.memory, allocated.hooks, none, .error (.useAfterFree oldId)⟩
  let copySize := if oldSize.bytes < newSize.bytes then oldSize else newSize
  let copied := hooks.copyMemory allocated.hooks allocated.memory pointer
      newPointer.withOptionalProvenance copySize false true
  let copiedMemory ← match copied.outcome with
    | .ok () => pure copied.memory
    | .error message =>
        return ⟨copied.memory, copied.hooks, none, .error (.hookFailure "memCopy" message)⟩
  let freed := deallocatePtr copiedMemory copied.hooks pointer oldSizeAndAlign kind hooks
  match freed.outcome with
  | .ok () => return ⟨freed.memory, freed.hooks, freed.detached, .ok newPointer⟩
  | .error error => return ⟨freed.memory, freed.hooks, freed.detached, .error error⟩

end MemoryLifecycle

end Miri.Memory
