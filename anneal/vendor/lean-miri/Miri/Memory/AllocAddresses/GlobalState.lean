import Miri.Memory.NativeBuffer
import Miri.Memory.Identity
import Miri.Memory.Pointer
import Miri.Memory.AllocAddresses.AddressGenerator
import Miri.Memory.AllocAddresses.ReusePool

/-! A checked port of the non-host-specific state transitions in Miri's
`alloc_addresses/mod.rs`. Allocation metadata, liveness, host addresses,
borrow-tracker exposure, and cross-thread clock acquisition remain explicit
caller hooks. -/

namespace Miri.Memory.AllocAddresses

open Miri.ABI Miri.Memory Miri.Concurrency

inductive ProvenanceMode where
  | default
  | permissive
  | strict
  deriving DecidableEq, Repr

inductive AddressSpaceMode where
  | managed
  | nativeLib
  deriving DecidableEq, Repr

namespace AddressSpaceMode

def fromFlags (nativeLibEnabled : Bool) : AddressSpaceMode :=
  if nativeLibEnabled then .nativeLib else .managed

end AddressSpaceMode

instance : ToString AddressSpaceMode where
  toString
    | .managed => "managed"
    | .nativeLib => "native-lib"
inductive AllocationAddressKind where
  | liveData
  | typeId
  | dead
  deriving DecidableEq, Repr

structure AllocationAddressInfo where
  kind : AllocationAddressKind
  live : Bool
  size : Size
  align : Align
  memoryKind : Option AddressMemoryKind
  thread : AddressThreadId
  deriving Repr

structure AddressRandomChoices where
  /-- Outcome of the source address-reuse Bernoulli draw. -/
  reuse : Bool
  /-- Outcome of the cross-thread Bernoulli draw, consumed only after reuse. -/
  crossThread : Bool
  /-- Absolute pool index in the source `begin..end` random range. -/
  poolIndex : Nat
  /-- Slack outcome in the source `0..16` range for a fresh address. -/
  slack : Fin 16

structure AddressExternalHooks where
  /-- Native libraries supply physical addresses; absence remains an explicit capability requirement. -/
  externalAddress : Option UInt64 := none

structure BaseAddressEntry where
  allocId : AllocId
  address : UInt64
  deriving Repr

structure InverseAddressEntry where
  address : UInt64
  allocId : AllocId
  deriving Repr

structure AddressGenerationState where
  generator : AddressGenerator
  reusePool : ReusePool
  deriving Repr

structure GlobalAddressState where
  intToPtrMap : Array InverseAddressEntry := #[]
  baseAddr : Array BaseAddressEntry := #[]
  exposed : Array AllocId := #[]
  provenanceMode : ProvenanceMode
  addressMode : AddressSpaceMode
  generation : Option AddressGenerationState
  /-- Source native prepared_alloc_bytes, surviving global-memory snapshots. -/
  preparedNativeBytes : Array (AllocId × PreparedGlobalBytes) := #[]
  deriving Repr

inductive AddressStateError where
  | reusePool (error : ReusePoolError)
  | addressGenerator (error : AddressGeneratorError)
  | pointerArithmetic (error : PointerError)
  | missingBaseAddress (allocId : AllocId)
  | baseAddressAlreadyCached (allocId : AllocId) (address : UInt64)
  | missingInverseEntry (address : UInt64)
  | inverseEntryMismatch (address : UInt64) (expected actual : AllocId)
  | duplicateAddress (address : UInt64) (existingAllocId newAllocId : AllocId)
  | missingAddressGeneration
  | unexpectedAddressGeneration
  | missingAllocationInfo (allocId : AllocId)
  | missingMemoryKind (allocId : AllocId)
  | deadAllocation (allocId : AllocId)
  | strictAddressLookup
  | strictIntegerToPointerCast
  | missingAllocationSize (allocId : AllocId)
  | missingLivenessStatus (allocId : AllocId)
  | deadAllocationInAddressIndex (allocId : AllocId)
  | externalAddressHookRequired (mode : AddressSpaceMode)
  | borrowTrackerHookRequired (allocId : AllocId) (tag : BorTag)
  | borrowTrackerFailure (allocId : AllocId) (tag : BorTag) (message : String)
  | acquireClockFailure (address : UInt64) (clock : VClock) (message : String)
  | malformedInverseIndex (index length : Nat)
  deriving Repr

instance : ToString AddressStateError where
  toString
    | .reusePool error => toString error
    | .addressGenerator error => toString error
    | .pointerArithmetic error =>
        match error with
        | .sourceSizeError reason => toString reason
        | .unsignedConversionOverflow => "target pointer unsigned conversion overflow"
        | .signedConversionOverflow => "target pointer signed conversion overflow"
        | .relativeProvenanceHasNoAbsoluteAddress => "relative pointer provenance has no absolute address"
    | .missingBaseAddress id => s!"allocation {id.value} has no cached base address"
    | .baseAddressAlreadyCached id address =>
        s!"allocation {id.value} already has cached base address {address}"
    | .missingInverseEntry address => s!"address {address} has no inverse allocation entry"
    | .inverseEntryMismatch address expected actual =>
        s!"inverse address {address} maps to {actual.value}, expected {expected.value}"
    | .duplicateAddress address existing new =>
        s!"address {address} is already assigned to allocations {existing.value} and {new.value}"
    | .missingAddressGeneration => "managed allocation address generation is unavailable"
    | .unexpectedAddressGeneration => "external address mode unexpectedly has managed generation state"
    | .missingAllocationInfo id => s!"allocation metadata is required for allocation {id.value}"
    | .missingMemoryKind id =>
        s!"memory kind is required to assign an address to allocation {id.value}"
    | .deadAllocation id => s!"cannot assign an address to dead allocation {id.value}"
    | .strictAddressLookup => "integer-to-pointer lookup is disabled by strict provenance"
    | .strictIntegerToPointerCast => "integer-to-pointer cast is disabled by strict provenance"
    | .missingAllocationSize id => s!"allocation size is unavailable for allocation {id.value}"
    | .missingLivenessStatus id => s!"allocation liveness is unavailable for allocation {id.value}"
    | .deadAllocationInAddressIndex id =>
        s!"dead allocation {id.value} remains in the integer-to-pointer index"
    | .externalAddressHookRequired mode => s!"{mode} address hook must supply an address"
    | .borrowTrackerHookRequired id _ =>
        s!"borrow-tracker expose-tag hook is required for allocation {id.value}"
    | .borrowTrackerFailure id _ message =>
        s!"borrow-tracker expose-tag failed for allocation {id.value}: {message}"
    | .acquireClockFailure address _ message =>
        s!"clock acquire failed before using reused address {address}: {message}"
    | .malformedInverseIndex index length =>
        s!"inverse-address index {index} is outside {length} entries"

structure AddressStateResult (α : Type) where
  state : GlobalAddressState
  outcome : Except AddressStateError α

/-- A selected cross-thread reuse is not reported as immediately usable until
its synchronization hook has completed. -/
inductive AddressAssignment where
  | ready (address : UInt64)
  | acquireRequired (allocId : AllocId) (address : UInt64) (clock : VClock)
  deriving Repr

structure AddressLookupHooks where
  sizeOf : AllocId → Option Size
  isLive : AllocId → Option Bool

namespace GlobalAddressState

def new (provenanceMode : ProvenanceMode) (mode : AddressSpaceMode)
    (start stop : UInt64) (config : AddressReuseConfig) :
    Except AddressStateError GlobalAddressState := do
  let generation ←
    if mode == .managed then
      let pool ← (ReusePool.new config).mapError AddressStateError.reusePool
      pure (some ⟨AddressGenerator.new start stop, pool⟩)
    else pure none
  return ⟨#[], #[], #[], provenanceMode, mode, generation, #[]⟩

private def findBase (entries : Array BaseAddressEntry) (id : AllocId) : Option UInt64 :=
  (entries.find? fun entry => entry.allocId == id).map BaseAddressEntry.address

private def insertBase (entries : Array BaseAddressEntry) (id : AllocId)
    (address : UInt64) : Array BaseAddressEntry :=
  ((entries.filter fun entry => entry.allocId != id).push ⟨id, address⟩)

private def findInverseIndex (entries : Array InverseAddressEntry)
    (address : UInt64) : Nat × Bool := Id.run do
  let mut low := 0
  let mut high := entries.size
  let mut found : Option Nat := none
  while low < high && found.isNone do
    let middle := low + (high - low) / 2
    match entries[middle]? with
    | none => high := middle
    | some entry =>
        if entry.address < address then low := middle + 1
        else if address < entry.address then high := middle
        else found := some middle
  match found with
  | some index => return (index, true)
  | none => return (low, false)

/-- Cache first in `baseAddr`, then add the nonzero address to the sorted
inverse vector. A duplicate inverse address reports the source `unwrap_err`
failure after retaining the earlier base-map insertion. -/
def cacheAddress (state : GlobalAddressState) (id : AllocId)
    (address : UInt64) : AddressStateResult Unit := Id.run do
  if let some oldAddress := findBase state.baseAddr id then
    return ⟨state, .error (.baseAddressAlreadyCached id oldAddress)⟩
  let withBase := { state with baseAddr := insertBase state.baseAddr id address }
  if address == 0 then return ⟨withBase, .ok ()⟩
  let (position, found) := findInverseIndex state.intToPtrMap address
  if found then
    match state.intToPtrMap[position]? with
    | some old => return ⟨withBase, .error (.duplicateAddress address old.allocId id)⟩
    | none => return ⟨withBase, .error (.malformedInverseIndex position state.intToPtrMap.size)⟩
  if h : position ≤ state.intToPtrMap.size then
    let inserted := state.intToPtrMap.insertIdx position ⟨address, id⟩ h
    return ⟨{ withBase with intToPtrMap := inserted }, .ok ()⟩
  else
    return ⟨withBase, .error (.malformedInverseIndex position state.intToPtrMap.size)⟩

private def setGeneration (state : GlobalAddressState)
    (generation : AddressGenerationState) : GlobalAddressState :=
  { state with generation := some generation }

/-- The cached fast path precedes allocation-info and random-choice requirements.
Managed choices remain explicit; native addresses require external hooks. -/
def addrFromAllocId (state : GlobalAddressState) (id : AllocId)
    (info? : Option AllocationAddressInfo) (choices : AddressRandomChoices)
    (hooks : AddressExternalHooks := {}) : AddressStateResult AddressAssignment := Id.run do
  if let some address := findBase state.baseAddr id then
    return ⟨state, .ok (.ready address)⟩
  let some info := info?
    | return ⟨state, .error (.missingAllocationInfo id)⟩
  /- The source `addr_from_alloc_id` requires `memory_kind` in its outer
  uncached branch before calling `addr_from_alloc_id_uncached`. That branch
  also applies to `TypeId`, whose resulting address is always zero. -/
  let some memoryKind := info.memoryKind
    | return ⟨state, .error (.missingMemoryKind id)⟩
  if info.kind == .dead || !info.live then
    return ⟨state, .error (.deadAllocation id)⟩
  if info.kind == .typeId then
    let cached := state.cacheAddress id 0
    match cached.outcome with
    | .ok _ => return ⟨cached.state, .ok (.ready 0)⟩
    | .error error => return ⟨cached.state, .error error⟩
  match state.addressMode with
  | .nativeLib =>
      let some address := hooks.externalAddress
        | return ⟨state, .error (.externalAddressHookRequired state.addressMode)⟩
      let cached := state.cacheAddress id address
      match cached.outcome with
      | .ok _ => return ⟨cached.state, .ok (.ready address)⟩
      | .error error => return ⟨cached.state, .error error⟩
  | .managed =>
      let some generation := state.generation
        | return ⟨state, .error .missingAddressGeneration⟩
      let taken := generation.reusePool.takeAddr choices.reuse choices.crossThread
          choices.poolIndex info.size info.align memoryKind info.thread
      let nextGeneration := { generation with reusePool := taken.state }
      let afterTake := state.setGeneration nextGeneration
      match taken.outcome with
      | .error error =>
          return ⟨afterTake, .error (.reusePool error)⟩
      | .ok (some reused) =>
          match reused.clockToAcquire with
          | some clock => return ⟨afterTake, .ok (.acquireRequired id reused.address clock)⟩
          | none =>
              let cached := afterTake.cacheAddress id reused.address
              match cached.outcome with
              | .ok _ => return ⟨cached.state, .ok (.ready reused.address)⟩
              | .error error => return ⟨cached.state, .error error⟩
      | .ok none =>
          let generated := generation.generator.generate info.size info.align choices.slack
          let generatedGeneration := { nextGeneration with generator := generated.state }
          let afterGenerate := state.setGeneration generatedGeneration
          match generated.outcome with
          | .error error => return ⟨afterGenerate, .error (.addressGenerator error)⟩
          | .ok address =>
              let remaining := generated.state.getRemaining
              let updatedPool := if remaining.start > remaining.stop / 2 then
                  generatedGeneration.reusePool.addressSpaceShortage
                else generatedGeneration.reusePool
              let readyState := afterGenerate.setGeneration
                  { generatedGeneration with reusePool := updatedPool }
              let cached := readyState.cacheAddress id address
              match cached.outcome with
              | .ok _ => return ⟨cached.state, .ok (.ready address)⟩
              | .error error => return ⟨cached.state, .error error⟩

/-- Complete a cross-thread reuse after the caller has acquired the returned
clock. The address is cached only after successful acquisition, matching the
source's `?` before `interp_ok`. -/
def completeAcquire (pending : AddressStateResult AddressAssignment)
    (clockResult : Except String Unit) : AddressStateResult AddressAssignment :=
  match pending.outcome with
  | .error _ => pending
  | .ok (.ready _) => pending
  | .ok (.acquireRequired id address clock) =>
      match clockResult with
      | .error message =>
          ⟨pending.state, .error (.acquireClockFailure address clock message)⟩
      | .ok () =>
          let cached := pending.state.cacheAddress id address
          match cached.outcome with
          | .ok _ => ⟨cached.state, .ok (.ready address)⟩
          | .error error => ⟨cached.state, .error error⟩

/-- Binary search in the source's address-sorted inverse map. -/
private def inverseSearch (entries : Array InverseAddressEntry)
    (address : UInt64) : Nat × Bool := findInverseIndex entries address

/-- Source `alloc_id_from_addr`, with allocation-size and liveness lookups as
explicit caller hooks. Negative accesses search from `addr.saturating_sub(1)`.
Only addresses in exposed allocations produce wildcard provenance. -/
def allocIdFromAddr (state : GlobalAddressState) (address : UInt64)
    (size : Int64) (hooks : AddressLookupHooks) :
    Except AddressStateError (Option AllocId) := do
  if state.provenanceMode == .strict then throw .strictAddressLookup
  let searchAddress := if size.toInt < 0 then
      if address == 0 then 0 else address - 1
    else address
  let (position, found) := inverseSearch state.intToPtrMap searchAddress
  let candidate ←
    if found then
      match state.intToPtrMap[position]? with
      | some entry => pure (some entry.allocId)
      | none => throw (.malformedInverseIndex position state.intToPtrMap.size)
    else if position == 0 then pure none
    else
      match state.intToPtrMap[position - 1]? with
      | none => throw (.malformedInverseIndex (position - 1) state.intToPtrMap.size)
      | some entry =>
          let offset := searchAddress - entry.address
          let some allocationSize := hooks.sizeOf entry.allocId
            | throw (.missingAllocationSize entry.allocId)
          if offset < allocationSize.bytes then pure (some entry.allocId) else pure none
  let some id := candidate | return none
  if !state.exposed.contains id then return none
  match hooks.isLive id with
  | none => throw (.missingLivenessStatus id)
  | some false => throw (.deadAllocationInAddressIndex id)
  | some true => return some id

/-- Source `expose_provenance`. If borrow tracking is enabled, insertion into
the exposed set precedes the explicit tracker hook result. -/
def exposeProvenance (state : GlobalAddressState) (provenance : Provenance)
    (allocationLive? : Option Bool) (borrowTrackerEnabled : Bool)
    (tagHook? : Option (Except String Unit)) : AddressStateResult Unit := Id.run do
  match provenance with
  | .wildcard => return ⟨state, .ok ()⟩
  | .concrete id tag =>
      if state.provenanceMode == .strict then return ⟨state, .ok ()⟩
      match allocationLive? with
      | none => return ⟨state, .error (.missingLivenessStatus id)⟩
      | some false => return ⟨state, .ok ()⟩
      | some true =>
          let exposed := if state.exposed.contains id then state.exposed
            else state.exposed.push id
          let nextState := { state with exposed }
          if !borrowTrackerEnabled then return ⟨nextState, .ok ()⟩
          match tagHook? with
          | none => return ⟨nextState, .error (.borrowTrackerHookRequired id tag)⟩
          | some (.error message) =>
              return ⟨nextState, .error (.borrowTrackerFailure id tag message)⟩
          | some (.ok ()) => return ⟨nextState, .ok ()⟩

/-- Source `ptr_from_addr_cast`: default mode retains wildcard provenance and
reports the source warning as metadata; strict mode returns the explicit stop. -/
def ptrFromAddrCast (state : GlobalAddressState) (address : UInt64)
    (firstAtSourceLocation : Bool) :
    AddressStateResult (Pointer (Option Provenance) × Bool) :=
  match state.provenanceMode with
  | .strict => ⟨state, .error .strictIntegerToPointerCast⟩
  | .default =>
      ⟨state, .ok (Pointer.new (some .wildcard) (Size.ofBytes address), firstAtSourceLocation)⟩
  | .permissive =>
      ⟨state, .ok (Pointer.new (some .wildcard) (Size.ofBytes address), false)⟩

def exposedAllocations (state : GlobalAddressState) : Array AllocId := state.exposed

/-- The source GC hook only removes entries from the cached id-to-base map.
The inverse map and exposed set are already cleared by free. -/
def removeUnreachableAllocs (state : GlobalAddressState) (liveIds : Array AllocId) :
    GlobalAddressState :=
  { state with baseAddr := state.baseAddr.filter fun entry => liveIds.contains entry.allocId }

/-- Source `ptr_get_alloc`. This returns a concrete allocation directly or
resolves wildcard provenance through the exposed inverse map; validity and
allocation bounds are checked by later memory hooks. -/
def ptrGetAlloc (state : GlobalAddressState) (pointer : Pointer Provenance)
    (accessSize : Int64) (hooks : AddressLookupHooks) (cx : PointerArithmetic) :
    Except AddressStateError (Option (AllocId × Size)) := do
  let allocId ← match pointer.provenance with
    | .concrete id _ => pure (some id)
    | .wildcard => state.allocIdFromAddr pointer.offset.bytes accessSize hooks
  let some allocId := allocId | return none
  let some baseAddress := findBase state.baseAddr allocId
    | throw (.missingBaseAddress allocId)
  let relative := pointer.offset.bytes - baseAddress
  let relative ← (cx.truncateToTargetUsize relative).mapError AddressStateError.pointerArithmetic
  return some (allocId, Size.ofBytes relative)

/-- Source `free_alloc_id`: remove inverse/exposed membership while retaining
the base cache, then offer the freed range to the reuse pool. -/
def freeAllocId (state : GlobalAddressState) (id : AllocId) (size : Size)
    (align : Align) (kind : AddressMemoryKind) (thread : AddressThreadId)
    (reuseChoice : Bool) (clock : Unit → VClock) : AddressStateResult Unit := Id.run do
  let some address := findBase state.baseAddr id
    | return ⟨state, .error (.missingBaseAddress id)⟩
  let (position, found) := findInverseIndex state.intToPtrMap address
  if !found then return ⟨state, .error (.missingInverseEntry address)⟩
  if hpos : position < state.intToPtrMap.size then
    let inverseEntry := state.intToPtrMap[position]
    let afterRemove := { state with
      intToPtrMap := state.intToPtrMap.eraseIdx position hpos
      exposed := state.exposed.filter fun allocId => allocId != id }
    if inverseEntry.allocId != id then
      return ⟨afterRemove, .error (.inverseEntryMismatch address id inverseEntry.allocId)⟩
    match state.generation with
    | none => return ⟨afterRemove, .ok ()⟩
    | some generation =>
      let added := generation.reusePool.addAddr reuseChoice address size align kind thread clock
      let nextGeneration := { generation with reusePool := added.state }
      let nextState := afterRemove.setGeneration nextGeneration
      match added.outcome with
      | .ok _ => return ⟨nextState, .ok ()⟩
      | .error error => return ⟨nextState, .error (.reusePool error)⟩
  else
    return ⟨state, .error (.malformedInverseIndex position state.intToPtrMap.size)⟩

/-- Proof interface to the existing inverse-search consumer, exact base case. -/
theorem allocation_base_zero (state : GlobalAddressState) (address : UInt64) (id : AllocId)
    (hooks : AddressLookupHooks) (position : Nat)
    (mode : state.provenanceMode ≠ .strict)
    (search : findInverseIndex state.intToPtrMap address = (position,true))
    (row : state.intToPtrMap[position]? = some ⟨address,id⟩)
    (exposed : state.exposed.contains id = true) (live : hooks.isLive id = some true) :
    state.allocIdFromAddr address 0 hooks = .ok (some id) := by
  have member : id ∈ state.exposed := by simpa using exposed
  simp [allocIdFromAddr,inverseSearch,search,mode,row,member,live,
    bind,Bind.bind,Except.bind,pure,Pure.pure,Except.pure]

/-- Proof interface to the existing inverse-search consumer, interior case. -/
theorem allocation_interior_zero (state : GlobalAddressState) (address base : UInt64) (id : AllocId)
    (hooks : AddressLookupHooks) (size : Size) (position : Nat)
    (mode : state.provenanceMode ≠ .strict)
    (search : findInverseIndex state.intToPtrMap address = (position+1,false))
    (row : state.intToPtrMap[position]? = some ⟨base,id⟩)
    (known : hooks.sizeOf id = some size) (inside : address-base < size.bytes)
    (exposed : state.exposed.contains id = true) (live : hooks.isLive id = some true) :
    state.allocIdFromAddr address 0 hooks = .ok (some id) := by
  have member : id ∈ state.exposed := by simpa using exposed
  simp [allocIdFromAddr,inverseSearch,search,mode,row,known,inside,member,live,
    bind,Bind.bind,Except.bind,pure,Pure.pure,Except.pure]

/-- The selected allocation and a current base cache complete ptr_get_alloc. -/
theorem pointer_from_selection (state : GlobalAddressState) (pointer : Pointer Provenance)
    (count : Int64) (hooks : AddressLookupHooks) (arithmetic : PointerArithmetic)
    (id : AllocId) (base relative : UInt64)
    (selected : (match pointer.provenance with
      | .concrete id _ => (Except.ok (some id) : Except AddressStateError (Option AllocId))
      | .wildcard => state.allocIdFromAddr pointer.offset.bytes count hooks) = .ok (some id))
    (cached : state.baseAddr.find? (fun row => row.allocId == id) = some ⟨id,base⟩)
    (truncated : arithmetic.truncateToTargetUsize (pointer.offset.bytes-base) = .ok relative) :
    state.ptrGetAlloc pointer count hooks arithmetic = .ok (some (id,Size.ofBytes relative)) := by
  cases kind : pointer.provenance with
  | concrete supplied tag =>
    have same : supplied = id := by simpa only [kind,Except.ok.injEq,Option.some.injEq] using selected
    subst supplied
    simp [ptrGetAlloc,kind,findBase,cached,truncated,Except.mapError,bind,Bind.bind,Except.bind,pure,Pure.pure,Except.pure]
  | wildcard =>
    have chosen : state.allocIdFromAddr pointer.offset.bytes count hooks = .ok (some id) := by simpa only [kind] using selected
    simp [ptrGetAlloc,kind,chosen,findBase,cached,truncated,Except.mapError,bind,Bind.bind,Except.bind,pure,Pure.pure,Except.pure]

end GlobalAddressState

end Miri.Memory.AllocAddresses
