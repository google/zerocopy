import Miri.Interpreter.MachineHooks
import Miri.Memory.AllocAddresses

/-! Stateful bindings of pinned `miri/src/alloc_addresses/mod.rs` to the
canonical interpreter machine. Random outcomes are inputs, never fixed seeds.
Native allocation and compiler-global materialization are external effects. -/
namespace Miri.Interpreter.PointerMachine
open Miri.ABI Miri.Memory Miri.Memory.AllocAddresses

structure User (U : Type) where
  addresses : GlobalAddressState
  payload : U
  symbolicAlignment : Array (AllocId × Size × Align) := #[]

abbrev State (K U : Type) := MachineHooks.State K (User U)
abbrev M (K U A : Type) := MachineHooks.M K (User U) A

structure Hooks (K U : Type) where
  arithmetic : PointerArithmetic
  externalAddress : AllocId → AllocationAddressInfo → M K U UInt64
  /-- Compiler globals may require allocation before Tree Borrows has an extra. -/
  ensureTreeExtra : AllocId → M K U Unit
  diagnosticIntToPtr : M K U Unit
  /-- Strict provenance is a machine termination, not Rust UB. -/
  strictIntToPtr : StepError
  classifyAddressError : AddressStateError → StepError

private def addresses : M K U GlobalAddressState := do
  return (← get).machine.user.addresses

private def setAddresses (value : GlobalAddressState) : M K U Unit :=
  modify fun state => { state with machine := { state.machine with user :=
    { state.machine.user with addresses := value } } }

private def finish (h : Hooks K U) (result : AddressStateResult A) : M K U A := do
  setAddresses result.state
  match result.outcome with
  | .ok value => return value
  | .error error => throw (h.classifyAddressError error)

/-- The cached path performs no metadata lookup, thread lookup or external call. -/
def addrFromAllocId (h : Hooks K U) (id : AllocId)
    (kind : Option AddressMemoryKind) (choice : AddressRandomChoices) : M K U UInt64 := do
  let state ← addresses
  if let some cached := state.baseAddr.find? (fun entry => entry.allocId == id) then
    return cached.address
  let some kind := kind | throw (h.classifyAddressError (.missingMemoryKind id))
  let memory := (← get).machine.memory
  let info ← match memory.getAllocInfo id with
    | .ok info => pure info
    | .error error => throw (.callback s!"address allocation metadata: {reprStr error}")
  let info : AllocationAddressInfo := {
    kind := if info.kind == .dead then .dead else if info.kind == .typeId then .typeId else .liveData
    live := memory.isAllocLive id
    size := info.size, align := info.align, memoryKind := some kind
    thread := UInt32.ofNat (← get).machine.threads.activeThread.toNat }
  let external ← if state.addressMode != .managed && info.kind != .typeId && info.live then
      pure (some (← h.externalAddress id info)) else pure none
  -- Native address acquisition may install prepared backing in this same
  -- source address state. Cache against the updated state, retaining ownership.
  let current ← addresses
  let result := current.addrFromAllocId id (some info) choice ⟨external⟩
  let assignment ← finish h result
  match assignment with
  | .ready address => return address
  | .acquireRequired id address clock =>
    let machine := (← get).machine
    if let some global := machine.dataRace then
      match global.acquireClock machine.threads clock with
      | .error error => throw (.callback s!"address reuse clock acquisition: {reprStr error}")
      | .ok global => modify fun state => { state with machine := { state.machine with dataRace := some global } }
    let cached ← addresses
    finish h (cached.cacheAddress id address)
    return address

/-- Exposure commits set membership before materializing globals or mutating TB.
All per-range tree mutations are retained even when exposure fails. -/
def exposeProvenance [DecidableEq K] (h : Hooks K U) (provenance : Provenance) : M K U Unit := do
  let .concrete id tag := provenance | return ()
  let state ← addresses
  if state.provenanceMode == .strict then return ()
  if !(← get).machine.memory.isAllocLive id then return ()
  finish h (state.exposeProvenance provenance (some true) false none)
  if (← get).machine.borrowTracker.isSome then
    let info ← match (← get).machine.memory.getAllocInfo id with
      | .ok info => pure info
      | .error error => throw (.callback s!"exposed allocation metadata: {reprStr error}")
    if info.kind != .liveData then return ()
    h.ensureTreeExtra id
    let machine := (← get).machine
    let some tracker := machine.borrowTracker
      | throw (.invalidProgram "borrow tracker removed during exposure")
    let some entry := machine.memory.live.find? (fun entry => entry.1 == id)
      | throw (.invalidProgram "exposed allocation has no Tree Borrows extra")
    let result := entry.2.allocation.extra.exposeTag tracker.global.protectedTags tag
    let memory ← match machine.memory.setLiveAllocation id (entry.2.allocation.setExtra result.tree) with
      | .ok memory => pure memory
      | .error error => throw (.invalidProgram s!"exposure tree update: {reprStr error}")
    modify fun state => { state with machine := { state.machine with memory } }
    match result.outcome with
    | .ok () => pure ()
    | .error error => throw (.invalidProgram s!"Tree Borrows exposure invariant: {reprStr error}")

/-- Integer casts create wildcard provenance without allocation resolution. -/
def pointerFromExposedAddress (h : Hooks K U) (address : UInt64) :
    M K U (Pointer (Option Provenance)) := do
  let state ← addresses
  match state.provenanceMode with
  | .strict => throw h.strictIntToPtr
  | .default => h.diagnosticIntToPtr
  | .permissive => pure ()
  return Pointer.new (some .wildcard) (Size.ofBytes address)

/-- Allocation resolution uses actual canonical memory liveness and sizes;
dead concrete provenance is intentionally returned for later UAF checking. -/
def ptrGetAlloc (h : Hooks K U) (pointer : Pointer Provenance) (size : Int64) :
    M K U (Option (AllocId × Size)) := do
  let memory := (← get).machine.memory
  let lookup : AddressLookupHooks := {
    sizeOf := fun id => (memory.getAllocInfo id).toOption.map (·.size)
    isLive := fun id => some (memory.isAllocLive id) }
  match (← addresses).ptrGetAlloc pointer size lookup h.arithmetic with
  | .ok value => return value
  | .error error => throw (h.classifyAddressError error)

/-- Relative compiler root pointers become absolute without losing identity/tag. -/
def adjustAllocRootPointer (h : Hooks K U) (id : AllocId) (tag : BorTag)
    (offset : Size) (kind : AddressMemoryKind) (choice : AddressRandomChoices) :
    M K U (Pointer Provenance) := do
  let base ← addrFromAllocId h id (some kind) choice
  let pointer := Pointer.new (Provenance.concrete id tag) (Size.ofBytes base)
  match pointer.wrappingOffset offset h.arithmetic with
  | .ok pointer => return pointer
  | .error error => throw (h.classifyAddressError (.pointerArithmetic error))

/-- Source removal precedes pool choice, clock release and pool insertion.
The old vector clock is stored while the canonical active clock increments. -/
def freeAllocId (h : Hooks K U) (id : AllocId) (size : Size) (align : Align)
    (kind : AddressMemoryKind) (choice : Bool) : M K U Unit := do
  let initial ← addresses
  let base := (initial.baseAddr.find? fun entry => entry.allocId == id).map (·.address)
  let removed := { initial with generation := none }.freeAllocId id size align kind 0 false
    (fun _ => Miri.Concurrency.VClock.default)
  let removedState := match removed.outcome with
    | .error (.inverseEntryMismatch ..) => { removed.state with exposed := initial.exposed }
    | _ => removed.state
  setAddresses { removedState with generation := initial.generation }
  match removed.outcome with
  | .error error => throw (h.classifyAddressError error)
  | .ok () => pure ()
  let some generation := initial.generation | return ()
  let some base := base | throw (.invalidProgram "free address lost base cache")
  let machine := (← get).machine
  let snapshot ← if kind != .stack && choice &&
      ReusePool.bernoulliChoiceAllowed generation.reusePool.addressReuseRate choice then do
    match machine.dataRace with
    | none => pure Miri.Concurrency.VClock.default
    | some global =>
      match global.releaseClock machine.threads with
      | .error error => throw (.callback s!"free address release clock: {reprStr error}")
      | .ok (global, snapshot) =>
        modify fun state => { state with machine := { state.machine with dataRace := some global } }
        pure snapshot
    else pure Miri.Concurrency.VClock.default
  let result := generation.reusePool.addAddr choice base size align kind
    (UInt32.ofNat machine.threads.activeThread.toNat) (fun _ => snapshot)
  let current ← addresses
  setAddresses { current with generation := some { generation with reusePool := result.state } }
  match result.outcome with
  | .ok () => pure ()
  | .error error => throw (h.classifyAddressError (.reusePool error))

/-- Source GC only drops id-to-base entries after the collector has proved
unreachability; inverse/exposed entries are removed by deallocation. -/
def removeUnreachableAllocs (live : Array AllocId) : M K U Unit := do
  setAddresses ((← addresses).removeUnreachableAllocs live)

/-- Native memory ownership and native call trampolines cannot be represented
by synthetic addresses. The external provider must consume prepared bytes,
check host alignment/length, and copy the supplied contents in source order. -/
structure GlobalBytesHooks (K U : Type) where
  nativeEnabled : Bool
  nativePreparedBytes : AllocId → Array UInt8 → Align → M K U (Array UInt8)

def getGlobalAllocBytes (h : Hooks K U) (bytesHooks : GlobalBytesHooks K U)
    (id : AllocId) (bytes : Array UInt8) (align : Align)
    (choice : AddressRandomChoices) : M K U (Array UInt8) := do
  unless ((← get).machine.memory.findGlobal? id).isSome do
    throw (.invalidProgram "get_global_alloc_bytes requires a compiler global")
  if bytesHooks.nativeEnabled then
    let _ ← addrFromAllocId h id (some .other) choice
    bytesHooks.nativePreparedBytes id bytes align
  else

    return bytes

/-- Source symbolic alignment override. Non-live and non-symbolic cases defer
only the ordinary concrete alignment check to the existing memory engine. -/
def symbolicAlignment (symbolic : Bool) (kind : AllocationKind)
    (allocationAlign : Align) (promise : Option (Size × Align))
    (offset : Size) (required : Align) : Except AlignError (Option Misalignment) := do
  if !symbolic || kind != .liveData then return none
  let (promisedOffset, promisedAlign) := promise.getD (Size.ZERO, allocationAlign)
  if promisedAlign.pow2 < required.pow2 then return some ⟨promisedAlign, required⟩
  let distance := offset.bytes - promisedOffset.bytes
  let bytes ← required.bytes
  if distance % bytes == 0 then return none
  let actual := Align.maxAlignedFactor (Size.ofBytes distance)
  -- A failing distance has fewer trailing zeroes than the required alignment.
  let _ ← actual.bytes
  return some ⟨actual, required⟩

end Miri.Interpreter.PointerMachine
