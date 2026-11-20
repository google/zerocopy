import Miri.Interpreter.MiriShims
import Miri.Interpreter.RawMemoryMachine
import Miri.Interpreter.TypedMachineBindings

/-! Concrete machine bindings for the Miri-only extern driver. The user-state
lens must target the same static/tracked allocation lists as machine exit.
Pointers, symbolic alignment, payloads, threads and GC use their canonical state.
-/
namespace Miri.Interpreter.MiriShimMachine
open Miri.ABI Miri.Memory Miri.MIR Miri.Concurrency
abbrev State := PointerMachine.State
abbrev M := PointerMachine.M

structure Bookkeeping where
  trackedAllocations : Array AllocId
  staticRoots : Array AllocId

structure Hooks (K U C E Other : Type) where
  access : PlaceMachine.AccessConfig K (PointerMachine.User U)
  pointer : PointerMachine.Hooks K U
  place : PlaceHooks Provenance (State K U) C E
  bookkeeping : U → Bookkeeping
  setBookkeeping : Bookkeeping → U → U
  cAllocation : MemoryKind K → Bool
  u64Layout : C → M K U LocalLayout
  boolLayout : C → M K U LocalLayout
  usizeLayout : C → M K U LocalLayout
  unwind : Unwind.Hooks K (PointerMachine.User U) C Other
  gc : ProvenanceGC.Hooks K (PointerMachine.User U)

private def lift (value : Except StepError A) : M K U A :=
  match value with | .ok value => pure value | .error error => throw error

private def readScalar [DecidableEq K] (h : Hooks K U C E Other) (op : OpTy Provenance) : M K U (Scalar Provenance) := do
  let immediate ← PlaceMachine.readImmediate h.access op
  lift (immediate.imm.toScalar.mapError ScalarOps.immediateError)

private def writeScalar (h : Hooks K U C E Other) (choice : C) (layout : LocalLayout)
    (value : Scalar Provenance) (dest : RuntimePlace Provenance) : M K U Unit := do
  unless dest.layout == layout do throw (.invalidProgram "Miri shim result compiler layout mismatch")
  writePlaceImmediate h.place choice (.scalar value) dest

/-- Source failed ptr_get_alloc_id is a value until the calling arm applies its
error policy. This conversion retains all effects from pointer resolution. -/
def allocation (h : Hooks K U C E Other) (pointer : Pointer (Option Provenance)) :
    M K U (Except StepError (AllocId × Size)) := fun state =>
  match pointer.provenance with
  | none => .ok (.error (.undefinedBehavior "pointer has no allocation provenance")) state
  | some provenance =>
    match PointerMachine.ptrGetAlloc h.pointer (Pointer.new provenance pointer.offset) 0 state with
    | .error error state => .ok (.error error) state
    | .ok none state => .ok (.error (.undefinedBehavior "pointer does not resolve to an allocation")) state
    | .ok (some location) state => .ok (.ok location) state

private def allocationInfo (id : AllocId) : M K U (Size × Align × AllocationKind) := do
  match (← get).machine.memory.getAllocInfo id with
  | .ok info => return (info.size,info.align,info.kind)
  | .error error => throw (.invalidProgram s!"Miri shim allocation metadata: {reprStr error}")

private def track (h : Hooks K U C E Other) (id : AllocId) : M K U Bool := do
  let user := (← get).machine.user.payload
  let bookkeeping := h.bookkeeping user
  if bookkeeping.trackedAllocations.contains id then return false
  let payload := h.setBookkeeping { bookkeeping with trackedAllocations := bookkeeping.trackedAllocations.push id } user
  modify fun state => { state with machine := { state.machine with user := { state.machine.user with payload } } }
  return true

private def staticRoot (h : Hooks K U C E Other) (id : AllocId) : M K U Unit := do
  let user := (← get).machine.user.payload
  let bookkeeping := h.bookkeeping user
  let payload := h.setBookkeeping { bookkeeping with staticRoots := bookkeeping.staticRoots.push id } user
  modify fun state => { state with machine := { state.machine with user := { state.machine.user with payload } } }

/-- No allocation/liveness check is imposed here: source promises are recorded
for any resolved provenance, including dead allocations, using actual offset. -/
def symbolicPromise (h : Hooks K U C E Other) (pointer : Pointer (Option Provenance))
    (alignment : Align) : M K U Unit := do
  let location ← allocation h pointer
  let (id,offset) ← match location with
    | .ok location => pure location
    | .error (.undefinedBehavior _) => return ()
    | .error error => throw error
  let (_,native,_) ← allocationInfo id
  if alignment.pow2 > native.pow2 then
    let promises := (← get).machine.user.symbolicAlignment
    let old := promises.find? (·.1 == id)
    if old.isNone || old.any (fun entry => alignment.pow2 > entry.2.2.pow2) then
      let promises := (promises.filter (·.1 != id)).push (id,offset,alignment)
      modify fun state => { state with machine := { state.machine with user :=
        { state.machine.user with symbolicAlignment := promises } } }

/-- Construct the source Miri operations over the canonical machine while
keeping host paths, diagnostics, output, and other source effects explicit.
This constructor accepts the nonrecursive CoreHooks projection, so callers do
not need to manufacture a complete ForeignItems dispatch record just to bind
the physical memory/provenance/thread effects. -/
def core [DecidableEq K] (h : Hooks K U C E Other) (choice : C)
    (base : MiriShims.CoreHooks Provenance (State K U) D (RuntimePlace Provenance) B I HostPath) :
    MiriShims.CoreHooks Provenance (State K U) D (RuntimePlace Provenance) B I HostPath :=
  { base with
    readU64 := fun op => do lift ((← readScalar h op).toUInt64.mapError ScalarOps.scalarError)
    readU8 := fun op => do lift ((← readScalar h op).toUInt8.mapError ScalarOps.scalarError)
    readBool := fun op => do lift ((← readScalar h op).toBool.mapError ScalarOps.scalarError)
    readImmediate := PlaceMachine.readImmediate h.access
    readByteSlice := fun value => do
      let (pointer,length) ← lift (value.imm.toScalarPair.mapError ScalarOps.immediateError)
      let pointer ← lift (pointer.toPointer h.access.runtime.base |>.mapError ScalarOps.scalarError)
      let length ← lift (length.toTargetUsize h.pointer.arithmetic.pointerSize |>.mapError ScalarOps.scalarError)
      RawMemoryMachine.readBytes h.access h.pointer.arithmetic pointer length
    writeU64 := fun value dest => do
      let layout ← h.u64Layout choice
      unless layout.layout.isSized && layout.layout.size.bytes == 8 do
        throw (.invalidProgram "Miri shim u64 compiler layout")
      let scalar ← lift (Scalar.fromUInt (BitVec.ofNat 128 value.toNat) layout.layout.size |>.mapError ScalarOps.scalarError)
      writeScalar h choice layout scalar dest
    writeUsize := fun value dest => do
      let layout ← h.usizeLayout choice
      unless layout.layout.isSized && layout.layout.size == h.access.runtime.pointerOffset do
        throw (.invalidProgram "Miri shim usize compiler layout")
      -- rustc Scalar::from_target_usize uses the target pointer offset width.
      let scalar ← lift (Scalar.fromUInt (BitVec.ofNat 128 value.toNat) h.access.runtime.pointerOffset |>.mapError ScalarOps.scalarError)
      writeScalar h choice layout scalar dest
    writeBool := fun value dest => do
      let layout ← h.boolLayout choice
      unless layout.layout.isSized && layout.layout.size.bytes == 1 do
        throw (.invalidProgram "Miri shim bool compiler layout")
      writeScalar h choice layout (Scalar.fromBool value) dest
    allocation := allocation h
    allocationInfo := allocationInfo
    localCAllocation := fun id => do
      let entry := (← get).machine.memory.live.find? (·.1 == id)
      return entry.any (fun (_,entry) => h.cAllocation entry.kind)
    trackAllocation := track h
    staticRoot := staticRoot h
    startUnwind := Unwind.handleStartUnwind h.unwind choice
    provenanceGc := ProvenanceGC.run h.gc
    threadFromUsize := fun value => do
      match ThreadId.ofNat value.toNat with
      | .error _ => return none
      | .ok id => return if ((← get).machine.threads.thread? id).isSome then some id else none
    yieldThread := modify fun state => { state with machine := { state.machine with threads := state.machine.threads.yield } }
    symbolicPromise := symbolicPromise h }

/-- ABI, host paths, actual thread creation/join and diagnostic ancestry remain
required until their source dictionaries are installed. No success defaults. -/
def bind [DecidableEq K] (h : Hooks K U C E Other) (choice : C)
    (base : MiriShims.Hooks Provenance (State K U) D (RuntimePlace Provenance) B I HostPath) :
    MiriShims.Hooks Provenance (State K U) D (RuntimePlace Provenance) B I HostPath :=
  let bound := core h choice base.core
  { base with toOperations := bound.toOperations }

end Miri.Interpreter.MiriShimMachine
