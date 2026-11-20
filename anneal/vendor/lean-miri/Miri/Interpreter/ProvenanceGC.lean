import Miri.Interpreter.PointerMachine
import Miri.Interpreter.ThreadStacks
import Miri.Interpreter.Unwind
import Miri.Concurrency.WeakMemory

/-! Source provenance_gc.rs, machine.rs::VisitProvenance, thread.rs frame
visitors. This collects provenance as ghost data: it performs no Rust memory
read, initialization check, race access or retag. Missing user-state visitors
remain required operations; arbitrary empty roots are not a closed interpreter.
-/
namespace Miri.Interpreter.ProvenanceGC
open Miri.ABI Miri.Memory Miri.MIR Miri.Concurrency
open MachineHooks (M)

structure Roots where
  allocations : Array AllocId := #[]
  tags : Array BorTag := #[]

namespace Roots

def add (roots : Roots) (id : Option AllocId) (tag : Option BorTag) : Roots :=
  { allocations := match id with
      | some id => if roots.allocations.contains id then roots.allocations else roots.allocations.push id
      | none => roots.allocations
    tags := match tag with
      | some tag => if roots.tags.contains tag then roots.tags else roots.tags.push tag
      | none => roots.tags }

def provenance (roots : Roots) : Provenance → Roots
  | .concrete id tag => roots.add (some id) (some tag)
  | .wildcard => roots

def pointer (roots : Roots) (pointer : Pointer (Option Provenance)) : Roots :=
  match pointer.provenance with | none => roots | some value => roots.provenance value

def strictPointer (roots : Roots) (pointer : Pointer Provenance) : Roots :=
  roots.provenance pointer.provenance

def scalar (roots : Roots) (value : Scalar Provenance) : Except StepError Roots := do
  match ← (value.toBitsOrPtrInternal value.size).mapError (fun error =>
      StepError.invalidProgram s!"GC scalar representation: {reprStr error}") with
  | .bits _ => return roots
  | .pointer pointer => return roots.strictPointer pointer

def immediate (roots : Roots) : Immediate Provenance → Except StepError Roots
  | .scalar value => roots.scalar value
  | .scalarPair first second => do return ← (← roots.scalar first).scalar second
  | .uninit => .ok roots

def metadata (roots : Roots) : MemPlaceMeta Provenance → Except StepError Roots
  | .metadata value => roots.scalar value
  | .none => .ok roots

def memPlace (roots : Roots) (place : MemPlace Provenance) : Except StepError Roots :=
  (roots.pointer place.ptr).metadata place.metadata

def operand (roots : Roots) : Operand Provenance → Except StepError Roots
  | .immediate value => roots.immediate value
  | .indirect place => roots.memPlace place

def runtimePlace (roots : Roots) (place : RuntimeStackPlace Provenance) : Except StepError Roots :=
  match place with
  | .memory value => roots.memPlace value.mplace
  | .frameLocal .. => .ok roots

def frame (roots : Roots) (frame : Frame Provenance LocalLayout MachineHooks.FrameExtra) :
    Except StepError Roots := do
  let mut roots ← roots.runtimePlace frame.returnPlace
  for entry in frame.locals do
    if let .live value := entry.value then roots ← roots.operand value
  -- Source does not separately visit va_list or track_caller diagnostic spans.
  if let some catchData := frame.extra.catchUnwind then
    roots := roots.pointer catchData.catchFn
    roots ← roots.immediate catchData.data.imm
    roots ← roots.memPlace catchData.dest.mplace
  if let some borrow := frame.extra.borrowTracker then
    for (id,tag) in borrow.protectedTags do roots := roots.add (some id) (some tag)
  return roots

def stack (roots : Roots) (stack : ThreadStacks.ActualStack) : Except StepError Roots := do
  let mut roots := roots
  for frame in stack.frames do roots ← roots.frame frame
  return roots

/-- Allocation bytes include partial pointer fragments. Tree roots/exposed tags
are visited even for allocations with no reachable pointer; allocation IDs of
live entries themselves are deliberately not added to the collected set. -/
def allocation (roots : Roots) (borrowTracking : Bool) (allocation : Allocation Provenance Miri.TreeBorrows.BorrowTree) : Roots := Id.run do
  let mut roots := roots
  for provenance in allocation.provenanceMap.provenances do roots := roots.provenance provenance
  if borrowTracking then
    for tag in allocation.extra.provenanceTags do roots := roots.add none (some tag)
  return roots

def storeBuffer (roots : Roots) (allocation : StoreBufferAlloc (Scalar Provenance)) : Except StepError Roots := do
  let mut roots := roots
  for object in allocation.storeBuffers.objects do
    for element in object.data.entries do
      if let some value := element.val then roots ← roots.scalar value
  return roots

/-- The arena is only a representation of the actual per-thread payload
vectors: visit exactly referenced entries, and reject missing/ambiguous tokens.
Unused arena slots are not roots. -/
def unwindPayloads (roots : Roots) (manager : ThreadManager) (store : Unwind.PayloadStore) :
    Except StepError Roots := do
  let mut roots := roots
  for thread in manager.threads do
    for token in thread.unwindPayloads do
      let values := store.values.filter (·.1 == token)
      let some entry := values[0]? | throw (.invalidProgram "GC: missing unwind payload")
      if values.size != 1 then throw (.invalidProgram "GC: ambiguous unwind payload")
      roots ← roots.immediate entry.2.imm
  return roots

end Roots

/-- Concrete visitors for user-embedded state must cover inactive stacks,
unwind payloads, last-error storage, thread-local allocations, TLS, env/dirs/fds,
weak store buffers, entry pointers and extern statics. Do not use a callback
that ignores a field merely because its source module has not been ported.
Machine alloc-address/TB/VClock globals intentionally carry no GC roots. -/
structure Hooks (K User : Type) where
  visitUser : MachineHooks.State K User → Roots → Except StepError Roots
  addresses : User → Miri.Memory.AllocAddresses.GlobalAddressState
  setAddresses : Miri.Memory.AllocAddresses.GlobalAddressState → User → User
  symbolicAlignment : User → Array (AllocId × Size × Align)
  setSymbolicAlignment : Array (AllocId × Size × Align) → User → User

private def lift (value : Except StepError A) : M K User A :=
  match value with | .ok value => pure value | .error error => throw error

/-- Full source collection and pruning order. All live bytes are scanned,
including leaked allocations. Global compiler allocations count as live via
MemoryState.isAllocLive but are not prematurely materialized by collection. -/
def run [DecidableEq K] (h : Hooks K User) : M K User Unit := do
  let state ← get
  let mut roots : Roots := {}
  for (_,entry) in state.machine.memory.live do roots := roots.allocation state.machine.borrowTracker.isSome entry.allocation
  roots ← lift (roots.stack state.stack)
  roots ← lift (h.visitUser state roots)
  if state.machine.borrowTracker.isSome then
    -- Commit each allocation's pruning before checking its explicit invariant
    -- outcome; a representation failure preserves the already-mutated prefix.
    for (id,_) in state.machine.memory.live do
      let machine := (← get).machine
      let some entry := machine.memory.live.find? (·.1 == id) |
        throw (.invalidProgram "GC live allocation disappeared")
      let result := entry.2.allocation.extra.removeUnreachableTags roots.tags
      let memory ← lift ((machine.memory.setLiveAllocation id (entry.2.allocation.setExtra result.tree)).mapError
        (fun error => .invalidProgram s!"GC tree replacement: {reprStr error}"))
      modify fun s => { s with machine := { s.machine with memory } }
      match result.outcome with
      | .ok () => pure ()
      | .error error => throw (.invalidProgram s!"GC tree invariant: {reprStr error}")
  let machine := (← get).machine
  let live := fun id => roots.allocations.contains id || machine.memory.isAllocLive id
  let allocationSpans := machine.allocationSpans.filter (fun entry => live entry.1)
  let user := h.setSymbolicAlignment ((h.symbolicAlignment machine.user).filter (fun entry => live entry.1)) machine.user
  -- Only base_addr is collected: inverse/exposed indexes are pruned by free.
  let addresses := h.addresses user
  let user := h.setAddresses { addresses with baseAddr := addresses.baseAddr.filter (fun entry => live entry.allocId) } user
  let borrowTracker := machine.borrowTracker.map fun borrow => { borrow with global :=
    { borrow.global with rootPointerTags := borrow.global.rootPointerTags.filter (fun entry => live entry.1) } }
  let memory := machine.memory.removeUnreachable roots.allocations
  modify fun s => { s with machine := { s.machine with allocationSpans,user,borrowTracker,memory } }

end Miri.Interpreter.ProvenanceGC
