import Miri.Interpreter.MemoryExtras
import Miri.Interpreter.ValidityMachine
import Miri.Interpreter.PointerMachineBindings

/-! Source data_race.rs atomic physical operations coupled to canonical
PlaceMachine bytes, MemoryExtras clocks/store buffers, PointerMachine addresses,
and ValidityMachine's single ghost/alignment policy. No shadow atomic memory. -/
namespace Miri.Interpreter.AtomicMachine
open Miri.ABI Miri.Memory Miri.Concurrency
abbrev User := ValidityMachine.UserState
abbrev State K U := ValidityMachine.State K U
abbrev M K U := ValidityMachine.M K U

private def liftMachine (action : PlaceMachine.MachineM K (User U) A) : M K U A := fun state =>
  match action state.machine with
  | .ok value machine => .ok value {state with machine}
  | .error error machine => .error error {state with machine}

private def memoryPlace (place : RuntimePlace Provenance) : Except StepError (MPlaceTy Provenance) :=
  match place.ref with
  | .memory memory => .ok ⟨memory,place.layout⟩
  | .local .. => .error (.invalidProgram "atomic dereference produced a local place")
private def liftResult (result : Except StepError A) : M K U A :=
  match result with | .ok value => pure value | .error error => throw error

def physicalRead [DecidableEq K] (access : PlaceMachine.AccessConfig K (User U))
    (place : RuntimePlace Provenance) : M K U (RvalueImmTy Provenance) := do
  let memory ← liftResult (memoryPlace place)
  PlaceMachine.readImmediate access ⟨.indirect memory.mplace,memory.layout⟩

/-- The source ghost scope suppresses machine read hooks, but retains pointer
resolution, lazy allocation materialization, and raw-read errors/mutations.
Only the read's error is discarded; invalid ghost nesting is not discarded. -/
def ghostRead [DecidableEq K] (access : PlaceMachine.AccessConfig K (User U))
    (place : RuntimePlace Provenance) : M K U (Option (Scalar Provenance)) :=
  ValidityMachine.withGhostValidation do
    try
      let value ← physicalRead {access with ghostMode := true} place
      let scalar ← liftResult (value.imm.toScalar |>.mapError ScalarOps.immediateError)
      pure (some scalar)
    catch _ => pure none

/-- Atomic mutability uses get_alloc_raw (not metadata-only get_alloc_info), so
compiler globals materialize before read-only restrictions are applied. -/
def mutability [DecidableEq K] (access : PlaceMachine.AccessConfig K (User U))
    (id : AllocId) : M K U Mutability := do
  let state ← get
  let result := MemoryLifecycle.getAllocRaw state.machine.memory
    (⟨state.machine,none⟩ : PlaceMachine.AccessState K (User U)) id access.globalKind access.globalHooks
  let machine := {result.hooks.machine with memory := result.memory}
  set {state with machine}
  match result.outcome with
  | .ok allocation => pure allocation.mutability
  | .error error =>
    throw (result.hooks.pendingError.getD (access.memoryError (.pointerAccess (.rawAccess error))))

/-- Source ptr_try_get_alloc_id(ptr,0). The assertion for an unresolved address
belongs to atomic_access_check; this does not run physical access hooks. -/
def resolve (pointers : PointerMachine.Hooks K (ValidityMachine.Control U))
    (pointer : Pointer (Option Provenance)) : M K U (AllocId × Size) := do
  let state ← get
  let result := PointerMachine.resolvePointer pointers state.machine.memory state pointer 0
  set result.state
  match result.outcome with
  | .error error => throw (.callback error)
  | .ok (.error _) => throw (.invalidProgram "there are no zero-sized atomic accesses")
  | .ok (.ok resolved) => pure (resolved.allocId,resolved.offset)

def checkAlignment (pointers : PointerMachine.Hooks K (ValidityMachine.Control U))
    (pointer : Pointer (Option Provenance)) (align : Align) : M K U Unit := do
  let policy := (← get).machine.user.payload.alignment
  PointerMachine.checkAlignment pointers (policy == .Symbolic) (policy != .None) pointer align

/-- Concrete dictionary for source atomic access/load/store/CAS/RMW/fences.
Compiler generic ordering/volatile evaluation, typed dereference, scalar type
queries, finite weak-memory choices, and diagnostics are retained
from base; every physical/race/weak/TB/sync operation below is canonical. -/
def bind [DecidableEq K]
    (base : IntrinsicAtomicHooks Provenance (State K U) C (RuntimePlace Provenance))
    (access : PlaceMachine.AccessConfig K (User U))
    (allocation : PlaceMachine.AllocationConfig K (User U))
    (compiler : PlaceMachine.CompilerHooks K (User U) C)
    (pointers : PointerMachine.Hooks K (ValidityMachine.Control U))
    (extras : MemoryExtras.Hooks K (User U) Payload) :
    IntrinsicAtomicHooks Provenance (State K U) C (RuntimePlace Provenance) :=
  let access := MemoryExtras.bindAccess extras access
  let places := PlaceMachine.placeHooks access allocation compiler
  {base with
    target := access.runtime.base
    getGlobal := fun state => state.machine.dataRace
    setGlobal := fun state global => {state with machine := {state.machine with dataRace := some global}}
    threads := fun state => state.machine.threads
    getAtomic := fun state id => MemoryExtras.getAtomic extras state.machine id
    setAtomic := fun id atomic => liftMachine (MemoryExtras.commitAtomic extras id atomic)
    placeLayout := RuntimePlace.layout
    placePointer := fun place => do return (← memoryPlace place).mplace.ptr
    readImmediate := fun _ => PlaceMachine.readImmediate access
    physicalRead := fun _ => physicalRead access
    physicalWrite := fun c value place => do
      let _ ← liftResult (memoryPlace place)
      writePlaceImmediate places c value place
    ghostRead := fun _ => ghostRead access
    checkPointerAlign := fun _ => checkAlignment pointers
    resolveAllocation := fun _ => resolve pointers
    mutability := fun _ => mutability access
    writeImmediate := fun c value dest => writePlaceImmediate places c value dest }
end Miri.Interpreter.AtomicMachine
