import Miri.Interpreter.TypedValidityProviders
import Miri.Input.CompilerDiscriminantFacts
import Miri.Interpreter.Aggregate

/-! Canonical typed-memory provider closure: address resolution retains source
TB tag/wildcard extras, and discriminant execution consumes actual compiler
facts plus real typed field reads/writes. No synthetic stack is constructed. -/
namespace Miri.Interpreter.TypedMemoryProviders
open Miri.ABI Miri.Memory Miri.MIR Miri.Input
abbrev User := ValidityMachine.UserState
abbrev State K U := ValidityMachine.State K U
abbrev Machine K U := MachineHooks.MachineState K (User U)
abbrev M K U := ValidityMachine.M K U

/-- Source ptr_try_get_alloc_id performs address lookup without ordinary access
hooks. Parent provenance is reduced only to its source tag/wildcard extra;
allocation identity stays in ResolvedPointer.allocId and the address cache. -/
def resolvePointer (pointers : PointerMachine.Hooks K (ValidityMachine.Control U))
    (memory : MemoryState Provenance Miri.TreeBorrows.BorrowTree K)
    (pointer : Pointer (Option Provenance)) (size : Int) :
    PlaceMachine.MachineM K (User U) (Except UInt64 (ResolvedPointer ProvenanceExtra)) := do
  if size < -(2^63 : Int) || size >= 2^63 then
    throw (.invalidProgram "memory address resolution access size exceeds i64")
  let some provenance := pointer.provenance | return .error pointer.offset.bytes
  let lookup : Memory.AllocAddresses.AddressLookupHooks := {
    sizeOf := fun id => (memory.getAllocInfo id).toOption.map (·.size)
    isLive := fun id => some (memory.isAllocLive id) }
  let result := (← get).user.addresses.ptrGetAlloc (Pointer.new provenance pointer.offset) (Int64.ofInt size) lookup pointers.arithmetic
  match result with
  | .error error => throw (pointers.classifyAddressError error)
  | .ok none => pure (.error pointer.offset.bytes)
  | .ok (some (id,offset)) =>
    let extra := match provenance with
      | .concrete _ tag => ProvenanceExtra.concrete tag
      | .wildcard => ProvenanceExtra.wildcard
    pure (.ok ⟨id,offset,extra⟩)

def bindAccess (pointers : PointerMachine.Hooks K (ValidityMachine.Control U))
    (base : ValidityMachine.Access K U) : ValidityMachine.Access K U :=
  {base with resolvePointer := resolvePointer pointers}

/-- Lifecycle's older resolver boundary has no typed error variant; preserve
that error in AccessState.pendingError, which AllocationMachine propagates
before classifying its legacy pointer failure. Resolution failure commits no
allocation removal or byte effects. -/
def lifecycleResolver (pointers : PointerMachine.Hooks K (ValidityMachine.Control U)) :
    MemoryState Provenance Miri.TreeBorrows.BorrowTree K →
      PlaceMachine.AccessState K (User U) → Pointer (Option Provenance) → Int →
      PointerResolutionResult Provenance Miri.TreeBorrows.BorrowTree K
        (PlaceMachine.AccessState K (User U)) ProvenanceExtra :=
  fun memory state ptr size =>
    let state := {state with machine := {state.machine with memory}}
    match resolvePointer pointers memory ptr size state.machine with
    | .ok result machine =>
      {memory := machine.memory,state := {state with machine},outcome := result.map fun resolved =>
        (resolved.allocId,resolved.offset,resolved.extra)}
    | .error error machine =>
      {memory := machine.memory,state := ⟨machine,some error⟩,outcome := .error ptr.offset.bytes}

def bindLifecycle (pointers : PointerMachine.Hooks K (ValidityMachine.Control U))
    (base : MemoryLifecycleHooks Provenance Miri.TreeBorrows.BorrowTree K
      (PlaceMachine.AccessState K (User U)) ProvenanceExtra) :
    MemoryLifecycleHooks Provenance Miri.TreeBorrows.BorrowTree K
      (PlaceMachine.AccessState K (User U)) ProvenanceExtra :=
  {base with resolvePointer := lifecycleResolver pointers}

/-- All five discriminant compiler queries come from actual exporter evidence.
Read/write field operations are canonical source projections and typed memory;
source invalid-tag/niche/order logic remains the existing Discriminant driver. -/
def discriminant [DecidableEq K] (facts : CompilerFacts.Context)
    (access : ValidityMachine.Access K U)
    (projection : PlaceProjectionHooks Provenance (State K U) C MachineHooks.FrameExtra)
    (base : DiscriminantHooks Provenance (State K U) C (RuntimePlace Provenance)) :
    DiscriminantHooks Provenance (State K U) C (RuntimePlace Provenance) :=
  {CompilerDiscriminantFacts.hooks facts base with
    runtimeTarget := access.runtime
    projectRead := fun c source field => do
      let cx ← projection.place.projection c
      match projectField cx source field with
      | .ok value => pure value
      | .error error => throw (IntrinsicVectorMachine.projectionError error)
    readImmediate := fun _ => ValidityMachine.readImmediate access
    destLayout := RuntimePlace.layout
    projectWrite := PlaceDynamic.field projection
    writeScalar := fun c scalar dest => writePlaceImmediate projection.place c (.scalar scalar) dest
    toOp := placeToOp projection.place
    scalarMayBeNull := fun _ => ValidityMachine.scalarMayBeNull}

/-- Rvalue and Aggregate run exactly the same discriminant record, so direct,
niche and uninhabited checks cannot diverge between reads and tag writes. -/
def bindRvalue
    (discr : DiscriminantHooks Provenance (State K U) C (RuntimePlace Provenance))
    (base : RvalueHooks Provenance (State K U) C (RuntimePlace Provenance)) :
    RvalueHooks Provenance (State K U) C (RuntimePlace Provenance) :=
  {base with
    readDiscriminant := Discriminant.readDiscriminant discr
    discriminantForVariant := Discriminant.discriminantForVariant discr}

def bindAggregate
    (discr : DiscriminantHooks Provenance (State K U) C (RuntimePlace Provenance))
    (base : AggregateHooks Provenance (State K U) C (RuntimePlace Provenance)) :
    AggregateHooks Provenance (State K U) C (RuntimePlace Provenance) :=
  {base with writeDiscriminant := Discriminant.writeDiscriminant discr}

def bindIntrinsics
    (discr : DiscriminantHooks Provenance (State K U) C (RuntimePlace Provenance))
    (base : IntrinsicHooks Provenance (State K U) C (RuntimePlace Provenance)) :
    IntrinsicHooks Provenance (State K U) C (RuntimePlace Provenance) :=
  {base with
    readDiscriminant := Discriminant.readDiscriminant discr
    discriminantForVariant := Discriminant.discriminantForVariant discr}
end Miri.Interpreter.TypedMemoryProviders
