import Miri.Interpreter.PointerPlaceMachine
import Miri.Interpreter.Math.Bindings

/-! Canonical SIMD/architecture/x86 execution dictionaries. Compiler vector and
integer type construction remains typed metadata; projection, typed memory,
transmute and pointer conversion execute the existing source operations. -/
namespace Miri.Interpreter.IntrinsicVectorMachine
open Miri.ABI Miri.Memory Miri.MIR
abbrev User := ValidityMachine.UserState
abbrev State K U := ValidityMachine.State K U
abbrev M K U := ValidityMachine.M K U
private def liftResult (result : Except StepError A) : M K U A :=
  match result with | .ok value => pure value | .error error => throw error

/-- Classification is retained explicitly for nonportable compiler/machine
errors; numeric bounds and scalar reads have their source interpreter classes. -/
def projectionError : ProjectionError → StepError
  | .machineError error => error
  | .obligation message => .callback message
  | .invariant message => .invalidProgram message
  | .bounds len index => .undefinedBehavior s!"index {index} out of bounds for length {len}"
  | .pointerArithOverflow => .undefinedBehavior "overflowing in-bounds pointer offset"
  | .scalar error => ScalarOps.scalarError error
  | .immediate error => ScalarOps.immediateError error
  | .offset (.inbounds (.access (.allocationLookup (.unavailable id)))) =>
    .callback s!"projection allocation metadata unavailable: {reprStr id}"
  | .offset (.inbounds (.access (.malformedAlignment error))) =>
    .invalidProgram s!"projection alignment: {reprStr error}"
  | .offset (.inbounds (.access (.sizeDoesNotFitI64 size))) =>
    .invalidProgram s!"projection size exceeds i64: {reprStr size}"
  | .offset (.inbounds (.access (.signedSizeOutsideI64 size))) =>
    .invalidProgram s!"projection signed size exceeds i64: {size}"
  | .offset (.inbounds (.access (.pointerArithmetic error))) =>
    .invalidProgram s!"projection pointer arithmetic: {reprStr error}"
  | .offset (.inbounds (.access error)) => .undefinedBehavior s!"in-bounds pointer projection: {reprStr error}"
  | .offset (.inbounds (.pointer error)) => .invalidProgram s!"projection pointer representation: {reprStr error}"
  | .offset error => .invalidProgram s!"pointer projection: {reprStr error}"
  | .layout error => .invalidProgram s!"projection layout: {reprStr error}"
  | .align error => .invalidProgram s!"projection alignment: {reprStr error}"
  | .size error => .invalidProgram s!"projection size: {reprStr error}"

private def memoryPlace (place : RuntimePlace Provenance) : M K U (MPlaceTy Provenance) :=
  match place.ref with
  | .memory value => pure ⟨value,place.layout⟩
  | .local .. => throw (.invalidProgram "SIMD dereference must produce a memory place")

/-- Source Projectable::transmute assertions, then zero-offset wrapping
projection. The operation never erases/recreates pointer provenance. -/
def transmuteWrite (projection : PlaceProjectionHooks Provenance (State K U) C MachineHooks.FrameExtra)
    (choice : C) (source : RuntimePlace Provenance) (target : LocalLayout) : M K U (RuntimePlace Provenance) := do
  if !source.layout.layout.isSized || !target.layout.isSized || source.layout.layout.size != target.layout.size then
    throw (.invalidProgram "transmute requires equally sized layouts")
  PlaceDynamic.offsetWithMeta projection choice source .ZERO .wrapping .none target

/-- Source field/index projection is retained for every lane: initialization,
provenance and hooks are checked by the later actual read/write, not simulated
by extracting an untyped array of values. -/
def bindSimd [DecidableEq K]
    (base : IntrinsicSimdHooks Provenance (State K U) C (RuntimePlace Provenance))
    (access : PlaceMachine.AccessConfig K (User U))
    (projection : PlaceProjectionHooks Provenance (State K U) C MachineHooks.FrameExtra)
    (copy : PlaceCopyHooks Provenance (State K U) C)
    (pointerCompiler : PointerPlaceMachine.Compiler K U C)
    (pointers : PointerMachine.Hooks K (ValidityMachine.Control U)) :
    IntrinsicSimdHooks Provenance (State K U) C (RuntimePlace Provenance) :=
  let places := projection.place
  {base with
    target := access.runtime.base
    forceAllocation := fun c source => do
      let memory ← forceAllocation places c source
      pure ⟨.memory memory.mplace,memory.layout⟩
    placeLayout := RuntimePlace.layout
    placePointer := fun source => match source.ref with
      | .memory memory => pure memory.ptr
      | .local .. => .error (.invalidProgram "SIMD backing place has not been allocated")
    fieldRead := fun c source index => do
      match source.op with
      | .immediate _ => liftResult (projectField (← places.projection c) source index |>.mapError projectionError)
      | .indirect memory =>
        let projected ← PlaceDynamic.field projection c ⟨.memory memory,source.layout⟩ index
        match projected.ref with
        | .memory memory => pure ⟨.indirect memory,projected.layout⟩
        | .local .. => throw (.invalidProgram "indirect SIMD field projection became local")
    fieldWrite := PlaceDynamic.field projection
    fieldLayout := fun c layout index => do
      let cx ← places.projection c
      liftResult (cx.field layout index |>.mapError projectionError)
    indexRead := fun c source index => do
      match source.op with
      | .immediate _ => liftResult (projectIndex (← places.projection c) source index |>.mapError projectionError)
      | .indirect memory =>
        let projected ← PlaceDynamic.index projection c ⟨.memory memory,source.layout⟩ index
        match projected.ref with
        | .memory memory => pure ⟨.indirect memory,projected.layout⟩
        | .local .. => throw (.invalidProgram "indirect SIMD index projection became local")
    indexWrite := PlaceDynamic.index projection
    readImmediate := fun _ => PlaceMachine.readImmediate access
    writeImmediate := fun c value dest => writePlaceImmediate places c value dest
    copyOp := fun c source dest => copyRuntimePlace places copy c source dest false
    derefImmediate := fun c value => do
      let memory ← PointerPlaceMachine.fromImmediate access pointerCompiler c value
      pure ⟨.memory memory.mplace,memory.layout⟩
    readPlaceImmediate := fun _ source => do
      let memory ← memoryPlace source
      PlaceMachine.readImmediate access ⟨.indirect memory.mplace,memory.layout⟩
    unalignedPlace := fun _ ptr layout => do
      let memory ← PointerPlaceMachine.fromPointer access ptr layout true
      pure ⟨.memory memory.mplace,memory.layout⟩
    checkAlign := fun _ => AtomicMachine.checkAlignment pointers
    readBytes := fun _ ptr size => do
      pure (← RawMemoryMachine.readBytes access pointers.arithmetic ptr size.bytes).data
    writeBytes := fun _ ptr bytes => RawMemoryMachine.writeBytes access pointers.arithmetic ptr ⟨bytes⟩ }

/-- Shared backing dictionary for AArch64/LoongArch and all x86 families. -/
def bindArchitecture (base : ArchitectureHooks Provenance (State K U) C (RuntimePlace Provenance))
    (simd : IntrinsicSimdHooks Provenance (State K U) C (RuntimePlace Provenance))
    (projection : PlaceProjectionHooks Provenance (State K U) C MachineHooks.FrameExtra)
    (u128Layout : LocalLayout) : ArchitectureHooks Provenance (State K U) C (RuntimePlace Provenance) :=
  {base with simd, transmuteDestU128 := fun c dest => transmuteWrite projection c dest u128Layout}

/-- x86 reinterpretation remains source Projectable wrapping projection;
actual gathers use the full canonical global-aware memory copy. -/
def bindX86 [DecidableEq K]
    (base : IntrinsicX86.Hooks Provenance (State K U) C (RuntimePlace Provenance))
    (architecture : ArchitectureHooks Provenance (State K U) C (RuntimePlace Provenance))
    (access : PlaceMachine.AccessConfig K (User U))
    (projection : PlaceProjectionHooks Provenance (State K U) C MachineHooks.FrameExtra)
    (pointers : PointerMachine.Hooks K (ValidityMachine.Control U)) :
    IntrinsicX86.Hooks Provenance (State K U) C (RuntimePlace Provenance) :=
  {base with
    architecture := architecture
    transmuteRead := fun c source target => do
      liftResult (source.transmute (← projection.place.projection c) target |>.mapError projectionError)
    transmuteWrite := transmuteWrite projection
    memCopy := fun _ source dest size nonoverlapping =>
      GlobalMemoryCopyMachine.copy access pointers.arithmetic source dest size 1 nonoverlapping }
end Miri.Interpreter.IntrinsicVectorMachine
