import Miri.Interpreter.CompilerExecutionProviders

/-! Connected compiler and machine providers for runtime typed validity and
Tree Borrows. Existing actual vtable/discriminant/global compiler dictionaries
remain shared; no new representation of values, heaps, or type IDs is added. -/
namespace Miri.Interpreter.TypedValidityProviders
open Miri.ABI Miri.Memory Miri.MIR Miri.Input
abbrev User := ValidityMachine.UserState
abbrev State K U := ValidityMachine.State K U
abbrev M K U := ValidityMachine.M K U
private def liftResult (result : Except String A) : M K U A :=
  match result with | .ok value => pure value | .error error => throw (.callback s!"compiler validity query: {error}")

/-- Source ptr_try_get_alloc_id(ptr,0) supplies the actual offset and parent TB
provenance, including wildcard provenance. No physical read/access hooks run. -/
def resolveAllocation (pointers : PointerMachine.Hooks K (ValidityMachine.Control U))
    (ptr : Pointer (Option Provenance)) : M K U (Option Miri.TreeBorrows.RetagPipeline.ResolvedLocation) := do
  let state ← get
  let result := PointerMachine.resolvePointer pointers state.machine.memory state ptr 0
  set result.state
  match result.outcome with
  | .error error => throw (.callback error)
  | .ok (.error _) => pure none
  | .ok (.ok resolved) =>
    let extra := match resolved.extra with
      | .concrete _ tag => ProvenanceExtra.concrete tag
      | .wildcard => ProvenanceExtra.wildcard
    pure (some ⟨resolved.allocId,resolved.offset,extra⟩)

/-- Close compiler queries, pointer conversion/resolution, dynamic layout and
actual freeze projections. Source diagnostic policy, rustc_no_writable and
configuration flags remain typed inputs, not successful placeholder defaults. -/
def retagHooks [DecidableEq K] (prepared : CompilerFactAdapters.Prepared)
    (runtime : CompilerRuntimeQueries.Prepared)
    (access : ValidityMachine.Access K U)
    (projection : PlaceProjectionHooks Provenance (State K U) C MachineHooks.FrameExtra)
    (vtable : VTableHooks Provenance (State K U) C F A)
    (pointers : PointerMachine.Hooks K (ValidityMachine.Control U)) (choice : C)
    (base : TypedRetag.Hooks K (User U)) : TypedRetag.Hooks K (User U) :=
  let base := CompilerFacts.typedRetagHooks prepared.context base
  let dynamic := PlaceDynamic.withVTable projection.dynamic vtable
  let toMemory := fun (place : RuntimePlace Provenance) =>
    match place.ref with
    | .memory memory => pure (MPlaceTy.mk memory place.layout)
    | .local .. => throw (.invalidProgram "freeze projection returned a local place")
  let freeze := {base.freeze with
    target := pointers.arithmetic
    debugAssertions := projection.place.debugAssertions
    sizeAndAlign := fun place => DynamicLayout.sizeAndAlignFromMeta dynamic choice projection.dynamicFuel place.mplace.metadata place.layout
    projectField := fun place index => do
      toMemory (← PlaceDynamic.field projection choice ⟨.memory place.mplace,place.layout⟩ index)
    arrayLength := fun place => PlaceDynamic.length projection choice ⟨.memory place.mplace,place.layout⟩
    projectIndex := fun place index => do
      toMemory (← PlaceDynamic.index projection choice ⟨.memory place.mplace,place.layout⟩ index)
    projectBox := fun place => do
      let (pointer,allocator) ← CompilerExecutionProviders.projectBox prepared.context runtime projection choice ⟨.memory place.mplace,place.layout⟩
      pure (← toMemory pointer,← toMemory allocator)
    unpackDynTrait := fun place => do
      let .dynamic expected ← liftResult (CompilerFactAdapters.validityKind prepared place.layout.ty)
        | throw (.invalidProgram "freeze dyn unpack on non-dynamic compiler type")
      let inner ← VTable.unpackDynTrait vtable choice ⟨.indirect place.mplace,place.layout⟩ expected
      let .indirect memory := inner.op | throw (.invalidProgram "dynamic unpack returned immediate")
      pure ⟨memory,inner.layout⟩}
  let base := {base with
    freeze
    immPtrToMPlace := PointerPlaceMachine.fromImmediate access (CompilerExecutionProviders.pointerCompiler prepared) choice
    sizeAndAlign := fun place => DynamicLayout.sizeAndAlignFromMeta dynamic choice projection.dynamicFuel place.mplace.metadata place.layout
    checkPtrAccess := ValidityMachine.checkPointerAccess access
    resolveAllocation := resolveAllocation pointers
    ensureTreeExtra := pointers.ensureTreeExtra }
  let base := TypedMachineBindings.retagHooks access base
  {base with writeUninit := fun place => do
    let access ← ValidityMachine.scopedAccess access
    PlaceMachine.writeMemory access (fun _ => false) .uninit place}

/-- Compose compiler type/path evidence, real Box projection, actual immediate
pointer construction and existing canonical memory/ghost/retag visitor. The
remaining base CTFE lookup and vtable/discriminant records are genuine compiler
allocation/type pipelines, not a guessed result from payload bytes. -/
def visitor [DecidableEq K] (prepared : CompilerFactAdapters.Prepared)
    (runtime : CompilerRuntimeQueries.Prepared)
    (access : ValidityMachine.Access K U)
    (allocation : PlaceMachine.AllocationConfig K (User U))
    (compiler : ValidityMachine.Compiler K U C)
    (pointers : PointerMachine.Hooks K (ValidityMachine.Control U))
    (retag : TypedRetag.Hooks K (User U)) (retagFuel : Nat)
    (base : ValidityVisitor.Hooks Provenance (State K U) C MachineHooks.FrameExtra F A ValidityMemory.PaddingHandle) :
    ValidityVisitor.Hooks Provenance (State K U) C MachineHooks.FrameExtra F A ValidityMemory.PaddingHandle :=
  let base := CompilerPaths.validityHooks prepared base
  let dynamic := PlaceDynamic.withVTable base.projection.dynamic base.vtable
  let pointer := CompilerExecutionProviders.pointerCompiler prepared
  let compiler := PointerPlaceMachine.bindCompiler access allocation pointer dynamic base.vtable base.projection.dynamicFuel compiler
  let base := {base with
    unitLayout := fun _ => liftResult (CompilerPrimitiveFacts.unitLayout prepared.context.runtime)
    projectBox := CompilerExecutionProviders.projectBox prepared.context runtime base.projection
    ptrToPlace := PointerPlaceMachine.fromImmediate access pointer }
  let base := ValidityMachine.visitor base access allocation compiler retag retagFuel
  -- The final pointer/retag callbacks sample choice and ghost state at the event,
  -- so no stale choice/projection or duplicated scoped state is captured.
  {base with
    ptrToPlace := PointerPlaceMachine.fromImmediate access pointer
    retagPointer := fun choice value ty =>
      let retag := retagHooks prepared runtime access base.projection base.vtable pointers choice retag
      TypedRetag.machineRetagPtrValue retag retagFuel value ty}
end Miri.Interpreter.TypedValidityProviders
