import Miri.Interpreter.TypedValidityProviders

/-! Direct stateful Tree Borrows construction. Only source configuration,
attribute queries and diagnostic emission enter as leaves; projection, pointer
resolution, protection and memory writes are the canonical machine operations.
Sources: tree_borrows/mod.rs; helpers.rs UnsafeCellVisitor; machine.rs retag. -/
namespace Miri.Input.EvalRetagMachine
open Miri.ABI Miri.Memory Miri.MIR Miri.Interpreter
open Miri.TreeBorrows
structure Leaves (K U : Type) where
  implicitWrites : MachineHooks.M K (ValidityMachine.UserState U) Bool
  rustcNoWritable : DefId → MachineHooks.M K (ValidityMachine.UserState U) Bool
  preciseInteriorMut : MachineHooks.M K (ValidityMachine.UserState U) Bool
  logCreation : MPlaceTy Provenance → Size → RetagPolicy.NewPermission → BorTag →
    Option RetagPipeline.ResolvedLocation → MachineHooks.M K (ValidityMachine.UserState U) Unit

private def lift (value : Except String A) : MachineHooks.M K U A :=
  match value with | .ok value => pure value | .error reason => throw (.unsupported reason)
private def memory (place : RuntimePlace Provenance) : MachineHooks.M K U (MPlaceTy Provenance) :=
  match place.ref with
  | .memory value => pure ⟨value,place.layout⟩
  | .local .. => throw (.invalidProgram "freeze projection returned a local place")

def hooks [DecidableEq K] (prepared : CompilerFactAdapters.Prepared)
    (runtime : CompilerRuntimeQueries.Prepared) (leaves : Leaves K U)
    (access : ValidityMachine.Access K U)
    (projection : PlaceProjectionHooks Provenance (ValidityMachine.State K U) C MachineHooks.FrameExtra)
    (vtable : VTableHooks Provenance (ValidityMachine.State K U) C F A)
    (pointers : PointerMachine.Hooks K (ValidityMachine.Control U)) (choice : C) :
    TypedRetag.Hooks K (ValidityMachine.UserState U) :=
  let context := prepared.context
  let dynamic := PlaceDynamic.withVTable projection.dynamic vtable
  let size := fun (place : MPlaceTy Provenance) =>
    DynamicLayout.sizeAndAlignFromMeta dynamic choice projection.dynamicFuel place.mplace.metadata place.layout
  {
    typeShape := fun ty => lift (CompilerFacts.retagTypeShape context ty)
    builtinDeref := fun ty => lift (CompilerFacts.requiredType context ty "builtin_deref_explicit")
    referencePointee := fun ty => lift (CompilerFacts.referencePointee context ty)
    isUnpin := fun ty => lift (CompilerFacts.boolean context ty "is_unpin")
    isUnsafeUnpin := fun ty => lift (CompilerFacts.boolean context ty "is_unsafe_unpin")
    typeIsFreeze := fun ty => lift (CompilerFacts.boolean context ty "is_freeze")
    implicitWrites := leaves.implicitWrites
    rustcNoWritable := leaves.rustcNoWritable
    preciseInteriorMut := leaves.preciseInteriorMut
    immPtrToMPlace := PointerPlaceMachine.fromImmediate access (CompilerExecutionProviders.pointerCompiler prepared) choice
    sizeAndAlign := size
    checkPtrAccess := ValidityMachine.checkPointerAccess access
    resolveAllocation := TypedValidityProviders.resolveAllocation pointers
    logCreation := leaves.logCreation
    ensureTreeExtra := pointers.ensureTreeExtra
    reconstruct := fun value place => do
      let immediate ← match place.mplace.toRef access.runtime.base with
        | .ok immediate => pure immediate
        | .error error => throw (.invalidProgram s!"retagged reference: {reprStr error}")
      pure ⟨immediate,value.layout⟩
    writeUninit := fun place => do
      let access ← ValidityMachine.scopedAccess access
      PlaceMachine.writeMemory access (fun _ => false) .uninit place
    freeze := {
      target := pointers.arithmetic
      debugAssertions := projection.place.debugAssertions
      isUnsafeCell := fun ty => lift (CompilerFacts.boolean context ty "is_unsafe_cell")
      typeIsFreeze := fun ty => lift (CompilerFacts.boolean context ty "is_freeze")
      isDynamic := fun ty => lift (CompilerFacts.boolean context ty "is_dynamic")
      isBox := fun ty => lift (CompilerFacts.boolean context ty "is_box")
      isTooGeneric := fun ty => lift (CompilerFacts.boolean context ty "is_too_generic")
      sizeAndAlign := size
      projectField := fun place index => do
        memory (← PlaceDynamic.field projection choice ⟨.memory place.mplace,place.layout⟩ index)
      arrayLength := fun place => PlaceDynamic.length projection choice ⟨.memory place.mplace,place.layout⟩
      projectIndex := fun place index => do
        memory (← PlaceDynamic.index projection choice ⟨.memory place.mplace,place.layout⟩ index)
      projectBox := fun place => do
        let (pointer,allocator) ← CompilerExecutionProviders.projectBox context runtime projection choice
          ⟨.memory place.mplace,place.layout⟩
        pure (← memory pointer,← memory allocator)
      unpackDynTrait := fun place => do
        let .dynamic expected ← lift (CompilerFactAdapters.validityKind prepared place.layout.ty)
          | throw (.invalidProgram "freeze dyn unpack on non-dynamic compiler type")
        let inner ← VTable.unpackDynTrait vtable choice ⟨.indirect place.mplace,place.layout⟩ expected
        let .indirect memory := inner.op | throw (.invalidProgram "dynamic unpack returned immediate")
        pure ⟨memory,inner.layout⟩ } }
end Miri.Input.EvalRetagMachine
