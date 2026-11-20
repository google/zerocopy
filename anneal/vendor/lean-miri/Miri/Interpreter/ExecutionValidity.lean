import Miri.Interpreter.ValidityMachine

/-! Direct validity visitor construction from surviving compiler/CTFE queries.
Every byte/scalar access, provenance/padding operation, scoped ghost validation,
union-range cache and pointer check is the actual canonical implementation.
The recursive visitor and freeze-sensitive retag policy are reused unchanged. -/
namespace Miri.Interpreter.ExecutionValidity
open Miri.ABI Miri.Memory Miri.MIR
open ValidityVisitor Miri.Memory.Validity
open MachineHooks (FrameExtra)
structure Leaves (S C : Type) where
  classify : C → TyId → M S TypeKind
  unitLayout : C → M S LocalLayout
  typeName : C → TyId → M S String
  opsemInhabited : C → TyId → M S Bool
  isFreeze : C → TyId → M S Bool
  fieldPath : C → LocalLayout → Nat → TyId → M S PathElem
  variantPath : C → LocalLayout → Nat → M S PathElem
  projectBox : C → RuntimePlace Provenance → M S (RuntimePlace Provenance × RuntimePlace Provenance)
  metadataTail : C → TyId → M S MetadataTail
  ctfePointerLookup : C → MPlaceTy Provenance → CtfeMode → M S PointerAllocLookup

def Leaves.ofHooks (h : Hooks Provenance S C E F A Pad) : Leaves S C :=
  ⟨h.classify,h.unitLayout,h.typeName,h.opsemInhabited,h.isFreeze,h.fieldPath,h.variantPath,
    h.projectBox,h.metadataTail,h.ctfePointerLookup⟩

def hooks [DecidableEq K] (queries : Leaves (ValidityMachine.State K U) C)
    (access : ValidityMachine.Access K U)
    (allocation : PlaceMachine.AllocationConfig K (ValidityMachine.UserState U))
    (compiler : ValidityMachine.Compiler K U C)
    (projection : PlaceProjectionHooks Provenance (ValidityMachine.State K U) C FrameExtra)
    (vtable : VTableHooks Provenance (ValidityMachine.State K U) C F A)
    (discriminant : DiscriminantHooks Provenance (ValidityMachine.State K U) C (RuntimePlace Provenance))
    (retag : TypedRetag.Hooks K (ValidityMachine.UserState U)) (retagBudget : Nat) :
    Hooks Provenance (ValidityMachine.State K U) C FrameExtra F A ValidityMemory.PaddingHandle :=
  let compiler := ValidityMachine.compilerPolicy compiler
  let place := ValidityMachine.placeHooks access allocation compiler
  let dynamic := PlaceDynamic.withVTable projection.dynamic vtable
  let environment := ValidityMachine.memoryEnvironment access
  let source : Hooks Provenance (ValidityMachine.State K U) C FrameExtra F A ValidityMemory.PaddingHandle := {
    classify := queries.classify
    unitLayout := queries.unitLayout
    typeName := queries.typeName
    opsemInhabited := queries.opsemInhabited
    isFreeze := queries.isFreeze
    fieldPath := queries.fieldPath
    variantPath := queries.variantPath
    projectBox := queries.projectBox
    metadataTail := queries.metadataTail
    ctfePointerLookup := queries.ctfePointerLookup
    target := access.runtime
    debugAssertions := compiler.debugAssertions
    projection := projection
    vtable := vtable
    discriminant := discriminant
    toOp := placeToOp place
    readImmediate := fun c value expected => do
      ValidityMemory.readImmediate environment (← placeToOp place c value) expected
    clearProvenance := fun c value => ValidityMemory.clearPlaceProvenance environment place c
      ValidityMachine.validationInProgress MachineHooks.afterLocalWrite value
    writeNoValidate := fun c value destination => do
      let validate ← ValidityMachine.enforceValidity
      ValidityMemory.writeNoValidate environment place c (fun _ => validate) value destination
    sizeAndAlign := fun c value => DynamicLayout.sizeAndAlignFromMeta dynamic c projection.dynamicFuel
      value.mplace.metadata value.layout
    ptrToPlace := fun _ => retag.immPtrToMPlace
    checkPointerAccess := fun _ => ValidityMachine.checkPointerAccessResult access
    checkPointerAlign := fun _ => ValidityMachine.checkPointerAlign access
    checkPointerAlignResult := fun _ => ValidityMachine.checkPointerAlignResult access
    scalarMayBeNull := fun _ => ValidityMachine.scalarMayBeNull
    retagPointer := fun _ value ty => TypedRetag.machineRetagPtrValue retag retagBudget value ty
    inMutableMemory := fun _ => ValidityMachine.inMutableMemory
    readBytes := fun _ => ValidityMemory.readBytes environment
    clearBytesProvenance := fun _ => ValidityMemory.clearBytesProvenance environment
    beginPadding := fun _ => ValidityMemory.beginPadding environment
    writePadding := fun _ => ValidityMemory.writePadding environment
    cachedUnionRanges := fun _ layout compute => ValidityMachine.cachedUnionRanges layout compute
    withGhostValidation := ValidityMachine.withGhostValidation }
  ValidityMachine.visitor source access allocation compiler retag retagBudget
end Miri.Interpreter.ExecutionValidity
