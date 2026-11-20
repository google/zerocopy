import Miri.Interpreter.PlaceDynamic
import Miri.Interpreter.FunctionPointerConsumers
import Miri.Interpreter.TypedMachineBindings

/-! Reduced cast leaves and direct physical CastHooks construction. Compiler,
vtable and provenance policies survive; canonical memory/copy/projection,
function-pointer resolution and recursive validation never enter as a dummy
base dictionary. The Cast.cast source policy is reused unchanged. -/
namespace Miri.Interpreter.ExecutionCast
open Miri.ABI Miri.Memory Miri.MIR
open MachineHooks (M State FrameExtra)
structure Leaves (S C : Type) where
  typeInfo : C → TyId → RvalueM S CastTypeInfo
  layoutOf : C → TyId → RvalueM S (TyAndLayout TyId)
  exposeProvenance : C → Provenance → RvalueM S Unit
  pointerFromExposedAddress : C → UInt64 → RvalueM S (Pointer (Option Provenance))
  usizeLayout : C → RvalueM S (TyAndLayout TyId)
  ensureMonomorphic : C → TyId → RvalueM S Unit
  requireNoBoundVars : C → Array GenericArg → RvalueM S Unit
  resolveFunction : C → DefId → Array GenericArg → RvalueM S (Option CallInstance)
  resolveClosureFnOnce : C → DefId → Array GenericArg → RvalueM S CallInstance
  builtinDeref : C → TyId → Bool → RvalueM S (Option TyId)
  boxLayout : C → TyId → RvalueM S (TyAndLayout TyId)
  validateImmediateABI : Immediate Provenance → LayoutData → Except StepError Unit
  fieldLayout : C → TyAndLayout TyId → Nat → RvalueM S (TyAndLayout TyId)
  lockstepTails : C → TyId → TyId → RvalueM S (TyId × TyId)
  vtableType : C → Pointer (Option Provenance) → Option Nat → RvalueM S TyId
  vtablePointer : C → TyId → Nat → RvalueM S (Pointer (Option Provenance))
  principal : C → Nat → RvalueM S (Option Nat)
  vtableEntries : C → Option Nat → TyId → RvalueM S (Array (VTableEntry CallInstance))
  supertraitSlot : C → TyId → TyId → RvalueM S (Option Nat)
  eraseSelfTraitRef : C → Nat → RvalueM S Nat
  normalizePrincipal : C → Nat → RvalueM S (Option Nat)

def Leaves.ofHooks (h : CastHooks Provenance S C V) : Leaves S C where
  typeInfo := h.typeInfo
  layoutOf := h.layoutOf
  exposeProvenance := h.exposeProvenance
  pointerFromExposedAddress := h.pointerFromExposedAddress
  usizeLayout := h.usizeLayout
  ensureMonomorphic := h.ensureMonomorphic
  requireNoBoundVars := h.requireNoBoundVars
  resolveFunction := h.resolveFunction
  resolveClosureFnOnce := h.resolveClosureFnOnce
  builtinDeref := h.builtinDeref
  boxLayout := h.boxLayout
  validateImmediateABI := h.validateImmediateABI
  fieldLayout := h.fieldLayout
  lockstepTails := h.lockstepTails
  vtableType := h.vtableType
  vtablePointer := h.vtablePointer
  principal := h.principal
  vtableEntries := h.vtableEntries
  supertraitSlot := h.supertraitSlot
  eraseSelfTraitRef := h.eraseSelfTraitRef
  normalizePrincipal := h.normalizePrincipal

def hooks [DecidableEq K] (queries : Leaves (State K U) C)
    (access : PlaceMachine.AccessConfig K U) (allocation : PlaceMachine.AllocationConfig K U)
    (compiler : PlaceMachine.CompilerHooks K U C)
    (projection : PlaceProjectionHooks Provenance (State K U) C FrameExtra)
    (copy : PlaceCopyHooks Provenance (State K U) C)
    (retag : TypedRetag.Hooks K U)
    (validity : ValidityVisitor.Hooks Provenance (State K U) C FrameExtra (FnVal O) (FnAbi TyId) Pad)
    (functions : FunctionPointers.Hooks K U O)
    (floats : FloatOpsHooks Provenance (State K U) C)
    (dereference : C → OpTy Provenance → M K U (MPlaceTy Provenance))
    (projectRead : C → OpTy Provenance → Nat → M K U (OpTy Provenance))
    (validationRecursive : C → LocalLayout → M K U Bool)
    (retagBudget validationBudget : Nat) :
    CastHooks Provenance (State K U) C (RuntimePlace Provenance) :=
  let place := projection.place
  {
    typeInfo := queries.typeInfo
    layoutOf := queries.layoutOf
    exposeProvenance := queries.exposeProvenance
    pointerFromExposedAddress := queries.pointerFromExposedAddress
    usizeLayout := queries.usizeLayout
    ensureMonomorphic := queries.ensureMonomorphic
    requireNoBoundVars := queries.requireNoBoundVars
    resolveFunction := queries.resolveFunction
    resolveClosureFnOnce := queries.resolveClosureFnOnce
    builtinDeref := queries.builtinDeref
    boxLayout := queries.boxLayout
    validateImmediateABI := queries.validateImmediateABI
    fieldLayout := queries.fieldLayout
    lockstepTails := queries.lockstepTails
    vtableType := queries.vtableType
    vtablePointer := queries.vtablePointer
    principal := queries.principal
    vtableEntries := queries.vtableEntries
    supertraitSlot := queries.supertraitSlot
    eraseSelfTraitRef := queries.eraseSelfTraitRef
    normalizePrincipal := queries.normalizePrincipal
    target := access.runtime.base
    destLayout := RuntimePlace.layout
    readImmediate := fun _ => PlaceMachine.readImmediate access
    writeImmediate := writePlaceImmediate place
    writePointer := fun c pointer dest => do
      let scalar ← match Scalar.fromMaybePointer access.runtime.base pointer with
        | .ok value => pure value | .error error => throw (ScalarOps.scalarError error)
      writePlaceImmediate place c (.scalar scalar) dest
    enforceValidity := compiler.enforceValidity
    enforceValidityRecursively := validationRecursive
    validatePlace := fun c dest recursive reset =>
      ValidityVisitor.validatePlace (TypedMachineBindings.bindValidity validity retag retagBudget)
        c validationBudget dest recursive reset
    derefPointer := fun c operand => do let _ ← dereference c operand; pure ()
    checkFunctionPointer := fun _ pointer => do let _ ← FunctionPointers.getPtrFn functions pointer; pure ()
    functionPointer := fun _ callee => return (← FunctionPointers.functionPointer functions (.Instance callee)).withOptionalProvenance
    floatOps := floats
    copyAllowTransmute := fun c source dest => copyRuntimePlace place copy c source dest true
    copyNoValidate := copyRuntimePlaceNoValidate place copy
    projectRead := projectRead
    projectWrite := PlaceDynamic.field projection }
end Miri.Interpreter.ExecutionCast
