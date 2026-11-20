import Miri.Input.CompilerProviders
import Miri.Interpreter.ExecutionCast

/-! Direct cast query construction. Unexported generic/trait transformations
remain named mandatory compiler queries, rather than a baseline CastHooks
record containing physical operations that will subsequently be overwritten. -/
namespace Miri.Input.CompilerCastLeaves
open Miri.ABI Miri.Interpreter Miri.Memory Miri.MIR
structure Required (S C : Type) where
  requireNoBoundVars : C → Array GenericArg → RvalueM S Unit
  resolveFunction : C → DefId → Array GenericArg → RvalueM S (Option CallInstance)
  resolveClosureFnOnce : C → DefId → Array GenericArg → RvalueM S CallInstance
  lockstepTails : C → TyId → TyId → RvalueM S (TyId × TyId)
  boxLayout : C → TyId → RvalueM S (TyAndLayout TyId)
  principal : C → Nat → RvalueM S (Option Nat)
  supertraitSlot : C → TyId → TyId → RvalueM S (Option Nat)
  eraseSelfTraitRef : C → Nat → RvalueM S Nat
  normalizePrincipal : C → Nat → RvalueM S (Option Nat)

private def lift (value : Except String A) : EStateM StepError S A :=
  match value with
  | .ok value => pure value
  | .error reason => throw (.unsupported s!"cast compiler query: {reason}")

def make (p : CompilerProviders.Prepared) (required : Required S C)
    (vtable : VTableHooks Provenance S C CallInstance (FnAbi TyId))
    (expose : C → Provenance → RvalueM S Unit)
    (fromExposed : C → UInt64 → RvalueM S (Pointer (Option Provenance)))
    (validateABI : Immediate Provenance → LayoutData → Except StepError Unit) :
    ExecutionCast.Leaves S C :=
  let facts := p.lifecycle.calls.symbols.facts
  let context := facts.context
  { typeInfo := fun _ ty => lift (CompilerFactAdapters.castTypeInfo facts ty)
    layoutOf := fun _ ty => lift (CompilerFacts.layoutOf context ty)
    exposeProvenance := expose
    pointerFromExposedAddress := fromExposed
    usizeLayout := fun _ => lift (context.primitiveLayout "usize")
    ensureMonomorphic := fun _ ty => do
      unless ← lift (CompilerFacts.boolean context ty "is_monomorphic_enough") do
        throw (.invalidProgram "compiler type still requires instantiation")
    requireNoBoundVars := required.requireNoBoundVars
    resolveFunction := required.resolveFunction
    resolveClosureFnOnce := required.resolveClosureFnOnce
    builtinDeref := fun _ ty explicit => lift (CompilerFacts.builtinDeref context ty explicit)
    boxLayout := required.boxLayout
    validateImmediateABI := validateABI
    fieldLayout := fun _ parent index => lift (context.runtime.field parent index |>.mapError toString)
    lockstepTails := required.lockstepTails
    vtableType := VTable.getPtrVTableType vtable
    vtablePointer := VTable.getPointer vtable
    principal := required.principal
    vtableEntries := vtable.entries
    supertraitSlot := required.supertraitSlot
    eraseSelfTraitRef := required.eraseSelfTraitRef
    normalizePrincipal := required.normalizePrincipal }
end Miri.Input.CompilerCastLeaves
