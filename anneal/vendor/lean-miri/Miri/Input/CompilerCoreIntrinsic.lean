import Miri.Input.CompilerProviders
import Miri.Interpreter.CompilerExecutionProviders
import Miri.Interpreter.ExecutionIntrinsic

/-! Direct compiler-only queries for ordinary intrinsics.rs. variant_count
peels exactly one Pat, handles ADT declarations without requiring mono, rejects
source generic/bound cases and returns zero for the source non-ADT kinds. -/
namespace Miri.Input.CompilerCoreIntrinsic
open Lean Miri.ABI Miri.Interpreter
private def lift (value : Except String A) : EStateM StepError S A :=
  match value with | .ok value => pure value | .error e => throw (.unsupported e)

def variantCount (p : CompilerProviders.Prepared) (ty : MIR.TyId) : Except StepError Nat := do
  let get := fun id => do
    let source ← (p.runtime.node id).mapError (fun e => StepError.unsupported (toString e))
    unless source.shapeStatus == .supported do
      throw (.unsupported "variant_count compiler shape unresolved")
    pure source
  let source ← get ty
  let source ← if source.shapeKind == .patternType then do
      let id ← ((source.payload.getObjVal? "shape").bind (·.getObjVal? "base") >>= fun value =>
        value.getObjValAs? Nat "type_id").mapError StepError.unsupported
      get id
    else pure source
  match source.shapeKind with
  | .alias | .parameter | .placeholderType | .inferenceType =>
    throw (.invalidProgram "TooGeneric in variant_count")
  | .patternType | .boundType => throw (.invalidProgram "source invariant: invalid nested pattern/bound type in variant_count")
  | .unknown _ => throw (.unsupported "variant_count compiler shape unknown")
  | .adt =>
    let variants ← ((source.payload.getObjVal? "shape").bind (·.getObjVal? "variants") >>= Json.getArr?).mapError StepError.unsupported
    pure variants.size
  | _ => pure 0

structure Queries (S C : Type) where
  layoutOf : C → MIR.TyId → RvalueM S LocalLayout
  pointeeType : C → MIR.TyId → RvalueM S MIR.TyId
  integerKind : C → MIR.TyId → RvalueM S MIR.IntegerKind
  usizeLayout : C → RvalueM S LocalLayout
  isizeLayout : C → RvalueM S LocalLayout
  variantLayout : C → LocalLayout → Nat → RvalueM S LocalLayout
  ensureMonomorphic : C → MIR.TyId → RvalueM S Unit
  needsDrop : C → MIR.TyId → RvalueM S Bool
  variantCount : C → MIR.TyId → RvalueM S Nat

def make (p : CompilerProviders.Prepared) : Queries S C :=
  let context := p.lifecycle.calls.symbols.facts.context
  { layoutOf := fun _ ty => lift (CompilerFacts.layoutOf context ty)
    pointeeType := fun _ ty => lift (CompilerFacts.requiredType context ty "builtin_deref_explicit")
    integerKind := fun _ ty => match CompilerExecutionProviders.integerKind context ty with
      | .ok value => pure value | .error e => throw e
    usizeLayout := fun _ => lift (p.primitiveLayout "usize")
    isizeLayout := fun _ => lift (p.primitiveLayout "isize")
    variantLayout := fun _ layout index => lift (p.runtime.forVariant layout index |>.mapError toString)
    ensureMonomorphic := fun _ ty => do
      unless ← lift (CompilerFacts.boolean context ty "is_monomorphic_enough") do
        throw (.invalidProgram "TooGeneric: intrinsic type requires instantiation")
    needsDrop := fun _ ty => lift (CompilerFacts.boolean context ty "needs_drop")
    variantCount := fun _ ty => match variantCount p ty with
      | .ok value => pure value | .error e => throw e }
end Miri.Input.CompilerCoreIntrinsic
