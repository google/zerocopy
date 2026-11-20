import Miri.Input.CompilerProviders
import Miri.Interpreter.CompilerExecutionProviders
import Miri.Interpreter.IntrinsicSymbolsMachine

/-! Exact C-varargs compiler leaves from intrinsics.rs:877–931,1416–1433;
identical_c_types delegates to the source call.rs structural compatibility port.
Target-specific VaList fields come from instantiated compiler ADT declarations.
-/
namespace Miri.Input.CompilerVarArgsLeaves
open Miri.ABI Miri.Interpreter Miri.Memory
private def lift (value : Except String A) : EStateM StepError S A :=
  match value with | .ok value => pure value | .error e => throw (.unsupported e)
private def checked (value : Except StepError A) : EStateM StepError S A :=
  match value with | .ok value => pure value | .error e => throw e

def make (p : CompilerProviders.Prepared) (compatibilityBudget : Nat) :
    IntrinsicSymbolsMachine.VarArgsLeaves K U C :=
  let context := p.lifecycle.calls.symbols.facts.context
  { layoutOf := fun _ ty => lift (CompilerFacts.layoutOf context ty)
    typeInfo := fun _ ty => do
      let source ← lift (context.runtime.node ty |>.mapError toString)
      unless source.shapeStatus == .supported do throw (.unsupported "varargs compiler shape unavailable")
      match source.shapeKind with
      | .int => return .signedInteger (← checked (CompilerExecutionProviders.integerKind context ty))
      | .uint => return .unsignedInteger (← checked (CompilerExecutionProviders.integerKind context ty))
      | .rawPointer | .reference =>
        return .pointer (← lift (CompilerFacts.requiredType context ty "builtin_deref_explicit"))
      | .unknown _ => throw (.unsupported "varargs compiler shape unknown")
      | _ => pure .other
    identicalCTypes := fun _ left right =>
      LayoutCompat.identicalCTypes (CompilerFacts.compatibilityQueries context) compatibilityBudget left right
    isCVoid := fun _ ty => lift (CompilerFacts.boolean context ty "is_c_void")
    vaListFields := fun _ ty => do
      let adt ← lift (CompilerFacts.adtInfo context ty)
      if adt.kind == .Enum then throw (.invalidProgram "VaListImpl must be a non-enum ADT")
      unless adt.variants.size == 1 do throw (.invalidProgram "VaListImpl has invalid non-enum variant declarations")
      let some fields := adt.variants[0]? | throw (.unsupported "VaListImpl compiler fields unavailable")
      pure (fields.map (·.ty))
    isRawPointer := fun _ ty => do
      let source ← lift (context.runtime.node ty |>.mapError toString)
      unless source.shapeStatus == .supported do throw (.unsupported "VaList field compiler shape unavailable")
      match source.shapeKind with
      | .unknown _ => throw (.unsupported "VaList field compiler shape unknown")
      | shape => pure (shape == .rawPointer) }
end Miri.Input.CompilerVarArgsLeaves
