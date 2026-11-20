import Miri.Input.CompilerFacts
import Miri.Interpreter.ShimSignatureMachine

/-! Exact lang-item identity query for C variadic void/character pointer
compatibility. Missing facts are unresolved; spelling/size does not imply void. -/
namespace Miri.Input.CompilerShimSignatures
open Miri.Interpreter

def hooks (context : CompilerFacts.Context) (base : ShimSignatures.Hooks P S D MD Ptr B I) :
    ShimSignatures.Hooks P S D MD Ptr B I :=
  {base with isCVoid := fun ty =>
    match CompilerFacts.boolean context ty "is_c_void" with
    | .ok value => pure value
    | .error reason => throw (.unsupported s!"compiler c_void query: {reason}")}
end Miri.Input.CompilerShimSignatures
