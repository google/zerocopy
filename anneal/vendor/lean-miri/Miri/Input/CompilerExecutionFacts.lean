import Miri.Input.CompilerIntrinsicFacts
import Miri.Input.CompilerIntrinsicConstants

/-! Actual source intrinsic identity/override/fallback attributes and session
runtime-check values, attached to the same canonical execution dictionary. -/
namespace Miri.Input.CompilerExecutionFacts
open Miri.Interpreter
private def lift (result : Except String A) : MachineHooks.M K User A :=
  match result with
  | .ok value => pure value
  | .error error => throw (.unsupported s!"compiler execution query: {error}")

def hooks (p : CompilerIntrinsicFacts.Prepared) (base : ExecutionMachine.Config K User C Other Extern Host) :
    ExecutionMachine.Config K User C Other Extern Host :=
  {CompilerIntrinsicConstants.hooks p base with
    operands := {base.operands with runtimeChecks := fun _ kind => lift (CompilerIntrinsicFacts.runtimeChecks p kind)}
    intrinsicName := fun callee => lift (CompilerIntrinsicFacts.itemName p callee)
    intrinsicMustOverride := fun callee => lift (CompilerIntrinsicFacts.mustOverride p callee)
    intrinsicFallbackIsSpec := fun callee => lift (CompilerIntrinsicFacts.fallbackIsSpec p callee)}
end Miri.Input.CompilerExecutionFacts
