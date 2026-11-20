import Miri.Input.CompilerIntrinsicFacts
import Miri.Interpreter.ExecutionCallLeaves

/-! machine.rs::check_fn_target_features exact compiler attributes/session.
Feature order and all Enabled/Forced/Implied kinds are retained in input. The
source driver performs the initial guard, diagnostic filtering and wasm abort.
-/
namespace Miri.Input.CompilerTargetFeatures
open Lean Miri.Interpreter
private def payload (p : CompilerIntrinsicFacts.Prepared) (callee : CallInstance) : Except String Json := do
  let some entry := p.entries.find? (·.callee == callee) | throw "missing exact full-instance target features"
  pure entry.payload

def required (p : CompilerIntrinsicFacts.Prepared) (callee : CallInstance) :
    Except String (Array ExecutionCallLeaves.TargetFeature) := do
  (← (← (← payload p callee).getObjVal? "target_features").getArr?).mapM fun feature => do
    let name ← (← feature.getObjVal? "name").getStr?
    let implied ← match ← (← feature.getObjVal? "kind").getStr? with
      | "implied" => pure true | "enabled" | "forced" => pure false
      | _ => throw "unknown compiler target-feature kind"
    pure ⟨name,implied⟩

def available (p : CompilerIntrinsicFacts.Prepared) (name : String) : Except String Bool := do
  let session ← p.program.input.raw.getObjVal? "compiler_session_queries"
  let names ← (← (← session.getObjVal? "internal_target_features").getArr?).mapM Json.getStr?
  pure (names.contains name)

def isLikeWasm (p : CompilerIntrinsicFacts.Prepared) : Except String Bool := do
  let session ← p.program.input.raw.getObjVal? "compiler_session_queries"
  (← session.getObjVal? "is_like_wasm").getBool?
private def lift (query : Except String A) : EStateM StepError S A :=
  match query with | .ok value => pure value | .error error => throw (.unsupported error)

def dictionary (p : CompilerIntrinsicFacts.Prepared) : ExecutionCallLeaves.TargetFeatures S :=
  {required := fun callee => lift (required p callee)
   available := fun name => lift (available p name)
   isLikeWasm := lift (isLikeWasm p)}
end Miri.Input.CompilerTargetFeatures
