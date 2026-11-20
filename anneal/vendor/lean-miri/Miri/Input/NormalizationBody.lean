import Lean

/-! Resolve the body carried by compiler normalization evidence.

Legacy exports embed the normalized body. Compact exports may instead point
at the source body's top-level JSON when the two complete serialized bodies
are equal. Unknown references and malformed encodings fail closed. -/
namespace Miri.Input.NormalizationBody
open Lean

def resolve (normalization sourceBody : Json) : Except String Json := do
  unless (← (← normalization.getObjVal? "status").getStr?) == "supported" do
    throw "compiler body normalization is unresolved"
  match normalization.getObjVal? "body", normalization.getObjVal? "body_ref" with
  | .ok body, .error _ =>
    let _ ← body.getObj?
    pure body
  | .error _, .ok reference => do
    unless (← reference.getStr?) == "source_body" do
      throw "unknown compiler normalization body reference"
    let _ ← sourceBody.getObj?
    pure sourceBody
  | .ok _, .ok _ => throw "normalization evidence has both body and body_ref"
  | .error _, .error _ => throw "normalization evidence has neither body nor body_ref"

end Miri.Input.NormalizationBody
