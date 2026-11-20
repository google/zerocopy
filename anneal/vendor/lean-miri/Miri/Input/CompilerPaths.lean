import Miri.Input.CompilerFactAdapters

/-! Pinned interpret/validity.rs::aggregate_field_path_elem (371-452) and
visit_variant (1277-1290). Paths are diagnostics only. Field names come from
actual compiler definitions; dyn paths require the actual projected child type.
Captured-variable numeric names are used only after explicit capture-name query
evidence reports no binding name, as in the source fallback. -/
namespace Miri.Input.CompilerPaths
open Lean Miri.ABI Miri.Memory Miri.Interpreter
abbrev Result := Except String
private def field (j : Json) (key : String) : Result Json := j.getObjVal? key
private def array (j : Json) (key : String) : Result (Array Json) := do (← field j key).getArr?
private def natural (j : Json) (key : String) : Result Nat := do (← field j key).getNat?
private def string (j : Json) (key : String) : Result String := do (← field j key).getStr?
private def node (context : CompilerFacts.Context) (id : TypeId) : Result TypeNode :=
  (context.runtime.node id).mapError toString
private def sourceVariant (source : TypeNode) (index : Nat) : Result Json := do
  let variants ← array (← field source.payload "shape") "variants"
  let some variant := variants.find? (fun item => (natural item "index").toOption == some index)
    | throw "compiler variant identity missing"
  pure variant

def variantPath (context : CompilerFacts.Context) (layout : TyAndLayout TypeId) (index : Nat) : Result PathElem := do
  let source ← node context layout.ty
  match source.shapeKind with
  | .adt => return .variant (← string (← sourceVariant source index) "name")
  | .coroutine => pure (.coroutineState index)
  | _ => throw "source invariant: variant path requested for non-variant type"

def fieldPath (context : CompilerFacts.Context) (layout : TyAndLayout TypeId)
    (index : Nat) (childType : TypeId) : Result PathElem := do
  let source ← node context layout.ty
  if let .Multiple _ _ tagField _ := layout.layout.variants then
    if tagField == index then
      if source.shapeMetadata.adtKind == some .enumKind then return .enumTag
      if source.shapeKind == .coroutine then return .coroutineTag
      throw "source invariant: tag path on non-variant type"
  match source.shapeKind with
  | .closure | .coroutine | .coroutineClosure =>
    let some facts := source.compilerFacts | throw "capture-name compiler evidence missing"
    unless facts.captureNamesStatus == some .supported do throw "capture-name compiler query unresolved"
    let some names := facts.captureNames | throw "capture-name compiler array evidence missing"
    let name := match names[index]? with
      | none | some none => toString index
      | some (some name) => name
    pure (.capturedVar name)
  | .tuple => pure (.tupleElem index)
  | .adt =>
    let variantIndex ← match layout.layout.variants with
      | .Single index => pure index
      | .Empty => throw "source invariant: field path in Variants::Empty"
      | .Multiple .. => throw "source invariant: non-tag field path before variant selection"
    let fields ← array (← sourceVariant source variantIndex) "fields"
    let some item := fields.find? (fun item => (natural item "index").toOption == some index)
      | throw "compiler ADT field identity missing"
    return .field (← string item "name")
  | .array | .slice => pure (.arrayElem index)
  | .dynamicTraitObject =>
    unless index == 0 do throw "source invariant: dyn projected field index is not zero"
    return .dynDowncast (← node context childType).display
  | _ => throw "source invariant: aggregate field path on non-aggregate type"

private def lift (value : Result A) : EStateM StepError S A :=
  match value with
  | .ok value => pure value
  | .error error => throw (.invalidProgram error)

/-- Bind diagnostic paths using the actual projected child type supplied by the
visitor, including dynamically unpacked values and Box allocator projections. -/
def validityHooks (prepared : CompilerFactAdapters.Prepared)
    (machine : ValidityVisitor.Hooks P S C E Fn Abi Pad) :
    ValidityVisitor.Hooks P S C E Fn Abi Pad :=
  { CompilerFactAdapters.validityHooks prepared machine with
    fieldPath := fun _ layout index childType =>
      lift (fieldPath prepared.context layout index childType)
    variantPath := fun _ layout index =>
      lift (variantPath prepared.context layout index) }

end Miri.Input.CompilerPaths
