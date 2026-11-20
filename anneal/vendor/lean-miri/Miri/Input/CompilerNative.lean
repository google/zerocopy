import Miri.Input.EvalNativeConstruction
import Miri.Input.CompilerProviders
import Miri.Interpreter.NativeAbi

/-! Native libffi compiler queries from native_lib/mod.rs:367–435. Shape is
actual compiler ADT/tuple evidence, not diagnostic spelling or ABI size. -/
namespace Miri.Input.CompilerNative
open Lean Miri.ABI Miri.Memory Miri.MIR Miri.Interpreter
private def lift (value : Except String A) : EStateM StepError S A :=
  match value with | .ok value => pure value | .error reason => throw (.callback s!"native compiler query unavailable: {reason}")

private def shape (p : CompilerProviders.Prepared) (layout : LocalLayout) : Except String Native.TypeShape := do
  let source ← p.runtime.node layout.ty |>.mapError toString
  unless source.shapeStatus == .supported do throw "native type shape evidence unresolved"
  if source.shapeKind == .adt then
    let value ← source.payload.getObjVal? "shape"
    let repr ← value.getObjVal? "representation"
    let reprC ← repr.getObjValAs? Bool "c"
    let (isEnum,isStruct) ← match source.shapeMetadata.adtKind with
      | some .enumKind => pure (true,false)
      | some .structKind => pure (false,true)
      | some .unionKind => pure (false,false)
      | _ => throw "native ADT kind evidence missing or unresolved"
    -- Scalar ABI queries only the ADT flags, not its unused field layouts.
    if let .Scalar .. := layout.layout.backendRepr then return .adt isEnum isStruct reprC #[]
    if !isStruct || !reprC then return .adt isEnum isStruct reprC #[]
    let info ← CompilerFacts.adtInfo p.lifecycle.calls.symbols.facts.context layout.ty
    unless info.variants.size == 1 do throw "native struct lacks one non-enum variant"
    let some fields := info.variants[0]? | throw "native struct fields unavailable"
    pure (.adt isEnum isStruct reprC (fields.map (·.ty)))
  else if source.shapeKind == .tuple then
    let value ← source.payload.getObjVal? "shape"
    let elements ← (← value.getObjVal? "elements").getArr?
    pure (if elements.isEmpty then .emptyTuple else .other)
  else pure .other

/-- Genuine compiler-query failure becomes the source unsupported-FFI-type
outcome. Missing/unresolved metadata remains a separate outer error. Runtime
array identities are read from the same persistent canonical constructor World. -/
def abiQueries (p : CompilerProviders.Prepared)
    (arrays : RuntimeArrayQueries.Access S) : NativeAbi.Queries S C where
  typeShape := fun _ layout => do
    let world := arrays.get (← get)
    if world.entries.any (·.value.ty == layout.ty) then
      let actual ← lift ((RuntimeArrayTypes.lookup world layout.ty).mapError reprStr)
      unless actual == layout do throw (.invalidProgram "native runtime array layout disagrees with canonical type")
      pure .other
    else lift (shape p layout)
  layoutOf := fun _ ty => do
    let world := arrays.get (← get)
    if world.entries.any (·.value.ty == ty) then
      return .ok (← lift ((RuntimeArrayTypes.lookup world ty).mapError reprStr))
    let node ← lift (p.runtime.node ty |>.mapError toString)
    if node.layout.kind == .layoutQueryError then return .error ()
    return .ok (← lift (p.runtime.lookup ty |>.mapError toString))
/-- The same genuine compiler queries work on full-state native calls and
machine-only closure construction, without introducing an artificial frame. -/
def make (p : CompilerProviders.Prepared)
    (arrays : RuntimeArrayQueries.Access (NativeMachine.State MiriMemoryKind U)) :
    EvalNativeConstruction.Compiler U C where
  typeShape := (abiQueries p arrays).typeShape
  layoutOf := (abiQueries p arrays).layoutOf
end Miri.Input.CompilerNative
