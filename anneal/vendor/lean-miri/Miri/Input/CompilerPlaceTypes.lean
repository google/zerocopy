import Miri.Input.CompilerFrameContext

/-! Exact debug-only place/operand type checks, place.rs:626–643 and
operand.rs:805–830. The compiler's instantiated body supplies each expected
place type. Runtime projection/layouts never substitute for that query. -/
namespace Miri.Input.CompilerPlaceTypes
open Lean Miri.ABI Miri.Interpreter Miri.Memory

private def scan (ctx : LowerContext) (requested : MIR.Place) :
    Nat → Json → Json → Except String (Array MIR.TyId)
  | 0,_,_ => throw "place query traversal budget exhausted"
  | fuel+1,source,normalized => do
    let mut found := #[]
    if (source.getObjVal? "local").isOk && (source.getObjVal? "projection").isOk then
      let key ← lowerCompilerPlace ctx (← ctx.decodeCompilerValue source)
      if key == requested then
        found := found.push (← (← normalized.getObjVal? "type").getObjValAs? Nat "type_id")
    match source with
    | .arr values =>
      let counterparts ← normalized.getArr?
      unless values.size == counterparts.size do throw "normalization changed source place container length"
      for index in [:values.size] do
        let some original := values[index]? | throw "source traversal index absent"
        let some actual := counterparts[index]? | throw "normalized traversal index absent"
        found := found ++ (← scan ctx requested fuel original actual)
    | .obj fields =>
      for (key,value) in fields.toList do
        -- Scalar metadata may legitimately change during normalization. Only
        -- containers can contain further source places.
        match value with
        | .arr _ | .obj _ =>
          found := found ++ (← scan ctx requested fuel value (← normalized.getObjVal? key))
        | _ => pure ()
    | _ => pure ()
    pure found

def expectedLayout (p : CompilerProviders.Prepared) (frame : CompilerFrameContext.ActualFrame)
    (requested : MIR.Place) : Except String LocalLayout := do
  let body ← CompilerFrameContext.bodyOfFrame p frame
  let source ← body.input.payload.getObjVal? "basic_blocks"
  let normalized ← (← CompilerFrameContext.normalizedBody p frame).getObjVal? "basic_blocks"
  let ids ← scan p.loweringContext requested
    (source.compress.length+1) source normalized
  let some id := ids[0]? | throw "place has no exact compiler normalization evidence in canonical body"
  unless ids.all (· == id) do throw "same source place has conflicting normalized compiler types"
  p.runtime.lookup id |>.mapError toString

def check (p : CompilerProviders.Prepared) (debugAssertions : Bool)
    (relateCovariantly : LocalLayout → LocalLayout → MachineHooks.M K U Bool)
    (requested : MIR.Place) (actual : LocalLayout) : MachineHooks.M K U Unit := do
  if !debugAssertions then return
  let expected ← match expectedLayout p (← MachineHooks.currentFrame) requested with
    | .ok value => pure value
    | .error reason => throw (.unsupported s!"compiler place type query: {reason}")
  let related ← if expected.ty == actual.ty then pure true else relateCovariantly expected actual
  unless related do throw (.invalidProgram "MIR place compiler type differs from evaluated place type")
  unless expected.layout == actual.layout do
    throw (.invalidProgram "MIR covariant assignment has different compiler layouts")

def operand (p : CompilerProviders.Prepared) (debugAssertions : Bool)
    (relateCovariantly : LocalLayout → LocalLayout → MachineHooks.M K U Bool)
    (_ : C) (requested : MIR.Place) (value : OpTy Provenance) : MachineHooks.M K U Unit :=
  check p debugAssertions relateCovariantly requested value.layout

def place (p : CompilerProviders.Prepared) (debugAssertions : Bool)
    (relateCovariantly : LocalLayout → LocalLayout → MachineHooks.M K U Bool)
    (_ : C) (requested : MIR.Place) (value : RuntimePlace Provenance) : MachineHooks.M K U Unit :=
  check p debugAssertions relateCovariantly requested value.layout
end Miri.Input.CompilerPlaceTypes
