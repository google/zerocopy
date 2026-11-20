import Miri.Input.CompilerCallPipeline
import Miri.Input.CompilerShimAbi
import Miri.Interpreter.Backtrace

/-! Exact compiler type/ABI/symbolic-function leaves for backtrace.rs.
Source-map, hygiene and symbol-rendering services remain required; no name or
line number is inferred from diagnostic spellings or a nearby exported span. -/
namespace Miri.Input.CompilerBacktraceFacts
open Miri.ABI Miri.Memory Miri.Interpreter
abbrev Result := Except String

private def lift (result : Result A) : EStateM StepError S A :=
  match result with
  | .ok value => pure value
  | .error error => throw (.unsupported s!"compiler backtrace query: {error}")

def unitPointerLayout (prepared : CompilerCallPipeline.Prepared) : Result LocalLayout := do
  let unit ← CompilerFacts.unitLayout prepared.symbols.facts.context
  let pointer ← CompilerRuntimeQueries.mutPointerType prepared.runtime unit.ty
  CompilerFacts.layoutOf prepared.symbols.facts.context pointer

/-- Only an actual ADT receives the source repr(C) check. A known non-ADT
returns None; unavailable type/repr metadata is an error, not a non-ADT default. -/
def adtReprC (prepared : CompilerCallPipeline.Prepared) (ty : MIR.TyId) : Result (Option Bool) := do
  let node ← prepared.symbols.facts.context.runtime.node ty |>.mapError toString
  unless node.shapeStatus == .supported do throw "return type compiler shape unresolved"
  if node.shapeKind == .adt then
    return some (← CompilerFacts.adtInfo prepared.symbols.facts.context ty).reprC
  match node.shapeKind with
  | .unknown tag => throw s!"unknown return type compiler shape {tag}"
  | _ => return none

def hooks (prepared : CompilerCallPipeline.Prepared) (shim : CompilerShimAbi.Prepared)
    (image : AllocationImage.Imported) (memory : S → MemoryState P Extra K)
    (base : Backtrace.Hooks P S D MD B I E Loc) : Backtrace.Hooks P S D MD B I E Loc := Id.run do
  let lookup := CompilerVTableRuntime.GlobalLookup.prepare prepared.symbols
  { base with
    foreign := CompilerShimAbi.hooks shim base.foreign
    unitPointerLayout := lift (unitPointerLayout prepared)
    globalFunction := fun id => do
      lift (CompilerVTableRuntime.globalFunctionUsing prepared.symbols lookup image (memory (← get)) id) }

def reprCHook (prepared : CompilerCallPipeline.Prepared) (ty : MIR.TyId) : EStateM StepError S (Option Bool) :=
  lift (adtReprC prepared ty)

end Miri.Input.CompilerBacktraceFacts
