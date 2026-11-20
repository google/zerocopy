import Miri.Input.EvalRuntimeConstruction

/-! Exact compiler startup facts and the small source-owned arguments adapter.
These are separate from host environment contents: the latter remain the
explicit `EvalBootstrap.Configuration` supplied by the embedding. -/
namespace Miri.Input.EvalStartupRuntimeConstruction
open Lean Miri.ABI Miri.Memory Miri.MIR Miri.Interpreter

structure StartupFacts where
  noCore : Except String Bool
  coreEscapeDefault : Except String (DefinitionId × Bool)

private def field (value : Json) (name : String) : Except String Json :=
  value.getObjVal? name

private def fieldString (value : Json) (name : String) : Except String String := do
  (← field value name).getStr?

private def fieldNat (value : Json) (name : String) : Except String Nat := do
  (← field value name).getNat?

private def queryValue (query : Json) : Except String Json := do
  let status ← fieldString query "status"
  if status == "supported" then field query "value"
  else if status == "unsupported" then do
    let reason := match (field query "reason").bind Json.getStr? with
      | .ok message => message
      | .error _ => "exact compiler startup query is unavailable"
    throw reason
  else throw s!"unknown compiler startup query status `{status}`"

/-- Prepare source facts from the pinned exporter query table. Failed queries
remain stored and are raised only if the corresponding source startup path
asks for them. The escape-default identity must already be in the canonical
definition table; no path or display-name identity is synthesized here. -/
def prepare (compiler : CompilerProviders.Prepared) : Except String StartupFacts := do
  let queries ← field compiler.program.input.raw "compiler_runtime_queries"
  let startup ← field queries "startup"
  let noCore := do
    let value ← queryValue (← field startup "no_core")
    value.getBool?
  let coreEscapeDefault := do
    let value ← queryValue (← field startup "core_escape_default")
    let rawDefinition ← field value "definition"
    let source : DefinitionId := ⟨← fieldNat rawDefinition "crate", ← fieldNat rawDefinition "index"⟩
    let available ← (← field value "mir_available").getBool?
    pure (source,available)
  return ⟨noCore, coreEscapeDefault⟩

private def demanded (query : Except String A) : MachineHooks.M K U A :=
  match query with
  | .ok value => pure value
  | .error reason => throw (.unsupported reason)

/-- Attach exact exporter-derived no_core and sentinel-MIR facts to the argv
constructor from the same fixed execution Config. No target knob is supplied
by the caller, and failed compiler queries remain demand-time Unknown. -/
def argumentsFromExecution
    (compiler : CompilerProviders.Prepared)
    (execution : EvalExecutable.Core Os R P H D O Aff B Host C ClockHost)
    (facts : StartupFacts) :
    Except String (EntryArguments.Hooks MiriMemoryKind
      (ThreadStacks.Storage (EvalExecutable.U Os R P H D O Aff B Host))
      (ValidityMachine.Control (ThreadStacks.Storage (EvalRuntimeConstruction.W Os R P H D O Aff B Host)))
      P C) :=
  let result := EvalRuntimeConstruction.argumentsFromExecution compiler execution false
    (demanded (facts.coreEscapeDefault.map Prod.snd))
  let windows := compiler.externStatics.targetFacts.map fun target => target.os == "windows"
  do
    let hooks ← result
    let windows ← windows
    pure {hooks with windows, isNoCore := demanded facts.noCore}

end Miri.Input.EvalStartupRuntimeConstruction
