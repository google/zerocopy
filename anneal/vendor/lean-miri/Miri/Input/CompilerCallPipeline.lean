import Miri.Input.CompilerVTableRuntime
import Miri.Input.CallResolution

/-! Shared preparation and actual compiler-leaf wiring for virtual/drop/caller
calls. All adapters retain one final compilation-local identity table; none
selects a body, type or instance by name or structural resemblance. -/
namespace Miri.Input.CompilerCallPipeline
open Lean Miri.ABI Miri.Memory Miri.Interpreter
abbrev Result := Except String

structure Prepared where
  scopes : CompilerScopes.Prepared
  runtime : CompilerRuntimeQueries.Prepared
  symbols : CompilerVTableRuntime.Prepared
  calls : CallResolution.Prepared
  sourceEquality : RuntimeMetadata.JsonReflexivity calls.runtime.source.raw

/-- Each stage appends identities without moving existing indices. Rebind all
views to the final table so full shim instances, inline spans, const arguments
and executable body identities remain compilation-local and consistent. -/
def prepareProfiled (profile : Lean.Options) (program : LoweredProgram) : Result Prepared := do
  let scopes := profileit "preparation.call.scopes" profile fun _ => CompilerScopes.prepare program
  let runtime ← profileit "preparation.call.runtime_queries" profile fun _ =>
    CompilerRuntimeQueries.prepare scopes.program
  let metadata ← profileit "preparation.call.runtime_metadata" profile fun _ =>
    (RuntimeMetadata.ofDocument runtime.program.input).mapError toString
  let sourceEquality := profileit "preparation.call.source_equality" profile fun _ =>
    RuntimeMetadata.JsonReflexivity.prepare (left := metadata.source.raw)
  let context ← profileit "preparation.call.compiler_facts" profile fun _ =>
    CompilerFacts.ofProgram metadata runtime.program (some sourceEquality)
  let facts ← profileit "preparation.call.fact_adapters" profile fun _ =>
    CompilerFactAdapters.prepare context
  let symbols := profileit "preparation.call.vtable_runtime" profile fun _ =>
    CompilerVTableRuntime.prepare facts
  let calls ← profileit "preparation.call.resolution" profile fun _ =>
    CallResolution.prepareWithRuntimeProfiled profile metadata symbols.facts.context.program (some sourceEquality)
  profileit "preparation.call.inline_attribute_validation" profile fun _ => do
    for (callee,trackCaller) in runtime.callerLocation do
      if let some inlineAttribute ← CompilerVirtualFacts.inlineAttribute scopes callee then
        unless inlineAttribute == trackCaller do throw "inlined/global full-instance caller attributes conflict"
  let program := calls.program
  let context := symbols.facts.context.withProgram program
  let symbols := { symbols with facts := { symbols.facts with context } }
  return ⟨{ scopes with program },{ runtime with program },symbols,calls,calls.sourceEquality⟩

def prepare (program : LoweredProgram) : Result Prepared :=
  prepareProfiled {} program

private def lift (result : Result A) : EStateM StepError S A :=
  match result with
  | .ok value => pure value
  | .error error => throw (.unsupported s!"compiler call pipeline: {error}")

def compilerHooks (prepared : Prepared) (base : VirtualCalls.CompilerHooks S C) :
    VirtualCalls.CompilerHooks S C :=
  CompilerVirtualFacts.scopeHooks prepared.scopes
    (CompilerRuntimeQueries.hooks prepared.runtime
      (CompilerVirtualFacts.compilerHooks prepared.symbols.facts base))

def vtableHooks (prepared : Prepared) (image : AllocationImage.Imported)
    (memory : S → MemoryState P E K) (base : VTableHooks P S C CallInstance (FnAbi MIR.TyId)) :
    VTableHooks P S C CallInstance (FnAbi MIR.TyId) :=
  CompilerVTableFacts.hooks prepared.symbols.facts
    (CompilerVTableRuntime.hooks prepared.symbols image memory base)

/-- Runtime reads/projections/pointer alignment remain actual machine actions.
Every replaced compiler/symbolic leaf uses the exact imported query evidence. -/
def runtimeHooks (prepared : Prepared) (image : AllocationImage.Imported)
    (memory : S → MemoryState P Extra K) (base : VirtualCalls.Hooks P S C E) :
    VirtualCalls.Hooks P S C E :=
  { base with
    compiler := compilerHooks prepared base.compiler
    vtable := vtableHooks prepared image memory base.vtable }

/-- Source load_mir returns the exact body-table key with executable MIR. Missing
or ambiguous instance bodies, failed substitutions and templates are errors. -/
def loadMir (prepared : Prepared) (fnInstance : CallInstance) : EStateM StepError S LoadedBody :=
  lift (CallResolution.loadedBodyOfInstance prepared.calls fnInstance)

def bindFunctionCalls (prepared : Prepared)
    (base : FunctionCalls.Hooks P S C E Other Extern FnABI ArgABI) :
    FunctionCalls.Hooks P S C E Other Extern FnABI ArgABI :=
  { base with loadMir := fun _ fnInstance => loadMir prepared fnInstance }

end Miri.Input.CompilerCallPipeline
