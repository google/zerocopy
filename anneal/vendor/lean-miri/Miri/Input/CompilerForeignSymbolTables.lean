import Miri.Interpreter.ForeignItems
import Miri.Input.CompilerVTableRuntime
import Miri.Input.CompilerCallPipeline

/-! Immutable compiler symbol and allocator-shim tables. This module contains
only source metadata decoding and exact lookup policy, so preparation can be
cached by the compiler provider without depending on runtime foreign hooks. -/
namespace Miri.Input.CompilerForeignSymbolTables
open Miri.Interpreter

structure Candidate where
  symbol : String
  explicitSymbol : Bool
  /-- Only callable exports need a MIR instance. Statics/non-callables must
  still participate in symbol clashes and in the exported-function UB guard. -/
  fnInstance : Option CallInstance
  crateIndex : Nat
  crateName : String
  weak : Bool
  spanLo : Nat
  spanHi : Nat
  kind : ForeignItems.ExportKind
  compilerBuiltins : Bool
  deriving Repr, DecidableEq

inductive AllocatorTarget where
  | redirect (symbol : String)
  | special (method : ForeignItems.SpecialAllocatorMethod)
  deriving Repr, DecidableEq

structure AllocatorEntry where
  symbol : String
  target : AllocatorTarget
  deriving Repr, DecidableEq

structure Prepared where
  noAllocShimSymbol : String
  /-- Exact `iter_exported_symbols` iteration order; do not sort this array. -/
  candidates : Array Candidate
  allocatorEntries : Array AllocatorEntry
  deriving Repr, DecidableEq

private def field (j : Lean.Json) (name : String) : Except String Lean.Json := j.getObjVal? name
private def text (j : Lean.Json) (name : String) : Except String String := do
  (← field j name).getStr?
private def natural (j : Lean.Json) (name : String) : Except String Nat := do
  (← field j name).getNat?
private def boolean (j : Lean.Json) (name : String) : Except String Bool := do
  (← field j name).getBool?
private def compilerValue (j : Lean.Json) : Except String Lean.Json := do
  let status ← text j "status"
  unless status == "supported" do
    let reason := match text j "reason" with
      | .ok message => message
      | .error _ => "compiler query did not provide a reason"
    throw s!"compiler foreign-symbol query unresolved: {reason}"
  field j "value"

private def exportKind (value : String) : Except String ForeignItems.ExportKind :=
  match value with
  | "function" => pure .function
  | "associated_function" => pure .associatedFunction
  | "static" => pure .staticItem
  | "other" => pure .other
  | _ => throw s!"unknown exported symbol definition kind `{value}`"

private def allocatorTarget (record : Lean.Json) : Except String AllocatorTarget := do
  let target ← field record "target"
  match ← text target "kind" with
  | "redirect" => return .redirect (← text target "symbol")
  | "special" =>
    let method ← text target "method"
    match method with
    | "alloc" => return .special .Alloc
    | "alloc_zeroed" => return .special .AllocZeroed
    | "dealloc" => return .special .Dealloc
    | "realloc" => return .special .Realloc
    | _ => throw s!"unknown compiler special allocator method `{method}`"
  | kind => throw s!"unknown compiler allocator target `{kind}`"

/-- Callable exports can have compiler identity without an eager MIR body.
Resolve their ID through the finalized `compiler_runtime_queries.instances`
identity table; a later selected lookup still uses CallResolution.loadMir and
preserves a missing-body error. -/
private def callableInstance (prepared : CompilerVTableRuntime.Prepared)
    (ctx : LowerContext) (identity : Lean.Json) : Except String CallInstance := do
  let program := prepared.facts.context.program
  let tables := program.compilerTables
  let (callee,next) ← CompilerInstance.decode ctx tables identity
  unless next.definitions == tables.definitions && next.typeConstants == tables.typeConstants do
    throw "exported callable identity is absent from finalized compiler tables"
  return callee

/-- Decode the exact compiler symbol tables. `CompilerVTableRuntime.Prepared`
already owns the final shared instance table, so every emitted candidate ID is
resolved through that table and never reconstructed from a path/display. -/
def prepare (instances : CompilerVTableRuntime.Prepared) : Except String Prepared := do
  let program := instances.facts.context.program
  let queries ← field program.input.raw "compiler_runtime_queries"
  let source ← field queries "foreign_symbols"
  let noAlloc ← field source "no_alloc_shim_symbol"
  unless (← text noAlloc "status") == "supported" do
    throw "compiler no-allocation shim symbol unresolved"
  let noAllocName ← text noAlloc "value"
  let candidateRecords ← (← compilerValue (← field source "exported_candidates")).getArr?
  let mut lowering : Option LowerContext := none
  let mut candidates := #[]
  let mut previousIndex : Option Nat := none
  for position in [:candidateRecords.size] do
    let some record := candidateRecords[position]? | throw "exported symbol candidate missing"
    let index ← natural record "iteration_index"
    if let some previous := previousIndex then
      unless previous < index do
        throw "exported symbol iterator order is missing or inconsistent"
    previousIndex := some index
    let kind ← exportKind (← text record "definition_kind")
    let callee ← if kind == .function || kind == .associatedFunction then do
        let identity ← field record "callable_identity"
        let ctx := match lowering with
          | some ctx => ctx
          | none => LowerContext.ofDocument program.input
        lowering := some ctx
        let decoded ← callableInstance instances ctx identity
        -- The separate ID remains globally unique for table joins; decoding
        -- uses only this minimal mono identity, not eager instance metadata.
        pure (some decoded)
      else pure none
    let span ← field record "span"
    let candidate : Candidate := {
      symbol := ← text record "symbol"
      explicitSymbol := ← boolean record "explicit_symbol"
      fnInstance := callee
      crateIndex := ← natural record "crate_index"
      crateName := ← text record "crate_name"
      weak := ← boolean record "weak"
      spanLo := ← natural span "lo"
      spanHi := ← natural span "hi"
      kind := kind
      compilerBuiltins := ← boolean record "compiler_builtins" }
    candidates := candidates.push candidate
  let allocatorRecords ← (← compilerValue (← field source "allocator_shims")).getArr?
  let mut allocatorEntries := #[]
  for record in allocatorRecords do
    let entry : AllocatorEntry := ⟨← text record "symbol",← allocatorTarget record⟩
    if allocatorEntries.any (·.symbol == entry.symbol) then
      throw s!"duplicate compiler allocator shim symbol `{entry.symbol}`"
    allocatorEntries := allocatorEntries.push entry
  return ⟨noAllocName,candidates,allocatorEntries⟩

private def earlierSpan (left right : Candidate) : Bool :=
  left.spanLo < right.spanLo ||
    (left.spanLo == right.spanLo && left.spanHi < right.spanHi)

/-- Miri's lookup_exported_symbol weak/strong precedence and duplicate error.
The array order is the pinned iterator order, including local-crate-first and
linked dependency order. Equal-strength duplicate definitions terminate. -/
def lookup (prepared : Prepared) (symbol : String) : Except StepError (Option Candidate) := do
  let mut selected : Option Candidate := none
  for candidate in prepared.candidates do
    if candidate.explicitSymbol && candidate.symbol == symbol then
      if let some previous := selected then
        match candidate.weak, previous.weak with
        | false, true => selected := some candidate
        | true, false => pure ()
        | _, _ =>
          let (first,second) := if earlierSpan previous candidate then
              (previous,candidate) else (candidate,previous)
          throw (StepError.machineStop s!"multiple symbol definitions `{symbol}` in crates {first.crateName} and {second.crateName}")
      else selected := some candidate
  return selected

/-- Exact lookup_exported_fn type guard. Loading MIR is a separate canonical
CompilerCallPipeline operation, and its missing-body error is preserved. -/
def lookupFunction (prepared : Prepared)
    (loadMir : CallInstance → EStateM StepError S LoadedBody)
    (symbol : String) : EStateM StepError S (Option (LoadedBody × CallInstance)) := do
  let candidate? ← match lookup prepared symbol with
    | .ok result => pure result
    | .error error => throw error
  let some candidate := candidate? | return none
  if candidate.kind != .function && candidate.kind != .associatedFunction then
    throw (.undefinedBehavior "attempt to call an exported symbol that is not defined as a function")
  let some fnInstance := candidate.fnInstance | throw (.unsupported "callable exported symbol has no compiler instance identity")
  return some (← loadMir fnInstance,fnInstance)

def allocatorSymbol (prepared : Prepared) (symbol : String) :
    Option (ForeignItems.AllocatorSymbol CallInstance) :=
  (prepared.allocatorEntries.find? (·.symbol == symbol)).map fun entry =>
    match entry.target with
    | .redirect target => .redirect target
    | .special method => .special method

/-- Source sig.rs exemption: compiler-builtins definitions do not clash with
Miri's built-in implementation. Every other exact exported candidate does. -/
def checkSymbolClash (prepared : Prepared) (symbol : String) :
    Except StepError Unit := do
  match ← lookup prepared symbol with
  | none => pure ()
  | some candidate =>
    if candidate.compilerBuiltins then pure ()
    else throw (StepError.machineStop s!"symbol shim clashing `{symbol}` at {candidate.crateName}:{candidate.spanLo}..{candidate.spanHi}")

end Miri.Input.CompilerForeignSymbolTables
