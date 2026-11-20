import Miri.Input.CompilerCastLeaves
import Miri.Input.CompilerVTableFacts
import Miri.Input.CompilerVTableRuntime

/-! Exact compiler query closure for interpret/cast.rs. Query results are
compiler evidence keyed by complete source types/arguments; this module is not
an instance solver and does not guess trait relationships from layouts. -/
namespace Miri.Input.CompilerCastQueries
open Lean Miri.ABI Miri.MIR Miri.Memory Miri.Interpreter
abbrev Result := Except String
private def facts (p : CompilerProviders.Prepared) := p.lifecycle.calls.symbols.facts
private def records (p : CompilerProviders.Prepared) : Result (Array Json) := do
  (← p.program.input.raw.getObjVal? "compiler_cast_queries").getArr?
private def text (j : Json) (key : String) : Result String := do (← j.getObjVal? key).getStr?
private def ref (j : Json) (key : String) : Result TyId := do
  (← (← j.getObjVal? key).getObjVal? "type_id").getNat?
private def value (j : Json) : Result Json := do
  unless (← text j "typing_env") == "fully_monomorphized" do throw "cast query typing environment mismatch"
  unless (← text j "status") == "supported" do throw "cast compiler query unavailable"
  j.getObjVal? "value"
private def unique (entries : Array Json) : Result Json := do
  let some first := entries[0]? | throw "missing exact cast compiler query"
  unless entries.all (· == first) do throw "conflicting exact cast compiler queries"
  pure first
private def query (p : CompilerProviders.Prepared) (kind : String) (source : TyId) : Result Json := do
  unique ((← records p).filter fun record =>
    (text record "query_kind").toOption == some kind && (ref record "input_type").toOption == some source)
private def pairQuery (p : CompilerProviders.Prepared) (kind : String) (source target : TyId) : Result Json := do
  unique ((← records p).filter fun record =>
    (text record "query_kind").toOption == some kind &&
    (ref record "input_source").toOption == some source && (ref record "input_target").toOption == some target)
private def layout (p : CompilerProviders.Prepared) (id : TyId) : Result LocalLayout :=
  ((facts p).context.runtime.lookup id).mapError toString

private def resolutionRecord (p : CompilerProviders.Prepared) (kind : String)
    (definition : DefId) (args : Array GenericArg) : Result Json := do
  let mut matching := #[]
  for record in ← records p do
    if (text record "query_kind").toOption == some kind then
      let input ← ref record "input_type"
      let inputKind ← CompilerFactAdapters.castTypeInfo (facts p) input
      let matchesInput := match inputKind with
        | .fnDefinition source actual => kind == "resolve_fn_ptr" && source == definition && actual == args
        | .closure source actual _ => kind == "resolve_closure_fn_once" && source == definition && actual == args
        | _ => false
      if matchesInput then matching := matching.push record
  unique matching
private def decodeInstance (p : CompilerProviders.Prepared) (j : Json) : Result CallInstance := do
  let tables := p.program.compilerTables
  let (resolved,next) ← CompilerInstance.decode p.loweringContext tables j
  unless next.definitions == tables.definitions && next.typeConstants == tables.typeConstants do
    throw "cast resolution requires unprepared shared compiler identities"
  pure resolved

def resolveFunction (p : CompilerProviders.Prepared) (definition : DefId)
    (args : Array GenericArg) : Result (Option CallInstance) := do
  let result ← value (← resolutionRecord p "resolve_fn_ptr" definition args)
  if result == Json.null then pure none else pure (some (← decodeInstance p result))

def resolveClosureFnOnce (p : CompilerProviders.Prepared) (definition : DefId)
    (args : Array GenericArg) : Result CallInstance := do
  decodeInstance p (← value (← resolutionRecord p "resolve_closure_fn_once" definition args))

def noBoundVars (p : CompilerProviders.Prepared) (args : Array GenericArg) : Result Bool := do
  let mut evidence := #[]
  for record in ← records p do
    if (text record "query_kind").toOption == some "resolve_fn_ptr" then
      let input ← ref record "input_type"
      if let .fnDefinition _ actual ← CompilerFactAdapters.castTypeInfo (facts p) input then
        if actual == args then
          unless (← text record "typing_env") == "fully_monomorphized" do throw "no_bound_vars typing environment mismatch"
          evidence := evidence.push (← (← record.getObjVal? "args_no_bound_vars").getBool?)
  let some first := evidence[0]? | throw "missing exact generic arguments no_bound_vars query"
  unless evidence.all (· == first) do throw "conflicting no_bound_vars evidence"
  pure first

def lockstepTails (p : CompilerProviders.Prepared) (source target : TyId) : Result (TyId × TyId) := do
  let result ← value (← pairQuery p "lockstep_tails" source target)
  let source ← ref result "source_tail"
  let target ← ref result "target_tail"
  let _ ← layout p source
  let _ ← layout p target
  pure (source,target)

def boxLayout (p : CompilerProviders.Prepared) (pointee : TyId) : Result LocalLayout := do
  let result ← value (← query p "box_type" pointee)
  let id ← (← result.getObjVal? "type_id").getNat?
  layout p id

def supertraitSlot (p : CompilerProviders.Prepared) (source target : TyId) : Result (Option Nat) := do
  let result ← value (← pairQuery p "supertrait_slot" source target)
  if result == Json.null then pure none else pure (some (← result.getNat?))

private def principalValue (j : Json) : Result (Option Nat) := do
  let result ← j.getObjVal? "principal_predicate"
  if result == Json.null then pure none else pure (some (← (← result.getObjVal? "predicate_id").getNat?))

/-- Full predicate-list identity is the key. The principal is exported by the
compiler, not reconstructed by picking the first non-auto predicate. -/
def principal (p : CompilerProviders.Prepared) (token : Nat) : Result (Option Nat) := do
  let some predicates := (facts p).dynamicPredicates[token]? | throw "missing full dynamic predicate-list identity"
  let mut results := #[]
  for node in p.runtime.source.types do
    if node.shapeKind == .dynamicTraitObject then
      let shape ← node.payload.getObjVal? "shape"
      if (← shape.getObjVal? "predicates") == predicates then results := results.push (← principalValue shape)
  for allocation in p.program.input.allocations do
    if let some (.vtable source) := allocation.data then
      if (← source.payload.getObjVal? "predicates") == predicates then
        results := results.push (← principalValue source.payload)
  let some first := results[0]? | throw "missing compiler principal query for exact predicate list"
  unless results.all (· == first) do throw "conflicting compiler principal queries"
  pure first

def normalizePrincipal (p : CompilerProviders.Prepared) (token : Nat) : Result (Option Nat) := do
  let some id ← principal p token | return none
  let entries := p.program.input.compilerPredicates.filter (·.id == id)
  let some entry := entries[0]? | throw "missing principal predicate normalization evidence"
  unless entries.all (·.payload == entry.payload) do throw "conflicting principal normalization evidence"
  pure (some (← CompilerVTableFacts.normalizePredicate (facts p) ⟨id,entry.stableKey,entry.autoTrait⟩))

/-- The runtime VTableEntry representation stores the target principal. The
source relation is validated by the same exact allocation-to-query resolver
used to build that entry, including query-backed source vtables that do not
appear as `.vtable` nodes in the allocation graph. -/
def eraseSelfTraitRef (p : CompilerProviders.Prepared) (token : Nat) : Result Nat := do
  let runtime := p.lifecycle.calls.symbols
  for allocation in p.program.input.allocations do
    if let some (.vtable source) := allocation.data then
      for entry in source.entries do
        if entry.status == .supported && entry.kind == .supertraitVtablePointer then
          if (CompilerVTableRuntime.supertraitPrincipal runtime source.typeId entry).toOption == some token then
            return token
  let queryRows ← (← p.program.input.raw.getObjVal? "compiler_vtable_queries").getArr?
  for row in queryRows do
    let some metadata := (row.getObjVal? "vtable_metadata").toOption | continue
    unless (metadata.getObjValAs? String "status").toOption == some "supported" do continue
    let some typeRef := (row.getObjVal? "input_type").toOption | continue
    let some sourceType := (typeRef.getObjValAs? Nat "type_id").toOption | continue
    let some entryValues := ((metadata.getObjVal? "entries").bind Json.getArr?).toOption | continue
    for (entryValue, index) in entryValues.toList.zipIdx do
      let some entry := (Input.decodeVtableEntry entryValue
        s!"$.compiler_vtable_queries.vtable_metadata.entries[{index}]").toOption | continue
      if entry.status == .supported && entry.kind == .supertraitVtablePointer &&
          (CompilerVTableRuntime.supertraitPrincipal runtime sourceType entry).toOption == some token then
        return token
  throw "missing exact exported TraitVPtr erase_self_ty relation"
private def lift (query : Result A) : RvalueM S A :=
  match query with | .ok value => pure value | .error error => throw (.unsupported s!"cast compiler query: {error}")

def required (p : CompilerProviders.Prepared) : CompilerCastLeaves.Required S C where
  requireNoBoundVars := fun _ args => do
    unless ← lift (noBoundVars p args) do
      throw (.invalidProgram "source no_bound_vars assertion failed")
  resolveFunction := fun _ definition args => lift (resolveFunction p definition args)
  resolveClosureFnOnce := fun _ definition args => lift (resolveClosureFnOnce p definition args)
  lockstepTails := fun _ source target => lift (lockstepTails p source target)
  boxLayout := fun _ ty => lift (boxLayout p ty)
  principal := fun _ token => lift (principal p token)
  supertraitSlot := fun _ source target => lift (supertraitSlot p source target)
  eraseSelfTraitRef := fun _ token => lift (eraseSelfTraitRef p token)
  normalizePrincipal := fun _ token => lift (normalizePrincipal p token)

end Miri.Input.CompilerCastQueries
