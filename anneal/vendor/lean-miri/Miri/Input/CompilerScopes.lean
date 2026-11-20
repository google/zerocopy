import Miri.Input.CompilerInstance
import Miri.Interpreter.VirtualCalls

/-! Exact SourceScopeData evidence for Body::caller_location_span (mir/mod.rs).
Body indices are explicit source identities; structural Body equality is never
used to discover an identity. Legacy absent inline metadata fails closed. -/
namespace Miri.Input.CompilerScopes
open Lean Miri.Interpreter
structure Entry where
  scope : VirtualCalls.CallerScope
  trackCaller : Option Bool
structure Prepared where
  program : LoweredProgram
  scopes : Array (Array (Except String Entry))
private def decodeEntry (ctx : LowerContext) (tables : CompilerTables) (j : Json) :
    Except String (Entry × CompilerTables) := do
  let inlined ← j.getObjVal? "inlined"
  let parent ← j.getObjVal? "inlined_parent_scope"
  let parent ← if parent == Json.null then pure none else parent.getNat? |>.map some
  if inlined == Json.null then
    pure (⟨⟨none,parent⟩,none⟩,tables)
  else
    let (fnInstance,tables) ← CompilerInstance.decode ctx tables inlined
    let span ← ctx.decodeCompilerValue (← inlined.getObjVal? "callsite_span")
    let (span,tables) ← lowerCompilerSpan tables span
    let track ← (← inlined.getObjVal? "requires_caller_location").getBool?
    pure (⟨⟨some (fnInstance,span),parent⟩,some track⟩,tables)

def prepare (program : LoweredProgram) : Prepared := Id.run do
  let ctx := LowerContext.ofDocument program.input
  let mut tables := program.compilerTables
  let mut all := #[]
  for body in program.bundle.bodies do
    let mut entries := #[]
    match body.input.sourceScopes with
    | none => entries := #[.error "missing source_scopes compiler metadata"]
    | some scopes =>
      for index in [:scopes.size] do
        let result := do
          let some scope := scopes[index]? | throw "source scope canonical index missing"
          unless (← (← scope.getObjVal? "scope").getNat?) == index do
            throw "source scope index does not match canonical position"
          decodeEntry ctx tables scope
        match result with
        | .error e => entries := entries.push (.error e)
        | .ok (entry,next) =>
          tables := next
          entries := entries.push (.ok entry)
    all := all.push entries
  return ⟨program.withCompilerTables tables,all⟩

/-- The caller supplies the canonical body index from its frame identity map.
No fallback chooses a root, promoted body, or template by structural equality. -/
def sourceScope (prepared : Prepared) (bodyIndex scopeIndex : Nat) :
    Except String VirtualCalls.CallerScope := do
  let some scopes := prepared.scopes[bodyIndex]? | throw "unknown canonical body index"
  let some entry := scopes[scopeIndex]? | throw "unknown canonical source scope"
  pure (← entry).scope

/-- Full inlinecallee instances are the keys, including every generic argument. -/
def inlineRequiresCallerLocation (prepared : Prepared) (fnInstance : CallInstance) :
    Except String Bool := do
  let mut found := none
  for scopes in prepared.scopes do
    for entry in scopes do
      if let .ok entry := entry then
        if let some (callee,_) := entry.scope.inlined then
          if callee == fnInstance then
            let some track := entry.trackCaller | throw "missing inlinecallee track_caller query"
            if let some prior := found then
              unless prior == track do throw "conflicting inlinecallee track_caller query"
            found := some track
  let some result := found | throw "missing full-fnInstance requires_caller_location query"
  pure result
end Miri.Input.CompilerScopes
