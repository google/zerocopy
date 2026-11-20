import Miri.Input.CompilerInstance
import Miri.Input.CompilerExternAbi
import Miri.Interpreter.MainMachine

/-! eval.rs::call_main entry signature and lang_start queries. Original bound
variables, return type and Ty::new_fn_ptr identity are retained. Resolution is
keyed by the exact start DefId and complete source generic argument vector.
Link-section static reading remains a separate stateful global-memory query.
-/
namespace Miri.Input.CompilerMain
open Lean Miri.ABI Miri.Interpreter
structure Entry where
  definition : MIR.DefId
  parameters : Array MainGenericParameter
  signature : Except String MainSignature
  start : Except String (Option CallInstance)
structure Section where
  definition : MIR.DefId
  span : MIR.SpanRef
  ty : MIR.TyId
  allocation : AllocationId
structure SectionQuery where
  name : String
  result : Except String Section
structure Prepared where
  program : LoweredProgram
  runtime : RuntimeMetadata
  start : Option MIR.DefId
  compilerEntry : Option MIR.DefId
  /-- Exact rustc EntryFnType attached to tcx.entry_fn. When absent, the
  compiler did not select a Rust main and the source may use Miri's
  separately selected miri_start entry. -/
  compilerEntryType : Except String (Option (MIR.DefId × MainEntryType))
  entries : Array Entry
  sections : Except String (Array SectionQuery)
private def intern (tables : CompilerTables) (value : Json) : Except String (MIR.DefId × CompilerTables) := do
  let source : DefinitionId := ⟨← (← value.getObjVal? "crate").getNat?,← (← value.getObjVal? "index").getNat?⟩
  match lookupDefinitionId tables.definitions source with
  | .ok id => pure (id,tables)
  | .error _ => pure (tables.definitions.size,{tables with definitions := tables.definitions.push source})
private def supported (query : Json) : Except String Json := do
  unless (← (← query.getObjVal? "status").getStr?) == "supported" do throw "main compiler query is unresolved"
  query.getObjVal? "value"
private def typeId (context : LowerContext) (j : Json) : Except String MIR.TyId := do
  let id ← (← j.getObjVal? "type_id").getNat?
  unless context.containsTypeId id do throw "main compiler query references missing type"
  pure id

def prepare (runtime : RuntimeMetadata) (program : LoweredProgram)
    (sourceEquality : Option (RuntimeMetadata.JsonReflexivity runtime.source.raw) := none) : Except String Prepared := do
  unless RuntimeMetadata.JsonReflexivity.matchesRightOr sourceEquality program.input.raw do
    throw "main query metadata document mismatch"
  let source ← program.input.raw.getObjVal? "compiler_main_queries"
  unless (← (← source.getObjVal? "typing_env").getStr?) == "fully_monomorphized" do throw "main query environment mismatch"
  let ctx := LowerContext.ofDocument program.input
  let mut tables := program.compilerTables
  let startSource ← source.getObjVal? "start_lang_item"
  let start ← if startSource == .null then pure none else do
    let (id,next) ← intern tables startSource
    tables := next
    pure (some id)
  let entrySource ← source.getObjVal? "compiler_entry"
  let compilerEntry ← if entrySource == .null then pure none else do
    let (id,next) ← intern tables entrySource
    tables := next
    pure (some id)
  let compilerEntryType : Except String (Option (MIR.DefId × MainEntryType)) := do
    match source.getObjVal? "compiler_entry_type" with
      | .error _ =>
        if compilerEntry.isSome then throw "rustc selected main lacks exact EntryFnType query"
        else pure none
      | .ok query => do
        let value ← supported query
        if value == .null then
          if compilerEntry.isSome then throw "rustc selected main lacks exact EntryFnType"
          pure none
        else do
          let definitionJson ← value.getObjVal? "definition"
          let sourceDefinition : DefinitionId := ⟨
            ← (← definitionJson.getObjVal? "crate").getNat?,
            ← (← definitionJson.getObjVal? "index").getNat?⟩
          let definition ← lookupDefinitionId tables.definitions sourceDefinition
          unless compilerEntry == some definition do
            throw "rustc EntryFnType definition differs from compiler-selected entry"
          let kind ← (← value.getObjVal? "kind").getStr?
          unless kind == "rustc_main" do throw s!"unsupported rustc EntryFnType `{kind}`"
          let sigpipe ← (← value.getObjVal? "sigpipe").getNat?
          unless sigpipe <= 255 do throw "rustc EntryFnType sigpipe does not fit u8"
          pure (some (definition,.rustcMain (UInt8.ofNat sigpipe)))
  let mut entries : Array Entry := #[]
  for record in ← (← source.getObjVal? "entries").getArr? do
    let (definition,next) ← intern tables (← record.getObjVal? "definition")
    tables := next
    if entries.any (·.definition == definition) then throw "duplicate source main definition key"
    let parameters ← (← (← record.getObjVal? "generic_parameters").getArr?).mapM fun value => do
      match ← value.getStr? with
      | "lifetime" => pure MainGenericParameter.lifetime
      | "type_parameter" => pure .typeParameter | "const_parameter" => pure .constParameter
      | _ => throw "unknown main generic parameter kind"
    let signature := do
      let value ← supported (← record.getObjVal? "signature_query")
      pure (⟨← (← value.getObjVal? "has_bound_variables").getBool?,
        ← (← value.getObjVal? "output_has_bound_variables").getBool?,
        ← typeId ctx (← value.getObjVal? "return_type"),
        ← typeId ctx (← value.getObjVal? "function_pointer_type")⟩ : MainSignature)
    let resolution := do
      let value ← supported (← record.getObjVal? "signature_query")
      unless (← (← value.getObjVal? "compiler_selected_entry").getBool?) do
        throw "lang_start query not requested for a non-compiler-selected entry"
      supported (← value.getObjVal? "start_resolution")
    let outcome : Except String (Option CallInstance) ← match resolution with
      | .error error => pure (.error error)
      | .ok value =>
        if value == .null then pure (.ok none) else
          match CompilerInstance.decode ctx tables value with
          | .error error => pure (.error error)
          | .ok (callee,next) => tables := next; pure (.ok (some callee))
    entries := entries.push ⟨definition,parameters,signature,outcome⟩
  let sectionSources := do (← supported (← source.getObjVal? "link_sections")).getArr?
  let mut sections : Array SectionQuery := #[]
  let sectionsResult : Except String (Array SectionQuery) ← match sectionSources with
    | .error error => pure (.error error)
    | .ok records =>
      for record in records do
        let name ← (← record.getObjVal? "section").getStr?
        let decoded := do
          let (definition,next) ← intern tables (← record.getObjVal? "definition")
          let (span,next) ← lowerCompilerSpan next (← ctx.decodeCompilerValue (← record.getObjVal? "span"))
          let value ← supported (← record.getObjVal? "global_query")
          let ty ← typeId ctx (← value.getObjVal? "type")
          let allocation ← (← (← value.getObjVal? "allocation").getObjVal? "allocation_id").getNat?
          unless ctx.containsAllocationId allocation do throw "link-section static allocation missing from compiler graph"
          pure ((⟨definition,span,ty,allocation⟩ : Section),next)
        let result ← match decoded with
          | .error error => pure (.error error)
          | .ok (value,next) => tables := next; pure (.ok value)
        sections := sections.push ⟨name,result⟩
      pure (.ok sections)
  pure ⟨program.withCompilerTables tables,runtime,start,compilerEntry,compilerEntryType,entries,sectionsResult⟩
private def entry (p : Prepared) (definition : MIR.DefId) : Except String Entry := do
  let some entry := p.entries.find? (·.definition == definition) | throw "missing exact source main entry query"
  pure entry

def resolve (p : Prepared) (definition : MIR.DefId) (args : Array MIR.GenericArg) : Except String (Option CallInstance) := do
  unless p.start == some definition do throw "main resolution request is not the actual start lang item"
  let some entryId := p.compilerEntry | throw "source compiler has no executable entry"
  let entry ← entry p entryId
  let signature ← entry.signature
  unless args == #[.Type signature.returnType] do throw "missing exact lang_start argument-vector query"
  entry.start

/-- Exact compiler-selected ordinary entry metadata for the source startup
factory. `none` is retained for the separate MiriStart entry path. -/
def sourceCompilerEntry (p : Prepared) : Except String (Option (MIR.DefId × MainEntryType)) :=
  p.compilerEntryType

private def lift (value : Except String A) : MainMachine.M U A :=
  match value with | .ok value => pure value | .error error => throw (.unsupported error)

def hooks (p : Prepared) (base : MainMachine.Hooks U C O ABI.ExternAbi F A Aff P) :
    MainMachine.Hooks U C O ABI.ExternAbi F A Aff P :=
  {base with
    cNoUnwind := .C false
    genericParameters := fun id => lift do return (← entry p id).parameters
    entrySignature := fun id => lift do (← entry p id).signature
    startLangItem := pure p.start
    resolveInstance := fun id args => lift (resolve p id args)
    layoutOf := fun ty => lift (p.runtime.lookup ty |>.mapError toString)}
end Miri.Input.CompilerMain
