import Miri.Input.CompilerLinkSections

/-! helpers.rs::eval_path and eval_context.rs::eval_global for exact named
libc globals used by pthread synchronization. Query identity is the full source
path; static and const allocations are materialized through the canonical
allocation image and root-pointer operations. -/
namespace Miri.Input.CompilerNamedGlobals
open Lean Miri.ABI Miri.Memory Miri.Interpreter

structure Value where
  definition : MIR.DefId
  ty : MIR.TyId
  allocation : AllocationId
  isStatic : Bool

structure Entry where
  name : String
  result : Except String Value
  payload : Json

structure Prepared where
  program : LoweredProgram
  runtime : RuntimeMetadata
  entries : Array Entry

private def field (j : Json) (key : String) : Except String Json := j.getObjVal? key

private def supported (j : Json) : Except String Json := do
  unless (← (← field j "status").getStr?) == "supported" do
    throw s!"named compiler global unavailable: {((field j "reason").bind Json.getStr?).toOption}"
  field j "value"

private def definition (tables : CompilerTables) (raw : Json) :
    Except String (MIR.DefId × CompilerTables) := do
  let source : DefinitionId := ⟨← (← field raw "crate").getNat?, ← (← field raw "index").getNat?⟩
  match lookupDefinitionId tables.definitions source with
  | .ok id => pure (id, tables)
  | .error _ => pure (tables.definitions.size, {tables with definitions := tables.definitions.push source})

private def sourcePath (record : Json) (name : String) : Except String Unit := do
  let parts ← (← field record "path").getArr?
  unless parts.size == 2 do throw "named compiler global path must be exactly libc::<name>"
  let some first := parts[0]? | throw "named compiler global path is missing its crate component"
  let some second := parts[1]? | throw "named compiler global path is missing its item component"
  unless (← first.getStr?) == "libc" && (← second.getStr?) == name do
    throw "named compiler global path must be exactly libc::<name>"
  pure ()

private def decodeValue (ctx : LowerContext) (tables : CompilerTables) (record : Json) (name : String) :
    Except String (Value × CompilerTables) := do
  let query ← field record "query"
  let payload ← supported query
  let (defId, tables) ← definition tables (← field payload "definition")
  let kind ← (← field payload "kind").getStr?
  let isStatic ← match kind with
    | "static" => pure true
    | "const_allocation" => pure false
    | _ => throw s!"named compiler global {name} has unknown allocation kind `{kind}`"
  let ty ← (← (← field payload "type").getObjVal? "type_id").getNat?
  unless ctx.containsTypeId ty do throw "named compiler global references absent compiler type"
  let allocation ← (← (← field payload "allocation").getObjVal? "allocation_id").getNat?
  unless ctx.containsAllocationId allocation do throw "named compiler global references absent allocation image"
  pure (⟨defId, ty, allocation, isStatic⟩, tables)

/-- Retain every exact path query, including unavailable rows. Failed queries
are raised only when the corresponding source path is demanded. -/
def prepare (runtime : RuntimeMetadata) (program : LoweredProgram)
    (sourceEquality : Option (RuntimeMetadata.JsonReflexivity runtime.source.raw) := none) : Except String Prepared := do
  unless RuntimeMetadata.JsonReflexivity.matchesRightOr sourceEquality program.input.raw do
    throw "named global metadata document mismatch"
  let records ← (← program.input.raw.getObjVal? "compiler_named_statics").getArr?
  let ctx := LowerContext.ofDocument program.input
  let mut tables := program.compilerTables
  let mut entries := #[]
  for record in records do
    let name ← (← field record "name").getStr?
    sourcePath record name
    unless (← (← field record "typing_env").getStr?) == "fully_monomorphized" do
      throw "named global compiler environment mismatch"
    unless !(entries.any (·.name == name)) do throw "duplicate compiler named global query"
    let result := (decodeValue ctx tables record name).map fun (value, next) => (value, next)
    let result ← match result with
      | .error reason => pure (.error reason)
      | .ok (value, next) => tables := next; pure (.ok value)
    entries := entries.push ⟨name, result, record⟩
  pure ⟨program.withCompilerTables tables, runtime, entries⟩

private def value (prepared : Prepared) (name : String) : Except String Value := do
  let some entry := prepared.entries.find? (·.name == name)
    | throw s!"missing exact compiler named global query libc::{name}"
  entry.result

private def lift (query : Except String A) : MachineHooks.M K U A :=
  match query with
  | .ok value => pure value
  | .error reason => throw (.unsupported reason)

/-- Execute the source global-root-pointer query using the imported compiler
allocation and ordinary extern/static pointer hooks. No name or byte-content
lookup substitutes for the exact compiler row. -/
def global (prepared : Prepared) (memory : CompilerLinkSections.Memory K U Other)
    (name : String) : MachineHooks.M K U (MPlaceTy Provenance) := do
  let entry ← lift (value prepared name)
  let operand ← CompilerLinkSections.globalRef prepared.runtime memory
    ⟨entry.definition, entry.ty, entry.allocation, entry.isStatic⟩
  match operand.op with
  | .indirect place => pure ⟨place, operand.layout⟩
  | .immediate _ => throw (.invalidProgram "source eval_global named initializer did not produce an indirect place")

end Miri.Input.CompilerNamedGlobals
