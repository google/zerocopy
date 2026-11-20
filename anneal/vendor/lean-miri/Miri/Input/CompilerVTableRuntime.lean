import Miri.Input.CompilerVirtualFacts
import Miri.Input.CompilerInstance

/-! Actual imported GlobalAlloc::Function/VTable identity leaves. Runtime
allocation IDs are resolved through AllocationImage's mapping, never equated
with exported IDs. Complete instances share the program's compiler tables. -/
namespace Miri.Input.CompilerVTableRuntime
open Lean Miri.Memory Miri.Interpreter
abbrev Result := Except String

structure InstanceEvidence where
  id : InstanceId
  outcome : Result CallInstance

structure ArrayReflexivity {α : Type} [BEq α] (values : Array α) where
  private mk ::
  private checked : Option (PLift ((values == values) = true))

private def ArrayReflexivity.prepare {α : Type} [BEq α] (values : Array α) : ArrayReflexivity values :=
  ⟨if h : values == values then some ⟨h⟩ else none⟩

private def ArrayReflexivity.matchesRight {α : Type} [BEq α] {values : Array α}
    (certificate : ArrayReflexivity values) (candidate : Array α) : Bool :=
  match certificate.checked with
  | none => values == candidate
  | some ⟨reflexive⟩ =>
    withPtrEq values candidate (fun _ => values == candidate)
      (by intro equal; cases equal; exact reflexive)

structure Prepared where
  facts : CompilerFactAdapters.Prepared
  instances : Array InstanceEvidence
  obligations : Array Obligation

/-- Decode every registered instance, including callable shims without MIR.
Body availability is not required to establish the full function identity.
Missing identity evidence remains a per-instance error, not a guessed Item. -/
def prepare (facts : CompilerFactAdapters.Prepared) : Prepared := Id.run do
  let program := facts.context.program
  let ctx := facts.context.loweringContext
  let mut tables := program.compilerTables
  let mut instances := #[]
  let mut obligations := #[]
  for source in program.input.instances do
    let outcome := CompilerInstance.decode ctx tables source.payload
    match outcome with
    | .ok (fnInstance,next) =>
      tables := next
      instances := instances.push ⟨source.id,.ok fnInstance⟩
    | .error error =>
      instances := instances.push ⟨source.id,.error error⟩
      obligations := obligations.push ⟨s!"instances[{source.id}].vtable_runtime",error⟩
  let context := facts.context.withProgram (program.withCompilerTables tables)
  return ⟨{ facts with context },instances,obligations⟩

structure GlobalLookup (prepared : Prepared) where
  private mk ::
  private instanceRows : Array InstanceEvidence
  private instanceBuckets : Std.HashMap Nat (Array InstanceEvidence)
  private exactInstances : instanceRows = prepared.instances
  private definitionRows : Array DefinitionId
  private definitionIndex : Std.HashMap (Nat × Nat) Nat
  private exactDefinitions : definitionRows = prepared.facts.context.program.compilerTables.definitions
  private definitionReflexivity : ArrayReflexivity definitionRows
  private typeConstantRows : Array MIR.TypeConst
  private exactTypeConstants : typeConstantRows = prepared.facts.context.program.compilerTables.typeConstants
  private typeConstantReflexivity : ArrayReflexivity typeConstantRows

def GlobalLookup.prepare (prepared : Prepared) : GlobalLookup prepared := Id.run do
  let instanceRows := prepared.instances
  let mut instanceBuckets : Std.HashMap Nat (Array InstanceEvidence) := {}
  for evidence in instanceRows do
    let bucket := (instanceBuckets[evidence.id]?).getD #[]
    instanceBuckets := instanceBuckets.insert evidence.id (bucket.push evidence)
  let definitionRows := prepared.facts.context.program.compilerTables.definitions
  let mut definitionIndex : Std.HashMap (Nat × Nat) Nat := {}
  for (definition, index) in definitionRows.toList.zipIdx do
    let key := (definition.crateIndex, definition.index)
    if !(definitionIndex.contains key) then
      definitionIndex := definitionIndex.insert key index
  let typeConstantRows := prepared.facts.context.program.compilerTables.typeConstants
  return ⟨instanceRows,instanceBuckets,rfl,definitionRows,definitionIndex,rfl,
    ArrayReflexivity.prepare definitionRows,typeConstantRows,rfl,
    ArrayReflexivity.prepare typeConstantRows⟩

def functionInstanceUsing (prepared : Prepared) (lookup : GlobalLookup prepared)
    (id : InstanceId) : Result CallInstance := do
  let candidates := (lookup.instanceBuckets[id]?).getD #[]
  unless candidates.size == 1 do throw "missing or ambiguous complete compiler function instance"
  let some value := candidates[0]? | throw "compiler function instance missing"
  value.outcome

def functionInstance (prepared : Prepared) (id : InstanceId) : Result CallInstance := do
  -- Manual construction keeps the original source-order scan; hot source
  -- startup and runtime hooks use one checked GlobalLookup view instead.
  let candidates := prepared.instances.filter (·.id == id)
  unless candidates.size == 1 do throw "missing or ambiguous complete compiler function instance"
  let some value := candidates[0]? | throw "compiler function instance missing"
  value.outcome

private def lookupDefinitionId (lookup : GlobalLookup prepared) (sourceId : DefinitionId) : Result MIR.DefId := do
  match lookup.definitionIndex[(sourceId.crateIndex, sourceId.index)]? with
  | some id => pure id
  | none => throw s!"unresolved compiler definition {sourceId.crateIndex}:{sourceId.index}"

/-- None means a known non-symbolic-function/vtable allocation. Missing image
metadata for an allocation declared symbolic is unresolved evidence, not None. -/
private def sourceNode (image : AllocationImage.Imported) (memory : MemoryState P E K)
    (id : AllocId) : Result (Option AllocationNode) := do
  if memory.hasImportedRuntimeId id then
    return some (← image.sourceNode memory id)
  let info ← (memory.getAllocInfo id).mapError fun error => reprStr error
  if info.kind == .function || info.kind == .vtable then
    throw "symbolic allocation has no imported compiler identity"
  return none

def globalFunctionUsing (prepared : Prepared) (lookup : GlobalLookup prepared)
    (image : AllocationImage.Imported)
    (memory : MemoryState P E K) (id : AllocId) : Result (Option CallInstance) := do
  let some node ← sourceNode image memory id | return none
  let some (.function source) := node.data | return none
  let fnInstance ← functionInstanceUsing prepared lookup source.instanceId
  let tables := prepared.facts.context.program.compilerTables
  let definition ← lookupDefinitionId lookup source.definitionId
  unless fnInstance.defId == definition do throw "global function/full-instance definition mismatch"
  let (args,next) ← lowerCompilerGenericArgs prepared.facts.context.loweringContext
    tables source.genericArgs
  unless ArrayReflexivity.matchesRight lookup.definitionReflexivity next.definitions &&
      ArrayReflexivity.matchesRight lookup.typeConstantReflexivity next.typeConstants do
    throw "global function arguments require unprepared compiler identities"
  unless args == fnInstance.args do throw "global function/full-instance generic arguments mismatch"
  return some fnInstance

def globalFunction (prepared : Prepared) (image : AllocationImage.Imported)
    (memory : MemoryState P E K) (id : AllocId) : Result (Option CallInstance) :=
  globalFunctionUsing prepared (GlobalLookup.prepare prepared) image memory id

def globalVTable (prepared : Prepared) (image : AllocationImage.Imported)
    (memory : MemoryState P E K) (id : AllocId) : Result (Option (MIR.TyId × Nat)) := do
  let some node ← sourceNode image memory id | return none
  let some (.vtable source) := node.data | return none
  let _ ← prepared.facts.context.runtime.node source.typeId |>.mapError toString
  let predicates ← source.payload.getObjVal? "predicates"
  let token ← CompilerVTableFacts.exportedArrayToken prepared.facts predicates
  return some (source.typeId,token)

def globalVTableUsing (prepared : Prepared) (_lookup : GlobalLookup prepared)
    (image : AllocationImage.Imported) (memory : MemoryState P E K) (id : AllocId) :
    Result (Option (MIR.TyId × Nat)) :=
  globalVTable prepared image memory id

private def principal (source : VtableAllocation) : Result (Option Nat) := do
  let value ← source.payload.getObjVal? "principal_predicate"
  if value == Json.null then return none
  return some (← (← value.getObjVal? "predicate_id").getNat?)

/-- vtable_allocation is queried with an instantiated principal, unlike a
symbolic vtable's full higher-ranked predicate list. Use the compiler's exact
late-bound-erasure/normalization evidence; never compare names or discard the
predicate identity on the original symbolic query. -/
private def allocationPrincipal (facts : CompilerFactAdapters.Prepared)
    (value : Json) : Result (Nat × Json) := do
  let id ← value.getObjValAs? Nat "predicate_id"
  let sources := facts.context.program.input.compilerPredicates.filter (·.id == id)
  let some source := sources[0]? | throw "memory-backed vtable principal normalization evidence missing"
  unless sources.all (·.payload == source.payload) && source.original == value do
    throw "memory-backed vtable principal conflicts with normalization evidence"
  let normalized ← CompilerVTableFacts.normalizePredicate facts ⟨id,source.stableKey,source.autoTrait⟩
  let targets := facts.context.program.input.compilerPredicates.filter (·.id == normalized)
  let some target := targets[0]? | throw "normalized memory-backed vtable principal evidence missing"
  unless targets.all (·.payload == target.payload) &&
      (target.original.getObjValAs? String "status").toOption == some "supported" &&
      (target.original.getObjValAs? String "kind").toOption == some "trait" do
    throw "normalized memory-backed vtable principal evidence conflicts"
  return (normalized, target.original)

/-- Resolve a memory-backed vtable through the exact compiler allocation ID
recorded for a principal/type query. Query metadata alone is not enough: the
source TraitVPtr allocation must equal this ID. Each row must agree with its
complete predicate key, while rows sharing the allocation must agree on the
allocation's type, compiler-normalized principal, layout, and entries. A named
HRTB and its instantiated principal can legitimately share this memory image;
their symbolic type/predicate/salt keys remain distinct. -/
def queryTargetPrincipal (facts : CompilerFactAdapters.Prepared)
    (raw : Json) (sourceType allocationId : Nat) : Result Nat := do
  let queryRows ← (← raw.getObjVal? "compiler_vtable_queries").getArr?
  let mut found : Option (Nat × Json) := none
  for (row, rowIndex) in queryRows.toList.zipIdx do
    unless (row.getObjValAs? Nat "vtable_allocation_id").toOption == some allocationId do
      continue
    let rowType ← (← (← row.getObjVal? "input_type").getObjVal? "type_id").getNat?
    unless rowType == sourceType do
      throw "memory-backed supertrait target compiler type mismatch"
    let some metadata := (row.getObjVal? "vtable_metadata").toOption
      | throw s!"compiler vtable target row {rowIndex} lacks metadata"
    unless (row.getObjValAs? String "status").toOption == some "supported" &&
        (metadata.getObjValAs? String "status").toOption == some "supported" &&
        (metadata.getObjValAs? String "layout_status").toOption == some "supported" do
      throw s!"compiler vtable target row {rowIndex} has unresolved metadata"
    let metadataType ← metadata.getObjVal? "type"
    unless ((metadataType.getObjValAs? Nat "type_id").toOption == some sourceType) do
      throw "memory-backed supertrait target metadata type mismatch"
    let metadataPredicates ← (metadata.getObjVal? "predicates").bind Json.getArr?
    let rowPredicates ← (row.getObjVal? "input_predicates").bind Json.getArr?
    unless metadataPredicates == rowPredicates do
      throw "memory-backed supertrait target predicates disagree with query key"
    let principalPredicate ← metadata.getObjVal? "principal_predicate"
    unless principalPredicate != Json.null &&
        (principalPredicate.getObjValAs? String "status").toOption == some "supported" &&
        (principalPredicate.getObjValAs? String "kind").toOption == some "trait" do
      throw "memory-backed supertrait target has no supported principal trait"
    let (targetPrincipal, allocationPredicate) ← allocationPrincipal facts principalPredicate
    let entries ← metadata.getObjVal? "entries"
    let _ ← entries.getArr?
    let size ← (metadata.getObjVal? "size_bytes").bind Json.getNat?
    let align ← (metadata.getObjVal? "align_bytes").bind Json.getNat?
    let evidence := Json.mkObj [
      ("type", metadataType),
      ("principal_predicate", allocationPredicate),
      ("status", .str "supported"),
      ("layout_status", .str "supported"),
      ("size_bytes", toJson size),
      ("align_bytes", toJson align),
      ("entries", entries)]
    if let some (previousPrincipal, previousEvidence) := found then
      unless previousPrincipal == targetPrincipal && previousEvidence == evidence do
        throw "conflicting compiler vtable rows for exact allocation identity"
    else
      found := some (targetPrincipal, evidence)
  let some (targetPrincipal, _) := found
    | throw "exact compiler vtable query for supertrait allocation is missing"
  return targetPrincipal

/-- Recover the target principal only through the exact serialized compiler
allocation identity. A direct `.vtable` node carries its own type/principal;
rustc may instead serialize the same global allocation as memory, in which
case the query row's `vtable_allocation_id` is the required identity join. -/
def supertraitPrincipal (prepared : Prepared) (sourceType : MIR.TyId)
    (entry : Input.VtableEntry) : Result Nat := do
  unless entry.status == .supported && entry.kind == .supertraitVtablePointer do
    throw "supertrait vtable entry is unresolved"
  let some sourceId := entry.allocationId | throw "supertrait vtable source allocation missing"
  let nodes := prepared.facts.context.program.input.allocations.filter (·.id == sourceId)
  unless nodes.size == 1 do throw "supertrait vtable allocation identity is missing or ambiguous"
  let some target := nodes[0]? | throw "supertrait vtable allocation evidence missing"
  unless target.status == .supported do throw "supertrait vtable allocation is unresolved"
  match target.kind, target.data with
  | .vtable, some (.vtable vtable) =>
    unless vtable.typeId == sourceType do throw "supertrait vtable concrete type mismatch"
    let some targetPrincipal ← principal vtable
      | throw "supertrait vtable has no principal"
    return targetPrincipal
  | .memory, some (.memory _) =>
    queryTargetPrincipal prepared.facts prepared.facts.context.program.input.raw sourceType sourceId
  | _, _ => throw "supertrait allocation is neither a compiler vtable nor its memory image"

private def methodInstanceUsing (prepared : Prepared) (lookup : GlobalLookup prepared)
    (entry : Input.VtableEntry) : Result CallInstance := do
  let some id := entry.instanceId | throw "vtable method complete instance ID missing"
  let fnInstance ← functionInstanceUsing prepared lookup id
  let some definition := entry.definitionId | throw "vtable method definition evidence missing"
  let tables := prepared.facts.context.program.compilerTables
  let actualDefinition ← lookupDefinitionId lookup definition
  unless actualDefinition == fnInstance.defId do throw "vtable method/full-instance definition mismatch"
  let some args := entry.genericArgs | throw "vtable method generic arguments missing"
  let (args,next) ← lowerCompilerGenericArgs prepared.facts.context.loweringContext tables args
  unless ArrayReflexivity.matchesRight lookup.definitionReflexivity next.definitions &&
      ArrayReflexivity.matchesRight lookup.typeConstantReflexivity next.typeConstants do
    throw "vtable method arguments require unprepared identities"
  unless args == fnInstance.args do throw "vtable method/full-instance arguments mismatch"
  return fnInstance

private def entryValueUsing (prepared : Prepared) (lookup : GlobalLookup prepared)
    (sourceType : MIR.TyId)
    (entry : Input.VtableEntry) : Result (Interpreter.VTableEntry CallInstance) := do
  unless entry.status == .supported do throw "compiler vtable entry unresolved"
  match entry.kind with
  | .dropInPlace | .dropInPlaceNull => return .dropInPlace
  | .sizeBytes => return .size
  | .alignBytes => return .align
  | .vacant => return .vacant
  | .method => return .method (← methodInstanceUsing prepared lookup entry)
  | .supertraitVtablePointer =>
    let token ← supertraitPrincipal prepared sourceType entry
    return .traitVPtr token
  | .unknown tag => throw s!"unknown compiler vtable entry {tag}"

/-- Actual compiler vtable_entries result keyed by its concrete type and exact
compiler principal. Repeated symbolic allocations must provide identical query
results; allocation-ID coincidence and type-size inference are never keys. -/
def entriesUsing (prepared : Prepared) (lookup : GlobalLookup prepared)
    (expectedPrincipal : Option Nat) (ty : MIR.TyId) :
    Result (Array (Interpreter.VTableEntry CallInstance)) := do
  let mut found : Option (Array Input.VtableEntry) := none
  for node in prepared.facts.context.program.input.allocations do
    if let some (.vtable source) := node.data then
      if source.typeId == ty then
        if (← principal source) == expectedPrincipal then
          if let some previous := found then
            unless previous.map (·.payload) == source.entries.map (·.payload) do
              throw "conflicting compiler vtable_entries queries"
          else found := some source.entries
  let raw := prepared.facts.context.program.input.raw
  let queryRows ← (← raw.getObjVal? "compiler_vtable_queries").getArr?
  for (row, rowIndex) in queryRows.toList.zipIdx do
    let some rowType := (row.getObjVal? "input_type").toOption | continue
    unless ((rowType.getObjValAs? Nat "type_id").toOption == some ty) do continue
    let some metadata := (row.getObjVal? "vtable_metadata").toOption | continue
    let predicate := (metadata.getObjVal? "principal_predicate").toOption.getD .null
    let rowPrincipal ← if predicate == .null then pure none else
      (predicate.getObjVal? "predicate_id").bind Json.getNat? |>.map some
    unless rowPrincipal == expectedPrincipal do continue
    unless (row.getObjValAs? String "status").toOption == some "supported" &&
        (metadata.getObjValAs? String "status").toOption == some "supported" &&
        (metadata.getObjValAs? String "layout_status").toOption == some "supported" do
      throw s!"compiler vtable query row {rowIndex} has unresolved runtime metadata"
    let metadataPredicates ← (metadata.getObjVal? "predicates").bind Json.getArr?
    let rowPredicates ← (row.getObjVal? "input_predicates").bind Json.getArr?
    unless metadataPredicates == rowPredicates do
      throw "compiler vtable metadata predicate identity disagrees with its query key"
    let metadataType ← metadata.getObjVal? "type"
    unless ((metadataType.getObjValAs? Nat "type_id").toOption == some ty) do
      throw "compiler vtable metadata type disagrees with its query key"
    let entryJson ← (metadata.getObjVal? "entries").bind Json.getArr?
    let mut sourceEntries := #[]
    for (entry, index) in entryJson.toList.zipIdx do
      sourceEntries := sourceEntries.push (← Input.decodeVtableEntry entry
        s!"$.compiler_vtable_queries[{rowIndex}].vtable_metadata.entries[{index}]")
    if let some previous := found then
      unless previous.map (·.payload) == sourceEntries.map (·.payload) do
        throw "conflicting source compiler vtable_entries query metadata"
    else found := some sourceEntries
  let some source := found | throw "exact compiler principal/type vtable_entries query missing"
  source.mapM (entryValueUsing prepared lookup ty)

def entries (prepared : Prepared) (expectedPrincipal : Option Nat) (ty : MIR.TyId) :
    Result (Array (Interpreter.VTableEntry CallInstance)) :=
  entriesUsing prepared (GlobalLookup.prepare prepared) expectedPrincipal ty

private def lift (value : Result A) : EStateM StepError S A :=
  match value with
  | .ok value => pure value
  | .error error => throw (.unsupported s!"compiler symbolic allocation query: {error}")

/-- Install imported symbolic allocation queries with canonical machine memory.
Address resolution and vtable-entry/principal queries remain required leaves;
this does not manufacture them from the selected pointer's bytes. -/
def hooks (prepared : Prepared) (image : AllocationImage.Imported)
    (memory : S → MemoryState P E K) (base : VTableHooks P S C CallInstance Abi) :
    VTableHooks P S C CallInstance Abi := Id.run do
  let lookup := GlobalLookup.prepare prepared
  { base with
    entries := fun _ principal ty => lift (entriesUsing prepared lookup principal ty)
    globalFunction := fun _ id => do lift (globalFunctionUsing prepared lookup image (memory (← get)) id)
    globalVTable := fun _ id => do lift (globalVTable prepared image (memory (← get)) id) }

end Miri.Input.CompilerVTableRuntime
