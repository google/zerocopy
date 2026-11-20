import Miri.Input.CompilerLinkSections

/-! Exact compiler support for `machine.rs::extern_static_pointer`.
Declaration metadata is keyed by shared DefId identity. Exported-static
resolution retains the source-selected symbol winner and its allocation ID;
the winner is materialized only through the canonical imported global table.
-/
namespace Miri.Input.CompilerExternStatic
open Lean Miri.ABI Miri.Memory Miri.Interpreter

structure Declaration where
  definition : MIR.DefId
  symbol : String
  size : Size
  align : Align
  linkage : ExternStatic.ImportLinkage
  mutable : Bool
  result : Except String Unit
  deriving DecidableEq, Repr

structure Winner where
  definition : Option MIR.DefId
  kind : String
  allocation : Option AllocationId
  status : String
  reason : String

structure Selected where
  symbol : String
  winner : Winner

/-- Target attributes returned by rustc's parsed Session target. `families`
is the exact cfg family set; neither family nor environment is inferred from
the target triple. -/
structure TargetFacts where
  os : String
  env : String
  binaryFormat : String
  families : Array String
  deriving DecidableEq, Repr

structure Prepared where
  program : LoweredProgram
  runtime : RuntimeMetadata
  sourceStatus : Except String Unit
  targetFacts : Except String TargetFacts
  declarations : Array Declaration
  selected : Array Selected

private def field (j : Json) (key : String) : Except String Json := j.getObjVal? key
private def str (j : Json) (key : String) : Except String String := do
  (← field j key).getStr?
private def nat (j : Json) (key : String) : Except String Nat := do
  (← field j key).getNat?
private def statusResult (j : Json) : Except String Json := do
  match ← str j "status" with
  | "supported" => field j "value"
  | "unsupported" =>
    let reason := match (field j "reason").bind Json.getStr? with
      | .ok reason => reason
      | .error _ => "compiler extern-static query unavailable"
    throw reason
  | value => throw s!"unknown compiler extern-static status `{value}`"

private def definition (tables : CompilerTables) (raw : Json) :
    Except String (MIR.DefId × CompilerTables) := do
  let source : DefinitionId := ⟨← nat raw "crate", ← nat raw "index"⟩
  match lookupDefinitionId tables.definitions source with
  | .ok id => pure (id,tables)
  | .error _ => pure (tables.definitions.size,{tables with definitions := tables.definitions.push source})

private def linkage (raw : Json) : Except String ExternStatic.ImportLinkage := do
  let kind ← str raw "kind"
  match kind with
  | "none" => pure .none
  | "external_weak" => pure .externalWeak
  | "other" => pure .other
  | _ => throw s!"unknown compiler extern-static import linkage `{kind}`"

private def decodeDeclaration (ctx : LowerContext) (tables : CompilerTables) (raw : Json) :
    Except String (Declaration × CompilerTables) := do
  let (definitionId,tables) ← definition tables (← field raw "definition")
  let result := do
    unless (← str raw "status") == "supported" do
      let reason := match (field raw "reason").bind Json.getStr? with
        | .ok reason => reason
        | .error _ => "compiler extern-static declaration query unavailable"
      throw reason
    unless (← str raw "typing_env") == "fully_monomorphized" do
      throw "extern-static declaration has a non-canonical typing environment"
    let ty ← nat (← field raw "type") "type_id"
    unless ctx.containsTypeId ty do throw "extern-static declaration references absent compiler type"
    let layout ← field raw "layout"
    let size ← RuntimeMetadata.size (← nat layout "size_bytes") |>.mapError toString
    let align ← RuntimeMetadata.alignment (← nat layout "abi_align_bytes") |>.mapError toString
    let mutable ← (← field raw "decl_is_mut").getBool?
    let definitionMutability ← str raw "definition_mutability"
    let typeIsFreeze ← (← field raw "type_is_freeze").getBool?
    let sourceMutability ← match definitionMutability with
      | "mutable" => pure true
      | "immutable" => pure (!typeIsFreeze)
      | other => throw s!"unknown source static mutability `{other}`"
    unless mutable == sourceMutability do
      throw "extern-static declaration mutability disagrees with definition mutability and Freeze query"
    pure (← str raw "symbol",size,align,← linkage (← field raw "import_linkage"),mutable)
  let decoded ← match result with
    | .ok (symbol,size,align,linkage,mutable) =>
      pure ⟨definitionId,symbol,size,align,linkage,mutable,.ok ()⟩
    | .error reason =>
      let symbol := ((field raw "symbol").bind Json.getStr?).toOption.getD ""
      pure ⟨definitionId,symbol,.ZERO,.ONE,.other,false,.error reason⟩
  pure (decoded,tables)

private def selectedWinner (ctx : LowerContext) (tables : CompilerTables)
    (raw : Json) :
    Except String (Winner × CompilerTables) := do
  let status ← str raw "status"
  if status == "ambiguous" then
    return (⟨none,"ambiguous",none,status,((field raw "reason").bind Json.getStr?).toOption.getD "ambiguous exported symbol"⟩,tables)
  if status != "supported" then
    return (⟨none,"unknown",none,status,((field raw "reason").bind Json.getStr?).toOption.getD "exported symbol query unavailable"⟩,tables)
  let (definitionId,tables) ← definition tables (← field raw "definition")
  let kind ← str raw "kind"
  if kind != "static" then
    return (⟨some definitionId,kind,none,status,""⟩,tables)
  let (embedded,tables) ← decodeDeclaration ctx tables (← field raw "declaration")
  unless embedded.definition == definitionId do
    throw "selected exported static declaration DefId differs from its winner"
  unless embedded.symbol == (← str raw "symbol") do
    throw "selected exported static declaration symbol differs from its winner"
  -- The exported definition is a distinct compiler item from the foreign
  -- declaration that demanded this symbol. `declarations` records only the
  -- latter; the selected winner carries its own exact declaration facts.
  if let .error reason := embedded.result then
    return (⟨some definitionId,kind,none,"unsupported",reason⟩,tables)
  let allocationResult := do
    let allocation ← statusResult (← field raw "allocation")
    let id ← nat allocation "allocation_id"
    unless ctx.containsAllocationId id do throw "selected exported static allocation is absent from compiler graph"
    pure id
  let allocation ← match allocationResult with
    | .ok id => pure (some id)
    | .error reason =>
      return (⟨some definitionId,kind,none,"unsupported",reason⟩,tables)
  return (⟨some definitionId,kind,allocation,status,""⟩,tables)

def prepare (runtime : RuntimeMetadata) (program : LoweredProgram)
    (sourceEquality : Option (RuntimeMetadata.JsonReflexivity runtime.source.raw) := none) : Except String Prepared := do
  unless RuntimeMetadata.JsonReflexivity.matchesRightOr sourceEquality program.input.raw do
    throw "extern-static metadata document mismatch"
  let ctx := LowerContext.ofDocument program.input
  let sourceResult := do
    let queries ← field program.input.raw "compiler_runtime_queries"
    let foreign ← field queries "foreign_symbols"
    let source ← field foreign "extern_statics"
    let source ← statusResult source
    unless (← str source "typing_env") == "fully_monomorphized" do
      throw "extern-static table has a non-canonical typing environment"
    pure source
  let targetResult := do
    let queries ← field program.input.raw "compiler_runtime_queries"
    let foreign ← field queries "foreign_symbols"
    let target ← statusResult (← field foreign "target")
    let os ← str target "os"
    let env ← str target "env"
    let binaryFormat ← str target "binary_format"
    let families ← (← field target "families").getArr?
    let mut parsed := #[]
    for family in families do
      let family ← family.getStr?
      if parsed.contains family then throw "duplicate rustc target family"
      parsed := parsed.push family
    pure ⟨os,env,binaryFormat,parsed⟩
  match sourceResult with
  | .error reason =>
    pure ⟨program,runtime,.error reason,targetResult,#[],#[]⟩
  | .ok source => do
    let mut tables := program.compilerTables
    let mut declarations := #[]
    let mut selected := #[]
    for raw in ← (← field source "declarations").getArr? do
      let (entry,next) ← decodeDeclaration ctx tables raw
      tables := next
      if let some old := declarations.find? (·.definition == entry.definition) then
        unless old == entry do throw "conflicting exact extern-static declaration queries"
      else declarations := declarations.push entry
    for raw in ← (← field source "selected_exported").getArr? do
      let symbol ← str raw "symbol"
      if selected.any (·.symbol == symbol) then throw "duplicate selected exported symbol row"
      let (winner,next) ← selectedWinner ctx tables raw
      tables := next
      selected := selected.push ⟨symbol,winner⟩
    pure ⟨program.withCompilerTables tables,runtime,.ok (),targetResult,declarations,selected⟩

private def declaration (p : Prepared) (id : MIR.DefId) : Except String Declaration := do
  let some entry := p.declarations.find? (·.definition == id)
    | match p.sourceStatus with
      | .ok () => throw "missing exact compiler extern-static declaration row"
      | .error reason => throw reason
  match entry.result with
  | .ok () => pure entry
  | .error reason => throw reason

private def stepError (reason : String) : StepError := .unsupported s!"compiler extern-static query: {reason}"

private def runtimeDeclaration (p : Prepared) (id : MIR.DefId) :
    ExternStatic.M S ExternStatic.Declaration := do
  match declaration p id with
  | .error reason => throw (stepError reason)
  | .ok entry => pure ⟨entry.symbol,entry.size,entry.align,entry.linkage⟩

private def selected (p : Prepared) (name : String) : ExternStatic.M S (Option Winner) := do
  let some entry := p.selected.find? (·.symbol == name)
    | match p.sourceStatus with
      | .ok () => return none
      | .error reason => throw (stepError reason)
  match entry.winner.status with
  | "supported" => return some entry.winner
  | "ambiguous" => throw (.machineStop entry.winner.reason)
  | _ => throw (stepError entry.winner.reason)

private def liftMemory (result : Except ε A) (showError : ε → String) : ExternStatic.M S A :=
  match result with
  | .ok value => pure value
  | .error error => throw (.invalidProgram (showError error))

/-! Build the source resolver on any persistent machine state. The caller
supplies its canonical memory/runtime views and root-pointer operation; this
lets constants and allocation-image relocations share one resolver even though
the latter intentionally run without a MIR frame. -/
def hooksOn [DecidableEq K] (p : Prepared) (image : AllocationImage.Imported)
    (memory : S → MemoryState Provenance Miri.TreeBorrows.BorrowTree K)
    (externStaticState : S → ExternStatic.State)
    (checkSymbolClash : String → ExternStatic.M S Unit)
    (rootPointer : AllocId → ExternStatic.M S StrictPointer) :
    ExternStatic.ResolveHooks S Winner := by
  let pointerSize := p.runtime.target.pointerSize
  exact {
    get := do return externStaticState (← get)
    declaration := runtimeDeclaration p
    pointerSize
    checkSymbolClash
    allocationInfo := fun id => do
      let info ← liftMemory ((memory (← get)).getAllocInfo id) reprStr
      pure ⟨info.size,info.align⟩
    lookupStatic := selected p
    evalGlobal := fun winner => do
      unless winner.kind == "static" do
        throw (.undefinedBehavior "attempt to access an exported symbol that is not defined as a static")
      let some definitionId := winner.definition | throw (stepError "selected static has no exact DefId")
      let some allocation := winner.allocation | throw (stepError "selected static initializer allocation is unavailable")
      let currentMemory := memory (← get)
      unless image.source.any (·.id == allocation) do
        throw (stepError "selected static allocation is absent from canonical imported image")
      let id ← liftMemory (AllocationImage.runtimeId currentMemory allocation) id
      let some info := currentMemory.findGlobal? id | throw (stepError "selected static is absent from imported global allocations")
      match info.payload with
      | some (.static actual true false false) =>
        unless actual == definitionId do throw (.invalidProgram "selected static allocation DefId mismatch")
      | some (.static _ false _ _) => throw (.undefinedBehavior "exported symbol is not defined as a static")
      | some (.static _ _ true _) => throw (.invalidProgram "exported static unexpectedly has thread-local storage")
      | some (.static _ _ _ true) => throw (stepError "selected exported static is a foreign item")
      | _ => throw (stepError "selected static allocation payload is not a source static")
      rootPointer id
    declarationMutable := fun definitionId => do
      match declaration p definitionId with
      | .ok entry => pure entry.mutable
      | .error reason => throw (stepError reason)
    allocationMutable := fun id => do
      let info ← liftMemory ((memory (← get)).getAllocInfo id) reprStr
      pure (info.mutability == .Mut) }

def resolveOn [DecidableEq K] (p : Prepared) (image : AllocationImage.Imported)
    (memory : S → MemoryState Provenance Miri.TreeBorrows.BorrowTree K)
    (externStaticState : S → ExternStatic.State)
    (checkSymbolClash : String → ExternStatic.M S Unit)
    (rootPointer : AllocId → ExternStatic.M S StrictPointer)
    (definitionId : MIR.DefId) : ExternStatic.M S StrictPointer :=
  ExternStatic.resolve (hooksOn p image memory externStaticState checkSymbolClash rootPointer)
    definitionId

/-! Actual full-interpreter adapter, including the source function-pointer
root operation and the same runtime ExternStatic storage used by GC. -/
def hooks [DecidableEq K] (p : Prepared) (image : AllocationImage.Imported)
    (checkSymbolClash : String → MachineHooks.M K U Unit)
    (functions : FunctionPointers.Hooks K U Other)
    (externStaticState : U → ExternStatic.State) :
    ExternStatic.ResolveHooks (MachineHooks.State K U) Winner :=
  hooksOn p image (fun state => state.machine.memory)
    (fun state => externStaticState state.machine.user) checkSymbolClash
    (FunctionPointers.rootPointer functions)

def resolve [DecidableEq K] (p : Prepared) (image : AllocationImage.Imported)
    (checkSymbolClash : String → MachineHooks.M K U Unit)
    (functions : FunctionPointers.Hooks K U Other)
    (externStaticState : U → ExternStatic.State) (definitionId : MIR.DefId) :
    MachineHooks.M K U (StrictPointer) :=
  ExternStatic.resolve (hooks p image checkSymbolClash functions externStaticState) definitionId

end Miri.Input.CompilerExternStatic
