import Miri.Input.CompilerScopes

/-! Compiler-owned call.rs constructors/drop queries. All keys use canonical
shared type IDs and complete instances. Absent evidence remains an error. -/
namespace Miri.Input.CompilerRuntimeQueries
open Lean Miri.Interpreter
structure TypeEntry where
  typeId : Nat
  pointerType : Nat
  referenceType : Nat
  dropGlue : Except String CallInstance
structure VirtualEntry where
  original : CallInstance
  methodDefinition : MIR.DefId
  parentTrait : MIR.DefId
  concreteType : Nat
  rebasedArgs : Array MIR.GenericArg
  resolved : Except String CallInstance
structure Prepared where
  program : LoweredProgram
  types : Array TypeEntry
  callerLocation : Array (CallInstance × Bool)
  virtualQueries : Array VirtualEntry
private def value (j : Json) (key : String) : Except String Json := do
  let entry ← j.getObjVal? key
  unless (← (← entry.getObjVal? "status").getStr?) == "supported" do
    throw s!"unresolved compiler runtime query {key}"
  entry.getObjVal? "value"
private def typeId (ctx : LowerContext) (j : Json) : Except String Nat := do
  let id ← (← j.getObjVal? "type_id").getNat?
  unless ctx.containsTypeId id do throw "runtime query references absent compiler type"
  pure id

private def definition (tables : CompilerTables) (j : Json) :
    Except String (MIR.DefId × CompilerTables) := do
  let id : DefinitionId := ⟨← (← j.getObjVal? "crate").getNat?, ← (← j.getObjVal? "index").getNat?⟩
  match lookupDefinitionId tables.definitions id with
  | .ok id => pure (id,tables)
  | .error _ => pure (tables.definitions.size,{tables with definitions := tables.definitions.push id})

def prepare (program : LoweredProgram) : Except String Prepared := do
  let raw ← program.input.raw.getObjVal? "compiler_runtime_queries"
  let ctx := LowerContext.ofDocument program.input
  let mut tables := program.compilerTables
  let mut types := #[]
  for entry in (← (← raw.getObjVal? "types").getArr?) do
    unless (← (← entry.getObjVal? "typing_env").getStr?) == "fully_monomorphized" do
      throw "runtime query typing environment mismatch"
    let id ← (← entry.getObjVal? "input_type_id").getNat?
    unless ctx.containsTypeId id do throw "runtime query input type absent"
    let pointer ← typeId ctx (← value entry "mut_pointer_type")
    let reference ← typeId ctx (← value entry "mut_reference_type")
    let dropResult := do CompilerInstance.decode ctx tables (← value entry "drop_glue")
    let drop ← match dropResult with
      | .error e => pure (.error e)
      | .ok (callee,next) =>
        tables := next
        pure (.ok callee)
    unless !(types.any (·.typeId == id)) do throw "duplicate compiler runtime type query"
    types := types.push ⟨id,pointer,reference,drop⟩
  let mut callers := #[]
  for entry in (← (← raw.getObjVal? "instances").getArr?) do
    let (callee,next) ← CompilerInstance.decode ctx tables entry
    tables := next
    let track ← (← entry.getObjVal? "requires_caller_location").getBool?
    if let some (_,prior) := callers.find? (·.1 == callee) then
      unless prior == track do throw "conflicting full-instance caller-location query"
    else callers := callers.push (callee,track)
  let mut virtualQueries := #[]
  for query in (← (← raw.getObjVal? "virtual").getArr?) do
    unless (← (← query.getObjVal? "typing_env").getStr?) == "fully_monomorphized" do
      throw "virtual query typing environment mismatch"
    let (original,next) ← CompilerInstance.decode ctx tables (← query.getObjVal? "original")
    tables := next
    let (method,next) ← definition tables (← query.getObjVal? "method_definition")
    tables := next
    let (parent,next) ← definition tables (← query.getObjVal? "parent_trait")
    tables := next
    let concrete ← typeId ctx (← query.getObjVal? "concrete_type")
    let args ← ctx.decodeCompilerValue (← query.getObjVal? "rebased_args")
    let (args,next) ← lowerCompilerGenericArgs ctx tables args
    tables := next
    let outcome := do CompilerInstance.decode ctx tables (← value query "resolved")
    let resolved ← match outcome with
      | .error e => pure (.error e)
      | .ok (callee,next) =>
        tables := next
        pure (.ok callee)
    virtualQueries := virtualQueries.push ⟨original,method,parent,concrete,args,resolved⟩
  pure ⟨program.withCompilerTables tables,types,callers,virtualQueries⟩
private def entry (prepared : Prepared) (id : Nat) : Except String TypeEntry := do
  let some entry := prepared.types.find? (·.typeId == id)
    | throw "missing exact compiler runtime type query"
  pure entry

def mutPointerType (prepared : Prepared) (id : Nat) : Except String Nat :=
  return (← entry prepared id).pointerType

def mutReferenceType (prepared : Prepared) (id : Nat) : Except String Nat :=
  return (← entry prepared id).referenceType

def resolveDropGlue (prepared : Prepared) (id : Nat) : Except String CallInstance := do
  (← entry prepared id).dropGlue

def requiresCallerLocation (prepared : Prepared) (callee : CallInstance) : Except String Bool := do
  let some (_,track) := prepared.callerLocation.find? (·.1 == callee)
    | throw "missing exact full-instance caller-location query"
  pure track
def parentTrait (prepared : Prepared) (method : MIR.DefId) : Except String MIR.DefId := do
  let matching := prepared.virtualQueries.filter (·.methodDefinition == method)
  let some first := matching[0]? | throw "missing exact virtual parent-trait query"
  unless matching.all (·.parentTrait == first.parentTrait) do throw "conflicting parent-trait queries"
  pure first.parentTrait

def rebaseVirtualArgs (prepared : Prepared) (args : Array MIR.GenericArg)
    (parent : MIR.DefId) (concrete : Nat) : Except String (Array MIR.GenericArg) := do
  let matching := prepared.virtualQueries.filter fun entry =>
    entry.original.args == args && entry.parentTrait == parent && entry.concreteType == concrete
  let some first := matching[0]? | throw "missing complete-key virtual rebase query"
  unless matching.all (·.rebasedArgs == first.rebasedArgs) do throw "conflicting virtual rebase queries"
  pure first.rebasedArgs

def expectResolveForVTable (prepared : Prepared) (method : MIR.DefId)
    (args : Array MIR.GenericArg) : Except String CallInstance := do
  let matching := prepared.virtualQueries.filter fun entry =>
    entry.methodDefinition == method && entry.rebasedArgs == args
  let some first := matching[0]? | throw "missing complete-key virtual resolution query"
  let callee ← first.resolved
  for entry in matching do
    unless (← entry.resolved) == callee do throw "conflicting virtual resolutions"
  pure callee
private def lift (result : Except String A) : EStateM StepError S A :=
  match result with
  | .ok result => pure result
  | .error error => throw (.invalidProgram error)

def hooks (prepared : Prepared) (base : VirtualCalls.CompilerHooks S C) :
    VirtualCalls.CompilerHooks S C :=
  { base with
    mutPointerType := fun ty => lift (mutPointerType prepared ty)
    mutReferenceType := fun ty => lift (mutReferenceType prepared ty)
    resolveDropGlue := fun ty => lift (resolveDropGlue prepared ty)
    requiresCallerLocation := fun callee => lift (requiresCallerLocation prepared callee)
    parentTrait := fun method => lift (parentTrait prepared method)
    rebaseVirtualArgs := fun args parent concrete => lift (rebaseVirtualArgs prepared args parent concrete)
    expectResolveForVTable := fun _ method args => lift (expectResolveForVTable prepared method args) }
end Miri.Input.CompilerRuntimeQueries
