import Miri.Input.CompilerFacts
import Miri.Interpreter.Cast

/-! Compiler shape/query adapters for Cast and ValidityVisitor. Definition and
TypeConst IDs are appended to the existing shared bundle, never source indices.
Dynamic-predicate tokens index an explicit shared table of original compiler
predicate arrays; vtable consumers must use this same table and still discharge
normalization/stable-comparison queries. -/
namespace Miri.Input.CompilerFactAdapters
open Lean Miri.ABI Miri.Memory Miri.Interpreter
abbrev Result := Except String
/-- Canonical source pattern identities; range constants share the program's
TypeConst table and Or children share this pattern table. -/
inductive PatternIdentity where
  | range (start finish : MIR.TypeConstId)
  | or (children : Array Nat)
  | notNull
  deriving Repr, DecidableEq

private partial def lowerPattern (ctx : LowerContext) (tables : CompilerTables)
    (nodes : Array PatternIdentity) (pattern : CompilerPattern) : Result (Nat × CompilerTables × Array PatternIdentity) := do
  let (value,tables,nodes) ← match pattern with
    | .range start finish => do
      let (start,tables) ← lowerCompilerTypeConst ctx tables (← decodeCompilerValue start)
      let (finish,tables) ← lowerCompilerTypeConst ctx tables (← decodeCompilerValue finish)
      pure (PatternIdentity.range start finish,tables,nodes)
    | .or children => do
      let mut tables := tables
      let mut nodes := nodes
      let mut ids := #[]
      for child in children do
        let (id,nextTables,nextNodes) ← lowerPattern ctx tables nodes child
        tables := nextTables; nodes := nextNodes; ids := ids.push id
      pure (PatternIdentity.or ids,tables,nodes)
    | .notNull => pure (PatternIdentity.notNull,tables,nodes)
  match nodes.toList.idxOf? value with
  | some id => pure (id,tables,nodes)
  | none => pure (nodes.size,tables,nodes.push value)

structure Prepared where
  context : CompilerFacts.Context
  dynamicPredicates : Array Json
  patterns : Array PatternIdentity
  castTypes : Array (TypeId × Result CastTypeInfo)
  obligations : Array Obligation

private def field (j : Json) (key : String) : Result Json := j.getObjVal? key
private def natural (j : Json) (key : String) : Result Nat := do (← field j key).getNat?
private def string (j : Json) (key : String) : Result String := do (← field j key).getStr?
private def array (j : Json) (key : String) : Result (Array Json) := do (← field j key).getArr?
private def source (context : CompilerFacts.Context) (id : TypeId) : Result TypeNode :=
  (context.runtime.node id).mapError toString
private def shape (context : CompilerFacts.Context) (id : TypeId) : Result Json := do field (← source context id).payload "shape"
private def typeRef (context : CompilerFacts.Context) (j : Json) : Result TypeId := do
  let id ← natural j "type_id"
  let _ ← source context id
  pure id
private def sourceDefinition (node : TypeNode) : Result DefinitionId := do
  let some facts := node.compilerFacts | throw "type compiler definition evidence missing"
  let value ← field facts.payload "definition"
  pure ⟨← natural value "crate",← natural value "index"⟩
private def ensureDefinition (tables : CompilerTables) (id : DefinitionId) : CompilerTables :=
  if tables.definitions.contains id then tables else { tables with definitions := tables.definitions.push id }

private def castType (context : CompilerFacts.Context) (tables : CompilerTables) (predicates : Array Json)
    (patternIds : Array (TypeId × Nat)) (id : TypeId) : Result (CastTypeInfo × CompilerTables) := do
  let node ← source context id
  let value ← shape context id
  let ty key := do typeRef context (← field value key)
  let unchanged value := pure (value,tables)
  match node.shapeKind with
  | .int | .uint =>
    match node.shapeMetadata.signedKind <|> node.shapeMetadata.unsignedKind with
    | some (.known kind) => unchanged (.integer kind)
    | _ => throw "integer kind evidence unavailable"
  | .float =>
    let format ← match node.shapeMetadata.floatKind with
      | some .f16 => pure FloatFormat.binary16 | some .f32 => pure .binary32
      | some .f64 => pure .binary64 | some .f128 => pure .binary128
      | _ => throw "unsupported compiler float format"
    unchanged (.floating format)
  | .bool => unchanged .boolean | .char => unchanged .character
  | .rawPointer => unchanged (.rawPointer (← ty "pointee"))
  | .reference => unchanged (.reference (← ty "pointee"))
  | .functionPointer => unchanged .fnPointer
  | .adt =>
    let definition ← sourceDefinition node
    let tables := ensureDefinition tables definition
    pure (.adt (← lookupDefinitionId tables.definitions definition),tables)
  | .functionDefinition | .closure =>
    let definition ← sourceDefinition node
    let tables := ensureDefinition tables definition
    let (args,tables) ← lowerCompilerGenericArgs context.loweringContext tables
      (← context.loweringContext.decodeCompilerValue (← field value "generic_args"))
    let definition ← lookupDefinitionId tables.definitions definition
    if node.shapeKind == .functionDefinition then pure (.fnDefinition definition args,tables)
    else pure (.closure definition args (← natural value "upvar_count"),tables)
  | .array =>
    let layout ← CompilerFacts.layoutOf context id
    let .Array _ count := layout.layout.fields | throw "array compiler layout lacks source array count"
    unchanged (.array (← ty "element") count)
  | .slice => unchanged (.slice (← ty "element"))
  | .dynamicTraitObject =>
    let value ← field value "predicates"
    let some token := predicates.toList.idxOf? value | throw "dynamic predicate table identity missing"
    unchanged (.dynamic token)
  | .patternType =>
    let some (_,id) := patternIds.find? (·.1 == id) | throw "canonical compiler pattern identity missing"
    unchanged (.pattern (← ty "base") id)
  | _ => throw "type kind is outside the cast operand domain"

def prepare (context : CompilerFacts.Context) : Result Prepared := do
  let loweringContext := context.loweringContext
  let mut predicates := #[]
  for node in context.runtime.source.types do
    if node.shapeKind == .dynamicTraitObject then
      let value ← field (← field node.payload "shape") "predicates"
      unless predicates.contains value do predicates := predicates.push value
  for allocation in context.program.input.allocations do
    if let some (.vtable source) := allocation.data then
      let value ← field source.payload "predicates"
      unless predicates.contains value do predicates := predicates.push value
  -- Region-erased/anonymized outputs share this same predicate-array table.
  -- Existing source tokens keep their indices; newly exported outputs append.
  if let .ok queries := context.program.input.raw.getObjVal? "compiler_vtable_queries" then
    for query in (← queries.getArr?) do
      for key in #["input_predicates","output_predicates"] do
        let value ← field query key
        let _ ← value.getArr?
        unless predicates.contains value do predicates := predicates.push value
  let mut tables := context.program.compilerTables
  let mut casts := #[]
  let mut obligations := #[]
  let mut patterns := #[]
  let mut patternIds := #[]
  for node in context.runtime.source.types do
    if let some pattern := node.pattern then
      match lowerPattern loweringContext tables patterns pattern with
      | .ok (id,nextTables,nextPatterns) =>
        tables := nextTables; patterns := nextPatterns; patternIds := patternIds.push (node.id,id)
      | .error error => obligations := obligations.push ⟨s!"types[{node.id}].pattern",error⟩
  for node in context.runtime.source.types do
    match castType context tables predicates patternIds node.id with
    | .ok (kind,next) => casts := casts.push (node.id,.ok kind); tables := next
    | .error error =>
      casts := casts.push (node.id,.error error)
      obligations := obligations.push ⟨s!"types[{node.id}].cast",error⟩
  pure ⟨context.withProgram (context.program.withCompilerTables tables),predicates,patterns,casts,obligations⟩

def castTypeInfo (prepared : Prepared) (id : TypeId) : Result CastTypeInfo := do
  let some (_,result) := prepared.castTypes.find? (·.1 == id) | throw "compiler cast type identity missing"
  result
private def dynamicToken (prepared : Prepared) (id : TypeId) : Result Nat := do
  let value ← field (← shape prepared.context id) "predicates"
  let some token := prepared.dynamicPredicates.toList.idxOf? value | throw "dynamic predicate identity missing"
  pure token

def validityKind (prepared : Prepared) (id : TypeId) : Result ValidityVisitor.TypeKind := do
  let context := prepared.context
  let node ← source context id
  let value ← shape context id
  let ty key := do typeRef context (← field value key)
  match node.shapeKind with
  | .bool => pure .boolean | .char => pure .character | .int | .uint => pure .integer
  | .float => pure .float | .functionPointer => pure .functionPointer | .never => pure .never
  | .foreign => pure .foreign | .functionDefinition => pure .functionDefinition
  | .rawPointer =>
    let pointee ← ty "pointee"
    return .rawPointer pointee (← CompilerFacts.boolean context pointee "is_sized")
  | .reference => return .reference ((← CompilerFacts.referencePointee context id).2 == .Mut)
  | .str => pure .string
  | .array | .slice => return .sequence (← ty "element")
  | .dynamicTraitObject => return .dynamic (← dynamicToken prepared id)
  | .patternType => return .pattern (← ty "base")
  | .unsafeBinder => pure .unsafeBinder
  | .adt | .tuple | .closure | .coroutine | .coroutineClosure =>
    if ← CompilerFacts.boolean context id "is_box" then pure .box else
      return .aggregate (← CompilerFacts.boolean context id "is_like_maybe_dangling")
        (← CompilerFacts.boolean context id "is_unsafe_cell") (node.shapeMetadata.adtKind == some .enumKind)
  | _ => throw "non-normalized/unsupported compiler type in validity query"

def metadataTail (prepared : Prepared) (id : TypeId) : Result ValidityVisitor.MetadataTail := do
  let tail ← CompilerFacts.requiredType prepared.context id "metadata_tail"
  let node ← source prepared.context tail
  match node.shapeKind with
  | .dynamicTraitObject => return .dynamic (← dynamicToken prepared tail)
  | .slice | .str => pure .sliceOrStr
  | .foreign => pure .foreign
  | _ => throw "metadata validation requested for a sized or unsupported tail"

private def lift (value : Result A) : EStateM StepError S A :=
  match value with | .ok value => pure value | .error error => throw (.invalidProgram error)

def castHooks (prepared : Prepared) (machine : CastHooks P S C V) : CastHooks P S C V :=
  { machine with
    typeInfo := fun _ ty => lift (castTypeInfo prepared ty)
    layoutOf := fun _ ty => lift (CompilerFacts.layoutOf prepared.context ty)
    builtinDeref := fun _ ty explicit => lift (CompilerFacts.builtinDeref prepared.context ty explicit)
    ensureMonomorphic := fun _ ty => do
      unless ← lift (CompilerFacts.boolean prepared.context ty "is_monomorphic_enough") do throw (.invalidProgram "compiler type still requires instantiation") }

def validityHooks (prepared : Prepared) (machine : ValidityVisitor.Hooks P S C E Fn Abi Pad) : ValidityVisitor.Hooks P S C E Fn Abi Pad :=
  { machine with
    classify := fun _ ty => lift (validityKind prepared ty)
    metadataTail := fun _ ty => lift (metadataTail prepared ty)
    unitLayout := fun _ => lift (CompilerFacts.unitLayout prepared.context)
    typeName := fun _ ty => do pure (← lift (source prepared.context ty)).display
    opsemInhabited := fun _ ty => lift (CompilerFacts.boolean prepared.context ty "opsem_inhabited")
    isFreeze := fun _ ty => lift (CompilerFacts.boolean prepared.context ty "is_freeze") }
/-- The diagnostic type name is a pure compiler-node projection. -/
theorem validity_typeName_of_node (prepared : Prepared)
    (machine : ValidityVisitor.Hooks P S C E Fn Abi Pad) (choice : C)
    (ty : TypeId) (node : TypeNode)
    (found : prepared.context.runtime.node ty = .ok node) :
    (validityHooks prepared machine).typeName choice ty = pure node.display := by
  funext state
  simp [validityHooks, source, lift, found, Except.mapError,
    bind, Bind.bind, EStateM.bind, pure, Pure.pure, EStateM.pure]

end Miri.Input.CompilerFactAdapters
