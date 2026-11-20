import Miri.Input.CompilerGlobals
import Miri.Input.CompilerPrimitiveFacts
import Miri.Interpreter.TypedRetag
import Miri.Interpreter.LayoutCompat
import Miri.Interpreter.ValidityVisitor

/-! Required compiler facts for the fixed interpreter. Query evidence is keyed
by exact compilation-local TyId and explicit fully_monomorphized typing_env.
Sources: rustc_middle ty/{util,sty,inhabitedness}; interpret/{call,visitor,validity}
and Miri helpers.rs UnsafeCellVisitor/tree_borrows/mod.rs NewPermission.
No diagnostic type spelling establishes a semantic property. -/
namespace Miri.Input.CompilerFacts
open Lean Miri.ABI Miri.Memory Miri.Interpreter
abbrev Result := Except String

private def computeUnitLayout (runtime : RuntimeMetadata.Indexed) :
    Result (TyAndLayout TypeId) := do
  let some source := runtime.source.types.find? (fun ty =>
    ty.shapeKind == .tuple &&
      ((ty.payload.getObjVal? "shape").bind fun shape =>
        (shape.getObjVal? "elements").bind Json.getArr?).toOption == some #[])
    | throw "compiler unit type identity missing"
  runtime.lookup source.id |>.mapError toString

set_option autoImplicit false in
structure UnitLayoutCache (runtime : RuntimeMetadata.Indexed) where
  private mk ::
  value : Result (TyAndLayout TypeId)
  exact : value = computeUnitLayout runtime

def bindUnitLayout (runtime : RuntimeMetadata.Indexed) : UnitLayoutCache runtime :=
  let value := computeUnitLayout runtime
  ⟨value, rfl⟩

structure Context where
  runtime : RuntimeMetadata.Indexed
  /-- Exact direct primitive query results for the metadata owned by this
  context. Manual contexts may omit the cache. -/
  primitiveQueries : Option (CompilerPrimitiveFacts.Bound runtime.toRuntimeMetadata) := none
  /-- The first-match unit query result is stored as data, including failure,
  and bound to this exact indexed metadata value. -/
  unitLayoutCache : Option (UnitLayoutCache runtime) := none
  program : LoweredProgram
  /-- Context caches are certified for this exact source document. Manual
  contexts may omit it and retain the uncached accessor fallback. -/
  lowering : Option (LowerContext.Bound program.input) := none

def Context.loweringContext (context : Context) : LowerContext :=
  match context.lowering with
  | some prepared => prepared.value
  | none => LowerContext.ofDocument context.program.input

def Context.primitiveLayout (context : Context) (key : String) :
    Except String (TyAndLayout TypeId) :=
  match context.primitiveQueries with
  | some cache => CompilerPrimitiveFacts.primitiveLayoutBound context.runtime.toRuntimeMetadata cache key
  | none => CompilerPrimitiveFacts.primitiveLayout context.runtime.toRuntimeMetadata key

def Context.orderingLayout (context : Context) : Except String (TyAndLayout TypeId) :=
  match context.primitiveQueries with
  | some cache => CompilerPrimitiveFacts.orderingLayoutBound context.runtime.toRuntimeMetadata cache
  | none => CompilerPrimitiveFacts.orderingLayout context.runtime.toRuntimeMetadata

/-- Rebind every document-dependent cache when the owning lowered program changes. -/
def Context.withProgram (context : Context) (program : LoweredProgram) : Context :=
  { context with program, lowering := some (LowerContext.bindDocument program.input) }

def ofProgram (runtime : RuntimeMetadata) (program : LoweredProgram)
    (sourceEquality : Option (RuntimeMetadata.JsonReflexivity runtime.source.raw) := none) : Result Context := do
  unless RuntimeMetadata.JsonReflexivity.matchesRightOr sourceEquality program.input.raw do
    throw "compiler facts/runtime metadata are from different documents"
  let program := CompilerGlobals.prepareProgram program
  let indexed := RuntimeMetadata.Indexed.ofMetadata runtime sourceEquality
  let baseRuntime := indexed.toRuntimeMetadata
  return {
    runtime := indexed
    primitiveQueries := some (CompilerPrimitiveFacts.bind baseRuntime)
    unitLayoutCache := some (bindUnitLayout indexed)
    program
    lowering := some (LowerContext.bindDocument program.input)
  }
private def node (context : Context) (id : TypeId) : Result TypeNode :=
  (context.runtime.node id).mapError toString
private def facts (context : Context) (id : TypeId) : Result TypeCompilerFacts := do
  let source ← node context id
  let some facts := source.compilerFacts | throw s!"missing compiler_facts for type {id}"
  unless facts.inputTypeId == id && facts.typingEnvironment == "fully_monomorphized" do
    throw "compiler query type/typing-environment key mismatch"
  pure facts

def boolean (context : Context) (id : TypeId) (query : String) : Result Bool := do
  let facts ← facts context id
  let some (_,entry) := facts.booleanQueries.find? (·.1 == query) | throw s!"missing compiler boolean query {query}"
  unless entry.status == .supported do throw s!"unresolved compiler query {query}: {entry.reason}"
  let some value := entry.value | throw s!"compiler boolean query {query} has no value"
  pure value

def optionalType (context : Context) (id : TypeId) (query : String) : Result (Option TypeId) := do
  let facts ← facts context id
  let some (_,entry) := facts.typeQueries.find? (·.1 == query) | throw s!"missing compiler type query {query}"
  unless entry.status == .supported do throw s!"unresolved compiler type query {query}: {entry.reason}"
  if let some ty := entry.value then let _ ← node context ty
  pure entry.value

def requiredType (context : Context) (id : TypeId) (query : String) : Result TypeId := do
  let some ty ← optionalType context id query | throw s!"compiler query {query} returned None"
  pure ty
private def field (j : Json) (key : String) : Result Json := j.getObjVal? key
private def string (j : Json) (key : String) : Result String := do (← field j key).getStr?
private def bool (j : Json) (key : String) : Result Bool := do (← field j key).getBool?
private def array (j : Json) (key : String) : Result (Array Json) := do (← field j key).getArr?
private def shape (context : Context) (id : TypeId) : Result Json := do
  let source ← node context id
  unless source.shapeStatus == .supported do throw "compiler type shape unresolved"
  field source.payload "shape"
private def typeRef (context : Context) (j : Json) : Result TypeId := do
  let id ← (← field j "type_id").getNat?
  let _ ← node context id
  pure id

def layoutOf (context : Context) (id : TypeId) : Result (TyAndLayout TypeId) :=
  (context.runtime.lookup id).mapError toString

def unitLayout (context : Context) : Result (TyAndLayout TypeId) := do
  match context.unitLayoutCache with
  | some cached => cached.value
  | none => computeUnitLayout context.runtime

def builtinDeref (context : Context) (id : TypeId) (explicit : Bool) : Result (Option TypeId) :=
  optionalType context id (if explicit then "builtin_deref_explicit" else "builtin_deref_implicit")

def referencePointee (context : Context) (id : TypeId) : Result (TypeId × MIR.Mutability) := do
  let source ← node context id
  unless source.shapeKind == .reference do throw "reference_pointee requested for a non-reference"
  let value ← shape context id
  let pointee ← typeRef context (← field value "pointee")
  let mutable ← string (← field value "mutability") "kind"
  let mutable ← match mutable with
    | "mutable" => pure MIR.Mutability.Mut
    | "immutable" => pure .Not
    | _ => throw "unknown reference mutability"
  pure (pointee,mutable)

def retagTypeShape (context : Context) (id : TypeId) : Result Miri.TreeBorrows.RetagPipeline.RetagTypeShape := do
  let source ← node context id
  pure ⟨← boolean context id "is_global_box",source.shapeKind == .reference,
    source.shapeKind == .rawPointer,← boolean context id "is_box"⟩

private def adtPayload (context : Context) (id : TypeId) : Result Json := do
  let some payload := (← facts context id).adtPayload | throw "ADT query requested for a non-ADT"
  pure payload

def itemName (context : Context) (id : TypeId) : Result String := do string (← adtPayload context id) "item_name"
def nonnullOptimizationGuaranteed (context : Context) (id : TypeId) : Result Bool := do
  bool (← adtPayload context id) "nonnull_optimization_guaranteed"
def reprEqualUpToSeed (context : Context) (left right : TypeId) : Result Bool := do
  let a ← field (← shape context left) "representation"
  let b ← field (← shape context right) "representation"
  let mut same := true
  -- Exactly ReprOptions::equal_up_to_seed: no field is dropped except seed.
  for key in #["integer","align_bytes","pack_bytes","flags_bits","scalable_element"] do
    let av ← field a key
    let bv ← field b key
    same := same && av == bv
  pure same

def adtInfo (context : Context) (id : TypeId) : Result (LayoutCompat.AdtInfo TypeId) := do
  let source ← node context id
  unless source.shapeKind == .adt do throw "ADT layout query on non-ADT"
  let value ← shape context id
  let repr ← field value "representation"
  let kind ← match source.shapeMetadata.adtKind with
    | some .structKind => pure LayoutCompat.AdtKind.Struct
    | some .unionKind => pure .Union
    | some .enumKind => pure .Enum
    | _ => throw "unknown ADT kind"
  let mut variants := #[]
  for variant in ← array value "variants" do
    let mut fields := #[]
    for item in ← array variant "fields" do
      fields := fields.push (⟨← string item "name", ← typeRef context (← field item "type")⟩ : LayoutCompat.Field TypeId)
    variants := variants.push fields
  pure ⟨kind,← bool repr "transparent",← bool repr "c",← bool repr "rust",variants⟩

def compatibilityKind (context : Context) (id : TypeId) : Result (LayoutCompat.TypeKind TypeId) := do
  let source ← node context id
  let value ← shape context id
  match source.shapeKind with
  | .tuple => pure .tuple | .never => pure .never | .functionDefinition => pure .functionDefinition
  | .closure => pure .closure | .coroutine => pure .coroutine | .coroutineClosure => pure .coroutineClosure
  | .array => return .array (← typeRef context (← field value "element"))
  | .adt => pure .adt
  | .patternType => return .pattern (← typeRef context (← field value "base"))
  | .unsafeBinder => pure .unsafeBinder | .alias => pure .alias
  | .reference => return .reference (← typeRef context (← field value "pointee"))
  | .rawPointer => return .rawPointer (← typeRef context (← field value "pointee"))
  | .functionPointer => pure .functionPointer
  | .int | .uint =>
    match source.shapeMetadata.signedKind <|> source.shapeMetadata.unsignedKind with
    | some (.known kind) => pure (.integer kind)
    | _ => throw "compiler integer kind missing"
  | .char => pure .char
  | .bool | .float | .foreign | .str | .slice | .dynamicTraitObject => pure .other
  | _ => throw "non-normalized compiler type in ABI compatibility query"

private def lift (value : Result A) : EStateM StepError S A :=
  match value with | .ok value => pure value | .error error => throw (.invalidProgram error)

/-- Replace only compiler leaves; all actual memory/projection/dyn operations
retain their source implementation and stateful failure behavior. -/
def typedRetagHooks (context : Context) (machine : TypedRetag.Hooks K U) : TypedRetag.Hooks K U :=
  { machine with
    typeShape := fun ty => lift (retagTypeShape context ty)
    builtinDeref := fun ty => lift (requiredType context ty "builtin_deref_explicit")
    referencePointee := fun ty => lift (referencePointee context ty)
    isUnpin := fun ty => lift (boolean context ty "is_unpin")
    isUnsafeUnpin := fun ty => lift (boolean context ty "is_unsafe_unpin")
    typeIsFreeze := fun ty => lift (boolean context ty "is_freeze")
    freeze := { machine.freeze with
      isUnsafeCell := fun ty => lift (boolean context ty "is_unsafe_cell")
      typeIsFreeze := fun ty => lift (boolean context ty "is_freeze")
      isDynamic := fun ty => lift (boolean context ty "is_dynamic")
      isBox := fun ty => lift (boolean context ty "is_box")
      isTooGeneric := fun ty => lift (boolean context ty "is_too_generic") } }

def compatibilityQueries (context : Context) : LayoutCompat.Queries TypeId S := {
  target := context.runtime.target
  kind := fun ty => lift (compatibilityKind context ty)
  adt := fun ty => lift (adtInfo context ty)
  field := fun layout index => lift ((context.runtime.field layout index).mapError toString)
  layoutOf := fun ty => lift (layoutOf context ty)
  unitLayout := lift (unitLayout context)
  eraseUnsafeBinder := fun ty => lift (requiredType context ty "unsafe_binder_erased")
  normalize := fun ty => lift (requiredType context ty "normalized")
  reprEqualUpToSeed := fun a b => lift (reprEqualUpToSeed context a b)
  itemName := fun ty => lift (itemName context ty)
  nonnullOptimizationGuaranteed := fun ty => lift (nonnullOptimizationGuaranteed context ty)
  isGlobalBox := fun ty => lift (boolean context ty "is_global_box")
  boxedType := fun ty => lift (requiredType context ty "boxed_type")
  pointerMetadataType := fun ty => lift (requiredType context ty "pointer_metadata_type") }

end Miri.Input.CompilerFacts
