import Lean.Util.Profile
import Miri.Input.CompilerInstance
import Miri.Input.NormalizationBody
import Miri.Input.RuntimeMetadata
import Miri.Interpreter.Constant

/-! Checked reuse of real rustc normalization and Const::eval query results.
Sources: ty/instance.rs::try_instantiate_mir_and_normalize_erasing_regions;
mir/consts.rs::Const::eval; Miri operand.rs::eval_const_to_op. A query key
contains the complete instance, source body, MIR location and structural operand
path. A source span alone is never an identity. Failed or absent compiler
queries remain obligations and fail when requested. -/
namespace Miri.Input.CompilerConstantQueries
open Lean Miri.Interpreter

inductive PathElement where
  | field (name : String)
  | index (value : Nat)
  deriving Repr, DecidableEq
structure Site where
  bodyIndex : Nat
  location : MIR.Location
  path : Array PathElement
  deriving Repr, DecidableEq
structure Evidence where
  site : Site
  query : CompilerConstantEvidence
  sourcePayload : Json
  normalizedPayload : Json
structure Prepared where
  program : LoweredProgram
  evidence : Array Evidence
  obligations : Array Obligation

/-! A source compatibility check is deep over JSON. Production preparation
does it once, then carries this binding with the exact values it checked.
The private constructor and dependent indices prevent a caller from supplying
an arbitrary cached Boolean or reusing it for different metadata. -/
structure Binding (prepared : Prepared) (runtime : RuntimeMetadata) where
  private mk ::
  compatible : Bool
  correct : compatible = (runtime.source.raw == prepared.program.input.raw)

def bind (prepared : Prepared) (runtime : RuntimeMetadata)
    (sourceEquality : Option (RuntimeMetadata.JsonReflexivity runtime.source.raw) := none) : Binding prepared runtime :=
  let compatible := RuntimeMetadata.JsonReflexivity.matchesRightOr sourceEquality prepared.program.input.raw
  ⟨compatible, RuntimeMetadata.JsonReflexivity.matchesRightOr_eq sourceEquality prepared.program.input.raw⟩

private def field (j : Json) (key : String) : Except String Json := j.getObjVal? key
private def natural (j : Json) (key : String) : Except String Nat := do (← field j key).getNat?
private def array (j : Json) (key : String) : Except String (Array Json) := do (← field j key).getArr?
private partial def constants (j : Json) (path : Array PathElement := #[]) : Array (Array PathElement × Json) :=
  if ((j.getObjVal? "constant").bind (fun c => c.getObjValAs? String "kind")).toOption == some "evaluated_const" then #[(path,j)]
  else match j with
  | .arr values => (values.mapIdx fun i value => constants value (path.push (.index i))).flatten
  | .obj fields => (fields.toList.toArray.map fun (name,value) => constants value (path.push (.field name))).flatten
  | _ => #[]

private def lookupPath (j : Json) (path : Array PathElement) : Except String Json :=
  path.foldlM (fun value key => match key with
    | .field name => field value name
    | .index i => do
      let values ← value.getArr?
      match values[i]? with
      | some value => pure value
      | none => throw "normalized query changed operand structural path") j

private def sourceConstants (bodyIndex : Nat) (body : Json) : Except String (Array (Site × Json)) := do
  let mut found := #[]
  for block in ← array body "basic_blocks" do
    let blockId ← natural block "block"
    let statements ← array block "statements"
    for i in [:statements.size] do
      let some statement := statements[i]? | throw "statement array changed"
      for (path, value) in constants statement do
        found := found.push (⟨bodyIndex, ⟨blockId,i⟩, path⟩,value)
    for (path,value) in constants (← field block "terminator") do
      found := found.push (⟨bodyIndex, ⟨blockId,statements.size⟩,path⟩,value)
  pure found

private def normalizedOperand (body : Json) (site : Site) : Except String Json := do
  let blocks ← array body "basic_blocks"
  let some block := blocks.find? (fun b => (natural b "block").toOption == some site.location.block)
    | throw "normalized body is missing source basic block"
  let statements ← array block "statements"
  let envelope ← if site.location.statementIndex == statements.size then field block "terminator"
    else match statements[site.location.statementIndex]? with
      | some statement => pure statement
      | none => throw "normalized body is missing source statement"
  lookupPath envelope site.path

private def evidenceAt (ctx : LowerContext) (interner : CompilerSpanInterner) (fnInstance : CallInstance)
    (site : Site) (original normalized : Json) : Except String (Evidence × CompilerSpanInterner) := do
  unless (← field original "span") == (← field normalized "span") do throw "normalization changed constant source span"
  let (source,interner) ← lowerCompilerConstOperandWithInterner ctx interner (← ctx.decodeCompilerValue original)
  let (normal,interner) ← lowerCompilerConstOperandWithInterner ctx interner (← ctx.decodeCompilerValue normalized)
  let evaluated ← field normalized "constant"
  unless (← evaluated.getObjValAs? String "status") == "supported" do throw "compiler Const::eval did not produce a value"
  let ty ← natural (← field normalized "type") "type_id"
  let value ← lowerCompilerConstValue ctx ty (← ctx.decodeCompilerValue (← field evaluated "value"))
  pure (⟨site, ⟨fnInstance,source.value,normal.value,normal.span,value⟩, original, normalized⟩,
    interner)

private structure PrepareState where
  interner : CompilerSpanInterner
  evidence : Array Evidence
  obligations : Array Obligation

private def prepareBody (ctx : LowerContext)
    (program : LoweredProgram) (bodyIndex : Nat) (state : PrepareState) :
    Except String PrepareState := do
  let some body := program.bundle.bodies[bodyIndex]? | throw "body index missing"
  match field body.input.payload "constant_query_context" with
  | .error _ =>
    let obligation : Obligation := ⟨s!"bodies[{bodyIndex}].constant_query_context",
      "compiler current-instance normalization query is missing"⟩
    pure { state with obligations := state.obligations.push obligation }
  | .ok queryContext => do
    let (fnInstance,nextTables) ← CompilerInstance.decode ctx state.interner.getTables queryContext
    let interner := state.interner.rebind nextTables
    let normalization ← field queryContext "normalization"
    if (normalization.getObjValAs? String "status").toOption != some "supported" then
      let obligation : Obligation := ⟨s!"bodies[{bodyIndex}].constant_query_context",
        "compiler current-instance normalization query failed"⟩
      pure { state with interner, obligations := state.obligations.push obligation }
    else
      let normalizedBody ← NormalizationBody.resolve normalization body.input.payload
      let mut interner := interner
      let mut evidence := state.evidence
      let mut obligations := state.obligations
      for (site,original) in ← sourceConstants bodyIndex body.input.payload do
        let result := do
          let normalized ← normalizedOperand normalizedBody site
          evidenceAt ctx interner fnInstance site original normalized
        match result with
        | .ok (entry,nextInterner) =>
          evidence := evidence.push entry
          interner := nextInterner
        | .error message =>
          obligations := obligations.push
            ⟨s!"bodies[{bodyIndex}].constant[{reprStr site.location},{reprStr site.path}]",message⟩
      pure ⟨interner,evidence,obligations⟩

private def prepareBodies (ctx : LowerContext) (program : LoweredProgram)
    (initial : PrepareState) : Except String PrepareState := do
  let mut state := initial
  for bodyIndex in [:program.bundle.bodies.size] do
    state ← prepareBody ctx program bodyIndex state
  pure state

/-- Build only from explicit exporter compiler-query context. In particular,
monomorphic-looking syntax is never taken as evidence of normalization. -/
def prepareProfiled (profile : Lean.Options) (input : LoweredProgram) : Except String Prepared := do
  let program := profileit "preparation.constants.globals" profile fun _ =>
    CompilerGlobals.prepareProgram input
  let ctx := profileit "preparation.constants.context" profile fun _ =>
    LowerContext.ofDocument program.input
  let initial : PrepareState := ⟨CompilerSpanInterner.ofTables program.compilerTables, #[], #[]⟩
  let state ← profileit "preparation.constants.bodies" profile fun _ =>
    prepareBodies ctx program initial
  let program := program.withCompilerTables state.interner.getTables
  pure ⟨program,state.evidence,state.obligations⟩

def prepare (input : LoweredProgram) : Except String Prepared := prepareProfiled {} input

/-- Bind the exact interpreter source site before evaluation. All machine
provenance/extern-static leaves retain their stateful failure behavior. -/
def queriesAt (prepared : Prepared) (site : Site) (machine : ConstantQueries P E K H) : ConstantQueries P E K H :=
  let evidence := (prepared.evidence.filter (·.site == site)).map (·.query)
  { machine with
    instantiateAndNormalize := fun fnInstance original =>
      match normalizationFromEvidence evidence fnInstance original with
      | .ok value => pure value
      | .error error => throw error
    evaluate := fun fnInstance normalized span =>
      match evaluationFromEvidence evidence fnInstance normalized span with
      | .ok value => pure value
      | .error error => throw error }

end Miri.Input.CompilerConstantQueries
