import Miri.Input.CompilerInstance
import Miri.Interpreter.OperandMachine

/-! Source intrinsics/mod.rs fallback policy and machine.rs runtime_checks.
Attribute membership and intrinsic override policy are actual rustc queries,
never inferred from a spelling or absence of an implementation in Lean.
-/
namespace Miri.Input.CompilerIntrinsicFacts
open Lean Miri.Interpreter
structure Metadata where
  mustOverride : Bool
  fallbackIsSpec : Bool
structure Entry where
  callee : CallInstance
  name : Except String String
  intrinsic : Except String (Option Metadata)
  payload : Json
structure Prepared where
  program : LoweredProgram
  entries : Array Entry
  checks : Array (MIR.RuntimeChecks × Bool)
private def supportedValue (j : Json) : Except String Json := do
  unless (← (← j.getObjVal? "status").getStr?) == "supported" do
    throw s!"compiler intrinsic query unavailable: {((j.getObjVal? "reason").bind Json.getStr?).toOption}"
  j.getObjVal? "value"

def prepare (program : LoweredProgram) : Except String Prepared := do
  let query ← program.input.raw.getObjVal? "compiler_runtime_queries"
  let records ← (← query.getObjVal? "instances").getArr?
  let ctx := LowerContext.ofDocument program.input
  let mut tables := program.compilerTables
  let mut entries := #[]
  for record in records do
    let (callee,next) ← CompilerInstance.decode ctx tables record
    tables := next
    unless !(entries.any (·.callee == callee)) do throw "duplicate full-instance intrinsic metadata key"
    let name := do (← supportedValue (← record.getObjVal? "item_name")).getStr?
    let intrinsic := do
      let value ← supportedValue (← record.getObjVal? "intrinsic_metadata")
      if value == Json.null then pure none else
        pure (some (⟨← (← value.getObjVal? "must_be_overridden").getBool?,
          ← (← value.getObjVal? "fallback_is_spec").getBool?⟩ : Metadata))
    entries := entries.push ⟨callee,name,intrinsic,record⟩
  let session ← program.input.raw.getObjVal? "compiler_session_queries"
  let mut checks := #[]
  for check in (← (← session.getObjVal? "runtime_checks").getArr?) do
    unless (← (← check.getObjVal? "status").getStr?) == "supported" do
      throw "compiler session runtime-check query unavailable"
    let kind ← (← check.getObjVal? "kind").getStr?
    let kind : MIR.RuntimeChecks ← match kind with
      | "ub_checks" => pure .UbChecks | "contract_checks" => pure .ContractChecks
      | "overflow_checks" => pure .OverflowChecks
      | _ => throw "unknown compiler runtime-check kind"
    unless !(checks.any (·.1 == kind)) do throw "duplicate compiler runtime-check query"
    checks := checks.push (kind,← (← check.getObjVal? "enabled").getBool?)
  pure ⟨program.withCompilerTables tables,entries,checks⟩
private def entry (prepared : Prepared) (callee : CallInstance) : Except String Entry := do
  let some entry := prepared.entries.find? (·.callee == callee)
    | throw "missing exact full-instance intrinsic metadata"
  pure entry

def itemName (prepared : Prepared) (callee : CallInstance) : Except String String := do
  (← entry prepared callee).name
private def metadata (prepared : Prepared) (callee : CallInstance) : Except String Metadata := do
  let some value ← (← entry prepared callee).intrinsic
    | throw "source intrinsic metadata unwrap: definition is not an intrinsic"
  pure value

def mustOverride (prepared : Prepared) (callee : CallInstance) : Except String Bool := do
  pure (← metadata prepared callee).mustOverride

def fallbackIsSpec (prepared : Prepared) (callee : CallInstance) : Except String Bool := do
  pure (← metadata prepared callee).fallbackIsSpec

def runtimeChecks (prepared : Prepared) (kind : MIR.RuntimeChecks) : Except String Bool := do
  let some (_,enabled) := prepared.checks.find? (·.1 == kind)
    | throw "missing actual compiler session runtime-check value"
  pure enabled

def operandHooks (prepared : Prepared) (base : OperandMachine.Hooks K User C) :
    OperandMachine.Hooks K User C :=
  { base with runtimeChecks := fun _ kind =>
      match runtimeChecks prepared kind with
      | .ok enabled => pure enabled
      | .error reason => throw (.unsupported reason) }
end Miri.Input.CompilerIntrinsicFacts
