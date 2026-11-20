import Miri.Input.CompilerProviders
import Miri.Interpreter.ConstantMachine

/-! Direct intrinsics.rs type_name/caller_location ConstValue queries. Source
allocation identities are materialized by the actual constant root-pointer
pipeline, with supplied destination layout checked at the original event. -/
namespace Miri.Input.CompilerValueConstants
open Lean Miri.ABI Miri.Interpreter Miri.Memory
private def ref (j : Json) : Except String MIR.TyId := j.getObjValAs? Nat "type_id"
private def records (p : CompilerProviders.Prepared) (key : String) : Except String (Array Json) := do
  (← p.program.input.raw.getObjVal? key).getArr?
private def unique (entries : Array Json) : Except String Json := do
  let some first := entries[0]? | throw "missing exact compiler intrinsic constant query"
  unless entries.all (· == first) do throw "conflicting exact compiler intrinsic constant queries"
  pure first
private def decode (p : CompilerProviders.Prepared) (record : Json) :
    Except String (MIR.TyId × MIR.ConstValue) := do
  unless (← record.getObjValAs? String "status") == "supported" do
    throw s!"compiler intrinsic constant query failed: {record.compress}"
  let ty ← ref (← record.getObjVal? "result_type")
  let _ ← p.runtime.node ty |>.mapError toString
  let value ← lowerCompilerConstValue p.loweringContext ty
    (← p.loweringContext.decodeCompilerValue (← record.getObjVal? "value"))
  pure (ty,value)

def typeName (p : CompilerProviders.Prepared) (ty : MIR.TyId) :
    Except String (MIR.TyId × MIR.ConstValue) := do
  let matching := (← records p "compiler_type_name_constants").filter fun record =>
    ((record.getObjVal? "input_type").bind ref).toOption == some ty
  let record ← unique matching
  unless (← record.getObjValAs? String "typing_env") == "fully_monomorphized" do
    throw "type_name compiler query typing environment mismatch"
  decode p record

def callerLocationReference (p : CompilerProviders.Prepared) (span : MIR.SpanRef) :
    Except String (MIR.TyId × MIR.ConstValue) := do
  unless span.id < p.program.compilerTables.spans.size do throw "caller-location span absent from shared table"
  let mut matching := #[]
  for record in ← records p "compiler_caller_location_constants" do
    let (actual,tables) ← lowerCompilerSpan p.program.compilerTables
      (← p.loweringContext.decodeCompilerValue (← record.getObjVal? "span"))
    if tables.spans == p.program.compilerTables.spans && actual == span then
      matching := matching.push record
  decode p (← unique matching)

/-- Retain the scan's demand-local error order, but build its span index once.
Each row starts from the same base: missing spans cannot pollute later rows.
The immutable ConstValue is still materialized as a fresh runtime global by
EvalCallerLocationConstruction; no guest pointer is cached here. -/
def callerLocation (p : CompilerProviders.Prepared) (span : MIR.SpanRef) :
    Except String (MIR.TyId × MIR.ConstValue) := do
  unless span.id < p.program.compilerTables.spans.size do throw "caller-location span absent from shared table"
  let entries ← records p "compiler_caller_location_constants"
  let base := CompilerSpanInterner.ofTables p.program.compilerTables
  let mut matching := #[]
  for record in entries do
    let (actual,next) ← lowerCompilerSpanWithInterner base
      (← p.loweringContext.decodeCompilerValue (← record.getObjVal? "span"))
    if next.sameSpansAs base && actual == span then
      matching := matching.push record
  decode p (← unique matching)

def eval (p : CompilerProviders.Prepared)
    (functions : FunctionPointers.Hooks K U Other) (arithmetic : PointerArithmetic)
    (externStatic : MIR.DefId → MachineHooks.M K U (Pointer Provenance))
    (classifyError : ConstantError → StepError)
    (checkKnown : LocalLayout → LocalLayout → MachineHooks.M K U Bool)
    (query : Except String (MIR.TyId × MIR.ConstValue)) (destination : LocalLayout) :
    MachineHooks.M K U (OpTy Provenance) := do
  let (ty,value) ← match query with
    | .ok value => pure value
    | .error reason => throw (.unsupported reason)
  ConstantMachine.evalValueWithLayout p.runtime functions arithmetic externStatic classifyError
    value ty (some destination) (some checkKnown)

def typeNameHook (p : CompilerProviders.Prepared)
    (functions : FunctionPointers.Hooks K U Other) (arithmetic : PointerArithmetic)
    (externStatic : MIR.DefId → MachineHooks.M K U (Pointer Provenance))
    (classifyError : ConstantError → StepError)
    (checkKnown : LocalLayout → LocalLayout → MachineHooks.M K U Bool)
    (_ : C) (ty : MIR.TyId) (destination : LocalLayout) : MachineHooks.M K U (OpTy Provenance) :=
  eval p functions arithmetic externStatic classifyError checkKnown (typeName p ty) destination

def callerLocationHook (p : CompilerProviders.Prepared)
    (functions : FunctionPointers.Hooks K U Other) (arithmetic : PointerArithmetic)
    (externStatic : MIR.DefId → MachineHooks.M K U (Pointer Provenance))
    (classifyError : ConstantError → StepError)
    (checkKnown : LocalLayout → LocalLayout → MachineHooks.M K U Bool)
    (currentLocation : MachineHooks.M K U MIR.SpanRef)
    (_ : C) (destination : LocalLayout) : MachineHooks.M K U (OpTy Provenance) := do
  let span ← currentLocation
  eval p functions arithmetic externStatic classifyError checkKnown (callerLocation p span) destination
end Miri.Input.CompilerValueConstants
