import Miri.Input.CompilerProviders

/-! eval_context.rs:184–212 mir_assign_valid_types. Equal canonical types
short-circuit the relation; other pairs require exact rustc Covariant evidence.
Successful relation checks retain the source layout-equality assertion. -/
namespace Miri.Input.CompilerCovariance
open Lean Miri.ABI Miri.Interpreter
def relationWithIndex {raw : Json} (index : CompilerQueryIndices.Covariance raw)
    (source target : MIR.TyId) : Except String Bool := do
  if source == target then return true
  match index.data.headerError with
  | some error => throw error
  | none => pure ()
  let mut found := none
  for (_,entry) in CompilerQueryIndices.covarianceRows index source target do
    unless (← entry.getObjValAs? String "typing_env") == "fully_monomorphized" &&
        (← entry.getObjValAs? String "variance") == "covariant" do
      throw s!"compiler covariance query key/environment mismatch (source={source}, target={target})"
    unless (← entry.getObjValAs? String "status") == "supported" do
      throw s!"compiler covariance query unresolved (source={source}, target={target})"
    let value ← entry.getObjValAs? Bool "value"
    if let some old := found then
      unless old == value do
        throw s!"conflicting compiler covariance query results (source={source}, target={target})"
    found := some value
  if let some (_,error) := index.data.firstRowError then throw error
  let some value := found |
    throw s!"missing exact rustc covariance relation query (source={source}, target={target})"
  pure value

def relation (p : CompilerProviders.Prepared) (source target : MIR.TyId) : Except String Bool :=
  relationWithIndex p.covarianceIndex source target

def compatible (p : CompilerProviders.Prepared) (debugAssertions : Bool)
    (source target : LocalLayout) : Except StepError Bool := do
  let related ← relation p source.ty target.ty |>.mapError StepError.unsupported
  if !related then return false
  if debugAssertions || source.ty != target.ty then
    unless source.layout == target.layout do
      throw (.invalidProgram "covariant MIR assignment has unequal layouts")
  pure true

def hook (p : CompilerProviders.Prepared) (debugAssertions : Bool)
    (source target : LocalLayout) : EStateM StepError S Bool :=
  match compatible p debugAssertions source target with
  | .ok value => pure value
  | .error error => throw error
end Miri.Input.CompilerCovariance
