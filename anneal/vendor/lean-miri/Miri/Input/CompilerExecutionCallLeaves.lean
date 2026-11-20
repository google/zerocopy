import Miri.Input.CompilerProviders
import Miri.Input.CompilerCallFacts
import Miri.Input.CompilerTargetFeatures
import Miri.Interpreter.ExecutionCallLeaves

/-! Construct the complete source call compiler dictionary from the single
prepared compiler program. No independently supplied signature/ABI/type/target
feature dictionary is accepted. Source query failures remain typed errors at
that operation; no names or equivalent layouts establish identities. -/
namespace Miri.Input.CompilerExecutionCallLeaves
open Lean Miri.ABI Miri.Interpreter
private def lift (query : Except String A) : MachineHooks.M K U A :=
  match query with | .ok value => pure value | .error error => throw (.unsupported error)

def tupleFields (p : CompilerProviders.Prepared) (ty : MIR.TyId) : Except String (Array MIR.TyId) := do
  let node ← p.runtime.node ty |>.mapError toString
  unless node.shapeStatus == .supported && node.shapeKind == .tuple do
    throw "source RustCall spreading requires the exact tuple type"
  let elements ← (← (← node.payload.getObjVal? "shape").getObjVal? "elements").getArr?
  elements.mapM fun value => do
    let id ← (← value.getObjVal? "type_id").getNat?
    let _ ← p.runtime.node id |>.mapError toString
    pure id

def closureUpvarCount (p : CompilerProviders.Prepared) (ty : MIR.TyId) : Except String (Option Nat) := do
  let node ← p.runtime.node ty |>.mapError toString
  unless node.shapeStatus == .supported do throw "closure-kind compiler evidence is unavailable"
  if node.shapeKind != .closure then return none
  return some (← (← (← node.payload.getObjVal? "shape").getObjVal? "upvar_count").getNat?)

/-- Exact source ExternAbi identity, canonical FnAbi records, shared DefIds/
TypeConstIds and actual current BodyIdentity all belong to this same program. -/
def make (p : CompilerProviders.Prepared) (compatibilityBudget : Nat) :
    ExecutionCallLeaves.Compiler (MachineHooks.State K U) C ABI.ExternAbi := {
  functionSignature := fun _ layout => lift do
    let (count,sourceAbi) ← CompilerFunctionFacts.signature p.functions layout.ty
    pure (count,← CompilerExternAbi.decode sourceAbi)
  functionKind := fun ty => lift (CompilerFunctionFacts.kind p.functions ty)
  resolve := fun _ definition args => CompilerProviders.resolveCurrent p definition args
  fnAbiOfFnPtr := fun _ layout extra => lift (CompilerFunctionFacts.pointerAbi p.functions layout.ty extra)
  fnAbiOfInstance := fun _ callee extra => lift (CompilerInstanceAbi.abiOfInstance p.lifecycle.instances callee extra)
  isRustCall := fun abi => abi == .RustCall
  rustAbi := .Rust
  checkArgumentCompat := fun _ caller callee =>
    LayoutCompat.checkArgumentCompat (CompilerFacts.compatibilityQueries p.lifecycle.calls.symbols.facts.context)
      compatibilityBudget caller callee
  targetFeatures := CompilerTargetFeatures.dictionary p.intrinsics
  tupleFields := fun ty => lift (tupleFields p ty)
  isClosureLike := fun callee => lift (CompilerCallFacts.isClosureLike p.intrinsics callee)
  closureUpvarCount := fun ty => lift (closureUpvarCount p ty)
  llvmLinkName := fun callee => do
    let some name ← lift (CompilerCallFacts.codegenSymbolName p.intrinsics callee)
      | throw (.invalidProgram "source LLVM intrinsic requires a codegen symbol_name attribute")
    pure name }
end Miri.Input.CompilerExecutionCallLeaves
