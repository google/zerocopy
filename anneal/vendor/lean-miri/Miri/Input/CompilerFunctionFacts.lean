import Miri.Input.CompilerInstanceAbi
import Miri.Input.CompilerExternAbi

/-! `step.rs::eval_fn_call`: normalized original signature and function kind,
plus `fn_abi_of_fn_ptr` keyed by original function type and ordered extra types.
The ExternAbi remains the exact compiler payload; its interpretation is explicit.
No indirect runtime target is converted into a fabricated static instance. -/
namespace Miri.Input.CompilerFunctionFacts
open Lean Miri.ABI Miri.Interpreter
structure Function where
  ty : MIR.TyId
  kind : CallFunctionKind
  signature : Except String (Nat × Json)
structure PointerAbi where
  ty : MIR.TyId
  extra : Array MIR.TyId
  result : Except String (FnAbi MIR.TyId)
structure Prepared where
  program : LoweredProgram
  functions : Array Function
  pointerAbis : Array PointerAbi
private def text (j : Json) (key : String) : Except String String := do
  (← j.getObjVal? key).getStr?
private def knownType (ctx : LowerContext) (id : Nat) : Except String Nat := do
  unless ctx.containsTypeId id do throw "function query references missing compiler type"
  pure id
private def supported (j : Json) : Except String Json := do
  unless (← text j "status") == "supported" do
    throw s!"unresolved compiler function query: {((j.getObjVal? "reason").bind Json.getStr?).toOption}"
  j.getObjVal? "value"

def prepare (runtime : RuntimeMetadata) (program : LoweredProgram)
    (sourceEquality : Option (RuntimeMetadata.JsonReflexivity runtime.source.raw) := none)
    (abiCache : Option (CallResolution.FunctionAbiCache runtime) := none) : Except String Prepared := do
  unless RuntimeMetadata.JsonReflexivity.matchesRightOr sourceEquality program.input.raw do
    throw "function query metadata document mismatch"
  let source ← program.input.raw.getObjVal? "compiler_function_facts"
  let ctx := LowerContext.ofDocument program.input
  let mut tables := program.compilerTables
  let mut functions := #[]
  for record in ← (← source.getObjVal? "types").getArr? do
    unless (← text record "typing_env") == "fully_monomorphized" do throw "function query environment mismatch"
    let ty ← knownType ctx (← (← record.getObjVal? "type_id").getNat?)
    if functions.any (fun f => f.ty == ty) then throw "duplicate compiler function type query"
    let sourceKind ← record.getObjVal? "function_kind"
    let kind ← match ← text sourceKind "kind" with
      | "function_pointer" => pure CallFunctionKind.FnPtr
      | "function_definition" => do
        let (callee,next) ← CompilerInstance.decode ctx tables sourceKind
        tables := next
        match callee.kind with
        | .Item defId => pure (.FnDef defId callee.args)
        | _ => throw "FnDef compiler type did not contain its exact Item definition"
      | _ => throw "unknown compiler function kind"
    let signature := do
      let value ← supported (← record.getObjVal? "signature_query")
      let inputs ← (← value.getObjVal? "inputs").getArr?
      for input in inputs do
        let _ ← knownType ctx (← (← input.getObjVal? "type_id").getNat?)
      pure (inputs.size,← value.getObjVal? "abi")
    functions := functions.push ⟨ty,kind,signature⟩
  let mut abis := #[]
  for record in ← (← source.getObjVal? "pointer_abis").getArr? do
    unless (← text record "typing_env") == "fully_monomorphized" do throw "FnPtr ABI environment mismatch"
    let ty ← knownType ctx (← (← record.getObjVal? "type_id").getNat?)
    let some function := functions.find? (fun f => f.ty == ty) | throw "FnPtr ABI has no function-kind evidence"
    match function.kind with
    | .FnPtr => pure ()
    | _ => throw "FnPtr ABI query references a non-pointer function type"
    let extra ← (← (← record.getObjVal? "extra_argument_types").getArr?).mapM fun input => do
      knownType ctx (← (← input.getObjVal? "type_id").getNat?)
    if abis.any (fun entry => entry.ty == ty && entry.extra == extra) then throw "duplicate FnPtr ABI query key"
    let result := do
      let value ← supported (← record.getObjVal? "abi_query")
      CallResolution.functionAbiJson runtime value abiCache
    abis := abis.push ⟨ty,extra,result⟩
  pure ⟨program.withCompilerTables tables,functions,abis⟩

def signature (prepared : Prepared) (ty : MIR.TyId) : Except String (Nat × Json) := do
  let some entry := prepared.functions.find? (fun f => f.ty == ty) | throw "missing normalized original function signature"
  entry.signature

def kind (prepared : Prepared) (ty : MIR.TyId) : Except String CallFunctionKind := do
  let some entry := prepared.functions.find? (fun f => f.ty == ty) | throw "missing exact compiler function-kind query"
  pure entry.kind

def pointerAbi (prepared : Prepared) (ty : MIR.TyId) (extra : Array MIR.TyId) : Except String (FnAbi MIR.TyId) := do
  let some entry := prepared.pointerAbis.find? (fun e => e.ty == ty && e.extra == extra)
    | throw "missing exact function-pointer/extra-argument FnAbi query"
  entry.result

def hooks (prepared : Prepared) (extern : Json → Except String Extern)
    (base : CallHooks P S C E Other Extern (FnAbi MIR.TyId) (ArgAbi MIR.TyId)) :
    CallHooks P S C E Other Extern (FnAbi MIR.TyId) (ArgAbi MIR.TyId) :=
  { base with
    functionSignature := fun _ layout =>
      match signature prepared layout.ty >>= fun (count,abi) => return (count,← extern abi) with
      | .ok value => pure value | .error error => throw (.unsupported error)
    functionKind := fun ty => match kind prepared ty with
      | .ok value => pure value | .error error => throw (.unsupported error)
    fnAbiOfFnPtr := fun _ layout extra => match pointerAbi prepared layout.ty extra with
      | .ok value => pure value | .error error => throw (.unsupported error) }
/-- Production ExternAbi identity retains every pinned source variant/unwind
field, independently of the target canonical calling convention. -/
def concreteHooks (prepared : Prepared)
    (base : CallHooks P S C E Other ABI.ExternAbi (FnAbi MIR.TyId) (ArgAbi MIR.TyId)) :
    CallHooks P S C E Other ABI.ExternAbi (FnAbi MIR.TyId) (ArgAbi MIR.TyId) :=
  hooks prepared CompilerExternAbi.decode base

end Miri.Input.CompilerFunctionFacts
