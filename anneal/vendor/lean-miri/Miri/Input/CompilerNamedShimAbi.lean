import Miri.Input.CallResolution

/-! Name-keyed source shim requests whose argument types require compiler path
lookup (currently libc::pid_t CPU affinity signatures). No libc typedef is
replaced with an integer chosen by its size or diagnostic name. -/
namespace Miri.Input.CompilerNamedShimAbi
open Lean Miri.ABI Miri.Interpreter
structure Entry where
  name : String
  abi : Except String (FnAbi MIR.TyId)
structure Prepared where
  entries : Array Entry
private def supported (j : Json) : Except String Unit := do
  unless (← (← j.getObjVal? "status").getStr?) == "supported" do
    throw s!"named shim ABI query unavailable: {((j.getObjVal? "reason").bind Json.getStr?).toOption}"

def prepare (runtime : RuntimeMetadata)
    (abiCache : Option (CallResolution.FunctionAbiCache runtime) := none) : Except String Prepared := do
  let records ← (← runtime.source.raw.getObjVal? "compiler_named_shim_abis").getArr?
  let mut entries := #[]
  for record in records do
    let name ← (← record.getObjVal? "name").getStr?
    unless !(entries.any (·.name == name)) do throw "duplicate named compiler shim query"
    let recipe ← record.getObjVal? "recipe"
    unless (← (← recipe.getObjVal? "typing_env").getStr?) == "fully_monomorphized" do
      throw "named shim typing environment mismatch"
    let abi := do
      let query ← recipe.getObjVal? "query"
      supported query
      let result ← query.getObjVal? "abi_query"
      supported result
      CallResolution.functionAbiJson runtime (← result.getObjVal? "value") abiCache
    entries := entries.push ⟨name,abi⟩
  pure ⟨entries⟩

def expectedAbi (prepared : Prepared) (name : String) : Except String (FnAbi MIR.TyId) := do
  let some entry := prepared.entries.find? (·.name == name)
    | throw s!"missing exact named compiler shim ABI query {name}"
  entry.abi

def query (prepared : Prepared) (name : String) : EStateM StepError S (FnAbi MIR.TyId) :=
  match expectedAbi prepared name with
  | .ok abi => pure abi
  | .error reason => throw (.unsupported reason)
end Miri.Input.CompilerNamedShimAbi
