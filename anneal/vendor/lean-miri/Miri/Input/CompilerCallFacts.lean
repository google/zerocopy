import Miri.Input.CompilerIntrinsicFacts

/-! call.rs find_mir_or_eval_fn and noncapturing-closure source predicates.
Exact full-instance evidence supplies compiler symbol spelling; neither source
definition paths nor debug displays substitute for tcx.symbol_name(instance).
-/
namespace Miri.Input.CompilerCallFacts
open Lean Miri.Interpreter
private def entry (p : CompilerIntrinsicFacts.Prepared) (callee : CallInstance) : Except String Json := do
  let some value := p.entries.find? (·.callee == callee) | throw "missing exact full-instance call facts"
  pure value.payload

def isForeignItem (p : CompilerIntrinsicFacts.Prepared) (callee : CallInstance) : Except String Bool := do
  (← (← entry p callee).getObjVal? "is_foreign_item").getBool?

def isClosureLike (p : CompilerIntrinsicFacts.Prepared) (callee : CallInstance) : Except String Bool := do
  (← (← entry p callee).getObjVal? "is_closure_like").getBool?

def symbolName (p : CompilerIntrinsicFacts.Prepared) (callee : CallInstance) : Except String String := do
  let query ← (← entry p callee).getObjVal? "symbol_name"
  unless (← (← query.getObjVal? "status").getStr?) == "supported" do
    throw "compiler symbol name query requires a complete concrete callable instance"
  (← query.getObjVal? "value").getStr?
/-- LLVM source dispatch reads codegen attributes, not mangled symbol_name. -/
def codegenSymbolName (p : CompilerIntrinsicFacts.Prepared) (callee : CallInstance) : Except String (Option String) := do
  let query ← (← entry p callee).getObjVal? "codegen_symbol_name"
  unless (← (← query.getObjVal? "status").getStr?) == "supported" do
    throw "definition does not support exact codegen symbol attributes"
  let value ← query.getObjVal? "value"
  if value == .null then pure none else return some (← value.getStr?)
end Miri.Input.CompilerCallFacts
