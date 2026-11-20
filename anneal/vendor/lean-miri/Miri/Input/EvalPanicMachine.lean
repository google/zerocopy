import Miri.Input.CompilerPanicFacts
import Miri.Input.CompilerGlobalBytes
import Miri.Input.EvalCallRuntime

/-! Actual source panic query closure. Byte catalog attachment precedes runtime
allocation; each panic still samples its salt and adjusts the actual global
root before metadata/layout construction and lang-item lookup. -/
namespace Miri.Input.EvalPanicMachine
open Miri.ABI Miri.Memory Miri.MIR Miri.Interpreter
private def query (value : Except String A) : MachineHooks.M K U A :=
  match value with | .ok value => pure value | .error error => throw (.unsupported error)

def queries (program : LoweredProgram) (runtime : RuntimeMetadata)
    (bytes : CompilerGlobalBytes.Prepared)
    (functions : FunctionPointers.Hooks K (ValidityMachine.UserState U) O)
    (access : ValidityMachine.Access K U) [DecidableEq K] :
    EvalCallRuntime.PanicQueries K (ValidityMachine.UserState U) C where
  allocateStringDedup := fun _ text => GlobalByteMachine.string functions access
    (CompilerGlobalBytes.strLayout runtime bytes) text
  langItem := fun _ item => query (CompilerPanicFacts.langItem program item)
  genericParameters := fun _ id => query (CompilerPanicFacts.genericParameters program id)
end Miri.Input.EvalPanicMachine
