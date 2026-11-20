import Miri.Input.CompilerProviders
import Miri.Interpreter.GlobalAllocationMachine

/-! Compiler initializer queries and canonical global materialization share
the imported AllocationImage identity map; no initializer bytes are guessed. -/
namespace Miri.Input.EvalGlobalAllocationMachine
open Miri.Memory Miri.Interpreter

def make [DecidableEq K] (p : CompilerProviders.Prepared) (image : AllocationImage.Imported)
    (extras : MemoryExtras.Hooks K U P)
    (leaves : GlobalAllocationMachine.Leaves K U) :
    GlobalAllocationHooks Provenance Miri.TreeBorrows.BorrowTree K
      (PlaceMachine.AccessState K U) :=
  GlobalAllocationMachine.hooks p.runtime.target.base extras leaves fun memory state definition =>
    let result := image.evaluateStaticInitializer {state with machine := {state.machine with memory}} definition
    ⟨result.state.machine.memory,result.state,result.outcome⟩

end Miri.Input.EvalGlobalAllocationMachine
