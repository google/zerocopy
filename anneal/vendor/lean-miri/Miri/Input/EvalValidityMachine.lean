import Miri.Input.EvalProjectionMachine
import Miri.Interpreter.ExecutionValidity
import Miri.Interpreter.FunctionPointerConsumers

/-! Production validity construction at the actual stored Control layer. No
base visitor or independent ghost/union-cache setters enter this interface. -/
namespace Miri.Input.EvalValidityMachine
open Miri.ABI Miri.Memory Miri.MIR Miri.Interpreter

/-- All portable memory/provenance/padding operations are canonical. The final
provider wrapper installs exact compiler paths, source box projection, and
choice-time typed retag preparation over the same state. -/
def hooks [DecidableEq K]
    (prepared : CompilerFactAdapters.Prepared) (runtime : CompilerRuntimeQueries.Prepared)
    (leaves : ExecutionValidity.Leaves (ValidityMachine.State K U) C)
    (access : ValidityMachine.Access K U)
    (allocation : PlaceMachine.AllocationConfig K (ValidityMachine.UserState U))
    (compiler : ValidityMachine.Compiler K U C)
    (projection : PlaceProjectionHooks Provenance (ValidityMachine.State K U) C MachineHooks.FrameExtra)
    (vtable : VTableHooks Provenance (ValidityMachine.State K U) C (FnVal O) (FnAbi TyId))
    (discriminant : DiscriminantHooks Provenance (ValidityMachine.State K U) C (RuntimePlace Provenance))
    (pointers : PointerMachine.Hooks K (ValidityMachine.Control U))
    (retag : TypedRetag.Hooks K (ValidityMachine.UserState U)) (retagBudget : Nat) :
    ValidityVisitor.Hooks Provenance (ValidityMachine.State K U) C MachineHooks.FrameExtra
      (FnVal O) (FnAbi TyId) ValidityMemory.PaddingHandle :=
  let source := ExecutionValidity.hooks leaves access allocation compiler projection vtable discriminant retag retagBudget
  TypedValidityProviders.visitor prepared runtime access allocation compiler pointers retag retagBudget source
end Miri.Input.EvalValidityMachine
