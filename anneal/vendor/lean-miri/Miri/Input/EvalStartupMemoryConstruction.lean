import Miri.Input.EvalStartupAssembly
import Miri.Input.EvalAllocationMachine
import Miri.Input.EvalCoreMachine
import Miri.Input.EvalConfigurationCore
import Miri.Input.EvalPointerSource
import Miri.Interpreter.ConcurrencyErrors

/-! Build the startup environment's memory bundle from the same fixed source
execution configuration. Deallocation is a machine action composed at each
call site, so span and address-release hooks see the actual active stack. -/
namespace Miri.Input.EvalStartupMemoryConstruction
open Miri.ABI Miri.Memory Miri.MIR Miri.Interpreter

abbrev W := EvalEntryMachine.W
abbrev InnerControl Os R P H D O Aff B Host :=
  ValidityMachine.Control (ThreadStacks.Storage (W Os R P H D O Aff B Host))

def environmentMemory [DecidableEq MiriMemoryKind]
    (prepared : EvalPreparation.Prepared)
    (execution : EvalExecutable.Core Os R P H D O Aff B Host C ClockHost)
    (leaves : EvalConfigurationCore.Leaves Os R P H D O Aff B Host C ClockHost)
    (spans : AllocationDriver.SpanHooks)
    (choice : C)
    (alignment : ValidityMachine.AlignmentCheck)
    (stringScanBudget : Nat) :
    EvalHostRuntimeConstruction.EnvironmentMemory (InnerControl Os R P H D O Aff B Host) C P := Id.run do
  let extras : MemoryExtras.Hooks MiriMemoryKind
      (EvalAllocationMachine.User Os R P H D O Aff B Host) P :=
    EvalCoreMachine.extras leaves.sync ConcurrencyErrors.storeBuffer
  let source : EvalPointerSource.Constructed Os R P H D O Aff B Host :=
    EvalPointerSource.make prepared.compiler prepared.image extras
    leaves.pointerSource choice
  -- Deallocation's sole diagnostic is `FreedAlloc(id)` in Miri's non-halting
  -- diagnostics stream; it does not influence execution. The allocation
  -- diagnostic callback has a different source signature (id, size, align)
  -- and is intentionally not misapplied here.
  let diagnostic : AllocId → PlaceMachine.MachineM MiriMemoryKind
      (EvalAllocationMachine.User Os R P H D O Aff B Host) Unit :=
    fun _ => pure ()
  let nativeDrop := leaves.pointerSource.nativeHost.map fun host =>
    NativeAllocationLifecycle.releaseAllocation
      (NativeAllocationLifecycle.liftBacking host.backing)
  let deallocate := fun pointer old kind =>
    EvalAllocationMachine.deallocateWith spans source.pointers extras
      diagnostic nativeDrop pointer old kind
  let arrays : RuntimeArrayQueries.Access
      (EvalHostRuntimeConstruction.RuntimeState (InnerControl Os R P H D O Aff B Host)) := {
    get := fun state => EvalPointerSource.arrays.get state.machine
    set := fun state world => {state with machine := EvalPointerSource.arrays.set state.machine world} }
  return {
    access := execution.access
    allocation := execution.allocation
    deallocate
    pointers := source.pointers
    projection := execution.projection
    arrays
    symbolicAlignment := alignment == .Symbolic
    enforceAlignment := alignment != .None
    stringScanBudget
    choice
    pointerTy := prepared.layouts.arguments.u8Pointer.ty
    pointerLayout := prepared.layouts.unitPtrMut }

end Miri.Input.EvalStartupMemoryConstruction
