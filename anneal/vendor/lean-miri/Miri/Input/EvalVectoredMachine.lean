import Miri.Input.EvalCompilerMachine
import Miri.Input.CompilerNamedFields
import Miri.Interpreter.UnixVectoredMachine

/-! Close vectored IO on the actual EvalWorld type interner, pointer state,
Stack allocator and deallocation lifecycle. No standalone temporary-memory
model or invented iovec field/type identity is supplied by the caller. -/
namespace Miri.Input.EvalVectoredMachine
open Miri.ABI Miri.Memory Miri.MIR Miri.Interpreter
abbrev User := EvalCoreMachine.User
abbrev State := EvalCoreMachine.State
private def lift (value : Except String A) : MachineHooks.M K U A :=
  match value with | .ok value => pure value | .error reason => throw (.unsupported reason)

def hooks (runtime : RuntimeMetadata)
    (config : ExecutionMachine.Config MiriMemoryKind (User Os R P H D O Aff B WorldHost) C O X ClockHost)
    (choice : C) (spans : AllocationDriver.SpanHooks)
    (pointers : PointerMachine.Hooks MiriMemoryKind
      (ValidityMachine.Control (ThreadStacks.Storage (EvalWorld.World Os R P H D O Aff B WorldHost))))
    (extras : MemoryExtras.Hooks MiriMemoryKind (User Os R P H D O Aff B WorldHost) P)
    (deallocation : AllocationMachine.DeallocationHooks MiriMemoryKind
      (User Os R P H D O Aff B WorldHost) P)
    (base : UnixVectored.Hooks (State Os R P H D O Aff B WorldHost) H D O E Meta) :
    UnixVectored.Hooks (State Os R P H D O Aff B WorldHost) H D O E Meta :=
  UnixVectoredMachine.bind config.access config.allocation pointers
    (ExecutionMachine.projectionHooks config)
    (PlaceMachine.placeHooks config.access config.allocation config.compiler) choice
    (lift (CompilerPrimitiveFacts.unitLayout runtime))
    (CompilerNamedFields.iovecArrayLayout runtime EvalProjectionMachine.arrays)
    (fun parent name => do
      match CompilerNamedFields.fieldIndex runtime parent name with
      | .ok index => pure index | .error error => throw error)
    (fun pointer => EvalAllocationMachine.deallocate spans pointers extras deallocation pointer none .stack)
    base
end Miri.Input.EvalVectoredMachine
