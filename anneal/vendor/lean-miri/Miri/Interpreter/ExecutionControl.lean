import Miri.Interpreter.CallMachine
import Miri.Interpreter.FunctionCalls

/-! Direct source return/unwind dictionary construction. The only compiler
input is bodySpan; no overwritten pop/copy/cleanup callbacks are accepted. -/
namespace Miri.Interpreter.ExecutionControl
open Miri.Memory Miri.ABI Miri.MIR
open MachineHooks (M State FrameExtra)

def hooks [DecidableEq K]
    (bodySpan : Frame Provenance LocalLayout FrameExtra → Except StepError SpanRef)
    (lifecycle : CallMachine.Lifecycle K U C)
    (access : PlaceMachine.AccessConfig K U)
    (place : PlaceHooks Provenance (State K U) C FrameExtra)
    (copy : PlaceCopyHooks Provenance (State K U) C)
    (queries : TypedRetag.Hooks K U)
    (helpers : FunctionCalls.Hooks Provenance (State K U) C FrameExtra O X F A)
    (unwindTerminateFunction : C → UnwindTerminateReason → M K U CallInstance) :
    ControlHooks Provenance LocalLayout FrameExtra (MachineHooks.MachineState K U) C (OpTy Provenance) :=
  let retag := TypedMachineBindings.retagHooks access queries
  {bodySpan := bodySpan
   returnOperand := fun c state => MachineHooks.run (place.localToOp c 0) state
   popFrame := fun _ state => MachineHooks.run (TypedMachineBindings.popRaw retag) state
   copyReturn := fun c value view state => MachineHooks.run
     (copyRuntimePlace place copy c value view.toRuntimePlace true) state
   cleanupFrame := fun c unwinding frame state => MachineHooks.run
     (CallMachine.cleanup lifecycle c unwinding frame) state
   unwindTerminate := fun c reason => MachineHooks.run do
     let callee ← unwindTerminateFunction c reason
     FunctionCalls.callFunction helpers c callee helpers.call.rustAbi #[] none (.goto none .Unreachable)}
end Miri.Interpreter.ExecutionControl
