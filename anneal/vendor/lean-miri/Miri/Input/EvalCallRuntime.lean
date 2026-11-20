import Miri.Input.EvalConfiguration
import Miri.Interpreter.Panic

/-! Source unwind/panic operational dictionaries over the canonical World.
Only compiler string allocation/lang-item queries and the internal recursive
call edge remain arguments. Reads, writes, allocation materialization,
function-pointer resolution and payload storage are actual source operations.
Sources: shims/{unwind,panic}.rs; interpret/place.rs::mplace_to_imm_ptr. -/
namespace Miri.Input.EvalCallRuntime
open Miri.ABI Miri.Memory Miri.MIR Miri.Interpreter
abbrev User := EvalCoreMachine.User
abbrev State := EvalCoreMachine.State
private def lift (value : Except StepError A) : MachineHooks.M K U A :=
  match value with | .ok value => pure value | .error error => throw error
private def query (value : Except String A) : MachineHooks.M K U A :=
  match value with | .ok value => pure value | .error reason => throw (.unsupported reason)

/-- The recursive call edge is installed internally by the top-level runner.
It is not an after-pop result oracle; Unwind.afterStackPop still owns source
write/pop/resolve/call order and every failure prefix. -/
def unwind
    (access : ValidityMachine.Access MiriMemoryKind (EvalCoreMachine.Stored Os R P H D O Aff B Host))
    (projection : PlaceProjectionHooks Provenance (State Os R P H D O Aff B Host) C MachineHooks.FrameExtra)
    (functions : FunctionPointers.Hooks MiriMemoryKind (User Os R P H D O Aff B Host) O)
    (panicUnwinds : Bool)
    (callFunction : C → CallInstance → Array (RvalueImmTy Provenance) → ReturnContinuation →
      MachineHooks.M MiriMemoryKind (User Os R P H D O Aff B Host) Unit) :
    Unwind.Hooks MiriMemoryKind (User Os R P H D O Aff B Host) C O where
  payloads := fun user => user.payload.payload.user.runtime.unwindPayloads
  setPayloads := fun unwindPayloads user => {user with payload := {user.payload with payload :=
    {user.payload.payload with user := {user.payload.payload.user with runtime :=
      {user.payload.payload.user.runtime with unwindPayloads}}}}}
  readImmediate := fun _ => ValidityMachine.readImmediate access
  readPointer := fun _ operand => do
    let value ← ValidityMachine.readImmediate access operand
    let scalar ← lift (value.imm.toScalar |>.mapError ScalarOps.immediateError)
    lift (scalar.toPointer access.runtime.base |>.mapError ScalarOps.scalarError)
  forceAllocation := forceAllocation projection.place
  getPtrFn := fun _ pointer => FunctionPointers.getPtrFn functions pointer
  callFunction := callFunction
  writeNull := fun c dest => do
    let value ← lift (Scalar.fromInt 0 dest.layout.layout.size |>.mapError ScalarOps.scalarError)
    writePlaceImmediate projection.place c (.scalar value) ⟨.memory dest.mplace,dest.layout⟩
  writeScalar := fun c value dest =>
    writePlaceImmediate projection.place c (.scalar value) ⟨.memory dest.mplace,dest.layout⟩
  panicUnwinds := panicUnwinds

/-- Canonical mplace_to_imm_ptr(None): reference reconstruction precedes
Ty::new_mut_ptr, and its exact compiler layout is queried afterward. -/
def toImmediatePointer (p : CompilerProviders.Prepared) (target : TargetDataLayout)
    (place : MPlaceTy Provenance) : MachineHooks.M K U (RvalueImmTy Provenance) := do
  let immediate ← lift (place.mplace.toRef target |>.mapError fun e =>
    StepError.invalidProgram s!"mplace_to_imm_ptr: {reprStr e}")
  let ty ← query (CompilerRuntimeQueries.mutPointerType p.lifecycle.calls.runtime place.layout.ty)
  let layout ← query (p.runtime.lookup ty |>.mapError toString)
  pure ⟨immediate,layout⟩

structure PanicQueries (K U C : Type) where
  /-- Source tcx.allocate_bytes_dedup + str layout/metadata pipeline. This
  compiler-global allocation operation must retain real pointer provenance. -/
  allocateStringDedup : C → String → MachineHooks.M K U (MPlaceTy Provenance)
  langItem : C → Panic.LangItem → MachineHooks.M K U (Option DefId)
  genericParameters : C → DefId → MachineHooks.M K U (Array MainGenericParameter)

def panic (p : CompilerProviders.Prepared) (queries : PanicQueries K U C)
    (target : TargetDataLayout) (driver : Unwind.Hooks K U C O)
    (operands : OperandMachine.Hooks K U C) : Panic.Hooks K U C O where
  driver := driver
  allocateStringDedup := queries.allocateStringDedup
  toImmediatePointer := fun _ => toImmediatePointer p target
  langItem := queries.langItem
  genericParameters := queries.genericParameters
  evalOperand := fun c op => OperandMachine.evalOperand operands c op none
  evalOperandAt := fun c path op => OperandMachine.evalOperandAt operands c path op none
end Miri.Input.EvalCallRuntime
