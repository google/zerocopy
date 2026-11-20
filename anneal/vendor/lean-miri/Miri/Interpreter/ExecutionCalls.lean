import Miri.Interpreter.FunctionPointers
import Miri.Interpreter.ExecutionCallLeaves
import Miri.Interpreter.CallMachine
import Miri.Interpreter.OperandMachine
import Miri.Interpreter.RawMemoryMachine

/-! Construct complete CallHooks from canonical runtime operations. Unlike a
record-update adapter this accepts no independently supplied frame, local,
copy, retag, varargs, virtual or lifecycle operation to overwrite later. -/
namespace Miri.Interpreter.ExecutionCalls
open Miri.ABI Miri.Memory Miri.MIR
open MachineHooks (M State FrameExtra)

private def lift (value : Except StepError A) : M K U A :=
  match value with | .ok value => pure value | .error error => throw error

/-- Runtime receiver operations are the same actual reads/typed projections
as ordinary operands. Source pointer construction caches alignment only. -/
def virtualHooks [DecidableEq K] (leaves : ExecutionCallLeaves.Virtual K U C)
    (access : PlaceMachine.AccessConfig K U) (operands : OperandMachine.Hooks K U C)
    (debugAssertions : Bool) : VirtualCalls.Hooks Provenance (State K U) C FrameExtra where
  debugAssertions := debugAssertions
  compiler := leaves.compiler
  target := access.runtime.base
  vtable := leaves.vtable
  getFrame := MachineHooks.currentFrame
  readImmediate := fun _ => PlaceMachine.readImmediate access
  immPtrToMPlace := fun _ => VirtualCalls.pointerPlace leaves.compiler access.runtime.base
    (PointerPlaceMachine.misalignmentWith access leaves.alignment)
  projectField := OperandMachine.field operands

/-- Source fn_arg_project_field retains Copy versus InPlace. -/
def projectArgument (operands : OperandMachine.Hooks K U C) (choice : C)
    (argument : FnArg Provenance) (index : Nat) : M K U (FnArg Provenance) := do
  match argument with
  | .Copy operand => return .Copy (← OperandMachine.field operands choice operand index)
  | .InPlace memory =>
    let result ← OperandMachine.field operands choice ⟨.indirect memory.mplace,memory.layout⟩ index
    match result.op with
    | .indirect memory => return .InPlace ⟨memory,result.layout⟩
    | .immediate _ => throw (.invalidProgram "in-place argument projection became immediate")

private def memoryPlace (place : RuntimePlace Provenance) : M K U (MPlaceTy Provenance) :=
  match place.ref with
  | .memory memory => pure ⟨memory,place.layout⟩
  | .local .. => throw (.invalidProgram "memory varargs projection became a local")

def make [DecidableEq K] (leaves : ExecutionCallLeaves.Hooks (State K U) C Other Extern)
    (lifecycle : CallMachine.Lifecycle K U C)
    (access : PlaceMachine.AccessConfig K U) (allocation : PlaceMachine.AllocationConfig K U)
    (compiler : PlaceMachine.CompilerHooks K U C) (copy : PlaceCopyHooks Provenance (State K U) C)
    (queries : TypedRetag.Hooks K U) (retagBudget virtualBudget : Nat)
    (operands : OperandMachine.Hooks K U C)
    (projection : PlaceProjectionHooks Provenance (State K U) C FrameExtra)
    (functions : FunctionPointers.Hooks K U Other)
    (virtual : VirtualCalls.Hooks Provenance (State K U) C FrameExtra)
    (varargs : IntrinsicVarArgsHooks Provenance (State K U) C (RuntimePlace Provenance))
    (arithmetic : PointerArithmetic)
    (intrinsic : C → CallInstance → Array (OpTy Provenance) → RuntimeStackPlace Provenance →
      Option BasicBlockId → UnwindAction → M K U (Option CallInstance)) :
    CallHooks Provenance (State K U) C FrameExtra Other Extern (FnAbi TyId) (ArgAbi TyId) :=
  let place := projection.place
  let retag := queries
  let writePointer := fun c pointer (dest : MPlaceTy Provenance) => do
    let scalar ← lift (Scalar.fromMaybePointer access.runtime.base pointer |>.mapError ScalarOps.scalarError)
    writePlaceImmediate place c (.scalar scalar) ⟨.memory dest.mplace,dest.layout⟩
  {debugAssertions := compiler.debugAssertions
   getFrame := MachineHooks.currentFrame
   setFrame := MachineHooks.setCurrentFrame
   frameIndex := do match (← get).stack.frameIndex with
      | .ok index => pure index | .error error => throw (.stack error)
   evalOperand := fun c operand => OperandMachine.evalOperand operands c operand none
   evalOperandAt := fun c path operand => OperandMachine.evalOperandAt operands c path operand none
   evalPlace := fun c dest skip => return (← PlaceDynamic.evalPlace projection c dest skip).stackView
   placeToOp := fun c dest => placeToOp place c dest.toRuntimePlace
   forceAllocation := fun c dest => forceAllocation place c dest.toRuntimePlace
   functionSignature := leaves.compiler.functionSignature
   functionKind := leaves.compiler.functionKind
   readPointer := fun _ operand => do
      let value ← PlaceMachine.readImmediate access operand
      let scalar ← lift (value.imm.toScalar.mapError ScalarOps.immediateError)
      lift (scalar.toPointer access.runtime.base |>.mapError ScalarOps.scalarError)
   getPtrFn := fun _ pointer => FunctionPointers.getPtrFn functions pointer
   resolve := leaves.compiler.resolve
   fnAbiOfFnPtr := leaves.compiler.fnAbiOfFnPtr
   fnAbiOfInstance := leaves.compiler.fnAbiOfInstance
   requiresCallerLocation := virtual.compiler.requiresCallerLocation
   callerLocation := VirtualCalls.callerLocation virtual virtualBudget
   abiCanUnwind := FnAbi.canUnwind
   abiVariadic := FnAbi.cVariadic
   abiFixedCount := fun abi => abi.fixedCount.toNat
   abiArgs := FnAbi.args
   abiReturn := FnAbi.ret
   sameConvention := fun left right => left.conv == right.conv
   isRustCall := leaves.compiler.isRustCall
   rustAbi := leaves.compiler.rustAbi
   argLayout := ArgAbi.layout
   argIsIgnore := ArgAbi.isIgnore
   isOneZst := fun layout => layout.layout.is1zst
   checkArgumentCompat := leaves.compiler.checkArgumentCompat
   checkTargetFeatures := fun _ callee => ExecutionCallLeaves.checkTargetFeatures leaves.compiler.targetFeatures callee
   tupleFields := leaves.compiler.tupleFields
   projectFnArg := projectArgument operands
   localLayout := PlaceMachine.layoutLocal compiler
   localSpan := compiler.localSpan
   storageLiveDyn := fun _ id metadata => MachineHooks.storageLiveDyn lifecycle.storage id metadata
   copyAllowTransmute := fun c source dest => copyRuntimePlace place copy c source dest.toRuntimePlace true
   protectArgument := fun _ memory => TypedRetag.protectInPlaceFunctionArgument retag retagBudget memory
   withRetagMode := fun _ mode action => MachineHooks.withRetagMode mode action
   nonCapturingClosure := fun _ callee abi => ExecutionCallLeaves.nonCapturingClosure leaves.compiler callee abi
   allocateStack := fun _ layout => PlaceMachine.allocateStack allocation layout
   copyToMemory := fun c source dest => copyRuntimePlace place copy c source ⟨.memory dest.mplace,dest.layout⟩ false
   vaListPtr := fun c values => IntrinsicVarArgs.createList varargs c
      (values.toList.map fun value => ⟨.memory value.mplace,value.layout⟩)
   writeZeroBytes := fun _ pointer size => RawMemoryMachine.writeRepeatedByte access arithmetic pointer 0 size.bytes
   vaListKeyField := fun c memory => do
      memoryPlace (← IntrinsicVarArgs.keyField varargs c ⟨.memory memory.mplace,memory.layout⟩)
   writePointerToMemory := writePointer
   pushRaw := fun _ => CallMachine.pushRaw lifecycle compiler.debugAssertions
   pushDone := fun _ => CallMachine.pushDone lifecycle
   popRaw := fun _ => TypedMachineBindings.popRaw retag
   cleanup := CallMachine.cleanup lifecycle
   -- Miri inherits the source rustc Machine::after_stack_frame_init empty hook.
   afterFrameInit := fun _ => pure ()
   callExtra := CallDispatchMachine.callExtra leaves.dispatch
   callIntrinsic := intrinsic
   callLlvmIntrinsic := fun c callee args dest ret => do
      let name ← leaves.compiler.llvmLinkName callee
      IntrinsicArchitecture.callLlvm (← leaves.llvm callee) c name args dest.toRuntimePlace ret
   findMirOrEvalFn := CallDispatchMachine.findMirOrEvalFn leaves.dispatch
   resolveVirtual := fun c callee method slot abi args =>
      VirtualCalls.resolveVirtual virtual c virtualBudget callee method slot abi args
   isDynamic := fun ty => return (← virtual.compiler.classifyReceiver ty) == .dynamic
   unpackDynForDrop := VirtualCalls.unpackDynForDrop virtual
   resolveDropGlue := fun _ ty => virtual.compiler.resolveDropGlue ty
   mplaceToMutRef := fun _ memory => VirtualCalls.mplaceToMutRef virtual memory
   fakeUnitReturn := fun _ => do
      let layout ← virtual.compiler.unitLayout
      match FunctionCalls.fakeAllocZst layout with
      | .ok memory => pure (.memory memory)
      | .error error => throw error}
/-- Actual helpers.rs call/thread-root helper dictionary. Origin mutations
keep all other thread/stack fields, including saved full frame identities. -/
def helpers (leaves : ExecutionCallLeaves.Helpers (State K U) C Extern)
    (calls : CallHooks Provenance (State K U) C FrameExtra Other Extern (FnAbi TyId) (ArgAbi TyId)) :
    FunctionCalls.Hooks Provenance (State K U) C FrameExtra Other Extern (FnAbi TyId) (ArgAbi TyId) where
  call := calls
  loadMir := leaves.loadMir
  unitLayout := leaves.unitLayout
  fnAbiOfSignature := leaves.fnAbiOfSignature
  callerLocationType := leaves.callerLocationType
  activeStackEmpty := return (← get).stack.frames.isEmpty
  originIsDummy := do
    let some thread := (← get).machine.threads.activeThread?
      | throw (.invalidProgram "active source helper thread is absent")
    return thread.originSpanToken == leaves.dummySpan.id
  setOrigin := fun span => do
    let state ← get
    let manager := state.machine.threads
    let some thread := manager.activeThread?
      | throw (.invalidProgram "active source helper thread is absent")
    set {state with machine := {state.machine with threads := {manager with
      threads := manager.threads.set manager.activeThread.toNat {thread with originSpanToken := span.id}}}}

end Miri.Interpreter.ExecutionCalls
