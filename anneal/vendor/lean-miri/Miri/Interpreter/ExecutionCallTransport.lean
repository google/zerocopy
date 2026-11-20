import Miri.Interpreter.ExecutionStateTransport
import Miri.Interpreter.FunctionCalls

/-! Complete source call dictionary reassociation for actual outer thread
stacks. No call, return copy, retag scope or failure state is replaced. -/
namespace Miri.Interpreter.ExecutionCallTransport
open Miri.Memory Miri.ABI
open ExecutionStateTransport

def calls (h : CallHooks P (MachineHooks.State K (Inner U)) C E O X F A) :
    CallHooks P (MachineHooks.State K (Outer U)) C E O X F A where
  debugAssertions := h.debugAssertions
  getFrame := action (h.getFrame)
  setFrame := fun a0 => action (h.setFrame a0)
  frameIndex := action (h.frameIndex)
  evalOperand := fun a0 a1 => action (h.evalOperand a0 a1)
  evalOperandAt := fun a0 a1 a2 => action (h.evalOperandAt a0 a1 a2)
  evalPlace := fun a0 a1 a2 => action (h.evalPlace a0 a1 a2)
  placeToOp := fun a0 a1 => action (h.placeToOp a0 a1)
  forceAllocation := fun a0 a1 => action (h.forceAllocation a0 a1)
  functionSignature := fun a0 a1 => action (h.functionSignature a0 a1)
  functionKind := fun a0 => action (h.functionKind a0)
  readPointer := fun a0 a1 => action (h.readPointer a0 a1)
  getPtrFn := fun a0 a1 => action (h.getPtrFn a0 a1)
  resolve := fun a0 a1 a2 => action (h.resolve a0 a1 a2)
  fnAbiOfFnPtr := fun a0 a1 a2 => action (h.fnAbiOfFnPtr a0 a1 a2)
  fnAbiOfInstance := fun a0 a1 a2 => action (h.fnAbiOfInstance a0 a1 a2)
  requiresCallerLocation := fun a0 => action (h.requiresCallerLocation a0)
  callerLocation := action (h.callerLocation)
  abiCanUnwind := h.abiCanUnwind
  abiVariadic := h.abiVariadic
  abiFixedCount := h.abiFixedCount
  abiArgs := h.abiArgs
  abiReturn := h.abiReturn
  sameConvention := h.sameConvention
  isRustCall := h.isRustCall
  rustAbi := h.rustAbi
  argLayout := h.argLayout
  argIsIgnore := h.argIsIgnore
  isOneZst := h.isOneZst
  checkArgumentCompat := fun a0 a1 a2 => action (h.checkArgumentCompat a0 a1 a2)
  checkTargetFeatures := fun a0 a1 => action (h.checkTargetFeatures a0 a1)
  tupleFields := fun a0 => action (h.tupleFields a0)
  projectFnArg := fun a0 a1 a2 => action (h.projectFnArg a0 a1 a2)
  localLayout := fun a0 a1 => action (h.localLayout a0 a1)
  localSpan := fun a0 a1 => action (h.localSpan a0 a1)
  storageLiveDyn := fun a0 a1 a2 => action (h.storageLiveDyn a0 a1 a2)
  copyAllowTransmute := fun a0 a1 a2 => action (h.copyAllowTransmute a0 a1 a2)
  protectArgument := fun a0 a1 => action (h.protectArgument a0 a1)
  withRetagMode := fun c mode body => action (h.withRetagMode c mode (reverseAction body))
  nonCapturingClosure := fun a0 a1 a2 => action (h.nonCapturingClosure a0 a1 a2)
  allocateStack := fun a0 a1 => action (h.allocateStack a0 a1)
  copyToMemory := fun a0 a1 a2 => action (h.copyToMemory a0 a1 a2)
  vaListPtr := fun a0 a1 => action (h.vaListPtr a0 a1)
  writeZeroBytes := fun a0 a1 a2 => action (h.writeZeroBytes a0 a1 a2)
  vaListKeyField := fun a0 a1 => action (h.vaListKeyField a0 a1)
  writePointerToMemory := fun a0 a1 a2 => action (h.writePointerToMemory a0 a1 a2)
  pushRaw := fun a0 a1 a2 a3 a4 => action (h.pushRaw a0 a1 a2 a3 a4)
  pushDone := fun a0 => action (h.pushDone a0)
  popRaw := fun a0 => action (h.popRaw a0)
  cleanup := fun a0 a1 a2 => action (h.cleanup a0 a1 a2)
  afterFrameInit := fun a0 => action (h.afterFrameInit a0)
  callExtra := fun a0 a1 a2 a3 a4 a5 a6 => action (h.callExtra a0 a1 a2 a3 a4 a5 a6)
  callIntrinsic := fun a0 a1 a2 a3 a4 a5 => action (h.callIntrinsic a0 a1 a2 a3 a4 a5)
  callLlvmIntrinsic := fun a0 a1 a2 a3 a4 => action (h.callLlvmIntrinsic a0 a1 a2 a3 a4)
  findMirOrEvalFn := fun a0 a1 a2 a3 a4 a5 a6 => action (h.findMirOrEvalFn a0 a1 a2 a3 a4 a5 a6)
  resolveVirtual := fun a0 a1 a2 a3 a4 a5 => action (h.resolveVirtual a0 a1 a2 a3 a4 a5)
  isDynamic := fun a0 => action (h.isDynamic a0)
  unpackDynForDrop := fun a0 a1 => action (h.unpackDynForDrop a0 a1)
  resolveDropGlue := fun a0 a1 => action (h.resolveDropGlue a0 a1)
  mplaceToMutRef := fun a0 a1 => action (h.mplaceToMutRef a0 a1)
  fakeUnitReturn := fun a0 => action (h.fakeUnitReturn a0)

def functions (h : FunctionCalls.Hooks P (MachineHooks.State K (Inner U)) C E O X F A) :
    FunctionCalls.Hooks P (MachineHooks.State K (Outer U)) C E O X F A where
  call := calls h.call
  loadMir := fun c callee => action (h.loadMir c callee)
  unitLayout := h.unitLayout
  fnAbiOfSignature := fun c request => action (h.fnAbiOfSignature c request)
  callerLocationType := action h.callerLocationType
  activeStackEmpty := action h.activeStackEmpty
  originIsDummy := action h.originIsDummy
  setOrigin := fun span => action (h.setOrigin span)

def pointers (h : FunctionPointers.Hooks K (Inner U) O) : FunctionPointers.Hooks K (Outer U) O where
  registry := fun u => h.registry (toInner u)
  putRegistry := fun u r => toOuter (h.putRegistry (toInner u) r)
  crossCrateInlineAlways := h.crossCrateInlineAlways
  inlineNever := fun callee => action (h.inlineNever callee)
  chooseSalt := action h.chooseSalt
  ptrGetAlloc := fun pointer => action (h.ptrGetAlloc pointer)
  adjustRootPointer := fun id tag => action (h.adjustRootPointer id tag)
  importedFunction := fun id => action (h.importedFunction id)
end Miri.Interpreter.ExecutionCallTransport
