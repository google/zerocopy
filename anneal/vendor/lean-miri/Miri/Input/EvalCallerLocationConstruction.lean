import Miri.Input.CompilerValueConstants
import Miri.Interpreter.FunctionPointers
import Miri.Input.AllocationImage

/-! Miri's caller-location intrinsic interns the compiler ConstValue, but
Miri imports the resulting global afresh on each intrinsic evaluation.  This
adapter preserves the immutable CTFE allocation graph and only creates a new
runtime global identity/root; it deliberately does not materialize/read the
template through guest memory. -/
namespace Miri.Input.EvalCallerLocationConstruction
open Lean Miri.ABI Miri.Memory Miri.MIR Miri.Interpreter

def hook (p : CompilerProviders.Prepared)
    (functions : FunctionPointers.Hooks K User Other)
    (currentLocation : MachineHooks.M K User SpanRef)
    (pointee : TyId → Except String (Option TyId))
    (classifyError : ConstantError → StepError)
    (checkKnown : LocalLayout → LocalLayout → MachineHooks.M K User Bool)
    (_ : C) (destination : LocalLayout) : MachineHooks.M K User (OpTy Provenance) := do
  -- Keep the source frame/current-location lookup before consulting the
  -- compiler's cached ConstValue row.
  let span ← currentLocation
  let (ty,value) ← match CompilerValueConstants.callerLocation p span with
    | .ok result => pure result
    | .error reason => throw (.unsupported reason)
  let some currentFrame := (← get).stack.currentFrame? | throw (.stack .emptyStack)
  let (exportId, offset, immutable, sharedRef) ← match value with
    | .Scalar (.Ptr (.Allocation id offset immutable sharedRef)) =>
      pure (id, offset, immutable, sharedRef)
    | _ => throw (.unsupported "caller-location compiler constant is not an allocation pointer")
  unless offset == 0 do
    throw (.unsupported "caller-location compiler constant has a nonzero root offset")
  let state ← get
  let templateId ← match AllocationImage.runtimeId state.machine.memory exportId with
    | .ok id => pure id
    | .error reason => throw (.unsupported reason)
  let template ← match state.machine.memory.findGlobal? templateId with
    | some entry => pure entry
    | none => throw (.unsupported "caller-location CTFE root is absent from imported globals")
  let templateAllocation ← match template.payload with
    | some (.memory allocation) => pure allocation
    | _ => throw (.unsupported "caller-location CTFE root has no memory allocation payload")
  unless template.kind == .memory && template.mutability == .Not &&
      template.size == templateAllocation.byteSize &&
      template.align == templateAllocation.align && templateAllocation.mutability == .Not do
    throw (.unsupported "caller-location CTFE root is not an immutable memory global")
  -- Validate the exact serialized CTFE root flags and imported graph mapping;
  -- the cloned Allocation retains its bytes, init mask, relocations and the
  -- shared filename's CtfeProvenance unchanged.
  match AllocationImage.provenance state.machine.memory exportId immutable sharedRef with
  | .ok _ => pure ()
  | .error reason => throw (.unsupported reason)
  -- Miri allocates/imports the fresh caller-location global before the later
  -- result-layout compatibility checks. Retain this ID/global if those checks
  -- fail, and never deduplicate same-span invocations.
  let (memory,reserved) := state.machine.memory.reserveAllocId
  set {state with machine := {state.machine with memory}}
  let freshId ← match reserved with
    | .ok id => pure id
    | .error error => throw (.resourceExhaustion s!"caller-location global identity: {reprStr error}")
  let state ← get
  let memory := MemoryState.pushGlobal state.machine.memory
    ⟨freshId,.memory,templateAllocation.byteSize,templateAllocation.align,.Not,some (.memory templateAllocation)⟩
  set {state with machine := {state.machine with memory}}
  let pointeeTy ← match pointee ty with
    | .ok (some id) => pure id
    | .ok none => throw (.invalidProgram "caller-location result is not a pointer type")
    | .error reason => throw (.unsupported reason)
  let pointeeLayout ← match p.runtime.lookup pointeeTy with
    | .ok layout => pure layout
    | .error error => throw (.unsupported (toString error))
  unless template.size == pointeeLayout.layout.size &&
      template.align.pow2 == pointeeLayout.layout.align.abi.pow2 do
    throw (.unsupported "caller-location CTFE root layout does not match compiler Location layout")
  let computed ← match p.runtime.lookup ty with
    | .ok layout => pure layout
    | .error error => throw (classifyError (.metadata (toString error)))
  unless ← checkKnown ⟨computed.ty,computed.layout⟩ destination do
    throw (.invalidProgram "known constant layout differs from compiler layout")
  let pointer ← FunctionPointers.rootPointer functions freshId
  let scalar ← match Scalar.fromMaybePointer p.runtime.target.base pointer.withOptionalProvenance with
    | .ok scalar => pure scalar
    | .error error => throw (ScalarOps.scalarError error)
  -- Keep the current frame alive through this operation, just as the ordinary
  -- ConstValue conversion path requires before returning a typed operand.
  let _ := currentFrame
  pure ⟨.immediate (.scalar scalar), destination⟩
end Miri.Input.EvalCallerLocationConstruction
