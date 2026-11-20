import Miri.Interpreter.OperandPath
import Miri.Interpreter.Unwind
import Miri.Interpreter.MainThread

/-! Pinned shims/panic.rs and mir/terminator.rs::AssertKind::panic_function.
These operations call the actual panic lang item; a failed assertion is not
silently converted into a normal return, UB, or a completed unwind. -/
namespace Miri.Interpreter.Panic
open Miri.Memory Miri.MIR
open MachineHooks (M)

inductive LangItem where
  | Panic | PanicNounwind | PanicBoundsCheck | PanicMisalignedPointerDereference
  | PanicAddOverflow | PanicSubOverflow | PanicMulOverflow | PanicDivOverflow
  | PanicRemOverflow | PanicNegOverflow | PanicShrOverflow | PanicShlOverflow
  | PanicDivZero | PanicRemZero | PanicNullPointerDereference | PanicNullReferenceConstructed
  | PanicInvalidEnumConstruction
  | PanicCoroutineResumed | PanicAsyncFnResumed | PanicAsyncGenFnResumed | PanicGenFnNone
  | PanicCoroutineResumedPanic | PanicAsyncFnResumedPanic | PanicAsyncGenFnResumedPanic | PanicGenFnNonePanic
  | PanicCoroutineResumedDrop | PanicAsyncFnResumedDrop | PanicAsyncGenFnResumedDrop | PanicGenFnNoneDrop
  deriving DecidableEq, Repr

private def afterReturn : CoroutineKind → LangItem
  | .Coroutine _ => .PanicCoroutineResumed
  | .Desugared .Async _ => .PanicAsyncFnResumed
  | .Desugared .AsyncGen _ => .PanicAsyncGenFnResumed
  | .Desugared .Gen _ => .PanicGenFnNone
private def afterPanic : CoroutineKind → LangItem
  | .Coroutine _ => .PanicCoroutineResumedPanic
  | .Desugared .Async _ => .PanicAsyncFnResumedPanic
  | .Desugared .AsyncGen _ => .PanicAsyncGenFnResumedPanic
  | .Desugared .Gen _ => .PanicGenFnNonePanic
private def afterDrop : CoroutineKind → LangItem
  | .Coroutine _ => .PanicCoroutineResumedDrop
  | .Desugared .Async _ => .PanicAsyncFnResumedDrop
  | .Desugared .AsyncGen _ => .PanicAsyncGenFnResumedDrop
  | .Desugared .Gen _ => .PanicGenFnNoneDrop

/-- Exact source mapping; bounds/misalignment use their argument-bearing
special handlers and impossible overflowing operators are compiler errors. -/
def assertLangItem : AssertKind → Except StepError LangItem
  | .Overflow .Add .. => .ok .PanicAddOverflow
  | .Overflow .Sub .. => .ok .PanicSubOverflow
  | .Overflow .Mul .. => .ok .PanicMulOverflow
  | .Overflow .Div .. => .ok .PanicDivOverflow
  | .Overflow .Rem .. => .ok .PanicRemOverflow
  | .Overflow .Shr .. => .ok .PanicShrOverflow
  | .Overflow .Shl .. => .ok .PanicShlOverflow
  | .Overflow .. => .error (.invalidProgram "non-overflowing operator in AssertKind::Overflow")
  | .OverflowNeg _ => .ok .PanicNegOverflow
  | .DivisionByZero _ => .ok .PanicDivZero
  | .RemainderByZero _ => .ok .PanicRemZero
  | .ResumedAfterReturn kind => .ok (afterReturn kind)
  | .ResumedAfterPanic kind => .ok (afterPanic kind)
  | .ResumedAfterDrop kind => .ok (afterDrop kind)
  | .NullPointerDereference => .ok .PanicNullPointerDereference
  | .NullReferenceConstructed => .ok .PanicNullReferenceConstructed
  | .InvalidEnumConstruction _ => .ok .PanicInvalidEnumConstruction
  | .BoundsCheck .. | .MisalignedPointerDereference .. =>
    .error (.invalidProgram "special AssertKind passed to panic_function")

structure Hooks (K User C Other : Type) where
  driver : Unwind.Hooks K User C Other
  allocateStringDedup : C → String → M K User (MPlaceTy Provenance)
  toImmediatePointer : C → MPlaceTy Provenance → M K User (RvalueImmTy Provenance)
  langItem : C → LangItem → M K User (Option DefId)
  genericParameters : C → DefId → M K User (Array MainGenericParameter)
  evalOperand : C → MIR.Operand → M K User (OpTy Provenance)
  evalOperandAt : C → OperandPath → MIR.Operand → M K User (OpTy Provenance) := fun c _ => evalOperand c

private def mono (h : Hooks K User C Other) (choice : C) (item : LangItem) : M K User CallInstance := do
  let some definition ← h.langItem choice item |
    throw (.invalidProgram "missing panic language item")
  let mut args := #[]
  for parameter in ← h.genericParameters choice definition do
    match parameter with
    | .lifetime => args := args.push (.Lifetime .Erased)
    | .typeParameter | .constParameter =>
      throw (.invalidProgram "Instance::mono called on type/const generic panic item")
  return ⟨.Item definition, args⟩

private def call (h : Hooks K User C Other) (choice : C) (item : LangItem)
    (args : Array (RvalueImmTy Provenance)) (unwind : UnwindAction) : M K User Unit := do
  let fnInstance ← mono h choice item
  h.driver.callFunction choice fnInstance args (.goto none unwind)

/-- Allocate/deduplicate the message before resolving the panic lang item. -/
def start (h : Hooks K User C Other) (choice : C) (message : String)
    (unwind : UnwindAction) : M K User Unit := do
  let message ← h.allocateStringDedup choice message
  let fnInstance ← mono h choice .Panic
  let arg ← h.toImmediatePointer choice message
  h.driver.callFunction choice fnInstance #[arg] (.goto none unwind)

def startNounwind (h : Hooks K User C Other) (choice : C) (message : String) : M K User Unit := do
  let message ← h.allocateStringDedup choice message
  let fnInstance ← mono h choice .PanicNounwind
  let arg ← h.toImmediatePointer choice message
  h.driver.callFunction choice fnInstance #[arg] (.goto none .Unreachable)

/-- Read only the operands read by the source: index before length for bounds,
required before found for alignment, no diagnostic operand reads otherwise. -/
def assertPanic (h : Hooks K User C Other) (choice : C)
    (message : AssertKind) (unwind : UnwindAction) : M K User Unit := do
  match message with
  | .BoundsCheck len index =>
    let index ← h.driver.readImmediate choice (← h.evalOperandAt choice (OperandPath.assertion "index") index)
    let len ← h.driver.readImmediate choice (← h.evalOperandAt choice (OperandPath.assertion "length") len)
    call h choice .PanicBoundsCheck #[index, len] unwind
  | .MisalignedPointerDereference required found =>
    let required ← h.driver.readImmediate choice (← h.evalOperandAt choice (OperandPath.assertion "required") required)
    let found ← h.driver.readImmediate choice (← h.evalOperandAt choice (OperandPath.assertion "found") found)
    call h choice .PanicMisalignedPointerDereference #[required, found] unwind
  | _ =>
    let item ← match assertLangItem message with
      | .ok item => pure item
      | .error error => throw error
    call h choice item #[] unwind

end Miri.Interpreter.Panic
