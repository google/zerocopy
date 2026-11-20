import Miri.Interpreter.Rvalue
import Miri.Interpreter.IntegerOps

/-! Typed dispatch from pinned `interpret/operator.rs::binary_op/unary_op`.
Compiler classification and result layouts are required queries. Float and
pointer operations remain explicit machine obligations. -/
namespace Miri.Interpreter
open Miri.ABI Miri.Memory Miri.MIR

inductive ScalarTypeClass where
  | boolean | character | integer (kind : IntegerKind) | floating | pointer | functionPointer
  deriving DecidableEq, Repr

structure ScalarOpsHooks (Prov S C : Type) where
  classify : C → MIR.TyId → RvalueM S ScalarTypeClass
  boolLayout : C → RvalueM S (TyAndLayout MIR.TyId)
  orderingLayout : C → RvalueM S (TyAndLayout MIR.TyId)
  overflowLayout : C → TyAndLayout MIR.TyId → RvalueM S (TyAndLayout MIR.TyId)
  metadataLayout : C → MIR.TyId → RvalueM S (TyAndLayout MIR.TyId)
  unitLayout : C → RvalueM S (TyAndLayout MIR.TyId)
  floatBinary : C → BinOp → RvalueImmTy Prov → RvalueImmTy Prov → RvalueM S (RvalueImmTy Prov)
  pointerBinary : C → BinOp → RvalueImmTy Prov → RvalueImmTy Prov → RvalueM S (RvalueImmTy Prov)
  floatUnary : C → UnOp → RvalueImmTy Prov → RvalueM S (RvalueImmTy Prov)
  derefValidity : C → RvalueImmTy Prov → RvalueM S Unit

namespace ScalarOps

def scalarIntError : ScalarIntError → StepError
  | e@(.invalidBool _) | e@(.invalidChar _) => .undefinedBehavior (toString e)
  | e => .invalidProgram (toString e)

def scalarError : ScalarError → StepError
  | .scalarInt e => scalarIntError e
  | .readPointerAsInt => .unsupported "read pointer as integer"
  | e => .invalidProgram (toString e)

def immediateError : ImmediateError → StepError
  | .scalar e => scalarError e
  | .unexpectedUninit => .invalidProgram "uninitialized immediate reached scalar operator"
  | .expectedInteger => .unsupported "read pointer as integer"
  | e => .invalidProgram s!"{repr e}"

def integerError : IntegerOpError → StepError
  | .scalar e => scalarIntError e
  | .undefinedBehavior e => .undefinedBehavior s!"{repr e}"
  | e => .invalidProgram s!"{repr e}"

private def liftResult (result : Except StepError A) : RvalueM S A :=
  match result with | .ok value => pure value | .error reason => throw reason

private def toScalar (value : RvalueImmTy Prov) : RvalueM S (Memory.Scalar Prov) :=
  liftResult (value.imm.toScalar.mapError immediateError)

private def toInteger [PointerProvenance Prov] (value : RvalueImmTy Prov)
    (kind : IntegerKind) : RvalueM S IntegerValue := do
  let scalar ← toScalar value
  let scalar ← liftResult (scalar.toScalarInt.mapError scalarError)
  -- ImmTy::to_scalar_int checks the scalar's size against its typed layout.
  let _ ← liftResult (scalar.toBits value.layout.layout.size |>.mapError scalarIntError)
  return ⟨scalar, ⟨value.layout.layout.size, kind⟩⟩

private def finish (h : ScalarOpsHooks Prov S C) (choice : C)
    (input : TyAndLayout MIR.TyId) : IntegerResult → RvalueM S (RvalueImmTy Prov)
  | .scalar value => pure ⟨.scalar (.fromScalarInt value), input⟩
  | .withOverflow value overflow => do
    let layout ← h.overflowLayout choice input
    return ⟨.scalarPair (.fromScalarInt value) (.fromBool overflow), layout⟩
  | .boolean value => do
    let layout ← h.boolLayout choice
    return ⟨.scalar (.fromBool value), layout⟩
  | .ordering value => do
    let layout ← h.orderingLayout choice
    let integer : Int := match value with | .lt => -1 | .eq => 0 | .gt => 1
    let scalar ← liftResult (Memory.Scalar.fromInt integer (Size.ofBytes 1) |>.mapError scalarError)
    return ⟨.scalar scalar, layout⟩

private def assertSameType (left right : RvalueImmTy Prov) : RvalueM S Unit :=
  if left.layout.ty == right.layout.ty then pure ()
  else throw (.invalidProgram "asymmetric scalar operand types")

private def isShift (op : BinOp) : Bool :=
  op == .Shl || op == .ShlUnchecked || op == .Shr || op == .ShrUnchecked

/-- Match on the compiler-owned left type; differing type IDs remain distinct
when their ABI sizes or scalar representations happen to agree. -/
def binary [PointerProvenance Prov] (h : ScalarOpsHooks Prov S C) (choice : C)
    (op : BinOp) (left right : RvalueImmTy Prov) : RvalueM S (RvalueImmTy Prov) := do
  match ← h.classify choice left.layout.ty with
  | .character =>
    assertSameType left right
    let l ← toScalar left
    let r ← toScalar right
    let l ← liftResult (l.toChar.mapError scalarError)
    let r ← liftResult (r.toChar.mapError scalarError)
    let result ← liftResult (IntegerOps.binaryChar op l r |>.mapError integerError)
    finish h choice left.layout result
  | .boolean =>
    assertSameType left right
    let l ← toScalar left
    let r ← toScalar right
    let l ← liftResult (l.toBool.mapError scalarError)
    let r ← liftResult (r.toBool.mapError scalarError)
    let result ← liftResult (IntegerOps.binaryBool op l r |>.mapError integerError)
    finish h choice left.layout result
  | .floating =>
    assertSameType left right
    h.floatBinary choice op left right
  | .integer kind =>
    let .integer rightKind ← h.classify choice right.layout.ty
      | throw (.invalidProgram "integer binary RHS is not integral")
    let l ← toInteger left kind
    let r ← toInteger right rightKind
    if !isShift op then assertSameType left right
    let result ← liftResult (IntegerOps.binary op l r |>.mapError integerError)
    finish h choice left.layout result
  | .pointer | .functionPointer =>
    let rhs ← h.classify choice right.layout.ty
    match rhs with
    | .pointer | .functionPointer | .integer _ => h.pointerBinary choice op left right
    | _ => throw (.invalidProgram "pointer binary RHS is neither pointer nor integer")

def unary [PointerProvenance Prov] (h : ScalarOpsHooks Prov S C) (choice : C)
    (op : UnOp) (value : RvalueImmTy Prov) : RvalueM S (RvalueImmTy Prov) := do
  match ← h.classify choice value.layout.ty with
  | .boolean =>
    let scalar ← toScalar value
    let b ← liftResult (scalar.toBool.mapError scalarError)
    if op != .Not then throw (.invalidProgram "invalid boolean unary operation")
    finish h choice value.layout (.boolean (!b))
  | .integer kind =>
    let integer ← toInteger value kind
    let scalar ← liftResult (IntegerOps.unary op integer |>.mapError integerError)
    return ⟨.scalar (.fromScalarInt scalar), value.layout⟩
  | .floating =>
    let _ ← toScalar value
    if op != .Neg then throw (.invalidProgram "invalid float unary operation")
    h.floatUnary choice op value
  | .pointer =>
    if op != .PtrMetadata then throw (.invalidProgram "invalid pointer unary operation")
    h.derefValidity choice value
    let (_, metadata) ← liftResult (value.imm.toScalarAndMeta |>.mapError immediateError)
    match metadata with
    | .metadata scalar =>
      let layout ← h.metadataLayout choice value.layout.ty
      return ⟨.scalar scalar, layout⟩
    | .none =>
      let layout ← h.unitLayout choice
      return ⟨.uninit, layout⟩
  | .character => throw (.invalidProgram "invalid character unary operation")
  | .functionPointer => throw (.invalidProgram "invalid function-pointer unary operation")

end ScalarOps
end Miri.Interpreter
