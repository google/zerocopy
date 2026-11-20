import Miri.Interpreter.Float
import Miri.Interpreter.ScalarOps

/-! Typed MIR and cast adapters. Canonical compiler type/format/layout queries
remain mandatory; every generated NaN choice is checked against the pinned
Miri candidate relation, rather than trusting a random seed or host float. -/
namespace Miri.Interpreter
open Miri.ABI Miri.Memory Miri.MIR

structure FloatOpsHooks (P S C : Type) where
  integerKindOf : C → MIR.TyId → RvalueM S IntegerKind
  formatOf : C → MIR.TyId → RvalueM S FloatFormat
  boolLayout : C → RvalueM S (TyAndLayout MIR.TyId)
  floatNondeterministic : Bool
  chooseNaN : C → List FloatBits → RvalueM S Nat

namespace FloatOps
private def liftResult (value : Except StepError A) : RvalueM S A :=
  match value with | .ok value => pure value | .error error => throw error
private def engine (value : Except FloatError A) : RvalueM S A :=
  liftResult (value.mapError fun e => .invalidProgram s!"float engine: {repr e}")
private def scalarResult (bits : FloatBits) (layout : TyAndLayout MIR.TyId) : RvalueM S (RvalueImmTy P) := do
  if layout.layout.size != bits.format.size then throw (.invalidProgram "float result layout size mismatch")
  let scalar ← liftResult (Memory.Scalar.fromUInt bits.bits bits.format.size |>.mapError ScalarOps.scalarError)
  return ⟨.scalar scalar, layout⟩

private def readScalarBits [PointerProvenance P] (h : FloatOpsHooks P S C) (choice : C)
    (value : RvalueImmTy P) (scalar : Memory.Scalar P) : RvalueM S FloatBits := do
  let format ← h.formatOf choice value.layout.ty
  if value.layout.layout.size != format.size then throw (.invalidProgram "float operand layout size mismatch")
  let bits ← liftResult (scalar.toBits format.size |>.mapError ScalarOps.scalarError)
  return ⟨format, bits⟩

def readBits [PointerProvenance P] (h : FloatOpsHooks P S C) (choice : C)
    (value : RvalueImmTy P) : RvalueM S FloatBits := do
  let scalar ← liftResult (value.imm.toScalar |>.mapError ScalarOps.immediateError)
  readScalarBits h choice value scalar

def adjustNaN (h : FloatOpsHooks P S C) (choice : C) (value : FloatBits)
    (inputs : List FloatBits) : RvalueM S FloatBits := do
  if !(← engine value.isNaN) then return value
  let candidates ← engine (FloatBits.nanChoices value.format inputs h.floatNondeterministic)
  if !h.floatNondeterministic then return FloatBits.preferredNaN value.format
  let index ← h.chooseNaN choice candidates
  let some result := candidates[index]? | throw (.invalidProgram "invalid floating NaN choice index")
  return result

def binary [PointerProvenance P] (h : FloatOpsHooks P S C) (choice : C)
    (op : BinOp) (left right : RvalueImmTy P) : RvalueM S (RvalueImmTy P) := do
  if left.layout.ty != right.layout.ty then throw (.invalidProgram "asymmetric float operand types")
  -- Source extracts both scalar shapes before converting either float payload.
  let leftScalar ← liftResult (left.imm.toScalar |>.mapError ScalarOps.immediateError)
  let rightScalar ← liftResult (right.imm.toScalar |>.mapError ScalarOps.immediateError)
  let leftBits ← readScalarBits h choice left leftScalar
  let rightBits ← readScalarBits h choice right rightScalar
  match op with
  | .Eq | .Ne | .Lt | .Le | .Gt | .Ge =>
    let result ← engine (leftBits.comparison op rightBits)
    let layout ← h.boolLayout choice
    return ⟨.scalar (.fromBool result), layout⟩
  | .Add | .Sub | .Mul | .Div | .Rem =>
    let result ← engine (leftBits.arithmetic op rightBits)
    let result ← adjustNaN h choice result [leftBits, rightBits]
    scalarResult result left.layout
  | _ => throw (.invalidProgram "invalid floating binary operation")

def unary [PointerProvenance P] (h : FloatOpsHooks P S C) (choice : C)
    (op : UnOp) (value : RvalueImmTy P) : RvalueM S (RvalueImmTy P) := do
  let scalar ← liftResult (value.imm.toScalar |>.mapError ScalarOps.immediateError)
  if op != .Neg then throw (.invalidProgram "invalid floating unary operation")
  let bits ← readScalarBits h choice value scalar
  -- Source negation is a bitwise sign change: no NaN adjustment or quieting.
  scalarResult (← engine bits.negate) value.layout

def castFloatToFloat [PointerProvenance P] (h : FloatOpsHooks P S C) (choice : C)
    (value : RvalueImmTy P) (target : TyAndLayout MIR.TyId) : RvalueM S (RvalueImmTy P) := do
  let bits ← readBits h choice value
  let format ← h.formatOf choice target.ty
  let result ← engine (bits.convert format)
  let result ← adjustNaN h choice result [bits]
  scalarResult result target

def castFloatToInt [PointerProvenance P] (h : FloatOpsHooks P S C) (choice : C)
    (value : RvalueImmTy P) (target : TyAndLayout MIR.TyId) : RvalueM S (RvalueImmTy P) := do
  let bits ← readBits h choice value
  let kind ← h.integerKindOf choice target.ty
  let isSigned := kind.signed
  let width ← liftResult (target.layout.size.bitsNat |>.mapError fun e => .invalidProgram (toString e))
  let integer ← engine (bits.toInteger width isSigned)
  let scalar ← if isSigned then
      liftResult (Memory.Scalar.fromInt integer target.layout.size |>.mapError ScalarOps.scalarError)
    else liftResult (Memory.Scalar.fromUInt (BitVec.ofInt 128 integer) target.layout.size
      |>.mapError ScalarOps.scalarError)
  return ⟨.scalar scalar, target⟩

def castIntToFloat [PointerProvenance P] (h : FloatOpsHooks P S C) (choice : C)
    (value : RvalueImmTy P) (target : TyAndLayout MIR.TyId) : RvalueM S (RvalueImmTy P) := do
  let kind ← h.integerKindOf choice value.layout.ty
  let isSigned := kind.signed
  let scalar ← liftResult (value.imm.toScalar |>.mapError ScalarOps.immediateError)
  let integer ← if isSigned then
      liftResult (scalar.toInt value.layout.layout.size |>.mapError ScalarOps.scalarError)
    else do
      let bits ← liftResult (scalar.toUInt value.layout.layout.size |>.mapError ScalarOps.scalarError)
      pure (Int.ofNat bits.toNat)
  let format ← h.formatOf choice target.ty
  scalarResult (← engine (FloatBits.fromInteger format integer)) target

end FloatOps
end Miri.Interpreter
