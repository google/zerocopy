import Miri.Interpreter.ScalarOps
import Miri.Interpreter.FloatOps
import Miri.Interpreter.PlaceMachine

/-! Compiler-only scalar leaves and the integer subpath used by source pointer
arithmetic. No placeholder float/pointer/dereference callbacks are constructed
merely to run an integer operation. The scalar-size/type/overflow checks are
identical to ScalarOps.binary's integer arm. -/
namespace Miri.Interpreter.ExecutionScalar
open Miri.ABI Miri.Memory Miri.MIR
structure Leaves (S C : Type) where
  classify : C → TyId → RvalueM S ScalarTypeClass
  boolLayout : C → RvalueM S LocalLayout
  orderingLayout : C → RvalueM S LocalLayout
  overflowLayout : C → LocalLayout → RvalueM S LocalLayout
  metadataLayout : C → TyId → RvalueM S LocalLayout
  unitLayout : C → RvalueM S LocalLayout

def Leaves.ofHooks (h : ScalarOpsHooks P S C) : Leaves S C :=
  ⟨h.classify,h.boolLayout,h.orderingLayout,h.overflowLayout,h.metadataLayout,h.unitLayout⟩
private def lift (value : Except StepError A) : RvalueM S A :=
  match value with | .ok value => pure value | .error error => throw error
private def integer [PointerProvenance P] (value : RvalueImmTy P) (kind : IntegerKind) :
    RvalueM S IntegerValue := do
  let scalar ← lift (value.imm.toScalar.mapError ScalarOps.immediateError)
  let scalar ← lift (scalar.toScalarInt.mapError ScalarOps.scalarError)
  let _ ← lift (scalar.toBits value.layout.layout.size |>.mapError ScalarOps.scalarIntError)
  return ⟨scalar,⟨value.layout.layout.size,kind⟩⟩

def finish (h : Leaves S C) (choice : C) (input : LocalLayout) :
    IntegerResult → RvalueM S (RvalueImmTy P)
  | .scalar value => pure ⟨.scalar (.fromScalarInt value),input⟩
  | .withOverflow value overflow => do
    let layout ← h.overflowLayout choice input
    return ⟨.scalarPair (.fromScalarInt value) (.fromBool overflow),layout⟩
  | .boolean value => do return ⟨.scalar (.fromBool value),← h.boolLayout choice⟩
  | .ordering value => do
    let layout ← h.orderingLayout choice
    let integer : Int := match value with | .lt => -1 | .eq => 0 | .gt => 1
    let scalar ← lift (Memory.Scalar.fromInt integer (Size.ofBytes 1) |>.mapError ScalarOps.scalarError)
    return ⟨.scalar scalar,layout⟩

def integerBinary [PointerProvenance P] (h : Leaves S C) (choice : C)
    (op : BinOp) (left right : RvalueImmTy P) : RvalueM S (RvalueImmTy P) := do
  let .integer kind ← h.classify choice left.layout.ty
    | throw (.invalidProgram "pointer arithmetic integer subpath has non-integral LHS")
  let .integer rightKind ← h.classify choice right.layout.ty
    | throw (.invalidProgram "integer binary RHS is not integral")
  let leftValue ← integer left kind
  let rightValue ← integer right rightKind
  unless op == .Shl || op == .ShlUnchecked || op == .Shr || op == .ShrUnchecked do
    unless left.layout.ty == right.layout.ty do throw (.invalidProgram "asymmetric scalar operand types")
  let result ← lift (IntegerOps.binary op leftValue rightValue |>.mapError ScalarOps.integerError)
  finish h choice left.layout result

private def scalar (value : RvalueImmTy P) : RvalueM S (Memory.Scalar P) :=
  lift (value.imm.toScalar.mapError ScalarOps.immediateError)

/-- Pinned Miri machine pointer comparison/atomic arithmetic fallback. Only
actual result-layout and integer actions are required, not a full scalar record. -/
def pointerBinary [PointerProvenance P] (target : TargetDataLayout)
    (queries : Leaves S C) (isRaw : C → TyId → RvalueM S Bool)
    (usizeLayout : C → RvalueM S LocalLayout) (choice : C)
    (op : BinOp) (left right : RvalueImmTy P) : RvalueM S (RvalueImmTy P) := do
  let size := Size.fromBits target.pointerWidth.bits
  match op with
  | .Eq | .Ne | .Lt | .Le | .Gt | .Ge =>
    unless left.layout.layout.backendRepr == right.layout.layout.backendRepr do
      throw (.invalidProgram "pointer comparison backend mismatch")
    let pair := fun (value : RvalueImmTy P) => do
      match value.imm with
      | .scalar a => pure ((← lift (a.toBits size |>.mapError ScalarOps.scalarError)),(0 : U128))
      | .scalarPair a b =>
        let a ← lift (a.toBits size |>.mapError ScalarOps.scalarError)
        let b ← lift (b.toBits size |>.mapError ScalarOps.scalarError)
        pure (a,b)
      | .uninit => throw (.invalidProgram "uninitialized pointer comparison immediate")
    let left ← pair left
    let right ← pair right
    let order := if left.1 == right.1 then compare left.2.toNat right.2.toNat else compare left.1.toNat right.1.toNat
    let result := match op with
      | .Eq => order == .eq | .Ne => order != .eq | .Lt => order == .lt
      | .Le => order != .gt | .Gt => order == .gt | .Ge => order != .lt | _ => false
    return ⟨.scalar (.fromBool result),← queries.boolLayout choice⟩
  | .Add | .Sub | .BitOr | .BitAnd | .BitXor =>
    unless ← isRaw choice left.layout.ty do throw (.invalidProgram "atomic pointer arithmetic requires raw pointer")
    let layout ← usizeLayout choice
    unless right.layout.ty == layout.ty do throw (.invalidProgram "atomic pointer arithmetic RHS must be usize")
    let ptr ← lift ((← scalar left).toPointer target |>.mapError ScalarOps.scalarError)
    unless PointerProvenance.offsetIsAddr (Prov := P) do
      throw (.unsupported "Miri atomic pointer arithmetic requires address provenance")
    let address ← lift (Memory.Scalar.fromUInt (BitVec.ofNat 128 ptr.offset.bytes.toNat) layout.layout.size |>.mapError ScalarOps.scalarError)
    let result ← integerBinary queries choice op ⟨.scalar address,layout⟩ right
    let address ← lift ((← scalar result).toTargetUsize size |>.mapError ScalarOps.scalarError)
    let ptr := {ptr with offset := Size.ofBytes address}
    let value ← lift (Memory.Scalar.fromMaybePointer target ptr |>.mapError ScalarOps.scalarError)
    return ⟨.scalar value,layout⟩
  | _ => throw (.invalidProgram "unsupported Miri pointer binary operation")

private def machineAction (action : PlaceMachine.MachineM K U A) : MachineHooks.M K U A := fun state =>
  match action state.machine with
  | .ok value machine => .ok value {state with machine}
  | .error error machine => .error error {state with machine}

/-- Full scalar dictionary constructed without overwritten input callbacks.
Pointer offsets retain compiler layout→multiply/overflow→signed conversion→
allocation bounds→wrapping-address order; dereference uses the actual source
operand driver supplied by the physical factory. -/
def hooks (queries : Leaves (MachineHooks.State K U) C)
    (access : PlaceMachine.AccessConfig K U) (arithmetic : PointerArithmetic)
    (isRaw : C → TyId → MachineHooks.M K U Bool)
    (usizeLayout : C → MachineHooks.M K U LocalLayout)
    (pointeeLayout : C → TyId → MachineHooks.M K U LocalLayout)
    (dereference : C → OpTy Provenance → MachineHooks.M K U (MPlaceTy Provenance))
    (floats : FloatOpsHooks Provenance (MachineHooks.State K U) C) :
    ScalarOpsHooks Provenance (MachineHooks.State K U) C where
  classify := queries.classify
  boolLayout := queries.boolLayout
  orderingLayout := queries.orderingLayout
  overflowLayout := queries.overflowLayout
  metadataLayout := queries.metadataLayout
  unitLayout := queries.unitLayout
  floatBinary := FloatOps.binary floats
  floatUnary := FloatOps.unary floats
  derefValidity := fun c value => do
    let _ ← dereference c ⟨.immediate value.imm,value.layout⟩
    pure ()
  pointerBinary := fun c op left right => do
    if op != .Offset then return ← pointerBinary access.runtime.base queries isRaw usizeLayout c op left right
    let pointer ← lift ((← scalar left).toPointer access.runtime.base |>.mapError ScalarOps.scalarError)
    let layout ← pointeeLayout c left.layout.ty
    unless layout.layout.isSized && layout.layout.size.bytes.toNat < 2^63 do
      throw (.invalidProgram "pointer Offset requires sized pointee fitting i64")
    let stride ← lift (Memory.Scalar.fromInt (Int.ofNat layout.layout.size.bytes.toNat) right.layout.layout.size
      |>.mapError ScalarOps.scalarError)
    let multiplied ← integerBinary queries c .MulWithOverflow right ⟨.scalar stride,right.layout⟩
    let (value,overflow) ← lift (multiplied.imm.toScalarPair.mapError ScalarOps.immediateError)
    if ← lift (overflow.toBool.mapError ScalarOps.scalarError) then throw (.undefinedBehavior "PointerArithOverflow")
    let offset ← lift (value.toTargetIsize arithmetic.pointerSize |>.mapError ScalarOps.scalarError)
    let signed ← lift (right.layout.layout.backendRepr.isSigned.mapError fun error => .invalidProgram (reprStr error))
    if !signed && offset.toInt < 0 then throw (.undefinedBehavior "PointerArithOverflow")
    if offset != 0 then
      let memory := (← get).machine.memory
      let resolved ← machineAction (access.resolvePointer memory pointer offset.toInt)
      match checkPtrAccessSigned arithmetic pointer offset .inboundsPointerArithmetic
          (fun _ _ => resolved) memory.getAllocInfo with
      | .ok () => pure ()
      | .error (.allocationLookup (.unavailable id)) => throw (.unsupported s!"missing pointer allocation {id.value}")
      | .error error => throw (.undefinedBehavior (toString error))
    let pointer ← lift (pointer.wrappingSignedOffset offset arithmetic |>.mapError
      fun error => .invalidProgram (reprStr error))
    let result ← lift (Memory.Scalar.fromMaybePointer access.runtime.base pointer |>.mapError ScalarOps.scalarError)
    return ⟨.scalar result,left.layout⟩
end Miri.Interpreter.ExecutionScalar
