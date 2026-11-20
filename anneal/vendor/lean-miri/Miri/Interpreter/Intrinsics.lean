import Miri.Interpreter.OperandPath
import Miri.Interpreter.Cast
import Miri.Interpreter.IntrinsicFloat
import Miri.Interpreter.Discriminant
import Miri.Interpreter.IntrinsicAtomic
import Miri.Interpreter.IntrinsicTypeId
import Miri.Interpreter.IntrinsicVarArgs
import Miri.Interpreter.IntrinsicSimd
import Miri.Interpreter.Math.Dispatch

/-! Source scalar/memory/pointer intrinsic dispatch from pinned core
`interpret/intrinsics.rs` and Miri `intrinsics/{mod,math}.rs`. Unhandled names
return false for source MIR fallback; recognized missing families fail visibly.
No arithmetic branch delegates to a generic name-to-result callback. -/
namespace Miri.Interpreter
open Miri.ABI Miri.Memory Miri.MIR

structure IntrinsicHooks (P S C V : Type) where
  simdHooks : IntrinsicSimdHooks P S C V
  atomicHooks : IntrinsicAtomicHooks P S C V
  typeIdHooks : IntrinsicTypeIdHooks P S C V
  varArgsHooks : IntrinsicVarArgsHooks P S C V
  varArgsFuel : Nat
  target : TargetDataLayout
  /-- Scalar::from_target_usize uses pointer_offset; target-sized reads use pointer_size. -/
  pointerOffset : Size
  maxSizeOfVal : Size
  destLayout : V → TyAndLayout TyId
  layoutOf : C → TyId → RvalueM S (TyAndLayout TyId)
  pointeeType : C → TyId → RvalueM S TyId
  integerKind : C → TyId → RvalueM S IntegerKind
  usizeLayout : C → RvalueM S (TyAndLayout TyId)
  isizeLayout : C → RvalueM S (TyAndLayout TyId)
  readImmediate : C → OpTy P → RvalueM S (RvalueImmTy P)
  evalOperand : C → MIR.Operand → RvalueM S (OpTy P)
  evalOperandAt : C → OperandPath → MIR.Operand → RvalueM S (OpTy P) := fun c _ => evalOperand c
  writeImmediate : C → Immediate P → V → RvalueM S Unit
  writePointer : C → Pointer (Option P) → V → RvalueM S Unit
  copyOp : C → OpTy P → V → RvalueM S Unit
  placeToOp : C → V → RvalueM S (OpTy P)
  placePointer : V → Except StepError (Pointer (Option P))
  derefPointer : C → OpTy P → RvalueM S V
  immPointerToPlace : C → RvalueImmTy P → RvalueM S (OpTy P)
  dynamicSizeAlign : C → OpTy P → RvalueM S (Option (Size × Align))
  scalarOps : ScalarOpsHooks P S C
  floatOps : FloatOpsHooks P S C
  applyFloatNondeterminism : C → RvalueImmTy P → RvalueM S (RvalueImmTy P)
  chooseEqualFloatRight : C → FloatBits → FloatBits → RvalueM S Bool
  fuseMulAdd : C → RvalueM S Bool
  floatFastError : C → RvalueImmTy P → Nat → RvalueM S (RvalueImmTy P)
  checkAlign : C → Pointer (Option P) → Align → RvalueM S Unit
  memCopy : C → Pointer (Option P) → Pointer (Option P) → Size → Bool → RvalueM S Unit
  writeBytes : C → Pointer (Option P) → UInt8 → Size → RvalueM S Unit
  readBytesStripProvenance : C → Pointer (Option P) → Size → RvalueM S (Array UInt8)
  allocateStack : C → TyAndLayout TyId → RvalueM S V
  deallocateStack : C → Pointer (Option P) → RvalueM S Unit
  enforceValidity : C → TyAndLayout TyId → RvalueM S Bool
  enforceValidityRecursively : C → TyAndLayout TyId → RvalueM S Bool
  validatePlace : C → V → Bool → Bool → RvalueM S Unit
  tryAllocId : C → Pointer (Option P) → RvalueM S (Except UInt64 (AllocId × Size))
  checkSignedAccess : C → Pointer (Option P) → Int64 → RvalueM S (Except StepError Unit)
  vtableSizeAlign : C → Pointer (Option P) → Option Nat → RvalueM S (Size × Align)
  readDiscriminant : C → OpTy P → RvalueM S VariantIndex
  discriminantForVariant : C → TyId → VariantIndex → RvalueM S (RvalueImmTy P)
  variantLayout : C → TyAndLayout TyId → Nat → RvalueM S (TyAndLayout TyId)
  ensureMonomorphic : C → TyId → RvalueM S Unit
  typeNameConstant : C → TyId → TyAndLayout TyId → RvalueM S (OpTy P)
  needsDrop : C → TyId → RvalueM S Bool
  variantCount : C → TyId → RvalueM S Nat
  callerLocationConstant : C → TyAndLayout TyId → RvalueM S (OpTy P)
  chooseStaticKnown : C → RvalueM S Bool
  catchUnwind : C → OpTy P → OpTy P → OpTy P → V → Option BasicBlockId → RvalueM S Unit
  returnToBlock : C → Option BasicBlockId → RvalueM S Unit
  /-- Optional source Miri math-family implementation. This is a typed
  capability, not a name/result oracle; ordinary core operations remain in
  their existing branches and the math family is consulted only at the
  unknown-intrinsic fallback point. -/
  mathHooks : Option (Miri.Interpreter.Math.Hooks P S C V) := none

/-- Shared memory operations need no function instance, generic-constant
queries, SIMD/atomic dispatcher, return destination or fallback dictionary. -/
structure MemoryIntrinsicHooks (P S C : Type) where
  target : TargetDataLayout
  maxSizeOfVal : Size
  layoutOf : C → TyId → RvalueM S (TyAndLayout TyId)
  pointeeType : C → TyId → RvalueM S TyId
  readImmediate : C → OpTy P → RvalueM S (RvalueImmTy P)
  checkAlign : C → Pointer (Option P) → Align → RvalueM S Unit
  memCopy : C → Pointer (Option P) → Pointer (Option P) → Size → Bool → RvalueM S Unit

def IntrinsicHooks.memory (h : IntrinsicHooks P S C V) : MemoryIntrinsicHooks P S C :=
  ⟨h.target,h.maxSizeOfVal,h.layoutOf,h.pointeeType,h.readImmediate,h.checkAlign,h.memCopy⟩

namespace Intrinsics
private def invalid (message : String) : RvalueM S A := throw (.invalidProgram message)
private def ub (message : String) : RvalueM S A := throw (.undefinedBehavior message)
private def liftResult (result : Except StepError A) : RvalueM S A :=
  match result with | .ok result => pure result | .error error => throw error
private def arg (args : Array (OpTy P)) (index : Nat) : RvalueM S (OpTy P) :=
  match args[index]? with | some value => pure value | none => invalid "intrinsic argument count mismatch"
private def typeArg (args : Array TyId) : RvalueM S TyId :=
  match args[0]? with | some value => pure value | none => invalid "intrinsic requires type argument"
private def arity (args : Array (OpTy P)) (count : Nat) : RvalueM S Unit :=
  if args.size == count then pure () else ub "intrinsic argument count mismatch"
/-- Core volatile arms use span_bug!, unlike Miri check_intrinsic_arg_count. -/
private def coreArity (args : Array (OpTy P)) (count : Nat) : RvalueM S Unit :=
  if args.size == count then pure () else invalid "invalid core volatile intrinsic call"
private def scalar [PointerProvenance P] (h : IntrinsicHooks P S C V) (choice : C) (value : OpTy P) : RvalueM S (Memory.Scalar P) := do
  let immediate ← h.readImmediate choice value
  liftResult (immediate.imm.toScalar |>.mapError ScalarOps.immediateError)
private def pointer [PointerProvenance P] (h : IntrinsicHooks P S C V) (choice : C) (value : OpTy P) : RvalueM S (Pointer (Option P)) := do
  let scalar ← scalar h choice value
  liftResult (scalar.toPointer h.target |>.mapError ScalarOps.scalarError)
private def usize [PointerProvenance P] (h : IntrinsicHooks P S C V) (choice : C) (value : OpTy P) : RvalueM S UInt64 := do
  let scalar ← scalar h choice value
  liftResult (scalar.toTargetUsize (Size.fromBits h.target.pointerWidth.bits) |>.mapError ScalarOps.scalarError)
private def isize [PointerProvenance P] (h : IntrinsicHooks P S C V) (choice : C) (value : OpTy P) : RvalueM S Int64 := do
  let scalar ← scalar h choice value
  liftResult (scalar.toTargetIsize (Size.fromBits h.target.pointerWidth.bits) |>.mapError ScalarOps.scalarError)
private def writeScalar (h : IntrinsicHooks P S C V) (choice : C) (value : Memory.Scalar P) (dest : V) :=
  h.writeImmediate choice (.scalar value) dest
private def writeUsize (h : IntrinsicHooks P S C V) (choice : C) (value : UInt64) (dest : V) : RvalueM S Unit := do
  let scalar ← liftResult (Memory.Scalar.fromUInt (BitVec.ofNat 128 value.toNat)
    h.pointerOffset |>.mapError ScalarOps.scalarError)
  writeScalar h choice scalar dest
private def integerValue [PointerProvenance P] (h : IntrinsicHooks P S C V) (choice : C)
    (value : RvalueImmTy P) : RvalueM S IntegerValue := do
  let kind ← h.integerKind choice value.layout.ty
  let scalar ← liftResult (value.imm.toScalarInt |>.mapError ScalarOps.immediateError)
  pure ⟨scalar, ⟨value.layout.layout.size, kind⟩⟩
private def integerArithmeticError : IntegerArithmeticIntrinsicError → StepError
  | .integerOperation error => ScalarOps.integerError error
  | .scalar error => ScalarOps.scalarIntError error
  | .exactDivisionHasRemainder _ => .undefinedBehavior "exact_div has nonzero remainder"
  | error => .invalidProgram s!"{repr error}"
private def numericName : String → Option IntegerIntrinsic
  | "ctpop" => some .ctpop | "cttz" => some .cttz | "cttz_nonzero" => some .cttzNonzero
  | "ctlz" => some .ctlz | "ctlz_nonzero" => some .ctlzNonzero
  | "bswap" => some .bswap | "bitreverse" => some .bitreverse | _ => none

/-- Source count read precedes pointee layout and multiplication; pointer reads
and alignment checks follow, including for zero-length copies. -/
def copyWith [PointerProvenance P] (h : MemoryIntrinsicHooks P S C) (choice : C)
    (source dest count : OpTy P) (nonoverlapping : Bool) : RvalueM S Unit := do
  let read := fun operand => do
    let value ← h.readImmediate choice operand
    liftResult (value.imm.toScalar |>.mapError ScalarOps.immediateError)
  let count ← liftResult ((← read count).toTargetUsize (Size.fromBits h.target.pointerWidth.bits) |>.mapError ScalarOps.scalarError)
  let ty ← h.pointeeType choice source.layout.ty
  let layout ← h.layoutOf choice ty
  let some size := IntegerOps.computeSizeInBytes layout.layout.size count h.maxSizeOfVal
    | ub "overflow computing total size of copy"
  let source ← liftResult ((← read source).toPointer h.target |>.mapError ScalarOps.scalarError)
  let dest ← liftResult ((← read dest).toPointer h.target |>.mapError ScalarOps.scalarError)
  h.checkAlign choice source layout.layout.align.abi
  h.checkAlign choice dest layout.layout.align.abi
  h.memCopy choice source dest size nonoverlapping

def copy [PointerProvenance P] (h : IntrinsicHooks P S C V) (choice : C)
    (source dest count : OpTy P) (nonoverlapping : Bool) : RvalueM S Unit :=
  copyWith h.memory choice source dest count nonoverlapping

def writeBytes [PointerProvenance P] (h : IntrinsicHooks P S C V) (choice : C)
    (dest byte count : OpTy P) : RvalueM S Unit := do
  let ty ← h.pointeeType choice dest.layout.ty
  let layout ← h.layoutOf choice ty
  let dest ← pointer h choice dest
  let byte ← liftResult ((← scalar h choice byte).toUInt8 |>.mapError ScalarOps.scalarError)
  let count ← usize h choice count
  let some size := IntegerOps.computeSizeInBytes layout.layout.size count h.maxSizeOfVal
    | ub "overflow computing total size of write_bytes"
  h.writeBytes choice dest byte size

private def bytesCompare : List UInt8 → List UInt8 → Ordering
  | [], [] => .eq | [], _ :: _ => .lt | _ :: _, [] => .gt
  | a :: as, b :: bs => if a == b then bytesCompare as bs else compare a b

def compareBytes [PointerProvenance P] (h : IntrinsicHooks P S C V) (choice : C)
    (left right count : OpTy P) : RvalueM S (Memory.Scalar P) := do
  let left ← pointer h choice left
  let right ← pointer h choice right
  let count := Size.ofBytes (← usize h choice count)
  let left ← h.readBytesStripProvenance choice left count
  let right ← h.readBytesStripProvenance choice right count
  let result : Int32 := match bytesCompare left.toList right.toList with | .lt => -1 | .eq => 0 | .gt => 1
  pure (.fromScalarInt (.ofInt32 result))

def rawEq [PointerProvenance P] (h : IntrinsicHooks P S C V) (choice : C) (left right : OpTy P) : RvalueM S Bool := do
  let layout ← h.layoutOf choice (← h.pointeeType choice left.layout.ty)
  if !layout.layout.isSized then invalid "raw_eq requires sized pointee"
  let read := fun (op : OpTy P) => do
    let ptr ← pointer h choice op
    h.checkAlign choice ptr layout.layout.align.abi
    h.readBytesStripProvenance choice ptr layout.layout.size
  let left ← read left
  let right ← read right
  pure (left == right)

def typedSwap [PointerProvenance P] (h : IntrinsicHooks P S C V) (choice : C) (left right : OpTy P) : RvalueM S Unit := do
  let left ← h.derefPointer choice left
  let right ← h.derefPointer choice right
  let layout := h.destLayout left
  if layout != h.destLayout right || !layout.layout.isSized then invalid "typed swap layout mismatch or unsized type"
  let temp ← h.allocateStack choice layout
  h.copyOp choice (← h.placeToOp choice left) temp
  let rightPtr ← liftResult (h.placePointer right)
  let leftPtr ← liftResult (h.placePointer left)
  h.memCopy choice rightPtr leftPtr layout.layout.size true
  if ← h.enforceValidity choice layout then
    let recursive ← h.enforceValidityRecursively choice layout
    h.validatePlace choice left recursive true
  h.copyOp choice (← h.placeToOp choice temp) right
  h.deallocateStack choice (← liftResult (h.placePointer temp))

/-- Core ptr_offset_from computes addresses only for address provenance, or
common-allocation offsets otherwise; both directed ranges must be valid. -/
def pointerOffsetFrom [PointerProvenance P] (h : IntrinsicHooks P S C V) (choice : C)
    (a b : OpTy P) (pointee : TyId) (unsigned : Bool) (dest : V) : RvalueM S Unit := do
  let a ← pointer h choice a
  let b ← pointer h choice b
  let unsignedLayout ← h.usizeLayout choice
  let signedLayout ← h.isizeLayout choice
  let (aOffset, bOffset) ← if PointerProvenance.offsetIsAddr (Prov := P) then pure (a.offset.bytes, b.offset.bytes)
    else do
      let a ← h.tryAllocId choice a
      let b ← h.tryAllocId choice b
      match a, b with
      | .error a, .error b => pure (a, b)
      | .ok (aId, a), .ok (bId, b) =>
        if aId != bId then ub "ptr_offset_from pointers do not share allocation"
        pure (a.bytes, b.bytes)
      | _, _ => ub "ptr_offset_from pointers do not share allocation"
  let makeOffset := fun (offset : UInt64) => do
    let scalar ← liftResult (Memory.Scalar.fromUInt (Prov := P) (BitVec.ofNat 128 offset.toNat)
      unsignedLayout.layout.size |>.mapError ScalarOps.scalarError)
    pure (RvalueImmTy.mk (.scalar scalar) unsignedLayout)
  let aValue ← makeOffset aOffset
  let bValue ← makeOffset bOffset
  let result ← ScalarOps.binary h.scalarOps choice .SubWithOverflow aValue bValue
  let (value, overflow) ← liftResult (result.imm.toScalarPair |>.mapError ScalarOps.immediateError)
  let overflow ← liftResult (overflow.toBool |>.mapError ScalarOps.scalarError)
  let distance ← liftResult (value.toTargetIsize (Size.fromBits h.target.pointerWidth.bits)
    |>.mapError ScalarOps.scalarError)
  let distance := distance.toInt
  if overflow then
    if unsigned then ub "ptr_offset_from_unsigned has negative distance"
    let minimum : Int := -(2^(h.target.pointerWidth.bits.toNat-1))
    if distance >= 0 || distance == minimum then ub "ptr_offset_from first pointer too far before second"
  else if distance < 0 then ub "ptr_offset_from first pointer too far ahead of second"
  match ← h.checkSignedAccess choice b (Int64.ofInt distance) with
  | .ok _ => pure ()
  | .error _ =>
    let aId ← h.tryAllocId choice a
    let bId ← h.tryAllocId choice b
    match aId, bId with
    | .ok (aId, _), .ok (bId, _) =>
      if aId == bId then ub "ptr_offset_from range is not in-bounds"
      else ub "ptr_offset_from pointers do not share allocation"
    | _, _ => ub "ptr_offset_from pointers do not share allocation"
  match ← h.checkSignedAccess choice a (Int64.ofInt (-distance)) with
  | .ok _ => pure ()
  | .error _ => ub "ptr_offset_from pointers do not share allocation"
  let ret := if unsigned then unsignedLayout else signedLayout
  let layout ← h.layoutOf choice pointee
  let kind ← h.integerKind choice ret.ty
  let make := fun (n : Int) => do
    let scalar ← liftResult (Memory.Scalar.fromInt (Prov := P) n ret.layout.size |>.mapError ScalarOps.scalarError)
    liftResult (scalar.toScalarInt |>.mapError ScalarOps.scalarError)
  let a ← make distance
  let b ← make (Int.ofNat layout.layout.size.bytes.toNat)
  let value ← liftResult (IntegerArithmeticIntrinsic.exactDiv ⟨a, ⟨ret.layout.size, kind⟩⟩
    ⟨b, ⟨ret.layout.size, kind⟩⟩ |>.mapError integerArithmeticError)
  writeScalar h choice (.fromScalarInt value) dest

private def floatEngine (result : Except FloatError A) : RvalueM S A :=
  liftResult (result.mapError fun e => .invalidProgram s!"{repr e}")
private def floatName (name : String) : Option (String × FloatFormat) :=
  ([("f16", FloatFormat.binary16), ("f32", .binary32), ("f64", .binary64), ("f128", .binary128)]).findSome? fun (suffix, format) =>
    if name.endsWith suffix then some ((name.dropEnd suffix.length).toString, format) else none
private def floatValue [PointerProvenance P] (h : IntrinsicHooks P S C V) (choice : C) (op : OpTy P) (format : FloatFormat) : RvalueM S FloatBits := do
  let scalar ← scalar h choice op
  let bits ← liftResult (scalar.toBits format.size |>.mapError ScalarOps.scalarError)
  pure ⟨format, bits⟩
private def writeFloat (h : IntrinsicHooks P S C V) (choice : C) (value : FloatBits) (dest : V) : RvalueM S Unit := do
  let scalar ← liftResult (Memory.Scalar.fromUInt value.bits value.format.size |>.mapError ScalarOps.scalarError)
  writeScalar h choice scalar dest

/-- Portable suffixed float intrinsic families, including genuinely fused FMA.
Only the machine's choice of fusion/equal operand/NaN remains effectful. -/
def floatIntrinsic [PointerProvenance P] (h : IntrinsicHooks P S C V) (choice : C)
    (name : String) (args : Array (OpTy P)) (dest : V) : RvalueM S Bool := do
  let some (base, format) := floatName name | return false
  match base with
  | "floor" | "ceil" | "trunc" | "round" | "round_ties_even_" =>
    let value ← floatValue h choice (← arg args 0) format
    let mode := match base with
      | "floor" => FloatIntegralRound.floor | "ceil" => .ceil | "trunc" => .trunc
      | "round" => .away | _ => .even
    let result ← floatEngine (IntrinsicFloat.roundIntegral value mode)
    writeFloat h choice (← FloatOps.adjustNaN h.floatOps choice result [value]) dest
  | "copysign" =>
    let a ← floatValue h choice (← arg args 0) format
    let b ← floatValue h choice (← arg args 1) format
    writeFloat h choice (← floatEngine (IntrinsicFloat.copySign a b)) dest
  | "minimum" | "maximum" | "minimum_number_nsz_" | "maximum_number_nsz_" =>
    let a ← floatValue h choice (← arg args 0) format
    let b ← floatValue h choice (← arg args 1) format
    let op := match base with
      | "minimum" => FloatMinMax.minimum | "maximum" => .maximum
      | "minimum_number_nsz_" => .minimumNumber | _ => .maximumNumber
    let number := op == .minimumNumber || op == .maximumNumber
    let equal ← floatEngine (a.comparison .Eq b)
    let choose ← if number && equal then h.chooseEqualFloatRight choice a b else pure false
    let result ← floatEngine (IntrinsicFloat.minMax a b op choose)
    let result ← if number && equal then pure result else FloatOps.adjustNaN h.floatOps choice result [a,b]
    writeFloat h choice result dest
  | "fma" | "fmuladd" =>
    let a ← floatValue h choice (← arg args 0) format
    let b ← floatValue h choice (← arg args 1) format
    let c ← floatValue h choice (← arg args 2) format
    let fuse ← if base == "fma" then pure true else h.fuseMulAdd choice
    let result ← if fuse then floatEngine (IntrinsicFloat.fusedMulAdd a b c)
      else do
        let product ← floatEngine (a.arithmetic .Mul b)
        floatEngine (product.arithmetic .Add c)
    writeFloat h choice (← FloatOps.adjustNaN h.floatOps choice result [a,b,c]) dest
  | _ => return false
  return true

/-- Source handled-result distinction: false permits the compiler's intrinsic
MIR fallback. This never manufactures a successful result for an unknown name. -/
def eval [PointerProvenance P] (h : IntrinsicHooks P S C V) (choice : C) (name : String)
    (types : Array TyId) (args : Array (OpTy P)) (dest : V) (ret : Option BasicBlockId) : RvalueM S Bool := do
  if name.startsWith "atomic_" then return (← IntrinsicAtomic.eval h.atomicHooks choice name args dest ret)
  if name.startsWith "simd_" then return (← IntrinsicSimd.eval h.simdHooks choice name args dest ret)
  if let some numeric := numericName name then
    let layout ← h.layoutOf choice (← typeArg types)
    let value ← scalar h choice (← arg args 0)
    let kind ← h.integerKind choice layout.ty
    let retKind ← h.integerKind choice (h.destLayout dest).ty
    let scalar ← liftResult (value.toScalarInt |>.mapError ScalarOps.scalarError)
    let _ ← liftResult (scalar.toBits layout.layout.size |>.mapError ScalarOps.scalarIntError)
    if (numeric == .bswap || numeric == .bitreverse) && layout != h.destLayout dest then invalid "numeric intrinsic layout mismatch"
    let result ← liftResult (IntegerIntrinsic.run numeric scalar ⟨layout.layout.size, kind⟩
      ⟨(h.destLayout dest).layout.size, retKind⟩ |>.mapError fun e => match e with
        | .scalar e => ScalarOps.scalarIntError e
        | .undefinedBehaviorOnZero _ => .undefinedBehavior "nonzero count intrinsic called on zero"
        | .layoutMismatch _ _ => .invalidProgram "numeric intrinsic layout mismatch")
    writeScalar h choice (.fromScalarInt result) dest
    h.returnToBlock choice ret
    return true
  match name with
  | "size_of" | "align_of" =>
    let layout ← h.layoutOf choice (← typeArg types)
    if !layout.layout.isSized then invalid "size_of/align_of requires sized type"
    let value ← if name == "size_of" then pure layout.layout.size.bytes
      else liftResult (layout.layout.align.abi.bytes |>.mapError fun e => .invalidProgram (toString e))
    writeUsize h choice value dest
  | "offset_of" =>
    let variant ← liftResult ((← scalar h choice (← arg args 0)).toUInt32 |>.mapError ScalarOps.scalarError)
    let field ← liftResult ((← scalar h choice (← arg args 1)).toUInt32 |>.mapError ScalarOps.scalarError)
    let layout ← h.layoutOf choice (← typeArg types)
    let layout ← h.variantLayout choice layout variant.toNat
    let offset ← liftResult (layout.layout.fields.offset field.toNat |>.mapError fun e => .invalidProgram s!"{repr e}")
    writeUsize h choice offset.bytes dest
  | "variant_count" => writeUsize h choice (UInt64.ofNat (← h.variantCount choice (← typeArg types))) dest
  | "type_name" =>
    let ty ← typeArg types
    h.ensureMonomorphic choice ty
    h.copyOp choice (← h.typeNameConstant choice ty (h.destLayout dest)) dest
  | "needs_drop" =>
    let ty ← typeArg types
    h.ensureMonomorphic choice ty
    writeScalar h choice (.fromBool (← h.needsDrop choice ty)) dest
  | "type_id" =>
    let ty ← typeArg types
    h.ensureMonomorphic choice ty
    IntrinsicTypeId.write h.typeIdHooks choice ty dest
  | "type_id_eq" =>
    let a ← IntrinsicTypeId.read h.typeIdHooks choice (← arg args 0)
    let b ← IntrinsicTypeId.read h.typeIdHooks choice (← arg args 1)
    writeScalar h choice (.fromBool (a == b)) dest
  | "caller_location" => h.copyOp choice (← h.callerLocationConstant choice (h.destLayout dest)) dest
  | "align_of_val" | "size_of_val" =>
    let place ← h.immPointerToPlace choice (← h.readImmediate choice (← arg args 0))
    let some (size, align) ← h.dynamicSizeAlign choice place | throw (.unsupported "extern type does not have known layout")
    let value ← if name == "size_of_val" then pure size.bytes
      else liftResult (align.bytes |>.mapError fun e => .invalidProgram (toString e))
    writeUsize h choice value dest
  | "saturating_add" | "saturating_sub" | "exact_div" =>
    let left ← h.readImmediate choice (← arg args 0)
    let right ← h.readImmediate choice (← arg args 1)
    if left.layout.ty != right.layout.ty then invalid "integer intrinsic operand types differ"
    let _ ← h.integerKind choice left.layout.ty
    if name == "exact_div" then
      let rem ← ScalarOps.binary h.scalarOps choice .Rem left right
      let rem ← liftResult (rem.imm.toScalar |>.mapError ScalarOps.immediateError)
      let rem ← liftResult (rem.toBits left.layout.layout.size |>.mapError ScalarOps.scalarError)
      if rem != 0 then ub "exact_div has nonzero remainder"
      let result ← ScalarOps.binary h.scalarOps choice .Div left right
      h.writeImmediate choice result.imm dest
    else
      -- Keep the canonical overflowing result-layout query performed by binary_op.
      let result ← ScalarOps.binary h.scalarOps choice
        (if name == "saturating_add" then .AddWithOverflow else .SubWithOverflow) left right
      let (value, overflow) ← liftResult (result.imm.toScalarPair |>.mapError ScalarOps.immediateError)
      let overflow ← liftResult (overflow.toBool |>.mapError ScalarOps.scalarError)
      let value ← if !overflow then pure value else do
        let signed ← match left.layout.layout.backendRepr.isSigned with
          | .ok value => pure value | .error _ => invalid "saturating arithmetic needs scalar ABI"
        if signed then
          let first ← liftResult (left.imm.toScalar |>.mapError ScalarOps.immediateError)
          let first ← liftResult (first.toInt left.layout.layout.size |>.mapError ScalarOps.scalarError)
          let bound ← liftResult ((if first >= 0 then left.layout.layout.size.signedIntMax
            else left.layout.layout.size.signedIntMin) |>.mapError fun e => .invalidProgram (toString e))
          liftResult (Memory.Scalar.fromInt bound left.layout.layout.size |>.mapError ScalarOps.scalarError)
        else
          let bound ← if name == "saturating_add" then
              liftResult (left.layout.layout.size.unsignedIntMax |>.mapError fun e => .invalidProgram (toString e))
            else pure 0
          liftResult (Memory.Scalar.fromUInt bound left.layout.layout.size |>.mapError ScalarOps.scalarError)
      writeScalar h choice value dest
  | "copy" => copy h choice (← arg args 0) (← arg args 1) (← arg args 2) false
  | "write_bytes" | "volatile_set_memory" =>
    if name == "volatile_set_memory" then coreArity args 3
    writeBytes h choice (← arg args 0) (← arg args 1) (← arg args 2)
  | "compare_bytes" => writeScalar h choice (← compareBytes h choice (← arg args 0) (← arg args 1) (← arg args 2)) dest
  | "raw_eq" => writeScalar h choice (.fromBool (← rawEq h choice (← arg args 0) (← arg args 1))) dest
  | "typed_swap_nonoverlapping" => typedSwap h choice (← arg args 0) (← arg args 1)
  | "arith_offset" =>
    let ptr ← pointer h choice (← arg args 0)
    let count ← isize h choice (← arg args 1)
    let layout ← h.layoutOf choice (← typeArg types)
    if layout.layout.size.bytes.toNat >= 2^63 then invalid "pointee size exceeds i64"
    let offset := Int64.ofInt (count.toInt * Int.ofNat layout.layout.size.bytes.toNat)
    let result ← liftResult (ptr.wrappingSignedOffset offset ⟨Size.fromBits h.target.pointerWidth.bits⟩
      |>.mapError fun e => .invalidProgram s!"{repr e}")
    h.writePointer choice result dest
  | "ptr_offset_from" | "ptr_offset_from_unsigned" =>
    pointerOffsetFrom h choice (← arg args 0) (← arg args 1) (← typeArg types) (name == "ptr_offset_from_unsigned") dest
  | "black_box" => h.copyOp choice (← arg args 0) dest
  | "volatile_load" =>
    coreArity args 1
    let place ← h.derefPointer choice (← arg args 0)
    h.copyOp choice (← h.placeToOp choice place) dest
  | "volatile_store" =>
    coreArity args 2
    let place ← h.derefPointer choice (← arg args 0)
    h.copyOp choice (← arg args 1) place
  | "vtable_size" | "vtable_align" =>
    let ptr ← pointer h choice (← arg args 0)
    let (size, align) ← h.vtableSizeAlign choice ptr none
    let value ← if name == "vtable_size" then pure size.bytes
      else liftResult (align.bytes |>.mapError fun e => .invalidProgram (toString e))
    writeUsize h choice value dest
  | "discriminant_value" =>
    let place ← h.derefPointer choice (← arg args 0)
    let op ← h.placeToOp choice place
    let variant ← h.readDiscriminant choice op
    let result ← h.discriminantForVariant choice op.layout.ty variant
    h.writeImmediate choice result.imm dest
  | "fadd_algebraic" | "fsub_algebraic" | "fmul_algebraic" | "fdiv_algebraic" | "frem_algebraic" =>
    let a ← h.readImmediate choice (← arg args 0)
    let b ← h.readImmediate choice (← arg args 1)
    let op := match name with
      | "fadd_algebraic" => BinOp.Add | "fsub_algebraic" => .Sub
      | "fmul_algebraic" => .Mul | "fdiv_algebraic" => .Div | _ => .Rem
    let result ← ScalarOps.binary h.scalarOps choice op a b
    let result ← h.applyFloatNondeterminism choice result
    h.writeImmediate choice result.imm dest
  | "fadd_fast" | "fsub_fast" | "fmul_fast" | "fdiv_fast" | "frem_fast" =>
    arity args 2
    let a ← h.readImmediate choice (← arg args 0)
    let b ← h.readImmediate choice (← arg args 1)
    let finite := fun value => do
      let bits ← FloatOps.readBits h.floatOps choice value
      match (← floatEngine bits.decode).value with
      | .finite _ _ => pure true | _ => pure false
    let aFinite ← finite a
    let bFinite ← finite b
    if !aFinite && !bFinite then ub "fast float intrinsic has two non-finite inputs"
    if !aFinite then ub "fast float intrinsic has non-finite first input"
    if !bFinite then ub "fast float intrinsic has non-finite second input"
    let op := match name with
      | "fadd_fast" => BinOp.Add | "fsub_fast" => .Sub
      | "fmul_fast" => .Mul | "fdiv_fast" => .Div | _ => .Rem
    let result ← ScalarOps.binary h.scalarOps choice op a b
    if !(← finite result) then ub "fast float intrinsic produced non-finite result"
    let result ← h.floatFastError choice result 4
    h.writeImmediate choice result.imm dest
  | "fabs" =>
    let value ← h.readImmediate choice (← arg args 0)
    let bits ← FloatOps.readBits h.floatOps choice value
    writeFloat h choice (← floatEngine (IntrinsicFloat.abs bits)) dest
  | "va_copy" => IntrinsicVarArgs.copy h.varArgsHooks choice (← arg args 0) dest
  | "va_end" => IntrinsicVarArgs.finish h.varArgsHooks choice (← arg args 0)
  | "va_arg" => IntrinsicVarArgs.next h.varArgsHooks choice h.varArgsFuel (← arg args 0) dest
  | "abort_immediate" => throw (.machineStop "the program aborted execution")
  | "breakpoint" => arity args 0; throw (.machineStop "trace/breakpoint trap")
  | "catch_unwind" =>
    arity args 3
    h.catchUnwind choice (← arg args 0) (← arg args 1) (← arg args 2) dest ret
    return true
  | "ptr_mask" =>
    arity args 2
    let ptr ← pointer h choice (← arg args 0)
    let mask ← usize h choice (← arg args 1)
    h.writePointer choice { ptr with offset := Size.ofBytes (UInt64.land ptr.offset.bytes mask) } dest
  | "is_val_statically_known" =>
    arity args 1
    writeScalar h choice (.fromBool (← h.chooseStaticKnown choice)) dest
  | "assert_inhabited" | "assert_zero_valid" | "assert_mem_uninitialized_valid" => pure ()
  | "float_to_int_unchecked" =>
    arity args 1
    let source ← h.readImmediate choice (← arg args 0)
    let bits ← FloatOps.readBits h.floatOps choice source
    let target := h.destLayout dest
    let kind ← h.integerKind choice target.ty
    let width ← liftResult (target.layout.size.bitsNat |>.mapError fun e => .invalidProgram (toString e))
    let some result ← floatEngine (IntrinsicFloat.toIntegerChecked bits width kind.signed)
      | ub "float_to_int_unchecked value cannot be represented in target type"
    let scalar ← if kind.signed then liftResult (Memory.Scalar.fromInt result target.layout.size |>.mapError ScalarOps.scalarError)
      else liftResult (Memory.Scalar.fromUInt (BitVec.ofInt 128 result) target.layout.size |>.mapError ScalarOps.scalarError)
    writeScalar h choice scalar dest
  | _ =>
    if !(← floatIntrinsic h choice name args dest) then
      match h.mathHooks with
      | none => return false
      | some math =>
        if !(← Miri.Interpreter.Math.evalIntrinsic math choice name types args dest) then
          return false
  h.returnToBlock choice ret
  return true

/-- MIR fallback arithmetic uses the existing concrete scalar engine; intrinsic
names that the pinned dispatcher does not intercept must enter that fallback
rather than acquiring invented dispatcher behavior. -/
def arithmetic [PointerProvenance P] (h : IntrinsicHooks P S C V) (choice : C)
    (op : BinOp) (left right : OpTy P) (dest : V) : RvalueM S Unit := do
  let left ← h.readImmediate choice left
  let right ← h.readImmediate choice right
  let result ← ScalarOps.binary h.scalarOps choice op left right
  h.writeImmediate choice result.imm dest

/-- Actual memory-copy primitive adapter, preserving updated memory and machine
state even on failure. Error classification is an explicit required boundary. -/
def memoryCopyAdapter [DecidableEq K]
    (target : TargetDataLayout)
    (hooks : MemoryCopyHooks P E K H PE)
    (classifyError : MemoryLifecycleError → StepError)
    (choice : C) (source dest : Pointer (Option P)) (size : Size) (nonoverlapping : Bool) :
    RvalueM (MemoryState P E K × H) Unit := fun state =>
  let _ := choice
  let result := MemoryLifecycle.memCopyRepeatedly state.1 state.2 source dest size 1 nonoverlapping
    (Size.fromBits target.pointerWidth.bits) hooks
  match result.outcome with
  | .ok _ => .ok () (result.memory, result.hooks)
  | .error error => .error (classifyError error) (result.memory, result.hooks)

/-- Source statement intrinsics preserve operand evaluation order and UB. -/
def evalNondivergingWith [PointerProvenance P] (h : MemoryIntrinsicHooks P S C)
    (evalOperandAt : C → OperandPath → MIR.Operand → RvalueM S (OpTy P)) (choice : C)
    (intrinsic : NonDivergingIntrinsic) : RvalueM S Unit := do
  match intrinsic with
  | .Assume condition =>
    let op ← evalOperandAt choice (OperandPath.instruction "value") condition
    let value ← h.readImmediate choice op
    let scalar ← liftResult (value.imm.toScalar |>.mapError ScalarOps.immediateError)
    let condition ← liftResult (scalar.toBool |>.mapError ScalarOps.scalarError)
    if !condition then ub "assume called with false"
  | .CopyNonOverlapping args =>
    let source ← evalOperandAt choice (OperandPath.instruction "src") args.source
    let dest ← evalOperandAt choice (OperandPath.instruction "dst") args.destination
    let count ← evalOperandAt choice (OperandPath.instruction "count") args.count
    copyWith h choice source dest count true

def evalNondiverging [PointerProvenance P] (h : IntrinsicHooks P S C V) (choice : C)
    (intrinsic : NonDivergingIntrinsic) : RvalueM S Unit :=
  evalNondivergingWith h.memory h.evalOperandAt choice intrinsic

end Intrinsics
end Miri.Interpreter
