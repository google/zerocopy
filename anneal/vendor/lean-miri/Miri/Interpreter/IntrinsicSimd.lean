import Miri.Interpreter.Cast
import Miri.Interpreter.IntrinsicFloat

/-! Pinned core intrinsics/simd.rs and Miri intrinsics/simd.rs dispatch.
Every lane retains its canonical compiler type and full pointer provenance;
projection, memory and compiler dependencies remain required typed effects. -/
namespace Miri.Interpreter
open Miri.ABI Miri.Memory Miri.MIR
inductive SimdMathOp where
  | sqrt | sin | cos | exp | exp2 | log | log2 | log10
  deriving DecidableEq, Repr
structure IntrinsicSimdHooks (P S C V : Type) where
  target : TargetDataLayout
  boolTy : TyId
  u8Ty : TyId
  isSimd : C → TyId → RvalueM S Bool
  simdSizeAndType : C → TyId → RvalueM S (UInt64 × TyId)
  forceAllocation : C → V → RvalueM S V
  placeLayout : V → TyAndLayout TyId
  placePointer : V → Except StepError (Pointer (Option P))
  fieldRead : C → OpTy P → Nat → RvalueM S (OpTy P)
  fieldWrite : C → V → Nat → RvalueM S V
  fieldLayout : C → TyAndLayout TyId → Nat → RvalueM S (TyAndLayout TyId)
  indexRead : C → OpTy P → UInt64 → RvalueM S (OpTy P)
  indexWrite : C → V → UInt64 → RvalueM S V
  readImmediate : C → OpTy P → RvalueM S (RvalueImmTy P)
  writeImmediate : C → Immediate P → V → RvalueM S Unit
  copyOp : C → OpTy P → V → RvalueM S Unit
  derefImmediate : C → RvalueImmTy P → RvalueM S V
  readPlaceImmediate : C → V → RvalueM S (RvalueImmTy P)
  unalignedPlace : C → Pointer (Option P) → TyAndLayout TyId → RvalueM S V
  checkAlign : C → Pointer (Option P) → Align → RvalueM S Unit
  readBytes : C → Pointer (Option P) → Size → RvalueM S (Array UInt8)
  writeBytes : C → Pointer (Option P) → Array UInt8 → RvalueM S Unit
  shuffleConst : C → Nat → RvalueM S (Array UInt32)
  alignmentConst : C → Nat → RvalueM S Memory.SimdAlignment
  scalarOps : ScalarOpsHooks P S C
  floatOps : FloatOpsHooks P S C
  castHooks : CastHooks P S C V
  chooseEqualFloatRight : C → FloatBits → FloatBits → RvalueM S Bool
  fuseMulAdd : C → RvalueM S Bool
  mathLane : C → SimdMathOp → OpTy P → V → RvalueM S Unit
  returnToBlock : C → Option BasicBlockId → RvalueM S Unit

namespace IntrinsicSimd
private def invalid (message : String) : RvalueM S A := throw (.invalidProgram message)
private def ub (message : String) : RvalueM S A := throw (.undefinedBehavior message)
private def liftResult (result : Except StepError A) : RvalueM S A :=
  match result with | .ok result => pure result | .error error => throw error
private def engine (result : Except FloatError A) : RvalueM S A :=
  liftResult (result.mapError fun error => .invalidProgram s!"{repr error}")
private def scalar (value : RvalueImmTy P) : RvalueM S (Memory.Scalar P) :=
  liftResult (value.imm.toScalar |>.mapError ScalarOps.immediateError)
private def arg (args : Array (OpTy P)) (index : Nat) : RvalueM S (OpTy P) :=
  match args[index]? with | some value => pure value | none => invalid "SIMD intrinsic missing argument"
private def arity (args : Array (OpTy P)) (count : Nat) : RvalueM S Unit :=
  if args.size == count then pure () else ub "SIMD intrinsic argument count mismatch"
private def sameLength (a b : UInt64) : RvalueM S Unit :=
  if a == b then pure () else invalid "SIMD vector length mismatch"
private def arrayLength (layout : TyAndLayout TyId) : RvalueM S UInt64 :=
  match layout.layout.fields with | .Array _ count => pure count | _ => invalid "SIMD sole field must be array"
private def toRead (h : IntrinsicSimdHooks P S C V) (choice : C) (op : OpTy P) : RvalueM S (OpTy P × UInt64) := do
  if !(← h.isSimd choice op.layout.ty) then invalid "project_to_simd requires repr(simd)"
  let array ← h.fieldRead choice op 0
  pure (array, ← arrayLength array.layout)
private def toWrite (h : IntrinsicSimdHooks P S C V) (choice : C) (dest : V) : RvalueM S (V × UInt64) := do
  if !(← h.isSimd choice (h.placeLayout dest).ty) then invalid "project_to_simd requires repr(simd)"
  let array ← h.fieldWrite choice dest 0
  pure (array, ← arrayLength (h.placeLayout array))
private def lane (h : IntrinsicSimdHooks P S C V) (choice : C) (array : OpTy P) (index : UInt64) : RvalueM S (RvalueImmTy P) := do
  h.readImmediate choice (← h.indexRead choice array index)
private def writeScalar (h : IntrinsicSimdHooks P S C V) (choice : C) (value : Memory.Scalar P) (dest : V) :=
  h.writeImmediate choice (.scalar value) dest

def elementToBool [PointerProvenance P] (h : IntrinsicSimdHooks P S C V) (choice : C) (value : RvalueImmTy P) : RvalueM S Bool := do
  let _ ← h.floatOps.integerKindOf choice value.layout.ty
  let value ← liftResult ((← scalar value).toInt value.layout.layout.size |>.mapError ScalarOps.scalarError)
  if value == 0 then pure false else if value == -1 then pure true
  else ub "each SIMD mask element must be all-zero or all-one bits"
private def boolElement (value : Bool) (size : Size) : RvalueM S (Memory.Scalar P) :=
  liftResult (Memory.Scalar.fromInt (if value then -1 else 0) size |>.mapError ScalarOps.scalarError)
private def floatScalar (bits : FloatBits) : RvalueM S (Memory.Scalar P) :=
  liftResult (Memory.Scalar.fromUInt bits.bits bits.format.size |>.mapError ScalarOps.scalarError)
private def floatMinMax [PointerProvenance P] (h : IntrinsicSimdHooks P S C V) (choice : C)
    (minimum : Bool) (left right : RvalueImmTy P) : RvalueM S (Memory.Scalar P) := do
  if left.layout.ty != right.layout.ty then invalid "SIMD float minmax operand types differ"
  let a ← FloatOps.readBits h.floatOps choice left
  let b ← FloatOps.readBits h.floatOps choice right
  let equal ← engine (a.comparison .Eq b)
  let choose ← if equal then h.chooseEqualFloatRight choice a b else pure false
  let result ← engine (IntrinsicFloat.minMax a b (if minimum then .minimumNumber else .maximumNumber) choose)
  let result ← if equal then pure result else FloatOps.adjustNaN h.floatOps choice result [a,b]
  floatScalar result

private def saturating [PointerProvenance P] (h : IntrinsicSimdHooks P S C V) (choice : C)
    (add : Bool) (left right : RvalueImmTy P) : RvalueM S (Memory.Scalar P) := do
  if left.layout.ty != right.layout.ty then invalid "SIMD saturating operand types differ"
  let _ ← h.floatOps.integerKindOf choice left.layout.ty
  let result ← ScalarOps.binary h.scalarOps choice (if add then .AddWithOverflow else .SubWithOverflow) left right
  let (value,overflow) ← liftResult (result.imm.toScalarPair |>.mapError ScalarOps.immediateError)
  if !(← liftResult (overflow.toBool |>.mapError ScalarOps.scalarError)) then return value
  let signed ← match left.layout.layout.backendRepr.isSigned with | .ok signed => pure signed | .error _ => invalid "saturating source is not scalar"
  if signed then
    let first ← liftResult ((← scalar left).toInt left.layout.layout.size |>.mapError ScalarOps.scalarError)
    let bound ← liftResult ((if first >= 0 then left.layout.layout.size.signedIntMax else left.layout.layout.size.signedIntMin)
      |>.mapError fun e => .invalidProgram (toString e))
    liftResult (Memory.Scalar.fromInt bound left.layout.layout.size |>.mapError ScalarOps.scalarError)
  else
    let bound ← if add then liftResult (left.layout.layout.size.unsignedIntMax |>.mapError fun e => .invalidProgram (toString e)) else pure 0
    liftResult (Memory.Scalar.fromUInt bound left.layout.layout.size |>.mapError ScalarOps.scalarError)

private def numeric [PointerProvenance P] (h : IntrinsicSimdHooks P S C V) (choice : C)
    (op : IntegerIntrinsic) (value : RvalueImmTy P) : RvalueM S (Memory.Scalar P) := do
  let kind ← h.floatOps.integerKindOf choice value.layout.ty
  let scalar ← liftResult (value.imm.toScalarInt |>.mapError ScalarOps.immediateError)
  let type := IntegerType.mk value.layout.layout.size kind
  let result ← liftResult (IntegerIntrinsic.run op scalar type type |>.mapError fun e => match e with
    | .scalar e => ScalarOps.scalarIntError e
    | .undefinedBehaviorOnZero _ => .undefinedBehavior "nonzero SIMD numeric intrinsic called on zero"
    | _ => .invalidProgram "SIMD numeric layout mismatch")
  pure (.fromScalarInt result)

private def shift [PointerProvenance P] (h : IntrinsicSimdHooks P S C V) (choice : C) (op : BinOp)
    (index : UInt64) (left right : RvalueImmTy P) : RvalueM S (RvalueImmTy P) := do
  let leftKind ← h.floatOps.integerKindOf choice left.layout.ty
  let rightKind ← h.floatOps.integerKindOf choice right.layout.ty
  let leftScalar ← liftResult (left.imm.toScalarInt |>.mapError ScalarOps.immediateError)
  let rightScalar ← liftResult (right.imm.toScalarInt |>.mapError ScalarOps.immediateError)
  let result ← match IntegerOps.binary op ⟨leftScalar, ⟨left.layout.layout.size,leftKind⟩⟩
      ⟨rightScalar, ⟨right.layout.layout.size,rightKind⟩⟩ with
    | .ok (.scalar result) => pure result
    | .ok _ => invalid "SIMD shift returned nonscalar"
    | .error (.undefinedBehavior (.shiftOverflow _ amount _)) => ub s!"overflowing SIMD shift by {amount} in lane {index}"
    | .error error => throw (ScalarOps.integerError error)
  pure ⟨.scalar (.fromScalarInt result),left.layout⟩

private def wrappingOffset [PointerProvenance P] (h : IntrinsicSimdHooks P S C V) (choice : C)
    (left right : RvalueImmTy P) : RvalueM S (Memory.Scalar P) := do
  let ptr ← liftResult ((← scalar left).toPointer h.target |>.mapError ScalarOps.scalarError)
  let count ← liftResult ((← scalar right).toTargetIsize (Size.fromBits h.target.pointerWidth.bits) |>.mapError ScalarOps.scalarError)
  let some pointee ← h.castHooks.builtinDeref choice left.layout.ty true | invalid "SIMD pointer has no pointee"
  let layout ← h.castHooks.layoutOf choice pointee
  if layout.layout.size.bytes.toNat >= 2^63 then invalid "SIMD pointee size exceeds i64"
  let offset := Int64.ofInt (count.toInt * Int.ofNat layout.layout.size.bytes.toNat)
  let ptr ← liftResult (ptr.wrappingSignedOffset offset ⟨Size.fromBits h.target.pointerWidth.bits⟩ |>.mapError fun e => .invalidProgram s!"{repr e}")
  liftResult (Memory.Scalar.fromMaybePointer h.target ptr |>.mapError ScalarOps.scalarError)

private def binaryName : String → Option BinOp
  | "simd_add" => some .Add | "simd_sub" => some .Sub | "simd_mul" => some .Mul
  | "simd_div" => some .Div | "simd_rem" => some .Rem | "simd_shl" => some .ShlUnchecked | "simd_shr" => some .ShrUnchecked
  | "simd_and" => some .BitAnd | "simd_or" => some .BitOr | "simd_xor" => some .BitXor
  | "simd_eq" => some .Eq | "simd_ne" => some .Ne | "simd_lt" => some .Lt
  | "simd_le" => some .Le | "simd_gt" => some .Gt | "simd_ge" => some .Ge | _ => none
private def comparison : BinOp → Bool
  | .Eq | .Ne | .Lt | .Le | .Gt | .Ge => true | _ => false

private def checkPointerAlignment (h : IntrinsicSimdHooks P S C V) (choice : C)
    (ptr : Pointer (Option P)) (layout : TyAndLayout TyId) (alignment : Memory.SimdAlignment) : RvalueM S Unit := do
  if !(← h.isSimd choice layout.ty) then invalid "SIMD alignment check requires SIMD type"
  match layout.layout.backendRepr with
  | .SimdVector | .Memory => pure ()
  | _ => invalid "unexpected SIMD backend representation"
  match alignment with
  | .unaligned => pure ()
  | .element => h.checkAlign choice ptr (← h.fieldLayout choice layout 0).layout.align.abi
  | .vector => h.checkAlign choice ptr layout.layout.align.abi

private def bitIndex (target : TargetDataLayout) (index len : Nat) : RvalueM S Nat := do
  if index >= len then invalid "SIMD bit index out of bounds"
  pure (match target.endian with | .little => index | .big => len-1-index)
private def bitmaskLength (len : UInt64) : RvalueM S Nat := do
  let bits := ((len.toNat+7)/8)*8
  if bits > 64 then throw (.unsupported "SIMD bitmask vectors larger than 64 lanes")
  pure bits
private def decodeBytes (target : TargetDataLayout) (bytes : Array UInt8) : Nat :=
  match target.endian with
  | .big => bytes.foldl (fun acc byte => acc*256+byte.toNat) 0
  | .little => (bytes.toList.reverse).foldl (fun acc byte => acc*256+byte.toNat) 0
private def encodeBytes (target : TargetDataLayout) (bits size : Nat) : Array UInt8 :=
  (List.range size |>.map fun index => UInt8.ofNat (bits / 2^(8*(match target.endian with | .little => index | .big => size-1-index)) % 256)).toArray

private def readMask [PointerProvenance P] (h : IntrinsicSimdHooks P S C V) (choice : C) (mask : OpTy P) (len : Nat) : RvalueM S Nat := do
  let bits ← liftResult (mask.layout.layout.size.bitsNat |>.mapError fun e => .invalidProgram (toString e))
  match ← h.castHooks.typeInfo choice mask.layout.ty with
  | .integer kind =>
    if kind.signed || bits < len then invalid "invalid SIMD integer mask type/width"
    let scalar ← scalar (← h.readImmediate choice mask)
    let value ← liftResult (scalar.toBits mask.layout.layout.size |>.mapError ScalarOps.scalarError)
    if value.toNat >= 2^64 then invalid "SIMD mask integer exceeds u64"
    pure value.toNat
  | .array element _ =>
    if element != h.u8Ty || bits != len then invalid "invalid SIMD byte-array mask type/width"
    let .indirect place := mask.op | invalid "SIMD byte-array mask must be indirect"
    let bytes ← h.readBytes choice place.ptr mask.layout.layout.size
    if bytes.size != mask.layout.layout.size.bytes.toNat then invalid "SIMD mask byte-read length mismatch"
    pure (decodeBytes h.target bytes)
  | _ => invalid "invalid SIMD mask type"

private def castLane [PointerProvenance P] (h : IntrinsicSimdHooks P S C V) (choice : C)
    (name : String) (source : RvalueImmTy P) (target : TyAndLayout TyId) : RvalueM S (RvalueImmTy P) := do
  let sourceKind ← h.castHooks.typeInfo choice source.layout.ty
  let targetKind ← h.castHooks.typeInfo choice target.ty
  match sourceKind,targetKind with
  | .integer _, .integer _ | .integer _, .floating _ =>
    if name != "simd_as" && name != "simd_cast" then throw (.unsupported "unsupported SIMD integer cast")
    Cast.castFromIntLike h.castHooks choice (← scalar source) source.layout target
  | .floating _, .floating _ =>
    if name != "simd_as" && name != "simd_cast" then throw (.unsupported "unsupported SIMD float cast")
    FloatOps.castFloatToFloat h.floatOps choice source target
  | .floating _, .integer kind =>
    if name == "simd_as" then FloatOps.castFloatToInt h.floatOps choice source target
    else if name == "simd_cast" then
      let bits ← FloatOps.readBits h.floatOps choice source
      let width ← liftResult (target.layout.size.bitsNat |>.mapError fun e => .invalidProgram (toString e))
      let some value ← engine (IntrinsicFloat.toIntegerChecked bits width kind.signed) | ub "simd_cast value cannot be represented"
      let value ← if kind.signed then liftResult (Memory.Scalar.fromInt value target.layout.size |>.mapError ScalarOps.scalarError)
        else liftResult (Memory.Scalar.fromUInt (BitVec.ofInt 128 value) target.layout.size |>.mapError ScalarOps.scalarError)
      pure ⟨.scalar value,target⟩
    else throw (.unsupported "unsupported SIMD float-to-int cast")
  | .rawPointer _, .rawPointer _ =>
    if name != "simd_cast_ptr" then throw (.unsupported "unsupported SIMD pointer cast")
    Cast.ptrToPtr h.castHooks choice source target
  | .integer _, .rawPointer _ =>
    if name != "simd_with_exposed_provenance" then throw (.unsupported "unsupported SIMD from-exposed cast")
    Cast.pointerWithExposedProvenance h.castHooks choice source target
  | .rawPointer _, .integer _ =>
    if name != "simd_expose_provenance" then throw (.unsupported "unsupported SIMD expose cast")
    Cast.pointerExposeProvenance h.castHooks choice source target
  | _,_ => throw (.unsupported "unsupported SIMD lane cast types")

/-- Core always forces the destination before dispatch; lane effects occur in
source order and remain committed when a later lane fails. -/
def eval [PointerProvenance P] (h : IntrinsicSimdHooks P S C V) (choice : C) (name : String)
    (args : Array (OpTy P)) (dest : V) (ret : Option BasicBlockId) : RvalueM S Bool := do
  let originalDest ← h.forceAllocation choice dest
  let dest := originalDest
  if let some op := binaryName name then
    let (left,leftLen) ← toRead h choice (← arg args 0)
    let (right,rightLen) ← toRead h choice (← arg args 1)
    let (dest,destLen) ← toWrite h choice dest
    sameLength destLen leftLen
    sameLength destLen rightLen
    for index in [:destLen.toNat] do
      let i := UInt64.ofNat index
      let left ← lane h choice left i
      let right ← lane h choice right i
      let dest ← h.indexWrite choice dest i
      let value ← if op == .ShlUnchecked || op == .ShrUnchecked then shift h choice op i left right
        else ScalarOps.binary h.scalarOps choice op left right
      if comparison op then
        if value.layout.ty != h.boolTy then invalid "SIMD comparison did not return bool"
        let value ← liftResult ((← scalar value).toBool |>.mapError ScalarOps.scalarError)
        writeScalar h choice (← boolElement value (h.placeLayout dest).layout.size) dest
      else
        if value.layout.ty == h.boolTy || value.layout.ty != (h.placeLayout dest).ty then invalid "SIMD lane result type mismatch"
        h.writeImmediate choice value.imm dest
  else
    match name with
    | "simd_insert" | "simd_insert_dyn" | "simd_extract" | "simd_extract_dyn" =>
      let value ← h.readImmediate choice (← arg args 1)
      let index ← liftResult ((← scalar value).toUInt32 |>.mapError ScalarOps.scalarError)
      let index := UInt64.ofNat index.toNat
      let insert := name == "simd_insert" || name == "simd_insert_dyn"
      let element ← if insert then pure (some (← arg args 2)) else pure none
      let (input,len) ← toRead h choice (← arg args 0)
      if name == "simd_extract" || name == "simd_extract_dyn" then
        if index >= len then ub "SIMD extract index out of bounds"
        h.copyOp choice (← h.indexRead choice input index) dest
      else
        let some element := element | invalid "SIMD insert missing element"
        let (dest,destLen) ← toWrite h choice dest
        sameLength len destLen
        if index >= len then ub "SIMD insert index out of bounds"
        for i in [:destLen.toNat] do
          let place ← h.indexWrite choice dest (UInt64.ofNat i)
          let value ← if i == index.toNat then pure element else h.indexRead choice input (UInt64.ofNat i)
          h.copyOp choice value place
    | "simd_splat" =>
      let element ← arg args 0
      let (dest,len) ← toWrite h choice dest
      for i in [:len.toNat] do h.copyOp choice element (← h.indexWrite choice dest (UInt64.ofNat i))
    | "simd_neg" | "simd_fabs" | "simd_ceil" | "simd_floor" | "simd_round" | "simd_round_ties_even" | "simd_trunc"
    | "simd_ctlz" | "simd_ctpop" | "simd_cttz" | "simd_bswap" | "simd_bitreverse" =>
      let (input,len) ← toRead h choice (← arg args 0)
      let (dest,destLen) ← toWrite h choice dest
      sameLength destLen len
      for i in [:len.toNat] do
        let value ← lane h choice input (UInt64.ofNat i)
        let dest ← h.indexWrite choice dest (UInt64.ofNat i)
        let result ← match name with
          | "simd_neg" => scalar (← ScalarOps.unary h.scalarOps choice .Neg value)
          | "simd_ctlz" => numeric h choice .ctlz value | "simd_ctpop" => numeric h choice .ctpop value
          | "simd_cttz" => numeric h choice .cttz value | "simd_bswap" => numeric h choice .bswap value
          | "simd_bitreverse" => numeric h choice .bitreverse value
          | _ => do
            let bits ← FloatOps.readBits h.floatOps choice value
            if name == "simd_fabs" then floatScalar (← engine (IntrinsicFloat.abs bits))
            else
              let mode := match name with | "simd_ceil" => FloatIntegralRound.ceil | "simd_floor" => .floor
                                          | "simd_round" => .away | "simd_trunc" => .trunc | _ => .even
              let result ← engine (IntrinsicFloat.roundIntegral bits mode)
              floatScalar (← FloatOps.adjustNaN h.floatOps choice result [bits])
        writeScalar h choice result dest
    | "simd_maximum_number_nsz" | "simd_minimum_number_nsz" | "simd_saturating_add" | "simd_saturating_sub" | "simd_arith_offset" =>
      let (left,len) ← toRead h choice (← arg args 0)
      let (right,rightLen) ← toRead h choice (← arg args 1)
      let (dest,destLen) ← toWrite h choice dest
      sameLength destLen len
      sameLength destLen rightLen
      for i in [:len.toNat] do
        let left ← lane h choice left (UInt64.ofNat i)
        let right ← lane h choice right (UInt64.ofNat i)
        let dest ← h.indexWrite choice dest (UInt64.ofNat i)
        let result ← if name == "simd_arith_offset" then wrappingOffset h choice left right
          else if name == "simd_saturating_add" || name == "simd_saturating_sub" then saturating h choice (name == "simd_saturating_add") left right
          else floatMinMax h choice (name == "simd_minimum_number_nsz") left right
        writeScalar h choice result dest
    | "simd_reduce_and" | "simd_reduce_or" | "simd_reduce_xor" | "simd_reduce_any" | "simd_reduce_all" | "simd_reduce_max" | "simd_reduce_min" =>
      let (input,len) ← toRead h choice (← arg args 0)
      let boolean := name == "simd_reduce_any" || name == "simd_reduce_all"
      let toBool := fun value => do
        pure (RvalueImmTy.mk (.scalar (.fromBool (← elementToBool h choice value))) (← h.scalarOps.boolLayout choice))
      let mut result ← lane h choice input 0
      if boolean then result ← toBool result
      for i in [1:len.toNat] do
        let value ← lane h choice input (UInt64.ofNat i)
        if name == "simd_reduce_max" || name == "simd_reduce_min" then
          match ← h.castHooks.typeInfo choice result.layout.ty with
          | .floating _ => result := ⟨.scalar (← floatMinMax h choice (name == "simd_reduce_min") result value),result.layout⟩
          | _ =>
            let compared ← ScalarOps.binary h.scalarOps choice (if name == "simd_reduce_min" then .Le else .Ge) result value
            if !(← liftResult ((← scalar compared).toBool |>.mapError ScalarOps.scalarError)) then result := value
        else
          let value ← if boolean then toBool value else pure value
          result ← ScalarOps.binary h.scalarOps choice
            (if name == "simd_reduce_and" || name == "simd_reduce_all" then .BitAnd
             else if name == "simd_reduce_xor" then .BitXor else .BitOr) result value
      h.writeImmediate choice result.imm dest
    | "simd_reduce_add_ordered" | "simd_reduce_mul_ordered" =>
      let (input,len) ← toRead h choice (← arg args 0)
      let mut result ← h.readImmediate choice (← arg args 1)
      for i in [:len.toNat] do
        let value ← lane h choice input (UInt64.ofNat i)
        result ← ScalarOps.binary h.scalarOps choice (if name == "simd_reduce_add_ordered" then .Add else .Mul) result value
      h.writeImmediate choice result.imm dest
    | "simd_select" | "simd_select_bitmask" =>
      let mask ← arg args 0
      let (mask,maskLen) ← if name == "simd_select" then toRead h choice mask else pure (mask,0)
      let (yes,yesLen) ← toRead h choice (← arg args 1)
      let (no,noLen) ← toRead h choice (← arg args 2)
      let (dest,len) ← toWrite h choice dest
      let maskWidth ← if name == "simd_select_bitmask" then bitmaskLength len else pure 0
      if name == "simd_select" then sameLength len maskLen
      sameLength len yesLen
      sameLength len noLen
      let maskBits ← if name == "simd_select_bitmask" then readMask h choice mask maskWidth else pure 0
      for i in [:len.toNat] do
        let maskValue ← if name == "simd_select" then pure (some (← lane h choice mask (UInt64.ofNat i))) else pure none
        let yes ← lane h choice yes (UInt64.ofNat i)
        let no ← lane h choice no (UInt64.ofNat i)
        let dest ← h.indexWrite choice dest (UInt64.ofNat i)
        let mask ← match maskValue with
          | some value => elementToBool h choice value
          | none => pure (Nat.testBit maskBits (← bitIndex h.target i len.toNat))
        h.writeImmediate choice (if mask then yes.imm else no.imm) dest
    | "simd_bitmask" =>
      let (input,len) ← toRead h choice (← arg args 0)
      let maskLen ← bitmaskLength len
      let mut bits := 0
      for i in [:len.toNat] do
        if ← elementToBool h choice (← lane h choice input (UInt64.ofNat i)) then
          bits := bits + 2^(← bitIndex h.target i len.toNat)
      let layout := h.placeLayout dest
      let width ← liftResult (layout.layout.size.bitsNat |>.mapError fun e => .invalidProgram (toString e))
      match ← h.castHooks.typeInfo choice layout.ty with
      | .integer kind =>
        if kind.signed || width < maskLen then invalid "invalid SIMD bitmask integer destination"
        writeScalar h choice (← liftResult (Memory.Scalar.fromUInt (BitVec.ofNat 128 bits) layout.layout.size |>.mapError ScalarOps.scalarError)) dest
      | .array element _ =>
        if element != h.u8Ty || width != maskLen then invalid "invalid SIMD bitmask byte-array destination"
        let ptr ← liftResult (h.placePointer dest)
        h.writeBytes choice ptr (encodeBytes h.target bits layout.layout.size.bytes.toNat)
      | _ => invalid "invalid SIMD bitmask return type"
    | "simd_cast" | "simd_as" | "simd_cast_ptr" | "simd_with_exposed_provenance" | "simd_expose_provenance" =>
      if name == "simd_expose_provenance" then arity args 1
      let (input,len) ← toRead h choice (← arg args 0)
      let (dest,destLen) ← toWrite h choice dest
      sameLength destLen len
      for i in [:len.toNat] do
        let input ← lane h choice input (UInt64.ofNat i)
        let dest ← h.indexWrite choice dest (UInt64.ofNat i)
        let value ← castLane h choice name input (h.placeLayout dest)
        h.writeImmediate choice value.imm dest
    | "simd_shuffle" | "simd_shuffle_const_generic" =>
      let (left,len) ← toRead h choice (← arg args 0)
      let (right,rightLen) ← toRead h choice (← arg args 1)
      let (indices,indexLen) ← if name == "simd_shuffle" then toRead h choice (← arg args 2) else pure (left,0)
      let (dest,destLen) ← toWrite h choice dest
      let constIndices ← if name == "simd_shuffle_const_generic" then h.shuffleConst choice 2 else pure #[]
      sameLength len rightLen
      if name == "simd_shuffle" then sameLength indexLen destLen
      else if constIndices.size != destLen.toNat then invalid "SIMD shuffle constant length mismatch"
      for i in [:destLen.toNat] do
        let index ← if name == "simd_shuffle" then
            liftResult ((← scalar (← lane h choice indices (UInt64.ofNat i))).toUInt32 |>.mapError ScalarOps.scalarError)
          else match constIndices[i]? with | some index => pure index | none => invalid "SIMD shuffle constant index missing"
        let dest ← h.indexWrite choice dest (UInt64.ofNat i)
        let index := UInt64.ofNat index.toNat
        let value ← if index < len then lane h choice left index
          else do
            let total := len.toNat + rightLen.toNat
            if total >= 2^64 then invalid "SIMD shuffle total length exceeds u64"
            if index.toNat < total then lane h choice right (index-len)
            else ub "SIMD shuffle index out of bounds"
        h.writeImmediate choice value.imm dest
    | "simd_gather" | "simd_scatter" =>
      let (values,len) ← toRead h choice (← arg args 0)
      let (pointers,ptrLen) ← toRead h choice (← arg args 1)
      let (masks,maskLen) ← toRead h choice (← arg args 2)
      let (dest,destLen) ← if name == "simd_gather" then toWrite h choice dest else pure (dest,len)
      sameLength destLen len
      sameLength destLen ptrLen
      sameLength destLen maskLen
      for i in [:len.toNat] do
        let value ← lane h choice values (UInt64.ofNat i)
        let ptr ← lane h choice pointers (UInt64.ofNat i)
        let mask ← lane h choice masks (UInt64.ofNat i)
        if name == "simd_gather" then
          let dest ← h.indexWrite choice dest (UInt64.ofNat i)
          let value ← if ← elementToBool h choice mask then h.readPlaceImmediate choice (← h.derefImmediate choice ptr) else pure value
          h.writeImmediate choice value.imm dest
        else if ← elementToBool h choice mask then
          h.writeImmediate choice value.imm (← h.derefImmediate choice ptr)
    | "simd_masked_load" | "simd_masked_store" =>
      let (masks,maskLen) ← toRead h choice (← arg args 0)
      let pointer ← h.readImmediate choice (← arg args 1)
      let ptr ← liftResult ((← scalar pointer).toPointer h.target |>.mapError ScalarOps.scalarError)
      let valuesOp ← arg args 2
      let (values,len) ← toRead h choice valuesOp
      let vectorLayout := if name == "simd_masked_load" then h.placeLayout originalDest else valuesOp.layout
      let (dest,destLen) ← if name == "simd_masked_load" then toWrite h choice dest else pure (dest,len)
      sameLength destLen maskLen
      sameLength destLen len
      let alignment ← h.alignmentConst choice 3
      checkPointerAlignment h choice ptr vectorLayout alignment
      for i in [:len.toNat] do
        let mask ← lane h choice masks (UInt64.ofNat i)
        let value ← lane h choice values (UInt64.ofNat i)
        if name == "simd_masked_load" then
          let dest ← h.indexWrite choice dest (UInt64.ofNat i)
          let value ← if ← elementToBool h choice mask then
              let layout := h.placeLayout dest
              let offset ← liftResult (layout.layout.size.mul (UInt64.ofNat i) |>.mapError fun e => .invalidProgram (toString e))
              let ptr ← liftResult (ptr.wrappingOffset offset ⟨Size.fromBits h.target.pointerWidth.bits⟩ |>.mapError fun e => .invalidProgram s!"{repr e}")
              h.readPlaceImmediate choice (← h.unalignedPlace choice ptr layout)
            else pure value
          h.writeImmediate choice value.imm dest
        else if ← elementToBool h choice mask then
          let offset ← liftResult (value.layout.layout.size.mul (UInt64.ofNat i) |>.mapError fun e => .invalidProgram (toString e))
          let ptr ← liftResult (ptr.wrappingOffset offset ⟨Size.fromBits h.target.pointerWidth.bits⟩ |>.mapError fun e => .invalidProgram s!"{repr e}")
          h.writeImmediate choice value.imm (← h.unalignedPlace choice ptr value.layout)
    | "simd_fma" | "simd_relaxed_fma" =>
      let (a,len) ← toRead h choice (← arg args 0)
      let (b,bLen) ← toRead h choice (← arg args 1)
      let (c,cLen) ← toRead h choice (← arg args 2)
      let (dest,destLen) ← toWrite h choice dest
      sameLength destLen len
      sameLength destLen bLen
      sameLength destLen cLen
      for i in [:len.toNat] do
        let a ← lane h choice a (UInt64.ofNat i)
        let _ ← scalar a
        let b ← lane h choice b (UInt64.ofNat i)
        let _ ← scalar b
        let c ← lane h choice c (UInt64.ofNat i)
        let _ ← scalar c
        let dest ← h.indexWrite choice dest (UInt64.ofNat i)
        let format ← h.floatOps.formatOf choice (h.placeLayout dest).ty
        let read := fun value => do
          let value ← scalar value
          let bits ← liftResult (value.toBits format.size |>.mapError ScalarOps.scalarError)
          pure (FloatBits.mk format bits)
        let a ← read a
        let b ← read b
        let c ← read c
        let fuse ← if name == "simd_fma" then pure true else h.fuseMulAdd choice
        let result ← if fuse then engine (IntrinsicFloat.fusedMulAdd a b c)
          else engine ((← engine (a.arithmetic .Mul b)).arithmetic .Add c)
        writeScalar h choice (← floatScalar (← FloatOps.adjustNaN h.floatOps choice result [a,b,c])) dest
    | "simd_funnel_shl" | "simd_funnel_shr" =>
      let original ← arg args 0
      let (left,_) ← toRead h choice original
      let (right,_) ← toRead h choice (← arg args 1)
      let (amount,_) ← toRead h choice (← arg args 2)
      let (dest,_) ← toWrite h choice dest
      let (len,elementTy) ← h.simdSizeAndType choice original.layout.ty
      let _ ← h.floatOps.integerKindOf choice elementTy
      let layout ← h.castHooks.layoutOf choice elementTy
      let width ← liftResult (layout.layout.size.bitsNat |>.mapError fun e => .invalidProgram (toString e))
      for i in [:len.toNat] do
        let read := fun op => do
          liftResult ((← scalar (← lane h choice op (UInt64.ofNat i))).toBits layout.layout.size |>.mapError ScalarOps.scalarError)
        let left ← read left
        let right ← read right
        let amount ← read amount
        if amount.toNat >= width then ub s!"overflowing funnel shift in lane {i}"
        let shift := amount.toNat
        let inverse := width-shift
        let result := if name == "simd_funnel_shl" then Nat.lor (left.toNat * 2^shift) (right.toNat / 2^inverse)
          else Nat.lor (left.toNat * 2^inverse) (right.toNat / 2^shift)
        let (value,_) ← liftResult (ScalarInt.truncateFromUInt (BitVec.ofNat 128 result) layout.layout.size |>.mapError ScalarOps.scalarIntError)
        writeScalar h choice (.fromScalarInt value) (← h.indexWrite choice dest (UInt64.ofNat i))
    | "simd_fsqrt" | "simd_fsin" | "simd_fcos" | "simd_fexp" | "simd_fexp2" | "simd_flog" | "simd_flog2" | "simd_flog10" =>
      arity args 1
      let (input,len) ← toRead h choice (← arg args 0)
      let (dest,destLen) ← toWrite h choice dest
      sameLength destLen len
      let op := match name with
        | "simd_fsqrt" => SimdMathOp.sqrt | "simd_fsin" => .sin | "simd_fcos" => .cos
        | "simd_fexp" => .exp | "simd_fexp2" => .exp2 | "simd_flog" => .log | "simd_flog2" => .log2 | _ => .log10
      for i in [:len.toNat] do
        let input ← h.indexRead choice input (UInt64.ofNat i)
        let dest ← h.indexWrite choice dest (UInt64.ofNat i)
        let format ← h.floatOps.formatOf choice input.layout.ty
        if op != .sqrt && format == .binary128 then throw (.unsupported "pinned Miri f128 host unary operation is unimplemented")
        h.mathLane choice op input dest
    | _ => return false
  h.returnToBlock choice ret
  return true
end IntrinsicSimd
end Miri.Interpreter
