import Miri.Interpreter.IntrinsicX86.Basic
namespace Miri.Interpreter.IntrinsicX86
open Miri.ABI Miri.Memory Miri.MIR

inductive FloatBin where
  | cmp (gt lt eq unordered : Bool) | min | max

def cmpImm (h : Hooks P S C V) (choice : C) (name : String) (imm : Int8) : M S FloatBin := do
  let value := imm.toInt
  if value < 0 || value >= 32 then invalid "invalid x86 comparison immediate"
  let (gt,lt,eq,u) := match value.toNat % 8 with
    | 0 => (false,false,true,false) | 1 => (false,true,false,false)
    | 2 => (false,true,true,false) | 3 => (false,false,false,true)
    | 4 => (true,true,false,true) | 5 => (true,false,true,true)
    | 6 => (true,false,false,true) | _ => (true,true,true,false)
  if value.toNat &&& 8 != 0 then
    feature h choice name "avx"
    pure (.cmp gt lt eq (!u))
  else pure (.cmp gt lt eq u)

def readFloat [PointerProvenance P] (value : Memory.Scalar P) (format : FloatFormat) : M S FloatBits := do
  let bits ← scalarResult (value.toBits format.size)
  let value : FloatBits := ⟨format,bits⟩
  let _ ← floatResult value.decode
  pure value

def floatScalar (value : FloatBits) : M S (Memory.Scalar P) := scalarResult (Memory.Scalar.fromUInt value.bits value.format.size)

def floatBin [PointerProvenance P] (format : FloatFormat) (op : FloatBin)
    (left right : RvalueImmTy P) : M S (Memory.Scalar P) := do
  let leftScalar ← scalar left
  let left ← readFloat leftScalar format
  let rightScalar ← scalar right
  let right ← readFloat rightScalar format
  let compared ← floatResult (left.partialCompare right)
  match op with
  | .cmp gt lt eq unordered =>
    let yes := match compared with | none => unordered | some .lt => lt | some .eq => eq | some .gt => gt
    fromUInt (if yes then 2^format.width-1 else 0) format.size
  | .min => pure (if compared == some .lt then leftScalar else rightScalar)
  | .max => pure (if compared == some .gt then leftScalar else rightScalar)

def floatBinary [PointerProvenance P] (h : Hooks P S C V) (choice : C) (format : FloatFormat)
    (op : FloatBin) (first : Bool) (left right : OpTy P) (dest : V) : M S Unit := do
  let (left,ln) ← projectRead h choice left
  let (right,rn) ← projectRead h choice right
  let (dest,n) ← projectWrite h choice dest
  same n ln
  same n rn
  if first then
    let left0 ← readLane h choice left 0
    let right0 ← readLane h choice right 0
    let result ← floatBin format op left0 right0
    write h choice result (← h.architecture.simd.indexWrite choice dest 0)
    copyRest h choice left dest n
  else
    for i in [:n.toNat] do
      let i := UInt64.ofNat i
      let left ← readLane h choice left i
      let right ← readLane h choice right i
      let dest ← h.architecture.simd.indexWrite choice dest i
      write h choice (← floatBin format op left right) dest

/-- Source relative-error arithmetic, with all legal RNG choices explicit. -/
def relativeError (h : Hooks P S C V) (choice : C) (value : FloatBits) : M S FloatBits := do
  if !h.floatNondet || h.roundingError == .none then return value
  let decoded ← floatResult value.decode
  match decoded.value with
  | .finite n _ => if n == 0 then return value
  | _ => return value
  let precision := value.format.fractionBits+1
  let magnitude ← if h.roundingError == .max then pure (2^precision-1) else h.errorMagnitude choice precision
  if magnitude >= 2^precision then invalid "illegal x86 relative-error choice"
  let negative ← h.errorNegative choice
  let error ← floatResult (FloatBits.roundRatio value.format negative magnitude (2^(precision+12)))
  let product ← floatResult (FloatBits.arithmetic .Mul value error)
  floatResult (FloatBits.arithmetic .Add value product)

def floatUnary [PointerProvenance P] (h : Hooks P S C V) (choice : C) (rsqrt first : Bool)
    (source : OpTy P) (dest : V) : M S Unit := do
  let (source,sn) ← projectRead h choice source
  let (dest,n) ← projectWrite h choice dest
  same n sn
  let run := fun i => do
    let value ← readLane h choice source i
    let projected ← if first then pure none else pure (some (← h.architecture.simd.indexWrite choice dest i))
    let value ← readFloat (← scalar value) .binary32
    let denominator ← if rsqrt then h.sqrt choice value else pure value
    let one ← floatResult (FloatBits.fromInteger .binary32 1)
    -- rustc_apfloat propagates and quiets the RHS NaN here. Unlike MIR
    -- arithmetic, this source helper never applies Miri adjust_nan afterward.
    let divided ← if ← floatResult denominator.isNaN then
        floatResult (denominator.convert denominator.format)
      else floatResult (FloatBits.arithmetic .Div one denominator)
    let result ← relativeError h choice divided
    let dest ← match projected with | some dest => pure dest | none => h.architecture.simd.indexWrite choice dest i
    write h choice (← floatScalar result) dest
  if first then
    run 0
    copyRest h choice source dest n
  else for i in [:n.toNat] do run (UInt64.ofNat i)

def roundingImm (value : Int32) : Except StepError FloatIntegralRound :=
  let value := value.toInt
  if value < 0 || value >= 16 then .error (.invalidProgram "invalid x86 rounding mode")
  else .ok (match value.toNat &&& 7 with | 0 => .even | 1 => .floor | 2 => .ceil | 3 => .trunc | _ => .even)

def roundFloat [PointerProvenance P] (h : Hooks P S C V) (choice : C) (format : FloatFormat)
    (left : Option (OpTy P)) (source rounding : OpTy P) (dest : V) : M S Unit := do
  let left ← match left with | none => pure none | some left => pure (some (← projectRead h choice left))
  let (source,sn) ← projectRead h choice source
  let (dest,n) ← projectWrite h choice dest
  if let some (_,ln) := left then same n ln
  same n sn
  let rounding ← liftResult (roundingImm (← scalarResult ((← read h choice rounding).toInt32)))
  let count := if left.isSome then 1 else n.toNat
  for i in [:count] do
    let i := UInt64.ofNat i
    let value ← readFloat (← readScalarLane h choice source i) format
    let result ← floatResult (IntrinsicFloat.roundIntegral value rounding)
    write h choice (← floatScalar result) (← h.architecture.simd.indexWrite choice dest i)
  if let some (left,_) := left then copyRest h choice left dest n

def checkedFloatToInt [PointerProvenance P] (h : Hooks P S C V) (choice : C)
    (source : RvalueImmTy P) (dest : TyAndLayout TyId) (rounding : FloatIntegralRound) : M S (RvalueImmTy P) := do
  let value ← FloatOps.readBits h.architecture.simd.floatOps choice source
  let value ← floatResult (IntrinsicFloat.roundIntegral value rounding)
  let decoded ← floatResult value.decode
  let minimum ← sizeResult dest.layout.size.signedIntMin
  let maximum ← sizeResult dest.layout.size.signedIntMax
  let result := match decoded.value with
    | .finite numerator denominator =>
      let n := Int.ofNat (numerator/denominator)
      let n := if decoded.negative then -n else n
      if minimum <= n && n <= maximum then n else minimum
    | _ => minimum
  makeImm result dest

def convertFloatToInt [PointerProvenance P] (h : Hooks P S C V) (choice : C)
    (source : OpTy P) (rounding : FloatIntegralRound) (dest : V) : M S Unit := do
  let (source,sn) ← projectRead h choice source
  let (dest,n) ← projectWrite h choice dest
  let element ← h.architecture.simd.fieldLayout choice (h.architecture.simd.placeLayout dest) 0
  let .integer kind ← h.architecture.simd.scalarOps.classify choice element.ty
    | invalid "x86 float conversion output must be signed integer"
  unless kind.signed do invalid "x86 float conversion output must be signed integer"
  for i in [:min sn.toNat n.toNat] do
    let value ← readLane h choice source (UInt64.ofNat i)
    let dest ← h.architecture.simd.indexWrite choice dest (UInt64.ofNat i)
    let result ← checkedFloatToInt h choice value (h.architecture.simd.placeLayout dest) rounding
    h.architecture.simd.writeImmediate choice result.imm dest
  for i in [sn.toNat:n.toNat] do
    let dest ← h.architecture.simd.indexWrite choice dest (UInt64.ofNat i)
    write h choice (← fromInt 0 (h.architecture.simd.placeLayout dest).layout.size) dest

end Miri.Interpreter.IntrinsicX86
