import Miri.Interpreter.IntrinsicX86.Extras
namespace Miri.Interpreter.IntrinsicX86
open Miri.ABI Miri.Memory Miri.MIR

def floatDispatch [PointerProvenance P] (h : Hooks P S C V) (choice : C)
    (full name : String) (args : Array (OpTy P)) (dest : V) : M S Bool := do
  let double := name.endsWith ".sd" || name.endsWith ".pd" || name.endsWith ".pd.256"
  let format := if double then FloatFormat.binary64 else .binary32
  if ["sse.min.ss","sse.max.ss","sse.min.ps","sse.max.ps","sse2.min.sd","sse2.max.sd","sse2.min.pd","sse2.max.pd",
      "avx.min.ps.256","avx.max.ps.256","avx.min.pd.256","avx.max.pd.256"].contains name then
    signature h choice full args 2
    let minimum := name.startsWith "sse.min" || name.startsWith "sse2.min" || name.startsWith "avx.min"
    floatBinary h choice format (if minimum then .min else .max) (name.endsWith ".ss" || name.endsWith ".sd")
      (← arg args 0) (← arg args 1) dest
  else if ["sse.cmp.ss","sse.cmp.ps","sse2.cmp.sd","sse2.cmp.pd","avx.cmp.ps.256","avx.cmp.pd.256"].contains name then
    signature h choice full args 3
    let op ← cmpImm h choice full (← scalarResult ((← read h choice (← arg args 2)).toInt8))
    floatBinary h choice format op (name.endsWith ".ss" || name.endsWith ".sd") (← arg args 0) (← arg args 1) dest
  else if ["sse.rcp.ss","sse.rsqrt.ss","sse.rcp.ps","sse.rsqrt.ps","avx.rcp.ps.256","avx.rsqrt.ps.256"].contains name then
    signature h choice full args 1
    floatUnary h choice (name.startsWith "sse.rsqrt" || name.startsWith "avx.rsqrt") (name.endsWith ".ss") (← arg args 0) dest
  else if ["sse41.round.ss","sse41.round.sd"].contains name then
    signature h choice full args 3
    roundFloat h choice format (some (← arg args 0)) (← arg args 1) (← arg args 2) dest
  else if ["sse41.round.ps","sse41.round.pd","avx.round.ps.256","avx.round.pd.256"].contains name then
    signature h choice full args 2
    roundFloat h choice format none (← arg args 0) (← arg args 1) dest
  else if ["sse2.cvtps2dq","sse2.cvttps2dq","sse2.cvtpd2dq","sse2.cvttpd2dq","avx.cvt.ps2dq.256","avx.cvtt.ps2dq.256","avx.cvt.pd2dq.256","avx.cvtt.pd2dq.256"].contains name then
    signature h choice full args 1
    let source ← arg args 0
    if name.startsWith "sse2." then
      let (sn,_) ← h.architecture.simd.simdSizeAndType choice source.layout.ty
      let (dn,_) ← h.architecture.simd.simdSizeAndType choice (h.architecture.simd.placeLayout dest).ty
      same sn (if name == "sse2.cvtps2dq" || name == "sse2.cvttps2dq" then 4 else 2)
      same dn 4
    let trunc := name.startsWith "sse2.cvtt" || name.startsWith "avx.cvtt"
    convertFloatToInt h choice source (if trunc then .trunc else .even) dest
  else if ["sse.cvtss2si","sse.cvttss2si","sse.cvtss2si64","sse.cvttss2si64","sse2.cvtsd2si","sse2.cvttsd2si","sse2.cvtsd2si64","sse2.cvttsd2si64"].contains name then
    signature h choice full args 1
    let (source,_) ← projectRead h choice (← arg args 0)
    let source ← readLane h choice source 0
    let trunc := name.startsWith "sse.cvtt" || name.startsWith "sse2.cvtt"
    let result ← checkedFloatToInt h choice source (h.architecture.simd.placeLayout dest) (if trunc then .trunc else .even)
    h.architecture.simd.writeImmediate choice result.imm dest
  else if name == "sse2.cvtsd2ss" then
    signature h choice full args 2
    let (left,ln) ← projectRead h choice (← arg args 0)
    let (right,_) ← projectRead h choice (← arg args 1)
    let (dest,n) ← projectWrite h choice dest
    same n ln
    let right ← readLane h choice right 0
    let dest0 ← h.architecture.simd.indexWrite choice dest 0
    let result ← FloatOps.castFloatToFloat h.architecture.simd.floatOps choice right (h.architecture.simd.placeLayout dest0)
    h.architecture.simd.writeImmediate choice result.imm dest0
    copyRest h choice left dest n
  else if ["sse.comieq.ss","sse.comilt.ss","sse.comile.ss","sse.comigt.ss","sse.comige.ss","sse.comineq.ss",
      "sse.ucomieq.ss","sse.ucomilt.ss","sse.ucomile.ss","sse.ucomigt.ss","sse.ucomige.ss","sse.ucomineq.ss",
      "sse2.comieq.sd","sse2.comilt.sd","sse2.comile.sd","sse2.comigt.sd","sse2.comige.sd","sse2.comineq.sd",
      "sse2.ucomieq.sd","sse2.ucomilt.sd","sse2.ucomile.sd","sse2.ucomigt.sd","sse2.ucomige.sd","sse2.ucomineq.sd"].contains name then
    signature h choice full args 2
    let (left,ln) ← projectRead h choice (← arg args 0)
    let (right,rn) ← projectRead h choice (← arg args 1)
    same ln rn
    let left ← readFloat (← readScalarLane h choice left 0) format
    let right ← readFloat (← readScalarLane h choice right 0) format
    let order ← floatResult (left.partialCompare right)
    let operation := ((name.splitOn ".")[1]?).getD ""
    let result := if operation.endsWith "neq" then order != some .eq else if operation.endsWith "eq" then order == some .eq
      else if operation.endsWith "lt" then order == some .lt else if operation.endsWith "le" then order == some .lt || order == some .eq
      else if operation.endsWith "gt" then order == some .gt else order == some .gt || order == some .eq
    write h choice (.fromScalarInt (.ofUInt32 (if result then 1 else 0))) dest
  else return false
  return true

end Miri.Interpreter.IntrinsicX86
