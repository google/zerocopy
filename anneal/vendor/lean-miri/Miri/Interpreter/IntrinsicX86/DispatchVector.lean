import Miri.Interpreter.IntrinsicX86.DispatchFloat
namespace Miri.Interpreter.IntrinsicX86
open Miri.ABI Miri.Memory Miri.MIR
inductive VectorInstruction where
  | avg | mulHigh | madWord | madByte | mulRound | sign | shuffle | sad
  | pack (bits : Nat) (signed : Bool)
  | permute | permute2 | shiftScalar (op : Shift) | shiftVector (op : Shift)
  | dot | multipleSad | dotBytes | ternary | permuteFloat (double : Bool)
  | insert | minPosition | test (high : Bool) (kind : Nat) | unaligned | nop | gather

def vectorSpec : String → Option VectorInstruction
  | "sse2.pavg.b" => some (.avg)
  | "sse2.pavg.w" => some (.avg)
  | "sse2.pmulh.w" => some (.mulHigh)
  | "sse2.pmulhu.w" => some (.mulHigh)
  | "sse2.pmadd.wd" => some (.madWord)
  | "sse2.psad.bw" => some (.sad)
  | "sse2.psll.w" => some (.shiftScalar .left)
  | "sse2.psll.d" => some (.shiftScalar .left)
  | "sse2.psll.q" => some (.shiftScalar .left)
  | "sse2.psrl.w" => some (.shiftScalar .logicalRight)
  | "sse2.psrl.d" => some (.shiftScalar .logicalRight)
  | "sse2.psrl.q" => some (.shiftScalar .logicalRight)
  | "sse2.psra.w" => some (.shiftScalar .arithmeticRight)
  | "sse2.psra.d" => some (.shiftScalar .arithmeticRight)
  | "sse2.packsswb.128" => some (.pack 16 true)
  | "sse2.packuswb.128" => some (.pack 16 false)
  | "sse2.packssdw.128" => some (.pack 32 true)
  | "avx2.pavg.b" => some (.avg)
  | "avx2.pavg.w" => some (.avg)
  | "avx2.pmulh.w" => some (.mulHigh)
  | "avx2.pmulhu.w" => some (.mulHigh)
  | "avx2.pmadd.wd" => some (.madWord)
  | "avx2.psad.bw" => some (.sad)
  | "avx2.psll.w" => some (.shiftScalar .left)
  | "avx2.psll.d" => some (.shiftScalar .left)
  | "avx2.psll.q" => some (.shiftScalar .left)
  | "avx2.psrl.w" => some (.shiftScalar .logicalRight)
  | "avx2.psrl.d" => some (.shiftScalar .logicalRight)
  | "avx2.psrl.q" => some (.shiftScalar .logicalRight)
  | "avx2.psra.w" => some (.shiftScalar .arithmeticRight)
  | "avx2.psra.d" => some (.shiftScalar .arithmeticRight)
  | "avx2.packsswb" => some (.pack 16 true)
  | "avx2.packuswb" => some (.pack 16 false)
  | "avx2.packssdw" => some (.pack 32 true)
  | "avx2.packusdw" => some (.pack 32 false)
  | "sse3.ldu.dq" => some (.unaligned)
  | "ssse3.pshuf.b.128" => some (.shuffle)
  | "ssse3.pmadd.ub.sw.128" => some (.madByte)
  | "ssse3.pmul.hr.sw.128" => some (.mulRound)
  | "ssse3.psign.b.128" => some (.sign)
  | "ssse3.psign.w.128" => some (.sign)
  | "ssse3.psign.d.128" => some (.sign)
  | "sse41.insertps" => some (.insert)
  | "sse41.packusdw" => some (.pack 32 false)
  | "sse41.dpps" => some (.dot)
  | "sse41.dppd" => some (.dot)
  | "sse41.phminposuw" => some (.minPosition)
  | "sse41.mpsadbw" => some (.multipleSad)
  | "sse41.ptestnzc" => some (.test false 2)
  | "avx.dp.ps.256" => some (.dot)
  | "avx.ldu.dq.256" => some (.unaligned)
  | "avx.ptestnzc.256" => some (.test false 2)
  | "avx.vzeroupper" => some (.nop)
  | "avx.vzeroall" => some (.nop)
  | "avx.vpermilvar.ps" => some (.permuteFloat false)
  | "avx.vpermilvar.ps.256" => some (.permuteFloat false)
  | "avx.vtestz.ps.256" => some (.test true 0)
  | "avx.vtestc.ps.256" => some (.test true 1)
  | "avx.vtestnzc.ps" => some (.test true 2)
  | "avx.vtestnzc.ps.256" => some (.test true 2)
  | "avx.vpermilvar.pd" => some (.permuteFloat true)
  | "avx.vpermilvar.pd.256" => some (.permuteFloat true)
  | "avx.vtestz.pd.256" => some (.test true 0)
  | "avx.vtestc.pd.256" => some (.test true 1)
  | "avx.vtestnzc.pd" => some (.test true 2)
  | "avx.vtestnzc.pd.256" => some (.test true 2)
  | "avx2.pmadd.ub.sw" => some (.madByte)
  | "avx2.mpsadbw" => some (.multipleSad)
  | "avx2.pmul.hr.sw" => some (.mulRound)
  | "avx2.permd" => some (.permute)
  | "avx2.permps" => some (.permute)
  | "avx2.pshuf.b" => some (.shuffle)
  | "avx2.psign.b" => some (.sign)
  | "avx2.psign.w" => some (.sign)
  | "avx2.psign.d" => some (.sign)
  | "avx2.psllv.d" => some (.shiftVector .left)
  | "avx2.psllv.d.256" => some (.shiftVector .left)
  | "avx2.psllv.q" => some (.shiftVector .left)
  | "avx2.psllv.q.256" => some (.shiftVector .left)
  | "avx2.psrlv.d" => some (.shiftVector .logicalRight)
  | "avx2.psrlv.d.256" => some (.shiftVector .logicalRight)
  | "avx2.psrlv.q" => some (.shiftVector .logicalRight)
  | "avx2.psrlv.q.256" => some (.shiftVector .logicalRight)
  | "avx2.psrav.d" => some (.shiftVector .arithmeticRight)
  | "avx2.psrav.d.256" => some (.shiftVector .arithmeticRight)
  | "avx2.gather.d.d" => some (.gather)
  | "avx2.gather.d.d.256" => some (.gather)
  | "avx2.gather.d.q" => some (.gather)
  | "avx2.gather.d.q.256" => some (.gather)
  | "avx2.gather.d.pd" => some (.gather)
  | "avx2.gather.d.pd.256" => some (.gather)
  | "avx2.gather.d.ps" => some (.gather)
  | "avx2.gather.d.ps.256" => some (.gather)
  | "avx2.gather.q.d" => some (.gather)
  | "avx2.gather.q.d.256" => some (.gather)
  | "avx2.gather.q.q" => some (.gather)
  | "avx2.gather.q.q.256" => some (.gather)
  | "avx2.gather.q.pd" => some (.gather)
  | "avx2.gather.q.pd.256" => some (.gather)
  | "avx2.gather.q.ps" => some (.gather)
  | "avx2.gather.q.ps.256" => some (.gather)
  | "avx512.pternlog.d.128" => some (.ternary)
  | "avx512.pternlog.d.256" => some (.ternary)
  | "avx512.pternlog.d.512" => some (.ternary)
  | "avx512.pternlog.q.128" => some (.ternary)
  | "avx512.pternlog.q.256" => some (.ternary)
  | "avx512.pternlog.q.512" => some (.ternary)
  | "avx512.psad.bw.512" => some (.sad)
  | "avx512.pmaddw.d.512" => some (.madWord)
  | "avx512.pmaddubs.w.512" => some (.madByte)
  | "avx512.permvar.si.512" => some (.permute)
  | "avx512.permvar.di.512" => some (.permute)
  | "avx512.permvar.qi.512" => some (.permute)
  | "avx512.permvar.qi.256" => some (.permute)
  | "avx512.permvar.qi.128" => some (.permute)
  | "avx512.vpermi2var.q.512" => some (.permute2)
  | "avx512.vpermi2var.qi.512" => some (.permute2)
  | "avx512.pshuf.b.512" => some (.shuffle)
  | "avx512.vpdpbusd.512" => some (.dotBytes)
  | "avx512.vpdpbusd.256" => some (.dotBytes)
  | "avx512.vpdpbusd.128" => some (.dotBytes)
  | "avx512.packsswb.512" => some (.pack 16 true)
  | "avx512.packuswb.512" => some (.pack 16 false)
  | "avx512.packssdw.512" => some (.pack 32 true)
  | "avx512.packusdw.512" => some (.pack 32 false)
  | "avx512.pavg.b.512" => some (.avg)
  | "avx512.pavg.w.512" => some (.avg)
  | _ => none

def vectorArity : VectorInstruction → Nat
  | .gather => 5 | .ternary => 4 | .permute2 | .dot | .multipleSad | .dotBytes | .insert => 3
  | .minPosition | .unaligned => 1 | .nop => 0 | _ => 2

def vectorDispatch [PointerProvenance P] (h : Hooks P S C V) (choice : C)
    (full name : String) (args : Array (OpTy P)) (dest : V) : M S Bool := do
  let some operation := vectorSpec name | return false
  if name.startsWith "avx512.pternlog" then
    feature h choice full "avx512f"
    unless name.endsWith ".512" do feature h choice full "avx512vl"
  else if name.startsWith "avx512.permvar.qi" then
    feature h choice full "avx512vbmi"
    unless name.endsWith "512" do feature h choice full "avx512vl"
  else if name == "avx512.vpermi2var.qi.512" then feature h choice full "avx512vbmi"
  else if name.startsWith "avx512.vpdpbusd" then
    feature h choice full "avx512vnni"
    unless name.endsWith ".512" do feature h choice full "avx512vl"
  else if ["avx512.psad.bw.512","avx512.pmaddw.d.512","avx512.packsswb.512","avx512.packuswb.512",
      "avx512.packssdw.512","avx512.packusdw.512","avx512.pavg.b.512","avx512.pavg.w.512"].contains name then
    feature h choice full "avx512bw"
  signature h choice full args (vectorArity operation)
  match operation with
  | .nop => pure ()
  | .unaligned =>
    let pointer ← scalarResult ((← read h choice (← arg args 0)).toPointer h.architecture.simd.target)
    let dest ← h.architecture.simd.forceAllocation choice dest
    let destPointer ← liftResult (h.architecture.simd.placePointer dest)
    h.memCopy choice pointer destPointer (h.architecture.simd.placeLayout dest).layout.size true
  | .minPosition => minPosition h choice (← arg args 0) dest
  | .ternary => ternary h choice (← arg args 0) (← arg args 1) (← arg args 2) (← arg args 3) dest
  | .gather => gather h choice (← arg args 0) (← arg args 1) (← arg args 2) (← arg args 3) (← arg args 4) dest
  | .permute2 => permute h choice (← arg args 0) (← arg args 1) (some (← arg args 2)) dest
  | .dot => dotProduct h choice (← arg args 0) (← arg args 1) (← arg args 2) dest
  | .multipleSad => multipleSadBytes h choice (← arg args 0) (← arg args 1) (← arg args 2) dest
  | .dotBytes => dotBytes h choice (← arg args 0) (← arg args 1) (← arg args 2) dest
  | .insert => insertPs h choice (← arg args 0) (← arg args 1) (← arg args 2) dest
  | .avg => wideBinary h choice true (← arg args 0) (← arg args 1) dest
  | .mulHigh => wideBinary h choice false (← arg args 0) (← arg args 1) dest
  | .madWord => multiplyAdd h choice false (← arg args 0) (← arg args 1) dest
  | .madByte => multiplyAdd h choice true (← arg args 0) (← arg args 1) dest
  | .mulRound => multiplyRound h choice (← arg args 0) (← arg args 1) dest
  | .sign => signVector h choice (← arg args 0) (← arg args 1) dest
  | .shuffle => shuffleBytes h choice (← arg args 0) (← arg args 1) dest
  | .sad => sadBytes h choice (← arg args 0) (← arg args 1) dest
  | .pack bits signed => pack h choice bits signed (← arg args 0) (← arg args 1) dest
  | .permute => permute h choice (← arg args 0) (← arg args 1) none dest
  | .shiftScalar op => shiftByScalar h choice (← arg args 0) (← arg args 1) dest op
  | .shiftVector op => shiftVector h choice (← arg args 0) (← arg args 1) dest op
  | .permuteFloat double => permuteFloat h choice double (← arg args 0) (← arg args 1) dest
  | .test high kind =>
    let (a,b) ← testBits h choice (← arg args 0) (← arg args 1) high
    let value := if kind == 0 then a else if kind == 1 then b else !a && !b
    write h choice (.fromScalarInt (.ofUInt32 (if value then 1 else 0))) dest
  return true

end Miri.Interpreter.IntrinsicX86
