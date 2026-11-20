import Miri.Interpreter.IntrinsicX86.DispatchVector

/-! Connected pinned x86 architecture intrinsic dispatcher. All recognized
portable arms use concrete helpers; compiler/host-sqrt queries remain explicit. -/
namespace Miri.Interpreter.IntrinsicX86
open Miri.ABI Miri.Memory Miri.MIR

def crcDispatch [PointerProvenance P] (h : Hooks P S C V) (choice : C) (full name : String)
    (args : Array (OpTy P)) (dest : V) : M S Bool := do
  let bits ← match name with
    | "crc32.32.8" => pure 8 | "crc32.32.16" => pure 16
    | "crc32.32.32" => pure 32 | "crc32.64.64" => pure 64 | _ => return false
  if bits == 64 && !h.x86_64 then return false
  signature h choice full args 2
  let a ← read h choice (← arg args 0)
  let b ← read h choice (← arg args 1)
  let a ← if bits == 64 then do pure (UInt32.ofNat (← scalarResult a.toUInt64).toNat)
    else scalarResult a.toUInt32
  let data ← scalarResult (b.toUInt (Size.fromBits (UInt64.ofNat bits)))
  let result ← liftResult (IntrinsicCrypto.crc32 a (UInt64.ofNat data.toNat) bits 0x11EDC6F41)
  write h choice (← fromUInt result.toNat (Size.ofBytes (if bits == 64 then 8 else 4))) dest
  return true

/-- Source namespace routing is distinct from name recognition: unconditional
ISA checks of each sub-dispatcher also run for unknown names in that namespace. -/
def eval [PointerProvenance P] (h : Hooks P S C V) (choice : C)
    (full : String) (args : Array (OpTy P)) (dest : V) : M S Bool := do
  unless full.startsWith "llvm.x86." do invalid "x86 intrinsic prefix assertion"
  let name := (full.drop 9).toString
  if ["addcarry.32","addcarry.64","subborrow.32","subborrow.64"].contains name then
    if name.endsWith "64" && !h.x86_64 then return false
    signature h choice full args 3
    let op := if name.startsWith "add" then BinOp.AddWithOverflow else .SubWithOverflow
    let (sum,carryOut) ← carry h choice (← arg args 0) (← arg args 1) (← arg args 2) op
    let carryDest ← h.architecture.simd.fieldWrite choice dest 0
    write h choice carryOut carryDest
    let sumDest ← h.architecture.simd.fieldWrite choice dest 1
    h.architecture.simd.writeImmediate choice sum.imm sumDest
    return true
  if name == "sse2.pause" then
    signature h choice full args 0
    if h.sse2Enabled then h.yieldThread choice
    return true
  if ["pclmulqdq","pclmulqdq.256","pclmulqdq.512"].contains name then
    feature h choice full "pclmulqdq"
    let n ← if name.endsWith ".256" then do feature h choice full "vpclmulqdq"; pure 4
      else if name.endsWith ".512" then do
        feature h choice full "vpclmulqdq"
        feature h choice full "avx512f"
        pure 8
      else pure 2
    signature h choice full args 3
    pclmul h choice (← arg args 0) (← arg args 1) (← arg args 2) dest n
    return true
  if name.startsWith "bmi." then return ← bmi h choice full ((name.drop 4).toString) args dest
  if name.startsWith "vgf2p8affine" || name.startsWith "vgf2p8mulb" then return ← gfni h choice full name args dest
  if name.startsWith "sha" then return ← sha h choice full ((name.drop 3).toString) args dest
  if name.startsWith "aesni." then return ← aesni h choice full ((name.drop 6).toString) args dest
  let group ← if name.startsWith "sse." then pure (some "sse")
    else if name.startsWith "sse2." then pure (some "sse2")
    else if name.startsWith "sse3." then pure (some "sse3")
    else if name.startsWith "ssse3." then pure (some "ssse3")
    else if name.startsWith "sse41." then pure (some "sse4.1")
    else if name.startsWith "sse42." then pure (some "sse4.2")
    else if name.startsWith "avx." then pure (some "avx")
    else if name.startsWith "avx2." then pure (some "avx2")
    else if name.startsWith "avx512." then pure none
    else return false
  if let some group := group then feature h choice full group
  if name.startsWith "sse42." then
    let suffix := (name.drop 6).toString
    if ← stringDispatch h choice full suffix args dest then return true
    return ← crcDispatch h choice full suffix args dest
  if ← floatDispatch h choice full name args dest then return true
  vectorDispatch h choice full name args dest

/-- Install the concrete complete x86 family in the architecture dispatcher;
portable LLVM/AArch64/LoongArch behavior retains its existing implementation. -/
def architectureDispatch (h : Hooks P S C V)
    (base : IntrinsicArchitecture.DispatchHooks P S C V) [PointerProvenance P] :
    IntrinsicArchitecture.DispatchHooks P S C V :=
  { base with x86 := eval h }

end Miri.Interpreter.IntrinsicX86
