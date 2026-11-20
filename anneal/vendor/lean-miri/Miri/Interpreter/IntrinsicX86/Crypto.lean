import Miri.Interpreter.IntrinsicX86.Strings
import Miri.Interpreter.IntrinsicX86.Aes
namespace Miri.Interpreter.IntrinsicX86
open Miri.ABI Miri.Memory Miri.MIR
open IntrinsicCrypto

/-- Constants transcribed from pinned math.rs::aes::SBOX. -/
def sbox : Array UInt8 := #[
  0x63, 0x7c, 0x77, 0x7b, 0xf2, 0x6b, 0x6f, 0xc5, 0x30, 0x01, 0x67, 0x2b, 0xfe, 0xd7, 0xab, 0x76, 0xca, 0x82, 0xc9, 0x7d, 0xfa, 0x59, 0x47, 0xf0, 0xad, 0xd4, 0xa2, 0xaf, 0x9c, 0xa4, 0x72, 0xc0, 0xb7, 0xfd, 0x93, 0x26, 0x36, 0x3f, 0xf7, 0xcc, 0x34, 0xa5, 0xe5, 0xf1, 0x71, 0xd8, 0x31, 0x15, 0x04, 0xc7, 0x23, 0xc3, 0x18, 0x96, 0x05, 0x9a, 0x07, 0x12, 0x80, 0xe2, 0xeb, 0x27, 0xb2, 0x75, 0x09, 0x83, 0x2c, 0x1a, 0x1b, 0x6e, 0x5a, 0xa0, 0x52, 0x3b, 0xd6, 0xb3, 0x29, 0xe3, 0x2f, 0x84, 0x53, 0xd1, 0x00, 0xed, 0x20, 0xfc, 0xb1, 0x5b, 0x6a, 0xcb, 0xbe, 0x39, 0x4a, 0x4c, 0x58, 0xcf, 0xd0, 0xef, 0xaa, 0xfb, 0x43, 0x4d, 0x33, 0x85, 0x45, 0xf9, 0x02, 0x7f, 0x50, 0x3c, 0x9f, 0xa8, 0x51, 0xa3, 0x40, 0x8f, 0x92, 0x9d, 0x38, 0xf5, 0xbc, 0xb6, 0xda, 0x21, 0x10, 0xff, 0xf3, 0xd2, 0xcd, 0x0c, 0x13, 0xec, 0x5f, 0x97, 0x44, 0x17, 0xc4, 0xa7, 0x7e, 0x3d, 0x64, 0x5d, 0x19, 0x73, 0x60, 0x81, 0x4f, 0xdc, 0x22, 0x2a, 0x90, 0x88, 0x46, 0xee, 0xb8, 0x14, 0xde, 0x5e, 0x0b, 0xdb, 0xe0, 0x32, 0x3a, 0x0a, 0x49, 0x06, 0x24, 0x5c, 0xc2, 0xd3, 0xac, 0x62, 0x91, 0x95, 0xe4, 0x79, 0xe7, 0xc8, 0x37, 0x6d, 0x8d, 0xd5, 0x4e, 0xa9, 0x6c, 0x56, 0xf4, 0xea, 0x65, 0x7a, 0xae, 0x08, 0xba, 0x78, 0x25, 0x2e, 0x1c, 0xa6, 0xb4, 0xc6, 0xe8, 0xdd, 0x74, 0x1f, 0x4b, 0xbd, 0x8b, 0x8a, 0x70, 0x3e, 0xb5, 0x66, 0x48, 0x03, 0xf6, 0x0e, 0x61, 0x35, 0x57, 0xb9, 0x86, 0xc1, 0x1d, 0x9e, 0xe1, 0xf8, 0x98, 0x11, 0x69, 0xd9, 0x8e, 0x94, 0x9b, 0x1e, 0x87, 0xe9, 0xce, 0x55, 0x28, 0xdf, 0x8c, 0xa1, 0x89, 0x0d, 0xbf, 0xe6, 0x42, 0x68, 0x41, 0x99, 0x2d, 0x0f, 0xb0, 0x54, 0xbb, 0x16]

def subWord (value : UInt32) : Except StepError UInt32 := do
  let mut result := 0
  for i in [:4] do
    let index := (value.toNat >>> (i*8)) &&& 255
    let some byte := sbox[index]? | throw (.invalidProgram "AES SBOX table assertion")
    result := result ||| (byte.toNat <<< (i*8))
  return UInt32.ofNat result

def aesKeygen (value : U128) (rcon : UInt8) : Except StepError U128 := do
  let a ← subWord (UInt32.ofNat (value.toNat >>> 32))
  let c ← subWord (UInt32.ofNat (value.toNat >>> 96))
  let rotate := fun (x : UInt32) => (x >>> 8) ||| (x <<< 24)
  let b := rotate a ^^^ UInt32.ofNat rcon.toNat
  let d := rotate c ^^^ UInt32.ofNat rcon.toNat
  pure (BitVec.ofNat 128 (a.toNat ||| (b.toNat <<< 32) ||| (c.toNat <<< 64) ||| (d.toNat <<< 96)))

def gfMultiply (left right : UInt8) : UInt8 := Id.run do
  let mut result : UInt32 := 0
  for i in [:8] do
    if left.toNat &&& (1 <<< i) != 0 then result := result ^^^ (UInt32.ofNat right.toNat <<< UInt32.ofNat i)
  for i in [8:15].toList.reverse do
    if result.toNat &&& (1 <<< i) != 0 then result := result ^^^ (0x11b <<< UInt32.ofNat (i-8))
  return UInt8.ofNat result.toNat

def gfInverse (value : UInt8) : UInt8 := Id.run do
  if value == 0 then return 0
  let mut y := gfMultiply value value
  let mut x := y
  for _ in [2:8] do
    x := gfMultiply x x
    y := gfMultiply x y
  return y

def gfni [PointerProvenance P] (h : Hooks P S C V) (choice : C) (full name : String)
    (args : Array (OpTy P)) (dest : V) : M S Bool := do
  feature h choice full "gfni"
  if name.endsWith ".256" then feature h choice full "avx"
  else if name.endsWith ".512" then feature h choice full "avx512f"
  let affine := ["vgf2p8affineqb.128","vgf2p8affineqb.256","vgf2p8affineqb.512"].contains name
  let inverse := ["vgf2p8affineinvqb.128","vgf2p8affineinvqb.256","vgf2p8affineinvqb.512"].contains name
  let multiply := ["vgf2p8mulb.128","vgf2p8mulb.256","vgf2p8mulb.512"].contains name
  unless affine || inverse || multiply do return false
  signature h choice full args (if multiply then 2 else 3)
  let (left,ln) ← projectRead h choice (← arg args 0)
  let (right,rn) ← projectRead h choice (← arg args 1)
  let (dest,n) ← projectWrite h choice dest
  if multiply then
    same ln rn
    same n rn
    for i in [:n.toNat] do
      let i := UInt64.ofNat i
      let left ← scalarResult ((← readScalarLane h choice left i).toUInt8)
      let right ← scalarResult ((← readScalarLane h choice right i).toUInt8)
      let dest ← h.architecture.simd.indexWrite choice dest i
      write h choice (.fromScalarInt (.ofUInt8 (gfMultiply left right))) dest
  else
    same n rn
    same n ln
    let imm ← scalarResult ((← read h choice (← arg args 2)).toUInt8)
    for chunk in [:((n.toNat+7)/8)] do
      let mut matrix : Array UInt8 := #[]
      for j in [:8] do
        matrix := matrix.push (← scalarResult ((← readScalarLane h choice right (UInt64.ofNat (chunk*8+j))).toUInt8))
      for j in [:8] do
        let index := UInt64.ofNat (chunk*8+j)
        let left ← scalarResult ((← readScalarLane h choice left index).toUInt8)
        let left := if inverse then gfInverse left else left
        let mut result : UInt8 := 0
        for bit in [:8] do
          let some row := matrix[bit]? | invalid "GFNI matrix index assertion"
          let mut b := row &&& left
          b := (b &&& (15 : UInt8)) ^^^ (b >>> (4 : UInt8))
          b := (b &&& (3 : UInt8)) ^^^ (b >>> (2 : UInt8))
          b := (b &&& (1 : UInt8)) ^^^ (b >>> (1 : UInt8))
          result := result ||| (b <<< UInt8.ofNat (7-bit))
        let dest ← h.architecture.simd.indexWrite choice dest index
        write h choice (.fromScalarInt (.ofUInt8 (result ^^^ imm))) dest
  return true

def aesni [PointerProvenance P] (h : Hooks P S C V) (choice : C) (full name : String)
    (args : Array (OpTy P)) (dest : V) : M S Bool := do
  feature h choice full "aes"
  if name == "aesimc" || name == "aeskeygenassist" then
    signature h choice full args (if name == "aesimc" then 1 else 2)
    let layout ← h.integerLayout choice 128 false
    let source ← h.transmuteRead choice (← arg args 0) layout
    let dest ← h.transmuteWrite choice dest layout
    if name == "aesimc" then
      let value ← scalarResult ((← read h choice source).toUInt128)
      write h choice (← fromUInt (Aes.mixColumns true value).toNat (Size.ofBytes 16)) dest
    else
      let rcon ← scalarResult ((← read h choice (← arg args 1)).toUInt8)
      let value ← scalarResult ((← read h choice source).toUInt128)
      let result ← liftResult (aesKeygen value rcon)
      write h choice (← fromUInt result.toNat (Size.ofBytes 16)) dest
  else
    let decrypt := ["aesdec","aesdec.256","aesdec.512","aesdeclast","aesdeclast.256","aesdeclast.512"].contains name
    let encrypt := ["aesenc","aesenc.256","aesenc.512","aesenclast","aesenclast.256","aesenclast.512"].contains name
    unless decrypt || encrypt do return false
    signature h choice full args 2
    let source ← arg args 0
    let key ← arg args 1
    let size := (h.architecture.simd.placeLayout dest).layout.size
    unless size == source.layout.layout.size do invalid "AES state size differs"
    unless size == key.layout.layout.size do invalid "AES key size differs"
    unless size.bytes % 16 == 0 do invalid "AES size is not multiple of 16"
    let n := size.bytes/16
    let layout ← h.integerLayout choice 128 false
    let array ← h.arrayLayout choice layout.ty n
    let source ← h.transmuteRead choice source array
    let key ← h.transmuteRead choice key array
    let dest ← h.transmuteWrite choice dest array
    let last := name.startsWith "aesenclast" || name.startsWith "aesdeclast"
    for i in [:n.toNat] do
      let i := UInt64.ofNat i
      let source ← scalarResult ((← readScalarLane h choice source i).toUInt128)
      let key ← scalarResult ((← readScalarLane h choice key i).toUInt128)
      let dest ← h.architecture.simd.indexWrite choice dest i
      let result ← if last then do
        let round := Aes.round decrypt source 0
        let undone := Aes.mixColumns (!decrypt) round
        pure (undone ^^^ key)
        else pure (Aes.round decrypt source key)
      write h choice (← fromUInt result.toNat (Size.ofBytes 16)) dest
  return true

def pclmul [PointerProvenance P] (h : Hooks P S C V) (choice : C)
    (left right immediate : OpTy P) (dest : V) (n : UInt64) : M S Unit := do
  unless left.layout == right.layout do invalid "PCLMUL layouts differ"
  unless left.layout.layout.size == (h.architecture.simd.placeLayout dest).layout.size do invalid "PCLMUL sizes differ"
  unless n == 2 || n == 4 || n == 8 do invalid "PCLMUL length assertion"
  let sourceTy ← h.integerLayout choice 64 false
  let sourceLayout ← h.arrayLayout choice sourceTy.ty n
  let destTy ← h.integerLayout choice 128 false
  let destLayout ← h.arrayLayout choice destTy.ty (n/2)
  let left ← h.transmuteRead choice left sourceLayout
  let right ← h.transmuteRead choice right sourceLayout
  let dest ← h.transmuteWrite choice dest destLayout
  let imm ← scalarResult ((← read h choice immediate).toUInt8)
  for i in [:n.toNat/2] do
    let left ← scalarResult ((← readScalarLane h choice left (UInt64.ofNat (i*2 + if imm &&& 1 == 0 then 0 else 1))).toUInt64)
    let right ← scalarResult ((← readScalarLane h choice right (UInt64.ofNat (i*2 + if imm &&& 16 == 0 then 0 else 1))).toUInt64)
    let result := carryless64 left right
    write h choice (← fromUInt result.toNat (Size.ofBytes 16)) (← h.architecture.simd.indexWrite choice dest (UInt64.ofNat i))

def readReverseQuad [PointerProvenance P] (h : Hooks P S C V) (choice : C) (source : OpTy P) : M S (Quad UInt32) := do
  let d ← scalarResult ((← readScalarLane h choice source 0).toUInt32)
  let c ← scalarResult ((← readScalarLane h choice source 1).toUInt32)
  let b ← scalarResult ((← readScalarLane h choice source 2).toUInt32)
  let a ← scalarResult ((← readScalarLane h choice source 3).toUInt32)
  pure ⟨a,b,c,d⟩

def sha [PointerProvenance P] (h : Hooks P S C V) (choice : C) (full name : String)
    (args : Array (OpTy P)) (dest : V) : M S Bool := do
  feature h choice full "sha"
  unless ["256rnds2","256msg1","256msg2"].contains name do return false
  let rounds := name == "256rnds2"
  signature h choice full args (if rounds then 3 else 2)
  let (a,an) ← projectRead h choice (← arg args 0)
  let (b,bn) ← projectRead h choice (← arg args 1)
  let k ← if rounds then pure (some (← projectRead h choice (← arg args 2))) else pure none
  let (dest,n) ← projectWrite h choice dest
  same an 4
  same bn 4
  if let some (_,kn) := k then same kn 4
  same n 4
  let a ← readReverseQuad h choice a
  let b ← readReverseQuad h choice b
  let result : Quad UInt32 ← if rounds then do
    let some (k,_) := k | invalid "SHA rounds key missing"
    let k ← readReverseQuad h choice k
    let first := shaRound ⟨b.a,b.b,a.a,a.b⟩ ⟨b.c,b.d,a.c,a.d⟩ k.d
    let second := shaRound first.1 first.2 k.c
    pure ⟨second.1.a,second.1.b,second.2.a,second.2.b⟩
    else if name == "256msg1" then pure ⟨a.a+sigma0 b.d,a.b+sigma0 a.a,a.c+sigma0 a.b,a.d+sigma0 a.c⟩
    else
      let w16 := a.d+sigma1 b.b
      let w17 := a.c+sigma1 b.a
      let w18 := a.b+sigma1 w16
      let w19 := a.a+sigma1 w17
      pure ⟨w19,w18,w17,w16⟩
  for (i,value) in [(0,result.d),(1,result.c),(2,result.b),(3,result.a)] do
    write h choice (.fromScalarInt (.ofUInt32 value)) (← h.architecture.simd.indexWrite choice dest i)
  return true

end Miri.Interpreter.IntrinsicX86
