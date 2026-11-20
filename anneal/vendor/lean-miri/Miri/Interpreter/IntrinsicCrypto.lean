import Miri.Interpreter.IntrinsicSimd

/-! Finite-width polynomial and SHA256 math from pinned intrinsics/math.rs
and aarch64.rs. No host cryptographic approximation is used. -/
namespace Miri.Interpreter.IntrinsicCrypto
open Miri.ABI

structure Quad (A : Type) where
  a : A
  b : A
  c : A
  d : A
  deriving DecidableEq, Repr

private def reverseBits (width value : Nat) : Nat :=
  (List.range width).foldl (fun result i => result * 2 + ((value >>> i) &&& 1)) 0

/-- Descending polynomial degrees reproduce the source leading-zero loop. -/
def crc32 (crc : UInt32) (data : UInt64) (bits : Nat) (polynomial : U128) :
    Except StepError UInt32 := do
  if bits > 64 || (bits != 64 && data.toNat >= 2^bits) then
    throw (.invalidProgram "crc32 data is larger than its bit size")
  if polynomial.toNat == 0 then throw (.invalidProgram "zero CRC polynomial")
  let c := reverseBits 32 crc.toNat
  let v := reverseBits 64 data.toNat >>> (64-bits)
  let mut dividend := BitVec.ofNat 128 ((c <<< bits) ^^^ (v <<< 32))
  let degree := polynomial.toNat.log2
  for i in (List.range 128).reverse do
    if i >= degree && dividend.getLsbD i then
      dividend := dividend ^^^ (polynomial <<< (i-degree))
  if dividend.toNat >= 2^32 then throw (.invalidProgram "CRC remainder exceeds u32")
  return UInt32.ofNat (reverseBits 32 dividend.toNat)

def carryless64 (left right : UInt64) : U128 :=
  (List.range 64).foldl (fun result i =>
    if ((left.toNat >>> i) &&& 1) != 0 then result ^^^ (BitVec.ofNat 128 right.toNat <<< i) else result) 0

private def rotr (x : UInt32) (n : UInt32) : UInt32 := (x >>> n) ||| (x <<< (32-n))
def sigma0 (x : UInt32) : UInt32 := rotr x 7 ^^^ rotr x 18 ^^^ (x >>> 3)
def sigma1 (x : UInt32) : UInt32 := rotr x 17 ^^^ rotr x 19 ^^^ (x >>> 10)

def shaRound (abcd efgh : Quad UInt32) (wk : UInt32) : Quad UInt32 × Quad UInt32 :=
  let s1 := rotr efgh.a 6 ^^^ rotr efgh.a 11 ^^^ rotr efgh.a 25
  let ch := (efgh.a &&& efgh.b) ^^^ ((~~~efgh.a) &&& efgh.c)
  let t1 := s1 + ch + wk + efgh.d
  let s0 := rotr abcd.a 2 ^^^ rotr abcd.a 13 ^^^ rotr abcd.a 22
  let maj := (abcd.a &&& abcd.b) ^^^ (abcd.a &&& abcd.c) ^^^ (abcd.b &&& abcd.c)
  let t2 := s0 + maj
  (⟨t1+t2, abcd.a, abcd.b, abcd.c⟩, ⟨abcd.d+t1, efgh.a, efgh.b, efgh.c⟩)

def shaHash (abcd efgh wk : Quad UInt32) : Quad UInt32 × Quad UInt32 :=
  [wk.a, wk.b, wk.c, wk.d].foldl (fun (a,e) k => shaRound a e k) (abcd,efgh)

def shaSu0 (a b : Quad UInt32) : Quad UInt32 :=
  ⟨a.a + sigma0 a.b, a.b + sigma0 a.c, a.c + sigma0 a.d, a.d + sigma0 b.a⟩

def shaSu1 (a b c : Quad UInt32) : Quad UInt32 :=
  let r0 := a.a + b.b + sigma1 c.c
  let r1 := a.b + b.c + sigma1 c.d
  let r2 := a.c + b.d + sigma1 r0
  let r3 := a.d + c.a + sigma1 r1
  ⟨r0,r1,r2,r3⟩

end Miri.Interpreter.IntrinsicCrypto
