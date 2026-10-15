import Sail.Common

section VectorConversionTests

open Sail

def valueBytes : Vector (BitVec 8) 8 := ⟨#[
  BitVec.ofNat 8 0x1,
  BitVec.ofNat 8 0x2,
  BitVec.ofNat 8 0x3,
  BitVec.ofNat 8 0x4,
  BitVec.ofNat 8 0x5,
  BitVec.ofNat 8 0x6,
  BitVec.ofNat 8 0x7,
  BitVec.ofNat 8 0x8,
  ], rfl⟩
def valueVec : BitVec (8*8) := vecbytes_to_bitvec valueBytes
#guard valueVec.toHex == "0807060504030201"
#guard (bitvec_to_vecbytes valueVec) == valueBytes

def myVecBool : Vector Bool 8 := ⟨#[
  true, true, false, false, -- 0x3
  false, false, false, true -- 0x8
  ], rfl⟩
def myBitVec : BitVec 8 := vecbool_to_bitvec myVecBool
#guard myBitVec.toHex == "83"
#guard (bitvec_to_vecbool myBitVec) == myVecBool

end VectorConversionTests
