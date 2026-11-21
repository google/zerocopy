-- Copyright 2026 The Fuchsia Authors
--
-- Licensed under a BSD-style license <LICENSE-BSD>, Apache License, Version 2.0
-- <LICENSE-APACHE or https://www.apache.org/licenses/LICENSE-2.0>, or the MIT
-- license <LICENSE-MIT or https://opensource.org/licenses/MIT>, at your option.
-- This file may not be copied, modified, or distributed except according to
-- those terms.

prelude
import Init.Core
import Init.Data.BitVec.Basic
import Init.Data.BitVec.Lemmas
import Init.Data.List.Basic
import Init.Data.Nat.Basic
import NeonTriangulationCore

/-!
# `NeonTriangulation24`

Completion shard (`p16..p25`: across-vector reductions `UADDLV`/`UMAXV`/`UMINV`
with `FMOV` scalar writeback, 128-bit & 64-bit `REV64` upper-64 zeroing, `EXT`,
destructive `BSL`, `CNT`, carry-less `PMULL`/`PMULL64` GPR-pair `X1:X0`,
`AESE`/`AESMC`, `SHA512H`/`SHA512SU0`, and 64-bit Castagnoli `CRC32CX` with `W0`
upper-32 zeroing), importing `NeonTriangulationCore` (`p01..p15` + 4 UB and
cross-ISA crypto asymmetry theorems) for all 34 compiled `.o` functions.
-/

namespace NeonTriangulation24

open VendorArm64Ref WordArm64

-- 20. `p16_vaddlvq_u8` (3-step `uaddlv h0, v0.16b ; fmov w0, s0 ; ret`, bridged to `IntrinsicAarch64Ext`)
theorem triangulate_p16_vaddlvq_u8 (a : BitVec 128) (sp lr : BitVec 64) (mem : ByteMem) :
    TriangulatedGp64 (liftExtU16_zext64 "llvm.aarch64.neon.uaddlv.i32.v16i8" [.b128 a])
      (spec_p16 a) p16Words 3 (mkCallVec a 0#128 0#128 sp lr mem) lr := by
  have hEv : IntrinsicAarch64Ext.evalAarch64Ext "llvm.aarch64.neon.uaddlv.i32.v16i8" [.b128 a] =
      some (.ok (.b32 (BitVec.ofNat 32 (uaddlvLoop 16 8 a)))) := rfl
  have hMiri : liftExtU16_zext64 "llvm.aarch64.neon.uaddlv.i32.v16i8" [.b128 a] = .ok (spec_p16 a) := by
    unfold liftExtU16_zext64 spec_p16
    rw [hEv]
    dsimp only []
    apply congrArg Except.ok
    apply BitVec.eq_of_toNat_eq
    rw [BitVec.toNat_setWidth, BitVec.extractLsb'_toNat, BitVec.toNat_ofNat,
        BitVec.toNat_setWidth, BitVec.toNat_ofNat, Nat.shiftRight_zero,
        Nat.mod_mod_of_dvd _ (by decide : 2 ^ 16 ∣ 2 ^ 32)]
  refine mkTriGp64_3 hMiri rfl rfl rfl ?_
  change (BitVec.extractLsb' 0 32 ((BitVec.extractLsb' 0 32 ((BitVec.ofNat 16 (uaddlvLoop 16 8 a)).zeroExtend 128)).zeroExtend 64)).zeroExtend 64 =
         (BitVec.ofNat 16 (uaddlvLoop 16 8 a)).zeroExtend 64
  rw [extract32_zeroExtend128_16]
  apply BitVec.eq_of_toNat_eq
  rw [BitVec.toNat_setWidth, BitVec.extractLsb'_toNat, BitVec.toNat_setWidth, Nat.shiftRight_zero]
  have h16 : (BitVec.ofNat 16 (uaddlvLoop 16 8 a)).toNat < 2 ^ 16 := (BitVec.ofNat 16 _).isLt
  have h64 : (BitVec.ofNat 16 (uaddlvLoop 16 8 a)).toNat < 2 ^ 64 := Nat.lt_trans h16 (by decide)
  have h32 : (BitVec.ofNat 16 (uaddlvLoop 16 8 a)).toNat < 2 ^ 32 := Nat.lt_trans h16 (by decide)
  rw [Nat.mod_eq_of_lt h64, Nat.mod_eq_of_lt h32, Nat.mod_eq_of_lt h64]

-- 21. `p17_vmaxvq_u8` (3-step `umaxv b0, v0.16b ; fmov w0, s0 ; ret`, bridged to `IntrinsicAarch64Ext`)
theorem triangulate_p17_vmaxvq_u8 (a : BitVec 128) (sp lr : BitVec 64) (mem : ByteMem) :
    TriangulatedGp64 (liftExtU8_zext64 "llvm.aarch64.neon.umaxv.i8.v16i8" [.b128 a])
      (spec_p17 a) p17Words 3 (mkCallVec a 0#128 0#128 sp lr mem) lr := by
  refine mkTriGp64_3 rfl rfl rfl rfl ?_
  change (BitVec.extractLsb' 0 32 ((BitVec.extractLsb' 0 32 ((BitVec.ofNat 8 (umaxvLoop 16 8 a)).zeroExtend 128)).zeroExtend 64)).zeroExtend 64 =
         (BitVec.ofNat 8 (umaxvLoop 16 8 a)).zeroExtend 64
  rw [extract32_zeroExtend128_8]
  apply BitVec.eq_of_toNat_eq
  rw [BitVec.toNat_setWidth, BitVec.extractLsb'_toNat, BitVec.toNat_setWidth, Nat.shiftRight_zero]
  have h8  : (BitVec.ofNat 8 (umaxvLoop 16 8 a)).toNat < 2 ^ 8  := (BitVec.ofNat 8 _).isLt
  have h64 : (BitVec.ofNat 8 (umaxvLoop 16 8 a)).toNat < 2 ^ 64 := Nat.lt_trans h8 (by decide)
  have h32 : (BitVec.ofNat 8 (umaxvLoop 16 8 a)).toNat < 2 ^ 32 := Nat.lt_trans h8 (by decide)
  rw [Nat.mod_eq_of_lt h64, Nat.mod_eq_of_lt h32, Nat.mod_eq_of_lt h64]

-- 22. `p17b_vminvq_u8` (3-step `uminv b0, v0.16b ; fmov w0, s0 ; ret`, bridged to `IntrinsicAarch64Ext`)
theorem triangulate_p17b_vminvq_u8 (a : BitVec 128) (sp lr : BitVec 64) (mem : ByteMem) :
    TriangulatedGp64 (liftExtU8_zext64 "llvm.aarch64.neon.uminv.i8.v16i8" [.b128 a])
      (spec_p17b a) p17bWords 3 (mkCallVec a 0#128 0#128 sp lr mem) lr := by
  refine mkTriGp64_3 rfl rfl rfl rfl ?_
  change (BitVec.extractLsb' 0 32 ((BitVec.extractLsb' 0 32 ((BitVec.ofNat 8 (uminvLoop 16 8 a)).zeroExtend 128)).zeroExtend 64)).zeroExtend 64 =
         (BitVec.ofNat 8 (uminvLoop 16 8 a)).zeroExtend 64
  rw [extract32_zeroExtend128_8]
  apply BitVec.eq_of_toNat_eq
  rw [BitVec.toNat_setWidth, BitVec.extractLsb'_toNat, BitVec.toNat_setWidth, Nat.shiftRight_zero]
  have h8  : (BitVec.ofNat 8 (uminvLoop 16 8 a)).toNat < 2 ^ 8  := (BitVec.ofNat 8 _).isLt
  have h64 : (BitVec.ofNat 8 (uminvLoop 16 8 a)).toNat < 2 ^ 64 := Nat.lt_trans h8 (by decide)
  have h32 : (BitVec.ofNat 8 (uminvLoop 16 8 a)).toNat < 2 ^ 32 := Nat.lt_trans h8 (by decide)
  rw [Nat.mod_eq_of_lt h64, Nat.mod_eq_of_lt h32, Nat.mod_eq_of_lt h64]

-- 23. `p18_vrev64q_u8` (`rev64 v0.16b, v0.16b`)
theorem triangulate_p18_vrev64q_u8 (a : BitVec 128) (sp lr : BitVec 64) (mem : ByteMem) :
    TriangulatedVec128 (.ok (spec_p18 a)) (spec_p18 a) p18Words 2 (mkCallVec a 0#128 0#128 sp lr mem) lr :=
  mkTriVec128Fast rfl rfl rfl

-- 24. `p18b_vrev64_u8` (64-bit `rev64 v0.8b, v0.8b` with `V0[127:64]` zeroing!)
theorem triangulate_p18b_vrev64_u8 (a : BitVec 128) (sp lr : BitVec 64) (mem : ByteMem) :
    TriangulatedVec128 (.ok (spec_p18b a)) (spec_p18b a) p18bWords 2 (mkCallVec a 0#128 0#128 sp lr mem) lr :=
  mkTriVec128Fast rfl rfl rfl

-- 25. `p19_vextq_u8_5` (`ext v0.16b, v0.16b, v1.16b, #5`)
theorem triangulate_p19_vextq_u8_5 (a b : BitVec 128) (sp lr : BitVec 64) (mem : ByteMem) :
    TriangulatedVec128 (.ok (spec_p19 a b)) (spec_p19 a b) p19Words 2 (mkCallVec a b 0#128 sp lr mem) lr :=
  mkTriVec128Fast rfl rfl rfl

-- 26. `p20_vbslq_u8` (`bsl v0.16b, v1.16b, v2.16b`: destructive `Rd = v0 = mask`)
theorem triangulate_p20_vbslq_u8 (mask a b : BitVec 128) (sp lr : BitVec 64) (mem : ByteMem) :
    TriangulatedVec128 (.ok (spec_p20 mask a b)) (spec_p20 mask a b) p20Words 2 (mkCallVec mask a b sp lr mem) lr :=
  mkTriVec128Fast rfl rfl rfl

-- 27. `p21_vcntq_u8` (`cnt v0.16b, v0.16b`)
theorem triangulate_p21_vcntq_u8 (a : BitVec 128) (sp lr : BitVec 64) (mem : ByteMem) :
    TriangulatedVec128 (.ok (spec_p21 a)) (spec_p21 a) p21Words 2 (mkCallVec a 0#128 0#128 sp lr mem) lr :=
  mkTriVec128Fast rfl rfl rfl

theorem ext_packHalfs128_eq (f g : Nat → BitVec 16)
    (h0 : f 0 = g 0) (h1 : f 1 = g 1) (h2 : f 2 = g 2) (h3 : f 3 = g 3)
    (h4 : f 4 = g 4) (h5 : f 5 = g 5) (h6 : f 6 = g 6) (h7 : f 7 = g 7) :
    IntrinsicAarch64Ext.packHalfs128 f = packHalfs128 g := by
  unfold IntrinsicAarch64Ext.packHalfs128 packHalfs128
  rw [h0, h1, h2, h3, h4, h5, h6, h7]

theorem ext_pmullByte_eq (a8 b8 : BitVec 8) :
    IntrinsicAarch64Ext.pmullByte a8 b8 = pmullByte a8 b8 := rfl

-- 28. `p22_vmull_p8` (`pmull v0.8h, v0.8b, v1.8b`, bridged to `IntrinsicAarch64Ext`)
theorem triangulate_p22_vmull_p8 (a b : BitVec 128) (sp lr : BitVec 64) (mem : ByteMem) :
    TriangulatedVec128
      (liftExt128 "llvm.aarch64.neon.pmull.v8i16" [.b64 (BitVec.extractLsb' 0 64 a), .b64 (BitVec.extractLsb' 0 64 b)])
      (spec_p22 a b) p22Words 2 (mkCallVec a b 0#128 sp lr mem) lr := by
  have hEv : IntrinsicAarch64Ext.evalAarch64Ext "llvm.aarch64.neon.pmull.v8i16"
      [.b64 (BitVec.extractLsb' 0 64 a), .b64 (BitVec.extractLsb' 0 64 b)] =
      some (.ok (.b128 (IntrinsicAarch64Ext.pmull_v8i16 (BitVec.extractLsb' 0 64 a) (BitVec.extractLsb' 0 64 b)))) := rfl
  have hMiri : liftExt128 "llvm.aarch64.neon.pmull.v8i16"
      [.b64 (BitVec.extractLsb' 0 64 a), .b64 (BitVec.extractLsb' 0 64 b)] = .ok (spec_p22 a b) := by
    unfold liftExt128 spec_p22
    rw [hEv]
    dsimp only [IntrinsicAarch64Ext.pmull_v8i16]
    apply congrArg Except.ok
    have lane (k : Nat) (hk : k * 8 + 8 <= 64) :
        IntrinsicAarch64Ext.pmullByte (IntrinsicAarch64Ext.getByte64 (BitVec.extractLsb' 0 64 a) k)
          (IntrinsicAarch64Ext.getByte64 (BitVec.extractLsb' 0 64 b) k) =
        pmullByte (getByte128 a k) (getByte128 b k) := by
      rw [ext_pmullByte_eq, getByte64_extract0 a k hk, getByte64_extract0 b k hk]
    exact ext_packHalfs128_eq _ _
      (lane 0 (by decide)) (lane 1 (by decide)) (lane 2 (by decide)) (lane 3 (by decide))
      (lane 4 (by decide)) (lane 5 (by decide)) (lane 6 (by decide)) (lane 7 (by decide))
  exact mkTriVec128Fast hMiri rfl rfl

-- 29. `p22b_vmull_p64` (6-step `fmov d0,x1 ; fmov d1,x0 ; pmull v0.1q,v1.1d,v0.1d ; mov x1,v0.d[1] ; fmov x0,d0 ; ret`)
theorem triangulate_p22b_vmull_p64 (a b : BitVec 64) (sp lr : BitVec 64) (mem : ByteMem) :
    TriangulatedGpPair128
      (liftExt128 "llvm.aarch64.neon.pmull64" [.b64 a, .b64 b])
      (spec_p22b a b) p22bWords 6 (mkCallGp a b sp lr mem) lr := by
  refine mkTriGpPair128_6
    (ins0 := .fmovGpToVec .x64 0#5 1#5)
    (ins1 := .fmovGpToVec .x64 1#5 0#5)
    (ins2 := .neonPmull false .e64 0#5 1#5 0#5)
    (ins3 := .neonUmov .e64 1#5 0#5 1)
    (ins4 := .fmovVecToGp .x64 0#5 0#5)
    (ins5 := .ret reg30)
    rfl rfl rfl rfl rfl rfl rfl ?_
  have hb0  : (0#5 == reg31) = false := rfl
  have hb1  : (1#5 == reg31) = false := rfl
  have hb30 : (reg30 == reg31) = false := rfl
  have h10  : (1#5 == (0#5 : Reg5)) = false := rfl
  have h01  : (0#5 == (1#5 : Reg5)) = false := rfl
  have h00  : (0#5 == (0#5 : Reg5)) = true  := rfl
  have h11  : (1#5 == (1#5 : Reg5)) = true  := rfl
  have hm2  : 1 % 2 = 1 := rfl
  simp only [execInstr, execScalarInstr, execNeonInstr, mkCallGp,
             readXzr, writeXzr, readVec, writeVec, maskWidth, getDword128, spec_p22b,
             hb0, hb1, hb30, h10, h01, h00, h11, hm2,
             Bool.false_eq_true, ↓reduceIte, Nat.zero_mul, Nat.one_mul,
             extract64_zeroExtend128_64, concat_hi64_lo64]

-- 30. `p23_vaeseq_u8` (`aese v0.16b, v1.16b`, bridged to `IntrinsicAarch64Ext`)
theorem triangulate_p23_vaeseq_u8 (data key : BitVec 128) (sp lr : BitVec 64) (mem : ByteMem) :
    TriangulatedVec128 (liftExt128 "llvm.aarch64.crypto.aese" [.b128 data, .b128 key])
      (spec_p23 data key) p23Words 2 (mkCallVec data key 0#128 sp lr mem) lr :=
  mkTriVec128Fast (congrArg Except.ok (ext_aese128_eq data key)) rfl rfl

-- 31. `p23b_vaesmcq_u8` (`aesmc v0.16b, v0.16b`, bridged to `IntrinsicAarch64Ext`)
theorem triangulate_p23b_vaesmcq_u8 (data : BitVec 128) (sp lr : BitVec 64) (mem : ByteMem) :
    TriangulatedVec128 (liftExt128 "llvm.aarch64.crypto.aesmc" [.b128 data])
      (spec_p23b data) p23bWords 2 (mkCallVec data 0#128 0#128 sp lr mem) lr :=
  mkTriVec128Fast (congrArg Except.ok (ext_aesmc128_eq data)) rfl rfl

-- 32. `p24_vsha512hq_u64` (`sha512h q0, q1, v2.2d`, bridged to `IntrinsicAarch64Ext`)
theorem triangulate_p24_vsha512hq_u64 (a b c : BitVec 128) (sp lr : BitVec 64) (mem : ByteMem) :
    TriangulatedVec128 (liftExt128 "llvm.aarch64.crypto.sha512h" [.b128 a, .b128 b, .b128 c])
      (spec_p24 a b c) p24Words 2 (mkCallVec a b c sp lr mem) lr :=
  mkTriVec128Fast rfl rfl rfl

-- 33. `p24b_vsha512su0q_u64` (`sha512su0 v0.2d, v1.2d`, bridged to `IntrinsicAarch64Ext`)
theorem triangulate_p24b_vsha512su0q_u64 (a b : BitVec 128) (sp lr : BitVec 64) (mem : ByteMem) :
    TriangulatedVec128 (liftExt128 "llvm.aarch64.crypto.sha512su0" [.b128 a, .b128 b])
      (spec_p24b a b) p24bWords 2 (mkCallVec a b 0#128 sp lr mem) lr :=
  mkTriVec128Fast rfl rfl rfl

-- 34. `p25_crc32cd` (`crc32cx w0, w0, x1`: 64-bit Castagnoli CRC-32C with W0 upper-32 zeroing!)
theorem triangulate_p25_crc32cd (crc data sp lr : BitVec 64) (mem : ByteMem) :
    TriangulatedGp64 (.ok (spec_p25 crc data))
      (spec_p25 crc data) p25Words 2 (mkCallGp crc data sp lr mem) lr := by
  refine mkTriGp64_2 rfl rfl rfl ?_
  change (BitVec.extractLsb' 0 32 ((crc32Multi true 8 (BitVec.extractLsb' 0 32 ((BitVec.extractLsb' 0 32 crc).zeroExtend 64)) data).zeroExtend 64)).zeroExtend 64 =
         (crc32Multi true 8 (BitVec.extractLsb' 0 32 crc) data).zeroExtend 64
  have hcrc : BitVec.extractLsb' 0 32 ((BitVec.extractLsb' 0 32 crc).zeroExtend 64) = BitVec.extractLsb' 0 32 crc := by
    apply BitVec.eq_of_toNat_eq
    rw [BitVec.extractLsb'_toNat, BitVec.toNat_setWidth, Nat.shiftRight_zero]
    have h32 : (BitVec.extractLsb' 0 32 crc).toNat < 2 ^ 32 := (BitVec.extractLsb' 0 32 crc).isLt
    have h64 : (BitVec.extractLsb' 0 32 crc).toNat < 2 ^ 64 := Nat.lt_trans h32 (by decide)
    rw [Nat.mod_eq_of_lt h64, Nat.mod_eq_of_lt h32]
  rw [hcrc]
  apply BitVec.eq_of_toNat_eq
  rw [BitVec.toNat_setWidth, BitVec.extractLsb'_toNat, BitVec.toNat_setWidth, Nat.shiftRight_zero]
  have hlt32 : (crc32Multi true 8 (BitVec.extractLsb' 0 32 crc) data).toNat < 2 ^ 32 := (crc32Multi _ _ _ _).isLt
  have hlt64 : (crc32Multi true 8 (BitVec.extractLsb' 0 32 crc) data).toNat < 2 ^ 64 := Nat.lt_trans hlt32 (by decide)
  rw [Nat.mod_eq_of_lt hlt64, Nat.mod_eq_of_lt hlt32, Nat.mod_eq_of_lt hlt64]

end NeonTriangulation24
