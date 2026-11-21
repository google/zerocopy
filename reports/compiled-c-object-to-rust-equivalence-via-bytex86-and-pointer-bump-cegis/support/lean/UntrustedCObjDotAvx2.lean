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
import Init.Data.Nat.Basic
import Init.Data.Nat.Lemmas
import Init.Omega
import ByteX86Gcc
import RustFfiSpecs
import CompiledCObjImages
import UntrustedCObjHints
import UntrustedCObjSimdHelpers
import UntrustedCObjDotAvx2Tail

/-!
# `UntrustedCObjDotAvx2`

Top-level equivalence proof for `gcc 15.2.0 -O3 -mavx2` `c_dot_u8_u16`
(`cFfiKernelsO3Avx2Obj` at `0x140`, `stackReserve = 0`, `0` `sorry`, `0` `isPartial`):
- Handles `len = 0` (`0x430`), `1 ≤ len ≤ 31` (`0x433` -> `dotO3_epi16_0x211`),
  the `32`-element AVX2 hot loop (`0x170..0x1df`, split into three shallow 8-insn
  steps `A`/`B`/`C`), horizontal `vextracti128` + `vpsrldq` reduction (`0x1e1..0x204`),
  clean `vzeroupper; ret` (`0x423`), and non-zero remainder `vmovdqa; vzeroupper`
  joining `UntrustedCObjDotAvx2Tail.dotO3_epi16_0x211`.
-/

namespace UntrustedCObjDotAvx2

open ByteX86Gcc
open RustFfiSpecs
open CompiledCObjImages
open UntrustedCObjHints
open UntrustedCObjSimdHelpers
open UntrustedCObjDotAvx2Tail

private abbrev y0 : YmmIdx := ⟨0, by decide⟩
private abbrev y1 : YmmIdx := ⟨1, by decide⟩
private abbrev y2 : YmmIdx := ⟨2, by decide⟩
private abbrev y3 : YmmIdx := ⟨3, by decide⟩
private abbrev y4 : YmmIdx := ⟨4, by decide⟩
private abbrev y5 : YmmIdx := ⟨5, by decide⟩

private theorem vzeroUpperAll_lo128 (ymms : YmmIdx → BitVec 256) (r : YmmIdx) :
    BitVec.extractLsb' 0 128 (vzeroUpperAll ymms r) = BitVec.extractLsb' 0 128 (ymms r) := by
  unfold vzeroUpperAll; exact extract_lo128_zeroExtend256 _

private theorem vzeroUpperAll_clean (ymms : YmmIdx → BitVec 256) :
    ∀ r : YmmIdx, BitVec.extractLsb' 128 128 (vzeroUpperAll ymms r) = 0#128 := by
  intro r; unfold vzeroUpperAll; apply BitVec.eq_of_getLsbD_eq; intro b hb
  unfold BitVec.zeroExtend; simp [hb]

private theorem nat_mul32_step0 {q : Nat} (hq : 1 ≤ q) :
    (q - (0 + 1)) * 32 + 32 = q * 32 := by omega

private theorem nat_mul32_stepM {q m : Nat} (hle : m + 1 < q) :
    (q - (m + 1 + 1)) * 32 + 32 = (q - (m + 1)) * 32 := by omega

/-! ## Section 1: Pure-Bool Reflected Decodes (`0x140..0x211`, `0x423..0x440`) -/

private theorem dotO3_test : decodeX64 (fetchWindow16 dotO3Cmap 0x400140#64) =
    .ok (.aluRmReg .s64 .test (.reg .rdx) .rdx) 3 := decodeAt_of_check rfl
private theorem dotO3_je0 : decodeX64 (fetchWindow16 dotO3Cmap 0x400143#64) =
    .ok (.jccRel .e 0x00000000000002e7#64) 6 := decodeAt_of_check rfl

private theorem dotO3_zero_xor : decodeX64 (fetchWindow16 dotO3Cmap 0x400430#64) =
    .ok (.aluRmReg .s32 .xor (.reg .rax) .rax) 2 := decodeAt_of_check rfl
private theorem dotO3_zero_ret : decodeX64 (fetchWindow16 dotO3Cmap 0x400432#64) =
    .ok .ret64 1 := decodeAt_of_check rfl

private def dotO3_lenChkSeq : List (X64Instr × BitVec 64) := [
  (.lea .s64 .rax { base := some .rdx, disp := 0xffffffffffffffff#64 }, 0x40014d#64),
  (.aluImm .s64 .cmp (.reg .rax) 0x1e#64, 0x400151#64)
]
private theorem dotO3_lenChk_dec : decodeSeqAt dotO3Cmap 2 0x400149#64 = some dotO3_lenChkSeq :=
  decodeSeqAt_of_check rfl rfl
private theorem dotO3_lenChk_jbe : decodeX64 (fetchWindow16 dotO3Cmap 0x400151#64) =
    .ok (.jccRel .be 0x00000000000002dc#64) 6 := decodeAt_of_check rfl

private def dotO3_skip32Seq : List (X64Instr × BitVec 64) := [
  (.simdBitwise .vex128 .xor y2 y2 (.reg y2), 0x400437#64),
  (.aluRmReg .s32 .xor (.reg .r9) .r9, 0x40043a#64),
  (.aluRmReg .s32 .xor (.reg .rax) .rax, 0x40043c#64)
]
private theorem dotO3_skip32_dec : decodeSeqAt dotO3Cmap 3 0x400433#64 = some dotO3_skip32Seq :=
  decodeSeqAt_of_check rfl rfl
private theorem dotO3_skip32_jmp : decodeX64 (fetchWindow16 dotO3Cmap 0x40043c#64) =
    .ok (.jmpRel 0xfffffffffffffdd0#64) 5 := decodeAt_of_check rfl

private def dotO3_avxPreSeq : List (X64Instr × BitVec 64) := [
  (.movStore .s64 (.reg .r9) .rdx, 0x40015a#64),
  (.aluRmReg .s32 .xor (.reg .rax) .rax, 0x40015c#64),
  (.simdBitwise .vex128 .xor y3 y3 (.reg y3), 0x400160#64),
  (.aluImm .s64 .and (.reg .r9) 0xffffffffffffffe0#64, 0x400164#64),
  (.nop, 0x400165#64),
  (.nop, 0x400170#64)
]
private theorem dotO3_avxPre_dec : decodeSeqAt dotO3Cmap 6 0x400157#64 = some dotO3_avxPreSeq :=
  decodeSeqAt_of_check rfl rfl

private def dotO3_avxASeq : List (X64Instr × BitVec 64) := [
  (.simdMovLoad .vex256 y0 (.mem { base := some .rdi, index := some (.rax, 0) }), 0x400175#64),
  (.simdMovLoad .vex256 y1 (.mem { base := some .rsi, index := some (.rax, 1) }), 0x40017a#64),
  (.simdMovLoad .vex256 y5 (.mem { base := some .rsi, index := some (.rax, 1), disp := 0x20#64 }), 0x400180#64),
  (.aluImm .s64 .add (.reg .rax) 0x20#64, 0x400184#64),
  (.simdExtend .vex256 .zxbw y2 (.reg y0), 0x400189#64),
  (.simdExtract128 (.reg y0) y0 0x01#8, 0x40018f#64),
  (.simdPmullw .vex256 y4 y2 (.reg y1), 0x400193#64),
  (.simdPmulhuw .vex256 y2 y2 (.reg y1), 0x400197#64)
]
private theorem dotO3_avxA_dec : decodeSeqAt dotO3Cmap 8 0x400170#64 = some dotO3_avxASeq :=
  decodeSeqAt_of_check rfl rfl

private def dotO3_avxBSeq : List (X64Instr × BitVec 64) := [
  (.simdExtend .vex256 .zxbw y0 (.reg y0), 0x40019c#64),
  (.simdUnpack .vex256 .lwd y1 y4 (.reg y2), 0x4001a0#64),
  (.simdUnpack .vex256 .hwd y2 y4 (.reg y2), 0x4001a4#64),
  (.simdPerm2i128 y4 y1 (.reg y2) 0x20#8, 0x4001aa#64),
  (.simdPerm2i128 y1 y1 (.reg y2) 0x31#8, 0x4001b0#64),
  (.simdAdd .vex256 .e32 y1 y1 (.reg y4), 0x4001b4#64),
  (.simdPmullw .vex256 y4 y0 (.reg y5), 0x4001b8#64),
  (.simdPmulhuw .vex256 y0 y0 (.reg y5), 0x4001bc#64)
]
private theorem dotO3_avxB_dec : decodeSeqAt dotO3Cmap 8 0x400197#64 = some dotO3_avxBSeq :=
  decodeSeqAt_of_check rfl rfl

private def dotO3_avxCSeq : List (X64Instr × BitVec 64) := [
  (.simdUnpack .vex256 .lwd y2 y4 (.reg y0), 0x4001c0#64),
  (.simdUnpack .vex256 .hwd y0 y4 (.reg y0), 0x4001c4#64),
  (.simdPerm2i128 y4 y2 (.reg y0) 0x20#8, 0x4001ca#64),
  (.simdPerm2i128 y2 y2 (.reg y0) 0x31#8, 0x4001d0#64),
  (.simdAdd .vex256 .e32 y2 y2 (.reg y4), 0x4001d4#64),
  (.simdAdd .vex256 .e32 y1 y1 (.reg y2), 0x4001d8#64),
  (.simdAdd .vex256 .e32 y3 y3 (.reg y1), 0x4001dc#64),
  (.aluRmReg .s64 .cmp (.reg .r9) .rax, 0x4001df#64)
]
private theorem dotO3_avxC_dec : decodeSeqAt dotO3Cmap 8 0x4001bc#64 = some dotO3_avxCSeq :=
  decodeSeqAt_of_check rfl rfl
private theorem dotO3_avx_jne : decodeX64 (fetchWindow16 dotO3Cmap 0x4001df#64) =
    .ok (.jccRel .ne 0xffffffffffffff8f#64) 2 := decodeAt_of_check rfl

private def dotO3_horizSeq : List (X64Instr × BitVec 64) := [
  (.simdExtract128 (.reg y0) y3 0x01#8, 0x4001e7#64),
  (.simdAdd .vex128 .e32 y0 y0 (.reg y3), 0x4001eb#64),
  (.simdPsrldq .vex128 y1 y0 0x08#8, 0x4001f0#64),
  (.simdAdd .vex128 .e32 y1 y0 (.reg y1), 0x4001f4#64),
  (.simdPsrldq .vex128 y2 y1 0x04#8, 0x4001f9#64),
  (.simdAdd .vex128 .e32 y1 y1 (.reg y2), 0x4001fd#64),
  (.simdMovXToGpr true false (.reg .rax) y1, 0x400201#64),
  (.aluRmReg .s64 .cmp (.reg .rdx) .r9, 0x400204#64)
]
private theorem dotO3_horiz_dec : decodeSeqAt dotO3Cmap 8 0x4001e1#64 = some dotO3_horizSeq :=
  decodeSeqAt_of_check rfl rfl
private theorem dotO3_horiz_je : decodeX64 (fetchWindow16 dotO3Cmap 0x400204#64) =
    .ok (.jccRel .e 0x0000000000000219#64) 6 := decodeAt_of_check rfl

private theorem dotO3_vzu423 : decodeX64 (fetchWindow16 dotO3Cmap 0x400423#64) =
    .ok .vzeroupper 3 := decodeAt_of_check rfl

private def dotO3_toEpi16Seq : List (X64Instr × BitVec 64) := [
  (.simdMovLoad .vex128 y2 (.reg y0), 0x40020e#64),
  (.vzeroupper, 0x400211#64)
]
private theorem dotO3_toEpi16_dec : decodeSeqAt dotO3Cmap 2 0x40020a#64 = some dotO3_toEpi16Seq :=
  decodeSeqAt_of_check rfl rfl

/-! ## Section 2: `32`-Elem AVX2 Dot-Product Lane Algebra -/

private def vpaddd256 (a b : BitVec 256) : BitVec 256 :=
  (packDwords128 fun i => getDword128 (BitVec.extractLsb' 128 128 a) i +
                          getDword128 (BitVec.extractLsb' 128 128 b) i) ++
  (packDwords128 fun i => getDword128 (BitVec.extractLsb' 0 128 a) i +
                          getDword128 (BitVec.extractLsb' 0 128 b) i)

private def pmullw256 (a b : BitVec 256) : BitVec 256 :=
  pmullw128 (BitVec.extractLsb' 128 128 a) (BitVec.extractLsb' 128 128 b) ++
  pmullw128 (BitVec.extractLsb' 0 128 a) (BitVec.extractLsb' 0 128 b)

private def pmulhuw256 (a b : BitVec 256) : BitVec 256 :=
  pmulhuw128 (BitVec.extractLsb' 128 128 a) (BitVec.extractLsb' 128 128 b) ++
  pmulhuw128 (BitVec.extractLsb' 0 128 a) (BitVec.extractLsb' 0 128 b)

private def unpack256 (op : VecUnpackOp) (a b : BitVec 256) : BitVec 256 :=
  unpack128 op (BitVec.extractLsb' 128 128 a) (BitVec.extractLsb' 128 128 b) ++
  unpack128 op (BitVec.extractLsb' 0 128 a) (BitVec.extractLsb' 0 128 b)

private theorem sumDwords256_vpaddd256 (a b : BitVec 256) :
    sumDwords256 (vpaddd256 a b) = sumDwords256 a + sumDwords256 b :=
  sumDwords256_vpaddd a b

private theorem rustDotU8U16From_acc_shift (m : ByteMem) (n : Nat) :
    ∀ (pa pb : BitVec 64) (acc : BitVec 32),
      rustDotU8U16From m pa pb n acc = acc + rustDotU8U16From m pa pb n 0#32 := by
  induction n with
  | zero => intro _ _ acc; rw [rustDotU8U16From_zero, rustDotU8U16From_zero, BitVec.add_zero]
  | succ k ih =>
    intro pa pb acc
    rw [rustDotU8U16From_succ, rustDotU8U16From_succ, ih, ih (pa + 1#64) (pb + 2#64) (dotStepU8U16 0#32 _ _)]
    unfold dotStepU8U16; rw [BitVec.zero_add, BitVec.add_assoc]

private theorem dot16_avx2_half_algebra (m : ByteMem) (pa pb : BitVec 64) :
    let a128 := readMem128 m pa
    let b256 := readMem256 m pb
    let aW := packWords256 fun i => (getByte128 a128 i).zeroExtend 16
    let lo := pmullw256 aW b256
    let hi := pmulhuw256 aW b256
    let uL := unpack256 .lwd lo hi
    let uH := unpack256 .hwd lo hi
    let s := vpaddd256 (perm2i128Eval uL uH 0x31#8) (perm2i128Eval uL uH 0x20#8)
    sumDwords256 s = rustDotU8U16From m pa pb 16 0#32 := by
  dsimp only [vpaddd256]
  rw [sumDwords256_vpaddd, sumDwords256_perm2i128_add]
  dsimp only [unpack256]
  rw [sumDwords256_append, sumDwords256_append]
  dsimp only [pmullw256, pmulhuw256]
  repeat rw [extract_lo128_append]
  repeat rw [extract_hi128_append]
  have ha := BitVec.add_assoc (n := 32)
  have hc := BitVec.add_comm (n := 32)
  have hrearr : ∀ (l0 l1 h0 h1 : BitVec 32), (l0 + l1) + (h0 + h1) = (h0 + l0) + (h1 + l1) := by
    intro l0 l1 h0 h1
    rw [ha, ← ha l1 h0 h1, hc l1 h0, ha h0 l1 h1, ← ha, hc l0 h0, hc l1 h1]
  rw [hrearr]
  rw [sumDwords128_unpack_mul_pair, sumDwords128_unpack_mul_pair]
  repeat rw [getWord128_packWords256_lo]
  repeat rw [getWord128_packWords256_hi]
  rw [readMem256_lo128, readMem256_hi128]
  repeat rw [readMem128_byte_at]
  repeat rw [readMem128_word_at]
  dsimp only
  repeat rw [zext8_16_32_eq]
  have hlo8 :
      (m (pa + BitVec.ofNat 64 0)).zeroExtend 32 * (readMem16 m (pb + BitVec.ofNat 64 (2 * 0))).zeroExtend 32 +
      (m (pa + BitVec.ofNat 64 1)).zeroExtend 32 * (readMem16 m (pb + BitVec.ofNat 64 (2 * 1))).zeroExtend 32 +
      (m (pa + BitVec.ofNat 64 2)).zeroExtend 32 * (readMem16 m (pb + BitVec.ofNat 64 (2 * 2))).zeroExtend 32 +
      (m (pa + BitVec.ofNat 64 3)).zeroExtend 32 * (readMem16 m (pb + BitVec.ofNat 64 (2 * 3))).zeroExtend 32 +
      (m (pa + BitVec.ofNat 64 4)).zeroExtend 32 * (readMem16 m (pb + BitVec.ofNat 64 (2 * 4))).zeroExtend 32 +
      (m (pa + BitVec.ofNat 64 5)).zeroExtend 32 * (readMem16 m (pb + BitVec.ofNat 64 (2 * 5))).zeroExtend 32 +
      (m (pa + BitVec.ofNat 64 6)).zeroExtend 32 * (readMem16 m (pb + BitVec.ofNat 64 (2 * 6))).zeroExtend 32 +
      (m (pa + BitVec.ofNat 64 7)).zeroExtend 32 * (readMem16 m (pb + BitVec.ofNat 64 (2 * 7))).zeroExtend 32 =
      rustDotU8U16From m pa pb 8 0#32 := by
    rw [rustDotU8U16From_8, BitVec.zero_add]
  have hhi8 :
      (m (pa + BitVec.ofNat 64 8)).zeroExtend 32 * (readMem16 m ((pb + 16#64) + BitVec.ofNat 64 (2 * 0))).zeroExtend 32 +
      (m (pa + BitVec.ofNat 64 9)).zeroExtend 32 * (readMem16 m ((pb + 16#64) + BitVec.ofNat 64 (2 * 1))).zeroExtend 32 +
      (m (pa + BitVec.ofNat 64 10)).zeroExtend 32 * (readMem16 m ((pb + 16#64) + BitVec.ofNat 64 (2 * 2))).zeroExtend 32 +
      (m (pa + BitVec.ofNat 64 11)).zeroExtend 32 * (readMem16 m ((pb + 16#64) + BitVec.ofNat 64 (2 * 3))).zeroExtend 32 +
      (m (pa + BitVec.ofNat 64 12)).zeroExtend 32 * (readMem16 m ((pb + 16#64) + BitVec.ofNat 64 (2 * 4))).zeroExtend 32 +
      (m (pa + BitVec.ofNat 64 13)).zeroExtend 32 * (readMem16 m ((pb + 16#64) + BitVec.ofNat 64 (2 * 5))).zeroExtend 32 +
      (m (pa + BitVec.ofNat 64 14)).zeroExtend 32 * (readMem16 m ((pb + 16#64) + BitVec.ofNat 64 (2 * 6))).zeroExtend 32 +
      (m (pa + BitVec.ofNat 64 15)).zeroExtend 32 * (readMem16 m ((pb + 16#64) + BitVec.ofNat 64 (2 * 7))).zeroExtend 32 =
      rustDotU8U16From m (pa + 8#64) (pb + 16#64) 8 0#32 := by
    rw [rustDotU8U16From_8, BitVec.zero_add]
    have hp : ∀ k : Nat, (pa + BitVec.ofNat 64 8) + BitVec.ofNat 64 k = pa + BitVec.ofNat 64 (8 + k) :=
      bv64_add_ofNat_assoc pa 8
    change _ =
      (m ((pa + BitVec.ofNat 64 8) + BitVec.ofNat 64 0)).zeroExtend 32 * (readMem16 m ((pb + 16#64) + BitVec.ofNat 64 0)).zeroExtend 32 +
      (m ((pa + BitVec.ofNat 64 8) + BitVec.ofNat 64 1)).zeroExtend 32 * (readMem16 m ((pb + 16#64) + BitVec.ofNat 64 2)).zeroExtend 32 +
      (m ((pa + BitVec.ofNat 64 8) + BitVec.ofNat 64 2)).zeroExtend 32 * (readMem16 m ((pb + 16#64) + BitVec.ofNat 64 4)).zeroExtend 32 +
      (m ((pa + BitVec.ofNat 64 8) + BitVec.ofNat 64 3)).zeroExtend 32 * (readMem16 m ((pb + 16#64) + BitVec.ofNat 64 6)).zeroExtend 32 +
      (m ((pa + BitVec.ofNat 64 8) + BitVec.ofNat 64 4)).zeroExtend 32 * (readMem16 m ((pb + 16#64) + BitVec.ofNat 64 8)).zeroExtend 32 +
      (m ((pa + BitVec.ofNat 64 8) + BitVec.ofNat 64 5)).zeroExtend 32 * (readMem16 m ((pb + 16#64) + BitVec.ofNat 64 10)).zeroExtend 32 +
      (m ((pa + BitVec.ofNat 64 8) + BitVec.ofNat 64 6)).zeroExtend 32 * (readMem16 m ((pb + 16#64) + BitVec.ofNat 64 12)).zeroExtend 32 +
      (m ((pa + BitVec.ofNat 64 8) + BitVec.ofNat 64 7)).zeroExtend 32 * (readMem16 m ((pb + 16#64) + BitVec.ofNat 64 14)).zeroExtend 32
    rw [hp 0, hp 1, hp 2, hp 3, hp 4, hp 5, hp 6, hp 7]
  rw [hlo8, hhi8,
      show rustDotU8U16From m pa pb 16 0#32 = rustDotU8U16From m pa pb (8 + 8) 0#32 from rfl,
      rustDotU8U16From_split,
      rustDotU8U16From_acc_shift m 8 (pa + BitVec.ofNat 64 8) (pb + BitVec.ofNat 64 (2 * 8)) (rustDotU8U16From m pa pb 8 0#32),
      show (16#64 : BitVec 64) = BitVec.ofNat 64 (2 * 8) from rfl]

private theorem dot32_avx2_algebra (m : ByteMem) (pa pb : BitVec 64) (acc3 : BitVec 256) :
    let a256 := readMem256 m pa
    let bLo256 := readMem256 m pb
    let bHi256 := readMem256 m (pb + 0x20#64)
    let aLoW := packWords256 fun i => (getByte128 (BitVec.extractLsb' 0 128 a256) i).zeroExtend 16
    let aHiW := packWords256 fun i => (getByte128 (BitVec.extractLsb' 128 128 a256) i).zeroExtend 16
    let lo1 := pmullw256 aLoW bLo256
    let hi1 := pmulhuw256 aLoW bLo256
    let u1L := unpack256 .lwd lo1 hi1
    let u1H := unpack256 .hwd lo1 hi1
    let s1  := vpaddd256 (perm2i128Eval u1L u1H 0x31#8) (perm2i128Eval u1L u1H 0x20#8)
    let lo2 := pmullw256 aHiW bHi256
    let hi2 := pmulhuw256 aHiW bHi256
    let u2L := unpack256 .lwd lo2 hi2
    let u2H := unpack256 .hwd lo2 hi2
    let s2  := vpaddd256 (perm2i128Eval u2L u2H 0x31#8) (perm2i128Eval u2L u2H 0x20#8)
    sumDwords256 (vpaddd256 acc3 (vpaddd256 s1 s2)) =
      rustDotU8U16From m pa pb 32 (sumDwords256 acc3) := by
  dsimp only
  rw [sumDwords256_vpaddd256, sumDwords256_vpaddd256]
  rw [readMem256_lo128, readMem256_hi128]
  rw [dot16_avx2_half_algebra m pa pb, dot16_avx2_half_algebra m (pa + 16#64) (pb + 0x20#64)]
  rw [show rustDotU8U16From m pa pb 32 (sumDwords256 acc3) =
        rustDotU8U16From m pa pb (16 + 16) (sumDwords256 acc3) from rfl,
      rustDotU8U16From_split,
      rustDotU8U16From_acc_shift m 16 (pa + BitVec.ofNat 64 16) (pb + BitVec.ofNat 64 (2 * 16)) (rustDotU8U16From m pa pb 16 (sumDwords256 acc3)),
      rustDotU8U16From_acc_shift m 16 pa pb (sumDwords256 acc3),
      show (0x20#64 : BitVec 64) = BitVec.ofNat 64 (2 * 16) from rfl, BitVec.add_assoc]

/-! ## Section 3: Shallow 8-Insn AVX2 Loop Steps (`0x170..0x1df`) & Loop Induction -/

private theorem dotO3_avx_stepA (s : X64State) (aPtr bPtr : BitVec 64) (done idx : Nat) (nd : Nat → UndefChoice)
    (hrun : s.halted = false) (hnf : s.fault = false) (hrip : s.rip = 0x400170#64)
    (hrdi : s.regs .rdi = aPtr) (hrsi : s.regs .rsi = bPtr) (hrax : s.regs .rax = BitVec.ofNat 64 done)
    (h2done : 2 * done < 2 ^ 64) :
    let a256 := readMem256 s.mem (aPtr + BitVec.ofNat 64 done)
    let bLo256 := readMem256 s.mem (bPtr + BitVec.ofNat 64 (2 * done))
    let bHi256 := readMem256 s.mem ((bPtr + BitVec.ofNat 64 (2 * done)) + 0x20#64)
    let aLoW := packWords256 fun i => (getByte128 (BitVec.extractLsb' 0 128 a256) i).zeroExtend 16
    let sA := runFrom dotO3Cmap 8 idx nd s
    sA.halted = false ∧ sA.fault = false ∧ sA.rip = 0x400197#64 ∧ sA.mem = s.mem ∧
    sA.regs = regUpd s.regs .rax (BitVec.ofNat 64 (done + 32)) ∧
    BitVec.extractLsb' 0 128 (sA.ymms y0) = BitVec.extractLsb' 128 128 a256 ∧
    sA.ymms y2 = pmulhuw256 aLoW bLo256 ∧
    sA.ymms y3 = s.ymms y3 ∧
    sA.ymms y4 = pmullw256 aLoW bLo256 ∧
    sA.ymms y5 = bHi256 := by
  dsimp only
  have hshl : BitVec.ofNat 64 done <<< 1 = BitVec.ofNat 64 (2 * done) := by
    have htn : (BitVec.ofNat 64 done).toNat = done := by rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)]
    rw [bv64_shl1_toNat (by rw [htn]; omega), htn]
  have hadd32 : BitVec.ofNat 64 done + 0x20#64 = BitVec.ofNat 64 (done + 32) := by
    change BitVec.ofNat 64 done + BitVec.ofNat 64 32 = _; exact bv64_ofNat_add done 32
  let a256 := readMem256 s.mem (aPtr + BitVec.ofNat 64 done)
  let bLo256 := readMem256 s.mem (bPtr + BitVec.ofNat 64 (2 * done))
  let bHi256 := readMem256 s.mem ((bPtr + BitVec.ofNat 64 (2 * done)) + 0x20#64)
  let aLoW := packWords256 fun i => (getByte128 (BitVec.extractLsb' 0 128 a256) i).zeroExtend 16
  let y1s := ymmUpd s.ymms y0 a256
  let y2s := ymmUpd y1s y1 bLo256
  let y3s := ymmUpd y2s y5 bHi256
  let r1  := regUpd s.regs .rax (BitVec.ofNat 64 (done + 32))
  let fl1 := (evalAluN (by decide) .add (BitVec.ofNat 64 done) 0x20#64 s.flags (nd (idx + 3)).flags).2
  let y4s := ymmUpd y3s y2 aLoW
  let y5s := writeXmm128 true y4s y0 (BitVec.extractLsb' 128 128 a256)
  let y6s := ymmUpd y5s y4 (pmullw256 aLoW bLo256)
  let y7s := ymmUpd y6s y2 (pmulhuw256 aLoW bLo256)
  rcases runFrom_of_decodeSeqAt dotO3_avxA_dec idx nd s hrun hnf hrip with ⟨hseq, _, _⟩
  have he : runFrom dotO3Cmap 8 idx nd s = { s with rip := 0x400197#64, regs := r1, ymms := y7s, flags := fl1 } := by
    rw [hseq]; dsimp only [dotO3_avxASeq]
    rw [execInstrSeq_succ_cons, exec_simdMovLoad_vex256_mem, evalByteAddr_base_idx0, hrdi, hrax]
    change execInstrSeq 7 _ _ _ { s with rip := 0x400175#64, ymms := y1s } = _
    rw [execInstrSeq_succ_cons, exec_simdMovLoad_vex256_mem, evalByteAddr_base_idx1_disp, hrsi, hrax, hshl, BitVec.add_zero]
    change execInstrSeq 6 _ _ _ { s with rip := 0x40017a#64, ymms := y2s } = _
    rw [execInstrSeq_succ_cons, exec_simdMovLoad_vex256_mem, evalByteAddr_base_idx1_disp, hrsi, hrax, hshl]
    change execInstrSeq 5 _ _ _ { s with rip := 0x400180#64, ymms := y3s } = _
    rw [execInstrSeq_succ_cons, exec_aluImm_s64_add]
    dsimp only; rw [hrax, hadd32]
    change execInstrSeq 4 _ _ _ { s with rip := 0x400184#64, regs := r1, ymms := y3s, flags := fl1 } = _
    rw [execInstrSeq_succ_cons, exec_simdExtend_vex256_zxbw_reg]
    dsimp only; rw [show y3s y0 = a256 from by dsimp only [y3s, y2s, y1s]; (repeat rw [ymmUpd_ne _ (by decide)]); exact ymmUpd_eq _ _ _]
    change execInstrSeq 3 _ _ _ { s with rip := 0x400189#64, regs := r1, ymms := y4s, flags := fl1 } = _
    rw [execInstrSeq_succ_cons, exec_simdExtract128_hi_reg]
    dsimp only; rw [show y4s y0 = a256 from by dsimp only [y4s, y3s, y2s, y1s]; (repeat rw [ymmUpd_ne _ (by decide)]); exact ymmUpd_eq _ _ _]
    change execInstrSeq 2 _ _ _ { s with rip := 0x40018f#64, regs := r1, ymms := y5s, flags := fl1 } = _
    rw [execInstrSeq_succ_cons, exec_simdPmullw_vex256_reg]
    dsimp only
    rw [show y5s y2 = aLoW from by dsimp only [y5s, y4s]; rw [writeXmm128_ne true _ (by decide : y2 ≠ y0), ymmUpd_eq],
        show y5s y1 = bLo256 from by dsimp only [y5s, y4s, y3s, y2s]; rw [writeXmm128_ne true _ (by decide : y1 ≠ y0)]; (repeat rw [ymmUpd_ne _ (by decide)]); exact ymmUpd_eq _ _ _]
    change execInstrSeq 1 _ _ _ { s with rip := 0x400193#64, regs := r1, ymms := y6s, flags := fl1 } = _
    rw [execInstrSeq_succ_cons, exec_simdPmulhuw_vex256_reg, execInstrSeq_zero]
    dsimp only
    rw [show y6s y2 = aLoW from by dsimp only [y6s, y5s, y4s]; rw [ymmUpd_ne _ (by decide), writeXmm128_ne true _ (by decide : y2 ≠ y0), ymmUpd_eq],
        show y6s y1 = bLo256 from by dsimp only [y6s, y5s, y4s, y3s, y2s]; rw [ymmUpd_ne _ (by decide), writeXmm128_ne true _ (by decide : y1 ≠ y0)]; (repeat rw [ymmUpd_ne _ (by decide)]); exact ymmUpd_eq _ _ _]
    rfl
  rw [he]; refine ⟨hrun, hnf, rfl, rfl, rfl, ?_, ?_, ?_, ?_, ?_⟩
  · dsimp only [y7s, y6s, y5s]; rw [ymmUpd_ne _ (by decide), ymmUpd_ne _ (by decide), writeXmm128_true_lo]
  · dsimp only [y7s]; exact ymmUpd_eq _ _ _
  · dsimp only [y7s, y6s, y5s, y4s, y3s, y2s, y1s]
    rw [ymmUpd_ne _ (by decide), ymmUpd_ne _ (by decide), writeXmm128_ne true _ (by decide : y3 ≠ y0)]
    repeat rw [ymmUpd_ne _ (by decide)]
  · dsimp only [y7s, y6s]; rw [ymmUpd_ne _ (by decide), ymmUpd_eq]
  · dsimp only [y7s, y6s, y5s, y4s, y3s]
    rw [ymmUpd_ne _ (by decide), ymmUpd_ne _ (by decide), writeXmm128_ne true _ (by decide : y5 ≠ y0),
        ymmUpd_ne _ (by decide), ymmUpd_eq]

private theorem dotO3_avx_stepB (sA : X64State) (aHi128 : BitVec 128) (lo1 hi1 bHi256 acc3 : BitVec 256)
    (idx : Nat) (nd : Nat → UndefChoice)
    (hrun : sA.halted = false) (hnf : sA.fault = false) (hrip : sA.rip = 0x400197#64)
    (hy0 : BitVec.extractLsb' 0 128 (sA.ymms y0) = aHi128)
    (hy2 : sA.ymms y2 = hi1) (hy3 : sA.ymms y3 = acc3) (hy4 : sA.ymms y4 = lo1) (hy5 : sA.ymms y5 = bHi256) :
    let aHiW := packWords256 fun i => (getByte128 aHi128 i).zeroExtend 16
    let u1L := unpack256 .lwd lo1 hi1
    let u1H := unpack256 .hwd lo1 hi1
    let s1  := vpaddd256 (perm2i128Eval u1L u1H 0x31#8) (perm2i128Eval u1L u1H 0x20#8)
    let sB := runFrom dotO3Cmap 8 idx nd sA
    sB.halted = false ∧ sB.fault = false ∧ sB.rip = 0x4001bc#64 ∧ sB.mem = sA.mem ∧ sB.regs = sA.regs ∧
    sB.ymms y0 = pmulhuw256 aHiW bHi256 ∧
    sB.ymms y1 = s1 ∧
    sB.ymms y3 = acc3 ∧
    sB.ymms y4 = pmullw256 aHiW bHi256 := by
  dsimp only
  let aHiW := packWords256 fun i => (getByte128 aHi128 i).zeroExtend 16
  let u1L := unpack256 .lwd lo1 hi1
  let u1H := unpack256 .hwd lo1 hi1
  let p20 := perm2i128Eval u1L u1H 0x20#8
  let p31 := perm2i128Eval u1L u1H 0x31#8
  let s1  := vpaddd256 p31 p20
  let y1s := ymmUpd sA.ymms y0 aHiW
  let y2s := ymmUpd y1s y1 u1L
  let y3s := ymmUpd y2s y2 u1H
  let y4s := ymmUpd y3s y4 p20
  let y5s := ymmUpd y4s y1 p31
  let y6s := ymmUpd y5s y1 s1
  let y7s := ymmUpd y6s y4 (pmullw256 aHiW bHi256)
  let y8s := ymmUpd y7s y0 (pmulhuw256 aHiW bHi256)
  rcases runFrom_of_decodeSeqAt dotO3_avxB_dec idx nd sA hrun hnf hrip with ⟨hseq, _, _⟩
  have he : runFrom dotO3Cmap 8 idx nd sA = { sA with rip := 0x4001bc#64, ymms := y8s } := by
    rw [hseq]; dsimp only [dotO3_avxBSeq]
    rw [execInstrSeq_succ_cons, exec_simdExtend_vex256_zxbw_reg, hy0]
    change execInstrSeq 7 _ _ _ { sA with rip := 0x40019c#64, ymms := y1s } = _
    rw [execInstrSeq_succ_cons, exec_simdUnpack_vex256_reg]
    dsimp only; rw [show y1s y4 = lo1 from by dsimp only [y1s]; rw [ymmUpd_ne _ (by decide), hy4],
                    show y1s y2 = hi1 from by dsimp only [y1s]; rw [ymmUpd_ne _ (by decide), hy2]]
    change execInstrSeq 6 _ _ _ { sA with rip := 0x4001a0#64, ymms := y2s } = _
    rw [execInstrSeq_succ_cons, exec_simdUnpack_vex256_reg]
    dsimp only; rw [show y2s y4 = lo1 from by dsimp only [y2s, y1s]; (repeat rw [ymmUpd_ne _ (by decide)]); exact hy4,
                    show y2s y2 = hi1 from by dsimp only [y2s, y1s]; (repeat rw [ymmUpd_ne _ (by decide)]); exact hy2]
    change execInstrSeq 5 _ _ _ { sA with rip := 0x4001a4#64, ymms := y3s } = _
    rw [execInstrSeq_succ_cons, exec_simdPerm2i128_reg]
    dsimp only; rw [show y3s y1 = u1L from by dsimp only [y3s, y2s]; rw [ymmUpd_ne _ (by decide), ymmUpd_eq],
                    show y3s y2 = u1H from ymmUpd_eq _ _ _]
    change execInstrSeq 4 _ _ _ { sA with rip := 0x4001aa#64, ymms := y4s } = _
    rw [execInstrSeq_succ_cons, exec_simdPerm2i128_reg]
    dsimp only; rw [show y4s y1 = u1L from by dsimp only [y4s, y3s, y2s]; (repeat rw [ymmUpd_ne _ (by decide)]); exact ymmUpd_eq _ _ _,
                    show y4s y2 = u1H from by dsimp only [y4s, y3s]; rw [ymmUpd_ne _ (by decide), ymmUpd_eq]]
    change execInstrSeq 3 _ _ _ { sA with rip := 0x4001b0#64, ymms := y5s } = _
    rw [execInstrSeq_succ_cons, exec_simdAdd_vex256_e32_reg]
    dsimp only; rw [show y5s y1 = p31 from ymmUpd_eq _ _ _,
                    show y5s y4 = p20 from by dsimp only [y5s, y4s]; rw [ymmUpd_ne _ (by decide), ymmUpd_eq]]
    change execInstrSeq 2 _ _ _ { sA with rip := 0x4001b4#64, ymms := y6s } = _
    rw [execInstrSeq_succ_cons, exec_simdPmullw_vex256_reg]
    dsimp only; rw [show y6s y0 = aHiW from by dsimp only [y6s, y5s, y4s, y3s, y2s, y1s]; (repeat rw [ymmUpd_ne _ (by decide)]); exact ymmUpd_eq _ _ _,
                    show y6s y5 = bHi256 from by dsimp only [y6s, y5s, y4s, y3s, y2s, y1s]; (repeat rw [ymmUpd_ne _ (by decide)]); exact hy5]
    change execInstrSeq 1 _ _ _ { sA with rip := 0x4001b8#64, ymms := y7s } = _
    rw [execInstrSeq_succ_cons, exec_simdPmulhuw_vex256_reg, execInstrSeq_zero]
    dsimp only; rw [show y7s y0 = aHiW from by dsimp only [y7s, y6s, y5s, y4s, y3s, y2s, y1s]; (repeat rw [ymmUpd_ne _ (by decide)]); exact ymmUpd_eq _ _ _,
                    show y7s y5 = bHi256 from by dsimp only [y7s, y6s, y5s, y4s, y3s, y2s, y1s]; (repeat rw [ymmUpd_ne _ (by decide)]); exact hy5]
    rfl
  rw [he]; refine ⟨hrun, hnf, rfl, rfl, rfl, ?_, ?_, ?_, ?_⟩
  · dsimp only [y8s]; exact ymmUpd_eq _ _ _
  · dsimp only [y8s, y7s, y6s]; (repeat rw [ymmUpd_ne _ (by decide)]); exact ymmUpd_eq _ _ _
  · dsimp only [y8s, y7s, y6s, y5s, y4s, y3s, y2s, y1s]; (repeat rw [ymmUpd_ne _ (by decide)]); exact hy3
  · dsimp only [y8s, y7s]; rw [ymmUpd_ne _ (by decide), ymmUpd_eq]

private theorem dotO3_avx_stepC (sB : X64State) (lo2 hi2 s1 acc3 : BitVec 256)
    (idx : Nat) (nd : Nat → UndefChoice)
    (hrun : sB.halted = false) (hnf : sB.fault = false) (hrip : sB.rip = 0x4001bc#64)
    (hy0 : sB.ymms y0 = hi2) (hy1 : sB.ymms y1 = s1) (hy3 : sB.ymms y3 = acc3) (hy4 : sB.ymms y4 = lo2) :
    let u2L := unpack256 .lwd lo2 hi2
    let u2H := unpack256 .hwd lo2 hi2
    let s2  := vpaddd256 (perm2i128Eval u2L u2H 0x31#8) (perm2i128Eval u2L u2H 0x20#8)
    let acc3' := vpaddd256 acc3 (vpaddd256 s1 s2)
    let sC := runFrom dotO3Cmap 8 idx nd sB
    sC.halted = false ∧ sC.fault = false ∧ sC.rip = 0x4001df#64 ∧ sC.mem = sB.mem ∧ sC.regs = sB.regs ∧
    sC.ymms y3 = acc3' ∧
    sC.flags = (evalAluN (by decide) .cmp (sB.regs .r9) (sB.regs .rax) sB.flags (nd (idx + 7)).flags).2 := by
  dsimp only
  let u2L := unpack256 .lwd lo2 hi2
  let u2H := unpack256 .hwd lo2 hi2
  let p20 := perm2i128Eval u2L u2H 0x20#8
  let p31 := perm2i128Eval u2L u2H 0x31#8
  let s2  := vpaddd256 p31 p20
  let s12 := vpaddd256 s1 s2
  let acc3' := vpaddd256 acc3 s12
  let y1s := ymmUpd sB.ymms y2 u2L
  let y2s := ymmUpd y1s y0 u2H
  let y3s := ymmUpd y2s y4 p20
  let y4s := ymmUpd y3s y2 p31
  let y5s := ymmUpd y4s y2 s2
  let y6s := ymmUpd y5s y1 s12
  let y7s := ymmUpd y6s y3 acc3'
  rcases runFrom_of_decodeSeqAt dotO3_avxC_dec idx nd sB hrun hnf hrip with ⟨hseq, _, _⟩
  have he : runFrom dotO3Cmap 8 idx nd sB =
      { sB with rip := 0x4001df#64, ymms := y7s,
                flags := (evalAluN (by decide) .cmp (sB.regs .r9) (sB.regs .rax) sB.flags (nd (idx + 7)).flags).2 } := by
    rw [hseq]; dsimp only [dotO3_avxCSeq]
    rw [execInstrSeq_succ_cons, exec_simdUnpack_vex256_reg, hy4, hy0]
    change execInstrSeq 7 _ _ _ { sB with rip := 0x4001c0#64, ymms := y1s } = _
    rw [execInstrSeq_succ_cons, exec_simdUnpack_vex256_reg]
    dsimp only; rw [show y1s y4 = lo2 from by dsimp only [y1s]; rw [ymmUpd_ne _ (by decide), hy4],
                    show y1s y0 = hi2 from by dsimp only [y1s]; rw [ymmUpd_ne _ (by decide), hy0]]
    change execInstrSeq 6 _ _ _ { sB with rip := 0x4001c4#64, ymms := y2s } = _
    rw [execInstrSeq_succ_cons, exec_simdPerm2i128_reg]
    dsimp only; rw [show y2s y2 = u2L from by dsimp only [y2s, y1s]; rw [ymmUpd_ne _ (by decide), ymmUpd_eq],
                    show y2s y0 = u2H from ymmUpd_eq _ _ _]
    change execInstrSeq 5 _ _ _ { sB with rip := 0x4001ca#64, ymms := y3s } = _
    rw [execInstrSeq_succ_cons, exec_simdPerm2i128_reg]
    dsimp only; rw [show y3s y2 = u2L from by dsimp only [y3s, y2s, y1s]; (repeat rw [ymmUpd_ne _ (by decide)]); exact ymmUpd_eq _ _ _,
                    show y3s y0 = u2H from by dsimp only [y3s, y2s]; rw [ymmUpd_ne _ (by decide), ymmUpd_eq]]
    change execInstrSeq 4 _ _ _ { sB with rip := 0x4001d0#64, ymms := y4s } = _
    rw [execInstrSeq_succ_cons, exec_simdAdd_vex256_e32_reg]
    dsimp only; rw [show y4s y2 = p31 from ymmUpd_eq _ _ _,
                    show y4s y4 = p20 from by dsimp only [y4s, y3s]; rw [ymmUpd_ne _ (by decide), ymmUpd_eq]]
    change execInstrSeq 3 _ _ _ { sB with rip := 0x4001d4#64, ymms := y5s } = _
    rw [execInstrSeq_succ_cons, exec_simdAdd_vex256_e32_reg]
    dsimp only; rw [show y5s y1 = s1 from by dsimp only [y5s, y4s, y3s, y2s, y1s]; (repeat rw [ymmUpd_ne _ (by decide)]); exact hy1,
                    show y5s y2 = s2 from ymmUpd_eq _ _ _]
    change execInstrSeq 2 _ _ _ { sB with rip := 0x4001d8#64, ymms := y6s } = _
    rw [execInstrSeq_succ_cons, exec_simdAdd_vex256_e32_reg]
    dsimp only; rw [show y6s y3 = acc3 from by dsimp only [y6s, y5s, y4s, y3s, y2s, y1s]; (repeat rw [ymmUpd_ne _ (by decide)]); exact hy3,
                    show y6s y1 = s12 from ymmUpd_eq _ _ _]
    change execInstrSeq 1 _ _ _ { sB with rip := 0x4001dc#64, ymms := y7s } = _
    rw [execInstrSeq_succ_cons, exec_aluRmReg_s64_cmp, execInstrSeq_zero]
  rw [he]; refine ⟨hrun, hnf, rfl, rfl, rfl, by dsimp only [y7s]; exact ymmUpd_eq _ _ _, rfl⟩

private theorem dotO3_avx_iter (s0 s : X64State) (done bound idx : Nat) (nd : Nat → UndefChoice)
    (hpre : DotU8U16Pre 0 s0)
    (hrun : s.halted = false) (hnf : s.fault = false) (hrip : s.rip = 0x400170#64) (hmem : s.mem = s0.mem)
    (hrdi : s.regs .rdi = s0.regs .rdi) (hrsi : s.regs .rsi = s0.regs .rsi)
    (hrdx : s.regs .rdx = s0.regs .rdx) (hr9 : s.regs .r9 = BitVec.ofNat 64 bound)
    (hrax : s.regs .rax = BitVec.ofNat 64 done)
    (hy3 : sumDwords256 (s.ymms y3) = rustDotU8U16From s0.mem (s0.regs .rdi) (s0.regs .rsi) done 0#32)
    (hcs : SysVCalleeSavedPreserved s0 s)
    (hdoneBound : done + 32 ≤ (s0.regs .rdx).toNat) :
    let s1 := runFrom dotO3Cmap 24 idx nd s
    s1.halted = false ∧ s1.fault = false ∧ s1.rip = 0x4001df#64 ∧ s1.mem = s0.mem ∧
    s1.regs .rdi = s0.regs .rdi ∧ s1.regs .rsi = s0.regs .rsi ∧ s1.regs .rdx = s0.regs .rdx ∧
    s1.regs .r9 = BitVec.ofNat 64 bound ∧ s1.regs .rax = BitVec.ofNat 64 (done + 32) ∧
    sumDwords256 (s1.ymms y3) = rustDotU8U16From s0.mem (s0.regs .rdi) (s0.regs .rsi) (done + 32) 0#32 ∧
    SysVCalleeSavedPreserved s0 s1 ∧
    s1.flags = (evalAluN (by decide) .cmp (BitVec.ofNat 64 bound) (BitVec.ofNat 64 (done + 32))
                 (runFrom dotO3Cmap 16 idx nd s).flags (nd (idx + 23)).flags).2 := by
  have h2len := hpre.1
  have hA := dotO3_avx_stepA s (s0.regs .rdi) (s0.regs .rsi) done idx nd hrun hnf hrip hrdi hrsi hrax (by omega)
  generalize hsA : runFrom dotO3Cmap 8 idx nd s = sA at hA
  rcases hA with ⟨hAr, hAf, hArip, hAm, hAregs, hAy0, hAy2, hAy3, hAy4, hAy5⟩
  have hB := dotO3_avx_stepB sA _ _ _ _ (s.ymms y3) (idx + 8) nd hAr hAf hArip hAy0 hAy2 hAy3 hAy4 hAy5
  generalize hsB : runFrom dotO3Cmap 8 (idx + 8) nd sA = sB at hB
  rcases hB with ⟨hBr, hBf, hBrip, hBm, hBregs, hBy0, hBy1, hBy3, hBy4⟩
  have hC := dotO3_avx_stepC sB _ _ _ (s.ymms y3) (idx + 16) nd hBr hBf hBrip hBy0 hBy1 hBy3 hBy4
  generalize hsC : runFrom dotO3Cmap 8 (idx + 16) nd sB = sC at hC
  rcases hC with ⟨hCr, hCf, hCrip, hCm, hCregs, hCy3, hCfl⟩
  have hrun24 : runFrom dotO3Cmap 24 idx nd s = sC := by
    rw [show (24 : Nat) = 8 + (8 + 8) by rfl, runFrom_add, hsA, runFrom_add, hsB,
        show idx + 8 + 8 = idx + 16 by omega, hsC]
  have hrun16 : runFrom dotO3Cmap 16 idx nd s = sB := by
    rw [show (16 : Nat) = 8 + 8 by rfl, runFrom_add, hsA, hsB]
  have hCmem : sC.mem = s0.mem := by rw [hCm, hBm, hAm, hmem]
  have hCregsEq : sC.regs = regUpd s.regs .rax (BitVec.ofNat 64 (done + 32)) := by rw [hCregs, hBregs, hAregs]
  have hCsum : sumDwords256 (sC.ymms y3) = rustDotU8U16From s0.mem (s0.regs .rdi) (s0.regs .rsi) (done + 32) 0#32 := by
    rw [hCy3, hmem, dot32_avx2_algebra, hy3, rustDotU8U16From_split]
  have hCcs : SysVCalleeSavedPreserved s0 sC := by
    unfold SysVCalleeSavedPreserved at hcs ⊢; rw [hCregsEq]; exact cs_step_caller (r := .rax) rfl hcs
  rw [hrun24, hrun16]
  refine ⟨hCr, hCf, hCrip, hCmem,
    by rw [hCregsEq, regUpd_ne _ (by decide), hrdi],
    by rw [hCregsEq, regUpd_ne _ (by decide), hrsi],
    by rw [hCregsEq, regUpd_ne _ (by decide), hrdx],
    by rw [hCregsEq, regUpd_ne _ (by decide), hr9],
    by rw [hCregsEq, regUpd_eq],
    hCsum, hCcs, ?_⟩
  rw [hCfl, hBregs, hAregs, regUpd_ne _ (by decide), regUpd_eq, hr9]

private theorem dotO3_avx_loop (s0 : X64State) (hpre : DotU8U16Pre 0 s0) (nd : Nat → UndefChoice)
    (q : Nat) (rem : Nat) :
    ∀ (idx : Nat) (s : X64State),
      rem < q → q * 32 ≤ (s0.regs .rdx).toNat →
      s.halted = false → s.fault = false → s.rip = 0x400170#64 → s.mem = s0.mem →
      s.regs .rdi = s0.regs .rdi → s.regs .rsi = s0.regs .rsi → s.regs .rdx = s0.regs .rdx →
      s.regs .r9 = BitVec.ofNat 64 (q * 32) →
      s.regs .rax = BitVec.ofNat 64 ((q - (rem + 1)) * 32) →
      sumDwords256 (s.ymms y3) = rustDotU8U16From s0.mem (s0.regs .rdi) (s0.regs .rsi) ((q - (rem + 1)) * 32) 0#32 →
      SysVCalleeSavedPreserved s0 s →
      let sf := runFrom dotO3Cmap (25 * (rem + 1)) idx nd s
      sf.halted = false ∧ sf.fault = false ∧ sf.rip = 0x4001e1#64 ∧ sf.mem = s0.mem ∧
      sf.regs .rdi = s0.regs .rdi ∧ sf.regs .rsi = s0.regs .rsi ∧ sf.regs .rdx = s0.regs .rdx ∧
      sf.regs .r9 = BitVec.ofNat 64 (q * 32) ∧
      sumDwords256 (sf.ymms y3) = rustDotU8U16From s0.mem (s0.regs .rdi) (s0.regs .rsi) (q * 32) 0#32 ∧
      SysVCalleeSavedPreserved s0 sf := by
  induction rem with
  | zero =>
    intro idx s hlt hqb hrun hnf hrip hmem hrdi hrsi hrdx hr9 hrax hy3 hcs
    dsimp only
    have hdone := nat_mul32_step0 hlt
    have hstep := dotO3_avx_iter s0 s ((q - (0 + 1)) * 32) (q * 32) idx nd hpre hrun hnf hrip hmem
      hrdi hrsi hrdx hr9 hrax hy3 hcs (by rw [hdone]; exact hqb)
    generalize hs1 : runFrom dotO3Cmap 24 idx nd s = s1 at hstep
    rcases hstep with ⟨h1r, h1f, h1rip, h1m, h1di, h1si, h1dx, h1r9, h1ax, h1y3, h1cs, h1fl⟩
    rw [hdone] at h1y3 h1fl
    have hcc : evalCond .ne s1.flags = false := by
      rw [h1fl]; exact evalCond_ne_of_zf_true (by rw [cmp_flags_zf, cmp_sub_self_zero])
    rw [show 25 * (0 + 1) = 24 + 1 by rfl, runFrom_add, hs1,
        runFrom_succ, step_at_concrete dotO3_avx_jne _ s1 h1r h1f h1rip, exec_jcc_fall hcc, runFrom_zero]
    exact ⟨h1r, h1f, rfl, h1m, h1di, h1si, h1dx, h1r9, h1y3, h1cs⟩
  | succ m ih =>
    intro idx s hlt hqb hrun hnf hrip hmem hrdi hrsi hrdx hr9 hrax hy3 hcs
    dsimp only
    have hdone := nat_mul32_stepM hlt
    have hbd : (q - (m + 1 + 1)) * 32 + 32 ≤ (s0.regs .rdx).toNat := by
      rw [hdone]; exact Nat.le_trans (Nat.mul_le_mul_right 32 (Nat.sub_le q (m + 1))) hqb
    have hstep := dotO3_avx_iter s0 s ((q - (m + 1 + 1)) * 32) (q * 32) idx nd hpre hrun hnf hrip hmem
      hrdi hrsi hrdx hr9 hrax hy3 hcs hbd
    generalize hs1 : runFrom dotO3Cmap 24 idx nd s = s1 at hstep
    rcases hstep with ⟨h1r, h1f, h1rip, h1m, h1di, h1si, h1dx, h1r9, h1ax, h1y3, h1cs, h1fl⟩
    have hlt64 := (s0.regs .rdx).isLt
    have hne : BitVec.ofNat 64 (q * 32) ≠ BitVec.ofNat 64 ((q - (m + 1)) * 32) := by
      intro heq
      have ht := congrArg BitVec.toNat heq
      rw [BitVec.toNat_ofNat, BitVec.toNat_ofNat,
          Nat.mod_eq_of_lt (Nat.lt_of_le_of_lt hqb hlt64),
          Nat.mod_eq_of_lt (Nat.lt_of_le_of_lt (Nat.le_trans (Nat.mul_le_mul_right 32 (Nat.sub_le q (m + 1))) hqb) hlt64)] at ht
      omega
    rw [hdone] at h1ax h1y3 h1fl
    have hcc : evalCond .ne s1.flags = true := by
      rw [h1fl]; exact evalCond_ne_of_zf_false (by rw [cmp_flags_zf, cmp_sub_zero_false_of_ne hne])
    rw [show 25 * (m + 1 + 1) = (24 + 1) + 25 * (m + 1) by omega, runFrom_add, runFrom_add, hs1,
        runFrom_succ, step_at_concrete dotO3_avx_jne _ s1 h1r h1f h1rip, exec_jcc_taken hcc, runFrom_zero]
    exact ih (idx + (24 + 1)) { s1 with rip := 0x400170#64 } (Nat.lt_of_succ_lt hlt) hqb
      h1r h1f rfl h1m h1di h1si h1dx h1r9 h1ax h1y3 h1cs

/-! ## Section 4: Horizontal Reduction (`0x1e1..0x204`) & Top-Level Equivalence Theorem -/

private theorem dotO3_horiz_step (s : X64State) (idx : Nat) (nd : Nat → UndefChoice)
    (hrun : s.halted = false) (hnf : s.fault = false) (hrip : s.rip = 0x4001e1#64) :
    let sH := runFrom dotO3Cmap 8 idx nd s
    sH.halted = false ∧ sH.fault = false ∧ sH.rip = 0x400204#64 ∧ sH.mem = s.mem ∧
    sH.regs = regUpd s.regs .rax ((sumDwords256 (s.ymms y3)).zeroExtend 64) ∧
    sumDwords128 (BitVec.extractLsb' 0 128 (sH.ymms y0)) = sumDwords256 (s.ymms y3) ∧
    sH.flags = (evalAluN (by decide) .cmp (s.regs .rdx) (s.regs .r9) s.flags (nd (idx + 7)).flags).2 := by
  dsimp only
  let v3 := s.ymms y3
  let x0_0 := BitVec.extractLsb' 128 128 v3
  let x0_1 := packDwords128 fun i => getDword128 x0_0 i + getDword128 (BitVec.extractLsb' 0 128 v3) i
  let x1_0 := psrldq128 x0_1 8#8
  let x1_1 := packDwords128 fun i => getDword128 x0_1 i + getDword128 x1_0 i
  let x2_0 := psrldq128 x1_1 4#8
  let x1_2 := packDwords128 fun i => getDword128 x1_1 i + getDword128 x2_0 i
  let y1s := writeXmm128 true s.ymms y0 x0_0
  let y2s := writeXmm128 true y1s y0 x0_1
  let y3s := writeXmm128 true y2s y1 x1_0
  let y4s := writeXmm128 true y3s y1 x1_1
  let y5s := writeXmm128 true y4s y2 x2_0
  let y6s := writeXmm128 true y5s y1 x1_2
  have hx0Sum : sumDwords128 x0_1 = sumDwords256 v3 := by
    dsimp only [x0_1, x0_0]; rw [sumDwords128_paddd, BitVec.add_comm]; rfl
  have hres32 : BitVec.extractLsb' 0 32 (y6s y1) = sumDwords256 v3 := by
    have h1 : BitVec.extractLsb' 0 32 (y6s y1) = BitVec.extractLsb' 0 32 x1_2 := by
      dsimp only [y6s]; rw [writeXmm128_true_eq, ymmUpd_eq]
      apply BitVec.eq_of_getLsbD_eq; intro b hb
      rw [BitVec.getLsbD_extractLsb', BitVec.getLsbD_extractLsb', BitVec.getLsbD_append]
      simp [show b < 128 by omega]
    rw [h1, show BitVec.extractLsb' 0 32 x1_2 = sumDwords128 x0_1 from horiz_reduce_128_eq x0_1, hx0Sum]
  rcases runFrom_of_decodeSeqAt dotO3_horiz_dec idx nd s hrun hnf hrip with ⟨hseq, _, _⟩
  have he : runFrom dotO3Cmap 8 idx nd s =
      { s with rip := 0x400204#64,
               regs := regUpd s.regs .rax ((sumDwords256 v3).zeroExtend 64),
               ymms := y6s,
               flags := (evalAluN (by decide) .cmp (s.regs .rdx) (s.regs .r9) s.flags (nd (idx + 7)).flags).2 } := by
    rw [hseq]; dsimp only [dotO3_horizSeq]
    rw [execInstrSeq_succ_cons, exec_simdExtract128_hi_reg]
    change execInstrSeq 7 _ _ _ { s with rip := 0x4001e7#64, ymms := y1s } = _
    rw [execInstrSeq_succ_cons, exec_simdAdd_vex128_e32_reg]
    dsimp only; rw [show BitVec.extractLsb' 0 128 (y1s y0) = x0_0 from writeXmm128_true_lo _ _ _,
                    show BitVec.extractLsb' 0 128 (y1s y3) = BitVec.extractLsb' 0 128 v3 from by dsimp only [y1s]; rw [writeXmm128_ne true _ (by decide : y3 ≠ y0)]]
    change execInstrSeq 6 _ _ _ { s with rip := 0x4001eb#64, ymms := y2s } = _
    rw [execInstrSeq_succ_cons, exec_simdPsrldq_vex128]
    dsimp only; rw [show BitVec.extractLsb' 0 128 (y2s y0) = x0_1 from writeXmm128_true_lo _ _ _]
    change execInstrSeq 5 _ _ _ { s with rip := 0x4001f0#64, ymms := y3s } = _
    rw [execInstrSeq_succ_cons, exec_simdAdd_vex128_e32_reg]
    dsimp only; rw [show BitVec.extractLsb' 0 128 (y3s y0) = x0_1 from by dsimp only [y3s]; rw [writeXmm128_ne true _ (by decide : y0 ≠ y1), writeXmm128_true_lo],
                    show BitVec.extractLsb' 0 128 (y3s y1) = x1_0 from writeXmm128_true_lo _ _ _]
    change execInstrSeq 4 _ _ _ { s with rip := 0x4001f4#64, ymms := y4s } = _
    rw [execInstrSeq_succ_cons, exec_simdPsrldq_vex128]
    dsimp only; rw [show BitVec.extractLsb' 0 128 (y4s y1) = x1_1 from writeXmm128_true_lo _ _ _]
    change execInstrSeq 3 _ _ _ { s with rip := 0x4001f9#64, ymms := y5s } = _
    rw [execInstrSeq_succ_cons, exec_simdAdd_vex128_e32_reg]
    dsimp only; rw [show BitVec.extractLsb' 0 128 (y5s y1) = x1_1 from by dsimp only [y5s]; rw [writeXmm128_ne true _ (by decide : y1 ≠ y2), writeXmm128_true_lo],
                    show BitVec.extractLsb' 0 128 (y5s y2) = x2_0 from writeXmm128_true_lo _ _ _]
    change execInstrSeq 2 _ _ _ { s with rip := 0x4001fd#64, ymms := y6s } = _
    rw [execInstrSeq_succ_cons, exec_simdMovXToGpr_s32_reg]
    dsimp only; rw [hres32]
    rw [execInstrSeq_succ_cons, exec_aluRmReg_s64_cmp, execInstrSeq_zero]
    dsimp only; rw [regUpd_ne _ (by decide), regUpd_ne _ (by decide)]
  rw [he]; refine ⟨hrun, hnf, rfl, rfl, rfl, ?_, rfl⟩
  dsimp only [y6s, y5s, y4s, y3s]
  (repeat rw [writeXmm128_ne true _ (by decide)])
  rw [writeXmm128_true_lo, hx0Sum]

/-- **Kernel-Checked Equivalence Proof for `gcc 15.2.0 -O3 -mavx2` `c_dot_u8_u16`:**
    Proves all execution paths (`len = 0`, `1 ≤ len ≤ 31` direct entry to epilogue,
    `32`-element AVX2 hot loop + horizontal `vextracti128`/`vpsrldq` reduction,
    clean `vzeroupper; ret` when `32 ∣ len`, and `vmovdqa; vzeroupper` cascade into
    `16`-elem VEX-128 -> `8`-elem `vpmulld` -> `1..7`-elem scalar tail) match
    `RustDotU8U16Post` with `SysVCalleeSavedPreserved` and `UpperYmmCleanOrPreserved`. -/
theorem prove_c_dot_u8_u16_o3_avx2 :
    CObjectMatchesRustContract cFfiKernelsO3Avx2Obj 0x140#64 (DotU8U16Pre 0) (DotU8U16Post 0) := by
  intro s0 nd hrun hnf hrip hpre
  have h2len := hpre.1
  have hlenLt := (s0.regs .rdx).isLt
  have hcs0 : SysVCalleeSavedPreserved s0 s0 := ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩
  have hcm : objCodeMap cFfiKernelsO3Avx2Obj = dotO3Cmap := rfl
  by_cases hlen0 : (s0.regs .rdx).toNat = 0
  · have hdx0 : s0.regs .rdx = 0#64 := BitVec.eq_of_toNat_eq hlen0
    have hzf : evalCond .e (evalAluN (by decide) .test (s0.regs .rdx) (s0.regs .rdx) s0.flags (nd 0).flags).2 = true := by
      rw [evalCond_e_of_zf_true (by rw [test_flags_zf, hdx0]; rfl)]
    have hsf : runFrom dotO3Cmap 4 0 nd s0 =
        { s0 with
          rip := 0x400432#64,
          regs := regUpd s0.regs .rax 0#64,
          flags := (evalAluN (by decide) .xor (BitVec.extractLsb' 0 32 (s0.regs .rax)) (BitVec.extractLsb' 0 32 (s0.regs .rax))
                     (evalAluN (by decide) .test (s0.regs .rdx) (s0.regs .rdx) s0.flags (nd 0).flags).2
                     (nd 2).flags).2,
          halted := true } := by
      rw [runFrom_succ, step_at_concrete dotO3_test _ s0 hrun hnf hrip, exec_aluRmReg_s64_test]
      rw [runFrom_succ, step_at_concrete dotO3_je0 _ { s0 with rip := 0x400140#64 + BitVec.ofNat 64 3, flags := _ } hrun hnf rfl, exec_jcc_taken hzf]
      rw [runFrom_succ, step_at_concrete dotO3_zero_xor _ { s0 with rip := 0x400143#64 + BitVec.ofNat 64 6 + 0x2e7#64, flags := _ } hrun hnf rfl, exec_aluRmReg_s32_xor_self]
      rw [runFrom_succ, step_at_concrete dotO3_zero_ret _ { s0 with rip := 0x400430#64 + BitVec.ofNat 64 2, regs := _, flags := _ } hrun hnf rfl, exec_ret, runFrom_zero]
      rfl
    refine ⟨4, ?_⟩
    rw [runX64_eq_runFrom, hcm, hsf]
    refine ⟨rfl, hnf, by unfold SysVCalleeSavedPreserved; dsimp only; exact cs_step_caller (r := .rax) rfl hcs0, fun hc => hc, ?_, fun _ _ => rfl⟩
    dsimp only; rw [regUpd_eq, hlen0]; rfl
  · have hlenPos : 0 < (s0.regs .rdx).toNat := by omega
    have hzf : evalCond .e (evalAluN (by decide) .test (s0.regs .rdx) (s0.regs .rdx) s0.flags (nd 0).flags).2 = false :=
      evalCond_e_of_zf_false (by rw [test_flags_zf, test64_self_zero_eq]; simp [hlen0])
    let s1 := runFrom dotO3Cmap 2 0 nd s0
    have hs1 : s1 = { s0 with rip := 0x400149#64, flags := (evalAluN (by decide) .test (s0.regs .rdx) (s0.regs .rdx) s0.flags (nd 0).flags).2 } := by
      dsimp only [s1]
      rw [runFrom_succ, step_at_concrete dotO3_test _ s0 hrun hnf hrip, exec_aluRmReg_s64_test]
      rw [runFrom_succ, step_at_concrete dotO3_je0 _ { s0 with rip := 0x400140#64 + BitVec.ofNat 64 3, flags := _ } hrun hnf rfl, exec_jcc_fall hzf, runFrom_zero]
      rfl
    rcases runFrom_of_decodeSeqAt dotO3_lenChk_dec 2 nd s1 (by rw [hs1]; exact hrun) (by rw [hs1]; exact hnf) (by rw [hs1]) with ⟨hlc, hrunL, hnfL⟩
    have heLen : execInstrSeq 2 dotO3_lenChkSeq 2 nd s1 =
        { s1 with
          rip := 0x400151#64,
          regs := regUpd s1.regs .rax (s0.regs .rdx + 0xffffffffffffffff#64),
          flags := (evalAluN (by decide) .cmp (s0.regs .rdx + 0xffffffffffffffff#64) 0x1e#64 s1.flags (nd 3).flags).2 } := by
      dsimp only [dotO3_lenChkSeq]
      rw [execInstrSeq_succ_cons, exec_lea_s64, evalByteAddr_base_disp, show s1.regs .rdx = s0.regs .rdx by rw [hs1]]
      rw [execInstrSeq_succ_cons, exec_aluImm_s64_cmp, execInstrSeq_zero]
      dsimp only; rw [regUpd_eq]
    have hbe31 := bv64_sub1_cmp_be (s0.regs .rdx) 30 hlenPos (by decide)
    by_cases hle31 : (s0.regs .rdx).toNat ≤ 31
    · have hcc31 : evalCond .be (execInstrSeq 2 dotO3_lenChkSeq 2 nd s1).flags = true := by
        rw [heLen]; dsimp only; rw [evalCond_be_of_flags, cmp_flags_cf, cmp_flags_zf]
        change (decide ((s0.regs .rdx + 0xffffffffffffffff#64).toNat < 30) || ((s0.regs .rdx + 0xffffffffffffffff#64) - BitVec.ofNat 64 30 == 0#64)) = true
        rw [hbe31]; simp [hle31]
      let s2 := runFrom dotO3Cmap 3 2 nd s1
      have hs2 : s2 = { execInstrSeq 2 dotO3_lenChkSeq 2 nd s1 with rip := 0x400433#64 } := by
        dsimp only [s2]
        rw [show (3 : Nat) = 2 + 1 by rfl, runFrom_add, hlc, runFrom_succ,
            step_at_concrete dotO3_lenChk_jbe _ _ hrunL hnfL (by rw [heLen]), exec_jcc_taken hcc31, runFrom_zero]
        rw [heLen]; rfl
      rcases runFrom_of_decodeSeqAt dotO3_skip32_dec 5 nd s2
        (by rw [hs2, heLen, hs1]; exact hrun) (by rw [hs2, heLen, hs1]; exact hnf) (by rw [hs2]) with ⟨hsk, hrunSk, hnfSk⟩
      have heSk : execInstrSeq 3 dotO3_skip32Seq 5 nd s2 =
          { s2 with
            rip := 0x40043c#64,
            regs := regUpd (regUpd s2.regs .r9 0#64) .rax 0#64,
            ymms := writeXmm128 true s2.ymms y2 0#128,
            flags := (evalAluN (by decide) .xor (BitVec.extractLsb' 0 32 (s2.regs .rax)) (BitVec.extractLsb' 0 32 (s2.regs .rax))
                       (evalAluN (by decide) .xor (BitVec.extractLsb' 0 32 (s2.regs .r9)) (BitVec.extractLsb' 0 32 (s2.regs .r9))
                         s2.flags (nd 6).flags).2 (nd 7).flags).2 } := by
        dsimp only [dotO3_skip32Seq]
        rw [execInstrSeq_succ_cons, exec_simdBitwise_vex128_xor_self]
        rw [execInstrSeq_succ_cons, exec_aluRmReg_s32_xor_self]
        rw [execInstrSeq_succ_cons, exec_aluRmReg_s32_xor_self, execInstrSeq_zero]
        dsimp only; rw [regUpd_ne _ (by decide)]
      let s3 := runFrom dotO3Cmap 4 5 nd s2
      have hs3 : s3 = { execInstrSeq 3 dotO3_skip32Seq 5 nd s2 with rip := 0x400211#64 } := by
        dsimp only [s3]
        rw [show (4 : Nat) = 3 + 1 by rfl, runFrom_add, hsk, runFrom_succ,
            step_at_concrete dotO3_skip32_jmp _ _ hrunSk hnfSk (by rw [heSk]), exec_jmp, runFrom_zero]
        rw [heSk]; rfl
      have hcs3 : SysVCalleeSavedPreserved s0 s3 := by
        unfold SysVCalleeSavedPreserved at hcs0 ⊢; rw [hs3, heSk, hs2, heLen, hs1]; dsimp only
        exact cs_step_caller (r := .rax) rfl (cs_step_caller (r := .r9) rfl (cs_step_caller (r := .rax) rfl hcs0))
      have hym3 : UpperYmmCleanOrPreserved s0 s3 := fun hc => by
        rw [hs3, heSk]; exact writeXmm128_true_preserves_clean _ _ _ (by rw [hs2, heLen, hs1]; exact hc)
      have hEpi := dotO3_epi16_0x211 s0 s3 0 9 nd hpre
        (by rw [hs3, heSk, hs2, heLen, hs1]; exact hrun) (by rw [hs3, heSk, hs2, heLen, hs1]; exact hnf) (by rw [hs3])
        (by rw [hs3, heSk, hs2, heLen, hs1])
        (by rw [hs3, heSk, hs2, heLen, hs1]; dsimp only; repeat rw [regUpd_ne _ (by decide)])
        (by rw [hs3, heSk, hs2, heLen, hs1]; dsimp only; repeat rw [regUpd_ne _ (by decide)])
        (by rw [hs3, heSk, hs2, heLen, hs1]; dsimp only; repeat rw [regUpd_ne _ (by decide)])
        (by rw [hs3, heSk]; dsimp only; rw [regUpd_ne _ (by decide), regUpd_eq])
        (by rw [hs3, heSk]; dsimp only; rw [regUpd_eq]; rfl)
        (by rw [hs3, heSk]; dsimp only; rw [writeXmm128_true_lo, sumDwords128_zero]; rfl)
        hcs3 hym3 hlenPos (by omega)
      rcases hEpi with ⟨k, hk⟩
      refine ⟨9 + k, ?_⟩
      rw [runX64_eq_runFrom, hcm, show 9 + k = 2 + (3 + (4 + k)) by omega, runFrom_add, runFrom_add, runFrom_add]
      simpa [Nat.add_assoc] using hk
    · have hcc31 : evalCond .be (execInstrSeq 2 dotO3_lenChkSeq 2 nd s1).flags = false := by
        rw [heLen]; dsimp only; rw [evalCond_be_of_flags, cmp_flags_cf, cmp_flags_zf]
        change (decide ((s0.regs .rdx + 0xffffffffffffffff#64).toNat < 30) || ((s0.regs .rdx + 0xffffffffffffffff#64) - BitVec.ofNat 64 30 == 0#64)) = false
        rw [hbe31]; simp [hle31]
      let s2 := runFrom dotO3Cmap 3 2 nd s1
      have hs2 : s2 = { execInstrSeq 2 dotO3_lenChkSeq 2 nd s1 with rip := 0x400157#64 } := by
        dsimp only [s2]
        rw [show (3 : Nat) = 2 + 1 by rfl, runFrom_add, hlc, runFrom_succ,
            step_at_concrete dotO3_lenChk_jbe _ _ hrunL hnfL (by rw [heLen]), exec_jcc_fall hcc31, runFrom_zero]
        rw [heLen]; rfl
      rcases runFrom_of_decodeSeqAt dotO3_avxPre_dec 5 nd s2
        (by rw [hs2, heLen, hs1]; exact hrun) (by rw [hs2, heLen, hs1]; exact hnf) (by rw [hs2]) with ⟨hap, hrunAP, hnfAP⟩
      let q : Nat := (s0.regs .rdx).toNat / 32
      have hqPos : 1 ≤ q := by dsimp only [q]; omega
      have hqBound : q * 32 ≤ (s0.regs .rdx).toNat := by dsimp only [q]; omega
      have hmask32 : s0.regs .rdx &&& 0xffffffffffffffe0#64 = BitVec.ofNat 64 (q * 32) := by
        apply BitVec.eq_of_toNat_eq
        rw [bv64_and_neg32_toNat, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)]
      have heAP : execInstrSeq 6 dotO3_avxPreSeq 5 nd s2 =
          { s2 with
            rip := 0x400170#64,
            regs := regUpd (regUpd (regUpd s2.regs .r9 (s0.regs .rdx)) .rax 0#64) .r9 (BitVec.ofNat 64 (q * 32)),
            ymms := writeXmm128 true s2.ymms y3 0#128,
            flags := (evalAluN (by decide) .and (s0.regs .rdx) 0xffffffffffffffe0#64
                       (evalAluN (by decide) .xor (BitVec.extractLsb' 0 32 (s2.regs .rax)) (BitVec.extractLsb' 0 32 (s2.regs .rax))
                         s2.flags (nd 6).flags).2 (nd 8).flags).2 } := by
        dsimp only [dotO3_avxPreSeq]
        have h2dx : s2.regs .rdx = s0.regs .rdx := by rw [hs2, heLen, hs1]; dsimp only; rw [regUpd_ne _ (by decide)]
        rw [execInstrSeq_succ_cons, exec_movStore_s64_reg, h2dx]
        rw [execInstrSeq_succ_cons, exec_aluRmReg_s32_xor_self]
        dsimp only; rw [regUpd_ne _ (by decide)]
        rw [execInstrSeq_succ_cons, exec_simdBitwise_vex128_xor_self]
        rw [execInstrSeq_succ_cons, exec_aluImm_s64_and]
        dsimp only; rw [regUpd_ne _ (by decide), regUpd_eq, hmask32]
        rw [execInstrSeq_succ_cons, exec_nop, execInstrSeq_succ_cons, exec_nop, execInstrSeq_zero]
      let s3 := runFrom dotO3Cmap 6 5 nd s2
      have hs3 : s3 = execInstrSeq 6 dotO3_avxPreSeq 5 nd s2 := hap
      have hcs3 : SysVCalleeSavedPreserved s0 s3 := by
        unfold SysVCalleeSavedPreserved at hcs0 ⊢; rw [hs3, heAP, hs2, heLen, hs1]; dsimp only
        exact cs_step_caller (r := .r9) rfl (cs_step_caller (r := .rax) rfl
          (cs_step_caller (r := .r9) rfl (cs_step_caller (r := .rax) rfl hcs0)))
      have hy3Zero : sumDwords256 (s3.ymms y3) = 0#32 := by
        rw [hs3, heAP]; dsimp only; rw [writeXmm128_true_eq, ymmUpd_eq]
        exact sumDwords256_zero
      have hAvx := dotO3_avx_loop s0 hpre nd q (q - 1) 11 s3
        (by omega) hqBound (by rw [hs3]; exact hrunAP) (by rw [hs3]; exact hnfAP) (by rw [hs3, heAP])
        (by rw [hs3, heAP, hs2, heLen, hs1])
        (by rw [hs3, heAP, hs2, heLen, hs1]; dsimp only; repeat rw [regUpd_ne _ (by decide)])
        (by rw [hs3, heAP, hs2, heLen, hs1]; dsimp only; repeat rw [regUpd_ne _ (by decide)])
        (by rw [hs3, heAP, hs2, heLen, hs1]; dsimp only; repeat rw [regUpd_ne _ (by decide)])
        (by rw [hs3, heAP]; dsimp only; exact regUpd_eq _ _ _)
        (by rw [hs3, heAP]; dsimp only; rw [regUpd_ne _ (by decide), regUpd_eq, show (q - (q - 1 + 1)) * 32 = 0 by omega])
        (by rw [hy3Zero, show (q - (q - 1 + 1)) * 32 = 0 by omega]; rfl)
        hcs3
      generalize hs4 : runFrom dotO3Cmap (25 * (q - 1 + 1)) 11 nd s3 = s4 at hAvx
      rcases hAvx with ⟨h4r, h4f, h4rip, h4m, h4di, h4si, h4dx, h4r9, h4y3, h4cs⟩
      let idx4 := 11 + 25 * (q - 1 + 1)
      have hH := dotO3_horiz_step s4 idx4 nd h4r h4f h4rip
      generalize hsH : runFrom dotO3Cmap 8 idx4 nd s4 = sH at hH
      rcases hH with ⟨hHr, hHf, hHrip, hHm, hHregs, hHy0, hHfl⟩
      rw [h4y3] at hHregs hHy0
      rw [h4dx, h4r9] at hHfl
      have hHcs : SysVCalleeSavedPreserved s0 sH := by
        unfold SysVCalleeSavedPreserved at h4cs ⊢; rw [hHregs]; exact cs_step_caller (r := .rax) rfl h4cs
      have hrunH : runFrom dotO3Cmap (idx4 + 8) 0 nd s0 = sH := by
        rw [show idx4 + 8 = 2 + (3 + (6 + (25 * (q - 1 + 1) + 8))) by dsimp only [idx4]; omega,
            runFrom_add, runFrom_add, runFrom_add, runFrom_add, hs4, hsH]
      by_cases hmod32 : (s0.regs .rdx).toNat = q * 32
      · have hdxEq : s0.regs .rdx = BitVec.ofNat 64 (q * 32) := by
          rw [← hmod32, BitVec.ofNat_toNat, BitVec.setWidth_eq]
        have hcc32 : evalCond .e sH.flags = true := by
          rw [hHfl]; exact evalCond_e_of_zf_true (by rw [cmp_flags_zf, ← hdxEq, cmp_sub_self_zero])
        have hsf : runFrom dotO3Cmap 3 (idx4 + 8) nd sH =
            { sH with rip := 0x400426#64, ymms := vzeroUpperAll sH.ymms, halted := true } := by
          rw [runFrom_succ, step_at_concrete dotO3_horiz_je _ sH hHr hHf hHrip, exec_jcc_taken hcc32]
          rw [runFrom_succ, step_at_concrete dotO3_vzu423 _ { sH with rip := 0x400204#64 + BitVec.ofNat 64 6 + 0x219#64 } hHr hHf rfl, exec_vzeroupper]
          rw [runFrom_succ, step_at_concrete dotO3_ret426 _ { sH with rip := 0x400423#64 + BitVec.ofNat 64 3, ymms := _ } hHr hHf rfl, exec_ret, runFrom_zero]
          rfl
        refine ⟨idx4 + 11, ?_⟩
        rw [runX64_eq_runFrom, hcm, show idx4 + 11 = (idx4 + 8) + 3 by omega, runFrom_add, hrunH,
            show 0 + (idx4 + 8) = idx4 + 8 by omega, hsf]
        refine ⟨rfl, hHf, hHcs, fun _ => vzeroUpperAll_clean _, ?_, fun _ _ => by rw [hHm, h4m]⟩
        dsimp only; rw [hHregs, regUpd_eq, zext32_extract32_eq, hmod32]; rfl
      · have hdxNe : s0.regs .rdx ≠ BitVec.ofNat 64 (q * 32) := fun heq => by
          have ht := congrArg BitVec.toNat heq
          rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)] at ht; exact hmod32 ht
        have hcc32 : evalCond .e sH.flags = false := by
          rw [hHfl]; exact evalCond_e_of_zf_false (by rw [cmp_flags_zf, cmp_sub_zero_false_of_ne hdxNe])
        let s5 := runFrom dotO3Cmap 1 (idx4 + 8) nd sH
        have hs5 : s5 = { sH with rip := 0x40020a#64 } := by
          dsimp only [s5]; rw [runFrom_succ, step_at_concrete dotO3_horiz_je _ sH hHr hHf hHrip, exec_jcc_fall hcc32, runFrom_zero]; rfl
        rcases runFrom_of_decodeSeqAt dotO3_toEpi16_dec (idx4 + 9) nd s5
          (by rw [hs5]; exact hHr) (by rw [hs5]; exact hHf) (by rw [hs5]) with ⟨hto, hrunT, hnfT⟩
        have heTo : execInstrSeq 2 dotO3_toEpi16Seq (idx4 + 9) nd s5 =
            { s5 with rip := 0x400211#64, ymms := vzeroUpperAll (writeXmm128 true s5.ymms y2 (BitVec.extractLsb' 0 128 (s5.ymms y0))) } := by
          dsimp only [dotO3_toEpi16Seq]
          rw [execInstrSeq_succ_cons, exec_simdMovLoad_vex128_reg]
          rw [execInstrSeq_succ_cons, exec_vzeroupper, execInstrSeq_zero]
        let s6 := runFrom dotO3Cmap 2 (idx4 + 9) nd s5
        have hs6 : s6 = execInstrSeq 2 dotO3_toEpi16Seq (idx4 + 9) nd s5 := hto
        have hEpi := dotO3_epi16_0x211 s0 s6 (q * 32) (idx4 + 11) nd hpre
          (by rw [hs6]; exact hrunT) (by rw [hs6]; exact hnfT) (by rw [hs6, heTo])
          (by rw [hs6, heTo, hs5, hHm, h4m])
          (by rw [hs6, heTo, hs5, hHregs, regUpd_ne _ (by decide), h4di])
          (by rw [hs6, heTo, hs5, hHregs, regUpd_ne _ (by decide), h4si])
          (by rw [hs6, heTo, hs5, hHregs, regUpd_ne _ (by decide), h4dx])
          (by rw [hs6, heTo, hs5, hHregs, regUpd_ne _ (by decide), h4r9])
          (by rw [hs6, heTo, hs5, hHregs, regUpd_eq, zext32_extract32_eq])
          (by rw [hs6, heTo]; dsimp only; rw [vzeroUpperAll_lo128, writeXmm128_true_lo, hs5, hHy0])
          (by unfold SysVCalleeSavedPreserved at hHcs ⊢; rw [hs6, heTo, hs5]; exact hHcs)
          (fun _ => by rw [hs6, heTo]; exact vzeroUpperAll_clean _)
          (by omega) (by dsimp only [q]; omega)
        rcases hEpi with ⟨k, hk⟩
        refine ⟨idx4 + 11 + k, ?_⟩
        rw [runX64_eq_runFrom, hcm, show idx4 + 11 + k = (idx4 + 8) + (1 + (2 + k)) by omega,
            runFrom_add, hrunH, show 0 + (idx4 + 8) = idx4 + 8 by omega, runFrom_add, runFrom_add]
        simpa [Nat.add_assoc] using hk

end UntrustedCObjDotAvx2
