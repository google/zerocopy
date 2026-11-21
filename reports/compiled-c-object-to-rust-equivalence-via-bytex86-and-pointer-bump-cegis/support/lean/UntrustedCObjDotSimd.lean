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

/-!
# `UntrustedCObjDotSimd`

Kernel-checked equivalence proof for `gcc 15.2.0 -O2` `c_dot_u8_u16`
(`cFfiKernelsO2Obj` at `0x140`, `stackReserve = 0`, `0` `sorry`, `0` `isPartial`):
- `len = 0` early return (`0x400220`)
- `1 ≤ len ≤ 15` direct jump (`0x400225 -> 0x400200`) to scalar tail loop
- `len ≥ 16`: legacy non-VEX SSE2 `16`-element widening dot-product loop
  (`0x400170..0x4001d5`, `punpck{h,l}bw` + `pmullw`/`pmulhuw` + `punpck{h,l}wd`
  + `paddd`), horizontal `psrldq 8`/`4` reduction (`0x4001d5..0x4001f6`), and
  scalar tail loop (`0x400200..0x40021b`). Every legacy SSE2 op preserves
  `bits[255:128]` of all 16 YMM registers verbatim (`writeXmm128_false_preserves_hi`).
-/

namespace UntrustedCObjDotSimd

open ByteX86Gcc
open RustFfiSpecs
open CompiledCObjImages
open UntrustedCObjHints
open UntrustedCObjSimdHelpers

private def dotO2Cmap : CodeMap := objCodeMap cFfiKernelsO2Obj

private abbrev y0 : YmmIdx := ⟨0, by decide⟩
private abbrev y1 : YmmIdx := ⟨1, by decide⟩
private abbrev y2 : YmmIdx := ⟨2, by decide⟩
private abbrev y3 : YmmIdx := ⟨3, by decide⟩
private abbrev y4 : YmmIdx := ⟨4, by decide⟩
private abbrev y5 : YmmIdx := ⟨5, by decide⟩
private abbrev y6 : YmmIdx := ⟨6, by decide⟩

/-! ## Section 1: Pure-Bool Reflected Decodes for `c_dot_u8_u16 -O2` -/

private def dotO2_entrySeq : List (X64Instr × BitVec 64) := [
  (.movStore .s64 (.reg .r9) .rdx, 0x400143#64),
  (.aluRmReg .s64 .test (.reg .rdx) .rdx, 0x400146#64)
]
private theorem dotO2_entry_dec : decodeSeqAt dotO2Cmap 2 0x400140#64 = some dotO2_entrySeq :=
  decodeSeqAt_of_check rfl rfl
private theorem dotO2_entry_je : decodeX64 (fetchWindow16 dotO2Cmap 0x400146#64) =
    .ok (.jccRel .e 0x00000000000000d4#64) 6 := decodeAt_of_check rfl

private def dotO2_zeroSeq : List (X64Instr × BitVec 64) := [
  (.aluRmReg .s32 .xor (.reg .rdx) .rdx, 0x400222#64),
  (.movStore .s32 (.reg .rax) .rdx, 0x400224#64)
]
private theorem dotO2_zero_dec : decodeSeqAt dotO2Cmap 2 0x400220#64 = some dotO2_zeroSeq :=
  decodeSeqAt_of_check rfl rfl
private theorem dotO2_zero_ret : decodeX64 (fetchWindow16 dotO2Cmap 0x400224#64) =
    .ok .ret64 1 := decodeAt_of_check rfl

private def dotO2_lenChkSeq : List (X64Instr × BitVec 64) := [
  (.lea .s64 .rax { base := some .rdx, disp := 0xffffffffffffffff#64 }, 0x400150#64),
  (.aluImm .s64 .cmp (.reg .rax) 0x0e#64, 0x400154#64)
]
private theorem dotO2_lenChk_dec : decodeSeqAt dotO2Cmap 2 0x40014c#64 = some dotO2_lenChkSeq :=
  decodeSeqAt_of_check rfl rfl
private theorem dotO2_lenChk_jbe : decodeX64 (fetchWindow16 dotO2Cmap 0x400154#64) =
    .ok (.jccRel .be 0x00000000000000cb#64) 6 := decodeAt_of_check rfl

private def dotO2_smallSeq : List (X64Instr × BitVec 64) := [
  (.aluRmReg .s32 .xor (.reg .rax) .rax, 0x400227#64),
  (.aluRmReg .s32 .xor (.reg .rdx) .rdx, 0x400229#64)
]
private theorem dotO2_small_dec : decodeSeqAt dotO2Cmap 2 0x400225#64 = some dotO2_smallSeq :=
  decodeSeqAt_of_check rfl rfl
private theorem dotO2_small_jmp : decodeX64 (fetchWindow16 dotO2Cmap 0x400229#64) =
    .ok (.jmpRel 0xffffffffffffffd5#64) 2 := decodeAt_of_check rfl

private def dotO2_simdPreSeq : List (X64Instr × BitVec 64) := [
  (.movStore .s64 (.reg .rax) .rdx, 0x40015d#64),
  (.simdBitwise .legacy128 .xor y3 y3 (.reg y3), 0x400161#64),
  (.simdBitwise .legacy128 .xor y6 y6 (.reg y6), 0x400165#64),
  (.aluRmReg .s32 .xor (.reg .rdx) .rdx, 0x400167#64),
  (.aluImm .s64 .and (.reg .rax) 0xfffffffffffffff0#64, 0x40016b#64),
  (.nop, 0x400170#64)
]
private theorem dotO2_simdPre_dec : decodeSeqAt dotO2Cmap 6 0x40015a#64 = some dotO2_simdPreSeq :=
  decodeSeqAt_of_check rfl rfl

private def dotO2_bodyASeq : List (X64Instr × BitVec 64) := [
  (.simdMovLoad .legacy128 y5 (.mem { base := some .rsi, index := some (.rdx, 1), disp := 0x10#64 }), 0x400176#64),
  (.simdMovLoad .legacy128 y1 (.mem { base := some .rdi, index := some (.rdx, 0) }), 0x40017b#64),
  (.simdMovLoad .legacy128 y4 (.mem { base := some .rsi, index := some (.rdx, 1) }), 0x400180#64),
  (.aluImm .s64 .add (.reg .rdx) 0x10#64, 0x400184#64),
  (.simdMovLoad .legacy128 y2 (.reg y1), 0x400188#64),
  (.simdMovLoad .legacy128 y0 (.reg y5), 0x40018c#64),
  (.simdUnpack .legacy128 .hbw y1 y1 (.reg y6), 0x400190#64)
]
private theorem dotO2_bodyA_dec : decodeSeqAt dotO2Cmap 7 0x400170#64 = some dotO2_bodyASeq :=
  decodeSeqAt_of_check rfl rfl

private def dotO2_bodyBSeq : List (X64Instr × BitVec 64) := [
  (.simdPmullw .legacy128 y0 y0 (.reg y1), 0x400194#64),
  (.simdPmulhuw .legacy128 y1 y1 (.reg y5), 0x400198#64),
  (.simdUnpack .legacy128 .lbw y2 y2 (.reg y6), 0x40019c#64),
  (.simdMovLoad .legacy128 y5 (.reg y0), 0x4001a0#64),
  (.simdUnpack .legacy128 .hwd y0 y0 (.reg y1), 0x4001a4#64),
  (.simdUnpack .legacy128 .lwd y5 y5 (.reg y1), 0x4001a8#64),
  (.simdMovLoad .legacy128 y1 (.reg y4), 0x4001ac#64),
  (.simdPmullw .legacy128 y1 y1 (.reg y2), 0x4001b0#64)
]
private theorem dotO2_bodyB_dec : decodeSeqAt dotO2Cmap 8 0x400190#64 = some dotO2_bodyBSeq :=
  decodeSeqAt_of_check rfl rfl

private def dotO2_bodyCSeq : List (X64Instr × BitVec 64) := [
  (.simdPmulhuw .legacy128 y2 y2 (.reg y4), 0x4001b4#64),
  (.simdAdd .legacy128 .e32 y0 y0 (.reg y5), 0x4001b8#64),
  (.simdMovLoad .legacy128 y4 (.reg y1), 0x4001bc#64),
  (.simdUnpack .legacy128 .hwd y1 y1 (.reg y2), 0x4001c0#64),
  (.simdUnpack .legacy128 .lwd y4 y4 (.reg y2), 0x4001c4#64),
  (.simdAdd .legacy128 .e32 y1 y1 (.reg y4), 0x4001c8#64),
  (.simdAdd .legacy128 .e32 y0 y0 (.reg y1), 0x4001cc#64),
  (.simdAdd .legacy128 .e32 y3 y3 (.reg y0), 0x4001d0#64),
  (.aluRmReg .s64 .cmp (.reg .rdx) .rax, 0x4001d3#64)
]
private theorem dotO2_bodyC_dec : decodeSeqAt dotO2Cmap 9 0x4001b0#64 = some dotO2_bodyCSeq :=
  decodeSeqAt_of_check rfl rfl
private theorem dotO2_loop_jne : decodeX64 (fetchWindow16 dotO2Cmap 0x4001d3#64) =
    .ok (.jccRel .ne 0xffffffffffffff9b#64) 2 := decodeAt_of_check rfl

private def dotO2_horizSeq : List (X64Instr × BitVec 64) := [
  (.simdMovLoad .legacy128 y0 (.reg y3), 0x4001d9#64),
  (.simdPsrldq .legacy128 y0 y0 0x08#8, 0x4001de#64),
  (.simdAdd .legacy128 .e32 y3 y3 (.reg y0), 0x4001e2#64),
  (.simdMovLoad .legacy128 y0 (.reg y3), 0x4001e6#64),
  (.simdPsrldq .legacy128 y0 y0 0x04#8, 0x4001eb#64),
  (.simdAdd .legacy128 .e32 y3 y3 (.reg y0), 0x4001ef#64),
  (.simdMovXToGpr false false (.reg .rdx) y3, 0x4001f3#64),
  (.aluRmReg .s64 .cmp (.reg .r9) .rax, 0x4001f6#64)
]
private theorem dotO2_horiz_dec : decodeSeqAt dotO2Cmap 8 0x4001d5#64 = some dotO2_horizSeq :=
  decodeSeqAt_of_check rfl rfl
private theorem dotO2_horiz_je : decodeX64 (fetchWindow16 dotO2Cmap 0x4001f6#64) =
    .ok (.jccRel .e 0x0000000000000020#64) 2 := decodeAt_of_check rfl
private theorem dotO2_horiz_nop : decodeX64 (fetchWindow16 dotO2Cmap 0x4001f8#64) =
    .ok .nop 8 := decodeAt_of_check rfl

private def dotO2_tailSeq : List (X64Instr × BitVec 64) := [
  (.movzx16 .s32 .rcx (.mem { base := some .rsi, index := some (.rax, 1) }), 0x400204#64),
  (.movzx8 .s32 .r8 (.mem8 { base := some .rdi, index := some (.rax, 0) }), 0x400209#64),
  (.aluImm .s64 .add (.reg .rax) 1#64, 0x40020d#64),
  (.imul2 .s32 .rcx (.reg .r8), 0x400211#64),
  (.aluRmReg .s32 .add (.reg .rdx) .rcx, 0x400213#64),
  (.aluRmReg .s64 .cmp (.reg .rax) .r9, 0x400216#64)
]
private theorem dotO2_tail_dec : decodeSeqAt dotO2Cmap 6 0x400200#64 = some dotO2_tailSeq :=
  decodeSeqAt_of_check rfl rfl
private theorem dotO2_tail_jb : decodeX64 (fetchWindow16 dotO2Cmap 0x400216#64) =
    .ok (.jccRel .b 0xffffffffffffffe8#64) 2 := decodeAt_of_check rfl
private theorem dotO2_ret_mov : decodeX64 (fetchWindow16 dotO2Cmap 0x400218#64) =
    .ok (.movStore .s32 (.reg .rax) .rdx) 2 := decodeAt_of_check rfl
private theorem dotO2_ret_ret : decodeX64 (fetchWindow16 dotO2Cmap 0x40021a#64) =
    .ok .ret64 1 := decodeAt_of_check rfl

/-! ## Section 2: `16`-Elem SSE2 Widening Dot-Product Algebra & Scalar Tail -/

private theorem pmulhuw128_comm (x y : BitVec 128) :
    pmulhuw128 x y = pmulhuw128 y x := by
  unfold pmulhuw128
  congr 1; funext i; rw [Nat.mul_comm]

private theorem dot16_sse2_algebra (m : ByteMem) (pa pb : BitVec 64) (acc : BitVec 32) :
    let a128 := readMem128 m pa
    let bLo  := readMem128 m pb
    let bHi  := readMem128 m (pb + 16#64)
    let aHi16 := unpack128 .hbw a128 0#128
    let aLo16 := unpack128 .lbw a128 0#128
    let loHi := pmullw128 bHi aHi16
    let hiHi := pmulhuw128 aHi16 bHi
    let loLo := pmullw128 bLo aLo16
    let hiLo := pmulhuw128 aLo16 bLo
    let vHi  := packDwords128 fun i => getDword128 (unpack128 .hwd loHi hiHi) i + getDword128 (unpack128 .lwd loHi hiHi) i
    let vLo  := packDwords128 fun i => getDword128 (unpack128 .hwd loLo hiLo) i + getDword128 (unpack128 .lwd loLo hiLo) i
    let v16  := packDwords128 fun i => getDword128 vHi i + getDword128 vLo i
    acc + sumDwords128 v16 = rustDotU8U16From m pa pb 16 acc := by
  dsimp only
  rw [sumDwords128_paddd, sumDwords128_paddd, sumDwords128_paddd]
  rw [pmulhuw128_comm (unpack128 .hbw (readMem128 m pa) 0#128) (readMem128 m (pb + 16#64)),
      pmulhuw128_comm (unpack128 .lbw (readMem128 m pa) 0#128) (readMem128 m pb)]
  rw [sumDwords128_unpack_mul_pair, sumDwords128_unpack_mul_pair]
  rw [show rustDotU8U16From m pa pb 16 acc = rustDotU8U16From m pa pb (8 + 8) acc from rfl,
      rustDotU8U16From_split, rustDotU8U16From_8, rustDotU8U16From_8]
  have hcomm : ∀ x y : BitVec 32, x * y = y * x := BitVec.mul_comm
  have hlo : ∀ i : Fin 8,
      (getWord128 (readMem128 m pb) i).zeroExtend 32 *
        (getWord128 (unpack128 .lbw (readMem128 m pa) 0#128) i).zeroExtend 32 =
      (m (pa + BitVec.ofNat 64 i.val)).zeroExtend 32 * (readMem16 m (pb + BitVec.ofNat 64 (2 * i.val))).zeroExtend 32 := by
    intro i
    rw [getWord128_unpack_lbw_zero, zext8_16_32_eq, readMem128_byte_at, readMem128_word_at, hcomm]
  have hhi : ∀ i : Fin 8,
      (getWord128 (readMem128 m (pb + 16#64)) i).zeroExtend 32 *
        (getWord128 (unpack128 .hbw (readMem128 m pa) 0#128) i).zeroExtend 32 =
      (m ((pa + 8#64) + BitVec.ofNat 64 i.val)).zeroExtend 32 *
        (readMem16 m ((pb + 16#64) + BitVec.ofNat 64 (2 * i.val))).zeroExtend 32 := by
    intro i
    rw [getWord128_unpack_hbw_zero, zext8_16_32_eq, readMem128_byte_at, readMem128_word_at, hcomm]
    have ha : pa + BitVec.ofNat 64 (8 + i.val) = (pa + 8#64) + BitVec.ofNat 64 i.val :=
      (bv64_add_ofNat_assoc pa 8 i.val).symm
    rw [ha]
  rw [hhi ⟨0, by decide⟩, hhi ⟨1, by decide⟩, hhi ⟨2, by decide⟩, hhi ⟨3, by decide⟩,
      hhi ⟨4, by decide⟩, hhi ⟨5, by decide⟩, hhi ⟨6, by decide⟩, hhi ⟨7, by decide⟩]
  rw [hlo ⟨0, by decide⟩, hlo ⟨1, by decide⟩, hlo ⟨2, by decide⟩, hlo ⟨3, by decide⟩,
      hlo ⟨4, by decide⟩, hlo ⟨5, by decide⟩, hlo ⟨6, by decide⟩, hlo ⟨7, by decide⟩]
  dsimp only
  rw [BitVec.add_comm (n := 32) (_ + _ + _ + _ + _ + _ + _ + _), ← BitVec.add_assoc]

private theorem dotO2_scalar_tail_step (s0 s : X64State) (done idx : Nat) (nd : Nat → UndefChoice)
    (hpre : DotU8U16Pre 0 s0)
    (hrun : s.halted = false) (hnf : s.fault = false) (hrip : s.rip = 0x400200#64)
    (hmem : s.mem = s0.mem)
    (hrdi : s.regs .rdi = s0.regs .rdi) (hrsi : s.regs .rsi = s0.regs .rsi)
    (hr9 : s.regs .r9 = s0.regs .rdx)
    (hrax : s.regs .rax = BitVec.ofNat 64 done)
    (hrdx : BitVec.extractLsb' 0 32 (s.regs .rdx) = rustDotU8U16From s0.mem (s0.regs .rdi) (s0.regs .rsi) done 0#32)
    (hcs : SysVCalleeSavedPreserved s0 s)
    (hymm : ∀ r : YmmIdx, BitVec.extractLsb' 128 128 (s.ymms r) = BitVec.extractLsb' 128 128 (s0.ymms r))
    (hlt : done < (s0.regs .rdx).toNat) :
    let s' := runFrom dotO2Cmap 7 idx nd s
    s'.halted = false ∧ s'.fault = false ∧
    s'.rip = (if done + 1 < (s0.regs .rdx).toNat then 0x400200#64 else 0x400218#64) ∧
    s'.mem = s0.mem ∧
    s'.regs .rdi = s0.regs .rdi ∧ s'.regs .rsi = s0.regs .rsi ∧ s'.regs .r9 = s0.regs .rdx ∧
    s'.regs .rax = BitVec.ofNat 64 (done + 1) ∧
    BitVec.extractLsb' 0 32 (s'.regs .rdx) = rustDotU8U16From s0.mem (s0.regs .rdi) (s0.regs .rsi) (done + 1) 0#32 ∧
    SysVCalleeSavedPreserved s0 s' ∧
    (∀ r : YmmIdx, BitVec.extractLsb' 128 128 (s'.ymms r) = BitVec.extractLsb' 128 128 (s0.ymms r)) := by
  have h2len : 2 * (s0.regs .rdx).toNat < 2 ^ 64 := hpre.1
  have hlenLt := (s0.regs .rdx).isLt
  have hshl1 : BitVec.ofNat 64 done <<< 1 = BitVec.ofNat 64 (2 * done) := by
    have htn : (BitVec.ofNat 64 done).toNat = done := by rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)]
    rw [bv64_shl1_toNat (by rw [htn]; omega), htn]
  have hadd1 : BitVec.ofNat 64 done + 1#64 = BitVec.ofNat 64 (done + 1) := by
    change BitVec.ofNat 64 done + BitVec.ofNat 64 1 = BitVec.ofNat 64 (done + 1)
    exact bv64_ofNat_add done 1
  dsimp only
  rw [show (7 : Nat) = 6 + 1 by rfl, runFrom_add]
  rcases runFrom_of_decodeSeqAt dotO2_tail_dec idx nd s hrun hnf hrip with ⟨hseq, hrun1, hnf1⟩
  rw [hseq]
  let w16 : BitVec 16 := readMem16 s0.mem (s0.regs .rsi + BitVec.ofNat 64 (2 * done))
  let b8  : BitVec 8  := s0.mem (s0.regs .rdi + BitVec.ofNat 64 done)
  let acc' : BitVec 32 := rustDotU8U16From s0.mem (s0.regs .rdi) (s0.regs .rsi) done 0#32 +
    (w16.zeroExtend 32 * b8.zeroExtend 32)
  have haccEq : acc' = rustDotU8U16From s0.mem (s0.regs .rdi) (s0.regs .rsi) (done + 1) 0#32 := by
    dsimp only [acc', w16, b8]
    rw [rustDotU8U16From_split, rustDotU8U16From_succ, rustDotU8U16From_zero]
    unfold dotStepU8U16
    rw [BitVec.mul_comm]
  have he : execInstrSeq 6 dotO2_tailSeq idx nd s =
      { s with
        rip := 0x400216#64,
        regs := regUpd (regUpd (regUpd (regUpd (regUpd s.regs .rcx (w16.zeroExtend 64))
          .r8 (b8.zeroExtend 64)) .rax (BitVec.ofNat 64 (done + 1)))
          .rcx ((w16.zeroExtend 32 * b8.zeroExtend 32).zeroExtend 64))
          .rdx (acc'.zeroExtend 64),
        flags := (evalAluN (by decide) .cmp (BitVec.ofNat 64 (done + 1)) (s0.regs .rdx)
                   (evalAluN (by decide) .add (rustDotU8U16From s0.mem (s0.regs .rdi) (s0.regs .rsi) done 0#32)
                     (w16.zeroExtend 32 * b8.zeroExtend 32)
                     (evalImulSz .s32 ((w16.zeroExtend 32).zeroExtend 64) ((b8.zeroExtend 32).zeroExtend 64) (nd (idx + 3)).flags).2
                     (nd (idx + 4)).flags).2
                   (nd (idx + 5)).flags).2 } := by
    dsimp only [dotO2_tailSeq]
    have hw16 : readMem16 s.mem (s0.regs .rsi + BitVec.ofNat 64 (2 * done)) = w16 := by rw [hmem]
    have hb8  : s.mem (s0.regs .rdi + BitVec.ofNat 64 done) = b8 := by rw [hmem]
    rw [execInstrSeq_succ_cons, exec_movzx16_s32_mem, evalByteAddr_base_idx1, hrsi, hrax, hshl1, hw16]
    rw [execInstrSeq_succ_cons, exec_movzx8_s32_mem, evalByteAddr_base_idx0]
    dsimp only; rw [regUpd_ne _ (by decide), regUpd_ne _ (by decide), hrdi, hrax, hb8]
    rw [execInstrSeq_succ_cons, exec_aluImm_s64_add]
    dsimp only; rw [regUpd_ne _ (by decide), regUpd_ne _ (by decide), hrax, hadd1]
    rw [execInstrSeq_succ_cons, exec_imul2_s32_reg]
    dsimp only
    rw [regUpd_ne _ (by decide), regUpd_ne _ (by decide), regUpd_eq, regUpd_ne _ (by decide), regUpd_eq]
    have hx16 : BitVec.extractLsb' 0 32 (w16.zeroExtend 64) = w16.zeroExtend 32 := by
      apply BitVec.eq_of_getLsbD_eq; intro b hb; unfold BitVec.zeroExtend; simp [hb, show b < 64 by omega]
    have hx8 : BitVec.extractLsb' 0 32 (b8.zeroExtend 64) = b8.zeroExtend 32 := by
      apply BitVec.eq_of_getLsbD_eq; intro b hb; unfold BitVec.zeroExtend; simp [hb, show b < 64 by omega]
    rw [hx16, hx8]
    rw [execInstrSeq_succ_cons, exec_aluRmReg_s32_add]
    dsimp only
    rw [regUpd_ne _ (by decide), regUpd_ne _ (by decide), regUpd_ne _ (by decide), regUpd_ne _ (by decide),
        regUpd_eq, hrdx, zext32_extract32_eq]
    rw [execInstrSeq_succ_cons, exec_aluRmReg_s64_cmp, execInstrSeq_zero]
    dsimp only
    rw [regUpd_ne _ (by decide), regUpd_ne _ (by decide), regUpd_eq,
        regUpd_ne _ (by decide), regUpd_ne _ (by decide), regUpd_ne _ (by decide), regUpd_ne _ (by decide),
        regUpd_ne _ (by decide), hr9]
  rw [he] at hrun1 hnf1 ⊢
  rw [runFrom_succ, step_at_concrete dotO2_tail_jb _ _ hrun1 hnf1 rfl, runFrom_zero]
  have htn1 : (BitVec.ofNat 64 (done + 1)).toNat = done + 1 := by
    rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)]
  by_cases hcont : done + 1 < (s0.regs .rdx).toNat
  · rw [exec_jcc_taken (by dsimp only; rw [evalCond_b_of_flags, cmp_flags_cf, htn1]; exact decide_eq_true hcont)]
    simp only [hcont, ite_true]
    refine ⟨hrun, hnf, rfl, hmem, ?_, ?_, ?_, ?_, ?_, ?_, hymm⟩
    · (repeat rw [regUpd_ne _ (by decide)]); exact hrdi
    · (repeat rw [regUpd_ne _ (by decide)]); exact hrsi
    · (repeat rw [regUpd_ne _ (by decide)]); exact hr9
    · rw [regUpd_ne _ (by decide), regUpd_ne _ (by decide), regUpd_eq]
    · rw [regUpd_eq, zext32_extract32_eq, haccEq]
    · unfold SysVCalleeSavedPreserved at hcs ⊢; dsimp only
      exact cs_step_caller (r := .rdx) rfl (cs_step_caller (r := .rcx) rfl
        (cs_step_caller (r := .rax) rfl (cs_step_caller (r := .r8) rfl (cs_step_caller (r := .rcx) rfl hcs))))
  · rw [exec_jcc_fall (by dsimp only; rw [evalCond_b_of_flags, cmp_flags_cf, htn1]; exact decide_eq_false hcont)]
    simp only [hcont, ite_false]
    refine ⟨hrun, hnf, rfl, hmem, ?_, ?_, ?_, ?_, ?_, ?_, hymm⟩
    · (repeat rw [regUpd_ne _ (by decide)]); exact hrdi
    · (repeat rw [regUpd_ne _ (by decide)]); exact hrsi
    · (repeat rw [regUpd_ne _ (by decide)]); exact hr9
    · rw [regUpd_ne _ (by decide), regUpd_ne _ (by decide), regUpd_eq]
    · rw [regUpd_eq, zext32_extract32_eq, haccEq]
    · unfold SysVCalleeSavedPreserved at hcs ⊢; dsimp only
      exact cs_step_caller (r := .rdx) rfl (cs_step_caller (r := .rcx) rfl
        (cs_step_caller (r := .rax) rfl (cs_step_caller (r := .r8) rfl (cs_step_caller (r := .rcx) rfl hcs))))

private theorem dotO2_scalar_tail_loop (s0 : X64State) (hpre : DotU8U16Pre 0 s0) (nd : Nat → UndefChoice) :
    ∀ (k : Nat) (idx : Nat) (s : X64State),
      k + 1 ≤ (s0.regs .rdx).toNat →
      s.halted = false → s.fault = false → s.rip = 0x400200#64 → s.mem = s0.mem →
      s.regs .rdi = s0.regs .rdi → s.regs .rsi = s0.regs .rsi → s.regs .r9 = s0.regs .rdx →
      s.regs .rax = BitVec.ofNat 64 ((s0.regs .rdx).toNat - (k + 1)) →
      BitVec.extractLsb' 0 32 (s.regs .rdx) =
        rustDotU8U16From s0.mem (s0.regs .rdi) (s0.regs .rsi) ((s0.regs .rdx).toNat - (k + 1)) 0#32 →
      SysVCalleeSavedPreserved s0 s →
      (∀ r : YmmIdx, BitVec.extractLsb' 128 128 (s.ymms r) = BitVec.extractLsb' 128 128 (s0.ymms r)) →
      let sf := runFrom dotO2Cmap (7 * (k + 1)) idx nd s
      sf.halted = false ∧ sf.fault = false ∧ sf.rip = 0x400218#64 ∧ sf.mem = s0.mem ∧
      BitVec.extractLsb' 0 32 (sf.regs .rdx) = rustDotU8U16 s0.mem (s0.regs .rdi) (s0.regs .rsi) (s0.regs .rdx).toNat ∧
      SysVCalleeSavedPreserved s0 sf ∧
      (∀ r : YmmIdx, BitVec.extractLsb' 128 128 (sf.ymms r) = BitVec.extractLsb' 128 128 (s0.ymms r)) := by
  intro k
  induction k with
  | zero =>
    intro idx s hle hrun hnf hrip hmem hrdi hrsi hr9 hrax hrdx hcs hymm
    have hlt0 : (s0.regs .rdx).toNat - 1 < (s0.regs .rdx).toNat := by clear hcs hymm hpre; omega
    have hdone : (s0.regs .rdx).toNat - 1 + 1 = (s0.regs .rdx).toNat := by clear hcs hymm hpre; omega
    have hnc : ¬ ((s0.regs .rdx).toNat - 1 + 1 < (s0.regs .rdx).toNat) := by clear hcs hymm hpre; omega
    have h1 := dotO2_scalar_tail_step s0 s ((s0.regs .rdx).toNat - 1) idx nd hpre
      hrun hnf hrip hmem hrdi hrsi hr9 hrax hrdx hcs hymm hlt0
    simp only [hnc, ite_false] at h1
    rw [hdone] at h1
    rcases h1 with ⟨hr, hf, hri, hm, _, _, _, _, hdx, hcs', hym'⟩
    exact ⟨hr, hf, hri, hm, hdx, hcs', hym'⟩
  | succ m ih =>
    intro idx s hle hrun hnf hrip hmem hrdi hrsi hr9 hrax hrdx hcs hymm
    have hltm : (s0.regs .rdx).toNat - (m + 1 + 1) < (s0.regs .rdx).toNat := by clear ih hcs hymm hpre; omega
    have hc : (s0.regs .rdx).toNat - (m + 1 + 1) + 1 < (s0.regs .rdx).toNat := by clear ih hcs hymm hpre; omega
    have hnext : (s0.regs .rdx).toNat - (m + 1 + 1) + 1 = (s0.regs .rdx).toNat - (m + 1) := by clear ih hcs hymm hpre; omega
    have hlem : m + 1 ≤ (s0.regs .rdx).toNat := by clear ih hcs hymm hpre; omega
    have h7m : 7 * (m + 1 + 1) = 7 + 7 * (m + 1) := by clear ih hcs hymm hpre; omega
    dsimp only; rw [h7m, runFrom_add]
    have h1 := dotO2_scalar_tail_step s0 s ((s0.regs .rdx).toNat - (m + 1 + 1)) idx nd hpre
      hrun hnf hrip hmem hrdi hrsi hr9 hrax hrdx hcs hymm hltm
    simp only [hc, ite_true] at h1
    rw [hnext] at h1
    rcases h1 with ⟨hr, hf, hri, hm, hdi, hsi, h9, hax, hdx, hcs', hym'⟩
    exact ih (idx + 7) (runFrom dotO2Cmap 7 idx nd s) hlem hr hf hri hm hdi hsi h9 hax hdx hcs' hym'

private theorem dotO2_ret_0x218 (s0 s : X64State) (idx : Nat) (nd : Nat → UndefChoice)
    (hrun : s.halted = false) (hnf : s.fault = false) (hrip : s.rip = 0x400218#64)
    (hmem : s.mem = s0.mem)
    (hrdx : BitVec.extractLsb' 0 32 (s.regs .rdx) = rustDotU8U16 s0.mem (s0.regs .rdi) (s0.regs .rsi) (s0.regs .rdx).toNat)
    (hcs : SysVCalleeSavedPreserved s0 s)
    (hymm : ∀ r : YmmIdx, BitVec.extractLsb' 128 128 (s.ymms r) = BitVec.extractLsb' 128 128 (s0.ymms r)) :
    let sf := runFrom dotO2Cmap 2 idx nd s
    sf.halted = true ∧ sf.fault = false ∧
    SysVCalleeSavedPreserved s0 sf ∧ UpperYmmCleanOrPreserved s0 sf ∧
    DotU8U16Post 0 s0 sf := by
  dsimp only
  rw [runFrom_succ, step_at_concrete dotO2_ret_mov _ _ hrun hnf hrip, exec_movStore_s32_reg]
  rw [runFrom_succ, step_at_concrete dotO2_ret_ret _ { s with rip := 0x400218#64 + BitVec.ofNat 64 2, regs := _ } hrun hnf rfl,
      exec_ret, runFrom_zero]
  refine ⟨rfl, hnf, ?_, ?_, ?_, fun _ _ => hmem ▸ rfl⟩
  · unfold SysVCalleeSavedPreserved at hcs ⊢; dsimp only; exact cs_step_caller (r := .rax) rfl hcs
  · intro h0 r; dsimp only; rw [hymm r]; exact h0 r
  · dsimp only; rw [regUpd_eq, zext32_extract32_eq, hrdx]

/-! ## Section 3: `16`-Elem Legacy SSE2 Loop & Horizontal Reduction -/

private theorem dotO2_stepA (s : X64State) (aPtr bPtr : BitVec 64) (done idx : Nat) (nd : Nat → UndefChoice)
    (hshl : BitVec.ofNat 64 done <<< 1 = BitVec.ofNat 64 (2 * done))
    (hrun : s.halted = false) (hnf : s.fault = false) (hrip : s.rip = 0x400170#64)
    (hrdi : s.regs .rdi = aPtr) (hrsi : s.regs .rsi = bPtr)
    (hrdx : s.regs .rdx = BitVec.ofNat 64 done)
    (hy6 : BitVec.extractLsb' 0 128 (s.ymms y6) = 0#128) :
    let pa := aPtr + BitVec.ofNat 64 done
    let pb := bPtr + BitVec.ofNat 64 (2 * done)
    let a128 := readMem128 s.mem pa
    let bLo  := readMem128 s.mem pb
    let bHi  := readMem128 s.mem (pb + 16#64)
    let sA := runFrom dotO2Cmap 7 idx nd s
    sA.halted = false ∧ sA.fault = false ∧ sA.rip = 0x400190#64 ∧ sA.mem = s.mem ∧
    sA.regs = regUpd s.regs .rdx (BitVec.ofNat 64 (done + 16)) ∧
    BitVec.extractLsb' 0 128 (sA.ymms y0) = bHi ∧
    BitVec.extractLsb' 0 128 (sA.ymms y1) = unpack128 .hbw a128 0#128 ∧
    BitVec.extractLsb' 0 128 (sA.ymms y2) = a128 ∧
    BitVec.extractLsb' 0 128 (sA.ymms y3) = BitVec.extractLsb' 0 128 (s.ymms y3) ∧
    BitVec.extractLsb' 0 128 (sA.ymms y4) = bLo ∧
    BitVec.extractLsb' 0 128 (sA.ymms y5) = bHi ∧
    BitVec.extractLsb' 0 128 (sA.ymms y6) = 0#128 ∧
    (∀ r : YmmIdx, BitVec.extractLsb' 128 128 (sA.ymms r) = BitVec.extractLsb' 128 128 (s.ymms r)) := by
  dsimp only
  have hadd16 : BitVec.ofNat 64 done + 0x10#64 = BitVec.ofNat 64 (done + 16) := by
    change BitVec.ofNat 64 done + BitVec.ofNat 64 16 = BitVec.ofNat 64 (done + 16); exact bv64_ofNat_add done 16
  let a128 := readMem128 s.mem (aPtr + BitVec.ofNat 64 done)
  let bLo  := readMem128 s.mem (bPtr + BitVec.ofNat 64 (2 * done))
  let bHi  := readMem128 s.mem ((bPtr + BitVec.ofNat 64 (2 * done)) + 16#64)
  let y1s := writeXmm128 false s.ymms y5 bHi
  let y2s := writeXmm128 false y1s y1 a128
  let y3s := writeXmm128 false y2s y4 bLo
  let y4s := writeXmm128 false y3s y2 a128
  let y5s := writeXmm128 false y4s y0 bHi
  let y6s := writeXmm128 false y5s y1 (unpack128 .hbw a128 0#128)
  let rA := regUpd s.regs .rdx (BitVec.ofNat 64 (done + 16))
  rcases runFrom_of_decodeSeqAt dotO2_bodyA_dec idx nd s hrun hnf hrip with ⟨hseq, _, _⟩
  have he : runFrom dotO2Cmap 7 idx nd s =
      { s with
        rip := 0x400190#64,
        regs := rA,
        ymms := y6s,
        flags := (evalAluN (by decide) .add (BitVec.ofNat 64 done) 0x10#64 s.flags (nd (idx + 3)).flags).2 } := by
    rw [hseq]; dsimp only [dotO2_bodyASeq]
    rw [execInstrSeq_succ_cons, exec_simdMovLoad_legacy128_mem, evalByteAddr_base_idx1_disp, hrsi, hrdx, hshl]
    change execInstrSeq 6 _ _ _ { s with rip := 0x400176#64, ymms := y1s } = _
    rw [execInstrSeq_succ_cons, exec_simdMovLoad_legacy128_mem, evalByteAddr_base_idx0, hrdi, hrdx]
    change execInstrSeq 5 _ _ _ { s with rip := 0x40017b#64, ymms := y2s } = _
    rw [execInstrSeq_succ_cons, exec_simdMovLoad_legacy128_mem, evalByteAddr_base_idx1, hrsi, hrdx, hshl]
    change execInstrSeq 4 _ _ _ { s with rip := 0x400180#64, ymms := y3s } = _
    rw [execInstrSeq_succ_cons, exec_aluImm_s64_add, hrdx, hadd16]
    change execInstrSeq 3 _ _ _ { s with rip := 0x400184#64, regs := rA, ymms := y3s, flags := _ } = _
    rw [execInstrSeq_succ_cons, exec_simdMovLoad_legacy128_reg]
    dsimp only; rw [show BitVec.extractLsb' 0 128 (y3s y1) = a128 from by dsimp only [y3s, y2s]; rw [writeXmm128_ne false _ (by decide : y1 ≠ y4), writeXmm128_false_lo]]
    change execInstrSeq 2 _ _ _ { s with rip := 0x400188#64, regs := rA, ymms := y4s, flags := _ } = _
    rw [execInstrSeq_succ_cons, exec_simdMovLoad_legacy128_reg]
    dsimp only; rw [show BitVec.extractLsb' 0 128 (y4s y5) = bHi from by dsimp only [y4s, y3s, y2s, y1s]; (repeat rw [writeXmm128_ne false _ (by decide)]); exact writeXmm128_false_lo _ _ _]
    change execInstrSeq 1 _ _ _ { s with rip := 0x40018c#64, regs := rA, ymms := y5s, flags := _ } = _
    rw [execInstrSeq_succ_cons, exec_simdUnpack_legacy128_reg, execInstrSeq_zero]
    dsimp only
    rw [show BitVec.extractLsb' 0 128 (y5s y1) = a128 from by dsimp only [y5s, y4s, y3s, y2s]; (repeat rw [writeXmm128_ne false _ (by decide)]); exact writeXmm128_false_lo _ _ _,
        show BitVec.extractLsb' 0 128 (y5s y6) = 0#128 from by dsimp only [y5s, y4s, y3s, y2s, y1s]; (repeat rw [writeXmm128_ne false _ (by decide)]); exact hy6]
  rw [he]; refine ⟨hrun, hnf, rfl, rfl, rfl, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · dsimp only [y6s, y5s]; rw [writeXmm128_ne false _ (by decide : y0 ≠ y1), writeXmm128_false_lo]
  · exact writeXmm128_false_lo _ _ _
  · dsimp only [y6s, y5s, y4s]; (repeat rw [writeXmm128_ne false _ (by decide)]); exact writeXmm128_false_lo _ _ _
  · dsimp only [y6s, y5s, y4s, y3s, y2s, y1s]; repeat rw [writeXmm128_ne false _ (by decide)]
  · dsimp only [y6s, y5s, y4s, y3s]; (repeat rw [writeXmm128_ne false _ (by decide)]); exact writeXmm128_false_lo _ _ _
  · dsimp only [y6s, y5s, y4s, y3s, y2s, y1s]
    rw [writeXmm128_ne false _ (by decide : y5 ≠ y1), writeXmm128_ne false _ (by decide : y5 ≠ y0),
        writeXmm128_ne false _ (by decide : y5 ≠ y2), writeXmm128_ne false _ (by decide : y5 ≠ y4),
        writeXmm128_ne false _ (by decide : y5 ≠ y1), writeXmm128_false_lo]
  · dsimp only [y6s, y5s, y4s, y3s, y2s, y1s]; (repeat rw [writeXmm128_ne false _ (by decide)]); exact hy6
  · intro r; dsimp only [y6s, y5s, y4s, y3s, y2s, y1s]; repeat rw [writeXmm128_false_preserves_hi]

private theorem dotO2_stepB (sA : X64State) (a128 bLo bHi aHi16 : BitVec 128) (idx : Nat) (nd : Nat → UndefChoice)
    (hrun : sA.halted = false) (hnf : sA.fault = false) (hrip : sA.rip = 0x400190#64)
    (hy0 : BitVec.extractLsb' 0 128 (sA.ymms y0) = bHi)
    (hy1 : BitVec.extractLsb' 0 128 (sA.ymms y1) = aHi16)
    (hy2 : BitVec.extractLsb' 0 128 (sA.ymms y2) = a128)
    (hy4 : BitVec.extractLsb' 0 128 (sA.ymms y4) = bLo)
    (hy5 : BitVec.extractLsb' 0 128 (sA.ymms y5) = bHi)
    (hy6 : BitVec.extractLsb' 0 128 (sA.ymms y6) = 0#128) :
    let loHi := pmullw128 bHi aHi16
    let hiHi := pmulhuw128 aHi16 bHi
    let aLo16 := unpack128 .lbw a128 0#128
    let sB := runFrom dotO2Cmap 8 idx nd sA
    sB.halted = false ∧ sB.fault = false ∧ sB.rip = 0x4001b0#64 ∧
    sB.mem = sA.mem ∧ sB.regs = sA.regs ∧
    BitVec.extractLsb' 0 128 (sB.ymms y0) = unpack128 .hwd loHi hiHi ∧
    BitVec.extractLsb' 0 128 (sB.ymms y1) = pmullw128 bLo aLo16 ∧
    BitVec.extractLsb' 0 128 (sB.ymms y2) = aLo16 ∧
    BitVec.extractLsb' 0 128 (sB.ymms y3) = BitVec.extractLsb' 0 128 (sA.ymms y3) ∧
    BitVec.extractLsb' 0 128 (sB.ymms y4) = bLo ∧
    BitVec.extractLsb' 0 128 (sB.ymms y5) = unpack128 .lwd loHi hiHi ∧
    BitVec.extractLsb' 0 128 (sB.ymms y6) = 0#128 ∧
    (∀ r : YmmIdx, BitVec.extractLsb' 128 128 (sB.ymms r) = BitVec.extractLsb' 128 128 (sA.ymms r)) := by
  dsimp only
  let loHi := pmullw128 bHi aHi16
  let hiHi := pmulhuw128 aHi16 bHi
  let aLo16 := unpack128 .lbw a128 0#128
  let y1s := writeXmm128 false sA.ymms y0 loHi
  let y2s := writeXmm128 false y1s y1 hiHi
  let y3s := writeXmm128 false y2s y2 aLo16
  let y4s := writeXmm128 false y3s y5 loHi
  let y5s := writeXmm128 false y4s y0 (unpack128 .hwd loHi hiHi)
  let y6s := writeXmm128 false y5s y5 (unpack128 .lwd loHi hiHi)
  let y7s := writeXmm128 false y6s y1 bLo
  let y8s := writeXmm128 false y7s y1 (pmullw128 bLo aLo16)
  rcases runFrom_of_decodeSeqAt dotO2_bodyB_dec idx nd sA hrun hnf hrip with ⟨hseq, _, _⟩
  have he : runFrom dotO2Cmap 8 idx nd sA = { sA with rip := 0x4001b0#64, ymms := y8s } := by
    rw [hseq]; dsimp only [dotO2_bodyBSeq]
    rw [execInstrSeq_succ_cons, exec_simdPmullw_legacy128_reg, hy0, hy1]
    change execInstrSeq 7 _ _ _ { sA with rip := 0x400194#64, ymms := y1s } = _
    rw [execInstrSeq_succ_cons, exec_simdPmulhuw_legacy128_reg]
    dsimp only; rw [show BitVec.extractLsb' 0 128 (y1s y1) = aHi16 from by dsimp only [y1s]; rw [writeXmm128_ne false _ (by decide : y1 ≠ y0), hy1],
                    show BitVec.extractLsb' 0 128 (y1s y5) = bHi from by dsimp only [y1s]; rw [writeXmm128_ne false _ (by decide : y5 ≠ y0), hy5]]
    change execInstrSeq 6 _ _ _ { sA with rip := 0x400198#64, ymms := y2s } = _
    rw [execInstrSeq_succ_cons, exec_simdUnpack_legacy128_reg]
    dsimp only; rw [show BitVec.extractLsb' 0 128 (y2s y2) = a128 from by dsimp only [y2s, y1s]; (repeat rw [writeXmm128_ne false _ (by decide)]); exact hy2,
                    show BitVec.extractLsb' 0 128 (y2s y6) = 0#128 from by dsimp only [y2s, y1s]; (repeat rw [writeXmm128_ne false _ (by decide)]); exact hy6]
    change execInstrSeq 5 _ _ _ { sA with rip := 0x40019c#64, ymms := y3s } = _
    rw [execInstrSeq_succ_cons, exec_simdMovLoad_legacy128_reg]
    dsimp only; rw [show BitVec.extractLsb' 0 128 (y3s y0) = loHi from by dsimp only [y3s, y2s, y1s]; (repeat rw [writeXmm128_ne false _ (by decide)]); exact writeXmm128_false_lo _ _ _]
    change execInstrSeq 4 _ _ _ { sA with rip := 0x4001a0#64, ymms := y4s } = _
    rw [execInstrSeq_succ_cons, exec_simdUnpack_legacy128_reg]
    dsimp only; rw [show BitVec.extractLsb' 0 128 (y4s y0) = loHi from by dsimp only [y4s, y3s, y2s, y1s]; (repeat rw [writeXmm128_ne false _ (by decide)]); exact writeXmm128_false_lo _ _ _,
                    show BitVec.extractLsb' 0 128 (y4s y1) = hiHi from by dsimp only [y4s, y3s, y2s]; (repeat rw [writeXmm128_ne false _ (by decide)]); exact writeXmm128_false_lo _ _ _]
    change execInstrSeq 3 _ _ _ { sA with rip := 0x4001a4#64, ymms := y5s } = _
    rw [execInstrSeq_succ_cons, exec_simdUnpack_legacy128_reg]
    dsimp only; rw [show BitVec.extractLsb' 0 128 (y5s y5) = loHi from by dsimp only [y5s, y4s]; rw [writeXmm128_ne false _ (by decide : y5 ≠ y0), writeXmm128_false_lo],
                    show BitVec.extractLsb' 0 128 (y5s y1) = hiHi from by dsimp only [y5s, y4s, y3s, y2s]; (repeat rw [writeXmm128_ne false _ (by decide)]); exact writeXmm128_false_lo _ _ _]
    change execInstrSeq 2 _ _ _ { sA with rip := 0x4001a8#64, ymms := y6s } = _
    rw [execInstrSeq_succ_cons, exec_simdMovLoad_legacy128_reg]
    dsimp only; rw [show BitVec.extractLsb' 0 128 (y6s y4) = bLo from by dsimp only [y6s, y5s, y4s, y3s, y2s, y1s]; (repeat rw [writeXmm128_ne false _ (by decide)]); exact hy4]
    change execInstrSeq 1 _ _ _ { sA with rip := 0x4001ac#64, ymms := y7s } = _
    rw [execInstrSeq_succ_cons, exec_simdPmullw_legacy128_reg, execInstrSeq_zero]
    dsimp only; rw [show BitVec.extractLsb' 0 128 (y7s y1) = bLo from writeXmm128_false_lo _ _ _,
                    show BitVec.extractLsb' 0 128 (y7s y2) = aLo16 from by dsimp only [y7s, y6s, y5s, y4s, y3s]; (repeat rw [writeXmm128_ne false _ (by decide)]); exact writeXmm128_false_lo _ _ _]
  rw [he]; refine ⟨hrun, hnf, rfl, rfl, rfl, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · dsimp only [y8s, y7s, y6s, y5s]; (repeat rw [writeXmm128_ne false _ (by decide)]); exact writeXmm128_false_lo _ _ _
  · exact writeXmm128_false_lo _ _ _
  · dsimp only [y8s, y7s, y6s, y5s, y4s, y3s]; (repeat rw [writeXmm128_ne false _ (by decide)]); exact writeXmm128_false_lo _ _ _
  · dsimp only [y8s, y7s, y6s, y5s, y4s, y3s, y2s, y1s]; repeat rw [writeXmm128_ne false _ (by decide)]
  · dsimp only [y8s, y7s, y6s, y5s, y4s, y3s, y2s, y1s]; (repeat rw [writeXmm128_ne false _ (by decide)]); exact hy4
  · dsimp only [y8s, y7s, y6s]; (repeat rw [writeXmm128_ne false _ (by decide)]); exact writeXmm128_false_lo _ _ _
  · dsimp only [y8s, y7s, y6s, y5s, y4s, y3s, y2s, y1s]; (repeat rw [writeXmm128_ne false _ (by decide)]); exact hy6
  · intro r; dsimp only [y8s, y7s, y6s, y5s, y4s, y3s, y2s, y1s]; repeat rw [writeXmm128_false_preserves_hi]

private theorem dotO2_stepC (sB : X64State) (vHiH loLo aLo16 accV bLo vHiL : BitVec 128) (rdxV raxV : BitVec 64)
    (idx : Nat) (nd : Nat → UndefChoice)
    (hrun : sB.halted = false) (hnf : sB.fault = false) (hrip : sB.rip = 0x4001b0#64)
    (hrdx : sB.regs .rdx = rdxV) (hrax : sB.regs .rax = raxV)
    (hy0 : BitVec.extractLsb' 0 128 (sB.ymms y0) = vHiH)
    (hy1 : BitVec.extractLsb' 0 128 (sB.ymms y1) = loLo)
    (hy2 : BitVec.extractLsb' 0 128 (sB.ymms y2) = aLo16)
    (hy3 : BitVec.extractLsb' 0 128 (sB.ymms y3) = accV)
    (hy4 : BitVec.extractLsb' 0 128 (sB.ymms y4) = bLo)
    (hy5 : BitVec.extractLsb' 0 128 (sB.ymms y5) = vHiL)
    (hy6 : BitVec.extractLsb' 0 128 (sB.ymms y6) = 0#128) :
    let hiLo := pmulhuw128 aLo16 bLo
    let vHi := packDwords128 fun i => getDword128 vHiH i + getDword128 vHiL i
    let vLo := packDwords128 fun i => getDword128 (unpack128 .hwd loLo hiLo) i + getDword128 (unpack128 .lwd loLo hiLo) i
    let v16 := packDwords128 fun i => getDword128 vHi i + getDword128 vLo i
    let sC := runFrom dotO2Cmap 9 idx nd sB
    sC.halted = false ∧ sC.fault = false ∧ sC.rip = 0x4001d3#64 ∧
    sC.mem = sB.mem ∧ sC.regs = sB.regs ∧
    sC.flags = (evalAluN (by decide) .cmp rdxV raxV sB.flags (nd (idx + 8)).flags).2 ∧
    BitVec.extractLsb' 0 128 (sC.ymms y3) = (packDwords128 fun i => getDword128 accV i + getDword128 v16 i) ∧
    BitVec.extractLsb' 0 128 (sC.ymms y6) = 0#128 ∧
    (∀ r : YmmIdx, BitVec.extractLsb' 128 128 (sC.ymms r) = BitVec.extractLsb' 128 128 (sB.ymms r)) := by
  dsimp only
  let hiLo := pmulhuw128 aLo16 bLo
  let vHi := packDwords128 fun i => getDword128 vHiH i + getDword128 vHiL i
  let vLoH := unpack128 .hwd loLo hiLo
  let vLoL := unpack128 .lwd loLo hiLo
  let vLo := packDwords128 fun i => getDword128 vLoH i + getDword128 vLoL i
  let v16 := packDwords128 fun i => getDword128 vHi i + getDword128 vLo i
  let acc' := packDwords128 fun i => getDword128 accV i + getDword128 v16 i
  let y1s := writeXmm128 false sB.ymms y2 hiLo
  let y2s := writeXmm128 false y1s y0 vHi
  let y3s := writeXmm128 false y2s y4 loLo
  let y4s := writeXmm128 false y3s y1 vLoH
  let y5s := writeXmm128 false y4s y4 vLoL
  let y6s := writeXmm128 false y5s y1 vLo
  let y7s := writeXmm128 false y6s y0 v16
  let y8s := writeXmm128 false y7s y3 acc'
  rcases runFrom_of_decodeSeqAt dotO2_bodyC_dec idx nd sB hrun hnf hrip with ⟨hseq, _, _⟩
  have he : runFrom dotO2Cmap 9 idx nd sB =
      { sB with
        rip := 0x4001d3#64,
        ymms := y8s,
        flags := (evalAluN (by decide) .cmp rdxV raxV sB.flags (nd (idx + 8)).flags).2 } := by
    rw [hseq]; dsimp only [dotO2_bodyCSeq]
    rw [execInstrSeq_succ_cons, exec_simdPmulhuw_legacy128_reg, hy2, hy4]
    change execInstrSeq 8 _ _ _ { sB with rip := 0x4001b4#64, ymms := y1s } = _
    rw [execInstrSeq_succ_cons, exec_simdAdd_legacy128_e32_reg]
    dsimp only; rw [show BitVec.extractLsb' 0 128 (y1s y0) = vHiH from by dsimp only [y1s]; rw [writeXmm128_ne false _ (by decide : y0 ≠ y2), hy0],
                    show BitVec.extractLsb' 0 128 (y1s y5) = vHiL from by dsimp only [y1s]; rw [writeXmm128_ne false _ (by decide : y5 ≠ y2), hy5]]
    change execInstrSeq 7 _ _ _ { sB with rip := 0x4001b8#64, ymms := y2s } = _
    rw [execInstrSeq_succ_cons, exec_simdMovLoad_legacy128_reg]
    dsimp only; rw [show BitVec.extractLsb' 0 128 (y2s y1) = loLo from by dsimp only [y2s, y1s]; (repeat rw [writeXmm128_ne false _ (by decide)]); exact hy1]
    change execInstrSeq 6 _ _ _ { sB with rip := 0x4001bc#64, ymms := y3s } = _
    rw [execInstrSeq_succ_cons, exec_simdUnpack_legacy128_reg]
    dsimp only; rw [show BitVec.extractLsb' 0 128 (y3s y1) = loLo from by dsimp only [y3s, y2s, y1s]; (repeat rw [writeXmm128_ne false _ (by decide)]); exact hy1,
                    show BitVec.extractLsb' 0 128 (y3s y2) = hiLo from by dsimp only [y3s, y2s, y1s]; (repeat rw [writeXmm128_ne false _ (by decide)]); exact writeXmm128_false_lo _ _ _]
    change execInstrSeq 5 _ _ _ { sB with rip := 0x4001c0#64, ymms := y4s } = _
    rw [execInstrSeq_succ_cons, exec_simdUnpack_legacy128_reg]
    dsimp only; rw [show BitVec.extractLsb' 0 128 (y4s y4) = loLo from by dsimp only [y4s, y3s]; rw [writeXmm128_ne false _ (by decide : y4 ≠ y1), writeXmm128_false_lo],
                    show BitVec.extractLsb' 0 128 (y4s y2) = hiLo from by dsimp only [y4s, y3s, y2s, y1s]; (repeat rw [writeXmm128_ne false _ (by decide)]); exact writeXmm128_false_lo _ _ _]
    change execInstrSeq 4 _ _ _ { sB with rip := 0x4001c4#64, ymms := y5s } = _
    rw [execInstrSeq_succ_cons, exec_simdAdd_legacy128_e32_reg]
    dsimp only; rw [show BitVec.extractLsb' 0 128 (y5s y1) = vLoH from by dsimp only [y5s, y4s]; rw [writeXmm128_ne false _ (by decide : y1 ≠ y4), writeXmm128_false_lo],
                    show BitVec.extractLsb' 0 128 (y5s y4) = vLoL from writeXmm128_false_lo _ _ _]
    change execInstrSeq 3 _ _ _ { sB with rip := 0x4001c8#64, ymms := y6s } = _
    rw [execInstrSeq_succ_cons, exec_simdAdd_legacy128_e32_reg]
    dsimp only; rw [show BitVec.extractLsb' 0 128 (y6s y0) = vHi from by dsimp only [y6s, y5s, y4s, y3s, y2s]; (repeat rw [writeXmm128_ne false _ (by decide)]); exact writeXmm128_false_lo _ _ _,
                    show BitVec.extractLsb' 0 128 (y6s y1) = vLo from writeXmm128_false_lo _ _ _]
    change execInstrSeq 2 _ _ _ { sB with rip := 0x4001cc#64, ymms := y7s } = _
    rw [execInstrSeq_succ_cons, exec_simdAdd_legacy128_e32_reg]
    dsimp only; rw [show BitVec.extractLsb' 0 128 (y7s y3) = accV from by dsimp only [y7s, y6s, y5s, y4s, y3s, y2s, y1s]; (repeat rw [writeXmm128_ne false _ (by decide)]); exact hy3,
                    show BitVec.extractLsb' 0 128 (y7s y0) = v16 from writeXmm128_false_lo _ _ _]
    change execInstrSeq 1 _ _ _ { sB with rip := 0x4001d0#64, ymms := y8s } = _
    rw [execInstrSeq_succ_cons, exec_aluRmReg_s64_cmp, execInstrSeq_zero]
    dsimp only; rw [hrdx, hrax]
  rw [he]; refine ⟨hrun, hnf, rfl, rfl, rfl, rfl, ?_, ?_, ?_⟩
  · exact writeXmm128_false_lo _ _ _
  · dsimp only [y8s, y7s, y6s, y5s, y4s, y3s, y2s, y1s]; (repeat rw [writeXmm128_ne false _ (by decide)]); exact hy6
  · intro r; dsimp only [y8s, y7s, y6s, y5s, y4s, y3s, y2s, y1s]; repeat rw [writeXmm128_false_preserves_hi]

private theorem dotO2_simd_step (s0 s : X64State) (hpre : DotU8U16Pre 0 s0) (nd : Nat → UndefChoice)
    (q done idx : Nat)
    (hstep : done + 16 ≤ q * 16) (hqle : q * 16 ≤ (s0.regs .rdx).toNat)
    (hrun : s.halted = false) (hnf : s.fault = false) (hrip : s.rip = 0x400170#64)
    (hmem : s.mem = s0.mem)
    (hrdi : s.regs .rdi = s0.regs .rdi) (hrsi : s.regs .rsi = s0.regs .rsi)
    (hr9 : s.regs .r9 = s0.regs .rdx)
    (hrax : s.regs .rax = BitVec.ofNat 64 (q * 16))
    (hrdx : s.regs .rdx = BitVec.ofNat 64 done)
    (hy3 : sumDwords128 (BitVec.extractLsb' 0 128 (s.ymms y3)) =
      rustDotU8U16From s0.mem (s0.regs .rdi) (s0.regs .rsi) done 0#32)
    (hy6 : BitVec.extractLsb' 0 128 (s.ymms y6) = 0#128)
    (hcs : SysVCalleeSavedPreserved s0 s)
    (hymm : ∀ r : YmmIdx, BitVec.extractLsb' 128 128 (s.ymms r) = BitVec.extractLsb' 128 128 (s0.ymms r)) :
    let s' := runFrom dotO2Cmap 25 idx nd s
    s'.halted = false ∧ s'.fault = false ∧
    s'.rip = (if done + 16 = q * 16 then 0x4001d5#64 else 0x400170#64) ∧
    s'.mem = s0.mem ∧
    s'.regs .rdi = s0.regs .rdi ∧ s'.regs .rsi = s0.regs .rsi ∧ s'.regs .r9 = s0.regs .rdx ∧
    s'.regs .rax = BitVec.ofNat 64 (q * 16) ∧
    s'.regs .rdx = BitVec.ofNat 64 (done + 16) ∧
    sumDwords128 (BitVec.extractLsb' 0 128 (s'.ymms y3)) =
      rustDotU8U16From s0.mem (s0.regs .rdi) (s0.regs .rsi) (done + 16) 0#32 ∧
    BitVec.extractLsb' 0 128 (s'.ymms y6) = 0#128 ∧
    SysVCalleeSavedPreserved s0 s' ∧
    (∀ r : YmmIdx, BitVec.extractLsb' 128 128 (s'.ymms r) = BitVec.extractLsb' 128 128 (s0.ymms r)) := by
  have h2len : 2 * (s0.regs .rdx).toNat < 2 ^ 64 := hpre.1
  have hlenLt := (s0.regs .rdx).isLt
  have hshl1 : BitVec.ofNat 64 done <<< 1 = BitVec.ofNat 64 (2 * done) := by
    have htn : (BitVec.ofNat 64 done).toNat = done := by
      rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by clear hpre hy3 hy6 hcs hymm; omega)]
    rw [bv64_shl1_toNat (by clear hpre hy3 hy6 hcs hymm; rw [htn]; omega), htn]
  have hA := dotO2_stepA s (s0.regs .rdi) (s0.regs .rsi) done idx nd hshl1 hrun hnf hrip hrdi hrsi hrdx hy6
  generalize hsA : runFrom dotO2Cmap 7 idx nd s = sA at hA
  rcases hA with ⟨hAr, hAf, hArip, hAm, hAregs, hAy0, hAy1, hAy2, hAy3, hAy4, hAy5, hAy6, hAhi⟩
  have hB := dotO2_stepB sA _ _ _ _ (idx + 7) nd hAr hAf hArip hAy0 hAy1 hAy2 hAy4 hAy5 hAy6
  generalize hsB : runFrom dotO2Cmap 8 (idx + 7) nd sA = sB at hB
  rcases hB with ⟨hBr, hBf, hBrip, hBm, hBregs, hBy0, hBy1, hBy2, hBy3, hBy4, hBy5, hBy6, hBhi⟩
  have hC := dotO2_stepC sB _ _ _ _ _ _ (BitVec.ofNat 64 (done + 16)) (BitVec.ofNat 64 (q * 16)) (idx + 15) nd
    hBr hBf hBrip (by rw [hBregs, hAregs]; exact regUpd_eq _ _ _)
    (by rw [hBregs, hAregs]; rw [regUpd_ne _ (by decide), hrax])
    hBy0 hBy1 hBy2 (by rw [hBy3, hAy3]) hBy4 hBy5 hBy6
  generalize hsC : runFrom dotO2Cmap 9 (idx + 15) nd sB = sC at hC
  rcases hC with ⟨hCr, hCf, hCrip, hCm, hCregs, hCfl, hCy3, hCy6, hChi⟩
  have hCsum : sumDwords128 (BitVec.extractLsb' 0 128 (sC.ymms y3)) =
      rustDotU8U16From s0.mem (s0.regs .rdi) (s0.regs .rsi) (done + 16) 0#32 := by
    rw [hCy3, sumDwords128_paddd, hy3, rustDotU8U16From_split, hmem]
    exact dot16_sse2_algebra s0.mem (s0.regs .rdi + BitVec.ofNat 64 done) (s0.regs .rsi + BitVec.ofNat 64 (2 * done)) _
  have hCcs : SysVCalleeSavedPreserved s0 sC := by
    unfold SysVCalleeSavedPreserved at hcs ⊢; rw [hCregs, hBregs, hAregs]; exact cs_step_caller (r := .rdx) rfl hcs
  have hChimm : ∀ r : YmmIdx, BitVec.extractLsb' 128 128 (sC.ymms r) = BitVec.extractLsb' 128 128 (s0.ymms r) :=
    fun r => by rw [hChi r, hBhi r, hAhi r, hymm r]
  have hCm0 : sC.mem = s0.mem := by rw [hCm, hBm, hAm, hmem]
  dsimp only
  rw [show (25 : Nat) = 7 + (8 + (9 + 1)) by rfl, runFrom_add, hsA, runFrom_add, hsB,
      show idx + 7 + 8 = idx + 15 by omega, runFrom_add, hsC,
      runFrom_succ, step_at_concrete dotO2_loop_jne _ sC hCr hCf hCrip, runFrom_zero]
  by_cases hdone : done + 16 = q * 16
  · have hzf : evalCond .ne sC.flags = false := by
      rw [hCfl, hdone]; exact evalCond_ne_of_zf_true (by rw [cmp_flags_zf, cmp_sub_self_zero])
    rw [exec_jcc_fall hzf]
    simp only [hdone, ite_true]
    refine ⟨hCr, hCf, rfl, hCm0,
      by rw [hCregs, hBregs, hAregs, regUpd_ne _ (by decide), hrdi],
      by rw [hCregs, hBregs, hAregs, regUpd_ne _ (by decide), hrsi],
      by rw [hCregs, hBregs, hAregs, regUpd_ne _ (by decide), hr9],
      by rw [hCregs, hBregs, hAregs, regUpd_ne _ (by decide), hrax],
      by rw [hCregs, hBregs, hAregs, regUpd_eq, hdone],
      hdone ▸ hCsum, hCy6,
      by unfold SysVCalleeSavedPreserved at hcs ⊢; dsimp only; rw [hCregs, hBregs, hAregs]; exact cs_step_caller (r := .rdx) rfl hcs,
      hChimm⟩
  · have hne : BitVec.ofNat 64 (done + 16) ≠ BitVec.ofNat 64 (q * 16) := by
      intro heq; have ht := congrArg BitVec.toNat heq
      have h1 : done + 16 < 2 ^ 64 := Nat.lt_of_le_of_lt (Nat.le_trans hstep hqle) hlenLt
      have h2 : q * 16 < 2 ^ 64 := Nat.lt_of_le_of_lt hqle hlenLt
      rw [BitVec.toNat_ofNat, BitVec.toNat_ofNat, Nat.mod_eq_of_lt h1, Nat.mod_eq_of_lt h2] at ht
      exact hdone ht
    have hzf : evalCond .ne sC.flags = true := by
      rw [hCfl]; exact evalCond_ne_of_zf_false (by rw [cmp_flags_zf, cmp_sub_zero_false_of_ne hne])
    rw [exec_jcc_taken hzf]
    simp only [hdone, ite_false]
    refine ⟨hCr, hCf, rfl, hCm0,
      by rw [hCregs, hBregs, hAregs, regUpd_ne _ (by decide), hrdi],
      by rw [hCregs, hBregs, hAregs, regUpd_ne _ (by decide), hrsi],
      by rw [hCregs, hBregs, hAregs, regUpd_ne _ (by decide), hr9],
      by rw [hCregs, hBregs, hAregs, regUpd_ne _ (by decide), hrax],
      by rw [hCregs, hBregs, hAregs, regUpd_eq],
      hCsum, hCy6,
      by unfold SysVCalleeSavedPreserved at hcs ⊢; dsimp only; rw [hCregs, hBregs, hAregs]; exact cs_step_caller (r := .rdx) rfl hcs,
      hChimm⟩

private theorem nat_mul16_step0 (q : Nat) (h : (0 + 1) * 16 ≤ q * 16) :
    (q - 1) * 16 + 16 ≤ q * 16 ∧ (q - 1) * 16 + 16 = q * 16 := by omega

private theorem nat_mul16_stepM (q m : Nat) (h : (m + 1 + 1) * 16 ≤ q * 16) :
    (q - (m + 1 + 1)) * 16 + 16 ≤ q * 16 ∧
    ¬ ((q - (m + 1 + 1)) * 16 + 16 = q * 16) ∧
    (q - (m + 1 + 1)) * 16 + 16 = (q - (m + 1)) * 16 ∧
    (m + 1) * 16 ≤ q * 16 ∧
    25 * (m + 1 + 1) = 25 + 25 * (m + 1) := by omega

private theorem dotO2_simd_loop (s0 : X64State) (hpre : DotU8U16Pre 0 s0) (nd : Nat → UndefChoice)
    (q : Nat) :
    ∀ (k : Nat) (idx : Nat) (s : X64State),
      (k + 1) * 16 ≤ q * 16 → q * 16 ≤ (s0.regs .rdx).toNat →
      s.halted = false → s.fault = false → s.rip = 0x400170#64 → s.mem = s0.mem →
      s.regs .rdi = s0.regs .rdi → s.regs .rsi = s0.regs .rsi → s.regs .r9 = s0.regs .rdx →
      s.regs .rax = BitVec.ofNat 64 (q * 16) →
      s.regs .rdx = BitVec.ofNat 64 ((q - (k + 1)) * 16) →
      sumDwords128 (BitVec.extractLsb' 0 128 (s.ymms y3)) =
        rustDotU8U16From s0.mem (s0.regs .rdi) (s0.regs .rsi) ((q - (k + 1)) * 16) 0#32 →
      BitVec.extractLsb' 0 128 (s.ymms y6) = 0#128 →
      SysVCalleeSavedPreserved s0 s →
      (∀ r : YmmIdx, BitVec.extractLsb' 128 128 (s.ymms r) = BitVec.extractLsb' 128 128 (s0.ymms r)) →
      let sf := runFrom dotO2Cmap (25 * (k + 1)) idx nd s
      sf.halted = false ∧ sf.fault = false ∧ sf.rip = 0x4001d5#64 ∧ sf.mem = s0.mem ∧
      sf.regs .rdi = s0.regs .rdi ∧ sf.regs .rsi = s0.regs .rsi ∧ sf.regs .r9 = s0.regs .rdx ∧
      sf.regs .rax = BitVec.ofNat 64 (q * 16) ∧
      sumDwords128 (BitVec.extractLsb' 0 128 (sf.ymms y3)) =
        rustDotU8U16From s0.mem (s0.regs .rdi) (s0.regs .rsi) (q * 16) 0#32 ∧
      SysVCalleeSavedPreserved s0 sf ∧
      (∀ r : YmmIdx, BitVec.extractLsb' 128 128 (sf.ymms r) = BitVec.extractLsb' 128 128 (s0.ymms r)) := by
  intro k
  induction k with
  | zero =>
    intro idx s hle hqle hrun hnf hrip hmem hrdi hrsi hr9 hrax hrdx hy3 hy6 hcs hymm
    rcases nat_mul16_step0 q hle with ⟨hstep0, heq⟩
    have h1 := dotO2_simd_step s0 s hpre nd q ((q - 1) * 16) idx hstep0 hqle
      hrun hnf hrip hmem hrdi hrsi hr9 hrax hrdx hy3 hy6 hcs hymm
    simp only [heq, ite_true] at h1
    rcases h1 with ⟨hr, hf, hri, hm, hdi, hsi, h9, hax, _, hy3', _, hcs', hym'⟩
    exact ⟨hr, hf, hri, hm, hdi, hsi, h9, hax, hy3', hcs', hym'⟩
  | succ m ih =>
    intro idx s hle hqle hrun hnf hrip hmem hrdi hrsi hr9 hrax hrdx hy3 hy6 hcs hymm
    rcases nat_mul16_stepM q m hle with ⟨hstepM, hne, hnext, hleM, h25m⟩
    dsimp only; rw [h25m, runFrom_add]
    have h1 := dotO2_simd_step s0 s hpre nd q ((q - (m + 1 + 1)) * 16) idx hstepM hqle
      hrun hnf hrip hmem hrdi hrsi hr9 hrax hrdx hy3 hy6 hcs hymm
    simp only [hne, ite_false] at h1
    rw [hnext] at h1
    rcases h1 with ⟨hr, hf, hri, hm, hdi, hsi, h9, hax, hdx, hy3', hy6', hcs', hym'⟩
    exact ih (idx + 25) (runFrom dotO2Cmap 25 idx nd s) hleM hqle hr hf hri hm hdi hsi h9 hax hdx hy3' hy6' hcs' hym'

/-! ## Section 4: Top-Level Equivalence Theorem for `c_dot_u8_u16 -O2` -/

/-- **Main Theorem (`c_dot_u8_u16 -O2`):**
    All execution paths of `gcc 15.2.0 -O2` `c_dot_u8_u16` (`cFfiKernelsO2Obj` at
    `0x140`: `len = 0`, `1 ≤ len ≤ 15` scalar tail, and `len ≥ 16` legacy non-VEX
    SSE2 `16`-element loop + horizontal `psrldq` reduction + scalar tail) compute
    `rustDotU8U16` with `ReadOnlyMemFrame`, `SysVCalleeSavedPreserved`, and exact
    upper-YMM preservation (`UpperYmmCleanOrPreserved`). -/
theorem prove_c_dot_u8_u16_o2 :
    CObjectMatchesRustContract cFfiKernelsO2Obj 0x140#64 (DotU8U16Pre 0) (DotU8U16Post 0) := by
  intro s0 nd hrun hnf hrip hpre
  change s0.rip = 0x400140#64 at hrip
  have hcs0 : SysVCalleeSavedPreserved s0 s0 := ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩
  have hymm0 : ∀ r : YmmIdx, BitVec.extractLsb' 128 128 (s0.ymms r) = BitVec.extractLsb' 128 128 (s0.ymms r) := fun _ => rfl
  rcases runFrom_of_decodeSeqAt dotO2_entry_dec 0 nd s0 hrun hnf hrip with ⟨hent, hrunE, hnfE⟩
  have heEnt : execInstrSeq 2 dotO2_entrySeq 0 nd s0 =
      { s0 with
        rip := 0x400146#64,
        regs := regUpd s0.regs .r9 (s0.regs .rdx),
        flags := (evalAluN (by decide) .test (s0.regs .rdx) (s0.regs .rdx) s0.flags (nd 1).flags).2 } := by
    dsimp only [dotO2_entrySeq]
    rw [execInstrSeq_succ_cons, exec_movStore_s64_reg, execInstrSeq_succ_cons, exec_aluRmReg_s64_test, execInstrSeq_zero]
    dsimp only; rw [regUpd_ne _ (by decide)]
  by_cases hlen0 : (s0.regs .rdx).toNat = 0
  · have hzf : evalCond .e (execInstrSeq 2 dotO2_entrySeq 0 nd s0).flags = true := by
      rw [heEnt]; dsimp only; exact evalCond_e_of_zf_true (by rw [test_flags_zf, test64_self_zero_eq]; simp [hlen0])
    let sZ0 := runFrom dotO2Cmap 3 0 nd s0
    have hsZ0 : sZ0 = { execInstrSeq 2 dotO2_entrySeq 0 nd s0 with rip := 0x400220#64 } := by
      dsimp only [sZ0]
      rw [show (3 : Nat) = 2 + 1 by rfl, runFrom_add, hent, runFrom_succ,
          step_at_concrete dotO2_entry_je _ _ hrunE hnfE (by rw [heEnt]), exec_jcc_taken hzf, runFrom_zero]
      rw [heEnt]; rfl
    rcases runFrom_of_decodeSeqAt dotO2_zero_dec 3 nd sZ0
      (by rw [hsZ0, heEnt]; exact hrun) (by rw [hsZ0, heEnt]; exact hnf) (by rw [hsZ0]) with ⟨hzs, hrunZ, hnfZ⟩
    have heZ : execInstrSeq 2 dotO2_zeroSeq 3 nd sZ0 =
        { sZ0 with
          rip := 0x400224#64,
          regs := regUpd (regUpd sZ0.regs .rdx 0#64) .rax 0#64,
          flags := (evalAluN (by decide) .xor (BitVec.extractLsb' 0 32 (sZ0.regs .rdx)) (BitVec.extractLsb' 0 32 (sZ0.regs .rdx)) sZ0.flags (nd 3).flags).2 } := by
      dsimp only [dotO2_zeroSeq]
      rw [execInstrSeq_succ_cons, exec_aluRmReg_s32_xor_self, execInstrSeq_succ_cons, exec_movStore_s32_reg, execInstrSeq_zero]
      dsimp only; rw [regUpd_eq]; rfl
    have hsf : runFrom dotO2Cmap 3 3 nd sZ0 = { execInstrSeq 2 dotO2_zeroSeq 3 nd sZ0 with halted := true } := by
      rw [show (3 : Nat) = 2 + 1 by rfl, runFrom_add, hzs, runFrom_succ,
          step_at_concrete dotO2_zero_ret _ _ hrunZ hnfZ (by rw [heZ]), exec_ret, runFrom_zero]
    refine ⟨6, ?_⟩
    dsimp only; rw [runX64_eq_runFrom, show (6 : Nat) = 3 + 3 by rfl, runFrom_add]
    change (runFrom dotO2Cmap 3 3 nd sZ0).halted = true ∧
      (runFrom dotO2Cmap 3 3 nd sZ0).fault = false ∧
      SysVCalleeSavedPreserved s0 (runFrom dotO2Cmap 3 3 nd sZ0) ∧
      UpperYmmCleanOrPreserved s0 (runFrom dotO2Cmap 3 3 nd sZ0) ∧
      DotU8U16Post 0 s0 (runFrom dotO2Cmap 3 3 nd sZ0)
    rw [hsf, heZ, hsZ0, heEnt]
    refine ⟨rfl, hnf, ?_, fun h => h, ?_, fun _ _ => rfl⟩
    · unfold SysVCalleeSavedPreserved at hcs0 ⊢; dsimp only
      exact cs_step_caller (r := .rax) rfl (cs_step_caller (r := .rdx) rfl (cs_step_caller (r := .r9) rfl hcs0))
    · dsimp only; rw [regUpd_eq, hlen0]; rfl
  · have hzf : evalCond .e (execInstrSeq 2 dotO2_entrySeq 0 nd s0).flags = false := by
      rw [heEnt]; dsimp only; exact evalCond_e_of_zf_false (by rw [test_flags_zf, test64_self_zero_eq]; simp [hlen0])
    let s1 := runFrom dotO2Cmap 3 0 nd s0
    have hs1 : s1 = { execInstrSeq 2 dotO2_entrySeq 0 nd s0 with rip := 0x40014c#64 } := by
      dsimp only [s1]
      rw [show (3 : Nat) = 2 + 1 by rfl, runFrom_add, hent, runFrom_succ,
          step_at_concrete dotO2_entry_je _ _ hrunE hnfE (by rw [heEnt]), exec_jcc_fall hzf, runFrom_zero]
      rw [heEnt]; rfl
    rcases runFrom_of_decodeSeqAt dotO2_lenChk_dec 3 nd s1
      (by rw [hs1, heEnt]; exact hrun) (by rw [hs1, heEnt]; exact hnf) (by rw [hs1]) with ⟨hlc, hrunL, hnfL⟩
    have heL : execInstrSeq 2 dotO2_lenChkSeq 3 nd s1 =
        { s1 with
          rip := 0x400154#64,
          regs := regUpd s1.regs .rax (s0.regs .rdx + 0xffffffffffffffff#64),
          flags := (evalAluN (by decide) .cmp (s0.regs .rdx + 0xffffffffffffffff#64) 0x0e#64 s1.flags (nd 4).flags).2 } := by
      dsimp only [dotO2_lenChkSeq]
      have h1dx : s1.regs .rdx = s0.regs .rdx := by rw [hs1, heEnt]; dsimp only; rw [regUpd_ne _ (by decide)]
      rw [execInstrSeq_succ_cons, exec_lea_s64, evalByteAddr_base_disp, h1dx]
      rw [execInstrSeq_succ_cons, exec_aluImm_s64_cmp, execInstrSeq_zero]
      dsimp only; rw [regUpd_eq]
    have hbe15 := bv64_sub1_cmp_be (s0.regs .rdx) 14 (by omega) (by decide)
    by_cases hle15 : (s0.regs .rdx).toNat ≤ 15
    · have hcc15 : evalCond .be (execInstrSeq 2 dotO2_lenChkSeq 3 nd s1).flags = true := by
        rw [heL]; dsimp only; rw [evalCond_be_of_flags, cmp_flags_cf, cmp_flags_zf]
        change (decide ((s0.regs .rdx + 0xffffffffffffffff#64).toNat < 14) || ((s0.regs .rdx + 0xffffffffffffffff#64) - BitVec.ofNat 64 14 == 0#64)) = true
        rw [hbe15]; simp [hle15]
      let s2 := runFrom dotO2Cmap 3 3 nd s1
      have hs2 : s2 = { execInstrSeq 2 dotO2_lenChkSeq 3 nd s1 with rip := 0x400225#64 } := by
        dsimp only [s2]
        rw [show (3 : Nat) = 2 + 1 by rfl, runFrom_add, hlc, runFrom_succ,
            step_at_concrete dotO2_lenChk_jbe _ _ hrunL hnfL (by rw [heL]), exec_jcc_taken hcc15, runFrom_zero]
        rw [heL]; rfl
      rcases runFrom_of_decodeSeqAt dotO2_small_dec 6 nd s2
        (by rw [hs2, heL, hs1, heEnt]; exact hrun) (by rw [hs2, heL, hs1, heEnt]; exact hnf) (by rw [hs2]) with ⟨hsm, hrunS, hnfS⟩
      have heSm : execInstrSeq 2 dotO2_smallSeq 6 nd s2 =
          { s2 with
            rip := 0x400229#64,
            regs := regUpd (regUpd s2.regs .rax 0#64) .rdx 0#64,
            flags := (evalAluN (by decide) .xor (BitVec.extractLsb' 0 32 (s2.regs .rdx)) (BitVec.extractLsb' 0 32 (s2.regs .rdx))
                       (evalAluN (by decide) .xor (BitVec.extractLsb' 0 32 (s2.regs .rax)) (BitVec.extractLsb' 0 32 (s2.regs .rax)) s2.flags (nd 6).flags).2
                       (nd 7).flags).2 } := by
        dsimp only [dotO2_smallSeq]
        rw [execInstrSeq_succ_cons, exec_aluRmReg_s32_xor_self, execInstrSeq_succ_cons, exec_aluRmReg_s32_xor_self, execInstrSeq_zero]
        dsimp only; rw [regUpd_ne _ (by decide)]
      let s3 := runFrom dotO2Cmap 3 6 nd s2
      have hs3 : s3 = { execInstrSeq 2 dotO2_smallSeq 6 nd s2 with rip := 0x400200#64 } := by
        dsimp only [s3]
        rw [show (3 : Nat) = 2 + 1 by rfl, runFrom_add, hsm, runFrom_succ,
            step_at_concrete dotO2_small_jmp _ _ hrunS hnfS (by rw [heSm]), exec_jmp, runFrom_zero]
        rw [heSm]; rfl
      let kLen := (s0.regs .rdx).toNat - 1
      have hcs3 : SysVCalleeSavedPreserved s0 s3 := by
        unfold SysVCalleeSavedPreserved at hcs0 ⊢
        rw [hs3, heSm, hs2, heL, hs1, heEnt]; dsimp only
        exact cs_step_caller (r := .rdx) rfl (cs_step_caller (r := .rax) rfl
          (cs_step_caller (r := .rax) rfl (cs_step_caller (r := .r9) rfl hcs0)))
      have hLoop := dotO2_scalar_tail_loop s0 hpre nd kLen 9 s3 (by dsimp only [kLen]; omega)
        (by rw [hs3, heSm, hs2, heL, hs1, heEnt]; exact hrun)
        (by rw [hs3, heSm, hs2, heL, hs1, heEnt]; exact hnf)
        (by rw [hs3]) (by rw [hs3, heSm, hs2, heL, hs1, heEnt])
        (by rw [hs3, heSm, hs2, heL, hs1, heEnt]; dsimp only; repeat rw [regUpd_ne _ (by decide)])
        (by rw [hs3, heSm, hs2, heL, hs1, heEnt]; dsimp only; repeat rw [regUpd_ne _ (by decide)])
        (by rw [hs3, heSm, hs2, heL, hs1, heEnt]; dsimp only; rw [regUpd_ne _ (by decide), regUpd_ne _ (by decide), regUpd_ne _ (by decide), regUpd_eq])
        (by rw [hs3, heSm]; dsimp only; rw [regUpd_ne _ (by decide), regUpd_eq, show (s0.regs .rdx).toNat - (kLen + 1) = 0 by dsimp only [kLen]; omega])
        (by rw [hs3, heSm]; dsimp only; rw [regUpd_eq, show (s0.regs .rdx).toNat - (kLen + 1) = 0 by dsimp only [kLen]; omega]; rfl)
        hcs3 (by rw [hs3, heSm, hs2, heL, hs1, heEnt]; exact hymm0)
      rcases hLoop with ⟨hlr, hlf, hlrip, hlm, hldx, hlcs, hlym⟩
      have hRet := dotO2_ret_0x218 s0 (runFrom dotO2Cmap (7 * (kLen + 1)) 9 nd s3) (9 + 7 * (kLen + 1)) nd
        hlr hlf hlrip hlm hldx hlcs hlym
      refine ⟨9 + 7 * (kLen + 1) + 2, ?_⟩
      rw [runX64_eq_runFrom, show 9 + 7 * (kLen + 1) + 2 = (3 + (3 + (3 + 7 * (kLen + 1)))) + 2 by omega,
          runFrom_add, runFrom_add, runFrom_add, runFrom_add,
          show 0 + (3 + (3 + (3 + 7 * (kLen + 1)))) = 9 + 7 * (kLen + 1) by omega]
      exact hRet
    · have hcc15 : evalCond .be (execInstrSeq 2 dotO2_lenChkSeq 3 nd s1).flags = false := by
        rw [heL]; dsimp only; rw [evalCond_be_of_flags, cmp_flags_cf, cmp_flags_zf]
        change (decide ((s0.regs .rdx + 0xffffffffffffffff#64).toNat < 14) || ((s0.regs .rdx + 0xffffffffffffffff#64) - BitVec.ofNat 64 14 == 0#64)) = false
        rw [hbe15]; simp [hle15]
      let s2 := runFrom dotO2Cmap 3 3 nd s1
      have hs2 : s2 = { execInstrSeq 2 dotO2_lenChkSeq 3 nd s1 with rip := 0x40015a#64 } := by
        dsimp only [s2]
        rw [show (3 : Nat) = 2 + 1 by rfl, runFrom_add, hlc, runFrom_succ,
            step_at_concrete dotO2_lenChk_jbe _ _ hrunL hnfL (by rw [heL]), exec_jcc_fall hcc15, runFrom_zero]
        rw [heL]; rfl
      rcases runFrom_of_decodeSeqAt dotO2_simdPre_dec 6 nd s2
        (by rw [hs2, heL, hs1, heEnt]; exact hrun) (by rw [hs2, heL, hs1, heEnt]; exact hnf) (by rw [hs2]) with ⟨hsp, hrunP, hnfP⟩
      let q : Nat := (s0.regs .rdx).toNat / 16
      have hqPos : 1 ≤ q := by dsimp only [q]; omega
      have hqBound : q * 16 ≤ (s0.regs .rdx).toNat := by dsimp only [q]; omega
      have hmask16 : s0.regs .rdx &&& 0xfffffffffffffff0#64 = BitVec.ofNat 64 (q * 16) := by
        apply BitVec.eq_of_toNat_eq; have hlt64 := (s0.regs .rdx).isLt
        rw [bv64_and_neg16_toNat, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)]
      have heP : execInstrSeq 6 dotO2_simdPreSeq 6 nd s2 =
          { s2 with
            rip := 0x400170#64,
            regs := regUpd (regUpd (regUpd s2.regs .rax (s0.regs .rdx)) .rdx 0#64) .rax (BitVec.ofNat 64 (q * 16)),
            ymms := writeXmm128 false (writeXmm128 false s2.ymms y3 0#128) y6 0#128,
            flags := (evalAluN (by decide) .and (s0.regs .rdx) 0xfffffffffffffff0#64
                       (evalAluN (by decide) .xor (BitVec.extractLsb' 0 32 (s0.regs .rdx)) (BitVec.extractLsb' 0 32 (s0.regs .rdx)) s2.flags (nd 9).flags).2
                       (nd 10).flags).2 } := by
        dsimp only [dotO2_simdPreSeq]
        have h2dx : s2.regs .rdx = s0.regs .rdx := by rw [hs2, heL, hs1, heEnt]; dsimp only; rw [regUpd_ne _ (by decide), regUpd_ne _ (by decide)]
        rw [execInstrSeq_succ_cons, exec_movStore_s64_reg, h2dx]
        rw [execInstrSeq_succ_cons, exec_simdBitwise_legacy128_xor_self]
        rw [execInstrSeq_succ_cons, exec_simdBitwise_legacy128_xor_self]
        rw [execInstrSeq_succ_cons, exec_aluRmReg_s32_xor_self]
        dsimp only; rw [regUpd_ne _ (by decide), h2dx]
        rw [execInstrSeq_succ_cons, exec_aluImm_s64_and]
        dsimp only; rw [regUpd_ne _ (by decide), regUpd_eq, hmask16]
        rw [execInstrSeq_succ_cons, exec_nop, execInstrSeq_zero]
      let s3 := runFrom dotO2Cmap 6 6 nd s2
      have hs3 : s3 = execInstrSeq 6 dotO2_simdPreSeq 6 nd s2 := hsp
      have hcs3 : SysVCalleeSavedPreserved s0 s3 := by
        unfold SysVCalleeSavedPreserved at hcs0 ⊢
        rw [hs3, heP, hs2, heL, hs1, heEnt]; dsimp only
        exact cs_step_caller (r := .rax) rfl (cs_step_caller (r := .rdx) rfl (cs_step_caller (r := .rax) rfl
          (cs_step_caller (r := .rax) rfl (cs_step_caller (r := .r9) rfl hcs0))))
      have hym3 : ∀ r : YmmIdx, BitVec.extractLsb' 128 128 (s3.ymms r) = BitVec.extractLsb' 128 128 (s0.ymms r) := by
        intro r; rw [hs3, heP]; dsimp only; rw [writeXmm128_false_preserves_hi, writeXmm128_false_preserves_hi, hs2, heL, hs1, heEnt]
      have hSimd := dotO2_simd_loop s0 hpre nd q (q - 1) 12 s3 (by omega) hqBound
        (by rw [hs3]; exact hrunP) (by rw [hs3]; exact hnfP) (by rw [hs3, heP])
        (by rw [hs3, heP, hs2, heL, hs1, heEnt])
        (by rw [hs3, heP, hs2, heL, hs1, heEnt]; dsimp only; repeat rw [regUpd_ne _ (by decide)])
        (by rw [hs3, heP, hs2, heL, hs1, heEnt]; dsimp only; repeat rw [regUpd_ne _ (by decide)])
        (by rw [hs3, heP, hs2, heL, hs1, heEnt]; dsimp only; rw [regUpd_ne _ (by decide), regUpd_ne _ (by decide), regUpd_ne _ (by decide), regUpd_ne _ (by decide), regUpd_eq])
        (by rw [hs3, heP]; dsimp only; rw [regUpd_eq])
        (by rw [hs3, heP]; dsimp only; rw [regUpd_ne _ (by decide), regUpd_eq, show (q - (q - 1 + 1)) * 16 = 0 by omega])
        (by rw [hs3, heP]; dsimp only; rw [writeXmm128_ne false _ (by decide : y3 ≠ y6), writeXmm128_false_lo, show (q - (q - 1 + 1)) * 16 = 0 by omega]; rfl)
        (by rw [hs3, heP]; dsimp only; exact writeXmm128_false_lo _ _ _)
        hcs3 hym3
      generalize hs4 : runFrom dotO2Cmap (25 * (q - 1 + 1)) 12 nd s3 = s4 at hSimd
      rcases hSimd with ⟨h4r, h4f, h4rip, h4m, h4di, h4si, h4r9, h4ax, h4y3, h4cs, h4ym⟩
      let idx4 := 12 + 25 * (q - 1 + 1)
      rcases runFrom_of_decodeSeqAt dotO2_horiz_dec idx4 nd s4 h4r h4f h4rip with ⟨hhz, hrunH, hnfH⟩
      let v0 := BitVec.extractLsb' 0 128 (s4.ymms y3)
      let v1 := packDwords128 fun i => getDword128 v0 i + getDword128 (psrldq128 v0 8#8) i
      let v2 := packDwords128 fun i => getDword128 v1 i + getDword128 (psrldq128 v1 4#8) i
      let yH1 := writeXmm128 false s4.ymms y0 v0
      let yH2 := writeXmm128 false yH1 y0 (psrldq128 v0 8#8)
      let yH3 := writeXmm128 false yH2 y3 v1
      let yH4 := writeXmm128 false yH3 y0 v1
      let yH5 := writeXmm128 false yH4 y0 (psrldq128 v1 4#8)
      let yH6 := writeXmm128 false yH5 y3 v2
      have hsumV2 : BitVec.extractLsb' 0 32 (yH6 y3) = sumDwords128 v0 := by
        have hlo3 : BitVec.extractLsb' 0 128 (yH6 y3) = v2 := writeXmm128_false_lo _ _ _
        have hex : BitVec.extractLsb' 0 32 (yH6 y3) = BitVec.extractLsb' 0 32 (BitVec.extractLsb' 0 128 (yH6 y3)) := by
          apply BitVec.eq_of_getLsbD_eq; intro b _hb; simp
        rw [hex, hlo3]; exact horiz_reduce_128_eq v0
      have heH : execInstrSeq 8 dotO2_horizSeq idx4 nd s4 =
          { s4 with
            rip := 0x4001f6#64,
            regs := regUpd s4.regs .rdx ((sumDwords128 v0).zeroExtend 64),
            ymms := yH6,
            flags := (evalAluN (by decide) .cmp (s0.regs .rdx) (BitVec.ofNat 64 (q * 16)) s4.flags (nd (idx4 + 7)).flags).2 } := by
        dsimp only [dotO2_horizSeq]
        rw [execInstrSeq_succ_cons, exec_simdMovLoad_legacy128_reg]
        change execInstrSeq 7 _ _ _ { s4 with rip := 0x4001d9#64, ymms := yH1 } = _
        rw [execInstrSeq_succ_cons, exec_simdPsrldq_legacy128]
        dsimp only; rw [show BitVec.extractLsb' 0 128 (yH1 y0) = v0 from writeXmm128_false_lo _ _ _]
        change execInstrSeq 6 _ _ _ { s4 with rip := 0x4001de#64, ymms := yH2 } = _
        rw [execInstrSeq_succ_cons, exec_simdAdd_legacy128_e32_reg]
        dsimp only
        rw [show BitVec.extractLsb' 0 128 (yH2 y3) = v0 from by
              dsimp only [yH2, yH1]; rw [writeXmm128_ne false _ (by decide : y3 ≠ y0), writeXmm128_ne false _ (by decide : y3 ≠ y0)],
            show BitVec.extractLsb' 0 128 (yH2 y0) = psrldq128 v0 8#8 from writeXmm128_false_lo _ _ _]
        change execInstrSeq 5 _ _ _ { s4 with rip := 0x4001e2#64, ymms := yH3 } = _
        rw [execInstrSeq_succ_cons, exec_simdMovLoad_legacy128_reg]
        dsimp only; rw [show BitVec.extractLsb' 0 128 (yH3 y3) = v1 from writeXmm128_false_lo _ _ _]
        change execInstrSeq 4 _ _ _ { s4 with rip := 0x4001e6#64, ymms := yH4 } = _
        rw [execInstrSeq_succ_cons, exec_simdPsrldq_legacy128]
        dsimp only; rw [show BitVec.extractLsb' 0 128 (yH4 y0) = v1 from writeXmm128_false_lo _ _ _]
        change execInstrSeq 3 _ _ _ { s4 with rip := 0x4001eb#64, ymms := yH5 } = _
        rw [execInstrSeq_succ_cons, exec_simdAdd_legacy128_e32_reg]
        dsimp only
        rw [show BitVec.extractLsb' 0 128 (yH5 y3) = v1 from by
              dsimp only [yH5, yH4]; rw [writeXmm128_ne false _ (by decide : y3 ≠ y0), writeXmm128_ne false _ (by decide : y3 ≠ y0), writeXmm128_false_lo],
            show BitVec.extractLsb' 0 128 (yH5 y0) = psrldq128 v1 4#8 from writeXmm128_false_lo _ _ _]
        change execInstrSeq 2 _ _ _ { s4 with rip := 0x4001ef#64, ymms := yH6 } = _
        rw [execInstrSeq_succ_cons, exec_simdMovXToGpr_s32_reg]
        dsimp only; rw [hsumV2]
        rw [execInstrSeq_succ_cons, exec_aluRmReg_s64_cmp, execInstrSeq_zero]
        dsimp only; rw [regUpd_ne _ (by decide), regUpd_ne _ (by decide), h4r9, h4ax]
      have hymH : ∀ r : YmmIdx, BitVec.extractLsb' 128 128 (yH6 r) = BitVec.extractLsb' 128 128 (s0.ymms r) := by
        intro r; dsimp only [yH6, yH5, yH4, yH3, yH2, yH1]
        repeat rw [writeXmm128_false_preserves_hi]
        exact h4ym r
      have hcsH : SysVCalleeSavedPreserved s0 (execInstrSeq 8 dotO2_horizSeq idx4 nd s4) := by
        unfold SysVCalleeSavedPreserved at h4cs ⊢; rw [heH]; dsimp only
        exact cs_step_caller (r := .rdx) rfl h4cs
      by_cases hmod16 : (s0.regs .rdx).toNat = q * 16
      · have hdxEq : s0.regs .rdx = BitVec.ofNat 64 (q * 16) := by
          rw [← hmod16, BitVec.ofNat_toNat, BitVec.setWidth_eq]
        have hzf16 : evalCond .e (execInstrSeq 8 dotO2_horizSeq idx4 nd s4).flags = true := by
          rw [heH]; dsimp only; exact evalCond_e_of_zf_true (by rw [cmp_flags_zf, ← hdxEq, cmp_sub_self_zero])
        let s5 := runFrom dotO2Cmap 9 idx4 nd s4
        have hs5 : s5 = { execInstrSeq 8 dotO2_horizSeq idx4 nd s4 with rip := 0x400218#64 } := by
          dsimp only [s5]
          rw [show (9 : Nat) = 8 + 1 by rfl, runFrom_add, hhz, runFrom_succ,
              step_at_concrete dotO2_horiz_je _ _ hrunH hnfH (by rw [heH]), exec_jcc_taken hzf16, runFrom_zero]
          rw [heH]; rfl
        have hRet := dotO2_ret_0x218 s0 s5 (idx4 + 9) nd
          (by rw [hs5]; exact hrunH) (by rw [hs5]; exact hnfH) (by rw [hs5])
          (by rw [hs5, heH]; exact h4m)
          (by rw [hs5, heH]; dsimp only; rw [regUpd_eq, zext32_extract32_eq, h4y3, ← hmod16]; rfl)
          (by rw [hs5]; exact hcsH) (by rw [hs5, heH]; exact hymH)
        refine ⟨idx4 + 9 + 2, ?_⟩
        have hrunS4 : runFrom (objCodeMap cFfiKernelsO2Obj) (idx4 + 9 + 2) 0 nd s0 =
            runFrom dotO2Cmap 2 (idx4 + 9) nd s5 := by
          have hcm : objCodeMap cFfiKernelsO2Obj = dotO2Cmap := rfl
          rw [hcm, show idx4 + 9 + 2 = (3 + (3 + (6 + 25 * (q - 1 + 1)))) + (9 + 2) by dsimp only [idx4]; omega,
              runFrom_add, runFrom_add, runFrom_add, runFrom_add, runFrom_add,
              show (0 : Nat) + 3 = 3 by rfl, show (3 : Nat) + 3 = 6 by rfl, show (6 : Nat) + 6 = 12 by rfl]
          change runFrom dotO2Cmap 2 (0 + (3 + (3 + (6 + 25 * (q - 1 + 1)))) + 9) nd
            (runFrom dotO2Cmap 9 (0 + (3 + (3 + (6 + 25 * (q - 1 + 1))))) nd (runFrom dotO2Cmap (25 * (q - 1 + 1)) 12 nd s3)) = _
          rw [hs4, show 0 + (3 + (3 + (6 + 25 * (q - 1 + 1)))) = idx4 by dsimp only [idx4]; omega]
        rw [runX64_eq_runFrom, hrunS4]
        exact hRet
      · have hdxNe : s0.regs .rdx ≠ BitVec.ofNat 64 (q * 16) := by
          intro heq; have hlt64 := (s0.regs .rdx).isLt; have ht := congrArg BitVec.toNat heq
          rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)] at ht; exact hmod16 ht
        have hzf16 : evalCond .e (execInstrSeq 8 dotO2_horizSeq idx4 nd s4).flags = false := by
          rw [heH]; dsimp only; exact evalCond_e_of_zf_false (by rw [cmp_flags_zf, cmp_sub_zero_false_of_ne hdxNe])
        let s5 := runFrom dotO2Cmap 10 idx4 nd s4
        have hs5 : s5 = { execInstrSeq 8 dotO2_horizSeq idx4 nd s4 with rip := 0x400200#64 } := by
          dsimp only [s5]
          rw [show (10 : Nat) = 8 + 2 by rfl, runFrom_add, hhz, runFrom_succ,
              step_at_concrete dotO2_horiz_je _ _ hrunH hnfH (by rw [heH]), exec_jcc_fall hzf16]
          rw [runFrom_succ, step_at_concrete dotO2_horiz_nop _ { execInstrSeq 8 dotO2_horizSeq idx4 nd s4 with rip := 0x4001f6#64 + BitVec.ofNat 64 2 } hrunH hnfH rfl,
              exec_nop, runFrom_zero]
          rw [heH]; rfl
        let rem := (s0.regs .rdx).toNat - q * 16
        have hremPos : 1 ≤ rem := by dsimp only [rem]; omega
        have hsubRem : (s0.regs .rdx).toNat - (rem - 1 + 1) = q * 16 := by dsimp only [rem]; omega
        have hTail := dotO2_scalar_tail_loop s0 hpre nd (rem - 1) (idx4 + 10) s5 (by dsimp only [rem]; omega)
          (by rw [hs5]; exact hrunH) (by rw [hs5]; exact hnfH) (by rw [hs5])
          (by rw [hs5, heH]; exact h4m)
          (by rw [hs5, heH]; dsimp only; rw [regUpd_ne _ (by decide), h4di])
          (by rw [hs5, heH]; dsimp only; rw [regUpd_ne _ (by decide), h4si])
          (by rw [hs5, heH]; dsimp only; rw [regUpd_ne _ (by decide), h4r9])
          (by rw [hs5, heH]; dsimp only; rw [regUpd_ne _ (by decide), h4ax, hsubRem])
          (by rw [hs5, heH]; dsimp only; rw [regUpd_eq, zext32_extract32_eq, h4y3, hsubRem])
          (by rw [hs5]; exact hcsH) (by rw [hs5, heH]; exact hymH)
        rcases hTail with ⟨htr, htf, htrip, htm, htdx, htcs, htym⟩
        have hRet := dotO2_ret_0x218 s0 (runFrom dotO2Cmap (7 * (rem - 1 + 1)) (idx4 + 10) nd s5)
          (idx4 + 10 + 7 * (rem - 1 + 1)) nd htr htf htrip htm htdx htcs htym
        refine ⟨idx4 + 10 + 7 * (rem - 1 + 1) + 2, ?_⟩
        have hrunS4 : runFrom (objCodeMap cFfiKernelsO2Obj) (idx4 + 10 + 7 * (rem - 1 + 1) + 2) 0 nd s0 =
            runFrom dotO2Cmap 2 (idx4 + 10 + 7 * (rem - 1 + 1)) nd (runFrom dotO2Cmap (7 * (rem - 1 + 1)) (idx4 + 10) nd s5) := by
          have hcm : objCodeMap cFfiKernelsO2Obj = dotO2Cmap := rfl
          rw [hcm, show idx4 + 10 + 7 * (rem - 1 + 1) + 2 =
              (3 + (3 + (6 + 25 * (q - 1 + 1)))) + ((10 + 7 * (rem - 1 + 1)) + 2) by dsimp only [idx4]; omega,
              runFrom_add, runFrom_add, runFrom_add, runFrom_add, runFrom_add, runFrom_add,
              show (0 : Nat) + 3 = 3 by rfl, show (3 : Nat) + 3 = 6 by rfl, show (6 : Nat) + 6 = 12 by rfl]
          change runFrom dotO2Cmap 2 (0 + (3 + (3 + (6 + 25 * (q - 1 + 1)))) + (10 + 7 * (rem - 1 + 1))) nd
            (runFrom dotO2Cmap (7 * (rem - 1 + 1)) (0 + (3 + (3 + (6 + 25 * (q - 1 + 1)))) + 10) nd
              (runFrom dotO2Cmap 10 (0 + (3 + (3 + (6 + 25 * (q - 1 + 1))))) nd (runFrom dotO2Cmap (25 * (q - 1 + 1)) 12 nd s3))) = _
          rw [hs4, show 0 + (3 + (3 + (6 + 25 * (q - 1 + 1)))) = idx4 by dsimp only [idx4]; omega, ← Nat.add_assoc]
        rw [runX64_eq_runFrom, hrunS4]
        exact hRet

end UntrustedCObjDotSimd
