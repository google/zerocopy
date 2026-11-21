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
# `UntrustedCObjDotAvx2Tail`

Cascading epilogue proofs (`16`-elem VEX-128 -> `8`-elem `vpmulld`+`vpsrlq 0x20`
-> unrolled `1..7`-elem scalar tail) for `gcc 15.2.0 -O3 -mavx2` `c_dot_u8_u16`
(`cFfiKernelsO3Avx2Obj` at `0x140`, `stackReserve = 0`, `0` `sorry`, `0` `isPartial`).
Split from `UntrustedCObjDotAvx2` so each module stays well below the `< 15 s`
synchronous compilation budget.
-/

namespace UntrustedCObjDotAvx2Tail

open ByteX86Gcc
open RustFfiSpecs
open CompiledCObjImages
open UntrustedCObjHints
open UntrustedCObjSimdHelpers

def dotO3Cmap : CodeMap := objCodeMap cFfiKernelsO3Avx2Obj

private abbrev y0 : YmmIdx := ⟨0, by decide⟩
private abbrev y1 : YmmIdx := ⟨1, by decide⟩
private abbrev y2 : YmmIdx := ⟨2, by decide⟩
private abbrev y3 : YmmIdx := ⟨3, by decide⟩
private abbrev y4 : YmmIdx := ⟨4, by decide⟩
private abbrev y5 : YmmIdx := ⟨5, by decide⟩
private abbrev y6 : YmmIdx := ⟨6, by decide⟩

theorem writeXmm128_true_lo (ymms : YmmIdx → BitVec 256) (r : YmmIdx) (v : BitVec 128) :
    BitVec.extractLsb' 0 128 (writeXmm128 true ymms r v r) = v := by
  rw [writeXmm128_true_eq, ymmUpd_eq, extract_lo128_append]

/-! ## Section 1: Pure-Bool Reflected Decodes (`0x211..0x44f`) -/

theorem dotO3_ret426 : decodeX64 (fetchWindow16 dotO3Cmap 0x400426#64) =
    .ok .ret64 1 := decodeAt_of_check rfl

private def dotO3_epi16ChkSeq : List (X64Instr × BitVec 64) := [
  (.movStore .s64 (.reg .r8) .rdx, 0x400214#64),
  (.aluRmReg .s64 .sub (.reg .r8) .r9, 0x400217#64),
  (.lea .s64 .rcx { base := some .r8, disp := 0xffffffffffffffff#64 }, 0x40021b#64),
  (.aluImm .s64 .cmp (.reg .rcx) 0x0e#64, 0x40021f#64)
]
private theorem dotO3_epi16Chk_dec : decodeSeqAt dotO3Cmap 4 0x400211#64 = some dotO3_epi16ChkSeq :=
  decodeSeqAt_of_check rfl rfl
private theorem dotO3_epi16Chk_jbe : decodeX64 (fetchWindow16 dotO3Cmap 0x40021f#64) =
    .ok (.jccRel .be 0x000000000000021c#64) 6 := decodeAt_of_check rfl

private def dotO3_skip16Seq : List (X64Instr × BitVec 64) := [
  (.simdMovGprToX true false y5 (.reg .rax), 0x400445#64),
  (.movStore .s64 (.reg .rcx) .r9, 0x400448#64),
  (.aluRmReg .s32 .xor (.reg .r10) .r10, 0x40044b#64)
]
private theorem dotO3_skip16_dec : decodeSeqAt dotO3Cmap 3 0x400441#64 = some dotO3_skip16Seq :=
  decodeSeqAt_of_check rfl rfl
private theorem dotO3_skip16_jmp : decodeX64 (fetchWindow16 dotO3Cmap 0x40044b#64) =
    .ok (.jmpRel 0xfffffffffffffe5f#64) 5 := decodeAt_of_check rfl

private def dotO3_epi16ASeq : List (X64Instr × BitVec 64) := [
  (.lea .s64 .rax { base := some .rsi, index := some (.r9, 1) }, 0x400229#64),
  (.simdMovLoad .vex128 y1 (.mem { base := some .rdi, index := some (.r9, 0) }), 0x40022f#64),
  (.simdMovLoad .vex128 y5 (.mem { base := some .rax }), 0x400233#64),
  (.simdMovLoad .vex128 y4 (.mem { base := some .rax, disp := 0x10#64 }), 0x400238#64),
  (.simdExtend .vex128 .zxbw y3 (.reg y1), 0x40023d#64),
  (.simdPsrldq .vex128 y1 y1 0x08#8, 0x400242#64),
  (.simdPmullw .vex128 y0 y3 (.reg y5), 0x400246#64),
  (.simdPmulhuw .vex128 y3 y3 (.reg y5), 0x40024a#64)
]
private theorem dotO3_epi16A_dec : decodeSeqAt dotO3Cmap 8 0x400225#64 = some dotO3_epi16ASeq :=
  decodeSeqAt_of_check rfl rfl

private def dotO3_epi16BSeq : List (X64Instr × BitVec 64) := [
  (.simdExtend .vex128 .zxbw y1 (.reg y1), 0x40024f#64),
  (.simdUnpack .vex128 .lwd y5 y0 (.reg y3), 0x400253#64),
  (.simdUnpack .vex128 .hwd y0 y0 (.reg y3), 0x400257#64),
  (.simdAdd .vex128 .e32 y0 y0 (.reg y5), 0x40025b#64),
  (.simdAdd .vex128 .e32 y0 y0 (.reg y2), 0x40025f#64),
  (.simdPmullw .vex128 y2 y1 (.reg y4), 0x400263#64),
  (.simdPmulhuw .vex128 y1 y1 (.reg y4), 0x400267#64),
  (.simdUnpack .vex128 .lwd y3 y2 (.reg y1), 0x40026b#64)
]
private theorem dotO3_epi16B_dec : decodeSeqAt dotO3Cmap 8 0x40024a#64 = some dotO3_epi16BSeq :=
  decodeSeqAt_of_check rfl rfl

private def dotO3_epi16CSeq : List (X64Instr × BitVec 64) := [
  (.simdUnpack .vex128 .hwd y2 y2 (.reg y1), 0x40026f#64),
  (.simdAdd .vex128 .e32 y2 y2 (.reg y3), 0x400273#64),
  (.simdAdd .vex128 .e32 y0 y0 (.reg y2), 0x400277#64),
  (.simdPsrldq .vex128 y1 y0 0x08#8, 0x40027c#64),
  (.simdAdd .vex128 .e32 y1 y0 (.reg y1), 0x400280#64),
  (.simdPsrldq .vex128 y2 y1 0x04#8, 0x400285#64),
  (.simdAdd .vex128 .e32 y1 y1 (.reg y2), 0x400289#64),
  (.simdMovXToGpr true false (.reg .rax) y1, 0x40028d#64),
  (.alu8Imm .test (.reg8 (.lo8 .r8)) 0x0f#8, 0x400291#64)
]
private theorem dotO3_epi16C_dec : decodeSeqAt dotO3Cmap 9 0x40026b#64 = some dotO3_epi16CSeq :=
  decodeSeqAt_of_check rfl rfl
private theorem dotO3_epi16_je : decodeX64 (fetchWindow16 dotO3Cmap 0x400291#64) =
    .ok (.jccRel .e 0x000000000000018f#64) 6 := decodeAt_of_check rfl

private def dotO3_post16Seq : List (X64Instr × BitVec 64) := [
  (.simdMovLoad .vex128 y5 (.reg y0), 0x40029b#64),
  (.simdPsrldq .vex128 y0 y0 0x08#8, 0x4002a0#64),
  (.movStore .s64 (.reg .r10) .r8, 0x4002a3#64),
  (.simdAdd .vex128 .e32 y5 y5 (.reg y0), 0x4002a7#64),
  (.aluImm .s64 .and (.reg .r10) 0xfffffffffffffff0#64, 0x4002ab#64),
  (.lea .s64 .rcx { base := some .r9, index := some (.r10, 0) }, 0x4002af#64)
]
private theorem dotO3_post16_dec : decodeSeqAt dotO3Cmap 6 0x400297#64 = some dotO3_post16Seq :=
  decodeSeqAt_of_check rfl rfl

private def dotO3_epi8ChkSeq : List (X64Instr × BitVec 64) := [
  (.aluRmReg .s64 .sub (.reg .r8) .r10, 0x4002b2#64),
  (.lea .s64 .r11 { base := some .r8, disp := 0xffffffffffffffff#64 }, 0x4002b6#64),
  (.aluImm .s64 .cmp (.reg .r11) 0x06#64, 0x4002ba#64)
]
private theorem dotO3_epi8Chk_dec : decodeSeqAt dotO3Cmap 3 0x4002af#64 = some dotO3_epi8ChkSeq :=
  decodeSeqAt_of_check rfl rfl
private theorem dotO3_epi8Chk_jbe : decodeX64 (fetchWindow16 dotO3Cmap 0x4002ba#64) =
    .ok (.jccRel .be 0x00000000000000a5#64) 6 := decodeAt_of_check rfl

private def dotO3_epi8ASeq : List (X64Instr × BitVec 64) := [
  (.lea .s64 .rax { base := some .r9, index := some (.r10, 0) }, 0x4002c4#64),
  (.simdMovqLoad true y0 (.mem { base := some .rdi, index := some (.rax, 0) }), 0x4002c9#64),
  (.lea .s64 .r9 { base := some .rsi, index := some (.rax, 1) }, 0x4002cd#64),
  (.simdMovqLoad true y4 (.mem { base := some .r9 }), 0x4002d2#64),
  (.simdMovqLoad true y3 (.mem { base := some .r9, disp := 0x08#64 }), 0x4002d8#64),
  (.simdExtend .vex128 .zxbw y2 (.reg y0), 0x4002dd#64),
  (.simdPsrlqImm .vex128 y0 y0 0x20#8, 0x4002e2#64),
  (.simdExtend .vex128 .zxwd y1 (.reg y2), 0x4002e7#64)
]
private theorem dotO3_epi8A_dec : decodeSeqAt dotO3Cmap 8 0x4002c0#64 = some dotO3_epi8ASeq :=
  decodeSeqAt_of_check rfl rfl

private def dotO3_epi8BSeq : List (X64Instr × BitVec 64) := [
  (.simdExtend .vex128 .zxwd y6 (.reg y4), 0x4002ec#64),
  (.simdExtend .vex128 .zxbw y0 (.reg y0), 0x4002f1#64),
  (.simdPsrlqImm .vex128 y2 y2 0x20#8, 0x4002f6#64),
  (.simdPsrlqImm .vex128 y4 y4 0x20#8, 0x4002fb#64),
  (.simdExtend .vex128 .zxwd y4 (.reg y4), 0x400300#64),
  (.simdPmulld .vex128 y1 y1 (.reg y6), 0x400305#64),
  (.simdExtend .vex128 .zxwd y2 (.reg y2), 0x40030a#64),
  (.simdPmulld .vex128 y2 y2 (.reg y4), 0x40030f#64)
]
private theorem dotO3_epi8B_dec : decodeSeqAt dotO3Cmap 8 0x4002e7#64 = some dotO3_epi8BSeq :=
  decodeSeqAt_of_check rfl rfl

private def dotO3_epi8CSeq : List (X64Instr × BitVec 64) := [
  (.simdExtend .vex128 .zxwd y4 (.reg y3), 0x400314#64),
  (.simdPsrlqImm .vex128 y3 y3 0x20#8, 0x400319#64),
  (.simdExtend .vex128 .zxwd y3 (.reg y3), 0x40031e#64),
  (.simdAdd .vex128 .e32 y1 y1 (.reg y2), 0x400322#64),
  (.simdExtend .vex128 .zxwd y2 (.reg y0), 0x400327#64),
  (.simdPsrlqImm .vex128 y0 y0 0x20#8, 0x40032c#64),
  (.simdPmulld .vex128 y2 y2 (.reg y4), 0x400331#64),
  (.simdExtend .vex128 .zxwd y0 (.reg y0), 0x400336#64)
]
private theorem dotO3_epi8C_dec : decodeSeqAt dotO3Cmap 8 0x40030f#64 = some dotO3_epi8CSeq :=
  decodeSeqAt_of_check rfl rfl

private def dotO3_epi8DSeq : List (X64Instr × BitVec 64) := [
  (.simdPmulld .vex128 y0 y0 (.reg y3), 0x40033b#64),
  (.simdAdd .vex128 .e32 y1 y1 (.reg y5), 0x40033f#64),
  (.simdAdd .vex128 .e32 y0 y2 (.reg y0), 0x400343#64),
  (.simdAdd .vex128 .e32 y0 y1 (.reg y0), 0x400347#64),
  (.simdPsrlqImm .vex128 y1 y0 0x20#8, 0x40034c#64),
  (.simdAdd .vex128 .e32 y0 y0 (.reg y1), 0x400350#64),
  (.simdMovXToGpr true false (.reg .rax) y0, 0x400354#64),
  (.alu8Imm .test (.reg8 (.lo8 .r8)) 0x07#8, 0x400358#64)
]
private theorem dotO3_epi8D_dec : decodeSeqAt dotO3Cmap 8 0x400336#64 = some dotO3_epi8DSeq :=
  decodeSeqAt_of_check rfl rfl
private theorem dotO3_epi8_je : decodeX64 (fetchWindow16 dotO3Cmap 0x400358#64) =
    .ok (.jccRel .e 0x00000000000000c8#64) 6 := decodeAt_of_check rfl

private def dotO3_post8Seq : List (X64Instr × BitVec 64) := [
  (.aluImm .s64 .and (.reg .r8) 0xfffffffffffffff8#64, 0x400362#64),
  (.aluRmReg .s64 .add (.reg .rcx) .r8, 0x400365#64)
]
private theorem dotO3_post8_dec : decodeSeqAt dotO3Cmap 2 0x40035e#64 = some dotO3_post8Seq :=
  decodeSeqAt_of_check rfl rfl

private def dotO3_t0Seq : List (X64Instr × BitVec 64) := [
  (.movzx8 .s32 .r8 (.mem8 { base := some .rdi, index := some (.rcx, 0) }), 0x40036a#64),
  (.movzx16 .s32 .r9 (.mem { base := some .rsi, index := some (.rcx, 1) }), 0x40036f#64),
  (.imul2 .s32 .r8 (.reg .r9), 0x400373#64),
  (.aluRmReg .s32 .add (.reg .rax) .r8, 0x400376#64),
  (.lea .s64 .r8 { base := some .rcx, disp := 1#64 }, 0x40037a#64),
  (.aluRmReg .s64 .cmp (.reg .r8) .rdx, 0x40037d#64)
]
private theorem dotO3_t0_dec : decodeSeqAt dotO3Cmap 6 0x400365#64 = some dotO3_t0Seq :=
  decodeSeqAt_of_check rfl rfl
private theorem dotO3_t0_jae : decodeX64 (fetchWindow16 dotO3Cmap 0x40037d#64) =
    .ok (.jccRel .ae 0x00000000000000a3#64) 6 := decodeAt_of_check rfl

private def dotO3_t1Seq : List (X64Instr × BitVec 64) := [
  (.movzx16 .s32 .r8 (.mem { base := some .rsi, index := some (.rcx, 1), disp := 2#64 }), 0x400389#64),
  (.movzx8 .s32 .r9 (.mem8 { base := some .rdi, index := some (.rcx, 0), disp := 1#64 }), 0x40038f#64),
  (.imul2 .s32 .r8 (.reg .r9), 0x400393#64),
  (.aluRmReg .s32 .add (.reg .rax) .r8, 0x400396#64),
  (.lea .s64 .r8 { base := some .rcx, disp := 2#64 }, 0x40039a#64),
  (.aluRmReg .s64 .cmp (.reg .r8) .rdx, 0x40039d#64)
]
private theorem dotO3_t1_dec : decodeSeqAt dotO3Cmap 6 0x400383#64 = some dotO3_t1Seq :=
  decodeSeqAt_of_check rfl rfl
private theorem dotO3_t1_jae : decodeX64 (fetchWindow16 dotO3Cmap 0x40039d#64) =
    .ok (.jccRel .ae 0x0000000000000083#64) 6 := decodeAt_of_check rfl

private def dotO3_t2Seq : List (X64Instr × BitVec 64) := [
  (.movzx16 .s32 .r8 (.mem { base := some .rsi, index := some (.rcx, 1), disp := 4#64 }), 0x4003a9#64),
  (.movzx8 .s32 .r9 (.mem8 { base := some .rdi, index := some (.rcx, 0), disp := 2#64 }), 0x4003af#64),
  (.imul2 .s32 .r8 (.reg .r9), 0x4003b3#64),
  (.aluRmReg .s32 .add (.reg .rax) .r8, 0x4003b6#64),
  (.lea .s64 .r8 { base := some .rcx, disp := 3#64 }, 0x4003ba#64),
  (.aluRmReg .s64 .cmp (.reg .r8) .rdx, 0x4003bd#64)
]
private theorem dotO3_t2_dec : decodeSeqAt dotO3Cmap 6 0x4003a3#64 = some dotO3_t2Seq :=
  decodeSeqAt_of_check rfl rfl
private theorem dotO3_t2_jae : decodeX64 (fetchWindow16 dotO3Cmap 0x4003bd#64) =
    .ok (.jccRel .ae 0x0000000000000067#64) 2 := decodeAt_of_check rfl

private def dotO3_t3Seq : List (X64Instr × BitVec 64) := [
  (.movzx16 .s32 .r8 (.mem { base := some .rsi, index := some (.rcx, 1), disp := 6#64 }), 0x4003c5#64),
  (.movzx8 .s32 .r9 (.mem8 { base := some .rdi, index := some (.rcx, 0), disp := 3#64 }), 0x4003cb#64),
  (.imul2 .s32 .r8 (.reg .r9), 0x4003cf#64),
  (.aluRmReg .s32 .add (.reg .rax) .r8, 0x4003d2#64),
  (.lea .s64 .r8 { base := some .rcx, disp := 4#64 }, 0x4003d6#64),
  (.aluRmReg .s64 .cmp (.reg .r8) .rdx, 0x4003d9#64)
]
private theorem dotO3_t3_dec : decodeSeqAt dotO3Cmap 6 0x4003bf#64 = some dotO3_t3Seq :=
  decodeSeqAt_of_check rfl rfl
private theorem dotO3_t3_jae : decodeX64 (fetchWindow16 dotO3Cmap 0x4003d9#64) =
    .ok (.jccRel .ae 0x000000000000004b#64) 2 := decodeAt_of_check rfl

private def dotO3_t4Seq : List (X64Instr × BitVec 64) := [
  (.movzx16 .s32 .r8 (.mem { base := some .rsi, index := some (.rcx, 1), disp := 8#64 }), 0x4003e1#64),
  (.movzx8 .s32 .r9 (.mem8 { base := some .rdi, index := some (.rcx, 0), disp := 4#64 }), 0x4003e7#64),
  (.imul2 .s32 .r8 (.reg .r9), 0x4003eb#64),
  (.aluRmReg .s32 .add (.reg .rax) .r8, 0x4003ee#64),
  (.lea .s64 .r8 { base := some .rcx, disp := 5#64 }, 0x4003f2#64),
  (.aluRmReg .s64 .cmp (.reg .r8) .rdx, 0x4003f5#64)
]
private theorem dotO3_t4_dec : decodeSeqAt dotO3Cmap 6 0x4003db#64 = some dotO3_t4Seq :=
  decodeSeqAt_of_check rfl rfl
private theorem dotO3_t4_jae : decodeX64 (fetchWindow16 dotO3Cmap 0x4003f5#64) =
    .ok (.jccRel .ae 0x000000000000002f#64) 2 := decodeAt_of_check rfl

private def dotO3_t5Seq : List (X64Instr × BitVec 64) := [
  (.movzx16 .s32 .r8 (.mem { base := some .rsi, index := some (.rcx, 1), disp := 0x0a#64 }), 0x4003fd#64),
  (.movzx8 .s32 .r9 (.mem8 { base := some .rdi, index := some (.rcx, 0), disp := 5#64 }), 0x400403#64),
  (.imul2 .s32 .r8 (.reg .r9), 0x400407#64),
  (.aluRmReg .s32 .add (.reg .rax) .r8, 0x40040a#64),
  (.lea .s64 .r8 { base := some .rcx, disp := 6#64 }, 0x40040e#64),
  (.aluRmReg .s64 .cmp (.reg .r8) .rdx, 0x400411#64)
]
private theorem dotO3_t5_dec : decodeSeqAt dotO3Cmap 6 0x4003f7#64 = some dotO3_t5Seq :=
  decodeSeqAt_of_check rfl rfl
private theorem dotO3_t5_jae : decodeX64 (fetchWindow16 dotO3Cmap 0x400411#64) =
    .ok (.jccRel .ae 0x0000000000000013#64) 2 := decodeAt_of_check rfl

private def dotO3_t6Seq : List (X64Instr × BitVec 64) := [
  (.movzx16 .s32 .rdx (.mem { base := some .rsi, index := some (.rcx, 1), disp := 0x0c#64 }), 0x400418#64),
  (.movzx8 .s32 .rcx (.mem8 { base := some .rdi, index := some (.rcx, 0), disp := 6#64 }), 0x40041d#64),
  (.imul2 .s32 .rdx (.reg .rcx), 0x400420#64),
  (.aluRmReg .s32 .add (.reg .rax) .rdx, 0x400422#64)
]
private theorem dotO3_t6_dec : decodeSeqAt dotO3Cmap 4 0x400413#64 = some dotO3_t6Seq :=
  decodeSeqAt_of_check rfl rfl
private theorem dotO3_ret422 : decodeX64 (fetchWindow16 dotO3Cmap 0x400422#64) =
    .ok .ret64 1 := decodeAt_of_check rfl

/-! ## Section 2: Unrolled `1..7`-Elem Scalar Tail (`0x365..0x426`) -/

private theorem zext16_32_64 (w : BitVec 16) : BitVec.extractLsb' 0 32 (w.zeroExtend 64) = w.zeroExtend 32 := by
  apply BitVec.eq_of_getLsbD_eq; intro b hb; unfold BitVec.zeroExtend; simp [hb, show b < 64 by omega]

private theorem zext8_32_64 (v : BitVec 8) : BitVec.extractLsb' 0 32 (v.zeroExtend 64) = v.zeroExtend 32 := by
  apply BitVec.eq_of_getLsbD_eq; intro b hb; unfold BitVec.zeroExtend; simp [hb, show b < 64 by omega]

private theorem dotO3_ret_at (s0 s : X64State) (retIp : BitVec 64) (idx : Nat) (nd : Nat → UndefChoice)
    (hdec : decodeX64 (fetchWindow16 dotO3Cmap retIp) = .ok .ret64 1)
    (hrun : s.halted = false) (hnf : s.fault = false) (hrip : s.rip = retIp) (hmem : s.mem = s0.mem)
    (hrax : BitVec.extractLsb' 0 32 (s.regs .rax) = rustDotU8U16 s0.mem (s0.regs .rdi) (s0.regs .rsi) (s0.regs .rdx).toNat)
    (hcs : SysVCalleeSavedPreserved s0 s) (hymm : UpperYmmCleanOrPreserved s0 s) :
    let sf := runFrom dotO3Cmap 1 idx nd s
    sf.halted = true ∧ sf.fault = false ∧
    SysVCalleeSavedPreserved s0 sf ∧ UpperYmmCleanOrPreserved s0 sf ∧
    DotU8U16Post 0 s0 sf := by
  dsimp only; rw [runFrom_succ, step_at_concrete hdec _ s hrun hnf hrip, exec_ret, runFrom_zero]
  exact ⟨rfl, hnf, hcs, hymm, hrax, fun _ _ => hmem ▸ rfl⟩

private theorem dotO3_tail_step {rip nextRip jaeRel : BitVec 64} {k jaeLen : Nat}
    {n1 n2 n3 n4 n5 : BitVec 64}
    (hdec : decodeSeqAt dotO3Cmap 6 rip = some [
      (.movzx16 .s32 .r8 (.mem { base := some .rsi, index := some (.rcx, 1), disp := BitVec.ofNat 64 (2 * k) }), n1),
      (.movzx8 .s32 .r9 (.mem8 { base := some .rdi, index := some (.rcx, 0), disp := BitVec.ofNat 64 k }), n2),
      (.imul2 .s32 .r8 (.reg .r9), n3),
      (.aluRmReg .s32 .add (.reg .rax) .r8, n4),
      (.lea .s64 .r8 { base := some .rcx, disp := BitVec.ofNat 64 (k + 1) }, n5),
      (.aluRmReg .s64 .cmp (.reg .r8) .rdx, nextRip)
    ])
    (hjae : decodeX64 (fetchWindow16 dotO3Cmap nextRip) = .ok (.jccRel .ae jaeRel) jaeLen)
    (htgt : nextRip + BitVec.ofNat 64 jaeLen + jaeRel = 0x400426#64)
    (s0 s : X64State) (base idx : Nat) (nd : Nat → UndefChoice)
    (hpre : DotU8U16Pre 0 s0)
    (hrun : s.halted = false) (hnf : s.fault = false) (hrip : s.rip = rip) (hmem : s.mem = s0.mem)
    (hrdi : s.regs .rdi = s0.regs .rdi) (hrsi : s.regs .rsi = s0.regs .rsi)
    (hrdx : s.regs .rdx = s0.regs .rdx) (hrcx : s.regs .rcx = BitVec.ofNat 64 base)
    (hrax : BitVec.extractLsb' 0 32 (s.regs .rax) =
      rustDotU8U16From s0.mem (s0.regs .rdi) (s0.regs .rsi) (base + k) 0#32)
    (hcs : SysVCalleeSavedPreserved s0 s) (hymm : UpperYmmCleanOrPreserved s0 s)
    (hlt : base + k < (s0.regs .rdx).toNat) :
    let s' := runFrom dotO3Cmap 7 idx nd s
    s'.halted = false ∧ s'.fault = false ∧
    s'.rip = (if base + (k + 1) < (s0.regs .rdx).toNat then nextRip + BitVec.ofNat 64 jaeLen else 0x400426#64) ∧
    s'.mem = s0.mem ∧
    s'.regs .rdi = s0.regs .rdi ∧ s'.regs .rsi = s0.regs .rsi ∧
    s'.regs .rdx = s0.regs .rdx ∧ s'.regs .rcx = BitVec.ofNat 64 base ∧
    BitVec.extractLsb' 0 32 (s'.regs .rax) =
      rustDotU8U16From s0.mem (s0.regs .rdi) (s0.regs .rsi) (base + (k + 1)) 0#32 ∧
    SysVCalleeSavedPreserved s0 s' ∧ UpperYmmCleanOrPreserved s0 s' := by
  have h2len := hpre.1
  have hlenLt := (s0.regs .rdx).isLt
  have hshl : BitVec.ofNat 64 base <<< 1 = BitVec.ofNat 64 (2 * base) := by
    have htn : (BitVec.ofNat 64 base).toNat = base := by rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)]
    rw [bv64_shl1_toNat (by rw [htn]; omega), htn]
  have haddrB : (s0.regs .rsi + BitVec.ofNat 64 (2 * base)) + BitVec.ofNat 64 (2 * k) =
      s0.regs .rsi + BitVec.ofNat 64 (2 * (base + k)) := by
    rw [bv64_add_ofNat_assoc]; congr 2; omega
  have haddrA : (s0.regs .rdi + BitVec.ofNat 64 base) + BitVec.ofNat 64 k =
      s0.regs .rdi + BitVec.ofNat 64 (base + k) := bv64_add_ofNat_assoc _ _ _
  have haddK1 : BitVec.ofNat 64 base + BitVec.ofNat 64 (k + 1) = BitVec.ofNat 64 (base + (k + 1)) :=
    bv64_ofNat_add _ _
  let w16 := readMem16 s0.mem (s0.regs .rsi + BitVec.ofNat 64 (2 * (base + k)))
  let b8  := s0.mem (s0.regs .rdi + BitVec.ofNat 64 (base + k))
  let acc' : BitVec 32 := rustDotU8U16From s0.mem (s0.regs .rdi) (s0.regs .rsi) (base + k) 0#32 +
    (w16.zeroExtend 32 * b8.zeroExtend 32)
  have haccEq : acc' = rustDotU8U16From s0.mem (s0.regs .rdi) (s0.regs .rsi) (base + (k + 1)) 0#32 := by
    have hidx : base + (k + 1) = (base + k) + 1 := by omega
    rw [hidx, rustDotU8U16From_split, rustDotU8U16From_succ, rustDotU8U16From_zero]
    unfold dotStepU8U16; dsimp only [acc', w16, b8]; rw [BitVec.mul_comm]
  dsimp only
  rw [show (7 : Nat) = 6 + 1 by rfl, runFrom_add]
  rcases runFrom_of_decodeSeqAt hdec idx nd s hrun hnf hrip with ⟨hseq, hrun1, hnf1⟩
  rw [hseq]
  have hw16 : readMem16 s.mem (s0.regs .rsi + BitVec.ofNat 64 (2 * (base + k))) = w16 := by rw [hmem]
  have hb8  : s.mem (s0.regs .rdi + BitVec.ofNat 64 (base + k)) = b8 := by rw [hmem]
  let stepSeq : List (X64Instr × BitVec 64) := [
    (.movzx16 .s32 .r8 (.mem { base := some .rsi, index := some (.rcx, 1), disp := BitVec.ofNat 64 (2 * k) }), n1),
    (.movzx8 .s32 .r9 (.mem8 { base := some .rdi, index := some (.rcx, 0), disp := BitVec.ofNat 64 k }), n2),
    (.imul2 .s32 .r8 (.reg .r9), n3),
    (.aluRmReg .s32 .add (.reg .rax) .r8, n4),
    (.lea .s64 .r8 { base := some .rcx, disp := BitVec.ofNat 64 (k + 1) }, n5),
    (.aluRmReg .s64 .cmp (.reg .r8) .rdx, nextRip)
  ]
  have he : execInstrSeq 6 stepSeq idx nd s =
      { s with
        rip := nextRip,
        regs := regUpd (regUpd (regUpd (regUpd (regUpd s.regs .r8 (w16.zeroExtend 64))
          .r9 (b8.zeroExtend 64)) .r8 ((w16.zeroExtend 32 * b8.zeroExtend 32).zeroExtend 64))
          .rax (acc'.zeroExtend 64)) .r8 (BitVec.ofNat 64 (base + (k + 1))),
        flags := (evalAluN (by decide) .cmp (BitVec.ofNat 64 (base + (k + 1))) (s0.regs .rdx)
                   (evalAluN (by decide) .add (rustDotU8U16From s0.mem (s0.regs .rdi) (s0.regs .rsi) (base + k) 0#32)
                     (w16.zeroExtend 32 * b8.zeroExtend 32)
                     (evalImulSz .s32 ((w16.zeroExtend 32).zeroExtend 64) ((b8.zeroExtend 32).zeroExtend 64) (nd (idx + 2)).flags).2
                     (nd (idx + 3)).flags).2
                   (nd (idx + 5)).flags).2 } := by
    rw [execInstrSeq_succ_cons, exec_movzx16_s32_mem, evalByteAddr_base_idx1_disp, hrsi, hrcx, hshl, haddrB, hw16]
    rw [execInstrSeq_succ_cons, exec_movzx8_s32_mem, evalByteAddr_base_idx0_disp]
    dsimp only; rw [regUpd_ne _ (by decide), regUpd_ne _ (by decide), hrdi, hrcx, haddrA, hb8]
    rw [execInstrSeq_succ_cons, exec_imul2_s32_reg]
    dsimp only; rw [regUpd_ne _ (by decide), regUpd_eq, regUpd_eq, zext16_32_64, zext8_32_64]
    rw [execInstrSeq_succ_cons, exec_aluRmReg_s32_add]
    dsimp only; rw [regUpd_ne _ (by decide), regUpd_ne _ (by decide), regUpd_ne _ (by decide), regUpd_eq, hrax, zext32_extract32_eq]
    rw [execInstrSeq_succ_cons, exec_lea_s64, evalByteAddr_base_disp]
    dsimp only; rw [regUpd_ne _ (by decide), regUpd_ne _ (by decide), regUpd_ne _ (by decide), regUpd_ne _ (by decide), hrcx, haddK1]
    rw [execInstrSeq_succ_cons, exec_aluRmReg_s64_cmp, execInstrSeq_zero]
    dsimp only; rw [regUpd_eq, regUpd_ne _ (by decide), regUpd_ne _ (by decide), regUpd_ne _ (by decide), regUpd_ne _ (by decide), regUpd_ne _ (by decide), hrdx]
  rw [he] at hrun1 hnf1 ⊢
  rw [runFrom_succ, step_at_concrete hjae _ _ hrun1 hnf1 rfl, runFrom_zero]
  have htn1 : (BitVec.ofNat 64 (base + (k + 1))).toNat = base + (k + 1) := by
    rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)]
  have hcs' : SysVCalleeSavedPreserved s0
      { s with
        regs := regUpd (regUpd (regUpd (regUpd (regUpd s.regs .r8 (w16.zeroExtend 64))
          .r9 (b8.zeroExtend 64)) .r8 ((w16.zeroExtend 32 * b8.zeroExtend 32).zeroExtend 64))
          .rax (acc'.zeroExtend 64)) .r8 (BitVec.ofNat 64 (base + (k + 1))) } := by
    unfold SysVCalleeSavedPreserved at hcs ⊢; dsimp only
    exact cs_step_caller (r := .r8) rfl (cs_step_caller (r := .rax) rfl
      (cs_step_caller (r := .r8) rfl (cs_step_caller (r := .r9) rfl (cs_step_caller (r := .r8) rfl hcs))))
  by_cases hcont : base + (k + 1) < (s0.regs .rdx).toNat
  · rw [exec_jcc_fall (by dsimp only; rw [evalCond_ae_of_flags, cmp_flags_cf, htn1]; simp [hcont])]
    simp only [hcont, ite_true]
    refine ⟨hrun, hnf, trivial, hmem, ?_, ?_, ?_, ?_, ?_, hcs', hymm⟩
    · repeat rw [regUpd_ne _ (by decide)]; exact hrdi
    · repeat rw [regUpd_ne _ (by decide)]; exact hrsi
    · repeat rw [regUpd_ne _ (by decide)]; exact hrdx
    · repeat rw [regUpd_ne _ (by decide)]; exact hrcx
    · rw [regUpd_ne _ (by decide), regUpd_eq, zext32_extract32_eq, haccEq]
  · rw [exec_jcc_taken (by dsimp only; rw [evalCond_ae_of_flags, cmp_flags_cf, htn1]; simp [hcont]), htgt]
    simp only [hcont, ite_false]
    refine ⟨hrun, hnf, trivial, hmem, ?_, ?_, ?_, ?_, ?_, hcs', hymm⟩
    · repeat rw [regUpd_ne _ (by decide)]; exact hrdi
    · repeat rw [regUpd_ne _ (by decide)]; exact hrsi
    · repeat rw [regUpd_ne _ (by decide)]; exact hrdx
    · repeat rw [regUpd_ne _ (by decide)]; exact hrcx
    · rw [regUpd_ne _ (by decide), regUpd_eq, zext32_extract32_eq, haccEq]

private theorem dotO3_unrolled_0x365 (s0 s : X64State) (base idx : Nat) (nd : Nat → UndefChoice)
    (hpre : DotU8U16Pre 0 s0)
    (hrun : s.halted = false) (hnf : s.fault = false) (hrip : s.rip = 0x400365#64) (hmem : s.mem = s0.mem)
    (hrdi : s.regs .rdi = s0.regs .rdi) (hrsi : s.regs .rsi = s0.regs .rsi)
    (hrdx : s.regs .rdx = s0.regs .rdx) (hrcx : s.regs .rcx = BitVec.ofNat 64 base)
    (hrax : BitVec.extractLsb' 0 32 (s.regs .rax) =
      rustDotU8U16From s0.mem (s0.regs .rdi) (s0.regs .rsi) base 0#32)
    (hcs : SysVCalleeSavedPreserved s0 s) (hymm : UpperYmmCleanOrPreserved s0 s)
    (hremLo : base < (s0.regs .rdx).toNat) (hremHi : (s0.regs .rdx).toNat ≤ base + 7) :
    ∃ steps : Nat,
      let sf := runFrom dotO3Cmap steps idx nd s
      sf.halted = true ∧ sf.fault = false ∧
      SysVCalleeSavedPreserved s0 sf ∧ UpperYmmCleanOrPreserved s0 sf ∧
      DotU8U16Post 0 s0 sf := by
  have h2len := hpre.1; have hlenLt := (s0.regs .rdx).isLt
  have hshl : BitVec.ofNat 64 base <<< 1 = BitVec.ofNat 64 (2 * base) := by
    have htn : (BitVec.ofNat 64 base).toNat = base := by rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)]
    rw [bv64_shl1_toNat (by rw [htn]; omega), htn]
  -- Element 0 (0x400365..0x40037d + jae 0x400426)
  rcases runFrom_of_decodeSeqAt dotO3_t0_dec idx nd s hrun hnf hrip with ⟨ht0, hrun0, hnf0⟩
  let b0 := s0.mem (s0.regs .rdi + BitVec.ofNat 64 base)
  let w0 := readMem16 s0.mem (s0.regs .rsi + BitVec.ofNat 64 (2 * base))
  let acc0 : BitVec 32 := rustDotU8U16From s0.mem (s0.regs .rdi) (s0.regs .rsi) base 0#32 +
    (b0.zeroExtend 32 * w0.zeroExtend 32)
  have hacc0 : acc0 = rustDotU8U16From s0.mem (s0.regs .rdi) (s0.regs .rsi) (base + 1) 0#32 := by
    rw [rustDotU8U16From_split, rustDotU8U16From_succ, rustDotU8U16From_zero]; rfl
  have hb0m : s.mem (s0.regs .rdi + BitVec.ofNat 64 base) = b0 := by rw [hmem]
  have hw0m : readMem16 s.mem (s0.regs .rsi + BitVec.ofNat 64 (2 * base)) = w0 := by rw [hmem]
  have hadd1 : BitVec.ofNat 64 base + 1#64 = BitVec.ofNat 64 (base + 1) := by
    change BitVec.ofNat 64 base + BitVec.ofNat 64 1 = _; exact bv64_ofNat_add _ _
  have he0 : execInstrSeq 6 dotO3_t0Seq idx nd s =
      { s with
        rip := 0x40037d#64,
        regs := regUpd (regUpd (regUpd (regUpd (regUpd s.regs .r8 (b0.zeroExtend 64))
          .r9 (w0.zeroExtend 64)) .r8 ((b0.zeroExtend 32 * w0.zeroExtend 32).zeroExtend 64))
          .rax (acc0.zeroExtend 64)) .r8 (BitVec.ofNat 64 (base + 1)),
        flags := (evalAluN (by decide) .cmp (BitVec.ofNat 64 (base + 1)) (s0.regs .rdx)
                   (evalAluN (by decide) .add (rustDotU8U16From s0.mem (s0.regs .rdi) (s0.regs .rsi) base 0#32)
                     (b0.zeroExtend 32 * w0.zeroExtend 32)
                     (evalImulSz .s32 ((b0.zeroExtend 32).zeroExtend 64) ((w0.zeroExtend 32).zeroExtend 64) (nd (idx + 2)).flags).2
                     (nd (idx + 3)).flags).2
                   (nd (idx + 5)).flags).2 } := by
    dsimp only [dotO3_t0Seq]
    rw [execInstrSeq_succ_cons, exec_movzx8_s32_mem, evalByteAddr_base_idx0, hrdi, hrcx, hb0m]
    rw [execInstrSeq_succ_cons, exec_movzx16_s32_mem, evalByteAddr_base_idx1]
    dsimp only; rw [regUpd_ne _ (by decide), regUpd_ne _ (by decide), hrsi, hrcx, hshl, hw0m]
    rw [execInstrSeq_succ_cons, exec_imul2_s32_reg]
    dsimp only; rw [regUpd_ne _ (by decide), regUpd_eq, regUpd_eq, zext8_32_64, zext16_32_64]
    rw [execInstrSeq_succ_cons, exec_aluRmReg_s32_add]
    dsimp only; rw [regUpd_ne _ (by decide), regUpd_ne _ (by decide), regUpd_ne _ (by decide), regUpd_eq, hrax, zext32_extract32_eq]
    rw [execInstrSeq_succ_cons, exec_lea_s64, evalByteAddr_base_disp]
    dsimp only; rw [regUpd_ne _ (by decide), regUpd_ne _ (by decide), regUpd_ne _ (by decide), regUpd_ne _ (by decide), hrcx, hadd1]
    rw [execInstrSeq_succ_cons, exec_aluRmReg_s64_cmp, execInstrSeq_zero]
    dsimp only; rw [regUpd_eq, regUpd_ne _ (by decide), regUpd_ne _ (by decide), regUpd_ne _ (by decide), regUpd_ne _ (by decide), regUpd_ne _ (by decide), hrdx]
  have htn1 : (BitVec.ofNat 64 (base + 1)).toNat = base + 1 := by rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)]
  have hcs1 : SysVCalleeSavedPreserved s0 (execInstrSeq 6 dotO3_t0Seq idx nd s) := by
    unfold SysVCalleeSavedPreserved at hcs ⊢; rw [he0]; dsimp only
    exact cs_step_caller (r := .r8) rfl (cs_step_caller (r := .rax) rfl
      (cs_step_caller (r := .r8) rfl (cs_step_caller (r := .r9) rfl (cs_step_caller (r := .r8) rfl hcs))))
  by_cases hc1 : base + 1 < (s0.regs .rdx).toNat
  · have hcc1 : evalCond .ae (execInstrSeq 6 dotO3_t0Seq idx nd s).flags = false := by
      rw [he0]; dsimp only; rw [evalCond_ae_of_flags, cmp_flags_cf, htn1]; simp [hc1]
    let s1 := runFrom dotO3Cmap 7 idx nd s
    have hs1Eq : s1 = { execInstrSeq 6 dotO3_t0Seq idx nd s with rip := 0x400383#64 } := by
      dsimp only [s1]; rw [show (7 : Nat) = 6 + 1 by rfl, runFrom_add, ht0, runFrom_succ,
        step_at_concrete dotO3_t0_jae _ _ hrun0 hnf0 (by rw [he0]), exec_jcc_fall hcc1, runFrom_zero]; rw [he0]; rfl
    have h1 := dotO3_tail_step (k := 1) dotO3_t1_dec dotO3_t1_jae rfl s0 s1 base (idx + 7) nd hpre
      (by rw [hs1Eq]; exact hrun0) (by rw [hs1Eq]; exact hnf0) (by rw [hs1Eq]) (by rw [hs1Eq, he0]; exact hmem)
      (by rw [hs1Eq, he0]; dsimp only; repeat rw [regUpd_ne _ (by decide)]; exact hrdi)
      (by rw [hs1Eq, he0]; dsimp only; repeat rw [regUpd_ne _ (by decide)]; exact hrsi)
      (by rw [hs1Eq, he0]; dsimp only; repeat rw [regUpd_ne _ (by decide)]; exact hrdx)
      (by rw [hs1Eq, he0]; dsimp only; repeat rw [regUpd_ne _ (by decide)]; exact hrcx)
      (by rw [hs1Eq, he0]; dsimp only; rw [regUpd_ne _ (by decide), regUpd_eq, zext32_extract32_eq, hacc0])
      (by rw [hs1Eq]; exact hcs1) (by rw [hs1Eq, he0]; exact hymm) hc1
    generalize hs2 : runFrom dotO3Cmap 7 (idx + 7) nd s1 = s2 at h1
    rcases h1 with ⟨h2r, h2f, h2rip, h2m, h2di, h2si, h2dx, h2cx, h2ax, h2cs, h2ym⟩
    by_cases hc2 : base + 2 < (s0.regs .rdx).toNat
    · simp only [hc2, ite_true] at h2rip
      have h2 := dotO3_tail_step (k := 2) dotO3_t2_dec dotO3_t2_jae rfl s0 s2 base (idx + 14) nd hpre
        h2r h2f h2rip h2m h2di h2si h2dx h2cx h2ax h2cs h2ym hc2
      generalize hs3 : runFrom dotO3Cmap 7 (idx + 14) nd s2 = s3 at h2
      rcases h2 with ⟨h3r, h3f, h3rip, h3m, h3di, h3si, h3dx, h3cx, h3ax, h3cs, h3ym⟩
      by_cases hc3 : base + 3 < (s0.regs .rdx).toNat
      · simp only [hc3, ite_true] at h3rip
        have h3 := dotO3_tail_step (k := 3) dotO3_t3_dec dotO3_t3_jae rfl s0 s3 base (idx + 21) nd hpre
          h3r h3f h3rip h3m h3di h3si h3dx h3cx h3ax h3cs h3ym hc3
        generalize hs4 : runFrom dotO3Cmap 7 (idx + 21) nd s3 = s4 at h3
        rcases h3 with ⟨h4r, h4f, h4rip, h4m, h4di, h4si, h4dx, h4cx, h4ax, h4cs, h4ym⟩
        by_cases hc4 : base + 4 < (s0.regs .rdx).toNat
        · simp only [hc4, ite_true] at h4rip
          have h4 := dotO3_tail_step (k := 4) dotO3_t4_dec dotO3_t4_jae rfl s0 s4 base (idx + 28) nd hpre
            h4r h4f h4rip h4m h4di h4si h4dx h4cx h4ax h4cs h4ym hc4
          generalize hs5 : runFrom dotO3Cmap 7 (idx + 28) nd s4 = s5 at h4
          rcases h4 with ⟨h5r, h5f, h5rip, h5m, h5di, h5si, h5dx, h5cx, h5ax, h5cs, h5ym⟩
          by_cases hc5 : base + 5 < (s0.regs .rdx).toNat
          · simp only [hc5, ite_true] at h5rip
            have h5 := dotO3_tail_step (k := 5) dotO3_t5_dec dotO3_t5_jae rfl s0 s5 base (idx + 35) nd hpre
              h5r h5f h5rip h5m h5di h5si h5dx h5cx h5ax h5cs h5ym hc5
            generalize hs6 : runFrom dotO3Cmap 7 (idx + 35) nd s5 = s6 at h5
            rcases h5 with ⟨h6r, h6f, h6rip, h6m, h6di, h6si, h6dx, h6cx, h6ax, h6cs, h6ym⟩
            by_cases hc6 : base + 6 < (s0.regs .rdx).toNat
            · simp only [hc6, ite_true] at h6rip
              rcases runFrom_of_decodeSeqAt dotO3_t6_dec (idx + 42) nd s6 h6r h6f h6rip with ⟨ht6, h7r, h7f⟩
              have haddrB6 : (s0.regs .rsi + BitVec.ofNat 64 (2 * base)) + 0x0c#64 =
                  s0.regs .rsi + BitVec.ofNat 64 (2 * (base + 6)) := by
                change (s0.regs .rsi + BitVec.ofNat 64 (2 * base)) + BitVec.ofNat 64 12 = _
                have h12 : 2 * base + 12 = 2 * (base + 6) := by omega
                rw [bv64_add_ofNat_assoc, h12]
              have haddrA6 : (s0.regs .rdi + BitVec.ofNat 64 base) + 6#64 =
                  s0.regs .rdi + BitVec.ofNat 64 (base + 6) := bv64_add_ofNat_assoc _ _ _
              let w6 := readMem16 s0.mem (s0.regs .rsi + BitVec.ofNat 64 (2 * (base + 6)))
              let b6 := s0.mem (s0.regs .rdi + BitVec.ofNat 64 (base + 6))
              let acc6 : BitVec 32 := rustDotU8U16From s0.mem (s0.regs .rdi) (s0.regs .rsi) (base + 6) 0#32 +
                (w6.zeroExtend 32 * b6.zeroExtend 32)
              have hacc6 : acc6 = rustDotU8U16 s0.mem (s0.regs .rdi) (s0.regs .rsi) (s0.regs .rdx).toNat := by
                have hlen7 : (s0.regs .rdx).toNat = (base + 6) + 1 := by omega
                rw [hlen7]; unfold rustDotU8U16
                rw [rustDotU8U16From_split, rustDotU8U16From_succ, rustDotU8U16From_zero]
                unfold dotStepU8U16; dsimp only [acc6, w6, b6]; rw [BitVec.mul_comm]
              have hw6m : readMem16 s6.mem (s0.regs .rsi + BitVec.ofNat 64 (2 * (base + 6))) = w6 := by rw [h6m]
              have hb6m : s6.mem (s0.regs .rdi + BitVec.ofNat 64 (base + 6)) = b6 := by rw [h6m]
              have he6 : execInstrSeq 4 dotO3_t6Seq (idx + 42) nd s6 =
                  { s6 with
                    rip := 0x400422#64,
                    regs := regUpd (regUpd (regUpd (regUpd s6.regs .rdx (w6.zeroExtend 64))
                      .rcx (b6.zeroExtend 64)) .rdx ((w6.zeroExtend 32 * b6.zeroExtend 32).zeroExtend 64))
                      .rax (acc6.zeroExtend 64),
                    flags := (evalAluN (by decide) .add (rustDotU8U16From s0.mem (s0.regs .rdi) (s0.regs .rsi) (base + 6) 0#32)
                               (w6.zeroExtend 32 * b6.zeroExtend 32)
                               (evalImulSz .s32 ((w6.zeroExtend 32).zeroExtend 64) ((b6.zeroExtend 32).zeroExtend 64) (nd (idx + 44)).flags).2
                               (nd (idx + 45)).flags).2 } := by
                dsimp only [dotO3_t6Seq]
                rw [execInstrSeq_succ_cons, exec_movzx16_s32_mem, evalByteAddr_base_idx1_disp, h6si, h6cx, hshl, haddrB6, hw6m]
                rw [execInstrSeq_succ_cons, exec_movzx8_s32_mem, evalByteAddr_base_idx0_disp]
                dsimp only; rw [regUpd_ne _ (by decide), regUpd_ne _ (by decide), h6di, h6cx, haddrA6, hb6m]
                rw [execInstrSeq_succ_cons, exec_imul2_s32_reg]
                dsimp only; rw [regUpd_ne _ (by decide), regUpd_eq, regUpd_eq, zext16_32_64, zext8_32_64]
                rw [execInstrSeq_succ_cons, exec_aluRmReg_s32_add, execInstrSeq_zero]
                dsimp only; rw [regUpd_ne _ (by decide), regUpd_ne _ (by decide), regUpd_ne _ (by decide), regUpd_eq, h6ax, zext32_extract32_eq]
              have hRet := dotO3_ret_at s0 (runFrom dotO3Cmap 4 (idx + 42) nd s6) 0x400422#64 (idx + 46) nd dotO3_ret422
                (by rw [ht6]; exact h7r) (by rw [ht6]; exact h7f) (by rw [ht6, he6]) (by rw [ht6, he6]; exact h6m)
                (by rw [ht6, he6]; dsimp only; rw [regUpd_eq, zext32_extract32_eq, hacc6])
                (by unfold SysVCalleeSavedPreserved at h6cs ⊢; rw [ht6, he6]; dsimp only
                    exact cs_step_caller (r := .rax) rfl (cs_step_caller (r := .rdx) rfl (cs_step_caller (r := .rcx) rfl (cs_step_caller (r := .rdx) rfl h6cs))))
                (by rw [ht6, he6]; exact h6ym)
              refine ⟨47, ?_⟩
              rw [show (47 : Nat) = 7 + (7 + (7 + (7 + (7 + (7 + (4 + 1)))))) by rfl,
                  runFrom_add, runFrom_add, hs2, runFrom_add, hs3, runFrom_add, hs4, runFrom_add, hs5, runFrom_add, hs6, runFrom_add]
              exact hRet
            · simp only [hc6, ite_false] at h6rip
              have hlen6 : base + 6 = (s0.regs .rdx).toNat := by omega
              rw [hlen6] at h6ax
              have hRet := dotO3_ret_at s0 s6 0x400426#64 (idx + 42) nd dotO3_ret426 h6r h6f h6rip h6m h6ax h6cs h6ym
              refine ⟨43, ?_⟩
              rw [show (43 : Nat) = 7 + (7 + (7 + (7 + (7 + (7 + 1))))) by rfl,
                  runFrom_add, runFrom_add, hs2, runFrom_add, hs3, runFrom_add, hs4, runFrom_add, hs5, runFrom_add, hs6]
              exact hRet
          · simp only [hc5, ite_false] at h5rip
            have hlen5 : base + 5 = (s0.regs .rdx).toNat := by omega
            rw [hlen5] at h5ax
            have hRet := dotO3_ret_at s0 s5 0x400426#64 (idx + 35) nd dotO3_ret426 h5r h5f h5rip h5m h5ax h5cs h5ym
            refine ⟨36, ?_⟩
            rw [show (36 : Nat) = 7 + (7 + (7 + (7 + (7 + 1)))) by rfl,
                runFrom_add, runFrom_add, hs2, runFrom_add, hs3, runFrom_add, hs4, runFrom_add, hs5]
            exact hRet
        · simp only [hc4, ite_false] at h4rip
          have hlen4 : base + 4 = (s0.regs .rdx).toNat := by omega
          rw [hlen4] at h4ax
          have hRet := dotO3_ret_at s0 s4 0x400426#64 (idx + 28) nd dotO3_ret426 h4r h4f h4rip h4m h4ax h4cs h4ym
          refine ⟨29, ?_⟩
          rw [show (29 : Nat) = 7 + (7 + (7 + (7 + 1))) by rfl,
              runFrom_add, runFrom_add, hs2, runFrom_add, hs3, runFrom_add, hs4]
          exact hRet
      · simp only [hc3, ite_false] at h3rip
        have hlen3 : base + 3 = (s0.regs .rdx).toNat := by omega
        rw [hlen3] at h3ax
        have hRet := dotO3_ret_at s0 s3 0x400426#64 (idx + 21) nd dotO3_ret426 h3r h3f h3rip h3m h3ax h3cs h3ym
        refine ⟨22, ?_⟩
        rw [show (22 : Nat) = 7 + (7 + (7 + 1)) by rfl,
            runFrom_add, runFrom_add, hs2, runFrom_add, hs3]
        exact hRet
    · simp only [hc2, ite_false] at h2rip
      have hlen2 : base + 2 = (s0.regs .rdx).toNat := by omega
      rw [hlen2] at h2ax
      have hRet := dotO3_ret_at s0 s2 0x400426#64 (idx + 14) nd dotO3_ret426 h2r h2f h2rip h2m h2ax h2cs h2ym
      refine ⟨15, ?_⟩
      rw [show (15 : Nat) = 7 + (7 + 1) by rfl, runFrom_add, runFrom_add, hs2]
      exact hRet
  · have hcc1 : evalCond .ae (execInstrSeq 6 dotO3_t0Seq idx nd s).flags = true := by
      rw [he0]; dsimp only; rw [evalCond_ae_of_flags, cmp_flags_cf, htn1]; simp [hc1]
    have hlen1 : base + 1 = (s0.regs .rdx).toNat := by omega
    let s1 := runFrom dotO3Cmap 7 idx nd s
    have hs1Eq : s1 = { execInstrSeq 6 dotO3_t0Seq idx nd s with rip := 0x400426#64 } := by
      dsimp only [s1]; rw [show (7 : Nat) = 6 + 1 by rfl, runFrom_add, ht0, runFrom_succ,
        step_at_concrete dotO3_t0_jae _ _ hrun0 hnf0 (by rw [he0]), exec_jcc_taken hcc1, runFrom_zero]; rw [he0]; rfl
    have hRet := dotO3_ret_at s0 s1 0x400426#64 (idx + 7) nd dotO3_ret426
      (by rw [hs1Eq]; exact hrun0) (by rw [hs1Eq]; exact hnf0) (by rw [hs1Eq]) (by rw [hs1Eq, he0]; exact hmem)
      (by rw [hs1Eq, he0]; dsimp only; rw [regUpd_ne _ (by decide), regUpd_eq, zext32_extract32_eq, hacc0, hlen1]; rfl)
      (by rw [hs1Eq]; exact hcs1) (by rw [hs1Eq, he0]; exact hymm)
    refine ⟨8, ?_⟩
    rw [show (8 : Nat) = 7 + 1 by rfl, runFrom_add]
    exact hRet

/-! ## Section 3: `8`-Elem `vpmulld` + `vpsrlq 0x20` Epilogue (`0x2af..0x365`) -/

private theorem zext64_lo_word (q : BitVec 64) (k : Fin 4) :
    BitVec.extractLsb' (k.val * 16) 16 (BitVec.extractLsb' 0 64 (q.zeroExtend 128)) =
      BitVec.extractLsb' (k.val * 16) 16 q := by
  rw [extract_lo64_zext128]

private theorem dot8_vpmulld_algebra (m : ByteMem) (pa pb : BitVec 64) (accV : BitVec 128) :
    let aQ := readMem64 m pa
    let bLoQ := readMem64 m pb
    let bHiQ := readMem64 m (pb + 8#64)
    let x0_0 := aQ.zeroExtend 128
    let x2_0 := packWords128 fun i => (BitVec.extractLsb' (i.val * 8) 8 (BitVec.extractLsb' 0 64 x0_0)).zeroExtend 16
    let x0_1 := psrlqImm128 x0_0 0x20#8
    let x1_0 := packDwords128 fun i => (BitVec.extractLsb' (i.val * 16) 16 (BitVec.extractLsb' 0 64 x2_0)).zeroExtend 32
    let x6_0 := packDwords128 fun i => (BitVec.extractLsb' (i.val * 16) 16 (BitVec.extractLsb' 0 64 (bLoQ.zeroExtend 128))).zeroExtend 32
    let x0_2 := packWords128 fun i => (BitVec.extractLsb' (i.val * 8) 8 (BitVec.extractLsb' 0 64 x0_1)).zeroExtend 16
    let x2_1 := psrlqImm128 x2_0 0x20#8
    let x4_1 := psrlqImm128 (bLoQ.zeroExtend 128) 0x20#8
    let x4_2 := packDwords128 fun i => (BitVec.extractLsb' (i.val * 16) 16 (BitVec.extractLsb' 0 64 x4_1)).zeroExtend 32
    let p01  := pmulld128 x1_0 x6_0
    let x2_2 := packDwords128 fun i => (BitVec.extractLsb' (i.val * 16) 16 (BitVec.extractLsb' 0 64 x2_1)).zeroExtend 32
    let p23  := pmulld128 x2_2 x4_2
    let x4_3 := packDwords128 fun i => (BitVec.extractLsb' (i.val * 16) 16 (BitVec.extractLsb' 0 64 (bHiQ.zeroExtend 128))).zeroExtend 32
    let x3_1 := psrlqImm128 (bHiQ.zeroExtend 128) 0x20#8
    let x3_2 := packDwords128 fun i => (BitVec.extractLsb' (i.val * 16) 16 (BitVec.extractLsb' 0 64 x3_1)).zeroExtend 32
    let s03  := packDwords128 fun i => getDword128 p01 i + getDword128 p23 i
    let x2_3 := packDwords128 fun i => (BitVec.extractLsb' (i.val * 16) 16 (BitVec.extractLsb' 0 64 x0_2)).zeroExtend 32
    let x0_3 := psrlqImm128 x0_2 0x20#8
    let p45  := pmulld128 x2_3 x4_3
    let x0_4 := packDwords128 fun i => (BitVec.extractLsb' (i.val * 16) 16 (BitVec.extractLsb' 0 64 x0_3)).zeroExtend 32
    let p67  := pmulld128 x0_4 x3_2
    let s03a := packDwords128 fun i => getDword128 s03 i + getDword128 accV i
    let s47  := packDwords128 fun i => getDword128 p45 i + getDword128 p67 i
    let sAll := packDwords128 fun i => getDword128 s03a i + getDword128 s47 i
    sumLo2Dwords128 sAll = rustDotU8U16From m pa pb 8 (sumLo2Dwords128 accV) := by
  dsimp only
  rw [sumLo2Dwords128_paddd, sumLo2Dwords128_paddd, sumLo2Dwords128_paddd, sumLo2Dwords128_paddd]
  have hp : ∀ (u v : BitVec 128),
      sumLo2Dwords128 (pmulld128 u v) =
        getDword128 u ⟨0, by decide⟩ * getDword128 v ⟨0, by decide⟩ +
        getDword128 u ⟨1, by decide⟩ * getDword128 v ⟨1, by decide⟩ := by
    intro u v; unfold sumLo2Dwords128; rw [getDword128_pmulld, getDword128_pmulld]
  rw [hp, hp, hp, hp]
  repeat rw [getDword128_packDwords128]
  dsimp only
  repeat rw [psrlq32_lo64_eq]
  repeat rw [extract_lo64_zext128]
  have h1a : ∀ k : Fin 2, BitVec.extractLsb' (k.val * 16) 16 (BitVec.extractLsb' 0 64 (packWords128 fun i =>
      (BitVec.extractLsb' (i.val * 8) 8 (readMem64 m pa)).zeroExtend 16)) =
      (m (pa + BitVec.ofNat 64 k.val)).zeroExtend 16 := by
    intro k; rw [extract_lo64_packWords128_word _ ⟨k.val, by omega⟩]
    dsimp only; change (byteOf64 (readMem64 m pa) k.val).zeroExtend 16 = _
    rw [readMem64_byte_at _ _ k.val (by omega)]
  have h2a : ∀ k : Fin 2, BitVec.extractLsb' (k.val * 16) 16 ((BitVec.extractLsb' 0 64 (packWords128 fun i =>
      (BitVec.extractLsb' (i.val * 8) 8 (readMem64 m pa)).zeroExtend 16)) >>> 32) =
      (m (pa + BitVec.ofNat 64 (2 + k.val))).zeroExtend 16 := by
    intro k; rw [extract_lo64_shr32_word _ k, extract_lo64_packWords128_word _ ⟨2 + k.val, by omega⟩]
    dsimp only; change (byteOf64 (readMem64 m pa) (2 + k.val)).zeroExtend 16 = _
    rw [readMem64_byte_at _ _ (2 + k.val) (by omega)]
  have h3a : ∀ k : Fin 2, BitVec.extractLsb' (k.val * 16) 16 (BitVec.extractLsb' 0 64 (packWords128 fun i =>
      (BitVec.extractLsb' (i.val * 8) 8 (readMem64 m pa >>> 32)).zeroExtend 16)) =
      (m (pa + BitVec.ofNat 64 (4 + k.val))).zeroExtend 16 := by
    intro k; rw [extract_lo64_packWords128_word _ ⟨k.val, by omega⟩]
    dsimp only; rw [extract_lo64_shr32_byte _ ⟨k.val, by omega⟩, readMem64_byte_at _ _ (4 + k.val) (by omega)]
  have h4a : ∀ k : Fin 2, BitVec.extractLsb' (k.val * 16) 16 ((BitVec.extractLsb' 0 64 (packWords128 fun i =>
      (BitVec.extractLsb' (i.val * 8) 8 (readMem64 m pa >>> 32)).zeroExtend 16)) >>> 32) =
      (m (pa + BitVec.ofNat 64 (6 + k.val))).zeroExtend 16 := by
    intro k; rw [extract_lo64_shr32_word _ k, extract_lo64_packWords128_word _ ⟨2 + k.val, by omega⟩]
    dsimp only; rw [extract_lo64_shr32_byte _ ⟨2 + k.val, by omega⟩, readMem64_byte_at _ _ (4 + (2 + k.val)) (by omega)]
    have h6 : 4 + (2 + k.val) = 6 + k.val := by omega
    rw [h6]
  have h1b : ∀ k : Fin 2, BitVec.extractLsb' (k.val * 16) 16 (readMem64 m pb) =
      readMem16 m (pb + BitVec.ofNat 64 (2 * k.val)) := fun k => readMem64_word_at m pb ⟨k.val, by omega⟩
  have h2b : ∀ k : Fin 2, BitVec.extractLsb' (k.val * 16) 16 (readMem64 m pb >>> 32) =
      readMem16 m (pb + BitVec.ofNat 64 (2 * (2 + k.val))) := by
    intro k; rw [extract_lo64_shr32_word _ k, readMem64_word_at m pb ⟨2 + k.val, by omega⟩]
  have h3b : ∀ k : Fin 2, BitVec.extractLsb' (k.val * 16) 16 (readMem64 m (pb + 8#64)) =
      readMem16 m (pb + BitVec.ofNat 64 (8 + 2 * k.val)) := by
    intro k; rw [readMem64_word_at m (pb + 8#64) ⟨k.val, by omega⟩]; dsimp only
    change readMem16 m ((pb + BitVec.ofNat 64 8) + BitVec.ofNat 64 (2 * k.val)) = _
    rw [bv64_add_ofNat_assoc]
  have h4b : ∀ k : Fin 2, BitVec.extractLsb' (k.val * 16) 16 (readMem64 m (pb + 8#64) >>> 32) =
      readMem16 m (pb + BitVec.ofNat 64 (8 + 2 * (2 + k.val))) := by
    intro k; rw [extract_lo64_shr32_word _ k, readMem64_word_at m (pb + 8#64) ⟨2 + k.val, by omega⟩]; dsimp only
    change readMem16 m ((pb + BitVec.ofNat 64 8) + BitVec.ofNat 64 (2 * (2 + k.val))) = _
    rw [bv64_add_ofNat_assoc]
  rw [h1a ⟨0, by decide⟩, h1a ⟨1, by decide⟩, h2a ⟨0, by decide⟩, h2a ⟨1, by decide⟩,
      h3a ⟨0, by decide⟩, h3a ⟨1, by decide⟩, h4a ⟨0, by decide⟩, h4a ⟨1, by decide⟩,
      h1b ⟨0, by decide⟩, h1b ⟨1, by decide⟩, h2b ⟨0, by decide⟩, h2b ⟨1, by decide⟩,
      h3b ⟨0, by decide⟩, h3b ⟨1, by decide⟩, h4b ⟨0, by decide⟩, h4b ⟨1, by decide⟩]
  repeat rw [zext8_16_32_eq]
  rw [rustDotU8U16From_8]
  dsimp only
  have ha := BitVec.add_assoc (n := 32); have hc := BitVec.add_comm (n := 32)
  rw [hc (_ + _ + (_ + _)) (sumLo2Dwords128 accV)]
  simp only [ha]

private theorem dotO3_epi8_stepA (s : X64State) (aPtr bPtr : BitVec 64) (done0 r10Val idx : Nat)
    (nd : Nat → UndefChoice)
    (hshl : BitVec.ofNat 64 (done0 + r10Val) <<< 1 = BitVec.ofNat 64 (2 * (done0 + r10Val)))
    (hrun : s.halted = false) (hnf : s.fault = false) (hrip : s.rip = 0x4002c0#64)
    (hrdi : s.regs .rdi = aPtr) (hrsi : s.regs .rsi = bPtr)
    (hr9 : s.regs .r9 = BitVec.ofNat 64 done0) (hr10 : s.regs .r10 = BitVec.ofNat 64 r10Val) :
    let base := done0 + r10Val
    let aQ := readMem64 s.mem (aPtr + BitVec.ofNat 64 base)
    let bLoQ := readMem64 s.mem (bPtr + BitVec.ofNat 64 (2 * base))
    let bHiQ := readMem64 s.mem ((bPtr + BitVec.ofNat 64 (2 * base)) + 8#64)
    let x0_0 := aQ.zeroExtend 128
    let x2_0 := packWords128 fun i => (BitVec.extractLsb' (i.val * 8) 8 (BitVec.extractLsb' 0 64 x0_0)).zeroExtend 16
    let sA := runFrom dotO3Cmap 8 idx nd s
    sA.halted = false ∧ sA.fault = false ∧ sA.rip = 0x4002e7#64 ∧ sA.mem = s.mem ∧
    sA.regs = regUpd (regUpd s.regs .rax (BitVec.ofNat 64 base)) .r9 (bPtr + BitVec.ofNat 64 (2 * base)) ∧
    BitVec.extractLsb' 0 128 (sA.ymms y0) = psrlqImm128 x0_0 0x20#8 ∧
    BitVec.extractLsb' 0 128 (sA.ymms y1) = (packDwords128 fun i => (BitVec.extractLsb' (i.val * 16) 16 (BitVec.extractLsb' 0 64 x2_0)).zeroExtend 32) ∧
    BitVec.extractLsb' 0 128 (sA.ymms y2) = x2_0 ∧
    BitVec.extractLsb' 0 128 (sA.ymms y3) = bHiQ.zeroExtend 128 ∧
    BitVec.extractLsb' 0 128 (sA.ymms y4) = bLoQ.zeroExtend 128 ∧
    BitVec.extractLsb' 0 128 (sA.ymms y5) = BitVec.extractLsb' 0 128 (s.ymms y5) ∧
    (AllUpperYmmClean s → AllUpperYmmClean sA) := by
  dsimp only
  let base := done0 + r10Val
  let aQ := readMem64 s.mem (aPtr + BitVec.ofNat 64 base)
  let bLoQ := readMem64 s.mem (bPtr + BitVec.ofNat 64 (2 * base))
  let bHiQ := readMem64 s.mem ((bPtr + BitVec.ofNat 64 (2 * base)) + 8#64)
  let x0_0 := aQ.zeroExtend 128
  let x2_0 := packWords128 fun i => (BitVec.extractLsb' (i.val * 8) 8 (BitVec.extractLsb' 0 64 x0_0)).zeroExtend 16
  let x0_1 := psrlqImm128 x0_0 0x20#8
  let x1_0 := packDwords128 fun i => (BitVec.extractLsb' (i.val * 16) 16 (BitVec.extractLsb' 0 64 x2_0)).zeroExtend 32
  let r1 := regUpd s.regs .rax (BitVec.ofNat 64 base)
  let r2 := regUpd r1 .r9 (bPtr + BitVec.ofNat 64 (2 * base))
  let y1s := writeXmm128 true s.ymms y0 x0_0
  let y2s := writeXmm128 true y1s y4 (bLoQ.zeroExtend 128)
  let y3s := writeXmm128 true y2s y3 (bHiQ.zeroExtend 128)
  let y4s := writeXmm128 true y3s y2 x2_0
  let y5s := writeXmm128 true y4s y0 x0_1
  let y6s := writeXmm128 true y5s y1 x1_0
  rcases runFrom_of_decodeSeqAt dotO3_epi8A_dec idx nd s hrun hnf hrip with ⟨hseq, _, _⟩
  have hlo64_wx : ∀ (ym : YmmIdx → BitVec 256) (r : YmmIdx) (v : BitVec 128),
      BitVec.extractLsb' 0 64 (writeXmm128 true ym r v r) = BitVec.extractLsb' 0 64 v := fun ym r v => by
    rw [writeXmm128_true_eq, ymmUpd_eq]; apply BitVec.eq_of_getLsbD_eq; intro b hb
    rw [BitVec.getLsbD_extractLsb', BitVec.getLsbD_extractLsb', BitVec.getLsbD_append]; simp [hb, show b < 128 by omega]
  have he : runFrom dotO3Cmap 8 idx nd s = { s with rip := 0x4002e7#64, regs := r2, ymms := y6s } := by
    rw [hseq]; dsimp only [dotO3_epi8ASeq]
    rw [execInstrSeq_succ_cons, exec_lea_s64, evalByteAddr_base_idx0, hr9, hr10, bv64_ofNat_add]
    change execInstrSeq 7 _ _ _ { s with rip := 0x4002c4#64, regs := r1 } = _
    rw [execInstrSeq_succ_cons, exec_simdMovqLoad_vex_mem, evalByteAddr_base_idx0]
    dsimp only [r1]; rw [regUpd_ne _ (by decide), regUpd_eq, hrdi]
    change execInstrSeq 6 _ _ _ { s with rip := 0x4002c9#64, regs := r1, ymms := y1s } = _
    rw [execInstrSeq_succ_cons, exec_lea_s64, evalByteAddr_base_idx1]
    dsimp only [r1]; rw [regUpd_ne _ (by decide), regUpd_eq, hrsi, hshl]
    change execInstrSeq 5 _ _ _ { s with rip := 0x4002cd#64, regs := r2, ymms := y1s } = _
    rw [execInstrSeq_succ_cons, exec_simdMovqLoad_vex_mem, evalByteAddr_base]
    dsimp only [r2]; rw [regUpd_eq]
    change execInstrSeq 4 _ _ _ { s with rip := 0x4002d2#64, regs := r2, ymms := y2s } = _
    rw [execInstrSeq_succ_cons, exec_simdMovqLoad_vex_mem, evalByteAddr_base_disp]
    dsimp only [r2]; rw [regUpd_eq]
    change execInstrSeq 3 _ _ _ { s with rip := 0x4002d8#64, regs := r2, ymms := y3s } = _
    rw [execInstrSeq_succ_cons, exec_simdExtend_vex128_zxbw_reg]
    dsimp only; rw [show BitVec.extractLsb' 0 64 (y3s y0) = BitVec.extractLsb' 0 64 x0_0 from by
      dsimp only [y3s, y2s, y1s]; (repeat rw [writeXmm128_ne true _ (by decide)]); exact hlo64_wx _ _ _]
    change execInstrSeq 2 _ _ _ { s with rip := 0x4002dd#64, regs := r2, ymms := y4s } = _
    rw [execInstrSeq_succ_cons, exec_simdPsrlqImm_vex128]
    dsimp only; rw [show BitVec.extractLsb' 0 128 (y4s y0) = x0_0 from by
      dsimp only [y4s, y3s, y2s, y1s]; (repeat rw [writeXmm128_ne true _ (by decide)]); exact writeXmm128_true_lo _ _ _]
    change execInstrSeq 1 _ _ _ { s with rip := 0x4002e2#64, regs := r2, ymms := y5s } = _
    rw [execInstrSeq_succ_cons, exec_simdExtend_vex128_zxwd_reg, execInstrSeq_zero]
    dsimp only; rw [show BitVec.extractLsb' 0 64 (y5s y2) = BitVec.extractLsb' 0 64 x2_0 from by
      dsimp only [y5s, y4s]; rw [writeXmm128_ne true _ (by decide : y2 ≠ y0), hlo64_wx]]
  rw [he]; refine ⟨hrun, hnf, rfl, rfl, rfl, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · dsimp only [y6s, y5s]; rw [writeXmm128_ne true _ (by decide : y0 ≠ y1), writeXmm128_true_lo]
  · exact writeXmm128_true_lo _ _ _
  · dsimp only [y6s, y5s, y4s]; (repeat rw [writeXmm128_ne true _ (by decide)]); exact writeXmm128_true_lo _ _ _
  · dsimp only [y6s, y5s, y4s, y3s]; (repeat rw [writeXmm128_ne true _ (by decide)]); exact writeXmm128_true_lo _ _ _
  · dsimp only [y6s, y5s, y4s, y3s, y2s]; (repeat rw [writeXmm128_ne true _ (by decide)]); exact writeXmm128_true_lo _ _ _
  · dsimp only [y6s, y5s, y4s, y3s, y2s, y1s]; repeat rw [writeXmm128_ne true _ (by decide)]
  · intro hc; exact writeXmm128_true_preserves_clean _ _ _ (writeXmm128_true_preserves_clean _ _ _
      (writeXmm128_true_preserves_clean _ _ _ (writeXmm128_true_preserves_clean _ _ _
        (writeXmm128_true_preserves_clean _ _ _ (writeXmm128_true_preserves_clean _ _ _ hc)))))

private theorem dotO3_epi8_stepB (sA : X64State) (v0 v1 v2 v3 v4 : BitVec 128) (idx : Nat) (nd : Nat → UndefChoice)
    (hrun : sA.halted = false) (hnf : sA.fault = false) (hrip : sA.rip = 0x4002e7#64)
    (hy0 : BitVec.extractLsb' 0 128 (sA.ymms y0) = v0) (hy1 : BitVec.extractLsb' 0 128 (sA.ymms y1) = v1)
    (hy2 : BitVec.extractLsb' 0 128 (sA.ymms y2) = v2) (hy3 : BitVec.extractLsb' 0 128 (sA.ymms y3) = v3)
    (hy4 : BitVec.extractLsb' 0 128 (sA.ymms y4) = v4) :
    let x6_0 := packDwords128 fun i => (BitVec.extractLsb' (i.val * 16) 16 (BitVec.extractLsb' 0 64 v4)).zeroExtend 32
    let x0_2 := packWords128 fun i => (BitVec.extractLsb' (i.val * 8) 8 (BitVec.extractLsb' 0 64 v0)).zeroExtend 16
    let x2_1 := psrlqImm128 v2 0x20#8
    let x4_1 := psrlqImm128 v4 0x20#8
    let x4_2 := packDwords128 fun i => (BitVec.extractLsb' (i.val * 16) 16 (BitVec.extractLsb' 0 64 x4_1)).zeroExtend 32
    let x2_2 := packDwords128 fun i => (BitVec.extractLsb' (i.val * 16) 16 (BitVec.extractLsb' 0 64 x2_1)).zeroExtend 32
    let sB := runFrom dotO3Cmap 8 idx nd sA
    sB.halted = false ∧ sB.fault = false ∧ sB.rip = 0x40030f#64 ∧ sB.mem = sA.mem ∧ sB.regs = sA.regs ∧
    BitVec.extractLsb' 0 128 (sB.ymms y0) = x0_2 ∧
    BitVec.extractLsb' 0 128 (sB.ymms y1) = pmulld128 v1 x6_0 ∧
    BitVec.extractLsb' 0 128 (sB.ymms y2) = pmulld128 x2_2 x4_2 ∧
    BitVec.extractLsb' 0 128 (sB.ymms y3) = v3 ∧
    BitVec.extractLsb' 0 128 (sB.ymms y5) = BitVec.extractLsb' 0 128 (sA.ymms y5) ∧
    (AllUpperYmmClean sA → AllUpperYmmClean sB) := by
  dsimp only
  have hlo64_of_lo128 : ∀ {x : BitVec 256} {v : BitVec 128}, BitVec.extractLsb' 0 128 x = v →
      BitVec.extractLsb' 0 64 x = BitVec.extractLsb' 0 64 v := fun {x v} h => by
    rw [← h]; apply BitVec.eq_of_getLsbD_eq; intro b _hb; simp
  let x6_0 := packDwords128 fun i => (BitVec.extractLsb' (i.val * 16) 16 (BitVec.extractLsb' 0 64 v4)).zeroExtend 32
  let x0_2 := packWords128 fun i => (BitVec.extractLsb' (i.val * 8) 8 (BitVec.extractLsb' 0 64 v0)).zeroExtend 16
  let x2_1 := psrlqImm128 v2 0x20#8
  let x4_1 := psrlqImm128 v4 0x20#8
  let x4_2 := packDwords128 fun i => (BitVec.extractLsb' (i.val * 16) 16 (BitVec.extractLsb' 0 64 x4_1)).zeroExtend 32
  let p01  := pmulld128 v1 x6_0
  let x2_2 := packDwords128 fun i => (BitVec.extractLsb' (i.val * 16) 16 (BitVec.extractLsb' 0 64 x2_1)).zeroExtend 32
  let p23  := pmulld128 x2_2 x4_2
  let y1s := writeXmm128 true sA.ymms y6 x6_0
  let y2s := writeXmm128 true y1s y0 x0_2
  let y3s := writeXmm128 true y2s y2 x2_1
  let y4s := writeXmm128 true y3s y4 x4_1
  let y5s := writeXmm128 true y4s y4 x4_2
  let y6s := writeXmm128 true y5s y1 p01
  let y7s := writeXmm128 true y6s y2 x2_2
  let y8s := writeXmm128 true y7s y2 p23
  rcases runFrom_of_decodeSeqAt dotO3_epi8B_dec idx nd sA hrun hnf hrip with ⟨hseq, _, _⟩
  have he : runFrom dotO3Cmap 8 idx nd sA = { sA with rip := 0x40030f#64, ymms := y8s } := by
    rw [hseq]; dsimp only [dotO3_epi8BSeq]
    rw [execInstrSeq_succ_cons, exec_simdExtend_vex128_zxwd_reg, hlo64_of_lo128 hy4]
    change execInstrSeq 7 _ _ _ { sA with rip := 0x4002ec#64, ymms := y1s } = _
    rw [execInstrSeq_succ_cons, exec_simdExtend_vex128_zxbw_reg]
    dsimp only; rw [hlo64_of_lo128 (show BitVec.extractLsb' 0 128 (y1s y0) = v0 from by dsimp only [y1s]; rw [writeXmm128_ne true _ (by decide : y0 ≠ y6), hy0])]
    change execInstrSeq 6 _ _ _ { sA with rip := 0x4002f1#64, ymms := y2s } = _
    rw [execInstrSeq_succ_cons, exec_simdPsrlqImm_vex128]
    dsimp only; rw [show BitVec.extractLsb' 0 128 (y2s y2) = v2 from by dsimp only [y2s, y1s]; (repeat rw [writeXmm128_ne true _ (by decide)]); exact hy2]
    change execInstrSeq 5 _ _ _ { sA with rip := 0x4002f6#64, ymms := y3s } = _
    rw [execInstrSeq_succ_cons, exec_simdPsrlqImm_vex128]
    dsimp only; rw [show BitVec.extractLsb' 0 128 (y3s y4) = v4 from by dsimp only [y3s, y2s, y1s]; (repeat rw [writeXmm128_ne true _ (by decide)]); exact hy4]
    change execInstrSeq 4 _ _ _ { sA with rip := 0x4002fb#64, ymms := y4s } = _
    rw [execInstrSeq_succ_cons, exec_simdExtend_vex128_zxwd_reg]
    dsimp only; rw [hlo64_of_lo128 (writeXmm128_true_lo _ _ _)]
    change execInstrSeq 3 _ _ _ { sA with rip := 0x400300#64, ymms := y5s } = _
    rw [execInstrSeq_succ_cons, exec_simdPmulld_vex128_reg]
    dsimp only; rw [show BitVec.extractLsb' 0 128 (y5s y1) = v1 from by dsimp only [y5s, y4s, y3s, y2s, y1s]; (repeat rw [writeXmm128_ne true _ (by decide)]); exact hy1,
                    show BitVec.extractLsb' 0 128 (y5s y6) = x6_0 from by dsimp only [y5s, y4s, y3s, y2s, y1s]; (repeat rw [writeXmm128_ne true _ (by decide)]); exact writeXmm128_true_lo _ _ _]
    change execInstrSeq 2 _ _ _ { sA with rip := 0x400305#64, ymms := y6s } = _
    rw [execInstrSeq_succ_cons, exec_simdExtend_vex128_zxwd_reg]
    dsimp only; rw [hlo64_of_lo128 (show BitVec.extractLsb' 0 128 (y6s y2) = x2_1 from by dsimp only [y6s, y5s, y4s, y3s]; (repeat rw [writeXmm128_ne true _ (by decide)]); exact writeXmm128_true_lo _ _ _)]
    change execInstrSeq 1 _ _ _ { sA with rip := 0x40030a#64, ymms := y7s } = _
    rw [execInstrSeq_succ_cons, exec_simdPmulld_vex128_reg, execInstrSeq_zero]
    dsimp only; rw [show BitVec.extractLsb' 0 128 (y7s y2) = x2_2 from writeXmm128_true_lo _ _ _,
                    show BitVec.extractLsb' 0 128 (y7s y4) = x4_2 from by dsimp only [y7s, y6s, y5s]; (repeat rw [writeXmm128_ne true _ (by decide)]); exact writeXmm128_true_lo _ _ _]
  rw [he]; refine ⟨hrun, hnf, rfl, rfl, rfl, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · dsimp only [y8s, y7s, y6s, y5s, y4s, y3s, y2s]; (repeat rw [writeXmm128_ne true _ (by decide)]); exact writeXmm128_true_lo _ _ _
  · dsimp only [y8s, y7s, y6s]; (repeat rw [writeXmm128_ne true _ (by decide)]); exact writeXmm128_true_lo _ _ _
  · exact writeXmm128_true_lo _ _ _
  · dsimp only [y8s, y7s, y6s, y5s, y4s, y3s, y2s, y1s]; (repeat rw [writeXmm128_ne true _ (by decide)]); exact hy3
  · dsimp only [y8s, y7s, y6s, y5s, y4s, y3s, y2s, y1s]; repeat rw [writeXmm128_ne true _ (by decide)]
  · intro hc; exact writeXmm128_true_preserves_clean _ _ _ (writeXmm128_true_preserves_clean _ _ _
      (writeXmm128_true_preserves_clean _ _ _ (writeXmm128_true_preserves_clean _ _ _
        (writeXmm128_true_preserves_clean _ _ _ (writeXmm128_true_preserves_clean _ _ _
          (writeXmm128_true_preserves_clean _ _ _ (writeXmm128_true_preserves_clean _ _ _ hc)))))))

private theorem dotO3_epi8_stepC (sB : X64State) (v0 v1 v2 v3 : BitVec 128) (idx : Nat) (nd : Nat → UndefChoice)
    (hrun : sB.halted = false) (hnf : sB.fault = false) (hrip : sB.rip = 0x40030f#64)
    (hy0 : BitVec.extractLsb' 0 128 (sB.ymms y0) = v0) (hy1 : BitVec.extractLsb' 0 128 (sB.ymms y1) = v1)
    (hy2 : BitVec.extractLsb' 0 128 (sB.ymms y2) = v2) (hy3 : BitVec.extractLsb' 0 128 (sB.ymms y3) = v3) :
    let x4_3 := packDwords128 fun i => (BitVec.extractLsb' (i.val * 16) 16 (BitVec.extractLsb' 0 64 v3)).zeroExtend 32
    let x3_1 := psrlqImm128 v3 0x20#8
    let x3_2 := packDwords128 fun i => (BitVec.extractLsb' (i.val * 16) 16 (BitVec.extractLsb' 0 64 x3_1)).zeroExtend 32
    let s03  := packDwords128 fun i => getDword128 v1 i + getDword128 v2 i
    let x2_3 := packDwords128 fun i => (BitVec.extractLsb' (i.val * 16) 16 (BitVec.extractLsb' 0 64 v0)).zeroExtend 32
    let x0_3 := psrlqImm128 v0 0x20#8
    let p45  := pmulld128 x2_3 x4_3
    let x0_4 := packDwords128 fun i => (BitVec.extractLsb' (i.val * 16) 16 (BitVec.extractLsb' 0 64 x0_3)).zeroExtend 32
    let sC := runFrom dotO3Cmap 8 idx nd sB
    sC.halted = false ∧ sC.fault = false ∧ sC.rip = 0x400336#64 ∧ sC.mem = sB.mem ∧ sC.regs = sB.regs ∧
    BitVec.extractLsb' 0 128 (sC.ymms y0) = x0_4 ∧
    BitVec.extractLsb' 0 128 (sC.ymms y1) = s03 ∧
    BitVec.extractLsb' 0 128 (sC.ymms y2) = p45 ∧
    BitVec.extractLsb' 0 128 (sC.ymms y3) = x3_2 ∧
    BitVec.extractLsb' 0 128 (sC.ymms y5) = BitVec.extractLsb' 0 128 (sB.ymms y5) ∧
    (AllUpperYmmClean sB → AllUpperYmmClean sC) := by
  dsimp only
  have hlo64_of_lo128 : ∀ {x : BitVec 256} {v : BitVec 128}, BitVec.extractLsb' 0 128 x = v →
      BitVec.extractLsb' 0 64 x = BitVec.extractLsb' 0 64 v := fun {x v} h => by
    rw [← h]; apply BitVec.eq_of_getLsbD_eq; intro b _hb; simp
  let x4_3 := packDwords128 fun i => (BitVec.extractLsb' (i.val * 16) 16 (BitVec.extractLsb' 0 64 v3)).zeroExtend 32
  let x3_1 := psrlqImm128 v3 0x20#8
  let x3_2 := packDwords128 fun i => (BitVec.extractLsb' (i.val * 16) 16 (BitVec.extractLsb' 0 64 x3_1)).zeroExtend 32
  let s03  := packDwords128 fun i => getDword128 v1 i + getDword128 v2 i
  let x2_3 := packDwords128 fun i => (BitVec.extractLsb' (i.val * 16) 16 (BitVec.extractLsb' 0 64 v0)).zeroExtend 32
  let x0_3 := psrlqImm128 v0 0x20#8
  let p45  := pmulld128 x2_3 x4_3
  let x0_4 := packDwords128 fun i => (BitVec.extractLsb' (i.val * 16) 16 (BitVec.extractLsb' 0 64 x0_3)).zeroExtend 32
  let y1s := writeXmm128 true sB.ymms y4 x4_3
  let y2s := writeXmm128 true y1s y3 x3_1
  let y3s := writeXmm128 true y2s y3 x3_2
  let y4s := writeXmm128 true y3s y1 s03
  let y5s := writeXmm128 true y4s y2 x2_3
  let y6s := writeXmm128 true y5s y0 x0_3
  let y7s := writeXmm128 true y6s y2 p45
  let y8s := writeXmm128 true y7s y0 x0_4
  rcases runFrom_of_decodeSeqAt dotO3_epi8C_dec idx nd sB hrun hnf hrip with ⟨hseq, _, _⟩
  have he : runFrom dotO3Cmap 8 idx nd sB = { sB with rip := 0x400336#64, ymms := y8s } := by
    rw [hseq]; dsimp only [dotO3_epi8CSeq]
    rw [execInstrSeq_succ_cons, exec_simdExtend_vex128_zxwd_reg, hlo64_of_lo128 hy3]
    change execInstrSeq 7 _ _ _ { sB with rip := 0x400314#64, ymms := y1s } = _
    rw [execInstrSeq_succ_cons, exec_simdPsrlqImm_vex128]
    dsimp only; rw [show BitVec.extractLsb' 0 128 (y1s y3) = v3 from by dsimp only [y1s]; rw [writeXmm128_ne true _ (by decide : y3 ≠ y4), hy3]]
    change execInstrSeq 6 _ _ _ { sB with rip := 0x400319#64, ymms := y2s } = _
    rw [execInstrSeq_succ_cons, exec_simdExtend_vex128_zxwd_reg]
    dsimp only; rw [hlo64_of_lo128 (writeXmm128_true_lo _ _ _)]
    change execInstrSeq 5 _ _ _ { sB with rip := 0x40031e#64, ymms := y3s } = _
    rw [execInstrSeq_succ_cons, exec_simdAdd_vex128_e32_reg]
    dsimp only; rw [show BitVec.extractLsb' 0 128 (y3s y1) = v1 from by dsimp only [y3s, y2s, y1s]; (repeat rw [writeXmm128_ne true _ (by decide)]); exact hy1,
                    show BitVec.extractLsb' 0 128 (y3s y2) = v2 from by dsimp only [y3s, y2s, y1s]; (repeat rw [writeXmm128_ne true _ (by decide)]); exact hy2]
    change execInstrSeq 4 _ _ _ { sB with rip := 0x400322#64, ymms := y4s } = _
    rw [execInstrSeq_succ_cons, exec_simdExtend_vex128_zxwd_reg]
    dsimp only; rw [hlo64_of_lo128 (show BitVec.extractLsb' 0 128 (y4s y0) = v0 from by dsimp only [y4s, y3s, y2s, y1s]; (repeat rw [writeXmm128_ne true _ (by decide)]); exact hy0)]
    change execInstrSeq 3 _ _ _ { sB with rip := 0x400327#64, ymms := y5s } = _
    rw [execInstrSeq_succ_cons, exec_simdPsrlqImm_vex128]
    dsimp only; rw [show BitVec.extractLsb' 0 128 (y5s y0) = v0 from by dsimp only [y5s, y4s, y3s, y2s, y1s]; (repeat rw [writeXmm128_ne true _ (by decide)]); exact hy0]
    change execInstrSeq 2 _ _ _ { sB with rip := 0x40032c#64, ymms := y6s } = _
    rw [execInstrSeq_succ_cons, exec_simdPmulld_vex128_reg]
    dsimp only; rw [show BitVec.extractLsb' 0 128 (y6s y2) = x2_3 from by dsimp only [y6s, y5s]; rw [writeXmm128_ne true _ (by decide : y2 ≠ y0), writeXmm128_true_lo],
                    show BitVec.extractLsb' 0 128 (y6s y4) = x4_3 from by dsimp only [y6s, y5s, y4s, y3s, y2s, y1s]; (repeat rw [writeXmm128_ne true _ (by decide)]); exact writeXmm128_true_lo _ _ _]
    change execInstrSeq 1 _ _ _ { sB with rip := 0x400331#64, ymms := y7s } = _
    rw [execInstrSeq_succ_cons, exec_simdExtend_vex128_zxwd_reg, execInstrSeq_zero]
    dsimp only; rw [hlo64_of_lo128 (show BitVec.extractLsb' 0 128 (y7s y0) = x0_3 from by dsimp only [y7s, y6s]; rw [writeXmm128_ne true _ (by decide : y0 ≠ y2), writeXmm128_true_lo])]
  rw [he]; refine ⟨hrun, hnf, rfl, rfl, rfl, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact writeXmm128_true_lo _ _ _
  · dsimp only [y8s, y7s, y6s, y5s, y4s]; (repeat rw [writeXmm128_ne true _ (by decide)]); exact writeXmm128_true_lo _ _ _
  · dsimp only [y8s, y7s]; rw [writeXmm128_ne true _ (by decide : y2 ≠ y0), writeXmm128_true_lo]
  · dsimp only [y8s, y7s, y6s, y5s, y4s, y3s]; (repeat rw [writeXmm128_ne true _ (by decide)]); exact writeXmm128_true_lo _ _ _
  · dsimp only [y8s, y7s, y6s, y5s, y4s, y3s, y2s, y1s]; repeat rw [writeXmm128_ne true _ (by decide)]
  · intro hc; exact writeXmm128_true_preserves_clean _ _ _ (writeXmm128_true_preserves_clean _ _ _
      (writeXmm128_true_preserves_clean _ _ _ (writeXmm128_true_preserves_clean _ _ _
        (writeXmm128_true_preserves_clean _ _ _ (writeXmm128_true_preserves_clean _ _ _
          (writeXmm128_true_preserves_clean _ _ _ (writeXmm128_true_preserves_clean _ _ _ hc)))))))

private theorem dotO3_epi8_stepD (sC : X64State) (v0 v1 v2 v3 v5 : BitVec 128) (r8V : BitVec 64)
    (idx : Nat) (nd : Nat → UndefChoice)
    (hrun : sC.halted = false) (hnf : sC.fault = false) (hrip : sC.rip = 0x400336#64)
    (hr8 : sC.regs .r8 = r8V)
    (hy0 : BitVec.extractLsb' 0 128 (sC.ymms y0) = v0) (hy1 : BitVec.extractLsb' 0 128 (sC.ymms y1) = v1)
    (hy2 : BitVec.extractLsb' 0 128 (sC.ymms y2) = v2) (hy3 : BitVec.extractLsb' 0 128 (sC.ymms y3) = v3)
    (hy5 : BitVec.extractLsb' 0 128 (sC.ymms y5) = v5) :
    let p67  := pmulld128 v0 v3
    let s03a := packDwords128 fun i => getDword128 v1 i + getDword128 v5 i
    let s47  := packDwords128 fun i => getDword128 v2 i + getDword128 p67 i
    let sAll := packDwords128 fun i => getDword128 s03a i + getDword128 s47 i
    let sD := runFrom dotO3Cmap 8 idx nd sC
    sD.halted = false ∧ sD.fault = false ∧ sD.rip = 0x400358#64 ∧ sD.mem = sC.mem ∧
    sD.regs = regUpd sC.regs .rax ((sumLo2Dwords128 sAll).zeroExtend 64) ∧
    sD.flags = (evalAluN (by decide) .test (BitVec.extractLsb' 0 8 r8V) 0x07#8 sC.flags (nd (idx + 7)).flags).2 ∧
    (AllUpperYmmClean sC → AllUpperYmmClean sD) := by
  dsimp only
  let p67  := pmulld128 v0 v3
  let s03a := packDwords128 fun i => getDword128 v1 i + getDword128 v5 i
  let s47  := packDwords128 fun i => getDword128 v2 i + getDword128 p67 i
  let sAll := packDwords128 fun i => getDword128 s03a i + getDword128 s47 i
  let sSh  := psrlqImm128 sAll 0x20#8
  let sFin := packDwords128 fun i => getDword128 sAll i + getDword128 sSh i
  let y1s := writeXmm128 true sC.ymms y0 p67
  let y2s := writeXmm128 true y1s y1 s03a
  let y3s := writeXmm128 true y2s y0 s47
  let y4s := writeXmm128 true y3s y0 sAll
  let y5s := writeXmm128 true y4s y1 sSh
  let y6s := writeXmm128 true y5s y0 sFin
  have hlo32 : BitVec.extractLsb' 0 32 (y6s y0) = sumLo2Dwords128 sAll := by
    have hx : BitVec.extractLsb' 0 32 (y6s y0) = BitVec.extractLsb' 0 32 (BitVec.extractLsb' 0 128 (y6s y0)) := by
      apply BitVec.eq_of_getLsbD_eq; intro b _hb; simp
    rw [hx, writeXmm128_true_lo]; exact fold_psrlq32_eq_sumLo2 sAll
  rcases runFrom_of_decodeSeqAt dotO3_epi8D_dec idx nd sC hrun hnf hrip with ⟨hseq, _, _⟩
  have he : runFrom dotO3Cmap 8 idx nd sC =
      { sC with
        rip := 0x400358#64,
        regs := regUpd sC.regs .rax ((sumLo2Dwords128 sAll).zeroExtend 64),
        ymms := y6s,
        flags := (evalAluN (by decide) .test (BitVec.extractLsb' 0 8 r8V) 0x07#8 sC.flags (nd (idx + 7)).flags).2 } := by
    rw [hseq]; dsimp only [dotO3_epi8DSeq]
    rw [execInstrSeq_succ_cons, exec_simdPmulld_vex128_reg, hy0, hy3]
    change execInstrSeq 7 _ _ _ { sC with rip := 0x40033b#64, ymms := y1s } = _
    rw [execInstrSeq_succ_cons, exec_simdAdd_vex128_e32_reg]
    dsimp only; rw [show BitVec.extractLsb' 0 128 (y1s y1) = v1 from by dsimp only [y1s]; rw [writeXmm128_ne true _ (by decide : y1 ≠ y0), hy1],
                    show BitVec.extractLsb' 0 128 (y1s y5) = v5 from by dsimp only [y1s]; rw [writeXmm128_ne true _ (by decide : y5 ≠ y0), hy5]]
    change execInstrSeq 6 _ _ _ { sC with rip := 0x40033f#64, ymms := y2s } = _
    rw [execInstrSeq_succ_cons, exec_simdAdd_vex128_e32_reg]
    dsimp only; rw [show BitVec.extractLsb' 0 128 (y2s y2) = v2 from by dsimp only [y2s, y1s]; (repeat rw [writeXmm128_ne true _ (by decide)]); exact hy2,
                    show BitVec.extractLsb' 0 128 (y2s y0) = p67 from by dsimp only [y2s, y1s]; rw [writeXmm128_ne true _ (by decide : y0 ≠ y1), writeXmm128_true_lo]]
    change execInstrSeq 5 _ _ _ { sC with rip := 0x400343#64, ymms := y3s } = _
    rw [execInstrSeq_succ_cons, exec_simdAdd_vex128_e32_reg]
    dsimp only; rw [show BitVec.extractLsb' 0 128 (y3s y1) = s03a from by dsimp only [y3s, y2s]; rw [writeXmm128_ne true _ (by decide : y1 ≠ y0), writeXmm128_true_lo],
                    show BitVec.extractLsb' 0 128 (y3s y0) = s47 from writeXmm128_true_lo _ _ _]
    change execInstrSeq 4 _ _ _ { sC with rip := 0x400347#64, ymms := y4s } = _
    rw [execInstrSeq_succ_cons, exec_simdPsrlqImm_vex128]
    dsimp only; rw [show BitVec.extractLsb' 0 128 (y4s y0) = sAll from writeXmm128_true_lo _ _ _]
    change execInstrSeq 3 _ _ _ { sC with rip := 0x40034c#64, ymms := y5s } = _
    rw [execInstrSeq_succ_cons, exec_simdAdd_vex128_e32_reg]
    dsimp only; rw [show BitVec.extractLsb' 0 128 (y5s y0) = sAll from by dsimp only [y5s, y4s]; rw [writeXmm128_ne true _ (by decide : y0 ≠ y1), writeXmm128_true_lo],
                    show BitVec.extractLsb' 0 128 (y5s y1) = sSh from writeXmm128_true_lo _ _ _]
    change execInstrSeq 2 _ _ _ { sC with rip := 0x400350#64, ymms := y6s } = _
    rw [execInstrSeq_succ_cons, exec_simdMovXToGpr_s32_reg]
    dsimp only; rw [hlo32]
    rw [execInstrSeq_succ_cons, exec_alu8Imm_test_lo8, execInstrSeq_zero]
    dsimp only; rw [regUpd_ne _ (by decide), hr8]
  rw [he]; refine ⟨hrun, hnf, rfl, rfl, rfl, rfl, ?_⟩
  intro hc; exact writeXmm128_true_preserves_clean _ _ _ (writeXmm128_true_preserves_clean _ _ _
    (writeXmm128_true_preserves_clean _ _ _ (writeXmm128_true_preserves_clean _ _ _
      (writeXmm128_true_preserves_clean _ _ _ (writeXmm128_true_preserves_clean _ _ _ hc)))))

private theorem dotO3_epi8_0x2af (s0 s : X64State) (done0 r10Val idx : Nat) (nd : Nat → UndefChoice)
    (hpre : DotU8U16Pre 0 s0)
    (hrun : s.halted = false) (hnf : s.fault = false) (hrip : s.rip = 0x4002af#64) (hmem : s.mem = s0.mem)
    (hrdi : s.regs .rdi = s0.regs .rdi) (hrsi : s.regs .rsi = s0.regs .rsi) (hrdx : s.regs .rdx = s0.regs .rdx)
    (hr9 : s.regs .r9 = BitVec.ofNat 64 done0) (hr10 : s.regs .r10 = BitVec.ofNat 64 r10Val)
    (hrcx : s.regs .rcx = BitVec.ofNat 64 (done0 + r10Val))
    (hr8 : s.regs .r8 = BitVec.ofNat 64 ((s0.regs .rdx).toNat - done0))
    (hrax : BitVec.extractLsb' 0 32 (s.regs .rax) =
      rustDotU8U16From s0.mem (s0.regs .rdi) (s0.regs .rsi) (done0 + r10Val) 0#32)
    (hy5 : sumLo2Dwords128 (BitVec.extractLsb' 0 128 (s.ymms y5)) =
      rustDotU8U16From s0.mem (s0.regs .rdi) (s0.regs .rsi) (done0 + r10Val) 0#32)
    (hcs : SysVCalleeSavedPreserved s0 s) (hymm : UpperYmmCleanOrPreserved s0 s)
    (hlt : done0 + r10Val < (s0.regs .rdx).toNat)
    (hremHi : (s0.regs .rdx).toNat - (done0 + r10Val) ≤ 15) :
    ∃ steps : Nat,
      let sf := runFrom dotO3Cmap steps idx nd s
      sf.halted = true ∧ sf.fault = false ∧
      SysVCalleeSavedPreserved s0 sf ∧ UpperYmmCleanOrPreserved s0 sf ∧
      DotU8U16Post 0 s0 sf := by
  have h2len := hpre.1; have hlenLt := (s0.regs .rdx).isLt
  have hsub8 : BitVec.ofNat 64 ((s0.regs .rdx).toNat - done0) - BitVec.ofNat 64 r10Val =
      BitVec.ofNat 64 ((s0.regs .rdx).toNat - (done0 + r10Val)) := by
    apply BitVec.eq_of_toNat_eq
    rw [bv64_sub_toNat_of_le (by simp [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega : (s0.regs .rdx).toNat - done0 < 2 ^ 64), Nat.mod_eq_of_lt (by omega : r10Val < 2 ^ 64)]; omega)]
    simp [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega : (s0.regs .rdx).toNat - done0 < 2 ^ 64),
          Nat.mod_eq_of_lt (by omega : r10Val < 2 ^ 64), Nat.mod_eq_of_lt (by omega : (s0.regs .rdx).toNat - (done0 + r10Val) < 2 ^ 64)]
    omega
  let remBv : BitVec 64 := BitVec.ofNat 64 ((s0.regs .rdx).toNat - (done0 + r10Val))
  have hremTn : remBv.toNat = (s0.regs .rdx).toNat - (done0 + r10Val) := by
    dsimp only [remBv]; rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)]
  rcases runFrom_of_decodeSeqAt dotO3_epi8Chk_dec idx nd s hrun hnf hrip with ⟨hchk, hrun1, hnf1⟩
  have heChk : execInstrSeq 3 dotO3_epi8ChkSeq idx nd s =
      { s with
        rip := 0x4002ba#64,
        regs := regUpd (regUpd s.regs .r8 remBv) .r11 (remBv + 0xffffffffffffffff#64),
        flags := (evalAluN (by decide) .cmp (remBv + 0xffffffffffffffff#64) 0x06#64
                   (evalAluN (by decide) .sub (BitVec.ofNat 64 ((s0.regs .rdx).toNat - done0)) (BitVec.ofNat 64 r10Val) s.flags (nd idx).flags).2
                   (nd (idx + 2)).flags).2 } := by
    dsimp only [dotO3_epi8ChkSeq]
    rw [execInstrSeq_succ_cons, exec_aluRmReg_s64_sub, hr8, hr10, hsub8]
    rw [execInstrSeq_succ_cons, exec_lea_s64, evalByteAddr_base_disp]
    dsimp only; rw [regUpd_eq]
    rw [execInstrSeq_succ_cons, exec_aluImm_s64_cmp, execInstrSeq_zero]
    dsimp only; rw [regUpd_eq]
  have hbe7 := bv64_sub1_cmp_be remBv 6 (by rw [hremTn]; omega) (by decide)
  rw [hremTn] at hbe7
  by_cases hle7 : (s0.regs .rdx).toNat - (done0 + r10Val) ≤ 7
  · have hcc7 : evalCond .be (execInstrSeq 3 dotO3_epi8ChkSeq idx nd s).flags = true := by
      rw [heChk]; dsimp only; rw [evalCond_be_of_flags, cmp_flags_cf, cmp_flags_zf]
      change (decide ((remBv + 0xffffffffffffffff#64).toNat < 6) || ((remBv + 0xffffffffffffffff#64) - BitVec.ofNat 64 6 == 0#64)) = true
      rw [hbe7]; simp [hle7]
    let s1 := runFrom dotO3Cmap 4 idx nd s
    have hs1 : s1 = { execInstrSeq 3 dotO3_epi8ChkSeq idx nd s with rip := 0x400365#64 } := by
      dsimp only [s1]; rw [show (4 : Nat) = 3 + 1 by rfl, runFrom_add, hchk, runFrom_succ,
        step_at_concrete dotO3_epi8Chk_jbe _ _ hrun1 hnf1 (by rw [heChk]), exec_jcc_taken hcc7, runFrom_zero]
      rw [heChk]; rfl
    have hcs1 : SysVCalleeSavedPreserved s0 s1 := by
      unfold SysVCalleeSavedPreserved at hcs ⊢; rw [hs1, heChk]; dsimp only
      exact cs_step_caller (r := .r11) rfl (cs_step_caller (r := .r8) rfl hcs)
    have hTail := dotO3_unrolled_0x365 s0 s1 (done0 + r10Val) (idx + 4) nd hpre
      (by rw [hs1, heChk]; exact hrun) (by rw [hs1, heChk]; exact hnf) (by rw [hs1]) (by rw [hs1, heChk]; exact hmem)
      (by rw [hs1, heChk]; dsimp only; (repeat rw [regUpd_ne _ (by decide)]); exact hrdi)
      (by rw [hs1, heChk]; dsimp only; (repeat rw [regUpd_ne _ (by decide)]); exact hrsi)
      (by rw [hs1, heChk]; dsimp only; (repeat rw [regUpd_ne _ (by decide)]); exact hrdx)
      (by rw [hs1, heChk]; dsimp only; (repeat rw [regUpd_ne _ (by decide)]); exact hrcx)
      (by rw [hs1, heChk]; dsimp only; (repeat rw [regUpd_ne _ (by decide)]); exact hrax)
      hcs1 (by rw [hs1, heChk]; exact hymm) hlt (by omega)
    rcases hTail with ⟨k, hk⟩
    exact ⟨4 + k, by rw [runFrom_add]; exact hk⟩
  · have hcc7 : evalCond .be (execInstrSeq 3 dotO3_epi8ChkSeq idx nd s).flags = false := by
      rw [heChk]; dsimp only; rw [evalCond_be_of_flags, cmp_flags_cf, cmp_flags_zf]
      change (decide ((remBv + 0xffffffffffffffff#64).toNat < 6) || ((remBv + 0xffffffffffffffff#64) - BitVec.ofNat 64 6 == 0#64)) = false
      rw [hbe7]; simp [hle7]
    let s1 := runFrom dotO3Cmap 4 idx nd s
    have hs1 : s1 = { execInstrSeq 3 dotO3_epi8ChkSeq idx nd s with rip := 0x4002c0#64 } := by
      dsimp only [s1]; rw [show (4 : Nat) = 3 + 1 by rfl, runFrom_add, hchk, runFrom_succ,
        step_at_concrete dotO3_epi8Chk_jbe _ _ hrun1 hnf1 (by rw [heChk]), exec_jcc_fall hcc7, runFrom_zero]
      rw [heChk]; rfl
    have hshlBase : BitVec.ofNat 64 (done0 + r10Val) <<< 1 = BitVec.ofNat 64 (2 * (done0 + r10Val)) := by
      have htn : (BitVec.ofNat 64 (done0 + r10Val)).toNat = done0 + r10Val := by
        rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)]
      rw [bv64_shl1_toNat (by rw [htn]; omega), htn]
    have hA := dotO3_epi8_stepA s1 (s0.regs .rdi) (s0.regs .rsi) done0 r10Val (idx + 4) nd hshlBase
      (by rw [hs1, heChk]; exact hrun) (by rw [hs1, heChk]; exact hnf) (by rw [hs1])
      (by rw [hs1, heChk]; dsimp only; (repeat rw [regUpd_ne _ (by decide)]); exact hrdi)
      (by rw [hs1, heChk]; dsimp only; (repeat rw [regUpd_ne _ (by decide)]); exact hrsi)
      (by rw [hs1, heChk]; dsimp only; (repeat rw [regUpd_ne _ (by decide)]); exact hr9)
      (by rw [hs1, heChk]; dsimp only; (repeat rw [regUpd_ne _ (by decide)]); exact hr10)
    generalize hsA : runFrom dotO3Cmap 8 (idx + 4) nd s1 = sA at hA
    rcases hA with ⟨hAr, hAf, hArip, hAm, hAregs, hAy0, hAy1, hAy2, hAy3, hAy4, hAy5, hAym⟩
    have hB := dotO3_epi8_stepB sA _ _ _ _ _ (idx + 12) nd hAr hAf hArip hAy0 hAy1 hAy2 hAy3 hAy4
    generalize hsB : runFrom dotO3Cmap 8 (idx + 12) nd sA = sB at hB
    rcases hB with ⟨hBr, hBf, hBrip, hBm, hBregs, hBy0, hBy1, hBy2, hBy3, hBy5, hBym⟩
    have hC := dotO3_epi8_stepC sB _ _ _ _ (idx + 20) nd hBr hBf hBrip hBy0 hBy1 hBy2 hBy3
    generalize hsC : runFrom dotO3Cmap 8 (idx + 20) nd sB = sC at hC
    rcases hC with ⟨hCr, hCf, hCrip, hCm, hCregs, hCy0, hCy1, hCy2, hCy3, hCy5, hCym⟩
    have hCr8 : sC.regs .r8 = remBv := by
      rw [hCregs, hBregs, hAregs]; rw [regUpd_ne _ (by decide), regUpd_ne _ (by decide), hs1, heChk]; dsimp only
      rw [regUpd_ne _ (by decide), regUpd_eq]
    have hD := dotO3_epi8_stepD sC _ _ _ _ (BitVec.extractLsb' 0 128 (s.ymms y5)) remBv (idx + 28) nd
      hCr hCf hCrip hCr8 hCy0 hCy1 hCy2 hCy3 (by rw [hCy5, hBy5, hAy5, hs1, heChk])
    generalize hsD : runFrom dotO3Cmap 8 (idx + 28) nd sC = sD at hD
    rcases hD with ⟨hDr, hDf, hDrip, hDm, hDregs, hDfl, hDym⟩
    have hDm0 : sD.mem = s0.mem := by rw [hDm, hCm, hBm, hAm, hs1, heChk]; exact hmem
    have hDym0 : UpperYmmCleanOrPreserved s0 sD := fun hc => hDym (hCym (hBym (hAym (by rw [hs1, heChk]; exact hymm hc))))
    have hDax : BitVec.extractLsb' 0 32 (sD.regs .rax) =
        rustDotU8U16From s0.mem (s0.regs .rdi) (s0.regs .rsi) (done0 + r10Val + 8) 0#32 := by
      rw [hDregs, regUpd_eq, zext32_extract32_eq]
      have hs1m : s1.mem = s0.mem := by rw [hs1, heChk]; exact hmem
      rw [hs1m, dot8_vpmulld_algebra, hy5, ← rustDotU8U16From_split]
    have hDcs : SysVCalleeSavedPreserved s0 sD := by
      unfold SysVCalleeSavedPreserved at hcs ⊢
      rw [hDregs, hCregs, hBregs, hAregs, hs1, heChk]; dsimp only
      exact cs_step_caller (r := .rax) rfl (cs_step_caller (r := .r9) rfl (cs_step_caller (r := .rax) rfl
        (cs_step_caller (r := .r11) rfl (cs_step_caller (r := .r8) rfl hcs))))
    have hrunD : runFrom dotO3Cmap 36 idx nd s = sD := by
      rw [show (36 : Nat) = 4 + (8 + (8 + (8 + 8))) by rfl, runFrom_add, runFrom_add, hsA,
          show idx + 4 + 8 = idx + 12 by omega, runFrom_add, hsB,
          show idx + 12 + 8 = idx + 20 by omega, runFrom_add, hsC,
          show idx + 20 + 8 = idx + 28 by omega, hsD]
    have htest7 := bv64_test_lo8_7_eq remBv
    rw [hremTn] at htest7
    by_cases hmod8 : ((s0.regs .rdx).toNat - (done0 + r10Val)) % 8 = 0
    · have hcc8 : evalCond .e sD.flags = true := by
        rw [hDfl]; exact evalCond_e_of_zf_true (by rw [test_flags_zf, htest7]; simp [hmod8])
      have hlen8 : done0 + r10Val + 8 = (s0.regs .rdx).toNat := by omega
      rw [hlen8] at hDax
      let sE := runFrom dotO3Cmap 1 (idx + 36) nd sD
      have hsE : sE = { sD with rip := 0x400426#64 } := by
        dsimp only [sE]; rw [runFrom_succ, step_at_concrete dotO3_epi8_je _ sD hDr hDf hDrip, exec_jcc_taken hcc8, runFrom_zero]; rfl
      have hRet := dotO3_ret_at s0 sE 0x400426#64 (idx + 37) nd dotO3_ret426
        (by rw [hsE]; exact hDr) (by rw [hsE]; exact hDf) (by rw [hsE]) (by rw [hsE]; exact hDm0)
        (by rw [hsE]; exact hDax)
        (by unfold SysVCalleeSavedPreserved at hDcs ⊢; rw [hsE]; exact hDcs)
        (by rw [hsE]; exact hDym0)
      refine ⟨38, ?_⟩
      rw [show (38 : Nat) = 36 + (1 + 1) by rfl, runFrom_add, hrunD, runFrom_add]
      exact hRet
    · have hcc8 : evalCond .e sD.flags = false := by
        rw [hDfl]; exact evalCond_e_of_zf_false (by rw [test_flags_zf, htest7]; simp [hmod8])
      let sE := runFrom dotO3Cmap 1 (idx + 36) nd sD
      have hsE : sE = { sD with rip := 0x40035e#64 } := by
        dsimp only [sE]; rw [runFrom_succ, step_at_concrete dotO3_epi8_je _ sD hDr hDf hDrip, exec_jcc_fall hcc8, runFrom_zero]; rfl
      rcases runFrom_of_decodeSeqAt dotO3_post8_dec (idx + 37) nd sE
        (by rw [hsE]; exact hDr) (by rw [hsE]; exact hDf) (by rw [hsE]) with ⟨hp8, hrunP, hnfP⟩
      have hmask8 : remBv &&& 0xfffffffffffffff8#64 = BitVec.ofNat 64 8 := by
        apply BitVec.eq_of_toNat_eq; rw [bv64_and_neg8_toNat, hremTn, BitVec.toNat_ofNat]; omega
      have heP8 : execInstrSeq 2 dotO3_post8Seq (idx + 37) nd sE =
          { sE with
            rip := 0x400365#64,
            regs := regUpd (regUpd sE.regs .r8 (BitVec.ofNat 64 8)) .rcx (BitVec.ofNat 64 (done0 + r10Val + 8)),
            flags := (evalAluN (by decide) .add (BitVec.ofNat 64 (done0 + r10Val)) (BitVec.ofNat 64 8)
                       (evalAluN (by decide) .and remBv 0xfffffffffffffff8#64 sE.flags (nd (idx + 37)).flags).2
                       (nd (idx + 38)).flags).2 } := by
        dsimp only [dotO3_post8Seq]
        have hEr8 : sE.regs .r8 = remBv := by rw [hsE, hDregs, regUpd_ne _ (by decide), hCr8]
        have hEcx : sE.regs .rcx = BitVec.ofNat 64 (done0 + r10Val) := by
          rw [hsE, hDregs, hCregs, hBregs, hAregs]; (repeat rw [regUpd_ne _ (by decide)]); rw [hs1, heChk]; dsimp only
          (repeat rw [regUpd_ne _ (by decide)]); exact hrcx
        rw [execInstrSeq_succ_cons, exec_aluImm_s64_and, hEr8, hmask8]
        rw [execInstrSeq_succ_cons, exec_aluRmReg_s64_add, execInstrSeq_zero]
        dsimp only; rw [regUpd_ne _ (by decide), regUpd_eq, hEcx, bv64_ofNat_add]
      let sF := runFrom dotO3Cmap 2 (idx + 37) nd sE
      have hsF : sF = execInstrSeq 2 dotO3_post8Seq (idx + 37) nd sE := hp8
      have hFcs : SysVCalleeSavedPreserved s0 sF := by
        unfold SysVCalleeSavedPreserved at hDcs ⊢; rw [hsF, heP8, hsE]; dsimp only
        exact cs_step_caller (r := .rcx) rfl (cs_step_caller (r := .r8) rfl hDcs)
      have hTail := dotO3_unrolled_0x365 s0 sF (done0 + r10Val + 8) (idx + 39) nd hpre
        (by rw [hsF]; exact hrunP) (by rw [hsF]; exact hnfP) (by rw [hsF, heP8]) (by rw [hsF, heP8, hsE]; exact hDm0)
        (by rw [hsF, heP8]; dsimp only; (repeat rw [regUpd_ne _ (by decide)]); rw [hsE, hDregs, hCregs, hBregs, hAregs]; (repeat rw [regUpd_ne _ (by decide)]); rw [hs1, heChk]; dsimp only; (repeat rw [regUpd_ne _ (by decide)]); exact hrdi)
        (by rw [hsF, heP8]; dsimp only; (repeat rw [regUpd_ne _ (by decide)]); rw [hsE, hDregs, hCregs, hBregs, hAregs]; (repeat rw [regUpd_ne _ (by decide)]); rw [hs1, heChk]; dsimp only; (repeat rw [regUpd_ne _ (by decide)]); exact hrsi)
        (by rw [hsF, heP8]; dsimp only; (repeat rw [regUpd_ne _ (by decide)]); rw [hsE, hDregs, hCregs, hBregs, hAregs]; (repeat rw [regUpd_ne _ (by decide)]); rw [hs1, heChk]; dsimp only; (repeat rw [regUpd_ne _ (by decide)]); exact hrdx)
        (by rw [hsF, heP8]; dsimp only; exact regUpd_eq _ _ _)
        (by rw [hsF, heP8]; dsimp only; (repeat rw [regUpd_ne _ (by decide)]); rw [hsE]; exact hDax)
        hFcs (by rw [hsF, heP8, hsE]; exact hDym0) (by omega) (by omega)
      rcases hTail with ⟨k, hk⟩
      refine ⟨39 + k, ?_⟩
      rw [show 39 + k = 36 + (1 + (2 + k)) by omega, runFrom_add, hrunD, runFrom_add, runFrom_add]
      simpa [Nat.add_assoc] using hk

/-! ## Section 4: `16`-Elem VEX-128 Epilogue (`0x211..0x2af` + `0x441`) -/

private theorem dot16_vex128_algebra (m : ByteMem) (pa pb : BitVec 64) (accV : BitVec 128) :
    let a128 := readMem128 m pa
    let bLo  := readMem128 m pb
    let bHi  := readMem128 m (pb + 16#64)
    let aLo16 := packWords128 fun i => (BitVec.extractLsb' (i.val * 8) 8 (BitVec.extractLsb' 0 64 a128)).zeroExtend 16
    let aHi16 := packWords128 fun i => (BitVec.extractLsb' (i.val * 8) 8 (BitVec.extractLsb' 0 64 (psrldq128 a128 8#8))).zeroExtend 16
    let loLo := pmullw128 aLo16 bLo
    let hiLo := pmulhuw128 aLo16 bLo
    let sLo  := packDwords128 fun i => getDword128 (unpack128 .hwd loLo hiLo) i + getDword128 (unpack128 .lwd loLo hiLo) i
    let sLoA := packDwords128 fun i => getDword128 sLo i + getDword128 accV i
    let loHi := pmullw128 aHi16 bHi
    let hiHi := pmulhuw128 aHi16 bHi
    let sHi  := packDwords128 fun i => getDword128 (unpack128 .hwd loHi hiHi) i + getDword128 (unpack128 .lwd loHi hiHi) i
    let sAll := packDwords128 fun i => getDword128 sLoA i + getDword128 sHi i
    sumDwords128 sAll = rustDotU8U16From m pa pb 16 (sumDwords128 accV) := by
  dsimp only
  rw [sumDwords128_paddd, sumDwords128_paddd, sumDwords128_paddd, sumDwords128_paddd]
  rw [sumDwords128_unpack_mul_pair, sumDwords128_unpack_mul_pair]
  rw [show rustDotU8U16From m pa pb 16 (sumDwords128 accV) = rustDotU8U16From m pa pb (8 + 8) (sumDwords128 accV) from rfl,
      rustDotU8U16From_split, rustDotU8U16From_8, rustDotU8U16From_8]
  have hlo : ∀ i : Fin 8,
      (getWord128 (packWords128 fun j => (BitVec.extractLsb' (j.val * 8) 8 (BitVec.extractLsb' 0 64 (readMem128 m pa))).zeroExtend 16) i).zeroExtend 32 *
        (getWord128 (readMem128 m pb) i).zeroExtend 32 =
      (m (pa + BitVec.ofNat 64 i.val)).zeroExtend 32 * (readMem16 m (pb + BitVec.ofNat 64 (2 * i.val))).zeroExtend 32 := by
    intro i; rw [getWord128_packWords128, zext8_16_32_eq, readMem128_word_at]
    have hb : BitVec.extractLsb' (i.val * 8) 8 (BitVec.extractLsb' 0 64 (readMem128 m pa)) =
        getByte128 (readMem128 m pa) ⟨i.val, by omega⟩ := by
      unfold getByte128; apply BitVec.eq_of_getLsbD_eq; intro b hb; simp [show i.val * 8 + b < 64 by omega]
    rw [hb, readMem128_byte_at]
  have hhi : ∀ i : Fin 8,
      (getWord128 (packWords128 fun j => (BitVec.extractLsb' (j.val * 8) 8 (BitVec.extractLsb' 0 64 (psrldq128 (readMem128 m pa) 8#8))).zeroExtend 16) i).zeroExtend 32 *
        (getWord128 (readMem128 m (pb + 16#64)) i).zeroExtend 32 =
      (m ((pa + 8#64) + BitVec.ofNat 64 i.val)).zeroExtend 32 * (readMem16 m ((pb + 16#64) + BitVec.ofNat 64 (2 * i.val))).zeroExtend 32 := by
    intro i; rw [getWord128_packWords128, zext8_16_32_eq, readMem128_word_at]
    have hb : BitVec.extractLsb' (i.val * 8) 8 (BitVec.extractLsb' 0 64 (psrldq128 (readMem128 m pa) 8#8)) =
        getByte128 (psrldq128 (readMem128 m pa) 8#8) ⟨i.val, by omega⟩ := by
      unfold getByte128; apply BitVec.eq_of_getLsbD_eq; intro b hb; simp [show i.val * 8 + b < 64 by omega]
    rw [hb, getByte128_psrldq8, readMem128_byte_at]
    have ha : pa + BitVec.ofNat 64 (8 + i.val) = (pa + 8#64) + BitVec.ofNat 64 i.val :=
      (bv64_add_ofNat_assoc pa 8 i.val).symm
    rw [ha]
  rw [hlo ⟨0, by decide⟩, hlo ⟨1, by decide⟩, hlo ⟨2, by decide⟩, hlo ⟨3, by decide⟩,
      hlo ⟨4, by decide⟩, hlo ⟨5, by decide⟩, hlo ⟨6, by decide⟩, hlo ⟨7, by decide⟩]
  rw [hhi ⟨0, by decide⟩, hhi ⟨1, by decide⟩, hhi ⟨2, by decide⟩, hhi ⟨3, by decide⟩,
      hhi ⟨4, by decide⟩, hhi ⟨5, by decide⟩, hhi ⟨6, by decide⟩, hhi ⟨7, by decide⟩]
  dsimp only
  rw [BitVec.add_comm (n := 32) (_ + _ + _ + _ + _ + _ + _ + _) (sumDwords128 accV)]

private theorem dotO3_epi16_stepA (s : X64State) (aPtr bPtr : BitVec 64) (done idx : Nat) (nd : Nat → UndefChoice)
    (hshl : BitVec.ofNat 64 done <<< 1 = BitVec.ofNat 64 (2 * done))
    (hrun : s.halted = false) (hnf : s.fault = false) (hrip : s.rip = 0x400225#64)
    (hrdi : s.regs .rdi = aPtr) (hrsi : s.regs .rsi = bPtr) (hr9 : s.regs .r9 = BitVec.ofNat 64 done) :
    let a128 := readMem128 s.mem (aPtr + BitVec.ofNat 64 done)
    let bLo  := readMem128 s.mem (bPtr + BitVec.ofNat 64 (2 * done))
    let bHi  := readMem128 s.mem ((bPtr + BitVec.ofNat 64 (2 * done)) + 16#64)
    let aLo16 := packWords128 fun i => (BitVec.extractLsb' (i.val * 8) 8 (BitVec.extractLsb' 0 64 a128)).zeroExtend 16
    let sA := runFrom dotO3Cmap 8 idx nd s
    sA.halted = false ∧ sA.fault = false ∧ sA.rip = 0x40024a#64 ∧ sA.mem = s.mem ∧
    sA.regs = regUpd s.regs .rax (bPtr + BitVec.ofNat 64 (2 * done)) ∧
    BitVec.extractLsb' 0 128 (sA.ymms y0) = pmullw128 aLo16 bLo ∧
    BitVec.extractLsb' 0 128 (sA.ymms y1) = psrldq128 a128 8#8 ∧
    BitVec.extractLsb' 0 128 (sA.ymms y2) = BitVec.extractLsb' 0 128 (s.ymms y2) ∧
    BitVec.extractLsb' 0 128 (sA.ymms y3) = pmulhuw128 aLo16 bLo ∧
    BitVec.extractLsb' 0 128 (sA.ymms y4) = bHi ∧
    (AllUpperYmmClean s → AllUpperYmmClean sA) := by
  dsimp only
  have hlo64_wx : ∀ (ym : YmmIdx → BitVec 256) (r : YmmIdx) (v : BitVec 128),
      BitVec.extractLsb' 0 64 (writeXmm128 true ym r v r) = BitVec.extractLsb' 0 64 v := fun ym r v => by
    rw [writeXmm128_true_eq, ymmUpd_eq]; apply BitVec.eq_of_getLsbD_eq; intro b hb
    rw [BitVec.getLsbD_extractLsb', BitVec.getLsbD_extractLsb', BitVec.getLsbD_append]
    simp [show b < 128 by omega]
  let a128 := readMem128 s.mem (aPtr + BitVec.ofNat 64 done)
  let bLo  := readMem128 s.mem (bPtr + BitVec.ofNat 64 (2 * done))
  let bHi  := readMem128 s.mem ((bPtr + BitVec.ofNat 64 (2 * done)) + 16#64)
  let aLo16 := packWords128 fun i => (BitVec.extractLsb' (i.val * 8) 8 (BitVec.extractLsb' 0 64 a128)).zeroExtend 16
  let aSh  := psrldq128 a128 8#8
  let r1  := regUpd s.regs .rax (bPtr + BitVec.ofNat 64 (2 * done))
  let y1s := writeXmm128 true s.ymms y1 a128
  let y2s := writeXmm128 true y1s y5 bLo
  let y3s := writeXmm128 true y2s y4 bHi
  let y4s := writeXmm128 true y3s y3 aLo16
  let y5s := writeXmm128 true y4s y1 aSh
  let y6s := writeXmm128 true y5s y0 (pmullw128 aLo16 bLo)
  let y7s := writeXmm128 true y6s y3 (pmulhuw128 aLo16 bLo)
  rcases runFrom_of_decodeSeqAt dotO3_epi16A_dec idx nd s hrun hnf hrip with ⟨hseq, _, _⟩
  have he : runFrom dotO3Cmap 8 idx nd s = { s with rip := 0x40024a#64, regs := r1, ymms := y7s } := by
    rw [hseq]; dsimp only [dotO3_epi16ASeq]
    rw [execInstrSeq_succ_cons, exec_lea_s64, evalByteAddr_base_idx1, hrsi, hr9, hshl]
    change execInstrSeq 7 _ _ _ { s with rip := 0x400229#64, regs := r1 } = _
    rw [execInstrSeq_succ_cons, exec_simdMovLoad_vex128_mem, evalByteAddr_base_idx0]
    dsimp only [r1]; rw [regUpd_ne _ (by decide), regUpd_ne _ (by decide), hrdi, hr9]
    change execInstrSeq 6 _ _ _ { s with rip := 0x40022f#64, regs := r1, ymms := y1s } = _
    rw [execInstrSeq_succ_cons, exec_simdMovLoad_vex128_mem, evalByteAddr_base]
    dsimp only [r1]; rw [regUpd_eq]
    change execInstrSeq 5 _ _ _ { s with rip := 0x400233#64, regs := r1, ymms := y2s } = _
    rw [execInstrSeq_succ_cons, exec_simdMovLoad_vex128_mem, evalByteAddr_base_disp]
    dsimp only [r1]; rw [regUpd_eq]
    change execInstrSeq 4 _ _ _ { s with rip := 0x400238#64, regs := r1, ymms := y3s } = _
    rw [execInstrSeq_succ_cons, exec_simdExtend_vex128_zxbw_reg]
    dsimp only; rw [show BitVec.extractLsb' 0 64 (y3s y1) = BitVec.extractLsb' 0 64 a128 from by
      dsimp only [y3s, y2s, y1s]; (repeat rw [writeXmm128_ne true _ (by decide)]); exact hlo64_wx _ _ _]
    change execInstrSeq 3 _ _ _ { s with rip := 0x40023d#64, regs := r1, ymms := y4s } = _
    rw [execInstrSeq_succ_cons, exec_simdPsrldq_vex128]
    dsimp only; rw [show BitVec.extractLsb' 0 128 (y4s y1) = a128 from by
      dsimp only [y4s, y3s, y2s, y1s]; (repeat rw [writeXmm128_ne true _ (by decide)]); exact writeXmm128_true_lo _ _ _]
    change execInstrSeq 2 _ _ _ { s with rip := 0x400242#64, regs := r1, ymms := y5s } = _
    rw [execInstrSeq_succ_cons, exec_simdPmullw_vex128_reg]
    dsimp only; rw [show BitVec.extractLsb' 0 128 (y5s y3) = aLo16 from by dsimp only [y5s, y4s]; rw [writeXmm128_ne true _ (by decide : y3 ≠ y1), writeXmm128_true_lo],
                    show BitVec.extractLsb' 0 128 (y5s y5) = bLo from by dsimp only [y5s, y4s, y3s, y2s]; (repeat rw [writeXmm128_ne true _ (by decide)]); exact writeXmm128_true_lo _ _ _]
    change execInstrSeq 1 _ _ _ { s with rip := 0x400246#64, regs := r1, ymms := y6s } = _
    rw [execInstrSeq_succ_cons, exec_simdPmulhuw_vex128_reg, execInstrSeq_zero]
    dsimp only; rw [show BitVec.extractLsb' 0 128 (y6s y3) = aLo16 from by dsimp only [y6s, y5s, y4s]; (repeat rw [writeXmm128_ne true _ (by decide)]); exact writeXmm128_true_lo _ _ _,
                    show BitVec.extractLsb' 0 128 (y6s y5) = bLo from by dsimp only [y6s, y5s, y4s, y3s, y2s]; (repeat rw [writeXmm128_ne true _ (by decide)]); exact writeXmm128_true_lo _ _ _]
  rw [he]; refine ⟨hrun, hnf, rfl, rfl, rfl, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · dsimp only [y7s, y6s]; rw [writeXmm128_ne true _ (by decide : y0 ≠ y3), writeXmm128_true_lo]
  · dsimp only [y7s, y6s, y5s]; (repeat rw [writeXmm128_ne true _ (by decide)]); exact writeXmm128_true_lo _ _ _
  · dsimp only [y7s, y6s, y5s, y4s, y3s, y2s, y1s]; repeat rw [writeXmm128_ne true _ (by decide)]
  · exact writeXmm128_true_lo _ _ _
  · dsimp only [y7s, y6s, y5s, y4s, y3s]; (repeat rw [writeXmm128_ne true _ (by decide)]); exact writeXmm128_true_lo _ _ _
  · intro hc; exact writeXmm128_true_preserves_clean _ _ _ (writeXmm128_true_preserves_clean _ _ _
      (writeXmm128_true_preserves_clean _ _ _ (writeXmm128_true_preserves_clean _ _ _
        (writeXmm128_true_preserves_clean _ _ _ (writeXmm128_true_preserves_clean _ _ _
          (writeXmm128_true_preserves_clean _ _ _ hc))))))

private theorem dotO3_epi16_stepB (sA : X64State) (loLo aSh accV hiLo bHi : BitVec 128) (idx : Nat) (nd : Nat → UndefChoice)
    (hrun : sA.halted = false) (hnf : sA.fault = false) (hrip : sA.rip = 0x40024a#64)
    (hy0 : BitVec.extractLsb' 0 128 (sA.ymms y0) = loLo) (hy1 : BitVec.extractLsb' 0 128 (sA.ymms y1) = aSh)
    (hy2 : BitVec.extractLsb' 0 128 (sA.ymms y2) = accV) (hy3 : BitVec.extractLsb' 0 128 (sA.ymms y3) = hiLo)
    (hy4 : BitVec.extractLsb' 0 128 (sA.ymms y4) = bHi) :
    let aHi16 := packWords128 fun i => (BitVec.extractLsb' (i.val * 8) 8 (BitVec.extractLsb' 0 64 aSh)).zeroExtend 16
    let sLo := packDwords128 fun i => getDword128 (unpack128 .hwd loLo hiLo) i + getDword128 (unpack128 .lwd loLo hiLo) i
    let sLoA := packDwords128 fun i => getDword128 sLo i + getDword128 accV i
    let loHi := pmullw128 aHi16 bHi
    let hiHi := pmulhuw128 aHi16 bHi
    let sB := runFrom dotO3Cmap 8 idx nd sA
    sB.halted = false ∧ sB.fault = false ∧ sB.rip = 0x40026b#64 ∧ sB.mem = sA.mem ∧ sB.regs = sA.regs ∧
    BitVec.extractLsb' 0 128 (sB.ymms y0) = sLoA ∧
    BitVec.extractLsb' 0 128 (sB.ymms y1) = hiHi ∧
    BitVec.extractLsb' 0 128 (sB.ymms y2) = loHi ∧
    BitVec.extractLsb' 0 128 (sB.ymms y3) = unpack128 .lwd loHi hiHi ∧
    (AllUpperYmmClean sA → AllUpperYmmClean sB) := by
  dsimp only
  have hlo64_of_lo128 : ∀ {x : BitVec 256} {v : BitVec 128}, BitVec.extractLsb' 0 128 x = v →
      BitVec.extractLsb' 0 64 x = BitVec.extractLsb' 0 64 v := fun {x v} h => by
    rw [← h]; apply BitVec.eq_of_getLsbD_eq; intro b _hb; simp
  let aHi16 := packWords128 fun i => (BitVec.extractLsb' (i.val * 8) 8 (BitVec.extractLsb' 0 64 aSh)).zeroExtend 16
  let sLoL := unpack128 .lwd loLo hiLo
  let sLoH := unpack128 .hwd loLo hiLo
  let sLo  := packDwords128 fun i => getDword128 sLoH i + getDword128 sLoL i
  let sLoA := packDwords128 fun i => getDword128 sLo i + getDword128 accV i
  let loHi := pmullw128 aHi16 bHi
  let hiHi := pmulhuw128 aHi16 bHi
  let y1s := writeXmm128 true sA.ymms y1 aHi16
  let y2s := writeXmm128 true y1s y5 sLoL
  let y3s := writeXmm128 true y2s y0 sLoH
  let y4s := writeXmm128 true y3s y0 sLo
  let y5s := writeXmm128 true y4s y0 sLoA
  let y6s := writeXmm128 true y5s y2 loHi
  let y7s := writeXmm128 true y6s y1 hiHi
  let y8s := writeXmm128 true y7s y3 (unpack128 .lwd loHi hiHi)
  rcases runFrom_of_decodeSeqAt dotO3_epi16B_dec idx nd sA hrun hnf hrip with ⟨hseq, _, _⟩
  have he : runFrom dotO3Cmap 8 idx nd sA = { sA with rip := 0x40026b#64, ymms := y8s } := by
    rw [hseq]; dsimp only [dotO3_epi16BSeq]
    rw [execInstrSeq_succ_cons, exec_simdExtend_vex128_zxbw_reg, hlo64_of_lo128 hy1]
    change execInstrSeq 7 _ _ _ { sA with rip := 0x40024f#64, ymms := y1s } = _
    rw [execInstrSeq_succ_cons, exec_simdUnpack_vex128_reg]
    dsimp only; rw [show BitVec.extractLsb' 0 128 (y1s y0) = loLo from by dsimp only [y1s]; rw [writeXmm128_ne true _ (by decide : y0 ≠ y1), hy0],
                    show BitVec.extractLsb' 0 128 (y1s y3) = hiLo from by dsimp only [y1s]; rw [writeXmm128_ne true _ (by decide : y3 ≠ y1), hy3]]
    change execInstrSeq 6 _ _ _ { sA with rip := 0x400253#64, ymms := y2s } = _
    rw [execInstrSeq_succ_cons, exec_simdUnpack_vex128_reg]
    dsimp only; rw [show BitVec.extractLsb' 0 128 (y2s y0) = loLo from by dsimp only [y2s, y1s]; (repeat rw [writeXmm128_ne true _ (by decide)]); exact hy0,
                    show BitVec.extractLsb' 0 128 (y2s y3) = hiLo from by dsimp only [y2s, y1s]; (repeat rw [writeXmm128_ne true _ (by decide)]); exact hy3]
    change execInstrSeq 5 _ _ _ { sA with rip := 0x400257#64, ymms := y3s } = _
    rw [execInstrSeq_succ_cons, exec_simdAdd_vex128_e32_reg]
    dsimp only; rw [show BitVec.extractLsb' 0 128 (y3s y0) = sLoH from writeXmm128_true_lo _ _ _,
                    show BitVec.extractLsb' 0 128 (y3s y5) = sLoL from by dsimp only [y3s, y2s]; rw [writeXmm128_ne true _ (by decide : y5 ≠ y0), writeXmm128_true_lo]]
    change execInstrSeq 4 _ _ _ { sA with rip := 0x40025b#64, ymms := y4s } = _
    rw [execInstrSeq_succ_cons, exec_simdAdd_vex128_e32_reg]
    dsimp only; rw [show BitVec.extractLsb' 0 128 (y4s y0) = sLo from writeXmm128_true_lo _ _ _,
                    show BitVec.extractLsb' 0 128 (y4s y2) = accV from by dsimp only [y4s, y3s, y2s, y1s]; (repeat rw [writeXmm128_ne true _ (by decide)]); exact hy2]
    change execInstrSeq 3 _ _ _ { sA with rip := 0x40025f#64, ymms := y5s } = _
    rw [execInstrSeq_succ_cons, exec_simdPmullw_vex128_reg]
    dsimp only; rw [show BitVec.extractLsb' 0 128 (y5s y1) = aHi16 from by dsimp only [y5s, y4s, y3s, y2s]; (repeat rw [writeXmm128_ne true _ (by decide)]); exact writeXmm128_true_lo _ _ _,
                    show BitVec.extractLsb' 0 128 (y5s y4) = bHi from by dsimp only [y5s, y4s, y3s, y2s, y1s]; (repeat rw [writeXmm128_ne true _ (by decide)]); exact hy4]
    change execInstrSeq 2 _ _ _ { sA with rip := 0x400263#64, ymms := y6s } = _
    rw [execInstrSeq_succ_cons, exec_simdPmulhuw_vex128_reg]
    dsimp only; rw [show BitVec.extractLsb' 0 128 (y6s y1) = aHi16 from by dsimp only [y6s, y5s, y4s, y3s, y2s]; (repeat rw [writeXmm128_ne true _ (by decide)]); exact writeXmm128_true_lo _ _ _,
                    show BitVec.extractLsb' 0 128 (y6s y4) = bHi from by dsimp only [y6s, y5s, y4s, y3s, y2s, y1s]; (repeat rw [writeXmm128_ne true _ (by decide)]); exact hy4]
    change execInstrSeq 1 _ _ _ { sA with rip := 0x400267#64, ymms := y7s } = _
    rw [execInstrSeq_succ_cons, exec_simdUnpack_vex128_reg, execInstrSeq_zero]
    dsimp only; rw [show BitVec.extractLsb' 0 128 (y7s y2) = loHi from by dsimp only [y7s, y6s]; rw [writeXmm128_ne true _ (by decide : y2 ≠ y1), writeXmm128_true_lo],
                    show BitVec.extractLsb' 0 128 (y7s y1) = hiHi from writeXmm128_true_lo _ _ _]
  rw [he]; refine ⟨hrun, hnf, rfl, rfl, rfl, ?_, ?_, ?_, ?_, ?_⟩
  · dsimp only [y8s, y7s, y6s, y5s]; (repeat rw [writeXmm128_ne true _ (by decide)]); exact writeXmm128_true_lo _ _ _
  · dsimp only [y8s, y7s]; rw [writeXmm128_ne true _ (by decide : y1 ≠ y3), writeXmm128_true_lo]
  · dsimp only [y8s, y7s, y6s]; (repeat rw [writeXmm128_ne true _ (by decide)]); exact writeXmm128_true_lo _ _ _
  · exact writeXmm128_true_lo _ _ _
  · intro hc; exact writeXmm128_true_preserves_clean _ _ _ (writeXmm128_true_preserves_clean _ _ _
      (writeXmm128_true_preserves_clean _ _ _ (writeXmm128_true_preserves_clean _ _ _
        (writeXmm128_true_preserves_clean _ _ _ (writeXmm128_true_preserves_clean _ _ _
          (writeXmm128_true_preserves_clean _ _ _ (writeXmm128_true_preserves_clean _ _ _ hc)))))))

private theorem dotO3_epi16_stepC (sB : X64State) (sLoA hiHi loHi sHiL : BitVec 128) (r8V : BitVec 64)
    (idx : Nat) (nd : Nat → UndefChoice)
    (hrun : sB.halted = false) (hnf : sB.fault = false) (hrip : sB.rip = 0x40026b#64)
    (hr8 : sB.regs .r8 = r8V)
    (hy0 : BitVec.extractLsb' 0 128 (sB.ymms y0) = sLoA) (hy1 : BitVec.extractLsb' 0 128 (sB.ymms y1) = hiHi)
    (hy2 : BitVec.extractLsb' 0 128 (sB.ymms y2) = loHi) (hy3 : BitVec.extractLsb' 0 128 (sB.ymms y3) = sHiL) :
    let sHi  := packDwords128 fun i => getDword128 (unpack128 .hwd loHi hiHi) i + getDword128 sHiL i
    let sAll := packDwords128 fun i => getDword128 sLoA i + getDword128 sHi i
    let sC := runFrom dotO3Cmap 9 idx nd sB
    sC.halted = false ∧ sC.fault = false ∧ sC.rip = 0x400291#64 ∧ sC.mem = sB.mem ∧
    sC.regs = regUpd sB.regs .rax ((sumDwords128 sAll).zeroExtend 64) ∧
    sC.flags = (evalAluN (by decide) .test (BitVec.extractLsb' 0 8 r8V) 0x0f#8 sB.flags (nd (idx + 8)).flags).2 ∧
    BitVec.extractLsb' 0 128 (sC.ymms y0) = sAll ∧
    (AllUpperYmmClean sB → AllUpperYmmClean sC) := by
  dsimp only
  let sHiH := unpack128 .hwd loHi hiHi
  let sHi  := packDwords128 fun i => getDword128 sHiH i + getDword128 sHiL i
  let sAll := packDwords128 fun i => getDword128 sLoA i + getDword128 sHi i
  let v1   := packDwords128 fun i => getDword128 sAll i + getDword128 (psrldq128 sAll 8#8) i
  let v2   := packDwords128 fun i => getDword128 v1 i + getDword128 (psrldq128 v1 4#8) i
  let y1s := writeXmm128 true sB.ymms y2 sHiH
  let y2s := writeXmm128 true y1s y2 sHi
  let y3s := writeXmm128 true y2s y0 sAll
  let y4s := writeXmm128 true y3s y1 (psrldq128 sAll 8#8)
  let y5s := writeXmm128 true y4s y1 v1
  let y6s := writeXmm128 true y5s y2 (psrldq128 v1 4#8)
  let y7s := writeXmm128 true y6s y1 v2
  have hlo32 : BitVec.extractLsb' 0 32 (y7s y1) = sumDwords128 sAll := by
    have hx : BitVec.extractLsb' 0 32 (y7s y1) = BitVec.extractLsb' 0 32 (BitVec.extractLsb' 0 128 (y7s y1)) := by
      apply BitVec.eq_of_getLsbD_eq; intro b _hb; simp
    rw [hx, writeXmm128_true_lo]; exact horiz_reduce_128_eq sAll
  rcases runFrom_of_decodeSeqAt dotO3_epi16C_dec idx nd sB hrun hnf hrip with ⟨hseq, _, _⟩
  have he : runFrom dotO3Cmap 9 idx nd sB =
      { sB with
        rip := 0x400291#64,
        regs := regUpd sB.regs .rax ((sumDwords128 sAll).zeroExtend 64),
        ymms := y7s,
        flags := (evalAluN (by decide) .test (BitVec.extractLsb' 0 8 r8V) 0x0f#8 sB.flags (nd (idx + 8)).flags).2 } := by
    rw [hseq]; dsimp only [dotO3_epi16CSeq]
    rw [execInstrSeq_succ_cons, exec_simdUnpack_vex128_reg, hy2, hy1]
    change execInstrSeq 8 _ _ _ { sB with rip := 0x40026f#64, ymms := y1s } = _
    rw [execInstrSeq_succ_cons, exec_simdAdd_vex128_e32_reg]
    dsimp only; rw [show BitVec.extractLsb' 0 128 (y1s y2) = sHiH from writeXmm128_true_lo _ _ _,
                    show BitVec.extractLsb' 0 128 (y1s y3) = sHiL from by dsimp only [y1s]; rw [writeXmm128_ne true _ (by decide : y3 ≠ y2), hy3]]
    change execInstrSeq 7 _ _ _ { sB with rip := 0x400273#64, ymms := y2s } = _
    rw [execInstrSeq_succ_cons, exec_simdAdd_vex128_e32_reg]
    dsimp only; rw [show BitVec.extractLsb' 0 128 (y2s y0) = sLoA from by dsimp only [y2s, y1s]; (repeat rw [writeXmm128_ne true _ (by decide)]); exact hy0,
                    show BitVec.extractLsb' 0 128 (y2s y2) = sHi from writeXmm128_true_lo _ _ _]
    change execInstrSeq 6 _ _ _ { sB with rip := 0x400277#64, ymms := y3s } = _
    rw [execInstrSeq_succ_cons, exec_simdPsrldq_vex128]
    dsimp only; rw [show BitVec.extractLsb' 0 128 (y3s y0) = sAll from writeXmm128_true_lo _ _ _]
    change execInstrSeq 5 _ _ _ { sB with rip := 0x40027c#64, ymms := y4s } = _
    rw [execInstrSeq_succ_cons, exec_simdAdd_vex128_e32_reg]
    dsimp only; rw [show BitVec.extractLsb' 0 128 (y4s y0) = sAll from by dsimp only [y4s, y3s]; rw [writeXmm128_ne true _ (by decide : y0 ≠ y1), writeXmm128_true_lo],
                    show BitVec.extractLsb' 0 128 (y4s y1) = psrldq128 sAll 8#8 from writeXmm128_true_lo _ _ _]
    change execInstrSeq 4 _ _ _ { sB with rip := 0x400280#64, ymms := y5s } = _
    rw [execInstrSeq_succ_cons, exec_simdPsrldq_vex128]
    dsimp only; rw [show BitVec.extractLsb' 0 128 (y5s y1) = v1 from writeXmm128_true_lo _ _ _]
    change execInstrSeq 3 _ _ _ { sB with rip := 0x400285#64, ymms := y6s } = _
    rw [execInstrSeq_succ_cons, exec_simdAdd_vex128_e32_reg]
    dsimp only; rw [show BitVec.extractLsb' 0 128 (y6s y1) = v1 from by dsimp only [y6s, y5s]; rw [writeXmm128_ne true _ (by decide : y1 ≠ y2), writeXmm128_true_lo],
                    show BitVec.extractLsb' 0 128 (y6s y2) = psrldq128 v1 4#8 from writeXmm128_true_lo _ _ _]
    change execInstrSeq 2 _ _ _ { sB with rip := 0x400289#64, ymms := y7s } = _
    rw [execInstrSeq_succ_cons, exec_simdMovXToGpr_s32_reg]
    dsimp only; rw [hlo32]
    rw [execInstrSeq_succ_cons, exec_alu8Imm_test_lo8, execInstrSeq_zero]
    dsimp only; rw [regUpd_ne _ (by decide), hr8]
  rw [he]; refine ⟨hrun, hnf, rfl, rfl, rfl, rfl, ?_, ?_⟩
  · dsimp only [y7s, y6s, y5s, y4s, y3s]; (repeat rw [writeXmm128_ne true _ (by decide)]); exact writeXmm128_true_lo _ _ _
  · intro hc; exact writeXmm128_true_preserves_clean _ _ _ (writeXmm128_true_preserves_clean _ _ _
      (writeXmm128_true_preserves_clean _ _ _ (writeXmm128_true_preserves_clean _ _ _
        (writeXmm128_true_preserves_clean _ _ _ (writeXmm128_true_preserves_clean _ _ _
          (writeXmm128_true_preserves_clean _ _ _ hc))))))

theorem dotO3_epi16_0x211 (s0 s : X64State) (done idx : Nat) (nd : Nat → UndefChoice)
    (hpre : DotU8U16Pre 0 s0)
    (hrun : s.halted = false) (hnf : s.fault = false) (hrip : s.rip = 0x400211#64) (hmem : s.mem = s0.mem)
    (hrdi : s.regs .rdi = s0.regs .rdi) (hrsi : s.regs .rsi = s0.regs .rsi) (hrdx : s.regs .rdx = s0.regs .rdx)
    (hr9 : s.regs .r9 = BitVec.ofNat 64 done)
    (hrax : BitVec.extractLsb' 0 32 (s.regs .rax) =
      rustDotU8U16From s0.mem (s0.regs .rdi) (s0.regs .rsi) done 0#32)
    (hy2 : sumDwords128 (BitVec.extractLsb' 0 128 (s.ymms y2)) =
      rustDotU8U16From s0.mem (s0.regs .rdi) (s0.regs .rsi) done 0#32)
    (hcs : SysVCalleeSavedPreserved s0 s) (hymm : UpperYmmCleanOrPreserved s0 s)
    (hlt : done < (s0.regs .rdx).toNat) (hremHi : (s0.regs .rdx).toNat - done ≤ 31) :
    ∃ steps : Nat,
      let sf := runFrom dotO3Cmap steps idx nd s
      sf.halted = true ∧ sf.fault = false ∧
      SysVCalleeSavedPreserved s0 sf ∧ UpperYmmCleanOrPreserved s0 sf ∧
      DotU8U16Post 0 s0 sf := by
  have h2len := hpre.1; have hlenLt := (s0.regs .rdx).isLt
  have hsub8 : s0.regs .rdx - BitVec.ofNat 64 done = BitVec.ofNat 64 ((s0.regs .rdx).toNat - done) := by
    apply BitVec.eq_of_toNat_eq
    have hdtn : (BitVec.ofNat 64 done).toNat = done := by rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)]
    rw [bv64_sub_toNat_of_le (by rw [hdtn]; omega), hdtn, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)]
  let remBv : BitVec 64 := BitVec.ofNat 64 ((s0.regs .rdx).toNat - done)
  have hremTn : remBv.toNat = (s0.regs .rdx).toNat - done := by
    dsimp only [remBv]; rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)]
  rcases runFrom_of_decodeSeqAt dotO3_epi16Chk_dec idx nd s hrun hnf hrip with ⟨hchk, hrun1, hnf1⟩
  have heChk : execInstrSeq 4 dotO3_epi16ChkSeq idx nd s =
      { s with
        rip := 0x40021f#64,
        regs := regUpd (regUpd (regUpd s.regs .r8 (s0.regs .rdx)) .r8 remBv) .rcx (remBv + 0xffffffffffffffff#64),
        flags := (evalAluN (by decide) .cmp (remBv + 0xffffffffffffffff#64) 0x0e#64
                   (evalAluN (by decide) .sub (s0.regs .rdx) (BitVec.ofNat 64 done) s.flags (nd (idx + 1)).flags).2
                   (nd (idx + 3)).flags).2 } := by
    dsimp only [dotO3_epi16ChkSeq]
    rw [execInstrSeq_succ_cons, exec_movStore_s64_reg, hrdx]
    rw [execInstrSeq_succ_cons, exec_aluRmReg_s64_sub]
    dsimp only; rw [regUpd_eq, regUpd_ne _ (by decide), hr9, hsub8]
    rw [execInstrSeq_succ_cons, exec_lea_s64, evalByteAddr_base_disp]
    dsimp only; rw [regUpd_eq]
    rw [execInstrSeq_succ_cons, exec_aluImm_s64_cmp, execInstrSeq_zero]
    dsimp only; rw [regUpd_eq]
  have hbe15 := bv64_sub1_cmp_be remBv 14 (by rw [hremTn]; omega) (by decide)
  rw [hremTn] at hbe15
  by_cases hle15 : (s0.regs .rdx).toNat - done ≤ 15
  · have hcc15 : evalCond .be (execInstrSeq 4 dotO3_epi16ChkSeq idx nd s).flags = true := by
      rw [heChk]; dsimp only; rw [evalCond_be_of_flags, cmp_flags_cf, cmp_flags_zf]
      change (decide ((remBv + 0xffffffffffffffff#64).toNat < 14) || ((remBv + 0xffffffffffffffff#64) - BitVec.ofNat 64 14 == 0#64)) = true
      rw [hbe15]; simp [hle15]
    let s1 := runFrom dotO3Cmap 5 idx nd s
    have hs1 : s1 = { execInstrSeq 4 dotO3_epi16ChkSeq idx nd s with rip := 0x400441#64 } := by
      dsimp only [s1]; rw [show (5 : Nat) = 4 + 1 by rfl, runFrom_add, hchk, runFrom_succ,
        step_at_concrete dotO3_epi16Chk_jbe _ _ hrun1 hnf1 (by rw [heChk]), exec_jcc_taken hcc15, runFrom_zero]
      rw [heChk]; rfl
    rcases runFrom_of_decodeSeqAt dotO3_skip16_dec (idx + 5) nd s1
      (by rw [hs1, heChk]; exact hrun) (by rw [hs1, heChk]; exact hnf) (by rw [hs1]) with ⟨hsk, hrun2, hnf2⟩
    have h1ax : BitVec.extractLsb' 0 32 (s1.regs .rax) = rustDotU8U16From s0.mem (s0.regs .rdi) (s0.regs .rsi) done 0#32 := by
      rw [hs1, heChk]; dsimp only; (repeat rw [regUpd_ne _ (by decide)]); exact hrax
    have h1r9 : s1.regs .r9 = BitVec.ofNat 64 done := by
      rw [hs1, heChk]; dsimp only; (repeat rw [regUpd_ne _ (by decide)]); exact hr9
    have heSk : execInstrSeq 3 dotO3_skip16Seq (idx + 5) nd s1 =
        { s1 with
          rip := 0x40044b#64,
          regs := regUpd (regUpd s1.regs .rcx (BitVec.ofNat 64 done)) .r10 0#64,
          ymms := writeXmm128 true s1.ymms y5 (((rustDotU8U16From s0.mem (s0.regs .rdi) (s0.regs .rsi) done 0#32).zeroExtend 64).zeroExtend 128),
          flags := (evalAluN (by decide) .xor (BitVec.extractLsb' 0 32 (s1.regs .r10)) (BitVec.extractLsb' 0 32 (s1.regs .r10)) s1.flags (nd (idx + 7)).flags).2 } := by
      dsimp only [dotO3_skip16Seq]
      rw [execInstrSeq_succ_cons, exec_simdMovGprToX_vex32_reg, h1ax]
      rw [execInstrSeq_succ_cons, exec_movStore_s64_reg, h1r9]
      rw [execInstrSeq_succ_cons, exec_aluRmReg_s32_xor_self, execInstrSeq_zero]
      dsimp only; rw [regUpd_ne _ (by decide)]
    let s2 := runFrom dotO3Cmap 4 (idx + 5) nd s1
    have hs2 : s2 = { execInstrSeq 3 dotO3_skip16Seq (idx + 5) nd s1 with rip := 0x4002af#64 } := by
      dsimp only [s2]; rw [show (4 : Nat) = 3 + 1 by rfl, runFrom_add, hsk, runFrom_succ,
        step_at_concrete dotO3_skip16_jmp _ _ hrun2 hnf2 (by rw [heSk]), exec_jmp, runFrom_zero]
      rw [heSk]; rfl
    have hcs2 : SysVCalleeSavedPreserved s0 s2 := by
      unfold SysVCalleeSavedPreserved at hcs ⊢; rw [hs2, heSk, hs1, heChk]; dsimp only
      exact cs_step_caller (r := .r10) rfl (cs_step_caller (r := .rcx) rfl
        (cs_step_caller (r := .rcx) rfl (cs_step_caller (r := .r8) rfl (cs_step_caller (r := .r8) rfl hcs))))
    have hE8 := dotO3_epi8_0x2af s0 s2 done 0 (idx + 9) nd hpre
      (by rw [hs2, heSk, hs1, heChk]; exact hrun) (by rw [hs2, heSk, hs1, heChk]; exact hnf) (by rw [hs2])
      (by rw [hs2, heSk, hs1, heChk]; exact hmem)
      (by rw [hs2, heSk, hs1, heChk]; dsimp only; (repeat rw [regUpd_ne _ (by decide)]); exact hrdi)
      (by rw [hs2, heSk, hs1, heChk]; dsimp only; (repeat rw [regUpd_ne _ (by decide)]); exact hrsi)
      (by rw [hs2, heSk, hs1, heChk]; dsimp only; (repeat rw [regUpd_ne _ (by decide)]); exact hrdx)
      (by rw [hs2, heSk, hs1, heChk]; dsimp only; (repeat rw [regUpd_ne _ (by decide)]); exact hr9)
      (by rw [hs2, heSk]; dsimp only; exact regUpd_eq _ _ _)
      (by rw [hs2, heSk]; dsimp only; rw [regUpd_ne _ (by decide), regUpd_eq, Nat.add_zero])
      (by rw [hs2, heSk, hs1, heChk]; dsimp only; rw [regUpd_ne _ (by decide), regUpd_ne _ (by decide), regUpd_ne _ (by decide), regUpd_eq])
      (by rw [hs2, heSk]; dsimp only; rw [regUpd_ne _ (by decide), regUpd_ne _ (by decide), h1ax, Nat.add_zero])
      (by rw [hs2, heSk]; dsimp only; rw [writeXmm128_true_lo, sumLo2Dwords128_zext32, Nat.add_zero])
      hcs2 (fun hc => by rw [hs2, heSk]; exact writeXmm128_true_preserves_clean _ _ _ (by rw [hs1, heChk]; exact hymm hc))
      (by omega) (by omega)
    rcases hE8 with ⟨k, hk⟩
    exact ⟨9 + k, by rw [show 9 + k = 5 + (4 + k) by omega, runFrom_add, runFrom_add]; simpa [Nat.add_assoc] using hk⟩
  · have hcc15 : evalCond .be (execInstrSeq 4 dotO3_epi16ChkSeq idx nd s).flags = false := by
      rw [heChk]; dsimp only; rw [evalCond_be_of_flags, cmp_flags_cf, cmp_flags_zf]
      change (decide ((remBv + 0xffffffffffffffff#64).toNat < 14) || ((remBv + 0xffffffffffffffff#64) - BitVec.ofNat 64 14 == 0#64)) = false
      rw [hbe15]; simp [hle15]
    let s1 := runFrom dotO3Cmap 5 idx nd s
    have hs1 : s1 = { execInstrSeq 4 dotO3_epi16ChkSeq idx nd s with rip := 0x400225#64 } := by
      dsimp only [s1]; rw [show (5 : Nat) = 4 + 1 by rfl, runFrom_add, hchk, runFrom_succ,
        step_at_concrete dotO3_epi16Chk_jbe _ _ hrun1 hnf1 (by rw [heChk]), exec_jcc_fall hcc15, runFrom_zero]
      rw [heChk]; rfl
    have hshlDone : BitVec.ofNat 64 done <<< 1 = BitVec.ofNat 64 (2 * done) := by
      have htn : (BitVec.ofNat 64 done).toNat = done := by rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)]
      rw [bv64_shl1_toNat (by rw [htn]; omega), htn]
    have hA := dotO3_epi16_stepA s1 (s0.regs .rdi) (s0.regs .rsi) done (idx + 5) nd hshlDone
      (by rw [hs1, heChk]; exact hrun) (by rw [hs1, heChk]; exact hnf) (by rw [hs1])
      (by rw [hs1, heChk]; dsimp only; (repeat rw [regUpd_ne _ (by decide)]); exact hrdi)
      (by rw [hs1, heChk]; dsimp only; (repeat rw [regUpd_ne _ (by decide)]); exact hrsi)
      (by rw [hs1, heChk]; dsimp only; (repeat rw [regUpd_ne _ (by decide)]); exact hr9)
    generalize hsA : runFrom dotO3Cmap 8 (idx + 5) nd s1 = sA at hA
    rcases hA with ⟨hAr, hAf, hArip, hAm, hAregs, hAy0, hAy1, hAy2, hAy3, hAy4, hAym⟩
    have hB := dotO3_epi16_stepB sA _ _ (BitVec.extractLsb' 0 128 (s.ymms y2)) _ _ (idx + 13) nd
      hAr hAf hArip hAy0 hAy1 (by rw [hAy2, hs1, heChk]) hAy3 hAy4
    generalize hsB : runFrom dotO3Cmap 8 (idx + 13) nd sA = sB at hB
    rcases hB with ⟨hBr, hBf, hBrip, hBm, hBregs, hBy0, hBy1, hBy2, hBy3, hBym⟩
    have hBr8 : sB.regs .r8 = remBv := by
      rw [hBregs, hAregs, regUpd_ne _ (by decide), hs1, heChk]; dsimp only; rw [regUpd_ne _ (by decide), regUpd_eq]
    have hC := dotO3_epi16_stepC sB _ _ _ _ remBv (idx + 21) nd hBr hBf hBrip hBr8 hBy0 hBy1 hBy2 hBy3
    generalize hsC : runFrom dotO3Cmap 9 (idx + 21) nd sB = sC at hC
    rcases hC with ⟨hCr, hCf, hCrip, hCm, hCregs, hCfl, hCy0, hCym⟩
    have hCm0 : sC.mem = s0.mem := by rw [hCm, hBm, hAm, hs1, heChk]; exact hmem
    have hCym0 : UpperYmmCleanOrPreserved s0 sC := fun hc => hCym (hBym (hAym (by rw [hs1, heChk]; exact hymm hc)))
    have hCsum : sumDwords128 (BitVec.extractLsb' 0 128 (sC.ymms y0)) =
        rustDotU8U16From s0.mem (s0.regs .rdi) (s0.regs .rsi) (done + 16) 0#32 := by
      rw [hCy0]; have hs1m : s1.mem = s0.mem := by rw [hs1, heChk]; exact hmem
      rw [hs1m, dot16_vex128_algebra, hy2, ← rustDotU8U16From_split]
    have hCax : BitVec.extractLsb' 0 32 (sC.regs .rax) =
        rustDotU8U16From s0.mem (s0.regs .rdi) (s0.regs .rsi) (done + 16) 0#32 := by
      rw [hCregs, regUpd_eq, zext32_extract32_eq, ← hCy0, hCsum]
    have hCcs : SysVCalleeSavedPreserved s0 sC := by
      unfold SysVCalleeSavedPreserved at hcs ⊢
      rw [hCregs, hBregs, hAregs, hs1, heChk]; dsimp only
      exact cs_step_caller (r := .rax) rfl (cs_step_caller (r := .rax) rfl
        (cs_step_caller (r := .rcx) rfl (cs_step_caller (r := .r8) rfl (cs_step_caller (r := .r8) rfl hcs))))
    have hrunC : runFrom dotO3Cmap 30 idx nd s = sC := by
      rw [show (30 : Nat) = 5 + (8 + (8 + 9)) by rfl, runFrom_add, runFrom_add, hsA,
          show idx + 5 + 8 = idx + 13 by omega, runFrom_add, hsB,
          show idx + 13 + 8 = idx + 21 by omega, hsC]
    have htest15 := bv64_test_lo8_15_eq remBv
    rw [hremTn] at htest15
    by_cases hmod16 : ((s0.regs .rdx).toNat - done) % 16 = 0
    · have hcc16 : evalCond .e sC.flags = true := by
        rw [hCfl]; exact evalCond_e_of_zf_true (by rw [test_flags_zf, htest15]; simp [hmod16])
      have hlen16 : done + 16 = (s0.regs .rdx).toNat := by omega
      rw [hlen16] at hCax
      let sD := runFrom dotO3Cmap 1 (idx + 30) nd sC
      have hsD : sD = { sC with rip := 0x400426#64 } := by
        dsimp only [sD]; rw [runFrom_succ, step_at_concrete dotO3_epi16_je _ sC hCr hCf hCrip, exec_jcc_taken hcc16, runFrom_zero]; rfl
      have hRet := dotO3_ret_at s0 sD 0x400426#64 (idx + 31) nd dotO3_ret426
        (by rw [hsD]; exact hCr) (by rw [hsD]; exact hCf) (by rw [hsD]) (by rw [hsD]; exact hCm0)
        (by rw [hsD]; exact hCax)
        (by unfold SysVCalleeSavedPreserved at hCcs ⊢; rw [hsD]; exact hCcs)
        (by rw [hsD]; exact hCym0)
      refine ⟨32, ?_⟩
      rw [show (32 : Nat) = 30 + (1 + 1) by rfl, runFrom_add, hrunC, runFrom_add]
      exact hRet
    · have hcc16 : evalCond .e sC.flags = false := by
        rw [hCfl]; exact evalCond_e_of_zf_false (by rw [test_flags_zf, htest15]; simp [hmod16])
      let sD := runFrom dotO3Cmap 1 (idx + 30) nd sC
      have hsD : sD = { sC with rip := 0x400297#64 } := by
        dsimp only [sD]; rw [runFrom_succ, step_at_concrete dotO3_epi16_je _ sC hCr hCf hCrip, exec_jcc_fall hcc16, runFrom_zero]; rfl
      rcases runFrom_of_decodeSeqAt dotO3_post16_dec (idx + 31) nd sD
        (by rw [hsD]; exact hCr) (by rw [hsD]; exact hCf) (by rw [hsD]) with ⟨hp16, hrunP, hnfP⟩
      have hmask16 : remBv &&& 0xfffffffffffffff0#64 = BitVec.ofNat 64 16 := by
        apply BitVec.eq_of_toNat_eq; rw [bv64_and_neg16_toNat, hremTn, BitVec.toNat_ofNat]; omega
      let sAllV := BitVec.extractLsb' 0 128 (sC.ymms y0)
      let folded := packDwords128 fun i => getDword128 sAllV i + getDword128 (psrldq128 sAllV 8#8) i
      let yP1 := writeXmm128 true sD.ymms y5 sAllV
      let yP2 := writeXmm128 true yP1 y0 (psrldq128 sAllV 8#8)
      let yP3 := writeXmm128 true yP2 y5 folded
      have hDr8 : sD.regs .r8 = remBv := by rw [hsD, hCregs, regUpd_ne _ (by decide), hBr8]
      have hDr9 : sD.regs .r9 = BitVec.ofNat 64 done := by
        rw [hsD, hCregs, hBregs, hAregs]; (repeat rw [regUpd_ne _ (by decide)]); rw [hs1, heChk]; dsimp only
        (repeat rw [regUpd_ne _ (by decide)]); exact hr9
      have heP16 : execInstrSeq 6 dotO3_post16Seq (idx + 31) nd sD =
          { sD with
            rip := 0x4002af#64,
            regs := regUpd (regUpd (regUpd sD.regs .r10 remBv) .r10 (BitVec.ofNat 64 16)) .rcx (BitVec.ofNat 64 (done + 16)),
            ymms := yP3,
            flags := (evalAluN (by decide) .and remBv 0xfffffffffffffff0#64 sD.flags (nd (idx + 35)).flags).2 } := by
        dsimp only [dotO3_post16Seq]
        have hDy0 : BitVec.extractLsb' 0 128 (sD.ymms y0) = sAllV := by rw [hsD]
        rw [execInstrSeq_succ_cons, exec_simdMovLoad_vex128_reg, hDy0]
        change execInstrSeq 5 _ _ _ { sD with rip := 0x40029b#64, ymms := yP1 } = _
        rw [execInstrSeq_succ_cons, exec_simdPsrldq_vex128]
        dsimp only; rw [show BitVec.extractLsb' 0 128 (yP1 y0) = sAllV from by dsimp only [yP1]; rw [writeXmm128_ne true _ (by decide : y0 ≠ y5), hDy0]]
        change execInstrSeq 4 _ _ _ { sD with rip := 0x4002a0#64, ymms := yP2 } = _
        rw [execInstrSeq_succ_cons, exec_movStore_s64_reg, hDr8]
        rw [execInstrSeq_succ_cons, exec_simdAdd_vex128_e32_reg]
        dsimp only; rw [show BitVec.extractLsb' 0 128 (yP2 y5) = sAllV from by dsimp only [yP2, yP1]; rw [writeXmm128_ne true _ (by decide : y5 ≠ y0), writeXmm128_true_lo],
                        show BitVec.extractLsb' 0 128 (yP2 y0) = psrldq128 sAllV 8#8 from writeXmm128_true_lo _ _ _]
        rw [execInstrSeq_succ_cons, exec_aluImm_s64_and]
        dsimp only; rw [regUpd_eq, hmask16]
        rw [execInstrSeq_succ_cons, exec_lea_s64, evalByteAddr_base_idx0, execInstrSeq_zero]
        dsimp only; rw [regUpd_ne _ (by decide), regUpd_ne _ (by decide), regUpd_eq, hDr9, bv64_ofNat_add]
      let sE := runFrom dotO3Cmap 6 (idx + 31) nd sD
      have hsE : sE = execInstrSeq 6 dotO3_post16Seq (idx + 31) nd sD := hp16
      have hEcs : SysVCalleeSavedPreserved s0 sE := by
        unfold SysVCalleeSavedPreserved at hCcs ⊢; rw [hsE, heP16, hsD]; dsimp only
        exact cs_step_caller (r := .rcx) rfl (cs_step_caller (r := .r10) rfl (cs_step_caller (r := .r10) rfl hCcs))
      have hEym : UpperYmmCleanOrPreserved s0 sE := fun hc => by
        rw [hsE, heP16]; exact writeXmm128_true_preserves_clean _ _ _ (writeXmm128_true_preserves_clean _ _ _
          (writeXmm128_true_preserves_clean _ _ _ (by rw [hsD]; exact hCym0 hc)))
      have hE8 := dotO3_epi8_0x2af s0 sE done 16 (idx + 37) nd hpre
        (by rw [hsE]; exact hrunP) (by rw [hsE]; exact hnfP) (by rw [hsE, heP16]) (by rw [hsE, heP16, hsD]; exact hCm0)
        (by rw [hsE, heP16]; dsimp only; (repeat rw [regUpd_ne _ (by decide)]); rw [hsD, hCregs, hBregs, hAregs]; (repeat rw [regUpd_ne _ (by decide)]); rw [hs1, heChk]; dsimp only; (repeat rw [regUpd_ne _ (by decide)]); exact hrdi)
        (by rw [hsE, heP16]; dsimp only; (repeat rw [regUpd_ne _ (by decide)]); rw [hsD, hCregs, hBregs, hAregs]; (repeat rw [regUpd_ne _ (by decide)]); rw [hs1, heChk]; dsimp only; (repeat rw [regUpd_ne _ (by decide)]); exact hrsi)
        (by rw [hsE, heP16]; dsimp only; (repeat rw [regUpd_ne _ (by decide)]); rw [hsD, hCregs, hBregs, hAregs]; (repeat rw [regUpd_ne _ (by decide)]); rw [hs1, heChk]; dsimp only; (repeat rw [regUpd_ne _ (by decide)]); exact hrdx)
        (by rw [hsE, heP16]; dsimp only; (repeat rw [regUpd_ne _ (by decide)]); exact hDr9)
        (by rw [hsE, heP16]; dsimp only; rw [regUpd_ne _ (by decide), regUpd_eq])
        (by rw [hsE, heP16]; dsimp only; exact regUpd_eq _ _ _)
        (by rw [hsE, heP16]; dsimp only; (repeat rw [regUpd_ne _ (by decide)]); exact hDr8)
        (by rw [hsE, heP16]; dsimp only; (repeat rw [regUpd_ne _ (by decide)]); rw [hsD]; exact hCax)
        (by rw [hsE, heP16]; dsimp only; rw [writeXmm128_true_lo, sumLo2Dwords128_fold8_eq]; exact hCsum)
        hEcs hEym (by omega) (by omega)
      rcases hE8 with ⟨k, hk⟩
      refine ⟨37 + k, ?_⟩
      rw [show 37 + k = 30 + (1 + (6 + k)) by omega, runFrom_add, hrunC, runFrom_add, runFrom_add]
      simpa [Nat.add_assoc] using hk

end UntrustedCObjDotAvx2Tail
