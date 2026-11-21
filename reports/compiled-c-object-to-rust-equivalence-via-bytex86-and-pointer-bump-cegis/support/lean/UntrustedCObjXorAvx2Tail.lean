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
# `UntrustedCObjXorAvx2Tail`

Cascading `16B` VEX-128 epilogue (`0x4bf`), shrink-wrapped `push rbp; mov rbp, rsp;
push rbx` (`0x4fb`, `sp_delta = -16`), `8B` `mov bh, bl` + `vpshuflw` (`0x50d`),
`1..7B` unrolled scalar tail (`0x53d..0x5b7`), and `mov rbx, [rbp-8]; leave; ret`
(`0x5bb`) for `gcc 15.2.0 -O3 -mavx2` `c_xor_stream` (`0` `sorry`, `0` `isPartial`).
-/

namespace UntrustedCObjXorAvx2Tail

open ByteX86Gcc
open RustFfiSpecs
open CompiledCObjImages
open UntrustedCObjHints
open UntrustedCObjSimdHelpers

abbrev xorCmap : CodeMap := objCodeMap cFfiKernelsO3Avx2Obj
private abbrev y0 : YmmIdx := ⟨0, by decide⟩
private abbrev y1 : YmmIdx := ⟨1, by decide⟩
private abbrev y2 : YmmIdx := ⟨2, by decide⟩

/-! ## Section 1: Reflected Epilogue & Shrink-Wrapped Tail Decodes -/

theorem xorO3_ret609 : decodeX64 (fetchWindow16 xorCmap 0x400609#64) =
    .ok .ret64 1 := decodeAt_of_check rfl

private def xorO3_epi16ChkSeq : List (X64Instr × BitVec 64) := [
  (.movStore .s64 (.reg .r9) .r8, 0x4004c2#64),
  (.aluRmReg .s64 .sub (.reg .r9) .rdx, 0x4004c5#64),
  (.lea .s64 .rax { base := some .r9, disp := 0xffffffffffffffff#64 }, 0x4004c9#64),
  (.aluImm .s64 .cmp (.reg .rax) 0x0e#64, 0x4004cd#64)
]
private theorem xorO3_epi16Chk_dec : decodeSeqAt xorCmap 4 0x4004bf#64 = some xorO3_epi16ChkSeq :=
  decodeSeqAt_of_check rfl rfl
private theorem xorO3_epi16Chk_jbe : decodeX64 (fetchWindow16 xorCmap 0x4004cd#64) =
    .ok (.jccRel .be 0x0000000000000127#64) 6 := decodeAt_of_check rfl

private def xorO3_skip16Seq : List (X64Instr × BitVec 64) := [
  (.movStore .s64 (.reg .rax) .rdx, 0x4005fd#64),
  (.aluRmReg .s32 .xor (.reg .r10) .r10, 0x400600#64)
]
private theorem xorO3_skip16_dec : decodeSeqAt xorCmap 2 0x4005fa#64 = some xorO3_skip16Seq :=
  decodeSeqAt_of_check rfl rfl
private theorem xorO3_skip16_jmp : decodeX64 (fetchWindow16 xorCmap 0x400600#64) =
    .ok (.jmpRel 0xfffffffffffffef6#64) 5 := decodeAt_of_check rfl

private def xorO3_epi16BodySeq : List (X64Instr × BitVec 64) := [
  (.simdMovGprToX true false y0 (.reg .rcx), 0x4004d7#64),
  (.simdBroadcastB .vex128 y0 (.reg y0), 0x4004dc#64),
  (.simdBitwise .vex128 .xor y0 y0 (.mem { base := some .rsi, index := some (.rdx, 0) }), 0x4004e1#64),
  (.simdMovStore .vex128 (.mem { base := some .rdi, index := some (.rdx, 0) }) y0, 0x4004e6#64),
  (.alu8Imm .test (.reg8 (.lo8 .r9)) 0x0f#8, 0x4004ea#64)
]
private theorem xorO3_epi16Body_dec : decodeSeqAt xorCmap 5 0x4004d3#64 = some xorO3_epi16BodySeq :=
  decodeSeqAt_of_check rfl rfl
private theorem xorO3_epi16_je : decodeX64 (fetchWindow16 xorCmap 0x4004ea#64) =
    .ok (.jccRel .e 0x0000000000000119#64) 6 := decodeAt_of_check rfl

private def xorO3_post16Seq : List (X64Instr × BitVec 64) := [
  (.movStore .s64 (.reg .r10) .r9, 0x4004f3#64),
  (.aluImm .s64 .and (.reg .r10) 0xfffffffffffffff0#64, 0x4004f7#64),
  (.lea .s64 .rax { base := some .rdx, index := some (.r10, 0) }, 0x4004fb#64)
]
private theorem xorO3_post16_dec : decodeSeqAt xorCmap 3 0x4004f0#64 = some xorO3_post16Seq :=
  decodeSeqAt_of_check rfl rfl

private def xorO3_pushSeq : List (X64Instr × BitVec 64) := [
  (.push64 .rbp, 0x4004fc#64),
  (.aluRmReg .s64 .sub (.reg .r9) .r10, 0x4004ff#64),
  (.lea .s64 .r11 { base := some .r9, disp := 0xffffffffffffffff#64 }, 0x400503#64),
  (.movStore .s64 (.reg .rbp) .rsp, 0x400506#64),
  (.push64 .rbx, 0x400507#64),
  (.aluImm .s64 .cmp (.reg .r11) 0x06#64, 0x40050b#64)
]
private theorem xorO3_push_dec : decodeSeqAt xorCmap 6 0x4004fb#64 = some xorO3_pushSeq :=
  decodeSeqAt_of_check rfl rfl
private theorem xorO3_push_jbe : decodeX64 (fetchWindow16 xorCmap 0x40050b#64) =
    .ok (.jccRel .be 0x0000000000000030#64) 2 := decodeAt_of_check rfl

private def xorO3_tail8Seq : List (X64Instr × BitVec 64) := [
  (.movzx8 .s32 .rbx (.reg8 (.lo8 .rcx)), 0x400510#64),
  (.aluRmReg .s64 .add (.reg .rdx) .r10, 0x400513#64),
  (.mov8Store (.reg8 (.hi8 .rbx)) (.lo8 .rbx), 0x400515#64),
  (.simdMovqLoad true y1 (.mem { base := some .rsi, index := some (.rdx, 0) }), 0x40051a#64),
  (.simdMovGprToX true false y2 (.reg .rbx), 0x40051e#64),
  (.simdPshuflw .vex128 y0 (.reg y2) 0x00#8, 0x400523#64),
  (.simdBitwise .vex128 .xor y1 y1 (.reg y0), 0x400527#64),
  (.simdMovqStore true (.mem { base := some .rdi, index := some (.rdx, 0) }) y1, 0x40052c#64),
  (.alu8Imm .test (.reg8 (.lo8 .r9)) 0x07#8, 0x400530#64)
]
private theorem xorO3_tail8_dec : decodeSeqAt xorCmap 9 0x40050d#64 = some xorO3_tail8Seq :=
  decodeSeqAt_of_check rfl rfl
private theorem xorO3_tail8_je : decodeX64 (fetchWindow16 xorCmap 0x400530#64) =
    .ok (.jccRel .e 0x0000000000000085#64) 6 := decodeAt_of_check rfl

private def xorO3_post8Seq : List (X64Instr × BitVec 64) := [
  (.aluImm .s64 .and (.reg .r9) 0xfffffffffffffff8#64, 0x40053a#64),
  (.aluRmReg .s64 .add (.reg .rax) .r9, 0x40053d#64)
]
private theorem xorO3_post8_dec : decodeSeqAt xorCmap 2 0x400536#64 = some xorO3_post8Seq :=
  decodeSeqAt_of_check rfl rfl

private def xorO3_t0Seq : List (X64Instr × BitVec 64) := [
  (.movzx8 .s32 .rdx (.mem8 { base := some .rsi, index := some (.rax, 0), disp := 0#64 }), 0x400541#64),
  (.aluRmReg .s32 .xor (.reg .rdx) .rcx, 0x400543#64),
  (.mov8Store (.mem8 { base := some .rdi, index := some (.rax, 0), disp := 0#64 }) (.lo8 .rdx), 0x400546#64),
  (.lea .s64 .rdx { base := some .rax, disp := 1#64 }, 0x40054a#64),
  (.aluRmReg .s64 .cmp (.reg .rdx) .r8, 0x40054d#64)
]
private theorem xorO3_t0_dec : decodeSeqAt xorCmap 5 0x40053d#64 = some xorO3_t0Seq :=
  decodeSeqAt_of_check rfl rfl
private theorem xorO3_t0_jae : decodeX64 (fetchWindow16 xorCmap 0x40054d#64) =
    .ok (.jccRel .ae 0x6c#64) 2 := decodeAt_of_check rfl

private def xorO3_t1Seq : List (X64Instr × BitVec 64) := [
  (.movzx8 .s32 .rdx (.mem8 { base := some .rsi, index := some (.rax, 0), disp := 1#64 }), 0x400554#64),
  (.aluRmReg .s32 .xor (.reg .rdx) .rcx, 0x400556#64),
  (.mov8Store (.mem8 { base := some .rdi, index := some (.rax, 0), disp := 1#64 }) (.lo8 .rdx), 0x40055a#64),
  (.lea .s64 .rdx { base := some .rax, disp := 2#64 }, 0x40055e#64),
  (.aluRmReg .s64 .cmp (.reg .rdx) .r8, 0x400561#64)
]
private theorem xorO3_t1_dec : decodeSeqAt xorCmap 5 0x40054f#64 = some xorO3_t1Seq :=
  decodeSeqAt_of_check rfl rfl
private theorem xorO3_t1_jae : decodeX64 (fetchWindow16 xorCmap 0x400561#64) =
    .ok (.jccRel .ae 0x58#64) 2 := decodeAt_of_check rfl

private def xorO3_t2Seq : List (X64Instr × BitVec 64) := [
  (.movzx8 .s32 .rdx (.mem8 { base := some .rsi, index := some (.rax, 0), disp := 2#64 }), 0x400568#64),
  (.aluRmReg .s32 .xor (.reg .rdx) .rcx, 0x40056a#64),
  (.mov8Store (.mem8 { base := some .rdi, index := some (.rax, 0), disp := 2#64 }) (.lo8 .rdx), 0x40056e#64),
  (.lea .s64 .rdx { base := some .rax, disp := 3#64 }, 0x400572#64),
  (.aluRmReg .s64 .cmp (.reg .rdx) .r8, 0x400575#64)
]
private theorem xorO3_t2_dec : decodeSeqAt xorCmap 5 0x400563#64 = some xorO3_t2Seq :=
  decodeSeqAt_of_check rfl rfl
private theorem xorO3_t2_jae : decodeX64 (fetchWindow16 xorCmap 0x400575#64) =
    .ok (.jccRel .ae 0x44#64) 2 := decodeAt_of_check rfl

private def xorO3_t3Seq : List (X64Instr × BitVec 64) := [
  (.movzx8 .s32 .rdx (.mem8 { base := some .rsi, index := some (.rax, 0), disp := 3#64 }), 0x40057c#64),
  (.aluRmReg .s32 .xor (.reg .rdx) .rcx, 0x40057e#64),
  (.mov8Store (.mem8 { base := some .rdi, index := some (.rax, 0), disp := 3#64 }) (.lo8 .rdx), 0x400582#64),
  (.lea .s64 .rdx { base := some .rax, disp := 4#64 }, 0x400586#64),
  (.aluRmReg .s64 .cmp (.reg .rdx) .r8, 0x400589#64)
]
private theorem xorO3_t3_dec : decodeSeqAt xorCmap 5 0x400577#64 = some xorO3_t3Seq :=
  decodeSeqAt_of_check rfl rfl
private theorem xorO3_t3_jae : decodeX64 (fetchWindow16 xorCmap 0x400589#64) =
    .ok (.jccRel .ae 0x30#64) 2 := decodeAt_of_check rfl

private def xorO3_t4Seq : List (X64Instr × BitVec 64) := [
  (.movzx8 .s32 .rdx (.mem8 { base := some .rsi, index := some (.rax, 0), disp := 4#64 }), 0x400590#64),
  (.aluRmReg .s32 .xor (.reg .rdx) .rcx, 0x400592#64),
  (.mov8Store (.mem8 { base := some .rdi, index := some (.rax, 0), disp := 4#64 }) (.lo8 .rdx), 0x400596#64),
  (.lea .s64 .rdx { base := some .rax, disp := 5#64 }, 0x40059a#64),
  (.aluRmReg .s64 .cmp (.reg .rdx) .r8, 0x40059d#64)
]
private theorem xorO3_t4_dec : decodeSeqAt xorCmap 5 0x40058b#64 = some xorO3_t4Seq :=
  decodeSeqAt_of_check rfl rfl
private theorem xorO3_t4_jae : decodeX64 (fetchWindow16 xorCmap 0x40059d#64) =
    .ok (.jccRel .ae 0x1c#64) 2 := decodeAt_of_check rfl

private def xorO3_t5Seq : List (X64Instr × BitVec 64) := [
  (.movzx8 .s32 .rdx (.mem8 { base := some .rsi, index := some (.rax, 0), disp := 5#64 }), 0x4005a4#64),
  (.aluRmReg .s32 .xor (.reg .rdx) .rcx, 0x4005a6#64),
  (.mov8Store (.mem8 { base := some .rdi, index := some (.rax, 0), disp := 5#64 }) (.lo8 .rdx), 0x4005aa#64),
  (.lea .s64 .rdx { base := some .rax, disp := 6#64 }, 0x4005ae#64),
  (.aluRmReg .s64 .cmp (.reg .rdx) .r8, 0x4005b1#64)
]
private theorem xorO3_t5_dec : decodeSeqAt xorCmap 5 0x40059f#64 = some xorO3_t5Seq :=
  decodeSeqAt_of_check rfl rfl
private theorem xorO3_t5_jae : decodeX64 (fetchWindow16 xorCmap 0x4005b1#64) =
    .ok (.jccRel .ae 0x08#64) 2 := decodeAt_of_check rfl

private def xorO3_t6Seq : List (X64Instr × BitVec 64) := [
  (.alu8RegRm .xor (.lo8 .rcx) (.mem8 { base := some .rsi, index := some (.rax, 0), disp := 6#64 }), 0x4005b7#64),
  (.mov8Store (.mem8 { base := some .rdi, index := some (.rax, 0), disp := 6#64 }) (.lo8 .rcx), 0x4005bb#64)
]
private theorem xorO3_t6_dec : decodeSeqAt xorCmap 2 0x4005b3#64 = some xorO3_t6Seq :=
  decodeSeqAt_of_check rfl rfl

private def xorO3_epiRetSeq : List (X64Instr × BitVec 64) := [
  (.movLoad .s64 .rbx (.mem { base := some .rbp, disp := 0xfffffffffffffff8#64 }), 0x4005bf#64),
  (.leave64, 0x4005c0#64)
]
private theorem xorO3_epiRet_dec : decodeSeqAt xorCmap 2 0x4005bb#64 = some xorO3_epiRetSeq :=
  decodeSeqAt_of_check rfl rfl
private theorem xorO3_epiRet_ret : decodeX64 (fetchWindow16 xorCmap 0x4005c0#64) =
    .ok .ret64 1 := decodeAt_of_check rfl

/-! ## Section 2: `XorPrefixInv`, Epilogue (`0x5bb`), & Unrolled Tail (`0x53d`) -/

def XorPrefixInv (m0 m : ByteMem) (dst src rsp0 : BitVec 64) (len done : Nat) (key : BitVec 8) : Prop :=
  done ≤ len ∧
  (∀ i : Nat, i < done → m (dst + BitVec.ofNat 64 i) = m0 (src + BitVec.ofNat 64 i) ^^^ key) ∧
  (∀ addr : BitVec 64, ¬ InSliceRange addr dst done → ¬ InPrivateStackWindow addr rsp0 16 → m addr = m0 addr)

theorem xorPrefix_src_eq {m0 m : ByteMem} {dst src rsp0 : BitVec 64} {len done : Nat} {key : BitVec 8}
    (hnwS : NoWrapSlice src len) (hdisj : DisjointSlices dst len src len)
    (hstkS : DisjointFromStack src len rsp0 16)
    (hinv : XorPrefixInv m0 m dst src rsp0 len done key)
    {i : Nat} (hi : i < len) :
    m (src + BitVec.ofNat 64 i) = m0 (src + BitVec.ofNat 64 i) := by
  apply hinv.2.2
  · intro hin
    unfold InSliceRange at hin
    unfold DisjointSlices at hdisj
    have ht := ptr_offset_toNat hnwS (by omega : i ≤ len)
    have hle := hinv.1
    omega
  · exact slice_addr_not_in_private_stack hnwS hstkS hi

theorem xorPrefix_step1 {m0 m : ByteMem} {dst src rsp0 : BitVec 64} {len done : Nat} {key : BitVec 8}
    (hnwD : NoWrapSlice dst len) (hinv : XorPrefixInv m0 m dst src rsp0 len done key)
    (hlt : done < len) :
    XorPrefixInv m0 (memUpd8 m (dst + BitVec.ofNat 64 done) (m0 (src + BitVec.ofNat 64 done) ^^^ key))
      dst src rsp0 len (done + 1) key := by
  refine ⟨by omega, ?_, ?_⟩
  · intro i hi
    by_cases heq : i = done
    · subst heq; exact memUpd8_eq _ _ _
    · rw [memUpd8_ne _ (ptr_offset_ne hnwD (by omega) (by omega) heq)]
      exact hinv.2.1 i (by omega)
  · intro addr hnotSlice hnotStk
    have hne : addr ≠ dst + BitVec.ofNat 64 done := by
      intro heq; apply hnotSlice; unfold InSliceRange
      rw [heq, ptr_offset_toNat hnwD (by omega)]; omega
    rw [memUpd8_ne _ hne]
    exact hinv.2.2 addr (fun h => hnotSlice (by unfold InSliceRange at h ⊢; exact ⟨h.1, by omega⟩)) hnotStk

theorem xorPrefix_step_block {m0 m m' : ByteMem} {dst src rsp0 : BitVec 64} {len done blk : Nat} {key : BitVec 8}
    (hnwD : NoWrapSlice dst len) (hinv : XorPrefixInv m0 m dst src rsp0 len done key)
    (hbound : done + blk ≤ len)
    (hwr : ∀ j : Nat, j < blk → m' (dst + BitVec.ofNat 64 (done + j)) = m0 (src + BitVec.ofNat 64 (done + j)) ^^^ key)
    (hout : ∀ addr : BitVec 64, (∀ j : Nat, j < blk → addr ≠ dst + BitVec.ofNat 64 (done + j)) → m' addr = m addr) :
    XorPrefixInv m0 m' dst src rsp0 len (done + blk) key := by
  refine ⟨hbound, ?_, ?_⟩
  · intro i hi
    by_cases hlt : i < done
    · rw [hout _ (fun j hj => ptr_offset_ne hnwD (by omega) (by omega) (by omega))]
      exact hinv.2.1 i hlt
    · have hj : i - done < blk := by omega
      have heq : done + (i - done) = i := by omega
      rw [← heq]; exact hwr (i - done) hj
  · intro addr hnotSlice hnotStk
    rw [hout addr (fun j hj heq => by
          apply hnotSlice; unfold InSliceRange
          rw [heq, ptr_offset_toNat hnwD (by omega)]; omega)]
    exact hinv.2.2 addr (fun h => hnotSlice (by unfold InSliceRange at h ⊢; exact ⟨h.1, by omega⟩)) hnotStk

theorem xor_lo8_extract (a : BitVec 8) (c : BitVec 64) :
    BitVec.extractLsb' 0 8 ((BitVec.extractLsb' 0 32 (a.zeroExtend 64) ^^^ BitVec.extractLsb' 0 32 c).zeroExtend 64) =
      a ^^^ BitVec.extractLsb' 0 8 c := by
  apply BitVec.eq_of_getLsbD_eq; intro i hi
  unfold BitVec.zeroExtend
  simp [hi, show i < 32 by omega, show i < 64 by omega]

private theorem xor_epilogue_0x5bb (s0 s : X64State) (idx : Nat) (nd : Nat → UndefChoice)
    (hrun : s.halted = false) (hnf : s.fault = false) (hrip : s.rip = 0x4005bb#64)
    (hrsp0 : 16 ≤ (s0.regs .rsp).toNat)
    (hrbp : s.regs .rbp = s0.regs .rsp - 8#64)
    (hcs : s.regs .r12 = s0.regs .r12 ∧ s.regs .r13 = s0.regs .r13 ∧
           s.regs .r14 = s0.regs .r14 ∧ s.regs .r15 = s0.regs .r15)
    (hsavedRbp : readMem64 s.mem (s0.regs .rsp - 8#64) = s0.regs .rbp)
    (hsavedRbx : readMem64 s.mem (s0.regs .rsp - 16#64) = s0.regs .rbx)
    (hymm : UpperYmmCleanOrPreserved s0 s)
    (hpost : XorStreamContractPost 16 s0 s) :
    ∃ steps : Nat,
      let sf := runFrom xorCmap steps idx nd s
      sf.halted = true ∧ sf.fault = false ∧
      SysVCalleeSavedPreserved s0 sf ∧ UpperYmmCleanOrPreserved s0 sf ∧
      XorStreamContractPost 16 s0 sf := by
  refine ⟨3, ?_⟩
  rw [show (3 : Nat) = 2 + 1 by rfl, runFrom_add]
  rcases runFrom_of_decodeSeqAt xorO3_epiRet_dec idx nd s hrun hnf hrip with ⟨hseq, hrun1, hnf1⟩
  rw [hseq]
  have he : execInstrSeq 2 xorO3_epiRetSeq idx nd s =
      { s with
        rip := 0x4005c0#64,
        regs := regUpd (regUpd (regUpd s.regs .rbx (s0.regs .rbx)) .rsp (s0.regs .rsp)) .rbp (s0.regs .rbp) } := by
    dsimp only [xorO3_epiRetSeq]
    rw [execInstrSeq_succ_cons, exec_movLoad_s64_mem, evalByteAddr_base_disp, hrbp,
        bv64_sub8_add_neg8_eq_sub16 _ hrsp0, hsavedRbx,
        execInstrSeq_succ_cons, exec_leave64, execInstrSeq_zero]
    dsimp only
    rw [regUpd_ne _ (by decide), hrbp, hsavedRbp, BitVec.sub_add_cancel]
  rw [he] at hrun1 hnf1 ⊢
  rw [runFrom_succ, step_at_concrete xorO3_epiRet_ret _ _ hrun1 hnf1 rfl, exec_ret, runFrom_zero]
  refine ⟨rfl, hnf, ?_, hymm, hpost⟩
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · dsimp only; rw [regUpd_ne _ (by decide), regUpd_eq]
  · dsimp only; rw [regUpd_ne _ (by decide), regUpd_ne _ (by decide), regUpd_eq]
  · dsimp only; rw [regUpd_eq]
  · dsimp only; rw [regUpd_ne _ (by decide), regUpd_ne _ (by decide), regUpd_ne _ (by decide)]; exact hcs.1
  · dsimp only; rw [regUpd_ne _ (by decide), regUpd_ne _ (by decide), regUpd_ne _ (by decide)]; exact hcs.2.1
  · dsimp only; rw [regUpd_ne _ (by decide), regUpd_ne _ (by decide), regUpd_ne _ (by decide)]; exact hcs.2.2.1
  · dsimp only; rw [regUpd_ne _ (by decide), regUpd_ne _ (by decide), regUpd_ne _ (by decide)]; exact hcs.2.2.2

private theorem xorO3_tail_step {rip nextRip : BitVec 64} {jaeRel : BitVec 64} {k : Nat}
    {n1 n2 n3 n4 : BitVec 64}
    (hdec : decodeSeqAt xorCmap 5 rip = some [
      (.movzx8 .s32 .rdx (.mem8 { base := some .rsi, index := some (.rax, 0), disp := BitVec.ofNat 64 k }), n1),
      (.aluRmReg .s32 .xor (.reg .rdx) .rcx, n2),
      (.mov8Store (.mem8 { base := some .rdi, index := some (.rax, 0), disp := BitVec.ofNat 64 k }) (.lo8 .rdx), n3),
      (.lea .s64 .rdx { base := some .rax, disp := BitVec.ofNat 64 (k + 1) }, n4),
      (.aluRmReg .s64 .cmp (.reg .rdx) .r8, nextRip)
    ])
    (hjae : decodeX64 (fetchWindow16 xorCmap nextRip) = .ok (.jccRel .ae jaeRel) 2)
    (htgt : nextRip + 2#64 + jaeRel = 0x4005bb#64)
    (s0 s : X64State) (base : Nat) (idx : Nat) (nd : Nat → UndefChoice)
    (hpre : XorStreamPre 16 s0)
    (hrun : s.halted = false) (hnf : s.fault = false) (hrip : s.rip = rip)
    (hrdi : s.regs .rdi = s0.regs .rdi) (hrsi : s.regs .rsi = s0.regs .rsi)
    (hrcx : BitVec.extractLsb' 0 8 (s.regs .rcx) = BitVec.extractLsb' 0 8 (s0.regs .rcx))
    (hr8 : s.regs .r8 = s0.regs .rdx) (hrax : s.regs .rax = BitVec.ofNat 64 base)
    (hrbp : s.regs .rbp = s0.regs .rsp - 8#64)
    (hcs : s.regs .r12 = s0.regs .r12 ∧ s.regs .r13 = s0.regs .r13 ∧
           s.regs .r14 = s0.regs .r14 ∧ s.regs .r15 = s0.regs .r15)
    (hsavedRbp : readMem64 s.mem (s0.regs .rsp - 8#64) = s0.regs .rbp)
    (hsavedRbx : readMem64 s.mem (s0.regs .rsp - 16#64) = s0.regs .rbx)
    (hymm : UpperYmmCleanOrPreserved s0 s)
    (hinv : XorPrefixInv s0.mem s.mem (s0.regs .rdi) (s0.regs .rsi) (s0.regs .rsp) (s0.regs .rdx).toNat (base + k) (BitVec.extractLsb' 0 8 (s0.regs .rcx)))
    (hlt : base + k < (s0.regs .rdx).toNat) :
    let s' := runFrom xorCmap 6 idx nd s
    s'.halted = false ∧ s'.fault = false ∧
    s'.rip = (if base + (k + 1) < (s0.regs .rdx).toNat then nextRip + 2#64 else 0x4005bb#64) ∧
    s'.regs .rdi = s0.regs .rdi ∧ s'.regs .rsi = s0.regs .rsi ∧
    BitVec.extractLsb' 0 8 (s'.regs .rcx) = BitVec.extractLsb' 0 8 (s0.regs .rcx) ∧
    s'.regs .r8 = s0.regs .rdx ∧ s'.regs .rax = BitVec.ofNat 64 base ∧
    s'.regs .rbp = s0.regs .rsp - 8#64 ∧
    (s'.regs .r12 = s0.regs .r12 ∧ s'.regs .r13 = s0.regs .r13 ∧
     s'.regs .r14 = s0.regs .r14 ∧ s'.regs .r15 = s0.regs .r15) ∧
    readMem64 s'.mem (s0.regs .rsp - 8#64) = s0.regs .rbp ∧
    readMem64 s'.mem (s0.regs .rsp - 16#64) = s0.regs .rbx ∧
    UpperYmmCleanOrPreserved s0 s' ∧
    XorPrefixInv s0.mem s'.mem (s0.regs .rdi) (s0.regs .rsi) (s0.regs .rsp) (s0.regs .rdx).toNat (base + (k + 1)) (BitVec.extractLsb' 0 8 (s0.regs .rcx)) := by
  rcases hpre with ⟨hnwD, hnwS, hdisj, hstkD, hstkS⟩
  dsimp only
  rw [show (6 : Nat) = 5 + 1 by rfl, runFrom_add]
  rcases runFrom_of_decodeSeqAt hdec idx nd s hrun hnf hrip with ⟨hseq, hrun1, hnf1⟩
  rw [hseq]
  have haddrS : (s0.regs .rsi + BitVec.ofNat 64 base) + BitVec.ofNat 64 k = s0.regs .rsi + BitVec.ofNat 64 (base + k) :=
    bv64_add_ofNat_assoc _ _ _
  have haddrD : (s0.regs .rdi + BitVec.ofNat 64 base) + BitVec.ofNat 64 k = s0.regs .rdi + BitVec.ofNat 64 (base + k) :=
    bv64_add_ofNat_assoc _ _ _
  have hsrc := xorPrefix_src_eq hnwS hdisj hstkS hinv hlt
  let stepSeq : List (X64Instr × BitVec 64) := [
    (.movzx8 .s32 .rdx (.mem8 { base := some .rsi, index := some (.rax, 0), disp := BitVec.ofNat 64 k }), n1),
    (.aluRmReg .s32 .xor (.reg .rdx) .rcx, n2),
    (.mov8Store (.mem8 { base := some .rdi, index := some (.rax, 0), disp := BitVec.ofNat 64 k }) (.lo8 .rdx), n3),
    (.lea .s64 .rdx { base := some .rax, disp := BitVec.ofNat 64 (k + 1) }, n4),
    (.aluRmReg .s64 .cmp (.reg .rdx) .r8, nextRip)
  ]
  let bk : BitVec 8 := s0.mem (s0.regs .rsi + BitVec.ofNat 64 (base + k)) ^^^ BitVec.extractLsb' 0 8 (s0.regs .rcx)
  have he : execInstrSeq 5 stepSeq idx nd s =
      { s with
        rip := nextRip,
        regs := regUpd (regUpd (regUpd s.regs .rdx ((s0.mem (s0.regs .rsi + BitVec.ofNat 64 (base + k))).zeroExtend 64))
          .rdx ((BitVec.extractLsb' 0 32 ((s0.mem (s0.regs .rsi + BitVec.ofNat 64 (base + k))).zeroExtend 64) ^^^ BitVec.extractLsb' 0 32 (s.regs .rcx)).zeroExtend 64))
          .rdx (BitVec.ofNat 64 (base + (k + 1))),
        mem := memUpd8 s.mem (s0.regs .rdi + BitVec.ofNat 64 (base + k)) bk,
        flags := (evalAluN (by decide) .cmp (BitVec.ofNat 64 (base + (k + 1))) (s0.regs .rdx)
                   (evalAluN (by decide) .xor (BitVec.extractLsb' 0 32 ((s0.mem (s0.regs .rsi + BitVec.ofNat 64 (base + k))).zeroExtend 64))
                     (BitVec.extractLsb' 0 32 (s.regs .rcx)) s.flags (nd (idx + 1)).flags).2
                   (nd (idx + 4)).flags).2 } := by
    dsimp only [stepSeq, bk]
    rw [execInstrSeq_succ_cons, exec_movzx8_s32_mem, evalByteAddr_base_idx0_disp, hrsi, hrax, haddrS, hsrc]
    rw [execInstrSeq_succ_cons, exec_aluRmReg_s32_xor]
    dsimp only; rw [regUpd_eq, regUpd_ne _ (by decide)]
    rw [execInstrSeq_succ_cons, exec_mov8Store_mem_lo8, evalByteAddr_base_idx0_disp]
    dsimp only
    rw [regUpd_ne _ (by decide), regUpd_ne _ (by decide), regUpd_ne _ (by decide), regUpd_ne _ (by decide),
        hrdi, hrax, haddrD, regUpd_eq, xor_lo8_extract, hrcx]
    rw [execInstrSeq_succ_cons, exec_lea_s64, evalByteAddr_base_disp]
    dsimp only
    rw [regUpd_ne _ (by decide), regUpd_ne _ (by decide), hrax, bv64_ofNat_add]
    rw [execInstrSeq_succ_cons, exec_aluRmReg_s64_cmp, execInstrSeq_zero]
    dsimp only
    rw [regUpd_eq, regUpd_ne _ (by decide), regUpd_ne _ (by decide), regUpd_ne _ (by decide), hr8]
  change (runFrom xorCmap 1 (idx + 5) nd (execInstrSeq 5 stepSeq idx nd s)).halted = false ∧ _
  change (execInstrSeq 5 stepSeq idx nd s).halted = false at hrun1
  change (execInstrSeq 5 stepSeq idx nd s).fault = false at hnf1
  rw [he] at hrun1 hnf1 ⊢
  rw [runFrom_succ, step_at_concrete hjae _ _ hrun1 hnf1 rfl, runFrom_zero]
  have hlt64 : base + (k + 1) < 2 ^ 64 := by have := (s0.regs .rdx).isLt; omega
  have htn : (BitVec.ofNat 64 (base + (k + 1))).toNat = base + (k + 1) := by
    rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt hlt64]
  have hstk := stack16_slots_private_and_disjoint hstkD.1
  have hnotStkD := slice_addr_not_in_private_stack hnwD hstkD hlt
  have hrRbp : readMem64 (memUpd8 s.mem (s0.regs .rdi + BitVec.ofNat 64 (base + k)) bk) (s0.regs .rsp - 8#64) = s0.regs .rbp := by
    rw [← hsavedRbp]; apply readMem64_congr; intro j hj
    apply memUpd8_ne; intro heq; rw [← heq] at hnotStkD; exact hnotStkD (hstk.1 j hj)
  have hrRbx : readMem64 (memUpd8 s.mem (s0.regs .rdi + BitVec.ofNat 64 (base + k)) bk) (s0.regs .rsp - 16#64) = s0.regs .rbx := by
    rw [← hsavedRbx]; apply readMem64_congr; intro j hj
    apply memUpd8_ne; intro heq; rw [← heq] at hnotStkD; exact hnotStkD (hstk.2.1 j hj)
  have hinv' := xorPrefix_step1 hnwD hinv hlt
  have hinv'' : XorPrefixInv s0.mem (memUpd8 s.mem (s0.regs .rdi + BitVec.ofNat 64 (base + k)) bk)
      (s0.regs .rdi) (s0.regs .rsi) (s0.regs .rsp) (s0.regs .rdx).toNat (base + (k + 1)) (BitVec.extractLsb' 0 8 (s0.regs .rcx)) := by
    have hidx : base + k + 1 = base + (k + 1) := by omega
    rw [← hidx]; exact hinv'
  by_cases hcont : base + (k + 1) < (s0.regs .rdx).toNat
  · rw [exec_jcc_fall (by dsimp only; rw [evalCond_ae_of_flags, cmp_flags_cf, htn]; simp [hcont])]
    simp only [hcont, ite_true]
    refine ⟨hrun, hnf, trivial, ?_, ?_, ?_, ?_, ?_, ?_, ?_, hrRbp, hrRbx, hymm, hinv''⟩
    · rw [regUpd_ne _ (by decide), regUpd_ne _ (by decide), regUpd_ne _ (by decide), hrdi]
    · rw [regUpd_ne _ (by decide), regUpd_ne _ (by decide), regUpd_ne _ (by decide), hrsi]
    · rw [regUpd_ne _ (by decide), regUpd_ne _ (by decide), regUpd_ne _ (by decide), hrcx]
    · rw [regUpd_ne _ (by decide), regUpd_ne _ (by decide), regUpd_ne _ (by decide), hr8]
    · rw [regUpd_ne _ (by decide), regUpd_ne _ (by decide), regUpd_ne _ (by decide), hrax]
    · rw [regUpd_ne _ (by decide), regUpd_ne _ (by decide), regUpd_ne _ (by decide), hrbp]
    · exact ⟨by rw [regUpd_ne _ (by decide), regUpd_ne _ (by decide), regUpd_ne _ (by decide)]; exact hcs.1,
             by rw [regUpd_ne _ (by decide), regUpd_ne _ (by decide), regUpd_ne _ (by decide)]; exact hcs.2.1,
             by rw [regUpd_ne _ (by decide), regUpd_ne _ (by decide), regUpd_ne _ (by decide)]; exact hcs.2.2.1,
             by rw [regUpd_ne _ (by decide), regUpd_ne _ (by decide), regUpd_ne _ (by decide)]; exact hcs.2.2.2⟩
  · rw [exec_jcc_taken (by dsimp only; rw [evalCond_ae_of_flags, cmp_flags_cf, htn]; simp [hcont]), htgt]
    simp only [hcont, ite_false]
    refine ⟨hrun, hnf, trivial, ?_, ?_, ?_, ?_, ?_, ?_, ?_, hrRbp, hrRbx, hymm, hinv''⟩
    · rw [regUpd_ne _ (by decide), regUpd_ne _ (by decide), regUpd_ne _ (by decide), hrdi]
    · rw [regUpd_ne _ (by decide), regUpd_ne _ (by decide), regUpd_ne _ (by decide), hrsi]
    · rw [regUpd_ne _ (by decide), regUpd_ne _ (by decide), regUpd_ne _ (by decide), hrcx]
    · rw [regUpd_ne _ (by decide), regUpd_ne _ (by decide), regUpd_ne _ (by decide), hr8]
    · rw [regUpd_ne _ (by decide), regUpd_ne _ (by decide), regUpd_ne _ (by decide), hrax]
    · rw [regUpd_ne _ (by decide), regUpd_ne _ (by decide), regUpd_ne _ (by decide), hrbp]
    · exact ⟨by rw [regUpd_ne _ (by decide), regUpd_ne _ (by decide), regUpd_ne _ (by decide)]; exact hcs.1,
             by rw [regUpd_ne _ (by decide), regUpd_ne _ (by decide), regUpd_ne _ (by decide)]; exact hcs.2.1,
             by rw [regUpd_ne _ (by decide), regUpd_ne _ (by decide), regUpd_ne _ (by decide)]; exact hcs.2.2.1,
             by rw [regUpd_ne _ (by decide), regUpd_ne _ (by decide), regUpd_ne _ (by decide)]; exact hcs.2.2.2⟩

private theorem xorO3_unrolled_0x53d (s0 s : X64State) (base : Nat) (idx : Nat) (nd : Nat → UndefChoice)
    (hpre : XorStreamPre 16 s0)
    (hrun : s.halted = false) (hnf : s.fault = false) (hrip : s.rip = 0x40053d#64)
    (hrdi : s.regs .rdi = s0.regs .rdi) (hrsi : s.regs .rsi = s0.regs .rsi)
    (hrcx : BitVec.extractLsb' 0 8 (s.regs .rcx) = BitVec.extractLsb' 0 8 (s0.regs .rcx))
    (hr8 : s.regs .r8 = s0.regs .rdx) (hrax : s.regs .rax = BitVec.ofNat 64 base)
    (hrbp : s.regs .rbp = s0.regs .rsp - 8#64)
    (hcs : s.regs .r12 = s0.regs .r12 ∧ s.regs .r13 = s0.regs .r13 ∧
           s.regs .r14 = s0.regs .r14 ∧ s.regs .r15 = s0.regs .r15)
    (hsavedRbp : readMem64 s.mem (s0.regs .rsp - 8#64) = s0.regs .rbp)
    (hsavedRbx : readMem64 s.mem (s0.regs .rsp - 16#64) = s0.regs .rbx)
    (hymm : UpperYmmCleanOrPreserved s0 s)
    (hinv : XorPrefixInv s0.mem s.mem (s0.regs .rdi) (s0.regs .rsi) (s0.regs .rsp) (s0.regs .rdx).toNat base (BitVec.extractLsb' 0 8 (s0.regs .rcx)))
    (hremLo : base < (s0.regs .rdx).toNat) (hremHi : (s0.regs .rdx).toNat ≤ base + 7) :
    ∃ steps : Nat,
      let sf := runFrom xorCmap steps idx nd s
      sf.halted = true ∧ sf.fault = false ∧
      SysVCalleeSavedPreserved s0 sf ∧ UpperYmmCleanOrPreserved s0 sf ∧
      XorStreamContractPost 16 s0 sf := by
  have hpre' := hpre
  rcases hpre' with ⟨hnwD, hnwS, hdisj, hstkD, hstkS⟩
  have h0 := xorO3_tail_step (k := 0) xorO3_t0_dec xorO3_t0_jae rfl s0 s base idx nd hpre
    hrun hnf hrip hrdi hrsi hrcx hr8 hrax hrbp hcs hsavedRbp hsavedRbx hymm
    (by simpa [Nat.add_zero] using hinv) (by omega)
  generalize hs1 : runFrom xorCmap 6 idx nd s = s1 at h0
  rcases h0 with ⟨h1r, h1f, h1rip, h1di, h1si, h1cx, h1r8, h1ax, h1bp, h1cs, h1sbp, h1sbx, h1ym, h1inv⟩
  by_cases hc1 : base + 1 < (s0.regs .rdx).toNat
  · simp only [hc1, ite_true] at h1rip
    have h1 := xorO3_tail_step (k := 1) xorO3_t1_dec xorO3_t1_jae rfl s0 s1 base (idx + 6) nd hpre
      h1r h1f h1rip h1di h1si h1cx h1r8 h1ax h1bp h1cs h1sbp h1sbx h1ym h1inv hc1
    generalize hs2 : runFrom xorCmap 6 (idx + 6) nd s1 = s2 at h1
    rcases h1 with ⟨h2r, h2f, h2rip, h2di, h2si, h2cx, h2r8, h2ax, h2bp, h2cs, h2sbp, h2sbx, h2ym, h2inv⟩
    by_cases hc2 : base + 2 < (s0.regs .rdx).toNat
    · simp only [hc2, ite_true] at h2rip
      have h2 := xorO3_tail_step (k := 2) xorO3_t2_dec xorO3_t2_jae rfl s0 s2 base (idx + 12) nd hpre
        h2r h2f h2rip h2di h2si h2cx h2r8 h2ax h2bp h2cs h2sbp h2sbx h2ym h2inv hc2
      generalize hs3 : runFrom xorCmap 6 (idx + 12) nd s2 = s3 at h2
      rcases h2 with ⟨h3r, h3f, h3rip, h3di, h3si, h3cx, h3r8, h3ax, h3bp, h3cs, h3sbp, h3sbx, h3ym, h3inv⟩
      by_cases hc3 : base + 3 < (s0.regs .rdx).toNat
      · simp only [hc3, ite_true] at h3rip
        have h3 := xorO3_tail_step (k := 3) xorO3_t3_dec xorO3_t3_jae rfl s0 s3 base (idx + 18) nd hpre
          h3r h3f h3rip h3di h3si h3cx h3r8 h3ax h3bp h3cs h3sbp h3sbx h3ym h3inv hc3
        generalize hs4 : runFrom xorCmap 6 (idx + 18) nd s3 = s4 at h3
        rcases h3 with ⟨h4r, h4f, h4rip, h4di, h4si, h4cx, h4r8, h4ax, h4bp, h4cs, h4sbp, h4sbx, h4ym, h4inv⟩
        by_cases hc4 : base + 4 < (s0.regs .rdx).toNat
        · simp only [hc4, ite_true] at h4rip
          have h4 := xorO3_tail_step (k := 4) xorO3_t4_dec xorO3_t4_jae rfl s0 s4 base (idx + 24) nd hpre
            h4r h4f h4rip h4di h4si h4cx h4r8 h4ax h4bp h4cs h4sbp h4sbx h4ym h4inv hc4
          generalize hs5 : runFrom xorCmap 6 (idx + 24) nd s4 = s5 at h4
          rcases h4 with ⟨h5r, h5f, h5rip, h5di, h5si, h5cx, h5r8, h5ax, h5bp, h5cs, h5sbp, h5sbx, h5ym, h5inv⟩
          by_cases hc5 : base + 5 < (s0.regs .rdx).toNat
          · simp only [hc5, ite_true] at h5rip
            have h5 := xorO3_tail_step (k := 5) xorO3_t5_dec xorO3_t5_jae rfl s0 s5 base (idx + 30) nd hpre
              h5r h5f h5rip h5di h5si h5cx h5r8 h5ax h5bp h5cs h5sbp h5sbx h5ym h5inv hc5
            generalize hs6 : runFrom xorCmap 6 (idx + 30) nd s5 = s6 at h5
            rcases h5 with ⟨h6r, h6f, h6rip, h6di, h6si, h6cx, h6r8, h6ax, h6bp, h6cs, h6sbp, h6sbx, h6ym, h6inv⟩
            by_cases hc6 : base + 6 < (s0.regs .rdx).toNat
            · simp only [hc6, ite_true] at h6rip
              rcases runFrom_of_decodeSeqAt xorO3_t6_dec (idx + 36) nd s6 h6r h6f h6rip with ⟨ht6, h7r, h7f⟩
              have hsrc6 := xorPrefix_src_eq hnwS hdisj hstkS h6inv hc6
              have haddrS6 : (s0.regs .rsi + BitVec.ofNat 64 base) + 6#64 = s0.regs .rsi + BitVec.ofNat 64 (base + 6) :=
                bv64_add_ofNat_assoc _ _ _
              have haddrD6 : (s0.regs .rdi + BitVec.ofNat 64 base) + 6#64 = s0.regs .rdi + BitVec.ofNat 64 (base + 6) :=
                bv64_add_ofNat_assoc _ _ _
              let b6 : BitVec 8 := s0.mem (s0.regs .rsi + BitVec.ofNat 64 (base + 6)) ^^^ BitVec.extractLsb' 0 8 (s0.regs .rcx)
              have he6 : execInstrSeq 2 xorO3_t6Seq (idx + 36) nd s6 =
                  { s6 with
                    rip := 0x4005bb#64,
                    regs := writeSubReg8 s6.regs (.lo8 .rcx) (BitVec.extractLsb' 0 8 (s0.regs .rcx) ^^^ s0.mem (s0.regs .rsi + BitVec.ofNat 64 (base + 6))),
                    mem := memUpd8 s6.mem (s0.regs .rdi + BitVec.ofNat 64 (base + 6)) b6,
                    flags := (evalAluN (by decide) .xor (BitVec.extractLsb' 0 8 (s0.regs .rcx)) (s0.mem (s0.regs .rsi + BitVec.ofNat 64 (base + 6))) s6.flags (nd (idx + 36)).flags).2 } := by
                dsimp only [xorO3_t6Seq, b6]
                rw [execInstrSeq_succ_cons, exec_alu8RegRm_xor_lo8_mem, evalByteAddr_base_idx0_disp, h6si, h6ax, haddrS6, hsrc6, h6cx]
                rw [execInstrSeq_succ_cons, exec_mov8Store_mem_lo8, evalByteAddr_base_idx0_disp, execInstrSeq_zero]
                dsimp only
                have hlo := writeSubReg8_lo8_preserves_hi56 s6.regs .rcx (BitVec.extractLsb' 0 8 (s0.regs .rcx) ^^^ s0.mem (s0.regs .rsi + BitVec.ofNat 64 (base + 6)))
                rw [hlo.2.2 .rdi (by decide), hlo.2.2 .rax (by decide), h6di, h6ax, haddrD6, hlo.1, BitVec.xor_comm]
              have h7lo := writeSubReg8_lo8_preserves_hi56 s6.regs .rcx (BitVec.extractLsb' 0 8 (s0.regs .rcx) ^^^ s0.mem (s0.regs .rsi + BitVec.ofNat 64 (base + 6)))
              have hstk := stack16_slots_private_and_disjoint hstkD.1
              have hnotStkD := slice_addr_not_in_private_stack hnwD hstkD hc6
              have hrRbp7 : readMem64 (memUpd8 s6.mem (s0.regs .rdi + BitVec.ofNat 64 (base + 6)) b6) (s0.regs .rsp - 8#64) = s0.regs .rbp := by
                rw [← h6sbp]; apply readMem64_congr; intro j hj
                apply memUpd8_ne; intro heq; rw [← heq] at hnotStkD; exact hnotStkD (hstk.1 j hj)
              have hrRbx7 : readMem64 (memUpd8 s6.mem (s0.regs .rdi + BitVec.ofNat 64 (base + 6)) b6) (s0.regs .rsp - 16#64) = s0.regs .rbx := by
                rw [← h6sbx]; apply readMem64_congr; intro j hj
                apply memUpd8_ne; intro heq; rw [← heq] at hnotStkD; exact hnotStkD (hstk.2.1 j hj)
              have hinv7 := xorPrefix_step1 hnwD h6inv hc6
              have hlen7 : base + 6 + 1 = (s0.regs .rdx).toNat := by omega
              rw [hlen7] at hinv7
              have hepi := xor_epilogue_0x5bb s0 (runFrom xorCmap 2 (idx + 36) nd s6) (idx + 38) nd
                (by rw [ht6]; exact h7r) (by rw [ht6]; exact h7f) (by rw [ht6, he6])
                hstkD.1
                (by rw [ht6, he6]; dsimp only; rw [h7lo.2.2 .rbp (by decide), h6bp])
                (by rw [ht6, he6]; dsimp only; exact ⟨by rw [h7lo.2.2 .r12 (by decide)]; exact h6cs.1,
                      by rw [h7lo.2.2 .r13 (by decide)]; exact h6cs.2.1,
                      by rw [h7lo.2.2 .r14 (by decide)]; exact h6cs.2.2.1,
                      by rw [h7lo.2.2 .r15 (by decide)]; exact h6cs.2.2.2⟩)
                (by rw [ht6, he6]; exact hrRbp7)
                (by rw [ht6, he6]; exact hrRbx7)
                (by rw [ht6, he6]; exact h6ym)
                (by rw [ht6, he6]; exact hinv7.2)
              rcases hepi with ⟨k, hk⟩
              refine ⟨38 + k, ?_⟩
              rw [show 38 + k = 6 + (6 + (6 + (6 + (6 + (6 + (2 + k)))))) by omega,
                  runFrom_add, hs1, runFrom_add, hs2, runFrom_add, hs3, runFrom_add, hs4,
                  runFrom_add, hs5, runFrom_add, hs6, runFrom_add]
              simpa [Nat.add_assoc] using hk
            · simp only [hc6, ite_false] at h6rip
              have hlen6 : base + 6 = (s0.regs .rdx).toNat := by omega
              rw [hlen6] at h6inv
              rcases xor_epilogue_0x5bb s0 s6 (idx + 36) nd h6r h6f h6rip hstkD.1 h6bp h6cs h6sbp h6sbx h6ym h6inv.2 with ⟨k, hk⟩
              refine ⟨36 + k, ?_⟩
              rw [show 36 + k = 6 + (6 + (6 + (6 + (6 + (6 + k))))) by omega,
                  runFrom_add, hs1, runFrom_add, hs2, runFrom_add, hs3, runFrom_add, hs4, runFrom_add, hs5, runFrom_add, hs6]
              simpa [Nat.add_assoc] using hk
          · simp only [hc5, ite_false] at h5rip
            have hlen5 : base + 5 = (s0.regs .rdx).toNat := by omega
            rw [hlen5] at h5inv
            rcases xor_epilogue_0x5bb s0 s5 (idx + 30) nd h5r h5f h5rip hstkD.1 h5bp h5cs h5sbp h5sbx h5ym h5inv.2 with ⟨k, hk⟩
            refine ⟨30 + k, ?_⟩
            rw [show 30 + k = 6 + (6 + (6 + (6 + (6 + k)))) by omega,
                runFrom_add, hs1, runFrom_add, hs2, runFrom_add, hs3, runFrom_add, hs4, runFrom_add, hs5]
            simpa [Nat.add_assoc] using hk
        · simp only [hc4, ite_false] at h4rip
          have hlen4 : base + 4 = (s0.regs .rdx).toNat := by omega
          rw [hlen4] at h4inv
          rcases xor_epilogue_0x5bb s0 s4 (idx + 24) nd h4r h4f h4rip hstkD.1 h4bp h4cs h4sbp h4sbx h4ym h4inv.2 with ⟨k, hk⟩
          refine ⟨24 + k, ?_⟩
          rw [show 24 + k = 6 + (6 + (6 + (6 + k))) by omega,
              runFrom_add, hs1, runFrom_add, hs2, runFrom_add, hs3, runFrom_add, hs4]
          simpa [Nat.add_assoc] using hk
      · simp only [hc3, ite_false] at h3rip
        have hlen3 : base + 3 = (s0.regs .rdx).toNat := by omega
        rw [hlen3] at h3inv
        rcases xor_epilogue_0x5bb s0 s3 (idx + 18) nd h3r h3f h3rip hstkD.1 h3bp h3cs h3sbp h3sbx h3ym h3inv.2 with ⟨k, hk⟩
        refine ⟨18 + k, ?_⟩
        rw [show 18 + k = 6 + (6 + (6 + k)) by omega,
            runFrom_add, hs1, runFrom_add, hs2, runFrom_add, hs3]
        simpa [Nat.add_assoc] using hk
    · simp only [hc2, ite_false] at h2rip
      have hlen2 : base + 2 = (s0.regs .rdx).toNat := by omega
      rw [hlen2] at h2inv
      rcases xor_epilogue_0x5bb s0 s2 (idx + 12) nd h2r h2f h2rip hstkD.1 h2bp h2cs h2sbp h2sbx h2ym h2inv.2 with ⟨k, hk⟩
      refine ⟨12 + k, ?_⟩
      rw [show 12 + k = 6 + (6 + k) by omega, runFrom_add, hs1, runFrom_add, hs2]
      simpa [Nat.add_assoc] using hk
  · simp only [hc1, ite_false] at h1rip
    have hlen1 : base + 1 = (s0.regs .rdx).toNat := by omega
    rw [hlen1] at h1inv
    rcases xor_epilogue_0x5bb s0 s1 (idx + 6) nd h1r h1f h1rip hstkD.1 h1bp h1cs h1sbp h1sbx h1ym h1inv.2 with ⟨k, hk⟩
    refine ⟨6 + k, ?_⟩
    rw [runFrom_add, hs1]
    exact hk

private theorem xorO3_shrinkwrap_0x4fb (s0 s : X64State) (done0 r10Val : Nat) (idx : Nat) (nd : Nat → UndefChoice)
    (hpre : XorStreamPre 16 s0)
    (hrun : s.halted = false) (hnf : s.fault = false) (hrip : s.rip = 0x4004fb#64)
    (hrdi : s.regs .rdi = s0.regs .rdi) (hrsi : s.regs .rsi = s0.regs .rsi)
    (hrcx : BitVec.extractLsb' 0 8 (s.regs .rcx) = BitVec.extractLsb' 0 8 (s0.regs .rcx))
    (hr8 : s.regs .r8 = s0.regs .rdx)
    (hrdx : s.regs .rdx = BitVec.ofNat 64 done0)
    (hr10 : s.regs .r10 = BitVec.ofNat 64 r10Val)
    (hrax : s.regs .rax = BitVec.ofNat 64 (done0 + r10Val))
    (hr9 : s.regs .r9 = BitVec.ofNat 64 ((s0.regs .rdx).toNat - done0))
    (hcs : SysVCalleeSavedPreserved s0 s)
    (hymm : UpperYmmCleanOrPreserved s0 s)
    (hinv : XorPrefixInv s0.mem s.mem (s0.regs .rdi) (s0.regs .rsi) (s0.regs .rsp) (s0.regs .rdx).toNat (done0 + r10Val) (BitVec.extractLsb' 0 8 (s0.regs .rcx)))
    (hr10Le : done0 + r10Val < (s0.regs .rdx).toNat)
    (hremHi : (s0.regs .rdx).toNat - (done0 + r10Val) ≤ 15) :
    ∃ steps : Nat,
      let sf := runFrom xorCmap steps idx nd s
      sf.halted = true ∧ sf.fault = false ∧
      SysVCalleeSavedPreserved s0 sf ∧ UpperYmmCleanOrPreserved s0 sf ∧
      XorStreamContractPost 16 s0 sf := by
  have hpre' := hpre
  rcases hpre' with ⟨hnwD, hnwS, hdisj, hstkD, hstkS⟩
  have hstk := stack16_slots_private_and_disjoint hstkD.1
  rcases hcs with ⟨hsp, hbx, hbp, hr12, hr13, hr14, hr15⟩
  have hlenLt := (s0.regs .rdx).isLt
  have hremPos : 0 < (s0.regs .rdx).toNat - (done0 + r10Val) := by omega
  have hsub9 : BitVec.ofNat 64 ((s0.regs .rdx).toNat - done0) - BitVec.ofNat 64 r10Val =
      BitVec.ofNat 64 ((s0.regs .rdx).toNat - (done0 + r10Val)) := by
    apply BitVec.eq_of_toNat_eq
    rw [bv64_sub_toNat_of_le (by simp [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega : (s0.regs .rdx).toNat - done0 < 2 ^ 64), Nat.mod_eq_of_lt (by omega : r10Val < 2 ^ 64)]; omega)]
    simp [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega : (s0.regs .rdx).toNat - done0 < 2 ^ 64),
          Nat.mod_eq_of_lt (by omega : r10Val < 2 ^ 64),
          Nat.mod_eq_of_lt (by omega : (s0.regs .rdx).toNat - (done0 + r10Val) < 2 ^ 64)]
    omega
  rcases runFrom_of_decodeSeqAt xorO3_push_dec idx nd s hrun hnf hrip with ⟨hseq, hrun1, hnf1⟩
  let remBv : BitVec 64 := BitVec.ofNat 64 ((s0.regs .rdx).toNat - (done0 + r10Val))
  have hremBvTn : remBv.toNat = (s0.regs .rdx).toNat - (done0 + r10Val) := by
    dsimp only [remBv]; rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)]
  have hsp16 : (s0.regs .rsp - 8#64) - 8#64 = s0.regs .rsp - 16#64 :=
    bv64_sub8_sub8_eq_sub16 (s0.regs .rsp) hstkD.1
  have hePush : execInstrSeq 6 xorO3_pushSeq idx nd s =
      { s with
        rip := 0x40050b#64,
        regs := regUpd (regUpd (regUpd (regUpd (regUpd s.regs .rsp (s0.regs .rsp - 8#64))
          .r9 remBv) .r11 (remBv + 0xffffffffffffffff#64)) .rbp (s0.regs .rsp - 8#64))
          .rsp (s0.regs .rsp - 16#64),
        mem := writeMem64 (writeMem64 s.mem (s0.regs .rsp - 8#64) (s0.regs .rbp)) (s0.regs .rsp - 16#64) (s0.regs .rbx),
        flags := (evalAluN (by decide) .cmp (remBv + 0xffffffffffffffff#64) 6#64
                   (evalAluN (by decide) .sub (BitVec.ofNat 64 ((s0.regs .rdx).toNat - done0)) (BitVec.ofNat 64 r10Val) s.flags (nd (idx + 1)).flags).2
                   (nd (idx + 5)).flags).2 } := by
    dsimp only [xorO3_pushSeq]
    rw [execInstrSeq_succ_cons, exec_push64, hsp, hbp]
    rw [execInstrSeq_succ_cons, exec_aluRmReg_s64_sub]
    dsimp only; rw [regUpd_ne _ (by decide), regUpd_ne _ (by decide), hr9, hr10, hsub9]
    rw [execInstrSeq_succ_cons, exec_lea_s64, evalByteAddr_base_disp]
    dsimp only; rw [regUpd_eq]
    rw [execInstrSeq_succ_cons, exec_movStore_s64_reg]
    dsimp only; rw [regUpd_ne _ (by decide), regUpd_ne _ (by decide), regUpd_eq]
    rw [execInstrSeq_succ_cons, exec_push64]
    dsimp only; rw [regUpd_ne _ (by decide), regUpd_ne _ (by decide), regUpd_ne _ (by decide), regUpd_eq,
                    regUpd_ne _ (by decide), regUpd_ne _ (by decide), regUpd_ne _ (by decide), regUpd_ne _ (by decide),
                    hbx, hsp16]
    rw [execInstrSeq_succ_cons, exec_aluImm_s64_cmp, execInstrSeq_zero]
    dsimp only; rw [regUpd_ne _ (by decide), regUpd_ne _ (by decide), regUpd_eq]
  have hmemPushInv : XorPrefixInv s0.mem
      (writeMem64 (writeMem64 s.mem (s0.regs .rsp - 8#64) (s0.regs .rbp)) (s0.regs .rsp - 16#64) (s0.regs .rbx))
      (s0.regs .rdi) (s0.regs .rsi) (s0.regs .rsp) (s0.regs .rdx).toNat (done0 + r10Val) (BitVec.extractLsb' 0 8 (s0.regs .rcx)) := by
    refine ⟨hinv.1, ?_, ?_⟩
    · intro i hi
      have hns := slice_addr_not_in_private_stack hnwD hstkD (by omega : i < (s0.regs .rdx).toNat)
      rw [writeMem64_byte_ne _ _ _ _ (fun j hj heq => by rw [heq] at hns; exact hns (hstk.2.1 j hj)),
          writeMem64_byte_ne _ _ _ _ (fun j hj heq => by rw [heq] at hns; exact hns (hstk.1 j hj))]
      exact hinv.2.1 i hi
    · intro addr hnsl hnstk
      rw [writeMem64_byte_ne _ _ _ _ (fun j hj heq => by rw [heq] at hnstk; exact hnstk (hstk.2.1 j hj)),
          writeMem64_byte_ne _ _ _ _ (fun j hj heq => by rw [heq] at hnstk; exact hnstk (hstk.1 j hj))]
      exact hinv.2.2 addr hnsl hnstk
  have hsbp1 : readMem64 (writeMem64 (writeMem64 s.mem (s0.regs .rsp - 8#64) (s0.regs .rbp)) (s0.regs .rsp - 16#64) (s0.regs .rbx))
      (s0.regs .rsp - 8#64) = s0.regs .rbp :=
    Eq.trans
      (readMem64_congr (fun j hj => writeMem64_byte_ne _ _ _ _ (fun k hk => hstk.2.2 j k hj hk)))
      (ByteX86Gcc.readMem64_writeMem64_same s.mem (s0.regs .rsp - 8#64) (s0.regs .rbp))
  have hsbx1 : readMem64 (writeMem64 (writeMem64 s.mem (s0.regs .rsp - 8#64) (s0.regs .rbp)) (s0.regs .rsp - 16#64) (s0.regs .rbx))
      (s0.regs .rsp - 16#64) = s0.regs .rbx := ByteX86Gcc.readMem64_writeMem64_same _ _ _
  have hbe := bv64_sub1_cmp_be remBv 6 (by rw [hremBvTn]; exact hremPos) (by decide)
  rw [hremBvTn] at hbe
  by_cases hle7 : (s0.regs .rdx).toNat - (done0 + r10Val) ≤ 7
  · have hcc : evalCond .be (execInstrSeq 6 xorO3_pushSeq idx nd s).flags = true := by
      rw [hePush]; dsimp only
      rw [evalCond_be_of_flags, cmp_flags_cf, cmp_flags_zf]
      change (decide ((remBv + 0xffffffffffffffff#64).toNat < 6) || ((remBv + 0xffffffffffffffff#64) - BitVec.ofNat 64 6 == 0#64)) = true
      rw [hbe]; simp [hle7]
    let s1 := runFrom xorCmap 7 idx nd s
    have hs1Eq : s1 = { execInstrSeq 6 xorO3_pushSeq idx nd s with rip := 0x40053d#64 } := by
      dsimp only [s1]
      rw [show (7 : Nat) = 6 + 1 by rfl, runFrom_add, hseq, runFrom_succ,
          step_at_concrete xorO3_push_jbe _ _ hrun1 hnf1 (by rw [hePush]),
          exec_jcc_taken hcc, runFrom_zero]
      rw [hePush]; rfl
    have heTail := xorO3_unrolled_0x53d s0 s1 (done0 + r10Val) (idx + 7) nd hpre
      (by rw [hs1Eq, hePush]; exact hrun) (by rw [hs1Eq, hePush]; exact hnf) (by rw [hs1Eq])
      (by rw [hs1Eq, hePush]; dsimp only; repeat rw [regUpd_ne _ (by decide)]; exact hrdi)
      (by rw [hs1Eq, hePush]; dsimp only; repeat rw [regUpd_ne _ (by decide)]; exact hrsi)
      (by rw [hs1Eq, hePush]; dsimp only; repeat rw [regUpd_ne _ (by decide)]; exact hrcx)
      (by rw [hs1Eq, hePush]; dsimp only; repeat rw [regUpd_ne _ (by decide)]; exact hr8)
      (by rw [hs1Eq, hePush]; dsimp only; repeat rw [regUpd_ne _ (by decide)]; exact hrax)
      (by rw [hs1Eq, hePush]; dsimp only; rw [regUpd_ne _ (by decide), regUpd_eq])
      (by rw [hs1Eq, hePush]; dsimp only; exact ⟨by repeat rw [regUpd_ne _ (by decide)]; exact hr12,
            by repeat rw [regUpd_ne _ (by decide)]; exact hr13,
            by repeat rw [regUpd_ne _ (by decide)]; exact hr14,
            by repeat rw [regUpd_ne _ (by decide)]; exact hr15⟩)
      (by rw [hs1Eq, hePush]; exact hsbp1)
      (by rw [hs1Eq, hePush]; exact hsbx1)
      (by rw [hs1Eq, hePush]; exact hymm)
      (by rw [hs1Eq, hePush]; exact hmemPushInv)
      hr10Le (by omega)
    rcases heTail with ⟨k, hk⟩
    exact ⟨7 + k, by rw [runFrom_add]; exact hk⟩
  · have hcc : evalCond .be (execInstrSeq 6 xorO3_pushSeq idx nd s).flags = false := by
      rw [hePush]; dsimp only
      rw [evalCond_be_of_flags, cmp_flags_cf, cmp_flags_zf]
      change (decide ((remBv + 0xffffffffffffffff#64).toNat < 6) || ((remBv + 0xffffffffffffffff#64) - BitVec.ofNat 64 6 == 0#64)) = false
      rw [hbe]; simp [hle7]
    let s1 := runFrom xorCmap 7 idx nd s
    have hs1Eq : s1 = { execInstrSeq 6 xorO3_pushSeq idx nd s with rip := 0x40050d#64 } := by
      dsimp only [s1]
      rw [show (7 : Nat) = 6 + 1 by rfl, runFrom_add, hseq, runFrom_succ,
          step_at_concrete xorO3_push_jbe _ _ hrun1 hnf1 (by rw [hePush]),
          exec_jcc_fall hcc, runFrom_zero]
      rw [hePush]; rfl
    rcases runFrom_of_decodeSeqAt xorO3_tail8_dec (idx + 7) nd s1
      (by rw [hs1Eq, hePush]; exact hrun) (by rw [hs1Eq, hePush]; exact hnf) (by rw [hs1Eq]) with ⟨ht8, hrun2, hnf2⟩
    let s1Regs := s1.regs
    let key8 : BitVec 8 := BitVec.extractLsb' 0 8 (s0.regs .rcx)
    have h1cx : BitVec.extractLsb' 0 8 (s1Regs .rcx) = key8 := by
      dsimp only [s1Regs, key8]; rw [hs1Eq, hePush]; dsimp only; repeat rw [regUpd_ne _ (by decide)]; exact hrcx
    have h1di : s1Regs .rdi = s0.regs .rdi := by
      dsimp only [s1Regs]; rw [hs1Eq, hePush]; dsimp only; repeat rw [regUpd_ne _ (by decide)]; exact hrdi
    have h1si : s1Regs .rsi = s0.regs .rsi := by
      dsimp only [s1Regs]; rw [hs1Eq, hePush]; dsimp only; repeat rw [regUpd_ne _ (by decide)]; exact hrsi
    have h1dx : s1Regs .rdx = BitVec.ofNat 64 done0 := by
      dsimp only [s1Regs]; rw [hs1Eq, hePush]; dsimp only; repeat rw [regUpd_ne _ (by decide)]; exact hrdx
    have h1r10 : s1Regs .r10 = BitVec.ofNat 64 r10Val := by
      dsimp only [s1Regs]; rw [hs1Eq, hePush]; dsimp only; repeat rw [regUpd_ne _ (by decide)]; exact hr10
    have h1r9 : s1Regs .r9 = remBv := by
      dsimp only [s1Regs]; rw [hs1Eq, hePush]; dsimp only; rw [regUpd_ne _ (by decide), regUpd_ne _ (by decide), regUpd_ne _ (by decide), regUpd_eq]
    have h1r8 : s1Regs .r8 = s0.regs .rdx := by
      dsimp only [s1Regs]; rw [hs1Eq, hePush]; dsimp only; repeat rw [regUpd_ne _ (by decide)]; exact hr8
    have h1ax : s1Regs .rax = BitVec.ofNat 64 (done0 + r10Val) := by
      dsimp only [s1Regs]; rw [hs1Eq, hePush]; dsimp only; repeat rw [regUpd_ne _ (by decide)]; exact hrax
    have h1bp : s1Regs .rbp = s0.regs .rsp - 8#64 := by
      dsimp only [s1Regs]; rw [hs1Eq, hePush]; dsimp only; rw [regUpd_ne _ (by decide), regUpd_eq]
    let rAfter1 := regUpd s1Regs .rbx (key8.zeroExtend 64)
    let rAfter2 := regUpd rAfter1 .rdx (BitVec.ofNat 64 (done0 + r10Val))
    let rAfter3 := writeSubReg8 rAfter2 (.hi8 .rbx) (readSubReg8 rAfter2 (.lo8 .rbx))
    let x2Val : BitVec 128 := ((BitVec.extractLsb' 0 32 (rAfter3 .rbx)).zeroExtend 64).zeroExtend 128
    let x0Val : BitVec 128 := pshuflw128 x2Val 0#8
    let srcQ : BitVec 64 := readMem64 s1.mem (s0.regs .rsi + BitVec.ofNat 64 (done0 + r10Val))
    let xor128 : BitVec 128 := srcQ.zeroExtend 128 ^^^ x0Val
    let yAfter1 := writeXmm128 true s1.ymms y1 (srcQ.zeroExtend 128)
    let yAfter2 := writeXmm128 true yAfter1 y2 x2Val
    let yAfter3 := writeXmm128 true yAfter2 y0 x0Val
    let yAfter4 := writeXmm128 true yAfter3 y1 xor128
    let memAfter8 := writeMem64 s1.mem (s0.regs .rdi + BitVec.ofNat 64 (done0 + r10Val)) (BitVec.extractLsb' 0 64 xor128)
    have hr3Pres : ∀ r : Reg, r ≠ .rbx → r ≠ .rdx → rAfter3 r = s1Regs r := by
      intro r hnb hnd
      dsimp only [rAfter3]
      have hr3 := writeSubReg8_hi8_preserves_lo8_and_hi48 rAfter2 .rbx (readSubReg8 rAfter2 (.lo8 .rbx))
      rw [hr3.2.2.2 r hnb]
      dsimp only [rAfter2, rAfter1]
      rw [regUpd_ne _ hnd, regUpd_ne _ hnb]
    have hr3Rdx : rAfter3 .rdx = BitVec.ofNat 64 (done0 + r10Val) := by
      dsimp only [rAfter3]
      have hr3 := writeSubReg8_hi8_preserves_lo8_and_hi48 rAfter2 .rbx (readSubReg8 rAfter2 (.lo8 .rbx))
      rw [hr3.2.2.2 .rdx (by decide)]
      dsimp only [rAfter2]; exact regUpd_eq _ _ _
    have hwx_lo : ∀ (ymms : YmmIdx → BitVec 256) (r : YmmIdx) (v : BitVec 128),
        BitVec.extractLsb' 0 128 (writeXmm128 true ymms r v r) = v := fun ymms r v => by
      rw [writeXmm128_true_eq, ymmUpd_eq, extract_lo128_append]
    have hwx_lo64 : ∀ (ymms : YmmIdx → BitVec 256) (r : YmmIdx) (v : BitVec 128),
        BitVec.extractLsb' 0 64 (writeXmm128 true ymms r v r) = BitVec.extractLsb' 0 64 v := fun ymms r v => by
      rw [writeXmm128_true_eq, ymmUpd_eq]
      apply BitVec.eq_of_getLsbD_eq; intro b hb
      rw [BitVec.getLsbD_extractLsb', BitVec.getLsbD_extractLsb', BitVec.getLsbD_append]
      simp [hb, show b < 128 by omega]
    have heT8 : execInstrSeq 9 xorO3_tail8Seq (idx + 7) nd s1 =
        { s1 with
          rip := 0x400530#64,
          regs := rAfter3,
          ymms := yAfter4,
          mem := memAfter8,
          flags := (evalAluN (by decide) .test (BitVec.extractLsb' 0 8 remBv) 0x07#8
                     (evalAluN (by decide) .add (BitVec.ofNat 64 done0) (BitVec.ofNat 64 r10Val) s1.flags (nd (idx + 8)).flags).2
                     (nd (idx + 15)).flags).2 } := by
      dsimp only [xorO3_tail8Seq]
      rw [execInstrSeq_succ_cons, exec_movzx8_s32_lo8, h1cx]
      change execInstrSeq 8 _ _ _ { s1 with rip := 0x400510#64, regs := rAfter1 } = _
      rw [execInstrSeq_succ_cons, exec_aluRmReg_s64_add]
      dsimp only [rAfter1]
      rw [regUpd_ne _ (by decide), regUpd_ne _ (by decide), h1dx, h1r10, bv64_ofNat_add]
      change execInstrSeq 7 _ _ _ { s1 with rip := 0x400513#64, regs := rAfter2, flags := _ } = _
      rw [execInstrSeq_succ_cons, exec_mov8Store_hi8_lo8]
      change execInstrSeq 6 _ _ _ { s1 with rip := 0x400515#64, regs := rAfter3, flags := _ } = _
      rw [execInstrSeq_succ_cons, exec_simdMovqLoad_vex_mem, evalByteAddr_base_idx0]
      dsimp only
      rw [hr3Pres .rsi (by decide) (by decide), hr3Rdx, h1si]
      change execInstrSeq 5 _ _ _ { s1 with rip := 0x40051a#64, regs := rAfter3, ymms := yAfter1, flags := _ } = _
      rw [execInstrSeq_succ_cons, exec_simdMovGprToX_vex32_reg]
      change execInstrSeq 4 _ _ _ { s1 with rip := 0x40051e#64, regs := rAfter3, ymms := yAfter2, flags := _ } = _
      rw [execInstrSeq_succ_cons, exec_simdPshuflw_vex128_reg]
      dsimp only; rw [show BitVec.extractLsb' 0 128 (yAfter2 y2) = x2Val from hwx_lo _ _ _]
      change execInstrSeq 3 _ _ _ { s1 with rip := 0x400523#64, regs := rAfter3, ymms := yAfter3, flags := _ } = _
      rw [execInstrSeq_succ_cons, exec_simdBitwise_vex128_xor_reg]
      dsimp only
      rw [show BitVec.extractLsb' 0 128 (yAfter3 y0) = x0Val from hwx_lo _ _ _,
          show BitVec.extractLsb' 0 128 (yAfter3 y1) = srcQ.zeroExtend 128 from by
            dsimp only [yAfter3, yAfter2, yAfter1]
            rw [writeXmm128_ne true _ (by decide : y1 ≠ y0), writeXmm128_ne true _ (by decide : y1 ≠ y2), hwx_lo]]
      change execInstrSeq 2 _ _ _ { s1 with rip := 0x400527#64, regs := rAfter3, ymms := yAfter4, flags := _ } = _
      rw [execInstrSeq_succ_cons, exec_simdMovqStore_vex_mem, evalByteAddr_base_idx0]
      dsimp only
      rw [hr3Pres .rdi (by decide) (by decide), hr3Rdx, h1di, hwx_lo64]
      rw [execInstrSeq_succ_cons, exec_alu8Imm_test_lo8, execInstrSeq_zero]
      dsimp only
      rw [hr3Pres .r9 (by decide) (by decide), h1r9]
    have hsplat8 : ∀ j : Nat, j < 8 → byteOf64 (BitVec.extractLsb' 0 64 x0Val) j = key8 := by
      intro j hj
      have hm := mov_bh_bl_pshuflw_splat8 (regUpd s1Regs .rdx (BitVec.ofNat 64 (done0 + r10Val))) key8 j hj
      have hrbxeq : rAfter3 .rbx =
          (writeSubReg8 (writeRegSz .s32 (regUpd s1Regs .rdx (BitVec.ofNat 64 (done0 + r10Val))) .rbx (key8.zeroExtend 64))
            (.hi8 .rbx) (readSubReg8 (writeRegSz .s32 (regUpd s1Regs .rdx (BitVec.ofNat 64 (done0 + r10Val))) .rbx (key8.zeroExtend 64)) (.lo8 .rbx))) .rbx := by
        dsimp only [rAfter3, rAfter2, rAfter1, writeSubReg8, readSubReg8, writeRegSz]
        rw [regUpd_eq, regUpd_eq, regUpd_ne _ (by decide), regUpd_eq, regUpd_eq, zext8_32_64_eq]
      dsimp only [x0Val, x2Val]
      rw [hrbxeq]; exact hm
    have h1memInv : XorPrefixInv s0.mem s1.mem (s0.regs .rdi) (s0.regs .rsi) (s0.regs .rsp) (s0.regs .rdx).toNat (done0 + r10Val) key8 := by
      rw [hs1Eq, hePush]; exact hmemPushInv
    have hmem8Inv : XorPrefixInv s0.mem memAfter8 (s0.regs .rdi) (s0.regs .rsi) (s0.regs .rsp) (s0.regs .rdx).toNat (done0 + r10Val + 8) key8 := by
      apply xorPrefix_step_block hnwD h1memInv (by omega)
      · intro j hj
        dsimp only [memAfter8]
        have hdp : s0.regs .rdi + BitVec.ofNat 64 (done0 + r10Val + j) =
            (s0.regs .rdi + BitVec.ofNat 64 (done0 + r10Val)) + BitVec.ofNat 64 j := (bv64_add_ofNat_assoc _ _ _).symm
        rw [hdp, writeMem64_at_offset _ _ _ j hj]
        have hloXor : BitVec.extractLsb' 0 64 xor128 = srcQ ^^^ BitVec.extractLsb' 0 64 x0Val := by
          dsimp only [xor128]; apply BitVec.eq_of_getLsbD_eq; intro b hb
          unfold BitVec.zeroExtend; simp [hb, show b < 128 by omega]
        rw [hloXor, xor64_byte_at _ _ j hj, hsplat8 j hj]
        dsimp only [srcQ]
        rw [readMem64_byte_at _ _ j hj, bv64_add_ofNat_assoc,
            xorPrefix_src_eq hnwS hdisj hstkS h1memInv (by omega)]
      · intro addr hout
        dsimp only [memAfter8]
        apply writeMem64_byte_ne; intro j hj
        rw [bv64_add_ofNat_assoc]; exact hout j hj
    have hrRbp8 : readMem64 memAfter8 (s0.regs .rsp - 8#64) = s0.regs .rbp := by
      have h1sbp : readMem64 s1.mem (s0.regs .rsp - 8#64) = s0.regs .rbp := by rw [hs1Eq, hePush]; exact hsbp1
      rw [← h1sbp]; apply readMem64_congr; intro j hj
      dsimp only [memAfter8]; apply writeMem64_byte_ne; intro k hk heq
      rw [bv64_add_ofNat_assoc] at heq
      exact slice_addr_not_in_private_stack hnwD hstkD (by omega : done0 + r10Val + k < (s0.regs .rdx).toNat) (heq ▸ hstk.1 j hj)
    have hrRbx8 : readMem64 memAfter8 (s0.regs .rsp - 16#64) = s0.regs .rbx := by
      have h1sbx : readMem64 s1.mem (s0.regs .rsp - 16#64) = s0.regs .rbx := by rw [hs1Eq, hePush]; exact hsbx1
      rw [← h1sbx]; apply readMem64_congr; intro j hj
      dsimp only [memAfter8]; apply writeMem64_byte_ne; intro k hk heq
      rw [bv64_add_ofNat_assoc] at heq
      exact slice_addr_not_in_private_stack hnwD hstkD (by omega : done0 + r10Val + k < (s0.regs .rdx).toNat) (heq ▸ hstk.2.1 j hj)
    have hymm8 : AllUpperYmmClean s0 → ∀ idx : YmmIdx, BitVec.extractLsb' 128 128 (yAfter4 idx) = 0#128 := by
      intro h0
      have hy1 : AllUpperYmmClean s1 := by rw [hs1Eq, hePush]; exact hymm h0
      exact writeXmm128_true_preserves_clean _ _ _ (writeXmm128_true_preserves_clean _ _ _
        (writeXmm128_true_preserves_clean _ _ _ (writeXmm128_true_preserves_clean _ _ _ hy1)))
    have htest7 := bv64_test_lo8_7_eq remBv
    rw [hremBvTn] at htest7
    by_cases hmod8 : ((s0.regs .rdx).toNat - (done0 + r10Val)) % 8 = 0
    · have hcc8 : evalCond .e (execInstrSeq 9 xorO3_tail8Seq (idx + 7) nd s1).flags = true := by
        rw [heT8]; dsimp only; rw [evalCond_e_of_zf_true (by rw [test_flags_zf, htest7]; simp [hmod8])]
      let s2 := runFrom xorCmap 10 (idx + 7) nd s1
      have hs2Eq : s2 = { execInstrSeq 9 xorO3_tail8Seq (idx + 7) nd s1 with rip := 0x4005bb#64 } := by
        dsimp only [s2]
        rw [show (10 : Nat) = 9 + 1 by rfl, runFrom_add, ht8, runFrom_succ,
            step_at_concrete xorO3_tail8_je _ _ hrun2 hnf2 (by rw [heT8]),
            exec_jcc_taken hcc8, runFrom_zero]
        rw [heT8]; rfl
      have hlen8 : done0 + r10Val + 8 = (s0.regs .rdx).toNat := by omega
      rw [hlen8] at hmem8Inv
      have hepi := xor_epilogue_0x5bb s0 s2 (idx + 17) nd
        (by rw [hs2Eq, heT8, hs1Eq, hePush]; exact hrun)
        (by rw [hs2Eq, heT8, hs1Eq, hePush]; exact hnf)
        (by rw [hs2Eq]) hstkD.1
        (by rw [hs2Eq, heT8]; dsimp only; rw [hr3Pres .rbp (by decide) (by decide), h1bp])
        (by rw [hs2Eq, heT8]; dsimp only; exact ⟨by rw [hr3Pres .r12 (by decide) (by decide)]; dsimp only [s1Regs]; rw [hs1Eq, hePush]; dsimp only; repeat rw [regUpd_ne _ (by decide)]; exact hr12,
              by rw [hr3Pres .r13 (by decide) (by decide)]; dsimp only [s1Regs]; rw [hs1Eq, hePush]; dsimp only; repeat rw [regUpd_ne _ (by decide)]; exact hr13,
              by rw [hr3Pres .r14 (by decide) (by decide)]; dsimp only [s1Regs]; rw [hs1Eq, hePush]; dsimp only; repeat rw [regUpd_ne _ (by decide)]; exact hr14,
              by rw [hr3Pres .r15 (by decide) (by decide)]; dsimp only [s1Regs]; rw [hs1Eq, hePush]; dsimp only; repeat rw [regUpd_ne _ (by decide)]; exact hr15⟩)
        (by rw [hs2Eq, heT8]; exact hrRbp8)
        (by rw [hs2Eq, heT8]; exact hrRbx8)
        (by rw [hs2Eq, heT8]; exact hymm8)
        (by rw [hs2Eq, heT8]; exact hmem8Inv.2)
      rcases hepi with ⟨k, hk⟩
      exact ⟨17 + k, by rw [show 17 + k = 7 + (10 + k) by omega, runFrom_add, runFrom_add]; simpa [Nat.add_assoc] using hk⟩
    · have hcc8 : evalCond .e (execInstrSeq 9 xorO3_tail8Seq (idx + 7) nd s1).flags = false := by
        rw [heT8]; dsimp only; rw [evalCond_e_of_zf_false (by rw [test_flags_zf, htest7]; simp [hmod8])]
      let s2 := runFrom xorCmap 10 (idx + 7) nd s1
      have hs2Eq : s2 = { execInstrSeq 9 xorO3_tail8Seq (idx + 7) nd s1 with rip := 0x400536#64 } := by
        dsimp only [s2]
        rw [show (10 : Nat) = 9 + 1 by rfl, runFrom_add, ht8, runFrom_succ,
            step_at_concrete xorO3_tail8_je _ _ hrun2 hnf2 (by rw [heT8]),
            exec_jcc_fall hcc8, runFrom_zero]
        rw [heT8]; rfl
      rcases runFrom_of_decodeSeqAt xorO3_post8_dec (idx + 17) nd s2
        (by rw [hs2Eq, heT8, hs1Eq, hePush]; exact hrun)
        (by rw [hs2Eq, heT8, hs1Eq, hePush]; exact hnf) (by rw [hs2Eq]) with ⟨hp8, hrun3, hnf3⟩
      have hmask8 : remBv &&& 0xfffffffffffffff8#64 = BitVec.ofNat 64 8 := by
        apply BitVec.eq_of_toNat_eq
        rw [bv64_and_neg8_toNat, hremBvTn, BitVec.toNat_ofNat]; omega
      have heP8 : execInstrSeq 2 xorO3_post8Seq (idx + 17) nd s2 =
          { s2 with
            rip := 0x40053d#64,
            regs := regUpd (regUpd s2.regs .r9 (BitVec.ofNat 64 8)) .rax (BitVec.ofNat 64 (done0 + r10Val + 8)),
            flags := (evalAluN (by decide) .add (BitVec.ofNat 64 (done0 + r10Val)) (BitVec.ofNat 64 8)
                       (evalAluN (by decide) .and remBv 0xfffffffffffffff8#64 s2.flags (nd (idx + 17)).flags).2
                       (nd (idx + 18)).flags).2 } := by
        dsimp only [xorO3_post8Seq]
        have h2r9 : s2.regs .r9 = remBv := by rw [hs2Eq, heT8]; dsimp only; rw [hr3Pres .r9 (by decide) (by decide), h1r9]
        have h2ax : s2.regs .rax = BitVec.ofNat 64 (done0 + r10Val) := by rw [hs2Eq, heT8]; dsimp only; rw [hr3Pres .rax (by decide) (by decide), h1ax]
        rw [execInstrSeq_succ_cons, exec_aluImm_s64_and, h2r9, hmask8]
        rw [execInstrSeq_succ_cons, exec_aluRmReg_s64_add, execInstrSeq_zero]
        dsimp only; rw [regUpd_ne _ (by decide), regUpd_eq, h2ax, bv64_ofNat_add]
      let s3 := runFrom xorCmap 2 (idx + 17) nd s2
      have hs3Eq : s3 = execInstrSeq 2 xorO3_post8Seq (idx + 17) nd s2 := hp8
      have heTail := xorO3_unrolled_0x53d s0 s3 (done0 + r10Val + 8) (idx + 19) nd hpre
        (by rw [hs3Eq]; exact hrun3) (by rw [hs3Eq]; exact hnf3) (by rw [hs3Eq, heP8])
        (by rw [hs3Eq, heP8]; dsimp only; rw [regUpd_ne _ (by decide), regUpd_ne _ (by decide), hs2Eq, heT8]; dsimp only; rw [hr3Pres .rdi (by decide) (by decide), h1di])
        (by rw [hs3Eq, heP8]; dsimp only; rw [regUpd_ne _ (by decide), regUpd_ne _ (by decide), hs2Eq, heT8]; dsimp only; rw [hr3Pres .rsi (by decide) (by decide), h1si])
        (by rw [hs3Eq, heP8]; dsimp only; rw [regUpd_ne _ (by decide), regUpd_ne _ (by decide), hs2Eq, heT8]; dsimp only; rw [hr3Pres .rcx (by decide) (by decide), h1cx])
        (by rw [hs3Eq, heP8]; dsimp only; rw [regUpd_ne _ (by decide), regUpd_ne _ (by decide), hs2Eq, heT8]; dsimp only; rw [hr3Pres .r8 (by decide) (by decide), h1r8])
        (by rw [hs3Eq, heP8]; dsimp only; rw [regUpd_eq])
        (by rw [hs3Eq, heP8]; dsimp only; rw [regUpd_ne _ (by decide), regUpd_ne _ (by decide), hs2Eq, heT8]; dsimp only; rw [hr3Pres .rbp (by decide) (by decide), h1bp])
        (by rw [hs3Eq, heP8]; dsimp only; exact ⟨by rw [regUpd_ne _ (by decide), regUpd_ne _ (by decide), hs2Eq, heT8]; dsimp only; rw [hr3Pres .r12 (by decide) (by decide)]; dsimp only [s1Regs]; rw [hs1Eq, hePush]; dsimp only; repeat rw [regUpd_ne _ (by decide)]; exact hr12,
              by rw [regUpd_ne _ (by decide), regUpd_ne _ (by decide), hs2Eq, heT8]; dsimp only; rw [hr3Pres .r13 (by decide) (by decide)]; dsimp only [s1Regs]; rw [hs1Eq, hePush]; dsimp only; repeat rw [regUpd_ne _ (by decide)]; exact hr13,
              by rw [regUpd_ne _ (by decide), regUpd_ne _ (by decide), hs2Eq, heT8]; dsimp only; rw [hr3Pres .r14 (by decide) (by decide)]; dsimp only [s1Regs]; rw [hs1Eq, hePush]; dsimp only; repeat rw [regUpd_ne _ (by decide)]; exact hr14,
              by rw [regUpd_ne _ (by decide), regUpd_ne _ (by decide), hs2Eq, heT8]; dsimp only; rw [hr3Pres .r15 (by decide) (by decide)]; dsimp only [s1Regs]; rw [hs1Eq, hePush]; dsimp only; repeat rw [regUpd_ne _ (by decide)]; exact hr15⟩)
        (by rw [hs3Eq, heP8, hs2Eq, heT8]; exact hrRbp8)
        (by rw [hs3Eq, heP8, hs2Eq, heT8]; exact hrRbx8)
        (by rw [hs3Eq, heP8, hs2Eq, heT8]; exact hymm8)
        (by rw [hs3Eq, heP8, hs2Eq, heT8]; exact hmem8Inv)
        (by omega) (by omega)
      rcases heTail with ⟨k, hk⟩
      exact ⟨19 + k, by rw [show 19 + k = 7 + (10 + (2 + k)) by omega, runFrom_add, runFrom_add, runFrom_add]; simpa [Nat.add_assoc] using hk⟩

theorem xorO3_epi16_0x4bf (s0 s : X64State) (done : Nat) (idx : Nat) (nd : Nat → UndefChoice)
    (hpre : XorStreamPre 16 s0)
    (hrun : s.halted = false) (hnf : s.fault = false) (hrip : s.rip = 0x4004bf#64)
    (hrdi : s.regs .rdi = s0.regs .rdi) (hrsi : s.regs .rsi = s0.regs .rsi)
    (hrcx : BitVec.extractLsb' 0 8 (s.regs .rcx) = BitVec.extractLsb' 0 8 (s0.regs .rcx))
    (hr8 : s.regs .r8 = s0.regs .rdx)
    (hrdx : s.regs .rdx = BitVec.ofNat 64 done)
    (hcs : SysVCalleeSavedPreserved s0 s)
    (hymm : UpperYmmCleanOrPreserved s0 s)
    (hinv : XorPrefixInv s0.mem s.mem (s0.regs .rdi) (s0.regs .rsi) (s0.regs .rsp) (s0.regs .rdx).toNat done (BitVec.extractLsb' 0 8 (s0.regs .rcx)))
    (hlt : done < (s0.regs .rdx).toNat)
    (hremHi : (s0.regs .rdx).toNat - done ≤ 31) :
    ∃ steps : Nat,
      let sf := runFrom xorCmap steps idx nd s
      sf.halted = true ∧ sf.fault = false ∧
      SysVCalleeSavedPreserved s0 sf ∧ UpperYmmCleanOrPreserved s0 sf ∧
      XorStreamContractPost 16 s0 sf := by
  have hpre' := hpre
  rcases hpre' with ⟨hnwD, hnwS, hdisj, hstkD, hstkS⟩
  have hlenLt := (s0.regs .rdx).isLt
  have hsub9 : s0.regs .rdx - BitVec.ofNat 64 done = BitVec.ofNat 64 ((s0.regs .rdx).toNat - done) := by
    apply BitVec.eq_of_toNat_eq
    have hdtn : (BitVec.ofNat 64 done).toNat = done := by rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)]
    rw [bv64_sub_toNat_of_le (by rw [hdtn]; omega), hdtn, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)]
  let remBv : BitVec 64 := BitVec.ofNat 64 ((s0.regs .rdx).toNat - done)
  have hremTn : remBv.toNat = (s0.regs .rdx).toNat - done := by
    dsimp only [remBv]; rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)]
  rcases runFrom_of_decodeSeqAt xorO3_epi16Chk_dec idx nd s hrun hnf hrip with ⟨hseq, hrun1, hnf1⟩
  have heChk : execInstrSeq 4 xorO3_epi16ChkSeq idx nd s =
      { s with
        rip := 0x4004cd#64,
        regs := regUpd (regUpd (regUpd s.regs .r9 (s0.regs .rdx)) .r9 remBv) .rax (remBv + 0xffffffffffffffff#64),
        flags := (evalAluN (by decide) .cmp (remBv + 0xffffffffffffffff#64) 0x0e#64
                   (evalAluN (by decide) .sub (s0.regs .rdx) (BitVec.ofNat 64 done) s.flags (nd (idx + 1)).flags).2
                   (nd (idx + 3)).flags).2 } := by
    dsimp only [xorO3_epi16ChkSeq]
    rw [execInstrSeq_succ_cons, exec_movStore_s64_reg, hr8]
    rw [execInstrSeq_succ_cons, exec_aluRmReg_s64_sub]
    dsimp only; rw [regUpd_eq, regUpd_ne _ (by decide), hrdx, hsub9]
    rw [execInstrSeq_succ_cons, exec_lea_s64, evalByteAddr_base_disp]
    dsimp only; rw [regUpd_eq]
    rw [execInstrSeq_succ_cons, exec_aluImm_s64_cmp, execInstrSeq_zero]
    dsimp only; rw [regUpd_eq]
  have hbe := bv64_sub1_cmp_be remBv 14 (by rw [hremTn]; omega) (by decide)
  rw [hremTn] at hbe
  by_cases hle15 : (s0.regs .rdx).toNat - done ≤ 15
  · have hcc : evalCond .be (execInstrSeq 4 xorO3_epi16ChkSeq idx nd s).flags = true := by
      rw [heChk]; dsimp only
      rw [evalCond_be_of_flags, cmp_flags_cf, cmp_flags_zf]
      change (decide ((remBv + 0xffffffffffffffff#64).toNat < 14) || ((remBv + 0xffffffffffffffff#64) - BitVec.ofNat 64 14 == 0#64)) = true
      rw [hbe]; simp [hle15]
    let s1 := runFrom xorCmap 5 idx nd s
    have hs1Eq : s1 = { execInstrSeq 4 xorO3_epi16ChkSeq idx nd s with rip := 0x4005fa#64 } := by
      dsimp only [s1]
      rw [show (5 : Nat) = 4 + 1 by rfl, runFrom_add, hseq, runFrom_succ,
          step_at_concrete xorO3_epi16Chk_jbe _ _ hrun1 hnf1 (by rw [heChk]),
          exec_jcc_taken hcc, runFrom_zero]
      rw [heChk]; rfl
    rcases runFrom_of_decodeSeqAt xorO3_skip16_dec (idx + 5) nd s1
      (by rw [hs1Eq, heChk]; exact hrun) (by rw [hs1Eq, heChk]; exact hnf) (by rw [hs1Eq]) with ⟨hsk, hrun2, hnf2⟩
    have heSk : execInstrSeq 2 xorO3_skip16Seq (idx + 5) nd s1 =
        { s1 with
          rip := 0x400600#64,
          regs := regUpd (regUpd s1.regs .rax (BitVec.ofNat 64 done)) .r10 0#64,
          flags := (evalAluN (by decide) .xor (BitVec.extractLsb' 0 32 (s1.regs .r10)) (BitVec.extractLsb' 0 32 (s1.regs .r10)) s1.flags (nd (idx + 6)).flags).2 } := by
      dsimp only [xorO3_skip16Seq]
      have h1dx : s1.regs .rdx = BitVec.ofNat 64 done := by rw [hs1Eq, heChk]; dsimp only; repeat rw [regUpd_ne _ (by decide)]; exact hrdx
      rw [execInstrSeq_succ_cons, exec_movStore_s64_reg, h1dx]
      rw [execInstrSeq_succ_cons, exec_aluRmReg_s32_xor_self, execInstrSeq_zero]
      dsimp only; rw [regUpd_ne _ (by decide)]
    let s2 := runFrom xorCmap 3 (idx + 5) nd s1
    have hs2Eq : s2 = { execInstrSeq 2 xorO3_skip16Seq (idx + 5) nd s1 with rip := 0x4004fb#64 } := by
      dsimp only [s2]
      rw [show (3 : Nat) = 2 + 1 by rfl, runFrom_add, hsk, runFrom_succ,
          step_at_concrete xorO3_skip16_jmp _ _ hrun2 hnf2 (by rw [heSk]), exec_jmp, runFrom_zero]
      rw [heSk]; rfl
    have hcs2 : SysVCalleeSavedPreserved s0 s2 := by
      unfold SysVCalleeSavedPreserved at hcs ⊢
      rw [hs2Eq, heSk, hs1Eq, heChk]; dsimp only
      exact cs_step_caller (r := .r10) rfl (cs_step_caller (r := .rax) rfl
        (cs_step_caller (r := .rax) rfl (cs_step_caller (r := .r9) rfl (cs_step_caller (r := .r9) rfl hcs))))
    have hsw := xorO3_shrinkwrap_0x4fb s0 s2 done 0 (idx + 8) nd hpre
      (by rw [hs2Eq, heSk, hs1Eq, heChk]; exact hrun) (by rw [hs2Eq, heSk, hs1Eq, heChk]; exact hnf) (by rw [hs2Eq])
      (by rw [hs2Eq, heSk, hs1Eq, heChk]; dsimp only; repeat rw [regUpd_ne _ (by decide)]; exact hrdi)
      (by rw [hs2Eq, heSk, hs1Eq, heChk]; dsimp only; repeat rw [regUpd_ne _ (by decide)]; exact hrsi)
      (by rw [hs2Eq, heSk, hs1Eq, heChk]; dsimp only; repeat rw [regUpd_ne _ (by decide)]; exact hrcx)
      (by rw [hs2Eq, heSk, hs1Eq, heChk]; dsimp only; repeat rw [regUpd_ne _ (by decide)]; exact hr8)
      (by rw [hs2Eq, heSk, hs1Eq, heChk]; dsimp only; repeat rw [regUpd_ne _ (by decide)]; exact hrdx)
      (by rw [hs2Eq, heSk]; dsimp only; exact regUpd_eq _ _ _)
      (by rw [hs2Eq, heSk]; dsimp only; rw [regUpd_ne _ (by decide), regUpd_eq, Nat.add_zero])
      (by rw [hs2Eq, heSk, hs1Eq, heChk]; dsimp only; rw [regUpd_ne _ (by decide), regUpd_ne _ (by decide), regUpd_ne _ (by decide), regUpd_eq])
      hcs2
      (by rw [hs2Eq, heSk, hs1Eq, heChk]; exact hymm)
      (by rw [hs2Eq, heSk, hs1Eq, heChk, Nat.add_zero]; exact hinv)
      (by omega) (by omega)
    rcases hsw with ⟨k, hk⟩
    exact ⟨8 + k, by rw [show 8 + k = 5 + (3 + k) by omega, runFrom_add, runFrom_add]; simpa [Nat.add_assoc] using hk⟩
  · have hcc : evalCond .be (execInstrSeq 4 xorO3_epi16ChkSeq idx nd s).flags = false := by
      rw [heChk]; dsimp only
      rw [evalCond_be_of_flags, cmp_flags_cf, cmp_flags_zf]
      change (decide ((remBv + 0xffffffffffffffff#64).toNat < 14) || ((remBv + 0xffffffffffffffff#64) - BitVec.ofNat 64 14 == 0#64)) = false
      rw [hbe]; simp [hle15]
    let s1 := runFrom xorCmap 5 idx nd s
    have hs1Eq : s1 = { execInstrSeq 4 xorO3_epi16ChkSeq idx nd s with rip := 0x4004d3#64 } := by
      dsimp only [s1]
      rw [show (5 : Nat) = 4 + 1 by rfl, runFrom_add, hseq, runFrom_succ,
          step_at_concrete xorO3_epi16Chk_jbe _ _ hrun1 hnf1 (by rw [heChk]),
          exec_jcc_fall hcc, runFrom_zero]
      rw [heChk]; rfl
    rcases runFrom_of_decodeSeqAt xorO3_epi16Body_dec (idx + 5) nd s1
      (by rw [hs1Eq, heChk]; exact hrun) (by rw [hs1Eq, heChk]; exact hnf) (by rw [hs1Eq]) with ⟨he16d, hrun2, hnf2⟩
    let key8 : BitVec 8 := BitVec.extractLsb' 0 8 (s0.regs .rcx)
    have h1di : s1.regs .rdi = s0.regs .rdi := by rw [hs1Eq, heChk]; dsimp only; repeat rw [regUpd_ne _ (by decide)]; exact hrdi
    have h1si : s1.regs .rsi = s0.regs .rsi := by rw [hs1Eq, heChk]; dsimp only; repeat rw [regUpd_ne _ (by decide)]; exact hrsi
    have h1cx : BitVec.extractLsb' 0 8 (s1.regs .rcx) = key8 := by rw [hs1Eq, heChk]; dsimp only; repeat rw [regUpd_ne _ (by decide)]; exact hrcx
    have h1dx : s1.regs .rdx = BitVec.ofNat 64 done := by rw [hs1Eq, heChk]; dsimp only; repeat rw [regUpd_ne _ (by decide)]; exact hrdx
    have h1r8 : s1.regs .r8 = s0.regs .rdx := by rw [hs1Eq, heChk]; dsimp only; repeat rw [regUpd_ne _ (by decide)]; exact hr8
    have h1r9 : s1.regs .r9 = remBv := by rw [hs1Eq, heChk]; dsimp only; rw [regUpd_ne _ (by decide), regUpd_eq]
    have h1ym : UpperYmmCleanOrPreserved s0 s1 := by rw [hs1Eq, heChk]; exact hymm
    have h1mem : s1.mem = s.mem := by rw [hs1Eq, heChk]
    let splat128 : BitVec 128 := packBytes128 fun _ => key8
    let xor128v : BitVec 128 := splat128 ^^^ readMem128 s.mem (s0.regs .rsi + BitVec.ofNat 64 done)
    let y16_1 := writeXmm128 true s1.ymms y0 (((BitVec.extractLsb' 0 32 (s1.regs .rcx)).zeroExtend 64).zeroExtend 128)
    let y16_2 := writeXmm128 true y16_1 y0 splat128
    let y16_3 := writeXmm128 true y16_2 y0 xor128v
    let mem16 := writeMem128 s.mem (s0.regs .rdi + BitVec.ofNat 64 done) xor128v
    have hwx_lo16 : ∀ (ymms : YmmIdx → BitVec 256) (r : YmmIdx) (v : BitVec 128),
        BitVec.extractLsb' 0 128 (writeXmm128 true ymms r v r) = v := fun ymms r v => by
      rw [writeXmm128_true_eq, ymmUpd_eq, extract_lo128_append]
    have he16Body : execInstrSeq 5 xorO3_epi16BodySeq (idx + 5) nd s1 =
        { s1 with
          rip := 0x4004ea#64,
          ymms := y16_3,
          mem := mem16,
          flags := (evalAluN (by decide) .test (BitVec.extractLsb' 0 8 remBv) 0x0f#8 s1.flags (nd (idx + 9)).flags).2 } := by
      dsimp only [xorO3_epi16BodySeq]
      rw [execInstrSeq_succ_cons, exec_simdMovGprToX_vex32_reg]
      change execInstrSeq 4 _ _ _ { s1 with rip := 0x4004d7#64, ymms := y16_1 } = _
      rw [execInstrSeq_succ_cons, exec_simdBroadcastB_vex128_reg]
      have hb0 : BitVec.extractLsb' 0 8 (y16_1 y0) = key8 := by
        dsimp only [y16_1]; rw [writeXmm128_true_eq, ymmUpd_eq, ← h1cx]
        apply BitVec.eq_of_getLsbD_eq; intro b hb
        rw [BitVec.getLsbD_extractLsb', BitVec.getLsbD_append]
        unfold BitVec.zeroExtend
        simp [hb, show b < 32 by omega, show b < 64 by omega, show b < 128 by omega]
      dsimp only; rw [hb0]
      change execInstrSeq 3 _ _ _ { s1 with rip := 0x4004dc#64, ymms := y16_2 } = _
      rw [execInstrSeq_succ_cons, exec_simdBitwise_vex128_xor_mem, evalByteAddr_base_idx0]
      dsimp only; rw [show BitVec.extractLsb' 0 128 (y16_2 y0) = splat128 from hwx_lo16 _ _ _, h1si, h1dx, h1mem]
      change execInstrSeq 2 _ _ _ { s1 with rip := 0x4004e1#64, ymms := y16_3, mem := s.mem } = _
      rw [execInstrSeq_succ_cons, exec_simdMovStore_vex128_mem, evalByteAddr_base_idx0]
      dsimp only; rw [show BitVec.extractLsb' 0 128 (y16_3 y0) = xor128v from hwx_lo16 _ _ _, h1di, h1dx]
      rw [execInstrSeq_succ_cons, exec_alu8Imm_test_lo8, execInstrSeq_zero]
      dsimp only; rw [h1r9]
    have hmem16Inv : XorPrefixInv s0.mem mem16 (s0.regs .rdi) (s0.regs .rsi) (s0.regs .rsp) (s0.regs .rdx).toNat (done + 16) key8 := by
      apply xorPrefix_step_block hnwD hinv (by omega)
      · intro j hj
        dsimp only [mem16]
        have hdp : s0.regs .rdi + BitVec.ofNat 64 (done + j) = (s0.regs .rdi + BitVec.ofNat 64 done) + BitVec.ofNat 64 j :=
          (bv64_add_ofNat_assoc _ _ _).symm
        rw [hdp, writeMem128_at_offset _ _ _ j hj]
        dsimp only [xor128v, splat128]
        rw [xor128_splat_byte_at s.mem (s0.regs .rsi + BitVec.ofNat 64 done) key8 ⟨j, hj⟩]
        dsimp only; rw [bv64_add_ofNat_assoc, xorPrefix_src_eq hnwS hdisj hstkS hinv (by omega)]
      · intro addr hout
        dsimp only [mem16]; apply writeMem128_byte_ne; intro j hj
        rw [bv64_add_ofNat_assoc]; exact hout j hj
    have hymm16 : AllUpperYmmClean s0 → ∀ idx : YmmIdx, BitVec.extractLsb' 128 128 (y16_3 idx) = 0#128 :=
      fun h0 => writeXmm128_true_preserves_clean _ _ _ (writeXmm128_true_preserves_clean _ _ _
        (writeXmm128_true_preserves_clean _ _ _ (h1ym h0)))
    have hcs1 : SysVCalleeSavedPreserved s0 s1 := by
      unfold SysVCalleeSavedPreserved at hcs ⊢
      rw [hs1Eq, heChk]; dsimp only
      exact cs_step_caller (r := .rax) rfl (cs_step_caller (r := .r9) rfl (cs_step_caller (r := .r9) rfl hcs))
    have htest15 := bv64_test_lo8_15_eq remBv
    rw [hremTn] at htest15
    by_cases hmod16 : ((s0.regs .rdx).toNat - done) % 16 = 0
    · have hcc16 : evalCond .e (execInstrSeq 5 xorO3_epi16BodySeq (idx + 5) nd s1).flags = true := by
        rw [he16Body]; dsimp only; rw [evalCond_e_of_zf_true (by rw [test_flags_zf, htest15]; simp [hmod16])]
      have hlen16 : done + 16 = (s0.regs .rdx).toNat := by omega
      rw [hlen16] at hmem16Inv
      let sRet := runFrom xorCmap 6 (idx + 5) nd s1
      have hsRetEq : sRet = { execInstrSeq 5 xorO3_epi16BodySeq (idx + 5) nd s1 with rip := 0x400609#64 } := by
        dsimp only [sRet]
        rw [show (6 : Nat) = 5 + 1 by rfl, runFrom_add, he16d, runFrom_succ,
            step_at_concrete xorO3_epi16_je _ _ hrun2 hnf2 (by rw [he16Body]),
            exec_jcc_taken hcc16, runFrom_zero]
        rw [he16Body]; rfl
      have hsf : runFrom xorCmap 1 (idx + 5 + 6) nd sRet =
          { s1 with
            rip := 0x400609#64,
            ymms := y16_3,
            mem := mem16,
            flags := (evalAluN (by decide) .test (BitVec.extractLsb' 0 8 remBv) 0x0f#8 s1.flags (nd (idx + 9)).flags).2,
            halted := true } := by
        rw [hsRetEq, he16Body, runFrom_succ,
            step_at_concrete xorO3_ret609 _ _ (by rw [hs1Eq, heChk]; exact hrun) (by rw [hs1Eq, heChk]; exact hnf) rfl,
            exec_ret, runFrom_zero]
      refine ⟨12, ?_⟩
      dsimp only
      rw [show (12 : Nat) = 5 + (6 + 1) by rfl, runFrom_add, runFrom_add]
      change (runFrom xorCmap 1 (idx + 5 + 6) nd sRet).halted = true ∧
        (runFrom xorCmap 1 (idx + 5 + 6) nd sRet).fault = false ∧
        SysVCalleeSavedPreserved s0 (runFrom xorCmap 1 (idx + 5 + 6) nd sRet) ∧
        UpperYmmCleanOrPreserved s0 (runFrom xorCmap 1 (idx + 5 + 6) nd sRet) ∧
        XorStreamContractPost 16 s0 (runFrom xorCmap 1 (idx + 5 + 6) nd sRet)
      rw [hsf]
      exact ⟨rfl, by rw [hs1Eq, heChk]; exact hnf, hcs1, hymm16, hmem16Inv.2⟩
    · have hcc16 : evalCond .e (execInstrSeq 5 xorO3_epi16BodySeq (idx + 5) nd s1).flags = false := by
        rw [he16Body]; dsimp only; rw [evalCond_e_of_zf_false (by rw [test_flags_zf, htest15]; simp [hmod16])]
      let s2 := runFrom xorCmap 6 (idx + 5) nd s1
      have hs2Eq : s2 = { execInstrSeq 5 xorO3_epi16BodySeq (idx + 5) nd s1 with rip := 0x4004f0#64 } := by
        dsimp only [s2]
        rw [show (6 : Nat) = 5 + 1 by rfl, runFrom_add, he16d, runFrom_succ,
            step_at_concrete xorO3_epi16_je _ _ hrun2 hnf2 (by rw [he16Body]),
            exec_jcc_fall hcc16, runFrom_zero]
        rw [he16Body]; rfl
      rcases runFrom_of_decodeSeqAt xorO3_post16_dec (idx + 11) nd s2
        (by rw [hs2Eq, he16Body, hs1Eq, heChk]; exact hrun)
        (by rw [hs2Eq, he16Body, hs1Eq, heChk]; exact hnf) (by rw [hs2Eq]) with ⟨hp16, hrun3, hnf3⟩
      have hmask16 : remBv &&& 0xfffffffffffffff0#64 = BitVec.ofNat 64 16 := by
        apply BitVec.eq_of_toNat_eq
        rw [bv64_and_neg16_toNat, hremTn, BitVec.toNat_ofNat]; omega
      have heP16 : execInstrSeq 3 xorO3_post16Seq (idx + 11) nd s2 =
          { s2 with
            rip := 0x4004fb#64,
            regs := regUpd (regUpd (regUpd s2.regs .r10 remBv) .r10 (BitVec.ofNat 64 16)) .rax (BitVec.ofNat 64 (done + 16)),
            flags := (evalAluN (by decide) .and remBv 0xfffffffffffffff0#64 s2.flags (nd (idx + 12)).flags).2 } := by
        dsimp only [xorO3_post16Seq]
        have h2r9 : s2.regs .r9 = remBv := by rw [hs2Eq, he16Body]; exact h1r9
        have h2dx : s2.regs .rdx = BitVec.ofNat 64 done := by rw [hs2Eq, he16Body]; exact h1dx
        rw [execInstrSeq_succ_cons, exec_movStore_s64_reg, h2r9]
        rw [execInstrSeq_succ_cons, exec_aluImm_s64_and]
        dsimp only; rw [regUpd_eq, hmask16]
        rw [execInstrSeq_succ_cons, exec_lea_s64, evalByteAddr_base_idx0, execInstrSeq_zero]
        dsimp only; rw [regUpd_ne _ (by decide), regUpd_ne _ (by decide), regUpd_eq, h2dx, bv64_ofNat_add]
      let s3 := runFrom xorCmap 3 (idx + 11) nd s2
      have hs3Eq : s3 = execInstrSeq 3 xorO3_post16Seq (idx + 11) nd s2 := hp16
      have hcs3 : SysVCalleeSavedPreserved s0 s3 := by
        unfold SysVCalleeSavedPreserved at hcs1 ⊢
        rw [hs3Eq, heP16]; dsimp only
        have hcs2 : s2.regs .rsp = s0.regs .rsp ∧ s2.regs .rbx = s0.regs .rbx ∧ s2.regs .rbp = s0.regs .rbp ∧
            s2.regs .r12 = s0.regs .r12 ∧ s2.regs .r13 = s0.regs .r13 ∧ s2.regs .r14 = s0.regs .r14 ∧ s2.regs .r15 = s0.regs .r15 := by
          rw [hs2Eq, he16Body]; exact hcs1
        exact cs_step_caller (r := .rax) rfl (cs_step_caller (r := .r10) rfl (cs_step_caller (r := .r10) rfl hcs2))
      have hsw := xorO3_shrinkwrap_0x4fb s0 s3 done 16 (idx + 14) nd hpre
        (by rw [hs3Eq]; exact hrun3) (by rw [hs3Eq]; exact hnf3) (by rw [hs3Eq, heP16])
        (by rw [hs3Eq, heP16]; dsimp only; repeat rw [regUpd_ne _ (by decide)]; rw [hs2Eq, he16Body]; exact h1di)
        (by rw [hs3Eq, heP16]; dsimp only; repeat rw [regUpd_ne _ (by decide)]; rw [hs2Eq, he16Body]; exact h1si)
        (by rw [hs3Eq, heP16]; dsimp only; repeat rw [regUpd_ne _ (by decide)]; rw [hs2Eq, he16Body]; exact h1cx)
        (by rw [hs3Eq, heP16]; dsimp only; repeat rw [regUpd_ne _ (by decide)]; rw [hs2Eq, he16Body]; exact h1r8)
        (by rw [hs3Eq, heP16]; dsimp only; repeat rw [regUpd_ne _ (by decide)]; rw [hs2Eq, he16Body]; exact h1dx)
        (by rw [hs3Eq, heP16]; dsimp only; rw [regUpd_ne _ (by decide), regUpd_eq])
        (by rw [hs3Eq, heP16]; dsimp only; rw [regUpd_eq])
        (by rw [hs3Eq, heP16]; dsimp only; repeat rw [regUpd_ne _ (by decide)]; rw [hs2Eq, he16Body]; exact h1r9)
        hcs3
        (by rw [hs3Eq, heP16, hs2Eq, he16Body]; exact hymm16)
        (by rw [hs3Eq, heP16, hs2Eq, he16Body]; exact hmem16Inv)
        (by omega) (by omega)
      rcases hsw with ⟨k, hk⟩
      exact ⟨14 + k, by rw [show 14 + k = 5 + (6 + (3 + k)) by omega, runFrom_add, runFrom_add, runFrom_add]; simpa [Nat.add_assoc] using hk⟩

end UntrustedCObjXorAvx2Tail
