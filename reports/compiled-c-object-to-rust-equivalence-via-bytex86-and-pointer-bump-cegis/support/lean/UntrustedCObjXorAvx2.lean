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
import UntrustedCObjXorAvx2Tail

/-!
# `UntrustedCObjXorAvx2`

Top-level equivalence proof for `gcc 15.2.0 -O3 -mavx2` `c_xor_stream`
(`cFfiKernelsO3Avx2Obj` at `0x450`, `stackReserve = 16`, `0` `sorry`, `0` `isPartial`):
- `prove_c_xor_stream_o3_avx2`: proves `len = 0`, alias fallback scalar loop
  (`0x5c8`), `32B` AVX2 hot loop (`0x4a0`) + `vzeroupper`, and joins
  `UntrustedCObjXorAvx2Tail.xorO3_epi16_0x4bf` (`16B` VEX-128 + shrink-wrapped
  `push rbp; push rbx` `8B` `mov bh, bl` + `vpshuflw` + `1..7B` unrolled tail).
- `c_xor_stream_o3_avx2_overlap_guard_discharged`: proves safe-Rust `Tree Borrows`
  disjointness (`DisjointSlices`) unconditionally discharges GCC's runtime
  non-`restrict` overlap guard for `len ≥ 32`.
-/

namespace UntrustedCObjXorAvx2

open ByteX86Gcc
open RustFfiSpecs
open CompiledCObjImages
open UntrustedCObjHints
open UntrustedCObjSimdHelpers
open UntrustedCObjXorAvx2Tail

private abbrev y0 : YmmIdx := ⟨0, by decide⟩
private abbrev y1 : YmmIdx := ⟨1, by decide⟩

/-! ## Section 1: Reflected Hot-Loop & Alias-Guard Decodes -/

private theorem xorO3_test : decodeX64 (fetchWindow16 xorCmap 0x400450#64) =
    .ok (.aluRmReg .s64 .test (.reg .rdx) .rdx) 3 := decodeAt_of_check rfl
private theorem xorO3_je0 : decodeX64 (fetchWindow16 xorCmap 0x400453#64) =
    .ok (.jccRel .e 0x00000000000001b0#64) 6 := decodeAt_of_check rfl
private theorem xorO3_vzu605 : decodeX64 (fetchWindow16 xorCmap 0x400605#64) =
    .ok .vzeroupper 3 := decodeAt_of_check rfl
private theorem xorO3_ret608 : decodeX64 (fetchWindow16 xorCmap 0x400608#64) =
    .ok .ret64 1 := decodeAt_of_check rfl

private def xorO3_aliasSeq : List (X64Instr × BitVec 64) := [
  (.lea .s64 .rax { base := some .rdi, disp := 0xffffffffffffffff#64 }, 0x40045d#64),
  (.movStore .s64 (.reg .r8) .rdx, 0x400460#64),
  (.aluRmReg .s64 .sub (.reg .rax) .rsi, 0x400463#64),
  (.aluImm .s64 .cmp (.reg .rax) 0x1e#64, 0x400467#64)
]
private theorem xorO3_alias_dec : decodeSeqAt xorCmap 4 0x400459#64 = some xorO3_aliasSeq :=
  decodeSeqAt_of_check rfl rfl
private theorem xorO3_alias_jbe : decodeX64 (fetchWindow16 xorCmap 0x400467#64) =
    .ok (.jccRel .be 0x000000000000015b#64) 6 := decodeAt_of_check rfl

private def xorO3_lenChkSeq : List (X64Instr × BitVec 64) := [
  (.lea .s64 .rax { base := some .rdx, disp := 0xffffffffffffffff#64 }, 0x400471#64),
  (.aluImm .s64 .cmp (.reg .rax) 0x1e#64, 0x400475#64)
]
private theorem xorO3_lenChk_dec : decodeSeqAt xorCmap 2 0x40046d#64 = some xorO3_lenChkSeq :=
  decodeSeqAt_of_check rfl rfl
private theorem xorO3_lenChk_jbe : decodeX64 (fetchWindow16 xorCmap 0x400475#64) =
    .ok (.jccRel .be 0x0000000000000178#64) 6 := decodeAt_of_check rfl

private theorem xorO3_skip32_xor : decodeX64 (fetchWindow16 xorCmap 0x4005f3#64) =
    .ok (.aluRmReg .s32 .xor (.reg .rdx) .rdx) 2 := decodeAt_of_check rfl
private theorem xorO3_skip32_jmp : decodeX64 (fetchWindow16 xorCmap 0x4005f5#64) =
    .ok (.jmpRel 0xfffffffffffffec5#64) 5 := decodeAt_of_check rfl

private def xorO3_avxPreSeq : List (X64Instr × BitVec 64) := [
  (.simdMovGprToX true false y1 (.reg .rcx), 0x40047f#64),
  (.aluImm .s64 .and (.reg .rdx) 0xffffffffffffffe0#64, 0x400483#64),
  (.aluRmReg .s32 .xor (.reg .rax) .rax, 0x400485#64),
  (.simdBroadcastB .vex256 y1 (.reg y1), 0x40048a#64),
  (.nop, 0x400495#64),
  (.nop, 0x4004a0#64)
]
private theorem xorO3_avxPre_dec : decodeSeqAt xorCmap 6 0x40047b#64 = some xorO3_avxPreSeq :=
  decodeSeqAt_of_check rfl rfl

private def xorO3_avxLoopSeq : List (X64Instr × BitVec 64) := [
  (.simdBitwise .vex256 .xor y0 y1 (.mem { base := some .rsi, index := some (.rax, 0) }), 0x4004a5#64),
  (.simdMovStore .vex256 (.mem { base := some .rdi, index := some (.rax, 0) }) y0, 0x4004aa#64),
  (.aluImm .s64 .add (.reg .rax) 0x20#64, 0x4004ae#64),
  (.aluRmReg .s64 .cmp (.reg .rax) .rdx, 0x4004b1#64)
]
private theorem xorO3_avxLoop_dec : decodeSeqAt xorCmap 4 0x4004a0#64 = some xorO3_avxLoopSeq :=
  decodeSeqAt_of_check rfl rfl
private theorem xorO3_avxLoop_jne : decodeX64 (fetchWindow16 xorCmap 0x4004b1#64) =
    .ok (.jccRel .ne 0xffffffffffffffed#64) 2 := decodeAt_of_check rfl

private theorem xorO3_postAvx_cmp : decodeX64 (fetchWindow16 xorCmap 0x4004b3#64) =
    .ok (.aluRmReg .s64 .cmp (.reg .r8) .rdx) 3 := decodeAt_of_check rfl
private theorem xorO3_postAvx_je : decodeX64 (fetchWindow16 xorCmap 0x4004b6#64) =
    .ok (.jccRel .e 0x0000000000000149#64) 6 := decodeAt_of_check rfl
private theorem xorO3_vzu4bc : decodeX64 (fetchWindow16 xorCmap 0x4004bc#64) =
    .ok .vzeroupper 3 := decodeAt_of_check rfl

private def xorO3_fallPreSeq : List (X64Instr × BitVec 64) := [
  (.aluRmReg .s32 .xor (.reg .rax) .rax, 0x4005ca#64),
  (.nop, 0x4005d5#64),
  (.nop, 0x4005e0#64)
]
private theorem xorO3_fallPre_dec : decodeSeqAt xorCmap 3 0x4005c8#64 = some xorO3_fallPreSeq :=
  decodeSeqAt_of_check rfl rfl

private def xorO3_fallLoopSeq : List (X64Instr × BitVec 64) := [
  (.movzx8 .s32 .rdx (.mem8 { base := some .rsi, index := some (.rax, 0) }), 0x4005e4#64),
  (.aluRmReg .s32 .xor (.reg .rdx) .rcx, 0x4005e6#64),
  (.mov8Store (.mem8 { base := some .rdi, index := some (.rax, 0) }) (.lo8 .rdx), 0x4005e9#64),
  (.aluImm .s64 .add (.reg .rax) 1#64, 0x4005ed#64),
  (.aluRmReg .s64 .cmp (.reg .r8) .rax, 0x4005f0#64)
]
private theorem xorO3_fallLoop_dec : decodeSeqAt xorCmap 5 0x4005e0#64 = some xorO3_fallLoopSeq :=
  decodeSeqAt_of_check rfl rfl
private theorem xorO3_fallLoop_jne : decodeX64 (fetchWindow16 xorCmap 0x4005f0#64) =
    .ok (.jccRel .ne 0xffffffffffffffee#64) 2 := decodeAt_of_check rfl
private theorem xorO3_fall_ret : decodeX64 (fetchWindow16 xorCmap 0x4005f2#64) =
    .ok .ret64 1 := decodeAt_of_check rfl

/-! ## Section 2: `32B` AVX2 Loop & Scalar Alias-Fallback Loop Inductions -/

private theorem xorO3_avx_step (s0 s : X64State) (hpre : XorStreamPre 16 s0) (nd : Nat → UndefChoice)
    (q done idx : Nat)
    (hstep : done + 32 ≤ q * 32) (hqle : q * 32 ≤ (s0.regs .rdx).toNat)
    (hrun : s.halted = false) (hnf : s.fault = false) (hrip : s.rip = 0x4004a0#64)
    (hrdi : s.regs .rdi = s0.regs .rdi) (hrsi : s.regs .rsi = s0.regs .rsi)
    (hrcx : BitVec.extractLsb' 0 8 (s.regs .rcx) = BitVec.extractLsb' 0 8 (s0.regs .rcx))
    (hr8 : s.regs .r8 = s0.regs .rdx)
    (hrdx : s.regs .rdx = BitVec.ofNat 64 (q * 32))
    (hrax : s.regs .rax = BitVec.ofNat 64 done)
    (hy1 : s.ymms y1 = packBytes256 (fun _ => BitVec.extractLsb' 0 8 (s0.regs .rcx)))
    (hcs : SysVCalleeSavedPreserved s0 s)
    (hinv : XorPrefixInv s0.mem s.mem (s0.regs .rdi) (s0.regs .rsi) (s0.regs .rsp) (s0.regs .rdx).toNat
      done (BitVec.extractLsb' 0 8 (s0.regs .rcx))) :
    let s' := runFrom xorCmap 5 idx nd s
    s'.halted = false ∧ s'.fault = false ∧
    s'.rip = (if done + 32 = q * 32 then 0x4004b3#64 else 0x4004a0#64) ∧
    s'.regs .rdi = s0.regs .rdi ∧ s'.regs .rsi = s0.regs .rsi ∧
    BitVec.extractLsb' 0 8 (s'.regs .rcx) = BitVec.extractLsb' 0 8 (s0.regs .rcx) ∧
    s'.regs .r8 = s0.regs .rdx ∧ s'.regs .rdx = BitVec.ofNat 64 (q * 32) ∧
    s'.regs .rax = BitVec.ofNat 64 (done + 32) ∧
    s'.ymms y1 = packBytes256 (fun _ => BitVec.extractLsb' 0 8 (s0.regs .rcx)) ∧
    SysVCalleeSavedPreserved s0 s' ∧
    XorPrefixInv s0.mem s'.mem (s0.regs .rdi) (s0.regs .rsi) (s0.regs .rsp) (s0.regs .rdx).toNat
      (done + 32) (BitVec.extractLsb' 0 8 (s0.regs .rcx)) := by
  rcases hpre with ⟨hnwD, hnwS, hdisj, hstkD, hstkS⟩
  dsimp only
  rw [show (5 : Nat) = 4 + 1 by rfl, runFrom_add]
  rcases runFrom_of_decodeSeqAt xorO3_avxLoop_dec idx nd s hrun hnf hrip with ⟨hseq, hrun1, hnf1⟩
  rw [hseq]
  let key8 := BitVec.extractLsb' 0 8 (s0.regs .rcx)
  let xval : BitVec 256 :=
    (BitVec.extractLsb' 128 128 (packBytes256 fun _ => key8) ^^^ BitVec.extractLsb' 128 128 (readMem256 s.mem (s0.regs .rsi + BitVec.ofNat 64 done))) ++
    (BitVec.extractLsb' 0 128 (packBytes256 fun _ => key8) ^^^ BitVec.extractLsb' 0 128 (readMem256 s.mem (s0.regs .rsi + BitVec.ofNat 64 done)))
  have hadd32 : BitVec.ofNat 64 done + 0x20#64 = BitVec.ofNat 64 (done + 32) := by
    change BitVec.ofNat 64 done + BitVec.ofNat 64 32 = BitVec.ofNat 64 (done + 32)
    exact bv64_ofNat_add done 32
  have he : execInstrSeq 4 xorO3_avxLoopSeq idx nd s =
      { s with
        rip := 0x4004b1#64,
        regs := regUpd s.regs .rax (BitVec.ofNat 64 (done + 32)),
        ymms := ymmUpd s.ymms y0 xval,
        mem := writeMem256 s.mem (s0.regs .rdi + BitVec.ofNat 64 done) xval,
        flags := (evalAluN (by decide) .cmp (BitVec.ofNat 64 (done + 32)) (BitVec.ofNat 64 (q * 32))
                   (evalAluN (by decide) .add (BitVec.ofNat 64 done) 0x20#64 s.flags (nd (idx + 2)).flags).2
                   (nd (idx + 3)).flags).2 } := by
    dsimp only [xorO3_avxLoopSeq]
    rw [execInstrSeq_succ_cons, exec_simdBitwise_vex256_xor_mem, evalByteAddr_base_idx0, hrsi, hrax, hy1]
    rw [execInstrSeq_succ_cons, exec_simdMovStore_vex256_mem, evalByteAddr_base_idx0]
    dsimp only; rw [hrdi, hrax, ymmUpd_eq]
    rw [execInstrSeq_succ_cons, exec_aluImm_s64_add]
    dsimp only; rw [hrax, hadd32]
    rw [execInstrSeq_succ_cons, exec_aluRmReg_s64_cmp, execInstrSeq_zero]
    dsimp only; rw [regUpd_eq, regUpd_ne _ (by decide), hrdx]
  rw [he] at hrun1 hnf1 ⊢
  have hinv' : XorPrefixInv s0.mem (writeMem256 s.mem (s0.regs .rdi + BitVec.ofNat 64 done) xval)
      (s0.regs .rdi) (s0.regs .rsi) (s0.regs .rsp) (s0.regs .rdx).toNat (done + 32) key8 := by
    apply xorPrefix_step_block hnwD hinv (by omega)
    · intro j hj
      have hdp : s0.regs .rdi + BitVec.ofNat 64 (done + j) = (s0.regs .rdi + BitVec.ofNat 64 done) + BitVec.ofNat 64 j :=
        (bv64_add_ofNat_assoc _ _ _).symm
      rw [hdp, writeMem256_at_offset _ _ _ j hj]
      dsimp only [xval]
      rw [xor256_splat_byte_at s.mem (s0.regs .rsi + BitVec.ofNat 64 done) key8 ⟨j, hj⟩]
      dsimp only; rw [bv64_add_ofNat_assoc, xorPrefix_src_eq hnwS hdisj hstkS hinv (by omega)]
    · intro addr hout
      apply writeMem256_byte_ne; intro j hj; rw [bv64_add_ofNat_assoc]; exact hout j hj
  rw [runFrom_succ, step_at_concrete xorO3_avxLoop_jne _ _ hrun1 hnf1 rfl, runFrom_zero]
  by_cases hdone : done + 32 = q * 32
  · rw [exec_jcc_fall (by dsimp only; rw [hdone]; exact evalCond_ne_of_zf_true (by rw [cmp_flags_zf, cmp_sub_self_zero]))]
    simp only [hdone, ite_true]
    refine ⟨hrun, hnf, rfl, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, hdone ▸ hinv'⟩
    · rw [regUpd_ne _ (by decide), hrdi]
    · rw [regUpd_ne _ (by decide), hrsi]
    · rw [regUpd_ne _ (by decide), hrcx]
    · rw [regUpd_ne _ (by decide), hr8]
    · rw [regUpd_ne _ (by decide), hrdx]
    · rw [regUpd_eq]
    · rw [ymmUpd_ne _ (by decide : y1 ≠ y0), hy1]
    · unfold SysVCalleeSavedPreserved at hcs ⊢; dsimp only; exact cs_step_caller (r := .rax) rfl hcs
  · have hne : BitVec.ofNat 64 (done + 32) ≠ BitVec.ofNat 64 (q * 32) := by
      intro heq; have hlt64 := (s0.regs .rdx).isLt; have ht := congrArg BitVec.toNat heq
      have h1 : done + 32 < 2 ^ 64 := Nat.lt_of_le_of_lt (Nat.le_trans hstep hqle) hlt64
      have h2 : q * 32 < 2 ^ 64 := Nat.lt_of_le_of_lt hqle hlt64
      rw [BitVec.toNat_ofNat, BitVec.toNat_ofNat, Nat.mod_eq_of_lt h1, Nat.mod_eq_of_lt h2] at ht
      exact hdone ht
    rw [exec_jcc_taken (by dsimp only; exact evalCond_ne_of_zf_false (by rw [cmp_flags_zf, cmp_sub_zero_false_of_ne hne]))]
    simp only [hdone, ite_false]
    refine ⟨hrun, hnf, rfl, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, hinv'⟩
    · rw [regUpd_ne _ (by decide), hrdi]
    · rw [regUpd_ne _ (by decide), hrsi]
    · rw [regUpd_ne _ (by decide), hrcx]
    · rw [regUpd_ne _ (by decide), hr8]
    · rw [regUpd_ne _ (by decide), hrdx]
    · rw [regUpd_eq]
    · rw [ymmUpd_ne _ (by decide : y1 ≠ y0), hy1]
    · unfold SysVCalleeSavedPreserved at hcs ⊢; dsimp only; exact cs_step_caller (r := .rax) rfl hcs

private theorem nat_mul32_step0 (q : Nat) (h : (0 + 1) * 32 ≤ q * 32) :
    (q - 1) * 32 + 32 ≤ q * 32 ∧ (q - 1) * 32 + 32 = q * 32 := by omega

private theorem nat_mul32_stepM (q m : Nat) (h : (m + 1 + 1) * 32 ≤ q * 32) :
    (q - (m + 1 + 1)) * 32 + 32 ≤ q * 32 ∧
    ¬ ((q - (m + 1 + 1)) * 32 + 32 = q * 32) ∧
    (q - (m + 1 + 1)) * 32 + 32 = (q - (m + 1)) * 32 ∧
    (m + 1) * 32 ≤ q * 32 ∧
    5 * (m + 1 + 1) = 5 + 5 * (m + 1) := by omega

private theorem xorO3_avx_loop (s0 : X64State) (hpre : XorStreamPre 16 s0) (nd : Nat → UndefChoice)
    (q : Nat) :
    ∀ (k : Nat) (idx : Nat) (s : X64State),
      (k + 1) * 32 ≤ q * 32 → q * 32 ≤ (s0.regs .rdx).toNat →
      s.halted = false → s.fault = false → s.rip = 0x4004a0#64 →
      s.regs .rdi = s0.regs .rdi → s.regs .rsi = s0.regs .rsi →
      BitVec.extractLsb' 0 8 (s.regs .rcx) = BitVec.extractLsb' 0 8 (s0.regs .rcx) →
      s.regs .r8 = s0.regs .rdx →
      s.regs .rdx = BitVec.ofNat 64 (q * 32) →
      s.regs .rax = BitVec.ofNat 64 ((q - (k + 1)) * 32) →
      s.ymms y1 = packBytes256 (fun _ => BitVec.extractLsb' 0 8 (s0.regs .rcx)) →
      SysVCalleeSavedPreserved s0 s →
      XorPrefixInv s0.mem s.mem (s0.regs .rdi) (s0.regs .rsi) (s0.regs .rsp) (s0.regs .rdx).toNat
        ((q - (k + 1)) * 32) (BitVec.extractLsb' 0 8 (s0.regs .rcx)) →
      let sf := runFrom xorCmap (5 * (k + 1)) idx nd s
      sf.halted = false ∧ sf.fault = false ∧ sf.rip = 0x4004b3#64 ∧
      sf.regs .rdi = s0.regs .rdi ∧ sf.regs .rsi = s0.regs .rsi ∧
      BitVec.extractLsb' 0 8 (sf.regs .rcx) = BitVec.extractLsb' 0 8 (s0.regs .rcx) ∧
      sf.regs .r8 = s0.regs .rdx ∧ sf.regs .rdx = BitVec.ofNat 64 (q * 32) ∧
      SysVCalleeSavedPreserved s0 sf ∧
      XorPrefixInv s0.mem sf.mem (s0.regs .rdi) (s0.regs .rsi) (s0.regs .rsp) (s0.regs .rdx).toNat
        (q * 32) (BitVec.extractLsb' 0 8 (s0.regs .rcx)) := by
  intro k
  induction k with
  | zero =>
    intro idx s hle hqle hrun hnf hrip hrdi hrsi hrcx hr8 hrdx hrax hy1 hcs hinv
    rcases nat_mul32_step0 q hle with ⟨hstep0, heq⟩
    have h1 := xorO3_avx_step s0 s hpre nd q ((q - 1) * 32) idx hstep0 hqle
      hrun hnf hrip hrdi hrsi hrcx hr8 hrdx hrax hy1 hcs hinv
    simp only [heq, ite_true] at h1
    rcases h1 with ⟨hr, hf, hri, hdi, hsi, hcx, h8, hdx, _, _, hcs', hinv'⟩
    exact ⟨hr, hf, hri, hdi, hsi, hcx, h8, hdx, hcs', hinv'⟩
  | succ m ih =>
    intro idx s hle hqle hrun hnf hrip hrdi hrsi hrcx hr8 hrdx hrax hy1 hcs hinv
    rcases nat_mul32_stepM q m hle with ⟨hstepM, hne, hnext, hleM, h5m⟩
    dsimp only
    rw [h5m, runFrom_add]
    have h1 := xorO3_avx_step s0 s hpre nd q ((q - (m + 1 + 1)) * 32) idx hstepM hqle
      hrun hnf hrip hrdi hrsi hrcx hr8 hrdx hrax hy1 hcs hinv
    simp only [hne, ite_false] at h1
    rw [hnext] at h1
    rcases h1 with ⟨hr, hf, hri, hdi, hsi, hcx, h8, hdx, hax, hy1', hcs', hinv'⟩
    exact ih (idx + 5) (runFrom xorCmap 5 idx nd s) hleM hqle hr hf hri hdi hsi hcx h8 hdx hax hy1' hcs' hinv'

private theorem xorO3_fallback_loop (s0 : X64State) (hpre : XorStreamPre 16 s0) (nd : Nat → UndefChoice) :
    ∀ (k : Nat) (idx : Nat) (s : X64State),
      k + 1 ≤ (s0.regs .rdx).toNat →
      s.halted = false → s.fault = false → s.rip = 0x4005e0#64 →
      s.regs .rdi = s0.regs .rdi → s.regs .rsi = s0.regs .rsi →
      BitVec.extractLsb' 0 8 (s.regs .rcx) = BitVec.extractLsb' 0 8 (s0.regs .rcx) →
      s.regs .r8 = s0.regs .rdx →
      s.regs .rax = BitVec.ofNat 64 ((s0.regs .rdx).toNat - (k + 1)) →
      s.ymms = s0.ymms →
      SysVCalleeSavedPreserved s0 s →
      XorPrefixInv s0.mem s.mem (s0.regs .rdi) (s0.regs .rsi) (s0.regs .rsp) (s0.regs .rdx).toNat
        ((s0.regs .rdx).toNat - (k + 1)) (BitVec.extractLsb' 0 8 (s0.regs .rcx)) →
      let sf := runFrom xorCmap (6 * (k + 1)) idx nd s
      sf.halted = false ∧ sf.fault = false ∧ sf.rip = 0x4005f2#64 ∧
      sf.ymms = s0.ymms ∧ SysVCalleeSavedPreserved s0 sf ∧
      XorStreamContractPost 16 s0 sf := by
  have hpre' := hpre
  rcases hpre' with ⟨hnwD, hnwS, hdisj, hstkD, hstkS⟩
  intro k
  induction k with
  | zero =>
    intro idx s hle hrun hnf hrip hrdi hrsi hrcx hr8 hrax hymm hcs hinv
    dsimp only
    rw [show 6 * (0 + 1) = 5 + 1 by rfl, runFrom_add]
    rcases runFrom_of_decodeSeqAt xorO3_fallLoop_dec idx nd s hrun hnf hrip with ⟨hseq, hrun1, hnf1⟩
    rw [hseq]
    let pos := (s0.regs .rdx).toNat - 1
    have hpos1 : pos + 1 = (s0.regs .rdx).toNat := by dsimp only [pos]; omega
    have hadd1 : BitVec.ofNat 64 pos + 1#64 = s0.regs .rdx := by
      change BitVec.ofNat 64 pos + BitVec.ofNat 64 1 = s0.regs .rdx
      rw [bv64_ofNat_add, hpos1, BitVec.ofNat_toNat, BitVec.setWidth_eq]
    have hsrc := xorPrefix_src_eq hnwS hdisj hstkS hinv (by omega : pos < (s0.regs .rdx).toNat)
    have he : execInstrSeq 5 xorO3_fallLoopSeq idx nd s =
        { s with
          rip := 0x4005f0#64,
          regs := regUpd (regUpd (regUpd s.regs .rdx ((s0.mem (s0.regs .rsi + BitVec.ofNat 64 pos)).zeroExtend 64))
            .rdx ((BitVec.extractLsb' 0 32 ((s0.mem (s0.regs .rsi + BitVec.ofNat 64 pos)).zeroExtend 64) ^^^ BitVec.extractLsb' 0 32 (s.regs .rcx)).zeroExtend 64))
            .rax (s0.regs .rdx),
          mem := memUpd8 s.mem (s0.regs .rdi + BitVec.ofNat 64 pos)
                   (s0.mem (s0.regs .rsi + BitVec.ofNat 64 pos) ^^^ BitVec.extractLsb' 0 8 (s0.regs .rcx)),
          flags := (evalAluN (by decide) .cmp (s0.regs .rdx) (s0.regs .rdx)
                     (evalAluN (by decide) .add (BitVec.ofNat 64 pos) 1#64
                       (evalAluN (by decide) .xor (BitVec.extractLsb' 0 32 ((s0.mem (s0.regs .rsi + BitVec.ofNat 64 pos)).zeroExtend 64))
                         (BitVec.extractLsb' 0 32 (s.regs .rcx)) s.flags (nd (idx + 1)).flags).2
                       (nd (idx + 3)).flags).2
                     (nd (idx + 4)).flags).2 } := by
      dsimp only [xorO3_fallLoopSeq]
      rw [execInstrSeq_succ_cons, exec_movzx8_s32_mem, evalByteAddr_base_idx0, hrsi, hrax, hsrc]
      rw [execInstrSeq_succ_cons, exec_aluRmReg_s32_xor]
      dsimp only; rw [regUpd_eq, regUpd_ne _ (by decide)]
      rw [execInstrSeq_succ_cons, exec_mov8Store_mem_lo8, evalByteAddr_base_idx0]
      dsimp only; rw [regUpd_ne _ (by decide), regUpd_ne _ (by decide), regUpd_ne _ (by decide), regUpd_ne _ (by decide),
                      hrdi, hrax, regUpd_eq, xor_lo8_extract, hrcx]
      rw [execInstrSeq_succ_cons, exec_aluImm_s64_add]
      dsimp only; rw [regUpd_ne _ (by decide), regUpd_ne _ (by decide), hrax, hadd1]
      rw [execInstrSeq_succ_cons, exec_aluRmReg_s64_cmp, execInstrSeq_zero]
      dsimp only; rw [regUpd_ne _ (by decide), regUpd_ne _ (by decide), regUpd_ne _ (by decide), hr8, regUpd_eq]
    rw [he] at hrun1 hnf1 ⊢
    rw [runFrom_succ, step_at_concrete xorO3_fallLoop_jne _ _ hrun1 hnf1 rfl,
        exec_jcc_fall (evalCond_ne_of_zf_true (by rw [cmp_flags_zf, cmp_sub_self_zero])), runFrom_zero]
    have hinv' := xorPrefix_step1 hnwD hinv (by omega : pos < (s0.regs .rdx).toNat)
    rw [hpos1] at hinv'
    exact ⟨hrun, hnf, rfl, hymm,
      by unfold SysVCalleeSavedPreserved at hcs ⊢; dsimp only; exact cs_step_caller (r := .rax) rfl (cs_step_caller (r := .rdx) rfl (cs_step_caller (r := .rdx) rfl hcs)),
      hinv'.2⟩
  | succ m ih =>
    intro idx s hle hrun hnf hrip hrdi hrsi hrcx hr8 hrax hymm hcs hinv
    dsimp only
    rw [show 6 * (m + 1 + 1) = 6 + 6 * (m + 1) by omega, runFrom_add]
    rw [show (6 : Nat) = 5 + 1 by rfl, runFrom_add]
    rcases runFrom_of_decodeSeqAt xorO3_fallLoop_dec idx nd s hrun hnf hrip with ⟨hseq, hrun1, hnf1⟩
    rw [hseq]
    let pos := (s0.regs .rdx).toNat - (m + 2)
    have hpos1 : pos + 1 = (s0.regs .rdx).toNat - (m + 1) := by dsimp only [pos]; omega
    have hadd1 : BitVec.ofNat 64 pos + 1#64 = BitVec.ofNat 64 ((s0.regs .rdx).toNat - (m + 1)) := by
      change BitVec.ofNat 64 pos + BitVec.ofNat 64 1 = _; rw [bv64_ofNat_add, hpos1]
    have hsrc := xorPrefix_src_eq hnwS hdisj hstkS hinv (by omega : pos < (s0.regs .rdx).toNat)
    have he : execInstrSeq 5 xorO3_fallLoopSeq idx nd s =
        { s with
          rip := 0x4005f0#64,
          regs := regUpd (regUpd (regUpd s.regs .rdx ((s0.mem (s0.regs .rsi + BitVec.ofNat 64 pos)).zeroExtend 64))
            .rdx ((BitVec.extractLsb' 0 32 ((s0.mem (s0.regs .rsi + BitVec.ofNat 64 pos)).zeroExtend 64) ^^^ BitVec.extractLsb' 0 32 (s.regs .rcx)).zeroExtend 64))
            .rax (BitVec.ofNat 64 ((s0.regs .rdx).toNat - (m + 1))),
          mem := memUpd8 s.mem (s0.regs .rdi + BitVec.ofNat 64 pos)
                   (s0.mem (s0.regs .rsi + BitVec.ofNat 64 pos) ^^^ BitVec.extractLsb' 0 8 (s0.regs .rcx)),
          flags := (evalAluN (by decide) .cmp (s0.regs .rdx) (BitVec.ofNat 64 ((s0.regs .rdx).toNat - (m + 1)))
                     (evalAluN (by decide) .add (BitVec.ofNat 64 pos) 1#64
                       (evalAluN (by decide) .xor (BitVec.extractLsb' 0 32 ((s0.mem (s0.regs .rsi + BitVec.ofNat 64 pos)).zeroExtend 64))
                         (BitVec.extractLsb' 0 32 (s.regs .rcx)) s.flags (nd (idx + 1)).flags).2
                       (nd (idx + 3)).flags).2
                     (nd (idx + 4)).flags).2 } := by
      dsimp only [xorO3_fallLoopSeq]
      rw [execInstrSeq_succ_cons, exec_movzx8_s32_mem, evalByteAddr_base_idx0, hrsi, hrax, hsrc]
      rw [execInstrSeq_succ_cons, exec_aluRmReg_s32_xor]
      dsimp only; rw [regUpd_eq, regUpd_ne _ (by decide)]
      rw [execInstrSeq_succ_cons, exec_mov8Store_mem_lo8, evalByteAddr_base_idx0]
      dsimp only; rw [regUpd_ne _ (by decide), regUpd_ne _ (by decide), regUpd_ne _ (by decide), regUpd_ne _ (by decide),
                      hrdi, hrax, regUpd_eq, xor_lo8_extract, hrcx]
      rw [execInstrSeq_succ_cons, exec_aluImm_s64_add]
      dsimp only; rw [regUpd_ne _ (by decide), regUpd_ne _ (by decide), hrax, hadd1]
      rw [execInstrSeq_succ_cons, exec_aluRmReg_s64_cmp, execInstrSeq_zero]
      dsimp only; rw [regUpd_ne _ (by decide), regUpd_ne _ (by decide), regUpd_ne _ (by decide), hr8, regUpd_eq]
    rw [he] at hrun1 hnf1 ⊢
    have hne : s0.regs .rdx ≠ BitVec.ofNat 64 ((s0.regs .rdx).toNat - (m + 1)) := by
      intro heq
      have hlt64 := (s0.regs .rdx).isLt
      have ht := congrArg BitVec.toNat heq
      rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)] at ht; omega
    rw [runFrom_succ, step_at_concrete xorO3_fallLoop_jne _ _ hrun1 hnf1 rfl,
        exec_jcc_taken (evalCond_ne_of_zf_false (by rw [cmp_flags_zf, cmp_sub_zero_false_of_ne hne])),
        runFrom_zero]
    have hinv' := xorPrefix_step1 hnwD hinv (by omega : pos < (s0.regs .rdx).toNat)
    rw [hpos1] at hinv'
    exact ih (idx + 6) _ (by omega) hrun hnf rfl
      (by dsimp only; repeat rw [regUpd_ne _ (by decide)]; exact hrdi)
      (by dsimp only; repeat rw [regUpd_ne _ (by decide)]; exact hrsi)
      (by dsimp only; repeat rw [regUpd_ne _ (by decide)]; exact hrcx)
      (by dsimp only; repeat rw [regUpd_ne _ (by decide)]; exact hr8)
      (by dsimp only; rw [regUpd_eq])
      hymm
      (by unfold SysVCalleeSavedPreserved at hcs ⊢; dsimp only; exact cs_step_caller (r := .rax) rfl (cs_step_caller (r := .rdx) rfl (cs_step_caller (r := .rdx) rfl hcs)))
      hinv'

/-! ## Section 3: Main Equivalence & Tree Borrows Alias-Guard Discharge Theorems -/

/-- **Kernel-Checked Equivalence Proof for `gcc 15.2.0 -O3 -mavx2` `c_xor_stream`:**
    Proves all execution paths (`len = 0`, alias fallback `0x5c8`, `32B` AVX2 loop
    + `vzeroupper`, `16B` VEX-128 epilogue, shrink-wrapped `push rbp; push rbx`
    `8B` `mov bh, bl` + `vpshuflw`, `1..7B` unrolled tail, and `leave; ret`) match
    `RustXorStreamPost` with `SysVCalleeSavedPreserved` and `UpperYmmCleanOrPreserved`. -/
theorem prove_c_xor_stream_o3_avx2 :
    CObjectMatchesRustContract cFfiKernelsO3Avx2Obj 0x450#64 (XorStreamPre 16) (XorStreamContractPost 16) := by
  intro s0 nd hrun hnf hrip hpre
  change s0.rip = 0x400450#64 at hrip
  have hcs0 : SysVCalleeSavedPreserved s0 s0 := ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩
  have hinv0 : XorPrefixInv s0.mem s0.mem (s0.regs .rdi) (s0.regs .rsi) (s0.regs .rsp) (s0.regs .rdx).toNat 0 (BitVec.extractLsb' 0 8 (s0.regs .rcx)) :=
    ⟨Nat.zero_le _, fun _ hi => by omega, fun _ _ _ => rfl⟩
  by_cases hlen0 : (s0.regs .rdx).toNat = 0
  · refine ⟨3, ?_⟩
    rw [runX64_eq_runFrom, runFrom_succ, step_at_concrete xorO3_test _ _ hrun hnf hrip, exec_aluRmReg_s64_test]
    have hzf : evalCond .e (evalAluN (by decide) .test (s0.regs .rdx) (s0.regs .rdx) s0.flags (nd 0).flags).2 = true := by
      rw [evalCond_e_of_zf_true (by rw [test_flags_zf, test64_self_zero_eq]; simp [hlen0])]
    rw [runFrom_succ, step_at_concrete xorO3_je0 _ { s0 with rip := 0x400450#64 + BitVec.ofNat 64 3, flags := _ } hrun hnf rfl, exec_jcc_taken hzf]
    rw [runFrom_succ, step_at_concrete xorO3_ret609 _ { s0 with rip := 0x400453#64 + BitVec.ofNat 64 6 + 0x1b0#64, flags := _ } hrun hnf rfl, exec_ret, runFrom_zero]
    exact ⟨rfl, hnf, hcs0, fun h => h, ⟨fun _ hi => by omega, fun _ _ _ => rfl⟩⟩
  · have hzf0 : evalCond .e (evalAluN (by decide) .test (s0.regs .rdx) (s0.regs .rdx) s0.flags (nd 0).flags).2 = false := by
      rw [evalCond_e_of_zf_false (by rw [test_flags_zf, test64_self_zero_eq]; simp [hlen0])]
    let sA := runFrom xorCmap 2 0 nd s0
    have hsAEq : sA =
        { s0 with
          rip := 0x400459#64,
          flags := (evalAluN (by decide) .test (s0.regs .rdx) (s0.regs .rdx) s0.flags (nd 0).flags).2 } := by
      dsimp only [sA]
      rw [runFrom_succ, step_at_concrete xorO3_test _ _ hrun hnf hrip, exec_aluRmReg_s64_test]
      rw [runFrom_succ, step_at_concrete xorO3_je0 _ { s0 with rip := 0x400450#64 + BitVec.ofNat 64 3, flags := _ } hrun hnf rfl, exec_jcc_fall hzf0, runFrom_zero]
      rfl
    rcases runFrom_of_decodeSeqAt xorO3_alias_dec 2 nd sA (by rw [hsAEq]; exact hrun) (by rw [hsAEq]; exact hnf) (by rw [hsAEq]) with ⟨hals, hrunA, hnfA⟩
    let gap : BitVec 64 := (s0.regs .rdi + 0xffffffffffffffff#64) - s0.regs .rsi
    have heAlias : execInstrSeq 4 xorO3_aliasSeq 2 nd sA =
        { sA with
          rip := 0x400467#64,
          regs := regUpd (regUpd (regUpd s0.regs .rax (s0.regs .rdi + 0xffffffffffffffff#64)) .r8 (s0.regs .rdx)) .rax gap,
          flags := (evalAluN (by decide) .cmp gap 0x1e#64
                     (evalAluN (by decide) .sub (s0.regs .rdi + 0xffffffffffffffff#64) (s0.regs .rsi) sA.flags (nd 4).flags).2
                     (nd 5).flags).2 } := by
      dsimp only [xorO3_aliasSeq]
      have hAr : sA.regs = s0.regs := by rw [hsAEq]
      rw [execInstrSeq_succ_cons, exec_lea_s64, evalByteAddr_base_disp, hAr]
      rw [execInstrSeq_succ_cons, exec_movStore_s64_reg]
      dsimp only; rw [regUpd_ne _ (by decide)]
      rw [execInstrSeq_succ_cons, exec_aluRmReg_s64_sub]
      dsimp only; rw [regUpd_ne _ (by decide), regUpd_eq, regUpd_ne _ (by decide), regUpd_ne _ (by decide)]
      rw [execInstrSeq_succ_cons, exec_aluImm_s64_cmp, execInstrSeq_zero]
      dsimp only; rw [regUpd_eq]
    cases hAlias : evalCond .be (execInstrSeq 4 xorO3_aliasSeq 2 nd sA).flags with
    | true =>
      let sF0 := runFrom xorCmap 5 2 nd sA
      have hsF0Eq : sF0 = { execInstrSeq 4 xorO3_aliasSeq 2 nd sA with rip := 0x4005c8#64 } := by
        dsimp only [sF0]
        rw [show (5 : Nat) = 4 + 1 by rfl, runFrom_add, hals, runFrom_succ,
            step_at_concrete xorO3_alias_jbe _ _ hrunA hnfA (by rw [heAlias]),
            exec_jcc_taken hAlias, runFrom_zero]
        rw [heAlias]; rfl
      rcases runFrom_of_decodeSeqAt xorO3_fallPre_dec 7 nd sF0
        (by rw [hsF0Eq, heAlias, hsAEq]; exact hrun) (by rw [hsF0Eq, heAlias, hsAEq]; exact hnf) (by rw [hsF0Eq]) with ⟨hfp, hrunF1, hnfF1⟩
      have heFP : execInstrSeq 3 xorO3_fallPreSeq 7 nd sF0 =
          { sF0 with
            rip := 0x4005e0#64,
            regs := regUpd sF0.regs .rax 0#64,
            flags := (evalAluN (by decide) .xor (BitVec.extractLsb' 0 32 (sF0.regs .rax)) (BitVec.extractLsb' 0 32 (sF0.regs .rax)) sF0.flags (nd 7).flags).2 } := by
        dsimp only [xorO3_fallPreSeq]
        rw [execInstrSeq_succ_cons, exec_aluRmReg_s32_xor_self,
            execInstrSeq_succ_cons, exec_nop, execInstrSeq_succ_cons, exec_nop, execInstrSeq_zero]
      let sF1 := runFrom xorCmap 3 7 nd sF0
      have hsF1Eq : sF1 = execInstrSeq 3 xorO3_fallPreSeq 7 nd sF0 := hfp
      let kLen := (s0.regs .rdx).toNat - 1
      have hcsF1 : SysVCalleeSavedPreserved s0 sF1 := by
        unfold SysVCalleeSavedPreserved at hcs0 ⊢
        rw [hsF1Eq, heFP, hsF0Eq, heAlias]; dsimp only
        exact cs_step_caller (r := .rax) rfl (cs_step_caller (r := .rax) rfl (cs_step_caller (r := .r8) rfl (cs_step_caller (r := .rax) rfl hcs0)))
      have hLoop := xorO3_fallback_loop s0 hpre nd kLen 10 sF1 (by dsimp only [kLen]; omega)
        (by rw [hsF1Eq]; exact hrunF1) (by rw [hsF1Eq]; exact hnfF1) (by rw [hsF1Eq, heFP])
        (by rw [hsF1Eq, heFP]; dsimp only; rw [regUpd_ne _ (by decide), hsF0Eq, heAlias]; dsimp only; repeat rw [regUpd_ne _ (by decide)])
        (by rw [hsF1Eq, heFP]; dsimp only; rw [regUpd_ne _ (by decide), hsF0Eq, heAlias]; dsimp only; repeat rw [regUpd_ne _ (by decide)])
        (by rw [hsF1Eq, heFP]; dsimp only; rw [regUpd_ne _ (by decide), hsF0Eq, heAlias]; dsimp only; repeat rw [regUpd_ne _ (by decide)])
        (by rw [hsF1Eq, heFP]; dsimp only; rw [regUpd_ne _ (by decide), hsF0Eq, heAlias]; dsimp only; rw [regUpd_ne _ (by decide), regUpd_eq])
        (by rw [hsF1Eq, heFP]; dsimp only; rw [regUpd_eq, show (s0.regs .rdx).toNat - (kLen + 1) = 0 by dsimp only [kLen]; omega])
        (by rw [hsF1Eq, heFP, hsF0Eq, heAlias, hsAEq])
        hcsF1
        (by rw [hsF1Eq, heFP, hsF0Eq, heAlias, hsAEq, show (s0.regs .rdx).toNat - (kLen + 1) = 0 by dsimp only [kLen]; omega]; exact hinv0)
      rcases hLoop with ⟨hlr, hlf, hlrip, hlym, hlcs, hlpost⟩
      refine ⟨10 + 6 * (kLen + 1) + 1, ?_⟩
      rw [runX64_eq_runFrom, show 10 + 6 * (kLen + 1) + 1 = (2 + (5 + (3 + 6 * (kLen + 1)))) + 1 by omega,
          runFrom_add, runFrom_add, runFrom_add, runFrom_add]
      rw [runFrom_succ, step_at_concrete xorO3_fall_ret _ _ hlr hlf hlrip, exec_ret, runFrom_zero]
      exact ⟨rfl, hlf, hlcs, fun h => by dsimp only [AllUpperYmmClean]; rw [hlym]; exact h, hlpost⟩
    | false =>
      let sB := runFrom xorCmap 5 2 nd sA
      have hsBEq : sB = { execInstrSeq 4 xorO3_aliasSeq 2 nd sA with rip := 0x40046d#64 } := by
        dsimp only [sB]
        rw [show (5 : Nat) = 4 + 1 by rfl, runFrom_add, hals, runFrom_succ,
            step_at_concrete xorO3_alias_jbe _ _ hrunA hnfA (by rw [heAlias]),
            exec_jcc_fall hAlias, runFrom_zero]
        rw [heAlias]; rfl
      rcases runFrom_of_decodeSeqAt xorO3_lenChk_dec 7 nd sB
        (by rw [hsBEq, heAlias, hsAEq]; exact hrun) (by rw [hsBEq, heAlias, hsAEq]; exact hnf) (by rw [hsBEq]) with ⟨hlc, hrunL, hnfL⟩
      have heLen : execInstrSeq 2 xorO3_lenChkSeq 7 nd sB =
          { sB with
            rip := 0x400475#64,
            regs := regUpd sB.regs .rax (s0.regs .rdx + 0xffffffffffffffff#64),
            flags := (evalAluN (by decide) .cmp (s0.regs .rdx + 0xffffffffffffffff#64) 0x1e#64 sB.flags (nd 8).flags).2 } := by
        dsimp only [xorO3_lenChkSeq]
        have hBdx : sB.regs .rdx = s0.regs .rdx := by rw [hsBEq, heAlias]; dsimp only; repeat rw [regUpd_ne _ (by decide)]
        rw [execInstrSeq_succ_cons, exec_lea_s64, evalByteAddr_base_disp, hBdx]
        rw [execInstrSeq_succ_cons, exec_aluImm_s64_cmp, execInstrSeq_zero]
        dsimp only; rw [regUpd_eq]
      have hbe31 := bv64_sub1_cmp_be (s0.regs .rdx) 30 (by omega) (by decide)
      by_cases hle31 : (s0.regs .rdx).toNat ≤ 31
      · have hcc31 : evalCond .be (execInstrSeq 2 xorO3_lenChkSeq 7 nd sB).flags = true := by
          rw [heLen]; dsimp only
          rw [evalCond_be_of_flags, cmp_flags_cf, cmp_flags_zf]
          change (decide ((s0.regs .rdx + 0xffffffffffffffff#64).toNat < 30) || ((s0.regs .rdx + 0xffffffffffffffff#64) - BitVec.ofNat 64 30 == 0#64)) = true
          rw [hbe31]; simp [hle31]
        let sS := runFrom xorCmap 3 7 nd sB
        have hsSEq : sS = { execInstrSeq 2 xorO3_lenChkSeq 7 nd sB with rip := 0x4005f3#64 } := by
          dsimp only [sS]
          rw [show (3 : Nat) = 2 + 1 by rfl, runFrom_add, hlc, runFrom_succ,
              step_at_concrete xorO3_lenChk_jbe _ _ hrunL hnfL (by rw [heLen]),
              exec_jcc_taken hcc31, runFrom_zero]
          rw [heLen]; rfl
        let sE := runFrom xorCmap 2 10 nd sS
        have hsEEq : sE =
            { sS with
              rip := 0x4004bf#64,
              regs := regUpd sS.regs .rdx 0#64,
              flags := (evalAluN (by decide) .xor (BitVec.extractLsb' 0 32 (sS.regs .rdx)) (BitVec.extractLsb' 0 32 (sS.regs .rdx)) sS.flags (nd 10).flags).2 } := by
          dsimp only [sE]
          have hSr : sS.halted = false := by rw [hsSEq, heLen, hsBEq, heAlias, hsAEq]; exact hrun
          have hSf : sS.fault = false := by rw [hsSEq, heLen, hsBEq, heAlias, hsAEq]; exact hnf
          rw [runFrom_succ, step_at_concrete xorO3_skip32_xor _ _ hSr hSf (by rw [hsSEq]), exec_aluRmReg_s32_xor_self]
          rw [runFrom_succ, step_at_concrete xorO3_skip32_jmp _ { sS with rip := 0x4005f3#64 + BitVec.ofNat 64 2, regs := _, flags := _ } hSr hSf rfl, exec_jmp, runFrom_zero]
          rfl
        have hcsE : SysVCalleeSavedPreserved s0 sE := by
          unfold SysVCalleeSavedPreserved at hcs0 ⊢
          rw [hsEEq, hsSEq, heLen, hsBEq, heAlias]; dsimp only
          exact cs_step_caller (r := .rdx) rfl (cs_step_caller (r := .rax) rfl
            (cs_step_caller (r := .rax) rfl (cs_step_caller (r := .r8) rfl (cs_step_caller (r := .rax) rfl hcs0))))
        have hepi := xorO3_epi16_0x4bf s0 sE 0 12 nd hpre
          (by rw [hsEEq, hsSEq, heLen, hsBEq, heAlias, hsAEq]; exact hrun)
          (by rw [hsEEq, hsSEq, heLen, hsBEq, heAlias, hsAEq]; exact hnf)
          (by rw [hsEEq])
          (by rw [hsEEq]; dsimp only; rw [regUpd_ne _ (by decide), hsSEq, heLen]; dsimp only; rw [regUpd_ne _ (by decide), hsBEq, heAlias]; dsimp only; repeat rw [regUpd_ne _ (by decide)])
          (by rw [hsEEq]; dsimp only; rw [regUpd_ne _ (by decide), hsSEq, heLen]; dsimp only; rw [regUpd_ne _ (by decide), hsBEq, heAlias]; dsimp only; repeat rw [regUpd_ne _ (by decide)])
          (by rw [hsEEq]; dsimp only; rw [regUpd_ne _ (by decide), hsSEq, heLen]; dsimp only; rw [regUpd_ne _ (by decide), hsBEq, heAlias]; dsimp only; repeat rw [regUpd_ne _ (by decide)])
          (by rw [hsEEq]; dsimp only; rw [regUpd_ne _ (by decide), hsSEq, heLen]; dsimp only; rw [regUpd_ne _ (by decide), hsBEq, heAlias]; dsimp only; rw [regUpd_ne _ (by decide), regUpd_eq])
          (by rw [hsEEq]; dsimp only; exact regUpd_eq _ _ _)
          hcsE
          (by rw [hsEEq, hsSEq, heLen, hsBEq, heAlias, hsAEq]; exact fun h => h)
          (by rw [hsEEq, hsSEq, heLen, hsBEq, heAlias, hsAEq]; exact hinv0)
          (by omega) (by omega)
        rcases hepi with ⟨k, hk⟩
        exact ⟨12 + k, by rw [runX64_eq_runFrom, show 12 + k = 2 + (5 + (3 + (2 + k))) by omega, runFrom_add, runFrom_add, runFrom_add, runFrom_add]; simpa [Nat.add_assoc] using hk⟩
      · have hcc31 : evalCond .be (execInstrSeq 2 xorO3_lenChkSeq 7 nd sB).flags = false := by
          rw [heLen]; dsimp only
          rw [evalCond_be_of_flags, cmp_flags_cf, cmp_flags_zf]
          change (decide ((s0.regs .rdx + 0xffffffffffffffff#64).toNat < 30) || ((s0.regs .rdx + 0xffffffffffffffff#64) - BitVec.ofNat 64 30 == 0#64)) = false
          rw [hbe31]; simp [hle31]
        let sV0 := runFrom xorCmap 3 7 nd sB
        have hsV0Eq : sV0 = { execInstrSeq 2 xorO3_lenChkSeq 7 nd sB with rip := 0x40047b#64 } := by
          dsimp only [sV0]
          rw [show (3 : Nat) = 2 + 1 by rfl, runFrom_add, hlc, runFrom_succ,
              step_at_concrete xorO3_lenChk_jbe _ _ hrunL hnfL (by rw [heLen]),
              exec_jcc_fall hcc31, runFrom_zero]
          rw [heLen]; rfl
        rcases runFrom_of_decodeSeqAt xorO3_avxPre_dec 10 nd sV0
          (by rw [hsV0Eq, heLen, hsBEq, heAlias, hsAEq]; exact hrun)
          (by rw [hsV0Eq, heLen, hsBEq, heAlias, hsAEq]; exact hnf) (by rw [hsV0Eq]) with ⟨hap, hrunAP, hnfAP⟩
        let q : Nat := (s0.regs .rdx).toNat / 32
        have hqPos : 1 ≤ q := by dsimp only [q]; omega
        have hqBound : q * 32 ≤ (s0.regs .rdx).toNat := by dsimp only [q]; omega
        have hmask32 : s0.regs .rdx &&& 0xffffffffffffffe0#64 = BitVec.ofNat 64 (q * 32) := by
          apply BitVec.eq_of_toNat_eq
          have hlt64 := (s0.regs .rdx).isLt
          rw [bv64_and_neg32_toNat, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)]
        let key8 := BitVec.extractLsb' 0 8 (s0.regs .rcx)
        have heAP : execInstrSeq 6 xorO3_avxPreSeq 10 nd sV0 =
            { sV0 with
              rip := 0x4004a0#64,
              regs := regUpd (regUpd sV0.regs .rdx (BitVec.ofNat 64 (q * 32))) .rax 0#64,
              ymms := ymmUpd (writeXmm128 true sV0.ymms y1 (((BitVec.extractLsb' 0 32 (s0.regs .rcx)).zeroExtend 64).zeroExtend 128)) y1 (packBytes256 fun _ => key8),
              flags := (evalAluN (by decide) .xor (BitVec.extractLsb' 0 32 (sV0.regs .rax)) (BitVec.extractLsb' 0 32 (sV0.regs .rax))
                         (evalAluN (by decide) .and (s0.regs .rdx) 0xffffffffffffffe0#64 sV0.flags (nd 11).flags).2
                         (nd 12).flags).2 } := by
          dsimp only [xorO3_avxPreSeq]
          have hVcx : sV0.regs .rcx = s0.regs .rcx := by rw [hsV0Eq, heLen]; dsimp only; rw [regUpd_ne _ (by decide), hsBEq, heAlias]; dsimp only; repeat rw [regUpd_ne _ (by decide)]
          have hVdx : sV0.regs .rdx = s0.regs .rdx := by rw [hsV0Eq, heLen]; dsimp only; rw [regUpd_ne _ (by decide), hsBEq, heAlias]; dsimp only; repeat rw [regUpd_ne _ (by decide)]
          rw [execInstrSeq_succ_cons, exec_simdMovGprToX_vex32_reg, hVcx]
          rw [execInstrSeq_succ_cons, exec_aluImm_s64_and, hVdx, hmask32]
          rw [execInstrSeq_succ_cons, exec_aluRmReg_s32_xor_self]
          dsimp only; rw [regUpd_ne _ (by decide)]
          rw [execInstrSeq_succ_cons, exec_simdBroadcastB_vex256_reg]
          have hb0 : BitVec.extractLsb' 0 8 (writeXmm128 true sV0.ymms y1 (((BitVec.extractLsb' 0 32 (s0.regs .rcx)).zeroExtend 64).zeroExtend 128) y1) = key8 := by
            dsimp only [key8]
            rw [writeXmm128_true_eq, ymmUpd_eq]
            apply BitVec.eq_of_getLsbD_eq; intro b hb
            rw [BitVec.getLsbD_extractLsb', BitVec.getLsbD_append]
            unfold BitVec.zeroExtend
            simp [hb, show b < 32 by omega, show b < 64 by omega, show b < 128 by omega]
          dsimp only; rw [hb0]
          rw [execInstrSeq_succ_cons, exec_nop, execInstrSeq_succ_cons, exec_nop, execInstrSeq_zero]
        let sV1 := runFrom xorCmap 6 10 nd sV0
        have hsV1Eq : sV1 = execInstrSeq 6 xorO3_avxPreSeq 10 nd sV0 := hap
        have hcsV1 : SysVCalleeSavedPreserved s0 sV1 := by
          unfold SysVCalleeSavedPreserved at hcs0 ⊢
          rw [hsV1Eq, heAP, hsV0Eq, heLen, hsBEq, heAlias]; dsimp only
          exact cs_step_caller (r := .rax) rfl (cs_step_caller (r := .rdx) rfl
            (cs_step_caller (r := .rax) rfl (cs_step_caller (r := .rax) rfl (cs_step_caller (r := .r8) rfl (cs_step_caller (r := .rax) rfl hcs0)))))
        have hAvx := xorO3_avx_loop s0 hpre nd q (q - 1) 16 sV1
          (by omega) hqBound (by rw [hsV1Eq]; exact hrunAP) (by rw [hsV1Eq]; exact hnfAP) (by rw [hsV1Eq, heAP])
          (by rw [hsV1Eq, heAP]; dsimp only; rw [regUpd_ne _ (by decide), regUpd_ne _ (by decide), hsV0Eq, heLen]; dsimp only; rw [regUpd_ne _ (by decide), hsBEq, heAlias]; dsimp only; repeat rw [regUpd_ne _ (by decide)])
          (by rw [hsV1Eq, heAP]; dsimp only; rw [regUpd_ne _ (by decide), regUpd_ne _ (by decide), hsV0Eq, heLen]; dsimp only; rw [regUpd_ne _ (by decide), hsBEq, heAlias]; dsimp only; repeat rw [regUpd_ne _ (by decide)])
          (by rw [hsV1Eq, heAP]; dsimp only; rw [regUpd_ne _ (by decide), regUpd_ne _ (by decide), hsV0Eq, heLen]; dsimp only; rw [regUpd_ne _ (by decide), hsBEq, heAlias]; dsimp only; repeat rw [regUpd_ne _ (by decide)])
          (by rw [hsV1Eq, heAP]; dsimp only; rw [regUpd_ne _ (by decide), regUpd_ne _ (by decide), hsV0Eq, heLen]; dsimp only; rw [regUpd_ne _ (by decide), hsBEq, heAlias]; dsimp only; rw [regUpd_ne _ (by decide), regUpd_eq])
          (by rw [hsV1Eq, heAP]; dsimp only; rw [regUpd_ne _ (by decide), regUpd_eq])
          (by rw [hsV1Eq, heAP]; dsimp only; rw [regUpd_eq, show (q - (q - 1 + 1)) * 32 = 0 by omega])
          (by rw [hsV1Eq, heAP]; dsimp only; rw [ymmUpd_eq])
          hcsV1
          (by rw [hsV1Eq, heAP, hsV0Eq, heLen, hsBEq, heAlias, hsAEq, show (q - (q - 1 + 1)) * 32 = 0 by omega]; exact hinv0)
        generalize hsV2 : runFrom xorCmap (5 * (q - 1 + 1)) 16 nd sV1 = sV2 at hAvx
        rcases hAvx with ⟨h2r, h2f, h2rip, h2di, h2si, h2cx, h2r8, h2dx, h2cs, h2inv⟩
        let idx2 := 16 + 5 * (q - 1 + 1)
        by_cases hmod32 : (s0.regs .rdx).toNat = q * 32
        · have hdxEq : s0.regs .rdx = BitVec.ofNat 64 (q * 32) := by
            rw [← hmod32, BitVec.ofNat_toNat, BitVec.setWidth_eq]
          have hzf32 : evalCond .e (evalAluN (by decide) .cmp (s0.regs .rdx) (BitVec.ofNat 64 (q * 32)) sV2.flags (nd idx2).flags).2 = true := by
            rw [evalCond_e_of_zf_true (by rw [cmp_flags_zf, ← hdxEq, cmp_sub_self_zero])]
          have hsf : runFrom xorCmap 4 idx2 nd sV2 =
              { sV2 with
                rip := 0x400608#64,
                ymms := vzeroUpperAll sV2.ymms,
                flags := (evalAluN (by decide) .cmp (s0.regs .rdx) (BitVec.ofNat 64 (q * 32)) sV2.flags (nd idx2).flags).2,
                halted := true } := by
            rw [runFrom_succ, step_at_concrete xorO3_postAvx_cmp _ _ h2r h2f h2rip, exec_aluRmReg_s64_cmp, h2r8, h2dx]
            rw [runFrom_succ, step_at_concrete xorO3_postAvx_je _ { sV2 with rip := 0x4004b3#64 + BitVec.ofNat 64 3, flags := _ } h2r h2f rfl, exec_jcc_taken hzf32]
            rw [runFrom_succ, step_at_concrete xorO3_vzu605 _ { sV2 with rip := 0x4004b6#64 + BitVec.ofNat 64 6 + 0x149#64, flags := _ } h2r h2f rfl, exec_vzeroupper]
            rw [runFrom_succ, step_at_concrete xorO3_ret608 _ { sV2 with rip := 0x400605#64 + BitVec.ofNat 64 3, ymms := _, flags := _ } h2r h2f rfl, exec_ret, runFrom_zero]
            rfl
          refine ⟨idx2 + 4, ?_⟩
          dsimp only
          rw [runX64_eq_runFrom, show idx2 + 4 = (2 + (5 + (3 + (6 + 5 * (q - 1 + 1))))) + 4 by dsimp only [idx2]; omega,
              runFrom_add, runFrom_add, runFrom_add, runFrom_add, runFrom_add, hsV2,
              show 0 + (2 + (5 + (3 + (6 + 5 * (q - 1 + 1))))) = idx2 by dsimp only [idx2]; omega]
          change (runFrom xorCmap 4 idx2 nd sV2).halted = true ∧
            (runFrom xorCmap 4 idx2 nd sV2).fault = false ∧
            SysVCalleeSavedPreserved s0 (runFrom xorCmap 4 idx2 nd sV2) ∧
            UpperYmmCleanOrPreserved s0 (runFrom xorCmap 4 idx2 nd sV2) ∧
            XorStreamContractPost 16 s0 (runFrom xorCmap 4 idx2 nd sV2)
          rw [hsf, ← hmod32]
          rw [← hmod32] at h2inv
          exact ⟨rfl, h2f, h2cs, fun _ => vzeroUpperAll_clean _, h2inv.2⟩
        · have hdxNe : s0.regs .rdx ≠ BitVec.ofNat 64 (q * 32) := by
            intro heq; have hlt64 := (s0.regs .rdx).isLt
            have ht := congrArg BitVec.toNat heq
            rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)] at ht; exact hmod32 ht
          have hzf32 : evalCond .e (evalAluN (by decide) .cmp (s0.regs .rdx) (BitVec.ofNat 64 (q * 32)) sV2.flags (nd idx2).flags).2 = false := by
            rw [evalCond_e_of_zf_false (by rw [cmp_flags_zf, cmp_sub_zero_false_of_ne hdxNe])]
          let sV3 := runFrom xorCmap 3 idx2 nd sV2
          have hsV3Eq : sV3 =
              { sV2 with
                rip := 0x4004bf#64,
                ymms := vzeroUpperAll sV2.ymms,
                flags := (evalAluN (by decide) .cmp (s0.regs .rdx) (BitVec.ofNat 64 (q * 32)) sV2.flags (nd idx2).flags).2 } := by
            dsimp only [sV3]
            rw [runFrom_succ, step_at_concrete xorO3_postAvx_cmp _ _ h2r h2f h2rip, exec_aluRmReg_s64_cmp, h2r8, h2dx]
            rw [runFrom_succ, step_at_concrete xorO3_postAvx_je _ { sV2 with rip := 0x4004b3#64 + BitVec.ofNat 64 3, flags := _ } h2r h2f rfl, exec_jcc_fall hzf32]
            rw [runFrom_succ, step_at_concrete xorO3_vzu4bc _ { sV2 with rip := 0x4004b6#64 + BitVec.ofNat 64 6, flags := _ } h2r h2f rfl, exec_vzeroupper, runFrom_zero]
            rfl
          have hepi := xorO3_epi16_0x4bf s0 sV3 (q * 32) (idx2 + 3) nd hpre
            (by rw [hsV3Eq]; exact h2r) (by rw [hsV3Eq]; exact h2f) (by rw [hsV3Eq])
            (by rw [hsV3Eq]; exact h2di) (by rw [hsV3Eq]; exact h2si) (by rw [hsV3Eq]; exact h2cx)
            (by rw [hsV3Eq]; exact h2r8) (by rw [hsV3Eq]; exact h2dx)
            (by rw [hsV3Eq]; exact h2cs) (by rw [hsV3Eq]; exact fun _ => vzeroUpperAll_clean _)
            (by rw [hsV3Eq]; exact h2inv) (by omega) (by dsimp only [q]; omega)
          rcases hepi with ⟨k, hk⟩
          refine ⟨idx2 + 3 + k, ?_⟩
          rw [runX64_eq_runFrom, show idx2 + 3 + k = (2 + (5 + (3 + (6 + 5 * (q - 1 + 1))))) + (3 + k) by dsimp only [idx2]; omega,
              runFrom_add, runFrom_add, runFrom_add, runFrom_add, runFrom_add, runFrom_add, hsV2,
              show 0 + (2 + (5 + (3 + (6 + 5 * (q - 1 + 1))))) = idx2 by dsimp only [idx2]; omega]
          exact hk

/-- **Tree Borrows Disjointness Discharges GCC's Non-`restrict` Alias Guard:**
    For any safe-Rust call to `c_xor_stream -O3 -mavx2` with `len ≥ 32` and
    non-null `dst` (`0 < dst.toNat`, `src.toNat + 31 < 2^64`), the `0x467`
    `jbe` alias guard is provably **not taken** (`evalCond .be = false`), so
    execution unconditionally enters the `32B` AVX2 fast path at `0x40046d`. -/
theorem c_xor_stream_o3_avx2_overlap_guard_discharged (s0 : X64State) (nd : Nat → UndefChoice)
    (hrun : s0.halted = false) (hnf : s0.fault = false) (hrip : s0.rip = 0x400450#64)
    (hpre : XorStreamPre 16 s0)
    (hlen32 : 32 ≤ (s0.regs .rdx).toNat)
    (hdstPos : 0 < (s0.regs .rdi).toNat)
    (hsrcBound : (s0.regs .rsi).toNat + 31 < 2 ^ 64) :
    (runX64 cFfiKernelsO3Avx2Obj 7 nd s0).rip = 0x40046d#64 := by
  rcases hpre with ⟨hnwD, hnwS, hdisj, _, _⟩
  have hgt30 := disjoint_slices_discharges_gcc_overlap_guard hnwD hnwS hdisj hlen32 hdstPos hsrcBound
  rw [runX64_eq_runFrom]
  have hzf0 : evalCond .e (evalAluN (by decide) .test (s0.regs .rdx) (s0.regs .rdx) s0.flags (nd 0).flags).2 = false := by
    rw [evalCond_e_of_zf_false (by rw [test_flags_zf, test64_self_zero_eq]; simp [show (s0.regs .rdx).toNat ≠ 0 by omega])]
  rw [show (7 : Nat) = 2 + (4 + 1) by rfl, runFrom_add]
  let sA : X64State := { s0 with rip := 0x400459#64, flags := (evalAluN (by decide) .test (s0.regs .rdx) (s0.regs .rdx) s0.flags (nd 0).flags).2 }
  have hsA : runFrom xorCmap 2 0 nd s0 = sA := by
    rw [runFrom_succ, step_at_concrete xorO3_test _ _ hrun hnf hrip, exec_aluRmReg_s64_test]
    rw [runFrom_succ, step_at_concrete xorO3_je0 _ { s0 with rip := 0x400450#64 + BitVec.ofNat 64 3, flags := _ } hrun hnf rfl, exec_jcc_fall hzf0, runFrom_zero]
    rfl
  rw [hsA, runFrom_add]
  rcases runFrom_of_decodeSeqAt xorO3_alias_dec 2 nd sA hrun hnf rfl with ⟨hals, hrunA, hnfA⟩
  rw [hals]
  let gap : BitVec 64 := (s0.regs .rdi + 0xffffffffffffffff#64) - s0.regs .rsi
  have heAlias : execInstrSeq 4 xorO3_aliasSeq 2 nd sA =
      { sA with
        rip := 0x400467#64,
        regs := regUpd (regUpd (regUpd s0.regs .rax (s0.regs .rdi + 0xffffffffffffffff#64)) .r8 (s0.regs .rdx)) .rax gap,
        flags := (evalAluN (by decide) .cmp gap 0x1e#64
                   (evalAluN (by decide) .sub (s0.regs .rdi + 0xffffffffffffffff#64) (s0.regs .rsi) sA.flags (nd 4).flags).2
                   (nd 5).flags).2 } := by
    dsimp only [xorO3_aliasSeq]
    rw [execInstrSeq_succ_cons, exec_lea_s64, evalByteAddr_base_disp]
    rw [execInstrSeq_succ_cons, exec_movStore_s64_reg]
    dsimp only [sA]; rw [regUpd_ne _ (by decide)]
    rw [execInstrSeq_succ_cons, exec_aluRmReg_s64_sub]
    dsimp only; rw [regUpd_ne _ (by decide), regUpd_eq, regUpd_ne _ (by decide), regUpd_ne _ (by decide)]
    rw [execInstrSeq_succ_cons, exec_aluImm_s64_cmp, execInstrSeq_zero]
    dsimp only; rw [regUpd_eq]
  rw [heAlias] at hrunA hnfA ⊢
  have hbeF : evalCond .be (evalAluN (by decide) .cmp gap 0x1e#64
      (evalAluN (by decide) .sub (s0.regs .rdi + 0xffffffffffffffff#64) (s0.regs .rsi) sA.flags (nd 4).flags).2
      (nd 5).flags).2 = false := by
    rw [evalCond_be_of_flags, cmp_flags_cf, cmp_flags_zf]
    have hlt30 : decide (gap.toNat < (0x1e#64 : BitVec 64).toNat) = false := by
      have h30 : (0x1e#64 : BitVec 64).toNat = 30 := rfl
      rw [h30]
      exact decide_eq_false (by dsimp only [gap]; omega)
    have hne30 : gap ≠ 0x1e#64 := by
      intro heq; have ht := congrArg BitVec.toNat heq; change gap.toNat = 30 at ht; dsimp only [gap] at ht; omega
    rw [hlt30, cmp_sub_zero_false_of_ne hne30]; rfl
  rw [runFrom_succ, step_at_concrete xorO3_alias_jbe _ _ hrunA hnfA rfl]
  rw [exec_jcc_fall (by dsimp only; exact hbeF), runFrom_zero]
  rfl

end UntrustedCObjXorAvx2
