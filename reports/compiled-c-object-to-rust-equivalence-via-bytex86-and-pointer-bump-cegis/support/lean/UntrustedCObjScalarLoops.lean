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

/-!
# `UntrustedCObjScalarLoops`

Kernel-checked equivalence proofs (`0` `sorry`, `0` `isPartial`) for the read-only
counterless pointer-bump scalar C FFI `.o` kernels compiled by `gcc 15.2.0` at
both `-O2` and `-O3 -mavx2`:
- `c_fnv1a64` (`-O2` & `-O3 -mavx2`): `prove_c_fnv1a64_o2`, `prove_c_fnv1a64_o3`
- `c_checksum_rol_u8` (`-O2` & `-O3 -mavx2`): `prove_c_checksum_rol_o2`, `prove_c_checksum_rol_o3`
- `c_adler32_chunk` (`-O2` & `-O3 -mavx2`): `prove_c_adler32_chunk_o2`, `prove_c_adler32_chunk_o3`
-/

namespace UntrustedCObjScalarLoops

open ByteX86Gcc
open RustFfiSpecs
open CompiledCObjImages
open UntrustedCObjHints

theorem upperClean_of_ymms_eq {s0 s1 : X64State} (hy : s1.ymms = s0.ymms) :
    UpperYmmCleanOrPreserved s0 s1 := fun hc idx => hy ▸ hc idx

theorem readOnlyFrame_of_mem_eq {m : ByteMem} (rsp0 : BitVec 64) (sr : Nat) :
    ReadOnlyMemFrame m m rsp0 sr := fun _ _ => rfl

theorem bv8_ext32_of_ext64 (b : BitVec 8) :
    BitVec.extractLsb' 0 32 (b.zeroExtend 64) = b.zeroExtend 32 := by
  apply BitVec.eq_of_toNat_eq
  have hlt := b.isLt
  unfold BitVec.zeroExtend
  simp only [BitVec.extractLsb'_toNat, Nat.shiftRight_zero, BitVec.toNat_setWidth]
  rw [Nat.mod_eq_of_lt (by omega : b.toNat < 2 ^ 64),
      Nat.mod_eq_of_lt (by omega : b.toNat < 2 ^ 32)]

/-! ## 1. `c_fnv1a64` (`0x00` in `-O2` & `-O3 -mavx2`) -/

def fnvPreSeq : List (X64Instr × BitVec 64) :=
  [ (.movImm .s64 .rax 0xcbf29ce484222325#64, 0x40000f#64),
    (.aluRmReg .s64 .add (.reg .rsi) .rdi, 0x400012#64),
    (.movImm .s64 .rcx 0x00000100000001b3#64, 0x40001c#64),
    (.nop, 0x400020#64) ]

def fnvLoopSeq : List (X64Instr × BitVec 64) :=
  [ (.movzx8 .s32 .rdx (.mem8 { base := some .rdi }), 0x400023#64),
    (.aluImm .s64 .add (.reg .rdi) 1#64, 0x400027#64),
    (.aluRmReg .s64 .xor (.reg .rax) .rdx, 0x40002a#64),
    (.imul2 .s64 .rax (.reg .rcx), 0x40002e#64),
    (.aluRmReg .s64 .cmp (.reg .rsi) .rdi, 0x400031#64) ]

structure FnvInv (s0 : X64State) (endPtr p acc : BitVec 64) (st : X64State) : Prop where
  run   : st.halted = false
  nf    : st.fault = false
  rip   : st.rip = 0x400020#64
  mem   : st.mem = s0.mem
  ymms  : st.ymms = s0.ymms
  cs    : SysVCalleeSavedPreserved s0 st
  rdi   : st.regs .rdi = p
  rsi   : st.regs .rsi = endPtr
  rcx   : st.regs .rcx = 0x00000100000001b3#64
  rax   : st.regs .rax = acc

theorem fnv_body_step {s0 : X64State} {endPtr p acc : BitVec 64} {idx : Nat}
    {nd : Nat → UndefChoice} {st : X64State} (hin : FnvInv s0 endPtr p acc st) :
    let sm := execInstrSeq 5 fnvLoopSeq idx nd st
    sm.halted = false ∧ sm.fault = false ∧ sm.rip = 0x400031#64 ∧
    sm.mem = s0.mem ∧ sm.ymms = s0.ymms ∧ SysVCalleeSavedPreserved s0 sm ∧
    sm.regs .rdi = p + 1#64 ∧ sm.regs .rsi = endPtr ∧
    sm.regs .rcx = 0x00000100000001b3#64 ∧
    sm.regs .rax = fnv1aStep acc (s0.mem p) ∧
    sm.flags.zf = (endPtr - (p + 1#64) == 0#64) := by
  dsimp only [fnvLoopSeq]
  rw [execInstrSeq_succ_cons, exec_movzx8_s32_mem, evalByteAddr_base,
      execInstrSeq_succ_cons, exec_aluImm_s64_add,
      execInstrSeq_succ_cons, exec_aluRmReg_s64_xor,
      execInstrSeq_succ_cons, exec_imul2_s64_reg,
      execInstrSeq_succ_cons, exec_aluRmReg_s64_cmp, execInstrSeq_zero]
  refine ⟨hin.run, hin.nf, rfl, hin.mem, hin.ymms, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · dsimp only [SysVCalleeSavedPreserved]
    repeat (apply cs_step_caller; · decide)
    exact hin.cs
  · simp only [regUpd_eq, regUpd_ne _ (by decide : Reg.rdi ≠ .rax), regUpd_ne _ (by decide : Reg.rdi ≠ .rdx), hin.rdi]
  · simp only [regUpd_ne _ (by decide : Reg.rsi ≠ .rax), regUpd_ne _ (by decide : Reg.rsi ≠ .rdi),
               regUpd_ne _ (by decide : Reg.rsi ≠ .rdx), hin.rsi]
  · simp only [regUpd_ne _ (by decide : Reg.rcx ≠ .rax), regUpd_ne _ (by decide : Reg.rcx ≠ .rdi),
               regUpd_ne _ (by decide : Reg.rcx ≠ .rdx), hin.rcx]
  · simp only [fnv1aStep, regUpd_eq, regUpd_ne _ (by decide : Reg.rax ≠ .rdi), regUpd_ne _ (by decide : Reg.rax ≠ .rdx),
               regUpd_ne _ (by decide : Reg.rdx ≠ .rdi), regUpd_ne _ (by decide : Reg.rcx ≠ .rax),
               regUpd_ne _ (by decide : Reg.rcx ≠ .rdi), regUpd_ne _ (by decide : Reg.rcx ≠ .rdx),
               hin.rdi, hin.rax, hin.rcx, hin.mem]
  · rw [cmp_flags_zf]
    simp only [regUpd_eq, regUpd_ne _ (by decide : Reg.rsi ≠ .rax), regUpd_ne _ (by decide : Reg.rsi ≠ .rdi),
               regUpd_ne _ (by decide : Reg.rsi ≠ .rdx), regUpd_ne _ (by decide : Reg.rdi ≠ .rax),
               regUpd_ne _ (by decide : Reg.rdi ≠ .rdx), hin.rsi, hin.rdi]

theorem fnv_loop_ind {cmap : CodeMap}
    (hbody : decodeSeqAt cmap 5 0x400020#64 = some fnvLoopSeq)
    (hjne  : decodeX64 (fetchWindow16 cmap 0x400031#64) = .ok (.jccRel .ne 0xffffffffffffffed#64) 2)
    (hret  : decodeX64 (fetchWindow16 cmap 0x400033#64) = .ok .ret64 1)
    (s0 : X64State) (nd : Nat → UndefChoice) :
    ∀ (rem : Nat) (p acc : BitVec 64) (idx : Nat) (st : X64State),
      NoWrapSlice p (rem + 1) →
      FnvInv s0 (p + BitVec.ofNat 64 (rem + 1)) p acc st →
      ∃ steps : Nat,
        let sf := runFrom cmap steps idx nd st
        sf.halted = true ∧ sf.fault = false ∧
        SysVCalleeSavedPreserved s0 sf ∧ sf.ymms = s0.ymms ∧ sf.mem = s0.mem ∧
        sf.regs .rax = rustFnv1a64From s0.mem p (rem + 1) acc := by
  intro rem
  induction rem with
  | zero =>
    intro p acc idx st _ hin
    refine ⟨5 + (1 + 1), ?_⟩
    dsimp only
    rw [runFrom_add, runFrom_add]
    rcases runFrom_of_decodeSeqAt hbody idx nd st hin.run hin.nf hin.rip with ⟨hseq, _, _⟩
    rw [hseq]
    rcases fnv_body_step hin with ⟨hr1, hf1, hrip1, hm1, hy1, hcs1, _, _, _, hrax1, hzf1⟩
    generalize execInstrSeq 5 fnvLoopSeq idx nd st = sm at hr1 hf1 hrip1 hm1 hy1 hcs1 hrax1 hzf1 ⊢
    have hzf_t : sm.flags.zf = true := by rw [hzf1]; exact cmp_sub_self_zero (p + 1#64)
    have hs_jne : runFrom cmap 1 (idx + 5) nd sm = { sm with
          rip := 0x400033#64 } := by
      rw [runFrom_succ, runFrom_zero, step_at_concrete hjne _ sm hr1 hf1 hrip1,
          exec_jcc_fall (evalCond_ne_of_zf_true hzf_t)]; rfl
    rw [hs_jne]
    have hs_ret : runFrom cmap 1 (idx + 5 + 1) nd { sm with
          rip := 0x400033#64 } =
        { sm with
          rip := 0x400033#64, halted := true } := by
      rw [runFrom_succ, runFrom_zero, step_at_concrete hret _ { sm with
          rip := 0x400033#64 } hr1 hf1 rfl, exec_ret]
    rw [hs_ret]
    rw [rustFnv1a64From_succ, rustFnv1a64From_zero]
    exact ⟨rfl, hf1, hcs1, hy1, hm1, hrax1⟩
  | succ k ih =>
    intro p acc idx st hnw hin
    rcases runFrom_of_decodeSeqAt hbody idx nd st hin.run hin.nf hin.rip with ⟨hseq, _, _⟩
    rcases fnv_body_step hin with ⟨hr1, hf1, hrip1, hm1, hy1, hcs1, hrdi1, hrsi1, hrcx1, hrax1, hzf1⟩
    generalize execInstrSeq 5 fnvLoopSeq idx nd st = sm at hseq hr1 hf1 hrip1 hm1 hy1 hcs1 hrdi1 hrsi1 hrcx1 hrax1 hzf1
    have hne : p + BitVec.ofNat 64 (k + 2) ≠ p + 1#64 := ptr_offset_ne hnw (by omega) (by omega) (by omega)
    have hzf_f : sm.flags.zf = false := by rw [hzf1]; exact cmp_sub_zero_false_of_ne hne
    have hs_jne : runFrom cmap 1 (idx + 5) nd sm = { sm with
          rip := 0x400020#64 } := by
      rw [runFrom_succ, runFrom_zero, step_at_concrete hjne _ sm hr1 hf1 hrip1,
          exec_jcc_taken (evalCond_ne_of_zf_false hzf_f)]; rfl
    have hnw' : NoWrapSlice (p + 1#64) (k + 1) := by
      unfold NoWrapSlice at hnw ⊢
      have hp1 := ptr_offset_toNat hnw (by omega : 1 ≤ k + 2)
      change (p + BitVec.ofNat 64 1).toNat + (k + 1) < 2 ^ 64; omega
    have hend : p + BitVec.ofNat 64 (k + 2) = (p + 1#64) + BitVec.ofNat 64 (k + 1) := by
      change p + BitVec.ofNat 64 (k + 2) = p + BitVec.ofNat 64 1 + BitVec.ofNat 64 (k + 1)
      rw [bv64_add_ofNat_assoc]; congr 2; omega
    have hin_n : FnvInv s0 ((p + 1#64) + BitVec.ofNat 64 (k + 1)) (p + 1#64)
        (fnv1aStep acc (s0.mem p)) { sm with
          rip := 0x400020#64 } :=
      ⟨hr1, hf1, rfl, hm1, hy1, hcs1, hrdi1, hend ▸ hrsi1, hrcx1, hrax1⟩
    rcases ih (p + 1#64) (fnv1aStep acc (s0.mem p)) (idx + 5 + 1) { sm with
          rip := 0x400020#64 } hnw' hin_n with ⟨st_ih, hih⟩
    refine ⟨5 + (1 + st_ih), ?_⟩
    dsimp only at hih ⊢
    rw [runFrom_add, hseq, runFrom_add, hs_jne, rustFnv1a64From_succ]
    exact hih

theorem prove_c_fnv1a64_generic (img : X64ObjImage) (hbase : img.codeBase = 0x400000#64)
    (htest : decodeX64 (fetchWindow16 (objCodeMap img) 0x400000#64) = .ok (.aluRmReg .s64 .test (.reg .rsi) .rsi) 3)
    (hje   : decodeX64 (fetchWindow16 (objCodeMap img) 0x400003#64) = .ok (.jccRel .e 0x33#64) 2)
    (hpre  : decodeSeqAt (objCodeMap img) 4 0x400005#64 = some fnvPreSeq)
    (hbody : decodeSeqAt (objCodeMap img) 5 0x400020#64 = some fnvLoopSeq)
    (hjne  : decodeX64 (fetchWindow16 (objCodeMap img) 0x400031#64) = .ok (.jccRel .ne 0xffffffffffffffed#64) 2)
    (hret1 : decodeX64 (fetchWindow16 (objCodeMap img) 0x400033#64) = .ok .ret64 1)
    (hmov0 : decodeX64 (fetchWindow16 (objCodeMap img) 0x400038#64) = .ok (.movImm .s64 .rax 0xcbf29ce484222325#64) 10)
    (hret0 : decodeX64 (fetchWindow16 (objCodeMap img) 0x400042#64) = .ok .ret64 1) :
    CObjectMatchesRustContract img 0x0#64 (Fnv1a64Pre 0) (Fnv1a64Post 0) := by
  intro s0 nd hrun hnf hrip ⟨hnw, _⟩
  rw [hbase, BitVec.add_zero] at hrip
  let cmap := objCodeMap img
  let s1 : X64State :=
    { s0 with
      rip := 0x400003#64,
      flags := (evalAluN (by decide) .test (s0.regs .rsi) (s0.regs .rsi) s0.flags (nd 0).flags).2 }
  have hs1 : runFrom cmap 1 0 nd s0 = s1 := by
    rw [runFrom_succ, runFrom_zero, step_at_concrete htest _ s0 hrun hnf hrip, exec_aluRmReg_s64_test]; rfl
  cases hlen : (s0.regs .rsi).toNat with
  | zero =>
    refine ⟨1 + (1 + (1 + 1)), ?_⟩
    dsimp only
    rw [runX64_eq_runFrom, runFrom_add, hs1, runFrom_add, runFrom_add]
    have hzf1 : s1.flags.zf = true := by rw [test_flags_zf, test64_self_zero_eq, hlen]; rfl
    have hs2 : runFrom cmap 1 1 nd s1 = { s1 with
          rip := 0x400038#64 } := by
      rw [runFrom_succ, runFrom_zero, step_at_concrete hje _ s1 hrun hnf rfl,
          exec_jcc_taken (evalCond_e_of_zf_true hzf1)]; rfl
    rw [hs2]
    let s2 := { s1 with
          rip := 0x400038#64 }
    have hs3 : runFrom cmap 1 2 nd s2 = { s2 with
          rip := 0x400042#64, regs := regUpd s0.regs .rax 0xcbf29ce484222325#64 } := by
      rw [runFrom_succ, runFrom_zero, step_at_concrete hmov0 _ s2 hrun hnf rfl, exec_movImm_s64]; rfl
    rw [hs3]
    let s3 := { s2 with
          rip := 0x400042#64, regs := regUpd s0.regs .rax 0xcbf29ce484222325#64 }
    have hs4 : runFrom cmap 1 3 nd s3 = { s3 with halted := true } := by
      rw [runFrom_succ, runFrom_zero, step_at_concrete hret0 _ s3 hrun hnf rfl, exec_ret]
    rw [hs4]
    have hcs : SysVCalleeSavedPreserved s0 { s3 with halted := true } := by
      dsimp only [SysVCalleeSavedPreserved, s3]
      apply cs_step_caller; · decide
      exact ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩
    refine ⟨rfl, hnf, hcs, upperClean_of_ymms_eq rfl, ?_⟩
    unfold Fnv1a64Post rustFnv1a64; rw [hlen, rustFnv1a64From_zero]
    exact ⟨by dsimp only [s3]; exact regUpd_eq _ _ _, readOnlyFrame_of_mem_eq _ _⟩
  | succ rem =>
    have hzf1 : s1.flags.zf = false := by rw [test_flags_zf, test64_self_zero_eq, hlen]; rfl
    let s2 : X64State := { s1 with rip := 0x400005#64 }
    have hs2 : runFrom cmap 1 1 nd s1 = s2 := by
      rw [runFrom_succ, runFrom_zero, step_at_concrete hje _ s1 hrun hnf rfl,
          exec_jcc_fall (evalCond_e_of_zf_false hzf1)]; rfl
    rcases runFrom_of_decodeSeqAt hpre 2 nd s2 hrun hnf rfl with ⟨hseq_pre, _, _⟩
    let sp : X64State :=
      { s2 with
        rip := 0x400020#64,
        regs := regUpd (regUpd (regUpd s0.regs .rax 0xcbf29ce484222325#64)
          .rsi (s0.regs .rsi + s0.regs .rdi)) .rcx 0x00000100000001b3#64,
        flags := (evalAluN (by decide) .add (s0.regs .rsi) (s0.regs .rdi) s2.flags (nd 3).flags).2 }
    have hpre_eq : execInstrSeq 4 fnvPreSeq 2 nd s2 = sp := by
      dsimp only [fnvPreSeq, sp]
      rw [execInstrSeq_succ_cons, exec_movImm_s64,
          execInstrSeq_succ_cons, exec_aluRmReg_s64_add,
          execInstrSeq_succ_cons, exec_movImm_s64,
          execInstrSeq_succ_cons, exec_nop, execInstrSeq_zero]
      simp only [s2, s1, regUpd_ne _ (by decide : Reg.rsi ≠ .rax), regUpd_ne _ (by decide : Reg.rdi ≠ .rax)]
    have hrsi_eq : s0.regs .rsi = BitVec.ofNat 64 (rem + 1) := by
      apply BitVec.eq_of_toNat_eq
      rw [hlen, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by rw [← hlen]; exact (s0.regs .rsi).isLt)]
    have hnw' : NoWrapSlice (s0.regs .rdi) (rem + 1) := by rwa [← hlen]
    have hcs_p : SysVCalleeSavedPreserved s0 sp := by
      dsimp only [SysVCalleeSavedPreserved, sp]
      repeat (apply cs_step_caller; · decide)
      exact ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩
    have hin0 : FnvInv s0 (s0.regs .rdi + BitVec.ofNat 64 (rem + 1)) (s0.regs .rdi) 0xcbf29ce484222325#64 sp := by
      refine ⟨hrun, hnf, rfl, rfl, rfl, hcs_p, ?_, ?_, ?_, ?_⟩
      · dsimp only [sp]; simp [regUpd_ne _ (by decide : Reg.rdi ≠ .rcx), regUpd_ne _ (by decide : Reg.rdi ≠ .rsi), regUpd_ne _ (by decide : Reg.rdi ≠ .rax)]
      · dsimp only [sp]; simp [regUpd_ne _ (by decide : Reg.rsi ≠ .rcx), regUpd_eq, hrsi_eq, BitVec.add_comm]
      · dsimp only [sp]; exact regUpd_eq _ _ _
      · dsimp only [sp]; simp [regUpd_ne _ (by decide : Reg.rax ≠ .rcx), regUpd_ne _ (by decide : Reg.rax ≠ .rsi), regUpd_eq]
    rcases fnv_loop_ind hbody hjne hret1 s0 nd rem (s0.regs .rdi) 0xcbf29ce484222325#64 6 sp hnw' hin0 with ⟨st_l, hl⟩
    refine ⟨1 + (1 + (4 + st_l)), ?_⟩
    dsimp only at hl ⊢
    rw [runX64_eq_runFrom, runFrom_add, hs1, runFrom_add, hs2, runFrom_add, hseq_pre, hpre_eq]
    rcases hl with ⟨hh, hnf', hcs', hym', hmem', hrax⟩
    refine ⟨hh, hnf', hcs', upperClean_of_ymms_eq hym', ?_⟩
    unfold Fnv1a64Post rustFnv1a64; rw [hlen, hrax, hmem']
    exact ⟨rfl, readOnlyFrame_of_mem_eq _ _⟩

theorem prove_c_fnv1a64_o2 :
    CObjectMatchesRustContract cFfiKernelsO2Obj 0x0#64 (Fnv1a64Pre 0) (Fnv1a64Post 0) :=
  prove_c_fnv1a64_generic cFfiKernelsO2Obj rfl
    (decodeAt_of_check rfl) (decodeAt_of_check rfl)
    (decodeSeqAt_of_check rfl rfl) (decodeSeqAt_of_check rfl rfl)
    (decodeAt_of_check rfl) (decodeAt_of_check rfl)
    (decodeAt_of_check rfl) (decodeAt_of_check rfl)

theorem prove_c_fnv1a64_o3 :
    CObjectMatchesRustContract cFfiKernelsO3Avx2Obj 0x0#64 (Fnv1a64Pre 0) (Fnv1a64Post 0) :=
  prove_c_fnv1a64_generic cFfiKernelsO3Avx2Obj rfl
    (decodeAt_of_check rfl) (decodeAt_of_check rfl)
    (decodeSeqAt_of_check rfl rfl) (decodeSeqAt_of_check rfl rfl)
    (decodeAt_of_check rfl) (decodeAt_of_check rfl)
    (decodeAt_of_check rfl) (decodeAt_of_check rfl)

/-! ## 2. `c_checksum_rol_u8` (`0xD0` in `-O2` & `-O3 -mavx2`) -/

def rolPreSeq : List (X64Instr × BitVec 64) :=
  [ (.aluRmReg .s64 .add (.reg .rsi) .rdi, 0x4000d8#64),
    (.aluRmReg .s32 .xor (.reg .rax) .rax, 0x4000da#64),
    (.nop, 0x4000e0#64) ]

def rolLoopSeq : List (X64Instr × BitVec 64) :=
  [ (.movzx8 .s32 .rdx (.mem8 { base := some .rdi }), 0x4000e3#64),
    (.shiftImm .s32 .rol (.reg .rax) 0x05#8, 0x4000e6#64),
    (.aluImm .s64 .add (.reg .rdi) 1#64, 0x4000ea#64),
    (.aluRmReg .s32 .xor (.reg .rax) .rdx, 0x4000ec#64),
    (.aluRmReg .s64 .cmp (.reg .rdi) .rsi, 0x4000ef#64) ]

structure RolInv (s0 : X64State) (endPtr p : BitVec 64) (acc : BitVec 32) (st : X64State) : Prop where
  run  : st.halted = false
  nf   : st.fault = false
  rip  : st.rip = 0x4000e0#64
  mem  : st.mem = s0.mem
  ymms : st.ymms = s0.ymms
  cs   : SysVCalleeSavedPreserved s0 st
  rdi  : st.regs .rdi = p
  rsi  : st.regs .rsi = endPtr
  rax  : st.regs .rax = acc.zeroExtend 64

theorem rol_body_step {s0 : X64State} {endPtr p : BitVec 64} {acc : BitVec 32} {idx : Nat}
    {nd : Nat → UndefChoice} {st : X64State} (hin : RolInv s0 endPtr p acc st) :
    let sm := execInstrSeq 5 rolLoopSeq idx nd st
    sm.halted = false ∧ sm.fault = false ∧ sm.rip = 0x4000ef#64 ∧
    sm.mem = s0.mem ∧ sm.ymms = s0.ymms ∧ SysVCalleeSavedPreserved s0 sm ∧
    sm.regs .rdi = p + 1#64 ∧ sm.regs .rsi = endPtr ∧
    sm.regs .rax = (rolXorStep acc (s0.mem p)).zeroExtend 64 ∧
    sm.flags.zf = ((p + 1#64) - endPtr == 0#64) := by
  dsimp only [rolLoopSeq]
  rw [execInstrSeq_succ_cons, exec_movzx8_s32_mem, evalByteAddr_base,
      execInstrSeq_succ_cons, exec_shiftImm_s32_rol (hc := by decide),
      execInstrSeq_succ_cons, exec_aluImm_s64_add,
      execInstrSeq_succ_cons, exec_aluRmReg_s32_xor,
      execInstrSeq_succ_cons, exec_aluRmReg_s64_cmp, execInstrSeq_zero]
  have hc5 : ((0x05#8 : BitVec 8).toNat &&& 31) = 5 := rfl
  refine ⟨hin.run, hin.nf, rfl, hin.mem, hin.ymms, ?_, ?_, ?_, ?_, ?_⟩
  · dsimp only [SysVCalleeSavedPreserved]
    repeat (apply cs_step_caller; · decide)
    exact hin.cs
  · simp only [regUpd_eq, regUpd_ne _ (by decide : Reg.rdi ≠ .rax), regUpd_ne _ (by decide : Reg.rdi ≠ .rdx), hin.rdi]
  · simp only [regUpd_ne _ (by decide : Reg.rsi ≠ .rax), regUpd_ne _ (by decide : Reg.rsi ≠ .rdi),
               regUpd_ne _ (by decide : Reg.rsi ≠ .rdx), hin.rsi]
  · simp only [rolXorStep, hc5, regUpd_eq, regUpd_ne _ (by decide : Reg.rax ≠ .rdi),
               regUpd_ne _ (by decide : Reg.rax ≠ .rdx), regUpd_ne _ (by decide : Reg.rdx ≠ .rdi),
               regUpd_ne _ (by decide : Reg.rdx ≠ .rax), hin.rdi, hin.rax, hin.mem,
               zext32_extract32_eq, bv8_ext32_of_ext64]
  · rw [cmp_flags_zf]
    simp only [regUpd_eq, regUpd_ne _ (by decide : Reg.rdi ≠ .rax), regUpd_ne _ (by decide : Reg.rdi ≠ .rdx),
               regUpd_ne _ (by decide : Reg.rsi ≠ .rax), regUpd_ne _ (by decide : Reg.rsi ≠ .rdi),
               regUpd_ne _ (by decide : Reg.rsi ≠ .rdx), hin.rdi, hin.rsi]

theorem rol_loop_ind {cmap : CodeMap}
    (hbody : decodeSeqAt cmap 5 0x4000e0#64 = some rolLoopSeq)
    (hjne  : decodeX64 (fetchWindow16 cmap 0x4000ef#64) = .ok (.jccRel .ne 0xffffffffffffffef#64) 2)
    (hret  : decodeX64 (fetchWindow16 cmap 0x4000f1#64) = .ok .ret64 1)
    (s0 : X64State) (nd : Nat → UndefChoice) :
    ∀ (rem : Nat) (p : BitVec 64) (acc : BitVec 32) (idx : Nat) (st : X64State),
      NoWrapSlice p (rem + 1) →
      RolInv s0 (p + BitVec.ofNat 64 (rem + 1)) p acc st →
      ∃ steps : Nat,
        let sf := runFrom cmap steps idx nd st
        sf.halted = true ∧ sf.fault = false ∧
        SysVCalleeSavedPreserved s0 sf ∧ sf.ymms = s0.ymms ∧ sf.mem = s0.mem ∧
        BitVec.extractLsb' 0 32 (sf.regs .rax) = rustChecksumRolFrom s0.mem p (rem + 1) acc := by
  intro rem
  induction rem with
  | zero =>
    intro p acc idx st _ hin
    refine ⟨5 + (1 + 1), ?_⟩
    dsimp only
    rw [runFrom_add, runFrom_add]
    rcases runFrom_of_decodeSeqAt hbody idx nd st hin.run hin.nf hin.rip with ⟨hseq, _, _⟩
    rw [hseq]
    rcases rol_body_step hin with ⟨hr1, hf1, hrip1, hm1, hy1, hcs1, _, _, hrax1, hzf1⟩
    generalize execInstrSeq 5 rolLoopSeq idx nd st = sm at hr1 hf1 hrip1 hm1 hy1 hcs1 hrax1 hzf1 ⊢
    have hzf_t : sm.flags.zf = true := by rw [hzf1]; exact cmp_sub_self_zero (p + 1#64)
    have hs_jne : runFrom cmap 1 (idx + 5) nd sm = { sm with
          rip := 0x4000f1#64 } := by
      rw [runFrom_succ, runFrom_zero, step_at_concrete hjne _ sm hr1 hf1 hrip1,
          exec_jcc_fall (evalCond_ne_of_zf_true hzf_t)]; rfl
    rw [hs_jne]
    have hs_ret : runFrom cmap 1 (idx + 5 + 1) nd { sm with
          rip := 0x4000f1#64 } =
        { sm with
          rip := 0x4000f1#64, halted := true } := by
      rw [runFrom_succ, runFrom_zero, step_at_concrete hret _ { sm with
          rip := 0x4000f1#64 } hr1 hf1 rfl, exec_ret]
    rw [hs_ret, rustChecksumRolFrom_succ, rustChecksumRolFrom_zero]
    refine ⟨rfl, hf1, hcs1, hy1, hm1, ?_⟩
    change BitVec.extractLsb' 0 32 (sm.regs .rax) = rolXorStep acc (s0.mem p)
    rw [hrax1, zext32_extract32_eq]
  | succ k ih =>
    intro p acc idx st hnw hin
    rcases runFrom_of_decodeSeqAt hbody idx nd st hin.run hin.nf hin.rip with ⟨hseq, _, _⟩
    rcases rol_body_step hin with ⟨hr1, hf1, hrip1, hm1, hy1, hcs1, hrdi1, hrsi1, hrax1, hzf1⟩
    generalize execInstrSeq 5 rolLoopSeq idx nd st = sm at hseq hr1 hf1 hrip1 hm1 hy1 hcs1 hrdi1 hrsi1 hrax1 hzf1
    have hne : p + 1#64 ≠ p + BitVec.ofNat 64 (k + 2) := ptr_offset_ne hnw (by omega) (by omega) (by omega)
    have hzf_f : sm.flags.zf = false := by rw [hzf1]; exact cmp_sub_zero_false_of_ne hne
    have hs_jne : runFrom cmap 1 (idx + 5) nd sm = { sm with
          rip := 0x4000e0#64 } := by
      rw [runFrom_succ, runFrom_zero, step_at_concrete hjne _ sm hr1 hf1 hrip1,
          exec_jcc_taken (evalCond_ne_of_zf_false hzf_f)]; rfl
    have hnw' : NoWrapSlice (p + 1#64) (k + 1) := by
      unfold NoWrapSlice at hnw ⊢
      have hp1 := ptr_offset_toNat hnw (by omega : 1 ≤ k + 2)
      change (p + BitVec.ofNat 64 1).toNat + (k + 1) < 2 ^ 64; omega
    have hend : p + BitVec.ofNat 64 (k + 2) = (p + 1#64) + BitVec.ofNat 64 (k + 1) := by
      change p + BitVec.ofNat 64 (k + 2) = p + BitVec.ofNat 64 1 + BitVec.ofNat 64 (k + 1)
      rw [bv64_add_ofNat_assoc]; congr 2; omega
    have hin_n : RolInv s0 ((p + 1#64) + BitVec.ofNat 64 (k + 1)) (p + 1#64)
        (rolXorStep acc (s0.mem p)) { sm with
          rip := 0x4000e0#64 } :=
      ⟨hr1, hf1, rfl, hm1, hy1, hcs1, hrdi1, hend ▸ hrsi1, hrax1⟩
    rcases ih (p + 1#64) (rolXorStep acc (s0.mem p)) (idx + 5 + 1) { sm with
          rip := 0x4000e0#64 } hnw' hin_n with ⟨st_ih, hih⟩
    refine ⟨5 + (1 + st_ih), ?_⟩
    dsimp only at hih ⊢
    rw [runFrom_add, hseq, runFrom_add, hs_jne, rustChecksumRolFrom_succ]
    exact hih

theorem prove_c_checksum_rol_generic (img : X64ObjImage) (hbase : img.codeBase = 0x400000#64)
    (htest : decodeX64 (fetchWindow16 (objCodeMap img) 0x4000d0#64) = .ok (.aluRmReg .s64 .test (.reg .rsi) .rsi) 3)
    (hje   : decodeX64 (fetchWindow16 (objCodeMap img) 0x4000d3#64) = .ok (.jccRel .e 0x23#64) 2)
    (hpre  : decodeSeqAt (objCodeMap img) 3 0x4000d5#64 = some rolPreSeq)
    (hbody : decodeSeqAt (objCodeMap img) 5 0x4000e0#64 = some rolLoopSeq)
    (hjne  : decodeX64 (fetchWindow16 (objCodeMap img) 0x4000ef#64) = .ok (.jccRel .ne 0xffffffffffffffef#64) 2)
    (hret1 : decodeX64 (fetchWindow16 (objCodeMap img) 0x4000f1#64) = .ok .ret64 1)
    (hxor0 : decodeX64 (fetchWindow16 (objCodeMap img) 0x4000f8#64) = .ok (.aluRmReg .s32 .xor (.reg .rax) .rax) 2)
    (hret0 : decodeX64 (fetchWindow16 (objCodeMap img) 0x4000fa#64) = .ok .ret64 1) :
    CObjectMatchesRustContract img 0xd0#64 (ChecksumRolPre 0) (ChecksumRolPost 0) := by
  intro s0 nd hrun hnf hrip ⟨hnw, _⟩
  rw [hbase] at hrip
  have hrip' : s0.rip = 0x4000d0#64 := hrip
  let cmap := objCodeMap img
  let s1 : X64State :=
    { s0 with
      rip := 0x4000d3#64,
      flags := (evalAluN (by decide) .test (s0.regs .rsi) (s0.regs .rsi) s0.flags (nd 0).flags).2 }
  have hs1 : runFrom cmap 1 0 nd s0 = s1 := by
    rw [runFrom_succ, runFrom_zero, step_at_concrete htest _ s0 hrun hnf hrip', exec_aluRmReg_s64_test]; rfl
  cases hlen : (s0.regs .rsi).toNat with
  | zero =>
    refine ⟨1 + (1 + (1 + 1)), ?_⟩
    dsimp only
    rw [runX64_eq_runFrom, runFrom_add, hs1, runFrom_add, runFrom_add]
    have hzf1 : s1.flags.zf = true := by rw [test_flags_zf, test64_self_zero_eq, hlen]; rfl
    have hs2 : runFrom cmap 1 1 nd s1 = { s1 with
          rip := 0x4000f8#64 } := by
      rw [runFrom_succ, runFrom_zero, step_at_concrete hje _ s1 hrun hnf rfl,
          exec_jcc_taken (evalCond_e_of_zf_true hzf1)]; rfl
    rw [hs2]
    let s2 := { s1 with
          rip := 0x4000f8#64 }
    let s3 : X64State :=
      { s2 with
        rip := 0x4000fa#64,
        regs := regUpd s0.regs .rax 0#64,
        flags := (evalAluN (by decide) .xor (BitVec.extractLsb' 0 32 (s0.regs .rax)) (BitVec.extractLsb' 0 32 (s0.regs .rax)) s2.flags (nd 2).flags).2 }
    have hs3 : runFrom cmap 1 2 nd s2 = s3 := by
      rw [runFrom_succ, runFrom_zero, step_at_concrete hxor0 _ s2 hrun hnf rfl, exec_aluRmReg_s32_xor_self]; rfl
    rw [hs3]
    have hs4 : runFrom cmap 1 3 nd s3 = { s3 with halted := true } := by
      rw [runFrom_succ, runFrom_zero, step_at_concrete hret0 _ s3 hrun hnf rfl, exec_ret]
    rw [hs4]
    have hcs : SysVCalleeSavedPreserved s0 { s3 with halted := true } := by
      dsimp only [SysVCalleeSavedPreserved, s3]
      apply cs_step_caller; · decide
      exact ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩
    refine ⟨rfl, hnf, hcs, upperClean_of_ymms_eq rfl, ?_⟩
    unfold ChecksumRolPost rustChecksumRolU8; rw [hlen, rustChecksumRolFrom_zero]
    exact ⟨by dsimp only [s3]; simp [regUpd_eq], readOnlyFrame_of_mem_eq _ _⟩
  | succ rem =>
    have hzf1 : s1.flags.zf = false := by rw [test_flags_zf, test64_self_zero_eq, hlen]; rfl
    let s2 : X64State := { s1 with rip := 0x4000d5#64 }
    have hs2 : runFrom cmap 1 1 nd s1 = s2 := by
      rw [runFrom_succ, runFrom_zero, step_at_concrete hje _ s1 hrun hnf rfl,
          exec_jcc_fall (evalCond_e_of_zf_false hzf1)]; rfl
    rcases runFrom_of_decodeSeqAt hpre 2 nd s2 hrun hnf rfl with ⟨hseq_pre, _, _⟩
    let sp : X64State :=
      { s2 with
        rip := 0x4000e0#64,
        regs := regUpd (regUpd s0.regs .rsi (s0.regs .rsi + s0.regs .rdi)) .rax 0#64,
        flags := (evalAluN (by decide) .xor
          (BitVec.extractLsb' 0 32 (regUpd s0.regs .rsi (s0.regs .rsi + s0.regs .rdi) .rax))
          (BitVec.extractLsb' 0 32 (regUpd s0.regs .rsi (s0.regs .rsi + s0.regs .rdi) .rax))
          (evalAluN (by decide) .add (s0.regs .rsi) (s0.regs .rdi) s2.flags (nd 2).flags).2 (nd 3).flags).2 }
    have hpre_eq : execInstrSeq 3 rolPreSeq 2 nd s2 = sp := by
      dsimp only [rolPreSeq, sp]
      rw [execInstrSeq_succ_cons, exec_aluRmReg_s64_add,
          execInstrSeq_succ_cons, exec_aluRmReg_s32_xor_self,
          execInstrSeq_succ_cons, exec_nop, execInstrSeq_zero]
    have hrsi_eq : s0.regs .rsi = BitVec.ofNat 64 (rem + 1) := by
      apply BitVec.eq_of_toNat_eq
      rw [hlen, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by rw [← hlen]; exact (s0.regs .rsi).isLt)]
    have hnw' : NoWrapSlice (s0.regs .rdi) (rem + 1) := by rwa [← hlen]
    have hcs_p : SysVCalleeSavedPreserved s0 sp := by
      dsimp only [SysVCalleeSavedPreserved, sp]
      repeat (apply cs_step_caller; · decide)
      exact ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩
    have hin0 : RolInv s0 (s0.regs .rdi + BitVec.ofNat 64 (rem + 1)) (s0.regs .rdi) 0#32 sp := by
      refine ⟨hrun, hnf, rfl, rfl, rfl, hcs_p, ?_, ?_, ?_⟩
      · dsimp only [sp]; simp [regUpd_ne _ (by decide : Reg.rdi ≠ .rax), regUpd_ne _ (by decide : Reg.rdi ≠ .rsi)]
      · dsimp only [sp]; simp [regUpd_ne _ (by decide : Reg.rsi ≠ .rax), regUpd_eq, hrsi_eq, BitVec.add_comm]
      · dsimp only [sp]; exact regUpd_eq _ _ _
    rcases rol_loop_ind hbody hjne hret1 s0 nd rem (s0.regs .rdi) 0#32 5 sp hnw' hin0 with ⟨st_l, hl⟩
    refine ⟨1 + (1 + (3 + st_l)), ?_⟩
    dsimp only at hl ⊢
    rw [runX64_eq_runFrom, runFrom_add, hs1, runFrom_add, hs2, runFrom_add, hseq_pre, hpre_eq]
    rcases hl with ⟨hh, hnf', hcs', hym', hmem', hrax⟩
    refine ⟨hh, hnf', hcs', upperClean_of_ymms_eq hym', ?_⟩
    unfold ChecksumRolPost rustChecksumRolU8; rw [hlen, hrax, hmem']
    exact ⟨rfl, readOnlyFrame_of_mem_eq _ _⟩

theorem prove_c_checksum_rol_o2 :
    CObjectMatchesRustContract cFfiKernelsO2Obj 0xd0#64 (ChecksumRolPre 0) (ChecksumRolPost 0) :=
  prove_c_checksum_rol_generic cFfiKernelsO2Obj rfl
    (decodeAt_of_check rfl) (decodeAt_of_check rfl)
    (decodeSeqAt_of_check rfl rfl) (decodeSeqAt_of_check rfl rfl)
    (decodeAt_of_check rfl) (decodeAt_of_check rfl)
    (decodeAt_of_check rfl) (decodeAt_of_check rfl)

theorem prove_c_checksum_rol_o3 :
    CObjectMatchesRustContract cFfiKernelsO3Avx2Obj 0xd0#64 (ChecksumRolPre 0) (ChecksumRolPost 0) :=
  prove_c_checksum_rol_generic cFfiKernelsO3Avx2Obj rfl
    (decodeAt_of_check rfl) (decodeAt_of_check rfl)
    (decodeSeqAt_of_check rfl rfl) (decodeSeqAt_of_check rfl rfl)
    (decodeAt_of_check rfl) (decodeAt_of_check rfl)
    (decodeAt_of_check rfl) (decodeAt_of_check rfl)

/-! ## 3. `c_adler32_chunk` (`0x50` in `-O2` & `-O3 -mavx2`: `movzx` + `11B` NOPs + Barrett `65521`) -/

def adlerEntrySeq : List (X64Instr × BitVec 64) :=
  [ (.movzx16 .s32 .rcx (.reg .rdx), 0x400053#64),
    (.shiftImm .s32 .shr (.reg .rdx) 0x10#8, 0x400056#64),
    (.aluRmReg .s64 .test (.reg .rsi) .rsi, 0x400059#64) ]

def adlerPreSeq : List (X64Instr × BitVec 64) :=
  [ (.aluRmReg .s64 .add (.reg .rsi) .rdi, 0x40005e#64),
    (.movImm .s32 .r8 0x0000000080078071#64, 0x400064#64),
    (.nop, 0x40006a#64),
    (.nop, 0x400075#64),
    (.nop, 0x400080#64) ]

def adlerLoopASeq : List (X64Instr × BitVec 64) :=
  [ (.movzx8 .s32 .rax (.mem8 { base := some .rdi }), 0x400083#64),
    (.aluImm .s64 .add (.reg .rdi) 1#64, 0x400087#64),
    (.aluRmReg .s32 .add (.reg .rcx) .rax, 0x400089#64),
    (.movStore .s64 (.reg .rax) .rcx, 0x40008c#64),
    (.imul2 .s64 .rcx (.reg .r8), 0x400090#64),
    (.shiftImm .s64 .shr (.reg .rcx) 0x2f#8, 0x400094#64),
    (.imul3 .s32 .r9 (.reg .rcx) 0x000000000000fff1#64, 0x40009b#64),
    (.aluRmReg .s32 .sub (.reg .rax) .r9, 0x40009e#64) ]

def adlerLoopBSeq : List (X64Instr × BitVec 64) :=
  [ (.aluRmReg .s32 .add (.reg .rdx) .rax, 0x4000a0#64),
    (.movStore .s32 (.reg .rcx) .rax, 0x4000a2#64),
    (.movStore .s32 (.reg .rdx) .rdx, 0x4000a4#64),
    (.movStore .s64 (.reg .rax) .rdx, 0x4000a7#64),
    (.imul2 .s64 .rdx (.reg .r8), 0x4000ab#64),
    (.shiftImm .s64 .shr (.reg .rdx) 0x2f#8, 0x4000af#64),
    (.imul3 .s32 .r9 (.reg .rdx) 0x000000000000fff1#64, 0x4000b6#64),
    (.aluRmReg .s32 .sub (.reg .rax) .r9, 0x4000b9#64),
    (.movStore .s32 (.reg .rdx) .rax, 0x4000bb#64) ]

def adlerExitSeq : List (X64Instr × BitVec 64) :=
  [ (.shiftImm .s32 .shl (.reg .rdx) 0x10#8, 0x4000c3#64),
    (.movStore .s32 (.reg .rax) .rdx, 0x4000c5#64),
    (.aluRmReg .s32 .or (.reg .rax) .rcx, 0x4000c7#64) ]

theorem adler_init_lo16 (rdx64 : BitVec 64) :
    let init32 := BitVec.extractLsb' 0 32 rdx64
    (BitVec.extractLsb' 0 16 rdx64).zeroExtend 64 = (init32 &&& 0xFFFF#32).zeroExtend 64 ∧
    (init32 &&& 0xFFFF#32).toNat ≤ 65535 := by
  dsimp only
  refine ⟨?_, ?_⟩
  · apply BitVec.eq_of_toNat_eq
    unfold BitVec.zeroExtend
    simp only [BitVec.toNat_setWidth, BitVec.extractLsb'_toNat, Nat.shiftRight_zero, BitVec.toNat_and]
    have h1 : (0xFFFF#32 : BitVec 32).toNat = 65535 := rfl
    rw [h1]
    have h2 : (rdx64.toNat % 2 ^ 32) &&& 65535 = rdx64.toNat % 2 ^ 16 := by
      have hm16 : ∀ n : Nat, n &&& 65535 = n % 65536 := fun n => Nat.and_two_pow_sub_one_eq_mod n 16
      rw [hm16]
      have hdiv : 2 ^ 32 = 65536 * 65536 := rfl
      rw [hdiv, Nat.mod_mul_left_mod]
    rw [h2]
  · rw [BitVec.toNat_and]; exact Nat.and_le_right

theorem barrett65521_step_ext (s32 : BitVec 32) (hs : s32.toNat ≤ 196560) :
    let s64 := s32.zeroExtend 64
    let q64 := (s64 * 0x80078071#64) >>> 47
    let prod32 := BitVec.extractLsb' 0 32 q64 * 0xFFF1#32
    (s32 - prod32).zeroExtend 64 = (BitVec.ofNat 32 (s32.toNat % 65521)).zeroExtend 64 ∧
    (BitVec.ofNat 32 (s32.toNat % 65521)).toNat < 65521 := by
  dsimp only
  have hs64 : (s32.zeroExtend 64).toNat = s32.toNat := by
    unfold BitVec.zeroExtend; rw [BitVec.toNat_setWidth]
    exact Nat.mod_eq_of_lt (Nat.lt_trans s32.isLt (by decide))
  have hb := barrett65521_step (s32.zeroExtend 64) (by rw [hs64]; exact hs)
  dsimp only at hb
  rw [zext32_extract32_eq, hs64] at hb
  exact ⟨congrArg (BitVec.zeroExtend 64) hb.1, hb.1 ▸ hb.2⟩

structure AdlerInv (s0 : X64State) (endPtr p : BitVec 64) (a b : BitVec 32) (st : X64State) : Prop where
  run  : st.halted = false
  nf   : st.fault = false
  rip  : st.rip = 0x400080#64
  mem  : st.mem = s0.mem
  ymms : st.ymms = s0.ymms
  cs   : SysVCalleeSavedPreserved s0 st
  rdi  : st.regs .rdi = p
  rsi  : st.regs .rsi = endPtr
  r8   : st.regs .r8 = 0x0000000080078071#64
  rcx  : st.regs .rcx = a.zeroExtend 64
  rdx  : st.regs .rdx = b.zeroExtend 64
  ha   : a.toNat ≤ 65535
  hb   : b.toNat ≤ 65535

theorem adler_step_A {s0 : X64State} {endPtr p : BitVec 64} {a b : BitVec 32}
    {idx : Nat} {nd : Nat → UndefChoice} {st : X64State}
    (hin : AdlerInv s0 endPtr p a b st) :
    let sa := execInstrSeq 8 adlerLoopASeq idx nd st
    let a' := BitVec.ofNat 32 ((a.toNat + (s0.mem p).toNat) % 65521)
    sa.halted = false ∧ sa.fault = false ∧ sa.rip = 0x40009e#64 ∧
    sa.mem = s0.mem ∧ sa.ymms = s0.ymms ∧ SysVCalleeSavedPreserved s0 sa ∧
    sa.regs .rdi = p + 1#64 ∧ sa.regs .rsi = endPtr ∧
    sa.regs .r8 = 0x0000000080078071#64 ∧
    sa.regs .rdx = b.zeroExtend 64 ∧
    sa.regs .rax = a'.zeroExtend 64 ∧ a'.toNat < 65521 := by
  dsimp only [adlerLoopASeq]
  rw [execInstrSeq_succ_cons, exec_movzx8_s32_mem, evalByteAddr_base,
      execInstrSeq_succ_cons, exec_aluImm_s64_add,
      execInstrSeq_succ_cons, exec_aluRmReg_s32_add,
      execInstrSeq_succ_cons, exec_movStore_s64_reg,
      execInstrSeq_succ_cons, exec_imul2_s64_reg,
      execInstrSeq_succ_cons, exec_shiftImm_s64_shr (hc := by decide),
      execInstrSeq_succ_cons, exec_imul3_s32_reg,
      execInstrSeq_succ_cons, exec_aluRmReg_s32_sub, execInstrSeq_zero]
  let x8 := s0.mem p
  have hsum : (a + x8.zeroExtend 32).toNat = a.toNat + x8.toNat ∧ a.toNat + x8.toNat ≤ 65790 := by
    have hx_eq : (x8.zeroExtend 32).toNat = x8.toNat := by
      unfold BitVec.zeroExtend; rw [BitVec.toNat_setWidth, Nat.mod_eq_of_lt (Nat.lt_trans x8.isLt (by decide))]
    rw [BitVec.toNat_add, hx_eq]; have ha := hin.ha; have hx := x8.isLt
    exact ⟨Nat.mod_eq_of_lt (by omega), by omega⟩
  have hbar := barrett65521_step_ext (a + x8.zeroExtend 32) (by omega)
  rw [hsum.1] at hbar
  have hc47 : ((0x2f#8 : BitVec 8).toNat &&& 63) = 47 := rfl
  have hf1 : BitVec.extractLsb' 0 32 (0x000000000000fff1#64 : BitVec 64) = 0xFFF1#32 := rfl
  refine ⟨hin.run, hin.nf, rfl, hin.mem, hin.ymms, ?_, ?_, ?_, ?_, ?_, ?_, hbar.2⟩
  · dsimp only [SysVCalleeSavedPreserved]
    repeat (apply cs_step_caller; · decide)
    exact hin.cs
  · simp only [regUpd_ne _ (by decide : Reg.rdi ≠ .rax), regUpd_ne _ (by decide : Reg.rdi ≠ .r9),
               regUpd_ne _ (by decide : Reg.rdi ≠ .rcx), regUpd_eq, hin.rdi]
  · simp only [regUpd_ne _ (by decide : Reg.rsi ≠ .rax), regUpd_ne _ (by decide : Reg.rsi ≠ .r9),
               regUpd_ne _ (by decide : Reg.rsi ≠ .rcx), regUpd_ne _ (by decide : Reg.rsi ≠ .rdi), hin.rsi]
  · simp only [regUpd_ne _ (by decide : Reg.r8 ≠ .rax), regUpd_ne _ (by decide : Reg.r8 ≠ .r9),
               regUpd_ne _ (by decide : Reg.r8 ≠ .rcx), regUpd_ne _ (by decide : Reg.r8 ≠ .rdi), hin.r8]
  · simp only [regUpd_ne _ (by decide : Reg.rdx ≠ .rax), regUpd_ne _ (by decide : Reg.rdx ≠ .r9),
               regUpd_ne _ (by decide : Reg.rdx ≠ .rcx), regUpd_ne _ (by decide : Reg.rdx ≠ .rdi), hin.rdx]
  · simp only [hc47, hf1, regUpd_eq,
               regUpd_ne _ (by decide : Reg.rax ≠ .r9), regUpd_ne _ (by decide : Reg.rax ≠ .rcx),
               regUpd_ne _ (by decide : Reg.rax ≠ .rdi), regUpd_ne _ (by decide : Reg.rcx ≠ .rax),
               regUpd_ne _ (by decide : Reg.rcx ≠ .rdi), regUpd_ne _ (by decide : Reg.r8 ≠ .rax),
               regUpd_ne _ (by decide : Reg.r8 ≠ .rcx), regUpd_ne _ (by decide : Reg.r8 ≠ .rdi),
               hin.rdi, hin.rcx, hin.r8, hin.mem, zext32_extract32_eq, bv8_ext32_of_ext64]
    exact hbar.1

theorem adler_step_B {s0 : X64State} {endPtr p : BitVec 64} {a' b : BitVec 32}
    {idx : Nat} {nd : Nat → UndefChoice} {sa : X64State}
    (hrun : sa.halted = false) (hnf : sa.fault = false) (hrip : sa.rip = 0x40009e#64)
    (hmem : sa.mem = s0.mem) (hymms : sa.ymms = s0.ymms) (hcs : SysVCalleeSavedPreserved s0 sa)
    (hrdi : sa.regs .rdi = p + 1#64) (hrsi : sa.regs .rsi = endPtr)
    (hr8  : sa.regs .r8 = 0x0000000080078071#64)
    (hrdx : sa.regs .rdx = b.zeroExtend 64) (hrax : sa.regs .rax = a'.zeroExtend 64)
    (ha'  : a'.toNat < 65521) (hb : b.toNat ≤ 65535) :
    let sb := execInstrSeq 9 adlerLoopBSeq idx nd sa
    let b' := BitVec.ofNat 32 ((b.toNat + a'.toNat) % 65521)
    sb.halted = false ∧ sb.fault = false ∧ sb.rip = 0x4000bb#64 ∧
    sb.mem = s0.mem ∧ sb.ymms = s0.ymms ∧ SysVCalleeSavedPreserved s0 sb ∧
    sb.regs .rdi = p + 1#64 ∧ sb.regs .rsi = endPtr ∧
    sb.regs .r8 = 0x0000000080078071#64 ∧
    sb.regs .rcx = a'.zeroExtend 64 ∧
    sb.regs .rdx = b'.zeroExtend 64 ∧ b'.toNat < 65521 := by
  have _ := hrip
  dsimp only [adlerLoopBSeq]
  rw [execInstrSeq_succ_cons, exec_aluRmReg_s32_add,
      execInstrSeq_succ_cons, exec_movStore_s32_reg,
      execInstrSeq_succ_cons, exec_movStore_s32_reg,
      execInstrSeq_succ_cons, exec_movStore_s64_reg,
      execInstrSeq_succ_cons, exec_imul2_s64_reg,
      execInstrSeq_succ_cons, exec_shiftImm_s64_shr (hc := by decide),
      execInstrSeq_succ_cons, exec_imul3_s32_reg,
      execInstrSeq_succ_cons, exec_aluRmReg_s32_sub,
      execInstrSeq_succ_cons, exec_movStore_s32_reg, execInstrSeq_zero]
  have hsum : (b + a').toNat = b.toNat + a'.toNat ∧ b.toNat + a'.toNat ≤ 131055 := by
    rw [BitVec.toNat_add]; exact ⟨Nat.mod_eq_of_lt (by omega), by omega⟩
  have hbar := barrett65521_step_ext (b + a') (by omega)
  rw [hsum.1] at hbar
  have hc47 : ((0x2f#8 : BitVec 8).toNat &&& 63) = 47 := rfl
  have hf1 : BitVec.extractLsb' 0 32 (0x000000000000fff1#64 : BitVec 64) = 0xFFF1#32 := rfl
  refine ⟨hrun, hnf, rfl, hmem, hymms, ?_, ?_, ?_, ?_, ?_, ?_, hbar.2⟩
  · dsimp only [SysVCalleeSavedPreserved]
    repeat (apply cs_step_caller; · decide)
    exact hcs
  · simp only [regUpd_ne _ (by decide : Reg.rdi ≠ .rdx), regUpd_ne _ (by decide : Reg.rdi ≠ .rax),
               regUpd_ne _ (by decide : Reg.rdi ≠ .r9), regUpd_ne _ (by decide : Reg.rdi ≠ .rcx), hrdi]
  · simp only [regUpd_ne _ (by decide : Reg.rsi ≠ .rdx), regUpd_ne _ (by decide : Reg.rsi ≠ .rax),
               regUpd_ne _ (by decide : Reg.rsi ≠ .r9), regUpd_ne _ (by decide : Reg.rsi ≠ .rcx), hrsi]
  · simp only [regUpd_ne _ (by decide : Reg.r8 ≠ .rdx), regUpd_ne _ (by decide : Reg.r8 ≠ .rax),
               regUpd_ne _ (by decide : Reg.r8 ≠ .r9), regUpd_ne _ (by decide : Reg.r8 ≠ .rcx), hr8]
  · simp only [regUpd_ne _ (by decide : Reg.rcx ≠ .rdx), regUpd_ne _ (by decide : Reg.rcx ≠ .rax),
               regUpd_ne _ (by decide : Reg.rcx ≠ .r9), regUpd_eq,
               regUpd_ne _ (by decide : Reg.rax ≠ .rdx), hrax, zext32_extract32_eq]
  · simp only [hc47, hf1, regUpd_eq,
               regUpd_ne _ (by decide : Reg.rax ≠ .r9), regUpd_ne _ (by decide : Reg.rax ≠ .rdx),
               regUpd_ne _ (by decide : Reg.rdx ≠ .rax), regUpd_ne _ (by decide : Reg.rdx ≠ .rcx),
               regUpd_ne _ (by decide : Reg.r8 ≠ .rax), regUpd_ne _ (by decide : Reg.r8 ≠ .rdx),
               regUpd_ne _ (by decide : Reg.r8 ≠ .rcx),
               hrdx, hrax, hr8, zext32_extract32_eq]
    exact hbar.1

theorem adler_exit_pack {cmap : CodeMap} {s0 : X64State} {a b : BitVec 32} {idx : Nat}
    {nd : Nat → UndefChoice} {st : X64State}
    (hbody : decodeSeqAt cmap 3 0x4000c0#64 = some adlerExitSeq)
    (hret  : decodeX64 (fetchWindow16 cmap 0x4000c7#64) = .ok .ret64 1)
    (hrun : st.halted = false) (hnf : st.fault = false) (hrip : st.rip = 0x4000c0#64)
    (hmem : st.mem = s0.mem) (hymms : st.ymms = s0.ymms) (hcs : SysVCalleeSavedPreserved s0 st)
    (hrcx : st.regs .rcx = a.zeroExtend 64) (hrdx : st.regs .rdx = b.zeroExtend 64) :
    let sf := runFrom cmap 4 idx nd st
    sf.halted = true ∧ sf.fault = false ∧
    SysVCalleeSavedPreserved s0 sf ∧ sf.ymms = s0.ymms ∧ sf.mem = s0.mem ∧
    BitVec.extractLsb' 0 32 (sf.regs .rax) = (b <<< 16) ||| a := by
  dsimp only
  rw [show (4 : Nat) = 3 + 1 from rfl, runFrom_add]
  rcases runFrom_of_decodeSeqAt hbody idx nd st hrun hnf hrip with ⟨hseq, _, _⟩
  rw [hseq]
  let sx : X64State :=
    { st with
      rip := 0x4000c7#64,
      regs := regUpd (regUpd (regUpd st.regs .rdx ((b <<< 16).zeroExtend 64))
        .rax ((b <<< 16).zeroExtend 64)) .rax (((b <<< 16) ||| a).zeroExtend 64),
      flags := (evalAluN (by decide) .or (b <<< 16) a
        (evalShiftSz .s32 .shl ((BitVec.extractLsb' 0 32 (st.regs .rdx)).zeroExtend 64) 0x10#8 st.flags (nd idx).flags).2
        (nd (idx + 1 + 1)).flags).2 }
  have hex_eq : execInstrSeq 3 adlerExitSeq idx nd st = sx := by
    dsimp only [adlerExitSeq, sx]
    rw [execInstrSeq_succ_cons, exec_shiftImm_s32_shl (hc := by decide),
        execInstrSeq_succ_cons, exec_movStore_s32_reg,
        execInstrSeq_succ_cons, exec_aluRmReg_s32_or, execInstrSeq_zero]
    have hc16 : ((0x10#8 : BitVec 8).toNat &&& 31) = 16 := rfl
    simp only [hc16, regUpd_eq, regUpd_ne _ (by decide : Reg.rcx ≠ .rax), regUpd_ne _ (by decide : Reg.rcx ≠ .rdx),
               hrdx, hrcx, zext32_extract32_eq]
  rw [hex_eq, runFrom_succ, runFrom_zero, step_at_concrete hret _ sx hrun hnf rfl, exec_ret]
  refine ⟨rfl, hnf, ?_, hymms, hmem, ?_⟩
  · dsimp only [SysVCalleeSavedPreserved, sx]
    repeat (apply cs_step_caller; · decide)
    exact hcs
  · dsimp only [sx]; rw [regUpd_eq, zext32_extract32_eq]

theorem adler_loop_ind {cmap : CodeMap} (swapCmp : Bool)
    (hbodyA : decodeSeqAt cmap 8 0x400080#64 = some adlerLoopASeq)
    (hbodyB : decodeSeqAt cmap 9 0x40009e#64 = some adlerLoopBSeq)
    (hcmp   : decodeX64 (fetchWindow16 cmap 0x4000bb#64) =
              .ok (if swapCmp then .aluRmReg .s64 .cmp (.reg .rdi) .rsi else .aluRmReg .s64 .cmp (.reg .rsi) .rdi) 3)
    (hjne   : decodeX64 (fetchWindow16 cmap 0x4000be#64) = .ok (.jccRel .ne 0xffffffffffffffc0#64) 2)
    (hexit  : decodeSeqAt cmap 3 0x4000c0#64 = some adlerExitSeq)
    (hret   : decodeX64 (fetchWindow16 cmap 0x4000c7#64) = .ok .ret64 1)
    (s0 : X64State) (nd : Nat → UndefChoice) :
    ∀ (rem : Nat) (p : BitVec 64) (a b : BitVec 32) (idx : Nat) (st : X64State),
      NoWrapSlice p (rem + 1) →
      AdlerInv s0 (p + BitVec.ofNat 64 (rem + 1)) p a b st →
      ∃ steps : Nat,
        let sf := runFrom cmap steps idx nd st
        let (af, bf) := rustAdler32Loop s0.mem p (rem + 1) a b
        sf.halted = true ∧ sf.fault = false ∧
        SysVCalleeSavedPreserved s0 sf ∧ sf.ymms = s0.ymms ∧ sf.mem = s0.mem ∧
        BitVec.extractLsb' 0 32 (sf.regs .rax) = (bf <<< 16) ||| af := by
  intro rem
  induction rem with
  | zero =>
    intro p a b idx st _ hin
    refine ⟨8 + (9 + (1 + (1 + 4))), ?_⟩
    dsimp only
    rw [runFrom_add, runFrom_add, runFrom_add, runFrom_add]
    rcases runFrom_of_decodeSeqAt hbodyA idx nd st hin.run hin.nf hin.rip with ⟨hseqA, _, _⟩
    rw [hseqA]
    rcases adler_step_A hin with ⟨hrA, hfA, hripA, hmA, hyA, hcsA, hrdiA, hrsiA, hr8A, hrdxA, hraxA, ha'lt⟩
    generalize execInstrSeq 8 adlerLoopASeq idx nd st = sa at hrA hfA hripA hmA hyA hcsA hrdiA hrsiA hr8A hrdxA hraxA ⊢
    rcases runFrom_of_decodeSeqAt hbodyB (idx + 8) nd sa hrA hfA hripA with ⟨hseqB, _, _⟩
    rw [hseqB]
    rcases adler_step_B hrA hfA hripA hmA hyA hcsA hrdiA hrsiA hr8A hrdxA hraxA ha'lt hin.hb with
      ⟨hrB, hfB, hripB, hmB, hyB, hcsB, hrdiB, hrsiB, _, hrcxB, hrdxB, _⟩
    generalize execInstrSeq 9 adlerLoopBSeq (idx + 8) nd sa = sb at hrB hfB hripB hmB hyB hcsB hrdiB hrsiB hrcxB hrdxB ⊢
    have hs_cmp : runFrom cmap 1 (idx + 8 + 9) nd sb =
        execByteInstr (if swapCmp then .aluRmReg .s64 .cmp (.reg .rdi) .rsi else .aluRmReg .s64 .cmp (.reg .rsi) .rdi)
          0x4000be#64 (nd (idx + 8 + 9)) sb := by
      rw [runFrom_succ, runFrom_zero, step_at_concrete hcmp _ sb hrB hfB hripB]; rfl
    rw [hs_cmp]
    have hsc_p :
        let sc := execByteInstr (if swapCmp then .aluRmReg .s64 .cmp (.reg .rdi) .rsi else .aluRmReg .s64 .cmp (.reg .rsi) .rdi)
                    0x4000be#64 (nd (idx + 8 + 9)) sb
        sc.halted = false ∧ sc.fault = false ∧ sc.rip = 0x4000be#64 ∧
        sc.mem = s0.mem ∧ sc.ymms = s0.ymms ∧ sc.regs = sb.regs ∧ sc.flags.zf = true := by
      cases swapCmp
      · dsimp only; simp only [Bool.false_eq_true, ite_false]; rw [exec_aluRmReg_s64_cmp]
        exact ⟨hrB, hfB, rfl, hmB, hyB, rfl, by rw [cmp_flags_zf, hrsiB, hrdiB]; exact cmp_sub_self_zero _⟩
      · dsimp only; simp only [ite_true]; rw [exec_aluRmReg_s64_cmp]
        exact ⟨hrB, hfB, rfl, hmB, hyB, rfl, by rw [cmp_flags_zf, hrdiB, hrsiB]; exact cmp_sub_self_zero _⟩
    generalize execByteInstr (if swapCmp then .aluRmReg .s64 .cmp (.reg .rdi) .rsi else .aluRmReg .s64 .cmp (.reg .rsi) .rdi)
                 0x4000be#64 (nd (idx + 8 + 9)) sb = sc at hsc_p ⊢
    have hs_jne : runFrom cmap 1 (idx + 8 + 9 + 1) nd sc = { sc with
          rip := 0x4000c0#64 } := by
      rw [runFrom_succ, runFrom_zero, step_at_concrete hjne _ sc hsc_p.1 hsc_p.2.1 hsc_p.2.2.1,
          exec_jcc_fall (evalCond_ne_of_zf_true hsc_p.2.2.2.2.2.2)]; rfl
    rw [hs_jne, rustAdler32Loop_succ, rustAdler32Loop_zero]
    have hreg := hsc_p.2.2.2.2.2.1
    have hcs_sc : SysVCalleeSavedPreserved s0 { sc with
          rip := 0x4000c0#64 } := by
      rcases hcsB with ⟨c1, c2, c3, c4, c5, c6, c7⟩
      exact ⟨hreg ▸ c1, hreg ▸ c2, hreg ▸ c3, hreg ▸ c4, hreg ▸ c5, hreg ▸ c6, hreg ▸ c7⟩
    exact adler_exit_pack hexit hret hsc_p.1 hsc_p.2.1 rfl hsc_p.2.2.2.1 hsc_p.2.2.2.2.1 hcs_sc
      (hreg ▸ hrcxB) (hreg ▸ hrdxB)
  | succ k ih =>
    intro p a b idx st hnw hin
    rcases runFrom_of_decodeSeqAt hbodyA idx nd st hin.run hin.nf hin.rip with ⟨hseqA, _, _⟩
    rcases adler_step_A hin with ⟨hrA, hfA, hripA, hmA, hyA, hcsA, hrdiA, hrsiA, hr8A, hrdxA, hraxA, ha'lt⟩
    generalize execInstrSeq 8 adlerLoopASeq idx nd st = sa at hseqA hrA hfA hripA hmA hyA hcsA hrdiA hrsiA hr8A hrdxA hraxA
    rcases runFrom_of_decodeSeqAt hbodyB (idx + 8) nd sa hrA hfA hripA with ⟨hseqB, _, _⟩
    rcases adler_step_B hrA hfA hripA hmA hyA hcsA hrdiA hrsiA hr8A hrdxA hraxA ha'lt hin.hb with
      ⟨hrB, hfB, hripB, hmB, hyB, hcsB, hrdiB, hrsiB, hr8B, hrcxB, hrdxB, hb'lt⟩
    generalize execInstrSeq 9 adlerLoopBSeq (idx + 8) nd sa = sb at hseqB hrB hfB hripB hmB hyB hcsB hrdiB hrsiB hr8B hrcxB hrdxB
    have hs_cmp : runFrom cmap 1 (idx + 8 + 9) nd sb =
        execByteInstr (if swapCmp then .aluRmReg .s64 .cmp (.reg .rdi) .rsi else .aluRmReg .s64 .cmp (.reg .rsi) .rdi)
          0x4000be#64 (nd (idx + 8 + 9)) sb := by
      rw [runFrom_succ, runFrom_zero, step_at_concrete hcmp _ sb hrB hfB hripB]; rfl
    have hne1 : p + BitVec.ofNat 64 (k + 2) ≠ p + 1#64 := ptr_offset_ne hnw (by omega) (by omega) (by omega)
    have hne2 : p + 1#64 ≠ p + BitVec.ofNat 64 (k + 2) := fun h => hne1 h.symm
    have hsc_p :
        let sc := execByteInstr (if swapCmp then .aluRmReg .s64 .cmp (.reg .rdi) .rsi else .aluRmReg .s64 .cmp (.reg .rsi) .rdi)
                    0x4000be#64 (nd (idx + 8 + 9)) sb
        sc.halted = false ∧ sc.fault = false ∧ sc.rip = 0x4000be#64 ∧
        sc.mem = s0.mem ∧ sc.ymms = s0.ymms ∧ sc.regs = sb.regs ∧ sc.flags.zf = false := by
      cases swapCmp
      · dsimp only; simp only [Bool.false_eq_true, ite_false]; rw [exec_aluRmReg_s64_cmp]
        exact ⟨hrB, hfB, rfl, hmB, hyB, rfl, by rw [cmp_flags_zf, hrsiB, hrdiB]; exact cmp_sub_zero_false_of_ne hne1⟩
      · dsimp only; simp only [ite_true]; rw [exec_aluRmReg_s64_cmp]
        exact ⟨hrB, hfB, rfl, hmB, hyB, rfl, by rw [cmp_flags_zf, hrdiB, hrsiB]; exact cmp_sub_zero_false_of_ne hne2⟩
    generalize execByteInstr (if swapCmp then .aluRmReg .s64 .cmp (.reg .rdi) .rsi else .aluRmReg .s64 .cmp (.reg .rsi) .rdi)
                 0x4000be#64 (nd (idx + 8 + 9)) sb = sc at hs_cmp hsc_p
    have hs_jne : runFrom cmap 1 (idx + 8 + 9 + 1) nd sc = { sc with
          rip := 0x400080#64 } := by
      rw [runFrom_succ, runFrom_zero, step_at_concrete hjne _ sc hsc_p.1 hsc_p.2.1 hsc_p.2.2.1,
          exec_jcc_taken (evalCond_ne_of_zf_false hsc_p.2.2.2.2.2.2)]; rfl
    have hnw' : NoWrapSlice (p + 1#64) (k + 1) := by
      unfold NoWrapSlice at hnw ⊢
      have hp1 := ptr_offset_toNat hnw (by omega : 1 ≤ k + 2)
      change (p + BitVec.ofNat 64 1).toNat + (k + 1) < 2 ^ 64; omega
    have hend : p + BitVec.ofNat 64 (k + 2) = (p + 1#64) + BitVec.ofNat 64 (k + 1) := by
      change p + BitVec.ofNat 64 (k + 2) = p + BitVec.ofNat 64 1 + BitVec.ofNat 64 (k + 1)
      rw [bv64_add_ofNat_assoc]; congr 2; omega
    let ab' := adlerStep (a, b) (s0.mem p)
    have hreg := hsc_p.2.2.2.2.2.1
    have hin_n : AdlerInv s0 ((p + 1#64) + BitVec.ofNat 64 (k + 1)) (p + 1#64)
        ab'.1 ab'.2 { sc with
          rip := 0x400080#64 } := by
      rcases hcsB with ⟨c1, c2, c3, c4, c5, c6, c7⟩
      exact ⟨hsc_p.1, hsc_p.2.1, rfl, hsc_p.2.2.2.1, hsc_p.2.2.2.2.1,
             ⟨hreg ▸ c1, hreg ▸ c2, hreg ▸ c3, hreg ▸ c4, hreg ▸ c5, hreg ▸ c6, hreg ▸ c7⟩,
             hreg ▸ hrdiB, hend ▸ (hreg ▸ hrsiB), hreg ▸ hr8B, hreg ▸ hrcxB, hreg ▸ hrdxB,
             by dsimp only [ab', adlerStep]; omega, by dsimp only [ab', adlerStep]; omega⟩
    rcases ih (p + 1#64) ab'.1 ab'.2 (idx + 8 + 9 + 1 + 1) { sc with
          rip := 0x400080#64 } hnw' hin_n with ⟨st_ih, hih⟩
    refine ⟨8 + (9 + (1 + (1 + st_ih))), ?_⟩
    dsimp only at hih ⊢
    rw [runFrom_add, hseqA, runFrom_add, hseqB, runFrom_add, hs_cmp, runFrom_add, hs_jne, rustAdler32Loop_succ]
    exact hih

theorem prove_c_adler32_chunk_generic (img : X64ObjImage) (hbase : img.codeBase = 0x400000#64)
    (swapCmp : Bool)
    (hentry : decodeSeqAt (objCodeMap img) 3 0x400050#64 = some adlerEntrySeq)
    (hje    : decodeX64 (fetchWindow16 (objCodeMap img) 0x400059#64) = .ok (.jccRel .e 0x65#64) 2)
    (hpre   : decodeSeqAt (objCodeMap img) 5 0x40005b#64 = some adlerPreSeq)
    (hbodyA : decodeSeqAt (objCodeMap img) 8 0x400080#64 = some adlerLoopASeq)
    (hbodyB : decodeSeqAt (objCodeMap img) 9 0x40009e#64 = some adlerLoopBSeq)
    (hcmp   : decodeX64 (fetchWindow16 (objCodeMap img) 0x4000bb#64) =
              .ok (if swapCmp then .aluRmReg .s64 .cmp (.reg .rdi) .rsi else .aluRmReg .s64 .cmp (.reg .rsi) .rdi) 3)
    (hjne   : decodeX64 (fetchWindow16 (objCodeMap img) 0x4000be#64) = .ok (.jccRel .ne 0xffffffffffffffc0#64) 2)
    (hexit  : decodeSeqAt (objCodeMap img) 3 0x4000c0#64 = some adlerExitSeq)
    (hret   : decodeX64 (fetchWindow16 (objCodeMap img) 0x4000c7#64) = .ok .ret64 1) :
    CObjectMatchesRustContract img 0x50#64 (Adler32Pre 0) (Adler32Post 0) := by
  intro s0 nd hrun hnf hrip ⟨hnw, _⟩
  rw [hbase] at hrip
  have hrip' : s0.rip = 0x400050#64 := hrip
  let cmap := objCodeMap img
  rcases runFrom_of_decodeSeqAt hentry 0 nd s0 hrun hnf hrip' with ⟨hseq_e, _, _⟩
  let init32 := BitVec.extractLsb' 0 32 (s0.regs .rdx)
  rcases adler_init_lo16 (s0.regs .rdx) with ⟨hlo_eq, hlo_le⟩
  have hhi_le : (init32 >>> 16).toNat ≤ 65535 := by
    rw [BitVec.toNat_ushiftRight, Nat.shiftRight_eq_div_pow]; have hlt := init32.isLt; omega
  let se : X64State :=
    { s0 with
      rip := 0x400059#64,
      regs := regUpd (regUpd s0.regs .rcx ((init32 &&& 0xFFFF#32).zeroExtend 64))
        .rdx ((init32 >>> 16).zeroExtend 64),
      flags := (evalAluN (by decide) .test (s0.regs .rsi) (s0.regs .rsi)
        (evalShiftSz .s32 .shr ((BitVec.extractLsb' 0 32 (s0.regs .rdx)).zeroExtend 64) 0x10#8 s0.flags (nd 1).flags).2
        (nd 2).flags).2 }
  have hent_eq : execInstrSeq 3 adlerEntrySeq 0 nd s0 = se := by
    dsimp only [adlerEntrySeq, se]
    rw [execInstrSeq_succ_cons, exec_movzx16_s32_reg,
        execInstrSeq_succ_cons, exec_shiftImm_s32_shr (hc := by decide),
        execInstrSeq_succ_cons, exec_aluRmReg_s64_test, execInstrSeq_zero]
    have hc16 : ((0x10#8 : BitVec 8).toNat &&& 31) = 16 := rfl
    simp only [hc16, init32, regUpd_ne _ (by decide : Reg.rdx ≠ .rcx),
               regUpd_ne _ (by decide : Reg.rsi ≠ .rdx), regUpd_ne _ (by decide : Reg.rsi ≠ .rcx),
               hlo_eq]
  have hcs_e : SysVCalleeSavedPreserved s0 se := by
    dsimp only [SysVCalleeSavedPreserved, se]
    repeat (apply cs_step_caller; · decide)
    exact ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩
  cases hlen : (s0.regs .rsi).toNat with
  | zero =>
    refine ⟨3 + (1 + 4), ?_⟩
    dsimp only
    rw [runX64_eq_runFrom, runFrom_add, hseq_e, hent_eq, runFrom_add]
    have hzf_e : se.flags.zf = true := by dsimp only [se]; rw [test_flags_zf, test64_self_zero_eq, hlen]; rfl
    have hs_je : runFrom cmap 1 3 nd se = { se with rip := 0x4000c0#64 } := by
      rw [runFrom_succ, runFrom_zero, step_at_concrete hje _ se hrun hnf rfl,
          exec_jcc_taken (evalCond_e_of_zf_true hzf_e)]; rfl
    rw [hs_je]
    have hrcx_e : se.regs .rcx = (init32 &&& 0xFFFF#32).zeroExtend 64 := by
      dsimp only [se]; simp [regUpd_ne _ (by decide : Reg.rcx ≠ .rdx), regUpd_eq]
    have hrdx_e : se.regs .rdx = (init32 >>> 16).zeroExtend 64 := by
      dsimp only [se]; exact regUpd_eq _ _ _
    rcases adler_exit_pack hexit hret (st := { se with rip := 0x4000c0#64 }) hrun hnf rfl rfl rfl hcs_e hrcx_e hrdx_e (idx := 0 + 3 + 1) (nd := nd) with
      ⟨hh, hnf', hcs', hym', hmem', hrax⟩
    refine ⟨hh, hnf', hcs', upperClean_of_ymms_eq hym', ?_⟩
    unfold Adler32Post rustAdler32Chunk; rw [hlen, rustAdler32Loop_zero]
    exact ⟨hrax, by rw [hmem']; exact readOnlyFrame_of_mem_eq _ _⟩
  | succ rem =>
    have hzf_e : se.flags.zf = false := by dsimp only [se]; rw [test_flags_zf, test64_self_zero_eq, hlen]; rfl
    let s2 : X64State := { se with rip := 0x40005b#64 }
    have hs_je : runFrom cmap 1 3 nd se = s2 := by
      rw [runFrom_succ, runFrom_zero, step_at_concrete hje _ se hrun hnf rfl,
          exec_jcc_fall (evalCond_e_of_zf_false hzf_e)]; rfl
    rcases runFrom_of_decodeSeqAt hpre 4 nd s2 hrun hnf rfl with ⟨hseq_p, _, _⟩
    let sp : X64State :=
      { s2 with
        rip := 0x400080#64,
        regs := regUpd (regUpd s2.regs .rsi (s2.regs .rsi + s2.regs .rdi)) .r8 0x0000000080078071#64,
        flags := (evalAluN (by decide) .add (s2.regs .rsi) (s2.regs .rdi) s2.flags (nd 4).flags).2 }
    have hpre_eq : execInstrSeq 5 adlerPreSeq 4 nd s2 = sp := by
      dsimp only [adlerPreSeq, sp]
      rw [execInstrSeq_succ_cons, exec_aluRmReg_s64_add,
          execInstrSeq_succ_cons, exec_movImm_s32,
          execInstrSeq_succ_cons, exec_nop,
          execInstrSeq_succ_cons, exec_nop,
          execInstrSeq_succ_cons, exec_nop, execInstrSeq_zero]
      rfl
    have hrsi_eq : s0.regs .rsi = BitVec.ofNat 64 (rem + 1) := by
      apply BitVec.eq_of_toNat_eq
      rw [hlen, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by rw [← hlen]; exact (s0.regs .rsi).isLt)]
    have hnw' : NoWrapSlice (s0.regs .rdi) (rem + 1) := by rwa [← hlen]
    have hcs_p : SysVCalleeSavedPreserved s0 sp := by
      dsimp only [SysVCalleeSavedPreserved, sp]
      repeat (apply cs_step_caller; · decide)
      exact hcs_e
    have hin0 : AdlerInv s0 (s0.regs .rdi + BitVec.ofNat 64 (rem + 1)) (s0.regs .rdi)
        (init32 &&& 0xFFFF#32) (init32 >>> 16) sp := by
      refine ⟨hrun, hnf, rfl, rfl, rfl, hcs_p, ?_, ?_, ?_, ?_, ?_, hlo_le, hhi_le⟩
      · dsimp only [sp, s2, se]
        simp [regUpd_ne _ (by decide : Reg.rdi ≠ .r8), regUpd_ne _ (by decide : Reg.rdi ≠ .rsi),
              regUpd_ne _ (by decide : Reg.rdi ≠ .rdx), regUpd_ne _ (by decide : Reg.rdi ≠ .rcx)]
      · dsimp only [sp, s2, se]
        simp [regUpd_ne _ (by decide : Reg.rsi ≠ .r8), regUpd_eq,
              regUpd_ne _ (by decide : Reg.rsi ≠ .rdx), regUpd_ne _ (by decide : Reg.rsi ≠ .rcx),
              regUpd_ne _ (by decide : Reg.rdi ≠ .rdx), regUpd_ne _ (by decide : Reg.rdi ≠ .rcx),
              hrsi_eq, BitVec.add_comm]
      · dsimp only [sp]; exact regUpd_eq _ _ _
      · dsimp only [sp, s2, se]
        simp [regUpd_ne _ (by decide : Reg.rcx ≠ .r8), regUpd_ne _ (by decide : Reg.rcx ≠ .rsi),
              regUpd_ne _ (by decide : Reg.rcx ≠ .rdx), regUpd_eq]
      · dsimp only [sp, s2, se]
        simp [regUpd_ne _ (by decide : Reg.rdx ≠ .r8), regUpd_ne _ (by decide : Reg.rdx ≠ .rsi), regUpd_eq]
    rcases adler_loop_ind swapCmp hbodyA hbodyB hcmp hjne hexit hret s0 nd rem (s0.regs .rdi)
        (init32 &&& 0xFFFF#32) (init32 >>> 16) 9 sp hnw' hin0 with ⟨st_l, hl⟩
    refine ⟨3 + (1 + (5 + st_l)), ?_⟩
    dsimp only at hl ⊢
    rw [runX64_eq_runFrom, runFrom_add, hseq_e, hent_eq, runFrom_add, hs_je, runFrom_add, hseq_p, hpre_eq]
    rcases hl with ⟨hh, hnf', hcs', hym', hmem', hrax⟩
    refine ⟨hh, hnf', hcs', upperClean_of_ymms_eq hym', ?_⟩
    unfold Adler32Post rustAdler32Chunk; rw [hlen]
    exact ⟨hrax, hmem' ▸ readOnlyFrame_of_mem_eq _ _⟩

theorem prove_c_adler32_chunk_o2 :
    CObjectMatchesRustContract cFfiKernelsO2Obj 0x50#64 (Adler32Pre 0) (Adler32Post 0) :=
  prove_c_adler32_chunk_generic cFfiKernelsO2Obj rfl false
    (decodeSeqAt_of_check rfl rfl) (decodeAt_of_check rfl)
    (decodeSeqAt_of_check rfl rfl) (decodeSeqAt_of_check rfl rfl) (decodeSeqAt_of_check rfl rfl)
    (decodeAt_of_check rfl) (decodeAt_of_check rfl)
    (decodeSeqAt_of_check rfl rfl) (decodeAt_of_check rfl)

theorem prove_c_adler32_chunk_o3 :
    CObjectMatchesRustContract cFfiKernelsO3Avx2Obj 0x50#64 (Adler32Pre 0) (Adler32Post 0) :=
  prove_c_adler32_chunk_generic cFfiKernelsO3Avx2Obj rfl true
    (decodeSeqAt_of_check rfl rfl) (decodeAt_of_check rfl)
    (decodeSeqAt_of_check rfl rfl) (decodeSeqAt_of_check rfl rfl) (decodeSeqAt_of_check rfl rfl)
    (decodeAt_of_check rfl) (decodeAt_of_check rfl)
    (decodeSeqAt_of_check rfl rfl) (decodeAt_of_check rfl)

end UntrustedCObjScalarLoops
