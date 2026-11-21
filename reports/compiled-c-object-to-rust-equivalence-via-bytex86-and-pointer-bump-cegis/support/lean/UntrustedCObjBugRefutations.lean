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
import Init.Omega
import ByteX86Gcc
import RustFfiSpecs
import CompiledCObjImages
import UntrustedCObjHints

/-!
# `UntrustedCObjBugRefutations`

Kernel-checked negative refutation theorems (`¬ CObjectMatchesRustContract`, `0`
`sorry`, `0` `isPartial`) on the literal `gcc 15.2.0 -O2` compiled object
`cFfiBugsO2Obj` (`support/c_ffi_bugs.c`), driven by minimal witnesses matching
`CaDiCaL 2.1.2` `exit 10` SAT synthesis and `support/repro_c_ffi_bugs.rs`:

1. `refute_bug1_int_len_endpoints`: 32-bit `int len` truncation (`test esi, esi; jle`)
   returns `0` on `len = 0x80000000` (`buf[0] = 1, buf[len-1] = 2`), vs Rust `3`.
2. `refute_bug2_signed_char_fnv1a`: signed `char` sign-extension (`movsx rdx, [rdi]`)
   on `len = 1, buf[0] = 0x80` produces `0xffffffffffffff80` XOR instead of `0x80`.
3. `refute_bug3_off_by_one_xor`: off-by-one `i <= len` (`cmp rsi, rax; jae`)
   overwrites `dst[0]` on `len = 0`, violating `RustXorStreamPost` memory framing.
4. `refute_bug4_asm_clobber_abi`: returns the exact Rust sum (`rax = 0` on `len = 0`),
   yet clobbers callee-saved `rbx`/`r12` and leaves dirty `YMM0[255:128] = 0xff..ff`
   without `vzeroupper`, violating both `SysVCalleeSavedPreserved` and
   `UpperYmmCleanOrPreserved`.
-/

namespace UntrustedCObjBugRefutations

open ByteX86Gcc
open RustFfiSpecs
open CompiledCObjImages
open UntrustedCObjHints

private def zeroFlags : RFlags := { cf := false, pf := false, af := false, zf := false, sf := false, of := false }
private def zeroUndef : UndefChoice := { flags := zeroFlags, undefGpr := 0#64 }
private def constNd : Nat → UndefChoice := fun _ => zeroUndef

private theorem exec_aluRmReg_s32_test (dst src : Reg) (nr : BitVec 64) (ch : UndefChoice) (s : X64State) :
    execByteInstr (.aluRmReg .s32 .test (.reg dst) src) nr ch s =
      { s with rip := nr,
               flags := (evalAluN (by decide) .test (BitVec.extractLsb' 0 32 (s.regs dst))
                 (BitVec.extractLsb' 0 32 (s.regs src)) s.flags ch.flags).2 } := by
  dsimp only [execByteInstr, evalAluSz, readByteRm, readRegSz]
  rw [ifTrue (by decide), zext32_extract32_eq, zext32_extract32_eq]

private theorem exec_unaryRm_s64_inc (dst : Reg) (nr : BitVec 64) (ch : UndefChoice) (s : X64State) :
    execByteInstr (.unaryRm .s64 .inc (.reg dst)) nr ch s =
      { s with rip := nr,
               regs := regUpd s.regs dst (s.regs dst + 1#64),
               flags := (evalUnarySz .s64 .inc (s.regs dst) s.flags).2 } := rfl

private theorem exec_simdCmpeq_vex256_e32_self (r : YmmIdx) (nr : BitVec 64) (ch : UndefChoice) (s : X64State) :
    execByteInstr (.simdCmpeq .vex256 .e32 r r (.reg r)) nr ch s =
      { s with rip := nr,
               ymms := ymmUpd s.ymms r
                 ((packDwords128 fun i => if getDword128 (BitVec.extractLsb' 128 128 (s.ymms r)) i ==
                                            getDword128 (BitVec.extractLsb' 128 128 (s.ymms r)) i
                                          then 0xFFFFFFFF#32 else 0#32) ++
                  (packDwords128 fun i => if getDword128 (BitVec.extractLsb' 0 128 (s.ymms r)) i ==
                                            getDword128 (BitVec.extractLsb' 0 128 (s.ymms r)) i
                                          then 0xFFFFFFFF#32 else 0#32)) } := rfl

private theorem runX64_halted_unique {img : X64ObjImage} {s0 sh : X64State} {nd : Nat → UndefChoice}
    {k : Nat} (hrun : runFrom (objCodeMap img) k 0 nd s0 = sh)
    (hpre : ∀ j : Nat, j < k → (runFrom (objCodeMap img) j 0 nd s0).halted = false)
    (hh : sh.halted = true) (steps : Nat) (hhs : (runX64 img steps nd s0).halted = true) :
    runX64 img steps nd s0 = sh := by
  rw [runX64_eq_runFrom] at hhs ⊢
  by_cases hlt : steps < k
  · exact absurd hhs (by rw [hpre steps hlt]; decide)
  · have hsplit : steps = k + (steps - k) := by omega
    rw [hsplit, runFrom_add, hrun, runFrom_halted_const _ _ _ _ _ hh]

private theorem halted_false_prefix {cmap : CodeMap} {s0 sMid : X64State} {nd : Nat → UndefChoice}
    {m : Nat} (hrm : runFrom cmap m 0 nd s0 = sMid) (hf : sMid.halted = false) :
    ∀ j : Nat, j ≤ m → (runFrom cmap j 0 nd s0).halted = false := by
  intro j hj
  cases hq : (runFrom cmap j 0 nd s0).halted
  · rfl
  · have hsub : m = j + (m - j) := by omega
    have hc := runFrom_halted_const cmap (m - j) (0 + j) nd _ hq
    rw [← runFrom_add, ← hsub, hrm] at hc
    rw [hc, hq] at hf; nomatch hf

/-! ## Bug 1: `c_bug1_int_len_endpoints` (`0x00`, 32-bit `int len` truncation) -/

private def bug1InitState : X64State :=
  { rip := 0x400000#64,
    regs := fun r => match r with
      | .rdi => 0x100000#64
      | .rsi => 0x80000000#64
      | .rsp => 0x10000#64
      | _    => 0#64,
    ymms := fun _ => 0#256,
    flags := zeroFlags,
    mem := fun a =>
      if a == 0x100000#64 then 1#8
      else if a == 0x800fffff#64 then 2#8
      else 0#8,
    halted := false,
    fault := false }

private theorem bug1_trace :
    let cmap := objCodeMap cFfiBugsO2Obj
    let sf := runFrom cmap 4 0 constNd bug1InitState
    sf.halted = true ∧ sf.regs .rax = 0#64 ∧
    (∀ j : Nat, j < 4 → (runFrom cmap j 0 constNd bug1InitState).halted = false) := by
  have hd0 : decodeX64 (fetchWindow16 (objCodeMap cFfiBugsO2Obj) 0x400000#64) =
      .ok (.aluRmReg .s32 .xor (.reg .rax) .rax) 2 := decodeAt_of_check rfl
  have hd1 : decodeX64 (fetchWindow16 (objCodeMap cFfiBugsO2Obj) 0x400002#64) =
      .ok (.aluRmReg .s32 .test (.reg .rsi) .rsi) 2 := decodeAt_of_check rfl
  have hd2 : decodeX64 (fetchWindow16 (objCodeMap cFfiBugsO2Obj) 0x400004#64) =
      .ok (.jccRel .le 0x10#64) 2 := decodeAt_of_check rfl
  have hd3 : decodeX64 (fetchWindow16 (objCodeMap cFfiBugsO2Obj) 0x400016#64) =
      .ok .ret64 1 := decodeAt_of_check rfl
  let cmap := objCodeMap cFfiBugsO2Obj
  let s1 : X64State :=
    { bug1InitState with
      rip := 0x400002#64,
      regs := regUpd bug1InitState.regs .rax 0#64,
      flags := (evalAluN (by decide) .xor (BitVec.extractLsb' 0 32 (bug1InitState.regs .rax))
        (BitVec.extractLsb' 0 32 (bug1InitState.regs .rax)) bug1InitState.flags zeroFlags).2 }
  have hs1 : stepX64 cmap (constNd 0) bug1InitState = s1 := by
    rw [step_at_concrete hd0 _ bug1InitState rfl rfl rfl, exec_aluRmReg_s32_xor_self]; rfl
  let s2 : X64State :=
    { s1 with
      rip := 0x400004#64,
      flags := (evalAluN (by decide) .test (BitVec.extractLsb' 0 32 (s1.regs .rsi))
        (BitVec.extractLsb' 0 32 (s1.regs .rsi)) s1.flags zeroFlags).2 }
  have hs2 : stepX64 cmap (constNd 1) s1 = s2 := by
    rw [step_at_concrete hd1 _ s1 rfl rfl rfl, exec_aluRmReg_s32_test]; rfl
  have hcond : evalCond .le s2.flags = true := by
    dsimp only [evalCond, s2]
    rw [test_flags_zf, test_flags_sf, test_flags_of]
    have hrsi : BitVec.extractLsb' 0 32 (s1.regs .rsi) = 0x80000000#32 := by
      dsimp only [s1]; rw [regUpd_ne _ (by decide : Reg.rsi ≠ .rax)]; rfl
    rw [hrsi]; decide
  let s3 : X64State := { s2 with rip := 0x400016#64 }
  have hs3 : stepX64 cmap (constNd 2) s2 = s3 := by
    rw [step_at_concrete hd2 _ s2 rfl rfl rfl, exec_jcc_taken hcond]; rfl
  have hs4 : stepX64 cmap (constNd 3) s3 = { s3 with halted := true } := by
    rw [step_at_concrete hd3 _ s3 rfl rfl rfl, exec_ret]
  have hr3 : runFrom cmap 3 0 constNd bug1InitState = s3 := by
    rw [runFrom_succ, hs1, runFrom_succ, hs2, runFrom_succ, hs3, runFrom_zero]
  have hr4 : runFrom cmap 4 0 constNd bug1InitState = { s3 with halted := true } := by
    rw [show (4 : Nat) = 3 + 1 from rfl, runFrom_add, hr3, runFrom_succ, runFrom_zero]; exact hs4
  refine ⟨by rw [hr4], ?_, fun j hj => halted_false_prefix hr3 rfl j (by omega)⟩
  rw [hr4]; dsimp only [s3, s2, s1]; exact regUpd_eq _ _ _

theorem refute_bug1_int_len_endpoints :
    ¬ CObjectMatchesRustContract cFfiBugsO2Obj 0x0#64 (Bug1EndpointsPre 0) (Bug1EndpointsPost 0) := by
  intro hmatch
  have hpre : Bug1EndpointsPre 0 bug1InitState := by
    unfold Bug1EndpointsPre NoWrapSlice DisjointFromStack
    exact ⟨by decide, by decide, Or.inr (by decide)⟩
  rcases hmatch bug1InitState constNd rfl rfl rfl hpre with ⟨steps, hh, _, _, _, hrax, _⟩
  rcases bug1_trace with ⟨hh4, hrax4, hlt4⟩
  have heq := runX64_halted_unique rfl hlt4 hh4 steps hh
  rw [heq, hrax4] at hrax
  have hrust : rustEndpointsU64 bug1InitState.mem (bug1InitState.regs .rdi) (bug1InitState.regs .rsi).toNat = 3#64 := by
    have hl : (bug1InitState.regs .rsi).toNat = 0x7fffffff + 1 := rfl
    rw [hl]; rfl
  rw [hrust] at hrax
  exact absurd hrax (by decide)

/-! ## Bug 2: `c_bug2_signed_char_fnv1a` (`0x20`, signed `char` `movsx`) -/

private def bug2InitState : X64State :=
  { rip := 0x400020#64,
    regs := fun r => match r with
      | .rdi => 0x1000#64
      | .rsi => 1#64
      | .rsp => 0x10000#64
      | _    => 0#64,
    ymms := fun _ => 0#256,
    flags := zeroFlags,
    mem := fun _ => 0x80#8,
    halted := false,
    fault := false }

private def bug2PreSeq : List (X64Instr × BitVec 64) :=
  [ (.movImm .s64 .rax 0xcbf29ce484222325#64, 0x40002f#64),
    (.aluRmReg .s64 .add (.reg .rsi) .rdi, 0x400032#64),
    (.movImm .s64 .rcx 0x00000100000001b3#64, 0x40003c#64),
    (.nop, 0x400040#64) ]

private def bug2LoopSeq : List (X64Instr × BitVec 64) :=
  [ (.movsx8 .s64 .rdx (.mem8 { base := some .rdi }), 0x400044#64),
    (.aluImm .s64 .add (.reg .rdi) 1#64, 0x400048#64),
    (.aluRmReg .s64 .xor (.reg .rax) .rdx, 0x40004b#64),
    (.imul2 .s64 .rax (.reg .rcx), 0x40004f#64),
    (.aluRmReg .s64 .cmp (.reg .rsi) .rdi, 0x400052#64) ]

private theorem bug2_trace :
    let cmap := objCodeMap cFfiBugsO2Obj
    let sf := runFrom cmap 13 0 constNd bug2InitState
    sf.halted = true ∧
    sf.regs .rax = (0xcbf29ce484222325#64 ^^^ 0xffffffffffffff80#64) * 0x100000001b3#64 ∧
    (∀ j : Nat, j < 13 → (runFrom cmap j 0 constNd bug2InitState).halted = false) := by
  have hd_t   : decodeX64 (fetchWindow16 (objCodeMap cFfiBugsO2Obj) 0x400020#64) = .ok (.aluRmReg .s64 .test (.reg .rsi) .rsi) 3 := decodeAt_of_check rfl
  have hd_je  : decodeX64 (fetchWindow16 (objCodeMap cFfiBugsO2Obj) 0x400023#64) = .ok (.jccRel .e 0x33#64) 2 := decodeAt_of_check rfl
  have hd_pre : decodeSeqAt (objCodeMap cFfiBugsO2Obj) 4 0x400025#64 = some bug2PreSeq := decodeSeqAt_of_check rfl rfl
  have hd_lp  : decodeSeqAt (objCodeMap cFfiBugsO2Obj) 5 0x400040#64 = some bug2LoopSeq := decodeSeqAt_of_check rfl rfl
  have hd_jne : decodeX64 (fetchWindow16 (objCodeMap cFfiBugsO2Obj) 0x400052#64) = .ok (.jccRel .ne 0xffffffffffffffec#64) 2 := decodeAt_of_check rfl
  have hd_ret : decodeX64 (fetchWindow16 (objCodeMap cFfiBugsO2Obj) 0x400054#64) = .ok .ret64 1 := decodeAt_of_check rfl
  let cmap := objCodeMap cFfiBugsO2Obj
  let s1 : X64State :=
    { bug2InitState with
      rip := 0x400023#64,
      flags := (evalAluN (by decide) .test (bug2InitState.regs .rsi) (bug2InitState.regs .rsi) bug2InitState.flags zeroFlags).2 }
  have hs1 : stepX64 cmap (constNd 0) bug2InitState = s1 := by
    rw [step_at_concrete hd_t _ bug2InitState rfl rfl rfl, exec_aluRmReg_s64_test]; rfl
  have hzf1 : s1.flags.zf = false := by dsimp only [s1]; rw [test_flags_zf]; decide
  let s2 : X64State := { s1 with rip := 0x400025#64 }
  have hs2 : stepX64 cmap (constNd 1) s1 = s2 := by
    rw [step_at_concrete hd_je _ s1 rfl rfl rfl, exec_jcc_fall (evalCond_e_of_zf_false hzf1)]; rfl
  rcases runFrom_of_decodeSeqAt hd_pre 2 constNd s2 rfl rfl rfl with ⟨hpre_r, _, _⟩
  let s6 : X64State :=
    { s2 with
      rip := 0x400040#64,
      regs := regUpd (regUpd (regUpd bug2InitState.regs .rax 0xcbf29ce484222325#64) .rsi 0x1001#64) .rcx 0x100000001b3#64,
      flags := (evalAluN (by decide) .add 1#64 0x1000#64 s2.flags zeroFlags).2 }
  have hs6 : execInstrSeq 4 bug2PreSeq 2 constNd s2 = s6 := by
    dsimp only [bug2PreSeq, s6]
    rw [execInstrSeq_succ_cons, exec_movImm_s64,
        execInstrSeq_succ_cons, exec_aluRmReg_s64_add,
        execInstrSeq_succ_cons, exec_movImm_s64,
        execInstrSeq_succ_cons, exec_nop, execInstrSeq_zero]
    simp only [s2, s1, constNd, regUpd_ne _ (by decide : Reg.rsi ≠ .rax), regUpd_ne _ (by decide : Reg.rdi ≠ .rax)]
    rfl
  rcases runFrom_of_decodeSeqAt hd_lp 6 constNd s6 rfl rfl rfl with ⟨hlp_r, _, _⟩
  have hlp_p :
      let s11 := execInstrSeq 5 bug2LoopSeq 6 constNd s6
      s11.halted = false ∧ s11.fault = false ∧ s11.rip = 0x400052#64 ∧
      s11.regs .rax = (0xcbf29ce484222325#64 ^^^ 0xffffffffffffff80#64) * 0x100000001b3#64 ∧
      s11.flags.zf = true := by
    dsimp only [bug2LoopSeq]
    rw [execInstrSeq_succ_cons, exec_movsx8_s64_mem, evalByteAddr_base,
        execInstrSeq_succ_cons, exec_aluImm_s64_add,
        execInstrSeq_succ_cons, exec_aluRmReg_s64_xor,
        execInstrSeq_succ_cons, exec_imul2_s64_reg,
        execInstrSeq_succ_cons, exec_aluRmReg_s64_cmp, execInstrSeq_zero]
    refine ⟨rfl, rfl, rfl, ?_, ?_⟩
    · simp only [regUpd_eq, regUpd_ne _ (by decide : Reg.rax ≠ .rdi), regUpd_ne _ (by decide : Reg.rax ≠ .rdx),
                 regUpd_ne _ (by decide : Reg.rdx ≠ .rdi), regUpd_ne _ (by decide : Reg.rcx ≠ .rax),
                 regUpd_ne _ (by decide : Reg.rcx ≠ .rdi), regUpd_ne _ (by decide : Reg.rcx ≠ .rdx), s6, s2, s1]
      simp only [regUpd_eq, regUpd_ne _ (by decide : Reg.rax ≠ .rcx), regUpd_ne _ (by decide : Reg.rax ≠ .rsi)]
      rfl
    · rw [cmp_flags_zf]
      simp only [regUpd_eq, regUpd_ne _ (by decide : Reg.rsi ≠ .rax), regUpd_ne _ (by decide : Reg.rsi ≠ .rdi),
                 regUpd_ne _ (by decide : Reg.rsi ≠ .rdx), regUpd_ne _ (by decide : Reg.rdi ≠ .rax),
                 regUpd_ne _ (by decide : Reg.rdi ≠ .rdx), s6, s2, s1]
      simp only [regUpd_eq, regUpd_ne _ (by decide : Reg.rsi ≠ .rcx),
                 regUpd_ne _ (by decide : Reg.rdi ≠ .rcx), regUpd_ne _ (by decide : Reg.rdi ≠ .rsi),
                 regUpd_ne _ (by decide : Reg.rdi ≠ .rax)]
      decide
  generalize execInstrSeq 5 bug2LoopSeq 6 constNd s6 = s11 at hlp_r hlp_p
  let s12 : X64State := { s11 with rip := 0x400054#64 }
  have hs12 : stepX64 cmap (constNd 11) s11 = s12 := by
    rw [step_at_concrete hd_jne _ s11 hlp_p.1 hlp_p.2.1 hlp_p.2.2.1,
        exec_jcc_fall (evalCond_ne_of_zf_true hlp_p.2.2.2.2)]; rfl
  have hs13 : stepX64 cmap (constNd 12) s12 = { s12 with halted := true } := by
    rw [step_at_concrete hd_ret _ s12 hlp_p.1 hlp_p.2.1 rfl, exec_ret]
  have hr1 : runFrom cmap 1 0 constNd bug2InitState = s1 := by rw [runFrom_succ, runFrom_zero, hs1]
  have hr2 : runFrom cmap 1 1 constNd s1 = s2 := by rw [runFrom_succ, runFrom_zero, hs2]
  have hr12 : runFrom cmap 12 0 constNd bug2InitState = s12 := by
    rw [show (12 : Nat) = 1 + (1 + (4 + (5 + 1))) from rfl,
        runFrom_add, hr1, runFrom_add, hr2,
        runFrom_add, hpre_r, hs6, runFrom_add, hlp_r, runFrom_succ, runFrom_zero, hs12]
  have hr13 : runFrom cmap 13 0 constNd bug2InitState = { s12 with halted := true } := by
    rw [show (13 : Nat) = 12 + 1 from rfl, runFrom_add, hr12, runFrom_succ, runFrom_zero]; exact hs13
  refine ⟨by rw [hr13], by rw [hr13]; exact hlp_p.2.2.2.1,
          fun j hj => halted_false_prefix hr12 hlp_p.1 j (by omega)⟩

theorem refute_bug2_signed_char_fnv1a :
    ¬ CObjectMatchesRustContract cFfiBugsO2Obj 0x20#64 (Fnv1a64Pre 0) (Fnv1a64Post 0) := by
  intro hmatch
  have hpre : Fnv1a64Pre 0 bug2InitState := by
    unfold Fnv1a64Pre NoWrapSlice DisjointFromStack
    exact ⟨by decide, by decide, Or.inl (by decide)⟩
  rcases hmatch bug2InitState constNd rfl rfl rfl hpre with ⟨steps, hh, _, _, _, hrax, _⟩
  rcases bug2_trace with ⟨hh13, hrax13, hlt13⟩
  have heq := runX64_halted_unique rfl hlt13 hh13 steps hh
  rw [heq, hrax13] at hrax
  have hrust : rustFnv1a64 bug2InitState.mem (bug2InitState.regs .rdi) (bug2InitState.regs .rsi).toNat =
      (0xcbf29ce484222325#64 ^^^ 0x80#64) * 0x100000001b3#64 := by
    unfold rustFnv1a64
    change rustFnv1a64From bug2InitState.mem 0x1000#64 1 0xcbf29ce484222325#64 = _
    rw [rustFnv1a64From_succ, rustFnv1a64From_zero]; rfl
  rw [hrust] at hrax
  exact absurd hrax (by decide)

/-! ## Bug 3: `c_bug3_off_by_one_xor` (`0x70`, `i <= len` OOB write on `len = 0`) -/

private def bug3InitState : X64State :=
  { rip := 0x400070#64,
    regs := fun r => match r with
      | .rdi => 0x2000#64
      | .rsi => 0x1000#64
      | .rdx => 0#64
      | .rcx => 1#64
      | .rsp => 0x10000#64
      | _    => 0#64,
    ymms := fun _ => 0#256,
    flags := zeroFlags,
    mem := fun a => if a == 0x2000#64 then 0xaa#8 else 0#8,
    halted := false,
    fault := false }

private def bug3PreSeq : List (X64Instr × BitVec 64) :=
  [ (.movStore .s64 (.reg .r8) .rdi, 0x400073#64),
    (.aluRmReg .s32 .xor (.reg .rax) .rax, 0x400075#64),
    (.movStore .s64 (.reg .rdi) .rsi, 0x400078#64),
    (.movStore .s64 (.reg .rsi) .rdx, 0x40007b#64),
    (.nop, 0x400080#64) ]

private def bug3LoopSeq : List (X64Instr × BitVec 64) :=
  [ (.movzx8 .s32 .rdx (.mem8 { base := some .rdi, index := some (.rax, 0) }), 0x400084#64),
    (.aluRmReg .s32 .xor (.reg .rdx) .rcx, 0x400086#64),
    (.mov8Store (.mem8 { base := some .r8, index := some (.rax, 0) }) (.lo8 .rdx), 0x40008a#64),
    (.aluImm .s64 .add (.reg .rax) 1#64, 0x40008e#64),
    (.aluRmReg .s64 .cmp (.reg .rsi) .rax, 0x400091#64) ]

private theorem bug3_trace :
    let cmap := objCodeMap cFfiBugsO2Obj
    let sf := runFrom cmap 12 0 constNd bug3InitState
    sf.halted = true ∧ sf.mem 0x2000#64 = 1#8 ∧
    (∀ j : Nat, j < 12 → (runFrom cmap j 0 constNd bug3InitState).halted = false) := by
  have hd_pre : decodeSeqAt (objCodeMap cFfiBugsO2Obj) 5 0x400070#64 = some bug3PreSeq := decodeSeqAt_of_check rfl rfl
  have hd_lp  : decodeSeqAt (objCodeMap cFfiBugsO2Obj) 5 0x400080#64 = some bug3LoopSeq := decodeSeqAt_of_check rfl rfl
  have hd_jae : decodeX64 (fetchWindow16 (objCodeMap cFfiBugsO2Obj) 0x400091#64) = .ok (.jccRel .ae 0xffffffffffffffed#64) 2 := decodeAt_of_check rfl
  have hd_ret : decodeX64 (fetchWindow16 (objCodeMap cFfiBugsO2Obj) 0x400093#64) = .ok .ret64 1 := decodeAt_of_check rfl
  let cmap := objCodeMap cFfiBugsO2Obj
  rcases runFrom_of_decodeSeqAt hd_pre 0 constNd bug3InitState rfl rfl rfl with ⟨hpre_r, _, _⟩
  have hs5_p :
      let s5 := execInstrSeq 5 bug3PreSeq 0 constNd bug3InitState
      s5.halted = false ∧ s5.fault = false ∧ s5.rip = 0x400080#64 ∧
      s5.mem = bug3InitState.mem ∧
      s5.regs .r8 = 0x2000#64 ∧ s5.regs .rdi = 0x1000#64 ∧
      s5.regs .rsi = 0#64 ∧ s5.regs .rcx = 1#64 ∧ s5.regs .rax = 0#64 := by
    dsimp only [bug3PreSeq]
    rw [execInstrSeq_succ_cons, exec_movStore_s64_reg,
        execInstrSeq_succ_cons, exec_aluRmReg_s32_xor_self,
        execInstrSeq_succ_cons, exec_movStore_s64_reg,
        execInstrSeq_succ_cons, exec_movStore_s64_reg,
        execInstrSeq_succ_cons, exec_nop, execInstrSeq_zero]
    refine ⟨rfl, rfl, rfl, rfl, ?_, ?_, ?_, ?_, ?_⟩
    · simp [regUpd_ne _ (by decide : Reg.r8 ≠ .rsi), regUpd_ne _ (by decide : Reg.r8 ≠ .rdi),
            regUpd_ne _ (by decide : Reg.r8 ≠ .rax), regUpd_eq]; rfl
    · simp [regUpd_ne _ (by decide : Reg.rdi ≠ .rsi), regUpd_eq,
            regUpd_ne _ (by decide : Reg.rsi ≠ .rax), regUpd_ne _ (by decide : Reg.rsi ≠ .r8)]; rfl
    · simp [regUpd_eq, regUpd_ne _ (by decide : Reg.rdx ≠ .rdi), regUpd_ne _ (by decide : Reg.rdx ≠ .rax),
            regUpd_ne _ (by decide : Reg.rdx ≠ .r8)]; rfl
    · simp [regUpd_ne _ (by decide : Reg.rcx ≠ .rsi), regUpd_ne _ (by decide : Reg.rcx ≠ .rdi),
            regUpd_ne _ (by decide : Reg.rcx ≠ .rax), regUpd_ne _ (by decide : Reg.rcx ≠ .r8)]; rfl
    · simp [regUpd_ne _ (by decide : Reg.rax ≠ .rsi), regUpd_ne _ (by decide : Reg.rax ≠ .rdi), regUpd_eq]
  generalize execInstrSeq 5 bug3PreSeq 0 constNd bug3InitState = s5 at hpre_r hs5_p
  rcases runFrom_of_decodeSeqAt hd_lp 5 constNd s5 hs5_p.1 hs5_p.2.1 hs5_p.2.2.1 with ⟨hlp_r, _, _⟩
  have hs10_p :
      let s10 := execInstrSeq 5 bug3LoopSeq 5 constNd s5
      s10.halted = false ∧ s10.fault = false ∧ s10.rip = 0x400091#64 ∧
      s10.mem 0x2000#64 = 1#8 ∧ s10.flags.cf = true := by
    dsimp only [bug3LoopSeq]
    rw [execInstrSeq_succ_cons, exec_movzx8_s32_mem, evalByteAddr_base_idx0,
        execInstrSeq_succ_cons, exec_aluRmReg_s32_xor,
        execInstrSeq_succ_cons, exec_mov8Store_mem_lo8, evalByteAddr_base_idx0,
        execInstrSeq_succ_cons, exec_aluImm_s64_add,
        execInstrSeq_succ_cons, exec_aluRmReg_s64_cmp, execInstrSeq_zero]
    refine ⟨hs5_p.1, hs5_p.2.1, rfl, ?_, ?_⟩
    · simp only [regUpd_eq, regUpd_ne _ (by decide : Reg.r8 ≠ .rdx), regUpd_ne _ (by decide : Reg.rax ≠ .rdx),
                 regUpd_ne _ (by decide : Reg.rcx ≠ .rdx), hs5_p.2.2.2.1, hs5_p.2.2.2.2.1,
                 hs5_p.2.2.2.2.2.1, hs5_p.2.2.2.2.2.2.2.1, hs5_p.2.2.2.2.2.2.2.2]
      decide
    · rw [cmp_flags_cf]
      simp only [regUpd_eq, regUpd_ne _ (by decide : Reg.rsi ≠ .rax), regUpd_ne _ (by decide : Reg.rsi ≠ .rdx),
                 regUpd_ne _ (by decide : Reg.rax ≠ .rdx), hs5_p.2.2.2.2.2.2.1, hs5_p.2.2.2.2.2.2.2.2]
      decide
  generalize execInstrSeq 5 bug3LoopSeq 5 constNd s5 = s10 at hlp_r hs10_p
  let s11 : X64State := { s10 with rip := 0x400093#64 }
  have hs11 : stepX64 cmap (constNd 10) s10 = s11 := by
    rw [step_at_concrete hd_jae _ s10 hs10_p.1 hs10_p.2.1 hs10_p.2.2.1,
        exec_jcc_fall (by rw [evalCond_ae_of_flags, hs10_p.2.2.2.2]; rfl)]; rfl
  have hs12 : stepX64 cmap (constNd 11) s11 = { s11 with halted := true } := by
    rw [step_at_concrete hd_ret _ s11 hs10_p.1 hs10_p.2.1 rfl, exec_ret]
  have hr11 : runFrom cmap 11 0 constNd bug3InitState = s11 := by
    rw [show (11 : Nat) = 5 + (5 + 1) from rfl, runFrom_add, hpre_r, runFrom_add, hlp_r, runFrom_succ, runFrom_zero, hs11]
  have hr12 : runFrom cmap 12 0 constNd bug3InitState = { s11 with halted := true } := by
    rw [show (12 : Nat) = 11 + 1 from rfl, runFrom_add, hr11, runFrom_succ, runFrom_zero]; exact hs12
  refine ⟨by rw [hr12], by rw [hr12]; exact hs10_p.2.2.2.1,
          fun j hj => halted_false_prefix hr11 hs10_p.1 j (by omega)⟩

theorem refute_bug3_off_by_one_xor :
    ¬ CObjectMatchesRustContract cFfiBugsO2Obj 0x70#64 (XorStreamPre 0) (XorStreamContractPost 0) := by
  intro hmatch
  have hpre : XorStreamPre 0 bug3InitState := by
    unfold XorStreamPre NoWrapSlice DisjointSlices DisjointFromStack
    exact ⟨by decide, by decide, Or.inr (by decide), ⟨by decide, Or.inl (by decide)⟩, ⟨by decide, Or.inl (by decide)⟩⟩
  rcases hmatch bug3InitState constNd rfl rfl rfl hpre with ⟨steps, hh, _, _, _, _, hframe⟩
  rcases bug3_trace with ⟨hh12, hmem12, hlt12⟩
  have heq := runX64_halted_unique rfl hlt12 hh12 steps hh
  have hout := hframe 0x2000#64 (by intro ⟨h1, h2⟩; change 0x2000 ≤ _ at h1; change _ < 0x2000 + 0 at h2; omega)
    (by intro ⟨h1, h2⟩; change 0x10000 - 0 ≤ _ at h1; change _ < 0x10000 at h2; omega)
  rw [heq, hmem12] at hout
  exact absurd hout (by decide)

/-! ## Bug 4: `c_bug4_asm_clobber_abi` (`0xa0`, callee-saved `rbx`/`r12` + missing `vzeroupper`) -/

private def bug4InitState : X64State :=
  { rip := 0x4000a0#64,
    regs := fun r => match r with
      | .rdi => 0x1000#64
      | .rsi => 0#64
      | .rsp => 0x10000#64
      | _    => 0#64,
    ymms := fun _ => 0#256,
    flags := zeroFlags,
    mem := fun _ => 0#8,
    halted := false,
    fault := false }

private def bug4EntrySeq : List (X64Instr × BitVec 64) :=
  [ (.aluRmReg .s32 .xor (.reg .r8) .r8, 0x4000a3#64),
    (.movImm .s64 .rbx 0xdeadbeefcafebabe#64, 0x4000ad#64),
    (.unaryRm .s64 .inc (.reg .r12), 0x4000b0#64),
    (.simdCmpeq .vex256 .e32 0 0 (.reg 0), 0x4000b4#64),
    (.movStore .s64 (.reg .rax) .r8, 0x4000b7#64),
    (.aluRmReg .s64 .test (.reg .rsi) .rsi, 0x4000ba#64) ]

theorem bug4_functional_rax_matches_yet_abi_violated :
    let cmap := objCodeMap cFfiBugsO2Obj
    let sf := runFrom cmap 8 0 constNd bug4InitState
    sf.halted = true ∧
    sf.regs .rax = rustSumU8ToU64 bug4InitState.mem (bug4InitState.regs .rdi) (bug4InitState.regs .rsi).toNat ∧
    sf.regs .rbx = 0xdeadbeefcafebabe#64 ∧
    sf.regs .r12 = 1#64 ∧
    BitVec.extractLsb' 128 128 (sf.ymms 0) = 0xffffffffffffffffffffffffffffffff#128 ∧
    (∀ j : Nat, j < 8 → (runFrom cmap j 0 constNd bug4InitState).halted = false) := by
  have hd_ent : decodeSeqAt (objCodeMap cFfiBugsO2Obj) 6 0x4000a0#64 = some bug4EntrySeq := decodeSeqAt_of_check rfl rfl
  have hd_je  : decodeX64 (fetchWindow16 (objCodeMap cFfiBugsO2Obj) 0x4000ba#64) = .ok (.jccRel .e 0xf0#64) 6 := decodeAt_of_check rfl
  have hd_ret : decodeX64 (fetchWindow16 (objCodeMap cFfiBugsO2Obj) 0x4001b0#64) = .ok .ret64 1 := decodeAt_of_check rfl
  let cmap := objCodeMap cFfiBugsO2Obj
  rcases runFrom_of_decodeSeqAt hd_ent 0 constNd bug4InitState rfl rfl rfl with ⟨hent_r, _, _⟩
  have hs6_p :
      let s6 := execInstrSeq 6 bug4EntrySeq 0 constNd bug4InitState
      s6.halted = false ∧ s6.fault = false ∧ s6.rip = 0x4000ba#64 ∧
      s6.regs .rax = 0#64 ∧ s6.regs .rbx = 0xdeadbeefcafebabe#64 ∧ s6.regs .r12 = 1#64 ∧
      BitVec.extractLsb' 128 128 (s6.ymms 0) = 0xffffffffffffffffffffffffffffffff#128 ∧
      s6.flags.zf = true := by
    dsimp only [bug4EntrySeq]
    rw [execInstrSeq_succ_cons, exec_aluRmReg_s32_xor_self,
        execInstrSeq_succ_cons, exec_movImm_s64,
        execInstrSeq_succ_cons, exec_unaryRm_s64_inc,
        execInstrSeq_succ_cons, exec_simdCmpeq_vex256_e32_self,
        execInstrSeq_succ_cons, exec_movStore_s64_reg,
        execInstrSeq_succ_cons, exec_aluRmReg_s64_test, execInstrSeq_zero]
    refine ⟨rfl, rfl, rfl, ?_, ?_, ?_, ?_, ?_⟩
    · simp [regUpd_eq, regUpd_ne _ (by decide : Reg.r8 ≠ .r12), regUpd_ne _ (by decide : Reg.r8 ≠ .rbx)]
    · simp [regUpd_ne _ (by decide : Reg.rbx ≠ .rax), regUpd_ne _ (by decide : Reg.rbx ≠ .r12), regUpd_eq]
    · simp [regUpd_ne _ (by decide : Reg.r12 ≠ .rax), regUpd_eq,
            regUpd_ne _ (by decide : Reg.r12 ≠ .rbx), regUpd_ne _ (by decide : Reg.r12 ≠ .r8)]; rfl
    · simp [ymmUpd]; decide
    · rw [test_flags_zf]
      simp [regUpd_ne _ (by decide : Reg.rsi ≠ .rax), regUpd_ne _ (by decide : Reg.rsi ≠ .r12),
            regUpd_ne _ (by decide : Reg.rsi ≠ .rbx), regUpd_ne _ (by decide : Reg.rsi ≠ .r8)]
      decide
  generalize execInstrSeq 6 bug4EntrySeq 0 constNd bug4InitState = s6 at hent_r hs6_p
  let s7 : X64State := { s6 with rip := 0x4001b0#64 }
  have hs7 : stepX64 cmap (constNd 6) s6 = s7 := by
    rw [step_at_concrete hd_je _ s6 hs6_p.1 hs6_p.2.1 hs6_p.2.2.1,
        exec_jcc_taken (evalCond_e_of_zf_true hs6_p.2.2.2.2.2.2.2)]; rfl
  have hs8 : stepX64 cmap (constNd 7) s7 = { s7 with halted := true } := by
    rw [step_at_concrete hd_ret _ s7 hs6_p.1 hs6_p.2.1 rfl, exec_ret]
  have hr7 : runFrom cmap 7 0 constNd bug4InitState = s7 := by
    rw [show (7 : Nat) = 6 + 1 from rfl, runFrom_add, hent_r, runFrom_succ, runFrom_zero, hs7]
  have hr8 : runFrom cmap 8 0 constNd bug4InitState = { s7 with halted := true } := by
    rw [show (8 : Nat) = 7 + 1 from rfl, runFrom_add, hr7, runFrom_succ, runFrom_zero]; exact hs8
  refine ⟨by rw [hr8], ?_, by rw [hr8]; exact hs6_p.2.2.2.2.1,
          by rw [hr8]; exact hs6_p.2.2.2.2.2.1, by rw [hr8]; exact hs6_p.2.2.2.2.2.2.1,
          fun j hj => halted_false_prefix hr7 hs6_p.1 j (by omega)⟩
  rw [hr8]
  unfold rustSumU8ToU64
  change s6.regs .rax = rustSumU8From bug4InitState.mem 0x1000#64 0 0#64
  rw [rustSumU8From_zero]
  exact hs6_p.2.2.2.1

private theorem bug4_upper_clean : AllUpperYmmClean bug4InitState := by
  intro _
  change BitVec.extractLsb' 128 128 0#256 = 0#128
  decide

theorem refute_bug4_asm_clobber_abi :
    ¬ CObjectMatchesRustContract cFfiBugsO2Obj 0xa0#64 (Bug4SumPre 0) (Bug4SumPost 0) := by
  intro hmatch
  have hpre : Bug4SumPre 0 bug4InitState := by
    unfold Bug4SumPre NoWrapSlice DisjointFromStack
    exact ⟨bug4_upper_clean, by decide, ⟨by decide, Or.inl (by decide)⟩⟩
  rcases hmatch bug4InitState constNd rfl rfl rfl hpre with ⟨steps, hh, _, hcs, _, _⟩
  rcases bug4_functional_rax_matches_yet_abi_violated with ⟨hh8, _, hrbx8, _, _, hlt8⟩
  have heq := runX64_halted_unique rfl hlt8 hh8 steps hh
  have hrbx := hcs.2.1
  rw [heq, hrbx8] at hrbx
  exact absurd hrbx (by decide)

theorem refute_bug4_dirty_upper_ymm :
    ¬ (∀ (s0 : X64State) (nd : Nat → UndefChoice),
        s0.halted = false → s0.fault = false → s0.rip = cFfiBugsO2Obj.codeBase + 0xa0#64 →
        Bug4SumPre 0 s0 →
        ∃ steps : Nat, let s1 := runX64 cFfiBugsO2Obj steps nd s0
          s1.halted = true ∧ UpperYmmCleanOrPreserved s0 s1) := by
  intro hmatch
  have hpre : Bug4SumPre 0 bug4InitState := by
    unfold Bug4SumPre NoWrapSlice DisjointFromStack
    exact ⟨bug4_upper_clean, by decide, ⟨by decide, Or.inl (by decide)⟩⟩
  rcases hmatch bug4InitState constNd rfl rfl rfl hpre with ⟨steps, hh, hym⟩
  rcases bug4_functional_rax_matches_yet_abi_violated with ⟨hh8, _, _, _, hymm8, hlt8⟩
  have heq := runX64_halted_unique rfl hlt8 hh8 steps hh
  have hclean := hym bug4_upper_clean 0
  rw [heq, hymm8] at hclean
  exact absurd hclean (by decide)

end UntrustedCObjBugRefutations
