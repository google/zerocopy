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
# `UntrustedCObjMutLoops`

Kernel-checked equivalence proofs (`0` `sorry`, `0` `isPartial`) for the mutable
scalar C FFI `.o` kernels compiled by `gcc 15.2.0`:
- `c_ascii_tolower` (`-O2` & `-O3 -mavx2`, `0x100`): conditional in-place store
  diamond (`lea edx, [rax - 0x41]; cmp dl, 0x19; ja; add eax, 0x20; mov [rdi], al`)
  with counterless pointer-bump schedule and byte-exact non-slice memory framing.
- `c_xor_stream` (`-O2`, `0x230`): indexed streaming XOR loop with safe-Rust
  `DisjointSlices` read-preservation and byte-exact framing.
-/

namespace UntrustedCObjMutLoops

open ByteX86Gcc
open RustFfiSpecs
open CompiledCObjImages
open UntrustedCObjHints

private theorem upperClean_of_ymms_eq {s0 s1 : X64State} (hy : s1.ymms = s0.ymms) :
    UpperYmmCleanOrPreserved s0 s1 := fun hc idx => hy ▸ hc idx

private theorem bv64_add_toNat_lt {p : BitVec 64} {n i : Nat}
    (hnw : NoWrapSlice p n) (hi : i < n) :
    (p + BitVec.ofNat 64 i).toNat = p.toNat + i :=
  ptr_offset_toNat hnw (by omega)

private theorem not_in_prefix_of_ge {p : BitVec 64} {n done i : Nat}
    (hnw : NoWrapSlice p n) (hdone : done ≤ i) (hi : i < n) :
    ¬ InSliceRange (p + BitVec.ofNat 64 i) p done := by
  intro ⟨_, hlt⟩
  have h := bv64_add_toNat_lt hnw hi
  omega

private theorem not_in_dst_of_disjoint {dst src : BitVec 64} {len done i : Nat}
    (hnwd : NoWrapSlice dst len) (hnws : NoWrapSlice src len)
    (hdisj : DisjointSlices dst len src len) (hd : done ≤ len) (hi : i < len) :
    ¬ InSliceRange (src + BitVec.ofNat 64 i) dst done := by
  intro ⟨hlo, hhi⟩
  have hs := bv64_add_toNat_lt hnws hi
  have _ := hnwd
  rcases hdisj with h1 | h2 <;> omega

private theorem addr_ne_prefix {p : BitVec 64} {n done i : Nat}
    (hnw : NoWrapSlice p n) (hi : i < done) (hd : done < n) :
    p + BitVec.ofNat 64 i ≠ p + BitVec.ofNat 64 done :=
  ptr_offset_ne hnw (by omega) (by omega) (by omega)

private theorem addr_ne_outside {p a : BitVec 64} {n done : Nat}
    (hnw : NoWrapSlice p n) (hd : done < n) (hout : ¬ InSliceRange a p (done + 1)) :
    a ≠ p + BitVec.ofNat 64 done := by
  intro heq
  apply hout
  have h := bv64_add_toNat_lt hnw hd
  exact ⟨by rw [heq, h]; omega, by rw [heq, h]; omega⟩

private theorem not_in_shorter_prefix {p a : BitVec 64} {done : Nat}
    (hout : ¬ InSliceRange a p (done + 1)) : ¬ InSliceRange a p done := by
  intro ⟨h1, h2⟩; exact hout ⟨h1, by omega⟩

private theorem memUpd_eq (m : ByteMem) (a : BitVec 64) (v : BitVec 8) :
    memUpd8 m a v a = v := by
  unfold memUpd8; simp

private theorem memUpd_ne (m : ByteMem) {a b : BitVec 64} (v : BitVec 8) (h : b ≠ a) :
    memUpd8 m a v b = m b := by
  unfold memUpd8; simp [h]

private theorem ascii_sub65_ext8 (c : BitVec 8) :
    BitVec.extractLsb' 0 8 ((BitVec.extractLsb' 0 32 (c.zeroExtend 64 + 0xffffffffffffffbf#64)).zeroExtend 64) =
      c - 65#8 := by
  have h1 : ∀ x : BitVec 64,
      BitVec.extractLsb' 0 8 ((BitVec.extractLsb' 0 32 x).zeroExtend 64) = BitVec.extractLsb' 0 8 x := by
    intro x; apply BitVec.eq_of_getLsbD_eq; intro i hi
    unfold BitVec.zeroExtend
    simp [hi, show i < 32 by omega, show i < 64 by omega]
  rw [h1]
  have h2 : ∀ x y : BitVec 64, BitVec.extractLsb' 0 8 (x + y) =
      BitVec.extractLsb' 0 8 x + BitVec.extractLsb' 0 8 y := by
    intro x y; apply BitVec.eq_of_toNat_eq
    simp only [BitVec.extractLsb'_toNat, Nat.shiftRight_zero, BitVec.toNat_add]
    rw [show (2 ^ 64 : Nat) = 2 ^ 8 * 2 ^ 56 from rfl, Nat.mod_mul_right_mod, Nat.add_mod]
  rw [h2]
  have h3 : BitVec.extractLsb' 0 8 (c.zeroExtend 64) = c := by
    apply BitVec.eq_of_getLsbD_eq; intro i hi
    unfold BitVec.zeroExtend
    simp [hi, show i < 64 by omega]
  have h4 : BitVec.extractLsb' 0 8 0xffffffffffffffbf#64 = 0xbf#8 := rfl
  rw [h3, h4]
  apply BitVec.eq_of_toNat_eq
  rw [BitVec.toNat_add, BitVec.toNat_sub]
  have hbf : (0xbf#8 : BitVec 8).toNat = 191 := rfl
  have h65 : (65#8 : BitVec 8).toNat = 65 := rfl
  rw [hbf, h65, show 2 ^ 8 - 65 = 191 from rfl, Nat.add_comm]

private theorem ascii_add32_ext8 (c : BitVec 8) :
    BitVec.extractLsb' 0 8 ((BitVec.extractLsb' 0 32 (c.zeroExtend 64) + BitVec.extractLsb' 0 32 0x20#64).zeroExtend 64) =
      c + 32#8 := by
  have h1 : ∀ x : BitVec 32,
      BitVec.extractLsb' 0 8 (x.zeroExtend 64) = BitVec.extractLsb' 0 8 x := by
    intro x; apply BitVec.eq_of_getLsbD_eq; intro i hi
    unfold BitVec.zeroExtend
    simp [hi, show i < 32 by omega, show i < 64 by omega]
  rw [h1]
  have h2 : ∀ x y : BitVec 32, BitVec.extractLsb' 0 8 (x + y) =
      BitVec.extractLsb' 0 8 x + BitVec.extractLsb' 0 8 y := by
    intro x y; apply BitVec.eq_of_toNat_eq
    simp only [BitVec.extractLsb'_toNat, Nat.shiftRight_zero, BitVec.toNat_add]
    rw [show (2 ^ 32 : Nat) = 2 ^ 8 * 2 ^ 24 from rfl, Nat.mod_mul_right_mod, Nat.add_mod]
  rw [h2]
  have h3 : BitVec.extractLsb' 0 8 (BitVec.extractLsb' 0 32 (c.zeroExtend 64)) = c := by
    apply BitVec.eq_of_getLsbD_eq; intro i hi
    unfold BitVec.zeroExtend
    simp [hi, show i < 64 by omega]
  have h4 : BitVec.extractLsb' 0 8 (BitVec.extractLsb' 0 32 0x20#64) = 32#8 := rfl
  rw [h3, h4]

private theorem ascii_ja_false_of_lt {d : BitVec 8} (hlt : d.toNat < 26) :
    (!decide (d.toNat < (0x19#8 : BitVec 8).toNat) && !(d - 0x19#8 == 0#8)) = false := by
  have h19 : (0x19#8 : BitVec 8).toNat = 25 := rfl
  by_cases hlt25 : d.toNat < 25
  · have h1 : decide (d.toNat < (0x19#8 : BitVec 8).toNat) = true := by rw [h19]; exact decide_eq_true hlt25
    rw [h1]; rfl
  · have hd25 : d = 0x19#8 := BitVec.eq_of_toNat_eq (by rw [h19]; omega)
    rw [hd25]; rfl

private theorem ascii_ja_true_of_ge {d : BitVec 8} (hge : ¬ d.toNat < 26) :
    (!decide (d.toNat < (0x19#8 : BitVec 8).toNat) && !(d - 0x19#8 == 0#8)) = true := by
  have h19 : (0x19#8 : BitVec 8).toNat = 25 := rfl
  have h1 : decide (d.toNat < (0x19#8 : BitVec 8).toNat) = false := by rw [h19]; exact decide_eq_false (by omega)
  have h2 : (d - 0x19#8 == 0#8) = false := by
    cases hq : (d - 0x19#8 == 0#8)
    · rfl
    · have heq := congrArg BitVec.toNat (eq_of_beq hq)
      rw [BitVec.toNat_sub, h19] at heq
      have hd := d.isLt
      have h0 : (0#8 : BitVec 8).toNat = 0 := rfl
      rw [h0] at heq
      omega
  rw [h1, h2]; rfl

private theorem ascii_tolower_of_lt {c : BitVec 8} (hlt : (c - 65#8).toNat < 26) :
    rustAsciiTolowerByte c = c + 32#8 := by
  unfold rustAsciiTolowerByte; simp only [hlt, ite_true]

private theorem ascii_tolower_of_ge {c : BitVec 8} (hge : ¬ (c - 65#8).toNat < 26) :
    rustAsciiTolowerByte c = c := by
  unfold rustAsciiTolowerByte; simp only [hge, ite_false]

/-! ## 1. `c_ascii_tolower` (`0x100` in `-O2` & `-O3 -mavx2`) -/

def asciiPreSeq : List (X64Instr × BitVec 64) :=
  [ (.aluRmReg .s64 .add (.reg .rsi) .rdi, 0x400108#64),
    (.nop, 0x40010a#64),
    (.nop, 0x400115#64),
    (.nop, 0x400120#64) ]

def asciiHeadSeq : List (X64Instr × BitVec 64) :=
  [ (.movzx8 .s32 .rax (.mem8 { base := some .rdi }), 0x400123#64),
    (.lea .s32 .rdx { base := some .rax, disp := 0xffffffffffffffbf#64 }, 0x400126#64),
    (.alu8Imm .cmp (.reg8 (.lo8 .rdx)) 0x19#8, 0x400129#64) ]

def asciiStoreSeq : List (X64Instr × BitVec 64) :=
  [ (.aluImm .s32 .add (.reg .rax) 0x20#64, 0x40012e#64),
    (.mov8Store (.mem8 { base := some .rdi }) (.lo8 .rax), 0x400130#64) ]

def asciiLatchSeq : List (X64Instr × BitVec 64) :=
  [ (.aluImm .s64 .add (.reg .rdi) 1#64, 0x400134#64),
    (.aluRmReg .s64 .cmp (.reg .rdi) .rsi, 0x400137#64) ]

structure AsciiInv (s0 : X64State) (buf : BitVec 64) (len done : Nat) (st : X64State) : Prop where
  run    : st.halted = false
  nf     : st.fault = false
  rip    : st.rip = 0x400120#64
  ymms   : st.ymms = s0.ymms
  cs     : SysVCalleeSavedPreserved s0 st
  rdi    : st.regs .rdi = buf + BitVec.ofNat 64 done
  rsi    : st.regs .rsi = buf + BitVec.ofNat 64 len
  prefixEq : ∀ i : Nat, i < done →
    st.mem (buf + BitVec.ofNat 64 i) = rustAsciiTolowerByte (s0.mem (buf + BitVec.ofNat 64 i))
  outsideEq : ∀ addr : BitVec 64, ¬ InSliceRange addr buf done → st.mem addr = s0.mem addr

theorem ascii_head_step {s0 : X64State} {buf : BitVec 64} {len done : Nat} {idx : Nat}
    {nd : Nat → UndefChoice} {st : X64State}
    (hnw : NoWrapSlice buf len) (hd : done < len) (hin : AsciiInv s0 buf len done st) :
    let sh := execInstrSeq 3 asciiHeadSeq idx nd st
    let c := s0.mem (buf + BitVec.ofNat 64 done)
    sh.halted = false ∧ sh.fault = false ∧ sh.rip = 0x400129#64 ∧
    sh.mem = st.mem ∧ sh.ymms = s0.ymms ∧ SysVCalleeSavedPreserved s0 sh ∧
    sh.regs .rdi = buf + BitVec.ofNat 64 done ∧
    sh.regs .rsi = buf + BitVec.ofNat 64 len ∧
    sh.regs .rax = c.zeroExtend 64 ∧
    sh.flags.cf = decide ((c - 65#8).toNat < (0x19#8 : BitVec 8).toNat) ∧
    sh.flags.zf = ((c - 65#8) - 0x19#8 == 0#8) := by
  have hc_mem : st.mem (buf + BitVec.ofNat 64 done) = s0.mem (buf + BitVec.ofNat 64 done) :=
    hin.outsideEq _ (not_in_prefix_of_ge hnw (Nat.le_refl done) hd)
  dsimp only [asciiHeadSeq]
  rw [execInstrSeq_succ_cons, exec_movzx8_s32_mem, evalByteAddr_base,
      execInstrSeq_succ_cons, exec_lea_s32, evalByteAddr_base_disp,
      execInstrSeq_succ_cons, exec_alu8Imm_cmp_lo8, execInstrSeq_zero]
  refine ⟨hin.run, hin.nf, rfl, rfl, hin.ymms, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · dsimp only [SysVCalleeSavedPreserved]
    repeat (apply cs_step_caller; · decide)
    exact hin.cs
  · simp only [regUpd_ne _ (by decide : Reg.rdi ≠ .rdx), regUpd_ne _ (by decide : Reg.rdi ≠ .rax), hin.rdi]
  · simp only [regUpd_ne _ (by decide : Reg.rsi ≠ .rdx), regUpd_ne _ (by decide : Reg.rsi ≠ .rax), hin.rsi]
  · simp only [regUpd_ne _ (by decide : Reg.rax ≠ .rdx), regUpd_eq, hin.rdi, hc_mem]
  · rw [cmp_flags_cf]
    simp only [regUpd_eq, hin.rdi, hc_mem, ascii_sub65_ext8]
  · rw [cmp_flags_zf]
    simp only [regUpd_eq, hin.rdi, hc_mem, ascii_sub65_ext8]

theorem ascii_store_step {s0 : X64State} {buf : BitVec 64} {len done : Nat} {idx : Nat}
    {nd : Nat → UndefChoice} {sh : X64State} {c : BitVec 8}
    (hrun : sh.halted = false) (hnf : sh.fault = false) (hym : sh.ymms = s0.ymms)
    (hcs : SysVCalleeSavedPreserved s0 sh)
    (hrdi : sh.regs .rdi = buf + BitVec.ofNat 64 done)
    (hrsi : sh.regs .rsi = buf + BitVec.ofNat 64 len)
    (hrax : sh.regs .rax = c.zeroExtend 64) :
    let ss := execInstrSeq 2 asciiStoreSeq idx nd sh
    ss.halted = false ∧ ss.fault = false ∧ ss.rip = 0x400130#64 ∧
    ss.ymms = s0.ymms ∧ SysVCalleeSavedPreserved s0 ss ∧
    ss.regs .rdi = buf + BitVec.ofNat 64 done ∧
    ss.regs .rsi = buf + BitVec.ofNat 64 len ∧
    ss.mem = memUpd8 sh.mem (buf + BitVec.ofNat 64 done) (c + 32#8) := by
  dsimp only [asciiStoreSeq]
  rw [execInstrSeq_succ_cons, exec_aluImm_s32_add,
      execInstrSeq_succ_cons, exec_mov8Store_mem_lo8, evalByteAddr_base, execInstrSeq_zero]
  refine ⟨hrun, hnf, rfl, hym, ?_, ?_, ?_, ?_⟩
  · dsimp only [SysVCalleeSavedPreserved]
    apply cs_step_caller; · decide
    exact hcs
  · simp only [regUpd_ne _ (by decide : Reg.rdi ≠ .rax), hrdi]
  · simp only [regUpd_ne _ (by decide : Reg.rsi ≠ .rax), hrsi]
  · simp only [regUpd_ne _ (by decide : Reg.rdi ≠ .rax), regUpd_eq, hrdi, hrax, ascii_add32_ext8]

theorem ascii_latch_step {s0 : X64State} {buf : BitVec 64} {len done : Nat} {idx : Nat}
    {nd : Nat → UndefChoice} {sl : X64State}
    (hrun : sl.halted = false) (hnf : sl.fault = false) (hym : sl.ymms = s0.ymms)
    (hcs : SysVCalleeSavedPreserved s0 sl)
    (hrdi : sl.regs .rdi = buf + BitVec.ofNat 64 done)
    (hrsi : sl.regs .rsi = buf + BitVec.ofNat 64 len) :
    let se := execInstrSeq 2 asciiLatchSeq idx nd sl
    se.halted = false ∧ se.fault = false ∧ se.rip = 0x400137#64 ∧
    se.mem = sl.mem ∧ se.ymms = s0.ymms ∧ SysVCalleeSavedPreserved s0 se ∧
    se.regs .rdi = buf + BitVec.ofNat 64 (done + 1) ∧
    se.regs .rsi = buf + BitVec.ofNat 64 len ∧
    se.flags.zf = (buf + BitVec.ofNat 64 (done + 1) - (buf + BitVec.ofNat 64 len) == 0#64) := by
  dsimp only [asciiLatchSeq]
  rw [execInstrSeq_succ_cons, exec_aluImm_s64_add,
      execInstrSeq_succ_cons, exec_aluRmReg_s64_cmp, execInstrSeq_zero]
  have hptr : buf + BitVec.ofNat 64 done + 1#64 = buf + BitVec.ofNat 64 (done + 1) := by
    change buf + BitVec.ofNat 64 done + BitVec.ofNat 64 1 = buf + BitVec.ofNat 64 (done + 1)
    rw [bv64_add_ofNat_assoc]
  refine ⟨hrun, hnf, rfl, rfl, hym, ?_, ?_, ?_, ?_⟩
  · dsimp only [SysVCalleeSavedPreserved]
    apply cs_step_caller; · decide
    exact hcs
  · simp only [regUpd_eq, hrdi, hptr]
  · simp only [regUpd_ne _ (by decide : Reg.rsi ≠ .rdi), hrsi]
  · rw [cmp_flags_zf]
    simp only [regUpd_eq, regUpd_ne _ (by decide : Reg.rsi ≠ .rdi), hrdi, hrsi, hptr]

theorem ascii_diamond_step {cmap : CodeMap}
    (hhead  : decodeSeqAt cmap 3 0x400120#64 = some asciiHeadSeq)
    (hja    : decodeX64 (fetchWindow16 cmap 0x400129#64) = .ok (.jccRel .a 0x05#64) 2)
    (hstore : decodeSeqAt cmap 2 0x40012b#64 = some asciiStoreSeq)
    {s0 : X64State} {buf : BitVec 64} {len done : Nat} {idx : Nat}
    {nd : Nat → UndefChoice} {st : X64State}
    (hnw : NoWrapSlice buf len) (hd : done < len) (hin : AsciiInv s0 buf len done st) :
    ∃ (k : Nat) (sl : X64State),
      runFrom cmap k idx nd st = sl ∧
      sl.halted = false ∧ sl.fault = false ∧ sl.rip = 0x400130#64 ∧
      sl.ymms = s0.ymms ∧ SysVCalleeSavedPreserved s0 sl ∧
      sl.regs .rdi = buf + BitVec.ofNat 64 done ∧
      sl.regs .rsi = buf + BitVec.ofNat 64 len ∧
      (∀ i : Nat, i < done + 1 →
        sl.mem (buf + BitVec.ofNat 64 i) = rustAsciiTolowerByte (s0.mem (buf + BitVec.ofNat 64 i))) ∧
      (∀ addr : BitVec 64, ¬ InSliceRange addr buf (done + 1) → sl.mem addr = s0.mem addr) := by
  rcases runFrom_of_decodeSeqAt hhead idx nd st hin.run hin.nf hin.rip with ⟨hseq_h, _, _⟩
  rcases ascii_head_step hnw hd hin with ⟨hr1, hf1, hrip1, hm1, hy1, hcs1, hrdi1, hrsi1, hrax1, hcf1, hzf1⟩
  generalize execInstrSeq 3 asciiHeadSeq idx nd st = sh at hseq_h hr1 hf1 hrip1 hm1 hy1 hcs1 hrdi1 hrsi1 hrax1 hcf1 hzf1
  let c := s0.mem (buf + BitVec.ofNat 64 done)
  by_cases hlt : (c - 65#8).toNat < 26
  · have hcond : evalCond .a sh.flags = false := by
      rw [evalCond_a_of_flags, hcf1, hzf1]; exact ascii_ja_false_of_lt hlt
    have hs_ja : runFrom cmap 1 (idx + 3) nd sh = { sh with rip := 0x40012b#64 } := by
      rw [runFrom_succ, runFrom_zero, step_at_concrete hja _ sh hr1 hf1 hrip1,
          exec_jcc_fall hcond]; rfl
    rcases runFrom_of_decodeSeqAt hstore (idx + 3 + 1) nd { sh with rip := 0x40012b#64 } hr1 hf1 rfl with ⟨hseq_s, _, _⟩
    rcases ascii_store_step (sh := { sh with rip := 0x40012b#64 }) (idx := idx + 3 + 1) (nd := nd)
        hr1 hf1 hy1 hcs1 hrdi1 hrsi1 hrax1 with
      ⟨hr2, hf2, hrip2, hy2, hcs2, hrdi2, hrsi2, hm2⟩
    generalize execInstrSeq 2 asciiStoreSeq (idx + 3 + 1) nd { sh with rip := 0x40012b#64 } = ss at hseq_s hr2 hf2 hrip2 hy2 hcs2 hrdi2 hrsi2 hm2
    refine ⟨3 + (1 + 2), ss, ?_, hr2, hf2, hrip2, hy2, hcs2, hrdi2, hrsi2, ?_, ?_⟩
    · rw [runFrom_add, hseq_h, runFrom_add, hs_ja, hseq_s]
    · intro i hi
      by_cases hcur : i = done
      · subst hcur; rw [hm2, memUpd_eq, ascii_tolower_of_lt hlt]
      · have hilt : i < done := by omega
        rw [hm2, memUpd_ne _ _ (addr_ne_prefix hnw hilt hd), hm1]
        exact hin.prefixEq i hilt
    · intro addr hout
      rw [hm2, memUpd_ne _ _ (addr_ne_outside hnw hd hout), hm1]
      exact hin.outsideEq addr (not_in_shorter_prefix hout)
  · have hcond : evalCond .a sh.flags = true := by
      rw [evalCond_a_of_flags, hcf1, hzf1]; exact ascii_ja_true_of_ge hlt
    have hs_ja : runFrom cmap 1 (idx + 3) nd sh = { sh with rip := 0x400130#64 } := by
      rw [runFrom_succ, runFrom_zero, step_at_concrete hja _ sh hr1 hf1 hrip1,
          exec_jcc_taken hcond]; rfl
    refine ⟨3 + 1, { sh with rip := 0x400130#64 }, ?_, hr1, hf1, rfl, hy1, hcs1, hrdi1, hrsi1, ?_, ?_⟩
    · rw [runFrom_add, hseq_h, hs_ja]
    · intro i hi
      by_cases hcur : i = done
      · subst hcur
        change sh.mem (buf + BitVec.ofNat 64 i) = rustAsciiTolowerByte c
        rw [hm1, hin.outsideEq _ (not_in_prefix_of_ge hnw (Nat.le_refl i) hd), ascii_tolower_of_ge hlt]
      · have hilt : i < done := by omega
        change sh.mem (buf + BitVec.ofNat 64 i) = _
        rw [hm1]; exact hin.prefixEq i hilt
    · intro addr hout
      change sh.mem addr = s0.mem addr
      rw [hm1]; exact hin.outsideEq addr (not_in_shorter_prefix hout)

theorem ascii_loop_ind {cmap : CodeMap}
    (hhead  : decodeSeqAt cmap 3 0x400120#64 = some asciiHeadSeq)
    (hja    : decodeX64 (fetchWindow16 cmap 0x400129#64) = .ok (.jccRel .a 0x05#64) 2)
    (hstore : decodeSeqAt cmap 2 0x40012b#64 = some asciiStoreSeq)
    (hlatch : decodeSeqAt cmap 2 0x400130#64 = some asciiLatchSeq)
    (hjne   : decodeX64 (fetchWindow16 cmap 0x400137#64) = .ok (.jccRel .ne 0xffffffffffffffe7#64) 2)
    (hret   : decodeX64 (fetchWindow16 cmap 0x400139#64) = .ok .ret64 1)
    (s0 : X64State) (buf : BitVec 64) (len : Nat) (hnw : NoWrapSlice buf len)
    (nd : Nat → UndefChoice) :
    ∀ (rem done idx : Nat) (st : X64State),
      done + (rem + 1) = len →
      AsciiInv s0 buf len done st →
      ∃ steps : Nat,
        let sf := runFrom cmap steps idx nd st
        sf.halted = true ∧ sf.fault = false ∧
        SysVCalleeSavedPreserved s0 sf ∧ sf.ymms = s0.ymms ∧
        RustAsciiTolowerPost s0.mem sf.mem buf len (s0.regs .rsp) 0 := by
  intro rem
  induction rem with
  | zero =>
    intro done idx st hsum hin
    have hd : done < len := by omega
    rcases ascii_diamond_step hhead hja hstore hnw hd hin with
      ⟨kd, sl, hrun_d, hrl, hfl, hripl, hyl, hcsl, hrdil, hrsil, hpref, hout⟩
    rcases runFrom_of_decodeSeqAt hlatch (idx + kd) nd sl hrl hfl hripl with ⟨hseq_l, _, _⟩
    rcases ascii_latch_step (idx := idx + kd) (nd := nd) hrl hfl hyl hcsl hrdil hrsil with
      ⟨hre, hfe, hripe, hme, hye, hcse, hrdie, hrsie, hzfe⟩
    generalize execInstrSeq 2 asciiLatchSeq (idx + kd) nd sl = se at hseq_l hre hfe hripe hme hye hcse hrdie hrsie hzfe
    have heq_end : done + 1 = len := by omega
    have hzf_t : se.flags.zf = true := by rw [hzfe, heq_end]; exact cmp_sub_self_zero _
    have hs_jne : runFrom cmap 1 (idx + kd + 2) nd se = { se with rip := 0x400139#64 } := by
      rw [runFrom_succ, runFrom_zero, step_at_concrete hjne _ se hre hfe hripe,
          exec_jcc_fall (evalCond_ne_of_zf_true hzf_t)]; rfl
    have hs_ret : runFrom cmap 1 (idx + kd + 2 + 1) nd { se with rip := 0x400139#64 } =
        { se with rip := 0x400139#64, halted := true } := by
      rw [runFrom_succ, runFrom_zero, step_at_concrete hret _ { se with rip := 0x400139#64 } hre hfe rfl, exec_ret]
    refine ⟨kd + (2 + (1 + 1)), ?_⟩
    dsimp only
    rw [runFrom_add, hrun_d, runFrom_add, hseq_l, runFrom_add, hs_jne, hs_ret]
    refine ⟨rfl, hfe, hcse, hye, ?_, ?_⟩
    · intro i hi; change se.mem _ = _; rw [hme]; exact hpref i (by omega)
    · intro addr hni _; change se.mem addr = _; rw [hme]; exact hout addr (by rwa [heq_end])
  | succ k ih =>
    intro done idx st hsum hin
    have hd : done < len := by omega
    rcases ascii_diamond_step hhead hja hstore hnw hd hin with
      ⟨kd, sl, hrun_d, hrl, hfl, hripl, hyl, hcsl, hrdil, hrsil, hpref, hout⟩
    rcases runFrom_of_decodeSeqAt hlatch (idx + kd) nd sl hrl hfl hripl with ⟨hseq_l, _, _⟩
    rcases ascii_latch_step (idx := idx + kd) (nd := nd) hrl hfl hyl hcsl hrdil hrsil with
      ⟨hre, hfe, hripe, hme, hye, hcse, hrdie, hrsie, hzfe⟩
    generalize execInstrSeq 2 asciiLatchSeq (idx + kd) nd sl = se at hseq_l hre hfe hripe hme hye hcse hrdie hrsie hzfe
    have hne : buf + BitVec.ofNat 64 (done + 1) ≠ buf + BitVec.ofNat 64 len :=
      ptr_offset_ne hnw (by omega) (by omega) (by omega)
    have hzf_f : se.flags.zf = false := by rw [hzfe]; exact cmp_sub_zero_false_of_ne hne
    have hs_jne : runFrom cmap 1 (idx + kd + 2) nd se = { se with rip := 0x400120#64 } := by
      rw [runFrom_succ, runFrom_zero, step_at_concrete hjne _ se hre hfe hripe,
          exec_jcc_taken (evalCond_ne_of_zf_false hzf_f)]; rfl
    have hin_n : AsciiInv s0 buf len (done + 1) { se with rip := 0x400120#64 } :=
      ⟨hre, hfe, rfl, hye, hcse, hrdie, hrsie, fun i hi => by change se.mem _ = _; rw [hme]; exact hpref i hi,
       fun a ha => by change se.mem a = _; rw [hme]; exact hout a ha⟩
    rcases ih (done + 1) (idx + kd + 2 + 1) { se with rip := 0x400120#64 } (by omega) hin_n with ⟨st_ih, hih⟩
    refine ⟨kd + (2 + (1 + st_ih)), ?_⟩
    dsimp only at hih ⊢
    rw [runFrom_add, hrun_d, runFrom_add, hseq_l, runFrom_add, hs_jne]
    exact hih

theorem prove_c_ascii_tolower_generic (img : X64ObjImage) (hbase : img.codeBase = 0x400000#64)
    (htest  : decodeX64 (fetchWindow16 (objCodeMap img) 0x400100#64) = .ok (.aluRmReg .s64 .test (.reg .rsi) .rsi) 3)
    (hje    : decodeX64 (fetchWindow16 (objCodeMap img) 0x400103#64) = .ok (.jccRel .e 0x34#64) 2)
    (hpre   : decodeSeqAt (objCodeMap img) 4 0x400105#64 = some asciiPreSeq)
    (hhead  : decodeSeqAt (objCodeMap img) 3 0x400120#64 = some asciiHeadSeq)
    (hja    : decodeX64 (fetchWindow16 (objCodeMap img) 0x400129#64) = .ok (.jccRel .a 0x05#64) 2)
    (hstore : decodeSeqAt (objCodeMap img) 2 0x40012b#64 = some asciiStoreSeq)
    (hlatch : decodeSeqAt (objCodeMap img) 2 0x400130#64 = some asciiLatchSeq)
    (hjne   : decodeX64 (fetchWindow16 (objCodeMap img) 0x400137#64) = .ok (.jccRel .ne 0xffffffffffffffe7#64) 2)
    (hret   : decodeX64 (fetchWindow16 (objCodeMap img) 0x400139#64) = .ok .ret64 1) :
    CObjectMatchesRustContract img 0x100#64 (AsciiTolowerPre 0) (AsciiTolowerContractPost 0) := by
  intro s0 nd hrun hnf hrip ⟨hnw, _⟩
  rw [hbase] at hrip
  have hrip' : s0.rip = 0x400100#64 := hrip
  let cmap := objCodeMap img
  let s1 : X64State :=
    { s0 with
      rip := 0x400103#64,
      flags := (evalAluN (by decide) .test (s0.regs .rsi) (s0.regs .rsi) s0.flags (nd 0).flags).2 }
  have hs1 : runFrom cmap 1 0 nd s0 = s1 := by
    rw [runFrom_succ, runFrom_zero, step_at_concrete htest _ s0 hrun hnf hrip', exec_aluRmReg_s64_test]; rfl
  cases hlen : (s0.regs .rsi).toNat with
  | zero =>
    refine ⟨1 + (1 + 1), ?_⟩
    dsimp only
    rw [runX64_eq_runFrom, runFrom_add, hs1, runFrom_add]
    have hzf1 : s1.flags.zf = true := by dsimp only [s1]; rw [test_flags_zf, test64_self_zero_eq, hlen]; rfl
    have hs2 : runFrom cmap 1 1 nd s1 = { s1 with rip := 0x400139#64 } := by
      rw [runFrom_succ, runFrom_zero, step_at_concrete hje _ s1 hrun hnf rfl,
          exec_jcc_taken (evalCond_e_of_zf_true hzf1)]; rfl
    rw [hs2]
    have hs3 : runFrom cmap 1 2 nd { s1 with rip := 0x400139#64 } =
        { s1 with rip := 0x400139#64, halted := true } := by
      rw [runFrom_succ, runFrom_zero, step_at_concrete hret _ { s1 with rip := 0x400139#64 } hrun hnf rfl, exec_ret]
    rw [hs3]
    refine ⟨rfl, hnf, ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩, upperClean_of_ymms_eq rfl, ?_⟩
    unfold AsciiTolowerContractPost RustAsciiTolowerPost; rw [hlen]
    exact ⟨fun i hi => absurd hi (by omega), fun _ _ _ => rfl⟩
  | succ rem =>
    have hzf1 : s1.flags.zf = false := by dsimp only [s1]; rw [test_flags_zf, test64_self_zero_eq, hlen]; rfl
    let s2 : X64State := { s1 with rip := 0x400105#64 }
    have hs2 : runFrom cmap 1 1 nd s1 = s2 := by
      rw [runFrom_succ, runFrom_zero, step_at_concrete hje _ s1 hrun hnf rfl,
          exec_jcc_fall (evalCond_e_of_zf_false hzf1)]; rfl
    rcases runFrom_of_decodeSeqAt hpre 2 nd s2 hrun hnf rfl with ⟨hseq_p, _, _⟩
    let sp : X64State :=
      { s2 with
        rip := 0x400120#64,
        regs := regUpd s0.regs .rsi (s0.regs .rsi + s0.regs .rdi),
        flags := (evalAluN (by decide) .add (s0.regs .rsi) (s0.regs .rdi) s2.flags (nd 2).flags).2 }
    have hpre_eq : execInstrSeq 4 asciiPreSeq 2 nd s2 = sp := by
      dsimp only [asciiPreSeq, sp]
      rw [execInstrSeq_succ_cons, exec_aluRmReg_s64_add,
          execInstrSeq_succ_cons, exec_nop,
          execInstrSeq_succ_cons, exec_nop,
          execInstrSeq_succ_cons, exec_nop, execInstrSeq_zero]
    have hrsi_eq : s0.regs .rsi = BitVec.ofNat 64 (rem + 1) := by
      apply BitVec.eq_of_toNat_eq
      rw [hlen, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by rw [← hlen]; exact (s0.regs .rsi).isLt)]
    have hnw' : NoWrapSlice (s0.regs .rdi) (rem + 1) := by rwa [← hlen]
    have hcs_p : SysVCalleeSavedPreserved s0 sp := by
      dsimp only [SysVCalleeSavedPreserved, sp]
      apply cs_step_caller; · decide
      exact ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩
    have hin0 : AsciiInv s0 (s0.regs .rdi) (rem + 1) 0 sp := by
      refine ⟨hrun, hnf, rfl, rfl, hcs_p, ?_, ?_, fun i hi => absurd hi (by omega), fun _ _ => rfl⟩
      · dsimp only [sp]; rw [regUpd_ne _ (by decide : Reg.rdi ≠ .rsi), BitVec.add_zero]
      · dsimp only [sp]; rw [regUpd_eq, hrsi_eq, BitVec.add_comm]
    rcases ascii_loop_ind hhead hja hstore hlatch hjne hret s0 (s0.regs .rdi) (rem + 1) hnw' nd
        rem 0 6 sp (by omega) hin0 with ⟨st_l, hl⟩
    refine ⟨1 + (1 + (4 + st_l)), ?_⟩
    dsimp only at hl ⊢
    rw [runX64_eq_runFrom, runFrom_add, hs1, runFrom_add, hs2, runFrom_add, hseq_p, hpre_eq]
    rcases hl with ⟨hh, hnf', hcs', hym', hpost⟩
    refine ⟨hh, hnf', hcs', upperClean_of_ymms_eq hym', ?_⟩
    unfold AsciiTolowerContractPost; rw [hlen]; exact hpost

theorem prove_c_ascii_tolower_o2 :
    CObjectMatchesRustContract cFfiKernelsO2Obj 0x100#64 (AsciiTolowerPre 0) (AsciiTolowerContractPost 0) :=
  prove_c_ascii_tolower_generic cFfiKernelsO2Obj rfl
    (decodeAt_of_check rfl) (decodeAt_of_check rfl)
    (decodeSeqAt_of_check rfl rfl) (decodeSeqAt_of_check rfl rfl)
    (decodeAt_of_check rfl) (decodeSeqAt_of_check rfl rfl) (decodeSeqAt_of_check rfl rfl)
    (decodeAt_of_check rfl) (decodeAt_of_check rfl)

theorem prove_c_ascii_tolower_o3 :
    CObjectMatchesRustContract cFfiKernelsO3Avx2Obj 0x100#64 (AsciiTolowerPre 0) (AsciiTolowerContractPost 0) :=
  prove_c_ascii_tolower_generic cFfiKernelsO3Avx2Obj rfl
    (decodeAt_of_check rfl) (decodeAt_of_check rfl)
    (decodeSeqAt_of_check rfl rfl) (decodeSeqAt_of_check rfl rfl)
    (decodeAt_of_check rfl) (decodeSeqAt_of_check rfl rfl) (decodeSeqAt_of_check rfl rfl)
    (decodeAt_of_check rfl) (decodeAt_of_check rfl)

/-! ## 2. `c_xor_stream` (`-O2`, `0x230`: Indexed Streaming XOR + Disjoint Framing) -/

def xorO2EntrySeq : List (X64Instr × BitVec 64) :=
  [ (.movStore .s64 (.reg .r8) .rsi, 0x400233#64),
    (.movStore .s64 (.reg .rsi) .rdx, 0x400236#64),
    (.aluRmReg .s64 .test (.reg .rdx) .rdx, 0x400239#64) ]

def xorO2PreSeq : List (X64Instr × BitVec 64) :=
  [ (.aluRmReg .s32 .xor (.reg .rax) .rax, 0x40023d#64),
    (.nop, 0x400240#64) ]

def xorO2LoopSeq : List (X64Instr × BitVec 64) :=
  [ (.movzx8 .s32 .rdx (.mem8 { base := some .r8, index := some (.rax, 0) }), 0x400245#64),
    (.aluRmReg .s32 .xor (.reg .rdx) .rcx, 0x400247#64),
    (.mov8Store (.mem8 { base := some .rdi, index := some (.rax, 0) }) (.lo8 .rdx), 0x40024a#64),
    (.aluImm .s64 .add (.reg .rax) 1#64, 0x40024e#64),
    (.aluRmReg .s64 .cmp (.reg .rsi) .rax, 0x400251#64) ]

private theorem xor8_of_zext32_xor (b : BitVec 8) (rcx : BitVec 64) :
    BitVec.extractLsb' 0 8
      ((BitVec.extractLsb' 0 32 (b.zeroExtend 64) ^^^ BitVec.extractLsb' 0 32 rcx).zeroExtend 64) =
      b ^^^ BitVec.extractLsb' 0 8 rcx := by
  apply BitVec.eq_of_getLsbD_eq
  intro i hi
  unfold BitVec.zeroExtend
  simp [hi, show i < 32 by omega, show i < 64 by omega]

structure XorO2Inv (s0 : X64State) (dst src : BitVec 64) (len done : Nat) (st : X64State) : Prop where
  run    : st.halted = false
  nf     : st.fault = false
  rip    : st.rip = 0x400240#64
  ymms   : st.ymms = s0.ymms
  cs     : SysVCalleeSavedPreserved s0 st
  rdi    : st.regs .rdi = dst
  r8     : st.regs .r8 = src
  rsi    : st.regs .rsi = BitVec.ofNat 64 len
  rcx    : st.regs .rcx = s0.regs .rcx
  rax    : st.regs .rax = BitVec.ofNat 64 done
  prefixEq : ∀ i : Nat, i < done →
    st.mem (dst + BitVec.ofNat 64 i) = s0.mem (src + BitVec.ofNat 64 i) ^^^ BitVec.extractLsb' 0 8 (s0.regs .rcx)
  outsideEq : ∀ addr : BitVec 64, ¬ InSliceRange addr dst done → st.mem addr = s0.mem addr

theorem xor_o2_body_step {s0 : X64State} {dst src : BitVec 64} {len done : Nat} {idx : Nat}
    {nd : Nat → UndefChoice} {st : X64State}
    (hnwd : NoWrapSlice dst len) (hnws : NoWrapSlice src len)
    (hdisj : DisjointSlices dst len src len) (hd : done < len)
    (hin : XorO2Inv s0 dst src len done st) :
    let sm := execInstrSeq 5 xorO2LoopSeq idx nd st
    sm.halted = false ∧ sm.fault = false ∧ sm.rip = 0x400251#64 ∧
    sm.ymms = s0.ymms ∧ SysVCalleeSavedPreserved s0 sm ∧
    sm.regs .rdi = dst ∧ sm.regs .r8 = src ∧
    sm.regs .rsi = BitVec.ofNat 64 len ∧ sm.regs .rcx = s0.regs .rcx ∧
    sm.regs .rax = BitVec.ofNat 64 (done + 1) ∧
    sm.flags.zf = (BitVec.ofNat 64 len - BitVec.ofNat 64 (done + 1) == 0#64) ∧
    (∀ i : Nat, i < done + 1 →
      sm.mem (dst + BitVec.ofNat 64 i) = s0.mem (src + BitVec.ofNat 64 i) ^^^ BitVec.extractLsb' 0 8 (s0.regs .rcx)) ∧
    (∀ addr : BitVec 64, ¬ InSliceRange addr dst (done + 1) → sm.mem addr = s0.mem addr) := by
  have hsrc_mem : st.mem (src + BitVec.ofNat 64 done) = s0.mem (src + BitVec.ofNat 64 done) :=
    hin.outsideEq _ (not_in_dst_of_disjoint hnwd hnws hdisj (by omega) hd)
  dsimp only [xorO2LoopSeq]
  rw [execInstrSeq_succ_cons, exec_movzx8_s32_mem, evalByteAddr_base_idx0,
      execInstrSeq_succ_cons, exec_aluRmReg_s32_xor,
      execInstrSeq_succ_cons, exec_mov8Store_mem_lo8, evalByteAddr_base_idx0,
      execInstrSeq_succ_cons, exec_aluImm_s64_add,
      execInstrSeq_succ_cons, exec_aluRmReg_s64_cmp, execInstrSeq_zero]
  have hadd1 : BitVec.ofNat 64 done + 1#64 = BitVec.ofNat 64 (done + 1) := by
    change BitVec.ofNat 64 done + BitVec.ofNat 64 1 = BitVec.ofNat 64 (done + 1)
    rw [bv64_ofNat_add]
  refine ⟨hin.run, hin.nf, rfl, hin.ymms, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · dsimp only [SysVCalleeSavedPreserved]
    repeat (apply cs_step_caller; · decide)
    exact hin.cs
  · simp only [regUpd_ne _ (by decide : Reg.rdi ≠ .rax), regUpd_ne _ (by decide : Reg.rdi ≠ .rdx), hin.rdi]
  · simp only [regUpd_ne _ (by decide : Reg.r8 ≠ .rax), regUpd_ne _ (by decide : Reg.r8 ≠ .rdx), hin.r8]
  · simp only [regUpd_ne _ (by decide : Reg.rsi ≠ .rax), regUpd_ne _ (by decide : Reg.rsi ≠ .rdx), hin.rsi]
  · simp only [regUpd_ne _ (by decide : Reg.rcx ≠ .rax), regUpd_ne _ (by decide : Reg.rcx ≠ .rdx), hin.rcx]
  · simp only [regUpd_eq, regUpd_ne _ (by decide : Reg.rax ≠ .rdx), hin.rax, hadd1]
  · rw [cmp_flags_zf]
    simp only [regUpd_eq, regUpd_ne _ (by decide : Reg.rsi ≠ .rax), regUpd_ne _ (by decide : Reg.rsi ≠ .rdx),
               regUpd_ne _ (by decide : Reg.rax ≠ .rdx), hin.rsi, hin.rax, hadd1]
  · intro i hi
    simp only [regUpd_eq, regUpd_ne _ (by decide : Reg.rdi ≠ .rdx), regUpd_ne _ (by decide : Reg.rax ≠ .rdx),
               regUpd_ne _ (by decide : Reg.rcx ≠ .rdx), hin.rdi, hin.r8, hin.rax, hin.rcx, hsrc_mem, xor8_of_zext32_xor]
    by_cases hcur : i = done
    · subst hcur; exact memUpd_eq _ _ _
    · have hilt : i < done := by omega
      rw [memUpd_ne _ _ (addr_ne_prefix hnwd hilt hd)]
      exact hin.prefixEq i hilt
  · intro addr hout
    simp only [regUpd_eq, regUpd_ne _ (by decide : Reg.rdi ≠ .rdx), regUpd_ne _ (by decide : Reg.rax ≠ .rdx),
               regUpd_ne _ (by decide : Reg.rcx ≠ .rdx), hin.rdi, hin.r8, hin.rax, hin.rcx, hsrc_mem]
    rw [memUpd_ne _ _ (addr_ne_outside hnwd hd hout)]
    exact hin.outsideEq addr (not_in_shorter_prefix hout)

theorem xor_o2_loop_ind {cmap : CodeMap}
    (hbody : decodeSeqAt cmap 5 0x400240#64 = some xorO2LoopSeq)
    (hjne  : decodeX64 (fetchWindow16 cmap 0x400251#64) = .ok (.jccRel .ne 0xffffffffffffffed#64) 2)
    (hret  : decodeX64 (fetchWindow16 cmap 0x400253#64) = .ok .ret64 1)
    (s0 : X64State) (dst src : BitVec 64) (len : Nat)
    (hnwd : NoWrapSlice dst len) (hnws : NoWrapSlice src len)
    (hdisj : DisjointSlices dst len src len) (nd : Nat → UndefChoice) :
    ∀ (rem done idx : Nat) (st : X64State),
      done + (rem + 1) = len →
      XorO2Inv s0 dst src len done st →
      ∃ steps : Nat,
        let sf := runFrom cmap steps idx nd st
        sf.halted = true ∧ sf.fault = false ∧
        SysVCalleeSavedPreserved s0 sf ∧ sf.ymms = s0.ymms ∧
        RustXorStreamPost s0.mem sf.mem dst src len (BitVec.extractLsb' 0 8 (s0.regs .rcx)) (s0.regs .rsp) 0 := by
  intro rem
  induction rem with
  | zero =>
    intro done idx st hsum hin
    have hd : done < len := by omega
    rcases runFrom_of_decodeSeqAt hbody idx nd st hin.run hin.nf hin.rip with ⟨hseq, _, _⟩
    rcases xor_o2_body_step hnwd hnws hdisj hd hin with
      ⟨hr1, hf1, hrip1, hy1, hcs1, _, _, _, _, _, hzf1, hpref, hout⟩
    generalize execInstrSeq 5 xorO2LoopSeq idx nd st = sm at hseq hr1 hf1 hrip1 hy1 hcs1 hzf1 hpref hout
    have heq : done + 1 = len := by omega
    have hzf_t : sm.flags.zf = true := by rw [hzf1, heq]; exact cmp_sub_self_zero _
    have hs_jne : runFrom cmap 1 (idx + 5) nd sm = { sm with rip := 0x400253#64 } := by
      rw [runFrom_succ, runFrom_zero, step_at_concrete hjne _ sm hr1 hf1 hrip1,
          exec_jcc_fall (evalCond_ne_of_zf_true hzf_t)]; rfl
    have hs_ret : runFrom cmap 1 (idx + 5 + 1) nd { sm with rip := 0x400253#64 } =
        { sm with rip := 0x400253#64, halted := true } := by
      rw [runFrom_succ, runFrom_zero, step_at_concrete hret _ { sm with rip := 0x400253#64 } hr1 hf1 rfl, exec_ret]
    refine ⟨5 + (1 + 1), ?_⟩
    dsimp only
    rw [runFrom_add, hseq, runFrom_add, hs_jne, hs_ret]
    exact ⟨rfl, hf1, hcs1, hy1, fun i hi => hpref i (by omega), fun a ha _ => hout a (by rwa [heq])⟩
  | succ k ih =>
    intro done idx st hsum hin
    have hd : done < len := by omega
    rcases runFrom_of_decodeSeqAt hbody idx nd st hin.run hin.nf hin.rip with ⟨hseq, _, _⟩
    rcases xor_o2_body_step hnwd hnws hdisj hd hin with
      ⟨hr1, hf1, hrip1, hy1, hcs1, hrdi1, hr81, hrsi1, hrcx1, hrax1, hzf1, hpref, hout⟩
    generalize execInstrSeq 5 xorO2LoopSeq idx nd st = sm at hseq hr1 hf1 hrip1 hy1 hcs1 hrdi1 hr81 hrsi1 hrcx1 hrax1 hzf1 hpref hout
    have hlen_lt : len < 2 ^ 64 := by unfold NoWrapSlice at hnwd; omega
    have hne : BitVec.ofNat 64 len ≠ BitVec.ofNat 64 (done + 1) := by
      intro heq
      have ht := congrArg BitVec.toNat heq
      rw [BitVec.toNat_ofNat, BitVec.toNat_ofNat,
          Nat.mod_eq_of_lt hlen_lt, Nat.mod_eq_of_lt (by omega)] at ht
      omega
    have hzf_f : sm.flags.zf = false := by rw [hzf1]; exact cmp_sub_zero_false_of_ne hne
    have hs_jne : runFrom cmap 1 (idx + 5) nd sm = { sm with rip := 0x400240#64 } := by
      rw [runFrom_succ, runFrom_zero, step_at_concrete hjne _ sm hr1 hf1 hrip1,
          exec_jcc_taken (evalCond_ne_of_zf_false hzf_f)]; rfl
    have hin_n : XorO2Inv s0 dst src len (done + 1) { sm with rip := 0x400240#64 } :=
      ⟨hr1, hf1, rfl, hy1, hcs1, hrdi1, hr81, hrsi1, hrcx1, hrax1, hpref, hout⟩
    rcases ih (done + 1) (idx + 5 + 1) { sm with rip := 0x400240#64 } (by omega) hin_n with ⟨st_ih, hih⟩
    refine ⟨5 + (1 + st_ih), ?_⟩
    dsimp only at hih ⊢
    rw [runFrom_add, hseq, runFrom_add, hs_jne]
    exact hih

theorem prove_c_xor_stream_o2 :
    CObjectMatchesRustContract cFfiKernelsO2Obj 0x230#64 (XorStreamPre 0) (XorStreamContractPost 0) := by
  have hentry : decodeSeqAt (objCodeMap cFfiKernelsO2Obj) 3 0x400230#64 = some xorO2EntrySeq :=
    decodeSeqAt_of_check rfl rfl
  have hje    : decodeX64 (fetchWindow16 (objCodeMap cFfiKernelsO2Obj) 0x400239#64) = .ok (.jccRel .e 0x18#64) 2 :=
    decodeAt_of_check rfl
  have hpre   : decodeSeqAt (objCodeMap cFfiKernelsO2Obj) 2 0x40023b#64 = some xorO2PreSeq :=
    decodeSeqAt_of_check rfl rfl
  have hbody  : decodeSeqAt (objCodeMap cFfiKernelsO2Obj) 5 0x400240#64 = some xorO2LoopSeq :=
    decodeSeqAt_of_check rfl rfl
  have hjne   : decodeX64 (fetchWindow16 (objCodeMap cFfiKernelsO2Obj) 0x400251#64) = .ok (.jccRel .ne 0xffffffffffffffed#64) 2 :=
    decodeAt_of_check rfl
  have hret   : decodeX64 (fetchWindow16 (objCodeMap cFfiKernelsO2Obj) 0x400253#64) = .ok .ret64 1 :=
    decodeAt_of_check rfl
  intro s0 nd hrun hnf hrip ⟨hnwd, hnws, hdisj, _, _⟩
  have hrip' : s0.rip = 0x400230#64 := hrip
  let cmap := objCodeMap cFfiKernelsO2Obj
  rcases runFrom_of_decodeSeqAt hentry 0 nd s0 hrun hnf hrip' with ⟨hseq_e, _, _⟩
  let se : X64State :=
    { s0 with
      rip := 0x400239#64,
      regs := regUpd (regUpd s0.regs .r8 (s0.regs .rsi)) .rsi (s0.regs .rdx),
      flags := (evalAluN (by decide) .test (s0.regs .rdx) (s0.regs .rdx) s0.flags (nd 2).flags).2 }
  have hent_eq : execInstrSeq 3 xorO2EntrySeq 0 nd s0 = se := by
    dsimp only [xorO2EntrySeq, se]
    rw [execInstrSeq_succ_cons, exec_movStore_s64_reg,
        execInstrSeq_succ_cons, exec_movStore_s64_reg,
        execInstrSeq_succ_cons, exec_aluRmReg_s64_test, execInstrSeq_zero]
    simp only [regUpd_ne _ (by decide : Reg.rdx ≠ .r8), regUpd_ne _ (by decide : Reg.rdx ≠ .rsi)]
  have hcs_e : SysVCalleeSavedPreserved s0 se := by
    dsimp only [SysVCalleeSavedPreserved, se]
    repeat (apply cs_step_caller; · decide)
    exact ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩
  cases hlen : (s0.regs .rdx).toNat with
  | zero =>
    refine ⟨3 + (1 + 1), ?_⟩
    dsimp only
    rw [runX64_eq_runFrom, runFrom_add, hseq_e, hent_eq, runFrom_add]
    have hzf_e : se.flags.zf = true := by dsimp only [se]; rw [test_flags_zf, test64_self_zero_eq, hlen]; rfl
    have hs_je : runFrom cmap 1 3 nd se = { se with rip := 0x400253#64 } := by
      rw [runFrom_succ, runFrom_zero, step_at_concrete hje _ se hrun hnf rfl,
          exec_jcc_taken (evalCond_e_of_zf_true hzf_e)]; rfl
    rw [hs_je]
    have hs_ret : runFrom cmap 1 4 nd { se with rip := 0x400253#64 } =
        { se with rip := 0x400253#64, halted := true } := by
      rw [runFrom_succ, runFrom_zero, step_at_concrete hret _ { se with rip := 0x400253#64 } hrun hnf rfl, exec_ret]
    rw [hs_ret]
    refine ⟨rfl, hnf, hcs_e, upperClean_of_ymms_eq rfl, ?_⟩
    unfold XorStreamContractPost RustXorStreamPost; rw [hlen]
    exact ⟨fun i hi => absurd hi (by omega), fun _ _ _ => rfl⟩
  | succ rem =>
    have hzf_e : se.flags.zf = false := by dsimp only [se]; rw [test_flags_zf, test64_self_zero_eq, hlen]; rfl
    let s2 : X64State := { se with rip := 0x40023b#64 }
    have hs_je : runFrom cmap 1 3 nd se = s2 := by
      rw [runFrom_succ, runFrom_zero, step_at_concrete hje _ se hrun hnf rfl,
          exec_jcc_fall (evalCond_e_of_zf_false hzf_e)]; rfl
    rcases runFrom_of_decodeSeqAt hpre 4 nd s2 hrun hnf rfl with ⟨hseq_p, _, _⟩
    let sp : X64State :=
      { s2 with
        rip := 0x400240#64,
        regs := regUpd s2.regs .rax 0#64,
        flags := (evalAluN (by decide) .xor (BitVec.extractLsb' 0 32 (s2.regs .rax))
          (BitVec.extractLsb' 0 32 (s2.regs .rax)) s2.flags (nd 4).flags).2 }
    have hpre_eq : execInstrSeq 2 xorO2PreSeq 4 nd s2 = sp := by
      dsimp only [xorO2PreSeq, sp]
      rw [execInstrSeq_succ_cons, exec_aluRmReg_s32_xor_self,
          execInstrSeq_succ_cons, exec_nop, execInstrSeq_zero]
    have hrdx_eq : s0.regs .rdx = BitVec.ofNat 64 (rem + 1) := by
      apply BitVec.eq_of_toNat_eq
      rw [hlen, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by rw [← hlen]; exact (s0.regs .rdx).isLt)]
    have hnwd' : NoWrapSlice (s0.regs .rdi) (rem + 1) := by rwa [← hlen]
    have hnws' : NoWrapSlice (s0.regs .rsi) (rem + 1) := by rwa [← hlen]
    have hdisj' : DisjointSlices (s0.regs .rdi) (rem + 1) (s0.regs .rsi) (rem + 1) := by rwa [← hlen]
    have hcs_p : SysVCalleeSavedPreserved s0 sp := by
      dsimp only [SysVCalleeSavedPreserved, sp]
      apply cs_step_caller; · decide
      exact hcs_e
    have hin0 : XorO2Inv s0 (s0.regs .rdi) (s0.regs .rsi) (rem + 1) 0 sp := by
      refine ⟨hrun, hnf, rfl, rfl, hcs_p, ?_, ?_, ?_, ?_, ?_, fun i hi => absurd hi (by omega), fun _ _ => rfl⟩
      · dsimp only [sp, s2, se]; simp [regUpd_ne _ (by decide : Reg.rdi ≠ .rax), regUpd_ne _ (by decide : Reg.rdi ≠ .rsi), regUpd_ne _ (by decide : Reg.rdi ≠ .r8)]
      · dsimp only [sp, s2, se]; simp [regUpd_ne _ (by decide : Reg.r8 ≠ .rax), regUpd_ne _ (by decide : Reg.r8 ≠ .rsi), regUpd_eq]
      · dsimp only [sp, s2, se]; simp [regUpd_ne _ (by decide : Reg.rsi ≠ .rax), regUpd_eq, hrdx_eq]
      · dsimp only [sp, s2, se]; simp [regUpd_ne _ (by decide : Reg.rcx ≠ .rax), regUpd_ne _ (by decide : Reg.rcx ≠ .rsi), regUpd_ne _ (by decide : Reg.rcx ≠ .r8)]
      · dsimp only [sp]; exact regUpd_eq _ _ _
    rcases xor_o2_loop_ind hbody hjne hret s0 (s0.regs .rdi) (s0.regs .rsi) (rem + 1)
        hnwd' hnws' hdisj' nd rem 0 6 sp (by omega) hin0 with ⟨st_l, hl⟩
    refine ⟨3 + (1 + (2 + st_l)), ?_⟩
    dsimp only at hl ⊢
    rw [runX64_eq_runFrom, runFrom_add, hseq_e, hent_eq, runFrom_add, hs_je, runFrom_add, hseq_p, hpre_eq]
    rcases hl with ⟨hh, hnf', hcs', hym', hpost⟩
    refine ⟨hh, hnf', hcs', upperClean_of_ymms_eq hym', ?_⟩
    unfold XorStreamContractPost; rw [hlen]; exact hpost

end UntrustedCObjMutLoops
