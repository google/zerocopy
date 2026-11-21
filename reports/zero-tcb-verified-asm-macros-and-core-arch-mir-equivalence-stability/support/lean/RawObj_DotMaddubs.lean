-- Copyright 2026 The Fuchsia Authors
--
-- Licensed under a BSD-style license <LICENSE-BSD>, Apache License, Version 2.0
-- <LICENSE-APACHE or https://www.apache.org/licenses/LICENSE-2.0>, or the MIT
-- license <LICENSE-MIT or https://opensource.org/licenses/MIT>, at your option.
-- This file may not be copied, modified, or distributed except according to
-- those terms.

prelude
import Init.Core
import Init.Data.Nat.Basic
import Init.Omega
import AsmMirBase
import IsaLemmas

/-!
Regime (a): Unassisted direct `.o` machine-byte proof for `dot_maddubs_unroll2_asm`
(125 bytes, 31 instructions, 2x-unrolled loop + `vzeroupper`) without `UntrustedHints`.
-/

namespace LockedObligations

open AsmMirBase IsaLemmas

private def RawDotInv (s0 : X86State) (blocks k : Nat) (st : X86State) : Prop :=
  st.rip = 28 ∧
  st.halted = false ∧
  st.fault = false ∧
  st.gpr .rdi = s0.gpr .rdi ∧
  st.gpr .rsi = s0.gpr .rsi ∧
  st.gpr .rsp = s0.gpr .rsp ∧
  st.gpr .rdx = 64 * blocks ∧
  st.gpr .rcx = 64 * k ∧
  st.mem64 = s0.mem64 ∧
  st.mem8 = s0.mem8 ∧
  st.ymm .ymm2 = ymmOnes16 ∧
  (ymmSum8Mod32 (st.ymm .ymm0) + ymmSum8Mod32 (st.ymm .ymm1)) % M32 =
    dotBlocks64Spec s0.mem8 (s0.gpr .rdi) (s0.gpr .rsi) k

theorem verify_dot_maddubs_obj (s : X86State)
    (hrip : s.rip = 0) (hnh : s.halted = false) (hnf : s.fault = false)
    (hblk : 64 * (s.gpr .rdx % W64) < W64) :
    let blocks := s.gpr .rdx % W64
    let sf := run dotObjBytes (18 + 13 * blocks) s
    sf.halted = true ∧
    sf.fault = false ∧
    sf.ymmDirty = false ∧
    sf.gpr .rsp = s.gpr .rsp ∧
    sf.mem64 = s.mem64 ∧
    sf.mem8 = s.mem8 ∧
    sf.gpr .rax = dotBlocks64Spec s.mem8 (s.gpr .rdi) (s.gpr .rsi) blocks := by
  -- 10-step epilogue at byte offset 85 (`vpaddd` .. `vzeroupper` .. `ret`)
  have h_epilog : ∀ (se : X86State) (target : Nat),
      se.rip = 85 → se.halted = false → se.fault = false →
      se.gpr .rsp = s.gpr .rsp → se.mem64 = s.mem64 → se.mem8 = s.mem8 →
      (ymmSum8Mod32 (se.ymm .ymm0) + ymmSum8Mod32 (se.ymm .ymm1)) % M32 = target →
      let sf := run dotObjBytes 10 se
      sf.halted = true ∧ sf.fault = false ∧ sf.ymmDirty = false ∧
      sf.gpr .rsp = s.gpr .rsp ∧ sf.mem64 = s.mem64 ∧ sf.mem8 = s.mem8 ∧
      sf.gpr .rax = target := by
    intro se target herip henh henf hersp hem64 hem8 hesum
    let v256 := evalVpaddd256 (se.ymm .ymm0) (se.ymm .ymm1)
    let vhi  := evalVextracti128Hi v256
    let v128 := evalVpaddd128 v256 vhi
    let vs1  := evalVpshufd128 v128 0x4e
    let v64  := evalVpaddd128 v128 vs1
    let vs2  := evalVpshufd128 v64 0xb1
    let v32  := evalVpaddd128 v64 vs2
    let y1 := ymmUpd se.ymm .ymm0 v256
    let e1 : X86State := { se with rip := 89, ymmDirty := true, ymm := y1 }
    have he1 : step dotObjBytes se = e1 := by
      rw [step_of_decode (s := se) (ins := .vpaddd256 .ymm0 .ymm0 .ymm1) (len := 4) henh henf (by rw [herip]; rfl)]
      dsimp [execInsn, e1, y1]; rw [herip]
    let y2 := ymmUpd y1 .ymm1 vhi
    let e2 : X86State := { e1 with rip := 95, ymm := y2 }
    have he2 : step dotObjBytes e1 = e2 := by
      rw [step_of_decode (s := e1) henh henf rfl]; dsimp [execInsn, e2, e1, y2, y1, ymmUpd]; rfl
    let y3 := ymmUpd y2 .ymm0 v128
    let e3 : X86State := { e2 with rip := 99, ymm := y3 }
    have he3 : step dotObjBytes e2 = e3 := by
      rw [step_of_decode (s := e2) henh henf rfl]; dsimp [execInsn, e3, e2, y3, y2, y1, ymmUpd]; rfl
    let y4 := ymmUpd y3 .ymm1 vs1
    let e4 : X86State := { e3 with rip := 104, ymm := y4 }
    have he4 : step dotObjBytes e3 = e4 := by
      rw [step_of_decode (s := e3) henh henf rfl]; dsimp [execInsn, e4, e3, y4, y3, ymmUpd]; rfl
    let y5 := ymmUpd y4 .ymm0 v64
    let e5 : X86State := { e4 with rip := 108, ymm := y5 }
    have he5 : step dotObjBytes e4 = e5 := by
      rw [step_of_decode (s := e4) henh henf rfl]; dsimp [execInsn, e5, e4, y5, y4, y3, ymmUpd]; rfl
    let y6 := ymmUpd y5 .ymm1 vs2
    let e6 : X86State := { e5 with rip := 113, ymm := y6 }
    have he6 : step dotObjBytes e5 = e6 := by
      rw [step_of_decode (s := e5) henh henf rfl]; dsimp [execInsn, e6, e5, y6, y5, ymmUpd]; rfl
    let y7 := ymmUpd y6 .ymm0 v32
    let e7 : X86State := { e6 with rip := 117, ymm := y7 }
    have he7 : step dotObjBytes e6 = e7 := by
      rw [step_of_decode (s := e6) henh henf rfl]; dsimp [execInsn, e7, e6, y7, y6, y5, ymmUpd]; rfl
    let e8 : X86State := { e7 with rip := 121, gpr := gprUpd se.gpr .rax (v32.d0 % M32) }
    have he8 : step dotObjBytes e7 = e8 := by
      rw [step_of_decode (s := e7) henh henf rfl]; dsimp [execInsn, e8, e7, e6, e5, e4, e3, e2, e1, y7, ymmUpd]; rfl
    let e9 : X86State := { e8 with rip := 124, ymmDirty := false, ymm := zeroUpperAll y7 }
    have he9 : step dotObjBytes e8 = e9 := by
      rw [step_of_decode (s := e8) henh henf rfl]; rfl
    let e10 : X86State := { e9 with halted := true }
    have he10 : step dotObjBytes e9 = e10 := by
      rw [step_of_decode (s := e9) henh henf rfl]; rfl
    have hrun10 : run dotObjBytes 10 se = e10 := by
      rw [run_succ, he1, run_succ, he2, run_succ, he3, run_succ, he4, run_succ, he5,
          run_succ, he6, run_succ, he7, run_succ, he8, run_succ, he9, run_succ, he10, run_zero]
    dsimp only; rw [hrun10]
    have hrax : e10.gpr .rax = target := by
      change v32.d0 % M32 = target
      have hred := horizontal_reduce_256 v256
      dsimp only at hred
      rw [hred, ymmSum8_vpaddd256, hesum]
    exact ⟨rfl, henf, rfl, hersp, hem64, hem8, hrax⟩
  -- Prologue steps at byte offsets 0, 4, 8, 11
  let q1 : X86State := { s with rip := 4, ymmDirty := true, ymm := ymmUpd s.ymm .ymm0 ymmZero }
  have hq1 : step dotObjBytes s = q1 := by
    rw [step_of_decode (s := s) (ins := .vpxorZero256 .ymm0) (len := 4) hnh hnf (by rw [hrip]; rfl)]
    dsimp [execInsn, q1]; rw [hrip]
  let q2 : X86State := { q1 with rip := 8, ymm := ymmUpd q1.ymm .ymm1 ymmZero }
  have hq2 : step dotObjBytes q1 = q2 := by rw [step_of_decode (s := q1) hnh hnf rfl]; rfl
  let q3 : X86State := { q2 with rip := 11, cf := false, of_ := false, zf := decide (s.gpr .rdx % W64 = 0) }
  have hq3 : step dotObjBytes q2 = q3 := by rw [step_of_decode (s := q2) hnh hnf rfl]; rfl
  let q4 : X86State := { q3 with rip := if q3.zf then 85 else 13, leak := s.leak ++ [.branch q3.zf 85] }
  have hq4 : step dotObjBytes q3 = q4 := by rw [step_of_decode (s := q3) hnh hnf rfl]; rfl
  have hrun4 : run dotObjBytes 4 s = q4 := by
    rw [run_succ, hq1, run_succ, hq2, run_succ, hq3, run_succ, hq4, run_zero]
  dsimp only
  cases hblocks : s.gpr .rdx % W64 with
  | zero =>
    have hzf : q3.zf = true := by dsimp [q3]; rw [hblocks]; rfl
    have hq4_rip : q4.rip = 85 := by dsimp [q4]; rw [hzf]; rfl
    have hep := h_epilog q4 0 hq4_rip hnh hnf rfl rfl rfl (by dsimp [q4, q3, q2, q1, ymmUpd]; rfl)
    dsimp only at hep
    have hsplit : (18 : Nat) = 4 + (10 + 4) := rfl
    rw [Nat.mul_zero, Nat.add_zero, hsplit, run_add dotObjBytes 4 (10 + 4) s, hrun4,
        run_add dotObjBytes 10 4 q4, run_halted dotObjBytes 4 hep.1]
    exact hep
  | succ m =>
    have hzf : q3.zf = false := by
      dsimp [q3]; rw [hblocks]; exact decide_eq_false (Nat.succ_ne_zero m)
    have hq4_rip : q4.rip = 13 := by dsimp [q4]; rw [hzf]; rfl
    let q5 : X86State := { q4 with rip := 17, ymmDirty := true, ymm := ymmUpd q4.ymm .ymm2 ymmAllOnes }
    have hq5 : step dotObjBytes q4 = q5 := by
      rw [step_of_decode (s := q4) (ins := .vpcmpeqdAll1 .ymm2) (len := 4) hnh hnf (by rw [hq4_rip]; rfl)]
      dsimp [execInsn, q5]; rw [hq4_rip]
    let q6 : X86State := { q5 with rip := 22, ymm := ymmUpd q5.ymm .ymm2 ymmOnes16 }
    have hq6 : step dotObjBytes q5 = q6 := by
      rw [step_of_decode (s := q5) (ins := .vpsrlwImm256 .ymm2 .ymm2 15) (len := 5) hnh hnf rfl]
      dsimp [execInsn, q6, q5, ymmUpd]; rfl
    rw [hblocks] at hblk
    let q7 : X86State := { q6 with rip := 26, gpr := gprUpd s.gpr .rdx (64 * (m + 1)) }
    have hq7 : step dotObjBytes q6 = q7 := by
      rw [step_of_decode (s := q6) (ins := .shlImm64 .rdx 6) (len := 4) hnh hnf rfl]
      dsimp [execInsn, q7, q6, q5, q4, q3, q2, q1]
      have heq : (s.gpr .rdx % W64 * 64) % W64 = 64 * (m + 1) := by
        rw [hblocks, Nat.mul_comm, Nat.mod_eq_of_lt hblk]
      rw [heq]
    let q8 : X86State := { q7 with rip := 28, cf := false, of_ := false, zf := true, gpr := gprUpd q7.gpr .rcx 0 }
    have hq8 : step dotObjBytes q7 = q8 := by rw [step_of_decode (s := q7) hnh hnf rfl]; rfl
    have hrun8 : run dotObjBytes 8 s = q8 := by
      have e8 : (8 : Nat) = 4 + 4 := rfl
      rw [e8, run_add dotObjBytes 4 4 s, hrun4, run_succ, hq5, run_succ, hq6, run_succ, hq7, run_succ, hq8, run_zero]
    have hinv0 : RawDotInv s (m + 1) 0 q8 := by
      refine ⟨rfl, hnh, hnf, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, ?_⟩
      dsimp [q8, q7, q6, q5, q4, q3, q2, q1, ymmUpd]; rfl
    -- 13-step loop body from byte offset 28 .. 83
    have h_iter : ∀ {k : Nat} {st : X86State},
        k < m + 1 → RawDotInv s (m + 1) k st →
        let st' := run dotObjBytes 13 st
        st'.halted = false ∧ st'.fault = false ∧
        st'.gpr .rdi = s.gpr .rdi ∧ st'.gpr .rsi = s.gpr .rsi ∧ st'.gpr .rsp = s.gpr .rsp ∧
        st'.gpr .rdx = 64 * (m + 1) ∧ st'.gpr .rcx = 64 * (k + 1) ∧
        st'.mem64 = s.mem64 ∧ st'.mem8 = s.mem8 ∧ st'.ymm .ymm2 = ymmOnes16 ∧
        (ymmSum8Mod32 (st'.ymm .ymm0) + ymmSum8Mod32 (st'.ymm .ymm1)) % M32 =
          dotBlocks64Spec s.mem8 (s.gpr .rdi) (s.gpr .rsi) (k + 1) ∧
        st'.rip = (if k + 1 < m + 1 then 28 else 85) := by
      intro k st hk ⟨hrip_k, hnh_k, hnf_k, hrdi_k, hrsi_k, hrsp_k, hrdx_k, hrcx_k, hm64_k, hm8_k, hymm2_k, hsum_k⟩
      let rdi := s.gpr .rdi
      let rsi := s.gpr .rsi
      let vu0 := loadYmm256 s.mem8 ((rdi + 64 * k) % W64)
      let vs0 := loadYmm256 s.mem8 ((rsi + 64 * k) % W64)
      let vp0 := evalVpmaddubsw vu0 vs0
      let vw0 := evalVpmaddwd vp0 ymmOnes16
      let acc0' := evalVpaddd256 (st.ymm .ymm0) vw0
      let vu1 := loadYmm256 s.mem8 ((rdi + (64 * k + 32)) % W64)
      let vs1 := loadYmm256 s.mem8 ((rsi + (64 * k + 32)) % W64)
      let vp1 := evalVpmaddubsw vu1 vs1
      let vw1 := evalVpmaddwd vp1 ymmOnes16
      let acc1' := evalVpaddd256 (st.ymm .ymm1) vw1

      let y_1 := ymmUpd st.ymm .ymm3 vu0
      let lk1 := st.leak ++ [.load256 ((rdi + 64 * k) % W64)]
      let b1 : X86State := { st with rip := 33, ymmDirty := true, ymm := y_1, leak := lk1 }
      have hb1 : step dotObjBytes st = b1 :=
        (step_of_decode (s := st) (ins := .vmovdquLd256 .ymm3 .rdi .rcx 0) (len := 5) hnh_k hnf_k (by rw [hrip_k]; rfl)).trans
          (exec_vmovdquLd256 (by rw [hrip_k]) (by rw [hrdi_k, hrcx_k, Nat.add_zero]) hm8_k)

      let y_2 := ymmUpd y_1 .ymm4 vs0
      let lk2 := lk1 ++ [.load256 ((rsi + 64 * k) % W64)]
      let b2 : X86State := { b1 with rip := 38, ymm := y_2, leak := lk2 }
      have hb2 : step dotObjBytes b1 = b2 :=
        (step_of_decode (s := b1) (ins := .vmovdquLd256 .ymm4 .rsi .rcx 0) (len := 5) hnh_k hnf_k rfl).trans
          (exec_vmovdquLd256 rfl
            (by change (st.gpr .rsi + st.gpr .rcx + 0) % W64 = _; rw [hrsi_k, hrcx_k, Nat.add_zero]) hm8_k)

      let y_3 := ymmUpd y_2 .ymm3 vp0
      let b3 : X86State := { b2 with rip := 43, ymm := y_3 }
      have hb3 : step dotObjBytes b2 = b3 := by
        rw [step_of_decode (s := b2) (ins := .vpmaddubsw .ymm3 .ymm3 .ymm4) (len := 5) hnh_k hnf_k rfl]
        dsimp [execInsn, b3, b2, y_3, y_2, y_1, ymmUpd]

      let y_4 := ymmUpd y_3 .ymm3 vw0
      let b4 : X86State := { b3 with rip := 47, ymm := y_4 }
      have hb4 : step dotObjBytes b3 = b4 := by
        rw [step_of_decode (s := b3) (ins := .vpmaddwd .ymm3 .ymm3 .ymm2) (len := 4) hnh_k hnf_k rfl]
        dsimp [execInsn, b4, b3, y_4, y_3, y_2, y_1, ymmUpd]; rw [hymm2_k]

      let y_5 := ymmUpd y_4 .ymm0 acc0'
      let b5 : X86State := { b4 with rip := 51, ymm := y_5 }
      have hb5 : step dotObjBytes b4 = b5 := by
        rw [step_of_decode (s := b4) (ins := .vpaddd256 .ymm0 .ymm0 .ymm3) (len := 4) hnh_k hnf_k rfl]
        dsimp [execInsn, b5, b4, y_5, y_4, y_3, y_2, y_1, ymmUpd]

      let y_6 := ymmUpd y_5 .ymm5 vu1
      let lk6 := lk2 ++ [.load256 ((rdi + (64 * k + 32)) % W64)]
      let b6 : X86State := { b5 with rip := 57, ymm := y_6, leak := lk6 }
      have hb6 : step dotObjBytes b5 = b6 :=
        (step_of_decode (s := b5) (ins := .vmovdquLd256 .ymm5 .rdi .rcx 32) (len := 6) hnh_k hnf_k rfl).trans
          (exec_vmovdquLd256 rfl
            (by change (st.gpr .rdi + st.gpr .rcx + 32) % W64 = _; rw [hrdi_k, hrcx_k, Nat.add_assoc]) hm8_k)

      let y_7 := ymmUpd y_6 .ymm6 vs1
      let lk7 := lk6 ++ [.load256 ((rsi + (64 * k + 32)) % W64)]
      let b7 : X86State := { b6 with rip := 63, ymm := y_7, leak := lk7 }
      have hb7 : step dotObjBytes b6 = b7 :=
        (step_of_decode (s := b6) (ins := .vmovdquLd256 .ymm6 .rsi .rcx 32) (len := 6) hnh_k hnf_k rfl).trans
          (exec_vmovdquLd256 rfl
            (by change (st.gpr .rsi + st.gpr .rcx + 32) % W64 = _; rw [hrsi_k, hrcx_k, Nat.add_assoc]) hm8_k)

      let y_8 := ymmUpd y_7 .ymm5 vp1
      let b8 : X86State := { b7 with rip := 68, ymm := y_8 }
      have hb8 : step dotObjBytes b7 = b8 := by
        rw [step_of_decode (s := b7) (ins := .vpmaddubsw .ymm5 .ymm5 .ymm6) (len := 5) hnh_k hnf_k rfl]
        dsimp [execInsn, b8, b7, y_8, y_7, y_6, ymmUpd]

      let y_9 := ymmUpd y_8 .ymm5 vw1
      let b9 : X86State := { b8 with rip := 72, ymm := y_9 }
      have hb9 : step dotObjBytes b8 = b9 := by
        rw [step_of_decode (s := b8) (ins := .vpmaddwd .ymm5 .ymm5 .ymm2) (len := 4) hnh_k hnf_k rfl]
        dsimp [execInsn, b9, b8, y_9, y_8, y_7, y_6, y_5, y_4, y_3, y_2, y_1, ymmUpd]; rw [hymm2_k]

      let y_10 := ymmUpd y_9 .ymm1 acc1'
      let b10 : X86State := { b9 with rip := 76, ymm := y_10 }
      have hb10 : step dotObjBytes b9 = b10 := by
        rw [step_of_decode (s := b9) (ins := .vpaddd256 .ymm1 .ymm1 .ymm5) (len := 4) hnh_k hnf_k rfl]
        dsimp [execInsn, b10, b9, y_10, y_9, y_8, y_7, y_6, y_5, y_4, y_3, y_2, y_1, ymmUpd]

      have hk64_lt : 64 * k < W64 := by omega
      have hk1_64_lt : 64 * (k + 1) < W64 := by omega
      let g_11 := gprUpd st.gpr .rcx (64 * (k + 1))
      let b11 : X86State := { b10 with rip := 80, cf := false, zf := decide (64 * (k + 1) = 0), gpr := g_11 }
      have hb11 : step dotObjBytes b10 = b11 :=
        (step_of_decode (s := b10) (ins := .addImm64 .rcx 64) (len := 4) hnh_k hnf_k rfl).trans
          (exec_addImm64 rfl
            (by change (st.gpr .rcx % W64) + 64 = 64 * (k + 1); rw [hrcx_k, Nat.mod_eq_of_lt hk64_lt]; omega)
            hk1_64_lt)

      let b12 : X86State := { b11 with rip := 83, cf := decide (64 * (k + 1) < 64 * (m + 1)),
                                       zf := decide (64 * (k + 1) = 64 * (m + 1)), of_ := false }
      have hb12 : step dotObjBytes b11 = b12 :=
        (step_of_decode (s := b11) (ins := .cmpReg64 .rcx .rdx) (len := 3) hnh_k hnf_k rfl).trans
          (exec_cmpReg64 rfl (by change (64 * (k + 1)) % W64 = 64 * (k + 1); exact Nat.mod_eq_of_lt hk1_64_lt)
            (by change st.gpr .rdx % W64 = 64 * (m + 1); rw [hrdx_k, Nat.mod_eq_of_lt hblk]))

      let taken := decide (64 * (k + 1) < 64 * (m + 1))
      let b13 : X86State := { b12 with rip := if taken then 28 else 85, leak := lk7 ++ [.branch taken 28] }
      have hb13 : step dotObjBytes b12 = b13 := by
        rw [step_of_decode (s := b12) hnh_k hnf_k rfl]; rfl

      have hrun13 : run dotObjBytes 13 st = b13 := by
        rw [run_succ, hb1, run_succ, hb2, run_succ, hb3, run_succ, hb4, run_succ, hb5,
            run_succ, hb6, run_succ, hb7, run_succ, hb8, run_succ, hb9, run_succ, hb10,
            run_succ, hb11, run_succ, hb12, run_succ, hb13, run_zero]
      dsimp only; rw [hrun13]
      have hsum_next : (ymmSum8Mod32 (b13.ymm .ymm0) + ymmSum8Mod32 (b13.ymm .ymm1)) % M32 =
          dotBlocks64Spec s.mem8 rdi rsi (k + 1) := by
        let x0 := ymmSum8Mod32 (st.ymm .ymm0)
        let x1 := ymmSum8Mod32 (st.ymm .ymm1)
        let w0 := ymmSum8Mod32 vw0
        let w1 := ymmSum8Mod32 vw1
        change (ymmSum8Mod32 acc0' + ymmSum8Mod32 acc1') % M32 = dotBlocks64Spec s.mem8 rdi rsi (k + 1)
        dsimp [acc0', acc1']
        rw [ymmSum8_vpaddd256, ymmSum8_vpaddd256, ← Nat.add_mod]
        unfold dotBlocks64Spec
        change (x0 + w0 + (x1 + w1)) % M32 = (dotBlocks64Spec s.mem8 rdi rsi k + w0 + w1) % M32
        have hsum_x : (x0 + x1) % M32 = dotBlocks64Spec s.mem8 rdi rsi k := hsum_k
        rw [← hsum_x, Nat.add_assoc ((x0 + x1) % M32) w0 w1, Nat.mod_add_mod]
        exact congrArg (· % M32) (by omega)
      have hrip_next : b13.rip = (if k + 1 < m + 1 then 28 else 85) := by
        change (if taken = true then 28 else 85) = (if k + 1 < m + 1 then 28 else 85)
        cases hlt : decide (k + 1 < m + 1) with
        | true =>
          have hklt := of_decide_eq_true hlt
          have hc : taken = true := decide_eq_true (by omega)
          simp only [hc, ↓reduceIte, hklt]
        | false =>
          have hknlt := of_decide_eq_false hlt
          have hc : taken = false := decide_eq_false (by omega)
          simp only [hc, Bool.false_eq_true, ↓reduceIte, hknlt]
      exact ⟨hnh_k, hnf_k, hrdi_k, hrsi_k, hrsp_k, hrdx_k, rfl, hm64_k, hm8_k, hymm2_k, hsum_next, hrip_next⟩
    have h_loop_m : ∀ (j : Nat), j ≤ m →
        RawDotInv s (m + 1) j (run dotObjBytes (13 * j) q8) := by
      intro j hj
      induction j with
      | zero => rw [Nat.mul_zero, run_zero]; exact hinv0
      | succ j ih =>
        have hprev := ih (Nat.le_of_succ_le hj)
        have hmul : 13 * (j + 1) = 13 * j + 13 := by omega
        rw [hmul, run_add dotObjBytes (13 * j) 13 q8]
        have hstep := h_iter (by omega : j < m + 1) hprev
        dsimp only at hstep
        have hj_lt : j + 1 < m + 1 := by omega
        have hrip_j : (run dotObjBytes 13 (run dotObjBytes (13 * j) q8)).rip = 28 := by
          rw [hstep.2.2.2.2.2.2.2.2.2.2.2]; simp [hj_lt]
        exact ⟨hrip_j, hstep.1, hstep.2.1, hstep.2.2.1, hstep.2.2.2.1, hstep.2.2.2.2.1,
               hstep.2.2.2.2.2.1, hstep.2.2.2.2.2.2.1, hstep.2.2.2.2.2.2.2.1,
               hstep.2.2.2.2.2.2.2.2.1, hstep.2.2.2.2.2.2.2.2.2.1, hstep.2.2.2.2.2.2.2.2.2.2.1⟩
    have hinv_m := h_loop_m m (Nat.le_refl m)
    have hlast := h_iter (Nat.lt_succ_self m) hinv_m
    dsimp only at hlast
    let s_exit := run dotObjBytes 13 (run dotObjBytes (13 * m) q8)
    have hexit_rip : s_exit.rip = 85 := by
      change (run dotObjBytes 13 (run dotObjBytes (13 * m) q8)).rip = 85
      rw [hlast.2.2.2.2.2.2.2.2.2.2.2]; simp
    have hep := h_epilog s_exit (dotBlocks64Spec s.mem8 (s.gpr .rdi) (s.gpr .rsi) (m + 1))
      hexit_rip hlast.1 hlast.2.1 hlast.2.2.2.2.1 hlast.2.2.2.2.2.2.2.1 hlast.2.2.2.2.2.2.2.2.1
      hlast.2.2.2.2.2.2.2.2.2.2.1
    dsimp only at hep
    have hfuel : 18 + 13 * (m + 1) = 8 + (13 * m + (13 + 10)) := by omega
    rw [hfuel, run_add dotObjBytes 8 _ s, hrun8, run_add dotObjBytes (13 * m) (13 + 10) q8,
        run_add dotObjBytes 13 10 (run dotObjBytes (13 * m) q8)]
    exact hep

end LockedObligations
