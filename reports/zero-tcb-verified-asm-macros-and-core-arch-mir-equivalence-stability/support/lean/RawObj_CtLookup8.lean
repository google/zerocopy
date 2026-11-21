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
Regime (a): Unassisted direct `.o` machine-byte proof for `ct_lookup8_cmov_asm`
(98 bytes, 26 instructions: functional correctness + 2-safety constant-time leakage)
without `UntrustedHints`.
-/

namespace LockedObligations

open AsmMirBase IsaLemmas

private theorem rawCtSelect8_eq (s : X86State) (base idx : Nat) :
    ctSelectMirTwin s base idx = lookup8Spec s base idx := by
  unfold ctSelectMirTwin lookup8Spec ctSelectStep
  by_cases h7 : idx = 7
  · subst h7; simp
  · by_cases h6 : idx = 6
    · subst h6; simp
    · by_cases h5 : idx = 5
      · subst h5; simp
      · by_cases h4 : idx = 4
        · subst h4; simp
        · by_cases h3 : idx = 3
          · subst h3; simp
          · by_cases h2 : idx = 2
            · subst h2; simp
            · by_cases h1 : idx = 1
              · subst h1; simp
              · by_cases h0 : idx = 0
                · subst h0; simp
                · have hnlt : ¬ (idx < 8) := by omega
                  simp [h7, h6, h5, h4, h3, h2, h1, h0, hnlt]

private theorem rawCt_exec (s : X86State)
    (hrip : s.rip = 0) (hnh : s.halted = false) (hnf : s.fault = false) (hymm : s.ymmDirty = false) :
    let sf := run ctObjBytes 26 s
    let b := s.gpr .rdi
    sf.halted = true ∧
    sf.fault = false ∧
    sf.gpr .rsp = s.gpr .rsp ∧
    sf.mem64 = s.mem64 ∧
    sf.gpr .rax = lookup8Spec s b (s.gpr .rsi % W64) ∧
    sf.leak = s.leak ++
      [ .load64 ((b + 0) % W64),  .load64 ((b + 8) % W64),
        .load64 ((b + 16) % W64), .load64 ((b + 24) % W64),
        .load64 ((b + 32) % W64), .load64 ((b + 40) % W64),
        .load64 ((b + 48) % W64), .load64 ((b + 56) % W64) ] := by
  let b := s.gpr .rdi
  let idx := s.gpr .rsi % W64
  let a0 := ctSelectStep s b idx 0 0
  let a1 := ctSelectStep s b idx a0 1
  let a2 := ctSelectStep s b idx a1 2
  let a3 := ctSelectStep s b idx a2 3
  let a4 := ctSelectStep s b idx a3 4
  let a5 := ctSelectStep s b idx a4 5
  let a6 := ctSelectStep s b idx a5 6
  let a7 := ctSelectStep s b idx a6 7
  have ha_lt : ∀ acc k, acc < W64 → ctSelectStep s b idx acc k < W64 := by
    intro acc k hacc; unfold ctSelectStep; split
    · exact readMem64_lt _ _
    · exact hacc
  have ha0_lt : a0 < W64 := ha_lt 0 0 (by decide)
  have ha1_lt : a1 < W64 := ha_lt a0 1 ha0_lt
  have ha2_lt : a2 < W64 := ha_lt a1 2 ha1_lt
  have ha3_lt : a3 < W64 := ha_lt a2 3 ha2_lt
  have ha4_lt : a4 < W64 := ha_lt a3 4 ha3_lt
  have ha5_lt : a5 < W64 := ha_lt a4 5 ha4_lt
  have ha6_lt : a6 < W64 := ha_lt a5 6 ha5_lt
  have hcmov_eq : ∀ acc k (hacc : acc < W64),
      (if decide (idx = k) then readMem64 s ((b + 8 * k) % W64) % W64 else acc % W64) =
      ctSelectStep s b idx acc k := by
    intro acc k hacc
    rw [Nat.mod_eq_of_lt (readMem64_lt s _), Nat.mod_eq_of_lt hacc]
    unfold ctSelectStep
    cases hd : decide (idx = k) with
    | true => simp [of_decide_eq_true hd]
    | false => simp [of_decide_eq_false hd]

  -- PC 0: xor eax, eax
  let k1 : X86State := { s with rip := 2, cf := false, of_ := false, zf := true, gpr := gprUpd s.gpr .rax 0 }
  have hk1 : step ctObjBytes s = k1 :=
    (step_of_decode (s := s) (ins := .xorZero32 .rax) (len := 2) hnh hnf (by rw [hrip]; rfl)).trans
      (exec_xorZero32 (by rw [hrip]))

  -- Entry 0 (PC 2, 5, 9)
  let l0 := s.leak ++ [.load64 ((b + 0) % W64)]
  let k2 : X86State := { k1 with rip := 5, gpr := gprUpd k1.gpr .r8 (readMem64 s ((b + 0) % W64)), leak := l0 }
  have hk2 : step ctObjBytes k1 = k2 := by rw [step_of_decode (s := k1) hnh hnf rfl]; rfl
  let k3 : X86State := { k2 with rip := 9, cf := decide (idx < 0), zf := decide (idx = 0), of_ := false }
  have hk3 : step ctObjBytes k2 = k3 := by rw [step_of_decode (s := k2) hnh hnf rfl]; rfl
  let k4 : X86State := { k3 with rip := 13, gpr := gprUpd k2.gpr .rax a0 }
  have hk4 : step ctObjBytes k3 = k4 := by
    rw [step_of_decode (s := k3) (ins := .cmove64 .rax .r8) (len := 4) hnh hnf rfl]
    dsimp [execInsn, k4, k3, k2, k1, gprUpd]
    have h0 := hcmov_eq 0 0 (by decide); dsimp at h0; rw [h0]

  -- Entry 1 (PC 13, 17, 21)
  let l1 := l0 ++ [.load64 ((b + 8) % W64)]
  let k5 : X86State := { k4 with rip := 17, gpr := gprUpd k4.gpr .r8 (readMem64 s ((b + 8) % W64)), leak := l1 }
  have hk5 : step ctObjBytes k4 = k5 := by rw [step_of_decode (s := k4) hnh hnf rfl]; rfl
  let k6 : X86State := { k5 with rip := 21, cf := decide (idx < 1), zf := decide (idx = 1), of_ := false }
  have hk6 : step ctObjBytes k5 = k6 := by rw [step_of_decode (s := k5) hnh hnf rfl]; rfl
  let k7 : X86State := { k6 with rip := 25, gpr := gprUpd k5.gpr .rax a1 }
  have hk7 : step ctObjBytes k6 = k7 := by
    rw [step_of_decode (s := k6) (ins := .cmove64 .rax .r8) (len := 4) hnh hnf rfl]
    dsimp [execInsn, k7, k6, k5, k4, gprUpd]; rw [hcmov_eq a0 1 ha0_lt]

  -- Entry 2 (PC 25, 29, 33)
  let l2 := l1 ++ [.load64 ((b + 16) % W64)]
  let k8 : X86State := { k7 with rip := 29, gpr := gprUpd k7.gpr .r8 (readMem64 s ((b + 16) % W64)), leak := l2 }
  have hk8 : step ctObjBytes k7 = k8 := by rw [step_of_decode (s := k7) hnh hnf rfl]; rfl
  let k9 : X86State := { k8 with rip := 33, cf := decide (idx < 2), zf := decide (idx = 2), of_ := false }
  have hk9 : step ctObjBytes k8 = k9 := by rw [step_of_decode (s := k8) hnh hnf rfl]; rfl
  let k10 : X86State := { k9 with rip := 37, gpr := gprUpd k8.gpr .rax a2 }
  have hk10 : step ctObjBytes k9 = k10 := by
    rw [step_of_decode (s := k9) (ins := .cmove64 .rax .r8) (len := 4) hnh hnf rfl]
    dsimp [execInsn, k10, k9, k8, k7, gprUpd]; rw [hcmov_eq a1 2 ha1_lt]

  -- Entry 3 (PC 37, 41, 45)
  let l3 := l2 ++ [.load64 ((b + 24) % W64)]
  let k11 : X86State := { k10 with rip := 41, gpr := gprUpd k10.gpr .r8 (readMem64 s ((b + 24) % W64)), leak := l3 }
  have hk11 : step ctObjBytes k10 = k11 := by rw [step_of_decode (s := k10) hnh hnf rfl]; rfl
  let k12 : X86State := { k11 with rip := 45, cf := decide (idx < 3), zf := decide (idx = 3), of_ := false }
  have hk12 : step ctObjBytes k11 = k12 := by rw [step_of_decode (s := k11) hnh hnf rfl]; rfl
  let k13 : X86State := { k12 with rip := 49, gpr := gprUpd k11.gpr .rax a3 }
  have hk13 : step ctObjBytes k12 = k13 := by
    rw [step_of_decode (s := k12) (ins := .cmove64 .rax .r8) (len := 4) hnh hnf rfl]
    dsimp [execInsn, k13, k12, k11, k10, gprUpd]; rw [hcmov_eq a2 3 ha2_lt]

  -- Entry 4 (PC 49, 53, 57)
  let l4 := l3 ++ [.load64 ((b + 32) % W64)]
  let k14 : X86State := { k13 with rip := 53, gpr := gprUpd k13.gpr .r8 (readMem64 s ((b + 32) % W64)), leak := l4 }
  have hk14 : step ctObjBytes k13 = k14 := by rw [step_of_decode (s := k13) hnh hnf rfl]; rfl
  let k15 : X86State := { k14 with rip := 57, cf := decide (idx < 4), zf := decide (idx = 4), of_ := false }
  have hk15 : step ctObjBytes k14 = k15 := by rw [step_of_decode (s := k14) hnh hnf rfl]; rfl
  let k16 : X86State := { k15 with rip := 61, gpr := gprUpd k14.gpr .rax a4 }
  have hk16 : step ctObjBytes k15 = k16 := by
    rw [step_of_decode (s := k15) (ins := .cmove64 .rax .r8) (len := 4) hnh hnf rfl]
    dsimp [execInsn, k16, k15, k14, k13, gprUpd]; rw [hcmov_eq a3 4 ha3_lt]

  -- Entry 5 (PC 61, 65, 69)
  let l5 := l4 ++ [.load64 ((b + 40) % W64)]
  let k17 : X86State := { k16 with rip := 65, gpr := gprUpd k16.gpr .r8 (readMem64 s ((b + 40) % W64)), leak := l5 }
  have hk17 : step ctObjBytes k16 = k17 := by rw [step_of_decode (s := k16) hnh hnf rfl]; rfl
  let k18 : X86State := { k17 with rip := 69, cf := decide (idx < 5), zf := decide (idx = 5), of_ := false }
  have hk18 : step ctObjBytes k17 = k18 := by rw [step_of_decode (s := k17) hnh hnf rfl]; rfl
  let k19 : X86State := { k18 with rip := 73, gpr := gprUpd k17.gpr .rax a5 }
  have hk19 : step ctObjBytes k18 = k19 := by
    rw [step_of_decode (s := k18) (ins := .cmove64 .rax .r8) (len := 4) hnh hnf rfl]
    dsimp [execInsn, k19, k18, k17, k16, gprUpd]; rw [hcmov_eq a4 5 ha4_lt]

  -- Entry 6 (PC 73, 77, 81)
  let l6 := l5 ++ [.load64 ((b + 48) % W64)]
  let k20 : X86State := { k19 with rip := 77, gpr := gprUpd k19.gpr .r8 (readMem64 s ((b + 48) % W64)), leak := l6 }
  have hk20 : step ctObjBytes k19 = k20 := by rw [step_of_decode (s := k19) hnh hnf rfl]; rfl
  let k21 : X86State := { k20 with rip := 81, cf := decide (idx < 6), zf := decide (idx = 6), of_ := false }
  have hk21 : step ctObjBytes k20 = k21 := by rw [step_of_decode (s := k20) hnh hnf rfl]; rfl
  let k22 : X86State := { k21 with rip := 85, gpr := gprUpd k20.gpr .rax a6 }
  have hk22 : step ctObjBytes k21 = k22 := by
    rw [step_of_decode (s := k21) (ins := .cmove64 .rax .r8) (len := 4) hnh hnf rfl]
    dsimp [execInsn, k22, k21, k20, k19, gprUpd]; rw [hcmov_eq a5 6 ha5_lt]

  -- Entry 7 (PC 85, 89, 93) + ret (PC 97)
  let l7 := l6 ++ [.load64 ((b + 56) % W64)]
  let k23 : X86State := { k22 with rip := 89, gpr := gprUpd k22.gpr .r8 (readMem64 s ((b + 56) % W64)), leak := l7 }
  have hk23 : step ctObjBytes k22 = k23 := by rw [step_of_decode (s := k22) hnh hnf rfl]; rfl
  let k24 : X86State := { k23 with rip := 93, cf := decide (idx < 7), zf := decide (idx = 7), of_ := false }
  have hk24 : step ctObjBytes k23 = k24 := by rw [step_of_decode (s := k23) hnh hnf rfl]; rfl
  let k25 : X86State := { k24 with rip := 97, gpr := gprUpd k23.gpr .rax a7 }
  have hk25 : step ctObjBytes k24 = k25 := by
    rw [step_of_decode (s := k24) (ins := .cmove64 .rax .r8) (len := 4) hnh hnf rfl]
    dsimp [execInsn, k25, k24, k23, k22, gprUpd]; rw [hcmov_eq a6 7 ha6_lt]

  let k26 : X86State := { k25 with halted := true }
  have hk26 : step ctObjBytes k25 = k26 :=
    (step_of_decode (s := k25) hnh hnf rfl).trans (exec_ret_clean hymm)

  have hrun26 : run ctObjBytes 26 s = k26 := by
    rw [run_succ, hk1, run_succ, hk2, run_succ, hk3, run_succ, hk4, run_succ, hk5,
        run_succ, hk6, run_succ, hk7, run_succ, hk8, run_succ, hk9, run_succ, hk10,
        run_succ, hk11, run_succ, hk12, run_succ, hk13, run_succ, hk14, run_succ, hk15,
        run_succ, hk16, run_succ, hk17, run_succ, hk18, run_succ, hk19, run_succ, hk20,
        run_succ, hk21, run_succ, hk22, run_succ, hk23, run_succ, hk24, run_succ, hk25,
        run_succ, hk26, run_zero]
  dsimp only; rw [hrun26]
  have hrax_f : k26.gpr .rax = lookup8Spec s b idx := by
    change a7 = lookup8Spec s b idx
    rw [← rawCtSelect8_eq]; rfl
  refine ⟨rfl, hnf, rfl, rfl, hrax_f, ?_⟩
  dsimp [k26, k25, k24, k23, l7, l6, l5, l4, l3, l2, l1, l0, b]
  simp [List.append_assoc]

theorem verify_ct_lookup8_obj (s : X86State)
    (hrip : s.rip = 0) (hnh : s.halted = false) (hnf : s.fault = false) (hymm : s.ymmDirty = false) :
    let sf := run ctObjBytes 26 s
    sf.halted = true ∧
    sf.fault = false ∧
    sf.gpr .rsp = s.gpr .rsp ∧
    sf.mem64 = s.mem64 ∧
    sf.gpr .rax = lookup8Spec s (s.gpr .rdi) (s.gpr .rsi % W64) := by
  have h := rawCt_exec s hrip hnh hnf hymm
  exact ⟨h.1, h.2.1, h.2.2.1, h.2.2.2.1, h.2.2.2.2.1⟩

theorem verify_ct_lookup8_2safety (s1 s2 : X86State)
    (hrip1 : s1.rip = 0) (hnh1 : s1.halted = false) (hnf1 : s1.fault = false) (hymm1 : s1.ymmDirty = false)
    (hrip2 : s2.rip = 0) (hnh2 : s2.halted = false) (hnf2 : s2.fault = false) (hymm2 : s2.ymmDirty = false)
    (hpub : s1.gpr .rdi = s2.gpr .rdi) (hleak : s1.leak = s2.leak) :
    (run ctObjBytes 26 s1).leak = (run ctObjBytes 26 s2).leak := by
  have ex1 := rawCt_exec s1 hrip1 hnh1 hnf1 hymm1
  have ex2 := rawCt_exec s2 hrip2 hnh2 hnf2 hymm2
  dsimp only at ex1 ex2
  rw [ex1.2.2.2.2.2, ex2.2.2.2.2.2, hpub, hleak]

end LockedObligations
