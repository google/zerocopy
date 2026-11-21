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
Regime (a): Unassisted direct `.o` machine-byte proof for `mulx_adcx_adox_mac4_asm`
(100 bytes, 20 instructions) without `UntrustedHints` certificate reflection.
-/

namespace LockedObligations

open AsmMirBase IsaLemmas

theorem verify_mulx_mac4_obj (s : X86State)
    (hrip : s.rip = 0) (hnh : s.halted = false) (hnf : s.fault = false) (hymm : s.ymmDirty = false)
    (hrdi : s.gpr .rdi + 24 < W64) (hrsi : s.gpr .rsi + 24 < W64)
    (hdisj : s.gpr .rdi + 32 ≤ s.gpr .rsi ∨ s.gpr .rsi + 32 ≤ s.gpr .rdi) :
    let sf := run mulxObjBytes 20 s
    let rdi := s.gpr .rdi
    let rsi := s.gpr .rsi
    sf.halted = true ∧
    sf.fault = false ∧
    sf.cf = false ∧
    sf.of_ = false ∧
    sf.gpr .rsp = s.gpr .rsp ∧
    sf.gpr .rbx = s.gpr .rbx ∧
    val5Limbs (readMem64 sf rdi) (readMem64 sf (rdi + 8))
              (readMem64 sf (rdi + 16)) (readMem64 sf (rdi + 24)) (sf.gpr .rax) =
      mac4RefVal (readMem64 s rdi) (readMem64 s (rdi + 8))
                 (readMem64 s (rdi + 16)) (readMem64 s (rdi + 24))
                 (readMem64 s rsi) (readMem64 s (rsi + 8))
                 (readMem64 s (rsi + 16)) (readMem64 s (rsi + 24))
                 (s.gpr .rdx % W64) := by
  let rdi := s.gpr .rdi
  let rsi := s.gpr .rsi
  let b := s.gpr .rdx % W64
  let t0 := readMem64 s rdi
  let t1 := readMem64 s (rdi + 8)
  let t2 := readMem64 s (rdi + 16)
  let t3 := readMem64 s (rdi + 24)
  let a0 := readMem64 s rsi
  let a1 := readMem64 s (rsi + 8)
  let a2 := readMem64 s (rsi + 16)
  let a3 := readMem64 s (rsi + 24)
  have md0 : rdi % W64 = rdi := Nat.mod_eq_of_lt (by omega)
  have md1 : (rdi + 8) % W64 = rdi + 8 := Nat.mod_eq_of_lt (by omega)
  have md2 : (rdi + 16) % W64 = rdi + 16 := Nat.mod_eq_of_lt (by omega)
  have md3 : (rdi + 24) % W64 = rdi + 24 := Nat.mod_eq_of_lt hrdi
  have ms0 : rsi % W64 = rsi := Nat.mod_eq_of_lt (by omega)
  have ms1 : (rsi + 8) % W64 = rsi + 8 := Nat.mod_eq_of_lt (by omega)
  have ms2 : (rsi + 16) % W64 = rsi + 16 := Nat.mod_eq_of_lt (by omega)
  have ms3 : (rsi + 24) % W64 = rsi + 24 := Nat.mod_eq_of_lt hrsi
  have hlt_w : ∀ x, x % W64 % W64 = x % W64 := fun x => Nat.mod_mod x W64
  have hcomb := mac4_combine_conservation t0 t1 t2 t3 a0 a1 a2 a3 b
    (readMem64_lt s rdi) (readMem64_lt s (rdi + 8)) (readMem64_lt s (rdi + 16)) (readMem64_lt s (rdi + 24))
    (readMem64_lt s rsi) (readMem64_lt s (rsi + 8)) (readMem64_lt s (rsi + 16)) (readMem64_lt s (rsi + 24))
    (Nat.mod_lt _ (by decide : 0 < W64))
  dsimp only at hcomb
  let lo0 := (b * a0) % W64; let hi0 := ((b * a0) / W64) % W64
  let lo1 := (b * a1) % W64; let hi1 := ((b * a1) / W64) % W64
  let lo2 := (b * a2) % W64; let hi2 := ((b * a2) / W64) % W64
  let lo3 := (b * a3) % W64; let hi3 := ((b * a3) / W64) % W64
  let sum0 := lo0 + t0
  let out0 := sum0 % W64; let cf1 := sum0 / W64
  let u1v := hi0 + lo1 + cf1
  let r9_1 := u1v % W64; let cf2 := u1v / W64
  let v1 := r9_1 + t1 + 0
  let out1 := v1 % W64; let of2 := v1 / W64
  let u2v := hi1 + lo2 + cf2
  let r10_2 := u2v % W64; let cf3 := u2v / W64
  let v2 := r10_2 + t2 + of2
  let out2 := v2 % W64; let of3 := v2 / W64
  let u3v := hi2 + lo3 + cf3
  let r11_3 := u3v % W64; let cf4 := u3v / W64
  let v3 := r11_3 + t3 + of3
  let out3 := v3 % W64; let of4 := v3 / W64
  let u4v := hi3 + cf4
  let rax1 := u4v % W64
  let v4 := rax1 + of4
  let out4 := v4 % W64
  have hw64 : W64 = 18446744073709551616 := rfl
  have hlo0 : lo0 < W64 := Nat.mod_lt _ (by decide)
  have hhi0 : hi0 < W64 := Nat.mod_lt _ (by decide)
  have hlo1 : lo1 < W64 := Nat.mod_lt _ (by decide)
  have hhi1 : hi1 < W64 := Nat.mod_lt _ (by decide)
  have hlo2 : lo2 < W64 := Nat.mod_lt _ (by decide)
  have hhi2 : hi2 < W64 := Nat.mod_lt _ (by decide)
  have hlo3 : lo3 < W64 := Nat.mod_lt _ (by decide)
  have hhi3 : hi3 < W64 := Nat.mod_lt _ (by decide)
  have ht0 : t0 < W64 := readMem64_lt s rdi
  have ht1 : t1 < W64 := readMem64_lt s (rdi + 8)
  have ht2 : t2 < W64 := readMem64_lt s (rdi + 16)
  have ht3 : t3 < W64 := readMem64_lt s (rdi + 24)
  have hr9_lt   : r9_1 < W64  := Nat.mod_lt _ (by decide)
  have hr10_lt  : r10_2 < W64 := Nat.mod_lt _ (by decide)
  have hr11_lt  : r11_3 < W64 := Nat.mod_lt _ (by decide)
  have hout0_lt : out0 < W64  := Nat.mod_lt _ (by decide)
  have hout1_lt : out1 < W64  := Nat.mod_lt _ (by decide)
  have hout2_lt : out2 < W64  := Nat.mod_lt _ (by decide)
  have hout3_lt : out3 < W64  := Nat.mod_lt _ (by decide)
  have hcf1_b : b2n (decide (sum0 ≥ W64)) = cf1 := b2n_decide_ge sum0 (by omega)
  have hcf1_le : cf1 ≤ 1 := Nat.le_of_lt_succ ((Nat.div_lt_iff_lt_mul (by decide : 0 < W64)).mpr (by omega))
  have hcf2_b : b2n (decide (u1v ≥ W64)) = cf2 := b2n_decide_ge u1v (by omega)
  have hcf2_le : cf2 ≤ 1 := Nat.le_of_lt_succ ((Nat.div_lt_iff_lt_mul (by decide : 0 < W64)).mpr (by omega))
  have hof2_b : b2n (decide (v1 ≥ W64)) = of2 := b2n_decide_ge v1 (by omega)
  have hof2_le : of2 ≤ 1 := Nat.le_of_lt_succ ((Nat.div_lt_iff_lt_mul (by decide : 0 < W64)).mpr (by omega))
  have hcf3_b : b2n (decide (u2v ≥ W64)) = cf3 := b2n_decide_ge u2v (by omega)
  have hcf3_le : cf3 ≤ 1 := Nat.le_of_lt_succ ((Nat.div_lt_iff_lt_mul (by decide : 0 < W64)).mpr (by omega))
  have hof3_b : b2n (decide (v2 ≥ W64)) = of3 := b2n_decide_ge v2 (by omega)
  have hof3_le : of3 ≤ 1 := Nat.le_of_lt_succ ((Nat.div_lt_iff_lt_mul (by decide : 0 < W64)).mpr (by omega))
  have hcf4_b : b2n (decide (u3v ≥ W64)) = cf4 := b2n_decide_ge u3v (by omega)
  have hof4_b : b2n (decide (v3 ≥ W64)) = of4 := b2n_decide_ge v3 (by omega)

  -- Manual PC-by-PC decode & state stepping across byte offsets 0, 2, 4, 9, 15, ..., 99
  let g1 := gprUpd s.gpr .rcx 0
  let k1 : X86State := { s with rip := 2, cf := false, of_ := false, zf := true, gpr := g1 }
  have hk1 : step mulxObjBytes s = k1 :=
    (step_of_decode (s := s) hnh hnf (by rw [hrip]; rfl)).trans (exec_xorZero32 (by rw [hrip]))

  let g2 := gprUpd g1 .rax 0
  let k2 : X86State := { k1 with rip := 4, gpr := g2 }
  have hk2 : step mulxObjBytes k1 = k2 :=
    (step_of_decode (s := k1) hnh hnf rfl).trans (exec_xorZero32 rfl)

  let g3 := gprUpd (gprUpd g2 .r8 lo0) .r9 hi0
  let l_3 := s.leak ++ [.load64 rsi]
  let k3 : X86State := { k2 with rip := 9, gpr := g3, leak := l_3 }
  have hk3 : step mulxObjBytes k2 = k3 :=
    (step_of_decode (s := k2) hnh hnf rfl).trans
      (exec_mulxMem (by decide) rfl rfl (by change (rsi + 0) % W64 = rsi; rw [Nat.add_zero, ms0]) rfl)

  let g4 := gprUpd g3 .r8 out0
  let l_4 := l_3 ++ [.load64 rdi]
  let k4 : X86State := { k3 with rip := 15, cf := decide (sum0 ≥ W64), gpr := g4, leak := l_4 }
  have hk4 : step mulxObjBytes k3 = k4 :=
    (step_of_decode (s := k3) hnh hnf rfl).trans
      (exec_adcxMem rfl (by change lo0 % W64 = lo0; exact Nat.mod_eq_of_lt hlo0)
        (by change (rdi + 0) % W64 = rdi; rw [Nat.add_zero, md0]) rfl rfl)

  let m5 := mem64Upd s.mem64 rdi out0
  let l_5 := l_4 ++ [.store64 rdi]
  let k5 : X86State := { k4 with rip := 18, mem64 := m5, leak := l_5 }
  have hk5 : step mulxObjBytes k4 = k5 :=
    (step_of_decode (s := k4) hnh hnf rfl).trans
      (exec_movStore64 rfl (by change (rdi + 0) % W64 = rdi; rw [Nat.add_zero, md0])
        (by change out0 % W64 = out0; exact Nat.mod_eq_of_lt hout0_lt))

  let g6 := gprUpd (gprUpd g4 .r8 lo1) .r10 hi1
  let l_6 := l_5 ++ [.load64 (rsi + 8)]
  let k6 : X86State := { k5 with rip := 24, gpr := g6, leak := l_6 }
  have hk6 : step mulxObjBytes k5 = k6 :=
    (step_of_decode (s := k5) hnh hnf rfl).trans
      (exec_mulxMem (by decide) rfl rfl ms1
        (by unfold readMem64; dsimp [k5, m5]; rw [mem64Upd_ne (by omega)]; rfl))

  let g7 := gprUpd g6 .r9 r9_1
  let k7 : X86State := { k6 with rip := 30, cf := decide (u1v ≥ W64), gpr := g7 }
  have hk7 : step mulxObjBytes k6 = k7 :=
    (step_of_decode (s := k6) hnh hnf rfl).trans
      (exec_adcxReg rfl (by change hi0 % W64 = hi0; exact Nat.mod_eq_of_lt hhi0)
        (by change lo1 % W64 = lo1; exact Nat.mod_eq_of_lt hlo1) hcf1_b)

  let g8 := gprUpd g7 .r9 out1
  let l_8 := l_6 ++ [.load64 (rdi + 8)]
  let k8 : X86State := { k7 with rip := 37, of_ := decide (v1 ≥ W64), gpr := g8, leak := l_8 }
  have hk8 : step mulxObjBytes k7 = k8 :=
    (step_of_decode (s := k7) hnh hnf rfl).trans
      (exec_adoxMem rfl (by change r9_1 % W64 = r9_1; exact Nat.mod_eq_of_lt hr9_lt) md1
        (by unfold readMem64; dsimp [k7, k6, k5, m5]; rw [mem64Upd_ne (by omega)]; rfl) rfl)

  let m9 := mem64Upd m5 (rdi + 8) out1
  let l_9 := l_8 ++ [.store64 (rdi + 8)]
  let k9 : X86State := { k8 with rip := 41, mem64 := m9, leak := l_9 }
  have hk9 : step mulxObjBytes k8 = k9 :=
    (step_of_decode (s := k8) hnh hnf rfl).trans
      (exec_movStore64 rfl md1 (by change out1 % W64 = out1; exact Nat.mod_eq_of_lt hout1_lt))

  let g10 := gprUpd (gprUpd g8 .r8 lo2) .r11 hi2
  let l_10 := l_9 ++ [.load64 (rsi + 16)]
  let k10 : X86State := { k9 with rip := 47, gpr := g10, leak := l_10 }
  have hk10 : step mulxObjBytes k9 = k10 :=
    (step_of_decode (s := k9) hnh hnf rfl).trans
      (exec_mulxMem (by decide) rfl rfl ms2
        (by unfold readMem64; dsimp [k9, m9, m5]; rw [mem64Upd_ne (by omega), mem64Upd_ne (by omega)]; rfl))

  let g11 := gprUpd g10 .r10 r10_2
  let k11 : X86State := { k10 with rip := 53, cf := decide (u2v ≥ W64), gpr := g11 }
  have hk11 : step mulxObjBytes k10 = k11 :=
    (step_of_decode (s := k10) hnh hnf rfl).trans
      (exec_adcxReg rfl (by change hi1 % W64 = hi1; exact Nat.mod_eq_of_lt hhi1)
        (by change lo2 % W64 = lo2; exact Nat.mod_eq_of_lt hlo2) hcf2_b)

  let g12 := gprUpd g11 .r10 out2
  let l_12 := l_10 ++ [.load64 (rdi + 16)]
  let k12 : X86State := { k11 with rip := 60, of_ := decide (v2 ≥ W64), gpr := g12, leak := l_12 }
  have hk12 : step mulxObjBytes k11 = k12 :=
    (step_of_decode (s := k11) hnh hnf rfl).trans
      (exec_adoxMem rfl (by change r10_2 % W64 = r10_2; exact Nat.mod_eq_of_lt hr10_lt) md2
        (by unfold readMem64; dsimp [k11, k10, k9, m9, m5]; rw [mem64Upd_ne (by omega), mem64Upd_ne (by omega)]; rfl) hof2_b)

  let m13 := mem64Upd m9 (rdi + 16) out2
  let l_13 := l_12 ++ [.store64 (rdi + 16)]
  let k13 : X86State := { k12 with rip := 64, mem64 := m13, leak := l_13 }
  have hk13 : step mulxObjBytes k12 = k13 :=
    (step_of_decode (s := k12) hnh hnf rfl).trans
      (exec_movStore64 rfl md2 (by change out2 % W64 = out2; exact Nat.mod_eq_of_lt hout2_lt))

  let g14 := gprUpd (gprUpd g12 .r8 lo3) .r9 hi3
  let l_14 := l_13 ++ [.load64 (rsi + 24)]
  let k14 : X86State := { k13 with rip := 70, gpr := g14, leak := l_14 }
  have hk14 : step mulxObjBytes k13 = k14 :=
    (step_of_decode (s := k13) hnh hnf rfl).trans
      (exec_mulxMem (by decide) rfl rfl ms3
        (by unfold readMem64; dsimp [k13, m13, m9, m5]; rw [mem64Upd_ne (by omega), mem64Upd_ne (by omega), mem64Upd_ne (by omega)]; rfl))

  let g15 := gprUpd g14 .r11 r11_3
  let k15 : X86State := { k14 with rip := 76, cf := decide (u3v ≥ W64), gpr := g15 }
  have hk15 : step mulxObjBytes k14 = k15 :=
    (step_of_decode (s := k14) hnh hnf rfl).trans
      (exec_adcxReg rfl (by change hi2 % W64 = hi2; exact Nat.mod_eq_of_lt hhi2)
        (by change lo3 % W64 = lo3; exact Nat.mod_eq_of_lt hlo3) hcf3_b)

  let g16 := gprUpd g15 .r11 out3
  let l_16 := l_14 ++ [.load64 (rdi + 24)]
  let k16 : X86State := { k15 with rip := 83, of_ := decide (v3 ≥ W64), gpr := g16, leak := l_16 }
  have hk16 : step mulxObjBytes k15 = k16 :=
    (step_of_decode (s := k15) hnh hnf rfl).trans
      (exec_adoxMem rfl (by change r11_3 % W64 = r11_3; exact Nat.mod_eq_of_lt hr11_lt) md3
        (by unfold readMem64; dsimp [k15, k14, k13, m13, m9, m5]; rw [mem64Upd_ne (by omega), mem64Upd_ne (by omega), mem64Upd_ne (by omega)]; rfl) hof3_b)

  let m17 := mem64Upd m13 (rdi + 24) out3
  let l_17 := l_16 ++ [.store64 (rdi + 24)]
  let k17 : X86State := { k16 with rip := 87, mem64 := m17, leak := l_17 }
  have hk17 : step mulxObjBytes k16 = k17 :=
    (step_of_decode (s := k16) hnh hnf rfl).trans
      (exec_movStore64 rfl md3 (by change out3 % W64 = out3; exact Nat.mod_eq_of_lt hout3_lt))

  have hu4_lt : u4v < W64 := by
    have hz : u4v / W64 = 0 := hcomb.2.1
    have h1 : u4v < 1 * W64 := (Nat.div_lt_iff_lt_mul (by decide : 0 < W64)).mp (by rw [hz]; decide)
    omega
  let g18 := gprUpd g16 .rax rax1
  let k18 : X86State := { k17 with rip := 93, cf := false, gpr := g18 }
  have hk18 : step mulxObjBytes k17 = k18 := by
    refine (step_of_decode (s := k17) hnh hnf rfl).trans
      ((exec_adcxReg rfl (x := 0) (y := hi3) (c := cf4) rfl
        (by change hi3 % W64 = hi3; exact Nat.mod_eq_of_lt hhi3) hcf4_b).trans ?_)
    have e1 : 0 + hi3 + cf4 = u4v := by dsimp [u4v]; omega
    have e2 : decide (0 + hi3 + cf4 ≥ W64) = false := by
      rw [e1]; exact decide_eq_false (Nat.not_le_of_lt hu4_lt)
    rw [e2, e1]; exact rfl

  have hv4_lt : v4 < W64 := by
    have hz : v4 / W64 = 0 := hcomb.2.2
    have h1 : v4 < 1 * W64 := (Nat.div_lt_iff_lt_mul (by decide : 0 < W64)).mp (by rw [hz]; decide)
    omega
  let g19 := gprUpd g18 .rax out4
  let k19 : X86State := { k18 with rip := 99, of_ := false, gpr := g19 }
  have hk19 : step mulxObjBytes k18 = k19 := by
    have hrax1_lt : rax1 < W64 := Nat.mod_lt _ (by decide)
    refine (step_of_decode (s := k18) hnh hnf rfl).trans
      ((exec_adoxReg rfl (x := rax1) (y := 0) (c := of4)
        (by change rax1 % W64 = rax1; exact Nat.mod_eq_of_lt hrax1_lt) rfl hof4_b).trans ?_)
    have e1 : rax1 + 0 + of4 = v4 := rfl
    have e2 : decide (rax1 + 0 + of4 ≥ W64) = false := by
      rw [e1]; exact decide_eq_false (Nat.not_le_of_lt hv4_lt)
    rw [e2, e1]; exact rfl

  let k20 : X86State := { k19 with halted := true }
  have hk20 : step mulxObjBytes k19 = k20 :=
    (step_of_decode (s := k19) hnh hnf rfl).trans (exec_ret_clean hymm)

  have hrun20 : run mulxObjBytes 20 s = k20 := by
    rw [run_succ, hk1, run_succ, hk2, run_succ, hk3, run_succ, hk4, run_succ, hk5,
        run_succ, hk6, run_succ, hk7, run_succ, hk8, run_succ, hk9, run_succ, hk10,
        run_succ, hk11, run_succ, hk12, run_succ, hk13, run_succ, hk14, run_succ, hk15,
        run_succ, hk16, run_succ, hk17, run_succ, hk18, run_succ, hk19, run_succ, hk20, run_zero]
  dsimp only; rw [hrun20]
  have hm0 : readMem64 k20 rdi = out0 := by
    unfold readMem64; dsimp [k20, k19, k18, k17, m17, m13, m9, m5]
    rw [mem64Upd_ne (by omega), mem64Upd_ne (by omega), mem64Upd_ne (by omega), mem64Upd_eq]
    simp only [Nat.mod_eq_of_lt hout0_lt]
  have hm1 : readMem64 k20 (rdi + 8) = out1 := by
    unfold readMem64; dsimp [k20, k19, k18, k17, m17, m13, m9]
    rw [mem64Upd_ne (by omega), mem64Upd_ne (by omega), mem64Upd_eq]
    simp only [Nat.mod_eq_of_lt hout1_lt]
  have hm2 : readMem64 k20 (rdi + 16) = out2 := by
    unfold readMem64; dsimp [k20, k19, k18, k17, m17, m13]
    rw [mem64Upd_ne (by omega), mem64Upd_eq]
    simp only [Nat.mod_eq_of_lt hout2_lt]
  have hm3 : readMem64 k20 (rdi + 24) = out3 := by
    unfold readMem64; dsimp [k20, k19, k18, k17, m17]
    rw [mem64Upd_eq]; simp only [Nat.mod_eq_of_lt hout3_lt]
  rw [hm0, hm1, hm2, hm3]
  exact ⟨rfl, hnf, rfl, rfl, rfl, rfl, hcomb.1⟩

end LockedObligations
