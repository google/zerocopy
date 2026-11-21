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
import Init.Data.Int.Basic
import Init.Data.List.Basic
import Init.Data.UInt.Basic
import Init.Omega
import AsmMirBase
import IsaLemmas

/-!
Reusable untrusted certificate checkers (`UntrustedHints.*`) consumed inside proof bodies
for `asm_verified!`-emitted `.o` kernels.
By Statement-Origin Separation, **zero** `UntrustedHints.*` declarations ever appear in the
type (`ConstantInfo.type`) of any locked verification theorem; every `HintCert` is checked
against the exact compiled `.o` byte list inside the proof term.
-/

namespace UntrustedHints

open AsmMirBase IsaLemmas

def checkAt (code : List UInt8) (pc : Nat) (expected : X86Insn) (nextPc : Nat) : Bool :=
  match decodeX86At code pc with
  | some (ins, len) => decide (ins = expected) && decide (pc + len = nextPc)
  | none => false

theorem checkAt_sound {code : List UInt8} {pc : Nat} {expected : X86Insn} {nextPc : Nat}
    (h : checkAt code pc expected nextPc = true) :
    ∃ len, decodeX86At code pc = some (expected, len) ∧ pc + len = nextPc := by
  unfold checkAt at h
  cases hdec : decodeX86At code pc with
  | none => rw [hdec] at h; contradiction
  | some pair =>
    rw [hdec] at h
    rcases pair with ⟨ins, len⟩
    dsimp only at h
    have hp := Bool.and_eq_true_iff.mp h
    exact ⟨len, by rw [of_decide_eq_true hp.1], of_decide_eq_true hp.2⟩

theorem step_checkAt (code : List UInt8) (s : X86State) {pc : Nat} {expected : X86Insn} {nextPc : Nat}
    (hrip : s.rip = pc) (hnh : s.halted = false) (hnf : s.fault = false)
    (hchk : checkAt code pc expected nextPc = true) :
    ∃ len, pc + len = nextPc ∧ step code s = execInsn expected len s := by
  rcases checkAt_sound hchk with ⟨len, hdec, hlen⟩
  refine ⟨len, hlen, ?_⟩
  rw [← hrip] at hdec
  exact step_of_decode hnh hnf hdec

-- ============================================================================
-- 1. Certificate Checker for 4-Limb BMI2 `mulx` + ADX (`adcx`/`adox`) Kernels
-- ============================================================================

structure DualCarryMac4Cert where
  (p0 p1 p2 p3 p4 p5 p6 p7 p8 p9 : Nat)
  (p10 p11 p12 p13 p14 p15 p16 p17 p18 p19 : Nat)

def checkDualCarryMac4Cert (code : List UInt8) (c : DualCarryMac4Cert) : Bool :=
  decide (c.p0 = 0) &&
  checkAt code c.p0  (.xorZero32 .rcx)           c.p1  &&
  checkAt code c.p1  (.xorZero32 .rax)           c.p2  &&
  checkAt code c.p2  (.mulxMem .r9 .r8 .rsi 0)   c.p3  &&
  checkAt code c.p3  (.adcxMem .r8 .rdi 0)       c.p4  &&
  checkAt code c.p4  (.movStore64 .rdi 0 .r8)    c.p5  &&
  checkAt code c.p5  (.mulxMem .r10 .r8 .rsi 8)  c.p6  &&
  checkAt code c.p6  (.adcxReg .r9 .r8)          c.p7  &&
  checkAt code c.p7  (.adoxMem .r9 .rdi 8)       c.p8  &&
  checkAt code c.p8  (.movStore64 .rdi 8 .r9)    c.p9  &&
  checkAt code c.p9  (.mulxMem .r11 .r8 .rsi 16) c.p10 &&
  checkAt code c.p10 (.adcxReg .r10 .r8)         c.p11 &&
  checkAt code c.p11 (.adoxMem .r10 .rdi 16)     c.p12 &&
  checkAt code c.p12 (.movStore64 .rdi 16 .r10)  c.p13 &&
  checkAt code c.p13 (.mulxMem .r9 .r8 .rsi 24)  c.p14 &&
  checkAt code c.p14 (.adcxReg .r11 .r8)         c.p15 &&
  checkAt code c.p15 (.adoxMem .r11 .rdi 24)     c.p16 &&
  checkAt code c.p16 (.movStore64 .rdi 24 .r11)  c.p17 &&
  checkAt code c.p17 (.adcxReg .rax .r9)         c.p18 &&
  checkAt code c.p18 (.adoxReg .rax .rcx)        c.p19 &&
  match decodeX86At code c.p19 with
  | some (.ret, _) => true
  | _ => false

theorem checkDualCarryMac4Cert_sound {code : List UInt8} {c : DualCarryMac4Cert} (s : X86State)
    (hcert : checkDualCarryMac4Cert code c = true)
    (hrip : s.rip = 0) (hnh : s.halted = false) (hnf : s.fault = false) (hymm : s.ymmDirty = false)
    (hrdi : s.gpr .rdi + 24 < W64) (hrsi : s.gpr .rsi + 24 < W64)
    (hdisj : s.gpr .rdi + 32 ≤ s.gpr .rsi ∨ s.gpr .rsi + 32 ≤ s.gpr .rdi) :
    let sf := run code 20 s
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
  unfold checkDualCarryMac4Cert at hcert
  have u20 := Bool.and_eq_true_iff.mp hcert
  have u19 := Bool.and_eq_true_iff.mp u20.1
  have u18 := Bool.and_eq_true_iff.mp u19.1
  have u17 := Bool.and_eq_true_iff.mp u18.1
  have u16 := Bool.and_eq_true_iff.mp u17.1
  have u15 := Bool.and_eq_true_iff.mp u16.1
  have u14 := Bool.and_eq_true_iff.mp u15.1
  have u13 := Bool.and_eq_true_iff.mp u14.1
  have u12 := Bool.and_eq_true_iff.mp u13.1
  have u11 := Bool.and_eq_true_iff.mp u12.1
  have u10 := Bool.and_eq_true_iff.mp u11.1
  have u9  := Bool.and_eq_true_iff.mp u10.1
  have u8  := Bool.and_eq_true_iff.mp u9.1
  have u7  := Bool.and_eq_true_iff.mp u8.1
  have u6  := Bool.and_eq_true_iff.mp u7.1
  have u5  := Bool.and_eq_true_iff.mp u6.1
  have u4  := Bool.and_eq_true_iff.mp u5.1
  have u3  := Bool.and_eq_true_iff.mp u4.1
  have u2  := Bool.and_eq_true_iff.mp u3.1
  have u1  := Bool.and_eq_true_iff.mp u2.1
  have hp0 : c.p0 = 0 := of_decide_eq_true u1.1
  have hret_dec : ∃ lret, decodeX86At code c.p19 = some (.ret, lret) := by
    have hr := u20.2
    cases hd : decodeX86At code c.p19 with
    | none => rw [hd] at hr; contradiction
    | some pr =>
      rcases pr with ⟨ins, lr⟩
      cases ins <;> rw [hd] at hr <;> try contradiction
      exact ⟨lr, rfl⟩
  rcases hret_dec with ⟨lret, hret⟩
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
  -- Flat O(1)-size scalar definitions for all intermediate values (zero exponential AST duplication!)
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
  -- Bounds for `b2n (decide (... ≥ W64)) = ... / W64`:
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
  -- Step-by-step execution using flat O(1) state records `k1..k20`
  rcases step_checkAt code s (hrip.trans hp0.symm) hnh hnf u1.2 with ⟨l0, hl0, hs0⟩
  let g1 := gprUpd s.gpr .rcx 0
  let k1 : X86State := { s with rip := c.p1, cf := false, of_ := false, zf := true, gpr := g1 }
  have hk1 : step code s = k1 := hs0.trans (exec_xorZero32 (by rw [hrip, ← hp0, hl0]))

  rcases step_checkAt code k1 rfl hnh hnf u2.2 with ⟨l1, hl1, hs1⟩
  let g2 := gprUpd g1 .rax 0
  let k2 : X86State := { k1 with rip := c.p2, gpr := g2 }
  have hk2 : step code k1 = k2 := hs1.trans (exec_xorZero32 hl1)

  rcases step_checkAt code k2 rfl hnh hnf u3.2 with ⟨l2, hl2, hs2⟩
  let g3 := gprUpd (gprUpd g2 .r8 lo0) .r9 hi0
  let l_3 := s.leak ++ [.load64 rsi]
  let k3 : X86State := { k2 with rip := c.p3, gpr := g3, leak := l_3 }
  have hk3 : step code k2 = k3 :=
    hs2.trans (exec_mulxMem (by decide) hl2 rfl (by change (rsi + 0) % W64 = rsi; rw [Nat.add_zero, ms0]) rfl)

  rcases step_checkAt code k3 rfl hnh hnf u4.2 with ⟨l3, hl3, hs3⟩
  let g4 := gprUpd g3 .r8 out0
  let l_4 := l_3 ++ [.load64 rdi]
  let k4 : X86State := { k3 with rip := c.p4, cf := decide (sum0 ≥ W64), gpr := g4, leak := l_4 }
  have hk4 : step code k3 = k4 :=
    hs3.trans (exec_adcxMem hl3 (by change lo0 % W64 = lo0; exact Nat.mod_eq_of_lt hlo0)
      (by change (rdi + 0) % W64 = rdi; rw [Nat.add_zero, md0]) rfl rfl)

  rcases step_checkAt code k4 rfl hnh hnf u5.2 with ⟨l4, hl4, hs4⟩
  let m5 := mem64Upd s.mem64 rdi out0
  let l_5 := l_4 ++ [.store64 rdi]
  let k5 : X86State := { k4 with rip := c.p5, mem64 := m5, leak := l_5 }
  have hk5 : step code k4 = k5 :=
    hs4.trans (exec_movStore64 hl4 (by change (rdi + 0) % W64 = rdi; rw [Nat.add_zero, md0])
      (by change out0 % W64 = out0; exact Nat.mod_eq_of_lt hout0_lt))

  rcases step_checkAt code k5 rfl hnh hnf u6.2 with ⟨l5, hl5, hs5⟩
  let g6 := gprUpd (gprUpd g4 .r8 lo1) .r10 hi1
  let l_6 := l_5 ++ [.load64 (rsi + 8)]
  let k6 : X86State := { k5 with rip := c.p6, gpr := g6, leak := l_6 }
  have hk6 : step code k5 = k6 :=
    hs5.trans (exec_mulxMem (by decide) hl5 rfl ms1
      (by unfold readMem64; dsimp [k5, m5]; rw [mem64Upd_ne (by omega)]; rfl))

  rcases step_checkAt code k6 rfl hnh hnf u7.2 with ⟨l6, hl6, hs6⟩
  let g7 := gprUpd g6 .r9 r9_1
  let k7 : X86State := { k6 with rip := c.p7, cf := decide (u1v ≥ W64), gpr := g7 }
  have hk7 : step code k6 = k7 :=
    hs6.trans (exec_adcxReg hl6 (by change hi0 % W64 = hi0; exact Nat.mod_eq_of_lt hhi0)
      (by change lo1 % W64 = lo1; exact Nat.mod_eq_of_lt hlo1) hcf1_b)

  rcases step_checkAt code k7 rfl hnh hnf u8.2 with ⟨l7, hl7, hs7⟩
  let g8 := gprUpd g7 .r9 out1
  let l_8 := l_6 ++ [.load64 (rdi + 8)]
  let k8 : X86State := { k7 with rip := c.p8, of_ := decide (v1 ≥ W64), gpr := g8, leak := l_8 }
  have hk8 : step code k7 = k8 :=
    hs7.trans (exec_adoxMem hl7 (by change r9_1 % W64 = r9_1; exact Nat.mod_eq_of_lt hr9_lt) md1
      (by unfold readMem64; dsimp [k7, k6, k5, m5]; rw [mem64Upd_ne (by omega)]; rfl) rfl)

  rcases step_checkAt code k8 rfl hnh hnf u9.2 with ⟨l8, hl8, hs8⟩
  let m9 := mem64Upd m5 (rdi + 8) out1
  let l_9 := l_8 ++ [.store64 (rdi + 8)]
  let k9 : X86State := { k8 with rip := c.p9, mem64 := m9, leak := l_9 }
  have hk9 : step code k8 = k9 :=
    hs8.trans (exec_movStore64 hl8 md1 (by change out1 % W64 = out1; exact Nat.mod_eq_of_lt hout1_lt))

  rcases step_checkAt code k9 rfl hnh hnf u10.2 with ⟨l9, hl9, hs9⟩
  let g10 := gprUpd (gprUpd g8 .r8 lo2) .r11 hi2
  let l_10 := l_9 ++ [.load64 (rsi + 16)]
  let k10 : X86State := { k9 with rip := c.p10, gpr := g10, leak := l_10 }
  have hk10 : step code k9 = k10 :=
    hs9.trans (exec_mulxMem (by decide) hl9 rfl ms2
      (by unfold readMem64; dsimp [k9, m9, m5]; rw [mem64Upd_ne (by omega), mem64Upd_ne (by omega)]; rfl))

  rcases step_checkAt code k10 rfl hnh hnf u11.2 with ⟨l10, hl10, hs10⟩
  let g11 := gprUpd g10 .r10 r10_2
  let k11 : X86State := { k10 with rip := c.p11, cf := decide (u2v ≥ W64), gpr := g11 }
  have hk11 : step code k10 = k11 :=
    hs10.trans (exec_adcxReg hl10 (by change hi1 % W64 = hi1; exact Nat.mod_eq_of_lt hhi1)
      (by change lo2 % W64 = lo2; exact Nat.mod_eq_of_lt hlo2) hcf2_b)

  rcases step_checkAt code k11 rfl hnh hnf u12.2 with ⟨l11, hl11, hs11⟩
  let g12 := gprUpd g11 .r10 out2
  let l_12 := l_10 ++ [.load64 (rdi + 16)]
  let k12 : X86State := { k11 with rip := c.p12, of_ := decide (v2 ≥ W64), gpr := g12, leak := l_12 }
  have hk12 : step code k11 = k12 :=
    hs11.trans (exec_adoxMem hl11 (by change r10_2 % W64 = r10_2; exact Nat.mod_eq_of_lt hr10_lt) md2
      (by unfold readMem64; dsimp [k11, k10, k9, m9, m5]; rw [mem64Upd_ne (by omega), mem64Upd_ne (by omega)]; rfl) hof2_b)

  rcases step_checkAt code k12 rfl hnh hnf u13.2 with ⟨l12, hl12, hs12⟩
  let m13 := mem64Upd m9 (rdi + 16) out2
  let l_13 := l_12 ++ [.store64 (rdi + 16)]
  let k13 : X86State := { k12 with rip := c.p13, mem64 := m13, leak := l_13 }
  have hk13 : step code k12 = k13 :=
    hs12.trans (exec_movStore64 hl12 md2 (by change out2 % W64 = out2; exact Nat.mod_eq_of_lt hout2_lt))

  rcases step_checkAt code k13 rfl hnh hnf u14.2 with ⟨l13, hl13, hs13⟩
  let g14 := gprUpd (gprUpd g12 .r8 lo3) .r9 hi3
  let l_14 := l_13 ++ [.load64 (rsi + 24)]
  let k14 : X86State := { k13 with rip := c.p14, gpr := g14, leak := l_14 }
  have hk14 : step code k13 = k14 :=
    hs13.trans (exec_mulxMem (by decide) hl13 rfl ms3
      (by unfold readMem64; dsimp [k13, m13, m9, m5]; rw [mem64Upd_ne (by omega), mem64Upd_ne (by omega), mem64Upd_ne (by omega)]; rfl))

  rcases step_checkAt code k14 rfl hnh hnf u15.2 with ⟨l14, hl14, hs14⟩
  let g15 := gprUpd g14 .r11 r11_3
  let k15 : X86State := { k14 with rip := c.p15, cf := decide (u3v ≥ W64), gpr := g15 }
  have hk15 : step code k14 = k15 :=
    hs14.trans (exec_adcxReg hl14 (by change hi2 % W64 = hi2; exact Nat.mod_eq_of_lt hhi2)
      (by change lo3 % W64 = lo3; exact Nat.mod_eq_of_lt hlo3) hcf3_b)

  rcases step_checkAt code k15 rfl hnh hnf u16.2 with ⟨l15, hl15, hs15⟩
  let g16 := gprUpd g15 .r11 out3
  let l_16 := l_14 ++ [.load64 (rdi + 24)]
  let k16 : X86State := { k15 with rip := c.p16, of_ := decide (v3 ≥ W64), gpr := g16, leak := l_16 }
  have hk16 : step code k15 = k16 :=
    hs15.trans (exec_adoxMem hl15 (by change r11_3 % W64 = r11_3; exact Nat.mod_eq_of_lt hr11_lt) md3
      (by unfold readMem64; dsimp [k15, k14, k13, m13, m9, m5]; rw [mem64Upd_ne (by omega), mem64Upd_ne (by omega), mem64Upd_ne (by omega)]; rfl) hof3_b)

  rcases step_checkAt code k16 rfl hnh hnf u17.2 with ⟨l16, hl16, hs16⟩
  let m17 := mem64Upd m13 (rdi + 24) out3
  let l_17 := l_16 ++ [.store64 (rdi + 24)]
  let k17 : X86State := { k16 with rip := c.p17, mem64 := m17, leak := l_17 }
  have hk17 : step code k16 = k17 :=
    hs16.trans (exec_movStore64 hl16 md3 (by change out3 % W64 = out3; exact Nat.mod_eq_of_lt hout3_lt))

  rcases step_checkAt code k17 rfl hnh hnf u18.2 with ⟨l17, hl17, hs17⟩
  have hu4_lt : u4v < W64 := by
    have hz : u4v / W64 = 0 := hcomb.2.1
    have h1 : u4v < 1 * W64 := (Nat.div_lt_iff_lt_mul (by decide : 0 < W64)).mp (by rw [hz]; decide)
    omega
  let g18 := gprUpd g16 .rax rax1
  let k18 : X86State := { k17 with rip := c.p18, cf := false, gpr := g18 }
  have hk18 : step code k17 = k18 := by
    refine hs17.trans ((exec_adcxReg hl17 (x := 0) (y := hi3) (c := cf4) rfl
      (by change hi3 % W64 = hi3; exact Nat.mod_eq_of_lt hhi3) hcf4_b).trans ?_)
    have e1 : 0 + hi3 + cf4 = u4v := by dsimp [u4v]; omega
    have e2 : decide (0 + hi3 + cf4 ≥ W64) = false := by
      rw [e1]; exact decide_eq_false (Nat.not_le_of_lt hu4_lt)
    rw [e2, e1]

  rcases step_checkAt code k18 rfl hnh hnf u19.2 with ⟨l18, hl18, hs18⟩
  have hv4_lt : v4 < W64 := by
    have hz : v4 / W64 = 0 := hcomb.2.2
    have h1 : v4 < 1 * W64 := (Nat.div_lt_iff_lt_mul (by decide : 0 < W64)).mp (by rw [hz]; decide)
    omega
  let g19 := gprUpd g18 .rax out4
  let k19 : X86State := { k18 with rip := c.p19, of_ := false, gpr := g19 }
  have hk19 : step code k18 = k19 := by
    have hrax1_lt : rax1 < W64 := Nat.mod_lt _ (by decide)
    refine hs18.trans ((exec_adoxReg hl18 (x := rax1) (y := 0) (c := of4)
      (by change rax1 % W64 = rax1; exact Nat.mod_eq_of_lt hrax1_lt) rfl hof4_b).trans ?_)
    have e1 : rax1 + 0 + of4 = v4 := rfl
    have e2 : decide (rax1 + 0 + of4 ≥ W64) = false := by
      rw [e1]; exact decide_eq_false (Nat.not_le_of_lt hv4_lt)
    rw [e2, e1]

  let k20 : X86State := { k19 with halted := true }
  have hk20 : step code k19 = k20 :=
    (@step_of_decode code k19 .ret lret hnh hnf hret).trans (exec_ret_clean hymm)

  have hrun20 : run code 20 s = k20 := by
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
  have hrax_f : k20.gpr .rax = out4 := rfl
  have hrsp_f : k20.gpr .rsp = s.gpr .rsp := rfl
  have hrbx_f : k20.gpr .rbx = s.gpr .rbx := rfl
  rw [hm0, hm1, hm2, hm3, hrax_f]
  exact ⟨rfl, hnf, rfl, rfl, hrsp_f, hrbx_f, hcomb.1⟩

-- ============================================================================
-- 2. Certificate Checker for 2x-Unrolled AVX2 `vpmaddubsw` + `vpmaddwd` Loop
-- ============================================================================

structure SimdDotUnroll2Cert where
  (p0 p1 p2 p3 p4 p5 p6 p7 : Nat)
  (p8 p9 p10 p11 p12 p13 p14 p15 p16 p17 p18 p19 p20 : Nat)
  (p21 p22 p23 p24 p25 p26 p27 p28 p29 p30 : Nat)

def checkSimdDotUnroll2Cert (code : List UInt8) (c : SimdDotUnroll2Cert) : Bool :=
  decide (c.p0 = 0) &&
  checkAt code c.p0  (.vpxorZero256 .ymm0)               c.p1  &&
  checkAt code c.p1  (.vpxorZero256 .ymm1)               c.p2  &&
  checkAt code c.p2  (.testSelf64 .rdx)                  c.p3  &&
  checkAt code c.p3  (.jeTarget c.p21)                   c.p4  &&
  checkAt code c.p4  (.vpcmpeqdAll1 .ymm2)               c.p5  &&
  checkAt code c.p5  (.vpsrlwImm256 .ymm2 .ymm2 15)      c.p6  &&
  checkAt code c.p6  (.shlImm64 .rdx 6)                  c.p7  &&
  checkAt code c.p7  (.xorZero32 .rcx)                   c.p8  &&
  checkAt code c.p8  (.vmovdquLd256 .ymm3 .rdi .rcx 0)   c.p9  &&
  checkAt code c.p9  (.vmovdquLd256 .ymm4 .rsi .rcx 0)   c.p10 &&
  checkAt code c.p10 (.vpmaddubsw .ymm3 .ymm3 .ymm4)     c.p11 &&
  checkAt code c.p11 (.vpmaddwd .ymm3 .ymm3 .ymm2)       c.p12 &&
  checkAt code c.p12 (.vpaddd256 .ymm0 .ymm0 .ymm3)      c.p13 &&
  checkAt code c.p13 (.vmovdquLd256 .ymm5 .rdi .rcx 32)  c.p14 &&
  checkAt code c.p14 (.vmovdquLd256 .ymm6 .rsi .rcx 32)  c.p15 &&
  checkAt code c.p15 (.vpmaddubsw .ymm5 .ymm5 .ymm6)     c.p16 &&
  checkAt code c.p16 (.vpmaddwd .ymm5 .ymm5 .ymm2)       c.p17 &&
  checkAt code c.p17 (.vpaddd256 .ymm1 .ymm1 .ymm5)      c.p18 &&
  checkAt code c.p18 (.addImm64 .rcx 64)                 c.p19 &&
  checkAt code c.p19 (.cmpReg64 .rcx .rdx)               c.p20 &&
  checkAt code c.p20 (.jbTarget c.p8)                    c.p21 &&
  checkAt code c.p21 (.vpaddd256 .ymm0 .ymm0 .ymm1)      c.p22 &&
  checkAt code c.p22 (.vextracti128 .ymm1 .ymm0 1)       c.p23 &&
  checkAt code c.p23 (.vpaddd128 .ymm0 .ymm0 .ymm1)      c.p24 &&
  checkAt code c.p24 (.vpshufd128 .ymm1 .ymm0 0x4e)      c.p25 &&
  checkAt code c.p25 (.vpaddd128 .ymm0 .ymm0 .ymm1)      c.p26 &&
  checkAt code c.p26 (.vpshufd128 .ymm1 .ymm0 0xb1)      c.p27 &&
  checkAt code c.p27 (.vpaddd128 .ymm0 .ymm0 .ymm1)      c.p28 &&
  checkAt code c.p28 (.vmovdToGpr32 .rax .ymm0)          c.p29 &&
  checkAt code c.p29 .vzeroupper                         c.p30 &&
  match decodeX86At code c.p30 with
  | some (.ret, _) => true
  | _ => false

private def DotLoopInv (s0 : X86State) (loopPc blocks k : Nat) (st : X86State) : Prop :=
  st.rip = loopPc ∧
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

theorem checkSimdDotUnroll2Cert_sound {code : List UInt8} {c : SimdDotUnroll2Cert} (s : X86State)
    (hcert : checkSimdDotUnroll2Cert code c = true)
    (hrip : s.rip = 0) (hnh : s.halted = false) (hnf : s.fault = false)
    (hblk : 64 * (s.gpr .rdx % W64) < W64) :
    let blocks := s.gpr .rdx % W64
    let sf := run code (18 + 13 * blocks) s
    sf.halted = true ∧
    sf.fault = false ∧
    sf.ymmDirty = false ∧
    sf.gpr .rsp = s.gpr .rsp ∧
    sf.mem64 = s.mem64 ∧
    sf.mem8 = s.mem8 ∧
    sf.gpr .rax = dotBlocks64Spec s.mem8 (s.gpr .rdi) (s.gpr .rsi) blocks := by
  unfold checkSimdDotUnroll2Cert at hcert
  have u31 := Bool.and_eq_true_iff.mp hcert
  have u30 := Bool.and_eq_true_iff.mp u31.1
  have u29 := Bool.and_eq_true_iff.mp u30.1
  have u28 := Bool.and_eq_true_iff.mp u29.1
  have u27 := Bool.and_eq_true_iff.mp u28.1
  have u26 := Bool.and_eq_true_iff.mp u27.1
  have u25 := Bool.and_eq_true_iff.mp u26.1
  have u24 := Bool.and_eq_true_iff.mp u25.1
  have u23 := Bool.and_eq_true_iff.mp u24.1
  have u22 := Bool.and_eq_true_iff.mp u23.1
  have u21 := Bool.and_eq_true_iff.mp u22.1
  have u20 := Bool.and_eq_true_iff.mp u21.1
  have u19 := Bool.and_eq_true_iff.mp u20.1
  have u18 := Bool.and_eq_true_iff.mp u19.1
  have u17 := Bool.and_eq_true_iff.mp u18.1
  have u16 := Bool.and_eq_true_iff.mp u17.1
  have u15 := Bool.and_eq_true_iff.mp u16.1
  have u14 := Bool.and_eq_true_iff.mp u15.1
  have u13 := Bool.and_eq_true_iff.mp u14.1
  have u12 := Bool.and_eq_true_iff.mp u13.1
  have u11 := Bool.and_eq_true_iff.mp u12.1
  have u10 := Bool.and_eq_true_iff.mp u11.1
  have u9  := Bool.and_eq_true_iff.mp u10.1
  have u8  := Bool.and_eq_true_iff.mp u9.1
  have u7  := Bool.and_eq_true_iff.mp u8.1
  have u6  := Bool.and_eq_true_iff.mp u7.1
  have u5  := Bool.and_eq_true_iff.mp u6.1
  have u4  := Bool.and_eq_true_iff.mp u5.1
  have u3  := Bool.and_eq_true_iff.mp u4.1
  have u2  := Bool.and_eq_true_iff.mp u3.1
  have u1  := Bool.and_eq_true_iff.mp u2.1
  have hp0 : c.p0 = 0 := of_decide_eq_true u1.1
  have hret_dec : ∃ lret, decodeX86At code c.p30 = some (.ret, lret) := by
    have hr := u31.2
    cases hd : decodeX86At code c.p30 with
    | none => rw [hd] at hr; contradiction
    | some pr =>
      rcases pr with ⟨ins, lr⟩
      cases ins <;> rw [hd] at hr <;> try contradiction
      exact ⟨lr, rfl⟩
  rcases hret_dec with ⟨lret, hret⟩
  -- Shared 10-step epilogue lemma from `c.p21` using flat O(1) intermediate states
  have h_epilog : ∀ (se : X86State) (target : Nat),
      se.rip = c.p21 → se.halted = false → se.fault = false →
      se.gpr .rsp = s.gpr .rsp → se.mem64 = s.mem64 → se.mem8 = s.mem8 →
      (ymmSum8Mod32 (se.ymm .ymm0) + ymmSum8Mod32 (se.ymm .ymm1)) % M32 = target →
      let sf := run code 10 se
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
    rcases step_checkAt code se herip henh henf u22.2 with ⟨le0, hle0, es0⟩
    let y1 := ymmUpd se.ymm .ymm0 v256
    let e1 : X86State := { se with rip := c.p22, ymmDirty := true, ymm := y1 }
    have he1 : step code se = e1 := by rw [es0]; dsimp [execInsn, e1, y1]; rw [herip, hle0]
    rcases step_checkAt code e1 rfl henh henf u23.2 with ⟨le1, hle1, es1⟩
    let y2 := ymmUpd y1 .ymm1 vhi
    let e2 : X86State := { e1 with rip := c.p23, ymm := y2 }
    have he2 : step code e1 = e2 := by rw [es1]; dsimp [execInsn, e2, e1, y2, y1, ymmUpd]; rw [hle1]
    rcases step_checkAt code e2 rfl henh henf u24.2 with ⟨le2, hle2, es2⟩
    let y3 := ymmUpd y2 .ymm0 v128
    let e3 : X86State := { e2 with rip := c.p24, ymm := y3 }
    have he3 : step code e2 = e3 := by rw [es2]; dsimp [execInsn, e3, e2, y3, y2, y1, ymmUpd]; rw [hle2]
    rcases step_checkAt code e3 rfl henh henf u25.2 with ⟨le3, hle3, es3⟩
    let y4 := ymmUpd y3 .ymm1 vs1
    let e4 : X86State := { e3 with rip := c.p25, ymm := y4 }
    have he4 : step code e3 = e4 := by rw [es3]; dsimp [execInsn, e4, e3, y4, y3, ymmUpd]; rw [hle3]
    rcases step_checkAt code e4 rfl henh henf u26.2 with ⟨le4, hle4, es4⟩
    let y5 := ymmUpd y4 .ymm0 v64
    let e5 : X86State := { e4 with rip := c.p26, ymm := y5 }
    have he5 : step code e4 = e5 := by rw [es4]; dsimp [execInsn, e5, e4, y5, y4, y3, ymmUpd]; rw [hle4]
    rcases step_checkAt code e5 rfl henh henf u27.2 with ⟨le5, hle5, es5⟩
    let y6 := ymmUpd y5 .ymm1 vs2
    let e6 : X86State := { e5 with rip := c.p27, ymm := y6 }
    have he6 : step code e5 = e6 := by rw [es5]; dsimp [execInsn, e6, e5, y6, y5, ymmUpd]; rw [hle5]
    rcases step_checkAt code e6 rfl henh henf u28.2 with ⟨le6, hle6, es6⟩
    let y7 := ymmUpd y6 .ymm0 v32
    let e7 : X86State := { e6 with rip := c.p28, ymm := y7 }
    have he7 : step code e6 = e7 := by rw [es6]; dsimp [execInsn, e7, e6, y7, y6, y5, ymmUpd]; rw [hle6]
    rcases step_checkAt code e7 rfl henh henf u29.2 with ⟨le7, hle7, es7⟩
    let e8 : X86State := { e7 with rip := c.p29, gpr := gprUpd se.gpr .rax (v32.d0 % M32) }
    have he8 : step code e7 = e8 := by rw [es7]; dsimp [execInsn, e8, e7, e6, e5, e4, e3, e2, e1, y7, ymmUpd]; rw [hle7]
    rcases step_checkAt code e8 rfl henh henf u30.2 with ⟨le8, hle8, es8⟩
    let e9 : X86State := { e8 with rip := c.p30, ymmDirty := false, ymm := zeroUpperAll y7 }
    have he9 : step code e8 = e9 := by rw [es8]; dsimp [execInsn, e9, e8]; rw [hle8]
    let e10 : X86State := { e9 with halted := true }
    have he10 : step code e9 = e10 :=
      (@step_of_decode code e9 .ret lret henh henf hret).trans (exec_ret_clean rfl)
    have hrun10 : run code 10 se = e10 := by
      rw [run_succ, he1, run_succ, he2, run_succ, he3, run_succ, he4, run_succ, he5,
          run_succ, he6, run_succ, he7, run_succ, he8, run_succ, he9, run_succ, he10, run_zero]
    dsimp only; rw [hrun10]
    have hrax : e10.gpr .rax = target := by
      change v32.d0 % M32 = target
      have hred := horizontal_reduce_256 v256
      dsimp only at hred
      rw [hred, ymmSum8_vpaddd256, hesum]
    exact ⟨rfl, henf, rfl, hersp, hem64, hem8, hrax⟩
  -- Prologue 4 steps (`p0..p3`)
  rcases step_checkAt code s (hrip.trans hp0.symm) hnh hnf u1.2 with ⟨lp0, hlp0, ps0⟩
  let q1 : X86State := { s with rip := c.p1, ymmDirty := true, ymm := ymmUpd s.ymm .ymm0 ymmZero }
  have hq1 : step code s = q1 := by rw [ps0]; dsimp [execInsn, q1]; rw [hrip, ← hp0, hlp0]
  rcases step_checkAt code q1 rfl hnh hnf u2.2 with ⟨lp1, hlp1, ps1⟩
  let q2 : X86State := { q1 with rip := c.p2, ymm := ymmUpd q1.ymm .ymm1 ymmZero }
  have hq2 : step code q1 = q2 := by rw [ps1]; dsimp [execInsn, q2, q1]; rw [hlp1]
  rcases step_checkAt code q2 rfl hnh hnf u3.2 with ⟨lp2, hlp2, ps2⟩
  let q3 : X86State := { q2 with rip := c.p3, cf := false, of_ := false, zf := decide (s.gpr .rdx % W64 = 0) }
  have hq3 : step code q2 = q3 := by rw [ps2]; dsimp [execInsn, q3, q2, q1]; rw [hlp2]
  rcases step_checkAt code q3 rfl hnh hnf u4.2 with ⟨lp3, hlp3, ps3⟩
  let q4 : X86State := { q3 with rip := if q3.zf then c.p21 else c.p4, leak := s.leak ++ [.branch q3.zf c.p21] }
  have hq4 : step code q3 = q4 := by rw [ps3]; dsimp [execInsn, q4, q3, q2, q1]; rw [hlp3]
  have hrun4 : run code 4 s = q4 := by
    rw [run_succ, hq1, run_succ, hq2, run_succ, hq3, run_succ, hq4, run_zero]
  dsimp only
  cases hblocks : s.gpr .rdx % W64 with
  | zero =>
    have hzf : q3.zf = true := by dsimp [q3]; rw [hblocks]; rfl
    have hq4_rip : q4.rip = c.p21 := by dsimp [q4]; rw [hzf]; rfl
    have hep := h_epilog q4 0 hq4_rip hnh hnf rfl rfl rfl (by dsimp [q4, q3, q2, q1, ymmUpd]; rfl)
    dsimp only at hep
    have hsplit : (18 : Nat) = 4 + (10 + 4) := rfl
    rw [Nat.mul_zero, Nat.add_zero, hsplit, run_add code 4 (10 + 4) s, hrun4,
        run_add code 10 4 q4, run_halted code 4 hep.1]
    exact hep
  | succ m =>
    have hzf : q3.zf = false := by
      dsimp [q3]; rw [hblocks]; exact decide_eq_false (Nat.succ_ne_zero m)
    have hq4_rip : q4.rip = c.p4 := by dsimp [q4]; rw [hzf]; rfl
    rcases step_checkAt code q4 hq4_rip hnh hnf u5.2 with ⟨lp4, hlp4, ps4⟩
    let q5 : X86State := { q4 with rip := c.p5, ymmDirty := true, ymm := ymmUpd q4.ymm .ymm2 ymmAllOnes }
    have hq5 : step code q4 = q5 := by rw [ps4]; dsimp [execInsn, q5]; rw [hq4_rip, hlp4]
    rcases step_checkAt code q5 rfl hnh hnf u6.2 with ⟨lp5, hlp5, ps5⟩
    let q6 : X86State := { q5 with rip := c.p6, ymm := ymmUpd q5.ymm .ymm2 ymmOnes16 }
    have hq6 : step code q5 = q6 := by rw [ps5]; dsimp [execInsn, q6, q5, ymmUpd]; rw [hlp5]; rfl
    rcases step_checkAt code q6 rfl hnh hnf u7.2 with ⟨lp6, hlp6, ps6⟩
    rw [hblocks] at hblk
    let q7 : X86State := { q6 with rip := c.p7, gpr := gprUpd s.gpr .rdx (64 * (m + 1)) }
    have hq7 : step code q6 = q7 := by
      rw [ps6]; dsimp [execInsn, q7, q6, q5, q4, q3, q2, q1]
      have heq : (s.gpr .rdx % W64 * 64) % W64 = 64 * (m + 1) := by
        rw [hblocks, Nat.mul_comm, Nat.mod_eq_of_lt hblk]
      rw [hlp6, heq]
    rcases step_checkAt code q7 rfl hnh hnf u8.2 with ⟨lp7, hlp7, ps7⟩
    let q8 : X86State := { q7 with rip := c.p8, cf := false, of_ := false, zf := true, gpr := gprUpd q7.gpr .rcx 0 }
    have hq8 : step code q7 = q8 := by rw [ps7]; dsimp [execInsn, q8, q7]; rw [hlp7]
    have hrun8 : run code 8 s = q8 := by
      have e8 : (8 : Nat) = 4 + 4 := rfl
      rw [e8, run_add code 4 4 s, hrun4, run_succ, hq5, run_succ, hq6, run_succ, hq7, run_succ, hq8, run_zero]
    have hinv0 : DotLoopInv s c.p8 (m + 1) 0 q8 := by
      refine ⟨rfl, hnh, hnf, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, ?_⟩
      dsimp [q8, q7, q6, q5, q4, q3, q2, q1, ymmUpd]; rfl
    -- 13-step single-iteration lemma using flat O(1) state records
    have h_iter : ∀ {k : Nat} {st : X86State},
        k < m + 1 → DotLoopInv s c.p8 (m + 1) k st →
        let st' := run code 13 st
        st'.halted = false ∧ st'.fault = false ∧
        st'.gpr .rdi = s.gpr .rdi ∧ st'.gpr .rsi = s.gpr .rsi ∧ st'.gpr .rsp = s.gpr .rsp ∧
        st'.gpr .rdx = 64 * (m + 1) ∧ st'.gpr .rcx = 64 * (k + 1) ∧
        st'.mem64 = s.mem64 ∧ st'.mem8 = s.mem8 ∧ st'.ymm .ymm2 = ymmOnes16 ∧
        (ymmSum8Mod32 (st'.ymm .ymm0) + ymmSum8Mod32 (st'.ymm .ymm1)) % M32 =
          dotBlocks64Spec s.mem8 (s.gpr .rdi) (s.gpr .rsi) (k + 1) ∧
        st'.rip = (if k + 1 < m + 1 then c.p8 else c.p21) := by
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

      rcases step_checkAt code st hrip_k hnh_k hnf_k u9.2 with ⟨lb0, hlb0, bs0⟩
      let y_1 := ymmUpd st.ymm .ymm3 vu0
      let lk1 := st.leak ++ [.load256 ((rdi + 64 * k) % W64)]
      let b1 : X86State := { st with rip := c.p9, ymmDirty := true, ymm := y_1, leak := lk1 }
      have hb1 : step code st = b1 :=
        bs0.trans (exec_vmovdquLd256 (by rw [hrip_k, hlb0])
          (by rw [hrdi_k, hrcx_k, Nat.add_zero]) hm8_k)

      rcases step_checkAt code b1 rfl hnh_k hnf_k u10.2 with ⟨lb1, hlb1, bs1⟩
      let y_2 := ymmUpd y_1 .ymm4 vs0
      let lk2 := lk1 ++ [.load256 ((rsi + 64 * k) % W64)]
      let b2 : X86State := { b1 with rip := c.p10, ymm := y_2, leak := lk2 }
      have hb2 : step code b1 = b2 :=
        bs1.trans (exec_vmovdquLd256 hlb1
          (by change (st.gpr .rsi + st.gpr .rcx + 0) % W64 = _; rw [hrsi_k, hrcx_k, Nat.add_zero]) hm8_k)

      rcases step_checkAt code b2 rfl hnh_k hnf_k u11.2 with ⟨lb2, hlb2, bs2⟩
      let y_3 := ymmUpd y_2 .ymm3 vp0
      let b3 : X86State := { b2 with rip := c.p11, ymm := y_3 }
      have hb3 : step code b2 = b3 := by rw [bs2]; dsimp [execInsn, b3, b2, y_3, y_2, y_1, ymmUpd]; rw [hlb2]

      rcases step_checkAt code b3 rfl hnh_k hnf_k u12.2 with ⟨lb3, hlb3, bs3⟩
      let y_4 := ymmUpd y_3 .ymm3 vw0
      let b4 : X86State := { b3 with rip := c.p12, ymm := y_4 }
      have hb4 : step code b3 = b4 := by
        rw [bs3]; dsimp [execInsn, b4, b3, y_4, y_3, y_2, y_1, ymmUpd]; rw [hlb3, hymm2_k]

      rcases step_checkAt code b4 rfl hnh_k hnf_k u13.2 with ⟨lb4, hlb4, bs4⟩
      let y_5 := ymmUpd y_4 .ymm0 acc0'
      let b5 : X86State := { b4 with rip := c.p13, ymm := y_5 }
      have hb5 : step code b4 = b5 := by rw [bs4]; dsimp [execInsn, b5, b4, y_5, y_4, y_3, y_2, y_1, ymmUpd]; rw [hlb4]

      rcases step_checkAt code b5 rfl hnh_k hnf_k u14.2 with ⟨lb5, hlb5, bs5⟩
      let y_6 := ymmUpd y_5 .ymm5 vu1
      let lk6 := lk2 ++ [.load256 ((rdi + (64 * k + 32)) % W64)]
      let b6 : X86State := { b5 with rip := c.p14, ymm := y_6, leak := lk6 }
      have hb6 : step code b5 = b6 :=
        bs5.trans (exec_vmovdquLd256 hlb5
          (by change (st.gpr .rdi + st.gpr .rcx + 32) % W64 = _; rw [hrdi_k, hrcx_k, Nat.add_assoc]) hm8_k)

      rcases step_checkAt code b6 rfl hnh_k hnf_k u15.2 with ⟨lb6, hlb6, bs6⟩
      let y_7 := ymmUpd y_6 .ymm6 vs1
      let lk7 := lk6 ++ [.load256 ((rsi + (64 * k + 32)) % W64)]
      let b7 : X86State := { b6 with rip := c.p15, ymm := y_7, leak := lk7 }
      have hb7 : step code b6 = b7 :=
        bs6.trans (exec_vmovdquLd256 hlb6
          (by change (st.gpr .rsi + st.gpr .rcx + 32) % W64 = _; rw [hrsi_k, hrcx_k, Nat.add_assoc]) hm8_k)

      rcases step_checkAt code b7 rfl hnh_k hnf_k u16.2 with ⟨lb7, hlb7, bs7⟩
      let y_8 := ymmUpd y_7 .ymm5 vp1
      let b8 : X86State := { b7 with rip := c.p16, ymm := y_8 }
      have hb8 : step code b7 = b8 := by rw [bs7]; dsimp [execInsn, b8, b7, y_8, y_7, y_6, ymmUpd]; rw [hlb7]

      rcases step_checkAt code b8 rfl hnh_k hnf_k u17.2 with ⟨lb8, hlb8, bs8⟩
      let y_9 := ymmUpd y_8 .ymm5 vw1
      let b9 : X86State := { b8 with rip := c.p17, ymm := y_9 }
      have hb9 : step code b8 = b9 := by
        rw [bs8]; dsimp [execInsn, b9, b8, y_9, y_8, y_7, y_6, y_5, y_4, y_3, y_2, y_1, ymmUpd]; rw [hlb8, hymm2_k]

      rcases step_checkAt code b9 rfl hnh_k hnf_k u18.2 with ⟨lb9, hlb9, bs9⟩
      let y_10 := ymmUpd y_9 .ymm1 acc1'
      let b10 : X86State := { b9 with rip := c.p18, ymm := y_10 }
      have hb10 : step code b9 = b10 := by
        rw [bs9]; dsimp [execInsn, b10, b9, y_10, y_9, y_8, y_7, y_6, y_5, y_4, y_3, y_2, y_1, ymmUpd]; rw [hlb9]

      have hk64_lt : 64 * k < W64 := by omega
      have hk1_64_lt : 64 * (k + 1) < W64 := by omega
      rcases step_checkAt code b10 rfl hnh_k hnf_k u19.2 with ⟨lb10, hlb10, bs10⟩
      let g_11 := gprUpd st.gpr .rcx (64 * (k + 1))
      let b11 : X86State := { b10 with rip := c.p19, cf := false, zf := decide (64 * (k + 1) = 0), gpr := g_11 }
      have hb11 : step code b10 = b11 :=
        bs10.trans (exec_addImm64 hlb10
          (by change (st.gpr .rcx % W64) + 64 = 64 * (k + 1); rw [hrcx_k, Nat.mod_eq_of_lt hk64_lt]; omega)
          hk1_64_lt)

      rcases step_checkAt code b11 rfl hnh_k hnf_k u20.2 with ⟨lb11, hlb11, bs11⟩
      let b12 : X86State := { b11 with rip := c.p20, cf := decide (64 * (k + 1) < 64 * (m + 1)),
                                       zf := decide (64 * (k + 1) = 64 * (m + 1)), of_ := false }
      have hb12 : step code b11 = b12 :=
        bs11.trans (exec_cmpReg64 hlb11 (Nat.mod_eq_of_lt hk1_64_lt)
          (by change st.gpr .rdx % W64 = 64 * (m + 1); rw [hrdx_k, Nat.mod_eq_of_lt hblk]))

      rcases step_checkAt code b12 rfl hnh_k hnf_k u21.2 with ⟨lb12, hlb12, bs12⟩
      let taken := decide (64 * (k + 1) < 64 * (m + 1))
      let b13 : X86State := { b12 with rip := if taken then c.p8 else c.p21, leak := lk7 ++ [.branch taken c.p8] }
      have hb13 : step code b12 = b13 := by
        rw [bs12]; dsimp [execInsn, b13, b12, b11, b10, b9, b8, b7, taken]
        rw [hlb12]
      have hrun13 : run code 13 st = b13 := by
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
      have hrip_next : b13.rip = (if k + 1 < m + 1 then c.p8 else c.p21) := by
        change (if taken = true then c.p8 else c.p21) = (if k + 1 < m + 1 then c.p8 else c.p21)
        cases hlt : decide (k + 1 < m + 1) with
        | true =>
          have hklt := of_decide_eq_true hlt
          have hc : taken = true := decide_eq_true (by omega)
          simp only [hc, ↓reduceIte, hklt]
        | false =>
          have hknlt := of_decide_eq_false hlt
          have hc : taken = false := decide_eq_false (by omega)
          simp only [hc, Bool.false_eq_true, ↓reduceIte, hknlt]
      have hymm2_next : b13.ymm .ymm2 = ymmOnes16 := hymm2_k
      exact ⟨hnh_k, hnf_k, hrdi_k, hrsi_k, hrsp_k, hrdx_k, rfl, hm64_k, hm8_k, hymm2_next, hsum_next, hrip_next⟩
    have h_loop_m : ∀ (j : Nat), j ≤ m →
        DotLoopInv s c.p8 (m + 1) j (run code (13 * j) q8) := by
      intro j hj
      induction j with
      | zero => rw [Nat.mul_zero, run_zero]; exact hinv0
      | succ j ih =>
        have hprev := ih (Nat.le_of_succ_le hj)
        have hmul : 13 * (j + 1) = 13 * j + 13 := by omega
        rw [hmul, run_add code (13 * j) 13 q8]
        have hstep := h_iter (by omega : j < m + 1) hprev
        dsimp only at hstep
        have hj_lt : j + 1 < m + 1 := by omega
        have hrip_j : (run code 13 (run code (13 * j) q8)).rip = c.p8 := by
          rw [hstep.2.2.2.2.2.2.2.2.2.2.2]; simp [hj_lt]
        exact ⟨hrip_j, hstep.1, hstep.2.1, hstep.2.2.1, hstep.2.2.2.1, hstep.2.2.2.2.1,
               hstep.2.2.2.2.2.1, hstep.2.2.2.2.2.2.1, hstep.2.2.2.2.2.2.2.1,
               hstep.2.2.2.2.2.2.2.2.1, hstep.2.2.2.2.2.2.2.2.2.1, hstep.2.2.2.2.2.2.2.2.2.2.1⟩
    have hinv_m := h_loop_m m (Nat.le_refl m)
    have hlast := h_iter (Nat.lt_succ_self m) hinv_m
    dsimp only at hlast
    let s_exit := run code 13 (run code (13 * m) q8)
    have hexit_rip : s_exit.rip = c.p21 := by
      change (run code 13 (run code (13 * m) q8)).rip = c.p21
      rw [hlast.2.2.2.2.2.2.2.2.2.2.2]; simp
    have hep := h_epilog s_exit (dotBlocks64Spec s.mem8 (s.gpr .rdi) (s.gpr .rsi) (m + 1))
      hexit_rip hlast.1 hlast.2.1 hlast.2.2.2.2.1 hlast.2.2.2.2.2.2.2.1 hlast.2.2.2.2.2.2.2.2.1
      hlast.2.2.2.2.2.2.2.2.2.2.1
    dsimp only at hep
    have hfuel : 18 + 13 * (m + 1) = 8 + (13 * m + (13 + 10)) := by omega
    rw [hfuel, run_add code 8 _ s, hrun8, run_add code (13 * m) (13 + 10) q8,
        run_add code 13 10 (run code (13 * m) q8)]
    exact hep

-- ============================================================================
-- 3. Certificate Checker for 8-Entry Constant-Time `cmove` Linear Scan
-- ============================================================================

structure CtLinearScan8Cert where
  (p0 p1 p2 p3 p4 p5 p6 p7 p8 p9 p10 p11 p12 : Nat)
  (p13 p14 p15 p16 p17 p18 p19 p20 p21 p22 p23 p24 p25 : Nat)

def checkScanEntry (code : List UInt8) (pa pb pc pd : Nat) (k : Nat) : Bool :=
  checkAt code pa (.movLoad64 .r8 .rdi (8 * k)) pb &&
  checkAt code pb (.cmpImm64 .rsi k)            pc &&
  checkAt code pc (.cmove64 .rax .r8)           pd

def checkCtLinearScan8Cert (code : List UInt8) (c : CtLinearScan8Cert) : Bool :=
  decide (c.p0 = 0) &&
  checkAt code c.p0 (.xorZero32 .rax) c.p1 &&
  checkScanEntry code c.p1  c.p2  c.p3  c.p4  0 &&
  checkScanEntry code c.p4  c.p5  c.p6  c.p7  1 &&
  checkScanEntry code c.p7  c.p8  c.p9  c.p10 2 &&
  checkScanEntry code c.p10 c.p11 c.p12 c.p13 3 &&
  checkScanEntry code c.p13 c.p14 c.p15 c.p16 4 &&
  checkScanEntry code c.p16 c.p17 c.p18 c.p19 5 &&
  checkScanEntry code c.p19 c.p20 c.p21 c.p22 6 &&
  checkScanEntry code c.p22 c.p23 c.p24 c.p25 7 &&
  match decodeX86At code c.p25 with
  | some (.ret, _) => true
  | _ => false

private theorem step3_scanEntry (code : List UInt8) (st : X86State)
    {pa pb pc pd k : Nat}
    (hrip : st.rip = pa) (hnh : st.halted = false) (hnf : st.fault = false)
    (hacc_lt : st.gpr .rax < W64)
    (hchk : checkScanEntry code pa pb pc pd k = true) :
    let sf := run code 3 st
    sf.rip = pd ∧ sf.halted = false ∧ sf.fault = false ∧ sf.ymmDirty = st.ymmDirty ∧
    sf.gpr .rdi = st.gpr .rdi ∧ sf.gpr .rsi = st.gpr .rsi ∧ sf.gpr .rsp = st.gpr .rsp ∧
    sf.mem64 = st.mem64 ∧
    sf.gpr .rax < W64 ∧
    sf.gpr .rax = ctSelectStep st (st.gpr .rdi) (st.gpr .rsi % W64) (st.gpr .rax) k ∧
    sf.leak = st.leak ++ [.load64 ((st.gpr .rdi + 8 * k) % W64)] := by
  unfold checkScanEntry at hchk
  have u2 := Bool.and_eq_true_iff.mp hchk
  have u1 := Bool.and_eq_true_iff.mp u2.1
  let addr := (st.gpr .rdi + 8 * k) % W64
  let loaded := readMem64 st addr
  let nextAcc := ctSelectStep st (st.gpr .rdi) (st.gpr .rsi % W64) (st.gpr .rax) k
  rcases step_checkAt code st hrip hnh hnf u1.1 with ⟨l0, hl0, s0⟩
  let st1 : X86State := { st with rip := pb, gpr := gprUpd st.gpr .r8 loaded, leak := st.leak ++ [.load64 addr] }
  have hst1 : step code st = st1 := s0.trans (exec_movLoad64 (by rw [hrip, hl0]) rfl rfl)
  rcases step_checkAt code st1 rfl hnh hnf u1.2 with ⟨l1, hl1, s1⟩
  let st2 : X86State := { st1 with rip := pc, cf := decide (st.gpr .rsi % W64 < k),
                                   zf := decide (st.gpr .rsi % W64 = k), of_ := false }
  have hst2 : step code st1 = st2 := s1.trans (exec_cmpImm64 hl1 rfl)
  rcases step_checkAt code st2 rfl hnh hnf u2.2 with ⟨l2, hl2, s2⟩
  let st3 : X86State := { st2 with rip := pd, gpr := gprUpd st1.gpr .rax nextAcc }
  have hval_lt : loaded < W64 := readMem64_lt st addr
  have hst3 : step code st2 = st3 :=
    s2.trans (exec_cmove64 hl2 (by
      change (if decide (st.gpr .rsi % W64 = k) then loaded % W64 else st.gpr .rax % W64) = nextAcc
      rw [Nat.mod_eq_of_lt hval_lt, Nat.mod_eq_of_lt hacc_lt]
      dsimp [nextAcc, ctSelectStep, loaded, addr]
      cases hd : decide (st.gpr .rsi % W64 = k) with
      | true => simp [of_decide_eq_true hd]
      | false => simp [of_decide_eq_false hd]))
  have hrun3 : run code 3 st = st3 := by
    rw [run_succ, hst1, run_succ, hst2, run_succ, hst3, run_zero]
  dsimp only; rw [hrun3]
  have hrax_lt3 : nextAcc < W64 := by
    dsimp [nextAcc, ctSelectStep]; split
    · exact hval_lt
    · exact hacc_lt
  exact ⟨rfl, hnh, hnf, rfl, rfl, rfl, rfl, rfl, hrax_lt3, rfl, rfl⟩

private theorem ctSelect8_eq_lookup8 (s : X86State) (base idx : Nat) :
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

theorem checkCtLinearScan8Cert_exec {code : List UInt8} {c : CtLinearScan8Cert} (s : X86State)
    (hcert : checkCtLinearScan8Cert code c = true)
    (hrip : s.rip = 0) (hnh : s.halted = false) (hnf : s.fault = false) (hymm : s.ymmDirty = false) :
    let sf := run code 26 s
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
  unfold checkCtLinearScan8Cert at hcert
  have u10 := Bool.and_eq_true_iff.mp hcert
  have u9  := Bool.and_eq_true_iff.mp u10.1
  have u8  := Bool.and_eq_true_iff.mp u9.1
  have u7  := Bool.and_eq_true_iff.mp u8.1
  have u6  := Bool.and_eq_true_iff.mp u7.1
  have u5  := Bool.and_eq_true_iff.mp u6.1
  have u4  := Bool.and_eq_true_iff.mp u5.1
  have u3  := Bool.and_eq_true_iff.mp u4.1
  have u2  := Bool.and_eq_true_iff.mp u3.1
  have u1  := Bool.and_eq_true_iff.mp u2.1
  have hp0 : c.p0 = 0 := of_decide_eq_true u1.1
  have hret_dec : ∃ lret, decodeX86At code c.p25 = some (.ret, lret) := by
    have hr := u10.2
    cases hd : decodeX86At code c.p25 with
    | none => rw [hd] at hr; contradiction
    | some pr =>
      rcases pr with ⟨ins, lr⟩
      cases ins <;> rw [hd] at hr <;> try contradiction
      exact ⟨lr, rfl⟩
  rcases hret_dec with ⟨lret, hret⟩
  rcases step_checkAt code s (hrip.trans hp0.symm) hnh hnf u1.2 with ⟨lz, hlz, sz⟩
  let q0 : X86State := { s with rip := c.p1, cf := false, of_ := false, zf := true, gpr := gprUpd s.gpr .rax 0 }
  have hq0_step : step code s = q0 := sz.trans (exec_xorZero32 (by rw [hrip, ← hp0, hlz]))
  have hq0_lt : q0.gpr .rax < W64 := by dsimp [q0, gprUpd]; decide
  have e0 := step3_scanEntry code q0 rfl hnh hnf hq0_lt u2.2
  dsimp only at e0; let q1 := run code 3 q0
  have e1 := step3_scanEntry code q1 e0.1 e0.2.1 e0.2.2.1 e0.2.2.2.2.2.2.2.2.1 u3.2
  dsimp only at e1; let q2 := run code 3 q1
  have e2 := step3_scanEntry code q2 e1.1 e1.2.1 e1.2.2.1 e1.2.2.2.2.2.2.2.2.1 u4.2
  dsimp only at e2; let q3 := run code 3 q2
  have e3 := step3_scanEntry code q3 e2.1 e2.2.1 e2.2.2.1 e2.2.2.2.2.2.2.2.2.1 u5.2
  dsimp only at e3; let q4 := run code 3 q3
  have e4 := step3_scanEntry code q4 e3.1 e3.2.1 e3.2.2.1 e3.2.2.2.2.2.2.2.2.1 u6.2
  dsimp only at e4; let q5 := run code 3 q4
  have e5 := step3_scanEntry code q5 e4.1 e4.2.1 e4.2.2.1 e4.2.2.2.2.2.2.2.2.1 u7.2
  dsimp only at e5; let q6 := run code 3 q5
  have e6 := step3_scanEntry code q6 e5.1 e5.2.1 e5.2.2.1 e5.2.2.2.2.2.2.2.2.1 u8.2
  dsimp only at e6; let q7 := run code 3 q6
  have e7 := step3_scanEntry code q7 e6.1 e6.2.1 e6.2.2.1 e6.2.2.2.2.2.2.2.2.1 u9.2
  dsimp only at e7; let q8 := run code 3 q7
  have hs_ret : step code q8 = execInsn .ret lret q8 := by
    have hd : decodeX86At code q8.rip = some (.ret, lret) := by rw [e7.1]; exact hret
    exact step_of_decode e7.2.1 e7.2.2.1 hd
  have hrun26 : run code 26 s = execInsn .ret lret q8 := by
    rw [run_succ, hq0_step]
    have f : (25 : Nat) = 3 + (3 + (3 + (3 + (3 + (3 + (3 + (3 + 1))))))) := rfl
    rw [f, run_add code 3 _ q0, run_add code 3 _ q1, run_add code 3 _ q2, run_add code 3 _ q3,
        run_add code 3 _ q4, run_add code 3 _ q5, run_add code 3 _ q6, run_add code 3 _ q7,
        run_succ, hs_ret, run_zero]
  dsimp only; rw [hrun26]
  have hymm8 : q8.ymmDirty = false := by
    rw [e7.2.2.2.1, e6.2.2.2.1, e5.2.2.2.1, e4.2.2.2.1, e3.2.2.2.1, e2.2.2.2.1, e1.2.2.2.1, e0.2.2.2.1]
    exact hymm
  have hrsp8 : q8.gpr .rsp = s.gpr .rsp := by
    rw [e7.2.2.2.2.2.2.1, e6.2.2.2.2.2.2.1, e5.2.2.2.2.2.2.1, e4.2.2.2.2.2.2.1,
        e3.2.2.2.2.2.2.1, e2.2.2.2.2.2.2.1, e1.2.2.2.2.2.2.1, e0.2.2.2.2.2.2.1]; rfl
  have hm8 : q8.mem64 = s.mem64 := by
    rw [e7.2.2.2.2.2.2.2.1, e6.2.2.2.2.2.2.2.1, e5.2.2.2.2.2.2.2.1, e4.2.2.2.2.2.2.2.1,
        e3.2.2.2.2.2.2.2.1, e2.2.2.2.2.2.2.2.1, e1.2.2.2.2.2.2.2.1, e0.2.2.2.2.2.2.2.1]
  have d0 : q0.gpr .rdi = s.gpr .rdi := rfl
  have d1 : q1.gpr .rdi = s.gpr .rdi := e0.2.2.2.2.1.trans d0
  have d2 : q2.gpr .rdi = s.gpr .rdi := e1.2.2.2.2.1.trans d1
  have d3 : q3.gpr .rdi = s.gpr .rdi := e2.2.2.2.2.1.trans d2
  have d4 : q4.gpr .rdi = s.gpr .rdi := e3.2.2.2.2.1.trans d3
  have d5 : q5.gpr .rdi = s.gpr .rdi := e4.2.2.2.2.1.trans d4
  have d6 : q6.gpr .rdi = s.gpr .rdi := e5.2.2.2.2.1.trans d5
  have d7 : q7.gpr .rdi = s.gpr .rdi := e6.2.2.2.2.1.trans d6
  have s0_rsi : q0.gpr .rsi = s.gpr .rsi := rfl
  have s1_rsi : q1.gpr .rsi = s.gpr .rsi := e0.2.2.2.2.2.1.trans s0_rsi
  have s2_rsi : q2.gpr .rsi = s.gpr .rsi := e1.2.2.2.2.2.1.trans s1_rsi
  have s3_rsi : q3.gpr .rsi = s.gpr .rsi := e2.2.2.2.2.2.1.trans s2_rsi
  have s4_rsi : q4.gpr .rsi = s.gpr .rsi := e3.2.2.2.2.2.1.trans s3_rsi
  have s5_rsi : q5.gpr .rsi = s.gpr .rsi := e4.2.2.2.2.2.1.trans s4_rsi
  have s6_rsi : q6.gpr .rsi = s.gpr .rsi := e5.2.2.2.2.2.1.trans s5_rsi
  have s7_rsi : q7.gpr .rsi = s.gpr .rsi := e6.2.2.2.2.2.1.trans s6_rsi
  have step_mem_eq : ∀ {st : X86State} (hm : st.mem64 = s.mem64) (a i acc k : Nat),
      ctSelectStep st a i acc k = ctSelectStep s a i acc k := by
    intro st hm a i acc k; unfold ctSelectStep readMem64; rw [hm]
  have m0 : q0.mem64 = s.mem64 := rfl
  have m1 : q1.mem64 = s.mem64 := e0.2.2.2.2.2.2.2.1.trans m0
  have m2 : q2.mem64 = s.mem64 := e1.2.2.2.2.2.2.2.1.trans m1
  have m3 : q3.mem64 = s.mem64 := e2.2.2.2.2.2.2.2.1.trans m2
  have m4 : q4.mem64 = s.mem64 := e3.2.2.2.2.2.2.2.1.trans m3
  have m5 : q5.mem64 = s.mem64 := e4.2.2.2.2.2.2.2.1.trans m4
  have m6 : q6.mem64 = s.mem64 := e5.2.2.2.2.2.2.2.1.trans m5
  have m7 : q7.mem64 = s.mem64 := e6.2.2.2.2.2.2.2.1.trans m6
  have hrax8 : q8.gpr .rax = lookup8Spec s (s.gpr .rdi) (s.gpr .rsi % W64) := by
    rw [← ctSelect8_eq_lookup8]
    unfold ctSelectMirTwin
    have q0_rax : q0.gpr .rax = 0 := rfl
    rw [e7.2.2.2.2.2.2.2.2.2.1, d7, s7_rsi, step_mem_eq m7]
    rw [e6.2.2.2.2.2.2.2.2.2.1, d6, s6_rsi, step_mem_eq m6]
    rw [e5.2.2.2.2.2.2.2.2.2.1, d5, s5_rsi, step_mem_eq m5]
    rw [e4.2.2.2.2.2.2.2.2.2.1, d4, s4_rsi, step_mem_eq m4]
    rw [e3.2.2.2.2.2.2.2.2.2.1, d3, s3_rsi, step_mem_eq m3]
    rw [e2.2.2.2.2.2.2.2.2.2.1, d2, s2_rsi, step_mem_eq m2]
    rw [e1.2.2.2.2.2.2.2.2.2.1, d1, s1_rsi, step_mem_eq m1]
    rw [e0.2.2.2.2.2.2.2.2.2.1, d0, s0_rsi, q0_rax, step_mem_eq m0]
  have hleak8 : q8.leak = s.leak ++
      [ .load64 ((s.gpr .rdi + 0) % W64),  .load64 ((s.gpr .rdi + 8) % W64),
        .load64 ((s.gpr .rdi + 16) % W64), .load64 ((s.gpr .rdi + 24) % W64),
        .load64 ((s.gpr .rdi + 32) % W64), .load64 ((s.gpr .rdi + 40) % W64),
        .load64 ((s.gpr .rdi + 48) % W64), .load64 ((s.gpr .rdi + 56) % W64) ] := by
    have l0_eq : q0.leak = s.leak := rfl
    rw [e7.2.2.2.2.2.2.2.2.2.2, d7, e6.2.2.2.2.2.2.2.2.2.2, d6,
        e5.2.2.2.2.2.2.2.2.2.2, d5, e4.2.2.2.2.2.2.2.2.2.2, d4,
        e3.2.2.2.2.2.2.2.2.2.2, d3, e2.2.2.2.2.2.2.2.2.2.2, d2,
        e1.2.2.2.2.2.2.2.2.2.2, d1, e0.2.2.2.2.2.2.2.2.2.2, d0, l0_eq]
    simp [List.append_assoc]
  rw [exec_ret_clean hymm8]
  exact ⟨rfl, e7.2.2.1, hrsp8, hm8, hrax8, hleak8⟩

theorem checkCtLinearScan8Cert_2safety {code : List UInt8} {c : CtLinearScan8Cert}
    (s1 s2 : X86State)
    (hcert : checkCtLinearScan8Cert code c = true)
    (hrip1 : s1.rip = 0) (hnh1 : s1.halted = false) (hnf1 : s1.fault = false) (hymm1 : s1.ymmDirty = false)
    (hrip2 : s2.rip = 0) (hnh2 : s2.halted = false) (hnf2 : s2.fault = false) (hymm2 : s2.ymmDirty = false)
    (hpub_base : s1.gpr .rdi = s2.gpr .rdi)
    (hleak_init : s1.leak = s2.leak) :
    (run code 26 s1).leak = (run code 26 s2).leak := by
  have ex1 := checkCtLinearScan8Cert_exec s1 hcert hrip1 hnh1 hnf1 hymm1
  have ex2 := checkCtLinearScan8Cert_exec s2 hcert hrip2 hnh2 hnf2 hymm2
  dsimp only at ex1 ex2
  rw [ex1.2.2.2.2.2, ex2.2.2.2.2.2, hpub_base, hleak_init]

end UntrustedHints
