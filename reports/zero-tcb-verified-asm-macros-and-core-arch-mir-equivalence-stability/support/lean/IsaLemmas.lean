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

/-!
Shared general ISA stepping, register/memory framing, 320-bit dual-carry conservation,
and 256-bit SIMD horizontal-reduction lemmas used across all three verification regimes.
-/

namespace IsaLemmas

open AsmMirBase

theorem gprUpd_eq (f : Gpr → Nat) (r : Gpr) (v : Nat) :
    gprUpd f r v r = v := by
  unfold gprUpd; simp

theorem gprUpd_ne (f : Gpr → Nat) {r q : Gpr} (v : Nat) (h : q ≠ r) :
    gprUpd f r v q = f q := by
  unfold gprUpd; simp [h]

theorem ymmUpd_eq (f : Ymm → Ymm256) (r : Ymm) (v : Ymm256) :
    ymmUpd f r v r = v := by
  unfold ymmUpd; simp

theorem ymmUpd_ne (f : Ymm → Ymm256) {r q : Ymm} (v : Ymm256) (h : q ≠ r) :
    ymmUpd f r v q = f q := by
  unfold ymmUpd; simp [h]

theorem mem64Upd_eq {m : Nat → Nat} {a v : Nat} :
    mem64Upd m a v a = v % W64 := by
  unfold mem64Upd; simp

theorem mem64Upd_ne {m : Nat → Nat} {a q v : Nat} (h : q ≠ a) :
    mem64Upd m a v q = m q := by
  unfold mem64Upd; simp [h]

theorem readMem64_lt (s : X86State) (a : Nat) :
    readMem64 s a < W64 := by
  unfold readMem64
  exact Nat.mod_lt _ (by decide : 0 < W64)

theorem run_zero (code : List UInt8) (s : X86State) :
    run code 0 s = s := rfl

theorem run_succ (code : List UInt8) (n : Nat) (s : X86State) :
    run code (n + 1) s = run code n (step code s) := rfl

theorem run_add (code : List UInt8) :
    ∀ (m n : Nat) (s : X86State), run code (m + n) s = run code n (run code m s)
  | 0, n, s => by simp [run]
  | m + 1, n, s => by
    rw [Nat.succ_add, run_succ, run_succ, run_add code m n (step code s)]

theorem step_halted (code : List UInt8) {s : X86State} (h : s.halted = true) :
    step code s = s := by
  unfold step; rw [h]; rfl

theorem run_halted (code : List UInt8) :
    ∀ (n : Nat) {s : X86State}, s.halted = true → run code n s = s
  | 0, _, _ => rfl
  | n + 1, s, hh => by
    rw [run_succ, step_halted code hh, run_halted code n hh]

theorem step_of_decode {code : List UInt8} {s : X86State} {ins : X86Insn} {len : Nat}
    (hnh : s.halted = false) (hnf : s.fault = false)
    (hdec : decodeX86At code s.rip = some (ins, len)) :
    step code s = execInsn ins len s := by
  unfold step
  rw [hnh, hnf, hdec]
  rfl

-- ============================================================================
-- 320-bit BMI2 `mulx` + ADX (`adcx` / `adox`) Dual-Carry Arithmetic Laws
-- ============================================================================

theorem b2n_decide_ge (sum : Nat) (hsum : sum < 2 * W64) :
    b2n (decide (sum ≥ W64)) = sum / W64 := by
  unfold b2n
  cases h : decide (sum ≥ W64) with
  | true =>
    have hge : sum ≥ W64 := of_decide_eq_true h
    change 1 = sum / W64
    symm
    have hsub : sum - W64 < W64 := by unfold W64 at *; omega
    have heq : sum = W64 + (sum - W64) := by omega
    rw [heq, Nat.add_comm, Nat.add_div_right _ (by decide : 0 < W64), Nat.div_eq_of_lt hsub]
  | false =>
    have hlt : sum < W64 := Nat.lt_of_not_le (of_decide_eq_false h)
    change 0 = sum / W64
    exact (Nat.div_eq_of_lt hlt).symm

theorem mulx_hi_lt_w64 (b a : Nat) (hb : b < W64) (ha : a < W64) :
    (b * a) / W64 < W64 - 1 := by
  have h1 : b ≤ W64 - 1 := by omega
  have h2 : a ≤ W64 - 1 := by omega
  have hprod : b * a ≤ (W64 - 1) * (W64 - 1) := Nat.mul_le_mul h1 h2
  have hlt : (W64 - 1) * (W64 - 1) < (W64 - 1) * W64 := by decide
  exact (Nat.div_lt_iff_lt_mul (by decide : 0 < W64)).mpr (Nat.lt_of_le_of_lt hprod hlt)

theorem mulx_split_eq (b a : Nat) (hb : b < W64) (ha : a < W64) :
    (b * a) % W64 + W64 * (((b * a) / W64) % W64) = b * a := by
  have hhi : (b * a) / W64 < W64 :=
    Nat.lt_trans (mulx_hi_lt_w64 b a hb ha) (by decide)
  rw [Nat.mod_eq_of_lt hhi]
  exact Nat.mod_add_div (b * a) W64

theorem limb0_conservation (lo0 hi0 t0 b a0 : Nat)
    (hm0 : lo0 + W64 * hi0 = b * a0) :
    (lo0 + t0) % W64 + W64 * (hi0 + (lo0 + t0) / W64) = t0 + b * a0 := by
  have hdiv := Nat.mod_add_div (lo0 + t0) W64
  have hmul := Nat.mul_add W64 hi0 ((lo0 + t0) / W64)
  omega

theorem limb_step_conservation (prevHi lo hi t cf of_ b a : Nat)
    (hm : lo + W64 * hi = b * a) :
    ((prevHi + lo + cf) % W64 + t + of_) % W64 +
      W64 * (hi + (prevHi + lo + cf) / W64 + ((prevHi + lo + cf) % W64 + t + of_) / W64) =
      prevHi + cf + of_ + t + b * a := by
  have hu := Nat.mod_add_div (prevHi + lo + cf) W64
  have hv := Nat.mod_add_div ((prevHi + lo + cf) % W64 + t + of_) W64
  have hw : W64 * (hi + (prevHi + lo + cf) / W64 + ((prevHi + lo + cf) % W64 + t + of_) / W64) =
      W64 * hi + W64 * ((prevHi + lo + cf) / W64) + W64 * (((prevHi + lo + cf) % W64 + t + of_) / W64) := by
    rw [Nat.mul_add, Nat.mul_add]
  omega

private theorem chain4_linear
    (o0 o1 o2 o3 topSum c0 c1 c2 t0 t1 t2 t3 p0 p1 p2 p3 : Nat)
    (h0 : o0 + W64 * c0 = t0 + p0)
    (h1 : o1 + W64 * c1 = c0 + t1 + p1)
    (h2 : o2 + W64 * c2 = c1 + t2 + p2)
    (h3 : o3 + W64 * topSum = c2 + t3 + p3) :
    o0 + W64 * (o1 + W64 * (o2 + W64 * (o3 + W64 * topSum))) =
      (t0 + W64 * (t1 + W64 * (t2 + W64 * t3))) +
      (p0 + W64 * (p1 + W64 * (p2 + W64 * p3))) := by
  unfold W64 at *
  omega

private theorem val4Limbs_lt_w4 (x0 x1 x2 x3 : Nat)
    (h0 : x0 < W64) (h1 : x1 < W64) (h2 : x2 < W64) (h3 : x3 < W64) :
    val4Limbs x0 x1 x2 x3 < W64 * (W64 * (W64 * W64)) := by
  unfold val4Limbs W64 at *
  omega

private theorem b_mul_val4Limbs (b a0 a1 a2 a3 : Nat) :
    b * val4Limbs a0 a1 a2 a3 = b * a0 + W64 * (b * a1 + W64 * (b * a2 + W64 * (b * a3))) := by
  unfold val4Limbs
  rw [Nat.mul_add b a0 _, Nat.mul_left_comm b W64 _,
      Nat.mul_add b a1 _, Nat.mul_left_comm b W64 _,
      Nat.mul_add b a2 _, Nat.mul_left_comm b W64 _]

theorem mac4_combine_conservation
    (t0 t1 t2 t3 a0 a1 a2 a3 b : Nat)
    (ht0 : t0 < W64) (ht1 : t1 < W64) (ht2 : t2 < W64) (ht3 : t3 < W64)
    (ha0 : a0 < W64) (ha1 : a1 < W64) (ha2 : a2 < W64) (ha3 : a3 < W64)
    (hb : b < W64) :
    let lo0 := (b * a0) % W64; let hi0 := ((b * a0) / W64) % W64
    let lo1 := (b * a1) % W64; let hi1 := ((b * a1) / W64) % W64
    let lo2 := (b * a2) % W64; let hi2 := ((b * a2) / W64) % W64
    let lo3 := (b * a3) % W64; let hi3 := ((b * a3) / W64) % W64
    let s0 := lo0 + t0
    let out0 := s0 % W64; let cf1 := s0 / W64
    let u1 := hi0 + lo1 + cf1
    let r9 := u1 % W64; let cf2 := u1 / W64
    let v1 := r9 + t1 + 0
    let out1 := v1 % W64; let of2 := v1 / W64
    let u2 := hi1 + lo2 + cf2
    let r10 := u2 % W64; let cf3 := u2 / W64
    let v2 := r10 + t2 + of2
    let out2 := v2 % W64; let of3 := v2 / W64
    let u3 := hi2 + lo3 + cf3
    let r11 := u3 % W64; let cf4 := u3 / W64
    let v3 := r11 + t3 + of3
    let out3 := v3 % W64; let of4 := v3 / W64
    let u4 := hi3 + cf4
    let rax1 := u4 % W64; let cf5 := u4 / W64
    let v4 := rax1 + of4
    let out4 := v4 % W64; let of5 := v4 / W64
    val5Limbs out0 out1 out2 out3 out4 = mac4RefVal t0 t1 t2 t3 a0 a1 a2 a3 b ∧
    cf5 = 0 ∧ of5 = 0 := by
  intro lo0 hi0 lo1 hi1 lo2 hi2 lo3 hi3 s0 out0 cf1 u1 r9 cf2 v1 out1 of2 u2 r10 cf3 v2 out2 of3 u3 r11 cf4 v3 out3 of4 u4 rax1 cf5 v4 out4 of5
  have hm0 : lo0 + W64 * hi0 = b * a0 := mulx_split_eq b a0 hb ha0
  have hm1 : lo1 + W64 * hi1 = b * a1 := mulx_split_eq b a1 hb ha1
  have hm2 : lo2 + W64 * hi2 = b * a2 := mulx_split_eq b a2 hb ha2
  have hm3 : lo3 + W64 * hi3 = b * a3 := mulx_split_eq b a3 hb ha3
  have hc0 : out0 + W64 * (hi0 + cf1) = t0 + b * a0 :=
    limb0_conservation lo0 hi0 t0 b a0 hm0
  have hc1 : out1 + W64 * (hi1 + cf2 + of2) = (hi0 + cf1) + t1 + b * a1 :=
    limb_step_conservation hi0 lo1 hi1 t1 cf1 0 b a1 hm1
  have hc2 : out2 + W64 * (hi2 + cf3 + of3) = (hi1 + cf2 + of2) + t2 + b * a2 :=
    limb_step_conservation hi1 lo2 hi2 t2 cf2 of2 b a2 hm2
  have hc3 : out3 + W64 * (hi3 + cf4 + of4) = (hi2 + cf3 + of3) + t3 + b * a3 :=
    limb_step_conservation hi2 lo3 hi3 t3 cf3 of3 b a3 hm3
  let topSum := hi3 + cf4 + of4
  have hchain := chain4_linear out0 out1 out2 out3 topSum
    (hi0 + cf1) (hi1 + cf2 + of2) (hi2 + cf3 + of3)
    t0 t1 t2 t3 (b * a0) (b * a1) (b * a2) (b * a3) hc0 hc1 hc2 hc3
  have hval5 : val5Limbs out0 out1 out2 out3 topSum = mac4RefVal t0 t1 t2 t3 a0 a1 a2 a3 b := by
    unfold val5Limbs mac4RefVal
    rw [b_mul_val4Limbs b a0 a1 a2 a3]
    exact hchain
  let W4 := W64 * (W64 * (W64 * W64))
  have ht_lt : val4Limbs t0 t1 t2 t3 < W4 := val4Limbs_lt_w4 t0 t1 t2 t3 ht0 ht1 ht2 ht3
  have ha_lt : val4Limbs a0 a1 a2 a3 < W4 := val4Limbs_lt_w4 a0 a1 a2 a3 ha0 ha1 ha2 ha3
  have href_lt : mac4RefVal t0 t1 t2 t3 a0 a1 a2 a3 b < W64 * W4 := by
    unfold mac4RefVal
    have h1 : val4Limbs t0 t1 t2 t3 ≤ W4 - 1 := Nat.le_sub_one_of_lt ht_lt
    have h2 : b * val4Limbs a0 a1 a2 a3 ≤ (W64 - 1) * (W4 - 1) :=
      Nat.mul_le_mul (Nat.le_sub_one_of_lt hb) (Nat.le_sub_one_of_lt ha_lt)
    have h3 : (W4 - 1) + (W64 - 1) * (W4 - 1) < W64 * W4 := by dsimp [W4]; decide
    exact Nat.lt_of_le_of_lt (Nat.add_le_add h1 h2) h3
  have htop_le : topSum * W4 ≤ val5Limbs out0 out1 out2 out3 topSum := by
    unfold val5Limbs
    dsimp [W4]
    unfold W64
    omega
  have htop_lt : topSum < W64 := by
    rw [hval5] at htop_le
    exact Nat.lt_of_mul_lt_mul_right (Nat.lt_of_le_of_lt htop_le href_lt)
  have hu4_lt : u4 < W64 :=
    Nat.lt_of_le_of_lt (Nat.le_add_right (hi3 + cf4) of4) htop_lt
  have hcf5 : cf5 = 0 := Nat.div_eq_of_lt hu4_lt
  have hrax1 : rax1 = u4 := Nat.mod_eq_of_lt hu4_lt
  have hv4 : v4 = topSum := by dsimp [v4, topSum]; rw [hrax1]
  have hof5 : of5 = 0 := by dsimp [of5]; rw [hv4]; exact Nat.div_eq_of_lt htop_lt
  have hout4 : out4 = topSum := by dsimp [out4]; rw [hv4]; exact Nat.mod_eq_of_lt htop_lt
  rw [hout4]
  exact ⟨hval5, hcf5, hof5⟩

-- ============================================================================
-- 256-bit AVX2 `vpcmpeqd`/`vpsrlw`/`vpaddd` & Horizontal Reduction Laws
-- ============================================================================

theorem vpsrlw15_allOnes : vpsrlw15 ymmAllOnes = ymmOnes16 := rfl

theorem ymmSum8_zero : ymmSum8Mod32 ymmZero = 0 := rfl

private theorem step_mod_sum {p q r : Nat} (h : p % M32 = r % M32) :
    (p + q % M32) % M32 = (r + q) % M32 := by
  rw [Nat.add_mod_mod, ← Nat.mod_add_mod, h, Nat.mod_add_mod]

theorem ymmSum8_vpaddd256 (a b : Ymm256) :
    ymmSum8Mod32 (evalVpaddd256 a b) = (ymmSum8Mod32 a + ymmSum8Mod32 b) % M32 := by
  unfold ymmSum8Mod32 evalVpaddd256
  dsimp only
  have h0 : ((a.d0 + b.d0) % M32) % M32 = (a.d0 + b.d0) % M32 := Nat.mod_mod _ _
  have h7 := step_mod_sum (q := a.d7 + b.d7)
    (step_mod_sum (q := a.d6 + b.d6)
      (step_mod_sum (q := a.d5 + b.d5)
        (step_mod_sum (q := a.d4 + b.d4)
          (step_mod_sum (q := a.d3 + b.d3)
            (step_mod_sum (q := a.d2 + b.d2)
              (step_mod_sum (q := a.d1 + b.d1) h0))))))
  rw [h7, ← Nat.add_mod]
  have perm : a.d0 + b.d0 + (a.d1 + b.d1) + (a.d2 + b.d2) + (a.d3 + b.d3) +
              (a.d4 + b.d4) + (a.d5 + b.d5) + (a.d6 + b.d6) + (a.d7 + b.d7) =
              (a.d0 + a.d1 + a.d2 + a.d3 + a.d4 + a.d5 + a.d6 + a.d7) +
              (b.d0 + b.d1 + b.d2 + b.d3 + b.d4 + b.d5 + b.d6 + b.d7) := by omega
  rw [perm]

theorem horizontal_reduce_256 (v : Ymm256) :
    let sum128 := evalVpaddd128 v (evalVextracti128Hi v)
    let sum64  := evalVpaddd128 sum128 (evalVpshufd128 sum128 0x4e)
    let sum32  := evalVpaddd128 sum64  (evalVpshufd128 sum64  0xb1)
    sum32.d0 % M32 = ymmSum8Mod32 v := by
  change (((((v.d0 + v.d4) % M32 + (v.d2 + v.d6) % M32) % M32) +
           (((v.d1 + v.d5) % M32 + (v.d3 + v.d7) % M32) % M32)) % M32) % M32 =
         (v.d0 + v.d1 + v.d2 + v.d3 + v.d4 + v.d5 + v.d6 + v.d7) % M32
  simp only [Nat.mod_mod, Nat.add_mod_mod, Nat.mod_add_mod]
  have perm : v.d0 + v.d4 + (v.d2 + v.d6) + (v.d1 + v.d5 + (v.d3 + v.d7)) =
      v.d0 + v.d1 + v.d2 + v.d3 + v.d4 + v.d5 + v.d6 + v.d7 := by omega
  rw [perm]

-- ============================================================================
-- Abstract Instruction-Stepping Lemmas (Eliminate `Decidable` Motive Blowup)
-- ============================================================================

theorem exec_xorZero32 {r : Gpr} {len nextRip : Nat} {s : X86State}
    (hrip : s.rip + len = nextRip) :
    execInsn (.xorZero32 r) len s =
      { s with rip := nextRip, cf := false, of_ := false, zf := true, gpr := gprUpd s.gpr r 0 } := by
  dsimp [execInsn]; simp only [hrip]

theorem exec_mulxMem {hi lo base : Gpr} {disp len nextRip b addr mval : Nat} {s : X86State}
    (hne : hi ≠ lo) (hrip : s.rip + len = nextRip)
    (hb : s.gpr .rdx % W64 = b)
    (ha : (s.gpr base + disp) % W64 = addr)
    (hm : readMem64 s addr = mval) :
    execInsn (.mulxMem hi lo base disp) len s =
      { s with rip := nextRip,
               gpr := gprUpd (gprUpd s.gpr lo ((b * mval) % W64)) hi (((b * mval) / W64) % W64),
               leak := s.leak ++ [.load64 addr] } := by
  dsimp [execInsn]; simp only [hne, ↓reduceIte, hrip, hb, ha, hm]

theorem exec_adcxMem {dst base : Gpr} {disp len nextRip x addr mval c : Nat} {s : X86State}
    (hrip : s.rip + len = nextRip)
    (hx : s.gpr dst % W64 = x)
    (ha : (s.gpr base + disp) % W64 = addr)
    (hm : readMem64 s addr = mval)
    (hc : b2n s.cf = c) :
    execInsn (.adcxMem dst base disp) len s =
      { s with rip := nextRip,
               cf := decide (x + mval + c ≥ W64),
               gpr := gprUpd s.gpr dst ((x + mval + c) % W64),
               leak := s.leak ++ [.load64 addr] } := by
  dsimp [execInsn]; simp only [hrip, hx, ha, hm, hc]

theorem exec_adcxReg {dst src : Gpr} {len nextRip x y c : Nat} {s : X86State}
    (hrip : s.rip + len = nextRip)
    (hx : s.gpr dst % W64 = x)
    (hy : s.gpr src % W64 = y)
    (hc : b2n s.cf = c) :
    execInsn (.adcxReg dst src) len s =
      { s with rip := nextRip,
               cf := decide (x + y + c ≥ W64),
               gpr := gprUpd s.gpr dst ((x + y + c) % W64) } := by
  dsimp [execInsn]; simp only [hrip, hx, hy, hc]

theorem exec_adoxMem {dst base : Gpr} {disp len nextRip x addr mval c : Nat} {s : X86State}
    (hrip : s.rip + len = nextRip)
    (hx : s.gpr dst % W64 = x)
    (ha : (s.gpr base + disp) % W64 = addr)
    (hm : readMem64 s addr = mval)
    (hc : b2n s.of_ = c) :
    execInsn (.adoxMem dst base disp) len s =
      { s with rip := nextRip,
               of_ := decide (x + mval + c ≥ W64),
               gpr := gprUpd s.gpr dst ((x + mval + c) % W64),
               leak := s.leak ++ [.load64 addr] } := by
  dsimp [execInsn]; simp only [hrip, hx, ha, hm, hc]

theorem exec_adoxReg {dst src : Gpr} {len nextRip x y c : Nat} {s : X86State}
    (hrip : s.rip + len = nextRip)
    (hx : s.gpr dst % W64 = x)
    (hy : s.gpr src % W64 = y)
    (hc : b2n s.of_ = c) :
    execInsn (.adoxReg dst src) len s =
      { s with rip := nextRip,
               of_ := decide (x + y + c ≥ W64),
               gpr := gprUpd s.gpr dst ((x + y + c) % W64) } := by
  dsimp [execInsn]; simp only [hrip, hx, hy, hc]

theorem exec_movStore64 {base : Gpr} {disp : Nat} {src : Gpr} {len nextRip addr v : Nat} {s : X86State}
    (hrip : s.rip + len = nextRip)
    (ha : (s.gpr base + disp) % W64 = addr)
    (hv : s.gpr src % W64 = v) :
    execInsn (.movStore64 base disp src) len s =
      { s with rip := nextRip, mem64 := mem64Upd s.mem64 addr v, leak := s.leak ++ [.store64 addr] } := by
  dsimp [execInsn]; simp only [hrip, ha, hv]

theorem exec_movLoad64 {dst base : Gpr} {disp len nextRip addr mval : Nat} {s : X86State}
    (hrip : s.rip + len = nextRip)
    (ha : (s.gpr base + disp) % W64 = addr)
    (hm : readMem64 s addr = mval) :
    execInsn (.movLoad64 dst base disp) len s =
      { s with rip := nextRip, gpr := gprUpd s.gpr dst mval, leak := s.leak ++ [.load64 addr] } := by
  dsimp [execInsn]; simp only [hrip, ha, hm]

theorem exec_cmpImm64 {reg : Gpr} {imm len nextRip lhs : Nat} {s : X86State}
    (hrip : s.rip + len = nextRip)
    (hl : s.gpr reg % W64 = lhs) :
    execInsn (.cmpImm64 reg imm) len s =
      { s with rip := nextRip, cf := decide (lhs < imm), zf := decide (lhs = imm), of_ := false } := by
  dsimp [execInsn]; simp only [hrip, hl]

theorem exec_cmove64 {dst src : Gpr} {len nextRip v : Nat} {s : X86State}
    (hrip : s.rip + len = nextRip)
    (hv : (if s.zf then s.gpr src % W64 else s.gpr dst % W64) = v) :
    execInsn (.cmove64 dst src) len s =
      { s with rip := nextRip, gpr := gprUpd s.gpr dst v } := by
  dsimp [execInsn]; simp only [hrip, hv]

theorem exec_vmovdquLd256 {dst : Ymm} {base idx : Gpr} {disp len nextRip addr : Nat}
    {m8 : Nat → UInt8} {s : X86State}
    (hrip : s.rip + len = nextRip)
    (ha : (s.gpr base + s.gpr idx + disp) % W64 = addr)
    (hm : s.mem8 = m8) :
    execInsn (.vmovdquLd256 dst base idx disp) len s =
      { s with rip := nextRip, ymmDirty := true, ymm := ymmUpd s.ymm dst (loadYmm256 m8 addr),
               leak := s.leak ++ [.load256 addr] } := by
  dsimp [execInsn]; simp only [hrip, ha, hm]

theorem exec_addImm64 {dst : Gpr} {imm len nextRip v : Nat} {s : X86State}
    (hrip : s.rip + len = nextRip)
    (hv : (s.gpr dst % W64) + imm = v)
    (hlt : v < W64) :
    execInsn (.addImm64 dst imm) len s =
      { s with rip := nextRip, cf := false, zf := decide (v = 0), gpr := gprUpd s.gpr dst v } := by
  dsimp [execInsn]; simp only [hrip, hv, Nat.mod_eq_of_lt hlt, decide_eq_false (Nat.not_le_of_lt hlt)]

theorem exec_cmpReg64 {lhs rhs : Gpr} {len nextRip va vb : Nat} {s : X86State}
    (hrip : s.rip + len = nextRip)
    (ha : s.gpr lhs % W64 = va)
    (hb : s.gpr rhs % W64 = vb) :
    execInsn (.cmpReg64 lhs rhs) len s =
      { s with rip := nextRip, cf := decide (va < vb), zf := decide (va = vb), of_ := false } := by
  dsimp [execInsn]; simp only [hrip, ha, hb]

theorem exec_ret_clean {len : Nat} {s : X86State} (hy : s.ymmDirty = false) :
    execInsn .ret len s = { s with halted := true } := by
  dsimp [execInsn]; simp only [hy]; rfl

end IsaLemmas
