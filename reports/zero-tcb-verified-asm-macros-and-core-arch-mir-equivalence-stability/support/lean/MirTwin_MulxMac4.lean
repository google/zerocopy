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

namespace LockedObligations

open AsmMirBase IsaLemmas

theorem verify_mulx_mac4_mir_twin
    (t0 t1 t2 t3 a0 a1 a2 a3 b : Nat)
    (ht0 : t0 < W64) (ht1 : t1 < W64) (ht2 : t2 < W64) (ht3 : t3 < W64)
    (ha0 : a0 < W64) (ha1 : a1 < W64) (ha2 : a2 < W64) (ha3 : a3 < W64)
    (hb : b < W64) :
    let (out0, out1, out2, out3, out4) := mulxMac4MirTwin t0 t1 t2 t3 a0 a1 a2 a3 b
    val5Limbs out0 out1 out2 out3 out4 = mac4RefVal t0 t1 t2 t3 a0 a1 a2 a3 b := by
  unfold mulxMac4MirTwin mulxU64Prim addcarryxU64Prim
  dsimp only
  rw [Nat.mod_eq_of_lt ha0, Nat.mod_eq_of_lt ha1, Nat.mod_eq_of_lt ha2, Nat.mod_eq_of_lt ha3,
      Nat.mod_eq_of_lt hb, Nat.mod_eq_of_lt ht0, Nat.mod_eq_of_lt ht1, Nat.mod_eq_of_lt ht2,
      Nat.mod_eq_of_lt ht3]
  have m_comm0 : a0 * b = b * a0 := Nat.mul_comm a0 b
  have m_comm1 : a1 * b = b * a1 := Nat.mul_comm a1 b
  have m_comm2 : a2 * b = b * a2 := Nat.mul_comm a2 b
  have m_comm3 : a3 * b = b * a3 := Nat.mul_comm a3 b
  rw [m_comm0, m_comm1, m_comm2, m_comm3]
  have mod_id : ∀ x, x % W64 % W64 = x % W64 := fun x => Nat.mod_mod x W64
  simp only [mod_id, Nat.zero_mod, Nat.add_zero]
  have hw64 : W64 = 18446744073709551616 := rfl
  have hlo0 : (b * a0) % W64 < W64 := Nat.mod_lt _ (by decide)
  have hhi0 : ((b * a0) / W64) % W64 < W64 := Nat.mod_lt _ (by decide)
  have hlo1 : (b * a1) % W64 < W64 := Nat.mod_lt _ (by decide)
  have hhi1 : ((b * a1) / W64) % W64 < W64 := Nat.mod_lt _ (by decide)
  have hlo2 : (b * a2) % W64 < W64 := Nat.mod_lt _ (by decide)
  have hhi2 : ((b * a2) / W64) % W64 < W64 := Nat.mod_lt _ (by decide)
  have hlo3 : (b * a3) % W64 < W64 := Nat.mod_lt _ (by decide)
  have hhi3 : ((b * a3) / W64) % W64 < W64 := Nat.mod_lt _ (by decide)
  have c1_lt : ((b * a0) % W64 + t0) / W64 < 2 :=
    (Nat.div_lt_iff_lt_mul (by decide : 0 < W64)).mpr (by omega)
  rw [Nat.mod_eq_of_lt c1_lt]
  have c2_lt : (((b * a0) / W64) % W64 + (b * a1) % W64 + ((b * a0) % W64 + t0) / W64) / W64 < 2 :=
    (Nat.div_lt_iff_lt_mul (by decide : 0 < W64)).mpr (by omega)
  rw [Nat.mod_eq_of_lt c2_lt]
  let r9 := (((b * a0) / W64) % W64 + (b * a1) % W64 + ((b * a0) % W64 + t0) / W64) % W64
  have hr9 : r9 < W64 := Nat.mod_lt _ (by decide)
  have o2_lt : (r9 + t1) / W64 < 2 :=
    (Nat.div_lt_iff_lt_mul (by decide : 0 < W64)).mpr (by omega)
  have hc := mac4_combine_conservation t0 t1 t2 t3 a0 a1 a2 a3 b ht0 ht1 ht2 ht3 ha0 ha1 ha2 ha3 hb
  dsimp only [Nat.add_zero] at hc
  let cf2 := (((b * a0) / W64) % W64 + (b * a1) % W64 + ((b * a0) % W64 + t0) / W64) / W64
  have hcf2 : cf2 < 2 := c2_lt
  let of2 := (r9 + t1) / W64
  have hof2 : of2 < 2 := o2_lt
  have c3_lt : (((b * a1) / W64) % W64 + (b * a2) % W64 + cf2) / W64 < 2 :=
    (Nat.div_lt_iff_lt_mul (by decide : 0 < W64)).mpr (by omega)
  let r10 := (((b * a1) / W64) % W64 + (b * a2) % W64 + cf2) % W64
  have hr10 : r10 < W64 := Nat.mod_lt _ (by decide)
  have o3_lt : (r10 + t2 + of2) / W64 < 2 :=
    (Nat.div_lt_iff_lt_mul (by decide : 0 < W64)).mpr (by omega)
  let cf3 := (((b * a1) / W64) % W64 + (b * a2) % W64 + cf2) / W64
  have hcf3 : cf3 < 2 := c3_lt
  let of3 := (r10 + t2 + of2) / W64
  have hof3 : of3 < 2 := o3_lt
  have c4_lt : (((b * a2) / W64) % W64 + (b * a3) % W64 + cf3) / W64 < 2 :=
    (Nat.div_lt_iff_lt_mul (by decide : 0 < W64)).mpr (by omega)
  let r11 := (((b * a2) / W64) % W64 + (b * a3) % W64 + cf3) % W64
  have hr11 : r11 < W64 := Nat.mod_lt _ (by decide)
  have o4_lt : (r11 + t3 + of3) / W64 < 2 :=
    (Nat.div_lt_iff_lt_mul (by decide : 0 < W64)).mpr (by omega)
  dsimp only [r9, cf2, of2, r10, cf3, of3, r11] at o2_lt c3_lt o3_lt c4_lt o4_lt
  simp only [Nat.mod_eq_of_lt o2_lt, Nat.mod_eq_of_lt c3_lt,
             Nat.mod_eq_of_lt o3_lt, Nat.mod_eq_of_lt c4_lt,
             Nat.mod_eq_of_lt o4_lt]
  exact hc.1

end LockedObligations
