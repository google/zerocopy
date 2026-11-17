-- Copyright 2026 The Fuchsia Authors
--
-- Licensed under a BSD-style license <LICENSE-BSD>, Apache License, Version 2.0
-- <LICENSE-APACHE or https://www.apache.org/licenses/LICENSE-2.0>, or the MIT
-- license <LICENSE-MIT or https://opensource.org/licenses/MIT>, at your option.
-- This file may not be copied, modified, or distributed except according to
-- those terms.

/-!
# Lean 4 formal overflow bounds for delayed-modulo Adler-32, nested u16 lanes, and AVX-512 VNNI chunks
-/

namespace AdlerSimdOverflowBounds

/-! ### 6.2 Adler-32: delayed modulo, exact scalar ceiling `5552`, nested
`u16 → u32` lanes (`K = 16`), and division-free reduction -/

def adlerMod : Nat := 65521

def adlerStepMod (ab : Nat × Nat) (byte : Nat) : Nat × Nat :=
  let a' := (ab.1 + byte) % adlerMod
  let b' := (ab.2 + a') % adlerMod
  (a', b')

def adlerStepRaw (ab : Nat × Nat) (byte : Nat) : Nat × Nat :=
  let a' := ab.1 + byte
  let b' := ab.2 + a'
  (a', b')

def adlerReduce (ab : Nat × Nat) : Nat × Nat := (ab.1 % adlerMod, ab.2 % adlerMod)

theorem adlerStepRaw_reduce_comm (ab : Nat × Nat) (byte : Nat) :
    adlerReduce (adlerStepRaw ab byte) = adlerStepMod (adlerReduce ab) byte := by
  cases ab with
  | mk a b =>
    unfold adlerReduce adlerStepRaw adlerStepMod
    dsimp only
    have h1 : (a + byte) % adlerMod = (a % adlerMod + byte) % adlerMod := by
      rw [Nat.mod_add_mod]
    have h2 : (b + (a + byte)) % adlerMod =
        (b % adlerMod + (a + byte) % adlerMod) % adlerMod := by
      rw [← Nat.add_mod]
    rw [← h1, ← h2]

theorem adlerFold_delayed_correct (bytes : List Nat) (ab : Nat × Nat) :
    adlerReduce (bytes.foldl adlerStepRaw ab) = bytes.foldl adlerStepMod (adlerReduce ab) := by
  induction bytes generalizing ab with
  | nil => rfl
  | cons byte rest ih =>
    simp only [List.foldl_cons]
    rw [ih (adlerStepRaw ab byte), adlerStepRaw_reduce_comm]

/-- Worst-case unreduced `s2` after `n` bytes from `s1, s2 ≤ 65520`. -/
def adlerMaxB (n : Nat) : Nat := 65520 + n * 65520 + 255 * (n * (n + 1) / 2)

/-- Exact values: `adlerMaxB 5552 = 4,294,690,200 < 2^32 ≤ 4,296,171,735 =
adlerMaxB 5553`, and `5552 = 347 · 16`. -/
theorem adler_scalar_5552_ceiling :
    adlerMaxB 5552 = 4294690200 ∧ adlerMaxB 5552 < Nat.pow 2 32 ∧
    adlerMaxB 5553 = 4296171735 ∧ Nat.pow 2 32 ≤ adlerMaxB 5553 ∧
    347 * 16 = 5552 := by
  decide

/-- Per-lane step of the nested kernel in source order
(`s2_16[i] += s1_16[i]; s1_16[i] += blk[i]`). -/
def laneStep (st : Nat × Nat) (b : Nat) : Nat × Nat := (st.1 + b, st.2 + st.1)

theorem laneFold_mono : ∀ (bs : List Nat) (a b a' b' : Nat), a ≤ a' → b ≤ b' →
    (∀ x ∈ bs, x ≤ 255) →
    (bs.foldl laneStep (a, b)).1 ≤ ((List.replicate bs.length 255).foldl laneStep (a', b')).1 ∧
    (bs.foldl laneStep (a, b)).2 ≤ ((List.replicate bs.length 255).foldl laneStep (a', b')).2
  | [], a, b, a', b', ha, hb, _ => by simpa using And.intro ha hb
  | x :: xs, a, b, a', b', ha, hb, hx => by
    have hx0 : x ≤ 255 := hx x (List.mem_cons_self ..)
    have hxs : ∀ y ∈ xs, y ≤ 255 := fun y hy => hx y (List.mem_cons_of_mem _ hy)
    have ih := laneFold_mono xs (a + x) (b + a) (a' + 255) (b' + a') (by omega) (by omega) hxs
    simpa [List.foldl_cons, List.replicate_succ, laneStep] using ih

/-- Exact per-lane bound for one `K = 16` super-block: `s1_16 ≤ 4,080` and
`s2_16 ≤ 255 · 16 · 15 / 2 = 30,600`, for every input. -/
theorem adler_u16_K16_exact (bs : List Nat) (hlen : bs.length = 16)
    (hb : ∀ x ∈ bs, x ≤ 255) :
    (bs.foldl laneStep (0, 0)).1 ≤ 4080 ∧ (bs.foldl laneStep (0, 0)).2 ≤ 30600 := by
  have h := laneFold_mono bs 0 0 0 0 (Nat.le_refl _) (Nat.le_refl _) hb
  rw [hlen] at h
  have hc : (List.replicate 16 255).foldl laneStep (0, 0) = (4080, 30600) := by decide
  rw [hc] at h
  exact h

/-- Thresholds: the crude bound `255·K²` is `65,280 ≤ 65,535` exactly at `K = 16`
(`K = 17` exceeds `u16`); with the source update order the exact worst case
first exceeds `u16` at `K = 24` (`K = 23`: 64,515), and `K = 32` gives 126,480. -/
theorem adler_u16_K_thresholds :
    255 * 16 * 16 = 65280 ∧ 65280 ≤ 65535 ∧ 65535 < 255 * 17 * 17 ∧
    ((List.replicate 23 255).foldl laneStep (0, 0)).2 = 64515 ∧
    ((List.replicate 24 255).foldl laneStep (0, 0)).2 = 70380 ∧
    ((List.replicate 32 255).foldl laneStep (0, 0)).2 = 126480 ∧
    255 * (16 * (16 + 1) / 2) = 34680 := by
  decide

/-- Division-free reduction modulo 65521 using `2^16 ≡ 15`. -/
def adlerReduceU32Nat (v : Nat) : Nat :=
  let t1 := v % 65536 + (v / 65536) * 15
  let t2 := t1 % 65536 + (t1 / 65536) * 15
  if t2 ≥ 65521 then t2 - 65521 else t2

theorem adlerReduceU32Nat_exact (v : Nat) (hv : v < Nat.pow 2 32) :
    adlerReduceU32Nat v = v % adlerMod ∧ adlerReduceU32Nat v < adlerMod := by
  unfold adlerReduceU32Nat adlerMod
  let t1 := v % 65536 + v / 65536 * 15
  let t2 := t1 % 65536 + t1 / 65536 * 15
  change (if t2 ≥ 65521 then t2 - 65521 else t2) = v % 65521 ∧
    (if t2 ≥ 65521 then t2 - 65521 else t2) < 65521
  have hv32 : v < 4294967296 := hv
  have hv_eq : v = t1 + (v / 65536) * 65521 := by omega
  have ht1_le : t1 ≤ 1048560 := by omega
  have ht1_eq : t1 = t2 + (t1 / 65536) * 65521 := by omega
  have ht2_le : t2 ≤ 65760 := by omega
  have hmod1 : v % 65521 = t1 % 65521 := by
    rw [hv_eq, Nat.add_mul_mod_self_right]
  have hmod2 : t1 % 65521 = t2 % 65521 := by
    rw [ht1_eq, Nat.add_mul_mod_self_right]
  rw [hmod1, hmod2]
  split <;> rename_i hge
  · have hlt : t2 - 65521 < 65521 := by omega
    have hsub : t2 = (t2 - 65521) + 1 * 65521 := by omega
    constructor
    · conv => rhs; rw [hsub, Nat.add_mul_mod_self_right]
      exact (Nat.mod_eq_of_lt hlt).symm
    · exact hlt
  · have hlt : t2 < 65521 := by omega
    exact ⟨(Nat.mod_eq_of_lt hlt).symm, hlt⟩

/-! ### 6.3 Dual-stream AVX-512 VNNI chunk ceiling (`2048` 128-byte blocks) -/

/-- Crude bound used to justify the `2048` cap: a `u32` prefix lane gaining
`1020 = 4·255` per 64-byte half. -/
def adlerAvx512MaxPrevB (blocks : Nat) : Nat := 1020 * blocks * blocks

def adlerAvx512MaxDot (blocks : Nat) : Nat := blocks * 2 * (255 * 250)

theorem avx512_crude_bounds :
    adlerAvx512MaxPrevB 2048 = 4278190080 ∧ adlerAvx512MaxPrevB 2048 < Nat.pow 2 32 ∧
    adlerAvx512MaxPrevB 2052 < Nat.pow 2 32 ∧ Nat.pow 2 32 ≤ adlerAvx512MaxPrevB 2053 ∧
    adlerAvx512MaxDot 2048 = 261120000 := by
  decide

/-- Lanes as actually used by the shipped kernel: `vpsadbw` sums 8 bytes into a
`u64` lane (`2040` per vector; prefix lane `≤ 2040·N(N-1)/2`), and `vpdpbusd`
adds 4 weighted bytes into a `u32` lane (weights `64..61` in lane 0:
`255·250 = 63,750` per vector). -/
theorem avx512_shipped_lane_bounds :
    8 * 255 = 2040 ∧ 2040 * (2048 * 2047 / 2) = 4276101120 ∧
    255 * (64 + 63 + 62 + 61) = 63750 ∧ 2048 * 63750 = 130560000 ∧
    2048 * 63750 < Nat.pow 2 31 ∧ 33686 * 63750 < Nat.pow 2 31 ∧
    Nat.pow 2 31 ≤ 33687 * 63750 := by
  decide

/-- The figure `4,275,969,680` is below `2^32` but coincides with none of the
derived bounds and is not a multiple of 255. -/
theorem avx512_unreproduced_figure :
    (4275969680 : Nat) < Nat.pow 2 32 ∧ 4275969680 ≠ adlerAvx512MaxPrevB 2048 ∧
    (4275969680 : Nat) ≠ 2040 * (2048 * 2047 / 2) ∧ 4275969680 % 255 ≠ 0 := by
  decide


/-! ## Axiom receipts -/


/-- info: 'AdlerSimdOverflowBounds.adlerStepRaw_reduce_comm' depends on axioms: [propext] -/
#guard_msgs in
#print axioms adlerStepRaw_reduce_comm

/-- info: 'AdlerSimdOverflowBounds.adlerFold_delayed_correct' depends on axioms: [propext] -/
#guard_msgs in
#print axioms adlerFold_delayed_correct

/-- info: 'AdlerSimdOverflowBounds.adler_scalar_5552_ceiling' does not depend on any axioms -/
#guard_msgs in
#print axioms adler_scalar_5552_ceiling

/-- info: 'AdlerSimdOverflowBounds.laneFold_mono' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms laneFold_mono

/-- info: 'AdlerSimdOverflowBounds.adler_u16_K16_exact' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms adler_u16_K16_exact

/-- info: 'AdlerSimdOverflowBounds.adler_u16_K_thresholds' does not depend on any axioms -/
#guard_msgs in
#print axioms adler_u16_K_thresholds

/-- info: 'AdlerSimdOverflowBounds.adlerReduceU32Nat_exact' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms adlerReduceU32Nat_exact

/-- info: 'AdlerSimdOverflowBounds.avx512_crude_bounds' does not depend on any axioms -/
#guard_msgs in
#print axioms avx512_crude_bounds

/-- info: 'AdlerSimdOverflowBounds.avx512_shipped_lane_bounds' does not depend on any axioms -/
#guard_msgs in
#print axioms avx512_shipped_lane_bounds

/-- info: 'AdlerSimdOverflowBounds.avx512_unreproduced_figure' does not depend on any axioms -/
#guard_msgs in
#print axioms avx512_unreproduced_figure

end AdlerSimdOverflowBounds
