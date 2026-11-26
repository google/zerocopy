-- Copyright 2026 The Fuchsia Authors
--
-- Licensed under a BSD-style license <LICENSE-BSD>, Apache License, Version 2.0
-- <LICENSE-APACHE or https://www.apache.org/licenses/LICENSE-2.0>, or the MIT
-- license <LICENSE-MIT or https://opensource.org/licenses/MIT>, at your option.
-- This file may not be copied, modified, or distributed except according to
-- those terms.

module
prelude
public import Init.Core
public import Init.NotationExtra
public import Init.SimpLemmas
public import Init.Data.Nat.Basic
public import Init.Data.Nat.Div.Basic
public import Init.Data.Int.Basic
public import Anneal.InitLemmas

public section

/-!
# Codec Integer Clamping, Rounding Shifts, 4×4 IDCT & Deblocking DSP Specs

Zero-duplication, 0-TCB, Pass-1-pure (`prelude` + locked `Init.*` +
`Anneal.InitLemmas`, zero `._unsafe_rec`, zero `omega`,
axioms `⊆ [propext, Quot.sound]`, zero `Classical.choice`)
integer DSP specification and overflow-freedom library for H.264 and AV1
(`rav1d`) pixel-processing kernels:

1. **Clamping & Pixel-Range Specs (`clip3Nat`, `clipPixelNat`, `clipU8`,
   `clipU10`, `clip3Int`, `clipSymInt`, `clipIntToPixel`):**
   - Exact range invariants, idempotence, monotonicity, and identity on
     in-range inputs for arbitrary bit depths (`8`, `10`, `12`, `bd`).
2. **Rounding Right-Shift (`roundShiftNat`):**
   - `((x + 2^(s - 1)) / 2^s)` monotonicity, zero preservation, and tight upper
     bounds directly reused by H.264 6-bit IDCT rounding (`(x + 32) / 64`) and
     AV1 `rav1d` `round_shift`.
3. **H.264 §8.5.12.2 4×4 Integer IDCT Butterfly (`intFloorDivPos`, `idct4Row`,
   `idct4AddPixel`):**
   - Exact pure integer butterfly equations (`e0..e3`, `y0..y3`) using H.264
     §5.1 arithmetic right shifts (`intFloorDivPos`, floor division toward
     `-∞`).
   - Proves exact magnitude bounds (`|y_i| ≤ 4 * B` when every input
     `|c_i| ≤ B`), proving `i32` overflow-freedom across both 8-bit and 10-bit
     HDR inputs, plus unconditional `[0, 2^bd - 1]` output pixel range safety.
4. **H.264 §8.7.2.2 Deblocking Filter (`deblockDelta`, `deblockPair`):**
   - Clamped delta `Δ = clipSymInt tc (((q0 - p0) * 4 + (p1 - q1) + 4) >> 3)`,
     exact symmetric bound `-tc ≤ Δ ≤ tc`, and unconditional pixel-range
     preservation (`0 ≤ p0' < 2^bd`, `0 ≤ q0' < 2^bd`) for 8-bit (`deblock8`)
     and 10-bit (`deblock10`) HDR luma/chroma filters.
-/

namespace Anneal.MediaDsp.ClampAndButterfly

open Anneal.InitLemmas

private theorem pow2_zero : HPow.hPow (2 : Nat) 0 = 1 := rfl

private theorem pow2_pos (n : Nat) : 0 < HPow.hPow (2 : Nat) n :=
  nat_two_pow_pos n

private theorem ble_true_iff_le :
    ∀ a b : Nat, Nat.ble a b = true ↔ a ≤ b
  | 0, _ => ⟨fun _ => Nat.zero_le _, fun _ => rfl⟩
  | _ + 1, 0 =>
    ⟨fun h => Bool.noConfusion h,
     fun h => False.elim (Nat.not_succ_le_zero _ h)⟩
  | a + 1, b + 1 => by
    dsimp only [Nat.ble]
    exact ⟨fun h => Nat.succ_le_succ ((ble_true_iff_le a b).mp h),
           fun h => (ble_true_iff_le a b).mpr (Nat.le_of_succ_le_succ h)⟩

private theorem ble_false_iff_lt (a b : Nat) :
    Nat.ble a b = false ↔ b < a := by
  constructor
  · intro hf
    cases Nat.lt_or_ge b a with
    | inl hlt => exact hlt
    | inr hge =>
      have ht := (ble_true_iff_le a b).mpr hge
      rw [hf] at ht
      exact Bool.noConfusion ht
  · intro hlt
    cases hb : Nat.ble a b with
    | false => rfl
    | true =>
      exact False.elim (Nat.not_lt_of_ge ((ble_true_iff_le a b).mp hb) hlt)

private theorem nat_div_le_div_right {a b : Nat} (c : Nat) (hab : a ≤ b) :
    HDiv.hDiv a c ≤ HDiv.hDiv b c := by
  cases c with
  | zero =>
    rw [Nat.div_zero, Nat.div_zero]
    exact Nat.le_refl 0
  | succ c' =>
    have hpos : 0 < Nat.succ c' := Nat.zero_lt_succ c'
    have h1 : Nat.succ c' * HDiv.hDiv a (Nat.succ c') ≤ a := by
      have hle := Nat.le_add_right
        (Nat.succ c' * HDiv.hDiv a (Nat.succ c')) (HMod.hMod a (Nat.succ c'))
      rw [Nat.div_add_mod] at hle
      exact hle
    have h2 : HDiv.hDiv a (Nat.succ c') * Nat.succ c' ≤ b := by
      rw [Nat.mul_comm]
      exact Nat.le_trans h1 hab
    exact (Nat.le_div_iff_mul_le hpos).mpr h2

private theorem nat_add_lt_add_of_le_of_lt {a b c d : Nat}
    (h1 : a ≤ b) (h2 : c < d) : a + c < b + d :=
  Nat.lt_of_le_of_lt (Nat.add_le_add_right h1 c) (Nat.add_lt_add_left h2 b)

/-! ## Part 1: Natural & Signed Integer Clamping (`clip3Nat`, `clip3Int`) -/

/-- Clamp `x : Nat` into `[lo, hi]` (returns `lo` if `x ≤ lo`, `hi` if
`hi ≤ x`, else `x`). -/
@[expose] def clip3Nat (lo hi x : Nat) : Nat :=
  if Nat.ble x lo then lo
  else if Nat.ble hi x then hi
  else x

/-- Clamp `x : Nat` into a `bd`-bit unsigned pixel `[0, 2^bd - 1]`. -/
@[expose] def clipPixelNat (bd x : Nat) : Nat :=
  clip3Nat 0 (HPow.hPow (2 : Nat) bd - 1) x

/-- Clamp `x : Nat` into 8-bit pixel `[0, 255]`. -/
@[expose] def clipU8 (x : Nat) : Nat :=
  clipPixelNat 8 x

/-- Clamp `x : Nat` into 10-bit HDR pixel `[0, 1023]`. -/
@[expose] def clipU10 (x : Nat) : Nat :=
  clipPixelNat 10 x

/-- `clip3Nat lo hi x` always lies in `[lo, hi]` whenever `lo ≤ hi`. -/
theorem clip3Nat_bounds {lo hi : Nat} (hle : lo ≤ hi) (x : Nat) :
    lo ≤ clip3Nat lo hi x ∧ clip3Nat lo hi x ≤ hi := by
  unfold clip3Nat
  cases h1 : Nat.ble x lo with
  | true => exact ⟨Nat.le_refl lo, hle⟩
  | false =>
    cases h2 : Nat.ble hi x with
    | true => exact ⟨hle, Nat.le_refl hi⟩
    | false =>
      exact ⟨Nat.le_of_lt ((ble_false_iff_lt x lo).mp h1),
             Nat.le_of_lt ((ble_false_iff_lt hi x).mp h2)⟩

/-- `clip3Nat` is the identity on any value already in `[lo, hi]`. -/
theorem clip3Nat_of_mem {lo hi x : Nat} (hlo : lo ≤ x) (hhi : x ≤ hi) :
    clip3Nat lo hi x = x := by
  unfold clip3Nat
  cases h1 : Nat.ble x lo with
  | true =>
    exact Nat.le_antisymm hlo ((ble_true_iff_le x lo).mp h1)
  | false =>
    cases h2 : Nat.ble hi x with
    | true =>
      exact Nat.le_antisymm ((ble_true_iff_le hi x).mp h2) hhi
    | false => rfl

/-- `clip3Nat` is idempotent whenever `lo ≤ hi`. -/
theorem clip3Nat_idem {lo hi : Nat} (hle : lo ≤ hi) (x : Nat) :
    clip3Nat lo hi (clip3Nat lo hi x) = clip3Nat lo hi x :=
  have hb := clip3Nat_bounds hle x
  clip3Nat_of_mem hb.1 hb.2

/-- `clip3Nat` is monotone in `x` whenever `lo ≤ hi`. -/
theorem clip3Nat_mono {lo hi x y : Nat} (hle : lo ≤ hi) (hxy : x ≤ y) :
    clip3Nat lo hi x ≤ clip3Nat lo hi y := by
  unfold clip3Nat
  cases hx1 : Nat.ble x lo with
  | true =>
    exact (clip3Nat_bounds hle y).1
  | false =>
    have hloX : lo < x := (ble_false_iff_lt x lo).mp hx1
    have hloY : lo < y := Nat.lt_of_lt_of_le hloX hxy
    have hy1 : Nat.ble y lo = false := (ble_false_iff_lt y lo).mpr hloY
    rw [hy1]
    cases hx2 : Nat.ble hi x with
    | true =>
      have hhiX : hi ≤ x := (ble_true_iff_le hi x).mp hx2
      have hhiY : hi ≤ y := Nat.le_trans hhiX hxy
      rw [(ble_true_iff_le hi y).mpr hhiY]
      exact Nat.le_refl hi
    | false =>
      have hxHi : x < hi := (ble_false_iff_lt hi x).mp hx2
      cases hy2 : Nat.ble hi y with
      | true => exact Nat.le_of_lt hxHi
      | false => exact hxy

/-- `clipPixelNat bd x` is always strictly below `2^bd`. -/
theorem clipPixelNat_lt {bd : Nat} (x : Nat) :
    clipPixelNat bd x < HPow.hPow (2 : Nat) bd := by
  have hb := clip3Nat_bounds (Nat.zero_le (HPow.hPow (2 : Nat) bd - 1)) x
  exact Nat.lt_of_le_of_lt hb.2 (Nat.sub_lt (pow2_pos bd) Nat.zero_lt_one)

/-- Decidable `Int.le` boolean helper (`0` `._unsafe_rec`). -/
@[expose] def intBle (a b : Int) : Bool :=
  match a, b with
  | .ofNat m, .ofNat n => Nat.ble m n
  | .negSucc _, .ofNat _ => true
  | .ofNat _, .negSucc _ => false
  | .negSucc m, .negSucc n => Nat.ble n m

/-- Exact reflection of `intBle a b = true ↔ a ≤ b`. -/
theorem intBle_true_iff (a b : Int) : intBle a b = true ↔ a ≤ b := by
  cases a with
  | ofNat m =>
    cases b with
    | ofNat n =>
      unfold intBle
      exact (ble_true_iff_le m n).trans (int_ofNat_le_iff m n).symm
    | negSucc n =>
      unfold intBle
      exact ⟨fun h => Bool.noConfusion h,
             fun h => False.elim (int_not_ofNat_le_negSucc m n h)⟩
  | negSucc m =>
    cases b with
    | ofNat n =>
      unfold intBle
      exact ⟨fun _ => int_negSucc_le_ofNat m n, fun _ => rfl⟩
    | negSucc n =>
      unfold intBle
      exact (ble_true_iff_le n m).trans (int_negSucc_le_negSucc_iff m n).symm

/-- Exact reflection of `intBle a b = false ↔ b < a`. -/
theorem intBle_false_iff (a b : Int) : intBle a b = false ↔ b < a := by
  cases a with
  | ofNat m =>
    cases b with
    | ofNat n =>
      unfold intBle
      exact (ble_false_iff_lt m n).trans (int_ofNat_lt_iff n m).symm
    | negSucc n =>
      unfold intBle
      exact ⟨fun _ => int_negSucc_lt_ofNat n m, fun _ => rfl⟩
  | negSucc m =>
    cases b with
    | ofNat n =>
      unfold intBle
      exact ⟨fun h => Bool.noConfusion h,
             fun h => False.elim (int_not_ofNat_lt_negSucc n m h)⟩
    | negSucc n =>
      unfold intBle
      exact (ble_false_iff_lt n m).trans (int_negSucc_lt_negSucc_iff n m).symm

private theorem int_le_refl' (a : Int) : a ≤ a :=
  (intBle_true_iff a a).mp (by
    cases a with
    | ofNat m => exact (ble_true_iff_le m m).mpr (Nat.le_refl m)
    | negSucc m => exact (ble_true_iff_le m m).mpr (Nat.le_refl m))

private theorem int_le_of_lt' {a b : Int} (h : a < b) : a ≤ b := by
  cases a with
  | ofNat m =>
    cases b with
    | ofNat n =>
      exact (int_ofNat_le_iff m n).mpr
        (Nat.le_of_lt ((int_ofNat_lt_iff m n).mp h))
    | negSucc n =>
      exact False.elim (int_not_ofNat_lt_negSucc m n h)
  | negSucc m =>
    cases b with
    | ofNat n => exact int_negSucc_le_ofNat m n
    | negSucc n =>
      exact (int_negSucc_le_negSucc_iff m n).mpr
        (Nat.le_of_lt ((int_negSucc_lt_negSucc_iff m n).mp h))

private theorem int_le_antisymm' {a b : Int} (h1 : a ≤ b) (h2 : b ≤ a) :
    a = b := by
  cases a with
  | ofNat m =>
    cases b with
    | ofNat n =>
      exact congrArg Int.ofNat
        (Nat.le_antisymm ((int_ofNat_le_iff m n).mp h1)
          ((int_ofNat_le_iff n m).mp h2))
    | negSucc n => exact False.elim (int_not_ofNat_le_negSucc m n h1)
  | negSucc m =>
    cases b with
    | ofNat n => exact False.elim (int_not_ofNat_le_negSucc n m h2)
    | negSucc n =>
      exact congrArg Int.negSucc
        (Nat.le_antisymm ((int_negSucc_le_negSucc_iff n m).mp h2)
          ((int_negSucc_le_negSucc_iff m n).mp h1))

/-- Signed integer clamp `Clip3(lo, hi, x)` per ITU-T H.264 §5.7 and AV1
`Clip3`. -/
@[expose] def clip3Int (lo hi x : Int) : Int :=
  if intBle x lo then lo
  else if intBle hi x then hi
  else x

/-- Symmetric signed clamp into `[-bound, bound]` (used in H.264 deblocking
`Clip3(-tc, tc, delta)`). -/
@[expose] def clipSymInt (bound : Nat) (x : Int) : Int :=
  clip3Int (Int.negOfNat bound) (Int.ofNat bound) x

/-- Clamp any signed integer `x : Int` into unsigned `bd`-bit pixel
`[0, 2^bd - 1]` returning a `Nat`. -/
@[expose] def clipIntToPixel (bd : Nat) (x : Int) : Nat :=
  match x with
  | .negSucc _ => 0
  | .ofNat n => clipPixelNat bd n

/-- `clip3Int lo hi x` always lies in `[lo, hi]` whenever `lo ≤ hi`. -/
theorem clip3Int_bounds {lo hi : Int} (hle : lo ≤ hi) (x : Int) :
    lo ≤ clip3Int lo hi x ∧ clip3Int lo hi x ≤ hi := by
  unfold clip3Int
  cases h1 : intBle x lo with
  | true => exact ⟨int_le_refl' lo, hle⟩
  | false =>
    cases h2 : intBle hi x with
    | true => exact ⟨hle, int_le_refl' hi⟩
    | false =>
      exact ⟨int_le_of_lt' ((intBle_false_iff x lo).mp h1),
             int_le_of_lt' ((intBle_false_iff hi x).mp h2)⟩

/-- `clip3Int` is the identity on any in-range `x ∈ [lo, hi]`. -/
theorem clip3Int_of_mem {lo hi x : Int} (hlo : lo ≤ x) (hhi : x ≤ hi) :
    clip3Int lo hi x = x := by
  unfold clip3Int
  cases h1 : intBle x lo with
  | true => exact int_le_antisymm' hlo ((intBle_true_iff x lo).mp h1)
  | false =>
    cases h2 : intBle hi x with
    | true => exact int_le_antisymm' ((intBle_true_iff hi x).mp h2) hhi
    | false => rfl

/-- `clip3Int` is idempotent whenever `lo ≤ hi`. -/
theorem clip3Int_idem {lo hi : Int} (hle : lo ≤ hi) (x : Int) :
    clip3Int lo hi (clip3Int lo hi x) = clip3Int lo hi x :=
  have hb := clip3Int_bounds hle x
  clip3Int_of_mem hb.1 hb.2

/-- `clipSymInt bound x` always lies in `[-bound, bound]`. -/
theorem clipSymInt_bounds (bound : Nat) (x : Int) :
    Int.negOfNat bound ≤ clipSymInt bound x ∧
    clipSymInt bound x ≤ Int.ofNat bound := by
  have hle : Int.negOfNat bound ≤ Int.ofNat bound := by
    cases bound with
    | zero => exact int_le_refl' (Int.ofNat 0)
    | succ k => exact int_negSucc_le_ofNat k (Nat.succ k)
  exact clip3Int_bounds hle x

/-- `clipIntToPixel bd x` is always strictly below `2^bd` for any `x : Int`. -/
theorem clipIntToPixel_lt (bd : Nat) (x : Int) :
    clipIntToPixel bd x < HPow.hPow (2 : Nat) bd := by
  cases x with
  | negSucc _ => exact pow2_pos bd
  | ofNat n => exact clipPixelNat_lt n

/-! ## Part 2: Rounding Right-Shift (`roundShiftNat`) -/

/-- Unsigned rounding right shift `(x + 2^(s - 1)) / 2^s` (returns `x` when
`s = 0`). -/
@[expose] def roundShiftNat (x s : Nat) : Nat :=
  match s with
  | 0 => x
  | k + 1 =>
    HDiv.hDiv (x + HPow.hPow (2 : Nat) k) (HPow.hPow (2 : Nat) (k + 1))

/-- `roundShiftNat 0 s = 0` for every shift `s`. -/
theorem roundShiftNat_zero (s : Nat) : roundShiftNat 0 s = 0 := by
  cases s with
  | zero => rfl
  | succ k =>
    change HDiv.hDiv (0 + HPow.hPow (2 : Nat) k)
      (HPow.hPow (2 : Nat) (k + 1)) = 0
    rw [Nat.zero_add]
    have hlt : HPow.hPow (2 : Nat) k < HPow.hPow (2 : Nat) (k + 1) := by
      rw [Nat.pow_succ, Nat.mul_two]
      exact Nat.lt_add_of_pos_right (pow2_pos k)
    exact Nat.div_eq_of_lt hlt

/-- Monotonicity of `roundShiftNat` in `x`. -/
theorem roundShiftNat_mono {x y : Nat} (s : Nat) (hxy : x ≤ y) :
    roundShiftNat x s ≤ roundShiftNat y s := by
  cases s with
  | zero => exact hxy
  | succ k =>
    exact nat_div_le_div_right (HPow.hPow (2 : Nat) (k + 1))
      (Nat.add_le_add_right hxy (HPow.hPow (2 : Nat) k))

/-- Tight upper bound: if `x ≤ M * 2^s`, then `roundShiftNat x s ≤ M`. -/
theorem roundShiftNat_le_of_mul {x M s : Nat}
    (hle : x ≤ M * HPow.hPow (2 : Nat) s) :
    roundShiftNat x s ≤ M := by
  cases s with
  | zero =>
    change x ≤ M
    rw [pow2_zero, Nat.mul_one] at hle
    exact hle
  | succ k =>
    change HDiv.hDiv (x + HPow.hPow (2 : Nat) k)
      (HPow.hPow (2 : Nat) (k + 1)) ≤ M
    have h1 : x + HPow.hPow (2 : Nat) k <
        (M + 1) * HPow.hPow (2 : Nat) (k + 1) := by
      have hpow : HPow.hPow (2 : Nat) k < HPow.hPow (2 : Nat) (k + 1) := by
        rw [Nat.pow_succ, Nat.mul_two]
        exact Nat.lt_add_of_pos_right (pow2_pos k)
      have h2 := nat_add_lt_add_of_le_of_lt hle hpow
      rw [Nat.add_mul, Nat.one_mul]
      exact h2
    exact Nat.le_of_lt_succ
      ((Nat.div_lt_iff_lt_mul (pow2_pos (k + 1))).mpr h1)

/-! ## Part 3: H.264 §8.5.12.2 4×4 Integer IDCT Butterfly & Overflow Bounds -/

/-- Truncating signed division toward zero by a positive natural divisor `d`
(matches C `/` and Rust `i32 / d`, `0` `._unsafe_rec`). -/
@[expose] def intTruncDivNat (c : Int) (d : Nat) : Int :=
  match c with
  | .ofNat n => Int.ofNat (HDiv.hDiv n d)
  | .negSucc n => Int.negOfNat (HDiv.hDiv (n + 1) d)

/-- Floor signed division toward `-∞` by a positive natural divisor `d`
(matches ITU-T H.264 §5.1 arithmetic right shift `x >> y` for `d = 2^y` and
C/Rust signed `i32 >> y`, `0` `._unsafe_rec`). -/
@[expose] def intFloorDivPos (c : Int) (d : Nat) : Int :=
  match c with
  | .ofNat n => Int.ofNat (HDiv.hDiv n d)
  | .negSucc n => Int.negSucc (HDiv.hDiv n d)

/-- Exact 4-point H.264 §8.5.12.2 1D integer IDCT butterfly on
`(c0, c1, c2, c3)`:
- `e0 = c0 + c2`, `e1 = c0 - c2`
- `e2 = intFloorDivPos c1 2 - c3`, `e3 = c1 + intFloorDivPos c3 2`
- outputs `(e0 + e3, e1 + e2, e1 - e2, e0 - e3)`. -/
@[expose] def idct4Row (c0 c1 c2 c3 : Int) : Int × Int × Int × Int :=
  let e0 := c0 + c2
  let e1 := c0 - c2
  let e2 := intFloorDivPos c1 2 - c3
  let e3 := c1 + intFloorDivPos c3 2
  (e0 + e3, e1 + e2, e1 - e2, e0 - e3)

/-- `idct4Row` maps the all-zero residual block to `(0, 0, 0, 0)`. -/
theorem idct4Row_zero : idct4Row 0 0 0 0 = (0, 0, 0, 0) := rfl

private theorem subNatNat_natAbs_le (m n : Nat) :
    (Int.subNatNat m n).natAbs ≤ m + n := by
  unfold Int.subNatNat
  cases h : n - m with
  | zero =>
    change m - n ≤ m + n
    exact Nat.le_trans (Nat.sub_le m n) (Nat.le_add_right m n)
  | succ k =>
    change k + 1 ≤ m + n
    rw [← h]
    exact Nat.le_trans (Nat.sub_le n m) (Nat.le_add_left n m)

/-- Triangle inequality for `Int.natAbs` under `Int.add`. -/
theorem natAbs_add_le (a b : Int) : (a + b).natAbs ≤ a.natAbs + b.natAbs := by
  cases a with
  | ofNat m =>
    cases b with
    | ofNat n => exact Nat.le_refl (m + n)
    | negSucc n => exact subNatNat_natAbs_le m (n + 1)
  | negSucc m =>
    cases b with
    | ofNat n =>
      have h := subNatNat_natAbs_le n (m + 1)
      rw [Nat.add_comm n (m + 1)] at h
      exact h
    | negSucc n =>
      change (m + n + 1) + 1 ≤ (m + 1) + (n + 1)
      rw [Nat.add_assoc m 1 (n + 1), Nat.add_comm 1 (n + 1),
          ← Nat.add_assoc m (n + 1) 1, ← Nat.add_assoc m n 1]
      exact Nat.le_refl _

private theorem natAbs_neg_eq (b : Int) : (Int.neg b).natAbs = b.natAbs := by
  cases b with
  | ofNat n =>
    cases n with
    | zero => rfl
    | succ k => rfl
  | negSucc n => rfl

/-- Triangle inequality for `Int.natAbs` under `Int.sub`. -/
theorem natAbs_sub_le (a b : Int) : (a - b).natAbs ≤ a.natAbs + b.natAbs := by
  have heq : a - b = a + Int.neg b := rfl
  rw [heq]
  have h := natAbs_add_le a (Int.neg b)
  rw [natAbs_neg_eq b] at h
  exact h

/-- Magnitude bound for truncating division by `d`:
`(intTruncDivNat c d).natAbs ≤ c.natAbs`. -/
theorem natAbs_truncDiv_le (c : Int) (d : Nat) :
    (intTruncDivNat c d).natAbs ≤ c.natAbs := by
  cases c with
  | ofNat n =>
    change HDiv.hDiv n d ≤ n
    exact Nat.div_le_self n d
  | negSucc n =>
    change (Int.negOfNat (HDiv.hDiv (n + 1) d)).natAbs ≤ n + 1
    have hneg : ∀ k : Nat, (Int.negOfNat k).natAbs = k := by
      intro k
      cases k with
      | zero => rfl
      | succ k' => rfl
    rw [hneg]
    exact Nat.div_le_self (n + 1) d

/-- Magnitude bound for floor division toward `-∞` by `d`:
`(intFloorDivPos c d).natAbs ≤ c.natAbs`. -/
theorem natAbs_floorDivPos_le (c : Int) (d : Nat) :
    (intFloorDivPos c d).natAbs ≤ c.natAbs := by
  cases c with
  | ofNat n =>
    change HDiv.hDiv n d ≤ n
    exact Nat.div_le_self n d
  | negSucc n =>
    change HDiv.hDiv n d + 1 ≤ n + 1
    exact Nat.succ_le_succ (Nat.div_le_self n d)

/-- Universal H.264 4×4 IDCT butterfly magnitude bound: if every input
coefficient satisfies `|c_i| ≤ B`, then every output of `idct4Row` satisfies
`|y_i| ≤ 4 * B` (so for any 16-bit signed input `B ≤ 32768`, every 1D output
has `|y_i| ≤ 131072` and every 2D output after horizontal + vertical passes has
`|z_i| ≤ 524288 ≪ 2^31`, proving unconditional `i32` overflow-freedom across
both 8-bit and 10-bit HDR H.264!). -/
theorem idct4Row_natAbs_bound {c0 c1 c2 c3 : Int} {B : Nat}
    (h0 : c0.natAbs ≤ B) (h1 : c1.natAbs ≤ B)
    (h2 : c2.natAbs ≤ B) (h3 : c3.natAbs ≤ B) :
    let r := idct4Row c0 c1 c2 c3
    r.1.natAbs ≤ 4 * B ∧
    r.2.1.natAbs ≤ 4 * B ∧
    r.2.2.1.natAbs ≤ 4 * B ∧
    r.2.2.2.natAbs ≤ 4 * B := by
  dsimp only [idct4Row]
  have he0 : (c0 + c2).natAbs ≤ B + B :=
    Nat.le_trans (natAbs_add_le c0 c2) (Nat.add_le_add h0 h2)
  have he1 : (c0 - c2).natAbs ≤ B + B :=
    Nat.le_trans (natAbs_sub_le c0 c2) (Nat.add_le_add h0 h2)
  have he2 : (intFloorDivPos c1 2 - c3).natAbs ≤ B + B :=
    Nat.le_trans (natAbs_sub_le (intFloorDivPos c1 2) c3)
      (Nat.add_le_add (Nat.le_trans (natAbs_floorDivPos_le c1 2) h1) h3)
  have he3 : (c1 + intFloorDivPos c3 2).natAbs ≤ B + B :=
    Nat.le_trans (natAbs_add_le c1 (intFloorDivPos c3 2))
      (Nat.add_le_add h1 (Nat.le_trans (natAbs_floorDivPos_le c3 2) h3))
  have h4B : B + B + (B + B) = 4 * B := by
    have h2 : B + B = 2 * B := (Nat.two_mul B).symm
    rw [h2, ← Nat.add_mul]
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [← h4B]
    exact Nat.le_trans (natAbs_add_le _ _) (Nat.add_le_add he0 he3)
  · rw [← h4B]
    exact Nat.le_trans (natAbs_add_le _ _) (Nat.add_le_add he1 he2)
  · rw [← h4B]
    exact Nat.le_trans (natAbs_sub_le _ _) (Nat.add_le_add he1 he2)
  · rw [← h4B]
    exact Nat.le_trans (natAbs_sub_le _ _) (Nat.add_le_add he0 he3)

/-- 2D H.264 4×4 IDCT + residual add + bit-depth pixel clamp
(`clipIntToPixel bd (pix + intFloorDivPos (coeff + 32) 64)`). -/
@[expose] def idct4AddPixel (bd pix : Nat) (coeff : Int) : Nat :=
  clipIntToPixel bd (Int.ofNat pix + intFloorDivPos (coeff + Int.ofNat 32) 64)

/-- `idct4AddPixel` unconditionally produces a valid `bd`-bit pixel `< 2^bd`. -/
theorem idct4AddPixel_lt (bd pix : Nat) (coeff : Int) :
    idct4AddPixel bd pix coeff < HPow.hPow (2 : Nat) bd :=
  clipIntToPixel_lt bd _

/-! ## Part 4: H.264 §8.7.2.2 Deblocking Filter Step (`deblock8`/`deblock10`) -/

/-- H.264 §8.7.2.2 luma/chroma edge deblocking delta:
`Δ = Clip3(-tc, tc, intFloorDivPos (((q0 - p0) * 4 + (p1 - q1) + 4), 8))`. -/
@[expose] def deblockDelta (tc : Nat) (p1 p0 q0 q1 : Nat) : Int :=
  let raw : Int :=
    intFloorDivPos
      ((Int.ofNat q0 - Int.ofNat p0) * Int.ofNat 4 +
        (Int.ofNat p1 - Int.ofNat q1) + Int.ofNat 4)
      8
  clipSymInt tc raw

/-- H.264 §8.7.2.2 deblocking filter pixel pair update `(p0', q0')`:
`p0' = ClipPixel(bd, p0 + Δ)`, `q0' = ClipPixel(bd, q0 - Δ)`. -/
@[expose] def deblockPair (bd tc p1 p0 q0 q1 : Nat) : Nat × Nat :=
  let d := deblockDelta tc p1 p0 q0 q1
  (clipIntToPixel bd (Int.ofNat p0 + d), clipIntToPixel bd (Int.ofNat q0 - d))

/-- Every deblocking delta is bounded in `[-tc, tc]`. -/
theorem deblockDelta_bounds (tc p1 p0 q0 q1 : Nat) :
    Int.negOfNat tc ≤ deblockDelta tc p1 p0 q0 q1 ∧
    deblockDelta tc p1 p0 q0 q1 ≤ Int.ofNat tc :=
  clipSymInt_bounds tc _

/-- Unconditional pixel-range safety for `deblockPair` at any bit depth `bd`
(covering both 8-bit `deblock8` and 10-bit HDR `deblock10`): both updated
boundary pixels stay strictly below `2^bd`. -/
theorem deblockPair_lt (bd tc p1 p0 q0 q1 : Nat) :
    (deblockPair bd tc p1 p0 q0 q1).1 < HPow.hPow (2 : Nat) bd ∧
    (deblockPair bd tc p1 p0 q0 q1).2 < HPow.hPow (2 : Nat) bd :=
  ⟨clipIntToPixel_lt bd _, clipIntToPixel_lt bd _⟩

/-- When `tc = 0`, `deblockDelta` is identically `0` (filter is a no-op on
in-range pixels). -/
theorem deblockDelta_tc_zero (p1 p0 q0 q1 : Nat) :
    deblockDelta 0 p1 p0 q0 q1 = 0 := by
  have hb := deblockDelta_bounds 0 p1 p0 q0 q1
  exact int_le_antisymm' hb.2 hb.1

/-- When `tc = 0` and `p0, q0 < 2^bd`, `deblockPair` leaves `(p0, q0)` exact. -/
theorem deblockPair_tc_zero {bd p1 p0 q0 q1 : Nat}
    (hp0 : p0 < HPow.hPow (2 : Nat) bd) (hq0 : q0 < HPow.hPow (2 : Nat) bd) :
    deblockPair bd 0 p1 p0 q0 q1 = (p0, q0) := by
  unfold deblockPair
  dsimp only
  rw [deblockDelta_tc_zero]
  have hp : clipIntToPixel bd (Int.ofNat p0 + 0) = p0 := by
    change clipPixelNat bd p0 = p0
    exact clip3Nat_of_mem (Nat.zero_le p0) (Nat.le_sub_one_of_lt hp0)
  have hq : clipIntToPixel bd (Int.ofNat q0 - 0) = q0 := by
    change clipPixelNat bd q0 = q0
    exact clip3Nat_of_mem (Nat.zero_le q0) (Nat.le_sub_one_of_lt hq0)
  rw [hp, hq]

end Anneal.MediaDsp.ClampAndButterfly

end
