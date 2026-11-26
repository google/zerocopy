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
public import Init.Data.Nat.Basic
public import Init.Data.Int.Basic
public import Anneal.LinearArith

public section

/-!
# Division-Free Dyadic Jury-Stein-Lyapunov Certificates (`JuryStein`)

Zero-TCB algebraic certification of discrete-time second-order biquad/IIR
filter stability, quadratic Lyapunov contraction, division-free coordinatewise
ellipsoid bounds, and coupled normal-form symmetric saturation non-expansiveness
over exact scaled integers (`Int`, covering Q-format / dyadic coefficients with
scale `S = 2^k` and zero floating-point rounding axioms):

1. **Scaled Integer Representation & Jury Margins:**
   - `pow2Int` (`@Nat.rec`, `0` `._unsafe_rec`),
     homogeneous Jury margins `juryJ1`, `juryJ2`, `juryJ3`, determinant
     `juryDelta := J₁ * J₂ * J₃`, and `JuryStable S a₁ a₂`.
2. **Division-Free Polynomial Stein-Lyapunov Certificate (`steinP11`,
   `steinP12`, `steinP22`, `steinDet`):**
   - `stein_lyapunov_entry11`, `stein_lyapunov_entry12`, and
     `stein_lyapunov_entry22`: prove the exact universal ring identity
     `S² · P̃ - (S · A_c)ᵀ · P̃ · (S · A_c) = S² · Δ · I₂` over `ℤ[S, a₁, a₂]`.
   - `stein_det_factor` and `stein_pos_def_of_jury`: prove
     `det P̃ = 2 S² (S + a₂) Δ + 4 S² a₂² J₂ J₃ > 0`, `P₁₁ > 0`, `P₂₂ > 0`.
3. **Quadratic Contraction & Division-Free Ellipsoid Bounds:**
   - `quadForm`, `stein_quad_contraction`, `quadForm_complete_sq_1`,
     `quadForm_complete_sq_2`, `ellipsoid_coord_bounds`
     (`x₁² · det ≤ P₂₂ · Q(x)` and `x₂² · det ≤ P₁₁ · Q(x)` without roots or
     divisions), and `stein_quad_pos_of_jury`.
4. **Euclidean Companion Failure & Coupled Normal Form Saturation:**
   - `euclidean_fails_companion`: proves unweighted Euclidean norm expands on
     `(S, 0)` whenever `a₁ ≠ 0` and `S ≠ 0`.
   - `coupled_normal_l2_identity`, symmetric saturation `satSym`,
     `satSym_sq_le`, and `coupled_normal_sat_contraction` (proving homogeneous
     `‖sat(y)‖₂² ≤ (α² + β²) ‖x‖₂²` non-expansiveness for diagonal `P = I₂`
     coupled normal-form state updates).

All definitions are computable (`0` `._unsafe_rec`, `0` `noncomputable`, `0`
`omega`, `0` `decide`) and every declaration compiles using at most `[propext]`
(`0` `Classical.choice`, `0` `Quot.sound`).
-/

namespace Anneal.Float.JuryStein

open Anneal.LinearArith

/-! ## Part I: Constructive `Int` Ring & Order Helpers via `IntBalance` -/

private theorem intBalance_eq_int {x y : Int} {px nx py ny : Nat}
    (hx : IntBalance x px nx) (hy : IntBalance y py ny)
    (hEq : px + ny = py + nx) : x = y := by
  have h1 : x ≤ y := (intBalance_le hx hy).mpr (by rw [hEq]; exact Nat.le_refl _)
  have h2 : y ≤ x := (intBalance_le hy hx).mpr (by rw [hEq]; exact Nat.le_refl _)
  have hSub1 : IntBalance (Int.sub y x) (py + nx) (ny + px) :=
    intBalance_sub hy hx
  cases hD : Int.sub y x with
  | negSucc _ =>
    change Int.NonNeg (Int.sub y x) at h1
    rw [hD] at h1
    nomatch h1
  | ofNat m =>
    rw [hD] at hSub1
    dsimp only [IntBalance, intPos, intNeg] at hSub1
    rw [Nat.zero_add, Nat.add_comm ny px, hEq] at hSub1
    have hm0 : m = 0 := by
      have h' : m + (py + nx) = 0 + (py + nx) := by
        rw [Nat.zero_add]
        exact hSub1
      exact Nat.add_right_cancel h'
    -- Use x ≤ y ∧ y ≤ x directly on cases of x, y
    have hxy := (intBalance_le (intBalance_self x) (intBalance_self y)).mp h1
    have hyx := (intBalance_le (intBalance_self y) (intBalance_self x)).mp h2
    have hBalEq : intPos x + intNeg y = intPos y + intNeg x :=
      Nat.le_antisymm hxy hyx
    cases x with
    | ofNat a =>
      cases y with
      | ofNat b =>
        dsimp only [intPos, intNeg] at hBalEq
        rw [Nat.add_zero, Nat.add_zero] at hBalEq
        exact congrArg Int.ofNat hBalEq
      | negSucc b =>
        dsimp only [intPos, intNeg] at hBalEq
        rw [Nat.zero_add, Nat.add_zero] at hBalEq
        exact nomatch hBalEq
    | negSucc a =>
      cases y with
      | ofNat b =>
        dsimp only [intPos, intNeg] at hBalEq
        rw [Nat.zero_add, Nat.add_zero] at hBalEq
        exact nomatch hBalEq.symm
      | negSucc b =>
        dsimp only [intPos, intNeg] at hBalEq
        rw [Nat.zero_add, Nat.zero_add] at hBalEq
        exact congrArg Int.negSucc (Nat.succ.inj hBalEq.symm)

private theorem int_add_comm_dc (x y : Int) :
    Int.add x y = Int.add y x :=
  intBalance_eq_int
    (intBalance_add (intBalance_self x) (intBalance_self y))
    (intBalance_add (intBalance_self y) (intBalance_self x))
    (by
      rw [Nat.add_comm (intPos x) (intPos y),
        Nat.add_comm (intNeg y) (intNeg x)])

private theorem int_add_assoc_dc (x y z : Int) :
    Int.add (Int.add x y) z = Int.add x (Int.add y z) :=
  intBalance_eq_int
    (intBalance_add (intBalance_add (intBalance_self x) (intBalance_self y))
      (intBalance_self z))
    (intBalance_add (intBalance_self x)
      (intBalance_add (intBalance_self y) (intBalance_self z)))
    (by rw [Nat.add_assoc, Nat.add_assoc, Nat.add_assoc, Nat.add_assoc,
      Nat.add_assoc])

private theorem int_add_zero_dc (x : Int) :
    Int.add x (Int.ofNat 0) = x :=
  intBalance_eq_int
    (intBalance_add (intBalance_self x) (intBalance_ofNat 0))
    (intBalance_self x)
    (by rw [Nat.add_zero, Nat.add_zero])

private theorem int_zero_add_dc (x : Int) :
    Int.add (Int.ofNat 0) x = x := by
  rw [int_add_comm_dc, int_add_zero_dc]

private theorem int_mul_comm_dc (x y : Int) :
    Int.mul x y = Int.mul y x :=
  intBalance_eq_int
    (intBalance_mul (intBalance_self x) (intBalance_self y))
    (intBalance_mul (intBalance_self y) (intBalance_self x))
    (by
      rw [Nat.mul_comm (intPos x) (intPos y),
        Nat.mul_comm (intNeg x) (intNeg y),
        Nat.mul_comm (intPos y) (intNeg x),
        Nat.mul_comm (intNeg y) (intPos x),
        Nat.add_comm (intNeg x * intPos y) (intPos x * intNeg y)])

private theorem int_mul_zero_dc (x : Int) :
    Int.mul x (Int.ofNat 0) = Int.ofNat 0 :=
  intBalance_eq_int
    (intBalance_mul (intBalance_self x) (intBalance_ofNat 0))
    (intBalance_ofNat 0)
    (by rw [Nat.mul_zero, Nat.mul_zero, Nat.add_zero])

private theorem int_zero_mul_dc (x : Int) :
    Int.mul (Int.ofNat 0) x = Int.ofNat 0 := by
  rw [int_mul_comm_dc, int_mul_zero_dc]

private theorem int_mul_one_dc (x : Int) :
    Int.mul x (Int.ofNat 1) = x :=
  intBalance_eq_int
    (intBalance_mul (intBalance_self x) (intBalance_ofNat 1))
    (intBalance_self x)
    (by rw [Nat.mul_one, Nat.mul_zero, Nat.add_zero, Nat.mul_zero, Nat.mul_one,
      Nat.zero_add])

private theorem int_one_mul_dc (x : Int) :
    Int.mul (Int.ofNat 1) x = x := by
  rw [int_mul_comm_dc, int_mul_one_dc]

private theorem nat_add4_swap (a b c d : Nat) :
    (a + b) + (c + d) = (a + c) + (b + d) := by
  rw [Nat.add_assoc a b, ← Nat.add_assoc b c d, Nat.add_comm b c,
    Nat.add_assoc c b d, ← Nat.add_assoc a c]

private theorem int_mul_assoc_dc (x y z : Int) :
    Int.mul (Int.mul x y) z = Int.mul x (Int.mul y z) :=
  intBalance_eq_int
    (intBalance_mul (intBalance_mul (intBalance_self x) (intBalance_self y))
      (intBalance_self z))
    (intBalance_mul (intBalance_self x)
      (intBalance_mul (intBalance_self y) (intBalance_self z)))
    (by
      rw [Nat.add_mul, Nat.add_mul, Nat.add_mul, Nat.add_mul,
        Nat.mul_add, Nat.mul_add, Nat.mul_add, Nat.mul_add]
      rw [Nat.mul_assoc, Nat.mul_assoc, Nat.mul_assoc, Nat.mul_assoc,
        Nat.mul_assoc, Nat.mul_assoc, Nat.mul_assoc, Nat.mul_assoc]
      have hL :
          (intPos x * (intPos y * intPos z) + intNeg x * (intNeg y * intPos z)) +
              (intPos x * (intNeg y * intNeg z) + intNeg x * (intPos y * intNeg z)) =
            (intPos x * (intPos y * intPos z) + intPos x * (intNeg y * intNeg z)) +
              (intNeg x * (intPos y * intNeg z) + intNeg x * (intNeg y * intPos z)) := by
        rw [nat_add4_swap,
          Nat.add_comm (intNeg x * (intNeg y * intPos z))
            (intNeg x * (intPos y * intNeg z))]
      have hR :
          (intPos x * (intPos y * intNeg z) + intNeg x * (intNeg y * intNeg z)) +
              (intPos x * (intNeg y * intPos z) + intNeg x * (intPos y * intPos z)) =
            (intPos x * (intPos y * intNeg z) + intPos x * (intNeg y * intPos z)) +
              (intNeg x * (intPos y * intPos z) + intNeg x * (intNeg y * intNeg z)) := by
        rw [nat_add4_swap,
          Nat.add_comm (intNeg x * (intNeg y * intNeg z))
            (intNeg x * (intPos y * intPos z))]
      rw [hL, hR])

private theorem int_mul_add_dc (x y z : Int) :
    Int.mul x (Int.add y z) = Int.add (Int.mul x y) (Int.mul x z) :=
  intBalance_eq_int
    (intBalance_mul (intBalance_self x)
      (intBalance_add (intBalance_self y) (intBalance_self z)))
    (intBalance_add
      (intBalance_mul (intBalance_self x) (intBalance_self y))
      (intBalance_mul (intBalance_self x) (intBalance_self z)))
    (by
      rw [Nat.mul_add, Nat.mul_add, Nat.mul_add, Nat.mul_add]
      rw [nat_add4_swap (intPos x * intPos y) (intPos x * intPos z),
        nat_add4_swap (intPos x * intNeg y) (intPos x * intNeg z)])

private theorem int_add_mul_dc (x y z : Int) :
    Int.mul (Int.add x y) z = Int.add (Int.mul x z) (Int.mul y z) := by
  rw [int_mul_comm_dc, int_mul_add_dc, int_mul_comm_dc z x,
    int_mul_comm_dc z y]

private theorem int_sub_eq_add_neg_dc (x y : Int) :
    Int.sub x y = Int.add x (Int.neg y) :=
  intBalance_eq_int
    (intBalance_sub (intBalance_self x) (intBalance_self y))
    (intBalance_add (intBalance_self x) (intBalance_neg (intBalance_self y)))
    rfl

private theorem int_neg_neg_dc (x : Int) : Int.neg (Int.neg x) = x :=
  intBalance_eq_int
    (intBalance_neg (intBalance_neg (intBalance_self x)))
    (intBalance_self x)
    rfl

private theorem int_neg_add_dc (x y : Int) :
    Int.neg (Int.add x y) = Int.add (Int.neg x) (Int.neg y) :=
  intBalance_eq_int
    (intBalance_neg (intBalance_add (intBalance_self x) (intBalance_self y)))
    (intBalance_add (intBalance_neg (intBalance_self x))
      (intBalance_neg (intBalance_self y)))
    rfl

private theorem int_neg_mul_dc (x y : Int) :
    Int.mul (Int.neg x) y = Int.neg (Int.mul x y) :=
  intBalance_eq_int
    (intBalance_mul (intBalance_neg (intBalance_self x)) (intBalance_self y))
    (intBalance_neg (intBalance_mul (intBalance_self x) (intBalance_self y)))
    (by
      rw [Nat.add_comm (intNeg x * intPos y) (intPos x * intNeg y),
        Nat.add_comm (intPos x * intPos y) (intNeg x * intNeg y)])

private theorem int_mul_neg_dc (x y : Int) :
    Int.mul x (Int.neg y) = Int.neg (Int.mul x y) := by
  rw [int_mul_comm_dc, int_neg_mul_dc, int_mul_comm_dc]

private theorem int_add_neg_cancel_dc (x : Int) :
    Int.add x (Int.neg x) = Int.ofNat 0 :=
  intBalance_eq_int
    (intBalance_add (intBalance_self x) (intBalance_neg (intBalance_self x)))
    (intBalance_ofNat 0)
    (by rw [Nat.add_zero, Nat.zero_add, Nat.add_comm])

private theorem int_sub_self_dc (x : Int) :
    Int.sub x x = Int.ofNat 0 := by
  rw [int_sub_eq_add_neg_dc, int_add_neg_cancel_dc]

private theorem int_mul_sub_dc (x y z : Int) :
    Int.mul x (Int.sub y z) = Int.sub (Int.mul x y) (Int.mul x z) := by
  rw [int_sub_eq_add_neg_dc, int_mul_add_dc, int_mul_neg_dc,
    ← int_sub_eq_add_neg_dc]

private theorem int_sub_mul_dc (x y z : Int) :
    Int.mul (Int.sub x y) z = Int.sub (Int.mul x z) (Int.mul y z) := by
  rw [int_mul_comm_dc, int_mul_sub_dc, int_mul_comm_dc z x,
    int_mul_comm_dc z y]

private theorem int_add_sub_cancel_dc (x y : Int) :
    Int.sub (Int.add x y) y = x := by
  rw [int_sub_eq_add_neg_dc, int_add_assoc_dc, int_add_neg_cancel_dc,
    int_add_zero_dc]

private theorem int_sub_add_cancel_dc (x y : Int) :
    Int.add (Int.sub x y) y = x := by
  rw [int_sub_eq_add_neg_dc, int_add_assoc_dc, int_add_comm_dc (Int.neg y) y,
    int_add_neg_cancel_dc, int_add_zero_dc]

private theorem int_two_mul_dc (x : Int) :
    Int.mul (Int.ofNat 2) x = Int.add x x := by
  have h2 : Int.ofNat 2 = Int.add (Int.ofNat 1) (Int.ofNat 1) := rfl
  rw [h2, int_add_mul_dc, int_one_mul_dc]

private theorem int_diff_sq_dc (u v : Int) :
    Int.mul (Int.sub u v) (Int.add u v) =
      Int.sub (Int.mul u u) (Int.mul v v) := by
  rw [int_sub_mul_dc, int_mul_add_dc, int_mul_add_dc,
    int_sub_eq_add_neg_dc, int_neg_add_dc, int_mul_comm_dc v u]
  rw [int_add_assoc_dc, ← int_add_assoc_dc (Int.mul u v),
    int_add_neg_cancel_dc, int_zero_add_dc, ← int_sub_eq_add_neg_dc]

/-- Strict positivity on `Int`: `0 < x` means `Int.ofNat 1 ≤ x`. -/
@[expose] def IntPos (x : Int) : Prop :=
  Int.ofNat 1 ≤ x

/-- Non-negativity on `Int`: `0 ≤ x` means `Int.ofNat 0 ≤ x`. -/
@[expose] def IntNonNeg (x : Int) : Prop :=
  Int.ofNat 0 ≤ x

/-- Every square `x * x` is non-negative (`[propext]` only). -/
theorem int_sq_nonneg (x : Int) : IntNonNeg (Int.mul x x) := by
  dsimp only [IntNonNeg]
  have hSq := intBalance_mul (intBalance_self x) (intBalance_self x)
  apply (intBalance_le (intBalance_ofNat 0) hSq).mpr
  rw [Nat.zero_add, Nat.add_zero]
  cases x with
  | ofNat a =>
    dsimp only [intPos, intNeg]
    rw [Nat.mul_zero, Nat.zero_mul, Nat.add_zero]
    exact Nat.zero_le _
  | negSucc a =>
    dsimp only [intPos, intNeg]
    rw [Nat.zero_mul, Nat.mul_zero, Nat.add_zero]
    exact Nat.zero_le _

/-- Every non-zero integer has strictly positive square (`[propext]` only). -/
theorem int_sq_pos_of_ne_zero {x : Int} (hNe : x ≠ Int.ofNat 0) :
    IntPos (Int.mul x x) := by
  dsimp only [IntPos]
  have hSq := intBalance_mul (intBalance_self x) (intBalance_self x)
  apply (intBalance_le (intBalance_ofNat 1) hSq).mpr
  rw [Nat.add_zero]
  cases x with
  | ofNat a =>
    cases a with
    | zero => exact False.elim (hNe rfl)
    | succ a' =>
      dsimp only [intPos, intNeg]
      rw [Nat.mul_zero, Nat.zero_mul, Nat.add_zero, Nat.add_zero]
      exact Nat.mul_pos (Nat.zero_lt_succ a') (Nat.zero_lt_succ a')
  | negSucc a =>
    dsimp only [intPos, intNeg]
    rw [Nat.zero_mul, Nat.mul_zero, Nat.add_zero, Nat.add_zero, Nat.zero_add]
    exact Nat.mul_pos (Nat.zero_lt_succ a) (Nat.zero_lt_succ a)

/-- Product of two strictly positive `Int`s is strictly positive (`[propext]`
only). -/
theorem int_mul_pos_of_pos {x y : Int} (hx : IntPos x) (hy : IntPos y) :
    IntPos (Int.mul x y) := by
  dsimp only [IntPos] at hx hy
  dsimp only [IntPos]
  have h1 := (intBalance_le (intBalance_ofNat 1) (intBalance_self x)).mp hx
  have h2 := (intBalance_le (intBalance_ofNat 1) (intBalance_self y)).mp hy
  rw [Nat.add_zero] at h1 h2
  cases x with
  | negSucc _ =>
    dsimp only [intPos, intNeg] at h1
    rw [Nat.add_zero] at h1
    exact False.elim (Nat.not_lt_zero _ h1)
  | ofNat a =>
    cases y with
    | negSucc _ =>
      dsimp only [intPos, intNeg] at h2
      rw [Nat.add_zero] at h2
      exact False.elim (Nat.not_lt_zero _ h2)
    | ofNat b =>
      dsimp only [intPos, intNeg] at h1 h2
      rw [Nat.add_zero] at h1 h2
      have hProd : 1 ≤ a * b := Nat.mul_pos h1 h2
      exact (intBalance_le (intBalance_ofNat 1) (intBalance_ofNat (a * b))).mpr
        (by rw [Nat.add_zero, Nat.add_zero]; exact hProd)

/-- Product of two non-negative `Int`s is non-negative (`[propext]` only). -/
theorem int_mul_nonneg {x y : Int} (hx : IntNonNeg x) (hy : IntNonNeg y) :
    IntNonNeg (Int.mul x y) := by
  dsimp only [IntNonNeg] at hx hy
  dsimp only [IntNonNeg]
  have h1 := (intBalance_le (intBalance_ofNat 0) (intBalance_self x)).mp hx
  have h2 := (intBalance_le (intBalance_ofNat 0) (intBalance_self y)).mp hy
  cases x with
  | negSucc a =>
    dsimp only [intPos, intNeg] at h1
    rw [Nat.zero_add, Nat.add_zero] at h1
    exact False.elim (Nat.not_lt_zero a h1)
  | ofNat a =>
    cases y with
    | negSucc b =>
      dsimp only [intPos, intNeg] at h2
      rw [Nat.zero_add, Nat.add_zero] at h2
      exact False.elim (Nat.not_lt_zero b h2)
    | ofNat b =>
      exact (intBalance_le (intBalance_ofNat 0) (intBalance_ofNat (a * b))).mpr
        (Nat.zero_le _)

/-- Non-negative from positive (`[propext]` only). -/
theorem int_nonneg_of_pos {x : Int} (hx : IntPos x) : IntNonNeg x := by
  dsimp only [IntPos] at hx
  dsimp only [IntNonNeg]
  have h1 := (intBalance_le (intBalance_ofNat 1) (intBalance_self x)).mp hx
  apply (intBalance_le (intBalance_ofNat 0) (intBalance_self x)).mpr
  exact Nat.le_trans (Nat.add_le_add_right (Nat.zero_le 1) (intNeg x)) h1

/-- Sum of positive and non-negative `Int`s is strictly positive (`[propext]`
only). -/
theorem int_add_pos_nonneg {x y : Int} (hx : IntPos x) (hy : IntNonNeg y) :
    IntPos (Int.add x y) := by
  dsimp only [IntPos] at hx
  dsimp only [IntNonNeg] at hy
  dsimp only [IntPos]
  have h1 := (intBalance_le (intBalance_ofNat 1) (intBalance_self x)).mp hx
  have h2 := (intBalance_le (intBalance_ofNat 0) (intBalance_self y)).mp hy
  rw [Nat.add_zero] at h1
  rw [Nat.zero_add, Nat.add_zero] at h2
  apply (intBalance_le (intBalance_ofNat 1)
    (intBalance_add (intBalance_self x) (intBalance_self y))).mpr
  rw [Nat.add_zero, ← Nat.add_assoc]
  exact Nat.add_le_add h1 h2

/-- Sum of two non-negative `Int`s is non-negative (`[propext]` only). -/
theorem int_add_nonneg {x y : Int} (hx : IntNonNeg x) (hy : IntNonNeg y) :
    IntNonNeg (Int.add x y) := by
  dsimp only [IntNonNeg] at hx hy
  dsimp only [IntNonNeg]
  have h1 := (intBalance_le (intBalance_ofNat 0) (intBalance_self x)).mp hx
  have h2 := (intBalance_le (intBalance_ofNat 0) (intBalance_self y)).mp hy
  rw [Nat.zero_add, Nat.add_zero] at h1 h2
  apply (intBalance_le (intBalance_ofNat 0)
    (intBalance_add (intBalance_self x) (intBalance_self y))).mpr
  rw [Nat.zero_add, Nat.add_zero]
  exact Nat.add_le_add h1 h2

/-- `x ≤ y` iff `0 ≤ y - x` (`[propext]` only). -/
theorem int_le_iff_sub_nonneg (x y : Int) :
    x ≤ y ↔ IntNonNeg (Int.sub y x) := by
  dsimp only [IntNonNeg]
  have h1 := intBalance_le (intBalance_self x) (intBalance_self y)
  have h2 := intBalance_le (intBalance_ofNat 0)
    (intBalance_sub (intBalance_self y) (intBalance_self x))
  rw [h1, h2, Nat.zero_add, Nat.add_zero, Nat.add_comm (intNeg y) (intPos x),
    Nat.add_comm (intPos y) (intNeg x)]

/-- `0 < x` and `0 ≤ y` and `x = y`? Helper: `0 ≤ a * b` + `0 < a` implies
`0 ≤ b` (`[propext]` only). -/
theorem int_nonneg_of_mul_nonneg_left {a b : Int}
    (ha : IntPos a) (hab : IntNonNeg (Int.mul a b)) :
    IntNonNeg b := by
  dsimp only [IntPos] at ha
  dsimp only [IntNonNeg] at hab
  dsimp only [IntNonNeg]
  have h1 := (intBalance_le (intBalance_ofNat 1) (intBalance_self a)).mp ha
  have h2 := (intBalance_le (intBalance_ofNat 0) (intBalance_self (Int.mul a b))).mp hab
  cases a with
  | negSucc _ =>
    dsimp only [intPos, intNeg] at h1
    rw [Nat.add_zero, Nat.add_zero] at h1
    exact False.elim (Nat.not_lt_zero _ h1)
  | ofNat an =>
    dsimp only [intPos, intNeg] at h1
    rw [Nat.add_zero, Nat.add_zero] at h1
    cases b with
    | ofNat bn =>
      exact (intBalance_le (intBalance_ofNat 0) (intBalance_ofNat bn)).mpr
        (Nat.zero_le _)
    | negSucc bn =>
      have hMul := intBalance_mul (intBalance_ofNat an)
        (intBalance_self (Int.negSucc bn))
      have h2' := (intBalance_le (intBalance_ofNat 0) hMul).mp hab
      dsimp only [intPos, intNeg] at h2'
      rw [Nat.mul_zero, Nat.zero_mul, Nat.add_zero, Nat.add_zero,
        Nat.zero_add] at h2'
      have hPosProd : 0 < an * (bn + 1) :=
        Nat.mul_pos h1 (Nat.zero_lt_succ bn)
      exact False.elim (Nat.not_lt_of_ge h2' hPosProd)

/-- `0 < a` and `0 < a * b` imply `0 < b` (`[propext]` only). -/
theorem int_pos_of_mul_pos_left {a b : Int}
    (ha : IntPos a) (hab : IntPos (Int.mul a b)) :
    IntPos b := by
  have hNonNeg := int_nonneg_of_mul_nonneg_left ha (int_nonneg_of_pos hab)
  cases b with
  | negSucc bn =>
    have hBad := (intBalance_le (intBalance_ofNat 0)
      (intBalance_self (Int.negSucc bn))).mp hNonNeg
    dsimp only [intPos, intNeg] at hBad
    rw [Nat.zero_add, Nat.add_zero] at hBad
    exact False.elim (Nat.not_lt_zero bn hBad)
  | ofNat bn =>
    cases bn with
    | zero =>
      rw [int_mul_zero_dc] at hab
      have hBad := (intBalance_le (intBalance_ofNat 1)
        (intBalance_ofNat 0)).mp hab
      rw [Nat.add_zero, Nat.add_zero] at hBad
      exact False.elim (Nat.not_lt_zero 0 hBad)
    | succ bn' =>
      exact (intBalance_le (intBalance_ofNat 1) (intBalance_ofNat (bn' + 1))).mpr
        (by rw [Nat.add_zero, Nat.add_zero]; exact Nat.zero_lt_succ bn')

/-! ## Part II: Power-of-Two Scale & Division-Free Jury-Stein Certificate -/

/-- Exact power of two `2^k` as `Int` via `@Nat.rec` (`0` `._unsafe_rec`). -/
@[expose] def pow2Int (k : Nat) : Int :=
  Int.ofNat (@Nat.rec (fun _ => Nat) 1 (fun _ ih => ih + ih) k)

private theorem pow2Nat_ge_one_dc :
    ∀ n : Nat, 1 ≤ @Nat.rec (fun _ => Nat) 1 (fun _ ih => ih + ih) n
  | 0 => Nat.le_refl 1
  | m + 1 => Nat.le_trans (pow2Nat_ge_one_dc m) (Nat.le_add_right _ _)

/-- `0 < pow2Int k` for every `k : Nat` (`[propext]` only). -/
theorem pow2Int_pos (k : Nat) : IntPos (pow2Int k) := by
  dsimp only [IntPos, pow2Int]
  exact (intBalance_le (intBalance_ofNat 1) (intBalance_ofNat _)).mpr
    (by rw [Nat.add_zero, Nat.add_zero]; exact pow2Nat_ge_one_dc k)

/-- First linear Jury margin `J₁ = S - a₂`
(for `D(z) = z² + (a₁/S) z + a₂/S`). -/
@[expose] def juryJ1 (S a₂ : Int) : Int :=
  Int.sub S a₂

/-- Second linear Jury margin `J₂ = S + a₂ - a₁`. -/
@[expose] def juryJ2 (S a₁ a₂ : Int) : Int :=
  Int.sub (Int.add S a₂) a₁

/-- Third linear Jury margin `J₃ = S + a₂ + a₁`. -/
@[expose] def juryJ3 (S a₁ a₂ : Int) : Int :=
  Int.add (Int.add S a₂) a₁

/-- Factored Jury-Stein determinant `Δ(S, a₁, a₂) = J₁ · J₂ · J₃`. -/
@[expose] def juryDelta (S a₁ a₂ : Int) : Int :=
  Int.mul (Int.mul (juryJ1 S a₂) (juryJ2 S a₁ a₂)) (juryJ3 S a₁ a₂)

/-- Strict Jury Schur-stability predicate: `S > 0` and all three linear margins
`J₁, J₂, J₃ > 0`. -/
@[expose] def JuryStable (S a₁ a₂ : Int) : Prop :=
  IntPos S ∧ IntPos (juryJ1 S a₂) ∧ IntPos (juryJ2 S a₁ a₂) ∧
    IntPos (juryJ3 S a₁ a₂)

/-- Polynomial Stein-Lyapunov `(1, 1)` entry `P̃₁₁ = 2 S² (S + a₂)`. -/
@[expose] def steinP11 (S a₂ : Int) : Int :=
  Int.mul (Int.mul (Int.ofNat 2) (Int.mul S S)) (Int.add S a₂)

/-- Polynomial Stein-Lyapunov off-diagonal entry `P̃₁₂ = 2 S a₁ a₂`. -/
@[expose] def steinP12 (S a₁ a₂ : Int) : Int :=
  Int.mul (Int.mul (Int.ofNat 2) S) (Int.mul a₁ a₂)

/-- Polynomial Stein-Lyapunov `(2, 2)` entry
`P̃₂₂ = Δ(S, a₁, a₂) + 2 (S + a₂) a₂²`. -/
@[expose] def steinP22 (S a₁ a₂ : Int) : Int :=
  Int.add (juryDelta S a₁ a₂)
    (Int.mul (Int.mul (Int.ofNat 2) (Int.add S a₂)) (Int.mul a₂ a₂))

/-- Determinant `det P̃ = P̃₁₁ P̃₂₂ - P̃₁₂²`. -/
@[expose] def steinDet (S a₁ a₂ : Int) : Int :=
  Int.sub (Int.mul (steinP11 S a₂) (steinP22 S a₁ a₂))
    (Int.mul (steinP12 S a₁ a₂) (steinP12 S a₁ a₂))

/-- Exact `(2, 2)` Stein-Lyapunov polynomial identity (`[propext]` only):
`S² P̃₂₂ - a₂² P̃₁₁ = S² Δ`. -/
theorem stein_lyapunov_entry22 (S a₁ a₂ : Int) :
    Int.sub (Int.mul (Int.mul S S) (steinP22 S a₁ a₂))
      (Int.mul (Int.mul a₂ a₂) (steinP11 S a₂)) =
      Int.mul (Int.mul S S) (juryDelta S a₁ a₂) := by
  dsimp only [steinP22, steinP11]
  rw [int_mul_add_dc]
  have hEq :
      Int.mul (Int.mul S S)
          (Int.mul (Int.mul (Int.ofNat 2) (Int.add S a₂)) (Int.mul a₂ a₂)) =
        Int.mul (Int.mul a₂ a₂)
          (Int.mul (Int.mul (Int.ofNat 2) (Int.mul S S)) (Int.add S a₂)) := by
    rw [int_mul_comm_dc (Int.mul a₂ a₂),
      ← int_mul_assoc_dc (Int.mul S S)
        (Int.mul (Int.ofNat 2) (Int.add S a₂)) (Int.mul a₂ a₂)]
    apply congrArg (fun z => Int.mul z (Int.mul a₂ a₂))
    rw [← int_mul_assoc_dc (Int.mul S S) (Int.ofNat 2) (Int.add S a₂),
      int_mul_comm_dc (Int.mul S S) (Int.ofNat 2)]
  rw [hEq, int_add_sub_cancel_dc]

/-- Exact `(1, 2)` Stein-Lyapunov polynomial identity (`[propext]` only):
`S² P̃₁₂ - (a₁ a₂ P̃₁₁ - S a₂ P̃₁₂) = 0`. -/
theorem stein_lyapunov_entry12 (S a₁ a₂ : Int) :
    Int.sub (Int.mul (Int.mul S S) (steinP12 S a₁ a₂))
      (Int.sub (Int.mul (Int.mul a₁ a₂) (steinP11 S a₂))
        (Int.mul (Int.mul S a₂) (steinP12 S a₁ a₂))) =
      Int.ofNat 0 := by
  dsimp only [steinP11, steinP12]
  have h1 :
      Int.mul (Int.mul a₁ a₂)
          (Int.mul (Int.mul (Int.ofNat 2) (Int.mul S S)) (Int.add S a₂)) =
        Int.add
          (Int.mul (Int.mul S S)
            (Int.mul (Int.mul (Int.ofNat 2) S) (Int.mul a₁ a₂)))
          (Int.mul (Int.mul S a₂)
            (Int.mul (Int.mul (Int.ofNat 2) S) (Int.mul a₁ a₂))) := by
    rw [int_mul_add_dc (Int.mul (Int.ofNat 2) (Int.mul S S)) S a₂,
      int_mul_add_dc]
    have hA :
        Int.mul (Int.mul a₁ a₂)
            (Int.mul (Int.mul (Int.ofNat 2) (Int.mul S S)) S) =
          Int.mul (Int.mul S S)
            (Int.mul (Int.mul (Int.ofNat 2) S) (Int.mul a₁ a₂)) := by
      rw [int_mul_comm_dc (Int.mul a₁ a₂),
        int_mul_assoc_dc (Int.ofNat 2) (Int.mul S S) S,
        int_mul_comm_dc (Int.mul S S) S,
        ← int_mul_assoc_dc (Int.ofNat 2) S (Int.mul S S),
        int_mul_comm_dc (Int.mul (Int.ofNat 2) S) (Int.mul S S),
        int_mul_assoc_dc (Int.mul S S)]
    have hB :
        Int.mul (Int.mul a₁ a₂)
            (Int.mul (Int.mul (Int.ofNat 2) (Int.mul S S)) a₂) =
          Int.mul (Int.mul S a₂)
            (Int.mul (Int.mul (Int.ofNat 2) S) (Int.mul a₁ a₂)) := by
      rw [int_mul_comm_dc (Int.mul a₁ a₂),
        int_mul_assoc_dc (Int.ofNat 2) (Int.mul S S) a₂,
        int_mul_assoc_dc S S a₂,
        ← int_mul_assoc_dc (Int.ofNat 2) S (Int.mul S a₂),
        int_mul_comm_dc (Int.mul (Int.ofNat 2) S) (Int.mul S a₂),
        int_mul_assoc_dc (Int.mul S a₂)]
    rw [hA, hB]
  rw [h1, int_add_sub_cancel_dc, int_sub_self_dc]

private theorem juryDelta_expanded (S a₁ a₂ : Int) :
    juryDelta S a₁ a₂ =
      Int.mul (Int.sub S a₂)
        (Int.sub (Int.mul (Int.add S a₂) (Int.add S a₂)) (Int.mul a₁ a₁)) := by
  dsimp only [juryDelta, juryJ1, juryJ2, juryJ3]
  rw [int_mul_assoc_dc, int_diff_sq_dc]

/-- Exact `(1, 1)` Stein-Lyapunov polynomial identity (`[propext]` only):
`S² P̃₁₁ - (a₁² P̃₁₁ - 2 S a₁ P̃₁₂ + S² P̃₂₂) = S² Δ`. -/
theorem stein_lyapunov_entry11 (S a₁ a₂ : Int) :
    Int.sub (Int.mul (Int.mul S S) (steinP11 S a₂))
      (Int.add
        (Int.sub (Int.mul (Int.mul a₁ a₁) (steinP11 S a₂))
          (Int.mul (Int.mul (Int.ofNat 2) (Int.mul S a₁)) (steinP12 S a₁ a₂)))
        (Int.mul (Int.mul S S) (steinP22 S a₁ a₂))) =
      Int.mul (Int.mul S S) (juryDelta S a₁ a₂) := by
  -- Factor `S²` out of every term on the LHS:
  -- `S² · (2 (S+a₂)(S² - a₂²) - 2 (S-a₂) a₁² - Δ) = S² · (2Δ - Δ) = S² Δ`.
  have hCore :
      Int.sub
        (Int.mul (Int.ofNat 2) (Int.mul (Int.add S a₂)
          (Int.sub (Int.mul S S) (Int.mul a₂ a₂))))
        (Int.mul (Int.ofNat 2) (Int.mul (Int.sub S a₂) (Int.mul a₁ a₁))) =
      Int.add (juryDelta S a₁ a₂) (juryDelta S a₁ a₂) := by
    rw [← int_diff_sq_dc S a₂, ← int_mul_assoc_dc (Int.add S a₂),
      int_mul_comm_dc (Int.add S a₂) (Int.sub S a₂),
      int_mul_assoc_dc (Int.sub S a₂),
      ← int_mul_sub_dc (Int.ofNat 2),
      ← int_mul_sub_dc (Int.sub S a₂),
      ← juryDelta_expanded, int_two_mul_dc]
  -- Rewrite every LHS term as `S² * (...)`
  have hT1 :
      Int.mul (Int.mul S S) (steinP11 S a₂) =
        Int.mul (Int.mul S S)
          (Int.mul (Int.ofNat 2) (Int.mul (Int.add S a₂) (Int.mul S S))) := by
    dsimp only [steinP11]
    rw [int_mul_assoc_dc (Int.ofNat 2) (Int.mul S S) (Int.add S a₂),
      int_mul_comm_dc (Int.mul S S) (Int.add S a₂)]
  have hT2 :
      Int.sub (Int.mul (Int.mul a₁ a₁) (steinP11 S a₂))
          (Int.mul (Int.mul (Int.ofNat 2) (Int.mul S a₁)) (steinP12 S a₁ a₂)) =
        Int.mul (Int.mul S S)
          (Int.mul (Int.ofNat 2) (Int.mul (Int.sub S a₂) (Int.mul a₁ a₁))) := by
    dsimp only [steinP11, steinP12]
    have h2a :
        Int.mul (Int.mul a₁ a₁)
            (Int.mul (Int.mul (Int.ofNat 2) (Int.mul S S)) (Int.add S a₂)) =
          Int.mul (Int.mul S S)
            (Int.mul (Int.ofNat 2)
              (Int.mul (Int.add S a₂) (Int.mul a₁ a₁))) := by
      rw [int_mul_comm_dc (Int.mul a₁ a₁),
        int_mul_assoc_dc (Int.ofNat 2) (Int.mul S S) (Int.add S a₂),
        int_mul_comm_dc (Int.ofNat 2) (Int.mul (Int.mul S S) (Int.add S a₂)),
        int_mul_assoc_dc (Int.mul S S) (Int.add S a₂),
        int_mul_comm_dc (Int.add S a₂) (Int.ofNat 2),
        int_mul_assoc_dc (Int.mul S S) (Int.mul (Int.ofNat 2) (Int.add S a₂))
          (Int.mul a₁ a₁),
        int_mul_assoc_dc (Int.ofNat 2) (Int.add S a₂) (Int.mul a₁ a₁)]
    have h2b :
        Int.mul (Int.mul (Int.ofNat 2) (Int.mul S a₁))
            (Int.mul (Int.mul (Int.ofNat 2) S) (Int.mul a₁ a₂)) =
          Int.mul (Int.mul S S)
            (Int.mul (Int.ofNat 2)
              (Int.mul (Int.add a₂ a₂) (Int.mul a₁ a₁))) := by
      have hTwoA2 : Int.mul (Int.ofNat 2) a₂ = Int.add a₂ a₂ :=
        int_two_mul_dc a₂
      rw [← hTwoA2]
      -- Both sides equal `2 * 2 * S * S * a₁ * a₁ * a₂`
      have hLeft :
          Int.mul (Int.mul (Int.ofNat 2) (Int.mul S a₁))
              (Int.mul (Int.mul (Int.ofNat 2) S) (Int.mul a₁ a₂)) =
            Int.mul (Int.mul S S)
              (Int.mul (Int.ofNat 2)
                (Int.mul (Int.mul (Int.ofNat 2) a₂) (Int.mul a₁ a₁))) := by
        -- Rearrange factors via commutativity & associativity
        rw [← int_mul_assoc_dc (Int.ofNat 2) S a₁,
          int_mul_assoc_dc (Int.mul (Int.ofNat 2) S) a₁,
          int_mul_comm_dc a₁ (Int.mul (Int.mul (Int.ofNat 2) S) (Int.mul a₁ a₂)),
          int_mul_assoc_dc (Int.mul (Int.ofNat 2) S) (Int.mul a₁ a₂) a₁,
          ← int_mul_assoc_dc (Int.mul (Int.ofNat 2) S)
            (Int.mul (Int.ofNat 2) S),
          int_mul_assoc_dc (Int.ofNat 2) S (Int.mul (Int.ofNat 2) S),
          int_mul_comm_dc S (Int.mul (Int.ofNat 2) S),
          int_mul_assoc_dc (Int.ofNat 2) S S,
          ← int_mul_assoc_dc (Int.ofNat 2) (Int.ofNat 2) (Int.mul S S),
          int_mul_comm_dc (Int.mul (Int.ofNat 2) (Int.ofNat 2)) (Int.mul S S),
          int_mul_assoc_dc (Int.mul S S)
            (Int.mul (Int.ofNat 2) (Int.ofNat 2)),
          int_mul_assoc_dc (Int.ofNat 2) (Int.ofNat 2)]
        apply congrArg (Int.mul (Int.mul S S))
        apply congrArg (Int.mul (Int.ofNat 2))
        rw [int_mul_comm_dc (Int.mul a₁ a₂) a₁,
          int_mul_comm_dc a₁ a₂,
          ← int_mul_assoc_dc a₁ a₂ a₁,
          int_mul_comm_dc a₁ a₂,
          int_mul_assoc_dc a₂ a₁ a₁,
          ← int_mul_assoc_dc (Int.ofNat 2) a₂ (Int.mul a₁ a₁)]
      exact hLeft
    rw [h2a, h2b, ← int_mul_sub_dc (Int.mul S S), ← int_mul_sub_dc (Int.ofNat 2),
      ← int_sub_mul_dc (Int.add S a₂) (Int.add a₂ a₂) (Int.mul a₁ a₁)]
    have hDiff : Int.sub (Int.add S a₂) (Int.add a₂ a₂) = Int.sub S a₂ := by
      rw [int_sub_eq_add_neg_dc, int_neg_add_dc, ← int_add_assoc_dc,
        int_add_assoc_dc S a₂ (Int.neg a₂), int_add_neg_cancel_dc,
        int_add_zero_dc, ← int_sub_eq_add_neg_dc]
    rw [hDiff]
  have hT3 :
      Int.mul (Int.mul S S) (steinP22 S a₁ a₂) =
        Int.add (Int.mul (Int.mul S S) (juryDelta S a₁ a₂))
          (Int.mul (Int.mul S S)
            (Int.mul (Int.ofNat 2) (Int.mul (Int.add S a₂) (Int.mul a₂ a₂)))) := by
    dsimp only [steinP22]
    rw [int_mul_add_dc, int_mul_assoc_dc (Int.ofNat 2) (Int.add S a₂)]
  rw [hT1, hT2, hT3]
  -- Simplify `S² * (A - (B + (Δ + C))) = S² * ((A - C - B) - Δ) = S² * Δ`
  rw [← int_mul_add_dc (Int.mul S S), ← int_mul_add_dc (Int.mul S S),
    ← int_mul_sub_dc (Int.mul S S)]
  apply congrArg (Int.mul (Int.mul S S))
  have hRearr :
      Int.sub
          (Int.mul (Int.ofNat 2) (Int.mul (Int.add S a₂) (Int.mul S S)))
          (Int.add
            (Int.mul (Int.ofNat 2) (Int.mul (Int.sub S a₂) (Int.mul a₁ a₁)))
            (Int.add (juryDelta S a₁ a₂)
              (Int.mul (Int.ofNat 2)
                (Int.mul (Int.add S a₂) (Int.mul a₂ a₂))))) =
        Int.sub
          (Int.sub
            (Int.mul (Int.ofNat 2) (Int.mul (Int.add S a₂)
              (Int.sub (Int.mul S S) (Int.mul a₂ a₂))))
            (Int.mul (Int.ofNat 2) (Int.mul (Int.sub S a₂) (Int.mul a₁ a₁))))
          (juryDelta S a₁ a₂) := by
    rw [int_mul_sub_dc (Int.add S a₂), int_mul_sub_dc (Int.ofNat 2)]
    rw [int_sub_eq_add_neg_dc, int_sub_eq_add_neg_dc, int_sub_eq_add_neg_dc,
      int_sub_eq_add_neg_dc, int_sub_eq_add_neg_dc, int_neg_add_dc,
      int_neg_add_dc]
    rw [int_add_assoc_dc, int_add_assoc_dc]
    apply congrArg (Int.add (Int.mul (Int.ofNat 2)
      (Int.mul (Int.add S a₂) (Int.mul S S))))
    have hSwap3 : ∀ a b c : Int,
        Int.add a (Int.add b c) = Int.add c (Int.add a b) := fun a b c => by
      rw [int_add_comm_dc b c, ← int_add_assoc_dc a c b, int_add_comm_dc a c,
        int_add_assoc_dc c a b]
    exact hSwap3 _ _ _
  rw [hRearr, hCore, int_add_sub_cancel_dc]

/-- Exact determinant factorization (`[propext]` only):
`det P̃ = 2 S² (S + a₂) Δ + 4 S² a₂² J₂ J₃`. -/
theorem stein_det_factor (S a₁ a₂ : Int) :
    steinDet S a₁ a₂ =
      Int.add
        (Int.mul (Int.mul (Int.ofNat 2) (Int.mul S S))
          (Int.mul (Int.add S a₂) (juryDelta S a₁ a₂)))
        (Int.mul (Int.mul (Int.ofNat 4) (Int.mul (Int.mul S S) (Int.mul a₂ a₂)))
          (Int.mul (juryJ2 S a₁ a₂) (juryJ3 S a₁ a₂))) := by
  dsimp only [steinDet, steinP11, steinP22, steinP12, juryJ2, juryJ3]
  rw [int_mul_add_dc, int_diff_sq_dc]
  have hFirst :
      Int.mul (Int.mul (Int.mul (Int.ofNat 2) (Int.mul S S)) (Int.add S a₂))
          (juryDelta S a₁ a₂) =
        Int.mul (Int.mul (Int.ofNat 2) (Int.mul S S))
          (Int.mul (Int.add S a₂) (juryDelta S a₁ a₂)) :=
    int_mul_assoc_dc _ _ _
  have hFour : Int.ofNat 4 = Int.mul (Int.ofNat 2) (Int.ofNat 2) := rfl
  have hSecond :
      Int.sub
          (Int.mul
            (Int.mul (Int.mul (Int.ofNat 2) (Int.mul S S)) (Int.add S a₂))
            (Int.mul (Int.mul (Int.ofNat 2) (Int.add S a₂)) (Int.mul a₂ a₂)))
          (Int.mul
            (Int.mul (Int.mul (Int.ofNat 2) S) (Int.mul a₁ a₂))
            (Int.mul (Int.mul (Int.ofNat 2) S) (Int.mul a₁ a₂))) =
        Int.mul
          (Int.mul (Int.ofNat 4) (Int.mul (Int.mul S S) (Int.mul a₂ a₂)))
          (Int.sub (Int.mul (Int.add S a₂) (Int.add S a₂)) (Int.mul a₁ a₁)) := by
    rw [hFour, int_mul_sub_dc]
    have hL :
        Int.mul
            (Int.mul (Int.mul (Int.ofNat 2) (Int.mul S S)) (Int.add S a₂))
            (Int.mul (Int.mul (Int.ofNat 2) (Int.add S a₂)) (Int.mul a₂ a₂)) =
          Int.mul
            (Int.mul (Int.mul (Int.ofNat 2) (Int.ofNat 2))
              (Int.mul (Int.mul S S) (Int.mul a₂ a₂)))
            (Int.mul (Int.add S a₂) (Int.add S a₂)) := by
      rw [int_mul_assoc_dc (Int.mul (Int.ofNat 2) (Int.mul S S)) (Int.add S a₂),
        int_mul_comm_dc (Int.add S a₂),
        int_mul_assoc_dc (Int.mul (Int.ofNat 2) (Int.add S a₂)) (Int.mul a₂ a₂),
        int_mul_comm_dc (Int.mul a₂ a₂) (Int.add S a₂),
        int_mul_assoc_dc (Int.ofNat 2) (Int.add S a₂)
          (Int.mul (Int.add S a₂) (Int.mul a₂ a₂)),
        ← int_mul_assoc_dc (Int.add S a₂) (Int.add S a₂) (Int.mul a₂ a₂),
        int_mul_comm_dc (Int.mul (Int.add S a₂) (Int.add S a₂)) (Int.mul a₂ a₂),
        ← int_mul_assoc_dc (Int.ofNat 2) (Int.mul a₂ a₂),
        ← int_mul_assoc_dc (Int.mul (Int.ofNat 2) (Int.mul S S))
          (Int.mul (Int.ofNat 2) (Int.mul a₂ a₂))]
      apply congrArg (fun z => Int.mul z (Int.mul (Int.add S a₂) (Int.add S a₂)))
      rw [int_mul_assoc_dc (Int.ofNat 2) (Int.mul S S),
        int_mul_comm_dc (Int.mul S S) (Int.mul (Int.ofNat 2) (Int.mul a₂ a₂)),
        int_mul_assoc_dc (Int.ofNat 2) (Int.mul a₂ a₂) (Int.mul S S),
        ← int_mul_assoc_dc (Int.ofNat 2) (Int.ofNat 2),
        int_mul_comm_dc (Int.mul a₂ a₂) (Int.mul S S)]
    have hR :
        Int.mul
            (Int.mul (Int.mul (Int.ofNat 2) S) (Int.mul a₁ a₂))
            (Int.mul (Int.mul (Int.ofNat 2) S) (Int.mul a₁ a₂)) =
          Int.mul
            (Int.mul (Int.mul (Int.ofNat 2) (Int.ofNat 2))
              (Int.mul (Int.mul S S) (Int.mul a₂ a₂)))
            (Int.mul a₁ a₁) := by
      have hPair : ∀ p q : Int,
          Int.mul (Int.mul p q) (Int.mul p q) =
            Int.mul (Int.mul p p) (Int.mul q q) := fun p q => by
        rw [int_mul_assoc_dc p q (Int.mul p q), int_mul_comm_dc q (Int.mul p q),
          int_mul_assoc_dc p q q, ← int_mul_assoc_dc p p (Int.mul q q)]
      rw [hPair, hPair, hPair, int_mul_comm_dc (Int.mul a₁ a₁) (Int.mul a₂ a₂),
        int_mul_assoc_dc (Int.mul (Int.ofNat 2) (Int.ofNat 2)) (Int.mul S S),
        ← int_mul_assoc_dc (Int.mul S S) (Int.mul a₂ a₂),
        ← int_mul_assoc_dc (Int.mul (Int.ofNat 2) (Int.ofNat 2))
          (Int.mul (Int.mul S S) (Int.mul a₂ a₂))]
    rw [hL, hR]
  rw [hFirst, int_sub_eq_add_neg_dc, int_add_assoc_dc, ← int_sub_eq_add_neg_dc,
    hSecond]

/-- Positive definiteness of `P̃` under strict Jury stability (`[propext]`
only): `JuryStable S a₁ a₂` guarantees `Δ > 0`, `P̃₁₁ > 0`, `P̃₂₂ > 0`, and
`det P̃ > 0`. -/
theorem stein_pos_def_of_jury {S a₁ a₂ : Int} (hJ : JuryStable S a₁ a₂) :
    IntPos (juryDelta S a₁ a₂) ∧
    IntPos (steinP11 S a₂) ∧
    IntPos (steinP22 S a₁ a₂) ∧
    IntPos (steinDet S a₁ a₂) := by
  have hS := hJ.1
  have hJ1 := hJ.2.1
  have hJ2 := hJ.2.2.1
  have hJ3 := hJ.2.2.2
  have h2Pos : IntPos (Int.ofNat 2) :=
    (intBalance_le (intBalance_ofNat 1) (intBalance_ofNat 2)).mpr
      (Nat.le_of_ble_eq_true rfl)
  have h4Pos : IntPos (Int.ofNat 4) :=
    (intBalance_le (intBalance_ofNat 1) (intBalance_ofNat 4)).mpr
      (Nat.le_of_ble_eq_true rfl)
  have h2Sum : Int.mul (Int.ofNat 2) (Int.add S a₂) =
      Int.add (juryJ2 S a₁ a₂) (juryJ3 S a₁ a₂) := by
    dsimp only [juryJ2, juryJ3]
    rw [int_sub_eq_add_neg_dc, int_add_assoc_dc,
      ← int_add_assoc_dc (Int.neg a₁) (Int.add S a₂) a₁,
      int_add_comm_dc (Int.neg a₁) (Int.add S a₂),
      int_add_assoc_dc (Int.add S a₂) (Int.neg a₁) a₁,
      int_add_comm_dc (Int.neg a₁) a₁, int_add_neg_cancel_dc,
      int_add_zero_dc, int_two_mul_dc]
  have h2Sa2Pos : IntPos (Int.mul (Int.ofNat 2) (Int.add S a₂)) := by
    rw [h2Sum]
    exact int_add_pos_nonneg hJ2 (int_nonneg_of_pos hJ3)
  have hSa2Pos : IntPos (Int.add S a₂) :=
    int_pos_of_mul_pos_left h2Pos h2Sa2Pos
  have hS2Pos : IntPos (Int.mul S S) := int_mul_pos_of_pos hS hS
  have hJ23Pos : IntPos (Int.mul (juryJ2 S a₁ a₂) (juryJ3 S a₁ a₂)) :=
    int_mul_pos_of_pos hJ2 hJ3
  have hDeltaPos : IntPos (juryDelta S a₁ a₂) :=
    int_mul_pos_of_pos (int_mul_pos_of_pos hJ1 hJ2) hJ3
  have hP11Pos : IntPos (steinP11 S a₂) :=
    int_mul_pos_of_pos (int_mul_pos_of_pos h2Pos hS2Pos) hSa2Pos
  have hP22Pos : IntPos (steinP22 S a₁ a₂) :=
    int_add_pos_nonneg hDeltaPos
      (int_mul_nonneg (int_nonneg_of_pos h2Sa2Pos) (int_sq_nonneg a₂))
  have hDetPos : IntPos (steinDet S a₁ a₂) := by
    rw [stein_det_factor]
    exact int_add_pos_nonneg
      (int_mul_pos_of_pos (int_mul_pos_of_pos h2Pos hS2Pos)
        (int_mul_pos_of_pos hSa2Pos hDeltaPos))
      (int_mul_nonneg
        (int_mul_nonneg (int_nonneg_of_pos h4Pos)
          (int_mul_nonneg (int_nonneg_of_pos hS2Pos) (int_sq_nonneg a₂)))
        (int_nonneg_of_pos hJ23Pos))
  exact ⟨hDeltaPos, hP11Pos, hP22Pos, hDetPos⟩

/-! ## Part III: Quadratic Contraction & Division-Free Ellipsoid Bounds -/

/-- Symmetric 2x2 quadratic Lyapunov energy `p₁₁ x₁² + 2 p₁₂ x₁ x₂ + p₂₂ x₂²`.
-/
@[expose] def quadForm (p11 p12 p22 x1 x2 : Int) : Int :=
  Int.add
    (Int.add (Int.mul p11 (Int.mul x1 x1))
      (Int.mul (Int.mul (Int.ofNat 2) p12) (Int.mul x1 x2)))
    (Int.mul p22 (Int.mul x2 x2))

/-- First square-completion identity (`[propext]` only):
`p₁₁ Q(x) = (p₁₁ x₁ + p₁₂ x₂)² + (p₁₁ p₂₂ - p₁₂²) x₂²`. -/
theorem quadForm_complete_sq_1 (p11 p12 p22 x1 x2 : Int) :
    Int.mul p11 (quadForm p11 p12 p22 x1 x2) =
      Int.add
        (Int.mul (Int.add (Int.mul p11 x1) (Int.mul p12 x2))
          (Int.add (Int.mul p11 x1) (Int.mul p12 x2)))
        (Int.mul (Int.sub (Int.mul p11 p22) (Int.mul p12 p12))
          (Int.mul x2 x2)) := by
  dsimp only [quadForm]
  rw [int_mul_add_dc, int_mul_add_dc, int_add_mul_dc, int_mul_add_dc,
    int_mul_add_dc, int_sub_mul_dc]
  have hSq1 :
      Int.mul p11 (Int.mul p11 (Int.mul x1 x1)) =
        Int.mul (Int.mul p11 x1) (Int.mul p11 x1) := by
    rw [← int_mul_assoc_dc p11 p11, int_mul_assoc_dc p11 x1,
      int_mul_comm_dc x1 (Int.mul p11 x1), int_mul_assoc_dc p11 x1 x1,
      ← int_mul_assoc_dc p11 p11]
  have hSq2 :
      Int.mul (Int.mul p12 x2) (Int.mul p12 x2) =
        Int.mul (Int.mul p12 p12) (Int.mul x2 x2) := by
    rw [int_mul_assoc_dc p12 x2, int_mul_comm_dc x2 (Int.mul p12 x2),
      int_mul_assoc_dc p12 x2 x2, ← int_mul_assoc_dc p12 p12]
  have hCross :
      Int.mul p11 (Int.mul (Int.mul (Int.ofNat 2) p12) (Int.mul x1 x2)) =
        Int.add (Int.mul (Int.mul p11 x1) (Int.mul p12 x2))
          (Int.mul (Int.mul p12 x2) (Int.mul p11 x1)) := by
    rw [int_mul_comm_dc (Int.mul p12 x2) (Int.mul p11 x1), ← int_two_mul_dc]
    rw [int_mul_assoc_dc (Int.ofNat 2) p12, int_mul_comm_dc p11,
      int_mul_assoc_dc (Int.ofNat 2)]
    apply congrArg (Int.mul (Int.ofNat 2))
    rw [int_mul_assoc_dc p11 x1, int_mul_comm_dc x1 (Int.mul p12 x2),
      int_mul_assoc_dc p12 x2 x1, int_mul_comm_dc x2 x1,
      ← int_mul_assoc_dc p11 p12, int_mul_comm_dc p11 p12,
      int_mul_assoc_dc p12 p11, int_mul_comm_dc p11 (Int.mul x1 x2),
      int_mul_assoc_dc p12 (Int.mul x1 x2) p11]
  have hLast :
      Int.mul p11 (Int.mul p22 (Int.mul x2 x2)) =
        Int.mul (Int.mul p11 p22) (Int.mul x2 x2) :=
    (int_mul_assoc_dc p11 p22 (Int.mul x2 x2)).symm
  rw [hSq1, hCross, hLast, hSq2]
  have hGroup : ∀ ab b c d e : Int,
      Int.add (Int.add ab (Int.add b c)) d =
        Int.add (Int.add (Int.add ab b) (Int.add c e)) (Int.sub d e) :=
    fun ab b c d e => by
      rw [int_add_assoc_dc (Int.add ab b) (Int.add c e) (Int.sub d e),
        int_add_assoc_dc c e (Int.sub d e),
        int_add_comm_dc e (Int.sub d e),
        int_sub_add_cancel_dc,
        ← int_add_assoc_dc ab b c,
        int_add_assoc_dc (Int.add ab b) c d]
  exact hGroup _ _ _ _ _

/-- Second square-completion identity (`[propext]` only):
`p₂₂ Q(x) = (p₁₂ x₁ + p₂₂ x₂)² + (p₁₁ p₂₂ - p₁₂²) x₁²`. -/
theorem quadForm_complete_sq_2 (p11 p12 p22 x1 x2 : Int) :
    Int.mul p22 (quadForm p11 p12 p22 x1 x2) =
      Int.add
        (Int.mul (Int.add (Int.mul p12 x1) (Int.mul p22 x2))
          (Int.add (Int.mul p12 x1) (Int.mul p22 x2)))
        (Int.mul (Int.sub (Int.mul p11 p22) (Int.mul p12 p12))
          (Int.mul x1 x1)) := by
  have hSym : quadForm p11 p12 p22 x1 x2 = quadForm p22 p12 p11 x2 x1 := by
    dsimp only [quadForm]
    rw [int_add_comm_dc (Int.add (Int.mul p11 (Int.mul x1 x1)) _),
      int_add_comm_dc (Int.mul p11 (Int.mul x1 x1)),
      ← int_add_assoc_dc, int_mul_comm_dc x1 x2]
  rw [hSym, quadForm_complete_sq_1 p22 p12 p11 x2 x1,
    int_add_comm_dc (Int.mul p22 x2) (Int.mul p12 x1),
    int_mul_comm_dc p22 p11]

/-- Division-free coordinatewise ellipsoid register bounds (`[propext]` only):
for any symmetric matrix `(p11, p12, p22)`, `x₁² det ≤ p₂₂ Q(x)` and
`x₂² det ≤ p₁₁ Q(x)` hold with zero divisions or square roots. -/
theorem ellipsoid_coord_bounds (p11 p12 p22 x1 x2 : Int) :
    Int.mul (Int.sub (Int.mul p11 p22) (Int.mul p12 p12)) (Int.mul x1 x1) ≤
      Int.mul p22 (quadForm p11 p12 p22 x1 x2) ∧
    Int.mul (Int.sub (Int.mul p11 p22) (Int.mul p12 p12)) (Int.mul x2 x2) ≤
      Int.mul p11 (quadForm p11 p12 p22 x1 x2) := by
  refine ⟨?_, ?_⟩
  · rw [int_le_iff_sub_nonneg, quadForm_complete_sq_2, int_add_sub_cancel_dc]
    exact int_sq_nonneg _
  · rw [int_le_iff_sub_nonneg, quadForm_complete_sq_1, int_add_sub_cancel_dc]
    exact int_sq_nonneg _

/-- Exact quadratic Lyapunov contraction identity for scaled companion step
`(x₁', x₂') = (-a₁ x₁ - a₂ x₂, S x₁)` (`[propext]` only):
`Q(P̃, x') = S² Q(P̃, x) - S² Δ (x₁² + x₂²)`. -/
theorem stein_quad_contraction (S a₁ a₂ x₁ x₂ : Int) :
    let x1' := Int.sub (Int.neg (Int.mul a₁ x₁)) (Int.mul a₂ x₂)
    let x2' := Int.mul S x₁
    quadForm (steinP11 S a₂) (steinP12 S a₁ a₂) (steinP22 S a₁ a₂) x1' x2' =
      Int.sub
        (Int.mul (Int.mul S S)
          (quadForm (steinP11 S a₂) (steinP12 S a₁ a₂) (steinP22 S a₁ a₂)
            x₁ x₂))
        (Int.mul (Int.mul (Int.mul S S) (juryDelta S a₁ a₂))
          (Int.add (Int.mul x₁ x₁) (Int.mul x₂ x₂))) := by
  intro x1' x2'
  -- Algebraic congruence: for any `(p11, p12, p22)`,
  -- `Q(p, (-a₁ x₁ - a₂ x₂, S x₁))` expands as `c11 x₁² + 2 c12 x₁ x₂ + c22 x₂²`
  -- where:
  -- `c11 = a₁² p11 - 2 S a₁ p12 + S² p22`,
  -- `c12 = a₁ a₂ p11 - S a₂ p12`,
  -- `c22 = a₂² p11`.
  have hExpand :
      ∀ p11 p12 p22 : Int,
        quadForm p11 p12 p22 x1' x2' =
          Int.add
            (Int.add
              (Int.mul
                (Int.add
                  (Int.sub (Int.mul (Int.mul a₁ a₁) p11)
                    (Int.mul (Int.mul (Int.ofNat 2) (Int.mul S a₁)) p12))
                  (Int.mul (Int.mul S S) p22))
                (Int.mul x₁ x₁))
              (Int.mul
                (Int.mul (Int.ofNat 2)
                  (Int.sub (Int.mul (Int.mul a₁ a₂) p11)
                    (Int.mul (Int.mul S a₂) p12)))
                (Int.mul x₁ x₂)))
            (Int.mul (Int.mul (Int.mul a₂ a₂) p11) (Int.mul x₂ x₂)) := by
    intro p11 p12 p22
    dsimp only [quadForm, x1', x2']
    have hNegPair :
        Int.sub (Int.neg (Int.mul a₁ x₁)) (Int.mul a₂ x₂) =
          Int.neg (Int.add (Int.mul a₁ x₁) (Int.mul a₂ x₂)) := by
      rw [int_sub_eq_add_neg_dc, int_neg_add_dc]
    rw [hNegPair,
      int_neg_mul_dc (Int.add (Int.mul a₁ x₁) (Int.mul a₂ x₂))
        (Int.neg (Int.add (Int.mul a₁ x₁) (Int.mul a₂ x₂))),
      int_mul_neg_dc (Int.add (Int.mul a₁ x₁) (Int.mul a₂ x₂))
        (Int.add (Int.mul a₁ x₁) (Int.mul a₂ x₂)),
      int_neg_neg_dc,
      int_neg_mul_dc (Int.add (Int.mul a₁ x₁) (Int.mul a₂ x₂)) (Int.mul S x₁)]
    -- Expand `(a₁ x₁ + a₂ x₂)² = a₁² x₁² + 2 a₁ a₂ x₁ x₂ + a₂² x₂²`
    have hSqX1 :
        Int.mul (Int.add (Int.mul a₁ x₁) (Int.mul a₂ x₂))
            (Int.add (Int.mul a₁ x₁) (Int.mul a₂ x₂)) =
          Int.add
            (Int.add (Int.mul (Int.mul a₁ a₁) (Int.mul x₁ x₁))
              (Int.mul (Int.ofNat 2)
                (Int.mul (Int.mul a₁ a₂) (Int.mul x₁ x₂))))
            (Int.mul (Int.mul a₂ a₂) (Int.mul x₂ x₂)) := by
      have hP : ∀ u v : Int,
          Int.mul (Int.mul u v) (Int.mul u v) =
            Int.mul (Int.mul u u) (Int.mul v v) := fun u v => by
        rw [int_mul_assoc_dc u v, int_mul_comm_dc v (Int.mul u v),
          int_mul_assoc_dc u v v, ← int_mul_assoc_dc u u]
      have hC :
          Int.add (Int.mul (Int.mul a₁ x₁) (Int.mul a₂ x₂))
              (Int.mul (Int.mul a₂ x₂) (Int.mul a₁ x₁)) =
            Int.mul (Int.ofNat 2)
              (Int.mul (Int.mul a₁ a₂) (Int.mul x₁ x₂)) := by
        rw [int_mul_comm_dc (Int.mul a₂ x₂) (Int.mul a₁ x₁),
          ← int_two_mul_dc]
        apply congrArg (Int.mul (Int.ofNat 2))
        rw [int_mul_assoc_dc a₁ x₁, int_mul_comm_dc x₁ (Int.mul a₂ x₂),
          int_mul_assoc_dc a₂ x₂ x₁, int_mul_comm_dc x₂ x₁,
          ← int_mul_assoc_dc a₁ a₂]
      rw [int_add_mul_dc, int_mul_add_dc, int_mul_add_dc, hP, hP,
        int_add_assoc_dc (Int.mul (Int.mul a₁ a₁) (Int.mul x₁ x₁)),
        ← int_add_assoc_dc (Int.mul (Int.mul a₁ x₁) (Int.mul a₂ x₂)),
        hC, ← int_add_assoc_dc]
    -- Expand `2 p12 (-(a₁ x₁ + a₂ x₂) * (S x₁))`
    have hCrossX :
        Int.mul (Int.mul (Int.ofNat 2) p12)
            (Int.neg (Int.mul (Int.add (Int.mul a₁ x₁) (Int.mul a₂ x₂))
              (Int.mul S x₁))) =
          Int.add
            (Int.neg (Int.mul (Int.mul (Int.mul (Int.ofNat 2) (Int.mul S a₁)) p12)
              (Int.mul x₁ x₁)))
            (Int.neg (Int.mul (Int.mul (Int.ofNat 2) (Int.mul (Int.mul S a₂) p12))
              (Int.mul x₁ x₂))) := by
      rw [int_mul_neg_dc, int_add_mul_dc, int_mul_add_dc, int_neg_add_dc]
      have hLeftTerm :
          Int.mul (Int.mul (Int.ofNat 2) p12)
              (Int.mul (Int.mul a₁ x₁) (Int.mul S x₁)) =
            Int.mul (Int.mul (Int.mul (Int.ofNat 2) (Int.mul S a₁)) p12)
              (Int.mul x₁ x₁) := by
        rw [int_mul_assoc_dc (Int.ofNat 2) p12,
          int_mul_assoc_dc (Int.ofNat 2) (Int.mul S a₁),
          int_mul_assoc_dc (Int.ofNat 2)]
        apply congrArg (Int.mul (Int.ofNat 2))
        rw [int_mul_assoc_dc a₁ x₁, int_mul_comm_dc x₁ (Int.mul S x₁),
          int_mul_assoc_dc S x₁ x₁, ← int_mul_assoc_dc a₁ S,
          int_mul_comm_dc a₁ S, int_mul_comm_dc p12,
          int_mul_assoc_dc (Int.mul S a₁) (Int.mul x₁ x₁) p12,
          int_mul_comm_dc (Int.mul x₁ x₁) p12,
          ← int_mul_assoc_dc (Int.mul S a₁) p12]
      have hRightTerm :
          Int.mul (Int.mul (Int.ofNat 2) p12)
              (Int.mul (Int.mul a₂ x₂) (Int.mul S x₁)) =
            Int.mul (Int.mul (Int.ofNat 2) (Int.mul (Int.mul S a₂) p12))
              (Int.mul x₁ x₂) := by
        rw [int_mul_assoc_dc (Int.ofNat 2) p12,
          int_mul_assoc_dc (Int.ofNat 2)]
        apply congrArg (Int.mul (Int.ofNat 2))
        rw [int_mul_assoc_dc a₂ x₂, int_mul_comm_dc x₂ (Int.mul S x₁),
          int_mul_assoc_dc S x₁ x₂, ← int_mul_assoc_dc a₂ S,
          int_mul_comm_dc a₂ S, int_mul_comm_dc p12,
          int_mul_assoc_dc (Int.mul S a₂) (Int.mul x₁ x₂) p12,
          int_mul_comm_dc (Int.mul x₁ x₂) p12,
          ← int_mul_assoc_dc (Int.mul S a₂) p12]
      rw [hLeftTerm, hRightTerm]
    have hP22 :
        Int.mul p22 (Int.mul (Int.mul S x₁) (Int.mul S x₁)) =
          Int.mul (Int.mul (Int.mul S S) p22) (Int.mul x₁ x₁) := by
      rw [int_mul_assoc_dc S x₁, int_mul_comm_dc x₁ (Int.mul S x₁),
        int_mul_assoc_dc S x₁ x₁, ← int_mul_assoc_dc S S,
        ← int_mul_assoc_dc p22 (Int.mul S S), int_mul_comm_dc p22 (Int.mul S S)]
    rw [hSqX1, hCrossX, hP22, int_mul_add_dc, int_mul_add_dc]
    -- Match each of the 6 terms on LHS with the 6 terms on RHS
    rw [int_add_mul_dc, int_sub_mul_dc, int_mul_sub_dc, int_sub_mul_dc,
      int_sub_eq_add_neg_dc, int_sub_eq_add_neg_dc]
    have hA1 : Int.mul p11 (Int.mul (Int.mul a₁ a₁) (Int.mul x₁ x₁)) =
        Int.mul (Int.mul (Int.mul a₁ a₁) p11) (Int.mul x₁ x₁) := by
      rw [← int_mul_assoc_dc p11, int_mul_comm_dc p11 (Int.mul a₁ a₁)]
    have hA2 :
        Int.mul p11 (Int.mul (Int.ofNat 2)
            (Int.mul (Int.mul a₁ a₂) (Int.mul x₁ x₂))) =
          Int.mul (Int.mul (Int.ofNat 2) (Int.mul (Int.mul a₁ a₂) p11))
            (Int.mul x₁ x₂) := by
      rw [← int_mul_assoc_dc p11 (Int.ofNat 2),
        int_mul_comm_dc p11 (Int.ofNat 2),
        int_mul_assoc_dc (Int.ofNat 2) p11,
        ← int_mul_assoc_dc p11 (Int.mul a₁ a₂),
        int_mul_comm_dc p11 (Int.mul a₁ a₂),
        ← int_mul_assoc_dc (Int.ofNat 2)]
    have hA3 : Int.mul p11 (Int.mul (Int.mul a₂ a₂) (Int.mul x₂ x₂)) =
        Int.mul (Int.mul (Int.mul a₂ a₂) p11) (Int.mul x₂ x₂) := by
      rw [← int_mul_assoc_dc p11, int_mul_comm_dc p11 (Int.mul a₂ a₂)]
    rw [hA1, hA2, hA3]
    -- Pure Abelian-group rearrangement of 6 summands
    -- `(t1 + t2 + t3) + (t4 + t5) + t6` vs `((t1 + t4) + t6) + (t2 + t5) + t3`
    let t1 := Int.mul (Int.mul (Int.mul a₁ a₁) p11) (Int.mul x₁ x₁)
    let t2 := Int.mul (Int.mul (Int.ofNat 2) (Int.mul (Int.mul a₁ a₂) p11))
      (Int.mul x₁ x₂)
    let t3 := Int.mul (Int.mul (Int.mul a₂ a₂) p11) (Int.mul x₂ x₂)
    let t4 := Int.neg (Int.mul (Int.mul (Int.mul (Int.ofNat 2) (Int.mul S a₁)) p12)
      (Int.mul x₁ x₁))
    let t5 := Int.neg (Int.mul (Int.mul (Int.ofNat 2) (Int.mul (Int.mul S a₂) p12))
      (Int.mul x₁ x₂))
    let t6 := Int.mul (Int.mul (Int.mul S S) p22) (Int.mul x₁ x₁)
    have hSix : ∀ u1 u2 u3 u4 u5 u6 : Int,
        Int.add (Int.add (Int.add (Int.add u1 u2) u3) (Int.add u4 u5)) u6 =
          Int.add (Int.add (Int.add (Int.add u1 u4) u6) (Int.add u2 u5)) u3 :=
      fun u1 u2 u3 u4 u5 u6 => by
        rw [int_add_assoc_dc u1 u2 u3,
          int_add_assoc_dc u1 (Int.add u2 u3) (Int.add u4 u5),
          int_add_comm_dc (Int.add u2 u3) (Int.add u4 u5),
          ← int_add_assoc_dc u1 (Int.add u4 u5),
          ← int_add_assoc_dc u1 u4 u5,
          int_add_assoc_dc (Int.add u1 u4) u5 (Int.add u2 u3),
          int_add_comm_dc u5 (Int.add u2 u3),
          int_add_assoc_dc u2 u3 u5,
          int_add_comm_dc u3 u5,
          ← int_add_assoc_dc u2 u5 u3,
          ← int_add_assoc_dc (Int.add u1 u4) (Int.add u2 u5) u3,
          int_add_assoc_dc (Int.add (Int.add u1 u4) (Int.add u2 u5)) u3 u6,
          int_add_comm_dc u3 u6,
          ← int_add_assoc_dc (Int.add (Int.add u1 u4) (Int.add u2 u5)) u6 u3,
          int_add_assoc_dc (Int.add u1 u4) (Int.add u2 u5) u6,
          int_add_comm_dc (Int.add u2 u5) u6,
          ← int_add_assoc_dc (Int.add u1 u4) u6 (Int.add u2 u5)]
    exact hSix _ _ _ _ _ _
  rw [hExpand]
  -- Substitute the 3 Stein-Lyapunov matrix entry identities!
  have hSubId : ∀ a b c : Int, Int.sub a b = c → b = Int.sub a c := by
    intro a b c h
    rw [← h, int_sub_eq_add_neg_dc a (Int.sub a b), int_sub_eq_add_neg_dc a b,
      int_neg_add_dc, int_neg_neg_dc, int_add_comm_dc (Int.neg a) b,
      ← int_add_assoc_dc a b (Int.neg a), int_add_comm_dc a b,
      int_add_assoc_dc b a (Int.neg a), int_add_neg_cancel_dc, int_add_zero_dc]
  have h11 := hSubId _ _ _ (stein_lyapunov_entry11 S a₁ a₂)
  have h12 : Int.sub (Int.mul (Int.mul a₁ a₂) (steinP11 S a₂))
      (Int.mul (Int.mul S a₂) (steinP12 S a₁ a₂)) =
      Int.mul (Int.mul S S) (steinP12 S a₁ a₂) := by
    have h := hSubId _ _ _ (stein_lyapunov_entry12 S a₁ a₂)
    rw [int_sub_eq_add_neg_dc (Int.mul (Int.mul S S) (steinP12 S a₁ a₂))
        (Int.ofNat 0)] at h
    have hNeg0 : Int.neg (Int.ofNat 0) = Int.ofNat 0 := rfl
    rw [hNeg0, int_add_zero_dc] at h
    exact h
  have h22 := hSubId _ _ _ (stein_lyapunov_entry22 S a₁ a₂)
  rw [h11, h12, h22]
  dsimp only [quadForm]
  rw [int_sub_mul_dc, int_sub_mul_dc, int_mul_add_dc, int_mul_add_dc,
    int_mul_add_dc]
  rw [int_mul_assoc_dc (Int.mul S S) (steinP11 S a₂),
    int_mul_assoc_dc (Int.mul S S) (steinP22 S a₁ a₂),
    ← int_mul_assoc_dc (Int.ofNat 2) (Int.mul S S),
    int_mul_comm_dc (Int.ofNat 2) (Int.mul S S),
    int_mul_assoc_dc (Int.mul S S) (Int.ofNat 2),
    int_mul_assoc_dc (Int.mul S S) (Int.mul (Int.ofNat 2) (steinP12 S a₁ a₂))]
  let u1 := Int.mul (Int.mul S S) (Int.mul (steinP11 S a₂) (Int.mul x₁ x₁))
  let u2 := Int.mul (Int.mul S S)
    (Int.mul (Int.mul (Int.ofNat 2) (steinP12 S a₁ a₂)) (Int.mul x₁ x₂))
  let u3 := Int.mul (Int.mul S S) (Int.mul (steinP22 S a₁ a₂) (Int.mul x₂ x₂))
  let d1 := Int.mul (Int.mul (Int.mul S S) (juryDelta S a₁ a₂)) (Int.mul x₁ x₁)
  let d2 := Int.mul (Int.mul (Int.mul S S) (juryDelta S a₁ a₂)) (Int.mul x₂ x₂)
  change Int.add (Int.add (Int.sub u1 d1) u2) (Int.sub u3 d2) =
    Int.sub (Int.add (Int.add u1 u2) u3) (Int.add d1 d2)
  rw [int_sub_eq_add_neg_dc, int_sub_eq_add_neg_dc, int_sub_eq_add_neg_dc,
    int_neg_add_dc]
  rw [int_add_assoc_dc u1 (Int.neg d1) u2, int_add_comm_dc (Int.neg d1) u2,
    ← int_add_assoc_dc u1 u2 (Int.neg d1),
    int_add_assoc_dc (Int.add u1 u2) (Int.neg d1) (Int.add u3 (Int.neg d2)),
    ← int_add_assoc_dc (Int.neg d1) u3 (Int.neg d2),
    int_add_comm_dc (Int.neg d1) u3,
    int_add_assoc_dc u3 (Int.neg d1) (Int.neg d2),
    ← int_add_assoc_dc (Int.add u1 u2) u3]

/-- Strict positive-definiteness of the Stein-Lyapunov energy `Q(P̃, x)` under
`JuryStable S a₁ a₂` (`[propext]` only): `Q ≥ 0` everywhere, and `Q > 0` for
every non-zero state `(x₁, x₂) ≠ (0, 0)`. -/
theorem stein_quad_pos_of_jury {S a₁ a₂ : Int} (hJ : JuryStable S a₁ a₂)
    (x₁ x₂ : Int) :
    IntNonNeg (quadForm (steinP11 S a₂) (steinP12 S a₁ a₂) (steinP22 S a₁ a₂)
      x₁ x₂) ∧
    ((x₁ ≠ Int.ofNat 0 ∨ x₂ ≠ Int.ofNat 0) →
      IntPos (quadForm (steinP11 S a₂) (steinP12 S a₁ a₂) (steinP22 S a₁ a₂)
        x₁ x₂)) := by
  have hPD := stein_pos_def_of_jury hJ
  have hP11Pos := hPD.2.1
  have hP22Pos := hPD.2.2.1
  have hDetPos := hPD.2.2.2
  have hNonNeg :
      IntNonNeg (quadForm (steinP11 S a₂) (steinP12 S a₁ a₂)
        (steinP22 S a₁ a₂) x₁ x₂) := by
    apply int_nonneg_of_mul_nonneg_left hP11Pos
    rw [quadForm_complete_sq_1]
    exact int_add_nonneg (int_sq_nonneg _)
      (int_mul_nonneg (int_nonneg_of_pos hDetPos) (int_sq_nonneg x₂))
  refine ⟨hNonNeg, fun hNe => ?_⟩
  cases hNe with
  | inl hx1 =>
    apply int_pos_of_mul_pos_left hP22Pos
    rw [quadForm_complete_sq_2]
    rw [int_add_comm_dc]
    exact int_add_pos_nonneg
      (int_mul_pos_of_pos hDetPos (int_sq_pos_of_ne_zero hx1))
      (int_sq_nonneg _)
  | inr hx2 =>
    apply int_pos_of_mul_pos_left hP11Pos
    rw [quadForm_complete_sq_1]
    rw [int_add_comm_dc]
    exact int_add_pos_nonneg
      (int_mul_pos_of_pos hDetPos (int_sq_pos_of_ne_zero hx2))
      (int_sq_nonneg _)

/-! ## Part IV: Euclidean Failure & Coupled Normal Form Saturation -/

/-- Unweighted Euclidean norm fails to contract on companion matrices whenever
`S ≠ 0` and `a₁ ≠ 0` (`[propext]` only): on state `(S, 0)`,
`‖S · A_c · (S, 0)‖₂² - S² ‖(S, 0)‖₂² = a₁² S² > 0`. -/
theorem euclidean_fails_companion {S a₁ a₂ : Int}
    (hS : S ≠ Int.ofNat 0) (ha₁ : a₁ ≠ Int.ofNat 0) :
    let x1' := Int.sub (Int.neg (Int.mul a₁ S)) (Int.mul a₂ (Int.ofNat 0))
    let x2' := Int.mul S S
    IntPos (Int.sub
      (Int.add (Int.mul x1' x1') (Int.mul x2' x2'))
      (Int.mul (Int.mul S S)
        (Int.add (Int.mul S S) (Int.mul (Int.ofNat 0) (Int.ofNat 0))))) := by
  intro x1' x2'
  have hEq :
      Int.sub
          (Int.add (Int.mul x1' x1') (Int.mul x2' x2'))
          (Int.mul (Int.mul S S)
            (Int.add (Int.mul S S) (Int.mul (Int.ofNat 0) (Int.ofNat 0)))) =
        Int.mul (Int.mul a₁ a₁) (Int.mul S S) := by
    dsimp only [x1', x2']
    rw [int_mul_zero_dc, int_mul_zero_dc, int_add_zero_dc,
      int_sub_eq_add_neg_dc (Int.neg (Int.mul a₁ S)) (Int.ofNat 0)]
    have hNeg0 : Int.neg (Int.ofNat 0) = Int.ofNat 0 := rfl
    rw [hNeg0, int_add_zero_dc, int_neg_mul_dc, int_mul_neg_dc, int_neg_neg_dc,
      int_add_sub_cancel_dc]
    rw [int_mul_assoc_dc a₁ S, int_mul_comm_dc S (Int.mul a₁ S),
      int_mul_assoc_dc a₁ S S, ← int_mul_assoc_dc a₁ a₁]
  rw [hEq]
  exact int_mul_pos_of_pos (int_sq_pos_of_ne_zero ha₁) (int_sq_pos_of_ne_zero hS)

/-- Exact Euclidean `L₂²` identity for coupled normal form
`A_coupled = [[α, -β], [β, α]]` (`[propext]` only):
`(α x₁ - β x₂)² + (β x₁ + α x₂)² = (α² + β²)(x₁² + x₂²)`. -/
theorem coupled_normal_l2_identity (α β x₁ x₂ : Int) :
    Int.add
      (Int.mul (Int.sub (Int.mul α x₁) (Int.mul β x₂))
        (Int.sub (Int.mul α x₁) (Int.mul β x₂)))
      (Int.mul (Int.add (Int.mul β x₁) (Int.mul α x₂))
        (Int.add (Int.mul β x₁) (Int.mul α x₂))) =
      Int.mul (Int.add (Int.mul α α) (Int.mul β β))
        (Int.add (Int.mul x₁ x₁) (Int.mul x₂ x₂)) := by
  have hP : ∀ u v : Int,
      Int.mul (Int.mul u v) (Int.mul u v) =
        Int.mul (Int.mul u u) (Int.mul v v) := fun u v => by
    rw [int_mul_assoc_dc u v, int_mul_comm_dc v (Int.mul u v),
      int_mul_assoc_dc u v v, ← int_mul_assoc_dc u u]
  have hCrossEq :
      Int.mul (Int.mul α x₁) (Int.mul β x₂) =
        Int.mul (Int.mul β x₁) (Int.mul α x₂) := by
    rw [int_mul_assoc_dc α x₁, int_mul_comm_dc x₁ (Int.mul β x₂),
      int_mul_assoc_dc β x₂ x₁, ← int_mul_assoc_dc α β,
      int_mul_comm_dc α β, int_mul_assoc_dc β α,
      int_mul_comm_dc x₂ x₁, ← int_mul_assoc_dc α x₁ x₂,
      int_mul_comm_dc α x₁, int_mul_assoc_dc x₁ α x₂,
      ← int_mul_assoc_dc β x₁]
  have hSubSq :
      Int.mul (Int.sub (Int.mul α x₁) (Int.mul β x₂))
          (Int.sub (Int.mul α x₁) (Int.mul β x₂)) =
        Int.add
          (Int.add (Int.mul (Int.mul α α) (Int.mul x₁ x₁))
            (Int.mul (Int.mul β β) (Int.mul x₂ x₂)))
          (Int.neg (Int.add (Int.mul (Int.mul α x₁) (Int.mul β x₂))
            (Int.mul (Int.mul α x₁) (Int.mul β x₂)))) := by
    rw [int_sub_mul_dc, int_mul_sub_dc, int_mul_sub_dc, hP, hP,
      int_mul_comm_dc (Int.mul β x₂) (Int.mul α x₁)]
    rw [int_sub_eq_add_neg_dc, int_sub_eq_add_neg_dc, int_sub_eq_add_neg_dc,
      int_neg_add_dc, int_neg_neg_dc, int_neg_add_dc]
    rw [int_add_assoc_dc, int_add_comm_dc
        (Int.neg (Int.mul (Int.mul α x₁) (Int.mul β x₂)))
        (Int.add (Int.neg (Int.mul (Int.mul α x₁) (Int.mul β x₂)))
          (Int.mul (Int.mul β β) (Int.mul x₂ x₂))),
      int_add_assoc_dc,
      int_add_comm_dc (Int.mul (Int.mul β β) (Int.mul x₂ x₂)),
      ← int_add_assoc_dc
        (Int.neg (Int.mul (Int.mul α x₁) (Int.mul β x₂))),
      int_add_comm_dc
        (Int.add (Int.neg (Int.mul (Int.mul α x₁) (Int.mul β x₂)))
          (Int.neg (Int.mul (Int.mul α x₁) (Int.mul β x₂))))
        (Int.mul (Int.mul β β) (Int.mul x₂ x₂)),
      ← int_add_assoc_dc]
  have hAddSq :
      Int.mul (Int.add (Int.mul β x₁) (Int.mul α x₂))
          (Int.add (Int.mul β x₁) (Int.mul α x₂)) =
        Int.add
          (Int.add (Int.mul (Int.mul β β) (Int.mul x₁ x₁))
            (Int.mul (Int.mul α α) (Int.mul x₂ x₂)))
          (Int.add (Int.mul (Int.mul α x₁) (Int.mul β x₂))
            (Int.mul (Int.mul α x₁) (Int.mul β x₂))) := by
    rw [int_add_mul_dc, int_mul_add_dc, int_mul_add_dc, hP, hP,
      int_mul_comm_dc (Int.mul α x₂) (Int.mul β x₁), ← hCrossEq]
    rw [int_add_assoc_dc,
      int_add_comm_dc (Int.mul (Int.mul α x₁) (Int.mul β x₂))
        (Int.add (Int.mul (Int.mul α x₁) (Int.mul β x₂))
          (Int.mul (Int.mul α α) (Int.mul x₂ x₂))),
      int_add_assoc_dc,
      int_add_comm_dc (Int.mul (Int.mul α α) (Int.mul x₂ x₂)),
      ← int_add_assoc_dc (Int.mul (Int.mul α x₁) (Int.mul β x₂)),
      int_add_comm_dc
        (Int.add (Int.mul (Int.mul α x₁) (Int.mul β x₂))
          (Int.mul (Int.mul α x₁) (Int.mul β x₂)))
        (Int.mul (Int.mul α α) (Int.mul x₂ x₂)),
      ← int_add_assoc_dc]
  rw [hSubSq, hAddSq]
  -- Cancel opposite cross terms `(-2c) + (+2c) = 0`
  let a := Int.add (Int.mul (Int.mul α α) (Int.mul x₁ x₁))
    (Int.mul (Int.mul β β) (Int.mul x₂ x₂))
  let b := Int.add (Int.mul (Int.mul β β) (Int.mul x₁ x₁))
    (Int.mul (Int.mul α α) (Int.mul x₂ x₂))
  let c := Int.add (Int.mul (Int.mul α x₁) (Int.mul β x₂))
    (Int.mul (Int.mul α x₁) (Int.mul β x₂))
  have hCancel : Int.add (Int.add a (Int.neg c)) (Int.add b c) =
      Int.add a b := by
    rw [int_add_assoc_dc a (Int.neg c), int_add_comm_dc (Int.neg c) (Int.add b c),
      int_add_assoc_dc b c (Int.neg c), int_add_neg_cancel_dc,
      int_add_zero_dc]
  change Int.add (Int.add a (Int.neg c)) (Int.add b c) = _
  rw [hCancel]
  dsimp only [a, b]
  rw [int_add_mul_dc, int_mul_add_dc, int_mul_add_dc]
  rw [int_add_assoc_dc (Int.mul (Int.mul α α) (Int.mul x₁ x₁)),
    int_add_comm_dc (Int.mul (Int.mul β β) (Int.mul x₂ x₂)),
    int_add_assoc_dc (Int.mul (Int.mul β β) (Int.mul x₁ x₁)),
    int_add_comm_dc (Int.mul (Int.mul α α) (Int.mul x₂ x₂))
      (Int.mul (Int.mul β β) (Int.mul x₂ x₂)),
    ← int_add_assoc_dc (Int.mul (Int.mul β β) (Int.mul x₁ x₁)),
    int_add_comm_dc
      (Int.add (Int.mul (Int.mul β β) (Int.mul x₁ x₁))
        (Int.mul (Int.mul β β) (Int.mul x₂ x₂)))
      (Int.mul (Int.mul α α) (Int.mul x₂ x₂)),
    ← int_add_assoc_dc (Int.mul (Int.mul α α) (Int.mul x₁ x₁)),
    int_add_comm_dc (Int.mul (Int.mul β β) (Int.mul x₁ x₁))
      (Int.mul (Int.mul β β) (Int.mul x₂ x₂))]

/-- Symmetric signed saturation clamping `z` into `[-B, B]` for `B : Nat`
(`0` `._unsafe_rec`). -/
@[expose] def satSym (B : Nat) (z : Int) : Int :=
  match z with
  | Int.ofNat n =>
    match Nat.ble n B with
    | true => Int.ofNat n
    | false => Int.ofNat B
  | Int.negSucc k =>
    match Nat.ble (k + 1) B with
    | true => Int.negSucc k
    | false => Int.neg (Int.ofNat B)

private theorem natBle_true_iff_le_dc :
    ∀ a b : Nat, Nat.ble a b = true ↔ a ≤ b
  | 0, b => ⟨fun _ => Nat.zero_le b, fun _ => rfl⟩
  | _ + 1, 0 => ⟨fun h => Bool.noConfusion h, fun h => nomatch h⟩
  | a + 1, b + 1 =>
    ⟨fun h => Nat.succ_le_succ ((natBle_true_iff_le_dc a b).mp h),
     fun h => (natBle_true_iff_le_dc a b).mpr (Nat.le_of_succ_le_succ h)⟩

private theorem natLe_of_ble_false_dc {a b : Nat} (h : Nat.ble a b = false) :
    b ≤ a := by
  cases Nat.le_total b a with
  | inl hLe => exact hLe
  | inr hGe =>
    have hT := (natBle_true_iff_le_dc a b).mpr hGe
    rw [h] at hT
    exact Bool.noConfusion hT

/-- Componentwise symmetric saturation is non-expansive in square magnitude
(`(satSym B z)² ≤ z²`, `[propext]` only) for diagonal Euclidean norms. -/
theorem satSym_sq_le (B : Nat) (z : Int) :
    Int.mul (satSym B z) (satSym B z) ≤ Int.mul z z := by
  cases z with
  | ofNat n =>
    dsimp only [satSym]
    cases hB : Nat.ble n B with
    | true =>
      exact (intBalance_le (intBalance_self _) (intBalance_self _)).mpr
        (Nat.le_refl _)
    | false =>
      have hLe : B ≤ n := natLe_of_ble_false_dc hB
      exact (intBalance_le (intBalance_ofNat (B * B))
        (intBalance_ofNat (n * n))).mpr
        (by rw [Nat.add_zero, Nat.add_zero]; exact Nat.mul_le_mul hLe hLe)
  | negSucc k =>
    dsimp only [satSym]
    cases hB : Nat.ble (k + 1) B with
    | true =>
      exact (intBalance_le (intBalance_self _) (intBalance_self _)).mpr
        (Nat.le_refl _)
    | false =>
      have hLe : B ≤ k + 1 := natLe_of_ble_false_dc hB
      rw [int_neg_mul_dc, int_mul_neg_dc, int_neg_neg_dc]
      have hNegSq :
          Int.mul (Int.negSucc k) (Int.negSucc k) =
            Int.ofNat ((k + 1) * (k + 1)) :=
        intBalance_eq_int
          (intBalance_mul (intBalance_self (Int.negSucc k))
            (intBalance_self (Int.negSucc k)))
          (intBalance_ofNat ((k + 1) * (k + 1)))
          (by dsimp only [intPos, intNeg]
              rw [Nat.zero_mul, Nat.zero_mul, Nat.mul_zero, Nat.zero_add,
                Nat.add_zero, Nat.add_zero])
      rw [hNegSq]
      exact (intBalance_le (intBalance_ofNat (B * B))
        (intBalance_ofNat ((k + 1) * (k + 1)))).mpr
        (by rw [Nat.add_zero, Nat.add_zero]; exact Nat.mul_le_mul hLe hLe)

/-- Coupled normal-form zero-input saturation contraction (`[propext]` only):
applying symmetric saturation `satSym B` to the coupled normal-form next state
satisfies `‖sat(y)‖₂² ≤ (α² + β²) ‖x‖₂²`. -/
theorem coupled_normal_sat_contraction (B : Nat) (α β x₁ x₂ : Int) :
    let y₁ := Int.sub (Int.mul α x₁) (Int.mul β x₂)
    let y₂ := Int.add (Int.mul β x₁) (Int.mul α x₂)
    Int.add (Int.mul (satSym B y₁) (satSym B y₁))
        (Int.mul (satSym B y₂) (satSym B y₂)) ≤
      Int.mul (Int.add (Int.mul α α) (Int.mul β β))
        (Int.add (Int.mul x₁ x₁) (Int.mul x₂ x₂)) := by
  intro y₁ y₂
  rw [← coupled_normal_l2_identity α β x₁ x₂]
  have h1 := (int_le_iff_sub_nonneg _ _).mp (satSym_sq_le B y₁)
  have h2 := (int_le_iff_sub_nonneg _ _).mp (satSym_sq_le B y₂)
  apply (int_le_iff_sub_nonneg _ _).mpr
  have hEq :
      Int.sub (Int.add (Int.mul y₁ y₁) (Int.mul y₂ y₂))
          (Int.add (Int.mul (satSym B y₁) (satSym B y₁))
            (Int.mul (satSym B y₂) (satSym B y₂))) =
        Int.add (Int.sub (Int.mul y₁ y₁) (Int.mul (satSym B y₁) (satSym B y₁)))
          (Int.sub (Int.mul y₂ y₂) (Int.mul (satSym B y₂) (satSym B y₂))) := by
    rw [int_sub_eq_add_neg_dc, int_sub_eq_add_neg_dc, int_sub_eq_add_neg_dc,
      int_neg_add_dc, int_add_assoc_dc,
      ← int_add_assoc_dc (Int.mul y₂ y₂)
        (Int.neg (Int.mul (satSym B y₁) (satSym B y₁))),
      int_add_comm_dc (Int.mul y₂ y₂)
        (Int.neg (Int.mul (satSym B y₁) (satSym B y₁))),
      int_add_assoc_dc (Int.neg (Int.mul (satSym B y₁) (satSym B y₁))),
      ← int_add_assoc_dc]
  rw [hEq]
  exact int_add_nonneg h1 h2

end Anneal.Float.JuryStein

end
