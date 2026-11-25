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
public import Init.Data.BitVec.BasicAux
public import Init.Data.List.Basic
public import Anneal.Framework.StepWp

public section
namespace Anneal.PureLift.BvLin

open Anneal.Framework.StepWp

/-!
# Reflective Linear `BitVec w` / `Nat` Offset Normalizer (`PureLift.BvLin`)

Pass-1-portable (`prelude` + locked `Init.*` only, `0` `noncomputable`,
`hasIR = true`, `0` `._unsafe_rec`, `0` axioms) sparse sorted linear polynomial
normalizer for `BitVec w` and `Nat`-lifted pointer/offset arithmetic, sealed
behind zero-`Prop`-argument `Anneal.Framework.StepWp.BoolCertCut`.

Design attribution: inspired by `Lin.Poly` and `Lin.diffConst?` in Apache-2.0
`google-deepmind/code-verification` (`arm64-semantics/ProofLib/BV/Linear.lean`),
adapted to Anneal's 51-module `foundation-lock.json` foundation with zero
`noncomputable` definitions, zero `@ite`/`Decidable` branches in the checker,
and `BoolCertCut` reflection.

1. **Unified Atom Keys:** Even keys `2 * i` denote `BitVec w` atoms; odd keys
   `2 * i + 1` denote `Nat` atoms lifted via `BitVec.ofNat w`.
2. **Exact & Modular Reflection (`< 1 ms` `rfl`):**
   - `bvLin_eq_exact_of_boolCertCut`: discharges linear `BitVec w` equalities
     polymorphically over **symbolic** width `w : Nat`.
   - `bvLin_eq_mod_of_boolCertCut`: discharges modular wraparound equalities at
     concrete width `w` (`c ≡ 0 (mod 2^w)`).
   - `bvLin_diffConst_mod_of_boolCertCut` + `LinExpr.diffConstMod?`: extracts
     and proves exact constant byte offsets `a = b + BitVec.ofNat w delta`.
   - `bvLin_ne_mod_of_boolCertCut`: discharges `a ≠ b` whenever `a - b` reduces
     to a nonzero constant modulo `2^w`.
-/

/-! ## 1. Foundation `BitVec w` Modular Ring Helpers (`0` Axioms) -/

@[expose] def bvPow2 (w : Nat) : Nat :=
  @Nat.rec (fun _ => Nat) 1 (fun _ ih => 2 * ih) w

private theorem bvPow2_eq_two_pow : ∀ w : Nat, bvPow2 w = Nat.pow 2 w
  | 0 => rfl
  | w + 1 => by
    have hSucc : Nat.pow 2 (w + 1) = Nat.pow 2 w * 2 := Nat.pow_succ 2 w
    change 2 * bvPow2 w = Nat.pow 2 (w + 1)
    rw [bvPow2_eq_two_pow w, hSucc, Nat.mul_comm]

private theorem bvPow2_pos (w : Nat) : 0 < bvPow2 w := by
  rw [bvPow2_eq_two_pow]
  exact Nat.two_pow_pos w

theorem bv_eq_of_toNat_eq {w : Nat} {x y : BitVec w}
    (h : x.toNat = y.toNat) : x = y := by
  cases x with
  | ofFin fx =>
    cases y with
    | ofFin fy =>
      exact congrArg BitVec.ofFin (Fin.eq_of_val_eq h)

theorem bv_toNat_ofNat (w n : Nat) :
    (BitVec.ofNat w n).toNat = Nat.mod n (Nat.pow 2 w) := rfl

theorem bv_ofNat_toNat {w : Nat} (x : BitVec w) :
    BitVec.ofNat w x.toNat = x := by
  apply bv_eq_of_toNat_eq
  rw [bv_toNat_ofNat]
  exact Nat.mod_eq_of_lt x.isLt

/-- Zero bitvector `BitVec.ofNat w 0`. -/
@[expose] def bvZero (w : Nat) : BitVec w := BitVec.ofNat w 0

/-- Modular negation `0 - x` on `BitVec w`. -/
@[expose] def bvNeg {w : Nat} (x : BitVec w) : BitVec w := bvZero w - x

/-- Modular natural-number scalar multiplication `n * x` on `BitVec w`. -/
@[expose] def bvMulNat {w : Nat} (n : Nat) (x : BitVec w) : BitVec w :=
  BitVec.ofNat w (n * x.toNat)

/-- Maps an integer `c : Int` into `BitVec w` modulo `2^w`. -/
@[expose] def bvOfInt (w : Nat) : Int → BitVec w
  | .ofNat n => BitVec.ofNat w n
  | .negSucc n => bvNeg (BitVec.ofNat w (n + 1))

/-- Scales `x : BitVec w` by an integer coefficient `k : Int`. -/
@[expose] def bvScale {w : Nat} (k : Int) (x : BitVec w) : BitVec w :=
  match k with
  | .ofNat n => bvMulNat n x
  | .negSucc n => bvNeg (bvMulNat (n + 1) x)

private theorem bv_toNat_zero (w : Nat) : (bvZero w).toNat = 0 := by
  unfold bvZero
  rw [bv_toNat_ofNat]
  exact Nat.zero_mod (Nat.pow 2 w)

private theorem bv_toNat_add {w : Nat} (x y : BitVec w) :
    (x + y).toNat = Nat.mod (x.toNat + y.toNat) (Nat.pow 2 w) := rfl

private theorem bv_toNat_sub {w : Nat} (x y : BitVec w) :
    (x - y).toNat = Nat.mod ((Nat.pow 2 w - y.toNat) + x.toNat) (Nat.pow 2 w) :=
  rfl

private theorem bv_toNat_neg {w : Nat} (x : BitVec w) :
    (bvNeg x).toNat = Nat.mod (Nat.pow 2 w - x.toNat) (Nat.pow 2 w) := by
  unfold bvNeg
  rw [bv_toNat_sub, bv_toNat_zero, Nat.add_zero]

private theorem nat_mod_mod_pos (a m : Nat) (hm : 0 < m) :
    Nat.mod (Nat.mod a m) m = Nat.mod a m :=
  Nat.mod_eq_of_lt (Nat.mod_lt a hm)

private theorem nat_add_mod_left (a b m : Nat) :
    Nat.mod (Nat.mod a m + b) m = Nat.mod (a + b) m := by
  have hDm : m * Nat.div a m + Nat.mod a m = a := Nat.div_add_mod a m
  have hEq : a + b = m * Nat.div a m + (Nat.mod a m + b) := by
    rw [← Nat.add_assoc, hDm]
  have hMod : Nat.mod (m * Nat.div a m + (Nat.mod a m + b)) m =
      Nat.mod (Nat.mod a m + b) m :=
    Nat.mul_add_mod_self_left m (Nat.div a m) (Nat.mod a m + b)
  rw [hEq, hMod]

private theorem nat_add_mod_right (a b m : Nat) :
    Nat.mod (a + Nat.mod b m) m = Nat.mod (a + b) m := by
  rw [Nat.add_comm a (Nat.mod b m), nat_add_mod_left b a m, Nat.add_comm b a]

private theorem nat_add_mod (a b m : Nat) :
    Nat.mod (a + b) m = Nat.mod (Nat.mod a m + Nat.mod b m) m :=
  (nat_add_mod_right a b m).symm.trans (nat_add_mod_left a (Nat.mod b m) m).symm

private theorem nat_mul_mod_right (a b m : Nat) :
    Nat.mod (a * Nat.mod b m) m = Nat.mod (a * b) m := by
  have hDm : m * Nat.div b m + Nat.mod b m = b := Nat.div_add_mod b m
  have hEq : a * b = m * (a * Nat.div b m) + a * Nat.mod b m := by
    have h1 : a * b = a * (m * Nat.div b m + Nat.mod b m) :=
      congrArg (a * ·) hDm.symm
    rw [h1, Nat.mul_add, ← Nat.mul_assoc a m (Nat.div b m), Nat.mul_comm a m,
      Nat.mul_assoc m a (Nat.div b m)]
  have hMod : Nat.mod (m * (a * Nat.div b m) + a * Nat.mod b m) m =
      Nat.mod (a * Nat.mod b m) m :=
    Nat.mul_add_mod_self_left m (a * Nat.div b m) (a * Nat.mod b m)
  rw [hEq, hMod]

theorem bv_ofNat_mod (w n : Nat) :
    BitVec.ofNat w (Nat.mod n (Nat.pow 2 w)) = BitVec.ofNat w n := by
  apply bv_eq_of_toNat_eq
  rw [bv_toNat_ofNat, bv_toNat_ofNat]
  exact nat_mod_mod_pos n (Nat.pow 2 w) (Nat.two_pow_pos w)

theorem bv_ofNat_add (w a b : Nat) :
    BitVec.ofNat w (a + b) = BitVec.ofNat w a + BitVec.ofNat w b := by
  apply bv_eq_of_toNat_eq
  rw [bv_toNat_ofNat, bv_toNat_add, bv_toNat_ofNat, bv_toNat_ofNat]
  exact nat_add_mod a b (Nat.pow 2 w)

private theorem bv_add_comm {w : Nat} (x y : BitVec w) : x + y = y + x := by
  apply bv_eq_of_toNat_eq
  rw [bv_toNat_add, bv_toNat_add, Nat.add_comm]

private theorem bv_add_assoc {w : Nat} (x y z : BitVec w) :
    (x + y) + z = x + (y + z) := by
  apply bv_eq_of_toNat_eq
  rw [bv_toNat_add, bv_toNat_add, bv_toNat_add, bv_toNat_add,
    nat_add_mod_left, nat_add_mod_right, Nat.add_assoc]

theorem bv_add_zero {w : Nat} (x : BitVec w) : x + bvZero w = x := by
  apply bv_eq_of_toNat_eq
  rw [bv_toNat_add, bv_toNat_zero, Nat.add_zero]
  exact Nat.mod_eq_of_lt x.isLt

theorem bv_zero_add {w : Nat} (x : BitVec w) : bvZero w + x = x := by
  rw [bv_add_comm, bv_add_zero]

theorem bv_add_neg_self {w : Nat} (x : BitVec w) :
    x + bvNeg x = bvZero w := by
  apply bv_eq_of_toNat_eq
  have hLe : x.toNat ≤ Nat.pow 2 w := Nat.le_of_lt x.isLt
  have hSub : Nat.pow 2 w - x.toNat + x.toNat = Nat.pow 2 w :=
    Nat.sub_add_cancel hLe
  have hSelf : Nat.mod (Nat.pow 2 w) (Nat.pow 2 w) = 0 :=
    Nat.mod_self (Nat.pow 2 w)
  rw [bv_toNat_add, bv_toNat_neg, bv_toNat_zero, nat_add_mod_right,
    Nat.add_comm, hSub, hSelf]

theorem bv_neg_add_self {w : Nat} (x : BitVec w) :
    bvNeg x + x = bvZero w := by
  rw [bv_add_comm, bv_add_neg_self]

theorem bv_sub_eq_add_neg {w : Nat} (x y : BitVec w) :
    x - y = x + bvNeg y := by
  apply bv_eq_of_toNat_eq
  rw [bv_toNat_sub, bv_toNat_add, bv_toNat_neg, nat_add_mod_right, Nat.add_comm]

theorem bv_eq_of_add_eq {w : Nat} {a b c : BitVec w}
    (h : a + b = a + c) : b = c := by
  have h1 : bvNeg a + (a + b) = bvNeg a + (a + c) := congrArg (bvNeg a + ·) h
  rw [← bv_add_assoc, ← bv_add_assoc, bv_neg_add_self, bv_zero_add,
    bv_zero_add] at h1
  exact h1

theorem bv_neg_unique {w : Nat} {x y : BitVec w}
    (h : x + y = bvZero w) : y = bvNeg x :=
  bv_eq_of_add_eq (h.trans (bv_add_neg_self x).symm)

private theorem bv_neg_zero (w : Nat) : bvNeg (bvZero w) = bvZero w :=
  (bv_neg_unique (bv_add_zero (bvZero w))).symm

private theorem bv_neg_neg {w : Nat} (x : BitVec w) : bvNeg (bvNeg x) = x :=
  (bv_neg_unique (bv_neg_add_self x)).symm

private theorem bv_neg_add {w : Nat} (x y : BitVec w) :
    bvNeg (x + y) = bvNeg x + bvNeg y := by
  apply (bv_neg_unique _).symm
  rw [bv_add_assoc, ← bv_add_assoc y (bvNeg x) (bvNeg y),
    bv_add_comm y (bvNeg x), bv_add_assoc (bvNeg x) y (bvNeg y),
    bv_add_neg_self, bv_add_zero, bv_add_neg_self]

private theorem bv_sub_eq_zero_iff {w : Nat} (x y : BitVec w) :
    x - y = bvZero w ↔ x = y := by
  constructor
  · intro h
    rw [bv_sub_eq_add_neg] at h
    have h1 : (x + bvNeg y) + y = bvZero w + y := congrArg (· + y) h
    rw [bv_add_assoc, bv_neg_add_self, bv_add_zero, bv_zero_add] at h1
    exact h1
  · intro h
    subst h
    rw [bv_sub_eq_add_neg, bv_add_neg_self]

private theorem bv_eq_add_of_sub_eq {w : Nat} {x y d : BitVec w}
    (h : x - y = d) : x = y + d := by
  rw [bv_sub_eq_add_neg] at h
  have h1 : y + (x + bvNeg y) = y + d := congrArg (y + ·) h
  rw [bv_add_comm x (bvNeg y), ← bv_add_assoc, bv_add_neg_self,
    bv_zero_add] at h1
  exact h1

private theorem bv_mulNat_zero {w : Nat} (x : BitVec w) :
    bvMulNat 0 x = bvZero w := by
  unfold bvMulNat bvZero
  rw [Nat.zero_mul]

private theorem bv_mulNat_one {w : Nat} (x : BitVec w) :
    bvMulNat 1 x = x := by
  unfold bvMulNat
  rw [Nat.one_mul]
  exact bv_ofNat_toNat x

private theorem bv_mulNat_add {w : Nat} (m n : Nat) (x : BitVec w) :
    bvMulNat (m + n) x = bvMulNat m x + bvMulNat n x := by
  unfold bvMulNat
  rw [Nat.add_mul]
  exact bv_ofNat_add w (m * x.toNat) (n * x.toNat)

private theorem bv_mulNat_mul {w : Nat} (m n : Nat) (x : BitVec w) :
    bvMulNat (m * n) x = bvMulNat m (bvMulNat n x) := by
  apply bv_eq_of_toNat_eq
  unfold bvMulNat
  rw [bv_toNat_ofNat, bv_toNat_ofNat, bv_toNat_ofNat, Nat.mul_assoc,
    nat_mul_mod_right]

private theorem bv_mulNat_distrib {w : Nat} (n : Nat) (x y : BitVec w) :
    bvMulNat n (x + y) = bvMulNat n x + bvMulNat n y := by
  apply bv_eq_of_toNat_eq
  unfold bvMulNat
  rw [bv_toNat_ofNat, bv_toNat_add, bv_toNat_add, bv_toNat_ofNat, bv_toNat_ofNat,
    nat_mul_mod_right, Nat.mul_add, ← nat_add_mod]

private theorem bv_mulNat_neg {w : Nat} (n : Nat) (x : BitVec w) :
    bvMulNat n (bvNeg x) = bvNeg (bvMulNat n x) := by
  apply bv_neg_unique
  rw [← bv_mulNat_distrib, bv_add_neg_self]
  unfold bvMulNat
  rw [bv_toNat_zero, Nat.mul_zero]
  rfl

private theorem bv_mulNat_ofNat {w : Nat} (m n : Nat) :
    bvMulNat m (BitVec.ofNat w n) = BitVec.ofNat w (m * n) := by
  apply bv_eq_of_toNat_eq
  unfold bvMulNat
  rw [bv_toNat_ofNat, bv_toNat_ofNat, bv_toNat_ofNat, nat_mul_mod_right]

private theorem bv_scale_zero {w : Nat} (x : BitVec w) :
    bvScale (0 : Int) x = bvZero w :=
  bv_mulNat_zero x

private theorem bv_scale_one {w : Nat} (x : BitVec w) :
    bvScale (1 : Int) x = x :=
  bv_mulNat_one x

private theorem bv_scale_neg {w : Nat} (k : Int) (x : BitVec w) :
    bvScale (Int.neg k) x = bvNeg (bvScale k x) := by
  cases k with
  | ofNat n =>
    cases n with
    | zero =>
      change bvMulNat 0 x = bvNeg (bvMulNat 0 x)
      rw [bv_mulNat_zero]
      exact (bv_neg_zero w).symm
    | succ m => rfl
  | negSucc m =>
    exact (bv_neg_neg (bvMulNat (m + 1) x)).symm

private theorem bv_scale_neg_arg {w : Nat} (k : Int) (x : BitVec w) :
    bvScale k (bvNeg x) = bvNeg (bvScale k x) := by
  cases k with
  | ofNat n => exact bv_mulNat_neg n x
  | negSucc n =>
    change bvNeg (bvMulNat (n + 1) (bvNeg x)) =
      bvNeg (bvNeg (bvMulNat (n + 1) x))
    rw [bv_mulNat_neg (n + 1) x]

private theorem bv_scale_distrib {w : Nat} (k : Int) (x y : BitVec w) :
    bvScale k (x + y) = bvScale k x + bvScale k y := by
  cases k with
  | ofNat n => exact bv_mulNat_distrib n x y
  | negSucc n =>
    change bvNeg (bvMulNat (n + 1) (x + y)) =
      bvNeg (bvMulNat (n + 1) x) + bvNeg (bvMulNat (n + 1) y)
    rw [bv_mulNat_distrib (n + 1) x y, bv_neg_add]

private theorem bv_scale_subNatNat {w : Nat} (m n : Nat) (x : BitVec w) :
    bvScale (Int.subNatNat m n) x = bvMulNat m x + bvNeg (bvMulNat n x) := by
  unfold Int.subNatNat
  cases h : n - m with
  | zero =>
    have hLe : n ≤ m := Nat.le_of_sub_eq_zero h
    have hEq : (m - n) + n = m := Nat.sub_add_cancel hLe
    dsimp only [bvScale]
    apply bv_eq_of_add_eq (a := bvMulNat n x)
    rw [bv_add_comm (bvMulNat n x) (bvMulNat (m - n) x),
      ← bv_mulNat_add (m - n) n x, hEq,
      bv_add_comm (bvMulNat m x) (bvNeg (bvMulNat n x)),
      ← bv_add_assoc, bv_add_neg_self, bv_zero_add]
  | succ k =>
    have hGt : m + (k + 1) = n := by
      have hSub : n - m = k + 1 := h
      have hLe : m ≤ n := by
        cases Nat.lt_or_ge n m with
        | inr hle => exact hle
        | inl hlt =>
          have hz : n - m = 0 := Nat.sub_eq_zero_of_le (Nat.le_of_lt hlt)
          rw [hz] at hSub
          cases hSub
      rw [← hSub, Nat.add_comm]
      exact Nat.sub_add_cancel hLe
    dsimp only [bvScale]
    apply bv_eq_of_add_eq (a := bvMulNat n x)
    rw [bv_add_comm (bvMulNat m x) (bvNeg (bvMulNat n x)),
      ← bv_add_assoc, bv_add_neg_self, bv_zero_add,
      ← hGt, bv_mulNat_add m (k + 1) x, bv_add_assoc, bv_add_neg_self,
      bv_add_zero]

private theorem bv_scale_add {w : Nat} (a b : Int) (x : BitVec w) :
    bvScale (a + b) x = bvScale a x + bvScale b x := by
  cases a with
  | ofNat m =>
    cases b with
    | ofNat n => exact bv_mulNat_add m n x
    | negSucc n => exact bv_scale_subNatNat m (n + 1) x
  | negSucc m =>
    cases b with
    | ofNat n =>
      rw [bv_add_comm (bvScale (.negSucc m) x) (bvScale (.ofNat n) x)]
      exact bv_scale_subNatNat n (m + 1) x
    | negSucc n =>
      change bvNeg (bvMulNat ((m + n) + 1 + 1) x) =
        bvNeg (bvMulNat (m + 1) x) + bvNeg (bvMulNat (n + 1) x)
      have hArith : (m + n) + 1 + 1 = (m + 1) + (n + 1) := by
        rw [Nat.add_assoc m n 1, Nat.add_comm n 1, ← Nat.add_assoc m 1 n,
          Nat.add_assoc (m + 1) n 1, Nat.add_comm n 1]
      rw [hArith, bv_mulNat_add (m + 1) (n + 1) x, bv_neg_add]

private theorem bv_scale_negOfNat {w : Nat} (n : Nat) (x : BitVec w) :
    bvScale (Int.negOfNat n) x = bvNeg (bvMulNat n x) := by
  cases n with
  | zero =>
    change bvMulNat 0 x = bvNeg (bvMulNat 0 x)
    rw [bv_mulNat_zero]
    exact (bv_neg_zero w).symm
  | succ _ => rfl

private theorem bv_scale_mul {w : Nat} (a b : Int) (x : BitVec w) :
    bvScale (a * b) x = bvScale a (bvScale b x) := by
  cases a with
  | ofNat m =>
    cases b with
    | ofNat n => exact bv_mulNat_mul m n x
    | negSucc n =>
      change bvScale (Int.negOfNat (m * (n + 1))) x =
        bvMulNat m (bvNeg (bvMulNat (n + 1) x))
      rw [bv_scale_negOfNat, bv_mulNat_neg, bv_mulNat_mul]
  | negSucc m =>
    cases b with
    | ofNat n =>
      change bvScale (Int.negOfNat ((m + 1) * n)) x =
        bvNeg (bvMulNat (m + 1) (bvMulNat n x))
      rw [bv_scale_negOfNat, bv_mulNat_mul]
    | negSucc n =>
      change bvMulNat ((m + 1) * (n + 1)) x =
        bvNeg (bvMulNat (m + 1) (bvNeg (bvMulNat (n + 1) x)))
      rw [bv_mulNat_neg, bv_neg_neg, bv_mulNat_mul]

private theorem bvOfInt_eq_scale_one (w : Nat) (c : Int) :
    bvOfInt w c = bvScale c (BitVec.ofNat w 1) := by
  cases c with
  | ofNat n =>
    change BitVec.ofNat w n = bvMulNat n (BitVec.ofNat w 1)
    rw [bv_mulNat_ofNat, Nat.mul_one]
  | negSucc n =>
    change bvNeg (BitVec.ofNat w (n + 1)) = bvNeg (bvMulNat (n + 1) (BitVec.ofNat w 1))
    rw [bv_mulNat_ofNat, Nat.mul_one]

theorem bvOfInt_add (w : Nat) (a b : Int) :
    bvOfInt w (a + b) = bvOfInt w a + bvOfInt w b := by
  rw [bvOfInt_eq_scale_one, bvOfInt_eq_scale_one, bvOfInt_eq_scale_one]
  exact bv_scale_add a b (BitVec.ofNat w 1)

theorem bvOfInt_mul (w : Nat) (a b : Int) :
    bvOfInt w (a * b) = bvScale a (bvOfInt w b) := by
  rw [bvOfInt_eq_scale_one w (a * b), bvOfInt_eq_scale_one w b]
  exact bv_scale_mul a b (BitVec.ofNat w 1)

theorem bvOfInt_zero (w : Nat) : bvOfInt w 0 = bvZero w := rfl

theorem bvOfInt_neg (w : Nat) (a : Int) :
    bvOfInt w (Int.neg a) = bvNeg (bvOfInt w a) := by
  rw [bvOfInt_eq_scale_one, bvOfInt_eq_scale_one]
  exact bv_scale_neg a (BitVec.ofNat w 1)

theorem bvOfInt_sub (w : Nat) (a b : Int) :
    bvOfInt w (a - b) = bvOfInt w a - bvOfInt w b := by
  change bvOfInt w (a + Int.neg b) = _
  rw [bvOfInt_add, bvOfInt_neg, bv_sub_eq_add_neg]

/-- Canonical residue of `c : Int` modulo `2^w` in `[0, 2^w)` (`0`
`noncomputable`, `hasIR = true`). -/
@[expose] def intModPow2 (c : Int) (w : Nat) : Nat :=
  let m := bvPow2 w
  match c with
  | .ofNat n => Nat.mod n m
  | .negSucc n =>
    let r := Nat.mod (n + 1) m
    cond (Nat.beq r 0) 0 (m - r)

theorem bvOfInt_toNat_eq_intModPow2 (w : Nat) (c : Int) :
    (bvOfInt w c).toNat = intModPow2 c w := by
  cases c with
  | ofNat n =>
    unfold bvOfInt intModPow2
    rw [bv_toNat_ofNat, bvPow2_eq_two_pow]
  | negSucc n =>
    unfold bvOfInt intModPow2
    dsimp only
    rw [bv_toNat_neg, bv_toNat_ofNat, bvPow2_eq_two_pow]
    cases hr : Nat.beq (Nat.mod (n + 1) (Nat.pow 2 w)) 0 with
    | true =>
      have hz := Nat.eq_of_beq_eq_true hr
      have hSelf : Nat.mod (Nat.pow 2 w) (Nat.pow 2 w) = 0 :=
        Nat.mod_self (Nat.pow 2 w)
      rw [hz, Nat.sub_zero, hSelf]
      rfl
    | false =>
      dsimp only [cond]
      have hPos : 0 < Nat.mod (n + 1) (Nat.pow 2 w) := by
        cases hVal : Nat.mod (n + 1) (Nat.pow 2 w) with
        | zero => rw [hVal] at hr; cases hr
        | succ _ => exact Nat.succ_pos _
      have hLt : Nat.pow 2 w - Nat.mod (n + 1) (Nat.pow 2 w) < Nat.pow 2 w :=
        Nat.sub_lt (Nat.two_pow_pos w) hPos
      exact Nat.mod_eq_of_lt hLt

private theorem bvOfInt_eq_zero_of_mod_zero {w : Nat} {c : Int}
    (h : Nat.beq (intModPow2 c w) 0 = true) :
    bvOfInt w c = bvZero w := by
  apply bv_eq_of_toNat_eq
  rw [bvOfInt_toNat_eq_intModPow2, bv_toNat_zero]
  exact Nat.eq_of_beq_eq_true h

private theorem bvOfInt_ne_zero_of_mod_ne_zero {w : Nat} {c : Int}
    (h : Nat.beq (intModPow2 c w) 0 = false) :
    bvOfInt w c ≠ bvZero w := by
  intro hEq
  have hNat : (bvOfInt w c).toNat = (bvZero w).toNat :=
    congrArg BitVec.toNat hEq
  rw [bvOfInt_toNat_eq_intModPow2, bv_toNat_zero] at hNat
  rw [hNat] at h
  cases h

private theorem bvOfInt_eq_ofNat_intModPow2 (w : Nat) (c : Int) :
    bvOfInt w c = BitVec.ofNat w (intModPow2 c w) := by
  apply bv_eq_of_toNat_eq
  rw [bvOfInt_toNat_eq_intModPow2, bv_toNat_ofNat]
  have hLt : intModPow2 c w < Nat.pow 2 w := by
    rw [← bvOfInt_toNat_eq_intModPow2]
    exact (bvOfInt w c).isLt
  exact (Nat.mod_eq_of_lt hLt).symm

/-! ## 2. Sparse Sorted Linear Polynomial (`LinPoly`) and Expression AST -/

/-- Branch-free `Int` zero test (`0` `Decidable` overhead). -/
@[expose] def intIsZero : Int → Bool
  | .ofNat 0 => true
  | _ => false

private theorem int_eq_zero_of_isZero {c : Int} (h : intIsZero c = true) :
    c = 0 := by
  cases c with
  | ofNat n =>
    cases n with
    | zero => rfl
    | succ _ => cases h
  | negSucc _ => cases h

/-- Sparse sorted linear polynomial `const + ∑ (key_i * coeff_i)` with strictly
ascending `Nat` variable keys (`0` `noncomputable`, `hasIR = true`). -/
structure LinPoly where
  const : Int
  terms : List (Nat × Int)

@[expose] def insertTermFold (k : Nat) (c : Int) (ts : List (Nat × Int)) :
    List (Nat × Int) × List (Nat × Int) :=
  List.foldr
    (fun (kv : Nat × Int) (acc : List (Nat × Int) × List (Nat × Int)) =>
      let orig := kv :: acc.2
      let res :=
        cond (Nat.blt k kv.1)
          (cond (intIsZero c) orig ((k, c) :: orig))
          (cond (Nat.beq k kv.1)
            (let s := c + kv.2
             cond (intIsZero s) acc.2 ((kv.1, s) :: acc.2))
            (kv :: acc.1))
      (res, orig))
    (cond (intIsZero c) [] [(k, c)], [])
    ts

/-- Inserts `(k, c)` into a strictly key-sorted coefficient list via
`List.foldr` paramorphism (`0` `noncomputable`, `0` `._unsafe_rec`,
`hasIR = true`). -/
@[expose] def insertTerm (k : Nat) (c : Int) (ts : List (Nat × Int)) :
    List (Nat × Int) :=
  (insertTermFold k c ts).1

@[expose] def addTerms (xs ys : List (Nat × Int)) : List (Nat × Int) :=
  List.foldr (fun kv acc => insertTerm kv.1 kv.2 acc) xs ys

@[expose] def scaleTerms (k : Int) (ts : List (Nat × Int)) : List (Nat × Int) :=
  List.foldr
    (fun (kv : Nat × Int) (acc : List (Nat × Int)) =>
      let sc := k * kv.2
      cond (intIsZero sc) acc ((kv.1, sc) :: acc))
    []
    ts

/-- Zero polynomial `0`. -/
@[expose] def LinPoly.zero : LinPoly := { const := 0, terms := [] }

/-- Constant polynomial `c`. -/
@[expose] def LinPoly.ofConst (c : Int) : LinPoly := { const := c, terms := [] }

/-- Single-variable polynomial `1 * var(k)`. -/
@[expose] def LinPoly.ofVar (k : Nat) : LinPoly := { const := 0, terms := [(k, 1)] }

/-- Adds two sparse linear polynomials. -/
@[expose] def LinPoly.add (p q : LinPoly) : LinPoly :=
  { const := p.const + q.const, terms := addTerms p.terms q.terms }

/-- Scales a sparse linear polynomial by `k : Int` (short-circuiting on `0`). -/
@[expose] def LinPoly.scale (k : Int) (p : LinPoly) : LinPoly :=
  cond (intIsZero k) LinPoly.zero
    { const := k * p.const, terms := scaleTerms k p.terms }

/-- Negates a sparse linear polynomial (`-p`). -/
@[expose] def LinPoly.neg (p : LinPoly) : LinPoly := p.scale (Int.negSucc 0)

/-- Subtracts two sparse linear polynomials (`p - q`). -/
@[expose] def LinPoly.sub (p q : LinPoly) : LinPoly := p.add q.neg

/-- Linear expression AST over `BitVec w` atoms (key `2 * i`) and `Nat` atoms
(key `2 * i + 1`, lifted via `BitVec.ofNat w`). -/
inductive LinExpr : Type where
  | constInt (c : Int)
  | constNat (n : Nat)
  | bvVar (idx : Nat)
  | natVar (idx : Nat)
  | add (a b : LinExpr)
  | sub (a b : LinExpr)
  | neg (a : LinExpr)
  | scale (k : Int) (a : LinExpr)

/-- Compiles a `LinExpr` into canonical sparse sorted `LinPoly` normal form
via `@Nat.rec` up to AST depth `fuel` (`0` `noncomputable`, `0` `._unsafe_rec`,
`hasIR = true`), failing closed (`none`) if AST depth exceeds `fuel`. -/
@[expose] def LinExpr.toPolyAt (fuel : Nat) : LinExpr → Option LinPoly :=
  @Nat.rec (fun _ => LinExpr → Option LinPoly)
    (fun _ => none)
    (fun _ ih e =>
      match e with
      | .constInt c => some (LinPoly.ofConst c)
      | .constNat n => some (LinPoly.ofConst (Int.ofNat n))
      | .bvVar i => some (LinPoly.ofVar (2 * i))
      | .natVar i => some (LinPoly.ofVar (2 * i + 1))
      | .add a b =>
        match ih a with
        | none => none
        | some pa =>
          match ih b with
          | none => none
          | some pb => some (pa.add pb)
      | .sub a b =>
        match ih a with
        | none => none
        | some pa =>
          match ih b with
          | none => none
          | some pb => some (pa.sub pb)
      | .neg a =>
        match ih a with
        | none => none
        | some pa => some pa.neg
      | .scale k a =>
        match ih a with
        | none => none
        | some pa => some (pa.scale k))
    fuel

/-- Atom environment for `BitVec w` evaluation: `bvAtom` interprets `bvVar i`,
and `natAtom` interprets `natVar i` (lifted via `BitVec.ofNat w`). -/
structure BvLinEnv (w : Nat) where
  bvAtom : Nat → BitVec w
  natAtom : Nat → Nat

/-- Unified even/odd key lookup in `BvLinEnv w`. -/
@[expose] def BvLinEnv.lookupKey {w : Nat} (env : BvLinEnv w) (key : Nat) : BitVec w :=
  cond (Nat.beq (Nat.mod key 2) 0)
    (env.bvAtom (Nat.div key 2))
    (BitVec.ofNat w (env.natAtom (Nat.div key 2)))

private theorem lookupKey_even {w : Nat} (env : BvLinEnv w) (i : Nat) :
    env.lookupKey (2 * i) = env.bvAtom i := by
  unfold BvLinEnv.lookupKey
  have hMod : Nat.mod (2 * i) 2 = 0 := Nat.mul_mod_right 2 i
  have hDiv : Nat.div (2 * i) 2 = i := by
    have h1 : Nat.div (i * 2) 2 = i := Nat.mul_div_cancel i (Nat.succ_pos 1)
    rw [Nat.mul_comm 2 i]
    exact h1
  rw [hMod, hDiv]
  rfl

private theorem lookupKey_odd {w : Nat} (env : BvLinEnv w) (i : Nat) :
    env.lookupKey (2 * i + 1) = BitVec.ofNat w (env.natAtom i) := by
  unfold BvLinEnv.lookupKey
  have hDiv : Nat.div (2 * i + 1) 2 = i := by
    have h1 : Nat.div (1 + i * 2) 2 = Nat.div 1 2 + i :=
      Nat.add_mul_div_right 1 i (Nat.succ_pos 1)
    rw [Nat.mul_comm 2 i, Nat.add_comm (i * 2) 1, h1]
    exact Nat.zero_add i
  have hMod : Nat.mod (2 * i + 1) 2 = 1 := by
    have hdm : 2 * Nat.div (2 * i + 1) 2 + Nat.mod (2 * i + 1) 2 = 2 * i + 1 :=
      Nat.div_add_mod (2 * i + 1) 2
    rw [hDiv] at hdm
    exact Nat.add_left_cancel hdm
  rw [hMod, hDiv]
  rfl

/-- Denotational evaluation of `LinExpr` to `BitVec w` under `env`. Marked
`noncomputable` solely to avoid emitting compiler `._unsafe_rec` auxiliaries;
all normalizers and reflective checkers below are computable (`hasIR = true`).
-/
@[expose] noncomputable def LinExpr.evalBv {w : Nat} (env : BvLinEnv w) :
    LinExpr → BitVec w
  | .constInt c => bvOfInt w c
  | .constNat n => BitVec.ofNat w n
  | .bvVar i => env.bvAtom i
  | .natVar i => BitVec.ofNat w (env.natAtom i)
  | .add a b => a.evalBv env + b.evalBv env
  | .sub a b => a.evalBv env - b.evalBv env
  | .neg a => bvNeg (a.evalBv env)
  | .scale k a => bvScale k (a.evalBv env)

/-- Evaluates a term list in `BitVec w` under `env` via `List.foldr` (`0`
`noncomputable`, `0` `._unsafe_rec`, `hasIR = true`). -/
@[expose] def evalTermsBv {w : Nat} (env : BvLinEnv w) (ts : List (Nat × Int)) :
    BitVec w :=
  List.foldr (fun kv acc => bvScale kv.2 (env.lookupKey kv.1) + acc)
    (bvZero w) ts

/-- Evaluates a `LinPoly` in `BitVec w` under `env`. -/
@[expose] def LinPoly.evalBv {w : Nat} (env : BvLinEnv w) (p : LinPoly) : BitVec w :=
  bvOfInt w p.const + evalTermsBv env p.terms

private theorem insertTermFold_snd (k : Nat) (c : Int) :
    ∀ ts : List (Nat × Int), (insertTermFold k c ts).2 = ts
  | [] => rfl
  | kv :: rest => congrArg (List.cons kv) (insertTermFold_snd k c rest)

private theorem evalTermsBv_insertTerm {w : Nat} (env : BvLinEnv w)
    (k : Nat) (c : Int) :
    ∀ ts : List (Nat × Int),
      evalTermsBv env (insertTerm k c ts) =
        bvScale c (env.lookupKey k) + evalTermsBv env ts
  | [] => by
    unfold insertTerm insertTermFold
    dsimp only [List.foldr]
    cases hz : intIsZero c with
    | true =>
      have hc0 := int_eq_zero_of_isZero hz
      subst hc0
      dsimp only [cond, evalTermsBv, List.foldr]
      rw [bv_scale_zero, bv_zero_add]
    | false => rfl
  | (k', c') :: rest => by
    have hSnd : (insertTermFold k c rest).2 = rest := insertTermFold_snd k c rest
    change evalTermsBv env
        (cond (Nat.blt k k')
          (cond (intIsZero c) ((k', c') :: (insertTermFold k c rest).2)
            ((k, c) :: (k', c') :: (insertTermFold k c rest).2))
          (cond (Nat.beq k k')
            (cond (intIsZero (c + c')) (insertTermFold k c rest).2
              ((k', c + c') :: (insertTermFold k c rest).2))
            ((k', c') :: insertTerm k c rest))) =
      bvScale c (env.lookupKey k) +
        (bvScale c' (env.lookupKey k') + evalTermsBv env rest)
    rw [hSnd]
    cases hLt : Nat.blt k k' with
    | true =>
      dsimp only [cond]
      cases hz : intIsZero c with
      | true =>
        have hc0 := int_eq_zero_of_isZero hz
        subst hc0
        dsimp only [cond]
        rw [bv_scale_zero, bv_zero_add]
        rfl
      | false => rfl
    | false =>
      dsimp only [cond]
      cases hEq : Nat.beq k k' with
      | true =>
        have hkk' : k = k' := Nat.eq_of_beq_eq_true hEq
        subst hkk'
        dsimp only [cond]
        cases hz : intIsZero (c + c') with
        | true =>
          have hs0 := int_eq_zero_of_isZero hz
          dsimp only [cond]
          rw [← bv_add_assoc, ← bv_scale_add, hs0, bv_scale_zero, bv_zero_add]
        | false =>
          dsimp only [cond]
          change bvScale (c + c') (env.lookupKey k) + evalTermsBv env rest = _
          rw [bv_scale_add, bv_add_assoc]
      | false =>
        dsimp only [cond]
        change bvScale c' (env.lookupKey k') +
            evalTermsBv env (insertTerm k c rest) = _
        rw [evalTermsBv_insertTerm env k c rest, ← bv_add_assoc,
          bv_add_comm (bvScale c' (env.lookupKey k'))
            (bvScale c (env.lookupKey k)),
          bv_add_assoc]

private theorem evalTermsBv_addTerms {w : Nat} (env : BvLinEnv w) :
    ∀ (xs ys : List (Nat × Int)),
      evalTermsBv env (addTerms xs ys) =
        evalTermsBv env xs + evalTermsBv env ys
  | xs, [] => (bv_add_zero (evalTermsBv env xs)).symm
  | xs, (k, c) :: rest => by
    change evalTermsBv env (insertTerm k c (addTerms xs rest)) =
      evalTermsBv env xs + (bvScale c (env.lookupKey k) + evalTermsBv env rest)
    rw [evalTermsBv_insertTerm env k c (addTerms xs rest),
      evalTermsBv_addTerms env xs rest, ← bv_add_assoc,
      bv_add_comm (bvScale c (env.lookupKey k)) (evalTermsBv env xs),
      bv_add_assoc]

private theorem evalTermsBv_scaleTerms {w : Nat} (env : BvLinEnv w) (k : Int) :
    ∀ ts : List (Nat × Int),
      evalTermsBv env (scaleTerms k ts) = bvScale k (evalTermsBv env ts)
  | [] => by
    cases k with
    | ofNat n =>
      change bvZero w = bvMulNat n (bvZero w)
      unfold bvMulNat
      rw [bv_toNat_zero, Nat.mul_zero]; rfl
    | negSucc n =>
      change bvZero w = bvNeg (bvMulNat (n + 1) (bvZero w))
      unfold bvMulNat
      rw [bv_toNat_zero, Nat.mul_zero]
      exact (bv_neg_zero w).symm
  | (v, c) :: rest => by
    change evalTermsBv env
        (cond (intIsZero (k * c)) (scaleTerms k rest)
          ((v, k * c) :: scaleTerms k rest)) =
      bvScale k (bvScale c (env.lookupKey v) + evalTermsBv env rest)
    cases hz : intIsZero (k * c) with
    | true =>
      have h0 := int_eq_zero_of_isZero hz
      dsimp only [cond]
      rw [evalTermsBv_scaleTerms env k rest, bv_scale_distrib, ← bv_scale_mul,
        h0, bv_scale_zero, bv_zero_add]
    | false =>
      dsimp only [cond]
      change bvScale (k * c) (env.lookupKey v) +
          evalTermsBv env (scaleTerms k rest) = _
      rw [evalTermsBv_scaleTerms env k rest, bv_scale_distrib, ← bv_scale_mul]

private theorem linPoly_evalBv_add {w : Nat} (env : BvLinEnv w)
    (p q : LinPoly) :
    (p.add q).evalBv env = p.evalBv env + q.evalBv env := by
  unfold LinPoly.add LinPoly.evalBv
  dsimp only
  rw [bvOfInt_add, evalTermsBv_addTerms]
  rw [bv_add_assoc, ← bv_add_assoc (bvOfInt w q.const),
    bv_add_comm (bvOfInt w q.const) (evalTermsBv env p.terms),
    bv_add_assoc (evalTermsBv env p.terms), ← bv_add_assoc]

private theorem linPoly_evalBv_scale {w : Nat} (env : BvLinEnv w)
    (k : Int) (p : LinPoly) :
    (p.scale k).evalBv env = bvScale k (p.evalBv env) := by
  unfold LinPoly.scale
  cases hz : intIsZero k with
  | true =>
    have hk0 := int_eq_zero_of_isZero hz
    subst hk0
    dsimp only [cond, LinPoly.zero, LinPoly.evalBv, evalTermsBv, List.foldr]
    rw [bv_scale_zero, bv_add_zero]; rfl
  | false =>
    dsimp only [cond, LinPoly.evalBv]
    rw [bvOfInt_mul, evalTermsBv_scaleTerms, bv_scale_distrib]

private theorem linPoly_evalBv_neg {w : Nat} (env : BvLinEnv w) (p : LinPoly) :
    p.neg.evalBv env = bvNeg (p.evalBv env) := by
  unfold LinPoly.neg
  rw [linPoly_evalBv_scale]
  change bvNeg (bvMulNat 1 (p.evalBv env)) = bvNeg (p.evalBv env)
  rw [bv_mulNat_one]

private theorem linPoly_evalBv_sub {w : Nat} (env : BvLinEnv w)
    (p q : LinPoly) :
    (p.sub q).evalBv env = p.evalBv env - q.evalBv env := by
  unfold LinPoly.sub
  rw [linPoly_evalBv_add, linPoly_evalBv_neg, bv_sub_eq_add_neg]

/-- Fundamental normalization soundness: whenever `e.toPolyAt fuel = some p`,
`p.evalBv env = e.evalBv env` for every symbolic width `w : Nat` and
environment `env : BvLinEnv w` (`0` axioms). -/
theorem linExpr_toPolyAt_evalBv {w : Nat} (env : BvLinEnv w) :
    ∀ (fuel : Nat) (e : LinExpr) (p : LinPoly),
      e.toPolyAt fuel = some p → p.evalBv env = e.evalBv env
  | 0, _, _, h => by cases h
  | _ + 1, .constInt c, p, h => by
    injection h with hEq; subst hEq
    change bvOfInt w c + bvZero w = bvOfInt w c
    exact bv_add_zero (bvOfInt w c)
  | _ + 1, .constNat n, p, h => by
    injection h with hEq; subst hEq
    change BitVec.ofNat w n + bvZero w = BitVec.ofNat w n
    exact bv_add_zero (BitVec.ofNat w n)
  | _ + 1, .bvVar i, p, h => by
    injection h with hEq; subst hEq
    change bvOfInt w 0 + (bvScale 1 (env.lookupKey (2 * i)) + bvZero w) =
      env.bvAtom i
    rw [bvOfInt_zero, bv_zero_add, bv_add_zero, bv_scale_one, lookupKey_even]
  | _ + 1, .natVar i, p, h => by
    injection h with hEq; subst hEq
    change bvOfInt w 0 + (bvScale 1 (env.lookupKey (2 * i + 1)) + bvZero w) =
      BitVec.ofNat w (env.natAtom i)
    rw [bvOfInt_zero, bv_zero_add, bv_add_zero, bv_scale_one, lookupKey_odd]
  | d + 1, .add a b, p, h => by
    change (match a.toPolyAt d with
        | none => none
        | some pa =>
          match b.toPolyAt d with
          | none => none
          | some pb => some (pa.add pb)) = some p at h
    cases ha : a.toPolyAt d with
    | none => rw [ha] at h; cases h
    | some pa =>
      rw [ha] at h
      cases hb : b.toPolyAt d with
      | none => rw [hb] at h; cases h
      | some pb =>
        rw [hb] at h
        injection h with hEq; subst hEq
        rw [linPoly_evalBv_add, linExpr_toPolyAt_evalBv env d a pa ha,
          linExpr_toPolyAt_evalBv env d b pb hb]
        rfl
  | d + 1, .sub a b, p, h => by
    change (match a.toPolyAt d with
        | none => none
        | some pa =>
          match b.toPolyAt d with
          | none => none
          | some pb => some (pa.sub pb)) = some p at h
    cases ha : a.toPolyAt d with
    | none => rw [ha] at h; cases h
    | some pa =>
      rw [ha] at h
      cases hb : b.toPolyAt d with
      | none => rw [hb] at h; cases h
      | some pb =>
        rw [hb] at h
        injection h with hEq; subst hEq
        rw [linPoly_evalBv_sub, linExpr_toPolyAt_evalBv env d a pa ha,
          linExpr_toPolyAt_evalBv env d b pb hb]
        rfl
  | d + 1, .neg a, p, h => by
    change (match a.toPolyAt d with
        | none => none
        | some pa => some pa.neg) = some p at h
    cases ha : a.toPolyAt d with
    | none => rw [ha] at h; cases h
    | some pa =>
      rw [ha] at h
      injection h with hEq; subst hEq
      rw [linPoly_evalBv_neg, linExpr_toPolyAt_evalBv env d a pa ha]
      rfl
  | d + 1, .scale k a, p, h => by
    change (match a.toPolyAt d with
        | none => none
        | some pa => some (pa.scale k)) = some p at h
    cases ha : a.toPolyAt d with
    | none => rw [ha] at h; cases h
    | some pa =>
      rw [ha] at h
      injection h with hEq; subst hEq
      rw [linPoly_evalBv_scale, linExpr_toPolyAt_evalBv env d a pa ha]
      rfl

/-! ## 3. Constant-Offset Extraction (`diffConst?`) & `BoolCertCut` Checkers -/

/-- Extracts the exact integer constant difference `a - b` whenever all linear
variable terms cancel identically (`0` `noncomputable`, `0` `._unsafe_rec`,
`hasIR = true`). -/
@[expose] def LinExpr.diffConst? (a b : LinExpr) : Option Int :=
  match (LinExpr.sub a b).toPolyAt 64 with
  | none => none
  | some p =>
    match p.terms with
    | [] => some p.const
    | _ :: _ => none

/-- Extracts the canonical modular byte offset `(a - b) mod 2^w` whenever all
linear variable terms cancel identically (`0` `noncomputable`, `0`
`._unsafe_rec`, `hasIR = true`). -/
@[expose] def LinExpr.diffConstMod? (w : Nat) (a b : LinExpr) : Option Nat :=
  match LinExpr.diffConst? a b with
  | none => none
  | some c => some (intModPow2 c w)

/-- Soundness of `LinExpr.diffConst?`: if `a.diffConst? b = some c`, then
`a.evalBv env = b.evalBv env + bvOfInt w c` for every symbolic width `w`. -/
theorem linExpr_diffConst?_sound {w : Nat} (env : BvLinEnv w)
    {a b : LinExpr} {c : Int} (h : a.diffConst? b = some c) :
    a.evalBv env = b.evalBv env + bvOfInt w c := by
  unfold LinExpr.diffConst? at h
  cases hp : (LinExpr.sub a b).toPolyAt 64 with
  | none => rw [hp] at h; cases h
  | some p =>
    rw [hp] at h; dsimp only at h
    have hSub := linExpr_toPolyAt_evalBv env 64 (.sub a b) p hp
    change p.evalBv env = a.evalBv env - b.evalBv env at hSub
    unfold LinPoly.evalBv at hSub
    cases hTs : p.terms with
    | cons _ _ => rw [hTs] at h; cases h
    | nil =>
      rw [hTs] at h hSub
      injection h with hc
      rw [hc] at hSub
      change bvOfInt w c + bvZero w = a.evalBv env - b.evalBv env at hSub
      rw [bv_add_zero] at hSub
      exact bv_eq_add_of_sub_eq hSub.symm

/-- Soundness of `LinExpr.diffConstMod?`: if `a.diffConstMod? w b = some d`,
then `a.evalBv env = b.evalBv env + BitVec.ofNat w d`. -/
theorem linExpr_diffConstMod?_sound {w : Nat} (env : BvLinEnv w)
    {a b : LinExpr} {d : Nat} (h : a.diffConstMod? w b = some d) :
    a.evalBv env = b.evalBv env + BitVec.ofNat w d := by
  unfold LinExpr.diffConstMod? at h
  cases hDiff : a.diffConst? b with
  | none => rw [hDiff] at h; cases h
  | some c =>
    rw [hDiff] at h
    injection h with hd
    rw [← hd, ← bvOfInt_eq_ofNat_intModPow2 w c]
    exact linExpr_diffConst?_sound env hDiff

/-- Exact width-polymorphic equality checker: accepts `(a, b)` iff `a - b`
normalizes to constant `0` with no surviving variable terms. -/
@[expose] def bvLinCheckEqExact (cert : LinExpr × LinExpr) : Bool :=
  match cert.1.diffConst? cert.2 with
  | some c => intIsZero c
  | none => false

/-- Width-polymorphic equality soundness sealed behind `BoolCertCut`: works
for any symbolic width `w : Nat`. -/
theorem bvLin_eq_exact_of_boolCertCut {w : Nat} (env : BvLinEnv w)
    (a b : LinExpr) (hCert : BoolCertCut bvLinCheckEqExact (a, b)) :
    a.evalBv env = b.evalBv env := by
  have hRaw := BoolCertCut.unseal hCert
  unfold bvLinCheckEqExact at hRaw
  cases hDiff : a.diffConst? b with
  | none => rw [hDiff] at hRaw; cases hRaw
  | some c =>
    rw [hDiff] at hRaw
    have hc0 := int_eq_zero_of_isZero hRaw
    have hEq := linExpr_diffConst?_sound env hDiff
    rw [hc0, bvOfInt_zero, bv_add_zero] at hEq
    exact hEq

/-- Modular `BitVec w` equality checker: accepts `(w, a, b)` iff `a - b`
normalizes to a constant divisible by `2^w`. -/
@[expose] def bvLinCheckEqMod (cert : Nat × LinExpr × LinExpr) : Bool :=
  match cert.2.1.diffConstMod? cert.1 cert.2.2 with
  | some r => Nat.beq r 0
  | none => false

/-- Modular `BitVec w` equality soundness sealed behind `BoolCertCut`. -/
theorem bvLin_eq_mod_of_boolCertCut {w : Nat} (env : BvLinEnv w)
    (a b : LinExpr) (hCert : BoolCertCut bvLinCheckEqMod (w, a, b)) :
    a.evalBv env = b.evalBv env := by
  have hRaw := BoolCertCut.unseal hCert
  unfold bvLinCheckEqMod at hRaw
  cases hDiff : a.diffConstMod? w b with
  | none => rw [hDiff] at hRaw; cases hRaw
  | some r =>
    rw [hDiff] at hRaw
    have hr0 : r = 0 := Nat.eq_of_beq_eq_true hRaw
    have hEq := linExpr_diffConstMod?_sound env hDiff
    rw [hr0] at hEq
    exact hEq.trans (bv_add_zero (b.evalBv env))

/-- Constant pointer-offset checker: accepts `(w, a, b, delta)` iff
`a - b ≡ delta (mod 2^w)` with zero surviving variable terms. -/
@[expose] def bvLinCheckDiffConstMod (cert : Nat × LinExpr × LinExpr × Nat) : Bool :=
  match cert.2.1.diffConstMod? cert.1 cert.2.2.1 with
  | some r => Nat.beq r (Nat.mod cert.2.2.2 (bvPow2 cert.1))
  | none => false

/-- Constant pointer-offset soundness sealed behind `BoolCertCut`. -/
theorem bvLin_diffConst_mod_of_boolCertCut {w : Nat} (env : BvLinEnv w)
    (a b : LinExpr) (delta : Nat)
    (hCert : BoolCertCut bvLinCheckDiffConstMod (w, a, b, delta)) :
    a.evalBv env = b.evalBv env + BitVec.ofNat w delta := by
  have hRaw := BoolCertCut.unseal hCert
  unfold bvLinCheckDiffConstMod at hRaw
  cases hDiff : a.diffConstMod? w b with
  | none => rw [hDiff] at hRaw; cases hRaw
  | some r =>
    rw [hDiff] at hRaw
    have hr := Nat.eq_of_beq_eq_true hRaw
    have hEq := linExpr_diffConstMod?_sound env hDiff
    rw [hr, bvPow2_eq_two_pow, bv_ofNat_mod] at hEq
    exact hEq

/-- Modular `BitVec w` disequality checker: accepts `(w, a, b)` iff `a - b`
reduces to a nonzero constant modulo `2^w`. -/
@[expose] def bvLinCheckNeMod (cert : Nat × LinExpr × LinExpr) : Bool :=
  match cert.2.1.diffConst? cert.2.2 with
  | some c => !(Nat.beq (intModPow2 c cert.1) 0)
  | none => false

/-- Modular `BitVec w` disequality soundness sealed behind `BoolCertCut`. -/
theorem bvLin_ne_mod_of_boolCertCut {w : Nat} (env : BvLinEnv w)
    (a b : LinExpr) (hCert : BoolCertCut bvLinCheckNeMod (w, a, b)) :
    a.evalBv env ≠ b.evalBv env := by
  have hRaw := BoolCertCut.unseal hCert
  unfold bvLinCheckNeMod at hRaw
  cases hDiff : a.diffConst? b with
  | none => rw [hDiff] at hRaw; cases hRaw
  | some c =>
    rw [hDiff] at hRaw
    dsimp only at hRaw
    cases hz : Nat.beq (intModPow2 c w) 0 with
    | true => rw [hz] at hRaw; cases hRaw
    | false =>
      have hNe0 := bvOfInt_ne_zero_of_mod_ne_zero hz
      have hEq := linExpr_diffConst?_sound env hDiff
      intro hAB
      rw [hAB] at hEq
      have hZero : bvOfInt w c = bvZero w :=
        bv_eq_of_add_eq (hEq.symm.trans (bv_add_zero (b.evalBv env)).symm)
      exact hNe0 hZero

/-! ## 4. Kernel-Checked Canaries (`< 1 ms` `rfl`, `0` Axioms) -/

/-- Positive and negative `BvLin` canaries: symbolic-width pointer-stride
normalization, 64-bit modular wraparound, constant byte-offset extraction
(`diffConstMod?`), disequality refutation, and fail-closed rejection on
unmatched variables. -/
theorem bvLin_pointer_offset_canary :
    (∀ (w : Nat) (p : BitVec w) (n : Nat),
      (p + bvScale 4 (BitVec.ofNat w n) + BitVec.ofNat w 8) -
        (bvScale 2 (BitVec.ofNat w n) + BitVec.ofNat w 8) =
      p + bvScale 2 (BitVec.ofNat w n)) ∧
    (∀ (p : BitVec 64),
      p + BitVec.ofNat 64 (Nat.pow 2 64) = p) ∧
    (∀ (p : BitVec 64) (i : Nat),
      (p + bvScale 8 (BitVec.ofNat 64 i) + BitVec.ofNat 64 24) =
        (p + bvScale 8 (BitVec.ofNat 64 i) + BitVec.ofNat 64 8) +
          BitVec.ofNat 64 16) ∧
    (∀ (p : BitVec 64),
      p + BitVec.ofNat 64 8 ≠ p + BitVec.ofNat 64 16) ∧
    bvLinCheckEqMod (64, .bvVar 0, .bvVar 1) = false := by
  refine ⟨?_, ?_, ?_, ?_, rfl⟩
  · intro w p n
    let env : BvLinEnv w := ⟨fun _ => p, fun _ => n⟩
    let lhs : LinExpr :=
      .sub (.add (.add (.bvVar 0) (.scale 4 (.natVar 0))) (.constNat 8))
        (.add (.scale 2 (.natVar 0)) (.constNat 8))
    let rhs : LinExpr := .add (.bvVar 0) (.scale 2 (.natVar 0))
    exact bvLin_eq_exact_of_boolCertCut env lhs rhs
      (BoolCertCut.seal bvLinCheckEqExact (lhs, rhs) rfl)
  · intro p
    let env : BvLinEnv 64 := ⟨fun _ => p, fun _ => 0⟩
    have hPow : Nat.pow 2 64 = 18446744073709551616 := rfl
    rw [hPow]
    exact bvLin_eq_mod_of_boolCertCut env
      (.add (.bvVar 0) (.constNat 18446744073709551616)) (.bvVar 0)
      (BoolCertCut.seal bvLinCheckEqMod
        (64, .add (.bvVar 0) (.constNat 18446744073709551616), .bvVar 0) rfl)
  · intro p i
    let env : BvLinEnv 64 := ⟨fun _ => p, fun _ => i⟩
    let a : LinExpr :=
      .add (.add (.bvVar 0) (.scale 8 (.natVar 0))) (.constNat 24)
    let b : LinExpr :=
      .add (.add (.bvVar 0) (.scale 8 (.natVar 0))) (.constNat 8)
    exact bvLin_diffConst_mod_of_boolCertCut env a b 16
      (BoolCertCut.seal bvLinCheckDiffConstMod (64, a, b, 16) rfl)
  · intro p
    let env : BvLinEnv 64 := ⟨fun _ => p, fun _ => 0⟩
    let a : LinExpr := .add (.bvVar 0) (.constNat 8)
    let b : LinExpr := .add (.bvVar 0) (.constNat 16)
    exact bvLin_ne_mod_of_boolCertCut env a b
      (BoolCertCut.seal bvLinCheckNeMod (64, a, b) rfl)

end Anneal.PureLift.BvLin

end
