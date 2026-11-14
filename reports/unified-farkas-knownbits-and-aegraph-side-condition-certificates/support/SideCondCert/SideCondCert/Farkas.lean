-- Copyright 2026 The Fuchsia Authors
--
-- Licensed under a BSD-style license <LICENSE-BSD>, Apache License, Version 2.0
-- <LICENSE-APACHE or https://www.apache.org/licenses/LICENSE-2.0>, or the MIT
-- license <LICENSE-MIT or https://opensource.org/licenses/MIT>, at your option.
-- This file may not be copied, modified, or distributed except according to
-- those terms.

import SideCondCert.Domain

namespace SideCondCert

/-- Linear constraint `a * x + b * y + c ≤ 0` over two loop/index variables `(x, y : Int)`.
Models loop-header bounds guards (`i < n` as `1*i + (-1)*n + 1 ≤ 0`), subslice relationship
guards (`n ≤ len` as `1*n - 1*len + 0 ≤ 0`), and negated slice bounds check targets. -/
structure LinearLeZero where
  a : Int
  b : Int
  c : Int
  deriving DecidableEq, Repr

/-- Evaluate whether `(x, y)` satisfies `a * x + b * y + c ≤ 0`. -/
def LinearLeZero.holds (con : LinearLeZero) (x y : Int) : Prop :=
  con.a * x + con.b * y + con.c ≤ 0

/-- A 2-hypothesis Farkas certificate `(λ1, λ2, slack)` witnessing that any `(x, y)`
satisfying `h1 : c1.holds x y` and `h2 : c2.holds x y` cannot satisfy `negTarget.holds x y`
(i.e. `λ1 * c1 + λ2 * c2 + negTarget` reduces to a strictly positive constant `slack ≥ 1`,
contradicting `≤ 0`!).
This discharges `ConstraintElimination` and `IndVarSimplify` slice `panic_bounds_check`
eliminations in 6 integer multiplications without running `omega` search at check time. -/
structure FarkasCert2 where
  c1        : LinearLeZero
  c2        : LinearLeZero
  negTarget : LinearLeZero
  lam1      : Int
  lam2      : Int
  deriving DecidableEq, Repr

/-- Executable $O(1)$ boolean checker for `FarkasCert2`:
Verifies `0 ≤ lam1`, `0 ≤ lam2`, `lam1 * c1.a + lam2 * c2.a + negTarget.a = 0`,
`lam1 * c1.b + lam2 * c2.b + negTarget.b = 0`, and
`1 ≤ lam1 * c1.c + lam2 * c2.c + negTarget.c`. -/
def checkFarkasCert2 (cert : FarkasCert2) : Bool :=
  decide (0 ≤ cert.lam1 ∧
          0 ≤ cert.lam2 ∧
          cert.lam1 * cert.c1.a + cert.lam2 * cert.c2.a + cert.negTarget.a = 0 ∧
          cert.lam1 * cert.c1.b + cert.lam2 * cert.c2.b + cert.negTarget.b = 0 ∧
          1 ≤ cert.lam1 * cert.c1.c + cert.lam2 * cert.c2.c + cert.negTarget.c)

/-- Declarative validity specification for `FarkasCert2`. -/
structure ValidFarkasCert2 (cert : FarkasCert2) : Prop where
  lam1_nonneg : 0 ≤ cert.lam1
  lam2_nonneg : 0 ≤ cert.lam2
  cancel_a    : cert.lam1 * cert.c1.a + cert.lam2 * cert.c2.a + cert.negTarget.a = 0
  cancel_b    : cert.lam1 * cert.c1.b + cert.lam2 * cert.c2.b + cert.negTarget.b = 0
  pos_const   : 1 ≤ cert.lam1 * cert.c1.c + cert.lam2 * cert.c2.c + cert.negTarget.c

/-- Soundness of `checkFarkasCert2`: if `checkFarkasCert2 cert = true` and `(x, y)`
satisfies both loop/slice guards `cert.c1.holds x y` and `cert.c2.holds x y`, then
`cert.negTarget.holds x y` is false (`¬ cert.negTarget.holds x y`), proving the slice
index is strictly in bounds! -/
theorem checkFarkasCert2_sound (cert : FarkasCert2)
    (h_check : checkFarkasCert2 cert = true)
    (x y : Int)
    (h1 : cert.c1.holds x y)
    (h2 : cert.c2.holds x y) :
    ¬ cert.negTarget.holds x y := by
  simp only [checkFarkasCert2, decide_eq_true_eq] at h_check
  rcases h_check with ⟨h_l1, h_l2, h_a, h_b, h_c⟩
  intro h_neg
  unfold LinearLeZero.holds at h1 h2 h_neg
  have h_mul1 : cert.lam1 * (cert.c1.a * x + cert.c1.b * y + cert.c1.c) ≤ 0 :=
    Int.mul_nonpos_of_nonneg_of_nonpos h_l1 h1
  have h_mul2 : cert.lam2 * (cert.c2.a * x + cert.c2.b * y + cert.c2.c) ≤ 0 :=
    Int.mul_nonpos_of_nonneg_of_nonpos h_l2 h2
  have h_id :
      cert.lam1 * (cert.c1.a * x + cert.c1.b * y + cert.c1.c) +
      cert.lam2 * (cert.c2.a * x + cert.c2.b * y + cert.c2.c) +
      (cert.negTarget.a * x + cert.negTarget.b * y + cert.negTarget.c) =
      (cert.lam1 * cert.c1.a + cert.lam2 * cert.c2.a + cert.negTarget.a) * x +
      (cert.lam1 * cert.c1.b + cert.lam2 * cert.c2.b + cert.negTarget.b) * y +
      (cert.lam1 * cert.c1.c + cert.lam2 * cert.c2.c + cert.negTarget.c) := by
    simp only [Int.mul_add, Int.add_mul, ← Int.mul_assoc]
    omega
  rw [h_a, h_b] at h_id
  simp only [Int.zero_mul, Int.zero_add] at h_id
  omega

/-- Bidirectional equivalence between `checkFarkasCert2` and `ValidFarkasCert2`. -/
theorem checkFarkasCert2_iff_valid (cert : FarkasCert2) :
    checkFarkasCert2 cert = true ↔ ValidFarkasCert2 cert := by
  constructor
  · intro h
    simp only [checkFarkasCert2, decide_eq_true_eq] at h
    rcases h with ⟨l1, l2, ca, cb, pc⟩
    exact ⟨l1, l2, ca, cb, pc⟩
  · intro ⟨l1, l2, ca, cb, pc⟩
    simp [checkFarkasCert2, l1, l2, ca, cb, pc]

end SideCondCert
