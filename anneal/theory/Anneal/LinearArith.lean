-- Copyright 2026 The Fuchsia Authors
--
-- Licensed under a BSD-style license <LICENSE-BSD>, Apache License, Version 2.0
-- <LICENSE-APACHE or https://www.apache.org/licenses/LICENSE-2.0>, or the MIT
-- license <LICENSE-MIT or https://opensource.org/licenses/MIT>, at your option.
-- This file may not be copied, modified, or distributed except according to
-- those terms.

prelude
import Init.Core
import Init.NotationExtra
import Init.SimpLemmas
import Init.Data.Nat.Basic
import Init.Data.Nat.Div.Basic
import Init.Data.Nat.Bitwise.Basic
import Init.Data.Int.Basic
import Init.Data.List.Basic

/-!
# Sparse Linear Arithmetic & Chvatal-Gomory Cut Certifier (`Anneal.LinearArith`)

Pass-1-portable (`prelude` + `Init.*` only, zero `._unsafe_rec`, zero `omega`)
reflective linear-inequality certificate checker serving as an `omega`
substitute when a `CutStep` certificate is supplied in `anneal/theory/` and
`anneal/correspondence/` (callers construct surface goals and `CutStep` traces;
this module verifies them rather than searching for certificates).

- **Surface ASTs:** `IntLinExpr` (`IntCutIneq`, `IntCutGoal`) and `NatLinExpr`
  (`NatCutIneq`, `NatCutGoal`) encode integer and natural-number linear
  expressions over variable environments (`List Int` / `List Nat`), which
  `ineqToSparse` normalizes into `SparseIneq` rows (`evalTerms` bounded by
  `rhs`).
- **Proof steps (`CutStep`):** Certificates replay hypothesis loads
  (`CutStep.hyp idx`), nonnegative Farkas combinations
  (`CutStep.comb s1 k1 s2 k2`), and exact integer Chvatal-Gomory floor cuts
  (`CutStep.divCut g s`, dividing a row whose coefficients are divisible by
  `g > 0` and rounding `rhs` via `SInt.fdiv`). Floor cuts discharge integer
  parity and alignment obligations (such as `2 * i ≤ 2 * n + 1` together with
  `2 * n + 1 ≤ 2 * i`, which is satisfiable over rationals at `i = n + 1/2`)
  that rational Farkas combinations alone cannot refute.
- **Reflection:** `checkIntCutGoal_sound` reduces `IntCutGoal` checking to
  refuting `hyps ++ [negConcl]`, while `checkNatCutGoal_sound` reduces
  `NatCutGoal` checking to refuting `hyps ++ nonneg(vars) ++ [negConcl]`
  (preserving user hypothesis indices `0 .. hyps.length - 1`, followed by
  `0 ≤ var v` for each deduplicated variable in first-occurrence order, then
  `negConcl`). Every row coefficient and RHS is bounded by `magCap128`,
  derived rows accumulate in reverse insertion order (`DerivedRows`) with
  `O(1)` push and last-row lookup, and accepted traces discharge client goals
  by `rfl` or `decide` using only `[propext]`.
-/

namespace Anneal.LinearArith

/-! ## 1. Constructive `Int` <-> Sign-Magnitude `Nat` Bridge (`IntBalance`) -/

def intPos : Int → Nat
  | .ofNat n => n
  | .negSucc _ => 0

def intNeg : Int → Nat
  | .ofNat _ => 0
  | .negSucc m => m + 1

/-- Relational representation relating `x : Int` to a `(p, n) : Nat × Nat`
pair via `intPos x + n = intNeg x + p`. -/
def IntBalance (x : Int) (p n : Nat) : Prop :=
  intPos x + n = intNeg x + p

theorem add_four_rearrange (a b c d : Nat) :
    (a + b) + (c + d) = (a + c) + (b + d) := by
  rw [Nat.add_assoc a b (c + d), ← Nat.add_assoc b c d, Nat.add_comm b c,
      Nat.add_assoc c b d, ← Nat.add_assoc a c (b + d)]

theorem add_three_mid (a b c : Nat) : a + b + c = a + c + b := by
  rw [Nat.add_assoc, Nat.add_comm b c, ← Nat.add_assoc]

theorem intBalance_of_add_eq {x : Int} {p1 n1 p2 n2 : Nat}
    (h1 : IntBalance x p1 n1) (hEq : p1 + n2 = p2 + n1) :
    IntBalance x p2 n2 := by
  unfold IntBalance at h1
  unfold IntBalance
  have hSum : (intPos x + n2) + (p1 + n1) = (intNeg x + p2) + (p1 + n1) := by
    have hL : (intPos x + n2) + (p1 + n1) = (intPos x + n1) + (p1 + n2) := by
      rw [add_four_rearrange (intPos x) n2 p1 n1, Nat.add_comm n2 n1,
          ← add_four_rearrange (intPos x) p1 n1 n2]
    have hR : (intNeg x + p2) + (p1 + n1) = (intNeg x + p1) + (p2 + n1) :=
      add_four_rearrange (intNeg x) p2 p1 n1
    rw [hL, hR, h1, hEq]
  exact Nat.add_right_cancel hSum

/-- Two integers sharing a common `(p, n)` `IntBalance` pair are equal. -/
theorem intBalance_eq_of_eq {x y : Int} {p n : Nat}
    (hx : IntBalance x p n) (hy : IntBalance y p n) : x = y := by
  unfold IntBalance at hx hy
  cases x with
  | ofNat px =>
    cases y with
    | ofNat py =>
      dsimp [intPos, intNeg] at hx hy
      rw [Nat.zero_add] at hx hy
      have hEq : px + n = py + n := by rw [hx, hy]
      rw [Nat.add_right_cancel hEq]
    | negSucc ny =>
      dsimp [intPos, intNeg] at hx hy
      rw [Nat.zero_add] at hx hy
      have hBad : px + (ny + 1) + p = 0 + p := by
        rw [Nat.add_assoc, ← hy, hx, Nat.zero_add]
      have hZero : px + (ny + 1) = 0 := Nat.add_right_cancel hBad
      nomatch hZero
  | negSucc nx =>
    cases y with
    | ofNat py =>
      dsimp [intPos, intNeg] at hx hy
      rw [Nat.zero_add] at hx hy
      have hBad : py + (nx + 1) + p = 0 + p := by
        rw [Nat.add_assoc, ← hx, hy, Nat.zero_add]
      have hZero : py + (nx + 1) = 0 := Nat.add_right_cancel hBad
      nomatch hZero
    | negSucc ny =>
      dsimp [intPos, intNeg] at hx hy
      rw [Nat.zero_add] at hx hy
      have hEq : nx + 1 + p = ny + 1 + p := by rw [← hx, ← hy]
      have hSucc : nx + 1 = ny + 1 := Nat.add_right_cancel hEq
      have hN : nx = ny := Nat.succ.inj hSucc
      rw [hN]

theorem intBalance_self (x : Int) : IntBalance x (intPos x) (intNeg x) := by
  unfold IntBalance
  exact Nat.add_comm (intPos x) (intNeg x)

theorem intBalance_ofNat (n : Nat) : IntBalance (Int.ofNat n) n 0 := by
  dsimp [IntBalance, intPos, intNeg]; simp only [Nat.zero_add]

theorem intBalance_negOfNat : ∀ n : Nat, IntBalance (Int.negOfNat n) 0 n
  | 0 => rfl
  | _ + 1 => by
    dsimp [IntBalance, Int.negOfNat, intPos, intNeg]
    simp only [Nat.zero_add]

theorem intBalance_subNatNat (p n : Nat) :
    IntBalance (Int.subNatNat p n) p n := by
  unfold Int.subNatNat
  cases hSub : n - p with
  | zero =>
    have hLe : n ≤ p := Nat.le_of_sub_eq_zero hSub
    dsimp [IntBalance, intPos, intNeg]
    rw [Nat.zero_add, Nat.sub_add_cancel hLe]
  | succ k =>
    have hLt : p < n := Nat.lt_of_sub_eq_succ hSub
    have hAdd : p + (k + 1) = n := by
      rw [← hSub]
      exact Nat.add_sub_of_le (Nat.le_of_lt hLt)
    dsimp [IntBalance, intPos, intNeg]
    rw [Nat.zero_add, Nat.add_comm (k + 1) p]
    exact hAdd.symm

theorem intBalance_neg {x : Int} {p n : Nat} (h : IntBalance x p n) :
    IntBalance (Int.neg x) n p := by
  cases x with
  | ofNat mx =>
    dsimp [IntBalance, intPos, intNeg] at h
    rw [Nat.zero_add] at h
    have hb := intBalance_negOfNat mx
    exact intBalance_of_add_eq hb (by rw [Nat.zero_add, Nat.add_comm, h])
  | negSucc nx =>
    dsimp [IntBalance, intPos, intNeg] at h
    rw [Nat.zero_add] at h
    have hb := intBalance_ofNat (nx + 1)
    exact intBalance_of_add_eq hb (by rw [← h, Nat.add_zero])

theorem intBalance_add {x y : Int} {px nx py ny : Nat}
    (hx : IntBalance x px nx) (hy : IntBalance y py ny) :
    IntBalance (Int.add x y) (px + py) (nx + ny) := by
  cases x with
  | ofNat mx =>
    cases y with
    | ofNat my =>
      dsimp [IntBalance, intPos, intNeg] at hx hy
      rw [Nat.zero_add] at hx hy
      have hb := intBalance_ofNat (mx + my)
      exact intBalance_of_add_eq hb
        (by rw [Nat.add_zero, ← hx, ← hy, add_four_rearrange])
    | negSucc ny' =>
      dsimp [IntBalance, intPos, intNeg] at hx hy
      rw [Nat.zero_add] at hx hy
      have hb := intBalance_subNatNat mx (ny' + 1)
      exact intBalance_of_add_eq hb
        (by rw [← hx, hy, ← Nat.add_assoc mx nx ((ny' + 1) + py),
                Nat.add_comm (ny' + 1) py,
                ← Nat.add_assoc (mx + nx) py (ny' + 1)])
  | negSucc nx' =>
    cases y with
    | ofNat my =>
      dsimp [IntBalance, intPos, intNeg] at hx hy
      rw [Nat.zero_add] at hx hy
      have hb := intBalance_subNatNat my (nx' + 1)
      exact intBalance_of_add_eq hb
        (by rw [hx, ← hy, Nat.add_assoc (nx' + 1) px ny,
                Nat.add_comm (nx' + 1) (px + ny),
                ← Nat.add_assoc my (px + ny) (nx' + 1),
                ← Nat.add_assoc my px ny,
                Nat.add_comm my px, Nat.add_assoc px my ny])
    | negSucc ny' =>
      dsimp [IntBalance, intPos, intNeg] at hx hy
      rw [Nat.zero_add] at hx hy
      have hRHS :
          Int.add (Int.negSucc nx') (Int.negSucc ny') =
            Int.negSucc (Nat.succ (nx' + ny')) := rfl
      rw [hRHS]
      have hSum : Nat.succ (nx' + ny') + 1 = (nx' + 1) + (ny' + 1) := by
        rw [Nat.succ_eq_add_one, Nat.add_assoc nx' ny' 1,
            Nat.add_assoc nx' (ny' + 1) 1, Nat.add_comm (ny' + 1) 1,
            ← Nat.add_assoc nx' 1 (ny' + 1)]
      have hb :
          IntBalance (Int.negSucc (Nat.succ (nx' + ny'))) 0
            ((nx' + 1) + (ny' + 1)) := by
        dsimp [IntBalance, intPos, intNeg]
        rw [Nat.zero_add, Nat.add_zero, hSum]
      exact intBalance_of_add_eq hb
        (by rw [Nat.zero_add, hx, hy, add_four_rearrange,
                Nat.add_comm ((nx' + 1) + (ny' + 1)) (px + py)])

theorem intBalance_sub {x y : Int} {px nx py ny : Nat}
    (hx : IntBalance x px nx) (hy : IntBalance y py ny) :
    IntBalance (Int.sub x y) (px + ny) (nx + py) :=
  intBalance_add hx (intBalance_neg hy)

theorem intBalance_mul_nat {x : Int} {p n : Nat} (k : Nat)
    (h : IntBalance x p n) :
    IntBalance (Int.mul (Int.ofNat k) x) (k * p) (k * n) := by
  cases x with
  | ofNat mx =>
    dsimp [IntBalance, intPos, intNeg] at h
    rw [Nat.zero_add] at h
    have hb := intBalance_ofNat (k * mx)
    exact intBalance_of_add_eq hb (by rw [Nat.add_zero, ← Nat.mul_add, h])
  | negSucc nx =>
    dsimp [IntBalance, intPos, intNeg] at h
    rw [Nat.zero_add] at h
    have hb := intBalance_negOfNat (k * (nx + 1))
    exact intBalance_of_add_eq hb
      (by rw [Nat.zero_add, h, Nat.mul_add, Nat.add_comm (k * (nx + 1)) (k * p)])

theorem int_mul_negSucc_left (a : Nat) (y : Int) :
    Int.mul (Int.negSucc a) y = Int.neg (Int.mul (Int.ofNat (a + 1)) y) := by
  cases y with
  | ofNat _ => rfl
  | negSucc b =>
    exact (intBalance_eq_of_eq
      (intBalance_neg (intBalance_negOfNat ((a + 1) * (b + 1))))
      (intBalance_ofNat ((a + 1) * (b + 1)))).symm

theorem int_mul_negSucc_right (a b : Nat) :
    Int.mul (Int.ofNat a) (Int.negSucc b) =
      Int.neg (Int.mul (Int.ofNat a) (Int.ofNat (b + 1))) :=
  rfl

theorem nat_mul_balance_cancel (a nx px b ny py : Nat)
    (hx : a + nx = px) (hy : b + ny = py) :
    a * b + (px * ny + nx * py) = px * py + nx * ny := by
  rw [← hx, ← hy]
  rw [Nat.add_mul a nx ny, Nat.add_mul a nx (b + ny),
      Nat.mul_add a b ny, Nat.mul_add nx b ny]
  rw [Nat.add_comm (a * ny) (nx * ny),
      Nat.add_assoc (nx * ny) (a * ny) (nx * b + nx * ny)]
  rw [Nat.add_comm (nx * ny) (a * ny + (nx * b + nx * ny)),
      ← Nat.add_assoc (a * b)]
  rw [Nat.add_assoc (a * b) (a * ny) (nx * b + nx * ny)]

theorem intBalance_mul_nat_var (a : Nat) {px nx : Nat}
    (hx : IntBalance (Int.ofNat a) px nx)
    {y : Int} {py ny : Nat} (hy : IntBalance y py ny) :
    IntBalance (Int.mul (Int.ofNat a) y)
      (px * py + nx * ny) (px * ny + nx * py) := by
  dsimp [IntBalance, intPos, intNeg] at hx
  rw [Nat.zero_add] at hx
  cases y with
  | ofNat b =>
    dsimp [IntBalance, intPos, intNeg] at hy
    rw [Nat.zero_add] at hy
    have hEq := nat_mul_balance_cancel a nx px b ny py hx hy
    have hb := intBalance_ofNat (a * b)
    exact intBalance_of_add_eq hb (by rw [Nat.add_zero]; exact hEq)
  | negSucc b' =>
    dsimp [IntBalance, intPos, intNeg] at hy
    rw [Nat.zero_add] at hy
    have hEq := nat_mul_balance_cancel a nx px (b' + 1) py ny hx hy.symm
    rw [int_mul_negSucc_right]
    have hb := intBalance_neg (intBalance_ofNat (a * (b' + 1)))
    exact intBalance_of_add_eq hb
      (by rw [Nat.zero_add,
              Nat.add_comm (px * py + nx * ny) (a * (b' + 1))]
          exact hEq.symm)

theorem intBalance_mul {x y : Int} {px nx py ny : Nat}
    (hx : IntBalance x px nx) (hy : IntBalance y py ny) :
    IntBalance (Int.mul x y) (px * py + nx * ny) (px * ny + nx * py) := by
  cases x with
  | ofNat a => exact intBalance_mul_nat_var a hx hy
  | negSucc a' =>
    rw [int_mul_negSucc_left]
    have hxNeg : IntBalance (Int.ofNat (a' + 1)) nx px := intBalance_neg hx
    have hPos := intBalance_mul_nat_var (a' + 1) hxNeg hy
    have hRes := intBalance_neg hPos
    exact intBalance_of_add_eq hRes
      (by rw [Nat.add_comm (nx * py) (px * ny),
              Nat.add_comm (nx * ny) (px * py)])

/-- Translates `x ≤ y` into `px + ny ≤ py + nx` under `IntBalance`
witnesses. -/
theorem intBalance_le {x y : Int} {px nx py ny : Nat}
    (hx : IntBalance x px nx) (hy : IntBalance y py ny) :
    (x ≤ y) ↔ (px + ny ≤ py + nx) := by
  have hDiff : IntBalance (Int.sub y x) (py + nx) (ny + px) :=
    intBalance_sub hy hx
  unfold IntBalance at hDiff
  constructor
  · intro hLe
    cases hSub : Int.sub y x with
    | ofNat m =>
      rw [hSub] at hDiff
      dsimp [intPos, intNeg] at hDiff
      rw [Nat.zero_add, Nat.add_comm ny px] at hDiff
      have hLe' : px + ny ≤ m + (px + ny) := Nat.le_add_left (px + ny) m
      rw [hDiff] at hLe'
      exact hLe'
    | negSucc _ =>
      change Int.NonNeg (Int.sub y x) at hLe
      rw [hSub] at hLe
      nomatch hLe
  · intro hNat
    change Int.NonNeg (Int.sub y x)
    cases hSub : Int.sub y x with
    | ofNat m => exact Int.NonNeg.mk m
    | negSucc k =>
      rw [hSub] at hDiff
      dsimp [intPos, intNeg] at hDiff
      rw [Nat.zero_add] at hDiff
      have hBound : py + nx + (k + 1) ≤ py + nx := by
        rw [Nat.add_comm (k + 1) (py + nx)] at hDiff
        rw [← hDiff, Nat.add_comm ny px]
        exact hNat
      have hBad : k + 1 ≤ 0 := Nat.le_of_add_le_add_left hBound
      nomatch hBad

/-- Constructive contradiction principle on `Int`: `¬ (b + 1 ≤ a)`
implies `a ≤ b`. -/
theorem int_le_of_not_succ_le (a b : Int)
    (h : Int.add b (Int.ofNat 1) ≤ a → False) : a ≤ b := by
  have ha := intBalance_self a
  have hb := intBalance_self b
  have hb1 := intBalance_add hb (intBalance_ofNat 1)
  cases Nat.lt_or_ge (intPos b + intNeg a + 1) (intPos a + intNeg b + 1) with
  | inl hLt =>
    have hLeNat : intPos b + intNeg a + 1 ≤ intPos a + intNeg b :=
      Nat.le_of_lt_succ hLt
    have hLeInt : Int.add b (Int.ofNat 1) ≤ a := by
      have hIff := intBalance_le hb1 ha
      apply hIff.2
      rw [Nat.add_zero, add_three_mid (intPos b) 1 (intNeg a)]
      exact hLeNat
    exact False.elim (h hLeInt)
  | inr hGe =>
    have hLeNat : intPos a + intNeg b ≤ intPos b + intNeg a :=
      Nat.le_of_succ_le_succ hGe
    exact (intBalance_le ha hb).2 hLeNat

/-! ## 2. Sign-Magnitude `Nat` Carrier (`SInt`) with `magCap128` Guard -/

/-- Magnitude cap (`2^128`) bounding intermediate certificate scalars
and RHS values in `stepCut`. -/
def magCap128 : Nat := Nat.shiftLeft 1 128

/-- Kernel-reducible sign-magnitude integer used for `IntLinExpr`
constants and `SparseIneq` rows. -/
structure SInt where
  neg : Bool
  mag : Nat

def SInt.zero : SInt := ⟨false, 0⟩
def SInt.one : SInt := ⟨false, 1⟩
def SInt.negOne : SInt := ⟨true, 1⟩

/-- Interprets a sign-magnitude `SInt` as an `Int`. -/
def SInt.toInt (s : SInt) : Int :=
  match s.neg with
  | false => Int.ofNat s.mag
  | true => Int.negOfNat s.mag

def SInt.posPart (s : SInt) : Nat :=
  match s.neg with
  | false => s.mag
  | true => 0

def SInt.negPart (s : SInt) : Nat :=
  match s.neg with
  | false => 0
  | true => s.mag

theorem sint_intBalance (s : SInt) :
    IntBalance s.toInt s.posPart s.negPart := by
  cases hNeg : s.neg with
  | false =>
    dsimp [SInt.toInt, SInt.posPart, SInt.negPart]
    rw [hNeg]
    exact intBalance_ofNat s.mag
  | true =>
    dsimp [SInt.toInt, SInt.posPart, SInt.negPart]
    rw [hNeg]
    exact intBalance_negOfNat s.mag

/-- Normalizes a difference `p - n` of `Nat`s into a sign-magnitude
`SInt`. -/
def SInt.ofPN (p n : Nat) : SInt :=
  match Nat.ble n p with
  | true => ⟨false, p - n⟩
  | false => ⟨true, n - p⟩

theorem sint_ofPN_balance (p n : Nat) :
    IntBalance (SInt.ofPN p n).toInt p n := by
  dsimp [SInt.ofPN]
  cases hBle : Nat.ble n p with
  | true =>
    have hLe : n ≤ p := Nat.le_of_ble_eq_true hBle
    exact intBalance_of_add_eq (sint_intBalance ⟨false, p - n⟩)
      (by dsimp [SInt.posPart, SInt.negPart]; rw [Nat.sub_add_cancel hLe])
  | false =>
    have hNot : ¬ (n ≤ p) := fun h => by
      have ht := Nat.ble_eq_true_of_le h
      rw [ht] at hBle
      nomatch hBle
    have hLe : p ≤ n := Nat.le_of_lt (Nat.lt_of_not_le hNot)
    exact intBalance_of_add_eq (sint_intBalance ⟨true, n - p⟩)
      (by dsimp [SInt.posPart, SInt.negPart]
          rw [Nat.zero_add, Nat.add_comm p (n - p), Nat.sub_add_cancel hLe])

/-- Arithmetic negation on `SInt`, normalizing `-0` to `SInt.zero`. -/
def SInt.negate (s : SInt) : SInt :=
  match Nat.beq s.mag 0 with
  | true => SInt.zero
  | false => ⟨!s.neg, s.mag⟩

theorem sint_negate_balance (s : SInt) :
    IntBalance (SInt.negate s).toInt s.negPart s.posPart := by
  dsimp [SInt.negate]
  cases hZero : Nat.beq s.mag 0 with
  | true =>
    have hEq : s.mag = 0 := Nat.eq_of_beq_eq_true hZero
    cases hN : s.neg with
    | false =>
      dsimp [SInt.zero, SInt.toInt, SInt.posPart, SInt.negPart]
      rw [hN, hEq]; rfl
    | true =>
      dsimp [SInt.zero, SInt.toInt, SInt.posPart, SInt.negPart]
      rw [hN, hEq]; rfl
  | false =>
    cases hN : s.neg with
    | false =>
      dsimp [SInt.toInt, SInt.posPart, SInt.negPart]
      rw [hN]
      exact intBalance_negOfNat s.mag
    | true =>
      dsimp [SInt.toInt, SInt.posPart, SInt.negPart]
      rw [hN]
      exact intBalance_ofNat s.mag

/-- Addition on `SInt` via `SInt.ofPN` cancellation. -/
def SInt.add (a b : SInt) : SInt :=
  SInt.ofPN (a.posPart + b.posPart) (a.negPart + b.negPart)

theorem sint_add_balance (a b : SInt) :
    IntBalance (SInt.add a b).toInt
      (a.posPart + b.posPart) (a.negPart + b.negPart) :=
  sint_ofPN_balance (a.posPart + b.posPart) (a.negPart + b.negPart)

theorem sint_add_toInt (a b : SInt) :
    (SInt.add a b).toInt = Int.add a.toInt b.toInt :=
  intBalance_eq_of_eq (sint_add_balance a b)
    (intBalance_add (sint_intBalance a) (sint_intBalance b))

/-- Subtraction `a - b` on `SInt`. -/
def SInt.sub (a b : SInt) : SInt :=
  SInt.add a (SInt.negate b)

/-- Multiplies `s : SInt` by a nonnegative scalar `k : Nat`. -/
def SInt.scaleNat (k : Nat) (s : SInt) : SInt :=
  match Nat.beq k 0 with
  | true => SInt.zero
  | false =>
    match Nat.beq s.mag 0 with
    | true => SInt.zero
    | false => ⟨s.neg, k * s.mag⟩

theorem sint_scaleNat_toInt (k : Nat) (s : SInt) :
    (SInt.scaleNat k s).toInt = Int.mul (Int.ofNat k) s.toInt := by
  dsimp [SInt.scaleNat]
  cases hk : Nat.beq k 0 with
  | true =>
    have hK0 : k = 0 := Nat.eq_of_beq_eq_true hk
    rw [hK0]
    dsimp only [SInt.zero, SInt.toInt]
    exact intBalance_eq_of_eq (intBalance_ofNat 0)
      (intBalance_of_add_eq (intBalance_mul_nat 0 (sint_intBalance s))
        (by rw [Nat.zero_mul, Nat.zero_mul]))
  | false =>
    cases hm : Nat.beq s.mag 0 with
    | true =>
      have hM0 : s.mag = 0 := Nat.eq_of_beq_eq_true hm
      cases hN : s.neg with
      | false =>
        dsimp [SInt.toInt]; rw [hN, hM0]
        exact (intBalance_eq_of_eq (intBalance_mul_nat k (intBalance_ofNat 0))
          (intBalance_of_add_eq (intBalance_ofNat 0)
            (by rw [Nat.mul_zero]))).symm
      | true =>
        dsimp [SInt.toInt]; rw [hN, hM0]
        exact (intBalance_eq_of_eq
          (intBalance_mul_nat k (intBalance_negOfNat 0))
          (intBalance_of_add_eq (intBalance_ofNat 0)
            (by rw [Nat.mul_zero]))).symm
    | false =>
      cases hN : s.neg with
      | false =>
        dsimp [SInt.toInt]; rw [hN]
        exact intBalance_eq_of_eq (intBalance_ofNat (k * s.mag))
          (intBalance_mul_nat k (intBalance_ofNat s.mag))
      | true =>
        dsimp [SInt.toInt]; rw [hN]
        exact intBalance_eq_of_eq (intBalance_negOfNat (k * s.mag))
          (intBalance_mul_nat k (intBalance_negOfNat s.mag))

def boolXor (a b : Bool) : Bool :=
  match a, b with
  | false, false => false
  | true, true => false
  | _, _ => true

/-- Multiplication on `SInt`. -/
def SInt.mul (a b : SInt) : SInt :=
  match Nat.beq a.mag 0 || Nat.beq b.mag 0 with
  | true => SInt.zero
  | false => ⟨boolXor a.neg b.neg, a.mag * b.mag⟩

theorem sint_mul_toInt (a b : SInt) :
    (SInt.mul a b).toInt = Int.mul a.toInt b.toInt := by
  have ha := sint_intBalance a
  have hb := sint_intBalance b
  dsimp [SInt.mul]
  cases ha0 : Nat.beq a.mag 0 with
  | true =>
    have hMa : a.mag = 0 := Nat.eq_of_beq_eq_true ha0
    have haZero : IntBalance a.toInt 0 0 := by
      cases hNa : a.neg with
      | false => dsimp [SInt.toInt]; rw [hNa, hMa]; exact intBalance_ofNat 0
      | true => dsimp [SInt.toInt]; rw [hNa, hMa]; exact intBalance_negOfNat 0
    have hProd := intBalance_mul haZero hb
    rw [Nat.zero_mul, Nat.zero_mul, Nat.add_zero] at hProd
    exact intBalance_eq_of_eq (intBalance_ofNat 0) hProd
  | false =>
    cases hb0 : Nat.beq b.mag 0 with
    | true =>
      have hMb : b.mag = 0 := Nat.eq_of_beq_eq_true hb0
      have hbZero : IntBalance b.toInt 0 0 := by
        cases hNb : b.neg with
        | false => dsimp [SInt.toInt]; rw [hNb, hMb]; exact intBalance_ofNat 0
        | true => dsimp [SInt.toInt]; rw [hNb, hMb]; exact intBalance_negOfNat 0
      have hProd := intBalance_mul ha hbZero
      rw [Nat.mul_zero, Nat.mul_zero, Nat.add_zero] at hProd
      exact intBalance_eq_of_eq (intBalance_ofNat 0) hProd
    | false =>
      dsimp [Bool.or]
      cases hNa : a.neg with
      | false =>
        cases hNb : b.neg with
        | false =>
          dsimp [boolXor, SInt.toInt]; rw [hNa, hNb]
          have hProd :=
            intBalance_mul (intBalance_ofNat a.mag) (intBalance_ofNat b.mag)
          simp only [Nat.mul_zero, Nat.zero_mul, Nat.add_zero] at hProd
          exact intBalance_eq_of_eq (intBalance_ofNat (a.mag * b.mag)) hProd
        | true =>
          dsimp [boolXor, SInt.toInt]; rw [hNa, hNb]
          have hProd :=
            intBalance_mul (intBalance_ofNat a.mag) (intBalance_negOfNat b.mag)
          simp only [Nat.mul_zero, Nat.zero_mul, Nat.add_zero] at hProd
          exact intBalance_eq_of_eq (intBalance_negOfNat (a.mag * b.mag)) hProd
      | true =>
        cases hNb : b.neg with
        | false =>
          dsimp [boolXor, SInt.toInt]; rw [hNa, hNb]
          have hProd :=
            intBalance_mul (intBalance_negOfNat a.mag) (intBalance_ofNat b.mag)
          simp only [Nat.mul_zero, Nat.zero_mul, Nat.add_zero,
                     Nat.zero_add] at hProd
          exact intBalance_eq_of_eq (intBalance_negOfNat (a.mag * b.mag)) hProd
        | true =>
          dsimp [boolXor, SInt.toInt]; rw [hNa, hNb]
          have hProd :=
            intBalance_mul (intBalance_negOfNat a.mag)
              (intBalance_negOfNat b.mag)
          simp only [Nat.mul_zero, Nat.zero_mul, Nat.add_zero,
                     Nat.zero_add] at hProd
          exact intBalance_eq_of_eq (intBalance_ofNat (a.mag * b.mag)) hProd

def SInt.isZero (s : SInt) : Bool := Nat.beq s.mag 0

def SInt.isStrictlyNeg (s : SInt) : Bool :=
  s.neg && Nat.ble 1 s.mag

def SInt.withinCap (s : SInt) : Bool := Nat.ble s.mag magCap128

/-- Divides `s.mag` by `g` while preserving `s.neg` (sound when `g`
divides `s.mag` and `0 < g`). -/
def SInt.divExact (g : Nat) (s : SInt) : SInt :=
  ⟨s.neg, Nat.div s.mag g⟩

/-- Integer floor division on `SInt` for `0 < g`, rounding negative
values toward negative infinity. -/
def SInt.fdiv (s : SInt) (g : Nat) : SInt :=
  match s.neg with
  | false => ⟨false, Nat.div s.mag g⟩
  | true =>
    match s.mag with
    | 0 => SInt.zero
    | m + 1 => ⟨true, Nat.div m g + 1⟩

theorem sint_divExact_scale (g : Nat) (s : SInt)
    (hg : 0 < g) (hd : Nat.mod s.mag g = 0) :
    SInt.scaleNat g (SInt.divExact g s) = ⟨s.neg, s.mag⟩ ∨
    (s.mag = 0 ∧ SInt.scaleNat g (SInt.divExact g s) = SInt.zero) := by
  have hMulDiv : g * Nat.div s.mag g = s.mag := by
    have h := Nat.div_add_mod s.mag g
    dsimp only [HDiv.hDiv, Div.div, HMod.hMod, Mod.mod] at h
    rw [hd, Nat.add_zero] at h
    exact h
  cases hm : Nat.beq s.mag 0 with
  | true =>
    have hm0 : s.mag = 0 := Nat.eq_of_beq_eq_true hm
    right
    refine ⟨hm0, ?_⟩
    cases hg0 : Nat.beq g 0 with
    | true =>
      have hgZero : g = 0 := Nat.eq_of_beq_eq_true hg0
      rw [hgZero] at hg
      nomatch hg
    | false =>
      have hZeroDiv : Nat.div 0 g = 0 := by
        have h := Nat.zero_div g
        dsimp only [HDiv.hDiv, Div.div] at h
        exact h
      dsimp only [SInt.scaleNat, SInt.divExact]
      rw [hg0, hm0, hZeroDiv]
  | false =>
    left
    have hDivNe : Nat.beq (Nat.div s.mag g) 0 = false := by
      cases hq : Nat.beq (Nat.div s.mag g) 0 with
      | false => rfl
      | true =>
        have hq0 : Nat.div s.mag g = 0 := Nat.eq_of_beq_eq_true hq
        rw [hq0, Nat.mul_zero] at hMulDiv
        rw [← hMulDiv] at hm
        nomatch hm
    have hg0 : Nat.beq g 0 = false := by
      cases hb : Nat.beq g 0 with
      | false => rfl
      | true =>
        have hgZero : g = 0 := Nat.eq_of_beq_eq_true hb
        rw [hgZero] at hg
        nomatch hg
    dsimp [SInt.scaleNat, SInt.divExact]
    rw [hg0, hDivNe, hMulDiv]

theorem sint_divExact_toInt (g : Nat) (s : SInt)
    (hg : 0 < g) (hd : Nat.mod s.mag g = 0) :
    Int.mul (Int.ofNat g) (SInt.divExact g s).toInt = s.toInt := by
  rw [← sint_scaleNat_toInt]
  cases sint_divExact_scale g s hg hd with
  | inl hEq => rw [hEq]
  | inr hPair =>
    rw [hPair.2]
    cases hN : s.neg with
    | false => dsimp [SInt.toInt, SInt.zero]; rw [hN, hPair.1]; rfl
    | true => dsimp [SInt.toInt, SInt.zero]; rw [hN, hPair.1]; rfl

/-- Soundness of an integer Chvatal-Gomory floor cut: `0 < g` and
`g * lhs ≤ rhs.toInt` imply `lhs ≤ (SInt.fdiv rhs g).toInt`. -/
theorem chvatal_gomory_floor_sound {g : Nat} {lhs : Int} {rhs : SInt}
    (hg : 0 < g) (hLe : Int.mul (Int.ofNat g) lhs ≤ rhs.toInt) :
    lhs ≤ (SInt.fdiv rhs g).toInt := by
  have hl := intBalance_self lhs
  have hgl := intBalance_mul_nat g hl
  have hr := sint_intBalance rhs
  have hNat : g * intPos lhs + rhs.negPart ≤ rhs.posPart + g * intNeg lhs :=
    (intBalance_le hgl hr).1 hLe
  cases hNeg : rhs.neg with
  | false =>
    dsimp [SInt.posPart, SInt.negPart] at hNat
    rw [hNeg, Nat.add_zero] at hNat
    have hr' : IntBalance (SInt.fdiv rhs g).toInt (Nat.div rhs.mag g) 0 := by
      dsimp [SInt.fdiv]; rw [hNeg]; exact intBalance_ofNat (Nat.div rhs.mag g)
    apply (intBalance_le hl hr').2
    rw [Nat.add_zero]
    cases Nat.lt_or_ge (intPos lhs) (intNeg lhs) with
    | inl hLt =>
      exact Nat.le_trans (Nat.le_of_lt hLt)
        (Nat.le_add_left (intNeg lhs) (Nat.div rhs.mag g))
    | inr hGe =>
      have hDiffMul : g * (intPos lhs - intNeg lhs) ≤ rhs.mag := by
        dsimp only at hNat
        have hAdded :
            g * (intPos lhs - intNeg lhs) + g * intNeg lhs ≤
              rhs.mag + g * intNeg lhs := by
          rw [← Nat.mul_add, Nat.sub_add_cancel hGe]
          exact hNat
        exact Nat.le_of_add_le_add_right hAdded
      have hDiv : intPos lhs - intNeg lhs ≤ Nat.div rhs.mag g := by
        rw [Nat.mul_comm] at hDiffMul
        exact (Nat.le_div_iff_mul_le hg).2 hDiffMul
      have hAdd := Nat.add_le_add_right hDiv (intNeg lhs)
      rw [Nat.sub_add_cancel hGe] at hAdd
      exact hAdd
  | true =>
    cases hMag : rhs.mag with
    | zero =>
      dsimp [SInt.posPart, SInt.negPart] at hNat
      rw [hNeg, hMag, Nat.add_zero, Nat.zero_add] at hNat
      have hr' : IntBalance (SInt.fdiv rhs g).toInt 0 0 := by
        dsimp [SInt.fdiv]; rw [hNeg, hMag]; exact intBalance_ofNat 0
      apply (intBalance_le hl hr').2
      rw [Nat.add_zero, Nat.zero_add]
      exact Nat.le_of_mul_le_mul_left hNat hg
    | succ m =>
      dsimp [SInt.posPart, SInt.negPart] at hNat
      rw [hNeg, hMag, Nat.zero_add] at hNat
      have hr' : IntBalance (SInt.fdiv rhs g).toInt 0 (Nat.div m g + 1) := by
        dsimp [SInt.fdiv]; rw [hNeg, hMag]
        exact intBalance_negOfNat (Nat.div m g + 1)
      apply (intBalance_le hl hr').2
      rw [Nat.zero_add]
      cases Nat.lt_or_ge (intNeg lhs) (intPos lhs + (Nat.div m g + 1)) with
      | inr hGe => exact hGe
      | inl hLt =>
        have hLeSub : intNeg lhs ≤ intPos lhs + Nat.div m g :=
          Nat.le_of_lt_succ hLt
        have hMulLe : g * intNeg lhs ≤ g * intPos lhs + g * Nat.div m g := by
          rw [← Nat.mul_add]
          exact Nat.mul_le_mul_left g hLeSub
        have hDivMul : g * Nat.div m g ≤ m := by
          rw [Nat.mul_comm]
          exact Nat.div_mul_le_self m g
        have hUp : g * intNeg lhs ≤ g * intPos lhs + m :=
          Nat.le_trans hMulLe (Nat.add_le_add_left hDivMul (g * intPos lhs))
        have hBad : g * intPos lhs + m + 1 ≤ g * intPos lhs + m :=
          Nat.le_trans hNat hUp
        exact False.elim (Nat.not_succ_le_self (g * intPos lhs + m) hBad)

/-! ## 3. Surface `Int` & `Nat` ASTs and Sparse Cut Certifier -/

noncomputable def listGet? {α : Type} : List α → Nat → Option α
  | [], _ => none
  | x :: _, 0 => some x
  | _ :: xs, i + 1 => listGet? xs i

noncomputable def envLookupInt (env : List Int) (idx : Nat) : Int :=
  match listGet? env idx with
  | some v => v
  | none => 0

noncomputable def envLookupNat (env : List Nat) (idx : Nat) : Nat :=
  match listGet? env idx with
  | some v => v
  | none => 0

/-- Deeply embedded integer linear arithmetic expression over indexed
variables (`var idx`) and `SInt` scalars. -/
inductive IntLinExpr where
  | cst  (c : SInt)
  | var  (idx : Nat)
  | add  (a b : IntLinExpr)
  | sub  (a b : IntLinExpr)
  | neg  (a : IntLinExpr)
  | mulC (k : SInt) (a : IntLinExpr)

/-- Evaluates an `IntLinExpr` under variable environment `env`. -/
noncomputable def IntLinExpr.eval (env : List Int) : IntLinExpr → Int
  | .cst c => c.toInt
  | .var idx => envLookupInt env idx
  | .add a b => Int.add (a.eval env) (b.eval env)
  | .sub a b => Int.sub (a.eval env) (b.eval env)
  | .neg a => Int.neg (a.eval env)
  | .mulC k a => Int.mul k.toInt (a.eval env)

/-- Surface integer linear inequality `lhs ≤ rhs`. -/
structure IntCutIneq where
  lhs : IntLinExpr
  rhs : IntLinExpr

/-- Truth predicate `iq.lhs.eval env ≤ iq.rhs.eval env`. -/
def IntCutIneq.holds (env : List Int) (iq : IntCutIneq) : Prop :=
  iq.lhs.eval env ≤ iq.rhs.eval env

/-- Curried implication chain over hypothesis list `xs` ending in
`post`. -/
def HypsImp {α : Type} (holds : α → Prop) (xs : List α) (post : Prop) : Prop :=
  List.foldr (fun h acc => holds h → acc) post xs

/-- Surface `Int` linear entailment goal (`hyps ⊢ concl`). -/
structure IntCutGoal where
  hyps  : List IntCutIneq
  concl : IntCutIneq

/-- Universally quantified semantic proposition denoted by `g`. -/
def IntCutGoal.denote (g : IntCutGoal) : Prop :=
  ∀ env : List Int, HypsImp (IntCutIneq.holds env) g.hyps (g.concl.holds env)

/-- Deeply embedded natural-number linear arithmetic expression over
indexed variables (`var idx`) and `Nat` scalars. -/
inductive NatLinExpr where
  | cst  (n : Nat)
  | var  (idx : Nat)
  | add  (a b : NatLinExpr)
  | mulC (k : Nat) (a : NatLinExpr)

/-- Evaluates a `NatLinExpr` under variable environment `env`. -/
noncomputable def NatLinExpr.eval (env : List Nat) : NatLinExpr → Nat
  | .cst n => n
  | .var idx => envLookupNat env idx
  | .add a b => a.eval env + b.eval env
  | .mulC k a => k * a.eval env

/-- Embeds a `NatLinExpr` into `IntLinExpr` with nonnegative scalars. -/
noncomputable def NatLinExpr.toIntExpr : NatLinExpr → IntLinExpr
  | .cst n => .cst ⟨false, n⟩
  | .var idx => .var idx
  | .add a b => .add a.toIntExpr b.toIntExpr
  | .mulC k a => .mulC ⟨false, k⟩ a.toIntExpr

theorem natLinExpr_toInt_eval (env : List Nat) :
    ∀ e : NatLinExpr,
      e.toIntExpr.eval (env.map Int.ofNat) = Int.ofNat (e.eval env)
  | .cst _ => rfl
  | .var idx => by
    dsimp [NatLinExpr.toIntExpr, IntLinExpr.eval, NatLinExpr.eval,
           envLookupInt, envLookupNat]
    revert idx
    induction env with
    | nil => intro idx; cases idx <;> rfl
    | cons _ _ ih =>
      intro idx
      cases idx with
      | zero => rfl
      | succ i => exact ih i
  | .add a b => by
    dsimp [NatLinExpr.toIntExpr, IntLinExpr.eval, NatLinExpr.eval]
    rw [natLinExpr_toInt_eval env a, natLinExpr_toInt_eval env b]
    rfl
  | .mulC _ a => by
    dsimp [NatLinExpr.toIntExpr, IntLinExpr.eval, NatLinExpr.eval]
    rw [natLinExpr_toInt_eval env a]
    rfl

/-- Surface natural-number linear inequality `lhs ≤ rhs`. -/
structure NatCutIneq where
  lhs : NatLinExpr
  rhs : NatLinExpr

/-- Truth predicate `iq.lhs.eval env ≤ iq.rhs.eval env`. -/
def NatCutIneq.holds (env : List Nat) (iq : NatCutIneq) : Prop :=
  iq.lhs.eval env ≤ iq.rhs.eval env

noncomputable def NatCutIneq.toIntIneq (iq : NatCutIneq) : IntCutIneq :=
  ⟨iq.lhs.toIntExpr, iq.rhs.toIntExpr⟩

/-- Surface `Nat` linear entailment goal (`hyps ⊢ concl`). -/
structure NatCutGoal where
  hyps  : List NatCutIneq
  concl : NatCutIneq

/-- Universally quantified semantic proposition denoted by `g`. -/
def NatCutGoal.denote (g : NatCutGoal) : Prop :=
  ∀ env : List Nat, HypsImp (NatCutIneq.holds env) g.hyps (g.concl.holds env)

/-- Sparse linear inequality `evalTerms env terms ≤ rhs.toInt`. Builders such
as `normIntLinExpr` produce strictly ascending variable indices as a canonical
normal form; soundness theorems hold for arbitrary `terms` lists. -/
structure SparseIneq where
  terms : List (Nat × SInt)
  rhs   : SInt

/-- Evaluates a sparse linear term list against variable environment
`env`. -/
noncomputable def evalTerms (env : List Int) : List (Nat × SInt) → Int
  | [] => 0
  | (v, c) :: rest =>
    Int.add (Int.mul c.toInt (envLookupInt env v)) (evalTerms env rest)

/-- Truth predicate for a canonical `SparseIneq` under `env`. -/
def SparseIneq.holds (env : List Int) (row : SparseIneq) : Prop :=
  evalTerms env row.terms ≤ row.rhs.toInt

noncomputable def addTermsAux (v1 : Nat) (c1 : SInt) (tail1 : List (Nat × SInt))
    (rec1 : List (Nat × SInt) → List (Nat × SInt)) :
    List (Nat × SInt) → List (Nat × SInt)
  | [] => (v1, c1) :: tail1
  | (v2, c2) :: rest2 =>
    match Nat.blt v1 v2 with
    | true => (v1, c1) :: rec1 ((v2, c2) :: rest2)
    | false =>
      match Nat.beq v1 v2 with
      | true =>
        let sum := SInt.add c1 c2
        match sum.isZero with
        | true => rec1 rest2
        | false => (v1, sum) :: rec1 rest2
      | false => (v2, c2) :: addTermsAux v1 c1 tail1 rec1 rest2

/-- Merges two sorted sparse term lists, summing matching variables and
dropping zero-sum coefficients. -/
noncomputable def addTerms :
    List (Nat × SInt) → List (Nat × SInt) → List (Nat × SInt)
  | [] => fun t2 => t2
  | (v1, c1) :: rest1 => addTermsAux v1 c1 rest1 (addTerms rest1)

theorem int_add_comm (a b : Int) : Int.add a b = Int.add b a :=
  intBalance_eq_of_eq (intBalance_add (intBalance_self a) (intBalance_self b))
    (intBalance_of_add_eq
      (intBalance_add (intBalance_self b) (intBalance_self a))
      (by rw [Nat.add_comm (intPos b) (intPos a),
              Nat.add_comm (intNeg b) (intNeg a)]))

theorem int_add_assoc (a b c : Int) :
    Int.add (Int.add a b) c = Int.add a (Int.add b c) :=
  intBalance_eq_of_eq
    (intBalance_add (intBalance_add (intBalance_self a) (intBalance_self b))
      (intBalance_self c))
    (intBalance_of_add_eq
      (intBalance_add (intBalance_self a)
        (intBalance_add (intBalance_self b) (intBalance_self c)))
      (by rw [Nat.add_assoc (intPos a) (intPos b) (intPos c),
              Nat.add_assoc (intNeg a) (intNeg b) (intNeg c)]))

theorem int_zero_add (a : Int) : Int.add 0 a = a :=
  intBalance_eq_of_eq
    (intBalance_of_add_eq
      (intBalance_add (intBalance_ofNat 0) (intBalance_self a))
      (by rw [Nat.zero_add, Nat.zero_add]))
    (intBalance_self a)

theorem int_add_zero (a : Int) : Int.add a 0 = a := by
  rw [int_add_comm]; exact int_zero_add a

theorem int_mul_add (a b c : Int) :
    Int.mul a (Int.add b c) = Int.add (Int.mul a b) (Int.mul a c) := by
  have ha := intBalance_self a
  have hb := intBalance_self b
  have hc := intBalance_self c
  have hL := intBalance_mul ha (intBalance_add hb hc)
  have hR := intBalance_add (intBalance_mul ha hb) (intBalance_mul ha hc)
  apply intBalance_eq_of_eq hL
  apply intBalance_of_add_eq hR
  rw [Nat.mul_add, Nat.mul_add, Nat.mul_add, Nat.mul_add]
  rw [add_four_rearrange (intPos a * intPos b) (intPos a * intPos c)
        (intNeg a * intNeg b) (intNeg a * intNeg c)]
  rw [add_four_rearrange (intPos a * intNeg b) (intPos a * intNeg c)
        (intNeg a * intPos b) (intNeg a * intPos c)]

theorem int_add_mul (a b c : Int) :
    Int.mul (Int.add a b) c = Int.add (Int.mul a c) (Int.mul b c) := by
  have ha := intBalance_self a
  have hb := intBalance_self b
  have hc := intBalance_self c
  have hL := intBalance_mul (intBalance_add ha hb) hc
  have hR := intBalance_add (intBalance_mul ha hc) (intBalance_mul hb hc)
  apply intBalance_eq_of_eq hL
  apply intBalance_of_add_eq hR
  rw [Nat.add_mul, Nat.add_mul, Nat.add_mul, Nat.add_mul]
  rw [add_four_rearrange (intPos a * intPos c) (intPos b * intPos c)
        (intNeg a * intNeg c) (intNeg b * intNeg c)]
  rw [add_four_rearrange (intPos a * intNeg c) (intPos b * intNeg c)
        (intNeg a * intPos c) (intNeg b * intPos c)]

theorem int_mul_assoc (a b c : Int) :
    Int.mul (Int.mul a b) c = Int.mul a (Int.mul b c) := by
  have ha := intBalance_self a
  have hb := intBalance_self b
  have hc := intBalance_self c
  have hL := intBalance_mul (intBalance_mul ha hb) hc
  have hR := intBalance_mul ha (intBalance_mul hb hc)
  apply intBalance_eq_of_eq hL
  apply intBalance_of_add_eq hR
  rw [Nat.add_mul, Nat.add_mul, Nat.add_mul, Nat.add_mul]
  rw [Nat.mul_add, Nat.mul_add, Nat.mul_add, Nat.mul_add]
  rw [Nat.mul_assoc, Nat.mul_assoc, Nat.mul_assoc, Nat.mul_assoc]
  rw [Nat.mul_assoc, Nat.mul_assoc, Nat.mul_assoc, Nat.mul_assoc]
  have hSwap :
      (intPos a * (intPos b * intPos c) + intNeg a * (intNeg b * intPos c)) +
      (intPos a * (intNeg b * intNeg c) + intNeg a * (intPos b * intNeg c)) =
      (intPos a * (intPos b * intPos c) + intPos a * (intNeg b * intNeg c)) +
      (intNeg a * (intPos b * intNeg c) + intNeg a * (intNeg b * intPos c)) := by
    rw [add_four_rearrange]
    rw [Nat.add_comm (intNeg a * (intNeg b * intPos c))
          (intNeg a * (intPos b * intNeg c))]
  have hSwap2 :
      (intPos a * (intPos b * intNeg c) + intNeg a * (intNeg b * intNeg c)) +
      (intPos a * (intNeg b * intPos c) + intNeg a * (intPos b * intPos c)) =
      (intPos a * (intPos b * intNeg c) + intPos a * (intNeg b * intPos c)) +
      (intNeg a * (intPos b * intPos c) + intNeg a * (intNeg b * intNeg c)) := by
    rw [add_four_rearrange]
    rw [Nat.add_comm (intNeg a * (intNeg b * intNeg c))
          (intNeg a * (intPos b * intPos c))]
  rw [hSwap, hSwap2]

theorem int_zero_mul (a : Int) : Int.mul 0 a = 0 :=
  intBalance_eq_of_eq
    (intBalance_of_add_eq
      (intBalance_mul (intBalance_ofNat 0) (intBalance_self a))
      (by rw [Nat.zero_mul, Nat.zero_mul, Nat.add_zero]))
    (intBalance_ofNat 0)

theorem sint_toInt_of_isZero (s : SInt) (h : s.isZero = true) : s.toInt = 0 := by
  have hm : s.mag = 0 := Nat.eq_of_beq_eq_true h
  cases hN : s.neg with
  | false => dsimp [SInt.toInt]; rw [hN, hm]; rfl
  | true => dsimp [SInt.toInt]; rw [hN, hm]; rfl

theorem evalTerms_addAux (env : List Int) (v1 : Nat) (c1 : SInt)
    (tail1 : List (Nat × SInt))
    (rec1 : List (Nat × SInt) → List (Nat × SInt))
    (hRec : ∀ t, evalTerms env (rec1 t) =
      Int.add (evalTerms env tail1) (evalTerms env t)) :
    ∀ t2 : List (Nat × SInt),
      evalTerms env (addTermsAux v1 c1 tail1 rec1 t2) =
        Int.add (Int.add (Int.mul c1.toInt (envLookupInt env v1))
          (evalTerms env tail1)) (evalTerms env t2)
  | [] => by dsimp [addTermsAux, evalTerms]; rw [int_add_zero]
  | (v2, c2) :: rest2 => by
    dsimp [addTermsAux]
    cases hLt : Nat.blt v1 v2 with
    | true =>
      dsimp [evalTerms]
      rw [hRec ((v2, c2) :: rest2), int_add_assoc]
      rfl
    | false =>
      cases hEq : Nat.beq v1 v2 with
      | true =>
        have hV : v1 = v2 := Nat.eq_of_beq_eq_true hEq
        dsimp
        cases hZ : (SInt.add c1 c2).isZero with
        | true =>
          rw [hRec rest2]
          dsimp [evalTerms]
          have hSumZero : Int.add c1.toInt c2.toInt = 0 := by
            rw [← sint_add_toInt]; exact sint_toInt_of_isZero _ hZ
          rw [← hV]
          have hComb :
              Int.add (Int.mul c1.toInt (envLookupInt env v1))
                (Int.mul c2.toInt (envLookupInt env v1)) = 0 := by
            rw [← int_add_mul, hSumZero, int_zero_mul]
          have hRearr :
              Int.add (Int.add (Int.mul c1.toInt (envLookupInt env v1))
                (evalTerms env tail1))
                (Int.add (Int.mul c2.toInt (envLookupInt env v1))
                  (evalTerms env rest2)) =
              Int.add (Int.add (Int.mul c1.toInt (envLookupInt env v1))
                (Int.mul c2.toInt (envLookupInt env v1)))
                (Int.add (evalTerms env tail1) (evalTerms env rest2)) := by
            rw [int_add_assoc, int_add_assoc]
            rw [← int_add_assoc (evalTerms env tail1),
                int_add_comm (evalTerms env tail1) (Int.mul c2.toInt _)]
            rw [int_add_assoc (Int.mul c2.toInt _)]
          rw [hRearr, hComb, int_zero_add]
        | false =>
          dsimp only [evalTerms]
          rw [hRec rest2, sint_add_toInt, int_add_mul, ← hV]
          rw [int_add_assoc, int_add_assoc]
          rw [← int_add_assoc (Int.mul c2.toInt _),
              int_add_comm (Int.mul c2.toInt _) (evalTerms env tail1)]
          rw [int_add_assoc (evalTerms env tail1)]
      | false =>
        dsimp only [evalTerms]
        rw [evalTerms_addAux env v1 c1 tail1 rec1 hRec rest2]
        rw [← int_add_assoc, int_add_comm (Int.mul c2.toInt _), int_add_assoc]

theorem evalTerms_add (env : List Int) :
    ∀ t1 t2 : List (Nat × SInt),
      evalTerms env (addTerms t1 t2) =
        Int.add (evalTerms env t1) (evalTerms env t2)
  | [], _ => by dsimp [addTerms, evalTerms]; rw [int_zero_add]
  | (v1, c1) :: rest1, t2 => by
    dsimp [addTerms]
    exact evalTerms_addAux env v1 c1 rest1 (addTerms rest1)
      (evalTerms_add env rest1) t2

noncomputable def scaleTermsNat (k : Nat) :
    List (Nat × SInt) → List (Nat × SInt)
  | [] => []
  | (v, c) :: rest =>
    let scaled := SInt.scaleNat k c
    match scaled.isZero with
    | true => scaleTermsNat k rest
    | false => (v, scaled) :: scaleTermsNat k rest

noncomputable def scaleTermsSInt (k : SInt) :
    List (Nat × SInt) → List (Nat × SInt)
  | [] => []
  | (v, c) :: rest =>
    let scaled := SInt.mul k c
    match scaled.isZero with
    | true => scaleTermsSInt k rest
    | false => (v, scaled) :: scaleTermsSInt k rest

theorem evalTerms_scaleNat (env : List Int) (k : Nat) :
    ∀ ts : List (Nat × SInt),
      evalTerms env (scaleTermsNat k ts) =
        Int.mul (Int.ofNat k) (evalTerms env ts)
  | [] => by
    dsimp only [scaleTermsNat, evalTerms]
    exact intBalance_eq_of_eq (intBalance_ofNat 0)
      (intBalance_mul_nat k (intBalance_ofNat 0))
  | (_, c) :: rest => by
    dsimp only [scaleTermsNat, evalTerms]
    cases hz : (SInt.scaleNat k c).isZero with
    | true =>
      rw [evalTerms_scaleNat env k rest, int_mul_add, ← int_mul_assoc]
      have hK0 : Int.mul (Int.ofNat k) c.toInt = 0 := by
        rw [← sint_scaleNat_toInt, sint_toInt_of_isZero _ hz]
      rw [hK0, int_zero_mul, int_zero_add]
    | false =>
      dsimp only [evalTerms]
      rw [evalTerms_scaleNat env k rest, int_mul_add, ← int_mul_assoc,
          sint_scaleNat_toInt]

theorem evalTerms_scaleSInt (env : List Int) (k : SInt) :
    ∀ ts : List (Nat × SInt),
      evalTerms env (scaleTermsSInt k ts) =
        Int.mul k.toInt (evalTerms env ts)
  | [] => by
    dsimp only [scaleTermsSInt, evalTerms]
    exact intBalance_eq_of_eq (intBalance_ofNat 0)
      (intBalance_mul (sint_intBalance k) (intBalance_ofNat 0))
  | (_, c) :: rest => by
    dsimp only [scaleTermsSInt, evalTerms]
    cases hz : (SInt.mul k c).isZero with
    | true =>
      rw [evalTerms_scaleSInt env k rest, int_mul_add, ← int_mul_assoc]
      have hK0 : Int.mul k.toInt c.toInt = 0 := by
        rw [← sint_mul_toInt, sint_toInt_of_isZero _ hz]
      rw [hK0, int_zero_mul, int_zero_add]
    | false =>
      dsimp only [evalTerms]
      rw [evalTerms_scaleSInt env k rest, int_mul_add, ← int_mul_assoc,
          sint_mul_toInt]

/-- Normalizes an `IntLinExpr` into `(terms, constant)` sparse form. -/
noncomputable def normIntLinExpr : IntLinExpr → List (Nat × SInt) × SInt
  | .cst c => ([], c)
  | .var idx => ([(idx, SInt.one)], SInt.zero)
  | .add a b =>
    let na := normIntLinExpr a
    let nb := normIntLinExpr b
    (addTerms na.1 nb.1, SInt.add na.2 nb.2)
  | .sub a b =>
    let na := normIntLinExpr a
    let nb := normIntLinExpr b
    (addTerms na.1 (scaleTermsSInt SInt.negOne nb.1), SInt.sub na.2 nb.2)
  | .neg a =>
    let na := normIntLinExpr a
    (scaleTermsSInt SInt.negOne na.1, SInt.negate na.2)
  | .mulC k a =>
    let na := normIntLinExpr a
    (scaleTermsSInt k na.1, SInt.mul k na.2)

theorem int_one_mul (a : Int) : Int.mul 1 a = a :=
  intBalance_eq_of_eq
    (intBalance_of_add_eq (intBalance_mul_nat 1 (intBalance_self a))
      (by rw [Nat.one_mul, Nat.one_mul]))
    (intBalance_self a)

theorem int_negOne_mul (a : Int) : Int.mul (SInt.negOne).toInt a = Int.neg a :=
  intBalance_eq_of_eq
    (intBalance_mul (intBalance_negOfNat 1) (intBalance_self a))
    (intBalance_of_add_eq (intBalance_neg (intBalance_self a))
      (by simp only [Nat.zero_mul, Nat.one_mul, Nat.zero_add]))

theorem int_sub_eq_add_neg (a b : Int) :
    Int.sub a b = Int.add a (Int.neg b) := rfl

/-- Correctness of `normIntLinExpr`: `evalTerms` plus constant equals
`e.eval env`. -/
theorem normIntLinExpr_sound (env : List Int) :
    ∀ e : IntLinExpr,
      Int.add (evalTerms env (normIntLinExpr e).1)
        (normIntLinExpr e).2.toInt = e.eval env
  | .cst c => by
    dsimp [normIntLinExpr, evalTerms, IntLinExpr.eval]
    exact int_zero_add c.toInt
  | .var _ => by
    dsimp [normIntLinExpr, evalTerms, IntLinExpr.eval, SInt.one, SInt.zero,
           SInt.toInt]
    rw [int_add_zero, int_add_zero, int_one_mul]
  | .add a b => by
    dsimp [normIntLinExpr, IntLinExpr.eval]
    rw [evalTerms_add, sint_add_toInt]
    rw [← normIntLinExpr_sound env a, ← normIntLinExpr_sound env b]
    rw [int_add_assoc, int_add_assoc]
    rw [← int_add_assoc (evalTerms env (normIntLinExpr b).1)]
    rw [int_add_comm (evalTerms env (normIntLinExpr b).1)
          (normIntLinExpr a).2.toInt]
    rw [int_add_assoc (normIntLinExpr a).2.toInt]
  | .sub a b => by
    dsimp [normIntLinExpr, IntLinExpr.eval, SInt.sub]
    rw [evalTerms_add, evalTerms_scaleSInt, sint_add_toInt]
    have hNegC :
        (SInt.negate (normIntLinExpr b).2).toInt =
          Int.neg (normIntLinExpr b).2.toInt :=
      intBalance_eq_of_eq (sint_negate_balance _)
        (intBalance_neg (sint_intBalance _))
    rw [hNegC, int_negOne_mul, int_sub_eq_add_neg]
    rw [← normIntLinExpr_sound env a, ← normIntLinExpr_sound env b]
    have hNegAdd :
        Int.neg (Int.add (evalTerms env (normIntLinExpr b).1)
          (normIntLinExpr b).2.toInt) =
        Int.add (Int.neg (evalTerms env (normIntLinExpr b).1))
          (Int.neg (normIntLinExpr b).2.toInt) :=
      intBalance_eq_of_eq
        (intBalance_neg (intBalance_add (intBalance_self _)
          (intBalance_self _)))
        (intBalance_add (intBalance_neg (intBalance_self _))
          (intBalance_neg (intBalance_self _)))
    rw [hNegAdd, int_add_assoc, int_add_assoc]
    rw [← int_add_assoc (Int.neg (evalTerms env (normIntLinExpr b).1))]
    rw [int_add_comm (Int.neg (evalTerms env (normIntLinExpr b).1))
          (normIntLinExpr a).2.toInt]
    rw [int_add_assoc (normIntLinExpr a).2.toInt]
  | .neg a => by
    dsimp [normIntLinExpr, IntLinExpr.eval]
    rw [evalTerms_scaleSInt, int_negOne_mul]
    have hNegC :
        (SInt.negate (normIntLinExpr a).2).toInt =
          Int.neg (normIntLinExpr a).2.toInt :=
      intBalance_eq_of_eq (sint_negate_balance _)
        (intBalance_neg (sint_intBalance _))
    rw [hNegC, ← normIntLinExpr_sound env a]
    exact intBalance_eq_of_eq
      (intBalance_add (intBalance_neg (intBalance_self _))
        (intBalance_neg (intBalance_self _)))
      (intBalance_neg (intBalance_add (intBalance_self _) (intBalance_self _)))
  | .mulC k a => by
    dsimp [normIntLinExpr, IntLinExpr.eval]
    rw [evalTerms_scaleSInt, sint_mul_toInt, ← int_mul_add,
        normIntLinExpr_sound env a]

/-- Normalizes `lhs ≤ rhs` into canonical sparse form `(lhs - rhs) ≤ 0`. -/
noncomputable def ineqToSparse (iq : IntCutIneq) : SparseIneq :=
  let n := normIntLinExpr (.sub iq.lhs iq.rhs)
  ⟨n.1, SInt.negate n.2⟩

/-- Soundness of `ineqToSparse`: `iq.holds env` implies
`(ineqToSparse iq).holds env`. -/
theorem ineqToSparse_sound (env : List Int) (iq : IntCutIneq) :
    iq.holds env → (ineqToSparse iq).holds env := by
  intro hLe
  dsimp [ineqToSparse, SparseIneq.holds]
  have hN := normIntLinExpr_sound env (.sub iq.lhs iq.rhs)
  dsimp [IntLinExpr.eval] at hN
  have hDiff : Int.sub (iq.lhs.eval env) (iq.rhs.eval env) ≤ 0 := by
    have ha := intBalance_self (iq.lhs.eval env)
    have hb := intBalance_self (iq.rhs.eval env)
    apply (intBalance_le (intBalance_sub ha hb) (intBalance_ofNat 0)).2
    rw [Nat.zero_add,
        Nat.add_comm (intNeg (iq.lhs.eval env)) (intPos (iq.rhs.eval env))]
    exact (intBalance_le ha hb).1 hLe
  rw [← hN] at hDiff
  have hNegC := sint_negate_balance (normIntLinExpr (.sub iq.lhs iq.rhs)).2
  have hNegS :=
    intBalance_neg (sint_intBalance (normIntLinExpr (.sub iq.lhs iq.rhs)).2)
  have hEqNeg :
      (SInt.negate (normIntLinExpr (.sub iq.lhs iq.rhs)).2).toInt =
        Int.neg (normIntLinExpr (.sub iq.lhs iq.rhs)).2.toInt :=
    intBalance_eq_of_eq hNegC hNegS
  rw [hEqNeg]
  have ht :=
    intBalance_self (evalTerms env (normIntLinExpr (.sub iq.lhs iq.rhs)).1)
  have hc := intBalance_self (normIntLinExpr (.sub iq.lhs iq.rhs)).2.toInt
  apply (intBalance_le ht (intBalance_neg hc)).2
  have hZero := (intBalance_le (intBalance_add ht hc) (intBalance_ofNat 0)).1
    hDiff
  rw [Nat.zero_add,
      Nat.add_comm
        (intNeg (evalTerms env (normIntLinExpr (.sub iq.lhs iq.rhs)).1))
        (intNeg (normIntLinExpr (.sub iq.lhs iq.rhs)).2.toInt)] at hZero
  exact hZero

/-- Single step in a Farkas / Chvatal-Gomory refutation certificate:
- `hyp idx`: copy hypothesis `idx` into the derived row log.
- `comb s1 k1 s2 k2`: nonnegative linear combination `k1 * r1 + k2 * r2`.
- `divCut g s`: integer floor cut dividing derived row `s` by `g > 0`. -/
inductive CutStep where
  | hyp    (idx : Nat)
  | comb   (s1 : Nat) (k1 : Nat) (s2 : Nat) (k2 : Nat)
  | divCut (g : Nat) (s : Nat)

noncomputable def allDivisible (g : Nat) : List (Nat × SInt) → Bool
  | [] => true
  | (_, c) :: rest => Nat.beq (Nat.mod c.mag g) 0 && allDivisible g rest

noncomputable def divTerms (g : Nat) :
    List (Nat × SInt) → List (Nat × SInt)
  | [] => []
  | (v, c) :: rest =>
    let q := SInt.divExact g c
    match q.isZero with
    | true => divTerms g rest
    | false => (v, q) :: divTerms g rest

theorem evalTerms_divTerms (env : List Int) (g : Nat) (hg : 0 < g) :
    ∀ ts : List (Nat × SInt),
      allDivisible g ts = true →
      Int.mul (Int.ofNat g) (evalTerms env (divTerms g ts)) = evalTerms env ts
  | [], _ => by
    dsimp [divTerms, evalTerms]
    exact intBalance_eq_of_eq
      (intBalance_mul_nat g (intBalance_ofNat 0)) (intBalance_ofNat 0)
  | (_, c) :: rest, hDiv => by
    dsimp only [allDivisible] at hDiv
    revert hDiv
    cases hMod : Nat.beq (Nat.mod c.mag g) 0 with
    | false => intro h; nomatch h
    | true =>
      intro hRest
      dsimp only [Bool.and] at hRest
      have hMod0 : Nat.mod c.mag g = 0 := Nat.eq_of_beq_eq_true hMod
      have hHead := sint_divExact_toInt g c hg hMod0
      dsimp only [divTerms]
      cases hz : (SInt.divExact g c).isZero with
      | true =>
        have hC0 : c.toInt = 0 := by
          rw [← hHead, sint_toInt_of_isZero _ hz]
          exact intBalance_eq_of_eq
            (intBalance_mul_nat g (intBalance_ofNat 0)) (intBalance_ofNat 0)
        dsimp only [evalTerms]
        rw [hC0, int_zero_mul, int_zero_add]
        exact evalTerms_divTerms env g hg rest hRest
      | false =>
        dsimp only [evalTerms]
        rw [int_mul_add, ← int_mul_assoc, hHead,
            evalTerms_divTerms env g hg rest hRest]

/-- Checks that every coefficient in a sparse term list is within
`magCap128`. -/
noncomputable def termsWithinCap : List (Nat × SInt) → Bool
  | [] => true
  | (_, c) :: rest => c.withinCap && termsWithinCap rest

/-- Checks that both the RHS and every term coefficient in a sparse row are
within `magCap128`. -/
noncomputable def rowWithinCap (r : SparseIneq) : Bool :=
  r.rhs.withinCap && termsWithinCap r.terms

/-- Checks that every `SparseIneq` in a list satisfies `rowWithinCap`. -/
noncomputable def rowsWithinCap : List SparseIneq → Bool
  | [] => true
  | r :: rest => rowWithinCap r && rowsWithinCap rest

/-- Reverse-order accumulator of derived rows plus their count, giving `O(1)`
push (`r :: revRows`) and `O(1)` last-row access (`last?`). Forward step index
`idx < len` translates to reverse offset `len - 1 - idx`. -/
structure DerivedRows where
  revRows : List SparseIneq
  len : Nat

def DerivedRows.empty : DerivedRows := ⟨[], 0⟩

def DerivedRows.push (d : DerivedRows) (r : SparseIneq) : DerivedRows :=
  ⟨r :: d.revRows, d.len + 1⟩

noncomputable def DerivedRows.get? (d : DerivedRows) (idx : Nat) :
    Option SparseIneq :=
  match Nat.blt idx d.len with
  | false => none
  | true => listGet? d.revRows (d.len - 1 - idx)

def DerivedRows.last? (d : DerivedRows) : Option SparseIneq :=
  match d.revRows with
  | [] => none
  | r :: _ => some r

/-- Executes one `CutStep` against `hyps` and previously derived rows,
failing closed (`none`) on out-of-bounds indices, cap overflow on input or
output rows, or non-divisible coefficients. -/
noncomputable def stepCut (hyps : List SparseIneq) (derived : DerivedRows) :
    CutStep → Option SparseIneq
  | .hyp idx =>
    match listGet? hyps idx with
    | none => none
    | some r =>
      match rowWithinCap r with
      | true => some r
      | false => none
  | .comb s1 k1 s2 k2 =>
    match Nat.ble k1 magCap128 && Nat.ble k2 magCap128 with
    | false => none
    | true =>
      match derived.get? s1, derived.get? s2 with
      | some r1, some r2 =>
        match rowWithinCap r1 && rowWithinCap r2 with
        | false => none
        | true =>
          let t := addTerms (scaleTermsNat k1 r1.terms)
            (scaleTermsNat k2 r2.terms)
          let r :=
            SInt.add (SInt.scaleNat k1 r1.rhs) (SInt.scaleNat k2 r2.rhs)
          let outRow : SparseIneq := ⟨t, r⟩
          match rowWithinCap outRow with
          | true => some outRow
          | false => none
      | _, _ => none
  | .divCut g s =>
    match Nat.ble 1 g && Nat.ble g magCap128 with
    | false => none
    | true =>
      match derived.get? s with
      | none => none
      | some row =>
        match rowWithinCap row with
        | false => none
        | true =>
          match allDivisible g row.terms with
          | false => none
          | true =>
            let outRow : SparseIneq :=
              ⟨divTerms g row.terms, SInt.fdiv row.rhs g⟩
            match rowWithinCap outRow with
            | true => some outRow
            | false => none

/-- Universal predicate asserting every `SparseIneq` in `rows` holds. -/
def AllHolds (env : List Int) (rows : List SparseIneq) : Prop :=
  ∀ r : SparseIneq, r ∈ rows → r.holds env

theorem allHolds_listGet {env : List Int} {rows : List SparseIneq}
    (hAll : AllHolds env rows) :
    ∀ (idx : Nat) (r : SparseIneq), listGet? rows idx = some r → r.holds env := by
  intro idx
  revert rows
  induction idx with
  | zero =>
    intro rows hAll r hGet
    cases rows with
    | nil => nomatch hGet
    | cons x xs =>
      dsimp [listGet?] at hGet
      injection hGet with hEq
      rw [← hEq]
      exact hAll x (List.Mem.head xs)
  | succ _ ih =>
    intro rows hAll r hGet
    cases rows with
    | nil => nomatch hGet
    | cons x _ =>
      dsimp [listGet?] at hGet
      apply ih (fun y hy => hAll y (List.Mem.tail x hy)) r hGet

theorem mem_of_mem_append {α : Type} {x : α} {xs ys : List α} :
    x ∈ xs ++ ys → x ∈ xs ∨ x ∈ ys := by
  induction xs with
  | nil => intro h; exact Or.inr h
  | cons a _ ih =>
    intro h
    cases h with
    | head _ => exact Or.inl (List.Mem.head _)
    | tail _ hTail =>
      cases ih hTail with
      | inl hL => exact Or.inl (List.Mem.tail a hL)
      | inr hR => exact Or.inr hR

theorem allHolds_derivedGet {env : List Int} {d : DerivedRows}
    (hAll : AllHolds env d.revRows) {idx : Nat} {r : SparseIneq}
    (hGet : d.get? idx = some r) : r.holds env := by
  dsimp [DerivedRows.get?] at hGet
  cases hLt : Nat.blt idx d.len with
  | false => rw [hLt] at hGet; nomatch hGet
  | true =>
    rw [hLt] at hGet
    exact allHolds_listGet hAll (d.len - 1 - idx) r hGet

theorem derivedLast?_mem {d : DerivedRows} {r : SparseIneq}
    (hLast : d.last? = some r) : r ∈ d.revRows := by
  cases h : d.revRows with
  | nil => rw [DerivedRows.last?, h] at hLast; nomatch hLast
  | cons x xs =>
    rw [DerivedRows.last?, h] at hLast
    injection hLast with hEq
    rw [← hEq]
    exact List.Mem.head xs

theorem int_add_le_add {a b c d : Int} (h1 : a ≤ b) (h2 : c ≤ d) :
    Int.add a c ≤ Int.add b d := by
  have ha := intBalance_self a
  have hb := intBalance_self b
  have hc := intBalance_self c
  have hd := intBalance_self d
  have hn1 := (intBalance_le ha hb).1 h1
  have hn2 := (intBalance_le hc hd).1 h2
  apply (intBalance_le (intBalance_add ha hc) (intBalance_add hb hd)).2
  rw [add_four_rearrange (intPos a) (intPos c) (intNeg b) (intNeg d)]
  rw [add_four_rearrange (intPos b) (intPos d) (intNeg a) (intNeg c)]
  exact Nat.add_le_add hn1 hn2

theorem int_mul_nat_le_mul_nat (k : Nat) {a b : Int} (h : a ≤ b) :
    Int.mul (Int.ofNat k) a ≤ Int.mul (Int.ofNat k) b := by
  have ha := intBalance_self a
  have hb := intBalance_self b
  have hn := (intBalance_le ha hb).1 h
  apply (intBalance_le (intBalance_mul_nat k ha) (intBalance_mul_nat k hb)).2
  rw [← Nat.mul_add, ← Nat.mul_add]
  exact Nat.mul_le_mul_left k hn

/-- Any row produced by `stepCut` holds whenever `hyps` and `derived`
hold. -/
theorem stepCut_sound {env : List Int} {hyps : List SparseIneq}
    {derived : DerivedRows} {st : CutStep} {out : SparseIneq}
    (hHyps : AllHolds env hyps) (hDer : AllHolds env derived.revRows)
    (hStep : stepCut hyps derived st = some out) :
    out.holds env := by
  cases st with
  | hyp idx =>
    dsimp [stepCut] at hStep
    revert hStep
    cases hGet : listGet? hyps idx with
    | none => intro h; nomatch h
    | some r =>
      dsimp
      cases rowWithinCap r with
      | false => intro h; nomatch h
      | true =>
        intro hEq
        injection hEq with hOut
        rw [← hOut]
        exact allHolds_listGet hHyps idx r hGet
  | comb s1 k1 s2 k2 =>
    dsimp [stepCut] at hStep
    revert hStep
    cases Nat.ble k1 magCap128 && Nat.ble k2 magCap128 with
    | false => intro h; nomatch h
    | true =>
      cases hg1 : derived.get? s1 with
      | none => intro h; nomatch h
      | some r1 =>
        cases hg2 : derived.get? s2 with
        | none => intro h; nomatch h
        | some r2 =>
          dsimp
          cases rowWithinCap r1 && rowWithinCap r2 with
          | false => intro h; nomatch h
          | true =>
            dsimp
            cases rowWithinCap ⟨addTerms (scaleTermsNat k1 r1.terms)
                (scaleTermsNat k2 r2.terms),
                SInt.add (SInt.scaleNat k1 r1.rhs)
                  (SInt.scaleNat k2 r2.rhs)⟩ with
            | false => intro h; nomatch h
            | true =>
              intro hEq
              injection hEq with hOut
              rw [← hOut]
              dsimp [SparseIneq.holds]
              rw [evalTerms_add, evalTerms_scaleNat, evalTerms_scaleNat,
                  sint_add_toInt, sint_scaleNat_toInt, sint_scaleNat_toInt]
              have h1 :=
                int_mul_nat_le_mul_nat k1 (allHolds_derivedGet hDer hg1)
              have h2 :=
                int_mul_nat_le_mul_nat k2 (allHolds_derivedGet hDer hg2)
              exact int_add_le_add h1 h2
  | divCut g s =>
    dsimp [stepCut] at hStep
    revert hStep
    cases hg : Nat.ble 1 g && Nat.ble g magCap128 with
    | false => intro h; nomatch h
    | true =>
      cases hGet : derived.get? s with
      | none => intro h; nomatch h
      | some row =>
        dsimp
        cases rowWithinCap row with
        | false => intro h; nomatch h
        | true =>
          dsimp
          cases hDiv : allDivisible g row.terms with
          | false => intro h; nomatch h
          | true =>
            dsimp
            cases rowWithinCap ⟨divTerms g row.terms,
                SInt.fdiv row.rhs g⟩ with
            | false => intro h; nomatch h
            | true =>
              intro hEq
              injection hEq with hOut
              rw [← hOut]
              dsimp [SparseIneq.holds]
              have hg1 : Nat.ble 1 g = true := by
                cases hb : Nat.ble 1 g with
                | true => rfl
                | false => rw [hb] at hg; nomatch hg
              have hgPos : 0 < g := Nat.le_of_ble_eq_true hg1
              have hRow := allHolds_derivedGet hDer hGet
              dsimp [SparseIneq.holds] at hRow
              rw [← evalTerms_divTerms env g hgPos row.terms hDiv] at hRow
              exact chvatal_gomory_floor_sound hgPos hRow

noncomputable def runCutStepsAux (hyps : List SparseIneq) :
    List CutStep → DerivedRows → Option DerivedRows
  | [], acc => some acc
  | st :: rest, acc =>
    match stepCut hyps acc st with
    | none => none
    | some next => runCutStepsAux hyps rest (acc.push next)

/-- Preserves `AllHolds` across a valid sequence of `CutStep`s. -/
theorem runCutStepsAux_sound {env : List Int} {hyps : List SparseIneq}
    (hHyps : AllHolds env hyps) :
    ∀ (steps : List CutStep) (acc res : DerivedRows),
      AllHolds env acc.revRows →
      runCutStepsAux hyps steps acc = some res →
      AllHolds env res.revRows
  | [], acc, res, hAcc, hRun => by
    dsimp [runCutStepsAux] at hRun
    injection hRun with hEq
    rw [← hEq]
    exact hAcc
  | st :: rest, acc, res, hAcc, hRun => by
    dsimp [runCutStepsAux] at hRun
    revert hRun
    cases hSt : stepCut hyps acc st with
    | none => intro h; nomatch h
    | some next =>
      intro hRest
      have hNext := stepCut_sound hHyps hAcc hSt
      have hAcc' : AllHolds env (acc.push next).revRows := by
        intro r hr
        dsimp [DerivedRows.push] at hr
        cases hr with
        | head _ => exact hNext
        | tail _ hTail => exact hAcc r hTail
      exact runCutStepsAux_sound hHyps rest (acc.push next) res hAcc' hRest

/-- Runs `steps` and checks that the last derived row has empty terms and
strictly negative `rhs`, witnessing `0 ≤ rhs < 0`. -/
noncomputable def checkCutRefute (hyps : List SparseIneq)
    (steps : List CutStep) : Bool :=
  match rowsWithinCap hyps with
  | false => false
  | true =>
    match runCutStepsAux hyps steps DerivedRows.empty with
    | none => false
    | some derived =>
      match derived.last? with
      | none => false
      | some last =>
        match last.terms with
        | [] => last.rhs.isStrictlyNeg
        | _ :: _ => false

/-- Soundness of `checkCutRefute`: an accepted refutation trace proves
`hyps` cannot jointly hold. -/
theorem checkCutRefute_sound {env : List Int} {hyps : List SparseIneq}
    {steps : List CutStep}
    (hChk : checkCutRefute hyps steps = true)
    (hHyps : AllHolds env hyps) : False := by
  dsimp [checkCutRefute] at hChk
  cases hCap : rowsWithinCap hyps with
  | false => rw [hCap] at hChk; nomatch hChk
  | true =>
    rw [hCap] at hChk
    dsimp at hChk
    cases hRun : runCutStepsAux hyps steps DerivedRows.empty with
    | none => rw [hRun] at hChk; nomatch hChk
    | some derived =>
      rw [hRun] at hChk
      dsimp at hChk
      cases hLast : derived.last? with
      | none => rw [hLast] at hChk; nomatch hChk
      | some last =>
        rw [hLast] at hChk
        dsimp at hChk
        cases hTerms : last.terms with
        | cons _ _ => rw [hTerms] at hChk; nomatch hChk
        | nil =>
          rw [hTerms] at hChk
          dsimp [SInt.isStrictlyNeg] at hChk
          have hAll :=
            runCutStepsAux_sound hHyps steps DerivedRows.empty derived
              (fun _ hm => nomatch hm) hRun
          have hHold := hAll last (derivedLast?_mem hLast)
          dsimp [SparseIneq.holds] at hHold
          rw [hTerms] at hHold
          dsimp [evalTerms] at hHold
          cases hN : last.rhs.neg with
          | false => rw [hN] at hChk; nomatch hChk
          | true =>
            rw [hN] at hChk
            dsimp [Bool.and] at hChk
            have hGe1 : 1 ≤ last.rhs.mag := Nat.le_of_ble_eq_true hChk
            have hr := sint_intBalance last.rhs
            have hBad := (intBalance_le (intBalance_ofNat 0) hr).1 hHold
            dsimp [SInt.posPart, SInt.negPart] at hBad
            rw [hN, Nat.zero_add] at hBad
            dsimp only at hBad
            have hContra : 1 ≤ 0 := Nat.le_trans hGe1 hBad
            nomatch hContra

/-- Bool checker verifying an `IntCutGoal` by refuting
`g.hyps ++ [g.concl.rhs + 1 ≤ g.concl.lhs]` via `steps`. -/
noncomputable def checkIntCutGoal (g : IntCutGoal) (steps : List CutStep) :
    Bool :=
  let negConcl : IntCutIneq := ⟨.add g.concl.rhs (.cst SInt.one), g.concl.lhs⟩
  let allSparse := (g.hyps ++ [negConcl]).map ineqToSparse
  checkCutRefute allSparse steps

theorem hypsImp_allHolds_int (env : List Int) (iqs : List IntCutIneq)
    (post : Prop)
    (hCont : (AllHolds env (iqs.map ineqToSparse)) → post) :
    HypsImp (IntCutIneq.holds env) iqs post := by
  induction iqs generalizing post with
  | nil =>
    apply hCont
    intro _ hr
    nomatch hr
  | cons iq _ ih =>
    intro hHere
    apply ih
    intro hRest
    apply hCont
    intro r hr
    dsimp [List.map] at hr
    cases hr with
    | head _ => exact ineqToSparse_sound env iq hHere
    | tail _ hTail => exact hRest r hTail

/-- Master `Int` linear-inequality reflection theorem: an accepted
`checkIntCutGoal` run proves `g.denote`. -/
theorem checkIntCutGoal_sound (g : IntCutGoal) (steps : List CutStep)
    (hChk : checkIntCutGoal g steps = true) : g.denote := by
  intro env
  apply hypsImp_allHolds_int env g.hyps
  intro hHypsSparse
  apply int_le_of_not_succ_le
  intro hNegConcl
  let negConcl : IntCutIneq := ⟨.add g.concl.rhs (.cst SInt.one), g.concl.lhs⟩
  have hNegSparse : (ineqToSparse negConcl).holds env :=
    ineqToSparse_sound env negConcl hNegConcl
  apply checkCutRefute_sound hChk (env := env)
  intro r hr
  have hMap :
      (g.hyps ++ [negConcl]).map ineqToSparse =
        g.hyps.map ineqToSparse ++ [ineqToSparse negConcl] := by
    induction g.hyps with
    | nil => rfl
    | cons _ _ ih => dsimp [List.map]; rw [ih]
  rw [hMap] at hr
  cases mem_of_mem_append hr with
  | inl hL => exact hHypsSparse r hL
  | inr hR =>
    cases hR with
    | head _ => exact hNegSparse
    | tail _ hNil => nomatch hNil

/-- Inserts `v` into a list of variable indices if not already present. -/
noncomputable def insertNatDedup (v : Nat) : List Nat → List Nat
  | [] => [v]
  | x :: xs =>
    match Nat.beq v x with
    | true => x :: xs
    | false => x :: insertNatDedup v xs

/-- Collects deduplicated variable indices appearing in `NatLinExpr`. -/
noncomputable def natLinExprVars : NatLinExpr → List Nat → List Nat
  | .cst _, acc => acc
  | .var idx, acc => insertNatDedup idx acc
  | .add a b, acc => natLinExprVars b (natLinExprVars a acc)
  | .mulC _ a, acc => natLinExprVars a acc

/-- Collects deduplicated variable indices appearing in a `NatCutIneq`. -/
noncomputable def natIneqVars (iq : NatCutIneq) (acc : List Nat) : List Nat :=
  natLinExprVars iq.rhs (natLinExprVars iq.lhs acc)

/-- Collects deduplicated variable indices across a list of `NatCutIneq`s. -/
noncomputable def natIneqListVars : List NatCutIneq → List Nat → List Nat
  | [], acc => acc
  | iq :: rest, acc => natIneqListVars rest (natIneqVars iq acc)

/-- Collects all distinct variable indices referenced in `g : NatCutGoal`
across `g.hyps` and `g.concl`. -/
noncomputable def natGoalVars (g : NatCutGoal) : List Nat :=
  natIneqVars g.concl (natIneqListVars g.hyps [])

/-- Integer inequality asserting nonnegativity `0 ≤ var v`. -/
def natNonnegIntIneq (v : Nat) : IntCutIneq :=
  ⟨.cst SInt.zero, .var v⟩

/-- Embeds a `NatCutGoal` into an `IntCutGoal`, preserving user hypothesis
indices `0 .. g.hyps.length - 1` and appending `0 ≤ var v` for every variable
in `natGoalVars g`. -/
noncomputable def natCutGoalToInt (g : NatCutGoal) : IntCutGoal :=
  ⟨g.hyps.map NatCutIneq.toIntIneq ++ (natGoalVars g).map natNonnegIntIneq,
   g.concl.toIntIneq⟩

/-- Bool checker verifying a `NatCutGoal` by embedding it into
`IntCutGoal` via `natCutGoalToInt` and running `checkIntCutGoal`. -/
noncomputable def checkNatCutGoal (g : NatCutGoal) (steps : List CutStep) :
    Bool :=
  checkIntCutGoal (natCutGoalToInt g) steps

theorem envLookupInt_map_ofNat (env : List Nat) (v : Nat) :
    envLookupInt (env.map Int.ofNat) v = Int.ofNat (envLookupNat env v) := by
  dsimp [envLookupInt, envLookupNat]
  revert v
  induction env with
  | nil => intro v; cases v <;> rfl
  | cons _ _ ih =>
    intro v
    cases v with
    | zero => rfl
    | succ i => exact ih i

theorem natNonnegIntIneq_holds_ofNat (env : List Nat) (iq : IntCutIneq)
    (hMem : ∃ v, natNonnegIntIneq v = iq) :
    iq.holds (env.map Int.ofNat) := by
  let ⟨v, hv⟩ := hMem
  rw [← hv]
  dsimp [natNonnegIntIneq, IntCutIneq.holds, IntLinExpr.eval, SInt.toInt]
  rw [envLookupInt_map_ofNat env v]
  exact (intBalance_le (intBalance_ofNat 0) (intBalance_ofNat _)).2
    (Nat.zero_le _)

theorem hypsImp_nat_to_int (env : List Nat) (iqs : List NatCutIneq)
    (post : Prop)
    (hInt : HypsImp (IntCutIneq.holds (env.map Int.ofNat))
              (iqs.map NatCutIneq.toIntIneq) post) :
    HypsImp (NatCutIneq.holds env) iqs post := by
  induction iqs with
  | nil => exact hInt
  | cons iq _ ih =>
    intro hNat
    apply ih
    apply hInt
    dsimp [NatCutIneq.toIntIneq, IntCutIneq.holds]
    rw [natLinExpr_toInt_eval env iq.lhs, natLinExpr_toInt_eval env iq.rhs]
    exact (intBalance_le (intBalance_ofNat _) (intBalance_ofNat _)).2 hNat

theorem hypsImp_append {α : Type} {f : α → Prop} {p : Prop} :
    ∀ (xs ys : List α),
      HypsImp f (xs ++ ys) p → HypsImp f xs (HypsImp f ys p)
  | [], _, h => h
  | _ :: rest, ys, h => fun hx => hypsImp_append rest ys (h hx)

theorem hypsImp_of_nonneg (env : List Nat) {post : Prop} :
    ∀ (vs : List Nat),
      HypsImp (IntCutIneq.holds (env.map Int.ofNat))
        (vs.map natNonnegIntIneq) post → post
  | [], h => h
  | v :: rest, h =>
    hypsImp_of_nonneg env rest
      (h (natNonnegIntIneq_holds_ofNat env (natNonnegIntIneq v) ⟨v, rfl⟩))

theorem hypsImp_concl_mono {α : Type} {f : α → Prop} {p q : Prop}
    (hpq : p → q) : ∀ {xs : List α}, HypsImp f xs p → HypsImp f xs q
  | [], h => hpq h
  | _ :: _, h => fun ha => hypsImp_concl_mono hpq (h ha)

/-- Master `Nat` linear-inequality reflection theorem: serves as an `omega`
substitute when a `CutStep` certificate is supplied in Pass-1 `theory/` and
`correspondence/` modules, discharged via `rfl` or `decide`. -/
theorem checkNatCutGoal_sound (g : NatCutGoal) (steps : List CutStep)
    (hChk : checkNatCutGoal g steps = true) : g.denote := by
  intro env
  have hInt := checkIntCutGoal_sound _ steps hChk (env.map Int.ofNat)
  have hSplit :=
    hypsImp_append (g.hyps.map NatCutIneq.toIntIneq)
      ((natGoalVars g).map natNonnegIntIneq) hInt
  apply hypsImp_nat_to_int env g.hyps
  refine hypsImp_concl_mono ?_ hSplit
  intro hNonneg
  have hC := hypsImp_of_nonneg env (natGoalVars g) hNonneg
  dsimp [natCutGoalToInt, NatCutIneq.toIntIneq, IntCutIneq.holds] at hC
  rw [natLinExpr_toInt_eval env g.concl.lhs,
      natLinExpr_toInt_eval env g.concl.rhs] at hC
  exact (intBalance_le (intBalance_ofNat _) (intBalance_ofNat _)).1 hC

/-! ## 4. Built-In Farkas, Chvatal-Gomory Cut, and `Int` Canaries -/

/-- Stride-inequality canary goal encoding `2 * i + 1 ≤ 2 * n → i + 1 ≤ n`.
Even though `CutStep.divCut` can simplify the hypothesis, this goal is already
refutable over rationals by Farkas combination alone (`.hyp 0` is the user
hypothesis, `.hyp 1` and `.hyp 2` are auto-generated `0 ≤ i` and `0 ≤ n`, and
`.hyp 3` is the negated conclusion `n + 1 ≤ i + 1`). -/
def parityStrideGoal : NatCutGoal :=
  let i := NatLinExpr.var 0
  let n := NatLinExpr.var 1
  { hyps := [⟨.add (.mulC 2 i) (.cst 1), .mulC 2 n⟩]
    concl := ⟨.add i (.cst 1), n⟩ }

/-- Cut-free three-step Farkas certificate discharging `parityStrideGoal`. -/
def parityStrideFarkasCert : List CutStep :=
  [ .hyp 0
  , .hyp 3
  , .comb 0 1 1 2
  ]

/-- Four-step `CutStep` certificate applying `CutStep.divCut 2 0` before
combining rows to prove `parityStrideGoal`. -/
def parityStrideCert : List CutStep :=
  [ .hyp 0
  , .divCut 2 0
  , .hyp 3
  , .comb 1 1 2 1
  ]

/-- Canary theorem discharging `2 * i + 1 ≤ 2 * n → i < n` by `rfl` via
the cut-free Farkas certificate (`parityStrideCert` also checks below). -/
theorem parity_stride_lt (i n : Nat) (h : 2 * i + 1 ≤ 2 * n) : i < n :=
  checkNatCutGoal_sound parityStrideGoal parityStrideFarkasCert rfl [i, n] h

/-- Verifies that `parityStrideCert` (using `divCut`) also checks
`parityStrideGoal` by `rfl`. -/
theorem parity_stride_cut_cert_ok :
    checkNatCutGoal parityStrideGoal parityStrideCert = true :=
  rfl

/-- Hypothesis-free `Nat` nonnegativity goal `⊢ 0 ≤ var 0`, discharged using
the auto-generated `0 ≤ var 0` constraint at `.hyp 0`. -/
def natVarNonnegGoal : NatCutGoal :=
  { hyps := []
    concl := ⟨.cst 0, .var 0⟩ }

/-- Proves `∀ x : Nat, 0 ≤ x` from zero user hypotheses by citing the
auto-generated `.hyp 0` nonnegativity constraint via `rfl`. -/
theorem nat_var_nonneg_no_hyps (x : Nat) : 0 ≤ x :=
  checkNatCutGoal_sound natVarNonnegGoal [.hyp 0, .hyp 1, .comb 0 1 1 1] rfl
    [x]

/-- Proves by `rfl` that a hypothesis whose coefficient exceeds `magCap128`
is rejected at `.hyp` ingestion. -/
theorem hyp_coeff_over_cap_rejected :
    stepCut [⟨[(0, ⟨false, magCap128 + 1⟩)], SInt.zero⟩] DerivedRows.empty
      (.hyp 0) = none ∧
    checkIntCutGoal
      { hyps := [⟨.mulC ⟨false, magCap128 + 1⟩ (.var 0), .cst SInt.zero⟩]
        concl := ⟨.cst SInt.one, .cst SInt.zero⟩ }
      [.hyp 0] = false :=
  ⟨rfl, rfl⟩

/-- Proves by `rfl` that a hypothesis whose RHS exceeds `magCap128` is
rejected at `.hyp` ingestion. -/
theorem hyp_rhs_over_cap_rejected :
    stepCut [⟨[(0, SInt.one)], ⟨false, magCap128 + 1⟩⟩] DerivedRows.empty
      (.hyp 0) = none :=
  rfl

/-- Proves by `rfl` that an oversized negated conclusion row is rejected
upfront by `checkCutRefute`, even when never cited by `steps`. -/
theorem concl_over_cap_rejected :
    checkIntCutGoal
      { hyps := [⟨.cst SInt.one, .cst SInt.zero⟩]
        concl := ⟨.cst SInt.zero, .cst ⟨false, magCap128⟩⟩ }
      [.hyp 0] = false :=
  rfl

/-- Proves by `rfl` that repeated `.comb` doubling of a zero-RHS row whose
coefficient crosses `magCap128` is rejected fail-closed (`none` / `false`). -/
theorem comb_coeff_overflow_rejected :
    let edgeRow : SparseIneq := ⟨[(0, ⟨false, magCap128⟩)], SInt.zero⟩
    stepCut [edgeRow] (DerivedRows.empty.push edgeRow) (.comb 0 1 0 1) =
      none ∧
    checkIntCutGoal
      { hyps := [⟨.mulC ⟨false, magCap128⟩ (.var 0), .cst SInt.zero⟩]
        concl := ⟨.cst SInt.zero, .var 0⟩ }
      [.hyp 0, .comb 0 1 0 1] = false :=
  ⟨rfl, rfl⟩

/-- Proves by `rfl` that `DerivedRows` preserves forward step indexing across
multiple `O(1)` pushes, rejects out-of-bounds indices, and returns the latest
pushed row from `last?`. -/
theorem derived_rows_reverse_index_ok :
    let r0 : SparseIneq := ⟨[(0, SInt.one)], SInt.zero⟩
    let r1 : SparseIneq := ⟨[(1, SInt.one)], SInt.one⟩
    let r2 : SparseIneq := ⟨[], ⟨true, 1⟩⟩
    let d := ((DerivedRows.empty.push r0).push r1).push r2
    d.get? 0 = some r0 ∧ d.get? 1 = some r1 ∧ d.get? 2 = some r2 ∧
    d.get? 3 = none ∧ d.last? = some r2 :=
  ⟨rfl, rfl, rfl, rfl, rfl⟩

/-- True parity-gap canary goal encoding `2 * i ≤ 2 * n + 1` and
`2 * n + 1 ≤ 2 * i` implying `1 ≤ 0`. Satisfiable over rationals at
`i = n + 1/2`, so cut-free Farkas combinations cannot derive `0 ≤ -1`. -/
def parityCutReqGoal : NatCutGoal :=
  let i := NatLinExpr.var 0
  let n := NatLinExpr.var 1
  { hyps :=
      [ ⟨.mulC 2 i, .add (.mulC 2 n) (.cst 1)⟩
      , ⟨.add (.mulC 2 n) (.cst 1), .mulC 2 i⟩ ]
    concl := ⟨.cst 1, .cst 0⟩ }

/-- Five-step Chvatal-Gomory certificate applying `CutStep.divCut 2` to both
parity bounds (`2i - 2n ≤ 1 → i - n ≤ 0` and `-2i + 2n ≤ -1 → -i + n ≤ -1`)
before summing to `0 ≤ -1`. -/
def parityCutReqCert : List CutStep :=
  [ .hyp 0
  , .divCut 2 0
  , .hyp 1
  , .divCut 2 2
  , .comb 1 1 3 1
  ]

/-- Proves by `rfl` that `parityCutReqCert` derives `False` from
`2 * i ≤ 2 * n + 1` and `2 * n + 1 ≤ 2 * i`. -/
theorem parity_cut_req_false (i n : Nat)
    (h1 : 2 * i ≤ 2 * n + 1) (h2 : 2 * n + 1 ≤ 2 * i) : False :=
  nomatch checkNatCutGoal_sound parityCutReqGoal parityCutReqCert rfl [i, n]
    h1 h2

/-- Proves by `rfl` that cut-free Farkas combination
`[.hyp 0, .hyp 1, .comb 0 1 1 1]` evaluates to `false` on
`parityCutReqGoal`. -/
theorem parity_cut_req_without_cut_fails :
    checkNatCutGoal parityCutReqGoal [.hyp 0, .hyp 1, .comb 0 1 1 1] = false :=
  rfl

/-- `IntCutGoal` canary exercising `IntLinExpr` constructors `.sub`, `.neg`,
and negative `.mulC` (`(-2) * x - y ≤ 5 → -3 ≤ -y → -4 ≤ x`). -/
def intSubNegMulGoal : IntCutGoal :=
  let x := IntLinExpr.var 0
  let y := IntLinExpr.var 1
  { hyps :=
      [ ⟨.sub (.mulC ⟨true, 2⟩ x) y, .cst ⟨false, 5⟩⟩
      , ⟨.cst ⟨true, 3⟩, .neg y⟩ ]
    concl := ⟨.cst ⟨true, 4⟩, x⟩ }

/-- Five-step certificate discharging `intSubNegMulGoal`. -/
def intSubNegMulCert : List CutStep :=
  [ .hyp 0
  , .hyp 1
  , .comb 0 1 1 1
  , .hyp 2
  , .comb 2 1 3 2
  ]

/-- Canary theorem discharging `intSubNegMulGoal` over arbitrary `x y : Int`
by `rfl`. -/
theorem int_sub_neg_mul_lower_bound (x y : Int)
    (h1 : Int.sub (Int.mul (Int.negOfNat 2) x) y ≤ Int.ofNat 5)
    (h2 : Int.negOfNat 3 ≤ Int.neg y) :
    Int.negOfNat 4 ≤ x :=
  checkIntCutGoal_sound intSubNegMulGoal intSubNegMulCert rfl [x, y] h1 h2

end Anneal.LinearArith
