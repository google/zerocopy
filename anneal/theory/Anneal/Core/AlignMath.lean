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
public import Init.Data.BitVec.BasicAux
public import Init.Data.Int.Basic
public import Init.Data.Nat.Basic
public import Init.Data.Nat.Div.Basic
public import Init.Data.Nat.Bitwise.Basic
public import Trusted
public import Trusted.MirAst
public import Trusted.MirModel
public import Trusted.MirSemantics
public import Anneal.InitLemmas
public import Anneal.NatBitwise
public import Anneal.BitVec
public import Anneal.BitVecArith
public import Anneal.MirWp

public section

namespace Anneal.Core

open Trusted.MirAst Trusted.MirSemantics Anneal.MirWp

/-!
# Zerocopy Alignment & Padding Bitvector Algebra (`Anneal.Core.AlignMath`)

Kernel-checked alignment math backing `google/zerocopy` (`src/util/mod.rs`):
`padding_needed_for` and `round_down_to_next_multiple_of_alignment` across
arbitrary bitvector widths `w ≥ 1`, specialized to `u32` and `u64`, and
bridged to `Trusted.MirSemantics.Ops` for 64-bit (`u64` and `usize`) MIR
verification:

1. **Power-of-Two Predicate (`isPow2BV`):** Equates
   `align ≠ 0 ∧ align &&& (align - 1) = 0` to `∃ k < w, align = 1#w <<< k`,
   proves positivity, `(align - 1).toNat = align.toNat - 1`, and divisibility
   `Dvd.dvd align.toNat (2^w)`.
2. **Padding Equivalence, Congruence, & Minimality (`paddingFast`):** Proves
   `!(len - 1) &&& (align - 1) = paddingNaive len align`, `< align.toNat`,
   both mathematical and wraparound modular alignment (`(len + p).toNat %
   align.toNat = 0`), and uniqueness / minimality.
3. **Round-Down Bounds, Divisibility, & Maximality (`roundDownFast`):**
   Proves `roundDownFast n align ≤ n`, `m.toNat % align.toNat = 0`, maximality
   among aligned bitvectors `≤ n`, and the next-multiple bound.
4. **Width Specializations (`u32`, `u64`) & `Trusted.MirSemantics` Bridges:**
   Specializes all alignment laws to 32-bit and 64-bit bitvectors and bridges
   `evalBinOp .sub`, `evalUnOp .not`, and `evalBinOp .bitAnd` on 64-bit `u64`
   (`.int .i64 false`) and `usize` (`.int .isize false`) scalars.
-/

/-! ## 0. Foundation Arithmetic & Bitwise Helpers -/

private theorem nat_pow_zero (a : Nat) : Nat.pow a 0 = 1 := rfl

private theorem nat_pow_succ (a n : Nat) :
    Nat.pow a (n + 1) = Nat.pow a n * a :=
  Nat.pow_succ a n

private theorem nat_pow_add (a m n : Nat) :
    Nat.pow a (m + n) = Nat.pow a m * Nat.pow a n :=
  Anneal.InitLemmas.nat_pow_add a m n

private theorem nat_two_pow_pos (n : Nat) : 0 < Nat.pow 2 n :=
  Anneal.InitLemmas.nat_two_pow_pos n

private theorem nat_pow_le_pow_right {i j : Nat} (h : i ≤ j) :
    Nat.pow 2 i ≤ Nat.pow 2 j :=
  Nat.pow_le_pow_right (by decide : 0 < 2) h

private theorem nat_pow_lt_pow_right {i j : Nat} (h : i < j) :
    Nat.pow 2 i < Nat.pow 2 j := by
  have hSucc : Nat.pow 2 i < Nat.pow 2 i + Nat.pow 2 i :=
    Nat.lt_add_of_pos_right (nat_two_pow_pos i)
  have hDouble : Nat.pow 2 i + Nat.pow 2 i = Nat.pow 2 (i + 1) := by
    rw [nat_pow_succ, Nat.mul_two]
  rw [hDouble] at hSucc
  exact Nat.lt_of_lt_of_le hSucc (nat_pow_le_pow_right h)

private theorem nat_div_zero (n : Nat) : Nat.div n 0 = 0 :=
  Nat.div_zero n

private theorem nat_zero_div (n : Nat) : Nat.div 0 n = 0 :=
  Nat.zero_div n

private theorem nat_div_one (n : Nat) : Nat.div n 1 = n :=
  Nat.div_one n

private theorem nat_zero_mod (n : Nat) : Nat.mod 0 n = 0 :=
  Nat.zero_mod n

private theorem nat_mod_one (n : Nat) : Nat.mod n 1 = 0 :=
  Nat.mod_one n

private theorem nat_mod_self (n : Nat) : Nat.mod n n = 0 :=
  Nat.mod_self n

private theorem nat_mod_eq_of_lt {a b : Nat} (h : a < b) :
    Nat.mod a b = a :=
  Nat.mod_eq_of_lt h

private theorem nat_div_eq_of_lt {a b : Nat} (h : a < b) :
    Nat.div a b = 0 :=
  Nat.div_eq_of_lt h

private theorem nat_div_mul_le_self (m n : Nat) :
    Nat.div m n * n ≤ m :=
  Nat.div_mul_le_self m n

private theorem nat_le_div_iff_mul_le {x y k : Nat} (hk : 0 < k) :
    x ≤ Nat.div y k ↔ x * k ≤ y :=
  Nat.le_div_iff_mul_le hk

private theorem nat_div_lt_iff_lt_mul {x y k : Nat} (hk : 0 < k) :
    Nat.div x k < y ↔ x < y * k :=
  Nat.div_lt_iff_lt_mul hk

private theorem nat_div_le_div_right {a b : Nat} (h : a ≤ b) (c : Nat) :
    Nat.div a c ≤ Nat.div b c := by
  cases c with
  | zero =>
    rw [nat_div_zero, nat_div_zero]
    exact Nat.le_refl 0
  | succ c' =>
    have hc : 0 < Nat.succ c' := Nat.zero_lt_succ c'
    exact (nat_le_div_iff_mul_le hc).mpr
      (Nat.le_trans (nat_div_mul_le_self a (Nat.succ c')) h)

private theorem nat_div_add_mod (m k : Nat) :
    k * Nat.div m k + Nat.mod m k = m :=
  Nat.div_add_mod m k

private theorem nat_add_mul_div_left (x z : Nat) {y : Nat} (hy : 0 < y) :
    Nat.div (x + y * z) y = Nat.div x y + z :=
  Nat.add_mul_div_left x z hy

private theorem nat_add_mul_mod_self_left (x y z : Nat) :
    Nat.mod (x + y * z) y = Nat.mod x y :=
  Nat.add_mul_mod_self_left x y z

private theorem nat_mul_add_mod_self_left (a b c : Nat) :
    Nat.mod (a * b + c) a = Nat.mod c a :=
  Nat.mul_add_mod_self_left a b c

private theorem nat_mul_mod_right (m n : Nat) :
    Nat.mod (m * n) m = 0 :=
  Nat.mul_mod_right m n

private theorem nat_mul_div_right (n : Nat) {m : Nat} (hm : 0 < m) :
    Nat.div (m * n) m = n :=
  Nat.mul_div_right n hm

private theorem nat_mul_div_left (m : Nat) {n : Nat} (hn : 0 < n) :
    Nat.div (m * n) n = m :=
  Nat.mul_div_left m hn

private theorem nat_div_div_eq_div_mul (m n k : Nat) :
    Nat.div (Nat.div m n) k = Nat.div m (n * k) :=
  Nat.div_div_eq_div_mul m n k

private theorem nat_mod_two_cases (n : Nat) :
    Nat.mod n 2 = 0 ∨ Nat.mod n 2 = 1 := by
  have hlt : Nat.mod n 2 < 2 := Nat.mod_lt n (by decide)
  cases hm : Nat.mod n 2 with
  | zero => left; rfl
  | succ k =>
    cases k with
    | zero => right; rfl
    | succ k' =>
      rw [hm] at hlt
      exact False.elim (Nat.not_lt_of_ge
        (Nat.succ_le_succ (Nat.succ_le_succ (Nat.zero_le k'))) hlt)

private theorem nat_lt_of_add_lt_add_right {a b c : Nat}
    (h : a + c < b + c) : a < b := by
  cases Nat.lt_or_ge a b with
  | inl hlt => exact hlt
  | inr hge =>
    exact False.elim (Nat.not_lt_of_ge (Nat.add_le_add_right hge c) h)

private theorem nat_mod_mod_mul_left (n a b : Nat) :
    Nat.mod (Nat.mod n (a * b)) a = Nat.mod n a := by
  have hDiv : Nat.mod n (a * b) + a * (b * Nat.div n (a * b)) = n := by
    rw [← Nat.mul_assoc]
    exact Nat.mod_add_div n (a * b)
  exact (nat_add_mul_mod_self_left (Nat.mod n (a * b)) a
    (b * Nat.div n (a * b))).symm.trans (congrArg (fun k => Nat.mod k a) hDiv)

private theorem nat_shiftLeft_eq (m k : Nat) :
    Nat.shiftLeft m k = m * Nat.pow 2 k :=
  Nat.shiftLeft_eq m k

private theorem bool_and_comm (a b : Bool) : (a && b) = (b && a) := by
  cases a with
  | false =>
    cases b with
    | false => rfl
    | true => rfl
  | true =>
    cases b with
    | false => rfl
    | true => rfl

private theorem int_ofNat_sub_ofNat (a b : Nat) :
    Int.ofNat a - Int.ofNat b = Int.subNatNat a b := by
  cases b with
  | zero =>
    unfold Int.subNatNat
    rw [Nat.zero_sub a]
    rfl
  | succ _ => rfl

private theorem intEmod_ofNat (m k : Nat) :
    intEmod (.ofNat m) (.ofNat k) = .ofNat (Nat.mod m k) := rfl

private theorem intEmod_negSucc (m k : Nat) :
    intEmod (.negSucc m) (.ofNat k) =
      Int.subNatNat k (Nat.succ (Nat.mod m k)) := rfl

private theorem nat_add_mod_cancel_left (a b m : Nat) :
    Nat.mod (Nat.mod a m + b) m = Nat.mod (a + b) m := by
  have ha := nat_div_add_mod a m
  rw [Nat.add_comm (m * Nat.div a m) (Nat.mod a m)] at ha
  have h1 := congrArg (fun z => z + b) ha.symm
  rw [Nat.add_right_comm (Nat.mod a m) (m * Nat.div a m) b] at h1
  rw [h1, nat_add_mul_mod_self_left]

private theorem nat_add_mod_cancel_right (a b m : Nat) :
    Nat.mod (a + Nat.mod b m) m = Nat.mod (a + b) m := by
  rw [Nat.add_comm a (Nat.mod b m), nat_add_mod_cancel_left, Nat.add_comm]

private theorem nat_land_one_eq (k : Nat) :
    Nat.land 1 k = if decide (Nat.mod k 2 = 1) then 1 else 0 := by
  rw [Anneal.NatBitwise.land_eq_bitwise, Anneal.NatBitwise.unfold_eq]
  cases k with
  | zero => rfl
  | succ k' =>
    have hdiv1 : Nat.div 1 2 = 0 := by decide
    have hmod1 : decide (Nat.mod 1 2 = 1) = true := by decide
    have hbw0 : Nat.bitwise and 0 (Nat.div (Nat.succ k') 2) = 0 := by
      rw [Anneal.NatBitwise.unfold_eq]
      rfl
    rw [Anneal.InitLemmas.ite_false_of (by decide : ¬ (1 = 0)),
      Anneal.InitLemmas.ite_false_of (fun h => nomatch h)]
    dsimp only
    rw [hdiv1, hbw0, hmod1]
    cases decide (Nat.mod (Nat.succ k') 2 = 1) <;> rfl

private theorem nat_testBit_eq (m i : Nat) :
    m.testBit i = decide (Nat.mod (Nat.div m (Nat.pow 2 i)) 2 = 1) := by
  unfold Nat.testBit
  have hsr : Nat.shiftRight m i = Nat.div m (Nat.pow 2 i) :=
    Nat.shiftRight_eq_div_pow m i
  change (Nat.land 1 (Nat.shiftRight m i) != 0) = _
  rw [hsr, nat_land_one_eq]
  cases decide (Nat.mod (Nat.div m (Nat.pow 2 i)) 2 = 1) <;> rfl

private theorem nat_testBit_zero_bit (m : Nat) :
    m.testBit 0 = decide (Nat.mod m 2 = 1) := by
  rw [nat_testBit_eq, nat_pow_zero, nat_div_one]

private theorem nat_testBit_succ (m i : Nat) :
    m.testBit (i + 1) = (Nat.div m 2).testBit i := by
  rw [nat_testBit_eq, nat_testBit_eq, nat_div_div_eq_div_mul,
    Nat.mul_comm 2 (Nat.pow 2 i), ← nat_pow_succ]

private theorem nat_testBit_zero (i : Nat) :
    (0 : Nat).testBit i = false := by
  rw [nat_testBit_eq, nat_zero_div, nat_zero_mod]
  rfl

private theorem nat_mod_two_mul (m A : Nat) (hA : 0 < A) :
    Nat.mod m (2 * A) = 2 * Nat.mod (Nat.div m 2) A + Nat.mod m 2 := by
  have hm := nat_div_add_mod m 2
  have hq := nat_div_add_mod (Nat.div m 2) A
  have hEq :
      m = (2 * A) * Nat.div (Nat.div m 2) A +
        (2 * Nat.mod (Nat.div m 2) A + Nat.mod m 2) := by
    have h1 := congrArg (fun z => 2 * z + Nat.mod m 2) hq
    rw [hm, Nat.mul_add, ← Nat.mul_assoc, Nat.add_assoc] at h1
    exact h1.symm
  have hModLt : Nat.mod (Nat.div m 2) A < A := Nat.mod_lt _ hA
  have hRemLt : 2 * Nat.mod (Nat.div m 2) A + Nat.mod m 2 < 2 * A := by
    have h2 : 2 * Nat.mod (Nat.div m 2) A + 2 ≤ 2 * A := by
      have hSucc : Nat.mod (Nat.div m 2) A + 1 ≤ A := hModLt
      have hMul := Nat.mul_le_mul_left 2 hSucc
      rw [Nat.mul_add, Nat.mul_one] at hMul
      exact hMul
    have hm2 : Nat.mod m 2 < 2 := Nat.mod_lt m (by decide)
    exact Nat.lt_of_lt_of_le (Nat.add_lt_add_left hm2 _) h2
  have hL := congrArg (fun z => Nat.mod z (2 * A)) hEq
  rw [nat_mul_add_mod_self_left, nat_mod_eq_of_lt hRemLt] at hL
  exact hL

private theorem nat_testBit_mod_two_pow (k : Nat) :
    ∀ m i : Nat,
      (Nat.mod m (Nat.pow 2 k)).testBit i = (decide (i < k) && m.testBit i) := by
  induction k with
  | zero =>
    intro m i
    rw [nat_pow_zero, nat_mod_one, nat_testBit_zero]
    exact Eq.symm (Bool.false_and _)
  | succ k ih =>
    intro m i
    have hPow : Nat.pow 2 (k + 1) = 2 * Nat.pow 2 k := by
      rw [nat_pow_succ, Nat.mul_comm]
    rw [hPow, nat_mod_two_mul m (Nat.pow 2 k) (nat_two_pow_pos k)]
    cases i with
    | zero =>
      rw [nat_testBit_zero_bit, nat_testBit_zero_bit,
        nat_mul_add_mod_self_left,
        decide_eq_true (Nat.zero_lt_succ k), Bool.true_and]
      have hm2 : Nat.mod m 2 < 2 := Nat.mod_lt m (by decide)
      rw [nat_mod_eq_of_lt hm2]
    | succ i' =>
      rw [nat_testBit_succ, nat_testBit_succ]
      have hm2 : Nat.mod m 2 < 2 := Nat.mod_lt m (by decide)
      rw [Nat.add_comm (2 * Nat.mod (Nat.div m 2) (Nat.pow 2 k)) (Nat.mod m 2),
        nat_add_mul_div_left (Nat.mod m 2) _ (by decide : 0 < 2),
        nat_div_eq_of_lt hm2, Nat.zero_add, ih (Nat.div m 2) i']
      cases Nat.lt_or_ge i' k with
      | inl hlt =>
        rw [decide_eq_true hlt, decide_eq_true (Nat.succ_lt_succ hlt)]
      | inr hge =>
        rw [decide_eq_false (Nat.not_lt_of_ge hge),
          decide_eq_false (Nat.not_lt_of_ge (Nat.succ_le_succ hge))]

private theorem nat_land_lt_two_pow {w n m : Nat}
    (hn : n < Nat.pow 2 w) (hm : m < Nat.pow 2 w) :
    Nat.land n m < Nat.pow 2 w :=
  Anneal.NatBitwise.land_lt_two_pow hn hm

private theorem nat_eq_zero_of_testBit_below {w n : Nat}
    (hn : n < Nat.pow 2 w)
    (h : ∀ i : Nat, i < w → n.testBit i = false) : n = 0 := by
  let a := BitVec.ofNatLT n hn
  have hEq : a = BitVec.ofNat w 0 := by
    apply Anneal.BitVec.eq_of_testBit_eq
    intro i hi
    change n.testBit i = (BitVec.ofNat w 0).toNat.testBit i
    rw [h i hi, Anneal.BitVec.toNat_zero, nat_testBit_zero]
  have hNat := congrArg BitVec.toNat hEq
  rw [Anneal.BitVec.toNat_ofNatLT, Anneal.BitVec.toNat_zero] at hNat
  exact hNat

private theorem nat_land_sub_one_eq_zero :
    ∀ w n : Nat, n < Nat.pow 2 w → 0 < n → Nat.land n (n - 1) = 0 →
      ∃ k : Nat, k < w ∧ n = Nat.pow 2 k := by
  intro w
  induction w with
  | zero =>
    intro n hn hpos _
    have hZ : n = 0 := Nat.eq_zero_of_le_zero (Nat.le_of_lt_succ hn)
    rw [hZ] at hpos
    nomatch hpos
  | succ w ih =>
    intro n hn hpos hland
    let q := Nat.div n 2
    have hn1 : n - 1 < Nat.pow 2 (w + 1) :=
      Nat.lt_of_le_of_lt (Nat.sub_le n 1) hn
    have hPowSucc : Nat.pow 2 (w + 1) = 2 * Nat.pow 2 w := by
      rw [nat_pow_succ, Nat.mul_comm]
    have hDivLt : q < Nat.pow 2 w := by
      rw [nat_div_lt_iff_lt_mul (by decide : 0 < 2), Nat.mul_comm, ← hPowSucc]
      exact hn
    cases nat_mod_two_cases n with
    | inl hEven =>
      have hN : n = 2 * q := by
        have hm := nat_div_add_mod n 2
        rw [hEven, Nat.add_zero] at hm
        exact hm.symm
      have hQPos : 0 < q := by
        revert hN
        cases hq : q with
        | zero =>
          intro hN; rw [Nat.mul_zero] at hN
          rw [hN] at hpos
          nomatch hpos
        | succ q' => intro hN; exact Nat.zero_lt_succ q'
      have hN1 : n - 1 = 2 * (q - 1) + 1 := by
        have hQ : q = (q - 1) + 1 := Eq.symm (Nat.sub_add_cancel hQPos)
        have h1 : n = (2 * (q - 1) + 1) + 1 := by
          have h2 : 2 * q = 2 * ((q - 1) + 1) := congrArg (fun z => 2 * z) hQ
          rw [Nat.mul_add, Nat.mul_one] at h2
          rw [hN, h2, Nat.add_assoc]
        rw [h1, Nat.add_sub_cancel]
      have hDivN1 : Nat.div (n - 1) 2 = q - 1 := by
        rw [hN1, Nat.add_comm (2 * (q - 1)) 1,
          nat_add_mul_div_left 1 (q - 1) (by decide : 0 < 2),
          nat_div_eq_of_lt (by decide : 1 < 2), Nat.zero_add]
      have hQ1Lt : q - 1 < Nat.pow 2 w :=
        Nat.lt_of_le_of_lt (Nat.sub_le _ 1) hDivLt
      have hQLandLt : Nat.land q (q - 1) < Nat.pow 2 w :=
        nat_land_lt_two_pow hDivLt hQ1Lt
      have hQLand : Nat.land q (q - 1) = 0 := by
        apply nat_eq_zero_of_testBit_below hQLandLt
        intro i _
        have h1 :
            Nat.land q (q - 1) =
              (Anneal.BitVec.and (BitVec.ofNatLT q hDivLt)
                (BitVec.ofNatLT (q - 1) hQ1Lt)).toNat := rfl
        have h2 :
            Nat.land n (n - 1) =
              (Anneal.BitVec.and (BitVec.ofNatLT n hn)
                (BitVec.ofNatLT (n - 1) hn1)).toNat := rfl
        rw [h1, Anneal.BitVec.testBit_and, Anneal.BitVec.toNat_ofNatLT,
          Anneal.BitVec.toNat_ofNatLT]
        rw [← nat_testBit_succ n i, ← hDivN1, ← nat_testBit_succ (n - 1) i]
        have hBit := congrArg (fun z => z.testBit (i + 1)) hland
        rw [h2, Anneal.BitVec.testBit_and, Anneal.BitVec.toNat_ofNatLT,
          Anneal.BitVec.toNat_ofNatLT, nat_testBit_zero] at hBit
        exact hBit
      let ⟨k, hkw, hkq⟩ := ih q hDivLt hQPos hQLand
      refine ⟨k + 1, Nat.succ_lt_succ hkw, ?_⟩
      rw [hN, hkq, nat_pow_succ, Nat.mul_comm]
    | inr hOdd =>
      have hN : n = 2 * q + 1 := by
        have hm := nat_div_add_mod n 2
        rw [hOdd] at hm
        exact hm.symm
      have hN1 : n - 1 = 2 * q := by
        rw [hN, Nat.add_sub_cancel]
      have hDivN1 : Nat.div (n - 1) 2 = q := by
        rw [hN1]
        exact nat_mul_div_right q (by decide : 0 < 2)
      have hQ0 : q = 0 := by
        apply nat_eq_zero_of_testBit_below hDivLt
        intro i _
        have h2 :
            Nat.land n (n - 1) =
              (Anneal.BitVec.and (BitVec.ofNatLT n hn)
                (BitVec.ofNatLT (n - 1) hn1)).toNat := rfl
        have hBit := congrArg (fun z => z.testBit (i + 1)) hland
        rw [h2, Anneal.BitVec.testBit_and, Anneal.BitVec.toNat_ofNatLT,
          Anneal.BitVec.toNat_ofNatLT, nat_testBit_zero] at hBit
        change (n.testBit (i + 1) && (n - 1).testBit (i + 1)) = false at hBit
        rw [nat_testBit_succ, nat_testBit_succ, hDivN1] at hBit
        change (q.testBit i && q.testBit i) = false at hBit
        revert hBit
        cases hq : q.testBit i with
        | false => intro hBit; rfl
        | true =>
          intro hBit
          exact hBit
      refine ⟨0, Nat.zero_lt_succ w, ?_⟩
      rw [hN, hQ0, Nat.mul_zero, Nat.zero_add, nat_pow_zero]

/-! ## 1. Power-of-Two Predicate & Bitvector Characterization (`isPow2BV`) -/

/-- Power-of-two bitvector predicate matching `u*::is_power_of_two`:
`align ≠ 0 ∧ align &&& (align - 1) = 0`. -/
@[expose] def isPow2BV {w : Nat} (align : BitVec w) : Prop :=
  align ≠ BitVec.ofNat w 0 ∧
    Anneal.BitVec.and align (align - BitVec.ofNat w 1) = BitVec.ofNat w 0

/-- Every power-of-two bitvector has strictly positive `.toNat`. -/
theorem isPow2BV_pos {w : Nat} {align : BitVec w} (h : isPow2BV align) :
    0 < align.toNat := by
  cases hz : align.toNat with
  | zero =>
    have hEq : align = BitVec.ofNat w 0 :=
      Anneal.BitVec.eq_of_toNat_eq
        (Eq.trans hz (Eq.symm (Anneal.BitVec.toNat_zero w)))
    exact False.elim (h.1 hEq)
  | succ k => exact Nat.zero_lt_succ k

/-- Every power-of-two bitvector has positive bit width `0 < w`. -/
theorem isPow2BV_width_pos {w : Nat} {align : BitVec w} (h : isPow2BV align) :
    0 < w := by
  cases w with
  | zero =>
    have hZero : align.toNat = 0 :=
      Nat.eq_zero_of_le_zero (Nat.le_of_lt_succ align.isLt)
    have hPos := isPow2BV_pos h
    rw [hZero] at hPos
    nomatch hPos
  | succ w' => exact Nat.zero_lt_succ w'

/-- Exact `.toNat` of `x - 1#w` whenever `x ≠ 0#w`. -/
theorem toNat_sub_one_of_ne_zero {w : Nat} {x : BitVec w}
    (hx : x ≠ BitVec.ofNat w 0) :
    (x - BitVec.ofNat w 1).toNat = x.toNat - 1 := by
  have hxPos : 0 < x.toNat := by
    cases hz : x.toNat with
    | zero =>
      have hEq : x = BitVec.ofNat w 0 :=
        Anneal.BitVec.eq_of_toNat_eq
          (Eq.trans hz (Eq.symm (Anneal.BitVec.toNat_zero w)))
      exact False.elim (hx hEq)
    | succ k => exact Nat.zero_lt_succ k
  have hwPos : 0 < w := by
    cases w with
    | zero =>
      have hZ : x.toNat = 0 := Nat.eq_zero_of_le_zero (Nat.le_of_lt_succ x.isLt)
      rw [hZ] at hxPos
      nomatch hxPos
    | succ w' => exact Nat.zero_lt_succ w'
  have hPowGe : 2 ≤ Nat.pow 2 w := by
    have h1 : Nat.pow 2 1 = 2 := by decide
    rw [← h1]
    exact nat_pow_le_pow_right hwPos
  have h1Lt : 1 < Nat.pow 2 w := Nat.lt_of_lt_of_le (by decide : 1 < 2) hPowGe
  have h1Le : BitVec.ofNat w 1 ≤ x := by
    change (BitVec.ofNat w 1).toNat ≤ x.toNat
    rw [Anneal.BitVec.toNat_ofNat, nat_mod_eq_of_lt h1Lt]
    exact hxPos
  rw [Anneal.BitVec.toNat_sub_of_le h1Le, Anneal.BitVec.toNat_ofNat,
    nat_mod_eq_of_lt h1Lt]

/-- Characterization of `isPow2BV align`: there exists `k < w` such that
`align.toNat = 2^k` and `align = 1#w <<< k`. -/
theorem isPow2BV_exists_shl {w : Nat} {align : BitVec w}
    (h : isPow2BV align) :
    ∃ k : Nat, k < w ∧ align.toNat = Nat.pow 2 k ∧
      align = Anneal.BitVec.shl (BitVec.ofNat w 1) k := by
  have hPos := isPow2BV_pos h
  have hwPos := isPow2BV_width_pos h
  have hLand0 : Nat.land align.toNat (align.toNat - 1) = 0 := by
    have hAndNat := congrArg BitVec.toNat h.2
    rw [Anneal.BitVec.toNat_and, toNat_sub_one_of_ne_zero h.1,
      Anneal.BitVec.toNat_zero] at hAndNat
    exact hAndNat
  let ⟨k, hkw, hPow⟩ := nat_land_sub_one_eq_zero w align.toNat align.isLt hPos hLand0
  have h1Lt : 1 < Nat.pow 2 w := by
    have h1 : Nat.pow 2 1 = 2 := by decide
    have hPowGe : Nat.pow 2 1 ≤ Nat.pow 2 w := nat_pow_le_pow_right hwPos
    rw [h1] at hPowGe
    exact Nat.lt_of_lt_of_le (by decide : 1 < 2) hPowGe
  refine ⟨k, hkw, hPow, ?_⟩
  apply Anneal.BitVec.eq_of_toNat_eq
  rw [Anneal.BitVec.toNat_shl, Anneal.BitVec.toNat_ofNat,
    nat_mod_eq_of_lt h1Lt, nat_shiftLeft_eq, Nat.one_mul, hPow,
    nat_mod_eq_of_lt (nat_pow_lt_pow_right hkw)]

/-- Converse: for any `k < w`, `1#w <<< k` satisfies `isPow2BV`. -/
theorem isPow2BV_of_lt_width {w k : Nat} (hk : k < w) :
    isPow2BV (Anneal.BitVec.shl (BitVec.ofNat w 1) k) := by
  have hwPos : 0 < w := Nat.lt_of_le_of_lt (Nat.zero_le k) hk
  have h1Lt : 1 < Nat.pow 2 w := by
    have h1 : Nat.pow 2 1 = 2 := by decide
    have hPowGe : Nat.pow 2 1 ≤ Nat.pow 2 w := nat_pow_le_pow_right hwPos
    rw [h1] at hPowGe
    exact Nat.lt_of_lt_of_le (by decide : 1 < 2) hPowGe
  have hShlToNat : (Anneal.BitVec.shl (BitVec.ofNat w 1) k).toNat = Nat.pow 2 k := by
    rw [Anneal.BitVec.toNat_shl, Anneal.BitVec.toNat_ofNat,
      nat_mod_eq_of_lt h1Lt, nat_shiftLeft_eq, Nat.one_mul,
      nat_mod_eq_of_lt (nat_pow_lt_pow_right hk)]
  have hNe0 : Anneal.BitVec.shl (BitVec.ofNat w 1) k ≠ BitVec.ofNat w 0 := by
    intro hEq
    have hNat := congrArg BitVec.toNat hEq
    rw [hShlToNat, Anneal.BitVec.toNat_zero] at hNat
    have hPos := nat_two_pow_pos k
    rw [hNat] at hPos
    nomatch hPos
  refine ⟨hNe0, ?_⟩
  have hSubNat :
      (Anneal.BitVec.shl (BitVec.ofNat w 1) k - BitVec.ofNat w 1).toNat =
        Nat.pow 2 k - 1 := by
    rw [toNat_sub_one_of_ne_zero hNe0, hShlToNat]
  have hSubEqLow :
      Anneal.BitVec.shl (BitVec.ofNat w 1) k - BitVec.ofNat w 1 =
        Anneal.BitVec.lowMask w k := by
    apply Anneal.BitVec.eq_of_toNat_eq
    rw [hSubNat]
    unfold Anneal.BitVec.lowMask
    rw [Anneal.BitVec.toNat_ofNat]
    exact Eq.symm (nat_mod_eq_of_lt (Nat.lt_of_lt_of_le
      (Nat.sub_lt (nat_two_pow_pos k) Nat.one_pos)
      (nat_pow_le_pow_right (Nat.le_of_lt hk))))
  rw [hSubEqLow]
  apply Anneal.BitVec.eq_of_getLsbD_eq
  intro i hi
  rw [Anneal.BitVec.getLsbD_and, Anneal.BitVec.getLsbD_shl,
    Anneal.BitVec.getLsbD_lowMask hi, Anneal.BitVec.getLsbD_zero,
    decide_eq_true hi, Bool.true_and]
  cases Nat.lt_or_ge i k with
  | inl hlt =>
    rw [decide_eq_false (Nat.not_le_of_gt hlt), Bool.false_and, Bool.false_and]
  | inr hge =>
    rw [decide_eq_false (Nat.not_lt_of_ge hge), Bool.and_false]

/-- Exact equivalence `isPow2BV align ↔ ∃ k < w, align = 1#w <<< k`. -/
theorem isPow2BV_iff_exists_shl {w : Nat} (align : BitVec w) :
    isPow2BV align ↔
      ∃ k : Nat, k < w ∧ align = Anneal.BitVec.shl (BitVec.ofNat w 1) k :=
  ⟨fun h =>
    let ⟨k, hkw, _, hEq⟩ := isPow2BV_exists_shl h
    ⟨k, hkw, hEq⟩,
   fun ⟨k, hkw, hEq⟩ => by
    rw [hEq]
    exact isPow2BV_of_lt_width hkw⟩

/-- Every power-of-two `align : BitVec w` divides the bitvector modulus
`2^w`. -/
theorem isPow2BV_dvd_two_pow {w : Nat} {align : BitVec w}
    (h : isPow2BV align) :
    Dvd.dvd align.toNat (Nat.pow 2 w) := by
  let ⟨k, hkw, hPow, _⟩ := isPow2BV_exists_shl h
  have hSplit : w = k + (w - k) := Eq.symm (Nat.add_sub_of_le (Nat.le_of_lt hkw))
  refine ⟨Nat.pow 2 (w - k), ?_⟩
  rw [hPow, ← nat_pow_add, ← hSplit]

/-- When `isPow2BV align` with `align.toNat = 2^k` and `k < w`, `align - 1#w`
is exactly `Anneal.BitVec.lowMask w k`. -/
theorem align_sub_one_eq_lowMask {w k : Nat} {align : BitVec w}
    (hk : k < w) (hNe0 : align ≠ BitVec.ofNat w 0)
    (hPow : align.toNat = Nat.pow 2 k) :
    align - BitVec.ofNat w 1 = Anneal.BitVec.lowMask w k := by
  apply Anneal.BitVec.eq_of_toNat_eq
  rw [toNat_sub_one_of_ne_zero hNe0, hPow]
  unfold Anneal.BitVec.lowMask
  rw [Anneal.BitVec.toNat_ofNat]
  exact Eq.symm (nat_mod_eq_of_lt (Nat.lt_of_lt_of_le
    (Nat.sub_lt (nat_two_pow_pos k) Nat.one_pos)
    (nat_pow_le_pow_right (Nat.le_of_lt hk))))

/-! ## 2. Padding Formulas, Equivalence, Congruence, & Minimality -/

/-- Reference naive padding formula matching Zerocopy's SMT specification:
`0` if `len &&& (align - 1) = 0`, else `align - (len &&& (align - 1))`. -/
@[expose] def paddingNaive {w : Nat} (len align : BitVec w) : BitVec w :=
  let rem := Anneal.BitVec.and len (align - BitVec.ofNat w 1)
  if rem == BitVec.ofNat w 0 then BitVec.ofNat w 0 else align - rem

/-- Branch-free fast padding implementation matching `padding_needed_for`:
`!(len.wrapping_sub(1)) & (align - 1)`. -/
@[expose] def paddingFast {w : Nat} (len align : BitVec w) : BitVec w :=
  Anneal.BitVec.and (Anneal.BitVec.not (len - BitVec.ofNat w 1))
    (align - BitVec.ofNat w 1)

/-- Masking any `BitVec w` with `lowMask w k` (`k < w`) computes `x.toNat mod
2^k`. -/
theorem toNat_and_lowMask_eq_mod {w k : Nat} (hk : k < w) (x : BitVec w) :
    (Anneal.BitVec.and x (Anneal.BitVec.lowMask w k)).toNat =
      Nat.mod x.toNat (Nat.pow 2 k) := by
  have hModLt : Nat.mod x.toNat (Nat.pow 2 k) < Nat.pow 2 w :=
    Nat.lt_of_lt_of_le (Nat.mod_lt x.toNat (nat_two_pow_pos k))
      (nat_pow_le_pow_right (Nat.le_of_lt hk))
  have hEq :
      Anneal.BitVec.and x (Anneal.BitVec.lowMask w k) =
        BitVec.ofNatLT (Nat.mod x.toNat (Nat.pow 2 k)) hModLt := by
    apply Anneal.BitVec.eq_of_getLsbD_eq
    intro i hi
    rw [Anneal.BitVec.getLsbD_and, Anneal.BitVec.getLsbD_lowMask hi]
    unfold Anneal.BitVec.getLsbD
    rw [Anneal.BitVec.toNat_ofNatLT, nat_testBit_mod_two_pow, bool_and_comm]
  have hNat := congrArg BitVec.toNat hEq
  rw [Anneal.BitVec.toNat_ofNatLT] at hNat
  exact hNat

/-- Universal two's-complement identity `~~~(x - 1#w) = -x`. -/
theorem not_sub_one_eq_neg {w : Nat} (x : BitVec w) :
    Anneal.BitVec.not (x - BitVec.ofNat w 1) = Anneal.BitVecArith.neg x := by
  cases w with
  | zero =>
    apply Anneal.BitVec.eq_of_toNat_eq
    have hL : (Anneal.BitVec.not (x - BitVec.ofNat 0 1)).toNat = 0 :=
      Nat.eq_zero_of_le_zero (Nat.le_of_lt_succ
        (Anneal.BitVec.not (x - BitVec.ofNat 0 1)).isLt)
    have hR : (Anneal.BitVecArith.neg x).toNat = 0 :=
      Nat.eq_zero_of_le_zero (Nat.le_of_lt_succ (Anneal.BitVecArith.neg x).isLt)
    rw [hL, hR]
  | succ w' =>
    cases hx : x.toNat with
    | zero =>
      have hx0 : x = BitVec.ofNat (w' + 1) 0 :=
        Anneal.BitVec.eq_of_toNat_eq
          (Eq.trans hx (Eq.symm (Anneal.BitVec.toNat_zero (w' + 1))))
      have h1Lt : 1 < Nat.pow 2 (w' + 1) := by
        rw [nat_pow_succ, Nat.mul_two]
        exact Nat.lt_of_lt_of_le (by decide : 1 < 2)
          (Nat.add_le_add (nat_two_pow_pos w') (nat_two_pow_pos w'))
      have hSubAll1 :
          BitVec.ofNat (w' + 1) 0 - BitVec.ofNat (w' + 1) 1 =
            Anneal.BitVec.allOnes (w' + 1) := by
        apply Anneal.BitVec.eq_of_toNat_eq
        rw [Anneal.BitVec.toNat_sub, Anneal.BitVec.toNat_zero, Nat.add_zero,
          Anneal.BitVec.toNat_ofNat, nat_mod_eq_of_lt h1Lt,
          Anneal.BitVec.toNat_allOnes]
        exact nat_mod_eq_of_lt
          (Nat.sub_lt (nat_two_pow_pos (w' + 1)) Nat.one_pos)
      rw [hx0, hSubAll1, Anneal.BitVec.not_allOnes_eq_zero,
        Anneal.BitVecArith.neg_zero]
    | succ k =>
      have hPos : 0 < x.toNat := by
        rw [hx]
        exact Nat.zero_lt_succ k
      have hxNe0 : x ≠ BitVec.ofNat (w' + 1) 0 := by
        intro hEq
        have hNat := congrArg BitVec.toNat hEq
        rw [Anneal.BitVec.toNat_zero] at hNat
        rw [hNat] at hPos
        nomatch hPos
      apply Anneal.BitVec.eq_of_toNat_eq
      rw [Anneal.BitVecArith.toNat_not_eq_sub, toNat_sub_one_of_ne_zero hxNe0,
        Anneal.BitVecArith.toNat_neg_of_pos hPos, Nat.sub_sub,
        Nat.add_comm 1 (x.toNat - 1), Nat.sub_add_cancel hPos]

private theorem mod_neg_sub_pow_eq {w k : Nat} (hk : k < w) (len : BitVec w)
    (_hPos : 0 < len.toNat) :
    Nat.mod (Nat.pow 2 w - len.toNat) (Nat.pow 2 k) =
      if Nat.mod len.toNat (Nat.pow 2 k) = 0 then
        0
      else
        Nat.pow 2 k - Nat.mod len.toNat (Nat.pow 2 k) := by
  let A := Nat.pow 2 k
  have hAPos : 0 < A := nat_two_pow_pos k
  have hPowSplit : Nat.pow 2 w = A * Nat.pow 2 (w - k) := by
    have hEq : w = k + (w - k) := Eq.symm (Nat.add_sub_of_le (Nat.le_of_lt hk))
    rw [← nat_pow_add, ← hEq]
  have hLenLt : len.toNat < Nat.pow 2 w := len.isLt
  have hSplitLen := nat_div_add_mod len.toNat A
  let q := Nat.div len.toNat A
  cases hr0 : Nat.mod len.toNat A with
  | zero =>
    rw [Anneal.InitLemmas.ite_true_of rfl]
    have hLenEq : len.toNat = A * q := by
      have h1 := hSplitLen
      rw [hr0, Nat.add_zero] at h1
      exact h1.symm
    have hQLe : q ≤ Nat.pow 2 (w - k) := by
      cases Nat.lt_or_ge (Nat.pow 2 (w - k)) q with
      | inr hLe => exact hLe
      | inl hLt =>
        have hBad : Nat.pow 2 w < len.toNat := by
          rw [hPowSplit, hLenEq]
          exact Nat.mul_lt_mul_of_pos_left hLt hAPos
        exact False.elim (Nat.not_lt_of_ge (Nat.le_of_lt hLenLt) hBad)
    have hDiff : Nat.pow 2 w - len.toNat = A * (Nat.pow 2 (w - k) - q) := by
      rw [Nat.mul_sub_left_distrib, hPowSplit, hLenEq]
    rw [hDiff, nat_mul_mod_right]
  | succ r' =>
    let r := r' + 1
    have hNe : r ≠ 0 := fun h => nomatch h
    rw [Anneal.InitLemmas.ite_false_of hNe]
    have hrLt : r < A := by
      have hm := Nat.mod_lt len.toNat hAPos
      change Nat.mod len.toNat A < A at hm
      rw [hr0] at hm
      exact hm
    have hLenEq : len.toNat = A * q + r := by
      have h1 := hSplitLen
      rw [hr0] at h1
      exact h1.symm
    have hQLt : q < Nat.pow 2 (w - k) := by
      cases Nat.lt_or_ge q (Nat.pow 2 (w - k)) with
      | inl hLt => exact hLt
      | inr hGe =>
        have hBad : Nat.pow 2 w ≤ len.toNat := by
          rw [hPowSplit, hLenEq]
          exact Nat.le_trans (Nat.mul_le_mul_left A hGe) (Nat.le_add_right _ r)
        exact False.elim (Nat.not_lt_of_ge hBad hLenLt)
    have hWSub : Nat.pow 2 (w - k) = 1 + ((Nat.pow 2 (w - k) - (q + 1)) + q) := by
      have h1 : q + 1 ≤ Nat.pow 2 (w - k) := hQLt
      have h2 := Nat.sub_add_cancel h1
      rw [Nat.add_comm (Nat.pow 2 (w - k) - (q + 1)) (q + 1),
        Nat.add_assoc, Nat.add_left_comm q 1 (Nat.pow 2 (w - k) - (q + 1)),
        Nat.add_comm q (Nat.pow 2 (w - k) - (q + 1))] at h2
      exact h2.symm
    have hSum :
        Nat.pow 2 w - len.toNat =
          (A - r) + A * (Nat.pow 2 (w - k) - (q + 1)) := by
      have hTarget :
          ((A - r) + A * (Nat.pow 2 (w - k) - (q + 1))) + len.toNat =
            Nat.pow 2 w := by
        rw [hLenEq]
        have hAr : (A - r) + r = A := Nat.sub_add_cancel (Nat.le_of_lt hrLt)
        have hMulF :
            A + (A * (Nat.pow 2 (w - k) - (q + 1)) + A * q) =
              A * Nat.pow 2 (w - k) := by
          have h1 :
              A * 1 + A * ((Nat.pow 2 (w - k) - (q + 1)) + q) =
                A * Nat.pow 2 (w - k) := by
            rw [← Nat.mul_add, ← hWSub]
          rw [Nat.mul_one, Nat.mul_add] at h1
          exact h1
        rw [Nat.add_comm (A * q) r,
          Nat.add_assoc (A - r) (A * (Nat.pow 2 (w - k) - (q + 1))) (r + A * q),
          Nat.add_left_comm (A * (Nat.pow 2 (w - k) - (q + 1))) r (A * q),
          ← Nat.add_assoc (A - r) r, hAr, hMulF, ← hPowSplit]
      have hSub := congrArg (fun z => z - len.toNat) hTarget
      rw [Nat.add_sub_cancel] at hSub
      exact hSub.symm
    rw [hSum, nat_add_mul_mod_self_left]
    exact nat_mod_eq_of_lt (Nat.sub_lt hAPos (Nat.zero_lt_succ r'))

/-- Exact `.toNat` characterization of `paddingFast len align` for any
power-of-two `align : BitVec w`. -/
theorem toNat_paddingFast {w : Nat} {align : BitVec w}
    (hAlign : isPow2BV align) (len : BitVec w) :
    (paddingFast len align).toNat =
      if Nat.mod len.toNat align.toNat = 0 then
        0
      else
        align.toNat - Nat.mod len.toNat align.toNat := by
  let ⟨k, hkw, hPow, _⟩ := isPow2BV_exists_shl hAlign
  unfold paddingFast
  rw [not_sub_one_eq_neg, align_sub_one_eq_lowMask hkw hAlign.1 hPow,
    toNat_and_lowMask_eq_mod hkw, ← hPow]
  cases hLen0 : len.toNat with
  | zero =>
    have hLenZero : len = BitVec.ofNat w 0 :=
      Anneal.BitVec.eq_of_toNat_eq
        (Eq.trans hLen0 (Eq.symm (Anneal.BitVec.toNat_zero w)))
    rw [hLenZero, Anneal.BitVecArith.neg_zero, Anneal.BitVec.toNat_zero,
      nat_zero_mod, Anneal.InitLemmas.ite_true_of rfl]
  | succ l' =>
    have hLenPos : 0 < len.toNat := by
      rw [hLen0]
      exact Nat.zero_lt_succ l'
    rw [Anneal.BitVecArith.toNat_neg_of_pos hLenPos, hPow]
    rw [← hLen0]
    exact mod_neg_sub_pow_eq hkw len hLenPos

/-- Exact `.toNat` characterization of `paddingNaive len align` for any
power-of-two `align : BitVec w`. -/
theorem toNat_paddingNaive {w : Nat} {align : BitVec w}
    (hAlign : isPow2BV align) (len : BitVec w) :
    (paddingNaive len align).toNat =
      if Nat.mod len.toNat align.toNat = 0 then
        0
      else
        align.toNat - Nat.mod len.toNat align.toNat := by
  let ⟨k, hkw, hPow, _⟩ := isPow2BV_exists_shl hAlign
  unfold paddingNaive
  rw [align_sub_one_eq_lowMask hkw hAlign.1 hPow]
  let rem := Anneal.BitVec.and len (Anneal.BitVec.lowMask w k)
  have hRemNat : rem.toNat = Nat.mod len.toNat align.toNat := by
    rw [toNat_and_lowMask_eq_mod hkw, ← hPow]
  have hRemLt : rem ≤ align := by
    change rem.toNat ≤ align.toNat
    rw [hRemNat]
    exact Nat.le_of_lt (Nat.mod_lt len.toNat (isPow2BV_pos hAlign))
  cases hr : Nat.mod len.toNat align.toNat with
  | zero =>
    have hRemEq0 : rem = BitVec.ofNat w 0 :=
      Anneal.BitVec.eq_of_toNat_eq
        (hRemNat.trans (hr.trans (Eq.symm (Anneal.BitVec.toNat_zero w))))
    have hBeq : (rem == BitVec.ofNat w 0) = true := by
      rw [hRemEq0]
      exact beq_self_eq_true (BitVec.ofNat w 0)
    rw [MirWp.ite_bool_true hBeq, Anneal.BitVec.toNat_zero,
      Anneal.InitLemmas.ite_true_of rfl]
  | succ r' =>
    have hNe : Nat.mod len.toNat align.toNat ≠ 0 := by
      rw [hr]
      exact fun h => nomatch h
    have hBeqFalse : (rem == BitVec.ofNat w 0) = false := by
      cases hb : rem == BitVec.ofNat w 0 with
      | false => rfl
      | true =>
        have hEq0 := of_decide_eq_true hb
        have hNat := congrArg BitVec.toNat hEq0
        rw [hRemNat, Anneal.BitVec.toNat_zero] at hNat
        exact False.elim (hNe hNat)
    rw [MirWp.ite_bool_false hBeqFalse,
      Anneal.BitVec.toNat_sub_of_le hRemLt, hRemNat, hr,
      Anneal.InitLemmas.ite_false_of (fun h => nomatch h)]

/-- **Equivalence Theorem:** Zerocopy's branch-free `paddingFast len align`
(`!(len.wrapping_sub(1)) & (align - 1)`) equals `paddingNaive len align` for
all widths `w ≥ 1` and all `len, align : BitVec w` with `isPow2BV align`. -/
theorem paddingFast_eq_paddingNaive {w : Nat} {align : BitVec w}
    (hAlign : isPow2BV align) (len : BitVec w) :
    paddingFast len align = paddingNaive len align :=
  Anneal.BitVec.eq_of_toNat_eq
    ((toNat_paddingFast hAlign len).trans (toNat_paddingNaive hAlign len).symm)

/-- Strict upper bound matching `kani::ensures(|&p| p < align.get())`. -/
theorem toNat_paddingFast_lt {w : Nat} {align : BitVec w}
    (hAlign : isPow2BV align) (len : BitVec w) :
    (paddingFast len align).toNat < align.toNat := by
  have hAPos := isPow2BV_pos hAlign
  rw [toNat_paddingFast hAlign len]
  cases hr : Nat.mod len.toNat align.toNat with
  | zero => rw [Anneal.InitLemmas.ite_true_of rfl]; exact hAPos
  | succ r' =>
    rw [Anneal.InitLemmas.ite_false_of (fun h => nomatch h)]
    exact Nat.sub_lt hAPos (Nat.zero_lt_succ r')

/-- Bitvector strict upper bound `paddingFast len align < align`. -/
theorem paddingFast_lt {w : Nat} {align : BitVec w}
    (hAlign : isPow2BV align) (len : BitVec w) :
    paddingFast len align < align :=
  toNat_paddingFast_lt hAlign len

/-- Exact mathematical modular congruence
`(len.toNat + (paddingFast len align).toNat) % align.toNat = 0`. -/
theorem mod_add_paddingFast_eq_zero {w : Nat} {align : BitVec w}
    (hAlign : isPow2BV align) (len : BitVec w) :
    Nat.mod (len.toNat + (paddingFast len align).toNat) align.toNat = 0 := by
  have hAPos := isPow2BV_pos hAlign
  rw [toNat_paddingFast hAlign len]
  cases hr : Nat.mod len.toNat align.toNat with
  | zero =>
    rw [Anneal.InitLemmas.ite_true_of rfl, Nat.add_zero, hr]
  | succ r' =>
    rw [Anneal.InitLemmas.ite_false_of (fun h => nomatch h)]
    have hrLt : r' + 1 < align.toNat := by
      rw [← hr]
      exact Nat.mod_lt len.toNat hAPos
    have hDivMod := nat_div_add_mod len.toNat align.toNat
    rw [hr] at hDivMod
    have hSum :
        len.toNat + (align.toNat - (r' + 1)) =
          align.toNat * (Nat.div len.toNat align.toNat + 1) := by
      have h1 := congrArg (fun z => z + (align.toNat - (r' + 1))) hDivMod.symm
      rw [Nat.add_assoc, Nat.add_sub_of_le (Nat.le_of_lt hrLt)] at h1
      rw [h1, Nat.mul_add, Nat.mul_one]
    rw [hSum, nat_mul_mod_right]

/-- Wraparound modular congruence matching
`kani::ensures(|&p| len.wrapping_add(p) % align.get() == 0)`: because
`Dvd.dvd align.toNat (2^w)`, bitvector addition preserves divisibility even
when `len.toNat + p.toNat ≥ 2^w`. -/
theorem mod_wrap_add_paddingFast_eq_zero {w : Nat} {align : BitVec w}
    (hAlign : isPow2BV align) (len : BitVec w) :
    Nat.mod (len + paddingFast len align).toNat align.toNat = 0 := by
  let ⟨q, hDvd⟩ := isPow2BV_dvd_two_pow hAlign
  rw [Anneal.BitVec.toNat_add, hDvd, nat_mod_mod_mul_left]
  exact mod_add_paddingFast_eq_zero hAlign len

/-- Uniqueness of `paddingFast len align`: any `p < align` achieving modular
alignment `((len + p).toNat) % align.toNat = 0` must equal `paddingFast len
align`. -/
theorem paddingFast_unique_of_lt_and_wrap_mod {w : Nat} {align len p : BitVec w}
    (hAlign : isPow2BV align) (hpLt : p.toNat < align.toNat)
    (hpMod : Nat.mod (len + p).toNat align.toNat = 0) :
    p = paddingFast len align := by
  let ⟨q, hDvd⟩ := isPow2BV_dvd_two_pow hAlign
  rw [Anneal.BitVec.toNat_add, hDvd, nat_mod_mod_mul_left] at hpMod
  have hModEq :
      Nat.mod (Nat.mod len.toNat align.toNat + p.toNat) align.toNat = 0 := by
    rw [nat_add_mod_cancel_left]
    exact hpMod
  apply Anneal.BitVec.eq_of_toNat_eq
  rw [toNat_paddingFast hAlign len]
  cases hr : Nat.mod len.toNat align.toNat with
  | zero =>
    rw [Anneal.InitLemmas.ite_true_of rfl]
    rw [hr, Nat.zero_add, nat_mod_eq_of_lt hpLt] at hModEq
    exact hModEq
  | succ r' =>
    rw [Anneal.InitLemmas.ite_false_of (fun h => nomatch h)]
    have hrLt : r' + 1 < align.toNat := by
      rw [← hr]
      exact Nat.mod_lt len.toNat (isPow2BV_pos hAlign)
    rw [hr] at hModEq
    have hLt2 : r' + 1 + p.toNat < align.toNat + align.toNat :=
      Nat.add_lt_add hrLt hpLt
    have hGe : align.toNat ≤ r' + 1 + p.toNat := by
      cases Nat.lt_or_ge (r' + 1 + p.toNat) align.toNat with
      | inr h => exact h
      | inl hLt1 =>
        rw [nat_mod_eq_of_lt hLt1, Nat.succ_add] at hModEq
        nomatch hModEq
    have hSubLt : r' + 1 + p.toNat - align.toNat < align.toNat := by
      apply nat_lt_of_add_lt_add_right (c := align.toNat)
      rw [Nat.sub_add_cancel hGe]
      exact hLt2
    have hEqSum :
        r' + 1 + p.toNat = align.toNat * 1 + (r' + 1 + p.toNat - align.toNat) := by
      rw [Nat.mul_one, Nat.add_comm align.toNat, Nat.sub_add_cancel hGe]
    rw [hEqSum, nat_mul_add_mod_self_left, nat_mod_eq_of_lt hSubLt] at hModEq
    have hTot : r' + 1 + p.toNat = align.toNat := by
      have h1 := Nat.sub_add_cancel hGe
      rw [hModEq, Nat.zero_add] at h1
      exact h1.symm
    apply Nat.le_antisymm
    · exact Nat.le_sub_of_add_le
        (by rw [Nat.add_comm p.toNat (r' + 1), hTot]; exact Nat.le_refl _)
    · exact Nat.sub_le_of_le_add
        (by rw [Nat.add_comm p.toNat (r' + 1), hTot]; exact Nat.le_refl _)

/-- Minimality of `paddingFast len align`: any `p : BitVec w` making
`(len + p).toNat % align.toNat = 0` satisfies `paddingFast len align ≤ p`. -/
theorem paddingFast_minimal_of_wrap_mod {w : Nat} {align len p : BitVec w}
    (hAlign : isPow2BV align)
    (hpMod : Nat.mod (len + p).toNat align.toNat = 0) :
    paddingFast len align ≤ p := by
  change (paddingFast len align).toNat ≤ p.toNat
  let A := align.toNat
  have hAPos : 0 < A := isPow2BV_pos hAlign
  let ⟨q, hDvd⟩ := isPow2BV_dvd_two_pow hAlign
  rw [Anneal.BitVec.toNat_add, hDvd, nat_mod_mod_mul_left] at hpMod
  let pRem := BitVec.ofNatLT (Nat.mod p.toNat A)
    (Nat.lt_of_lt_of_le (Nat.mod_lt p.toNat hAPos)
      (Nat.le_of_lt align.isLt))
  have hpRemMod : Nat.mod (len + pRem).toNat A = 0 := by
    rw [Anneal.BitVec.toNat_add, hDvd, nat_mod_mod_mul_left,
      Anneal.BitVec.toNat_ofNatLT, nat_add_mod_cancel_right]
    exact hpMod
  have hpRemEq : pRem = paddingFast len align :=
    paddingFast_unique_of_lt_and_wrap_mod hAlign (Nat.mod_lt p.toNat hAPos)
      hpRemMod
  have hModLe : Nat.mod p.toNat A ≤ p.toNat := Nat.mod_le p.toNat A
  have hRemToNat := congrArg BitVec.toNat hpRemEq
  rw [Anneal.BitVec.toNat_ofNatLT] at hRemToNat
  rw [← hRemToNat]
  exact hModLe

/-! ## 3. Round-Down Bounds, Divisibility, & Maximality (`roundDownFast`) -/

/-- Branch-free fast round-down matching
`round_down_to_next_multiple_of_alignment`: `n & !(align - 1)`. -/
@[expose] def roundDownFast {w : Nat} (n align : BitVec w) : BitVec w :=
  Anneal.BitVec.and n (Anneal.BitVec.not (align - BitVec.ofNat w 1))

private theorem nat_testBit_div_mul_pow (m k i : Nat) :
    (Nat.div m (Nat.pow 2 k) * Nat.pow 2 k).testBit i =
      (decide (k ≤ i) && m.testBit i) := by
  let A := Nat.pow 2 k
  have hAPos : 0 < A := nat_two_pow_pos k
  cases Nat.lt_or_ge i k with
  | inl hlt =>
    rw [decide_eq_false (Nat.not_le_of_gt hlt), Bool.false_and, nat_testBit_eq]
    have hk : k = i + (k - i) := Eq.symm (Nat.add_sub_of_le (Nat.le_of_lt hlt))
    have hkiPos : 0 < k - i := Nat.zero_lt_sub_of_lt hlt
    have hkiEq : k - i = (k - i - 1) + 1 := Eq.symm (Nat.sub_add_cancel hkiPos)
    have hPowK : Nat.pow 2 k = Nat.pow 2 (k - i) * Nat.pow 2 i := by
      have h1 := congrArg (Nat.pow 2) hk
      rw [nat_pow_add, Nat.mul_comm] at h1
      exact h1
    have hPowEven : Nat.pow 2 (k - i) = 2 * Nat.pow 2 (k - i - 1) := by
      have h1 := congrArg (Nat.pow 2) hkiEq
      rw [nat_pow_succ, Nat.mul_comm] at h1
      exact h1
    rw [hPowK, ← Nat.mul_assoc, nat_mul_div_left _ (nat_two_pow_pos i),
      hPowEven, Nat.mul_left_comm, nat_mul_mod_right]
    rfl
  | inr hge =>
    rw [decide_eq_true hge, Bool.true_and, nat_testBit_eq, nat_testBit_eq]
    have hi : i = (i - k) + k := Eq.symm (Nat.sub_add_cancel hge)
    have hPowI : Nat.pow 2 i = Nat.pow 2 (i - k) * Nat.pow 2 k := by
      have h1 := congrArg (Nat.pow 2) hi
      rw [nat_pow_add] at h1
      exact h1
    rw [hPowI, Nat.mul_comm (Nat.pow 2 (i - k)) (Nat.pow 2 k),
      ← nat_div_div_eq_div_mul, Nat.mul_comm (Nat.div m (Nat.pow 2 k)) (Nat.pow 2 k),
      nat_mul_div_right _ hAPos, nat_div_div_eq_div_mul,
      Nat.mul_comm (Nat.pow 2 k) (Nat.pow 2 (i - k))]

/-- Exact `.toNat` characterization of `roundDownFast n align`:
`(roundDownFast n align).toNat = (n.toNat / align.toNat) * align.toNat`. -/
theorem toNat_roundDownFast_eq_div_mul {w : Nat} {align : BitVec w}
    (hAlign : isPow2BV align) (n : BitVec w) :
    (roundDownFast n align).toNat =
      Nat.div n.toNat align.toNat * align.toNat := by
  let ⟨k, hkw, hPow, _⟩ := isPow2BV_exists_shl hAlign
  have hMulLe : Nat.div n.toNat align.toNat * align.toNat ≤ n.toNat :=
    nat_div_mul_le_self n.toNat align.toNat
  have hMulLt : Nat.div n.toNat align.toNat * align.toNat < Nat.pow 2 w :=
    Nat.lt_of_le_of_lt hMulLe n.isLt
  have hEq :
      roundDownFast n align =
        BitVec.ofNatLT (Nat.div n.toNat align.toNat * align.toNat) hMulLt := by
    unfold roundDownFast
    rw [align_sub_one_eq_lowMask hkw hAlign.1 hPow]
    apply Anneal.BitVec.eq_of_getLsbD_eq
    intro i hi
    rw [Anneal.BitVec.getLsbD_and, Anneal.BitVec.getLsbD_not_of_lt _ hi,
      Anneal.BitVec.getLsbD_lowMask hi]
    unfold Anneal.BitVec.getLsbD
    rw [Anneal.BitVec.toNat_ofNatLT, hPow, nat_testBit_div_mul_pow,
      bool_and_comm]
    cases Nat.lt_or_ge i k with
    | inl hlt =>
      rw [decide_eq_true hlt, decide_eq_false (Nat.not_le_of_gt hlt)]
      rfl
    | inr hge =>
      rw [decide_eq_false (Nat.not_lt_of_ge hge), decide_eq_true hge]
      rfl
  have hNat := congrArg BitVec.toNat hEq
  rw [Anneal.BitVec.toNat_ofNatLT] at hNat
  exact hNat

/-- Decomposition `(roundDownFast n align).toNat + n.toNat % align.toNat =
n.toNat`. -/
theorem roundDownFast_add_mod_eq {w : Nat} {align : BitVec w}
    (hAlign : isPow2BV align) (n : BitVec w) :
    (roundDownFast n align).toNat + Nat.mod n.toNat align.toNat = n.toNat := by
  rw [toNat_roundDownFast_eq_div_mul hAlign n, Nat.mul_comm]
  exact nat_div_add_mod n.toNat align.toNat

/-- Upper bound `roundDownFast n align ≤ n` matching `m <= n`. -/
theorem roundDownFast_le {w : Nat} {align : BitVec w}
    (hAlign : isPow2BV align) (n : BitVec w) :
    roundDownFast n align ≤ n := by
  change (roundDownFast n align).toNat ≤ n.toNat
  rw [toNat_roundDownFast_eq_div_mul hAlign n]
  exact nat_div_mul_le_self n.toNat align.toNat

/-- Natural-number upper bound `(roundDownFast n align).toNat ≤ n.toNat`. -/
theorem toNat_roundDownFast_le {w : Nat} {align : BitVec w}
    (hAlign : isPow2BV align) (n : BitVec w) :
    (roundDownFast n align).toNat ≤ n.toNat :=
  roundDownFast_le hAlign n

/-- Divisibility `(roundDownFast n align).toNat % align.toNat = 0`. -/
theorem mod_roundDownFast_eq_zero {w : Nat} {align : BitVec w}
    (hAlign : isPow2BV align) (n : BitVec w) :
    Nat.mod (roundDownFast n align).toNat align.toNat = 0 := by
  rw [toNat_roundDownFast_eq_div_mul hAlign n, Nat.mul_comm]
  exact nat_mul_mod_right align.toNat (Nat.div n.toNat align.toNat)

/-- Strict next-multiple bound `n.toNat < (roundDownFast n align).toNat +
align.toNat`. -/
theorem lt_toNat_roundDownFast_add {w : Nat} {align : BitVec w}
    (hAlign : isPow2BV align) (n : BitVec w) :
    n.toNat < (roundDownFast n align).toNat + align.toNat := by
  rw [← roundDownFast_add_mod_eq hAlign n]
  exact Nat.add_lt_add_left (Nat.mod_lt n.toNat (isPow2BV_pos hAlign)) _

/-- Maximality matching `kani::ensures`: every `m ≤ n` divisible by
`align.toNat` satisfies `m ≤ roundDownFast n align`. -/
theorem roundDownFast_maximal {w : Nat} {align n m : BitVec w}
    (hAlign : isPow2BV align) (hmLe : m ≤ n)
    (hmMod : Nat.mod m.toNat align.toNat = 0) :
    m ≤ roundDownFast n align := by
  change m.toNat ≤ (roundDownFast n align).toNat
  have hDivMod := nat_div_add_mod m.toNat align.toNat
  rw [hmMod, Nat.add_zero] at hDivMod
  have hmEq : m.toNat = Nat.div m.toNat align.toNat * align.toNat := by
    rw [Nat.mul_comm]
    exact hDivMod.symm
  rw [toNat_roundDownFast_eq_div_mul hAlign n, hmEq]
  exact Nat.mul_le_mul_right align.toNat
    (nat_div_le_div_right (show m.toNat ≤ n.toNat from hmLe) align.toNat)

/-- Bitvector next-multiple bound matching Zerocopy's `checked_add(align)`
postcondition: when adding `align` does not overflow `2^w`, `n <
roundDownFast n align + align`. -/
theorem roundDownFast_next_multiple_gt {w : Nat} {align : BitVec w}
    (hAlign : isPow2BV align) (n : BitVec w)
    (hNoOvf : (roundDownFast n align).toNat + align.toNat < Nat.pow 2 w) :
    n < roundDownFast n align + align := by
  change n.toNat < (roundDownFast n align + align).toNat
  rw [Anneal.BitVec.toNat_add, nat_mod_eq_of_lt hNoOvf]
  exact lt_toNat_roundDownFast_add hAlign n

/-! ## 4. Width Specializations (`u32`, `u64`) & `MirSemantics` Bridges -/

/-- Convenience constructor showing `2^k` in width `w` (`k < w`) satisfies
`isPow2BV`. -/
theorem isPow2BV_ofNat_pow {w k : Nat} (hk : k < w) :
    isPow2BV (BitVec.ofNat w (Nat.pow 2 k)) := by
  have hwPos : 0 < w := Nat.lt_of_le_of_lt (Nat.zero_le k) hk
  have h1Lt : 1 < Nat.pow 2 w := by
    have h1 : Nat.pow 2 1 = 2 := by decide
    have hPowGe : Nat.pow 2 1 ≤ Nat.pow 2 w := nat_pow_le_pow_right hwPos
    rw [h1] at hPowGe
    exact Nat.lt_of_lt_of_le (by decide : 1 < 2) hPowGe
  have hEq : BitVec.ofNat w (Nat.pow 2 k) =
      Anneal.BitVec.shl (BitVec.ofNat w 1) k := by
    apply Anneal.BitVec.eq_of_toNat_eq
    rw [Anneal.BitVec.toNat_shl, Anneal.BitVec.toNat_ofNat,
      Anneal.BitVec.toNat_ofNat, nat_mod_eq_of_lt h1Lt, nat_shiftLeft_eq,
      Nat.one_mul]
  rw [hEq]
  exact isPow2BV_of_lt_width hk

/-- Specialized 32-bit `paddingFast` equivalence and alignment specification. -/
theorem paddingFast_spec_u32 {align : BitVec 32} (hAlign : isPow2BV align)
    (len : BitVec 32) :
    paddingFast len align = paddingNaive len align ∧
    (paddingFast len align).toNat < align.toNat ∧
    Nat.mod (len.toNat + (paddingFast len align).toNat) align.toNat = 0 ∧
    Nat.mod (len + paddingFast len align).toNat align.toNat = 0 ∧
    ∀ p : BitVec 32, Nat.mod (len + p).toNat align.toNat = 0 →
      paddingFast len align ≤ p :=
  ⟨paddingFast_eq_paddingNaive hAlign len,
   toNat_paddingFast_lt hAlign len,
   mod_add_paddingFast_eq_zero hAlign len,
   mod_wrap_add_paddingFast_eq_zero hAlign len,
   fun _ hpMod => paddingFast_minimal_of_wrap_mod hAlign hpMod⟩

/-- Specialized 64-bit `paddingFast` equivalence and alignment specification. -/
theorem paddingFast_spec_u64 {align : BitVec 64} (hAlign : isPow2BV align)
    (len : BitVec 64) :
    paddingFast len align = paddingNaive len align ∧
    (paddingFast len align).toNat < align.toNat ∧
    Nat.mod (len.toNat + (paddingFast len align).toNat) align.toNat = 0 ∧
    Nat.mod (len + paddingFast len align).toNat align.toNat = 0 ∧
    ∀ p : BitVec 64, Nat.mod (len + p).toNat align.toNat = 0 →
      paddingFast len align ≤ p :=
  ⟨paddingFast_eq_paddingNaive hAlign len,
   toNat_paddingFast_lt hAlign len,
   mod_add_paddingFast_eq_zero hAlign len,
   mod_wrap_add_paddingFast_eq_zero hAlign len,
   fun _ hpMod => paddingFast_minimal_of_wrap_mod hAlign hpMod⟩

/-- Specialized 32-bit `roundDownFast` bounds, divisibility, and maximality. -/
theorem roundDownFast_spec_u32 {align : BitVec 32} (hAlign : isPow2BV align)
    (n : BitVec 32) :
    roundDownFast n align ≤ n ∧
    Nat.mod (roundDownFast n align).toNat align.toNat = 0 ∧
    n.toNat < (roundDownFast n align).toNat + align.toNat ∧
    ∀ m : BitVec 32, m ≤ n → Nat.mod m.toNat align.toNat = 0 →
      m ≤ roundDownFast n align :=
  ⟨roundDownFast_le hAlign n,
   mod_roundDownFast_eq_zero hAlign n,
   lt_toNat_roundDownFast_add hAlign n,
   fun _ hmLe hmMod => roundDownFast_maximal hAlign hmLe hmMod⟩

/-- Specialized 64-bit `roundDownFast` bounds, divisibility, and maximality. -/
theorem roundDownFast_spec_u64 {align : BitVec 64} (hAlign : isPow2BV align)
    (n : BitVec 64) :
    roundDownFast n align ≤ n ∧
    Nat.mod (roundDownFast n align).toNat align.toNat = 0 ∧
    n.toNat < (roundDownFast n align).toNat + align.toNat ∧
    ∀ m : BitVec 64, m ≤ n → Nat.mod m.toNat align.toNat = 0 →
      m ≤ roundDownFast n align :=
  ⟨roundDownFast_le hAlign n,
   mod_roundDownFast_eq_zero hAlign n,
   lt_toNat_roundDownFast_add hAlign n,
   fun _ hmLe hmMod => roundDownFast_maximal hAlign hmLe hmMod⟩

/-- Canonical `u64` MIR type (`MirTy.int .i64 false`). -/
@[expose] def alignU64Ty : MirTy := .int .i64 false

/-- Embed a `BitVec 64` as a canonical well-formed Profile v1 `u64` `Val`. -/
@[expose] noncomputable def alignU64Val (x : BitVec 64) : Val :=
  .scalar ⟨.i64, false, bvZeroExtend 128 x⟩

/-- Constant `u64` `Operand` from `n : Nat`. -/
@[expose] def alignU64Const (n : Nat) : Operand :=
  .constant ⟨alignU64Ty, .scalar (BitVec.ofNat 128 n)⟩

/-- Every `alignU64Val x` passes `checkVal _ alignU64Ty = true`. -/
theorem checkVal_alignU64Val (x : BitVec 64) :
    checkVal (alignU64Val x) alignU64Ty = true :=
  MirWp.checkVal_scalar_of_toNat_lt (w := .i64) (s := false)
    (x := bvZeroExtend 128 x) (by
      rw [MirWp.bvZeroExtend_128_toNat]
      exact x.isLt)

/-- Canonical 64-bit `usize` MIR type (`MirTy.int .isize false`). -/
@[expose] def alignUsizeTy : MirTy := .int .isize false

/-- Embed a `BitVec 64` as a canonical well-formed Profile v1 64-bit `usize`
`Val`. -/
@[expose] noncomputable def alignUsizeVal (x : BitVec 64) : Val :=
  .scalar ⟨.isize, false, bvZeroExtend 128 x⟩

/-- Constant 64-bit `usize` `Operand` from `n : Nat`. -/
@[expose] def alignUsizeConst (n : Nat) : Operand :=
  .constant ⟨alignUsizeTy, .scalar (BitVec.ofNat 128 n)⟩

/-- Every `alignUsizeVal x` passes `checkVal _ alignUsizeTy = true`. -/
theorem checkVal_alignUsizeVal (x : BitVec 64) :
    checkVal (alignUsizeVal x) alignUsizeTy = true :=
  MirWp.checkVal_scalar_of_toNat_lt (w := .isize) (s := false)
    (x := bvZeroExtend 128 x) (by
      rw [MirWp.bvZeroExtend_128_toNat]
      exact x.isLt)

private theorem evalBinOp_unsigned_sub_align (w : IntWidth) (b₁ b₂ : BitVec 128) :
    evalBinOp .sub (.scalar ⟨w, false, b₁⟩) (.scalar ⟨w, false, b₂⟩) =
      .ok (.scalar ⟨w, false,
        truncateBits w (bvOfInt 128
          (decodeScalar ⟨w, false, b₁⟩ - decodeScalar ⟨w, false, b₂⟩))⟩) := by
  have hGuard : (!(IntWidth.beq w w && (false == false))) = false := by
    rw [IntWidth.beq_iff.mpr rfl]
    rfl
  exact (MirWp.ite_bool_false hGuard).trans
    (MirWp.ite_bool_false (MirWp.and_isUnchecked_false rfl))

private theorem bvOfInt_negSucc (w m : Nat)
    (hm : m < Nat.pow 2 w) :
    bvOfInt w (Int.negSucc m) = BitVec.ofNat w (Nat.pow 2 w - (m + 1)) := by
  have hmMod : Nat.mod m (Nat.pow 2 w) = m := nat_mod_eq_of_lt hm
  have hmSuccLe : Nat.succ m ≤ Nat.pow 2 w := hm
  have hToNat (k : Nat) : (Int.ofNat k).toNat = k := rfl
  have hSubNatNat :
      Int.subNatNat (Nat.pow 2 w) (Nat.succ m) =
        Int.ofNat (Nat.pow 2 w - Nat.succ m) := by
    unfold Int.subNatNat
    rw [Nat.sub_eq_zero_of_le hmSuccLe]
  unfold bvOfInt
  rw [intEmod_negSucc, hmMod, hSubNatNat, hToNat]

private theorem pow128_sub_eq_pow64_sub_add (d : Nat)
    (hdLe : d ≤ Nat.pow 2 64) :
    Nat.pow 2 128 - d =
      (Nat.pow 2 64 - d) + (Nat.pow 2 64 - 1) * Nat.pow 2 64 := by
  have hSum :
      ((Nat.pow 2 64 - d) + (Nat.pow 2 64 - 1) * Nat.pow 2 64) + d =
        Nat.pow 2 128 := by
    rw [Nat.add_right_comm, Nat.sub_add_cancel hdLe]
  have hC := congrArg (fun z => z - d) hSum
  rw [Nat.add_sub_cancel] at hC
  exact hC.symm

private theorem truncateBits_i64_bvOfInt_negSucc (d : Nat) (hdPos : 0 < d)
    (hdLe : d ≤ Nat.pow 2 64) :
    truncateBits .i64 (bvOfInt 128 (Int.negSucc (d - 1))) =
      bvZeroExtend 128
        (BitVec.ofNatLT (Nat.pow 2 64 - d)
          (Nat.sub_lt (nat_two_pow_pos 64) hdPos)) := by
  have hPow64Pos : 0 < Nat.pow 2 64 := nat_two_pow_pos 64
  have hd1Lt128 : d - 1 < Nat.pow 2 128 :=
    Nat.lt_of_le_of_lt (Nat.le_trans (Nat.sub_le d 1) hdLe)
      (by decide : Nat.pow 2 64 < Nat.pow 2 128)
  have hDecomp := pow128_sub_eq_pow64_sub_add d hdLe
  rw [bvOfInt_negSucc 128 (d - 1) hd1Lt128, Nat.sub_add_cancel hdPos,
    MirWp.truncateBits_i64_ofNat]
  apply congrArg (bvZeroExtend 128)
  apply Anneal.BitVec.eq_of_toNat_eq
  rw [Anneal.BitVec.toNat_ofNat, Anneal.BitVec.toNat_ofNatLT, hDecomp]
  change Nat.mod ((Nat.pow 2 64 - d) +
      (Nat.pow 2 64 - 1) * Nat.pow 2 64) (Nat.pow 2 64) =
    Nat.pow 2 64 - d
  rw [Nat.mul_comm (Nat.pow 2 64 - 1) (Nat.pow 2 64),
    nat_add_mul_mod_self_left]
  exact nat_mod_eq_of_lt (Nat.sub_lt hPow64Pos hdPos)

private theorem sub_64_bits_eq (x y : BitVec 64) :
    truncateBits .i64
      (bvOfInt 128
        (decodeScalar ⟨.i64, false, bvZeroExtend 128 x⟩ -
          decodeScalar ⟨.i64, false, bvZeroExtend 128 y⟩)) =
      bvZeroExtend 128 (x - y) := by
  have hDecX :
      decodeScalar ⟨.i64, false, bvZeroExtend 128 x⟩ = Int.ofNat x.toNat := by
    change Int.ofNat (truncateBits .i64 (bvZeroExtend 128 x)).toNat =
      Int.ofNat x.toNat
    rw [MirWp.truncateBits_i64_bvZeroExtend, MirWp.bvZeroExtend_128_toNat]
  have hDecY :
      decodeScalar ⟨.i64, false, bvZeroExtend 128 y⟩ = Int.ofNat y.toNat := by
    change Int.ofNat (truncateBits .i64 (bvZeroExtend 128 y)).toNat =
      Int.ofNat y.toNat
    rw [MirWp.truncateBits_i64_bvZeroExtend, MirWp.bvZeroExtend_128_toNat]
  rw [hDecX, hDecY]
  have hPow64Pos : 0 < Nat.pow 2 64 := nat_two_pow_pos 64
  have hToNat (k : Nat) : (Int.ofNat k).toNat = k := rfl
  cases Nat.lt_or_ge x.toNat y.toNat with
  | inr hGe =>
    have hSubInt : Int.ofNat x.toNat - Int.ofNat y.toNat =
        Int.ofNat (x.toNat - y.toNat) := by
      rw [int_ofNat_sub_ofNat]
      unfold Int.subNatNat
      rw [Nat.sub_eq_zero_of_le hGe]
    have hDiffLt : x.toNat - y.toNat < Nat.pow 2 64 :=
      Nat.lt_of_le_of_lt (Nat.sub_le _ _) x.isLt
    have hMod128 :
        Nat.mod (x.toNat - y.toNat) (Nat.pow 2 128) = x.toNat - y.toNat :=
      nat_mod_eq_of_lt (Nat.lt_trans hDiffLt (by decide))
    rw [hSubInt]
    unfold bvOfInt
    rw [intEmod_ofNat, hToNat, hMod128, MirWp.truncateBits_i64_ofNat]
    apply congrArg (bvZeroExtend 128)
    apply Anneal.BitVec.eq_of_toNat_eq
    rw [Anneal.BitVec.toNat_ofNat, nat_mod_eq_of_lt hDiffLt,
      Anneal.BitVec.toNat_sub_of_le hGe]
  | inl hLt =>
    have hdPos : 0 < y.toNat - x.toNat := Nat.zero_lt_sub_of_lt hLt
    have hdLe : y.toNat - x.toNat ≤ Nat.pow 2 64 :=
      Nat.le_of_lt (Nat.lt_of_le_of_lt (Nat.sub_le _ _) y.isLt)
    have hSubInt : Int.ofNat x.toNat - Int.ofNat y.toNat =
        Int.negSucc (y.toNat - x.toNat - 1) := by
      rw [int_ofNat_sub_ofNat]
      revert hdPos
      cases hd : y.toNat - x.toNat with
      | zero => intro hdPos; cases hdPos
      | succ _ =>
        intro hdPos; unfold Int.subNatNat
        rw [hd]
        rfl
    have hDiff64 :
        x - y =
          BitVec.ofNatLT (Nat.pow 2 64 - (y.toNat - x.toNat))
            (Nat.sub_lt hPow64Pos hdPos) := by
      apply Anneal.BitVec.eq_of_toNat_eq
      rw [Anneal.BitVec.toNat_sub, Anneal.BitVec.toNat_ofNatLT]
      have hEq1 : (Nat.pow 2 64 - y.toNat) + x.toNat =
          Nat.pow 2 64 - (y.toNat - x.toNat) := by
        have h1 : (Nat.pow 2 64 - y.toNat) + x.toNat + (y.toNat - x.toNat) =
            Nat.pow 2 64 := by
          rw [Nat.add_assoc, Nat.add_sub_of_le (Nat.le_of_lt hLt),
            Nat.sub_add_cancel (Nat.le_of_lt y.isLt)]
        have hC := congrArg (fun z => z - (y.toNat - x.toNat)) h1
        rw [Nat.add_sub_cancel] at hC
        exact hC
      rw [hEq1]
      exact nat_mod_eq_of_lt (Nat.sub_lt hPow64Pos hdPos)
    rw [hSubInt, truncateBits_i64_bvOfInt_negSucc (y.toNat - x.toNat) hdPos hdLe,
      hDiff64]

private theorem not_64_bits_eq (x : BitVec 64) :
    truncateBits .i64
      (bvOfInt 128 (intNot (decodeScalar ⟨.i64, false, bvZeroExtend 128 x⟩))) =
      bvZeroExtend 128 (Anneal.BitVec.not x) := by
  have hDec :
      decodeScalar ⟨.i64, false, bvZeroExtend 128 x⟩ = Int.ofNat x.toNat := by
    change Int.ofNat (truncateBits .i64 (bvZeroExtend 128 x)).toNat =
      Int.ofNat x.toNat
    rw [MirWp.truncateBits_i64_bvZeroExtend, MirWp.bvZeroExtend_128_toNat]
  rw [hDec]
  unfold intNot
  have hPow64Pos : 0 < Nat.pow 2 64 := nat_two_pow_pos 64
  have hdPos : 0 < x.toNat + 1 := Nat.zero_lt_succ x.toNat
  have hdLe : x.toNat + 1 ≤ Nat.pow 2 64 := x.isLt
  have hNot64 :
      Anneal.BitVec.not x =
        BitVec.ofNatLT (Nat.pow 2 64 - (x.toNat + 1))
          (Nat.sub_lt hPow64Pos hdPos) := by
    apply Anneal.BitVec.eq_of_toNat_eq
    rw [Anneal.BitVecArith.toNat_not_eq_sub, Anneal.BitVec.toNat_ofNatLT,
      Nat.sub_sub, Nat.add_comm 1 x.toNat]
  have hTr := truncateBits_i64_bvOfInt_negSucc (x.toNat + 1) hdPos hdLe
  change truncateBits .i64 (bvOfInt 128 (Int.negSucc x.toNat)) = _ at hTr
  rw [hTr, hNot64]

private theorem bitAnd_64_bits_eq (x y : BitVec 64) :
    truncateBits .i64
      (bvAnd (truncateBits .i64 (bvZeroExtend 128 x))
        (truncateBits .i64 (bvZeroExtend 128 y))) =
      bvZeroExtend 128 (Anneal.BitVec.and x y) := by
  have h := MirWp.u64BitAnd_sem_eq x y
  injection h with hSv
  injection hSv

/-- Wrapping `u64` `.sub` in `Trusted.MirSemantics.evalBinOp` coincides with
`BitVec 64` subtraction `x - y`. -/
theorem evalBinOp_sub_u64 (x y : BitVec 64) :
    evalBinOp .sub (alignU64Val x) (alignU64Val y) =
      .ok (alignU64Val (x - y)) := by
  unfold alignU64Val
  rw [evalBinOp_unsigned_sub_align]
  exact congrArg (fun b => Except.ok (Val.scalar ⟨.i64, false, b⟩))
    (sub_64_bits_eq x y)

/-- Wrapping 64-bit `usize` `.sub` in `Trusted.MirSemantics.evalBinOp`
coincides with `BitVec 64` subtraction `x - y`. -/
theorem evalBinOp_sub_usize (x y : BitVec 64) :
    evalBinOp .sub (alignUsizeVal x) (alignUsizeVal y) =
      .ok (alignUsizeVal (x - y)) := by
  unfold alignUsizeVal
  rw [evalBinOp_unsigned_sub_align]
  exact congrArg (fun b => Except.ok (Val.scalar ⟨.isize, false, b⟩))
    (sub_64_bits_eq x y)

/-- Bitwise complement `u64` `.not` in `Trusted.MirSemantics.evalUnOp`
coincides with `Anneal.BitVec.not x`. -/
theorem evalUnOp_not_u64 (x : BitVec 64) :
    evalUnOp .not (alignU64Val x) =
      .ok (alignU64Val (Anneal.BitVec.not x)) := by
  unfold evalUnOp alignU64Val truncateScalar
  exact congrArg (fun b => Except.ok (Val.scalar ⟨.i64, false, b⟩))
    (not_64_bits_eq x)

/-- Bitwise complement 64-bit `usize` `.not` in
`Trusted.MirSemantics.evalUnOp` coincides with `Anneal.BitVec.not x`. -/
theorem evalUnOp_not_usize (x : BitVec 64) :
    evalUnOp .not (alignUsizeVal x) =
      .ok (alignUsizeVal (Anneal.BitVec.not x)) := by
  unfold evalUnOp alignUsizeVal truncateScalar
  exact congrArg (fun b => Except.ok (Val.scalar ⟨.isize, false, b⟩))
    (not_64_bits_eq x)

/-- Bitwise AND `u64` `.bitAnd` in `Trusted.MirSemantics.evalBinOp` coincides
with `Anneal.BitVec.and x y`. -/
theorem evalBinOp_bitAnd_u64 (x y : BitVec 64) :
    evalBinOp .bitAnd (alignU64Val x) (alignU64Val y) =
      .ok (alignU64Val (Anneal.BitVec.and x y)) := by
  unfold evalBinOp alignU64Val
  dsimp only
  rw [MirWp.ite_bool_false (rfl : BinOp.bitAnd.isShift = false),
    MirWp.ite_bool_false (rfl : (!(IntWidth.beq .i64 .i64 &&
      (false == false))) = false)]
  exact congrArg (fun b => Except.ok (Val.scalar ⟨.i64, false, b⟩))
    (bitAnd_64_bits_eq x y)

/-- Bitwise AND 64-bit `usize` `.bitAnd` in `Trusted.MirSemantics.evalBinOp`
coincides with `Anneal.BitVec.and x y`. -/
theorem evalBinOp_bitAnd_usize (x y : BitVec 64) :
    evalBinOp .bitAnd (alignUsizeVal x) (alignUsizeVal y) =
      .ok (alignUsizeVal (Anneal.BitVec.and x y)) := by
  unfold evalBinOp alignUsizeVal
  dsimp only
  rw [MirWp.ite_bool_false (rfl : BinOp.bitAnd.isShift = false),
    MirWp.ite_bool_false (rfl : (!(IntWidth.beq .isize .isize &&
      (false == false))) = false)]
  exact congrArg (fun b => Except.ok (Val.scalar ⟨.isize, false, b⟩))
    (bitAnd_64_bits_eq x y)

end Anneal.Core

end
