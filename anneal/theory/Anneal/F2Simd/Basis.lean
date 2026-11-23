-- Copyright 2026 The Fuchsia Authors
--
-- Licensed under a BSD-style license <LICENSE-BSD>, Apache License, Version 2.0
-- <LICENSE-APACHE or https://www.apache.org/licenses/LICENSE-2.0>, or the MIT
-- license <LICENSE-MIT or https://opensource.org/licenses/MIT>, at your option.
-- This file may not be copied, modified, or distributed except according to
-- those terms.

prelude
import Init.NotationExtra
import Init.Data.BitVec.BasicAux
import Init.Data.Nat.Basic
import Init.Data.Nat.Bitwise.Basic
import Init.Data.Nat.Div.Basic
import Init.Data.List.Basic
import Anneal.BitVec

namespace Anneal.F2Simd

open Anneal.BitVec

/-!
# $\mathbb{F}_2$-Linear & Bilinear Basis Evaluators (`Anneal.F2Simd.Basis`)

Foundation-locked (`prelude` + `foundation-lock.json` + `Anneal.BitVec` only,
zero `noncomputable`, zero `omega`, zero `+kernel`) certificate checkers for
$\mathbb{F}_2$-linear, $\mathbb{F}_2$-bilinear, and cone-of-influence sliced
bit-vector transformations:

1. **`IsF2Linear1` / `IsF2Linear2` (`checkF2Linear1_sound`,
   `checkF2Linear2_sound`):** Universal `BitVec w` equivalence (`∀ x, f x = g x`
   and `∀ x y, f x y = g x y`) from `w` (respectively `w1 + w2`) unit-basis
   evaluations reduced by C++ GMP `Nat` equality (`rfl`).
2. **`IsF2Bilinear` (`checkF2Bilinear_sound`):** Universal 2-variable bilinear
   equivalence (`∀ x y, B1 x y = B2 x y`) from `w1 * w2` unit-basis evaluations,
   discharging 64×64 → 128-bit carryless polynomial multiplication identities
   where CDCL SAT bit-blasting stalls on XOR multiplier trees.
3. **Cone-of-influence basis slicing (`HasBitCone`, `hasBitCone_of_check`,
   `hasBitCone_of_range_check`, `hasBitCone_extractLsb`,
   `checkF2ConeLinear_sound`):** Once `HasBitCone` is established (structurally
   via `hasBitCone_extractLsb` or via `hasBitCone_of_range_check`),
   `checkF2ConeLinear_sound` discharges universal equivalence over wide
   registers from `|cone|` in-cone basis evaluations.
4. **Compositional linear circuit AST (`F2Circuit`, `F2Circuit.eval_isLinear`,
   `checkF2CircuitEq_sound`):** Structural `IsF2Linear1` synthesis for circuits
   built from `xor`, `andConst`, `shlConst`, `ushrConst`, `extract`, `concat`,
   and `comp`.
-/

/-! ## 1. Core `BitVec` $\mathbb{F}_2$ Operations and Algebraic Identities -/

/-- Zero `BitVec` of width `w` (`BitVec.ofNat w 0`). -/
def bvZero (w : Nat) : BitVec w :=
  BitVec.ofNat w 0

/-- `k`-th unit-basis `BitVec` of width `w` (`1 <<< k` modulo `2^w`). -/
def bvUnit (w k : Nat) : BitVec w :=
  shl (BitVec.ofNat w 1) k

/-- Fast C++ GMP `Nat.beq` equality test on `BitVec w`. -/
def bvEq {w : Nat} (a b : BitVec w) : Bool :=
  Nat.beq a.toNat b.toNat

/-- Extract `len` bits starting at bit `lo` (`setWidth len (ushr x lo)`, ordered
`(lo, len)` like `BitVec.extractLsb'`), extensionally equal to
`BitVec.extractLsb' lo len x` (`getLsbD_extractLsb`) and definitionally equal
(`rfl`) when `len < w`. -/
def extractLsb {w : Nat} (lo len : Nat) (x : BitVec w) : BitVec len :=
  setWidth len (ushr x lo)

/-- Concatenate high `wHi` bits `hi` above low `wLo` bits `lo` into width
`wHi + wLo`. -/
def concatBv {wHi wLo : Nat} (hi : BitVec wHi) (lo : BitVec wLo) :
    BitVec (wHi + wLo) :=
  or (shl (setWidth (wHi + wLo) hi) wLo) (setWidth (wHi + wLo) lo)

/-- Soundness of `bvEq`: `bvEq a b = true` implies `a = b`. -/
theorem bvEq_eq {w : Nat} {a b : BitVec w} (h : bvEq a b = true) : a = b :=
  eq_of_toNat_eq (Nat.eq_of_beq_eq_true h)

/-- Completeness of `bvEq`: `a = b` implies `bvEq a b = true`. -/
theorem bvEq_of_eq {w : Nat} {a b : BitVec w} (h : a = b) : bvEq a b = true := by
  subst h
  exact Nat.beq_refl a.toNat

private theorem bool_and_true_left {a b : Bool} (h : (a && b) = true) :
    a = true := by
  cases a with
  | false => nomatch h
  | true => rfl

private theorem bool_and_true_right {a b : Bool} (h : (a && b) = true) :
    b = true := by
  cases a with
  | false => nomatch h
  | true => exact h

private theorem one_lt_two_pow_succ (k : Nat) : 1 < Nat.pow 2 (k + 1) := by
  have hps : Nat.pow 2 (k + 1) = Nat.pow 2 k * 2 := Nat.pow_succ 2 k
  rw [hps]
  have hp : 1 ≤ Nat.pow 2 k := Nat.two_pow_pos k
  exact Nat.mul_le_mul_right 2 hp

private theorem nat_testBit_one :
    ∀ i : Nat, (1 : Nat).testBit i = decide (i = 0)
  | 0 => rfl
  | k + 1 => by
    unfold Nat.testBit
    have hsr : Nat.shiftRight 1 (k + 1) = Nat.div 1 (Nat.pow 2 (k + 1)) :=
      Nat.shiftRight_eq_div_pow 1 (k + 1)
    have hd : Nat.div 1 (Nat.pow 2 (k + 1)) = 0 :=
      Nat.div_eq_of_lt (one_lt_two_pow_succ k)
    change (Nat.land 1 (Nat.shiftRight 1 (k + 1)) != 0) = decide (k + 1 = 0)
    rw [hsr, hd]
    rfl

/-- Bit characterization of unit-basis vector `bvUnit w k` at `i < w`. -/
theorem getLsbD_bvUnit {w k i : Nat} (hi : i < w) :
    getLsbD (bvUnit w k) i = decide (i = k) := by
  unfold bvUnit
  rw [getLsbD_shl, decide_eq_true hi, Bool.true_and]
  cases Nat.lt_or_ge i k with
  | inl hlt =>
    rw [decide_eq_false (Nat.not_le_of_gt hlt), Bool.false_and]
    exact Eq.symm (decide_eq_false (Nat.ne_of_lt hlt))
  | inr hge =>
    rw [decide_eq_true hge, Bool.true_and, getLsbD_ofNat, nat_testBit_one]
    have hsub : i - k < w := Nat.lt_of_le_of_lt (Nat.sub_le i k) hi
    rw [decide_eq_true hsub, Bool.true_and]
    cases Nat.eq_or_lt_of_le hge with
    | inl heq =>
      subst heq
      rw [Nat.sub_self, decide_eq_true rfl]
      exact Eq.symm (decide_eq_true rfl)
    | inr hgt =>
      have hpos : 0 < i - k := Nat.zero_lt_sub_of_lt hgt
      rw [decide_eq_false (Nat.ne_of_gt hpos)]
      exact Eq.symm (decide_eq_false (Nat.ne_of_gt hgt))

/-- Bit characterization of `extractLsb lo len x`. -/
theorem getLsbD_extractLsb {w : Nat} (lo len : Nat) (x : BitVec w) (i : Nat) :
    getLsbD (extractLsb lo len x) i = (decide (i < len) && getLsbD x (i + lo)) := by
  unfold extractLsb
  rw [getLsbD_setWidth, getLsbD_ushr]

/-- Shifting a unit-basis vector `bvUnit w k` left by `s` yields
`bvUnit w (k + s)`. -/
theorem shl_bvUnit (w k s : Nat) :
    shl (bvUnit w k) s = bvUnit w (k + s) := by
  apply eq_of_getLsbD_eq
  intro i hi
  rw [getLsbD_shl, decide_eq_true hi, Bool.true_and, getLsbD_bvUnit hi]
  cases Nat.lt_or_ge i s with
  | inl hLt =>
    rw [decide_eq_false (Nat.not_le_of_gt hLt), Bool.false_and]
    have hNe : i ≠ k + s :=
      Nat.ne_of_lt (Nat.lt_of_lt_of_le hLt (Nat.le_add_left s k))
    exact Eq.symm (decide_eq_false hNe)
  | inr hGe =>
    have hSubLt : i - s < w := Nat.lt_of_le_of_lt (Nat.sub_le i s) hi
    rw [decide_eq_true hGe, Bool.true_and, getLsbD_bvUnit hSubLt]
    cases Nat.lt_or_ge (i - s) k with
    | inl hSubLtK =>
      rw [decide_eq_false (Nat.ne_of_lt hSubLtK)]
      have hLtSum : i < k + s := by
        have h1 := Nat.add_lt_add_right hSubLtK s
        rw [Nat.sub_add_cancel hGe] at h1
        exact h1
      exact Eq.symm (decide_eq_false (Nat.ne_of_lt hLtSum))
    | inr hSubGeK =>
      cases Nat.eq_or_lt_of_le hSubGeK with
      | inl hEq =>
        rw [hEq, Nat.sub_add_cancel hGe, decide_eq_true rfl,
          decide_eq_true rfl]
      | inr hGt =>
        rw [decide_eq_false (Nat.ne_of_gt hGt)]
        have hGtSum : k + s < i := by
          have h1 := Nat.add_lt_add_right hGt s
          rw [Nat.sub_add_cancel hGe] at h1
          exact h1
        exact Eq.symm (decide_eq_false (Nat.ne_of_gt hGtSum))

/-- Resizing unit-basis vector `bvUnit w1 k` (`k < w1`) to width `w2` yields
`bvUnit w2 k`. -/
theorem setWidth_bvUnit {w1 w2 k : Nat} (hk : k < w1) :
    setWidth w2 (bvUnit w1 k) = bvUnit w2 k := by
  apply eq_of_getLsbD_eq
  intro i hi
  rw [getLsbD_setWidth, decide_eq_true hi, Bool.true_and, getLsbD_bvUnit hi]
  cases Nat.lt_or_ge i w1 with
  | inl hi1 => exact getLsbD_bvUnit hi1
  | inr hGe =>
    rw [getLsbD_ge (bvUnit w1 k) hGe]
    have hNe : i ≠ k := Nat.ne_of_gt (Nat.lt_of_lt_of_le hk hGe)
    exact Eq.symm (decide_eq_false hNe)

/-- Extracting `[lo, lo + len)` from `bvUnit w k` when `lo ≤ k` and `k < w`
yields `bvUnit len (k - lo)`. -/
theorem extractLsb_bvUnit_lt {w lo len k : Nat}
    (hLo : lo ≤ k) (hW : k < w) :
    extractLsb lo len (bvUnit w k) = bvUnit len (k - lo) := by
  apply eq_of_getLsbD_eq
  intro i hi
  rw [getLsbD_extractLsb, decide_eq_true hi, Bool.true_and, getLsbD_bvUnit hi]
  cases Nat.lt_or_ge (i + lo) w with
  | inl hIn =>
    rw [getLsbD_bvUnit hIn]
    cases Nat.lt_or_ge i (k - lo) with
    | inl hLt =>
      rw [decide_eq_false (Nat.ne_of_lt hLt)]
      have h1 : i + lo < (k - lo) + lo := Nat.add_lt_add_right hLt lo
      rw [Nat.sub_add_cancel hLo] at h1
      exact decide_eq_false (Nat.ne_of_lt h1)
    | inr hGe =>
      cases Nat.eq_or_lt_of_le hGe with
      | inl hEq =>
        rw [← hEq, Nat.sub_add_cancel hLo, decide_eq_true rfl,
          decide_eq_true rfl]
      | inr hGt =>
        rw [decide_eq_false (Nat.ne_of_gt hGt)]
        have h1 : (k - lo) + lo < i + lo := Nat.add_lt_add_right hGt lo
        rw [Nat.sub_add_cancel hLo] at h1
        exact decide_eq_false (Nat.ne_of_gt h1)
  | inr hOut =>
    rw [getLsbD_ge (bvUnit w k) hOut]
    have hNe : i ≠ k - lo := by
      intro hEq
      have h1 : i + lo = k := by rw [hEq, Nat.sub_add_cancel hLo]
      rw [h1] at hOut
      exact Nat.not_lt_of_ge hOut hW
    exact Eq.symm (decide_eq_false hNe)

/-- Extracting `[lo, lo + len)` from an out-of-range unit-basis vector
`bvUnit wIn k` (`k < lo ∨ lo + len ≤ k`) yields `bvZero len`. -/
theorem extractLsb_bvUnit_outside {wIn lo len k : Nat}
    (hkOut : k < lo ∨ lo + len ≤ k) :
    extractLsb lo len (bvUnit wIn k) = bvZero len := by
  apply eq_of_getLsbD_eq
  intro i hi
  rw [getLsbD_extractLsb, decide_eq_true hi, Bool.true_and, bvZero,
    getLsbD_zero]
  cases Nat.lt_or_ge (i + lo) wIn with
  | inr hGe => exact getLsbD_ge (bvUnit wIn k) hGe
  | inl hLt =>
    rw [getLsbD_bvUnit hLt]
    apply decide_eq_false
    intro hEq
    cases hkOut with
    | inl hkLt =>
      have h1 : lo ≤ i + lo := Nat.le_add_left lo i
      rw [hEq] at h1
      exact Nat.not_lt_of_ge h1 hkLt
    | inr hLeK =>
      have h1 : i + lo < len + lo := Nat.add_lt_add_right hi lo
      rw [Nat.add_comm len lo, hEq] at h1
      exact Nat.not_lt_of_ge hLeK h1

/-- Left shift of `bvZero w` is `bvZero w`. -/
theorem shl_bvZero (w k : Nat) : shl (bvZero w) k = bvZero w := by
  apply eq_of_getLsbD_eq
  intro i _
  rw [getLsbD_shl, bvZero, getLsbD_zero, getLsbD_zero, Bool.and_false,
    Bool.and_false]

/-- Logical right shift of `bvZero w` is `bvZero w`. -/
theorem ushr_bvZero (w k : Nat) : ushr (bvZero w) k = bvZero w := by
  apply eq_of_getLsbD_eq
  intro i _
  rw [getLsbD_ushr, bvZero, getLsbD_zero, getLsbD_zero]

/-- `setWidth v` of `bvZero w` is `bvZero v`. -/
theorem setWidth_bvZero (w v : Nat) : setWidth v (bvZero w) = bvZero v := by
  apply eq_of_getLsbD_eq
  intro i _
  unfold bvZero
  rw [getLsbD_setWidth, getLsbD_zero, getLsbD_zero, Bool.and_false]

/-- `extractLsb lo len` of `bvZero w` is `bvZero len`. -/
theorem extractLsb_bvZero (w lo len : Nat) :
    extractLsb lo len (bvZero w) = bvZero len := by
  unfold extractLsb
  rw [ushr_bvZero, setWidth_bvZero]

/-- `concatBv` of two zero bitvectors is `bvZero (wHi + wLo)`. -/
theorem concatBv_bvZero (wHi wLo : Nat) :
    concatBv (bvZero wHi) (bvZero wLo) = bvZero (wHi + wLo) := by
  unfold concatBv
  rw [setWidth_bvZero, setWidth_bvZero, shl_bvZero, bvZero, or_zero]

/-- Right distributivity of `and` over `xor`. -/
theorem and_xor_distrib_right {w : Nat} (a b m : BitVec w) :
    and (xor a b) m = xor (and a m) (and b m) := by
  apply eq_of_getLsbD_eq
  intro i _
  rw [getLsbD_and, getLsbD_xor, getLsbD_xor, getLsbD_and, getLsbD_and]
  cases getLsbD a i <;> cases getLsbD b i <;> cases getLsbD m i <;> rfl

/-- Distributivity of `shl` over `xor`. -/
theorem shl_xor_distrib {w : Nat} (a b : BitVec w) (k : Nat) :
    shl (xor a b) k = xor (shl a k) (shl b k) := by
  apply eq_of_getLsbD_eq
  intro i hi
  rw [getLsbD_shl, getLsbD_xor, getLsbD_xor, getLsbD_shl, getLsbD_shl,
    decide_eq_true hi, Bool.true_and]
  cases decide (k ≤ i) <;>
    cases getLsbD a (i - k) <;>
    cases getLsbD b (i - k) <;> rfl

/-- Distributivity of `ushr` over `xor`. -/
theorem ushr_xor_distrib {w : Nat} (a b : BitVec w) (k : Nat) :
    ushr (xor a b) k = xor (ushr a k) (ushr b k) := by
  apply eq_of_getLsbD_eq
  intro i _
  rw [getLsbD_ushr, getLsbD_xor, getLsbD_xor, getLsbD_ushr, getLsbD_ushr]

/-- Distributivity of `setWidth` over `xor`. -/
theorem setWidth_xor_distrib {w : Nat} (v : Nat) (a b : BitVec w) :
    setWidth v (xor a b) = xor (setWidth v a) (setWidth v b) := by
  apply eq_of_getLsbD_eq
  intro i hi
  rw [getLsbD_setWidth, getLsbD_xor, getLsbD_xor, getLsbD_setWidth,
    getLsbD_setWidth, decide_eq_true hi, Bool.true_and, Bool.true_and,
    Bool.true_and]

/-- Distributivity of `extractLsb` over `xor`. -/
theorem extractLsb_xor_distrib {w : Nat} (lo len : Nat) (a b : BitVec w) :
    extractLsb lo len (xor a b) =
      xor (extractLsb lo len a) (extractLsb lo len b) := by
  unfold extractLsb
  rw [ushr_xor_distrib, setWidth_xor_distrib]

/-- Disjoint OR equals XOR when no bit position is set in both operands. -/
theorem or_eq_xor_of_disjoint {w : Nat} (a b : BitVec w)
    (hDisj : ∀ i, i < w → !(getLsbD a i && getLsbD b i) = true) :
    or a b = xor a b := by
  apply eq_of_getLsbD_eq
  intro i hi
  have hd := hDisj i hi
  rw [getLsbD_or, getLsbD_xor]
  cases ha : getLsbD a i <;> cases hb : getLsbD b i
  · rfl
  · rfl
  · rfl
  · rw [ha, hb] at hd; nomatch hd

/-- Four-term XOR exchange identity
`(p ^^^ q) ^^^ (r ^^^ s) = (p ^^^ r) ^^^ (q ^^^ s)`. -/
theorem xor_four_rearrange {w : Nat} (p q r s : BitVec w) :
    xor (xor p q) (xor r s) = xor (xor p r) (xor q s) := by
  apply eq_of_getLsbD_eq
  intro i _
  rw [getLsbD_xor, getLsbD_xor, getLsbD_xor, getLsbD_xor, getLsbD_xor, getLsbD_xor]
  cases getLsbD p i <;> cases getLsbD q i <;>
    cases getLsbD r i <;> cases getLsbD s i <;> rfl

/-- Six-term XOR exchange identity used by 3-way Karatsuba
linearity and bilinearity proofs. -/
theorem xor_six_rearrange {w : Nat} (a1 a2 b1 b2 c1 c2 : BitVec w) :
    xor (xor (xor a1 a2) (xor b1 b2)) (xor c1 c2) =
      xor (xor (xor a1 b1) c1) (xor (xor a2 b2) c2) := by
  apply eq_of_getLsbD_eq
  intro i _
  repeat rw [getLsbD_xor]
  cases getLsbD a1 i <;> cases getLsbD a2 i <;>
    cases getLsbD b1 i <;> cases getLsbD b2 i <;>
    cases getLsbD c1 i <;> cases getLsbD c2 i <;> rfl

private theorem concatBv_eq_xor {wHi wLo : Nat} (hi : BitVec wHi)
    (lo : BitVec wLo) :
    concatBv hi lo =
      xor (shl (setWidth (wHi + wLo) hi) wLo) (setWidth (wHi + wLo) lo) := by
  unfold concatBv
  apply or_eq_xor_of_disjoint
  intro i hiLt
  rw [getLsbD_shl, getLsbD_setWidth, getLsbD_setWidth, decide_eq_true hiLt,
    Bool.true_and, Bool.true_and]
  cases Nat.lt_or_ge i wLo with
  | inl hLtLo =>
    rw [decide_eq_false (Nat.not_le_of_gt hLtLo), Bool.false_and, Bool.false_and]
    rfl
  | inr hGeLo =>
    rw [getLsbD_ge lo hGeLo, Bool.and_false]
    rfl

/-- Distributivity of `concatBv` over `xor`. -/
theorem concatBv_xor_distrib {wHi wLo : Nat} (a1 a2 : BitVec wHi)
    (b1 b2 : BitVec wLo) :
    concatBv (xor a1 a2) (xor b1 b2) =
      xor (concatBv a1 b1) (concatBv a2 b2) := by
  rw [concatBv_eq_xor, concatBv_eq_xor, concatBv_eq_xor,
    setWidth_xor_distrib, setWidth_xor_distrib, shl_xor_distrib]
  exact xor_four_rearrange _ _ _ _

/-! ## 2. $\mathbb{F}_2$-Linear & Bilinear Structures and Evaluators -/

/-- Witness that `f : BitVec wIn → BitVec wOut` is $\mathbb{F}_2$-linear. -/
structure IsF2Linear1 {wIn wOut : Nat} (f : BitVec wIn → BitVec wOut) : Prop where
  map_zero : f (bvZero wIn) = bvZero wOut
  map_xor  : ∀ a b : BitVec wIn, f (xor a b) = xor (f a) (f b)

/-- Witness that `f : BitVec w1 → BitVec w2 → BitVec wOut` is jointly
$\mathbb{F}_2$-linear on `(BitVec w1 × BitVec w2)`. -/
structure IsF2Linear2 {w1 w2 wOut : Nat}
    (f : BitVec w1 → BitVec w2 → BitVec wOut) : Prop where
  map_zero : f (bvZero w1) (bvZero w2) = bvZero wOut
  map_xor  : ∀ (a1 a2 : BitVec w1) (b1 b2 : BitVec w2),
    f (xor a1 a2) (xor b1 b2) = xor (f a1 b1) (f a2 b2)

/-- Witness that `B : BitVec w1 → BitVec w2 → BitVec wOut` is
$\mathbb{F}_2$-bilinear. -/
structure IsF2Bilinear {w1 w2 wOut : Nat}
    (B : BitVec w1 → BitVec w2 → BitVec wOut) : Prop where
  zero_left  : ∀ y : BitVec w2, B (bvZero w1) y = bvZero wOut
  xor_left   : ∀ (a1 a2 : BitVec w1) (y : BitVec w2),
    B (xor a1 a2) y = xor (B a1 y) (B a2 y)
  zero_right : ∀ x : BitVec w1, B x (bvZero w2) = bvZero wOut
  xor_right  : ∀ (x : BitVec w1) (b1 b2 : BitVec w2),
    B x (xor b1 b2) = xor (B x b1) (B x b2)

/-- Reconstructs the lowest `n` bits of `x : BitVec w` as an $\mathbb{F}_2$ sum
of unit-basis vectors `bvUnit w k` using `@Nat.rec` (zero `._unsafe_rec`). -/
def bvBasisPrefix {w : Nat} (x : BitVec w) (n : Nat) : BitVec w :=
  @Nat.rec (fun _ => BitVec w)
    (bvZero w)
    (fun k prev =>
      match getLsbD x k with
      | false => prev
      | true  => xor prev (bvUnit w k))
    n

/-- Bitwise characterization of `bvBasisPrefix x n` at `i < w`. -/
theorem bvBasisPrefix_getLsbD {w : Nat} (x : BitVec w) :
    ∀ (n i : Nat), i < w →
      getLsbD (bvBasisPrefix x n) i = (decide (i < n) && getLsbD x i)
  | 0, i, _ => by
    change getLsbD (bvZero w) i = (decide (i < 0) && getLsbD x i)
    rw [bvZero, getLsbD_zero, decide_eq_false (Nat.not_lt_zero i),
      Bool.false_and]
  | k + 1, i, hi => by
    change getLsbD
      (match getLsbD x k with
       | false => bvBasisPrefix x k
       | true  => xor (bvBasisPrefix x k) (bvUnit w k)) i =
      (decide (i < k + 1) && getLsbD x i)
    cases hxk : getLsbD x k with
    | false =>
      dsimp only
      rw [bvBasisPrefix_getLsbD x k i hi]
      cases Nat.lt_or_ge i k with
      | inl hlt =>
        rw [decide_eq_true hlt, decide_eq_true (Nat.lt_succ_of_lt hlt)]
      | inr hge =>
        rw [decide_eq_false (Nat.not_lt_of_ge hge), Bool.false_and]
        cases Nat.eq_or_lt_of_le hge with
        | inl heq =>
          subst heq
          rw [hxk, Bool.and_false]
        | inr hgt =>
          rw [decide_eq_false (Nat.not_lt_of_ge (Nat.succ_le_of_lt hgt)),
            Bool.false_and]
    | true =>
      dsimp only
      rw [getLsbD_xor, bvBasisPrefix_getLsbD x k i hi, getLsbD_bvUnit hi]
      cases Nat.lt_or_ge i k with
      | inl hlt =>
        rw [decide_eq_true hlt, decide_eq_true (Nat.lt_succ_of_lt hlt),
          decide_eq_false (Nat.ne_of_lt hlt)]
        cases getLsbD x i <;> rfl
      | inr hge =>
        rw [decide_eq_false (Nat.not_lt_of_ge hge), Bool.false_and]
        cases Nat.eq_or_lt_of_le hge with
        | inl heq =>
          subst heq
          rw [decide_eq_true rfl, decide_eq_true (Nat.lt_succ_self _), hxk]
          rfl
        | inr hgt =>
          rw [decide_eq_false (Nat.ne_of_gt hgt),
            decide_eq_false (Nat.not_lt_of_ge (Nat.succ_le_of_lt hgt))]
          rfl

/-- Full `w`-bit basis expansion equals `x`. -/
theorem bvBasisPrefix_full {w : Nat} (x : BitVec w) :
    bvBasisPrefix x w = x := by
  apply eq_of_getLsbD_eq
  intro i hi
  rw [bvBasisPrefix_getLsbD x w i hi, decide_eq_true hi, Bool.true_and]

/-- Checks `bvEq (f (bvUnit wIn k)) (g (bvUnit wIn k))` for all `k < n` via
`@Nat.rec`. -/
def checkBasis1Aux {wIn wOut : Nat} (f g : BitVec wIn → BitVec wOut)
    (n : Nat) : Bool :=
  @Nat.rec (fun _ => Bool)
    true
    (fun k prev =>
      match prev with
      | false => false
      | true  => bvEq (f (bvUnit wIn k)) (g (bvUnit wIn k)))
    n

private theorem checkBasis1Aux_prefix_eq {wIn wOut : Nat}
    {f g : BitVec wIn → BitVec wOut}
    (hf : IsF2Linear1 f) (hg : IsF2Linear1 g) (x : BitVec wIn) :
    ∀ n : Nat, checkBasis1Aux f g n = true →
      f (bvBasisPrefix x n) = g (bvBasisPrefix x n)
  | 0, _ => by
    change f (bvZero wIn) = g (bvZero wIn)
    rw [hf.map_zero, hg.map_zero]
  | k + 1, hchk => by
    change (match checkBasis1Aux f g k with
      | false => false
      | true  => bvEq (f (bvUnit wIn k)) (g (bvUnit wIn k))) = true at hchk
    cases hprev : checkBasis1Aux f g k with
    | false => rw [hprev] at hchk; nomatch hchk
    | true =>
      rw [hprev] at hchk
      have ih := checkBasis1Aux_prefix_eq hf hg x k hprev
      have hk := bvEq_eq hchk
      change f (match getLsbD x k with
        | false => bvBasisPrefix x k
        | true  => xor (bvBasisPrefix x k) (bvUnit wIn k)) =
        g (match getLsbD x k with
        | false => bvBasisPrefix x k
        | true  => xor (bvBasisPrefix x k) (bvUnit wIn k))
      cases getLsbD x k with
      | false => exact ih
      | true =>
        dsimp only
        rw [hf.map_xor, hg.map_xor, ih, hk]

/-- Unary $\mathbb{F}_2$-linear equivalence checker (`wIn` basis checks). -/
def checkF2Linear1 {wIn wOut : Nat} (f g : BitVec wIn → BitVec wOut) : Bool :=
  checkBasis1Aux f g wIn

/-- Soundness of `checkF2Linear1`: `wIn` unit-basis checks imply universal
`BitVec wIn` equality. -/
theorem checkF2Linear1_sound {wIn wOut : Nat}
    {f g : BitVec wIn → BitVec wOut}
    (hf : IsF2Linear1 f) (hg : IsF2Linear1 g)
    (hcert : checkF2Linear1 f g = true) :
    ∀ x : BitVec wIn, f x = g x := by
  intro x
  rw [← bvBasisPrefix_full x]
  exact checkBasis1Aux_prefix_eq hf hg x wIn hcert

/-- Derives `checkBasis1Aux f g n = true` from a quantified unit-basis proof
`∀ k < n, f (bvUnit wIn k) = g (bvUnit wIn k)`. -/
theorem checkBasis1Aux_of_forall {wIn wOut : Nat}
    {f g : BitVec wIn → BitVec wOut} :
    ∀ n : Nat,
      (∀ k : Nat, k < n → f (bvUnit wIn k) = g (bvUnit wIn k)) →
      checkBasis1Aux f g n = true
  | 0, _ => rfl
  | k + 1, hEq => by
    have ih := checkBasis1Aux_of_forall k
      (fun j hj => hEq j (Nat.lt_succ_of_lt hj))
    change (match checkBasis1Aux f g k with
      | false => false
      | true  => bvEq (f (bvUnit wIn k)) (g (bvUnit wIn k))) = true
    rw [ih]
    exact bvEq_of_eq (hEq k (Nat.lt_succ_self k))

/-- Checks `len` consecutive unary basis vectors `start .. start + len - 1` via
`@Nat.rec` so wide (`128`-bit, `256`-bit) linear checks stay at bounded
recursion depth without `set_option`. -/
def checkLinear1Range {wIn wOut : Nat} (f g : BitVec wIn → BitVec wOut)
    (start len : Nat) : Bool :=
  @Nat.rec (fun _ => Bool)
    true
    (fun k prev =>
      match prev with
      | false => false
      | true  => bvEq (f (bvUnit wIn (start + k))) (g (bvUnit wIn (start + k))))
    len

private theorem checkLinear1Range_append_raw {wIn wOut : Nat}
    {f g : BitVec wIn → BitVec wOut} {start a : Nat}
    (ha : checkLinear1Range f g start a = true) :
    ∀ {b : Nat},
      checkLinear1Range f g (start + a) b = true →
      checkLinear1Range f g start (a + b) = true
  | 0, _ => by
    rw [Nat.add_zero]
    exact ha
  | b + 1, hb => by
    change (match checkLinear1Range f g (start + a) b with
      | false => false
      | true  =>
        bvEq (f (bvUnit wIn (start + a + b)))
          (g (bvUnit wIn (start + a + b)))) = true at hb
    cases hpb : checkLinear1Range f g (start + a) b with
    | false => rw [hpb] at hb; nomatch hb
    | true =>
      rw [hpb] at hb
      have ih := checkLinear1Range_append_raw ha hpb
      rw [Nat.add_succ]
      change (match checkLinear1Range f g start (a + b) with
        | false => false
        | true  =>
          bvEq (f (bvUnit wIn (start + (a + b))))
            (g (bvUnit wIn (start + (a + b))))) = true
      rw [ih, ← Nat.add_assoc start a b]
      exact hb

/-- Concatenates two adjacent `checkLinear1Range` slices `[start, start + a)`
and `[next, next + b)` without lazy-delta unfolding `checkLinear1Range` during
`Nat` index unification. -/
theorem checkLinear1Range_append {wIn wOut : Nat}
    {f g : BitVec wIn → BitVec wOut} {start a b next len : Nat}
    (hNext : start + a = next) (hLen : a + b = len)
    (ha : checkLinear1Range f g start a = true)
    (hb : checkLinear1Range f g next b = true) :
    checkLinear1Range f g start len = true := by
  subst hNext; subst hLen
  exact checkLinear1Range_append_raw ha hb

private theorem checkLinear1Range_zero_eq_aux {wIn wOut : Nat}
    (f g : BitVec wIn → BitVec wOut) :
    ∀ n : Nat, checkLinear1Range f g 0 n = checkBasis1Aux f g n
  | 0 => rfl
  | k + 1 => by
    change (match checkLinear1Range f g 0 k with
      | false => false
      | true  => bvEq (f (bvUnit wIn (0 + k))) (g (bvUnit wIn (0 + k)))) =
      (match checkBasis1Aux f g k with
      | false => false
      | true  => bvEq (f (bvUnit wIn k)) (g (bvUnit wIn k)))
    rw [checkLinear1Range_zero_eq_aux f g k, Nat.zero_add]

/-- Soundness of `checkLinear1Range` over `[0, wIn)`. -/
theorem checkF2Linear1Range_sound {wIn wOut : Nat}
    {f g : BitVec wIn → BitVec wOut}
    (hf : IsF2Linear1 f) (hg : IsF2Linear1 g)
    (hcert : checkLinear1Range f g 0 wIn = true) :
    ∀ x : BitVec wIn, f x = g x := by
  have hFull : checkF2Linear1 f g = true := by
    unfold checkF2Linear1
    rw [← checkLinear1Range_zero_eq_aux f g wIn]
    exact hcert
  exact checkF2Linear1_sound hf hg hFull

/-- Binary jointly $\mathbb{F}_2$-linear equivalence checker (`w1 + w2`
unit-basis checks). -/
def checkF2Linear2 {w1 w2 wOut : Nat}
    (f g : BitVec w1 → BitVec w2 → BitVec wOut) : Bool :=
  checkF2Linear1 (fun x => f x (bvZero w2)) (fun x => g x (bvZero w2)) &&
  checkF2Linear1 (fun y => f (bvZero w1) y) (fun y => g (bvZero w1) y)

/-- Soundness of `checkF2Linear2`: `w1 + w2` unit-basis checks imply universal
2-input equality. -/
theorem checkF2Linear2_sound {w1 w2 wOut : Nat}
    {f g : BitVec w1 → BitVec w2 → BitVec wOut}
    (hf : IsF2Linear2 f) (hg : IsF2Linear2 g)
    (hcert : checkF2Linear2 f g = true) :
    ∀ (x : BitVec w1) (y : BitVec w2), f x y = g x y := by
  intro x y
  have h1 := bool_and_true_left hcert
  have h2 := bool_and_true_right hcert
  have hz1 : xor (bvZero w1) (bvZero w1) = bvZero w1 := xor_zero (bvZero w1)
  have hz2 : xor (bvZero w2) (bvZero w2) = bvZero w2 := xor_zero (bvZero w2)
  have hfL : IsF2Linear1 (fun a => f a (bvZero w2)) :=
    { map_zero := hf.map_zero
      map_xor := fun a1 a2 => by
        have h := hf.map_xor a1 a2 (bvZero w2) (bvZero w2)
        rw [hz2] at h; exact h }
  have hgL : IsF2Linear1 (fun a => g a (bvZero w2)) :=
    { map_zero := hg.map_zero
      map_xor := fun a1 a2 => by
        have h := hg.map_xor a1 a2 (bvZero w2) (bvZero w2)
        rw [hz2] at h; exact h }
  have hfR : IsF2Linear1 (fun b => f (bvZero w1) b) :=
    { map_zero := hf.map_zero
      map_xor := fun b1 b2 => by
        have h := hf.map_xor (bvZero w1) (bvZero w1) b1 b2
        rw [hz1] at h; exact h }
  have hgR : IsF2Linear1 (fun b => g (bvZero w1) b) :=
    { map_zero := hg.map_zero
      map_xor := fun b1 b2 => by
        have h := hg.map_xor (bvZero w1) (bvZero w1) b1 b2
        rw [hz1] at h; exact h }
  have eqX := checkF2Linear1_sound hfL hgL h1 x
  have eqY := checkF2Linear1_sound hfR hgR h2 y
  have hx0 : xor x (bvZero w1) = x := xor_zero x
  have h0y : xor (bvZero w2) y = y := zero_xor y
  have splitF : f x y = xor (f x (bvZero w2)) (f (bvZero w1) y) := by
    have h := hf.map_xor x (bvZero w1) (bvZero w2) y
    rw [hx0, h0y] at h; exact h
  have splitG : g x y = xor (g x (bvZero w2)) (g (bvZero w1) y) := by
    have h := hg.map_xor x (bvZero w1) (bvZero w2) y
    rw [hx0, h0y] at h; exact h
  rw [splitF, splitG, eqX, eqY]

/-- Row helper checking `B1 (bvUnit w1 i)` against `B2 (bvUnit w1 i)` across
`i < n` via `@Nat.rec`. -/
def checkBilinearRows {w1 w2 wOut : Nat}
    (B1 B2 : BitVec w1 → BitVec w2 → BitVec wOut) (n : Nat) : Bool :=
  @Nat.rec (fun _ => Bool)
    true
    (fun i prev =>
      match prev with
      | false => false
      | true  =>
        checkF2Linear1 (fun y => B1 (bvUnit w1 i) y)
          (fun y => B2 (bvUnit w1 i) y))
    n

/-- Two-variable $\mathbb{F}_2$-bilinear equivalence checker (`w1 * w2`
unit-basis checks). -/
def checkF2Bilinear {w1 w2 wOut : Nat}
    (B1 B2 : BitVec w1 → BitVec w2 → BitVec wOut) : Bool :=
  checkBilinearRows B1 B2 w1

private theorem checkBilinearRows_sound_aux {w1 w2 wOut : Nat}
    {B1 B2 : BitVec w1 → BitVec w2 → BitVec wOut}
    (h1 : IsF2Bilinear B1) (h2 : IsF2Bilinear B2) (y : BitVec w2) :
    ∀ n : Nat, checkBilinearRows B1 B2 n = true →
      checkBasis1Aux (fun x => B1 x y) (fun x => B2 x y) n = true
  | 0, _ => rfl
  | i + 1, hchk => by
    change (match checkBilinearRows B1 B2 i with
      | false => false
      | true  =>
        checkF2Linear1 (fun b => B1 (bvUnit w1 i) b)
          (fun b => B2 (bvUnit w1 i) b)) = true at hchk
    cases hp : checkBilinearRows B1 B2 i with
    | false => rw [hp] at hchk; nomatch hchk
    | true =>
      rw [hp] at hchk
      have ih := checkBilinearRows_sound_aux h1 h2 y i hp
      have hB1R : IsF2Linear1 (fun b => B1 (bvUnit w1 i) b) :=
        ⟨h1.zero_right _, h1.xor_right _⟩
      have hB2R : IsF2Linear1 (fun b => B2 (bvUnit w1 i) b) :=
        ⟨h2.zero_right _, h2.xor_right _⟩
      have rowEq := checkF2Linear1_sound hB1R hB2R hchk y
      change (match checkBasis1Aux (fun x => B1 x y) (fun x => B2 x y) i with
        | false => false
        | true  => bvEq (B1 (bvUnit w1 i) y) (B2 (bvUnit w1 i) y)) = true
      rw [ih]
      exact bvEq_of_eq rowEq

/-- Soundness of `checkF2Bilinear`: `w1 * w2` unit-basis checks imply universal
bilinear equivalence `∀ x y, B1 x y = B2 x y`. -/
theorem checkF2Bilinear_sound {w1 w2 wOut : Nat}
    {B1 B2 : BitVec w1 → BitVec w2 → BitVec wOut}
    (h1 : IsF2Bilinear B1) (h2 : IsF2Bilinear B2)
    (hcert : checkF2Bilinear B1 B2 = true) :
    ∀ (x : BitVec w1) (y : BitVec w2), B1 x y = B2 x y := by
  intro x y
  have hL1 : IsF2Linear1 (fun a => B1 a y) :=
    ⟨h1.zero_left y, fun a1 a2 => h1.xor_left a1 a2 y⟩
  have hL2 : IsF2Linear1 (fun a => B2 a y) :=
    ⟨h2.zero_left y, fun a1 a2 => h2.xor_left a1 a2 y⟩
  exact checkF2Linear1_sound hL1 hL2
    (checkBilinearRows_sound_aux h1 h2 y w1 hcert) x

/-- Derives `checkBilinearRows B1 B2 n = true` from a quantified unit-basis
proof `∀ i < n, ∀ j < w2, B1 (bvUnit w1 i) (bvUnit w2 j) = B2 ...`. -/
theorem checkBilinearRows_of_forall {w1 w2 wOut : Nat}
    {B1 B2 : BitVec w1 → BitVec w2 → BitVec wOut} :
    ∀ n : Nat,
      (∀ i j : Nat, i < n → j < w2 →
        B1 (bvUnit w1 i) (bvUnit w2 j) = B2 (bvUnit w1 i) (bvUnit w2 j)) →
      checkBilinearRows B1 B2 n = true
  | 0, _ => rfl
  | i + 1, hEq => by
    have ih := checkBilinearRows_of_forall i
      (fun r c hr hc => hEq r c (Nat.lt_succ_of_lt hr) hc)
    change (match checkBilinearRows B1 B2 i with
      | false => false
      | true  =>
        checkF2Linear1 (fun y => B1 (bvUnit w1 i) y)
          (fun y => B2 (bvUnit w1 i) y)) = true
    rw [ih]
    exact checkBasis1Aux_of_forall w2 (fun j hj => hEq i j (Nat.lt_succ_self i) hj)

/-- Checks `len` consecutive bilinear basis rows `start .. start + len - 1` via
`@Nat.rec` so wide (`64×64`, `128×128`) bilinear certificates decompose into
independent `rfl` lemmas under Lean's default `whnf` heartbeat budget without
`set_option`. -/
def checkBilinearRange {w1 w2 wOut : Nat}
    (B1 B2 : BitVec w1 → BitVec w2 → BitVec wOut) (start len : Nat) : Bool :=
  @Nat.rec (fun _ => Bool)
    true
    (fun k prev =>
      match prev with
      | false => false
      | true  =>
        checkF2Linear1 (fun y => B1 (bvUnit w1 (start + k)) y)
          (fun y => B2 (bvUnit w1 (start + k)) y))
    len

private theorem checkBilinearRange_append_raw {w1 w2 wOut : Nat}
    {B1 B2 : BitVec w1 → BitVec w2 → BitVec wOut} {start a : Nat}
    (ha : checkBilinearRange B1 B2 start a = true) :
    ∀ {b : Nat},
      checkBilinearRange B1 B2 (start + a) b = true →
      checkBilinearRange B1 B2 start (a + b) = true
  | 0, _ => by
    rw [Nat.add_zero]
    exact ha
  | b + 1, hb => by
    change (match checkBilinearRange B1 B2 (start + a) b with
      | false => false
      | true  =>
        checkF2Linear1 (fun y => B1 (bvUnit w1 (start + a + b)) y)
          (fun y => B2 (bvUnit w1 (start + a + b)) y)) = true at hb
    cases hpb : checkBilinearRange B1 B2 (start + a) b with
    | false => rw [hpb] at hb; nomatch hb
    | true =>
      rw [hpb] at hb
      have ih := checkBilinearRange_append_raw ha hpb
      rw [Nat.add_succ]
      change (match checkBilinearRange B1 B2 start (a + b) with
        | false => false
        | true  =>
          checkF2Linear1 (fun y => B1 (bvUnit w1 (start + (a + b))) y)
            (fun y => B2 (bvUnit w1 (start + (a + b))) y)) = true
      rw [ih, ← Nat.add_assoc start a b]
      exact hb

/-- Concatenation lemma combining two adjacent `checkBilinearRange` slices
`[start, start + a)` and `[next, next + b)` without lazy-delta unfolding. -/
theorem checkBilinearRange_append {w1 w2 wOut : Nat}
    {B1 B2 : BitVec w1 → BitVec w2 → BitVec wOut} {start a b next len : Nat}
    (hNext : start + a = next) (hLen : a + b = len)
    (ha : checkBilinearRange B1 B2 start a = true)
    (hb : checkBilinearRange B1 B2 next b = true) :
    checkBilinearRange B1 B2 start len = true := by
  subst hNext; subst hLen
  exact checkBilinearRange_append_raw ha hb

private theorem checkBilinearRange_zero_eq_rows {w1 w2 wOut : Nat}
    (B1 B2 : BitVec w1 → BitVec w2 → BitVec wOut) :
    ∀ n : Nat, checkBilinearRange B1 B2 0 n = checkBilinearRows B1 B2 n
  | 0 => rfl
  | k + 1 => by
    change (match checkBilinearRange B1 B2 0 k with
      | false => false
      | true  =>
        checkF2Linear1 (fun y => B1 (bvUnit w1 (0 + k)) y)
          (fun y => B2 (bvUnit w1 (0 + k)) y)) =
      (match checkBilinearRows B1 B2 k with
      | false => false
      | true  =>
        checkF2Linear1 (fun y => B1 (bvUnit w1 k) y)
          (fun y => B2 (bvUnit w1 k) y))
    rw [checkBilinearRange_zero_eq_rows B1 B2 k, Nat.zero_add]

/-- Soundness of `checkBilinearRange` over `[0, w1)`. -/
theorem checkF2BilinearRange_sound {w1 w2 wOut : Nat}
    {B1 B2 : BitVec w1 → BitVec w2 → BitVec wOut}
    (h1 : IsF2Bilinear B1) (h2 : IsF2Bilinear B2)
    (hcert : checkBilinearRange B1 B2 0 w1 = true) :
    ∀ (x : BitVec w1) (y : BitVec w2), B1 x y = B2 x y := by
  have hRows : checkBilinearRows B1 B2 w1 = true := by
    rw [← checkBilinearRange_zero_eq_rows B1 B2 w1]
    exact hcert
  exact checkF2Bilinear_sound h1 h2 hRows

/-! ## 3. Cone-of-Influence Basis Slicing -/

/-- Decidable `Nat` membership test on `cone : List Nat`. -/
def natInCone (k : Nat) (cone : List Nat) : Bool :=
  cone.foldr (fun c acc => Nat.beq k c || acc) false

/-- Checks that `f (bvUnit wIn k) = g (bvUnit wIn k)` for every `k ∈ cone`. -/
def checkConeBasis1 {wIn wOut : Nat} (cone : List Nat)
    (f g : BitVec wIn → BitVec wOut) : Bool :=
  cone.foldr
    (fun k acc =>
      match acc with
      | false => false
      | true  => bvEq (f (bvUnit wIn k)) (g (bvUnit wIn k)))
    true

/-- Checks that `f (bvUnit wIn k) = 0` for every `k < n` outside `cone`. -/
def checkOutsideConeZeroAux {wIn wOut : Nat} (cone : List Nat)
    (f : BitVec wIn → BitVec wOut) (n : Nat) : Bool :=
  @Nat.rec (fun _ => Bool)
    true
    (fun k prev =>
      match prev with
      | false => false
      | true  =>
        if natInCone k cone then true else bvEq (f (bvUnit wIn k)) (bvZero wOut))
    n

/-- Checks that `f` maps every unit-basis bit outside `cone` in `0 .. wIn - 1`
to `bvZero wOut`. -/
def checkOutsideConeZero {wIn wOut : Nat} (cone : List Nat)
    (f : BitVec wIn → BitVec wOut) : Bool :=
  checkOutsideConeZeroAux cone f wIn

/-- Semantic cone-of-influence witness: `f` is $\mathbb{F}_2$-linear and maps
every unit-basis vector `k < wIn` outside `cone` to `bvZero wOut`. -/
structure HasBitCone {wIn wOut : Nat} (cone : List Nat)
    (f : BitVec wIn → BitVec wOut) : Prop where
  linear : IsF2Linear1 f
  outside_zero : ∀ k : Nat, k < wIn → natInCone k cone = false →
    f (bvUnit wIn k) = bvZero wOut

private theorem checkOutsideConeZeroAux_sound {wIn wOut : Nat}
    {cone : List Nat} {f : BitVec wIn → BitVec wOut} :
    ∀ {n k : Nat}, k < n → checkOutsideConeZeroAux cone f n = true →
      natInCone k cone = false → f (bvUnit wIn k) = bvZero wOut
  | 0, _, hk, _, _ => nomatch hk
  | m + 1, k, hk, hchk, hOut => by
    change (match checkOutsideConeZeroAux cone f m with
      | false => false
      | true  =>
        if natInCone m cone then true
        else bvEq (f (bvUnit wIn m)) (bvZero wOut)) = true at hchk
    cases hp : checkOutsideConeZeroAux cone f m with
    | false => rw [hp] at hchk; nomatch hchk
    | true =>
      rw [hp] at hchk
      cases Nat.lt_or_eq_of_le (Nat.le_of_lt_succ hk) with
      | inl hlt => exact checkOutsideConeZeroAux_sound hlt hp hOut
      | inr heq =>
        subst heq
        rw [hOut] at hchk
        exact bvEq_eq hchk

/-- Constructs `HasBitCone cone f` from `IsF2Linear1 f` and a `rfl`-checked
`checkOutsideConeZero cone f = true` certificate. -/
theorem hasBitCone_of_check {wIn wOut : Nat} (cone : List Nat)
    {f : BitVec wIn → BitVec wOut}
    (hf : IsF2Linear1 f) (hZero : checkOutsideConeZero cone f = true) :
    HasBitCone cone f :=
  { linear := hf
    outside_zero := fun _ hk hOut =>
      checkOutsideConeZeroAux_sound hk hZero hOut }

/-- Checks `len` consecutive basis indices `start .. start + len - 1` outside
`cone` map to `bvZero wOut`. -/
def checkOutsideConeZeroRange {wIn wOut : Nat} (cone : List Nat)
    (f : BitVec wIn → BitVec wOut) (start len : Nat) : Bool :=
  @Nat.rec (fun _ => Bool)
    true
    (fun k prev =>
      match prev with
      | false => false
      | true  =>
        if natInCone (start + k) cone then true
        else bvEq (f (bvUnit wIn (start + k))) (bvZero wOut))
    len

private theorem checkOutsideConeZeroRange_append_raw {wIn wOut : Nat}
    {cone : List Nat} {f : BitVec wIn → BitVec wOut} {start a : Nat}
    (ha : checkOutsideConeZeroRange cone f start a = true) :
    ∀ {b : Nat},
      checkOutsideConeZeroRange cone f (start + a) b = true →
      checkOutsideConeZeroRange cone f start (a + b) = true
  | 0, _ => by
    rw [Nat.add_zero]
    exact ha
  | b + 1, hb => by
    change (match checkOutsideConeZeroRange cone f (start + a) b with
      | false => false
      | true  =>
        if natInCone (start + a + b) cone then true
        else bvEq (f (bvUnit wIn (start + a + b))) (bvZero wOut)) = true at hb
    cases hpb : checkOutsideConeZeroRange cone f (start + a) b with
    | false => rw [hpb] at hb; nomatch hb
    | true =>
      rw [hpb] at hb
      have ih := checkOutsideConeZeroRange_append_raw ha hpb
      rw [Nat.add_succ]
      change (match checkOutsideConeZeroRange cone f start (a + b) with
        | false => false
        | true  =>
          if natInCone (start + (a + b)) cone then true
          else bvEq (f (bvUnit wIn (start + (a + b)))) (bvZero wOut)) = true
      rw [ih, ← Nat.add_assoc start a b]
      exact hb

/-- Concatenates two adjacent `checkOutsideConeZeroRange` slices without
lazy-delta unfolding. -/
theorem checkOutsideConeZeroRange_append {wIn wOut : Nat} {cone : List Nat}
    {f : BitVec wIn → BitVec wOut} {start a b next len : Nat}
    (hNext : start + a = next) (hLen : a + b = len)
    (ha : checkOutsideConeZeroRange cone f start a = true)
    (hb : checkOutsideConeZeroRange cone f next b = true) :
    checkOutsideConeZeroRange cone f start len = true := by
  subst hNext; subst hLen
  exact checkOutsideConeZeroRange_append_raw ha hb

private theorem checkOutsideConeZeroRange_zero_eq {wIn wOut : Nat}
    (cone : List Nat) (f : BitVec wIn → BitVec wOut) :
    ∀ n : Nat,
      checkOutsideConeZeroRange cone f 0 n = checkOutsideConeZeroAux cone f n
  | 0 => rfl
  | k + 1 => by
    change (match checkOutsideConeZeroRange cone f 0 k with
      | false => false
      | true  =>
        if natInCone (0 + k) cone then true
        else bvEq (f (bvUnit wIn (0 + k))) (bvZero wOut)) =
      (match checkOutsideConeZeroAux cone f k with
      | false => false
      | true  =>
        if natInCone k cone then true
        else bvEq (f (bvUnit wIn k)) (bvZero wOut))
    rw [checkOutsideConeZeroRange_zero_eq cone f k, Nat.zero_add]

/-- Constructs `HasBitCone cone f` from
`checkOutsideConeZeroRange cone f 0 wIn`. -/
theorem hasBitCone_of_range_check {wIn wOut : Nat} (cone : List Nat)
    {f : BitVec wIn → BitVec wOut}
    (hf : IsF2Linear1 f)
    (hZero : checkOutsideConeZeroRange cone f 0 wIn = true) :
    HasBitCone cone f := by
  have hFull : checkOutsideConeZero cone f = true := by
    unfold checkOutsideConeZero
    rw [← checkOutsideConeZeroRange_zero_eq cone f wIn]
    exact hZero
  exact hasBitCone_of_check cone hf hFull

private theorem checkConeBasis1_mem {wIn wOut : Nat} {k : Nat}
    {f g : BitVec wIn → BitVec wOut} :
    ∀ {cone : List Nat}, natInCone k cone = true →
      checkConeBasis1 cone f g = true →
      f (bvUnit wIn k) = g (bvUnit wIn k)
  | [], hIn, _ => nomatch hIn
  | c :: cs, hIn, hChk => by
    unfold checkConeBasis1 at hChk
    dsimp only [List.foldr] at hChk
    cases hTail : checkConeBasis1 cs f g with
    | false =>
      unfold checkConeBasis1 at hTail
      rw [hTail] at hChk
      nomatch hChk
    | true =>
      have hTailRaw :
          List.foldr
            (fun j acc =>
              match acc with
              | false => false
              | true => bvEq (f (bvUnit wIn j)) (g (bvUnit wIn j)))
            true cs = true := hTail
      rw [hTailRaw] at hChk
      unfold natInCone at hIn
      dsimp only [List.foldr] at hIn
      cases hEq : Nat.beq k c with
      | true =>
        have hkc := Nat.eq_of_beq_eq_true hEq
        subst hkc
        exact bvEq_eq hChk
      | false =>
        rw [hEq, Bool.false_or] at hIn
        exact checkConeBasis1_mem hIn hTail

private theorem cone_implies_checkBasis1Aux {wIn wOut : Nat}
    {cone : List Nat} {f g : BitVec wIn → BitVec wOut}
    (hf : HasBitCone cone f) (hg : HasBitCone cone g)
    (hCone : checkConeBasis1 cone f g = true) :
    ∀ n : Nat, n ≤ wIn → checkBasis1Aux f g n = true
  | 0, _ => rfl
  | k + 1, hle => by
    have hkLt : k < wIn := hle
    have ih := cone_implies_checkBasis1Aux hf hg hCone k (Nat.le_of_lt hkLt)
    change (match checkBasis1Aux f g k with
      | false => false
      | true  => bvEq (f (bvUnit wIn k)) (g (bvUnit wIn k))) = true
    rw [ih]
    cases hIn : natInCone k cone with
    | true =>
      exact bvEq_of_eq (checkConeBasis1_mem hIn hCone)
    | false =>
      rw [hf.outside_zero k hkLt hIn, hg.outside_zero k hkLt hIn]
      exact bvEq_of_eq rfl

/-- Cone-of-influence soundness: if `f` and `g` have bit-cone `cone`, then
`|cone|` unit-basis checks on `cone` suffice to prove `∀ x, f x = g x`. -/
theorem checkF2ConeLinear_sound {wIn wOut : Nat} (cone : List Nat)
    {f g : BitVec wIn → BitVec wOut}
    (hf : HasBitCone cone f) (hg : HasBitCone cone g)
    (hCone : checkConeBasis1 cone f g = true) :
    ∀ x : BitVec wIn, f x = g x :=
  checkF2Linear1_sound hf.linear hg.linear
    (cone_implies_checkBasis1Aux hf hg hCone wIn (Nat.le_refl wIn))

/-- Checks via `@Nat.rec` that every index `k < n` outside `cone` lies
outside `[lo, lo + len)`. -/
def checkConeContainsRange (cone : List Nat) (lo len n : Nat) : Bool :=
  @Nat.rec (fun _ => Bool)
    true
    (fun k prev =>
      match prev with
      | false => false
      | true  =>
        if natInCone k cone then true
        else Nat.ble (k + 1) lo || Nat.ble (lo + len) k)
    n

private theorem checkConeContainsRange_sound {cone : List Nat} {lo len : Nat} :
    ∀ {n k : Nat}, k < n → checkConeContainsRange cone lo len n = true →
      natInCone k cone = false → k < lo ∨ lo + len ≤ k
  | 0, _, hk, _, _ => nomatch hk
  | m + 1, k, hk, hchk, hOut => by
    change (match checkConeContainsRange cone lo len m with
      | false => false
      | true  =>
        if natInCone m cone then true
        else Nat.ble (m + 1) lo || Nat.ble (lo + len) m) = true at hchk
    cases hp : checkConeContainsRange cone lo len m with
    | false => rw [hp] at hchk; nomatch hchk
    | true =>
      rw [hp] at hchk
      cases Nat.lt_or_eq_of_le (Nat.le_of_lt_succ hk) with
      | inl hlt => exact checkConeContainsRange_sound hlt hp hOut
      | inr heq =>
        subst heq
        rw [hOut] at hchk
        cases hLtLo : Nat.ble (k + 1) lo with
        | true => exact Or.inl (Nat.le_of_ble_eq_true hLtLo)
        | false =>
          rw [hLtLo, Bool.false_or] at hchk
          exact Or.inr (Nat.le_of_ble_eq_true hchk)

/-- Any `IsF2Linear1` function composed with `extractLsb lo len` has bit-cone
`cone` whenever `checkConeContainsRange cone lo len wIn = true`. -/
theorem hasBitCone_extractLsb {wIn lo len wOut : Nat} (cone : List Nat)
    {h : BitVec len → BitVec wOut} (hh : IsF2Linear1 h)
    (hCov : checkConeContainsRange cone lo len wIn = true) :
    HasBitCone cone (fun v : BitVec wIn => h (extractLsb lo len v)) where
  linear :=
    { map_zero := by
        rw [extractLsb_bvZero, hh.map_zero]
      map_xor := fun a b => by
        rw [extractLsb_xor_distrib, hh.map_xor] }
  outside_zero := fun k hk hOut => by
    rw [extractLsb_bvUnit_outside (checkConeContainsRange_sound hk hCov hOut),
      hh.map_zero]

/-! ## 4. Compositional $\mathbb{F}_2$-Linear Circuit Combinators -/

/-- Deeply embedded compositional AST of $\mathbb{F}_2$-linear bit-vector
circuits `F2Circuit d wIn wOut` carrying structural fuel bound `d` so
`F2Circuit.eval` compiles via `@Nat.rec` (`0` `._unsafe_rec`, `0`
`noncomputable`) with automatic `IsF2Linear1` synthesis. -/
inductive F2Circuit : Nat → Nat → Nat → Type where
  | id        {w : Nat} : F2Circuit 0 w w
  | zero      {wIn wOut : Nat} : F2Circuit 0 wIn wOut
  | xor       {d1 d2 wIn wOut : Nat} :
      F2Circuit d1 wIn wOut → F2Circuit d2 wIn wOut →
      F2Circuit (d1 + d2 + 1) wIn wOut
  | andConst  {d wIn wOut : Nat} :
      F2Circuit d wIn wOut → BitVec wOut → F2Circuit (d + 1) wIn wOut
  | shlConst  {d wIn wOut : Nat} :
      F2Circuit d wIn wOut → Nat → F2Circuit (d + 1) wIn wOut
  | ushrConst {d wIn wOut : Nat} :
      F2Circuit d wIn wOut → Nat → F2Circuit (d + 1) wIn wOut
  | extract   {d wIn wMid : Nat} (lo len : Nat) :
      F2Circuit d wIn wMid → F2Circuit (d + 1) wIn len
  | concat    {d1 d2 wIn wHi wLo : Nat} :
      F2Circuit d1 wIn wHi → F2Circuit d2 wIn wLo →
      F2Circuit (d1 + d2 + 1) wIn (wHi + wLo)
  | comp      {d2 d1 w1 w2 w3 : Nat} :
      F2Circuit d2 w2 w3 → F2Circuit d1 w1 w2 →
      F2Circuit (d2 + d1 + 1) w1 w3

private def withStrictBv {w : Nat} {α : Type} (v : BitVec w)
    (k : BitVec w → α) : α :=
  match v with
  | .ofFin ⟨n, h⟩ =>
    @Nat.casesOn (fun t => t < Nat.pow 2 w → α) n
      (fun h0 => k (.ofFin ⟨0, h0⟩))
      (fun p hp => k (.ofFin ⟨Nat.succ p, hp⟩))
      h

private theorem withStrictBv_eq {w : Nat} {α : Type} (v : BitVec w)
    (k : BitVec w → α) : withStrictBv v k = k v := by
  cases v with
  | ofFin f =>
    cases f with
    | mk n h =>
      cases n <;> rfl

private def f2CircuitEvalStep
    (rec : ∀ {d wIn wOut : Nat},
      F2Circuit d wIn wOut → BitVec wIn → BitVec wOut)
    {d wIn wOut : Nat} (c : F2Circuit d wIn wOut) (x : BitVec wIn) :
    BitVec wOut :=
  match c with
  | .id => x
  | .zero => bvZero wOut
  | .xor c1 c2 => Anneal.BitVec.xor (rec c1 x) (rec c2 x)
  | .andConst c1 m => Anneal.BitVec.and (rec c1 x) m
  | .shlConst c1 k => Anneal.BitVec.shl (rec c1 x) k
  | .ushrConst c1 k => Anneal.BitVec.ushr (rec c1 x) k
  | .extract lo len c1 => extractLsb lo len (rec c1 x)
  | .concat cHi cLo => concatBv (rec cHi x) (rec cLo x)
  | .comp c2 c1 => withStrictBv (rec c1 x) (fun mid => rec c2 mid)

/-- Evaluates an `F2Circuit` under `fuel` steps via `@Nat.rec` (`0`
`._unsafe_rec`, `0` `noncomputable`). -/
def F2Circuit.evalAt (fuel : Nat) :
    ∀ {d wIn wOut : Nat}, F2Circuit d wIn wOut → BitVec wIn → BitVec wOut :=
  @Nat.rec
    (fun _ =>
      ∀ {d wIn wOut : Nat}, F2Circuit d wIn wOut → BitVec wIn → BitVec wOut)
    (fun {_ _ wOut} _ _ => bvZero wOut)
    (fun _ ih {_ _ _} c x => f2CircuitEvalStep ih c x)
    fuel

private theorem f2Circuit_evalAt_succ (fuel : Nat) {d wIn wOut : Nat}
    (c : F2Circuit d wIn wOut) (x : BitVec wIn) :
    F2Circuit.evalAt (fuel + 1) c x =
      f2CircuitEvalStep (F2Circuit.evalAt fuel) c x := rfl

/-- Total denotational evaluation of `c : F2Circuit d wIn wOut` at its exact
structural fuel bound `d + 1`. -/
def F2Circuit.eval {d wIn wOut : Nat} (c : F2Circuit d wIn wOut) :
    BitVec wIn → BitVec wOut :=
  F2Circuit.evalAt (d + 1) c

private theorem f2Circuit_lt_left {d1 d2 k : Nat}
    (h : d1 + d2 + 1 < k + 1) : d1 < k :=
  Nat.lt_of_le_of_lt (Nat.le_add_right d1 d2) (Nat.lt_of_succ_lt_succ h)

private theorem f2Circuit_lt_right {d1 d2 k : Nat}
    (h : d1 + d2 + 1 < k + 1) : d2 < k :=
  Nat.lt_of_le_of_lt (Nat.le_add_left d2 d1) (Nat.lt_of_succ_lt_succ h)

private theorem evalAt_stabilize :
    ∀ {d wIn wOut : Nat} (c : F2Circuit d wIn wOut) {f1 f2 : Nat},
      d < f1 → d < f2 → ∀ x : BitVec wIn,
      F2Circuit.evalAt f1 c x = F2Circuit.evalAt f2 c x
  | _, _, _, .id, 0, _, h1, _, _ => nomatch h1
  | _, _, _, .id, _ + 1, 0, _, h2, _ => nomatch h2
  | _, _, _, .id, _ + 1, _ + 1, _, _, _ => rfl
  | _, _, _, .zero, 0, _, h1, _, _ => nomatch h1
  | _, _, _, .zero, _ + 1, 0, _, h2, _ => nomatch h2
  | _, _, _, .zero, _ + 1, _ + 1, _, _, _ => rfl
  | _, _, _, .xor c1 c2, 0, _, h1, _, _ => nomatch h1
  | _, _, _, .xor c1 c2, _ + 1, 0, _, h2, _ => nomatch h2
  | _, _, _, .xor c1 c2, k1 + 1, k2 + 1, h1, h2, x => by
    rw [f2Circuit_evalAt_succ, f2Circuit_evalAt_succ]
    dsimp only [f2CircuitEvalStep]
    rw [evalAt_stabilize c1 (f2Circuit_lt_left h1) (f2Circuit_lt_left h2) x,
        evalAt_stabilize c2 (f2Circuit_lt_right h1) (f2Circuit_lt_right h2) x]
  | _, _, _, .andConst c1 m, 0, _, h1, _, _ => nomatch h1
  | _, _, _, .andConst c1 m, _ + 1, 0, _, h2, _ => nomatch h2
  | _, _, _, .andConst c1 m, k1 + 1, k2 + 1, h1, h2, x => by
    rw [f2Circuit_evalAt_succ, f2Circuit_evalAt_succ]
    dsimp only [f2CircuitEvalStep]
    rw [evalAt_stabilize c1 (Nat.lt_of_succ_lt_succ h1)
        (Nat.lt_of_succ_lt_succ h2) x]
  | _, _, _, .shlConst c1 s, 0, _, h1, _, _ => nomatch h1
  | _, _, _, .shlConst c1 s, _ + 1, 0, _, h2, _ => nomatch h2
  | _, _, _, .shlConst c1 s, k1 + 1, k2 + 1, h1, h2, x => by
    rw [f2Circuit_evalAt_succ, f2Circuit_evalAt_succ]
    dsimp only [f2CircuitEvalStep]
    rw [evalAt_stabilize c1 (Nat.lt_of_succ_lt_succ h1)
        (Nat.lt_of_succ_lt_succ h2) x]
  | _, _, _, .ushrConst c1 s, 0, _, h1, _, _ => nomatch h1
  | _, _, _, .ushrConst c1 s, _ + 1, 0, _, h2, _ => nomatch h2
  | _, _, _, .ushrConst c1 s, k1 + 1, k2 + 1, h1, h2, x => by
    rw [f2Circuit_evalAt_succ, f2Circuit_evalAt_succ]
    dsimp only [f2CircuitEvalStep]
    rw [evalAt_stabilize c1 (Nat.lt_of_succ_lt_succ h1)
        (Nat.lt_of_succ_lt_succ h2) x]
  | _, _, _, .extract lo len c1, 0, _, h1, _, _ => nomatch h1
  | _, _, _, .extract lo len c1, _ + 1, 0, _, h2, _ => nomatch h2
  | _, _, _, .extract lo len c1, k1 + 1, k2 + 1, h1, h2, x => by
    rw [f2Circuit_evalAt_succ, f2Circuit_evalAt_succ]
    dsimp only [f2CircuitEvalStep]
    rw [evalAt_stabilize c1 (Nat.lt_of_succ_lt_succ h1)
        (Nat.lt_of_succ_lt_succ h2) x]
  | _, _, _, .concat cHi cLo, 0, _, h1, _, _ => nomatch h1
  | _, _, _, .concat cHi cLo, _ + 1, 0, _, h2, _ => nomatch h2
  | _, _, _, .concat cHi cLo, k1 + 1, k2 + 1, h1, h2, x => by
    rw [f2Circuit_evalAt_succ, f2Circuit_evalAt_succ]
    dsimp only [f2CircuitEvalStep]
    rw [evalAt_stabilize cHi (f2Circuit_lt_left h1) (f2Circuit_lt_left h2) x,
        evalAt_stabilize cLo (f2Circuit_lt_right h1) (f2Circuit_lt_right h2) x]
  | _, _, _, .comp c2 c1, 0, _, h1, _, _ => nomatch h1
  | _, _, _, .comp c2 c1, _ + 1, 0, _, h2, _ => nomatch h2
  | _, _, _, .comp c2 c1, k1 + 1, k2 + 1, h1, h2, x => by
    rw [f2Circuit_evalAt_succ, f2Circuit_evalAt_succ]
    dsimp only [f2CircuitEvalStep]
    rw [withStrictBv_eq, withStrictBv_eq,
        evalAt_stabilize c1 (f2Circuit_lt_right h1) (f2Circuit_lt_right h2) x,
        evalAt_stabilize c2 (f2Circuit_lt_left h1) (f2Circuit_lt_left h2) _]

/-- Fuel adequacy: every `fuel > d` evaluates `c : F2Circuit d wIn wOut`
identically to `c.eval` (never hitting zero-fuel truncation). -/
theorem F2Circuit.evalAt_eq_eval {d wIn wOut : Nat}
    (c : F2Circuit d wIn wOut) {fuel : Nat} (h : d < fuel)
    (x : BitVec wIn) :
    F2Circuit.evalAt fuel c x = c.eval x :=
  evalAt_stabilize c h (Nat.lt_succ_self d) x

/-- Compositional denotation of `F2Circuit.comp`: `(c2.comp c1).eval x =
c2.eval (c1.eval x)`. -/
theorem F2Circuit.eval_comp {d2 d1 w1 w2 w3 : Nat}
    (c2 : F2Circuit d2 w2 w3) (c1 : F2Circuit d1 w1 w2) (x : BitVec w1) :
    (F2Circuit.comp c2 c1).eval x = c2.eval (c1.eval x) := by
  dsimp only [F2Circuit.eval]
  rw [f2Circuit_evalAt_succ]
  dsimp only [f2CircuitEvalStep]
  rw [withStrictBv_eq]
  have h1 : d1 < d2 + d1 + 1 :=
    Nat.lt_succ_of_le (Nat.le_add_left d1 d2)
  have h2 : d2 < d2 + d1 + 1 :=
    Nat.lt_succ_of_le (Nat.le_add_right d2 d1)
  rw [F2Circuit.evalAt_eq_eval c1 h1 x,
      F2Circuit.evalAt_eq_eval c2 h2 (c1.eval x)]
  rfl

private theorem evalAt_isLinear :
    ∀ (fuel : Nat) {d wIn wOut : Nat} (c : F2Circuit d wIn wOut),
      IsF2Linear1 (F2Circuit.evalAt fuel c)
  | 0, _, _, wO, _ =>
    { map_zero := rfl
      map_xor := fun _ _ => Eq.symm (xor_zero (bvZero wO)) }
  | fuel + 1, _, _, _, .id =>
    { map_zero := rfl, map_xor := fun _ _ => rfl }
  | fuel + 1, _, _, wO, .zero =>
    { map_zero := rfl
      map_xor := fun _ _ => Eq.symm (xor_zero (bvZero wO)) }
  | fuel + 1, _, _, _, .xor c1 c2 =>
    let h1 := evalAt_isLinear fuel c1
    let h2 := evalAt_isLinear fuel c2
    { map_zero := by
        rw [f2Circuit_evalAt_succ]
        dsimp only [f2CircuitEvalStep]
        rw [h1.map_zero, h2.map_zero, bvZero, xor_zero]
      map_xor := fun a b => by
        rw [f2Circuit_evalAt_succ, f2Circuit_evalAt_succ, f2Circuit_evalAt_succ]
        dsimp only [f2CircuitEvalStep]
        rw [h1.map_xor, h2.map_xor]
        exact xor_four_rearrange _ _ _ _ }
  | fuel + 1, _, _, _, .andConst c1 m =>
    let h1 := evalAt_isLinear fuel c1
    { map_zero := by
        rw [f2Circuit_evalAt_succ]
        dsimp only [f2CircuitEvalStep]
        rw [h1.map_zero, bvZero, zero_and]
      map_xor := fun a b => by
        rw [f2Circuit_evalAt_succ, f2Circuit_evalAt_succ, f2Circuit_evalAt_succ]
        dsimp only [f2CircuitEvalStep]
        rw [h1.map_xor, and_xor_distrib_right] }
  | fuel + 1, _, _, _, .shlConst c1 k =>
    let h1 := evalAt_isLinear fuel c1
    { map_zero := by
        rw [f2Circuit_evalAt_succ]
        dsimp only [f2CircuitEvalStep]
        rw [h1.map_zero, shl_bvZero]
      map_xor := fun a b => by
        rw [f2Circuit_evalAt_succ, f2Circuit_evalAt_succ, f2Circuit_evalAt_succ]
        dsimp only [f2CircuitEvalStep]
        rw [h1.map_xor, shl_xor_distrib] }
  | fuel + 1, _, _, _, .ushrConst c1 k =>
    let h1 := evalAt_isLinear fuel c1
    { map_zero := by
        rw [f2Circuit_evalAt_succ]
        dsimp only [f2CircuitEvalStep]
        rw [h1.map_zero, ushr_bvZero]
      map_xor := fun a b => by
        rw [f2Circuit_evalAt_succ, f2Circuit_evalAt_succ, f2Circuit_evalAt_succ]
        dsimp only [f2CircuitEvalStep]
        rw [h1.map_xor, ushr_xor_distrib] }
  | fuel + 1, _, _, _, .extract lo len c1 =>
    let h1 := evalAt_isLinear fuel c1
    { map_zero := by
        rw [f2Circuit_evalAt_succ]
        dsimp only [f2CircuitEvalStep]
        rw [h1.map_zero, extractLsb_bvZero]
      map_xor := fun a b => by
        rw [f2Circuit_evalAt_succ, f2Circuit_evalAt_succ, f2Circuit_evalAt_succ]
        dsimp only [f2CircuitEvalStep]
        rw [h1.map_xor, extractLsb_xor_distrib] }
  | fuel + 1, _, _, _, .concat cHi cLo =>
    let hHi := evalAt_isLinear fuel cHi
    let hLo := evalAt_isLinear fuel cLo
    { map_zero := by
        rw [f2Circuit_evalAt_succ]
        dsimp only [f2CircuitEvalStep]
        rw [hHi.map_zero, hLo.map_zero, concatBv_bvZero]
      map_xor := fun a b => by
        rw [f2Circuit_evalAt_succ, f2Circuit_evalAt_succ, f2Circuit_evalAt_succ]
        dsimp only [f2CircuitEvalStep]
        rw [hHi.map_xor, hLo.map_xor, concatBv_xor_distrib] }
  | fuel + 1, _, _, _, .comp c2 c1 =>
    let h1 := evalAt_isLinear fuel c1
    let h2 := evalAt_isLinear fuel c2
    { map_zero := by
        rw [f2Circuit_evalAt_succ]
        dsimp only [f2CircuitEvalStep]
        rw [withStrictBv_eq, h1.map_zero, h2.map_zero]
      map_xor := fun a b => by
        rw [f2Circuit_evalAt_succ, f2Circuit_evalAt_succ, f2Circuit_evalAt_succ]
        dsimp only [f2CircuitEvalStep]
        rw [withStrictBv_eq, withStrictBv_eq, withStrictBv_eq,
            h1.map_xor, h2.map_xor] }

/-- Every `F2Circuit` is automatically `IsF2Linear1`. -/
theorem F2Circuit.eval_isLinear {d wIn wOut : Nat}
    (c : F2Circuit d wIn wOut) : IsF2Linear1 c.eval :=
  evalAt_isLinear (d + 1) c

/-- Universal equivalence of two `F2Circuit`s (even of distinct structural
depths `d1` and `d2`) from `wIn` unit-basis checks, with no manual linearity
proofs required. -/
theorem checkF2CircuitEq_sound {d1 d2 wIn wOut : Nat}
    (c1 : F2Circuit d1 wIn wOut) (c2 : F2Circuit d2 wIn wOut)
    (hcert : checkF2Linear1 c1.eval c2.eval = true) :
    ∀ x : BitVec wIn, c1.eval x = c2.eval x :=
  checkF2Linear1_sound c1.eval_isLinear c2.eval_isLinear hcert

end Anneal.F2Simd
