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
public import Init.Data.BitVec.BasicAux
public import Init.Data.Int.Basic
public import Init.Data.Nat.Basic
public import Init.Data.Nat.Div.Basic
public import Init.Data.Nat.Bitwise.Basic
public import Init.Data.List.Basic
public import Init.Data.Fin.Basic
public import Init.Data.Char.Basic
public import Init.Control.Except
public import Trusted
public import Trusted.MirAst
public import Trusted.MirModel
public import Trusted.MirSemantics
public import Anneal.InitLemmas
public import Anneal.ClassicalEm
public import Anneal.BitVec
public import Anneal.BitVecArith
public import Anneal.Core.BitVecMirBridge

public section

namespace Anneal.Core

open Trusted.MirAst Trusted.MirSemantics

/-!
# Extended `BitVec` / `BitVecArith` Bridges to `Trusted.MirSemantics.Ops`

Extends `Anneal.Core.BitVecMirBridge` across the remaining operators present
in `Trusted.MirAst.Rvalues` and `Trusted.MirSemantics.Ops` (`3` axioms max:
`propext`, `Classical.choice`, `Quot.sound`; zero `omega`/`by_cases`/`sorry`):

1. **Generalized Shifts (`evalShiftOp`):** Signed-LHS (`s = true`,
   `shl`/`ashr`) and signed-RHS (`sR = true`, faulting `.undefined` on negative
   shift amounts in unchecked shifts) lemmas for all four shift operators,
   extending the unsigned bridges in `Anneal.Core.BitVecMirBridge`.
2. **Signed & Missing Arithmetic + Overflow Predicates (`evalArithOp`):**
   Computable bitvector overflow predicates `signedOverflowAddBv`,
   `signedOverflowSubBv`, and `signedOverflowMulBv` with `*_eq_false_iff`
   equivalences (`signedKey_add_no_overflow`, `signedKey_sub_no_overflow`),
   unsigned `mulWithOverflow`/`mulUnchecked`, signed `add`/`sub`/`mul`
   checked/unchecked bridges (across all widths including `.i128`/`u128`), and
   computable `bvSdiv`/`bvSrem` bridges for signed `.div`/`.rem` (covering zero
   divisors and `INT_MIN / -1`, `INT_MIN % -1` faults).
3. **Remaining `evalBinOp` Scalar, `bool`, and `char` Bridges:**
   Scalar `ne`/`gt`/`ge`/`cmp` (`OrderingVal`), mismatch/`.offset` rejections,
   all `.bool` operators (`eq`..`bitXor` and `.cmp`/arith rejections), and all
   `.char` comparison/`cmp` operators.
4. **`evalUnOp`, Negation Range/Tnum Transfers, & `evalIntToIntCast`:**
   `.not`/`.neg` on `.bool`/`.char`, `.ptrMetadata` fault, signed `.neg`
   interval and `tnum` soundness, and `.bool`/`.char`/`.int` casts to
   `.int`/`.char` (including `> 255` and negative-integer `.char` rejections).
-/

/-! ## 0. Helpers, `IntBalance`, & `bvToInt` / `bvOfInt` Normalizations -/

private theorem bvToScalar_width (w : IntWidth) (s : Bool)
    (x : BitVec (8 * w.byteSize)) : (bvToScalar w s x).width = w := rfl

private theorem bvToScalar_signed (w : IntWidth) (s : Bool)
    (x : BitVec (8 * w.byteSize)) : (bvToScalar w s x).signed = s := rfl

private theorem evalBinOp_header_eq (w : IntWidth) (s : Bool) :
    (!(IntWidth.beq w w && (s == s))) = false := by
  cases w <;> cases s <;> rfl

private theorem if_bool_true {α : Sort u} {b : Bool} (hb : b = true)
    (t e : α) : (if b then t else e) = t := by
  rw [hb]
  rfl

private theorem if_bool_false {α : Sort u} {b : Bool} (hb : b = false)
    (t e : α) : (if b then t else e) = e := by
  rw [hb]
  rfl

private theorem if_true_eq {α : Sort u} (t e : α) :
    (if true then t else e) = t := rfl

private theorem if_false_eq {α : Sort u} (t e : α) :
    (if false then t else e) = e := rfl

private theorem if_false_false_eq {α : Sort u} (t e : α) :
    (if false = false then t else e) = t := rfl

private theorem if_true_false_eq {α : Sort u} (t e : α) :
    (if true = false then t else e) = e := rfl

private theorem bitVec_toNat_lt_pow {W : Nat} (x : BitVec W) :
    x.toNat < Nat.pow 2 W :=
  x.isLt

private theorem nat_pow_succ (a n : Nat) :
    Nat.pow a (n + 1) = Nat.pow a n * a :=
  Nat.pow_succ a n

private theorem nat_two_pow_pos (n : Nat) : 0 < Nat.pow 2 n :=
  Anneal.InitLemmas.nat_two_pow_pos n

private theorem nat_two_pow_split {w : Nat} (hw : 0 < w) :
    Nat.pow 2 w = Nat.pow 2 (w - 1) + Nat.pow 2 (w - 1) := by
  cases w with
  | zero => nomatch hw
  | succ k =>
    change Nat.pow 2 (k + 1) = Nat.pow 2 k + Nat.pow 2 k
    rw [nat_pow_succ, Nat.mul_two]

private theorem intWidth_bitWidth_le_128_eight (w : IntWidth) :
    8 * w.byteSize ≤ 128 := by
  rw [← intWidth_bitWidth_eq_eight_mul]
  exact intWidth_bitWidth_le_128 w

private theorem intWidth_eight_le (w : IntWidth) :
    8 ≤ 8 * w.byteSize := by
  have hPos : 1 ≤ w.byteSize := intWidth_byteSize_pos w
  have hMul := Nat.mul_le_mul_left 8 hPos
  rw [Nat.mul_one] at hMul
  exact hMul

private theorem intWidth_dvd_two_pow (w wR : IntWidth) :
    ∃ q : Nat, 2 ≤ q ∧ Nat.pow 2 (8 * wR.byteSize) = q * (8 * w.byteSize) := by
  have h8 : ∃ q0 : Nat, 2 ≤ q0 ∧ Nat.pow 2 8 = q0 * (8 * w.byteSize) := by
    cases w with
    | i8 => exact ⟨32, by decide, by decide⟩
    | i16 => exact ⟨16, by decide, by decide⟩
    | i32 => exact ⟨8, by decide, by decide⟩
    | i64 => exact ⟨4, by decide, by decide⟩
    | i128 => exact ⟨2, by decide, by decide⟩
    | isize => exact ⟨4, by decide, by decide⟩
  let ⟨q0, hq0, hEq0⟩ := h8
  have hLeR : 8 ≤ 8 * wR.byteSize := intWidth_eight_le wR
  have hSplit : 8 * wR.byteSize = (8 * wR.byteSize - 8) + 8 :=
    Eq.symm (Nat.sub_add_cancel hLeR)
  have hPowR := congrArg (Nat.pow 2) hSplit
  rw [Anneal.InitLemmas.nat_pow_add] at hPowR
  have hPowPos : 1 ≤ Nat.pow 2 (8 * wR.byteSize - 8) := nat_two_pow_pos _
  refine ⟨Nat.pow 2 (8 * wR.byteSize - 8) * q0, ?_, ?_⟩
  · have hM := Nat.mul_le_mul hPowPos hq0
    rw [Nat.one_mul] at hM
    exact hM
  · rw [hPowR, hEq0, Nat.mul_assoc]

private theorem nat_div_add_mod (a m : Nat) :
    m * Nat.div a m + Nat.mod a m = a :=
  Nat.div_add_mod a m

private theorem nat_mod_self (n : Nat) : Nat.mod n n = 0 :=
  Nat.mod_self n

private theorem nat_zero_mod (m : Nat) : Nat.mod 0 m = 0 := by
  cases m with
  | zero => rfl
  | succ m' => exact Nat.mod_eq_of_lt (Nat.zero_lt_succ m')

private theorem nat_add_mod_right (a m : Nat) :
    Nat.mod (a + m) m = Nat.mod a m :=
  Nat.add_mod_right a m

private theorem nat_add_mod_left (a m : Nat) :
    Nat.mod (m + a) m = Nat.mod a m :=
  Nat.add_mod_left m a

private theorem nat_sub_right_comm (a b c : Nat) :
    a - b - c = a - c - b := by
  rw [Nat.sub_sub, Nat.add_comm b c, ← Nat.sub_sub]

private theorem nat_shiftLeft_eq (a k : Nat) :
    Nat.shiftLeft a k = a * Nat.pow 2 k :=
  Nat.shiftLeft_eq a k

private theorem nat_shiftRight_le (a k : Nat) :
    Nat.shiftRight a k ≤ a :=
  Nat.shiftRight_le a k

private theorem nat_mul_lt_mul' {a b c d : Nat} (hab : a ≤ b) (hcd : c < d)
    (hb : 0 < b) : a * c < b * d := by
  have h1 : a * c ≤ b * c := Nat.mul_le_mul_right c hab
  have hd : c + 1 ≤ d := hcd
  have h2 : b * c < b * d := by
    have hPos : 0 < b * 1 := by rw [Nat.mul_one]; exact hb
    have h3 : b * c + b * 1 ≤ b * d := by
      rw [← Nat.mul_add]
      exact Nat.mul_le_mul_left b hd
    exact Nat.lt_of_lt_of_le (Nat.lt_add_of_pos_right hPos) h3
  exact Nat.lt_of_le_of_lt h1 h2

private theorem nat_mod_eq_of_lt {a b : Nat} (h : a < b) : Nat.mod a b = a :=
  Nat.mod_eq_of_lt h

private theorem nat_add_mul_mod_self_left (a k m : Nat) :
    Nat.mod (a + k * m) m = Nat.mod a m := by
  rw [Nat.mul_comm k m]
  exact Nat.add_mul_mod_self_left a m k

private theorem nat_add_mod_cancel_left (a b m : Nat) :
    Nat.mod (Nat.mod a m + b) m = Nat.mod (a + b) m := by
  have h : a + b = (Nat.mod a m + b) + Nat.div a m * m := by
    have ha := nat_div_add_mod a m
    rw [Nat.add_comm (m * Nat.div a m) (Nat.mod a m),
      Nat.mul_comm m (Nat.div a m)] at ha
    have h1 := congrArg (fun z => z + b) ha
    rw [Nat.add_right_comm (Nat.mod a m) (Nat.div a m * m) b] at h1
    exact h1.symm
  rw [h, nat_add_mul_mod_self_left]

private theorem nat_mul_mod_cancel_left (a b m : Nat) :
    Nat.mod (Nat.mod a m * b) m = Nat.mod (a * b) m := by
  have h : a * b = Nat.mod a m * b + (Nat.div a m * b) * m := by
    have ha := nat_div_add_mod a m
    rw [Nat.add_comm (m * Nat.div a m) (Nat.mod a m),
      Nat.mul_comm m (Nat.div a m)] at ha
    have h1 := congrArg (fun z => z * b) ha
    rw [Nat.add_mul, Nat.mul_assoc (Nat.div a m) m b, Nat.mul_comm m b,
      ← Nat.mul_assoc (Nat.div a m) b m] at h1
    exact h1.symm
  rw [h, nat_add_mul_mod_self_left]

private theorem nat_mul_mod_cancel_right (a b m : Nat) :
    Nat.mod (a * Nat.mod b m) m = Nat.mod (a * b) m := by
  rw [Nat.mul_comm a (Nat.mod b m), nat_mul_mod_cancel_left, Nat.mul_comm]

private theorem nat_mul_mod (a b m : Nat) :
    Nat.mod (a * b) m = Nat.mod (Nat.mod a m * Nat.mod b m) m := by
  rw [nat_mul_mod_cancel_left, nat_mul_mod_cancel_right]

private theorem nat_mod_mod (a m : Nat) :
    Nat.mod (Nat.mod a m) m = Nat.mod a m := by
  have ha := nat_div_add_mod a m
  rw [Nat.add_comm, Nat.mul_comm] at ha
  have h1 := congrArg (fun z => Nat.mod z m) ha.symm
  rw [nat_add_mul_mod_self_left] at h1
  exact h1.symm

private theorem nat_mul_mod_left (a b : Nat) : Nat.mod (a * b) a = 0 := by
  rw [← Nat.zero_add (a * b), Nat.mul_comm a b, nat_add_mul_mod_self_left,
    nat_zero_mod]

private theorem nat_mul_mod_right (a b : Nat) : Nat.mod (a * b) b = 0 := by
  rw [Nat.mul_comm]
  exact nat_mul_mod_left b a

private theorem nat_shiftRight_zero (m : Nat) : Nat.shiftRight m 0 = m :=
  Eq.trans (Nat.shiftRight_eq_div_pow m 0) (Nat.div_one m)

private theorem toNat_truncateBits_eq_mod (w : IntWidth) (x : BitVec 128) :
    (truncateBits w x).toNat = Nat.mod x.toNat (Nat.pow 2 (8 * w.byteSize)) := by
  have hBw : w.bitWidth - 1 - 0 + 1 = 8 * w.byteSize := by cases w <;> rfl
  have hEq : bvExtractLsb (w.bitWidth - 1) 0 x =
      BitVec.ofNat (w.bitWidth - 1 - 0 + 1) x.toNat := by
    unfold bvExtractLsb bvExtractLsb'
    rw [nat_shiftRight_zero]
  unfold truncateBits
  rw [hEq,
    toNat_bvZeroExtend_of_le
      (by rw [hBw]; exact intWidth_bitWidth_le_128_eight w),
    Anneal.BitVec.toNat_ofNat, hBw]

private theorem nat_add_mod_cancel_right (a b m : Nat) :
    Nat.mod (a + Nat.mod b m) m = Nat.mod (a + b) m := by
  rw [Nat.add_comm a (Nat.mod b m), nat_add_mod_cancel_left, Nat.add_comm b a]

private theorem nat_add_mod (a b m : Nat) :
    Nat.mod (a + b) m = Nat.mod (Nat.mod a m + Nat.mod b m) m := by
  rw [nat_add_mod_cancel_left, nat_add_mod_cancel_right]

private theorem nat_lt_of_add_lt_add_right {a b c : Nat}
    (h : a + c < b + c) : a < b := by
  induction c with
  | zero =>
    rw [Nat.add_zero, Nat.add_zero] at h
    exact h
  | succ c ih =>
    rw [Nat.add_succ, Nat.add_succ] at h
    exact ih (Nat.lt_of_succ_lt_succ h)

private theorem nat_lt_of_add_lt_add_left {a b c : Nat}
    (h : c + a < c + b) : a < b := by
  rw [Nat.add_comm c a, Nat.add_comm c b] at h
  exact nat_lt_of_add_lt_add_right h

private theorem nat_le_of_add_le_add_right {a b c : Nat}
    (h : a + c ≤ b + c) : a ≤ b :=
  Nat.le_of_add_le_add_right h

private theorem nat_sub_sub_cancel_of_le {a b : Nat} (h : a ≤ b) :
    b - (b - a) = a := by
  have hSum : a + (b - a) = b := by
    rw [Nat.add_comm]
    exact Nat.sub_add_cancel h
  have hEq := congrArg (fun z => z - (b - a)) hSum.symm
  rw [Nat.add_sub_cancel] at hEq
  exact hEq

private theorem sub_add_comm_of_le {a b c : Nat} (h : b ≤ a) :
    (a - b) + c = (a + c) - b := by
  have h1 := congrArg (fun z => (z + c) - b) (Nat.sub_add_cancel h).symm
  rw [Nat.add_assoc, Nat.add_comm b c, ← Nat.add_assoc, Nat.add_sub_cancel] at h1
  exact h1.symm

private theorem nat_sub_add_comm_sub {a b c : Nat} (hb : b ≤ a) (hc : c ≤ b) :
    a - (b - c) = (a - b) + c := by
  have h1 : (b - c) + ((a - b) + c) = a := by
    rw [Nat.add_comm (a - b) c, ← Nat.add_assoc, Nat.sub_add_cancel hc,
      Nat.add_comm, Nat.sub_add_cancel hb]
  have h2 := congrArg (fun z => z - (b - c)) h1.symm
  rw [Nat.add_sub_cancel_left] at h2
  exact h2

private theorem int_ofNat_sub_ofNat (m n : Nat) :
    Int.ofNat m - Int.ofNat n = Int.subNatNat m n := by
  cases n with
  | zero =>
    change Int.ofNat m = Int.subNatNat m 0
    unfold Int.subNatNat
    rw [Nat.zero_sub, Nat.sub_zero]
  | succ _ => rfl

private theorem int_ofNat_le_iff {m n : Nat} :
    Int.ofNat m ≤ Int.ofNat n ↔ m ≤ n := by
  constructor
  · intro h
    change Int.NonNeg (Int.ofNat n - Int.ofNat m) at h
    rw [int_ofNat_sub_ofNat] at h
    unfold Int.subNatNat at h
    cases hSub : m - n with
    | zero => exact Nat.le_of_sub_eq_zero hSub
    | succ d =>
      rw [hSub] at h
      nomatch h
  · intro h
    change Int.NonNeg (Int.ofNat n - Int.ofNat m)
    rw [int_ofNat_sub_ofNat]
    unfold Int.subNatNat
    rw [Nat.sub_eq_zero_of_le h]
    exact Int.NonNeg.mk (n - m)

private theorem int_ofNat_lt_iff {m n : Nat} :
    Int.ofNat m < Int.ofNat n ↔ m < n :=
  int_ofNat_le_iff

private theorem int_negSucc_le_negSucc_iff {m n : Nat} :
    Int.negSucc m ≤ Int.negSucc n ↔ n ≤ m := by
  change Int.NonNeg (Int.subNatNat (Nat.succ m) (Nat.succ n)) ↔ _
  unfold Int.subNatNat
  constructor
  · intro h
    cases hSub : Nat.succ n - Nat.succ m with
    | zero => exact Nat.le_of_succ_le_succ (Nat.le_of_sub_eq_zero hSub)
    | succ d =>
      rw [hSub] at h
      nomatch h
  · intro h
    rw [Nat.sub_eq_zero_of_le (Nat.succ_le_succ h)]
    exact Int.NonNeg.mk _

private theorem int_negSucc_lt_negSucc_iff {m n : Nat} :
    Int.negSucc m < Int.negSucc n ↔ n < m := by
  change Int.negSucc m + 1 ≤ Int.negSucc n ↔ _
  cases m with
  | zero =>
    have h0 : Int.negSucc 0 + 1 = Int.ofNat 0 := rfl
    rw [h0]
    constructor
    · intro h
      change Int.NonNeg (Int.negSucc n - Int.ofNat 0) at h
      have hSub : Int.negSucc n - Int.ofNat 0 = Int.negSucc n := rfl
      rw [hSub] at h
      nomatch h
    · intro h
      nomatch h
  | succ m' =>
    have h1 : Int.negSucc (Nat.succ m') + 1 = Int.negSucc m' := rfl
    rw [h1, int_negSucc_le_negSucc_iff]
    exact ⟨Nat.lt_succ_of_le, Nat.le_of_lt_succ⟩

private theorem int_negSucc_lt_ofNat (m n : Nat) :
    Int.negSucc m < Int.ofNat n := by
  change Int.NonNeg (Int.ofNat n - (Int.negSucc m + 1))
  cases m with
  | zero => exact Int.NonNeg.mk n
  | succ m' => exact Int.NonNeg.mk _

private theorem int_negSucc_le_ofNat (m n : Nat) :
    Int.negSucc m ≤ Int.ofNat n :=
  Int.NonNeg.mk _

private theorem int_not_ofNat_le_negSucc (m n : Nat) :
    ¬ (Int.ofNat m ≤ Int.negSucc n) := by
  intro h
  change Int.NonNeg (Int.negSucc n - Int.ofNat m) at h
  cases m with
  | zero =>
    change Int.NonNeg (Int.negSucc n) at h
    nomatch h
  | succ k =>
    change Int.NonNeg (Int.negSucc (n + k).succ) at h
    nomatch h

private theorem int_not_lt_of_ofNat_negSucc (m n : Nat) :
    ¬ (Int.ofNat m < Int.negSucc n) := by
  intro h
  change Int.NonNeg (Int.negSucc n - Int.ofNat (m + 1)) at h
  have hSub : Int.negSucc n - Int.ofNat (m + 1) =
      Int.negSucc (n + (m + 1)) := rfl
  rw [hSub] at h
  nomatch h

private theorem int_not_lt_iff_le (a b : Int) : ¬ (a < b) ↔ b ≤ a := by
  cases a with
  | ofNat m =>
    cases b with
    | ofNat n =>
      rw [int_ofNat_lt_iff, int_ofNat_le_iff]
      exact ⟨Nat.le_of_not_lt, Nat.not_lt_of_ge⟩
    | negSucc n =>
      exact ⟨fun _ => int_negSucc_le_ofNat n m,
        fun _ => int_not_lt_of_ofNat_negSucc m n⟩
  | negSucc m =>
    cases b with
    | ofNat n =>
      exact ⟨fun h => False.elim (h (int_negSucc_lt_ofNat m n)),
        fun h => False.elim (int_not_ofNat_le_negSucc n m h)⟩
    | negSucc n =>
      rw [int_negSucc_lt_negSucc_iff, int_negSucc_le_negSucc_iff]
      exact ⟨Nat.le_of_not_lt, Nat.not_lt_of_ge⟩

private theorem int_not_le_iff_lt (a b : Int) : ¬ (a ≤ b) ↔ b < a := by
  constructor
  · intro h
    cases Anneal.ClassicalEm.prop_em (b < a) with
    | inl hlt => exact hlt
    | inr hnlt => exact False.elim (h ((int_not_lt_iff_le b a).mp hnlt))
  · intro hlt hle
    exact (int_not_lt_iff_le b a).mpr hle hlt

private theorem int_lt_or_ge (a b : Int) : a < b ∨ b ≤ a := by
  cases Anneal.ClassicalEm.prop_em (a < b) with
  | inl h => exact Or.inl h
  | inr h => exact Or.inr ((int_not_lt_iff_le a b).mp h)

private theorem int_neg_ofNat_eq (n : Nat) :
    Neg.neg (Int.ofNat n) =
      match n with | 0 => Int.ofNat 0 | k + 1 => Int.negSucc k := by
  cases n <;> rfl

private theorem int_ofNat_sub_eq_negSucc {m n : Nat} (h : m < n) :
    Int.ofNat m - Int.ofNat n = Int.negSucc (n - 1 - m) := by
  rw [int_ofNat_sub_ofNat]
  unfold Int.subNatNat
  have hPos : 0 < n - m := Nat.zero_lt_sub_of_lt h
  have hSplit : n - m = Nat.succ (n - 1 - m) := by
    have hC := Nat.sub_add_cancel hPos
    rw [Nat.sub_sub, Nat.add_comm m 1, ← Nat.sub_sub] at hC
    exact hC.symm
  rw [hSplit]

private theorem int_ofNat_sub_eq_ofNat {m n : Nat} (h : n ≤ m) :
    Int.ofNat m - Int.ofNat n = Int.ofNat (m - n) := by
  rw [int_ofNat_sub_ofNat]
  unfold Int.subNatNat
  rw [Nat.sub_eq_zero_of_le h]

private theorem intBalance_of_eq {a : Int} {pa na pb nb : Nat}
    (h1 : Anneal.InitLemmas.IntBalance a pa na)
    (hEq : pa + nb = pb + na) :
    Anneal.InitLemmas.IntBalance a pb nb := by
  unfold Anneal.InitLemmas.IntBalance at h1
  unfold Anneal.InitLemmas.IntBalance
  apply Nat.add_right_cancel (m := pa)
  have hL : (Anneal.InitLemmas.intPos a + nb) + pa =
      Anneal.InitLemmas.intPos a + (pa + nb) := by
    rw [Nat.add_assoc, Nat.add_comm nb pa]
  have hR : (Anneal.InitLemmas.intNeg a + pb) + pa =
      pb + (Anneal.InitLemmas.intNeg a + pa) := by
    rw [Nat.add_comm (Anneal.InitLemmas.intNeg a) pb, Nat.add_assoc]
  rw [hL, hEq, hR, ← h1, ← Nat.add_assoc,
    Nat.add_comm (Anneal.InitLemmas.intPos a) pb, Nat.add_assoc]

private theorem intBalance_neg_fn (x : Int) :
    Anneal.InitLemmas.IntBalance (Neg.neg x)
      (Anneal.InitLemmas.intNeg x) (Anneal.InitLemmas.intPos x) := by
  cases x with
  | ofNat m =>
    cases m with
    | zero => rfl
    | succ m' => exact Nat.add_comm 0 (m' + 1)
  | negSucc m => exact Nat.add_comm (m + 1) 0

private theorem intBalance_neg_of {a : Int} {pa na : Nat}
    (ha : Anneal.InitLemmas.IntBalance a pa na) :
    Anneal.InitLemmas.IntBalance (Neg.neg a) na pa := by
  refine intBalance_of_eq (intBalance_neg_fn a) ?_
  rw [Nat.add_comm na _, ha, Nat.add_comm _ pa]

private theorem intBalance_add_fn (x y : Int) :
    Anneal.InitLemmas.IntBalance (x + y)
      (Anneal.InitLemmas.intPos x + Anneal.InitLemmas.intPos y)
      (Anneal.InitLemmas.intNeg x + Anneal.InitLemmas.intNeg y) := by
  cases x with
  | ofNat a =>
    cases y with
    | ofNat b => exact Anneal.InitLemmas.intBalance_ofNat (a + b)
    | negSucc b =>
      dsimp only [Anneal.InitLemmas.intPos, Anneal.InitLemmas.intNeg]
      rw [Nat.add_zero, Nat.zero_add]
      exact Anneal.InitLemmas.intBalance_subNatNat a (b + 1)
  | negSucc a =>
    cases y with
    | ofNat b =>
      dsimp only [Anneal.InitLemmas.intPos, Anneal.InitLemmas.intNeg]
      rw [Nat.zero_add, Nat.add_zero]
      exact Anneal.InitLemmas.intBalance_subNatNat b (a + 1)
    | negSucc b =>
      dsimp only [Anneal.InitLemmas.IntBalance,
        Anneal.InitLemmas.intPos, Anneal.InitLemmas.intNeg]
      rw [Nat.zero_add, Nat.add_zero]
      change 0 + (a + 1 + (b + 1)) = (a + b + 1 + 1) + 0
      rw [Nat.zero_add, Nat.add_zero, Nat.add_assoc a 1 (b + 1),
        Nat.add_comm 1 (b + 1), ← Nat.add_assoc a (b + 1) 1,
        ← Nat.add_assoc a b 1]

private theorem intBalance_add_of {a b : Int} {pa na pb nb : Nat}
    (ha : Anneal.InitLemmas.IntBalance a pa na)
    (hb : Anneal.InitLemmas.IntBalance b pb nb) :
    Anneal.InitLemmas.IntBalance (a + b) (pa + pb) (na + nb) := by
  unfold Anneal.InitLemmas.IntBalance at ha hb
  have hEq : (Anneal.InitLemmas.intPos a + Anneal.InitLemmas.intPos b) +
      (na + nb) =
      (pa + pb) + (Anneal.InitLemmas.intNeg a + Anneal.InitLemmas.intNeg b) := by
    rw [Anneal.InitLemmas.add_four_rearrange, ha, hb,
      Anneal.InitLemmas.add_four_rearrange,
      Nat.add_comm (Anneal.InitLemmas.intNeg a + Anneal.InitLemmas.intNeg b)
        (pa + pb)]
  exact intBalance_of_eq (intBalance_add_fn a b) hEq

private theorem intBalance_sub_of {a b : Int} {pa na pb nb : Nat}
    (ha : Anneal.InitLemmas.IntBalance a pa na)
    (hb : Anneal.InitLemmas.IntBalance b pb nb) :
    Anneal.InitLemmas.IntBalance (a - b) (pa + nb) (na + pb) :=
  intBalance_add_of ha (intBalance_neg_of hb)

private theorem intBalance_lt_iff {a b : Int} {pa na pb nb : Nat}
    (ha : Anneal.InitLemmas.IntBalance a pa na)
    (hb : Anneal.InitLemmas.IntBalance b pb nb) :
    a < b ↔ pa + nb < pb + na := by
  unfold Anneal.InitLemmas.IntBalance at ha hb
  cases a with
  | ofNat ma =>
    cases b with
    | ofNat mb =>
      dsimp only [Anneal.InitLemmas.intPos, Anneal.InitLemmas.intNeg] at ha hb
      rw [Nat.zero_add] at ha hb
      rw [int_ofNat_lt_iff]
      have hL : ma + (na + nb) = (pa + nb) + 0 := by
        rw [← Nat.add_assoc, ha, Nat.add_zero]
      have hR : mb + (na + nb) = (pb + na) + 0 := by
        rw [Nat.add_comm na nb, ← Nat.add_assoc, hb, Nat.add_zero]
      constructor
      · intro hlt
        have hM := Nat.add_lt_add_right hlt (na + nb)
        rw [hL, hR, Nat.add_zero, Nat.add_zero] at hM
        exact hM
      · intro hlt
        apply nat_lt_of_add_lt_add_right (c := na + nb)
        rw [hL, hR, Nat.add_zero, Nat.add_zero]
        exact hlt
    | negSucc mb =>
      dsimp only [Anneal.InitLemmas.intPos, Anneal.InitLemmas.intNeg] at ha hb
      rw [Nat.zero_add] at ha hb
      have hGt : pb + na < pa + nb := by
        have hSum : (pb + na) + (mb + 1 + ma) = pa + nb := by
          rw [← ha, hb, ← Nat.add_assoc (pb + na) (mb + 1) ma,
            Nat.add_right_comm (pb + na) (mb + 1) ma, Nat.add_assoc pb na ma,
            Nat.add_comm pb (na + ma), Nat.add_comm na ma,
            Nat.add_assoc (ma + na) pb (mb + 1), Nat.add_comm pb (mb + 1)]
        have hPos : 0 < mb + 1 + ma := by
          rw [Nat.add_right_comm mb 1 ma]
          exact Nat.zero_lt_succ _
        rw [← hSum]
        exact Nat.lt_add_of_pos_right hPos
      exact ⟨fun h => False.elim (int_not_lt_of_ofNat_negSucc ma mb h),
        fun h => False.elim (Nat.lt_asymm h hGt)⟩
  | negSucc ma =>
    cases b with
    | ofNat mb =>
      dsimp only [Anneal.InitLemmas.intPos, Anneal.InitLemmas.intNeg] at ha hb
      rw [Nat.zero_add] at ha hb
      have hLt : pa + nb < pb + na := by
        have hSum : (pa + nb) + (ma + 1 + mb) = pb + na := by
          rw [ha, ← hb, ← Nat.add_assoc (pa + nb) (ma + 1) mb,
            Nat.add_right_comm (pa + nb) (ma + 1) mb, Nat.add_assoc pa nb mb,
            Nat.add_comm pa (nb + mb), Nat.add_comm nb mb,
            Nat.add_assoc (mb + nb) pa (ma + 1), Nat.add_comm pa (ma + 1)]
        have hPos : 0 < ma + 1 + mb := by
          rw [Nat.add_right_comm ma 1 mb]
          exact Nat.zero_lt_succ _
        rw [← hSum]
        exact Nat.lt_add_of_pos_right hPos
      exact ⟨fun _ => hLt, fun _ => int_negSucc_lt_ofNat ma mb⟩
    | negSucc mb =>
      dsimp only [Anneal.InitLemmas.intPos, Anneal.InitLemmas.intNeg] at ha hb
      rw [Nat.zero_add] at ha hb
      rw [int_negSucc_lt_negSucc_iff]
      have hEq1 : (pa + nb) + (ma + 1) = na + nb := by
        rw [Nat.add_assoc pa nb (ma + 1), Nat.add_comm nb (ma + 1),
          ← Nat.add_assoc pa (ma + 1) nb, Nat.add_comm pa (ma + 1), ← ha]
      have hEq2 : (pb + na) + (mb + 1) = na + nb := by
        rw [Nat.add_assoc pb na (mb + 1), Nat.add_comm na (mb + 1),
          ← Nat.add_assoc pb (mb + 1) na, Nat.add_comm pb (mb + 1), ← hb,
          Nat.add_comm nb na]
      constructor
      · intro hLt
        apply nat_lt_of_add_lt_add_right (c := ma + 1)
        rw [hEq1, ← hEq2]
        exact Nat.add_lt_add_left (Nat.succ_lt_succ hLt) (pb + na)
      · intro hLt
        apply Nat.lt_of_succ_lt_succ
        apply nat_lt_of_add_lt_add_left (c := pb + na)
        rw [hEq2, ← hEq1]
        exact Nat.add_lt_add_right hLt (ma + 1)

private theorem intBalance_le_iff {a b : Int} {pa na pb nb : Nat}
    (ha : Anneal.InitLemmas.IntBalance a pa na)
    (hb : Anneal.InitLemmas.IntBalance b pb nb) :
    a ≤ b ↔ pa + nb ≤ pb + na := by
  rw [← int_not_lt_iff_le, intBalance_lt_iff hb ha]
  exact ⟨Nat.le_of_not_lt, Nat.not_lt_of_ge⟩

private theorem intBalance_eq_of {a : Int} {pa na pb nb : Nat}
    (h1 : Anneal.InitLemmas.IntBalance a pa na)
    (h2 : Anneal.InitLemmas.IntBalance a pb nb) :
    pa + nb = pb + na := by
  unfold Anneal.InitLemmas.IntBalance at h1 h2
  apply Nat.add_right_cancel (m := Anneal.InitLemmas.intPos a)
  have hL : (pa + nb) + Anneal.InitLemmas.intPos a =
      pa + (Anneal.InitLemmas.intPos a + nb) := by
    rw [Nat.add_assoc, Nat.add_comm nb _]
  have hM : pa + (Anneal.InitLemmas.intPos a + nb) =
      (Anneal.InitLemmas.intPos a + na) + pb := by
    rw [h2, Nat.add_comm (Anneal.InitLemmas.intNeg a) pb,
      ← Nat.add_assoc pa pb (Anneal.InitLemmas.intNeg a),
      Nat.add_comm pa pb, Nat.add_assoc pb pa (Anneal.InitLemmas.intNeg a),
      Nat.add_comm pa (Anneal.InitLemmas.intNeg a), ← h1,
      Nat.add_comm pb (Anneal.InitLemmas.intPos a + na)]
  rw [hL, hM, Nat.add_comm (Anneal.InitLemmas.intPos a + na) pb,
    Nat.add_comm (Anneal.InitLemmas.intPos a) na, ← Nat.add_assoc]

private theorem intBalance_eq_iff {a b : Int} {pa na pb nb : Nat}
    (ha : Anneal.InitLemmas.IntBalance a pa na)
    (hb : Anneal.InitLemmas.IntBalance b pb nb) :
    a = b ↔ pa + nb = pb + na := by
  constructor
  · intro h
    subst h
    exact intBalance_eq_of ha hb
  · intro hEq
    have hLe1 : a ≤ b := (intBalance_le_iff ha hb).mpr (Nat.le_of_eq hEq)
    have hLe2 : b ≤ a := (intBalance_le_iff hb ha).mpr (Nat.le_of_eq hEq.symm)
    cases a <;> cases b
    · exact congrArg Int.ofNat (Nat.le_antisymm
        (int_ofNat_le_iff.mp hLe1) (int_ofNat_le_iff.mp hLe2))
    · exact False.elim (int_not_ofNat_le_negSucc _ _ hLe1)
    · exact False.elim (int_not_ofNat_le_negSucc _ _ hLe2)
    · exact congrArg Int.negSucc (Nat.le_antisymm
        (int_negSucc_le_negSucc_iff.mp hLe2)
        (int_negSucc_le_negSucc_iff.mp hLe1))


private theorem bvToInt_neg_eq_negSucc {W : Nat} (hW : 0 < W) {x : BitVec W}
    (hm : Anneal.BitVecArith.msb x = true) :
    bvToInt x = Int.negSucc (Nat.pow 2 W - 1 - x.toNat) := by
  have hGe := (Anneal.BitVecArith.msb_eq_true_iff hW x).mp hm
  have hTwoGe : Nat.pow 2 W ≤ 2 * x.toNat := by
    rw [nat_two_pow_split hW, Nat.two_mul]
    exact Nat.add_le_add hGe hGe
  unfold bvToInt
  rw [Anneal.InitLemmas.ite_false_of (Nat.not_lt_of_ge hTwoGe)]
  exact int_ofNat_sub_eq_negSucc x.isLt

private theorem bvToInt_pos_eq_ofNat {W : Nat} (hW : 0 < W) {x : BitVec W}
    (hm : Anneal.BitVecArith.msb x = false) :
    bvToInt x = Int.ofNat x.toNat := by
  have hLt := (Anneal.BitVecArith.msb_eq_false_iff hW x).mp hm
  have hTwoLt : 2 * x.toNat < Nat.pow 2 W := by
    rw [nat_two_pow_split hW, Nat.two_mul]
    exact Nat.add_lt_add hLt hLt
  unfold bvToInt
  rw [Anneal.InitLemmas.ite_true_of hTwoLt]

/-- Signed `decodeScalar (bvToScalar w true x)` equals `bvToInt x`. -/
theorem decodeScalar_signed_eq_bvToInt (w : IntWidth)
    (x : BitVec (8 * w.byteSize)) :
    decodeScalar (bvToScalar w true x) = bvToInt x := by
  have hW : 0 < 8 * w.byteSize := by
    rw [← intWidth_bitWidth_eq_eight_mul]
    exact intWidth_bitWidth_pos w
  cases hm : Anneal.BitVecArith.msb x with
  | false =>
    rw [decodeScalar_signed_of_msb_false hm, bvToInt_pos_eq_ofNat hW hm]
  | true =>
    rw [decodeScalar_signed_of_msb_true hm, bvToInt_neg_eq_negSucc hW hm]

/-- `truncateBits w (bvOfInt 128 z)` equals `bvZeroExtend 128 (bvOfInt (8 *
w.byteSize) z)` for every `z : Int`. -/
theorem truncateBits_bvOfInt_eq_bvZeroExtend (w : IntWidth) (z : Int) :
    truncateBits w (bvOfInt 128 z) =
      bvZeroExtend 128 (bvOfInt (8 * w.byteSize) z) := by
  apply Anneal.BitVec.eq_of_toNat_eq
  rw [toNat_bvZeroExtend_of_le (intWidth_bitWidth_le_128_eight w)]
  cases z with
  | ofNat m =>
    rw [toNat_truncateBits_bvOfInt_ofNat, toNat_bvOfInt_ofNat]
  | negSucc m =>
    rw [toNat_truncateBits_bvOfInt_negSucc, toNat_bvOfInt_negSucc]
    rw [Nat.sub_sub, Nat.add_comm 1 _]

/-- `signExtendBits w (bvZeroExtend 128 x)` equals `bvToInt x`. -/
theorem signExtendBits_bvZeroExtend (w : IntWidth)
    (x : BitVec (8 * w.byteSize)) :
    signExtendBits w (bvZeroExtend 128 x) = bvToInt x := by
  have hDec : decodeScalar (bvToScalar w true x) =
      signExtendBits w (bvZeroExtend 128 x) := by
    unfold decodeScalar bvToScalar
    rw [Anneal.InitLemmas.ite_true_of (rfl : true = true),
      truncateBits_bvZeroExtend]
  rw [← hDec, decodeScalar_signed_eq_bvToInt]

/-- `IntBalance` presentation of `bvToInt x` via `signedKey x` and
`2^(W - 1)`. -/
theorem intBalance_bvToInt {W : Nat} (hW : 0 < W) (x : BitVec W) :
    Anneal.InitLemmas.IntBalance (bvToInt x)
      (Anneal.BitVecArith.signedKey x) (Nat.pow 2 (W - 1)) := by
  let H := Nat.pow 2 (W - 1)
  have hPow : Nat.pow 2 W = H + H := nat_two_pow_split hW
  cases hm : Anneal.BitVecArith.msb x with
  | false =>
    rw [bvToInt_pos_eq_ofNat hW hm,
      Anneal.BitVecArith.signedKey_eq_of_msb_false hW hm]
    dsimp only [Anneal.InitLemmas.IntBalance,
      Anneal.InitLemmas.intPos, Anneal.InitLemmas.intNeg]
    rw [Nat.zero_add]
  | true =>
    have hGe := (Anneal.BitVecArith.msb_eq_true_iff hW x).mp hm
    rw [bvToInt_neg_eq_negSucc hW hm,
      Anneal.BitVecArith.signedKey_eq_of_msb_true hW hm]
    dsimp only [Anneal.InitLemmas.IntBalance,
      Anneal.InitLemmas.intPos, Anneal.InitLemmas.intNeg]
    rw [Nat.zero_add]
    have hSucc : Nat.pow 2 W - 1 - x.toNat + 1 = Nat.pow 2 W - x.toNat := by
      have hPosD : 0 < Nat.pow 2 W - x.toNat :=
        Nat.zero_lt_sub_of_lt (bitVec_toNat_lt_pow x)
      have hC := Nat.sub_add_cancel hPosD
      rw [Nat.sub_sub, Nat.add_comm x.toNat 1, ← Nat.sub_sub] at hC
      exact hC
    rw [hSucc]
    have hSum : (Nat.pow 2 W - x.toNat + (x.toNat - H)) + H = H + H := by
      rw [Nat.add_assoc, Nat.sub_add_cancel hGe,
        Nat.sub_add_cancel (Nat.le_of_lt (bitVec_toNat_lt_pow x)), hPow]
    exact (Nat.add_right_cancel hSum).symm

/-- For every positive width `W`, `bvToInt x` lies in `[-2^(W - 1),
2^(W - 1))`. -/
theorem bvToInt_in_width_range {W : Nat} (hW : 0 < W) (x : BitVec W) :
    Neg.neg (Int.ofNat (Nat.pow 2 (W - 1))) ≤ bvToInt x ∧
      bvToInt x < Int.ofNat (Nat.pow 2 (W - 1)) := by
  let H := Nat.pow 2 (W - 1)
  have hB := intBalance_bvToInt hW x
  have hNeg := intBalance_neg_of (Anneal.InitLemmas.intBalance_ofNat H)
  have hPos := Anneal.InitLemmas.intBalance_ofNat H
  have hK := Anneal.BitVecArith.signedKey_lt x
  rw [nat_two_pow_split hW] at hK
  refine ⟨?_, ?_⟩
  · rw [intBalance_le_iff hNeg hB, Nat.zero_add]
    exact Nat.le_add_left _ _
  · rw [intBalance_lt_iff hB hPos, Nat.add_zero]
    exact hK

/-- Round-trip: `bvToInt (bvOfInt W z) = z` whenever `W > 0` and `z` lies in
`[-2^(W - 1), 2^(W - 1))`. -/
theorem bvToInt_bvOfInt_eq_of_in_range {W : Nat} (hW : 0 < W) {z : Int}
    (hLo : Neg.neg (Int.ofNat (Nat.pow 2 (W - 1))) ≤ z)
    (hHi : z < Int.ofNat (Nat.pow 2 (W - 1))) :
    bvToInt (bvOfInt W z) = z := by
  let H := Nat.pow 2 (W - 1)
  have hHpos : 0 < H := nat_two_pow_pos (W - 1)
  have hPow : Nat.pow 2 W = H + H := nat_two_pow_split hW
  cases z with
  | ofNat m =>
    have hmLt : m < H := int_ofNat_lt_iff.mp hHi
    have hmLtW : m < Nat.pow 2 W := by
      rw [hPow]
      exact Nat.lt_of_lt_of_le hmLt (Nat.le_add_right H H)
    have hToNat : (bvOfInt W (Int.ofNat m)).toNat = m := by
      rw [toNat_bvOfInt_ofNat, nat_mod_eq_of_lt hmLtW]
    have hTwoLt : 2 * (bvOfInt W (Int.ofNat m)).toNat < Nat.pow 2 W := by
      rw [hToNat, hPow, Nat.two_mul]
      exact Nat.add_lt_add hmLt hmLt
    unfold bvToInt
    rw [Anneal.InitLemmas.ite_true_of hTwoLt, hToNat]
  | negSucc m =>
    have hNegH : Neg.neg (Int.ofNat H) = Int.negSucc (H - 1) := by
      cases hEq : H with
      | zero => rw [hEq] at hHpos; nomatch hHpos
      | succ k => rfl
    rw [hNegH, int_negSucc_le_negSucc_iff] at hLo
    have hmLtH : m < H := Nat.lt_of_le_of_lt hLo (Nat.sub_lt hHpos Nat.one_pos)
    have hmLtW : m < Nat.pow 2 W := by
      rw [hPow]
      exact Nat.lt_of_lt_of_le hmLtH (Nat.le_add_right H H)
    have hToNat : (bvOfInt W (Int.negSucc m)).toNat =
        Nat.pow 2 W - Nat.succ m := by
      rw [toNat_bvOfInt_negSucc, nat_mod_eq_of_lt hmLtW]
    have hGeH : H ≤ Nat.pow 2 W - Nat.succ m := by
      have hSuccLe : Nat.succ m ≤ H := hmLtH
      have h1 : Nat.pow 2 W - H ≤ Nat.pow 2 W - Nat.succ m :=
        Nat.sub_le_sub_left hSuccLe (Nat.pow 2 W)
      have hEq : Nat.pow 2 W - H = H := by rw [hPow, Nat.add_sub_cancel]
      rw [hEq] at h1
      exact h1
    have hTwoGe : Nat.pow 2 W ≤ 2 * (bvOfInt W (Int.negSucc m)).toNat := by
      rw [hToNat, hPow, Nat.two_mul]
      have hGeH2 : H ≤ (H + H) - Nat.succ m := by
        rw [← hPow]
        exact hGeH
      exact Nat.add_le_add hGeH2 hGeH2
    unfold bvToInt
    rw [Anneal.InitLemmas.ite_false_of (Nat.not_lt_of_ge hTwoGe)]
    change Int.ofNat (bvOfInt W (Int.negSucc m)).toNat -
        Int.ofNat (Nat.pow 2 W) = Int.negSucc m
    rw [int_ofNat_sub_eq_negSucc (bitVec_toNat_lt_pow _), hToNat]
    have hSuccLeW : Nat.succ m ≤ Nat.pow 2 W := hmLtW
    have hRes : Nat.pow 2 W - 1 - (Nat.pow 2 W - Nat.succ m) = m := by
      rw [nat_sub_right_comm, nat_sub_sub_cancel_of_le hSuccLeW]
      rfl
    rw [hRes]

/-- Injectivity of `bvToInt` on `BitVec W`. -/
theorem bvToInt_injective {W : Nat} {x y : BitVec W}
    (h : bvToInt x = bvToInt y) : x = y := by
  cases W with
  | zero =>
    apply Anneal.BitVec.eq_of_toNat_eq
    have hx : x.toNat = 0 := Nat.eq_zero_of_le_zero (Nat.le_of_lt_succ x.isLt)
    have hy : y.toNat = 0 := Nat.eq_zero_of_le_zero (Nat.le_of_lt_succ y.isLt)
    rw [hx, hy]
  | succ k =>
    have hW : 0 < k + 1 := Nat.zero_lt_succ k
    have hEq := (intBalance_eq_iff (intBalance_bvToInt hW x)
      (intBalance_bvToInt hW y)).mp h
    exact Anneal.BitVecArith.signedKey_injective (Nat.add_right_cancel hEq)

/-- `bvToInt (signBit (w := 8 * w.byteSize)) = signedMinInt w`. -/
theorem bvToInt_signBit (w : IntWidth) :
    bvToInt (Anneal.BitVecArith.signBit (w := 8 * w.byteSize)) =
      signedMinInt w := by
  have hW : 0 < 8 * w.byteSize := by
    rw [← intWidth_bitWidth_eq_eight_mul]
    exact intWidth_bitWidth_pos w
  have hm : Anneal.BitVecArith.msb
      (Anneal.BitVecArith.signBit (w := 8 * w.byteSize)) = true := by
    rw [Anneal.BitVecArith.msb_eq_true_iff hW,
      Anneal.BitVecArith.toNat_signBit_of_pos hW]
    exact Nat.le_refl _
  rw [bvToInt_neg_eq_negSucc hW hm, Anneal.BitVecArith.toNat_signBit_of_pos hW]
  have hPow : Nat.pow 2 (8 * w.byteSize) =
      Nat.pow 2 (8 * w.byteSize - 1) + Nat.pow 2 (8 * w.byteSize - 1) :=
    nat_two_pow_split hW
  have hSub : Nat.pow 2 (8 * w.byteSize) - 1 -
      Nat.pow 2 (8 * w.byteSize - 1) = Nat.pow 2 (8 * w.byteSize - 1) - 1 := by
    rw [hPow, nat_sub_right_comm, Nat.add_sub_cancel]
  rw [hSub]
  unfold signedMinInt
  rw [intWidth_bitWidth_eq_eight_mul]
  have hPos : 0 < Nat.pow 2 (8 * w.byteSize - 1) := nat_two_pow_pos _
  have hPowInt : HPow.hPow (2 : Int) (8 * w.byteSize - 1) =
      Int.ofNat (Nat.pow 2 (8 * w.byteSize - 1)) := rfl
  rw [hPowInt]
  cases hV : Nat.pow 2 (8 * w.byteSize - 1) with
  | zero => rw [hV] at hPos; nomatch hPos
  | succ k => rfl

/-- `bvToInt (allOnes W) = Neg.neg 1` for every `W > 0`. -/
theorem bvToInt_allOnes {W : Nat} (hW : 0 < W) :
    bvToInt (Anneal.BitVec.allOnes W) = Neg.neg 1 := by
  have hHalf : Nat.pow 2 (W - 1) ≤ Nat.pow 2 W - 1 := by
    rw [nat_two_pow_split hW, ← sub_add_comm_of_le (nat_two_pow_pos (W - 1))]
    exact Nat.le_add_left _ _
  have hm : Anneal.BitVecArith.msb (Anneal.BitVec.allOnes W) = true := by
    rw [Anneal.BitVecArith.msb_eq_true_iff hW, Anneal.BitVec.toNat_allOnes]
    exact hHalf
  rw [bvToInt_neg_eq_negSucc hW hm, Anneal.BitVec.toNat_allOnes, Nat.sub_self]
  rfl

private theorem nat_eq_of_mod_add_right {a b c P : Nat} (ha : a < P) (hb : b < P)
    (h : Nat.mod (a + c) P = Nat.mod (b + c) P) : a = b := by
  have hPpos : 0 < P := Nat.lt_of_le_of_lt (Nat.zero_le a) ha
  let q := P - Nat.mod c P
  have hcEq : c = P * Nat.div c P + Nat.mod c P :=
    (nat_div_add_mod c P).symm
  have hcq : c + q = (Nat.div c P + 1) * P := by
    have hrLe : Nat.mod c P ≤ P := Nat.le_of_lt (Nat.mod_lt c hPpos)
    have hc1 : c + q = (P * Nat.div c P + Nat.mod c P) + q :=
      congrArg (fun z => z + q) hcEq
    rw [hc1, Nat.add_assoc, Nat.add_comm (Nat.mod c P) _,
      Nat.sub_add_cancel hrLe, Nat.add_mul, Nat.one_mul,
      Nat.mul_comm (Nat.div c P) P]
  have haMod : Nat.mod (a + (c + q)) P = a := by
    rw [hcq, nat_add_mul_mod_self_left, nat_mod_eq_of_lt ha]
  have hbMod : Nat.mod (b + (c + q)) P = b := by
    rw [hcq, nat_add_mul_mod_self_left, nat_mod_eq_of_lt hb]
  have hL : Nat.mod (a + (c + q)) P = Nat.mod (Nat.mod (a + c) P + q) P := by
    rw [← Nat.add_assoc, ← nat_add_mod_cancel_left]
  have hR : Nat.mod (b + (c + q)) P = Nat.mod (Nat.mod (b + c) P + q) P := by
    rw [← Nat.add_assoc, ← nat_add_mod_cancel_left]
  rw [← haMod, hL, h, ← hR, hbMod]

private theorem bvOfInt_bvToInt_sub {W : Nat} (hW : 0 < W) (x y : BitVec W) :
    bvOfInt W (bvToInt x - bvToInt y) = x - y := by
  let P := Nat.pow 2 W
  have hPpos : 0 < P := nat_two_pow_pos W
  have hPow : P = Nat.pow 2 (W - 1) + Nat.pow 2 (W - 1) :=
    nat_two_pow_split hW
  have hB : Anneal.InitLemmas.IntBalance (bvToInt x - bvToInt y)
      (Anneal.BitVecArith.signedKey x + Nat.pow 2 (W - 1))
      (Nat.pow 2 (W - 1) + Anneal.BitVecArith.signedKey y) :=
    intBalance_sub_of (intBalance_bvToInt hW x) (intBalance_bvToInt hW y)
  have hMod : Nat.mod ((bvOfInt W (bvToInt x - bvToInt y)).toNat +
      (Nat.pow 2 (W - 1) + Anneal.BitVecArith.signedKey y)) P =
      Nat.mod (Anneal.BitVecArith.signedKey x + Nat.pow 2 (W - 1)) P := by
    cases hz : bvToInt x - bvToInt y with
    | ofNat m =>
      rw [toNat_bvOfInt_ofNat]
      unfold Anneal.InitLemmas.IntBalance Anneal.InitLemmas.intPos
        Anneal.InitLemmas.intNeg at hB
      rw [hz] at hB
      dsimp only at hB
      rw [Nat.zero_add] at hB
      rw [nat_add_mod_cancel_left, hB, Nat.add_comm]
    | negSucc m =>
      rw [toNat_bvOfInt_negSucc]
      unfold Anneal.InitLemmas.IntBalance Anneal.InitLemmas.intPos
        Anneal.InitLemmas.intNeg at hB
      rw [hz] at hB
      dsimp only at hB
      rw [Nat.zero_add] at hB
      have hMlt : Nat.mod m P < P := Nat.mod_lt m hPpos
      have hSplit : P * Nat.div m P + Nat.mod m P = m := nat_div_add_mod m P
      have hModNeg :
          Nat.mod (P - Nat.succ (Nat.mod m P) + (m + 1)) P = 0 := by
        have h1 : P - Nat.succ (Nat.mod m P) + (m + 1) =
            P + P * Nat.div m P := by
          have hSucc : Nat.succ (Nat.mod m P) ≤ P := hMlt
          have hAdd1 : m + 1 = (Nat.mod m P + 1) + P * Nat.div m P := by
            have hC := congrArg (fun z => z + 1) hSplit.symm
            rw [Nat.add_assoc (P * Nat.div m P) (Nat.mod m P) 1,
              Nat.add_comm (P * Nat.div m P) (Nat.mod m P + 1)] at hC
            exact hC
          rw [hAdd1, ← Nat.add_assoc]
          change (P - (Nat.mod m P + 1) + (Nat.mod m P + 1)) +
              P * Nat.div m P = _
          rw [Nat.sub_add_cancel hSucc]
        rw [h1, Nat.mul_comm P _, nat_add_mul_mod_self_left, nat_mod_self]
      have hSum1 : Nat.mod ((P - Nat.succ (Nat.mod m P) + (m + 1)) +
          (Anneal.BitVecArith.signedKey x + Nat.pow 2 (W - 1))) P =
          Nat.mod ((P - Nat.succ (Nat.mod m P)) +
            ((m + 1) + (Anneal.BitVecArith.signedKey x +
              Nat.pow 2 (W - 1)))) P :=
        congrArg (fun z => Nat.mod z P) (Nat.add_assoc _ _ _)
      rw [← hB] at hSum1
      rw [nat_add_mod (P - Nat.succ (Nat.mod m P) + (m + 1)) _ P,
        hModNeg, Nat.zero_add, nat_mod_mod] at hSum1
      exact hSum1.symm
  have hModX : Nat.mod (Anneal.BitVecArith.signedKey x) P =
      Nat.mod (x.toNat + Nat.pow 2 (W - 1)) P := by
    cases hm : Anneal.BitVecArith.msb x with
    | false => rw [Anneal.BitVecArith.signedKey_eq_of_msb_false hW hm]
    | true =>
      have hGe := (Anneal.BitVecArith.msb_eq_true_iff hW x).mp hm
      rw [Anneal.BitVecArith.signedKey_eq_of_msb_true hW hm]
      have hSplit : x.toNat + Nat.pow 2 (W - 1) =
          (x.toNat - Nat.pow 2 (W - 1)) + 1 * P := by
        rw [Nat.one_mul, hPow, ← Nat.add_assoc, Nat.sub_add_cancel hGe]
      rw [hSplit, nat_add_mul_mod_self_left]
  have hModY : Nat.mod (Anneal.BitVecArith.signedKey y) P =
      Nat.mod (y.toNat + Nat.pow 2 (W - 1)) P := by
    cases hm : Anneal.BitVecArith.msb y with
    | false => rw [Anneal.BitVecArith.signedKey_eq_of_msb_false hW hm]
    | true =>
      have hGe := (Anneal.BitVecArith.msb_eq_true_iff hW y).mp hm
      rw [Anneal.BitVecArith.signedKey_eq_of_msb_true hW hm]
      have hSplit : y.toNat + Nat.pow 2 (W - 1) =
          (y.toNat - Nat.pow 2 (W - 1)) + 1 * P := by
        rw [Nat.one_mul, hPow, ← Nat.add_assoc, Nat.sub_add_cancel hGe]
      rw [hSplit, nat_add_mul_mod_self_left]
  have hRhs : Nat.mod (Anneal.BitVecArith.signedKey x + Nat.pow 2 (W - 1)) P =
      Nat.mod x.toNat P := by
    rw [nat_add_mod (Anneal.BitVecArith.signedKey x) (Nat.pow 2 (W - 1)) P,
      hModX,
      ← nat_add_mod (x.toNat + Nat.pow 2 (W - 1)) (Nat.pow 2 (W - 1)) P,
      Nat.add_assoc, ← hPow, Nat.add_comm x.toNat P,
      nat_add_mod_left]
  have hDiff : Nat.mod ((x - y).toNat +
      (Nat.pow 2 (W - 1) + Anneal.BitVecArith.signedKey y)) P =
      Nat.mod x.toNat P := by
    rw [nat_add_mod (x - y).toNat _ P,
      nat_add_mod (Nat.pow 2 (W - 1)) (Anneal.BitVecArith.signedKey y) P,
      hModY,
      ← nat_add_mod (Nat.pow 2 (W - 1)) (y.toNat + Nat.pow 2 (W - 1)) P,
      ← nat_add_mod (x - y).toNat _ P, Anneal.BitVec.toNat_sub,
      nat_add_mod_cancel_left]
    have hyLeP : y.toNat ≤ P := Nat.le_of_lt (bitVec_toNat_lt_pow y)
    have hClean : (P - y.toNat + x.toNat) +
        (Nat.pow 2 (W - 1) + (y.toNat + Nat.pow 2 (W - 1))) =
        x.toNat + 2 * P := by
      rw [Nat.add_comm y.toNat (Nat.pow 2 (W - 1)),
        ← Nat.add_assoc (Nat.pow 2 (W - 1)) (Nat.pow 2 (W - 1)) y.toNat,
        ← hPow, Nat.add_comm P y.toNat,
        Nat.add_assoc (P - y.toNat) x.toNat (y.toNat + P),
        Nat.add_comm x.toNat (y.toNat + P),
        ← Nat.add_assoc (P - y.toNat) (y.toNat + P) x.toNat,
        ← Nat.add_assoc (P - y.toNat) y.toNat P,
        Nat.sub_add_cancel hyLeP, ← Nat.two_mul, Nat.add_comm (2 * P) x.toNat]
    rw [hClean, nat_add_mul_mod_self_left]
  apply Anneal.BitVec.eq_of_toNat_eq
  exact nat_eq_of_mod_add_right (bitVec_toNat_lt_pow _)
    (bitVec_toNat_lt_pow _) (hMod.trans (hRhs.trans hDiff.symm))

private theorem bvOfInt_bvToInt_signExtend {v w : Nat} (hw : 0 < w)
    (hle : w ≤ v) (x : BitVec w) :
    bvOfInt v (bvToInt x) = Anneal.BitVecArith.signExtend v x := by
  apply Anneal.BitVec.eq_of_toNat_eq
  cases hm : Anneal.BitVecArith.msb x with
  | false =>
    have hxLt : x.toNat < Nat.pow 2 v :=
      Nat.lt_of_lt_of_le (bitVec_toNat_lt_pow x)
        (Nat.pow_le_pow_right (by decide : 0 < 2) hle)
    rw [bvToInt_pos_eq_ofNat hw hm, toNat_bvOfInt_ofNat,
      Anneal.BitVecArith.signExtend_of_msb_false v hm,
      Anneal.BitVec.toNat_setWidth, nat_mod_eq_of_lt hxLt]
  | true =>
    have hPowLe : Nat.pow 2 w ≤ Nat.pow 2 v :=
      Nat.pow_le_pow_right (by decide : 0 < 2) hle
    have hDLt : Nat.pow 2 w - 1 - x.toNat < Nat.pow 2 v :=
      Nat.lt_of_lt_of_le
        (Nat.lt_of_le_of_lt (Nat.sub_le _ _)
          (Nat.sub_lt (nat_two_pow_pos w) Nat.one_pos))
        hPowLe
    rw [bvToInt_neg_eq_negSucc hw hm, toNat_bvOfInt_negSucc,
      nat_mod_eq_of_lt hDLt]
    have hNotSign :
        Anneal.BitVec.not (Anneal.BitVecArith.signExtend v x) =
          Anneal.BitVec.setWidth v (Anneal.BitVec.not x) := by
      apply Anneal.BitVec.eq_of_getLsbD_eq
      intro i hi
      rw [Anneal.BitVec.getLsbD_not_of_lt _ hi,
        Anneal.BitVecArith.getLsbD_signExtend,
        Anneal.BitVec.getLsbD_setWidth, decide_eq_true hi, Bool.true_and]
      cases Nat.lt_or_ge i w with
      | inl hlt =>
        rw [Anneal.InitLemmas.ite_true_of hlt,
          Anneal.BitVec.getLsbD_not_of_lt _ hlt, Bool.true_and]
      | inr hge =>
        rw [Anneal.InitLemmas.ite_false_of (Nat.not_lt_of_ge hge), hm,
          Bool.not_true, Anneal.BitVec.getLsbD_ge _ hge, Bool.true_and]
    have hToNat := congrArg BitVec.toNat hNotSign
    rw [Anneal.BitVecArith.toNat_not_eq_sub, Anneal.BitVec.toNat_setWidth,
      Anneal.BitVecArith.toNat_not_eq_sub, nat_mod_eq_of_lt hDLt] at hToNat
    have hInv := congrArg (fun z => Nat.pow 2 v - 1 - z) hToNat.symm
    rw [nat_sub_sub_cancel_of_le (Nat.le_sub_one_of_lt
      (bitVec_toNat_lt_pow (Anneal.BitVecArith.signExtend v x)))] at hInv
    have hSucc : Nat.pow 2 v - Nat.succ (Nat.pow 2 w - 1 - x.toNat) =
        Nat.pow 2 v - 1 - (Nat.pow 2 w - 1 - x.toNat) := by
      rw [Nat.sub_succ]
      change (Nat.pow 2 v - (Nat.pow 2 w - 1 - x.toNat)) - 1 = _
      rw [nat_sub_right_comm (Nat.pow 2 v) (Nat.pow 2 w - 1 - x.toNat) 1]
    rw [hSucc, hInv]

private theorem bvOfInt_signedMinInt (w : IntWidth) :
    bvOfInt (8 * w.byteSize) (signedMinInt w) =
      Anneal.BitVecArith.signBit (w := 8 * w.byteSize) := by
  have hW : 0 < 8 * w.byteSize := by
    rw [← intWidth_bitWidth_eq_eight_mul]
    exact intWidth_bitWidth_pos w
  apply bvToInt_injective
  rw [bvToInt_signBit]
  let h := bvToInt_in_width_range hW
    (Anneal.BitVecArith.signBit (w := 8 * w.byteSize))
  rw [bvToInt_signBit] at h
  exact bvToInt_bvOfInt_eq_of_in_range hW h.1 h.2


/-! ## 1. Generalized Shift Bridges -/

/-- `intEmod` of any `decodeScalar` by `w.bitWidth` equals `Int.ofNat
(y.toNat % (8 * w.byteSize))` across both unsigned and signed shift RHSs. -/
theorem intEmod_decodeScalar_eq_mod (w wR : IntWidth) (sR : Bool)
    (y : BitVec (8 * wR.byteSize)) :
    intEmod (decodeScalar (bvToScalar wR sR y)) (Int.ofNat w.bitWidth) =
      Int.ofNat (Nat.mod y.toNat (8 * w.byteSize)) := by
  have hW : 0 < 8 * w.byteSize := by
    rw [← intWidth_bitWidth_eq_eight_mul]
    exact intWidth_bitWidth_pos w
  rw [intWidth_bitWidth_eq_eight_mul]
  cases sR with
  | false =>
    rw [decodeScalar_unsigned_eq]
    rfl
  | true =>
    cases hm : Anneal.BitVecArith.msb y with
    | false =>
      rw [decodeScalar_signed_of_msb_false hm]
      rfl
    | true =>
      rw [decodeScalar_signed_of_msb_true hm]
      unfold intEmod Int.natAbs
      dsimp only
      let W := 8 * w.byteSize
      let N := Nat.pow 2 (8 * wR.byteSize)
      let ⟨q, hqGe, hPowEq⟩ := intWidth_dvd_two_pow w wR
      have hDivAdd : W * Nat.div y.toNat W + Nat.mod y.toNat W = y.toNat :=
        nat_div_add_mod y.toNat W
      let a := Nat.div y.toNat W
      let b := Nat.mod y.toNat W
      have hbLt : b < W := Nat.mod_lt y.toNat hW
      have haLt : a < q := by
        have hMul : a * W < q * W := by
          have h1 : a * W ≤ W * a + b := by
            rw [Nat.mul_comm a W]
            exact Nat.le_add_right _ _
          rw [hDivAdd] at h1
          rw [← hPowEq]
          exact Nat.lt_of_le_of_lt h1 (bitVec_toNat_lt_pow y)
        cases Nat.lt_or_ge a q with
        | inl hlt => exact hlt
        | inr hge =>
          exact False.elim (Nat.not_le_of_gt hMul (Nat.mul_le_mul_right W hge))
      have hSubDecomp : N - 1 - y.toNat =
          (W - 1 - b) + (q - a - 1) * W := by
        have hSum : ((W - 1 - b) + (q - a - 1) * W) + (y.toNat + 1) = N := by
          have hAdd1 : (W - 1 - b) + (b + 1) = W := by
            have hbLe : b ≤ W - 1 := Nat.le_sub_one_of_lt hbLt
            rw [← Nat.add_assoc, Nat.sub_add_cancel hbLe, Nat.sub_add_cancel hW]
          have hMulK : W + (q - a - 1) * W + a * W = q * W := by
            have hK : 1 + (q - a - 1) + a = q := by
              have haLe : a ≤ q - 1 := Nat.le_sub_one_of_lt haLt
              have hq1 : 1 ≤ q := Nat.le_trans (by decide : 1 ≤ 2) hqGe
              have hSwap : q - a - 1 = q - 1 - a := nat_sub_right_comm q a 1
              rw [hSwap, Nat.add_assoc 1 (q - 1 - a) a,
                Nat.sub_add_cancel haLe, Nat.add_comm 1 (q - 1),
                Nat.sub_add_cancel hq1]
            have hM := congrArg (fun z => z * W) hK
            rw [Nat.add_mul, Nat.add_mul, Nat.one_mul] at hM
            exact hM
          rw [← hDivAdd, Nat.mul_comm W a, Nat.add_assoc (a * W) b 1,
            Nat.add_assoc (W - 1 - b) ((q - a - 1) * W) (a * W + (b + 1)),
            ← Nat.add_assoc ((q - a - 1) * W) (a * W) (b + 1),
            Nat.add_comm ((q - a - 1) * W + a * W) (b + 1),
            ← Nat.add_assoc (W - 1 - b) (b + 1) ((q - a - 1) * W + a * W),
            hAdd1, ← Nat.add_assoc W ((q - a - 1) * W) (a * W), hMulK,
            ← hPowEq]
        have hD := congrArg (fun z => z - (y.toNat + 1)) hSum
        rw [Nat.add_sub_cancel, Nat.add_comm y.toNat 1, ← Nat.sub_sub] at hD
        exact hD.symm
      have hModEq : Nat.mod (N - 1 - y.toNat) W = W - 1 - b := by
        rw [hSubDecomp, nat_add_mul_mod_self_left,
          nat_mod_eq_of_lt (Nat.lt_of_le_of_lt (Nat.sub_le (W - 1) b)
            (Nat.sub_lt hW Nat.one_pos))]
      rw [hModEq]
      have hSucc : Nat.succ (W - 1 - b) = W - b := by
        have hPos : 0 < W - b := Nat.zero_lt_sub_of_lt hbLt
        have hC := Nat.sub_add_cancel hPos
        rw [nat_sub_right_comm] at hC
        exact hC
      rw [hSucc]
      unfold Int.subNatNat
      rw [Nat.sub_eq_zero_of_le (Nat.sub_le W b), nat_sub_sub_cancel_of_le
        (Nat.le_of_lt hbLt)]

private theorem toNat_truncateBits_bvOfInt_shl (w : IntWidth) (s : Bool)
    (x : BitVec (8 * w.byteSize)) (k : Nat) :
    (truncateBits w (bvOfInt 128
        (intShiftLeft (decodeScalar (bvToScalar w s x)) k))).toNat =
      (Anneal.BitVec.shl x k).toNat := by
  let W := 8 * w.byteSize
  let P := Nat.pow 2 W
  have hPpos : 0 < P := nat_two_pow_pos W
  rw [Anneal.BitVec.toNat_shl]
  cases s with
  | false =>
    rw [decodeScalar_unsigned_eq]
    unfold intShiftLeft
    rw [toNat_truncateBits_bvOfInt_ofNat]
  | true =>
    cases hm : Anneal.BitVecArith.msb x with
    | false =>
      rw [decodeScalar_signed_of_msb_false hm]
      unfold intShiftLeft
      rw [toNat_truncateBits_bvOfInt_ofNat]
    | true =>
      rw [decodeScalar_signed_of_msb_true hm]
      unfold intShiftLeft
      rw [toNat_truncateBits_bvOfInt_negSucc]
      have hBaseEq : P - 1 - x.toNat + 1 = P - x.toNat := by
        have hPos : 0 < P - x.toNat :=
          Nat.zero_lt_sub_of_lt (bitVec_toNat_lt_pow x)
        have hC := Nat.sub_add_cancel hPos
        rw [Nat.sub_sub, Nat.add_comm x.toNat 1, ← Nat.sub_sub] at hC
        exact hC
      rw [hBaseEq]
      let S := Nat.shiftLeft (P - x.toNat) k
      let T := Nat.shiftLeft x.toNat k
      have hSpos : 0 < S := by
        dsimp only [S]
        rw [nat_shiftLeft_eq]
        exact Nat.mul_pos (Nat.zero_lt_sub_of_lt (bitVec_toNat_lt_pow x))
          (nat_two_pow_pos k)
      have hS1 : (S - 1) + 1 = S := Nat.sub_add_cancel hSpos
      have hDivAdd : P * Nat.div (S - 1) P + Nat.mod (S - 1) P = S - 1 :=
        nat_div_add_mod (S - 1) P
      let r := Nat.mod (S - 1) P
      have hrLt : r < P := Nat.mod_lt (S - 1) hPpos
      have hrLe : r ≤ P - 1 := Nat.le_sub_one_of_lt hrLt
      have hRS : (P - 1 - r) + (r + 1) = P := by
        rw [← Nat.add_assoc, Nat.sub_add_cancel hrLe, Nat.sub_add_cancel hPpos]
      have hClean : (P - 1 - r) + S = P + P * Nat.div (S - 1) P := by
        have hS2 : S = (r + 1) + P * Nat.div (S - 1) P := by
          have hC := congrArg (fun z => z + 1) hDivAdd
          rw [hS1, Nat.add_assoc (P * Nat.div (S - 1) P) r 1,
            Nat.add_comm (P * Nat.div (S - 1) P) (r + 1)] at hC
          exact hC.symm
        have h1 := congrArg (fun z => (P - 1 - r) + z) hS2
        rw [← Nat.add_assoc, hRS] at h1
        exact h1
      have hSum : S + T = Nat.pow 2 k * P := by
        dsimp only [S, T]
        rw [nat_shiftLeft_eq, nat_shiftLeft_eq, ← Nat.add_mul,
          Nat.sub_add_cancel (Nat.le_of_lt (bitVec_toNat_lt_pow x)),
          Nat.mul_comm]
      have hSumMod : Nat.mod (((P - 1 - r) + S) + T) P =
          Nat.mod ((P - 1 - r) + (S + T)) P := by
        rw [Nat.add_assoc]
      have hLhsMod : Nat.mod (((P - 1 - r) + S) + T) P = Nat.mod T P := by
        rw [hClean, Nat.add_comm (P + P * Nat.div (S - 1) P) T,
          ← Nat.add_assoc T P (P * Nat.div (S - 1) P),
          Nat.mul_comm P (Nat.div (S - 1) P),
          nat_add_mul_mod_self_left, Nat.add_comm T P, nat_add_mod_left]
      have hRhsMod : Nat.mod ((P - 1 - r) + (S + T)) P = P - 1 - r := by
        rw [hSum, nat_add_mul_mod_self_left,
          nat_mod_eq_of_lt (Nat.lt_of_le_of_lt (Nat.sub_le (P - 1) r)
            (Nat.sub_lt hPpos Nat.one_pos))]
      rw [hSumMod, hRhsMod] at hLhsMod
      exact hLhsMod

private theorem intShiftRight_ofNat (n k : Nat) :
    intShiftRight (Int.ofNat n) k = Int.ofNat (Nat.shiftRight n k) := rfl

private theorem intShiftRight_negSucc (m k : Nat) :
    intShiftRight (Int.negSucc m) k = Int.negSucc (Nat.shiftRight m k) := rfl

private theorem toNat_truncateBits_bvOfInt_shr (w : IntWidth) (s : Bool)
    (x : BitVec (8 * w.byteSize)) (k : Nat) :
    (truncateBits w (bvOfInt 128
        (intShiftRight (decodeScalar (bvToScalar w s x)) k))).toNat =
      (if s then Anneal.BitVecArith.ashr x k else Anneal.BitVec.ushr x k).toNat := by
  cases s with
  | false =>
    rw [if_false_eq, decodeScalar_unsigned_eq, intShiftRight_ofNat,
      toNat_truncateBits_bvOfInt_ofNat, Anneal.BitVec.toNat_ushr,
      nat_mod_eq_of_lt (Nat.lt_of_le_of_lt (nat_shiftRight_le _ _)
        (bitVec_toNat_lt_pow x))]
  | true =>
    rw [if_true_eq]
    cases hm : Anneal.BitVecArith.msb x with
    | false =>
      rw [decodeScalar_signed_of_msb_false hm, intShiftRight_ofNat,
        toNat_truncateBits_bvOfInt_ofNat,
        Anneal.BitVecArith.ashr_of_msb_false k hm, Anneal.BitVec.toNat_ushr,
        nat_mod_eq_of_lt (Nat.lt_of_le_of_lt (nat_shiftRight_le _ _)
          (bitVec_toNat_lt_pow x))]
    | true =>
      rw [decodeScalar_signed_of_msb_true hm, intShiftRight_negSucc,
        toNat_truncateBits_bvOfInt_negSucc]
      have hSubMod :
          Nat.mod (Nat.shiftRight (Nat.pow 2 (8 * w.byteSize) - 1 - x.toNat) k)
              (Nat.pow 2 (8 * w.byteSize)) =
            Nat.shiftRight (Nat.pow 2 (8 * w.byteSize) - 1 - x.toNat) k := by
        apply nat_mod_eq_of_lt
        exact Nat.lt_of_le_of_lt (nat_shiftRight_le _ _)
          (Nat.lt_of_le_of_lt (Nat.sub_le _ _)
            (Nat.sub_lt (nat_two_pow_pos _) Nat.one_pos))
      rw [hSubMod]
      have hNot : (Anneal.BitVec.not x).toNat =
          Nat.pow 2 (8 * w.byteSize) - 1 - x.toNat :=
        Anneal.BitVecArith.toNat_not_eq_sub x
      have hAshr : Anneal.BitVecArith.ashr x k =
          Anneal.BitVec.not (Anneal.BitVec.ushr (Anneal.BitVec.not x) k) := by
        apply Anneal.BitVec.eq_of_getLsbD_eq
        intro i hi
        rw [Anneal.BitVecArith.getLsbD_ashr,
          Anneal.BitVec.getLsbD_not_of_lt _ hi,
          Anneal.BitVec.getLsbD_ushr, decide_eq_true hi, Bool.true_and]
        cases Nat.lt_or_ge (i + k) (8 * w.byteSize) with
        | inl hlt =>
          rw [Anneal.InitLemmas.ite_true_of hlt,
            Anneal.BitVec.getLsbD_not_of_lt _ hlt]
          cases Anneal.BitVec.getLsbD x (i + k) <;> rfl
        | inr hge =>
          rw [Anneal.InitLemmas.ite_false_of (Nat.not_lt_of_ge hge),
            Anneal.BitVec.getLsbD_ge _ hge, hm]
          rfl
      rw [hAshr, Anneal.BitVecArith.toNat_not_eq_sub,
        Anneal.BitVec.toNat_ushr, hNot]

private theorem shiftOverflow_eq (w wR : IntWidth) (sR : Bool)
    (y : BitVec (8 * wR.byteSize)) :
    (intEmod (decodeScalar (bvToScalar wR sR y)) (Int.ofNat w.bitWidth) !=
        decodeScalar (bvToScalar wR sR y)) =
      !((!sR || !Anneal.BitVecArith.msb y) &&
        decide (y.toNat < 8 * w.byteSize)) := by
  rw [intEmod_decodeScalar_eq_mod]
  cases sR with
  | false =>
    rw [decodeScalar_unsigned_eq]
    cases Nat.lt_or_ge y.toNat (8 * w.byteSize) with
    | inl hLt =>
      rw [decide_eq_true hLt, nat_mod_eq_of_lt hLt]
      change (!(Int.ofNat y.toNat == Int.ofNat y.toNat)) = _
      rw [beq_self_eq_true]
      rfl
    | inr hGe =>
      have hW : 0 < 8 * w.byteSize := by
        rw [← intWidth_bitWidth_eq_eight_mul]
        exact intWidth_bitWidth_pos w
      have hNeInt : Int.ofNat (Nat.mod y.toNat (8 * w.byteSize)) ≠
          Int.ofNat y.toNat :=
        fun h => Nat.ne_of_lt (Nat.lt_of_lt_of_le (Nat.mod_lt y.toNat hW) hGe)
          (Int.ofNat.inj h)
      rw [decide_eq_false (Nat.not_lt_of_ge hGe), bne_iff_ne.mpr hNeInt]
      rfl
  | true =>
    cases hm : Anneal.BitVecArith.msb y with
    | false =>
      rw [decodeScalar_signed_of_msb_false hm]
      cases Nat.lt_or_ge y.toNat (8 * w.byteSize) with
      | inl hLt =>
        rw [decide_eq_true hLt, nat_mod_eq_of_lt hLt]
        change (!(Int.ofNat y.toNat == Int.ofNat y.toNat)) = _
        rw [beq_self_eq_true]
        rfl
      | inr hGe =>
        have hW : 0 < 8 * w.byteSize := by
          rw [← intWidth_bitWidth_eq_eight_mul]
          exact intWidth_bitWidth_pos w
        have hNeInt : Int.ofNat (Nat.mod y.toNat (8 * w.byteSize)) ≠
            Int.ofNat y.toNat :=
          fun h => Nat.ne_of_lt (Nat.lt_of_lt_of_le (Nat.mod_lt y.toNat hW) hGe)
            (Int.ofNat.inj h)
        rw [decide_eq_false (Nat.not_lt_of_ge hGe), bne_iff_ne.mpr hNeInt]
        rfl
    | true =>
      rw [decodeScalar_signed_of_msb_true hm]
      have hNe : Int.ofNat (Nat.mod y.toNat (8 * w.byteSize)) ≠
          Int.negSucc (Nat.pow 2 (8 * wR.byteSize) - 1 - y.toNat) :=
        fun h => nomatch h
      rw [bne_iff_ne.mpr hNe]
      rfl

/-- Wrapping left shift (`BinOp.shl`) across arbitrary LHS signedness `s` and
RHS signedness `sR`: computes `Anneal.BitVec.shl x (y.toNat % (8 *
w.byteSize))`. -/
theorem evalBinOp_shl_eq_shl (w wR : IntWidth) (s sR : Bool)
    (x : BitVec (8 * w.byteSize)) (y : BitVec (8 * wR.byteSize)) :
    evalBinOp .shl (.scalar (bvToScalar w s x))
        (.scalar (bvToScalar wR sR y)) =
      .ok (.scalar (bvToScalar w s
        (Anneal.BitVec.shl x (Nat.mod y.toNat (8 * w.byteSize))))) := by
  unfold evalBinOp evalShiftOp
  dsimp only
  rw [if_bool_true (rfl : BinOp.shl.isShift = true), bvToScalar_width,
    bvToScalar_signed, intEmod_decodeScalar_eq_mod]
  dsimp only [Int.toNat]
  let ⟨lossy, hTrunc⟩ := truncateScalar_val_eq w s
    (intShiftLeft (decodeScalar (bvToScalar w s x))
      (Nat.mod y.toNat (8 * w.byteSize)))
  rw [hTrunc]
  dsimp only
  have hU : BinOp.shl.isUnchecked = false := rfl
  rw [hU, Bool.and_false, if_false_eq]
  have hBits : truncateBits w (bvOfInt 128
        (intShiftLeft (decodeScalar (bvToScalar w s x))
          (Nat.mod y.toNat (8 * w.byteSize)))) =
      bvZeroExtend 128
        (Anneal.BitVec.shl x (Nat.mod y.toNat (8 * w.byteSize))) := by
    apply Anneal.BitVec.eq_of_toNat_eq
    rw [toNat_truncateBits_bvOfInt_shl,
      toNat_bvZeroExtend_of_le (intWidth_bitWidth_le_128_eight w)]
  change Except.ok (Val.scalar ⟨w, s, truncateBits w (bvOfInt 128
      (intShiftLeft (decodeScalar (bvToScalar w s x))
        (Nat.mod y.toNat (8 * w.byteSize))))⟩) = _
  rw [hBits]
  rfl

/-- Wrapping right shift (`BinOp.shr`) across arbitrary LHS signedness `s` and
RHS signedness `sR`: computes `ashr` when `s = true` and `ushr` when `s =
false`, masking the shift amount modulo `8 * w.byteSize`. -/
theorem evalBinOp_shr_eq (w wR : IntWidth) (s sR : Bool)
    (x : BitVec (8 * w.byteSize)) (y : BitVec (8 * wR.byteSize)) :
    evalBinOp .shr (.scalar (bvToScalar w s x))
        (.scalar (bvToScalar wR sR y)) =
      .ok (.scalar (bvToScalar w s
        (if s then Anneal.BitVecArith.ashr x (Nat.mod y.toNat (8 * w.byteSize))
        else Anneal.BitVec.ushr x (Nat.mod y.toNat (8 * w.byteSize))))) := by
  unfold evalBinOp evalShiftOp
  dsimp only
  rw [if_bool_true (rfl : BinOp.shr.isShift = true), bvToScalar_width,
    bvToScalar_signed, intEmod_decodeScalar_eq_mod]
  dsimp only [Int.toNat]
  let ⟨lossy, hTrunc⟩ := truncateScalar_val_eq w s
    (intShiftRight (decodeScalar (bvToScalar w s x))
      (Nat.mod y.toNat (8 * w.byteSize)))
  rw [hTrunc]
  dsimp only
  have hU : BinOp.shr.isUnchecked = false := rfl
  rw [hU, Bool.and_false, if_false_eq]
  have hBits : truncateBits w (bvOfInt 128
        (intShiftRight (decodeScalar (bvToScalar w s x))
          (Nat.mod y.toNat (8 * w.byteSize)))) =
      bvZeroExtend 128 (if s then
          Anneal.BitVecArith.ashr x (Nat.mod y.toNat (8 * w.byteSize))
        else Anneal.BitVec.ushr x (Nat.mod y.toNat (8 * w.byteSize))) := by
    apply Anneal.BitVec.eq_of_toNat_eq
    rw [toNat_truncateBits_bvOfInt_shr,
      toNat_bvZeroExtend_of_le (intWidth_bitWidth_le_128_eight w)]
  change Except.ok (Val.scalar ⟨w, s, truncateBits w (bvOfInt 128
      (intShiftRight (decodeScalar (bvToScalar w s x))
        (Nat.mod y.toNat (8 * w.byteSize))))⟩) = _
  rw [hBits]
  rfl

/-- Generalized unchecked left shift (`BinOp.shlUnchecked`) across arbitrary
`s` and `sR`: succeeds iff `!sR || !msb y` and `y.toNat < 8 * w.byteSize`,
faulting with `.error .undefined` on negative or out-of-range shifts. -/
theorem evalBinOp_shlUnchecked_eq (w wR : IntWidth) (s sR : Bool)
    (x : BitVec (8 * w.byteSize)) (y : BitVec (8 * wR.byteSize)) :
    evalBinOp .shlUnchecked (.scalar (bvToScalar w s x))
        (.scalar (bvToScalar wR sR y)) =
      if (!sR || !Anneal.BitVecArith.msb y) &&
          decide (y.toNat < 8 * w.byteSize) then
        .ok (.scalar (bvToScalar w s (Anneal.BitVec.shl x y.toNat)))
      else
        .error .undefined := by
  unfold evalBinOp evalShiftOp
  dsimp only
  rw [if_bool_true (rfl : BinOp.shlUnchecked.isShift = true),
    bvToScalar_width, bvToScalar_signed]
  have hOvf := shiftOverflow_eq w wR sR y
  rw [intEmod_decodeScalar_eq_mod]
  dsimp only [Int.toNat]
  let ⟨lossy, hTrunc⟩ := truncateScalar_val_eq w s
    (intShiftLeft (decodeScalar (bvToScalar w s x))
      (Nat.mod y.toNat (8 * w.byteSize)))
  rw [hTrunc]
  dsimp only
  have hU : BinOp.shlUnchecked.isUnchecked = true := rfl
  rw [hU, Bool.and_true, ← intEmod_decodeScalar_eq_mod w wR sR y, hOvf]
  cases hCond : (!sR || !Anneal.BitVecArith.msb y) &&
      decide (y.toNat < 8 * w.byteSize) with
  | false =>
    rw [Bool.not_false, if_true_eq, if_false_eq]
  | true =>
    have hLt : y.toNat < 8 * w.byteSize :=
      of_decide_eq_true (Anneal.InitLemmas.bool_and_right hCond)
    have hModEq : Nat.mod y.toNat (8 * w.byteSize) = y.toNat :=
      nat_mod_eq_of_lt hLt
    rw [Bool.not_true, if_false_eq, if_true_eq]
    have hBits : truncateBits w (bvOfInt 128
          (intShiftLeft (decodeScalar (bvToScalar w s x))
            (Nat.mod y.toNat (8 * w.byteSize)))) =
        bvZeroExtend 128 (Anneal.BitVec.shl x y.toNat) := by
      apply Anneal.BitVec.eq_of_toNat_eq
      rw [toNat_truncateBits_bvOfInt_shl, hModEq,
        toNat_bvZeroExtend_of_le (intWidth_bitWidth_le_128_eight w)]
    change Except.ok (Val.scalar ⟨w, s, truncateBits w (bvOfInt 128
        (intShiftLeft (decodeScalar (bvToScalar w s x))
          (Nat.mod y.toNat (8 * w.byteSize))))⟩) = _
    rw [hBits]
    rfl

/-- Generalized unchecked right shift (`BinOp.shrUnchecked`) across arbitrary
`s` and `sR`: computes `ashr` (`s = true`) or `ushr` (`s = false`) iff
`!sR || !msb y` and `y.toNat < 8 * w.byteSize`, else `.error .undefined`. -/
theorem evalBinOp_shrUnchecked_eq (w wR : IntWidth) (s sR : Bool)
    (x : BitVec (8 * w.byteSize)) (y : BitVec (8 * wR.byteSize)) :
    evalBinOp .shrUnchecked (.scalar (bvToScalar w s x))
        (.scalar (bvToScalar wR sR y)) =
      if (!sR || !Anneal.BitVecArith.msb y) &&
          decide (y.toNat < 8 * w.byteSize) then
        .ok (.scalar (bvToScalar w s
          (if s then Anneal.BitVecArith.ashr x y.toNat
          else Anneal.BitVec.ushr x y.toNat)))
      else
        .error .undefined := by
  unfold evalBinOp evalShiftOp
  dsimp only
  rw [if_bool_true (rfl : BinOp.shrUnchecked.isShift = true),
    bvToScalar_width, bvToScalar_signed]
  have hOvf := shiftOverflow_eq w wR sR y
  rw [intEmod_decodeScalar_eq_mod]
  dsimp only [Int.toNat]
  let ⟨lossy, hTrunc⟩ := truncateScalar_val_eq w s
    (intShiftRight (decodeScalar (bvToScalar w s x))
      (Nat.mod y.toNat (8 * w.byteSize)))
  rw [hTrunc]
  dsimp only
  have hU : BinOp.shrUnchecked.isUnchecked = true := rfl
  rw [hU, Bool.and_true, ← intEmod_decodeScalar_eq_mod w wR sR y, hOvf]
  cases hCond : (!sR || !Anneal.BitVecArith.msb y) &&
      decide (y.toNat < 8 * w.byteSize) with
  | false =>
    rw [Bool.not_false, if_true_eq, if_false_eq]
  | true =>
    have hLt : y.toNat < 8 * w.byteSize :=
      of_decide_eq_true (Anneal.InitLemmas.bool_and_right hCond)
    have hModEq : Nat.mod y.toNat (8 * w.byteSize) = y.toNat :=
      nat_mod_eq_of_lt hLt
    rw [Bool.not_true, if_false_eq, if_true_eq]
    have hBits : truncateBits w (bvOfInt 128
          (intShiftRight (decodeScalar (bvToScalar w s x))
            (Nat.mod y.toNat (8 * w.byteSize)))) =
        bvZeroExtend 128 (if s then Anneal.BitVecArith.ashr x y.toNat
          else Anneal.BitVec.ushr x y.toNat) := by
      apply Anneal.BitVec.eq_of_toNat_eq
      rw [toNat_truncateBits_bvOfInt_shr, hModEq,
        toNat_bvZeroExtend_of_le (intWidth_bitWidth_le_128_eight w)]
    change Except.ok (Val.scalar ⟨w, s, truncateBits w (bvOfInt 128
        (intShiftRight (decodeScalar (bvToScalar w s x))
          (Nat.mod y.toNat (8 * w.byteSize))))⟩) = _
    rw [hBits]
    rfl

/-- Unchecked shift faults with `.error .undefined` on any negative signed
shift amount (`msb y = true`). -/
theorem evalBinOp_shiftUnchecked_neg_rhs_fault (op : BinOp)
    (hOp : op = .shlUnchecked ∨ op = .shrUnchecked)
    (w wR : IntWidth) (s : Bool)
    (x : BitVec (8 * w.byteSize)) {y : BitVec (8 * wR.byteSize)}
    (hNeg : Anneal.BitVecArith.msb y = true) :
    evalBinOp op (.scalar (bvToScalar w s x))
        (.scalar (bvToScalar wR true y)) = .error .undefined := by
  cases hOp with
  | inl h =>
    subst h
    rw [evalBinOp_shlUnchecked_eq, hNeg]
    rfl
  | inr h =>
    subst h
    rw [evalBinOp_shrUnchecked_eq, hNeg]
    rfl


/-! ## 2. Signed & Missing Arithmetic + Overflow Predicates -/

private theorem bvToInt_in_i128_range (y : BitVec 128) :
    (decide (bvToInt y < Neg.neg (HPow.hPow (2 : Int) 127)) ||
      decide (bvToInt y ≥ HPow.hPow (2 : Int) 127)) = false := by
  have h := bvToInt_in_width_range (by decide : 0 < 128) y
  have hP : HPow.hPow (2 : Int) 127 = Int.ofNat (Nat.pow 2 127) := rfl
  rw [hP, decide_eq_false ((int_not_lt_iff_le _ _).mpr h.1),
    decide_eq_false ((int_not_le_iff_lt _ _).mpr h.2)]
  rfl

private theorem unsigned_nat_overflow_flag_eq (w : IntWidth) (n : Nat) :
    let result := Int.ofNat n
    let hostOverflow :=
      decide (result < 0) || decide (result ≥ HPow.hPow (2 : Int) 128)
    let trunc := truncateBits w (bvOfInt 128 result)
    let lossy := trunc != bvOfInt 128 result
    (hostOverflow || lossy) =
      decide (Nat.pow 2 (8 * w.byteSize) ≤ n) := by
  let M := Nat.pow 2 (8 * w.byteSize)
  have hNotNeg : decide (Int.ofNat n < 0) = false :=
    decide_eq_false (fun h => nomatch h)
  have hMod : (truncateBits w (bvOfInt 128 (Int.ofNat n))).toNat = Nat.mod n M :=
    toNat_truncateBits_bvOfInt_ofNat w n
  have h128 : (bvOfInt 128 (Int.ofNat n)).toNat = Nat.mod n (Nat.pow 2 128) :=
    toNat_bvOfInt_ofNat 128 n
  cases Nat.lt_or_ge n M with
  | inl hLt =>
    have hLt128 : n < Nat.pow 2 128 :=
      Nat.lt_of_lt_of_le hLt
        (Nat.pow_le_pow_right (by decide : 0 < 2)
          (intWidth_bitWidth_le_128_eight w))
    have hNotGe : ¬ (Int.ofNat n ≥ HPow.hPow (2 : Int) 128) := by
      intro hGe
      have hP : Nat.pow 2 128 ≤ n :=
        int_ofNat_le_iff.mp (by change Int.ofNat (Nat.pow 2 128) ≤ _; exact hGe)
      exact Nat.not_le_of_gt hLt128 hP
    have hEqBv : truncateBits w (bvOfInt 128 (Int.ofNat n)) =
        bvOfInt 128 (Int.ofNat n) := by
      apply Anneal.BitVec.eq_of_toNat_eq
      rw [hMod, h128, nat_mod_eq_of_lt hLt, nat_mod_eq_of_lt hLt128]
    have hLossyFalse :
        (truncateBits w (bvOfInt 128 (Int.ofNat n)) !=
          bvOfInt 128 (Int.ofNat n)) = false := by
      change (!(truncateBits w (bvOfInt 128 (Int.ofNat n)) ==
          bvOfInt 128 (Int.ofNat n))) = false
      rw [hEqBv, beq_self_eq_true]
      rfl
    change (decide (Int.ofNat n < 0) ||
        decide (Int.ofNat n ≥ HPow.hPow (2 : Int) 128) ||
        (truncateBits w (bvOfInt 128 (Int.ofNat n)) !=
          bvOfInt 128 (Int.ofNat n))) =
      decide (M ≤ n)
    rw [hNotNeg, decide_eq_false hNotGe, hLossyFalse,
      decide_eq_false (Nat.not_le_of_gt hLt)]
    rfl
  | inr hGe =>
    rw [decide_eq_true hGe]
    cases Nat.lt_or_ge n (Nat.pow 2 128) with
    | inl hLt128 =>
      have hNeBv : truncateBits w (bvOfInt 128 (Int.ofNat n)) ≠
          bvOfInt 128 (Int.ofNat n) := by
        intro hEq
        have hNat := congrArg BitVec.toNat hEq
        rw [hMod, h128, nat_mod_eq_of_lt hLt128] at hNat
        have hLtM : Nat.mod n M < M := Nat.mod_lt _ (nat_two_pow_pos _)
        rw [hNat] at hLtM
        exact Nat.not_le_of_gt hLtM hGe
      have hLossyTrue :
          (truncateBits w (bvOfInt 128 (Int.ofNat n)) !=
            bvOfInt 128 (Int.ofNat n)) = true :=
        bne_iff_ne.mpr hNeBv
      change (decide (Int.ofNat n < 0) ||
          decide (Int.ofNat n ≥ HPow.hPow (2 : Int) 128) ||
          (truncateBits w (bvOfInt 128 (Int.ofNat n)) !=
            bvOfInt 128 (Int.ofNat n))) = true
      rw [hLossyTrue, Bool.or_true]
    | inr hGe128 =>
      have hGeI : Int.ofNat n ≥ HPow.hPow (2 : Int) 128 :=
        int_ofNat_le_iff.mpr hGe128
      change (decide (Int.ofNat n < 0) ||
          decide (Int.ofNat n ≥ HPow.hPow (2 : Int) 128) ||
          (truncateBits w (bvOfInt 128 (Int.ofNat n)) !=
            bvOfInt 128 (Int.ofNat n))) = true
      rw [decide_eq_true hGeI, Bool.or_true, Bool.true_or]

private theorem signed_int_overflow_flag_eq (w : IntWidth) (result : Int) :
    let hostOverflow :=
      decide (result < Neg.neg (HPow.hPow (2 : Int) 127)) ||
        decide (result ≥ HPow.hPow (2 : Int) 127)
    let trunc := truncateBits w (bvOfInt 128 result)
    let lossy :=
      signExtendBits w trunc != bvToInt (bvOfInt 128 result)
    (hostOverflow || lossy) =
      (decide (result < Neg.neg (Int.ofNat (Nat.pow 2 (8 * w.byteSize - 1)))) ||
        decide (Int.ofNat (Nat.pow 2 (8 * w.byteSize - 1)) ≤ result)) := by
  have hW : 0 < 8 * w.byteSize := by
    rw [← intWidth_bitWidth_eq_eight_mul]
    exact intWidth_bitWidth_pos w
  have hwLe : 8 * w.byteSize ≤ 128 := intWidth_bitWidth_le_128_eight w
  have hwSubLe : 8 * w.byteSize - 1 ≤ 127 := Nat.sub_le_sub_right hwLe 1
  have hHalfLe : Nat.pow 2 (8 * w.byteSize - 1) ≤ Nat.pow 2 127 :=
    Nat.pow_le_pow_right (by decide : 0 < 2) hwSubLe
  have hNegHalfGe :
      Neg.neg (HPow.hPow (2 : Int) 127) ≤
        Neg.neg (Int.ofNat (Nat.pow 2 (8 * w.byteSize - 1))) := by
    have hP27 : HPow.hPow (2 : Int) 127 = Int.ofNat (Nat.pow 2 127) := rfl
    rw [hP27]
    exact (intBalance_le_iff
      (intBalance_neg_of (Anneal.InitLemmas.intBalance_ofNat _))
      (intBalance_neg_of (Anneal.InitLemmas.intBalance_ofNat _))).mpr
      (by rw [Nat.zero_add, Nat.add_zero]; exact hHalfLe)
  let trunc := truncateBits w (bvOfInt 128 result)
  have hTruncEq : trunc = bvZeroExtend 128 (bvOfInt (8 * w.byteSize) result) :=
    truncateBits_bvOfInt_eq_bvZeroExtend w result
  have hDecEq : signExtendBits w trunc = bvToInt (bvOfInt (8 * w.byteSize) result) := by
    rw [hTruncEq, signExtendBits_bvZeroExtend]
  let hDecRange := bvToInt_in_width_range hW (bvOfInt (8 * w.byteSize) result)
  cases int_lt_or_ge result (Neg.neg (HPow.hPow (2 : Int) 127)) with
  | inl hLt127 =>
    have hLtW : result < Neg.neg (Int.ofNat (Nat.pow 2 (8 * w.byteSize - 1))) := by
      have hNeg := (intBalance_lt_iff (Anneal.InitLemmas.intBalance_self result)
        (intBalance_neg_of (Anneal.InitLemmas.intBalance_ofNat _))).mp hLt127
      have hLe := (intBalance_le_iff
        (intBalance_neg_of (Anneal.InitLemmas.intBalance_ofNat (Nat.pow 2 127)))
        (intBalance_neg_of (Anneal.InitLemmas.intBalance_ofNat
          (Nat.pow 2 (8 * w.byteSize - 1))))).mp hNegHalfGe
      rw [intBalance_lt_iff (Anneal.InitLemmas.intBalance_self result)
        (intBalance_neg_of (Anneal.InitLemmas.intBalance_ofNat _))]
      rw [Nat.zero_add, Nat.add_zero] at hLe
      have hSum := Nat.add_lt_add_right hNeg (Nat.pow 2 (8 * w.byteSize - 1))
      rw [Nat.zero_add, Nat.add_assoc, Nat.add_comm (Nat.pow 2 127),
        ← Nat.add_assoc] at hSum
      have hSumLe : Anneal.InitLemmas.intPos result +
          Nat.pow 2 (8 * w.byteSize - 1) + Nat.pow 2 127 <
          Anneal.InitLemmas.intNeg result + Nat.pow 2 127 :=
        Nat.lt_of_lt_of_le hSum (Nat.add_le_add_left hLe _)
      rw [Nat.zero_add]
      exact nat_lt_of_add_lt_add_right (c := Nat.pow 2 127) hSumLe
    change (decide (result < Neg.neg (HPow.hPow (2 : Int) 127)) ||
        decide (result ≥ HPow.hPow (2 : Int) 127) || _) =
      (decide (result < Neg.neg (Int.ofNat (Nat.pow 2 (8 * w.byteSize - 1)))) || _)
    rw [decide_eq_true hLt127, decide_eq_true hLtW, Bool.true_or, Bool.true_or,
      Bool.true_or]
  | inr hGeNeg127 =>
    cases int_lt_or_ge result (HPow.hPow (2 : Int) 127) with
    | inr hGe127 =>
      have hGeW : Int.ofNat (Nat.pow 2 (8 * w.byteSize - 1)) ≤ result := by
        have hP27 : HPow.hPow (2 : Int) 127 = Int.ofNat (Nat.pow 2 127) := rfl
        rw [hP27] at hGe127
        have h1 := (intBalance_le_iff (Anneal.InitLemmas.intBalance_ofNat _)
          (Anneal.InitLemmas.intBalance_self result)).mp hGe127
        rw [intBalance_le_iff (Anneal.InitLemmas.intBalance_ofNat _)
          (Anneal.InitLemmas.intBalance_self result), Nat.add_zero]
        rw [Nat.add_zero] at h1
        exact Nat.le_trans (Nat.add_le_add_right hHalfLe _) h1
      change (decide (result < Neg.neg (HPow.hPow (2 : Int) 127)) ||
          decide (result ≥ HPow.hPow (2 : Int) 127) || _) =
        (_ || decide (Int.ofNat (Nat.pow 2 (8 * w.byteSize - 1)) ≤ result))
      rw [decide_eq_true hGe127, decide_eq_true hGeW, Bool.or_true,
        Bool.or_true, Bool.true_or]
    | inl hLt127 =>
      have hHostFalse :
          (decide (result < Neg.neg (HPow.hPow (2 : Int) 127)) ||
            decide (result ≥ HPow.hPow (2 : Int) 127)) = false := by
        rw [decide_eq_false ((int_not_lt_iff_le _ _).mpr hGeNeg127),
          decide_eq_false ((int_not_le_iff_lt _ _).mpr hLt127)]
        rfl
      have h128 : bvToInt (bvOfInt 128 result) = result :=
        bvToInt_bvOfInt_eq_of_in_range (by decide : 0 < 128) hGeNeg127 hLt127
      change (decide (result < Neg.neg (HPow.hPow (2 : Int) 127)) ||
          decide (result ≥ HPow.hPow (2 : Int) 127) ||
          (signExtendBits w trunc != bvToInt (bvOfInt 128 result))) = _
      rw [hHostFalse, Bool.false_or, hDecEq, h128]
      cases int_lt_or_ge result
          (Neg.neg (Int.ofNat (Nat.pow 2 (8 * w.byteSize - 1)))) with
      | inl hLtW =>
        have hNe : bvToInt (bvOfInt (8 * w.byteSize) result) ≠ result := by
          intro hEq
          rw [hEq] at hDecRange
          exact (int_not_lt_iff_le _ _).mpr hDecRange.1 hLtW
        rw [decide_eq_true hLtW, Bool.true_or, bne_iff_ne.mpr hNe]
      | inr hGeNegW =>
        cases int_lt_or_ge result
            (Int.ofNat (Nat.pow 2 (8 * w.byteSize - 1))) with
        | inr hGeW =>
          have hNe : bvToInt (bvOfInt (8 * w.byteSize) result) ≠ result := by
            intro hEq
            rw [hEq] at hDecRange
            exact (int_not_le_iff_lt _ _).mpr hDecRange.2 hGeW
          rw [decide_eq_false ((int_not_lt_iff_le _ _).mpr hGeNegW),
            decide_eq_true hGeW, Bool.false_or, bne_iff_ne.mpr hNe]
        | inl hLtW =>
          have hEq : bvToInt (bvOfInt (8 * w.byteSize) result) = result :=
            bvToInt_bvOfInt_eq_of_in_range hW hGeNegW hLtW
          change (!(bvToInt (bvOfInt (8 * w.byteSize) result) == result)) = _
          rw [hEq, beq_self_eq_true,
            decide_eq_false ((int_not_lt_iff_le _ _).mpr hGeNegW),
            decide_eq_false ((int_not_le_iff_lt _ _).mpr hLtW)]
          rfl

/-- Unsigned `evalBinOp .mulWithOverflow` returns `(x * y, decide (2^(8 *
w.byteSize) ≤ x.toNat * y.toNat))` across all six widths (including `u128`). -/
theorem evalBinOp_mulWithOverflow_unsigned_eq (w : IntWidth)
    (x y : BitVec (8 * w.byteSize)) :
    evalBinOp .mulWithOverflow (.scalar (bvToScalar w false x))
        (.scalar (bvToScalar w false y)) =
      .ok (.tuple [
        .scalar (bvToScalar w false (Anneal.BitVec.mul x y)),
        .bool (decide (Nat.pow 2 (8 * w.byteSize) ≤ x.toNat * y.toNat))
      ]) := by
  unfold evalBinOp evalArithOp
  dsimp only
  rw [if_bool_false (rfl : BinOp.mulWithOverflow.isShift = false),
    bvToScalar_width, bvToScalar_width, bvToScalar_signed, bvToScalar_signed,
    if_bool_false (evalBinOp_header_eq w false),
    Bool.false_and, if_false_eq, Bool.false_and, Bool.false_and, if_false_eq,
    decodeScalar_unsigned_eq, decodeScalar_unsigned_eq]
  dsimp only [truncateScalar]
  rw [if_false_eq]
  dsimp only
  have hU : BinOp.mulWithOverflow.isUnchecked = false := rfl
  have hO : BinOp.mulWithOverflow.isOverflowing = true := rfl
  have hMulInt : Int.ofNat x.toNat * Int.ofNat y.toNat =
      Int.ofNat (x.toNat * y.toNat) := rfl
  rw [hU, hO, Bool.and_false, if_false_eq, if_true_eq, if_false_eq, hMulInt,
    unsigned_nat_overflow_flag_eq w (x.toNat * y.toNat)]
  have hBits : truncateBits w (bvOfInt 128 (Int.ofNat (x.toNat * y.toNat))) =
      bvZeroExtend 128 (Anneal.BitVec.mul x y) := by
    apply Anneal.BitVec.eq_of_toNat_eq
    rw [toNat_truncateBits_bvOfInt_ofNat,
      toNat_bvZeroExtend_of_le (intWidth_bitWidth_le_128_eight w),
      Anneal.BitVec.toNat_mul]
  change Except.ok (Val.tuple [Val.scalar ⟨w, false,
      truncateBits w (bvOfInt 128 (Int.ofNat (x.toNat * y.toNat)))⟩,
    Val.bool (decide (Nat.pow 2 (8 * w.byteSize) ≤ x.toNat * y.toNat))]) = _
  rw [hBits]
  rfl

/-- Unsigned `evalBinOp .mulUnchecked` succeeds with `x * y` iff
`x.toNat * y.toNat < 2^(8 * w.byteSize)` and faults with `.undefined`
otherwise (including `u128` overflow). -/
theorem evalBinOp_mulUnchecked_unsigned_eq (w : IntWidth)
    (x y : BitVec (8 * w.byteSize)) :
    evalBinOp .mulUnchecked (.scalar (bvToScalar w false x))
        (.scalar (bvToScalar w false y)) =
      if x.toNat * y.toNat < Nat.pow 2 (8 * w.byteSize) then
        .ok (.scalar (bvToScalar w false (Anneal.BitVec.mul x y)))
      else
        .error .undefined := by
  unfold evalBinOp evalArithOp
  dsimp only
  rw [if_bool_false (rfl : BinOp.mulUnchecked.isShift = false),
    bvToScalar_width, bvToScalar_width, bvToScalar_signed, bvToScalar_signed,
    if_bool_false (evalBinOp_header_eq w false),
    Bool.false_and, if_false_eq, Bool.false_and, Bool.false_and, if_false_eq,
    decodeScalar_unsigned_eq, decodeScalar_unsigned_eq]
  dsimp only [truncateScalar]
  rw [if_false_eq]
  dsimp only
  have hU : BinOp.mulUnchecked.isUnchecked = true := rfl
  have hMulInt : Int.ofNat x.toNat * Int.ofNat y.toNat =
      Int.ofNat (x.toNat * y.toNat) := rfl
  rw [hU, Bool.and_true, if_false_eq, hMulInt,
    unsigned_nat_overflow_flag_eq w (x.toNat * y.toNat)]
  cases Nat.lt_or_ge (x.toNat * y.toNat) (Nat.pow 2 (8 * w.byteSize)) with
  | inl hLt =>
    rw [Anneal.InitLemmas.ite_true_of hLt,
      decide_eq_false (Nat.not_le_of_gt hLt), if_false_eq]
    have hO : BinOp.mulUnchecked.isOverflowing = false := rfl
    rw [hO, if_false_eq]
    have hBits : truncateBits w (bvOfInt 128 (Int.ofNat (x.toNat * y.toNat))) =
        bvZeroExtend 128 (Anneal.BitVec.mul x y) := by
      apply Anneal.BitVec.eq_of_toNat_eq
      rw [toNat_truncateBits_bvOfInt_ofNat,
        toNat_bvZeroExtend_of_le (intWidth_bitWidth_le_128_eight w),
        Anneal.BitVec.toNat_mul]
    change Except.ok (Val.scalar ⟨w, false,
        truncateBits w (bvOfInt 128 (Int.ofNat (x.toNat * y.toNat)))⟩) = _
    rw [hBits]
    rfl
  | inr hGe =>
    rw [Anneal.InitLemmas.ite_false_of (Nat.not_lt_of_ge hGe),
      decide_eq_true hGe, if_true_eq]

/-- Bitvector signed-addition overflow predicate: equal sign bits flipping on
`(x + y)`. -/
@[expose] def signedOverflowAddBv {w : Nat} (x y : BitVec w) : Bool :=
  (Anneal.BitVecArith.msb x == Anneal.BitVecArith.msb y) &&
    (Anneal.BitVecArith.msb x != Anneal.BitVecArith.msb (x + y))

/-- Bitvector signed-subtraction overflow predicate: opposite sign bits where
`(x - y)` does not preserve `x`'s sign. -/
@[expose] def signedOverflowSubBv {w : Nat} (x y : BitVec w) : Bool :=
  (Anneal.BitVecArith.msb x != Anneal.BitVecArith.msb y) &&
    (Anneal.BitVecArith.msb x != Anneal.BitVecArith.msb (x - y))

/-- Bitvector signed-multiplication overflow predicate: `signExtend (2 * w)
x * signExtend (2 * w) y ≠ signExtend (2 * w) (x * y)` when `w > 0`. -/
@[expose] def signedOverflowMulBv {w : Nat} (x y : BitVec w) : Bool :=
  if w = 0 then
    false
  else
    Anneal.BitVec.mul (Anneal.BitVecArith.signExtend (2 * w) x)
        (Anneal.BitVecArith.signExtend (2 * w) y) !=
      Anneal.BitVecArith.signExtend (2 * w) (Anneal.BitVec.mul x y)

/-- Signed addition does not overflow (`signedOverflowAddBv x y = false`) iff
`2^(w - 1) ≤ signedKey x + signedKey y < 2^(w - 1) + 2^w`. -/
theorem signedOverflowAddBv_eq_false_iff {w : Nat} (hw : 0 < w)
    (x y : BitVec w) :
    signedOverflowAddBv x y = false ↔
      Nat.pow 2 (w - 1) ≤
          Anneal.BitVecArith.signedKey x + Anneal.BitVecArith.signedKey y ∧
        Anneal.BitVecArith.signedKey x + Anneal.BitVecArith.signedKey y <
          Nat.pow 2 (w - 1) + Nat.pow 2 w := by
  let H := Nat.pow 2 (w - 1)
  have hPow : Nat.pow 2 w = H + H := nat_two_pow_split hw
  unfold signedOverflowAddBv
  cases hmx : Anneal.BitVecArith.msb x <;>
    cases hmy : Anneal.BitVecArith.msb y
  · have hxLt : x.toNat < H :=
      (Anneal.BitVecArith.msb_eq_false_iff hw x).mp hmx
    have hyLt : y.toNat < H :=
      (Anneal.BitVecArith.msb_eq_false_iff hw y).mp hmy
    have hSumLt : x.toNat + y.toNat < Nat.pow 2 w := by
      rw [hPow]
      exact Nat.add_lt_add hxLt hyLt
    have hToNat : (x + y).toNat = x.toNat + y.toNat := by
      rw [Anneal.BitVec.toNat_add, nat_mod_eq_of_lt hSumLt]
    have hkx := Anneal.BitVecArith.signedKey_eq_of_msb_false hw hmx
    have hky := Anneal.BitVecArith.signedKey_eq_of_msb_false hw hmy
    have hNoUdf : H ≤ Anneal.BitVecArith.signedKey x +
        Anneal.BitVecArith.signedKey y := by
      rw [hkx]
      exact Nat.le_trans (Nat.le_add_left H x.toNat) (Nat.le_add_right _ _)
    constructor
    · intro hF
      refine ⟨hNoUdf, ?_⟩
      have hmz : Anneal.BitVecArith.msb (x + y) = false := by
        cases hmz' : Anneal.BitVecArith.msb (x + y) with
        | false => rfl
        | true => rw [hmz'] at hF; nomatch hF
      have hzLt := (Anneal.BitVecArith.msb_eq_false_iff hw (x + y)).mp hmz
      rw [hToNat] at hzLt
      rw [hkx, hky, hPow]
      have h1 : x.toNat + H + (y.toNat + H) =
          (x.toNat + y.toNat) + (H + H) := by
        rw [Nat.add_assoc x.toNat H (y.toNat + H),
          Nat.add_comm H (y.toNat + H), Nat.add_assoc y.toNat H H,
          ← Nat.add_assoc x.toNat y.toNat (H + H)]
      rw [h1]
      exact Nat.add_lt_add_right hzLt (H + H)
    · intro ⟨_, hNoOvf⟩
      have hxyLt : x.toNat + y.toNat < H := by
        rw [hkx, hky, hPow] at hNoOvf
        have h1 : (x.toNat + y.toNat) + (H + H) < H + (H + H) := by
          have hL : x.toNat + H + (y.toNat + H) =
              (x.toNat + y.toNat) + (H + H) := by
            rw [Nat.add_assoc x.toNat H (y.toNat + H),
              Nat.add_comm H (y.toNat + H), Nat.add_assoc y.toNat H H,
              ← Nat.add_assoc x.toNat y.toNat (H + H)]
          have hNoOvf' : x.toNat + H + (y.toNat + H) < H + (H + H) := hNoOvf
          rw [hL] at hNoOvf'
          exact hNoOvf'
        exact nat_lt_of_add_lt_add_right h1
      have hmz : Anneal.BitVecArith.msb (x + y) = false :=
        (Anneal.BitVecArith.msb_eq_false_iff hw (x + y)).mpr
          (by rw [hToNat]; exact hxyLt)
      rw [hmz]
      rfl
  · constructor
    · intro _
      have hkxGe := Anneal.BitVecArith.half_le_signedKey_of_msb_false hw hmx
      have hkyLt := Anneal.BitVecArith.signedKey_lt_half_of_msb_true hw hmy
      have hkxLt := Anneal.BitVecArith.signedKey_lt x
      refine ⟨Nat.le_trans hkxGe (Nat.le_add_right _ _), ?_⟩
      rw [Nat.add_comm H (Nat.pow 2 w)]
      exact Nat.add_lt_add hkxLt hkyLt
    · intro _; rfl
  · constructor
    · intro _
      have hkxLt := Anneal.BitVecArith.signedKey_lt_half_of_msb_true hw hmx
      have hkyGe := Anneal.BitVecArith.half_le_signedKey_of_msb_false hw hmy
      have hkyLt := Anneal.BitVecArith.signedKey_lt y
      refine ⟨Nat.le_trans hkyGe (Nat.le_add_left _ _), ?_⟩
      exact Nat.add_lt_add hkxLt hkyLt
    · intro _; rfl
  · have hxGe := (Anneal.BitVecArith.msb_eq_true_iff hw x).mp hmx
    have hyGe := (Anneal.BitVecArith.msb_eq_true_iff hw y).mp hmy
    have hSumGe : Nat.pow 2 w ≤ x.toNat + y.toNat := by
      rw [hPow]
      exact Nat.add_le_add hxGe hyGe
    have hSumLt : x.toNat + y.toNat < Nat.pow 2 w + Nat.pow 2 w :=
      Nat.add_lt_add (bitVec_toNat_lt_pow x) (bitVec_toNat_lt_pow y)
    have hToNat : (x + y).toNat = x.toNat + y.toNat - Nat.pow 2 w := by
      have hSplit : x.toNat + y.toNat =
          (x.toNat + y.toNat - Nat.pow 2 w) + Nat.pow 2 w :=
        Eq.symm (Nat.sub_add_cancel hSumGe)
      have hSubLt : x.toNat + y.toNat - Nat.pow 2 w < Nat.pow 2 w := by
        apply nat_lt_of_add_lt_add_right (c := Nat.pow 2 w)
        rw [Nat.sub_add_cancel hSumGe]
        exact hSumLt
      rw [Anneal.BitVec.toNat_add, hSplit, nat_add_mod_right,
        nat_mod_eq_of_lt hSubLt, Nat.add_sub_cancel]
    have hkx := Anneal.BitVecArith.signedKey_eq_of_msb_true hw hmx
    have hky := Anneal.BitVecArith.signedKey_eq_of_msb_true hw hmy
    have hkxLt := Anneal.BitVecArith.signedKey_lt_half_of_msb_true hw hmx
    have hkyLt := Anneal.BitVecArith.signedKey_lt_half_of_msb_true hw hmy
    have hNoOvf : Anneal.BitVecArith.signedKey x +
        Anneal.BitVecArith.signedKey y < H + Nat.pow 2 w := by
      rw [hPow, ← Nat.add_assoc]
      exact Nat.lt_of_lt_of_le (Nat.add_lt_add hkxLt hkyLt)
        (Nat.le_add_right _ _)
    constructor
    · intro hF
      refine ⟨?_, hNoOvf⟩
      have hmz : Anneal.BitVecArith.msb (x + y) = true := by
        cases hmz' : Anneal.BitVecArith.msb (x + y) with
        | true => rfl
        | false => rw [hmz'] at hF; nomatch hF
      have hzGe := (Anneal.BitVecArith.msb_eq_true_iff hw (x + y)).mp hmz
      rw [hToNat] at hzGe
      have hSumGe3 : H + Nat.pow 2 w ≤ x.toNat + y.toNat := by
        have h1 := Nat.add_le_add_right hzGe (Nat.pow 2 w)
        rw [Nat.sub_add_cancel hSumGe] at h1
        exact h1
      rw [hkx, hky]
      apply nat_le_of_add_le_add_right (c := H + H)
      have hLclean : (x.toNat - H + (y.toNat - H)) + (H + H) =
          x.toNat + y.toNat := by
        rw [Nat.add_assoc (x.toNat - H) (y.toNat - H) (H + H),
          ← Nat.add_assoc (y.toNat - H) H H, Nat.sub_add_cancel hyGe,
          Nat.add_comm y.toNat H, ← Nat.add_assoc (x.toNat - H) H y.toNat,
          Nat.sub_add_cancel hxGe]
      rw [hLclean, ← hPow]
      exact hSumGe3
    · intro ⟨hNoUdf, _⟩
      have hmz : Anneal.BitVecArith.msb (x + y) = true := by
        rw [Anneal.BitVecArith.msb_eq_true_iff hw (x + y), hToNat]
        apply nat_le_of_add_le_add_right (c := Nat.pow 2 w)
        rw [Nat.sub_add_cancel hSumGe]
        have hLclean : (x.toNat - H + (y.toNat - H)) + (H + H) =
            x.toNat + y.toNat := by
          rw [Nat.add_assoc (x.toNat - H) (y.toNat - H) (H + H),
            ← Nat.add_assoc (y.toNat - H) H H, Nat.sub_add_cancel hyGe,
            Nat.add_comm y.toNat H, ← Nat.add_assoc (x.toNat - H) H y.toNat,
            Nat.sub_add_cancel hxGe]
        rw [hkx, hky] at hNoUdf
        have h1 := Nat.add_le_add_right hNoUdf (H + H)
        rw [hLclean, ← hPow] at h1
        exact h1
      rw [hmz]
      rfl

/-- Exact `signedKey` of overflow-free and underflow-free signed subtraction
(`signedKey y ≤ signedKey x + 2^(w - 1)` and `signedKey x < signedKey y +
2^(w - 1)`). -/
theorem signedKey_sub_no_overflow {w : Nat} (hw : 0 < w) {a b : BitVec w}
    (hno_udf : Anneal.BitVecArith.signedKey b ≤
      Anneal.BitVecArith.signedKey a + Nat.pow 2 (w - 1))
    (hno_ovf : Anneal.BitVecArith.signedKey a <
      Anneal.BitVecArith.signedKey b + Nat.pow 2 (w - 1)) :
    Anneal.BitVecArith.signedKey (a - b) =
      Anneal.BitVecArith.signedKey a + Nat.pow 2 (w - 1) -
        Anneal.BitVecArith.signedKey b := by
  let H := Nat.pow 2 (w - 1)
  have hB := intBalance_sub_of (intBalance_bvToInt hw a) (intBalance_bvToInt hw b)
  have hLo : Neg.neg (Int.ofNat H) ≤ bvToInt a - bvToInt b := by
    rw [intBalance_le_iff (intBalance_neg_of (Anneal.InitLemmas.intBalance_ofNat H)) hB,
      Nat.zero_add,
      Nat.add_comm (Anneal.BitVecArith.signedKey a + Nat.pow 2 (w - 1)) H]
    exact Nat.add_le_add_left hno_udf H
  have hHi : bvToInt a - bvToInt b < Int.ofNat H := by
    rw [intBalance_lt_iff hB (Anneal.InitLemmas.intBalance_ofNat H),
      Nat.add_zero,
      Nat.add_comm H (Nat.pow 2 (w - 1) + Anneal.BitVecArith.signedKey b),
      Nat.add_comm (Nat.pow 2 (w - 1)) (Anneal.BitVecArith.signedKey b)]
    exact Nat.add_lt_add_right hno_ovf H
  have hBv : bvToInt (a - b) = bvToInt a - bvToInt b := by
    rw [← bvOfInt_bvToInt_sub hw a b]
    exact bvToInt_bvOfInt_eq_of_in_range hw hLo hHi
  have hEq := (intBalance_eq_iff (intBalance_bvToInt hw (a - b)) hB).mp hBv
  have hCancel : (Anneal.BitVecArith.signedKey (a - b) +
      Anneal.BitVecArith.signedKey b) + H =
      (Anneal.BitVecArith.signedKey a + H) + H := by
    rw [Nat.add_assoc, Nat.add_comm (Anneal.BitVecArith.signedKey b) H, hEq]
  have hSub := congrArg (fun z => z - Anneal.BitVecArith.signedKey b)
    (Nat.add_right_cancel hCancel)
  rw [Nat.add_sub_cancel] at hSub
  exact hSub

/-- Signed subtraction does not overflow (`signedOverflowSubBv x y = false`) iff
`signedKey y ≤ signedKey x + 2^(w - 1)` and `signedKey x < signedKey y +
2^(w - 1)`. -/
theorem signedOverflowSubBv_eq_false_iff {w : Nat} (hw : 0 < w)
    (x y : BitVec w) :
    signedOverflowSubBv x y = false ↔
      Anneal.BitVecArith.signedKey y ≤
          Anneal.BitVecArith.signedKey x + Nat.pow 2 (w - 1) ∧
        Anneal.BitVecArith.signedKey x <
          Anneal.BitVecArith.signedKey y + Nat.pow 2 (w - 1) := by
  let H := Nat.pow 2 (w - 1)
  have hPow : Nat.pow 2 w = H + H := nat_two_pow_split hw
  unfold signedOverflowSubBv
  cases hmx : Anneal.BitVecArith.msb x <;>
    cases hmy : Anneal.BitVecArith.msb y
  · have hkxLt := Anneal.BitVecArith.signedKey_lt x
    have hkyLt := Anneal.BitVecArith.signedKey_lt y
    have hkxGe := Anneal.BitVecArith.half_le_signedKey_of_msb_false hw hmx
    have hkyGe := Anneal.BitVecArith.half_le_signedKey_of_msb_false hw hmy
    rw [hPow] at hkxLt hkyLt
    exact ⟨fun _ => ⟨Nat.le_trans (Nat.le_of_lt hkyLt) (Nat.add_le_add_right hkxGe H),
      Nat.lt_of_lt_of_le hkxLt (Nat.add_le_add_right hkyGe H)⟩, fun _ => rfl⟩
  · have hxLt : x.toNat < H :=
      (Anneal.BitVecArith.msb_eq_false_iff hw x).mp hmx
    have hyGe := (Anneal.BitVecArith.msb_eq_true_iff hw y).mp hmy
    have hkx := Anneal.BitVecArith.signedKey_eq_of_msb_false hw hmx
    have hky := Anneal.BitVecArith.signedKey_eq_of_msb_true hw hmy
    have hNoUdf : Anneal.BitVecArith.signedKey y ≤
        Anneal.BitVecArith.signedKey x + H := by
      have hkyLt := Anneal.BitVecArith.signedKey_lt_half_of_msb_true hw hmy
      have hkxGe := Anneal.BitVecArith.half_le_signedKey_of_msb_false hw hmx
      exact Nat.le_trans (Nat.le_of_lt hkyLt) (Nat.le_trans hkxGe (Nat.le_add_right _ _))
    have hyLt : y.toNat < Nat.pow 2 w := bitVec_toNat_lt_pow y
    have hyLeW : y.toNat ≤ Nat.pow 2 w := Nat.le_of_lt hyLt
    have hSubVal : (x - y).toNat = (Nat.pow 2 w - y.toNat) + x.toNat := by
      have hAddLt : (Nat.pow 2 w - y.toNat) + x.toNat < Nat.pow 2 w := by
        apply nat_lt_of_add_lt_add_right (c := y.toNat)
        rw [Nat.add_assoc (Nat.pow 2 w - y.toNat) x.toNat y.toNat,
          Nat.add_comm x.toNat y.toNat,
          ← Nat.add_assoc (Nat.pow 2 w - y.toNat) y.toNat x.toNat,
          Nat.sub_add_cancel hyLeW]
        exact Nat.lt_of_lt_of_le (Nat.add_lt_add_left hxLt (Nat.pow 2 w))
          (Nat.add_le_add_left hyGe (Nat.pow 2 w))
      rw [Anneal.BitVec.toNat_sub, nat_mod_eq_of_lt hAddLt]
    have hyLeHH : y.toNat ≤ H + H := by
      rw [← hPow]
      exact hyLeW
    constructor
    · intro hF
      refine ⟨hNoUdf, ?_⟩
      have hmz : Anneal.BitVecArith.msb (x - y) = false := by
        cases hmz' : Anneal.BitVecArith.msb (x - y) with
        | false => rfl
        | true => rw [hmz'] at hF; nomatch hF
      have hzLt := (Anneal.BitVecArith.msb_eq_false_iff hw (x - y)).mp hmz
      rw [hSubVal, hPow] at hzLt
      have hAdd : (H + H) + x.toNat < H + y.toNat := by
        have h1 := Nat.add_lt_add_right hzLt y.toNat
        rw [Nat.add_assoc (H + H - y.toNat) x.toNat y.toNat,
          Nat.add_comm x.toNat y.toNat,
          ← Nat.add_assoc (H + H - y.toNat) y.toNat x.toNat,
          Nat.sub_add_cancel hyLeHH] at h1
        exact h1
      rw [hkx, hky, Nat.sub_add_cancel hyGe]
      rw [Nat.add_assoc H H x.toNat, Nat.add_comm H x.toNat] at hAdd
      exact nat_lt_of_add_lt_add_left hAdd
    · intro ⟨_, hNoOvf⟩
      rw [hkx, hky, Nat.sub_add_cancel hyGe] at hNoOvf
      have hzLt : (x - y).toNat < H := by
        rw [hSubVal, hPow]
        apply nat_lt_of_add_lt_add_right (c := y.toNat)
        rw [Nat.add_assoc (H + H - y.toNat) x.toNat y.toNat,
          Nat.add_comm x.toNat y.toNat,
          ← Nat.add_assoc (H + H - y.toNat) y.toNat x.toNat,
          Nat.sub_add_cancel hyLeHH, Nat.add_assoc H H x.toNat,
          Nat.add_comm H x.toNat, Nat.add_comm H (x.toNat + H),
          Nat.add_comm H y.toNat]
        exact Nat.add_lt_add_right hNoOvf H
      have hmz := (Anneal.BitVecArith.msb_eq_false_iff hw (x - y)).mpr hzLt
      rw [hmz]
      rfl
  · have hxGe := (Anneal.BitVecArith.msb_eq_true_iff hw x).mp hmx
    have hyLt : y.toNat < H :=
      (Anneal.BitVecArith.msb_eq_false_iff hw y).mp hmy
    have hkx := Anneal.BitVecArith.signedKey_eq_of_msb_true hw hmx
    have hky := Anneal.BitVecArith.signedKey_eq_of_msb_false hw hmy
    have hNoOvf : Anneal.BitVecArith.signedKey x <
        Anneal.BitVecArith.signedKey y + H := by
      have hkxLt := Anneal.BitVecArith.signedKey_lt_half_of_msb_true hw hmx
      have hkyGe := Anneal.BitVecArith.half_le_signedKey_of_msb_false hw hmy
      exact Nat.lt_of_lt_of_le hkxLt (Nat.le_trans hkyGe (Nat.le_add_right _ _))
    have hyLeX : y.toNat ≤ x.toNat := Nat.le_trans (Nat.le_of_lt hyLt) hxGe
    have hyLeW : y.toNat ≤ Nat.pow 2 w :=
      Nat.le_of_lt (bitVec_toNat_lt_pow y)
    have hSubVal : (x - y).toNat = x.toNat - y.toNat := by
      have hAdd : Nat.pow 2 w - y.toNat + x.toNat =
          (x.toNat - y.toNat) + Nat.pow 2 w := by
        apply Nat.add_right_cancel (m := y.toNat)
        rw [Nat.add_assoc (Nat.pow 2 w - y.toNat) x.toNat y.toNat,
          Nat.add_comm x.toNat y.toNat,
          ← Nat.add_assoc (Nat.pow 2 w - y.toNat) y.toNat x.toNat,
          Nat.sub_add_cancel hyLeW,
          Nat.add_assoc (x.toNat - y.toNat) (Nat.pow 2 w) y.toNat,
          Nat.add_comm (Nat.pow 2 w) y.toNat,
          ← Nat.add_assoc (x.toNat - y.toNat) y.toNat (Nat.pow 2 w),
          Nat.sub_add_cancel hyLeX, Nat.add_comm]
      rw [Anneal.BitVec.toNat_sub, hAdd, nat_add_mod_right,
        nat_mod_eq_of_lt (Nat.lt_of_le_of_lt (Nat.sub_le _ _)
          (bitVec_toNat_lt_pow x))]
    constructor
    · intro hF
      refine ⟨?_, hNoOvf⟩
      have hmz : Anneal.BitVecArith.msb (x - y) = true := by
        cases hmz' : Anneal.BitVecArith.msb (x - y) with
        | true => rfl
        | false => rw [hmz'] at hF; nomatch hF
      have hzGe := (Anneal.BitVecArith.msb_eq_true_iff hw (x - y)).mp hmz
      rw [hSubVal] at hzGe
      have hSum := Nat.add_le_add_right hzGe y.toNat
      rw [Nat.sub_add_cancel hyLeX, Nat.add_comm H y.toNat] at hSum
      rw [hkx, hky, Nat.sub_add_cancel hxGe]
      exact hSum
    · intro ⟨hNoUdf, _⟩
      rw [hkx, hky, Nat.sub_add_cancel hxGe] at hNoUdf
      have hzGe : H ≤ (x - y).toNat := by
        rw [hSubVal]
        apply nat_le_of_add_le_add_right (c := y.toNat)
        rw [Nat.sub_add_cancel hyLeX, Nat.add_comm H y.toNat]
        exact hNoUdf
      have hmz := (Anneal.BitVecArith.msb_eq_true_iff hw (x - y)).mpr hzGe
      rw [hmz]
      rfl
  · have hkxLt := Anneal.BitVecArith.signedKey_lt_half_of_msb_true hw hmx
    have hkyLt := Anneal.BitVecArith.signedKey_lt_half_of_msb_true hw hmy
    exact ⟨fun _ => ⟨Nat.le_trans (Nat.le_of_lt hkyLt) (Nat.le_add_left _ _),
      Nat.lt_of_lt_of_le hkxLt (Nat.le_add_left _ _)⟩, fun _ => rfl⟩

private theorem signedOverflowAddBv_eq_int_overflow {w : Nat} (hw : 0 < w)
    (x y : BitVec w) :
    signedOverflowAddBv x y =
      (decide (bvToInt x + bvToInt y < Neg.neg (Int.ofNat (Nat.pow 2 (w - 1)))) ||
        decide (Int.ofNat (Nat.pow 2 (w - 1)) ≤ bvToInt x + bvToInt y)) := by
  let H := Nat.pow 2 (w - 1)
  have hPow : Nat.pow 2 w = H + H := nat_two_pow_split hw
  have hB := intBalance_add_of (intBalance_bvToInt hw x) (intBalance_bvToInt hw y)
  have hNeg := intBalance_neg_of (Anneal.InitLemmas.intBalance_ofNat H)
  have hPos := Anneal.InitLemmas.intBalance_ofNat H
  have hLo : bvToInt x + bvToInt y < Neg.neg (Int.ofNat H) ↔
      Anneal.BitVecArith.signedKey x + Anneal.BitVecArith.signedKey y < H := by
    rw [intBalance_lt_iff hB hNeg, Nat.zero_add]
    exact ⟨fun h => nat_lt_of_add_lt_add_right (c := H) h,
      fun h => Nat.add_lt_add_right h H⟩
  have hHi : Int.ofNat H ≤ bvToInt x + bvToInt y ↔
      H + Nat.pow 2 w ≤
        Anneal.BitVecArith.signedKey x + Anneal.BitVecArith.signedKey y := by
    rw [intBalance_le_iff hPos hB, Nat.add_zero, hPow]
  cases hOv : signedOverflowAddBv x y with
  | false =>
    have hBounds := (signedOverflowAddBv_eq_false_iff hw x y).mp hOv
    rw [decide_eq_false (fun h => Nat.not_le_of_gt (hLo.mp h) hBounds.1),
      decide_eq_false (fun h => Nat.not_le_of_gt hBounds.2 (hHi.mp h))]
    rfl
  | true =>
    cases Nat.lt_or_ge
        (Anneal.BitVecArith.signedKey x + Anneal.BitVecArith.signedKey y) H with
    | inl hLt =>
      rw [decide_eq_true (hLo.mpr hLt), Bool.true_or]
    | inr hGe =>
      cases Nat.lt_or_ge
          (Anneal.BitVecArith.signedKey x + Anneal.BitVecArith.signedKey y)
          (H + Nat.pow 2 w) with
      | inl hLt2 =>
        have hF := (signedOverflowAddBv_eq_false_iff hw x y).mpr ⟨hGe, hLt2⟩
        rw [hF] at hOv
        nomatch hOv
      | inr hGe2 =>
        rw [decide_eq_true (hHi.mpr hGe2), Bool.or_true]

private theorem signedOverflowSubBv_eq_int_overflow {w : Nat} (hw : 0 < w)
    (x y : BitVec w) :
    signedOverflowSubBv x y =
      (decide (bvToInt x - bvToInt y < Neg.neg (Int.ofNat (Nat.pow 2 (w - 1)))) ||
        decide (Int.ofNat (Nat.pow 2 (w - 1)) ≤ bvToInt x - bvToInt y)) := by
  let H := Nat.pow 2 (w - 1)
  have hB := intBalance_sub_of (intBalance_bvToInt hw x) (intBalance_bvToInt hw y)
  have hNeg := intBalance_neg_of (Anneal.InitLemmas.intBalance_ofNat H)
  have hPos := Anneal.InitLemmas.intBalance_ofNat H
  have hLo : bvToInt x - bvToInt y < Neg.neg (Int.ofNat H) ↔
      Anneal.BitVecArith.signedKey x + H < Anneal.BitVecArith.signedKey y := by
    rw [intBalance_lt_iff hB hNeg, Nat.zero_add,
      Nat.add_comm H (Anneal.BitVecArith.signedKey y)]
    exact ⟨fun h => nat_lt_of_add_lt_add_right (c := H) h,
      fun h => Nat.add_lt_add_right h H⟩
  have hHi : Int.ofNat H ≤ bvToInt x - bvToInt y ↔
      Anneal.BitVecArith.signedKey y + H ≤ Anneal.BitVecArith.signedKey x := by
    rw [intBalance_le_iff hPos hB, Nat.add_zero,
      Nat.add_comm (Nat.pow 2 (w - 1)) (Anneal.BitVecArith.signedKey y),
      Nat.add_comm H (Anneal.BitVecArith.signedKey y + Nat.pow 2 (w - 1))]
    exact ⟨fun h => nat_le_of_add_le_add_right (c := H) h,
      fun h => Nat.add_le_add_right h H⟩
  cases hOv : signedOverflowSubBv x y with
  | false =>
    have hBounds := (signedOverflowSubBv_eq_false_iff hw x y).mp hOv
    rw [decide_eq_false (fun h => Nat.not_le_of_gt (hLo.mp h) hBounds.1),
      decide_eq_false (fun h => Nat.not_le_of_gt hBounds.2 (hHi.mp h))]
    rfl
  | true =>
    cases Nat.lt_or_ge
        (Anneal.BitVecArith.signedKey x + H) (Anneal.BitVecArith.signedKey y) with
    | inl hLt =>
      rw [decide_eq_true (hLo.mpr hLt), Bool.true_or]
    | inr hGe =>
      cases Nat.lt_or_ge
          (Anneal.BitVecArith.signedKey x) (Anneal.BitVecArith.signedKey y + H) with
      | inl hLt2 =>
        have hF := (signedOverflowSubBv_eq_false_iff hw x y).mpr ⟨hGe, hLt2⟩
        rw [hF] at hOv
        nomatch hOv
      | inr hGe2 =>
        rw [decide_eq_true (hHi.mpr hGe2), Bool.or_true]

private theorem bvOfInt_neg_ofNat {W : Nat} (k : Nat) :
    bvOfInt W (Neg.neg (Int.ofNat k)) = Anneal.BitVecArith.neg (BitVec.ofNat W k) := by
  let P := Nat.pow 2 W
  have hPpos : 0 < P := nat_two_pow_pos W
  apply Anneal.BitVec.eq_of_toNat_eq
  rw [Anneal.BitVecArith.toNat_neg, Anneal.BitVec.toNat_ofNat]
  cases k with
  | zero =>
    rw [nat_zero_mod, Nat.sub_zero, nat_mod_self]
    rfl
  | succ k' =>
    change (bvOfInt W (Int.negSucc k')).toNat = _
    rw [toNat_bvOfInt_negSucc]
    have h1 : Nat.succ k' = P * Nat.div (Nat.succ k') P +
        Nat.mod (Nat.succ k') P :=
      (nat_div_add_mod (Nat.succ k') P).symm
    cases hm : Nat.mod (Nat.succ k') P with
    | zero =>
      rw [Nat.sub_zero, nat_mod_self]
      -- `k' + 1 = P * q` with `q ≥ 1` so `k' = P * (q - 1) + (P - 1)`.
      have hDivPos : 0 < Nat.div (Nat.succ k') P := by
        cases hq : Nat.div (Nat.succ k') P with
        | zero =>
          rw [hq, hm, Nat.mul_zero, Nat.zero_add] at h1
          nomatch h1
        | succ _ => exact Nat.zero_lt_succ _
      have hSplit : k' = P * (Nat.div (Nat.succ k') P - 1) + (P - 1) := by
        have hMul : P * Nat.div (Nat.succ k') P =
            P * (Nat.div (Nat.succ k') P - 1) + P := by
          have hC := Nat.sub_add_cancel hDivPos
          have hM := congrArg (fun z => P * z) hC
          rw [Nat.mul_add, Nat.mul_one] at hM
          exact hM.symm
        rw [hm, Nat.add_zero, hMul] at h1
        have hSub := congrArg (fun z => z - 1) h1
        change (k' + 1) - 1 = _ at hSub
        rw [Nat.add_sub_cancel, Nat.add_sub_assoc hPpos] at hSub
        exact hSub
      rw [hSplit, Nat.add_comm (P * _) (P - 1), Nat.mul_comm P _,
        nat_add_mul_mod_self_left,
        nat_mod_eq_of_lt (Nat.sub_lt hPpos Nat.one_pos)]
      change Nat.pow 2 W - ((P - 1) + 1) = 0
      rw [Nat.sub_add_cancel hPpos, Nat.sub_self]
    | succ r =>
      have hrLt : r + 1 < P := by
        rw [← hm]
        exact Nat.mod_lt _ hPpos
      have hkMod : Nat.mod k' P = r := by
        have hEq : k' = r + P * Nat.div (Nat.succ k') P := by
          rw [hm] at h1
          have hSub := congrArg (fun z => z - 1) h1
          change (k' + 1) - 1 = _ at hSub
          rw [Nat.add_sub_cancel, ← Nat.add_assoc (P * Nat.div (Nat.succ k') P) r 1,
            Nat.add_sub_cancel, Nat.add_comm (P * _) r] at hSub
          exact hSub
        rw [hEq, Nat.mul_comm P _, nat_add_mul_mod_self_left,
          nat_mod_eq_of_lt (Nat.lt_of_succ_lt hrLt)]
      rw [hkMod]
      exact (nat_mod_eq_of_lt (Nat.sub_lt hPpos (Nat.zero_lt_succ r))).symm

private theorem bvOfInt_mul (W : Nat) (a b : Int) :
    bvOfInt W (a * b) = Anneal.BitVec.mul (bvOfInt W a) (bvOfInt W b) := by
  let P := Nat.pow 2 W
  have hPpos : 0 < P := nat_two_pow_pos W
  apply Anneal.BitVec.eq_of_toNat_eq
  rw [Anneal.BitVec.toNat_mul]
  cases a with
  | ofNat m =>
    cases b with
    | ofNat n =>
      rw [toNat_bvOfInt_ofNat, toNat_bvOfInt_ofNat,
        show Int.ofNat m * Int.ofNat n = Int.ofNat (m * n) from rfl,
        toNat_bvOfInt_ofNat, nat_mul_mod]
    | negSucc n =>
      have hMul : Int.ofNat m * Int.negSucc n =
          Neg.neg (Int.ofNat (m * (n + 1))) := by
        change Int.negOfNat (m * (n + 1)) = Neg.neg (Int.ofNat (m * (n + 1)))
        cases m * (n + 1) <;> rfl
      rw [hMul, bvOfInt_neg_ofNat, Anneal.BitVecArith.toNat_neg,
        Anneal.BitVec.toNat_ofNat, toNat_bvOfInt_ofNat, toNat_bvOfInt_negSucc]
      let am := Nat.mod m P
      let bn := Nat.succ (Nat.mod n P)
      have hbnLe : bn ≤ P := Nat.mod_lt n hPpos
      have h1 : am * (P - bn) + am * bn = am * P := by
        rw [← Nat.mul_add, Nat.sub_add_cancel hbnLe]
      have hMod1 : Nat.mod (am * (P - bn) + m * (n + 1)) P = 0 := by
        rw [nat_add_mod (am * (P - bn)) (m * (n + 1)) P]
        have hMmod : Nat.mod (m * (n + 1)) P = Nat.mod (am * bn) P := by
          have hSuccMod : Nat.mod (n + 1) P = Nat.mod bn P := by
            have hSplit := nat_div_add_mod n P
            have hC := congrArg (fun z => z + 1) hSplit.symm
            rw [Nat.add_assoc (P * Nat.div n P) (Nat.mod n P) 1,
              Nat.add_comm (P * Nat.div n P) (Nat.mod n P + 1)] at hC
            change Nat.mod (n + 1) P = Nat.mod bn P
            rw [hC, Nat.mul_comm P _, nat_add_mul_mod_self_left]
          rw [← nat_mul_mod_cancel_left m (n + 1) P]
          change Nat.mod (am * (n + 1)) P = Nat.mod (am * bn) P
          rw [← nat_mul_mod_cancel_right am (n + 1) P, hSuccMod,
            nat_mul_mod_cancel_right]
        rw [hMmod, ← nat_add_mod (am * (P - bn)) (am * bn) P, h1,
          nat_mul_mod_right]
      have hMod2 : Nat.mod (Nat.mod (P - Nat.mod (m * (n + 1)) P) P +
          m * (n + 1)) P = 0 := by
        rw [nat_add_mod, nat_mod_mod, ← nat_add_mod]
        have hSubLe : Nat.mod (m * (n + 1)) P ≤ P :=
          Nat.le_of_lt (Nat.mod_lt _ hPpos)
        have hSplit := nat_div_add_mod (m * (n + 1)) P
        have hSum : (P - Nat.mod (m * (n + 1)) P) + m * (n + 1) =
            P + P * Nat.div (m * (n + 1)) P := by
          have hC := congrArg (fun z => (P - Nat.mod (m * (n + 1)) P) + z)
            hSplit.symm
          rw [← Nat.add_assoc,
            Nat.add_comm (P - Nat.mod (m * (n + 1)) P)
              (P * Nat.div (m * (n + 1)) P),
            Nat.add_assoc, Nat.sub_add_cancel hSubLe,
            Nat.add_comm (P * Nat.div (m * (n + 1)) P) P] at hC
          exact hC
        rw [hSum, Nat.mul_comm P _, nat_add_mul_mod_self_left, nat_mod_self]
      have hL := congrArg (fun z => Nat.mod (z + m * (n + 1)) P)
        (nat_mod_mod (am * (P - bn)) P).symm
      rw [nat_add_mod (Nat.mod (am * (P - bn)) P) (m * (n + 1)) P,
        nat_mod_mod, ← nat_add_mod (am * (P - bn)) (m * (n + 1)) P, hMod1] at hL
      exact nat_eq_of_mod_add_right
        (Nat.mod_lt _ hPpos) (Nat.mod_lt _ hPpos) (hMod2.trans hL)
  | negSucc m =>
    cases b with
    | ofNat n =>
      have hMul : Int.negSucc m * Int.ofNat n =
          Neg.neg (Int.ofNat ((m + 1) * n)) := by
        change Int.negOfNat ((m + 1) * n) = Neg.neg (Int.ofNat ((m + 1) * n))
        cases (m + 1) * n <;> rfl
      rw [hMul, bvOfInt_neg_ofNat, Anneal.BitVecArith.toNat_neg,
        Anneal.BitVec.toNat_ofNat, toNat_bvOfInt_negSucc, toNat_bvOfInt_ofNat]
      let am := Nat.succ (Nat.mod m P)
      let bn := Nat.mod n P
      have hamLe : am ≤ P := Nat.mod_lt m hPpos
      have h1 : (P - am) * bn + am * bn = P * bn := by
        rw [← Nat.add_mul, Nat.sub_add_cancel hamLe]
      have hMod1 : Nat.mod ((P - am) * bn + (m + 1) * n) P = 0 := by
        rw [nat_add_mod ((P - am) * bn) ((m + 1) * n) P]
        have hMmod : Nat.mod ((m + 1) * n) P = Nat.mod (am * bn) P := by
          have hSuccMod : Nat.mod (m + 1) P = Nat.mod am P := by
            have hSplit := nat_div_add_mod m P
            have hC := congrArg (fun z => z + 1) hSplit.symm
            rw [Nat.add_assoc (P * Nat.div m P) (Nat.mod m P) 1,
              Nat.add_comm (P * Nat.div m P) (Nat.mod m P + 1)] at hC
            change Nat.mod (m + 1) P = Nat.mod am P
            rw [hC, Nat.mul_comm P _, nat_add_mul_mod_self_left]
          rw [← nat_mul_mod_cancel_right (m + 1) n P]
          change Nat.mod ((m + 1) * bn) P = Nat.mod (am * bn) P
          rw [← nat_mul_mod_cancel_left (m + 1) bn P, hSuccMod,
            nat_mul_mod_cancel_left]
        rw [hMmod, ← nat_add_mod ((P - am) * bn) (am * bn) P, h1,
          nat_mul_mod_left]
      have hMod2 : Nat.mod (Nat.mod (P - Nat.mod ((m + 1) * n) P) P +
          (m + 1) * n) P = 0 := by
        rw [nat_add_mod, nat_mod_mod, ← nat_add_mod]
        have hSubLe : Nat.mod ((m + 1) * n) P ≤ P :=
          Nat.le_of_lt (Nat.mod_lt _ hPpos)
        have hSplit := nat_div_add_mod ((m + 1) * n) P
        have hSum : (P - Nat.mod ((m + 1) * n) P) + (m + 1) * n =
            P + P * Nat.div ((m + 1) * n) P := by
          have hC := congrArg (fun z => (P - Nat.mod ((m + 1) * n) P) + z)
            hSplit.symm
          rw [← Nat.add_assoc,
            Nat.add_comm (P - Nat.mod ((m + 1) * n) P)
              (P * Nat.div ((m + 1) * n) P),
            Nat.add_assoc, Nat.sub_add_cancel hSubLe,
            Nat.add_comm (P * Nat.div ((m + 1) * n) P) P] at hC
          exact hC
        rw [hSum, Nat.mul_comm P _, nat_add_mul_mod_self_left, nat_mod_self]
      have hL : Nat.mod (Nat.mod ((P - am) * bn) P + (m + 1) * n) P = 0 := by
        rw [nat_add_mod (Nat.mod _ P) _ P, nat_mod_mod, ← nat_add_mod, hMod1]
      exact nat_eq_of_mod_add_right
        (Nat.mod_lt _ hPpos) (Nat.mod_lt _ hPpos) (hMod2.trans hL.symm)
    | negSucc n =>
      have hMul : Int.negSucc m * Int.negSucc n =
          Int.ofNat ((m + 1) * (n + 1)) := rfl
      rw [hMul, toNat_bvOfInt_ofNat, toNat_bvOfInt_negSucc,
        toNat_bvOfInt_negSucc]
      let am := Nat.succ (Nat.mod m P)
      let bn := Nat.succ (Nat.mod n P)
      have hamLe : am ≤ P := Nat.mod_lt m hPpos
      have hbnLe : bn ≤ P := Nat.mod_lt n hPpos
      have hModEq : Nat.mod ((P - am) * (P - bn) + am * (P - bn)) P = 0 := by
        rw [← Nat.add_mul, Nat.sub_add_cancel hamLe, nat_mul_mod_left]
      have hMod2 : Nat.mod ((m + 1) * (n + 1) + am * (P - bn)) P = 0 := by
        rw [nat_add_mod ((m + 1) * (n + 1)) _ P]
        have hM : Nat.mod ((m + 1) * (n + 1)) P = Nat.mod (am * bn) P := by
          rw [nat_mul_mod (m + 1) (n + 1) P]
          have hSm : Nat.mod (m + 1) P = Nat.mod am P := by
            have hSp := nat_div_add_mod m P
            rw [← hSp, Nat.add_assoc (P * Nat.div m P) _ 1,
              Nat.add_comm (P * Nat.div m P) _, Nat.mul_comm P _,
              nat_add_mul_mod_self_left]
          have hSn : Nat.mod (n + 1) P = Nat.mod bn P := by
            have hSp := nat_div_add_mod n P
            rw [← hSp, Nat.add_assoc (P * Nat.div n P) _ 1,
              Nat.add_comm (P * Nat.div n P) _, Nat.mul_comm P _,
              nat_add_mul_mod_self_left]
          rw [hSm, hSn, ← nat_mul_mod am bn P]
        rw [hM, ← nat_add_mod (am * bn) (am * (P - bn)) P, ← Nat.mul_add,
          Nat.add_comm bn (P - bn), Nat.sub_add_cancel hbnLe, nat_mul_mod_right]
      have hL : Nat.mod (Nat.mod ((P - am) * (P - bn)) P +
          am * (P - bn)) P = 0 := by
        rw [nat_add_mod (Nat.mod _ P) _ P, nat_mod_mod, ← nat_add_mod, hModEq]
      have hR : Nat.mod (Nat.mod ((m + 1) * (n + 1)) P +
          am * (P - bn)) P = 0 := by
        rw [nat_add_mod (Nat.mod _ P) _ P, nat_mod_mod, ← nat_add_mod, hMod2]
      exact nat_eq_of_mod_add_right
        (Nat.mod_lt _ hPpos) (Nat.mod_lt _ hPpos) (hR.trans hL.symm)

private theorem bvOfInt_bvToInt_self {W : Nat} (hW : 0 < W) (x : BitVec W) :
    bvOfInt W (bvToInt x) = x := by
  apply bvToInt_injective
  let h := bvToInt_in_width_range hW x
  exact bvToInt_bvOfInt_eq_of_in_range hW h.1 h.2

private theorem bvToInt_mul_in_double_width {w : Nat} (hw : 0 < w)
    (x y : BitVec w) :
    Neg.neg (Int.ofNat (Nat.pow 2 (2 * w - 1))) ≤ bvToInt x * bvToInt y ∧
      bvToInt x * bvToInt y < Int.ofNat (Nat.pow 2 (2 * w - 1)) := by
  let H := Nat.pow 2 (w - 1)
  have hPow2w : Nat.pow 2 (2 * w - 1) = H * H + H * H := by
    have hE2 : 2 * w - 1 = ((w - 1) + (w - 1)) + 1 := by
      have h1 : 2 * w = ((w - 1) + 1) + ((w - 1) + 1) := by
        rw [Nat.two_mul, Nat.sub_add_cancel hw]
      have hSum : ((w - 1) + 1) + ((w - 1) + 1) =
          ((w - 1) + (w - 1) + 1) + 1 := by
        rw [Nat.add_assoc (w - 1) 1 ((w - 1) + 1),
          Nat.add_comm 1 ((w - 1) + 1),
          ← Nat.add_assoc (w - 1) ((w - 1) + 1) 1,
          ← Nat.add_assoc (w - 1) (w - 1) 1]
      rw [h1, hSum, Nat.add_sub_cancel]
    rw [hE2, nat_pow_succ, Anneal.InitLemmas.nat_pow_add, Nat.mul_two]
  have hHH : 0 < H * H := Nat.mul_pos (nat_two_pow_pos _) (nat_two_pow_pos _)
  have hStrict : H * H < Nat.pow 2 (2 * w - 1) := by
    rw [hPow2w]
    exact Nat.lt_add_of_pos_right hHH
  have hPowW : Nat.pow 2 w = H + H := nat_two_pow_split hw
  cases hmx : Anneal.BitVecArith.msb x <;>
    cases hmy : Anneal.BitVecArith.msb y
  · have hxLt := (Anneal.BitVecArith.msb_eq_false_iff hw x).mp hmx
    have hyLt := (Anneal.BitVecArith.msb_eq_false_iff hw y).mp hmy
    rw [bvToInt_pos_eq_ofNat hw hmx, bvToInt_pos_eq_ofNat hw hmy]
    refine ⟨?_, ?_⟩
    · exact (intBalance_le_iff
        (intBalance_neg_of (Anneal.InitLemmas.intBalance_ofNat _))
        (Anneal.InitLemmas.intBalance_ofNat _)).mpr (by
          rw [Nat.zero_add]; exact Nat.zero_le _)
    · exact int_ofNat_lt_iff.mpr (Nat.lt_trans (nat_mul_lt_mul'
        (Nat.le_of_lt hxLt) hyLt (nat_two_pow_pos _)) hStrict)
  · have hxLt := (Anneal.BitVecArith.msb_eq_false_iff hw x).mp hmx
    have hyGe := (Anneal.BitVecArith.msb_eq_true_iff hw y).mp hmy
    have hbLe : Nat.pow 2 w - y.toNat ≤ H := by
      apply nat_le_of_add_le_add_right (c := y.toNat)
      rw [Nat.sub_add_cancel (Nat.le_of_lt (bitVec_toNat_lt_pow y)), hPowW]
      exact Nat.add_le_add_left hyGe H
    have hbEq : Nat.succ (Nat.pow 2 w - 1 - y.toNat) = Nat.pow 2 w - y.toNat := by
      have hC := Nat.sub_add_cancel
        (Nat.zero_lt_sub_of_lt (bitVec_toNat_lt_pow y))
      rw [Nat.sub_sub, Nat.add_comm y.toNat 1, ← Nat.sub_sub] at hC
      exact hC
    rw [bvToInt_pos_eq_ofNat hw hmx, bvToInt_neg_eq_negSucc hw hmy]
    have hMul : Int.ofNat x.toNat * Int.negSucc (Nat.pow 2 w - 1 - y.toNat) =
        Neg.neg (Int.ofNat (x.toNat * (Nat.pow 2 w - y.toNat))) := by
      rw [← hbEq]
      change Int.negOfNat (x.toNat * Nat.succ (Nat.pow 2 w - 1 - y.toNat)) =
        Neg.neg (Int.ofNat (x.toNat * Nat.succ (Nat.pow 2 w - 1 - y.toNat)))
      cases x.toNat * Nat.succ (Nat.pow 2 w - 1 - y.toNat) <;> rfl
    rw [hMul]
    have hProdLe : x.toNat * (Nat.pow 2 w - y.toNat) ≤ Nat.pow 2 (2 * w - 1) :=
      Nat.le_of_lt (Nat.lt_of_le_of_lt (Nat.mul_le_mul (Nat.le_of_lt hxLt) hbLe)
        hStrict)
    refine ⟨?_, ?_⟩
    · exact (intBalance_le_iff
        (intBalance_neg_of (Anneal.InitLemmas.intBalance_ofNat _))
        (intBalance_neg_of (Anneal.InitLemmas.intBalance_ofNat _))).mpr
        (by rw [Nat.zero_add, Nat.zero_add]; exact hProdLe)
    · exact (intBalance_lt_iff
        (intBalance_neg_of (Anneal.InitLemmas.intBalance_ofNat _))
        (Anneal.InitLemmas.intBalance_ofNat _)).mpr
        (by rw [Nat.zero_add]
            exact Nat.lt_of_lt_of_le (nat_two_pow_pos _)
              (Nat.le_add_right _ _))
  · have hxGe := (Anneal.BitVecArith.msb_eq_true_iff hw x).mp hmx
    have hyLt := (Anneal.BitVecArith.msb_eq_false_iff hw y).mp hmy
    have haLe : Nat.pow 2 w - x.toNat ≤ H := by
      apply nat_le_of_add_le_add_right (c := x.toNat)
      rw [Nat.sub_add_cancel (Nat.le_of_lt (bitVec_toNat_lt_pow x)), hPowW]
      exact Nat.add_le_add_left hxGe H
    have haEq : Nat.succ (Nat.pow 2 w - 1 - x.toNat) = Nat.pow 2 w - x.toNat := by
      have hC := Nat.sub_add_cancel
        (Nat.zero_lt_sub_of_lt (bitVec_toNat_lt_pow x))
      rw [Nat.sub_sub, Nat.add_comm x.toNat 1, ← Nat.sub_sub] at hC
      exact hC
    rw [bvToInt_neg_eq_negSucc hw hmx, bvToInt_pos_eq_ofNat hw hmy]
    have hMul : Int.negSucc (Nat.pow 2 w - 1 - x.toNat) * Int.ofNat y.toNat =
        Neg.neg (Int.ofNat ((Nat.pow 2 w - x.toNat) * y.toNat)) := by
      rw [← haEq]
      change Int.negOfNat (Nat.succ (Nat.pow 2 w - 1 - x.toNat) * y.toNat) =
        Neg.neg (Int.ofNat (Nat.succ (Nat.pow 2 w - 1 - x.toNat) * y.toNat))
      cases Nat.succ (Nat.pow 2 w - 1 - x.toNat) * y.toNat <;> rfl
    rw [hMul]
    have hProdLe : (Nat.pow 2 w - x.toNat) * y.toNat ≤ Nat.pow 2 (2 * w - 1) :=
      Nat.le_of_lt (Nat.lt_of_le_of_lt (Nat.mul_le_mul haLe (Nat.le_of_lt hyLt))
        hStrict)
    refine ⟨?_, ?_⟩
    · exact (intBalance_le_iff
        (intBalance_neg_of (Anneal.InitLemmas.intBalance_ofNat _))
        (intBalance_neg_of (Anneal.InitLemmas.intBalance_ofNat _))).mpr
        (by rw [Nat.zero_add, Nat.zero_add]; exact hProdLe)
    · exact (intBalance_lt_iff
        (intBalance_neg_of (Anneal.InitLemmas.intBalance_ofNat _))
        (Anneal.InitLemmas.intBalance_ofNat _)).mpr
        (by rw [Nat.zero_add]
            exact Nat.lt_of_lt_of_le (nat_two_pow_pos _)
              (Nat.le_add_right _ _))
  · have hxGe := (Anneal.BitVecArith.msb_eq_true_iff hw x).mp hmx
    have hyGe := (Anneal.BitVecArith.msb_eq_true_iff hw y).mp hmy
    have haLe : Nat.pow 2 w - x.toNat ≤ H := by
      apply nat_le_of_add_le_add_right (c := x.toNat)
      rw [Nat.sub_add_cancel (Nat.le_of_lt (bitVec_toNat_lt_pow x)), hPowW]
      exact Nat.add_le_add_left hxGe H
    have hbLe : Nat.pow 2 w - y.toNat ≤ H := by
      apply nat_le_of_add_le_add_right (c := y.toNat)
      rw [Nat.sub_add_cancel (Nat.le_of_lt (bitVec_toNat_lt_pow y)), hPowW]
      exact Nat.add_le_add_left hyGe H
    have haEq : Nat.succ (Nat.pow 2 w - 1 - x.toNat) = Nat.pow 2 w - x.toNat := by
      have hC := Nat.sub_add_cancel
        (Nat.zero_lt_sub_of_lt (bitVec_toNat_lt_pow x))
      rw [Nat.sub_sub, Nat.add_comm x.toNat 1, ← Nat.sub_sub] at hC
      exact hC
    have hbEq : Nat.succ (Nat.pow 2 w - 1 - y.toNat) = Nat.pow 2 w - y.toNat := by
      have hC := Nat.sub_add_cancel
        (Nat.zero_lt_sub_of_lt (bitVec_toNat_lt_pow y))
      rw [Nat.sub_sub, Nat.add_comm y.toNat 1, ← Nat.sub_sub] at hC
      exact hC
    rw [bvToInt_neg_eq_negSucc hw hmx, bvToInt_neg_eq_negSucc hw hmy]
    have hMul : Int.negSucc (Nat.pow 2 w - 1 - x.toNat) *
        Int.negSucc (Nat.pow 2 w - 1 - y.toNat) =
        Int.ofNat ((Nat.pow 2 w - x.toNat) * (Nat.pow 2 w - y.toNat)) := by
      rw [← haEq, ← hbEq]
      rfl
    rw [hMul]
    refine ⟨?_, ?_⟩
    · exact (intBalance_le_iff
        (intBalance_neg_of (Anneal.InitLemmas.intBalance_ofNat _))
        (Anneal.InitLemmas.intBalance_ofNat _)).mpr
        (by rw [Nat.zero_add]; exact Nat.zero_le _)
    · exact int_ofNat_lt_iff.mpr (Nat.lt_of_le_of_lt (Nat.mul_le_mul haLe hbLe)
        hStrict)

/-- Signed multiplication does not overflow (`signedOverflowMulBv x y = false`)
iff `-(2^(w - 1)) ≤ bvToInt x * bvToInt y < 2^(w - 1)`. -/
theorem signedOverflowMulBv_eq_false_iff {w : Nat} (hw : 0 < w)
    (x y : BitVec w) :
    signedOverflowMulBv x y = false ↔
      Neg.neg (Int.ofNat (Nat.pow 2 (w - 1))) ≤ bvToInt x * bvToInt y ∧
        bvToInt x * bvToInt y < Int.ofNat (Nat.pow 2 (w - 1)) := by
  unfold signedOverflowMulBv
  rw [Anneal.InitLemmas.ite_false_of (Nat.ne_of_gt hw)]
  have hwLe : w ≤ 2 * w := by
    rw [Nat.two_mul]
    exact Nat.le_add_right w w
  have hw2 : 0 < 2 * w := Nat.lt_of_lt_of_le hw hwLe
  have hX := (bvOfInt_bvToInt_signExtend hw hwLe x).symm
  have hY := (bvOfInt_bvToInt_signExtend hw hwLe y).symm
  have hZ := (bvOfInt_bvToInt_signExtend hw hwLe
    (Anneal.BitVec.mul x y)).symm
  have hMulBv :
      Anneal.BitVec.mul (Anneal.BitVecArith.signExtend (2 * w) x)
        (Anneal.BitVecArith.signExtend (2 * w) y) =
      bvOfInt (2 * w) (bvToInt x * bvToInt y) := by
    rw [hX, hY, ← bvOfInt_mul]
  have hMulW : Anneal.BitVec.mul x y = bvOfInt w (bvToInt x * bvToInt y) := by
    have h1 := bvOfInt_mul w (bvToInt x) (bvToInt y)
    rw [bvOfInt_bvToInt_self hw x, bvOfInt_bvToInt_self hw y] at h1
    exact h1.symm
  have hRange := bvToInt_mul_in_double_width hw x y
  rw [hMulBv, hZ]
  have hBne : (bvOfInt (2 * w) (bvToInt x * bvToInt y) !=
      bvOfInt (2 * w) (bvToInt (Anneal.BitVec.mul x y))) = false ↔
      bvOfInt (2 * w) (bvToInt x * bvToInt y) =
        bvOfInt (2 * w) (bvToInt (Anneal.BitVec.mul x y)) := by
    constructor
    · intro hF
      cases Anneal.ClassicalEm.prop_em
          (bvOfInt (2 * w) (bvToInt x * bvToInt y) =
            bvOfInt (2 * w) (bvToInt (Anneal.BitVec.mul x y))) with
      | inl hEq => exact hEq
      | inr hNe => rw [bne_iff_ne.mpr hNe] at hF; nomatch hF
    · intro hEq
      rw [hEq]
      change (!(bvOfInt (2 * w) (bvToInt (Anneal.BitVec.mul x y)) ==
          bvOfInt (2 * w) (bvToInt (Anneal.BitVec.mul x y)))) = false
      rw [beq_self_eq_true]
      rfl
  rw [hBne]
  constructor
  · intro hEq
    have hInt := congrArg bvToInt hEq
    rw [bvToInt_bvOfInt_eq_of_in_range hw2 hRange.1 hRange.2,
      bvToInt_bvOfInt_eq_of_in_range hw2
        (by have hR := bvToInt_in_width_range hw (Anneal.BitVec.mul x y)
            have hP : Nat.pow 2 (w - 1) ≤ Nat.pow 2 (2 * w - 1) :=
              Nat.pow_le_pow_right (by decide : 0 < 2)
                (Nat.sub_le_sub_right hwLe 1)
            exact (intBalance_le_iff
              (intBalance_neg_of (Anneal.InitLemmas.intBalance_ofNat _))
              (intBalance_bvToInt hw (Anneal.BitVec.mul x y))).mpr
              (by rw [Nat.zero_add]
                  have h1 := (intBalance_le_iff
                    (intBalance_neg_of (Anneal.InitLemmas.intBalance_ofNat _))
                    (intBalance_bvToInt hw (Anneal.BitVec.mul x y))).mp hR.1
                  rw [Nat.zero_add] at h1
                  exact Nat.le_trans h1 (Nat.add_le_add_left hP _)))
        (by have hR := bvToInt_in_width_range hw (Anneal.BitVec.mul x y)
            have hP : Nat.pow 2 (w - 1) ≤ Nat.pow 2 (2 * w - 1) :=
              Nat.pow_le_pow_right (by decide : 0 < 2)
                (Nat.sub_le_sub_right hwLe 1)
            exact (intBalance_lt_iff
              (intBalance_bvToInt hw (Anneal.BitVec.mul x y))
              (Anneal.InitLemmas.intBalance_ofNat _)).mpr
              (by rw [Nat.add_zero]
                  have h1 := (intBalance_lt_iff
                    (intBalance_bvToInt hw (Anneal.BitVec.mul x y))
                    (Anneal.InitLemmas.intBalance_ofNat _)).mp hR.2
                  rw [Nat.add_zero] at h1
                  exact Nat.lt_of_lt_of_le h1 (Nat.add_le_add_right hP _)))] at hInt
    rw [hInt]
    exact bvToInt_in_width_range hw (Anneal.BitVec.mul x y)
  · intro ⟨hLo, hHi⟩
    rw [hMulW, bvToInt_bvOfInt_eq_of_in_range hw hLo hHi]

private theorem signedOverflowMulBv_eq_int_overflow {w : Nat} (hw : 0 < w)
    (x y : BitVec w) :
    signedOverflowMulBv x y =
      (decide (bvToInt x * bvToInt y < Neg.neg (Int.ofNat (Nat.pow 2 (w - 1)))) ||
        decide (Int.ofNat (Nat.pow 2 (w - 1)) ≤ bvToInt x * bvToInt y)) := by
  cases hOv : signedOverflowMulBv x y with
  | false =>
    have hBounds := (signedOverflowMulBv_eq_false_iff hw x y).mp hOv
    rw [decide_eq_false ((int_not_lt_iff_le _ _).mpr hBounds.1),
      decide_eq_false ((int_not_le_iff_lt _ _).mpr hBounds.2)]
    rfl
  | true =>
    cases int_lt_or_ge (bvToInt x * bvToInt y)
        (Neg.neg (Int.ofNat (Nat.pow 2 (w - 1)))) with
    | inl hLt => rw [decide_eq_true hLt, Bool.true_or]
    | inr hGe =>
      cases int_lt_or_ge (bvToInt x * bvToInt y)
          (Int.ofNat (Nat.pow 2 (w - 1))) with
      | inr hGe2 => rw [decide_eq_true hGe2, Bool.or_true]
      | inl hLt2 =>
        have hF := (signedOverflowMulBv_eq_false_iff hw x y).mpr ⟨hGe, hLt2⟩
        rw [hF] at hOv
        nomatch hOv

private theorem bvOfInt_bvToInt_add {W : Nat} (hW : 0 < W) (x y : BitVec W) :
    bvOfInt W (bvToInt x + bvToInt y) = x + y := by
  -- Reduce `(a + b) % 2^W` via `IntBalance`:
  let P := Nat.pow 2 W
  have hPpos : 0 < P := nat_two_pow_pos W
  have hB := intBalance_add_of (intBalance_bvToInt hW x) (intBalance_bvToInt hW y)
  have hPow : P = Nat.pow 2 (W - 1) + Nat.pow 2 (W - 1) := nat_two_pow_split hW
  have hModX : Nat.mod (Anneal.BitVecArith.signedKey x) P =
      Nat.mod (x.toNat + Nat.pow 2 (W - 1)) P := by
    cases hm : Anneal.BitVecArith.msb x with
    | false => rw [Anneal.BitVecArith.signedKey_eq_of_msb_false hW hm]
    | true =>
      have hGe := (Anneal.BitVecArith.msb_eq_true_iff hW x).mp hm
      rw [Anneal.BitVecArith.signedKey_eq_of_msb_true hW hm]
      have hSplit : x.toNat + Nat.pow 2 (W - 1) =
          (x.toNat - Nat.pow 2 (W - 1)) + 1 * P := by
        rw [Nat.one_mul, hPow, ← Nat.add_assoc, Nat.sub_add_cancel hGe]
      rw [hSplit, nat_add_mul_mod_self_left]
  have hModY : Nat.mod (Anneal.BitVecArith.signedKey y) P =
      Nat.mod (y.toNat + Nat.pow 2 (W - 1)) P := by
    cases hm : Anneal.BitVecArith.msb y with
    | false => rw [Anneal.BitVecArith.signedKey_eq_of_msb_false hW hm]
    | true =>
      have hGe := (Anneal.BitVecArith.msb_eq_true_iff hW y).mp hm
      rw [Anneal.BitVecArith.signedKey_eq_of_msb_true hW hm]
      have hSplit : y.toNat + Nat.pow 2 (W - 1) =
          (y.toNat - Nat.pow 2 (W - 1)) + 1 * P := by
        rw [Nat.one_mul, hPow, ← Nat.add_assoc, Nat.sub_add_cancel hGe]
      rw [hSplit, nat_add_mul_mod_self_left]
  have hModSum : Nat.mod ((bvOfInt W (bvToInt x + bvToInt y)).toNat + P) P =
      Nat.mod (Anneal.BitVecArith.signedKey x +
        Anneal.BitVecArith.signedKey y) P := by
    cases hz : bvToInt x + bvToInt y with
    | ofNat m =>
      rw [toNat_bvOfInt_ofNat]
      unfold Anneal.InitLemmas.IntBalance Anneal.InitLemmas.intPos
        Anneal.InitLemmas.intNeg at hB
      rw [hz] at hB
      dsimp only at hB
      rw [Nat.zero_add, ← hPow] at hB
      rw [nat_add_mod_cancel_left, hB]
    | negSucc m =>
      rw [toNat_bvOfInt_negSucc]
      unfold Anneal.InitLemmas.IntBalance Anneal.InitLemmas.intPos
        Anneal.InitLemmas.intNeg at hB
      rw [hz] at hB
      dsimp only at hB
      rw [Nat.zero_add, ← hPow] at hB
      have hMlt : Nat.mod m P < P := Nat.mod_lt m hPpos
      have hSplit := nat_div_add_mod m P
      have hModNeg :
          Nat.mod (P - Nat.succ (Nat.mod m P) + (m + 1)) P = 0 := by
        have h1 : P - Nat.succ (Nat.mod m P) + (m + 1) =
            P + P * Nat.div m P := by
          have hSucc : Nat.succ (Nat.mod m P) ≤ P := hMlt
          have hAdd1 : m + 1 = (Nat.mod m P + 1) + P * Nat.div m P := by
            have hC := congrArg (fun z => z + 1) hSplit.symm
            rw [Nat.add_assoc (P * Nat.div m P) (Nat.mod m P) 1,
              Nat.add_comm (P * Nat.div m P) (Nat.mod m P + 1)] at hC
            exact hC
          rw [hAdd1, ← Nat.add_assoc]
          change (P - (Nat.mod m P + 1) + (Nat.mod m P + 1)) +
              P * Nat.div m P = _
          rw [Nat.sub_add_cancel hSucc]
        rw [h1, Nat.mul_comm P _, nat_add_mul_mod_self_left, nat_mod_self]
      have hSum1 : Nat.mod ((P - Nat.succ (Nat.mod m P) + (m + 1)) +
          (Anneal.BitVecArith.signedKey x + Anneal.BitVecArith.signedKey y)) P =
          Nat.mod ((P - Nat.succ (Nat.mod m P)) +
            ((m + 1) + (Anneal.BitVecArith.signedKey x +
              Anneal.BitVecArith.signedKey y))) P :=
        congrArg (fun z => Nat.mod z P) (Nat.add_assoc _ _ _)
      rw [← hB] at hSum1
      rw [nat_add_mod (P - Nat.succ (Nat.mod m P) + (m + 1)) _ P,
        hModNeg, Nat.zero_add, nat_mod_mod] at hSum1
      exact hSum1.symm
  have hRhs : Nat.mod (Anneal.BitVecArith.signedKey x +
      Anneal.BitVecArith.signedKey y) P = Nat.mod (x.toNat + y.toNat) P := by
    rw [nat_add_mod _ _ P, hModX, hModY, ← nat_add_mod,
      Anneal.InitLemmas.add_four_rearrange, ← hPow,
      Nat.add_comm (x.toNat + y.toNat) P, nat_add_mod_left]
  rw [nat_add_mod_right] at hModSum
  apply Anneal.BitVec.eq_of_toNat_eq
  rw [nat_mod_eq_of_lt (bitVec_toNat_lt_pow _)] at hModSum
  rw [Anneal.BitVec.toNat_add, hModSum, hRhs]

/-- Signed `evalBinOp .addWithOverflow` returns `(x + y, signedOverflowAddBv x
y)` across all six widths (including `i128`). -/
theorem evalBinOp_addWithOverflow_signed_eq (w : IntWidth)
    (x y : BitVec (8 * w.byteSize)) :
    evalBinOp .addWithOverflow (.scalar (bvToScalar w true x))
        (.scalar (bvToScalar w true y)) =
      .ok (.tuple [
        .scalar (bvToScalar w true (x + y)),
        .bool (signedOverflowAddBv x y)
      ]) := by
  have hW : 0 < 8 * w.byteSize := by
    rw [← intWidth_bitWidth_eq_eight_mul]
    exact intWidth_bitWidth_pos w
  unfold evalBinOp evalArithOp
  dsimp only
  rw [if_bool_false (rfl : BinOp.addWithOverflow.isShift = false),
    bvToScalar_width, bvToScalar_width, bvToScalar_signed, bvToScalar_signed,
    if_bool_false (evalBinOp_header_eq w true),
    Bool.false_and, if_false_eq, Bool.true_and, Bool.false_and, if_false_eq,
    decodeScalar_signed_eq_bvToInt, decodeScalar_signed_eq_bvToInt]
  dsimp only [truncateScalar]
  rw [if_true_eq, bvToInt_in_i128_range, if_false_eq, bvOfInt_128_bvToInt]
  dsimp only
  have hU : BinOp.addWithOverflow.isUnchecked = false := rfl
  have hO : BinOp.addWithOverflow.isOverflowing = true := rfl
  rw [hU, hO, Bool.and_false, if_false_eq, if_true_eq, if_true_eq,
    signed_int_overflow_flag_eq w (bvToInt x + bvToInt y),
    ← signedOverflowAddBv_eq_int_overflow hW x y]
  have hBits : truncateBits w (bvOfInt 128 (bvToInt x + bvToInt y)) =
      bvZeroExtend 128 (x + y) := by
    rw [truncateBits_bvOfInt_eq_bvZeroExtend, bvOfInt_bvToInt_add hW]
  change Except.ok (Val.tuple [Val.scalar ⟨w, true,
      truncateBits w (bvOfInt 128 (bvToInt x + bvToInt y))⟩,
    Val.bool (signedOverflowAddBv x y)]) = _
  rw [hBits]
  rfl

/-- Signed `evalBinOp .addUnchecked` succeeds with `x + y` iff
`signedOverflowAddBv x y = false` and faults with `.undefined` otherwise. -/
theorem evalBinOp_addUnchecked_signed_eq (w : IntWidth)
    (x y : BitVec (8 * w.byteSize)) :
    evalBinOp .addUnchecked (.scalar (bvToScalar w true x))
        (.scalar (bvToScalar w true y)) =
      if signedOverflowAddBv x y = false then
        .ok (.scalar (bvToScalar w true (x + y)))
      else
        .error .undefined := by
  have hW : 0 < 8 * w.byteSize := by
    rw [← intWidth_bitWidth_eq_eight_mul]
    exact intWidth_bitWidth_pos w
  unfold evalBinOp evalArithOp
  dsimp only
  rw [if_bool_false (rfl : BinOp.addUnchecked.isShift = false),
    bvToScalar_width, bvToScalar_width, bvToScalar_signed, bvToScalar_signed,
    if_bool_false (evalBinOp_header_eq w true),
    Bool.false_and, if_false_eq, Bool.true_and, Bool.false_and, if_false_eq,
    decodeScalar_signed_eq_bvToInt, decodeScalar_signed_eq_bvToInt]
  dsimp only [truncateScalar]
  rw [if_true_eq, bvToInt_in_i128_range, if_false_eq, bvOfInt_128_bvToInt]
  dsimp only
  have hU : BinOp.addUnchecked.isUnchecked = true := rfl
  rw [hU, Bool.and_true, if_true_eq,
    signed_int_overflow_flag_eq w (bvToInt x + bvToInt y),
    ← signedOverflowAddBv_eq_int_overflow hW x y]
  cases hOv : signedOverflowAddBv x y with
  | false =>
    rw [if_false_eq, if_false_false_eq]
    have hO : BinOp.addUnchecked.isOverflowing = false := rfl
    rw [hO, if_false_eq]
    have hBits : truncateBits w (bvOfInt 128 (bvToInt x + bvToInt y)) =
        bvZeroExtend 128 (x + y) := by
      rw [truncateBits_bvOfInt_eq_bvZeroExtend, bvOfInt_bvToInt_add hW]
    change Except.ok (Val.scalar ⟨w, true,
        truncateBits w (bvOfInt 128 (bvToInt x + bvToInt y))⟩) = _
    rw [hBits]
    rfl
  | true =>
    rw [if_true_eq, if_true_false_eq]

/-- Signed `evalBinOp .subWithOverflow` returns `(x - y, signedOverflowSubBv x
y)` across all six widths (including `i128`). -/
theorem evalBinOp_subWithOverflow_signed_eq (w : IntWidth)
    (x y : BitVec (8 * w.byteSize)) :
    evalBinOp .subWithOverflow (.scalar (bvToScalar w true x))
        (.scalar (bvToScalar w true y)) =
      .ok (.tuple [
        .scalar (bvToScalar w true (x - y)),
        .bool (signedOverflowSubBv x y)
      ]) := by
  have hW : 0 < 8 * w.byteSize := by
    rw [← intWidth_bitWidth_eq_eight_mul]
    exact intWidth_bitWidth_pos w
  unfold evalBinOp evalArithOp
  dsimp only
  rw [if_bool_false (rfl : BinOp.subWithOverflow.isShift = false),
    bvToScalar_width, bvToScalar_width, bvToScalar_signed, bvToScalar_signed,
    if_bool_false (evalBinOp_header_eq w true),
    Bool.false_and, if_false_eq, Bool.true_and, Bool.false_and, if_false_eq,
    decodeScalar_signed_eq_bvToInt, decodeScalar_signed_eq_bvToInt]
  dsimp only [truncateScalar]
  rw [if_true_eq, bvToInt_in_i128_range, if_false_eq, bvOfInt_128_bvToInt]
  dsimp only
  have hU : BinOp.subWithOverflow.isUnchecked = false := rfl
  have hO : BinOp.subWithOverflow.isOverflowing = true := rfl
  rw [hU, hO, Bool.and_false, if_false_eq, if_true_eq, if_true_eq,
    signed_int_overflow_flag_eq w (bvToInt x - bvToInt y),
    ← signedOverflowSubBv_eq_int_overflow hW x y]
  have hBits : truncateBits w (bvOfInt 128 (bvToInt x - bvToInt y)) =
      bvZeroExtend 128 (x - y) := by
    rw [truncateBits_bvOfInt_eq_bvZeroExtend, bvOfInt_bvToInt_sub hW]
  change Except.ok (Val.tuple [Val.scalar ⟨w, true,
      truncateBits w (bvOfInt 128 (bvToInt x - bvToInt y))⟩,
    Val.bool (signedOverflowSubBv x y)]) = _
  rw [hBits]
  rfl

/-- Signed `evalBinOp .subUnchecked` succeeds with `x - y` iff
`signedOverflowSubBv x y = false` and faults with `.undefined` otherwise. -/
theorem evalBinOp_subUnchecked_signed_eq (w : IntWidth)
    (x y : BitVec (8 * w.byteSize)) :
    evalBinOp .subUnchecked (.scalar (bvToScalar w true x))
        (.scalar (bvToScalar w true y)) =
      if signedOverflowSubBv x y = false then
        .ok (.scalar (bvToScalar w true (x - y)))
      else
        .error .undefined := by
  have hW : 0 < 8 * w.byteSize := by
    rw [← intWidth_bitWidth_eq_eight_mul]
    exact intWidth_bitWidth_pos w
  unfold evalBinOp evalArithOp
  dsimp only
  rw [if_bool_false (rfl : BinOp.subUnchecked.isShift = false),
    bvToScalar_width, bvToScalar_width, bvToScalar_signed, bvToScalar_signed,
    if_bool_false (evalBinOp_header_eq w true),
    Bool.false_and, if_false_eq, Bool.true_and, Bool.false_and, if_false_eq,
    decodeScalar_signed_eq_bvToInt, decodeScalar_signed_eq_bvToInt]
  dsimp only [truncateScalar]
  rw [if_true_eq, bvToInt_in_i128_range, if_false_eq, bvOfInt_128_bvToInt]
  dsimp only
  have hU : BinOp.subUnchecked.isUnchecked = true := rfl
  rw [hU, Bool.and_true, if_true_eq,
    signed_int_overflow_flag_eq w (bvToInt x - bvToInt y),
    ← signedOverflowSubBv_eq_int_overflow hW x y]
  cases hOv : signedOverflowSubBv x y with
  | false =>
    rw [if_false_eq, if_false_false_eq]
    have hO : BinOp.subUnchecked.isOverflowing = false := rfl
    rw [hO, if_false_eq]
    have hBits : truncateBits w (bvOfInt 128 (bvToInt x - bvToInt y)) =
        bvZeroExtend 128 (x - y) := by
      rw [truncateBits_bvOfInt_eq_bvZeroExtend, bvOfInt_bvToInt_sub hW]
    change Except.ok (Val.scalar ⟨w, true,
        truncateBits w (bvOfInt 128 (bvToInt x - bvToInt y))⟩) = _
    rw [hBits]
    rfl
  | true =>
    rw [if_true_eq, if_true_false_eq]

/-- Signed `evalBinOp .mulWithOverflow` returns `(x * y, signedOverflowMulBv x
y)` across all six widths (including `i128`). -/
theorem evalBinOp_mulWithOverflow_signed_eq (w : IntWidth)
    (x y : BitVec (8 * w.byteSize)) :
    evalBinOp .mulWithOverflow (.scalar (bvToScalar w true x))
        (.scalar (bvToScalar w true y)) =
      .ok (.tuple [
        .scalar (bvToScalar w true (Anneal.BitVec.mul x y)),
        .bool (signedOverflowMulBv x y)
      ]) := by
  have hW : 0 < 8 * w.byteSize := by
    rw [← intWidth_bitWidth_eq_eight_mul]
    exact intWidth_bitWidth_pos w
  unfold evalBinOp evalArithOp
  dsimp only
  rw [if_bool_false (rfl : BinOp.mulWithOverflow.isShift = false),
    bvToScalar_width, bvToScalar_width, bvToScalar_signed, bvToScalar_signed,
    if_bool_false (evalBinOp_header_eq w true),
    Bool.false_and, if_false_eq, Bool.true_and, Bool.false_and, if_false_eq,
    decodeScalar_signed_eq_bvToInt, decodeScalar_signed_eq_bvToInt]
  dsimp only [truncateScalar]
  rw [if_true_eq, bvToInt_in_i128_range, if_false_eq, bvOfInt_128_bvToInt]
  dsimp only
  have hU : BinOp.mulWithOverflow.isUnchecked = false := rfl
  have hO : BinOp.mulWithOverflow.isOverflowing = true := rfl
  rw [hU, hO, Bool.and_false, if_false_eq, if_true_eq, if_true_eq,
    signed_int_overflow_flag_eq w (bvToInt x * bvToInt y),
    ← signedOverflowMulBv_eq_int_overflow hW x y]
  have hBits : truncateBits w (bvOfInt 128 (bvToInt x * bvToInt y)) =
      bvZeroExtend 128 (Anneal.BitVec.mul x y) := by
    rw [truncateBits_bvOfInt_eq_bvZeroExtend, bvOfInt_mul,
      bvOfInt_bvToInt_self hW x, bvOfInt_bvToInt_self hW y]
  change Except.ok (Val.tuple [Val.scalar ⟨w, true,
      truncateBits w (bvOfInt 128 (bvToInt x * bvToInt y))⟩,
    Val.bool (signedOverflowMulBv x y)]) = _
  rw [hBits]
  rfl

/-- Signed `evalBinOp .mulUnchecked` succeeds with `x * y` iff
`signedOverflowMulBv x y = false` and faults with `.undefined` otherwise
(including `i128` host overflow). -/
theorem evalBinOp_mulUnchecked_signed_eq (w : IntWidth)
    (x y : BitVec (8 * w.byteSize)) :
    evalBinOp .mulUnchecked (.scalar (bvToScalar w true x))
        (.scalar (bvToScalar w true y)) =
      if signedOverflowMulBv x y = false then
        .ok (.scalar (bvToScalar w true (Anneal.BitVec.mul x y)))
      else
        .error .undefined := by
  have hW : 0 < 8 * w.byteSize := by
    rw [← intWidth_bitWidth_eq_eight_mul]
    exact intWidth_bitWidth_pos w
  unfold evalBinOp evalArithOp
  dsimp only
  rw [if_bool_false (rfl : BinOp.mulUnchecked.isShift = false),
    bvToScalar_width, bvToScalar_width, bvToScalar_signed, bvToScalar_signed,
    if_bool_false (evalBinOp_header_eq w true),
    Bool.false_and, if_false_eq, Bool.true_and, Bool.false_and, if_false_eq,
    decodeScalar_signed_eq_bvToInt, decodeScalar_signed_eq_bvToInt]
  dsimp only [truncateScalar]
  rw [if_true_eq, bvToInt_in_i128_range, if_false_eq, bvOfInt_128_bvToInt]
  dsimp only
  have hU : BinOp.mulUnchecked.isUnchecked = true := rfl
  rw [hU, Bool.and_true, if_true_eq,
    signed_int_overflow_flag_eq w (bvToInt x * bvToInt y),
    ← signedOverflowMulBv_eq_int_overflow hW x y]
  cases hOv : signedOverflowMulBv x y with
  | false =>
    rw [if_false_eq, if_false_false_eq]
    have hO : BinOp.mulUnchecked.isOverflowing = false := rfl
    rw [hO, if_false_eq]
    have hBits : truncateBits w (bvOfInt 128 (bvToInt x * bvToInt y)) =
        bvZeroExtend 128 (Anneal.BitVec.mul x y) := by
      rw [truncateBits_bvOfInt_eq_bvZeroExtend, bvOfInt_mul,
        bvOfInt_bvToInt_self hW x, bvOfInt_bvToInt_self hW y]
    change Except.ok (Val.scalar ⟨w, true,
        truncateBits w (bvOfInt 128 (bvToInt x * bvToInt y))⟩) = _
    rw [hBits]
    rfl
  | true =>
    rw [if_true_eq, if_true_false_eq]

/-- Unsigned magnitude of a signed `w`-bit bitvector (`-x` when `msb x = true`,
else `x`). -/
@[expose] def bvAbs {w : Nat} (x : BitVec w) : BitVec w :=
  if Anneal.BitVecArith.msb x then Anneal.BitVecArith.neg x else x

/-- Signed truncating division on `BitVec w` (`udiv` of magnitudes, negated
when operand sign bits differ). -/
@[expose] def bvSdiv {w : Nat} (x y : BitVec w) : BitVec w :=
  if Anneal.BitVecArith.msb x != Anneal.BitVecArith.msb y then
    Anneal.BitVecArith.neg (Anneal.BitVec.udiv (bvAbs x) (bvAbs y))
  else
    Anneal.BitVec.udiv (bvAbs x) (bvAbs y)

/-- Signed truncating remainder on `BitVec w` (`urem` of magnitudes, negated
when `msb x = true`). -/
@[expose] def bvSrem {w : Nat} (x y : BitVec w) : BitVec w :=
  if Anneal.BitVecArith.msb x then
    Anneal.BitVecArith.neg (Anneal.BitVecArith.urem (bvAbs x) (bvAbs y))
  else
    Anneal.BitVecArith.urem (bvAbs x) (bvAbs y)

private theorem bvAbs_toNat_pos {W : Nat} (_hW : 0 < W) {x : BitVec W}
    (hm : Anneal.BitVecArith.msb x = false) :
    (bvAbs x).toNat = x.toNat := by
  unfold bvAbs
  rw [if_bool_false hm]

private theorem bvAbs_toNat_neg {W : Nat} (hW : 0 < W) {x : BitVec W}
    (hm : Anneal.BitVecArith.msb x = true) :
    (bvAbs x).toNat = Nat.pow 2 W - x.toNat := by
  have hGe := (Anneal.BitVecArith.msb_eq_true_iff hW x).mp hm
  have hxPos : 0 < x.toNat := Nat.lt_of_lt_of_le (nat_two_pow_pos _) hGe
  unfold bvAbs
  rw [if_bool_true hm, Anneal.BitVecArith.toNat_neg_of_pos hxPos]

private theorem bvAbs_toNat_le_half {W : Nat} (hW : 0 < W) (x : BitVec W) :
    (bvAbs x).toNat ≤ Nat.pow 2 (W - 1) := by
  have hPow : Nat.pow 2 W = Nat.pow 2 (W - 1) + Nat.pow 2 (W - 1) :=
    nat_two_pow_split hW
  cases hm : Anneal.BitVecArith.msb x with
  | false =>
    rw [bvAbs_toNat_pos hW hm]
    exact Nat.le_of_lt ((Anneal.BitVecArith.msb_eq_false_iff hW x).mp hm)
  | true =>
    have hGe := (Anneal.BitVecArith.msb_eq_true_iff hW x).mp hm
    rw [bvAbs_toNat_neg hW hm]
    apply nat_le_of_add_le_add_right (c := x.toNat)
    rw [Nat.sub_add_cancel (Nat.le_of_lt (bitVec_toNat_lt_pow x)), hPow]
    exact Nat.add_le_add_left hGe _

private theorem bvAbs_eq_half_iff_signBit (w : IntWidth)
    (x : BitVec (8 * w.byteSize)) :
    (bvAbs x).toNat = Nat.pow 2 (8 * w.byteSize - 1) ↔
      x = Anneal.BitVecArith.signBit (w := 8 * w.byteSize) := by
  have hW : 0 < 8 * w.byteSize := by
    rw [← intWidth_bitWidth_eq_eight_mul]
    exact intWidth_bitWidth_pos w
  have hPow := nat_two_pow_split hW
  cases hm : Anneal.BitVecArith.msb x with
  | false =>
    have hxLt := (Anneal.BitVecArith.msb_eq_false_iff hW x).mp hm
    rw [bvAbs_toNat_pos hW hm]
    constructor
    · intro hEq
      rw [hEq] at hxLt
      exact False.elim (Nat.lt_irrefl _ hxLt)
    · intro hEq
      subst hEq
      have hmS : Anneal.BitVecArith.msb
          (Anneal.BitVecArith.signBit (w := 8 * w.byteSize)) = true := by
        rw [Anneal.BitVecArith.msb_eq_true_iff hW,
          Anneal.BitVecArith.toNat_signBit_of_pos hW]
        exact Nat.le_refl _
      rw [hmS] at hm
      nomatch hm
  | true =>
    rw [bvAbs_toNat_neg hW hm]
    constructor
    · intro hEq
      apply Anneal.BitVec.eq_of_toNat_eq
      rw [Anneal.BitVecArith.toNat_signBit_of_pos hW]
      have hAdd : Nat.pow 2 (8 * w.byteSize) =
          Nat.pow 2 (8 * w.byteSize - 1) + x.toNat := by
        rw [← hEq, Nat.sub_add_cancel (Nat.le_of_lt (bitVec_toNat_lt_pow x))]
      rw [hPow] at hAdd
      exact (Nat.add_left_cancel hAdd).symm
    · intro hEq
      rw [hEq, Anneal.BitVecArith.toNat_signBit_of_pos hW, hPow,
        Nat.add_sub_cancel]

private theorem bvAbs_eq_one_and_msb_true_iff_allOnes (w : IntWidth)
    (y : BitVec (8 * w.byteSize)) :
    (Anneal.BitVecArith.msb y = true ∧ (bvAbs y).toNat = 1) ↔
      y = Anneal.BitVec.allOnes (8 * w.byteSize) := by
  have hW : 0 < 8 * w.byteSize := by
    rw [← intWidth_bitWidth_eq_eight_mul]
    exact intWidth_bitWidth_pos w
  constructor
  · intro ⟨hm, hOne⟩
    rw [bvAbs_toNat_neg hW hm] at hOne
    apply Anneal.BitVec.eq_of_toNat_eq
    rw [Anneal.BitVec.toNat_allOnes]
    have hAdd := congrArg (fun z => z + y.toNat) hOne
    rw [Nat.sub_add_cancel (Nat.le_of_lt (bitVec_toNat_lt_pow y)),
      Nat.add_comm 1 y.toNat] at hAdd
    have hSub := congrArg (fun z => z - 1) hAdd
    rw [Nat.add_sub_cancel] at hSub
    exact hSub.symm
  · intro hEq
    subst hEq
    have hHalf : Nat.pow 2 (8 * w.byteSize - 1) ≤
        Nat.pow 2 (8 * w.byteSize) - 1 := by
      rw [nat_two_pow_split hW, ← sub_add_comm_of_le (nat_two_pow_pos _)]
      exact Nat.le_add_left _ _
    have hm : Anneal.BitVecArith.msb
        (Anneal.BitVec.allOnes (8 * w.byteSize)) = true := by
      rw [Anneal.BitVecArith.msb_eq_true_iff hW, Anneal.BitVec.toNat_allOnes]
      exact hHalf
    refine ⟨hm, ?_⟩
    rw [bvAbs_toNat_neg hW hm, Anneal.BitVec.toNat_allOnes,
      nat_sub_sub_cancel_of_le (nat_two_pow_pos _)]

private theorem bvAbs_pos_of_ne_zero {W : Nat} (hW : 0 < W) {y : BitVec W}
    (hy : y.toNat ≠ 0) : 0 < (bvAbs y).toNat := by
  cases hm : Anneal.BitVecArith.msb y with
  | false =>
    rw [bvAbs_toNat_pos hW hm]
    exact Nat.pos_of_ne_zero hy
  | true =>
    rw [bvAbs_toNat_neg hW hm]
    exact Nat.zero_lt_sub_of_lt (bitVec_toNat_lt_pow y)

private theorem decodeScalar_signed_eq_zero_iff (w : IntWidth)
    (y : BitVec (8 * w.byteSize)) :
    (decodeScalar (bvToScalar w true y) == 0) = decide (y.toNat = 0) := by
  have hZero : (0 : Int) = decodeScalar (bvToScalar w true
      (BitVec.ofNat (8 * w.byteSize) 0)) := by
    have hm : Anneal.BitVecArith.msb (BitVec.ofNat (8 * w.byteSize) 0) =
        false := by
      have hW : 0 < 8 * w.byteSize := by
        rw [← intWidth_bitWidth_eq_eight_mul]
        exact intWidth_bitWidth_pos w
      rw [Anneal.BitVecArith.msb_eq_false_iff hW, Anneal.BitVec.toNat_zero]
      exact nat_two_pow_pos _
    rw [decodeScalar_signed_of_msb_false hm, Anneal.BitVec.toNat_zero]
    rfl
  cases Nat.decEq y.toNat 0 with
  | isTrue hEq =>
    have hy0 : y = BitVec.ofNat (8 * w.byteSize) 0 :=
      Anneal.BitVec.eq_of_toNat_eq (hEq.trans (Anneal.BitVec.toNat_zero _).symm)
    subst hy0
    rw [← hZero, beq_self_eq_true, decide_eq_true (Anneal.BitVec.toNat_zero _)]
  | isFalse hNe =>
    have hyNe : y ≠ BitVec.ofNat (8 * w.byteSize) 0 :=
      fun h => hNe (h ▸ Anneal.BitVec.toNat_zero _)
    have hDNe : decodeScalar (bvToScalar w true y) ≠ 0 := by
      intro hEq
      rw [hZero] at hEq
      exact hyNe ((decodeScalar_eq_iff w true y _).mp hEq)
    have hBeq : (decodeScalar (bvToScalar w true y) == 0) = false := by
      cases hc : decodeScalar (bvToScalar w true y) == 0 with
      | false => rfl
      | true => exact False.elim (hDNe (of_decide_eq_true hc))
    rw [hBeq, decide_eq_false hNe]

private theorem decodeScalar_signed_eq_min_iff (w : IntWidth)
    (x : BitVec (8 * w.byteSize)) :
    (decodeScalar (bvToScalar w true x) == signedMinInt w) =
      (x == Anneal.BitVecArith.signBit (w := 8 * w.byteSize)) := by
  have hMin : signedMinInt w =
      decodeScalar (bvToScalar w true
        (Anneal.BitVecArith.signBit (w := 8 * w.byteSize))) := by
    rw [decodeScalar_signed_eq_bvToInt, bvToInt_signBit]
  cases Anneal.ClassicalEm.prop_em
      (x = Anneal.BitVecArith.signBit (w := 8 * w.byteSize)) with
  | inl hEq =>
    subst hEq
    rw [← hMin, beq_self_eq_true, beq_self_eq_true]
  | inr hNe =>
    have hDNe : decodeScalar (bvToScalar w true x) ≠ signedMinInt w := by
      intro hEq
      rw [hMin] at hEq
      exact hNe ((decodeScalar_eq_iff w true x _).mp hEq)
    have h1 : (decodeScalar (bvToScalar w true x) == signedMinInt w) = false := by
      cases hc : decodeScalar (bvToScalar w true x) == signedMinInt w with
      | false => rfl
      | true => exact False.elim (hDNe (of_decide_eq_true hc))
    have h2 : (x == Anneal.BitVecArith.signBit (w := 8 * w.byteSize)) = false := by
      cases hc : x == Anneal.BitVecArith.signBit (w := 8 * w.byteSize) with
      | false => rfl
      | true => exact False.elim (hNe (of_decide_eq_true hc))
    rw [h1, h2]

private theorem decodeScalar_signed_eq_neg_one_iff (w : IntWidth)
    (y : BitVec (8 * w.byteSize)) :
    (decodeScalar (bvToScalar w true y) == Neg.neg 1) =
      (y == Anneal.BitVec.allOnes (8 * w.byteSize)) := by
  have hW : 0 < 8 * w.byteSize := by
    rw [← intWidth_bitWidth_eq_eight_mul]
    exact intWidth_bitWidth_pos w
  have hNeg1 : Neg.neg (1 : Int) =
      decodeScalar (bvToScalar w true
        (Anneal.BitVec.allOnes (8 * w.byteSize))) := by
    rw [decodeScalar_signed_eq_bvToInt, bvToInt_allOnes hW]
  cases Anneal.ClassicalEm.prop_em
      (y = Anneal.BitVec.allOnes (8 * w.byteSize)) with
  | inl hEq =>
    subst hEq
    rw [← hNeg1, beq_self_eq_true, beq_self_eq_true]
  | inr hNe =>
    have hDNe : decodeScalar (bvToScalar w true y) ≠ Neg.neg 1 := by
      intro hEq
      rw [hNeg1] at hEq
      exact hNe ((decodeScalar_eq_iff w true y _).mp hEq)
    have h1 : (decodeScalar (bvToScalar w true y) == Neg.neg 1) = false := by
      cases hc : decodeScalar (bvToScalar w true y) == Neg.neg 1 with
      | false => rfl
      | true => exact False.elim (hDNe (of_decide_eq_true hc))
    have h2 : (y == Anneal.BitVec.allOnes (8 * w.byteSize)) = false := by
      cases hc : y == Anneal.BitVec.allOnes (8 * w.byteSize) with
      | false => rfl
      | true => exact False.elim (hNe (of_decide_eq_true hc))
    rw [h1, h2]

/-- Signed `evalBinOp .div` faults with `.error .undefined` when `y.toNat = 0`.
-/
theorem evalBinOp_div_signed_zero_fault (w : IntWidth)
    (x : BitVec (8 * w.byteSize)) {y : BitVec (8 * w.byteSize)}
    (hy : y.toNat = 0) :
    evalBinOp .div (.scalar (bvToScalar w true x))
        (.scalar (bvToScalar w true y)) = .error .undefined := by
  unfold evalBinOp evalArithOp
  dsimp only
  rw [if_bool_false (rfl : BinOp.div.isShift = false),
    bvToScalar_width, bvToScalar_width, bvToScalar_signed, bvToScalar_signed,
    if_bool_false (evalBinOp_header_eq w true),
    decodeScalar_signed_eq_zero_iff w y, decide_eq_true hy]
  rfl

/-- Signed `evalBinOp .div` faults with `.error .undefined` on `INT_MIN / -1`.
-/
theorem evalBinOp_div_signed_min_neg_one_fault (w : IntWidth) :
    evalBinOp .div
        (.scalar (bvToScalar w true
          (Anneal.BitVecArith.signBit (w := 8 * w.byteSize))))
        (.scalar (bvToScalar w true
          (Anneal.BitVec.allOnes (8 * w.byteSize)))) = .error .undefined := by
  unfold evalBinOp evalArithOp
  dsimp only
  rw [if_bool_false (rfl : BinOp.div.isShift = false),
    bvToScalar_width, bvToScalar_width, bvToScalar_signed, bvToScalar_signed,
    if_bool_false (evalBinOp_header_eq w true)]
  have hYnz : (Anneal.BitVec.allOnes (8 * w.byteSize)).toNat ≠ 0 := by
    rw [Anneal.BitVec.toNat_allOnes]
    exact Nat.ne_of_gt (Nat.zero_lt_sub_of_lt
      (Nat.lt_of_lt_of_le (by decide : 1 < Nat.pow 2 8)
        (Nat.pow_le_pow_right (by decide : 0 < 2) (intWidth_eight_le w))))
  rw [decodeScalar_signed_eq_zero_iff, decide_eq_false hYnz, Bool.and_false,
    if_false_eq, decodeScalar_signed_eq_min_iff,
    decodeScalar_signed_eq_neg_one_iff, beq_self_eq_true, beq_self_eq_true]
  rfl

/-- Signed `evalBinOp .rem` faults with `.error .undefined` when `y.toNat = 0`.
-/
theorem evalBinOp_rem_signed_zero_fault (w : IntWidth)
    (x : BitVec (8 * w.byteSize)) {y : BitVec (8 * w.byteSize)}
    (hy : y.toNat = 0) :
    evalBinOp .rem (.scalar (bvToScalar w true x))
        (.scalar (bvToScalar w true y)) = .error .undefined := by
  unfold evalBinOp evalArithOp
  dsimp only
  rw [if_bool_false (rfl : BinOp.rem.isShift = false),
    bvToScalar_width, bvToScalar_width, bvToScalar_signed, bvToScalar_signed,
    if_bool_false (evalBinOp_header_eq w true),
    decodeScalar_signed_eq_zero_iff w y, decide_eq_true hy]
  rfl

/-- Signed `evalBinOp .rem` faults with `.error .undefined` on `INT_MIN % -1`.
-/
theorem evalBinOp_rem_signed_min_neg_one_fault (w : IntWidth) :
    evalBinOp .rem
        (.scalar (bvToScalar w true
          (Anneal.BitVecArith.signBit (w := 8 * w.byteSize))))
        (.scalar (bvToScalar w true
          (Anneal.BitVec.allOnes (8 * w.byteSize)))) = .error .undefined := by
  unfold evalBinOp evalArithOp
  dsimp only
  rw [if_bool_false (rfl : BinOp.rem.isShift = false),
    bvToScalar_width, bvToScalar_width, bvToScalar_signed, bvToScalar_signed,
    if_bool_false (evalBinOp_header_eq w true)]
  have hYnz : (Anneal.BitVec.allOnes (8 * w.byteSize)).toNat ≠ 0 := by
    rw [Anneal.BitVec.toNat_allOnes]
    exact Nat.ne_of_gt (Nat.zero_lt_sub_of_lt
      (Nat.lt_of_lt_of_le (by decide : 1 < Nat.pow 2 8)
        (Nat.pow_le_pow_right (by decide : 0 < 2) (intWidth_eight_le w))))
  rw [decodeScalar_signed_eq_zero_iff, decide_eq_false hYnz, Bool.and_false,
    if_false_eq, decodeScalar_signed_eq_min_iff,
    decodeScalar_signed_eq_neg_one_iff, beq_self_eq_true, beq_self_eq_true]
  rfl

private theorem bvOfInt_ofNat (W n : Nat) :
    bvOfInt W (Int.ofNat n) = BitVec.ofNat W n := by
  apply Anneal.BitVec.eq_of_toNat_eq
  rw [toNat_bvOfInt_ofNat, Anneal.BitVec.toNat_ofNat]

/-- Signed `evalBinOp .div` returns `bvSdiv x y` whenever `y ≠ 0` and
`¬ (x = signBit ∧ y = allOnes)`. -/
theorem evalBinOp_div_signed_eq (w : IntWidth)
    {x y : BitVec (8 * w.byteSize)} (hy : y.toNat ≠ 0)
    (hNoOvf : ¬ (x = Anneal.BitVecArith.signBit (w := 8 * w.byteSize) ∧
        y = Anneal.BitVec.allOnes (8 * w.byteSize))) :
    evalBinOp .div (.scalar (bvToScalar w true x))
        (.scalar (bvToScalar w true y)) =
      .ok (.scalar (bvToScalar w true (bvSdiv x y))) := by
  have hW : 0 < 8 * w.byteSize := by
    rw [← intWidth_bitWidth_eq_eight_mul]
    exact intWidth_bitWidth_pos w
  let W := 8 * w.byteSize
  have hMinNe : (x == Anneal.BitVecArith.signBit (w := W) &&
      y == Anneal.BitVec.allOnes W) = false := by
    cases hx : x == Anneal.BitVecArith.signBit (w := W)
    · rfl
    · cases hy1 : y == Anneal.BitVec.allOnes W
      · rfl
      · exact False.elim (hNoOvf ⟨of_decide_eq_true hx, of_decide_eq_true hy1⟩)
  unfold evalBinOp evalArithOp
  dsimp only
  rw [if_bool_false (rfl : BinOp.div.isShift = false),
    bvToScalar_width, bvToScalar_width, bvToScalar_signed, bvToScalar_signed,
    if_bool_false (evalBinOp_header_eq w true),
    decodeScalar_signed_eq_zero_iff w y, decide_eq_false hy, Bool.and_false,
    if_false_eq, decodeScalar_signed_eq_min_iff w x,
    decodeScalar_signed_eq_neg_one_iff w y, hMinNe, Bool.and_false, if_false_eq]
  let l := decodeScalar (bvToScalar w true x)
  let r := decodeScalar (bvToScalar w true y)
  let ⟨lossy, hTrunc⟩ := truncateScalar_val_eq w true (intTdiv l r)
  rw [hTrunc]
  dsimp only
  have hU : BinOp.div.isUnchecked = false := rfl
  have hO : BinOp.div.isOverflowing = false := rfl
  rw [hU, hO, Bool.and_false, if_false_eq, if_false_eq]
  have hBvEq : bvOfInt W (intTdiv l r) = bvSdiv x y := by
    unfold bvSdiv
    have hbyPos : 0 < (bvAbs y).toNat := bvAbs_pos_of_ne_zero hW hy
    have hUdiv : Anneal.BitVec.udiv (bvAbs x) (bvAbs y) =
        BitVec.ofNat W (Nat.div (bvAbs x).toNat (bvAbs y).toNat) := by
      apply Anneal.BitVec.eq_of_toNat_eq
      rw [Anneal.BitVec.toNat_udiv, Anneal.BitVec.toNat_ofNat]
      exact (nat_mod_eq_of_lt (Nat.lt_of_le_of_lt (Nat.div_le_self _ _)
        (bitVec_toNat_lt_pow (bvAbs x)))).symm
    cases hmx : Anneal.BitVecArith.msb x <;>
      cases hmy : Anneal.BitVecArith.msb y
    · have hl : l = Int.ofNat (bvAbs x).toNat := by
        dsimp only [l]
        rw [decodeScalar_signed_of_msb_false hmx, bvAbs_toNat_pos hW hmx]
      have hr : r = Int.ofNat (bvAbs y).toNat := by
        dsimp only [r]
        rw [decodeScalar_signed_of_msb_false hmy, bvAbs_toNat_pos hW hmy]
      rw [hl, hr]
      change bvOfInt W (intTdiv (Int.ofNat (bvAbs x).toNat)
          (Int.ofNat (bvAbs y).toNat)) =
        Anneal.BitVec.udiv (bvAbs x) (bvAbs y)
      unfold intTdiv
      dsimp only
      rw [bvOfInt_ofNat, hUdiv]
    · have hl : l = Int.ofNat (bvAbs x).toNat := by
        dsimp only [l]
        rw [decodeScalar_signed_of_msb_false hmx, bvAbs_toNat_pos hW hmx]
      have hyEq : Nat.succ (Nat.pow 2 W - 1 - y.toNat) = (bvAbs y).toNat := by
        rw [bvAbs_toNat_neg hW hmy]
        have hC := Nat.sub_add_cancel
          (Nat.zero_lt_sub_of_lt (bitVec_toNat_lt_pow y))
        rw [Nat.sub_sub, Nat.add_comm y.toNat 1, ← Nat.sub_sub] at hC
        exact hC
      have hr : r = Int.negSucc (Nat.pow 2 W - 1 - y.toNat) := by
        dsimp only [r]
        exact decodeScalar_signed_of_msb_true hmy
      rw [hl, hr]
      change bvOfInt W (intTdiv (Int.ofNat (bvAbs x).toNat)
          (Int.negSucc (Nat.pow 2 W - 1 - y.toNat))) =
        Anneal.BitVecArith.neg (Anneal.BitVec.udiv (bvAbs x) (bvAbs y))
      unfold intTdiv
      dsimp only
      rw [hyEq]
      change bvOfInt W (Neg.neg (Int.ofNat _)) = _
      rw [bvOfInt_neg_ofNat, hUdiv]
    · have hxEq : Nat.succ (Nat.pow 2 W - 1 - x.toNat) = (bvAbs x).toNat := by
        rw [bvAbs_toNat_neg hW hmx]
        have hC := Nat.sub_add_cancel
          (Nat.zero_lt_sub_of_lt (bitVec_toNat_lt_pow x))
        rw [Nat.sub_sub, Nat.add_comm x.toNat 1, ← Nat.sub_sub] at hC
        exact hC
      have hl : l = Int.negSucc (Nat.pow 2 W - 1 - x.toNat) := by
        dsimp only [l]
        exact decodeScalar_signed_of_msb_true hmx
      have hr : r = Int.ofNat (bvAbs y).toNat := by
        dsimp only [r]
        rw [decodeScalar_signed_of_msb_false hmy, bvAbs_toNat_pos hW hmy]
      rw [hl, hr]
      change bvOfInt W (intTdiv (Int.negSucc (Nat.pow 2 W - 1 - x.toNat))
          (Int.ofNat (bvAbs y).toNat)) =
        Anneal.BitVecArith.neg (Anneal.BitVec.udiv (bvAbs x) (bvAbs y))
      unfold intTdiv
      dsimp only
      rw [hxEq]
      change bvOfInt W (Neg.neg (Int.ofNat _)) = _
      rw [bvOfInt_neg_ofNat, hUdiv]
    · have hxEq : Nat.succ (Nat.pow 2 W - 1 - x.toNat) = (bvAbs x).toNat := by
        rw [bvAbs_toNat_neg hW hmx]
        have hC := Nat.sub_add_cancel
          (Nat.zero_lt_sub_of_lt (bitVec_toNat_lt_pow x))
        rw [Nat.sub_sub, Nat.add_comm x.toNat 1, ← Nat.sub_sub] at hC
        exact hC
      have hyEq : Nat.succ (Nat.pow 2 W - 1 - y.toNat) = (bvAbs y).toNat := by
        rw [bvAbs_toNat_neg hW hmy]
        have hC := Nat.sub_add_cancel
          (Nat.zero_lt_sub_of_lt (bitVec_toNat_lt_pow y))
        rw [Nat.sub_sub, Nat.add_comm y.toNat 1, ← Nat.sub_sub] at hC
        exact hC
      have hl : l = Int.negSucc (Nat.pow 2 W - 1 - x.toNat) := by
        dsimp only [l]
        exact decodeScalar_signed_of_msb_true hmx
      have hr : r = Int.negSucc (Nat.pow 2 W - 1 - y.toNat) := by
        dsimp only [r]
        exact decodeScalar_signed_of_msb_true hmy
      rw [hl, hr]
      change bvOfInt W (intTdiv (Int.negSucc (Nat.pow 2 W - 1 - x.toNat))
          (Int.negSucc (Nat.pow 2 W - 1 - y.toNat))) =
        Anneal.BitVec.udiv (bvAbs x) (bvAbs y)
      unfold intTdiv
      dsimp only
      rw [hxEq, hyEq, bvOfInt_ofNat, hUdiv]
  change Except.ok (Val.scalar ⟨w, true, truncateBits w (bvOfInt 128 (intTdiv l r))⟩) = _
  rw [truncateBits_bvOfInt_eq_bvZeroExtend, hBvEq]
  rfl

/-- Signed `evalBinOp .rem` returns `bvSrem x y` whenever `y ≠ 0` and
`¬ (x = signBit ∧ y = allOnes)`. -/
theorem evalBinOp_rem_signed_eq (w : IntWidth)
    {x y : BitVec (8 * w.byteSize)} (hy : y.toNat ≠ 0)
    (hNoOvf : ¬ (x = Anneal.BitVecArith.signBit (w := 8 * w.byteSize) ∧
        y = Anneal.BitVec.allOnes (8 * w.byteSize))) :
    evalBinOp .rem (.scalar (bvToScalar w true x))
        (.scalar (bvToScalar w true y)) =
      .ok (.scalar (bvToScalar w true (bvSrem x y))) := by
  have hW : 0 < 8 * w.byteSize := by
    rw [← intWidth_bitWidth_eq_eight_mul]
    exact intWidth_bitWidth_pos w
  let W := 8 * w.byteSize
  have hMinNe : (x == Anneal.BitVecArith.signBit (w := W) &&
      y == Anneal.BitVec.allOnes W) = false := by
    cases hx : x == Anneal.BitVecArith.signBit (w := W)
    · rfl
    · cases hy1 : y == Anneal.BitVec.allOnes W
      · rfl
      · exact False.elim (hNoOvf ⟨of_decide_eq_true hx, of_decide_eq_true hy1⟩)
  unfold evalBinOp evalArithOp
  dsimp only
  rw [if_bool_false (rfl : BinOp.rem.isShift = false),
    bvToScalar_width, bvToScalar_width, bvToScalar_signed, bvToScalar_signed,
    if_bool_false (evalBinOp_header_eq w true),
    decodeScalar_signed_eq_zero_iff w y, decide_eq_false hy, Bool.and_false,
    if_false_eq, decodeScalar_signed_eq_min_iff w x,
    decodeScalar_signed_eq_neg_one_iff w y, hMinNe, Bool.and_false, if_false_eq]
  let l := decodeScalar (bvToScalar w true x)
  let r := decodeScalar (bvToScalar w true y)
  let ⟨lossy, hTrunc⟩ := truncateScalar_val_eq w true (intTmod l r)
  rw [hTrunc]
  dsimp only
  have hU : BinOp.rem.isUnchecked = false := rfl
  have hO : BinOp.rem.isOverflowing = false := rfl
  rw [hU, hO, Bool.and_false, if_false_eq, if_false_eq]
  have hBvEq : bvOfInt W (intTmod l r) = bvSrem x y := by
    unfold bvSrem
    have hbyPos : 0 < (bvAbs y).toNat := bvAbs_pos_of_ne_zero hW hy
    have hUrem : Anneal.BitVecArith.urem (bvAbs x) (bvAbs y) =
        BitVec.ofNat W (Nat.mod (bvAbs x).toNat (bvAbs y).toNat) := by
      apply Anneal.BitVec.eq_of_toNat_eq
      rw [Anneal.BitVec.toNat_ofNat]
      exact (nat_mod_eq_of_lt (Nat.lt_trans (Nat.mod_lt _ hbyPos)
        (bitVec_toNat_lt_pow (bvAbs y)))).symm
    cases hmx : Anneal.BitVecArith.msb x <;>
      cases hmy : Anneal.BitVecArith.msb y
    · have hl : l = Int.ofNat (bvAbs x).toNat := by
        dsimp only [l]
        rw [decodeScalar_signed_of_msb_false hmx, bvAbs_toNat_pos hW hmx]
      have hr : r = Int.ofNat (bvAbs y).toNat := by
        dsimp only [r]
        rw [decodeScalar_signed_of_msb_false hmy, bvAbs_toNat_pos hW hmy]
      rw [hl, hr, if_false_eq]
      unfold intTmod
      rw [bvOfInt_ofNat, hUrem]
    · have hl : l = Int.ofNat (bvAbs x).toNat := by
        dsimp only [l]
        rw [decodeScalar_signed_of_msb_false hmx, bvAbs_toNat_pos hW hmx]
      have hyEq : Nat.succ (Nat.pow 2 W - 1 - y.toNat) = (bvAbs y).toNat := by
        rw [bvAbs_toNat_neg hW hmy]
        have hC := Nat.sub_add_cancel
          (Nat.zero_lt_sub_of_lt (bitVec_toNat_lt_pow y))
        rw [Nat.sub_sub, Nat.add_comm y.toNat 1, ← Nat.sub_sub] at hC
        exact hC
      have hr : r = Int.negSucc (Nat.pow 2 W - 1 - y.toNat) := by
        dsimp only [r]
        exact decodeScalar_signed_of_msb_true hmy
      rw [hl, hr, if_false_eq]
      unfold intTmod
      dsimp only
      rw [hyEq, bvOfInt_ofNat, hUrem]
    · have hxEq : Nat.succ (Nat.pow 2 W - 1 - x.toNat) = (bvAbs x).toNat := by
        rw [bvAbs_toNat_neg hW hmx]
        have hC := Nat.sub_add_cancel
          (Nat.zero_lt_sub_of_lt (bitVec_toNat_lt_pow x))
        rw [Nat.sub_sub, Nat.add_comm x.toNat 1, ← Nat.sub_sub] at hC
        exact hC
      have hl : l = Int.negSucc (Nat.pow 2 W - 1 - x.toNat) := by
        dsimp only [l]
        exact decodeScalar_signed_of_msb_true hmx
      have hr : r = Int.ofNat (bvAbs y).toNat := by
        dsimp only [r]
        rw [decodeScalar_signed_of_msb_false hmy, bvAbs_toNat_pos hW hmy]
      rw [hl, hr, if_true_eq]
      unfold intTmod
      dsimp only
      rw [hxEq]
      change bvOfInt W (Neg.neg (Int.ofNat _)) = _
      rw [bvOfInt_neg_ofNat, hUrem]
    · have hxEq : Nat.succ (Nat.pow 2 W - 1 - x.toNat) = (bvAbs x).toNat := by
        rw [bvAbs_toNat_neg hW hmx]
        have hC := Nat.sub_add_cancel
          (Nat.zero_lt_sub_of_lt (bitVec_toNat_lt_pow x))
        rw [Nat.sub_sub, Nat.add_comm x.toNat 1, ← Nat.sub_sub] at hC
        exact hC
      have hyEq : Nat.succ (Nat.pow 2 W - 1 - y.toNat) = (bvAbs y).toNat := by
        rw [bvAbs_toNat_neg hW hmy]
        have hC := Nat.sub_add_cancel
          (Nat.zero_lt_sub_of_lt (bitVec_toNat_lt_pow y))
        rw [Nat.sub_sub, Nat.add_comm y.toNat 1, ← Nat.sub_sub] at hC
        exact hC
      have hl : l = Int.negSucc (Nat.pow 2 W - 1 - x.toNat) := by
        dsimp only [l]
        exact decodeScalar_signed_of_msb_true hmx
      have hr : r = Int.negSucc (Nat.pow 2 W - 1 - y.toNat) := by
        dsimp only [r]
        exact decodeScalar_signed_of_msb_true hmy
      rw [hl, hr, if_true_eq]
      unfold intTmod
      dsimp only
      rw [hxEq, hyEq]
      change bvOfInt W (Neg.neg (Int.ofNat _)) = _
      rw [bvOfInt_neg_ofNat, hUrem]
  change Except.ok (Val.scalar ⟨w, true, truncateBits w (bvOfInt 128 (intTmod l r))⟩) = _
  rw [truncateBits_bvOfInt_eq_bvZeroExtend, hBvEq]
  rfl


/-! ## 3. Remaining `evalBinOp` Scalar, `bool`, and `char` Bridges -/

/-- Computable `OrderingVal` comparison on natural numbers, matching
`cmpOrderingOfInt` on `Int.ofNat`. -/
@[expose] def cmpOrderingOfNat (a b : Nat) : OrderingVal :=
  if decide (a < b) then .less
  else if decide (a = b) then .equal
  else .greater

/-- Computable signed `OrderingVal` comparison on `BitVec w` via `signedKey`. -/
@[expose] def bvScmp {w : Nat} (x y : BitVec w) : OrderingVal :=
  cmpOrderingOfNat
    (Anneal.BitVecArith.signedKey x) (Anneal.BitVecArith.signedKey y)

theorem cmpOrderingOfNat_eq_less_iff {a b : Nat} :
    cmpOrderingOfNat a b = .less ↔ a < b := by
  unfold cmpOrderingOfNat
  cases Nat.lt_or_ge a b with
  | inl hLt =>
    rw [decide_eq_true hLt]
    exact ⟨fun _ => hLt, fun _ => rfl⟩
  | inr hGe =>
    rw [decide_eq_false (Nat.not_lt_of_ge hGe)]
    cases Nat.decEq a b with
    | isTrue hEq =>
      rw [decide_eq_true hEq]
      exact ⟨(fun h => by cases h),
        fun hLt => False.elim (Nat.not_lt_of_ge hGe hLt)⟩
    | isFalse hNe =>
      rw [decide_eq_false hNe]
      exact ⟨(fun h => by cases h),
        fun hLt => False.elim (Nat.not_lt_of_ge hGe hLt)⟩

theorem cmpOrderingOfNat_eq_equal_iff {a b : Nat} :
    cmpOrderingOfNat a b = .equal ↔ a = b := by
  unfold cmpOrderingOfNat
  cases Nat.lt_or_ge a b with
  | inl hLt =>
    rw [decide_eq_true hLt]
    exact ⟨(fun h => by cases h), fun hEq => False.elim (Nat.ne_of_lt hLt hEq)⟩
  | inr hGe =>
    rw [decide_eq_false (Nat.not_lt_of_ge hGe)]
    cases Nat.decEq a b with
    | isTrue hEq =>
      rw [decide_eq_true hEq]
      exact ⟨fun _ => hEq, fun _ => rfl⟩
    | isFalse hNe =>
      rw [decide_eq_false hNe]
      exact ⟨(fun h => by cases h), fun hEq => False.elim (hNe hEq)⟩

theorem cmpOrderingOfNat_eq_greater_iff {a b : Nat} :
    cmpOrderingOfNat a b = .greater ↔ b < a := by
  unfold cmpOrderingOfNat
  cases Nat.lt_or_ge a b with
  | inl hLt =>
    rw [decide_eq_true hLt]
    exact ⟨(fun h => by cases h),
      fun hGt => False.elim (Nat.lt_asymm hLt hGt)⟩
  | inr hGe =>
    rw [decide_eq_false (Nat.not_lt_of_ge hGe)]
    cases Nat.decEq a b with
    | isTrue hEq =>
      rw [decide_eq_true hEq]
      exact ⟨(fun h => by cases h),
        fun hGt => False.elim (Nat.ne_of_gt hGt hEq)⟩
    | isFalse hNe =>
      rw [decide_eq_false hNe]
      have hGt : b < a := Nat.lt_of_le_of_ne hGe (fun h => hNe h.symm)
      exact ⟨fun _ => hGt, fun _ => rfl⟩

theorem bvScmp_eq_less_iff {w : Nat} (x y : BitVec w) :
    bvScmp x y = .less ↔ Anneal.BitVecArith.slt x y :=
  cmpOrderingOfNat_eq_less_iff

theorem bvScmp_eq_equal_iff {w : Nat} (x y : BitVec w) :
    bvScmp x y = .equal ↔ x = y := by
  unfold bvScmp
  rw [cmpOrderingOfNat_eq_equal_iff]
  exact ⟨Anneal.BitVecArith.signedKey_injective, fun h => by rw [h]⟩

theorem bvScmp_eq_greater_iff {w : Nat} (x y : BitVec w) :
    bvScmp x y = .greater ↔ Anneal.BitVecArith.slt y x :=
  cmpOrderingOfNat_eq_greater_iff

/-- `evalBinOp .ne` decides bitvector inequality `x ≠ y` across both
signedness modes. -/
theorem evalBinOp_ne_eq (w : IntWidth) (s : Bool)
    (x y : BitVec (8 * w.byteSize)) :
    evalBinOp .ne (.scalar (bvToScalar w s x))
        (.scalar (bvToScalar w s y)) =
      .ok (.bool (decide (x ≠ y))) := by
  unfold evalBinOp
  dsimp only
  rw [if_bool_false (rfl : BinOp.ne.isShift = false), bvToScalar_width,
    bvToScalar_width, bvToScalar_signed, bvToScalar_signed,
    if_bool_false (evalBinOp_header_eq w s)]
  cases Nat.decEq x.toNat y.toNat with
  | isTrue hEq =>
    have hBv : x = y := Anneal.BitVec.eq_of_toNat_eq hEq
    subst hBv
    have hb : (decodeScalar (bvToScalar w s x) !=
        decodeScalar (bvToScalar w s x)) = false := by
      change (!(decodeScalar (bvToScalar w s x) ==
        decodeScalar (bvToScalar w s x))) = false
      rw [beq_self_eq_true]
      rfl
    rw [hb, decide_eq_false (fun h => h rfl)]
  | isFalse hNe =>
    have hBvNe : x ≠ y := fun h => hNe (congrArg BitVec.toNat h)
    have hDecNe : decodeScalar (bvToScalar w s x) ≠
        decodeScalar (bvToScalar w s y) :=
      fun h => hBvNe ((decodeScalar_eq_iff w s x y).mp h)
    have hb : (decodeScalar (bvToScalar w s x) !=
        decodeScalar (bvToScalar w s y)) = true :=
      bne_iff_ne.mpr hDecNe
    rw [hb, decide_eq_true hBvNe]

/-- Unsigned `evalBinOp .gt` decides `y.toNat < x.toNat`. -/
theorem evalBinOp_gt_unsigned_eq (w : IntWidth)
    (x y : BitVec (8 * w.byteSize)) :
    evalBinOp .gt (.scalar (bvToScalar w false x))
        (.scalar (bvToScalar w false y)) =
      .ok (.bool (decide (y.toNat < x.toNat))) := by
  unfold evalBinOp
  dsimp only
  rw [if_bool_false (rfl : BinOp.gt.isShift = false), bvToScalar_width,
    bvToScalar_width, bvToScalar_signed, bvToScalar_signed,
    if_bool_false (evalBinOp_header_eq w false),
    decodeScalar_unsigned_eq, decodeScalar_unsigned_eq]
  cases Nat.lt_or_ge y.toNat x.toNat with
  | inl h =>
    have hGt : Int.ofNat x.toNat > Int.ofNat y.toNat := int_ofNat_lt_iff.mpr h
    rw [decide_eq_true h, decide_eq_true hGt]
  | inr h =>
    have hNot : ¬ (Int.ofNat x.toNat > Int.ofNat y.toNat) :=
      fun hGt => Nat.not_lt_of_ge h (int_ofNat_lt_iff.mp hGt)
    rw [decide_eq_false (Nat.not_lt_of_ge h), decide_eq_false hNot]

/-- Unsigned `evalBinOp .ge` decides `y.toNat ≤ x.toNat`. -/
theorem evalBinOp_ge_unsigned_eq (w : IntWidth)
    (x y : BitVec (8 * w.byteSize)) :
    evalBinOp .ge (.scalar (bvToScalar w false x))
        (.scalar (bvToScalar w false y)) =
      .ok (.bool (decide (y.toNat ≤ x.toNat))) := by
  unfold evalBinOp
  dsimp only
  rw [if_bool_false (rfl : BinOp.ge.isShift = false), bvToScalar_width,
    bvToScalar_width, bvToScalar_signed, bvToScalar_signed,
    if_bool_false (evalBinOp_header_eq w false),
    decodeScalar_unsigned_eq, decodeScalar_unsigned_eq]
  cases Nat.lt_or_ge x.toNat y.toNat with
  | inl h =>
    have hN : ¬ (y.toNat ≤ x.toNat) := Nat.not_le_of_gt h
    have hNot : ¬ (Int.ofNat x.toNat ≥ Int.ofNat y.toNat) :=
      fun hGe => hN (int_ofNat_le_iff.mp hGe)
    rw [decide_eq_false hN, decide_eq_false hNot]
  | inr h =>
    have hGe : Int.ofNat x.toNat ≥ Int.ofNat y.toNat := int_ofNat_le_iff.mpr h
    rw [decide_eq_true h, decide_eq_true hGe]

/-- Signed `evalBinOp .gt` computes `decide (signedKey y < signedKey x)`. -/
theorem evalBinOp_gt_signed_eq_decide (w : IntWidth)
    (x y : BitVec (8 * w.byteSize)) :
    evalBinOp .gt (.scalar (bvToScalar w true x))
        (.scalar (bvToScalar w true y)) =
      .ok (.bool (decide
        (Anneal.BitVecArith.signedKey y < Anneal.BitVecArith.signedKey x))) := by
  unfold evalBinOp
  dsimp only
  rw [if_bool_false (rfl : BinOp.gt.isShift = false), bvToScalar_width,
    bvToScalar_width, bvToScalar_signed, bvToScalar_signed,
    if_bool_false (evalBinOp_header_eq w true)]
  cases h : decide (decodeScalar (bvToScalar w true x) >
      decodeScalar (bvToScalar w true y)) with
  | true =>
    have hLt : Anneal.BitVecArith.signedKey y <
        Anneal.BitVecArith.signedKey x :=
      (decodeScalar_lt_iff_slt y x).mp (of_decide_eq_true h)
    rw [decide_eq_true hLt]
  | false =>
    have hNot : ¬ (Anneal.BitVecArith.signedKey y <
        Anneal.BitVecArith.signedKey x) :=
      fun hs => of_decide_eq_false h ((decodeScalar_lt_iff_slt y x).mpr hs)
    rw [decide_eq_false hNot]

/-- Signed `evalBinOp .gt` agrees with `Anneal.BitVecArith.slt y x`. -/
theorem evalBinOp_gt_signed_eq_slt (w : IntWidth)
    (x y : BitVec (8 * w.byteSize)) :
    ∃ b : Bool,
      evalBinOp .gt (.scalar (bvToScalar w true x))
          (.scalar (bvToScalar w true y)) = .ok (.bool b) ∧
      (b = true ↔ Anneal.BitVecArith.slt y x) := by
  refine ⟨decide (Anneal.BitVecArith.signedKey y <
      Anneal.BitVecArith.signedKey x), evalBinOp_gt_signed_eq_decide w x y, ?_⟩
  exact ⟨fun h => @of_decide_eq_true
      (Anneal.BitVecArith.signedKey y < Anneal.BitVecArith.signedKey x) _ h,
    fun h => @decide_eq_true
      (Anneal.BitVecArith.signedKey y < Anneal.BitVecArith.signedKey x) _ h⟩

/-- Signed `evalBinOp .ge` computes `decide (signedKey y ≤ signedKey x)`. -/
theorem evalBinOp_ge_signed_eq_decide (w : IntWidth)
    (x y : BitVec (8 * w.byteSize)) :
    evalBinOp .ge (.scalar (bvToScalar w true x))
        (.scalar (bvToScalar w true y)) =
      .ok (.bool (decide
        (Anneal.BitVecArith.signedKey y ≤ Anneal.BitVecArith.signedKey x))) := by
  unfold evalBinOp
  dsimp only
  rw [if_bool_false (rfl : BinOp.ge.isShift = false), bvToScalar_width,
    bvToScalar_width, bvToScalar_signed, bvToScalar_signed,
    if_bool_false (evalBinOp_header_eq w true)]
  cases h : decide (decodeScalar (bvToScalar w true x) ≥
      decodeScalar (bvToScalar w true y)) with
  | true =>
    have hLe : Anneal.BitVecArith.signedKey y ≤
        Anneal.BitVecArith.signedKey x :=
      (decodeScalar_le_iff_sle y x).mp (of_decide_eq_true h)
    rw [decide_eq_true hLe]
  | false =>
    have hNot : ¬ (Anneal.BitVecArith.signedKey y ≤
        Anneal.BitVecArith.signedKey x) :=
      fun hs => of_decide_eq_false h ((decodeScalar_le_iff_sle y x).mpr hs)
    rw [decide_eq_false hNot]

/-- Signed `evalBinOp .ge` agrees with `Anneal.BitVecArith.sle y x`. -/
theorem evalBinOp_ge_signed_eq_sle (w : IntWidth)
    (x y : BitVec (8 * w.byteSize)) :
    ∃ b : Bool,
      evalBinOp .ge (.scalar (bvToScalar w true x))
          (.scalar (bvToScalar w true y)) = .ok (.bool b) ∧
      (b = true ↔ Anneal.BitVecArith.sle y x) := by
  refine ⟨decide (Anneal.BitVecArith.signedKey y ≤
      Anneal.BitVecArith.signedKey x), evalBinOp_ge_signed_eq_decide w x y, ?_⟩
  exact ⟨fun h => @of_decide_eq_true
      (Anneal.BitVecArith.signedKey y ≤ Anneal.BitVecArith.signedKey x) _ h,
    fun h => @decide_eq_true
      (Anneal.BitVecArith.signedKey y ≤ Anneal.BitVecArith.signedKey x) _ h⟩

/-- Unsigned `evalBinOp .cmp` computes `cmpOrderingOfNat x.toNat y.toNat`. -/
theorem evalBinOp_cmp_unsigned_eq (w : IntWidth)
    (x y : BitVec (8 * w.byteSize)) :
    evalBinOp .cmp (.scalar (bvToScalar w false x))
        (.scalar (bvToScalar w false y)) =
      .ok (.ordering (cmpOrderingOfNat x.toNat y.toNat)) := by
  unfold evalBinOp cmpOrderingOfInt cmpOrderingOfNat
  dsimp only
  rw [if_bool_false (rfl : BinOp.cmp.isShift = false), bvToScalar_width,
    bvToScalar_width, bvToScalar_signed, bvToScalar_signed,
    if_bool_false (evalBinOp_header_eq w false),
    decodeScalar_unsigned_eq, decodeScalar_unsigned_eq]
  cases Nat.lt_or_ge x.toNat y.toNat with
  | inl hLt =>
    rw [decide_eq_true (int_ofNat_lt_iff.mpr hLt), decide_eq_true hLt]
    rfl
  | inr hGe =>
    have hNotLt : ¬ (Int.ofNat x.toNat < Int.ofNat y.toNat) :=
      fun h => Nat.not_lt_of_ge hGe (int_ofNat_lt_iff.mp h)
    rw [decide_eq_false hNotLt, decide_eq_false (Nat.not_lt_of_ge hGe)]
    cases Nat.eq_or_lt_of_le hGe with
    | inl hEq =>
      rw [decide_eq_true (congrArg Int.ofNat hEq.symm), decide_eq_true hEq.symm]
    | inr hGt =>
      have hNeNat : x.toNat ≠ y.toNat := Nat.ne_of_gt hGt
      have hNeInt : Int.ofNat x.toNat ≠ Int.ofNat y.toNat :=
        fun h => hNeNat (Int.ofNat.inj h)
      rw [decide_eq_false hNeInt, decide_eq_false hNeNat]

/-- Signed `evalBinOp .cmp` computes `bvScmp x y`. -/
theorem evalBinOp_cmp_signed_eq (w : IntWidth)
    (x y : BitVec (8 * w.byteSize)) :
    evalBinOp .cmp (.scalar (bvToScalar w true x))
        (.scalar (bvToScalar w true y)) =
      .ok (.ordering (bvScmp x y)) := by
  unfold evalBinOp bvScmp cmpOrderingOfInt cmpOrderingOfNat
  dsimp only
  rw [if_bool_false (rfl : BinOp.cmp.isShift = false), bvToScalar_width,
    bvToScalar_width, bvToScalar_signed, bvToScalar_signed,
    if_bool_false (evalBinOp_header_eq w true)]
  cases Nat.lt_or_ge
      (Anneal.BitVecArith.signedKey x) (Anneal.BitVecArith.signedKey y) with
  | inl hLt =>
    have hIntLt : decodeScalar (bvToScalar w true x) <
        decodeScalar (bvToScalar w true y) :=
      (decodeScalar_lt_iff_slt x y).mpr hLt
    rw [decide_eq_true hIntLt, decide_eq_true hLt]
    rfl
  | inr hGe =>
    have hNotIntLt : ¬ (decodeScalar (bvToScalar w true x) <
        decodeScalar (bvToScalar w true y)) :=
      fun h => Nat.not_lt_of_ge hGe ((decodeScalar_lt_iff_slt x y).mp h)
    rw [decide_eq_false hNotIntLt, decide_eq_false (Nat.not_lt_of_ge hGe)]
    cases Nat.eq_or_lt_of_le hGe with
    | inl hEq =>
      have hBvEq : x = y := Anneal.BitVecArith.signedKey_injective hEq.symm
      have hIntEq : decodeScalar (bvToScalar w true x) =
          decodeScalar (bvToScalar w true y) := by
        rw [hBvEq]
      rw [decide_eq_true hIntEq, decide_eq_true hEq.symm]
    | inr hGt =>
      have hNeKey : Anneal.BitVecArith.signedKey x ≠
          Anneal.BitVecArith.signedKey y := Nat.ne_of_gt hGt
      have hNeBv : x ≠ y := fun h => hNeKey (by rw [h])
      have hNeInt : decodeScalar (bvToScalar w true x) ≠
          decodeScalar (bvToScalar w true y) :=
        fun h => hNeBv ((decodeScalar_eq_iff w true x y).mp h)
      rw [decide_eq_false hNeInt, decide_eq_false hNeKey]

/-- Any non-shift `evalBinOp` with mismatched operand width or signedness
fails closed with `.error .unsupported`. -/
theorem evalBinOp_nonShift_mismatch_unsupported {op : BinOp}
    (hNonShift : op.isShift = false) {l r : ScalarVal}
    (hMis : (IntWidth.beq l.width r.width && (l.signed == r.signed)) = false) :
    evalBinOp op (.scalar l) (.scalar r) = .error .unsupported := by
  unfold evalBinOp
  dsimp only
  rw [if_bool_false hNonShift, hMis]
  rfl

/-- Pointer `BinOp.offset` on integer scalars always fails closed with
`.error .unsupported`. -/
theorem evalBinOp_offset_scalar_unsupported (l r : ScalarVal) :
    evalBinOp .offset (.scalar l) (.scalar r) = .error .unsupported := by
  unfold evalBinOp
  dsimp only
  cases IntWidth.beq l.width r.width && (l.signed == r.signed) <;> rfl

/-- `evalBinOp .eq` on `.bool`. -/
theorem evalBinOp_bool_eq_eq (l r : Bool) :
    evalBinOp .eq (.bool l) (.bool r) = .ok (.bool (l == r)) := rfl

/-- `evalBinOp .ne` on `.bool`. -/
theorem evalBinOp_bool_ne_eq (l r : Bool) :
    evalBinOp .ne (.bool l) (.bool r) = .ok (.bool (l != r)) := rfl

/-- `evalBinOp .lt` on `.bool`. -/
theorem evalBinOp_bool_lt_eq (l r : Bool) :
    evalBinOp .lt (.bool l) (.bool r) = .ok (.bool (!l && r)) := rfl

/-- `evalBinOp .le` on `.bool`. -/
theorem evalBinOp_bool_le_eq (l r : Bool) :
    evalBinOp .le (.bool l) (.bool r) = .ok (.bool (!l || r)) := rfl

/-- `evalBinOp .gt` on `.bool`. -/
theorem evalBinOp_bool_gt_eq (l r : Bool) :
    evalBinOp .gt (.bool l) (.bool r) = .ok (.bool (l && !r)) := rfl

/-- `evalBinOp .ge` on `.bool`. -/
theorem evalBinOp_bool_ge_eq (l r : Bool) :
    evalBinOp .ge (.bool l) (.bool r) = .ok (.bool (l || !r)) := rfl

/-- `evalBinOp .bitAnd` on `.bool`. -/
theorem evalBinOp_bool_bitAnd_eq (l r : Bool) :
    evalBinOp .bitAnd (.bool l) (.bool r) = .ok (.bool (l && r)) := rfl

/-- `evalBinOp .bitOr` on `.bool`. -/
theorem evalBinOp_bool_bitOr_eq (l r : Bool) :
    evalBinOp .bitOr (.bool l) (.bool r) = .ok (.bool (l || r)) := rfl

/-- `evalBinOp .bitXor` on `.bool`. -/
theorem evalBinOp_bool_bitXor_eq (l r : Bool) :
    evalBinOp .bitXor (.bool l) (.bool r) = .ok (.bool (bne l r)) := rfl

/-- `evalBinOp .cmp` on `.bool` fails closed with `.error .unsupported`. -/
theorem evalBinOp_bool_cmp_unsupported (l r : Bool) :
    evalBinOp .cmp (.bool l) (.bool r) = .error .unsupported := rfl

/-- All arithmetic, shift, `.cmp`, and `.offset` operators on `.bool` fail
closed with `.error .unsupported`. -/
theorem evalBinOp_bool_unsupported {op : BinOp}
    (h : op ≠ .eq ∧ op ≠ .ne ∧ op ≠ .lt ∧ op ≠ .le ∧ op ≠ .gt ∧ op ≠ .ge ∧
      op ≠ .bitAnd ∧ op ≠ .bitOr ∧ op ≠ .bitXor)
    (l r : Bool) :
    evalBinOp op (.bool l) (.bool r) = .error .unsupported := by
  cases op with
  | eq => exact False.elim (h.1 rfl)
  | ne => exact False.elim (h.2.1 rfl)
  | lt => exact False.elim (h.2.2.1 rfl)
  | le => exact False.elim (h.2.2.2.1 rfl)
  | gt => exact False.elim (h.2.2.2.2.1 rfl)
  | ge => exact False.elim (h.2.2.2.2.2.1 rfl)
  | bitAnd => exact False.elim (h.2.2.2.2.2.2.1 rfl)
  | bitOr => exact False.elim (h.2.2.2.2.2.2.2.1 rfl)
  | bitXor => exact False.elim (h.2.2.2.2.2.2.2.2 rfl)
  | add | addUnchecked | addWithOverflow | sub | subUnchecked | subWithOverflow
  | mul | mulUnchecked | mulWithOverflow | div | rem | shl | shlUnchecked
  | shr | shrUnchecked | cmp | offset => rfl

private theorem char_toNat_inj {l r : Char} (h : l.toNat = r.toNat) :
    l = r := by
  cases l with
  | mk lv lh =>
    cases r with
    | mk rv rh =>
      cases lv with
      | ofBitVec lbv =>
        cases rv with
        | ofBitVec rbv =>
          have hBv : lbv = rbv := Anneal.BitVec.eq_of_toNat_eq h
          subst hBv
          rfl

/-- `evalBinOp .eq` on `.char` decides `l = r`. -/
theorem evalBinOp_char_eq_eq (l r : Char) :
    evalBinOp .eq (.char l) (.char r) = .ok (.bool (decide (l = r))) := by
  unfold evalBinOp
  dsimp only
  cases Nat.decEq l.toNat r.toNat with
  | isTrue hEq =>
    have hCEq : l = r := char_toNat_inj hEq
    subst hCEq
    rw [beq_self_eq_true, decide_eq_true rfl]
  | isFalse hNe =>
    have hCNe : l ≠ r := fun h => hNe (congrArg Char.toNat h)
    have hIntNe : Int.ofNat l.toNat ≠ Int.ofNat r.toNat :=
      fun h => hNe (Int.ofNat.inj h)
    have hb : (Int.ofNat l.toNat == Int.ofNat r.toNat) = false := by
      cases hc : Int.ofNat l.toNat == Int.ofNat r.toNat with
      | false => rfl
      | true => exact False.elim (hIntNe (of_decide_eq_true hc))
    rw [hb, decide_eq_false hCNe]

/-- `evalBinOp .ne` on `.char` decides `l ≠ r`. -/
theorem evalBinOp_char_ne_eq (l r : Char) :
    evalBinOp .ne (.char l) (.char r) = .ok (.bool (decide (l ≠ r))) := by
  unfold evalBinOp
  dsimp only
  cases Nat.decEq l.toNat r.toNat with
  | isTrue hEq =>
    have hCEq : l = r := char_toNat_inj hEq
    subst hCEq
    have hb : (Int.ofNat l.toNat != Int.ofNat l.toNat) = false := by
      change (!(Int.ofNat l.toNat == Int.ofNat l.toNat)) = false
      rw [beq_self_eq_true]
      rfl
    rw [hb, decide_eq_false (fun h => h rfl)]
  | isFalse hNe =>
    have hCNe : l ≠ r := fun h => hNe (congrArg Char.toNat h)
    have hIntNe : Int.ofNat l.toNat ≠ Int.ofNat r.toNat :=
      fun h => hNe (Int.ofNat.inj h)
    have hb : (Int.ofNat l.toNat != Int.ofNat r.toNat) = true :=
      bne_iff_ne.mpr hIntNe
    rw [hb, decide_eq_true hCNe]

/-- `evalBinOp .lt` on `.char` decides `l.toNat < r.toNat`. -/
theorem evalBinOp_char_lt_eq (l r : Char) :
    evalBinOp .lt (.char l) (.char r) =
      .ok (.bool (decide (l.toNat < r.toNat))) := by
  unfold evalBinOp
  dsimp only
  cases Nat.lt_or_ge l.toNat r.toNat with
  | inl h =>
    rw [decide_eq_true h, decide_eq_true (int_ofNat_lt_iff.mpr h)]
  | inr h =>
    rw [decide_eq_false (Nat.not_lt_of_ge h),
      decide_eq_false (fun hlt => Nat.not_lt_of_ge h (int_ofNat_lt_iff.mp hlt))]

/-- `evalBinOp .le` on `.char` decides `l.toNat ≤ r.toNat`. -/
theorem evalBinOp_char_le_eq (l r : Char) :
    evalBinOp .le (.char l) (.char r) =
      .ok (.bool (decide (l.toNat ≤ r.toNat))) := by
  unfold evalBinOp
  dsimp only
  cases Nat.lt_or_ge r.toNat l.toNat with
  | inl h =>
    have hN : ¬ (l.toNat ≤ r.toNat) := Nat.not_le_of_gt h
    rw [decide_eq_false hN,
      decide_eq_false (fun hle => hN (int_ofNat_le_iff.mp hle))]
  | inr h =>
    rw [decide_eq_true h, decide_eq_true (int_ofNat_le_iff.mpr h)]

/-- `evalBinOp .gt` on `.char` decides `r.toNat < l.toNat`. -/
theorem evalBinOp_char_gt_eq (l r : Char) :
    evalBinOp .gt (.char l) (.char r) =
      .ok (.bool (decide (r.toNat < l.toNat))) := by
  unfold evalBinOp
  dsimp only
  cases Nat.lt_or_ge r.toNat l.toNat with
  | inl h =>
    have hGt : Int.ofNat l.toNat > Int.ofNat r.toNat := int_ofNat_lt_iff.mpr h
    rw [decide_eq_true h, decide_eq_true hGt]
  | inr h =>
    have hNot : ¬ (Int.ofNat l.toNat > Int.ofNat r.toNat) :=
      fun hGt => Nat.not_lt_of_ge h (int_ofNat_lt_iff.mp hGt)
    rw [decide_eq_false (Nat.not_lt_of_ge h), decide_eq_false hNot]

/-- `evalBinOp .ge` on `.char` decides `r.toNat ≤ l.toNat`. -/
theorem evalBinOp_char_ge_eq (l r : Char) :
    evalBinOp .ge (.char l) (.char r) =
      .ok (.bool (decide (r.toNat ≤ l.toNat))) := by
  unfold evalBinOp
  dsimp only
  cases Nat.lt_or_ge l.toNat r.toNat with
  | inl h =>
    have hN : ¬ (r.toNat ≤ l.toNat) := Nat.not_le_of_gt h
    have hNot : ¬ (Int.ofNat l.toNat ≥ Int.ofNat r.toNat) :=
      fun hGe => hN (int_ofNat_le_iff.mp hGe)
    rw [decide_eq_false hN, decide_eq_false hNot]
  | inr h =>
    have hGe : Int.ofNat l.toNat ≥ Int.ofNat r.toNat := int_ofNat_le_iff.mpr h
    rw [decide_eq_true h, decide_eq_true hGe]

/-- `evalBinOp .cmp` on `.char` computes `cmpOrderingOfNat l.toNat r.toNat`. -/
theorem evalBinOp_char_cmp_eq (l r : Char) :
    evalBinOp .cmp (.char l) (.char r) =
      .ok (.ordering (cmpOrderingOfNat l.toNat r.toNat)) := by
  unfold evalBinOp cmpOrderingOfInt cmpOrderingOfNat
  dsimp only
  cases Nat.lt_or_ge l.toNat r.toNat with
  | inl hLt =>
    rw [decide_eq_true (int_ofNat_lt_iff.mpr hLt), decide_eq_true hLt]
    rfl
  | inr hGe =>
    have hNotLt : ¬ (Int.ofNat l.toNat < Int.ofNat r.toNat) :=
      fun h => Nat.not_lt_of_ge hGe (int_ofNat_lt_iff.mp h)
    rw [decide_eq_false hNotLt, decide_eq_false (Nat.not_lt_of_ge hGe)]
    cases Nat.eq_or_lt_of_le hGe with
    | inl hEq =>
      rw [decide_eq_true (congrArg Int.ofNat hEq.symm), decide_eq_true hEq.symm]
    | inr hGt =>
      have hNeNat : l.toNat ≠ r.toNat := Nat.ne_of_gt hGt
      have hNeInt : Int.ofNat l.toNat ≠ Int.ofNat r.toNat :=
        fun h => hNeNat (Int.ofNat.inj h)
      rw [decide_eq_false hNeInt, decide_eq_false hNeNat]

/-- All arithmetic, bitwise, shift, and `.offset` operators on `.char` fail
closed with `.error .unsupported`. -/
theorem evalBinOp_char_unsupported {op : BinOp}
    (h : op ≠ .eq ∧ op ≠ .ne ∧ op ≠ .lt ∧ op ≠ .le ∧ op ≠ .gt ∧ op ≠ .ge ∧
      op ≠ .cmp)
    (l r : Char) :
    evalBinOp op (.char l) (.char r) = .error .unsupported := by
  cases op with
  | eq => exact False.elim (h.1 rfl)
  | ne => exact False.elim (h.2.1 rfl)
  | lt => exact False.elim (h.2.2.1 rfl)
  | le => exact False.elim (h.2.2.2.1 rfl)
  | gt => exact False.elim (h.2.2.2.2.1 rfl)
  | ge => exact False.elim (h.2.2.2.2.2.1 rfl)
  | cmp => exact False.elim (h.2.2.2.2.2.2 rfl)
  | add | addUnchecked | addWithOverflow | sub | subUnchecked | subWithOverflow
  | mul | mulUnchecked | mulWithOverflow | div | rem | bitXor | bitAnd | bitOr
  | shl | shlUnchecked | shr | shrUnchecked | offset => rfl


/-! ## 4. `evalUnOp`, Negation Range/Tnum Transfers, & `evalIntToIntCast` -/

/-- `evalUnOp .not` on `.bool` computes `!b`. -/
theorem evalUnOp_not_bool_eq (b : Bool) :
    evalUnOp .not (.bool b) = .ok (.bool (!b)) := rfl

/-- `evalUnOp .neg` on `.bool` fails closed with `.error .unsupported`. -/
theorem evalUnOp_neg_bool_unsupported (b : Bool) :
    evalUnOp .neg (.bool b) = .error .unsupported := rfl

/-- Every `UnOp` on `.char` fails closed with `.error .unsupported`. -/
theorem evalUnOp_char_unsupported (op : UnOp) (c : Char) :
    evalUnOp op (.char c) = .error .unsupported := by
  cases op <;> rfl

/-- `UnOp.ptrMetadata` fails closed with `.error .unsupported` on every value.
-/
theorem evalUnOp_ptrMetadata_unsupported (v : Val) :
    evalUnOp .ptrMetadata v = .error .unsupported := by
  cases v <;> rfl

private theorem bvOfInt_neg_bvToInt {W : Nat} (hW : 0 < W) (x : BitVec W) :
    bvOfInt W (Neg.neg (bvToInt x)) = Anneal.BitVecArith.neg x := by
  apply Anneal.BitVec.eq_of_toNat_eq
  cases hx0 : x.toNat with
  | zero =>
    have hxZero : x = BitVec.ofNat W 0 :=
      Anneal.BitVec.eq_of_toNat_eq (hx0.trans (Anneal.BitVec.toNat_zero W).symm)
    subst hxZero
    have hm : Anneal.BitVecArith.msb (BitVec.ofNat W 0) = false := by
      rw [Anneal.BitVecArith.msb_eq_false_iff hW, Anneal.BitVec.toNat_zero]
      exact nat_two_pow_pos _
    rw [bvToInt_pos_eq_ofNat hW hm, Anneal.BitVec.toNat_zero,
      Anneal.BitVecArith.neg_zero]
    rfl
  | succ k =>
    have hxPos : 0 < x.toNat := by rw [hx0]; exact Nat.zero_lt_succ k
    rw [Anneal.BitVecArith.toNat_neg_of_pos hxPos]
    cases hm : Anneal.BitVecArith.msb x with
    | false =>
      rw [bvToInt_pos_eq_ofNat hW hm, hx0]
      change (bvOfInt W (Int.negSucc k)).toNat = Nat.pow 2 W - Nat.succ k
      rw [toNat_bvOfInt_negSucc]
      have hkLt : k < Nat.pow 2 W := by
        have hSuccLt : Nat.succ k < Nat.pow 2 W := by
          change k + 1 < Nat.pow 2 W
          rw [← hx0]
          exact bitVec_toNat_lt_pow x
        exact Nat.lt_trans (Nat.lt_succ_self k) hSuccLt
      rw [nat_mod_eq_of_lt hkLt]
    | true =>
      rw [bvToInt_neg_eq_negSucc hW hm]
      have hNeg : Neg.neg (Int.negSucc (Nat.pow 2 W - 1 - x.toNat)) =
          Int.ofNat (Nat.pow 2 W - x.toNat) := by
        have hSucc : Nat.succ (Nat.pow 2 W - 1 - x.toNat) =
            Nat.pow 2 W - x.toNat := by
          have hC := Nat.sub_add_cancel
            (Nat.zero_lt_sub_of_lt (bitVec_toNat_lt_pow x))
          rw [Nat.sub_sub, Nat.add_comm x.toNat 1, ← Nat.sub_sub] at hC
          exact hC
        change Int.ofNat (Nat.succ (Nat.pow 2 W - 1 - x.toNat)) = _
        rw [hSucc]
      rw [hNeg, toNat_bvOfInt_ofNat]
      have hSubLt : Nat.pow 2 W - x.toNat < Nat.pow 2 W :=
        Nat.sub_lt (nat_two_pow_pos W) hxPos
      rw [nat_mod_eq_of_lt hSubLt]

private theorem signedKey_signBit_eq_zero {W : Nat} (hW : 0 < W) :
    Anneal.BitVecArith.signedKey (Anneal.BitVecArith.signBit (w := W)) = 0 := by
  have hm : Anneal.BitVecArith.msb (Anneal.BitVecArith.signBit (w := W)) =
      true := by
    rw [Anneal.BitVecArith.msb_eq_true_iff hW,
      Anneal.BitVecArith.toNat_signBit_of_pos hW]
    exact Nat.le_refl _
  rw [Anneal.BitVecArith.signedKey_eq_of_msb_true hW hm,
    Anneal.BitVecArith.toNat_signBit_of_pos hW, Nat.sub_self]

/-- Signed negation reflects `signedKey` across `2^w` for every non-`INT_MIN`
bitvector (`0 < signedKey x`): `signedKey (neg x) = 2^w - signedKey x`. -/
theorem signedKey_neg_of_pos {w : Nat} (hw : 0 < w) {x : BitVec w}
    (hPos : 0 < Anneal.BitVecArith.signedKey x) :
    Anneal.BitVecArith.signedKey (Anneal.BitVecArith.neg x) =
      Nat.pow 2 w - Anneal.BitVecArith.signedKey x := by
  let H := Nat.pow 2 (w - 1)
  have hPow : Nat.pow 2 w = H + H := nat_two_pow_split hw
  have hBx := intBalance_bvToInt hw x
  have hBNeg := intBalance_neg_of hBx
  have hNegPos := Anneal.InitLemmas.intBalance_ofNat H
  have hNegBound := intBalance_neg_of hNegPos
  have hKlt := Anneal.BitVecArith.signedKey_lt x
  rw [hPow] at hKlt
  have hLo : Neg.neg (Int.ofNat H) ≤ Neg.neg (bvToInt x) := by
    rw [intBalance_le_iff hNegBound hBNeg, Nat.zero_add]
    exact Nat.le_of_lt hKlt
  have hHi : Neg.neg (bvToInt x) < Int.ofNat H := by
    rw [intBalance_lt_iff hBNeg hNegPos, Nat.add_zero]
    exact Nat.add_lt_add_left hPos H
  have hBvToIntNeg : bvToInt (Anneal.BitVecArith.neg x) = Neg.neg (bvToInt x) := by
    rw [← bvOfInt_neg_bvToInt hw x]
    exact bvToInt_bvOfInt_eq_of_in_range hw hLo hHi
  have hEqBal :
      Anneal.BitVecArith.signedKey (Anneal.BitVecArith.neg x) +
        Anneal.BitVecArith.signedKey x = H + H := by
    have hB1 := intBalance_bvToInt hw (Anneal.BitVecArith.neg x)
    rw [hBvToIntNeg] at hB1
    exact intBalance_eq_of hB1 hBNeg
  rw [← hPow] at hEqBal
  have hD := congrArg (fun z => z - Anneal.BitVecArith.signedKey x) hEqBal
  rw [Nat.add_sub_cancel] at hD
  exact hD

/-- Soundness of signed interval transfer for `evalUnOp .neg`: when `lo >ₛ
INT_MIN` and `lo ≤ₛ x ≤ₛ hi`, `evalUnOp .neg` produces `-x` bounded in
`[-hi, -lo]`. -/
theorem evalUnOp_neg_srange_sound (w : IntWidth)
    {lo x hi : BitVec (8 * w.byteSize)}
    (hNoMin : Anneal.BitVecArith.slt
      (Anneal.BitVecArith.signBit (w := 8 * w.byteSize)) lo)
    (hLo : Anneal.BitVecArith.sle lo x)
    (hHi : Anneal.BitVecArith.sle x hi) :
    evalUnOp .neg (.scalar (bvToScalar w true x)) =
        .ok (.scalar (bvToScalar w true (Anneal.BitVecArith.neg x))) ∧
      Anneal.BitVecArith.sle
        (Anneal.BitVecArith.neg hi) (Anneal.BitVecArith.neg x) ∧
      Anneal.BitVecArith.sle
        (Anneal.BitVecArith.neg x) (Anneal.BitVecArith.neg lo) := by
  have hW : 0 < 8 * w.byteSize := by
    rw [← intWidth_bitWidth_eq_eight_mul]
    exact intWidth_bitWidth_pos w
  have hLoPos : 0 < Anneal.BitVecArith.signedKey lo := by
    change Anneal.BitVecArith.signedKey
      (Anneal.BitVecArith.signBit (w := 8 * w.byteSize)) <
      Anneal.BitVecArith.signedKey lo at hNoMin
    rw [signedKey_signBit_eq_zero hW] at hNoMin
    exact hNoMin
  have hXPos : 0 < Anneal.BitVecArith.signedKey x :=
    Nat.lt_of_lt_of_le hLoPos hLo
  have hHiPos : 0 < Anneal.BitVecArith.signedKey hi :=
    Nat.lt_of_lt_of_le hXPos hHi
  refine ⟨evalUnOp_neg_signed_eq_neg w x, ?_, ?_⟩
  · change Anneal.BitVecArith.signedKey (Anneal.BitVecArith.neg hi) ≤
      Anneal.BitVecArith.signedKey (Anneal.BitVecArith.neg x)
    rw [signedKey_neg_of_pos hW hHiPos, signedKey_neg_of_pos hW hXPos]
    exact Nat.sub_le_sub_left hHi _
  · change Anneal.BitVecArith.signedKey (Anneal.BitVecArith.neg x) ≤
      Anneal.BitVecArith.signedKey (Anneal.BitVecArith.neg lo)
    rw [signedKey_neg_of_pos hW hXPos, signedKey_neg_of_pos hW hLoPos]
    exact Nat.sub_le_sub_left hLo _

/-- Tnum unknown-mask transfer for two's-complement negation `-x = ~~~x + 1`.
-/
@[expose] def tnumNegMask {w : Nat} (m v : BitVec w) : BitVec w :=
  let u := Anneal.BitVec.and (Anneal.BitVec.not v) (Anneal.BitVec.not m)
  let sv := u + BitVec.ofNat w 1
  let sigma := m + sv
  let chi := Anneal.BitVec.xor sigma sv
  Anneal.BitVec.or chi m

/-- Tnum canonical known-value transfer for two's-complement negation. -/
@[expose] def tnumNegVal {w : Nat} (m v : BitVec w) : BitVec w :=
  let u := Anneal.BitVec.and (Anneal.BitVec.not v) (Anneal.BitVec.not m)
  let sv := u + BitVec.ofNat w 1
  Anneal.BitVec.and sv (Anneal.BitVec.not (tnumNegMask m v))

/-- Soundness of `tnumNegMask`/`tnumNegVal` for bitvector negation
`Anneal.BitVecArith.neg x`. -/
theorem tnum_neg_sound {w : Nat} {m x v : BitVec w}
    (h : Anneal.BitVec.MaskEq m x v) :
    Anneal.BitVec.MaskEq (tnumNegMask m v) (Anneal.BitVecArith.neg x)
      (tnumNegVal m v) := by
  have hNot : Anneal.BitVec.MaskEq m (Anneal.BitVec.not x)
      (Anneal.BitVec.not v) :=
    Anneal.BitVec.tnum_not_sound h
  let u := Anneal.BitVec.and (Anneal.BitVec.not v) (Anneal.BitVec.not m)
  have hNotCanon : Anneal.BitVec.MaskEq m (Anneal.BitVec.not x) u :=
    Anneal.BitVec.maskEq_canonical.1 hNot
  have hc1 : Anneal.BitVec.and u m = BitVec.ofNat w 0 := by
    dsimp only [u]
    rw [Anneal.BitVec.and_assoc,
      Anneal.BitVec.and_comm (Anneal.BitVec.not m) m,
      Anneal.BitVec.and_not_self, Anneal.BitVec.and_zero]
  have hZero : Anneal.BitVec.MaskEq (BitVec.ofNat w 0)
      (BitVec.ofNat w 1) (BitVec.ofNat w 1) :=
    Anneal.BitVec.maskEq_refl _ _
  have hc2 : Anneal.BitVec.and (BitVec.ofNat w 1) (BitVec.ofNat w 0) =
      BitVec.ofNat w 0 :=
    Anneal.BitVec.and_zero _
  have hAdd := Anneal.BitVecArith.tnum_add_sound hNotCanon hZero hc1 hc2
  have hMAddZero : m + BitVec.ofNat w 0 = m := by
    apply Anneal.BitVec.eq_of_toNat_eq
    rw [Anneal.BitVec.toNat_add, Anneal.BitVec.toNat_zero, Nat.add_zero]
    exact nat_mod_eq_of_lt (bitVec_toNat_lt_pow m)
  have hMOrZero : Anneal.BitVec.or m (BitVec.ofNat w 0) = m :=
    Anneal.BitVec.or_zero m
  rw [hMAddZero, hMOrZero, ← Anneal.BitVecArith.neg_eq_not_add_one] at hAdd
  exact hAdd

/-- Operational tnum soundness lift for signed `evalUnOp .neg`. -/
theorem evalUnOp_neg_tnum_sound {w : IntWidth}
    {m x v : BitVec (8 * w.byteSize)}
    (h : Anneal.BitVec.MaskEq m x v) :
    ∃ r : BitVec (8 * w.byteSize),
      evalUnOp .neg (.scalar (bvToScalar w true x)) =
        .ok (.scalar (bvToScalar w true r)) ∧
      Anneal.BitVec.MaskEq (tnumNegMask m v) r (tnumNegVal m v) :=
  ⟨Anneal.BitVecArith.neg x, evalUnOp_neg_signed_eq_neg w x, tnum_neg_sound h⟩

/-- `evalIntToIntCast` from `.bool` to `.int w s` yields `0` or `1` in
`bvToScalar w s`. -/
theorem evalIntToIntCast_bool_to_int (b : Bool) (w : IntWidth) (s : Bool) :
    evalIntToIntCast (.bool b) (.int w s) =
      .ok (.scalar (bvToScalar w s
        (if b then BitVec.ofNat (8 * w.byteSize) 1
        else BitVec.ofNat (8 * w.byteSize) 0))) := by
  have hW : 8 ≤ 8 * w.byteSize := intWidth_eight_le w
  have hOneLt : 1 < Nat.pow 2 (8 * w.byteSize) :=
    Nat.lt_of_lt_of_le (by decide : 1 < Nat.pow 2 8)
      (Nat.pow_le_pow_right (by decide : 0 < 2) hW)
  cases b with
  | false =>
    unfold evalIntToIntCast intLikeBits bvToScalar
    dsimp only
    have hBits : truncateBits w (BitVec.ofNat 128 0) =
        bvZeroExtend 128 (BitVec.ofNat (8 * w.byteSize) 0) := by
      apply Anneal.BitVec.eq_of_toNat_eq
      rw [toNat_truncateBits_eq_mod, Anneal.BitVec.toNat_ofNat,
        toNat_bvZeroExtend_of_le (intWidth_bitWidth_le_128_eight w),
        Anneal.BitVec.toNat_zero, nat_zero_mod]
    change Except.ok (Val.scalar ⟨w, s, truncateBits w (BitVec.ofNat 128 0)⟩) =
      Except.ok (Val.scalar ⟨w, s,
        bvZeroExtend 128 (BitVec.ofNat (8 * w.byteSize) 0)⟩)
    rw [hBits]
  | true =>
    unfold evalIntToIntCast intLikeBits bvToScalar
    dsimp only
    have hBits : truncateBits w (BitVec.ofNat 128 1) =
        bvZeroExtend 128 (BitVec.ofNat (8 * w.byteSize) 1) := by
      apply Anneal.BitVec.eq_of_toNat_eq
      rw [toNat_truncateBits_eq_mod,
        Anneal.BitVec.toNat_ofNat,
        nat_mod_eq_of_lt (by decide : 1 < Nat.pow 2 128),
        nat_mod_eq_of_lt hOneLt,
        toNat_bvZeroExtend_of_le (intWidth_bitWidth_le_128_eight w),
        Anneal.BitVec.toNat_ofNat, nat_mod_eq_of_lt hOneLt]
    change Except.ok (Val.scalar ⟨w, s, truncateBits w (BitVec.ofNat 128 1)⟩) =
      Except.ok (Val.scalar ⟨w, s,
        bvZeroExtend 128 (BitVec.ofNat (8 * w.byteSize) 1)⟩)
    rw [hBits]

/-- `evalIntToIntCast` from `.char` to `.int w s` truncates/zero-extends
`c.toNat` into `bvToScalar w s`. -/
theorem evalIntToIntCast_char_to_int (c : Char) (w : IntWidth) (s : Bool) :
    evalIntToIntCast (.char c) (.int w s) =
      .ok (.scalar (bvToScalar w s
        (BitVec.ofNat (8 * w.byteSize) c.toNat))) := by
  unfold evalIntToIntCast intLikeBits bvToScalar
  dsimp only
  have hc32 : c.toNat < Nat.pow 2 32 :=
    bitVec_toNat_lt_pow c.val.toBitVec
  have hc128 : c.toNat < Nat.pow 2 128 :=
    Nat.lt_trans hc32 (by decide : Nat.pow 2 32 < Nat.pow 2 128)
  have hBits : truncateBits w (BitVec.ofNat 128 c.toNat) =
      bvZeroExtend 128 (BitVec.ofNat (8 * w.byteSize) c.toNat) := by
    apply Anneal.BitVec.eq_of_toNat_eq
    rw [toNat_truncateBits_eq_mod,
      Anneal.BitVec.toNat_ofNat, nat_mod_eq_of_lt hc128,
      toNat_bvZeroExtend_of_le (intWidth_bitWidth_le_128_eight w),
      Anneal.BitVec.toNat_ofNat]
  change Except.ok (Val.scalar ⟨w, s,
      truncateBits w (BitVec.ofNat 128 c.toNat)⟩) =
    Except.ok (Val.scalar ⟨w, s,
      bvZeroExtend 128 (BitVec.ofNat (8 * w.byteSize) c.toNat)⟩)
  rw [hBits]

private theorem nat_ble_255_eq_decide (n : Nat) :
    Nat.ble n 255 = decide (n ≤ 255) := by
  have hEq : (Nat.ble n 255 = true) = (n ≤ 255) := Nat.ble_eq
  cases hb : Nat.ble n 255 with
  | true =>
    have hLe : n ≤ 255 := Eq.mp hEq hb
    rw [decide_eq_true hLe]
  | false =>
    have hN : ¬ (n ≤ 255) := fun h => by
      have ht : Nat.ble n 255 = true := Eq.mpr hEq h
      rw [ht] at hb
      cases hb
    rw [decide_eq_false hN]

/-- `evalIntToIntCast` from an unsigned scalar to `.char` succeeds iff
`x.toNat ≤ 255` and fails closed with `.error .unsupported` above `255`. -/
theorem evalIntToIntCast_unsigned_to_char (w : IntWidth)
    (x : BitVec (8 * w.byteSize)) :
    evalIntToIntCast (.scalar (bvToScalar w false x)) .char =
      if decide (x.toNat ≤ 255) then
        .ok (.char (Char.ofNat x.toNat))
      else
        .error .unsupported := by
  unfold evalIntToIntCast intLikeBits bvToScalar
  dsimp only
  rw [if_false_eq, truncateBits_bvZeroExtend,
    toNat_bvZeroExtend_of_le (intWidth_bitWidth_le_128_eight w) x]
  dsimp only
  rw [nat_ble_255_eq_decide]

/-- `evalIntToIntCast` from a non-negative signed scalar (`msb x = false`) to
`.char` succeeds iff `x.toNat ≤ 255` and fails with `.error .unsupported`
above `255`. -/
theorem evalIntToIntCast_signed_nonneg_to_char (w : IntWidth)
    {x : BitVec (8 * w.byteSize)} (hm : Anneal.BitVecArith.msb x = false) :
    evalIntToIntCast (.scalar (bvToScalar w true x)) .char =
      if decide (x.toNat ≤ 255) then
        .ok (.char (Char.ofNat x.toNat))
      else
        .error .unsupported := by
  unfold evalIntToIntCast intLikeBits
  dsimp only
  rw [bvToScalar_width, bvToScalar_signed, if_true_eq,
    decodeScalar_signed_of_msb_false hm]
  have hx128 : x.toNat < Nat.pow 2 128 :=
    Nat.lt_of_lt_of_le (bitVec_toNat_lt_pow x)
      (Nat.pow_le_pow_right (by decide : 0 < 2)
        (intWidth_bitWidth_le_128_eight w))
  have hBits : (bvOfInt 128 (Int.ofNat x.toNat)).toNat = x.toNat := by
    rw [toNat_bvOfInt_ofNat, nat_mod_eq_of_lt hx128]
  rw [hBits]
  dsimp only
  rw [nat_ble_255_eq_decide]

/-- `evalIntToIntCast` from any negative signed scalar (`msb x = true`) to
`.char` always fails closed with `.error .unsupported`. -/
theorem evalIntToIntCast_signed_neg_to_char_unsupported (w : IntWidth)
    {x : BitVec (8 * w.byteSize)} (hm : Anneal.BitVecArith.msb x = true) :
    evalIntToIntCast (.scalar (bvToScalar w true x)) .char =
      .error .unsupported := by
  have hW : 0 < 8 * w.byteSize := by
    rw [← intWidth_bitWidth_eq_eight_mul]
    exact intWidth_bitWidth_pos w
  have hWle : 8 * w.byteSize ≤ 128 := intWidth_bitWidth_le_128_eight w
  have hGeHalf := (Anneal.BitVecArith.msb_eq_true_iff hW x).mp hm
  let W := 8 * w.byteSize
  let d := Nat.pow 2 W - 1 - x.toNat
  have hdLtHalf : d < Nat.pow 2 (W - 1) := by
    have hPow : Nat.pow 2 W = Nat.pow 2 (W - 1) + Nat.pow 2 (W - 1) :=
      nat_two_pow_split hW
    dsimp only [d]
    apply nat_lt_of_add_lt_add_right (c := Nat.pow 2 (W - 1))
    have hSub : Nat.pow 2 W - 1 - x.toNat + Nat.pow 2 (W - 1) ≤
        Nat.pow 2 W - 1 := by
      have h1 := Nat.add_le_add_left hGeHalf (Nat.pow 2 W - 1 - x.toNat)
      rw [Nat.sub_add_cancel (Nat.le_sub_one_of_lt
        (bitVec_toNat_lt_pow x))] at h1
      exact h1
    have hLtPow : Nat.pow 2 W - 1 < Nat.pow 2 (W - 1) + Nat.pow 2 (W - 1) := by
      rw [← hPow]
      exact Nat.sub_lt (nat_two_pow_pos W) Nat.one_pos
    exact Nat.lt_of_le_of_lt hSub hLtPow
  have hHalf127 : Nat.pow 2 (W - 1) ≤ Nat.pow 2 127 :=
    Nat.pow_le_pow_right (by decide : 0 < 2) (Nat.sub_le_sub_right hWle 1)
  have hdLt127 : d < Nat.pow 2 127 := Nat.lt_of_lt_of_le hdLtHalf hHalf127
  have hdLt128 : d < Nat.pow 2 128 :=
    Nat.lt_trans hdLt127 (by decide : Nat.pow 2 127 < Nat.pow 2 128)
  have hToNat : (bvOfInt 128 (Int.negSucc d)).toNat = Nat.pow 2 128 - (d + 1) := by
    rw [toNat_bvOfInt_negSucc, nat_mod_eq_of_lt hdLt128]
  have h255Lt : 255 < Nat.pow 2 128 - (d + 1) := by
    have hPow128 : Nat.pow 2 128 = Nat.pow 2 127 + Nat.pow 2 127 := by decide
    have hGe127 : Nat.pow 2 127 ≤ Nat.pow 2 128 - (d + 1) := by
      apply nat_le_of_add_le_add_right (c := d + 1)
      rw [Nat.sub_add_cancel hdLt128, hPow128]
      exact Nat.add_le_add_left hdLt127 _
    exact Nat.lt_of_lt_of_le (by decide : 255 < Nat.pow 2 127) hGe127
  unfold evalIntToIntCast intLikeBits
  dsimp only
  rw [bvToScalar_width, bvToScalar_signed, if_true_eq,
    decodeScalar_signed_of_msb_true hm]
  change (if Nat.ble (bvOfInt 128 (Int.negSucc d)).toNat 255 then
      Except.ok (Val.char (Char.ofNat (bvOfInt 128 (Int.negSucc d)).toNat))
    else Except.error FaultKind.unsupported) = _
  rw [hToNat, nat_ble_255_eq_decide, decide_eq_false (Nat.not_le_of_gt h255Lt),
    if_false_eq]

/-- `evalIntToIntCast` from `.bool` to `.char` produces `Char.ofNat 1` or
`Char.ofNat 0`. -/
theorem evalIntToIntCast_bool_to_char (b : Bool) :
    evalIntToIntCast (.bool b) .char =
      .ok (.char (Char.ofNat (if b then 1 else 0))) := by
  cases b <;> rfl

/-- `evalIntToIntCast` from `.char c` to `.char` succeeds with `c` iff
`c.toNat ≤ 255` and fails closed with `.error .unsupported` above `255`. -/
theorem evalIntToIntCast_char_to_char (c : Char) :
    evalIntToIntCast (.char c) .char =
      if decide (c.toNat ≤ 255) then
        .ok (.char c)
      else
        .error .unsupported := by
  unfold evalIntToIntCast intLikeBits
  dsimp only
  rw [nat_ble_255_eq_decide]
  cases hc : decide (c.toNat ≤ 255) with
  | false => rfl
  | true =>
    have hCeq : Char.ofNat c.toNat = c := by
      apply char_toNat_inj
      unfold Char.ofNat
      have hValid : Nat.isValidChar c.toNat := c.valid
      rw [Anneal.InitLemmas.dite_true_of hValid]
      rfl
    change Except.ok (Val.char (Char.ofNat c.toNat)) = Except.ok (Val.char c)
    rw [hCeq]

/-- `evalIntToIntCast` rejects any value outside scalar/bool/char
(`intLikeBits v = none`) with `.error .unsupported`. -/
theorem evalIntToIntCast_unsupported_source {v : Val}
    (hNone : intLikeBits v = none) (castTy : MirTy) :
    evalIntToIntCast v castTy = .error .unsupported := by
  unfold evalIntToIntCast
  rw [hNone]

/-- `evalIntToIntCast` rejects any target type other than `.int _ _` and
`.char` with `.error .unsupported`. -/
theorem evalIntToIntCast_unsupported_target (v : Val) {castTy : MirTy}
    (hNotInt : ∀ w s, castTy ≠ .int w s) (hNotChar : castTy ≠ .char) :
    evalIntToIntCast v castTy = .error .unsupported := by
  unfold evalIntToIntCast
  cases intLikeBits v with
  | none => rfl
  | some _ =>
    cases castTy with
    | int w s => exact False.elim (hNotInt w s rfl)
    | char => exact False.elim (hNotChar rfl)
    | bool | unit | never | ordering | enum _ | ref _ _ | rawPtr _ _
    | slice _ | array _ _ | rangeTo _ | rangeFrom _ | range _ | option _
    | tuple _ | unsupported => rfl

end Anneal.Core

end
