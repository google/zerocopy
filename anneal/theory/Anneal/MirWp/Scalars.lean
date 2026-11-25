-- Copyright 2026 The Fuchsia Authors
--
-- Licensed under a BSD-style license <LICENSE-BSD>, Apache License, Version 2.0
-- <LICENSE-APACHE or https://www.apache.org/licenses/LICENSE-2.0>, or the MIT
-- license <LICENSE-MIT or https://opensource.org/licenses/MIT>, at your option.
-- This file may not be copied, modified, or distributed except according to
-- those terms.

module
prelude
public import Init.NotationExtra
public import Init.Data.BitVec.BasicAux
public import Init.Data.Int.Basic
public import Init.Data.Nat.Div.Basic
public import Init.Data.Nat.Bitwise.Basic
public import Init.Control.Except
public import Trusted
public import Trusted.MirAst
public import Trusted.MirSemantics
public import Anneal.NatBitwise
public import Anneal.MirWp.Core

public section

namespace Anneal.MirWp

open Trusted.MirAst Trusted.MirSemantics

/-! ## Width-Parametric `IntWidth`, `BitVec`, and `truncateScalar` Adequacy -/

/-- Extensionality of `BitVec n` via `.toNat`. -/
theorem bitVec_eq_of_toNat_eq {n : Nat} {a b : BitVec n}
    (h : a.toNat = b.toNat) : a = b := by
  cases a with
  | ofFin fa =>
    cases b with
    | ofFin fb =>
      exact congrArg BitVec.ofFin (Fin.eq_of_val_eq h)

/-- Unsigned modulus $2^{\text{bitWidth}}$ for proof-side wrapping and range
lemmas. Defined directly in `theory/` rather than `Trusted.MirAst` so the
trusted specification stays free of proof-only arithmetic helpers. -/
@[expose] def intWidthModulus : IntWidth → Nat
  | .i8 => Nat.pow 2 8
  | .i16 => Nat.pow 2 16
  | .i32 => Nat.pow 2 32
  | .i64 | .isize => Nat.pow 2 64
  | .i128 => Nat.pow 2 128

/-- Every `IntWidth` has a strictly positive unsigned modulus $2^{\text{bits}}$.
-/
theorem intWidth_modulus_pos (w : IntWidth) : 0 < intWidthModulus w := by
  cases w <;> decide

/-- Exact arithmetic characterization of `truncateBits` across all six
`IntWidth` variants (`.i8`, `.i16`, `.i32`, `.i64`, `.i128`, `.isize`). -/
theorem toNat_truncateBits (w : IntWidth) (x : BitVec 128) :
    (truncateBits w x).toNat = Nat.mod x.toNat (intWidthModulus w) := by
  cases w
  · exact Nat.mod_eq_of_lt
      (Nat.lt_of_lt_of_le (bvExtractLsb 7 0 x).isLt (by decide))
  · exact Nat.mod_eq_of_lt
      (Nat.lt_of_lt_of_le (bvExtractLsb 15 0 x).isLt (by decide))
  · exact Nat.mod_eq_of_lt
      (Nat.lt_of_lt_of_le (bvExtractLsb 31 0 x).isLt (by decide))
  · exact Nat.mod_eq_of_lt
      (Nat.lt_of_lt_of_le (bvExtractLsb 63 0 x).isLt (by decide))
  · exact Nat.mod_eq_of_lt (bvExtractLsb 127 0 x).isLt
  · exact Nat.mod_eq_of_lt
      (Nat.lt_of_lt_of_le (bvExtractLsb 63 0 x).isLt (by decide))

/-- Width-parametric idempotence of `truncateBits` across all `IntWidth`s. -/
theorem truncateBits_idem (w : IntWidth) (x : BitVec 128) :
    truncateBits w (truncateBits w x) = truncateBits w x := by
  apply bitVec_eq_of_toNat_eq
  rw [toNat_truncateBits, toNat_truncateBits]
  exact Nat.mod_eq_of_lt (Nat.mod_lt x.toNat (intWidth_modulus_pos w))

/-- `.i64` specialization of `truncateBits_idem` for 64-bit scalar proofs. -/
theorem truncateBits_i64_idem (x : BitVec 128) :
    truncateBits .i64 (truncateBits .i64 x) = truncateBits .i64 x :=
  truncateBits_idem .i64 x

/-- Any `BitVec 128` bounded by `intWidthModulus w` is fixed by
`truncateBits w`. -/
theorem truncateBits_of_toNat_lt {w : IntWidth} {x : BitVec 128}
    (h : x.toNat < intWidthModulus w) :
    truncateBits w x = x := by
  apply bitVec_eq_of_toNat_eq
  rw [toNat_truncateBits]
  exact Nat.mod_eq_of_lt h

/-- Every scalar payload produced by `truncateBits w` satisfies `ScalarVal.wf`.
-/
theorem scalarWf_truncateBits (w : IntWidth) (s : Bool) (x : BitVec 128) :
    ScalarVal.wf ⟨w, s, truncateBits w x⟩ = true := by
  unfold ScalarVal.wf
  dsimp only
  rw [truncateBits_idem]
  exact beq_self_eq_true (truncateBits w x)

/-- Simplify a propositional `if-then-else` when the condition holds. -/
theorem ite_prop_true {α : Type} {P : Prop} {inst : Decidable P}
    {t e : α} (h : P) : (@ite α P inst t e) = t := by
  cases inst with
  | isTrue _ => rfl
  | isFalse hn => exact False.elim (hn h)

/-- Simplify a propositional `if-then-else` when the condition is refuted. -/
theorem ite_prop_false {α : Type} {P : Prop} {inst : Decidable P}
    {t e : α} (h : ¬ P) : (@ite α P inst t e) = e := by
  cases inst with
  | isTrue hp => exact False.elim (h hp)
  | isFalse _ => rfl

/-- Simplify a boolean `if-then-else` when the condition is `true`. -/
theorem ite_bool_true {α : Type} {b : Bool} {t e : α}
    (hb : b = true) : (if b then t else e) = t := by
  subst hb
  rfl

/-- Simplify a boolean `if-then-else` when the condition is `false`. -/
theorem ite_bool_false {α : Type} {b : Bool} {t e : α}
    (hb : b = false) : (if b then t else e) = e := by
  subst hb
  rfl

/-- Every 128-bit bitvector decodes via `bvToInt` strictly within the signed
`i128` range `[-2^127, 2^127)`, refuting the `.unsupported` range guard in
`truncateScalar`. -/
theorem bvToInt_in_i128_range (x : BitVec 128) :
    (decide (bvToInt x < Neg.neg (HPow.hPow (2 : Int) 127)) ||
      decide (bvToInt x ≥ HPow.hPow (2 : Int) 127)) = false := by
  unfold bvToInt
  have hPow128 : Nat.pow 2 128 = 2 * Nat.pow 2 127 := by decide
  have hHalf128 : Nat.pow 2 128 = Nat.pow 2 127 + Nat.pow 2 127 := by decide
  have hInt127 : HPow.hPow (2 : Int) 127 = Int.ofNat (Nat.pow 2 127) := by
    decide
  have hNeg127 : Neg.neg (Int.ofNat (Nat.pow 2 127)) =
      Int.negSucc (Nat.pow 2 127 - 1) := by decide
  rw [hInt127, hNeg127]
  cases Nat.lt_or_ge (2 * x.toNat) (Nat.pow 2 128) with
  | inl hCmp =>
    rw [ite_prop_true hCmp]
    have hLt2 : 2 * x.toNat < 2 * Nat.pow 2 127 := by
      rw [← hPow128]
      exact hCmp
    have hLt : x.toNat < Nat.pow 2 127 := by
      cases Nat.lt_or_ge x.toNat (Nat.pow 2 127) with
      | inl h => exact h
      | inr hGe =>
        have hGe2 : 2 * Nat.pow 2 127 ≤ 2 * x.toNat :=
          Nat.mul_le_mul_left 2 hGe
        exact False.elim (Nat.not_le_of_gt hLt2 hGe2)
    have hNotNeg :
        ¬ (Int.ofNat x.toNat < Int.negSucc (Nat.pow 2 127 - 1)) :=
      fun h => nomatch h
    have hNotGe : ¬ (Int.ofNat x.toNat ≥ Int.ofNat (Nat.pow 2 127)) := by
      intro hGeI
      have hPos127 : Nat.pow 2 127 = Nat.succ (Nat.pow 2 127 - 1) := by decide
      rw [hPos127] at hGeI
      change Int.NonNeg
        (Int.subNatNat x.toNat (Nat.succ (Nat.pow 2 127 - 1))) at hGeI
      rw [← hPos127] at hGeI
      unfold Int.subNatNat at hGeI
      cases hSub : Nat.pow 2 127 - x.toNat with
      | zero => exact Nat.not_le_of_gt hLt (Nat.le_of_sub_eq_zero hSub)
      | succ k => rw [hSub] at hGeI; nomatch hGeI
    rw [decide_eq_false hNotNeg, decide_eq_false hNotGe]
    rfl
  | inr hCmp =>
    rw [ite_prop_false (Nat.not_lt_of_ge hCmp)]
    have hGe2 : 2 * Nat.pow 2 127 ≤ 2 * x.toNat := by
      rw [← hPow128]
      exact hCmp
    have hGe : Nat.pow 2 127 ≤ x.toNat := by
      cases Nat.lt_or_ge x.toNat (Nat.pow 2 127) with
      | inr h => exact h
      | inl hLt =>
        have hLt2 : 2 * x.toNat < 2 * Nat.pow 2 127 := by
          have h1 : x.toNat + x.toNat < Nat.pow 2 127 + Nat.pow 2 127 :=
            Nat.add_lt_add hLt hLt
          have hMulL : 2 * x.toNat = x.toNat + x.toNat :=
            Nat.succ_mul 1 x.toNat ▸ congrArg (fun z => z + x.toNat)
              (Nat.one_mul x.toNat)
          have hMulR : 2 * Nat.pow 2 127 =
              Nat.pow 2 127 + Nat.pow 2 127 :=
            Nat.succ_mul 1 (Nat.pow 2 127) ▸
              congrArg (fun z => z + Nat.pow 2 127)
                (Nat.one_mul (Nat.pow 2 127))
          rw [hMulL, hMulR]
          exact h1
        exact False.elim (Nat.not_lt_of_ge hGe2 hLt2)
    have hSubDef :
        Int.ofNat x.toNat - Int.ofNat (Nat.pow 2 128) =
        Int.subNatNat x.toNat (Nat.pow 2 128) := by
      have h1 : Neg.neg (Int.ofNat (Nat.pow 2 128)) =
          Int.negSucc (Nat.pow 2 128 - 1) := by decide
      have h2 : Nat.succ (Nat.pow 2 128 - 1) = Nat.pow 2 128 := by decide
      change Int.add (Int.ofNat x.toNat)
        (Neg.neg (Int.ofNat (Nat.pow 2 128))) = _
      rw [h1]
      change Int.subNatNat x.toNat (Nat.succ (Nat.pow 2 128 - 1)) = _
      rw [h2]
    rw [hSubDef]
    unfold Int.subNatNat
    cases hDiff : Nat.pow 2 128 - x.toNat with
    | zero =>
      exact False.elim (Nat.not_le_of_gt x.isLt (Nat.le_of_sub_eq_zero hDiff))
    | succ k =>
      dsimp only
      have hKLt : k < Nat.pow 2 127 := by
        have hSum : x.toNat + (k + 1) = Nat.pow 2 127 + Nat.pow 2 127 := by
          have hAdd := Nat.add_sub_of_le (Nat.le_of_lt x.isLt)
          have hHalfPow :
              HPow.hPow (2 : Nat) 128 = Nat.pow 2 127 + Nat.pow 2 127 := by
            decide
          change x.toNat + (Nat.pow 2 128 - x.toNat) =
            HPow.hPow (2 : Nat) 128 at hAdd
          rw [hDiff, hHalfPow] at hAdd
          exact hAdd
        have hLeAdd : Nat.pow 2 127 + (k + 1) ≤
            Nat.pow 2 127 + Nat.pow 2 127 := by
          rw [← hSum]
          exact Nat.add_le_add_right hGe (k + 1)
        exact Nat.le_of_add_le_add_left hLeAdd
      have hNotGe : ¬ (Int.negSucc k ≥ Int.ofNat (Nat.pow 2 127)) := by
        intro hGeI
        have hPos127 : Nat.pow 2 127 = Nat.succ (Nat.pow 2 127 - 1) := by
          decide
        rw [hPos127] at hGeI
        nomatch hGeI
      have hNotLt :
          ¬ (Int.negSucc k < Int.negSucc (Nat.pow 2 127 - 1)) := by
        intro hLtI
        cases k with
        | zero =>
          have hZ : Int.negSucc 0 + 1 = Int.ofNat 0 := by decide
          change Int.NonNeg
            (Int.negSucc (Nat.pow 2 127 - 1) - (Int.negSucc 0 + 1)) at hLtI
          rw [hZ] at hLtI
          nomatch hLtI
        | succ k' =>
          have hSucc127 : Nat.succ (Nat.pow 2 127 - 1) = Nat.pow 2 127 := by
            decide
          change Int.NonNeg
            (Int.subNatNat (Nat.succ k')
              (Nat.succ (Nat.pow 2 127 - 1))) at hLtI
          rw [hSucc127] at hLtI
          unfold Int.subNatNat at hLtI
          cases hRem : Nat.pow 2 127 - Nat.succ k' with
          | zero =>
            exact Nat.not_le_of_gt hKLt (Nat.le_of_sub_eq_zero hRem)
          | succ r =>
            rw [hRem] at hLtI
            nomatch hLtI
      rw [decide_eq_false hNotLt, decide_eq_false hNotGe]
      rfl

/-- Totality and `ScalarVal.wf` preservation of `truncateScalar` across all six
`IntWidth` variants, both signedness modes, and all integers `value : Int`. -/
theorem truncateScalar_ok (w : IntWidth) (s : Bool) (value : Int) :
    ∃ (sv : ScalarVal) (lossy : Bool),
      truncateScalar w s value = .ok (sv, lossy) ∧
      sv.width = w ∧ sv.signed = s ∧ sv.wf = true := by
  unfold truncateScalar
  cases s with
  | false =>
    exact ⟨⟨w, false, truncateBits w (bvOfInt 128 value)⟩,
      truncateBits w (bvOfInt 128 value) != bvOfInt 128 value,
      rfl, rfl, rfl, scalarWf_truncateBits w false (bvOfInt 128 value)⟩
  | true =>
    dsimp only
    rw [bvToInt_in_i128_range (bvOfInt 128 value)]
    let wrapped := bvToInt (bvOfInt 128 value)
    let raw := bvOfInt 128 wrapped
    let trunc := truncateBits w raw
    exact ⟨⟨w, true, trunc⟩, signExtendBits w trunc != wrapped,
      rfl, rfl, rfl, scalarWf_truncateBits w true raw⟩

/-! ### 64-Bit Bitvector and Bitwise Arithmetic Normalization -/

private theorem nat_mod_mod_mul_left (n a b : Nat) :
    Nat.mod (Nat.mod n (a * b)) a = Nat.mod n a := by
  have hDiv : Nat.mod n (a * b) + a * (b * Nat.div n (a * b)) = n := by
    rw [← Nat.mul_assoc]
    exact Nat.mod_add_div n (a * b)
  exact (Nat.add_mul_mod_self_left (Nat.mod n (a * b)) a
    (b * Nat.div n (a * b))).symm.trans (congrArg (fun k => Nat.mod k a) hDiv)

/-- Bitwise combination of two `n`-bit naturals stays below `2 ^ n`. -/
theorem nat_bitwise_lt_two_pow (f : Bool → Bool → Bool) :
    ∀ (n a b : Nat), a < Nat.pow 2 n → b < Nat.pow 2 n →
      Nat.bitwise f a b < Nat.pow 2 n :=
  Anneal.NatBitwise.lt_two_pow f

/-- Zero-extending a 64-bit bitvector to 128 bits preserves `.toNat`. -/
theorem bvZeroExtend_128_toNat (w : BitVec 64) :
    (bvZeroExtend 128 w).toNat = w.toNat :=
  Nat.mod_eq_of_lt (Nat.lt_trans w.isLt (by decide))

/-- Truncating `BitVec.ofNat 128 n` to `.i64` agrees with zero-extending
`BitVec.ofNat 64 n`. -/
theorem truncateBits_i64_ofNat (n : Nat) :
    truncateBits .i64 (BitVec.ofNat 128 n) =
      bvZeroExtend 128 (BitVec.ofNat 64 n) := by
  apply bitVec_eq_of_toNat_eq
  rw [toNat_truncateBits, bvZeroExtend_128_toNat]
  have hPow : Nat.pow 2 128 = Nat.pow 2 64 * Nat.pow 2 64 := by decide
  change Nat.mod (Nat.mod n (Nat.pow 2 128)) (Nat.pow 2 64) =
    Nat.mod n (Nat.pow 2 64)
  rw [hPow]
  exact nat_mod_mod_mul_left n (Nat.pow 2 64) (Nat.pow 2 64)

/-- Zero-extending a 64-bit bitvector to 128 bits is fixed by `truncateBits
.i64`. -/
theorem truncateBits_i64_bvZeroExtend (w : BitVec 64) :
    truncateBits .i64 (bvZeroExtend 128 w) = bvZeroExtend 128 w :=
  truncateBits_of_toNat_lt (by
    rw [bvZeroExtend_128_toNat]
    exact w.isLt)

/-- Truncating `BitVec.ofNat 128 n` to `.i64` is the identity when
`n < 2 ^ 64`. -/
theorem truncateBits_i64_ofNat_lt {n : Nat} (h : n < Nat.pow 2 64) :
    truncateBits .i64 (BitVec.ofNat 128 n) = BitVec.ofNat 128 n := by
  apply truncateBits_of_toNat_lt
  change Nat.mod n (Nat.pow 2 128) < Nat.pow 2 IntWidth.i64.bitWidth
  exact Nat.lt_of_le_of_lt (Nat.mod_le _ _) h

/-- Computable closed-form result value of 64-bit unsigned bitwise AND. -/
@[expose] def u64BitAndVal (x y : BitVec 64) : Val :=
  .scalar ⟨.i64, false, BitVec.ofNat 128 (Nat.land x.toNat y.toNat)⟩

/-- Computable closed-form result value of 64-bit unsigned bitwise OR. -/
@[expose] def u64BitOrVal (x y : BitVec 64) : Val :=
  .scalar ⟨.i64, false, BitVec.ofNat 128 (Nat.lor x.toNat y.toNat)⟩

/-- Computable closed-form result value of 64-bit unsigned left shift by `k`. -/
@[expose] def u64ShlVal (x : BitVec 64) (k : Nat) : Val :=
  .scalar ⟨.i64, false,
    BitVec.ofNat 128 (BitVec.ofNat 64 (Nat.shiftLeft x.toNat k)).toNat⟩

/-- Computable closed-form result value of 64-bit unsigned logical right shift
by `k`. -/
@[expose] def u64ShrVal (x : BitVec 64) (k : Nat) : Val :=
  .scalar ⟨.i64, false, BitVec.ofNat 128 (Nat.shiftRight x.toNat k)⟩

/-- Definitional unfolding of `u64BitAndVal x y`. -/
theorem u64BitAndVal_eq (x y : BitVec 64) :
    u64BitAndVal x y =
      .scalar ⟨.i64, false, BitVec.ofNat 128 (Nat.land x.toNat y.toNat)⟩ :=
  rfl

/-- Definitional unfolding of `u64BitOrVal x y`. -/
theorem u64BitOrVal_eq (x y : BitVec 64) :
    u64BitOrVal x y =
      .scalar ⟨.i64, false, BitVec.ofNat 128 (Nat.lor x.toNat y.toNat)⟩ :=
  rfl

/-- Equivalence of `u64ShlVal x k` with `bvZeroExtend 128`. -/
theorem u64ShlVal_eq (x : BitVec 64) (k : Nat) :
    u64ShlVal x k =
      .scalar ⟨.i64, false,
        bvZeroExtend 128 (BitVec.ofNat 64 (Nat.shiftLeft x.toNat k))⟩ :=
  rfl

/-- Definitional unfolding of `u64ShrVal x k`. -/
theorem u64ShrVal_eq (x : BitVec 64) (k : Nat) :
    u64ShrVal x k =
      .scalar ⟨.i64, false, BitVec.ofNat 128 (Nat.shiftRight x.toNat k)⟩ :=
  rfl

/-- `Trusted.MirSemantics` 64-bit bitwise AND reduces to `u64BitAndVal`. -/
theorem u64BitAnd_sem_eq (x y : BitVec 64) :
    (.scalar ⟨.i64, false,
      truncateBits .i64 (bvAnd (truncateBits .i64 (bvZeroExtend 128 x))
        (truncateBits .i64 (bvZeroExtend 128 y)))⟩ : Val) =
      u64BitAndVal x y := by
  unfold u64BitAndVal bvAnd
  rw [truncateBits_i64_bvZeroExtend x, truncateBits_i64_bvZeroExtend y,
      bvZeroExtend_128_toNat x, bvZeroExtend_128_toNat y]
  exact congrArg (fun b => Val.scalar ⟨.i64, false, b⟩)
    (truncateBits_i64_ofNat_lt
      (Anneal.NatBitwise.land_lt_two_pow x.isLt y.isLt))

/-- `Trusted.MirSemantics` 64-bit bitwise OR reduces to `u64BitOrVal`. -/
theorem u64BitOr_sem_eq (x y : BitVec 64) :
    (.scalar ⟨.i64, false,
      truncateBits .i64 (bvOr (truncateBits .i64 (bvZeroExtend 128 x))
        (truncateBits .i64 (bvZeroExtend 128 y)))⟩ : Val) =
      u64BitOrVal x y := by
  unfold u64BitOrVal bvOr
  rw [truncateBits_i64_bvZeroExtend x, truncateBits_i64_bvZeroExtend y,
      bvZeroExtend_128_toNat x, bvZeroExtend_128_toNat y]
  exact congrArg (fun b => Val.scalar ⟨.i64, false, b⟩)
    (truncateBits_i64_ofNat_lt
      (Anneal.NatBitwise.lor_lt_two_pow x.isLt y.isLt))

/-- `Trusted.MirSemantics` 64-bit left shift reduces to `u64ShlVal`. -/
theorem u64Shl_sem_eq (x : BitVec 64) (k : Nat) :
    (.scalar ⟨.i64, false,
      truncateBits .i64 (bvOfInt 128
        (.ofNat (Nat.shiftLeft
          (truncateBits .i64 (bvZeroExtend 128 x)).toNat k)))⟩ : Val) =
      u64ShlVal x k := by
  rw [u64ShlVal_eq]
  unfold bvOfInt intEmod
  rw [truncateBits_i64_bvZeroExtend x, bvZeroExtend_128_toNat x]
  dsimp only [Int.natAbs, Int.toNat]
  rw [truncateBits_i64_ofNat]
  have hMod :
      BitVec.ofNat 64
        (Nat.mod (Nat.shiftLeft x.toNat k) (Nat.pow 2 128)) =
      BitVec.ofNat 64 (Nat.shiftLeft x.toNat k) := by
    apply bitVec_eq_of_toNat_eq
    have hPow : Nat.pow 2 128 = Nat.pow 2 64 * Nat.pow 2 64 := by decide
    change Nat.mod (Nat.mod (Nat.shiftLeft x.toNat k) (Nat.pow 2 128))
        (Nat.pow 2 64) =
      Nat.mod (Nat.shiftLeft x.toNat k) (Nat.pow 2 64)
    rw [hPow]
    exact nat_mod_mod_mul_left _ (Nat.pow 2 64) (Nat.pow 2 64)
  rw [hMod]

/-- `Trusted.MirSemantics` 64-bit logical right shift reduces to `u64ShrVal`. -/
theorem u64Shr_sem_eq (x : BitVec 64) (k : Nat) :
    (.scalar ⟨.i64, false,
      truncateBits .i64 (bvOfInt 128
        (.ofNat (Nat.shiftRight
          (truncateBits .i64 (bvZeroExtend 128 x)).toNat k)))⟩ : Val) =
      u64ShrVal x k := by
  unfold u64ShrVal bvOfInt intEmod
  rw [truncateBits_i64_bvZeroExtend x, bvZeroExtend_128_toNat x]
  dsimp only [Int.natAbs, Int.toNat]
  have hLt : Nat.shiftRight x.toNat k < Nat.pow 2 64 :=
    Nat.lt_of_le_of_lt (Nat.shiftRight_le _ _) x.isLt
  have hMod :
      Nat.mod (Nat.shiftRight x.toNat k) (Nat.pow 2 128) =
      Nat.shiftRight x.toNat k :=
    Nat.mod_eq_of_lt (Nat.lt_trans hLt (by decide))
  rw [hMod]
  exact congrArg (fun b => Val.scalar ⟨.i64, false, b⟩)
    (truncateBits_i64_ofNat_lt hLt)

/-! ## Abstract-Modulus Signed Cast, Scalar Decode, and Width-Parametric `evalBinOp` Lemmas -/

/-- Half-modulus $2^{\text{bitWidth} - 1}$ for signed scalar range reasoning. -/
@[expose] def intWidthHalfModulus : IntWidth → Nat
  | .i8 => Nat.pow 2 7
  | .i16 => Nat.pow 2 15
  | .i32 => Nat.pow 2 31
  | .i64 | .isize => Nat.pow 2 63
  | .i128 => Nat.pow 2 127

/-- Every `IntWidth` has a strictly positive half-modulus `2^(bits-1)`. -/
theorem intWidthHalfModulus_pos (w : IntWidth) : 0 < intWidthHalfModulus w := by
  cases w <;> decide

/-- `intWidthModulus w = 2 * intWidthHalfModulus w`. -/
theorem intWidthModulus_eq_two_mul_half (w : IntWidth) :
    intWidthModulus w = 2 * intWidthHalfModulus w := by
  cases w <;> decide

/-- `intWidthModulus w = intWidthHalfModulus w + intWidthHalfModulus w`. -/
theorem intWidthModulus_eq_half_add_half (w : IntWidth) :
    intWidthModulus w = intWidthHalfModulus w + intWidthHalfModulus w := by
  cases w <;> decide

/-- `intWidthHalfModulus w < intWidthModulus w`. -/
theorem intWidthHalfModulus_lt_modulus (w : IntWidth) :
    intWidthHalfModulus w < intWidthModulus w := by
  cases w <;> decide

/-- `intWidthModulus w ≤ 2^128`. -/
theorem intWidthModulus_le_pow_128 (w : IntWidth) :
    intWidthModulus w ≤ Nat.pow 2 128 := by
  cases w <;> decide

/-- `intWidthHalfModulus w ≤ 2^127`. -/
theorem intWidthHalfModulus_le_pow_127 (w : IntWidth) :
    intWidthHalfModulus w ≤ Nat.pow 2 127 := by
  cases w <;> decide

/-- `intWidthModulus w` divides `2^128`. -/
theorem intWidthModulus_dvd_pow_128 (w : IntWidth) :
    Nat.mod (Nat.pow 2 128) (intWidthModulus w) = 0 := by
  cases w <;> decide

private theorem int_subNatNat_of_le (N k : Nat) (h : k ≤ N) :
    Int.subNatNat N k = Int.ofNat (N - k) := by
  unfold Int.subNatNat
  rw [Nat.sub_eq_zero_of_le h]

private theorem int_subNatNat_of_lt (a N : Nat) (h : a < N) :
    Int.subNatNat a N = Int.negSucc (N - a - 1) := by
  unfold Int.subNatNat
  have hPos : 0 < N - a := Nat.sub_pos_of_lt h
  cases hSub : N - a with
  | zero => rw [hSub] at hPos; nomatch hPos
  | succ r => rfl

private theorem int_ofNat_sub_eq_subNatNat (a b : Nat) :
    Int.ofNat a - Int.ofNat b = Int.subNatNat a b := by
  cases b with
  | zero =>
    unfold Int.subNatNat
    rw [Nat.zero_sub a, Nat.sub_zero]
    change Int.ofNat (a + 0) = Int.ofNat a
    rw [Nat.add_zero]
  | succ _ => rfl

private theorem int_ofNat_sub_of_le {a b : Nat} (h : b ≤ a) :
    Int.ofNat a - Int.ofNat b = Int.ofNat (a - b) :=
  (int_ofNat_sub_eq_subNatNat a b).trans (int_subNatNat_of_le a b h)

private theorem int_ofNat_sub_of_lt {a b : Nat} (h : a < b) :
    Int.ofNat a - Int.ofNat b = Int.negSucc (b - a - 1) :=
  (int_ofNat_sub_eq_subNatNat a b).trans (int_subNatNat_of_lt a b h)

/-- Abstract-modulus `intEmod` on non-negative integers. -/
theorem intEmod_ofNat (a N : Nat) :
    intEmod (Int.ofNat a) (Int.ofNat N) = Int.ofNat (Nat.mod a N) := rfl

/-- Abstract-modulus `intEmod (Int.negSucc m) (Int.ofNat N)` for `0 < N`,
parameterized over an abstract `N` so the kernel never unfolds `2^128`. -/
theorem intEmod_negSucc_of_pos (m N : Nat) (hN : 0 < N) :
    intEmod (Int.negSucc m) (Int.ofNat N) =
      Int.ofNat (N - (Nat.mod m N + 1)) := by
  dsimp only [intEmod, Int.natAbs]
  have hLe : Nat.mod m N + 1 ≤ N := Nat.succ_le_of_lt (Nat.mod_lt m hN)
  exact int_subNatNat_of_le N (Nat.mod m N + 1) hLe

private theorem nat_mod_eq_of_lt {a b : Nat} (h : a < b) : Nat.mod a b = a :=
  Nat.mod_eq_of_lt h

private theorem nat_mod_self (a : Nat) : Nat.mod a a = 0 :=
  Nat.mod_self a

private theorem nat_mul_mod_right (a b : Nat) : Nat.mod (a * b) a = 0 :=
  Nat.mul_mod_right a b

private theorem nat_add_mul_mod_self_left (a b c : Nat) :
    Nat.mod (a + b * c) b = Nat.mod a b :=
  Nat.add_mul_mod_self_left a b c

private theorem nat_add_mod_left_eq (a b m : Nat) :
    Nat.mod (Nat.mod a m + b) m = Nat.mod (a + b) m := by
  have hDecomp : a = m * Nat.div a m + Nat.mod a m := (Nat.div_add_mod a m).symm
  have hRearr : a + b = (Nat.mod a m + b) + m * Nat.div a m := by
    have h1 := congrArg (fun z => z + b) hDecomp
    rw [Nat.add_assoc, Nat.add_comm (m * Nat.div a m) (Nat.mod a m + b)] at h1
    exact h1
  rw [hRearr, nat_add_mul_mod_self_left]

private theorem bitVec128_ofNat_toNat_id (v : BitVec 128) :
    BitVec.ofNat 128 v.toNat = v := by
  apply bitVec_eq_of_toNat_eq
  exact nat_mod_eq_of_lt v.isLt

/-- Abstract-modulus `intEmod (Int.negSucc m) (Int.ofNat N)` when `m < N`. -/
theorem intEmod_negSucc_of_lt (m N : Nat) (h : m < N) :
    intEmod (Int.negSucc m) (Int.ofNat N) = Int.ofNat (N - (m + 1)) := by
  have hN : 0 < N := Nat.lt_of_le_of_lt (Nat.zero_le m) h
  rw [intEmod_negSucc_of_pos m N hN, nat_mod_eq_of_lt h]

/-- `BitVec.toNat` of `bvOfInt n (Int.ofNat a)`. -/
theorem bvOfInt_ofNat_toNat (n a : Nat) :
    (bvOfInt n (Int.ofNat a)).toNat = Nat.mod a (Nat.pow 2 n) := by
  dsimp only [bvOfInt]
  rw [intEmod_ofNat]
  change Nat.mod (Nat.mod a (Nat.pow 2 n)) (Nat.pow 2 n) = Nat.mod a (Nat.pow 2 n)
  exact nat_mod_eq_of_lt (Nat.mod_lt a (Nat.pow_pos (Nat.zero_lt_succ 1)))

/-- Abstract-modulus `BitVec.toNat` of `bvOfInt n (Int.negSucc m)`, avoiding
structural unfolding of `2^n` on symbolic `m`. -/
theorem bvOfInt_negSucc_toNat (n m : Nat) :
    (bvOfInt n (Int.negSucc m)).toNat =
      Nat.pow 2 n - (Nat.mod m (Nat.pow 2 n) + 1) := by
  have hPos : 0 < Nat.pow 2 n := Nat.pow_pos (Nat.zero_lt_succ 1)
  dsimp only [bvOfInt]
  rw [intEmod_negSucc_of_pos m (Nat.pow 2 n) hPos]
  change Nat.mod (Nat.pow 2 n - (Nat.mod m (Nat.pow 2 n) + 1)) (Nat.pow 2 n) =
    Nat.pow 2 n - (Nat.mod m (Nat.pow 2 n) + 1)
  exact nat_mod_eq_of_lt (Nat.sub_lt hPos (Nat.zero_lt_succ _))

/-- `BitVec.toNat` of `bvOfInt n (Int.negSucc m)` when `m < 2^n`. -/
theorem bvOfInt_negSucc_toNat_of_lt (n m : Nat) (h : m < Nat.pow 2 n) :
    (bvOfInt n (Int.negSucc m)).toNat = Nat.pow 2 n - (m + 1) := by
  rw [bvOfInt_negSucc_toNat n m, nat_mod_eq_of_lt h]

private theorem nat_sub_mod_of_dvd {N M k : Nat}
    (hM : 0 < M) (hDvd : Nat.mod N M = 0) (_hPos : 0 < k) (hKLt : k ≤ N) :
    Nat.mod (N - k) M =
      if Nat.beq (Nat.mod k M) 0 then 0 else M - Nat.mod k M := by
  have hNDecomp : N = M * Nat.div N M := by
    have h : M * Nat.div N M + Nat.mod N M = N := Nat.div_add_mod N M
    rw [hDvd, Nat.add_zero] at h
    exact h.symm
  have hKDecomp : M * Nat.div k M + Nat.mod k M = k := Nat.div_add_mod k M
  cases hZ : Nat.beq (Nat.mod k M) 0 with
  | true =>
    have hR0 : Nat.mod k M = 0 := Nat.eq_of_beq_eq_true hZ
    rw [hR0, Nat.add_zero] at hKDecomp
    have hSub : N - k = M * (Nat.div N M - Nat.div k M) := by
      have hMul : M * (Nat.div N M - Nat.div k M) = M * Nat.div N M - M * Nat.div k M :=
        Nat.mul_sub_left_distrib M (Nat.div N M) (Nat.div k M)
      rw [hMul, ← hNDecomp, hKDecomp]
    rw [hSub, nat_mul_mod_right]
    rfl
  | false =>
    have hRPos : 0 < Nat.mod k M := by
      cases hr : Nat.mod k M with
      | zero => rw [hr] at hZ; nomatch hZ
      | succ _ => exact Nat.zero_lt_succ _
    have hRLt : Nat.mod k M < M := Nat.mod_lt k hM
    have hQlt : Nat.div k M < Nat.div N M := by
      cases Nat.lt_or_ge (Nat.div k M) (Nat.div N M) with
      | inl h => exact h
      | inr hGe =>
        have h1 : N < k := by
          rw [hNDecomp, ← hKDecomp]
          exact Nat.lt_of_le_of_lt (Nat.mul_le_mul_left M hGe)
            (Nat.lt_add_of_pos_right hRPos)
        exact False.elim (Nat.not_le_of_gt h1 hKLt)
    have hQSuccLe : Nat.div k M + 1 ≤ Nat.div N M := hQlt
    have hSub : N - k = (M - Nat.mod k M) + M * (Nat.div N M - (Nat.div k M + 1)) := by
      have hAdd :
          ((M - Nat.mod k M) + M * (Nat.div N M - (Nat.div k M + 1))) + k = N := by
        have hRearr :
            ((M - Nat.mod k M) + M * (Nat.div N M - (Nat.div k M + 1))) +
              (M * Nat.div k M + Nat.mod k M) =
            ((M - Nat.mod k M) + Nat.mod k M) +
              (M * (Nat.div N M - (Nat.div k M + 1)) + M * Nat.div k M) := by
          rw [Nat.add_assoc (M - Nat.mod k M) _ (M * Nat.div k M + Nat.mod k M),
              Nat.add_comm (M * Nat.div k M) (Nat.mod k M),
              ← Nat.add_assoc (M * (Nat.div N M - (Nat.div k M + 1))) (Nat.mod k M) (M * Nat.div k M),
              Nat.add_comm (M * (Nat.div N M - (Nat.div k M + 1))) (Nat.mod k M),
              Nat.add_assoc (Nat.mod k M) _ (M * Nat.div k M),
              ← Nat.add_assoc (M - Nat.mod k M) (Nat.mod k M) _]
        have hStep1 :
            ((M - Nat.mod k M) + M * (Nat.div N M - (Nat.div k M + 1))) + k =
            ((M - Nat.mod k M) + M * (Nat.div N M - (Nat.div k M + 1))) +
              (M * Nat.div k M + Nat.mod k M) :=
          congrArg (fun z => ((M - Nat.mod k M) + M * (Nat.div N M - (Nat.div k M + 1))) + z)
            hKDecomp.symm
        rw [hStep1, hRearr, Nat.sub_add_cancel (Nat.le_of_lt hRLt),
            ← Nat.mul_add M (Nat.div N M - (Nat.div k M + 1)) (Nat.div k M)]
        have h1 : M + M * ((Nat.div N M - (Nat.div k M + 1)) + Nat.div k M) =
            M * (1 + ((Nat.div N M - (Nat.div k M + 1)) + Nat.div k M)) := by
          rw [Nat.mul_add M 1 _, Nat.mul_one]
        rw [h1]
        have h2 : 1 + ((Nat.div N M - (Nat.div k M + 1)) + Nat.div k M) = Nat.div N M := by
          rw [Nat.add_comm 1 _, Nat.add_assoc _ (Nat.div k M) 1,
              Nat.sub_add_cancel hQSuccLe]
        rw [h2, ← hNDecomp]
      have hStep := congrArg (fun z => z - k) hAdd.symm
      rw [Nat.add_sub_cancel] at hStep
      exact hStep
    rw [hSub, nat_add_mul_mod_self_left, nat_mod_eq_of_lt (Nat.sub_lt hM hRPos)]
    rfl

/-- Abstract-modulus modular reduction of `(bvOfInt n (Int.negSucc m)).toNat`
modulo any divisor `M` of `2^n` (e.g. `intWidthModulus w` dividing `2^128`). -/
theorem bvOfInt_negSucc_mod_of_dvd {n M : Nat} (m : Nat)
    (hM : 0 < M) (hDvd : Nat.mod (Nat.pow 2 n) M = 0) :
    Nat.mod (bvOfInt n (Int.negSucc m)).toNat M = M - (Nat.mod m M + 1) := by
  have hPosN : 0 < Nat.pow 2 n := Nat.pow_pos (Nat.zero_lt_succ 1)
  rw [bvOfInt_negSucc_toNat n m]
  let k := Nat.mod m (Nat.pow 2 n) + 1
  have hkLe : k ≤ Nat.pow 2 n := Nat.succ_le_of_lt (Nat.mod_lt m hPosN)
  have hkPos : 0 < k := Nat.zero_lt_succ _
  rw [nat_sub_mod_of_dvd hM hDvd hkPos hkLe]
  have hModK : Nat.mod k M = Nat.mod (Nat.mod m M + 1) M := by
    have hM1 : Nat.mod (Nat.mod m (Nat.pow 2 n)) M = Nat.mod m M := by
      have hNDecomp : Nat.pow 2 n = M * Nat.div (Nat.pow 2 n) M := by
        have h : M * Nat.div (Nat.pow 2 n) M + Nat.mod (Nat.pow 2 n) M = Nat.pow 2 n :=
          Nat.div_add_mod (Nat.pow 2 n) M
        rw [hDvd, Nat.add_zero] at h
        exact h.symm
      rw [hNDecomp]
      exact nat_mod_mod_mul_left m M (Nat.div (Nat.pow 2 n) M)
    dsimp only [k]
    rw [← nat_add_mod_left_eq (Nat.mod m (Nat.pow 2 n)) 1 M, hM1]
  rw [hModK]
  have hR1Le : Nat.mod m M + 1 ≤ M := Nat.succ_le_of_lt (Nat.mod_lt m hM)
  cases Nat.eq_or_lt_of_le hR1Le with
  | inl hEqM =>
    rw [hEqM, nat_mod_self, Nat.sub_self]
    rfl
  | inr hLtM =>
    rw [nat_mod_eq_of_lt hLtM]
    have hNeZ : Nat.beq (Nat.mod m M + 1) 0 = false := rfl
    rw [hNeZ]
    rfl

/-- Exact `.toNat` of `truncateBits w (bvOfInt 128 (Int.ofNat a))` across all
six `IntWidth`s. -/
theorem truncateBits_bvOfInt_ofNat_toNat (w : IntWidth) (a : Nat) :
    (truncateBits w (bvOfInt 128 (Int.ofNat a))).toNat =
      Nat.mod a (intWidthModulus w) := by
  rw [toNat_truncateBits, bvOfInt_ofNat_toNat]
  have hDvd := intWidthModulus_dvd_pow_128 w
  have hN : Nat.pow 2 128 = intWidthModulus w * Nat.div (Nat.pow 2 128) (intWidthModulus w) := by
    have h : intWidthModulus w * Nat.div (Nat.pow 2 128) (intWidthModulus w) +
        Nat.mod (Nat.pow 2 128) (intWidthModulus w) = Nat.pow 2 128 :=
      Nat.div_add_mod (Nat.pow 2 128) (intWidthModulus w)
    rw [hDvd, Nat.add_zero] at h
    exact h.symm
  rw [hN]
  exact nat_mod_mod_mul_left a (intWidthModulus w) _

/-- Exact `.toNat` of `truncateBits w (bvOfInt 128 (Int.negSucc m))` across all
six `IntWidth`s without unfolding `2^128` structurally. -/
theorem truncateBits_bvOfInt_negSucc_toNat (w : IntWidth) (m : Nat) :
    (truncateBits w (bvOfInt 128 (Int.negSucc m))).toNat =
      intWidthModulus w - (Nat.mod m (intWidthModulus w) + 1) := by
  rw [toNat_truncateBits]
  exact bvOfInt_negSucc_mod_of_dvd m (intWidth_modulus_pos w) (intWidthModulus_dvd_pow_128 w)

/-- Round-trip `bvOfInt 128 (bvToInt x) = x` for every `x : BitVec 128`. -/
theorem bvOfInt_bvToInt_128 (x : BitVec 128) :
    bvOfInt 128 (bvToInt x) = x := by
  apply bitVec_eq_of_toNat_eq
  unfold bvToInt
  cases Nat.lt_or_ge (2 * x.toNat) (Nat.pow 2 128) with
  | inl hLt =>
    rw [ite_prop_true hLt, bvOfInt_ofNat_toNat, nat_mod_eq_of_lt x.isLt]
  | inr hGe =>
    rw [ite_prop_false (Nat.not_lt_of_ge hGe), int_ofNat_sub_of_lt x.isLt]
    have hDiffPos : 0 < Nat.pow 2 128 - x.toNat := Nat.sub_pos_of_lt x.isLt
    have hDiffLt : Nat.pow 2 128 - x.toNat - 1 < Nat.pow 2 128 :=
      Nat.lt_of_le_of_lt (Nat.sub_le _ 1)
        (Nat.sub_lt (Nat.pow_pos (Nat.zero_lt_succ 1)) (by
          cases hx : x.toNat with
          | zero =>
            rw [hx] at hGe
            have h0 : 2 * 0 = 0 := rfl
            rw [h0] at hGe
            have hPos : 0 < Nat.pow 2 128 := Nat.pow_pos (Nat.zero_lt_succ 1)
            exact False.elim (Nat.not_le_of_gt hPos hGe)
          | succ _ => exact Nat.zero_lt_succ _))
    rw [bvOfInt_negSucc_toNat_of_lt 128 _ hDiffLt, Nat.sub_add_cancel hDiffPos]
    have hAdd : (Nat.pow 2 128 - x.toNat) + x.toNat = Nat.pow 2 128 :=
      Nat.sub_add_cancel (Nat.le_of_lt x.isLt)
    have hStep := congrArg (fun z => z - (Nat.pow 2 128 - x.toNat)) hAdd.symm
    rw [Nat.add_comm (Nat.pow 2 128 - x.toNat) x.toNat, Nat.add_sub_cancel] at hStep
    exact hStep

private theorem bvToInt_bvOfInt_128_of_lt_half {a : Nat}
    (h : a < Nat.pow 2 127) :
    bvToInt (bvOfInt 128 (Int.ofNat a)) = Int.ofNat a := by
  have h128 : a < Nat.pow 2 128 := Nat.lt_trans h (by decide)
  have hToNat : (bvOfInt 128 (Int.ofNat a)).toNat = a := by
    rw [bvOfInt_ofNat_toNat, nat_mod_eq_of_lt h128]
  unfold bvToInt
  rw [hToNat]
  have h2 : 2 * a < Nat.pow 2 128 := by
    have hEq : Nat.pow 2 128 = 2 * Nat.pow 2 127 := by decide
    rw [hEq]
    exact Nat.mul_lt_mul_of_pos_left h (Nat.zero_lt_succ 1)
  rw [ite_prop_true h2]

private theorem bvToInt_bvOfInt_128_negSucc_of_lt_half {m : Nat}
    (h : m < Nat.pow 2 127) :
    bvToInt (bvOfInt 128 (Int.negSucc m)) = Int.negSucc m := by
  have h128 : m < Nat.pow 2 128 := Nat.lt_trans h (by decide)
  have hToNat : (bvOfInt 128 (Int.negSucc m)).toNat = Nat.pow 2 128 - (m + 1) :=
    bvOfInt_negSucc_toNat_of_lt 128 m h128
  unfold bvToInt
  rw [hToNat]
  have hPow : Nat.pow 2 128 = Nat.pow 2 127 + Nat.pow 2 127 := by decide
  have hGeHalf : Nat.pow 2 127 ≤ Nat.pow 2 128 - (m + 1) := by
    have hLe : m + 1 ≤ Nat.pow 2 127 := Nat.succ_le_of_lt h
    have h1 : Nat.pow 2 127 + (m + 1) ≤ Nat.pow 2 128 := by
      rw [hPow]
      exact Nat.add_le_add_left hLe (Nat.pow 2 127)
    have h2 := Nat.sub_le_sub_right h1 (m + 1)
    rw [Nat.add_sub_cancel] at h2
    exact h2
  have hGe2 : Nat.pow 2 128 ≤ 2 * (Nat.pow 2 128 - (m + 1)) := by
    have hEq2 : Nat.pow 2 128 = 2 * Nat.pow 2 127 := by decide
    rw [hEq2]
    exact Nat.mul_le_mul_left 2 hGeHalf
  rw [ite_prop_false (Nat.not_lt_of_ge hGe2)]
  have hLt128 : Nat.pow 2 128 - (m + 1) < Nat.pow 2 128 :=
    Nat.sub_lt (Nat.pow_pos (Nat.zero_lt_succ 1)) (Nat.zero_lt_succ m)
  rw [int_ofNat_sub_of_lt hLt128]
  have hSubSelf : Nat.pow 2 128 - (Nat.pow 2 128 - (m + 1)) = m + 1 := by
    have hAdd : (Nat.pow 2 128 - (m + 1)) + (m + 1) = Nat.pow 2 128 :=
      Nat.sub_add_cancel (Nat.succ_le_of_lt h128)
    have hStep := congrArg (fun z => z - (Nat.pow 2 128 - (m + 1))) hAdd.symm
    rw [Nat.add_comm (Nat.pow 2 128 - (m + 1)) (m + 1), Nat.add_sub_cancel] at hStep
    exact hStep
  rw [hSubSelf]
  rfl

/-- Signed decoding (`signExtendBits`) when the low `w.bitWidth` bits lie in
`[0, 2^(w-1))`. -/
theorem signExtendBits_eq_of_lt_half (w : IntWidth) (b : BitVec 128)
    (h : Nat.mod b.toNat (intWidthModulus w) < intWidthHalfModulus w) :
    signExtendBits w b = Int.ofNat (Nat.mod b.toNat (intWidthModulus w)) := by
  have hStep : ∀ (k : Nat) (hk : k = w.bitWidth) (hM : intWidthModulus w = Nat.pow 2 k)
      (hH : intWidthHalfModulus w = Nat.pow 2 (k - 1))
      (h2 : Nat.pow 2 k = 2 * Nat.pow 2 (k - 1)),
      let low : BitVec k := BitVec.ofNat k (Nat.shiftRight b.toNat 0)
      bvToInt (bvSignExtend 128 low) = Int.ofNat (Nat.mod b.toNat (intWidthModulus w)) := by
    intro k _ hM hH h2
    have hLowToNat : (BitVec.ofNat k (Nat.shiftRight b.toNat 0)).toNat =
        Nat.mod b.toNat (intWidthModulus w) := by
      rw [hM]; rfl
    have hCmp : 2 * (BitVec.ofNat k (Nat.shiftRight b.toNat 0)).toNat < Nat.pow 2 k := by
      rw [hLowToNat, h2, ← hH]
      exact Nat.mul_lt_mul_of_pos_left h (Nat.zero_lt_succ 1)
    dsimp only [bvSignExtend]
    unfold bvToInt
    rw [ite_prop_true hCmp, hLowToNat]
    have hLt127 : Nat.mod b.toNat (intWidthModulus w) < Nat.pow 2 127 :=
      Nat.lt_of_lt_of_le h (intWidthHalfModulus_le_pow_127 w)
    exact bvToInt_bvOfInt_128_of_lt_half hLt127
  dsimp only [signExtendBits, bvExtractLsb, bvExtractLsb']
  cases w with
  | i8 => exact hStep 8 rfl rfl rfl (by decide)
  | i16 => exact hStep 16 rfl rfl rfl (by decide)
  | i32 => exact hStep 32 rfl rfl rfl (by decide)
  | i64 => exact hStep 64 rfl rfl rfl (by decide)
  | i128 => exact hStep 128 rfl rfl rfl (by decide)
  | isize => exact hStep 64 rfl rfl rfl (by decide)

/-- Signed decoding (`signExtendBits`) when the low `w.bitWidth` bits lie in
`[2^(w-1), 2^w)`, avoiding structural `2^128` unfolding. -/
theorem signExtendBits_eq_of_ge_half (w : IntWidth) (b : BitVec 128)
    (h : intWidthHalfModulus w ≤ Nat.mod b.toNat (intWidthModulus w)) :
    signExtendBits w b =
      Int.negSucc (intWidthModulus w - Nat.mod b.toNat (intWidthModulus w) - 1) := by
  have hModLt : Nat.mod b.toNat (intWidthModulus w) < intWidthModulus w :=
    Nat.mod_lt _ (intWidth_modulus_pos w)
  have hStep : ∀ (k : Nat) (hk : k = w.bitWidth) (hM : intWidthModulus w = Nat.pow 2 k)
      (hH : intWidthHalfModulus w = Nat.pow 2 (k - 1))
      (h2 : Nat.pow 2 k = 2 * Nat.pow 2 (k - 1)),
      let low : BitVec k := BitVec.ofNat k (Nat.shiftRight b.toNat 0)
      bvToInt (bvSignExtend 128 low) =
        Int.negSucc (intWidthModulus w - Nat.mod b.toNat (intWidthModulus w) - 1) := by
    intro k _ hM hH h2
    have hLowToNat : (BitVec.ofNat k (Nat.shiftRight b.toNat 0)).toNat =
        Nat.mod b.toNat (intWidthModulus w) := by
      rw [hM]; rfl
    have hCmp : Nat.pow 2 k ≤ 2 * (BitVec.ofNat k (Nat.shiftRight b.toNat 0)).toNat := by
      rw [hLowToNat, h2, ← hH]
      exact Nat.mul_le_mul_left 2 h
    dsimp only [bvSignExtend]
    have hInner :
        bvToInt (BitVec.ofNat k (Nat.shiftRight b.toNat 0)) =
          Int.negSucc (intWidthModulus w - Nat.mod b.toNat (intWidthModulus w) - 1) := by
      unfold bvToInt
      rw [ite_prop_false (Nat.not_lt_of_ge hCmp), hLowToNat, ← hM,
          int_ofNat_sub_of_lt hModLt]
    rw [hInner]
    have hDiffLeHalf : intWidthModulus w - Nat.mod b.toNat (intWidthModulus w) ≤
        intWidthHalfModulus w := by
      have h1 := Nat.sub_le_sub_left h (intWidthModulus w)
      have h2' : intWidthModulus w - intWidthHalfModulus w = intWidthHalfModulus w := by
        rw [intWidthModulus_eq_half_add_half w, Nat.add_sub_cancel]
      rw [h2'] at h1
      exact h1
    have hDiffPos : 0 < intWidthModulus w - Nat.mod b.toNat (intWidthModulus w) :=
      Nat.sub_pos_of_lt hModLt
    have hMLtHalf : intWidthModulus w - Nat.mod b.toNat (intWidthModulus w) - 1 <
        intWidthHalfModulus w :=
      Nat.lt_of_lt_of_le (Nat.sub_lt hDiffPos (Nat.zero_lt_succ 0)) hDiffLeHalf
    have hMLt127 : intWidthModulus w - Nat.mod b.toNat (intWidthModulus w) - 1 <
        Nat.pow 2 127 :=
      Nat.lt_of_lt_of_le hMLtHalf (intWidthHalfModulus_le_pow_127 w)
    exact bvToInt_bvOfInt_128_negSucc_of_lt_half hMLt127
  dsimp only [signExtendBits, bvExtractLsb, bvExtractLsb']
  cases w with
  | i8 => exact hStep 8 rfl rfl rfl (by decide)
  | i16 => exact hStep 16 rfl rfl rfl (by decide)
  | i32 => exact hStep 32 rfl rfl rfl (by decide)
  | i64 => exact hStep 64 rfl rfl rfl (by decide)
  | i128 => exact hStep 128 rfl rfl rfl (by decide)
  | isize => exact hStep 64 rfl rfl rfl (by decide)

/-- Width-parametric `decodeScalar` for unsigned scalars. -/
theorem decodeScalar_unsigned (w : IntWidth) (b : BitVec 128) :
    decodeScalar ⟨w, false, b⟩ = Int.ofNat (Nat.mod b.toNat (intWidthModulus w)) := by
  dsimp only [decodeScalar]
  rw [ite_bool_false rfl, toNat_truncateBits]

/-- Width-parametric `decodeScalar` for in-range unsigned scalars. -/
theorem decodeScalar_unsigned_of_lt {w : IntWidth} {b : BitVec 128}
    (h : b.toNat < intWidthModulus w) :
    decodeScalar ⟨w, false, b⟩ = Int.ofNat b.toNat := by
  rw [decodeScalar_unsigned, nat_mod_eq_of_lt h]

/-- Width-parametric `decodeScalar` for non-negative signed scalars. -/
theorem decodeScalar_signed_of_lt_half {w : IntWidth} {b : BitVec 128}
    (h : b.toNat < intWidthHalfModulus w) :
    decodeScalar ⟨w, true, b⟩ = Int.ofNat b.toNat := by
  have hLt : b.toNat < intWidthModulus w :=
    Nat.lt_trans h (intWidthHalfModulus_lt_modulus w)
  dsimp only [decodeScalar]
  rw [ite_bool_true rfl, truncateBits_of_toNat_lt hLt,
      signExtendBits_eq_of_lt_half w b (by rw [nat_mod_eq_of_lt hLt]; exact h),
      nat_mod_eq_of_lt hLt]

/-- Width-parametric `decodeScalar` for negative signed scalars. -/
theorem decodeScalar_signed_of_ge_half {w : IntWidth} {b : BitVec 128}
    (hGe : intWidthHalfModulus w ≤ b.toNat) (hLt : b.toNat < intWidthModulus w) :
    decodeScalar ⟨w, true, b⟩ = Int.negSucc (intWidthModulus w - b.toNat - 1) := by
  dsimp only [decodeScalar]
  rw [ite_bool_true rfl, truncateBits_of_toNat_lt hLt,
      signExtendBits_eq_of_ge_half w b (by rw [nat_mod_eq_of_lt hLt]; exact hGe),
      nat_mod_eq_of_lt hLt]

/-- Pre-eliminated unsigned `truncateScalar` equation avoiding the dependent
`Decidable` motive error in the dead signed branch. -/
theorem truncateScalar_unsigned_eq (w : IntWidth) (value : Int) :
    truncateScalar w false value =
      .ok (⟨w, false, truncateBits w (bvOfInt 128 value)⟩,
        truncateBits w (bvOfInt 128 value) != bvOfInt 128 value) := rfl

/-- Pre-eliminated signed `truncateScalar` equation eliminating the unreachable
`[-2^127, 2^127)` range guard via `bvToInt_in_i128_range`. -/
theorem truncateScalar_signed_eq (w : IntWidth) (value : Int) :
    truncateScalar w true value =
      .ok (⟨w, true, truncateBits w (bvOfInt 128 value)⟩,
        signExtendBits w (truncateBits w (bvOfInt 128 value)) !=
          bvToInt (bvOfInt 128 value)) := by
  unfold truncateScalar
  dsimp only
  rw [bvToInt_in_i128_range (bvOfInt 128 value), bvOfInt_bvToInt_128]
  rfl

/-- Unsigned-source `evalIntToIntCast` equation across all widths and target
signedness modes. -/
theorem evalIntToIntCast_unsigned (wSrc wDst : IntWidth) (sDst : Bool)
    (b : BitVec 128) :
    evalIntToIntCast (.scalar ⟨wSrc, false, b⟩) (.int wDst sDst) =
      .ok (.scalar ⟨wDst, sDst,
        BitVec.ofNat 128
          (Nat.mod (Nat.mod b.toNat (intWidthModulus wSrc))
            (intWidthModulus wDst))⟩) := by
  dsimp only [evalIntToIntCast, intLikeBits]
  rw [ite_bool_false rfl]
  apply congrArg Except.ok
  apply congrArg (fun bv => Val.scalar ⟨wDst, sDst, bv⟩)
  apply bitVec_eq_of_toNat_eq
  rw [toNat_truncateBits, toNat_truncateBits]
  have hModLt128 : Nat.mod b.toNat (intWidthModulus wSrc) < Nat.pow 2 128 :=
    Nat.lt_of_lt_of_le (Nat.mod_lt _ (intWidth_modulus_pos wSrc))
      (intWidthModulus_le_pow_128 wSrc)
  have hModDst128 :
      Nat.mod (Nat.mod b.toNat (intWidthModulus wSrc)) (intWidthModulus wDst) <
        Nat.pow 2 128 :=
    Nat.lt_of_lt_of_le (Nat.mod_lt _ (intWidth_modulus_pos wDst))
      (intWidthModulus_le_pow_128 wDst)
  change Nat.mod (Nat.mod (Nat.mod b.toNat (intWidthModulus wSrc)) (Nat.pow 2 128))
      (intWidthModulus wDst) =
    Nat.mod (Nat.mod (Nat.mod b.toNat (intWidthModulus wSrc)) (intWidthModulus wDst))
      (Nat.pow 2 128)
  rw [nat_mod_eq_of_lt hModLt128, nat_mod_eq_of_lt hModDst128]

/-- Non-negative signed-source `evalIntToIntCast` equation across all widths
and target signedness modes. -/
theorem evalIntToIntCast_signed_of_nonneg (wSrc wDst : IntWidth) (sDst : Bool)
    {b : BitVec 128} (h : b.toNat < intWidthHalfModulus wSrc) :
    evalIntToIntCast (.scalar ⟨wSrc, true, b⟩) (.int wDst sDst) =
      .ok (.scalar ⟨wDst, sDst, truncateBits wDst b⟩) := by
  dsimp only [evalIntToIntCast, intLikeBits]
  rw [ite_bool_true rfl, decodeScalar_signed_of_lt_half h]
  apply congrArg Except.ok
  apply congrArg (fun bv => Val.scalar ⟨wDst, sDst, bv⟩)
  apply bitVec_eq_of_toNat_eq
  rw [toNat_truncateBits, toNat_truncateBits, bvOfInt_ofNat_toNat]
  have h128 : b.toNat < Nat.pow 2 128 := b.isLt
  change Nat.mod (Nat.mod (Nat.mod b.toNat (Nat.pow 2 128)) (Nat.pow 2 128))
      (intWidthModulus wDst) =
    Nat.mod b.toNat (intWidthModulus wDst)
  rw [nat_mod_eq_of_lt h128, nat_mod_eq_of_lt h128]

/-- Negative signed-source `evalIntToIntCast` equation across all widths and
target signedness modes (e.g. negative `isize as usize`, `i8 as u64`,
`i128 as u128`), parameterized via abstract-modulus lemmas so Lean's kernel
never hits deep recursion on `Int.subNatNat (2^128) k`. -/
theorem evalIntToIntCast_signed_of_neg (wSrc wDst : IntWidth) (sDst : Bool)
    {b : BitVec 128}
    (hGe : intWidthHalfModulus wSrc ≤ b.toNat)
    (hLt : b.toNat < intWidthModulus wSrc) :
    evalIntToIntCast (.scalar ⟨wSrc, true, b⟩) (.int wDst sDst) =
      .ok (.scalar ⟨wDst, sDst,
        BitVec.ofNat 128
          (intWidthModulus wDst -
            (Nat.mod (intWidthModulus wSrc - b.toNat - 1)
              (intWidthModulus wDst) + 1))⟩) := by
  dsimp only [evalIntToIntCast, intLikeBits]
  rw [ite_bool_true rfl, decodeScalar_signed_of_ge_half hGe hLt]
  apply congrArg Except.ok
  apply congrArg (fun bv => Val.scalar ⟨wDst, sDst, bv⟩)
  apply bitVec_eq_of_toNat_eq
  rw [bitVec128_ofNat_toNat_id (bvOfInt 128 (Int.negSucc (intWidthModulus wSrc - b.toNat - 1))),
      truncateBits_bvOfInt_negSucc_toNat]
  have hResLt :
      intWidthModulus wDst -
        (Nat.mod (intWidthModulus wSrc - b.toNat - 1) (intWidthModulus wDst) + 1) <
      Nat.pow 2 128 :=
    Nat.lt_of_lt_of_le
      (Nat.sub_lt (intWidth_modulus_pos wDst) (Nat.zero_lt_succ _))
      (intWidthModulus_le_pow_128 wDst)
  change _ = Nat.mod _ (Nat.pow 2 128)
  rw [nat_mod_eq_of_lt hResLt]

/-- Same-width signed cast (`isize as usize`, `i64 as u64`, `i128 as u128`)
preserves the underlying truncated bit-pattern verbatim with no sign case-split
needed at the call site. -/
theorem evalIntToIntCast_signed_same_width {wSrc wDst : IntWidth} (sDst : Bool)
    {b : BitVec 128}
    (hMod : intWidthModulus wSrc = intWidthModulus wDst)
    (hLt : b.toNat < intWidthModulus wSrc) :
    evalIntToIntCast (.scalar ⟨wSrc, true, b⟩) (.int wDst sDst) =
      .ok (.scalar ⟨wDst, sDst, b⟩) := by
  cases Nat.lt_or_ge b.toNat (intWidthHalfModulus wSrc) with
  | inl hNonneg =>
    rw [evalIntToIntCast_signed_of_nonneg wSrc wDst sDst hNonneg,
        truncateBits_of_toNat_lt (by rw [← hMod]; exact hLt)]
  | inr hNeg =>
    rw [evalIntToIntCast_signed_of_neg wSrc wDst sDst hNeg hLt, ← hMod]
    apply congrArg Except.ok
    apply congrArg (fun bv => Val.scalar ⟨wDst, sDst, bv⟩)
    apply bitVec_eq_of_toNat_eq
    have hDiffPos : 0 < intWidthModulus wSrc - b.toNat := Nat.sub_pos_of_lt hLt
    have hDiffPredLt : intWidthModulus wSrc - b.toNat - 1 < intWidthModulus wSrc :=
      Nat.lt_of_lt_of_le (Nat.sub_lt hDiffPos (Nat.zero_lt_succ 0))
        (Nat.sub_le (intWidthModulus wSrc) b.toNat)
    rw [nat_mod_eq_of_lt hDiffPredLt, Nat.sub_add_cancel hDiffPos]
    have hSubSelf : intWidthModulus wSrc - (intWidthModulus wSrc - b.toNat) = b.toNat := by
      have hAdd := Nat.sub_add_cancel (Nat.le_of_lt hLt)
      have hStep := congrArg (fun z => z - (intWidthModulus wSrc - b.toNat)) hAdd.symm
      rw [Nat.add_comm (intWidthModulus wSrc - b.toNat) b.toNat, Nat.add_sub_cancel] at hStep
      exact hStep
    rw [hSubSelf]
    change Nat.mod b.toNat (Nat.pow 2 128) = b.toNat
    exact nat_mod_eq_of_lt b.isLt

/-- `bool` to integer `evalIntToIntCast` equation across all widths and
signedness modes. -/
theorem evalIntToIntCast_bool (b : Bool) (wDst : IntWidth) (sDst : Bool) :
    evalIntToIntCast (.bool b) (.int wDst sDst) =
      .ok (.scalar ⟨wDst, sDst, BitVec.ofNat 128 (if b then 1 else 0)⟩) := by
  dsimp only [evalIntToIntCast, intLikeBits]
  apply congrArg Except.ok
  apply congrArg (fun bv => Val.scalar ⟨wDst, sDst, bv⟩)
  apply truncateBits_of_toNat_lt
  cases b with
  | false => exact intWidth_modulus_pos wDst
  | true =>
    change Nat.mod 1 (Nat.pow 2 128) < intWidthModulus wDst
    cases wDst <;> decide

private theorem same_scalar_guard_false (w : IntWidth) (s : Bool) :
    (!(IntWidth.beq w w && (s == s))) = false := by
  have hw : IntWidth.beq w w = true := by cases w <;> rfl
  have hs : (s == s) = true := by cases s <;> rfl
  rw [hw, hs]
  rfl

/-- Width- and signedness-parametric `evalBinOp .bitAnd` closed form. -/
theorem evalBinOp_bitAnd_eq (w : IntWidth) (s : Bool) (b₁ b₂ : BitVec 128)
    (h₁ : b₁.toNat < intWidthModulus w) (h₂ : b₂.toNat < intWidthModulus w) :
    evalBinOp .bitAnd (.scalar ⟨w, s, b₁⟩) (.scalar ⟨w, s, b₂⟩) =
      .ok (.scalar ⟨w, s, truncateBits w (BitVec.ofNat 128 (Nat.land b₁.toNat b₂.toNat))⟩) := by
  dsimp only [evalBinOp, bvAnd]
  rw [ite_bool_false (b := BinOp.bitAnd.isShift) rfl,
      ite_bool_false (same_scalar_guard_false w s),
      truncateBits_of_toNat_lt h₁, truncateBits_of_toNat_lt h₂]

/-- Width- and signedness-parametric `evalBinOp .bitOr` closed form. -/
theorem evalBinOp_bitOr_eq (w : IntWidth) (s : Bool) (b₁ b₂ : BitVec 128)
    (h₁ : b₁.toNat < intWidthModulus w) (h₂ : b₂.toNat < intWidthModulus w) :
    evalBinOp .bitOr (.scalar ⟨w, s, b₁⟩) (.scalar ⟨w, s, b₂⟩) =
      .ok (.scalar ⟨w, s, truncateBits w (BitVec.ofNat 128 (Nat.lor b₁.toNat b₂.toNat))⟩) := by
  dsimp only [evalBinOp, bvOr]
  rw [ite_bool_false (b := BinOp.bitOr.isShift) rfl,
      ite_bool_false (same_scalar_guard_false w s),
      truncateBits_of_toNat_lt h₁, truncateBits_of_toNat_lt h₂]

/-- Width- and signedness-parametric `evalBinOp .bitXor` closed form. -/
theorem evalBinOp_bitXor_eq (w : IntWidth) (s : Bool) (b₁ b₂ : BitVec 128)
    (h₁ : b₁.toNat < intWidthModulus w) (h₂ : b₂.toNat < intWidthModulus w) :
    evalBinOp .bitXor (.scalar ⟨w, s, b₁⟩) (.scalar ⟨w, s, b₂⟩) =
      .ok (.scalar ⟨w, s, truncateBits w (BitVec.ofNat 128 (Nat.xor b₁.toNat b₂.toNat))⟩) := by
  dsimp only [evalBinOp, bvXor]
  rw [ite_bool_false (b := BinOp.bitXor.isShift) rfl,
      ite_bool_false (same_scalar_guard_false w s),
      truncateBits_of_toNat_lt h₁, truncateBits_of_toNat_lt h₂]

/-- Width-parametric unsigned wrapping `.shl` closed form (eliminating the
`zetaHave` / `let` trap in `evalShiftOp`). -/
theorem evalBinOp_shl_unsigned_eq (w rw_ : IntWidth) {b₁ b₂ : BitVec 128}
    (h₁ : b₁.toNat < intWidthModulus w) (h₂ : b₂.toNat < intWidthModulus rw_) :
    evalBinOp .shl (.scalar ⟨w, false, b₁⟩) (.scalar ⟨rw_, false, b₂⟩) =
      .ok (.scalar ⟨w, false,
        BitVec.ofNat 128
          (Nat.mod (Nat.shiftLeft b₁.toNat (Nat.mod b₂.toNat w.bitWidth))
            (intWidthModulus w))⟩) := by
  dsimp only [evalBinOp]
  rw [ite_bool_true (b := BinOp.shl.isShift) rfl,
      decodeScalar_unsigned_of_lt h₁, decodeScalar_unsigned_of_lt h₂]
  dsimp only [evalShiftOp, intShiftLeft]
  rw [intEmod_ofNat]
  change (match truncateScalar w false
      (Int.ofNat (Nat.shiftLeft b₁.toNat (Nat.mod b₂.toNat w.bitWidth))) with
    | Except.error k => Except.error k
    | Except.ok (res, _) =>
      if (Int.ofNat (Nat.mod b₂.toNat w.bitWidth) != Int.ofNat b₂.toNat) && false then
        Except.error FaultKind.undefined
      else Except.ok (Val.scalar res)) = _
  rw [truncateScalar_unsigned_eq]
  dsimp only
  rw [ite_bool_false (Bool.and_false _)]
  apply congrArg Except.ok
  apply congrArg (fun bv => Val.scalar ⟨w, false, bv⟩)
  apply bitVec_eq_of_toNat_eq
  rw [truncateBits_bvOfInt_ofNat_toNat]
  have hResLt :
      Nat.mod (Nat.shiftLeft b₁.toNat (Nat.mod b₂.toNat w.bitWidth)) (intWidthModulus w) <
        Nat.pow 2 128 :=
    Nat.lt_of_lt_of_le (Nat.mod_lt _ (intWidth_modulus_pos w))
      (intWidthModulus_le_pow_128 w)
  change _ = Nat.mod _ (Nat.pow 2 128)
  rw [nat_mod_eq_of_lt hResLt]

/-- Width-parametric unsigned wrapping `.shr` closed form (eliminating the
`zetaHave` / `let` trap in `evalShiftOp`). -/
theorem evalBinOp_shr_unsigned_eq (w rw_ : IntWidth) {b₁ b₂ : BitVec 128}
    (h₁ : b₁.toNat < intWidthModulus w) (h₂ : b₂.toNat < intWidthModulus rw_) :
    evalBinOp .shr (.scalar ⟨w, false, b₁⟩) (.scalar ⟨rw_, false, b₂⟩) =
      .ok (.scalar ⟨w, false,
        BitVec.ofNat 128
          (Nat.shiftRight b₁.toNat (Nat.mod b₂.toNat w.bitWidth))⟩) := by
  dsimp only [evalBinOp]
  rw [ite_bool_true (b := BinOp.shr.isShift) rfl,
      decodeScalar_unsigned_of_lt h₁, decodeScalar_unsigned_of_lt h₂]
  dsimp only [evalShiftOp, intShiftRight]
  rw [intEmod_ofNat]
  change (match truncateScalar w false
      (Int.ofNat (Nat.shiftRight b₁.toNat (Nat.mod b₂.toNat w.bitWidth))) with
    | Except.error k => Except.error k
    | Except.ok (res, _) =>
      if (Int.ofNat (Nat.mod b₂.toNat w.bitWidth) != Int.ofNat b₂.toNat) && false then
        Except.error FaultKind.undefined
      else Except.ok (Val.scalar res)) = _
  rw [truncateScalar_unsigned_eq]
  dsimp only
  rw [ite_bool_false (Bool.and_false _)]
  apply congrArg Except.ok
  apply congrArg (fun bv => Val.scalar ⟨w, false, bv⟩)
  apply bitVec_eq_of_toNat_eq
  rw [truncateBits_bvOfInt_ofNat_toNat]
  have hLt : Nat.shiftRight b₁.toNat (Nat.mod b₂.toNat w.bitWidth) < intWidthModulus w :=
    Nat.lt_of_le_of_lt (Nat.shiftRight_le _ _) h₁
  have h128 : Nat.shiftRight b₁.toNat (Nat.mod b₂.toNat w.bitWidth) < Nat.pow 2 128 :=
    Nat.lt_of_lt_of_le hLt (intWidthModulus_le_pow_128 w)
  rw [nat_mod_eq_of_lt hLt]
  change _ = Nat.mod _ (Nat.pow 2 128)
  rw [nat_mod_eq_of_lt h128]

/-- Width-parametric unsigned wrapping `.add` closed form across all six widths
(including `u128` and `usize`). -/
theorem evalBinOp_add_unsigned_eq (w : IntWidth) {b₁ b₂ : BitVec 128}
    (h₁ : b₁.toNat < intWidthModulus w) (h₂ : b₂.toNat < intWidthModulus w) :
    evalBinOp .add (.scalar ⟨w, false, b₁⟩) (.scalar ⟨w, false, b₂⟩) =
      .ok (.scalar ⟨w, false,
        BitVec.ofNat 128 (Nat.mod (b₁.toNat + b₂.toNat) (intWidthModulus w))⟩) := by
  dsimp only [evalBinOp]
  rw [ite_bool_false (b := BinOp.add.isShift) rfl,
      ite_bool_false (same_scalar_guard_false w false),
      decodeScalar_unsigned_of_lt h₁, decodeScalar_unsigned_of_lt h₂]
  dsimp only [evalArithOp]
  have hSum : Int.ofNat b₁.toNat + Int.ofNat b₂.toNat = Int.ofNat (b₁.toNat + b₂.toNat) := rfl
  rw [ite_bool_false (b := (false && _)) rfl,
      ite_bool_false (b := (false && false && _)) rfl,
      hSum, truncateScalar_unsigned_eq]
  dsimp only
  rw [ite_bool_false (b := (_ && BinOp.add.isUnchecked)) (Bool.and_false _),
      ite_bool_false (b := BinOp.add.isOverflowing) rfl]
  apply congrArg Except.ok
  apply congrArg (fun bv => Val.scalar ⟨w, false, bv⟩)
  apply bitVec_eq_of_toNat_eq
  rw [truncateBits_bvOfInt_ofNat_toNat]
  have h128 : Nat.mod (b₁.toNat + b₂.toNat) (intWidthModulus w) < Nat.pow 2 128 :=
    Nat.lt_of_lt_of_le (Nat.mod_lt _ (intWidth_modulus_pos w))
      (intWidthModulus_le_pow_128 w)
  change _ = Nat.mod _ (Nat.pow 2 128)
  rw [nat_mod_eq_of_lt h128]

/-- Width-parametric scalar comparison closed forms (`eq`, `ne`, `lt`, `le`,
`gt`, `ge`) across all widths and signedness modes. -/
theorem evalBinOp_cmp_eq (w : IntWidth) (s : Bool) (b₁ b₂ : BitVec 128) :
    evalBinOp .eq (.scalar ⟨w, s, b₁⟩) (.scalar ⟨w, s, b₂⟩) =
      .ok (.bool (decodeScalar ⟨w, s, b₁⟩ == decodeScalar ⟨w, s, b₂⟩)) ∧
    evalBinOp .ne (.scalar ⟨w, s, b₁⟩) (.scalar ⟨w, s, b₂⟩) =
      .ok (.bool (decodeScalar ⟨w, s, b₁⟩ != decodeScalar ⟨w, s, b₂⟩)) ∧
    evalBinOp .lt (.scalar ⟨w, s, b₁⟩) (.scalar ⟨w, s, b₂⟩) =
      .ok (.bool (decide (decodeScalar ⟨w, s, b₁⟩ < decodeScalar ⟨w, s, b₂⟩))) ∧
    evalBinOp .le (.scalar ⟨w, s, b₁⟩) (.scalar ⟨w, s, b₂⟩) =
      .ok (.bool (decide (decodeScalar ⟨w, s, b₁⟩ ≤ decodeScalar ⟨w, s, b₂⟩))) ∧
    evalBinOp .gt (.scalar ⟨w, s, b₁⟩) (.scalar ⟨w, s, b₂⟩) =
      .ok (.bool (decide (decodeScalar ⟨w, s, b₁⟩ > decodeScalar ⟨w, s, b₂⟩))) ∧
    evalBinOp .ge (.scalar ⟨w, s, b₁⟩) (.scalar ⟨w, s, b₂⟩) =
      .ok (.bool (decide (decodeScalar ⟨w, s, b₁⟩ ≥ decodeScalar ⟨w, s, b₂⟩))) := by
  have hG := same_scalar_guard_false w s
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · dsimp only [evalBinOp]; rw [ite_bool_false (b := BinOp.eq.isShift) rfl, ite_bool_false hG]
  · dsimp only [evalBinOp]; rw [ite_bool_false (b := BinOp.ne.isShift) rfl, ite_bool_false hG]
  · dsimp only [evalBinOp]; rw [ite_bool_false (b := BinOp.lt.isShift) rfl, ite_bool_false hG]
  · dsimp only [evalBinOp]; rw [ite_bool_false (b := BinOp.le.isShift) rfl, ite_bool_false hG]
  · dsimp only [evalBinOp]; rw [ite_bool_false (b := BinOp.gt.isShift) rfl, ite_bool_false hG]
  · dsimp only [evalBinOp]; rw [ite_bool_false (b := BinOp.ge.isShift) rfl, ite_bool_false hG]

end Anneal.MirWp

end
