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

end Anneal.MirWp

end
