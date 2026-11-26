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
public import Init.Data.Nat.Div.Basic
public import Init.Data.Nat.Bitwise.Basic
public import Init.Data.Int.Basic
public import Init.Data.BitVec.BasicAux
public import Anneal.LinearArith
public import Anneal.NatBitwise
public import Anneal.Float.SoftFloat

public section

/-!
# IEEE-754 Rust `as` & Intrinsic Casts (`IeeeCast`)

Pass-1-pure (`0` TCB LOC, `0` `._unsafe_rec`, `0` `Classical.choice`,
axioms `⊆ [propext, Quot.sound]`) mechanization of all three Rust MIR
floating-point cast families (`CastKind.floatToInt`, `CastKind.intToFloat`,
`CastKind.floatToFloat`) plus `core::intrinsics::float_to_int_unchecked`:

1. **`FloatToInt` (`evalFloatToIntSaturating` & `evalFloatToIntChecked`):**
   - Safe Rust `as`: `NaN ↦ 0`, `+∞ ↦ MAX`, `-∞ ↦ MIN`, finite values truncate
     toward zero (`truncRatio`) and clamp into `[minValue, maxValue]`, encoded
     in canonical `w`-bit two's complement (`encodeTwosComplement`).
   - Unchecked intrinsic (`float_to_int_unchecked`): returns `none` on `NaN`,
     `±∞`, or truncated integer outside `[minValue, maxValue]`, and agrees
     identically with `evalFloatToIntSaturating` whenever `some` is returned
     (`evalFloatToIntChecked_some_agrees_saturating`).
2. **`IntToFloat` (`evalIntToFloatRoundTiesToEven` & generic
   `evalIntToFloat`):**
   - Rounds signed (`i8..i128`, `isize`) and unsigned (`u8..u128`, `usize`)
     integers to `f32`/`f64` via `roundRatioBits`, including the
     `tiesAwayFromZero` contrast model (`9007199254740993_i64 as f64`).
3. **`FloatToFloat` (`evalFloatToFloatRoundTiesToEven` & `convertFloatBits`):**
   - Computes the deterministic base `f32 ↔ f64` conversion matching
     `Miri.Interpreter.FloatBits.convert`, preserving signed zeros and
     infinities, rounding finite values (`f32 → f64` exact), and
     quieting/shifting NaN payloads (`convertFloatBits_nan_isQuietNaNBits`,
     never collapsing narrowed SNaNs to `±∞`). Full RFC 3514 nondeterministic
     NaN adjustment (`adjustNaN`) is layered on top by `EvalFloatToFloatRel` in
     `Anneal.Float.IeeeArith`.
-/

namespace Anneal.Float

open Anneal.LinearArith

/-! ## Part I: Integer Cast Targets & Two's-Complement Codec -/

/-- Integer widths supported by `FloatToInt` / `IntToFloat`. -/
inductive FloatIntWidth : Type where
  | i8 : FloatIntWidth
  | i16 : FloatIntWidth
  | i32 : FloatIntWidth
  | i64 : FloatIntWidth
  | i128 : FloatIntWidth
  | isize : FloatIntWidth

/-- Target pointer width (`32`-bit vs `64`-bit `isize`/`usize`). -/
inductive FloatPtrWidth : Type where
  | bits32 : FloatPtrWidth
  | bits64 : FloatPtrWidth

/-- Bit width of `FloatPtrWidth`. -/
@[expose] def FloatPtrWidth.bits : FloatPtrWidth → Nat
  | .bits32 => 32
  | .bits64 => 64

/-- Target integer descriptor (`width` and `signed`). -/
structure FloatIntTarget : Type where
  width : FloatIntWidth
  signed : Bool

/-- Bit width of a `FloatIntTarget` (`8`, `16`, `32`, `64`, or `128`). -/
@[expose] def FloatIntTarget.bitWidth (pw : FloatPtrWidth) (t : FloatIntTarget) : Nat :=
  match t.width with
  | .i8 => 8
  | .i16 => 16
  | .i32 => 32
  | .i64 => 64
  | .i128 => 128
  | .isize => pw.bits

/-- Byte width of a `FloatIntTarget` (`1`, `2`, `4`, `8`, or `16`). -/
@[expose] def FloatIntTarget.byteWidth (pw : FloatPtrWidth) (t : FloatIntTarget) : Nat :=
  Nat.div (t.bitWidth pw) 8

/-- Minimum representable integer (`-2^(w-1)` signed, `0` unsigned). -/
@[expose] def FloatIntTarget.minValue (pw : FloatPtrWidth) (t : FloatIntTarget) : Int :=
  if t.signed then Int.neg (Int.ofNat (pow2 (t.bitWidth pw - 1))) else Int.ofNat 0

/-- Maximum representable integer (`2^(w-1) - 1` signed, `2^w - 1` unsigned). -/
@[expose] def FloatIntTarget.maxValue (pw : FloatPtrWidth) (t : FloatIntTarget) : Int :=
  if t.signed then
    Int.sub (Int.ofNat (pow2 (t.bitWidth pw - 1))) (Int.ofNat 1)
  else
    Int.sub (Int.ofNat (pow2 (t.bitWidth pw))) (Int.ofNat 1)

/-- Canonical scalar integer output (`bits < 2^(8 * byteWidth)`). -/
structure FloatScalarInt : Type where
  bits : Nat
  byteWidth : Nat

/-- Clamp `v` into `[lo, hi]`. -/
@[expose] def clampInt (lo hi v : Int) : Int :=
  intMax lo (intMin hi v)

/-- Truncation toward zero of `(-1)^neg * (n / d)`. -/
@[expose] def truncRatio (neg : Bool) (n d : Nat) : Int :=
  let q := Nat.div n d
  if neg then Int.neg (Int.ofNat q) else Int.ofNat q

/-- Mathematical integer produced by Rust's saturating `as` float-to-int
cast. -/
@[expose] def floatToIntValue (k : FloatKind) (lo hi : Int) : Int :=
  match k with
  | .nan _ _ _ => Int.ofNat 0
  | .inf neg => if neg then lo else hi
  | .zero _ => Int.ofNat 0
  | .finite neg n d => clampInt lo hi (truncRatio neg n d)

/-- Canonical `w`-bit two's-complement bit pattern of `v : Int`, matching
`Trusted.MirSemantics.bvOfInt`. -/
@[expose] def encodeTwosComplement (w : Nat) (v : Int) : Nat :=
  let m := pow2 w
  match v with
  | .ofNat n => Nat.mod n m
  | .negSucc n => m - (Nat.mod n m + 1)

/-- Rust `as` saturating float-to-int cast (`CastKind.floatToInt`). -/
@[expose] def evalFloatToIntSaturating (src : IeeeFormat) (bits : Nat)
    (target : FloatIntTarget) (pw : FloatPtrWidth) : FloatScalarInt :=
  let w := target.bitWidth pw
  let val := floatToIntValue (decodeBits src (Nat.mod bits (pow2 src.width)))
    (target.minValue pw) (target.maxValue pw)
  ⟨encodeTwosComplement w val, target.byteWidth pw⟩

/-- Checked float-to-int intrinsic (`core::intrinsics::float_to_int_unchecked`):
returns `none` (UB) on `NaN`, `±∞`, or truncated value outside
`[target.minValue pw, target.maxValue pw]`. -/
@[expose] def evalFloatToIntChecked (src : IeeeFormat) (bits : Nat)
    (target : FloatIntTarget) (pw : FloatPtrWidth) : Option Int :=
  match decodeBits src (Nat.mod bits (pow2 src.width)) with
  | .nan _ _ _ => none
  | .inf _ => none
  | .zero _ => some (Int.ofNat 0)
  | .finite neg n d =>
    let tr := truncRatio neg n d
    let lo := target.minValue pw
    let hi := target.maxValue pw
    match intLeB lo tr && intLeB tr hi with
    | true => some tr
    | false => none

/-! ## Part II: `IntToFloat` & `FloatToFloat` Casts -/

/-- Mathematical integer value of a `w`-bit signed or unsigned bit pattern. -/
@[expose] def intValueOfBits (signed : Bool) (w bits : Nat) : Int :=
  let b := Nat.mod bits (pow2 w)
  match signed && Nat.ble (pow2 (w - 1)) b with
  | true => Int.sub (Int.ofNat b) (Int.ofNat (pow2 w))
  | false => Int.ofNat b

/-- Generic-mode integer-to-float cast (`CastKind.intToFloat`). -/
@[expose] def evalIntToFloat (mode : RoundingMode) (signed : Bool)
    (w bits : Nat) (dst : IeeeFormat) : Nat :=
  let v := intValueOfBits signed w bits
  roundRatioBits mode dst (intLtB v (Int.ofNat 0)) (Int.natAbs v) 1

/-- Rust `as` integer-to-float cast (`roundTiesToEven`). -/
@[expose] def evalIntToFloatRoundTiesToEven (signed : Bool) (w bits : Nat)
    (dst : IeeeFormat) : Nat :=
  evalIntToFloat .tiesToEven signed w bits dst

/-- Deterministic base float-to-float conversion (`CastKind.floatToFloat` prior
to RFC 3514 `adjustNaN`), matching `Miri.Interpreter.FloatBits.convert` and
`rustc_apfloat` quieting NaN shift. See `EvalFloatToFloatRel` in
`Anneal.Float.IeeeArith` for the relational NaN-choice cast specification. -/
@[expose] def convertFloatBits (mode : RoundingMode) (src dst : IeeeFormat)
    (bits : Nat) : Nat :=
  match decodeBits src (Nat.mod bits (pow2 src.width)) with
  | .zero neg => zeroBits dst neg
  | .finite neg n d => roundRatioBits mode dst neg n d
  | .inf neg => infBits dst neg
  | .nan neg _ payload =>
    let quiet := Nat.lor payload src.quietBitMask
    let shifted :=
      match Nat.ble src.fractionBits dst.fractionBits with
      | true => quiet * pow2 (dst.fractionBits - src.fractionBits)
      | false => Nat.div quiet (pow2 (src.fractionBits - dst.fractionBits))
    encodeBits dst neg dst.allOnesExp (Nat.lor shifted dst.quietBitMask)

/-- Deterministic `roundTiesToEven` base float-to-float conversion
(`Miri.Interpreter.FloatBits.convert`; paired with `nanChoices` in
`EvalFloatToFloatRel` for RFC 3514 NaN nondeterminism). -/
@[expose] def evalFloatToFloatRoundTiesToEven (src dst : IeeeFormat)
    (bits : Nat) : Nat :=
  convertFloatBits .tiesToEven src dst bits

/-- Base `BitVec 32 → BitVec 64` widening conversion (quieting NaN payload
shift; see `EvalFloatToFloatRel` for RFC 3514 NaN sign/payload choice). -/
@[expose] def f32ToF64 (x : F32Bits) : F64Bits :=
  BitVec.ofNat 64 (evalFloatToFloatRoundTiesToEven .binary32 .binary64 x.toNat)

/-- Base `BitVec 64 → BitVec 32` narrowing conversion (quieting NaN payload
shift; see `EvalFloatToFloatRel` for RFC 3514 NaN sign/payload choice). -/
@[expose] def f64ToF32 (x : F64Bits) : F32Bits :=
  BitVec.ofNat 32 (evalFloatToFloatRoundTiesToEven .binary64 .binary32 x.toNat)

/-! ## Part III: Soundness, Width, Saturation, & NaN Quieting Theorems -/

/-- `encodeTwosComplement w v < 2^w` for every `w` and `v` (`[propext]`
only). -/
theorem encodeTwosComplement_lt (w : Nat) (v : Int) :
    encodeTwosComplement w v < pow2 w := by
  dsimp only [encodeTwosComplement]
  have hPos : 0 < pow2 w := pow2_pos w
  cases v with
  | ofNat n => exact Nat.mod_lt n hPos
  | negSucc n =>
    exact Nat.sub_lt hPos (Nat.zero_lt_succ (Nat.mod n (pow2 w)))

/-- `evalFloatToIntSaturating` always produces an in-width bit pattern
(`[propext]` only). -/
theorem evalFloatToIntSaturating_bits_lt (src : IeeeFormat) (bits : Nat)
    (target : FloatIntTarget) (pw : FloatPtrWidth) :
    (evalFloatToIntSaturating src bits target pw).bits <
      pow2 (target.bitWidth pw) :=
  encodeTwosComplement_lt _ _

/-- `clampInt lo hi v` lies in `[lo, hi]` whenever `lo ≤ hi` (`[propext]`). -/
theorem clampInt_bounds {lo hi v : Int} (hLoHi : lo ≤ hi) :
    lo ≤ clampInt lo hi v ∧ clampInt lo hi v ≤ hi := by
  dsimp only [clampInt, intMax, intMin]
  cases hHV : intLeB hi v with
  | true =>
    have hLoLeHi : intLeB lo hi = true := (intLeB_iff_le lo hi).mpr hLoHi
    rw [hLoLeHi]
    exact ⟨hLoHi, (intBalance_le (intBalance_self hi) (intBalance_self hi)).mpr (Nat.le_refl _)⟩
  | false =>
    have hVLeHi : v ≤ hi := le_of_intLeB_false hHV
    cases hLV : intLeB lo v with
    | true =>
      exact ⟨(intLeB_iff_le lo v).mp hLV, hVLeHi⟩
    | false =>
      exact ⟨(intBalance_le (intBalance_self lo) (intBalance_self lo)).mpr (Nat.le_refl _), hLoHi⟩

/-- Every NaN bit pattern maps to `0` under `evalFloatToIntSaturating`
(`[propext]`). -/
theorem evalFloatToIntSaturating_of_isNaN (src : IeeeFormat) {bits : Nat}
    (target : FloatIntTarget) (pw : FloatPtrWidth)
    (hNaN : isNaNBits src (Nat.mod bits (pow2 src.width)) = true) :
    (evalFloatToIntSaturating src bits target pw).bits = 0 := by
  dsimp only [evalFloatToIntSaturating, floatToIntValue]
  dsimp only [isNaNBits] at hNaN
  cases hDec : decodeBits src (Nat.mod bits (pow2 src.width)) with
  | nan _ _ _ =>
    dsimp only [encodeTwosComplement]
    exact Nat.zero_mod _
  | zero _ => rw [hDec] at hNaN; exact Bool.noConfusion hNaN
  | finite _ _ _ => rw [hDec] at hNaN; exact Bool.noConfusion hNaN
  | inf _ => rw [hDec] at hNaN; exact Bool.noConfusion hNaN

/-- Both `+0.0` and `-0.0` map to `0` under `evalFloatToIntSaturating`
(`[propext]` only). -/
theorem evalFloatToIntSaturating_zeroBits (src : IeeeFormat) (neg : Bool)
    (target : FloatIntTarget) (pw : FloatPtrWidth) :
    (evalFloatToIntSaturating src (zeroBits src neg) target pw).bits = 0 := by
  have hMod : Nat.mod (zeroBits src neg) (pow2 src.width) = zeroBits src neg :=
    Nat.mod_eq_of_lt (zeroBits_lt src neg)
  dsimp only [evalFloatToIntSaturating]
  rw [hMod]
  cases src <;> cases neg <;> exact Nat.zero_mod _

/-- `+∞` saturates to `target.maxValue pw` and `-∞` saturates to
`target.minValue pw` (`[propext]` only). -/
theorem evalFloatToIntSaturating_infBits (src : IeeeFormat) (neg : Bool)
    (target : FloatIntTarget) (pw : FloatPtrWidth) :
    (evalFloatToIntSaturating src (infBits src neg) target pw).bits =
      encodeTwosComplement (target.bitWidth pw)
        (if neg then target.minValue pw else target.maxValue pw) := by
  have hMod : Nat.mod (infBits src neg) (pow2 src.width) = infBits src neg :=
    Nat.mod_eq_of_lt (infBits_lt src neg)
  dsimp only [evalFloatToIntSaturating]
  rw [hMod]
  cases src <;> cases neg <;> rfl

/-- Whenever `evalFloatToIntChecked` returns `some v`, `float_to_int_unchecked`
is UB-free and produces the exact same scalar as safe `as`
`evalFloatToIntSaturating` (`[propext]` only). -/
theorem evalFloatToIntChecked_some_agrees_saturating (src : IeeeFormat)
    (bits : Nat) (target : FloatIntTarget) (pw : FloatPtrWidth) {v : Int}
    (hOk : evalFloatToIntChecked src bits target pw = some v) :
    evalFloatToIntSaturating src bits target pw =
      ⟨encodeTwosComplement (target.bitWidth pw) v, target.byteWidth pw⟩ := by
  dsimp only [evalFloatToIntChecked] at hOk
  dsimp only [evalFloatToIntSaturating, floatToIntValue]
  cases hDec : decodeBits src (Nat.mod bits (pow2 src.width)) with
  | nan _ _ _ => rw [hDec] at hOk; nomatch hOk
  | inf _ => rw [hDec] at hOk; nomatch hOk
  | zero _ =>
    rw [hDec] at hOk
    injection hOk with hV
    subst hV
    rfl
  | finite neg n d =>
    rw [hDec] at hOk
    dsimp only at hOk
    cases hRange :
        intLeB (target.minValue pw) (truncRatio neg n d) &&
          intLeB (truncRatio neg n d) (target.maxValue pw) with
    | false =>
      rw [hRange] at hOk
      nomatch hOk
    | true =>
      rw [hRange] at hOk
      injection hOk with hV
      subst hV
      have hL : intLeB (target.minValue pw) (truncRatio neg n d) = true :=
        Anneal.InitLemmas.bool_and_left hRange
      have hR : intLeB (truncRatio neg n d) (target.maxValue pw) = true :=
        Anneal.InitLemmas.bool_and_right hRange
      dsimp only [clampInt, intMax, intMin]
      cases hHiLe : intLeB (target.maxValue pw) (truncRatio neg n d) with
      | false =>
        rw [hL]
      | true =>
        have hGe := (intLeB_iff_le _ _).mp hHiLe
        have hLe := (intLeB_iff_le _ _).mp hR
        have hEq : target.maxValue pw = truncRatio neg n d := by
          have h1 := (intBalance_le (intBalance_self _) (intBalance_self _)).mp hGe
          have h2 := (intBalance_le (intBalance_self _) (intBalance_self _)).mp hLe
          have hNatEq := Nat.le_antisymm h1 h2
          cases hA : target.maxValue pw with
          | ofNat a =>
            cases hB : truncRatio neg n d with
            | ofNat b =>
              rw [hA, hB] at hNatEq
              dsimp only [intPos, intNeg] at hNatEq
              rw [Nat.add_zero, Nat.add_zero] at hNatEq
              exact congrArg Int.ofNat hNatEq
            | negSucc b =>
              rw [hA, hB] at hNatEq
              dsimp only [intPos, intNeg] at hNatEq
              rw [Nat.zero_add, Nat.add_zero] at hNatEq
              exact nomatch hNatEq
          | negSucc a =>
            cases hB : truncRatio neg n d with
            | ofNat b =>
              rw [hA, hB] at hNatEq
              dsimp only [intPos, intNeg] at hNatEq
              rw [Nat.zero_add, Nat.add_zero] at hNatEq
              exact nomatch hNatEq.symm
            | negSucc b =>
              rw [hA, hB] at hNatEq
              dsimp only [intPos, intNeg] at hNatEq
              rw [Nat.zero_add, Nat.zero_add] at hNatEq
              exact congrArg Int.negSucc (Nat.succ.inj hNatEq.symm)
        rw [hEq, hL]

/-- `evalIntToFloat` always fits in `dst.width` bits (`[propext]` only). -/
theorem evalIntToFloat_lt (mode : RoundingMode) (signed : Bool)
    (w bits : Nat) (dst : IeeeFormat) :
    evalIntToFloat mode signed w bits dst < pow2 dst.width :=
  roundRatioBits_lt mode dst _ _ 1

private theorem nat_zero_mod_ic (b : Nat) : Nat.mod 0 b = 0 :=
  Nat.zero_mod b

private theorem nat_mod_eq_of_lt_ic {a b : Nat} (h : a < b) :
    Nat.mod a b = a :=
  Nat.mod_eq_of_lt h

private theorem ite_true_ic {α : Type} {p : Prop} [hdec : Decidable p]
    (hp : p) (a b : α) : (if p then a else b) = a := by
  cases hdec with
  | isTrue _ => rfl
  | isFalse hnp => exact False.elim (hnp hp)

private theorem ite_false_ic {α : Type} {p : Prop} [hdec : Decidable p]
    (hnp : ¬ p) (a b : α) : (if p then a else b) = b := by
  cases hdec with
  | isTrue hp => exact False.elim (hnp hp)
  | isFalse _ => rfl

/-- `0` casts to `+0.0` (`0`) for every signed/unsigned integer width
(`[propext]` only). -/
theorem evalIntToFloatRoundTiesToEven_zero (signed : Bool) (w : Nat)
    (dst : IeeeFormat) :
    evalIntToFloatRoundTiesToEven signed w 0 dst = zeroBits dst false := by
  dsimp only [evalIntToFloatRoundTiesToEven, evalIntToFloat, intValueOfBits]
  rw [nat_zero_mod_ic]
  have hBleFalse : Nat.ble (pow2 (w - 1)) 0 = false := by
    cases hP : pow2 (w - 1) with
    | zero => exact False.elim (Nat.ne_of_gt (pow2_pos (w - 1)) hP)
    | succ _ => rfl
  rw [hBleFalse]
  cases signed <;> rfl

private theorem quiet_shifted_lt (src dst : IeeeFormat) {payload : Nat}
    (hPay : payload < pow2 src.fractionBits) :
    let quiet := Nat.lor payload src.quietBitMask
    let shifted :=
      match Nat.ble src.fractionBits dst.fractionBits with
      | true => quiet * pow2 (dst.fractionBits - src.fractionBits)
      | false => Nat.div quiet (pow2 (src.fractionBits - dst.fractionBits))
    Nat.lor shifted dst.quietBitMask < pow2 dst.fractionBits := by
  have hMaskSrc : src.quietBitMask < pow2 src.fractionBits := by
    cases src <;> decide
  have hMaskDst : dst.quietBitMask < pow2 dst.fractionBits := by
    cases dst <;> decide
  have hQuietLt : Nat.lor payload src.quietBitMask < pow2 src.fractionBits := by
    rw [pow2_eq_natPow src.fractionBits]
    rw [pow2_eq_natPow src.fractionBits] at hPay hMaskSrc
    exact Anneal.NatBitwise.lor_lt_two_pow hPay hMaskSrc
  dsimp only
  rw [pow2_eq_natPow dst.fractionBits]
  rw [pow2_eq_natPow dst.fractionBits] at hMaskDst
  apply Anneal.NatBitwise.lor_lt_two_pow _ hMaskDst
  rw [← pow2_eq_natPow dst.fractionBits]
  cases src with
  | binary32 =>
    cases dst with
    | binary32 =>
      dsimp only [IeeeFormat.fractionBits] at hQuietLt
      change Nat.lor payload IeeeFormat.binary32.quietBitMask * 1 < pow2 23
      rw [Nat.mul_one]
      exact hQuietLt
    | binary64 =>
      dsimp only [IeeeFormat.fractionBits] at hQuietLt
      change Nat.lor payload IeeeFormat.binary32.quietBitMask * pow2 29 < pow2 52
      have hEq : pow2 52 = pow2 23 * pow2 29 := pow2_add 23 29
      rw [hEq]
      exact Nat.mul_lt_mul_of_pos_right hQuietLt (pow2_pos 29)
  | binary64 =>
    cases dst with
    | binary32 =>
      dsimp only [IeeeFormat.fractionBits] at hQuietLt
      dsimp only [IeeeFormat.fractionBits]
      apply (Nat.div_lt_iff_lt_mul (pow2_pos 29)).mpr
      change Nat.lor payload IeeeFormat.binary64.quietBitMask < pow2 23 * pow2 29
      have hEq : pow2 23 * pow2 29 = pow2 52 := (pow2_add 23 29).symm
      rw [hEq]
      exact hQuietLt
    | binary64 =>
      dsimp only [IeeeFormat.fractionBits] at hQuietLt
      change Nat.lor payload IeeeFormat.binary64.quietBitMask * 1 < pow2 52
      rw [Nat.mul_one]
      exact hQuietLt

/-- `convertFloatBits` always produces a valid `< 2^dst.width` bit pattern
(`[propext, Quot.sound]`, `0` `Classical.choice`). -/
theorem convertFloatBits_lt (mode : RoundingMode) (src dst : IeeeFormat)
    (bits : Nat) :
    convertFloatBits mode src dst bits < pow2 dst.width := by
  dsimp only [convertFloatBits]
  have hPay : (unpackBits src (Nat.mod bits (pow2 src.width))).fraction <
      pow2 src.fractionBits :=
    Nat.mod_lt _ (pow2_pos src.fractionBits)
  dsimp only [decodeBits]
  cases Nat.beq (unpackBits src (Nat.mod bits (pow2 src.width))).exponent
      src.allOnesExp with
  | true =>
    cases Nat.beq (unpackBits src (Nat.mod bits (pow2 src.width))).fraction 0 with
    | true => exact infBits_lt dst _
    | false =>
      have hAllLt : dst.allOnesExp < pow2 dst.exponentBits := by
        cases dst <;> decide
      exact encodeBits_lt dst _ hAllLt (quiet_shifted_lt src dst hPay)
  | false =>
    cases Nat.beq (unpackBits src (Nat.mod bits (pow2 src.width))).exponent 0 with
    | true =>
      cases Nat.beq (unpackBits src (Nat.mod bits (pow2 src.width))).fraction 0 with
      | true => exact zeroBits_lt dst _
      | false => exact roundRatioBits_lt mode dst _ _ _
    | false => exact roundRatioBits_lt mode dst _ _ _

/-- `evalFloatToFloatRoundTiesToEven` preserves signed zeros
(`[propext]` only). -/
theorem evalFloatToFloatRoundTiesToEven_zeroBits (src dst : IeeeFormat)
    (neg : Bool) :
    evalFloatToFloatRoundTiesToEven src dst (zeroBits src neg) =
      zeroBits dst neg := by
  dsimp only [evalFloatToFloatRoundTiesToEven, convertFloatBits]
  rw [nat_mod_eq_of_lt_ic (zeroBits_lt src neg)]
  cases src <;> cases dst <;> cases neg <;> rfl

/-- `evalFloatToFloatRoundTiesToEven` preserves signed infinities
(`[propext]` only). -/
theorem evalFloatToFloatRoundTiesToEven_infBits (src dst : IeeeFormat)
    (neg : Bool) :
    evalFloatToFloatRoundTiesToEven src dst (infBits src neg) =
      infBits dst neg := by
  dsimp only [evalFloatToFloatRoundTiesToEven, convertFloatBits]
  rw [nat_mod_eq_of_lt_ic (infBits_lt src neg)]
  cases src <;> cases dst <;> cases neg <;> rfl

private theorem pow2_le_lor_right : ∀ k x : Nat, pow2 k ≤ Nat.lor x (pow2 k)
  | 0, x => by
    rw [Anneal.NatBitwise.lor_eq_bitwise]
    change 1 ≤ Nat.bitwise Bool.or x 1
    rw [Anneal.NatBitwise.unfold_eq]
    cases x with
    | zero =>
      rw [ite_true_ic rfl]
      exact Nat.le_refl 1
    | succ x' =>
      rw [ite_false_ic (fun h => nomatch h), ite_false_ic (fun h => nomatch h)]
      dsimp only
      have hDec1 : decide (Nat.mod 1 2 = 1) = true := rfl
      rw [hDec1, Bool.or_true]
      exact Nat.succ_le_succ (Nat.zero_le _)
  | k + 1, x => by
    rw [Anneal.NatBitwise.lor_eq_bitwise, Anneal.NatBitwise.unfold_eq]
    cases x with
    | zero =>
      rw [ite_true_ic rfl]
      exact Nat.le_refl _
    | succ x' =>
      have hNe0 : pow2 (k + 1) ≠ 0 := Nat.ne_of_gt (pow2_pos (k + 1))
      rw [ite_false_ic (fun h => nomatch h), ite_false_ic hNe0]
      dsimp only
      have hDiv2 : Nat.div (pow2 (k + 1)) 2 = pow2 k := by
        rw [pow2_succ]
        exact Nat.mul_div_cancel (pow2 k) (by decide : 0 < 2)
      rw [hDiv2, ← Anneal.NatBitwise.lor_eq_bitwise]
      have ih := pow2_le_lor_right k (Nat.div (x' + 1) 2)
      have hSplit : pow2 (k + 1) = pow2 k + pow2 k := by
        rw [pow2_succ, Nat.mul_two]
      have hSumLe : pow2 (k + 1) ≤
          Nat.lor (Nat.div (x' + 1) 2) (pow2 k) +
            Nat.lor (Nat.div (x' + 1) 2) (pow2 k) := by
        rw [hSplit]
        exact Nat.add_le_add ih ih
      cases Bool.or (decide (Nat.mod (x' + 1) 2 = 1))
          (decide (Nat.mod (pow2 (k + 1)) 2 = 1)) with
      | false => exact hSumLe
      | true => exact Nat.le_trans hSumLe (Nat.le_succ _)

private theorem lor_quietBitMask_pos (dst : IeeeFormat) (x : Nat) :
    dst.quietBitMask ≤ Nat.lor x dst.quietBitMask :=
  pow2_le_lor_right (dst.fractionBits - 1) x

/-- Every NaN input (quiet or signaling, widening or narrowing) converts under
`convertFloatBits` to a quiet NaN (never `±∞` or a signaling NaN)
(`[propext, Quot.sound]`, `0` `Classical.choice`). -/
theorem convertFloatBits_nan_isQuietNaNBits (mode : RoundingMode)
    (src dst : IeeeFormat) {bits : Nat}
    (hNaN : isNaNBits src (Nat.mod bits (pow2 src.width)) = true) :
    isQuietNaNBits dst (convertFloatBits mode src dst bits) = true := by
  dsimp only [convertFloatBits]
  dsimp only [isNaNBits] at hNaN
  have hPay : (unpackBits src (Nat.mod bits (pow2 src.width))).fraction <
      pow2 src.fractionBits :=
    Nat.mod_lt _ (pow2_pos src.fractionBits)
  dsimp only [decodeBits] at hNaN
  dsimp only [decodeBits]
  cases hE : Nat.beq (unpackBits src (Nat.mod bits (pow2 src.width))).exponent
      src.allOnesExp with
  | false =>
    rw [hE] at hNaN
    dsimp only at hNaN
    cases hE0 : Nat.beq (unpackBits src (Nat.mod bits (pow2 src.width))).exponent 0 with
    | false =>
      rw [hE0] at hNaN
      exact Bool.noConfusion hNaN
    | true =>
      rw [hE0] at hNaN
      dsimp only at hNaN
      cases hF0 : Nat.beq (unpackBits src (Nat.mod bits (pow2 src.width))).fraction 0 with
      | true => rw [hF0] at hNaN; exact Bool.noConfusion hNaN
      | false => rw [hF0] at hNaN; exact Bool.noConfusion hNaN
  | true =>
    cases hF : Nat.beq (unpackBits src (Nat.mod bits (pow2 src.width))).fraction 0 with
    | true =>
      rw [hE, hF] at hNaN
      exact Bool.noConfusion hNaN
    | false =>
      dsimp only [isQuietNaNBits, decodeBits]
      have hAllLt : dst.allOnesExp < pow2 dst.exponentBits := by
        cases dst <;> decide
      have hOutFracLt := quiet_shifted_lt src dst hPay
      rw [unpackBits_encodeBits dst _ hAllLt hOutFracLt]
      dsimp only
      have hAllBeq : Nat.beq dst.allOnesExp dst.allOnesExp = true := by
        cases dst <;> decide
      rw [hAllBeq]
      dsimp only
      let outFrac := Nat.lor
        (match Nat.ble src.fractionBits dst.fractionBits with
         | true =>
           Nat.lor (unpackBits src (Nat.mod bits (pow2 src.width))).fraction
             src.quietBitMask * pow2 (dst.fractionBits - src.fractionBits)
         | false =>
           Nat.div
             (Nat.lor (unpackBits src (Nat.mod bits (pow2 src.width))).fraction
               src.quietBitMask)
             (pow2 (src.fractionBits - dst.fractionBits)))
        dst.quietBitMask
      have hGeMask : dst.quietBitMask ≤ outFrac :=
        lor_quietBitMask_pos dst _
      have hMaskPos : 0 < dst.quietBitMask := by
        cases dst <;> decide
      have hOutNeZero : Nat.beq outFrac 0 = false := by
        cases hO : outFrac with
        | zero =>
          rw [hO] at hGeMask
          exact False.elim (Nat.not_lt_of_ge hGeMask hMaskPos)
        | succ _ => rfl
      change (match (match Nat.beq outFrac 0 with
        | true => FloatKind.inf (unpackBits src (Nat.mod bits (pow2 src.width))).neg
        | false =>
          FloatKind.nan (unpackBits src (Nat.mod bits (pow2 src.width))).neg
            (Nat.beq (Nat.mod (Nat.div outFrac dst.quietBitMask) 2) 1)
            outFrac) with
        | .nan _ quiet _ => quiet
        | _ => false) = true
      rw [hOutNeZero]
      dsimp only
      have hDivGe1 : 1 ≤ Nat.div outFrac dst.quietBitMask :=
        nat_div_pos hGeMask hMaskPos
      have hDivLt2 : Nat.div outFrac dst.quietBitMask < 2 := by
        apply (Nat.div_lt_iff_lt_mul hMaskPos).mpr
        have hTwoMask : 2 * dst.quietBitMask = pow2 dst.fractionBits := by
          cases dst <;> decide
        rw [hTwoMask]
        exact hOutFracLt
      cases hDiv : Nat.div outFrac dst.quietBitMask with
      | zero =>
        rw [hDiv] at hDivGe1
        exact False.elim (Nat.not_succ_le_zero 0 hDivGe1)
      | succ k =>
        rw [hDiv] at hDivLt2
        have hk0 : k = 0 := Nat.eq_zero_of_le_zero
          (Nat.le_of_lt_succ (Nat.lt_of_succ_lt_succ hDivLt2))
        subst hk0
        rfl

end Anneal.Float

end
