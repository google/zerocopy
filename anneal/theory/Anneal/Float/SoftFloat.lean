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
public import Init.Data.List.Basic
public import Anneal.InitLemmas
public import Anneal.LinearArith
public import Anneal.NatBitwise

public section

/-!
# Pure-Integer IEEE-754 SoftFloat Representation & Rounding (`SoftFloat`)

Zero-TCB, Pass-1-pure (`prelude` + locked `Init.*` only, `0` `._unsafe_rec`,
`0` `noncomputable`, `0` `omega`, `0` `Classical.choice`, `0` `Quot.sound`)
mechanization of IEEE 754-2008 `binary32` (`f32`) and `binary64` (`f64`) bit
representations, NaN/Inf/subnormal/normal/zero classification, all five
IEEE-754 / Rust rounding modes, and exact rational `roundRatio` with gradual
subnormal underflow:

1. **Bit-Exact Interchange Formats (`IeeeFormat`, `F32Bits`, `F64Bits`):**
   - Preserves all sign, quiet/signaling, and NaN payload bits across pack and
     unpack in compliance with Rust RFC 3514 (`float_semantics`), avoiding
     Lean's NaN-erasing `Init.Data.Float`.
2. **13-Step Recursion-Free Floor Base-2 Logarithm (`natLog2`,
   `ratioExponent`):**
   - Evaluates `⌊log₂ q⌋` for `0 < q < 2^8192` in 13 flat C++ GMP shifts
     (`0` `@Nat.rec`, stack depth `< 20` vs `TrustedBoundary`'s
     `maxRecDepth = 512`), covering `f32`, `f64`, `i128`/`u128`, and 3-operand
     `f64` FMA subnormals, with `[propext]`-only correctness
     (`natLog2_bounds`) and uniqueness (`natLog2_unique`).
3. **IEEE-754 Classification & Miri `FloatBits.decode` Lockstep:**
   - `FloatKind` (`.zero`, `.finite`, `.inf`, `.nan`), `decodeBits`, boolean
     classifiers (`isZeroBits`, `isSubnormalBits`, `isNormalBits`,
     `isFiniteBits`, `isInfiniteBits`, `isNaNBits`, `isQuietNaNBits`,
     `isSignalingNaNBits`), and literal `miriDecode` equivalence
     (`decodeBits_eq_miriDecode`).
4. **Five-Mode Rational Rounding (`RoundingMode`, `roundRatioBits`,
   `roundRatioTiesToEven`):**
   - `.tiesToEven`, `.tiesAwayFromZero`, `.towardZero`, `.towardPosInf`, and
     `.towardNegInf`, proving width bounds (`roundRatioBits_lt`,
     `roundRatioTiesToEven_lt`), signed-zero preservation
     (`roundRatioBits_zero`), and pack/unpack bijections
     (`unpackBits_encodeBits`, `encodeBits_unpackBits`).
-/

namespace Anneal.Float

open Anneal.LinearArith

/-! ## Part I: Constructive Power-of-Two, `Int` Order, & 13-Step `natLog2` -/

/-- Exact power of two `2^n` factored into `128`-bit chunks
(`(2^128)^(n/128) * 2^(n%128)`) so Lean's kernel and elaborator reduce `pow2 n`
via C++ GMP `reduce_nat` for all `n < 32768` without hitting
`exponentiation.threshold = 256` or `maxRecDepth = 512` (`0` `._unsafe_rec`). -/
@[expose] def pow2 (n : Nat) : Nat :=
  match Nat.blt n 128 with
  | true => Nat.pow 2 n
  | false => Nat.pow (Nat.pow 2 128) (Nat.div n 128) * Nat.pow 2 (Nat.mod n 128)

private theorem natPow_add_sf (a m : Nat) :
    ∀ k : Nat, Nat.pow a (m + k) = Nat.pow a m * Nat.pow a k
  | 0 => by
    rw [Nat.add_zero]
    exact (Nat.mul_one _).symm
  | k + 1 => by
    have ih := natPow_add_sf a m k
    change Nat.pow a (m + k) * a = Nat.pow a m * (Nat.pow a k * a)
    rw [ih, Nat.mul_assoc]

private theorem natPow_mul_sf (a m : Nat) :
    ∀ k : Nat, Nat.pow (Nat.pow a m) k = Nat.pow a (m * k)
  | 0 => rfl
  | k + 1 => by
    have ih := natPow_mul_sf a m k
    change Nat.pow (Nat.pow a m) k * Nat.pow a m = Nat.pow a (m * k + m)
    rw [ih, natPow_add_sf]

/-- Equivalence of chunked `pow2 n` with `Nat.pow 2 n` (`[propext]` only). -/
theorem pow2_eq_natPow (n : Nat) : pow2 n = Nat.pow 2 n := by
  dsimp only [pow2]
  cases Nat.blt n 128 with
  | true => rfl
  | false =>
    rw [natPow_mul_sf 2 128 (Nat.div n 128), ← natPow_add_sf]
    exact congrArg (Nat.pow 2) (Nat.div_add_mod n 128)

/-- Strict positivity `0 < 2^n` (`[propext]` only). -/
theorem pow2_pos (n : Nat) : 0 < pow2 n := by
  rw [pow2_eq_natPow]
  exact Nat.two_pow_pos n

/-- `2^(n + 1) = 2^n * 2` (`[propext]` only). -/
theorem pow2_succ (n : Nat) : pow2 (n + 1) = pow2 n * 2 := by
  rw [pow2_eq_natPow, pow2_eq_natPow]
  rfl

/-- `2^(a + b) = 2^a * 2^b` (`[propext]` only). -/
theorem pow2_add (a b : Nat) : pow2 (a + b) = pow2 a * pow2 b := by
  rw [pow2_eq_natPow, pow2_eq_natPow, pow2_eq_natPow]
  exact natPow_add_sf 2 a b

/-- Monotonicity `a ≤ b → 2^a ≤ 2^b` (`[propext]` only). -/
theorem pow2_le_of_le : ∀ {a b : Nat}, a ≤ b → pow2 a ≤ pow2 b
  | _, _, Nat.le.refl => Nat.le_refl _
  | a, b + 1, Nat.le.step h => by
    have ih := pow2_le_of_le h
    rw [pow2_succ b, Nat.mul_two]
    exact Nat.le_trans ih (Nat.le_add_right _ _)

/-- Constructive boolean `≤` on `Int` without `Decidable` instance bloat. -/
@[expose] def intLeB (a b : Int) : Bool :=
  match a, b with
  | .ofNat m, .ofNat n => Nat.ble m n
  | .ofNat _, .negSucc _ => false
  | .negSucc _, .ofNat _ => true
  | .negSucc m, .negSucc n => Nat.ble n m

/-- Constructive boolean `<` on `Int`. -/
@[expose] def intLtB (a b : Int) : Bool :=
  intLeB (Int.add a (Int.ofNat 1)) b

/-- Constructive boolean `==` on `Int`. -/
@[expose] def intEqB (a b : Int) : Bool :=
  match a, b with
  | .ofNat m, .ofNat n => Nat.beq m n
  | .negSucc m, .negSucc n => Nat.beq m n
  | _, _ => false

/-- Constructive maximum on `Int`. -/
@[expose] def intMax (a b : Int) : Int :=
  match intLeB a b with
  | true => b
  | false => a

/-- Constructive minimum on `Int`. -/
@[expose] def intMin (a b : Int) : Int :=
  match intLeB a b with
  | true => a
  | false => b

private theorem natBle_iff_le_sf : ∀ a b : Nat, Nat.ble a b = true ↔ a ≤ b
  | 0, b => ⟨fun _ => Nat.zero_le b, fun _ => rfl⟩
  | _ + 1, 0 => ⟨fun h => Bool.noConfusion h, fun h => nomatch h⟩
  | a + 1, b + 1 =>
    ⟨fun h => Nat.succ_le_succ ((natBle_iff_le_sf a b).mp h),
     fun h => (natBle_iff_le_sf a b).mpr (Nat.le_of_succ_le_succ h)⟩

private theorem natBeq_iff_eq_sf : ∀ a b : Nat, Nat.beq a b = true ↔ a = b
  | 0, 0 => ⟨fun _ => rfl, fun _ => rfl⟩
  | 0, _ + 1 => ⟨fun h => Bool.noConfusion h, fun h => nomatch h⟩
  | _ + 1, 0 => ⟨fun h => Bool.noConfusion h, fun h => nomatch h⟩
  | a + 1, b + 1 =>
    ⟨fun h => congrArg Nat.succ ((natBeq_iff_eq_sf a b).mp h),
     fun h => (natBeq_iff_eq_sf a b).mpr (Nat.succ.inj h)⟩

/-- `intLeB a b = true` iff `a ≤ b` (`[propext]` only). -/
theorem intLeB_iff_le (a b : Int) : intLeB a b = true ↔ a ≤ b := by
  have hBal := intBalance_le (intBalance_self a) (intBalance_self b)
  rw [hBal]
  cases a with
  | ofNat m =>
    cases b with
    | ofNat n =>
      dsimp only [intLeB, intPos, intNeg]
      rw [Nat.add_zero, Nat.add_zero]
      exact natBle_iff_le_sf m n
    | negSucc n =>
      dsimp only [intLeB, intPos, intNeg]
      rw [Nat.add_zero, Nat.zero_add]
      exact ⟨fun h => Bool.noConfusion h,
        fun h => False.elim (Nat.not_succ_le_zero _ (Nat.le_trans (Nat.le_add_left _ m) h))⟩
  | negSucc m =>
    cases b with
    | ofNat n =>
      dsimp only [intLeB, intPos, intNeg]
      rw [Nat.zero_add, Nat.add_zero]
      exact ⟨fun _ => Nat.zero_le _, fun _ => rfl⟩
    | negSucc n =>
      dsimp only [intLeB, intPos, intNeg]
      rw [Nat.zero_add, Nat.zero_add]
      exact ⟨fun h => Nat.succ_le_succ ((natBle_iff_le_sf n m).mp h),
        fun h => (natBle_iff_le_sf n m).mpr (Nat.le_of_succ_le_succ h)⟩

/-- `intLeB a b = false` implies `b ≤ a` (`[propext]` only). -/
theorem le_of_intLeB_false {a b : Int} (h : intLeB a b = false) : b ≤ a := by
  have hBalA := intBalance_self a
  have hBalB := intBalance_self b
  cases Nat.le_total (intPos b + intNeg a) (intPos a + intNeg b) with
  | inl hLe => exact (intBalance_le hBalB hBalA).mpr hLe
  | inr hGe =>
    have hAB : a ≤ b := (intBalance_le hBalA hBalB).mpr hGe
    have hT : intLeB a b = true := (intLeB_iff_le a b).mpr hAB
    rw [h] at hT
    exact Bool.noConfusion hT

/-- Single binary-peeling step for `natLog2`: tests `Nat.div rem (pow2 shift)`.
-/
@[expose] def log2Step (shift : Nat) (accAndRem : Nat × Nat) : Nat × Nat :=
  let acc := accAndRem.1
  let rem := accAndRem.2
  let shifted := Nat.div rem (pow2 shift)
  match Nat.beq shifted 0 with
  | true => (acc, rem)
  | false => (acc + shift, shifted)

/-- Floor base-2 logarithm `⌊log₂ q⌋` for `0 < q < 2^8192` in 13 recursion-free
GMP division steps (`0` `._unsafe_rec`, stack depth `< 20`). -/
@[expose] def natLog2 (q : Nat) : Nat :=
  let s12 := log2Step 4096 (0, q)
  let s11 := log2Step 2048 s12
  let s10 := log2Step 1024 s11
  let s9  := log2Step 512 s10
  let s8  := log2Step 256 s9
  let s7  := log2Step 128 s8
  let s6  := log2Step 64 s7
  let s5  := log2Step 32 s6
  let s4  := log2Step 16 s5
  let s3  := log2Step 8 s4
  let s2  := log2Step 4 s3
  let s1  := log2Step 2 s2
  let s0  := log2Step 1 s1
  s0.1

private def Log2Inv (q bound : Nat) (st : Nat × Nat) : Prop :=
  st.2 = Nat.div q (pow2 st.1) ∧ 1 ≤ st.2 ∧ st.2 < pow2 bound

private theorem nat_div_div_eq_sf (a b c : Nat) :
    Nat.div (Nat.div a b) c = Nat.div a (b * c) :=
  Nat.div_div_eq_div_mul a b c

/-- Positivity of `Nat.div` when `b ≤ a` and `0 < b` (`[propext]` only). -/
theorem nat_div_pos {a b : Nat} (hGe : b ≤ a) (hPos : 0 < b) :
    1 ≤ Nat.div a b := by
  cases hD : Nat.div a b with
  | succ k => exact Nat.succ_le_succ (Nat.zero_le k)
  | zero =>
    have hDivLt : Nat.div a b < 1 := by
      rw [hD]
      exact Nat.zero_lt_succ 0
    have hLtMul : a < 1 * b := (Nat.div_lt_iff_lt_mul hPos).mp hDivLt
    rw [Nat.one_mul] at hLtMul
    exact False.elim (Nat.not_lt_of_ge hGe hLtMul)

private theorem nat_add_mul_mod_left_sf (x y z : Nat) :
    Nat.mod (x + y * z) y = Nat.mod x y :=
  Nat.add_mul_mod_self_left x y z

private theorem nat_add_mul_div_left_sf (x z : Nat) {y : Nat} (h : 0 < y) :
    Nat.div (x + y * z) y = Nat.div x y + z :=
  Nat.add_mul_div_left x z h

private theorem nat_mod_eq_of_lt_sf {a b : Nat} (h : a < b) :
    Nat.mod a b = a :=
  Nat.mod_eq_of_lt h

private theorem nat_div_eq_of_lt_sf {a b : Nat} (h : a < b) :
    Nat.div a b = 0 :=
  Nat.div_eq_of_lt h

private theorem nat_div_add_mod_sf (a b : Nat) :
    b * Nat.div a b + Nat.mod a b = a :=
  Nat.div_add_mod a b

private theorem log2Step_inv {q s : Nat} {st : Nat × Nat}
    (h : Log2Inv q (s + s) st) : Log2Inv q s (log2Step s st) := by
  dsimp only [Log2Inv] at h
  dsimp only [log2Step]
  have hEq := h.1
  have hGe1 := h.2.1
  have hLt := h.2.2
  have hPosS : 0 < pow2 s := pow2_pos s
  cases hBeq : Nat.beq (Nat.div st.2 (pow2 s)) 0 with
  | true =>
    dsimp only [Log2Inv]
    have hZero : Nat.div st.2 (pow2 s) = 0 :=
      (natBeq_iff_eq_sf _ 0).mp hBeq
    have hRemLt : st.2 < pow2 s := by
      cases Nat.lt_or_ge st.2 (pow2 s) with
      | inl hL => exact hL
      | inr hG =>
        have hPosDiv : 1 ≤ Nat.div st.2 (pow2 s) := nat_div_pos hG hPosS
        rw [hZero] at hPosDiv
        exact False.elim (Nat.not_succ_le_zero 0 hPosDiv)
    exact ⟨hEq, hGe1, hRemLt⟩
  | false =>
    dsimp only [Log2Inv]
    have hNeZero : Nat.div st.2 (pow2 s) ≠ 0 := by
      intro hZ
      have hT : Nat.beq (Nat.div st.2 (pow2 s)) 0 = true :=
        (natBeq_iff_eq_sf _ 0).mpr hZ
      rw [hBeq] at hT
      exact Bool.noConfusion hT
    have hGe1' : 1 ≤ Nat.div st.2 (pow2 s) :=
      Nat.pos_of_ne_zero hNeZero
    have hEq' : Nat.div st.2 (pow2 s) = Nat.div q (pow2 (st.1 + s)) := by
      rw [hEq, nat_div_div_eq_sf, ← pow2_add st.1 s]
    have hLt' : Nat.div st.2 (pow2 s) < pow2 s := by
      rw [pow2_add s s] at hLt
      exact (Nat.div_lt_iff_lt_mul hPosS).mpr hLt
    exact ⟨hEq', hGe1', hLt'⟩

/-- Soundness of `natLog2` (`[propext]` only): for every `1 ≤ q < 2^8192`,
`2^(natLog2 q) ≤ q < 2^(natLog2 q + 1)`. -/
theorem natLog2_bounds {q : Nat} (hGe : 1 ≤ q) (hLt : q < pow2 8192) :
    pow2 (natLog2 q) ≤ q ∧ q < pow2 (natLog2 q + 1) := by
  let s12 := log2Step 4096 (0, q)
  let s11 := log2Step 2048 s12
  let s10 := log2Step 1024 s11
  let s9  := log2Step 512 s10
  let s8  := log2Step 256 s9
  let s7  := log2Step 128 s8
  let s6  := log2Step 64 s7
  let s5  := log2Step 32 s6
  let s4  := log2Step 16 s5
  let s3  := log2Step 8 s4
  let s2  := log2Step 4 s3
  let s1  := log2Step 2 s2
  let s0  := log2Step 1 s1
  have hInit : Log2Inv q (4096 + 4096) (0, q) :=
    ⟨(Nat.div_one q).symm, hGe, hLt⟩
  have h12 : Log2Inv q (2048 + 2048) s12 := log2Step_inv hInit
  have h11 : Log2Inv q (1024 + 1024) s11 := log2Step_inv h12
  have h10 : Log2Inv q (512 + 512) s10 := log2Step_inv h11
  have h9  : Log2Inv q (256 + 256) s9 := log2Step_inv h10
  have h8  : Log2Inv q (128 + 128) s8 := log2Step_inv h9
  have h7  : Log2Inv q (64 + 64) s7 := log2Step_inv h8
  have h6  : Log2Inv q (32 + 32) s6 := log2Step_inv h7
  have h5  : Log2Inv q (16 + 16) s5 := log2Step_inv h6
  have h4  : Log2Inv q (8 + 8) s4 := log2Step_inv h5
  have h3  : Log2Inv q (4 + 4) s3 := log2Step_inv h4
  have h2  : Log2Inv q (2 + 2) s2 := log2Step_inv h3
  have h1  : Log2Inv q (1 + 1) s1 := log2Step_inv h2
  have h0  : Log2Inv q 1 s0 := log2Step_inv h1
  change pow2 s0.1 ≤ q ∧ q < pow2 (s0.1 + 1)
  have hDivEq : s0.2 = Nat.div q (pow2 s0.1) := h0.1
  have hRemGe1 : 1 ≤ s0.2 := h0.2.1
  have hRemLt2 : s0.2 < 2 := h0.2.2
  have hPosP : 0 < pow2 s0.1 := pow2_pos s0.1
  have hLo : pow2 s0.1 ≤ q := by
    have hMul : Nat.div q (pow2 s0.1) * pow2 s0.1 ≤ q :=
      Nat.div_mul_le_self q (pow2 s0.1)
    rw [← hDivEq] at hMul
    have hLeMul : pow2 s0.1 ≤ s0.2 * pow2 s0.1 := by
      have hM := Nat.mul_le_mul_right (pow2 s0.1) hRemGe1
      rw [Nat.one_mul] at hM
      exact hM
    exact Nat.le_trans hLeMul hMul
  have hHi : q < pow2 (s0.1 + 1) := by
    rw [pow2_succ, Nat.mul_comm]
    have hDivLt2 : Nat.div q (pow2 s0.1) < 2 := by
      rw [← hDivEq]
      exact hRemLt2
    exact (Nat.div_lt_iff_lt_mul hPosP).mp hDivLt2
  exact ⟨hLo, hHi⟩

/-- Uniqueness of floor base-2 logarithm (`[propext]` only). -/
theorem natLog2_unique {q k1 k2 : Nat}
    (h1Lo : pow2 k1 ≤ q) (h1Hi : q < pow2 (k1 + 1))
    (h2Lo : pow2 k2 ≤ q) (h2Hi : q < pow2 (k2 + 1)) : k1 = k2 := by
  cases Nat.lt_or_ge k1 k2 with
  | inl hLt =>
    have hLe : pow2 (k1 + 1) ≤ pow2 k2 := pow2_le_of_le hLt
    exact False.elim (Nat.not_lt_of_ge (Nat.le_trans hLe h2Lo) h1Hi)
  | inr hGe =>
    cases Nat.lt_or_ge k2 k1 with
    | inl hLt2 =>
      have hLe : pow2 (k2 + 1) ≤ pow2 k1 := pow2_le_of_le hLt2
      exact False.elim (Nat.not_lt_of_ge (Nat.le_trans hLe h1Lo) h2Hi)
    | inr hGe2 =>
      exact Nat.le_antisymm hGe2 hGe

/-! ## Part II: IEEE-754 Interchange Formats & Bit Unpacking/Encoding -/

/-- IEEE-754 interchange formats of Rust's `f32` (`binary32`) and `f64`
(`binary64`). -/
inductive IeeeFormat : Type where
  | binary32 : IeeeFormat
  | binary64 : IeeeFormat

namespace IeeeFormat

/-- Explicit structural equality on `IeeeFormat`. -/
@[expose] def beq : IeeeFormat → IeeeFormat → Bool
  | .binary32, .binary32 => true
  | .binary64, .binary64 => true
  | _, _ => false

/-- Total bit width (`32` / `64`). -/
@[expose] def width : IeeeFormat → Nat
  | .binary32 => 32
  | .binary64 => 64

/-- Biased exponent field width (`8` / `11`). -/
@[expose] def exponentBits : IeeeFormat → Nat
  | .binary32 => 8
  | .binary64 => 11

/-- Trailing significand (fraction) field width (`23` / `52`). -/
@[expose] def fractionBits : IeeeFormat → Nat
  | .binary32 => 23
  | .binary64 => 52

/-- Significand precision `p = fractionBits + 1` (`24` / `53`). -/
@[expose] def precision (f : IeeeFormat) : Nat :=
  f.fractionBits + 1

/-- Exponent bias (`127` / `1023`). -/
@[expose] def bias : IeeeFormat → Nat
  | .binary32 => 127
  | .binary64 => 1023

/-- Byte width (`4` / `8`). -/
@[expose] def byteWidth : IeeeFormat → Nat
  | .binary32 => 4
  | .binary64 => 8

/-- Minimum normal unbiased exponent (`-126` / `-1022`). -/
@[expose] def minExponent (f : IeeeFormat) : Int :=
  Int.sub (Int.ofNat 1) (Int.ofNat f.bias)

/-- Maximum finite unbiased exponent (`127` / `1023`). -/
@[expose] def maxExponent (f : IeeeFormat) : Int :=
  Int.ofNat f.bias

/-- All-ones biased exponent field (`255` / `2047`). -/
@[expose] def allOnesExp (f : IeeeFormat) : Nat :=
  pow2 f.exponentBits - 1

/-- Quiet-NaN MSB mask inside the fraction field (`2^(fractionBits - 1)`). -/
@[expose] def quietBitMask (f : IeeeFormat) : Nat :=
  pow2 (f.fractionBits - 1)

/-- Sign-bit mask (`2^(width - 1)`). -/
@[expose] def signBitMask (f : IeeeFormat) : Nat :=
  pow2 (f.width - 1)

end IeeeFormat

/-- IEEE-754 `binary32` bit pattern (`f32::to_bits`). -/
abbrev F32Bits : Type := BitVec 32

/-- IEEE-754 `binary64` bit pattern (`f64::to_bits`). -/
abbrev F64Bits : Type := BitVec 64

/-- Raw sign / biased-exponent / fraction fields of an IEEE-754 bit pattern. -/
structure FloatComponents : Type where
  neg : Bool
  exponent : Nat
  fraction : Nat

/-- Split a bit pattern into its sign, biased exponent, and fraction fields. -/
@[expose] def unpackBits (f : IeeeFormat) (bits : Nat) : FloatComponents :=
  { neg := Nat.beq (Nat.mod (Nat.div bits (pow2 (f.width - 1))) 2) 1
    exponent := Nat.mod (Nat.div bits (pow2 f.fractionBits)) (pow2 f.exponentBits)
    fraction := Nat.mod bits (pow2 f.fractionBits) }

/-- Bit pattern of a signed zero (`+0.0` or `-0.0`). -/
@[expose] def zeroBits (f : IeeeFormat) (neg : Bool) : Nat :=
  match neg with
  | true => pow2 (f.width - 1)
  | false => 0

/-- Assemble a bit pattern from sign, biased exponent, and fraction fields. -/
@[expose] def encodeBits (f : IeeeFormat) (neg : Bool) (exponent fraction : Nat) : Nat :=
  zeroBits f neg + exponent * pow2 f.fractionBits + fraction

/-- Assemble a bit pattern from `FloatComponents`. -/
@[expose] def packBits (f : IeeeFormat) (c : FloatComponents) : Nat :=
  encodeBits f c.neg c.exponent c.fraction

/-- Bit pattern of a signed infinity (`+∞` or `-∞`). -/
@[expose] def infBits (f : IeeeFormat) (neg : Bool) : Nat :=
  encodeBits f neg f.allOnesExp 0

/-- Bit pattern of the canonical positive quiet NaN (`0x7fc0_0000` /
`0x7ff8_0000_0000_0000`). -/
@[expose] def preferredNaNBits (f : IeeeFormat) : Nat :=
  encodeBits f false f.allOnesExp f.quietBitMask

/-- Signed maximum finite bit pattern (`+MAX_FINITE` or `-MAX_FINITE`). -/
@[expose] def signedMaxFiniteBits (f : IeeeFormat) (neg : Bool) : Nat :=
  encodeBits f neg (f.allOnesExp - 1) (pow2 f.fractionBits - 1)

/-- Maximum finite positive bit pattern (`f32::MAX` / `f64::MAX`). -/
@[expose] def maxFiniteBits (f : IeeeFormat) : Nat :=
  signedMaxFiniteBits f false

/-- Minimum positive normal bit pattern (`f32::MIN_POSITIVE` /
`f64::MIN_POSITIVE`). -/
@[expose] def minNormalBits (f : IeeeFormat) : Nat :=
  encodeBits f false 1 0

/-- Minimum positive subnormal bit pattern (`0x0000_0001`). -/
@[expose] def minSubnormalBits (f : IeeeFormat) : Nat :=
  encodeBits f false 0 1

/-! ## Part III: Classification & Exact Rational Decoding -/

/-- Exact classification of an IEEE-754 bit pattern. Finite nonzero values carry
the exact rational magnitude `num / den` (`den` a power of two). -/
inductive FloatKind : Type where
  | zero (neg : Bool) : FloatKind
  | finite (neg : Bool) (num den : Nat) : FloatKind
  | inf (neg : Bool) : FloatKind
  | nan (neg : Bool) (quiet : Bool) (payload : Nat) : FloatKind

/-- Scale the rational `n / d` by `2^e`. -/
@[expose] def powScale (n d : Nat) : Int → Nat × Nat
  | .ofNat k => (n * pow2 k, d)
  | .negSucc k => (n, d * pow2 (k + 1))

/-- Exact IEEE-754 decoding of `bits` in format `f`. -/
@[expose] def decodeBits (f : IeeeFormat) (bits : Nat) : FloatKind :=
  let c := unpackBits f bits
  match Nat.beq c.exponent f.allOnesExp with
  | true =>
    match Nat.beq c.fraction 0 with
    | true => .inf c.neg
    | false =>
      let qBit := Nat.beq (Nat.mod (Nat.div c.fraction f.quietBitMask) 2) 1
      .nan c.neg qBit c.fraction
  | false =>
    match Nat.beq c.exponent 0 with
    | true =>
      match Nat.beq c.fraction 0 with
      | true => .zero c.neg
      | false =>
        let nd := powScale c.fraction 1
          (Int.sub f.minExponent (Int.ofNat f.fractionBits))
        .finite c.neg nd.1 nd.2
    | false =>
      let nd := powScale (pow2 f.fractionBits + c.fraction) 1
        (Int.sub (Int.sub (Int.ofNat c.exponent) (Int.ofNat f.bias))
          (Int.ofNat f.fractionBits))
      .finite c.neg nd.1 nd.2

/-- Extract sign bit (`true` iff negative). -/
@[expose] def signBitOf (f : IeeeFormat) (bits : Nat) : Bool :=
  (unpackBits f bits).neg

/-- `true` iff `bits` encodes `+0.0` or `-0.0`. -/
@[expose] def isZeroBits (f : IeeeFormat) (bits : Nat) : Bool :=
  let c := unpackBits f bits
  Nat.beq c.exponent 0 && Nat.beq c.fraction 0

/-- `true` iff `bits` encodes a nonzero subnormal (`exponent = 0`,
`fraction ≠ 0`). -/
@[expose] def isSubnormalBits (f : IeeeFormat) (bits : Nat) : Bool :=
  let c := unpackBits f bits
  Nat.beq c.exponent 0 && !Nat.beq c.fraction 0

/-- `true` iff `bits` encodes a finite normal number
(`1 ≤ exponent < allOnesExp`). -/
@[expose] def isNormalBits (f : IeeeFormat) (bits : Nat) : Bool :=
  let c := unpackBits f bits
  !Nat.beq c.exponent 0 && !Nat.beq c.exponent f.allOnesExp

/-- `true` iff `bits` encodes a finite value (zero, subnormal, or normal). -/
@[expose] def isFiniteBits (f : IeeeFormat) (bits : Nat) : Bool :=
  !Nat.beq (unpackBits f bits).exponent f.allOnesExp

/-- `true` iff `bits` encodes `+∞` or `-∞`. -/
@[expose] def isInfiniteBits (f : IeeeFormat) (bits : Nat) : Bool :=
  let c := unpackBits f bits
  Nat.beq c.exponent f.allOnesExp && Nat.beq c.fraction 0

/-- `true` iff `bits` decodes to any NaN (quiet or signaling). -/
@[expose] def isNaNBits (f : IeeeFormat) (bits : Nat) : Bool :=
  match decodeBits f bits with
  | .nan _ _ _ => true
  | _ => false

/-- `true` iff `bits` decodes to a quiet NaN (QNaN, quiet bit `1`). -/
@[expose] def isQuietNaNBits (f : IeeeFormat) (bits : Nat) : Bool :=
  match decodeBits f bits with
  | .nan _ quiet _ => quiet
  | _ => false

/-- `true` iff `bits` decodes to a signaling NaN (SNaN, quiet bit `0` and
nonzero lower payload). -/
@[expose] def isSignalingNaNBits (f : IeeeFormat) (bits : Nat) : Bool :=
  match decodeBits f bits with
  | .nan _ quiet _ => !quiet
  | _ => false

/-! ## Part IV: Rounding Modes & Exact Rational `roundRatio` -/

/-- IEEE 754-2008 §4.3 rounding-direction attributes (`tiesToEven`,
`tiesAwayFromZero` = `roundTiesToAway`, `towardZero`, `towardPosInf`, and
`towardNegInf`). -/
inductive RoundingMode : Type where
  | tiesToEven : RoundingMode
  | tiesAwayFromZero : RoundingMode
  | towardZero : RoundingMode
  | towardPosInf : RoundingMode
  | towardNegInf : RoundingMode

/-- Nearest integer to `n / d`, ties to even (IEEE 754-2008
`roundTiesToEven`). -/
@[expose] def roundQuotientTiesToEven (n d : Nat) : Nat :=
  let q := Nat.div n d
  let r := Nat.mod n d
  if Nat.blt d (r * 2) || (Nat.beq (r * 2) d && Nat.beq (Nat.mod q 2) 1) then
    q + 1
  else
    q

/-- Round nonnegative quotient `n / d` with sign `neg` according to `mode`. -/
@[expose] def roundQuotient (mode : RoundingMode) (neg : Bool) (n d : Nat) : Nat :=
  match mode with
  | .tiesToEven => roundQuotientTiesToEven n d
  | .tiesAwayFromZero =>
    let q := Nat.div n d
    let r := Nat.mod n d
    if Nat.ble d (r * 2) then q + 1 else q
  | .towardZero => Nat.div n d
  | .towardPosInf =>
    let q := Nat.div n d
    let r := Nat.mod n d
    if !neg && !Nat.beq r 0 then q + 1 else q
  | .towardNegInf =>
    let q := Nat.div n d
    let r := Nat.mod n d
    if neg && !Nat.beq r 0 then q + 1 else q

/-- `⌊log₂(n / d)⌋` for nonzero `n, d` (`0` host floats, `0` `._unsafe_rec`),
matching `Miri.Interpreter.FloatBits.ratioExponent`. -/
@[expose] def ratioExponent (n d : Nat) : Int :=
  match Nat.ble d n with
  | true => Int.ofNat (natLog2 (Nat.div n d))
  | false =>
    let k := natLog2 (Nat.div d n)
    match Nat.ble d (n * pow2 k) with
    | true => Int.neg (Int.ofNat k)
    | false => Int.neg (Int.ofNat (k + 1))

/-- IEEE 754-2008 §7.4 overflow result for sign `neg` under rounding direction
`mode`: returns `±MAX_FINITE` when `mode` rounds toward zero (`towardZero`,
`towardPosInf` on negative values, `towardNegInf` on positive values) and `±∞`
otherwise. -/
@[expose] def overflowBits (mode : RoundingMode) (f : IeeeFormat)
    (neg : Bool) : Nat :=
  match mode with
  | .tiesToEven => infBits f neg
  | .tiesAwayFromZero => infBits f neg
  | .towardZero => signedMaxFiniteBits f neg
  | .towardPosInf => if neg then signedMaxFiniteBits f true else infBits f false
  | .towardNegInf => if neg then infBits f true else signedMaxFiniteBits f false

/-- Correctly rounded IEEE-754 encoding of `(-1)^neg * n / d` in format `f`
under rounding direction `mode`. Clamping `exponent` to `f.minExponent` realizes
gradual subnormal underflow; binade carry bumps `exponent` and re-checks
`maxExponent` overflow via `overflowBits mode f neg` (IEEE 754-2008 §7.4). -/
@[expose] def roundRatioBits (mode : RoundingMode) (f : IeeeFormat)
    (neg : Bool) (n d : Nat) : Nat :=
  match Nat.beq d 0 with
  | true => preferredNaNBits f
  | false =>
    match Nat.beq n 0 with
    | true => zeroBits f neg
    | false =>
      let exponent := intMax (ratioExponent n d) f.minExponent
      match intLtB f.maxExponent exponent with
      | true => overflowBits mode f neg
      | false =>
        let scaled := powScale n d (Int.sub (Int.ofNat f.fractionBits) exponent)
        let significand := roundQuotient mode neg scaled.1 scaled.2
        let carry := Nat.ble (pow2 (f.fractionBits + 1)) significand
        let significand' := if carry then Nat.div significand 2 else significand
        let exponent' := if carry then Int.add exponent (Int.ofNat 1) else exponent
        match intLtB f.maxExponent exponent' with
        | true => overflowBits mode f neg
        | false =>
          match Nat.blt significand' (pow2 f.fractionBits) with
          | true =>
            match intEqB exponent' f.minExponent with
            | true => encodeBits f neg 0 significand'
            | false => preferredNaNBits f
          | false =>
            match Nat.ble (pow2 (f.fractionBits + 1)) significand' with
            | true => preferredNaNBits f
            | false =>
              encodeBits f neg
                (Int.toNat (Int.add exponent' (Int.ofNat f.bias)))
                (significand' - pow2 f.fractionBits)

/-- Default IEEE 754-2008 `roundTiesToEven` rational rounding (Rust primitive
arithmetic and `as` casts). -/
@[expose] def roundRatioTiesToEven (f : IeeeFormat) (neg : Bool) (n d : Nat) : Nat :=
  roundRatioBits .tiesToEven f neg n d

/-- `roundRatioTiesToEven` is definitionally `roundRatioBits .tiesToEven`. -/
theorem roundRatioBits_tiesToEven_eq (f : IeeeFormat) (neg : Bool) (n d : Nat) :
    roundRatioBits .tiesToEven f neg n d = roundRatioTiesToEven f neg n d :=
  rfl

/-! ## Part V: Miri `FloatBits.decode` Lockstep & Bit-Width / Structural Laws -/

/-- Literal mirror of `Miri.Interpreter.FloatClass`. -/
inductive MiriFloatClass : Type where
  | finite (numerator denominator : Nat) : MiriFloatClass
  | infinite : MiriFloatClass
  | nan (payload : Nat) : MiriFloatClass

/-- Literal mirror of `Miri.Interpreter.FloatDecoded`. -/
structure MiriFloatDecoded : Type where
  negative : Bool
  value : MiriFloatClass

/-- Literal transliteration of `Miri.Interpreter.FloatBits.decode`
(`vendor/lean-miri/Miri/Interpreter/Float.lean:57-70`). -/
@[expose] def miriDecode (f : IeeeFormat) (bits : Nat) : Option MiriFloatDecoded :=
  match Nat.ble (pow2 f.width) bits with
  | true => none
  | false =>
    let negative := !Nat.beq (Nat.div bits (pow2 (f.width - 1))) 0
    let exponent := Nat.mod (Nat.div bits (pow2 f.fractionBits)) (pow2 f.exponentBits)
    let fraction := Nat.mod bits (pow2 f.fractionBits)
    match Nat.beq exponent f.allOnesExp with
    | true =>
      some ⟨negative,
        if Nat.beq fraction 0 then .infinite else .nan fraction⟩
    | false =>
      let significand :=
        if Nat.beq exponent 0 then fraction else pow2 f.fractionBits + fraction
      let unbiased : Int :=
        if Nat.beq exponent 0 then f.minExponent
        else Int.sub (Int.ofNat exponent) (Int.ofNat f.bias)
      let nd := powScale significand 1 (Int.sub unbiased (Int.ofNat f.fractionBits))
      some ⟨negative, .finite nd.1 nd.2⟩

/-- Project `FloatKind` to Miri's `FloatDecoded` (mapping `.zero` to
`.finite 0 d`). -/
@[expose] def floatKindToMiri (f : IeeeFormat) : FloatKind → MiriFloatDecoded
  | .zero neg =>
    ⟨neg, .finite 0 (powScale 0 1 (Int.sub f.minExponent (Int.ofNat f.fractionBits))).2⟩
  | .finite neg n d => ⟨neg, .finite n d⟩
  | .inf neg => ⟨neg, .infinite⟩
  | .nan neg _ payload => ⟨neg, .nan payload⟩

private theorem format_width_split (f : IeeeFormat) :
    f.fractionBits + f.exponentBits = f.width - 1 := by
  cases f <;> rfl

private theorem format_width_succ (f : IeeeFormat) :
    (f.width - 1) + 1 = f.width := by
  cases f <;> rfl

/-- `zeroBits f neg < 2^f.width` (`[propext]` only). -/
theorem zeroBits_lt (f : IeeeFormat) (neg : Bool) :
    zeroBits f neg < pow2 f.width := by
  cases neg with
  | false => exact pow2_pos f.width
  | true =>
    dsimp only [zeroBits]
    rw [← format_width_succ f, pow2_succ]
    have hPos : 0 < pow2 (f.width - 1) := pow2_pos (f.width - 1)
    rw [Nat.mul_two]
    exact Nat.lt_add_of_pos_right hPos

/-- `encodeBits f neg exp frac < 2^f.width` whenever `exp < 2^f.exponentBits`
and `frac < 2^f.fractionBits` (`[propext]` only). -/
theorem encodeBits_lt (f : IeeeFormat) (neg : Bool) {exp frac : Nat}
    (hExp : exp < pow2 f.exponentBits) (hFrac : frac < pow2 f.fractionBits) :
    encodeBits f neg exp frac < pow2 f.width := by
  dsimp only [encodeBits]
  have hBody : exp * pow2 f.fractionBits + frac < pow2 (f.width - 1) := by
    rw [← format_width_split f, pow2_add, Nat.mul_comm (pow2 f.fractionBits)]
    have hExpLe : exp + 1 ≤ pow2 f.exponentBits := hExp
    have hMulLe : (exp + 1) * pow2 f.fractionBits ≤
        pow2 f.exponentBits * pow2 f.fractionBits :=
      Nat.mul_le_mul_right (pow2 f.fractionBits) hExpLe
    rw [Nat.add_mul, Nat.one_mul] at hMulLe
    exact Nat.lt_of_lt_of_le (Nat.add_lt_add_left hFrac _) hMulLe
  rw [← format_width_succ f, pow2_succ, Nat.mul_two]
  cases neg with
  | false =>
    dsimp only [zeroBits]
    rw [Nat.zero_add]
    exact Nat.lt_of_lt_of_le hBody (Nat.le_add_right _ _)
  | true =>
    dsimp only [zeroBits]
    rw [Nat.add_assoc]
    exact Nat.add_lt_add_left hBody _

/-- `infBits f neg < 2^f.width` (`[]` zero axioms). -/
theorem infBits_lt (f : IeeeFormat) (neg : Bool) :
    infBits f neg < pow2 f.width := by
  cases f <;> cases neg <;> decide

/-- `signedMaxFiniteBits f neg < 2^f.width` (`[]` zero axioms). -/
theorem signedMaxFiniteBits_lt (f : IeeeFormat) (neg : Bool) :
    signedMaxFiniteBits f neg < pow2 f.width := by
  cases f <;> cases neg <;> decide

/-- `overflowBits mode f neg < 2^f.width` (`[]` zero axioms). -/
theorem overflowBits_lt (mode : RoundingMode) (f : IeeeFormat) (neg : Bool) :
    overflowBits mode f neg < pow2 f.width := by
  cases mode <;> cases f <;> cases neg <;> decide

/-- `preferredNaNBits f < 2^f.width` (`[]` zero axioms). -/
theorem preferredNaNBits_lt (f : IeeeFormat) :
    preferredNaNBits f < pow2 f.width := by
  cases f <;> decide

/-- `preferredNaNBits f` is always a quiet NaN (`[propext]` only). -/
theorem isQuietNaNBits_preferredNaNBits (f : IeeeFormat) :
    isQuietNaNBits f (preferredNaNBits f) = true := by
  cases f <;> rfl

/-- `preferredNaNBits f` is always classified as NaN (`[propext]` only). -/
theorem isNaNBits_preferredNaNBits (f : IeeeFormat) :
    isNaNBits f (preferredNaNBits f) = true := by
  cases f <;> rfl

/-- `infBits f neg` is never NaN (`[propext]` only). -/
theorem isNaNBits_infBits (f : IeeeFormat) (neg : Bool) :
    isNaNBits f (infBits f neg) = false := by
  cases f <;> cases neg <;> rfl

/-- `zeroBits f neg` is never NaN (`[propext]` only). -/
theorem isNaNBits_zeroBits (f : IeeeFormat) (neg : Bool) :
    isNaNBits f (zeroBits f neg) = false := by
  cases f <;> cases neg <;> rfl

/-- Every zero input with nonzero denominator rounds to `zeroBits f neg`,
preserving `-0.0` vs `+0.0` under every rounding mode (`[propext]` only). -/
theorem roundRatioBits_zero (mode : RoundingMode) (f : IeeeFormat)
    (neg : Bool) {d : Nat} (hd : d ≠ 0) :
    roundRatioBits mode f neg 0 d = zeroBits f neg := by
  dsimp only [roundRatioBits]
  cases hBeq : Nat.beq d 0 with
  | false => rfl
  | true =>
    exact False.elim (hd ((natBeq_iff_eq_sf d 0).mp hBeq))

private theorem intLe_of_intLtB_false {a b : Int} (h : intLtB a b = false) :
    b ≤ a := by
  dsimp only [intLtB] at h
  have hBalA1 := intBalance_add (intBalance_self a) (intBalance_ofNat 1)
  have hBalB := intBalance_self b
  cases Nat.lt_or_ge (intPos b + intNeg a) (intPos a + 1 + intNeg b) with
  | inl hLtNat =>
    have hLeNat : intPos b + intNeg a ≤ intPos a + intNeg b := by
      rw [Nat.add_right_comm (intPos a) 1 (intNeg b)] at hLtNat
      exact Nat.le_of_lt_succ hLtNat
    exact (intBalance_le hBalB (intBalance_self a)).mpr hLeNat
  | inr hGeNat =>
    have hAB : Int.add a (Int.ofNat 1) ≤ b :=
      (intBalance_le hBalA1 hBalB).mpr (by
        dsimp only [intPos, intNeg]
        rw [Nat.add_zero]
        exact hGeNat)
    have hT : intLeB (Int.add a (Int.ofNat 1)) b = true :=
      (intLeB_iff_le _ _).mpr hAB
    rw [h] at hT
    exact Bool.noConfusion hT

private theorem natBlt_iff_lt_sf (a b : Nat) : Nat.blt a b = true ↔ a < b :=
  natBle_iff_le_sf (a + 1) b

/-- Output of `roundRatioBits` always fits in `f.width` bits (`[propext]`
only). -/
theorem roundRatioBits_lt (mode : RoundingMode) (f : IeeeFormat)
    (neg : Bool) (n d : Nat) :
    roundRatioBits mode f neg n d < pow2 f.width := by
  dsimp only [roundRatioBits]
  cases Nat.beq d 0 with
  | true => exact preferredNaNBits_lt f
  | false =>
    cases Nat.beq n 0 with
    | true => exact zeroBits_lt f neg
    | false =>
      dsimp only
      cases intLtB f.maxExponent (intMax (ratioExponent n d) f.minExponent) with
      | true => exact overflowBits_lt mode f neg
      | false =>
        dsimp only
        let exponent := intMax (ratioExponent n d) f.minExponent
        let scaled := powScale n d (Int.sub (Int.ofNat f.fractionBits) exponent)
        let significand := roundQuotient mode neg scaled.1 scaled.2
        let carry := Nat.ble (pow2 (f.fractionBits + 1)) significand
        let significand' := if carry then Nat.div significand 2 else significand
        let exponent' := if carry then Int.add exponent (Int.ofNat 1) else exponent
        cases hMax2 : intLtB f.maxExponent exponent' with
        | true => exact overflowBits_lt mode f neg
        | false =>
          cases hSub : Nat.blt significand' (pow2 f.fractionBits) with
          | true =>
            cases intEqB exponent' f.minExponent with
            | false => exact preferredNaNBits_lt f
            | true =>
              exact encodeBits_lt f neg (pow2_pos f.exponentBits)
                ((natBlt_iff_lt_sf _ _).mp hSub)
          | false =>
            cases hHi : Nat.ble (pow2 (f.fractionBits + 1)) significand' with
            | true => exact preferredNaNBits_lt f
            | false =>
              have hSigGe : pow2 f.fractionBits ≤ significand' := by
                cases Nat.lt_or_ge significand' (pow2 f.fractionBits) with
                | inr hG => exact hG
                | inl hL =>
                  have hT := (natBlt_iff_lt_sf _ _).mpr hL
                  rw [hSub] at hT
                  exact Bool.noConfusion hT
              have hSigLt : significand' < pow2 (f.fractionBits + 1) := by
                cases Nat.lt_or_ge significand' (pow2 (f.fractionBits + 1)) with
                | inl hL => exact hL
                | inr hG =>
                  have hT := (natBle_iff_le_sf _ _).mpr hG
                  rw [hHi] at hT
                  exact Bool.noConfusion hT
              have hFracLt : significand' - pow2 f.fractionBits < pow2 f.fractionBits := by
                rw [pow2_succ, Nat.mul_two] at hSigLt
                exact Nat.sub_lt_left_of_lt_add hSigGe hSigLt
              have hExpLeMax : exponent' ≤ f.maxExponent :=
                intLe_of_intLtB_false hMax2
              have hExpLtAll :
                  Int.toNat (Int.add exponent' (Int.ofNat f.bias)) <
                    pow2 f.exponentBits := by
                have hAddLe :
                    Int.add exponent' (Int.ofNat f.bias) ≤
                      Int.ofNat (f.bias + f.bias) := by
                  dsimp only [IeeeFormat.maxExponent] at hExpLeMax
                  have hB := (intBalance_le (intBalance_self exponent')
                    (intBalance_ofNat f.bias)).mp hExpLeMax
                  exact (intBalance_le
                    (intBalance_add (intBalance_self exponent')
                      (intBalance_ofNat f.bias))
                    (intBalance_ofNat (f.bias + f.bias))).mpr
                    (by
                      dsimp only [intPos, intNeg] at hB
                      dsimp only [intPos, intNeg]
                      rw [Nat.add_zero] at hB
                      rw [Nat.add_zero, Nat.add_zero, Nat.add_right_comm]
                      exact Nat.add_le_add_right hB f.bias)
                have hToNatLe :
                    Int.toNat (Int.add exponent' (Int.ofNat f.bias)) ≤
                      f.bias + f.bias := by
                  cases hE : Int.add exponent' (Int.ofNat f.bias) with
                  | negSucc _ => exact Nat.zero_le _
                  | ofNat k =>
                    rw [hE] at hAddLe
                    have hB := (intBalance_le (intBalance_ofNat k)
                      (intBalance_ofNat (f.bias + f.bias))).mp hAddLe
                    dsimp only [Int.toNat]
                    rw [Nat.add_zero, Nat.add_zero] at hB
                    exact hB
                have hBias2Lt : f.bias + f.bias < pow2 f.exponentBits - 1 := by
                  cases f <;> decide
                exact Nat.lt_of_le_of_lt hToNatLe
                  (Nat.lt_trans hBias2Lt
                    (Nat.sub_lt (pow2_pos f.exponentBits) (Nat.zero_lt_succ 0)))
              exact encodeBits_lt f neg hExpLtAll hFracLt

/-- `roundRatioTiesToEven f neg n d < 2^f.width` (`[propext]` only). -/
theorem roundRatioTiesToEven_lt (f : IeeeFormat) (neg : Bool) (n d : Nat) :
    roundRatioTiesToEven f neg n d < pow2 f.width :=
  roundRatioBits_lt .tiesToEven f neg n d

/-- Unpacking an encoded bit pattern recovers its exact components (`[propext]`
only). -/
theorem unpackBits_encodeBits (f : IeeeFormat) (neg : Bool) {exp frac : Nat}
    (hExp : exp < pow2 f.exponentBits) (hFrac : frac < pow2 f.fractionBits) :
    unpackBits f (encodeBits f neg exp frac) = ⟨neg, exp, frac⟩ := by
  dsimp only [unpackBits, encodeBits]
  have hPosF : 0 < pow2 f.fractionBits := pow2_pos f.fractionBits
  have hBodyLt : exp * pow2 f.fractionBits + frac < pow2 (f.width - 1) := by
    rw [← format_width_split f, pow2_add, Nat.mul_comm (pow2 f.fractionBits)]
    have hExpLe : exp + 1 ≤ pow2 f.exponentBits := hExp
    have hMulLe := Nat.mul_le_mul_right (pow2 f.fractionBits) hExpLe
    rw [Nat.add_mul, Nat.one_mul] at hMulLe
    exact Nat.lt_of_lt_of_le (Nat.add_lt_add_left hFrac _) hMulLe
  have hZeroMul : ∃ s : Nat,
      zeroBits f neg = (s * pow2 f.exponentBits) * pow2 f.fractionBits ∧
      s < 2 := by
    cases neg with
    | false =>
      refine ⟨0, ?_, by decide⟩
      dsimp only [zeroBits]
      rw [Nat.zero_mul, Nat.zero_mul]
    | true =>
      refine ⟨1, ?_, by decide⟩
      dsimp only [zeroBits]
      rw [Nat.one_mul, ← pow2_add, Nat.add_comm, format_width_split]
  cases hZeroMul with
  | intro s hs =>
    have hsEq := hs.1
    have hSumEq :
        zeroBits f neg + exp * pow2 f.fractionBits + frac =
          frac + pow2 f.fractionBits * (s * pow2 f.exponentBits + exp) := by
      rw [hsEq, ← Nat.add_mul, Nat.mul_comm _ (pow2 f.fractionBits),
        Nat.add_comm _ frac]
    have hFracEq :
        Nat.mod (zeroBits f neg + exp * pow2 f.fractionBits + frac)
          (pow2 f.fractionBits) = frac := by
      rw [hSumEq, nat_add_mul_mod_left_sf]
      exact nat_mod_eq_of_lt_sf hFrac
    have hDivF :
        Nat.div (zeroBits f neg + exp * pow2 f.fractionBits + frac)
          (pow2 f.fractionBits) = s * pow2 f.exponentBits + exp := by
      rw [hSumEq, nat_add_mul_div_left_sf _ _ hPosF, nat_div_eq_of_lt_sf hFrac,
        Nat.zero_add]
    have hExpEq :
        Nat.mod (Nat.div (zeroBits f neg + exp * pow2 f.fractionBits + frac)
          (pow2 f.fractionBits)) (pow2 f.exponentBits) = exp := by
      rw [hDivF, Nat.add_comm, Nat.mul_comm s, nat_add_mul_mod_left_sf]
      exact nat_mod_eq_of_lt_sf hExp
    have hSignEq :
        Nat.beq (Nat.mod (Nat.div
          (zeroBits f neg + exp * pow2 f.fractionBits + frac)
          (pow2 (f.width - 1))) 2) 1 = neg := by
      have hPosW : 0 < pow2 (f.width - 1) := pow2_pos (f.width - 1)
      cases neg with
      | false =>
        dsimp only [zeroBits]
        rw [Nat.zero_add, nat_div_eq_of_lt_sf hBodyLt]
        rfl
      | true =>
        dsimp only [zeroBits]
        have hRewriteTop :
            pow2 (f.width - 1) + exp * pow2 f.fractionBits + frac =
              (exp * pow2 f.fractionBits + frac) + pow2 (f.width - 1) * 1 := by
          rw [Nat.mul_one, Nat.add_comm (exp * pow2 f.fractionBits + frac),
            ← Nat.add_assoc]
        rw [hRewriteTop, nat_add_mul_div_left_sf _ _ hPosW,
          nat_div_eq_of_lt_sf hBodyLt, Nat.zero_add]
        rfl
    rw [hSignEq, hExpEq, hFracEq]

/-- Encoding unpacked bits of any `< 2^f.width` pattern recovers `bits`
(`[propext]` only). -/
theorem encodeBits_unpackBits (f : IeeeFormat) {bits : Nat}
    (hBits : bits < pow2 f.width) :
    encodeBits f (unpackBits f bits).neg (unpackBits f bits).exponent
      (unpackBits f bits).fraction = bits := by
  dsimp only [unpackBits, encodeBits]
  have hQ1 := nat_div_add_mod_sf bits (pow2 f.fractionBits)
  have hQ2 := nat_div_add_mod_sf (Nat.div bits (pow2 f.fractionBits))
    (pow2 f.exponentBits)
  have hTopEq :
      Nat.div (Nat.div bits (pow2 f.fractionBits)) (pow2 f.exponentBits) =
        Nat.div bits (pow2 (f.width - 1)) := by
    rw [nat_div_div_eq_sf, ← pow2_add, format_width_split]
  have hTopLt2 : Nat.div bits (pow2 (f.width - 1)) < 2 := by
    apply (Nat.div_lt_iff_lt_mul (pow2_pos (f.width - 1))).mpr
    rw [Nat.mul_comm, ← pow2_succ, format_width_succ]
    exact hBits
  have hZeroVal :
      zeroBits f (Nat.beq (Nat.mod (Nat.div bits (pow2 (f.width - 1))) 2) 1) =
        Nat.div bits (pow2 (f.width - 1)) * pow2 (f.width - 1) := by
    cases hD : Nat.div bits (pow2 (f.width - 1)) with
    | zero =>
      dsimp only [zeroBits]
      rw [Nat.zero_mul]
    | succ k =>
      rw [hD] at hTopLt2
      have hk0 : k = 0 :=
        Nat.eq_zero_of_le_zero (Nat.le_of_lt_succ (Nat.lt_of_succ_lt_succ hTopLt2))
      subst hk0
      dsimp only [zeroBits]
      rw [Nat.one_mul]
  rw [hZeroVal, ← hTopEq, ← format_width_split f, pow2_add,
    Nat.mul_comm (pow2 f.fractionBits) (pow2 f.exponentBits)]
  rw [← Nat.mul_assoc, ← Nat.add_mul,
    Nat.mul_comm (Nat.div (Nat.div bits (pow2 f.fractionBits)) (pow2 f.exponentBits)),
    hQ2]
  rw [Nat.mul_comm _ (pow2 f.fractionBits)]
  exact hQ1

/-- Exact equivalence between `decodeBits` and literal `miriDecode` across all
in-width `f32` and `f64` bit patterns (`[propext]` only). -/
theorem decodeBits_eq_miriDecode (f : IeeeFormat) {bits : Nat}
    (hBits : bits < pow2 f.width) :
    miriDecode f bits = some (floatKindToMiri f (decodeBits f bits)) := by
  dsimp only [miriDecode, decodeBits, unpackBits]
  have hBleFalse : Nat.ble (pow2 f.width) bits = false := by
    cases hB : Nat.ble (pow2 f.width) bits with
    | false => rfl
    | true =>
      have hGe := (natBle_iff_le_sf _ _).mp hB
      exact False.elim (Nat.not_lt_of_ge hGe hBits)
  rw [hBleFalse]
  dsimp only
  have hTopLt2 : Nat.div bits (pow2 (f.width - 1)) < 2 := by
    apply (Nat.div_lt_iff_lt_mul (pow2_pos (f.width - 1))).mpr
    rw [Nat.mul_comm, ← pow2_succ, format_width_succ]
    exact hBits
  have hSignEq :
      (!Nat.beq (Nat.div bits (pow2 (f.width - 1))) 0) =
        Nat.beq (Nat.mod (Nat.div bits (pow2 (f.width - 1))) 2) 1 := by
    cases hD : Nat.div bits (pow2 (f.width - 1)) with
    | zero => rfl
    | succ k =>
      rw [hD] at hTopLt2
      have hk0 : k = 0 := Nat.eq_zero_of_le_zero
        (Nat.le_of_lt_succ (Nat.lt_of_succ_lt_succ hTopLt2))
      subst hk0
      rfl
  rw [hSignEq]
  cases Nat.beq (Nat.mod (Nat.div bits (pow2 f.fractionBits)) (pow2 f.exponentBits))
      f.allOnesExp with
  | true =>
    cases Nat.beq (Nat.mod bits (pow2 f.fractionBits)) 0 <;> rfl
  | false =>
    cases Nat.beq (Nat.mod (Nat.div bits (pow2 f.fractionBits)) (pow2 f.exponentBits)) 0 with
    | false => rfl
    | true =>
      cases hF0 : Nat.beq (Nat.mod bits (pow2 f.fractionBits)) 0 with
      | false => rfl
      | true =>
        have hFracZero : Nat.mod bits (pow2 f.fractionBits) = 0 :=
          (natBeq_iff_eq_sf _ 0).mp hF0
        rw [hFracZero]
        cases f <;> rfl

end Anneal.Float

end
