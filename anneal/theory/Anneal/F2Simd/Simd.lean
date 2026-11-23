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
public import Init.Data.Nat.Basic
public import Init.Data.Nat.Bitwise.Basic
public import Init.Data.Nat.Div.Basic
public import Anneal.BitVec
public import Anneal.F2Simd.Basis

public section

namespace Anneal.F2Simd

open Anneal.BitVec

/-!
# Carryless Multiply & SIMD Byte-Shuffle Algebra (`Anneal.F2Simd.Simd`)

Foundation-locked (`prelude` + `foundation-lock.json` + `Anneal.BitVec`)
models and $\mathbb{F}_2$-linearity / $\mathbb{F}_2$-bilinearity proofs for:

1. **GMP-accelerated carryless polynomial multiplication (`clmulNatAux`,
   `clmul`, `clmulBvAux`, `clmul_eq_clmulBvAux`, `clmul_isBilinear`,
   `clmulKaratsuba64`, `clmulKaratsuba64_isBilinear`):** Evaluates carryless
   multiplication in native C++ GMP `Nat` bit arithmetic (`Nat.xor` /
   `Nat.shiftLeft`) with one final `BitVec.ofNat` wrap, proved extensionally
   equal to the bit-by-bit `BitVec` shift-and-XOR loop so both `IsF2Bilinear`
   proofs and 4,096-point `rfl` kernel checks stay compact and fast.
2. **Width-parametric SIMD lane packing (`getLane`, `packLanesAux`,
   `packLanes`, `checkUniformSimdLanes_sound`):** Reduces `numLanes`-wide
   uniform SIMD equivalence over `BitVec (numLanes * laneW)` to `laneW`
   unit-basis checks.
3. **128-bit `vpshufb` byte permutes & split-nibble $\text{GF}(2^8)$ SIMD
   lookup (`vpshufb128`, `vpshufb128_constCtrl_isLinear`, `checkLut16Linear`,
   `gf256SimdVpshufb128`, `gf256SimdVpshufb128_isLinear`, `gf256MulConstByte`,
   `gf256MulConstSimd128`, `gf256MulConstSimd128_isLinear`):** Proves constant
   control `vpshufb128` unconditionally $\mathbb{F}_2$-linear and certifies
   data-dependent 16-byte split-nibble $\text{GF}(2^8)$ lookup tables linear
   from a 16×16 LUT check.
-/

/-! ## 1. GMP Carryless Polynomial Multiplication & Karatsuba Decomposition -/

/-- Raw `Nat` carryless polynomial multiplication over the low `n` bits of `y`
using `@Nat.rec` (`Nat.xor` and `Nat.shiftLeft` run in C++ GMP). -/
@[expose]
def clmulNatAux (x y n : Nat) : Nat :=
  @Nat.rec (fun _ => Nat)
    0
    (fun i prev =>
      match y.testBit i with
      | false => prev
      | true  => Nat.xor prev (Nat.shiftLeft x i))
    n

/-- Arbitrary-width carryless polynomial multiplication modulo `2^wOut`
(keeping the low `wOut` bits when `wOut < 2 * w - 1`; `pclmulqdq` at `w = 64`,
`wOut = 128`), short-circuiting immediately when either operand is zero so
multi-limb Karatsuba subproducts skip zero limbs in `O(1)`. -/
@[expose]
def clmul (w wOut : Nat) (x y : BitVec w) : BitVec wOut :=
  if Nat.beq x.toNat 0 || Nat.beq y.toNat 0 then bvZero wOut
  else BitVec.ofNat wOut (clmulNatAux x.toNat y.toNat w)

/-- Bit-vector shift-and-XOR reference loop for carryless multiplication,
defined via `@Nat.rec`. -/
@[expose]
def clmulBvAux {wOut wY : Nat} (x : BitVec wOut) (y : BitVec wY)
    (n : Nat) : BitVec wOut :=
  @Nat.rec (fun _ => BitVec wOut)
    (bvZero wOut)
    (fun i prev =>
      match getLsbD y i with
      | false => prev
      | true  => xor prev (shl x i))
    n

private theorem nat_lt_two_pow_self : ∀ n : Nat, n < Nat.pow 2 n
  | 0 => Nat.zero_lt_one
  | m + 1 => by
    have hps : Nat.pow 2 (m + 1) = Nat.pow 2 m * 2 := Nat.pow_succ 2 m
    rw [hps, Nat.mul_succ, Nat.mul_one]
    exact Nat.add_le_add (nat_lt_two_pow_self m) (Nat.two_pow_pos m)

private theorem nat_testBit_xor_eq (a b k : Nat) :
    (Nat.xor a b).testBit k = (a.testBit k != b.testBit k) := by
  let W := a + b + 1
  have hA : a < Nat.pow 2 W :=
    Nat.lt_trans (Nat.lt_succ_of_le (Nat.le_add_right a b))
      (nat_lt_two_pow_self W)
  have hB : b < Nat.pow 2 W :=
    Nat.lt_trans (Nat.lt_succ_of_le (Nat.le_add_left b a))
      (nat_lt_two_pow_self W)
  exact getLsbD_xor (BitVec.ofNatLT a hA) (BitVec.ofNatLT b hB) k

private theorem nat_testBit_shiftLeft_eq (x i k : Nat) :
    (Nat.shiftLeft x i).testBit k = (decide (i ≤ k) && x.testBit (k - i)) := by
  let s := Nat.shiftLeft x i
  let W := s + x + k + 1
  have hS : s < Nat.pow 2 W :=
    Nat.lt_trans
      (Nat.lt_succ_of_le
        (Nat.le_trans (Nat.le_add_right s x) (Nat.le_add_right _ k)))
      (nat_lt_two_pow_self W)
  have hX : x < Nat.pow 2 W :=
    Nat.lt_trans
      (Nat.lt_succ_of_le
        (Nat.le_trans (Nat.le_add_left x s) (Nat.le_add_right _ k)))
      (nat_lt_two_pow_self W)
  have hkW : k < W :=
    Nat.lt_succ_of_le (Nat.le_add_left k (s + x))
  have hShl := getLsbD_shl (BitVec.ofNatLT x hX) i k
  have hm : Nat.mod s (Nat.pow 2 W) = s := Nat.mod_eq_of_lt hS
  unfold getLsbD at hShl
  rw [toNat_shl, toNat_ofNatLT, hm, decide_eq_true hkW, Bool.true_and] at hShl
  exact hShl

private theorem clmulNatAux_testBit_eq {w wOut : Nat} (x y : BitVec w)
    {k : Nat} (hk : k < wOut) :
    ∀ n : Nat,
      (clmulNatAux x.toNat y.toNat n).testBit k =
        getLsbD (clmulBvAux (setWidth wOut x) y n) k
  | 0 => by
    change (0 : Nat).testBit k = getLsbD (bvZero wOut) k
    have h0 : (0 : Nat).testBit k = false := getLsbD_zero 1 k
    rw [h0, bvZero, getLsbD_zero]
  | i + 1 => by
    change (match y.toNat.testBit i with
      | false => clmulNatAux x.toNat y.toNat i
      | true  => Nat.xor (clmulNatAux x.toNat y.toNat i)
                   (Nat.shiftLeft x.toNat i)).testBit k =
      getLsbD (match getLsbD y i with
      | false => clmulBvAux (setWidth wOut x) y i
      | true  => xor (clmulBvAux (setWidth wOut x) y i)
                   (shl (setWidth wOut x) i)) k
    have hy : y.toNat.testBit i = getLsbD y i := rfl
    rw [hy]
    cases getLsbD y i with
    | false => exact clmulNatAux_testBit_eq x y hk i
    | true =>
      dsimp only
      rw [nat_testBit_xor_eq, getLsbD_xor, clmulNatAux_testBit_eq x y hk i,
        nat_testBit_shiftLeft_eq, getLsbD_shl, decide_eq_true hk,
        Bool.true_and, getLsbD_setWidth]
      have hSubLt : k - i < wOut := Nat.lt_of_le_of_lt (Nat.sub_le k i) hk
      rw [decide_eq_true hSubLt, Bool.true_and]
      rfl

private theorem clmulBvAux_zero_left {wOut wY : Nat} (y : BitVec wY) :
    ∀ n : Nat, clmulBvAux (bvZero wOut) y n = bvZero wOut
  | 0 => rfl
  | i + 1 => by
    change (match getLsbD y i with
      | false => clmulBvAux (bvZero wOut) y i
      | true  => xor (clmulBvAux (bvZero wOut) y i) (shl (bvZero wOut) i)) =
      bvZero wOut
    rw [clmulBvAux_zero_left y i, shl_bvZero]
    cases getLsbD y i with
    | false => rfl
    | true => exact xor_zero (bvZero wOut)

private theorem clmulBvAux_zero_right {wOut wY : Nat} (x : BitVec wOut) :
    ∀ n : Nat, clmulBvAux x (bvZero wY) n = bvZero wOut
  | 0 => rfl
  | i + 1 => by
    change (match getLsbD (bvZero wY) i with
      | false => clmulBvAux x (bvZero wY) i
      | true  => xor (clmulBvAux x (bvZero wY) i) (shl x i)) = bvZero wOut
    rw [bvZero, getLsbD_zero]
    exact clmulBvAux_zero_right x i

/-- Extensional equivalence between GMP `clmul` and bit-vector `clmulBvAux`. -/
theorem clmul_eq_clmulBvAux (w wOut : Nat) (x y : BitVec w) :
    clmul w wOut x y = clmulBvAux (setWidth wOut x) y w := by
  unfold clmul
  cases hx0 : Nat.beq x.toNat 0 with
  | true =>
    have hOr : (true || Nat.beq y.toNat 0) = true := rfl
    have hIf :
        (if true = true then bvZero wOut
         else BitVec.ofNat wOut (clmulNatAux x.toNat y.toNat w)) =
        bvZero wOut := rfl
    rw [hOr, hIf]
    have hxEq : x = bvZero w := by
      apply eq_of_toNat_eq
      rw [Nat.eq_of_beq_eq_true hx0, bvZero, toNat_zero]
    rw [hxEq, setWidth_bvZero]
    exact Eq.symm (clmulBvAux_zero_left y w)
  | false =>
    have hOr : (false || Nat.beq y.toNat 0) = Nat.beq y.toNat 0 := rfl
    rw [hOr]
    cases hy0 : Nat.beq y.toNat 0 with
    | true =>
      have hIf :
          (if true = true then bvZero wOut
           else BitVec.ofNat wOut (clmulNatAux x.toNat y.toNat w)) =
          bvZero wOut := rfl
      rw [hIf]
      have hyEq : y = bvZero w := by
        apply eq_of_toNat_eq
        rw [Nat.eq_of_beq_eq_true hy0, bvZero, toNat_zero]
      rw [hyEq]
      exact Eq.symm (clmulBvAux_zero_right (setWidth wOut x) w)
    | false =>
      have hIf :
          (if false = true then bvZero wOut
           else BitVec.ofNat wOut (clmulNatAux x.toNat y.toNat w)) =
          BitVec.ofNat wOut (clmulNatAux x.toNat y.toNat w) := rfl
      rw [hIf]
      apply eq_of_getLsbD_eq
      intro k hk
      rw [getLsbD_ofNat, decide_eq_true hk, Bool.true_and]
      exact clmulNatAux_testBit_eq x y hk w

private theorem clmulBvAux_xor_left {wOut wY : Nat} (x1 x2 : BitVec wOut)
    (y : BitVec wY) :
    ∀ n : Nat,
      clmulBvAux (xor x1 x2) y n =
        xor (clmulBvAux x1 y n) (clmulBvAux x2 y n)
  | 0 => Eq.symm (xor_zero (bvZero wOut))
  | i + 1 => by
    change (match getLsbD y i with
      | false => clmulBvAux (xor x1 x2) y i
      | true  => xor (clmulBvAux (xor x1 x2) y i) (shl (xor x1 x2) i)) =
      xor (match getLsbD y i with
      | false => clmulBvAux x1 y i
      | true  => xor (clmulBvAux x1 y i) (shl x1 i))
          (match getLsbD y i with
      | false => clmulBvAux x2 y i
      | true  => xor (clmulBvAux x2 y i) (shl x2 i))
    rw [clmulBvAux_xor_left x1 x2 y i]
    cases getLsbD y i with
    | false => rfl
    | true =>
      dsimp only
      rw [shl_xor_distrib]
      exact xor_four_rearrange _ _ _ _

private theorem clmulBvAux_xor_right {wOut wY : Nat} (x : BitVec wOut)
    (y1 y2 : BitVec wY) :
    ∀ n : Nat,
      clmulBvAux x (xor y1 y2) n =
        xor (clmulBvAux x y1 n) (clmulBvAux x y2 n)
  | 0 => Eq.symm (xor_zero (bvZero wOut))
  | i + 1 => by
    change (match getLsbD (xor y1 y2) i with
      | false => clmulBvAux x (xor y1 y2) i
      | true  => xor (clmulBvAux x (xor y1 y2) i) (shl x i)) =
      xor (match getLsbD y1 i with
      | false => clmulBvAux x y1 i
      | true  => xor (clmulBvAux x y1 i) (shl x i))
          (match getLsbD y2 i with
      | false => clmulBvAux x y2 i
      | true  => xor (clmulBvAux x y2 i) (shl x i))
    rw [clmulBvAux_xor_right x y1 y2 i, getLsbD_xor]
    cases getLsbD y1 i <;> cases getLsbD y2 i
    · rfl
    · have hb : (false != true) = true := rfl
      rw [hb]; dsimp only
      exact xor_assoc _ _ _
    · have hb : (true != false) = true := rfl
      rw [hb]; dsimp only
      rw [xor_assoc, xor_comm (clmulBvAux x y2 i) (shl x i), ← xor_assoc]
    · have hb : (true != true) = false := rfl
      rw [hb]; dsimp only
      rw [xor_four_rearrange (clmulBvAux x y1 i) (shl x i)
            (clmulBvAux x y2 i) (shl x i),
          xor_self, xor_zero]

/-- Arbitrary-width `clmul w wOut` is $\mathbb{F}_2$-bilinear. -/
theorem clmul_isBilinear (w wOut : Nat) : IsF2Bilinear (clmul w wOut) where
  zero_left := fun y => by
    rw [clmul_eq_clmulBvAux, setWidth_bvZero]
    exact clmulBvAux_zero_left y w
  xor_left := fun a1 a2 y => by
    rw [clmul_eq_clmulBvAux, clmul_eq_clmulBvAux, clmul_eq_clmulBvAux,
      setWidth_xor_distrib]
    exact clmulBvAux_xor_left _ _ y w
  zero_right := fun x => by
    rw [clmul_eq_clmulBvAux]
    exact clmulBvAux_zero_right _ w
  xor_right := fun x b1 b2 => by
    rw [clmul_eq_clmulBvAux, clmul_eq_clmulBvAux, clmul_eq_clmulBvAux]
    exact clmulBvAux_xor_right _ b1 b2 w

/-- Three-multiply 64×64 → 128-bit Karatsuba carryless polynomial multiplication
built from three 32×32 → 64-bit `clmul` calls. -/
@[expose]
def clmulKaratsuba64 (x y : BitVec 64) : BitVec 128 :=
  let xLo : BitVec 32 := extractLsb 0 32 x
  let xHi : BitVec 32 := extractLsb 32 32 x
  let yLo : BitVec 32 := extractLsb 0 32 y
  let yHi : BitVec 32 := extractLsb 32 32 y
  let z0 : BitVec 128 := setWidth 128 (clmul 32 64 xLo yLo)
  let zHi : BitVec 128 := setWidth 128 (clmul 32 64 xHi yHi)
  let zMid : BitVec 128 :=
    setWidth 128 (clmul 32 64 (xor xLo xHi) (xor yLo yHi))
  let z1 : BitVec 128 := shl (xor (xor zMid z0) zHi) 32
  let z2 : BitVec 128 := shl zHi 64
  xor (xor z0 z1) z2

private theorem karatsuba_xor_rearrange {w : Nat}
    (z0a z0b zHa zHb zMa zMb : BitVec w) :
    xor (xor (xor z0a z0b)
          (shl (xor (xor (xor zMa zMb) (xor z0a z0b)) (xor zHa zHb)) 32))
        (shl (xor zHa zHb) 64) =
      xor (xor (xor z0a (shl (xor (xor zMa z0a) zHa) 32)) (shl zHa 64))
          (xor (xor z0b (shl (xor (xor zMb z0b) zHb) 32)) (shl zHb 64)) := by
  rw [xor_six_rearrange zMa zMb z0a z0b zHa zHb,
    shl_xor_distrib _ _ 32, shl_xor_distrib _ _ 64]
  exact xor_six_rearrange _ _ _ _ _ _

/-- `clmulKaratsuba64` is $\mathbb{F}_2$-bilinear. -/
theorem clmulKaratsuba64_isBilinear : IsF2Bilinear clmulKaratsuba64 where
  zero_left := fun y => by
    unfold clmulKaratsuba64
    dsimp only
    have hb := clmul_isBilinear 32 64
    have hz32 : xor (bvZero 32) (bvZero 32) = bvZero 32 :=
      xor_zero (bvZero 32)
    have hz128 : xor (bvZero 128) (bvZero 128) = bvZero 128 :=
      xor_zero (bvZero 128)
    rw [extractLsb_bvZero, extractLsb_bvZero, hz32,
      hb.zero_left, hb.zero_left, hb.zero_left, setWidth_bvZero, hz128, hz128,
      shl_bvZero, shl_bvZero, hz128, hz128]
  xor_left := fun a1 a2 y => by
    unfold clmulKaratsuba64
    dsimp only
    have hb := clmul_isBilinear 32 64
    rw [extractLsb_xor_distrib 0 32 a1 a2, extractLsb_xor_distrib 32 32 a1 a2,
      xor_four_rearrange (extractLsb 0 32 a1) (extractLsb 0 32 a2)
        (extractLsb 32 32 a1) (extractLsb 32 32 a2)]
    have h0 := hb.xor_left (extractLsb 0 32 a1) (extractLsb 0 32 a2)
      (extractLsb 0 32 y)
    have h2 := hb.xor_left (extractLsb 32 32 a1) (extractLsb 32 32 a2)
      (extractLsb 32 32 y)
    have hM := hb.xor_left
      (xor (extractLsb 0 32 a1) (extractLsb 32 32 a1))
      (xor (extractLsb 0 32 a2) (extractLsb 32 32 a2))
      (xor (extractLsb 0 32 y) (extractLsb 32 32 y))
    rw [h0, h2, hM, setWidth_xor_distrib, setWidth_xor_distrib,
      setWidth_xor_distrib]
    exact karatsuba_xor_rearrange _ _ _ _ _ _
  zero_right := fun x => by
    unfold clmulKaratsuba64
    dsimp only
    have hb := clmul_isBilinear 32 64
    have hz32 : xor (bvZero 32) (bvZero 32) = bvZero 32 :=
      xor_zero (bvZero 32)
    have hz128 : xor (bvZero 128) (bvZero 128) = bvZero 128 :=
      xor_zero (bvZero 128)
    rw [extractLsb_bvZero, extractLsb_bvZero, hz32,
      hb.zero_right, hb.zero_right, hb.zero_right, setWidth_bvZero, hz128,
      hz128, shl_bvZero, shl_bvZero, hz128, hz128]
  xor_right := fun x b1 b2 => by
    unfold clmulKaratsuba64
    dsimp only
    have hb := clmul_isBilinear 32 64
    rw [extractLsb_xor_distrib 0 32 b1 b2, extractLsb_xor_distrib 32 32 b1 b2,
      xor_four_rearrange (extractLsb 0 32 b1) (extractLsb 0 32 b2)
        (extractLsb 32 32 b1) (extractLsb 32 32 b2)]
    have h0 := hb.xor_right (extractLsb 0 32 x)
      (extractLsb 0 32 b1) (extractLsb 0 32 b2)
    have h2 := hb.xor_right (extractLsb 32 32 x)
      (extractLsb 32 32 b1) (extractLsb 32 32 b2)
    have hM := hb.xor_right
      (xor (extractLsb 0 32 x) (extractLsb 32 32 x))
      (xor (extractLsb 0 32 b1) (extractLsb 32 32 b1))
      (xor (extractLsb 0 32 b2) (extractLsb 32 32 b2))
    rw [h0, h2, hM, setWidth_xor_distrib, setWidth_xor_distrib,
      setWidth_xor_distrib]
    exact karatsuba_xor_rearrange _ _ _ _ _ _

/-- Carryless multiplication of two unit-basis vectors `bvUnit w i` and
`bvUnit w j` (`i < w`, `j < w`) yields `bvUnit wOut (i + j)`. -/
theorem clmul_bvUnit {w wOut i j : Nat} (hi : i < w) (hj : j < w) :
    clmul w wOut (bvUnit w i) (bvUnit w j) = bvUnit wOut (i + j) := by
  have hLe : ∀ (x : BitVec wOut), ∀ n : Nat, n ≤ j →
      clmulBvAux x (bvUnit w j) n = bvZero wOut := by
    intro x n hnj
    induction n with
    | zero => rfl
    | succ k ih =>
      have hkLtJ : k < j := hnj
      have hkLtW : k < w := Nat.lt_trans hkLtJ hj
      change (match getLsbD (bvUnit w j) k with
        | false => clmulBvAux x (bvUnit w j) k
        | true  => xor (clmulBvAux x (bvUnit w j) k) (shl x k)) = bvZero wOut
      rw [getLsbD_bvUnit hkLtW, decide_eq_false (Nat.ne_of_lt hkLtJ)]
      exact ih (Nat.le_of_lt hkLtJ)
  have hGt : ∀ (x : BitVec wOut), ∀ n : Nat, j < n → n ≤ w →
      clmulBvAux x (bvUnit w j) n = shl x j := by
    intro x n hjn hnw
    induction n with
    | zero => nomatch hjn
    | succ k ih =>
      have hkLtW : k < w := hnw
      change (match getLsbD (bvUnit w j) k with
        | false => clmulBvAux x (bvUnit w j) k
        | true  => xor (clmulBvAux x (bvUnit w j) k) (shl x k)) = shl x j
      cases Nat.lt_or_eq_of_le (Nat.le_of_lt_succ hjn) with
      | inl hjLtK =>
        rw [getLsbD_bvUnit hkLtW, decide_eq_false (Nat.ne_of_gt hjLtK)]
        exact ih hjLtK (Nat.le_of_lt hkLtW)
      | inr hjEqK =>
        subst hjEqK
        rw [getLsbD_bvUnit hkLtW, decide_eq_true rfl]
        dsimp only
        rw [hLe x j (Nat.le_refl j), bvZero, zero_xor]
  rw [clmul_eq_clmulBvAux,
    hGt (setWidth wOut (bvUnit w i)) w hj (Nat.le_refl w),
    setWidth_bvUnit hi, shl_bvUnit]

private theorem sub_32_lt_32 {k : Nat} (hk32 : 32 ≤ k) (hk64 : k < 64) :
    k - 32 < 32 :=
  Nat.sub_lt_left_of_lt_add hk32 hk64

/-- Carryless Karatsuba multiplication of two 64-bit unit-basis vectors
`bvUnit 64 i` and `bvUnit 64 j` (`i < 64`, `j < 64`) yields
`bvUnit 128 (i + j)`. -/
theorem clmulKaratsuba64_bvUnit {i j : Nat} (hi : i < 64) (hj : j < 64) :
    clmulKaratsuba64 (bvUnit 64 i) (bvUnit 64 j) = bvUnit 128 (i + j) := by
  unfold clmulKaratsuba64
  dsimp only
  have hb := clmul_isBilinear 32 64
  have hZL : ∀ y : BitVec 32, clmul 32 64 (BitVec.ofNat 32 0) y = BitVec.ofNat 64 0 :=
    hb.zero_left
  have hZR : ∀ x : BitVec 32, clmul 32 64 x (BitVec.ofNat 32 0) = BitVec.ofNat 64 0 :=
    hb.zero_right
  have h128 : setWidth 128 (BitVec.ofNat 64 0) = BitVec.ofNat 128 0 :=
    setWidth_bvZero 64 128
  have hShl32 : shl (BitVec.ofNat 128 0) 32 = BitVec.ofNat 128 0 :=
    shl_bvZero 128 32
  have hShl64 : shl (BitVec.ofNat 128 0) 64 = BitVec.ofNat 128 0 :=
    shl_bvZero 128 64
  cases Nat.lt_or_ge i 32 with
  | inl hiLo =>
    have hxLo : extractLsb 0 32 (bvUnit 64 i) = bvUnit 32 i :=
      extractLsb_bvUnit_lt (Nat.zero_le i) hi
    have hxHi : extractLsb 32 32 (bvUnit 64 i) = BitVec.ofNat 32 0 :=
      extractLsb_bvUnit_outside (Or.inl hiLo)
    rw [hxLo, hxHi, xor_zero]
    cases Nat.lt_or_ge j 32 with
    | inl hjLo =>
      have hyLo : extractLsb 0 32 (bvUnit 64 j) = bvUnit 32 j :=
        extractLsb_bvUnit_lt (Nat.zero_le j) hj
      have hyHi : extractLsb 32 32 (bvUnit 64 j) = BitVec.ofNat 32 0 :=
        extractLsb_bvUnit_outside (Or.inl hjLo)
      rw [hyLo, hyHi, xor_zero]
      change xor (xor (setWidth 128 (clmul 32 64 (bvUnit 32 i) (bvUnit 32 j)))
        (shl (xor (xor (setWidth 128 (clmul 32 64 (bvUnit 32 i) (bvUnit 32 j)))
            (setWidth 128 (clmul 32 64 (bvUnit 32 i) (bvUnit 32 j))))
            (setWidth 128 (clmul 32 64 (BitVec.ofNat 32 0) (BitVec.ofNat 32 0)))) 32))
        (shl (setWidth 128 (clmul 32 64 (BitVec.ofNat 32 0) (BitVec.ofNat 32 0))) 64) =
        bvUnit 128 (i + j)
      rw [hZL, h128, clmul_bvUnit hiLo hjLo,
        setWidth_bvUnit (Nat.add_lt_add hiLo hjLo),
        xor_self, zero_xor, hShl32, xor_zero, hShl64, xor_zero]
    | inr hjHi =>
      have hyLo : extractLsb 0 32 (bvUnit 64 j) = BitVec.ofNat 32 0 :=
        extractLsb_bvUnit_outside (Or.inr hjHi)
      have hyHi : extractLsb 32 32 (bvUnit 64 j) = bvUnit 32 (j - 32) :=
        extractLsb_bvUnit_lt hjHi hj
      have hjSub : j - 32 < 32 := sub_32_lt_32 hjHi hj
      rw [hyLo, hyHi, zero_xor]
      change xor (xor (setWidth 128 (clmul 32 64 (bvUnit 32 i) (BitVec.ofNat 32 0)))
        (shl (xor (xor (setWidth 128 (clmul 32 64 (bvUnit 32 i) (bvUnit 32 (j - 32))))
            (setWidth 128 (clmul 32 64 (bvUnit 32 i) (BitVec.ofNat 32 0))))
            (setWidth 128 (clmul 32 64 (BitVec.ofNat 32 0) (bvUnit 32 (j - 32))))) 32))
        (shl (setWidth 128 (clmul 32 64 (BitVec.ofNat 32 0) (bvUnit 32 (j - 32)))) 64) =
        bvUnit 128 (i + j)
      rw [hZR, hZL, h128,
        clmul_bvUnit hiLo hjSub,
        setWidth_bvUnit (Nat.add_lt_add hiLo hjSub),
        xor_zero, zero_xor, hShl64, xor_zero, xor_zero, shl_bvUnit,
        Nat.add_assoc, Nat.sub_add_cancel hjHi]
  | inr hiHi =>
    have hxLo : extractLsb 0 32 (bvUnit 64 i) = BitVec.ofNat 32 0 :=
      extractLsb_bvUnit_outside (Or.inr hiHi)
    have hxHi : extractLsb 32 32 (bvUnit 64 i) = bvUnit 32 (i - 32) :=
      extractLsb_bvUnit_lt hiHi hi
    have hiSub : i - 32 < 32 := sub_32_lt_32 hiHi hi
    rw [hxLo, hxHi, zero_xor]
    cases Nat.lt_or_ge j 32 with
    | inl hjLo =>
      have hyLo : extractLsb 0 32 (bvUnit 64 j) = bvUnit 32 j :=
        extractLsb_bvUnit_lt (Nat.zero_le j) hj
      have hyHi : extractLsb 32 32 (bvUnit 64 j) = BitVec.ofNat 32 0 :=
        extractLsb_bvUnit_outside (Or.inl hjLo)
      rw [hyLo, hyHi, xor_zero]
      change xor (xor (setWidth 128 (clmul 32 64 (BitVec.ofNat 32 0) (bvUnit 32 j)))
        (shl (xor (xor (setWidth 128 (clmul 32 64 (bvUnit 32 (i - 32)) (bvUnit 32 j)))
            (setWidth 128 (clmul 32 64 (BitVec.ofNat 32 0) (bvUnit 32 j))))
            (setWidth 128 (clmul 32 64 (bvUnit 32 (i - 32)) (BitVec.ofNat 32 0)))) 32))
        (shl (setWidth 128 (clmul 32 64 (bvUnit 32 (i - 32)) (BitVec.ofNat 32 0))) 64) =
        bvUnit 128 (i + j)
      rw [hZL, hZR, h128,
        clmul_bvUnit hiSub hjLo,
        setWidth_bvUnit (Nat.add_lt_add hiSub hjLo),
        xor_zero, zero_xor, hShl64, xor_zero, xor_zero, shl_bvUnit,
        Nat.add_right_comm, Nat.sub_add_cancel hiHi]
    | inr hjHi =>
      have hyLo : extractLsb 0 32 (bvUnit 64 j) = BitVec.ofNat 32 0 :=
        extractLsb_bvUnit_outside (Or.inr hjHi)
      have hyHi : extractLsb 32 32 (bvUnit 64 j) = bvUnit 32 (j - 32) :=
        extractLsb_bvUnit_lt hjHi hj
      have hjSub : j - 32 < 32 := sub_32_lt_32 hjHi hj
      rw [hyLo, hyHi, zero_xor]
      change xor (xor (setWidth 128 (clmul 32 64 (BitVec.ofNat 32 0) (BitVec.ofNat 32 0)))
        (shl (xor (xor (setWidth 128 (clmul 32 64 (bvUnit 32 (i - 32)) (bvUnit 32 (j - 32))))
            (setWidth 128 (clmul 32 64 (BitVec.ofNat 32 0) (BitVec.ofNat 32 0))))
            (setWidth 128 (clmul 32 64 (bvUnit 32 (i - 32)) (bvUnit 32 (j - 32))))) 32))
        (shl (setWidth 128 (clmul 32 64 (bvUnit 32 (i - 32)) (bvUnit 32 (j - 32)))) 64) =
        bvUnit 128 (i + j)
      rw [hZL, h128,
        clmul_bvUnit hiSub hjSub,
        setWidth_bvUnit (Nat.add_lt_add hiSub hjSub),
        xor_zero, xor_self, hShl32, xor_zero, zero_xor,
        shl_bvUnit]
      have hSum : (i - 32) + (j - 32) + 64 = i + j := by
        have h64 : (64 : Nat) = 32 + 32 := rfl
        rw [h64, ← Nat.add_assoc, Nat.add_right_comm (i - 32) (j - 32) 32,
          Nat.sub_add_cancel hiHi, Nat.add_assoc, Nat.sub_add_cancel hjHi]
      rw [hSum]

/-! ## 2. Width-Parametric SIMD Lane Packing & Uniform Lane Reduction -/

/-- Extracts `laneW`-bit lane `i` (`extractLsb (laneW * i) laneW v`) from a
wide register `v : BitVec w`. -/
@[expose]
def getLane {w : Nat} (laneW : Nat) (v : BitVec w) (i : Nat) : BitVec laneW :=
  extractLsb (laneW * i) laneW v

/-- Packs the first `n` `laneW`-bit lanes (`f 0` at LSB .. `f (n - 1)` at MSB)
into `BitVec wOut` via `@Nat.rec`. -/
@[expose]
def packLanesAux (wOut laneW : Nat) (f : Nat → BitVec laneW)
    (n : Nat) : BitVec wOut :=
  @Nat.rec (fun _ => BitVec wOut)
    (bvZero wOut)
    (fun k prev => xor prev (shl (setWidth wOut (f k)) (laneW * k)))
    n

/-- Packs `numLanes` `laneW`-bit lanes into `BitVec (numLanes * laneW)`. -/
@[expose]
def packLanes (numLanes laneW : Nat) (f : Nat → BitVec laneW) :
    BitVec (numLanes * laneW) :=
  packLanesAux (numLanes * laneW) laneW f numLanes

/-- Extracting any lane from `bvZero w` yields `bvZero laneW`. -/
theorem getLane_zero (w laneW i : Nat) :
    getLane laneW (bvZero w) i = bvZero laneW :=
  extractLsb_bvZero w (laneW * i) laneW

/-- `getLane` distributes over `xor`. -/
theorem getLane_xor {w : Nat} (laneW : Nat) (a b : BitVec w) (i : Nat) :
    getLane laneW (xor a b) i = xor (getLane laneW a i) (getLane laneW b i) :=
  extractLsb_xor_distrib (laneW * i) laneW a b

/-- `packLanesAux` of identically zero lanes is `bvZero wOut`. -/
theorem packLanesAux_zero (wOut laneW : Nat) (f : Nat → BitVec laneW)
    (hf : ∀ i, f i = bvZero laneW) :
    ∀ n : Nat, packLanesAux wOut laneW f n = bvZero wOut
  | 0 => rfl
  | k + 1 => by
    change xor (packLanesAux wOut laneW f k)
      (shl (setWidth wOut (f k)) (laneW * k)) = bvZero wOut
    rw [packLanesAux_zero wOut laneW f hf k, hf k, setWidth_bvZero, shl_bvZero,
      bvZero, xor_zero]

/-- `packLanesAux` distributes pointwise over lane `xor`. -/
theorem packLanesAux_xor (wOut laneW : Nat) (f g : Nat → BitVec laneW) :
    ∀ n : Nat,
      packLanesAux wOut laneW (fun i => xor (f i) (g i)) n =
        xor (packLanesAux wOut laneW f n) (packLanesAux wOut laneW g n)
  | 0 => Eq.symm (xor_zero (bvZero wOut))
  | k + 1 => by
    change xor (packLanesAux wOut laneW (fun i => xor (f i) (g i)) k)
      (shl (setWidth wOut (xor (f k) (g k))) (laneW * k)) =
      xor (xor (packLanesAux wOut laneW f k)
               (shl (setWidth wOut (f k)) (laneW * k)))
          (xor (packLanesAux wOut laneW g k)
               (shl (setWidth wOut (g k)) (laneW * k)))
    rw [packLanesAux_xor wOut laneW f g k, setWidth_xor_distrib,
      shl_xor_distrib]
    exact xor_four_rearrange _ _ _ _

/-- Pointwise congruence for `packLanesAux` on indices `i < n`. -/
theorem packLanesAux_congr {wOut laneW : Nat} {f g : Nat → BitVec laneW} :
    ∀ {n : Nat}, (∀ i, i < n → f i = g i) →
      packLanesAux wOut laneW f n = packLanesAux wOut laneW g n
  | 0, _ => rfl
  | k + 1, hfg => by
    change xor (packLanesAux wOut laneW f k)
      (shl (setWidth wOut (f k)) (laneW * k)) =
      xor (packLanesAux wOut laneW g k)
      (shl (setWidth wOut (g k)) (laneW * k))
    rw [packLanesAux_congr (fun i hi => hfg i (Nat.lt_succ_of_lt hi)),
      hfg k (Nat.lt_succ_self k)]

private theorem packLanesAux_bit_above {wOut laneW : Nat}
    (f : Nat → BitVec laneW) {i k : Nat} (hk : k < laneW)
    (hIn : k + laneW * i < wOut) :
    ∀ {m : Nat}, m ≤ i →
      getLsbD (packLanesAux wOut laneW f m) (k + laneW * i) = false
  | 0, _ => by
    change getLsbD (bvZero wOut) (k + laneW * i) = false
    exact getLsbD_zero wOut _
  | m + 1, hmLe => by
    change getLsbD
      (xor (packLanesAux wOut laneW f m)
           (shl (setWidth wOut (f m)) (laneW * m)))
      (k + laneW * i) = false
    rw [getLsbD_xor,
      packLanesAux_bit_above f hk hIn (Nat.le_of_succ_le hmLe),
      getLsbD_shl, decide_eq_true hIn, Bool.true_and]
    have hmLeI : laneW * m ≤ laneW * i :=
      Nat.mul_le_mul_left laneW (Nat.le_of_succ_le hmLe)
    have hGe : laneW * m ≤ k + laneW * i :=
      Nat.le_trans hmLeI (Nat.le_add_left (laneW * i) k)
    rw [decide_eq_true hGe, Bool.true_and, getLsbD_setWidth]
    have hDiffGe : laneW ≤ (k + laneW * i) - laneW * m := by
      have hdPos : 1 ≤ i - m := Nat.zero_lt_sub_of_lt hmLe
      have hMul : laneW * 1 ≤ laneW * (i - m) :=
        Nat.mul_le_mul_left laneW hdPos
      rw [Nat.mul_one] at hMul
      have hEqI : i = m + (i - m) :=
        Eq.symm (Nat.add_sub_of_le (Nat.le_of_succ_le hmLe))
      have hExpand : k + laneW * i = (k + laneW * (i - m)) + laneW * m := by
        have h1 := congrArg (fun z => k + laneW * z) hEqI
        rw [Nat.mul_add, Nat.add_comm (laneW * m) (laneW * (i - m)),
          ← Nat.add_assoc] at h1
        exact h1
      rw [hExpand, Nat.add_sub_cancel]
      exact Nat.le_trans hMul (Nat.le_add_left _ k)
    rw [getLsbD_ge (f m) hDiffGe, Bool.and_false]
    rfl

private theorem packLanesAux_bit_in {wOut laneW : Nat}
    (f : Nat → BitVec laneW) {i k : Nat} (hk : k < laneW)
    (hIn : k + laneW * i < wOut) :
    ∀ {m : Nat}, i < m →
      getLsbD (packLanesAux wOut laneW f m) (k + laneW * i) =
        getLsbD (f i) k
  | 0, hiLt => nomatch hiLt
  | m + 1, hiLt => by
    change getLsbD
      (xor (packLanesAux wOut laneW f m)
           (shl (setWidth wOut (f m)) (laneW * m)))
      (k + laneW * i) = getLsbD (f i) k
    cases Nat.lt_or_eq_of_le (Nat.le_of_lt_succ hiLt) with
    | inl hLtM =>
      rw [getLsbD_xor, packLanesAux_bit_in f hk hIn hLtM, getLsbD_shl]
      have hNextLe : laneW * (i + 1) ≤ laneW * m :=
        Nat.mul_le_mul_left laneW hLtM
      have hkLtNext : k + laneW * i < laneW * (i + 1) := by
        rw [Nat.mul_succ, Nat.add_comm (laneW * i) laneW]
        exact Nat.add_lt_add_right hk (laneW * i)
      have hNotLe : ¬ (laneW * m ≤ k + laneW * i) :=
        Nat.not_le_of_gt (Nat.lt_of_lt_of_le hkLtNext hNextLe)
      rw [decide_eq_false hNotLe, Bool.false_and, Bool.and_false]
      cases getLsbD (f i) k <;> rfl
    | inr hEqM =>
      subst hEqM
      rw [getLsbD_xor, packLanesAux_bit_above f hk hIn (Nat.le_refl _),
        getLsbD_shl, decide_eq_true hIn, Bool.true_and,
        decide_eq_true (Nat.le_add_left (laneW * _) k), Bool.true_and,
        Nat.add_sub_cancel, getLsbD_setWidth]
      have hkLtW : k < wOut :=
        Nat.lt_of_le_of_lt (Nat.le_add_right k (laneW * _)) hIn
      rw [decide_eq_true hkLtW, Bool.true_and]
      cases getLsbD (f _) k <;> rfl

/-- Extracting lane `i < n` from `packLanesAux wOut laneW f n` recovers `f i`
whenever `(i + 1) * laneW ≤ wOut`. -/
theorem getLane_packLanesAux {wOut laneW n : Nat} (f : Nat → BitVec laneW)
    {i : Nat} (hi : i < n) (hFit : laneW * (i + 1) ≤ wOut) :
    getLane laneW (packLanesAux wOut laneW f n) i = f i := by
  apply eq_of_getLsbD_eq
  intro k hk
  unfold getLane
  rw [getLsbD_extractLsb, decide_eq_true hk, Bool.true_and]
  have hkLtNext : k + laneW * i < laneW * (i + 1) := by
    rw [Nat.mul_succ, Nat.add_comm (laneW * i) laneW]
    exact Nat.add_lt_add_right hk (laneW * i)
  exact packLanesAux_bit_in f hk (Nat.lt_of_lt_of_le hkLtNext hFit) hi

/-- Extracting lane `i < numLanes` from `packLanes numLanes laneW f` recovers
`f i`. -/
theorem getLane_packLanes {numLanes laneW : Nat} (f : Nat → BitVec laneW)
    {i : Nat} (hi : i < numLanes) :
    getLane laneW (packLanes numLanes laneW f) i = f i := by
  unfold packLanes
  have hFit : laneW * (i + 1) ≤ numLanes * laneW := by
    rw [Nat.mul_comm numLanes laneW]
    exact Nat.mul_le_mul_left laneW hi
  exact getLane_packLanesAux f hi hFit

/-- `getLane` distributes over bitwise `and`. -/
theorem getLane_and {w : Nat} (laneW : Nat) (a b : BitVec w) (i : Nat) :
    getLane laneW (and a b) i = and (getLane laneW a i) (getLane laneW b i) := by
  apply eq_of_getLsbD_eq
  intro k hk
  unfold getLane
  rw [getLsbD_extractLsb, getLsbD_and, getLsbD_and, getLsbD_extractLsb,
    getLsbD_extractLsb, decide_eq_true hk, Bool.true_and, Bool.true_and,
    Bool.true_and]

/-- Any lane-uniform map induced by `fLane : BitVec laneW → BitVec laneW` with
`IsF2Linear1 fLane` is `IsF2Linear1` on `BitVec (numLanes * laneW)`. -/
theorem packLanes_uniform_isLinear (numLanes laneW : Nat)
    {fLane : BitVec laneW → BitVec laneW} (hf : IsF2Linear1 fLane) :
    IsF2Linear1
      (fun v : BitVec (numLanes * laneW) =>
        packLanes numLanes laneW (fun i => fLane (getLane laneW v i)))
  where
  map_zero := by
    unfold packLanes
    apply packLanesAux_zero
    intro i
    rw [getLane_zero, hf.map_zero]
  map_xor := fun a b => by
    unfold packLanes
    rw [← packLanesAux_xor]
    apply packLanesAux_congr
    intro i _
    rw [getLane_xor, hf.map_xor]

/-- Uniform SIMD lane reduction: checking `laneW` unit-basis vectors on
`fLane` vs. `gLane` discharges universal `numLanes`-lane equivalence across all
`2 ^ (numLanes * laneW)` register values. -/
theorem checkUniformSimdLanes_sound (numLanes laneW : Nat)
    {fLane gLane : BitVec laneW → BitVec laneW}
    (hf : IsF2Linear1 fLane) (hg : IsF2Linear1 gLane)
    (hLaneCert : checkF2Linear1 fLane gLane = true) :
    ∀ v : BitVec (numLanes * laneW),
      packLanes numLanes laneW (fun i => fLane (getLane laneW v i)) =
      packLanes numLanes laneW (fun i => gLane (getLane laneW v i)) := by
  intro v
  unfold packLanes
  apply packLanesAux_congr
  intro i _
  exact checkF2Linear1_sound hf hg hLaneCert (getLane laneW v i)

/-! ## 3. 128-Bit `vpshufb` Permutes & Split-Nibble $\text{GF}(2^8)$ SIMD -/

/-- Extracts byte `i` (`0 ≤ i < 16`) from a 128-bit SIMD register. -/
@[expose]
def getByte128 (v : BitVec 128) (i : Nat) : BitVec 8 :=
  getLane 8 v i

/-- Packs 16 bytes (`f 0` at LSB .. `f 15` at MSB) into `BitVec 128`. -/
@[expose]
def packBytes128 (f : Nat → BitVec 8) : BitVec 128 :=
  packLanesAux 128 8 f 16

@[expose]
def vpshufb128NatAux (src ctrl : Nat) (n : Nat) : Nat :=
  @Nat.rec (fun _ => Nat)
    0
    (fun i prev =>
      let cb := Nat.mod (Nat.shiftRight ctrl (8 * i)) 256
      match Nat.ble 128 cb with
      | true  => prev
      | false =>
        let idx := Nat.mod cb 16
        let b := Nat.mod (Nat.shiftRight src (8 * idx)) 256
        Nat.xor prev (Nat.shiftLeft b (8 * i)))
    n

/-- x86 SSSE3 `pshufb` / AVX `vpshufb` 16-byte table lookup
`vpshufb128 src ctrl` on one 128-bit lane: for each lane `i ∈ [0, 16)`, if bit
`7` of control byte `i` is `1` then `0`, else byte `(ctrl_byte_i & 0x0f)` of
`src`, evaluated in native GMP `Nat` arithmetic with one final `BitVec.ofNat`
wrap. Arm A64 `TBL` (`vqtbl1q_u8`) coincides only when every control byte
satisfies `cb < 16 ∨ cb ≥ 128` (as holds in `gf256SimdVpshufb128` after `0x0f`
masking). -/
@[expose]
def vpshufb128 (src ctrl : BitVec 128) : BitVec 128 :=
  BitVec.ofNat 128 (vpshufb128NatAux src.toNat ctrl.toNat 16)

private theorem testBit7_eq_ble128 {b : Nat} (hb : b < 256) :
    b.testBit 7 = Nat.ble 128 b := by
  cases Nat.lt_or_ge b 128 with
  | inl hlt =>
    have hBle : Nat.ble 128 b = false := by
      cases hb1 : Nat.ble 128 b with
      | false => rfl
      | true => exact False.elim (Nat.not_lt_of_ge (Nat.le_of_ble_eq_true hb1) hlt)
    have h7 : Nat.pow 2 7 = 128 := rfl
    have hbPow : b < Nat.pow 2 7 := by rw [h7]; exact hlt
    have hBit : getLsbD (BitVec.ofNatLT b hbPow) 7 = false :=
      getLsbD_ge (BitVec.ofNatLT b hbPow) (Nat.le_refl 7)
    rw [hBle]
    exact hBit
  | inr hge =>
    have hBle : Nat.ble 128 b = true := Nat.ble_eq_true_of_le hge
    have h256 : (256 : Nat) = Nat.pow 2 8 := rfl
    have hbPow : b < Nat.pow 2 8 := by rw [← h256]; exact hb
    have h7 : Nat.pow 2 7 = 128 := rfl
    let bv : BitVec 8 := BitVec.ofNatLT b hbPow
    have hBit : b.testBit 7 = getLsbD (ushr bv 7) 0 := by
      rw [getLsbD_ushr, Nat.zero_add]
      rfl
    have hDivEq : (ushr bv 7).toNat = 1 := by
      have hsr : Nat.shiftRight b 7 = Nat.div b (Nat.pow 2 7) :=
        Nat.shiftRight_eq_div_pow b 7
      rw [toNat_ushr, toNat_ofNatLT, hsr, h7]
      have hGe1 : 1 ≤ Nat.div b 128 :=
        (Nat.le_div_iff_mul_le (by decide : 0 < 128)).mpr
          (by rw [Nat.one_mul]; exact hge)
      have hLt2 : Nat.div b 128 < 2 :=
        (Nat.div_lt_iff_lt_mul (by decide : 0 < 128)).mpr hb
      cases hd : Nat.div b 128 with
      | zero => rw [hd] at hGe1; exact False.elim (Nat.not_succ_le_zero 0 hGe1)
      | succ d =>
        cases d with
        | zero => rfl
        | succ d' =>
          rw [hd] at hLt2
          exact False.elim (Nat.not_lt_of_ge
            (Nat.succ_le_succ (Nat.succ_le_succ (Nat.zero_le d'))) hLt2)
    have hBit1 : getLsbD (ushr bv 7) 0 = true := by
      change (ushr bv 7).toNat.testBit 0 = true
      rw [hDivEq]
      rfl
    rw [hBit, hBit1, hBle]

private theorem vpshufb128_prefix_eq (src ctrl : BitVec 128) :
    ∀ n : Nat,
      BitVec.ofNat 128 (vpshufb128NatAux src.toNat ctrl.toNat n) =
        packLanesAux 128 8
          (fun i =>
            let cb := getByte128 ctrl i
            match getLsbD cb 7 with
            | true  => bvZero 8
            | false => getByte128 src ((and cb (BitVec.ofNat 8 0x0f)).toNat))
          n
  | 0 => rfl
  | k + 1 => by
    let f := fun i =>
      let cb := getByte128 ctrl i
      match getLsbD cb 7 with
      | true  => bvZero 8
      | false => getByte128 src ((and cb (BitVec.ofNat 8 0x0f)).toNat)
    have ih := vpshufb128_prefix_eq src ctrl k
    change BitVec.ofNat 128
      (match Nat.ble 128 (Nat.mod (Nat.shiftRight ctrl.toNat (8 * k)) 256) with
       | true  => vpshufb128NatAux src.toNat ctrl.toNat k
       | false =>
         Nat.xor (vpshufb128NatAux src.toNat ctrl.toNat k)
           (Nat.shiftLeft
             (Nat.mod (Nat.shiftRight src.toNat
               (8 * Nat.mod (Nat.mod (Nat.shiftRight ctrl.toNat (8 * k)) 256) 16))
               256)
             (8 * k))) =
      xor (packLanesAux 128 8 f k) (shl (setWidth 128 (f k)) (8 * k))
    rw [← ih]
    let cbBv := getByte128 ctrl k
    have hcbNat : cbBv.toNat = Nat.mod (Nat.shiftRight ctrl.toNat (8 * k)) 256 := rfl
    have hcbBit : getLsbD cbBv 7 =
        Nat.ble 128 (Nat.mod (Nat.shiftRight ctrl.toNat (8 * k)) 256) := by
      rw [← hcbNat]
      exact testBit7_eq_ble128 cbBv.isLt
    have hfk : f k =
        match Nat.ble 128 (Nat.mod (Nat.shiftRight ctrl.toNat (8 * k)) 256) with
        | true  => bvZero 8
        | false =>
          getByte128 src
            (Nat.mod (Nat.mod (Nat.shiftRight ctrl.toNat (8 * k)) 256) 16) := by
      dsimp only [f]
      rw [hcbBit]
      cases hBle : Nat.ble 128 (Nat.mod (Nat.shiftRight ctrl.toNat (8 * k)) 256) with
      | true => rfl
      | false =>
        dsimp only
        have hIdx : (and cbBv (BitVec.ofNat 8 0x0f)).toNat =
            Nat.mod cbBv.toNat 16 := by
          have hPow4 : Nat.pow 2 4 = 16 := rfl
          have hPow8 : Nat.pow 2 8 = 256 := rfl
          have hMask : and cbBv (BitVec.ofNat 8 0x0f) =
              setWidth 8 (extractLsb 0 4 cbBv) := by
            apply eq_of_getLsbD_eq
            intro m hm
            rw [getLsbD_and, getLsbD_setWidth, getLsbD_extractLsb,
              decide_eq_true hm, Bool.true_and, Nat.add_zero]
            cases getLsbD cbBv m with
            | false => rw [Bool.false_and, Bool.and_false]
            | true =>
              rw [Bool.true_and, Bool.and_true]
              cases m with
              | zero => rfl
              | succ m1 => cases m1 with
                | zero => rfl
                | succ m2 => cases m2 with
                  | zero => rfl
                  | succ m3 => cases m3 with
                    | zero => rfl
                    | succ m4 => cases m4 with
                      | zero => rfl
                      | succ m5 => cases m5 with
                        | zero => rfl
                        | succ m6 => cases m6 with
                          | zero => rfl
                          | succ m7 => cases m7 with
                            | zero => rfl
                            | succ m8 =>
                              exact False.elim (Nat.not_lt_of_ge
                                (Nat.le_add_left 8 m8) hm)
          have hSr0 : Nat.shiftRight cbBv.toNat 0 = cbBv.toNat := rfl
          rw [hMask, toNat_setWidth, extractLsb, toNat_setWidth, toNat_ushr,
            hSr0, hPow4, hPow8]
          exact Nat.mod_eq_of_lt
            (Nat.lt_trans (Nat.mod_lt _ (by decide : 0 < 16))
              (by decide : 16 < 256))
        rw [hIdx, ← hcbNat]
    rw [hfk]
    cases Nat.ble 128 (Nat.mod (Nat.shiftRight ctrl.toNat (8 * k)) 256) with
    | true =>
      dsimp only
      rw [setWidth_bvZero, shl_bvZero, bvZero, xor_zero]
    | false =>
      dsimp only
      let idx := Nat.mod (Nat.mod (Nat.shiftRight ctrl.toNat (8 * k)) 256) 16
      let bBv := getByte128 src idx
      have hbNat : bBv.toNat = Nat.mod (Nat.shiftRight src.toNat (8 * idx)) 256 :=
        rfl
      rw [← hbNat]
      apply eq_of_getLsbD_eq
      intro m hm
      rw [getLsbD_ofNat, getLsbD_xor, getLsbD_ofNat, getLsbD_shl,
        getLsbD_setWidth, decide_eq_true hm, Bool.true_and, Bool.true_and,
        Bool.true_and]
      change Nat.testBit (Nat.xor (vpshufb128NatAux src.toNat ctrl.toNat k)
          (Nat.shiftLeft bBv.toNat (8 * k))) m =
        (Nat.testBit (vpshufb128NatAux src.toNat ctrl.toNat k) m !=
          (decide (8 * k ≤ m) && (decide (m - 8 * k < 128) &&
            getLsbD bBv (m - 8 * k))))
      rw [nat_testBit_xor_eq, nat_testBit_shiftLeft_eq]
      have hSubLt128 : m - 8 * k < 128 := Nat.lt_of_le_of_lt (Nat.sub_le m _) hm
      rw [decide_eq_true hSubLt128, Bool.true_and]
      cases Nat.lt_or_ge (m - 8 * k) 8 with
      | inl _ => rfl
      | inr hGe8 =>
        have hFalse : bBv.toNat.testBit (m - 8 * k) = false :=
          getLsbD_ge bBv hGe8
        have hLsb : getLsbD bBv (m - 8 * k) = false := hFalse
        rw [hFalse, hLsb, Bool.and_false]

/-- Extensional characterization of `vpshufb128` as 16 packed byte lanes. -/
theorem vpshufb128_eq_packBytes128 (src ctrl : BitVec 128) :
    vpshufb128 src ctrl =
      packBytes128 fun i =>
        let cb := getByte128 ctrl i
        match getLsbD cb 7 with
        | true  => bvZero 8
        | false => getByte128 src ((and cb (BitVec.ofNat 8 0x0f)).toNat) :=
  vpshufb128_prefix_eq src ctrl 16

/-- Dynamic-source, constant-control `vpshufb128` (`src ↦ vpshufb128 src ctrl`)
is unconditionally $\mathbb{F}_2$-linear for every control mask `ctrl`. -/
theorem vpshufb128_constCtrl_isLinear (ctrl : BitVec 128) :
    IsF2Linear1 (fun src => vpshufb128 src ctrl) where
  map_zero := by
    rw [vpshufb128_eq_packBytes128]
    unfold packBytes128
    apply packLanesAux_zero
    intro i
    dsimp only
    cases getLsbD (getByte128 ctrl i) 7 with
    | true => rfl
    | false => exact getLane_zero 128 8 _
  map_xor := fun a b => by
    rw [vpshufb128_eq_packBytes128, vpshufb128_eq_packBytes128,
      vpshufb128_eq_packBytes128]
    unfold packBytes128
    rw [← packLanesAux_xor]
    apply packLanesAux_congr
    intro i _
    dsimp only
    cases getLsbD (getByte128 ctrl i) 7 with
    | true => exact Eq.symm (xor_zero (bvZero 8))
    | false => exact getLane_xor 8 a b _

/-- Checks `lut[a ^ b] == lut[a] ^ lut[b]` for row `a` across `b < n`. -/
@[expose]
def checkLut16Row (lut : BitVec 128) (a n : Nat) : Bool :=
  @Nat.rec (fun _ => Bool)
    true
    (fun b prev =>
      match prev with
      | false => false
      | true  =>
        bvEq (getByte128 lut (Nat.xor a b))
          (xor (getByte128 lut a) (getByte128 lut b)))
    n

/-- Checks all 16×16 XOR pairs on `lut` across rows `a < m`. -/
@[expose]
def checkLut16LinearAux (lut : BitVec 128) (m : Nat) : Bool :=
  @Nat.rec (fun _ => Bool)
    true
    (fun a prev =>
      match prev with
      | false => false
      | true  => checkLut16Row lut a 16)
    m

/-- Certifies that 16-byte lookup table `lut : BitVec 128` is
$\mathbb{F}_2$-linear over 4-bit nibble indices `0 .. 15`. -/
@[expose]
def checkLut16Linear (lut : BitVec 128) : Bool :=
  bvEq (getByte128 lut 0) (bvZero 8) && checkLut16LinearAux lut 16

private theorem bool_and_left_s {a b : Bool} (h : (a && b) = true) :
    a = true := by
  cases a with
  | false => nomatch h
  | true => rfl

private theorem bool_and_right_s {a b : Bool} (h : (a && b) = true) :
    b = true := by
  cases a with
  | false => nomatch h
  | true => exact h

private theorem checkLut16Row_sound {lut : BitVec 128} {a : Nat} :
    ∀ {n b : Nat}, b < n → checkLut16Row lut a n = true →
      getByte128 lut (Nat.xor a b) =
        xor (getByte128 lut a) (getByte128 lut b)
  | 0, _, hb, _ => nomatch hb
  | k + 1, b, hb, hchk => by
    cases hp : checkLut16Row lut a k with
    | false =>
      change (match checkLut16Row lut a k with
        | false => false
        | true  => bvEq (getByte128 lut (Nat.xor a k))
                     (xor (getByte128 lut a) (getByte128 lut k))) = true at hchk
      rw [hp] at hchk
      nomatch hchk
    | true =>
      change (match checkLut16Row lut a k with
        | false => false
        | true  => bvEq (getByte128 lut (Nat.xor a k))
                     (xor (getByte128 lut a) (getByte128 lut k))) = true at hchk
      rw [hp] at hchk
      cases Nat.lt_or_eq_of_le (Nat.le_of_lt_succ hb) with
      | inl hlt => exact checkLut16Row_sound hlt hp
      | inr heq =>
        subst heq
        exact bvEq_eq hchk

private theorem checkLut16LinearAux_sound {lut : BitVec 128} :
    ∀ {m a b : Nat}, a < m → b < 16 → checkLut16LinearAux lut m = true →
      getByte128 lut (Nat.xor a b) =
        xor (getByte128 lut a) (getByte128 lut b)
  | 0, _, _, ha, _, _ => nomatch ha
  | k + 1, a, b, ha, hb, hchk => by
    change (match checkLut16LinearAux lut k with
      | false => false
      | true  => checkLut16Row lut k 16) = true at hchk
    cases hp : checkLut16LinearAux lut k with
    | false => rw [hp] at hchk; nomatch hchk
    | true =>
      rw [hp] at hchk
      cases Nat.lt_or_eq_of_le (Nat.le_of_lt_succ ha) with
      | inl hlt => exact checkLut16LinearAux_sound hlt hb hp
      | inr heq =>
        subst heq
        exact checkLut16Row_sound hb hchk

private theorem mask0f_bit :
    ∀ {j : Nat}, j < 8 →
      getLsbD (BitVec.ofNat 8 0x0f) j = decide (j < 4)
  | 0, _ => rfl
  | 1, _ => rfl
  | 2, _ => rfl
  | 3, _ => rfl
  | 4, _ => rfl
  | 5, _ => rfl
  | 6, _ => rfl
  | 7, _ => rfl
  | j + 8, hj => False.elim (Nat.not_lt_of_ge (Nat.le_add_left 8 j) hj)

private theorem mask0f_eq_extract4 (x : BitVec 8) :
    and x (BitVec.ofNat 8 0x0f) = setWidth 8 (extractLsb 0 4 x) := by
  apply eq_of_getLsbD_eq
  intro i hi
  rw [getLsbD_and, getLsbD_setWidth, getLsbD_extractLsb, decide_eq_true hi,
    Bool.true_and, Nat.add_zero, mask0f_bit hi]
  cases getLsbD x i <;> cases decide (i < 4) <;> rfl

private theorem nibble_mask_lt_16 (x : BitVec 8) :
    (and x (BitVec.ofNat 8 0x0f)).toNat < 16 := by
  rw [mask0f_eq_extract4, toNat_setWidth]
  have hLt4 : (extractLsb 0 4 x).toNat < 16 := (extractLsb 0 4 x).isLt
  have hLe256 : (extractLsb 0 4 x).toNat < 256 :=
    Nat.lt_trans hLt4 (by decide : 16 < 256)
  have hm256 : Nat.mod (extractLsb 0 4 x).toNat (Nat.pow 2 8) =
      (extractLsb 0 4 x).toNat := Nat.mod_eq_of_lt hLe256
  rw [hm256]
  exact hLt4

private theorem nibble_mask_msb_false (x : BitVec 8) :
    getLsbD (and x (BitVec.ofNat 8 0x0f)) 7 = false := by
  rw [getLsbD_and]
  have h7 : getLsbD (BitVec.ofNat 8 0x0f) 7 = false := rfl
  rw [h7, Bool.and_false]

/-- Constant `0x0f` low-nibble mask replicated across all 16 bytes of a 128-bit
register (`packBytes128 (fun _ => BitVec.ofNat 8 0x0f)`). -/
@[expose]
def simdMask0f128 : BitVec 128 :=
  packBytes128 (fun _ => BitVec.ofNat 8 0x0f)

/-- Vectorized split-nibble $\text{GF}(2^8)$ multiplication across 16 bytes
using two `vpshufb128` lookups. -/
@[expose]
def gf256SimdVpshufb128 (lutLo lutHi v : BitVec 128) : BitVec 128 :=
  let lo := and v simdMask0f128
  let hi := and (ushr v 4) simdMask0f128
  xor (vpshufb128 lutLo lo) (vpshufb128 lutHi hi)

private theorem getByte128_mask0f (v : BitVec 128) {i : Nat} (hi : i < 16) :
    getByte128 (and v simdMask0f128) i =
      and (getByte128 v i) (BitVec.ofNat 8 0x0f) := by
  unfold getByte128 simdMask0f128 packBytes128
  have hFit : 8 * (i + 1) ≤ 128 := by
    have hMul : 8 * (i + 1) ≤ 8 * 16 := Nat.mul_le_mul_left 8 hi
    exact hMul
  rw [getLane_and, getLane_packLanesAux _ hi hFit]

private theorem getByte128_ushr4_mask0f (v : BitVec 128) {i : Nat}
    (hi : i < 16) :
    getByte128 (and (ushr v 4) simdMask0f128) i =
      and (ushr (getByte128 v i) 4) (BitVec.ofNat 8 0x0f) := by
  rw [getByte128_mask0f (ushr v 4) hi]
  apply eq_of_getLsbD_eq
  intro k hk
  unfold getByte128 getLane
  rw [getLsbD_and, getLsbD_and, getLsbD_extractLsb, getLsbD_ushr,
    getLsbD_ushr, getLsbD_extractLsb, decide_eq_true hk, Bool.true_and]
  cases Nat.lt_or_ge k 4 with
  | inr hge4 =>
    rw [mask0f_bit hk, decide_eq_false (Nat.not_lt_of_ge hge4),
      Bool.and_false, Bool.and_false]
  | inl hlt4 =>
    have hk4Lt8 : k + 4 < 8 := Nat.add_lt_add_right hlt4 4
    have hAssoc : k + 8 * i + 4 = k + 4 + 8 * i := by
      rw [Nat.add_assoc k (8 * i) 4, Nat.add_comm (8 * i) 4,
        ← Nat.add_assoc k 4 (8 * i)]
    rw [decide_eq_true hk4Lt8, Bool.true_and, hAssoc]

/-- `gf256SimdVpshufb128 lutLo lutHi` is lane-uniform across all 16 byte
lanes of `BitVec 128`. -/
theorem gf256SimdVpshufb128_eq_packLanes (lutLo lutHi v : BitVec 128) :
    gf256SimdVpshufb128 lutLo lutHi v =
      packLanes 16 8 fun i =>
        xor
          (getByte128 lutLo ((and (getByte128 v i) (BitVec.ofNat 8 0x0f)).toNat))
          (getByte128 lutHi
            ((and (ushr (getByte128 v i) 4) (BitVec.ofNat 8 0x0f)).toNat)) := by
  unfold gf256SimdVpshufb128 packLanes
  dsimp only
  rw [vpshufb128_eq_packBytes128, vpshufb128_eq_packBytes128]
  unfold packBytes128
  rw [← packLanesAux_xor]
  apply packLanesAux_congr
  intro i hi
  dsimp only
  rw [getByte128_mask0f v hi, getByte128_ushr4_mask0f v hi,
    nibble_mask_msb_false, nibble_mask_msb_false]
  dsimp only
  rw [Anneal.BitVec.and_assoc, Anneal.BitVec.and_self,
    Anneal.BitVec.and_assoc, Anneal.BitVec.and_self]

/-- Extracting byte `i < 16` from `gf256SimdVpshufb128 lutLo lutHi v`
depends solely on byte `i` of `v`. -/
theorem getByte128_gf256SimdVpshufb128 (lutLo lutHi v : BitVec 128)
    {i : Nat} (hi : i < 16) :
    getByte128 (gf256SimdVpshufb128 lutLo lutHi v) i =
      xor
        (getByte128 lutLo ((and (getByte128 v i) (BitVec.ofNat 8 0x0f)).toNat))
        (getByte128 lutHi
          ((and (ushr (getByte128 v i) 4) (BitVec.ofNat 8 0x0f)).toNat)) := by
  rw [gf256SimdVpshufb128_eq_packLanes]
  exact getLane_packLanes _ hi

/-- Whenever `checkLut16Linear lutLo = true` and
`checkLut16Linear lutHi = true`, the 16-lane data-dependent `vpshufb128` lookup
`gf256SimdVpshufb128 lutLo lutHi` is `IsF2Linear1`. -/
theorem gf256SimdVpshufb128_isLinear {lutLo lutHi : BitVec 128}
    (hLo : checkLut16Linear lutLo = true)
    (hHi : checkLut16Linear lutHi = true) :
    IsF2Linear1 (gf256SimdVpshufb128 lutLo lutHi) where
  map_zero := by
    have zLo := bvEq_eq (bool_and_left_s hLo)
    have zHi := bvEq_eq (bool_and_left_s hHi)
    rw [gf256SimdVpshufb128_eq_packLanes]
    unfold packLanes
    apply packLanesAux_zero
    intro i
    have hZ : getByte128 (bvZero 128) i = bvZero 8 := getLane_zero 128 8 i
    rw [hZ]
    have hzAnd : (and (bvZero 8) (BitVec.ofNat 8 0x0f)).toNat = 0 := rfl
    have hzUshrAnd :
        (and (ushr (bvZero 8) 4) (BitVec.ofNat 8 0x0f)).toNat = 0 := rfl
    rw [hzAnd, hzUshrAnd, zLo, zHi, bvZero, xor_zero]
  map_xor := fun a b => by
    have hLoTbl := bool_and_right_s hLo
    have hHiTbl := bool_and_right_s hHi
    rw [gf256SimdVpshufb128_eq_packLanes, gf256SimdVpshufb128_eq_packLanes,
      gf256SimdVpshufb128_eq_packLanes]
    unfold packLanes
    rw [← packLanesAux_xor]
    apply packLanesAux_congr
    intro i _
    have hAx : getByte128 (xor a b) i =
        xor (getByte128 a i) (getByte128 b i) := getLane_xor 8 a b i
    rw [hAx, ushr_xor_distrib, and_xor_distrib_right,
      and_xor_distrib_right, toNat_xor, toNat_xor,
      checkLut16LinearAux_sound (nibble_mask_lt_16 _) (nibble_mask_lt_16 _)
        hLoTbl,
      checkLut16LinearAux_sound (nibble_mask_lt_16 _) (nibble_mask_lt_16 _)
        hHiTbl]
    exact xor_four_rearrange _ _ _ _

/-- $\text{GF}(2^8)$ `xtime` modulo the AES (Rijndael) polynomial
$x^8 + x^4 + x^3 + x + 1$ (`0x1b`). -/
@[expose]
def gf256Xtime (a : BitVec 8) : BitVec 8 :=
  match getLsbD a 7 with
  | false => shl a 1
  | true  => xor (shl a 1) (BitVec.ofNat 8 0x1b)

/-- Horner loop for byte-level $\text{GF}(2^8)$ constant multiplication by `c`
over `n ≤ 8` steps (`n = 8` in `gf256MulConstByte`) via `@Nat.rec`. -/
@[expose]
def gf256MulConstByteAux (c a : BitVec 8) (n : Nat) : BitVec 8 :=
  @Nat.rec (fun _ => BitVec 8)
    (bvZero 8)
    (fun k prev =>
      let shifted := gf256Xtime prev
      match getLsbD c (7 - k) with
      | false => shifted
      | true  => xor shifted a)
    n

/-- Byte-level $\text{GF}(2^8)$ multiplication by constant `c : BitVec 8`. -/
@[expose]
def gf256MulConstByte (c a : BitVec 8) : BitVec 8 :=
  gf256MulConstByteAux c a 8

/-- 16-lane SIMD reference $\text{GF}(2^8)$ constant multiplication on
`BitVec 128`. -/
@[expose]
def gf256MulConstSimd128 (c : BitVec 8) (v : BitVec 128) : BitVec 128 :=
  packBytes128 fun i => gf256MulConstByte c (getByte128 v i)

/-- Extracts byte `i < 16` from `gf256MulConstSimd128 c v`. -/
theorem getByte128_gf256MulConstSimd128 (c : BitVec 8) (v : BitVec 128)
    {i : Nat} (hi : i < 16) :
    getByte128 (gf256MulConstSimd128 c v) i =
      gf256MulConstByte c (getByte128 v i) := by
  unfold gf256MulConstSimd128 getByte128 packBytes128
  exact getLane_packLanesAux _ hi (Nat.mul_le_mul_left 8 hi)

private theorem gf256Xtime_zero : gf256Xtime (bvZero 8) = bvZero 8 := rfl

private theorem gf256Xtime_xor (a b : BitVec 8) :
    gf256Xtime (xor a b) = xor (gf256Xtime a) (gf256Xtime b) := by
  unfold gf256Xtime
  rw [getLsbD_xor, shl_xor_distrib]
  cases getLsbD a 7 <;> cases getLsbD b 7
  · rfl
  · have hb : (false != true) = true := rfl
    rw [hb]; dsimp only
    exact xor_assoc _ _ _
  · have hb : (true != false) = true := rfl
    rw [hb]; dsimp only
    rw [xor_assoc, xor_comm (shl b 1) (BitVec.ofNat 8 0x1b), ← xor_assoc]
  · have hb : (true != true) = false := rfl
    rw [hb]; dsimp only
    rw [xor_four_rearrange (shl a 1) (BitVec.ofNat 8 0x1b)
          (shl b 1) (BitVec.ofNat 8 0x1b),
        xor_self, xor_zero]

private theorem gf256MulConstByteAux_zero (c : BitVec 8) :
    ∀ n : Nat, gf256MulConstByteAux c (bvZero 8) n = bvZero 8
  | 0 => rfl
  | k + 1 => by
    change (match getLsbD c (7 - k) with
      | false => gf256Xtime (gf256MulConstByteAux c (bvZero 8) k)
      | true  => xor (gf256Xtime (gf256MulConstByteAux c (bvZero 8) k))
                   (bvZero 8)) = bvZero 8
    rw [gf256MulConstByteAux_zero c k, gf256Xtime_zero]
    cases getLsbD c (7 - k) with
    | false => rfl
    | true => exact xor_zero (bvZero 8)

private theorem gf256MulConstByteAux_xor (c a b : BitVec 8) :
    ∀ n : Nat,
      gf256MulConstByteAux c (xor a b) n =
        xor (gf256MulConstByteAux c a n) (gf256MulConstByteAux c b n)
  | 0 => Eq.symm (xor_zero (bvZero 8))
  | k + 1 => by
    change (match getLsbD c (7 - k) with
      | false => gf256Xtime (gf256MulConstByteAux c (xor a b) k)
      | true  => xor (gf256Xtime (gf256MulConstByteAux c (xor a b) k))
                   (xor a b)) =
      xor (match getLsbD c (7 - k) with
      | false => gf256Xtime (gf256MulConstByteAux c a k)
      | true  => xor (gf256Xtime (gf256MulConstByteAux c a k)) a)
          (match getLsbD c (7 - k) with
      | false => gf256Xtime (gf256MulConstByteAux c b k)
      | true  => xor (gf256Xtime (gf256MulConstByteAux c b k)) b)
    rw [gf256MulConstByteAux_xor c a b k, gf256Xtime_xor]
    cases getLsbD c (7 - k) with
    | false => rfl
    | true =>
      dsimp only
      exact xor_four_rearrange _ _ _ _

/-- Single-byte $\text{GF}(2^8)$ constant multiplication `gf256MulConstByte c`
is `IsF2Linear1`. -/
theorem gf256MulConstByte_isLinear (c : BitVec 8) :
    IsF2Linear1 (gf256MulConstByte c) where
  map_zero := gf256MulConstByteAux_zero c 8
  map_xor := fun a b => gf256MulConstByteAux_xor c a b 8

/-- 16-lane SIMD $\text{GF}(2^8)$ constant multiplication
`gf256MulConstSimd128 c` is `IsF2Linear1`. -/
theorem gf256MulConstSimd128_isLinear (c : BitVec 8) :
    IsF2Linear1 (gf256MulConstSimd128 c) where
  map_zero := by
    unfold gf256MulConstSimd128 packBytes128
    apply packLanesAux_zero
    intro i
    unfold getByte128
    rw [getLane_zero]
    exact gf256MulConstByteAux_zero c 8
  map_xor := fun a b => by
    unfold gf256MulConstSimd128 packBytes128
    rw [← packLanesAux_xor]
    apply packLanesAux_congr
    intro i _
    unfold getByte128
    rw [getLane_xor]
    exact gf256MulConstByteAux_xor c _ _ 8

/-- Precomputes the low-nibble 16-byte `vpshufb128` table for $\text{GF}(2^8)$
constant `c`. -/
@[expose]
def mkGf256LutLo (c : BitVec 8) : BitVec 128 :=
  packBytes128 fun nib => gf256MulConstByte c (BitVec.ofNat 8 nib)

/-- Precomputes the high-nibble 16-byte `vpshufb128` table for $\text{GF}(2^8)$
constant `c`. -/
@[expose]
def mkGf256LutHi (c : BitVec 8) : BitVec 128 :=
  packBytes128 fun nib => gf256MulConstByte c (BitVec.ofNat 8 (nib * 16))

end Anneal.F2Simd

end
