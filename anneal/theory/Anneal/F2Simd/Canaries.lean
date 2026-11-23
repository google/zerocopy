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
public import Init.Data.List.Basic
public import Anneal.BitVec
public import Anneal.F2Simd.Basis
public import Anneal.F2Simd.Simd

public section

namespace Anneal.F2Simd

open Anneal.BitVec

/-!
# End-to-End Canaries & Negative Suite (`Anneal.F2Simd.Canaries`)

Exercises every theorem family in `Anneal.F2Simd` purely within the Lean 4
kernel (`0` `+kernel`, `0` `omega`, `0` `noncomputable`, `0` `._unsafe_rec`):

1. **64×64 → 128-bit `pclmulqdq` Karatsuba vs. schoolbook equivalence &
   commutativity (`pclmulqdq64_karatsuba_eq_schoolbook`, `pclmulqdq64_comm`,
   `crc64_ecma_pclmulqdq_karatsuba_eq_schoolbook`):** Discharges universal
   128-bit polynomial identities via `checkF2Bilinear_sound` (over symbolic
   unit-basis lemmas `clmulKaratsuba64_bvUnit` and `clmul_bvUnit`) and unary
   `checkF2Linear1_sound` (`rfl`).
2. **128-bit `vpshufb128` split-nibble $\text{GF}(2^8)$ lookup & byte-swap
   involution (`vpshufb128_gf256_mul_0x9d_eq`,
   `vpshufb128_bswap32x4_involutive`):** Proves 16-lane data-dependent table
   lookup equivalent to polynomial $\text{GF}(2^8)$ multiplication across all
   `2^128` 128-bit register inputs via `checkUniformSimdLanes_sound`, plus `rfl`
   involution via `checkF2Linear1Range_sound`.
3. **Cone-of-influence basis slicing, 256-bit 32-lane uniform reduction, and
   `F2Circuit` Gray-code involution (`simd_lane3_cone_slice_gf256_0x0e_eq`,
   `uniform_simd32_gf256_0x0b_eq`, `f2Circuit_gray64_decode_encode_id`):**
   Exercises 8-bit cone slicing on a 128-bit register using
   `hasBitCone_extractLsb` and `checkF2ConeLinear_sound`, 8-basis-check
   reduction across 32 lanes (`BitVec 256`), and zero-boilerplate `F2Circuit`
   synthesis.
4. **Fail-closed negative regression suite
   (`canary_f2simd_negative_fail_closed_tests`):** Single-cause negative tests
   confirming each checker rejects perturbed linear, bilinear, LUT, cone, and
   high-bit-zeroed `vpshufb128` inputs.
-/

/-! ## 1. Linear Composition & Single-Byte Split-Nibble Helpers -/

/-- Composition of two `IsF2Linear1` maps is `IsF2Linear1`. -/
theorem isF2Linear1_comp {w1 w2 w3 : Nat}
    {g : BitVec w2 → BitVec w3} {f : BitVec w1 → BitVec w2}
    (hg : IsF2Linear1 g) (hf : IsF2Linear1 f) :
    IsF2Linear1 (fun x => g (f x)) where
  map_zero := by rw [hf.map_zero, hg.map_zero]
  map_xor := fun a b => by rw [hf.map_xor, hg.map_xor]

/-- `getLane laneW · i` is `IsF2Linear1`. -/
theorem getLane_isLinear (w laneW i : Nat) :
    IsF2Linear1 (fun v : BitVec w => getLane laneW v i) where
  map_zero := getLane_zero w laneW i
  map_xor := fun a b => getLane_xor laneW a b i

/-- Single-byte split-nibble $\text{GF}(2^8)$ lookup driven by two certified
16-byte tables `lutLo`, `lutHi`. -/
@[expose]
def gf256SplitNibbleByte (lutLo lutHi : BitVec 128) (x : BitVec 8) : BitVec 8 :=
  let loIdx := (and x (BitVec.ofNat 8 0x0f)).toNat
  let hiIdx := (and (ushr x 4) (BitVec.ofNat 8 0x0f)).toNat
  xor (getByte128 lutLo loIdx) (getByte128 lutHi hiIdx)

/-- `gf256SplitNibbleByte lutLo lutHi` is `IsF2Linear1` whenever both tables
pass `checkLut16Linear` (extracted from lane `0` of
`gf256SimdVpshufb128_isLinear`). -/
theorem gf256SplitNibbleByte_isLinear {lutLo lutHi : BitVec 128}
    (hLo : checkLut16Linear lutLo = true)
    (hHi : checkLut16Linear lutHi = true) :
    IsF2Linear1 (gf256SplitNibbleByte lutLo lutHi) := by
  have hSimd := gf256SimdVpshufb128_isLinear hLo hHi
  have hEmbed : IsF2Linear1 (fun x : BitVec 8 => setWidth 128 x) :=
    { map_zero := setWidth_bvZero 8 128
      map_xor := fun a b => setWidth_xor_distrib 128 a b }
  have hComp :=
    isF2Linear1_comp (getLane_isLinear 128 8 0)
      (isF2Linear1_comp hSimd hEmbed)
  have hPointwise : ∀ x : BitVec 8,
      gf256SplitNibbleByte lutLo lutHi x =
        getLane 8 (gf256SimdVpshufb128 lutLo lutHi (setWidth 128 x)) 0 := by
    intro x
    change gf256SplitNibbleByte lutLo lutHi x =
      getByte128 (gf256SimdVpshufb128 lutLo lutHi (setWidth 128 x)) 0
    rw [getByte128_gf256SimdVpshufb128 _ _ _ (by decide : 0 < 16)]
    have hByte0 : getByte128 (setWidth 128 x) 0 = x := by
      unfold getByte128 getLane
      apply eq_of_getLsbD_eq
      intro k hk
      rw [getLsbD_extractLsb, decide_eq_true hk, Bool.true_and, Nat.mul_zero,
        Nat.add_zero, getLsbD_setWidth,
        decide_eq_true (Nat.lt_trans hk (by decide : 8 < 128)), Bool.true_and]
    rw [hByte0]
    rfl
  exact
    { map_zero := by
        rw [hPointwise, hComp.map_zero]
      map_xor := fun a b => by
        rw [hPointwise, hPointwise, hPointwise, hComp.map_xor] }

/-! ## 2. End-to-End `pclmulqdq` & SIMD `vpshufb128` Soundness Canaries -/

/-- Full 64×64 → 128-bit `pclmulqdq` Karatsuba vs. schoolbook equivalence,
discharged via `checkF2Bilinear_sound` and `checkBilinearRows_of_forall`
over unit-basis identities `clmulKaratsuba64_bvUnit` and `clmul_bvUnit`. -/
theorem pclmulqdq64_karatsuba_eq_schoolbook :
    ∀ (x y : BitVec 64), clmulKaratsuba64 x y = clmul 64 128 x y :=
  checkF2Bilinear_sound clmulKaratsuba64_isBilinear (clmul_isBilinear 64 128)
    (checkBilinearRows_of_forall 64 fun _ _ hi hj => by
      rw [clmulKaratsuba64_bvUnit hi hj, clmul_bvUnit hi hj])

/-- Full 64×64 → 128-bit `pclmulqdq` commutativity (`clmul x y = clmul y x`),
discharged via `checkF2Bilinear_sound` and `clmul_bvUnit`. -/
theorem pclmulqdq64_comm :
    ∀ (x y : BitVec 64), clmul 64 128 x y = clmul 64 128 y x :=
  checkF2Bilinear_sound
    (clmul_isBilinear 64 128)
    { zero_left  := fun y => (clmul_isBilinear 64 128).zero_right y
      xor_left   := fun a1 a2 y => (clmul_isBilinear 64 128).xor_right y a1 a2
      zero_right := fun x => (clmul_isBilinear 64 128).zero_left x
      xor_right  := fun x b1 b2 => (clmul_isBilinear 64 128).xor_left b1 b2 x }
    (checkBilinearRows_of_forall 64 fun _ _ hi hj => by
      rw [clmul_bvUnit hi hj, clmul_bvUnit hj hi, Nat.add_comm])

/-- Constant-polynomial CRC-64-ECMA (`0x42f0e1eba9ea3693`) generator
multiplication: unary `checkF2Linear1_sound` requires only 64 GMP basis
evaluations (`rfl`). -/
theorem crc64_ecma_pclmulqdq_karatsuba_eq_schoolbook :
    ∀ x : BitVec 64,
      clmulKaratsuba64 x (BitVec.ofNat 64 0x42f0e1eba9ea3693) =
      clmul 64 128 x (BitVec.ofNat 64 0x42f0e1eba9ea3693) :=
  checkF2Linear1_sound
    ⟨clmulKaratsuba64_isBilinear.zero_left _,
     fun a1 a2 => clmulKaratsuba64_isBilinear.xor_left a1 a2 _⟩
    ⟨(clmul_isBilinear 64 128).zero_left _,
     fun a1 a2 => (clmul_isBilinear 64 128).xor_left a1 a2 _⟩
    rfl

/-- 16-lane 128-bit `vpshufb128` split-nibble $\text{GF}(2^8)$ multiplication by
`0x9d` equals 16-lane polynomial $\text{GF}(2^8)$ multiplication across all
`2^128` register values via `checkUniformSimdLanes_sound` (`8` basis checks
by `rfl`). -/
theorem vpshufb128_gf256_mul_0x9d_eq :
    ∀ v : BitVec 128,
      gf256SimdVpshufb128
        (mkGf256LutLo (BitVec.ofNat 8 0x9d))
        (mkGf256LutHi (BitVec.ofNat 8 0x9d)) v =
      gf256MulConstSimd128 (BitVec.ofNat 8 0x9d) v := by
  intro v
  rw [gf256SimdVpshufb128_eq_packLanes]
  exact checkUniformSimdLanes_sound 16 8
    (gf256SplitNibbleByte_isLinear rfl rfl)
    (gf256MulConstByte_isLinear (BitVec.ofNat 8 0x9d))
    rfl v

/-- Control mask for 4-lane 32-bit endian byte-swap (`bswap32x4`) in
`vpshufb128`. -/
@[expose]
def bswap32x4Ctrl128 : BitVec 128 :=
  BitVec.ofNat 128 0x0c0d0e0f08090a0b0405060700010203

private theorem bswap32x4_lo64 :
    checkLinear1Range
      (fun v => vpshufb128 (vpshufb128 v bswap32x4Ctrl128) bswap32x4Ctrl128)
      (fun v => v) 0 64 = true := rfl

private theorem bswap32x4_hi64 :
    checkLinear1Range
      (fun v => vpshufb128 (vpshufb128 v bswap32x4Ctrl128) bswap32x4Ctrl128)
      (fun v => v) 64 64 = true := rfl

/-- `vpshufb128` 4×`u32` byte-swap is an involution (`∀ v, bswap(bswap v) = v`)
across all `2^128` inputs (`rfl`). -/
theorem vpshufb128_bswap32x4_involutive :
    ∀ v : BitVec 128,
      vpshufb128 (vpshufb128 v bswap32x4Ctrl128) bswap32x4Ctrl128 = v := by
  have h128 := checkLinear1Range_append rfl rfl bswap32x4_lo64 bswap32x4_hi64
  exact checkF2Linear1Range_sound
    (isF2Linear1_comp
      (vpshufb128_constCtrl_isLinear bswap32x4Ctrl128)
      (vpshufb128_constCtrl_isLinear bswap32x4Ctrl128))
    { map_zero := rfl, map_xor := fun _ _ => rfl }
    h128

/-! ## 3. Cone-of-Influence Slicing, 256-Bit Uniform SIMD & `F2Circuit` -/

/-- Bit-cone `[24 .. 31]` for byte lane `3` of a 128-bit register. -/
@[expose]
def lane3BitCone : List Nat :=
  [24, 25, 26, 27, 28, 29, 30, 31]

/-- Single-lane cone-of-influence canary: proves lane `3` of 16-lane
`gf256SimdVpshufb128` (`0x0e`, AES InvMixColumns) equals lane `3` of
`gf256MulConstSimd128` from **8** in-cone basis checks via
`hasBitCone_extractLsb` and `checkF2ConeLinear_sound` (`rfl`). -/
theorem simd_lane3_cone_slice_gf256_0x0e_eq :
    ∀ v : BitVec 128,
      getByte128
        (gf256SimdVpshufb128
          (mkGf256LutLo (BitVec.ofNat 8 0x0e))
          (mkGf256LutHi (BitVec.ofNat 8 0x0e)) v) 3 =
      getByte128 (gf256MulConstSimd128 (BitVec.ofNat 8 0x0e) v) 3 := by
  intro v
  rw [getByte128_gf256SimdVpshufb128 _ _ _ (by decide : 3 < 16),
    getByte128_gf256MulConstSimd128 _ _ (by decide : 3 < 16)]
  have hConeL :
      HasBitCone lane3BitCone
        (fun x : BitVec 128 =>
          gf256SplitNibbleByte
            (mkGf256LutLo (BitVec.ofNat 8 0x0e))
            (mkGf256LutHi (BitVec.ofNat 8 0x0e))
            (extractLsb 24 8 x)) :=
    hasBitCone_extractLsb lane3BitCone
      (gf256SplitNibbleByte_isLinear rfl rfl) rfl
  have hConeR :
      HasBitCone lane3BitCone
        (fun x : BitVec 128 =>
          gf256MulConstByte (BitVec.ofNat 8 0x0e) (extractLsb 24 8 x)) :=
    hasBitCone_extractLsb lane3BitCone
      (gf256MulConstByte_isLinear (BitVec.ofNat 8 0x0e)) rfl
  exact checkF2ConeLinear_sound lane3BitCone hConeL hConeR rfl v

/-- 256-bit 32-lane uniform lane-wise reduction canary: proves 32-lane
split-nibble $\text{GF}(2^8)$ multiplication by `0x0b` equals 32-lane polynomial
multiplication across all `2^256` packed register values from **8** single-byte
unit-basis checks (`rfl`). -/
theorem uniform_simd32_gf256_0x0b_eq :
    ∀ v : BitVec (32 * 8),
      packLanes 32 8
        (fun i =>
          gf256SplitNibbleByte
            (mkGf256LutLo (BitVec.ofNat 8 0x0b))
            (mkGf256LutHi (BitVec.ofNat 8 0x0b))
            (getLane 8 v i)) =
      packLanes 32 8
        (fun i =>
          gf256MulConstByte (BitVec.ofNat 8 0x0b) (getLane 8 v i)) :=
  checkUniformSimdLanes_sound 32 8
    (gf256SplitNibbleByte_isLinear rfl rfl)
    (gf256MulConstByte_isLinear (BitVec.ofNat 8 0x0b))
    rfl

/-- 64-bit binary-to-Gray code `F2Circuit` (`x ^^^ (x >>> 1)`). -/
@[expose]
def grayEncodeCircuit64 : F2Circuit 2 64 64 :=
  .xor .id (.ushrConst .id 1)

/-- 64-bit Gray-to-binary logarithmic XOR cascade `F2Circuit`
(`1, 2, 4, 8, 16, 32` shift stages). -/
@[expose]
def grayDecodeCircuit64 : F2Circuit 17 64 64 :=
  let s1 : F2Circuit 2 64 64 := .xor .id (.ushrConst .id 1)
  let s2 : F2Circuit 2 64 64 := .xor .id (.ushrConst .id 2)
  let s4 : F2Circuit 2 64 64 := .xor .id (.ushrConst .id 4)
  let s8 : F2Circuit 2 64 64 := .xor .id (.ushrConst .id 8)
  let s16 : F2Circuit 2 64 64 := .xor .id (.ushrConst .id 16)
  let s32 : F2Circuit 2 64 64 := .xor .id (.ushrConst .id 32)
  .comp s32 (.comp s16 (.comp s8 (.comp s4 (.comp s2 s1))))

/-- Zero-boilerplate `F2Circuit` canary: proves 64-bit Gray decode is the exact
left inverse of Gray encode across all `2^64` inputs (`rfl`). -/
theorem f2Circuit_gray64_decode_encode_id :
    ∀ x : BitVec 64,
      grayDecodeCircuit64.eval (grayEncodeCircuit64.eval x) = x := by
  intro x
  rw [← F2Circuit.eval_comp]
  exact checkF2CircuitEq_sound
    (F2Circuit.comp grayDecodeCircuit64 grayEncodeCircuit64)
    F2Circuit.id
    rfl x

/-! ## 4. Joint Linear (`checkF2Linear2`) & Fail-Closed Negative Suite -/

/-- Positive 2-input `checkF2Linear2_sound` canary: 64-bit Feistel/XOR linear
mixing `(a <<< 7) ^^^ (b >>> 3)` vs. factored `F2Circuit` evaluation (`rfl`). -/
theorem checkF2Linear2_mix64_canary :
    ∀ (a b : BitVec 64),
      xor (shl a 7) (ushr b 3) =
      xor ((F2Circuit.shlConst F2Circuit.id 7).eval a)
          ((F2Circuit.ushrConst F2Circuit.id 3).eval b) :=
  checkF2Linear2_sound
    { map_zero := by rw [shl_bvZero, ushr_bvZero, bvZero, xor_zero]
      map_xor := fun a1 a2 b1 b2 => by
        rw [shl_xor_distrib, ushr_xor_distrib]
        exact xor_four_rearrange _ _ _ _ }
    { map_zero := by
        change xor (shl (bvZero 64) 7) (ushr (bvZero 64) 3) = bvZero 64
        rw [shl_bvZero, ushr_bvZero, bvZero, xor_zero]
      map_xor := fun a1 a2 b1 b2 => by
        change xor (shl (xor a1 a2) 7) (ushr (xor b1 b2) 3) =
          xor (xor (shl a1 7) (ushr b1 3)) (xor (shl a2 7) (ushr b2 3))
        rw [shl_xor_distrib, ushr_xor_distrib]
        exact xor_four_rearrange _ _ _ _ }
    rfl

/-- Fail-closed negative regression suite confirming that each certificate
checker rejects invalid/perturbed inputs:
1. `checkF2Linear1` rejects a single-bit mask perturbation on `BitVec 64`;
2. `checkF2Linear2` rejects asymmetric left/right shift mixes;
3. `checkF2Bilinear` rejects a broken Karatsuba missing the `zHi` cross-cancel;
4. `checkLut16Linear` rejects an affine table with `lut[0] ≠ 0`;
5. `checkLut16Linear` rejects a non-linear table with `lut[0] = 0` but
   `lut[1 ^ 2] ≠ lut[1] ^ lut[2]`;
6. `checkOutsideConeZero` rejects a lane projection leaking an out-of-cone bit;
7. `checkConeBasis1` rejects in-cone basis disagreement;
8. `vpshufb128` zeroes lanes whose control byte has bit `7` set (`0x80`). -/
theorem canary_f2simd_negative_fail_closed_tests :
    -- 1. Single-bit mask mismatch in `checkF2Linear1`:
    checkF2Linear1
      (fun x : BitVec 64 => x)
      (fun x : BitVec 64 => and x (BitVec.ofNat 64 0xfffffffffffffffe)) = false ∧
    -- 2. Asymmetric 2-input mix rejected by `checkF2Linear2`:
    checkF2Linear2
      (fun a b : BitVec 32 => xor (shl a 1) b)
      (fun a b : BitVec 32 => xor a (shl b 1)) = false ∧
    -- 3. Broken 16×16 -> 32-bit Karatsuba (omitting `zHi` from `z1`) rejected:
    checkF2Bilinear
      (fun x y : BitVec 16 =>
        let xLo := extractLsb 0 8 x
        let xHi := extractLsb 8 8 x
        let yLo := extractLsb 0 8 y
        let yHi := extractLsb 8 8 y
        let z0 := setWidth 32 (clmul 8 16 xLo yLo)
        let zHi := setWidth 32 (clmul 8 16 xHi yHi)
        let zMid := setWidth 32 (clmul 8 16 (xor xLo xHi) (xor yLo yHi))
        xor (xor z0 (shl (xor zMid z0) 8)) (shl zHi 16))
      (clmul 16 32) = false ∧
    -- 4. Affine LUT (`i ↦ i ^^^ 1`, `lut[0] = 1`) rejected by
    --    `checkLut16Linear`:
    checkLut16Linear
      (BitVec.ofNat 128 0x0e0f0c0d0a0b08090607040502030001) = false ∧
    -- 5. Non-linear LUT (`lut[0] = 0`, `lut[1] = 1`, `lut[2] = 2`, `lut[3] = 7`
    --    instead of `3`) rejected by `checkLut16Linear`:
    checkLut16Linear (BitVec.ofNat 128 0x07020100) = false ∧
    -- 6. Out-of-cone dependency (`lane 0` reading lane `3` cone) rejected:
    checkOutsideConeZero lane3BitCone
      (fun v : BitVec 128 => getByte128 v 0) = false ∧
    -- 7. In-cone disagreement on `lane3BitCone` rejected:
    checkConeBasis1 lane3BitCone
      (fun v : BitVec 128 => getByte128 v 3)
      (fun v : BitVec 128 => shl (getByte128 v 3) 1) = false ∧
    -- 8. `vpshufb128` control byte `0x80` zeroes output lane `0` even when
    --    source lane `0` is `0xff`:
    getByte128
      (vpshufb128 (BitVec.ofNat 128 0xff) (BitVec.ofNat 128 0x80)) 0 =
      bvZero 8 :=
  ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩

end Anneal.F2Simd

end
