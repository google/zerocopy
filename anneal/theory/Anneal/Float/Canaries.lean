-- Copyright 2026 The Fuchsia Authors
--
-- Licensed under a BSD-style license <LICENSE-BSD>, Apache License, Version 2.0
-- <LICENSE-APACHE or https://www.apache.org/licenses/LICENSE-2.0>, or the MIT
-- license <LICENSE-MIT or https://opensource.org/licenses/MIT>, at your option.
-- This file may not be copied, modified, or distributed except according to
-- those terms.

module
prelude
public import Anneal.Float

public section

/-!
# IEEE-754 SoftFloat, RFC 3514, & DSP Canaries (`Anneal.Float.Canaries`)

Positive and negative kernel-checked discriminators (`0` `._unsafe_rec`,
`0` `Classical.choice`, axioms `⊆ [propext, Quot.sound]`) exercising every layer
of `Anneal.Float`:

1. **RFC 3514 Bit-Identity, Subnormals, Binade Carry, & Directed Overflow:**
   - Signaling NaN bit preservation under unary `-`, `abs`, and `copysign`
     (`0x7f80_0001 → 0xff80_0001`, refuting NaN-erasing `Init.Data.Float`).
   - Narrowing `f64` SNaN `0x7ff0_0000_0000_0001` (`payload = 1`): base
     conversion quiets to `0x7fc0_0000`, while `nanChoicesSignaling` drops
     `lower = 0` so `+Inf` (`0x7f80_0000`) is rejected.
   - All 5 IEEE-754 indeterminate forms (`0/0`, `∞/∞`, `0*∞`, `1%0`, `∞%1`),
     `-2.0 % 2.0 = -0.0`, binade carry `(2 - 2^-23) + 2^-24 → 2.0`,
     `f32::MAX + f32::MAX` overflow to `+Inf`, and IEEE 754 §7.4 directed
     overflow (`±MAX_FINITE` vs `±Inf` across `towardZero`, `towardPosInf`, and
     `towardNegInf`).
2. **`simd_relaxed_fma` Precision Non-Monotonicity & Relational Casts:**
   - `x = 0x3f80_0001` (`1 + 2^-23`), `y = 0x3f80_0002` (`1 + 2^-22`):
     unfused `(x * x) - y = +0.0` (`0x0000_0000`) vs fused
     `fma(x, x, -y) = 2^-46` (`0x2880_0000`), both satisfying
     `EvalRelaxedFmaRel`.
   - `EvalFloatToFloatRel`: deterministic collapse on finite values vs RFC 3514
     sign/payload nondeterminism on NaN casts.
3. **Casts (`FloatToInt`, `IntToFloat`, `float_to_int_unchecked`):**
   - `NaN ↦ 0`, `±Inf ↦ MAX/MIN`, `evalFloatToIntChecked` UB rejection
     out-of-range vs agreement in-range, and `9007199254740993_i64 as f64`
     (`2^53 + 1`) ties-to-even (`2^53`) vs ties-away-from-zero (`2^53 + 2`)
     separation.
4. **Sterbenz Corner Guards & Audio/Video DSP Enclosures (`Opus`, `AAC`,
   `swscale`, `af_biquads`):**
   - **Sterbenz Corner Discrimination:** accepts `[3, 4]` vs `[2, 5]` while
     rejecting `[3, 3]` vs `[1, 33554430]` (and its negative mirror) so
     `encloseSubIeee` widens to enclose `-33554428`.
   - **Opus CELT / AAC / Vorbis IMDCT Butterfly:** `f32` twiddle rotation
     (`cos(π/8)`, `sin(π/8)`) over `[-1.0, 1.0]` under `simd_relaxed_fma`,
     bounded within `[-11900000 · 2^-23, +11900000 · 2^-23]` (`≈ ±1.4186`).
   - **Opus / AAC Float-to-`i16` PCM Output Stage:** scaling `[-1.0, 1.0]` by
     `32766.0_f32` passes `checkFloatToIntSafe` into `i16` (`[-32768, 32767]`),
     with negative control rejecting `32769.0_f32`.
   - **`swscale` 4-Tap Lanczos Polyphase Rescaler:**
     `[-1/16, 9/16, 9/16, -1/16]` over `[0, 255]` `u8` luma bounded within
     `[-33, 288]`, with negative control catching Lanczos ringing on unclamped
     `u8` `float_to_int_unchecked`.
   - **`af_biquads` / Opus SILK Complex-Pole IIR Resonator (`JuryStein`):**
     Q14 biquad (`S = 16384`, `a₁ = -28000`, `a₂ = 14000`, `a₁² < 4 S a₂`)
     certified Jury-stable with positive-definite Stein-Lyapunov contraction,
     paired with negative control rejecting unstable `a₂ = 17000`.
-/

namespace Anneal.Float.Canaries

open Anneal.Float
open Anneal.Float.JuryStein

/-! ## 1. RFC 3514 Bitwise Sign Preservation & Narrowing SNaN Guard -/

/-- `f32` signaling NaN `0x7f80_0001` preserves signaling bit and payload `1`
under unary negation (`0xff80_0001`), refuting `Init.Data.Float`
canonicalization. -/
theorem canary_f32_snan_neg_preserves_payload :
    isSignalingNaNBits .binary32 0x7f800001 = true ∧
    evalFloatNeg .binary32 0x7f800001 = 0xff800001 ∧
    isSignalingNaNBits .binary32 (evalFloatNeg .binary32 0x7f800001) = true ∧
    evalFloatAbs .binary32 0xff800001 = 0x7f800001 ∧
    evalFloatCopysign .binary32 0x7f800001 0x80000000 = 0xff800001 := by
  exact ⟨rfl, rfl, rfl, rfl, rfl⟩

/-- Narrowing `f64` SNaN `0x7ff0_0000_0000_0001` (`payload = 1`) to `f32` quiets
to `0x7fc0_0000`, while `nanChoicesSignaling` drops `lower = 0` so `+Inf`
(`0x7f80_0000`) is NEVER admitted in `nanChoices`. -/
theorem canary_f64_snan_narrow_no_inf :
    isSignalingNaNBits .binary64 0x7ff0000000000001 = true ∧
    evalFloatToFloatRoundTiesToEven .binary64 .binary32 0x7ff0000000000001 = 0x7fc00000 ∧
    nanChoicesSignaling .binary32 [(.binary64, 0x7ff0000000000001)] = [] ∧
    natListMem 0x7f800000
      (nanChoices .binary32 [(.binary64, 0x7ff0000000000001)] .nondeterministic) = false := by
  exact ⟨rfl, rfl, rfl, rfl⟩

/-- Finite `1.0_f32 + 2.0_f32 = 3.0_f32`, subnormal
`0x0000_0001 + 0x0000_0001 = 0x0000_0002`, binade carry
`(2 - 2^-23) + 2^-24 = 2.0_f32` (`0x3fff_ffff + 0x3380_0000 = 0x4000_0000`),
overflow `f32::MAX + f32::MAX = +Inf`, and signed-zero rules
(`-0.0 + +0.0 = +0.0`, `-0.0 + -0.0 = -0.0`, `-2.0 % 2.0 = -0.0`). -/
theorem canary_f32_arith_subnormal_overflow_signed_zero :
    evalFloatArithBase .add .binary32 0x3f800000 0x40000000 = 0x40400000 ∧
    evalFloatArithBase .add .binary32 0x00000001 0x00000001 = 0x00000002 ∧
    evalFloatArithBase .add .binary32 0x3fffffff 0x33800000 = 0x40000000 ∧
    evalFloatArithBase .add .binary32 0x7f7fffff 0x7f7fffff = 0x7f800000 ∧
    evalFloatArithBase .add .binary32 0x80000000 0x00000000 = 0x00000000 ∧
    evalFloatArithBase .add .binary32 0x80000000 0x80000000 = 0x80000000 ∧
    evalFloatArithBase .rem .binary32 0xc0000000 0x40000000 = 0x80000000 := by
  exact ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩

/-- IEEE 754-2008 §7.4 directed-rounding overflow: `towardZero`, `towardNegInf`
on positive overflow, and `towardPosInf` on negative overflow return
`±MAX_FINITE` (`0x7f7f_ffff` / `0xff7f_ffff`), whereas `towardPosInf` on
positive overflow and `towardNegInf` on negative overflow return `±Inf`. -/
theorem canary_directed_rounding_overflow_modes :
    roundRatioBits .towardZero .binary32 false (pow2 200) 1 = 0x7f7fffff ∧
    roundRatioBits .towardZero .binary32 true (pow2 200) 1 = 0xff7fffff ∧
    roundRatioBits .towardNegInf .binary32 false (pow2 200) 1 = 0x7f7fffff ∧
    roundRatioBits .towardNegInf .binary32 true (pow2 200) 1 = 0xff800000 ∧
    roundRatioBits .towardPosInf .binary32 false (pow2 200) 1 = 0x7f800000 ∧
    roundRatioBits .towardPosInf .binary32 true (pow2 200) 1 = 0xff7fffff ∧
    convertFloatBits .towardZero .binary64 .binary32 0x7fefffffffffffff =
      0x7f7fffff := by
  exact ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩

/-- All five IEEE-754 indeterminate forms (`0/0`, `∞/∞`, `0*∞`, `1%0`, `∞%1`)
produce `preferredNaNBits` and never trap or return `±Inf`. -/
theorem canary_five_indeterminate_forms :
    evalFloatArithBase .div .binary32 0x00000000 0x00000000 = 0x7fc00000 ∧
    evalFloatArithBase .div .binary32 0x7f800000 0x7f800000 = 0x7fc00000 ∧
    evalFloatArithBase .mul .binary32 0x00000000 0x7f800000 = 0x7fc00000 ∧
    evalFloatArithBase .rem .binary32 0x3f800000 0x00000000 = 0x7fc00000 ∧
    evalFloatArithBase .rem .binary32 0x7f800000 0x3f800000 = 0x7fc00000 := by
  exact ⟨rfl, rfl, rfl, rfl, rfl⟩

/-! ## 2. `simd_relaxed_fma` & Relational `FloatToFloat` Nondeterminism -/

/-- For `x = 1 + 2^-23` (`0x3f80_0001`) and `c = -(1 + 2^-22)` (`0xbf80_0002`),
unfused `(x * x) + c = +0.0` (`0x0000_0000`) whereas single-rounded
`fma(x, x, c) = 2^-46` (`0x2880_0000`); both satisfy `EvalRelaxedFmaRel`. -/
theorem canary_relaxed_fma_divergence :
    evalFloatUnfusedMulAddBase .binary32 0x3f800001 0x3f800001 0xbf800002 = 0x00000000 ∧
    evalFloatFmaBase .binary32 0x3f800001 0x3f800001 0xbf800002 = 0x28800000 ∧
    EvalRelaxedFmaRel .nondeterministic .binary32
      0x3f800001 0x3f800001 0xbf800002 0x28800000 ∧
    EvalRelaxedFmaRel .nondeterministic .binary32
      0x3f800001 0x3f800001 0xbf800002 0x00000000 := by
  refine ⟨rfl, rfl, ?_, ?_⟩
  · exact evalRelaxedFmaRel_of_fused .nondeterministic .binary32
      ((evalFloatFmaRel_of_not_nan .nondeterministic .binary32 0x28800000 rfl).mpr rfl)
  · exact evalRelaxedFmaRel_of_unfused .nondeterministic .binary32
      ((evalFloatBinOpRel_of_not_nan .nondeterministic .mul .binary32 0x3f800002 rfl).mpr rfl)
      ((evalFloatBinOpRel_of_not_nan .nondeterministic .add .binary32 0x00000000 rfl).mpr rfl)

/-- `EvalFloatToFloatRel` collapses deterministically on finite values
(`1.5_f32 → 1.5_f64`) while admitting both positive and negative canonical and
payload-shifted quiet NaN candidates on NaN inputs under RFC 3514. -/
theorem canary_float_to_float_rel_nondet :
    EvalFloatToFloatRel .nondeterministic .binary32 .binary64
      0x3fc00000 0x3ff8000000000000 ∧
    EvalFloatToFloatRel .nondeterministic .binary32 .binary64
      0x7fc00001 0x7ff8000000000000 ∧
    EvalFloatToFloatRel .nondeterministic .binary32 .binary64
      0x7fc00001 0xfff8000020000000 := by
  refine ⟨?_, ?_, ?_⟩
  · exact (evalFloatToFloatRel_of_not_nan .nondeterministic .binary32 .binary64
      0x3ff8000000000000 rfl).mpr rfl
  · exact List.Mem.head _
  · exact List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))

/-! ## 3. Casts: Saturating `as`, Checked Intrinsic, & Ties-to-Even -/

/-- `FloatToInt` saturating vs `float_to_int_unchecked` UB discrimination, plus
`i64` `2^53 + 1 = 9007199254740993` `tiesToEven` (`0x4340_0000_0000_0000`) vs
`tiesAwayFromZero` (`0x4340_0000_0000_0001`) separation. -/
theorem canary_casts_saturation_and_ties_to_even :
    (evalFloatToIntSaturating .binary32 0x7fc00000 ⟨.i32, true⟩ .bits64).bits = 0 ∧
    (evalFloatToIntSaturating .binary32 0x7f800000 ⟨.i8, false⟩ .bits64).bits = 255 ∧
    (evalFloatToIntSaturating .binary32 0xff800000 ⟨.i8, true⟩ .bits64).bits = 128 ∧
    evalFloatToIntChecked .binary32 0x43808000 ⟨.i8, false⟩ .bits64 = none ∧
    evalFloatToIntChecked .binary32 0x42280000 ⟨.i8, false⟩ .bits64 = some (Int.ofNat 42) ∧
    evalIntToFloatRoundTiesToEven true 64 9007199254740993 .binary64 =
      0x4340000000000000 ∧
    evalIntToFloat .tiesAwayFromZero true 64 9007199254740993 .binary64 =
      0x4340000000000001 := by
  exact ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩

/-! ## 4. Sterbenz Guards & Audio/Video DSP Enclosures (`Opus`, `swscale`) -/

/-- `checkSterbenzSub` accepts `[3, 4]` vs `[2, 5]` (`5 ≤ 2·3 ∧ 4 ≤ 2·2`) while
rejecting `[3, 3]` vs `[1, 33554430]` and `[-3, -3]` vs `[-33554430, -1]`, so
`encloseSubIeee` widens `[3, 3] - [1, 33554430]` to enclose the rounded `f32`
result `3.0 - 33554430.0 = -33554428.0` (`0xcbff_fffe`). -/
theorem canary_sterbenz_corner_soundness_and_neg_control :
    checkSterbenzSub ⟨Int.ofNat 3, Int.ofNat 4, Int.ofNat 0⟩
      ⟨Int.ofNat 2, Int.ofNat 5, Int.ofNat 0⟩ = true ∧
    checkSterbenzSub ⟨Int.ofNat 3, Int.ofNat 3, Int.ofNat 0⟩
      ⟨Int.ofNat 1, Int.ofNat 33554430, Int.ofNat 0⟩ = false ∧
    checkSterbenzSub ⟨Int.neg (Int.ofNat 3), Int.neg (Int.ofNat 3), Int.ofNat 0⟩
      ⟨Int.neg (Int.ofNat 33554430), Int.neg (Int.ofNat 1), Int.ofNat 0⟩ = false ∧
    evalFloatArithBase .sub .binary32 0x40400000 0x4bffffff = 0xcbfffffe ∧
    (match encloseSubIeee .binary32
        ⟨Int.ofNat 3, Int.ofNat 3, Int.ofNat 0⟩
        ⟨Int.ofNat 1, Int.ofNat 33554430, Int.ofNat 0⟩ 0,
          floatBitsToBox .binary32 0xcbfffffe with
     | some subBox, some actualPt =>
       checkFiniteEnclosure actualPt subBox .binary32
     | _, _ => false) = true := by
  exact ⟨rfl, rfl, rfl, rfl, rfl⟩

/-- Normalized `[-1.0, 1.0]` audio spectrum box (`exp2 = 0`). -/
@[expose] def unitAudioBox : DyadicBox :=
  { lo := Int.neg (Int.ofNat 1), hi := Int.ofNat 1, exp2 := Int.ofNat 0 }

/-- Exact `f32` twiddle bit-pinning for `cos(π/8) ≈ 0.9238795325`
(`0x3f6c_835e = 15500126 · 2^-24`) and `sin(π/8) ≈ 0.3826834324`
(`0x3ec3_ef15 = 12840725 · 2^-25`): verifies exact dyadic decoding,
`roundRatioTiesToEven` from 10-digit decimal approximations, and unit-circle
norm `cos² + sin² = 1 - 2^-24` (`0x3f7f_ffff`) in `f32`. -/
theorem canary_imdct_pi_over_8_twiddle_bits_pinned :
    floatBitsToBox .binary32 0x3f6c835e =
      some { lo := Int.ofNat 15500126
             hi := Int.ofNat 15500126
             exp2 := Int.neg (Int.ofNat 24) } ∧
    floatBitsToBox .binary32 0x3ec3ef15 =
      some { lo := Int.ofNat 12840725
             hi := Int.ofNat 12840725
             exp2 := Int.neg (Int.ofNat 25) } ∧
    roundRatioTiesToEven .binary32 false 9238795325 10000000000 = 0x3f6c835e ∧
    roundRatioTiesToEven .binary32 false 3826834324 10000000000 = 0x3ec3ef15 ∧
    evalFloatArithBase .add .binary32
      (evalFloatArithBase .mul .binary32 0x3f6c835e 0x3f6c835e)
      (evalFloatArithBase .mul .binary32 0x3ec3ef15 0x3ec3ef15) = 0x3f7fffff := by
  exact ⟨rfl, rfl, rfl, rfl, rfl⟩

/-- Exact `f32` twiddle boxes for `cos(π/8) ≈ 0.9238795` (`0x3f6c_835e`) and
`sin(π/8) ≈ 0.38268343` (`0x3ec3_ef15`) used in `Opus` CELT / `AAC` / `Vorbis`
IMDCT butterflies, bounded within `[-11900000 · 2^-23, +11900000 · 2^-23]`
(`≈ [-1.4186, +1.4186]`) across unfused `mul±mul` and `simd_relaxed_fma`
contractions. -/
theorem canary_opus_aac_imdct_butterfly_enclosure :
    (match floatBitsToBox .binary32 0x3f6c835e,
           floatBitsToBox .binary32 0x3ec3ef15 with
     | some cosB, some sinB =>
       match encloseImdctButterflyIeee .binary32 unitAudioBox unitAudioBox
           cosB sinB 24 with
       | some (reOut, imOut) =>
         let bound : DyadicBox :=
           { lo := Int.neg (Int.ofNat 11900000)
             hi := Int.ofNat 11900000
             exp2 := Int.neg (Int.ofNat 23) }
         checkFiniteEnclosure reOut bound .binary32 &&
           checkFiniteEnclosure imOut bound .binary32
       | none => false
     | _, _ => false) = true := by
  rfl

/-- `Opus` / `AAC` float-to-`i16` PCM output stage: scaling `[-1.0, 1.0]` by
`32766.0_f32` (`0x46ff_fc00`) passes `checkFloatToIntSafe` into `i16`
(`[-32768, 32767]`), whereas scaling by `32769.0_f32` (`0x4700_0100`) is
rejected (negative control). -/
theorem canary_opus_pcm_i16_quant_and_neg_control :
    (match floatBitsToBox .binary32 0x46fffc00 with
     | some gainB =>
       match encloseMulIeee .binary32 unitAudioBox gainB 24 with
       | some pcmBox => checkFloatToIntSafe pcmBox .bits64 ⟨.i16, true⟩
       | none => false
     | none => false) = true ∧
    (match floatBitsToBox .binary32 0x47000100 with
     | some badGainB =>
       match encloseMulIeee .binary32 unitAudioBox badGainB 24 with
       | some badPcmBox => checkFloatToIntSafe badPcmBox .bits64 ⟨.i16, true⟩
       | none => false
     | none => false) = false := by
  exact ⟨rfl, rfl⟩

/-- `swscale` 4-tap symmetric polyphase rescaler `[-1/16, 9/16, 9/16, -1/16]`
over `[0, 255]` `u8` luma pixels:
(1) Enclosed within `[-33, +288]` inside `maxFiniteBox .binary32`,
(2) Safe `i16` intermediate cast (`[-32768, 32767]`), and
(3) Negative control catching Lanczos ringing outside `[0, 255]` (`u8`
    `float_to_int_unchecked` without `[0, 255]` clamp would be UB). -/
theorem canary_swscale_polyphase_4tap_enclosure_and_ringing_catch :
    let tapNeg : DyadicBox :=
      { lo := Int.neg (Int.ofNat 1), hi := Int.neg (Int.ofNat 1),
        exp2 := Int.neg (Int.ofNat 4) }
    let tapPos : DyadicBox :=
      { lo := Int.ofNat 9, hi := Int.ofNat 9, exp2 := Int.neg (Int.ofNat 4) }
    let u8Pixel : DyadicBox :=
      { lo := Int.ofNat 0, hi := Int.ofNat 255, exp2 := Int.ofNat 0 }
    let targetBound : DyadicBox :=
      { lo := Int.neg (Int.ofNat 33), hi := Int.ofNat 288, exp2 := Int.ofNat 0 }
    match encloseFirDotIeee .binary32 [tapNeg, tapPos, tapPos, tapNeg] u8Pixel 24 with
    | none => False
    | some firBox =>
      checkFiniteEnclosure firBox targetBound .binary32 = true ∧
      checkFloatToIntSafe firBox .bits64 ⟨.i16, true⟩ = true ∧
      checkFloatToIntSafe firBox .bits64 ⟨.i8, false⟩ = false := by
  exact ⟨rfl, rfl, rfl⟩

/-- `af_biquads` / `Opus` SILK complex-conjugate-pole Q14 resonator
(`S = 16384 = 2^14`, `a₁ = -28000`, `a₂ = 14000`, where
`a₁² = 784_000_000 < 4 S a₂ = 917_504_000`):
certifies `JuryStable`, positive-definite `steinDet > 0`, and exact Lyapunov
contraction, paired with a negative control rejecting unstable `a₂ = 17000`
(`J₁ = 16384 - 17000 < 0`). -/
theorem canary_af_biquads_complex_pole_jury_stein :
    let S := Int.ofNat 16384
    let a1 := Int.neg (Int.ofNat 28000)
    let a2 := Int.ofNat 14000
    JuryStable S a1 a2 ∧
    IntPos (steinDet S a1 a2) ∧
    intLeB (Int.ofNat 1) (juryJ1 S (Int.ofNat 17000)) = false := by
  refine ⟨?_, ?_, rfl⟩
  · refine ⟨?_, ?_, ?_, ?_⟩
    · exact (intLeB_iff_le (Int.ofNat 1) (Int.ofNat 16384)).mp rfl
    · exact (intLeB_iff_le (Int.ofNat 1)
        (juryJ1 (Int.ofNat 16384) (Int.ofNat 14000))).mp rfl
    · exact (intLeB_iff_le (Int.ofNat 1)
        (juryJ2 (Int.ofNat 16384) (Int.neg (Int.ofNat 28000)) (Int.ofNat 14000))).mp rfl
    · exact (intLeB_iff_le (Int.ofNat 1)
        (juryJ3 (Int.ofNat 16384) (Int.neg (Int.ofNat 28000)) (Int.ofNat 14000))).mp rfl
  · have hJ : JuryStable (Int.ofNat 16384) (Int.neg (Int.ofNat 28000)) (Int.ofNat 14000) :=
      ⟨(intLeB_iff_le _ _).mp rfl,
       (intLeB_iff_le _ _).mp rfl,
       (intLeB_iff_le _ _).mp rfl,
       (intLeB_iff_le _ _).mp rfl⟩
    exact (stein_pos_def_of_jury hJ).2.2.2

end Anneal.Float.Canaries

end
