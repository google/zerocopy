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
public import Init.Data.List.Basic
public import Anneal.InitLemmas
public import Anneal.LinearArith
public import Anneal.Float.SoftFloat
public import Anneal.Float.IeeeCast
public import Anneal.Float.IeeeArith

public section

/-!
# Outward Dyadic Intervals, Sterbenz & DSP Enclosures (`DyadicCert`)

Pass-1-pure (`0` TCB LOC, `0` `._unsafe_rec`, `0` `Classical.choice`,
axioms `⊆ [propext, Quot.sound]`) outward dyadic interval algebra, Sterbenz and
integer-cast safety checkers, and computable Flocq/FloatLib mixed-error IEEE-754
rounding evaluators over `Init.Data.Int` for audio/video DSP kernels (`Opus`,
`AAC`, `Vorbis`, `af_afir`, `swresample`, `swscale`):

1. **Kernel-Verified Outward Dyadic Interval Algebra (`DyadicBox`,
   `compressBy`, `alignBoxes`, `addBox`, `subBox`, `hullBox`, `negBox`):**
   - Represents `[lo · 2^exp2, hi · 2^exp2]` over `Int` without `ℝ` or Mathlib,
     guarded by a 256-bit alignment/mantissa cap matching Lean's
     `check_nat_size`.
   - Proves exact rational soundness (`intFloorShr_sound`, `intCeilShr_sound`,
     `intFloorShr_ceilShr_bracket`, `negBox_sound`, `compressBy_sound`,
     `alignBoxes_sound`, `addBox_sound`, `subBox_sound`, `hullBox_sound_left`,
     `hullBox_sound_right`).
2. **Kernel-Verified Sterbenz, Finite-Range, & `FloatToInt` Safety Checkers:**
   - `checkSterbenzSub` + `checkSterbenzSub_sound`: proves worst-case corner
     satisfaction of Sterbenz's exact-subtraction condition (`y ≤ 2x ∧ x ≤ 2y`
     on nonnegative boxes, `2x ≤ y ∧ 2y ≤ x` on nonpositive boxes) for every
     pair of enclosed rationals.
   - `floatBitsToBox` + `floatBitsToBox_sound`, `checkInFiniteRange` +
     `checkInFiniteRange_sound`, `checkFiniteEnclosure` +
     `checkFiniteEnclosure_sound`, and `checkFloatToIntSafe` +
     `checkFloatToIntSafe_sound` (proving `evalFloatToIntChecked = some`,
     discharging `float_to_int_unchecked` UB for every enclosed finite float).
3. **Computable IEEE-754 Mixed-Error Rounding Evaluators (`widenMixedError`,
   `encloseAddIeee`, `encloseSubIeee`, `encloseMulIeee`, `encloseFmaIeee`,
   `encloseRelaxedFmaIeee`, `encloseFirDotIeee`, `encloseImdctButterflyIeee`):**
   - Evaluates outward mixed relative/subnormal error bounds
     (`max(2^-p |x|, η_f)`, `I_fused ⊔ I_unfused` for `simd_relaxed_fma`, FIR
     dot products, and 3-contraction IMDCT butterflies); linking
     `roundRatioBits` directly to `widenMixedError` is left to Phase-2
     correspondence proofs.
-/

namespace Anneal.Float

open Anneal.LinearArith

/-! ## Part I: Real-Free Rational Semantics & Outward Shift Compression -/

/-- Exact rational `num / den` (`0 < den` invariant). -/
structure RatVal : Type where
  num : Int
  den : Nat

/-- Cross-multiplied rational inequality `p.num * q.den ≤ q.num * p.den`. -/
@[expose] def ratLe (p q : RatVal) : Prop :=
  Int.mul p.num (Int.ofNat q.den) ≤ Int.mul q.num (Int.ofNat p.den)

/-- Cross-multiplied rational equality `p.num * q.den = q.num * p.den`. -/
@[expose] def ratEq (p q : RatVal) : Prop :=
  Int.mul p.num (Int.ofNat q.den) = Int.mul q.num (Int.ofNat p.den)

/-- Exact rational addition `p + q`. -/
@[expose] def ratAdd (p q : RatVal) : RatVal :=
  { num := Int.add (Int.mul p.num (Int.ofNat q.den))
      (Int.mul q.num (Int.ofNat p.den))
    den := p.den * q.den }

/-- Exact rational subtraction `p - q`. -/
@[expose] def ratSub (p q : RatVal) : RatVal :=
  ratAdd p ⟨Int.neg q.num, q.den⟩

/-- Embed dyadic `m · 2^exp2` as an exact `RatVal` (`0 < den`). -/
@[expose] def dyadicToRat (m : Int) (exp2 : Int) : RatVal :=
  match exp2 with
  | .ofNat k => ⟨Int.mul m (Int.ofNat (pow2 k)), 1⟩
  | .negSucc k => ⟨m, pow2 (k + 1)⟩

/-- Closed dyadic interval `[lo · 2^exp2, hi · 2^exp2]`. -/
structure DyadicBox : Type where
  lo : Int
  hi : Int
  exp2 : Int

/-- Semantic membership `q ∈ [b.lo · 2^b.exp2, b.hi · 2^b.exp2]`. -/
@[expose] def inDyadicBox (q : RatVal) (b : DyadicBox) : Prop :=
  ratLe (dyadicToRat b.lo b.exp2) q ∧ ratLe q (dyadicToRat b.hi b.exp2)

/-- Floor right-shift `⌊x / 2^s⌋` rounding toward `-∞`. -/
@[expose] def intFloorShr (x : Int) (s : Nat) : Int :=
  let p := pow2 s
  match x with
  | .ofNat n => .ofNat (Nat.div n p)
  | .negSucc n => .negSucc (Nat.div n p)

/-- Ceiling right-shift `⌈x / 2^s⌉ = -⌊(-x) / 2^s⌋` rounding toward `+∞`. -/
@[expose] def intCeilShr (x : Int) (s : Nat) : Int :=
  Int.neg (intFloorShr (Int.neg x) s)

/-- Outward-directed dyadic mantissa compression by `shift` bits. -/
@[expose] def compressBy (b : DyadicBox) (shift : Nat) : DyadicBox :=
  match Nat.beq shift 0 with
  | true => b
  | false =>
    { lo := intFloorShr b.lo shift
      hi := intCeilShr b.hi shift
      exp2 := Int.add b.exp2 (Int.ofNat shift) }

/-- Negate a `DyadicBox` (`[-hi, -lo] · 2^exp2`). -/
@[expose] def negBox (b : DyadicBox) : DyadicBox :=
  { lo := Int.neg b.hi, hi := Int.neg b.lo, exp2 := b.exp2 }

/-- Exact point `DyadicBox` for integer `n` (`[n, n] · 2^0`). -/
@[expose] def intPointBox (n : Int) : DyadicBox :=
  { lo := n, hi := n, exp2 := Int.ofNat 0 }

/-- Exact rational decoding of finite `f`-format bit patterns (`none` on `NaN`
or `±∞`). -/
@[expose] def decodeFiniteRat (f : IeeeFormat) (bits : Nat) : Option RatVal :=
  match decodeBits f (Nat.mod bits (pow2 f.width)) with
  | .zero _ => some ⟨Int.ofNat 0, 1⟩
  | .finite neg n d => some ⟨signedNum neg n, d⟩
  | .inf _ => none
  | .nan _ _ _ => none

/-- Decode any finite `f`-format bit pattern into an exact point `DyadicBox`
(`none` on `NaN` or `±∞`). -/
@[expose] def floatBitsToBox (f : IeeeFormat) (bits : Nat) : Option DyadicBox :=
  let c := unpackBits f (Nat.mod bits (pow2 f.width))
  match Nat.beq c.exponent f.allOnesExp with
  | true => none
  | false =>
    match Nat.beq c.exponent 0 with
    | true =>
      match Nat.beq c.fraction 0 with
      | true => some { lo := Int.ofNat 0, hi := Int.ofNat 0, exp2 := Int.ofNat 0 }
      | false =>
        let m := signedNum c.neg c.fraction
        let e := Int.sub f.minExponent (Int.ofNat f.fractionBits)
        some { lo := m, hi := m, exp2 := e }
    | false =>
      let m := signedNum c.neg (pow2 f.fractionBits + c.fraction)
      let e := Int.sub (Int.sub (Int.ofNat c.exponent) (Int.ofNat f.bias))
        (Int.ofNat f.fractionBits)
      some { lo := m, hi := m, exp2 := e }

/-! ## Part II: 256-Bit Guarded Interval Operations & IEEE-754 Evaluators -/

/-- Align two boxes to `min b1.exp2 b2.exp2` with a 256-bit shift DoS cap. -/
@[expose] def alignBoxes (b1 b2 : DyadicBox) :
    Option (Int × Int × Int × Int × Int) :=
  match intEqB b1.exp2 b2.exp2 with
  | true => some (b1.lo, b1.hi, b2.lo, b2.hi, b1.exp2)
  | false =>
    match intLtB b1.exp2 b2.exp2 with
    | true =>
      let diff := Int.natAbs (Int.sub b2.exp2 b1.exp2)
      match Nat.ble diff 256 with
      | true =>
        let scale := Int.ofNat (pow2 diff)
        some (b1.lo, b1.hi, Int.mul b2.lo scale, Int.mul b2.hi scale, b1.exp2)
      | false => none
    | false =>
      let diff := Int.natAbs (Int.sub b1.exp2 b2.exp2)
      match Nat.ble diff 256 with
      | true =>
        let scale := Int.ofNat (pow2 diff)
        some (Int.mul b1.lo scale, Int.mul b1.hi scale, b2.lo, b2.hi, b2.exp2)
      | false => none

/-- Outward dyadic box addition. -/
@[expose] def addBox (b1 b2 : DyadicBox) (shift : Nat) : Option DyadicBox :=
  match alignBoxes b1 b2 with
  | none => none
  | some (l1, h1, l2, h2, e) =>
    some (compressBy { lo := Int.add l1 l2, hi := Int.add h1 h2, exp2 := e } shift)

/-- Outward dyadic box subtraction. -/
@[expose] def subBox (b1 b2 : DyadicBox) (shift : Nat) : Option DyadicBox :=
  match alignBoxes b1 b2 with
  | none => none
  | some (l1, h1, l2, h2, e) =>
    some (compressBy { lo := Int.sub l1 h2, hi := Int.sub h1 l2, exp2 := e } shift)

/-- Convex hull `b1 ⊔ b2` (used to enclose `simd_relaxed_fma` branches). -/
@[expose] def hullBox (b1 b2 : DyadicBox) (shift : Nat) : Option DyadicBox :=
  match alignBoxes b1 b2 with
  | none => none
  | some (l1, h1, l2, h2, e) =>
    some (compressBy { lo := intMin l1 l2, hi := intMax h1 h2, exp2 := e } shift)

/-- Minimum of 4 integers. -/
@[expose] def minInt4 (a b c d : Int) : Int :=
  intMin (intMin a b) (intMin c d)

/-- Maximum of 4 integers. -/
@[expose] def maxInt4 (a b c d : Int) : Int :=
  intMax (intMax a b) (intMax c d)

/-- Outward dyadic box multiplication guarded at 256-bit mantissa magnitudes. -/
@[expose] def mulBox (b1 b2 : DyadicBox) (shift : Nat) : Option DyadicBox :=
  let cap := pow2 256
  match Nat.blt (Int.natAbs b1.lo) cap && Nat.blt (Int.natAbs b1.hi) cap &&
        Nat.blt (Int.natAbs b2.lo) cap && Nat.blt (Int.natAbs b2.hi) cap with
  | false => none
  | true =>
    let p1 := Int.mul b1.lo b2.lo
    let p2 := Int.mul b1.lo b2.hi
    let p3 := Int.mul b1.hi b2.lo
    let p4 := Int.mul b1.hi b2.hi
    some (compressBy
      { lo := minInt4 p1 p2 p3 p4
        hi := maxInt4 p1 p2 p3 p4
        exp2 := Int.add b1.exp2 b2.exp2 } shift)

/-- Exact finite range `[-MAX_FINITE, +MAX_FINITE]` of IEEE-754 format `f`. -/
@[expose] def maxFiniteBox (f : IeeeFormat) : DyadicBox :=
  let maxSig := Int.sub (Int.ofNat (pow2 f.precision)) (Int.ofNat 1)
  { lo := Int.neg maxSig
    hi := maxSig
    exp2 := Int.sub f.maxExponent (Int.ofNat f.fractionBits) }

/-- Sterbenz exact-subtraction corner check on aligned boxes (`0 ≤ l1, l2` with
`h2 ≤ 2·l1 ∧ h1 ≤ 2·l2`, or `h1, h2 ≤ 0` with `2·h1 ≤ l2 ∧ 2·h2 ≤ l1`). See
`checkSterbenzSub_sound` for universal corner entailment across all `x ∈ b1`
and `y ∈ b2`. -/
@[expose] def checkSterbenzSub (b1 b2 : DyadicBox) : Bool :=
  match alignBoxes b1 b2 with
  | none => false
  | some (l1, h1, l2, h2, _) =>
    (intLeB (Int.ofNat 0) l1 &&
      intLeB (Int.ofNat 0) l2 &&
      intLeB h2 (Int.mul (Int.ofNat 2) l1) &&
      intLeB h1 (Int.mul (Int.ofNat 2) l2)) ||
    (intLeB h1 (Int.ofNat 0) &&
      intLeB h2 (Int.ofNat 0) &&
      intLeB (Int.mul (Int.ofNat 2) h1) l2 &&
      intLeB (Int.mul (Int.ofNat 2) h2) l1)

/-- Checks `actual ⊆ target` AND `actual ⊆ maxFiniteBox f` (soundness:
`checkFiniteEnclosure_sound`). -/
@[expose] def checkFiniteEnclosure (actual target : DyadicBox)
    (f : IeeeFormat) : Bool :=
  match alignBoxes actual target, alignBoxes actual (maxFiniteBox f) with
  | some (al, ah, tl, th, _), some (al2, ah2, ml, mh, _) =>
    intLeB al ah && intLeB tl al && intLeB ah th &&
      intLeB ml al2 && intLeB ah2 mh
  | _, _ => false

/-- Checks that every value in `b` lies within the finite range of `f`
(`b ⊆ maxFiniteBox f`; soundness: `checkInFiniteRange_sound`). -/
@[expose] def checkInFiniteRange (b : DyadicBox) (f : IeeeFormat) : Bool :=
  match alignBoxes b (maxFiniteBox f) with
  | some (bl, bh, ml, mh, _) =>
    intLeB bl bh && intLeB ml bl && intLeB bh mh
  | none => false

/-- Computable Flocq/FloatLib mixed-error rounding widener for IEEE-754
`roundTiesToEven`: checks `b ⊆ maxFiniteBox f` and widens `b` by the maximum
of `2^-p · max(|b.lo|, |b.hi|)` and (when `includeSubnormalUlp` holds)
`2^(e_min - p)`. On `add`/`sub`, Hauser's subnormal-exactness property allows
`includeSubnormalUlp = false` (`η = 0`). -/
@[expose] def widenMixedError (f : IeeeFormat) (includeSubnormalUlp : Bool)
    (b : DyadicBox) (shift : Nat) : Option DyadicBox :=
  match checkInFiniteRange b f with
  | false => none
  | true =>
    let maxAbs := Nat.max (Int.natAbs b.lo) (Int.natAbs b.hi)
    let relBox : DyadicBox :=
      { lo := Int.neg (Int.ofNat maxAbs)
        hi := Int.ofNat maxAbs
        exp2 := Int.sub b.exp2 (Int.ofNat f.precision) }
    let errOpt : Option DyadicBox :=
      match includeSubnormalUlp with
      | false => some relBox
      | true =>
        let subBox : DyadicBox :=
          { lo := Int.neg (Int.ofNat 1)
            hi := Int.ofNat 1
            exp2 := Int.sub f.minExponent (Int.ofNat f.precision) }
        hullBox relBox subBox 0
    match errOpt with
    | none => none
    | some errB => addBox b errB shift

/-- Computable outward IEEE-754 `add` enclosure (`η = 0`). -/
@[expose] def encloseAddIeee (f : IeeeFormat) (b1 b2 : DyadicBox)
    (shift : Nat) : Option DyadicBox :=
  match addBox b1 b2 0 with
  | none => none
  | some exactSum => widenMixedError f false exactSum shift

/-- Computable outward IEEE-754 `sub` enclosure (skips rounding widening when
`checkSterbenzSub b1 b2` holds; otherwise widens with `η = 0`). -/
@[expose] def encloseSubIeee (f : IeeeFormat) (b1 b2 : DyadicBox)
    (shift : Nat) : Option DyadicBox :=
  match subBox b1 b2 0 with
  | none => none
  | some exactDiff =>
    match checkSterbenzSub b1 b2 && checkInFiniteRange exactDiff f with
    | true => some (compressBy exactDiff shift)
    | false => widenMixedError f false exactDiff shift

/-- Computable outward IEEE-754 `mul` enclosure (includes subnormal half-ULP
`η_f`). -/
@[expose] def encloseMulIeee (f : IeeeFormat) (b1 b2 : DyadicBox)
    (shift : Nat) : Option DyadicBox :=
  match mulBox b1 b2 0 with
  | none => none
  | some exactProd => widenMixedError f true exactProd shift

/-- Computable outward single-rounded IEEE-754 `fma(a, b, c)` enclosure. -/
@[expose] def encloseFmaIeee (f : IeeeFormat) (a b c : DyadicBox)
    (shift : Nat) : Option DyadicBox :=
  match mulBox a b 0 with
  | none => none
  | some abExact =>
    match addBox abExact c 0 with
    | none => none
    | some fmaExact => widenMixedError f true fmaExact shift

/-- Computable outward RFC 3514 `simd_relaxed_fma(a, b, c)` enclosure
(`I_fused ⊔ I_unfused`). -/
@[expose] def encloseRelaxedFmaIeee (f : IeeeFormat) (a b c : DyadicBox)
    (shift : Nat) : Option DyadicBox :=
  match encloseFmaIeee f a b c shift with
  | none => none
  | some fusedB =>
    match encloseMulIeee f a b shift with
    | none => none
    | some abRounded =>
      match encloseAddIeee f abRounded c shift with
      | none => none
      | some unfusedB => hullBox fusedB unfusedB shift

/-- Checks that every value in `b` lies within
`[target.minValue pw, target.maxValue pw]`, discharging `float_to_int_unchecked`
UB via `checkFloatToIntSafe_sound`. -/
@[expose] def checkFloatToIntSafe (b : DyadicBox) (pw : FloatPtrWidth)
    (target : FloatIntTarget) : Bool :=
  let intRangeBox : DyadicBox :=
    { lo := target.minValue pw
      hi := target.maxValue pw
      exp2 := Int.ofNat 0 }
  match alignBoxes b intRangeBox with
  | none => false
  | some (bl, bh, il, ih, _) =>
    intLeB bl bh && intLeB il bl && intLeB bh ih

/-! ## Part III: Audio/Video Media-DSP Kernel Evaluators (Opus / swscale) -/

/-- Sequential IEEE-754 FIR dot-product enclosure evaluator over `taps` with
uniform sample range `sampleRange` (models `swscale` polyphase horizontal and
vertical filters, `swresample`, and `af_afir` time-domain taps). -/
@[expose] def encloseFirDotIeee (f : IeeeFormat) (taps : List DyadicBox)
    (sampleRange : DyadicBox) (shift : Nat) : Option DyadicBox :=
  List.foldl
    (fun accOpt tap =>
      match accOpt with
      | none => none
      | some acc =>
        match encloseMulIeee f tap sampleRange shift with
        | none => none
        | some prod => encloseAddIeee f acc prod shift)
    (some (intPointBox (Int.ofNat 0)))
    taps

/-- 2D IMDCT / CELT twiddle rotation butterfly enclosure evaluator
`(x * cosTw - y * sinTw, x * sinTw + y * cosTw)` taking the convex hull across
unfused `mul±mul` and both `simd_relaxed_fma` contractions (`fma(x, cos, -ys)`
and `fma(-y, sin, xc)` on the real axis; `fma(x, sin, yc)` on the imaginary
axis). -/
@[expose] def encloseImdctButterflyIeee (f : IeeeFormat)
    (xBox yBox cosBox sinBox : DyadicBox) (shift : Nat) :
    Option (DyadicBox × DyadicBox) :=
  match encloseMulIeee f xBox cosBox shift,
        encloseMulIeee f yBox sinBox shift,
        encloseMulIeee f xBox sinBox shift,
        encloseMulIeee f yBox cosBox shift with
  | some xcRounded, some ysRounded, some xsRounded, some ycRounded =>
    match encloseSubIeee f xcRounded ysRounded shift,
          encloseRelaxedFmaIeee f xBox cosBox (negBox ysRounded) shift,
          encloseRelaxedFmaIeee f (negBox yBox) sinBox xcRounded shift,
          encloseAddIeee f xsRounded ycRounded shift,
          encloseRelaxedFmaIeee f xBox sinBox ycRounded shift with
    | some reUnfused, some reFmaPos, some reFmaNeg, some imUnfused,
        some imFma =>
      match hullBox reUnfused reFmaPos shift,
            hullBox imUnfused imFma shift with
      | some reHull12, some imOut =>
        match hullBox reHull12 reFmaNeg shift with
        | some reOut => some (reOut, imOut)
        | none => none
      | _, _ => none
    | _, _, _, _, _ => none
  | _, _, _, _ => none

/-! ## Part IV: Kernel-Checked Interval, Sterbenz, & Cast-Safety Proofs -/

private theorem nat_div_add_mod_dc (a b : Nat) :
    b * Nat.div a b + Nat.mod a b = a :=
  Nat.div_add_mod a b

private theorem natBle_iff_le_dc : ∀ a b : Nat, Nat.ble a b = true ↔ a ≤ b
  | 0, b => ⟨fun _ => Nat.zero_le b, fun _ => rfl⟩
  | _ + 1, 0 => ⟨fun h => Bool.noConfusion h, fun h => nomatch h⟩
  | a + 1, b + 1 =>
    ⟨fun h => Nat.succ_le_succ ((natBle_iff_le_dc a b).mp h),
     fun h => (natBle_iff_le_dc a b).mpr (Nat.le_of_succ_le_succ h)⟩

private theorem natBeq_refl_dc : ∀ n : Nat, Nat.beq n n = true
  | 0 => rfl
  | n + 1 => natBeq_refl_dc n

private theorem natBeq_iff_eq_dc (a b : Nat) : Nat.beq a b = true ↔ a = b :=
  ⟨Nat.eq_of_beq_eq_true, fun h => by subst h; exact natBeq_refl_dc a⟩

private theorem int_le_refl_dc (a : Int) : a ≤ a :=
  (intBalance_le (intBalance_self a) (intBalance_self a)).mpr (Nat.le_refl _)

private theorem int_le_trans_dc {a b c : Int} (h1 : a ≤ b) (h2 : b ≤ c) :
    a ≤ c := by
  have ha := intBalance_self a
  have hb := intBalance_self b
  have hc := intBalance_self c
  have hn1 := (intBalance_le ha hb).mp h1
  have hn2 := (intBalance_le hb hc).mp h2
  apply (intBalance_le ha hc).mpr
  have hSum := Nat.add_le_add hn1 hn2
  have hL :
      (intPos a + intNeg b) + (intPos b + intNeg c) =
        (intPos a + intNeg c) + (intPos b + intNeg b) := by
    rw [add_four_rearrange (intPos a) (intNeg b) (intPos b) (intNeg c),
      Nat.add_comm (intNeg b) (intNeg c),
      ← add_four_rearrange (intPos a) (intNeg c) (intPos b) (intNeg b)]
  have hR :
      (intPos b + intNeg a) + (intPos c + intNeg b) =
        (intPos c + intNeg a) + (intPos b + intNeg b) := by
    rw [add_four_rearrange (intPos b) (intNeg a) (intPos c) (intNeg b),
      Nat.add_comm (intPos b) (intPos c),
      ← add_four_rearrange (intPos c) (intNeg a) (intPos b) (intNeg b)]
  rw [hL, hR] at hSum
  exact Nat.le_of_add_le_add_right hSum

private theorem int_mul_comm_dc (a b : Int) : Int.mul a b = Int.mul b a :=
  intBalance_eq_of_eq
    (intBalance_mul (intBalance_self a) (intBalance_self b))
    (intBalance_of_add_eq
      (intBalance_mul (intBalance_self b) (intBalance_self a))
      (by
        rw [Nat.mul_comm (intPos b) (intPos a),
          Nat.mul_comm (intNeg b) (intNeg a),
          Nat.mul_comm (intPos b) (intNeg a),
          Nat.mul_comm (intNeg b) (intPos a),
          Nat.add_comm (intNeg a * intPos b) (intPos a * intNeg b)]))

private theorem int_neg_mul_left_dc (a b : Int) :
    Int.mul (Int.neg a) b = Int.neg (Int.mul a b) := by
  have h1 := intBalance_mul (intBalance_neg (intBalance_self a))
    (intBalance_self b)
  have h2 := intBalance_neg (intBalance_mul (intBalance_self a)
    (intBalance_self b))
  have hEqP :
      intPos a * intNeg b + intNeg a * intPos b =
        intNeg a * intPos b + intPos a * intNeg b :=
    Nat.add_comm _ _
  have hEqN :
      intPos a * intPos b + intNeg a * intNeg b =
        intNeg a * intNeg b + intPos a * intPos b :=
    Nat.add_comm _ _
  rw [hEqP, hEqN] at h2
  exact intBalance_eq_of_eq h1 h2

private theorem int_neg_neg_dc (a : Int) : Int.neg (Int.neg a) = a :=
  intBalance_eq_of_eq
    (intBalance_neg (intBalance_neg (intBalance_self a)))
    (intBalance_self a)

private theorem int_neg_le_neg_dc {x y : Int} (h : x ≤ y) :
    Int.neg y ≤ Int.neg x := by
  have hB := (intBalance_le (intBalance_self x) (intBalance_self y)).mp h
  apply (intBalance_le
    (intBalance_neg (intBalance_self y))
    (intBalance_neg (intBalance_self x))).mpr
  rw [Nat.add_comm (intNeg y), Nat.add_comm (intNeg x)]
  exact hB

private theorem int_mul_one_dc (x : Int) : Int.mul x (Int.ofNat 1) = x := by
  rw [int_mul_comm_dc]
  exact intBalance_eq_of_eq
    (intBalance_mul_nat 1 (intBalance_self x))
    (intBalance_of_add_eq (intBalance_self x)
      (by rw [Nat.one_mul, Nat.one_mul]))

private theorem int_mul_ofNat_assoc_dc (x : Int) (k1 k2 : Nat) :
    Int.mul (Int.mul x (Int.ofNat k1)) (Int.ofNat k2) =
      Int.mul x (Int.ofNat (k1 * k2)) := by
  cases x with
  | ofNat m =>
    change Int.ofNat ((m * k1) * k2) = Int.ofNat (m * (k1 * k2))
    exact congrArg Int.ofNat (Nat.mul_assoc m k1 k2)
  | negSucc m =>
    rw [int_mul_negSucc_left, int_neg_mul_left_dc, int_mul_negSucc_left]
    change Int.neg (Int.ofNat (((m + 1) * k1) * k2)) =
      Int.neg (Int.ofNat ((m + 1) * (k1 * k2)))
    exact congrArg (fun z => Int.neg (Int.ofNat z))
      (Nat.mul_assoc (m + 1) k1 k2)

private theorem int_add_mul_ofNat_dc (x y : Int) (k : Nat) :
    Int.mul (Int.add x y) (Int.ofNat k) =
      Int.add (Int.mul x (Int.ofNat k)) (Int.mul y (Int.ofNat k)) := by
  rw [int_mul_comm_dc (Int.add x y) (Int.ofNat k),
    int_mul_comm_dc x (Int.ofNat k),
    int_mul_comm_dc y (Int.ofNat k)]
  exact intBalance_eq_of_eq
    (intBalance_mul_nat k (intBalance_add (intBalance_self x)
      (intBalance_self y)))
    (intBalance_of_add_eq
      (intBalance_add (intBalance_mul_nat k (intBalance_self x))
        (intBalance_mul_nat k (intBalance_self y)))
      (by rw [Nat.mul_add, Nat.mul_add]))

private theorem int_mul_ofNat_right_le_dc (k : Nat) {x y : Int} (h : x ≤ y) :
    Int.mul x (Int.ofNat k) ≤ Int.mul y (Int.ofNat k) := by
  rw [int_mul_comm_dc x (Int.ofNat k), int_mul_comm_dc y (Int.ofNat k)]
  exact int_mul_nat_le_mul_nat k h

private theorem int_le_of_mul_ofNat_right_dc {x y : Int} {k : Nat}
    (hk : 0 < k) (h : Int.mul x (Int.ofNat k) ≤ Int.mul y (Int.ofNat k)) :
    x ≤ y := by
  rw [int_mul_comm_dc x (Int.ofNat k), int_mul_comm_dc y (Int.ofNat k)] at h
  have ha := intBalance_self x
  have hb := intBalance_self y
  have hNat := (intBalance_le (intBalance_mul_nat k ha)
    (intBalance_mul_nat k hb)).mp h
  rw [← Nat.mul_add, ← Nat.mul_add] at hNat
  exact (intBalance_le ha hb).mpr (Nat.le_of_mul_le_mul_left hNat hk)

private theorem intEqB_iff_eq_dc (a b : Int) : intEqB a b = true ↔ a = b := by
  cases a with
  | ofNat m =>
    cases b with
    | ofNat n =>
      dsimp only [intEqB]
      exact ⟨fun h => congrArg Int.ofNat ((natBeq_iff_eq_dc m n).mp h),
        fun h => (natBeq_iff_eq_dc m n).mpr (Int.ofNat.inj h)⟩
    | negSucc _ =>
      dsimp only [intEqB]
      exact ⟨fun h => Bool.noConfusion h, fun h => nomatch h⟩
  | negSucc m =>
    cases b with
    | ofNat _ =>
      dsimp only [intEqB]
      exact ⟨fun h => Bool.noConfusion h, fun h => nomatch h⟩
    | negSucc n =>
      dsimp only [intEqB]
      exact ⟨fun h => congrArg Int.negSucc ((natBeq_iff_eq_dc m n).mp h),
        fun h => (natBeq_iff_eq_dc m n).mpr (Int.negSucc.inj h)⟩

private theorem intMin_le_left_dc (a b : Int) : intMin a b ≤ a := by
  dsimp only [intMin]
  cases h : intLeB a b with
  | true => exact int_le_refl_dc a
  | false => exact le_of_intLeB_false h

private theorem intMin_le_right_dc (a b : Int) : intMin a b ≤ b := by
  dsimp only [intMin]
  cases h : intLeB a b with
  | true => exact (intLeB_iff_le a b).mp h
  | false => exact int_le_refl_dc b

private theorem le_intMax_left_dc (a b : Int) : a ≤ intMax a b := by
  dsimp only [intMax]
  cases h : intLeB a b with
  | true => exact (intLeB_iff_le a b).mp h
  | false => exact int_le_refl_dc a

private theorem le_intMax_right_dc (a b : Int) : b ≤ intMax a b := by
  dsimp only [intMax]
  cases h : intLeB a b with
  | true => exact int_le_refl_dc b
  | false => exact le_of_intLeB_false h

private theorem dyadicToRat_den_pos (m e : Int) :
    0 < (dyadicToRat m e).den := by
  cases e with
  | ofNat _ => exact Nat.zero_lt_succ 0
  | negSucc k => exact pow2_pos (k + 1)

private theorem ratLe_refl (q : RatVal) : ratLe q q :=
  int_le_refl_dc _

private theorem ratLe_trans {a b c : RatVal} (hb : 0 < b.den)
    (hab : ratLe a b) (hbc : ratLe b c) : ratLe a c := by
  dsimp only [ratLe] at hab hbc
  dsimp only [ratLe]
  have h1 := int_mul_ofNat_right_le_dc c.den hab
  have h2 := int_mul_ofNat_right_le_dc a.den hbc
  rw [int_mul_ofNat_assoc_dc a.num b.den c.den,
    Nat.mul_comm b.den c.den,
    ← int_mul_ofNat_assoc_dc a.num c.den b.den] at h1
  rw [int_mul_ofNat_assoc_dc b.num a.den c.den,
    Nat.mul_comm a.den c.den,
    ← int_mul_ofNat_assoc_dc b.num c.den a.den] at h1
  rw [int_mul_ofNat_assoc_dc c.num b.den a.den,
    Nat.mul_comm b.den a.den,
    ← int_mul_ofNat_assoc_dc c.num a.den b.den] at h2
  exact int_le_of_mul_ofNat_right_dc hb (int_le_trans_dc h1 h2)

private theorem ratEq_symm {p q : RatVal} (h : ratEq p q) : ratEq q p :=
  h.symm

private theorem ratLe_of_ratEq_left {p p' q : RatVal} (hp : 0 < p.den)
    (hEq : ratEq p p') (hLe : ratLe p q) : ratLe p' q := by
  have hEqLe : ratLe p' p := by
    dsimp only [ratLe]
    rw [← hEq]
    exact int_le_refl_dc _
  exact ratLe_trans hp hEqLe hLe

private theorem ratLe_of_ratEq_right {p q q' : RatVal} (hq : 0 < q.den)
    (hEq : ratEq q q') (hLe : ratLe p q) : ratLe p q' := by
  have hEqLe : ratLe q q' := by
    dsimp only [ratLe]
    rw [hEq]
    exact int_le_refl_dc _
  exact ratLe_trans hq hLe hEqLe

private theorem dyadicToRat_mono {m1 m2 : Int} (e : Int) (h : m1 ≤ m2) :
    ratLe (dyadicToRat m1 e) (dyadicToRat m2 e) := by
  cases e with
  | ofNat k =>
    dsimp only [dyadicToRat, ratLe]
    exact int_mul_ofNat_right_le_dc 1 (int_mul_ofNat_right_le_dc (pow2 k) h)
  | negSucc k =>
    dsimp only [dyadicToRat, ratLe]
    exact int_mul_ofNat_right_le_dc (pow2 (k + 1)) h

private theorem dyadicToRat_shift (m e : Int) (s : Nat) :
    ratEq (dyadicToRat m (Int.add e (Int.ofNat s)))
      (dyadicToRat (Int.mul m (Int.ofNat (pow2 s))) e) := by
  cases e with
  | ofNat k =>
    change ratEq (dyadicToRat m (Int.ofNat (k + s)))
      (dyadicToRat (Int.mul m (Int.ofNat (pow2 s))) (Int.ofNat k))
    dsimp only [dyadicToRat, ratEq]
    rw [int_mul_ofNat_assoc_dc m (pow2 s) (pow2 k),
      ← pow2_add s k, Nat.add_comm s k]
  | negSucc k =>
    change ratEq (dyadicToRat m (Int.subNatNat s (k + 1)))
      (dyadicToRat (Int.mul m (Int.ofNat (pow2 s))) (Int.negSucc k))
    unfold Int.subNatNat
    cases hSub : (k + 1) - s with
    | zero =>
      have hLe : k + 1 ≤ s := Nat.le_of_sub_eq_zero hSub
      dsimp only [dyadicToRat, ratEq]
      rw [int_mul_ofNat_assoc_dc m (pow2 (s - (k + 1))) (pow2 (k + 1)),
        ← pow2_add, Nat.sub_add_cancel hLe, int_mul_one_dc]
    | succ d =>
      have hLt : s < k + 1 := Nat.lt_of_sub_eq_succ hSub
      have hAdd : (d + 1) + s = k + 1 := by
        rw [← hSub]
        exact Nat.sub_add_cancel (Nat.le_of_lt hLt)
      dsimp only [dyadicToRat, ratEq]
      rw [int_mul_ofNat_assoc_dc m (pow2 s) (pow2 (d + 1)),
        ← pow2_add s (d + 1), Nat.add_comm s (d + 1), hAdd]

/-- Outward floor-shift soundness (`[propext]` only):
`⌊x / 2^s⌋ · 2^s ≤ x` for every `x : Int` and `s : Nat`. -/
theorem intFloorShr_sound (x : Int) (s : Nat) :
    Int.mul (intFloorShr x s) (Int.ofNat (pow2 s)) ≤ x := by
  have hPos : 0 < pow2 s := pow2_pos s
  cases x with
  | ofNat n =>
    dsimp only [intFloorShr]
    have hLe : Nat.div n (pow2 s) * pow2 s ≤ n :=
      Nat.div_mul_le_self n (pow2 s)
    have hMulEq :
        Int.mul (Int.ofNat (Nat.div n (pow2 s))) (Int.ofNat (pow2 s)) =
          Int.ofNat (Nat.div n (pow2 s) * pow2 s) := rfl
    rw [hMulEq]
    apply (intBalance_le
      (intBalance_ofNat (Nat.div n (pow2 s) * pow2 s))
      (intBalance_ofNat n)).mpr
    rw [Nat.add_zero, Nat.add_zero]
    exact hLe
  | negSucc n =>
    dsimp only [intFloorShr]
    have hDivMod := nat_div_add_mod_dc n (pow2 s)
    have hModLt : Nat.mod n (pow2 s) + 1 ≤ pow2 s :=
      Nat.mod_lt n hPos
    have hUpper : n + 1 ≤ (Nat.div n (pow2 s) + 1) * pow2 s := by
      have hStep :
          pow2 s * Nat.div n (pow2 s) + (Nat.mod n (pow2 s) + 1) ≤
            pow2 s * Nat.div n (pow2 s) + pow2 s :=
        Nat.add_le_add_left hModLt _
      rw [← Nat.add_assoc, hDivMod] at hStep
      have hRhs :
          pow2 s * Nat.div n (pow2 s) + pow2 s =
            (Nat.div n (pow2 s) + 1) * pow2 s := by
        rw [Nat.add_mul, Nat.one_mul, Nat.mul_comm (pow2 s)]
      rw [hRhs] at hStep
      exact hStep
    rw [int_mul_negSucc_left]
    have hMulPos :
        Int.mul (Int.ofNat (Nat.div n (pow2 s) + 1)) (Int.ofNat (pow2 s)) =
          Int.ofNat ((Nat.div n (pow2 s) + 1) * pow2 s) := rfl
    rw [hMulPos]
    apply (intBalance_le
      (intBalance_neg (intBalance_ofNat ((Nat.div n (pow2 s) + 1) * pow2 s)))
      (intBalance_self (Int.negSucc n))).mpr
    dsimp only [intPos, intNeg]
    rw [Nat.zero_add, Nat.zero_add]
    exact hUpper

/-- Outward ceiling-shift soundness (`[propext]` only):
`x ≤ ⌈x / 2^s⌉ · 2^s` for every `x : Int` and `s : Nat`. -/
theorem intCeilShr_sound (x : Int) (s : Nat) :
    x ≤ Int.mul (intCeilShr x s) (Int.ofNat (pow2 s)) := by
  dsimp only [intCeilShr]
  rw [int_neg_mul_left_dc]
  have hNeg := int_neg_le_neg_dc (intFloorShr_sound (Int.neg x) s)
  rw [int_neg_neg_dc] at hNeg
  exact hNeg

private theorem dyadicToRat_neg (m e : Int) :
    dyadicToRat (Int.neg m) e =
      ⟨Int.neg (dyadicToRat m e).num, (dyadicToRat m e).den⟩ := by
  cases e with
  | negSucc _ => rfl
  | ofNat k =>
    dsimp only [dyadicToRat]
    rw [int_neg_mul_left_dc]

/-- Negating a `DyadicBox` negates every enclosed rational (`[propext]`
only). -/
theorem negBox_sound {q : RatVal} {b : DyadicBox}
    (hq : inDyadicBox q b) :
    inDyadicBox ⟨Int.neg q.num, q.den⟩ (negBox b) := by
  dsimp only [inDyadicBox, negBox, ratLe] at hq
  dsimp only [inDyadicBox, negBox, ratLe]
  rw [dyadicToRat_neg b.hi b.exp2, dyadicToRat_neg b.lo b.exp2]
  dsimp only
  rw [int_neg_mul_left_dc, int_neg_mul_left_dc,
    int_neg_mul_left_dc, int_neg_mul_left_dc]
  exact ⟨int_neg_le_neg_dc hq.2, int_neg_le_neg_dc hq.1⟩

/-- Combined outward floor/ceiling shift bracket (`[propext]` only):
`⌊x / 2^s⌋ · 2^s ≤ x ≤ ⌈x / 2^s⌉ · 2^s` for every `x : Int` and `s : Nat`. -/
theorem intFloorShr_ceilShr_bracket (x : Int) (s : Nat) :
    Int.mul (intFloorShr x s) (Int.ofNat (pow2 s)) ≤ x ∧
      x ≤ Int.mul (intCeilShr x s) (Int.ofNat (pow2 s)) :=
  ⟨intFloorShr_sound x s, intCeilShr_sound x s⟩

/-- Outward shift compression preserves rational membership (`[propext]`
only). -/
theorem compressBy_sound {q : RatVal} {b : DyadicBox} (shift : Nat)
    (_hqDen : 0 < q.den) (hq : inDyadicBox q b) :
    inDyadicBox q (compressBy b shift) := by
  dsimp only [compressBy]
  cases Nat.beq shift 0 with
  | true => exact hq
  | false =>
    dsimp only [inDyadicBox]
    have hLoStep :
        ratLe (dyadicToRat (Int.mul (intFloorShr b.lo shift)
          (Int.ofNat (pow2 shift))) b.exp2) q :=
      ratLe_trans (dyadicToRat_den_pos b.lo b.exp2)
        (dyadicToRat_mono b.exp2 (intFloorShr_sound b.lo shift)) hq.1
    have hLo :
        ratLe (dyadicToRat (intFloorShr b.lo shift)
          (Int.add b.exp2 (Int.ofNat shift))) q :=
      ratLe_of_ratEq_left
        (dyadicToRat_den_pos _ b.exp2)
        (ratEq_symm (dyadicToRat_shift (intFloorShr b.lo shift) b.exp2 shift))
        hLoStep
    have hHiStep :
        ratLe q (dyadicToRat (Int.mul (intCeilShr b.hi shift)
          (Int.ofNat (pow2 shift))) b.exp2) :=
      ratLe_trans (dyadicToRat_den_pos b.hi b.exp2)
        hq.2 (dyadicToRat_mono b.exp2 (intCeilShr_sound b.hi shift))
    have hHi :
        ratLe q (dyadicToRat (intCeilShr b.hi shift)
          (Int.add b.exp2 (Int.ofNat shift))) :=
      ratLe_of_ratEq_right
        (dyadicToRat_den_pos _ b.exp2)
        (ratEq_symm (dyadicToRat_shift (intCeilShr b.hi shift) b.exp2 shift))
        hHiStep
    exact ⟨hLo, hHi⟩

private theorem add_natAbs_sub_of_le_dc {e1 e2 : Int} (hLe : e1 ≤ e2) :
    Int.add e1 (Int.ofNat (Int.natAbs (Int.sub e2 e1))) = e2 := by
  have hb1 := intBalance_self e1
  have hb2 := intBalance_self e2
  have hDiff := intBalance_sub hb2 hb1
  cases hSub : Int.sub e2 e1 with
  | negSucc _ =>
    change Int.NonNeg (Int.sub e2 e1) at hLe
    rw [hSub] at hLe
    nomatch hLe
  | ofNat d =>
    rw [hSub] at hDiff
    dsimp only [Int.natAbs]
    dsimp only [IntBalance, intPos, intNeg] at hDiff
    rw [Nat.zero_add] at hDiff
    exact intBalance_eq_of_eq
      (intBalance_add hb1 (intBalance_ofNat d))
      (intBalance_of_add_eq hb2
        (by
          have hDiff' : d + (intNeg e2 + intPos e1) = intPos e2 + intNeg e1 :=
            hDiff
          rw [Nat.add_comm (intNeg e2) (intPos e1)] at hDiff'
          rw [Nat.add_zero, Nat.add_comm (intPos e1) d, ← hDiff',
            ← Nat.add_assoc d (intPos e1) (intNeg e2)]))

private theorem intLe_of_intLtB_true_dc {a b : Int} (h : intLtB a b = true) :
    a ≤ b := by
  dsimp only [intLtB] at h
  have h1 := (intLeB_iff_le _ b).mp h
  have h01 : a ≤ Int.add a (Int.ofNat 1) := by
    apply (intBalance_le (intBalance_self a)
      (intBalance_add (intBalance_self a) (intBalance_ofNat 1))).mpr
    rw [Nat.add_zero, add_three_mid (intPos a) 1 (intNeg a)]
    exact Nat.le_add_right _ 1
  exact int_le_trans_dc h01 h1

private theorem intLe_of_intLtB_false_dc {a b : Int} (h : intLtB a b = false) :
    b ≤ a := by
  dsimp only [intLtB] at h
  have hGe : b ≤ Int.add a (Int.ofNat 1) := le_of_intLeB_false h
  have hb := intBalance_self b
  have ha := intBalance_self a
  cases Nat.lt_or_ge (intPos b + intNeg a) (intPos a + intNeg b + 1) with
  | inl hLt =>
    exact (intBalance_le hb ha).mpr (Nat.le_of_lt_succ hLt)
  | inr hGeNat =>
    have hAB : Int.add a (Int.ofNat 1) ≤ b := by
      apply (intBalance_le (intBalance_add ha (intBalance_ofNat 1)) hb).mpr
      rw [Nat.add_zero, add_three_mid (intPos a) 1 (intNeg b)]
      exact hGeNat
    have hT : intLeB (Int.add a (Int.ofNat 1)) b = true :=
      (intLeB_iff_le _ _).mpr hAB
    rw [h] at hT
    exact Bool.noConfusion hT

private theorem inDyadicBox_scale_exp {q : RatVal} {b : DyadicBox}
    {e : Int} {diff : Nat}
    (hExp : Int.add e (Int.ofNat diff) = b.exp2)
    (hq : inDyadicBox q b) :
    inDyadicBox q
      { lo := Int.mul b.lo (Int.ofNat (pow2 diff))
        hi := Int.mul b.hi (Int.ofNat (pow2 diff))
        exp2 := e } := by
  dsimp only [inDyadicBox] at hq
  dsimp only [inDyadicBox]
  rw [← hExp] at hq
  have hLo := ratLe_of_ratEq_left
    (dyadicToRat_den_pos b.lo (Int.add e (Int.ofNat diff)))
    (dyadicToRat_shift b.lo e diff) hq.1
  have hHi := ratLe_of_ratEq_right
    (dyadicToRat_den_pos b.hi (Int.add e (Int.ofNat diff)))
    (dyadicToRat_shift b.hi e diff) hq.2
  exact ⟨hLo, hHi⟩

/-- `alignBoxes` preserves rational membership in both operands (`[propext]`
only). -/
theorem alignBoxes_sound {b1 b2 : DyadicBox} {l1 h1 l2 h2 e : Int}
    (hAlign : alignBoxes b1 b2 = some (l1, h1, l2, h2, e)) :
    (∀ q1 : RatVal, inDyadicBox q1 b1 → inDyadicBox q1 ⟨l1, h1, e⟩) ∧
      (∀ q2 : RatVal, inDyadicBox q2 b2 → inDyadicBox q2 ⟨l2, h2, e⟩) := by
  dsimp only [alignBoxes] at hAlign
  cases hEq : intEqB b1.exp2 b2.exp2 with
  | true =>
    rw [hEq] at hAlign
    injection hAlign with hTup
    have hl1 : b1.lo = l1 := congrArg Prod.fst hTup
    have hh1 : b1.hi = h1 := congrArg (fun t => t.2.1) hTup
    have hl2 : b2.lo = l2 := congrArg (fun t => t.2.2.1) hTup
    have hh2 : b2.hi = h2 := congrArg (fun t => t.2.2.2.1) hTup
    have he : b1.exp2 = e := congrArg (fun t => t.2.2.2.2) hTup
    subst hl1; subst hh1; subst hl2; subst hh2; subst he
    have hExpEq : b1.exp2 = b2.exp2 := (intEqB_iff_eq_dc _ _).mp hEq
    exact ⟨fun _ h => h, fun _ h => by
      dsimp only [inDyadicBox] at h
      dsimp only [inDyadicBox]
      rw [hExpEq]
      exact h⟩
  | false =>
    rw [hEq] at hAlign
    dsimp only at hAlign
    cases hLt : intLtB b1.exp2 b2.exp2 with
    | true =>
      rw [hLt] at hAlign
      dsimp only at hAlign
      cases hCap : Nat.ble (Int.natAbs (Int.sub b2.exp2 b1.exp2)) 256 with
      | false => rw [hCap] at hAlign; nomatch hAlign
      | true =>
        rw [hCap] at hAlign
        injection hAlign with hTup
        have hl1 := congrArg Prod.fst hTup
        have hh1 := congrArg (fun t => t.2.1) hTup
        have hl2 := congrArg (fun t => t.2.2.1) hTup
        have hh2 := congrArg (fun t => t.2.2.2.1) hTup
        have he := congrArg (fun t => t.2.2.2.2) hTup
        subst hl1; subst hh1; subst hl2; subst hh2; subst he
        have hExp :
            Int.add b1.exp2 (Int.ofNat (Int.natAbs (Int.sub b2.exp2 b1.exp2))) =
              b2.exp2 :=
          add_natAbs_sub_of_le_dc (intLe_of_intLtB_true_dc hLt)
        exact ⟨fun _ h => h, fun _ h => inDyadicBox_scale_exp hExp h⟩
    | false =>
      rw [hLt] at hAlign
      dsimp only at hAlign
      cases hCap : Nat.ble (Int.natAbs (Int.sub b1.exp2 b2.exp2)) 256 with
      | false => rw [hCap] at hAlign; nomatch hAlign
      | true =>
        rw [hCap] at hAlign
        injection hAlign with hTup
        have hl1 := congrArg Prod.fst hTup
        have hh1 := congrArg (fun t => t.2.1) hTup
        have hl2 := congrArg (fun t => t.2.2.1) hTup
        have hh2 := congrArg (fun t => t.2.2.2.1) hTup
        have he := congrArg (fun t => t.2.2.2.2) hTup
        subst hl1; subst hh1; subst hl2; subst hh2; subst he
        have hExp :
            Int.add b2.exp2 (Int.ofNat (Int.natAbs (Int.sub b1.exp2 b2.exp2))) =
              b1.exp2 :=
          add_natAbs_sub_of_le_dc (intLe_of_intLtB_false_dc hLt)
        exact ⟨fun _ h => inDyadicBox_scale_exp hExp h, fun _ h => h⟩

private theorem ratAdd_same_exp_sound {q1 q2 : RatVal}
    {l1 h1 l2 h2 e : Int}
    (hq1 : inDyadicBox q1 ⟨l1, h1, e⟩)
    (hq2 : inDyadicBox q2 ⟨l2, h2, e⟩) :
    inDyadicBox (ratAdd q1 q2) ⟨Int.add l1 l2, Int.add h1 h2, e⟩ := by
  dsimp only [inDyadicBox] at hq1 hq2
  dsimp only [inDyadicBox, ratAdd]
  cases e with
  | ofNat k =>
    dsimp only [dyadicToRat, ratLe] at hq1 hq2
    dsimp only [dyadicToRat, ratLe]
    rw [int_mul_one_dc] at hq1 hq2
    rw [int_mul_one_dc]
    have hL1 := int_mul_ofNat_right_le_dc q2.den hq1.1
    have hL2 := int_mul_ofNat_right_le_dc q1.den hq2.1
    have hH1 := int_mul_ofNat_right_le_dc q2.den hq1.2
    have hH2 := int_mul_ofNat_right_le_dc q1.den hq2.2
    rw [int_mul_ofNat_assoc_dc (Int.mul l1 (Int.ofNat (pow2 k))) q1.den q2.den]
      at hL1
    rw [int_mul_ofNat_assoc_dc (Int.mul l2 (Int.ofNat (pow2 k))) q2.den q1.den,
      Nat.mul_comm q2.den q1.den] at hL2
    rw [int_mul_ofNat_assoc_dc (Int.mul h1 (Int.ofNat (pow2 k))) q1.den q2.den]
      at hH1
    rw [int_mul_ofNat_assoc_dc (Int.mul h2 (Int.ofNat (pow2 k))) q2.den q1.den,
      Nat.mul_comm q2.den q1.den] at hH2
    rw [int_add_mul_ofNat_dc l1 l2 (pow2 k),
      int_add_mul_ofNat_dc _ _ (q1.den * q2.den),
      int_add_mul_ofNat_dc h1 h2 (pow2 k),
      int_add_mul_ofNat_dc _ _ (q1.den * q2.den)]
    exact ⟨int_add_le_add hL1 hL2, int_add_le_add hH1 hH2⟩
  | negSucc k =>
    dsimp only [dyadicToRat, ratLe] at hq1 hq2
    dsimp only [dyadicToRat, ratLe]
    have hL1 := int_mul_ofNat_right_le_dc q2.den hq1.1
    have hL2 := int_mul_ofNat_right_le_dc q1.den hq2.1
    have hH1 := int_mul_ofNat_right_le_dc q2.den hq1.2
    have hH2 := int_mul_ofNat_right_le_dc q1.den hq2.2
    rw [int_mul_ofNat_assoc_dc l1 q1.den q2.den] at hL1
    rw [int_mul_ofNat_assoc_dc l2 q2.den q1.den,
      Nat.mul_comm q2.den q1.den] at hL2
    rw [int_mul_ofNat_assoc_dc q1.num (pow2 (k + 1)) q2.den,
      Nat.mul_comm (pow2 (k + 1)) q2.den,
      ← int_mul_ofNat_assoc_dc q1.num q2.den (pow2 (k + 1))] at hL1 hH1
    rw [int_mul_ofNat_assoc_dc q2.num (pow2 (k + 1)) q1.den,
      Nat.mul_comm (pow2 (k + 1)) q1.den,
      ← int_mul_ofNat_assoc_dc q2.num q1.den (pow2 (k + 1))] at hL2 hH2
    rw [int_mul_ofNat_assoc_dc h1 q1.den q2.den] at hH1
    rw [int_mul_ofNat_assoc_dc h2 q2.den q1.den,
      Nat.mul_comm q2.den q1.den] at hH2
    rw [int_add_mul_ofNat_dc l1 l2 (q1.den * q2.den),
      int_add_mul_ofNat_dc h1 h2 (q1.den * q2.den),
      int_add_mul_ofNat_dc _ _ (pow2 (k + 1))]
    exact ⟨int_add_le_add hL1 hL2, int_add_le_add hH1 hH2⟩

/-- `addBox` encloses the exact rational sum `ratAdd q1 q2` (`[propext]`
only). -/
theorem addBox_sound {q1 q2 : RatVal} {b1 b2 out : DyadicBox} {shift : Nat}
    (hq1Den : 0 < q1.den) (hq2Den : 0 < q2.den)
    (hq1 : inDyadicBox q1 b1) (hq2 : inDyadicBox q2 b2)
    (hAdd : addBox b1 b2 shift = some out) :
    inDyadicBox (ratAdd q1 q2) out := by
  dsimp only [addBox] at hAdd
  cases hAl : alignBoxes b1 b2 with
  | none => rw [hAl] at hAdd; nomatch hAdd
  | some tup =>
    rw [hAl] at hAdd
    cases tup with
    | mk l1 rest1 =>
      cases rest1 with
      | mk h1 rest2 =>
        cases rest2 with
        | mk l2 rest3 =>
          cases rest3 with
          | mk h2 e =>
            injection hAdd with hOut
            subst hOut
            have hPair := alignBoxes_sound hAl
            have hDenPos : 0 < (ratAdd q1 q2).den :=
              Nat.mul_pos hq1Den hq2Den
            exact compressBy_sound shift hDenPos
              (ratAdd_same_exp_sound (hPair.1 q1 hq1) (hPair.2 q2 hq2))

/-- `subBox` encloses the exact rational difference `ratSub q1 q2` (`[propext]`
only). -/
theorem subBox_sound {q1 q2 : RatVal} {b1 b2 out : DyadicBox} {shift : Nat}
    (hq1Den : 0 < q1.den) (hq2Den : 0 < q2.den)
    (hq1 : inDyadicBox q1 b1) (hq2 : inDyadicBox q2 b2)
    (hSub : subBox b1 b2 shift = some out) :
    inDyadicBox (ratSub q1 q2) out := by
  dsimp only [subBox] at hSub
  cases hAl : alignBoxes b1 b2 with
  | none => rw [hAl] at hSub; nomatch hSub
  | some tup =>
    rw [hAl] at hSub
    cases tup with
    | mk l1 rest1 =>
      cases rest1 with
      | mk h1 rest2 =>
        cases rest2 with
        | mk l2 rest3 =>
          cases rest3 with
          | mk h2 e =>
            injection hSub with hOut
            subst hOut
            have hPair := alignBoxes_sound hAl
            have hNeg2 : inDyadicBox ⟨Int.neg q2.num, q2.den⟩
                ⟨Int.neg h2, Int.neg l2, e⟩ :=
              negBox_sound (hPair.2 q2 hq2)
            have hDenPos : 0 < (ratSub q1 q2).den :=
              Nat.mul_pos hq1Den hq2Den
            exact compressBy_sound shift hDenPos
              (ratAdd_same_exp_sound (hPair.1 q1 hq1) hNeg2)

/-- Left branch inclusion in `hullBox` (`[propext]` only). -/
theorem hullBox_sound_left {q : RatVal} {b1 b2 out : DyadicBox} {shift : Nat}
    (hqDen : 0 < q.den) (hq : inDyadicBox q b1)
    (hHull : hullBox b1 b2 shift = some out) :
    inDyadicBox q out := by
  dsimp only [hullBox] at hHull
  cases hAl : alignBoxes b1 b2 with
  | none => rw [hAl] at hHull; nomatch hHull
  | some tup =>
    rw [hAl] at hHull
    cases tup with
    | mk l1 rest1 =>
      cases rest1 with
      | mk h1 rest2 =>
        cases rest2 with
        | mk l2 rest3 =>
          cases rest3 with
          | mk h2 e =>
            injection hHull with hOut
            subst hOut
            have hA := (alignBoxes_sound hAl).1 q hq
            have hLo := ratLe_trans (dyadicToRat_den_pos l1 e)
              (dyadicToRat_mono e (intMin_le_left_dc l1 l2)) hA.1
            have hHi := ratLe_trans (dyadicToRat_den_pos h1 e)
              hA.2 (dyadicToRat_mono e (le_intMax_left_dc h1 h2))
            exact compressBy_sound shift hqDen ⟨hLo, hHi⟩

/-- Right branch inclusion in `hullBox` (`[propext]` only). -/
theorem hullBox_sound_right {q : RatVal} {b1 b2 out : DyadicBox} {shift : Nat}
    (hqDen : 0 < q.den) (hq : inDyadicBox q b2)
    (hHull : hullBox b1 b2 shift = some out) :
    inDyadicBox q out := by
  dsimp only [hullBox] at hHull
  cases hAl : alignBoxes b1 b2 with
  | none => rw [hAl] at hHull; nomatch hHull
  | some tup =>
    rw [hAl] at hHull
    cases tup with
    | mk l1 rest1 =>
      cases rest1 with
      | mk h1 rest2 =>
        cases rest2 with
        | mk l2 rest3 =>
          cases rest3 with
          | mk h2 e =>
            injection hHull with hOut
            subst hOut
            have hA := (alignBoxes_sound hAl).2 q hq
            have hLo := ratLe_trans (dyadicToRat_den_pos l2 e)
              (dyadicToRat_mono e (intMin_le_right_dc l1 l2)) hA.1
            have hHi := ratLe_trans (dyadicToRat_den_pos h2 e)
              hA.2 (dyadicToRat_mono e (le_intMax_right_dc h1 h2))
            exact compressBy_sound shift hqDen ⟨hLo, hHi⟩

private theorem int_zero_mul_ofNat_dc (k : Nat) :
    Int.mul (Int.ofNat 0) (Int.ofNat k) = Int.ofNat 0 := by
  change Int.ofNat (0 * k) = Int.ofNat 0
  rw [Nat.zero_mul]

private theorem dyadicToRat_zero (e : Int) :
    ratEq ⟨Int.ofNat 0, 1⟩ (dyadicToRat (Int.ofNat 0) e) := by
  cases e with
  | ofNat k =>
    dsimp only [dyadicToRat, ratEq]
    rw [int_zero_mul_ofNat_dc, int_zero_mul_ofNat_dc, int_zero_mul_ofNat_dc]
  | negSucc k =>
    dsimp only [dyadicToRat, ratEq]
    rw [int_zero_mul_ofNat_dc, int_zero_mul_ofNat_dc]

private theorem dyadicToRat_two_mul (m e : Int) :
    ratEq (dyadicToRat (Int.mul (Int.ofNat 2) m) e)
      ⟨Int.mul (Int.ofNat 2) (dyadicToRat m e).num, (dyadicToRat m e).den⟩ := by
  cases e with
  | negSucc _ => rfl
  | ofNat k =>
    dsimp only [dyadicToRat, ratEq]
    rw [int_mul_one_dc, int_mul_one_dc,
      int_mul_comm_dc (Int.ofNat 2) m,
      int_mul_ofNat_assoc_dc m 2 (pow2 k),
      Nat.mul_comm 2 (pow2 k),
      ← int_mul_ofNat_assoc_dc m (pow2 k) 2,
      int_mul_comm_dc _ (Int.ofNat 2)]

private theorem ratLe_two_mul_mono {p q : RatVal} (h : ratLe p q) :
    ratLe ⟨Int.mul (Int.ofNat 2) p.num, p.den⟩
      ⟨Int.mul (Int.ofNat 2) q.num, q.den⟩ := by
  dsimp only [ratLe] at h
  dsimp only [ratLe]
  have h2 := int_mul_nat_le_mul_nat 2 h
  have hAssocL :
      Int.mul (Int.mul (Int.ofNat 2) p.num) (Int.ofNat q.den) =
        Int.mul (Int.ofNat 2) (Int.mul p.num (Int.ofNat q.den)) := by
    rw [int_mul_comm_dc (Int.ofNat 2) p.num,
      int_mul_ofNat_assoc_dc p.num 2 q.den,
      Nat.mul_comm 2 q.den,
      ← int_mul_ofNat_assoc_dc p.num q.den 2,
      int_mul_comm_dc _ (Int.ofNat 2)]
  have hAssocR :
      Int.mul (Int.mul (Int.ofNat 2) q.num) (Int.ofNat p.den) =
        Int.mul (Int.ofNat 2) (Int.mul q.num (Int.ofNat p.den)) := by
    rw [int_mul_comm_dc (Int.ofNat 2) q.num,
      int_mul_ofNat_assoc_dc q.num 2 p.den,
      Nat.mul_comm 2 p.den,
      ← int_mul_ofNat_assoc_dc q.num p.den 2,
      int_mul_comm_dc _ (Int.ofNat 2)]
  rw [hAssocL, hAssocR]
  exact h2

/-- Universal Sterbenz corner soundness (`[propext]` only): whenever
`checkSterbenzSub b1 b2 = true`, every `q1 ∈ b1` and `q2 ∈ b2` satisfies either
the nonnegative Sterbenz bounds (`0 ≤ q1, 0 ≤ q2, q2 ≤ 2·q1, q1 ≤ 2·q2`) or the
nonpositive mirror bounds (`q1 ≤ 0, q2 ≤ 0, 2·q1 ≤ q2, 2·q2 ≤ q1`). -/
theorem checkSterbenzSub_sound {q1 q2 : RatVal} {b1 b2 : DyadicBox}
    (hSterb : checkSterbenzSub b1 b2 = true)
    (hq1 : inDyadicBox q1 b1) (hq2 : inDyadicBox q2 b2) :
    (ratLe ⟨Int.ofNat 0, 1⟩ q1 ∧ ratLe ⟨Int.ofNat 0, 1⟩ q2 ∧
      ratLe q2 ⟨Int.mul (Int.ofNat 2) q1.num, q1.den⟩ ∧
      ratLe q1 ⟨Int.mul (Int.ofNat 2) q2.num, q2.den⟩) ∨
    (ratLe q1 ⟨Int.ofNat 0, 1⟩ ∧ ratLe q2 ⟨Int.ofNat 0, 1⟩ ∧
      ratLe ⟨Int.mul (Int.ofNat 2) q1.num, q1.den⟩ q2 ∧
      ratLe ⟨Int.mul (Int.ofNat 2) q2.num, q2.den⟩ q1) := by
  dsimp only [checkSterbenzSub] at hSterb
  cases hAl : alignBoxes b1 b2 with
  | none => rw [hAl] at hSterb; nomatch hSterb
  | some tup =>
    rw [hAl] at hSterb
    cases tup with
    | mk l1 rest1 =>
      cases rest1 with
      | mk h1 rest2 =>
        cases rest2 with
        | mk l2 rest3 =>
          cases rest3 with
          | mk h2 e =>
            dsimp only at hSterb
            have hPair := alignBoxes_sound hAl
            have hA1 := hPair.1 q1 hq1
            have hA2 := hPair.2 q2 hq2
            dsimp only [inDyadicBox] at hA1 hA2
            cases hPosBr :
                intLeB (Int.ofNat 0) l1 &&
                  intLeB (Int.ofNat 0) l2 &&
                  intLeB h2 (Int.mul (Int.ofNat 2) l1) &&
                  intLeB h1 (Int.mul (Int.ofNat 2) l2) with
            | true =>
              apply Or.inl
              have hP123 := Anneal.InitLemmas.bool_and_left hPosBr
              have hC4 := (intLeB_iff_le _ _).mp
                (Anneal.InitLemmas.bool_and_right hPosBr)
              have hP12 := Anneal.InitLemmas.bool_and_left hP123
              have hC3 := (intLeB_iff_le _ _).mp
                (Anneal.InitLemmas.bool_and_right hP123)
              have hC1 := (intLeB_iff_le _ _).mp
                (Anneal.InitLemmas.bool_and_left hP12)
              have hC2 := (intLeB_iff_le _ _).mp
                (Anneal.InitLemmas.bool_and_right hP12)
              have h0q1 : ratLe ⟨Int.ofNat 0, 1⟩ q1 :=
                ratLe_of_ratEq_left (dyadicToRat_den_pos (Int.ofNat 0) e)
                  (ratEq_symm (dyadicToRat_zero e))
                  (ratLe_trans (dyadicToRat_den_pos l1 e)
                    (dyadicToRat_mono e hC1) hA1.1)
              have h0q2 : ratLe ⟨Int.ofNat 0, 1⟩ q2 :=
                ratLe_of_ratEq_left (dyadicToRat_den_pos (Int.ofNat 0) e)
                  (ratEq_symm (dyadicToRat_zero e))
                  (ratLe_trans (dyadicToRat_den_pos l2 e)
                    (dyadicToRat_mono e hC2) hA2.1)
              have hq2_2l1 :
                  ratLe q2 ⟨Int.mul (Int.ofNat 2) (dyadicToRat l1 e).num,
                    (dyadicToRat l1 e).den⟩ :=
                ratLe_of_ratEq_right
                  (dyadicToRat_den_pos (Int.mul (Int.ofNat 2) l1) e)
                  (dyadicToRat_two_mul l1 e)
                  (ratLe_trans (dyadicToRat_den_pos h2 e)
                    hA2.2 (dyadicToRat_mono e hC3))
              have hq2_2q1 :
                  ratLe q2 ⟨Int.mul (Int.ofNat 2) q1.num, q1.den⟩ :=
                @ratLe_trans q2
                  ⟨Int.mul (Int.ofNat 2) (dyadicToRat l1 e).num,
                    (dyadicToRat l1 e).den⟩
                  ⟨Int.mul (Int.ofNat 2) q1.num, q1.den⟩
                  (dyadicToRat_den_pos l1 e)
                  hq2_2l1 (ratLe_two_mul_mono hA1.1)
              have hq1_2l2 :
                  ratLe q1 ⟨Int.mul (Int.ofNat 2) (dyadicToRat l2 e).num,
                    (dyadicToRat l2 e).den⟩ :=
                ratLe_of_ratEq_right
                  (dyadicToRat_den_pos (Int.mul (Int.ofNat 2) l2) e)
                  (dyadicToRat_two_mul l2 e)
                  (ratLe_trans (dyadicToRat_den_pos h1 e)
                    hA1.2 (dyadicToRat_mono e hC4))
              have hq1_2q2 :
                  ratLe q1 ⟨Int.mul (Int.ofNat 2) q2.num, q2.den⟩ :=
                @ratLe_trans q1
                  ⟨Int.mul (Int.ofNat 2) (dyadicToRat l2 e).num,
                    (dyadicToRat l2 e).den⟩
                  ⟨Int.mul (Int.ofNat 2) q2.num, q2.den⟩
                  (dyadicToRat_den_pos l2 e)
                  hq1_2l2 (ratLe_two_mul_mono hA2.1)
              exact ⟨h0q1, h0q2, hq2_2q1, hq1_2q2⟩
            | false =>
              rw [hPosBr] at hSterb
              dsimp only [Bool.or] at hSterb
              apply Or.inr
              have hN123 := Anneal.InitLemmas.bool_and_left hSterb
              have hC4 := (intLeB_iff_le _ _).mp
                (Anneal.InitLemmas.bool_and_right hSterb)
              have hN12 := Anneal.InitLemmas.bool_and_left hN123
              have hC3 := (intLeB_iff_le _ _).mp
                (Anneal.InitLemmas.bool_and_right hN123)
              have hC1 := (intLeB_iff_le _ _).mp
                (Anneal.InitLemmas.bool_and_left hN12)
              have hC2 := (intLeB_iff_le _ _).mp
                (Anneal.InitLemmas.bool_and_right hN12)
              have hq10 : ratLe q1 ⟨Int.ofNat 0, 1⟩ :=
                ratLe_of_ratEq_right (dyadicToRat_den_pos (Int.ofNat 0) e)
                  (ratEq_symm (dyadicToRat_zero e))
                  (ratLe_trans (dyadicToRat_den_pos h1 e)
                    hA1.2 (dyadicToRat_mono e hC1))
              have hq20 : ratLe q2 ⟨Int.ofNat 0, 1⟩ :=
                ratLe_of_ratEq_right (dyadicToRat_den_pos (Int.ofNat 0) e)
                  (ratEq_symm (dyadicToRat_zero e))
                  (ratLe_trans (dyadicToRat_den_pos h2 e)
                    hA2.2 (dyadicToRat_mono e hC2))
              have h2h1_q2 :
                  ratLe ⟨Int.mul (Int.ofNat 2) (dyadicToRat h1 e).num,
                    (dyadicToRat h1 e).den⟩ q2 :=
                ratLe_of_ratEq_left
                  (dyadicToRat_den_pos (Int.mul (Int.ofNat 2) h1) e)
                  (dyadicToRat_two_mul h1 e)
                  (ratLe_trans (dyadicToRat_den_pos l2 e)
                    (dyadicToRat_mono e hC3) hA2.1)
              have h2q1_q2 :
                  ratLe ⟨Int.mul (Int.ofNat 2) q1.num, q1.den⟩ q2 :=
                @ratLe_trans ⟨Int.mul (Int.ofNat 2) q1.num, q1.den⟩
                  ⟨Int.mul (Int.ofNat 2) (dyadicToRat h1 e).num,
                    (dyadicToRat h1 e).den⟩
                  q2
                  (dyadicToRat_den_pos h1 e)
                  (ratLe_two_mul_mono hA1.2) h2h1_q2
              have h2h2_q1 :
                  ratLe ⟨Int.mul (Int.ofNat 2) (dyadicToRat h2 e).num,
                    (dyadicToRat h2 e).den⟩ q1 :=
                ratLe_of_ratEq_left
                  (dyadicToRat_den_pos (Int.mul (Int.ofNat 2) h2) e)
                  (dyadicToRat_two_mul h2 e)
                  (ratLe_trans (dyadicToRat_den_pos l1 e)
                    (dyadicToRat_mono e hC4) hA1.1)
              have h2q2_q1 :
                  ratLe ⟨Int.mul (Int.ofNat 2) q2.num, q2.den⟩ q1 :=
                @ratLe_trans ⟨Int.mul (Int.ofNat 2) q2.num, q2.den⟩
                  ⟨Int.mul (Int.ofNat 2) (dyadicToRat h2 e).num,
                    (dyadicToRat h2 e).den⟩
                  q1
                  (dyadicToRat_den_pos h2 e)
                  (ratLe_two_mul_mono hA2.2) h2h2_q1
              exact ⟨hq10, hq20, h2q1_q2, h2q2_q1⟩

private theorem aligned_subset_sound {b target : DyadicBox}
    {bl bh tl th e : Int}
    (hAl : alignBoxes b target = some (bl, bh, tl, th, e))
    (hLo : tl ≤ bl) (hHi : bh ≤ th) :
    ∀ q : RatVal, inDyadicBox q b → inDyadicBox q target := by
  intro q hq
  have hPair := alignBoxes_sound hAl
  have hB := hPair.1 q hq
  have hInT : inDyadicBox q ⟨tl, th, e⟩ :=
    ⟨ratLe_trans (dyadicToRat_den_pos bl e) (dyadicToRat_mono e hLo) hB.1,
     ratLe_trans (dyadicToRat_den_pos bh e) hB.2 (dyadicToRat_mono e hHi)⟩
  -- Transfer back from aligned `⟨tl, th, e⟩` to `target`:
  dsimp only [alignBoxes] at hAl
  cases hEq : intEqB b.exp2 target.exp2 with
  | true =>
    rw [hEq] at hAl
    injection hAl with hTup
    have htl := congrArg (fun t => t.2.2.1) hTup
    have hth := congrArg (fun t => t.2.2.2.1) hTup
    have he := congrArg (fun t => t.2.2.2.2) hTup
    subst htl; subst hth; subst he
    have hExpEq : b.exp2 = target.exp2 := (intEqB_iff_eq_dc _ _).mp hEq
    dsimp only [inDyadicBox] at hInT
    dsimp only [inDyadicBox]
    rw [← hExpEq]
    exact hInT
  | false =>
    rw [hEq] at hAl
    dsimp only at hAl
    cases hLt : intLtB b.exp2 target.exp2 with
    | true =>
      rw [hLt] at hAl
      dsimp only at hAl
      cases hCap : Nat.ble (Int.natAbs (Int.sub target.exp2 b.exp2)) 256 with
      | false => rw [hCap] at hAl; nomatch hAl
      | true =>
        rw [hCap] at hAl
        injection hAl with hTup
        have htl := congrArg (fun t => t.2.2.1) hTup
        have hth := congrArg (fun t => t.2.2.2.1) hTup
        have he := congrArg (fun t => t.2.2.2.2) hTup
        subst htl; subst hth; subst he
        have hExp :
            Int.add b.exp2
              (Int.ofNat (Int.natAbs (Int.sub target.exp2 b.exp2))) =
              target.exp2 :=
          add_natAbs_sub_of_le_dc (intLe_of_intLtB_true_dc hLt)
        dsimp only [inDyadicBox] at hInT
        dsimp only [inDyadicBox]
        rw [← hExp]
        exact ⟨ratLe_of_ratEq_left
            (dyadicToRat_den_pos _ b.exp2)
            (ratEq_symm (dyadicToRat_shift target.lo b.exp2 _)) hInT.1,
          ratLe_of_ratEq_right
            (dyadicToRat_den_pos _ b.exp2)
            (ratEq_symm (dyadicToRat_shift target.hi b.exp2 _)) hInT.2⟩
    | false =>
      rw [hLt] at hAl
      dsimp only at hAl
      cases hCap : Nat.ble (Int.natAbs (Int.sub b.exp2 target.exp2)) 256 with
      | false => rw [hCap] at hAl; nomatch hAl
      | true =>
        rw [hCap] at hAl
        injection hAl with hTup
        have htl := congrArg (fun t => t.2.2.1) hTup
        have hth := congrArg (fun t => t.2.2.2.1) hTup
        have he := congrArg (fun t => t.2.2.2.2) hTup
        subst htl; subst hth; subst he
        exact hInT

/-- `checkInFiniteRange` implies semantic inclusion in `maxFiniteBox f`
(`[propext]` only). -/
theorem checkInFiniteRange_sound {q : RatVal} {b : DyadicBox} {f : IeeeFormat}
    (hChk : checkInFiniteRange b f = true) (hq : inDyadicBox q b) :
    inDyadicBox q (maxFiniteBox f) := by
  dsimp only [checkInFiniteRange] at hChk
  cases hAl : alignBoxes b (maxFiniteBox f) with
  | none => rw [hAl] at hChk; nomatch hChk
  | some tup =>
    rw [hAl] at hChk
    cases tup with
    | mk bl rest1 =>
      cases rest1 with
      | mk bh rest2 =>
        cases rest2 with
        | mk ml rest3 =>
          cases rest3 with
          | mk mh e =>
            have h12 := Anneal.InitLemmas.bool_and_left hChk
            have hHi := (intLeB_iff_le _ _).mp
              (Anneal.InitLemmas.bool_and_right hChk)
            have hLo := (intLeB_iff_le _ _).mp
              (Anneal.InitLemmas.bool_and_right h12)
            exact aligned_subset_sound hAl hLo hHi q hq

/-- `checkFiniteEnclosure` implies semantic inclusion in both `target` and
`maxFiniteBox f` (`[propext]` only). -/
theorem checkFiniteEnclosure_sound {q : RatVal} {actual target : DyadicBox}
    {f : IeeeFormat}
    (hChk : checkFiniteEnclosure actual target f = true)
    (hq : inDyadicBox q actual) :
    inDyadicBox q target ∧ inDyadicBox q (maxFiniteBox f) := by
  dsimp only [checkFiniteEnclosure] at hChk
  cases hAl1 : alignBoxes actual target with
  | none => rw [hAl1] at hChk; nomatch hChk
  | some tup1 =>
    rw [hAl1] at hChk
    cases hAl2 : alignBoxes actual (maxFiniteBox f) with
    | none => rw [hAl2] at hChk; nomatch hChk
    | some tup2 =>
      rw [hAl2] at hChk
      cases tup1 with
      | mk al r1 =>
        cases r1 with
        | mk ah r2 =>
          cases r2 with
          | mk tl r3 =>
            cases r3 with
            | mk th e1 =>
              cases tup2 with
              | mk al2 s1 =>
                cases s1 with
                | mk ah2 s2 =>
                  cases s2 with
                  | mk ml s3 =>
                    cases s3 with
                    | mk mh e2 =>
                      have h1234 := Anneal.InitLemmas.bool_and_left hChk
                      have hMHi := (intLeB_iff_le _ _).mp
                        (Anneal.InitLemmas.bool_and_right hChk)
                      have h123 := Anneal.InitLemmas.bool_and_left h1234
                      have hMLo := (intLeB_iff_le _ _).mp
                        (Anneal.InitLemmas.bool_and_right h1234)
                      have h12 := Anneal.InitLemmas.bool_and_left h123
                      have hTHi := (intLeB_iff_le _ _).mp
                        (Anneal.InitLemmas.bool_and_right h123)
                      have hTLo := (intLeB_iff_le _ _).mp
                        (Anneal.InitLemmas.bool_and_right h12)
                      exact ⟨aligned_subset_sound hAl1 hTLo hTHi q hq,
                        aligned_subset_sound hAl2 hMLo hMHi q hq⟩

private theorem powScale_ratEq_dyadic (neg : Bool) (sig : Nat) (e : Int) :
    let nd := powScale sig 1 e
    0 < nd.2 ∧ ratEq ⟨signedNum neg nd.1, nd.2⟩
      (dyadicToRat (signedNum neg sig) e) := by
  cases e with
  | ofNat k =>
    dsimp only [powScale, dyadicToRat, ratEq, signedNum]
    refine ⟨Nat.zero_lt_succ 0, ?_⟩
    cases neg with
    | false => rfl
    | true =>
      change Int.mul (Int.neg (Int.ofNat (sig * pow2 k))) (Int.ofNat 1) =
        Int.mul (Int.mul (Int.neg (Int.ofNat sig)) (Int.ofNat (pow2 k)))
          (Int.ofNat 1)
      rw [int_mul_one_dc, int_mul_one_dc, int_neg_mul_left_dc]
      rfl
  | negSucc k =>
    dsimp only [powScale, dyadicToRat, ratEq]
    rw [Nat.one_mul]
    exact ⟨pow2_pos (k + 1), rfl⟩

/-- `floatBitsToBox` decodes every finite IEEE-754 bit pattern into a tight
point `DyadicBox` enclosing its exact `decodeFiniteRat` rational (`[propext]`
only). -/
theorem floatBitsToBox_sound (f : IeeeFormat) (bits : Nat) {b : DyadicBox}
    (hBox : floatBitsToBox f bits = some b) :
    ∃ q : RatVal, decodeFiniteRat f bits = some q ∧ 0 < q.den ∧
      inDyadicBox q b := by
  dsimp only [floatBitsToBox] at hBox
  dsimp only [decodeFiniteRat]
  have hModIdem :
      Nat.mod (Nat.mod bits (pow2 f.width)) (pow2 f.width) =
        Nat.mod bits (pow2 f.width) :=
    Nat.mod_eq_of_lt (Nat.mod_lt bits (pow2_pos f.width))
  dsimp only [decodeBits]
  cases hAll :
      Nat.beq (unpackBits f (Nat.mod bits (pow2 f.width))).exponent
        f.allOnesExp with
  | true => rw [hAll] at hBox; nomatch hBox
  | false =>
    rw [hAll] at hBox
    dsimp only at hBox
    dsimp only
    cases hE0 :
        Nat.beq (unpackBits f (Nat.mod bits (pow2 f.width))).exponent 0 with
    | true =>
      rw [hE0] at hBox
      dsimp only at hBox
      dsimp only
      cases hF0 :
          Nat.beq (unpackBits f (Nat.mod bits (pow2 f.width))).fraction 0 with
      | true =>
        rw [hF0] at hBox
        dsimp only
        injection hBox with hB
        subst hB
        exact ⟨⟨Int.ofNat 0, 1⟩, rfl, Nat.zero_lt_succ 0,
          ⟨ratLe_refl _, ratLe_refl _⟩⟩
      | false =>
        rw [hF0] at hBox
        dsimp only
        injection hBox with hB
        subst hB
        let c := unpackBits f (Nat.mod bits (pow2 f.width))
        let e := Int.sub f.minExponent (Int.ofNat f.fractionBits)
        have hPS := powScale_ratEq_dyadic c.neg c.fraction e
        refine ⟨_, rfl, hPS.1, ?_⟩
        exact ⟨ratLe_of_ratEq_right
            (dyadicToRat_den_pos (signedNum c.neg c.fraction) e)
            (ratEq_symm hPS.2)
            (ratLe_refl (dyadicToRat (signedNum c.neg c.fraction) e)),
          ratLe_of_ratEq_left
            (dyadicToRat_den_pos (signedNum c.neg c.fraction) e)
            (ratEq_symm hPS.2)
            (ratLe_refl (dyadicToRat (signedNum c.neg c.fraction) e))⟩
    | false =>
      rw [hE0] at hBox
      dsimp only
      injection hBox with hB
      subst hB
      let c := unpackBits f (Nat.mod bits (pow2 f.width))
      let sig := pow2 f.fractionBits + c.fraction
      let e := Int.sub (Int.sub (Int.ofNat c.exponent) (Int.ofNat f.bias))
        (Int.ofNat f.fractionBits)
      have hPS := powScale_ratEq_dyadic c.neg sig e
      refine ⟨_, rfl, hPS.1, ?_⟩
      exact ⟨ratLe_of_ratEq_right
          (dyadicToRat_den_pos (signedNum c.neg sig) e)
          (ratEq_symm hPS.2)
          (ratLe_refl (dyadicToRat (signedNum c.neg sig) e)),
        ratLe_of_ratEq_left
          (dyadicToRat_den_pos (signedNum c.neg sig) e)
          (ratEq_symm hPS.2)
          (ratLe_refl (dyadicToRat (signedNum c.neg sig) e))⟩

private theorem minValue_nonpos_dc (pw : FloatPtrWidth) (t : FloatIntTarget) :
    t.minValue pw ≤ Int.ofNat 0 := by
  dsimp only [FloatIntTarget.minValue]
  cases t.signed with
  | false => exact int_le_refl_dc _
  | true =>
    apply (intBalance_le
      (intBalance_neg (intBalance_ofNat (pow2 (t.bitWidth pw - 1))))
      (intBalance_ofNat 0)).mpr
    exact Nat.zero_le _

private theorem maxValue_nonneg_dc (pw : FloatPtrWidth) (t : FloatIntTarget) :
    Int.ofNat 0 ≤ t.maxValue pw := by
  dsimp only [FloatIntTarget.maxValue]
  cases t.signed with
  | true =>
    have hGe1 : 1 ≤ pow2 (t.bitWidth pw - 1) := pow2_pos _
    apply (intBalance_le (intBalance_ofNat 0)
      (intBalance_sub (intBalance_ofNat (pow2 (t.bitWidth pw - 1)))
        (intBalance_ofNat 1))).mpr
    rw [Nat.zero_add, Nat.add_zero, Nat.add_zero]
    exact hGe1
  | false =>
    have hGe1 : 1 ≤ pow2 (t.bitWidth pw) := pow2_pos _
    apply (intBalance_le (intBalance_ofNat 0)
      (intBalance_sub (intBalance_ofNat (pow2 (t.bitWidth pw)))
        (intBalance_ofNat 1))).mpr
    rw [Nat.zero_add, Nat.add_zero, Nat.add_zero]
    exact hGe1

/-- `checkFloatToIntSafe` soundness (`[propext]` only): if
`checkFloatToIntSafe b pw target = true` and a finite `src` bit pattern decodes
to `q ∈ b`, then `evalFloatToIntChecked src bits target pw` returns `some v`
(`float_to_int_unchecked` is UB-free and agrees with
`evalFloatToIntSaturating` by `evalFloatToIntChecked_some_agrees_saturating`).
-/
theorem checkFloatToIntSafe_sound (src : IeeeFormat) (bits : Nat)
    {b : DyadicBox} (pw : FloatPtrWidth) (target : FloatIntTarget) {q : RatVal}
    (hSafe : checkFloatToIntSafe b pw target = true)
    (hDecQ : decodeFiniteRat src bits = some q)
    (hqDen : 0 < q.den)
    (hqIn : inDyadicBox q b) :
    ∃ v : Int, evalFloatToIntChecked src bits target pw = some v := by
  dsimp only [checkFloatToIntSafe] at hSafe
  let intRangeBox : DyadicBox :=
    { lo := target.minValue pw
      hi := target.maxValue pw
      exp2 := Int.ofNat 0 }
  have hInInt : inDyadicBox q intRangeBox := by
    cases hAl : alignBoxes b intRangeBox with
    | none => rw [hAl] at hSafe; nomatch hSafe
    | some tup =>
      rw [hAl] at hSafe
      cases tup with
      | mk bl r1 =>
        cases r1 with
        | mk bh r2 =>
          cases r2 with
          | mk il r3 =>
            cases r3 with
            | mk ih e =>
              have h12 := Anneal.InitLemmas.bool_and_left hSafe
              have hHi := (intLeB_iff_le _ _).mp
                (Anneal.InitLemmas.bool_and_right hSafe)
              have hLo := (intLeB_iff_le _ _).mp
                (Anneal.InitLemmas.bool_and_right h12)
              exact aligned_subset_sound hAl hLo hHi q hqIn
  dsimp only [decodeFiniteRat] at hDecQ
  dsimp only [evalFloatToIntChecked]
  cases hDec : decodeBits src (Nat.mod bits (pow2 src.width)) with
  | nan _ _ _ => rw [hDec] at hDecQ; nomatch hDecQ
  | inf _ => rw [hDec] at hDecQ; nomatch hDecQ
  | zero _ => exact ⟨Int.ofNat 0, rfl⟩
  | finite neg n d =>
    rw [hDec] at hDecQ
    injection hDecQ with hQEq
    subst hQEq
    dsimp only at hqDen
    dsimp only [inDyadicBox, intRangeBox, dyadicToRat, ratLe] at hInInt
    have hPow0 : pow2 0 = 1 := rfl
    rw [hPow0, int_mul_one_dc, int_mul_one_dc, int_mul_one_dc] at hInInt
    dsimp only
    have hLoTr : target.minValue pw ≤ truncRatio neg n d := by
      dsimp only [truncRatio]
      cases neg with
      | false =>
        exact int_le_trans_dc (minValue_nonpos_dc pw target)
          ((intBalance_le (intBalance_ofNat 0)
            (intBalance_ofNat (Nat.div n d))).mpr (Nat.zero_le _))
      | true =>
        dsimp only [signedNum] at hInInt
        have hDivMul :
            Int.mul (Int.neg (Int.ofNat (Nat.div n d))) (Int.ofNat d) =
              Int.neg (Int.ofNat (Nat.div n d * d)) := by
          rw [int_neg_mul_left_dc]
          rfl
        have hNegGe :
            Int.neg (Int.ofNat n) ≤
              Int.neg (Int.ofNat (Nat.div n d * d)) :=
          int_neg_le_neg_dc
            ((intBalance_le (intBalance_ofNat (Nat.div n d * d))
              (intBalance_ofNat n)).mpr
              (by rw [Nat.add_zero, Nat.add_zero]; exact Nat.div_mul_le_self n d))
        have hMulLe :
            Int.mul (target.minValue pw) (Int.ofNat d) ≤
              Int.mul (Int.neg (Int.ofNat (Nat.div n d))) (Int.ofNat d) := by
          rw [hDivMul]
          exact int_le_trans_dc hInInt.1 hNegGe
        exact int_le_of_mul_ofNat_right_dc hqDen hMulLe
    have hTrHi : truncRatio neg n d ≤ target.maxValue pw := by
      dsimp only [truncRatio]
      cases neg with
      | true =>
        exact int_le_trans_dc
          ((intBalance_le
            (intBalance_neg (intBalance_ofNat (Nat.div n d)))
            (intBalance_ofNat 0)).mpr (Nat.zero_le _))
          (maxValue_nonneg_dc pw target)
      | false =>
        dsimp only [signedNum] at hInInt
        have hDivLeN :
            Int.mul (Int.ofNat (Nat.div n d)) (Int.ofNat d) ≤ Int.ofNat n := by
          change Int.ofNat (Nat.div n d * d) ≤ Int.ofNat n
          exact (intBalance_le (intBalance_ofNat (Nat.div n d * d))
            (intBalance_ofNat n)).mpr
            (by rw [Nat.add_zero, Nat.add_zero]; exact Nat.div_mul_le_self n d)
        exact int_le_of_mul_ofNat_right_dc hqDen
          (int_le_trans_dc hDivLeN hInInt.2)
    have hLBool : intLeB (target.minValue pw) (truncRatio neg n d) = true :=
      (intLeB_iff_le _ _).mpr hLoTr
    have hRBool : intLeB (truncRatio neg n d) (target.maxValue pw) = true :=
      (intLeB_iff_le _ _).mpr hTrHi
    rw [hLBool, hRBool]
    exact ⟨truncRatio neg n d, rfl⟩

end Anneal.Float

end
