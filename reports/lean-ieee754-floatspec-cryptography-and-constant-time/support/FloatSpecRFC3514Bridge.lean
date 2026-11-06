-- Copyright 2026 The Fuchsia Authors
--
-- Licensed under a BSD-style license <LICENSE-BSD>, Apache License, Version 2.0
-- <LICENSE-APACHE or https://www.apache.org/licenses/LICENSE-2.0>, or the MIT
-- license <LICENSE-MIT or https://opensource.org/licenses/MIT>, at your option.
-- This file may not be copied, modified, or distributed except according to
-- those terms.

/-!
# `FloatSpec` Core IEEE-754 Port and Rust RFC 3514 Bridge (`v4.34.1`)

This standalone Lean `v4.34.1` module demonstrates that the computational and
structural IEEE-754 core of `Beneficial-AI-Foundation/FloatSpec` (commit
`158263e983ec3925e02b10f5b312498bf414e0f1`) has zero intrinsic dependency on
`Mathlib` (`ℝ` or `Mathlib.Tactic`) and compiles cleanly on core Lean `v4.34.1`
with zero unproved obligations and zero custom axioms.

Specifically, this module:
1. Ports `FloatSpec`'s integer, radix, binary-digit, and `FLT_exp` primitives
   from `FloatSpec/src/Core/Zaux.lean`, `FloatSpec/src/Core/Digits.lean`, and
   `FloatSpec/src/Core/FLT.lean` using only core Lean `Nat`, `Int`, and `Bool`.
2. Ports `FloatSpec`'s full-float (`FullFloat`, `full_float`), standard-float
   (`StandardFloat`), proof-carrying binary float (`binary_float prec emax`),
   permissive compatibility carrier (`Binary754 prec emax`), and single-NaN
   bridge (`BinarySingleNaNBridge.BinaryFloat`, `B2BSN`, `BSN2B`) from
   `FloatSpec/src/IEEE754/Binary.lean`.
3. Ports `FloatSpec`'s IEEE-754 bit-level packing/unpacking (`join_bits`,
   `split_bits`, `binary_to_bits`, `bits_to_binary`) from
   `FloatSpec/src/IEEE754/Bits.lean`.
4. Fixes `FloatSpec`'s `Babs` bug (`Binary.lean:364-369`, which left the sign
   bit of `.F754_nan s pl` unchanged instead of clearing it to `false`) and
   implements RFC 3514-compliant `Babs`, `Bneg` (`Bopp`), and `Bcopysign` that
   act bitwise on the sign bit across all four constructors without quieting or
   canonicalizing NaN payloads. Removing the bug eliminates the
   `(hx : is_nan_FF x = false)` precondition that `FloatSpec` had to attach to
   `Bsign_Babs_compat`, `Babs_idempotent_compat`, and `Babs_Bopp_compat`.
5. Bridges `FloatSpec`'s parameterized `BSN2B` NaN-handler architecture to
   Round 1's `FloatProbe.lean` RFC 3514 nondeterministic NaN envelope, proving
   that universal quantification over `FloatSpec` quiet-NaN handlers is
   extensionally equivalent to RFC 3514's demonic NaN choice and that any
   payload-oblivious theorem proved for a single default NaN handler transfers
   automatically to all RFC 3514 execution branches.
-/

namespace Anneal.FloatSpecBridge

-- ============================================================================
-- Section 1: Core Integer, Digit, and Format Primitives (`Zaux`, `Digits`)
-- ============================================================================

/-- Precision is strictly positive (`FloatSpec/src/Core/Defs.lean:32`). -/
class Prec_gt_0 (prec : Int) : Prop where
  pos : 0 < prec

/-- Precision is strictly less than the maximum exponent, and `emax ≥ 2`
(`FloatSpec/src/IEEE754/Binary.lean:34`). -/
class Prec_lt_emax (prec emax : Int) : Prop where
  prec_lt_emax : prec < emax
  emax_ge_2 : 2 ≤ emax

namespace Core.Zaux

/-- Coq-style binary positive integers (`FloatSpec/src/Core/Zaux.lean:29`). -/
inductive Positive where
  | xH : Positive
  | xO : Positive → Positive
  | xI : Positive → Positive
  deriving DecidableEq, Repr

/-- Conversion from `Positive` to `Nat` (`FloatSpec/src/Core/Zaux.lean:36`). -/
def positiveToNat : Positive → Nat
  | .xH => 1
  | .xO p => 2 * positiveToNat p
  | .xI p => 2 * positiveToNat p + 1

theorem positiveToNat_pos (p : Positive) : 0 < positiveToNat p := by
  induction p with
  | xH => decide
  | xO p ih =>
      simp only [positiveToNat]
      omega
  | xI p ih =>
      simp only [positiveToNat]
      omega

theorem positiveToNat_injective :
    ∀ {a b : Positive}, positiveToNat a = positiveToNat b → a = b
  | .xH, .xH, _ => rfl
  | .xH, .xO b, h => by
      have hb := positiveToNat_pos b
      simp [positiveToNat] at h
      omega
  | .xH, .xI b, h => by
      have hb := positiveToNat_pos b
      simp [positiveToNat] at h
      omega
  | .xO a, .xH, h => by
      have ha := positiveToNat_pos a
      simp [positiveToNat] at h
      omega
  | .xO a, .xO b, h => by
      simp [positiveToNat] at h
      exact congrArg Positive.xO (positiveToNat_injective (by omega))
  | .xO a, .xI b, h => by
      simp [positiveToNat] at h
      omega
  | .xI a, .xH, h => by
      have ha := positiveToNat_pos a
      simp [positiveToNat] at h
      omega
  | .xI a, .xO b, h => by
      simp [positiveToNat] at h
      omega
  | .xI a, .xI b, h => by
      simp [positiveToNat] at h
      exact congrArg Positive.xI (positiveToNat_injective (by omega))

/-- Boolean less-than comparison on integers
(`FloatSpec/src/Core/Zaux.lean`). -/
def Zlt_bool (x y : Int) : Bool :=
  decide (x < y)

/-- Conditional negation controlled by a sign bit
(`FloatSpec/src/Core/Zaux.lean:1774`). -/
def cond_Zopp (b : Bool) (x : Int) : Int :=
  if b then -x else x

end Core.Zaux

namespace Core.Digits

/-- Bit-length recursion on `Nat` (`FloatSpec/src/Core/Digits.lean:52`). -/
def digits2_Pnat_bitlength_payload : Nat → Nat
  | 0 => 0
  | n + 1 => 1 + digits2_Pnat_bitlength_payload ((n + 1) / 2)

/-- Zero-based index of the most significant bit of a positive natural number
(`FloatSpec/src/Core/Digits.lean:60`). -/
def digits2_Pnat (n : Nat) : Nat :=
  digits2_Pnat_bitlength_payload n - 1

theorem bitlength_pos {n : Nat} (hn : 0 < n) :
    0 < digits2_Pnat_bitlength_payload n := by
  cases n with
  | zero => omega
  | succ k =>
      rw [digits2_Pnat_bitlength_payload]
      omega

/-- Exact power-of-two bounds for `digits2_Pnat` (`Digits.lean:216`), proved
using only core Lean `Nat` and `omega` without `Mathlib`. -/
theorem digits2_Pnat_correct (n : Nat) (hn : 0 < n) :
    let d := digits2_Pnat n
    2 ^ d ≤ n ∧ n < 2 ^ (d + 1) := by
  induction n using Nat.strongRecOn with
  | ind m ih =>
      cases m with
      | zero => omega
      | succ k =>
          cases k with
          | zero =>
              simp [digits2_Pnat, digits2_Pnat_bitlength_payload]
          | succ k0 =>
              let m2 := (k0 + 2) / 2
              have hm2_pos : 0 < m2 := by omega
              have hm2_lt : m2 < k0 + 2 := by omega
              have ⟨hlo, hhi⟩ := ih m2 hm2_lt hm2_pos
              have hd_succ :
                  digits2_Pnat (k0 + 2) = digits2_Pnat m2 + 1 := by
                have hbl :
                    digits2_Pnat_bitlength_payload (k0 + 2) =
                      1 + digits2_Pnat_bitlength_payload m2 := by
                  rw [digits2_Pnat_bitlength_payload]
                have hpos2 : 0 < digits2_Pnat_bitlength_payload m2 :=
                  bitlength_pos hm2_pos
                dsimp [digits2_Pnat]
                omega
              dsimp only
              rw [hd_succ]
              have hpow1 :
                  2 ^ (digits2_Pnat m2 + 1) = 2 ^ digits2_Pnat m2 * 2 :=
                Nat.pow_succ 2 (digits2_Pnat m2)
              have hpow2 :
                  2 ^ (digits2_Pnat m2 + 1 + 1) =
                    2 ^ (digits2_Pnat m2 + 1) * 2 :=
                Nat.pow_succ 2 (digits2_Pnat m2 + 1)
              omega

/-- Binary digit count for positive naturals
(`FloatSpec/src/Core/Digits.lean:6298`). -/
def digits2_pos (m : Nat) : Int :=
  (digits2_Pnat m + 1 : Nat)

/-- Binary digit count for integers (`FloatSpec/src/Core/Digits.lean:6318`). -/
def Zdigits2 (n : Int) : Int :=
  if n = 0 then 0 else (digits2_Pnat n.natAbs + 1 : Nat)

/-- Fuel-bounded generic radix digit counter
(`FloatSpec/src/Core/Digits.lean:4186`). -/
def Zdigits_aux (beta p d pow : Int) : Nat → Int
  | 0 => d
  | fuel + 1 =>
      if p < pow then d
      else Zdigits_aux beta p (d + 1) (beta * pow) fuel

/-- Number of base-`beta` digits of an integer
(`FloatSpec/src/Core/Digits.lean:4192`). -/
def Zdigits (beta n : Int) : Int :=
  if n = 0 then 0
  else
    let fuel := n.natAbs.succ
    Zdigits_aux beta (n.natAbs : Int) 1 beta fuel

end Core.Digits

namespace Core.FLT

/-- IEEE-754 floating-point exponent function with underflow floor `emin`
(`FloatSpec/src/Core/FLT.lean:46`). -/
def FLT_exp (prec emin e : Int) : Int :=
  max (e - prec) emin

end Core.FLT

-- ============================================================================
-- Section 2: `FloatSpec` Binary IEEE-754 Carriers (`IEEE754/Binary.lean`)
-- ============================================================================

/-- `FloatSpec`'s `Nat`-mantissa full-float carrier (`Binary.lean:53`).
Every NaN carries its own sign bit `s` and payload `m`. -/
inductive FullFloat where
  | F754_zero (s : Bool) : FullFloat
  | F754_infinity (s : Bool) : FullFloat
  | F754_nan (s : Bool) (m : Nat) : FullFloat
  | F754_finite (s : Bool) (m : Nat) (e : Int) : FullFloat
  deriving DecidableEq, Repr

/-- Coq-faithful `full_float` carrier whose finite mantissa and NaN payload are
strictly positive (`Binary.lean:60`). -/
inductive full_float where
  | F754_zero (s : Bool) : full_float
  | F754_infinity (s : Bool) : full_float
  | F754_nan (s : Bool) (m : Core.Zaux.Positive) : full_float
  | F754_finite (s : Bool) (m : Core.Zaux.Positive) (e : Int) : full_float
  deriving DecidableEq, Repr

/-- Standard single-NaN float view (`Binary.lean:69`). -/
inductive StandardFloat where
  | S754_zero (s : Bool) : StandardFloat
  | S754_infinity (s : Bool) : StandardFloat
  | S754_nan : StandardFloat
  | S754_finite (s : Bool) (m : Nat) (e : Int) : StandardFloat
  deriving DecidableEq, Repr

/-- Erase NaN sign and payload to `StandardFloat` (`Binary.lean:77`). -/
def FF2SF (x : FullFloat) : StandardFloat :=
  match x with
  | .F754_zero s => .S754_zero s
  | .F754_infinity s => .S754_infinity s
  | .F754_nan _ _ => .S754_nan
  | .F754_finite s m e => .S754_finite s m e

/-- Lift `StandardFloat` to `FullFloat` using a fixed dummy NaN
(`Binary.lean:87`). -/
def SF2FF (x : StandardFloat) : FullFloat :=
  match x with
  | .S754_zero s => .F754_zero s
  | .S754_infinity s => .F754_infinity s
  | .S754_nan => .F754_nan false 1
  | .S754_finite s m e => .F754_finite s m e

theorem FF2SF_SF2FF (x : StandardFloat) : FF2SF (SF2FF x) = x := by
  cases x <;> rfl

/-- NaN classifier on `FullFloat` (`Binary.lean:105`). -/
def is_nan_FF (x : FullFloat) : Bool :=
  match x with
  | .F754_nan _ _ => true
  | _ => false

/-- Finite classifier on `FullFloat` (`Binary.lean:119`). -/
def is_finite_FF (x : FullFloat) : Bool :=
  match x with
  | .F754_finite _ _ _ => true
  | .F754_zero _ => true
  | _ => false

/-- Sign-bit extractor on `FullFloat` (`Binary.lean:134`). -/
def sign_FF (x : FullFloat) : Bool :=
  match x with
  | .F754_zero s => s
  | .F754_infinity s => s
  | .F754_nan s _ => s
  | .F754_finite s _ _ => s

/-- NaN payload extractor on `FullFloat` (`Binary.lean:294`). -/
def get_nan_pl (x : FullFloat) : Nat :=
  match x with
  | .F754_nan _ pl => pl
  | _ => 1

/-- Coq `nan_pl` validity check: a positive NaN payload fits in `prec - 1` bits,
meaning `digits2_pos pl < prec` (`Binary.lean:472`). -/
def nan_pl (prec : Int) (pl : Core.Zaux.Positive) : Bool :=
  Core.Zaux.Zlt_bool
    (Core.Digits.digits2_pos (Core.Zaux.positiveToNat pl))
    prec

/-- `Nat`-carrier variant of `nan_pl`: `0 < pl` and `digits2_pos pl < prec`. -/
def nan_pl_nat (prec : Int) (pl : Nat) : Bool :=
  decide (0 < pl) && Core.Zaux.Zlt_bool (Core.Digits.digits2_pos pl) prec

/-- Local `FLT_exp` wrapper matching `Binary.lean:477`. -/
def FLT_exp (emin prec e : Int) : Int :=
  Core.FLT.FLT_exp prec emin e

/-- Canonical mantissa check (`Binary.lean:486`). -/
def canonical_mantissa {prec emax : Int} (m : Nat) (e : Int) : Bool :=
  decide
    (e = FLT_exp (3 - emax - prec) prec (Core.Digits.Zdigits2 (m : Int) + e))

/-- Range-bounded predicate on `(m, e)` (`Binary.lean:492`). -/
def bounded {prec emax : Int} (m : Nat) (e : Int) : Bool :=
  decide (m < (2 : Nat) ^ prec.toNat) &&
    decide (3 - emax - prec ≤ e) &&
    decide (e ≤ emax - prec)

/-- Coq `SpecFloat.bounded`: canonical mantissa and upper exponent bound
(`Binary.lean:501`). -/
def specFloat_bounded {prec emax : Int} (m : Nat) (e : Int) : Bool :=
  canonical_mantissa (prec := prec) (emax := emax) m e &&
    decide (e ≤ emax - prec)

/-- Coq `Binary.v:binary_float`: proof-carrying IEEE-754 binary float with
explicit NaN sign and bounded positive payload (`Binary.lean:528`). -/
inductive binary_float (prec emax : Int) where
  | B754_zero (s : Bool) : binary_float prec emax
  | B754_infinity (s : Bool) : binary_float prec emax
  | B754_nan (s : Bool) (pl : Core.Zaux.Positive) :
      nan_pl prec pl = true → binary_float prec emax
  | B754_finite (s : Bool) (m : Core.Zaux.Positive) (e : Int) :
      specFloat_bounded (prec := prec) (emax := emax)
        (Core.Zaux.positiveToNat m) e = true →
      binary_float prec emax
  deriving DecidableEq

/-- Full-float validity predicate for `full_float` (`Binary.lean:551`). -/
def valid_full_float_binary {prec emax : Int} (x : full_float) : Bool :=
  match x with
  | .F754_finite _ m e =>
      specFloat_bounded (prec := prec) (emax := emax)
        (Core.Zaux.positiveToNat m) e
  | .F754_nan _ payload =>
      nan_pl prec payload
  | .F754_zero _ => true
  | .F754_infinity _ => true

/-- Coq `FF2B` on the proof-carrying `binary_float` carrier
(`Binary.lean:562`). -/
def fullFloatToBinaryFloat {prec emax : Int} (x : full_float)
    (hx : valid_full_float_binary (prec := prec) (emax := emax) x = true) :
    binary_float prec emax :=
  match x with
  | .F754_finite s m e =>
      .B754_finite s m e (by simpa [valid_full_float_binary] using hx)
  | .F754_infinity s => .B754_infinity s
  | .F754_zero s => .B754_zero s
  | .F754_nan s payload =>
      .B754_nan s payload (by simpa [valid_full_float_binary] using hx)

/-- Coq `B2FF` on the proof-carrying `binary_float` carrier
(`Binary.lean:578`). -/
def binaryFloatToFullFloat {prec emax : Int}
    (x : binary_float prec emax) : full_float :=
  match x with
  | .B754_finite s m e _ => .F754_finite s m e
  | .B754_infinity s => .F754_infinity s
  | .B754_zero s => .F754_zero s
  | .B754_nan s payload _ => .F754_nan s payload

theorem binaryFloatToFullFloat_fullFloatToBinaryFloat {prec emax : Int}
    (x : full_float)
    (hx : valid_full_float_binary (prec := prec) (emax := emax) x = true) :
    binaryFloatToFullFloat (prec := prec) (emax := emax)
      (fullFloatToBinaryFloat (prec := prec) (emax := emax) x hx) = x := by
  cases x <;> rfl

theorem valid_full_float_binary_binaryFloatToFullFloat {prec emax : Int}
    (x : binary_float prec emax) :
    valid_full_float_binary (prec := prec) (emax := emax)
      (binaryFloatToFullFloat (prec := prec) (emax := emax) x) = true := by
  cases x with
  | B754_zero _ => rfl
  | B754_infinity _ => rfl
  | B754_nan _ _ hPayload =>
      simpa [binaryFloatToFullFloat, valid_full_float_binary] using hPayload
  | B754_finite _ _ _ hBounded =>
      simpa [binaryFloatToFullFloat, valid_full_float_binary] using hBounded

theorem fullFloatToBinaryFloat_binaryFloatToFullFloat {prec emax : Int}
    (x : binary_float prec emax) :
    fullFloatToBinaryFloat (prec := prec) (emax := emax)
      (binaryFloatToFullFloat (prec := prec) (emax := emax) x)
      (valid_full_float_binary_binaryFloatToFullFloat x) = x := by
  cases x <;> rfl

/-- `FloatSpec`'s wrapper carrier `Binary754 prec emax` (`Binary.lean:511`). -/
structure Binary754 (prec emax : Int) where
  val : FullFloat
  deriving DecidableEq, Repr

/-- Construct `Binary754` from `FullFloat` (`Binary.lean:539`). -/
def FF2B {prec emax : Int} (x : FullFloat) : Binary754 prec emax :=
  ⟨x⟩

/-- Project `Binary754` to `FullFloat` (`Binary.lean:542`). -/
def B2FF {prec emax : Int} (x : Binary754 prec emax) : FullFloat :=
  x.val

@[simp]
theorem B2FF_FF2B {prec emax : Int} (x : FullFloat) :
    B2FF (FF2B (prec := prec) (emax := emax) x) = x := rfl

@[simp]
theorem FF2B_B2FF {prec emax : Int} (x : Binary754 prec emax) :
    FF2B (prec := prec) (emax := emax) (B2FF x) = x := by
  cases x
  rfl

-- ============================================================================
-- Section 3: IEEE-754 Bit-Level Encoding (`FloatSpec/src/IEEE754/Bits.lean`)
-- ============================================================================

/-- Pack sign `s`, mantissa field `m`, and biased exponent field `e` into an
IEEE-754 integer bit pattern (`Bits.lean:19`). -/
def join_bits (mw ew : Nat) (s : Bool) (m e : Int) : Int :=
  let sign_bit : Int := if s then (2 : Int) ^ ew else 0
  (sign_bit + e) * ((2 : Int) ^ mw) + m

/-- Unpack an IEEE-754 integer bit pattern into `(s, m, e)`
(`Bits.lean:107`). -/
def split_bits (mw ew : Nat) (x : Int) : Bool × Int × Int :=
  let mm : Int := (2 : Int) ^ mw
  let em : Int := (2 : Int) ^ ew
  (decide (mm * em ≤ x), x % mm, (x / mm) % em)

/-- Mantissa bit width `prec - 1` (`Bits.lean:290`). -/
def mant_width (prec : Int) : Nat :=
  Int.toNat (prec - 1)

/-- Exponent bit width `Zdigits 2 (emax + 1)` (`Bits.lean:293`). -/
def exp_width (emax : Int) : Nat :=
  Int.toNat (Core.Digits.Zdigits2 (emax + 1))

/-- Encode `Binary754 prec emax` into its IEEE-754 bit pattern
(`Bits.lean:300`). -/
def binary_to_bits (prec emax : Int) (x : Binary754 prec emax) : Int :=
  let mw := mant_width prec
  let ew := exp_width emax
  let mm : Int := (2 : Int) ^ mw
  let em : Int := (2 : Int) ^ ew
  let expMax : Int := em - 1
  let subExp : Int := (1 - emax) - (mw : Int)
  match x.val with
  | .F754_zero s =>
      join_bits mw ew s 0 0
  | .F754_infinity s =>
      join_bits mw ew s 0 expMax
  | .F754_nan s payload =>
      let payload : Int := (payload : Int) % mm
      let payload : Int :=
        if payload = 0 then (if 1 < mm then 1 else 0) else payload
      join_bits mw ew s payload expMax
  | .F754_finite s m e =>
      let m : Int := (m : Int)
      if m = 0 then
        join_bits mw ew s 0 0
      else if e = subExp ∧ m < mm then
        join_bits mw ew s m 0
      else
        let E : Int := e + (mw : Int) + emax
        if 1 ≤ E ∧ E < expMax ∧ mm ≤ m ∧ m < 2 * mm then
          join_bits mw ew s (m - mm) E
        else
          let nanPayload : Int := if 1 < mm then 1 else 0
          join_bits mw ew s nanPayload expMax

/-- Decode an IEEE-754 bit pattern into `Binary754 prec emax`
(`Bits.lean:334`). -/
def bits_to_binary (prec emax : Int) (bits : Int) : Binary754 prec emax :=
  let mw := mant_width prec
  let ew := exp_width emax
  let modulus : Int := (2 : Int) ^ (mw + ew + 1)
  let bits : Int := bits % modulus
  let mm : Int := (2 : Int) ^ mw
  let em : Int := (2 : Int) ^ ew
  let expMax : Int := em - 1
  let (s, mField, eField) := split_bits mw ew bits
  if eField = expMax then
    if mField = 0 then
      FF2B (.F754_infinity s)
    else
      FF2B (.F754_nan s (Int.toNat mField))
  else if eField = 0 then
    if mField = 0 then
      FF2B (.F754_zero s)
    else
      FF2B (.F754_finite s (Int.toNat mField) ((1 - emax) - (mw : Int)))
  else
    FF2B
      (.F754_finite s (Int.toNat (mm + mField)) ((eField - emax) - (mw : Int)))

-- ============================================================================
-- Section 4: Fixing `Babs` and Implementing `Bneg` and `Bcopysign` for RFC 3514
-- ============================================================================

/-!
## Diagnosis of `FloatSpec`'s `Babs` Bug (`Binary.lean:364-369`)

In `FloatSpec/src/IEEE754/Binary.lean:364-369`, `Babs` is defined as:
```lean
def Babs (x : FullFloat) : FullFloat :=
  match x with
  | FullFloat.F754_zero _ => FullFloat.F754_zero false
  | FullFloat.F754_infinity _ => FullFloat.F754_infinity false
  | FullFloat.F754_nan s pl => FullFloat.F754_nan s pl
  | FullFloat.F754_finite _ m e => FullFloat.F754_finite false m e
```
Because the `.F754_nan s pl` arm preserves `s` instead of setting the sign bit
to `false`:
1. `Babs` violates both IEEE 754-2008 §5.5.1 ("`abs(x)` copies a floating-point
   operand `x` to a destination in the same format, setting the sign bit to 0
   (positive) ... even if the operand is a NaN") and Rust RFC 3514 ("`abs`,
   negation (`-`), and `copysign` ... are guaranteed to solely access and
   modify the sign bit and leave the quiet/signaling bit and payload bits
   alone").
2. In `FloatSpec`, `Bsign_Babs_compat` (`Binary.lean:405`),
   `Babs_idempotent_compat` (`Binary.lean:417`), and `Babs_Bopp_compat`
   (`Binary.lean:428`) had to add the artificial hypothesis
   `(hx : is_nan_FF x = false)`.
-/

/-- `FloatSpec`'s upstream `Babs` definition (`Binary.lean:364-369`), which
erroneously preserves the sign bit `s` on `.F754_nan s pl`. -/
def Babs_upstream (x : FullFloat) : FullFloat :=
  match x with
  | .F754_zero _ => .F754_zero false
  | .F754_infinity _ => .F754_infinity false
  | .F754_nan s pl => .F754_nan s pl
  | .F754_finite _ m e => .F754_finite false m e

/-- Counterexample: `FloatSpec`'s upstream `Babs` fails to clear the sign bit
on a negative NaN (`s = true`), violating IEEE 754-2008 §5.5.1 and RFC 3514. -/
theorem Babs_upstream_fails_on_neg_nan (pl : Nat) :
    sign_FF (Babs_upstream (.F754_nan true pl)) = true ∧
    Babs_upstream (Babs_upstream (.F754_nan true pl)) ≠ .F754_nan false pl := by
  simp [Babs_upstream, sign_FF]

/-- RFC 3514 / IEEE 754-2008 §5.5.1 compliant `Bneg` (`Bopp`) on `FullFloat`:
flips the sign bit across all four constructors, leaving NaN payloads alone. -/
def Bneg_FF (x : FullFloat) : FullFloat :=
  match x with
  | .F754_zero s => .F754_zero (!s)
  | .F754_infinity s => .F754_infinity (!s)
  | .F754_nan s pl => .F754_nan (!s) pl
  | .F754_finite s m e => .F754_finite (!s) m e

/-- RFC 3514 / IEEE 754-2008 §5.5.1 compliant `Babs` on `FullFloat`:
clears the sign bit to `false` across all four constructors (including
`.F754_nan _ pl`), leaving the NaN payload `pl` untouched. -/
def Babs_FF (x : FullFloat) : FullFloat :=
  match x with
  | .F754_zero _ => .F754_zero false
  | .F754_infinity _ => .F754_infinity false
  | .F754_nan _ pl => .F754_nan false pl
  | .F754_finite _ m e => .F754_finite false m e

/-- RFC 3514 / IEEE 754-2008 §5.5.1 compliant `Bcopysign` on `FullFloat`:
copies `sign_FF y` into `x` across all four constructors of `x` (and all four
constructors of `y`), leaving `x`'s NaN payload untouched. -/
def Bcopysign_FF (x y : FullFloat) : FullFloat :=
  let sy := sign_FF y
  match x with
  | .F754_zero _ => .F754_zero sy
  | .F754_infinity _ => .F754_infinity sy
  | .F754_nan _ pl => .F754_nan sy pl
  | .F754_finite _ m e => .F754_finite sy m e

-- Unconditional algebraic and bitwise properties on `FullFloat` (holding for
-- all values including signaling and quiet NaNs, with NO `is_nan_FF x = false`
-- precondition):

@[simp]
theorem sign_FF_Babs (x : FullFloat) : sign_FF (Babs_FF x) = false := by
  cases x <;> rfl

@[simp]
theorem Babs_FF_idempotent (x : FullFloat) :
    Babs_FF (Babs_FF x) = Babs_FF x := by
  cases x <;> rfl

@[simp]
theorem Babs_Bneg_FF (x : FullFloat) : Babs_FF (Bneg_FF x) = Babs_FF x := by
  cases x <;> rfl

@[simp]
theorem Bneg_FF_involutive (x : FullFloat) : Bneg_FF (Bneg_FF x) = x := by
  cases x <;> simp [Bneg_FF]

@[simp]
theorem sign_FF_Bneg (x : FullFloat) : sign_FF (Bneg_FF x) = !sign_FF x := by
  cases x <;> rfl

@[simp]
theorem sign_FF_Bcopysign (x y : FullFloat) :
    sign_FF (Bcopysign_FF x y) = sign_FF y := by
  cases x <;> rfl

@[simp]
theorem Bcopysign_FF_self (x : FullFloat) : Bcopysign_FF x x = x := by
  cases x <;> rfl

@[simp]
theorem Bcopysign_Bneg_left_FF (x y : FullFloat) :
    Bcopysign_FF (Bneg_FF x) y = Bcopysign_FF x y := by
  cases x <;> rfl

@[simp]
theorem Bcopysign_Babs_left_FF (x y : FullFloat) :
    Bcopysign_FF (Babs_FF x) y = Bcopysign_FF x y := by
  cases x <;> rfl

@[simp]
theorem Babs_FF_eq_Bcopysign_pos_zero (x : FullFloat) :
    Babs_FF x = Bcopysign_FF x (.F754_zero false) := by
  cases x <;> rfl

@[simp]
theorem is_nan_Babs_FF (x : FullFloat) :
    is_nan_FF (Babs_FF x) = is_nan_FF x := by
  cases x <;> rfl

@[simp]
theorem is_nan_Bneg_FF (x : FullFloat) :
    is_nan_FF (Bneg_FF x) = is_nan_FF x := by
  cases x <;> rfl

@[simp]
theorem is_nan_Bcopysign_FF (x y : FullFloat) :
    is_nan_FF (Bcopysign_FF x y) = is_nan_FF x := by
  cases x <;> rfl

/-- RFC 3514 payload preservation: `Babs_FF`, `Bneg_FF`, and `Bcopysign_FF`
preserve the exact NaN payload `pl` (including the quiet/signaling bit) without
quieting or canonicalizing. -/
@[simp]
theorem get_nan_pl_Babs_FF (x : FullFloat) :
    get_nan_pl (Babs_FF x) = get_nan_pl x := by
  cases x <;> rfl

@[simp]
theorem get_nan_pl_Bneg_FF (x : FullFloat) :
    get_nan_pl (Bneg_FF x) = get_nan_pl x := by
  cases x <;> rfl

@[simp]
theorem get_nan_pl_Bcopysign_FF (x y : FullFloat) :
    get_nan_pl (Bcopysign_FF x y) = get_nan_pl x := by
  cases x <;> rfl

-- Proof-carrying `binary_float prec emax` versions of `Bneg`, `Babs`, and
-- `Bcopysign`:

namespace binary_float

/-- Sign-bit extractor on proof-carrying `binary_float prec emax`. -/
def Bsign {prec emax : Int} (x : binary_float prec emax) : Bool :=
  match x with
  | .B754_zero s => s
  | .B754_infinity s => s
  | .B754_nan s _ _ => s
  | .B754_finite s _ _ _ => s

/-- NaN classifier on proof-carrying `binary_float prec emax`. -/
def is_nan {prec emax : Int} (x : binary_float prec emax) : Bool :=
  match x with
  | .B754_nan _ _ _ => true
  | _ => false

/-- RFC 3514 `Bneg` (`Bopp`) on proof-carrying `binary_float prec emax`.
Because `nan_pl` and `specFloat_bounded` do not depend on the sign bit `s`,
the validity proofs pass through unchanged. -/
def Bneg {prec emax : Int} (x : binary_float prec emax) :
    binary_float prec emax :=
  match x with
  | .B754_zero s => .B754_zero (!s)
  | .B754_infinity s => .B754_infinity (!s)
  | .B754_nan s pl hpl => .B754_nan (!s) pl hpl
  | .B754_finite s m e hb => .B754_finite (!s) m e hb

/-- RFC 3514 `Babs` on proof-carrying `binary_float prec emax`. -/
def Babs {prec emax : Int} (x : binary_float prec emax) :
    binary_float prec emax :=
  match x with
  | .B754_zero _ => .B754_zero false
  | .B754_infinity _ => .B754_infinity false
  | .B754_nan _ pl hpl => .B754_nan false pl hpl
  | .B754_finite _ m e hb => .B754_finite false m e hb

/-- RFC 3514 `Bcopysign` on proof-carrying `binary_float prec emax`. -/
def Bcopysign {prec emax : Int} (x y : binary_float prec emax) :
    binary_float prec emax :=
  let sy := Bsign y
  match x with
  | .B754_zero _ => .B754_zero sy
  | .B754_infinity _ => .B754_infinity sy
  | .B754_nan _ pl hpl => .B754_nan sy pl hpl
  | .B754_finite _ m e hb => .B754_finite sy m e hb

@[simp]
theorem Bsign_Babs {prec emax : Int} (x : binary_float prec emax) :
    Bsign (Babs x) = false := by
  cases x <;> rfl

@[simp]
theorem Babs_idempotent {prec emax : Int} (x : binary_float prec emax) :
    Babs (Babs x) = Babs x := by
  cases x <;> rfl

@[simp]
theorem Babs_Bneg {prec emax : Int} (x : binary_float prec emax) :
    Babs (Bneg x) = Babs x := by
  cases x <;> rfl

@[simp]
theorem Bneg_involutive {prec emax : Int} (x : binary_float prec emax) :
    Bneg (Bneg x) = x := by
  cases x <;> simp [Bneg]

@[simp]
theorem Bsign_Bneg {prec emax : Int} (x : binary_float prec emax) :
    Bsign (Bneg x) = !Bsign x := by
  cases x <;> rfl

@[simp]
theorem Bsign_Bcopysign {prec emax : Int} (x y : binary_float prec emax) :
    Bsign (Bcopysign x y) = Bsign y := by
  cases x <;> rfl

@[simp]
theorem Bcopysign_self {prec emax : Int} (x : binary_float prec emax) :
    Bcopysign x x = x := by
  cases x <;> rfl

end binary_float

-- ============================================================================
-- Section 5: Bridge Between `FloatSpec` (`Binary.lean`) and Round 1's
-- `FloatProbe.lean` RFC 3514 Nondeterministic NaN Envelope
-- ============================================================================

/-!
## Connecting `FloatSpec`'s `BinarySingleNaNBridge` to `FloatProbe.lean`

In `FloatSpec/src/IEEE754/Binary.lean:1189-1565`, arithmetic operations such as
`Bplus`, `Bmult`, `Bdiv`, `Bsqrt`, and `Bfma` are defined by:
1. Erasing the operands' NaN payloads via `B2BSN : Binary754 prec emax →
   BinarySingleNaNBridge.BinaryFloat`.
2. Executing the single-NaN IEEE-754 operation on `BinaryFloat`.
3. Lifting the result back to `Binary754 prec emax` via `BSN2B nan x`, where
   `nan : { nan : Binary754 prec emax // is_nan_FF nan.val = true }` is produced
   by a caller-supplied NaN handler (e.g., `plus_nan x y`).

We prove below that:
- For `PackedFloat32` (`BitVec 32`) from Round 1's `FloatProbe.lean`, the
  bitwise operations `PackedFloat32.neg`, `PackedFloat32.abs`, and
  `PackedFloat32.copysign` commute strictly with decoding to `FullFloat` and
  applying `Bneg_FF`, `Babs_FF`, and `Bcopysign_FF`.
- For IEEE-754 arithmetic operations (`add`, `sub`, `mul`, `div`, `rem`),
  `FloatSpec`'s `BSN2B` NaN-handler parameterization and Round 1's RFC 3514
  relational envelope `Rfc3514BinOp` are dual representations of the exact same
  semantics:
  1. When the single-NaN result is non-NaN, the NaN handler is ignored and
     `FloatSpec` produces the unique deterministic result required by RFC 3514.
  2. When the single-NaN result is `.B754_nan`, any quiet-NaN handler in
     `FloatSpec` produces a valid member of the RFC 3514 nondeterministic
     quiet-NaN envelope, and conversely every branch of the RFC 3514 envelope
     is realized by a constant quiet-NaN handler in `FloatSpec`.
  3. Any payload-oblivious postcondition proved for a single default handler
     (such as `FloatSpec`'s `default_Bplus_nan`) holds across all branches of
     the RFC 3514 nondeterministic NaN envelope.
-/

namespace BinarySingleNaNBridge

/-- Single-NaN binary float carrier (`Binary.lean:1192`). -/
inductive BinaryFloat where
  | B754_zero (s : Bool) : BinaryFloat
  | B754_infinity (s : Bool) : BinaryFloat
  | B754_nan : BinaryFloat
  | B754_finite (s : Bool) (m : Nat) (e : Int) : BinaryFloat
  deriving DecidableEq, Repr

/-- Erase `Binary754` NaN sign and payload to `BinaryFloat`
(`Binary.lean:1214`). -/
def B2BSN {prec emax : Int} (x : Binary754 prec emax) : BinaryFloat :=
  match x.val with
  | .F754_zero s => .B754_zero s
  | .F754_infinity s => .B754_infinity s
  | .F754_nan _ _ => .B754_nan
  | .F754_finite s m e => .B754_finite s m e

/-- Lift a single-NaN `BinaryFloat` back to `Binary754` by supplying a
distinguished NaN witness `nan` (`Binary.lean:1224`). -/
def BSN2B {prec emax : Int}
    (nan : { nan : Binary754 prec emax // is_nan_FF nan.val = true })
    (x : BinaryFloat) : Binary754 prec emax :=
  match x with
  | .B754_nan => nan.val
  | .B754_zero s => FF2B (.F754_zero s)
  | .B754_infinity s => FF2B (.F754_infinity s)
  | .B754_finite s m e => FF2B (.F754_finite s m e)

theorem B2BSN_BSN2B {prec emax : Int}
    (nan : { nan : Binary754 prec emax // is_nan_FF nan.val = true })
    (x : BinaryFloat) :
    B2BSN (BSN2B nan x) = x := by
  cases x with
  | B754_zero s => rfl
  | B754_infinity s => rfl
  | B754_finite s m e => rfl
  | B754_nan =>
      rcases nan with ⟨⟨v⟩, hv⟩
      cases v <;> simp [is_nan_FF] at hv
      rfl

end BinarySingleNaNBridge

/-- A `FullFloat` NaN is a valid quiet NaN for precision `prec` (`prec ≥ 2`)
when its payload `pl` fits in `prec - 1` bits (`pl < 2^(prec - 1)`) and has the
quiet bit (bit `prec - 2`) set (`2^(prec - 2) ≤ pl`). For IEEE `binary32`
(`prec = 24`), this is `2^22 ≤ pl ∧ pl < 2^23`. -/
def is_quiet_nan_FF (prec : Int) (x : FullFloat) : Bool :=
  let mw := Int.toNat (prec - 1)
  let qbit := Int.toNat (prec - 2)
  match x with
  | .F754_nan _ pl =>
      decide (2 ^ qbit ≤ pl) && decide (pl < 2 ^ mw)
  | _ => false

theorem is_quiet_nan_implies_is_nan_FF (prec : Int) (x : FullFloat)
    (hq : is_quiet_nan_FF prec x = true) :
    is_nan_FF x = true := by
  cases x <;> simp [is_quiet_nan_FF, is_nan_FF] at hq ⊢

/-- `FloatSpec`'s parameterized binary operation pattern (`Bplus`, `Bmult`,
`Bdiv`), which delegates arithmetic to a single-NaN operation `bsnOp` and uses
`nan_handler x y` when the result is NaN (`Binary.lean:1456-1555`). -/
def FloatSpecParameterizedBinOp {prec emax : Int}
    (bsnOp : BinarySingleNaNBridge.BinaryFloat →
      BinarySingleNaNBridge.BinaryFloat →
      BinarySingleNaNBridge.BinaryFloat)
    (nan_handler : Binary754 prec emax → Binary754 prec emax →
      { nan : Binary754 prec emax // is_nan_FF nan.val = true })
    (x y : Binary754 prec emax) : Binary754 prec emax :=
  BinarySingleNaNBridge.BSN2B (nan_handler x y)
    (bsnOp (BinarySingleNaNBridge.B2BSN x) (BinarySingleNaNBridge.B2BSN y))

/-- RFC 3514 relational specification on `Binary754 prec emax`:
- If the single-NaN operation `bsnOp (B2BSN x) (B2BSN y)` produces a non-NaN
  value (`.B754_zero`, `.B754_infinity`, or `.B754_finite`), `out` is uniquely
  determined.
- If `bsnOp (B2BSN x) (B2BSN y)` produces `.B754_nan`, `out` may be *any*
  quiet NaN (`is_quiet_nan_FF prec out.val = true`) with arbitrary sign and
  arbitrary quiet payload. -/
def Rfc3514FullFloatEnvelope {prec emax : Int}
    (bsnOp : BinarySingleNaNBridge.BinaryFloat →
      BinarySingleNaNBridge.BinaryFloat →
      BinarySingleNaNBridge.BinaryFloat)
    (x y out : Binary754 prec emax) : Prop :=
  match
      bsnOp (BinarySingleNaNBridge.B2BSN x) (BinarySingleNaNBridge.B2BSN y) with
  | .B754_zero s => out = FF2B (.F754_zero s)
  | .B754_infinity s => out = FF2B (.F754_infinity s)
  | .B754_finite s m e => out = FF2B (.F754_finite s m e)
  | .B754_nan => is_quiet_nan_FF prec out.val = true

/-- **Theorem 1 (Non-NaN Determinism):** When the single-NaN operation produces
a non-NaN result, `FloatSpecParameterizedBinOp` is completely independent of the
choice of NaN handler. -/
theorem floatspec_non_nan_deterministic {prec emax : Int}
    (bsnOp : BinarySingleNaNBridge.BinaryFloat →
      BinarySingleNaNBridge.BinaryFloat →
      BinarySingleNaNBridge.BinaryFloat)
    (h1 h2 : Binary754 prec emax → Binary754 prec emax →
      { nan : Binary754 prec emax // is_nan_FF nan.val = true })
    (x y : Binary754 prec emax)
    (h_non_nan :
      bsnOp (BinarySingleNaNBridge.B2BSN x) (BinarySingleNaNBridge.B2BSN y) ≠
        .B754_nan) :
    FloatSpecParameterizedBinOp bsnOp h1 x y =
      FloatSpecParameterizedBinOp bsnOp h2 x y := by
  unfold FloatSpecParameterizedBinOp
  generalize hbsn :
    bsnOp (BinarySingleNaNBridge.B2BSN x) (BinarySingleNaNBridge.B2BSN y) = res
  cases res with
  | B754_zero s => rfl
  | B754_infinity s => rfl
  | B754_finite s m e => rfl
  | B754_nan => exact False.elim (h_non_nan hbsn)

/-- **Theorem 2 (`FloatSpec` Soundness w.r.t. RFC 3514):** For any NaN handler
`nan_handler` that produces quiet NaNs (`is_quiet_nan_FF prec`),
`FloatSpecParameterizedBinOp bsnOp nan_handler x y` satisfies
`Rfc3514FullFloatEnvelope bsnOp x y`. -/
theorem floatspec_quiet_handler_in_rfc3514_envelope {prec emax : Int}
    (bsnOp : BinarySingleNaNBridge.BinaryFloat →
      BinarySingleNaNBridge.BinaryFloat →
      BinarySingleNaNBridge.BinaryFloat)
    (nan_handler : Binary754 prec emax → Binary754 prec emax →
      { nan : Binary754 prec emax // is_nan_FF nan.val = true })
    (h_quiet : ∀ x y, is_quiet_nan_FF prec (nan_handler x y).val.val = true)
    (x y : Binary754 prec emax) :
    Rfc3514FullFloatEnvelope bsnOp x y
      (FloatSpecParameterizedBinOp bsnOp nan_handler x y) := by
  unfold Rfc3514FullFloatEnvelope FloatSpecParameterizedBinOp
  cases
      bsnOp (BinarySingleNaNBridge.B2BSN x) (BinarySingleNaNBridge.B2BSN y) with
  | B754_zero s => rfl
  | B754_infinity s => rfl
  | B754_finite s m e => rfl
  | B754_nan =>
      simpa [BinarySingleNaNBridge.BSN2B] using h_quiet x y

/-- **Theorem 3 (Completeness of `FloatSpec` NaN Handlers for RFC 3514):**
Every output `out` permitted by `Rfc3514FullFloatEnvelope bsnOp x y` is
realized by `FloatSpecParameterizedBinOp bsnOp` for an appropriate quiet-NaN
handler (given any fallback quiet NaN `default_qnan` for the non-NaN case). -/
theorem rfc3514_envelope_realized_by_floatspec_handler {prec emax : Int}
    (bsnOp : BinarySingleNaNBridge.BinaryFloat →
      BinarySingleNaNBridge.BinaryFloat →
      BinarySingleNaNBridge.BinaryFloat)
    (default_qnan : Binary754 prec emax)
    (h_default_quiet : is_quiet_nan_FF prec default_qnan.val = true)
    (x y out : Binary754 prec emax)
    (h_env : Rfc3514FullFloatEnvelope bsnOp x y out) :
    ∃ (nan_handler : Binary754 prec emax → Binary754 prec emax →
        { nan : Binary754 prec emax // is_nan_FF nan.val = true }),
      (∀ a b, is_quiet_nan_FF prec (nan_handler a b).val.val = true) ∧
      FloatSpecParameterizedBinOp bsnOp nan_handler x y = out := by
  unfold Rfc3514FullFloatEnvelope at h_env
  cases hbsn :
      bsnOp (BinarySingleNaNBridge.B2BSN x) (BinarySingleNaNBridge.B2BSN y) with
  | B754_zero s =>
      rw [hbsn] at h_env
      refine ⟨fun _ _ =>
        ⟨default_qnan, is_quiet_nan_implies_is_nan_FF prec _ h_default_quiet⟩,
        fun _ _ => h_default_quiet, ?_⟩
      simp [FloatSpecParameterizedBinOp, hbsn,
        BinarySingleNaNBridge.BSN2B, h_env]
  | B754_infinity s =>
      rw [hbsn] at h_env
      refine ⟨fun _ _ =>
        ⟨default_qnan, is_quiet_nan_implies_is_nan_FF prec _ h_default_quiet⟩,
        fun _ _ => h_default_quiet, ?_⟩
      simp [FloatSpecParameterizedBinOp, hbsn,
        BinarySingleNaNBridge.BSN2B, h_env]
  | B754_finite s m e =>
      rw [hbsn] at h_env
      refine ⟨fun _ _ =>
        ⟨default_qnan, is_quiet_nan_implies_is_nan_FF prec _ h_default_quiet⟩,
        fun _ _ => h_default_quiet, ?_⟩
      simp [FloatSpecParameterizedBinOp, hbsn,
        BinarySingleNaNBridge.BSN2B, h_env]
  | B754_nan =>
      rw [hbsn] at h_env
      refine ⟨fun _ _ =>
        ⟨out, is_quiet_nan_implies_is_nan_FF prec _ h_env⟩,
        fun _ _ => h_env, ?_⟩
      simp [FloatSpecParameterizedBinOp, hbsn, BinarySingleNaNBridge.BSN2B]

/-- A predicate on `Binary754 prec emax` is payload-oblivious when it depends
only on the single-NaN projection `B2BSN` (for instance, `is_finite_B`,
`is_nan_B`, or any real-valued `B2R` rounding theorem). -/
def PayloadObliviousB {prec emax : Int}
    (P : Binary754 prec emax → Prop) : Prop :=
  ∀ a b : Binary754 prec emax,
    BinarySingleNaNBridge.B2BSN a = BinarySingleNaNBridge.B2BSN b →
      (P a ↔ P b)

/-- **Theorem 4 (Transfer of Single-Handler `FloatSpec` Proofs to All RFC 3514
Branches):** Any payload-oblivious property `P` proved for `FloatSpec` using a
single default NaN handler (such as `default_Bplus_nan`) holds automatically
for *every* nondeterministic output `out` in `Rfc3514FullFloatEnvelope`. -/
theorem payload_oblivious_transfers_from_default_handler {prec emax : Int}
    (bsnOp : BinarySingleNaNBridge.BinaryFloat →
      BinarySingleNaNBridge.BinaryFloat →
      BinarySingleNaNBridge.BinaryFloat)
    (default_handler : Binary754 prec emax → Binary754 prec emax →
      { nan : Binary754 prec emax // is_nan_FF nan.val = true })
    (P : Binary754 prec emax → Prop)
    (h_oblivious : PayloadObliviousB P)
    (x y out : Binary754 prec emax)
    (h_default : P (FloatSpecParameterizedBinOp bsnOp default_handler x y))
    (h_env : Rfc3514FullFloatEnvelope bsnOp x y out) :
    P out := by
  have hbsn_eq :
      BinarySingleNaNBridge.B2BSN
        (FloatSpecParameterizedBinOp bsnOp default_handler x y) =
      BinarySingleNaNBridge.B2BSN out := by
    unfold FloatSpecParameterizedBinOp Rfc3514FullFloatEnvelope at *
    rw [BinarySingleNaNBridge.B2BSN_BSN2B]
    cases hbsn :
        bsnOp (BinarySingleNaNBridge.B2BSN x)
          (BinarySingleNaNBridge.B2BSN y) with
    | B754_zero s =>
        rw [hbsn] at h_env
        subst h_env
        rfl
    | B754_infinity s =>
        rw [hbsn] at h_env
        subst h_env
        rfl
    | B754_finite s m e =>
        rw [hbsn] at h_env
        subst h_env
        rfl
    | B754_nan =>
        rw [hbsn] at h_env
        have hout_nan := is_quiet_nan_implies_is_nan_FF prec out.val h_env
        rcases out with ⟨v⟩
        cases v <;> simp [is_nan_FF] at hout_nan
        rfl
  exact (h_oblivious _ _ hbsn_eq).mp h_default

-- ============================================================================
-- Section 6: Bit-Exact Bridge to Round 1's `PackedFloat32` (`BitVec 32`)
-- ============================================================================

/-- Round 1's IEEE-754 `binary32` (`f32`) bit-level representation from
`FloatProbe.lean`. -/
structure PackedFloat32 where
  bits : BitVec 32
  deriving DecidableEq, Repr

namespace PackedFloat32

def sign (x : PackedFloat32) : Bool := x.bits.getMsbD 0
def exp (x : PackedFloat32) : BitVec 8 := x.bits.extractLsb' 23 8
def mant (x : PackedFloat32) : BitVec 23 := x.bits.extractLsb' 0 23

/-- RFC 3514 bitwise negation: flips bit 31. -/
def neg (x : PackedFloat32) : PackedFloat32 :=
  ⟨x.bits ^^^ 0x80000000#32⟩

/-- RFC 3514 bitwise absolute value: clears bit 31. -/
def abs (x : PackedFloat32) : PackedFloat32 :=
  ⟨x.bits &&& 0x7fffffff#32⟩

/-- RFC 3514 bitwise copysign: copies bit 31 from `y` into `x`. -/
def copysign (x y : PackedFloat32) : PackedFloat32 :=
  ⟨(x.bits &&& 0x7fffffff#32) ||| (y.bits &&& 0x80000000#32)⟩

/-- Convert `PackedFloat32` into `FloatSpec`'s `FullFloat` representation for
`binary32` (`prec = 24`, `emax = 128`, `mw = 23`, `ew = 8`). -/
def toFullFloat (x : PackedFloat32) : FullFloat :=
  let s := x.sign
  let e := x.exp.toNat
  let m := x.mant.toNat
  if e = 255 then
    if m = 0 then .F754_infinity s
    else .F754_nan s m
  else if e = 0 then
    if m = 0 then .F754_zero s
    else .F754_finite s m (-149)
  else
    .F754_finite s ((2 ^ 23) + m) ((e : Int) - 150)

private theorem sign_mask_low_false :
    ∀ k : Fin 31, (0x80000000#32).getLsbD k.val = false := by decide

private theorem mag_mask_low_true :
    ∀ k : Fin 31, (0x7fffffff#32).getLsbD k.val = true := by decide

theorem sign_neg (x : PackedFloat32) : x.neg.sign = !x.sign := by
  simp [neg, sign, BitVec.getMsbD]

theorem exp_neg (x : PackedFloat32) : x.neg.exp = x.exp := by
  ext i hi
  have hk : (0x80000000#32).getLsbD (23 + i) = false :=
    sign_mask_low_false ⟨23 + i, by omega⟩
  simp [neg, exp, hk]

theorem mant_neg (x : PackedFloat32) : x.neg.mant = x.mant := by
  ext i hi
  have hk : (0x80000000#32).getLsbD i = false :=
    sign_mask_low_false ⟨i, by omega⟩
  simp [neg, mant, hk]

theorem sign_abs (x : PackedFloat32) : x.abs.sign = false := by
  simp [abs, sign, BitVec.getMsbD]

theorem exp_abs (x : PackedFloat32) : x.abs.exp = x.exp := by
  ext i hi
  have hk : (0x7fffffff#32).getLsbD (23 + i) = true :=
    mag_mask_low_true ⟨23 + i, by omega⟩
  simp [abs, exp, hk]

theorem mant_abs (x : PackedFloat32) : x.abs.mant = x.mant := by
  ext i hi
  have hk : (0x7fffffff#32).getLsbD i = true :=
    mag_mask_low_true ⟨i, by omega⟩
  simp [abs, mant, hk]

theorem sign_copysign (x y : PackedFloat32) :
    (x.copysign y).sign = y.sign := by
  simp [copysign, sign, BitVec.getMsbD]

theorem exp_copysign (x y : PackedFloat32) :
    (x.copysign y).exp = x.exp := by
  ext i hi
  have hk1 : (0x7fffffff#32).getLsbD (23 + i) = true :=
    mag_mask_low_true ⟨23 + i, by omega⟩
  have hk2 : (0x80000000#32).getLsbD (23 + i) = false :=
    sign_mask_low_false ⟨23 + i, by omega⟩
  simp [copysign, exp, hk1, hk2]

theorem mant_copysign (x y : PackedFloat32) :
    (x.copysign y).mant = x.mant := by
  ext i hi
  have hk1 : (0x7fffffff#32).getLsbD i = true :=
    mag_mask_low_true ⟨i, by omega⟩
  have hk2 : (0x80000000#32).getLsbD i = false :=
    sign_mask_low_false ⟨i, by omega⟩
  simp [copysign, mant, hk1, hk2]

/-- Bit-exact commutation between `PackedFloat32.neg` and `FloatSpec`'s
`Bneg_FF` across all $2^{32}$ `f32` bit patterns (including signaling and quiet
NaNs). -/
theorem toFullFloat_neg (x : PackedFloat32) :
    x.neg.toFullFloat = Bneg_FF x.toFullFloat := by
  dsimp only [toFullFloat]
  rw [sign_neg, exp_neg, mant_neg]
  by_cases he255 : x.exp.toNat = 255 <;>
    by_cases he0 : x.exp.toNat = 0 <;>
    by_cases hm0 : x.mant.toNat = 0 <;>
    simp [he255, he0, hm0, Bneg_FF]

/-- Bit-exact commutation between `PackedFloat32.abs` and our fixed RFC 3514
`Babs_FF` across all $2^{32}$ `f32` bit patterns (including signaling and quiet
NaNs). -/
theorem toFullFloat_abs (x : PackedFloat32) :
    x.abs.toFullFloat = Babs_FF x.toFullFloat := by
  dsimp only [toFullFloat]
  rw [sign_abs, exp_abs, mant_abs]
  by_cases he255 : x.exp.toNat = 255 <;>
    by_cases he0 : x.exp.toNat = 0 <;>
    by_cases hm0 : x.mant.toNat = 0 <;>
    simp [he255, he0, hm0, Babs_FF]

theorem sign_FF_toFullFloat (y : PackedFloat32) :
    sign_FF y.toFullFloat = y.sign := by
  dsimp only [toFullFloat]
  by_cases he255 : y.exp.toNat = 255 <;>
    by_cases he0 : y.exp.toNat = 0 <;>
    by_cases hm0 : y.mant.toNat = 0 <;>
    simp [he255, he0, hm0, sign_FF]

/-- Bit-exact commutation between `PackedFloat32.copysign` and `Bcopysign_FF`
across all $2^{32} \times 2^{32}$ pairs of `f32` bit patterns. -/
theorem toFullFloat_copysign (x y : PackedFloat32) :
    (x.copysign y).toFullFloat = Bcopysign_FF x.toFullFloat y.toFullFloat := by
  dsimp only [Bcopysign_FF]
  rw [sign_FF_toFullFloat]
  dsimp only [toFullFloat]
  rw [sign_copysign, exp_copysign, mant_copysign]
  by_cases he255 : x.exp.toNat = 255 <;>
    by_cases he0 : x.exp.toNat = 0 <;>
    by_cases hm0 : x.mant.toNat = 0 <;>
    simp [he255, he0, hm0]

end PackedFloat32

-- ============================================================================
-- Section 7: Kernel Axiom Audit (`#print axioms`)
-- ============================================================================

#print axioms Core.Digits.digits2_Pnat_correct
#print axioms binaryFloatToFullFloat_fullFloatToBinaryFloat
#print axioms fullFloatToBinaryFloat_binaryFloatToFullFloat
#print axioms Babs_upstream_fails_on_neg_nan
#print axioms sign_FF_Babs
#print axioms Babs_FF_idempotent
#print axioms Babs_Bneg_FF
#print axioms Bneg_FF_involutive
#print axioms sign_FF_Bcopysign
#print axioms binary_float.Bsign_Babs
#print axioms binary_float.Babs_idempotent
#print axioms binary_float.Babs_Bneg
#print axioms binary_float.Bneg_involutive
#print axioms binary_float.Bsign_Bcopysign
#print axioms floatspec_non_nan_deterministic
#print axioms floatspec_quiet_handler_in_rfc3514_envelope
#print axioms rfc3514_envelope_realized_by_floatspec_handler
#print axioms payload_oblivious_transfers_from_default_handler
#print axioms PackedFloat32.toFullFloat_neg
#print axioms PackedFloat32.toFullFloat_abs
#print axioms PackedFloat32.toFullFloat_copysign

end Anneal.FloatSpecBridge
