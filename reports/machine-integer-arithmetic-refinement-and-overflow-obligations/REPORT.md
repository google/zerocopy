# Machine-integer arithmetic in Lean: wrapping refinement, checked-arithmetic side conditions, division, shifts and casts for a Rust-style integer model

## Summary

This package is a self-contained, Mathlib-free Lean 4 development (namespace `Toy.MachInt`, Lean `v4.34.1`) of fixed-width unsigned and two's-complement signed integers over Lean core's `BitVec n`, with the side conditions under which machine arithmetic agrees with mathematical integer arithmetic. All 35 results below are kernel-checked with no `sorry` and only the standard axioms `propext`, `Classical.choice`, `Quot.sound`. Their connection to Rust is a separate, modeling-level claim (see Applicability and the `Basis: derived (modeling bridge)` lines in Findings).

*An agent relying on a result from this package must quote its plain-language claim and the relevant hypotheses and non-claims, not just its name or a paraphrase.*

Results (one plain-language claim each; every hypothesis named in a claim is part of it):

- **Result 1: wrapping evaluation refines integer ring arithmetic modulo 2^n.**
  - `evalWrap_toNat_eq_emod` (theorem): For every bitwidth n, environment env : Nat → BitVec n, and ring expression e : RingExpr (over +, -, *, unary -, variables, and literals), the unsigned value (evalWrap n env e).toNat equals the mathematical integer evaluation evalInt (fun i => (env i).toNat) e reduced modulo 2^n via Euclidean Int.emod, with no overflow side conditions.
  - `evalWrap_toInt_eq_bmod` (theorem): For every bitwidth n, environment env : Nat → BitVec n, and ring expression e : RingExpr, the signed two's-complement value (evalWrap n env e).toInt equals the mathematical integer evaluation evalInt (fun i => (env i).toInt) e reduced via balanced modulo Int.bmod · (2^n), with no overflow side conditions.
  - `evalWrap_eq_of_intRingIdentity` (theorem): For every bitwidth n, environment env : Nat → BitVec n, and pair of expressions e₁ e₂ : RingExpr satisfying IntRingIdentity e₁ e₂ (agreement under every mathematical valuation ρ : Nat → Int), their wrapping evaluations coincide: evalWrap n env e₁ = evalWrap n env e₂, with no overflow side conditions.
- **Result 2: checked evaluation is sound, and succeeds exactly when every subexpression is in range.**
  - `evalCheckedU_sound` (theorem): For every bitwidth n, environment env : Nat → BitVec n, ring expression e : RingExpr, and result v : BitVec n, if checked unsigned evaluation returns some v (evalCheckedU n env e = some v, which by definition of evalPlainU coincides with evalPlainU n env e = Outcome.ok v), then (v.toNat : Int) equals the unreduced mathematical integer evaluation evalInt (fun i => (env i).toNat) e.
  - `evalCheckedU_complete` (theorem): For every bitwidth n, environment env : Nat → BitVec n, and ring expression e : RingExpr, if every subexpression of e (variables, typed constants, and every compound node) evaluates inside InUnsignedRange n under SubexprsInRange (InUnsignedRange n) (fun i => (env i).toNat) e, then evalCheckedU n env e returns some (evalWrap n env e).
  - `evalCheckedU_isSome_iff_subexprsInRange` (characterization): For every bitwidth n, environment env : Nat → BitVec n, and ring expression e : RingExpr, checked unsigned evaluation succeeds ((evalCheckedU n env e).isSome = true) if and only if SubexprsInRange (InUnsignedRange n) (fun i => (env i).toNat) e holds.
  - `evalCheckedS_sound` (theorem): For every bitwidth n, environment env : Nat → BitVec n, ring expression e : RingExpr, and result v : BitVec n, if checked signed evaluation returns some v (evalCheckedS n env e = some v, definitionally evalPlainS n env e = Outcome.ok v), then v.toInt equals the unreduced mathematical integer evaluation evalInt (fun i => (env i).toInt) e.
  - `evalCheckedS_complete` (theorem): For every bitwidth n, environment env : Nat → BitVec n, and ring expression e : RingExpr, if every subexpression of e evaluates inside InSignedRange n under SubexprsInRange (InSignedRange n) (fun i => (env i).toInt) e, then evalCheckedS n env e returns some (evalWrap n env e).
  - `evalCheckedS_isSome_iff_subexprsInRange` (characterization): For every bitwidth n, environment env : Nat → BitVec n, and ring expression e : RingExpr, checked signed evaluation succeeds ((evalCheckedS n env e).isSome = true) if and only if SubexprsInRange (InSignedRange n) (fun i => (env i).toInt) e holds.
  - `ce_checked_add_sub_intermediate_overflow` (counterexample): For the expression (a + b) - b at 8 bits with (a, b) = (200u8, 100u8) unsigned and (100i8, 50i8) signed, the mathematical result equals a and lies in range, and wrapping evaluation recovers a, yet checked evaluation returns none and plain overflow-checked evaluation produces Outcome.panic.
- **Result 3: order under wrapping addition.**
  - `not_ult_allOnes_add_one` (impossibility): For every bitwidth n, BitVec.allOnes n + 1#n = 0#n, ¬ Ult (BitVec.allOnes n) (BitVec.allOnes n + 1#n), and ¬ (∀ x : BitVec n, Ult x (x + 1#n)). A companion lemma (ult_allOnes_add_one_allOnes_of_posWidth, not part of this statement) adds that under PosWidth n BitVec.allOnes n + 1#n wraps strictly below BitVec.allOnes n.
  - `not_slt_intMax_add_one` (impossibility): For every bitwidth n, BitVec.intMax n + 1#n = BitVec.intMin n, ¬ Slt (BitVec.intMax n) (BitVec.intMax n + 1#n), and ¬ (∀ x : BitVec n, Slt x (x + 1#n)). A companion lemma (slt_intMax_add_one_intMax_of_posWidth, not part of this statement) adds that under PosWidth n BitVec.intMax n + 1#n wraps strictly below BitVec.intMax n.
  - `ult_add_right_of_noUAddOverflow` (theorem): For bitvectors a b c : BitVec n, if Ult a b and NoUAddOverflow b c (which entails NoUAddOverflow a c), then Ult (a + c) (b + c).
  - `slt_add_right_of_noSAddOverflow` (theorem): For bitvectors a b c : BitVec n, if Slt a b, NoSAddOverflow a c, and NoSAddOverflow b c, then Slt (a + c) (b + c).
  - `ult_add_right_iff_uaddOverflow_eq` (characterization): For bitvectors a b c : BitVec n with Ult a b, wrapping unsigned addition preserves order (Ult (a + c) (b + c)) if and only if BitVec.uaddOverflow a c = BitVec.uaddOverflow b c (either neither wraps, or both wrap modulo 2^n).
  - `slt_add_right_iff_saddOverflow_eq` (characterization): For bitvectors a b c : BitVec n with Slt a b, wrapping signed addition preserves order (Slt (a + c) (b + c)) if and only if BitVec.saddOverflow a c = BitVec.saddOverflow b c (either neither wraps, or both wrap in the same direction).
- **Result 4: division and remainder.**
  - `checkedUDiv_and_checkedURem_eq_nat_div_mod` (theorem): For any a b : BitVec n satisfying NonZeroDiv b, both checkedUDiv a b and checkedURem a b return some q and some r with q.toNat = a.toNat / b.toNat and r.toNat = a.toNat % b.toNat.
  - `checkedSDiv_eq_some_and_toInt_eq_tdiv` (theorem): For any a b : BitVec n satisfying NonZeroDiv b and NoSDivOverflow a b, checkedSDiv a b returns some q whose signed integer value q.toInt equals truncating division a.toInt.tdiv b.toInt (not Lean's default Euclidean Int /).
  - `checkedSRem_eq_some_and_toInt_eq_tmod` (theorem): For any a b : BitVec n satisfying NonZeroDiv b and NoSDivOverflow a b, checkedSRem a b returns some r whose signed integer value r.toInt equals truncating remainder a.toInt.tmod b.toInt (not Lean's default Euclidean Int %).
  - `tdiv_not_inSignedRange_iff_intMin_negOne` (characterization): For every positive bitwidth PosWidth n and every a b : BitVec n, the mathematical truncating quotient a.toInt.tdiv b.toInt falls outside InSignedRange n if and only if a = BitVec.intMin n and b = -1#n.
  - `checkedSRem_intMin_negOne_eq_none` (theorem): For every positive bitwidth PosWidth n, -1#n is nonzero (NonZeroDiv (-1#n)) and the mathematical truncating remainder (BitVec.intMin n).toInt.tmod (-1#n).toInt lies in InSignedRange n, yet both checkedSRem (BitVec.intMin n) (-1#n) and checkedSRemEuclid (BitVec.intMin n) (-1#n) equal none.
  - `checkedSDivEuclid_eq_some_and_toInt_eq_ediv` (theorem): For any a b : BitVec n satisfying NonZeroDiv b and NoSDivOverflow a b, checkedSDivEuclid a b (modeling i<n>::checked_div_euclid) returns some q with q.toInt = a.toInt.ediv b.toInt (Lean's default Int /).
  - `checkedSRemEuclid_eq_some_and_toInt_eq_emod` (theorem): For any a b : BitVec n satisfying NonZeroDiv b and NoSDivOverflow a b, checkedSRemEuclid a b (modeling i<n>::checked_rem_euclid) returns some r with r.toInt = a.toInt.emod b.toInt (Lean's default Int %, always in [0, |b|)).
  - `ce_sdiv_srem_ne_int_ediv_emod` (counterexample): For (-7 : i8) and (4 : i8), Rust/bitvector truncating sdiv and srem yield (-1, -3) (Int.tdiv/Int.tmod), directly disagreeing with Lean's default Int / and % (-2, 1, matching sdivEuclid/sremEuclid); for (7 : i8) and (-4 : i8), truncating sdiv/srem coincide with Int.ediv/Int.emod (-1, 3) while differing from flooring Int.fdiv and BitVec.smod (-2, -1).
- **Result 5: shifts and shift-count masking.**
  - `wrappingShl_eq_mul_twoPow_of_shiftInBounds` (theorem): For any x : BitVec n and shift count k satisfying ShiftInBounds n k (k < n), checkedShl x k = some (wrappingShl x k), (wrappingShl x k).toNat = (x.toNat * 2^k) % 2^n, and (wrappingShl x k).toInt = Int.bmod (x.toInt * 2^k) (2^n).
  - `wrappingUShr_and_wrappingSShr_of_shiftInBounds` (theorem): For any x : BitVec n and shift count k satisfying ShiftInBounds n k (k < n), checkedUShr x k = some (wrappingUShr x k) with toNat = x.toNat / 2^k, and checkedSShr x k = some (wrappingSShr x k) with toInt = x.toInt.fdiv (2^k) (flooring division, not truncating tdiv).
  - `ce_wrappingShl_overshift_ne_mul_twoPow` (counterexample): At width n = 8 with shift counts k ≥ n: checkedShl (1#8) 8 = none and checkedShl (5#8) 9 = none, while (wrappingShl (1#8) 8).toNat ≠ (1 * 2^8) % 2^8, (wrappingShl (5#8) 9).toNat ≠ (5 * 2^9) % 2^8, and (wrappingShl (-1#8) 8).toInt ≠ Int.bmod (-1 * 2^8) (2^8); so without k < n the unsigned and signed multiplication identities of wrappingShl_eq_mul_twoPow_of_shiftInBounds fail.
  - `ce_checkedShl_drops_high_bits_without_none` (counterexample): At n = 8 and k = 1, ShiftInBounds 8 1 holds so checkedShl (128#8) 1 = some 0#8 and checkedShl (64#8) 1 = some (-128#8) succeed despite shifting out/overflowing high bits, whereas checkedUMul (128#8) 2#8 = none and checkedSMul (64#8) 2#8 = none.
- **Result 6: numeric `as` casts.**
  - `castFromUnsigned_toNat_eq_mod` (theorem): For every source width n, target width m, and x : BitVec n, (castFromUnsigned m x).toNat = x.toNat % 2^m unconditionally.
  - `castFromUnsigned_widened_toNat_eq_mod` (theorem): For any x : BitVec n and widths m, k satisfying WidthLe m k (m ≤ k), truncating/casting x to m bits and then widening/keeping to k bits satisfies (castFromUnsigned k (castFromUnsigned m x)).toNat = x.toNat % 2^m.
  - `cast_u32_to_u8_to_u32_eq_mod_256` (theorem): For every x : BitVec 32, casting to 8 bits and back to 32 bits yields (castFromUnsigned 32 (castFromUnsigned 8 x)).toNat = x.toNat % 256.
  - `castFromSigned_toInt_eq_of_widthLe` (theorem): For any signed n-bit value x : BitVec n and target width m satisfying WidthLe n m (n ≤ m), sign-extending x to m bits preserves its signed integer value: (castFromSigned m x).toInt = x.toInt.
  - `reinterpretCast_characterization` (characterization): For any bitwidth n and x : BitVec n, same-width reinterpretation reinterpretCast x satisfies (reinterpretCast x).toNat = if x.toInt < 0 then x.toInt + 2^n else x.toInt, and (reinterpretCast x).toInt = Int.bmod x.toNat (2^n).
  - `cast_roundTrip_widen_then_narrow_of_widthLe` (theorem): For any x : BitVec n and width m satisfying WidthLe n m (n ≤ m), widening then narrowing back is an exact identity for both unsigned (castFromUnsigned n (castFromUnsigned m x) = x) and signed (castFromSigned n (castFromSigned m x) = x) casts.
  - `ce_cast_roundTrip_narrow_then_widen` (counterexample): Narrowing then widening does not preserve values, unsigned or signed: castFromUnsigned 16 (castFromUnsigned 8 256#16) ≠ 256#16 and castFromSigned 16 (castFromSigned 8 128#16) ≠ 128#16; and sign-extending a signed value differs from first reinterpreting it as unsigned and then zero-extending: castFromSigned 16 (-1#8) ≠ castFromUnsigned 16 (reinterpretCast (-1#8)).

Companion results (proved, cited from the cards above): `castFromUnsigned_widened_toNat_eq_mod_forall_iff` (the composed unsigned cast identity holds for every `x` exactly when `m ≤ k ∨ n ≤ k`); `castFromUnsigned_widened_toNat_eq_mod_of_source_le` (it holds when `n ≤ k`); `mod_eq_and_mask_forall_iff_isPowerOfTwo` (`k % n = k &&& (n - 1)` for every `k` exactly when `n` is a power of two).

What these results do **not** say is recorded under Boundaries; the package-wide non-claims N1 (no floating point), N2 (`usize`/`isize` only by instantiating `n` for a stated target) and N3 (no claims about C or C++) apply to every result.

## Applicability

**Model fidelity: this is a toy model.** The definitions are written for this package (namespace `Toy.MachInt`); they are not extracted from, or checked against, the source of any Rust compiler, verifier, or standard library. They are intended to capture Rust's fixed-width integer types `u8`..`u128` and `i8`..`i128` (the width `n` is a parameter; Rust's types are the instances `n ∈ {8, 16, 32, 64, 128}`) and the following operations:

- wrapping ring operations (`wrapping_add`, `wrapping_sub`, `wrapping_mul`, `wrapping_neg`, `Wrapping<T>`) as `BitVec n` arithmetic (`evalWrap`);
- `checked_add`, `checked_sub`, `checked_mul`, `checked_neg` as `Option`-valued operations guarded by Lean core's overflow flags, and plain ring operators under overflow checks as `Outcome.ok`/`Outcome.panic` (`evalCheckedU`, `evalCheckedS`, `evalPlainU`, `evalPlainS`);
- `checked_div`, `checked_rem`, `checked_div_euclid`, `checked_rem_euclid` (`checkedUDiv`, `checkedURem`, `checkedSDiv`, `checkedSRem`, `checkedSDivEuclid`, `checkedSRemEuclid`, with `sdivEuclid`/`sremEuclid` as the Euclidean adjustment of Lean's `BitVec.sdiv`/`BitVec.srem`);
- `wrapping_shl`/`wrapping_shr` (count reduced modulo `n`) and `checked_shl`/`checked_shr` (`None` iff the count is at least `n`);
- integer-to-integer `as` casts (`castFromUnsigned` = `setWidth`, `castFromSigned` = `signExtend`, `reinterpretCast` = identity on bits).

**Known gaps between the model and Rust.**

- Plain `/`, `%`, `<<`, `>>` have no separate panicking evaluator; they are covered only through the `checked*` and `wrapping*` operations.
- `.lit k` is a typed constant value, not a literal token: out-of-range literal tokens are compile-time errors in Rust (deny-by-default `overflowing_literals`), `-128_i8` is unary minus applied to a literal (exempt from overflow), and unary `-` on unsigned types is error `E0600`. `evalCheckedU` models `.neg` by `checked_neg`, which has no plain-operator counterpart on unsigned types.
- Wrapping of plain operators when overflow checks are disabled is `rustc` behaviour, not a language guarantee (the Rust Reference permits a panic or a wrapped value; the Ferrocene Language Specification likewise allows either).
- The width `n` ranges over all naturals, including `n = 0` and non-power-of-two widths. At non-power-of-two widths the model's shift-count reduction `k % n` differs from Rust's mask `k & (BITS - 1)`; Rust has no such types.
- `usize`/`isize`, floating-point types, `bool`/`char`/enum/pointer casts, `From`/`TryFrom`, code generation, and C/C++ semantics are not modelled (see Boundaries).

**Toolchain.** Lean `leanprover/lean4:v4.34.1` (tag commit `5045d0056413266e57c625dcd7c365b10e377c52`), core library only: no Mathlib and no other Lake dependency (`lean/lakefile.toml` declares one `[[lean_lib]]`, `Toy`, and no `[[require]]`). Lean's default `Int` `/` and `%` at this version are `Int.ediv`/`Int.emod`; truncating division is written explicitly as `Int.tdiv`/`Int.tmod`.

**Relationship among the subjects in `REPORT.json`.** The Lean toolchain is the checker of every theorem. The Rust Reference, the Ferrocene Language Specification, the Rust 1.91.0 core library and RFC 0560 are the normative and documentation sources that the definitions are meant to mirror (the modeling bridge). The `rustc` nightly is the subject of the execution cross-checks in `support/`. Aeneas, CompCert, Isabelle/HOL, Boute (1992, on truncating, flooring and Euclidean division and remainder) and Dietz et al. are prior art: comparisons, not dependencies.

**Evidence roles.** Every theorem is `execution (Lean kernel check)`: it holds of the Lean definitions. Every statement about Rust or `rustc` is a separate `derived (modeling bridge)` claim, argued from the cited specifications and cross-checked (not proved) by the `rustc` runs, which were observed on one host (`x86_64-unknown-linux-gnu`) with `rustc 1.102.0-nightly (3ef0c22cd 2026-11-11)` in four profiles: debug, `-O`, `-O -C overflow-checks=yes`, and debug with `-C overflow-checks=no`.

## Findings

### Core definitions

Verbatim from `lean/Toy/MachInt/Defs.lean` (doc comments and `Decidable` instances omitted). Every definition has a proved positive and negative example in `lean/Toy/MachInt/Examples.lean` (`ex_*_pos`, `ex_*_neg`), e.g. `ex_inSignedRange_pos : InSignedRange 8 (-128)` and `ex_inSignedRange_neg : ¬ InSignedRange 8 128`, `ex_checkedSRem_neg : checkedSRem (BitVec.intMin 8) (-1#8) = none`.

```lean
def PosWidth (n : Nat) : Prop :=
  0 < n

def WidthLe (m n : Nat) : Prop :=
  m ≤ n

def ShiftInBounds (n k : Nat) : Prop :=
  k < n

def sMinVal (n : Nat) : Int :=
  (BitVec.intMin n).toInt

def sMaxVal (n : Nat) : Int :=
  (BitVec.intMax n).toInt

def InUnsignedRange (n : Nat) (z : Int) : Prop :=
  0 ≤ z ∧ z < ((2 ^ n : Nat) : Int)

def InSignedRange (n : Nat) (z : Int) : Prop :=
  sMinVal n ≤ z ∧ z ≤ sMaxVal n

inductive Outcome (α : Type) : Type
  | ok (val : α)
  | panic
  deriving DecidableEq, Repr

def Outcome.ofOption {α : Type} : Option α → Outcome α
  | some v => .ok v
  | none => .panic

inductive RingExpr : Type
  | var (idx : Nat)
  | lit (val : Int)
  | neg (e : RingExpr)
  | add (e₁ e₂ : RingExpr)
  | sub (e₁ e₂ : RingExpr)
  | mul (e₁ e₂ : RingExpr)
  deriving DecidableEq, Repr

def evalInt (ρ : Nat → Int) : RingExpr → Int
  | .var i => ρ i
  | .lit k => k
  | .neg e => -(evalInt ρ e)
  | .add e₁ e₂ => evalInt ρ e₁ + evalInt ρ e₂
  | .sub e₁ e₂ => evalInt ρ e₁ - evalInt ρ e₂
  | .mul e₁ e₂ => evalInt ρ e₁ * evalInt ρ e₂

def IntRingIdentity (e₁ e₂ : RingExpr) : Prop :=
  ∀ ρ : Nat → Int, evalInt ρ e₁ = evalInt ρ e₂

def evalWrap (n : Nat) (env : Nat → BitVec n) : RingExpr → BitVec n
  | .var i => env i
  | .lit k => BitVec.ofInt n k
  | .neg e => -(evalWrap n env e)
  | .add e₁ e₂ => evalWrap n env e₁ + evalWrap n env e₂
  | .sub e₁ e₂ => evalWrap n env e₁ - evalWrap n env e₂
  | .mul e₁ e₂ => evalWrap n env e₁ * evalWrap n env e₂

def checkedUNeg {n : Nat} (a : BitVec n) : Option (BitVec n) :=
  if a == 0#n then some 0#n else none

def checkedUAdd {n : Nat} (a b : BitVec n) : Option (BitVec n) :=
  if BitVec.uaddOverflow a b then none else some (a + b)

def checkedUSub {n : Nat} (a b : BitVec n) : Option (BitVec n) :=
  if BitVec.usubOverflow a b then none else some (a - b)

def checkedUMul {n : Nat} (a b : BitVec n) : Option (BitVec n) :=
  if BitVec.umulOverflow a b then none else some (a * b)

def checkedSNeg {n : Nat} (a : BitVec n) : Option (BitVec n) :=
  if BitVec.negOverflow a then none else some (-a)

def checkedSAdd {n : Nat} (a b : BitVec n) : Option (BitVec n) :=
  if BitVec.saddOverflow a b then none else some (a + b)

def checkedSSub {n : Nat} (a b : BitVec n) : Option (BitVec n) :=
  if BitVec.ssubOverflow a b then none else some (a - b)

def checkedSMul {n : Nat} (a b : BitVec n) : Option (BitVec n) :=
  if BitVec.smulOverflow a b then none else some (a * b)

def evalCheckedU (n : Nat) (env : Nat → BitVec n) : RingExpr → Option (BitVec n)
  | .var i => some (env i)
  | .lit k => if InUnsignedRange n k then some (BitVec.ofInt n k) else none
  | .neg e => (evalCheckedU n env e).bind checkedUNeg
  | .add e₁ e₂ => (evalCheckedU n env e₁).bind fun v₁ =>
      (evalCheckedU n env e₂).bind fun v₂ => checkedUAdd v₁ v₂
  | .sub e₁ e₂ => (evalCheckedU n env e₁).bind fun v₁ =>
      (evalCheckedU n env e₂).bind fun v₂ => checkedUSub v₁ v₂
  | .mul e₁ e₂ => (evalCheckedU n env e₁).bind fun v₁ =>
      (evalCheckedU n env e₂).bind fun v₂ => checkedUMul v₁ v₂

def evalCheckedS (n : Nat) (env : Nat → BitVec n) : RingExpr → Option (BitVec n)
  | .var i => some (env i)
  | .lit k => if InSignedRange n k then some (BitVec.ofInt n k) else none
  | .neg e => (evalCheckedS n env e).bind checkedSNeg
  | .add e₁ e₂ => (evalCheckedS n env e₁).bind fun v₁ =>
      (evalCheckedS n env e₂).bind fun v₂ => checkedSAdd v₁ v₂
  | .sub e₁ e₂ => (evalCheckedS n env e₁).bind fun v₁ =>
      (evalCheckedS n env e₂).bind fun v₂ => checkedSSub v₁ v₂
  | .mul e₁ e₂ => (evalCheckedS n env e₁).bind fun v₁ =>
      (evalCheckedS n env e₂).bind fun v₂ => checkedSMul v₁ v₂

def evalPlainU (n : Nat) (env : Nat → BitVec n) (e : RingExpr) : Outcome (BitVec n) :=
  Outcome.ofOption (evalCheckedU n env e)

def evalPlainS (n : Nat) (env : Nat → BitVec n) (e : RingExpr) : Outcome (BitVec n) :=
  Outcome.ofOption (evalCheckedS n env e)

def SubexprsInRange (P : Int → Prop) (ρ : Nat → Int) : RingExpr → Prop
  | .var i => P (ρ i)
  | .lit k => P k
  | .neg e => SubexprsInRange P ρ e ∧ P (evalInt ρ (.neg e))
  | .add e₁ e₂ => SubexprsInRange P ρ e₁ ∧ SubexprsInRange P ρ e₂ ∧ P (evalInt ρ (.add e₁ e₂))
  | .sub e₁ e₂ => SubexprsInRange P ρ e₁ ∧ SubexprsInRange P ρ e₂ ∧ P (evalInt ρ (.sub e₁ e₂))
  | .mul e₁ e₂ => SubexprsInRange P ρ e₁ ∧ SubexprsInRange P ρ e₂ ∧ P (evalInt ρ (.mul e₁ e₂))

def Ult {n : Nat} (a b : BitVec n) : Prop :=
  a.ult b = true

def Slt {n : Nat} (a b : BitVec n) : Prop :=
  a.slt b = true

def NoUAddOverflow {n : Nat} (a b : BitVec n) : Prop :=
  BitVec.uaddOverflow a b = false

def NoSAddOverflow {n : Nat} (a b : BitVec n) : Prop :=
  BitVec.saddOverflow a b = false

def NonZeroDiv {n : Nat} (b : BitVec n) : Prop :=
  b ≠ 0#n

def NoSDivOverflow {n : Nat} (a b : BitVec n) : Prop :=
  ¬ (a = BitVec.intMin n ∧ b = -1#n)

def checkedUDiv {n : Nat} (a b : BitVec n) : Option (BitVec n) :=
  if b == 0#n then none else some (a / b)

def checkedURem {n : Nat} (a b : BitVec n) : Option (BitVec n) :=
  if b == 0#n then none else some (a % b)

def checkedSDiv {n : Nat} (a b : BitVec n) : Option (BitVec n) :=
  if b == 0#n || (a == BitVec.intMin n && b == -1#n) then none else some (a.sdiv b)

def checkedSRem {n : Nat} (a b : BitVec n) : Option (BitVec n) :=
  if b == 0#n || (a == BitVec.intMin n && b == -1#n) then none else some (a.srem b)

def sdivEuclid {n : Nat} (a b : BitVec n) : BitVec n :=
  let q := a.sdiv b
  let r := a.srem b
  if r.slt 0#n then
    if (0#n).slt b then q - 1#n else q + 1#n
  else
    q

def sremEuclid {n : Nat} (a b : BitVec n) : BitVec n :=
  let r := a.srem b
  if r.slt 0#n then r + b.abs else r

def checkedSDivEuclid {n : Nat} (a b : BitVec n) : Option (BitVec n) :=
  if b == 0#n || (a == BitVec.intMin n && b == -1#n) then none else some (sdivEuclid a b)

def checkedSRemEuclid {n : Nat} (a b : BitVec n) : Option (BitVec n) :=
  if b == 0#n || (a == BitVec.intMin n && b == -1#n) then none else some (sremEuclid a b)

def wrappingShl {n : Nat} (x : BitVec n) (k : Nat) : BitVec n :=
  x <<< (k % n)

def wrappingUShr {n : Nat} (x : BitVec n) (k : Nat) : BitVec n :=
  x >>> (k % n)

def wrappingSShr {n : Nat} (x : BitVec n) (k : Nat) : BitVec n :=
  x.sshiftRight (k % n)

def checkedShl {n : Nat} (x : BitVec n) (k : Nat) : Option (BitVec n) :=
  if k < n then some (x <<< k) else none

def checkedUShr {n : Nat} (x : BitVec n) (k : Nat) : Option (BitVec n) :=
  if k < n then some (x >>> k) else none

def checkedSShr {n : Nat} (x : BitVec n) (k : Nat) : Option (BitVec n) :=
  if k < n then some (x.sshiftRight k) else none

def castFromUnsigned {n : Nat} (m : Nat) (x : BitVec n) : BitVec m :=
  x.setWidth m

def castFromSigned {n : Nat} (m : Nat) (x : BitVec n) : BitVec m :=
  x.signExtend m

def reinterpretCast {n : Nat} (x : BitVec n) : BitVec n :=
  x
```

One further package-local name occurs in the statements below: the expression `(x₀ + x₁) - x₁` used by the Result 2 counterexamples, verbatim from `lean/Toy/MachInt/Examples.lean`:

```lean
def addSubCancelExpr : RingExpr :=
  .sub (.add (.var 0) (.var 1)) (.var 1)
```

The statements also use these Lean core definitions (verbatim from `src/lean/Init/Data/BitVec/Basic.lean` at the pinned toolchain):

```lean
def intMin (w : Nat) := twoPow w (w - 1)
def intMax (w : Nat) := (twoPow w (w - 1)) - 1
def uaddOverflow {w : Nat} (x y : BitVec w) : Bool := x.toNat + y.toNat ≥ 2 ^ w
def saddOverflow {w : Nat} (x y : BitVec w) : Bool :=
  (x.toInt + y.toInt ≥ 2 ^ (w - 1)) || (x.toInt + y.toInt < - 2 ^ (w - 1))
def usubOverflow {w : Nat} (x y : BitVec w) : Bool := x.toNat < y.toNat
def ssubOverflow {w : Nat} (x y : BitVec w) : Bool :=
  (x.toInt - y.toInt ≥ 2 ^ (w - 1)) || (x.toInt - y.toInt < - 2 ^ (w - 1))
def negOverflow {w : Nat} (x : BitVec w) : Bool :=
  x.toInt == - 2 ^ (w - 1)
def umulOverflow {w : Nat} (x y : BitVec w) : Bool := x.toNat * y.toNat ≥ 2 ^ w
def smulOverflow {w : Nat} (x y : BitVec w) : Bool :=
  (x.toInt * y.toInt ≥ 2 ^ (w - 1)) || (x.toInt * y.toInt < - 2 ^ (w - 1))
```

Notation: `2 ^ n` in `Int.bmod x (2 ^ n)` is a natural number; `↑` is the coercion `Nat → Int`; `x.toNat`/`x.toInt` are the unsigned and two's-complement readings of `x : BitVec n`; `-1#n` is the all-ones vector. Statements below are printed by Lean's pretty-printer from the compiled declarations with namespace `Toy.MachInt` opened; where the specification predicates (`PosWidth`, `WidthLe`, `ShiftInBounds`, `InUnsignedRange`, `InSignedRange`, `sMinVal`, `sMaxVal`, `IntRingIdentity`, `Ult`, `Slt`, `NoUAddOverflow`, `NoSAddOverflow`, `NonZeroDiv`, `NoSDivOverflow`) occur, a second form with them unfolded (`Meta.deltaExpand`) follows. Where the default output would not elaborate back to the theorem's statement because the target type of a coercion `↑` is not fixed by its context, the statement is printed with `set_option pp.coercions.types true`, which shows that type, as in `(↑(2 ^ n) : Int)`.

### Result 1: wrapping evaluation refines integer ring arithmetic modulo 2^n

#### `evalWrap_toNat_eq_emod`

- **Tier:** T0. **Kind:** theorem. **Depth:** shallow.
- **Plain claim:** For every bitwidth n, environment env : Nat → BitVec n, and ring expression e : RingExpr (over +, -, *, unary -, variables, and literals), the unsigned value (evalWrap n env e).toNat equals the mathematical integer evaluation evalInt (fun i => (env i).toNat) e reduced modulo 2^n via Euclidean Int.emod, with no overflow side conditions.
- **Lean statement** (`Toy.MachInt.evalWrap_toNat_eq_emod`):

```lean
theorem evalWrap_toNat_eq_emod :
  ∀ (n : Nat) (env : Nat → BitVec n) (e : RingExpr),
    ↑(evalWrap n env e).toNat = evalInt (fun i => ↑(env i).toNat) e % ↑(2 ^ n)
```

- **Hypothesis ledger:** no hypotheses.
- **Non-vacuity witness:** At n = 8 with env = [200#8, 100#8] and e = (x₀ + x₁) - x₁, evalWrap evaluates to 200#8 and 200 = (200 + 100 - 100) % 256. Lean: `nv_evalWrap_toNat_eq_emod`.
- **Cited companion lemmas** (proved; statements hashed in `audit/statements.json`):

```lean
theorem ce_evalWrap_eq_not_imp_intRingIdentity :
  (∀ (env : Nat → BitVec 8),
      evalWrap 8 env ((RingExpr.lit 64).mul ((RingExpr.lit 4).mul (RingExpr.var 0))) =
        evalWrap 8 env (RingExpr.lit 0)) ∧
    ¬IntRingIdentity ((RingExpr.lit 64).mul ((RingExpr.lit 4).mul (RingExpr.var 0)))
          (RingExpr.lit 0) ∧
      (∀ (env : Nat → BitVec 8),
          evalWrap 8 env ((RingExpr.lit 128).mul ((RingExpr.var 0).add (RingExpr.var 0))) =
            evalWrap 8 env (RingExpr.lit 0)) ∧
        ¬IntRingIdentity ((RingExpr.lit 128).mul ((RingExpr.var 0).add (RingExpr.var 0)))
            (RingExpr.lit 0)
```

- **Prior art:**
  - The Rust Reference (rust-lang/reference commit c9cc32825b03fc206d9c6fe73e9ca6a2f3576d6c), src/expressions/operator-expr.md ([expr.operator.int-overflow.*]) (wrapping_add/sub/mul/neg modulo 2^n; behavior of plain operators when overflow checks are off is implementation-defined per behavior-not-considered-unsafe.md).
  - The Rust Reference (rust-lang/reference commit c9cc32825b03fc206d9c6fe73e9ca6a2f3576d6c), src/behavior-not-considered-unsafe.md (L14: non-debug overflow may panic or wrap at implementation's discretion)
  - Ferrocene Language Specification (rust-lang/fls commit bca860e8dab52715effdd49a792347b262f5e539), src/expressions.rst ('Arithmetic Overflow')
  - Rust RFC 0560: Integer Overflow (initially written by Gábor Lehel; edited by Nicholas Matsakis), https://github.com/rust-lang/rfcs/blob/f17e8623ee2e2854570dcdb936a9f4ab08c0fcd4/text/0560-integer-overflow.md (distinguishes intentional wrapping arithmetic via WrappingOps from overflow-as-error).
  - Lean 4.34.1 core library (leanprover/lean4:v4.34.1, commit 5045d0056413266e57c625dcd7c365b10e377c52), Init/Data/BitVec/Lemmas.lean (toNat_add, toNat_sub, toNat_mul, ofInt_add, ofInt_mul, ofInt_neg, toNat_ofInt, toInt_ofInt, ofInt_toInt), Init/Data/BitVec/Bootstrap.lean (toNat_neg) and Init/GrindInstances/Ring/BitVec.lean (Lean.Grind.CommRing (BitVec w), IsCharP (BitVec w) (2 ^ w)).
  - CompCert C verified compiler (AbsInt/CompCert commit 2685140bf72c959446981fb99b5e44a8975021bc), lib/Integers.v (add_signed, mul_signed: modular ring arithmetic on machine words).
- **Design question:** Identifies a fragment of machine-integer arithmetic (ring expressions under wrapping semantics) that refines modular mathematical integer arithmetic with zero overflow side conditions. Maximality is not claimed: other operations (for example unsigned bitwise operations) also need no side conditions.
- **Basis:** execution (Lean kernel check) of `evalWrap_toNat_eq_emod` and every Lean name listed above.
- **Basis:** derived (modeling bridge) for the Rust reading: `evalWrap` interprets `+`, `-`, `*` and unary `-` as Lean `BitVec n` operations, which are arithmetic modulo `2^n`. Rust's `wrapping_add`/`wrapping_sub`/`wrapping_mul`/`wrapping_neg` and `Wrapping<T>` are specified as modular arithmetic (Rust Reference `[expr.operator.int-overflow]`, core library documentation), and `rustc` additionally wraps plain `+`, `-`, `*` when overflow checks are disabled (implementation behaviour; the Reference also permits a panic). Reading a `u<n>`/`i<n>` value through `toNat`/`toInt` is the standard unsigned/two's-complement interpretation of its bit pattern, so for `n` in {8, 16, 32, 64, 128} these theorems describe expressions built from the explicitly wrapping operations. Execution cross-check (not proof): `u8::MAX.wrapping_add(1) = 0`, `i8::MAX.wrapping_add(1) = -128`, and `64*(4*x) = 0` for all `u8`/`i8` `x` in all four `rustc` profiles (`support/rustc_checks_output.txt`).
- **Non-claims:** package-wide N1, N2, N3, N5 (stated in full under Boundaries), and:
  - Does not claim that checked or plain overflow-checked evaluation agrees with wrapping evaluation; intermediate overflow causes checked evaluation to return none and plain evaluation to panic (see ce_checked_add_sub_intermediate_overflow).
  - Does not apply to division (/ or %), remainder, shifts (<< or >>), or ordering comparisons (<); see Results 3, 4, and 5.
  - Only unconditional identities transfer. An equation proved over `Int` using hypotheses about the variables (ranges, signs, nonzero divisors) need not hold in wrapping arithmetic. Conversely, an equation that holds in wrapping arithmetic need not hold over `Int` (e.g. `64 * (4 * x) = 0` on `u8`/`i8` or `128 * (x + x) = 0` on `u8`; see `ce_evalWrap_eq_not_imp_intRingIdentity`).

#### `evalWrap_toInt_eq_bmod`

- **Tier:** T0. **Kind:** theorem. **Depth:** shallow.
- **Plain claim:** For every bitwidth n, environment env : Nat → BitVec n, and ring expression e : RingExpr, the signed two's-complement value (evalWrap n env e).toInt equals the mathematical integer evaluation evalInt (fun i => (env i).toInt) e reduced via balanced modulo Int.bmod · (2^n), with no overflow side conditions.
- **Lean statement** (`Toy.MachInt.evalWrap_toInt_eq_bmod`):

```lean
theorem evalWrap_toInt_eq_bmod :
  ∀ (n : Nat) (env : Nat → BitVec n) (e : RingExpr),
    (evalWrap n env e).toInt = (evalInt (fun i => (env i).toInt) e).bmod (2 ^ n)
```

- **Hypothesis ledger:** no hypotheses.
- **Non-vacuity witness:** At n = 8 with env = [100#8, 50#8] and e = (x₀ + x₁) - x₁, (evalWrap 8 env e).toInt = 100 = Int.bmod (100 + 50 - 50) 256. Lean: `nv_evalWrap_toInt_eq_bmod`.
- **Prior art:**
  - The Rust Reference (rust-lang/reference commit c9cc32825b03fc206d9c6fe73e9ca6a2f3576d6c), src/expressions/operator-expr.md ([expr.operator.int-overflow.*]) (two's complement representation for signed fixed-width integers).
  - The Rust Reference (rust-lang/reference commit c9cc32825b03fc206d9c6fe73e9ca6a2f3576d6c), src/behavior-not-considered-unsafe.md (L14: non-debug overflow may panic or wrap at implementation's discretion)
  - Ferrocene Language Specification (rust-lang/fls commit bca860e8dab52715effdd49a792347b262f5e539), src/expressions.rst ('Arithmetic Overflow')
  - Lean 4.34.1 core library (leanprover/lean4:v4.34.1, commit 5045d0056413266e57c625dcd7c365b10e377c52), Init/Data/Int/DivMod/Basic.lean, Init/Data/BitVec/Lemmas.lean (toInt_add, toInt_sub, toInt_mul, toInt_neg in terms of Int.bmod), and Init/GrindInstances/Ring/BitVec.lean (CommRing (BitVec w)).
- **Design question:** Gives the exact signed-integer modular refinement invariant for two's-complement wrapping arithmetic, showing balanced modulo Int.bmod plays the role that Int.emod plays for unsigned arithmetic.
- **Basis:** execution (Lean kernel check) of `evalWrap_toInt_eq_bmod` and every Lean name listed above.
- **Basis:** derived (modeling bridge) for the Rust reading: `evalWrap` interprets `+`, `-`, `*` and unary `-` as Lean `BitVec n` operations, which are arithmetic modulo `2^n`. Rust's `wrapping_add`/`wrapping_sub`/`wrapping_mul`/`wrapping_neg` and `Wrapping<T>` are specified as modular arithmetic (Rust Reference `[expr.operator.int-overflow]`, core library documentation), and `rustc` additionally wraps plain `+`, `-`, `*` when overflow checks are disabled (implementation behaviour; the Reference also permits a panic). Reading a `u<n>`/`i<n>` value through `toNat`/`toInt` is the standard unsigned/two's-complement interpretation of its bit pattern, so for `n` in {8, 16, 32, 64, 128} these theorems describe expressions built from the explicitly wrapping operations. Execution cross-check (not proof): `u8::MAX.wrapping_add(1) = 0`, `i8::MAX.wrapping_add(1) = -128`, and `64*(4*x) = 0` for all `u8`/`i8` `x` in all four `rustc` profiles (`support/rustc_checks_output.txt`).
- **Non-claims:** package-wide N1, N2, N3, N5 (stated in full under Boundaries), and:
  - Does not claim that signed wrapping evaluation equals unreduced mathematical Int evaluation when intermediate or final results fall outside InSignedRange n.
  - Does not apply to C/C++ signed integer arithmetic, where signed overflow is undefined behavior rather than two's-complement wrapping.
  - Does not apply to division, remainder, shifts, or signed ordering (<).

#### `evalWrap_eq_of_intRingIdentity`

- **Tier:** T0. **Kind:** theorem. **Depth:** shallow.
- **Plain claim:** For every bitwidth n, environment env : Nat → BitVec n, and pair of expressions e₁ e₂ : RingExpr satisfying IntRingIdentity e₁ e₂ (agreement under every mathematical valuation ρ : Nat → Int), their wrapping evaluations coincide: evalWrap n env e₁ = evalWrap n env e₂, with no overflow side conditions.
- **Lean statement** (`Toy.MachInt.evalWrap_eq_of_intRingIdentity`):

```lean
theorem evalWrap_eq_of_intRingIdentity :
  ∀ (n : Nat) (env : Nat → BitVec n) {e₁ e₂ : RingExpr},
    IntRingIdentity e₁ e₂ → evalWrap n env e₁ = evalWrap n env e₂
-- with the specification predicates unfolded:
  ∀ (n : Nat) (env : Nat → BitVec n) {e₁ e₂ : RingExpr},
    (∀ (ρ : Nat → Int), evalInt ρ e₁ = evalInt ρ e₂) → evalWrap n env e₁ = evalWrap n env e₂
```

- **Hypothesis ledger:**
  - `hid : IntRingIdentity e₁ e₂` (tight: counterexample `ce_evalWrap_eq_drop_intRingIdentity`). Ensures e₁ and e₂ denote the same polynomial function over Int, hence agree modulo 2^n under the canonical ring homomorphism Int → BitVec n.

  Counterexample `ce_evalWrap_eq_drop_intRingIdentity` (all other hypotheses hold and the conclusion fails):

```lean
theorem ce_evalWrap_eq_drop_intRingIdentity :
  ∃ n env e₁ e₂, ¬IntRingIdentity e₁ e₂ ∧ evalWrap n env e₁ ≠ evalWrap n env e₂
```

- **Non-vacuity witness:** e₁ = (x₀ + x₁) - x₁ and e₂ = x₀ satisfy IntRingIdentity e₁ e₂ and agree under evalWrap 8 [200#8, 100#8]. Lean: `nv_evalWrap_eq_of_intRingIdentity`.
- **Cited companion lemmas** (proved; statements hashed in `audit/statements.json`):

```lean
theorem ce_evalWrap_eq_not_imp_intRingIdentity :
  (∀ (env : Nat → BitVec 8),
      evalWrap 8 env ((RingExpr.lit 64).mul ((RingExpr.lit 4).mul (RingExpr.var 0))) =
        evalWrap 8 env (RingExpr.lit 0)) ∧
    ¬IntRingIdentity ((RingExpr.lit 64).mul ((RingExpr.lit 4).mul (RingExpr.var 0)))
          (RingExpr.lit 0) ∧
      (∀ (env : Nat → BitVec 8),
          evalWrap 8 env ((RingExpr.lit 128).mul ((RingExpr.var 0).add (RingExpr.var 0))) =
            evalWrap 8 env (RingExpr.lit 0)) ∧
        ¬IntRingIdentity ((RingExpr.lit 128).mul ((RingExpr.var 0).add (RingExpr.var 0)))
            (RingExpr.lit 0)
```

- **Prior art:**
  - Lean 4.34.1 core library (leanprover/lean4:v4.34.1, commit 5045d0056413266e57c625dcd7c365b10e377c52), Init/GrindInstances/Ring/BitVec.lean (L21 CommRing (BitVec w), L48 IsCharP (BitVec w) (2 ^ w), allowing `grind` to prove polynomial identities over BitVec w for symbolic w) and Init/Data/BitVec/Lemmas.lean (ofInt_add, ofInt_mul, ofInt_neg).
  - Rust RFC 0560: Integer Overflow (initially written by Gábor Lehel; edited by Nicholas Matsakis), https://github.com/rust-lang/rfcs/blob/f17e8623ee2e2854570dcdb936a9f4ab08c0fcd4/text/0560-integer-overflow.md
  - CompCert C verified compiler (AbsInt/CompCert commit 2685140bf72c959446981fb99b5e44a8975021bc), lib/Integers.v (modular ring homomorphism on 32/64-bit words).
- **Design question:** Answers which algebraic identities transfer from mathematical integers to fixed-width integers with zero side conditions: every pure ring identity transfers under wrapping semantics.
- **Basis:** execution (Lean kernel check) of `evalWrap_eq_of_intRingIdentity` and every Lean name listed above.
- **Basis:** derived (modeling bridge) for the Rust reading: `evalWrap` interprets `+`, `-`, `*` and unary `-` as Lean `BitVec n` operations, which are arithmetic modulo `2^n`. Rust's `wrapping_add`/`wrapping_sub`/`wrapping_mul`/`wrapping_neg` and `Wrapping<T>` are specified as modular arithmetic (Rust Reference `[expr.operator.int-overflow]`, core library documentation), and `rustc` additionally wraps plain `+`, `-`, `*` when overflow checks are disabled (implementation behaviour; the Reference also permits a panic). Reading a `u<n>`/`i<n>` value through `toNat`/`toInt` is the standard unsigned/two's-complement interpretation of its bit pattern, so for `n` in {8, 16, 32, 64, 128} these theorems describe expressions built from the explicitly wrapping operations. Execution cross-check (not proof): `u8::MAX.wrapping_add(1) = 0`, `i8::MAX.wrapping_add(1) = -128`, and `64*(4*x) = 0` for all `u8`/`i8` `x` in all four `rustc` profiles (`support/rustc_checks_output.txt`).
- **Non-claims:** package-wide N1, N2, N3, N5 (stated in full under Boundaries), and:
  - Does not transfer identities under checked or plain overflow-checked evaluation: (a + b) - b panics on overflow even when a is in range (see ce_checked_add_sub_intermediate_overflow).
  - Only unconditional identities transfer. An equation proved over `Int` using hypotheses about the variables (ranges, signs, nonzero divisors) need not hold in wrapping arithmetic. Conversely, an equation that holds in wrapping arithmetic need not hold over `Int` (e.g. `64 * (4 * x) = 0` on `u8`/`i8` or `128 * (x + x) = 0` on `u8`; see `ce_evalWrap_eq_not_imp_intRingIdentity`).
  - Does not apply to expressions containing division, remainder, shifts, or comparisons.

### Result 2: checked evaluation is sound, and succeeds exactly when every subexpression is in range

#### `evalCheckedU_sound`

- **Tier:** T0. **Kind:** theorem. **Depth:** shallow.
- **Plain claim:** For every bitwidth n, environment env : Nat → BitVec n, ring expression e : RingExpr, and result v : BitVec n, if checked unsigned evaluation returns some v (evalCheckedU n env e = some v, which by definition of evalPlainU coincides with evalPlainU n env e = Outcome.ok v), then (v.toNat : Int) equals the unreduced mathematical integer evaluation evalInt (fun i => (env i).toNat) e.
- **Lean statement** (`Toy.MachInt.evalCheckedU_sound`):

```lean
theorem evalCheckedU_sound :
  ∀ (n : Nat) (env : Nat → BitVec n) (e : RingExpr) (v : BitVec n),
    evalCheckedU n env e = some v → ↑v.toNat = evalInt (fun i => ↑(env i).toNat) e
```

- **Hypothesis ledger:**
  - `hsome : evalCheckedU n env e = some v` (tight: counterexample `ce_evalCheckedU_sound_drop_some`). Guarantees that every literal and intermediate unsigned operation succeeded without wrapping, making bitvector evaluation exact in Nat/Int.

  Counterexample `ce_evalCheckedU_sound_drop_some` (all other hypotheses hold and the conclusion fails):

```lean
theorem ce_evalCheckedU_sound_drop_some :
  have env := fun x =>
    match x with
    | 0 => 200#8
    | x => 100#8;
  have e := (RingExpr.var 0).add (RingExpr.var 1);
  evalCheckedU 8 env e = none ∧ ↑(evalWrap 8 env e).toNat ≠ evalInt (fun i => ↑(env i).toNat) e
```

- **Non-vacuity witness:** At n = 8, env = [200#8, 55#8], and e = (x₀ + x₁) - x₁, evalCheckedU returns some 200#8 and 200 = evalInt [200, 55] e. Lean: `nv_evalCheckedU_sound`.
- **Prior art:**
  - The Rust Reference (rust-lang/reference commit c9cc32825b03fc206d9c6fe73e9ca6a2f3576d6c), src/expressions/operator-expr.md ([expr.operator.int-overflow.*])
  - The Rust Reference (rust-lang/reference commit c9cc32825b03fc206d9c6fe73e9ca6a2f3576d6c), src/behavior-not-considered-unsafe.md (L14: non-debug overflow may panic or wrap at implementation's discretion)
  - The Rust Reference (rust-lang/reference commit c9cc32825b03fc206d9c6fe73e9ca6a2f3576d6c), src/tokens.md (L518) and src/expressions/literal-expr.md (L426-429: overflowing_literals lint, negation of literal)
  - Ferrocene Language Specification (rust-lang/fls commit bca860e8dab52715effdd49a792347b262f5e539), src/expressions.rst ('Arithmetic Overflow')
  - Rust 1.91.0 core library (rust-lang/rust tag 1.91.0, commit f8297e351a40c1439a467bbbb6879088047f50b3), library/core/src/num/uint_macros.rs (checked_add, checked_sub, checked_mul, checked_neg; https://doc.rust-lang.org/1.91.0/core/primitive.u32.html#method.checked_add).
  - Lean 4.34.1 core library (leanprover/lean4:v4.34.1, commit 5045d0056413266e57c625dcd7c365b10e377c52), Init/Data/BitVec/Lemmas.lean (toNat_add_of_lt, toNat_sub_of_le, toNat_mul_of_lt).
- **Design question:** Justifies backward/value-soundness in verifiers (`execution (Lean kernel check)` for the model; `derived (modeling bridge)` connecting `evalPlainU = Outcome.ok v` to Rust plain unsigned `+`, `-`, `*` under overflow checks): once checked evaluation succeeds, the machine value equals its mathematical integer evaluation without wraparound.
- **Basis:** execution (Lean kernel check) of `evalCheckedU_sound` and every Lean name listed above.
- **Basis:** derived (modeling bridge) for the Rust reading: `evalCheckedU`/`evalCheckedS` model chains of `checked_add`/`checked_sub`/`checked_mul`/`checked_neg` that propagate `None`, and `evalPlainU`/`evalPlainS` (defined as `Outcome.ofOption` of the checked evaluators) model plain operators under overflow checks, with `none`/`Outcome.panic` standing for a panic. The core library documents `checked_*` as returning `None` exactly when the mathematical result is not representable, which is what Lean core's `uaddOverflow`, `usubOverflow`, `umulOverflow`, `saddOverflow`, `ssubOverflow`, `smulOverflow` and `negOverflow` flags decide. `.lit k` is a typed constant, not a Rust literal token (out-of-range literal tokens are compile-time errors under the deny-by-default `overflowing_literals` lint, and unary `-` on unsigned types is error `E0600`). Execution cross-check (not proof): `(200u8 + 100) - 100` and `(100i8 + 50) - 50` panic in the two overflow-checked profiles, and `200u8.checked_add(100)` and `100i8.checked_add(50)` return `None` in all four.
- **Non-claims:** package-wide N1, N2, N3, N5 (stated in full under Boundaries), and:
  - Does not assert that evalCheckedU succeeds whenever only the final value evalInt ... e is in InUnsignedRange n; intermediate overflow still returns none (see ce_checked_add_sub_intermediate_overflow).
  - Does not model division, remainder, or shifts (see Results 4 and 5).
  - `.lit k` stands for a typed constant value, not a Rust literal token. In Rust an out-of-range literal is a compile-time error (deny-by-default `overflowing_literals` lint) or is truncated, never a runtime panic. Unary minus applied directly to a literal never overflows (`-128_i8 == i8::MIN`). Unary minus does not exist on unsigned types. The model's `none` results for these cases have no Rust counterpart, and `SubexprsInRange` over-approximates the obligation for them.

#### `evalCheckedU_complete`

- **Tier:** T0. **Kind:** theorem. **Depth:** shallow.
- **Plain claim:** For every bitwidth n, environment env : Nat → BitVec n, and ring expression e : RingExpr, if every subexpression of e (variables, typed constants, and every compound node) evaluates inside InUnsignedRange n under SubexprsInRange (InUnsignedRange n) (fun i => (env i).toNat) e, then evalCheckedU n env e returns some (evalWrap n env e).
- **Lean statement** (`Toy.MachInt.evalCheckedU_complete`):

```lean
theorem evalCheckedU_complete :
  ∀ (n : Nat) (env : Nat → BitVec n) (e : RingExpr),
    SubexprsInRange (InUnsignedRange n) (fun i => ↑(env i).toNat) e →
      evalCheckedU n env e = some (evalWrap n env e)
-- with the specification predicates unfolded:
  ∀ (n : Nat) (env : Nat → BitVec n) (e : RingExpr),
    SubexprsInRange (fun z => 0 ≤ z ∧ z < ↑(2 ^ n)) (fun i => ↑(env i).toNat) e →
      evalCheckedU n env e = some (evalWrap n env e)
```

- **Hypothesis ledger:**
  - `hrange : SubexprsInRange (InUnsignedRange n) (fun i => (env i).toNat) e` (tight: counterexample `ce_checkedU_add_sub_intermediate_overflow`). Rules out out-of-range literals and intermediate subexpression overflows even when the root expression value lies in InUnsignedRange n.

  Counterexample `ce_checkedU_add_sub_intermediate_overflow` (all other hypotheses hold and the conclusion fails):

```lean
theorem ce_checkedU_add_sub_intermediate_overflow :
  have env := fun x =>
    match x with
    | 0 => 200#8
    | x => 100#8;
  have ρ := fun i => ↑(env i).toNat;
  InUnsignedRange 8 (evalInt ρ addSubCancelExpr) ∧
    ¬SubexprsInRange (InUnsignedRange 8) ρ addSubCancelExpr ∧
      evalCheckedU 8 env addSubCancelExpr ≠ some (evalWrap 8 env addSubCancelExpr)
```

- **Non-vacuity witness:** At n = 8, env = [200#8, 55#8], and e = (x₀ + x₁) - x₁, all subexpressions (200, 55, 255, 200) lie in [0, 256) and evalCheckedU returns some 200#8. Lean: `nv_evalCheckedU_complete`.
- **Prior art:**
  - The Rust Reference (rust-lang/reference commit c9cc32825b03fc206d9c6fe73e9ca6a2f3576d6c), src/expressions/operator-expr.md ([expr.operator.int-overflow.*]).
  - Rust RFC 0560: Integer Overflow (initially written by Gábor Lehel; edited by Nicholas Matsakis), https://github.com/rust-lang/rfcs/blob/f17e8623ee2e2854570dcdb936a9f4ab08c0fcd4/text/0560-integer-overflow.md.
- **Design question:** Specifies a sufficient per-subexpression range obligation for panic-free checked unsigned ring evaluation (also shown necessary in the model by `evalCheckedU_isSome_iff_subexprsInRange`).
- **Basis:** execution (Lean kernel check) of `evalCheckedU_complete` and every Lean name listed above.
- **Basis:** derived (modeling bridge) for the Rust reading: `evalCheckedU`/`evalCheckedS` model chains of `checked_add`/`checked_sub`/`checked_mul`/`checked_neg` that propagate `None`, and `evalPlainU`/`evalPlainS` (defined as `Outcome.ofOption` of the checked evaluators) model plain operators under overflow checks, with `none`/`Outcome.panic` standing for a panic. The core library documents `checked_*` as returning `None` exactly when the mathematical result is not representable, which is what Lean core's `uaddOverflow`, `usubOverflow`, `umulOverflow`, `saddOverflow`, `ssubOverflow`, `smulOverflow` and `negOverflow` flags decide. `.lit k` is a typed constant, not a Rust literal token (out-of-range literal tokens are compile-time errors under the deny-by-default `overflowing_literals` lint, and unary `-` on unsigned types is error `E0600`). Execution cross-check (not proof): `(200u8 + 100) - 100` and `(100i8 + 50) - 50` panic in the two overflow-checked profiles, and `200u8.checked_add(100)` and `100i8.checked_add(50)` return `None` in all four.
- **Non-claims:** package-wide N1, N2, N3, N5 (stated in full under Boundaries), and:
  - Does not weaken SubexprsInRange to checking only the root value InUnsignedRange n (evalInt ... e); (200u8 + 100u8) - 100u8 refutes that weakening (ce_checkedU_add_sub_intermediate_overflow).
  - Does not assert that SubexprsInRange holds without verifier overflow proof obligations.
  - `.lit k` stands for a typed constant value, not a Rust literal token. In Rust an out-of-range literal is a compile-time error (deny-by-default `overflowing_literals` lint) or is truncated, never a runtime panic. Unary minus applied directly to a literal never overflows (`-128_i8 == i8::MIN`). Unary minus does not exist on unsigned types. The model's `none` results for these cases have no Rust counterpart, and `SubexprsInRange` over-approximates the obligation for them.

#### `evalCheckedU_isSome_iff_subexprsInRange`

- **Tier:** T0. **Kind:** characterization. **Depth:** shallow.
- **Plain claim:** For every bitwidth n, environment env : Nat → BitVec n, and ring expression e : RingExpr, checked unsigned evaluation succeeds ((evalCheckedU n env e).isSome = true) if and only if SubexprsInRange (InUnsignedRange n) (fun i => (env i).toNat) e holds.
- **Lean statement** (`Toy.MachInt.evalCheckedU_isSome_iff_subexprsInRange`):

```lean
theorem evalCheckedU_isSome_iff_subexprsInRange :
  ∀ (n : Nat) (env : Nat → BitVec n) (e : RingExpr),
    (evalCheckedU n env e).isSome = true ↔
      SubexprsInRange (InUnsignedRange n) (fun i => ↑(env i).toNat) e
-- with the specification predicates unfolded:
  ∀ (n : Nat) (env : Nat → BitVec n) (e : RingExpr),
    (evalCheckedU n env e).isSome = true ↔
      SubexprsInRange (fun z => 0 ≤ z ∧ z < ↑(2 ^ n)) (fun i => ↑(env i).toNat) e
```

- **Hypothesis ledger:** no hypotheses.
- **Non-vacuity witness:** At n = 8 on (x₀ + x₁) - x₁: env = [200#8, 55#8] satisfies SubexprsInRange (InUnsignedRange 8) and gives isSome = true, while env = [200#8, 100#8] violates SubexprsInRange at the sum and gives isSome = false. Lean: `nv_evalCheckedU_isSome_iff_subexprsInRange`.
- **Prior art:**
  - The Rust Reference (rust-lang/reference commit c9cc32825b03fc206d9c6fe73e9ca6a2f3576d6c), src/expressions/operator-expr.md ([expr.operator.int-overflow.*])
  - The Rust Reference (rust-lang/reference commit c9cc32825b03fc206d9c6fe73e9ca6a2f3576d6c), src/behavior-not-considered-unsafe.md (L14: non-debug overflow may panic or wrap at implementation's discretion)
  - The Rust Reference (rust-lang/reference commit c9cc32825b03fc206d9c6fe73e9ca6a2f3576d6c), src/tokens.md (L518) and src/expressions/literal-expr.md (L426-429: overflowing_literals lint, negation of literal)
  - Ferrocene Language Specification (rust-lang/fls commit bca860e8dab52715effdd49a792347b262f5e539), src/expressions.rst ('Arithmetic Overflow')
  - Rust 1.91.0 core library (rust-lang/rust tag 1.91.0, commit f8297e351a40c1439a467bbbb6879088047f50b3), library/core/src/num/uint_macros.rs (checked_add, checked_sub, checked_mul, checked_neg).
- **Design question:** Characterizes the exact necessary and sufficient per-subexpression range obligation for checked unsigned ring evaluation in the model.
- **Basis:** execution (Lean kernel check) of `evalCheckedU_isSome_iff_subexprsInRange` and every Lean name listed above.
- **Basis:** derived (modeling bridge) for the Rust reading: `evalCheckedU`/`evalCheckedS` model chains of `checked_add`/`checked_sub`/`checked_mul`/`checked_neg` that propagate `None`, and `evalPlainU`/`evalPlainS` (defined as `Outcome.ofOption` of the checked evaluators) model plain operators under overflow checks, with `none`/`Outcome.panic` standing for a panic. The core library documents `checked_*` as returning `None` exactly when the mathematical result is not representable, which is what Lean core's `uaddOverflow`, `usubOverflow`, `umulOverflow`, `saddOverflow`, `ssubOverflow`, `smulOverflow` and `negOverflow` flags decide. `.lit k` is a typed constant, not a Rust literal token (out-of-range literal tokens are compile-time errors under the deny-by-default `overflowing_literals` lint, and unary `-` on unsigned types is error `E0600`). Execution cross-check (not proof): `(200u8 + 100) - 100` and `(100i8 + 50) - 50` panic in the two overflow-checked profiles, and `200u8.checked_add(100)` and `100i8.checked_add(50)` return `None` in all four.
- **Non-claims:** package-wide N1, N2, N3, N5 (stated in full under Boundaries), and:
  - Does not claim that failing `SubexprsInRange` implies the final expression value is out of range (`ce_checkedU_add_sub_intermediate_overflow`).
  - `.lit k` stands for a typed constant value, not a Rust literal token. In Rust an out-of-range literal is a compile-time error (deny-by-default `overflowing_literals` lint) or is truncated, never a runtime panic. Unary minus applied directly to a literal never overflows (`-128_i8 == i8::MIN`). Unary minus does not exist on unsigned types. The model's `none` results for these cases have no Rust counterpart, and `SubexprsInRange` over-approximates the obligation for them.

#### `evalCheckedS_sound`

- **Tier:** T0. **Kind:** theorem. **Depth:** shallow.
- **Plain claim:** For every bitwidth n, environment env : Nat → BitVec n, ring expression e : RingExpr, and result v : BitVec n, if checked signed evaluation returns some v (evalCheckedS n env e = some v, definitionally evalPlainS n env e = Outcome.ok v), then v.toInt equals the unreduced mathematical integer evaluation evalInt (fun i => (env i).toInt) e.
- **Lean statement** (`Toy.MachInt.evalCheckedS_sound`):

```lean
theorem evalCheckedS_sound :
  ∀ (n : Nat) (env : Nat → BitVec n) (e : RingExpr) (v : BitVec n),
    evalCheckedS n env e = some v → v.toInt = evalInt (fun i => (env i).toInt) e
```

- **Hypothesis ledger:**
  - `hsome : evalCheckedS n env e = some v` (tight: counterexample `ce_evalCheckedS_sound_drop_some`). Guarantees that every literal and intermediate signed operation stays in [sMinVal n, sMaxVal n] without two's-complement wraparound.

  Counterexample `ce_evalCheckedS_sound_drop_some` (all other hypotheses hold and the conclusion fails):

```lean
theorem ce_evalCheckedS_sound_drop_some :
  have env := fun x =>
    match x with
    | 0 => 100#8
    | x => 50#8;
  have e := (RingExpr.var 0).add (RingExpr.var 1);
  evalCheckedS 8 env e = none ∧ (evalWrap 8 env e).toInt ≠ evalInt (fun i => (env i).toInt) e
```

- **Non-vacuity witness:** At n = 8, env = [100#8, 27#8], and e = (x₀ + x₁) - x₁, evalCheckedS returns some 100#8 and (100#8).toInt = 100 = evalInt [100, 27] e. Lean: `nv_evalCheckedS_sound`.
- **Prior art:**
  - The Rust Reference (rust-lang/reference commit c9cc32825b03fc206d9c6fe73e9ca6a2f3576d6c), src/expressions/operator-expr.md ([expr.operator.int-overflow.*])
  - The Rust Reference (rust-lang/reference commit c9cc32825b03fc206d9c6fe73e9ca6a2f3576d6c), src/behavior-not-considered-unsafe.md (L14: non-debug overflow may panic or wrap at implementation's discretion)
  - The Rust Reference (rust-lang/reference commit c9cc32825b03fc206d9c6fe73e9ca6a2f3576d6c), src/tokens.md (L518) and src/expressions/literal-expr.md (L426-429: overflowing_literals lint, negation of literal)
  - Ferrocene Language Specification (rust-lang/fls commit bca860e8dab52715effdd49a792347b262f5e539), src/expressions.rst ('Arithmetic Overflow')
  - Rust 1.91.0 core library (rust-lang/rust tag 1.91.0, commit f8297e351a40c1439a467bbbb6879088047f50b3), library/core/src/num/int_macros.rs (checked_add, checked_sub, checked_mul, checked_neg; https://doc.rust-lang.org/1.91.0/core/primitive.i32.html#method.checked_add).
- **Design question:** Justifies signed integer translation soundness (`execution (Lean kernel check)` for the model; `derived (modeling bridge)` connecting `evalPlainS` to Rust plain signed `+`, `-`, `*`, and non-literal unary `-` under overflow checks).
- **Basis:** execution (Lean kernel check) of `evalCheckedS_sound` and every Lean name listed above.
- **Basis:** derived (modeling bridge) for the Rust reading: `evalCheckedU`/`evalCheckedS` model chains of `checked_add`/`checked_sub`/`checked_mul`/`checked_neg` that propagate `None`, and `evalPlainU`/`evalPlainS` (defined as `Outcome.ofOption` of the checked evaluators) model plain operators under overflow checks, with `none`/`Outcome.panic` standing for a panic. The core library documents `checked_*` as returning `None` exactly when the mathematical result is not representable, which is what Lean core's `uaddOverflow`, `usubOverflow`, `umulOverflow`, `saddOverflow`, `ssubOverflow`, `smulOverflow` and `negOverflow` flags decide. `.lit k` is a typed constant, not a Rust literal token (out-of-range literal tokens are compile-time errors under the deny-by-default `overflowing_literals` lint, and unary `-` on unsigned types is error `E0600`). Execution cross-check (not proof): `(200u8 + 100) - 100` and `(100i8 + 50) - 50` panic in the two overflow-checked profiles, and `200u8.checked_add(100)` and `100i8.checked_add(50)` return `None` in all four.
- **Non-claims:** package-wide N1, N2, N3, N5 (stated in full under Boundaries), and:
  - Does not assert that evalCheckedS succeeds when only the final result is in InSignedRange n.
  - `.lit k` stands for a typed constant value, not a Rust literal token. In Rust an out-of-range literal is a compile-time error (deny-by-default `overflowing_literals` lint) or is truncated, never a runtime panic. Unary minus applied directly to a literal never overflows (`-128_i8 == i8::MIN`). Unary minus does not exist on unsigned types. The model's `none` results for these cases have no Rust counterpart, and `SubexprsInRange` over-approximates the obligation for them.

#### `evalCheckedS_complete`

- **Tier:** T0. **Kind:** theorem. **Depth:** shallow.
- **Plain claim:** For every bitwidth n, environment env : Nat → BitVec n, and ring expression e : RingExpr, if every subexpression of e evaluates inside InSignedRange n under SubexprsInRange (InSignedRange n) (fun i => (env i).toInt) e, then evalCheckedS n env e returns some (evalWrap n env e).
- **Lean statement** (`Toy.MachInt.evalCheckedS_complete`):

```lean
theorem evalCheckedS_complete :
  ∀ (n : Nat) (env : Nat → BitVec n) (e : RingExpr),
    SubexprsInRange (InSignedRange n) (fun i => (env i).toInt) e →
      evalCheckedS n env e = some (evalWrap n env e)
-- with the specification predicates unfolded:
  ∀ (n : Nat) (env : Nat → BitVec n) (e : RingExpr),
    SubexprsInRange (fun z => (BitVec.intMin n).toInt ≤ z ∧ z ≤ (BitVec.intMax n).toInt)
        (fun i => (env i).toInt) e →
      evalCheckedS n env e = some (evalWrap n env e)
```

- **Hypothesis ledger:**
  - `hrange : SubexprsInRange (InSignedRange n) (fun i => (env i).toInt) e` (tight: counterexample `ce_checkedS_add_sub_intermediate_overflow`). Rules out out-of-range literals and intermediate signed overflows (including negating MIN) even when the root expression lies in InSignedRange n.

  Counterexample `ce_checkedS_add_sub_intermediate_overflow` (all other hypotheses hold and the conclusion fails):

```lean
theorem ce_checkedS_add_sub_intermediate_overflow :
  have env := fun x =>
    match x with
    | 0 => 100#8
    | x => 50#8;
  have ρ := fun i => (env i).toInt;
  InSignedRange 8 (evalInt ρ addSubCancelExpr) ∧
    ¬SubexprsInRange (InSignedRange 8) ρ addSubCancelExpr ∧
      evalCheckedS 8 env addSubCancelExpr ≠ some (evalWrap 8 env addSubCancelExpr)
```

- **Non-vacuity witness:** At n = 8, env = [100#8, 27#8], and e = (x₀ + x₁) - x₁, all subexpressions (100, 27, 127, 100) lie in [-128, 127] and evalCheckedS returns some 100#8. Lean: `nv_evalCheckedS_complete`.
- **Cited companion lemmas** (proved; statements hashed in `audit/statements.json`):

```lean
theorem inSignedRange_iff_two_pow_of_posWidth :
  ∀ {n : Nat},
    PosWidth n → ∀ (z : Int), InSignedRange n z ↔ -↑(2 ^ (n - 1)) ≤ z ∧ z < ↑(2 ^ (n - 1))
```

- **Prior art:**
  - The Rust Reference (rust-lang/reference commit c9cc32825b03fc206d9c6fe73e9ca6a2f3576d6c), src/expressions/operator-expr.md ([expr.operator.int-overflow.*]).
  - Rust RFC 0560: Integer Overflow (initially written by Gábor Lehel; edited by Nicholas Matsakis), https://github.com/rust-lang/rfcs/blob/f17e8623ee2e2854570dcdb936a9f4ab08c0fcd4/text/0560-integer-overflow.md.
- **Design question:** Specifies a sufficient per-subexpression two's-complement range obligation for panic-free checked signed ring evaluation (also shown necessary in the model by `evalCheckedS_isSome_iff_subexprsInRange`).
- **Basis:** execution (Lean kernel check) of `evalCheckedS_complete` and every Lean name listed above.
- **Basis:** derived (modeling bridge) for the Rust reading: `evalCheckedU`/`evalCheckedS` model chains of `checked_add`/`checked_sub`/`checked_mul`/`checked_neg` that propagate `None`, and `evalPlainU`/`evalPlainS` (defined as `Outcome.ofOption` of the checked evaluators) model plain operators under overflow checks, with `none`/`Outcome.panic` standing for a panic. The core library documents `checked_*` as returning `None` exactly when the mathematical result is not representable, which is what Lean core's `uaddOverflow`, `usubOverflow`, `umulOverflow`, `saddOverflow`, `ssubOverflow`, `smulOverflow` and `negOverflow` flags decide. `.lit k` is a typed constant, not a Rust literal token (out-of-range literal tokens are compile-time errors under the deny-by-default `overflowing_literals` lint, and unary `-` on unsigned types is error `E0600`). Execution cross-check (not proof): `(200u8 + 100) - 100` and `(100i8 + 50) - 50` panic in the two overflow-checked profiles, and `200u8.checked_add(100)` and `100i8.checked_add(50)` return `None` in all four.
- **Non-claims:** package-wide N1, N2, N3, N5 (stated in full under Boundaries), and:
  - Does not allow substituting root-only range checks for SubexprsInRange (InSignedRange n); (100i8 + 50i8) - 50i8 refutes that weakening (ce_checkedS_add_sub_intermediate_overflow).
  - Does not claim signed range equals -(2^(n-1))..2^(n-1)-1 at n = 0; at n = 0, sMinVal 0 = sMaxVal 0 = 0 (see inSignedRange_iff_two_pow_of_posWidth).
  - `.lit k` stands for a typed constant value, not a Rust literal token. In Rust an out-of-range literal is a compile-time error (deny-by-default `overflowing_literals` lint) or is truncated, never a runtime panic. Unary minus applied directly to a literal never overflows (`-128_i8 == i8::MIN`). Unary minus does not exist on unsigned types. The model's `none` results for these cases have no Rust counterpart, and `SubexprsInRange` over-approximates the obligation for them.

#### `evalCheckedS_isSome_iff_subexprsInRange`

- **Tier:** T0. **Kind:** characterization. **Depth:** shallow.
- **Plain claim:** For every bitwidth n, environment env : Nat → BitVec n, and ring expression e : RingExpr, checked signed evaluation succeeds ((evalCheckedS n env e).isSome = true) if and only if SubexprsInRange (InSignedRange n) (fun i => (env i).toInt) e holds.
- **Lean statement** (`Toy.MachInt.evalCheckedS_isSome_iff_subexprsInRange`):

```lean
theorem evalCheckedS_isSome_iff_subexprsInRange :
  ∀ (n : Nat) (env : Nat → BitVec n) (e : RingExpr),
    (evalCheckedS n env e).isSome = true ↔
      SubexprsInRange (InSignedRange n) (fun i => (env i).toInt) e
-- with the specification predicates unfolded:
  ∀ (n : Nat) (env : Nat → BitVec n) (e : RingExpr),
    (evalCheckedS n env e).isSome = true ↔
      SubexprsInRange (fun z => (BitVec.intMin n).toInt ≤ z ∧ z ≤ (BitVec.intMax n).toInt)
        (fun i => (env i).toInt) e
```

- **Hypothesis ledger:** no hypotheses.
- **Non-vacuity witness:** At n = 8 on (x₀ + x₁) - x₁: env = [100#8, 27#8] satisfies SubexprsInRange (InSignedRange 8) and gives isSome = true, while env = [100#8, 50#8] violates SubexprsInRange at the sum and gives isSome = false. Lean: `nv_evalCheckedS_isSome_iff_subexprsInRange`.
- **Prior art:**
  - The Rust Reference (rust-lang/reference commit c9cc32825b03fc206d9c6fe73e9ca6a2f3576d6c), src/expressions/operator-expr.md ([expr.operator.int-overflow.*])
  - The Rust Reference (rust-lang/reference commit c9cc32825b03fc206d9c6fe73e9ca6a2f3576d6c), src/behavior-not-considered-unsafe.md (L14: non-debug overflow may panic or wrap at implementation's discretion)
  - The Rust Reference (rust-lang/reference commit c9cc32825b03fc206d9c6fe73e9ca6a2f3576d6c), src/tokens.md (L518) and src/expressions/literal-expr.md (L426-429: overflowing_literals lint, negation of literal)
  - Ferrocene Language Specification (rust-lang/fls commit bca860e8dab52715effdd49a792347b262f5e539), src/expressions.rst ('Arithmetic Overflow')
  - Rust 1.91.0 core library (rust-lang/rust tag 1.91.0, commit f8297e351a40c1439a467bbbb6879088047f50b3), library/core/src/num/int_macros.rs (checked_add, checked_sub, checked_mul, checked_neg).
- **Design question:** Characterizes the exact necessary and sufficient per-subexpression two's-complement range obligation for checked signed ring evaluation in the model.
- **Basis:** execution (Lean kernel check) of `evalCheckedS_isSome_iff_subexprsInRange` and every Lean name listed above.
- **Basis:** derived (modeling bridge) for the Rust reading: `evalCheckedU`/`evalCheckedS` model chains of `checked_add`/`checked_sub`/`checked_mul`/`checked_neg` that propagate `None`, and `evalPlainU`/`evalPlainS` (defined as `Outcome.ofOption` of the checked evaluators) model plain operators under overflow checks, with `none`/`Outcome.panic` standing for a panic. The core library documents `checked_*` as returning `None` exactly when the mathematical result is not representable, which is what Lean core's `uaddOverflow`, `usubOverflow`, `umulOverflow`, `saddOverflow`, `ssubOverflow`, `smulOverflow` and `negOverflow` flags decide. `.lit k` is a typed constant, not a Rust literal token (out-of-range literal tokens are compile-time errors under the deny-by-default `overflowing_literals` lint, and unary `-` on unsigned types is error `E0600`). Execution cross-check (not proof): `(200u8 + 100) - 100` and `(100i8 + 50) - 50` panic in the two overflow-checked profiles, and `200u8.checked_add(100)` and `100i8.checked_add(50)` return `None` in all four.
- **Non-claims:** package-wide N1, N2, N3, N5 (stated in full under Boundaries), and:
  - Does not claim that failing `SubexprsInRange` implies the final expression value is out of range (`ce_checkedS_add_sub_intermediate_overflow`).
  - `.lit k` stands for a typed constant value, not a Rust literal token. In Rust an out-of-range literal is a compile-time error (deny-by-default `overflowing_literals` lint) or is truncated, never a runtime panic. Unary minus applied directly to a literal never overflows (`-128_i8 == i8::MIN`). Unary minus does not exist on unsigned types. The model's `none` results for these cases have no Rust counterpart, and `SubexprsInRange` over-approximates the obligation for them.

#### `ce_checked_add_sub_intermediate_overflow`

- **Tier:** T0. **Kind:** counterexample. **Depth:** definitional.
- **Plain claim:** For the expression (a + b) - b at 8 bits with (a, b) = (200u8, 100u8) unsigned and (100i8, 50i8) signed, the mathematical result equals a and lies in range, and wrapping evaluation recovers a, yet checked evaluation returns none and plain overflow-checked evaluation produces Outcome.panic.
- **Lean statement** (`Toy.MachInt.ce_checked_add_sub_intermediate_overflow`):

```lean
theorem ce_checked_add_sub_intermediate_overflow :
  have uEnv := fun x =>
    match x with
    | 0 => 200#8
    | x => 100#8;
  have uIntEnv := fun i => ↑(uEnv i).toNat;
  have sEnv := fun x =>
    match x with
    | 0 => 100#8
    | x => 50#8;
  have sIntEnv := fun i => (sEnv i).toInt;
  InUnsignedRange 8 (evalInt uIntEnv addSubCancelExpr) ∧
    ↑(evalWrap 8 uEnv addSubCancelExpr).toNat = evalInt uIntEnv addSubCancelExpr ∧
      evalCheckedU 8 uEnv addSubCancelExpr = none ∧
        evalPlainU 8 uEnv addSubCancelExpr = Outcome.panic ∧
          InSignedRange 8 (evalInt sIntEnv addSubCancelExpr) ∧
            (evalWrap 8 sEnv addSubCancelExpr).toInt = evalInt sIntEnv addSubCancelExpr ∧
              evalCheckedS 8 sEnv addSubCancelExpr = none ∧
                evalPlainS 8 sEnv addSubCancelExpr = Outcome.panic
-- with the specification predicates unfolded:
  have uEnv := fun x =>
    match x with
    | 0 => 200#8
    | x => 100#8;
  have uIntEnv := fun i => ↑(uEnv i).toNat;
  have sEnv := fun x =>
    match x with
    | 0 => 100#8
    | x => 50#8;
  have sIntEnv := fun i => (sEnv i).toInt;
  (0 ≤ evalInt uIntEnv addSubCancelExpr ∧ evalInt uIntEnv addSubCancelExpr < ↑(2 ^ 8)) ∧
    ↑(evalWrap 8 uEnv addSubCancelExpr).toNat = evalInt uIntEnv addSubCancelExpr ∧
      evalCheckedU 8 uEnv addSubCancelExpr = none ∧
        evalPlainU 8 uEnv addSubCancelExpr = Outcome.panic ∧
          ((BitVec.intMin 8).toInt ≤ evalInt sIntEnv addSubCancelExpr ∧
              evalInt sIntEnv addSubCancelExpr ≤ (BitVec.intMax 8).toInt) ∧
            (evalWrap 8 sEnv addSubCancelExpr).toInt = evalInt sIntEnv addSubCancelExpr ∧
              evalCheckedS 8 sEnv addSubCancelExpr = none ∧
                evalPlainS 8 sEnv addSubCancelExpr = Outcome.panic
```

- **Hypothesis ledger:** no hypotheses.
- **Non-vacuity witness:** Self-witnessing concrete counterexample on BitVec 8, cross-checked against rustc (program `support/rustc_semantics_checks.rs`, recorded output `support/rustc_checks_output.txt`). Lean: `ce_checked_add_sub_intermediate_overflow`.
- **Prior art:**
  - The Rust Reference (rust-lang/reference commit c9cc32825b03fc206d9c6fe73e9ca6a2f3576d6c), src/expressions/operator-expr.md ([expr.operator.int-overflow.*])
  - The Rust Reference (rust-lang/reference commit c9cc32825b03fc206d9c6fe73e9ca6a2f3576d6c), src/behavior-not-considered-unsafe.md (L14: non-debug overflow may panic or wrap at implementation's discretion)
  - Rust RFC 0560: Integer Overflow (initially written by Gábor Lehel; edited by Nicholas Matsakis), https://github.com/rust-lang/rfcs/blob/f17e8623ee2e2854570dcdb936a9f4ab08c0fcd4/text/0560-integer-overflow.md
  - Will Dietz, Peng Li, John Regehr, Vikram Adve. Understanding Integer Overflow in C/C++. ICSE 2012, pp. 760-770, DOI 10.1109/ICSE.2012.6227142 (taxonomy and empirical study of integer overflow in C/C++; cited only for the C/C++ contrast in the non-claims, not for the Rust model).
- **Design question:** Demonstrates why verifiers modeling plain or checked arithmetic cannot discharge overflow obligations solely at the final result of a compound expression.
- **Basis:** execution (Lean kernel check) of `ce_checked_add_sub_intermediate_overflow` and every Lean name listed above.
- **Basis:** derived (modeling bridge) for the Rust reading: `evalCheckedU`/`evalCheckedS` model chains of `checked_add`/`checked_sub`/`checked_mul`/`checked_neg` that propagate `None`, and `evalPlainU`/`evalPlainS` (defined as `Outcome.ofOption` of the checked evaluators) model plain operators under overflow checks, with `none`/`Outcome.panic` standing for a panic. The core library documents `checked_*` as returning `None` exactly when the mathematical result is not representable, which is what Lean core's `uaddOverflow`, `usubOverflow`, `umulOverflow`, `saddOverflow`, `ssubOverflow`, `smulOverflow` and `negOverflow` flags decide. `.lit k` is a typed constant, not a Rust literal token (out-of-range literal tokens are compile-time errors under the deny-by-default `overflowing_literals` lint, and unary `-` on unsigned types is error `E0600`). Execution cross-check (not proof): `(200u8 + 100) - 100` and `(100i8 + 50) - 50` panic in the two overflow-checked profiles, and `200u8.checked_add(100)` and `100i8.checked_add(50)` return `None` in all four.
- **Non-claims:** package-wide N1, N2, N3, N5 (stated in full under Boundaries), and:
  - Does not claim that wrapping evaluation fails to recover a; wrapping evaluation succeeds precisely because ring identities transfer without intermediate range bounds.
  - `.lit k` stands for a typed constant value, not a Rust literal token. In Rust an out-of-range literal is a compile-time error (deny-by-default `overflowing_literals` lint) or is truncated, never a runtime panic. Unary minus applied directly to a literal never overflows (`-128_i8 == i8::MIN`). Unary minus does not exist on unsigned types. The model's `none` results for these cases have no Rust counterpart, and `SubexprsInRange` over-approximates the obligation for them.

### Result 3: order under wrapping addition

#### `not_ult_allOnes_add_one`

- **Tier:** T0. **Kind:** impossibility. **Depth:** shallow.
- **Plain claim:** For every bitwidth n, BitVec.allOnes n + 1#n = 0#n, ¬ Ult (BitVec.allOnes n) (BitVec.allOnes n + 1#n), and ¬ (∀ x : BitVec n, Ult x (x + 1#n)). A companion lemma (ult_allOnes_add_one_allOnes_of_posWidth, not part of this statement) adds that under PosWidth n BitVec.allOnes n + 1#n wraps strictly below BitVec.allOnes n.
- **Lean statement** (`Toy.MachInt.not_ult_allOnes_add_one`):

```lean
theorem not_ult_allOnes_add_one :
  ∀ (n : Nat),
    BitVec.allOnes n + 1#n = 0#n ∧
      ¬Ult (BitVec.allOnes n) (BitVec.allOnes n + 1#n) ∧ ¬∀ (x : BitVec n), Ult x (x + 1#n)
-- with the specification predicates unfolded:
  ∀ (n : Nat),
    BitVec.allOnes n + 1#n = 0#n ∧
      ¬(BitVec.allOnes n).ult (BitVec.allOnes n + 1#n) = true ∧
        ¬∀ (x : BitVec n), x.ult (x + 1#n) = true
```

- **Hypothesis ledger:** no hypotheses.
- **Non-vacuity witness:** At n = 8, 255#8 + 1#8 = 0#8, ¬ Ult 255#8 (255#8 + 1#8), Ult (255#8 + 1#8) 255#8, and ¬ (∀ x : BitVec 8, Ult x (x + 1#8)). Lean: `nv_not_ult_allOnes_add_one`.
- **Positive control** (a nearby setting where the impossibility's conclusion fails): `pc_ult_add_one_of_lt_uMax`:

```lean
theorem pc_ult_add_one_of_lt_uMax :
  (∀ (n : Nat) (x : BitVec n), Ult x (BitVec.allOnes n) → Ult x (x + 1#n)) ∧
    Ult (254#8) (BitVec.allOnes 8) ∧ Ult (254#8) (254#8 + 1#8)
```

- **Cited companion lemmas** (proved; statements hashed in `audit/statements.json`):

```lean
theorem not_ult_add_one_uMax :
  ∀ (n : Nat), ¬∀ (x : BitVec n), Ult x (x + 1#n)
```

```lean
theorem ult_add_one_iff_ne_allOnes :
  ∀ {n : Nat} (x : BitVec n), Ult x (x + 1#n) ↔ x ≠ BitVec.allOnes n
```

```lean
theorem ult_allOnes_add_one_allOnes_of_posWidth :
  ∀ {n : Nat}, PosWidth n → Ult (BitVec.allOnes n + 1#n) (BitVec.allOnes n)
```

- **Prior art:**
  - The Rust Reference (rust-lang/reference commit c9cc32825b03fc206d9c6fe73e9ca6a2f3576d6c), src/expressions/operator-expr.md ([expr.operator.int-overflow.*]).
  - Lean 4.34.1 core library (leanprover/lean4:v4.34.1, commit 5045d0056413266e57c625dcd7c365b10e377c52), Init/Data/BitVec/Lemmas.lean (toNat_add, toNat_allOnes).
- **Design question:** Refutes the naive mathematical-integer rule x + 1 > x under fixed-width wrapping unsigned arithmetic with the concrete u<n>::MAX witness exposed directly in the Lean statement (not_ult_add_one_uMax follows as a corollary).
- **Basis:** execution (Lean kernel check) of `not_ult_allOnes_add_one` and every Lean name listed above.
- **Basis:** derived (modeling bridge) for the Rust reading: `Ult`/`Slt` are Rust's `<` on `u<n>`/`i<n>` read through `toNat`/`toInt`, and `+` on `BitVec n` is wrapping addition. The statements therefore describe comparisons of `wrapping_add` results (or of plain `+` results in builds where `rustc` wraps). With overflow checks, `x + 1` at `MAX` panics instead of producing a false comparison. Execution cross-check (not proof): `u8::MAX.wrapping_add(1) = 0`, `i8::MAX.wrapping_add(1) = -128`, and both-wrap instances `44 < 94` (u8) and `-56 < -36` (i8).
- **Non-claims:** package-wide N1, N2, N3, N5 (stated in full under Boundaries), and:
  - Does not claim that x + 1#n wraps strictly below x at n = 0 (at n = 0, BitVec.allOnes 0 = 0#0 so 0 < 0 fails without wrapping strictly downward); strict wrap-below requires PosWidth n (ult_allOnes_add_one_allOnes_of_posWidth).
  - Does not rule out Ult x (x + 1#n) when restricted to x ≠ BitVec.allOnes n (ult_add_one_iff_ne_allOnes; see pc_ult_add_one_of_lt_uMax).
  - The impossibility concerns wrapping addition only. It is escaped by (i) restricting to `x < MAX` (positive control), (ii) checked or overflow-checked addition, where `x + 1` at `MAX` panics or returns `None` instead of producing a false comparison, and (iii) unbounded integers. No claim is made about how C compilers treat `x + 1 > x` for signed types (they may fold it to true because overflow is undefined).

#### `not_slt_intMax_add_one`

- **Tier:** T0. **Kind:** impossibility. **Depth:** shallow.
- **Plain claim:** For every bitwidth n, BitVec.intMax n + 1#n = BitVec.intMin n, ¬ Slt (BitVec.intMax n) (BitVec.intMax n + 1#n), and ¬ (∀ x : BitVec n, Slt x (x + 1#n)). A companion lemma (slt_intMax_add_one_intMax_of_posWidth, not part of this statement) adds that under PosWidth n BitVec.intMax n + 1#n wraps strictly below BitVec.intMax n.
- **Lean statement** (`Toy.MachInt.not_slt_intMax_add_one`):

```lean
theorem not_slt_intMax_add_one :
  ∀ (n : Nat),
    BitVec.intMax n + 1#n = BitVec.intMin n ∧
      ¬Slt (BitVec.intMax n) (BitVec.intMax n + 1#n) ∧ ¬∀ (x : BitVec n), Slt x (x + 1#n)
-- with the specification predicates unfolded:
  ∀ (n : Nat),
    BitVec.intMax n + 1#n = BitVec.intMin n ∧
      ¬(BitVec.intMax n).slt (BitVec.intMax n + 1#n) = true ∧
        ¬∀ (x : BitVec n), x.slt (x + 1#n) = true
```

- **Hypothesis ledger:** no hypotheses.
- **Non-vacuity witness:** At n = 8, 127#8 + 1#8 = -128#8, ¬ Slt 127#8 (127#8 + 1#8), Slt (127#8 + 1#8) 127#8, and ¬ (∀ x : BitVec 8, Slt x (x + 1#8)). Lean: `nv_not_slt_intMax_add_one`.
- **Positive control** (a nearby setting where the impossibility's conclusion fails): `pc_slt_add_one_of_lt_sMax`:

```lean
theorem pc_slt_add_one_of_lt_sMax :
  (∀ (n : Nat) (x : BitVec n), Slt x (BitVec.intMax n) → Slt x (x + 1#n)) ∧
    Slt (126#8) (BitVec.intMax 8) ∧ Slt (126#8) (126#8 + 1#8)
```

- **Cited companion lemmas** (proved; statements hashed in `audit/statements.json`):

```lean
theorem not_slt_add_one_sMax :
  ∀ (n : Nat), ¬∀ (x : BitVec n), Slt x (x + 1#n)
```

```lean
theorem slt_add_one_iff_ne_intMax :
  ∀ {n : Nat} (x : BitVec n), Slt x (x + 1#n) ↔ x ≠ BitVec.intMax n
```

```lean
theorem slt_intMax_add_one_intMax_of_posWidth :
  ∀ {n : Nat}, PosWidth n → Slt (BitVec.intMax n + 1#n) (BitVec.intMax n)
```

- **Prior art:**
  - The Rust Reference (rust-lang/reference commit c9cc32825b03fc206d9c6fe73e9ca6a2f3576d6c), src/expressions/operator-expr.md ([expr.operator.int-overflow.*]).
  - Lean 4.34.1 core library (leanprover/lean4:v4.34.1, commit 5045d0056413266e57c625dcd7c365b10e377c52), Init/Data/BitVec/Lemmas.lean (toInt_intMax, toInt_intMin_of_pos).
- **Design question:** Refutes the naive mathematical-integer rule x + 1 > x under fixed-width wrapping signed arithmetic with the concrete i<n>::MAX witness exposed directly in the Lean statement (not_slt_add_one_sMax follows as a corollary).
- **Basis:** execution (Lean kernel check) of `not_slt_intMax_add_one` and every Lean name listed above.
- **Basis:** derived (modeling bridge) for the Rust reading: `Ult`/`Slt` are Rust's `<` on `u<n>`/`i<n>` read through `toNat`/`toInt`, and `+` on `BitVec n` is wrapping addition. The statements therefore describe comparisons of `wrapping_add` results (or of plain `+` results in builds where `rustc` wraps). With overflow checks, `x + 1` at `MAX` panics instead of producing a false comparison. Execution cross-check (not proof): `u8::MAX.wrapping_add(1) = 0`, `i8::MAX.wrapping_add(1) = -128`, and both-wrap instances `44 < 94` (u8) and `-56 < -36` (i8).
- **Non-claims:** package-wide N1, N2, N3, N5 (stated in full under Boundaries), and:
  - Does not rule out Slt x (x + 1#n) when restricted to x ≠ BitVec.intMax n (slt_add_one_iff_ne_intMax; see pc_slt_add_one_of_lt_sMax, which holds even at n = 1 where -1 + 1 = 0 > -1).
  - The impossibility concerns wrapping addition only. It is escaped by (i) restricting to `x < MAX` (positive control), (ii) checked or overflow-checked addition, where `x + 1` at `MAX` panics or returns `None` instead of producing a false comparison, and (iii) unbounded integers. No claim is made about how C compilers treat `x + 1 > x` for signed types (they may fold it to true because overflow is undefined).

#### `ult_add_right_of_noUAddOverflow`

- **Tier:** T0. **Kind:** theorem. **Depth:** shallow.
- **Plain claim:** For bitvectors a b c : BitVec n, if Ult a b and NoUAddOverflow b c (which entails NoUAddOverflow a c), then Ult (a + c) (b + c).
- **Lean statement** (`Toy.MachInt.ult_add_right_of_noUAddOverflow`):

```lean
theorem ult_add_right_of_noUAddOverflow :
  ∀ {n : Nat} (a b c : BitVec n), Ult a b → NoUAddOverflow b c → Ult (a + c) (b + c)
-- with the specification predicates unfolded:
  ∀ {n : Nat} (a b c : BitVec n),
    a.ult b = true → b.uaddOverflow c = false → (a + c).ult (b + c) = true
```

- **Hypothesis ledger:**
  - `hlt : Ult a b` (tight: counterexample `ce_ult_add_right_drop_hlt`). Establishes the pre-addition unsigned strict inequality a.toNat < b.toNat.
  - `hnoB : NoUAddOverflow b c` (tight: counterexample `ce_ult_add_right_drop_noUAddOverflow`). Sufficient guard preventing b + c from wrapping modulo 2^n; together with Ult a b it entails NoUAddOverflow a c (exported as `noUAddOverflow_of_ult_of_noUAddOverflow`). Tight in the sense that it cannot be dropped alone, though not necessary when both sums wrap.

  Counterexample `ce_ult_add_right_drop_hlt` (all other hypotheses hold and the conclusion fails):

```lean
theorem ce_ult_add_right_drop_hlt :
  ¬Ult 10#8 5#8 ∧ NoUAddOverflow 5#8 1#8 ∧ ¬Ult (10#8 + 1#8) (5#8 + 1#8)
```


  Counterexample `ce_ult_add_right_drop_noUAddOverflow` (all other hypotheses hold and the conclusion fails):

```lean
theorem ce_ult_add_right_drop_noUAddOverflow :
  Ult 1#8 255#8 ∧ ¬NoUAddOverflow 255#8 1#8 ∧ ¬Ult (1#8 + 1#8) (255#8 + 1#8)
```

- **Non-vacuity witness:** 10#8 < 20#8 and 20#8 + 5#8 does not overflow u8, so 15#8 < 25#8. Lean: `nv_ult_add_right_of_noUAddOverflow`.
- **Cited companion lemmas** (proved; statements hashed in `audit/statements.json`):

```lean
theorem noUAddOverflow_of_ult_of_noUAddOverflow :
  ∀ {n : Nat} {a b c : BitVec n}, Ult a b → NoUAddOverflow b c → NoUAddOverflow a c
```

- **Prior art:**
  - Lean 4.34.1 core library (leanprover/lean4:v4.34.1, commit 5045d0056413266e57c625dcd7c365b10e377c52), Init/Data/BitVec/Lemmas.lean (toNat_add_of_lt, le_add_iff_sub_le).
- **Design question:** Identifies a sufficient no-overflow hypothesis (`NoUAddOverflow b c`, which cannot be dropped alone) to transfer < across unsigned addition: only the upper summand needs an overflow-freedom guard (see `ult_add_right_iff_uaddOverflow_eq` for the exact iff criterion including both-wrap cases).
- **Basis:** execution (Lean kernel check) of `ult_add_right_of_noUAddOverflow` and every Lean name listed above.
- **Basis:** derived (modeling bridge) for the Rust reading: `Ult`/`Slt` are Rust's `<` on `u<n>`/`i<n>` read through `toNat`/`toInt`, and `+` on `BitVec n` is wrapping addition. The statements therefore describe comparisons of `wrapping_add` results (or of plain `+` results in builds where `rustc` wraps). With overflow checks, `x + 1` at `MAX` panics instead of producing a false comparison. Execution cross-check (not proof): `u8::MAX.wrapping_add(1) = 0`, `i8::MAX.wrapping_add(1) = -128`, and both-wrap instances `44 < 94` (u8) and `-56 < -36` (i8).
- **Non-claims:** package-wide N1, N2, N3, N5 (stated in full under Boundaries), and:
  - Does not hold if only a + c is overflow-free while b + c wraps (ce_ult_add_right_drop_noUAddOverflow).
  - Does not require separately hypothesizing NoUAddOverflow a c, because Ult a b and NoUAddOverflow b c entail NoUAddOverflow a c (`noUAddOverflow_of_ult_of_noUAddOverflow`, unlike signed addition monotonicity with negative c).
  - The no-overflow hypotheses are sufficient, not necessary. When both sums wrap (in the same direction, for signed types), the order is still preserved, e.g. `200u8 < 250u8` and `200u8.wrapping_add(100) = 44 < 94 = 250u8.wrapping_add(100)`. Each guard is tight only in the sense that it cannot be dropped on its own.

#### `slt_add_right_of_noSAddOverflow`

- **Tier:** T0. **Kind:** theorem. **Depth:** shallow.
- **Plain claim:** For bitvectors a b c : BitVec n, if Slt a b, NoSAddOverflow a c, and NoSAddOverflow b c, then Slt (a + c) (b + c).
- **Lean statement** (`Toy.MachInt.slt_add_right_of_noSAddOverflow`):

```lean
theorem slt_add_right_of_noSAddOverflow :
  ∀ {n : Nat} (a b c : BitVec n),
    Slt a b → NoSAddOverflow a c → NoSAddOverflow b c → Slt (a + c) (b + c)
-- with the specification predicates unfolded:
  ∀ {n : Nat} (a b c : BitVec n),
    a.slt b = true →
      a.saddOverflow c = false → b.saddOverflow c = false → (a + c).slt (b + c) = true
```

- **Hypothesis ledger:**
  - `hlt : Slt a b` (tight: counterexample `ce_slt_add_right_drop_hlt`). Establishes the pre-addition signed strict inequality a.toInt < b.toInt.
  - `hnoA : NoSAddOverflow a c` (tight: counterexample `ce_slt_add_right_drop_noSAddOverflow_left`). Sufficient guard preventing signed underflow of a + c when c is negative (not entailed by NoSAddOverflow b c). Tight (cannot be dropped alone), though not necessary when both sums wrap in the same direction.
  - `hnoB : NoSAddOverflow b c` (tight: counterexample `ce_slt_add_right_drop_noSAddOverflow_right`). Sufficient guard preventing signed overflow of b + c when c is positive (not entailed by NoSAddOverflow a c). Tight (cannot be dropped alone), though not necessary when both sums wrap in the same direction.

  Counterexample `ce_slt_add_right_drop_hlt` (all other hypotheses hold and the conclusion fails):

```lean
theorem ce_slt_add_right_drop_hlt :
  ¬Slt 10#8 5#8 ∧ NoSAddOverflow 10#8 1#8 ∧ NoSAddOverflow 5#8 1#8 ∧ ¬Slt (10#8 + 1#8) (5#8 + 1#8)
```


  Counterexample `ce_slt_add_right_drop_noSAddOverflow_left` (all other hypotheses hold and the conclusion fails):

```lean
theorem ce_slt_add_right_drop_noSAddOverflow_left :
  Slt (-128#8) 10#8 ∧
    ¬NoSAddOverflow (-128#8) (-1#8) ∧
      NoSAddOverflow (10#8) (-1#8) ∧ ¬Slt (-128#8 + -1#8) (10#8 + -1#8)
```


  Counterexample `ce_slt_add_right_drop_noSAddOverflow_right` (all other hypotheses hold and the conclusion fails):

```lean
theorem ce_slt_add_right_drop_noSAddOverflow_right :
  Slt 10#8 127#8 ∧
    NoSAddOverflow 10#8 1#8 ∧ ¬NoSAddOverflow 127#8 1#8 ∧ ¬Slt (10#8 + 1#8) (127#8 + 1#8)
```

- **Non-vacuity witness:** -10#8 < 20#8 and neither -10#8 + 5#8 nor 20#8 + 5#8 overflows i8, yielding -5#8 < 25#8. Lean: `nv_slt_add_right_of_noSAddOverflow`.
- **Prior art:**
  - Lean 4.34.1 core library (leanprover/lean4:v4.34.1, commit 5045d0056413266e57c625dcd7c365b10e377c52), Init/Data/BitVec/Lemmas.lean and Init/Data/BitVec/Basic.lean (saddOverflow, toInt_add).
- **Design question:** Shows the asymmetry between unsigned and signed sufficient no-overflow guards for addition monotonicity: unsigned requires guarding only the upper summand, whereas signed requires guarding both summands (each cannot be dropped alone; see `slt_add_right_iff_saddOverflow_eq` for the exact iff criterion).
- **Basis:** execution (Lean kernel check) of `slt_add_right_of_noSAddOverflow` and every Lean name listed above.
- **Basis:** derived (modeling bridge) for the Rust reading: `Ult`/`Slt` are Rust's `<` on `u<n>`/`i<n>` read through `toNat`/`toInt`, and `+` on `BitVec n` is wrapping addition. The statements therefore describe comparisons of `wrapping_add` results (or of plain `+` results in builds where `rustc` wraps). With overflow checks, `x + 1` at `MAX` panics instead of producing a false comparison. Execution cross-check (not proof): `u8::MAX.wrapping_add(1) = 0`, `i8::MAX.wrapping_add(1) = -128`, and both-wrap instances `44 < 94` (u8) and `-56 < -36` (i8).
- **Non-claims:** package-wide N1, N2, N3, N5 (stated in full under Boundaries), and:
  - Does not allow dropping either NoSAddOverflow a c (negative c can underflow a + c alone) or NoSAddOverflow b c (positive c can overflow b + c alone).
  - Does not claim that both sums must have the same sign, nor that monotonicity fails only at MAX.
  - The no-overflow hypotheses are sufficient, not necessary. When both sums wrap in the same direction, the order is still preserved, e.g. `100i8 < 120i8` and `100i8.wrapping_add(100) = -56 < -36 = 120i8.wrapping_add(100)` (`ce_slt_add_right_both_wrap` proves `Slt (100#8 + 100#8) (120#8 + 100#8)` although both sums overflow). Each guard is tight only in the sense that it cannot be dropped on its own.

#### `ult_add_right_iff_uaddOverflow_eq`

- **Tier:** T0. **Kind:** characterization. **Depth:** shallow.
- **Plain claim:** For bitvectors a b c : BitVec n with Ult a b, wrapping unsigned addition preserves order (Ult (a + c) (b + c)) if and only if BitVec.uaddOverflow a c = BitVec.uaddOverflow b c (either neither wraps, or both wrap modulo 2^n).
- **Lean statement** (`Toy.MachInt.ult_add_right_iff_uaddOverflow_eq`):

```lean
theorem ult_add_right_iff_uaddOverflow_eq :
  ∀ {n : Nat} (a b c : BitVec n),
    Ult a b → (Ult (a + c) (b + c) ↔ a.uaddOverflow c = b.uaddOverflow c)
-- with the specification predicates unfolded:
  ∀ {n : Nat} (a b c : BitVec n),
    a.ult b = true → ((a + c).ult (b + c) = true ↔ a.uaddOverflow c = b.uaddOverflow c)
```

- **Hypothesis ledger:**
  - `hlt : Ult a b` (tight: counterexample `ce_ult_add_right_iff_drop_hlt`). Establishes the pre-addition strict unsigned inequality a.toNat < b.toNat.

  Counterexample `ce_ult_add_right_iff_drop_hlt` (all other hypotheses hold and the conclusion fails):

```lean
theorem ce_ult_add_right_iff_drop_hlt :
  ¬Ult 10#8 5#8 ∧
    ¬(Ult (10#8 + 1#8) (5#8 + 1#8) ↔ (10#8).uaddOverflow 1#8 = (5#8).uaddOverflow 1#8)
```

- **Non-vacuity witness:** At n = 8, Ult 200#8 250#8 holds, both sums overflow with c = 100#8, and Ult (200#8 + 100#8) (250#8 + 100#8) holds. Lean: `nv_ult_add_right_iff_uaddOverflow_eq`.
- **Cited companion lemmas** (proved; statements hashed in `audit/statements.json`):

```lean
theorem ce_ult_add_right_both_wrap :
  Ult 200#8 250#8 ∧
    ¬NoUAddOverflow 200#8 100#8 ∧
      ¬NoUAddOverflow 250#8 100#8 ∧ Ult (200#8 + 100#8) (250#8 + 100#8)
```

- **Prior art:**
  - Lean 4.34.1 core library (leanprover/lean4:v4.34.1, commit 5045d0056413266e57c625dcd7c365b10e377c52), Init/Data/BitVec/Basic.lean (uaddOverflow) and Init/Data/BitVec/Lemmas.lean (toNat_add).
- **Design question:** Gives the exact necessary-and-sufficient criterion for order preservation under wrapping unsigned addition, explaining both `ult_add_right_of_noUAddOverflow` and both-wrap cases.
- **Basis:** execution (Lean kernel check) of `ult_add_right_iff_uaddOverflow_eq` and every Lean name listed above.
- **Basis:** derived (modeling bridge) for the Rust reading: `Ult`/`Slt` are Rust's `<` on `u<n>`/`i<n>` read through `toNat`/`toInt`, and `+` on `BitVec n` is wrapping addition. The statements therefore describe comparisons of `wrapping_add` results (or of plain `+` results in builds where `rustc` wraps). With overflow checks, `x + 1` at `MAX` panics instead of producing a false comparison. Execution cross-check (not proof): `u8::MAX.wrapping_add(1) = 0`, `i8::MAX.wrapping_add(1) = -128`, and both-wrap instances `44 < 94` (u8) and `-56 < -36` (i8).
- **Non-claims:** package-wide N1, N2, N3, N5 (stated in full under Boundaries), and:
  - Does not extend to arbitrary c when `¬ Ult a b`; e.g., when a ≥ b, both sums may avoid overflow while `Ult (a + c) (b + c)` remains false (`ce_ult_add_right_iff_drop_hlt`).
  - Does not imply `NoUAddOverflow b c` when `Ult (a + c) (b + c)` holds; both sums may overflow together (`ce_ult_add_right_both_wrap`).

#### `slt_add_right_iff_saddOverflow_eq`

- **Tier:** T0. **Kind:** characterization. **Depth:** shallow.
- **Plain claim:** For bitvectors a b c : BitVec n with Slt a b, wrapping signed addition preserves order (Slt (a + c) (b + c)) if and only if BitVec.saddOverflow a c = BitVec.saddOverflow b c (either neither wraps, or both wrap in the same direction).
- **Lean statement** (`Toy.MachInt.slt_add_right_iff_saddOverflow_eq`):

```lean
theorem slt_add_right_iff_saddOverflow_eq :
  ∀ {n : Nat} (a b c : BitVec n),
    Slt a b → (Slt (a + c) (b + c) ↔ a.saddOverflow c = b.saddOverflow c)
-- with the specification predicates unfolded:
  ∀ {n : Nat} (a b c : BitVec n),
    a.slt b = true → ((a + c).slt (b + c) = true ↔ a.saddOverflow c = b.saddOverflow c)
```

- **Hypothesis ledger:**
  - `hlt : Slt a b` (tight: counterexample `ce_slt_add_right_iff_drop_hlt`). Establishes the pre-addition strict signed inequality a.toInt < b.toInt (which also guarantees that a + c cannot underflow while b + c overflows).

  Counterexample `ce_slt_add_right_iff_drop_hlt` (all other hypotheses hold and the conclusion fails):

```lean
theorem ce_slt_add_right_iff_drop_hlt :
  ¬Slt 10#8 5#8 ∧
    ¬(Slt (10#8 + 1#8) (5#8 + 1#8) ↔ (10#8).saddOverflow 1#8 = (5#8).saddOverflow 1#8)
```

- **Non-vacuity witness:** At n = 8, Slt 100#8 120#8 holds, both sums overflow with c = 100#8, and Slt (100#8 + 100#8) (120#8 + 100#8) holds. Lean: `nv_slt_add_right_iff_saddOverflow_eq`.
- **Cited companion lemmas** (proved; statements hashed in `audit/statements.json`):

```lean
theorem ce_slt_add_right_both_wrap :
  Slt 100#8 120#8 ∧
    ¬NoSAddOverflow 100#8 100#8 ∧
      ¬NoSAddOverflow 120#8 100#8 ∧ Slt (100#8 + 100#8) (120#8 + 100#8)
```

- **Prior art:**
  - Lean 4.34.1 core library (leanprover/lean4:v4.34.1, commit 5045d0056413266e57c625dcd7c365b10e377c52), Init/Data/BitVec/Basic.lean (saddOverflow) and Init/Data/BitVec/Lemmas.lean (toInt_add).
- **Design question:** Gives the exact necessary-and-sufficient criterion for order preservation under wrapping signed addition, complementing the sufficient no-overflow theorem `slt_add_right_of_noSAddOverflow`.
- **Basis:** execution (Lean kernel check) of `slt_add_right_iff_saddOverflow_eq` and every Lean name listed above.
- **Basis:** derived (modeling bridge) for the Rust reading: `Ult`/`Slt` are Rust's `<` on `u<n>`/`i<n>` read through `toNat`/`toInt`, and `+` on `BitVec n` is wrapping addition. The statements therefore describe comparisons of `wrapping_add` results (or of plain `+` results in builds where `rustc` wraps). With overflow checks, `x + 1` at `MAX` panics instead of producing a false comparison. Execution cross-check (not proof): `u8::MAX.wrapping_add(1) = 0`, `i8::MAX.wrapping_add(1) = -128`, and both-wrap instances `44 < 94` (u8) and `-56 < -36` (i8).
- **Non-claims:** package-wide N1, N2, N3, N5 (stated in full under Boundaries), and:
  - Does not extend to arbitrary a, b when `¬ Slt a b` (`ce_slt_add_right_iff_drop_hlt`).
  - Does not imply `NoSAddOverflow a c` or `NoSAddOverflow b c` when `Slt (a + c) (b + c)` holds; both sums may overflow in the same direction (`ce_slt_add_right_both_wrap`).

### Result 4: division and remainder

#### `checkedUDiv_and_checkedURem_eq_nat_div_mod`

- **Tier:** T0. **Kind:** theorem. **Depth:** shallow.
- **Plain claim:** For any a b : BitVec n satisfying NonZeroDiv b, both checkedUDiv a b and checkedURem a b return some q and some r with q.toNat = a.toNat / b.toNat and r.toNat = a.toNat % b.toNat.
- **Lean statement** (`Toy.MachInt.checkedUDiv_and_checkedURem_eq_nat_div_mod`):

```lean
theorem checkedUDiv_and_checkedURem_eq_nat_div_mod :
  ∀ {n : Nat} (a b : BitVec n),
    NonZeroDiv b →
      ∃ q r,
        checkedUDiv a b = some q ∧
          checkedURem a b = some r ∧ q.toNat = a.toNat / b.toNat ∧ r.toNat = a.toNat % b.toNat
-- with the specification predicates unfolded:
  ∀ {n : Nat} (a b : BitVec n),
    b ≠ 0#n →
      ∃ q r,
        checkedUDiv a b = some q ∧
          checkedURem a b = some r ∧ q.toNat = a.toNat / b.toNat ∧ r.toNat = a.toNat % b.toNat
```

- **Hypothesis ledger:**
  - `hb : NonZeroDiv b` (tight: counterexample `ce_checkedUDiv_drop_nonZeroDiv`). Rules out division/remainder by zero (the sole failure mode of unsigned division and remainder).

  Counterexample `ce_checkedUDiv_drop_nonZeroDiv` (all other hypotheses hold and the conclusion fails):

```lean
theorem ce_checkedUDiv_drop_nonZeroDiv :
  ¬NonZeroDiv 0#8 ∧
    ¬∃ q r,
        checkedUDiv 7#8 0#8 = some q ∧
          checkedURem 7#8 0#8 = some r ∧
            q.toNat = (7#8).toNat / (0#8).toNat ∧ r.toNat = (7#8).toNat % (0#8).toNat
```

- **Non-vacuity witness:** At n = 8, checkedUDiv 7#8 4#8 = some 1#8 and checkedURem 7#8 4#8 = some 3#8. Lean: `nv_checkedUDiv_and_checkedURem_eq_nat_div_mod`.
- **Prior art:**
  - The Rust Reference (rust-lang/reference commit c9cc32825b03fc206d9c6fe73e9ca6a2f3576d6c), src/expressions/operator-expr.md ([expr.operator.int-overflow.*])
  - Rust 1.91.0 core library (rust-lang/rust tag 1.91.0, commit f8297e351a40c1439a467bbbb6879088047f50b3), library/core/src/num/uint_macros.rs (checked_div, checked_rem; https://doc.rust-lang.org/1.91.0/core/primitive.u32.html#method.checked_div).
  - Lean 4.34.1 core library (leanprover/lean4:v4.34.1, commit 5045d0056413266e57c625dcd7c365b10e377c52), Init/Data/BitVec/Lemmas.lean (toNat_udiv, toNat_umod, toNat_div_toNat_lt).
- **Design question:** Establishes that unsigned division and remainder need only NonZeroDiv b and never overflow numerically.
- **Basis:** execution (Lean kernel check) of `checkedUDiv_and_checkedURem_eq_nat_div_mod` and every Lean name listed above.
- **Basis:** derived (modeling bridge) for the Rust reading: `checkedUDiv`, `checkedURem`, `checkedSDiv`, `checkedSRem`, `checkedSDivEuclid` and `checkedSRemEuclid` mirror `checked_div`, `checked_rem`, `checked_div_euclid` and `checked_rem_euclid` as documented in the core library: `None` on a zero divisor and, for signed types, on `(MIN, -1)` (for the remainders too, although the mathematical remainder `0` is representable). Rust's integer `/` and `%` round toward zero (Rust Reference), matching `Int.tdiv`/`Int.tmod`; `div_euclid`/`rem_euclid` match `Int.ediv`/`Int.emod`. Execution cross-check (not proof): `MIN / -1` and `MIN % -1` panic in all four profiles, the four `checked_*` methods return `None` at `(MIN, -1)`, and an exhaustive `i8` comparison of `/`, `%`, `div_euclid` and `rem_euclid` against truncating and Euclidean integer division finds 0 mismatches.
- **Non-claims:** package-wide N1, N2, N3 (stated in full under Boundaries), and:
  - Does not claim that Lean's total BitVec / 0#n = 0#n agrees with Rust; Rust panics on division/remainder by zero regardless of -C overflow-checks.
  - Does not apply to signed division/remainder, which has an additional MIN / -1 overflow trap.

#### `checkedSDiv_eq_some_and_toInt_eq_tdiv`

- **Tier:** T0. **Kind:** theorem. **Depth:** shallow.
- **Plain claim:** For any a b : BitVec n satisfying NonZeroDiv b and NoSDivOverflow a b, checkedSDiv a b returns some q whose signed integer value q.toInt equals truncating division a.toInt.tdiv b.toInt (not Lean's default Euclidean Int /).
- **Lean statement** (`Toy.MachInt.checkedSDiv_eq_some_and_toInt_eq_tdiv`):

```lean
theorem checkedSDiv_eq_some_and_toInt_eq_tdiv :
  ∀ {n : Nat} (a b : BitVec n),
    NonZeroDiv b →
      NoSDivOverflow a b → ∃ q, checkedSDiv a b = some q ∧ q.toInt = a.toInt.tdiv b.toInt
-- with the specification predicates unfolded:
  ∀ {n : Nat} (a b : BitVec n),
    b ≠ 0#n →
      ¬(a = BitVec.intMin n ∧ b = -1#n) →
        ∃ q, checkedSDiv a b = some q ∧ q.toInt = a.toInt.tdiv b.toInt
```

- **Hypothesis ledger:**
  - `hb : NonZeroDiv b` (tight: counterexample `ce_checkedSDiv_drop_nonZeroDiv`). Guards against division by zero.
  - `hno : NoSDivOverflow a b` (tight: counterexample `ce_checkedSDiv_drop_noSDivOverflow`). Guards against the unique two's-complement division overflow (a = intMin n ∧ b = -1#n).

  Counterexample `ce_checkedSDiv_drop_nonZeroDiv` (all other hypotheses hold and the conclusion fails):

```lean
theorem ce_checkedSDiv_drop_nonZeroDiv :
  ¬NonZeroDiv 0#8 ∧
    NoSDivOverflow 7#8 0#8 ∧
      ¬∃ q, checkedSDiv 7#8 0#8 = some q ∧ q.toInt = (7#8).toInt.tdiv (0#8).toInt
```


  Counterexample `ce_checkedSDiv_drop_noSDivOverflow` (all other hypotheses hold and the conclusion fails):

```lean
theorem ce_checkedSDiv_drop_noSDivOverflow :
  NonZeroDiv (-1#8) ∧
    ¬NoSDivOverflow (BitVec.intMin 8) (-1#8) ∧
      ¬∃ q,
          checkedSDiv (BitVec.intMin 8) (-1#8) = some q ∧
            q.toInt = (BitVec.intMin 8).toInt.tdiv (-1#8).toInt
```

- **Non-vacuity witness:** At n = 8, checkedSDiv (-7#8) 4#8 = some (-1#8) and (-1#8).toInt = (-7 : Int).tdiv 4. Lean: `nv_checkedSDiv_eq_some_and_toInt_eq_tdiv`.
- **Prior art:**
  - The Rust Reference (rust-lang/reference commit c9cc32825b03fc206d9c6fe73e9ca6a2f3576d6c), src/expressions/operator-expr.md ([expr.operator.int-overflow.*])
  - Rust 1.91.0 core library (rust-lang/rust tag 1.91.0, commit f8297e351a40c1439a467bbbb6879088047f50b3), library/core/src/num/int_macros.rs (checked_div at L868; https://doc.rust-lang.org/1.91.0/core/primitive.i32.html#method.checked_div).
  - Raymond T. Boute, 'The Euclidean definition of the functions div and mod', ACM TOPLAS 14(2), April 1992, pp. 127-144, DOI 10.1145/128861.128862 (distinguishes T-, F-, and E-rounding conventions).
  - Lean 4.34.1 core library (leanprover/lean4:v4.34.1, commit 5045d0056413266e57c625dcd7c365b10e377c52), Init/Data/Int/DivMod/Basic.lean and Init/Data/BitVec/Bitblast.lean (toInt_sdiv_of_ne_or_ne L1578, Int.tdiv vs Int.ediv).
  - CompCert C verified compiler (AbsInt/CompCert commit 2685140bf72c959446981fb99b5e44a8975021bc), lib/Integers.v (divs at L196, divs_mone at L1044).
  - Isabelle/HOL library (isabelle-prover/mirror-isabelle commit 20d6a3f7ffbaaa82e77f341d90db5070b3428fbe), src/HOL/Library/Signed_Division.thy (signed_divide / sdiv_mult_smod_eq).
  - Aeneas Lean standard library (AeneasVerif/aeneas commit 2e3d4488280bb8a95411db81019a7854a784861f), backends/lean/Aeneas/Std/Scalar/Ops/Div.lean (L20-25), Ops/Rem.lean (L19-21), and CheckedOps/Rem.lean (L61-64) (IScalar.div guards (MIN, -1)).
- **Design question:** Specifies the exact integer operation (Int.tdiv) and side conditions (NonZeroDiv, NoSDivOverflow) for translating Rust signed / into Lean.
- **Basis:** execution (Lean kernel check) of `checkedSDiv_eq_some_and_toInt_eq_tdiv` and every Lean name listed above.
- **Basis:** derived (modeling bridge) for the Rust reading: `checkedUDiv`, `checkedURem`, `checkedSDiv`, `checkedSRem`, `checkedSDivEuclid` and `checkedSRemEuclid` mirror `checked_div`, `checked_rem`, `checked_div_euclid` and `checked_rem_euclid` as documented in the core library: `None` on a zero divisor and, for signed types, on `(MIN, -1)` (for the remainders too, although the mathematical remainder `0` is representable). Rust's integer `/` and `%` round toward zero (Rust Reference), matching `Int.tdiv`/`Int.tmod`; `div_euclid`/`rem_euclid` match `Int.ediv`/`Int.emod`. Execution cross-check (not proof): `MIN / -1` and `MIN % -1` panic in all four profiles, the four `checked_*` methods return `None` at `(MIN, -1)`, and an exhaustive `i8` comparison of `/`, `%`, `div_euclid` and `rem_euclid` against truncating and Euclidean integer division finds 0 mismatches.
- **Non-claims:** package-wide N1, N2, N3 (stated in full under Boundaries), and:
  - Does not match Lean's default Int division a.toInt / b.toInt (which is Int.ediv) when a is negative and b does not divide a (see ce_sdiv_srem_ne_int_ediv_emod).
  - Does not claim that MIN / -1 wraps silently under plain / in release mode; Rust panics on MIN / -1 even when -C overflow-checks is disabled.

#### `checkedSRem_eq_some_and_toInt_eq_tmod`

- **Tier:** T0. **Kind:** theorem. **Depth:** shallow.
- **Plain claim:** For any a b : BitVec n satisfying NonZeroDiv b and NoSDivOverflow a b, checkedSRem a b returns some r whose signed integer value r.toInt equals truncating remainder a.toInt.tmod b.toInt (not Lean's default Euclidean Int %).
- **Lean statement** (`Toy.MachInt.checkedSRem_eq_some_and_toInt_eq_tmod`):

```lean
theorem checkedSRem_eq_some_and_toInt_eq_tmod :
  ∀ {n : Nat} (a b : BitVec n),
    NonZeroDiv b →
      NoSDivOverflow a b → ∃ r, checkedSRem a b = some r ∧ r.toInt = a.toInt.tmod b.toInt
-- with the specification predicates unfolded:
  ∀ {n : Nat} (a b : BitVec n),
    b ≠ 0#n →
      ¬(a = BitVec.intMin n ∧ b = -1#n) →
        ∃ r, checkedSRem a b = some r ∧ r.toInt = a.toInt.tmod b.toInt
```

- **Hypothesis ledger:**
  - `hb : NonZeroDiv b` (tight: counterexample `ce_checkedSRem_drop_nonZeroDiv`). Guards against remainder by zero.
  - `hno : NoSDivOverflow a b` (tight: counterexample `ce_checkedSRem_drop_noSDivOverflow`). Required even for remainder because Rust's checked_rem and % trap on (MIN, -1) alongside division.

  Counterexample `ce_checkedSRem_drop_nonZeroDiv` (all other hypotheses hold and the conclusion fails):

```lean
theorem ce_checkedSRem_drop_nonZeroDiv :
  ¬NonZeroDiv 0#8 ∧
    NoSDivOverflow 7#8 0#8 ∧
      ¬∃ r, checkedSRem 7#8 0#8 = some r ∧ r.toInt = (7#8).toInt.tmod (0#8).toInt
```


  Counterexample `ce_checkedSRem_drop_noSDivOverflow` (all other hypotheses hold and the conclusion fails):

```lean
theorem ce_checkedSRem_drop_noSDivOverflow :
  NonZeroDiv (-1#8) ∧
    ¬NoSDivOverflow (BitVec.intMin 8) (-1#8) ∧
      ¬∃ r,
          checkedSRem (BitVec.intMin 8) (-1#8) = some r ∧
            r.toInt = (BitVec.intMin 8).toInt.tmod (-1#8).toInt
```

- **Non-vacuity witness:** At n = 8, checkedSRem (-7#8) 4#8 = some (-3#8) and (-3#8).toInt = (-7 : Int).tmod 4. Lean: `nv_checkedSRem_eq_some_and_toInt_eq_tmod`.
- **Prior art:**
  - The Rust Reference (rust-lang/reference commit c9cc32825b03fc206d9c6fe73e9ca6a2f3576d6c), src/expressions/operator-expr.md ([expr.operator.int-overflow.*])
  - Rust 1.91.0 core library (rust-lang/rust tag 1.91.0, commit f8297e351a40c1439a467bbbb6879088047f50b3), library/core/src/num/int_macros.rs (checked_rem at L1102; strict_rem docs L1123 note MIN % -1 is 'invalid due to implementation artifacts'; https://doc.rust-lang.org/1.91.0/core/primitive.i32.html#method.checked_rem).
  - Raymond T. Boute, 'The Euclidean definition of the functions div and mod', ACM TOPLAS 14(2), April 1992, pp. 127-144, DOI 10.1145/128861.128862
  - Lean 4.34.1 core library (leanprover/lean4:v4.34.1, commit 5045d0056413266e57c625dcd7c365b10e377c52), Init/Data/BitVec/Bitblast.lean (toInt_srem L1832).
  - CompCert C verified compiler (AbsInt/CompCert commit 2685140bf72c959446981fb99b5e44a8975021bc), lib/Integers.v (mods at L198, mods_mone at L1062).
  - Aeneas Lean standard library (AeneasVerif/aeneas commit 2e3d4488280bb8a95411db81019a7854a784861f), backends/lean/Aeneas/Std/Scalar/Ops/Div.lean (L20-25), Ops/Rem.lean (L19-21), and CheckedOps/Rem.lean (L61-64) (notably, at commit 2e3d4488280b, IScalar.rem and core.num.checked_rem_IScalar_bv_spec guard only y.val != 0 and omit the (MIN, -1) failure guard, diverging from Rust's documented None).
- **Design question:** Prevents a common verifier soundness bug: translating % using Int % (Int.emod) or omitting the (MIN, -1) guard on remainder because 0 is representable.
- **Basis:** execution (Lean kernel check) of `checkedSRem_eq_some_and_toInt_eq_tmod` and every Lean name listed above.
- **Basis:** derived (modeling bridge) for the Rust reading: `checkedUDiv`, `checkedURem`, `checkedSDiv`, `checkedSRem`, `checkedSDivEuclid` and `checkedSRemEuclid` mirror `checked_div`, `checked_rem`, `checked_div_euclid` and `checked_rem_euclid` as documented in the core library: `None` on a zero divisor and, for signed types, on `(MIN, -1)` (for the remainders too, although the mathematical remainder `0` is representable). Rust's integer `/` and `%` round toward zero (Rust Reference), matching `Int.tdiv`/`Int.tmod`; `div_euclid`/`rem_euclid` match `Int.ediv`/`Int.emod`. Execution cross-check (not proof): `MIN / -1` and `MIN % -1` panic in all four profiles, the four `checked_*` methods return `None` at `(MIN, -1)`, and an exhaustive `i8` comparison of `/`, `%`, `div_euclid` and `rem_euclid` against truncating and Euclidean integer division finds 0 mismatches.
- **Non-claims:** package-wide N1, N2, N3 (stated in full under Boundaries), and:
  - Does not match Lean's default Int remainder a.toInt % b.toInt (which is Int.emod, always nonnegative for b ≠ 0) when a is negative and not divisible by b (see ce_sdiv_srem_ne_int_ediv_emod).
  - Does not succeed on (MIN, -1) merely because the mathematical remainder 0 fits in InSignedRange n; checkedSRem returns none and plain % panics unconditionally (see checkedSRem_intMin_negOne_eq_none).

#### `tdiv_not_inSignedRange_iff_intMin_negOne`

- **Tier:** T0. **Kind:** characterization. **Depth:** shallow.
- **Plain claim:** For every positive bitwidth PosWidth n and every a b : BitVec n, the mathematical truncating quotient a.toInt.tdiv b.toInt falls outside InSignedRange n if and only if a = BitVec.intMin n and b = -1#n.
- **Lean statement** (`Toy.MachInt.tdiv_not_inSignedRange_iff_intMin_negOne`):

```lean
theorem tdiv_not_inSignedRange_iff_intMin_negOne :
  ∀ {n : Nat},
    PosWidth n →
      ∀ (a b : BitVec n), ¬InSignedRange n (a.toInt.tdiv b.toInt) ↔ a = BitVec.intMin n ∧ b = -1#n
-- with the specification predicates unfolded:
  ∀ {n : Nat},
    0 < n →
      ∀ (a b : BitVec n),
        ¬((BitVec.intMin n).toInt ≤ a.toInt.tdiv b.toInt ∧
              a.toInt.tdiv b.toInt ≤ (BitVec.intMax n).toInt) ↔
          a = BitVec.intMin n ∧ b = -1#n
```

- **Hypothesis ledger:**
  - `hn : PosWidth n` (tight: counterexample `ce_tdiv_overflow_iff_drop_posWidth`, `ce_tdiv_overflow_iff_drop_posWidth_canonical`). Rules out the zero-width degeneracy n = 0 where intMin 0 = -1#0 = 0#0 yet 0.tdiv 0 = 0 ∈ InSignedRange 0.

  Counterexample `ce_tdiv_overflow_iff_drop_posWidth` (states the facts from which the failure follows; the canonical form is `ce_tdiv_overflow_iff_drop_posWidth_canonical` below):

```lean
theorem ce_tdiv_overflow_iff_drop_posWidth :
  ¬PosWidth 0 ∧
    (0#0 = BitVec.intMin 0 ∧ 0#0 = -1#0) ∧ InSignedRange 0 ((0#0).toInt.tdiv (0#0).toInt)
```


  Counterexample `ce_tdiv_overflow_iff_drop_posWidth_canonical` (all other hypotheses hold and the conclusion fails):

```lean
theorem ce_tdiv_overflow_iff_drop_posWidth_canonical :
  ¬PosWidth 0 ∧
    ¬(¬InSignedRange 0 ((0#0).toInt.tdiv (0#0).toInt) ↔ 0#0 = BitVec.intMin 0 ∧ 0#0 = -1#0)
```

- **Non-vacuity witness:** At n = 8, (BitVec.intMin 8).toInt.tdiv (-1#8).toInt = 128, which lies outside InSignedRange 8 = [-128, 127]. Both sides false: at n = 8, 5.tdiv (-1) = -5 is in range and (5#8, -1#8) is not (MIN, -1). Width one: -1#1 = intMin 1 and (intMin 1).toInt.tdiv (-1#1).toInt = 1 lies outside InSignedRange 1 = [-1, 0]. Lean: `nv_tdiv_not_inSignedRange_iff_intMin_negOne`, `nv_tdiv_iff_both_false`, `nv_tdiv_iff_width_one`.
- **Prior art:**
  - Rust 1.91.0 core library (rust-lang/rust tag 1.91.0, commit f8297e351a40c1439a467bbbb6879088047f50b3), library/core/src/num/int_macros.rs (strict_div docs: 'The only case where such an overflow can occur is when one divides MIN / -1 on a signed type').
  - Lean 4.34.1 core library (leanprover/lean4:v4.34.1, commit 5045d0056413266e57c625dcd7c365b10e377c52), Init/Data/BitVec/Bitblast.lean (BitVec.sdivOverflow_eq at L1321, proved for Int.ediv; BitVec.toInt_sdiv_of_ne_or_ne at L1578) and Init/Data/BitVec/Basic.lean (sdivOverflow at L845-852, SMT-LIB bvsdivo).
  - Lean 4.34.1 core library (leanprover/lean4:v4.34.1, commit 5045d0056413266e57c625dcd7c365b10e377c52), Init/Data/BitVec/Lemmas.lean (toInt_ediv_toInt_lt_*, sdivOverflow_eq_negOverflow_of_eq_allOnes).
- **Design question:** Establishes (alongside Lean core's `BitVec.sdivOverflow_eq`, which is phrased with `Int.ediv`) that checking a ≠ intMin n ∨ b ≠ -1#n is both necessary and sufficient for mathematical signed truncating division quotients to stay in range (`shallow` from `BitVec.toInt_sdiv_of_ne_or_ne`).
- **Basis:** execution (Lean kernel check) of `tdiv_not_inSignedRange_iff_intMin_negOne` and every Lean name listed above.
- **Basis:** derived (modeling bridge) for the Rust reading: `checkedUDiv`, `checkedURem`, `checkedSDiv`, `checkedSRem`, `checkedSDivEuclid` and `checkedSRemEuclid` mirror `checked_div`, `checked_rem`, `checked_div_euclid` and `checked_rem_euclid` as documented in the core library: `None` on a zero divisor and, for signed types, on `(MIN, -1)` (for the remainders too, although the mathematical remainder `0` is representable). Rust's integer `/` and `%` round toward zero (Rust Reference), matching `Int.tdiv`/`Int.tmod`; `div_euclid`/`rem_euclid` match `Int.ediv`/`Int.emod`. Execution cross-check (not proof): `MIN / -1` and `MIN % -1` panic in all four profiles, the four `checked_*` methods return `None` at `(MIN, -1)`, and an exhaustive `i8` comparison of `/`, `%`, `div_euclid` and `rem_euclid` against truncating and Euclidean integer division finds 0 mismatches.
- **Non-claims:** package-wide N1, N2, N3 (stated in full under Boundaries), and:
  - Does not claim that checkedSDiv succeeds whenever a.toInt.tdiv b.toInt is in InSignedRange n: division by zero yields tdiv = 0 ∈ InSignedRange n yet checkedSDiv returns none.
  - Does not characterize remainder overflow: tmod never leaves InSignedRange n, yet checkedSRem still returns none at (MIN, -1).
  - This characterizes when the mathematical truncating quotient leaves the signed range. It is not a characterization of when Rust's `/` panics: division by zero also panics, although `Int.tdiv x 0 = 0` is in range.

#### `checkedSRem_intMin_negOne_eq_none`

- **Tier:** T0. **Kind:** theorem. **Depth:** definitional.
- **Plain claim:** For every positive bitwidth PosWidth n, -1#n is nonzero (NonZeroDiv (-1#n)) and the mathematical truncating remainder (BitVec.intMin n).toInt.tmod (-1#n).toInt lies in InSignedRange n, yet both checkedSRem (BitVec.intMin n) (-1#n) and checkedSRemEuclid (BitVec.intMin n) (-1#n) equal none.
- **Lean statement** (`Toy.MachInt.checkedSRem_intMin_negOne_eq_none`):

```lean
theorem checkedSRem_intMin_negOne_eq_none :
  ∀ {n : Nat},
    PosWidth n →
      NonZeroDiv (-1#n) ∧
        InSignedRange n ((BitVec.intMin n).toInt.tmod (-1#n).toInt) ∧
          checkedSRem (BitVec.intMin n) (-1#n) = none ∧
            checkedSRemEuclid (BitVec.intMin n) (-1#n) = none
-- with the specification predicates unfolded:
  ∀ {n : Nat},
    0 < n →
      -1#n ≠ 0#n ∧
        ((BitVec.intMin n).toInt ≤ (BitVec.intMin n).toInt.tmod (-1#n).toInt ∧
            (BitVec.intMin n).toInt.tmod (-1#n).toInt ≤ (BitVec.intMax n).toInt) ∧
          checkedSRem (BitVec.intMin n) (-1#n) = none ∧
            checkedSRemEuclid (BitVec.intMin n) (-1#n) = none
```

- **Hypothesis ledger:**
  - `hn : PosWidth n` (tight: counterexample `ce_checkedSRem_intMin_drop_posWidth`, `ce_checkedSRem_intMin_drop_posWidth_canonical`). Ensures -1#n ≠ 0#n for the scene-setting NonZeroDiv (-1#n) conjunct (at n = 0, -1#0 = 0#0). The = none behavioral conjuncts themselves hold unconditionally at every width n via unfolding (`checkedSRem_intMin_negOne_eq_none_unconditional`).

  Counterexample `ce_checkedSRem_intMin_drop_posWidth` (states the facts from which the failure follows; the canonical form is `ce_checkedSRem_intMin_drop_posWidth_canonical` below):

```lean
theorem ce_checkedSRem_intMin_drop_posWidth :
  ¬PosWidth 0 ∧ ¬NonZeroDiv (-1#0)
```


  Counterexample `ce_checkedSRem_intMin_drop_posWidth_canonical` (all other hypotheses hold and the conclusion fails):

```lean
theorem ce_checkedSRem_intMin_drop_posWidth_canonical :
  ¬PosWidth 0 ∧
    ¬(NonZeroDiv (-1#0) ∧
        InSignedRange 0 ((BitVec.intMin 0).toInt.tmod (-1#0).toInt) ∧
          checkedSRem (BitVec.intMin 0) (-1#0) = none ∧
            checkedSRemEuclid (BitVec.intMin 0) (-1#0) = none)
```

- **Non-vacuity witness:** At n = 8, -1#8 ≠ 0#8 and 0 ∈ InSignedRange 8, yet checkedSRem (BitVec.intMin 8) (-1#8) = none. Lean: `nv_checkedSRem_intMin_negOne_eq_none`.
- **Cited companion lemmas** (proved; statements hashed in `audit/statements.json`):

```lean
theorem checkedSRem_intMin_negOne_eq_none_unconditional :
  ∀ (n : Nat),
    checkedSRem (BitVec.intMin n) (-1#n) = none ∧
      checkedSRemEuclid (BitVec.intMin n) (-1#n) = none
```

- **Prior art:**
  - The Rust Reference (rust-lang/reference commit c9cc32825b03fc206d9c6fe73e9ca6a2f3576d6c), src/expressions/operator-expr.md ([expr.operator.int-overflow.*]) (using / or % with MIN and -1 panics even when -C overflow-checks is disabled, 'for legacy reasons').
  - Rust 1.91.0 core library (rust-lang/rust tag 1.91.0, commit f8297e351a40c1439a467bbbb6879088047f50b3), library/core/src/num/int_macros.rs (checked_rem L1102, strict_rem L1123 'invalid due to implementation artifacts', checked_rem_euclid L1168; https://doc.rust-lang.org/1.91.0/core/primitive.i32.html#method.checked_rem).
  - Rust RFC 0560: Integer Overflow (initially written by Gábor Lehel; edited by Nicholas Matsakis), https://github.com/rust-lang/rfcs/blob/f17e8623ee2e2854570dcdb936a9f4ab08c0fcd4/text/0560-integer-overflow.md (unconditional panic on INT_MIN / -1 and INT_MIN % -1 'for legacy reasons').
  - Aeneas Lean standard library (AeneasVerif/aeneas commit 2e3d4488280bb8a95411db81019a7854a784861f), backends/lean/Aeneas/Std/Scalar/Ops/Div.lean (L20-25), Ops/Rem.lean (L19-21), and CheckedOps/Rem.lean (L61-64) (concrete modeling pitfall: IScalar.rem / checked_rem_IScalar at commit 2e3d4488280b omit the (MIN, -1) guard, returning ok/some 0 instead of Rust's documented None).
- **Design question:** Records the exact exception to 'in-range result implies no panic': verifiers cannot prove x % y panic-free from y ≠ 0 and in-range remainder alone; they must still discharge NoSDivOverflow x y.
- **Basis:** execution (Lean kernel check) of `checkedSRem_intMin_negOne_eq_none` and every Lean name listed above.
- **Basis:** derived (modeling bridge) for the Rust reading: `checkedUDiv`, `checkedURem`, `checkedSDiv`, `checkedSRem`, `checkedSDivEuclid` and `checkedSRemEuclid` mirror `checked_div`, `checked_rem`, `checked_div_euclid` and `checked_rem_euclid` as documented in the core library: `None` on a zero divisor and, for signed types, on `(MIN, -1)` (for the remainders too, although the mathematical remainder `0` is representable). Rust's integer `/` and `%` round toward zero (Rust Reference), matching `Int.tdiv`/`Int.tmod`; `div_euclid`/`rem_euclid` match `Int.ediv`/`Int.emod`. Execution cross-check (not proof): `MIN / -1` and `MIN % -1` panic in all four profiles, the four `checked_*` methods return `None` at `(MIN, -1)`, and an exhaustive `i8` comparison of `/`, `%`, `div_euclid` and `rem_euclid` against truncating and Euclidean integer division finds 0 mismatches.
- **Non-claims:** package-wide N1, N2, N3 (stated in full under Boundaries), and:
  - Does not claim that the mathematical remainder fails to fit in i<n>; the none outcome in our model reflects a documented Rust rule (core docs: 'invalid due to implementation artifacts'; Reference: 'for legacy reasons'), encoded directly in checkedSRem/checkedSRemEuclid (`derived (modeling bridge)`, cross-checked with rustc).
  - Does not apply to unsigned types, which have no -1 value causing division overflow.

#### `checkedSDivEuclid_eq_some_and_toInt_eq_ediv`

- **Tier:** T0. **Kind:** theorem. **Depth:** shallow.
- **Plain claim:** For any a b : BitVec n satisfying NonZeroDiv b and NoSDivOverflow a b, checkedSDivEuclid a b (modeling i<n>::checked_div_euclid) returns some q with q.toInt = a.toInt.ediv b.toInt (Lean's default Int /).
- **Lean statement** (`Toy.MachInt.checkedSDivEuclid_eq_some_and_toInt_eq_ediv`):

```lean
theorem checkedSDivEuclid_eq_some_and_toInt_eq_ediv :
  ∀ {n : Nat} (a b : BitVec n),
    NonZeroDiv b →
      NoSDivOverflow a b → ∃ q, checkedSDivEuclid a b = some q ∧ q.toInt = a.toInt.ediv b.toInt
-- with the specification predicates unfolded:
  ∀ {n : Nat} (a b : BitVec n),
    b ≠ 0#n →
      ¬(a = BitVec.intMin n ∧ b = -1#n) →
        ∃ q, checkedSDivEuclid a b = some q ∧ q.toInt = a.toInt.ediv b.toInt
```

- **Hypothesis ledger:**
  - `hb : NonZeroDiv b` (tight: counterexample `ce_checkedSDivEuclid_drop_nonZeroDiv`). Guards against division by zero.
  - `hno : NoSDivOverflow a b` (tight: counterexample `ce_checkedSDivEuclid_drop_noSDivOverflow`). Guards against (MIN, -1), where MIN.ediv (-1) = -MIN overflows InSignedRange n.

  Counterexample `ce_checkedSDivEuclid_drop_nonZeroDiv` (all other hypotheses hold and the conclusion fails):

```lean
theorem ce_checkedSDivEuclid_drop_nonZeroDiv :
  ¬NonZeroDiv 0#8 ∧
    NoSDivOverflow 7#8 0#8 ∧
      ¬∃ q, checkedSDivEuclid 7#8 0#8 = some q ∧ q.toInt = (7#8).toInt.ediv (0#8).toInt
```


  Counterexample `ce_checkedSDivEuclid_drop_noSDivOverflow` (all other hypotheses hold and the conclusion fails):

```lean
theorem ce_checkedSDivEuclid_drop_noSDivOverflow :
  NonZeroDiv (-1#8) ∧
    ¬NoSDivOverflow (BitVec.intMin 8) (-1#8) ∧
      ¬∃ q,
          checkedSDivEuclid (BitVec.intMin 8) (-1#8) = some q ∧
            q.toInt = (BitVec.intMin 8).toInt.ediv (-1#8).toInt
```

- **Non-vacuity witness:** At n = 8, checkedSDivEuclid (-7#8) 4#8 = some (-2#8) and (-2#8).toInt = (-7 : Int).ediv 4. Lean: `nv_checkedSDivEuclid_eq_some_and_toInt_eq_ediv`.
- **Prior art:**
  - Rust 1.91.0 core library (rust-lang/rust tag 1.91.0, commit f8297e351a40c1439a467bbbb6879088047f50b3), library/core/src/num/int_macros.rs (checked_div_euclid L935, div_euclid L3112; https://doc.rust-lang.org/1.91.0/core/primitive.i32.html#method.checked_div_euclid).
  - Raymond T. Boute, 'The Euclidean definition of the functions div and mod', ACM TOPLAS 14(2), April 1992, pp. 127-144, DOI 10.1145/128861.128862
  - Lean 4.34.1 core library (leanprover/lean4:v4.34.1, commit 5045d0056413266e57c625dcd7c365b10e377c52), Init/Data/Int/DivMod/Basic.lean (Int.ediv) and Init/Data/BitVec/Bitblast.lean (toInt_sdiv_of_ne_or_ne, toInt_srem).
- **Design question:** Connects Lean's default Int.ediv directly to Rust's explicit div_euclid / checked_div_euclid rather than Rust's `/` operator.
- **Basis:** execution (Lean kernel check) of `checkedSDivEuclid_eq_some_and_toInt_eq_ediv` and every Lean name listed above.
- **Basis:** derived (modeling bridge) for the Rust reading: `checkedUDiv`, `checkedURem`, `checkedSDiv`, `checkedSRem`, `checkedSDivEuclid` and `checkedSRemEuclid` mirror `checked_div`, `checked_rem`, `checked_div_euclid` and `checked_rem_euclid` as documented in the core library: `None` on a zero divisor and, for signed types, on `(MIN, -1)` (for the remainders too, although the mathematical remainder `0` is representable). Rust's integer `/` and `%` round toward zero (Rust Reference), matching `Int.tdiv`/`Int.tmod`; `div_euclid`/`rem_euclid` match `Int.ediv`/`Int.emod`. Execution cross-check (not proof): `MIN / -1` and `MIN % -1` panic in all four profiles, the four `checked_*` methods return `None` at `(MIN, -1)`, and an exhaustive `i8` comparison of `/`, `%`, `div_euclid` and `rem_euclid` against truncating and Euclidean integer division finds 0 mismatches.
- **Non-claims:** package-wide N1, N2, N3 (stated in full under Boundaries), and:
  - Does not match Rust's `/` operator (which is truncating Int.tdiv, not Int.ediv).
  - Does not avoid the (MIN, -1) trap.

#### `checkedSRemEuclid_eq_some_and_toInt_eq_emod`

- **Tier:** T0. **Kind:** theorem. **Depth:** shallow.
- **Plain claim:** For any a b : BitVec n satisfying NonZeroDiv b and NoSDivOverflow a b, checkedSRemEuclid a b (modeling i<n>::checked_rem_euclid) returns some r with r.toInt = a.toInt.emod b.toInt (Lean's default Int %, always in [0, |b|)).
- **Lean statement** (`Toy.MachInt.checkedSRemEuclid_eq_some_and_toInt_eq_emod`):

```lean
theorem checkedSRemEuclid_eq_some_and_toInt_eq_emod :
  ∀ {n : Nat} (a b : BitVec n),
    NonZeroDiv b →
      NoSDivOverflow a b → ∃ r, checkedSRemEuclid a b = some r ∧ r.toInt = a.toInt.emod b.toInt
-- with the specification predicates unfolded:
  ∀ {n : Nat} (a b : BitVec n),
    b ≠ 0#n →
      ¬(a = BitVec.intMin n ∧ b = -1#n) →
        ∃ r, checkedSRemEuclid a b = some r ∧ r.toInt = a.toInt.emod b.toInt
```

- **Hypothesis ledger:**
  - `hb : NonZeroDiv b` (tight: counterexample `ce_checkedSRemEuclid_drop_nonZeroDiv`). Guards against division by zero.
  - `hno : NoSDivOverflow a b` (tight: counterexample `ce_checkedSRemEuclid_drop_noSDivOverflow`). Required because checked_rem_euclid also rejects (MIN, -1) in Rust core.

  Counterexample `ce_checkedSRemEuclid_drop_nonZeroDiv` (all other hypotheses hold and the conclusion fails):

```lean
theorem ce_checkedSRemEuclid_drop_nonZeroDiv :
  ¬NonZeroDiv 0#8 ∧
    NoSDivOverflow 7#8 0#8 ∧
      ¬∃ r, checkedSRemEuclid 7#8 0#8 = some r ∧ r.toInt = (7#8).toInt.emod (0#8).toInt
```


  Counterexample `ce_checkedSRemEuclid_drop_noSDivOverflow` (all other hypotheses hold and the conclusion fails):

```lean
theorem ce_checkedSRemEuclid_drop_noSDivOverflow :
  NonZeroDiv (-1#8) ∧
    ¬NoSDivOverflow (BitVec.intMin 8) (-1#8) ∧
      ¬∃ r,
          checkedSRemEuclid (BitVec.intMin 8) (-1#8) = some r ∧
            r.toInt = (BitVec.intMin 8).toInt.emod (-1#8).toInt
```

- **Non-vacuity witness:** At n = 8, checkedSRemEuclid (-7#8) 4#8 = some (1#8) and (1#8).toInt = (-7 : Int).emod 4. Lean: `nv_checkedSRemEuclid_eq_some_and_toInt_eq_emod`.
- **Prior art:**
  - Rust 1.91.0 core library (rust-lang/rust tag 1.91.0, commit f8297e351a40c1439a467bbbb6879088047f50b3), library/core/src/num/int_macros.rs (checked_rem_euclid L1168, rem_euclid L3155, noting r.wrapping_add(rhs.wrapping_abs()) handles rhs == Self::MIN; https://doc.rust-lang.org/1.91.0/core/primitive.i32.html#method.checked_rem_euclid).
  - Raymond T. Boute, 'The Euclidean definition of the functions div and mod', ACM TOPLAS 14(2), April 1992, pp. 127-144, DOI 10.1145/128861.128862
  - Lean 4.34.1 core library (leanprover/lean4:v4.34.1, commit 5045d0056413266e57c625dcd7c365b10e377c52), Init/Data/Int/DivMod/Basic.lean (Int.emod) and Init/Data/BitVec/Bitblast.lean (toInt_srem).
- **Design question:** Connects Lean's default Int.emod to Rust's rem_euclid / checked_rem_euclid and explains why rhs = MIN still works safely when r < 0.
- **Basis:** execution (Lean kernel check) of `checkedSRemEuclid_eq_some_and_toInt_eq_emod` and every Lean name listed above.
- **Basis:** derived (modeling bridge) for the Rust reading: `checkedUDiv`, `checkedURem`, `checkedSDiv`, `checkedSRem`, `checkedSDivEuclid` and `checkedSRemEuclid` mirror `checked_div`, `checked_rem`, `checked_div_euclid` and `checked_rem_euclid` as documented in the core library: `None` on a zero divisor and, for signed types, on `(MIN, -1)` (for the remainders too, although the mathematical remainder `0` is representable). Rust's integer `/` and `%` round toward zero (Rust Reference), matching `Int.tdiv`/`Int.tmod`; `div_euclid`/`rem_euclid` match `Int.ediv`/`Int.emod`. Execution cross-check (not proof): `MIN / -1` and `MIN % -1` panic in all four profiles, the four `checked_*` methods return `None` at `(MIN, -1)`, and an exhaustive `i8` comparison of `/`, `%`, `div_euclid` and `rem_euclid` against truncating and Euclidean integer division finds 0 mismatches.
- **Non-claims:** package-wide N1, N2, N3 (stated in full under Boundaries), and:
  - Does not match Rust's `%` operator (which is truncating Int.tmod) when a < 0 and b does not divide a.
  - Does not fail when b = MIN and a = -1: (-1i8).rem_euclid (-128i8) = 127 fits in i8 via wrapping addition of b.abs.

#### `ce_sdiv_srem_ne_int_ediv_emod`

- **Tier:** T0. **Kind:** counterexample. **Depth:** definitional.
- **Plain claim:** For (-7 : i8) and (4 : i8), Rust/bitvector truncating sdiv and srem yield (-1, -3) (Int.tdiv/Int.tmod), directly disagreeing with Lean's default Int / and % (-2, 1, matching sdivEuclid/sremEuclid); for (7 : i8) and (-4 : i8), truncating sdiv/srem coincide with Int.ediv/Int.emod (-1, 3) while differing from flooring Int.fdiv and BitVec.smod (-2, -1).
- **Lean statement** (`Toy.MachInt.ce_sdiv_srem_ne_int_ediv_emod`):

```lean
theorem ce_sdiv_srem_ne_int_ediv_emod :
  ((-7#8).sdiv 4#8).toInt = -1 ∧
    ((-7#8).srem 4#8).toInt = -3 ∧
      -7 / 4 = -2 ∧
        -7 % 4 = 1 ∧
          ((-7#8).sdiv 4#8).toInt ≠ (-7#8).toInt / (4#8).toInt ∧
            ((-7#8).srem 4#8).toInt ≠ (-7#8).toInt % (4#8).toInt ∧
              (sdivEuclid (-7#8) 4#8).toInt = (-7).ediv 4 ∧
                (sremEuclid (-7#8) 4#8).toInt = (-7).emod 4 ∧
                  ((7#8).sdiv (-4#8)).toInt = (7#8).toInt / (-4#8).toInt ∧
                    ((7#8).srem (-4#8)).toInt = (7#8).toInt % (-4#8).toInt ∧
                      ((7#8).sdiv (-4#8)).toInt ≠ Int.fdiv 7 (-4) ∧
                        ((7#8).srem (-4#8)).toInt ≠ ((7#8).smod (-4#8)).toInt
```

- **Hypothesis ledger:** no hypotheses.
- **Non-vacuity witness:** Self-witnessing concrete counterexample on BitVec 8, cross-checked against rustc (program `support/rustc_semantics_checks.rs`, recorded output `support/rustc_checks_output.txt`). Lean: `ce_sdiv_srem_ne_int_ediv_emod`.
- **Prior art:**
  - Lean 4.34.1 core library (leanprover/lean4:v4.34.1, commit 5045d0056413266e57c625dcd7c365b10e377c52), Init/Data/Int/DivMod/Basic.lean (historical note: Int / and % use Int.ediv/Int.emod, not Int.tdiv/Int.tmod).
  - Raymond T. Boute, 'The Euclidean definition of the functions div and mod', ACM TOPLAS 14(2), 1992, DOI 10.1145/128861.128862.
- **Design question:** Separates T-, E-, and F-rounding conventions concretely to prevent silent semantic mismatch when translating Rust `/` and `%` to Lean `Int`.
- **Basis:** execution (Lean kernel check) of `ce_sdiv_srem_ne_int_ediv_emod` and every Lean name listed above.
- **Basis:** derived (modeling bridge) for the Rust reading: `checkedUDiv`, `checkedURem`, `checkedSDiv`, `checkedSRem`, `checkedSDivEuclid` and `checkedSRemEuclid` mirror `checked_div`, `checked_rem`, `checked_div_euclid` and `checked_rem_euclid` as documented in the core library: `None` on a zero divisor and, for signed types, on `(MIN, -1)` (for the remainders too, although the mathematical remainder `0` is representable). Rust's integer `/` and `%` round toward zero (Rust Reference), matching `Int.tdiv`/`Int.tmod`; `div_euclid`/`rem_euclid` match `Int.ediv`/`Int.emod`. Execution cross-check (not proof): `MIN / -1` and `MIN % -1` panic in all four profiles, the four `checked_*` methods return `None` at `(MIN, -1)`, and an exhaustive `i8` comparison of `/`, `%`, `div_euclid` and `rem_euclid` against truncating and Euclidean integer division finds 0 mismatches.
- **Non-claims:** package-wide N1, N2, N3 (stated in full under Boundaries), and:
  - Does not claim that sdiv/srem disagree with Int.ediv/Int.emod for nonnegative dividends a ≥ 0; disagreement requires a < 0 and ¬ (b ∣ a).

### Result 5: shifts and shift-count masking

#### `wrappingShl_eq_mul_twoPow_of_shiftInBounds`

- **Tier:** T0. **Kind:** theorem. **Depth:** shallow.
- **Plain claim:** For any x : BitVec n and shift count k satisfying ShiftInBounds n k (k < n), checkedShl x k = some (wrappingShl x k), (wrappingShl x k).toNat = (x.toNat * 2^k) % 2^n, and (wrappingShl x k).toInt = Int.bmod (x.toInt * 2^k) (2^n).
- **Lean statement** (`Toy.MachInt.wrappingShl_eq_mul_twoPow_of_shiftInBounds`):

```lean
theorem wrappingShl_eq_mul_twoPow_of_shiftInBounds :
  ∀ {n k : Nat} (x : BitVec n),
    ShiftInBounds n k →
      checkedShl x k = some (wrappingShl x k) ∧
        (wrappingShl x k).toNat = x.toNat * 2 ^ k % 2 ^ n ∧
          (wrappingShl x k).toInt = (x.toInt * ↑(2 ^ k)).bmod (2 ^ n)
-- with the specification predicates unfolded:
  ∀ {n k : Nat} (x : BitVec n),
    k < n →
      checkedShl x k = some (wrappingShl x k) ∧
        (wrappingShl x k).toNat = x.toNat * 2 ^ k % 2 ^ n ∧
          (wrappingShl x k).toInt = (x.toInt * ↑(2 ^ k)).bmod (2 ^ n)
```

- **Hypothesis ledger:**
  - `hk : ShiftInBounds n k` (tight: counterexample `ce_wrappingShl_overshift_ne_mul_twoPow`, `ce_wrappingShl_drop_shiftInBounds_canonical`). Prevents k % n from wrapping the shift count modulo n (unlike unbounded mathematical left shift).

  Counterexample `ce_wrappingShl_overshift_ne_mul_twoPow` (states the facts from which the failure follows; the canonical form is `ce_wrappingShl_drop_shiftInBounds_canonical` below):

```lean
theorem ce_wrappingShl_overshift_ne_mul_twoPow :
  checkedShl (1#8) 8 = none ∧
    (wrappingShl (1#8) 8).toNat ≠ 1 * 2 ^ 8 % 2 ^ 8 ∧
      checkedShl (5#8) 9 = none ∧
        (wrappingShl (5#8) 9).toNat ≠ 5 * 2 ^ 9 % 2 ^ 8 ∧
          (wrappingShl (-1#8) 8).toInt ≠ (-1 * (↑(2 ^ 8) : Int)).bmod (2 ^ 8)
```

  Counterexample `ce_wrappingShl_drop_shiftInBounds_canonical` (all other hypotheses hold and the conclusion fails):

```lean
theorem ce_wrappingShl_drop_shiftInBounds_canonical :
  ¬ShiftInBounds 8 8 ∧
    ¬(checkedShl (1#8) 8 = some (wrappingShl (1#8) 8) ∧
        (wrappingShl (1#8) 8).toNat = (1#8).toNat * 2 ^ 8 % 2 ^ 8 ∧
          (wrappingShl (1#8) 8).toInt = ((1#8).toInt * ↑(2 ^ 8)).bmod (2 ^ 8))
```

- **Non-vacuity witness:** At n = 8, x = 5#8, k = 3 < 8: checkedShl (5#8) 3 = some (wrappingShl (5#8) 3) = some (40#8). Lean: `nv_wrappingShl_eq_mul_twoPow_of_shiftInBounds`.
- **Cited companion lemmas** (proved; statements hashed in `audit/statements.json`):

```lean
theorem ce_wrappingShl_mod_ne_and_mask_nonPowTwo :
  4 % 3 ≠ 4 &&& 3 - 1 ∧ wrappingShl (1#3) 4 ≠ 1#3 <<< (4 &&& 3 - 1)
```

```lean
theorem mod_eq_and_mask_forall_iff_isPowerOfTwo :
  ∀ (n : Nat), (∀ (k : Nat), k % n = k &&& n - 1) ↔ ∃ m, n = 2 ^ m
```

```lean
theorem mod_twoPow_eq_and_mask :
  ∀ (m k : Nat), k % 2 ^ m = k &&& 2 ^ m - 1
```

- **Prior art:**
  - Rust 1.91.0 core library (rust-lang/rust tag 1.91.0, commit f8297e351a40c1439a467bbbb6879088047f50b3), library/core/src/num/int_macros.rs and uint_macros.rs. `checked_shl` (defined at int_macros.rs L1315 and uint_macros.rs L1723) is documented as "Checked shift left. Computes `self << rhs`, returning `None` if `rhs` is larger than or equal to the number of bits in `self`.", and its body tests only `rhs < Self::BITS`. `wrapping_shl` (defined at int_macros.rs L2281 and uint_macros.rs L2537) is documented as "Panic-free bitwise shift-left; yields `self << mask(rhs)`, where `mask` removes any high-order bits of `rhs` that would cause the shift to exceed the bitwidth of the type.", followed by a note that it "is *not* the same as a rotate-left", and its body shifts by `rhs & (Self::BITS - 1)`. Neither doc comment describes the plain `<<` operator (see N5). https://doc.rust-lang.org/1.91.0/core/primitive.u32.html#method.checked_shl, https://doc.rust-lang.org/1.91.0/core/primitive.u32.html#method.wrapping_shl.
  - The Rust Reference (rust-lang/reference commit c9cc32825b03fc206d9c6fe73e9ca6a2f3576d6c), src/expressions/operator-expr.md ([expr.operator.int-overflow.*]) ([expr.operator.int-overflow.shift]; supersedes RFC 560's unconditional shift-masking rule).
  - The Rust Reference (rust-lang/reference commit c9cc32825b03fc206d9c6fe73e9ca6a2f3576d6c), src/behavior-not-considered-unsafe.md (L14: non-debug overflow may panic or wrap at implementation's discretion)
  - Lean 4.34.1 core library (leanprover/lean4:v4.34.1, commit 5045d0056413266e57c625dcd7c365b10e377c52), Init/Data/BitVec/Lemmas.lean (toNat_shiftLeft, toInt_shiftLeft) and Init/Data/Nat/Bitwise/Lemmas.lean (testBit_mod_two_pow, testBit_two_pow_sub_one).
  - CompCert C verified compiler (AbsInt/CompCert commit 2685140bf72c959446981fb99b5e44a8975021bc), lib/Integers.v (shl_mul at L2267).
- **Design question:** Identifies the shift-count side condition (k < n) needed for `checked_shl` to return `Some` and for `wrapping_shl` to equal multiplication by 2^k modulo 2^n; neither `checked_shl` nor overflow-checked `<<` checks whether high bits are shifted out (`ce_checkedShl_drops_high_bits_without_none`).
- **Basis:** execution (Lean kernel check) of `wrappingShl_eq_mul_twoPow_of_shiftInBounds` and every Lean name listed above.
- **Basis:** derived (modeling bridge) for the Rust reading: `wrappingShl`/`wrappingUShr`/`wrappingSShr` reduce the shift count modulo `n`; Rust's `wrapping_shl`/`wrapping_shr` mask it with `rhs & (BITS - 1)`, and the two agree for every count exactly when `n` is a power of two (`mod_eq_and_mask_forall_iff_isPowerOfTwo`), which covers every Rust fixed-width integer type. `checkedShl`/`checkedUShr`/`checkedSShr` mirror `checked_shl`/`checked_shr` (`None` iff `rhs >= BITS`), and `>>` on signed types is an arithmetic shift (Rust Reference). Execution cross-check (not proof): `128u8.checked_shl(1) = Some(0)`, `64i8.checked_shl(1) = Some(-128)`, `1u8.wrapping_shl(8) = 1`, and `1u8 << 8` panics only under overflow checks.
- **Non-claims:** package-wide N1, N2, N3, N5 (stated in full under Boundaries), and:
  - Does not hold when k ≥ n: wrapping_shl masks k modulo n rather than shifting bits out to zero (see ce_wrappingShl_overshift_ne_mul_twoPow).
  - Does not equate wrapping_shl with Rust's unbounded_shl (which yields 0 for k ≥ n).
  - `ShiftInBounds n k` (equivalently, `checked_shl` returning `Some`, or `<<` not panicking under overflow checks) does not imply that no set bits are shifted out: `128u8.checked_shl(1) == Some(0)` (see `ce_checkedShl_drops_high_bits_without_none`). Replacing `x << k` by the unbounded integer `x * 2^k` additionally requires `x * 2^k < 2^n` (unsigned) or the signed analogue, which neither the operator nor `checked_shl` checks.
  - The model defines wrapping shifts by masking `k % n`, which equals Rust `core::num`'s bitmask `k & (BITS - 1)` for every shift count `k` if and only if `n` is a power of two (`mod_eq_and_mask_forall_iff_isPowerOfTwo`; the 'if' direction is `mod_twoPow_eq_and_mask`), and diverges at other widths, e.g. `n = 3, k = 4` (`ce_wrappingShl_mod_ne_and_mask_nonPowTwo`). All Rust fixed-width integer types have power-of-two widths. Plain shift operators (`<<`/`>>`, which panic under overflow checks and mask under `rustc` when checks are disabled) are not modeled by a separate `Outcome` evaluator.

#### `wrappingUShr_and_wrappingSShr_of_shiftInBounds`

- **Tier:** T0. **Kind:** theorem. **Depth:** shallow.
- **Plain claim:** For any x : BitVec n and shift count k satisfying ShiftInBounds n k (k < n), checkedUShr x k = some (wrappingUShr x k) with toNat = x.toNat / 2^k, and checkedSShr x k = some (wrappingSShr x k) with toInt = x.toInt.fdiv (2^k) (flooring division, not truncating tdiv).
- **Lean statement** (`Toy.MachInt.wrappingUShr_and_wrappingSShr_of_shiftInBounds`):

```lean
theorem wrappingUShr_and_wrappingSShr_of_shiftInBounds :
  ∀ {n k : Nat} (x : BitVec n),
    ShiftInBounds n k →
      checkedUShr x k = some (wrappingUShr x k) ∧
        (wrappingUShr x k).toNat = x.toNat / 2 ^ k ∧
          checkedSShr x k = some (wrappingSShr x k) ∧
            (wrappingSShr x k).toInt = x.toInt.fdiv ↑(2 ^ k)
-- with the specification predicates unfolded:
  ∀ {n k : Nat} (x : BitVec n),
    k < n →
      checkedUShr x k = some (wrappingUShr x k) ∧
        (wrappingUShr x k).toNat = x.toNat / 2 ^ k ∧
          checkedSShr x k = some (wrappingSShr x k) ∧
            (wrappingSShr x k).toInt = x.toInt.fdiv ↑(2 ^ k)
```

- **Hypothesis ledger:**
  - `hk : ShiftInBounds n k` (tight: counterexample `ce_wrappingShr_overshift`, `ce_wrappingShr_drop_shiftInBounds_canonical`). Prevents k % n from masking out high bits of the shift count k.

  Counterexample `ce_wrappingShr_overshift` (states the facts from which the failure follows; the canonical form is `ce_wrappingShr_drop_shiftInBounds_canonical` below):

```lean
theorem ce_wrappingShr_overshift :
  ¬ShiftInBounds 8 8 ∧
    checkedUShr (128#8) 8 = none ∧
      (wrappingUShr (128#8) 8).toNat ≠ (128#8).toNat / 2 ^ 8 ∧
        checkedSShr (-128#8) 8 = none ∧
          (wrappingSShr (-128#8) 8).toInt ≠ (-128#8).toInt.fdiv ↑(2 ^ 8)
```

  Counterexample `ce_wrappingShr_drop_shiftInBounds_canonical` (all other hypotheses hold and the conclusion fails):

```lean
theorem ce_wrappingShr_drop_shiftInBounds_canonical :
  ¬ShiftInBounds 8 8 ∧
    ¬(checkedUShr (128#8) 8 = some (wrappingUShr (128#8) 8) ∧
        (wrappingUShr (128#8) 8).toNat = (128#8).toNat / 2 ^ 8 ∧
          checkedSShr (128#8) 8 = some (wrappingSShr (128#8) 8) ∧
            (wrappingSShr (128#8) 8).toInt = (128#8).toInt.fdiv ↑(2 ^ 8))
```

- **Non-vacuity witness:** At n = 8, k = 2 < 8: wrappingUShr 9#8 2 = 2#8 and wrappingSShr (-7#8) 2 = -2#8 = (-7).fdiv 4. Lean: `nv_wrappingUShr_and_wrappingSShr_of_shiftInBounds`.
- **Cited companion lemmas** (proved; statements hashed in `audit/statements.json`):

```lean
theorem ce_sshiftRight_ne_sdiv_twoPow :
  (wrappingSShr (-1#8) 1).toInt = (-1).fdiv 2 ∧ (wrappingSShr (-1#8) 1).toInt ≠ (-1).tdiv 2
```

```lean
theorem ce_wrappingShl_mod_ne_and_mask_nonPowTwo :
  4 % 3 ≠ 4 &&& 3 - 1 ∧ wrappingShl (1#3) 4 ≠ 1#3 <<< (4 &&& 3 - 1)
```

```lean
theorem mod_eq_and_mask_forall_iff_isPowerOfTwo :
  ∀ (n : Nat), (∀ (k : Nat), k % n = k &&& n - 1) ↔ ∃ m, n = 2 ^ m
```

```lean
theorem mod_twoPow_eq_and_mask :
  ∀ (m k : Nat), k % 2 ^ m = k &&& 2 ^ m - 1
```

- **Prior art:**
  - Rust 1.91.0 core library (rust-lang/rust tag 1.91.0, commit f8297e351a40c1439a467bbbb6879088047f50b3), library/core/src/num/int_macros.rs and uint_macros.rs (checked_shr, wrapping_shr; https://doc.rust-lang.org/1.91.0/core/primitive.i32.html#method.wrapping_shr).
  - The Rust Reference (rust-lang/reference commit c9cc32825b03fc206d9c6fe73e9ca6a2f3576d6c), src/expressions/operator-expr.md ([expr.operator.int-overflow.*]) (arithmetic right shift on signed types; [expr.operator.int-overflow.shift] supersedes RFC 560's unconditional shift-masking rule).
  - The Rust Reference (rust-lang/reference commit c9cc32825b03fc206d9c6fe73e9ca6a2f3576d6c), src/behavior-not-considered-unsafe.md (L14: non-debug overflow may panic or wrap at implementation's discretion)
  - Lean 4.34.1 core library (leanprover/lean4:v4.34.1, commit 5045d0056413266e57c625dcd7c365b10e377c52), Init/Data/BitVec/Lemmas.lean (toNat_ushiftRight, sshiftRight_eq, le_toInt_shiftRight, toInt_shiftRight_lt).
- **Design question:** Prevents two distinct shift bugs in specifications: overshifting (k ≥ n) and confusing arithmetic right shift (flooring fdiv) with signed division by 2^k (truncating tdiv).
- **Basis:** execution (Lean kernel check) of `wrappingUShr_and_wrappingSShr_of_shiftInBounds` and every Lean name listed above.
- **Basis:** derived (modeling bridge) for the Rust reading: `wrappingShl`/`wrappingUShr`/`wrappingSShr` reduce the shift count modulo `n`; Rust's `wrapping_shl`/`wrapping_shr` mask it with `rhs & (BITS - 1)`, and the two agree for every count exactly when `n` is a power of two (`mod_eq_and_mask_forall_iff_isPowerOfTwo`), which covers every Rust fixed-width integer type. `checkedShl`/`checkedUShr`/`checkedSShr` mirror `checked_shl`/`checked_shr` (`None` iff `rhs >= BITS`), and `>>` on signed types is an arithmetic shift (Rust Reference). Execution cross-check (not proof): `128u8.checked_shl(1) = Some(0)`, `64i8.checked_shl(1) = Some(-128)`, `1u8.wrapping_shl(8) = 1`, and `1u8 << 8` panics only under overflow checks.
- **Non-claims:** package-wide N1, N2, N3, N5 (stated in full under Boundaries), and:
  - Does not equate signed arithmetic right shift `>>` with Rust's signed `/` by 2^k (which truncates toward 0, e.g. -1 >> 1 = -1 ≠ 0 = (-1).tdiv 2; see ce_sshiftRight_ne_sdiv_twoPow).
  - Does not hold when k ≥ n (see ce_wrappingShr_overshift).
  - The model defines wrapping shifts by masking `k % n`, which equals Rust `core::num`'s bitmask `k & (BITS - 1)` for every shift count `k` if and only if `n` is a power of two (`mod_eq_and_mask_forall_iff_isPowerOfTwo`; the 'if' direction is `mod_twoPow_eq_and_mask`), and diverges at other widths, e.g. `n = 3, k = 4` (`ce_wrappingShl_mod_ne_and_mask_nonPowTwo`). All Rust fixed-width integer types have power-of-two widths. Plain shift operators (`<<`/`>>`, which panic under overflow checks and mask under `rustc` when checks are disabled) are not modeled by a separate `Outcome` evaluator.

#### `ce_wrappingShl_overshift_ne_mul_twoPow`

- **Tier:** T0. **Kind:** counterexample. **Depth:** definitional.
- **Plain claim:** At width n = 8 with shift counts k ≥ n: checkedShl (1#8) 8 = none and checkedShl (5#8) 9 = none, while (wrappingShl (1#8) 8).toNat ≠ (1 * 2^8) % 2^8, (wrappingShl (5#8) 9).toNat ≠ (5 * 2^9) % 2^8, and (wrappingShl (-1#8) 8).toInt ≠ Int.bmod (-1 * 2^8) (2^8); so without k < n the unsigned and signed multiplication identities of wrappingShl_eq_mul_twoPow_of_shiftInBounds fail.
- **Lean statement** (`Toy.MachInt.ce_wrappingShl_overshift_ne_mul_twoPow`):

```lean
theorem ce_wrappingShl_overshift_ne_mul_twoPow :
  checkedShl (1#8) 8 = none ∧
    (wrappingShl (1#8) 8).toNat ≠ 1 * 2 ^ 8 % 2 ^ 8 ∧
      checkedShl (5#8) 9 = none ∧
        (wrappingShl (5#8) 9).toNat ≠ 5 * 2 ^ 9 % 2 ^ 8 ∧
          (wrappingShl (-1#8) 8).toInt ≠ (-1 * (↑(2 ^ 8) : Int)).bmod (2 ^ 8)
```

- **Hypothesis ledger:** no hypotheses.
- **Non-vacuity witness:** Self-witnessing concrete counterexample on BitVec 8, cross-checked against rustc (program `support/rustc_semantics_checks.rs`, recorded output `support/rustc_checks_output.txt`). Lean: `ce_wrappingShl_overshift_ne_mul_twoPow`.
- **Cited companion lemmas** (proved; statements hashed in `audit/statements.json`):

```lean
theorem ce_wrappingShl_mod_ne_and_mask_nonPowTwo :
  4 % 3 ≠ 4 &&& 3 - 1 ∧ wrappingShl (1#3) 4 ≠ 1#3 <<< (4 &&& 3 - 1)
```

```lean
theorem mod_eq_and_mask_forall_iff_isPowerOfTwo :
  ∀ (n : Nat), (∀ (k : Nat), k % n = k &&& n - 1) ↔ ∃ m, n = 2 ^ m
```

```lean
theorem mod_twoPow_eq_and_mask :
  ∀ (m k : Nat), k % 2 ^ m = k &&& 2 ^ m - 1
```

- **Prior art:**
  - Rust 1.91.0 core library (rust-lang/rust tag 1.91.0, commit f8297e351a40c1439a467bbbb6879088047f50b3), library/core/src/num/int_macros.rs and uint_macros.rs (`wrapping_shl`, defined at int_macros.rs L2281 and uint_macros.rs L2537, documented as yielding `self << mask(rhs)`, where `mask` removes any high-order bits of `rhs` that would cause the shift to exceed the bitwidth of the type, and implemented as a shift by `rhs & (Self::BITS - 1)`; https://doc.rust-lang.org/1.91.0/core/primitive.i32.html#method.wrapping_shl).
  - The Rust Reference (rust-lang/reference commit c9cc32825b03fc206d9c6fe73e9ca6a2f3576d6c), src/expressions/operator-expr.md ([expr.operator.int-overflow.*]) ([expr.operator.int-overflow.shift]).
  - The Rust Reference (rust-lang/reference commit c9cc32825b03fc206d9c6fe73e9ca6a2f3576d6c), src/behavior-not-considered-unsafe.md (L14: non-debug overflow may panic or wrap at implementation's discretion)
- **Design question:** Demonstrates why k < n cannot be omitted when modeling wrapping_shl (or unchecked rustc `<<`) as multiplication by 2^k modulo 2^n.
- **Basis:** execution (Lean kernel check) of `ce_wrappingShl_overshift_ne_mul_twoPow` and every Lean name listed above.
- **Basis:** derived (modeling bridge) for the Rust reading: `wrappingShl`/`wrappingUShr`/`wrappingSShr` reduce the shift count modulo `n`; Rust's `wrapping_shl`/`wrapping_shr` mask it with `rhs & (BITS - 1)`, and the two agree for every count exactly when `n` is a power of two (`mod_eq_and_mask_forall_iff_isPowerOfTwo`), which covers every Rust fixed-width integer type. `checkedShl`/`checkedUShr`/`checkedSShr` mirror `checked_shl`/`checked_shr` (`None` iff `rhs >= BITS`), and `>>` on signed types is an arithmetic shift (Rust Reference). In Rust terms the conjuncts concern `1u8.checked_shl(8)`, `5u8.checked_shl(9)`, `1u8.wrapping_shl(8)`, `5u8.wrapping_shl(9)` and `(-1i8).wrapping_shl(8)`. Execution cross-check (not proof): `1u8.checked_shl(8) = None`, `1u8.wrapping_shl(8) = 1`, `5u8.wrapping_shl(9) = 10`, `(-1i8).wrapping_shl(8) = -1`, `128u8.checked_shl(1) = Some(0)`, `64i8.checked_shl(1) = Some(-128)`, and `1u8 << 8` panics only under overflow checks.
- **Non-claims:** package-wide N1, N2, N3, N5 (stated in full under Boundaries), and:
  - Does not assert that plain `<<` masks k as a language guarantee when overflow checks are disabled; masking in unchecked builds is rustc behaviour while the Reference permits either panic or wrapping (and RFC 560's unconditional shift-masking rule is superseded by [expr.operator.int-overflow.shift]).
  - The model defines wrapping shifts by masking `k % n`, which equals Rust `core::num`'s bitmask `k & (BITS - 1)` for every shift count `k` if and only if `n` is a power of two (`mod_eq_and_mask_forall_iff_isPowerOfTwo`; the 'if' direction is `mod_twoPow_eq_and_mask`), and diverges at other widths, e.g. `n = 3, k = 4` (`ce_wrappingShl_mod_ne_and_mask_nonPowTwo`). All Rust fixed-width integer types have power-of-two widths. Plain shift operators (`<<`/`>>`, which panic under overflow checks and mask under `rustc` when checks are disabled) are not modeled by a separate `Outcome` evaluator.

#### `ce_checkedShl_drops_high_bits_without_none`

- **Tier:** T0. **Kind:** counterexample. **Depth:** definitional.
- **Plain claim:** At n = 8 and k = 1, ShiftInBounds 8 1 holds so checkedShl (128#8) 1 = some 0#8 and checkedShl (64#8) 1 = some (-128#8) succeed despite shifting out/overflowing high bits, whereas checkedUMul (128#8) 2#8 = none and checkedSMul (64#8) 2#8 = none.
- **Lean statement** (`Toy.MachInt.ce_checkedShl_drops_high_bits_without_none`):

```lean
theorem ce_checkedShl_drops_high_bits_without_none :
  ShiftInBounds 8 1 ∧
    checkedShl (128#8) 1 = some 0#8 ∧
      (0#8).toNat ≠ (128#8).toNat * 2 ^ 1 ∧
        checkedUMul 128#8 2#8 = none ∧
          checkedShl (64#8) 1 = some (-128#8) ∧
            (-128#8).toInt ≠ (64#8).toInt * ↑(2 ^ 1) ∧ checkedSMul 64#8 2#8 = none
-- with the specification predicates unfolded:
  1 < 8 ∧
    checkedShl (128#8) 1 = some 0#8 ∧
      (0#8).toNat ≠ (128#8).toNat * 2 ^ 1 ∧
        checkedUMul 128#8 2#8 = none ∧
          checkedShl (64#8) 1 = some (-128#8) ∧
            (-128#8).toInt ≠ (64#8).toInt * ↑(2 ^ 1) ∧ checkedSMul 64#8 2#8 = none
```

- **Hypothesis ledger:** no hypotheses.
- **Non-vacuity witness:** Self-witnessing concrete counterexample on BitVec 8, cross-checked against rustc (program `support/rustc_semantics_checks.rs`, recorded output `support/rustc_checks_output.txt`). Lean: `ce_checkedShl_drops_high_bits_without_none`.
- **Cited companion lemmas** (proved; statements hashed in `audit/statements.json`):

```lean
theorem ce_wrappingShl_mod_ne_and_mask_nonPowTwo :
  4 % 3 ≠ 4 &&& 3 - 1 ∧ wrappingShl (1#3) 4 ≠ 1#3 <<< (4 &&& 3 - 1)
```

```lean
theorem mod_eq_and_mask_forall_iff_isPowerOfTwo :
  ∀ (n : Nat), (∀ (k : Nat), k % n = k &&& n - 1) ↔ ∃ m, n = 2 ^ m
```

```lean
theorem mod_twoPow_eq_and_mask :
  ∀ (m k : Nat), k % 2 ^ m = k &&& 2 ^ m - 1
```

- **Prior art:**
  - Rust 1.91.0 core library (rust-lang/rust tag 1.91.0, commit f8297e351a40c1439a467bbbb6879088047f50b3), library/core/src/num/int_macros.rs and uint_macros.rs (`checked_shl`, defined at int_macros.rs L1315 and uint_macros.rs L1723; both doc comments include the example `0x10.checked_shl(BITS - 1) == Some(0)`, and both bodies test only `rhs < Self::BITS`; https://doc.rust-lang.org/1.91.0/core/primitive.u32.html#method.checked_shl).
  - The Rust Reference (rust-lang/reference commit c9cc32825b03fc206d9c6fe73e9ca6a2f3576d6c), src/expressions/operator-expr.md ([expr.operator.int-overflow.*]) ([expr.operator.int-overflow.shift]).
- **Design question:** Refutes the folklore rule that `x << k` under overflow checks equals unbounded `x * 2^k` whenever `k < BITS`.
- **Basis:** execution (Lean kernel check) of `ce_checkedShl_drops_high_bits_without_none` and every Lean name listed above.
- **Basis:** derived (modeling bridge) for the Rust reading: `wrappingShl`/`wrappingUShr`/`wrappingSShr` reduce the shift count modulo `n`; Rust's `wrapping_shl`/`wrapping_shr` mask it with `rhs & (BITS - 1)`, and the two agree for every count exactly when `n` is a power of two (`mod_eq_and_mask_forall_iff_isPowerOfTwo`), which covers every Rust fixed-width integer type. `checkedShl`/`checkedUShr`/`checkedSShr` mirror `checked_shl`/`checked_shr` (`None` iff `rhs >= BITS`), and `>>` on signed types is an arithmetic shift (Rust Reference). Execution cross-check (not proof): `128u8.checked_shl(1) = Some(0)`, `64i8.checked_shl(1) = Some(-128)`, `1u8.wrapping_shl(8) = 1`, and `1u8 << 8` panics only under overflow checks.
- **Non-claims:** package-wide N1, N2, N3, N5 (stated in full under Boundaries), and:
  - Does not claim `checked_shl` returns `None` when nonzero bits are shifted out; Rust's `checked_shl` checks only `rhs < BITS` (unlike the unstable `exact_shl`, feature `exact_bitshifts` at Rust 1.91.0, renamed `shl_exact` on later nightlies).
  - The model defines wrapping shifts by masking `k % n`, which equals Rust `core::num`'s bitmask `k & (BITS - 1)` for every shift count `k` if and only if `n` is a power of two (`mod_eq_and_mask_forall_iff_isPowerOfTwo`; the 'if' direction is `mod_twoPow_eq_and_mask`), and diverges at other widths, e.g. `n = 3, k = 4` (`ce_wrappingShl_mod_ne_and_mask_nonPowTwo`). All Rust fixed-width integer types have power-of-two widths. Plain shift operators (`<<`/`>>`, which panic under overflow checks and mask under `rustc` when checks are disabled) are not modeled by a separate `Outcome` evaluator.

### Result 6: numeric `as` casts

#### `castFromUnsigned_toNat_eq_mod`

- **Tier:** T0. **Kind:** theorem. **Depth:** definitional.
- **Plain claim:** For every source width n, target width m, and x : BitVec n, (castFromUnsigned m x).toNat = x.toNat % 2^m unconditionally.
- **Lean statement** (`Toy.MachInt.castFromUnsigned_toNat_eq_mod`):

```lean
theorem castFromUnsigned_toNat_eq_mod :
  ∀ {n m : Nat} (x : BitVec n), (castFromUnsigned m x).toNat = x.toNat % 2 ^ m
```

- **Hypothesis ledger:** no hypotheses.
- **Non-vacuity witness:** At n = 16, m = 8, x = 0x1234#16: (castFromUnsigned 8 (0x1234#16)).toNat = 0x34 = 0x1234 % 256. Lean: `nv_castFromUnsigned_toNat_eq_mod`.
- **Prior art:**
  - The Rust Reference (rust-lang/reference commit c9cc32825b03fc206d9c6fe73e9ca6a2f3576d6c), src/expressions/operator-expr.md ([expr.as.numeric.*]).
  - Lean 4.34.1 core library (leanprover/lean4:v4.34.1, commit 5045d0056413266e57c625dcd7c365b10e377c52), Init/Data/BitVec/Bootstrap.lean (toNat_setWidth).
- **Design question:** Reference point recording the exact mathematical semantics (`BitVec.toNat_setWidth`) for unsigned-source numeric `as` casts across arbitrary widths.
- **Basis:** execution (Lean kernel check) of `castFromUnsigned_toNat_eq_mod` and every Lean name listed above.
- **Basis:** derived (modeling bridge) for the Rust reading: `castFromUnsigned`/`castFromSigned` (Lean `setWidth`/`signExtend`) model integer-to-integer `as` casts as specified by the Rust Reference `[expr.as.numeric]`: same-size casts are no-ops, larger-to-smaller casts truncate, and smaller-to-larger casts zero-extend from unsigned and sign-extend from signed sources (the target's signedness does not affect the bits). Execution cross-check (not proof): `(256u16 as u8) as u16 = 0`, `(128i16 as i8) as i16 = -128`, `(-1i8) as u16 = 65535`, `((-1i8) as u8) as u16 = 255`, and `u8 -> u32 -> u16` preserves every value.
- **Non-claims:** package-wide N1, N2, N3, N4 (stated in full under Boundaries), and:
  - Does not claim that casting from a signed type via castFromSigned (m < n vs m ≥ n) agrees with unsigned zero-extension when x is negative.
  - Does not assert preservation of x.toInt under castFromUnsigned; e.g. 255u8 as i8 = -1.

#### `castFromUnsigned_widened_toNat_eq_mod`

- **Tier:** T0. **Kind:** theorem. **Depth:** shallow.
- **Plain claim:** For any x : BitVec n and widths m, k satisfying WidthLe m k (m ≤ k), truncating/casting x to m bits and then widening/keeping to k bits satisfies (castFromUnsigned k (castFromUnsigned m x)).toNat = x.toNat % 2^m.
- **Lean statement** (`Toy.MachInt.castFromUnsigned_widened_toNat_eq_mod`):

```lean
theorem castFromUnsigned_widened_toNat_eq_mod :
  ∀ {n m k : Nat} (x : BitVec n),
    WidthLe m k → (castFromUnsigned k (castFromUnsigned m x)).toNat = x.toNat % 2 ^ m
-- with the specification predicates unfolded:
  ∀ {n m k : Nat} (x : BitVec n),
    m ≤ k → (castFromUnsigned k (castFromUnsigned m x)).toNat = x.toNat % 2 ^ m
```

- **Hypothesis ledger:**
  - `hle : WidthLe m k` (tight: counterexample `ce_castFromUnsigned_widened_drop_widthLe`). Ensures the second cast from width m to width k does not further truncate the result modulo 2^k. Tight in the sense that it cannot be dropped (counterexample below), but sufficient rather than necessary: the identity also holds whenever n ≤ k (`castFromUnsigned_widened_toNat_eq_mod_of_source_le`), and it holds for every x exactly when m ≤ k ∨ n ≤ k (`castFromUnsigned_widened_toNat_eq_mod_forall_iff`).

  Counterexample `ce_castFromUnsigned_widened_drop_widthLe` (all other hypotheses hold and the conclusion fails):

```lean
theorem ce_castFromUnsigned_widened_drop_widthLe :
  ¬WidthLe 16 8 ∧
    (castFromUnsigned 8 (castFromUnsigned 16 256#32)).toNat ≠ (256#32).toNat % 2 ^ 16
```

- **Non-vacuity witness:** At n = 32, m = 8, k = 32, x = 0x12345678#32: ((x as u8) as u32).toNat = x.toNat % 256. Lean: `nv_castFromUnsigned_widened_toNat_eq_mod`.
- **Cited companion lemmas** (proved; statements hashed in `audit/statements.json`):

```lean
theorem castFromUnsigned_widened_toNat_eq_mod_forall_iff :
  ∀ (n m k : Nat),
    (∀ (x : BitVec n), (castFromUnsigned k (castFromUnsigned m x)).toNat = x.toNat % 2 ^ m) ↔
      m ≤ k ∨ n ≤ k
```

```lean
theorem castFromUnsigned_widened_toNat_eq_mod_of_source_le :
  ∀ {n m k : Nat} (x : BitVec n),
    n ≤ k → (castFromUnsigned k (castFromUnsigned m x)).toNat = x.toNat % 2 ^ m
```

```lean
theorem widened_identity_holds_without_widthLe :
  ¬WidthLe 32 16 ∧
    ∀ (x : BitVec 8), (castFromUnsigned 16 (castFromUnsigned 32 x)).toNat = x.toNat % 2 ^ 32
```

- **Prior art:**
  - The Rust Reference (rust-lang/reference commit c9cc32825b03fc206d9c6fe73e9ca6a2f3576d6c), src/expressions/operator-expr.md ([expr.as.numeric.*]).
  - Lean 4.34.1 core library (leanprover/lean4:v4.34.1, commit 5045d0056413266e57c625dcd7c365b10e377c52), Init/Data/BitVec/Lemmas.lean (toNat_setWidth_of_le) and Init/Data/BitVec/Bootstrap.lean (toNat_setWidth).
- **Design question:** Formalizes composed truncation-then-widening casts such as (x as u8) as u32 = x % 256 under a sufficient width constraint m ≤ k; the exact for-all-x condition is m ≤ k ∨ n ≤ k (`castFromUnsigned_widened_toNat_eq_mod_forall_iff`).
- **Basis:** execution (Lean kernel check) of `castFromUnsigned_widened_toNat_eq_mod` and every Lean name listed above.
- **Basis:** derived (modeling bridge) for the Rust reading: `castFromUnsigned`/`castFromSigned` (Lean `setWidth`/`signExtend`) model integer-to-integer `as` casts as specified by the Rust Reference `[expr.as.numeric]`: same-size casts are no-ops, larger-to-smaller casts truncate, and smaller-to-larger casts zero-extend from unsigned and sign-extend from signed sources (the target's signedness does not affect the bits). Execution cross-check (not proof): `(256u16 as u8) as u16 = 0`, `(128i16 as i8) as i16 = -128`, `(-1i8) as u16 = 65535`, `((-1i8) as u8) as u16 = 255`, and `u8 -> u32 -> u16` preserves every value.
- **Non-claims:** package-wide N1, N2, N3, N4 (stated in full under Boundaries), and:
  - Does not claim WidthLe m k is necessary: the identity also holds whenever n ≤ k, e.g. u8 → u32 → u16 (`castFromUnsigned_widened_toNat_eq_mod_of_source_le`, `widened_identity_holds_without_widthLe`); when k < m and k < n the second cast can truncate again modulo 2^k (`ce_castFromUnsigned_widened_drop_widthLe`; for every such n, m, k the value x = 2^k fails, `castFromUnsigned_widened_toNat_eq_mod_forall_iff`).
  - Does not apply when the intermediate cast passes through a signed type that is then widened (e.g. (x as i8) as u32 sign-extends bit 7 instead of zero-extending).

#### `cast_u32_to_u8_to_u32_eq_mod_256`

- **Tier:** T0. **Kind:** theorem. **Depth:** definitional.
- **Plain claim:** For every x : BitVec 32, casting to 8 bits and back to 32 bits yields (castFromUnsigned 32 (castFromUnsigned 8 x)).toNat = x.toNat % 256.
- **Lean statement** (`Toy.MachInt.cast_u32_to_u8_to_u32_eq_mod_256`):

```lean
theorem cast_u32_to_u8_to_u32_eq_mod_256 :
  ∀ (x : BitVec 32), (castFromUnsigned 32 (castFromUnsigned 8 x)).toNat = x.toNat % 256
```

- **Hypothesis ledger:** no hypotheses.
- **Non-vacuity witness:** At x = 0x12345678#32, (castFromUnsigned 32 (castFromUnsigned 8 x)).toNat = 0x78 = 0x12345678 % 256. Lean: `nv_cast_u32_to_u8_to_u32_eq_mod_256`.
- **Prior art:**
  - The Rust Reference (rust-lang/reference commit c9cc32825b03fc206d9c6fe73e9ca6a2f3576d6c), src/expressions/operator-expr.md ([expr.as.numeric.*]).
- **Design question:** Reference point instantiating `castFromUnsigned_widened_toNat_eq_mod` to record the canonical `(x as u8) as u32 = x % 256` idiom for specification reuse.
- **Basis:** execution (Lean kernel check) of `cast_u32_to_u8_to_u32_eq_mod_256` and every Lean name listed above.
- **Basis:** derived (modeling bridge) for the Rust reading: `castFromUnsigned`/`castFromSigned` (Lean `setWidth`/`signExtend`) model integer-to-integer `as` casts as specified by the Rust Reference `[expr.as.numeric]`: same-size casts are no-ops, larger-to-smaller casts truncate, and smaller-to-larger casts zero-extend from unsigned and sign-extend from signed sources (the target's signedness does not affect the bits). Execution cross-check (not proof): `(256u16 as u8) as u16 = 0`, `(128i16 as i8) as i16 = -128`, `(-1i8) as u16 = 65535`, `((-1i8) as u8) as u16 = 255`, and `u8 -> u32 -> u16` preserves every value.
- **Non-claims:** package-wide N1, N2, N3, N4 (stated in full under Boundaries), and:
  - Does not claim (x as i8) as i32 equals x % 256; sign extension produces values in [-128, 127].

#### `castFromSigned_toInt_eq_of_widthLe`

- **Tier:** T0. **Kind:** theorem. **Depth:** definitional.
- **Plain claim:** For any signed n-bit value x : BitVec n and target width m satisfying WidthLe n m (n ≤ m), sign-extending x to m bits preserves its signed integer value: (castFromSigned m x).toInt = x.toInt.
- **Lean statement** (`Toy.MachInt.castFromSigned_toInt_eq_of_widthLe`):

```lean
theorem castFromSigned_toInt_eq_of_widthLe :
  ∀ {n m : Nat} (x : BitVec n), WidthLe n m → (castFromSigned m x).toInt = x.toInt
-- with the specification predicates unfolded:
  ∀ {n m : Nat} (x : BitVec n), n ≤ m → (castFromSigned m x).toInt = x.toInt
```

- **Hypothesis ledger:**
  - `hle : WidthLe n m` (tight: counterexample `ce_castFromSigned_drop_widthLe`). Ensures no high bits (including the sign bit) are discarded during the signed cast.

  Counterexample `ce_castFromSigned_drop_widthLe` (all other hypotheses hold and the conclusion fails):

```lean
theorem ce_castFromSigned_drop_widthLe :
  ¬WidthLe 16 8 ∧ (castFromSigned 8 128#16).toInt ≠ (128#16).toInt
```

- **Non-vacuity witness:** At n = 8, m = 16, x = -17#8: (castFromSigned 16 (-17#8)).toInt = -17. Lean: `nv_castFromSigned_toInt_eq_of_widthLe`.
- **Prior art:**
  - The Rust Reference (rust-lang/reference commit c9cc32825b03fc206d9c6fe73e9ca6a2f3576d6c), src/expressions/operator-expr.md ([expr.as.numeric.*]) ('Casting from a smaller integer to a larger integer will ... sign-extend if the source is signed').
  - Lean 4.34.1 core library (leanprover/lean4:v4.34.1, commit 5045d0056413266e57c625dcd7c365b10e377c52), Init/Data/BitVec/Lemmas.lean (toInt_signExtend_of_le).
- **Design question:** Establishes that widening signed casts are value-preserving in toInt (even when targeting an unsigned wider type, where bit-level sign extension occurs before unsigned reinterpretation).
- **Basis:** execution (Lean kernel check) of `castFromSigned_toInt_eq_of_widthLe` and every Lean name listed above.
- **Basis:** derived (modeling bridge) for the Rust reading: `castFromUnsigned`/`castFromSigned` (Lean `setWidth`/`signExtend`) model integer-to-integer `as` casts as specified by the Rust Reference `[expr.as.numeric]`: same-size casts are no-ops, larger-to-smaller casts truncate, and smaller-to-larger casts zero-extend from unsigned and sign-extend from signed sources (the target's signedness does not affect the bits). Execution cross-check (not proof): `(256u16 as u8) as u16 = 0`, `(128i16 as i8) as i16 = -128`, `(-1i8) as u16 = 65535`, `((-1i8) as u8) as u16 = 255`, and `u8 -> u32 -> u16` preserves every value.
- **Non-claims:** package-wide N1, N2, N3, N4 (stated in full under Boundaries), and:
  - Does not preserve x.toNat for negative x (e.g. (-1i8) as u16 has toNat = 65535 ≠ 255 = (-1i8).toNat).
  - Does not hold when m < n; narrowing truncates bits (ce_castFromSigned_drop_widthLe).

#### `reinterpretCast_characterization`

- **Tier:** T0. **Kind:** characterization. **Depth:** definitional.
- **Plain claim:** For any bitwidth n and x : BitVec n, same-width reinterpretation reinterpretCast x satisfies (reinterpretCast x).toNat = if x.toInt < 0 then x.toInt + 2^n else x.toInt, and (reinterpretCast x).toInt = Int.bmod x.toNat (2^n).
- **Lean statement** (`Toy.MachInt.reinterpretCast_characterization`):

```lean
theorem reinterpretCast_characterization :
  ∀ {n : Nat} (x : BitVec n),
    ((↑(reinterpretCast x).toNat : Int) =
        if x.toInt < 0 then x.toInt + (↑(2 ^ n) : Int) else x.toInt) ∧
      (reinterpretCast x).toInt = (↑x.toNat : Int).bmod (2 ^ n)
```

- **Hypothesis ledger:** no hypotheses.
- **Non-vacuity witness:** At n = 8, x = -17#8: (reinterpretCast (-17#8)).toNat = 239 = -17 + 256 and (reinterpretCast (-17#8)).toInt = -17 = Int.bmod 239 256. Lean: `nv_reinterpretCast_characterization`.
- **Prior art:**
  - The Rust Reference (rust-lang/reference commit c9cc32825b03fc206d9c6fe73e9ca6a2f3576d6c), src/expressions/operator-expr.md ([expr.as.numeric.*]) ('Casting between two integers of the same size (e.g. i32 -> u32) is a no-op').
  - Lean 4.34.1 core library (leanprover/lean4:v4.34.1, commit 5045d0056413266e57c625dcd7c365b10e377c52), Init/Data/BitVec/Lemmas.lean (toInt_eq_msb_cond, toInt_eq_toNat_bmod).
- **Design question:** Reference point giving the two-way mathematical bridge between i<n> and u<n> values under same-width `as` reinterpretation (`reinterpretCast := id`).
- **Basis:** execution (Lean kernel check) of `reinterpretCast_characterization` and every Lean name listed above.
- **Basis:** derived (modeling bridge) for the Rust reading: `castFromUnsigned`/`castFromSigned` (Lean `setWidth`/`signExtend`) model integer-to-integer `as` casts as specified by the Rust Reference `[expr.as.numeric]`: same-size casts are no-ops, larger-to-smaller casts truncate, and smaller-to-larger casts zero-extend from unsigned and sign-extend from signed sources (the target's signedness does not affect the bits). Execution cross-check (not proof): `(256u16 as u8) as u16 = 0`, `(128i16 as i8) as i16 = -128`, `(-1i8) as u16 = 65535`, `((-1i8) as u8) as u16 = 255`, and `u8 -> u32 -> u16` preserves every value.
- **Non-claims:** package-wide N1, N2, N3, N4 (stated in full under Boundaries), and:
  - Does not preserve numerical value across sign change unless 0 ≤ x.toInt (i.e. x.msb = false); negative signed values become x.toInt + 2^n.
  - Does not model casts that simultaneously change width and signedness (where source signedness determines extension before reinterpretation).
  - That same-width integer `as` casts preserve raw bit patterns without changing values is a modeling bridge (`reinterpretCast := id`, confirmed against Rust Reference [expr.as.numeric.int-same-size] and rustc), while the theorem's algebraic identities reduce definitionally to Lean core `BitVec.toInt_eq_msb_cond` and `BitVec.toInt_eq_toNat_bmod`.

#### `cast_roundTrip_widen_then_narrow_of_widthLe`

- **Tier:** T0. **Kind:** theorem. **Depth:** shallow.
- **Plain claim:** For any x : BitVec n and width m satisfying WidthLe n m (n ≤ m), widening then narrowing back is an exact identity for both unsigned (castFromUnsigned n (castFromUnsigned m x) = x) and signed (castFromSigned n (castFromSigned m x) = x) casts.
- **Lean statement** (`Toy.MachInt.cast_roundTrip_widen_then_narrow_of_widthLe`):

```lean
theorem cast_roundTrip_widen_then_narrow_of_widthLe :
  ∀ {n m : Nat} (x : BitVec n),
    WidthLe n m →
      castFromUnsigned n (castFromUnsigned m x) = x ∧ castFromSigned n (castFromSigned m x) = x
-- with the specification predicates unfolded:
  ∀ {n m : Nat} (x : BitVec n),
    n ≤ m →
      castFromUnsigned n (castFromUnsigned m x) = x ∧ castFromSigned n (castFromSigned m x) = x
```

- **Hypothesis ledger:**
  - `hle : WidthLe n m` (tight: counterexample `ce_cast_roundTrip_drop_widthLe`, `ce_cast_roundTrip_drop_widthLe_canonical`). Prevents intermediate truncation when passing through width m.

  Counterexample `ce_cast_roundTrip_drop_widthLe` (states the facts from which the failure follows; the canonical form is `ce_cast_roundTrip_drop_widthLe_canonical` below):

```lean
theorem ce_cast_roundTrip_drop_widthLe :
  ¬WidthLe 16 8 ∧
    castFromUnsigned 16 (castFromUnsigned 8 256#16) ≠ 256#16 ∧
      castFromSigned 16 (castFromSigned 8 128#16) ≠ 128#16
```

  Counterexample `ce_cast_roundTrip_drop_widthLe_canonical` (all other hypotheses hold and the conclusion fails):

```lean
theorem ce_cast_roundTrip_drop_widthLe_canonical :
  ¬WidthLe 16 8 ∧
    ¬(castFromUnsigned 16 (castFromUnsigned 8 256#16) = 256#16 ∧
        castFromSigned 16 (castFromSigned 8 256#16) = 256#16)
```

- **Non-vacuity witness:** At n = 8, m = 16: (200u8 as u16) as u8 = 200u8 and (-17i8 as i16) as i8 = -17i8. Lean: `nv_cast_roundTrip_widen_then_narrow_of_widthLe`.
- **Prior art:**
  - The Rust Reference (rust-lang/reference commit c9cc32825b03fc206d9c6fe73e9ca6a2f3576d6c), src/expressions/operator-expr.md ([expr.as.numeric.*]).
  - Lean 4.34.1 core library (leanprover/lean4:v4.34.1, commit 5045d0056413266e57c625dcd7c365b10e377c52), Init/Data/BitVec/Lemmas.lean (toNat_setWidth_of_le, toInt_signExtend_of_le).
- **Design question:** Separates lossless cast round trips (widen-then-narrow) from lossy ones (narrow-then-widen) and mixed-signedness reordering hazards.
- **Basis:** execution (Lean kernel check) of `cast_roundTrip_widen_then_narrow_of_widthLe` and every Lean name listed above.
- **Basis:** derived (modeling bridge) for the Rust reading: `castFromUnsigned`/`castFromSigned` (Lean `setWidth`/`signExtend`) model integer-to-integer `as` casts as specified by the Rust Reference `[expr.as.numeric]`: same-size casts are no-ops, larger-to-smaller casts truncate, and smaller-to-larger casts zero-extend from unsigned and sign-extend from signed sources (the target's signedness does not affect the bits). Execution cross-check (not proof): `(256u16 as u8) as u16 = 0`, `(128i16 as i8) as i16 = -128`, `(-1i8) as u16 = 65535`, `((-1i8) as u8) as u16 = 255`, and `u8 -> u32 -> u16` preserves every value.
- **Non-claims:** package-wide N1, N2, N3, N4 (stated in full under Boundaries), and:
  - Does not hold in the opposite order (narrowing then widening loses high bits; see ce_cast_roundTrip_narrow_then_widen).
  - Does not claim that cast order is irrelevant when both width and signedness change: (-1i8) as u16 = 65535 ≠ 255 = ((-1i8) as u8) as u16.

#### `ce_cast_roundTrip_narrow_then_widen`

- **Tier:** T0. **Kind:** counterexample. **Depth:** definitional.
- **Plain claim:** Narrowing then widening does not preserve values, unsigned or signed: castFromUnsigned 16 (castFromUnsigned 8 256#16) ≠ 256#16 and castFromSigned 16 (castFromSigned 8 128#16) ≠ 128#16; and sign-extending a signed value differs from first reinterpreting it as unsigned and then zero-extending: castFromSigned 16 (-1#8) ≠ castFromUnsigned 16 (reinterpretCast (-1#8)).
- **Lean statement** (`Toy.MachInt.ce_cast_roundTrip_narrow_then_widen`):

```lean
theorem ce_cast_roundTrip_narrow_then_widen :
  castFromUnsigned 16 (castFromUnsigned 8 256#16) ≠ 256#16 ∧
    castFromSigned 16 (castFromSigned 8 128#16) ≠ 128#16 ∧
      castFromSigned 16 (-1#8) ≠ castFromUnsigned 16 (reinterpretCast (-1#8))
```

- **Hypothesis ledger:** no hypotheses.
- **Non-vacuity witness:** Self-witnessing concrete counterexample on BitVec 8 and BitVec 16, cross-checked against rustc (program `support/rustc_semantics_checks.rs`, recorded output `support/rustc_checks_output.txt`). Lean: `ce_cast_roundTrip_narrow_then_widen`.
- **Prior art:**
  - The Rust Reference (rust-lang/reference commit c9cc32825b03fc206d9c6fe73e9ca6a2f3576d6c), src/expressions/operator-expr.md ([expr.as.numeric.*]).
- **Design question:** Documents the concrete counterexamples where cast round trips and cast reassociations fail.
- **Basis:** execution (Lean kernel check) of `ce_cast_roundTrip_narrow_then_widen` and every Lean name listed above.
- **Basis:** derived (modeling bridge) for the Rust reading: `castFromUnsigned`/`castFromSigned` (Lean `setWidth`/`signExtend`) model integer-to-integer `as` casts as specified by the Rust Reference `[expr.as.numeric]`: same-size casts are no-ops, larger-to-smaller casts truncate, and smaller-to-larger casts zero-extend from unsigned and sign-extend from signed sources (the target's signedness does not affect the bits). In Rust terms the three conjuncts compare `(256u16 as u8) as u16` with `256u16`, `(128i16 as i8) as i16` with `128i16`, and `(-1i8) as u16` with `((-1i8) as u8) as u16`. Execution cross-check (not proof): `(256u16 as u8) as u16 = 0`, `(128i16 as i8) as i16 = -128`, `(-1i8) as u16 = 65535`, `((-1i8) as u8) as u16 = 255`, and `u8 -> u32 -> u16` preserves every value.
- **Non-claims:** package-wide N1, N2, N3, N4 (stated in full under Boundaries), and:
  - Does not claim that narrowing-then-widening fails when the source value already fits in the narrower target type.

## Boundaries

### Non-claims

Package-wide non-claims (N1–N3 are on every card; N4 on every cast card, i.e. every card of Result 6; N5 on every card whose Rust reading involves plain operators, i.e. every card of Results 1, 2, 3 and 5):

- **N1.** No claim is made about floating-point types. Ring identities do not transfer to f32/f64, and as casts from floats to integers round toward zero and saturate (NaN becomes 0) rather than reducing modulo 2^m.
- **N2.** `usize`/`isize` are not modelled. Their width depends on the target; results apply to them only by instantiating `n` with a stated target's pointer width (for example treating `usize`/`isize` as `u64`/`i64` at `n = 64` on a stated 64-bit target), which these results do not fix.
- **N3.** No claim is made about C or C++. There, signed overflow, INT_MIN / -1, INT_MIN % -1 (C11), and shifts by at least the bit width are undefined behaviour; operands narrower than int are promoted before arithmetic; and conversions of out-of-range values to signed types are implementation-defined in C (and were in C++ before C++20). Even where C and Rust agree (e.g. truncating /), these results are stated for the Rust model only. For a taxonomy and empirical study of integer overflow in C/C++ programs, see W. Dietz, P. Li, J. Regehr, V. Adve, "Understanding Integer Overflow in C/C++", ICSE 2012, pp. 760-770, DOI 10.1109/ICSE.2012.6227142; it is cited only as the C/C++ contrast, not as support for any result here.
- **N4.** Only integer-to-integer `as` casts between fixed widths are covered. No claim is made about `bool`/`char`/enum/pointer casts, `From`/`TryFrom` conversions (which reject out-of-range values), or float casts.
- **N5.** Wrapping of plain `+`, `-`, `*` and masking of `<<`/`>>` when overflow checks are disabled is `rustc` behaviour. The Rust Reference permits either a panic or a wrapped value in such builds. Only explicitly wrapping APIs (the `wrapping_*` and `overflowing_*` methods and `Wrapping<T>`) guarantee wrapping.

Result-specific non-claims:

- `evalWrap_toNat_eq_emod`:
  - Does not claim that checked or plain overflow-checked evaluation agrees with wrapping evaluation; intermediate overflow causes checked evaluation to return none and plain evaluation to panic (see ce_checked_add_sub_intermediate_overflow).
  - Does not apply to division (/ or %), remainder, shifts (<< or >>), or ordering comparisons (<); see Results 3, 4, and 5.
  - Only unconditional identities transfer. An equation proved over `Int` using hypotheses about the variables (ranges, signs, nonzero divisors) need not hold in wrapping arithmetic. Conversely, an equation that holds in wrapping arithmetic need not hold over `Int` (e.g. `64 * (4 * x) = 0` on `u8`/`i8` or `128 * (x + x) = 0` on `u8`; see `ce_evalWrap_eq_not_imp_intRingIdentity`).
- `evalWrap_toInt_eq_bmod`:
  - Does not claim that signed wrapping evaluation equals unreduced mathematical Int evaluation when intermediate or final results fall outside InSignedRange n.
  - Does not apply to C/C++ signed integer arithmetic, where signed overflow is undefined behavior rather than two's-complement wrapping.
  - Does not apply to division, remainder, shifts, or signed ordering (<).
- `evalWrap_eq_of_intRingIdentity`:
  - Does not transfer identities under checked or plain overflow-checked evaluation: (a + b) - b panics on overflow even when a is in range (see ce_checked_add_sub_intermediate_overflow).
  - Only unconditional identities transfer. An equation proved over `Int` using hypotheses about the variables (ranges, signs, nonzero divisors) need not hold in wrapping arithmetic. Conversely, an equation that holds in wrapping arithmetic need not hold over `Int` (e.g. `64 * (4 * x) = 0` on `u8`/`i8` or `128 * (x + x) = 0` on `u8`; see `ce_evalWrap_eq_not_imp_intRingIdentity`).
  - Does not apply to expressions containing division, remainder, shifts, or comparisons.
- `evalCheckedU_sound`:
  - Does not assert that evalCheckedU succeeds whenever only the final value evalInt ... e is in InUnsignedRange n; intermediate overflow still returns none (see ce_checked_add_sub_intermediate_overflow).
  - Does not model division, remainder, or shifts (see Results 4 and 5).
  - `.lit k` stands for a typed constant value, not a Rust literal token. In Rust an out-of-range literal is a compile-time error (deny-by-default `overflowing_literals` lint) or is truncated, never a runtime panic. Unary minus applied directly to a literal never overflows (`-128_i8 == i8::MIN`). Unary minus does not exist on unsigned types. The model's `none` results for these cases have no Rust counterpart, and `SubexprsInRange` over-approximates the obligation for them.
- `evalCheckedU_complete`:
  - Does not weaken SubexprsInRange to checking only the root value InUnsignedRange n (evalInt ... e); (200u8 + 100u8) - 100u8 refutes that weakening (ce_checkedU_add_sub_intermediate_overflow).
  - Does not assert that SubexprsInRange holds without verifier overflow proof obligations.
  - `.lit k` stands for a typed constant value, not a Rust literal token. In Rust an out-of-range literal is a compile-time error (deny-by-default `overflowing_literals` lint) or is truncated, never a runtime panic. Unary minus applied directly to a literal never overflows (`-128_i8 == i8::MIN`). Unary minus does not exist on unsigned types. The model's `none` results for these cases have no Rust counterpart, and `SubexprsInRange` over-approximates the obligation for them.
- `evalCheckedU_isSome_iff_subexprsInRange`:
  - Does not claim that failing `SubexprsInRange` implies the final expression value is out of range (`ce_checkedU_add_sub_intermediate_overflow`).
  - `.lit k` stands for a typed constant value, not a Rust literal token. In Rust an out-of-range literal is a compile-time error (deny-by-default `overflowing_literals` lint) or is truncated, never a runtime panic. Unary minus applied directly to a literal never overflows (`-128_i8 == i8::MIN`). Unary minus does not exist on unsigned types. The model's `none` results for these cases have no Rust counterpart, and `SubexprsInRange` over-approximates the obligation for them.
- `evalCheckedS_sound`:
  - Does not assert that evalCheckedS succeeds when only the final result is in InSignedRange n.
  - `.lit k` stands for a typed constant value, not a Rust literal token. In Rust an out-of-range literal is a compile-time error (deny-by-default `overflowing_literals` lint) or is truncated, never a runtime panic. Unary minus applied directly to a literal never overflows (`-128_i8 == i8::MIN`). Unary minus does not exist on unsigned types. The model's `none` results for these cases have no Rust counterpart, and `SubexprsInRange` over-approximates the obligation for them.
- `evalCheckedS_complete`:
  - Does not allow substituting root-only range checks for SubexprsInRange (InSignedRange n); (100i8 + 50i8) - 50i8 refutes that weakening (ce_checkedS_add_sub_intermediate_overflow).
  - Does not claim signed range equals -(2^(n-1))..2^(n-1)-1 at n = 0; at n = 0, sMinVal 0 = sMaxVal 0 = 0 (see inSignedRange_iff_two_pow_of_posWidth).
  - `.lit k` stands for a typed constant value, not a Rust literal token. In Rust an out-of-range literal is a compile-time error (deny-by-default `overflowing_literals` lint) or is truncated, never a runtime panic. Unary minus applied directly to a literal never overflows (`-128_i8 == i8::MIN`). Unary minus does not exist on unsigned types. The model's `none` results for these cases have no Rust counterpart, and `SubexprsInRange` over-approximates the obligation for them.
- `evalCheckedS_isSome_iff_subexprsInRange`:
  - Does not claim that failing `SubexprsInRange` implies the final expression value is out of range (`ce_checkedS_add_sub_intermediate_overflow`).
  - `.lit k` stands for a typed constant value, not a Rust literal token. In Rust an out-of-range literal is a compile-time error (deny-by-default `overflowing_literals` lint) or is truncated, never a runtime panic. Unary minus applied directly to a literal never overflows (`-128_i8 == i8::MIN`). Unary minus does not exist on unsigned types. The model's `none` results for these cases have no Rust counterpart, and `SubexprsInRange` over-approximates the obligation for them.
- `ce_checked_add_sub_intermediate_overflow`:
  - Does not claim that wrapping evaluation fails to recover a; wrapping evaluation succeeds precisely because ring identities transfer without intermediate range bounds.
  - `.lit k` stands for a typed constant value, not a Rust literal token. In Rust an out-of-range literal is a compile-time error (deny-by-default `overflowing_literals` lint) or is truncated, never a runtime panic. Unary minus applied directly to a literal never overflows (`-128_i8 == i8::MIN`). Unary minus does not exist on unsigned types. The model's `none` results for these cases have no Rust counterpart, and `SubexprsInRange` over-approximates the obligation for them.
- `not_ult_allOnes_add_one`:
  - Does not claim that x + 1#n wraps strictly below x at n = 0 (at n = 0, BitVec.allOnes 0 = 0#0 so 0 < 0 fails without wrapping strictly downward); strict wrap-below requires PosWidth n (ult_allOnes_add_one_allOnes_of_posWidth).
  - Does not rule out Ult x (x + 1#n) when restricted to x ≠ BitVec.allOnes n (ult_add_one_iff_ne_allOnes; see pc_ult_add_one_of_lt_uMax).
  - The impossibility concerns wrapping addition only. It is escaped by (i) restricting to `x < MAX` (positive control), (ii) checked or overflow-checked addition, where `x + 1` at `MAX` panics or returns `None` instead of producing a false comparison, and (iii) unbounded integers. No claim is made about how C compilers treat `x + 1 > x` for signed types (they may fold it to true because overflow is undefined).
- `not_slt_intMax_add_one`:
  - Does not rule out Slt x (x + 1#n) when restricted to x ≠ BitVec.intMax n (slt_add_one_iff_ne_intMax; see pc_slt_add_one_of_lt_sMax, which holds even at n = 1 where -1 + 1 = 0 > -1).
  - The impossibility concerns wrapping addition only. It is escaped by (i) restricting to `x < MAX` (positive control), (ii) checked or overflow-checked addition, where `x + 1` at `MAX` panics or returns `None` instead of producing a false comparison, and (iii) unbounded integers. No claim is made about how C compilers treat `x + 1 > x` for signed types (they may fold it to true because overflow is undefined).
- `ult_add_right_of_noUAddOverflow`:
  - Does not hold if only a + c is overflow-free while b + c wraps (ce_ult_add_right_drop_noUAddOverflow).
  - Does not require separately hypothesizing NoUAddOverflow a c, because Ult a b and NoUAddOverflow b c entail NoUAddOverflow a c (`noUAddOverflow_of_ult_of_noUAddOverflow`, unlike signed addition monotonicity with negative c).
  - The no-overflow hypotheses are sufficient, not necessary. When both sums wrap (in the same direction, for signed types), the order is still preserved, e.g. `200u8 < 250u8` and `200u8.wrapping_add(100) = 44 < 94 = 250u8.wrapping_add(100)`. Each guard is tight only in the sense that it cannot be dropped on its own.
- `slt_add_right_of_noSAddOverflow`:
  - Does not allow dropping either NoSAddOverflow a c (negative c can underflow a + c alone) or NoSAddOverflow b c (positive c can overflow b + c alone).
  - Does not claim that both sums must have the same sign, nor that monotonicity fails only at MAX.
  - The no-overflow hypotheses are sufficient, not necessary. When both sums wrap in the same direction, the order is still preserved, e.g. `100i8 < 120i8` and `100i8.wrapping_add(100) = -56 < -36 = 120i8.wrapping_add(100)` (`ce_slt_add_right_both_wrap` proves `Slt (100#8 + 100#8) (120#8 + 100#8)` although both sums overflow). Each guard is tight only in the sense that it cannot be dropped on its own.
- `ult_add_right_iff_uaddOverflow_eq`:
  - Does not extend to arbitrary c when `¬ Ult a b`; e.g., when a ≥ b, both sums may avoid overflow while `Ult (a + c) (b + c)` remains false (`ce_ult_add_right_iff_drop_hlt`).
  - Does not imply `NoUAddOverflow b c` when `Ult (a + c) (b + c)` holds; both sums may overflow together (`ce_ult_add_right_both_wrap`).
- `slt_add_right_iff_saddOverflow_eq`:
  - Does not extend to arbitrary a, b when `¬ Slt a b` (`ce_slt_add_right_iff_drop_hlt`).
  - Does not imply `NoSAddOverflow a c` or `NoSAddOverflow b c` when `Slt (a + c) (b + c)` holds; both sums may overflow in the same direction (`ce_slt_add_right_both_wrap`).
- `checkedUDiv_and_checkedURem_eq_nat_div_mod`:
  - Does not claim that Lean's total BitVec / 0#n = 0#n agrees with Rust; Rust panics on division/remainder by zero regardless of -C overflow-checks.
  - Does not apply to signed division/remainder, which has an additional MIN / -1 overflow trap.
- `checkedSDiv_eq_some_and_toInt_eq_tdiv`:
  - Does not match Lean's default Int division a.toInt / b.toInt (which is Int.ediv) when a is negative and b does not divide a (see ce_sdiv_srem_ne_int_ediv_emod).
  - Does not claim that MIN / -1 wraps silently under plain / in release mode; Rust panics on MIN / -1 even when -C overflow-checks is disabled.
- `checkedSRem_eq_some_and_toInt_eq_tmod`:
  - Does not match Lean's default Int remainder a.toInt % b.toInt (which is Int.emod, always nonnegative for b ≠ 0) when a is negative and not divisible by b (see ce_sdiv_srem_ne_int_ediv_emod).
  - Does not succeed on (MIN, -1) merely because the mathematical remainder 0 fits in InSignedRange n; checkedSRem returns none and plain % panics unconditionally (see checkedSRem_intMin_negOne_eq_none).
- `tdiv_not_inSignedRange_iff_intMin_negOne`:
  - Does not claim that checkedSDiv succeeds whenever a.toInt.tdiv b.toInt is in InSignedRange n: division by zero yields tdiv = 0 ∈ InSignedRange n yet checkedSDiv returns none.
  - Does not characterize remainder overflow: tmod never leaves InSignedRange n, yet checkedSRem still returns none at (MIN, -1).
  - This characterizes when the mathematical truncating quotient leaves the signed range. It is not a characterization of when Rust's `/` panics: division by zero also panics, although `Int.tdiv x 0 = 0` is in range.
- `checkedSRem_intMin_negOne_eq_none`:
  - Does not claim that the mathematical remainder fails to fit in i<n>; the none outcome in our model reflects a documented Rust rule (core docs: 'invalid due to implementation artifacts'; Reference: 'for legacy reasons'), encoded directly in checkedSRem/checkedSRemEuclid (`derived (modeling bridge)`, cross-checked with rustc).
  - Does not apply to unsigned types, which have no -1 value causing division overflow.
- `checkedSDivEuclid_eq_some_and_toInt_eq_ediv`:
  - Does not match Rust's `/` operator (which is truncating Int.tdiv, not Int.ediv).
  - Does not avoid the (MIN, -1) trap.
- `checkedSRemEuclid_eq_some_and_toInt_eq_emod`:
  - Does not match Rust's `%` operator (which is truncating Int.tmod) when a < 0 and b does not divide a.
  - Does not fail when b = MIN and a = -1: (-1i8).rem_euclid (-128i8) = 127 fits in i8 via wrapping addition of b.abs.
- `ce_sdiv_srem_ne_int_ediv_emod`:
  - Does not claim that sdiv/srem disagree with Int.ediv/Int.emod for nonnegative dividends a ≥ 0; disagreement requires a < 0 and ¬ (b ∣ a).
- `wrappingShl_eq_mul_twoPow_of_shiftInBounds`:
  - Does not hold when k ≥ n: wrapping_shl masks k modulo n rather than shifting bits out to zero (see ce_wrappingShl_overshift_ne_mul_twoPow).
  - Does not equate wrapping_shl with Rust's unbounded_shl (which yields 0 for k ≥ n).
  - `ShiftInBounds n k` (equivalently, `checked_shl` returning `Some`, or `<<` not panicking under overflow checks) does not imply that no set bits are shifted out: `128u8.checked_shl(1) == Some(0)` (see `ce_checkedShl_drops_high_bits_without_none`). Replacing `x << k` by the unbounded integer `x * 2^k` additionally requires `x * 2^k < 2^n` (unsigned) or the signed analogue, which neither the operator nor `checked_shl` checks.
  - The model defines wrapping shifts by masking `k % n`, which equals Rust `core::num`'s bitmask `k & (BITS - 1)` for every shift count `k` if and only if `n` is a power of two (`mod_eq_and_mask_forall_iff_isPowerOfTwo`; the 'if' direction is `mod_twoPow_eq_and_mask`), and diverges at other widths, e.g. `n = 3, k = 4` (`ce_wrappingShl_mod_ne_and_mask_nonPowTwo`). All Rust fixed-width integer types have power-of-two widths. Plain shift operators (`<<`/`>>`, which panic under overflow checks and mask under `rustc` when checks are disabled) are not modeled by a separate `Outcome` evaluator.
- `wrappingUShr_and_wrappingSShr_of_shiftInBounds`:
  - Does not equate signed arithmetic right shift `>>` with Rust's signed `/` by 2^k (which truncates toward 0, e.g. -1 >> 1 = -1 ≠ 0 = (-1).tdiv 2; see ce_sshiftRight_ne_sdiv_twoPow).
  - Does not hold when k ≥ n (see ce_wrappingShr_overshift).
  - The model defines wrapping shifts by masking `k % n`, which equals Rust `core::num`'s bitmask `k & (BITS - 1)` for every shift count `k` if and only if `n` is a power of two (`mod_eq_and_mask_forall_iff_isPowerOfTwo`; the 'if' direction is `mod_twoPow_eq_and_mask`), and diverges at other widths, e.g. `n = 3, k = 4` (`ce_wrappingShl_mod_ne_and_mask_nonPowTwo`). All Rust fixed-width integer types have power-of-two widths. Plain shift operators (`<<`/`>>`, which panic under overflow checks and mask under `rustc` when checks are disabled) are not modeled by a separate `Outcome` evaluator.
- `ce_wrappingShl_overshift_ne_mul_twoPow`:
  - Does not assert that plain `<<` masks k as a language guarantee when overflow checks are disabled; masking in unchecked builds is rustc behaviour while the Reference permits either panic or wrapping (and RFC 560's unconditional shift-masking rule is superseded by [expr.operator.int-overflow.shift]).
  - The model defines wrapping shifts by masking `k % n`, which equals Rust `core::num`'s bitmask `k & (BITS - 1)` for every shift count `k` if and only if `n` is a power of two (`mod_eq_and_mask_forall_iff_isPowerOfTwo`; the 'if' direction is `mod_twoPow_eq_and_mask`), and diverges at other widths, e.g. `n = 3, k = 4` (`ce_wrappingShl_mod_ne_and_mask_nonPowTwo`). All Rust fixed-width integer types have power-of-two widths. Plain shift operators (`<<`/`>>`, which panic under overflow checks and mask under `rustc` when checks are disabled) are not modeled by a separate `Outcome` evaluator.
- `ce_checkedShl_drops_high_bits_without_none`:
  - Does not claim `checked_shl` returns `None` when nonzero bits are shifted out; Rust's `checked_shl` checks only `rhs < BITS` (unlike the unstable `exact_shl`, feature `exact_bitshifts` at Rust 1.91.0, renamed `shl_exact` on later nightlies).
  - The model defines wrapping shifts by masking `k % n`, which equals Rust `core::num`'s bitmask `k & (BITS - 1)` for every shift count `k` if and only if `n` is a power of two (`mod_eq_and_mask_forall_iff_isPowerOfTwo`; the 'if' direction is `mod_twoPow_eq_and_mask`), and diverges at other widths, e.g. `n = 3, k = 4` (`ce_wrappingShl_mod_ne_and_mask_nonPowTwo`). All Rust fixed-width integer types have power-of-two widths. Plain shift operators (`<<`/`>>`, which panic under overflow checks and mask under `rustc` when checks are disabled) are not modeled by a separate `Outcome` evaluator.
- `castFromUnsigned_toNat_eq_mod`:
  - Does not claim that casting from a signed type via castFromSigned (m < n vs m ≥ n) agrees with unsigned zero-extension when x is negative.
  - Does not assert preservation of x.toInt under castFromUnsigned; e.g. 255u8 as i8 = -1.
- `castFromUnsigned_widened_toNat_eq_mod`:
  - Does not claim WidthLe m k is necessary: the identity also holds whenever n ≤ k, e.g. u8 → u32 → u16 (`castFromUnsigned_widened_toNat_eq_mod_of_source_le`, `widened_identity_holds_without_widthLe`); when k < m and k < n the second cast can truncate again modulo 2^k (`ce_castFromUnsigned_widened_drop_widthLe`; for every such n, m, k the value x = 2^k fails, `castFromUnsigned_widened_toNat_eq_mod_forall_iff`).
  - Does not apply when the intermediate cast passes through a signed type that is then widened (e.g. (x as i8) as u32 sign-extends bit 7 instead of zero-extending).
- `cast_u32_to_u8_to_u32_eq_mod_256`:
  - Does not claim (x as i8) as i32 equals x % 256; sign extension produces values in [-128, 127].
- `castFromSigned_toInt_eq_of_widthLe`:
  - Does not preserve x.toNat for negative x (e.g. (-1i8) as u16 has toNat = 65535 ≠ 255 = (-1i8).toNat).
  - Does not hold when m < n; narrowing truncates bits (ce_castFromSigned_drop_widthLe).
- `reinterpretCast_characterization`:
  - Does not preserve numerical value across sign change unless 0 ≤ x.toInt (i.e. x.msb = false); negative signed values become x.toInt + 2^n.
  - Does not model casts that simultaneously change width and signedness (where source signedness determines extension before reinterpretation).
  - That same-width integer `as` casts preserve raw bit patterns without changing values is a modeling bridge (`reinterpretCast := id`, confirmed against Rust Reference [expr.as.numeric.int-same-size] and rustc), while the theorem's algebraic identities reduce definitionally to Lean core `BitVec.toInt_eq_msb_cond` and `BitVec.toInt_eq_toNat_bmod`.
- `cast_roundTrip_widen_then_narrow_of_widthLe`:
  - Does not hold in the opposite order (narrowing then widening loses high bits; see ce_cast_roundTrip_narrow_then_widen).
  - Does not claim that cast order is irrelevant when both width and signedness change: (-1i8) as u16 = 65535 ≠ 255 = ((-1i8) as u8) as u16.
- `ce_cast_roundTrip_narrow_then_widen`:
  - Does not claim that narrowing-then-widening fails when the source value already fits in the narrower target type.

### Attractive stronger conclusions that are not established

- Result 1 identifies *a* side-condition-free fragment (ring expressions); it does not claim this fragment is maximal, and it says nothing about division, remainder, shifts or comparisons.
- Result 2 does not say that wrapping evaluation and checked evaluation agree when only the final value is in range: an intermediate overflow makes checked evaluation fail (`ce_checked_add_sub_intermediate_overflow`).
- Result 3's sufficient conditions are not necessary: both sums may wrap and order is still preserved (`ce_ult_add_right_both_wrap`, `ce_slt_add_right_both_wrap`); the exact criteria are the two `_iff_` characterizations.
- Result 4 does not say that `y ≠ 0` and an in-range remainder make `x % y` panic-free: `(MIN, -1)` must still be excluded (`checkedSRem_intMin_negOne_eq_none`). It does not characterize when Rust's `/` panics (division by zero also panics).
- Result 5 does not say that a shift that passes `checked_shl` is multiplication by `2^k` over the integers: set bits can be shifted out (`ce_checkedShl_drops_high_bits_without_none`).
- Result 6 does not say that narrowing then widening is lossless (`ce_cast_roundTrip_narrow_then_widen`), nor that `WidthLe m k` is necessary for the composed unsigned cast identity (it is not; the exact condition is `m ≤ k ∨ n ≤ k`).
- No result says anything about what a particular Rust compiler, optimizer or verifier does beyond the observed `rustc` runs; the Rust readings are modeling claims.

### Escape hatches for the impossibility results

`not_ult_allOnes_add_one` and `not_slt_intMax_add_one` show that `x < x + 1` fails at `MAX` under wrapping addition, at every width. They are defeated by dropping wrapping semantics: (i) restricting to `x < MAX` restores the property (positive controls `pc_ult_add_one_of_lt_uMax`, `pc_slt_add_one_of_lt_sMax`; exact characterizations `ult_add_one_iff_ne_allOnes`, `slt_add_one_iff_ne_intMax`); (ii) checked or overflow-checked addition panics or returns `None` at `MAX` instead of producing a false comparison; (iii) unbounded integers have no `MAX`.

### Tightness status

Every hypothesis of every result is `tight`, with a proved counterexample in which all other hypotheses hold and the conclusion fails. No hypothesis is labelled `harmless` or `unknown`. Several tight hypotheses are sufficient but not necessary; the cards say so explicitly (`NoUAddOverflow b c`, the two `NoSAddOverflow` guards, `WidthLe m k`).

### Disproved or dropped statements

None. Every result in this package is proved exactly as stated; no statement was found false or left unresolved.

## Evidence

**Kernel checks.** `lake build` of `lean/` under `leanprover/lean4:v4.34.1` builds the library `Toy`; its module `Toy.MachInt.Audit` fails to compile unless every declaration of the library depends only on `propext`, `Classical.choice` and `Quot.sound`. `audit/axioms.json` records the axioms of all 449 non-internal declarations; `audit/statements.json` records, for every Lean name referenced by `results.json` (120 names), the SHA-256 of the statement (Lean `repr` of the declaration's type) and of its definition closure (for each package-local constant reachable from the statement: `name : repr(type)`, plus ` := repr(value)` for non-theorems; sorted, newline-joined; theorem bodies are not hashed). Source files: `Defs.lean` (definitions), `Examples.lean` (definition examples and small helper lemmas), `Statements.lean` (main results), `Lemmas.lean` (proof-only lemmas), `Counterexamples.lean`, `Witnesses.lean`, `Supplements.lean` (companion results, canonical counterexamples, extra witnesses), `Audit.lean`.

Per referenced name (axioms from `#print axioms`/`collectAxioms`; hashes from `audit/statements.json`):

| Lean name (`Toy.MachInt.` omitted) | axioms | statement SHA-256 | closure SHA-256 |
| --- | --- | --- | --- |
| `castFromSigned_toInt_eq_of_widthLe` | Classical.choice, Quot.sound, propext | `985f3b2275d42d28245224ed78f1aa345a36d9efcd325f97e0ce2988173cd5ec` | `802f9c5518dabe2a96243eeaf6cc7e8d9cc24f39bf720d8c8f1de056aa69235a` |
| `castFromUnsigned_toNat_eq_mod` | propext | `6810f1dd98c9898249f762e840645421b5130d520095c50dbddbf9bf40b8f43c` | `0aea3399b8df1a3c19b63d9457761875f07dae0287d6016e97e0fe1c86c2f44f` |
| `castFromUnsigned_widened_toNat_eq_mod` | Quot.sound, propext | `fafec78d4e2227dd34a9cb2ce504dd7d5ac3537d5577b4f2cae16409eca37bda` | `5aa70cb5fc51c28a26db52a448ebc566f4a5eeba54b78f4b715a1f25c2470cbc` |
| `castFromUnsigned_widened_toNat_eq_mod_forall_iff` | Classical.choice, Quot.sound, propext | `c285f46696ca58f3cab8ee485d58926af404aeadcf9305f47126ab7841dcc86e` | `0aea3399b8df1a3c19b63d9457761875f07dae0287d6016e97e0fe1c86c2f44f` |
| `castFromUnsigned_widened_toNat_eq_mod_of_source_le` | propext | `10cf32bf29690834ec89ae5d1d30ec732bccc7c15357002e2893c5f2018d23a0` | `0aea3399b8df1a3c19b63d9457761875f07dae0287d6016e97e0fe1c86c2f44f` |
| `cast_roundTrip_widen_then_narrow_of_widthLe` | Classical.choice, Quot.sound, propext | `e58a8da773addb5db020118141a287e006f4594b628c31949a0492f08e1f25c5` | `1487124e1c5658009e98f76eeef42e6fa8a9e185b31ae70b492bbf9424a20af3` |
| `cast_u32_to_u8_to_u32_eq_mod_256` | Quot.sound, propext | `a27a6cb15d87a65dc321fb6ff2c040e81c75bee3015e1980730560afff89fe38` | `0aea3399b8df1a3c19b63d9457761875f07dae0287d6016e97e0fe1c86c2f44f` |
| `ce_castFromSigned_drop_widthLe` | propext | `3f1cba754755ea3e6f028e0303444448b52d2650e90645e920d6f31e76c99218` | `802f9c5518dabe2a96243eeaf6cc7e8d9cc24f39bf720d8c8f1de056aa69235a` |
| `ce_castFromUnsigned_widened_drop_widthLe` | (none) | `bbb4d40118cd1cd453d5076f0b55c28d44fe39fad1528ef882fb978da1e90ba7` | `5aa70cb5fc51c28a26db52a448ebc566f4a5eeba54b78f4b715a1f25c2470cbc` |
| `ce_cast_roundTrip_drop_widthLe` | propext | `38fd26297621cb0c66dd80e4bafcd1bda70b85337232ff11f1a232a032d3e5b2` | `1487124e1c5658009e98f76eeef42e6fa8a9e185b31ae70b492bbf9424a20af3` |
| `ce_cast_roundTrip_drop_widthLe_canonical` | propext | `b08f78b9e9e6a421246bd5e2541b15d0dcd91c5014f592a212ce8515b9c76d8c` | `1487124e1c5658009e98f76eeef42e6fa8a9e185b31ae70b492bbf9424a20af3` |
| `ce_cast_roundTrip_narrow_then_widen` | propext | `922186f2bdf43cedc9701bbde7a8238efb3de7a98d07b99e6384124d3666e035` | `57506bad8f67949acb3054f1b507d1488ad97869a426d8cd494b997cc1bfbbb1` |
| `ce_checkedSDivEuclid_drop_noSDivOverflow` | Classical.choice, Quot.sound, propext | `9cecba0852f2f36bc93cb1792974c0de2155717fb71ba7c3d6e481ad4eba0e4d` | `f68c9895262aff4560906cd900c34fa85b4912bb079bd7e134b71ee67cd6f6c0` |
| `ce_checkedSDivEuclid_drop_nonZeroDiv` | Classical.choice, Quot.sound, propext | `af56f24e91d4a66d9ede87fc63fb33d16c6b5cfd9afaffb8972e14bbb177a926` | `f68c9895262aff4560906cd900c34fa85b4912bb079bd7e134b71ee67cd6f6c0` |
| `ce_checkedSDiv_drop_noSDivOverflow` | Classical.choice, Quot.sound, propext | `a192d435cb02bb1a4cb11760da314827cb4488d8dc90f0d7108498cc8530f7ef` | `4e45f5b033b24b60bd8b77a0737b73f46565d65013626bd2acd0c0bbd44aa0a8` |
| `ce_checkedSDiv_drop_nonZeroDiv` | Classical.choice, Quot.sound, propext | `612e19e22dfc86a692e19087c282cfbcb78a9117c13f602c8e423cb048740b68` | `4e45f5b033b24b60bd8b77a0737b73f46565d65013626bd2acd0c0bbd44aa0a8` |
| `ce_checkedSRemEuclid_drop_noSDivOverflow` | Classical.choice, Quot.sound, propext | `3e600e02d102c768f7573fe2c5e381682ef6db8ace6594b7c53fee2f00cd8990` | `800bdbe36fbfc2e350fb7070833f9a982dcf4198190078111bfb6fdea6417a8d` |
| `ce_checkedSRemEuclid_drop_nonZeroDiv` | Classical.choice, Quot.sound, propext | `466da3ea23f76106badfd8e1e0eecc9924972616ca3d07cd9916aa49de813f08` | `800bdbe36fbfc2e350fb7070833f9a982dcf4198190078111bfb6fdea6417a8d` |
| `ce_checkedSRem_drop_noSDivOverflow` | Classical.choice, Quot.sound, propext | `488ca0064966af41fa4e5aa0a0a4bd61657acbc82974cfd58e17e1e13bc4e958` | `4bf4110a718052b1e2259d83555fba0218433e34d8365be93b98f7d89e7e6dcf` |
| `ce_checkedSRem_drop_nonZeroDiv` | Classical.choice, Quot.sound, propext | `76bb9d60b12022a039134d7e80efb9606b4690b464f3513d4a730ca527cdc22d` | `4bf4110a718052b1e2259d83555fba0218433e34d8365be93b98f7d89e7e6dcf` |
| `ce_checkedSRem_intMin_drop_posWidth` | (none) | `e72cbd6434c702c20224623fdff43bc972c65c5afb0c371bddb0c323f9440133` | `b3d8f405fdeb1020074e4359c2481ae95a8bc75b5875085d354564d82c855604` |
| `ce_checkedSRem_intMin_drop_posWidth_canonical` | propext | `7301b1bc286361e09af52cb9fb47934a59c5db96c5629920342e231d5ce0fcc5` | `92608c25c2c8e33db422bb1dc29128e23c96b9570a9d84e05c0f78a9a47afef0` |
| `ce_checkedS_add_sub_intermediate_overflow` | propext | `47ee531c933a2600fe04323f11d4d84bf129648c2053e03288cc0d4621194fb1` | `4517dbd594b2c8eb79c83cd335c0c2f97b5c8e02973cdeea10263aa1d50a1030` |
| `ce_checkedShl_drops_high_bits_without_none` | (none) | `47ed09491c27f9c832d1c6a84e13c4e9b3d5879b58d4918f30cb76fd75d8ab35` | `3bd909afe2fb0e2e680abea4d6d36e567e4078b7cd61dc13e6bddfb402c22d6d` |
| `ce_checkedUDiv_drop_nonZeroDiv` | Classical.choice, Quot.sound, propext | `201e4ecb060205cd68c0f56de83a42816ac4be2be783740fade4907ac77b59ce` | `f8068d9060d4995a006ccc4331e4d837f5f123fd41fda4ed4d3509e2d1ab57e9` |
| `ce_checkedU_add_sub_intermediate_overflow` | propext | `2f40df7989eed112722daf24e083fe9587e90bf5abf5fb7eeba29e6a6eb8927d` | `4cc12887f9f7bfc84f90779e9ece12c166ea62466b2d20005488d9a648121c1d` |
| `ce_checked_add_sub_intermediate_overflow` | propext | `114d88495d6b29bc021c9ea9ffa6c08bff2aef624575c2ff5ba881a98df777cc` | `99475c516a8bfaf11b6c88988610073fd8b46e49d9e08c1c1c5415e5d100db26` |
| `ce_evalCheckedS_sound_drop_some` | propext | `93e6b4417d95b954764bca6866d1e01c43da002a1854726dc4000de29feea7d8` | `aea424176f1924df25fa77c40fe2a142758f7503fd2c47aa48f6fb7233bf5694` |
| `ce_evalCheckedU_sound_drop_some` | propext | `49c04170aa5f0efbf611fee4c7807e11fb4c749ac51f8c51472b73d959f8c02f` | `98f74eed06f74a3f7300a3353d879c7b7b0a540663e7f96497352ed6f6319608` |
| `ce_evalWrap_eq_drop_intRingIdentity` | propext | `37e3b7d3a095134135e985adc18ae876acb165af2be8ecaf232e7ed1a28ef1c3` | `886de4ff74f0463cac8540e9a569f64532669b870e10ea1a42fed37bda9cc642` |
| `ce_evalWrap_eq_not_imp_intRingIdentity` | Quot.sound, propext | `80daa2f727ab1a1bd0b2e20fa333f74b0f9b0864b0adce394e8715c08e3c83b8` | `886de4ff74f0463cac8540e9a569f64532669b870e10ea1a42fed37bda9cc642` |
| `ce_sdiv_srem_ne_int_ediv_emod` | propext | `96510b80d8afbcb49a3cabc70687cee30b647e7d8703ef59642cf54d1f9c4bf1` | `288a8788d8e73bffcbc4de6dfcb982fd2115634bdfe0f76f579633f1ebf97780` |
| `ce_slt_add_right_both_wrap` | (none) | `f86e9323d1e2162c9869823adff4363877ebaae9e4289b0ca9f128781fb1b0ec` | `0ada6e89ff7b10fa132f1e5df649aa6528135a7b8a362ee07d25d23385cef9e2` |
| `ce_slt_add_right_drop_hlt` | (none) | `4aa2e9eb11636fe5ba197a03a75f111a721455d00960f29bffb1281e2bc52f70` | `0ada6e89ff7b10fa132f1e5df649aa6528135a7b8a362ee07d25d23385cef9e2` |
| `ce_slt_add_right_drop_noSAddOverflow_left` | (none) | `98c591726875c00011f445270d52a91ea70fca53d6207edf66580a898097c93f` | `0ada6e89ff7b10fa132f1e5df649aa6528135a7b8a362ee07d25d23385cef9e2` |
| `ce_slt_add_right_drop_noSAddOverflow_right` | (none) | `ed94810f2996f4e3a48a92ace77741f143f55b3a58b53a27b4e925cce8123da3` | `0ada6e89ff7b10fa132f1e5df649aa6528135a7b8a362ee07d25d23385cef9e2` |
| `ce_slt_add_right_iff_drop_hlt` | (none) | `dfeaa43cac161b74765a67d553cf9346db1356d69f3e0213fabeed1db3495d0f` | `50f144726f115cf6df864807c9dd871af3ade430eacebc011b21d02fdc100025` |
| `ce_sshiftRight_ne_sdiv_twoPow` | propext | `a94fa570c86d8070da6199f8003b9407c614478e4df0d4b6f5906b355f00fa54` | `73ad556b41b2a137dd4dee30d3466824db7cb6e980ee1fb72a65c46d3a62750e` |
| `ce_tdiv_overflow_iff_drop_posWidth` | (none) | `a5781dbc0bb979c20384d4332235514ab726d554ca34e4ad1a7e7da7443dac11` | `d72ddba922f27f7d7de95307b3e47833f5341a13bf7ea108defdb8863f93007e` |
| `ce_tdiv_overflow_iff_drop_posWidth_canonical` | (none) | `0be1998048bff46e3d0a8c3dc2928b5c6e9c737f408a6491fec1fd8c7feafdea` | `d72ddba922f27f7d7de95307b3e47833f5341a13bf7ea108defdb8863f93007e` |
| `ce_ult_add_right_both_wrap` | (none) | `d1c7152ea1254de945478f666a997d1506ab88e9b1bb79ab8711d1c3e25757af` | `82fea6fd02ade8648ab872fa27bb4599f26ee1e6b75dc8412751291f5441a3bf` |
| `ce_ult_add_right_drop_hlt` | (none) | `1354153e84bbfdeead4aafab80a064e2c65360c2fc7602bc3e28707d8729af8c` | `82fea6fd02ade8648ab872fa27bb4599f26ee1e6b75dc8412751291f5441a3bf` |
| `ce_ult_add_right_drop_noUAddOverflow` | (none) | `40ce71ed544a9bf5087c0bbe438e70e3cfb07c1716f603604cdac764776dc5fd` | `82fea6fd02ade8648ab872fa27bb4599f26ee1e6b75dc8412751291f5441a3bf` |
| `ce_ult_add_right_iff_drop_hlt` | (none) | `fabf3561967501902c3cbd93f06facb9017711cbc778f751ca187937fe619c0a` | `3afbf1830aa040c9eeae28b7fbe931fa1c9ba2f37f88fca5f747c8d008b79908` |
| `ce_wrappingShl_drop_shiftInBounds_canonical` | (none) | `ae0b6a5fb3cc27776e8a9a7f35fa72ceb0debe7a0cad5c2df2df360d5edf357e` | `8d9d9a8b7e31f71d64666e319cce8929a200af462f9e20a52c3120139a622f56` |
| `ce_wrappingShl_mod_ne_and_mask_nonPowTwo` | propext | `a907cc7fc0ed797b6772fba994c3c3bdfcf84cebf1b5376d3f316dc93881226d` | `f855338d89fdcea256b60645813b5f52a8b6abd9a84457e8015e896d24f1c063` |
| `ce_wrappingShl_overshift_ne_mul_twoPow` | (none) | `3026a15aa6ae8ab67af73dfa475f46665384c073ebcf7f7de20d5f3853a9e79c` | `52dd18dbce0f554e1a239434ef23a4a70904cf608f988fb9d17671c971414ab4` |
| `ce_wrappingShr_drop_shiftInBounds_canonical` | propext | `84b4b1a1c779616e7e1bb4bb9fb2863928dd8a433e42646962e1c7d9479351c5` | `7c6ee38ff40f67b62b58a76fb842d15c6cd1cb0e1bc770bd69825f68893ab9b7` |
| `ce_wrappingShr_overshift` | propext | `a6dcf588811c7e6d1f8abbc65be7d244a98e5f77fb63d7702af46f91f9a5b1e8` | `7c6ee38ff40f67b62b58a76fb842d15c6cd1cb0e1bc770bd69825f68893ab9b7` |
| `checkedSDivEuclid_eq_some_and_toInt_eq_ediv` | Classical.choice, Quot.sound, propext | `e1f99526ed70ba6b8e4385b18dd6c76ffc01e03c176c0eb639f66b02a6d5c3df` | `f68c9895262aff4560906cd900c34fa85b4912bb079bd7e134b71ee67cd6f6c0` |
| `checkedSDiv_eq_some_and_toInt_eq_tdiv` | Classical.choice, Quot.sound, propext | `81b9b8e20a0930c3ddcc6851c79e12fd62a177df30918ab4fd46131aad6886cf` | `4e45f5b033b24b60bd8b77a0737b73f46565d65013626bd2acd0c0bbd44aa0a8` |
| `checkedSRemEuclid_eq_some_and_toInt_eq_emod` | Classical.choice, Quot.sound, propext | `097e9354b3a7096e7c90fb1af1c3d813c4a64e425b0e88f11bdb501579eae9c7` | `800bdbe36fbfc2e350fb7070833f9a982dcf4198190078111bfb6fdea6417a8d` |
| `checkedSRem_eq_some_and_toInt_eq_tmod` | Classical.choice, Quot.sound, propext | `ff6c6a91992e6ece00c7a94be71c166eee249a12b0eefb241c48218c6cfda899` | `4bf4110a718052b1e2259d83555fba0218433e34d8365be93b98f7d89e7e6dcf` |
| `checkedSRem_intMin_negOne_eq_none` | Classical.choice, Quot.sound, propext | `2fce5efbef0e578529abc2b20eb8872cc69588903fa7e1ed1efbbd961a89a87f` | `92608c25c2c8e33db422bb1dc29128e23c96b9570a9d84e05c0f78a9a47afef0` |
| `checkedSRem_intMin_negOne_eq_none_unconditional` | Classical.choice, Quot.sound, propext | `5eb6d22496181c4cfa343058cfba90e19b2496f039beb131432eaaea675c8567` | `24899886da78b3e37e54dcbf253ac47d7855d05035762f94f60f9724b69ac56d` |
| `checkedUDiv_and_checkedURem_eq_nat_div_mod` | propext | `a79be113d3a0fa301431d5d36a3eeabea1bae5a47a5c98082230ae1234cfd65d` | `f8068d9060d4995a006ccc4331e4d837f5f123fd41fda4ed4d3509e2d1ab57e9` |
| `evalCheckedS_complete` | Classical.choice, Quot.sound, propext | `154b59abf0ba955d0d9d5978b3dc71de19d37b40f5999c598cbea728bec69e6c` | `58dfd4d52d134973ac269a34f4e4033e578a54758804a3efc303ebe68f9f37a9` |
| `evalCheckedS_isSome_iff_subexprsInRange` | Classical.choice, Quot.sound, propext | `f3af21fd6c439fcd4e69ef13d1d2a11269c19d07cc7ff82f1eb8d91473b5dd7d` | `302dc28e78064d0361efc4ddcfef07caa25d3881f39adb0d7c4efa09e9ee6d84` |
| `evalCheckedS_sound` | Classical.choice, Quot.sound, propext | `713df07b838928cf95a0b3bb68c02794950a60c8c9cb0be0325d02a2d147158b` | `884d329f87295d4646cbd02d8b3c4d0dde05b1d9a6e9e1cb0073248d17acb581` |
| `evalCheckedU_complete` | Classical.choice, Quot.sound, propext | `9bfd8070fd6ce3518932c574f4c9b2d224d0b20f6fd5a6cd81684bf02f7e4d25` | `976fbcf98ba00a1948e78070b5770a5c69d3fd230adde81807deb51c949bd010` |
| `evalCheckedU_isSome_iff_subexprsInRange` | Classical.choice, Quot.sound, propext | `bb58dbbd80c443d8e978c86758117228030bbe51c1bd8904cc58c07662f5ecc2` | `6c20f22d5d7fc0094824eaeb49ff910640968f23a8a92f2b9f648a4308654d96` |
| `evalCheckedU_sound` | Classical.choice, Quot.sound, propext | `ab5a7a4743c2bc34989c918c57f67286234b08b5917651cce0b4c456f6dfdf79` | `99f9fac39d7f44c9e45a99090a4410ee1bacc3ebdab33f49152ea287ea36120b` |
| `evalWrap_eq_of_intRingIdentity` | Classical.choice, Quot.sound, propext | `10a9204cacd343f1ec6aed4a8c5436375fbc992619c2db7513e3ba11da499733` | `886de4ff74f0463cac8540e9a569f64532669b870e10ea1a42fed37bda9cc642` |
| `evalWrap_toInt_eq_bmod` | Classical.choice, Quot.sound, propext | `52295dbe026f7a16cd52e96bc202f4b5f13d6fe82d7f37fa5f76e4cbb4394e91` | `a3110cc414bf73da6d3fcb50b0fd3d97ee05a9a7e06083c8cba1af5b72e9630c` |
| `evalWrap_toNat_eq_emod` | Quot.sound, propext | `25fbfd85c2831dae08625b4faf98873410815f6fc085947ea07256c16b48f5ee` | `a3110cc414bf73da6d3fcb50b0fd3d97ee05a9a7e06083c8cba1af5b72e9630c` |
| `inSignedRange_iff_two_pow_of_posWidth` | Classical.choice, Quot.sound, propext | `6be424d9b26912f7cc702189a55d3a5f208f8206d8e25eb400ecd95b30b7df76` | `d72ddba922f27f7d7de95307b3e47833f5341a13bf7ea108defdb8863f93007e` |
| `mod_eq_and_mask_forall_iff_isPowerOfTwo` | Classical.choice, Quot.sound, propext | `4352e883b2348d67d74e59c35c398190cb036d8f22900cf44d2a8b8be1a1ac68` | `e3b0c44298fc1c149afbf4c8996fb92427ae41e4649b934ca495991b7852b855` |
| `mod_twoPow_eq_and_mask` | Classical.choice, Quot.sound, propext | `35122bbcbf64048846d595f876fe31fd6122b6a6258fdd516ef6e614f9cf7db8` | `e3b0c44298fc1c149afbf4c8996fb92427ae41e4649b934ca495991b7852b855` |
| `noUAddOverflow_of_ult_of_noUAddOverflow` | Quot.sound, propext | `1a6b56ba0b94a5911f70404d991b32d4239965e36018ce4cb1b0b917b8d43afb` | `82fea6fd02ade8648ab872fa27bb4599f26ee1e6b75dc8412751291f5441a3bf` |
| `not_slt_add_one_sMax` | Quot.sound, propext | `4380a62cde32a8d19b0daa452b0bf05ad0dbabca05574a44c5856d0379f550da` | `50f144726f115cf6df864807c9dd871af3ade430eacebc011b21d02fdc100025` |
| `not_slt_intMax_add_one` | Quot.sound, propext | `6b83c83c23340ca2fbec3521199da6193a1b3ead4db9271654a7e9d62e8546f2` | `50f144726f115cf6df864807c9dd871af3ade430eacebc011b21d02fdc100025` |
| `not_ult_add_one_uMax` | propext | `bbd12d911faddfffa4fe0851f20003c7965b9c56a80a708a9b16108654315e97` | `3afbf1830aa040c9eeae28b7fbe931fa1c9ba2f37f88fca5f747c8d008b79908` |
| `not_ult_allOnes_add_one` | propext | `78fa2fa2da4c5e5a4385cb4befe98922959b54c8dcb82903790c4675d88bc2ec` | `3afbf1830aa040c9eeae28b7fbe931fa1c9ba2f37f88fca5f747c8d008b79908` |
| `nv_castFromSigned_toInt_eq_of_widthLe` | propext | `e6ff71b531660d80e91bd10a97519e8488177935c18ae932a6ac94e9633e3be8` | `802f9c5518dabe2a96243eeaf6cc7e8d9cc24f39bf720d8c8f1de056aa69235a` |
| `nv_castFromUnsigned_toNat_eq_mod` | (none) | `404ad8c10c54b803f7e878cdbbd390d4b51af90ea41cf0d031698537817a5203` | `0aea3399b8df1a3c19b63d9457761875f07dae0287d6016e97e0fe1c86c2f44f` |
| `nv_castFromUnsigned_widened_toNat_eq_mod` | (none) | `a073b9b90fedfb28beb638f45eb499cb68331463c1f121b90cb6a98cfe792760` | `5aa70cb5fc51c28a26db52a448ebc566f4a5eeba54b78f4b715a1f25c2470cbc` |
| `nv_cast_roundTrip_widen_then_narrow_of_widthLe` | propext | `a18bcc408c0dc54af342d4e099a47e6c942e05f831597125ed0a3d4841128d43` | `1487124e1c5658009e98f76eeef42e6fa8a9e185b31ae70b492bbf9424a20af3` |
| `nv_cast_u32_to_u8_to_u32_eq_mod_256` | (none) | `82215da9123db0998c20f9206dc6b8b1264b9a6f10318f86abb6377fd8758d3f` | `0aea3399b8df1a3c19b63d9457761875f07dae0287d6016e97e0fe1c86c2f44f` |
| `nv_checkedSDivEuclid_eq_some_and_toInt_eq_ediv` | propext | `2121b8ab668edc42e7c5c52c476110a4cf2cac5fbfc8c9b3e2b349dc3d018ae6` | `f68c9895262aff4560906cd900c34fa85b4912bb079bd7e134b71ee67cd6f6c0` |
| `nv_checkedSDiv_eq_some_and_toInt_eq_tdiv` | propext | `b4f3c01a6af743bf51b8c64599898a306021955449e13ab96cde32cb4f514284` | `4e45f5b033b24b60bd8b77a0737b73f46565d65013626bd2acd0c0bbd44aa0a8` |
| `nv_checkedSRemEuclid_eq_some_and_toInt_eq_emod` | propext | `d83f9cdc4344e049c81960d476ba707231c8b3ac6040a12df27c63978e63bde9` | `800bdbe36fbfc2e350fb7070833f9a982dcf4198190078111bfb6fdea6417a8d` |
| `nv_checkedSRem_eq_some_and_toInt_eq_tmod` | propext | `09f052199bbffc7bb1e122f5492cfe23c4331df2f615bc42e1c33904b8290137` | `4bf4110a718052b1e2259d83555fba0218433e34d8365be93b98f7d89e7e6dcf` |
| `nv_checkedSRem_intMin_negOne_eq_none` | propext | `c5cf6cb54cb38d3e28849cdea78bcdf0bd3d3c9922d886ad615d5ad68080cf53` | `c374210ad8c88a2af1f91aeed44f5c5fc8793d389e4b897b1ccc2366b39deb1b` |
| `nv_checkedUDiv_and_checkedURem_eq_nat_div_mod` | propext | `63a11b058688692490ded097f4a84a631727a2ecc26cf2d5e8ac16747bb60a78` | `f8068d9060d4995a006ccc4331e4d837f5f123fd41fda4ed4d3509e2d1ab57e9` |
| `nv_evalCheckedS_complete` | propext | `232d4bbffacd5d9bd39704edacc00dd63cd44200e1f87949b80b91192e5fe969` | `174b2d09bfd802599562efa103970cdf712626e38cad8d453690f49bd2cbddf8` |
| `nv_evalCheckedS_isSome_iff_subexprsInRange` | propext | `5a24e0eb8ec8020a8664faf740cefbec1bf9f1062c79d21d8086ba7639d1dc90` | `2dfccf15b4c362c5b086852e8b18814076230a54468708f3845f9706c64567d9` |
| `nv_evalCheckedS_sound` | propext | `1a5713c1682a408a1c35c7a205bd2b7133baeba071c42eff20881ac7e3d7acff` | `31b80201cbd684f900f0fa616bad1efad6fdff12a114d6856fa1c6bbaa22de04` |
| `nv_evalCheckedU_complete` | propext | `9d4800de9138ecaaa354a881e3c405a4209c49b9523c4aafe969b20e30eb7ff9` | `8abc1a2bd0a0867bf57487492d3a80bab15e04ec3a7463634dceaf9764769fe5` |
| `nv_evalCheckedU_isSome_iff_subexprsInRange` | propext | `4e64730c21bf3d70a9cf63cf84f210ec4a27573b52cbad2b9d02ef251cc78c0e` | `e382fc4317ebdfbc2615dd85c0ad2ad79a134a3db6a582b1a355f6a9a71ae591` |
| `nv_evalCheckedU_sound` | propext | `bbb97e8b61a9f3d080fe3698bb8c58393f7e5eff01b3ee5e772cdd9e7eb3fdd7` | `8f4bd276be47da7d0994a25e2238fc4bd9121804c98f4d9f99fc5f6ac087212b` |
| `nv_evalWrap_eq_of_intRingIdentity` | propext | `31568d9b9b8949d34815e5de10884ffb7cd79233b6047944792b742f69a95eb2` | `cca2160f262e5fe537c33071eaebd6507d9b4cbc014399eb64de8461186149e2` |
| `nv_evalWrap_toInt_eq_bmod` | propext | `70bf0aefc7240347d6ffa539d605fa085f8161e6075583bf04bde1baf5627ac7` | `320557da15ac2a5ebc63b202f9a659216246987d3539010679f3941f51f9317e` |
| `nv_evalWrap_toNat_eq_emod` | propext | `34fab757554ad8806811e40e35aecea9e016a0885301bf1dbec282dc1266a9d7` | `320557da15ac2a5ebc63b202f9a659216246987d3539010679f3941f51f9317e` |
| `nv_not_slt_intMax_add_one` | Quot.sound, propext | `80c664fefc38d50be1fd10b52af498cde81780a158d9b5b3b512f0dcaa44d7d9` | `50f144726f115cf6df864807c9dd871af3ade430eacebc011b21d02fdc100025` |
| `nv_not_ult_allOnes_add_one` | Quot.sound, propext | `c7542774902ce1fc466377796edaa7d29799d2c1831222a80f8d45e3b8ca25be` | `3afbf1830aa040c9eeae28b7fbe931fa1c9ba2f37f88fca5f747c8d008b79908` |
| `nv_reinterpretCast_characterization` | (none) | `bb89429b71fadc4eb614c3ec3cb8806afd6f51ccfbc1c1fd212497ff726e73be` | `aefd7fa58fea36e09cfbdeba34fba54fb275984bb83b66e1017bed0a67737f5a` |
| `nv_slt_add_right_iff_saddOverflow_eq` | (none) | `69a2040adcd15663c8b079cbfcf1436566039c394aa3c0e6e1e4d8b55becdf09` | `50f144726f115cf6df864807c9dd871af3ade430eacebc011b21d02fdc100025` |
| `nv_slt_add_right_of_noSAddOverflow` | (none) | `d6dfe5f05de766eff633aaca10907345a5c3ef6c356175383be6cbc93906b367` | `0ada6e89ff7b10fa132f1e5df649aa6528135a7b8a362ee07d25d23385cef9e2` |
| `nv_tdiv_iff_both_false` | (none) | `893fc50147af66de952e268b91b766eb9614a7e2922efd33d85dce4129f73042` | `d72ddba922f27f7d7de95307b3e47833f5341a13bf7ea108defdb8863f93007e` |
| `nv_tdiv_iff_width_one` | (none) | `5d568705296617cf93a06410ef1a2ef92a137b9984a443d30ad871dcdd89b03f` | `d72ddba922f27f7d7de95307b3e47833f5341a13bf7ea108defdb8863f93007e` |
| `nv_tdiv_not_inSignedRange_iff_intMin_negOne` | (none) | `e428f3c023f8fcfd33e61eeca2e2dcf0824d9d374d4107d0d961616bfbb1058a` | `d72ddba922f27f7d7de95307b3e47833f5341a13bf7ea108defdb8863f93007e` |
| `nv_ult_add_right_iff_uaddOverflow_eq` | (none) | `d9ed2f422a43c97ddf583e2e38aa6e997ba805d2356a06c5e2f58d341a93c9d7` | `3afbf1830aa040c9eeae28b7fbe931fa1c9ba2f37f88fca5f747c8d008b79908` |
| `nv_ult_add_right_of_noUAddOverflow` | (none) | `94e43fbf7fe4e1ede8de6f165f9028e4cf6dce90c39bf349a654c726337dd4df` | `82fea6fd02ade8648ab872fa27bb4599f26ee1e6b75dc8412751291f5441a3bf` |
| `nv_wrappingShl_eq_mul_twoPow_of_shiftInBounds` | (none) | `132e91d36f8b13b30d9655cb571e0626ba6f40952add4e65a182fa81fce9b26b` | `8d9d9a8b7e31f71d64666e319cce8929a200af462f9e20a52c3120139a622f56` |
| `nv_wrappingUShr_and_wrappingSShr_of_shiftInBounds` | propext | `b68a49a09ac785bbd8061567adb01978ceefdd9835602bda620fc38f9504ac3b` | `7c6ee38ff40f67b62b58a76fb842d15c6cd1cb0e1bc770bd69825f68893ab9b7` |
| `pc_slt_add_one_of_lt_sMax` | Classical.choice, Quot.sound, propext | `24632410fd42b63f125c1ca918b018b275f2ff5ae6df978acfe20fb07dd63707` | `50f144726f115cf6df864807c9dd871af3ade430eacebc011b21d02fdc100025` |
| `pc_ult_add_one_of_lt_uMax` | Quot.sound, propext | `39cda5f0833982d7d04610421e8ad9d0e41046aabcdd586bbcf85a85f23b5116` | `3afbf1830aa040c9eeae28b7fbe931fa1c9ba2f37f88fca5f747c8d008b79908` |
| `reinterpretCast_characterization` | Classical.choice, Quot.sound, propext | `ab14c57b29b044f1b3daa48577f3e3d0919916790084cf18aa2230c804babe0e` | `aefd7fa58fea36e09cfbdeba34fba54fb275984bb83b66e1017bed0a67737f5a` |
| `slt_add_one_iff_ne_intMax` | Classical.choice, Quot.sound, propext | `6be6e87572b5fa5608d0632d93ecbd6365fb3234e4e5f95d5545ac757ef3b0c7` | `50f144726f115cf6df864807c9dd871af3ade430eacebc011b21d02fdc100025` |
| `slt_add_right_iff_saddOverflow_eq` | Classical.choice, Quot.sound, propext | `25c6716625f0a9e41cc25de3dd2e84f0fa88e136828d83dcab5735b226e59f15` | `50f144726f115cf6df864807c9dd871af3ade430eacebc011b21d02fdc100025` |
| `slt_add_right_of_noSAddOverflow` | Quot.sound, propext | `2c1570ee6d7bd3c1d0ac6ea63449221cea17b7af1c173b6ac7975acf117eeb2e` | `0ada6e89ff7b10fa132f1e5df649aa6528135a7b8a362ee07d25d23385cef9e2` |
| `slt_intMax_add_one_intMax_of_posWidth` | Classical.choice, Quot.sound, propext | `92285032f7865d1a669b280d970f0ddb287df5c54df50f2b8a9ee2015e1eec27` | `4988b287e1d9d7e9d0c7bb200cd0c223b8ad7b19ec4078d5751079bed483ec32` |
| `tdiv_not_inSignedRange_iff_intMin_negOne` | Classical.choice, Quot.sound, propext | `33dc0c9e2f8dae652646939cd4f02bd7597751142fffafb6f5491b1c76bf33bd` | `d72ddba922f27f7d7de95307b3e47833f5341a13bf7ea108defdb8863f93007e` |
| `ult_add_one_iff_ne_allOnes` | Quot.sound, propext | `f83bdf966a2770632c9b17d215ccd2c5ead0e2770ab13c4008b46ed1eeb56b28` | `3afbf1830aa040c9eeae28b7fbe931fa1c9ba2f37f88fca5f747c8d008b79908` |
| `ult_add_right_iff_uaddOverflow_eq` | Classical.choice, Quot.sound, propext | `35e57ada919b0c8542245ac42b4d8192cb2a0d3b0253738ef9a8ad4942a9462b` | `3afbf1830aa040c9eeae28b7fbe931fa1c9ba2f37f88fca5f747c8d008b79908` |
| `ult_add_right_of_noUAddOverflow` | Quot.sound, propext | `0439b9517029c79a8470d538876311e246a54bd113ff2f1cc32f9141b1c25d90` | `82fea6fd02ade8648ab872fa27bb4599f26ee1e6b75dc8412751291f5441a3bf` |
| `ult_allOnes_add_one_allOnes_of_posWidth` | Quot.sound, propext | `20aaabafa3eaa07db2f658b80d3b56f4e50a7e2cfd835ee11461735a1c33c8db` | `fea1e2150a3fe497de4b7d5946287acfb2b5a26d0909a63d08da4892d5349171` |
| `widened_identity_holds_without_widthLe` | propext | `752e7ed551ade6865128df4e9eae6e0a14a59706ce474362d0b86451bfd69661` | `5aa70cb5fc51c28a26db52a448ebc566f4a5eeba54b78f4b715a1f25c2470cbc` |
| `wrappingShl_eq_mul_twoPow_of_shiftInBounds` | Quot.sound, propext | `5bbd880e0776c73a5cb97ae0bf0a72ade93e731af4cad1ee6b2da458f6f2df3f` | `8d9d9a8b7e31f71d64666e319cce8929a200af462f9e20a52c3120139a622f56` |
| `wrappingUShr_and_wrappingSShr_of_shiftInBounds` | Classical.choice, Quot.sound, propext | `7690297ddf21411a20fd7465b6f79f8d553b19a5879306870e17f39426981ef6` | `7c6ee38ff40f67b62b58a76fb842d15c6cd1cb0e1bc770bd69825f68893ab9b7` |

**Primary sources** (as cited on the cards; revisions are full commit hashes):

- The Rust Reference, `rust-lang/reference` commit `c9cc32825b03fc206d9c6fe73e9ca6a2f3576d6c`: `src/expressions/operator-expr.md` (`[expr.operator.int-overflow.*]`, `[expr.arith-logic]`, `[expr.as.numeric.*]`) and `src/behavior-not-considered-unsafe.md` (L14).
- Ferrocene Language Specification, `rust-lang/fls` commit `bca860e8dab52715effdd49a792347b262f5e539`, `src/expressions.rst` (Arithmetic Overflow).
- Rust core library, `rust-lang/rust` tag `1.91.0` (commit `f8297e351a40c1439a467bbbb6879088047f50b3`), `library/core/src/num/int_macros.rs` and `uint_macros.rs` (the `checked_*`, `wrapping_*`, `strict_*` and unstable `exact_shl` items cited on the cards).
- Rust RFC 0560, `rust-lang/rfcs` commit `f17e8623ee2e2854570dcdb936a9f4ab08c0fcd4`, `text/0560-integer-overflow.md`.
- Lean core library, `leanprover/lean4` tag `v4.34.1` (commit `5045d0056413266e57c625dcd7c365b10e377c52`): `src/lean/Init/Data/BitVec/{Basic,Bootstrap,Lemmas,Bitblast}.lean`, `src/lean/Init/Data/Int/DivMod/{Basic,Lemmas}.lean`, `src/lean/Init/Data/Nat/Power2/Bitwise.lean` (`Nat.ne_zero_and_sub_one_eq_zero_iff_isPowerOfTwo`, used by `mod_eq_and_mask_forall_iff_isPowerOfTwo`).
- Aeneas, `AeneasVerif/aeneas` commit `2e3d4488280bb8a95411db81019a7854a784861f`; CompCert, `AbsInt/CompCert` commit `2685140bf72c959446981fb99b5e44a8975021bc`; Isabelle/HOL, `isabelle-prover/mirror-isabelle` commit `20d6a3f7ffbaaa82e77f341d90db5070b3428fbe` (paths and line ranges on the cards).
- R. T. Boute, "The Euclidean definition of the functions div and mod", ACM TOPLAS 14(2), April 1992, pp. 127-144, DOI 10.1145/128861.128862.
- W. Dietz, P. Li, J. Regehr, V. Adve, "Understanding Integer Overflow in C/C++", ICSE 2012, pp. 760-770, DOI 10.1109/ICSE.2012.6227142.

**Execution cross-checks of the modeling bridge (not proofs).** `support/rustc_semantics_checks.rs` (program), `support/run_rustc_checks.sh` (runner: four profiles plus five compile-time rejection probes), `support/rustc_checks_output.txt` (output). Observed 2026-11-20 with `rustc 1.102.0-nightly (3ef0c22cd 2026-11-11)`, commit `3ef0c22cdb86ac42dc6b8f0f1ec36857daa6f2a1`, host `x86_64-unknown-linux-gnu`, LLVM 23.1.5. Profiles: `-C opt-level=0 -C debug-assertions=yes` (overflow checks on), `-C opt-level=3` (off), `-C opt-level=3 -C overflow-checks=yes` (on), `-C opt-level=0 -C debug-assertions=yes -C overflow-checks=no` (off). Every observation quoted in the `Basis: derived (modeling bridge)` lines above appears in that output in all four profiles, except the panics, which occur exactly in the two overflow-checked profiles (and `MIN / -1`, `MIN % -1`, `7 / 0`, which panic in all four). Compile-time probes: `128_i8`, `256` as `u8` and `-129_i8` are rejected by `overflowing_literals`; `-1u8` is `E0600`; `-(-128_i8)` is rejected by `arithmetic_overflow`. One line uses the unstable `shl_exact` (the later name of 1.91.0's `exact_shl`), so the program needs a nightly compiler.

## Revalidation

Requirements: `elan` (so that `lake` uses the toolchain pinned in `lean/lean-toolchain`) and `python3`. From the package directory:

```sh
python3 support/revalidate.py .
```

It copies `lean/` to a temporary directory (the package is not modified), runs `lake build`, scans the Lean sources for `sorry`, `admit`, `native_decide` and `axiom` declarations, computes the axioms of every library declaration with `Lean.collectAxioms` (only `propext`, `Classical.choice`, `Quot.sound` are accepted), and recomputes for every name referenced by `results.json` and every name in `audit/statements.json` the SHA-256 of `repr` of its type and of its definition closure (described under Evidence), comparing them with `audit/statements.json`. It prints `REVALIDATED` and exits 0 iff all checks pass.

The same audit without the script, using only `elan`, `lake` and `python3` (`lean/RevalidationAudit.lean` is outside the `Toy` library target and lists every card-referenced name):

```sh
cd lean
lake build
lake env lean RevalidationAudit.lean > /tmp/machint_audit.txt
cd ..
python3 - <<'EOF'
import hashlib, json, re
audit = json.loads(re.search(r'REVALIDATION_AUDIT_JSON (\{.*\})', open('/tmp/machint_audit.txt').read()).group(1))
allowed = {'propext', 'Classical.choice', 'Quot.sound'}
bad = [d['name'] for d in audit['decls'] if set(d['axioms']) - allowed]
rec = json.load(open('audit/statements.json'))['statements']
drift = []
for s in audit['stmts']:
    got = {'statement_sha256': hashlib.sha256(s['type_repr'].encode()).hexdigest(),
           'closure_sha256': hashlib.sha256('\n'.join(s['closure']).encode()).hexdigest(),
           'closure_size': len(s['closure'])}
    if s.get('missing') or rec.get(s['name']) != got:
        drift.append(s['name'])
print('axiom violations:', bad)
print('hash mismatches:', drift)
print('names checked:', len(audit['stmts']), 'of', len(rec), 'recorded')
EOF
```

Both lists must be empty. `lake build` alone also re-runs the in-library axiom audit (`Toy.MachInt.Audit`, which reports `AUDIT OK`).

To re-run the `rustc` cross-checks (needs a nightly `rustc` on `PATH`): `bash support/run_rustc_checks.sh > /tmp/rustc_out.txt` and compare with `support/rustc_checks_output.txt` (only the version header should differ on another nightly). A passing comparison re-establishes only the observed `rustc` behaviour on that compiler and host. For another Rust release, the modeling bridge must be re-argued from that release's Reference and core-library documentation (`[expr.operator.int-overflow]`, `[expr.arith-logic]`, `[expr.as.numeric]`, and the `checked_*`/`wrapping_*` method documentation); the kernel-checked theorems themselves do not depend on Rust.
