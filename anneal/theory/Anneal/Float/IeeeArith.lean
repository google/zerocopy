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

public section

/-!
# IEEE-754 & RFC 3514 Arithmetic, Comparisons, FMA, & NaN Choices (`IeeeArith`)

Pass-1-pure (`0` TCB LOC, `0` `._unsafe_rec`, `0` `Classical.choice`,
axioms `⊆ [propext, Quot.sound]`) operational and relational semantics of
IEEE-754 `f32`/`f64` arithmetic, comparisons, fused/relaxed multiply-add
(`fma` / `simd_relaxed_fma`), and RFC 3514 nondeterministic NaN payload
propagation:

1. **Bitwise Sign Operations (`evalFloatNeg`, `evalFloatAbs`,
   `evalFloatCopysign`):**
   - Flip/clear/copy only the sign bit while preserving exponent, quiet bit, and
     signaling NaN payloads verbatim (`evalFloatNeg_lt`,
     `evalFloatNeg_involutive`, `evalFloatAbs_lt`, `evalFloatAbs_idempotent`).
2. **IEEE-754 Partial Ordering & Boolean Comparisons (`FloatOrd`, `FloatCmpOp`,
   `evalFloatPartialCompare`, `evalFloatCmp`):**
   - `-0.0 == +0.0` (`evalFloatCmp_zero_eq_zero`), unordered NaNs, unconditional
     `PartialOrd` consistency (`evalFloatCmp_le_eq_lt_or_eq`,
     `evalFloatCmp_ge_eq_gt_or_eq`), and `.ne` duality
     (`evalFloatCmp_ne_eq_not_eq`).
3. **Single-Rounded Binary & Ternary Arithmetic (`FloatBinOp`, `exactSumFloat`,
   `evalFloatArithBase`, `evalFloatFmaBase`, `evalFloatUnfusedMulAddBase`):**
   - `add`, `sub`, `mul`, `div`, `rem`, and fused `(a * b) + c` (`fma`) over
     exact rationals with `roundRatioTiesToEven`, total on division/remainder by
     `±0.0` (never UB), signed-zero sum/product/remainder rules, and all five
     indeterminate forms (`0/0`, `∞/∞`, `0*∞`, `x%0`, `∞%y`).
4. **RFC 3514 Nondeterministic `nanChoices`, `FloatToFloat`, &
   `simd_relaxed_fma` (`FloatArithMode`, `nanChoices`, `EvalFloatToFloatRel`,
   `EvalFloatBinOpRel`, `EvalFloatFmaRel`, `EvalRelaxedFmaRel`):**
   - Enumerates preferred, quieted, and nonzero-lower-payload unchanged SNaN
     candidates with independent sign flip (`preferredNaNBits_mem_nanChoices`),
     proves `.deterministic → .nondeterministic` inclusion, and proves finite
     short-circuiting (`evalFloatToFloatRel_of_not_nan`,
     `evalFloatBinOpRel_of_not_nan`, `evalFloatFmaRel_of_not_nan`: whenever the
     base result is non-NaN, `.nondeterministic` collapses to exact
     deterministic equality).
-/

namespace Anneal.Float

open Anneal.LinearArith

/-! ## Part I: Bitwise Sign Operations (RFC 3514 Payload-Preserving) -/

/-- Bitwise IEEE-754 unary negation (`-x`): flips bit `f.width - 1` while
preserving signaling/quiet NaNs and payloads verbatim. -/
@[expose] def evalFloatNeg (f : IeeeFormat) (bits : Nat) : Nat :=
  let b := Nat.mod bits (pow2 f.width)
  let sign := f.signBitMask
  match Nat.ble sign b with
  | true => b - sign
  | false => b + sign

/-- Bitwise IEEE-754 absolute value (`x.abs()`): clears bit `f.width - 1`. -/
@[expose] def evalFloatAbs (f : IeeeFormat) (bits : Nat) : Nat :=
  Nat.mod bits f.signBitMask

/-- Bitwise IEEE-754 `copysign(mag, sgn)`: copies sign bit of `sgn` onto
`mag`. -/
@[expose] def evalFloatCopysign (f : IeeeFormat) (magBits sgnBits : Nat) : Nat :=
  let mag := evalFloatAbs f magBits
  match signBitOf f (Nat.mod sgnBits (pow2 f.width)) with
  | true => mag + f.signBitMask
  | false => mag

/-- Flip sign of a decoded `FloatKind`. -/
@[expose] def negateFloatKind : FloatKind → FloatKind
  | .zero neg => .zero (!neg)
  | .finite neg n d => .finite (!neg) n d
  | .inf neg => .inf (!neg)
  | .nan neg q p => .nan (!neg) q p

/-! ## Part II: IEEE-754 Partial Ordering & Boolean Comparisons -/

/-- Three-way ordering result for `evalFloatPartialCompare`
(`Init.Data.Ord.Basic` is outside `foundation-lock.json`, matching
`Trusted.MirSemantics.OrderingVal`). -/
inductive FloatOrd : Type where
  | lt : FloatOrd
  | eq : FloatOrd
  | gt : FloatOrd

/-- Floating-point comparison operators (`==`, `!=`, `<`, `<=`, `>`, `>=`). -/
inductive FloatCmpOp : Type where
  | eq : FloatCmpOp
  | ne : FloatCmpOp
  | lt : FloatCmpOp
  | le : FloatCmpOp
  | gt : FloatCmpOp
  | ge : FloatCmpOp

/-- Signed integer numerator `(-1)^neg * n`. -/
@[expose] def signedNum (neg : Bool) (n : Nat) : Int :=
  if neg then Int.neg (Int.ofNat n) else Int.ofNat n

/-- IEEE-754 partial ordering (`partial_cmp`): `none` if either operand is NaN,
`some .eq` on `±0.0`, exact cross-multiplied comparison on finite values. -/
@[expose] def evalFloatPartialCompare (f : IeeeFormat)
    (lhsBits rhsBits : Nat) : Option FloatOrd :=
  let l := decodeBits f (Nat.mod lhsBits (pow2 f.width))
  let r := decodeBits f (Nat.mod rhsBits (pow2 f.width))
  match l, r with
  | .nan _ _ _, _ => none
  | _, .nan _ _ _ => none
  | .inf ln, .inf rn =>
    some (match ln, rn with
      | true, true => .eq
      | false, false => .eq
      | true, false => .lt
      | false, true => .gt)
  | .inf ln, _ => some (if ln then .lt else .gt)
  | _, .inf rn => some (if rn then .gt else .lt)
  | .zero _, .zero _ => some .eq
  | .zero _, .finite rn rnum _ =>
    some (if Nat.beq rnum 0 then .eq else if rn then .gt else .lt)
  | .finite ln lnum _, .zero _ =>
    some (if Nat.beq lnum 0 then .eq else if ln then .lt else .gt)
  | .finite ln lnum lden, .finite rn rnum rden =>
    let lv := Int.mul (signedNum ln lnum) (Int.ofNat rden)
    let rv := Int.mul (signedNum rn rnum) (Int.ofNat lden)
    some (if intLtB lv rv then .lt else if intEqB lv rv then .eq else .gt)

/-- IEEE-754 boolean comparison evaluation (`PartialEq` / `PartialOrd`). -/
@[expose] def evalFloatCmp (op : FloatCmpOp) (f : IeeeFormat)
    (lhsBits rhsBits : Nat) : Bool :=
  let ord := evalFloatPartialCompare f lhsBits rhsBits
  match op with
  | .eq => match ord with | some .eq => true | _ => false
  | .ne => match ord with | some .eq => false | _ => true
  | .lt => match ord with | some .lt => true | _ => false
  | .le => match ord with | some .lt => true | some .eq => true | _ => false
  | .gt => match ord with | some .gt => true | _ => false
  | .ge => match ord with | some .gt => true | some .eq => true | _ => false

/-! ## Part III: Binary Arithmetic (`add`/`sub`/`mul`/`div`/`rem`) & FMA -/

/-- Primitive IEEE-754 binary arithmetic operators in MIR. -/
inductive FloatBinOp : Type where
  | add : FloatBinOp
  | sub : FloatBinOp
  | mul : FloatBinOp
  | div : FloatBinOp
  | rem : FloatBinOp

/-- Exact IEEE-754 sum under `roundTiesToEven` (exact zero is `-0.0` iff both
operands are `-0.0`). -/
@[expose] def exactSumFloat (f : IeeeFormat) (lhs rhs : FloatKind) : Nat :=
  match lhs, rhs with
  | .nan _ _ _, _ => preferredNaNBits f
  | _, .nan _ _ _ => preferredNaNBits f
  | .inf ln, .inf rn =>
    if bne ln rn then preferredNaNBits f else infBits f ln
  | .inf ln, _ => infBits f ln
  | _, .inf rn => infBits f rn
  | .zero ln, .zero rn => zeroBits f (ln && rn)
  | .zero ln, .finite rn rnum rden =>
    let sign := if Nat.beq rnum 0 then ln && rn else rn
    roundRatioTiesToEven f sign rnum rden
  | .finite ln lnum lden, .zero rn =>
    let sign := if Nat.beq lnum 0 then ln && rn else ln
    roundRatioTiesToEven f sign lnum lden
  | .finite ln lnum lden, .finite rn rnum rden =>
    let sum := Int.add (Int.mul (signedNum ln lnum) (Int.ofNat rden))
      (Int.mul (signedNum rn rnum) (Int.ofNat lden))
    let sign :=
      match intEqB sum (Int.ofNat 0) with
      | true => Nat.beq lnum 0 && (Nat.beq rnum 0 && (ln && rn))
      | false => intLtB sum (Int.ofNat 0)
    roundRatioTiesToEven f sign (Int.natAbs sum) (lden * rden)

/-- Deterministic base evaluator for IEEE-754 binary arithmetic (`add`, `sub`,
`mul`, `div`, `rem`), matching `Miri.Interpreter.FloatBits.arithmetic`. -/
@[expose] def evalFloatArithBase (op : FloatBinOp) (f : IeeeFormat)
    (lhsBits rhsBits : Nat) : Nat :=
  let lb := Nat.mod lhsBits (pow2 f.width)
  let rb := Nat.mod rhsBits (pow2 f.width)
  let l := decodeBits f lb
  let r := decodeBits f rb
  match op with
  | .add => exactSumFloat f l r
  | .sub => exactSumFloat f l (negateFloatKind r)
  | .mul =>
    match l, r with
    | .nan _ _ _, _ => preferredNaNBits f
    | _, .nan _ _ _ => preferredNaNBits f
    | .inf _, .zero _ => preferredNaNBits f
    | .zero _, .inf _ => preferredNaNBits f
    | .inf ln, .finite rn rnum _ =>
      if Nat.beq rnum 0 then preferredNaNBits f else infBits f (bne ln rn)
    | .finite ln lnum _, .inf rn =>
      if Nat.beq lnum 0 then preferredNaNBits f else infBits f (bne ln rn)
    | .inf ln, .inf rn => infBits f (bne ln rn)
    | .zero ln, .zero rn => zeroBits f (bne ln rn)
    | .zero ln, .finite rn _ _ => zeroBits f (bne ln rn)
    | .finite ln _ _, .zero rn => zeroBits f (bne ln rn)
    | .finite ln lnum lden, .finite rn rnum rden =>
      roundRatioTiesToEven f (bne ln rn) (lnum * rnum) (lden * rden)
  | .div =>
    match l, r with
    | .nan _ _ _, _ => preferredNaNBits f
    | _, .nan _ _ _ => preferredNaNBits f
    | .inf _, .inf _ => preferredNaNBits f
    | .zero _, .zero _ => preferredNaNBits f
    | .inf ln, .zero rn => infBits f (bne ln rn)
    | .inf ln, .finite rn _ _ => infBits f (bne ln rn)
    | .zero ln, .inf rn => zeroBits f (bne ln rn)
    | .zero ln, .finite rn rnum _ =>
      if Nat.beq rnum 0 then preferredNaNBits f else zeroBits f (bne ln rn)
    | .finite ln lnum _, .zero rn =>
      if Nat.beq lnum 0 then preferredNaNBits f else infBits f (bne ln rn)
    | .finite ln _ _, .inf rn => zeroBits f (bne ln rn)
    | .finite ln lnum lden, .finite rn rnum rden =>
      if Nat.beq rnum 0 then
        if Nat.beq lnum 0 then preferredNaNBits f else infBits f (bne ln rn)
      else
        roundRatioTiesToEven f (bne ln rn) (lnum * rden) (lden * rnum)
  | .rem =>
    match l, r with
    | .nan _ _ _, _ => preferredNaNBits f
    | _, .nan _ _ _ => preferredNaNBits f
    | .inf _, _ => preferredNaNBits f
    | _, .zero _ => preferredNaNBits f
    | .zero _, .inf _ => lb
    | .finite _ _ _, .inf _ => lb
    | .zero ln, .finite _ rnum _ =>
      if Nat.beq rnum 0 then preferredNaNBits f else zeroBits f ln
    | .finite ln lnum lden, .finite _ rnum rden =>
      if Nat.beq rnum 0 then preferredNaNBits f
      else
        let q := Nat.div (lnum * rden) (lden * rnum)
        let remVal := lnum * rden - q * (lden * rnum)
        roundRatioTiesToEven f ln remVal (lden * rden)

/-- Sign bit of a decoded `FloatKind`. -/
@[expose] def decodedSign : FloatKind → Bool
  | .zero n => n
  | .finite n _ _ => n
  | .inf n => n
  | .nan n _ _ => n

/-- `true` iff `FloatKind` has zero magnitude (`.zero` or degenerate
`.finite _ 0 _`). -/
@[expose] def decodedIsZeroMag : FloatKind → Bool
  | .zero _ => true
  | .finite _ num _ => Nat.beq num 0
  | _ => false

/-- Exact IEEE-754 single-rounded fused multiply-add `(a * b) + c`
(`f32::mul_add` / `f64::mul_add`), matching
`Miri.Interpreter.IntrinsicFloat.fusedMulAdd`. -/
@[expose] def evalFloatFmaBase (f : IeeeFormat)
    (aBits bBits cBits : Nat) : Nat :=
  let da := decodeBits f (Nat.mod aBits (pow2 f.width))
  let db := decodeBits f (Nat.mod bBits (pow2 f.width))
  let dc := decodeBits f (Nat.mod cBits (pow2 f.width))
  let prodNeg := bne (decodedSign da) (decodedSign db)
  match da, db, dc with
  | .nan _ _ _, _, _ => preferredNaNBits f
  | _, .nan _ _ _, _ => preferredNaNBits f
  | _, _, .nan _ _ _ => preferredNaNBits f
  | .inf _, bK, _ =>
    if decodedIsZeroMag bK then preferredNaNBits f
    else
      match dc with
      | .inf cn => if bne prodNeg cn then preferredNaNBits f else infBits f prodNeg
      | _ => infBits f prodNeg
  | aK, .inf _, _ =>
    if decodedIsZeroMag aK then preferredNaNBits f
    else
      match dc with
      | .inf cn => if bne prodNeg cn then preferredNaNBits f else infBits f prodNeg
      | _ => infBits f prodNeg
  | _, _, .inf cn => infBits f cn
  | .zero _, _, .zero cn => zeroBits f (prodNeg && cn)
  | _, .zero _, .zero cn => zeroBits f (prodNeg && cn)
  | .zero _, _, .finite cn cnum cden =>
    let sign := if Nat.beq cnum 0 then prodNeg && cn else cn
    roundRatioTiesToEven f sign cnum cden
  | _, .zero _, .finite cn cnum cden =>
    let sign := if Nat.beq cnum 0 then prodNeg && cn else cn
    roundRatioTiesToEven f sign cnum cden
  | .finite _ anum aden, .finite _ bnum bden, .zero cn =>
    let pn := anum * bnum
    let sign := if Nat.beq pn 0 then prodNeg && cn else prodNeg
    roundRatioTiesToEven f sign pn (aden * bden)
  | .finite _ anum aden, .finite _ bnum bden, .finite cn cnum cden =>
    let pn := anum * bnum
    let pd := aden * bden
    let res := Int.add (Int.mul (signedNum prodNeg pn) (Int.ofNat cden))
      (Int.mul (signedNum cn cnum) (Int.ofNat pd))
    let sign :=
      match intEqB res (Int.ofNat 0) with
      | true => Nat.beq pn 0 && (Nat.beq cnum 0 && (prodNeg && cn))
      | false => intLtB res (Int.ofNat 0)
    roundRatioTiesToEven f sign (Int.natAbs res) (pd * cden)

/-- Double-rounded `(a * b) + c` (the `fuse = false` branch of
`simd_relaxed_fma`). -/
@[expose] def evalFloatUnfusedMulAddBase (f : IeeeFormat)
    (aBits bBits cBits : Nat) : Nat :=
  let ab := evalFloatArithBase .mul f aBits bBits
  evalFloatArithBase .add f ab cBits

/-! ## Part IV: RFC 3514 `nanChoices` & Relational Nondeterminism -/

/-- NaN selection mode (`.deterministic` vs RFC 3514 `.nondeterministic`). -/
inductive FloatArithMode : Type where
  | deterministic : FloatArithMode
  | nondeterministic : FloatArithMode

/-- Quieted NaN candidates converted to `target` from each NaN input
(`List.foldr` avoids emitting `._unsafe_rec` in Pass-1 `anneal/theory/`). -/
@[expose] def nanChoicesQuieted (target : IeeeFormat)
    (inputs : List (IeeeFormat × Nat)) : List Nat :=
  List.foldr
    (fun inp tail =>
      let src := inp.1
      let b := Nat.mod inp.2 (pow2 src.width)
      match isNaNBits src b with
      | true => evalFloatToFloatRoundTiesToEven src target b :: tail
      | false => tail)
    []
    inputs

/-- Unchanged signaling NaN candidates converted to `target` when the lower
payload bits remain nonzero (`lower ≠ 0` prevents collapsing narrowed SNaNs to
`±∞`; `List.foldr` avoids `._unsafe_rec`). -/
@[expose] def nanChoicesSignaling (target : IeeeFormat)
    (inputs : List (IeeeFormat × Nat)) : List Nat :=
  List.foldr
    (fun inp tail =>
      let src := inp.1
      let b := Nat.mod inp.2 (pow2 src.width)
      match isSignalingNaNBits src b with
      | false => tail
      | true =>
        let converted := evalFloatToFloatRoundTiesToEven src target b
        let c := unpackBits target converted
        let lower := Nat.mod c.fraction target.quietBitMask
        match Nat.beq lower 0 with
        | true => tail
        | false => encodeBits target c.neg target.allOnesExp lower :: tail)
    []
    inputs

/-- Expand each candidate NaN into `[cand, -cand]` (independent sign choice;
`List.foldr` avoids `._unsafe_rec`). -/
@[expose] def expandNanSigns (target : IeeeFormat)
    (cands : List Nat) : List Nat :=
  List.foldr
    (fun cand tail => cand :: evalFloatNeg target cand :: tail)
    []
    cands

/-- Ordered list of admissible NaN bit patterns matching
`Miri.Interpreter.FloatBits.nanChoices`. -/
@[expose] def nanChoices (target : IeeeFormat)
    (inputs : List (IeeeFormat × Nat)) (mode : FloatArithMode) : List Nat :=
  match mode with
  | .deterministic => [preferredNaNBits target]
  | .nondeterministic =>
    let cands :=
      preferredNaNBits target ::
        (nanChoicesQuieted target inputs ++ nanChoicesSignaling target inputs)
    expandNanSigns target cands

/-- Boolean list membership on `Nat` (`List.foldr` avoids `._unsafe_rec`). -/
@[expose] def natListMem (x : Nat) (ys : List Nat) : Bool :=
  List.foldr (fun y acc => Nat.beq x y || acc) false ys

/-- Relational specification of Rust `as` float-to-float casts
(`CastKind.floatToFloat`) under `mode`, matching
`Miri.Interpreter.FloatOps.castFloatToFloat` (`convert` followed by
`adjustNaN` over `[(src, b)]`). -/
@[expose] def EvalFloatToFloatRel (mode : FloatArithMode)
    (src dst : IeeeFormat) (bits outBits : Nat) : Prop :=
  let base := evalFloatToFloatRoundTiesToEven src dst bits
  match isNaNBits dst base with
  | true =>
    let b := Nat.mod bits (pow2 src.width)
    outBits ∈ nanChoices dst [(src, b)] mode
  | false => outBits = base

/-- Relational specification of IEEE-754 binary arithmetic under `mode`. -/
@[expose] def EvalFloatBinOpRel (mode : FloatArithMode) (op : FloatBinOp)
    (f : IeeeFormat) (lhsBits rhsBits outBits : Nat) : Prop :=
  let base := evalFloatArithBase op f lhsBits rhsBits
  match isNaNBits f base with
  | true =>
    let lb := Nat.mod lhsBits (pow2 f.width)
    let rb := Nat.mod rhsBits (pow2 f.width)
    outBits ∈ nanChoices f [(f, lb), (f, rb)] mode
  | false => outBits = base

/-- Relational specification of IEEE-754 `fma` under `mode`. -/
@[expose] def EvalFloatFmaRel (mode : FloatArithMode) (f : IeeeFormat)
    (aBits bBits cBits outBits : Nat) : Prop :=
  let base := evalFloatFmaBase f aBits bBits cBits
  match isNaNBits f base with
  | true =>
    let ab := Nat.mod aBits (pow2 f.width)
    let bb := Nat.mod bBits (pow2 f.width)
    let cb := Nat.mod cBits (pow2 f.width)
    outBits ∈ nanChoices f [(f, ab), (f, bb), (f, cb)] mode
  | false => outBits = base

/-- Relational specification of `simd_relaxed_fma` (RFC 3514 demonic choice
between single-rounded FMA and double-rounded `mul` + `add`). -/
@[expose] def EvalRelaxedFmaRel (mode : FloatArithMode) (f : IeeeFormat)
    (aBits bBits cBits outBits : Nat) : Prop :=
  EvalFloatFmaRel mode f aBits bBits cBits outBits ∨
    (∃ midBits : Nat,
      EvalFloatBinOpRel mode .mul f aBits bBits midBits ∧
        EvalFloatBinOpRel mode .add f midBits cBits outBits)

/-! ## Part V: Algebraic, Order, Width, & NaN-Collapse Theorems -/

private theorem signBitMask_double (f : IeeeFormat) :
    f.signBitMask + f.signBitMask = pow2 f.width := by
  cases f <;> rfl

private theorem nat_mod_eq_of_lt_ia {a b : Nat} (h : a < b) :
    Nat.mod a b = a :=
  Nat.mod_eq_of_lt h

/-- `evalFloatNeg f bits < 2^f.width` (`[propext]` only). -/
theorem evalFloatNeg_lt (f : IeeeFormat) (bits : Nat) :
    evalFloatNeg f bits < pow2 f.width := by
  dsimp only [evalFloatNeg]
  have hMod : Nat.mod bits (pow2 f.width) < pow2 f.width :=
    Nat.mod_lt bits (pow2_pos f.width)
  cases hBle : Nat.ble f.signBitMask (Nat.mod bits (pow2 f.width)) with
  | true => exact Nat.lt_of_le_of_lt (Nat.sub_le _ _) hMod
  | false =>
    have hLtSign : Nat.mod bits (pow2 f.width) < f.signBitMask := by
      cases Nat.lt_or_ge (Nat.mod bits (pow2 f.width)) f.signBitMask with
      | inl hL => exact hL
      | inr hG =>
        have hBleDef : ∀ a b : Nat, a ≤ b → Nat.ble a b = true := by
          intro a
          induction a with
          | zero => intro _ _; rfl
          | succ a' ih =>
            intro b hb
            cases b with
            | zero => exact nomatch hb
            | succ b' => exact ih b' (Nat.le_of_succ_le_succ hb)
        rw [hBleDef _ _ hG] at hBle
        exact Bool.noConfusion hBle
    have hAdd := Nat.add_lt_add_right hLtSign f.signBitMask
    rw [signBitMask_double f] at hAdd
    exact hAdd

/-- `evalFloatNeg` is a bitwise involution on canonical `< 2^f.width` patterns
(`[propext]` only). -/
theorem evalFloatNeg_involutive (f : IeeeFormat) {bits : Nat}
    (hBits : bits < pow2 f.width) :
    evalFloatNeg f (evalFloatNeg f bits) = bits := by
  have hOutLt := evalFloatNeg_lt f bits
  let mid := evalFloatNeg f bits
  change evalFloatNeg f mid = bits
  dsimp only [evalFloatNeg]
  rw [nat_mod_eq_of_lt_ia hOutLt]
  dsimp only [mid, evalFloatNeg]
  rw [nat_mod_eq_of_lt_ia hBits]
  have hBleIff : ∀ a b : Nat, Nat.ble a b = true ↔ a ≤ b := by
    intro a
    induction a with
    | zero => intro b; exact ⟨fun _ => Nat.zero_le b, fun _ => rfl⟩
    | succ a' ih =>
      intro b
      cases b with
      | zero => exact ⟨fun h => Bool.noConfusion h, fun h => nomatch h⟩
      | succ b' =>
        exact ⟨fun h => Nat.succ_le_succ ((ih b').mp h),
          fun h => (ih b').mpr (Nat.le_of_succ_le_succ h)⟩
  cases hB1 : Nat.ble f.signBitMask bits with
  | true =>
    have hGe : f.signBitMask ≤ bits := (hBleIff _ _).mp hB1
    have hSubLt : bits - f.signBitMask < f.signBitMask := by
      rw [← signBitMask_double f] at hBits
      exact Nat.sub_lt_left_of_lt_add hGe hBits
    have hB2 : Nat.ble f.signBitMask (bits - f.signBitMask) = false := by
      cases hB : Nat.ble f.signBitMask (bits - f.signBitMask) with
      | false => rfl
      | true =>
        exact False.elim (Nat.not_lt_of_ge ((hBleIff _ _).mp hB) hSubLt)
    rw [hB2]
    exact Nat.sub_add_cancel hGe
  | false =>
    have hGe2 : f.signBitMask ≤ bits + f.signBitMask :=
      Nat.le_add_left _ _
    have hB2 : Nat.ble f.signBitMask (bits + f.signBitMask) = true :=
      (hBleIff _ _).mpr hGe2
    rw [hB2]
    exact Nat.add_sub_cancel _ _

/-- `evalFloatAbs f bits < 2^f.width` (`[]` zero axioms). -/
theorem evalFloatAbs_lt (f : IeeeFormat) (bits : Nat) :
    evalFloatAbs f bits < pow2 f.width := by
  dsimp only [evalFloatAbs]
  have hMaskPos : 0 < f.signBitMask := by cases f <;> decide
  have hMaskLt : f.signBitMask < pow2 f.width := by cases f <;> decide
  exact Nat.lt_trans (Nat.mod_lt bits hMaskPos) hMaskLt

/-- `evalFloatAbs` is idempotent (`[propext]` only). -/
theorem evalFloatAbs_idempotent (f : IeeeFormat) (bits : Nat) :
    evalFloatAbs f (evalFloatAbs f bits) = evalFloatAbs f bits := by
  dsimp only [evalFloatAbs]
  have hMaskPos : 0 < f.signBitMask := by cases f <;> decide
  exact Nat.mod_eq_of_lt (Nat.mod_lt bits hMaskPos)

/-- `evalFloatCmp .ne` is the exact boolean negation of `evalFloatCmp .eq`,
including on unordered NaN inputs (`[propext]` only). -/
theorem evalFloatCmp_ne_eq_not_eq (f : IeeeFormat) (lhs rhs : Nat) :
    evalFloatCmp .ne f lhs rhs = !(evalFloatCmp .eq f lhs rhs) := by
  dsimp only [evalFloatCmp]
  cases evalFloatPartialCompare f lhs rhs with
  | none => rfl
  | some ord => cases ord <;> rfl

/-- Unconditional `PartialOrd` consistency `le = (lt || eq)` (`[propext]`
only). -/
theorem evalFloatCmp_le_eq_lt_or_eq (f : IeeeFormat) (lhs rhs : Nat) :
    evalFloatCmp .le f lhs rhs =
      (evalFloatCmp .lt f lhs rhs || evalFloatCmp .eq f lhs rhs) := by
  dsimp only [evalFloatCmp]
  cases evalFloatPartialCompare f lhs rhs with
  | none => rfl
  | some ord => cases ord <;> rfl

/-- Unconditional `PartialOrd` consistency `ge = (gt || eq)` (`[propext]`
only). -/
theorem evalFloatCmp_ge_eq_gt_or_eq (f : IeeeFormat) (lhs rhs : Nat) :
    evalFloatCmp .ge f lhs rhs =
      (evalFloatCmp .gt f lhs rhs || evalFloatCmp .eq f lhs rhs) := by
  dsimp only [evalFloatCmp]
  cases evalFloatPartialCompare f lhs rhs with
  | none => rfl
  | some ord => cases ord <;> rfl

/-- Signed-zero equality `-0.0 == +0.0` holds in both `f32` and `f64`
(`[propext]` only). -/
theorem evalFloatCmp_zero_eq_zero (f : IeeeFormat) (s1 s2 : Bool) :
    evalFloatCmp .eq f (zeroBits f s1) (zeroBits f s2) = true := by
  dsimp only [evalFloatCmp, evalFloatPartialCompare]
  rw [nat_mod_eq_of_lt_ia (zeroBits_lt f s1),
    nat_mod_eq_of_lt_ia (zeroBits_lt f s2)]
  cases f <;> cases s1 <;> cases s2 <;> rfl

/-- Every `FloatBinOp` produces a canonical `< 2^f.width` bit pattern
(`[propext]`). -/
theorem evalFloatArithBase_lt (op : FloatBinOp) (f : IeeeFormat)
    (lhsBits rhsBits : Nat) :
    evalFloatArithBase op f lhsBits rhsBits < pow2 f.width := by
  have hExactLt : ∀ a b : FloatKind, exactSumFloat f a b < pow2 f.width := by
    intro a b
    cases a <;> (repeat exact preferredNaNBits_lt f) <;> cases b <;>
      first
      | exact preferredNaNBits_lt f
      | exact zeroBits_lt f _
      | exact infBits_lt f _
      | exact roundRatioTiesToEven_lt f _ _ _
      | (dsimp only [exactSumFloat]
         cases bne (_ : Bool) _ with
         | true => exact preferredNaNBits_lt f
         | false => exact infBits_lt f _)
  have hLbLt : Nat.mod lhsBits (pow2 f.width) < pow2 f.width :=
    Nat.mod_lt lhsBits (pow2_pos f.width)
  cases op with
  | add => exact hExactLt _ _
  | sub => exact hExactLt _ _
  | _ =>
    dsimp only [evalFloatArithBase]
    cases decodeBits f (Nat.mod lhsBits (pow2 f.width)) <;>
      (repeat exact preferredNaNBits_lt f) <;>
      cases decodeBits f (Nat.mod rhsBits (pow2 f.width)) <;>
      first
      | exact preferredNaNBits_lt f
      | exact zeroBits_lt f _
      | exact infBits_lt f _
      | exact roundRatioTiesToEven_lt f _ _ _
      | exact hLbLt
      | (dsimp only
         cases Nat.beq _ 0 <;>
           first
           | exact preferredNaNBits_lt f
           | exact zeroBits_lt f _
           | exact infBits_lt f _
           | exact roundRatioTiesToEven_lt f _ _ _
           | (cases Nat.beq _ 0 <;>
               first
               | exact preferredNaNBits_lt f
               | exact infBits_lt f _))

/-- `evalFloatFmaBase` always returns `< 2^f.width` (`[propext]` only). -/
theorem evalFloatFmaBase_lt (f : IeeeFormat) (aBits bBits cBits : Nat) :
    evalFloatFmaBase f aBits bBits cBits < pow2 f.width := by
  dsimp only [evalFloatFmaBase]
  cases decodeBits f (Nat.mod aBits (pow2 f.width)) <;>
    (repeat exact preferredNaNBits_lt f) <;>
    cases decodeBits f (Nat.mod bBits (pow2 f.width)) <;>
    (repeat exact preferredNaNBits_lt f) <;>
    cases decodeBits f (Nat.mod cBits (pow2 f.width)) <;>
    first
    | exact preferredNaNBits_lt f
    | exact zeroBits_lt f _
    | exact infBits_lt f _
    | exact roundRatioTiesToEven_lt f _ _ _
    | (dsimp only
       cases decodedIsZeroMag _ with
       | true => exact preferredNaNBits_lt f
       | false =>
         first
         | exact infBits_lt f _
         | (cases bne (_ : Bool) _ with
            | true => exact preferredNaNBits_lt f
            | false => exact infBits_lt f _))

/-- `preferredNaNBits target` is always an admissible candidate in `nanChoices`
(`[propext]` only). -/
theorem preferredNaNBits_mem_nanChoices (target : IeeeFormat)
    (inputs : List (IeeeFormat × Nat)) (mode : FloatArithMode) :
    preferredNaNBits target ∈ nanChoices target inputs mode := by
  cases mode with
  | deterministic => exact List.Mem.head _
  | nondeterministic => exact List.Mem.head _

/-- Mode inclusion for `EvalFloatToFloatRel`: `.deterministic` implies
`.nondeterministic` (`[propext]` only). -/
theorem evalFloatToFloatRel_det_imp_nondet (src dst : IeeeFormat)
    {bits outBits : Nat}
    (h : EvalFloatToFloatRel .deterministic src dst bits outBits) :
    EvalFloatToFloatRel .nondeterministic src dst bits outBits := by
  dsimp only [EvalFloatToFloatRel] at h
  dsimp only [EvalFloatToFloatRel]
  revert h
  cases hN : isNaNBits dst (evalFloatToFloatRoundTiesToEven src dst bits) with
  | false =>
    intro h
    exact h
  | true =>
    intro h
    dsimp only [nanChoices] at h
    cases h with
    | head =>
      dsimp only [nanChoices, expandNanSigns]
      exact List.Mem.head _
    | tail _ hNil => nomatch hNil

/-- Finite/infinite NaN-collapse law for `EvalFloatToFloatRel`: whenever the
base conversion is non-NaN, `EvalFloatToFloatRel` in ANY mode collapses to
exact equality with `evalFloatToFloatRoundTiesToEven` (`[propext]` only). -/
theorem evalFloatToFloatRel_of_not_nan (mode : FloatArithMode)
    (src dst : IeeeFormat) {bits : Nat} (outBits : Nat)
    (hNotNaN :
      isNaNBits dst (evalFloatToFloatRoundTiesToEven src dst bits) = false) :
    EvalFloatToFloatRel mode src dst bits outBits ↔
      outBits = evalFloatToFloatRoundTiesToEven src dst bits := by
  dsimp only [EvalFloatToFloatRel]
  rw [hNotNaN]

/-- Mode inclusion: every `.deterministic` outcome is admissible under
`.nondeterministic` (`[propext]` only). -/
theorem evalFloatBinOpRel_det_imp_nondet (op : FloatBinOp) (f : IeeeFormat)
    {lhsBits rhsBits outBits : Nat}
    (h : EvalFloatBinOpRel .deterministic op f lhsBits rhsBits outBits) :
    EvalFloatBinOpRel .nondeterministic op f lhsBits rhsBits outBits := by
  dsimp only [EvalFloatBinOpRel] at h
  dsimp only [EvalFloatBinOpRel]
  revert h
  cases hN : isNaNBits f (evalFloatArithBase op f lhsBits rhsBits) with
  | false =>
    intro h
    exact h
  | true =>
    intro h
    dsimp only [nanChoices] at h
    cases h with
    | head =>
      dsimp only [nanChoices, expandNanSigns]
      exact List.Mem.head _
    | tail _ hNil => nomatch hNil

/-- Mode inclusion for `EvalFloatFmaRel`: `.deterministic` implies
`.nondeterministic` (`[propext]` only). -/
theorem evalFloatFmaRel_det_imp_nondet (f : IeeeFormat)
    {aBits bBits cBits outBits : Nat}
    (h : EvalFloatFmaRel .deterministic f aBits bBits cBits outBits) :
    EvalFloatFmaRel .nondeterministic f aBits bBits cBits outBits := by
  dsimp only [EvalFloatFmaRel] at h
  dsimp only [EvalFloatFmaRel]
  revert h
  cases hN : isNaNBits f (evalFloatFmaBase f aBits bBits cBits) with
  | false =>
    intro h
    exact h
  | true =>
    intro h
    dsimp only [nanChoices] at h
    cases h with
    | head =>
      dsimp only [nanChoices, expandNanSigns]
      exact List.Mem.head _
    | tail _ hNil => nomatch hNil

/-- Finite/infinite NaN-collapse law: whenever `evalFloatArithBase` is non-NaN,
`EvalFloatBinOpRel` in ANY mode (including `.nondeterministic`) collapses to
exact equality with `evalFloatArithBase` (`[propext]` only). -/
theorem evalFloatBinOpRel_of_not_nan (mode : FloatArithMode) (op : FloatBinOp)
    (f : IeeeFormat) {lhsBits rhsBits : Nat} (outBits : Nat)
    (hNotNaN : isNaNBits f (evalFloatArithBase op f lhsBits rhsBits) = false) :
    EvalFloatBinOpRel mode op f lhsBits rhsBits outBits ↔
      outBits = evalFloatArithBase op f lhsBits rhsBits := by
  dsimp only [EvalFloatBinOpRel]
  rw [hNotNaN]

/-- Finite/infinite NaN-collapse law for `EvalFloatFmaRel` (`[propext]`
only). -/
theorem evalFloatFmaRel_of_not_nan (mode : FloatArithMode) (f : IeeeFormat)
    {aBits bBits cBits : Nat} (outBits : Nat)
    (hNotNaN : isNaNBits f (evalFloatFmaBase f aBits bBits cBits) = false) :
    EvalFloatFmaRel mode f aBits bBits cBits outBits ↔
      outBits = evalFloatFmaBase f aBits bBits cBits := by
  dsimp only [EvalFloatFmaRel]
  rw [hNotNaN]

/-- Fused branch inclusion in `EvalRelaxedFmaRel` (`[propext]` only). -/
theorem evalRelaxedFmaRel_of_fused (mode : FloatArithMode) (f : IeeeFormat)
    {aBits bBits cBits outBits : Nat}
    (h : EvalFloatFmaRel mode f aBits bBits cBits outBits) :
    EvalRelaxedFmaRel mode f aBits bBits cBits outBits :=
  Or.inl h

/-- Unfused double-rounding branch inclusion in `EvalRelaxedFmaRel`
(`[propext]` only). -/
theorem evalRelaxedFmaRel_of_unfused (mode : FloatArithMode) (f : IeeeFormat)
    {aBits bBits cBits midBits outBits : Nat}
    (hMul : EvalFloatBinOpRel mode .mul f aBits bBits midBits)
    (hAdd : EvalFloatBinOpRel mode .add f midBits cBits outBits) :
    EvalRelaxedFmaRel mode f aBits bBits cBits outBits :=
  Or.inr ⟨midBits, hMul, hAdd⟩

end Anneal.Float

end
