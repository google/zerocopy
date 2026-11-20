import ToyFarkas.Checker

/-!
# Bit-vector ↔ integer transfer for linear constraints

Affine expressions `e = Σ cᵢ xᵢ + k` with integer coefficients are evaluated in two ways:

* over `BitVec w` (`AffExpr.evalBv`): coefficients and constant are embedded with
  `BitVec.ofInt w`, and `+`, `*` wrap modulo `2^w`; the terms are summed left to right,
  `((0 + c₀ x₀) + c₁ x₁) + …`, and the constant is added last;
* over `Int` (`AffExpr.evalInt`), at a reading `ρ : Nat → Int` of the bit-vector variables:
  the **unsigned** reading `uval x i = (x i).toNat` or the **signed** reading
  `sval x i = (x i).toInt`.

A bit-vector comparison `e₁ ≤ e₂` uses `BitVec.ule` (unsigned) or `BitVec.sle` (signed).
The transfer theorems say that, when the *final* integer values of both sides are
representable (`InUnsignedRange w`, resp. `InSignedRange w`), the bit-vector comparison
holds iff the integer comparison of the matching reading holds. No hypothesis on intermediate
values is needed, because wrapping `+`/`*` commute with reduction modulo `2^w`; the
intermediate-value ("no-wrap") form is derived as a corollary.

The fact that wrapping evaluation is reduction of the integer value modulo `2^w`
(`AffExpr.evalBv_eq_ofInt`: `BitVec.ofInt w` commutes with `+` and `*`) is used as a helper
lemma; the results of this file are about comparisons.

"Interval transfer" here means transfer under the representable intervals `[0, 2^w)`
(unsigned) and `[-2^(w-1), 2^(w-1))` (signed, written `-2^w ≤ 2z < 2^w`); no abstract
interval domain or interval-arithmetic transfer function is defined.
-/

namespace Toy.Farkas

/-- An affine expression `Σ cᵢ xᵢ + const` with integer coefficients. -/
structure AffExpr where
  terms : SparseVec
  const : Int
  deriving DecidableEq, Repr

/-- Integer value at a reading `ρ`. -/
def AffExpr.evalInt (e : AffExpr) (ρ : Nat → Int) : Int :=
  SparseVec.eval e.terms ρ + e.const

/-- Wrapping bit-vector evaluation of a sparse linear form, summing the terms left to right:
`((0 + ofInt c₀ * x₀) + ofInt c₁ * x₁) + …`. -/
def SparseVec.evalBv (w : Nat) (v : SparseVec) (x : Nat → BitVec w) : BitVec w :=
  v.foldl (fun s p => s + BitVec.ofInt w p.2 * x p.1) 0#w

/-- Wrapping bit-vector evaluation of an affine expression. -/
def AffExpr.evalBv (w : Nat) (e : AffExpr) (x : Nat → BitVec w) : BitVec w :=
  SparseVec.evalBv w e.terms x + BitVec.ofInt w e.const

/-- Unsigned reading of bit-vector variables as integers. -/
def uval {w : Nat} (x : Nat → BitVec w) : Nat → Int := fun i => ((x i).toNat : Int)

/-- Signed (two's complement) reading of bit-vector variables as integers. -/
def sval {w : Nat} (x : Nat → BitVec w) : Nat → Int := fun i => (x i).toInt

/-- `z` is representable as a `w`-bit unsigned value: `0 ≤ z < 2^w`. -/
def InUnsignedRange (w : Nat) (z : Int) : Prop := 0 ≤ z ∧ z < (2 : Int) ^ w

/-- `z` is representable as a `w`-bit two's-complement value: `-2^w ≤ 2z < 2^w`, i.e.
`-2^(w-1) ≤ z < 2^(w-1)` for `w ≥ 1` and `z = 0` for `w = 0`. (Written with `2z` to avoid the
natural-number subtraction `w - 1`, which would wrongly admit `z = -1` at `w = 0`.) -/
def InSignedRange (w : Nat) (z : Int) : Prop := -((2 : Int) ^ w) ≤ 2 * z ∧ 2 * z < (2 : Int) ^ w

instance (w : Nat) (z : Int) : Decidable (InUnsignedRange w z) :=
  inferInstanceAs (Decidable (_ ∧ _))

instance (w : Nat) (z : Int) : Decidable (InSignedRange w z) :=
  inferInstanceAs (Decidable (_ ∧ _))

/-- The integer values computed by the left-to-right evaluation of `SparseVec.evalBv`, read
through `ρ`, starting from the running sum `acc`: for each term `(i, c)` in order, the coefficient
literal `c`, the product `c * ρ i`, and the new running sum. -/
def SparseVec.intermediatesFrom (v : SparseVec) (ρ : Nat → Int) (acc : Int) : List Int :=
  match v with
  | [] => []
  | p :: v => p.2 :: (p.2 * ρ p.1) :: (acc + p.2 * ρ p.1) ::
      SparseVec.intermediatesFrom v ρ (acc + p.2 * ρ p.1)

/-- Intermediate values of a sparse form: coefficient literals, products, and left-to-right
partial sums (prefix sums), in evaluation order. -/
def SparseVec.intermediates (v : SparseVec) (ρ : Nat → Int) : List Int :=
  SparseVec.intermediatesFrom v ρ 0

/-- Intermediate values of an affine expression: those of its linear part, then its constant
literal and its final value (the constant is added last). -/
def AffExpr.intermediates (e : AffExpr) (ρ : Nat → Int) : List Int :=
  SparseVec.intermediates e.terms ρ ++ [e.const, e.evalInt ρ]

/-- Unsigned no-wrap: every intermediate value (coefficient literals, products, left-to-right
partial sums, the constant, and the final value) is in the unsigned range.

This is a toy model of "no intermediate unsigned overflow". It differs from machine-level
no-wrap conditions (for example LLVM `nuw`) because `AffExpr` has no subtraction: `x₀ - x₁` is
`x₀ + (-1) * x₁`, so any term with a negative coefficient fails `NoWrapU` even when the machine
subtraction would not underflow (`ex_noWrapU_rejects_machine_subtraction`). -/
def NoWrapU (w : Nat) (e : AffExpr) (ρ : Nat → Int) : Prop :=
  ∀ z ∈ e.intermediates ρ, InUnsignedRange w z

/-- Signed no-wrap: every intermediate value (coefficient literals, products, left-to-right
partial sums, the constant, and the final value) is in the signed range. A toy model of "no
intermediate signed overflow" for the left-to-right evaluation order of `SparseVec.evalBv`. -/
def NoWrapS (w : Nat) (e : AffExpr) (ρ : Nat → Int) : Prop :=
  ∀ z ∈ e.intermediates ρ, InSignedRange w z

instance (w : Nat) (e : AffExpr) (ρ : Nat → Int) : Decidable (NoWrapU w e ρ) :=
  inferInstanceAs (Decidable (∀ z ∈ e.intermediates ρ, InUnsignedRange w z))

instance (w : Nat) (e : AffExpr) (ρ : Nat → Int) : Decidable (NoWrapS w e ρ) :=
  inferInstanceAs (Decidable (∀ z ∈ e.intermediates ρ, InSignedRange w z))

/-- A bit-vector point with `x₀ = a`, `x₁ = b`, all other variables `0`. -/
def bvPt2 {w : Nat} (a b : BitVec w) : Nat → BitVec w :=
  fun i => if i = 0 then a else if i = 1 then b else 0#w

/-! ## Definition examples -/

/-- `x₀ + x₀` (two entries for the same variable). -/
def eDouble : AffExpr := ⟨[(0, 1), (0, 1)], 0⟩
/-- The constant expression `k`. -/
def eConst (k : Int) : AffExpr := ⟨[], k⟩
/-- `x₀`. -/
def eX0 : AffExpr := ⟨[(0, 1)], 0⟩
/-- `x₁`. -/
def eX1 : AffExpr := ⟨[(1, 1)], 0⟩

theorem ex_evalInt_pos : eDouble.evalInt (uval (bvPt2 (200#8) 0#8)) = 400 := by decide
theorem ex_evalInt_neg : eDouble.evalInt (uval (bvPt2 (200#8) 0#8)) ≠ 144 := by decide
/-- Positive example: bit-vector evaluation wraps (`200 + 200 = 144` in 8 bits). -/
theorem ex_evalBv_pos : eDouble.evalBv 8 (bvPt2 (200#8) 0#8) = 144#8 := by decide
theorem ex_evalBv_neg : (eDouble.evalBv 8 (bvPt2 (200#8) 0#8)).toNat ≠ 400 := by decide
theorem ex_sparse_evalBv_pos : SparseVec.evalBv 8 [(0, -1)] (bvPt2 (1#8) 0#8) = 255#8 := by decide
theorem ex_sparse_evalBv_neg : SparseVec.evalBv 8 [(0, -1)] (bvPt2 (1#8) 0#8) ≠ 0#8 := by decide
/-- The two readings differ on `255#8`. -/
theorem ex_uval_pos : uval (bvPt2 (255#8) 0#8) 0 = 255 := by decide
theorem ex_uval_neg : uval (bvPt2 (255#8) 0#8) 0 ≠ -1 := by decide
theorem ex_sval_pos : sval (bvPt2 (255#8) 0#8) 0 = -1 := by decide
theorem ex_sval_neg : sval (bvPt2 (255#8) 0#8) 0 ≠ 255 := by decide
theorem ex_inUnsignedRange_pos : InUnsignedRange 8 255 := by decide
theorem ex_inUnsignedRange_neg : ¬ InUnsignedRange 8 256 ∧ ¬ InUnsignedRange 8 (-1) := by decide
theorem ex_inSignedRange_pos : InSignedRange 8 (-128) ∧ InSignedRange 8 127 := by decide
theorem ex_inSignedRange_neg : ¬ InSignedRange 8 128 ∧ ¬ InSignedRange 8 (-129) := by decide
/-- Negative example at width `0`: only `0` is representable (in particular not `-1`). -/
theorem ex_inSignedRange_zero_width : InSignedRange 0 0 ∧ ¬ InSignedRange 0 (-1) := by decide
/-- Positive example: coefficient literal `1`, product `200`, running sum `200`, then `1`, `200`,
running sum `400`, then the constant `0` and the final value `400` (left to right). -/
theorem ex_intermediates_pos :
    eDouble.intermediates (uval (bvPt2 (200#8) 0#8)) = [1, 200, 200, 1, 200, 400, 0, 400] := by
  decide
theorem ex_intermediates_neg :
    eDouble.intermediates (uval (bvPt2 (200#8) 0#8)) ≠ [400] := by decide
theorem ex_noWrapU_pos : NoWrapU 8 eDouble (uval (bvPt2 (100#8) 0#8)) := by decide
theorem ex_noWrapU_neg : ¬ NoWrapU 8 eDouble (uval (bvPt2 (200#8) 0#8)) := by decide
theorem ex_noWrapS_pos : NoWrapS 8 eDouble (sval (bvPt2 (50#8) 0#8)) := by decide
theorem ex_noWrapS_neg : ¬ NoWrapS 8 eDouble (sval (bvPt2 (100#8) 0#8)) := by decide
/-- Negative example: a coefficient literal that wraps (`1000` in 8 bits) violates both no-wrap
predicates even when its variable is `0`. -/
theorem ex_noWrap_checks_coefficient_literals :
    ¬ NoWrapU 8 ⟨[(0, 1000)], 0⟩ (uval (bvPt2 0#8 0#8)) ∧
    ¬ NoWrapS 8 ⟨[(0, 1000)], 0⟩ (sval (bvPt2 0#8 0#8)) := by decide
/-- Divergence from machine-level unsigned no-wrap: `x₀ - x₁` at `(10, 3)` is `10 - 3 = 7` without
underflow on an 8-bit machine, yet `NoWrapU` fails because the encoding `x₀ + (-1) * x₁` has the
coefficient literal `-1` and the product `-3`. -/
theorem ex_noWrapU_rejects_machine_subtraction :
    (10#8 - 3#8).toNat = 7 ∧
    AffExpr.evalInt ⟨[(0, 1), (1, -1)], 0⟩ (uval (bvPt2 (10#8) (3#8))) = 7 ∧
    ¬ NoWrapU 8 ⟨[(0, 1), (1, -1)], 0⟩ (uval (bvPt2 (10#8) (3#8))) := by decide

/-! ## Helper: wrapping evaluation is reduction of the integer value -/

theorem SparseVec.foldl_evalBv_eq_ofInt (w : Nat) (v : SparseVec) (x : Nat → BitVec w)
    (ρ : Nat → Int) (hρ : ∀ i, BitVec.ofInt w (ρ i) = x i) (acc : Int) :
    v.foldl (fun s p => s + BitVec.ofInt w p.2 * x p.1) (BitVec.ofInt w acc) =
      BitVec.ofInt w (acc + SparseVec.eval v ρ) := by
  induction v generalizing acc with
  | nil => simp
  | cons a v ih =>
    rw [List.foldl_cons, ← hρ a.1, ← BitVec.ofInt_mul, ← BitVec.ofInt_add, ih,
      SparseVec.eval_cons, Int.add_assoc]

theorem SparseVec.evalBv_eq_ofInt (w : Nat) (v : SparseVec) (x : Nat → BitVec w)
    (ρ : Nat → Int) (hρ : ∀ i, BitVec.ofInt w (ρ i) = x i) :
    SparseVec.evalBv w v x = BitVec.ofInt w (SparseVec.eval v ρ) := by
  have h := SparseVec.foldl_evalBv_eq_ofInt w v x ρ hρ 0
  rw [Int.zero_add] at h
  rw [SparseVec.evalBv, ← h]
  congr 1

theorem AffExpr.evalBv_eq_ofInt (w : Nat) (e : AffExpr) (x : Nat → BitVec w)
    (ρ : Nat → Int) (hρ : ∀ i, BitVec.ofInt w (ρ i) = x i) :
    e.evalBv w x = BitVec.ofInt w (e.evalInt ρ) := by
  rw [AffExpr.evalBv, SparseVec.evalBv_eq_ofInt w e.terms x ρ hρ, AffExpr.evalInt, BitVec.ofInt_add]

theorem ofInt_uval {w : Nat} (x : Nat → BitVec w) (i : Nat) : BitVec.ofInt w (uval x i) = x i := by
  simp [uval, BitVec.ofNat_toNat]

theorem ofInt_sval {w : Nat} (x : Nat → BitVec w) (i : Nat) : BitVec.ofInt w (sval x i) = x i := by
  simp [sval]

theorem toNat_ofInt_of_inUnsignedRange {w : Nat} {z : Int} (h : InUnsignedRange w z) :
    ((BitVec.ofInt w z).toNat : Int) = z := by
  rw [BitVec.toNat_ofInt, Int.natCast_pow]
  simp only [Int.cast_ofNat_Int]
  rw [Int.emod_eq_of_lt h.1 h.2]
  exact Int.toNat_of_nonneg h.1

theorem toInt_ofInt_of_inSignedRange {w : Nat} {z : Int} (h : InSignedRange w z) :
    (BitVec.ofInt w z).toInt = z := by
  rw [BitVec.toInt_ofInt]
  apply Int.bmod_eq_of_le_mul_two
  · have := h.1; rw [Int.natCast_pow]; simp only [Int.cast_ofNat_Int]; omega
  · have := h.2; rw [Int.natCast_pow]; simp only [Int.cast_ofNat_Int]; omega

/-! ## Transfer theorems -/

/-- **Unsigned transfer.** If the integer values of `e₁` and `e₂` under the unsigned reading
are both in `[0, 2^w)`, then the wrapping bit-vector comparison `e₁ ≤ᵤ e₂` holds iff the
integer comparison holds. -/
theorem bv_ule_iff_int_le_of_inUnsignedRange (w : Nat) (e₁ e₂ : AffExpr) (x : Nat → BitVec w)
    (h₁ : InUnsignedRange w (e₁.evalInt (uval x))) (h₂ : InUnsignedRange w (e₂.evalInt (uval x))) :
    (e₁.evalBv w x).ule (e₂.evalBv w x) = true ↔ e₁.evalInt (uval x) ≤ e₂.evalInt (uval x) := by
  rw [AffExpr.evalBv_eq_ofInt w e₁ x _ (ofInt_uval x), AffExpr.evalBv_eq_ofInt w e₂ x _ (ofInt_uval x),
    BitVec.ule_eq_decide, decide_eq_true_iff]
  have a := toNat_ofInt_of_inUnsignedRange h₁
  have b := toNat_ofInt_of_inUnsignedRange h₂
  omega

/-- **Unsigned transfer, strict.** Same hypotheses, for `<ᵤ`. -/
theorem bv_ult_iff_int_lt_of_inUnsignedRange (w : Nat) (e₁ e₂ : AffExpr) (x : Nat → BitVec w)
    (h₁ : InUnsignedRange w (e₁.evalInt (uval x))) (h₂ : InUnsignedRange w (e₂.evalInt (uval x))) :
    (e₁.evalBv w x).ult (e₂.evalBv w x) = true ↔ e₁.evalInt (uval x) < e₂.evalInt (uval x) := by
  rw [AffExpr.evalBv_eq_ofInt w e₁ x _ (ofInt_uval x), AffExpr.evalBv_eq_ofInt w e₂ x _ (ofInt_uval x),
    BitVec.ult_eq_decide, decide_eq_true_iff]
  have a := toNat_ofInt_of_inUnsignedRange h₁
  have b := toNat_ofInt_of_inUnsignedRange h₂
  omega

/-- **Signed transfer.** If the integer values of `e₁` and `e₂` under the signed reading are
both in the `w`-bit two's-complement range, then the wrapping bit-vector comparison `e₁ ≤ₛ e₂`
holds iff the integer comparison holds. -/
theorem bv_sle_iff_int_le_of_inSignedRange (w : Nat) (e₁ e₂ : AffExpr) (x : Nat → BitVec w)
    (h₁ : InSignedRange w (e₁.evalInt (sval x))) (h₂ : InSignedRange w (e₂.evalInt (sval x))) :
    (e₁.evalBv w x).sle (e₂.evalBv w x) = true ↔ e₁.evalInt (sval x) ≤ e₂.evalInt (sval x) := by
  rw [AffExpr.evalBv_eq_ofInt w e₁ x _ (ofInt_sval x), AffExpr.evalBv_eq_ofInt w e₂ x _ (ofInt_sval x),
    BitVec.sle_eq_decide, decide_eq_true_iff, toInt_ofInt_of_inSignedRange h₁,
    toInt_ofInt_of_inSignedRange h₂]

/-- **Signed transfer, strict.** Same hypotheses, for `<ₛ`. -/
theorem bv_slt_iff_int_lt_of_inSignedRange (w : Nat) (e₁ e₂ : AffExpr) (x : Nat → BitVec w)
    (h₁ : InSignedRange w (e₁.evalInt (sval x))) (h₂ : InSignedRange w (e₂.evalInt (sval x))) :
    (e₁.evalBv w x).slt (e₂.evalBv w x) = true ↔ e₁.evalInt (sval x) < e₂.evalInt (sval x) := by
  rw [AffExpr.evalBv_eq_ofInt w e₁ x _ (ofInt_sval x), AffExpr.evalBv_eq_ofInt w e₂ x _ (ofInt_sval x),
    BitVec.slt_eq_decide, decide_eq_true_iff, toInt_ofInt_of_inSignedRange h₁,
    toInt_ofInt_of_inSignedRange h₂]

/-! ## Forward transfer needs only one-sided bounds -/

/-- **Unsigned forward transfer with one-sided bounds.** If `e₁ < 2^w` and `0 ≤ e₂` (integer values
under the unsigned reading), then `e₁ ≤ᵤ e₂` implies `e₁ ≤ e₂` and `e₁ <ᵤ e₂` implies `e₁ < e₂`. If
`e₁ < 0` or `e₂ ≥ 2^w`, the integer comparison holds for any outcome of the bit-vector comparison. -/
theorem bv_ule_ult_imp_int_of_lhs_lt_of_rhs_nonneg (w : Nat) (e₁ e₂ : AffExpr) (x : Nat → BitVec w)
    (h₁ : e₁.evalInt (uval x) < (2 : Int) ^ w) (h₂ : 0 ≤ e₂.evalInt (uval x)) :
    ((e₁.evalBv w x).ule (e₂.evalBv w x) = true → e₁.evalInt (uval x) ≤ e₂.evalInt (uval x)) ∧
    ((e₁.evalBv w x).ult (e₂.evalBv w x) = true → e₁.evalInt (uval x) < e₂.evalInt (uval x)) := by
  by_cases h1lo : 0 ≤ e₁.evalInt (uval x)
  · by_cases h2hi : e₂.evalInt (uval x) < (2 : Int) ^ w
    · exact ⟨(bv_ule_iff_int_le_of_inUnsignedRange w e₁ e₂ x ⟨h1lo, h₁⟩ ⟨h₂, h2hi⟩).mp,
        (bv_ult_iff_int_lt_of_inUnsignedRange w e₁ e₂ x ⟨h1lo, h₁⟩ ⟨h₂, h2hi⟩).mp⟩
    · exact ⟨fun _ => by omega, fun _ => by omega⟩
  · exact ⟨fun _ => by omega, fun _ => by omega⟩

/-- **Signed forward transfer with one-sided bounds.** If `2 e₁ < 2^w` and `-2^w ≤ 2 e₂` (integer
values under the signed reading), then `e₁ ≤ₛ e₂` implies `e₁ ≤ e₂` and `e₁ <ₛ e₂` implies `e₁ < e₂`. -/
theorem bv_sle_slt_imp_int_of_lhs_lt_of_rhs_ge (w : Nat) (e₁ e₂ : AffExpr) (x : Nat → BitVec w)
    (h₁ : 2 * e₁.evalInt (sval x) < (2 : Int) ^ w) (h₂ : -((2 : Int) ^ w) ≤ 2 * e₂.evalInt (sval x)) :
    ((e₁.evalBv w x).sle (e₂.evalBv w x) = true → e₁.evalInt (sval x) ≤ e₂.evalInt (sval x)) ∧
    ((e₁.evalBv w x).slt (e₂.evalBv w x) = true → e₁.evalInt (sval x) < e₂.evalInt (sval x)) := by
  by_cases h1lo : -((2 : Int) ^ w) ≤ 2 * e₁.evalInt (sval x)
  · by_cases h2hi : 2 * e₂.evalInt (sval x) < (2 : Int) ^ w
    · exact ⟨(bv_sle_iff_int_le_of_inSignedRange w e₁ e₂ x ⟨h1lo, h₁⟩ ⟨h₂, h2hi⟩).mp,
        (bv_slt_iff_int_lt_of_inSignedRange w e₁ e₂ x ⟨h1lo, h₁⟩ ⟨h₂, h2hi⟩).mp⟩
    · exact ⟨fun _ => by omega, fun _ => by omega⟩
  · exact ⟨fun _ => by omega, fun _ => by omega⟩

/-! ## The intermediate-value (no-wrap) form, derived -/

theorem inUnsignedRange_evalInt_of_noWrapU (w : Nat) (e : AffExpr) (ρ : Nat → Int)
    (h : NoWrapU w e ρ) : InUnsignedRange w (e.evalInt ρ) :=
  h _ (by simp [AffExpr.intermediates])

theorem inSignedRange_evalInt_of_noWrapS (w : Nat) (e : AffExpr) (ρ : Nat → Int)
    (h : NoWrapS w e ρ) : InSignedRange w (e.evalInt ρ) :=
  h _ (by simp [AffExpr.intermediates])

/-- **Unsigned transfer under no intermediate wrap** (corollary of the unsigned transfer, which
needs only the final values in range; see `ce_noWrap_not_needed_for_wrapping_eval`). -/
theorem bv_ule_ult_iff_int_of_noWrapU (w : Nat) (e₁ e₂ : AffExpr) (x : Nat → BitVec w)
    (h₁ : NoWrapU w e₁ (uval x)) (h₂ : NoWrapU w e₂ (uval x)) :
    ((e₁.evalBv w x).ule (e₂.evalBv w x) = true ↔ e₁.evalInt (uval x) ≤ e₂.evalInt (uval x)) ∧
    ((e₁.evalBv w x).ult (e₂.evalBv w x) = true ↔ e₁.evalInt (uval x) < e₂.evalInt (uval x)) :=
  ⟨bv_ule_iff_int_le_of_inUnsignedRange w e₁ e₂ x
    (inUnsignedRange_evalInt_of_noWrapU w e₁ _ h₁) (inUnsignedRange_evalInt_of_noWrapU w e₂ _ h₂),
   bv_ult_iff_int_lt_of_inUnsignedRange w e₁ e₂ x
    (inUnsignedRange_evalInt_of_noWrapU w e₁ _ h₁) (inUnsignedRange_evalInt_of_noWrapU w e₂ _ h₂)⟩

/-- **Signed transfer under no intermediate wrap** (corollary of the signed transfer). -/
theorem bv_sle_slt_iff_int_of_noWrapS (w : Nat) (e₁ e₂ : AffExpr) (x : Nat → BitVec w)
    (h₁ : NoWrapS w e₁ (sval x)) (h₂ : NoWrapS w e₂ (sval x)) :
    ((e₁.evalBv w x).sle (e₂.evalBv w x) = true ↔ e₁.evalInt (sval x) ≤ e₂.evalInt (sval x)) ∧
    ((e₁.evalBv w x).slt (e₂.evalBv w x) = true ↔ e₁.evalInt (sval x) < e₂.evalInt (sval x)) :=
  ⟨bv_sle_iff_int_le_of_inSignedRange w e₁ e₂ x
    (inSignedRange_evalInt_of_noWrapS w e₁ _ h₁) (inSignedRange_evalInt_of_noWrapS w e₂ _ h₂),
   bv_slt_iff_int_lt_of_inSignedRange w e₁ e₂ x
    (inSignedRange_evalInt_of_noWrapS w e₁ _ h₁) (inSignedRange_evalInt_of_noWrapS w e₂ _ h₂)⟩

end Toy.Farkas
