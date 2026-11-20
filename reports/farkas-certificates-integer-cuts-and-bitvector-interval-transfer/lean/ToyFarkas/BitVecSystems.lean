import ToyFarkas.BitVecTransfer
import ToyFarkas.Completeness

/-!
# Bit-vector transfer: combined statements, atom systems, and counterexamples
-/

namespace Toy.Farkas

/-! ## Combined transfer statements -/

/-- **Unsigned transfer (both relations).** If the integer values of `e₁` and `e₂` under the
unsigned reading lie in `[0, 2^w)`, then `e₁ ≤ᵤ e₂` and `e₁ <ᵤ e₂` over `BitVec w` (wrapping
evaluation) hold iff `e₁ ≤ e₂`, resp. `e₁ < e₂`, hold over `Int`. -/
theorem bv_ule_ult_iff_int_of_inUnsignedRange (w : Nat) (e₁ e₂ : AffExpr) (x : Nat → BitVec w)
    (h₁ : InUnsignedRange w (e₁.evalInt (uval x))) (h₂ : InUnsignedRange w (e₂.evalInt (uval x))) :
    ((e₁.evalBv w x).ule (e₂.evalBv w x) = true ↔ e₁.evalInt (uval x) ≤ e₂.evalInt (uval x)) ∧
    ((e₁.evalBv w x).ult (e₂.evalBv w x) = true ↔ e₁.evalInt (uval x) < e₂.evalInt (uval x)) :=
  ⟨bv_ule_iff_int_le_of_inUnsignedRange w e₁ e₂ x h₁ h₂,
   bv_ult_iff_int_lt_of_inUnsignedRange w e₁ e₂ x h₁ h₂⟩

/-- **Signed transfer (both relations).** If the integer values of `e₁` and `e₂` under the
signed reading lie in the `w`-bit two's-complement range, then `e₁ ≤ₛ e₂` and `e₁ <ₛ e₂` over
`BitVec w` hold iff `e₁ ≤ e₂`, resp. `e₁ < e₂`, hold over `Int`. -/
theorem bv_sle_slt_iff_int_of_inSignedRange (w : Nat) (e₁ e₂ : AffExpr) (x : Nat → BitVec w)
    (h₁ : InSignedRange w (e₁.evalInt (sval x))) (h₂ : InSignedRange w (e₂.evalInt (sval x))) :
    ((e₁.evalBv w x).sle (e₂.evalBv w x) = true ↔ e₁.evalInt (sval x) ≤ e₂.evalInt (sval x)) ∧
    ((e₁.evalBv w x).slt (e₂.evalBv w x) = true ↔ e₁.evalInt (sval x) < e₂.evalInt (sval x)) :=
  ⟨bv_sle_iff_int_le_of_inSignedRange w e₁ e₂ x h₁ h₂,
   bv_slt_iff_int_lt_of_inSignedRange w e₁ e₂ x h₁ h₂⟩

/-! ## Bit-vector atoms, their integer translation, and the Farkas checker -/

/-- A bit-vector comparison atom `lhs ⋈ rhs` between affine expressions, `⋈ ∈ {≤, <}`. -/
structure BvAtom where
  lhs : AffExpr
  rel : Rel
  rhs : AffExpr
  deriving DecidableEq, Repr

/-- Unsigned reading of an atom: wrapping evaluation of both sides, compared with `ule`/`ult`. -/
def BvAtom.HoldsU (w : Nat) (a : BvAtom) (x : Nat → BitVec w) : Prop :=
  match a.rel with
  | .le => (a.lhs.evalBv w x).ule (a.rhs.evalBv w x) = true
  | .lt => (a.lhs.evalBv w x).ult (a.rhs.evalBv w x) = true

/-- Signed reading of an atom: wrapping evaluation of both sides, compared with `sle`/`slt`. -/
def BvAtom.HoldsS (w : Nat) (a : BvAtom) (x : Nat → BitVec w) : Prop :=
  match a.rel with
  | .le => (a.lhs.evalBv w x).sle (a.rhs.evalBv w x) = true
  | .lt => (a.lhs.evalBv w x).slt (a.rhs.evalBv w x) = true

instance (w : Nat) (a : BvAtom) (x : Nat → BitVec w) : Decidable (a.HoldsU w x) := by
  unfold BvAtom.HoldsU; split <;> infer_instance
instance (w : Nat) (a : BvAtom) (x : Nat → BitVec w) : Decidable (a.HoldsS w x) := by
  unfold BvAtom.HoldsS; split <;> infer_instance

/-- The integer constraint corresponding to an atom, in the normal form of `Constraint`:
`(lhs.terms - rhs.terms) · x ⋈ rhs.const - lhs.const`. (Moving terms across the comparison is
valid over `Int`, not over `BitVec w`; see `ce_bv_rearrangement_unsound`.) -/
def BvAtom.toConstraint (a : BvAtom) : Constraint :=
  ⟨a.lhs.terms ++ SparseVec.smul (-1) a.rhs.terms, a.rel, a.rhs.const - a.lhs.const⟩

/-- `x₀ + 1 ≤ x₁`. -/
def atomEx : BvAtom := ⟨⟨[(0, 1)], 1⟩, .le, ⟨[(1, 1)], 0⟩⟩

theorem ex_bvAtom_holdsU_pos : atomEx.HoldsU 8 (bvPt2 (3#8) (4#8)) := by decide
/-- Negative example: `5 ≤ᵤ 4` fails. -/
theorem ex_bvAtom_holdsU_neg : ¬ atomEx.HoldsU 8 (bvPt2 (4#8) (4#8)) := by decide
/-- Wrapping example: at `x₀ = 255`, `x₀ + 1` wraps to `0`, so the atom holds at `x₁ = 0` although
`256 ≤ 0` is false over `Int`. -/
theorem ex_bvAtom_holdsU_wrap : atomEx.HoldsU 8 (bvPt2 (255#8) (0#8)) := by decide
theorem ex_bvAtom_holdsS_pos : atomEx.HoldsS 8 (bvPt2 (255#8) (0#8)) := by decide
theorem ex_bvAtom_holdsS_neg : ¬ atomEx.HoldsS 8 (bvPt2 (5#8) (3#8)) := by decide
theorem ex_bvAtom_toConstraint_pos : atomEx.toConstraint = ⟨[(0, 1), (1, -1)], .le, -1⟩ := by decide
theorem ex_bvAtom_toConstraint_neg : atomEx.toConstraint ≠ ⟨[(0, 1), (1, -1)], .le, 1⟩ := by decide

theorem BvAtom.toConstraint_holdsInt_iff (a : BvAtom) (ρ : Nat → Int) :
    a.toConstraint.HoldsInt ρ ↔ a.rel.Sat (a.lhs.evalInt ρ) (a.rhs.evalInt ρ) := by
  obtain ⟨⟨lt, lc⟩, rel, ⟨rt, rc⟩⟩ := a
  cases rel <;>
    simp [BvAtom.toConstraint, Constraint.HoldsInt, Rel.Sat, AffExpr.evalInt,
      SparseVec.eval_append, SparseVec.eval_smul] <;> omega

theorem BvAtom.holdsU_iff_holdsInt_of_inUnsignedRange (w : Nat) (a : BvAtom) (x : Nat → BitVec w)
    (h₁ : InUnsignedRange w (a.lhs.evalInt (uval x))) (h₂ : InUnsignedRange w (a.rhs.evalInt (uval x))) :
    a.HoldsU w x ↔ a.toConstraint.HoldsInt (uval x) := by
  rw [BvAtom.toConstraint_holdsInt_iff]
  have T := bv_ule_ult_iff_int_of_inUnsignedRange w a.lhs a.rhs x h₁ h₂
  obtain ⟨l, rel, r⟩ := a
  cases rel
  · exact T.1
  · exact T.2

theorem BvAtom.holdsS_iff_holdsInt_of_inSignedRange (w : Nat) (a : BvAtom) (x : Nat → BitVec w)
    (h₁ : InSignedRange w (a.lhs.evalInt (sval x))) (h₂ : InSignedRange w (a.rhs.evalInt (sval x))) :
    a.HoldsS w x ↔ a.toConstraint.HoldsInt (sval x) := by
  rw [BvAtom.toConstraint_holdsInt_iff]
  have T := bv_sle_slt_iff_int_of_inSignedRange w a.lhs a.rhs x h₁ h₂
  obtain ⟨l, rel, r⟩ := a
  cases rel
  · exact T.1
  · exact T.2

theorem BvAtom.holdsInt_of_holdsU_of_lhs_lt_of_rhs_nonneg (w : Nat) (a : BvAtom) (x : Nat → BitVec w)
    (h₁ : a.lhs.evalInt (uval x) < (2 : Int) ^ w) (h₂ : 0 ≤ a.rhs.evalInt (uval x))
    (h : a.HoldsU w x) : a.toConstraint.HoldsInt (uval x) := by
  rw [BvAtom.toConstraint_holdsInt_iff]
  have T := bv_ule_ult_imp_int_of_lhs_lt_of_rhs_nonneg w a.lhs a.rhs x h₁ h₂
  obtain ⟨l, rel, r⟩ := a
  cases rel
  · exact T.1 h
  · exact T.2 h

theorem BvAtom.holdsInt_of_holdsS_of_lhs_lt_of_rhs_ge (w : Nat) (a : BvAtom) (x : Nat → BitVec w)
    (h₁ : 2 * a.lhs.evalInt (sval x) < (2 : Int) ^ w)
    (h₂ : -((2 : Int) ^ w) ≤ 2 * a.rhs.evalInt (sval x))
    (h : a.HoldsS w x) : a.toConstraint.HoldsInt (sval x) := by
  rw [BvAtom.toConstraint_holdsInt_iff]
  have T := bv_sle_slt_imp_int_of_lhs_lt_of_rhs_ge w a.lhs a.rhs x h₁ h₂
  obtain ⟨l, rel, r⟩ := a
  cases rel
  · exact T.1 h
  · exact T.2 h

/-- **Farkas certificates refute bit-vector systems under one-sided range facts (unsigned).** Let
`A` be a list of bit-vector atoms `lhs ⋈ rhs` and suppose `checkFarkas` accepts `cert` for their
integer translations. Let `x` be a bit-vector point at which every atom with a positive multiplier
has left-hand integer value (unsigned reading) `< 2^w` and right-hand integer value `≥ 0`. Then
those positively weighted atoms do not all hold in the unsigned bit-vector reading at `x`. -/
theorem checkFarkas_refutes_bvU_posSupport_of_lhs_lt_of_rhs_nonneg (A : List BvAtom)
    (cert : List Int) (h : checkFarkas (A.map BvAtom.toConstraint) cert = true)
    (w : Nat) (x : Nat → BitVec w)
    (hl : ∀ a ∈ posSupport cert A, a.lhs.evalInt (uval x) < (2 : Int) ^ w)
    (hr : ∀ a ∈ posSupport cert A, 0 ≤ a.rhs.evalInt (uval x)) :
    ¬ ∀ a ∈ posSupport cert A, a.HoldsU w x := by
  intro hA
  apply checkFarkas_sound_int_posSupport _ cert h (uval x)
  rw [posSupport_map]
  intro c hc
  obtain ⟨a, ha, rfl⟩ := List.mem_map.mp hc
  exact BvAtom.holdsInt_of_holdsU_of_lhs_lt_of_rhs_nonneg w a x (hl a ha) (hr a ha) (hA a ha)

/-- **Farkas certificates refute bit-vector systems under one-sided range facts (signed).** As
above, for the signed reading: every positively weighted atom has `2 * lhs < 2^w` and
`-2^w ≤ 2 * rhs` (integer values under the signed reading). -/
theorem checkFarkas_refutes_bvS_posSupport_of_lhs_lt_of_rhs_ge (A : List BvAtom)
    (cert : List Int) (h : checkFarkas (A.map BvAtom.toConstraint) cert = true)
    (w : Nat) (x : Nat → BitVec w)
    (hl : ∀ a ∈ posSupport cert A, 2 * a.lhs.evalInt (sval x) < (2 : Int) ^ w)
    (hr : ∀ a ∈ posSupport cert A, -((2 : Int) ^ w) ≤ 2 * a.rhs.evalInt (sval x)) :
    ¬ ∀ a ∈ posSupport cert A, a.HoldsS w x := by
  intro hA
  apply checkFarkas_sound_int_posSupport _ cert h (sval x)
  rw [posSupport_map]
  intro c hc
  obtain ⟨a, ha, rfl⟩ := List.mem_map.mp hc
  exact BvAtom.holdsInt_of_holdsS_of_lhs_lt_of_rhs_ge w a x (hl a ha) (hr a ha) (hA a ha)

/-- Two-sided corollary (unsigned): range facts `[0, 2^w)` on both sides of every atom. -/
theorem checkFarkas_refutes_bvU_of_inUnsignedRange (A : List BvAtom) (cert : List Int)
    (h : checkFarkas (A.map BvAtom.toConstraint) cert = true) (w : Nat) (x : Nat → BitVec w)
    (hl : ∀ a ∈ A, InUnsignedRange w (a.lhs.evalInt (uval x)))
    (hr : ∀ a ∈ A, InUnsignedRange w (a.rhs.evalInt (uval x))) :
    ¬ ∀ a ∈ A, a.HoldsU w x := fun hA =>
  checkFarkas_refutes_bvU_posSupport_of_lhs_lt_of_rhs_nonneg A cert h w x
    (fun a ha => (hl a (mem_of_mem_posSupport ha)).2) (fun a ha => (hr a (mem_of_mem_posSupport ha)).1)
    (fun a ha => hA a (mem_of_mem_posSupport ha))

/-- Two-sided corollary (signed): signed range on both sides of every atom. -/
theorem checkFarkas_refutes_bvS_of_inSignedRange (A : List BvAtom) (cert : List Int)
    (h : checkFarkas (A.map BvAtom.toConstraint) cert = true) (w : Nat) (x : Nat → BitVec w)
    (hl : ∀ a ∈ A, InSignedRange w (a.lhs.evalInt (sval x)))
    (hr : ∀ a ∈ A, InSignedRange w (a.rhs.evalInt (sval x))) :
    ¬ ∀ a ∈ A, a.HoldsS w x := fun hA =>
  checkFarkas_refutes_bvS_posSupport_of_lhs_lt_of_rhs_ge A cert h w x
    (fun a ha => (hl a (mem_of_mem_posSupport ha)).2) (fun a ha => (hr a (mem_of_mem_posSupport ha)).1)
    (fun a ha => hA a (mem_of_mem_posSupport ha))

/-! ## Non-vacuity -/

/-- Non-vacuity of unsigned transfer: `x₀ + x₀ ≤ᵤ 150` at `x₀ = 70` (both sides in range). -/
theorem nv_bv_ule_ult_transfer :
    InUnsignedRange 8 (eDouble.evalInt (uval (bvPt2 (70#8) 0#8))) ∧
    InUnsignedRange 8 ((eConst 150).evalInt (uval (bvPt2 (70#8) 0#8))) ∧
    (eDouble.evalBv 8 (bvPt2 (70#8) 0#8)).ule ((eConst 150).evalBv 8 (bvPt2 (70#8) 0#8)) = true := by
  decide

/-- Non-vacuity of signed transfer: `x₀ + x₀ ≤ₛ 0` at `x₀ = -50` (both sides in range). -/
theorem nv_bv_sle_slt_transfer :
    InSignedRange 8 (eDouble.evalInt (sval (bvPt2 (206#8) 0#8))) ∧
    InSignedRange 8 ((eConst 0).evalInt (sval (bvPt2 (206#8) 0#8))) ∧
    sval (bvPt2 (206#8) 0#8) 0 = -50 ∧
    (eDouble.evalBv 8 (bvPt2 (206#8) 0#8)).sle ((eConst 0).evalBv 8 (bvPt2 (206#8) 0#8)) = true := by
  decide

theorem nv_bv_ule_ult_noWrapU :
    NoWrapU 8 eDouble (uval (bvPt2 (70#8) 0#8)) ∧ NoWrapU 8 (eConst 150) (uval (bvPt2 (70#8) 0#8)) := by
  decide

theorem nv_bv_sle_slt_noWrapS :
    NoWrapS 8 eDouble (sval (bvPt2 (206#8) 0#8)) ∧ NoWrapS 8 (eConst 0) (sval (bvPt2 (206#8) 0#8)) := by
  decide

/-- `{x₀ <ᵤ x₁, x₁ ≤ᵤ x₀}`, refuted by the certificate `(1, 1)` (derives `0 < 0`). -/
def atomsLtLe : List BvAtom := [⟨⟨[(0, 1)], 0⟩, .lt, ⟨[(1, 1)], 0⟩⟩, ⟨⟨[(1, 1)], 0⟩, .le, ⟨[(0, 1)], 0⟩⟩]

/-- Non-vacuity of the unsigned refutation (one-sided form): the certificate is accepted, both
atoms are positively weighted, and at `x = (5, 9)` every one-sided range fact holds. -/
theorem nv_checkFarkas_refutes_bvU :
    checkFarkas (atomsLtLe.map BvAtom.toConstraint) [1, 1] = true ∧
    posSupport [1, 1] atomsLtLe = atomsLtLe ∧
    (∀ a ∈ posSupport [1, 1] atomsLtLe, a.lhs.evalInt (uval (bvPt2 (5#8) (9#8))) < (2 : Int) ^ 8) ∧
    (∀ a ∈ posSupport [1, 1] atomsLtLe, 0 ≤ a.rhs.evalInt (uval (bvPt2 (5#8) (9#8)))) := by decide

/-- Non-vacuity of the signed refutation (one-sided form), same atoms at `x = (-3, 9)`. -/
theorem nv_checkFarkas_refutes_bvS :
    checkFarkas (atomsLtLe.map BvAtom.toConstraint) [1, 1] = true ∧
    posSupport [1, 1] atomsLtLe = atomsLtLe ∧
    (∀ a ∈ posSupport [1, 1] atomsLtLe, 2 * a.lhs.evalInt (sval (bvPt2 (253#8) (9#8))) < (2 : Int) ^ 8) ∧
    (∀ a ∈ posSupport [1, 1] atomsLtLe,
      -((2 : Int) ^ 8) ≤ 2 * a.rhs.evalInt (sval (bvPt2 (253#8) (9#8)))) := by decide

/-- Non-vacuity of the two-sided corollaries. -/
theorem nv_checkFarkas_refutes_bv_two_sided :
    checkFarkas (atomsLtLe.map BvAtom.toConstraint) [1, 1] = true ∧
    (∀ a ∈ atomsLtLe, InUnsignedRange 8 (a.lhs.evalInt (uval (bvPt2 (5#8) (9#8))))) ∧
    (∀ a ∈ atomsLtLe, InUnsignedRange 8 (a.rhs.evalInt (uval (bvPt2 (5#8) (9#8))))) ∧
    (∀ a ∈ atomsLtLe, InSignedRange 8 (a.lhs.evalInt (sval (bvPt2 (253#8) (9#8))))) ∧
    (∀ a ∈ atomsLtLe, InSignedRange 8 (a.rhs.evalInt (sval (bvPt2 (253#8) (9#8))))) := by decide

/-- `{x₀ - 1 ≤ 0, 2 ≤ x₀}`: refuted by `(1, 1)`. -/
def atomsLhsUnderflowU : List BvAtom :=
  [⟨⟨[(0, 1)], -1⟩, .le, ⟨[], 0⟩⟩, ⟨⟨[], 2⟩, .le, ⟨[(0, 1)], 0⟩⟩]

/-- `{x₀ < x₁, x₁ ≤ x₀, 3x₀ ≤ x₁ - 10}`: the first two atoms are refuted by `(1, 1)`; the third gets
multiplier `0`. -/
def atomsZeroWeight : List BvAtom :=
  atomsLtLe ++ [⟨⟨[(0, 3)], 0⟩, .le, ⟨[(1, 1)], -10⟩⟩]

/-- **The one-sided, positively weighted hypotheses are strictly weaker than two-sided range
facts on every atom.** (1) At `x₀ = 0`, the left-hand value `-1` of `x₀ - 1 ≤ 0` is outside
`[0, 2^8)`, yet the one-sided facts hold. (2) In `atomsZeroWeight`, the zero-weighted third atom
has left-hand value `600 ≥ 2^8` at `x = (200, 200)` and is excluded from the support. -/
theorem ex_one_sided_posSupport_weaker_than_two_sided :
    (checkFarkas (atomsLhsUnderflowU.map BvAtom.toConstraint) [1, 1] = true ∧
      ¬ (∀ a ∈ atomsLhsUnderflowU, InUnsignedRange 8 (a.lhs.evalInt (uval (bvPt2 0#8 0#8)))) ∧
      (∀ a ∈ posSupport [1, 1] atomsLhsUnderflowU,
        a.lhs.evalInt (uval (bvPt2 0#8 0#8)) < (2 : Int) ^ 8) ∧
      (∀ a ∈ posSupport [1, 1] atomsLhsUnderflowU, 0 ≤ a.rhs.evalInt (uval (bvPt2 0#8 0#8)))) ∧
    (checkFarkas (atomsZeroWeight.map BvAtom.toConstraint) [1, 1, 0] = true ∧
      posSupport [1, 1, 0] atomsZeroWeight = atomsLtLe ∧
      ¬ (∀ a ∈ atomsZeroWeight, InUnsignedRange 8 (a.lhs.evalInt (uval (bvPt2 (200#8) (200#8)))))) := by
  decide

/-! ## Small-width exhaustive checks of the transfer statements -/

/-- Exhaustive check at width `3` of unsigned transfer for `e₁ = 2x₀ - x₁ + 1`, `e₂ = x₁`. -/
theorem check_bv_ule_transfer_w3 :
    ∀ a b : Fin 8,
      let x := bvPt2 (BitVec.ofNat 3 a) (BitVec.ofNat 3 b)
      let e₁ : AffExpr := ⟨[(0, 2), (1, -1)], 1⟩
      let e₂ : AffExpr := ⟨[(1, 1)], 0⟩
      InUnsignedRange 3 (e₁.evalInt (uval x)) → InUnsignedRange 3 (e₂.evalInt (uval x)) →
        ((e₁.evalBv 3 x).ule (e₂.evalBv 3 x) = true ↔ e₁.evalInt (uval x) ≤ e₂.evalInt (uval x)) := by
  decide

/-- Exhaustive check at width `3` of signed transfer for the same expressions. -/
theorem check_bv_sle_transfer_w3 :
    ∀ a b : Fin 8,
      let x := bvPt2 (BitVec.ofNat 3 a) (BitVec.ofNat 3 b)
      let e₁ : AffExpr := ⟨[(0, 2), (1, -1)], 1⟩
      let e₂ : AffExpr := ⟨[(1, 1)], 0⟩
      InSignedRange 3 (e₁.evalInt (sval x)) → InSignedRange 3 (e₂.evalInt (sval x)) →
        ((e₁.evalBv 3 x).sle (e₂.evalBv 3 x) = true ↔ e₁.evalInt (sval x) ≤ e₂.evalInt (sval x)) := by
  decide

/-- Check at width `0` on 25 constant pairs `(k₁ - 2, k₂ - 2)`, `k₁ k₂ < 5` (with a `3·x₀` term):
the signed statement holds (only `0` is representable). -/
theorem check_bv_sle_transfer_w0 :
    let x : Nat → BitVec 0 := fun _ => 0#0
    ∀ k₁ k₂ : Fin 5,
      let e₁ : AffExpr := ⟨[(0, 3)], (k₁ : Int) - 2⟩
      let e₂ : AffExpr := ⟨[], (k₂ : Int) - 2⟩
      InSignedRange 0 (e₁.evalInt (sval x)) → InSignedRange 0 (e₂.evalInt (sval x)) →
        ((e₁.evalBv 0 x).sle (e₂.evalBv 0 x) = true ↔ e₁.evalInt (sval x) ≤ e₂.evalInt (sval x)) := by
  decide

/-! ## Counterexamples -/

/-- **The left range hypothesis is necessary (unsigned).** At `w = 8`, `x₀ = 200`: `x₀ + x₀`
evaluates to `400 ∉ [0, 256)` (wraps to `144`), `150` is in range; `144 ≤ᵤ 150` holds but
`400 ≤ 150` fails. -/
theorem ce_bv_ule_lhs_out_of_range :
    ¬ InUnsignedRange 8 (eDouble.evalInt (uval (bvPt2 (200#8) 0#8))) ∧
    InUnsignedRange 8 ((eConst 150).evalInt (uval (bvPt2 (200#8) 0#8))) ∧
    (eDouble.evalBv 8 (bvPt2 (200#8) 0#8)).ule ((eConst 150).evalBv 8 (bvPt2 (200#8) 0#8)) = true ∧
    ¬ (eDouble.evalInt (uval (bvPt2 (200#8) 0#8)) ≤ (eConst 150).evalInt (uval (bvPt2 (200#8) 0#8))) := by
  decide

/-- **The right range hypothesis is necessary (unsigned).** At `w = 8`, `x₀ = 200`: `x₀` is in
range, the constant `300` is not (wraps to `44`); `200 ≤ᵤ 44` fails but `200 ≤ 300` holds. -/
theorem ce_bv_ule_rhs_out_of_range :
    InUnsignedRange 8 (eX0.evalInt (uval (bvPt2 (200#8) 0#8))) ∧
    ¬ InUnsignedRange 8 ((eConst 300).evalInt (uval (bvPt2 (200#8) 0#8))) ∧
    (eX0.evalBv 8 (bvPt2 (200#8) 0#8)).ule ((eConst 300).evalBv 8 (bvPt2 (200#8) 0#8)) = false ∧
    eX0.evalInt (uval (bvPt2 (200#8) 0#8)) ≤ (eConst 300).evalInt (uval (bvPt2 (200#8) 0#8)) := by
  decide

/-- **The left range hypothesis is necessary (signed).** At `w = 8`, `x₀ = 100`: `x₀ + x₀ = 200`
is out of signed range (wraps to `-56`); `-56 ≤ₛ 0` holds but `200 ≤ 0` fails. -/
theorem ce_bv_sle_lhs_out_of_range :
    ¬ InSignedRange 8 (eDouble.evalInt (sval (bvPt2 (100#8) 0#8))) ∧
    InSignedRange 8 ((eConst 0).evalInt (sval (bvPt2 (100#8) 0#8))) ∧
    (eDouble.evalBv 8 (bvPt2 (100#8) 0#8)).sle ((eConst 0).evalBv 8 (bvPt2 (100#8) 0#8)) = true ∧
    ¬ (eDouble.evalInt (sval (bvPt2 (100#8) 0#8)) ≤ (eConst 0).evalInt (sval (bvPt2 (100#8) 0#8))) := by
  decide

/-- **The right range hypothesis is necessary (signed).** At `w = 8`, `x₀ = 100`: the constant
`200` wraps to `-56`; `100 ≤ₛ -56` fails but `100 ≤ 200` holds. -/
theorem ce_bv_sle_rhs_out_of_range :
    InSignedRange 8 (eX0.evalInt (sval (bvPt2 (100#8) 0#8))) ∧
    ¬ InSignedRange 8 ((eConst 200).evalInt (sval (bvPt2 (100#8) 0#8))) ∧
    (eX0.evalBv 8 (bvPt2 (100#8) 0#8)).sle ((eConst 200).evalBv 8 (bvPt2 (100#8) 0#8)) = false ∧
    eX0.evalInt (sval (bvPt2 (100#8) 0#8)) ≤ (eConst 200).evalInt (sval (bvPt2 (100#8) 0#8)) := by
  decide

/-- **The reading must match the comparison.** At `w = 8`, `x₀ = 255#8`: under the signed
reading both sides of `x₀ ≤ 0` are in signed range and `-1 ≤ 0` holds, but the unsigned
comparison `255 ≤ᵤ 0` fails. Conversely, under the unsigned reading both sides are in unsigned
range and `255 ≤ 0` fails, but the signed comparison `-1 ≤ₛ 0` holds. -/
theorem ce_bv_reading_mismatch :
    (InSignedRange 8 (eX0.evalInt (sval (bvPt2 (255#8) 0#8))) ∧
      InSignedRange 8 ((eConst 0).evalInt (sval (bvPt2 (255#8) 0#8))) ∧
      eX0.evalInt (sval (bvPt2 (255#8) 0#8)) ≤ (eConst 0).evalInt (sval (bvPt2 (255#8) 0#8)) ∧
      (eX0.evalBv 8 (bvPt2 (255#8) 0#8)).ule ((eConst 0).evalBv 8 (bvPt2 (255#8) 0#8)) = false) ∧
    -- the converse mismatch: unsigned-reading ranges with the signed comparison
    (InUnsignedRange 8 (eX0.evalInt (uval (bvPt2 (255#8) 0#8))) ∧
      InUnsignedRange 8 ((eConst 0).evalInt (uval (bvPt2 (255#8) 0#8))) ∧
      ¬ (eX0.evalInt (uval (bvPt2 (255#8) 0#8)) ≤ (eConst 0).evalInt (uval (bvPt2 (255#8) 0#8))) ∧
      (eX0.evalBv 8 (bvPt2 (255#8) 0#8)).sle ((eConst 0).evalBv 8 (bvPt2 (255#8) 0#8)) = true) := by
  decide

/-- **Moving terms across a bit-vector comparison is unsound even when both sides are in
range.** At `w = 8`, `(x₀, x₁) = (0, 1)`: `x₀ ≤ᵤ x₁` holds (both sides in range, as does the
integer `0 ≤ 1`), but the rearranged `x₀ - x₁ ≤ᵤ 0` fails (`x₀ - x₁` wraps to `255`) although
the rearranged integer statement `-1 ≤ 0` holds. The same happens for the signed reading at
`(x₀, x₁) = (-100, 100)`: `-100 ≤ₛ 100` holds, but `x₀ - x₁ = -200` wraps to `56` and `56 ≤ₛ 0`
fails. -/
theorem ce_bv_rearrangement_unsound :
    (InUnsignedRange 8 (eX0.evalInt (uval (bvPt2 (0#8) (1#8)))) ∧
      InUnsignedRange 8 (eX1.evalInt (uval (bvPt2 (0#8) (1#8)))) ∧
      (eX0.evalBv 8 (bvPt2 (0#8) (1#8))).ule (eX1.evalBv 8 (bvPt2 (0#8) (1#8))) = true ∧
      (AffExpr.evalBv 8 ⟨[(0, 1), (1, -1)], 0⟩ (bvPt2 (0#8) (1#8))).ule
        ((eConst 0).evalBv 8 (bvPt2 (0#8) (1#8))) = false ∧
      AffExpr.evalInt ⟨[(0, 1), (1, -1)], 0⟩ (uval (bvPt2 (0#8) (1#8))) ≤
        (eConst 0).evalInt (uval (bvPt2 (0#8) (1#8)))) ∧
    -- signed: at `(x₀, x₁) = (-100, 100)`, `x₀ ≤ₛ x₁` holds but `x₀ - x₁` wraps to `56`
    (sval (bvPt2 (156#8) (100#8)) 0 = -100 ∧
      InSignedRange 8 (eX0.evalInt (sval (bvPt2 (156#8) (100#8)))) ∧
      InSignedRange 8 (eX1.evalInt (sval (bvPt2 (156#8) (100#8)))) ∧
      (eX0.evalBv 8 (bvPt2 (156#8) (100#8))).sle (eX1.evalBv 8 (bvPt2 (156#8) (100#8))) = true ∧
      (AffExpr.evalBv 8 ⟨[(0, 1), (1, -1)], 0⟩ (bvPt2 (156#8) (100#8))).sle
        ((eConst 0).evalBv 8 (bvPt2 (156#8) (100#8))) = false ∧
      AffExpr.evalInt ⟨[(0, 1), (1, -1)], 0⟩ (sval (bvPt2 (156#8) (100#8))) ≤
        (eConst 0).evalInt (sval (bvPt2 (156#8) (100#8)))) := by
  decide

/-- `x₀ + x₀ - x₀`, written `x₀ + x₀ + (-1) * x₀`. -/
def eAddAddSub : AffExpr := ⟨[(0, 1), (0, 1), (0, -1)], 0⟩

/-- **Intermediate wrap is harmless for wrapping evaluation when the final value is in range.**
Signed, `w = 8`, `x₀ = 100`: in the left-to-right evaluation of `x₀ + x₀ - x₀` the partial sum `200`
leaves the signed range, while every other intermediate value (coefficient literals, products,
the other partial sums, the constant, the final value `100`) is in range; so `NoWrapS` fails, yet
the wrapping value equals the integer value. Unsigned, `w = 8`, `x₀ = 200`: the partial sum `400`
leaves the unsigned range (as do the literal `-1` and the product `-200`), so `NoWrapU` fails, yet
the wrapping value equals the integer value `200`. By `bv_sle_slt_iff_int_of_inSignedRange` and
`bv_ule_ult_iff_int_of_inUnsignedRange`, comparisons with any in-range right-hand side therefore
transfer. -/
theorem ce_noWrap_not_needed_for_wrapping_eval :
    ((200 : Int) ∈ eAddAddSub.intermediates (sval (bvPt2 (100#8) 0#8)) ∧
      (∀ z ∈ eAddAddSub.intermediates (sval (bvPt2 (100#8) 0#8)), z ≠ 200 → InSignedRange 8 z) ∧
      ¬ NoWrapS 8 eAddAddSub (sval (bvPt2 (100#8) 0#8)) ∧
      InSignedRange 8 (eAddAddSub.evalInt (sval (bvPt2 (100#8) 0#8))) ∧
      (eAddAddSub.evalBv 8 (bvPt2 (100#8) 0#8)).toInt = eAddAddSub.evalInt (sval (bvPt2 (100#8) 0#8))) ∧
    ((400 : Int) ∈ eAddAddSub.intermediates (uval (bvPt2 (200#8) 0#8)) ∧
      ¬ NoWrapU 8 eAddAddSub (uval (bvPt2 (200#8) 0#8)) ∧
      InUnsignedRange 8 (eAddAddSub.evalInt (uval (bvPt2 (200#8) 0#8))) ∧
      ((eAddAddSub.evalBv 8 (bvPt2 (200#8) 0#8)).toNat : Int) =
        eAddAddSub.evalInt (uval (bvPt2 (200#8) 0#8))) := by
  decide

/-- `{3x₀ ≤ 100, 200 ≤ x₀}` as bit-vector atoms. -/
def atomsLhsWrapU : List BvAtom :=
  [⟨⟨[(0, 3)], 0⟩, .le, ⟨[], 100⟩⟩, ⟨⟨[], 200⟩, .le, ⟨[(0, 1)], 0⟩⟩]

/-- **The left-hand bound `lhs < 2^w` is necessary (unsigned).** The certificate `(1, 3)` refutes
the integer translation of `{3x₀ ≤ 100, 200 ≤ x₀}`; both atoms are positively weighted; at
`x₀ = 200#8` every right-hand value is `≥ 0` and both atoms hold in 8-bit unsigned arithmetic
(`3·200` wraps to `88`), while the left-hand value `600` is `≥ 2^8`. -/
theorem ce_checkFarkas_bvU_lhs_out_of_range :
    checkFarkas (atomsLhsWrapU.map BvAtom.toConstraint) [1, 3] = true ∧
    posSupport [1, 3] atomsLhsWrapU = atomsLhsWrapU ∧
    ¬ (∀ a ∈ posSupport [1, 3] atomsLhsWrapU, a.lhs.evalInt (uval (bvPt2 (200#8) 0#8)) < (2 : Int) ^ 8) ∧
    (∀ a ∈ posSupport [1, 3] atomsLhsWrapU, 0 ≤ a.rhs.evalInt (uval (bvPt2 (200#8) 0#8))) ∧
    (∀ a ∈ posSupport [1, 3] atomsLhsWrapU, a.HoldsU 8 (bvPt2 (200#8) 0#8)) := by decide

/-- `{200 ≤ x₀ - 1, x₀ ≤ 0}` as bit-vector atoms. -/
def atomsRhsWrapU : List BvAtom :=
  [⟨⟨[], 200⟩, .le, ⟨[(0, 1)], -1⟩⟩, ⟨⟨[(0, 1)], 0⟩, .le, ⟨[], 0⟩⟩]

/-- **The right-hand bound `0 ≤ rhs` is necessary (unsigned).** The certificate `(1, 1)` refutes
the integer translation of `{200 ≤ x₀ - 1, x₀ ≤ 0}`; at `x₀ = 0#8` every left-hand value is `< 2^8`
and both atoms hold (`x₀ - 1` wraps to `255`), while the right-hand value `-1` is negative. -/
theorem ce_checkFarkas_bvU_rhs_out_of_range :
    checkFarkas (atomsRhsWrapU.map BvAtom.toConstraint) [1, 1] = true ∧
    posSupport [1, 1] atomsRhsWrapU = atomsRhsWrapU ∧
    (∀ a ∈ posSupport [1, 1] atomsRhsWrapU, a.lhs.evalInt (uval (bvPt2 (0#8) 0#8)) < (2 : Int) ^ 8) ∧
    ¬ (∀ a ∈ posSupport [1, 1] atomsRhsWrapU, 0 ≤ a.rhs.evalInt (uval (bvPt2 (0#8) 0#8))) ∧
    (∀ a ∈ posSupport [1, 1] atomsRhsWrapU, a.HoldsU 8 (bvPt2 (0#8) 0#8)) := by decide

/-- `{3x₀ ≤ 100, 90 ≤ x₀}` as bit-vector atoms. -/
def atomsLhsWrapS : List BvAtom :=
  [⟨⟨[(0, 3)], 0⟩, .le, ⟨[], 100⟩⟩, ⟨⟨[], 90⟩, .le, ⟨[(0, 1)], 0⟩⟩]

/-- **The left-hand bound `2·lhs < 2^w` is necessary (signed).** The certificate `(1, 3)` refutes
the integer translation of `{3x₀ ≤ 100, 90 ≤ x₀}`; at `x₀ = 100#8` both atoms hold in 8-bit signed
arithmetic (`3·100` wraps to `44`), every right-hand value satisfies `-2^8 ≤ 2·rhs`, and the
left-hand value `300` has `2·300 ≥ 2^8`. -/
theorem ce_checkFarkas_bvS_lhs_out_of_range :
    checkFarkas (atomsLhsWrapS.map BvAtom.toConstraint) [1, 3] = true ∧
    posSupport [1, 3] atomsLhsWrapS = atomsLhsWrapS ∧
    ¬ (∀ a ∈ posSupport [1, 3] atomsLhsWrapS,
        2 * a.lhs.evalInt (sval (bvPt2 (100#8) 0#8)) < (2 : Int) ^ 8) ∧
    (∀ a ∈ posSupport [1, 3] atomsLhsWrapS,
        -((2 : Int) ^ 8) ≤ 2 * a.rhs.evalInt (sval (bvPt2 (100#8) 0#8))) ∧
    (∀ a ∈ posSupport [1, 3] atomsLhsWrapS, a.HoldsS 8 (bvPt2 (100#8) 0#8)) := by decide

/-- `{100 ≤ x₀ - 200, x₀ ≤ 50}` as bit-vector atoms. -/
def atomsRhsWrapS : List BvAtom :=
  [⟨⟨[], 100⟩, .le, ⟨[(0, 1)], -200⟩⟩, ⟨⟨[(0, 1)], 0⟩, .le, ⟨[], 50⟩⟩]

/-- **The right-hand bound `-2^w ≤ 2·rhs` is necessary (signed).** The certificate `(1, 1)` refutes
the integer translation of `{100 ≤ x₀ - 200, x₀ ≤ 50}`; at `x₀ = 50#8` both atoms hold in 8-bit
signed arithmetic (`50 - 200` wraps to `106`), every left-hand value satisfies `2·lhs < 2^8`, and
the right-hand value `-150` has `2·(-150) < -2^8`. -/
theorem ce_checkFarkas_bvS_rhs_out_of_range :
    checkFarkas (atomsRhsWrapS.map BvAtom.toConstraint) [1, 1] = true ∧
    posSupport [1, 1] atomsRhsWrapS = atomsRhsWrapS ∧
    (∀ a ∈ posSupport [1, 1] atomsRhsWrapS,
        2 * a.lhs.evalInt (sval (bvPt2 (50#8) 0#8)) < (2 : Int) ^ 8) ∧
    ¬ (∀ a ∈ posSupport [1, 1] atomsRhsWrapS,
        -((2 : Int) ^ 8) ≤ 2 * a.rhs.evalInt (sval (bvPt2 (50#8) 0#8))) ∧
    (∀ a ∈ posSupport [1, 1] atomsRhsWrapS, a.HoldsS 8 (bvPt2 (50#8) 0#8)) := by decide

/-- **Range facts on `lhs - rhs` do not suffice (signed).** For the atom `150 ≤ 100` at `w = 8`,
the integer difference `150 - 100 = 50` is in signed range, but the left-hand side `150` is not:
it wraps to `-106`, so `150 ≤ₛ 100` holds while `150 ≤ 100` fails. -/
theorem ce_bvS_range_on_difference_insufficient :
    InSignedRange 8 ((eConst 150).evalInt (sval (bvPt2 0#8 0#8)) -
      (eConst 100).evalInt (sval (bvPt2 0#8 0#8))) ∧
    ¬ InSignedRange 8 ((eConst 150).evalInt (sval (bvPt2 0#8 0#8))) ∧
    ((eConst 150).evalBv 8 (bvPt2 0#8 0#8)).sle ((eConst 100).evalBv 8 (bvPt2 0#8 0#8)) = true ∧
    ¬ ((eConst 150).evalInt (sval (bvPt2 0#8 0#8)) ≤ (eConst 100).evalInt (sval (bvPt2 0#8 0#8))) := by
  decide

/-! ### Tightness of the no-wrap corollaries -/

/-- Dropping the left no-wrap hypothesis (unsigned): `x₀ + x₀` at `x₀ = 200` wraps, the
constant `150` does not; `144 ≤ᵤ 150` holds but `400 ≤ 150` fails. -/
theorem ce_bv_ule_noWrapU_lhs :
    ¬ NoWrapU 8 eDouble (uval (bvPt2 (200#8) 0#8)) ∧ NoWrapU 8 (eConst 150) (uval (bvPt2 (200#8) 0#8)) ∧
    ¬ (((eDouble.evalBv 8 (bvPt2 (200#8) 0#8)).ule ((eConst 150).evalBv 8 (bvPt2 (200#8) 0#8)) = true ↔
        eDouble.evalInt (uval (bvPt2 (200#8) 0#8)) ≤ (eConst 150).evalInt (uval (bvPt2 (200#8) 0#8))) ∧
      ((eDouble.evalBv 8 (bvPt2 (200#8) 0#8)).ult ((eConst 150).evalBv 8 (bvPt2 (200#8) 0#8)) = true ↔
        eDouble.evalInt (uval (bvPt2 (200#8) 0#8)) < (eConst 150).evalInt (uval (bvPt2 (200#8) 0#8)))) := by
  decide

/-- Dropping the right no-wrap hypothesis (unsigned): `x₀ = 200` has no wrap, the constant `300`
does; `200 ≤ᵤ 44` fails but `200 ≤ 300` holds. -/
theorem ce_bv_ule_noWrapU_rhs :
    NoWrapU 8 eX0 (uval (bvPt2 (200#8) 0#8)) ∧ ¬ NoWrapU 8 (eConst 300) (uval (bvPt2 (200#8) 0#8)) ∧
    ¬ (((eX0.evalBv 8 (bvPt2 (200#8) 0#8)).ule ((eConst 300).evalBv 8 (bvPt2 (200#8) 0#8)) = true ↔
        eX0.evalInt (uval (bvPt2 (200#8) 0#8)) ≤ (eConst 300).evalInt (uval (bvPt2 (200#8) 0#8))) ∧
      ((eX0.evalBv 8 (bvPt2 (200#8) 0#8)).ult ((eConst 300).evalBv 8 (bvPt2 (200#8) 0#8)) = true ↔
        eX0.evalInt (uval (bvPt2 (200#8) 0#8)) < (eConst 300).evalInt (uval (bvPt2 (200#8) 0#8)))) := by
  decide

/-- Dropping the left no-wrap hypothesis (signed): `x₀ + x₀` at `x₀ = 100` wraps to `-56`. -/
theorem ce_bv_sle_noWrapS_lhs :
    ¬ NoWrapS 8 eDouble (sval (bvPt2 (100#8) 0#8)) ∧ NoWrapS 8 (eConst 0) (sval (bvPt2 (100#8) 0#8)) ∧
    ¬ (((eDouble.evalBv 8 (bvPt2 (100#8) 0#8)).sle ((eConst 0).evalBv 8 (bvPt2 (100#8) 0#8)) = true ↔
        eDouble.evalInt (sval (bvPt2 (100#8) 0#8)) ≤ (eConst 0).evalInt (sval (bvPt2 (100#8) 0#8))) ∧
      ((eDouble.evalBv 8 (bvPt2 (100#8) 0#8)).slt ((eConst 0).evalBv 8 (bvPt2 (100#8) 0#8)) = true ↔
        eDouble.evalInt (sval (bvPt2 (100#8) 0#8)) < (eConst 0).evalInt (sval (bvPt2 (100#8) 0#8)))) := by
  decide

/-- Dropping the right no-wrap hypothesis (signed): the constant `200` wraps to `-56`. -/
theorem ce_bv_sle_noWrapS_rhs :
    NoWrapS 8 eX0 (sval (bvPt2 (100#8) 0#8)) ∧ ¬ NoWrapS 8 (eConst 200) (sval (bvPt2 (100#8) 0#8)) ∧
    ¬ (((eX0.evalBv 8 (bvPt2 (100#8) 0#8)).sle ((eConst 200).evalBv 8 (bvPt2 (100#8) 0#8)) = true ↔
        eX0.evalInt (sval (bvPt2 (100#8) 0#8)) ≤ (eConst 200).evalInt (sval (bvPt2 (100#8) 0#8))) ∧
      ((eX0.evalBv 8 (bvPt2 (100#8) 0#8)).slt ((eConst 200).evalBv 8 (bvPt2 (100#8) 0#8)) = true ↔
        eX0.evalInt (sval (bvPt2 (100#8) 0#8)) < (eConst 200).evalInt (sval (bvPt2 (100#8) 0#8)))) := by
  decide

/-- `{x₀ ≤ x₁}` as a single bit-vector atom. -/
def atomsLe : List BvAtom := [⟨⟨[(0, 1)], 0⟩, .le, ⟨[(1, 1)], 0⟩⟩]

/-- The acceptance hypothesis of the bit-vector refutation theorems cannot be dropped: a
rejected certificate for `{x₀ ≤ x₁}`, which holds (unsigned and signed) at `x = (0, 0)`, where
every one-sided and two-sided range fact holds for the positively weighted atom. -/
theorem ce_checkFarkas_refutes_bv_rejected :
    checkFarkas (atomsLe.map BvAtom.toConstraint) [1] = false ∧
    posSupport [1] atomsLe = atomsLe ∧
    (∀ a ∈ atomsLe, InUnsignedRange 8 (a.lhs.evalInt (uval (bvPt2 0#8 0#8)))) ∧
    (∀ a ∈ atomsLe, InUnsignedRange 8 (a.rhs.evalInt (uval (bvPt2 0#8 0#8)))) ∧
    (∀ a ∈ atomsLe, InSignedRange 8 (a.lhs.evalInt (sval (bvPt2 0#8 0#8)))) ∧
    (∀ a ∈ atomsLe, InSignedRange 8 (a.rhs.evalInt (sval (bvPt2 0#8 0#8)))) ∧
    (∀ a ∈ atomsLe, a.HoldsU 8 (bvPt2 0#8 0#8)) ∧ (∀ a ∈ atomsLe, a.HoldsS 8 (bvPt2 0#8 0#8)) := by
  decide

/-- Bounded check (width `3`, two terms on `x₀`, every coefficient literal and constant in `[0, 8)`,
every point): in the unsigned reading, an in-range final value then implies `NoWrapU`. So unsigned
intermediate wrap with an in-range final value needs a negative or out-of-range literal. -/
theorem check_noWrapU_of_final_in_range_w3 :
    ∀ c1 c2 k : Fin 8, ∀ v : Fin 8,
      let e : AffExpr := ⟨[(0, (c1 : Int)), (0, (c2 : Int))], (k : Int)⟩
      InUnsignedRange 3 (e.evalInt (uval (bvPt2 (BitVec.ofNat 3 v) 0#3))) →
        NoWrapU 3 e (uval (bvPt2 (BitVec.ofNat 3 v) 0#3)) := by decide

/-! ### Limits of the bit-vector refutation theorems -/

/-- `{x₀ <ᵤ 0}`. -/
def atomsLtZero : List BvAtom := [⟨⟨[(0, 1)], 0⟩, .lt, ⟨[], 0⟩⟩]

/-- **The translation does not add variable domain bounds.** `x₀ <ᵤ 0` fails at every 8-bit
value of `x₀`, but its integer translation `x₀ < 0` holds at the integer point `x₀ = -1`, so
`checkFarkas` rejects every certificate (by soundness). Domain bounds such as `0 ≤ x₀` must be
added to `A` explicitly. -/
theorem ce_bv_domain_bounds_not_emitted :
    (∀ v : BitVec 8, ¬ ∀ a ∈ atomsLtZero, a.HoldsU 8 (bvPt2 v 0#8)) ∧
    SatInt (atomsLtZero.map BvAtom.toConstraint) (pt1 (-1)) ∧
    (∀ cert : List Int, checkFarkas (atomsLtZero.map BvAtom.toConstraint) cert = false) := by
  refine ⟨by decide, by decide, fun cert => ?_⟩
  cases hc : checkFarkas (atomsLtZero.map BvAtom.toConstraint) cert with
  | false => rfl
  | true => exact absurd (by decide) (checkFarkas_sound_int _ cert hc (pt1 (-1)))

/-- `{2x₀ ≤ᵤ 1, 1 ≤ᵤ 2x₀}`. -/
def atomsHalfU : List BvAtom := [⟨⟨[(0, 2)], 0⟩, .le, ⟨[], 1⟩⟩, ⟨⟨[], 1⟩, .le, ⟨[(0, 2)], 0⟩⟩]

/-- **Plain Farkas refutation is incomplete over `BitVec w`.** `{2x₀ ≤ᵤ 1, 1 ≤ᵤ 2x₀}` fails at every
8-bit value of `x₀` (`2x₀` is even), but `checkFarkas` rejects every certificate for its integer
translation, which the rational point `x₀ = 1/2` satisfies. -/
theorem ce_checkFarkas_bv_incomplete :
    (∀ v : BitVec 8, ¬ ∀ a ∈ atomsHalfU, a.HoldsU 8 (bvPt2 v 0#8)) ∧
    (0 : Int) < 2 ∧ SatScaled (atomsHalfU.map BvAtom.toConstraint) 2 (pt1 1) ∧
    (∀ cert : List Int, checkFarkas (atomsHalfU.map BvAtom.toConstraint) cert = false) := by
  refine ⟨by decide, by decide, by decide, fun cert => ?_⟩
  cases hc : checkFarkas (atomsHalfU.map BvAtom.toConstraint) cert with
  | false => rfl
  | true => exact absurd (by decide) (checkFarkas_sound_scaled _ cert hc 2 (by decide) (pt1 1))

/-- **Tightening a strict bit-vector comparison is unsound at the bottom of the range.** `x₀ <ᵤ 0`
fails at every 8-bit value, while its "tightened" form `x₀ ≤ᵤ 0 - 1` (the right-hand side wraps
to `255`) holds at every 8-bit value. -/
theorem ce_bv_tightening_unsound :
    (∀ v : BitVec 8, ¬ (⟨⟨[(0, 1)], 0⟩, .lt, ⟨[], 0⟩⟩ : BvAtom).HoldsU 8 (bvPt2 v 0#8)) ∧
    (∀ v : BitVec 8, (⟨⟨[(0, 1)], 0⟩, .le, ⟨[], -1⟩⟩ : BvAtom).HoldsU 8 (bvPt2 v 0#8)) := by
  decide

/-- **Over `BitVec w`, a non-zero integer form can vanish identically.** `256 · x₀` is not the
zero form (`isZero` rejects it), yet its 8-bit wrapping value is `0` at every 8-bit point. -/
theorem ex_isZero_not_bitvector_vanishing :
    SparseVec.isZero [(0, 256)] = false ∧
    (∀ v : BitVec 8, SparseVec.evalBv 8 [(0, 256)] (bvPt2 v 0#8) = 0#8) := by
  decide

end Toy.Farkas
