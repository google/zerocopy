import Toy.RA.Core

/-!
# Exclusive Resource Algebra (`Excl`)

Models unique, non-shareable ownership of a payload `x : α` (Iris's discrete
`exclR`). Any valid exclusive element rejects every non-empty frame and
therefore admits frame-preserving updates to any other valid exclusive element.
-/

namespace Toy.RA

/-- Elements of the exclusive resource algebra over payload type `α`: either
unique ownership `excl x` of a value `x`, or the invalid element `invalid`
produced by any attempt to compose two exclusive elements. Captures Iris's
`excl A` (`Excl a` and `ExclInvalid`). -/
inductive Excl (α : Type) where
  | excl (x : α)
  | invalid
  deriving DecidableEq, Repr

/-- The discrete exclusive resource algebra over `α`. Composition always yields
`invalid`; validity accepts exactly the `excl x` elements. -/
def exclRA (α : Type) : RawRA (Excl α) where
  op _ _ := .invalid
  valid
    | .excl _ => True
    | .invalid => False

theorem exclRA_opAssoc (α : Type) : OpAssoc (exclRA α) :=
  fun _ _ _ => rfl

theorem exclRA_opComm (α : Type) : OpComm (exclRA α) :=
  fun _ _ => rfl

theorem exclRA_validOpL (α : Type) : ValidOpL (exclRA α) :=
  fun _ _ h => False.elim h

theorem exclRA_isCoreFreeRA (α : Type) : IsCoreFreeRA (exclRA α) :=
  ⟨exclRA_opAssoc α, exclRA_opComm α, exclRA_validOpL α⟩

/-! ## Positive and Negative Examples for `exclRA` -/

theorem exclRA_valid_pos_example : (exclRA Nat).valid (.excl 0) := trivial

theorem exclRA_valid_neg_example : ¬ (exclRA Nat).valid .invalid :=
  fun h => h

theorem exclRA_op_neg_example :
    ¬ (exclRA Nat).valid ((exclRA Nat).op (.excl 0) (.excl 1)) :=
  fun h => h

/-! ## Main Results for Exclusive Ownership -/

/-- Nothing composes validly with an exclusive element `Excl.excl x` on the
right (and by commutativity, on the left). Captures Iris's `excl_exclusive`. -/
theorem excl_no_valid_frame {α : Type} (x : α) (f : Excl α) :
    ¬ (exclRA α).valid ((exclRA α).op (.excl x) f) :=
  fun h => h

theorem excl_isExclusive {α : Type} (x : α) : IsExclusive (exclRA α) (.excl x) :=
  excl_no_valid_frame x

theorem excl_no_valid_frame_nonvacuity :
    IsCoreFreeRA (exclRA Nat) ∧ (exclRA Nat).valid (.excl 0) ∧ (exclRA Nat).valid (.excl 1) :=
  ⟨exclRA_isCoreFreeRA Nat, trivial, trivial⟩

/-- Positive control for `excl_no_valid_frame`: in a shareable core-free RA
(`cappedNatRA`), two valid elements `0` and `1` compose validly (`0 + 1 ≤ 2`). -/
theorem excl_no_valid_frame_positive_control :
    IsCoreFreeRA cappedNatRA ∧ cappedNatRA.valid 0 ∧ cappedNatRA.valid 1 ∧
    cappedNatRA.valid (cappedNatRA.op 0 1) :=
  ⟨isCoreFreeRA_pos_example, by show 0 ≤ 2; omega, by show 1 ≤ 2; omega, by show 0 + 1 ≤ 2; omega⟩

/-- Characterization of frame-preserving updates out of `Excl.excl x`: an
exclusive element can update to `e` if and only if `e` is itself a valid
exclusive element `Excl.excl y`. In particular, `excl x ⤳ excl y` holds for all
`x` and `y`, while `excl x ⤳ invalid` fails. -/
theorem excl_fpUpdate_iff {α : Type} (x : α) (e : Excl α) :
    fpUpdate (exclRA α) (.excl x) e ↔ ∃ y : α, e = .excl y := by
  constructor
  · intro h
    have hv : (exclRA α).valid e := h none trivial
    cases e with
    | excl y => exact ⟨y, rfl⟩
    | invalid => exact False.elim hv
  · rintro ⟨y, rfl⟩
    exact exclusive_fpUpdate (exclRA α) (.excl x) (.excl y) (excl_isExclusive x) trivial

/-- Corollary: `excl x ⤳ excl y` for all `x y : α`. -/
theorem excl_fpUpdate {α : Type} (x y : α) :
    fpUpdate (exclRA α) (.excl x) (.excl y) :=
  (excl_fpUpdate_iff x (.excl y)).mpr ⟨y, rfl⟩

/-- Corollary: an exclusive element cannot frame-preservingly update to
`invalid` (witnessed by the empty frame `none`). -/
theorem excl_invalid_target_fails {α : Type} (x : α) :
    ¬ fpUpdate (exclRA α) (.excl x) .invalid := by
  intro h
  exact h none trivial

theorem excl_fpUpdate_iff_nonvacuity :
    IsCoreFreeRA (exclRA Bool) ∧ (exclRA Bool).valid (.excl false) ∧
    (exclRA Bool).valid (.excl true) :=
  ⟨exclRA_isCoreFreeRA Bool, trivial, trivial⟩

/-! ## Non-Vacuity and Target-Validity Tightness for `exclusive_fpUpdate` -/

theorem exclusive_fpUpdate_nonvacuity :
    IsCoreFreeRA (exclRA Bool) ∧ IsExclusive (exclRA Bool) (.excl false) ∧
    (exclRA Bool).valid (.excl true) :=
  ⟨exclRA_isCoreFreeRA Bool, excl_isExclusive false, trivial⟩

/-- Canonical counterexample showing `hb : R.valid b` is necessary in
`exclusive_fpUpdate`: in `exclRA Bool`, `IsExclusive` holds for `.excl false`
(and `IsCoreFreeRA` holds), `.invalid` fails validity, and `.excl false ⤳ .invalid`
fails at the empty frame `none`. -/
theorem exclusive_fpUpdate_invalid_target_counterexample :
    IsCoreFreeRA (exclRA Bool) ∧
    IsExclusive (exclRA Bool) (.excl false) ∧
    ¬ (exclRA Bool).valid .invalid ∧
    ¬ fpUpdate (exclRA Bool) (.excl false) .invalid :=
  ⟨exclRA_isCoreFreeRA Bool, excl_isExclusive false, fun h => h, excl_invalid_target_fails false⟩

end Toy.RA
