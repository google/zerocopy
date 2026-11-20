import ToyPerm.Frac
import ToyPerm.Count
import ToyPerm.Depth

/-!
# Cross-design comparisons

* The disjointness axiom of Dockins, Hobor and Appel (`a · a = b → a = b`; in a
  cancellative algebra: only the unit composes with itself) fails for fractional
  permissions, for counting permissions, and for the depth-sum algebra on cells
  over any inhabited payload type, because each lets two equal non-empty read
  permissions coexist. Over the empty payload type the depth-sum algebra has
  only the unit and satisfies disjointness.
* Reading sharing-depth cells as counting sources illustrates the token-return
  impossibility of the depth design: a counting source can take its last token
  back by composition, and this is consistent precisely because no second
  source can coexist with it.
-/

namespace Toy.Perm

open FracPerm Count PartialAlg Cell

/-- **None of the three permission algebras satisfies disjointness.** The
fractional algebra and the counting algebra violate disjointness, and so does
the depth-sum algebra on cells for every inhabited payload type `V`. -/
theorem fracAlg_countAlg_cellSumAlg_violate_disjointness :
    ¬ fracAlg.Disjointness ∧ ¬ countAlg.Disjointness ∧
      ∀ (V : Type) [DecidableEq V], Nonempty V → ¬ (cellSumAlg V).Disjointness := by
  refine ⟨fun h => ?_, fun h => ?_, fun V _ ⟨v⟩ h => ?_⟩
  · have := h _ _ (fracAlg_half_half)
    have := congrArg FracPerm.val this
    simp at this; grind
  · have := h _ _ countAlg_two_tokens_split
    simp [readToken, tokens] at this
  · have := h (.shared 1 v) (.shared 2 v) (by simp [cellSumAlg, cellSumOp])
    simp at this

/-- The witnesses behind `fracAlg_countAlg_cellSumAlg_violate_disjointness`:
`1/2 · 1/2 = 1` with `1/2 ≠ 1`; `readToken · readToken = tokens 2` with
`readToken ≠ tokens 2`; and, for every payload `v`,
`shared 1 v · shared 1 v = shared 2 v` with `shared 1 v ≠ shared 2 v`. -/
theorem disjointness_violation_witnesses :
    fracAlg.op (half full) (half full) = some full ∧ half full ≠ full ∧
      countAlg.op readToken readToken = some (tokens 2) ∧ readToken ≠ tokens 2 ∧
      ∀ (V : Type) [DecidableEq V] (v : V),
        (cellSumAlg V).op (.shared 1 v) (.shared 1 v) = some (.shared 2 v) ∧
          (Cell.shared 1 v : Cell V) ≠ .shared 2 v := by
  refine ⟨fracAlg_half_half, ?_, by decide, by decide, fun V _ v => ⟨by simp [cellSumAlg, cellSumOp], ?_⟩⟩
  · intro h; have := congrArg FracPerm.val h; simp at this; grind
  · intro h; cases h

/-- Non-vacuity of the third conjunct of
`fracAlg_countAlg_cellSumAlg_violate_disjointness` at a concrete inhabited payload
type: `Nat` is inhabited, `shared 1 7 · shared 1 7 = shared 2 7` with
`shared 1 7 ≠ shared 2 7`, and the depth-sum algebra over `Nat` violates
disjointness. -/
theorem disjointness_violation_witness_nat :
    Nonempty Nat ∧
      (cellSumAlg Nat).op (.shared 1 7) (.shared 1 7) = some (.shared 2 7) ∧
      (Cell.shared 1 7 : Cell Nat) ≠ .shared 2 7 ∧ ¬ (cellSumAlg Nat).Disjointness :=
  ⟨⟨7⟩, (disjointness_violation_witnesses.2.2.2.2 Nat 7).1,
    (disjointness_violation_witnesses.2.2.2.2 Nat 7).2,
    fracAlg_countAlg_cellSumAlg_violate_disjointness.2.2 Nat ⟨7⟩⟩

/-- Tightness of `Nonempty V` in the third conjunct of
`fracAlg_countAlg_cellSumAlg_violate_disjointness` (canonical form): over the
empty payload type, `borrowed` is the only cell, and the depth-sum algebra
satisfies disjointness. -/
theorem cellSumAlg_empty_disjointness : ¬ Nonempty Empty ∧ (cellSumAlg Empty).Disjointness := by
  refine ⟨fun ⟨x⟩ => (nomatch x), fun a b h => ?_⟩
  cases a with
  | borrowed => cases h; rfl
  | shared _ v => exact nomatch v

/-- Interpretation of cells as counting permissions (payloads ignored):
`shared d _ ↦ source d`, `borrowed ↦ none`. -/
def cellToCount {V : Type} : Cell V → Count
  | .shared d _ => source d
  | .borrowed => none

/-- Illustration for
`no_assoc_alg_returns_last_share_by_composition_beside_another_reader`: in the
counting algebra, with cells read as sources (`cellToCount`) and the token read
as a single read token, absorbing the token turns a source with count `1` into
the total permission, and a source with count `1` cannot be composed with the
total permission; consistently, two sources with count `1` cannot coexist, so
the state of hypothesis (i) is not consistent here. -/
theorem counting_returns_last_share_without_coexisting_reader :
    countAlg.op (cellToCount (Cell.shared 1 (7 : Nat))) readToken =
        some (cellToCount (Cell.shared 0 (7 : Nat))) ∧
      ¬ countAlg.Compat (cellToCount (Cell.shared 1 (7 : Nat))) (cellToCount (Cell.shared 0 (7 : Nat))) ∧
      ((countAlg.op (cellToCount (Cell.shared 1 (7 : Nat))) (cellToCount (Cell.shared 1 (7 : Nat)))).bind
        fun x => countAlg.op x readToken) = none := by
  decide

end Toy.Perm
