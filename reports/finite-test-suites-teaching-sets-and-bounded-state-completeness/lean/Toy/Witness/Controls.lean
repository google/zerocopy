/-
Cross-module positive controls connecting the patch-closed impossibility results
to the restricted positive classes (monotone conjunctions and bounded-state
Moore machines).
-/
import Toy.Witness.Core
import Toy.Witness.Unrestricted
import Toy.Witness.Conjunctions
import Toy.Witness.Moore

namespace Toy.Witness

/-- Positive control for `patchClosed_untested_input_patch_witness` and
`patchClosed_hasUntestedInput_no_teaching` drawn from monotone conjunctions
(`m = 2`): keeping `HasTwoDistinct Bool`, membership in the class, consistency
with `h`, an untested input `x₀ = (false, false) ∉ S.map Prod.fst`, and a
distinct output `true ≠ h x₀`, restricting `H` to `MonotoneConjunctions 2`
breaks single-point patch closure and allows the 2-example suite
`monotoneConjTeachingSet (fun _ => true)` to teach `x₀ ∧ x₁` on the 4-element
domain `BoolAssignment 2`. -/
theorem patchClosed_untested_input_positive_control_monotone_conj :
    let V : Fin 2 → Bool := fun _ => true
    let h : BoolAssignment 2 → Bool := evalMonotoneConj V
    let S : List (BoolAssignment 2 × Bool) := monotoneConjTeachingSet V
    let x₀ : BoolAssignment 2 := fun _ => false
    ¬ ClosedUnderPointPatches (MonotoneConjunctions 2) ∧
    ¬ IsUnrestricted (MonotoneConjunctions 2) ∧
    MonotoneConjunctions 2 h ∧
    Consistent S h ∧
    x₀ ∉ S.map Prod.fst ∧
    (true : Bool) ≠ h x₀ ∧
    Teaches (MonotoneConjunctions 2) h S := by
  let V : Fin 2 → Bool := fun _ => true
  let h : BoolAssignment 2 → Bool := evalMonotoneConj V
  let S : List (BoolAssignment 2 × Bool) := monotoneConjTeachingSet V
  let x₀ : BoolAssignment 2 := fun _ => false
  have hT : Teaches (MonotoneConjunctions 2) h S := monotone_conj_m2_all_teaches.1
  have hnotPatch : ¬ ClosedUnderPointPatches (MonotoneConjunctions 2) := by
    intro hClosed
    have hPatch := hClosed h (fun _ => true) false hT.1
    rcases hPatch with ⟨W, hW⟩
    have hval := congrFun hW (fun _ => true)
    rw [evalMonotoneConj_all_true, patchAt_self] at hval
    cases hval
  have hnotUnres : ¬ IsUnrestricted (MonotoneConjunctions 2) :=
    fun hU => hnotPatch (isUnrestricted_implies_closedUnderPointPatches hU)
  have hnotMem : x₀ ∉ S.map Prod.fst := by
    intro hmem
    simp only [S, V, monotoneConjTeachingSet_m2_all, List.map_cons, List.map_nil,
      List.mem_cons, List.not_mem_nil, or_false] at hmem
    rcases hmem with heq | heq
    · have h1 := congrFun heq 1; cases h1
    · have h0 := congrFun heq 0; cases h0
  exact ⟨hnotPatch, hnotUnres, hT.1, hT.2.1, hnotMem, by decide, hT⟩

end Toy.Witness
