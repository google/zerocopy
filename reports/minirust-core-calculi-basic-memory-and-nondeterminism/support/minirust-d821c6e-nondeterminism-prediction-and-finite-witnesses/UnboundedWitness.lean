import Std

/-
Proposed bounded checker run only; NOT executed in this investigation.
One prediction p is selected once. UB occurs after p safe ticks.
safeFor k p means this selected prediction survives the first k ticks.
The arithmetic abstraction isolates the quantifier error; it is not MiniRust.
-/
namespace UnboundedWitness

def safeFor (k p : Nat) : Prop := k ≤ p

theorem every_finite_bound_has_witness :
    ∀ k, ∃ p, safeFor k p := by
  intro k
  exact ⟨k, Nat.le_refl k⟩

theorem no_one_witness_covers_all_prefixes :
    ¬ ∃ p, ∀ k, safeFor k p := by
  intro h
  obtain ⟨p, hp⟩ := h
  exact Nat.not_succ_le_self p (hp (p + 1))

theorem finite_witnesses_do_not_imply_coherent_witness :
    (∀ k, ∃ p, safeFor k p) ∧ ¬ (∃ p, ∀ k, safeFor k p) :=
  ⟨every_finite_bound_has_witness, no_one_witness_covers_all_prefixes⟩

#print axioms every_finite_bound_has_witness
#print axioms no_one_witness_covers_all_prefixes
#print axioms finite_witnesses_do_not_imply_coherent_witness

end UnboundedWitness
