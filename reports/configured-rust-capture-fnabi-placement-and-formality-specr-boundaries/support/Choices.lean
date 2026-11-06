import Std

namespace Choices

def demonic (xs : List α) (ok : α → Prop) : Prop := ∀ x, x ∈ xs → ok x
def angelic (xs : List α) (ok : α → Prop) : Prop := ∃ x, x ∈ xs ∧ ok x

theorem empty_demonic (ok : α → Prop) : demonic [] ok := by simp [demonic]
theorem empty_angelic (ok : α → Prop) : ¬ angelic [] ok := by simp [angelic]

theorem existential_is_not_universal :
    angelic [false, true] (fun b => b = true) ∧
      ¬ demonic [false, true] (fun b => b = true) := by
  simp [angelic, demonic]

theorem uniform_choice_is_stronger :
    (∀ a : Bool, ∃ p : Bool, p = a) ∧
      ¬ (∃ p : Bool, ∀ a : Bool, p = a) := by
  constructor
  · intro a; exact ⟨a, rfl⟩
  · rintro ⟨p, h⟩
    have h1 := h false
    have h2 := h true
    cases p <;> simp_all

-- Soundness of a certificate that enumerates every allowed demonic choice.
theorem complete_demonic_certificate (allowed cert : List α) (ok : α → Prop)
    (complete : ∀ a, a ∈ allowed → a ∈ cert)
    (checked : demonic cert ok) : demonic allowed ok := by
  intro a ha
  exact checked a (complete a ha)

-- An angelic witness certificate needs membership and a continuation proof.
theorem angelic_certificate (allowed : List α) (ok : α → Prop)
    (witness : α) (member : witness ∈ allowed) (continuation : ok witness) :
    angelic allowed ok := ⟨witness, member, continuation⟩

#print axioms empty_demonic
#print axioms empty_angelic
#print axioms existential_is_not_universal
#print axioms uniform_choice_is_stronger
#print axioms complete_demonic_certificate
#print axioms angelic_certificate

end Choices

