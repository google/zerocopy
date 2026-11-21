/-
Toy.MagicDiv.Companions
=======================

Proof-only companion lemmas. Nothing else in the library depends on them; they
make two readings used in the report checkable in Lean.

* `directRemB_iff`: the Boolean checker `directRemB` (used by
  `count_single_word_u8_directRem_fails`) decides
  `∀ x < 2^N, directRem F d m x = x % d`.
* `ce_minimal_shift_u8_div7_input_range`: the pair `(293, 11)` of
  `minimal_shift_u8_div7` computes `x / 7` for every `x < 685` and fails at
  `x = 685`, so the input bound `x < 2^8` inside `MulShiftCorrect 8 7 293 11`
  cannot be dropped.
-/
import Toy.MagicDiv.Bounded

namespace Toy.MagicDiv

/-- Adequacy of the Boolean checker `directRemB`. -/
theorem directRemB_iff (N F d m : Nat) :
    directRemB N F d m = true ↔ ∀ x, x < 2 ^ N → directRem F d m x = x % d := by
  unfold directRemB
  rw [allBelow_iff]
  simp only [beq_iff_eq]

/-- The pair `(293, 11)` computes `x / 7` for every `x < 685` and fails at
`x = 685 > 2^8`. -/
theorem ce_minimal_shift_u8_div7_input_range :
    (∀ x, x < 685 → (x * 293) >>> 11 = x / 7) ∧ (685 * 293) >>> 11 ≠ 685 / 7 := by
  refine ⟨?_, by decide⟩
  have h : allBelow 685 (fun x => (x * 293) >>> 11 == x / 7) = true := by decide +kernel
  rw [allBelow_iff] at h
  intro x hx
  simpa using h x hx

end Toy.MagicDiv
