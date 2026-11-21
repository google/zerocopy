import Toy.Progress.Mixing

/-!
# Equivalent forms of forward-progress refinement

`Refines FPBeh src tgt` says that from every initial state every forward-progress behaviour
of `tgt` is one of `src`. Because the language is deterministic and every run has exactly one
divergence-observable behaviour (`obsBeh_exists`, `obsBeh_unique`), this is equivalent to:
from every initial state `s`, either `src` silently diverges from `s` (undefined behaviour
under `FPBeh`) or `tgt` and `src` have the same divergence-observable behaviours from `s`.

This module adds that equivalence and its instance for classic slices. It introduces no new
definitions.
-/

namespace Toy.Progress

/-- `Refines FPBeh src tgt` holds iff from every initial state `s`, either `src` silently
diverges from `s` or `tgt` and `src` have exactly the same divergence-observable behaviours
from `s`. -/
theorem refines_fpBeh_iff_silentlyDiverges_or_obsBeh_iff (src tgt : Cmd) :
    Refines FPBeh src tgt ↔
      ∀ s, SilentlyDiverges src s ∨ ∀ b, ObsBeh tgt s b ↔ ObsBeh src s b := by
  constructor
  · intro href s
    by_cases hsd : SilentlyDiverges src s
    · exact Or.inl hsd
    · right
      have hntgt : ¬ SilentlyDiverges tgt s := by
        intro hsdtgt
        obtain ⟨b₀, hb₀⟩ := obsBeh_exists src s
        have hex : ∃ b₁ : Beh, b₁ ≠ b₀ := by
          cases b₀ with
          | term t =>
            refine ⟨.term (0 :: t), fun he => ?_⟩
            have := congrArg List.length (Beh.term.inj he)
            simp at this
          | div _ => exact ⟨.term [], fun he => by cases he⟩
          | react _ => exact ⟨.term [], fun he => by cases he⟩
        obtain ⟨b₁, hne⟩ := hex
        rcases href s b₁ (Or.inl hsdtgt) with h | h
        · exact hsd h
        · exact hne (obsBeh_unique h hb₀)
      obtain ⟨b₀, hb₀⟩ := obsBeh_exists tgt s
      have hsrc₀ : ObsBeh src s b₀ := (href s b₀ (Or.inr hb₀)).resolve_left hsd
      intro b
      exact ⟨fun hb => (href s b (Or.inr hb)).resolve_left hsd,
        fun hb => (obsBeh_unique hsrc₀ hb) ▸ hb₀⟩
  · intro h s b hb
    rcases h s with hsd | heq
    · exact Or.inl hsd
    · rcases hb with ⟨t, ht⟩ | hob
      · exact Or.inl ⟨t, (heq _).1 ht⟩
      · exact Or.inr ((heq b).1 hob)

/-- For every classic slice `c'` of `c`, from every initial state `s`, either `c` silently
diverges from `s` or `c'` has exactly the divergence-observable behaviours of `c` from `s`.
This is `classicSlice_refines_forwardProgress` restated through
`refines_fpBeh_iff_silentlyDiverges_or_obsBeh_iff`. -/
theorem classicSlice_silentlyDiverges_or_obsBeh_iff (c c' : Cmd)
    (hSlice : IsClassicSlice c c') :
    ∀ s, SilentlyDiverges c s ∨ ∀ b, ObsBeh c' s b ↔ ObsBeh c s b :=
  (refines_fpBeh_iff_silentlyDiverges_or_obsBeh_iff c c').1
    (classicSlice_refines_forwardProgress c c' hSlice)

end Toy.Progress
