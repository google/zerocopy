import ToyWMM.Lemmas
import ToyWMM.Litmus

/-!
# Model inclusions: SC ⊆ TSO (strictly) and the rejected `ppo` variant ⊆ TSO
-/

namespace Toy.WMM

open Litmus

/-- **Model inclusion.** Every SC-consistent candidate execution is TSO-consistent. No
well-formedness hypothesis is needed: each TSO edge is an SC path. -/
theorem tsoConsistent_of_scConsistent {n : Nat} (X : Exec n) (h : X.SCConsistent) :
    X.TSOConsistent := by
  refine ⟨?_, ?_⟩
  · refine Rel.Acyclic.mono ?_ h
    intro a b hab
    simp only [Exec.uniprocRel, Exec.poLoc, Bool.or_eq_true, Bool.and_eq_true] at hab
    simp only [Exec.scRel, Bool.or_eq_true]
    rcases hab with ((h | h) | h) | h
    · exact Or.inl (Or.inl (Or.inl h.1.1.1))
    · exact Or.inl (Or.inl (Or.inr h))
    · exact Or.inl (Or.inr h)
    · exact Or.inr h
  · exact Rel.Acyclic.of_sub_path (fun a b hab => X.path_scRel_of_tsoRel hab) h

/-- The converse of `tsoConsistent_of_scConsistent` fails, even for well-formed executions
of a program: the SB weak-outcome execution (`Litmus.sb_weak_tso_allowed_sc_forbidden`). -/
theorem not_forall_wf_tsoConsistent_scConsistent :
    ¬ ∀ (X : Exec 6), X.Wf → X.TSOConsistent → X.SCConsistent :=
  fun h => sb_weak_tso_allowed_sc_forbidden.2.2.2
    (h _ sb_weak_tso_allowed_sc_forbidden.2.1 sb_weak_tso_allowed_sc_forbidden.2.2.1)

/-- **Inclusion of the rejected variant.** Keeping same-location write→read pairs in `ppo`
gives a model at least as strong as `TSOConsistent`: every execution consistent under the
variant is `TSOConsistent` (no well-formedness needed, since `ppo ⊆ ppoKeepSameLocWR`). -/
theorem tsoConsistent_of_tsoConsistentKeepSameLocWR {n : Nat} (X : Exec n)
    (h : X.TSOConsistentKeepSameLocWR) : X.TSOConsistent := by
  refine ⟨h.1, Rel.Acyclic.mono ?_ h.2⟩
  intro a b hab
  simp only [Exec.tsoRel, Bool.or_eq_true] at hab
  simp only [Bool.or_eq_true]
  rcases hab with (((h | h) | h) | h) | h
  · refine Or.inl (Or.inl (Or.inl (Or.inl ?_)))
    simp only [Exec.ppo, Bool.and_eq_true, Bool.not_eq_true'] at h
    simp only [Exec.ppoKeepSameLocWR, Bool.and_eq_true, Bool.not_eq_true', h.1, true_and]
    simp only [Bool.and_eq_false_iff] at h ⊢
    rcases h.2 with h' | h'
    · exact Or.inl (Or.inl h')
    · exact Or.inl (Or.inr h')
  · exact Or.inl (Or.inl (Or.inl (Or.inr h)))
  · exact Or.inl (Or.inl (Or.inr h))
  · exact Or.inl (Or.inr h)
  · exact Or.inr h

end Toy.WMM
