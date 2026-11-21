import ToyVariance.Corollaries

/-!
# Corollaries for the schematic body rule

Two facts about the schematic body rule at or beyond the inferred variance: a non-vacuity
witness for `bodyAx_inferVar_iff` (the rule at the inferred variance itself), and a tightness
witness for the hypothesis `hv` of `bodyRule_le_inferVar_sound` that states the failure of its
conclusion `Sound` directly.
-/

namespace Toy.Variance

/-- Non-vacuity of `bodyAx_inferVar_iff`: for `F = (T, ())` the inferred variance is `co`, the
rule at the inferred variance contains the proper pair `(&'static nat, ()) ≤ (&'sh nat, ())`,
and a program using it is typed. -/
theorem bodyAx_inferVar_iff_nonvacuous :
    inferVar rustTable (.prod .param .unit) = .co ∧
      BodyAx (.prod .param .unit) (inferVar rustTable (.prod .param .unit))
        (.prod rs .unit) (.prod rsh .unit) ∧ rs ≠ rsh ∧
      Typed (SubGen rustTable (BodyAx (.prod .param .unit) (inferVar rustTable (.prod .param .unit))))
        progBodyCov :=
  ⟨rfl, bodyAx_example, by decide, bodyAx_le_inferVar_iff_nonvacuous.2.2.2⟩

/-- Counterexample for the hypothesis `hv` of `bodyRule_le_inferVar_sound`, in canonical form:
for the data body `F = param` (inferred `co`), the declared variance `contra` is not at most as
permissive as the inferred one, and the body rule is not sound. -/
theorem bodyAx_param_contra_unsound :
    Variance.contra.le (inferVar rustTable .param) = false ∧
      ¬ Sound (SubGen rustTable (BodyAx .param .contra)) :=
  ⟨rfl, bodyRule_not_le_inferVar_unsound_of_dataBody .param rfl .contra rfl⟩

end Toy.Variance
