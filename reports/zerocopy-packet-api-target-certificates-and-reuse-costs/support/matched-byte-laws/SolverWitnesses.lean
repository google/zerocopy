import ByteLaws
open ByteLaws
namespace SolverWitnesses
def missing_initialization_s : Memory := ⟨0, 0, false, true, true, true, false, false⟩
def missing_initialization_t : Memory := ⟨0, 0, false, false, false, false, false, false⟩
theorem missing_initialization_countermodel : ¬ (intoWithoutInit missing_initialization_s) := by unfold intoWithoutInit; decide
#print axioms missing_initialization_countermodel
def alias_frame_s : Memory := ⟨0, 0, false, true, false, false, false, true⟩
def alias_frame_t : Memory := ⟨0, 0, false, false, false, false, false, true⟩
theorem alias_frame_countermodel : ¬ (WriteWithoutDisjoint alias_frame_s true true 1) := by unfold WriteWithoutDisjoint; decide
#print axioms alias_frame_countermodel
def bool_two_s : Memory := ⟨2, 0, true, false, true, false, false, false⟩
def bool_two_t : Memory := ⟨2, 0, true, false, true, false, false, false⟩
theorem bool_two_countermodel : ¬ (BoolWrongLaw bool_two_s bool_two_t 3) := by unfold BoolWrongLaw; decide
#print axioms bool_two_countermodel
def missing_stability_s : Memory := ⟨1, 0, true, false, true, false, false, false⟩
def missing_stability_t : Memory := ⟨2, 0, true, false, true, false, false, false⟩
theorem missing_stability_countermodel : ¬ (BoolWithoutStability missing_stability_s missing_stability_t) := by unfold BoolWithoutStability; decide
#print axioms missing_stability_countermodel
def array_index_omission_s : Memory := ⟨0, 2, true, true, true, true, false, false⟩
def array_index_omission_t : Memory := ⟨0, 2, true, true, true, true, false, false⟩
theorem array_index_omission_countermodel : ¬ (ArrayWrongLaw array_index_omission_s array_index_omission_t) := by unfold ArrayWrongLaw; decide
#print axioms array_index_omission_countermodel
end SolverWitnesses
