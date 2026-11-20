import ToyRelax

/-!
Revalidation audit (not part of the library target).

For every Lean name referenced by `results.json`, print its statement and the
axioms it depends on. Run from this directory after `lake build`:

    lake env lean RevalidationAudit.lean

Every `#print axioms` line must list only a subset of `propext`,
`Classical.choice`, `Quot.sound`.
-/

open Toy.Relax Toy.Unwind

#check @Toy.Relax.align_counterexample_still_terminates_valid
#print axioms Toy.Relax.align_counterexample_still_terminates_valid
#check @Toy.Relax.align_growShrink_differs_from_growOnly
#print axioms Toy.Relax.align_growShrink_differs_from_growOnly
#check @Toy.Relax.align_growShrink_four_cycle_from_allShort
#print axioms Toy.Relax.align_growShrink_four_cycle_from_allShort
#check @Toy.Relax.align_padding_breaks_leastness
#print axioms Toy.Relax.align_padding_breaks_leastness
#check @Toy.Relax.align_padding_breaks_size_optimality
#print axioms Toy.Relax.align_padding_breaks_size_optimality
#check @Toy.Relax.distMonotone_example_neg_align
#print axioms Toy.Relax.distMonotone_example_neg_align
#check @Toy.Relax.distMonotone_nonvacuity
#print axioms Toy.Relax.distMonotone_nonvacuity
#check @Toy.Relax.distMonotone_of_sizesMonotone
#print axioms Toy.Relax.distMonotone_of_sizesMonotone
#check @Toy.Relax.dist_decreases_when_size_between_decreases
#print axioms Toy.Relax.dist_decreases_when_size_between_decreases
#check @Toy.Relax.dist_le_dist_of_size_le_between
#print axioms Toy.Relax.dist_le_dist_of_size_le_between
#check @Toy.Relax.dist_mono_nonvacuity
#print axioms Toy.Relax.dist_mono_nonvacuity
#check @Toy.Relax.growShrink_allShort_nonvacuity
#print axioms Toy.Relax.growShrink_allShort_nonvacuity
#check @Toy.Relax.growShrink_two_cycle_controls
#print axioms Toy.Relax.growShrink_two_cycle_controls
#check @Toy.Relax.growShrink_two_cycle_from_nonbottom_start
#print axioms Toy.Relax.growShrink_two_cycle_from_nonbottom_start
#check @Toy.Relax.inverted_growShrink_two_cycle_from_allShort
#print axioms Toy.Relax.inverted_growShrink_two_cycle_from_allShort
#check @Toy.Relax.iter_stepGS_allShort_eq_iter_step_of_distMonotone
#print axioms Toy.Relax.iter_stepGS_allShort_eq_iter_step_of_distMonotone
#check @Toy.Relax.leastness_needs_upper_bound_above_start
#print axioms Toy.Relax.leastness_needs_upper_bound_above_start
#check @Toy.Relax.leastness_needs_valid_upper_bound
#print axioms Toy.Relax.leastness_needs_valid_upper_bound
#check @Toy.Relax.noAlign_needed_for_sizesMonotone
#print axioms Toy.Relax.noAlign_needed_for_sizesMonotone
#check @Toy.Relax.promote_relax_landsExactly_needs_sizesPositiveAt_after
#print axioms Toy.Relax.promote_relax_landsExactly_needs_sizesPositiveAt_after
#check @Toy.Relax.promote_relax_landsExactly_needs_sizesPositiveAt_before
#print axioms Toy.Relax.promote_relax_landsExactly_needs_sizesPositiveAt_before
#check @Toy.Relax.promote_relax_landsExactly_needs_valid
#print axioms Toy.Relax.promote_relax_landsExactly_needs_valid
#check @Toy.Relax.promote_relax_landsExactly_of_valid_of_sizesPositiveAt
#print axioms Toy.Relax.promote_relax_landsExactly_of_valid_of_sizesPositiveAt
#check @Toy.Relax.promote_relax_nonvacuity
#print axioms Toy.Relax.promote_relax_nonvacuity
#check @Toy.Relax.promote_without_relax_breaks_emitDisp
#print axioms Toy.Relax.promote_without_relax_breaks_emitDisp
#check @Toy.Relax.relaxLoop_numBranches_passes_insufficient
#print axioms Toy.Relax.relaxLoop_numBranches_passes_insufficient
#check @Toy.Relax.relaxLoop_returns_relax_within_numBranches_succ
#print axioms Toy.Relax.relaxLoop_returns_relax_within_numBranches_succ
#check @Toy.Relax.relax_allShort_totalSize_le_of_valid_of_distMonotone_of_short_le_long
#print axioms Toy.Relax.relax_allShort_totalSize_le_of_valid_of_distMonotone_of_short_le_long
#check @Toy.Relax.relax_le_of_valid_of_le_of_distMonotone
#print axioms Toy.Relax.relax_le_of_valid_of_le_of_distMonotone
#check @Toy.Relax.relax_le_of_valid_of_le_of_noAlign_of_short_le_long
#print axioms Toy.Relax.relax_le_of_valid_of_le_of_noAlign_of_short_le_long
#check @Toy.Relax.relax_least_nonvacuity
#print axioms Toy.Relax.relax_least_nonvacuity
#check @Toy.Relax.relax_nonvacuity_chain
#print axioms Toy.Relax.relax_nonvacuity_chain
#check @Toy.Relax.relax_valid_and_above_start
#print axioms Toy.Relax.relax_valid_and_above_start
#check @Toy.Relax.short_le_long_needed_for_sizesMonotone
#print axioms Toy.Relax.short_le_long_needed_for_sizesMonotone
#check @Toy.Relax.size_optimality_needs_distMonotone
#print axioms Toy.Relax.size_optimality_needs_distMonotone
#check @Toy.Relax.size_optimality_needs_short_le_long
#print axioms Toy.Relax.size_optimality_needs_short_le_long
#check @Toy.Relax.size_optimality_needs_valid
#print axioms Toy.Relax.size_optimality_needs_valid
#check @Toy.Relax.size_optimality_nonvacuity
#print axioms Toy.Relax.size_optimality_nonvacuity
#check @Toy.Relax.sizesMonotone_nonvacuity
#print axioms Toy.Relax.sizesMonotone_nonvacuity
#check @Toy.Relax.sizesMonotone_of_noAlign_of_short_le_long
#print axioms Toy.Relax.sizesMonotone_of_noAlign_of_short_le_long
#check @Toy.Relax.stale_displacement_lands_elsewhere
#print axioms Toy.Relax.stale_displacement_lands_elsewhere
#check @Toy.Unwind.checkTable_complete
#print axioms Toy.Unwind.checkTable_complete
#check @Toy.Unwind.checkTable_nonvacuity
#print axioms Toy.Unwind.checkTable_nonvacuity
#check @Toy.Unwind.checkTable_sound
#print axioms Toy.Unwind.checkTable_sound
#check @Toy.Unwind.checker_premise_needed
#print axioms Toy.Unwind.checker_premise_needed
#check @Toy.Unwind.genTable_correct_of_no_undefined
#print axioms Toy.Unwind.genTable_correct_of_no_undefined
#check @Toy.Unwind.genTable_no_undefined_nonvacuity
#print axioms Toy.Unwind.genTable_no_undefined_nonvacuity
#check @Toy.Unwind.genTable_with_undefined_incorrect
#print axioms Toy.Unwind.genTable_with_undefined_incorrect
#check @Toy.Unwind.missing_row_after_pop_incorrect
#print axioms Toy.Unwind.missing_row_after_pop_incorrect
#check @Toy.Unwind.offByOne_push_tables_incorrect
#print axioms Toy.Unwind.offByOne_push_tables_incorrect
#check @Toy.Unwind.stale_savedAt_after_pop_correct_without_reuse
#print axioms Toy.Unwind.stale_savedAt_after_pop_correct_without_reuse
#check @Toy.Unwind.stale_savedAt_after_pop_incorrect_after_slot_reuse
#print axioms Toy.Unwind.stale_savedAt_after_pop_incorrect_after_slot_reuse
#check @Toy.Unwind.tableCorrect_example_pos
#print axioms Toy.Unwind.tableCorrect_example_pos
#check @Toy.Unwind.tableCorrect_example_pos_pop
#print axioms Toy.Unwind.tableCorrect_example_pos_pop
#check @Toy.Unwind.tableCorrect_example_pos_reuse
#print axioms Toy.Unwind.tableCorrect_example_pos_reuse
#check @Toy.Unwind.tableCorrect_nonvacuity
#print axioms Toy.Unwind.tableCorrect_nonvacuity
