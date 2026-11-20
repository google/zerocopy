/-
Revalidation audit (not part of the `Toy` library target).

After `lake build`, run from this directory:

    lake env lean RevalidationAudit.lean

For every Lean declaration referenced by `results.json` this prints the axioms
it depends on.  Every line must list only `propext`, `Classical.choice`, and
`Quot.sound` (or no axioms at all).
-/
import Toy

#print axioms Toy.RedGreen.ambient_dependent_code_breaks_early_cutoff
#print axioms Toy.RedGreen.ambient_dependent_code_matches_no_from_scratch_eval
#print axioms Toy.RedGreen.cyclic_new_state_both_diverge
#print axioms Toy.RedGreen.early_cutoff_agrees_nonvacuous
#print axioms Toy.RedGreen.early_cutoff_agrees_with_reexecution_of_ordered_replay
#print axioms Toy.RedGreen.early_cutoff_never_executes_cached_query_with_unchanged_recorded_deps
#print axioms Toy.RedGreen.early_cutoff_reexecutes_query_whose_value_is_unchanged
#print axioms Toy.RedGreen.early_cutoff_skips_nonvacuous
#print axioms Toy.RedGreen.exhaustive_replay_diverges_on_dead_code_cycle
#print axioms Toy.RedGreen.exhaustive_replay_executes_dead_dependency_and_panics
#print axioms Toy.RedGreen.fetch_agrees_with_eval_during_revision_of_ordered_replay
#print axioms Toy.RedGreen.fetch_agrees_with_eval_nonvacuous
#print axioms Toy.RedGreen.fetch_agrees_with_eval_of_ordered_replay
#print axioms Toy.RedGreen.fetch_during_revision_nonvacuous
#print axioms Toy.RedGreen.fetch_eventually_eq_eval_during_revision_of_ordered_replay
#print axioms Toy.RedGreen.fetch_eventually_finishes_during_revision_of_terminates
#print axioms Toy.RedGreen.fetch_simulation_invariant
#print axioms Toy.RedGreen.fetch_simulation_invariant_nonvacuous
#print axioms Toy.RedGreen.fetch_value_sound_nonvacuous
#print axioms Toy.RedGreen.fetch_value_sound_of_any_replay
#print axioms Toy.RedGreen.fp_collision_breaks_early_cutoff
#print axioms Toy.RedGreen.fp_collision_diverges_although_new_state_terminates
#print axioms Toy.RedGreen.fp_collision_reexecutes_query_with_unchanged_recorded_dependencies
#print axioms Toy.RedGreen.fp_collision_reuses_stale_result
#print axioms Toy.RedGreen.inconsistent_db_breaks_early_cutoff
#print axioms Toy.RedGreen.inconsistent_db_diverges_although_new_state_terminates
#print axioms Toy.RedGreen.inconsistent_db_reuses_wrong_result
#print axioms Toy.RedGreen.no_cutoff_reexecutes_query_with_unchanged_recorded_dependencies
#print axioms Toy.RedGreen.ordered_replay_returns_from_scratch_value_on_dead_dependency
#print axioms Toy.RedGreen.reversed_replay_breaks_early_cutoff_agreement
#print axioms Toy.RedGreen.reversed_replay_diverges_on_dead_code_cycle
#print axioms Toy.RedGreen.reversed_replay_executes_dead_dependency_and_panics
#print axioms Toy.RedGreen.stale_db_reexecutes_query_with_unchanged_recorded_dependencies
#print axioms Toy.RedGreen.stale_done_slot_returns_wrong_result
#print axioms Toy.RedGreen.uncached_query_with_unchanged_recorded_dependencies_executes
#print axioms Toy.RedGreen.unreachable_db_diverges_although_new_state_terminates
#print axioms Toy.RedGreen.unreachable_db_reexecutes_query_with_unchanged_recorded_dependencies
#print axioms Toy.RedGreen.untracked_code_change_diverges_although_new_state_terminates
