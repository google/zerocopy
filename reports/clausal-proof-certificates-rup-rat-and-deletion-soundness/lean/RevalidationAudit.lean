import ToyDrat

/-!
# Axiom audit for every declaration referenced by `results.json`

The 85 declarations named in its structured fields, then the 20 further lemmas cited by name
only in its prose (non-claims, tier notes, non-vacuity witness descriptions, plain readings of
secondary theorems).

Not part of the `ToyDrat` library target. Run from this directory after `lake build`:

    lake env lean RevalidationAudit.lean

Each `#print axioms` line must report no axioms or a subset of
`propext`, `Classical.choice`, `Quot.sound`. Statement and definition-closure hashes are
recomputed by `support/revalidate.py` (see the package's Revalidation section).
-/

#print axioms Toy.Drat.rup_implies_entails
#print axioms Toy.Drat.rup_addition_preserves_equivalence
#print axioms Toy.Drat.equivalent_cons_iff_entails
#print axioms Toy.Drat.rup_implies_entails_tight_rup
#print axioms Toy.Drat.rup_implies_entails_nonvacuous
#print axioms Toy.Drat.rup_equivalence_tight_rup
#print axioms Toy.Drat.entails_not_implies_rup
#print axioms Toy.Drat.entails_not_implies_rup_satisfiable_nonempty
#print axioms Toy.Drat.ratOn_witness_satisfies
#print axioms Toy.Drat.ratOn_witness_tight_mem
#print axioms Toy.Drat.ratOn_witness_tight_rat
#print axioms Toy.Drat.ratOn_witness_tight_model
#print axioms Toy.Drat.ratOn_witness_nonvacuous
#print axioms Toy.Drat.rat_addition_preserves_satisfiability
#print axioms Toy.Drat.ratOn_preserves_satisfiability
#print axioms Toy.Drat.rat_addition_equisatisfiable
#print axioms Toy.Drat.rat_sat_tight_rat
#print axioms Toy.Drat.rat_sat_tight_sat
#print axioms Toy.Drat.rat_sat_nonvacuous
#print axioms Toy.Drat.ratOn_sat_tight_mem
#print axioms Toy.Drat.ratOn_sat_tight_rat
#print axioms Toy.Drat.ratOn_sat_tight_sat
#print axioms Toy.Drat.ratOn_sat_nonvacuous
#print axioms Toy.Drat.rat_equisat_tight_rat
#print axioms Toy.Drat.rat_addition_not_equivalence
#print axioms Toy.Drat.rat_addition_loses_projected_model
#print axioms Toy.Drat.rup_implies_rat_of_ne_nil
#print axioms Toy.Drat.rup_implies_ratOn
#print axioms Toy.Drat.rup_nil_not_rat
#print axioms Toy.Drat.rup_rat_tight_rup
#print axioms Toy.Drat.rup_rat_nonvacuous
#print axioms Toy.Drat.rat_check_depends_on_pivot_order
#print axioms Toy.Drat.checkGen_sound_unsat_of_addCheck_preserves_sat
#print axioms Toy.Drat.checkGen_unchecked_additions_unsound
#print axioms Toy.Drat.checker_acceptance_tight
#print axioms Toy.Drat.checkGen_sound_nonvacuous
#print axioms Toy.Drat.checkDRAT_sound_unsat
#print axioms Toy.Drat.checkOperational_sound_unsat
#print axioms Toy.Drat.checkDRAT_sound_nonvacuous
#print axioms Toy.Drat.addOK_preserves_satisfiability
#print axioms Toy.Drat.applyDel_preserves_satisfiability
#print axioms Toy.Drat.addOK_tight_check
#print axioms Toy.Drat.addOK_tight_sat
#print axioms Toy.Drat.addOK_nonvacuous
#print axioms Toy.Drat.applyDel_tight_sat
#print axioms Toy.Drat.applyDel_nonvacuous
#print axioms Toy.Drat.naiveSatCheck_unsound_with_deletions
#print axioms Toy.Drat.deletion_can_turn_unsat_into_sat
#print axioms Toy.Drat.naiveSatCheck_sound_of_noDeletions
#print axioms Toy.Drat.satCheckRupDel_sound
#print axioms Toy.Drat.replayRatDel_sat_backward
#print axioms Toy.Drat.replay_model_sound_of_noDeletions
#print axioms Toy.Drat.naiveSatCheck_noDel_tight_noDel
#print axioms Toy.Drat.naiveSatCheck_noDel_tight_accept
#print axioms Toy.Drat.naiveSatCheck_noDel_nonvacuous
#print axioms Toy.Drat.replay_model_sound_tight_noDel
#print axioms Toy.Drat.replay_model_sound_tight_replay
#print axioms Toy.Drat.replay_model_sound_tight_sat
#print axioms Toy.Drat.replay_model_sound_nonvacuous
#print axioms Toy.Drat.satCheckRupDel_tight_accept
#print axioms Toy.Drat.satCheckRupDel_nonvacuous
#print axioms Toy.Drat.replayRatDel_tight_replay
#print axioms Toy.Drat.replayRatDel_tight_sat
#print axioms Toy.Drat.replayRatDel_nonvacuous
#print axioms Toy.Drat.rat_after_deletion_not_rat_wrt_original
#print axioms Toy.Drat.operational_accepts_specified_rejects
#print axioms Toy.Drat.specified_accepts_operational_rejects
#print axioms Toy.Drat.checkDRUP_specified_implies_operational
#print axioms Toy.Drat.checkDRUP_honorAll_implies_any_policy
#print axioms Toy.Drat.checkDRUP_policy_tight_sub
#print axioms Toy.Drat.checkDRUP_policy_tight_accept
#print axioms Toy.Drat.checkDRUP_policy_nonvacuous
#print axioms Toy.Drat.lrat_hint_replay_implies_rup
#print axioms Toy.Drat.lrat_hint_replay_implies_entails
#print axioms Toy.Drat.lrat_tight_accept
#print axioms Toy.Drat.lratRupCheck_chain3
#print axioms Toy.Drat.lrat_hint_order_matters
#print axioms Toy.Drat.sloppy_hint_replay_unsound
#print axioms Toy.Drat.lratRupCheck_complete_of_wellformed
#print axioms Toy.Drat.lratRupCheckDedup_exists_iff_rup
#print axioms Toy.Drat.lratRupCheck_rejects_blocked_resolvent
#print axioms Toy.Drat.lratRupCheck_incomplete_tautology
#print axioms Toy.Drat.lratRupCheck_incomplete_dup_lits
#print axioms Toy.Drat.lrat_complete_tight_rup
#print axioms Toy.Drat.lrat_complete_nonvacuous
#print axioms Toy.Drat.rupCheck_of_mem
#print axioms Toy.Drat.lratRupCheck_side_conditions_not_necessary
#print axioms Toy.Drat.RAT_example_pos
#print axioms Toy.Drat.RAT_example_pos_not_entailed
#print axioms Toy.Drat.checkGen_empty_certificate
#print axioms Toy.Drat.checkSpecified_fullSquare
#print axioms Toy.Drat.drat_certificate_not_monotone_in_formula
#print axioms Toy.Drat.ignoreUnitDeletions_example_dup
#print axioms Toy.Drat.lratRupCheckDedup_eq_of_wellformed
#print axioms Toy.Drat.lratRupCheck_example_satisfied_hint
#print axioms Toy.Drat.lratRupCheck_example_trailing_hints
#print axioms Toy.Drat.one_copy_deletion_breaks_drup_monotonicity
#print axioms Toy.Drat.permuted_deletion_is_ignored
#print axioms Toy.Drat.ratCheck_example_neg
#print axioms Toy.Drat.ratOn_without_mem_unsound
#print axioms Toy.Drat.rat_not_monotone_in_formula
#print axioms Toy.Drat.rat_not_rup_addition_preserves_equivalence
#print axioms Toy.Drat.replayRatDel_final_model_not_original
#print axioms Toy.Drat.rupCheck_of_nil_mem
#print axioms Toy.Drat.rupCheck_sound
