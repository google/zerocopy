import KInd

/-!
# Axiom audit for every declaration referenced by `results.json`

Not part of the library target. Run from this directory after `lake build`:

    lake env lean RevalidationAudit.lean

Each `#print axioms` line must report only `propext`, `Classical.choice` and `Quot.sound` (or
no axioms). Statement and definition-closure hashes are recomputed by `support/revalidate.py`.
-/


#print axioms Toy.KInd.SimpleStep.mono
#print axioms Toy.KInd.Step.mono
#print axioms Toy.KInd.base_at_recurrence_diameter_unsound
#print axioms Toy.KInd.base_iff_exactBase_of_total
#print axioms Toy.KInd.bmc_complete_all_props_iff_reachDiameterBound
#print axioms Toy.KInd.bmc_complete_fin
#print axioms Toy.KInd.bmc_complete_fin_depth_tight
#print axioms Toy.KInd.bmc_complete_fin_depth_tight_all
#print axioms Toy.KInd.bmc_complete_of_reachDiameterBound
#print axioms Toy.KInd.bmc_complete_of_reachRecurrenceBound
#print axioms Toy.KInd.bmc_incomplete_every_depth_infinite
#print axioms Toy.KInd.bmc_incomplete_needs_not_reachDiameterBound
#print axioms Toy.KInd.bmc_incomplete_of_not_reachDiameterBound
#print axioms Toy.KInd.bmc_reachDiameter_needs_hb
#print axioms Toy.KInd.bmc_reachDiameter_needs_hd
#print axioms Toy.KInd.bmc_reachDiameter_needs_hk
#print axioms Toy.KInd.bmc_reachRecurrence_needs_hb
#print axioms Toy.KInd.bmc_reachRecurrence_needs_hk
#print axioms Toy.KInd.bmc_reachRecurrence_needs_hr
#print axioms Toy.KInd.chain_not_reachDiameterBound_one
#print axioms Toy.KInd.chain_reachDiameterBound_two
#print axioms Toy.KInd.chain_reachWithin_two_invariant
#print axioms Toy.KInd.exact_length_base_unsound_without_totality
#print axioms Toy.KInd.exists_simple_reachIn
#print axioms Toy.KInd.futureSafe_forever_weakest_inductive_strengthening
#print axioms Toy.KInd.futureSafe_strengthening_needs_base
#print axioms Toy.KInd.futureSafe_strengthening_needs_base_k1
#print axioms Toy.KInd.futureSafe_strengthening_needs_step
#print axioms Toy.KInd.futureSafe_strengthening_needs_step_k1
#print axioms Toy.KInd.invariant_iff_exists_inductive_strengthening
#print axioms Toy.KInd.invariant_iff_reachable_strengthening_inductive
#print axioms Toy.KInd.invariant_of_inductive_strengthening
#print axioms Toy.KInd.isReachDiameter_le_needs_hd
#print axioms Toy.KInd.isReachDiameter_le_needs_hr
#print axioms Toy.KInd.isReachDiameter_le_of_reachRecurrenceBound
#print axioms Toy.KInd.kind_simple_sound
#print axioms Toy.KInd.kind_simple_sound_base_depth_tight
#print axioms Toy.KInd.kind_simple_sound_needs_base
#print axioms Toy.KInd.kind_simple_sound_needs_base_k2
#print axioms Toy.KInd.kind_simple_sound_needs_step_k2
#print axioms Toy.KInd.kind_sound
#print axioms Toy.KInd.kind_sound_base_depth_tight
#print axioms Toy.KInd.kind_sound_needs_base
#print axioms Toy.KInd.kind_sound_needs_step
#print axioms Toy.KInd.kind_success_mono
#print axioms Toy.KInd.kind_success_mono_needs_base
#print axioms Toy.KInd.kind_success_mono_needs_le
#print axioms Toy.KInd.kind_success_mono_needs_step
#print axioms Toy.KInd.kind_success_mono_needs_step_invariant
#print axioms Toy.KInd.ladder_inductive_strengthening
#print axioms Toy.KInd.ladder_kind_succeeds_at_depth_succ
#print axioms Toy.KInd.ladder_needs_depth_succ
#print axioms Toy.KInd.ladder_reachDiameterBound_zero_bmc_zero
#print axioms Toy.KInd.loop_removal_needs_reachIn
#print axioms Toy.KInd.natDescent_bmc_zero_proves_invariant
#print axioms Toy.KInd.nonvacuity_base_iff_exactBase_of_total
#print axioms Toy.KInd.nonvacuity_bmc_complete_fin
#print axioms Toy.KInd.nonvacuity_bmc_complete_of_reachDiameterBound
#print axioms Toy.KInd.nonvacuity_bmc_complete_of_reachRecurrenceBound
#print axioms Toy.KInd.nonvacuity_exists_simple_reachIn
#print axioms Toy.KInd.nonvacuity_inductive_strengthening
#print axioms Toy.KInd.nonvacuity_isReachDiameter_le_of_reachRecurrenceBound
#print axioms Toy.KInd.nonvacuity_kind_simple_sound
#print axioms Toy.KInd.nonvacuity_kind_sound
#print axioms Toy.KInd.nonvacuity_kind_success_mono
#print axioms Toy.KInd.nonvacuity_simpleStep_mono
#print axioms Toy.KInd.nonvacuity_simpleStep_of_card_le
#print axioms Toy.KInd.nonvacuity_simple_kind_complete_fin
#print axioms Toy.KInd.nonvacuity_simple_kinductive_futureSafe_strengthening
#print axioms Toy.KInd.nonvacuity_step_mono
#print axioms Toy.KInd.one_induction_fails_two_induction_succeeds
#print axioms Toy.KInd.plain_kind_incomplete_every_depth
#print axioms Toy.KInd.reachDiameterBound_of_reachRecurrenceBound
#print axioms Toy.KInd.reachDiameterBound_of_reachRecurrenceBound_needs_hr
#print axioms Toy.KInd.reachDiameter_lt_reachRecurrenceDiameter_family
#print axioms Toy.KInd.reachable_strongest_inductive_invariant
#print axioms Toy.KInd.selfLoop_reachDiameterBound_zero_bmc_zero
#print axioms Toy.KInd.selfLoop_reachable_iff
#print axioms Toy.KInd.selfLoop_simple_kind_succeeds_at_two
#print axioms Toy.KInd.simpleStep_mono_needs_le
#print axioms Toy.KInd.simpleStep_mono_needs_step
#print axioms Toy.KInd.simpleStep_of_card_le
#print axioms Toy.KInd.simple_kind_complete_fin
#print axioms Toy.KInd.simple_kind_complete_fin_needs_invariant
#print axioms Toy.KInd.simple_kind_complete_fin_pred_of_init
#print axioms Toy.KInd.simple_kind_complete_fin_pred_of_init_needs_invariant
#print axioms Toy.KInd.simple_kind_depth_card_optimal_without_init
#print axioms Toy.KInd.simple_kind_depth_pred_optimal_with_init
#print axioms Toy.KInd.simple_kind_incomplete_every_depth_infinite
#print axioms Toy.KInd.simple_kinductive_futureSafe_strengthening
#print axioms Toy.KInd.step_card_of_acyclic
#print axioms Toy.KInd.step_mono_needs_le
#print axioms Toy.KInd.step_mono_needs_step
#print axioms Toy.KInd.step_zero_of_invariant_of_all_reachable
#print axioms Toy.KInd.strengthening_needs_consecution
#print axioms Toy.KInd.strengthening_needs_init_P
#print axioms Toy.KInd.strengthening_needs_init_Q
#print axioms Toy.KInd.triangle_reachDiameter_one_reachRecurrenceDiameter_two
