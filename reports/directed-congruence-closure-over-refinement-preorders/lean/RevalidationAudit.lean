import ToyDirCC

/-! Prints the axioms and the statement of every declaration referenced by `results.json`.
Run from `lean/` after `lake build` with `lake env lean RevalidationAudit.lean`. -/

#check @Toy.DirCC.Dup.dup_vs_let_hashcons_counterexample
#print axioms Toy.DirCC.Dup.dup_vs_let_hashcons_counterexample
#check @Toy.DirCC.Dup.hashcons_inline_sound_needs_uniqueTags
#print axioms Toy.DirCC.Dup.hashcons_inline_sound_needs_uniqueTags
#check @Toy.DirCC.Dup.hashcons_inline_sound_nonvacuous
#print axioms Toy.DirCC.Dup.hashcons_inline_sound_nonvacuous
#check @Toy.DirCC.Dup.hashcons_inline_sound_of_uniqueTags
#print axioms Toy.DirCC.Dup.hashcons_inline_sound_of_uniqueTags
#check @Toy.DirCC.Dup.hcSem_iff_tagSem_needs_letFree
#print axioms Toy.DirCC.Dup.hcSem_iff_tagSem_needs_letFree
#check @Toy.DirCC.Dup.hcSem_iff_tagSem_needs_wellTagged
#print axioms Toy.DirCC.Dup.hcSem_iff_tagSem_needs_wellTagged
#check @Toy.DirCC.Dup.hcSem_iff_tagSem_nonvacuous
#print axioms Toy.DirCC.Dup.hcSem_iff_tagSem_nonvacuous
#check @Toy.DirCC.Dup.hcSem_iff_tagSem_of_letFree_wellTagged
#print axioms Toy.DirCC.Dup.hcSem_iff_tagSem_of_letFree_wellTagged
#check @Toy.DirCC.Dup.tagSem_iff_indep_needs_uniqueTags
#print axioms Toy.DirCC.Dup.tagSem_iff_indep_needs_uniqueTags
#check @Toy.DirCC.Dup.tagSem_iff_indep_nonvacuous
#print axioms Toy.DirCC.Dup.tagSem_iff_indep_nonvacuous
#check @Toy.DirCC.Dup.tagSem_iff_indep_of_uniqueTags
#print axioms Toy.DirCC.Dup.tagSem_iff_indep_of_uniqueTags
#check @Toy.DirCC.check_sound
#print axioms Toy.DirCC.check_sound
#check @Toy.DirCC.check_sound_needs_check
#print axioms Toy.DirCC.check_sound_needs_check
#check @Toy.DirCC.check_sound_needs_factsHold
#print axioms Toy.DirCC.check_sound_needs_factsHold
#check @Toy.DirCC.check_sound_needs_kerAt
#print axioms Toy.DirCC.check_sound_needs_kerAt
#check @Toy.DirCC.check_sound_needs_monoAt
#print axioms Toy.DirCC.check_sound_needs_monoAt
#check @Toy.DirCC.check_sound_needs_refl
#print axioms Toy.DirCC.check_sound_needs_refl
#check @Toy.DirCC.check_sound_needs_trans
#print axioms Toy.DirCC.check_sound_needs_trans
#check @Toy.DirCC.check_sound_nonvacuous
#print axioms Toy.DirCC.check_sound_nonvacuous
#check @Toy.DirCC.check_sound_of_admissible
#print axioms Toy.DirCC.check_sound_of_admissible
#check @Toy.DirCC.check_sound_of_admissible_needs_admissible
#print axioms Toy.DirCC.check_sound_of_admissible_needs_admissible
#check @Toy.DirCC.check_sound_of_admissible_needs_check
#print axioms Toy.DirCC.check_sound_of_admissible_needs_check
#check @Toy.DirCC.check_sound_of_admissible_needs_factsHold
#print axioms Toy.DirCC.check_sound_of_admissible_needs_factsHold
#check @Toy.DirCC.check_sound_of_admissible_needs_kerAt
#print axioms Toy.DirCC.check_sound_of_admissible_needs_kerAt
#check @Toy.DirCC.check_sound_of_admissible_needs_monoAt
#print axioms Toy.DirCC.check_sound_of_admissible_needs_monoAt
#check @Toy.DirCC.check_sound_of_admissible_needs_refl
#print axioms Toy.DirCC.check_sound_of_admissible_needs_refl
#check @Toy.DirCC.check_sound_of_admissible_needs_trans
#print axioms Toy.DirCC.check_sound_of_admissible_needs_trans
#check @Toy.DirCC.check_sound_of_admissible_nonvacuous
#print axioms Toy.DirCC.check_sound_of_admissible_nonvacuous
#check @Toy.DirCC.eqCong_refuted_at_opaque
#print axioms Toy.DirCC.eqCong_refuted_at_opaque
#check @Toy.DirCC.eqCong_refuted_needs_opaque
#print axioms Toy.DirCC.eqCong_refuted_needs_opaque
#check @Toy.DirCC.eqCong_refuted_nonvacuous
#print axioms Toy.DirCC.eqCong_refuted_nonvacuous
#check @Toy.DirCC.eqCong_sound_at_nonOpaque
#print axioms Toy.DirCC.eqCong_sound_at_nonOpaque
#check @Toy.DirCC.extractWF_needs_chosenMono
#print axioms Toy.DirCC.extractWF_needs_chosenMono
#check @Toy.DirCC.extractWF_needs_chosenOriented
#print axioms Toy.DirCC.extractWF_needs_chosenOriented
#check @Toy.DirCC.extractWF_needs_monoAt
#print axioms Toy.DirCC.extractWF_needs_monoAt
#check @Toy.DirCC.extractWF_needs_trans
#print axioms Toy.DirCC.extractWF_needs_trans
#check @Toy.DirCC.extractWF_needs_wfBelow
#print axioms Toy.DirCC.extractWF_needs_wfBelow
#check @Toy.DirCC.extract_cycle_counterexample
#print axioms Toy.DirCC.extract_cycle_counterexample
#check @Toy.DirCC.extract_needs_choiceIn
#print axioms Toy.DirCC.extract_needs_choiceIn
#check @Toy.DirCC.extract_needs_chosenMono
#print axioms Toy.DirCC.extract_needs_chosenMono
#check @Toy.DirCC.extract_needs_extract_some
#print axioms Toy.DirCC.extract_needs_extract_some
#check @Toy.DirCC.extract_needs_monoAt
#print axioms Toy.DirCC.extract_needs_monoAt
#check @Toy.DirCC.extract_needs_trans
#print axioms Toy.DirCC.extract_needs_trans
#check @Toy.DirCC.extract_oriented_needs_oriented
#print axioms Toy.DirCC.extract_oriented_needs_oriented
#check @Toy.DirCC.extract_refines_nonvacuous
#print axioms Toy.DirCC.extract_refines_nonvacuous
#check @Toy.DirCC.extract_refines_of_chosenOriented_mono
#print axioms Toy.DirCC.extract_refines_of_chosenOriented_mono
#check @Toy.DirCC.extract_refines_of_oriented_mono
#print axioms Toy.DirCC.extract_refines_of_oriented_mono
#check @Toy.DirCC.extract_total_and_sound_of_wfBelow_oriented_mono
#print axioms Toy.DirCC.extract_total_and_sound_of_wfBelow_oriented_mono
#check @Toy.DirCC.extract_unoriented_counterexample
#print axioms Toy.DirCC.extract_unoriented_counterexample
#check @Toy.DirCC.extract_wf_nonvacuous
#print axioms Toy.DirCC.extract_wf_nonvacuous
#check @Toy.DirCC.monoCong_refuted_at_nonMono
#print axioms Toy.DirCC.monoCong_refuted_at_nonMono
#check @Toy.DirCC.monoCong_refuted_needs_nonMono
#print axioms Toy.DirCC.monoCong_refuted_needs_nonMono
#check @Toy.DirCC.monoCong_refuted_nonvacuous
#print axioms Toy.DirCC.monoCong_refuted_nonvacuous
#check @Toy.DirCC.monoCong_sound_at_mono
#print axioms Toy.DirCC.monoCong_sound_at_mono
#check @Toy.DirCC.not_policySound_permissive_oProfile
#print axioms Toy.DirCC.not_policySound_permissive_oProfile
#check @Toy.DirCC.pickFirst_eqCong_counterexample
#print axioms Toy.DirCC.pickFirst_eqCong_counterexample
#check @Toy.DirCC.pickMin_monoCong_counterexample
#print axioms Toy.DirCC.pickMin_monoCong_counterexample
#check @Toy.DirCC.policySound_iff_admissibleFor
#print axioms Toy.DirCC.policySound_iff_admissibleFor
#check @Toy.DirCC.policySound_nonvacuous
#print axioms Toy.DirCC.policySound_nonvacuous
#check @Toy.DirCC.policySound_permissive_of_empty_op
#print axioms Toy.DirCC.policySound_permissive_of_empty_op
#check @Toy.DirCC.policySound_standard_oProfile
#print axioms Toy.DirCC.policySound_standard_oProfile
