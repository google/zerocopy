/-
Axiom audit for the result theorems of this package (not part of the library target).
Run from this directory after `lake build`:  lake env lean AxiomAudit.lean
Each line of output must list only a subset of `propext`, `Classical.choice`, `Quot.sound`.
-/

import ToyPerm

#print axioms Toy.Perm.fracAlg_isPCM_cancel_positive
#print axioms Toy.Perm.countAlg_isPCM_cancel_positive
#print axioms Toy.Perm.fracAlg_countAlg_cellSumAlg_violate_disjointness
#print axioms Toy.Perm.fracAlg_nonzero_splits_into_two_nonzero_halves
#print axioms Toy.Perm.fracAlg_halvingSplit_composes
#print axioms Toy.Perm.fracAlg_halvingSplit_full_recombines_to_exclusive
#print axioms Toy.Perm.countAlg_readToken_atomic
#print axioms Toy.Perm.countAlg_split_of_source
#print axioms Toy.Perm.Cell.compatFPU_iff
#print axioms Toy.Perm.cellSumAlg_isPCM_cancel_positive_compat_iff
#print axioms Toy.Perm.restoring_steps_not_framePreserving_of_sharing_exclusion_neutral
#print axioms Toy.Perm.no_assoc_alg_returns_last_share_by_composition_beside_another_reader
#print axioms Toy.Perm.Cell.valid_set_iff
#print axioms Toy.Perm.CellStep.restoresExclusive_iff
#print axioms Toy.Perm.Cell.stepAt_isSome_iff
#print axioms Toy.Perm.cellSumAlg_composite_does_not_determine_endShare_enabled
#print axioms Toy.Perm.countBEmbed_injective_preserves_reflects_op_exclusive_readable
#print axioms Toy.Perm.no_opPreserving_map_countB_to_frac_reflecting_compat
#print axioms Toy.Perm.opPreserving_map_countB_to_frac_sources_or_bundles_compat
#print axioms Toy.Perm.opPreserving_maps_countB_to_frac_keep_either_pair_incompatible
#print axioms Toy.Perm.no_opPreserving_map_count_to_frac_with_nonzero_readToken
#print axioms Toy.Perm.no_opPreserving_map_to_count_sending_self_composite_to_total
#print axioms Toy.Perm.no_opPreserving_map_frac_to_count_sending_full_to_total
#print axioms Toy.Perm.no_opPreserving_map_halfGrid_to_count_sending_full_to_total
#print axioms Toy.Perm.opPreserving_map_frac_to_count_eq_none
#print axioms Toy.Perm.no_opPreserving_map_frac_to_count_with_nonempty_value
#print axioms Toy.Perm.countAlg_source_count_bounds_outstanding_pieces
#print axioms Toy.Perm.countAlg_complete_source_pos_has_outstanding_piece
#print axioms Toy.Perm.countAlg_source_one_complete_exactly_one_piece
#print axioms Toy.Perm.countAlg_readTokens_complete_iff_length_eq_count
#print axioms Toy.Perm.countAlg_total_splits_into_source_and_readTokens
#print axioms Toy.Perm.fracAlg_no_nonexclusive_element_bounds_outstanding_pieces
#print axioms Toy.Perm.fracAlg_owner_complement_splits_into_any_number
#print axioms Toy.Perm.reader_piece_does_not_determine_lastness
