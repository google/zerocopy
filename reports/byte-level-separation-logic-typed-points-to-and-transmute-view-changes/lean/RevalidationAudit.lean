import Toy

/-!
Axiom audit for every theorem referenced by `results.json` and by the report text (75 theorems,
including `Toy.ByteSL.Layout2.fits₁_zero`, which the report names only inside the quoted
definition of `structDecode`). Not part of the library target. Run from this directory after
`lake build`:

    lake env lean RevalidationAudit.lean

Every line printed must list only `propext`, `Classical.choice`, `Quot.sound` (or report that the
declaration does not depend on any axioms).
-/

#print axioms Toy.ByteSL.Heap.emp_val
#print axioms Toy.ByteSL.Heap.ext
#print axioms Toy.ByteSL.Heap.join_val
#print axioms Toy.ByteSL.Heap.set_val
#print axioms Toy.ByteSL.Layout2.fits₁_zero
#print axioms Toy.ByteSL.bcopyLoose_safetyMono_and_not_frameProp
#print axioms Toy.ByteSL.bstoreShared_safetyMono_and_not_frameProp
#print axioms Toy.ByteSL.byteHeap_frameRule_nonvacuous
#print axioms Toy.ByteSL.byteHeap_isSepAlgebra_and_not_rightCancel
#print axioms Toy.ByteSL.byte_and_typed_commands_nonvacuous
#print axioms Toy.ByteSL.byte_commands_local
#print axioms Toy.ByteSL.exists_ptsDec_viewChange_nonvacuous
#print axioms Toy.ByteSL.exists_ptsDec_viewChange_of_intoBytes_encodeLeast_fromBytes
#print axioms Toy.ByteSL.exists_ptsDec_viewChange_tight_hEL_A
#print axioms Toy.ByteSL.exists_ptsDec_viewChange_tight_hFB_B
#print axioms Toy.ByteSL.exists_ptsDec_viewChange_tight_hIB_A
#print axioms Toy.ByteSL.frameRuleSound_iff_safetyMono_and_frameProp
#print axioms Toy.ByteSL.niche_viewChange_one_directional
#print axioms Toy.ByteSL.not_sep_ptsDec_nonvacuous
#print axioms Toy.ByteSL.not_sep_ptsDec_of_full_of_pos_size
#print axioms Toy.ByteSL.not_sep_ptsDec_positive_control
#print axioms Toy.ByteSL.not_sep_ptsDec_tight_hn
#print axioms Toy.ByteSL.not_sep_ptsDec_tight_hpq
#print axioms Toy.ByteSL.padding_viewChange_one_directional
#print axioms Toy.ByteSL.ptsDec_entails_ptsDec_iff_transmute_eq_some_nonvacuous
#print axioms Toy.ByteSL.ptsDec_entails_ptsDec_iff_transmute_eq_some_of_decodeEncode_encodeLeast_decodeMono
#print axioms Toy.ByteSL.ptsDec_entails_ptsDec_of_transmute_eq_some_nonvacuous
#print axioms Toy.ByteSL.ptsDec_entails_ptsDec_of_transmute_eq_some_of_intoBytes_encodeLeast
#print axioms Toy.ByteSL.ptsDec_entails_ptsDec_of_transmute_tight_hEL_A
#print axioms Toy.ByteSL.ptsDec_entails_ptsDec_of_transmute_tight_hIB_A
#print axioms Toy.ByteSL.ptsDec_entails_ptsDec_of_transmute_tight_ht
#print axioms Toy.ByteSL.ptsDec_entails_ptsDec_tight_hDE_A
#print axioms Toy.ByteSL.ptsDec_entails_ptsDec_tight_hEL_A
#print axioms Toy.ByteSL.ptsDec_entails_ptsDec_tight_hM_B
#print axioms Toy.ByteSL.ptsDec_eq_byteUpClose_fails_boolNZRep
#print axioms Toy.ByteSL.ptsDec_eq_byteUpClose_fails_exactUnitRep
#print axioms Toy.ByteSL.ptsDec_eq_byteUpClose_fails_noneRep
#print axioms Toy.ByteSL.ptsDec_eq_byteUpClose_nonvacuous
#print axioms Toy.ByteSL.ptsDec_eq_byteUpClose_ptsEnc_iff_decodeMono_decodeEncode_encodeLeast
#print axioms Toy.ByteSL.ptsDec_iff_ptsEnc_iff_intoBytes_nonvacuous
#print axioms Toy.ByteSL.ptsDec_iff_ptsEnc_iff_intoBytes_of_decodeMono_decodeEncode_encodeLeast_nonempty
#print axioms Toy.ByteSL.ptsDec_iff_ptsEnc_iff_intoBytes_tight_hD
#print axioms Toy.ByteSL.ptsDec_iff_ptsEnc_iff_intoBytes_tight_hDE
#print axioms Toy.ByteSL.ptsDec_iff_ptsEnc_iff_intoBytes_tight_hEL
#print axioms Toy.ByteSL.ptsDec_iff_ptsEnc_iff_intoBytes_tight_hM
#print axioms Toy.ByteSL.ptsDec_struct_iff_sep_fields_padAny_nonvacuous
#print axioms Toy.ByteSL.ptsDec_struct_iff_sep_fields_padAny_of_nonOverlap
#print axioms Toy.ByteSL.ptsDec_struct_split_padUninit_fails
#print axioms Toy.ByteSL.ptsDec_struct_split_tight_hL
#print axioms Toy.ByteSL.ptsEnc_entails_ptsDec_fails_noneRep
#print axioms Toy.ByteSL.ptsEnc_entails_ptsDec_iff_decodeEncode
#print axioms Toy.ByteSL.ptsEnc_entails_ptsDec_iff_decodeEncode_nonvacuous
#print axioms Toy.ByteSL.ptsEnc_entails_ptsDec_iff_transmute_eq_some
#print axioms Toy.ByteSL.ptsEnc_entails_ptsDec_iff_transmute_eq_some_nonvacuous
#print axioms Toy.ByteSL.ptsEnc_struct_iff_sep_fields_padUninit_nonvacuous
#print axioms Toy.ByteSL.ptsEnc_struct_iff_sep_fields_padUninit_of_nonOverlap
#print axioms Toy.ByteSL.ptsEnc_struct_join_padAny_fails
#print axioms Toy.ByteSL.ptsEnc_struct_split_tight_hL
#print axioms Toy.ByteSL.readBytes_frame_stable
#print axioms Toy.ByteSL.readBytes_frame_stable_shared_ro_nonvacuous
#print axioms Toy.ByteSL.readBytes_frame_stable_tight_hd
#print axioms Toy.ByteSL.readBytes_frame_stable_tight_hr
#print axioms Toy.ByteSL.sep_ro_ptsDec_iff_block_decodes
#print axioms Toy.ByteSL.sep_ro_ptsDec_nonvacuous
#print axioms Toy.ByteSL.sep_ro_ptsDec_satisfiable_iff_common_bytes
#print axioms Toy.ByteSL.sep_ro_ptsEnc_satisfiable_iff_encode_eq
#print axioms Toy.ByteSL.tcopyLoose_local_nonvacuous
#print axioms Toy.ByteSL.tcopyLoose_local_of_decodeMono
#print axioms Toy.ByteSL.tcopyLoose_not_local_exactUnitRep
#print axioms Toy.ByteSL.tcopyLoose_reads_frame_owned_full_cell
#print axioms Toy.ByteSL.transmuteTotal_of_intoBytes_of_fromBytes
#print axioms Toy.ByteSL.typed_commands_local
#print axioms Toy.ByteSL.u8PadRep_laws_and_ptsDec_not_ptsEnc_of_init_padding
#print axioms Toy.ByteSL.u8PadRep_uninit_padding_ptsDec_and_ptsEnc
#print axioms Toy.ByteSL.viewChange_hyps_hold_and_source_ptsDec_empty_noneRep
