import ToyRepr

/-!
Axiom audit for the theorems referenced by `results.json` (and the supporting boundary theorems).
Not part of the library target. Run from this directory after `lake build`:

    lake env lean RevalidationAudit.lean

Every line printed must list only `propext`, `Classical.choice`, `Quot.sound`.
-/

#print axioms Toy.Repr.Rep.encode_injective_of_decodeEncode
#print axioms Toy.Repr.Rep.lowerAdjoint_iff_galois_liftEncode
#print axioms Toy.Repr.decodeIgnores_of_empty
#print axioms Toy.Repr.decodeIgnores_of_encode_uninit_nonvacuous
#print axioms Toy.Repr.decodeIgnores_of_encode_uninit_tight_hDE
#print axioms Toy.Repr.decodeIgnores_of_encode_uninit_tight_hEL
#print axioms Toy.Repr.decodeIgnores_of_encode_uninit_tight_hM
#print axioms Toy.Repr.decodeIgnores_of_encode_uninit_tight_hU
#print axioms Toy.Repr.decodeIgnores_of_threeLaws_of_encode_getElem_eq_uninit
#print axioms Toy.Repr.decode_eq_iff_threeLaws
#print axioms Toy.Repr.decode_eq_iff_threeLaws_nonvacuous
#print axioms Toy.Repr.decode_eq_iff_threeLaws_tight_hDE
#print axioms Toy.Repr.decode_eq_iff_threeLaws_tight_hEL
#print axioms Toy.Repr.decode_eq_iff_threeLaws_tight_hM
#print axioms Toy.Repr.encode_eq_iff_decodeEncode_encodeLeast
#print axioms Toy.Repr.encode_eq_iff_decodeEncode_encodeLeast_nonvacuous
#print axioms Toy.Repr.encode_eq_iff_decodeEncode_encodeLeast_tight_hDE
#print axioms Toy.Repr.encode_eq_iff_decodeEncode_encodeLeast_tight_hEL
#print axioms Toy.Repr.encode_getElem_eq_uninit_of_decodeEncode_encodeLeast_of_decodeIgnores
#print axioms Toy.Repr.encode_getElem_eq_uninit_of_decodeIgnores_nonvacuous
#print axioms Toy.Repr.encode_getElem_eq_uninit_of_decodeIgnores_tight_hDE
#print axioms Toy.Repr.encode_getElem_eq_uninit_of_decodeIgnores_tight_hEL
#print axioms Toy.Repr.encode_getElem_eq_uninit_of_decodeIgnores_tight_hIgn
#print axioms Toy.Repr.eq_of_encode_le_encode_nonvacuous
#print axioms Toy.Repr.eq_of_encode_le_encode_of_decodeMono_decodeEncode
#print axioms Toy.Repr.eq_of_encode_le_encode_tight_hDE
#print axioms Toy.Repr.eq_of_encode_le_encode_tight_hM
#print axioms Toy.Repr.ex_ptrDecodeStrict_accepts_duplicated_byte
#print axioms Toy.Repr.int_ptr_int_roundtrip_nonvacuous
#print axioms Toy.Repr.int_ptr_int_roundtrip_of_decodeEncode
#print axioms Toy.Repr.int_ptr_int_roundtrip_tight_hDEi
#print axioms Toy.Repr.int_ptr_int_roundtrip_tight_hDEp
#print axioms Toy.Repr.intoBytes_of_transmuteTotal_of_intoBytes_of_encodeLeast
#print axioms Toy.Repr.no_int_decoder_encodeLeast_fromBytes_of_provenance
#print axioms Toy.Repr.no_int_decoder_nonvacuous
#print axioms Toy.Repr.no_int_decoder_positive_control
#print axioms Toy.Repr.no_int_decoder_tight_b0
#print axioms Toy.Repr.no_int_decoder_tight_hn
#print axioms Toy.Repr.no_int_decoder_tight_p0
#print axioms Toy.Repr.no_lawful_decoder_for_conflictBoolEnc
#print axioms Toy.Repr.no_lawful_encoder_for_monotone_orUnitRep
#print axioms Toy.Repr.no_optProvPtr_decoder_decodeMono_decodeEncode_of_provInc
#print axioms Toy.Repr.no_ptr_decodeEncode_size_zero
#print axioms Toy.Repr.no_ptr_decoder_nonvacuous
#print axioms Toy.Repr.no_ptr_decoder_positive_control
#print axioms Toy.Repr.no_ptr_decoder_tight_b0
#print axioms Toy.Repr.no_ptr_decoder_tight_p0
#print axioms Toy.Repr.no_singleProvInt_decoder_encodeLeast_fromBytes_of_two_le
#print axioms Toy.Repr.prodRep_decodeEncode_of_fields_of_disjoint
#print axioms Toy.Repr.prodRep_decodeEncode_tight_hD
#print axioms Toy.Repr.prodRep_decodeEncode_tight_hDE
#print axioms Toy.Repr.prodRep_decodeMono_of_fields
#print axioms Toy.Repr.prodRep_decodeMono_tight_hM
#print axioms Toy.Repr.prodRep_encodeLeast_of_fields
#print axioms Toy.Repr.prodRep_encodeLeast_tight_hEL
#print axioms Toy.Repr.prodRep_fromBytes_of_fields
#print axioms Toy.Repr.prodRep_fromBytes_tight_hFB
#print axioms Toy.Repr.prodRep_intoBytes_nonvacuous
#print axioms Toy.Repr.prodRep_intoBytes_of_fields_of_covering
#print axioms Toy.Repr.prodRep_intoBytes_tight_hC
#print axioms Toy.Repr.prodRep_intoBytes_tight_hIB
#print axioms Toy.Repr.prodRep_laws_nonvacuous
#print axioms Toy.Repr.provIntRep_escape_hatch
#print axioms Toy.Repr.ptrDegradeRepInc_lawful_by_ptrValLe
#print axioms Toy.Repr.ptrStrictRepInc_not_decodeMonoBy_ptrValLe
#print axioms Toy.Repr.ptr_intStrip_ptr_roundtrip_drops_provenance_of_decodeEncode
#print axioms Toy.Repr.ptr_intStrip_ptr_roundtrip_nonvacuous
#print axioms Toy.Repr.ptr_intStrip_ptr_roundtrip_tight_hDEp
#print axioms Toy.Repr.reqProvPtrRepInc_threeLaws
#print axioms Toy.Repr.threeLaws_iff_lowerAdjoint
#print axioms Toy.Repr.threeLaws_iff_lowerAdjoint_nonvacuous
#print axioms Toy.Repr.transmuteTotal_iff_image_subset_valid
#print axioms Toy.Repr.transmuteTotal_iff_image_subset_valid_nonvacuous
#print axioms Toy.Repr.transmuteTotal_iff_initValid_subset_nonvacuous
#print axioms Toy.Repr.transmuteTotal_iff_initValid_subset_of_intoBytes_decodeEncode_encodeLeast
#print axioms Toy.Repr.transmuteTotal_iff_initValid_subset_tight_hDE_A
#print axioms Toy.Repr.transmuteTotal_iff_initValid_subset_tight_hEL_A
#print axioms Toy.Repr.transmuteTotal_iff_initValid_subset_tight_hIB_A
#print axioms Toy.Repr.transmuteTotal_iff_valid_subset_nonvacuous
#print axioms Toy.Repr.transmuteTotal_iff_valid_subset_of_laws
#print axioms Toy.Repr.transmuteTotal_iff_valid_subset_tight_hDE_A
#print axioms Toy.Repr.transmuteTotal_iff_valid_subset_tight_hEL_A
#print axioms Toy.Repr.transmuteTotal_iff_valid_subset_tight_hM_B
#print axioms Toy.Repr.transmuteTotal_of_intoBytes_of_fromBytes
#print axioms Toy.Repr.transmuteTotal_of_intoBytes_of_fromBytes_nonvacuous
#print axioms Toy.Repr.transmuteTotal_of_intoBytes_of_fromBytes_tight_hA
#print axioms Toy.Repr.transmuteTotal_of_intoBytes_of_fromBytes_tight_hB
#print axioms Toy.Repr.transmute_bab_roundtrip_of_total_of_intoBytes_encodeLeast_decodeEncode
#print axioms Toy.Repr.transmute_comp_fails_of_provInc
#print axioms Toy.Repr.transmute_comp_nonvacuous
#print axioms Toy.Repr.transmute_comp_of_total_of_encodeLeast_of_intoBytes
#print axioms Toy.Repr.transmute_comp_tight_hEL
#print axioms Toy.Repr.transmute_comp_tight_hIB
#print axioms Toy.Repr.transmute_comp_tight_htot
#print axioms Toy.Repr.transmute_injective_of_bab_hyps_of_decodeEncode_of_encodeLeast
#print axioms Toy.Repr.transmute_ptr_intStrict_eq_none
#print axioms Toy.Repr.transmute_roundtrip_nonvacuous
#print axioms Toy.Repr.transmute_roundtrip_second_step_not_injective
#print axioms Toy.Repr.transmute_roundtrip_second_step_not_injective_of_not_decodeEncode
#print axioms Toy.Repr.transmute_roundtrip_tight_hDE_B
#print axioms Toy.Repr.transmute_roundtrip_tight_hEL_A
#print axioms Toy.Repr.transmute_roundtrip_tight_hIB_A
#print axioms Toy.Repr.transmute_roundtrip_tight_htot
