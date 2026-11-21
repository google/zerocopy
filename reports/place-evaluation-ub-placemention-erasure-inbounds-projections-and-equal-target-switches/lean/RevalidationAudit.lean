import Toy

/-! Prints the axioms of every main result of the cards (not part of the library target). -/

#print axioms Toy.PlaceEval.evalPlace_eq_none_iff
#print axioms Toy.PlaceEval.evalPlace_deref_zeroFields
#print axioms Toy.PlaceEval.place_computation_not_free
#print axioms Toy.PlaceEval.erasePlaceMention_refinesPP
#print axioms Toy.PlaceEval.erasePlaceMention_equivPP_of_evalPlace_reachable
#print axioms Toy.PlaceEval.erasePlaceMention_equivPP_iff_slots
#print axioms Toy.PlaceEval.erasePlaceMention_equivPP_despite_reachable_failure
#print axioms Toy.PlaceEval.ubCheck_after_erasePlaceMention_misses_place_ub
#print axioms Toy.PlaceEval.ubCheck_after_eraseMarkers_misses_stale_read
#print axioms Toy.PlaceEval.ubFree_of_ubFree_erasePlaceMention_of_evalPlace_reachable
#print axioms Toy.PlaceEval.evalInt_copy_eq_none_iff
#print axioms Toy.PlaceEval.switchToGoto_refinesPP
#print axioms Toy.PlaceEval.switchToGoto_equivPP_of_operand_reachable
#print axioms Toy.PlaceEval.switchToGoto_equivPP_iff_slots
#print axioms Toy.PlaceEval.ref_eval_eq_none_iff
#print axioms Toy.PlaceEval.refToRaw_refinesPP
#print axioms Toy.PlaceEval.raw_ref_rewrites_not_equivalences
#print axioms Toy.PlaceEval.eraseMarkers_refinesPP_of_noProvConst
#print axioms Toy.PlaceEval.eraseMarkers_slots_refinesAcross_fresh_of_noProvConst
#print axioms Toy.PlaceEval.eraseMarkers_sharedSlot_lowering_mismatch
#print axioms Toy.PlaceEval.eraseMarkers_fresh_equivPP_of_alignPos_of_noAddrObs_of_ubFree
#print axioms Toy.PlaceEval.eraseMarkers_fresh_equivPP_without_ubFree_or_noAddrObs
#print axioms Toy.PlaceEval.eraseMarkers_fresh_equivPP_without_alignPos
