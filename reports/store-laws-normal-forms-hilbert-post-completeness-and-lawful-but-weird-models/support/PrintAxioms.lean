import Toy

/-! Axiom check for the main results of the package. Run from `lean/`:
`lake env lean ../support/PrintAxioms.lean`. -/

#print axioms Toy.StoreLaws.getGet_of_getPut_of_putGet
#print axioms Toy.StoreLaws.getPut_putGet_putPut_independent_bool
#print axioms Toy.StoreLaws.getGet_not_entailed_by_pairs_with_putPut_bool
#print axioms Toy.StoreLaws.entailsBool_iff
#print axioms Toy.StoreLaws.derivable_nf_of_getPut_putGet_putPut
#print axioms Toy.StoreLaws.canon_eq_of_derivable
#print axioms Toy.StoreLaws.derivable_iff_obsEq_of_getPut_putGet_putPut
#print axioms Toy.StoreLaws.interp_eq_fromObs_run_of_getPut_putGet_putPut
#print axioms Toy.StoreLaws.interp_eq_of_obsEq_of_getPut_putGet_putPut
#print axioms Toy.StoreLaws.fromObs_isHom_unique_of_getPut_putGet_putPut
#print axioms Toy.StoreLaws.getPut_putGet_putPut_iff_exists_surjective_isHom
#print axioms Toy.StoreLaws.valueOnly_lawful_not_faithful
#print axioms Toy.StoreLaws.unitModel_lawful_not_faithful
#print axioms Toy.StoreLaws.forall_interp_eq_iff_obsEq_of_getPut_putGet_putPut_of_nontrivial
#print axioms Toy.StoreLaws.extDerivable_total_of_not_derivable
#print axioms Toy.StoreLaws.writeLog_via_distinguishes_obsEq
#print axioms Toy.StoreLaws.writeLog_strict_profile_bool
#print axioms Toy.StoreLaws.readCounter_strict_profile_bool
#print axioms Toy.StoreLaws.inertHidden_interp_eq
#print axioms Toy.StoreLaws.derivable_lawsExcept_getGet_iff
#print axioms Toy.StoreLaws.dropGetPut_loses_nf
#print axioms Toy.StoreLaws.dropPutGet_loses_nf
#print axioms Toy.StoreLaws.dropPutPut_loses_nf
