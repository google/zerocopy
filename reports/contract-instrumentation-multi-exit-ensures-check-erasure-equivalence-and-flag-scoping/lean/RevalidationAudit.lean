import ToyContracts

/-! Manual axiom audit for the result theorem of every card. Not part of the library target:
run `lake env lean RevalidationAudit.lean` from this directory after `lake build`. Each printed
list must contain at most `propext`, `Classical.choice` and `Quot.sound`. -/

-- R1
#print axioms Toy.Contracts.run_instr_allExits_eq_instrObs_of_lowered
-- R2
#print axioms Toy.Contracts.req_and_ens_of_halts_ret_instr_allExits_lower
-- R4
#print axioms Toy.Contracts.halts_lower_iff_of_jumpsInRange
-- R5
#print axioms Toy.Contracts.cex_tailOnly_misses_early_return
-- R6
#print axioms Toy.Contracts.cex_tailOnly_misses_try_error_after_lowering
-- R7
#print axioms Toy.Contracts.cex_instr_before_lower_misses_try
-- R8
#print axioms Toy.Contracts.erase_instr_eq_of_noChecks
-- R24
#print axioms Toy.Contracts.instr_allExits_obsEq_self_iff_ensOnReturnsAt_of_lowered_of_req
-- R9
#print axioms Toy.Contracts.erasure_obsEq_iff_ensOnReturnsAt_of_lowered_of_noChecks_of_req
-- R10
#print axioms Toy.Contracts.erasure_obsEq_onReq_iff_staticObligation_of_lowered_of_noChecks
-- R11
#print axioms Toy.Contracts.not_haltsEqAt_erase_instr_of_req_false
-- R12
#print axioms Toy.Contracts.run_assumeErase_eq_ite_req
-- R13
#print axioms Toy.Contracts.instr_allExits_ubRefinesAt_assumeErase_of_noChecks_of_staticObligationAt
-- R14
#print axioms Toy.Contracts.not_assumeErase_ubRefinesAt_instr_of_req_false
-- R15
#print axioms Toy.Contracts.callRun_eq_ite_governingFlag_of_lowered
-- R16
#print axioms Toy.Contracts.detects_iff_governingFlag_of_lowered_of_noChecks_of_violation
-- R17
#print axioms Toy.Contracts.callRun_eq_run_of_not_violation
-- R18
#print axioms Toy.Contracts.cex_same_flags_detection_depends_on_placement
-- R19
#print axioms Toy.Contracts.cex_calleeSide_atInstantiation_definingFlag_on_undetected
-- R20
#print axioms Toy.Contracts.runtimeValue_iff_req_and_ens_of_lowered_of_noChecks_of_ctfeSkipConst
-- R21
#print axioms Toy.Contracts.runtimeValue_iff_staticObligationAt_of_lowered_of_noChecks_of_req_of_ctfeSkipConst
-- R22
#print axioms Toy.Contracts.cex_ctfeSkip_requires_violation
-- R23
#print axioms Toy.Contracts.cex_ctfeSkip_ensures_violation
