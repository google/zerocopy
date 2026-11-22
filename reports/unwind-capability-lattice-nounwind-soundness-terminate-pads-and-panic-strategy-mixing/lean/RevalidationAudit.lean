import ToyUnwindCap

/-!
Axiom audit of the 25 main theorems (outside the library target).
Run from `lean/` after `lake build`: `lake env lean RevalidationAudit.lean`.
Every output line must list at most `propext`, `Classical.choice` and `Quot.sound`.
-/

#print axioms Toy.UnwindCap.noUB_of_enforced_of_foreignCovered_of_siteAgreement
#print axioms Toy.UnwindCap.foreignCovered_std_of_foreignHonest_of_foreignNotGlue
#print axioms Toy.UnwindCap.precForeignSound_iff
#print axioms Toy.UnwindCap.std_and_abiFirst_foreignSound_but_differ
#print axioms Toy.UnwindCap.abortAllCanUnwind_not_foreignSound
#print axioms Toy.UnwindCap.abortAll_progAbortImportPlain_ub
#print axioms Toy.UnwindCap.insertPads_enforced
#print axioms Toy.UnwindCap.insertPads_body
#print axioms Toy.UnwindCap.padStmt_call
#print axioms Toy.UnwindCap.padStmt_raise
#print axioms Toy.UnwindCap.insertPads_foreignCovered
#print axioms Toy.UnwindCap.insertPads_siteAgreement
#print axioms Toy.UnwindCap.exec_insertPads_of_exec_of_ne_ub
#print axioms Toy.UnwindCap.noUB_insertPads_of_foreignCovered_of_siteAgreement
#print axioms Toy.UnwindCap.ub_of_selfNonUnwinding_of_unguarded_head_call_of_callee_unwinds
#print axioms Toy.UnwindCap.noUB_std_of_linkOK_of_enforced_of_foreignHonest_of_foreignNotGlue_of_glueAgreement
#print axioms Toy.UnwindCap.glueSiteSound_iff
#print axioms Toy.UnwindCap.glueSiteSound_iff_panicInDrop
#print axioms Toy.UnwindCap.compRet_eq_specRet_of_conforms
#print axioms Toy.UnwindCap.compUnwind_eq_specUnwind_iff_obligationsFull_of_noReachedNoneTerminate
#print axioms Toy.UnwindCap.compUnwind_eq_specUnwind_of_obligationsFull
#print axioms Toy.UnwindCap.robust_iff_shielded
#print axioms Toy.UnwindCap.robust_of_terminateShielded
#print axioms Toy.UnwindCap.withPads_exec_iff_of_padsNone_nonunwinding_of_enforcedAt_of_siteAgreementAt
#print axioms Toy.UnwindCap.withPads_exec_iff_of_padsNone_obligationFreeRaises_of_obligationCalleesNonUnwinding
