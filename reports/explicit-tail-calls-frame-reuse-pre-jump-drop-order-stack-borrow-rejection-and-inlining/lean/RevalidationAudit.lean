import ToyTailCall

/-!
Axiom audit of the 22 main theorems (outside the library target).
Run from `lean/` after `lake build`: `lake env lean RevalidationAudit.lean`.
Every output line must list at most `propext`, `Classical.choice` and `Quot.sound`.
-/

#print axioms Toy.TailCall.frameReuse_observes_iff_preJump_of_noStackBorrow
#print axioms Toy.TailCall.frameReuse_observes_of_preJump_of_ne_stackOverflow_of_noStackBorrow
#print axioms Toy.TailCall.countUp_frameReuse_runsTo
#print axioms Toy.TailCall.countUp_preJump_runsTo
#print axioms Toy.TailCall.countUp_callReturn_runsTo
#print axioms Toy.TailCall.callFree_frameReuse_maxDepth_of_entryOk
#print axioms Toy.TailCall.callFree_preJump_maxDepth_of_entryOk
#print axioms Toy.TailCall.mem_pendingDrops_iff
#print axioms Toy.TailCall.pendingDrops_pairwise_gt
#print axioms Toy.TailCall.noStackBorrow_of_escapeCheckAccepts
#print axioms Toy.TailCall.correctedCallSiteSplice_preserves_frameReuse_of_ne_ub_of_ne_stackOverflow
#print axioms Toy.TailCall.correctedTailSiteSplice_mutualRec_runsTo
#print axioms Toy.TailCall.correctedTailSiteSplice_mutualRec_overflows_any_slack
#print axioms Toy.TailCall.dropList_clears_pending_of_ne_abort
#print axioms Toy.TailCall.frameReuse_tailCall_finalizes_then_push_of_noPanic
#print axioms Toy.TailCall.frameReuse_finalization_unique_panic_drops_rest_then_unwinds
#print axioms Toy.TailCall.Layout.reuseSound_callerPops_iff
#print axioms Toy.TailCall.Layout.reuseSound_calleePops_iff
#print axioms Toy.TailCall.Layout.reuseSound_of_sigCheckFull
#print axioms Toy.TailCall.Layout.reuseSoundAt_zero_iff
#print axioms Toy.TailCall.Layout.reuseSoundAt_calleePops_iff
#print axioms Toy.TailCall.Layout.reuseSoundAt_callerPops_iff
