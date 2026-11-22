import Toy

/-!
Axiom audit for the toy model. Run with
`lake env lean Audit.lean` after `lake build`.
-/
open Toy

-- BI algebra and later modality
#print axioms SProp.imp_adj
#print axioms SProp.wand_adj
#print axioms SProp.sep_assoc
#print axioms SProp.later_intro
#print axioms SProp.later_and
#print axioms SProp.later_sep
#print axioms SProp.later_wand
#print axioms SProp.later_bot_not_bot
#print axioms SProp.later_ex_of_inhabited
#print axioms SProp.loeb
#print axioms SProp.loeb_internal
#print axioms SProp.later_contractive
#print axioms SProp.guarded_fixpoint_unique
#print axioms SProp.gfix_unfold
#print axioms sep_ne_and

-- Indexed BI algebra (hyperdoctrine) laws
#print axioms Pred.reidx_id
#print axioms Pred.reidx_comp
#print axioms Pred.reidx_and
#print axioms Pred.reidx_imp
#print axioms Pred.reidx_sep
#print axioms Pred.reidx_wand
#print axioms Pred.reidx_later
#print axioms Pred.ex_adj
#print axioms Pred.all_adj
#print axioms Pred.beck_chevalley_ex
#print axioms Pred.beck_chevalley_all
#print axioms Pred.frobenius_and
#print axioms Pred.frobenius_sep
#print axioms Pred.lawvere_eq

-- Object language: substitution lemma and soundness of the equational theory
#print axioms Tm.eval_sub
#print axioms Sub.den_comp
#print axioms Conv.sound

-- (a) Automatic substitution and binder congruence
#print axioms substP_comp
#print axioms substP_congr
#print axioms subst1_congr
#print axioms substP_forallT
#print axioms substP_existsT
#print axioms substP_wp
#print axioms wp_congr
#print axioms wp_beta
#print axioms wp_ret_lam_congr
#print axioms wp_bind_body_congr
#print axioms wpSem_ret
#print axioms wpSem_bind
#print axioms wpSem_tick
#print axioms wpSem_frame
#print axioms wpSem_wand

-- (b) Operational contrast
#print axioms wpo_bind
#print axioms appCtx_laws
#print axioms wpo_bind_app
#print axioms lamCtx_not_ctxLaws
#print axioms wpo_bind_fails_under_lam
#print axioms operational_predicate_distinguishes
#print axioms lamCtx_conv
#print axioms denotational_predicate_cannot_distinguish
#print axioms wp_agrees_under_lam

-- Soundness half of adequacy
#print axioms Step.sound
#print axioms Steps.sound
#print axioms Steps.ret_sound
