From simuliris.simulation Require Import slsls lifting.
From simuliris.stacked_borrows Require Import proofmode tactics.
From simuliris.stacked_borrows Require Import parallel_subst primitive_laws wf.

Section log_rel_structural.
  Context `{!sborGS Σ}.
  Context (expr_head_wf : expr_head → Prop).

  (** [log_rel_structural] is the main theorem one wants to prove. It
  implies the reflexivity theorem for expressions, evaluation contexts
  and general contexts.

  The theorem says that for any expressions with equal heads and related
  immediate subexpressions, the expressions themselves must also be related.
   *)
  Definition log_rel_structural : Prop := (∀ e_t e_s,
     let head_t := expr_split_head e_t in
     let head_s := expr_split_head e_s in
     expr_head_wf head_s.1 →
     head_s.1 = head_t.1 →
     ([∗list] e_t';e_s' ∈ head_t.2; head_s.2, log_rel e_t' e_s') -∗
     log_rel e_t e_s).


  Theorem log_rel_refl e :
    log_rel_structural →
    gen_expr_wf expr_head_wf e →
    ⊢ log_rel e e.
  Proof.
    intros He Hwf.
    iInduction e as [ ] "IH" using expr_ind forall (Hwf); destruct Hwf; iApply He; try done; simpl.
    all: try iDestruct ("IH" with "[%]") as "$".
    all: try iDestruct ("IH1" with "[%]") as "$".
    all: try naive_solver.
    (* [Case] left. *)
    iApply big_sepL2_forall.
    iSplitR; first done. iIntros (i e1 e2 Hs1 Hs2). simplify_eq.
    iApply (big_sepL_lookup with "IH"); first done.
    iPureIntro. match goal with H : _ ∧ Forall _ _ |- _ => destruct H as [_ Hexprs_wf] end.
    eapply Forall_lookup_1; last done.
    move : Hexprs_wf. rewrite Forall_fmap. done.
  Qed.

  Theorem log_rel_ectx K e_t e_s :
    log_rel_structural →
    gen_ectx_wf expr_head_wf K →
    log_rel e_t e_s -∗
    log_rel (fill K e_t) (fill K e_s).
  Proof.
    intros He Hwf. iInduction (K) as [ | Ki K] "IH" using rev_ind; first by eauto.
    iIntros "Hrel".
    rewrite ->gen_ectx_wf_snoc in Hwf. destruct Hwf as [Kwf [Hewf Hiwf]].
    iSpecialize ("IH" with "[//] Hrel").
    rewrite !fill_app /=.
    destruct Ki; simpl; iApply He => //=; iFrame "IH".
    all: move: Hiwf; rewrite /= ?Forall_cons ?Forall_nil => Hiwf.
    all: repeat iSplit; try done.
    all: try (iApply log_rel_refl; [naive_solver|]).
    all: try naive_solver.
    iApply big_sepL2_forall. iSplitR; first done.
    iIntros (i e1 e2 ? ?); simplify_eq.
    iApply log_rel_refl; first done.
    eapply Forall_lookup_1; done.
  Qed.

  Theorem log_rel_ctx C e_t e_s :
    log_rel_structural →
    gen_ctx_wf expr_head_wf C →
    log_rel e_t e_s -∗
    log_rel (fill_ctx C e_t) (fill_ctx C e_s).
  Proof.
    intros He Hwf. iInduction (C) as [ | Ci C] "IH" using rev_ind; first by eauto.
    iIntros "Hrel".
    rewrite ->gen_ctx_wf_snoc in Hwf. destruct Hwf as [Kwf [Hewf Hiwf]].
    iSpecialize ("IH" with "[//] Hrel").
    rewrite !fill_ctx_app /=.
    destruct Ci; simpl; iApply He => //=; iFrame "IH".
    all: move: Hiwf; rewrite /= ?Forall_cons ?Forall_nil => Hiwf.
    all: repeat iSplit; try done.
    all: try (iApply log_rel_refl; [done|]).
    all: try naive_solver.

    all: (iApply big_sepL2_forall; iSplitR; first done).
    all: iIntros (i e1 e2 ? ?); simplify_eq.
    all: iApply log_rel_refl; first done.
    all: eapply Forall_lookup_1; last done.
    - done.
    - move: Hiwf. rewrite Forall_app. naive_solver.
    - move: Hiwf. rewrite Forall_app. naive_solver.
  Qed.

  Corollary sim_refl π m1 m2 e Φ :
    dom m1 = dom m2 →
    free_vars e ⊆ dom m1 →
    log_rel_structural →
    gen_expr_wf expr_head_wf e →
    subst_map_rel rrel (dom m1) (map_zip m1 m2) -∗
    (∀ v_t v_s, rrel v_t v_s -∗ Φ (of_result v_t) (of_result v_s)) -∗
    subst_map m1 e ⪯{π} subst_map m2 e [{ Φ }].
  Proof.
    iIntros (Hdom Hfree ??) "Hrel HΦ".
    iApply (sim_expr_wand _ _ _ _ π with "[Hrel]").
    - iPoseProof log_rel_refl as "#Hlog"; [done..|].
      rewrite /gen_log_rel.
      iSpecialize ("Hlog" $! _ (map_zip m1 m2)).
      setoid_rewrite fst_map_zip.
      2: { move => ?. by rewrite -!elem_of_dom Hdom. }
      setoid_rewrite snd_map_zip.
      2: { move => ?. by rewrite -!elem_of_dom Hdom. }
      iApply ("Hlog" with "[Hrel]"); last done.
      iApply (subst_map_rel_weaken with "Hrel"). set_solver.
    - iIntros (e_t e_s) "(%v_t & %v_s & -> & -> & [_ Hv])". by iApply "HΦ".
  Qed.

End log_rel_structural.
