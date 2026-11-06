From simuliris.simulation Require Import slsls lifting gen_log_rel.
From simuliris.simulang Require Import proofmode tactics.
From simuliris.simulang Require Import primitive_laws wf gen_val_rel.

Section log_rel_structural.
  Context `{!sheapGS Σ} `{!sheapInv Σ}.
  Context (loc_rel : loc → loc → iProp Σ).
  Context (thread_own : thread_id → iProp Σ).
  Context (expr_head_wf : expr_head → Prop).
  Local Notation val_rel := (gen_val_rel loc_rel).
  Local Notation log_rel := (gen_log_rel val_rel thread_own).

  (** [log_rel_structural] is the main theorem one wants to prove. It
  implies the reflexivity theorem for expressions, evaluation contexts
  and general contexts.

  The theorem says that for any expressions with equal heads and related
  immediate subexpressions, the expressions themselves must also be related.

  TODO: Make this a typeclass?
   *)
  Definition log_rel_structural : Prop := (∀ e_t e_s,
     let head_t := expr_split_head e_t in
     let head_s := expr_split_head e_s in
     expr_head_wf head_s.1 →
     head_s.1 = head_t.1 →
     ([∗list] e_t';e_s' ∈ head_t.2; head_s.2, log_rel e_t' e_s') -∗
     log_rel e_t e_s).

  Theorem gen_log_rel_refl e :
    log_rel_structural →
    gen_expr_wf expr_head_wf e →
    ⊢ log_rel e e.
  Proof.
    intros He Hwf.
    iInduction e as [ ] "IH" forall (Hwf); destruct Hwf; iApply He; try done; simpl.
    all: try iDestruct ("IH" with "[%]") as "$".
    all: try iDestruct ("IH1" with "[%]") as "$".
    all: try iDestruct ("IH2" with "[%]") as "$".
    all: naive_solver.
  Qed.

  Theorem gen_log_rel_ectx K e_t e_s :
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
    destruct Ki; simpl.
    all: iApply He => //=; iFrame "IH".
    all: move: Hiwf; rewrite /= ?Forall_cons ?Forall_nil => Hiwf.
    all: repeat iSplit; try done.
    all: iApply gen_log_rel_refl; [done|].
    all: naive_solver.
  Qed.

  Theorem gen_log_rel_ctx C e_t e_s :
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
    all: iApply gen_log_rel_refl; [done|].
    all: naive_solver.
  Qed.

  Corollary sim_refl' π m1 m2 e Φ :
    dom m1 = dom m2 →
    free_vars e ⊆ dom m1 →
    log_rel_structural →
    gen_expr_wf expr_head_wf e →
    subst_map_rel val_rel (free_vars e) (map_zip m1 m2) -∗
    thread_own π -∗
    (∀ v_t v_s, thread_own π -∗ val_rel v_t v_s -∗ Φ (Val v_t) (Val v_s)) -∗
    subst_map m1 e ⪯{π} subst_map m2 e [{ Φ }].
  Proof.
    iIntros (Hdom Hfree ??) "Hrel Ht HΦ".
    iApply (sim_expr_wand with "[Hrel Ht]").
    - iPoseProof gen_log_rel_refl as "#Hlog"; [done..|].
      rewrite /log_rel.
      iSpecialize ("Hlog" $! _ (map_zip m1 m2)).
      setoid_rewrite fst_map_zip.
      2: { move => ?. by rewrite -!elem_of_dom Hdom. }
      setoid_rewrite snd_map_zip.
      2: { move => ?. by rewrite -!elem_of_dom Hdom. }
      iApply ("Hlog" with "[Hrel] Ht").
      iApply (subst_map_rel_weaken with "Hrel"). set_solver.
    - iIntros (e_t e_s) "(%v_t & %v_s & -> & -> & Ht & Hv)". by iApply ("HΦ" with "Ht").
  Qed.

  Corollary sim_refl π m1 m2 e Φ :
    dom m1 = dom m2 →
    free_vars e ⊆ dom m1 →
    log_rel_structural →
    gen_expr_wf expr_head_wf e →
    subst_map_rel val_rel (dom m1) (map_zip m1 m2) -∗
    thread_own π -∗
    (∀ v_t v_s, thread_own π -∗ val_rel v_t v_s -∗ Φ (Val v_t) (Val v_s)) -∗
    subst_map m1 e ⪯{π} subst_map m2 e [{ Φ }].
  Proof. 
    iIntros (Hdom Hfree ??) "Hrel Ht HΦ".
    iApply (sim_refl' with "[Hrel] Ht"); [done | done | done | done | | done].
    iApply subst_map_rel_weaken; done.
  Qed.
End log_rel_structural.
