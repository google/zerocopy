From simuliris.simulation Require Import slsls lifting gen_log_rel.
From simuliris.simulang Require Import proofmode tactics.
From simuliris.simulang Require Import gen_refl pure_refl wf log_rel_structural behavior.
From simuliris.simulang.na_inv Require Export inv.

(** * Reflexivity theorem for the heap bijection value relation *)

Section refl.
  Context `{naGS Σ}.

  Theorem na_log_rel_structural : log_rel_structural heapbij.loc_rel (λ π, na_locs π ∅) simulang_wf.
  Proof.
    intros e_t e_s ?? Hwf Hs. iIntros "IH".
    destruct e_s, e_t => //; simpl in Hs; simplify_eq.
    all: try by iApply pure_log_rel_structural; unfold loc_rel_func_law, loc_rel_inj_law, loc_rel_offset_law; eauto using heapbij_loc_func, heapbij_loc_inj, heapbij_loc_shift, sim_bij_contains_globalbij.
    all: try iDestruct "IH" as "[IH IH1]".
    all: try iDestruct "IH1" as "[IH1 IH2]".
    all: try iDestruct "IH2" as "[IH2 IH3]".
    - (* Call *)
      iApply (log_rel_call with "IH IH1").
      by iIntros (???).
    - (* Fork *)
      iApply (log_rel_fork with "IH").
      iIntros (????) "Ht Hsim Hfork". by iApply (sim_bij_fork with "Ht Hsim").
    - (* AllocN *)
      iApply (log_rel_allocN with "IH IH1").
      iIntros (n ?????) "Ht Hv Hcont".
      target_alloc l_t as "Hl_t" "Ha_t"; first done.
      source_alloc l_s as "Hl_s" "Ha_s"; first done.
      iApply (sim_bij_insertN with "Ha_t Ha_s Hl_t Hl_s [Hv]"); [lia | by rewrite length_replicate.. | | ].
      { iDestruct "Hv" as "#Hv".
        rewrite big_sepL2_replicate_l; last by rewrite length_replicate.
        generalize (Z.to_nat n) => n'.
        iInduction n' as [] "IHn"; cbn; first done. iFrame "Hv IHn".
      }
      by iApply "Hcont".
    - (* FreeN *)
      iApply (log_rel_freeN with "IH IH1").
      iIntros (??????) "Ht Hv Hcont". by iApply (sim_bij_free with "Hv Ht").
    - (* Load *)
      iApply (log_rel_load with "IH").
      iIntros (????) "Ht Hv Hcont". iApply (sim_bij_load with "Hv Ht"); [done..|].
      iIntros (??) "H ?". by iApply ("Hcont" with "[$]").
    - (* Store *)
      iApply (log_rel_store with "IH IH1").
      iIntros (??????) "Ht Hl Hv Hcont".
      match goal with | o : order |- _ => destruct o => // end.
      + by iApply (sim_bij_store_sc_empty with "Hl Ht Hv").
      + by iApply (sim_bij_store_na with "Hl Ht Hv").
  Qed.

  Corollary log_rel_refl e :
    expr_wf e →
    ⊢ log_rel e e.
  Proof.
    intros ?. iApply gen_log_rel_refl; first by apply na_log_rel_structural. done.
  Qed.

  Corollary log_rel_ctx C e_t e_s :
    ctx_wf C →
    log_rel e_t e_s -∗ log_rel (fill_ctx C e_t) (fill_ctx C e_s).
  Proof.
    intros ?. iApply gen_log_rel_ctx; first by apply na_log_rel_structural. done.
  Qed.

  Lemma log_rel_func x e_t e_s :
    free_vars e_t ∪ free_vars e_s ⊆ {[x]} →
    log_rel e_t e_s -∗
    func_rel (x, e_t) (x, e_s).
  Proof.
    apply gen_log_rel_func.
    iIntros (v_t v_s π). eauto.
  Qed.

End refl.
