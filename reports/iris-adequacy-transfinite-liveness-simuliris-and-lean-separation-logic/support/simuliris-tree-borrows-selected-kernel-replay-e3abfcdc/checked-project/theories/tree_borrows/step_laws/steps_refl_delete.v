From iris.proofmode Require Export proofmode.
From iris.base_logic.lib Require Import ghost_map.
From simuliris.base_logic Require Export gen_sim_prog.
From simuliris.simulation Require Export slsls.
From simuliris.simulation Require Import lifting.
From simuliris.tree_borrows Require Import tkmap_view.
From simuliris.tree_borrows Require Export defs class_instances.
From simuliris.tree_borrows Require Import wishlist steps_progress steps_inv.
From simuliris.tree_borrows Require Import logical_state inv_accessors.
From simuliris.tree_borrows.trees_equal Require Import trees_equal_base random_lemmas.
From simuliris.tree_borrows.trees_equal Require Import trees_equal_more_access trees_equal_dealloc trees_equal_preserved_by_access.

Section lifting.
Context `{!sborGS Σ}.
Implicit Types P Q : iProp Σ.
Implicit Types Φ : expr → expr → iProp Σ.
Implicit Types σ σ_s σ_t : state.
Implicit Types r r_s r_t : result.
Implicit Types l : loc.
Implicit Types f : fname.

Lemma sim_free_public sz sz' l_t l_s bor_t bor_s Φ π :
  rrel (PlaceR l_t bor_t sz') (PlaceR l_s bor_s sz) -∗
  #[☠] ⪯{π} #[☠] [{ Φ }] -∗
  Free (Place l_t bor_t sz') ⪯{π} Free (Place l_s bor_s sz) [{ Φ }].
Proof.
  iIntros "[#Hscrel ->] Hsim".
  iPoseProof (sc_rel_ptr_source with "Hscrel") as "[%Heq Hpub]". injection Heq as [= -> ->].
  iClear "Hscrel".
  iApply sim_lift_base_step_both. iIntros (P_t P_s σ_t σ_s ??) "[(HP_t & HP_s & Hbor) %Hsafe]".
  iModIntro.
  destruct Hsafe as [Hpool Hsafe].
  specialize (pool_safe_implies Hsafe Hpool) as (trs' & Hdealloc_s & Hpos & Hcontain & Happly_s).
  iPoseProof (bor_interp_get_pure with "Hbor") as "%Hp".
  destruct Hp as (Hsst_eq & Hsnp_eq & Hsnc_eq & Hscs_eq & Hwf_s & Hwf_t & Hdom_eq).
  odestruct (apply_within_trees_equal _ _ _ _ _ _ _ _ Happly_s) as (trt' & Happly_t & Heq'); [|exact Hsst_eq|].
  { intros ttr1 ttr1' ttr2 H1 H2 Httr1 Httr1' Httr2.
    assert (tree_contains bor_s ttr1) as Hcont' by rewrite /trees_contain /trees_at_block Httr1 // in Hcontain.
    edestruct tree_equal_allows_more_deallocation as (ttr2'&Httr2'). 9: exact H2.
    1,4,6,9: by eapply Hwf_s. 1-5: rewrite ?Hscs_eq; by eapply Hwf_t.
    1: eapply mk_is_Some, H1.
    exists ttr2'; split; first done.
    eapply tree_equal_memory_deallocate. 7-10: done.
    1,3,4: by eapply Hwf_s. 3: rewrite Hscs_eq. all: by eapply Hwf_t. }
  iSplitR.
  { iPureIntro. do 3 eexists. eapply dealloc_base_step'; try done.
    - setoid_rewrite <- elem_of_dom. setoid_rewrite <- elem_of_dom in Hdealloc_s. rewrite -Hdom_eq //.
    - rewrite - trees_equal_same_tags //.
    - rewrite -Hscs_eq. eapply Happly_t.
  }
  iIntros (e_t' efs_t σ_t') "%Hhead_t".
  specialize (head_free_inv _ _ _ _ _ _ _ _ Hhead_t) as (α'0 & Hdealloc' & _ & Hcontain' & Hα'0 & -> & -> & ->).
  assert (α'0 = trt') as ->.
  { rewrite -Hscs_eq Happly_t in Hα'0. by injection Hα'0 as <-. }
  iModIntro.
  pose (σ_s' := (mkState (free_mem l_s sz σ_s.(shp)) (delete l_s.1 trs') σ_s.(scs) σ_s.(snp) σ_s.(snc))).
  assert (Hhead_s : base_step P_s (Free (Place l_s bor_s sz)) σ_s (ValR [☠]%S) σ_s' []).
  { eapply dealloc_base_step'; eauto. }
  iExists (#[☠])%E, [], σ_s'. iSplitR; first done.
  iFrame "HP_t HP_s".
  iSplitR "Hsim"; first last. { iSplitL; done. }

  iDestruct "Hbor" as "(%M_call & %M_tag & %M_t & %M_s & (Hc & Htag_auth & Htag_t_auth & Htag_s_auth) & Htainted & Hpub_cid & #Hsrel & %Hcall_interp & %Htag_interp & _ & _)".
  iPoseProof (tkmap_lookup with "Htag_auth Hpub") as "%Hpub".

  (* we keep the base_step hypotheses to use the [base_step_wf] lemma below *)
  (* re-establish the invariants *)
  iExists M_call, M_tag, M_t, M_s.
  iFrame "Hc Htag_auth Htag_t_auth Htag_s_auth".
  iSplitL "Htainted"; last iSplitL "Hpub_cid"; last iSplit; last iSplit; last iSplit; last iSplit.
  - iDestruct "Htainted" as "(%M&Ht1&Ht2)". iExists M. iFrame "Ht1".
    iIntros (t' l' Htl'). iDestruct ("Ht2" $! t' l' Htl') as "($&%Ht2)". iPureIntro.
    destruct Ht2 as (Hlt&Ht2); split. 1: simpl; lia.
    rewrite /=. destruct (decide (l'.1 = l_s.1)) as [Heq|Hf].
    + rewrite Heq lookup_delete_eq //.
    + rewrite lookup_delete_ne //. eapply apply_within_trees_lookup in Happly_s as (_&H2). rewrite -H2 //.
  - (* pub cid *)
    iApply (pub_cid_interp_preserve_sub with "Hpub_cid"); simpl; done.
  - (* re-establish the state relation *)
    iDestruct "Hsrel" as "(_ & _ & _ & _ & _ & Hsrel)".
    iSplitR. { iPureIntro. simpl. apply free_mem_dom. done. }
    simpl. iSplit.
    1: iPureIntro; by eapply trees_equal_delete.
    do 3 (iSplit; first done).
    iIntros (l (sc & Hsome)).
    destruct (free_mem_lookup_case l l_s sz σ_t.(shp)) as [[Hi Hfreet] | (i & _ & -> & ?)]; last congruence.
    rewrite Hfreet in Hsome. iDestruct ("Hsrel" $! l with "[]") as "[Hpubl | Hprivl]"; first by eauto.
    + iLeft. iIntros (sc_t Hsc_t). simpl in *.
      rewrite Hfreet in Hsc_t. simplify_eq.
      iDestruct ("Hpubl" $! sc Hsome) as (sc_s) "[%Hsc_s Hscr]".
      iExists sc_s. iSplitR; last done.
      iPureIntro.
      destruct (free_mem_lookup_case l l_s sz σ_s.(shp)) as [[_ Hfrees] | (i' & Hi' & -> & _)].
      2: { specialize (Hi i' Hi'). congruence. }
      rewrite Hfrees Hsc_s. done.
    + iRight. done.
  - (* re-establish the call set interpretation *)
    iPureIntro.
    destruct Hcall_interp as (Hcall_interp&Hcc2). split; last first.
    1: done.
    pose proof Hcall_interp as Hcall_interp_old.
    intros c M' Hc. simpl. specialize (Hcall_interp _ _ Hc) as (Hcs & HM'). split; first done.
    intros t L HL. specialize (HM' _ _ HL) as (Hvalid & HM'). split; first done.
    intros l b Hl. specialize (HM' l b Hl).
    eapply tag_protected_preserved_by_delete. 5: apply HM'.
    1: apply Hwf_t. 1: eassumption. 1: apply Hcs.
    intros it -> Hll Hlu (ak&Hak&(vx&Hhl)) Hprot Hinit.
    rewrite /memory_deallocate in Happly_t.
    rewrite apply_within_trees_bind in Happly_t. eapply bind_Some in Happly_t as (trsmid&Haccess_t&Hcheck_t).
    rewrite Hscs_eq in Haccess_t.
    destruct Htag_interp as (Ht1&_). destruct (Ht1 _ _ Hak) as (Ht1'&Ht2&Htlocal&Ht3&Ht4&Ht5).
    specialize (Ht3 _ _ Hhl) as Ht3'.
    eapply (protected_active_loc_does_not_survive_write_access _ (mkState σ_t.(shp) trsmid σ_s.(scs) σ_t.(snp) σ_t.(snc))); simpl.
    1: exact Haccess_t. 1: done. 1: by rewrite Hscs_eq. 1: done. 1: done.
    2: done. 2: done. 2: exact Hpub.
    + destruct Ht3' as (_&Hhp).
      2: { destruct l as [lp1 lp2]. simpl in Hll|-*. subst lp1. assert (exists m, l_s.2 + m = lp2) as (m&Hm).
           { exists (lp2 - l_s.2). lia. }
           specialize (Hdealloc' m). rewrite /= /shift_loc /= Hm in Hdealloc'.
           eapply mk_is_Some, Hdealloc' in Hhp. lia. }
      exists it. rewrite Hll. split; first eapply Hlu. done.
    + eexists. split; first exact Hak. split; first eapply mk_is_Some, Hhl.
      do 3 eexists. split. 1: done.
      eexists. split; first exact Hc. eexists. split; first done. done.
    + intros ??? HH1 HH2. destruct (Ht1 _ _ HH1) as (_&_&_&HHt1&_&_). by eapply HHt1.
  - (* re-establish the tag interpretation *)
    destruct Htag_interp as (Htag_interp & Hdom_t & Hdom_s & Hunq1 & Hunq2).
    iPureIntro. split_and!; [ | done..].
    intros t tk Ht. simpl. specialize (Htag_interp _ _ Ht) as (? & ? & Hlocal & Hcontrol_t & Hcontrol_s & Hag).
    split_and!; [done | done | | | | done].
    + done.
    + intros l sc_t Hsc_t%Hcontrol_t. rewrite Hscs_eq in Happly_t.
      eapply loc_controlled_dealloc_update; [ apply Happly_t | done | done | | done ].
      intros -> _. rewrite Hpub in Ht. congruence.
    + intros l sc_s Hsc_s%Hcontrol_s.
      eapply loc_controlled_dealloc_update; [apply Happly_s | done | done | | done].
      intros -> _. rewrite Hpub in Ht. congruence.
  - iPureIntro. by eapply base_step_wf.
  - iPureIntro. by eapply base_step_wf.
Qed.

End lifting.


