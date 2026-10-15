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
From simuliris.tree_borrows.trees_equal Require Import trees_equal_endcall_law trees_equal_endcall_law_2.

Section lifting.
Context `{!sborGS Σ}.
Implicit Types P Q : iProp Σ.
Implicit Types Φ : expr → expr → iProp Σ.
Implicit Types σ σ_s σ_t : state.
Implicit Types r r_s r_t : result.
Implicit Types l : loc.
Implicit Types f : fname.

(** EndCall *)

Lemma sim_endcall_own c π Φ :
  c @@ ∅ -∗ (* needs to be empty so we don't trip private locations *)
  #[☠] ⪯{π} #[☠] [{ Φ }] -∗
  EndCall #[ScCallId c] ⪯{π} EndCall #[ScCallId c] [{ Φ }].
Proof.
  iIntros "Hcall Hsim". iApply sim_lift_base_step_both.
  iIntros (P_t P_s σ_t σ_s T_s K_s) "((HP_t & HP_s & Hbor) & %Hpool & %Hsafe)".
  iModIntro.
  iPoseProof (bor_interp_get_pure with "Hbor") as "%Hp".
  destruct Hp as (Hstrs_eq & Hsnp_eq & Hsnc_eq & Hscs_eq & Hwf_s & Hwf_t & Hdom_eq).
  specialize (pool_safe_implies Hsafe Hpool) as (?&[= <-]&Hcall_in & trss' & Htrss).
  edestruct trees_equal_access_all_protected_initialized as (trst' & Htrst & Htrseq').
  13: exact Hstrs_eq. 7,9: rewrite Hscs_eq. 13: exact Htrss. 1,4,6,9,10: by eapply Hwf_s. 6: rewrite Hsnp_eq Hsnc_eq. 1-6: by eapply Hwf_t. 1: done.
  iSplit.
  { iPureIntro. do 3 eexists. eapply end_call_base_step. all: by rewrite -Hscs_eq. }
  iIntros (e_t' efs_t σ_t') "%Hhead".
  specialize (head_end_call_inv _ _ _ _ _ _ Hhead) as (? & H & Hcall_int & -> & -> & ->).
  rewrite -Hscs_eq Htrst in H; injection H as <-.
  iExists (#[ ☠]%V)%E, [], (mkState σ_s.(shp) trss' (σ_s.(scs) ∖ {[c]}) σ_s.(snp) σ_s.(snc)).
  iSplitR. { iPureIntro. by eapply end_call_base_step. }
  iSplitR "Hsim"; last (simpl; by iFrame).
  iDestruct "Hbor" as "(%M_call & %M_tag & %M_t & %M_s & (Hc & Htag_auth & Htag_t_auth & Htag_s_auth) & Htainted & Hpub_cid & #Hsrel & %Hcall_interp & %Htag_interp & _)".
  specialize (state_wf_cid_agree _ Hwf_s _ Hcall_in) as Hlt_s.
  iPoseProof (ghost_map_lookup with "Hc Hcall") as "%Hlookup".
  iMod (ghost_map_delete with "Hc Hcall") as "Hc". iModIntro. simpl. iFrame "HP_s HP_t".
  iExists (delete c M_call), M_tag, M_t, M_s. rewrite /bor_interp_inner. iFrame.
  iSplitL "Htainted".
  { iDestruct "Htainted" as "(%M&Ht1&Ht2)". iExists M. iFrame "Ht1".
    iIntros (t' l' Htl'). iDestruct ("Ht2" $! t' l' Htl') as "($&%Ht2)". iPureIntro.
    simpl.
    eapply disabled_tag_access_all_protected_initialized in Ht2. 3: done. 2: by eapply Hwf_s.
    eapply disabled_tag_remove_call. 9: exact Ht2. 8: done. 7: done.
    1-6: by eapply Hwf_s. }
  iSplitL "Hpub_cid".
  { iApply (pub_cid_interp_preserve_sub with "Hpub_cid"); simpl; [set_solver.. | done]. }
  iSplitL "Hsrel".
  { iDestruct "Hsrel" as "(_ & _ & _ & _ & _ & Hl)". rewrite /state_rel. simpl.
    iSplit; first done. iSplit.
    { iPureIntro. eapply trees_equal_remove_call. 16: done. 14-15: done. 1,3,5,7,9,11: by eapply Hwf_s. 1,2,4: by eapply Hwf_t. 1-3: rewrite ?Hsnc_eq ?Hsnp_eq ?Hscs_eq; by eapply Hwf_t. done. }
    do 3 (iSplit; first (iPureIntro; try done; by f_equal)).
    iIntros (l Hl). iDestruct ("Hl" $! l Hl) as "[Hpub|%Hpriv]".
    { iLeft. rewrite /pub_loc /=. iApply "Hpub". }
    { iRight. iPureIntro. destruct Hpriv as (t&tk&Htk&Hlu&Ht). exists t, tk. do 2 (split; first done).
      destruct Ht as [->|(c'&ae&->&M&HM&Hin)]; first by left. right.
      exists c', ae; split; first done. exists M. split; last done.
      rewrite lookup_delete_ne //. intros <-.
      rewrite Hlookup in HM. injection HM as <-.
      destruct Hin as (x&Hx&_). by rewrite lookup_empty in Hx. }
  }
  iSplit.
  { iPureIntro. eapply call_set_interp_remove; simpl. 5: exact Hwf_t. 1-4,6: done.
    rewrite -Hscs_eq //. }
  iSplit.
  { iPureIntro. split_and!. 2-5: by eapply Htag_interp.
    destruct Htag_interp as (H1&H2&H3&H4&H5).
    intros t tk Htk. simpl. destruct (H1 t tk Htk) as (Hval1&Hval2&Hlocal&Hlu1&Hlu2&Hagree).
    split_and!; try done. (*
    - intros ->. split; intros ??; eapply trees_access_all_protected_initialized_contains.
      2, 4: done.  all: by eapply Hlocal. *)
    - intros l sc Hlusc.
      specialize (Hlu1 l sc Hlusc).
      eapply loc_controlled_trees_access_all_protected_initialized. 8: exact Hlu1.
      2: rewrite -Hscs_eq; exact Htrst. 2-5: done. all: done.
    - intros l sc Hlusc.
      specialize (Hlu2 l sc Hlusc).
      eapply loc_controlled_trees_access_all_protected_initialized. 8: exact Hlu2.
      2: exact Htrss. 2-5: done. 1-2: done.
 }
  iSplit; iPureIntro.
  all: eapply endcall_step_wf_inner.
  all: try done; by rewrite -Hscs_eq.
Qed.

Lemma sim_endcall π Φ c c' :
  sc_rel (ScCallId c') (ScCallId c) -∗
  #[☠] ⪯{π} #[☠] [{ Φ }] -∗
  EndCall #[ScCallId c'] ⪯{π} EndCall #[ScCallId c] [{ Φ }].
Proof.
  iIntros "#[-> Hsc] Hsim". iApply sim_lift_base_step_both.
  iIntros (P_t P_s σ_t σ_s T_s K_s) "((HP_t & HP_s & Hbor) & %Hpool & %Hsafe)".
  iModIntro.
  iPoseProof (bor_interp_get_pure with "Hbor") as "%Hp".
  destruct Hp as (Hstrs_eq & Hsnp_eq & Hsnc_eq & Hscs_eq & Hwf_s & Hwf_t & Hdom_eq).
  specialize (pool_safe_implies Hsafe Hpool) as (?&[= <-]&Hcall_in & trss' & Htrss).
  edestruct trees_equal_access_all_protected_initialized as (trst' & Htrst & Htrseq').
  13: exact Hstrs_eq. 7,9: rewrite Hscs_eq. 13: exact Htrss. 1,4,6,9,10: by eapply Hwf_s. 6: rewrite Hsnp_eq Hsnc_eq. 1-6: by eapply Hwf_t. 1: done.
  iSplit.
  { iPureIntro. do 3 eexists. eapply end_call_base_step. all: by rewrite -Hscs_eq. }
  iIntros (e_t' efs_t σ_t') "%Hhead".
  specialize (head_end_call_inv _ _ _ _ _ _ Hhead) as (? & H & Hcall_int & -> & -> & ->).
  rewrite -Hscs_eq Htrst in H; injection H as <-.
  iExists (#[ ☠]%V)%E, [], (mkState σ_s.(shp) trss' (σ_s.(scs) ∖ {[c]}) σ_s.(snp) σ_s.(snc)).
  iSplitR. { iPureIntro. by eapply end_call_base_step. }
  iSplitR "Hsim"; last (simpl; by iFrame).
  iDestruct "Hbor" as "(%M_call & %M_tag & %M_t & %M_s & (Hc & Htag_auth & Htag_t_auth & Htag_s_auth) & Htainted & Hpub_cid & #Hsrel & %Hcall_interp & %Htag_interp & _)".
  specialize (state_wf_cid_agree _ Hwf_s _ Hcall_in) as Hlt_s.
  iPoseProof (pub_cid_endcall with "Hsc Hpub_cid") as "(Hcall & Hpub_cid)".
  1: done. 1: done. 1: by rewrite -Hsnc_eq.
  iPoseProof (ghost_map_lookup with "Hc Hcall") as "%Hlookup".
  iMod (ghost_map_delete with "Hc Hcall") as "Hc". iModIntro. simpl. iFrame "HP_s HP_t".
  iExists (delete c M_call), M_tag, M_t, M_s. rewrite /bor_interp_inner. iFrame.
  iSplitL "Htainted".
  { iDestruct "Htainted" as "(%M&Ht1&Ht2)". iExists M. iFrame "Ht1".
    iIntros (t' l' Htl'). iDestruct ("Ht2" $! t' l' Htl') as "($&%Ht2)". iPureIntro.
    simpl.
    eapply disabled_tag_access_all_protected_initialized in Ht2. 3: done. 2: by eapply Hwf_s.
    eapply disabled_tag_remove_call. 9: exact Ht2. 8: done. 7: done.
    1-6: by eapply Hwf_s. }
  iSplitL "Hsrel".
  { iDestruct "Hsrel" as "(_ & _ & _ & _ & _ & Hl)". rewrite /state_rel. simpl.
    iSplit; first done. iSplit.
    { iPureIntro. eapply trees_equal_remove_call. 16: done. 14-15: done. 1,3,5,7,9,11: by eapply Hwf_s. 1,2,4: by eapply Hwf_t. 1-3: rewrite ?Hsnc_eq ?Hsnp_eq ?Hscs_eq; by eapply Hwf_t. done. }
    do 3 (iSplit; first (iPureIntro; try done; by f_equal)).
    iIntros (l Hl). iDestruct ("Hl" $! l Hl) as "[Hpub|%Hpriv]".
    { iLeft. rewrite /pub_loc /=. iApply "Hpub". }
    { iRight. iPureIntro. destruct Hpriv as (t&tk&Htk&Hlu&Ht). exists t, tk. do 2 (split; first done).
      destruct Ht as [->|(c'&ae&->&M&HM&Hin)]; first by left. right.
      exists c', ae; split; first done. exists M. split; last done.
      rewrite lookup_delete_ne //. intros <-.
      rewrite Hlookup in HM. injection HM as <-.
      destruct Hin as (x&Hx&_). by rewrite lookup_empty in Hx. }
  }
  iSplit.
  { iPureIntro. eapply call_set_interp_remove; simpl. 5: exact Hwf_t. 1-4,6: done.
    rewrite -Hscs_eq //. }
  iSplit.
  { iPureIntro. split_and!. 2-5: by eapply Htag_interp.
    destruct Htag_interp as (H1&H2&H3&H4&H5).
    intros t tk Htk. simpl. destruct (H1 t tk Htk) as (Hval1&Hval2&Hlocal&Hlu1&Hlu2&Hagree).
    split_and!; try done.
    (* - intros ->. split; intros ??; eapply trees_access_all_protected_initialized_contains.
      2, 4: done.  all: by eapply Hlocal. *)
    - intros l sc Hlusc.
      specialize (Hlu1 l sc Hlusc).
      eapply loc_controlled_trees_access_all_protected_initialized. 8: exact Hlu1.
      2: rewrite -Hscs_eq; exact Htrst. 2-5: done. 1-2: done.
    - intros l sc Hlusc.
      specialize (Hlu2 l sc Hlusc).
      eapply loc_controlled_trees_access_all_protected_initialized. 8: exact Hlu2.
      2: exact Htrss. 2-5: done. 1-2: done.
 }
  iSplit; iPureIntro.
  all: eapply endcall_step_wf_inner.
  all: try done; by rewrite -Hscs_eq.
Qed.

End lifting.


