From iris.proofmode Require Export proofmode.
From iris.base_logic.lib Require Import ghost_map.
From simuliris.base_logic Require Export gen_sim_prog.
From simuliris.simulation Require Export slsls.
From simuliris.simulation Require Import lifting.
From simuliris.tree_borrows Require Import tkmap_view.
From simuliris.tree_borrows Require Export defs class_instances.
From simuliris.tree_borrows Require Import wishlist steps_progress steps_inv.
From simuliris.tree_borrows Require Import logical_state inv_accessors early_proofmode.
From simuliris.tree_borrows.trees_equal Require Import trees_equal_base random_lemmas.
From simuliris.tree_borrows.trees_equal Require Import trees_equal_more_access trees_equal_preserved_by_access.

Section lifting.
Context `{!sborGS Σ}.
Implicit Types P Q : iProp Σ.
Implicit Types Φ : expr → expr → iProp Σ.
Implicit Types σ σ_s σ_t : state.
Implicit Types r r_s r_t : result.
Implicit Types l : loc.
Implicit Types f : fname.

Lemma target_copy_zero l t Ψ :
  (target_red #nil Ψ)%E -∗
  target_red (Copy (Place l t 0%nat)) Ψ.
Proof.
  iIntros "Hsim".
  iApply target_red_lift_base_step. iIntros (P_t σ_t P_s σ_s ?) "(HP_t & HP_s & Hbor)".
  iPoseProof (bor_interp_get_state_wf with "Hbor") as "[%Hwf_t %]".
  iModIntro. iDestruct "Hbor" as "(%M_call & %M_tag & %M_t & %M_s & Hbor)".
  destruct l as [blk off].
  iSplit.
  { iPureIntro. do 3 eexists. econstructor 2. 1: eapply CopyBS. 1: done.
    eapply ZeroCopyIS. done. }
  iIntros (e_t' efs_t σ_t' Hstep).
  eapply head_copy_inv in Hstep as (->&trs'&v'&->&->&Hread&[(_&_&HH)|(_&->&->)]).
  - lia.
  - iModIntro. iSplit; first done. simpl. iFrame "HP_s HP_t Hsim". do 4 iExists _. destruct σ_t. done.
Qed.

Lemma source_copy_zero l t π Ψ :
  (source_red #nil π Ψ)%E -∗
  source_red (Copy (Place l t 0%nat)) π Ψ.
Proof.
  iIntros "Hsim".
  iApply source_red_lift_base_step. iIntros (P_t σ_t P_s σ_s ??) "[(HP_t & HP_s & Hbor) _]".
  iModIntro. destruct l as [blk off]. iExists _, σ_s. iSplit.
  { iPureIntro. destruct σ_s. econstructor 2. all: simpl. 1: eapply CopyBS. 1: simpl; done.
    eapply ZeroCopyIS. done. }
  iModIntro. iFrame.
Qed.

Lemma target_write_zero l t Ψ :
  (target_red #[☠] Ψ)%E -∗
  target_red (Write (Place l t 0%nat) #[]) Ψ.
Proof.
  iIntros "Hsim".
  iApply target_red_lift_base_step. iIntros (P_t σ_t P_s σ_s ?) "(HP_t & HP_s & Hbor)".
  iPoseProof (bor_interp_get_state_wf with "Hbor") as "[%Hwf_t %]".
  iModIntro. iDestruct "Hbor" as "(%M_call & %M_tag & %M_t & %M_s & Hbor)".
  destruct l as [blk off].
  iSplit.
  { iPureIntro. do 3 eexists. econstructor 2. 1: eapply WriteBS. 1: done.
    1: simpl; intros ??; lia.
    eapply ZeroWriteIS. done. }
  iIntros (e_t' efs_t σ_t' Hstep).
  eapply head_write_inv in Hstep as (trs'&->&->&->&_&_&[(_&_&?)|(_&->)]).
  - lia.
  - iModIntro. iSplit; first done. simpl. iFrame "Hsim".
    iFrame "HP_t HP_s". destruct σ_t. by repeat iExists _.
Qed.

Lemma source_write_zero l t v π Ψ :
  (⌜v = nil⌝ -∗ source_red #[☠] π Ψ)%E -∗
  source_red (Write (Place l t 0%nat) #v) π Ψ.
Proof.
  iIntros "Hsim". iApply source_red_safe_implies.
  iIntros (Hv). destruct v; last done.
  iApply source_red_lift_base_step. iIntros (P_t σ_t P_s σ_s ??) "[(HP_t & HP_s & Hbor) _]".
  iModIntro. destruct l as [blk off]. iExists _, σ_s. iSplit.
  { iPureIntro. destruct σ_s. econstructor 2. all: simpl. 1: eapply WriteBS. 1: simpl; done.
    1: simpl; intros ??; lia.
    eapply ZeroWriteIS. done. }
  iModIntro. iFrame. by iApply "Hsim".
Qed.

Lemma sim_copy_public Φ π l_t bor_t sz l_s bor_s sz_t :
  rrel (PlaceR l_t bor_t sz_t) (PlaceR l_s bor_s sz) -∗
  (∀ v_t v_s, value_rel v_t v_s -∗ v_t ⪯{π} ValR v_s [{ Φ }]) -∗
  Copy (PlaceR l_t bor_t sz_t) ⪯{π} Copy (PlaceR l_s bor_s sz) [{ Φ }].
Proof.
  iIntros "[#Hscrel ->] Hsim".
  destruct (decide (sz = 0%nat)) as [->|Hne].
  { target_apply (Copy _) (target_copy_zero) "". source_apply (Copy _) (source_copy_zero) "".
    iApply "Hsim". rewrite /value_rel /=. iClear "Hscrel". iStopProof. done. }
  iPoseProof (sc_rel_ptr_source with "Hscrel") as "[%Heq Hpub]". injection Heq as [= -> ->].
  iClear "Hscrel".
  iApply sim_lift_base_step_both. iIntros (P_t P_s σ_t σ_s ??) "[(HP_t & HP_s & Hbor) %Hsafe]".
  iModIntro.
  destruct Hsafe as [Hpool Hsafe].
  iPoseProof (bor_interp_get_pure with "Hbor") as "%Hp".
  destruct Hp as (Hstrs_eq & Hsnp_eq & Hsnc_eq & Hscs_eq & Hwf_s & Hwf_t & Hdom_eq).
  specialize (pool_safe_implies Hsafe Hpool) as [(vr_s&Hreadmem&Hcontain_s&(trs_s'&Htrss)&_)|(_&_&[]%Hne)];
  pose proof Hcontain_s as Hcontain_t; rewrite trees_equal_same_tags in Hcontain_t; try done; last first.
(*  { (* We get poison *)
    assert (apply_within_trees (memory_access AccessRead (scs σ_s) bor_s (l_s.2, sz)) l_s.1 (strs σ_t) = None) as Hnotrees_t.
    { destruct apply_within_trees eqn:HSome in |-*; try done.
      eapply mk_is_Some, trees_equal_allows_more_access in HSome as (x&Hx); first by erewrite Hnotrees in Hx.
      1: by eapply trees_equal_sym. 1: eapply Hwf_t. 1-3: by eapply Hwf_s. 1: done. intros [=]. }
    iSplit. 
    { iPureIntro. do 3 eexists. eapply failed_copy_base_step'; try done.
      1: rewrite -Hscs_eq //.
      eapply read_mem_is_Some'. rewrite -Hdom_eq. by eapply read_mem_is_Some'.
    }
    iIntros (e_t' efs_t σ_t') "%Hhead_t".
    specialize (head_copy_inv _ _ _ _ _ _ _ _ Hhead_t) as (->&[((Hnotree&->&Hpoison&Hheapsome)&Hcontains_t)|(trs'&v'&->&Hσ_t'&Hreadmem&[(Hcontains_t&Hsometree&_)|([]%Hne&_&_)])]); last congruence.
    iModIntro. iExists e_t', [], σ_s. iSplit.
    { iPureIntro. subst e_t'. destruct σ_s, l_s. simpl. do 2 econstructor; by eauto. }
    simpl. iFrame. iSplit; last done. subst e_t'.
    iApply "Hsim". iApply big_sepL_sepL2_diag. iApply big_sepL_forall. by iIntros (k v (->&_)%lookup_replicate_1).
  } *)
  edestruct trees_equal_allows_more_access as (trs_t'&Htrst).
  1: done. 1: eapply Hwf_s. 1,2,3: rewrite ?Hscs_eq; eapply Hwf_t. 1: done. 1: done. 1: by eapply mk_is_Some.
  opose proof (trees_equal_preserved_by_access _ _ _ _ _ _ _ Hstrs_eq _ Htrss Htrst) as Hstrs_eq'.
  1,3,5: eapply Hwf_s. 1-3: rewrite ?Hscs_eq; eapply Hwf_t. 1: done.
  assert (is_Some (read_mem l_s sz (shp σ_t))) as (vr_t&Hreadmem_t).
  { eapply read_mem_is_Some'. eapply mk_is_Some in Hreadmem. rewrite -read_mem_is_Some' Hdom_eq in Hreadmem. done. }
  iSplit.
  { iPureIntro. do 3 eexists. eapply copy_base_step'. 1-3: done. rewrite -Hscs_eq. done. }
  (* we keep the base_step hypotheses to use the [base_step_wf] lemma below *)
  iIntros (e_t' efs_t σ_t') "%Hhead_t".
  specialize (head_copy_inv _ _ _ _ _ _ _ _ Hhead_t) as (->&tr'&vr_t'&->&Hσ_t'&H3&[(Hcontains_t&H4&_)|([]%Hne&_&_)]).
  assert (vr_t' = vr_t) as -> by congruence.
  assert (tr' = trs_t') as -> by congruence.
  clear H3 H4.
  iModIntro.
  pose (σ_s' := (mkState (shp σ_s) trs_s' (scs σ_s) (snp σ_s) (snc σ_s))).
  assert (Hhead_s : base_step P_s (Copy (Place l_s bor_s sz)) σ_s (ValR vr_s) σ_s' []).
  { eapply copy_base_step'; eauto. }
  iExists (Val vr_s), [], σ_s'. iSplitR; first done.
  iFrame "HP_t HP_s".

  iDestruct "Hbor" as "(%M_call & %M_tag & %M_t & %M_s & (Hc & Htag_auth & Htag_t_auth & Htag_s_auth) & Htainted & Hpub_cid & #Hsrel & %Hcall_interp & %Htag_interp & _ & _)".
  iPoseProof (tkmap_lookup with "Htag_auth Hpub") as "%Hpub".

  iSplitR "Hsim".
  {
    (* re-establish the invariants *)
    iExists M_call, M_tag, M_t, M_s.
    iFrame "Hc Htag_auth Htag_t_auth Htag_s_auth".
    subst σ_s' σ_t'.
    iSplitL "Htainted"; last iSplitL "Hpub_cid"; last iSplit; last iSplit; last iSplit; last iSplit.
    - iDestruct "Htainted" as "(%M'&Ht1&Ht2)". iExists M'. iFrame "Ht1".
      iIntros (t' l' Htl'). iDestruct ("Ht2" $! t' l' Htl') as "($&%Ht2)". iPureIntro.
      simpl. eapply disabled_tag_tree_apply_access_irreversible. 4: done. 2: done. 2: by eapply Hwf_s. done.
    - (* pub cid *)
      iApply (pub_cid_interp_preserve_sub with "Hpub_cid"); done.
    - repeat (iSplit; first done).
      simpl. iIntros (l) "Hs". iPoseProof (state_rel_pub_or_priv with "Hs Hsrel") as "$".
    - (* call invariant *)
      iPureIntro. destruct Hcall_interp as (Hcall_interp&Hcc2). split; last first. 1: done. intros c M' HM'_some.
      specialize (Hcall_interp c M' HM'_some) as (Hin & Hprot).
      split; first by apply Hin. intros pid L HL_some. specialize (Hprot pid L HL_some) as [Hpid Hprot].
      split; first by apply Hpid. intros l b Hin_l.
      specialize (Hprot l b Hin_l).
      eapply (tag_protected_preserved_by_access). 2: apply Htrst. 1: apply Hwf_t.
      1: by rewrite Hscs_eq. done.
    - (* tag invariant *)
      iPureIntro. destruct Htag_interp as (Htag_interp & Ht_dom & Hs_dom & Hunq1 & Hunq2). split_and!; [ | done..].
      intros t tk Htk_some. destruct (Htag_interp t tk Htk_some) as (Hsnp_lt_t & Hsnp_lt_s & Hlocal & Hctrl_t & Hctrl_s & Hag).
      split_and!; [ done | done | | | | done ].
      + done. (* intros ->. split; intros ??; eapply apply_within_trees_tag_count_preserves_exists.
        1, 4: done. 1, 3: eapply memory_access_tag_count.
        all: by eapply Hlocal. *)
      + intros l sc_t Hsc_t. eapply loc_controlled_read_preserved_everywhere.
        1: rewrite Hscs_eq in Htrst; eapply Htrst. 1: done. 1: by rewrite -Hscs_eq. 1-2: done.
        by eapply Hctrl_t.
      + intros l sc_s Hsc_s. eapply loc_controlled_read_preserved_everywhere.
        1: eapply Htrss. 1-4: done.
        by eapply Hctrl_s.
    - (* source state wf *)
      iPureIntro. eapply base_step_wf; done.
    - (* target state wf *)
      iPureIntro. eapply base_step_wf; done.
  }
  iSplitL; last done.

  iApply "Hsim".
  (* proving the value relation *)
  specialize (read_mem_values _ _ _ _ Hreadmem_t) as [Hlen_t Hvr_t].
  specialize (read_mem_values _ _ _ _ Hreadmem) as [Hlen_s Hvr_s].

  iApply big_sepL2_forall; iSplit; first (iPureIntro;lia).
  iIntros (i sc_t sc_s) "%Hs_t %Hs_s".
  assert (i < sz)%nat as Hi. { rewrite -Hlen_t. eapply lookup_lt_is_Some_1. eauto. }
  assert (is_Some (shp σ_t !! (l_s +ₗ i))) as Htloc.
  { exists sc_t. rewrite -Hs_t. by eapply Hvr_t. }
  iPoseProof (state_rel_pub_if_not_priv _ _ _ _ _ _ (l_s +ₗ i) with "[] Hsrel []") as "Hpubloc".
  1: done. 
  { iPureIntro. intros t Hpriv.
    eapply (protected_priv_loc_does_not_survive_access σ_t σ_t'). 10: exact Hpriv.
    1: rewrite Hscs_eq in Htrst. 1-3: by rewrite Hσ_t'. 1: done. 1: done. 1: simpl; lia.
    1: done. 1: done. 1: done.
    intros tg tk sc HH1 HH2.
    destruct (Htag_interp) as (H1&H2&H3&H4&H5).
    destruct (H1 tg tk HH1) as (_&_&_&HH3&HH4).
    apply HH3. done.
  }
  iPoseProof (pub_loc_lookup with "[] Hpubloc") as "(%sc_t' & %sc_s' & %Hread_both & Hsc_rel)"; first by eauto.
  enough (sc_t = sc_t' ∧ sc_s = sc_s') by naive_solver.
  move : Hread_both (Hvr_t i Hi) (Hvr_s i Hi) Hs_t Hs_s.
  by move => [-> ->] <- <- [= ->] [= ->].
Qed.

(** Write *)
Lemma sim_write_public Φ π l_t tg_t sz_t l_s tg_s sz_s v_t' v_s' :
  rrel (PlaceR l_t tg_t sz_t) (PlaceR l_s tg_s sz_s) -∗
  value_rel v_t' v_s' -∗
  (#[☠] ⪯{π} #[☠] [{ Φ }]) -∗
  Write (Place l_t tg_t sz_t) v_t' ⪯{π} Write (Place l_s tg_s sz_s) v_s' [{ Φ }].
Proof.
  iIntros "[#Hscrel ->] #Hvrel Hsim".
  destruct (decide (sz_s = 0%nat)) as [->|Hne].
  { source_apply (Write _ _) (source_write_zero) "->".
    iAssert ⌜v_t' = nil⌝%I as "->".
    { iPoseProof (big_sepL2_length with "Hvrel") as "%HH". by destruct v_t'. }
    target_apply (Write _ _) target_write_zero "".
    iApply "Hsim". }
  iPoseProof (sc_rel_ptr_source with "Hscrel") as "[%Heq Hpub]". injection Heq as [= -> ->].
  iClear "Hscrel".
  iApply sim_lift_base_step_both. iIntros (P_t P_s σ_t σ_s ??) "[(HP_t & HP_s & Hbor) %Hsafe]".
  iModIntro.
  destruct Hsafe as [Hpool Hsafe].
  iPoseProof (bor_interp_get_pure with "Hbor") as "%Hp".
  destruct Hp as (Hstrs_eq & Hsnp_eq & Hsnc_eq & Hscs_eq & Hwf_s & Hwf_t & Hdom_eq).
  specialize (pool_safe_implies Hsafe Hpool) as (Hread_s & [(Hcontain_s & trs_s' & Htrss)|[]%Hne] & Hlen).
  pose proof Hcontain_s as Hcontain_t; rewrite trees_equal_same_tags in Hcontain_t; try done.
  iPoseProof (value_rel_length with "Hvrel") as "%Hlen_t'".

  assert (∃ xx, apply_within_trees (memory_access AccessWrite (scs σ_t) tg_s (l_s.2, sz_s)) l_s.1 (strs σ_t) = Some xx) as (trs_t' & Htrst).
  { eapply trees_equal_allows_more_access. 1: by rewrite -Hscs_eq. 3: rewrite -Hscs_eq. 1: by apply Hwf_s. 1-3: rewrite ?Hscs_eq; by apply Hwf_t. 1-2: done. rewrite -Hscs_eq -Hlen. by eexists. }
  eassert (trees_equal _ _ trs_s' trs_t') as Htrseq.
  { eapply trees_equal_preserved_by_access. 7: done. 1,3,5: eapply Hwf_s. 1,2,3: rewrite ?Hscs_eq; eapply Hwf_t. 2: exact Htrss. 2: rewrite Hscs_eq Hlen //. done. }
  iSplitR.
  { iPureIntro. do 3 eexists. eapply write_base_step'; [lia | | |].
    - rewrite -Hdom_eq. intros n Hn. apply Hread_s. lia.
    - done.
    - apply Htrst.
  }
  iIntros (e_t' efs_t σ_t') "%Hhead_t".
  specialize (head_write_inv _ _ _ _ _ _ _ _ _ Hhead_t) as (trst_2 & -> & -> & -> & _ & Hin_dom & [(_ & Htrst'&_)|([]%Hne&_)]).
  assert (trst_2 = trs_t') as -> by congruence.
  iModIntro.
  pose (σ_s' := (mkState (write_mem l_s v_s' σ_s.(shp)) trs_s' σ_s.(scs) σ_s.(snp) σ_s.(snc))).
  assert (Hhead_s : base_step P_s (Write (Place l_s tg_s sz_s) v_s') σ_s (ValR [☠]%S) σ_s' []).
  { eapply write_base_step'; eauto. 2: by rewrite -Hlen. intros. rewrite Hdom_eq. apply Hin_dom. lia. }
  iExists (#[☠])%E, [], σ_s'. iSplitR; first done.
  iFrame "HP_t HP_s".
  iSplitR "Hsim"; first last. { iSplitL; done. }

  iDestruct "Hbor" as "(%M_call & %M_tag & %M_t & %M_s & (Hc & Htag_auth & Htag_t_auth & Htag_s_auth) & Htainted & Hpub_cid & #Hsrel & %Hcall_interp & %Htag_interp & _ & _)".
  iPoseProof (tkmap_lookup with "Htag_auth Hpub") as "%"; try done.

  (* we keep the base_step hypotheses to use the [base_step_wf] lemma below *)
  (* re-establish the invariants *)
  iExists M_call, M_tag, M_t, M_s.
  iFrame "Hc Htag_auth Htag_t_auth Htag_s_auth".
  iSplitL "Htainted"; last iSplitL "Hpub_cid"; last iSplit; last iSplit; last iSplit; last iSplit.
  - iDestruct "Htainted" as "(%M'&Ht1&Ht2)". iExists M'. iFrame "Ht1".
    iIntros (t' l' Htl'). iDestruct ("Ht2" $! t' l' Htl') as "($&%Ht2)". iPureIntro.
    simpl. eapply disabled_tag_tree_apply_access_irreversible. 4: done. 2: done. 2: by eapply Hwf_s. done.
  - (* pub cid *)
    iApply (pub_cid_interp_preserve_sub with "Hpub_cid"); done.
  - (* state rel *)
    rewrite /state_rel; simpl. iSplitL.
    { iPureIntro. erewrite !write_mem_dom_sane; first done. all: eauto. }
    do 4 (iSplitL; first done). iDestruct "Hsrel" as "(_ & _ & _ & _ & _ & Hsrel)".
    iIntros (l) "%Hs".
    specialize (write_mem_lookup l_s v_s' σ_s.(shp)) as (Heq & Heq').
    specialize (write_mem_lookup_case l_s v_t' σ_t.(shp) l) as [(i & Hi & -> & Hwrite) | (Hi & Hwrite)].
    + (* we wrote to the location, and the written values must be related *)
      iLeft. iIntros (sc_t Hsc_t). simpl in Hsc_t. rewrite Heq; last lia.
      iExists (v_s' !!! i). rewrite Hwrite in Hsc_t.
      rewrite -(list_lookup_total_correct _ _ _ Hsc_t).
      iSplitR. { iPureIntro. apply list_lookup_lookup_total. apply lookup_lt_is_Some_2. lia. }
      iApply (value_rel_lookup_total with "Hvrel"). lia.
    + (* unaffected location *)
      simpl. rewrite Hwrite in Hs.
      iDestruct ("Hsrel" $! l with "[//]") as "[Hpubl | Hprivl]"; last by iRight.
      iLeft. rewrite /pub_loc Hwrite Heq'; first done. intros. apply Hi. lia.
  - (* call invariant *)
    iPureIntro. destruct Hcall_interp as (Hcall_interp&Hcc2). split; last first. 1: done. intros c M' HM'_some. simpl.
    specialize (Hcall_interp c M' HM'_some) as (Hin & Hprot).
    split; first done. intros t L [Ht HL]%Hprot. split; first done.
    intros l b Hprotl%HL.
    eapply tag_protected_preserved_by_access; last done.
    1: by eapply Hwf_t. 1: done. apply Hin.
  - (* tag invariant *)
    iPureIntro. destruct Htag_interp as (Htag_interp & Ht_dom & Hs_dom & Hunq1 & Hunq2). split_and!; [ | done..].
    intros t tk Ht.
    specialize (Htag_interp _ _ Ht) as (? & ? & Hlocal & Hcontrolled_t & Hcontrolled_s & Hdom).
    split_and!; [ done | done | | | | done ].
    + apply Hlocal. (* intros ->. split; intros ??; eapply apply_within_trees_tag_count_preserves_exists.
      1, 4: done. 1, 3: eapply memory_access_tag_count.
      all: by eapply Hlocal. *)
    + intros l sc_t Hcontrol%Hcontrolled_t.
      destruct (decide (l.1 = l_s.1 ∧ l_s.2 ≤ l.2 < l_s.2 + sz_s)) as [(Hin1&Hin2)|Hout]; first 
      destruct (decide (t = tg_s)) as [->|Htgne].
      * assert (tk = tk_pub) as -> by congruence.
        eapply loc_controlled_write_invalidates_pub'; last done.
        all: done.
      * rewrite /loc_controlled. eapply loc_controlled_write_invalidates_others; last done.
        all: done.
      * eapply loc_controlled_access_outside; first done. all: try done.
        rewrite /= write_mem_lookup_outside // Hlen_t' Hlen //.
    + intros l sc_s Hcontrol%Hcontrolled_s.
      destruct (decide (l.1 = l_s.1 ∧ l_s.2 ≤ l.2 < l_s.2 + sz_s)) as [(Hin1&Hin2)|Hout]; first 
      destruct (decide (t = tg_s)) as [->|Htgne].
      * assert (tk = tk_pub) as -> by congruence.
        eapply loc_controlled_write_invalidates_pub'; last done.
        all: try done. by rewrite Hlen.
      * rewrite /loc_controlled. eapply loc_controlled_write_invalidates_others; last done.
        all: try done. by rewrite Hlen.
      * eapply loc_controlled_access_outside; first done. all: try done.
        2: by rewrite Hlen.
        rewrite /= write_mem_lookup_outside // Hlen //.
  - (* source state wf *)
    iPureIntro. eapply base_step_wf; done.
  - (* target state wf *)
    iPureIntro. eapply base_step_wf; done. 
Qed.


End lifting.


