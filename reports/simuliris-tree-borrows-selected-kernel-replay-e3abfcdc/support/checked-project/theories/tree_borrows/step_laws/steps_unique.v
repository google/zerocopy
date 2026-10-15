From iris.proofmode Require Export proofmode.
From iris.base_logic.lib Require Import ghost_map.
From simuliris.base_logic Require Export gen_sim_prog.
From simuliris.simulation Require Export slsls.
From simuliris.simulation Require Import lifting.
From simuliris.tree_borrows Require Import tkmap_view.
From simuliris.tree_borrows Require Export defs class_instances.
From simuliris.tree_borrows Require Import steps_progress steps_inv.
From simuliris.tree_borrows Require Import logical_state inv_accessors.
From simuliris.tree_borrows Require Import wishlist.
From simuliris.tree_borrows.trees_equal Require Import trees_equal_base random_lemmas.
From simuliris.tree_borrows.trees_equal Require Import trees_equal_more_access trees_equal_preserved_by_access disabled_tag_rejects_read_precisely.

(** * Simulation lemmas using the ghost state for proving optimizations *)
(* TODO: rename this file. It is not just about unique *)

Section lifting.
Context `{!sborGS Σ}.
Implicit Types P Q : iProp Σ.
Implicit Types Φ : expr → expr → iProp Σ.
Implicit Types σ σ_s σ_t : state.
Implicit Types r r_s r_t : result.
Implicit Types l : loc.
Implicit Types f : fname.

(** ** Read lemma *)

Lemma sim_copy v_t v_s v_rd_t v_rd_s sz l_hl l_rd t π tk Φ :
  sz ≠ 0%nat → (* if it is 0, use the zero-sized read lemma *)
  read_range l_rd.2 sz (list_to_heaplet v_t l_hl.2) = Some v_rd_t →
  read_range l_rd.2 sz (list_to_heaplet v_s l_hl.2) = Some v_rd_s →
  l_hl.1 = l_rd.1 →
  t $$ tk -∗
  l_hl ↦s∗[tk]{t} v_s -∗
  l_hl ↦t∗[tk]{t} v_t -∗
  (∀ v_res_s v_res_t, l_hl ↦s∗[tk]{t} v_s -∗ l_hl ↦t∗[tk]{t} v_t -∗ t $$ tk -∗ (⌜v_res_s = v_rd_s ∧ v_res_t = v_rd_t⌝ (*∨ ispoison v_res_s l_rd t sz ∗ ispoison v_res_t l_rd t sz*)) -∗ #v_res_t ⪯{π} #v_res_s  [{ Φ }])%E -∗
  (Copy (Place l_rd t sz))  ⪯{π} (Copy (Place l_rd t sz))  [{ Φ }].
Proof.
  iIntros (Hsz Hreadt Hreads Hl) "Htk Hs Ht Hsim".
  iApply sim_lift_base_step_both. iIntros (P_t P_s σ_t σ_s ??) "[(HP_t & HP_s & Hbor) %Hsafe]".
  iModIntro.
  destruct Hsafe as [Hpool Hsafe].
  iPoseProof (bor_interp_get_pure with "Hbor") as "%Hp".
  destruct Hp as (Hstrs_eq & Hsnp_eq & Hsnc_eq & Hscs_eq & Hwf_s & Hwf_t & Hdom_eq).
  specialize (pool_safe_implies Hsafe Hpool) as [(vr_s&Hreadmem&Hcontain_s&(trs_s'&Htrss)&_)|(_&_&[]%Hsz)];
  pose proof Hcontain_s as Hcontain_t; rewrite trees_equal_same_tags in Hcontain_t; try done; last first.
(*  { (* We get poison *)
    assert (apply_within_trees (memory_access AccessRead (scs σ_s) t (l_rd.2, sz)) l_rd.1 (strs σ_t) = None) as Hnotrees_t.
    { destruct apply_within_trees eqn:HSome in |-*; try done.
      eapply mk_is_Some, trees_equal_allows_more_access in HSome as (x&Hx); first by erewrite Hnotrees in Hx.
      1: by eapply trees_equal_sym. 1: eapply Hwf_t. 1-3: by eapply Hwf_s. 1: done. intros [=]. }
    iSplit. 
    { iPureIntro. do 3 eexists. eapply failed_copy_base_step'; try done.
      1: rewrite -Hscs_eq //.
      eapply read_mem_is_Some'. rewrite -Hdom_eq. by eapply read_mem_is_Some'.
    }
    iIntros (e_t' efs_t σ_t') "%Hhead_t".
    specialize (head_copy_inv _ _ _ _ _ _ _ _ Hhead_t) as (->&[((Hnotree&->&Hpoison&Hheapsome)&Hcontains_t)|(trs'&v'&->&Hσ_t'&Hreadmem&[(Hcontains_t&Hsometree&_)|([]%Hsz&_&_)])]); last congruence.

    pose proof Hnotrees as Hn2.
    rewrite /apply_within_trees in Hn2. pose proof Hcontain_s as Hcont.
    rewrite /trees_contain /trees_at_block in Hcont.
    destruct (strs σ_s !! l_rd.1) as [tr|] eqn:Heq; last done.
    simpl in *. eapply bind_None in Hn2 as [Hn2|(x1&Hx1&Hx2)]. 2: done.
    assert (tree_unique t tr) as (it&Hit)%unique_implies_lookup by by eapply Hwf_s.
    iDestruct "Hbor" as "(%M_call & %M_tag & %M_t & %M_s & Hbor)".
    iDestruct "Hbor" as "((Hc & Htag_auth & Htag_t_auth & Htag_s_auth) & Htainted & Hpub_cid & #Hsrel & %Hcall_interp & %Htag_interp & _ & _)".
    iPoseProof (tkmap_lookup with "Htag_auth Htk") as "%Htag".
    iPoseProof (ghost_map_lookup with "Htag_s_auth Hs") as "%Hs".
    eapply read_range_length in Hreads as HHsz.
    eapply read_range_length in Hreadt as HHszt.
    eapply read_fails_disabled_tag_or_prot_act_child in Hn2 as (l&Hl'&Hn2). 2-4: by eapply Hwf_s. 2: done.
    2: { intros l Hl' Him. destruct (Htag_interp) as (H1&_).
         specialize (H1 _ _ Htag) as (_&_&_&H2&H3&_).
         specialize (H3 (l_rd.1, l)). rewrite /range'_contains /= in Hl'.
         rewrite /heaplet_lookup /= -Hl /= Hs /= in H3.
         assert (∃ (il:nat), l = l_rd.2 + il) as (il&->).
         { exists (Z.to_nat (l - l_rd.2)). lia. }
         assert (il < length v_rd_s)%nat as (sc&Hsc)%lookup_lt_is_Some_2 by lia.
         eapply read_range_lookup_nth in Hreads. 2: done.
         specialize (H3 _ Hreads).
         eapply bor_state_own_on_not_reservedim. 5: exact H3. 1: done. 2: done. 2: done. 1: congruence. }
    rewrite /range'_contains /= in Hl'.
    destruct Hn2 as [Hn2|(Hn2&_)]. 
    2: { destruct (Htag_interp) as (H1&_).
         specialize (H1 _ _ Htag) as (_&_&_&H2&H3&_).
         specialize (H3 (l_rd.1, l)).
         rewrite /heaplet_lookup /= -Hl /= Hs /= in H3.
         assert (∃ (il:nat), l = l_rd.2 + il) as (il&->).
         { exists (Z.to_nat (l - l_rd.2)). lia. }
         assert (il < length v_rd_s)%nat as (sc&Hsc)%lookup_lt_is_Some_2 by lia.
         eapply read_range_lookup_nth in Hreads. 2: done.
         specialize (H3 _ Hreads).
         eapply bor_state_own_no_active_child in Hn2. 2,3: done. 2: eapply Hit.
         2: rewrite -Hl; exact H3. done. }

    iMod (tag_tainted_interp_insert _ _ (l_rd.1, l) with "Htainted") as "(Htainted&#Hpoison)".
    { split. 2: rewrite /= Heq; left; exact Hn2.
      destruct (Htag_interp) as (H1&_).
      specialize (H1 _ _ Htag) as (_&Hx&_). rewrite /tag_valid in Hx. lia. }
    iModIntro. iFrame "HP_t HP_s". iSpecialize ("Hsim" $! (replicate (length v_rd_s) _) (replicate (length v_rd_s) _) with "Hs Ht Htk []").
    { iRight. iSplit.
      { iExists (Z.to_nat (l - l_rd.2)). rewrite length_replicate. iSplit. 1: iPureIntro; split; last by f_equal.
        1: simpl; lia. simpl. assert ((l_rd +ₗ Z.to_nat (l - l_rd.2) = (l_rd.1, l))) as ->. 2: done.
        rewrite /shift_loc /=. simpl. f_equal. lia. }
      { iExists (Z.to_nat (l - l_rd.2)). rewrite length_replicate. iSplit. 1: iPureIntro; split; last by f_equal.
        1: simpl; lia. simpl. assert ((l_rd +ₗ Z.to_nat (l - l_rd.2) = (l_rd.1, l))) as ->. 2: done.
        rewrite /shift_loc /=. simpl. f_equal. lia. } }
     iExists e_t', [], σ_s. iSplit.
     { iPureIntro. subst e_t'. destruct σ_s, l_rd. simpl. do 2 econstructor; by eauto. }
     iSplitR "Hsim".
     { do 4 iExists _; destruct σ_s; iFrame. iFrame "Hsrel". done. }
     simpl. rewrite Hpoison. subst sz. iSplit; last done. iApply "Hsim".
  } *)
  edestruct trees_equal_allows_more_access as (trs_t'&Htrst).
  1: done. 1: eapply Hwf_s. 1,2,3: rewrite ?Hscs_eq; eapply Hwf_t. 1: done. 1: done. 1: by eapply mk_is_Some.
  opose proof (trees_equal_preserved_by_access _ _ _ _ _ _ _ Hstrs_eq _ Htrss Htrst) as Hstrs_eq'.
  1,3,5: eapply Hwf_s. 1-3: rewrite ?Hscs_eq; eapply Hwf_t. 1: done.
  assert (is_Some (read_mem l_rd sz (shp σ_t))) as (vr_t&Hreadmem_t).
  { eapply read_mem_is_Some'. eapply mk_is_Some in Hreadmem. rewrite -read_mem_is_Some' Hdom_eq in Hreadmem. done. }
  iSplit.
  { iPureIntro. do 3 eexists. eapply copy_base_step'. 1-3: done. rewrite -Hscs_eq. done. }
  (* we keep the base_step hypotheses to use the [base_step_wf] lemma below *)
  iIntros (e_t' efs_t σ_t') "%Hhead_t".
  specialize (head_copy_inv _ _ _ _ _ _ _ _ Hhead_t) as (->&tr'&vr_t'&->&Hσ_t'&H3&[(Hcontains_t&H4&_)|([]%Hsz&_&_)]).
  assert (vr_t' = vr_t) as -> by congruence.
  assert (tr' = trs_t') as -> by congruence.
  clear H3 H4.
  iModIntro.
  pose (σ_s' := (mkState (shp σ_s) trs_s' (scs σ_s) (snp σ_s) (snc σ_s))).
  assert (Hhead_s : base_step P_s (Copy (Place l_rd t sz)) σ_s (ValR vr_s) σ_s' []).
  { eapply copy_base_step'; eauto. }
  iExists (Val vr_s), [], σ_s'. iSplitR; first done.
  iFrame "HP_t HP_s".

  iDestruct "Hbor" as "(%M_call & %M_tag & %M_t & %M_s & Hbor)".
  eapply read_range_length in Hreads as Hlens. eapply read_range_length in Hreadt as Hlent.
  iPoseProof (bor_interp_readN_source_after_accesss with "Hbor Hs Htk") as "(%its&%trs&%Hits&%Htrs&%Howns)".
  1: exact Hreads. 1: done. 1: lia. 1: done. 1: eexists; rewrite Hlens; done.
  iPoseProof (bor_interp_readN_target_after_accesss with "Hbor Ht Htk") as "(%itt&%trt&%Hitt&%Htrt&%Hownt)".
  1: exact Hreadt. 1: done. 1: lia. 1: done. 1: eexists; rewrite Hlent -Hscs_eq; done.

  

  iDestruct "Hbor" as "((Hc & Htag_auth & Htag_t_auth & Htag_s_auth) & Htainted & Hpub_cid & #Hsrel & %Hcall_interp & %Htag_interp & _ & _)".
  iPoseProof (tkmap_lookup with "Htag_auth Htk") as "%Htk".
  iPoseProof (ghost_map_lookup with "Htag_t_auth Ht") as "%Ht".
  iPoseProof (ghost_map_lookup with "Htag_s_auth Hs") as "%Hs".

  iSplitR "Hsim Hs Ht Htk".
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
      intros t' tk' Htk_some. destruct (Htag_interp _ _ Htk_some) as (Hsnp_lt_t & Hsnp_lt_s & Hlocal & Hctrl_t & Hctrl_s & Hag).
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

  iApply ("Hsim" with "Hs Ht Htk"). iPureIntro.
  eapply read_range_list_to_heaplet_read_memory_strict in Hreads. 2: done.
  2: intros i Hi; specialize (Howns i Hi) as (_&H); exact H.
  eapply read_range_list_to_heaplet_read_memory_strict in Hreadt. 2: done.
  2: intros i Hi; specialize (Hownt i Hi) as (_&H); exact H.
  rewrite Hreadmem_t in Hreadt. rewrite Hreadmem in Hreads. simplify_eq.
  done.
Qed.


Lemma sim_into_read_for_simulation v_res_t v_res_s v_rd_t v_rd_s l_rd t :
  let sz := length v_rd_t in
  value_rel v_rd_t v_rd_s -∗
  (⌜v_res_s = v_rd_s ∧ v_res_t = v_rd_t⌝ (*∨ ispoison v_res_s l_rd t sz ∗ ispoison v_res_t l_rd t sz*)) -∗
  will_read_in_simulation v_rd_s v_res_t l_rd t.
Proof.
  intros sz. iIntros "Hv1 Hor".
  iPoseProof (value_rel_length with "Hv1") as "%Hlen".
  iDestruct "Hor" as "(->&->)".
  { done. } (*
  iRight. subst sz.
  iDestruct "Hp2" as "(%i&(_&%HH)&_)". rewrite HH.
  rewrite length_replicate Hlen. iSplit; first done.
  iDestruct "Hp1" as "(%ip&(%H1&%H2)&Hpp)". iExists ip. iSplit; last done.
  rewrite length_replicate. iPureIntro; split. 2: done.
  rewrite H2 length_replicate in H1. lia. *)
Qed.

Lemma sim_read_result_value_rel v_res_t v_res_s v_rd_t v_rd_s :
  let sz := length v_rd_t in
  value_rel v_rd_t v_rd_s -∗
  (⌜v_res_s = v_rd_s ∧ v_res_t = v_rd_t⌝ (* ∨ ispoison v_res_s l_rd t sz ∗ ispoison v_res_t l_rd t sz *) ) -∗
  value_rel v_res_t v_res_s.
Proof.
  intros sz. iIntros "Hv1 Hor".
  iPoseProof (value_rel_length with "Hv1") as "%Hlen".
  iDestruct "Hor" as "(->&->)".
  { done. } (*
  subst sz.
  iDestruct "Hp2" as "(%i&(_&%HH)&_)". rewrite HH.
  iDestruct "Hp1" as "(%ip&(%H1&%H2)&Hpp)". rewrite H2.
  iApply big_sepL2_forall. iSplit.
  { rewrite length_replicate //. }
  iIntros (k x1 x2 (->&_)%lookup_replicate_1 (->&_)%lookup_replicate_1). done. *)
Qed.



(** ** Write lemmas *)

(* TODO we can even strengthen this to learn that the old values were related if tkk = tk_res *)
(* This lemma is kind-of unusable, since b, and maybe c and M need to be specified manually *)
Lemma sim_write_activate_general (b:bool) c M π l t sz tkk v_t v_s v_t' v_s' Φ :
  length v_t = sz →
  length v_s = sz →
  t $$ tk_unq tkk -∗
  l ↦t∗[tk_unq tkk]{t} v_t -∗
  l ↦s∗[tk_unq tkk]{t} v_s -∗
  (* crucial: without protectors, we need to write related values, as the locations
    will need to be public in the state_rel -- after all, there is no protector, so it can't be private! *)
  (if b then value_rel v_t' v_s' else (⌜length v_t' = length v_s'⌝ ∗ c @@ M ∗ ⌜(∀ i: nat, (i < sz)%nat → ∃ ae, call_set_in M t (l +ₗ i) (EnsuringAccess ae))⌝)) -∗
  (t $$ tk_unq tk_act -∗ l ↦t∗[tk_unq tk_act]{t} v_t' -∗ l ↦s∗[tk_unq tk_act]{t} v_s' -∗ (if b then True else c @@ M) -∗ #[☠] ⪯{π} #[☠] [{ Φ }]) -∗
  Write (Place l t sz) #v_t' ⪯{π} Write (Place l t sz) #v_s' [{ Φ }].
Proof.
  (* get the loc controlled things. exploit source UB. update the ghost state. *)
  iIntros (Hsz1 Hsz2) "Htag Ht Hs Hvrel Hsim".
  iApply sim_lift_base_step_both. iIntros (P_t P_s σ_t σ_s ??) "[(HP_t & HP_s & Hbor) %Hsafe]".
  iDestruct "Hbor" as "(%M_call & %M_tag & %M_t & %M_s & Hbor)".
  iPoseProof (bor_interp_readN_target with "Hbor Ht Htag") as "%Hcontrol_t".
  iPoseProof (bor_interp_readN_source with "Hbor Hs Htag") as "%Hcontrol_s".

  iModIntro.
  destruct Hsafe as [Hpool Hsafe]. 
  specialize (pool_safe_implies Hsafe Hpool) as (Hread_s & Htreeorz & Hlen_s').
  iAssert (⌜length v_t' = length v_s'⌝)%I as "%Hlen_t'".
  { destruct b. 1: iPoseProof (value_rel_length with "Hvrel") as "$".
    by iDestruct "Hvrel" as "($&_)". }

  iPoseProof (bor_interp_get_pure with "[Hbor]") as "%Hp".
  1: by do 4 iExists _.
  destruct Hp as (Hsst_eq & Hstrs_eq & Hsnc_eq & Hscs_eq & Hwf_s & Hwf_t & Hdom_eq).
  destruct (decide (sz = 0%nat)) as [->|Hnonzero].
  { (* Handle zero-sized case *)
    destruct v_t; last done. destruct v_s; last done.
    destruct v_s'; last done. destruct v_t'; last done. destruct l as [blk off].
    iSplit. { iPureIntro. do 3 eexists. econstructor 2. 1: econstructor.
      1: done. 1: lia. 1: by eapply ZeroWriteIS. }
    iIntros (e_t' efs_t σ_t') "%Hhead_t".
    specialize (head_write_inv _ _ _ _ _ _ _ _ _ Hhead_t) as (trst_2 & -> & -> & -> & _ & Hin_dom & [(_ & _ &Hx)|(_&->)]); first done.
    iDestruct "Hbor" as "((Hc & Htag_auth & Htag_t_auth & Htag_s_auth) & Htainted & Hpub_cid & #Hsrel & %Hcall_interp & %Htag_interp & _ & _)".
    iPoseProof (ghost_map_lookup with "Htag_t_auth Ht") as "%Hheaplet_t".
    iPoseProof (ghost_map_lookup with "Htag_s_auth Hs") as "%Hheaplet_s".
    iPoseProof (tkmap_lookup with "Htag_auth Htag") as "%Htk".
    iMod (tkmap_update_strong (tk_unq tk_act) () with "Htag_auth Htag") as "(Htag_auth & Htag)"; first done.
    rewrite /= in Hhead_t.
    iModIntro. iExists _, _, _. iSplit.
    { iPureIntro. econstructor 2. 1: econstructor.
      1: done. 1: lia. 1: by eapply ZeroWriteIS. }
    simpl. iFrame "HP_t HP_s". 
    iSplitR "Hsim Hs Ht Htag Hvrel"; first last.
    { iSplitL. 2: iClear "#"; by iStopProof. iApply ("Hsim" with "Htag Ht Hs").
      destruct b; first done. iDestruct "Hvrel" as "(_&$&_)". }
    iExists _, _, _, _. iFrame. destruct σ_t as [shp_t strs_t scs_t snp_t snc_t], σ_s as [shp_s strs_s scs_s snp_s snc_s]. simpl in *.
    iSplit; last iPureIntro.
    { repeat (iSplit; first done). iDestruct "Hsrel" as "(_&_&_&_&_&Hsrel)". simpl. iIntros (l Hl).
      iDestruct ("Hsrel" $! l Hl) as "[$|%HH]". iRight. destruct HH as (t'&tk'&H1&H2&H3). iPureIntro. exists t', tk'.
      split; last done. rewrite lookup_insert_ne; first done.
      intros <-. destruct H2 as (sc&(M'&HM'&HHsc)%bind_Some). simpl in *.
      enough (l.1 = blk) as <-.
      { assert (M' = ∅) as -> by congruence. rewrite lookup_empty // in HHsc. }
      destruct Htag_interp as (HH1&HH2&HH3&HH4&HH5). eapply elem_of_dom_2 in HM'. eapply elem_of_dom_2 in Hheaplet_t.
      by eapply HH4. }
    split; last split; last done.
    { eapply call_set_interp_mono. 2: eassumption. intros ??[??] it ???? (tk' & Htk' & HHH).
      destruct (decide (itag it = t)) as [<-|Hne].
      { eexists. rewrite lookup_insert_eq. done. }
      { exists tk'. split; last done. by rewrite lookup_insert_ne. } }
    { destruct Htag_interp as (HH1&HH2&HH3&HH4&HH5). split_and!. 4-5: done. all: simpl in *.
      - intros t' tl' [(<-&[= <-])|(Hne&Hin)]%lookup_insert_Some.
        2: by eapply HH1.
        destruct (HH1 _ _ Htk) as (Hhl1&Hhl2&Hhllocal&Hhl3&Hhl4&Hhl5). split_and!. 1-3, 6: done.
        all: intros ll sc (MM&HM1&HM2)%bind_Some; simpl in *.
        all: enough (ll.1 = blk) as <-; first (assert (MM = ∅) as ->; [congruence|by rewrite lookup_empty in HM2]).
        1: eapply HH4; by eapply elem_of_dom. 1: eapply HH5; by eapply elem_of_dom.
      - intros ???. eapply elem_of_dom. rewrite dom_insert_lookup_L. 2: by eexists. by eapply elem_of_dom, HH2.
      - intros ???. eapply elem_of_dom. rewrite dom_insert_lookup_L. 2: by eexists. by eapply elem_of_dom, HH3. } }
  destruct Htreeorz as [(Hcontain&trs_s'&Htree_s)|?]. 2: done.

  eapply mk_is_Some in Htree_s as Htree_t.
  eapply trees_equal_allows_more_access in Htree_t as (trs_t' & Htree_t);
    [|done|eapply Hwf_s|eapply Hwf_t|rewrite ?Hscs_eq;by eapply Hwf_t|by eapply Hwf_t|done|done].

  edestruct (trees_equal_same_tags) as [HL _]; first done.
  eapply HL in Hcontain as Hcontain_t; clear HL.

  opose proof (trees_equal_preserved_by_access _ _ _ _ _ _ _ _ _ Htree_s Htree_t) as Hstrs_eq'.
  1,3,5: eapply Hwf_s. 1-3: rewrite ?Hscs_eq; eapply Hwf_t. 1, 2: done.

  (* from source reduction, we get that bor_state_pre is satisfied for the affected locations *)
  assert (∀ i, (i < length v_s)%nat → bor_state_own (l +ₗ i) t (tk_unq tkk) σ_s ∧ bor_state_own (l +ₗ i) t (tk_unq tkk) σ_t) as Hcontrol_own.
  { intros i Hi. 
    destruct (Hcontrol_s i Hi) as [Hown_s _].
    { rewrite bor_state_pre_unq_or; last (destruct tkk; tauto). rewrite /bor_state_pre_unq /=.
      eapply trees_contain_trees_lookup_1 in Hcontain as Hcontain2.
      2: apply Hwf_s. destruct Hcontain2 as (it & Hlookup).
      exists it; split; first done.
      eapply (apply_trees_access_lookup_general _ (l.2 + i)) in Htree_s as HH.
      2: apply Hwf_s. 2: lia. 2: apply Hlookup.
      destruct HH as (itnew & Hlookup_new & Hinit & Hprot & Haccess).
      destruct (item_lookup it (l.2 + i)) as [init perm] eqn:Hluit.
      simpl. erewrite trees_rel_dec_refl in Haccess.
      rewrite /apply_access_perm /= in Haccess.
      apply option_bind_inv in Haccess as (perm' & H1 & _).
      by destruct perm. }
    destruct (Hcontrol_t i) as [Hown_t _].
    1: lia.
    { rewrite bor_state_pre_unq_or; last (destruct tkk; tauto). rewrite /bor_state_pre_unq /=.
      eapply trees_contain_trees_lookup_1 in Hcontain_t as Hcontain2.
      2: apply Hwf_t. destruct Hcontain2 as (it & Hlookup).
      exists it; split; first done.
      eapply (apply_trees_access_lookup_general _ (l.2 + i)) in Htree_t as HH.
      2: apply Hwf_t. 2: lia. 2: apply Hlookup.
      destruct HH as (itnew & Hlookup_new & Hinit & Hprot & Haccess).
      destruct (item_lookup it (l.2 + i)) as [init perm] eqn:Hluit.
      simpl. erewrite trees_rel_dec_refl in Haccess.
      rewrite /apply_access_perm /= in Haccess.
      apply option_bind_inv in Haccess as (perm' & H1 & _).
      by destruct perm. }
    done.
  }

  iSplitR.
  { iPureIntro. do 3 eexists. eapply write_base_step'; [lia | |done|].
    - rewrite -Hdom_eq. intros n Hn. apply Hread_s. lia.
    - rewrite -Hscs_eq -Hlen_s'. apply Htree_t.
  }
  iIntros (e_t' efs_t σ_t') "%Hhead_t".
  specialize (head_write_inv _ _ _ _ _ _ _ _ _ Hhead_t) as (trs'' & -> & -> & -> & _ & Hin_dom & [(_ & Htrs'' & _)|([]%Hnonzero&_)]).
  assert (trs'' = trs_t') as -> by congruence. clear Htrs''.

  (* update the ghost state.
    no separate lemma for, this is quite an atomic operation. *)
  iDestruct "Hbor" as "((Hc & Htag_auth & Htag_t_auth & Htag_s_auth) & Htainted & Hpub_cid & #Hsrel & %Hcall_interp & %Htag_interp & _ & _)".
  iPoseProof (ghost_map_lookup with "Htag_t_auth Ht") as "%Hheaplet_t".
  iPoseProof (ghost_map_lookup with "Htag_s_auth Hs") as "%Hheaplet_s".
  iMod (ghost_map_array_tag_update _ _ _ v_t' with "Htag_t_auth Ht") as "[Ht Htag_t_auth]"; first lia.
  iMod (ghost_map_array_tag_update _ _ _ v_s' with "Htag_s_auth Hs") as "[Hs Htag_s_auth]"; first lia.
  iPoseProof (tkmap_lookup with "Htag_auth Htag") as "%Htk".
  iMod (tkmap_update_strong (tk_unq tk_act) () with "Htag_auth Htag") as "(Htag_auth & Htag)"; first done.
  iAssert ((□ if b then value_rel v_t' v_s' else ⌜M_call !! c = Some M ∧ (∀ i: nat, (i < sz)%nat → ∃ ae, call_set_in M t (l +ₗ i) (EnsuringAccess ae))⌝))%I as "#HvrelP".
  { destruct b. 1: by iPoseProof "Hvrel" as "#$". iDestruct "Hvrel" as "(_&H2&%H3)".
    iPoseProof (ghost_map_lookup with "Hc H2") as "%HH2". iModIntro. iPureIntro. done. }
  iAssert (if b then True else c @@ M)%I with "[Hvrel]" as "Hcs".
  { destruct b; first done. iDestruct "Hvrel" as "(_&$&_)". }

  iModIntro.
  pose (σ_s' := (mkState (write_mem l v_s' σ_s.(shp)) trs_s' σ_s.(scs) σ_s.(snp) σ_s.(snc))).
  assert (Hhead_s : base_step P_s (Write (Place l t sz) v_s') σ_s (ValR [☠]%S) σ_s' []).
  { rewrite Hlen_s' in Htree_s. eapply write_base_step'; eauto. intros. rewrite Hdom_eq. apply Hin_dom. lia. }
  iExists (#[☠])%E, [], σ_s'. iSplitR; first done.
  iFrame "HP_t HP_s".
  iSplitR "Hsim Hs Ht Htag Hcs"; first last.
  { iSplitL; last done. iApply ("Hsim" with "Htag Ht Hs Hcs"). }

  (* we keep the base_step hypotheses to use the [base_step_wf] lemma below *)
  (* re-establish the invariants *)
  (* TODO: large parts of this, except for the tag interpretation, are similar to
    the write_public lemma *)
  iExists M_call, (<[t:=(tk_unq tk_act, ())]> M_tag), (array_tag_map l t v_t' ∪ M_t), (array_tag_map l t v_s' ∪ M_s).
  rewrite -!@insert_union_singleton_l. (* TODO remove *)
  iFrame "Hc Htag_auth Htag_t_auth Htag_s_auth".
  iSplitL "Htainted"; last iSplitL "Hpub_cid"; last iSplit; last iSplit; last iSplit; last iSplit.
  - iDestruct "Htainted" as "(%M'&Ht1&Ht2)". iExists M'. iFrame "Ht1".
    iIntros (t' l' Htl'). iDestruct ("Ht2" $! t' l' Htl') as "($&%Ht2)". iPureIntro.
    simpl. eapply disabled_tag_tree_apply_access_irreversible. 4: done. 2: done. 2: by eapply Hwf_s. done.
  - (* pub cid *)
    iApply (pub_cid_interp_preserve_sub with "Hpub_cid"); done.
  - (* state rel *) 
    rewrite /state_rel; simpl. iSplitL.
    { iPureIntro. rewrite !write_mem_dom_sane; [by rewrite Hdom_eq | done..]. }
    do 4 (iSplitL; first done). iDestruct "Hsrel" as "(_ & _ & _ & _ & _ & Hsrel)".
    iIntros (l') "%Hs".
    specialize (write_mem_lookup l v_s' σ_s.(shp)) as (Heqwm & Heq').
    specialize (write_mem_lookup_case l v_t' σ_t.(shp) l') as [(i & Hi & -> & Hwrite) | (Hi & Hwrite)].
    + destruct b.
      * (* we wrote to the location, and the written values must be related *)
        iLeft. iIntros (sc_t Hsc_t). simpl in Hsc_t. rewrite Heqwm; last lia.
        iExists (v_s' !!! i). rewrite Hwrite in Hsc_t.
        rewrite -(list_lookup_total_correct _ _ _ Hsc_t).
        iSplitR. { iPureIntro. apply list_lookup_lookup_total. apply lookup_lt_is_Some_2. lia. }
        iApply (value_rel_lookup_total with "HvrelP"). lia.
      * (* the location is protected, we can write different values *)
        iRight. iPure "HvrelP" as (Hc&Hcs). iPureIntro. exists t. eexists. split; first by rewrite lookup_insert_eq. split.
        2: { right. edestruct Hcs as (ae&Hae). 1: rewrite -Hlen_s' -Hlen_t' //.
             do 2 eexists. split; first done. exists M. done. }
        rewrite /heaplet_lookup /= lookup_insert_eq /= list_to_heaplet_nth.
        by eapply lookup_lt_is_Some_2.
    + (* unaffected location (it can not be the same block) *)
      simpl. rewrite Hwrite in Hs.
      iDestruct ("Hsrel" $! l' with "[//]") as "[Hpubl | (%t' & %Hprivl)]".
      * iLeft. rewrite /pub_loc Hwrite Heq'; first done. intros. apply Hi. lia.
      * iRight. iPureIntro. exists t'.
        destruct Hprivl as (tk' & H & H0 & H1).
        destruct (decide (t = t')) as [<- | Hne].
        { exfalso. assert (l.1 = l'.1) as Hleq.
          { destruct Htag_interp as (_&_&_&Hunq_t&_).
            destruct H0 as (?&(x&Hx&_)%bind_Some).
            eapply Hunq_t; eapply elem_of_dom_2; first done.
            eapply Hx.
          }
          rewrite /heaplet_lookup /= -Hleq Hheaplet_t /= in H0.
          destruct H0 as (x&Hx%list_to_heaplet_lookup_Some).
          rewrite Hsz1 -Hlen_s' -Hlen_t' in Hx.
          specialize (Hi (Z.to_nat (l'.2 - l.2)) (ltac:(lia))).
          apply Hi, injective_projections; first by simpl.
          simpl. lia. }
        { exists tk'. split_and!; [by rewrite lookup_insert_ne | | done].
          rewrite /heaplet_lookup /= lookup_insert_ne //.
          congruence. }
  - (* call invariant *)
    iPureIntro. destruct Hcall_interp as (Hcall_interp&Hcc2). split; last done. intros c' M' HM'_some. simpl.
    specialize (Hcall_interp c' M' HM'_some) as (Hin & Hprot).
    split; first done. intros t' L [Ht HL]%Hprot. split; first done.
    intros l' b' HlL. specialize (HL l' b' HlL).
    eapply tag_protected_preserved_by_access; [eapply Hwf_t|done| | ].
    1: rewrite Hscs_eq; apply Hin.
    eapply tag_protected_for_mono. 2: done.
    intros l0 it Hit1 Hit2 Hit3 (tk&Htk'&Hhl).
    destruct (decide (itag it = t)) as [<-|]; last first.
    + exists tk. rewrite /heaplet_lookup !lookup_insert_ne /= //. congruence.
    + rewrite /tag_is_unq lookup_insert_eq. exists tk_act. split; first done.
      rewrite /heaplet_lookup /=. destruct (decide (l0.1 = l.1)) as [Heq|?].
      * rewrite Heq lookup_insert_eq // /=.
        rewrite /heaplet_lookup /= Heq Hheaplet_t /= in Hhl. eapply elem_of_dom.
        eapply elem_of_dom in Hhl.
        erewrite list_to_heaplet_dom_1. 1: exact Hhl. lia.
      * rewrite lookup_insert_ne. 2: congruence. apply Hhl.
  - (* tag invariant *)
    iPureIntro. destruct Htag_interp as (Htag_interp & Ht_dom & Hs_dom & Hunq1 & Hunq2). split_and!; [ | | | | ]; first last.
    1-2: rewrite /dom_unique_per_tag !dom_insert_lookup_L //.
    { intros t' l' (x1&Hx1%lookup_insert_Some). simpl in Hx1.
      destruct Hx1 as [([= -> _]&_)|[Hne1 Hx1]]; first by rewrite lookup_insert_eq.
      rewrite lookup_insert_ne; first eapply (Hs_dom _ l'). 1: by eexists.
      intros ->. eapply Hne1. f_equal. eapply Hunq2; eapply elem_of_dom_2; done.
    }
    { intros t' l' (x1&Hx1%lookup_insert_Some). simpl in Hx1.
      destruct Hx1 as [([= -> _]&_)|[Hne1 Hx1]]; first by rewrite lookup_insert_eq.
      rewrite lookup_insert_ne; first eapply (Ht_dom _ l'). 1: by eexists.
      intros ->. eapply Hne1. f_equal. eapply Hunq1; eapply elem_of_dom_2; done.
    }
    simpl.
    assert (∀ (lac:loc) (sc:scalar), l.1 = lac.1 → list_to_heaplet v_s' l.2 !! lac.2 = Some sc →
          loc_controlled lac t (tk_unq tk_act) sc σ_s') as Hlct_s.
    { intros lac sc H1 H2.
      assert (∃ sc_o, heaplet_lookup M_s (t, lac) = Some sc_o) as (sc_o & Hsco).
      { rewrite /heaplet_lookup /= -H1 Hheaplet_s /=.
        destruct (list_to_heaplet v_s l.2 !! lac.2) eqn:Heq; first by eexists.
        exfalso. eapply list_to_heaplet_lookup_Some in H2. eapply list_to_heaplet_lookup_None in Heq.
        lia. }
      eapply loc_controlled_write_becomes_active.
      1: exact Htree_s. 1-2: rewrite /=; by destruct l.
      1: done. 1: done. 1: congruence. 1: done. 1: done.
      destruct (Htag_interp _ _ Htk) as (_ & _ & _ & _ & Hcontrol_s' & _). by eapply Hcontrol_s'. }
    pose (σ_t' := (mkState (write_mem l v_t' (shp σ_t)) trs_t' (scs σ_t) (snp σ_t) (snc σ_t))).
    assert (∀ (lac:loc) (sc:scalar), l.1 = lac.1 → list_to_heaplet v_t' l.2 !! lac.2 = Some sc →
          loc_controlled lac t (tk_unq tk_act) sc σ_t') as Hlct_t.
    { intros lac sc H1 H2.
      assert (∃ sc_o, heaplet_lookup M_t (t, lac) = Some sc_o) as (sc_o & Hsco).
      { rewrite /heaplet_lookup /= -H1 Hheaplet_t /=.
        destruct (list_to_heaplet v_t l.2 !! lac.2) eqn:Heq; first by eexists.
        exfalso. eapply list_to_heaplet_lookup_Some in H2. eapply list_to_heaplet_lookup_None in Heq.
        lia. }
      rewrite Hscs_eq in Htree_t. eapply loc_controlled_write_becomes_active.
      1: exact Htree_t. 1-2: rewrite /=; by destruct l.
      1: done. 1: done. 1: congruence. 1: done. 1: done.
      destruct (Htag_interp _ _ Htk) as (_ & _ & _ & Hcontrol_t' & _). by eapply Hcontrol_t'. }
    intros t' tk' [(<- & [= <-])|(Hne & Ht)]%lookup_insert_Some.
    { destruct (Htag_interp _ _ Htk) as (Hvalid_s & Hvalid_t & Hlocal & Hcontrol_t' & Hcontrol_s' & Hagree).
      split_and!; [done|done|..]; last first.
      - eapply dom_agree_on_tag_update_same; first done.
        apply list_to_heaplet_dom_1; congruence.
      - intros lac sc (csv&[(Heq1&<-)|(Hne1&Hne2)]%lookup_insert_Some&H2)%bind_Some; last first.
        { exfalso. eapply Hne1. simpl. f_equal.
          eapply Hunq2; eapply elem_of_dom_2; done. }
        rewrite /= in Heq1,H2. injection Heq1 as Hlac.
        eapply Hlct_s; done.
      - intros lac sc (csv&[(Heq1&<-)|(Hne1&Hne2)]%lookup_insert_Some&H2)%bind_Some; last first.
        { exfalso. eapply Hne1. simpl. f_equal.
          eapply Hunq1; eapply elem_of_dom_2; done. }
        rewrite /= in Heq1,H2. injection Heq1 as Hlac.
        eapply Hlct_t; done.
      - done. }
    { (* we are a different tag *)
      destruct (Htag_interp _ _ Ht) as (Hv1&Hv2&Hlocal&Hlc1&Hlc2&Hagr).
      split_and!; try done; first last.
      - by eapply dom_agree_on_tag_upd_ne.
      - intros lw sc. rewrite (heaplet_lookup_raw_insert_ne (t,l) (t',lw)) //. 2: simpl; congruence.
        intros HM_s. specialize (Hlc2 _ _ HM_s).
        destruct (decide (lw.1 = l.1 ∧ (l.2 ≤ lw.2 < l.2 + length v_s')%Z)) as [Hin|Hout].
        2: { eapply loc_controlled_access_outside; try done.
             rewrite /σ_s' /=write_mem_lookup_outside //. }
        assert (∃ sc, list_to_heaplet v_s' l.2 !! lw.2 = Some sc) as (ssc&Hssc).
        { destruct (list_to_heaplet v_s' l.2 !! lw.2) eqn:Hhl; try by eexists.
          eapply list_to_heaplet_lookup_None in Hhl. lia. }
        rewrite /loc_controlled.
        eapply loc_controlled_write_invalidates_others.
        1: done. 1: subst σ_s'; by destruct l. 1: done. 1-2: apply Hin.
        1: done. 2: done. done.
      - intros lw sc. rewrite (heaplet_lookup_raw_insert_ne (t,l) (t',lw)) //. 2: simpl; congruence.
        intros HM_s. specialize (Hlc1 _ _ HM_s).
        destruct (decide (lw.1 = l.1 ∧ (l.2 ≤ lw.2 < l.2 + length v_s')%Z)) as [Hin|Hout].
        2: { eapply loc_controlled_access_outside; try done.
             rewrite /= write_mem_lookup_outside // Hlen_t' //. }
        assert (∃ sc, list_to_heaplet v_t' l.2 !! lw.2 = Some sc) as (ssc&Hssc).
        { destruct (list_to_heaplet v_t' l.2 !! lw.2) eqn:Hhl; try by eexists.
          eapply list_to_heaplet_lookup_None in Hhl. lia. }
        intros Hpre. exfalso. revert Hpre.
        eapply loc_controlled_write_invalidates_others. 
        1: by rewrite Hscs_eq in Htree_t. 1: subst σ_t'; by destruct l. 1: done. 1-2: apply Hin.
        1: done. 2: done. done.
      - intros ->. destruct Hlocal as (Hl1&Hl2); first done. split;
          intros ? MM [([= <- <-]&H)|(Hne2&H)]%lookup_insert_Some.
        1, 3: subst MM; setoid_rewrite list_to_heaplet_empty_length; congruence.
        1: by eapply Hl1. 1: by eapply Hl2.
    }
  - (* source state wf *)
    iPureIntro. eapply base_step_wf; done.
  - (* target state wf *)
    iPureIntro. eapply base_step_wf; done.
Qed.

Lemma sim_write_activate_unprotected π l t sz tkk v_t v_s v_t' v_s' Φ :
  length v_t = sz →
  length v_s = sz →
  t $$ tk_unq tkk -∗
  l ↦t∗[tk_unq tkk]{t} v_t -∗
  l ↦s∗[tk_unq tkk]{t} v_s -∗
  (* crucial: without protectors, we need to write related values, as the locations
    will need to be public in the state_rel -- after all, there is no protector, so it can't be private! *)
  value_rel v_t' v_s' -∗
  (t $$ tk_unq tk_act -∗ l ↦t∗[tk_unq tk_act]{t} v_t' -∗ l ↦s∗[tk_unq tk_act]{t} v_s' -∗ #[☠] ⪯{π} #[☠] [{ Φ }]) -∗
  Write (Place l t sz) #v_t' ⪯{π} Write (Place l t sz) #v_s' [{ Φ }].
Proof.
  iIntros (H1 H2) "H3 H4 H5 H6 H7".
  (* pick dummy values since these are unused if b=true *)
  iApply (sim_write_activate_general true 0%nat ∅ with "H3 H4 H5 [H6] [H7]").
  1: exact H1. 1: exact H2. 1: by simpl.
  simpl. iIntros "H8 H9 H10 _". iApply ("H7" with "H8 H9 H10").
Qed.

Lemma sim_write_activate_protected π l t sz tkk v_t v_s v_t' v_s' Φ c M:
  length v_t = sz →
  length v_s = sz →
  length v_t' = length v_s' →
  (∀ i: nat, (i < sz)%nat → ∃ ae, call_set_in M t (l +ₗ i) (EnsuringAccess ae)) →
  t $$ tk_unq tkk -∗
  l ↦t∗[tk_unq tkk]{t} v_t -∗
  l ↦s∗[tk_unq tkk]{t} v_s -∗
  (* with a protector, we don't need to write related values *)
  c @@ M -∗
  (t $$ tk_unq tk_act -∗ l ↦t∗[tk_unq tk_act]{t} v_t' -∗ l ↦s∗[tk_unq tk_act]{t} v_s' -∗ c @@ M -∗ #[☠] ⪯{π} #[☠] [{ Φ }]) -∗
  Write (Place l t sz) #v_t' ⪯{π} Write (Place l t sz) #v_s' [{ Φ }].
Proof.
  iIntros (H1 H2 H3 H4) "H5 H6 H7 H8 H9".
  iApply (sim_write_activate_general false c M with "H5 H6 H7 [H8] H9").
  1: exact H1. 1: exact H2.
  simpl. iFrame. iPureIntro. done.
Qed.

End lifting.
