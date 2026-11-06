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
From simuliris.tree_borrows.trees_equal Require Import trees_equal_source_read trees_equal_transitivity trees_equal_preserved_by_access_base disabled_tag_rejects_read_precisely.

(** * Simulation lemmas using the ghost state for proving optimizations *)

Section lifting.
Context `{!sborGS Σ}.
Implicit Types P Q : iProp Σ.
Implicit Types Φ : expr → expr → iProp Σ.
Implicit Types σ σ_s σ_t : state.
Implicit Types r r_s r_t : result.
Implicit Types l : loc.
Implicit Types f : fname.

(** ** Copy lemma *)

Lemma source_copy_any v_t v_rd sz l_hl l_rd t π Ψ tk :
  sz ≠ 0%nat → (* if it is 0, use the zero-sized read lemma *)
  read_range l_rd.2 sz (list_to_heaplet v_t l_hl.2) = Some v_rd →
  l_hl.1 = l_rd.1 →
  t $$ tk -∗
  l_hl ↦s∗[tk]{t} v_t -∗
  (∀ v_res, l_hl ↦s∗[tk]{t} v_t -∗ t $$ tk -∗ (⌜v_res = v_rd⌝) -∗ source_red #v_res π Ψ)%E -∗
  source_red (Copy (Place l_rd t sz)) π Ψ.
Proof.
  iIntros (Hnz Hread Hsameblk) "Htag Hs Hsim". eapply read_range_length in Hread as HH. subst sz.
  iApply source_red_lift_base_step. iIntros (P_t σ_t P_s σ_s T_s K_s) "((HP_t & HP_s & Hbor)&[%Ht_s %Hpoolsafe])".
  iPoseProof (bor_interp_get_pure with "Hbor") as "%Hp".
  destruct Hp as (Hstrs_eq & Hsnp_eq & Hsnc_eq & Hscs_eq & Hwf_s & Hwf_t & Hdom_eq).
  iModIntro. iDestruct "Hbor" as "(%M_call & %M_tag & %M_t & %M_s & Hbor)".
  eapply pool_safe_implies in Ht_s as Hfoo. 2: done.
  destruct Hfoo as [(v_rd'&Hv_rd&Hcont&Hreadsome&_)|(v_nil&Hread_nil&Hiszero)].
  2: lia.
(*  { (* poison *)
    pose proof Happly_none as Hn2.
    rewrite /apply_within_trees in Hn2.
    rewrite /trees_contain /trees_at_block in Hcont.
    destruct (strs σ_s !! l_rd.1) as [tr|] eqn:Heq; last done.
    simpl in *. eapply bind_None in Hn2 as [Hn2|(x1&Hx1&Hx2)]. 2: done.
    assert (tree_unique t tr) as (it&Hit)%unique_implies_lookup by by eapply Hwf_s.
    iDestruct "Hbor" as "((Hc & Htag_auth & Htag_t_auth & Htag_s_auth) & Htainted & Hpub_cid & #Hsrel & %Hcall_interp & %Htag_interp & _ & _)".
    iPoseProof (tkmap_lookup with "Htag_auth Htag") as "%Htag".
    iPoseProof (ghost_map_lookup with "Htag_s_auth Hs") as "%Hs".
    eapply read_fails_disabled_tag_or_prot_act_child in Hn2 as (l&Hl&Hn2). 2-4: by eapply Hwf_s. 2: done.
    2: { intros l Hl Him. destruct (Htag_interp) as (H1&_).
         specialize (H1 _ _ Htag) as (_&_&_&H2&H3&_).
         specialize (H3 (l_rd.1, l)). rewrite /range'_contains /= in Hl.
         rewrite /heaplet_lookup /= -Hsameblk /= Hs /= in H3.
         assert (∃ (il:nat), l = l_rd.2 + il) as (il&->).
         { exists (Z.to_nat (l - l_rd.2)). lia. }
         assert (il < length v_rd)%nat as (sc&Hsc)%lookup_lt_is_Some_2 by lia.
         eapply read_range_lookup_nth in Hread. 2: done.
         specialize (H3 _ Hread).
         eapply bor_state_own_on_not_reservedim. 5: exact H3. 1: done. 2: done. 2: done. 1: congruence. }
    rewrite /range'_contains /= in Hl.
    destruct Hn2 as [Hn2|(Hn2&_)]. 
    2: { destruct (Htag_interp) as (H1&_).
         specialize (H1 _ _ Htag) as (_&_&_&H2&H3&_).
         specialize (H3 (l_rd.1, l)).
         rewrite /heaplet_lookup /= -Hsameblk /= Hs /= in H3.
         assert (∃ (il:nat), l = l_rd.2 + il) as (il&->).
         { exists (Z.to_nat (l - l_rd.2)). lia. }
         assert (il < length v_rd)%nat as (sc&Hsc)%lookup_lt_is_Some_2 by lia.
         eapply read_range_lookup_nth in Hread. 2: done.
         specialize (H3 _ Hread).
         eapply bor_state_own_no_active_child in Hn2. 2,3: done. 2: eapply Hit.
         2: rewrite -Hsameblk; exact H3. done. }
    iExists _, _. iSplit.
    { iPureIntro. destruct l_rd. econstructor 2. 1: by eapply FailedCopyBS.
      econstructor. 2: done. rewrite /trees_contain /trees_at_block /= Heq //. }
    iMod (tag_tainted_interp_insert _ _ (l_rd.1, l) with "Htainted") as "(Htainted&#Hpoison)".
    { split. 2: rewrite /= Heq; left; exact Hn2.
      destruct (Htag_interp) as (H1&_).
      specialize (H1 _ _ Htag) as (_&Hx&_). rewrite /tag_valid in Hx. lia. }
    iModIntro. iFrame "HP_t HP_s". iSpecialize ("Hsim" $! (replicate (length v_rd) _) with "Hs Htag []").
    { iRight. iExists (Z.to_nat (l - l_rd.2)). rewrite length_replicate. iSplit. 1: iPureIntro; split; last done.
      1: simpl; lia. simpl. assert ((l_rd +ₗ Z.to_nat (l - l_rd.2) = (l_rd.1, l))) as ->. 2: done.
      rewrite /shift_loc /=. simpl. f_equal. lia. }
    1: iSplitR "Hsim"; last by iApply "Hsim".
    do 4 iExists _; destruct σ_s; iFrame. iFrame "Hsrel". done. } *)
  iPoseProof (bor_interp_readN_source_after_accesss with "Hbor Hs Htag") as "(%it&%tr&%Hit&%Htr&%Hown)".
  1: exact Hread. 1: done. 1: done. 1: done. 1: exact Hreadsome.
  opose proof* (read_range_list_to_heaplet_read_memory_strict) as READ_MEM. 1: exact Hread. 1: done.
  { intros i Hi. by eapply Hown. }
  destruct l_hl as [blk off_hl], l_rd as [blk2 off_rd]; simpl in *; subst blk2.
  odestruct (bor_state_own_enables_read false (off_rd, length v_rd)) as (Hcontain&trs'&Htrs').
  1: exact Hwf_s.
  { intros l (Hl1&Hl2); simpl in *. exists it, tr. do 2 (split; first done). assert (∃ (i:nat), l = off_rd + i) as (ii&Hii).
    1: exists (Z.to_nat (l - off_rd)); lia. subst l. eapply Hown. lia. } 1: simpl; lia.
  iExists _, _.
  eassert (base_step P_s (Copy (Place (blk, off_rd) t (length v_rd))) σ_s _ _ []) as Hstep.
  { eapply copy_base_step'. 1: done. 2: exact READ_MEM. 2: exact Htrs'. done. }
  iSplit; first done.
  assert (trees_equal (scs σ_s) Forwards trs' (strs σ_t)) as Hstrs_eq'.
  { eapply trees_equal_trans. 9: eapply Hstrs_eq.
    1,3,5,7: by eapply Hwf_s.
    1-3: eapply base_step_wf in Hwf_s; last done. 1-3: by eapply Hwf_s.
    change Forwards with (direction_flip Backwards).
    eapply trees_equal_sym.
    eapply apply_within_trees_lift. 2: exact Htrs'. 1: by eapply Hwf_s. simpl.
    intros trX tr' HH1 HH2 HH3. simpl in *. assert (tr = trX) as <- by congruence.
    eapply tree_equal_asymmetric_read_source.
    4: eapply HH3. 2: done. 1: by eapply Hwf_s.
    eapply source_only_read_pre_from_bor_state_own. 3: done. 2: done. 1: done. intros off (Ho1&Ho2); simpl in *.
    assert (∃ (i:nat), off = off_rd + i) as (i&->) by (exists (Z.to_nat (off - off_rd)); lia).
    eapply Hown. 1: lia. }

  iDestruct "Hbor" as "((Hc & Htag_auth & Htag_t_auth & Htag_s_auth) & Htainted & Hpub_cid & #Hsrel & %Hcall_interp & %Htag_interp & _ & _)".
  iPoseProof (tkmap_lookup with "Htag_auth Htag") as "%Htag".
  iPoseProof (ghost_map_lookup with "Htag_s_auth Hs") as "%Hs".

  iModIntro.
  iSplitR "Hs Htag Hsim".
  2: { iApply ("Hsim" with "Hs Htag"). by iPureIntro. }
  iFrame "HP_t HP_s". iExists M_call, M_tag, M_t, M_s.
  iFrame "Hc Htag_auth Htag_t_auth Htag_s_auth".
  iSplitL "Htainted"; last iSplitL "Hpub_cid". 3: iSplit; last iSplit; last (iPureIntro; split_and!).
  - iDestruct "Htainted" as "(%M'&Ht1&Ht2)". iExists M'. iFrame "Ht1".
    iIntros (t' l' Htl'). iDestruct ("Ht2" $! t' l' Htl') as "($&%Ht2)". iPureIntro.
    simpl. eapply disabled_tag_tree_apply_access_irreversible. 4: done. 2: done. 2: by eapply Hwf_s. done.
  - iApply (pub_cid_interp_preserve_sub with "Hpub_cid"); done.
  - repeat (iSplit; first done).
    simpl. iIntros (l) "Hs". iPoseProof (state_rel_pub_or_priv with "Hs Hsrel") as "$".
  - done.
  - (* tag invariant *)
    destruct Htag_interp as (Htag_interp & Ht_dom & Hs_dom & Hunq1 & Hunq2). split_and!; [ | done..].
    intros t' tk' Htk_some. destruct (Htag_interp _ _ Htk_some) as (Hsnp_lt_t & Hsnp_lt_s & Hlocal & Hctrl_t & Hctrl_s & Hag).
    split_and!; [ done | done | | | | done ].
    + done.
    + eapply Hctrl_t.
    + intros l sc_s Hsc_s. eapply loc_controlled_read_preserved_everywhere.
      1: eapply Htrs'. 1-4: done.
      by eapply Hctrl_s.
  - eapply (base_step_wf P_s). 2: exact Hwf_s. eapply copy_base_step'. 1: done. 2: exact READ_MEM. 2: exact Htrs'. done.
  - done.
Qed.
(*
Lemma source_copy_poison v_t v_rd sz l_hl l_rd t π Ψ tk v_read_earlier :
  sz ≠ 0%nat → (* if it is 0, it will not be poison *)
  read_range l_rd.2 sz (list_to_heaplet v_t l_hl.2) = Some v_rd →
  l_hl.1 = l_rd.1 →
  ispoison v_read_earlier l_rd t sz -∗
  t $$ tk -∗
  l_hl ↦s∗[tk]{t} v_t -∗
  (∀ v_res, l_hl ↦s∗[tk]{t} v_t -∗ t $$ tk -∗ ispoison v_res l_rd t sz -∗ source_red #v_res π Ψ)%E -∗
  source_red (Copy (Place l_rd t sz)) π Ψ.
Proof.
  iIntros (_ Hread Hsameblk ) "#Hpoison Htag Hs Hsim". eapply read_range_length in Hread as HH. subst sz.
  iApply source_red_lift_base_step. iIntros (P_t σ_t P_s σ_s T_s K_s) "((HP_t & HP_s & Hbor)&[%Ht_s %Hpoolsafe])".
  iPoseProof (bor_interp_get_pure with "Hbor") as "%Hp".
  destruct Hp as (Hstrs_eq & Hsnp_eq & Hsnc_eq & Hscs_eq & Hwf_s & Hwf_t & Hdom_eq).
  iModIntro. iDestruct "Hbor" as "(%M_call & %M_tag & %M_t & %M_s & Hbor)".
  iDestruct "Hpoison" as "(%i&%Hi&#Hpoison)".
  eapply pool_safe_implies in Ht_s as Hfoo. 2: done.
  destruct Hi as (Hi&->). rewrite length_replicate in Hi.
  destruct Hfoo as [(v_rd'&Hv_rd&Hcont&Hreadsome&_)|[(v_nil&Hread_nil&Hiszero)|(Hcont&Happly_none&Hmemsome)]]; last first.
  2: lia.
  - iExists _, _. iSplit.
    { iPureIntro. destruct l_rd. econstructor 2. 1: by eapply FailedCopyBS.
      econstructor; done. }
    iModIntro. iFrame "HP_t HP_s". iSpecialize ("Hsim" $! _ with "Hs Htag []"); last first.
    1: iSplitR "Hsim"; last by iApply "Hsim".
    1: do 4 iExists _; destruct σ_s; iApply "Hbor".
    iExists i. iFrame "Hpoison". rewrite length_replicate. iPureIntro. split; last done. lia.
  - iDestruct "Hbor" as "((Hc & Htag_auth & Htag_t_auth & Htag_s_auth) & Htainted & Hpub_cid & #Hsrel & %Hcall_interp & %Htag_interp & _ & _)".
    iPoseProof (tag_tainted_interp_lookup with "Hpoison Htainted") as "%Hpoison".
    exfalso. rewrite /trees_contain /trees_at_block /= in Hcont.
    destruct Hpoison as (Hv&Hpoison). simpl in Hpoison.
    destruct (strs σ_s !! l_rd.1) as [tr|] eqn:Heq. 2: done.
    destruct Hpoison as [HH|Hc]; last done.
    rewrite /apply_within_trees /= Heq /= in Hreadsome.
    opose proof (disabled_tag_no_access _ false _ AccessRead _ (l_rd.2 + i) (l_rd.2, length v_rd) _ HH _) as HNone.
    1: by eapply Hwf_s. 1: split; simpl in *; lia.
    rewrite /memory_access HNone in Hreadsome. simpl in Hreadsome. by destruct Hreadsome.
Qed. *)


Lemma source_copy_in_simulation v_t v_rd v_tgt sz l_hl l_rd t π Ψ tk :
  sz ≠ 0%nat → (* if it is 0, use the zero-sized read lemma *)
  read_range l_rd.2 sz (list_to_heaplet v_t l_hl.2) = Some v_rd →
  l_hl.1 = l_rd.1 →
  will_read_in_simulation v_rd v_tgt l_rd t -∗
  t $$ tk -∗
  l_hl ↦s∗[tk]{t} v_t -∗
  (∀ v_res, l_hl ↦s∗[tk]{t} v_t -∗ t $$ tk -∗ value_rel v_tgt v_res -∗ source_red #v_res π Ψ)%E -∗
  source_red (Copy (Place l_rd t sz)) π Ψ.
Proof.
  iIntros (Hsz Hrr Hhl).
  eapply read_range_length in Hrr as Hszlen.
  iIntros "#Hrel Htk Hhl Hsim".
  rewrite /will_read_in_simulation.
  - iPoseProof (value_rel_length with "Hrel") as "%Hlen".
    iApply (source_copy_any with "Htk Hhl [Hsim]"). 1-3: done.
    iIntros (v_res) "Hhl Htk ->";
      iApply ("Hsim" with "Hhl Htk").
    + done. (*
    + rewrite Hp2. iApply big_sepL2_forall. iSplit. 1: iPureIntro; rewrite length_replicate; lia.
      iIntros (k sc1 sc2 _ (->&HH2)%lookup_replicate_1). iApply sc_rel_source_poison.
  - subst sz. iDestruct "Hpoison" as "(%Hlen&Hpoison)".
    iApply (source_copy_poison with "[] Htk Hhl [Hsim]"). 1-3: done.
    1: rewrite Hlen; done.
    iIntros (v_res) "Hhl Htk #(%i&(%Hp1&%Hp2)&Hpoison2)".
    iApply ("Hsim" with "Hhl Htk").
    rewrite Hp2. iApply big_sepL2_forall. iSplit. 1: iPureIntro; rewrite length_replicate; lia.
    iIntros (k sc1 sc2 _ (->&HH2)%lookup_replicate_1). iApply sc_rel_source_poison. *)
Qed.


End lifting.