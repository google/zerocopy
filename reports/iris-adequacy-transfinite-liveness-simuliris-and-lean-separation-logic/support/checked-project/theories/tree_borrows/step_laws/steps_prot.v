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
From simuliris.tree_borrows.trees_equal Require Import trees_equal_asymmetric_prot trees_equal_transitivity trees_equal_preserved_by_access_base.

(** * Simulation lemmas using the ghost state for proving optimizations *)

Section lifting.
Context `{!sborGS Σ}.
Implicit Types P Q : iProp Σ.
Implicit Types Φ : expr → expr → iProp Σ.
Implicit Types σ σ_s σ_t : state.
Implicit Types r r_s r_t : result.
Implicit Types l : loc.
Implicit Types f : fname.

(** ** Copy lemmas *)
(* works with any tag *)
Lemma target_copy_protected v_t v_rd sz l_hl l_rd t Ψ c tk M L :
  sz ≠ 0%nat → (* if it is 0, use the zero-sized read lemma *)
  read_range l_rd.2 sz (list_to_heaplet v_t l_hl.2) = Some v_rd →
  l_hl.1 = l_rd.1 →
  (∀ off, range'_contains (l_rd.2, sz) off → ∃ ae, L !! (l_rd.1, off) = Some (EnsuringAccess ae)) →
  M !! t = Some L →
  c @@ M -∗
  t $$ tk -∗
  l_hl ↦t∗[tk]{t} v_t -∗
  (l_hl ↦t∗[tk]{t} v_t -∗ t $$ tk -∗ c @@ M -∗ target_red #v_rd Ψ)%E -∗
  target_red (Copy (Place l_rd t sz)) Ψ.
Proof.
  iIntros (Hnz Hread Hsameblk Hprot1 Hprot2) "Hprot3 Htag Ht Hsim". eapply read_range_length in Hread as HH. subst sz.
  iApply target_red_lift_base_step. iIntros (P_t σ_t P_s σ_s ?) "(HP_t & HP_s & Hbor)".
  iPoseProof (bor_interp_get_pure with "Hbor") as "%Hp".
  destruct Hp as (Hstrs_eq & Hsnp_eq & Hsnc_eq & Hscs_eq & Hwf_s & Hwf_t & Hdom_eq).
  iModIntro. iDestruct "Hbor" as "(%M_call & %M_tag & %M_t & %M_s & Hbor)".
  iPoseProof (bor_interp_readN_target_protected with "Hbor Hprot3 Ht Htag") as "(%it&%tr&%Hit&%Htr&%Hprot&%Hown)".
  1: exact Hread. 1: done. 1: done. 1: done. 1: done.
  opose proof* (read_range_list_to_heaplet_read_memory_strict) as READ_MEM. 1: exact Hread. 1: done.
  { intros i Hi. by eapply Hown. }
  destruct l_hl as [blk off_hl], l_rd as [blk2 off_rd]; simpl in *; subst blk2.
  odestruct (bor_state_own_enables_read false (off_rd, length v_rd)) as (Hcontain&trs'&Htrs').
  1: exact Hwf_t.
  { intros l (Hl1&Hl2); simpl in *. exists it, tr. do 2 (split; first done). assert (∃ (i:nat), l = off_rd + i) as (ii&Hii).
    1: exists (Z.to_nat (l - off_rd)); lia. subst l. eapply Hown. lia. } 1: simpl; lia.
  iSplit.
  { iPureIntro. do 3 eexists. eapply copy_base_step'. 1: done. 2: exact READ_MEM. 2: exact Htrs'. done. }
  iIntros (??? Hstep). pose proof Hstep as Hstep2.
  eapply head_copy_inv in Hstep2 as (->&trs''&v'&->&->&Hreadv'&[(_&Htrs''&Hnon)|(Hzero&->&->)]).
  2: done.
  assert (trs'' = trs') as ->.
  { rewrite /memory_access Htrs' in Htrs''. congruence. }
  assert (v_rd = v') as -> by congruence.
  assert (trees_equal (scs σ_s) Forwards (strs σ_s) trs') as Hstrs_eq'.
  { eapply trees_equal_trans. 8: eapply Hstrs_eq.
    1,7,8: rewrite Hscs_eq. 1,2,5,7: by eapply Hwf_t. 2-4: by eapply Hwf_s.
    eapply apply_within_trees_lift. 2: exact Htrs'. 1: by eapply Hwf_t. simpl.
    intros trX tr' HH1 HH2 HH3. simpl in *. assert (tr = trX) as <- by congruence.
    eapply tree_equal_asymmetric_read_protected.
    5: eapply HH3. 2: done. 1: by eapply Hwf_t. 1: done.
    eapply asymmetric_read_prot_pre_from_bor_state_own. 3: done. 2: done. 1: done. intros off (Ho1&Ho2); simpl in *.
    assert (∃ (i:nat), off = off_rd + i) as (i&->) by (exists (Z.to_nat (off - off_rd)); lia).
    eapply Hown. 1: lia. }

  iDestruct "Hbor" as "((Hc & Htag_auth & Htag_t_auth & Htag_s_auth) & Htainted & Hpub_cid & #Hsrel & %Hcall_interp & %Htag_interp & _ & _)".
  iPoseProof (tkmap_lookup with "Htag_auth Htag") as "%Htag".
  iPoseProof (ghost_map_lookup with "Htag_t_auth Ht") as "%Ht".
  iPoseProof (ghost_map_lookup with "Hc Hprot3") as "%Hprot3".

  iModIntro. iSplit; first done.
  iSplitR "Ht Htag Hprot3 Hsim".
  2: iApply ("Hsim" with "Ht Htag Hprot3").
  iFrame "HP_t HP_s". iExists M_call, M_tag, M_t, M_s.
  iFrame "Hc Htag_auth Htag_t_auth Htag_s_auth".
  iSplitL "Htainted"; last iSplitL "Hpub_cid". 3: iSplit; last iSplit; last (iPureIntro; split_and!).
  - done.
  - iApply (pub_cid_interp_preserve_sub with "Hpub_cid"); done.
  - repeat (iSplit; first done).
    simpl. iIntros (l) "Hs". iPoseProof (state_rel_pub_or_priv with "Hs Hsrel") as "$".
  - (* call invariant *)
    iPureIntro. destruct Hcall_interp as (Hcall_interp&Hcc2); split; last done.
    intros c' M' HM'_some.
    specialize (Hcall_interp _ M' HM'_some) as (Hin & Hprot').
    split; first by apply Hin. intros pid L' HL_some. specialize (Hprot' _ _ HL_some) as [Hpid Hprot'].
    split; first by apply Hpid. intros l b Hin_l.
    specialize (Hprot' l b Hin_l).
    eapply (tag_protected_preserved_by_access). 2: apply Htrs'. 1: apply Hwf_t. all: done.
  - (* tag invariant *)
    destruct Htag_interp as (Htag_interp & Ht_dom & Hs_dom & Hunq1 & Hunq2). split_and!; [ | done..].
    intros t' tk' Htk_some. destruct (Htag_interp _ _ Htk_some) as (Hsnp_lt_t & Hsnp_lt_s & Hlocal & Hctrl_t & Hctrl_s & Hag).
    split_and!; [ done | done | | | | done ].
    + done.
    + intros l sc_t Hsc_t. eapply loc_controlled_read_preserved_everywhere.
      1: eapply Htrs'. 1: done. 1: by rewrite -Hscs_eq. 1-2: done.
      by eapply Hctrl_t.
    + eapply Hctrl_s.
  - done.
  - eapply base_step_wf; done.
Qed.

Lemma source_copy_protected v_t v_rd sz l_hl l_rd t π Ψ c tk M L :
  sz ≠ 0%nat → (* if it is 0, use the zero-sized read lemma *)
  read_range l_rd.2 sz (list_to_heaplet v_t l_hl.2) = Some v_rd →
  l_hl.1 = l_rd.1 →
  (∀ off, range'_contains (l_rd.2, sz) off → ∃ ae, L !! (l_rd.1, off) = Some (EnsuringAccess ae)) →
  M !! t = Some L →
  c @@ M -∗
  t $$ tk -∗
  l_hl ↦s∗[tk]{t} v_t -∗
  (l_hl ↦s∗[tk]{t} v_t -∗ t $$ tk -∗ c @@ M -∗ source_red #v_rd π Ψ)%E -∗
  source_red (Copy (Place l_rd t sz)) π Ψ.
Proof.
  iIntros (Hnz Hread Hsameblk Hprot1 Hprot2) "Hprot3 Htag Hs Hsim". eapply read_range_length in Hread as HH. subst sz.
  iApply source_red_lift_base_step. iIntros (P_t σ_t P_s σ_s T_s K_s) "((HP_t & HP_s & Hbor)&%Ht_s)".
  iPoseProof (bor_interp_get_pure with "Hbor") as "%Hp".
  destruct Hp as (Hstrs_eq & Hsnp_eq & Hsnc_eq & Hscs_eq & Hwf_s & Hwf_t & Hdom_eq).
  iModIntro. iDestruct "Hbor" as "(%M_call & %M_tag & %M_t & %M_s & Hbor)".
  iPoseProof (bor_interp_readN_source_protected with "Hbor Hprot3 Hs Htag") as "(%it&%tr&%Hit&%Htr&%Hprot&%Hown)".
  1: exact Hread. 1: done. 1: done. 1: done. 1: done.
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
    eapply tree_equal_asymmetric_read_protected.
    5: eapply HH3. 2: done. 1: by eapply Hwf_s. 1: done.
    eapply asymmetric_read_prot_pre_from_bor_state_own. 3: done. 2: done. 1: done. intros off (Ho1&Ho2); simpl in *.
    assert (∃ (i:nat), off = off_rd + i) as (i&->) by (exists (Z.to_nat (off - off_rd)); lia).
    eapply Hown. 1: lia. }

  iDestruct "Hbor" as "((Hc & Htag_auth & Htag_t_auth & Htag_s_auth) & Htainted & Hpub_cid & #Hsrel & %Hcall_interp & %Htag_interp & _ & _)".
  iPoseProof (tkmap_lookup with "Htag_auth Htag") as "%Htag".
  iPoseProof (ghost_map_lookup with "Htag_s_auth Hs") as "%Hs".
  iPoseProof (ghost_map_lookup with "Hc Hprot3") as "%Hprot3".

  iModIntro.
  iSplitR "Hs Htag Hprot3 Hsim".
  2: iApply ("Hsim" with "Hs Htag Hprot3").
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

(** ** Write *)

Lemma target_write_protected_active v_t v_wr sz l_hl l_rd v_t' t Ψ c M L :
  sz ≠ 0%nat → (* if it is 0, use the zero-sized write lemma *)
  write_range l_hl.2 l_rd.2 v_wr v_t = Some v_t' →
  l_hl.1 = l_rd.1 →
  sz = length v_wr →
  (∀ off, range'_contains (l_rd.2, sz) off → ∃ ae, L !! (l_rd.1, off) = Some (EnsuringAccess ae)) →
  M !! t = Some L →
  c @@ M -∗
  t $$ tk_unq tk_act -∗
  l_hl ↦t∗[tk_unq tk_act]{t} v_t -∗
  (l_hl ↦t∗[tk_unq tk_act]{t} v_t' -∗ t $$ tk_unq tk_act -∗ c @@ M -∗ target_red #[☠] Ψ)%E -∗
  target_red (Write (Place l_rd t sz) #v_wr) Ψ.
Proof.
  iIntros (Hnz Hwrite Hsameblk Hlen HL HM) "Hc Htag Ht Hsim". eapply write_range_same_length in Hwrite as Hlength. subst sz.
  opose proof Hwrite as HH.
  eapply mk_is_Some, write_range_is_Some_read_range in HH as [vlsold Hreadsome]. eapply read_range_length in Hreadsome as Holdlen.
  iApply target_red_lift_base_step. iIntros (P_t σ_t P_s σ_s ?) "(HP_t & HP_s & Hbor)".
  iPoseProof (bor_interp_get_pure with "Hbor") as "%Hp".
  destruct Hp as (Hstrs_eq & Hsnp_eq & Hsnc_eq & Hscs_eq & Hwf_s & Hwf_t & Hdom_eq).
  iModIntro. iDestruct "Hbor" as "(%M_call & %M_tag & %M_t & %M_s & Hbor)".
  iPoseProof (bor_interp_readN_target_protected with "Hbor Hc Ht Htag") as "(%it&%tr&%Hit&%Htr&%Hprot&%Hown)".
  1: exact Hreadsome. 1: done. 1: done. 1: done. 1: congruence.
  opose proof* (write_range_write_memory_smaller) as (hp'&WRITE_MEM&Hd'). 1: exact Hwrite. 1: done.
  { rewrite -Holdlen. intros i Hx. pose proof Hx as (H1&H2)%Hown. erewrite H2. by eapply lookup_lt_is_Some_2. }
  destruct l_hl as [blk off_hl], l_rd as [blk2 off_rd]; simpl in *; subst blk2.
  eapply mk_is_Some in Hwrite as Hrangebounds. rewrite -write_range_valid_iff in Hrangebounds.
  odestruct (bor_state_own_unq_act_enables_write false (off_rd, length v_wr)) as (trs'&Htrs').
  1: exact Hwf_t.
  { intros l (Hl1&Hl2); simpl in *. exists it, tr. do 2 (split; first done). assert (∃ (i:nat), l = off_rd + i) as (ii&Hii).
    1: exists (Z.to_nat (l - off_rd)); lia. subst l. eapply Hown. lia. }
  2: done. 1: rewrite /trees_lookup /trees_at_block Hit. 1: by eexists.
  assert (∀ n : nat, (n < length v_wr)%nat → (blk, off_rd) +ₗ n ∈ dom (shp σ_t)) as WRITE_PRE.
  { intros n Hn. rewrite Holdlen in Hown.
    destruct (Hown n Hn) as (_&HH). eapply elem_of_dom. rewrite HH.
    eapply lookup_lt_is_Some_2. lia. }
  eassert (base_step P_t (Place (blk, off_rd) t (length v_wr) <- #v_wr) σ_t _ _ _) as HstepX.
  { eapply write_base_step'. 1: done. 3: exact Htrs'.
    2: { rewrite /trees_contain /trees_at_block /= Hit. apply Htr. } 1: exact WRITE_PRE. } 
  assert (trees_equal (scs σ_s) Forwards (strs σ_s) trs') as Hstrs_eq'.
  { eapply trees_equal_trans. 8: eapply Hstrs_eq.
    1,7,8: rewrite Hscs_eq. 1,2,5,7: by eapply Hwf_t. 2-4: by eapply Hwf_s.
    eapply apply_within_trees_lift. 2: exact Htrs'. 1: by eapply Hwf_t. simpl.
    intros trX tr' HH1 HH2 HH3. simpl in *. assert (tr = trX) as <- by congruence.
    eapply tree_equal_asymmetric_write_protected.
    5: eapply HH3. 2: done. 1: by eapply Hwf_t. 1: done.
    eapply asymmetric_write_prot_pre_from_bor_state_own_unq. 3: done. 2: done. 1: done. 1: done.
    intros off (Ho1&Ho2); simpl in *.
    assert (∃ (i:nat), off = off_rd + i) as (i&->) by (exists (Z.to_nat (off - off_rd)); lia).
    eapply Hown. 1: lia. }
  iSplit. 1: iPureIntro; do 3 eexists; done.
  iIntros (??? Hstep). pose proof Hstep as Hstep2.
  eapply head_write_inv in Hstep2 as (trs''&->&->&->&_&Hiinv&[(Hcont&Happly&Hlen)|(Hlen&->)]); last first.
  { exfalso. lia. }
  rewrite /memory_access /= Htrs' in Happly.
  assert (trs''=trs') as -> by congruence.
  rewrite WRITE_MEM.
  iDestruct "Hbor" as "((Hca & Htag_auth & Htag_t_auth & Htag_s_auth) & Htainted & Hpub_cid & #Hsrel & %Hcall_interp & %Htag_interp & _)".
  iPoseProof (tkmap_lookup with "Htag_auth Htag") as "%Htag".
  iPoseProof (ghost_map_lookup with "Hca Hc") as "%Hc".
  iPoseProof (ghost_map_lookup with "Htag_t_auth Ht") as "%Hhl".
  iMod (ghost_map_update (list_to_heaplet v_t' off_hl) with "Htag_t_auth Ht") as "(Htag_t_auth&Ht)". simpl.
  iModIntro.
  iSplit; first done.
  iSplitR "Hsim Htag Ht Hc".
  2: iApply ("Hsim" with "Ht Htag Hc"). iFrame "HP_t HP_s".
  iExists M_call, M_tag, (<[(t, blk):=list_to_heaplet v_t' off_hl]> M_t), M_s. iFrame "Htainted".
  iFrame. simpl. iSplit.
  { iSplit; last iSplit; last iSplit; last iSplit; last iSplit; try iPureIntro.
    { simpl. rewrite Hdom_eq. subst hp'. erewrite write_mem_dom_sane; first done. done. }
    1-4: done.
    simpl. iIntros (l Hl%elem_of_dom). rewrite -WRITE_MEM write_mem_dom_sane in Hl. 2: exact WRITE_PRE.
    eapply elem_of_dom in Hl.
    iDestruct "Hsrel" as "(_&_&_&_&_&Hsrel)". 
    destruct (decide (l.1 = blk ∧ off_rd ≤ l.2 < off_rd + length v_wr)) as [(<-&Hrange)|Hout].
    { iRight. iExists t. iPureIntro. exists (tk_unq tk_act). split; first done.
      split.
      - rewrite /heaplet_lookup lookup_insert_eq /=. destruct (list_to_heaplet v_t' off_hl !! l.2) eqn:HH; first done.
        eapply list_to_heaplet_lookup_None in HH. lia.
      - right. destruct (HL l.2) as (ae&Hae). 1: apply Hrange. eexists _, _. split; first done. eexists. split; first exact Hc.
        eexists. split; first exact HM. destruct l; apply Hae. }
    { iDestruct ("Hsrel" $! l Hl) as "[H|%Hpriv]".
      - iLeft. iIntros (sc Hsc). iApply "H".
        iPureIntro. rewrite /= -WRITE_MEM write_mem_lookup_outside // in Hsc.
      - iRight. iPureIntro. destruct Hpriv as (t'&tk&Htk&Htkhl&Hrst). exists t', tk.
        split; first done. split; last done.
        destruct (decide (t = t' ∧ blk = l.1)) as [(->&->)|Hne2].
        + rewrite /heaplet_lookup /= lookup_insert_eq /=.
          destruct (list_to_heaplet v_t' off_hl !! l.2) eqn:Heq. 1: done.
          eapply list_to_heaplet_lookup_None in Heq. eapply mk_is_Some, write_range_valid_iff in Hwrite. exfalso.
          rewrite /heaplet_lookup Hhl /= in Htkhl.
          destruct (list_to_heaplet v_t off_hl !! l.2) as [llll|] eqn:Heq2; last by destruct Htkhl.
          eapply list_to_heaplet_lookup_Some in Heq2. lia.
        +  rewrite /heaplet_lookup /= lookup_insert_ne //.
          intros [= -> ->]. destruct Htkhl as (x&(hl2&Hhl2&HHhl2)%bind_Some). simpl in *.
          rewrite Hhl2 in Hhl. injection Hhl as ->. eapply list_to_heaplet_lookup_Some in HHhl2. lia. } }
  iPureIntro. split_and!.
  - destruct Hcall_interp as (Hcall_interp&Hcc2). split; last done. intros c' M' HM'_some. simpl.
    specialize (Hcall_interp c' M' HM'_some) as (Hin & Hprot2).
    split; first done. intros t' L' [Ht HL']%Hprot2. split; first done.
    intros l' b' HlL. specialize (HL' l' b' HlL).
    eapply tag_protected_preserved_by_access; [eapply Hwf_t|done| | ].
    1: apply Hin.
    eapply tag_protected_for_mono. 2: done.
    intros l0 itX Hit1 Hit2 Hit3 (tk&Htk'&HhlX).
    destruct (decide (itag itX = t)) as [<-|]; last first.
    + exists tk. rewrite /heaplet_lookup !lookup_insert_ne /= //. congruence.
    + rewrite /tag_is_unq. exists tk. split; first done.
      rewrite /heaplet_lookup /=. destruct (decide (l0.1 = blk)) as [Heq|?].
      * rewrite Heq lookup_insert_eq // /=.
        rewrite /heaplet_lookup /= Heq Hhl /= in HhlX. eapply elem_of_dom.
        eapply elem_of_dom in HhlX.
        erewrite list_to_heaplet_dom_1. 1: exact HhlX. lia.
      * rewrite lookup_insert_ne. 2: congruence. apply HhlX.
  - destruct Htag_interp as (Ht1&Ht2&Ht3&Ht4&Ht5). split_and!.
    + intros t' tk' Htk'. destruct (Ht1 t' tk' Htk') as (HHt1&HHt2&HHtlocal&HHt3&HHt4&HHt5). split_and!.
      * done.
      * done.
      * intros ->. destruct (HHtlocal) as (Htl1&Htl2); first done. split.
        -- intros ? M' [([= -> ->]&H2)|(H1&H2)]%lookup_insert_Some.
           2: by eapply Htl1. subst M'. intros H%list_to_heaplet_empty_length.
           eapply Htl1. 1: eapply Hhl. simpl. eapply list_to_heaplet_empty_length. lia.
        -- done.
      * intros l sc (M'&HM'%lookup_insert_Some&HinM)%bind_Some. simpl in HM'.
        destruct HM' as [([= -> ->]&HM')|(Hne&HM')].
        -- assert (tk' = tk_unq tk_act) as -> by congruence. simpl. subst M'.
           assert (∃ sc_old, heaplet_lookup M_t (t', l) = Some sc_old) as [sc_old Hscold].
           { rewrite /heaplet_lookup /= Hhl /=. eapply elem_of_dom_2 in HinM. simpl in HinM.
             erewrite list_to_heaplet_dom_1 in HinM. 2: symmetry; exact Hlength.
             by eapply elem_of_dom in HinM. }
           specialize (HHt3 _ _ Hscold). eapply write_range_to_list_is_Some in Hwrite as (base&Hwrite&->&Hbase2).
           destruct (decide (off_hl + base ≤ l.2 < off_hl + base + length v_wr)) as [Hin|Hout].
           { eapply loc_controlled_write_becomes_active. 1: exact Htrs'. 8: exact HHt3.
             3,4: done. 2: done. 1: by subst hp'. 1: done. 1: done.
             eapply list_to_heaplet_lookup_Some in HinM as HinM2. simpl in HinM2. simpl.
             assert (∃ (i:nat), l.2 = off_hl + base + i) as [i Hi].
             1: exists (Z.to_nat (l.2-(off_hl + base))); lia. rewrite Hi list_to_heaplet_nth.
             ospecialize (Hd' i _). 1: lia.
             rewrite /= Hi /shift_loc /= in HinM. rewrite -Z.add_assoc -Nat2Z.inj_add list_to_heaplet_nth in HinM.
             subst v_t'. eapply write_range_to_list_lookup_inv in HinM as (HH3&HH4).
             ospecialize (HH3 _). 1: lia. rewrite HH3. f_equal. lia. }
           { eapply list_to_heaplet_lookup_Some in HinM as HH1. simpl in HH1.
             assert (sc_old = sc) as ->.
             { assert (∃ (i:nat), l.2 = off_hl + i) as [i Hi]. 1: exists (Z.to_nat (l.2 - off_hl)); lia.
               rewrite /= Hi list_to_heaplet_nth in HinM. subst v_t'. eapply write_range_to_list_lookup_inv in HinM as (HH3&HH4).
               ospecialize (HH4 _). 1: lia.
               rewrite /heaplet_lookup Hhl /= in Hscold. rewrite Hi list_to_heaplet_nth in Hscold. congruence. }
             eapply loc_controlled_access_outside. 1: exact Htrs'. 5: exact HHt3. 2: done. 2: done.
             2: simpl in *; lia. rewrite -WRITE_MEM /=. rewrite write_mem_lookup_outside //. simpl in *; lia. }
        -- intros Hpre. destruct (decide (blk = l.1 ∧ off_rd ≤ l.2 < off_rd + length v_wr)) as [(->&Hin)|Hout].
           { eapply loc_controlled_write_invalidates_others. 9: exact Hpre. 1: exact Htrs'. 1,2: done. 1: done. 1: lia.
             1: congruence. 1: done. eapply HHt3. rewrite /heaplet_lookup HM' /= HinM //. }
           { eapply loc_controlled_access_outside. 1: exact Htrs'. 2,3: done. 2: lia. 2: eapply HHt3; rewrite /heaplet_lookup HM' /= HinM //.
             2: done. rewrite -WRITE_MEM /=. rewrite write_mem_lookup_outside //. simpl in *; lia. }
      * done.
      * eapply dom_agree_on_tag_target_insert_same_dom. 3: done. 1: done.
        eapply list_to_heaplet_dom_1. lia.
    + intros ?? H%elem_of_dom. rewrite dom_insert_lookup_L in H. 2: done. by eapply Ht2, elem_of_dom.
    + done.
    + intros ??? H H2. rewrite !dom_insert_lookup_L in H,H2; last done. by eapply Ht4.
    + done.  
  - done.
  - subst hp'. eapply base_step_wf. 1: done. done.
Qed.



Lemma source_write_protected_active v_t v_wr sz l_hl l_rd v_t' t π Ψ c M L :
  sz ≠ 0%nat → (* if it is 0, use the zero-sized write lemma *)
  write_range l_hl.2 l_rd.2 v_wr v_t = Some v_t' →
  l_hl.1 = l_rd.1 →
  sz = length v_wr →
  (∀ off, range'_contains (l_rd.2, sz) off → ∃ ae, L !! (l_rd.1, off) = Some (EnsuringAccess ae)) →
  M !! t = Some L →
  c @@ M -∗
  t $$ tk_unq tk_act -∗
  l_hl ↦s∗[tk_unq tk_act]{t} v_t -∗
  (l_hl ↦s∗[tk_unq tk_act]{t} v_t' -∗ t $$ tk_unq tk_act -∗ c @@ M -∗ source_red #[☠] π Ψ)%E -∗
  source_red (Write (Place l_rd t sz) #v_wr) π Ψ.
Proof.
  iIntros (Hnz Hwrite Hsameblk Hlen HL HM) "Hc Htag Hs Hsim". eapply write_range_same_length in Hwrite as Hlength. subst sz.
  opose proof Hwrite as HH.
  eapply mk_is_Some, write_range_is_Some_read_range in HH as [vlsold Hreadsome]. eapply read_range_length in Hreadsome as Holdlen.
  iApply source_red_lift_base_step. iIntros (P_t σ_t P_s σ_s T_s K_s) "((HP_t & HP_s & Hbor)&%HT_s&%Hpoolsafe)".
  iPoseProof (bor_interp_get_pure with "Hbor") as "%Hp".
  destruct Hp as (Hstrs_eq & Hsnp_eq & Hsnc_eq & Hscs_eq & Hwf_s & Hwf_t & Hdom_eq).
  iModIntro. iDestruct "Hbor" as "(%M_call & %M_tag & %M_t & %M_s & Hbor)".
  iPoseProof (bor_interp_readN_source_protected with "Hbor Hc Hs Htag") as "(%it&%tr&%Hit&%Htr&%Hprot&%Hown)".
  1: exact Hreadsome. 1: done. 1: done. 1: done. 1: congruence.
  opose proof* (write_range_write_memory_smaller) as (hp'&WRITE_MEM&Hd'). 1: exact Hwrite. 1: done.
  { rewrite -Holdlen. intros i Hx. pose proof Hx as (H1&H2)%Hown. erewrite H2. by eapply lookup_lt_is_Some_2. }
  destruct l_hl as [blk off_hl], l_rd as [blk2 off_rd]; simpl in *; subst blk2.
  eapply mk_is_Some in Hwrite as Hrangebounds. rewrite -write_range_valid_iff in Hrangebounds.
  odestruct (bor_state_own_unq_act_enables_write false (off_rd, length v_wr)) as (trs'&Htrs').
  1: exact Hwf_s.
  { intros l (Hl1&Hl2); simpl in *. exists it, tr. do 2 (split; first done). assert (∃ (i:nat), l = off_rd + i) as (ii&Hii).
    1: exists (Z.to_nat (l - off_rd)); lia. subst l. eapply Hown. lia. }
  2: done. 1: rewrite /trees_lookup /trees_at_block Hit. 1: by eexists.
  assert (∀ n : nat, (n < length v_wr)%nat → (blk, off_rd) +ₗ n ∈ dom (shp σ_s)) as WRITE_PRE.
  { intros n Hn. rewrite Holdlen in Hown.
    destruct (Hown n Hn) as (_&HH). eapply elem_of_dom. rewrite HH.
    eapply lookup_lt_is_Some_2. lia. } 
  eassert (base_step P_s _ _ _ _ _) as Hstep.
  { eapply write_base_step' with (l:= (_, _)). 4: exact Htrs'.
    3: { rewrite /trees_contain /trees_at_block /= Hit. apply Htr. } 2: exact WRITE_PRE. 1: reflexivity. }
  assert (trees_equal (scs σ_s) Forwards trs' (strs σ_t)) as Hstrs_eq'.
  { eapply trees_equal_trans. 9: eapply Hstrs_eq.
    1,3,5,7: by eapply Hwf_s.
    1-3: eapply base_step_wf in Hwf_s; last done. 1-3: by eapply Hwf_s.
    change Forwards with (direction_flip Backwards).
    eapply trees_equal_sym.
    eapply apply_within_trees_lift. 2: exact Htrs'. 1: by eapply Hwf_s. simpl.
    intros trX tr' HH1 HH2 HH3. simpl in *. assert (tr = trX) as <- by congruence.
    eapply tree_equal_asymmetric_write_protected.
    5: eapply HH3. 2: done. 1: by eapply Hwf_s. 1: done.
    eapply asymmetric_write_prot_pre_from_bor_state_own_unq. 3: done. 2: done. 1: done. 1: done.
    intros off (Ho1&Ho2); simpl in *.
    assert (∃ (i:nat), off = off_rd + i) as (i&->) by (exists (Z.to_nat (off - off_rd)); lia).
    eapply Hown. 1: lia. }
  iExists _, _.
  iSplit; first done.
  iDestruct "Hbor" as "((Hca & Htag_auth & Htag_t_auth & Htag_s_auth) & Htainted & Hpub_cid & #Hsrel & %Hcall_interp & %Htag_interp & _)".
  iPoseProof (tkmap_lookup with "Htag_auth Htag") as "%Htag".
  iPoseProof (ghost_map_lookup with "Hca Hc") as "%Hc".
  iPoseProof (ghost_map_lookup with "Htag_s_auth Hs") as "%Hhl".
  iMod (ghost_map_update (list_to_heaplet v_t' off_hl) with "Htag_s_auth Hs") as "(Htag_s_auth&Hs)". simpl.
  iModIntro.
  iSplitR "Hsim Htag Hs Hc".
  2: iApply ("Hsim" with "Hs Htag Hc"). iFrame "HP_t HP_s".
  iExists M_call, M_tag, M_t, (<[(t, blk):=list_to_heaplet v_t' off_hl]> M_s).
  iFrame. simpl. iSplitL "Htainted".
  { iDestruct "Htainted" as "(%M'&Ht1&Ht2)". iExists M'. iFrame "Ht1".
    iIntros (t' l' Htl'). iDestruct ("Ht2" $! t' l' Htl') as "($&%Ht2)". iPureIntro.
    simpl. eapply disabled_tag_tree_apply_access_irreversible. 4: done. 3: by eapply Hwf_s. 1: done.
    rewrite /trees_contain /trees_at_block Hit. apply Htr. } iSplit.
  { iSplit; last iSplit; last iSplit; last iSplit; last iSplit; try iPureIntro.
    { simpl. rewrite -Hdom_eq. subst hp'. erewrite write_mem_dom_sane; first done. done. }
    1-4: done.
    simpl. iIntros (l Hl%elem_of_dom).
    eapply elem_of_dom in Hl.
    iDestruct "Hsrel" as "(_&_&_&_&_&Hsrel)". 
    destruct (decide (l.1 = blk ∧ off_rd ≤ l.2 < off_rd + length v_wr)) as [(<-&Hrange)|Hout].
    { iRight. iExists t. iPureIntro. exists (tk_unq tk_act). split; first done. destruct Htag_interp as (HH1&HH2&HH3&HH4&HH5).
      specialize (HH1 _ _ Htag) as (HHH1&HHH2&HHHl&HHH3&HHH4&HHH5A&HHH5B).
      split.
      - eapply HHH5B. rewrite /heaplet_lookup /= Hhl /=. destruct (list_to_heaplet v_t off_hl !! l.2) eqn:HH; first done.
        eapply list_to_heaplet_lookup_None in HH. lia.
      - right. destruct (HL l.2) as (ae&Hae). 1: apply Hrange. eexists _, _. split; first done. eexists. split; first exact Hc.
        eexists. split; first exact HM. destruct l; apply Hae. }
    { iDestruct ("Hsrel" $! l Hl) as "[H|%Hpriv]".
      - iLeft. iIntros (sc Hsc). rewrite /= write_mem_lookup_outside //. iApply "H". done.
      - iRight. done. } }
  iPureIntro. split_and!.
  - done.
  - destruct Htag_interp as (Ht1&Ht2&Ht3&Ht4&Ht5). split_and!.
    + intros t' tk' Htk'. destruct (Ht1 t' tk' Htk') as (HHt1&HHt2&HHtlocal&HHt3&HHt4&HHt5). split_and!.
      * done.
      * done.
      * intros ->. destruct (HHtlocal) as (Htl1&Htl2); first done. split.
        -- done.
        -- intros ? M' [([= -> ->]&H2)|(H1&H2)]%lookup_insert_Some.
           2: by eapply Htl2. subst M'. intros H%list_to_heaplet_empty_length.
           eapply Htl2. 1: eapply Hhl. simpl. eapply list_to_heaplet_empty_length. lia.
      * done.
      * intros l sc (M'&HM'%lookup_insert_Some&HinM)%bind_Some. simpl in HM'.
        destruct HM' as [([= -> ->]&HM')|(Hne&HM')].
        -- assert (tk' = tk_unq tk_act) as -> by congruence. simpl. subst M'.
           assert (∃ sc_old, heaplet_lookup M_s (t', l) = Some sc_old) as [sc_old Hscold].
           { rewrite /heaplet_lookup /= Hhl /=. eapply elem_of_dom_2 in HinM. simpl in HinM.
             erewrite list_to_heaplet_dom_1 in HinM. 2: symmetry; exact Hlength.
             by eapply elem_of_dom in HinM. }
           specialize (HHt4 _ _ Hscold). eapply write_range_to_list_is_Some in Hwrite as (base&Hwrite&->&Hbase2).
           destruct (decide (off_hl + base ≤ l.2 < off_hl + base + length v_wr)) as [Hin|Hout].
           { eapply loc_controlled_write_becomes_active. 1: exact Htrs'. 8: exact HHt4.
             3,4: done. 2: done. 1: by subst hp'. 1: done. 1: rewrite /trees_contain /trees_at_block Hit; eapply Htr.
             eapply list_to_heaplet_lookup_Some in HinM as HinM2. simpl in HinM2. simpl.
             assert (∃ (i:nat), l.2 = off_hl + base + i) as [i Hi].
             1: exists (Z.to_nat (l.2-(off_hl + base))); lia. rewrite Hi list_to_heaplet_nth.
             ospecialize (Hd' i _). 1: lia.
             rewrite /= Hi /shift_loc /= in HinM. rewrite -Z.add_assoc -Nat2Z.inj_add list_to_heaplet_nth in HinM.
             subst v_t'. eapply write_range_to_list_lookup_inv in HinM as (HH3&HH4).
             ospecialize (HH3 _). 1: lia. rewrite HH3. f_equal. lia. }
           { eapply list_to_heaplet_lookup_Some in HinM as HH1. simpl in HH1.
             assert (sc_old = sc) as ->.
             { assert (∃ (i:nat), l.2 = off_hl + i) as [i Hi]. 1: exists (Z.to_nat (l.2 - off_hl)); lia.
               rewrite /= Hi list_to_heaplet_nth in HinM. subst v_t'. eapply write_range_to_list_lookup_inv in HinM as (HH3&HH4).
               ospecialize (HH4 _). 1: lia.
               rewrite /heaplet_lookup Hhl /= in Hscold. rewrite Hi list_to_heaplet_nth in Hscold. congruence. }
             eapply loc_controlled_access_outside. 1: exact Htrs'. 5: exact HHt4. 2: done. 2: done.
             2: simpl in *; lia. rewrite write_mem_lookup_outside //. simpl in *; lia. }
        -- intros Hpre. destruct (decide (blk = l.1 ∧ off_rd ≤ l.2 < off_rd + length v_wr)) as [(->&Hin)|Hout].
           { eapply loc_controlled_write_invalidates_others. 9: exact Hpre. 1: exact Htrs'. 1,2: done. 1: done. 1: lia.
             1: congruence. 1: rewrite /trees_contain /trees_at_block Hit; eapply Htr. eapply HHt4. rewrite /heaplet_lookup HM' /= HinM //. }
           { eapply loc_controlled_access_outside. 1: exact Htrs'. 2,3: done. 2: lia. 2: eapply HHt4; rewrite /heaplet_lookup HM' /= HinM //.
             2: done. rewrite write_mem_lookup_outside //. simpl in *; lia. }
      * eapply dom_agree_on_tag_source_insert_same_dom. 3: done. 1: done.
        eapply list_to_heaplet_dom_1. lia.
    + done.
    + intros ?? H%elem_of_dom. rewrite dom_insert_lookup_L in H. 2: done. by eapply Ht3, elem_of_dom.
    + done.
    + intros ??? H H2. rewrite !dom_insert_lookup_L in H,H2; last done. by eapply Ht5.
  - subst hp'. eapply base_step_wf. 2: exact Hwf_s. done.
  - done.
Qed.

End lifting.
