From iris.proofmode Require Export proofmode.
From iris.base_logic.lib Require Import ghost_map.
From simuliris.base_logic Require Export gen_sim_prog.
From simuliris.simulation Require Export slsls.
From simuliris.simulation Require Import lifting.
From simuliris.tree_borrows Require Import tkmap_view.
From simuliris.tree_borrows Require Export defs.
From simuliris.tree_borrows Require Import steps_progress steps_inv logical_state.
From simuliris.tree_borrows.trees_equal Require Import trees_equal_base random_lemmas.



(** Lemmas / Accessors *)
Add Printing Constructor state item.
Section lemmas.
  Context `{bor_stateGS Σ}.
  Local Notation bor_interp := (bor_interp sc_rel).
  Local Notation bor_interp_inner := (bor_interp_inner sc_rel).

  Implicit Types
    (l : loc) (sc : scalar).

  Lemma init_mem_dom_L l n h :
    dom (init_mem l n h) = dom h ∪ dom (init_mem l n ∅).
  Proof. apply set_eq. intros l'. rewrite init_mem_dom. done. Qed.

  Lemma fresh_block_det σ_s σ_t :
    dom σ_s.(shp) = dom σ_t.(shp) →
    fresh_block σ_s.(shp) = fresh_block σ_t.(shp).
  Proof. rewrite /fresh_block. intros ->. done. Qed.

  Lemma free_mem_dom σ_t σ_s l n :
    dom σ_t.(shp) = dom σ_s.(shp) →
    dom (free_mem l n σ_t.(shp)) = dom (free_mem l n σ_s.(shp)).
  Proof.
    intros Hdom. induction n as [ | n IH] in l |-*; first done.
    simpl. rewrite !dom_delete_L IH. done.
  Qed.
  
  Lemma extend_trees_preserve off sz σ :
    let blk := fresh_block σ.(shp) in
    let nt := σ.(snp) in
    let α' := extend_trees σ.(snp) blk off sz σ.(strs) in
    state_wf σ →
    ∀ bb tree, σ.(strs) !! bb = Some tree → α' !! bb = Some tree.
  Proof.
    intros blk nt α' Hwf blk' stk. cbn. intros Hl'.
    rewrite /α' /extend_trees lookup_insert_ne //.
    intros <-. eapply elem_of_dom_2 in Hl'.
    rewrite state_wf_dom // in Hl'.
    eapply elem_of_map in Hl' as ((blk'&off'')&Heq&Heq2).
    cbn in Heq. subst blk'.
    by eapply is_fresh_block in Heq2.
  Qed.

  Lemma extend_trees_find_item σ t it off sz (loc : loc) :
    let blk := fresh_block σ.(shp) in
    let l := (blk, 0) in
    let nt := σ.(snp) in
    let α' := extend_trees σ.(snp) blk off sz σ.(strs) in
    state_wf σ →
    trees_lookup σ.(strs) loc.1 t it ->
    trees_lookup  α' loc.1 t it.
  Proof.
    intros blk l nt α' Hwf Hinv.
    inversion Hinv as [tree [H1 Lookup]]; clear Hinv.
    econstructor; split; last eassumption.
    by apply extend_trees_preserve.
  Qed.

  (* TODO refactor the tree lemmas *)
  Lemma exists_node_init_tree tg off (sz:nat) P :
    exists_node P (init_tree tg off sz) ↔
    P (mkItem tg None Disabled (init_perms Active off sz)).
  Proof.
    cbv -[init_perms]. tauto.
  Qed.

  Lemma every_node_init_tree tg off sz P :
    every_node P (init_tree tg off sz) ↔
    P (mkItem tg None Disabled (init_perms Active off sz)).
  Proof.
    cbv -[init_perms]. tauto.
  Qed.

  Lemma tree_lookup_init_tree t off sz : tree_lookup (init_tree t off sz) t (initial_item t off sz).
  Proof.
    split.
    - by eapply exists_node_init_tree.
    - by eapply every_node_init_tree.
  Qed.

  Lemma extend_trees_find_item_rev σ t it off sz (loc : loc) :
    let blk := fresh_block σ.(shp) in
    let l := (blk, 0) in
    let nt := σ.(snp) in
    let α' := extend_trees σ.(snp) blk off sz σ.(strs) in
    state_wf σ →
    trees_lookup α' loc.1 t it ->
    trees_lookup σ.(strs) loc.1 t it ∨ (it = mkItem nt None Disabled (init_perms Active off sz) ∧ loc.1 = blk).
  Proof.
    intros blk l nt α' Hwf Hinv.
    inversion Hinv as [tree [H1 Hinv1]]; clear Hinv.
    destruct loc as (blk'&off'). cbn in *.
    rewrite /α' /extend_trees in H1.
    eapply lookup_insert_Some in H1 as [(<-&Heq)|(H1&H2)].
    2: left; econstructor; split; last eassumption; done.
    right. subst tree.
    inversion Hinv1 as [Ex Unq]; simplify_eq.
    split; last reflexivity.
    inversion Ex as [Root|Else].
    - inversion Unq as [Eq]. rewrite <- Eq; last done. simpl. f_equal.
    - inversion Else; contradiction.
  Qed.

  Lemma init_mem_preserve σ n :
    let blk := fresh_block σ.(shp) in
    let l := (blk, 0) in
    let nt := σ.(snp) in
    let h' := init_mem l n σ.(shp) in
    ∀ l' sc, σ.(shp) !! l' = Some sc → h' !! l' = Some sc.
  Proof.
    intros blk l nt h' l' sc Hsc.
    rewrite (proj2 (init_mem_lookup _ _ _) l'); first done.
    intros i Hi ->.
    specialize (elem_of_dom σ.(shp) ((fresh_block (shp σ), 0) +ₗ i)).
    rewrite Hsc. intros (_ &Ha). specialize (Ha ltac:(eauto)).
    move : Ha. apply is_fresh_block.
  Qed.

  Lemma loc_controlled_alloc_update σ l' off sz n t (tk : tag_kind) sc :
    let blk := fresh_block σ.(shp) in
    let l := (blk, 0) in
    let nt := σ.(snp) in
    let h' := init_mem l n σ.(shp) in
    let α' := extend_trees σ.(snp) blk off sz σ.(strs) in
    let σ' := mkState h' α' σ.(scs) (S σ.(snp)) σ.(snc) in
    t ≠ nt →
    state_wf σ →
    loc_controlled l' t tk sc σ →
    loc_controlled l' t tk sc σ'.
  Proof.
    intros blk l nt h' α' σ' Hnt Hwf Hcontrolled Hpre.
    assert (bor_state_pre l' t tk σ) as [Hown Hmem]%Hcontrolled.
    (* FIXME: very ugly *)
    { destruct tk as [| |]; unfold bor_state_pre in Hpre|-*.
      3: done.
      all: destruct Hpre as (it & [Ha Hb]); exists it.
      all: split; auto; destruct (extend_trees_find_item_rev _ _ _ _ _ _ Hwf Ha) as [|[]]; [assumption|].
      all: subst it nt; pose proof (trees_lookup_correct_tag Ha) as SameTg.
      all: by rewrite /= in SameTg.
    }
    split; last by eapply init_mem_preserve.
    destruct Hown as (it & tr & Hin & Ht & Hinit & Htrs).
    exists it, tr; split_and!; try done.
    by apply extend_trees_preserve.
  Qed.

(*

  Lemma state_rel_alloc_update σ_t σ_s M_tag M_t M_t' M_call l n tk :
    let nt := σ_t.(snp) in
    (∀ t, is_Some (M_tag !! t) → t ≠ nt) →
    state_rel sc_rel M_tag M_t M_call σ_t σ_s -∗
    state_rel sc_rel (<[nt := (tk, ())]> M_tag) (M_t' ∪ M_t) M_call
      (mkState (init_mem l n (shp σ_t)) (init_stacks (sst σ_t) l n (Tagged nt)) (scs σ_t) (S σ_t.(snp)) (snc σ_t))
      (mkState (init_mem l n (shp σ_s)) (init_stacks (sst σ_s) l n (Tagged nt)) (scs σ_s) (S (snp σ_s)) (snc σ_s)).
  Proof.
    intros nt Hneq. iIntros "(%Hdom_eq & %Hsst_eq & %Hsnp_eq & %Hsnc_eq & %Hscs_eq & Hstate)".
    iSplitR. { simpl. rewrite !(init_mem_dom_L _ _ (shp _)) Hdom_eq. iPureIntro. set_solver. }
    simpl. rewrite Hsst_eq. iSplitR; first done.
    iSplitR; first by rewrite Hsnp_eq. do 2 (iSplitR; first done).
    iIntros (l' (s & [(Heq & Hi) | (i & Hi & ->)]%init_mem_lookup_case)).
    + (* old location *)
      iDestruct ("Hstate" $! l' with "[]") as "[Hpub | (%t & %Hpriv)]".
      { eauto. }
      * iLeft. simpl. iIntros (sc_t Hsc_t). simpl in Hsc_t.
        rewrite (proj2 (init_mem_lookup _ n _) l' Hi) in Hsc_t. simplify_eq.
        iDestruct ("Hpub" $! s with "[//]") as (sc_s Hsc_s) "Hscrel".
        iExists sc_s. iSplit; last done. iPureIntro.
        by rewrite (proj2 (init_mem_lookup _ n _) l' Hi).
      * iRight. iPureIntro. exists t.
        destruct Hpriv as (tk' & Htk & Hs & ?). exists tk'. split_and!; [ | | done].
        { rewrite lookup_insert_ne; first done. specialize (Hneq t ltac:(eauto)). done. }
        rewrite lookup_union_is_Some. eauto.
    + (* new location *)
      iLeft. rewrite /pub_loc /=. rewrite !(proj1 (init_mem_lookup _ _ _)); [ | done | done].
      iIntros (? [= <-]). iExists ☠%S. iSplit; done.
  Qed. *) 
(*
  Lemma call_set_interp_alloc_update σ n M_call :
    state_wf σ →
    let nt := σ.(snp) in
    let l := (fresh_block σ.(shp), 0) in
    call_set_interp M_call σ →
    call_set_interp M_call (mkState (init_mem l n (shp σ)) (init_stacks (sst σ) l n (Tagged nt)) (scs σ) (S σ.(snp)) (snc σ)).
  Proof.
    intros Hwf nt l Hcall_interp c M' [? HM']%Hcall_interp. simpl. split; first done.
    intros t L HL. specialize (HM' _ _ HL) as (?& HL'). split; first lia. intros l' Hl'.
    specialize (HL' l' Hl') as (stk & pm & Hstk & Hit & ?).
    exists stk, pm. split_and!; [ | done..].
    apply init_stack_preserve; done.
  Qed.

  Lemma loc_controlled_alloc_local σ l nt n l' sc :
    array_tag_map l nt (replicate n ScPoison) !! (nt, l') = Some sc →
    loc_controlled l' nt tk_local sc (mkState (init_mem l n σ.(shp)) (init_stacks σ.(sst) l n (Tagged nt)) σ.(scs) (S σ.(snp)) σ.(snc)).
  Proof.
    intros Hsc.
    specialize (array_tag_map_lookup2 l nt _ nt l' ltac:(eauto)) as [_ (i & Hi & ->)].
    intros _.
    rewrite array_tag_map_lookup_Some in Hsc; last done.
    apply lookup_replicate in Hsc as [-> Hi']. split.
    * simpl. rewrite (proj1 (init_stacks_lookup _ _ _ _)); done.
    * simpl. rewrite (proj1 (init_mem_lookup _ _ _ )); done.
  Qed.

  Lemma bor_interp_alloc_local σ_t σ_s T :
    let l_t := (fresh_block σ_t.(shp), 0) in
    let l_s := (fresh_block σ_s.(shp), 0) in
    let nt := σ_t.(snp) in
    state_wf (mkState (init_mem l_t (tsize T) σ_t.(shp)) (init_stacks σ_t.(sst) l_t (tsize T) (Tagged nt)) σ_t.(scs) (S σ_t.(snp)) σ_t.(snc)) →
    state_wf (mkState (init_mem l_s (tsize T) σ_s.(shp)) (init_stacks σ_s.(sst) l_s (tsize T) (Tagged nt)) σ_s.(scs) (S σ_s.(snp)) σ_s.(snc)) →
    bor_interp σ_t σ_s ==∗
    bor_interp
      (mkState (init_mem l_t (tsize T) σ_t.(shp)) (init_stacks σ_t.(sst) l_t (tsize T) (Tagged nt)) σ_t.(scs) (S σ_t.(snp)) σ_t.(snc))
      (mkState (init_mem l_s (tsize T) σ_s.(shp)) (init_stacks σ_s.(sst) l_s (tsize T) (Tagged nt)) σ_s.(scs) (S σ_s.(snp)) σ_s.(snc)) ∗
      nt $$ tk_local ∗
      l_t ↦t∗[tk_local]{nt} replicate (tsize T) ScPoison ∗
      l_s ↦s∗[tk_local]{nt} replicate (tsize T) ScPoison.
  Proof.
    intros l_t l_s nt Hwf_t' Hwf_s'.
    iIntros "(% & %M_tag & %M_t & %M_s & (Hcall_auth & Htag_auth & Ht_auth & Hs_auth) & Htainted & Hpub_cid & #Hstate & %Hcall_interp & %Htag_interp & %Hwf_s & %Hwf_t)".
    destruct Htag_interp as (Htag_interp & Ht_dom& Hs_dom).
    assert (M_tag !! nt = None) as M_tag_none.
    { destruct (M_tag !! nt) as [[? []] | ]eqn:Hs; last done.
      apply Htag_interp in Hs as (? & ? & _). lia.
    }
    assert (∀ l, M_t !! (nt, l) = None).
    { intros l. destruct (M_t !! (nt, l)) eqn:Hl; last done.
      specialize (Ht_dom nt l ltac:(eauto)) as (? & ?); congruence.
    }
    assert (∀ l, M_s !! (nt, l) = None).
    { intros l. destruct (M_s !! (nt, l)) eqn:Hl; last done.
      specialize (Hs_dom nt l ltac:(eauto)) as (? & ?); congruence.
    }
    (* update ghost state *)
    iMod (ghost_map_array_tag_insert _ _ (replicate (tsize T) ScPoison ) nt l_t with "Ht_auth") as "[Ht_mem Ht_auth]"; first done.
    iMod (ghost_map_array_tag_insert _ _ (replicate (tsize T) ScPoison ) nt l_s with "Hs_auth") as "[Hs_mem Hs_auth]"; first done.
    iMod (tkmap_insert tk_local nt () with "Htag_auth") as "[Htag_auth Hnt]"; first done.
    iModIntro.

    iFrame "Hnt Hs_mem Ht_mem".
    iExists _, _, _, _. iFrame "Htag_auth Ht_auth Hs_auth Hcall_auth". simpl.
    iPoseProof (state_rel_get_pure with "Hstate") as "%Hp".
    iPoseProof (state_rel_dom_eq with "Hstate") as "%Hdom_eq".
    destruct Hp as (Hsst_eq & Hsnp_eq & Hsnc_eq & Hscs_eq).
    assert (l_s = l_t) as Hl_eq.
    { subst l_s l_t. rewrite (fresh_block_det _ _ Hdom_eq). done. }
    iSplitL "Htainted". { subst nt. rewrite -Hsnp_eq. by iApply tag_tainted_interp_alloc. }
    iSplitL "Hpub_cid". { iApply (pub_cid_interp_preserve_sub with "Hpub_cid"); simpl; done. }
    iSplitL.
    { (* state rel *)
      rewrite Hl_eq. iApply state_rel_alloc_update; last done.
      intros t ([?[]] & Hs). specialize (Htag_interp _ _ Hs) as (? & ? & _). lia.
    }
    iSplitL.
    { iPureIntro. apply call_set_interp_alloc_update; done. }
    iSplitL.
    { (* tag interp *)
      iPureIntro. split_and!.
      { simpl. intros t tk. rewrite lookup_insert_Some. intros [[<- [= <-]] | [Hneq Hsome]].
        - (* new tag: under local control *)
          split_and!; [ lia | lia | | |].
          + intros l' sc_t Hsc_t%lookup_union_Some_inv_l; last done. by apply loc_controlled_alloc_local.
          + intros l' sc_t Hsc_s%lookup_union_Some_inv_l; last done. by apply loc_controlled_alloc_local.
          + apply dom_agree_on_tag_union; first last.
            { apply dom_agree_on_tag_not_elem; done. }
            rewrite Hl_eq. apply dom_agree_on_tag_array_tag_map.
            by rewrite length_replicate.
        - (* old tag *)
          specialize (Htag_interp _ _ Hsome) as (? & ? & Hcontrol_t & Hcontrol_s & Hag).
          split_and!; [lia | lia | .. ].
          + intros l' sc_t Hsc_t. apply loc_controlled_alloc_update; [done | done| ].
            rewrite lookup_union_r in Hsc_t; first by apply Hcontrol_t.
            apply array_tag_map_lookup_None. lia.
          + intros l' sc_s Hsc_s. subst nt. rewrite -Hsnp_eq. apply loc_controlled_alloc_update; [done | lia | ].
            rewrite lookup_union_r in Hsc_s; first by apply Hcontrol_s.
            apply array_tag_map_lookup_None. lia.
          + apply dom_agree_on_tag_union; last done.
            rewrite Hl_eq. apply dom_agree_on_tag_not_elem.
            all: intros l; rewrite array_tag_map_lookup_None; done.
      }
      all: intros t l'; rewrite lookup_insert_is_Some' lookup_union_is_Some;
        intros [[-> _]%array_tag_map_lookup2 | ?]; eauto.
    }
    eauto.
  Qed. *)

  (** Read lemmas *)

    Lemma bor_interp_local_shapes_tree_target σ_t σ_s M_call M_tag M_t M_s t l scs :
      bor_interp_inner σ_t σ_s M_call M_tag M_t M_s -∗
      l ↦t∗[tk_local]{t} scs -∗
      t $$ tk_local -∗
      ⌜∃ it, σ_t.(strs) !! l.1 = Some (branch it empty empty) ∧ root_invariant l.1 it σ_t.(shp) ∧ t = itag it⌝.
    Proof.
    iIntros "((Hc & Htag_auth & Htag_t_auth & Htag_s_auth) & Htainted & Hpub_cid & #Hsrel & %Hcall_interp & %Htag_interp & %Hwf_s & %Hwf_t)".
    iIntros "Hp Htag".
    iPoseProof (tkmap_lookup with "Htag_auth Htag") as "%Htag_lookup".
    destruct Htag_interp as (Htag_interp & _).
    destruct (Htag_interp _ _ Htag_lookup) as (_ & _ & Hlocal & Ht & Hs & Hagree).
    iPoseProof (ghost_map_lookup with "Htag_t_auth Hp") as "%Ht_lookup".
    iPureIntro. destruct Hlocal as (Hl1&Hl2). 1: done.
    specialize (Hl1 _ _ Ht_lookup) as Hne. rewrite list_to_heaplet_empty_length in Hne.
    specialize (Ht l). rewrite /heaplet_lookup /= Ht_lookup /= in Ht.
    assert (l.2 + (0%nat) = l.2) as Hzero by lia.
    pose proof (list_to_heaplet_nth scs l.2 0) as Hnth. rewrite Hzero in Hnth. rewrite Hnth in Ht.
    edestruct (lookup_lt_is_Some_2 scs 0) as [x Hx]. 1: lia.
    odestruct (Ht _ Hx _) as ((it&tr&Hit&Htr&Hini&Hperm&Hprot&Hothers)&HH); first done.
    pose proof (state_wf_roots_active _ Hwf_t _ _ Htr) as Htrc.
    pose tr as tr_main.
    destruct tr as [|itroot ? trb]; first done. destruct Htrc as (Htrc&->). exists itroot.
    assert (tree_contains (itag itroot) tr_main) as Hin1 by (simpl; tauto).
    eapply wf_tree_tree_unique in Hin1; last by eapply Hwf_t.
    eapply unique_implies_lookup in Hin1 as HHin1; destruct HHin1 as (ii1&Hii1%Hothers).
    split; last done. rewrite Htr.
    f_equal. f_equal. destruct trb as [|itb ??]; first done.
    assert (tree_contains (itag itb) tr_main) as Hin2 by (simpl; tauto).
    eapply wf_tree_tree_unique in Hin2; last by eapply Hwf_t.
    eapply unique_implies_lookup in Hin2 as HHin2; destruct HHin2 as (ii2&Hii2%Hothers).
    subst t. rewrite /tr_main /= /tree_unique /= !bool_decide_true // in Hin2.
  Qed.

    Lemma bor_interp_local_shapes_tree_source σ_t σ_s M_call M_tag M_t M_s t l scs :
      bor_interp_inner σ_t σ_s M_call M_tag M_t M_s -∗
      l ↦s∗[tk_local]{t} scs -∗
      t $$ tk_local -∗
      ⌜∃ it, σ_s.(strs) !! l.1 = Some (branch it empty empty) ∧ root_invariant l.1 it σ_s.(shp) ∧ t = itag it⌝.
    Proof.
    iIntros "((Hc & Htag_auth & Htag_t_auth & Htag_s_auth) & Htainted & Hpub_cid & #Hsrel & %Hcall_interp & %Htag_interp & %Hwf_s & %Hwf_t)".
    iIntros "Hp Htag".
    iPoseProof (tkmap_lookup with "Htag_auth Htag") as "%Htag_lookup".
    destruct Htag_interp as (Htag_interp & _).
    destruct (Htag_interp _ _ Htag_lookup) as (_ & _ & Hlocal & Ht & Hs & Hagree).
    iPoseProof (ghost_map_lookup with "Htag_s_auth Hp") as "%Ht_lookup".
    iPureIntro. destruct Hlocal as (Hl1&Hl2). 1: done.
    specialize (Hl2 _ _ Ht_lookup) as Hne. rewrite list_to_heaplet_empty_length in Hne.
    specialize (Hs l). rewrite /heaplet_lookup /= Ht_lookup /= in Hs.
    assert (l.2 + (0%nat) = l.2) as Hzero by lia.
    pose proof (list_to_heaplet_nth scs l.2 0) as Hnth. rewrite Hzero in Hnth. rewrite Hnth in Hs.
    edestruct (lookup_lt_is_Some_2 scs 0) as [x Hx]. 1: lia.
    odestruct (Hs _ Hx _) as ((it&tr&Hit&Htr&Hini&Hperm&Hprot&Hothers)&HH); first done.
    pose proof (state_wf_roots_active _ Hwf_s _ _ Htr) as Htrc.
    pose tr as tr_main.
    destruct tr as [|itroot ? trb]; first done. destruct Htrc as (Htrc&->). exists itroot.
    assert (tree_contains (itag itroot) tr_main) as Hin1 by (simpl; tauto).
    eapply wf_tree_tree_unique in Hin1; last by eapply Hwf_s.
    eapply unique_implies_lookup in Hin1 as HHin1; destruct HHin1 as (ii1&Hii1%Hothers).
    split. 2: done.
    rewrite Htr.
    f_equal. f_equal. destruct trb as [|itb ??]; first done.
    assert (tree_contains (itag itb) tr_main) as Hin2 by (simpl; tauto).
    eapply wf_tree_tree_unique in Hin2; last by eapply Hwf_s.
    eapply unique_implies_lookup in Hin2 as HHin2; destruct HHin2 as (ii2&Hii2%Hothers).
    subst t. rewrite /tr_main /= /tree_unique /= !bool_decide_true // in Hin2.
  Qed.


    Lemma bor_interp_readN_target_local σ_t σ_s M_call M_tag M_t M_s t l scs :
    bor_interp_inner σ_t σ_s M_call M_tag M_t M_s -∗
    l ↦t∗[tk_local]{t} scs -∗
    t $$ tk_local -∗
    ⌜∀ i : nat, (i < length scs)%nat → σ_t.(shp) !! (l +ₗ i) = scs !! i⌝ ∗
    ⌜∃ it, σ_t.(strs) !! l.1 = Some (branch it empty empty) ∧ root_invariant l.1 it σ_t.(shp) ∧ t = itag it⌝.
  Proof.
    iIntros "((Hc & Htag_auth & Htag_t_auth & Htag_s_auth) & Htainted & Hpub_cid & #Hsrel & %Hcall_interp & %Htag_interp & %Hwf_s & %Hwf_t)".
    iIntros "Hp Htag".
    iPoseProof (tkmap_lookup with "Htag_auth Htag") as "%Htag_lookup".
    pose proof Htag_interp as (Htag_interp2 & _).
    destruct (Htag_interp2 _ _ Htag_lookup) as (_ & _ & Hlocal & Ht & Hs & Hagree).
    iPoseProof (ghost_map_lookup with "Htag_t_auth Hp") as "%Ht_lookup".
    iPoseProof (bor_interp_local_shapes_tree_target with "[-Hp Htag] Hp Htag") as "%Htree".
    1: iFrame; iFrame "#"; iPureIntro; done.
    iPureIntro. split; last done.
    intros i Hi. edestruct (lookup_lt_is_Some_2 scs i) as [sc Hsc]; first done.
    rewrite Hsc.
    destruct (Ht (l +ₗ i) sc). 2: done. 1: rewrite /heaplet_lookup /= Ht_lookup /= list_to_heaplet_nth //. done.
  Qed.


    Lemma bor_interp_readN_source_local σ_t σ_s M_call M_tag M_t M_s t l scs :
    bor_interp_inner σ_t σ_s M_call M_tag M_t M_s -∗
    l ↦s∗[tk_local]{t} scs -∗
    t $$ tk_local -∗
    ⌜∀ i : nat, (i < length scs)%nat → σ_s.(shp) !! (l +ₗ i) = scs !! i⌝ ∗
    ⌜∃ it, σ_s.(strs) !! l.1 = Some (branch it empty empty) ∧ root_invariant l.1 it σ_s.(shp) ∧ t = itag it⌝.
  Proof.
    iIntros "((Hc & Htag_auth & Htag_t_auth & Htag_s_auth) & Htainted & Hpub_cid & #Hsrel & %Hcall_interp & %Htag_interp & %Hwf_s & %Hwf_t)".
    iIntros "Hp Htag".
    iPoseProof (tkmap_lookup with "Htag_auth Htag") as "%Htag_lookup".
    pose proof Htag_interp as (Htag_interp2 & _).
    destruct (Htag_interp2 _ _ Htag_lookup) as (_ & _ & Hlocal & Ht & Hs & Hagree).
    iPoseProof (ghost_map_lookup with "Htag_s_auth Hp") as "%Ht_lookup".
    iPoseProof (bor_interp_local_shapes_tree_source with "[-Hp Htag] Hp Htag") as "%Htree".
    1: iFrame; iFrame "#"; iPureIntro; done.
    iPureIntro. split; last done.
    intros i Hi. edestruct (lookup_lt_is_Some_2 scs i) as [sc Hsc]; first done.
    rewrite Hsc.
    destruct (Hs (l +ₗ i) sc). 2: done. 1: rewrite /heaplet_lookup /= Ht_lookup /= list_to_heaplet_nth //. done.
  Qed.

  Lemma protected_tags_bor_state_pre P c σ l tg ae tk :
    tag_protected_for P c σ.(strs) l tg (EnsuringAccess ae) →
    bor_state_pre l tg tk σ.
  Proof.
    intros (it&Hit&Hforcall&Hstrength&HP&Hinit&Hndis&Hncell).
    destruct tk.
    - by exists it.
    - by exists it.
    - done.
  Qed.

  Lemma bor_interp_readN_target_protected σ_t σ_s M_call M_tag M_t M_s t l_rd l_hl tk sz scs_hl scs_rd L M c :
    read_range l_rd.2 sz (list_to_heaplet scs_hl l_hl.2) = Some scs_rd →
    l_hl.1 = l_rd.1 →
    (∀ off, range'_contains (l_rd.2, sz) off → ∃ ae, L !! (l_rd.1, off) = Some (EnsuringAccess ae)) →
    M !! t = Some L →
    length scs_rd ≠ 0%nat →
    bor_interp_inner σ_t σ_s M_call M_tag M_t M_s -∗
  c @@ M -∗
    l_hl ↦t∗[tk]{t} scs_hl -∗
    t $$ tk -∗
    ∃ it tr, ⌜σ_t.(strs) !! l_rd.1 = Some tr ∧ tree_lookup tr t it ∧ protector_is_active (iprot it) σ_t.(scs) ∧
    ∀ i : nat, (i < length scs_rd)%nat → bor_state_own_on (l_rd +ₗ i) t tk σ_t it tr ∧ σ_t.(shp) !! (l_rd +ₗ i) = scs_rd !! i⌝.
  Proof.
    iIntros (Hrr Hsameblk Hprot1 Hprot2 Hnn) "((Hc & Htag_auth & Htag_t_auth & Htag_s_auth) & Htainted & Hpub_cid & #Hsrel & %Hcall_interp & %Htag_interp & %Hwf_s & %Hwf_t)".
    iIntros "Hprot3 Hp Htag".
    iPoseProof (tkmap_lookup with "Htag_auth Htag") as "%Htag_lookup".
    iPoseProof (ghost_map_lookup with "Htag_t_auth Hp") as "%Ht_lookup".
    iPoseProof (ghost_map_lookup with "Hc Hprot3") as "%Hprot_lookup".
    pose proof Htag_interp as (Htag_interp2 & _).
    destruct (Htag_interp2 _ _ Htag_lookup) as (_ & _ & _ & Ht & Hs & Hagree).
    destruct Hcall_interp as (Hcall_interp&_).
    specialize (Hcall_interp _ _ Hprot_lookup) as (Hprot4&Hcall_interp).
    specialize (Hcall_interp _ _ Hprot2) as (Hvalid&Hcall_interp).
    eapply read_range_length in Hrr as Hsz.
    assert (sz ≠ 0%nat) as Hnnsz by lia.
    opose proof (Hprot1 l_rd.2 _) as (ae1&Hae1). 1: split; simpl in *; lia.
    opose proof (Hcall_interp _ _ Hae1) as (it1&(tr1&Htr1&Hit11)&Hforcall&_).
    iExists it1, tr1. iPureIntro. do 2 (split; first done).
    split. 1: by eexists.
    intros i Hi.
    eapply lookup_lt_is_Some_2 in Hi as Hissome. destruct Hissome as (sc&Hsc).
    eapply read_range_lookup_nth in Hsc as Hschl. 2: eassumption.
    eapply list_to_heaplet_lookup_Some in Hschl as Hbounds.
    assert (∃ (i_rd:nat), (l_hl.2 + i_rd = l_rd.2 + i)%Z) as (i_rd&Hi_rd).
    { exists (Z.to_nat ((l_rd.2 + i) - l_hl.2)). lia. }
    ospecialize (Ht (l_rd +ₗ i) sc _).
    1: rewrite /heaplet_lookup /= -Hsameblk Ht_lookup /= //.
    destruct (Hprot1 (l_rd.2 + i)) as (ae&Hae). 1: subst sz; split; simpl; lia.
    specialize (Hcall_interp _ _ Hae).
    destruct Ht as (Ht1&Ht2).
    1: by eapply protected_tags_bor_state_pre.
    destruct Hcall_interp as (it&(tr&Htr&Hit)&Hpc&_). simpl in Htr,Htr1.
    assert (tr = tr1) as <- by congruence.
    assert (it = it1) as <- by by eapply tree_lookup_unique.
    destruct Ht1 as (it'&tr'&Hit'&Htr'&HH).
    simpl in *.
    assert (tr = tr') as <- by congruence.
    assert (it = it') as <- by by eapply tree_lookup_unique.
    rewrite Ht2. done.
  Qed.

  Lemma wf_trees_parents_not_disabled_self trs C tg (it : item) blk off :
    wf_trees trs →
    each_tree_protected_parents_not_disabled C trs →
    trees_lookup trs blk tg it →
    protector_is_active (iprot it) C →
    initialized (item_lookup it off) = PermInit →
    perm (item_lookup it off) = Disabled →
    False.
  Proof.
    intros (Hwf&_) Hntrs (tr&Htr&Hit) Hact Hini Hdis.
    specialize (Hwf _ _ Htr). eapply tree_lookup_correct_tag in Hit as Hit2; subst tg.
    specialize (Hntrs  _ _ Htr (itag it)). eapply every_child_ParentChildIn in Hntrs.
    2: eapply Hwf. 2,4: eapply Hwf, Hit. 2: eapply Hit. 2: by left.
    eapply every_node_eqv_universal in Hntrs.
    2: by eapply tree_lookup_to_exists_node.
    destruct Hntrs as [Hc|Hc]. 1-4: done.
    congruence.
  Qed.

  Lemma cell_node_perms_eq_up_to_C C tr1 tr2 tg off pr d lp1 lp2 :
    perm_eq_up_to_C C tr1 tr2 tg off pr d lp1 lp2 →
    perm lp1 = Cell → perm lp2 = Cell.
  Proof.
    intros Hsameperm.
    destruct lp1 as [it1i it1p].
    destruct lp2 as [it2i it2p]. simpl. intros ->.
    inversion Hsameperm as
      [perm Lookup EqLookup
      |??? Prot Confl1 Confl2 Lookup1 Lookup2
      |??? Prot Lookup1 Lookup2
      |p1 p2 Confl1 Confl2 Lookup1 Lookup2
      |witness_tg ?? Dis1 Dis2 SameInit SameCell
      |ini ?? witness_tg Frz Lookup1 Lookup2
      |p1 p2 ini Hd Lookup1 Lookup2
    ]; simplify_eq.
    - done.
    - inversion Confl1; congruence.
    - simpl in *. rewrite <- SameCell. done.
    - destruct d; inversion Hd.
  Qed.

  Lemma cell_nodes_trees_equal C d trs1 trs2 l tg it1 it2 :
    wf_trees trs1 → wf_trees trs2 →
    trees_equal C d trs1 trs2 →
    trees_lookup trs1 l.1 tg it1 →
    trees_lookup trs2 l.1 tg it2 →
    perm (item_lookup it1 l.2) = Cell →
    perm (item_lookup it2 l.2) = Cell.
  Proof.
    intros Hwf1 Hwf2 Heq (tr1&Htr1&Hit1) (tr2&Htr2&Hit2) Hcell.
    specialize (Heq l.1). rewrite Htr1 Htr2 in Heq.
    inversion Heq as [x y Heq2|]; subst.
    destruct Heq2 as (_&_&Heq2).
    edestruct Heq2 as (it1'&it2'&Hit1'&Hit2'&Heq2').
    1: eapply Hit1.
    eapply tree_lookup_unique in Hit1'; last exact Hit1.
    eapply tree_lookup_unique in Hit2'; last exact Hit2.
    subst it1' it2'.
    specialize (Heq2' l.2).
    destruct Heq2' as [Hsameprot Hsameperm].
    destruct (item_lookup it1 l.2) as [it1i it1p] eqn:Heqit1.
    destruct (item_lookup it2 l.2) as [it2i it2p] eqn:Heqit2.
    by eapply cell_node_perms_eq_up_to_C.
  Qed.

  Lemma tag_protected_for_trees_equal P C c d trs1 trs2 l tg ps :
    wf_trees trs1 → wf_trees trs2 →
    each_tree_protected_parents_not_disabled C trs1 →
    each_tree_protected_parents_not_disabled C trs2 →
    c ∈ C →
    trees_equal C d trs1 trs2 →
    tag_protected_for P c trs1 l tg ps →
    tag_protected_for P c trs2 l tg ps.
  Proof.
    intros Hwf1 Hwf2 Hnd1 Hnd2 Hc Heq. destruct ps as [|ae].
    - intros Hx it2 (tr2&Htr2&Hit2).
      specialize (Heq l.1). rewrite Htr2 in Heq.
      inversion Heq as [tr1 tr2' Heq12 Htr1 X5|]; simplify_eq. symmetry in Htr1.
      destruct (tree_equal_transfer_lookup_2 C Heq12 Hit2) as (it1&Hit1&Heqit).
      odestruct (Hx it1 _) as (HHit1&HHit1B&HXX&HHit1I&Hit1nD&HHit1nC). 1: by exists tr1.
      destruct (Heqit l.2) as (Heqprot&Heqperm).
      eapply perm_eq_up_to_C_same_init in Heqperm as Heqinit.
      rewrite HHit1I in Heqinit.
      split_and!.
      + by rewrite -Heqprot.
      + by rewrite -Heqprot.
      + done.
      + done.
      + intros Hndis. eapply wf_trees_parents_not_disabled_self.
        6: exact Hndis. 5: done. 3: exists tr2; done. 1-2: done.
        exists c. split; last done. by rewrite -Heqprot.
      + intros Hcell. eapply cell_node_perms_eq_up_to_C in Hcell; last by eapply perm_eq_up_to_C_sym in Heqperm.
        contradiction.
    - intros (it1&(tr1&Htr1&Hit1)&HHit1&HHit1B&HHit1X&HHit1I&HHit1nD&HHit1Cell).
      specialize (Heq l.1). rewrite Htr1 in Heq.
      inversion Heq as [tr1' tr2 Heq12 X4 Htr2|]; simplify_eq. symmetry in Htr2.
      destruct (tree_equal_transfer_lookup_1 C Heq12 Hit1) as (it2&Hit2&Heqit).
      exists it2. split. 1: by exists tr2.
      destruct (Heqit l.2) as (Heqprot&Heqperm).
      eapply perm_eq_up_to_C_same_init in Heqperm as Heqinit.
      rewrite HHit1I in Heqinit.
      split_and!.
      + by rewrite -Heqprot.
      + by rewrite -Heqprot.
      + intros [= ->]. eapply tree_lookup_correct_tag in Hit1, Hit2. rewrite Hit2 -Hit1. by eapply HHit1X.
      + done.
      + intros Hndis. eapply wf_trees_parents_not_disabled_self.
        6: exact Hndis. 5: done. 3: exists tr2; done. 1-2: done.
        exists c. split; last done. by rewrite -Heqprot.
      + intros Hcell. eapply cell_node_perms_eq_up_to_C in Hcell; last by eapply perm_eq_up_to_C_sym in Heqperm.
        contradiction.
  Qed.

  Lemma bor_interp_readN_source_protected σ_t σ_s M_call M_tag M_t M_s t l_rd l_hl tk sz scs_hl scs_rd L M c :
    read_range l_rd.2 sz (list_to_heaplet scs_hl l_hl.2) = Some scs_rd →
    l_hl.1 = l_rd.1 →
    (∀ off, range'_contains (l_rd.2, sz) off → ∃ ae, L !! (l_rd.1, off) = Some (EnsuringAccess ae)) →
    M !! t = Some L →
    length scs_rd ≠ 0%nat →
    bor_interp_inner σ_t σ_s M_call M_tag M_t M_s -∗
  c @@ M -∗
    l_hl ↦s∗[tk]{t} scs_hl -∗
    t $$ tk -∗
    ∃ it tr, ⌜σ_s.(strs) !! l_rd.1 = Some tr ∧ tree_lookup tr t it ∧ protector_is_active (iprot it) σ_s.(scs) ∧
    ∀ i : nat, (i < length scs_rd)%nat → bor_state_own_on (l_rd +ₗ i) t tk σ_s it tr ∧ σ_s.(shp) !! (l_rd +ₗ i) = scs_rd !! i⌝.
  Proof.
    iIntros (Hrr Hsameblk Hprot1 Hprot2 Hnn) "((Hc & Htag_auth & Htag_t_auth & Htag_s_auth) & Htainted & Hpub_cid & #Hsrel & %Hcall_interp & %Htag_interp & %Hwf_s & %Hwf_t)".
    iIntros "Hprot3 Hp Htag".
    iDestruct "Hsrel" as "(%Hdom_eq&%Hstrs_eq&%Hsnp_eq&%Hsnv_eq&%Hscs_eq&Hsrel)".
    iPoseProof (tkmap_lookup with "Htag_auth Htag") as "%Htag_lookup".
    iPoseProof (ghost_map_lookup with "Htag_s_auth Hp") as "%Ht_lookup".
    iPoseProof (ghost_map_lookup with "Hc Hprot3") as "%Hprot_lookup".
    pose proof Htag_interp as (Htag_interp2 & _).
    destruct (Htag_interp2 _ _ Htag_lookup) as (_ & _ & _ & Ht & Hs & Hagree).
    destruct Hcall_interp as (Hcall_interp&_).
    specialize (Hcall_interp _ _ Hprot_lookup) as (Hprot4&Hcall_interp).
    specialize (Hcall_interp _ _ Hprot2) as (Hvalid&Hcall_interp).
    eapply read_range_length in Hrr as Hsz.
    assert (sz ≠ 0%nat) as Hnnsz by lia.
    opose proof (Hprot1 l_rd.2 _) as (ae1&Hae1). 1: split; simpl in *; lia.
    opose proof (Hcall_interp _ _ Hae1) as (it1&(tr1&Htr1&Hit1)&Hforcall&_).
    simpl in *.
    assert (is_Some (σ_s.(strs) !! l_rd.1)) as [tr2 Htr2].
    { specialize (Hstrs_eq l_rd.1). rewrite Htr1 /= in Hstrs_eq.
      inversion Hstrs_eq. done. }
    eassert (tree_equal (scs σ_s) _ tr2 tr1) as Htr12.
    { specialize (Hstrs_eq l_rd.1). rewrite Htr1 Htr2 /= in Hstrs_eq. inversion Hstrs_eq; simplify_eq. done. }
    unshelve edestruct tree_equal_transfer_lookup_2 as (it2&Hit2&(Hitprot&Hit12)). 1: exact 0. 7: exact Htr12. 3: exact Hit1.
    iExists it2, tr2. iPureIntro. do 2 (split; first done).
    split. { exists c. split; last by rewrite Hscs_eq. by rewrite Hitprot. }
    intros i Hi.
    eapply lookup_lt_is_Some_2 in Hi as Hissome. destruct Hissome as (sc&Hsc).
    eapply read_range_lookup_nth in Hsc as Hschl. 2: eassumption.
    eapply list_to_heaplet_lookup_Some in Hschl as Hbounds.
    assert (∃ (i_rd:nat), (l_hl.2 + i_rd = l_rd.2 + i)%Z) as (i_rd&Hi_rd).
    { exists (Z.to_nat ((l_rd.2 + i) - l_hl.2)). lia. }
    ospecialize (Hs (l_rd +ₗ i) sc _).
    1: rewrite /heaplet_lookup /= -Hsameblk Ht_lookup /= //.
    destruct (Hprot1 (l_rd.2 + i)) as (ae&Hae). 1: subst sz; split; simpl; lia.
    specialize (Hcall_interp _ _ Hae).
    destruct Hs as (Ht1&Ht2).
    { eapply protected_tags_bor_state_pre. eapply tag_protected_for_trees_equal.
      7: exact Hcall_interp. 6: eapply trees_equal_sym, Hstrs_eq. 3, 5: rewrite Hscs_eq. 4: done.
      1, 3: eapply Hwf_t. 1, 2: eapply Hwf_s. }
    destruct Ht1 as (it'&tr'&Hit'&Htr'&HH).
    simpl in *.
    assert (tr2 = tr') as <- by congruence.
    assert (it2 = it') as <- by by eapply tree_lookup_unique.
    rewrite Ht2. done.
  Qed.

  Lemma bor_interp_readN_target σ_t σ_s M_call M_tag M_t M_s (t : tag) tk l v_t :
    bor_interp_inner σ_t σ_s M_call M_tag M_t M_s -∗
    l ↦t∗[tk]{t} v_t -∗
    t $$ tk -∗
    ⌜∀ i:nat, (i < length v_t)%nat → loc_controlled (l +ₗ i) t tk (v_t !!! i) σ_t⌝.
  Proof.
    iIntros "((Hc & Htag_auth & Htag_t_auth & Htag_s_auth) & Htainted & Hpub_cid & Hsrel & %Hcall & %Htag_interp & %Hwf_s & %Hwf_t)".
    iIntros "Hp Htag".
    iPoseProof (tkmap_lookup with "Htag_auth Htag") as "%Htag_lookup".
    destruct Htag_interp as (Htag_interp & _ & _).
    destruct (Htag_interp _ _ Htag_lookup) as (_ & _ & _ & Ht & _ & _).
    iPoseProof (ghost_map_lookup with "Htag_t_auth Hp") as "%Ht_lookup".
    iPureIntro.
    intros i Hi. eapply Ht.
    rewrite /heaplet_lookup Ht_lookup /= list_to_heaplet_nth list_lookup_lookup_total //.
    by apply lookup_lt_is_Some_2.
  Qed.

  Lemma bor_interp_readN_source σ_t σ_s M_call M_tag M_t M_s (t : tag) tk l v_s :
    bor_interp_inner σ_t σ_s M_call M_tag M_t M_s -∗
    l ↦s∗[tk]{t} v_s -∗
    t $$ tk -∗
      ⌜∀ i:nat, (i < length v_s)%nat → loc_controlled (l +ₗ i) t tk (v_s !!! i) σ_s⌝.
  Proof.
    iIntros "((Hc & Htag_auth & Htag_t_auth & Htag_s_auth) & Htainted & Hpub_cid & Hsrel & %Hcall & %Htag_interp & %Hwf_s & %Hwf_t)".
    iIntros "Hp Htag".
    iPoseProof (tkmap_lookup with "Htag_auth Htag") as "%Htag_lookup".
    destruct Htag_interp as (Htag_interp & _ & _).
    destruct (Htag_interp _ _ Htag_lookup) as (_ & _ & _ & _ & Hs & _).
    iPoseProof (ghost_map_lookup with "Htag_s_auth Hp") as "%Hs_lookup".
    iPureIntro. intros i Hi. eapply Hs.
    rewrite /heaplet_lookup Hs_lookup /= list_to_heaplet_nth list_lookup_lookup_total //.
    by apply lookup_lt_is_Some_2.
  Qed.

  Lemma bor_interp_readN_source_after_accesss b σ_t σ_s M_call M_tag M_t M_s t l_rd l_hl tk sz scs_hl scs_rd:
    read_range l_rd.2 sz (list_to_heaplet scs_hl l_hl.2) = Some scs_rd →
    l_hl.1 = l_rd.1 →
    length scs_rd ≠ 0%nat →
    trees_contain t (strs σ_s) l_rd.1 →
    is_Some (apply_within_trees (memory_access_maybe_nonchildren_only b AccessRead (scs σ_s) t (l_rd.2, length scs_rd)) l_rd.1 (strs σ_s)) →
    bor_interp_inner σ_t σ_s M_call M_tag M_t M_s -∗
    l_hl ↦s∗[tk]{t} scs_hl -∗
    t $$ tk -∗
    ∃ it tr, ⌜σ_s.(strs) !! l_rd.1 = Some tr ∧ tree_lookup tr t it ∧
    ∀ i : nat, (i < length scs_rd)%nat → bor_state_own_on (l_rd +ₗ i) t tk σ_s it tr ∧ σ_s.(shp) !! (l_rd +ₗ i) = scs_rd !! i⌝.
  Proof.
    iIntros (Hrr Hsameblk Hnn Hcontains (trs' & Htrs')) "((Hc & Htag_auth & Htag_t_auth & Htag_s_auth) & Htainted & Hpub_cid & #Hsrel & %Hcall_interp & %Htag_interp & %Hwf_s & %Hwf_t)".
    iIntros "Hp Htag".
    iDestruct "Hsrel" as "(%Hdom_eq&%Hstrs_eq&%Hsnp_eq&%Hsnv_eq&%Hscs_eq&Hsrel)".
    iPoseProof (tkmap_lookup with "Htag_auth Htag") as "%Htag_lookup".
    iPoseProof (ghost_map_lookup with "Htag_s_auth Hp") as "%Ht_lookup".
    pose proof Htag_interp as (Htag_interp2 & _).
    destruct (Htag_interp2 _ _ Htag_lookup) as (_ & _ & _ & Ht & Hs & Hagree).
    pose proof Htrs' as (tr1&Htr1&(tr1'&Htr1'&[= <-])%bind_Some)%bind_Some.
    rewrite /trees_contain /trees_at_block Htr1 in Hcontains.
    odestruct unique_implies_lookup as (it&Hit).
    { eapply Hwf_s. 1: exact Htr1. apply Hcontains. }
    eapply read_range_length in Hrr as Hsz.
    assert (sz ≠ 0%nat) as Hnnsz by lia.
    iExists it, tr1.
    do 2 (iSplit; first done). iPureIntro.
    intros i Hi.
    eapply lookup_lt_is_Some_2 in Hi as Hissome. destruct Hissome as (sc&Hsc).
    eapply read_range_lookup_nth in Hsc as Hschl. 2: eassumption.
    eapply list_to_heaplet_lookup_Some in Hschl as Hbounds.
    assert (∃ (i_rd:nat), (l_hl.2 + i_rd = l_rd.2 + i)%Z) as (i_rd&Hi_rd).
    { exists (Z.to_nat ((l_rd.2 + i) - l_hl.2)). lia. }
    ospecialize (Hs (l_rd +ₗ i) sc _).
    1: rewrite /heaplet_lookup /= -Hsameblk Ht_lookup /= //.
    destruct Hs as (Ht1&Ht2); last first.
    { destruct Ht1 as (it'&tr'&Hit'&Htr'&HH).
      simpl in *.
      assert (tr1 = tr') as <- by congruence.
      assert (it = it') as <- by by eapply tree_lookup_unique.
      rewrite Ht2. done. }
    enough (perm (item_lookup it (l_rd.2 + i)) ≠ Disabled).
    { destruct tk; try done.
      all: exists it; split; first by eexists.
      all: intros _; done. }
    eapply mk_is_Some, apply_access_success_condition, every_node_eqv_universal in Htr1'.
    2: eapply exists_determined_exists; eapply Hit.
    setoid_rewrite is_Some_ignore_bind in Htr1'.
    setoid_rewrite <- mem_apply_range'_success_condition in Htr1'.
    ospecialize (Htr1' (l_rd.2 + i) _).
    { split; simpl in *; lia. }
    eapply tree_lookup_correct_tag in Hit as Hit'; subst t.
    rewrite rel_dec_refl in Htr1'.
    rewrite maybe_non_children_only_no_effect in Htr1'. 2: done.
    destruct Htr1' as [x (x1&Hx1&_)%bind_Some].
    rewrite /item_lookup.
    rewrite /apply_access_perm_inner in Hx1.
    intros Hd; rewrite Hd in Hx1. congruence.
  Qed.

  Lemma bor_interp_readN_target_after_accesss b σ_t σ_s M_call M_tag M_t M_s t l_rd l_hl tk sz scs_hl scs_rd:
    read_range l_rd.2 sz (list_to_heaplet scs_hl l_hl.2) = Some scs_rd →
    l_hl.1 = l_rd.1 →
    length scs_rd ≠ 0%nat →
    trees_contain t (strs σ_t) l_rd.1 →
    is_Some (apply_within_trees (memory_access_maybe_nonchildren_only b AccessRead (scs σ_t) t (l_rd.2, length scs_rd)) l_rd.1 (strs σ_t)) →
    bor_interp_inner σ_t σ_s M_call M_tag M_t M_s -∗
    l_hl ↦t∗[tk]{t} scs_hl -∗
    t $$ tk -∗
    ∃ it tr, ⌜σ_t.(strs) !! l_rd.1 = Some tr ∧ tree_lookup tr t it ∧
    ∀ i : nat, (i < length scs_rd)%nat → bor_state_own_on (l_rd +ₗ i) t tk σ_t it tr ∧ σ_t.(shp) !! (l_rd +ₗ i) = scs_rd !! i⌝.
  Proof.
    iIntros (Hrr Hsameblk Hnn Hcontains (trs' & Htrs')) "((Hc & Htag_auth & Htag_t_auth & Htag_s_auth) & Htainted & Hpub_cid & #Hsrel & %Hcall_interp & %Htag_interp & %Hwf_s & %Hwf_t)".
    iIntros "Hp Htag".
    iDestruct "Hsrel" as "(%Hdom_eq&%Hstrs_eq&%Hsnp_eq&%Hsnv_eq&%Hscs_eq&Hsrel)".
    iPoseProof (tkmap_lookup with "Htag_auth Htag") as "%Htag_lookup".
    iPoseProof (ghost_map_lookup with "Htag_t_auth Hp") as "%Ht_lookup".
    pose proof Htag_interp as (Htag_interp2 & _).
    destruct (Htag_interp2 _ _ Htag_lookup) as (_ & _ & _ & Ht & Hs & Hagree).
    pose proof Htrs' as (tr1&Htr1&(tr1'&Htr1'&[= <-])%bind_Some)%bind_Some.
    rewrite /trees_contain /trees_at_block Htr1 in Hcontains.
    odestruct unique_implies_lookup as (it&Hit).
    { eapply Hwf_t. 1: exact Htr1. apply Hcontains. }
    eapply read_range_length in Hrr as Hsz.
    assert (sz ≠ 0%nat) as Hnnsz by lia.
    iExists it, tr1.
    do 2 (iSplit; first done). iPureIntro.
    intros i Hi.
    eapply lookup_lt_is_Some_2 in Hi as Hissome. destruct Hissome as (sc&Hsc).
    eapply read_range_lookup_nth in Hsc as Hschl. 2: eassumption.
    eapply list_to_heaplet_lookup_Some in Hschl as Hbounds.
    assert (∃ (i_rd:nat), (l_hl.2 + i_rd = l_rd.2 + i)%Z) as (i_rd&Hi_rd).
    { exists (Z.to_nat ((l_rd.2 + i) - l_hl.2)). lia. }
    ospecialize (Ht (l_rd +ₗ i) sc _).
    1: rewrite /heaplet_lookup /= -Hsameblk Ht_lookup /= //.
    destruct Ht as (Ht1&Ht2); last first.
    { destruct Ht1 as (it'&tr'&Hit'&Htr'&HH).
      simpl in *.
      assert (tr1 = tr') as <- by congruence.
      assert (it = it') as <- by by eapply tree_lookup_unique.
      rewrite Ht2. done. }
    enough (perm (item_lookup it (l_rd.2 + i)) ≠ Disabled).
    { destruct tk; try done.
      all: exists it; split; first by eexists.
      all: intros _; done. }
    eapply mk_is_Some, apply_access_success_condition, every_node_eqv_universal in Htr1'.
    2: eapply exists_determined_exists; eapply Hit.
    setoid_rewrite is_Some_ignore_bind in Htr1'.
    setoid_rewrite <- mem_apply_range'_success_condition in Htr1'.
    ospecialize (Htr1' (l_rd.2 + i) _).
    { split; simpl in *; lia. }
    eapply tree_lookup_correct_tag in Hit as Hit'; subst t.
    rewrite rel_dec_refl in Htr1'.
    rewrite maybe_non_children_only_no_effect in Htr1'. 2: done.
    destruct Htr1' as [x (x1&Hx1&_)%bind_Some].
    rewrite /item_lookup.
    rewrite /apply_access_perm_inner in Hx1.
    intros Hd; rewrite Hd in Hx1. congruence.
  Qed.

(*

  (** * Write lemmas *)
  Lemma loc_controlled_write_update σ bor tk l l' n α' sc v t :
    state_wf σ →
    (bor = Tagged t ∧ (∃ i:nat, l = l' +ₗ i ∧ (i < n)%nat) → tk = tk_pub) →
    memory_written σ.(sst) σ.(scs) l' bor n = Some α' →
    length v = n →
    loc_controlled l t tk sc σ →
    loc_controlled l t tk sc (mkState (write_mem l' v σ.(shp)) α' σ.(scs) σ.(snp) σ.(snc)).
  Proof.
    rewrite /loc_controlled //= => Hwf Hpub Hstack Hlen Hcontrol.
    destruct (write_mem_lookup_case l' v σ.(shp) l) as [(i & Hi & -> & Hwrite_i) | (Hi & ->)];
        first last.
    { (* l is NOT written to *)
      destruct (for_each_lookup _ _ _ _ _ Hstack) as (_ & _ & Hstack_eq).
      rewrite /bor_state_pre /bor_state_own. rewrite !Hstack_eq. 2: intros; apply Hi; lia.
      apply Hcontrol.
    }
    (* considering one of the written-to locations *)
    intros Hpre.
    specialize (for_each_access1 _ _ _ _ _ _ _ Hstack) as Hsub.
    destruct Hcontrol as (Hown & Hmem).
    { destruct tk; simpl in *; [ | | done].
      all: destruct Hpre as (stk & pm & opro & (stk' & -> & Hsubl & _)%Hsub & Hit & Hpm).
      all: apply Hsubl in Hit as ([pm' tg' opro'] & Hit2 & Htg & Hprot & Hperm).
      all: exists stk', pm', opro'; simpl in *; rewrite Htg.
      all:  split_and!; [done | done | rewrite Hperm; done].
    }
    (* we now lead this to a contradiction: the write was UB/the tags are contradictory *)
    specialize (for_each_lookup _ _ _ _ _ Hstack) as (Ha & _).
    destruct tk; simpl in *.
    * (* public *)
      destruct Hpre as (stk' & pm & opro & Hstk' & Hit & Hpm).
      exfalso. destruct Hown as (stk & Hstk & Hactive).
      specialize (Ha i _ ltac:(lia) Hstk) as (stk'' & Hstk'' & Hacc).
      destruct access1 as [[n' ?] | ] eqn:Hacc_eq; last done. injection Hacc as [= ->].
      simplify_eq.
      eapply access1_write_remove_incompatible_active_SRO; [ | done | apply Hacc_eq | done ].
      by eapply Hwf.
    * (* unique *)
      destruct Hpre as (stk' & pm & opro & Hstk' & Hit & Hpm).
      exfalso. destruct Hown as (stk & Hstk & Hprot).
      specialize (Ha i _ ltac:(lia) Hstk) as (stk'' & Hstk'' & Hacc).
      destruct access1 as [[n' ?] | ] eqn:Hacc_eq; last done. injection Hacc as [= ->].
      simplify_eq.
      destruct Hprot as (opro' & stk'' & ->).
      eapply access1_write_remove_incompatible_head;
        [ | eexists; eexists; reflexivity | apply Hacc_eq | | done].
      { by eapply Hwf. }
      (* contradiction, since t is public *)
      intros <-. enough (tk_unq = tk_pub) by congruence.
      apply Hpub. split; first done. eauto.
    * (* local *)
      exfalso.
      specialize (Ha i _ ltac:(lia) Hown) as (stk'' & Hstk'' & Hacc).
      destruct access1 as [[n' ?] | ] eqn:Hacc_eq; last done. injection Hacc as [= ->].
      specialize (access1_in_stack _ _ _ _ _ _ Hacc_eq) as (it & ->%list_elem_of_singleton & Htg & _).
      (* contradiction, since t is public *)
      simpl in Htg. subst bor. enough (tk_local = tk_pub) by congruence.
      apply Hpub. split; first done. exists i. split; first done. lia.
  Qed.

  Lemma state_upd_mem_compose f g σ :
    state_upd_mem f (state_upd_mem g σ) = state_upd_mem (f ∘ g) σ.
  Proof. destruct σ. done. Qed.

  Lemma write_mem_insert_commute_1 l l' v sc M :
    l.2 < l'.2 →
    <[ l := sc ]> (write_mem l' v M) = write_mem l' v (<[ l := sc ]> M).
  Proof.
    induction v as [|? v IH] in l, l', sc, M |-*; cbn; first done.
    intros Hl. rewrite (IH l (l' +ₗ 1)); first last.
    { destruct l', l; cbn in *; lia. }
    rewrite insert_insert_ne; first done. intros ->; lia.
  Qed.
  Lemma write_mem_head l sc v M :
    <[ l := sc ]> (write_mem (l +ₗ 1) v M) = write_mem l (sc :: v) M.
  Proof. rewrite write_mem_insert_commute_1; last by destruct l; cbn; lia. done. Qed.

  Global Instance state_upd_mem_proper : Proper ((eq ==> eq) ==> eq ==> eq) state_upd_mem.
  Proof.
    intros f g Heq ? σ ->. destruct σ as [ mem ]. by rewrite /state_upd_mem (Heq mem mem eq_refl).
  Qed.
  Lemma state_upd_write_mem_head sc v l σ :
    state_upd_mem (<[ l := sc ]> ∘ write_mem (l +ₗ 1) v) σ = state_upd_mem (write_mem l (sc :: v)) σ.
  Proof. destruct σ. rewrite /state_upd_mem. cbn. by rewrite write_mem_head. Qed.

  Lemma state_wf_upd_mem σ l sc :
    is_Some (σ.(shp) !! l) →
    state_wf σ →
    state_wf (state_upd_mem (<[l := sc]>) σ).
  Proof.
    intros Hs []. constructor; try done.
    rewrite dom_insert //.
    have ->: {[l]} ∪ dom (shp σ) ≡ dom (shp σ); last done.
    split; rewrite elem_of_union; last by eauto.
    intros [ ->%elem_of_singleton_1 | ]; last done.
    by apply elem_of_dom.
    Qed.

  Lemma bor_interp_write_target_local σ_t σ_s (t : ptr_id) l sc sc' :
    bor_interp σ_t σ_s -∗
    l ↦t[tk_local]{t} sc -∗
    t $$ tk_local ==∗
    bor_interp (state_upd_mem (<[l := sc']>) σ_t) σ_s ∗
    l ↦t[tk_local]{t} sc' ∗
    t $$ tk_local.
  Proof.
    iIntros "(%M_call & %M_tag & %M_t & %M_s & (Hc & Htag_auth & Htag_t_auth & Htag_s_auth) & Htainted & Hpub_cid & Hsrel & ? & %Htag_interp & %Hwf_s & %Hwf_t)".
    iIntros "Hp Htag".
    iPoseProof (tkmap_lookup with "Htag_auth Htag") as "%Htag_lookup".
    destruct Htag_interp as (Htag_interp & Ht_dom & Hs_dom).
    destruct (Htag_interp _ _ Htag_lookup) as (_ & _ & Ht & Hs & Hagree).
    iPoseProof (ghost_map_lookup with "Htag_t_auth Hp") as "%Ht_lookup".
    specialize (Ht _ _ Ht_lookup) as Hcontrol.
    specialize (loc_controlled_local _ _ _ _ Hcontrol) as (Hstack & Hmem).

    iMod (ghost_map_update sc' with "Htag_t_auth Hp") as "[Htag_t_auth $]".
    iModIntro. iFrame "Htag". rewrite /bor_interp.
    iExists M_call, M_tag, (<[(t, l):=sc']> M_t), M_s.
    iFrame. cbn. iSplitL "Hsrel".
    { iApply (state_rel_upd_priv_target with "Hsrel").
      - eauto.
      - exists tk_local. split_and!; [done | by eauto | by left ].
    }
    iSplitL; first last.
    { repeat iSplitL; [ done.. | ].
      iPureIntro. apply state_wf_upd_mem; [by eauto | done].
    }

    iPureIntro.
    split_and!.
    - intros t' tk' (? & ? & H')%Htag_interp. do 2 (split; first done).
      destruct H' as (Ha_t & Ha_s & Hagree').
      split_and!; [ | done | ].
      + intros l' sc_t.
        destruct (decide (t = t')) as [<- | Hneq]; first last.
        { rewrite lookup_insert_ne; last congruence. intros Hsc_t.
          destruct (decide (l' = l)) as [-> | Hneq_loc].
          { (* this is fine as tag t has local ownership: t' doesn't have any control *)
            eapply loc_controlled_local_authoritative; [ | by apply Ha_t | done].
            eapply loc_controlled_mem_insert. done.
          }
          apply loc_controlled_mem_insert_ne; [done | by apply Ha_t].
        }
        revert Ha_t.
        destruct (decide (l' = l)) as [-> | Hneq_loc] => Ha_t.
        * rewrite lookup_insert_eq => [= ->]. by eapply loc_controlled_mem_insert, Ha_t.
        * rewrite lookup_insert_ne; last congruence. intros ?.
          eapply loc_controlled_mem_insert_ne; [done | by apply Ha_t].
      + destruct (decide (t = t')) as [<- | Hneq].
        * eapply dom_agree_on_tag_upd_target; eauto.
        * eapply dom_agree_on_tag_upd_ne_target; eauto.
    - intros t' l'. rewrite lookup_insert_is_Some. intros [[= <- <-] | [_ ?%Ht_dom]]; last done. eauto.
    - done.
  Qed.

  Lemma bor_interp_writeN_target_local σ_t σ_s (t : ptr_id) l v v' :
    bor_interp σ_t σ_s -∗
    l ↦t∗[tk_local]{t} v -∗
    t $$ tk_local -∗
    ⌜length v' = length v⌝ ==∗
    bor_interp (state_upd_mem (write_mem l v') σ_t) σ_s ∗
    l ↦t∗[tk_local]{t} v' ∗
    t $$ tk_local.
  Proof.
    iInduction v' as [ | sc' v'] "IH" forall (l v).
    - iIntros "Hbor Hp Ht %Hlen". destruct v; last done. iFrame "Ht Hp". iModIntro. destruct σ_t; eauto.
    - iIntros "Hbor Hp Ht %Hlen". destruct v as [ | sc v]; first done.
      iPoseProof (big_sepL_cons with "Hp") as "[Hh Hp]".
      iMod  ("IH" $! (l +ₗ 1) v with "Hbor [Hp] Ht []") as "(Hbor & Hp & Ht)".
      { iApply (big_sepL_mono with "Hp"). intros i sc0 Hsc0. cbn.
        rewrite shift_loc_assoc. replace (1 + i)%Z with (Z.of_nat $ S i) by lia. done. }
      { cbn in Hlen. iPureIntro. lia. }
      iMod (bor_interp_write_target_local  _ _ _ _ _ sc' with "Hbor Hh Ht") as "(Hbor & Hh & Ht)".
      iModIntro. iFrame "Ht". iSplitL "Hbor".
      { rewrite state_upd_mem_compose. rewrite shift_loc_0_nat. by rewrite state_upd_write_mem_head. }
      iApply big_sepL_cons. iFrame "Hh". iApply (big_sepL_mono with "Hp").
      intros i sc0 Hsc0. cbn.
      rewrite shift_loc_assoc. replace (1 + i)%Z with (Z.of_nat $ S i) by lia. done.
  Qed.

  Lemma bor_interp_write_source_local σ_t σ_s (t : ptr_id) l sc sc' :
    bor_interp σ_t σ_s -∗
    l ↦s[tk_local]{t} sc -∗
    t $$ tk_local ==∗
    bor_interp σ_t (state_upd_mem (<[l := sc']>) σ_s) ∗
    l ↦s[tk_local]{t} sc' ∗
    t $$ tk_local.
  Proof.
    iIntros "(%M_call & %M_tag & %M_t & %M_s & (Hc & Htag_auth & Htag_t_auth & Htag_s_auth) & Htainted & Hpub_cid & Hsrel & ? & %Htag_interp & %Hwf_s & %Hwf_t)".
    iIntros "Hp Htag".
    iPoseProof (tkmap_lookup with "Htag_auth Htag") as "%Htag_lookup".
    destruct Htag_interp as (Htag_interp & Ht_dom & Hs_dom).
    destruct (Htag_interp _ _ Htag_lookup) as (_ & _ & Ht & Hs & Hagree).
    iPoseProof (ghost_map_lookup with "Htag_s_auth Hp") as "%Hs_lookup".
    specialize (Hs _ _ Hs_lookup) as Hcontrol.
    specialize (loc_controlled_local _ _ _ _ Hcontrol) as (Hstack & Hmem).
    iPoseProof (state_rel_dom_eq with "Hsrel") as "%Hdom_eq".

    iMod (ghost_map_update sc' with "Htag_s_auth Hp") as "[Htag_s_auth $]".
    iModIntro. iFrame "Htag". rewrite /bor_interp.
    iExists M_call, M_tag, M_t, (<[(t, l):=sc']> M_s).
    iFrame. cbn. iSplitL "Hsrel".
    { iApply (state_rel_upd_priv_source with "Hsrel").
      - apply elem_of_dom. rewrite Hdom_eq. apply elem_of_dom. eauto.
      - exists tk_local. split_and!; [done | | by left ].
        apply Hagree. eauto.
    }
    iSplitL; first last.
    { iSplitL; last done. iPureIntro. apply state_wf_upd_mem; [by eauto | done]. }

    iPureIntro.
    split_and!.
    - intros t' tk' (? & ? & H')%Htag_interp. do 2 (split; first done).
      destruct H' as (Ha_t & Ha_s & Hagree').
      split_and!; [ done | | ].
      + intros l' sc_t.
        destruct (decide (t = t')) as [<- | Hneq]; first last.
        { rewrite lookup_insert_ne; last congruence. intros Hsc_t.
          destruct (decide (l' = l)) as [-> | Hneq_loc].
          { (* this is fine as tag t has local ownership: t' doesn't have any control *)
            eapply loc_controlled_local_authoritative; [ | by apply Ha_s | done].
            eapply loc_controlled_mem_insert. done.
          }
          apply loc_controlled_mem_insert_ne; [done | by apply Ha_s].
        }
        revert Ha_s.
        destruct (decide (l' = l)) as [-> | Hneq_loc] => Ha_s.
        * rewrite lookup_insert_eq => [= ->]. by eapply loc_controlled_mem_insert, Ha_s.
        * rewrite lookup_insert_ne; last congruence. intros ?.
          eapply loc_controlled_mem_insert_ne; [done | by apply Ha_s].
      + destruct (decide (t = t')) as [<- | Hneq].
        * eapply dom_agree_on_tag_upd_source; eauto.
        * eapply dom_agree_on_tag_upd_ne_source; eauto.
    - done.
    - intros t' l'. rewrite lookup_insert_is_Some. intros [[= <- <-] | [_ ?%Hs_dom]]; last done. eauto.
  Qed.

  Lemma bor_interp_writeN_source_local σ_t σ_s (t : ptr_id) l v v' :
    bor_interp σ_t σ_s -∗
    l ↦s∗[tk_local]{t} v -∗
    t $$ tk_local -∗
    ⌜length v' = length v⌝ ==∗
    bor_interp σ_t (state_upd_mem (write_mem l v') σ_s) ∗
    l ↦s∗[tk_local]{t} v' ∗
    t $$ tk_local.
  Proof.
    iInduction v' as [ | sc' v'] "IH" forall (l v).
    - iIntros "Hbor Hp Hs %Hlen". destruct v; last done. iFrame "Hs Hp". iModIntro. destruct σ_s; eauto.
    - iIntros "Hbor Hp Hs %Hlen". destruct v as [ | sc v]; first done.
      iPoseProof (big_sepL_cons with "Hp") as "[Hh Hp]".
      iMod  ("IH" $! (l +ₗ 1) v with "Hbor [Hp] Hs []") as "(Hbor & Hp & Hs)".
      { iApply (big_sepL_mono with "Hp"). intros i sc0 Hsc0. cbn.
        rewrite shift_loc_assoc. replace (1 + i)%Z with (Z.of_nat $ S i) by lia. done. }
      { cbn in Hlen. iPureIntro. lia. }
      iMod (bor_interp_write_source_local  _ _ _ _ _ sc' with "Hbor Hh Hs") as "(Hbor & Hh & Hs)".
      iModIntro. iFrame "Hs". iSplitL "Hbor".
      { rewrite state_upd_mem_compose. rewrite shift_loc_0_nat. by rewrite state_upd_write_mem_head. }
      iApply big_sepL_cons. iFrame "Hh". iApply (big_sepL_mono with "Hp").
      intros i sc0 Hsc0. cbn.
      rewrite shift_loc_assoc. replace (1 + i)%Z with (Z.of_nat $ S i) by lia. done.
  Qed.

  (* TODO move *)
  Lemma loc_protected_by_mem_insert σ t l c sc' :
    loc_protected_by σ t l c →
    loc_protected_by (state_upd_mem <[l := sc']> σ) t l c.
  Proof. apply id. Qed.

  Lemma bor_interp_write_target_protected σ_t σ_s (t : ptr_id) l sc sc' c M :
    call_set_in M t l →
    bor_interp σ_t σ_s -∗
    l ↦t[tk_unq]{t} sc -∗
    c @@ M -∗
    t $$ tk_unq ==∗
    bor_interp (state_upd_mem (<[l := sc']>) σ_t) σ_s ∗
    l ↦t[tk_unq]{t} sc' ∗
    c @@ M ∗
    t $$ tk_unq.
  Proof.
    iIntros (Hl) "(%M_call & %M_tag & %M_t & %M_s & (Hc & Htag_auth & Htag_t_auth & Htag_s_auth) & Htainted & Hpub_cid & Hsrel & %Hcall_interp & %Htag_interp & %Hwf_s & %Hwf_t)".
    iIntros "Hp Hcall Htag".
    iPoseProof (tkmap_lookup with "Htag_auth Htag") as "%Htag_lookup".
    iPoseProof (ghost_map_lookup with "Hc Hcall") as "%Hcall".
    destruct Htag_interp as (Htag_interp & Ht_dom & Hs_dom).
    destruct (Htag_interp _ _ Htag_lookup) as (_ & _ & Ht & Hs & Hagree).
    iPoseProof (ghost_map_lookup with "Htag_t_auth Hp") as "%Ht_lookup".
    specialize (Ht _ _ Ht_lookup) as Hcontrol.
    assert (Hc_in : call_set_in' M_call c t l). { exists M. eauto. }
    specialize (call_set_interp_access _ _ _ _ _ Hcall_interp Hc_in) as Hprotected.
    specialize (loc_protected_bor_state_pre _ _ _ _ tk_unq Hprotected) as [Hown Hmem]%Hcontrol.

    iMod (ghost_map_update sc' with "Htag_t_auth Hp") as "[Htag_t_auth $]".
    iModIntro. iFrame "Htag Hcall". rewrite /bor_interp.
    iExists M_call, M_tag, (<[(t, l):=sc']> M_t), M_s.
    iFrame. cbn. iSplitL "Hsrel".
    { iApply (state_rel_upd_priv_target with "Hsrel").
      - eauto.
      - exists tk_unq. split_and!; [done | by eauto | right ].
        split; first done. eauto.
    }
    iSplitL; first done.
    iSplitL; first last.
    { repeat iSplitL; [ done.. | ].
      iPureIntro. apply state_wf_upd_mem; [by eauto | done].
    }

    iPureIntro.
    split_and!.
    - intros t' tk' (? & ? & H')%Htag_interp. do 2 (split; first done).
      destruct H' as (Ha_t & Ha_s & Hagree').
      split_and!; [ | done | ].
      + intros l' sc_t.
        destruct (decide (t = t')) as [<- | Hneq]; first last.
        { rewrite lookup_insert_ne; last congruence. intros Hsc_t.
          destruct (decide (l' = l)) as [-> | Hneq_loc].
          { (* this is fine as t' doesn't have any control *)
            eapply loc_controlled_protected_authoritative; [ |  | by apply Ha_t | done].
            - eapply loc_protected_by_mem_insert. done.
            - eapply loc_controlled_mem_insert. done.
          }
          apply loc_controlled_mem_insert_ne; [done | by apply Ha_t].
        }
        revert Ha_t.
        destruct (decide (l' = l)) as [-> | Hneq_loc] => Ha_t.
        * rewrite lookup_insert_eq => [= ->]. by eapply loc_controlled_mem_insert, Ha_t.
        * rewrite lookup_insert_ne; last congruence. intros ?.
          eapply loc_controlled_mem_insert_ne; [done | by apply Ha_t].
      + destruct (decide (t = t')) as [<- | Hneq].
        * eapply dom_agree_on_tag_upd_target; eauto.
        * eapply dom_agree_on_tag_upd_ne_target; eauto.
    - intros t' l'. rewrite lookup_insert_is_Some. intros [[= <- <-] | [_ ?%Ht_dom]]; last done. eauto.
    - done.
  Qed.

  Lemma bor_interp_writeN_target_protected σ_t σ_s (t : ptr_id) l v v' c M :
    (∀ i: nat, (i < length v)%nat → call_set_in M t (l +ₗ i)) →
    bor_interp σ_t σ_s -∗
    l ↦t∗[tk_unq]{t} v -∗
    t $$ tk_unq -∗
    c @@ M -∗
    ⌜length v' = length v⌝ ==∗
    bor_interp (state_upd_mem (write_mem l v') σ_t) σ_s ∗
    l ↦t∗[tk_unq]{t} v' ∗
    c @@ M ∗
    t $$ tk_unq.
  Proof.
    intros Hin.
    iInduction v' as [ | sc' v'] "IH" forall (l v Hin).
    - iIntros "Hbor Hp Hs Hc %Hlen". destruct v; last done. iFrame "Hs Hp Hc". iModIntro. destruct σ_t; eauto.
    - iIntros "Hbor Hp Hs Hc %Hlen". destruct v as [ | sc v]; first done.
      iPoseProof (big_sepL_cons with "Hp") as "[Hh Hp]".
      iMod  ("IH" $! (l +ₗ 1) v with "[] Hbor [Hp] Hs Hc []") as "(Hbor & Hp & Hc & Hs)".
      { iPureIntro. intros i Hi. rewrite shift_loc_assoc. replace (1+ i) with (Z.of_nat (S i)) by lia.
        apply Hin. simpl; lia. }
      { iApply (big_sepL_mono with "Hp"). intros i sc0 Hsc0. cbn.
        rewrite shift_loc_assoc. replace (1 + i)%Z with (Z.of_nat $ S i) by lia. done. }
      { cbn in Hlen. iPureIntro. lia. }
      iMod (bor_interp_write_target_protected  _ _ _ _ _ sc' with "Hbor Hh Hc Hs") as "(Hbor & Hh & Hc & Hs)".
      { apply Hin. simpl; lia. }
      iModIntro. iFrame "Hs Hc". iSplitL "Hbor".
      { rewrite state_upd_mem_compose. rewrite shift_loc_0_nat. by rewrite state_upd_write_mem_head. }
      iApply big_sepL_cons. iFrame "Hh". iApply (big_sepL_mono with "Hp").
      intros i sc0 Hsc0. cbn.
      rewrite shift_loc_assoc. replace (1 + i)%Z with (Z.of_nat $ S i) by lia. done.
  Qed.

  Lemma bor_interp_write_source_protected σ_t σ_s (t : ptr_id) l sc sc' c M :
    call_set_in M t l →
    bor_interp σ_t σ_s -∗
    l ↦s[tk_unq]{t} sc -∗
    c @@ M -∗
    t $$ tk_unq ==∗
    bor_interp σ_t (state_upd_mem (<[l := sc']>) σ_s) ∗
    l ↦s[tk_unq]{t} sc' ∗
    c @@ M ∗
    t $$ tk_unq.
  Proof.
    iIntros (Hl) "(%M_call & %M_tag & %M_t & %M_s & (Hc & Htag_auth & Htag_t_auth & Htag_s_auth) & Htainted & Hpub_cid & Hsrel & %Hcall_interp & %Htag_interp & %Hwf_s & %Hwf_t)".
    iIntros "Hp Hcall Htag".
    iPoseProof (tkmap_lookup with "Htag_auth Htag") as "%Htag_lookup".
    iPoseProof (ghost_map_lookup with "Hc Hcall") as "%Hcall".
    destruct Htag_interp as (Htag_interp & Ht_dom & Hs_dom).
    destruct (Htag_interp _ _ Htag_lookup) as (_ & _ & Ht & Hs & Hagree).
    iPoseProof (ghost_map_lookup with "Htag_s_auth Hp") as "%Hs_lookup".
    specialize (Hs _ _ Hs_lookup) as Hcontrol.
    assert (Hc_in : call_set_in' M_call c t l). { exists M. eauto. }
    specialize (call_set_interp_access _ _ _ _ _ Hcall_interp Hc_in) as Hprotected_t.
    iPoseProof (loc_protected_by_source with "Hsrel [//]") as "%Hprotected".
    specialize (loc_protected_bor_state_pre _ _ _ _ tk_unq Hprotected) as [Hown Hmem]%Hcontrol.
    iPoseProof (state_rel_dom_eq with "Hsrel") as "%Hdom_eq".

    iMod (ghost_map_update sc' with "Htag_s_auth Hp") as "[Htag_s_auth $]".
    iModIntro. iFrame "Htag Hcall". rewrite /bor_interp.
    iExists M_call, M_tag, M_t, (<[(t, l):=sc']> M_s).
    iFrame. cbn. iSplitL "Hsrel".
    { iApply (state_rel_upd_priv_source with "Hsrel").
      - apply elem_of_dom. rewrite Hdom_eq. apply elem_of_dom. eauto.
      - exists tk_unq. split_and!; [done |apply Hagree; eauto | right ].
        split; first done. eauto.
    }

    iSplitL; first done.
    iSplitL; first last.
    { repeat iSplitL; [ |done ].
      iPureIntro. apply state_wf_upd_mem; [by eauto | done].
    }

    iPureIntro.
    split_and!.
    - intros t' tk' (? & ? & H')%Htag_interp. do 2 (split; first done).
      destruct H' as (Ha_t & Ha_s & Hagree').
      split_and!; [ done| | ].
      + intros l' sc_s.
        destruct (decide (t = t')) as [<- | Hneq]; first last.
        { rewrite lookup_insert_ne; last congruence. intros Hsc_t.
          destruct (decide (l' = l)) as [-> | Hneq_loc].
          { (* this is fine as t' doesn't have any control *)
            eapply loc_controlled_protected_authoritative; [ |  | by apply Ha_s | done].
            - eapply loc_protected_by_mem_insert. done.
            - eapply loc_controlled_mem_insert. done.
          }
          apply loc_controlled_mem_insert_ne; [done | by apply Ha_s].
        }
        revert Ha_s.
        destruct (decide (l' = l)) as [-> | Hneq_loc] => Ha_s.
        * rewrite lookup_insert_eq => [= ->]. by eapply loc_controlled_mem_insert, Ha_s.
        * rewrite lookup_insert_ne; last congruence. intros ?.
          eapply loc_controlled_mem_insert_ne; [done | by apply Ha_s].
      + destruct (decide (t = t')) as [<- | Hneq].
        * eapply dom_agree_on_tag_upd_source; eauto.
        * eapply dom_agree_on_tag_upd_ne_source; eauto.
    - done.
    - intros t' l'. rewrite lookup_insert_is_Some. intros [[= <- <-] | [_ ?%Hs_dom]]; last done. eauto.
  Qed.

  Lemma bor_interp_writeN_source_protected σ_t σ_s (t : ptr_id) l v v' c M :
    (∀ i: nat, (i < length v)%nat → call_set_in M t (l +ₗ i)) →
    bor_interp σ_t σ_s -∗
    l ↦s∗[tk_unq]{t} v -∗
    t $$ tk_unq -∗
    c @@ M -∗
    ⌜length v' = length v⌝ ==∗
    bor_interp σ_t (state_upd_mem (write_mem l v') σ_s) ∗
    l ↦s∗[tk_unq]{t} v' ∗
    c @@ M ∗
    t $$ tk_unq.
  Proof.
    intros Hin.
    iInduction v' as [ | sc' v'] "IH" forall (l v Hin).
    - iIntros "Hbor Hp Hs Hc %Hlen". destruct v; last done. iFrame "Hs Hp Hc". iModIntro. destruct σ_s; eauto.
    - iIntros "Hbor Hp Hs Hc %Hlen". destruct v as [ | sc v]; first done.
      iPoseProof (big_sepL_cons with "Hp") as "[Hh Hp]".
      iMod  ("IH" $! (l +ₗ 1) v with "[] Hbor [Hp] Hs Hc []") as "(Hbor & Hp & Hc & Hs)".
      { iPureIntro. intros i Hi. rewrite shift_loc_assoc. replace (1+ i) with (Z.of_nat (S i)) by lia.
        apply Hin. simpl; lia. }
      { iApply (big_sepL_mono with "Hp"). intros i sc0 Hsc0. cbn.
        rewrite shift_loc_assoc. replace (1 + i)%Z with (Z.of_nat $ S i) by lia. done. }
      { cbn in Hlen. iPureIntro. lia. }
      iMod (bor_interp_write_source_protected  _ _ _ _ _ sc' with "Hbor Hh Hc Hs") as "(Hbor & Hh & Hc & Hs)".
      { apply Hin. simpl; lia. }
      iModIntro. iFrame "Hs Hc". iSplitL "Hbor".
      { rewrite state_upd_mem_compose. rewrite shift_loc_0_nat. by rewrite state_upd_write_mem_head. }
      iApply big_sepL_cons. iFrame "Hh". iApply (big_sepL_mono with "Hp").
      intros i sc0 Hsc0. cbn.
      rewrite shift_loc_assoc. replace (1 + i)%Z with (Z.of_nat $ S i) by lia. done.
  Qed.
  *)
  (** Dealloc lemmas *)
  Lemma loc_controlled_dealloc_update σ l l' sz (α' : trees) (acc_tg lu_tg : tag) (tk : tag_kind) sc :
    apply_within_trees (memory_deallocate σ.(scs) acc_tg (l.2, sz)) l.1 σ.(strs)  = Some α' →
    state_wf σ →
    trees_contain acc_tg σ.(strs) l.1 →
    (acc_tg = lu_tg → l.1 = l'.1 → tk ≠ tk_local) →
    loc_controlled l' lu_tg tk sc σ →
    loc_controlled l' lu_tg tk sc (mkState (free_mem l sz σ.(shp)) (delete l.1 α') σ.(scs) σ.(snp) σ.(snc)).
  Proof.
    intros Hdealloc Hwf Hcontain Hpub Hcontrol Hpre.
    edestruct free_mem_lookup as [_ free_mem_lookup].
    destruct tk as [|tkk|].
    - (* public *)
      destruct Hpre as (it'&Hlu'&Hndis). simpl in Hlu'|-*.
      destruct Hlu' as (tr'&Htr'&Hlu').
      pose proof Hdealloc as (trl&Htrl&(trl'&Htrl'&[= <-])%bind_Some)%bind_Some.
      rewrite delete_insert_eq in Htr'|-*.
      eapply lookup_delete_Some in Htr' as (Hne&Htr').
      destruct Hcontrol as (Hown&Hmem).
      { exists it'. split; last done. exists tr'. done. }
      split.
      2: { erewrite free_mem_lookup; first done.
           intros i _. intros ->. by simpl in Hne. }
      destruct Hown as (it&tr&Hlu&Htr&Hit).
      exists it, tr. split; first done. split; last done.
      rewrite /= lookup_delete_ne /= //.
    - (* unique *) (* it's the same proof *)
      destruct Hpre as (it'&Hlu'&Hndis). simpl in Hlu'|-*.
      destruct Hlu' as (tr'&Htr'&Hlu').
      pose proof Hdealloc as (trl&Htrl&(trl'&Htrl'&[= <-])%bind_Some)%bind_Some.
      rewrite delete_insert_eq in Htr'|-*.
      eapply lookup_delete_Some in Htr' as (Hne&Htr').
      destruct Hcontrol as (Hown&Hmem).
      { exists it'. split; last done. exists tr'. done. }
      split.
      2: { erewrite free_mem_lookup; first done.
           intros i _. intros ->. by simpl in Hne. }
      destruct Hown as (it&tr&Hlu&Htr&Hit).
      exists it, tr. split; first done. split; last done.
      rewrite /= lookup_delete_ne /= //.
    - (* local *)
      clear Hpre. destruct Hcontrol as [Hown Hshp]; first done. simpl.
      destruct (decide (l.1 = l'.1)) as [Hsameblk|Hne].
      + enough (acc_tg = lu_tg) by by ospecialize (Hpub _ _).
        destruct Hown as (tr&it&Hit&Htr&_&Hothers).
        odestruct unique_implies_lookup as (it2&Hlu2).
        2: symmetry; by eapply Hothers.
        eapply wf_tree_tree_unique. 1: by eapply Hwf.
        rewrite /trees_contain /trees_at_block Hsameblk Htr // in Hcontain.
      + split.
        2: { erewrite free_mem_lookup; first done.
             intros i _. intros ->. by simpl in Hne. }
        destruct Hown as (it&tr&Hit&Htr&HH).
        exists it, tr. split; first done. simpl. split; last done.
        pose proof Hdealloc as (trl&Htrl&(trl'&Htrl'&[= <-])%bind_Some)%bind_Some.
        rewrite delete_insert_eq lookup_delete_ne //.
  Qed. (*


  (** Retag *)
  Lemma loc_controlled_retag_ref σ c l ot T mut α' rk i sc :
    let nt := σ.(snp) in
    let pk := RefPtr mut in
    let tk := match mut with Mutable => tk_unq | Immutable => tk_pub end in
    (if mut is Immutable then is_freeze T else True) →
    retag σ.(sst) σ.(snp) σ.(scs) c l ot rk pk T = Some (Tagged nt, α', S σ.(snp)) →
    (is_two_phase rk = false) →
    (i < tsize T)%nat →
    σ.(shp) !! (l +ₗ i) = Some sc →
    loc_controlled (l +ₗ i) nt tk sc (mkState σ.(shp) α' σ.(scs) (S σ.(snp)) σ.(snc)).
  Proof.
    intros nt pk tk Hfreeze Hretag Hrk Hi Hsc Hpre. split; last done.
    destruct mut.
    * (* unique *)
      destruct Hpre as (st & pm' & opro & Hst & Hit & Hpm'). exists st. split; first done.
      rewrite /retag Hrk in Hretag.
      have EqRT':
        retag_ref σ.(sst) σ.(scs) σ.(snp) l ot T (UniqueRef false) (adding_protector rk c) =
          Some (Tagged nt, α', S nt) by done.
      destruct (tag_on_top_retag_ref_uniq _ _ _ _ _ _ _ _ _ _ EqRT' i ltac:(lia))
        as [pro1 Eqstk1]. rewrite Hst /= in Eqstk1.
      clear -Eqstk1. destruct st as [|? stk1]; [done|].
      simpl in Eqstk1. simplify_eq. by exists pro1, stk1.
    * (* shared *)
      destruct Hpre as (stk' & pm' & pro & Eqstk' & In' & NDIS). simpl in Eqstk'.
      exists stk'. split; [done|].
      have EqRT':
        retag_ref σ.(sst) σ.(scs) σ.(snp) l ot T SharedRef (adding_protector rk c) = Some (Tagged nt, α', S nt) by done.
      have HTOP := (tag_on_top_retag_ref_shr _ _ _ _ _ _ _ _ _ _ Hfreeze EqRT' i ltac:(lia)).
      clear -HTOP Eqstk'.
      apply tag_on_top_shr_active_SRO in HTOP as (?&?&?). by simplify_eq.
  Qed.

  Lemma loc_controlled_retag_update σ c l l' t tk' ot T pk rk α' nt nxtp' sc :
    state_wf σ →
    retag σ.(sst) σ.(snp) σ.(scs) c l ot rk pk T = Some (nt, α', nxtp') →
    (Tagged t = ot → tk' = tk_pub) →
    (t < σ.(snp))%nat →
    loc_controlled l' t tk' sc σ →
    loc_controlled l' t tk' sc (mkState σ.(shp) α' σ.(scs) nxtp' σ.(snc)).
  Proof.
    intros Hwf Hretag Hneq Hlt Hcontrolled.
    intros Hpre. destruct tk'.
    * destruct Hpre as (stk' & pm' & pro & Eqstk' & In' & ND).
      destruct (retag_item_in _ _ _ _ _ _ _ _ _ _ _ _ Hretag _ _ t _ Eqstk' In')
        as (stk & Eqstk & In); [done..|].

      destruct Hcontrolled as (Hown & Hl'). { simpl; naive_solver. }
      cbn. split; last done.
      exists stk'. split; [done|].
      destruct Hown as (stk1 & Eqstk1 & HTOP).
      rewrite Eqstk1 in Eqstk. simplify_eq.
      move : HTOP.
      have ND2 := proj2 (state_wf_stack_item _ Hwf _ _ Eqstk1).
      by apply (retag_item_active_SRO_preserving _ _ _ _ _ _ _ _ _ _ _ _ Hretag _ _ _ _ _ ND2 Eqstk1 Eqstk' In In').
    * destruct Hpre as (stk' & pm' & pro & Eqstk' & In' & ND).
      destruct (retag_item_in _ _ _ _ _ _ _ _ _ _ _ _ Hretag _ _ t _ Eqstk' In')
        as (stk & Eqstk & In); [done..|].
      destruct Hcontrolled as (Hown & Hl'); [simpl; naive_solver|].
      split; last done. cbn.
      exists stk'. split; [done|].
      destruct Hown as (stk1 & Eqstk1 & opro1 & HTOP).
      rewrite Eqstk1 in Eqstk. simplify_eq.
      have ND2 := proj2 (state_wf_stack_item _ Hwf _ _ Eqstk1).
      assert (opro1 = pro ∧ pm' = Unique) as [].
      { have In1 : mkItem Unique (Tagged t) opro1 ∈ stk.
        { destruct HTOP as [? HTOP]. rewrite HTOP. by left. }
        have EQ := stack_item_tagged_NoDup_eq _ _ _ t ND2 In1 In eq_refl eq_refl.
        by simplify_eq. } subst opro1 pm'. exists pro.
      have NEq: Tagged t ≠ ot.
      { intros <-. specialize (Hneq eq_refl). congruence. }
      move : HTOP.
      by apply (retag_item_head_preserving _ _ _ _ _ _ _ _ _ _ _ _ Hretag
                  _ _ _ _ _ ND2 Eqstk1 Eqstk' NEq In').
    * clear Hpre. specialize (Hcontrolled I) as (Hown & Hl'). split; last done.
      move : Hown. cbn.
      have NEq: ot ≠ Tagged t.
      { intros ->. specialize (Hneq eq_refl). congruence. }
      move : NEq. by eapply retag_Some_local.
  Qed. *)

End lemmas.

(*
(* accessing a local location is only possible with the same tag, retaining the same stack for the access *)
Lemma local_access_eq l t t' stk n stk' kind σ_s σ_t M_tag M_t M_s :
  σ_t.(sst) !! l = Some stk →
  access1 stk kind t' σ_t.(scs) = Some (n, stk') →
  M_tag !! t = Some (tk_local, ()) →
  is_Some (M_t !! (t, l)) →
  tag_interp M_tag M_t M_s σ_t σ_s →
  t' = Tagged t ∧ stk' = stk.
Proof.
  intros Hst Haccess Htag Ht Htag_interp.
  specialize (access1_in_stack _ _ _ _ _ _ Haccess) as (it & Hin_stack & <- & Henabled).
  destruct Htag_interp as (Htag_interp & _ & _).
  specialize (Htag_interp _ _ Htag) as (_ & _ & Htl & Hsl & Hdom).
  destruct Ht as (sc_t & Ht).
  specialize (Htl _ _ Ht) as Hcontrol.
  apply loc_controlled_local in Hcontrol as (Hcontrol & _).
  destruct (tag_unique_head_access σ_t.(scs) _ (Tagged t) None kind ltac:(by exists [])) as (n' & Hn).
  move : Hst Hin_stack Haccess .
  rewrite Hcontrol => [= <-]. rewrite list_elem_of_singleton => ->.
  rewrite Hn => [= _ <-]. done.
Qed.

Lemma protector_access_eq l t t' stk n stk' kind σ_s σ_t M_tag Mcall M_t M_s :
  σ_t.(sst) !! l = Some stk →
  access1 stk kind t' σ_t.(scs) = Some (n, stk') →
  M_tag !! t = Some (tk_unq, ()) →
  is_Some (M_t !! (t, l)) →
  (∃ (c: call_id), call_set_in' Mcall c t l) →
  tag_interp M_tag M_t M_s σ_t σ_s →
  call_set_interp Mcall σ_t →
  state_wf σ_t →
  t' = Tagged t.
Proof.
  intros Hst Haccess Htag Ht (c & Hcall) Htag_interp Hcall_interp Hwf.
  specialize (call_set_interp_access _ _ _ _ _ Hcall_interp Hcall) as (Hc_in & _ & (stk'' & pm & Hstk'' & Hin & Hpm)).
  destruct Htag_interp as (Htag_interp & _ & _).
  specialize (Htag_interp _ _ Htag) as (_ & _ & Htl & Hsl & Hdom).
  destruct Ht as (sc_t & Ht).
  specialize (Htl _ _ Ht) as Hcontrol.
  specialize (loc_controlled_unq _ _ _ _ _ Hcontrol Hstk'' ltac:(eauto)) as ((stk''' & opro & ->) & Hmem).
  move : Hstk'' Hin Haccess. rewrite Hst => [= Heq]. move : Hst. rewrite Heq => Hst Hi.
  have ->: opro = Some c.
  { destruct (state_wf_stack_item _ Hwf _ _ Hst) as [_ ND].
    have [=] := stack_item_tagged_NoDup_eq _ _ _ t ND Hi ltac:(by left) eq_refl eq_refl.
    done.
  }
  eapply access1_incompatible_head_protector; [by (eexists; eauto) | done].
Qed.

(* successfully accesses with a private location are only possible when the tag is equal *)
Lemma priv_loc_UB_access_eq l kind σ_s σ_t t t' stk M_tag M_t M_s Mcall :
  σ_t.(sst) !! l = Some stk →
  is_Some (access1 stk kind t' σ_t.(scs)) →
  priv_loc M_tag M_t Mcall t l →
  tag_interp M_tag M_t M_s σ_t σ_s →
  call_set_interp Mcall σ_t →
  state_wf σ_t →
  t' = Tagged t.
Proof.
  intros Hs ([? ?] & Haccess) Hpriv Htag_interp Hcall_interp Hwf.
  destruct Hpriv as (tk & Htag & Ht & [-> | [-> Hc]]).
  - by eapply local_access_eq.
  - eapply protector_access_eq; done.
Qed.

Definition untagged_or_public (M_tag : gmap ptr_id (tag_kind * unit)) t :=
  match t with
  | Tagged t2 => M_tag !! t2 = Some (tk_pub, ())
  | Untagged => True
  end.
Lemma priv_pub_access_UB l kind σ_s σ_t t t' stk M_tag Mcall M_t M_s :
  σ_t.(sst) !! l = Some stk →
  is_Some (access1 stk kind t' σ_t.(scs)) →
  priv_loc M_tag M_t Mcall t l →
  tag_interp M_tag M_t M_s σ_t σ_s →
  call_set_interp Mcall σ_t →
  state_wf σ_t →
  untagged_or_public M_tag t' →
  False.
Proof.
  intros Hs Haccess Hpriv Htag_interp Hcall_interp Hwf.
  rewrite (priv_loc_UB_access_eq _ _ _ _ _ _ _ _ _ _ _ Hs Haccess Hpriv Htag_interp Hcall_interp Hwf).
  destruct Hpriv as (tk & Hl & _ & [-> | [-> _]]); cbn; intros; simplify_eq.
Qed.

Lemma priv_loc_UB_retag_access_eq σ_s σ_t c l old new mut T kind α' nxtp' M_tag M_t M_s Mcall
  (FRZ: if mut is Immutable then is_freeze T else True)
  (N2P: kind ≠ TwoPhase) :
  retag σ_t.(sst) σ_t.(snp) σ_t.(scs) c l old kind (RefPtr mut) T = Some (new, α', nxtp') →
  ∀ i t, (i < tsize T)%nat →
  priv_loc M_tag M_t Mcall t (l +ₗ i) →
  tag_interp M_tag M_t M_s σ_t σ_s →
  call_set_interp Mcall σ_t →
  state_wf σ_t →
  untagged_or_public M_tag old →
  False.
Proof.
  intros Hrt i t Hi.
  have NZST: (0 < tsize T)%nat by lia.
  destruct (retag_change_ref_NZST _ _ _ _ _ _ _ _ _ _ _ _ NZST Hrt);
    subst new nxtp'.
  destruct (retag_Some_Ref _ _ _ _ _ _ _ _ _ _ _ _ NZST FRZ N2P Hrt _ Hi)
    as (stk & stk' & Eqstk & Eqstk' & GR).
  apply grant_access1 in GR; [|by destruct mut].
  revert Eqstk GR. by apply priv_pub_access_UB.
Qed.


(** TODO: these lemmas need a new home *)
Section lemmas.
Context `{!sborGS Σ}.
Implicit Types P Q : iProp Σ.
Implicit Types Φ : expr → expr → iProp Σ.
Implicit Types σ σ_s σ_t : state.
Implicit Types r r_s r_t : result.
Implicit Types l : loc.
Implicit Types f : fname.

Context (Ω : result → result → iProp Σ).


Lemma memory_read_access1 (stks : stacks) l n t calls :
  (∀ i: nat, (i < n)%nat → ∃ stk, stks !! (l +ₗ i) = Some stk ∧ ∃ m, access1 stk AccessRead (Tagged t) calls = Some (m, stk)) →
  memory_read stks calls l (Tagged t) n = Some stks.
Proof.
  induction n as [ | n IH]; cbn; first done.
  intros Hacc1. destruct (Hacc1 n ltac:(lia)) as (stkn & Hl & (m & Hacc1_n)). rewrite Hl.
  cbn. rewrite Hacc1_n. cbn.
  rewrite insert_id; last done. apply IH. intros i Hi. apply Hacc1. lia.
Qed.

Lemma bor_state_own_access1_read l t tk stk σ :
  bor_state_own l t tk σ →
  σ.(sst) !! l = Some stk →
  ∃ n, access1 stk AccessRead (Tagged t) σ.(scs) = Some (n, stk).
Proof.
  intros Hown. destruct tk; cbn in *.
  - destruct Hown as (st & -> & Hsro). move => [= <-]. by apply tag_SRO_top_access.
  - destruct Hown as (st & Hsst & (opro & st' & H)). simplify_eq. rewrite Hsst => [= <-].
    eapply tag_unique_head_access. eexists; eauto.
  - rewrite Hown => [= <-].
    eapply tag_unique_head_access. eexists; eauto.
Qed.


Lemma memory_written_access1 (stks : stacks) l n t calls :
  (∀ i: nat, (i < n)%nat → ∃ stk, stks !! (l +ₗ i) = Some stk ∧ ∃ m, access1 stk AccessWrite (Tagged t) calls = Some (m, stk)) →
  memory_written stks calls l (Tagged t) n = Some stks.
Proof.
  induction n as [ | n IH]; cbn; first done.
  intros Hacc1. destruct (Hacc1 n ltac:(lia)) as (stkn & Hl & (m & Hacc1_n)). rewrite Hl.
  cbn. rewrite Hacc1_n. cbn.
  rewrite insert_id; last done. apply IH. intros i Hi. apply Hacc1. lia.
Qed.

Lemma bor_state_own_access1_write l t tk stk σ :
  tk = tk_local ∨ tk = tk_unq →
  bor_state_own l t tk σ →
  σ.(sst) !! l = Some stk →
  ∃ n, access1 stk AccessWrite (Tagged t) σ.(scs) = Some (n, stk).
Proof.
  intros Htk Hown. destruct tk; cbn in *.
  - naive_solver.
  - destruct Hown as (st & Hsst & (opro & st' & H)). simplify_eq. rewrite Hsst => [= <-].
    eapply tag_unique_head_access. eexists; eauto.
  - rewrite Hown => [= <-].
    eapply tag_unique_head_access. eexists; eauto.
Qed.
End lemmas.

*)
