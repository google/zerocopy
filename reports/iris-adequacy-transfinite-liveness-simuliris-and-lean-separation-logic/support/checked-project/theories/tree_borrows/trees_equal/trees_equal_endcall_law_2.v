From iris.proofmode Require Export proofmode.
From iris.base_logic.lib Require Import ghost_map.
From simuliris.base_logic Require Export gen_sim_prog.
From simuliris.simulation Require Export slsls.
From simuliris.simulation Require Import lifting.
From simuliris.tree_borrows Require Import tkmap_view.
From simuliris.tree_borrows Require Export defs class_instances.
From simuliris.tree_borrows Require Import steps_progress steps_inv.
From simuliris.tree_borrows Require Import tree_access_laws logical_state inv_accessors.
From simuliris.tree_borrows.trees_equal Require Import trees_equal_base random_lemmas trees_equal_preserved_by_access trees_equal_more_access.

Section utils.

  Context (C : call_id_set).


  Lemma parents_not_disabled_child_not_prot_init tr tg1 tg2 it1 it2 off
    (Hwf : wf_tree tr)
    (HH : protected_parents_not_disabled C tr) :
    tree_lookup tr tg1 it1 →  
    tree_lookup tr tg2 it2 →
    ParentChildIn tg1 tg2 tr →
    perm (item_lookup it1 off) = Disabled →
    initialized (item_lookup it2 off) = PermInit →
    perm (item_lookup it2 off) ≠ Cell →
    protector_is_active (iprot it2) C →
    False.
  Proof.
    intros Hl1 Hl2 HPC Hp1 Hp2 HpC Hp3.
    specialize (HH tg1 off). eapply every_child_ParentChildIn in HH.
    2: done. 2, 4: eapply Hwf. 2,4: eapply Hl1. 2: eapply Hl2. 2: done.
    assert (tg1 = itag it1) as -> by by eapply tree_lookup_correct_tag in Hl1.
    assert (tg2 = itag it2) as -> by by eapply tree_lookup_correct_tag in Hl2.
    eapply every_node_eqv_universal in HH.
    2: eapply tree_lookup_to_exists_node, Hl2.
    odestruct (HH eq_refl Hp2 Hp3). 1: done. congruence.
  Qed.

  Lemma disabled_in_practice_not_prot_init tr tg1 tg2 it off
    (Hwf : wf_tree tr)
    (HNC : no_active_cousins C tr)
    (HH : protected_parents_not_disabled C tr) :
    tree_lookup tr tg2 it →
    initialized (item_lookup it off) = PermInit →
    perm (item_lookup it off) ≠ Cell →
    protector_is_active (iprot it) C →
    disabled_in_practice C tr tg2 tg1 off →
    False.
  Proof.
    intros Hl1 Hini Hncell Hperm [it_witness incl H1 H2 H3].
    destruct (decide (perm (item_lookup it_witness off) = Disabled)) as [Hdis|Hnondis].
    + eapply parents_not_disabled_child_not_prot_init. 1: exact Hwf. 1: done. 4: exact Hdis. 4: exact Hini. 4: exact Hncell. 4: exact Hperm.
      1-2: done.
      rewrite /rel_dec in H1. destruct decide; done.
    + inversion H3 as [X1 X2 X3|lp X HH1 HH2 X2]; simplify_eq.
      { rewrite -X2 in Hnondis. done. }
      inversion HH1 as [|tgcs itcs X1 X2 H1' H2' H3' H4 H5 X3 X4]; simplify_eq.
      { rewrite -HH2 in Hnondis. done. }
      eapply HNC. 1: exact Hl1. 1: exact H2'. 3: by erewrite H4.
      2: right; split. 2: by left. 2: done.
      rewrite rel_dec_flip2 /=.
      rewrite /rel_dec in H1|-*.
      destruct decide as [HPC1|] in H1; last done. clear H1.
      rewrite decide_False; last first.
      { intros HPC2. rewrite /rel_dec in H1'.
        destruct decide in H1'; try done.
        rewrite decide_True // in H1'.
        eapply ParentChild_transitive. 1: exact HPC1. done. }
      rewrite decide_False //.
      intros HPC2.
      eapply cousins_have_disjoint_children. 4: exact H1'. 4: exact HPC1. 4: done.
      all: eapply Hwf. 1: eapply Hl1. 1: eapply H2. 1: eapply H2'.
  Qed.


  Lemma perm_eq_up_to_C_same_cell d tr1 tr2 tg off prot it1 it2
    (Hwf1 : wf_tree tr1)
    (Hwf2 : wf_tree tr2) :
    tree_lookup tr1 tg it1 →
    tree_lookup tr2 tg it2 →
    perm_eq_up_to_C C tr1 tr2 tg off prot d (item_lookup it1 off) (item_lookup it2 off) →
    perm (item_lookup it1 off) = Cell ↔ perm (item_lookup it2 off) = Cell.
  Proof.
    intros Hl1 Hl2 H. inversion H as [| | |p1 p2 HX1 HX2 HX3 HX4|X1 X2 X3 X4 X5 X6 X7| |p1 p2 ini Hr]; try done; simplify_eq.
    - inversion HX1; inversion HX2; simplify_eq; simpl; split; congruence.
    - destruct d; simpl in Hr; inversion Hr; simplify_eq; simpl.
      all: split; intros ?; done.
  Qed.

  Lemma perm_eq_up_to_C_same_protected_active d tr1 tr2 tg off prot it1 it2 ev1 ev2
    (Hwf1 : wf_tree tr1)
    (Hwf2 : wf_tree tr2)
    (ProtParentsNonDis1 : protected_parents_not_disabled C tr1)
    (ProtParentsNonDis2 : protected_parents_not_disabled C tr2)
    (HCS1 : no_active_cousins C tr1)
    (HCS2 : no_active_cousins C tr2)
    (Hiwf1 : item_wf it1 ev1 ev2)
    (Hiwf2 : item_wf it2 ev1 ev2) :
    tree_lookup tr1 tg it1 →
    tree_lookup tr2 tg it2 →
    prot = iprot it1 → prot = iprot it2 →
    protector_is_active prot C →
    perm (item_lookup it1 off) ≠ Cell →
    perm (item_lookup it2 off) ≠ Cell →
    perm_eq_up_to_C C tr1 tr2 tg off prot d (item_lookup it1 off) (item_lookup it2 off) →
    perm (item_lookup it1 off) = Active ↔ perm (item_lookup it2 off) = Active.
  Proof.
    intros Hl1 Hl2 Hiprot1 Hiprot2 Hprot HnC1 HnC2 H. inversion H as [| | |p1 p2 HX1 HX2 HX3 HX4|X1 X2 X3 X4 X5 X6 X7| |p1 p2 ini Hr]; try done; simplify_eq.
    - simpl; split; intros Hact; exfalso.
      + rewrite /item_lookup in HX3.
        destruct lookup eqn:Heq in HX3.
        2: { simpl in HX3. injection HX3 as ->.
             eapply item_default_perm_valid in Hact; done. }
        rewrite /= in HX3. subst.
        eapply item_perms_valid in Heq. 2: done.
        simpl in Heq. by ospecialize (Heq _).
      + rewrite /item_lookup in HX4.
        destruct lookup eqn:Heq in HX4.
        2: { simpl in HX3. injection HX4 as ->.
             eapply item_default_perm_valid in Hact; done. }
        rewrite /= in HX4. subst.
        eapply item_perms_valid in Heq. 2: done.
        simpl in Heq. by ospecialize (Heq _).
    - split; intros XX; eapply item_wf_item_lookup_active in XX; try done.
      all: exfalso; destruct d;
           (eapply disabled_in_practice_not_prot_init in X4; [try done..| |by congruence]).
      all: congruence.
    - destruct d; simpl in Hr; inversion Hr; simplify_eq; simpl.
      all: split; intros ?; done.
  Qed.

  Lemma tree_equals_protected_initialized_one d tr1 tr2 cid ev1 ev2
    (AllUnique1 : forall tg, tree_contains tg tr1 -> tree_unique tg tr1)
    (AllUnique2 : forall tg, tree_contains tg tr2 -> tree_unique tg tr2)
    (PND1 : protected_parents_not_disabled C tr1)
    (PND2 : protected_parents_not_disabled C tr2)
    (HCS1 : no_active_cousins C tr1)
    (HCS2 : no_active_cousins C tr2)
    (Hiwf1 : tree_items_compat_nexts tr1 ev1 ev2)
    (Hiwf2 : tree_items_compat_nexts tr2 ev1 ev2) :
    cid ∈ C →
    tree_equal C d tr1 tr2 →
    tree_get_all_protected_tags_initialized_locs cid tr1 ⊆
    tree_get_all_protected_tags_initialized_locs cid tr2.
  Proof.
    intros Hcid Heq. intros (tg&lst).
    intros (it&Hlu&Hprot&Hinit)%tree_all_protected_initialized_elem_of; try done.
    all: eapply tree_all_protected_initialized_elem_of; first done.
    edestruct (tree_equal_transfer_lookup_1 C Heq Hlu) as (it'&Hit'&Heqit').
    exists it'. split; first done.
    split; first by erewrite <- item_eq_up_to_C_same_iprot.
    intros z. specialize (Hinit z). destruct (Heqit' z) as (Hproteq&Heqlu).
    erewrite <- perm_eq_up_to_C_same_init. 2: done.
    opose proof (perm_eq_up_to_C_same_cell _ _ _ _ _ _ _ _ _ _ _ _ _) as HH.
    5: exact Heqlu. 1-4: done. setoid_rewrite <- HH. 
    destruct (decide (perm (item_lookup it z) = Cell)) as [Hcell|Hncell].
    { rewrite Hcell. rewrite Hcell in Hinit. intros ?. rewrite Hinit. tauto. }
    setoid_rewrite <- perm_eq_up_to_C_same_protected_active. 17: eassumption. 2-7: try done.
    1,4,5,6,7: done.
    + eapply every_node_eqv_universal in Hiwf1. 2: eapply tree_lookup_to_exists_node, Hlu.
      exact Hiwf1.
    + eapply every_node_eqv_universal in Hiwf2. 2: eapply tree_lookup_to_exists_node, Hit'.
      exact Hiwf2.
    + by eexists cid.
    + done.
    + by rewrite -HH.
  Qed.

  Lemma tree_equals_protected_initialized d tr1 tr2 cid ev1 ev2
    (AllUnique1 : forall tg, tree_contains tg tr1 -> tree_unique tg tr1)
    (AllUnique2 : forall tg, tree_contains tg tr2 -> tree_unique tg tr2)
    (PND1 : protected_parents_not_disabled C tr1)
    (PND2 : protected_parents_not_disabled C tr2)
    (HCS1 : no_active_cousins C tr1)
    (HCS2 : no_active_cousins C tr2)
    (Hiwf1 : tree_items_compat_nexts tr1 ev1 ev2)
    (Hiwf2 : tree_items_compat_nexts tr2 ev1 ev2) :
    cid ∈ C →
    tree_equal C d tr1 tr2 →
    tree_get_all_protected_tags_initialized_locs cid tr1 =
    tree_get_all_protected_tags_initialized_locs cid tr2.
  Proof.
    intros Hcid Heq. eapply gset_leibniz. intros (tg&lst).
    split.
    - intros H. eapply tree_equals_protected_initialized_one; last exact H. all: done.
    - intros H. eapply tree_equals_protected_initialized_one; last exact H. 1-9: done.
      eapply tree_equal_sym. done.
  Qed.

  Lemma tree_equals_access_many_helper_2 tg (L : gmap Z _) tr1 tr1' tr2
    (Hwf1 : wf_tree tr1)
    (Hwf2 : wf_tree tr2) 
    (PMI : parents_more_init tr2)
    (ProtParentsNonDis2 : protected_parents_not_disabled C tr2) :
    parents_more_active tr1 → parents_more_active tr2 →
    no_active_cousins C tr1 → no_active_cousins C tr2 →
    tree_equal C Forwards tr1 tr2 →
    tree_unique tg tr1 →
    let fn := (λ tr, map_fold (λ l acc tr2, tr2 ≫= memory_access_nonchildren_only acc C tg (l, 1%nat)) (Some tr) L) in
    fn tr1 = Some tr1' →
    ∃ tr2', fn tr2 = Some tr2' ∧  tree_equal C Forwards tr1' tr2'.
  Proof.
    intros X1 X2 X3 X4 Heq Hunq''. simpl.
    map_fold_weak_ind L as off acc E Hnone Hfoo IH in tr1' Hunq''.
    { simpl. intros [= ->]; by eexists. }
    simpl. intros (tr1'''&H1&H2)%bind_Some.
    specialize (IH _ Hunq'' H1) as (tr2'''&Htr2&HHtr2p). rewrite Hfoo Htr2 /=.
    assert (tree_unique tg tr1''') as Hunq'''.
    { rewrite /tree_unique. erewrite <- tree_access_many_helper_2. 1: exact Hunq''. exact H1. }
    assert (wf_tree tr1''') as Hwf1'''.
    { eapply preserve_tag_count_wf. 1: eapply tree_access_many_helper_2. 1: exact Hwf1. 1: apply H1. }
    assert (wf_tree tr2''') as Hwf2'''.
    { eapply preserve_tag_count_wf. 1: eapply tree_access_many_helper_2. 1: exact Hwf2. 1: apply Htr2. } 
    opose proof (tree_equal_allows_more_access_nonchildren_only _ _ _ _ _ _ HHtr2p Hunq''' _) as (trr&Htrr).
    1, 2: by apply wf_tree_tree_unique. 3: done.
    1: { eapply tree_access_many_protected_not_disabled_helper_2. 5: exact Htr2. 1,3,4: done. destruct Heq as (Hx&_). by eapply Hx, unique_exists. }
    1: { eapply tree_access_many_more_init_helper_2. 4: exact Htr2. 1,3: done. destruct Heq as (Hx&_). by eapply Hx, unique_exists. }
    1: by eapply mk_is_Some.
    exists trr; split; first done.
    eapply tree_equal_preserved_by_memory_access_nonchildren_only.
    9-10: done. 7: done. 7: by eapply unique_exists.
    1-2: by eapply wf_tree_tree_unique.
    1,3: eapply tree_access_many_more_active_helper_2; last done; first done; last done.
    2: eapply Heq. 1-2: by eapply unique_exists.
    all: eapply tree_access_many_no_cousins_helper_2; last done; first done; last done.
    2: eapply Heq. 1-2: by eapply unique_exists.
  Qed.

  Lemma tree_equals_access_many_helper_1 (E : list (tag * gmap Z _)) tr1 tr1' tr2
    (Hwf1 : wf_tree tr1)
    (Hwf2 : wf_tree tr2)
    (PMI2 : parents_more_init tr2)
    (ProtParentsNonDis : protected_parents_not_disabled C tr2) :
    parents_more_active tr1 → parents_more_active tr2 →
    no_active_cousins C tr1 → no_active_cousins C tr2 →
    tree_equal C Forwards tr1 tr2 →
    (∀ tg L, (tg, L) ∈ E → tree_unique tg tr1)→
    let fn := (λ tr, foldr (λ '(tg, L) tr, tr ≫= λ tr1, map_fold (λ l acc tr2, tr2 ≫= memory_access_nonchildren_only acc C tg (l, 1%nat)) (Some tr1) L) (Some tr) E) in
    fn tr1 = Some tr1' →
    ∃ tr2', fn tr2 = Some tr2' ∧ tree_equal C Forwards tr1' tr2'.
  Proof.
    intros X1 X2 X3 X4 Heq Hunq.
    induction E as [|(tg&init_locs) S IH] in tr1',Hunq|-*.
    { simpl. intros [= ->]; by eexists. }
    simpl. intros (tr1''&H1&H2)%bind_Some.
    opose proof (IH _ _ H1) as (tr2''&Htr2&HHtr2); clear IH.
    { intros ???. eapply Hunq. by right. }
    rewrite Htr2 /=. pose proof Hunq as Hunq2.
    ospecialize (Hunq tg init_locs _). 1: by left. revert H2.
    eapply tree_equals_access_many_helper_2.
    { eapply preserve_tag_count_wf. 1: eapply tree_access_many_helper_1. 1: exact Hwf1. 1: apply H1. }
    { eapply preserve_tag_count_wf. 1: eapply tree_access_many_helper_1. 1: exact Hwf2. 1: exact Htr2. }
    { eapply tree_access_many_more_init_helper_1. 4: exact Htr2. 1,3: done. intros ???. destruct Heq as (HH&_); eapply HH, unique_exists, Hunq2. by right. }
    { eapply tree_access_many_protected_not_disabled_helper_1. 5: exact Htr2. 1,3,4: done. intros ???. destruct Heq as (HH&_); eapply HH, unique_exists, Hunq2. by right. }
    1,2: eapply tree_access_many_more_active_helper_1; last done; first done; last done; intros ???.
    2: eapply Heq. 1-2: eapply unique_exists, Hunq2; by right.
    1,2: eapply tree_access_many_no_cousins_helper_1; last done; first done; last done; intros ???.
    2: eapply Heq. 1-2: eapply unique_exists, Hunq2; by right.
    { done. }
    { rewrite /tree_unique. erewrite <- tree_access_many_helper_1. 1: exact Hunq. exact H1. }
  Qed.

  Lemma tree_equals_access_all_protected_initialized' tr1 tr1' tr2 cid ev1 ev2
    (Hwf1 : wf_tree tr1)
    (Hwf2 : wf_tree tr2)
    (PMI : parents_more_init tr2)
    (PMA1 : parents_more_active tr1)
    (PMA2 : parents_more_active tr2)
    (ProtParentsNonDis1 : protected_parents_not_disabled C tr1)
    (ProtParentsNonDis2 : protected_parents_not_disabled C tr2)
    (NA1 : no_active_cousins C tr1)
    (NA2 : no_active_cousins C tr2)
    (CC1 : tree_items_compat_nexts tr1 ev1 ev2)
    (CC2 : tree_items_compat_nexts tr2 ev1 ev2) :
    cid ∈ C →
    tree_equal C Forwards tr1 tr2 →
    tree_access_all_protected_initialized C cid tr1 = Some tr1' →
    ∃ tr2', tree_access_all_protected_initialized C cid tr2 = Some tr2' ∧
      tree_equal C Forwards tr1' tr2'.
  Proof.
    intros Hc Heq.
    rewrite /tree_access_all_protected_initialized.
    erewrite <- (tree_equals_protected_initialized Forwards tr1 tr2); last done.
    2-3: by eapply wf_tree_tree_unique. 2-8: done.
    eapply tree_equals_access_many_helper_1. 1-9: done.
    {intros tg E. setoid_rewrite elem_of_elements.
      intros (it&Hit&_)%tree_all_protected_initialized_elem_of. all: eapply wf_tree_tree_unique; try apply Hwf1.
      by eapply lookup_implies_contains. }
  Qed.

  Lemma trees_equal_access_all_protected_initialized trs1 trs1' trs2 cid ev1 ev2
    (Hwf1 : wf_trees trs1)
    (Hwf2 : wf_trees trs2)
    (PMI : each_tree_parents_more_init trs2)
    (PMA1 : each_tree_parents_more_active trs1)
    (PMA2 : each_tree_parents_more_active trs2)
    (ProtParentsNonDis1 : each_tree_protected_parents_not_disabled C trs1)
    (ProtParentsNonDis2 : each_tree_protected_parents_not_disabled C trs2)
    (NA1 : each_tree_no_active_cousins C trs1)
    (NA2 : each_tree_no_active_cousins C trs2)
    (CC1 : trees_compat_nexts trs1 ev1 ev2)
    (CC2 : trees_compat_nexts trs2 ev1 ev2) :
    cid ∈ C →
    trees_equal C Forwards trs1 trs2 →
    trees_access_all_protected_initialized C cid trs1 = Some trs1' →
    ∃ trs2', trees_access_all_protected_initialized C cid trs2 = Some trs2' ∧
      trees_equal C Forwards trs1' trs2'.
  Proof.
    intros Hc Heq Htrapi.
    epose proof (trees_access_all_protected_initialized_pointwise_1 _ _ _ _ Htrapi) as Htrapi1.
    odestruct (trees_access_all_protected_initialized_pointwise_2 _ trs2) as (trs2'&Htrs2').
    { intros k. destruct (Htrapi1 k) as (HH'&_). intros tr2 Htr2.
      specialize (Heq k). rewrite Htr2 in Heq. inversion Heq as [tr1 x1 Heqtr Htr1 e|]. subst x1.
      destruct (HH' tr1) as (tr1'&Htr1'&HHtr1'); first done.
      edestruct tree_equals_access_all_protected_initialized' as (tr2'&Htr2'&Heq').
      13: exact Heqtr. 13: exact HHtr1'. 1: by eapply Hwf1. 1: by eapply Hwf2.
      11: by eexists. 1: by eapply PMI. 1: by eapply PMA1. 1: by eapply PMA2. 1: by eapply ProtParentsNonDis1. 1: by eapply ProtParentsNonDis2.
      1: by eapply NA1. 1: by eapply NA2. 1: by eapply CC1. 1: by eapply CC2. done. }
    eexists; split; first done.
    intros k. specialize (Heq k).
    epose proof (trees_access_all_protected_initialized_pointwise_1 _ _ _ _ Htrs2' k) as (Htrapi2A&Htrapi2B).
    specialize (Htrapi1 k) as (Htrapi1A&Htrapi1B).
    inversion Heq as [tr1 tr2 Heqtr Htr1 Htr2|HNone1 HNone2]; last first.
    - rewrite Htrapi1B // Htrapi2B //. econstructor.
    - symmetry in Htr1,Htr2.
      destruct (Htrapi1A _ Htr1) as (tr1'&Htr1'&Hrapi1'). destruct (Htrapi2A _ Htr2) as (tr2'&Htr2'&Hrapi2').
      rewrite Htr1' Htr2'. econstructor.
      edestruct tree_equals_access_all_protected_initialized' as (tr2''&Htr2'u&Htr2'eq).
      14: exact Hrapi1'. 13: exact Heqtr. 1: by eapply Hwf1. 1: by eapply Hwf2. 1: by eapply PMI. 1: by eapply PMA1. 1: by eapply PMA2. 1: by eapply ProtParentsNonDis1. 1: by eapply ProtParentsNonDis2.
      1: by eapply NA1. 1: by eapply NA2. 1: by eapply CC1. 1: by eapply CC2. 1: done.
      rewrite Hrapi2' in Htr2'u. injection Htr2'u as <-. done.
  Qed.


  Lemma disabled_tag_at_access_many_helper_2 (L : gmap Z _) tr1 tr1' tg acc_tg loc :
    disabled_tag_at C tr1 tg loc →
    tree_contains acc_tg tr1 →
    wf_tree tr1 →
    let fn := (λ tr, map_fold (λ l acc tr2, tr2 ≫= memory_access_nonchildren_only acc C acc_tg (l, 1%nat)) (Some tr) L) in
    fn tr1 = Some tr1' →
    disabled_tag_at C tr1' tg loc.
  Proof.
    simpl. map_fold_weak_ind L as off acc E Hnone Hfoo IH in tr1'.
    1: intros ????; by simplify_eq.
    intros Hdis Hcont Hwf (tr1'''&H1&H2)%bind_Some.
    assert (wf_tree tr1''') as Hwf1'''.
    { eapply preserve_tag_count_wf. 1: eapply tree_access_many_helper_2. 1: exact Hwf. 1: apply H1. }
    assert (tree_contains acc_tg tr1''') as Hcont'''.
    { eapply preserve_tag_count_contains. 1: eapply tree_access_many_helper_2. 1: done. apply H1. }
    eapply disabled_tag_at_tree_apply_access_irreversible. 4: exact H2. 2,3: done.
    eapply IH. 1: done. 1-2: done. apply H1.
  Qed.

  Lemma disabled_tag_at_access_many_helper_1 (E : list (tag * gmap Z _)) tr1 tr1' tg loc :
    disabled_tag_at C tr1 tg loc →
    wf_tree tr1 →
    (∀ tg L, (tg, L) ∈ E → tree_contains tg tr1)→
    let fn := (λ tr, foldr (λ '(tg, L) tr, tr ≫= λ tr1, map_fold (λ l acc tr2, tr2 ≫= memory_access_nonchildren_only acc C tg (l, 1%nat)) (Some tr1) L) (Some tr) E) in
    fn tr1 = Some tr1' →
    disabled_tag_at C tr1' tg loc.
  Proof.
    simpl.
    induction E as [|(acc_tg&init_locs) S IH] in tr1'|-*.
    1: simpl; intros ????; by simplify_eq.
    simpl. intros Hdis Hwf Hcont (tr1'''&H1&H2)%bind_Some.
    assert (wf_tree tr1''') as Hwf1'''.
    { eapply preserve_tag_count_wf. 1: eapply tree_access_many_helper_1. 1: exact Hwf. 1: apply H1. }
    assert (tree_contains acc_tg tr1''') as Hcont'''.
    { eapply preserve_tag_count_contains. 1: eapply tree_access_many_helper_1. 1: eapply Hcont; by left. apply H1. }
    eapply disabled_tag_at_access_many_helper_2. 4: exact H2. 2,3: done.
    eapply IH. 1: done. 1: done. 2: apply H1.
    intros ???; eapply Hcont; by right.
  Qed.

  Lemma disabled_tag_at_access_all_protected_initialized cid tr1 tr1' tg loc :
    disabled_tag_at C tr1 tg loc →
    wf_tree tr1 →
    tree_access_all_protected_initialized C cid tr1 = Some tr1' →
    disabled_tag_at C tr1' tg loc.
  Proof.
    intros H1 H2. eapply disabled_tag_at_access_many_helper_1.
    1-2: done.
    intros tg' E. setoid_rewrite elem_of_elements.
    intros (it&Hit&_)%tree_all_protected_initialized_elem_of. 2: done.
    apply Hit.
  Qed.

  Lemma disabled_tag_access_all_protected_initialized cid nxtp trs1 trs1' tg loc :
    disabled_tag C trs1 nxtp tg loc →
    wf_trees trs1 →
    trees_access_all_protected_initialized C cid trs1 = Some trs1' →
    disabled_tag C trs1' nxtp tg loc.
  Proof.
    intros Dis Wf Acc.
    pose proof (trees_access_all_protected_initialized_pointwise_1 _ _ _ _ Acc loc.1) as (H1&H2).
    destruct Dis as (HH&Dis).
    split; first done.
    destruct (trs1 !! loc.1) as [tr|] eqn:Htr.
    2: by rewrite H2.
    specialize (H1 _ eq_refl) as (tr'&Htr'&HAcc). rewrite Htr'.
    destruct Dis as [Dis|Hne].
    - left. eapply disabled_tag_at_access_all_protected_initialized. 1: exact Dis. 2: done. by eapply Wf.
    - right. intros Hc. apply Hne. eapply preserve_tag_count_contains_2.
      3: exact HAcc. 2: done. by eapply tree_access_all_protected_initialized_tag_count.
  Qed.



End utils.