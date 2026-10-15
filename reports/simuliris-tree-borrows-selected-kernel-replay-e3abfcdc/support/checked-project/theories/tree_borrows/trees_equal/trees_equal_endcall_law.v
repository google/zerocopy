From iris.proofmode Require Export proofmode.
From iris.base_logic.lib Require Import ghost_map.
From simuliris.base_logic Require Export gen_sim_prog.
From simuliris.simulation Require Export slsls.
From simuliris.simulation Require Import lifting.
From simuliris.tree_borrows Require Import tkmap_view.
From simuliris.tree_borrows Require Export defs class_instances.
From simuliris.tree_borrows Require Import steps_progress steps_inv.
From simuliris.tree_borrows Require Import tree_access_laws logical_state inv_accessors.
From simuliris.tree_borrows.trees_equal Require Import trees_equal_base random_lemmas.



Definition is_pseudo_conflicted_by_in' C (tr : tree item) (tg tg_cous : tag) (it : item) (L : gmap Z access_kind) acc : Prop := 
  tree_lookup tr tg it ∧
  protector_is_active it.(iprot) C ∧
  rel_dec tr tg tg_cous = Foreign Cousin ∧
  ∃ it_cous l,
    l ∈ dom L ∧
    tree_lookup tr tg_cous it_cous ∧
    (item_lookup it l).(perm) = Reserved acc.

Definition is_pseudo_conflicted_by_in (C : call_id_set) (tr : tree item) (tg : tag) (it : item) (S : gset (tag * gmap Z access_kind)) acc : Prop := 
  ∃ tg_cous L,
    (tg_cous, L) ∈ S ∧
    is_pseudo_conflicted_by_in' C tr tg tg_cous it L acc.


Definition is_pseudo_disabled_by_in' C (tr : tree item) (tg tg_cous : tag) (it : item) (L : gmap Z access_kind) lp : Prop := 
  tree_lookup tr tg it ∧
  rel_dec tr tg tg_cous = Foreign Cousin ∧
  ∃ it_cous l,
    L !! l = Some AccessWrite ∧
    tree_lookup tr tg_cous it_cous ∧
    protector_is_active it_cous.(iprot) C ∧
    item_lookup it_cous l = mkPerm PermInit Active ∧
    item_lookup it l = mkPerm PermLazy lp ∧
    lp ≠ ReservedIM ∧
    lp ≠ Cell.

Definition is_pseudo_disabled_by_in (C : call_id_set) (tr : tree item) (tg : tag) (it : item) (S : gset (tag * gmap Z access_kind)) lp : Prop := 
  ∃ tg_cous L,
    (tg_cous, L) ∈ S ∧
    is_pseudo_disabled_by_in' C tr tg tg_cous it L lp.


Lemma tree_access_many_pseudo_confl_helper_2_pers C tg_acc (L : gmap Z _) tr1 trL S
  (Hwf1 : wf_tree tr1) :
  tree_unique tg_acc tr1 →
  let fn := (λ L tr, map_fold (λ l v tr2, tr2 ≫= memory_access_nonchildren_only v C tg_acc (l, 1%nat)) (Some tr) L) in
  fn L tr1 = Some trL →
  (∀ tg' it acc, is_pseudo_conflicted_by_in C tr1 tg' it S acc → acc = ResConflicted) →
  (∀ tg' it acc, is_pseudo_conflicted_by_in C trL tg' it S acc → acc = ResConflicted).
Proof.
  intros Hunq fn Hih H. revert Hih. subst fn. simpl.
  map_fold_weak_ind L as off v L HH1 HH2 IH in trL.
  1: by intros [= ->]. simpl.
  intros (tr2&Hoff&HL)%bind_Some.
  specialize (IH _ Hoff).
  intros tg' it acc (tg_cs&SL&HS&Hlu&Hisprot&Hreldec&it_cous&l&HlL&Hlucs&Hres).
  assert (tree_unique tg_acc tr2) as Hunq2.
  { rewrite /tree_unique. erewrite <- tree_access_many_helper_2. 1: exact Hunq. exact Hoff. }
  assert (wf_tree tr2) as Hwf2.
  { eapply preserve_tag_count_wf. 1: eapply tree_access_many_helper_2. 1: exact Hwf1. 1: apply Hoff. }
  destruct (decide (l = off)) as [->|Hne].
  - odestruct tree_access_lookup_general_rev as (it'&H1&H2&H3&H4).
    1: exact HL. 1: done. 2: exact Hlu. 1: split; first reflexivity; lia.
    odestruct tree_access_lookup_general_rev as (itcs'&H1cs&H2cs&H3cs&H4cs).
    1: exact HL. 1: done. 2: exact Hlucs. 1: split; first reflexivity; lia.
    eapply apply_access_perm_access_reserved_backwards in H4 as HHres.
    2: done. destruct HHres as (acto & Hacto).
    enough (acto = ResConflicted).
    { subst acto.
      eapply apply_access_perm_access_conflicted in H4 as HHres. 2: done. 2: exact Hres. congruence. }
    eapply IH.
    eexists tg_cs, SL. split; first done.
    split; first eapply H1.
    split; first by rewrite H3. split.
    { erewrite access_same_rel_dec; first done. apply HL. }
    exists itcs', off. do 2 (split; first done). done.
  - odestruct (tree_access_lookup_outside_rev l) as (it'&H1&H2&H3&H4).
    1: exact HL. 1: done. 2: exact Hlu. 1: lia.
    odestruct (tree_access_lookup_outside_rev l) as (itcs'&H1cs&H2cs&H3cs&H4cs).
    1: exact HL. 1: done. 2: exact Hlucs. 1: lia.
    rewrite -H4 in Hres. eapply IH.
    eexists tg_cs, SL. split; first done.
    split; first eapply H1.
    split; first by rewrite H3. split.
    { erewrite access_same_rel_dec; first done. apply HL. }
    exists itcs', l. do 2 (split; first done). done.
Qed.

Lemma tree_access_many_pseudo_dis_helper_2_pers C tg_acc (L : gmap Z _) tr1 trL S nxtp nxtc
  (Hwf1 : wf_tree tr1) :
  tree_unique tg_acc tr1 →
  tree_items_compat_nexts tr1 nxtp nxtc →
  let fn := (λ L tr, map_fold (λ l v tr2, tr2 ≫= memory_access_nonchildren_only v C tg_acc (l, 1%nat)) (Some tr) L) in
  fn L tr1 = Some trL →
  (∀ tg' it acc, is_pseudo_disabled_by_in C tr1 tg' it S acc → acc = Disabled) →
  (∀ tg' it acc, is_pseudo_disabled_by_in C trL tg' it S acc → acc = Disabled).
Proof.
  intros Hunq Hcompat fn Hih H. revert Hih. subst fn. simpl.
  map_fold_weak_ind L as off v L HH1 HH2 IH in trL.
  1: by intros [= ->]. simpl.
  intros (tr2&Hoff&HL)%bind_Some.
  specialize (IH _ Hoff).
  intros tg' it acc (tg_cs&SL&HS&Hlu&Hreldec&it_cous&l&HlL&Hlucs&Hisprotcs&Hppcs&Hres&Hlp&Hcell).
  assert (tree_unique tg_acc tr2) as Hunq2.
  { rewrite /tree_unique. erewrite <- tree_access_many_helper_2. 1: exact Hunq. exact Hoff. }
  assert (wf_tree tr2) as Hwf2.
  { eapply preserve_tag_count_wf. 1: eapply tree_access_many_helper_2. 1: exact Hwf1. 1: apply Hoff. }
  assert (tree_items_compat_nexts tr2 nxtp nxtc) as Hcompat2.
  { eapply tree_access_many_compat_nexts_helper_2. 2: done. done. }
  destruct (decide (l = off)) as [->|Hne].
  - odestruct tree_access_lookup_general_rev as (it'&H1&H2&H3&H4).
    1: exact HL. 1: done. 2: exact Hlu. 1: split; first reflexivity; lia.
    odestruct tree_access_lookup_general_rev as (itcs'&H1cs&H2cs&H3cs&H4cs).
    1: exact HL. 1: done. 2: exact Hlucs. 1: split; first reflexivity; lia.
    rewrite bool_decide_true // Hppcs in H4cs.
    assert (item_lookup itcs' off ≠ mkPerm PermLazy Active) as Hnolazyact.
    { intros Hff. eapply every_node_eqv_universal in Hcompat2 as HH.
      2: eapply tree_lookup_to_exists_node, H1cs.
      rewrite /item_lookup in Hff.
      destruct lookup as [l|] eqn:Hffff in Hff.
      { eapply item_perms_valid in Hffff. 2: done.
        simpl in Hff. subst l. 
        ospecialize (Hffff _). 1: done. done. }
      { eapply item_default_perm_valid. 1: done. simpl in Hff. by injection Hff. } }
    assert ((ParentChildIn tg_cs tg_acc tr2 ∧ v = AccessWrite) ∨ item_lookup itcs' off = {| initialized := PermInit; perm := Active |}) as HPC.
    { edestruct maybe_non_children_only_effect_or_nop_strong as [(Heff&HH)|(Heff&HH)]; erewrite Heff in H4cs; clear Heff.
      2: right; by injection H4cs.
      destruct HH as [|HH]; first done.
      rewrite /rel_dec in HH.
      rewrite /rel_dec /apply_access_perm /apply_access_perm_inner in H4cs.
      destruct v, (decide (ParentChildIn tg_cs tg_acc tr2)), (item_lookup itcs' off) as [[][|[]| | | |]] eqn:HHH.
      all: destruct (initialized (item_lookup itcs' off)) eqn:Heqini.
      all: rewrite /= in H4cs.
      all: try discriminate H4cs. 
      all: try (right; reflexivity).
      all: left; split; first eassumption. all: done. }
    assert (protector_is_active (iprot it) C → perm (item_lookup it' off) = ReservedIM → False) as HnoPRI.
    { rewrite -H3. intros (xx&Hxx&HHxx). eapply every_node_eqv_universal in Hcompat2 as HH.
      2: eapply tree_lookup_to_exists_node, H1. eapply item_perms_reserved_im_protected. 1: done.
      destruct (iprot it'); done. }
    destruct HPC as [(HPC&->)|Hact].
    + assert (rel_dec tr2 tg_acc tg' = Foreign Cousin) as Hrr.
      { erewrite <- access_same_rel_dec in Hreldec; last eassumption.
        rewrite /rel_dec. rewrite decide_False.
        2: { intros Hfoo. eapply cousins_have_disjoint_children.
             4: exact Hreldec.
             4: exact Hfoo. 4: done. all: try done.
             all: eapply Hwf2. 1: eapply H1. 1: eapply H1cs. }
        rewrite decide_False //.
        intros HH.
        rewrite /rel_dec in Hreldec.
        do 2 destruct decide in Hreldec; try done.
        opose proof (ParentChild_transitive _ _ _ _ HPC HH) as HHPC.
        tauto. }
      rewrite Hrr in H4.
      rewrite Hres maybe_non_children_only_no_effect // in H4.
      rewrite /apply_access_perm /apply_access_perm_inner in H4.
      destruct (item_lookup it' off) as [[][|[]| | | |]] eqn:Hppplu, (bool_decide (protector_is_active (iprot it) C)) eqn:Hprot.
      all: simpl in H4.
      all: try discriminate H4.
      all: injection H4 as <-. all: try reflexivity.
      all: exfalso; by eapply Hlp.
    + destruct (item_lookup it' off) as [[] pp] eqn:Heq.
      { eapply apply_access_perm_initialized in H4. 2: done. rewrite Hres in H4. done. }
      assert (pp = Disabled) as Hpp.
      { eapply IH. eexists _, _. split; first exact HS.
        split. 1: exact H1.
        split. 1: erewrite access_same_rel_dec; last done; done.
        exists itcs', off.
        split; first done.
        split; first done.
        split. 1: by rewrite H3cs.
        split; first done. split; first done.
        split.
        all: intros ->.
        all: edestruct maybe_non_children_only_effect_or_nop_strong as [(Heff&HH)|(Heff&HH)]; erewrite Heff in H4; clear Heff.
        2,4: injection H4 as H4; rewrite -H4 in Hres; injection Hres as <-; by eapply Hlp.
        all: rewrite /apply_access_perm /apply_access_perm_inner in H4.
        all: destruct v, (rel_dec tr2 tg_acc tg'), (bool_decide (protector_is_active (iprot it) C)) eqn:Hppr; simpl in H4.
        all: try discriminate H4.
        all: injection H4 as H4. all: rewrite -H4 in Hres.
        all: injection Hres as Hres. all: subst acc. Unshelve.
        all: try by eapply (Hcell).
        all: try by eapply (Hlp ResConflicted).
        all: try by eapply (Hlp ResActivable).
        all: eapply HnoPRI; first by eapply bool_decide_eq_true.
        all: reflexivity. }
      subst pp. eapply apply_access_perm_access_remains_disabled in H4. 2: done.
      rewrite Hres /= in H4. done.
  - odestruct (tree_access_lookup_outside_rev l) as (it'&H1&H2&H3&H4).
    1: exact HL. 1: done. 2: exact Hlu. 1: lia.
    odestruct (tree_access_lookup_outside_rev l) as (itcs'&H1cs&H2cs&H3cs&H4cs).
    1: exact HL. 1: done. 2: exact Hlucs. 1: lia.
    rewrite -H4 in Hres. eapply IH.
    eexists tg_cs, SL. split; first done.
    split; first eapply H1. split.
    { erewrite access_same_rel_dec; first done. apply HL. }
    exists itcs', l. do 2 (split; first done). rewrite H4cs Hres H3cs. done.
Qed.


Lemma tree_access_many_pseudo_confl_helper_2_news C tg_acc (L : gmap Z access_kind) tr1 trL
  (Hwf1 : wf_tree tr1) :
  tree_unique tg_acc tr1 →
  let fn := (λ L tr, map_fold (λ l v tr2, tr2 ≫= memory_access_nonchildren_only v C tg_acc (l, 1%nat)) (Some tr) L) in
  fn L tr1 = Some trL →
  (∀ tg' it acc, is_pseudo_conflicted_by_in' C trL tg' tg_acc it L acc → acc = ResConflicted).
Proof.
  intros Hunq fn.
  subst fn. simpl.
  map_fold_weak_ind L as off v L HH1 HH2 IH in trL.
  { simpl. intros [= ->] tg it acc (?&?&?&?&?&?&HH&_). set_solver. }
  intros (tr2&Hoff&HL)%bind_Some.
  specialize (IH _ Hoff).
  intros tg' it acc (Hlu&Hisprot&Hreldec&it_cous&l&HlL&Hlucs&Hres).
  assert (tree_unique tg_acc tr2) as Hunq2.
  { rewrite /tree_unique. erewrite <- tree_access_many_helper_2. 1: exact Hunq. exact Hoff. }
  assert (wf_tree tr2) as Hwf2.
  { eapply preserve_tag_count_wf. 1: eapply tree_access_many_helper_2. 1: exact Hwf1. 1: apply Hoff. }
  destruct (decide (l = off)) as [->|Hne].
  - odestruct tree_access_lookup_general_rev as (it'&H1&H2&H3&H4).
    1: exact HL. 1: done. 2: exact Hlu. 1: split; first reflexivity; lia.
    erewrite <- access_same_rel_dec in Hreldec; last eapply HL.
    rewrite rel_dec_flip2 Hreldec /= in H4.
    odestruct tree_access_lookup_general_rev as (itcs'&H1cs&H2cs&H3cs&H4cs).
    1: exact HL. 1: done. 2: exact Hlucs. 1: split; first reflexivity; lia.
    eapply (apply_access_perm_access_reserved_backwards false) in H4 as HHres.
    2: done. destruct HHres as (acto & Hacto).
    rewrite bool_decide_true in H4; last done.
    rewrite /apply_access_perm /apply_access_perm_inner /= Hacto /= in H4. repeat (case_match; try by simplify_eq; try simpl in H4).
    all: simpl in H4; simplify_eq; rewrite <- H4 in Hres; simpl in *; simplify_eq; done.
  - odestruct (tree_access_lookup_outside_rev l) as (it'&H1&H2&H3&H4).
    1: exact HL. 1: done. 2: exact Hlu. 1: lia.
    odestruct (tree_access_lookup_outside_rev l) as (itcs'&H1cs&H2cs&H3cs&H4cs).
    1: exact HL. 1: done. 2: exact Hlucs. 1: lia.
    rewrite -H4 in Hres. eapply IH.
    split; first exact H1.
    split; first by rewrite H3.
    split.
    { erewrite access_same_rel_dec; first done. apply HL. }
    exists itcs', l. split_and!; try done.
    rewrite dom_insert_L in HlL. set_solver.
Qed.

Lemma tree_access_many_pseudo_dis_helper_2_news C tg_acc (L : gmap Z access_kind) tr1 trL
  (Hwf1 : wf_tree tr1) :
  tree_unique tg_acc tr1 →
  let fn := (λ L tr, map_fold (λ l v tr2, tr2 ≫= memory_access_nonchildren_only v C tg_acc (l, 1%nat)) (Some tr) L) in
  fn L tr1 = Some trL →
  (∀ tg' it acc, is_pseudo_disabled_by_in' C trL tg' tg_acc it L acc → acc = Disabled).
Proof.
  intros Hunq fn.
  subst fn. simpl.
  map_fold_weak_ind L as off v L HH1 HH2 IH in trL.
  { simpl. intros [= ->] tg it acc (?&?&?&?&?&?&HH&_). set_solver. }
  intros (tr2&Hoff&HL)%bind_Some.
  specialize (IH _ Hoff).
  intros tg' it acc (Hlu&Hreldec&it_cous&l&HlL&Hlucs&Hisprot&Hiniact&Hres&Hnores&Hnocell).
  assert (tree_unique tg_acc tr2) as Hunq2.
  { rewrite /tree_unique. erewrite <- tree_access_many_helper_2. 1: exact Hunq. exact Hoff. }
  assert (wf_tree tr2) as Hwf2.
  { eapply preserve_tag_count_wf. 1: eapply tree_access_many_helper_2. 1: exact Hwf1. 1: apply Hoff. }
  destruct (decide (l = off)) as [->|Hne].
  - odestruct tree_access_lookup_general_rev as (it'&H1&H2&H3&H4).
    1: exact HL. 1: done. 2: exact Hlu. 1: split; first reflexivity; lia.
    odestruct tree_access_lookup_general_rev as (itcs'&H1cs&H2cs&H3cs&H4cs).
    1: exact HL. 1: done. 2: exact Hlucs. 1: split; first reflexivity; lia.
    rewrite rel_dec_flip2 in H4.
    erewrite <- access_same_rel_dec in Hreldec. 2: exact HL. rewrite Hreldec in H4.
    rewrite /maybe_non_children_only /= Hres in H4.
    destruct (item_lookup it' off) as [ini pp].
    destruct ini.
    { exfalso. eapply bind_Some in H4 as (x&Hx&(y&Hy&[=])%bind_Some). }
    rewrite lookup_insert_eq in HlL. injection HlL as ->.
    destruct pp as [|[]| | | |], (bool_decide (protector_is_active (iprot it) C)).
    all: simpl in H4; try discriminate H4; injection H4 as <-.
    all: try done. all: exfalso; by eapply Hnores.
  - odestruct (tree_access_lookup_outside_rev l) as (it'&H1&H2&H3&H4).
    1: exact HL. 1: done. 2: exact Hlu. 1: lia.
    odestruct (tree_access_lookup_outside_rev l) as (itcs'&H1cs&H2cs&H3cs&H4cs).
    1: exact HL. 1: done. 2: exact Hlucs. 1: lia.
    rewrite -H4 in Hres. eapply IH.
    split; first eapply H1. split.
    { erewrite access_same_rel_dec; first done. apply HL. }
    exists itcs', l. split.
    { rewrite lookup_insert_ne in HlL. all: done. }
    split; first done. rewrite H4cs Hres H3cs. done.
Qed.

Lemma tree_access_many_pseudo_confl_helper_2 C tg_acc (L : gmap Z _ ) tr1 trL S
  (Hwf1 : wf_tree tr1) :
  tree_unique tg_acc tr1 →
  let fn := (λ L tr, map_fold (λ l v tr2, tr2 ≫= memory_access_nonchildren_only v C tg_acc (l, 1%nat)) (Some tr) L) in
  fn L tr1 = Some trL →
  (∀ tg' it acc, is_pseudo_conflicted_by_in C tr1 tg' it S acc → acc = ResConflicted) →
  (∀ tg' it acc, is_pseudo_conflicted_by_in C trL tg' it (S ∪ {[ (tg_acc, L) ]}) acc → acc = ResConflicted).
Proof.
  intros Hunq fn Hfn H tg' it' acc (tg_cous&LS&[HH|[= -> -> ]%elem_of_singleton]%elem_of_union&Hrst).
  - eapply tree_access_many_pseudo_confl_helper_2_pers. 1: exact Hwf1. 1: apply Hunq. 1: apply Hfn.
    1: apply H. 1: do 2 eexists; done.
  - eapply tree_access_many_pseudo_confl_helper_2_news. 1: exact Hwf1. 1: apply Hunq. 1: apply Hfn. 1: apply Hrst.
Qed.

Lemma tree_access_many_pseudo_dis_helper_2 C tg_acc (L : gmap Z _ ) tr1 trL S nxtp nxtc
  (Hwf1 : wf_tree tr1) :
  tree_unique tg_acc tr1 →
  tree_items_compat_nexts tr1 nxtp nxtc →
  let fn := (λ L tr, map_fold (λ l v tr2, tr2 ≫= memory_access_nonchildren_only v C tg_acc (l, 1%nat)) (Some tr) L) in
  fn L tr1 = Some trL →
  (∀ tg' it acc, is_pseudo_disabled_by_in C tr1 tg' it S acc → acc = Disabled) →
  (∀ tg' it acc, is_pseudo_disabled_by_in C trL tg' it (S ∪ {[ (tg_acc, L) ]}) acc → acc = Disabled).
Proof.
  intros Hunq Hcompat fn Hfn H tg' it' acc (tg_cous&LS&[HH|[= -> -> ]%elem_of_singleton]%elem_of_union&Hrst).
  - eapply tree_access_many_pseudo_dis_helper_2_pers. 1: exact Hwf1. 1: apply Hunq. 1: done. 1: apply Hfn.
    1: apply H. 1: do 2 eexists; done.
  - eapply tree_access_many_pseudo_dis_helper_2_news. 1: exact Hwf1. 1: apply Hunq. 1: apply Hfn. 1: apply Hrst.
Qed.

Lemma tree_access_many_pseudo_confl_helper_1 C (L : list (tag * gmap Z _)) tr1 trL
  (Hwf1 : wf_tree tr1) :
  (∀ tg S, (tg, S) ∈ L → tree_unique tg tr1) →
  let fn := (λ E tr, foldr (λ '(tg, L) tr, tr ≫= λ tr1, map_fold (λ l v tr2, tr2 ≫= memory_access_nonchildren_only v C tg (l, 1%nat)) (Some tr1) (L)) (Some tr) E) in
  fn L tr1 = Some trL →
  (∀ tg' it acc, is_pseudo_conflicted_by_in C tr1 tg' it ∅ acc → acc = ResConflicted) →
  (∀ tg' it acc, is_pseudo_conflicted_by_in C trL tg' it (list_to_set L) acc → acc = ResConflicted).
Proof.
  intros Hunq fn Hfn H.
  induction L as [|(tg_acc&S) L IH] in trL,Hunq,Hfn|-*.
  1: rewrite list_to_set_nil; simpl in Hfn; injection Hfn as ->; done.
  simpl in Hfn.
  apply bind_Some in Hfn as (tr2&H1&H2).
  ospecialize (IH _ _ H1).
  { intros ???; eapply Hunq; by right. }
  rewrite list_to_set_cons union_comm_L.
  eapply tree_access_many_pseudo_confl_helper_2. 3: exact H2. 3: done.
  1: eapply preserve_tag_count_wf. 1: apply tree_access_many_helper_1. 1: done. 1: exact H1.
  rewrite /tree_unique. erewrite <- tree_access_many_helper_1; last exact H1. eapply Hunq.
  by left.
Qed.

Lemma tree_access_many_pseudo_dis_helper_1 C (L : list (tag * gmap Z _)) tr1 trL nxtp nxtc
  (Hwf1 : wf_tree tr1) :
  (∀ tg S, (tg, S) ∈ L → tree_unique tg tr1) →
  tree_items_compat_nexts tr1 nxtp nxtc →
  let fn := (λ E tr, foldr (λ '(tg, L) tr, tr ≫= λ tr1, map_fold (λ l v tr2, tr2 ≫= memory_access_nonchildren_only v C tg (l, 1%nat)) (Some tr1) (L)) (Some tr) E) in
  fn L tr1 = Some trL →
  (∀ tg' it acc, is_pseudo_disabled_by_in C tr1 tg' it ∅ acc → acc = Disabled) →
  (∀ tg' it acc, is_pseudo_disabled_by_in C trL tg' it (list_to_set L) acc → acc = Disabled).
Proof.
  intros Hunq Hcompat fn Hfn H.
  induction L as [|(tg_acc&S) L IH] in trL,Hunq,Hfn|-*.
  1: rewrite list_to_set_nil; simpl in Hfn; injection Hfn as ->; done.
  simpl in Hfn.
  apply bind_Some in Hfn as (tr2&H1&H2).
  ospecialize (IH _ _ H1).
  { intros ???; eapply Hunq; by right. }
  assert (tree_items_compat_nexts tr2 nxtp nxtc) as Hcompat2.
  { eapply tree_access_many_compat_nexts_helper_1. 2: done. done. }
  rewrite list_to_set_cons union_comm_L.
  eapply tree_access_many_pseudo_dis_helper_2. 4: exact H2. 4: done.
  1: eapply preserve_tag_count_wf. 1: apply tree_access_many_helper_1. 1: done. 1: exact H1. 2: done.
  rewrite /tree_unique. erewrite <- tree_access_many_helper_1; last exact H1. eapply Hunq.
  by left.
Qed.

Lemma tree_access_many_pseudo_confl_becomes_real C cid tr tr'
  (Hwf1 : wf_tree tr) :
  tree_access_all_protected_initialized C cid tr = Some tr' →
  (∀ tg' it acc, is_pseudo_conflicted_by_in C tr' tg' it (tree_get_all_protected_tags_initialized_locs cid tr) acc → acc = ResConflicted).
Proof.
  rewrite /tree_access_all_protected_initialized.
  pose (tree_get_all_protected_tags_initialized_locs cid tr) as L. fold L.
  intros Hfn. rewrite -(list_to_set_elements_L L).
  eapply tree_access_many_pseudo_confl_helper_1.
  - done.
  - eintros tg S (it&Hlu%lookup_implies_contains&_)%elem_of_elements%tree_all_protected_initialized_elem_of.
    all: by eapply wf_tree_tree_unique.
  - apply Hfn.
  - intros ??? (?&?&[]%elem_of_empty&_).
Qed.

Lemma tree_access_many_pseudo_dis_becomes_real C cid tr tr' nxtp nxtc
  (Hwf1 : wf_tree tr) 
  (Hcompat : tree_items_compat_nexts tr nxtp nxtc) :
  tree_access_all_protected_initialized C cid tr = Some tr' →
  (∀ tg' it acc, is_pseudo_disabled_by_in C tr' tg' it (tree_get_all_protected_tags_initialized_locs cid tr) acc → acc = Disabled).
Proof.
  rewrite /tree_access_all_protected_initialized.
  pose (tree_get_all_protected_tags_initialized_locs cid tr) as L. fold L.
  intros Hfn. rewrite -(list_to_set_elements_L L).
  eapply tree_access_many_pseudo_dis_helper_1.
  - done.
  - eintros tg S (it&Hlu%lookup_implies_contains&_)%elem_of_elements%tree_all_protected_initialized_elem_of.
    all: by eapply wf_tree_tree_unique.
  - done.
  - apply Hfn.
  - intros ??? (?&?&[]%elem_of_empty&_).
Qed.

Lemma tree_access_many_preserve_protector_2 C tg_acc (L : gmap Z _) tr1 trL
  (Hwf1 : wf_tree tr1) :
  let fn := (λ L tr, map_fold (λ l v tr2, tr2 ≫= memory_access_nonchildren_only v C tg_acc (l, 1%nat)) (Some tr) L) in
  fn L tr1 = Some trL →
  ∀ tgl it1 itL, tree_lookup tr1 tgl it1 → tree_lookup trL tgl itL → iprot it1 = iprot itL.
Proof.
  intros fn. subst fn. simpl.
  map_fold_weak_ind L as off v L HH1 HH2 IH in trL; simpl.
  { intros [= ->]. intros tg1 it1 it2 Hit1 Hit2. enough (it1 = it2) by (by simplify_eq).
    by eapply tree_lookup_unique. }
  intros (tr2&Hoff&HL)%bind_Some.
  specialize (IH _ Hoff).
  intros tgl it1 itL Hit1 HitL.
  assert (wf_tree tr2) as Hwf2.
  { eapply preserve_tag_count_wf. 1: eapply tree_access_many_helper_2. 1: exact Hwf1. 1: apply Hoff. }
  assert (∃ it, tree_lookup tr2 tgl it) as (it2&Hit2).
  { eapply lookup_implies_contains, count_gt0_exists in HitL.
    erewrite <- memory_access_tag_count in HitL; last done.
    eapply count_gt0_exists in HitL. by eapply unique_implies_lookup, wf_tree_tree_unique. }
  eapply apply_access_spec_per_node in HL as (itL'&Hacc&Hlu1&Hlu2). 2-3: by destruct Hit2.
  assert (tree_lookup trL tgl itL') as HH by done.
  pose proof (tree_lookup_unique _ _ _ _ HH HitL) as ->.
  symmetry in Hacc.
  eapply item_apply_access_preserves_metadata in Hacc as (He1&He2&He3).
  rewrite -He2. eapply IH; done.
Qed.

Lemma tree_access_many_preserve_protector_1 C (L : list (tag * gmap _ _)) tr1 trL
  (Hwf1 : wf_tree tr1) :
  let fn := (λ E tr, foldr (λ '(tg, L) tr, tr ≫= λ tr1, map_fold (λ l v tr2, tr2 ≫= memory_access_nonchildren_only v C tg (l, 1%nat)) (Some tr1) (L)) (Some tr) E) in
  fn L tr1 = Some trL →
  ∀ tgl it1 itL, tree_lookup tr1 tgl it1 → tree_lookup trL tgl itL → iprot it1 = iprot itL.
Proof.
  intros fn.
  induction L as [|(tg_acc&S) L IH] in trL|-*; simpl.
  { intros [= ->]. intros tg1 it1 it2 Hit1 Hit2. enough (it1 = it2) by (by simplify_eq).
    by eapply tree_lookup_unique. }
  intros (tr2&Hoff&HL)%bind_Some.
  specialize (IH _ Hoff).
  intros tgl it1 itL Hit1 HitL.
  assert (wf_tree tr2) as Hwf2.
  { eapply preserve_tag_count_wf. 1: eapply tree_access_many_helper_1. 1: exact Hwf1. 1: apply Hoff. }
  assert (∃ it, tree_lookup tr2 tgl it) as (it2&Hit2).
  { eapply lookup_implies_contains, count_gt0_exists in HitL.
    erewrite <- tree_access_many_helper_2 in HitL; last done.
    eapply count_gt0_exists in HitL. by eapply unique_implies_lookup, wf_tree_tree_unique. }
  erewrite <- (tree_access_many_preserve_protector_2 _ _ _ _ _ Hwf2 HL _ it2 itL); try done.
  eapply IH. all: done.
Qed.

Lemma tree_access_many_preserve_protector C cid tr1 trL
  (Hwf1 : wf_tree tr1) :
  tree_access_all_protected_initialized C cid tr1 = Some trL →
  ∀ tgl it1 itL, tree_lookup tr1 tgl it1 → tree_lookup trL tgl itL → iprot it1 = iprot itL.
Proof.
  rewrite /tree_access_all_protected_initialized.
  rewrite /set_fold /=. eapply tree_access_many_preserve_protector_1. done.
Qed.

Lemma tree_access_initialzed_equally_initialized b acc C tg_acc it_acc tr tr' off1 (sz : nat) offi :
  wf_tree tr →
  parents_more_init tr →
  tree_lookup tr tg_acc it_acc →
  (off1 ≤ offi < off1 + sz → initialized (item_lookup it_acc offi) = PermInit) →
  memory_access_maybe_nonchildren_only b acc C tg_acc (off1, sz) tr = Some tr' →
  ∀ tgl it it', tree_lookup tr tgl it → tree_lookup tr' tgl it' → initialized (item_lookup it offi) = initialized (item_lookup it' offi).
Proof.
  intros Hwf Hmoreinit Hlu Hinitacc Hacc tgl it it' Hit Hit'.
  destruct (decide (off1 ≤ offi < off1 + sz)) as [Hin|Hout]; last first.
  - eapply tree_access_lookup_outside in Hacc; [|done..|exact Hit].
    destruct Hacc as (itnew&Hitnewlu&Heq1&Heq2&Heq3).
    assert (itnew = it') as ->.
    { eapply tree_determined_unify. 1-2: eapply Hitnewlu. 1: apply Hit'. }
    by rewrite Heq3.
  - specialize (Hinitacc Hin).
    eapply tree_access_lookup_general in Hacc; [|done..|exact Hit].
    destruct Hacc as (itnew&Hitnewlu&Heq1&Heq2&Heq3).
    assert (itnew = it') as ->.
    { eapply tree_determined_unify. 1-2: eapply Hitnewlu. 1: apply Hit'. }
    edestruct maybe_non_children_only_effect_or_nop_strong as [(Heq&Haccrel)|(Heq&Hb&Himm)]; erewrite Heq in Heq3.
    2: by injection Heq3 as ->. clear Heq.
    eapply bind_Some in Heq3 as (pn&_&(pp&_&[= <-])%bind_Some).
    simpl. rewrite most_init_comm. rewrite /rel_dec in Haccrel|-*.
    destruct (decide (ParentChildIn tgl tg_acc tr)) as [HPCI|HnPCI]; last done. simpl.
    clear Haccrel.
    specialize (Hmoreinit tgl). eapply every_child_ParentChildIn in Hmoreinit; last eapply HPCI.
    2,3,5: eapply wf_tree_tree_unique; try done. 2,4: apply Hit. 2: apply Hlu.
    eapply every_node_eqv_universal in Hmoreinit.
    + eapply Hmoreinit. 2: exact Hinitacc. by eapply tree_lookup_correct_tag.
    + eapply exists_determined_exists; by eapply Hlu.
Qed.

Lemma tree_access_protected_active_initialized_equally acc C tg_acc it_acc tr tr' off1 (sz : nat) offi :
  wf_tree tr →
  parents_more_init tr →
  parents_more_active tr →
  no_active_cousins C tr →
  tree_lookup tr tg_acc it_acc →
  protector_is_active it_acc.(iprot) C →
  (off1 ≤ offi < off1 + sz → ∃ pp, (item_lookup it_acc offi) = mkPerm PermInit pp ∧ pp ≠ Cell ∧ (acc = AccessWrite → pp = Active)) →
  memory_access_nonchildren_only acc C tg_acc (off1, sz) tr = Some tr' →
  ∀ tgl it it', tree_lookup tr tgl it → tree_lookup tr' tgl it' → (item_lookup it offi) = mkPerm PermInit Active ↔ (item_lookup it' offi) = mkPerm PermInit Active.
Proof.
  intros Hwf Hmoreinit Hmoreactive Hcousins Hlu Hprot Hinitacc Hacc tgl it it' Hit Hit'.
  opose proof (tree_access_initialzed_equally_initialized true _ _ _ _ _ _ _ _ offi Hwf Hmoreinit Hlu _ Hacc _ _ _ Hit Hit') as Hiniteq.
  1: { intros ?. destruct Hinitacc as (pp&Hini&_). 1: done. rewrite Hini. done. }
  destruct (decide (off1 ≤ offi < off1 + sz)) as [Hin|Hout]; last first.
  - eapply tree_access_lookup_outside in Hacc; [|done..|exact Hit].
    destruct Hacc as (itnew&Hitnewlu&Heq1&Heq2&Heq3).
    assert (itnew = it') as ->.
    { eapply tree_determined_unify. 1-2: eapply Hitnewlu. 1: apply Hit'. }
    by rewrite Heq3.
  - specialize (Hinitacc Hin) as (ppi&Hinitacc&Hnocell&Hppi).
    eapply tree_access_lookup_general in Hacc as Hacc2; [|done..|exact Hit].
    destruct Hacc2 as (itnew&Hitnewlu&Heq1&Heq2&Heq3).
    assert (itnew = it') as ->.
    { eapply tree_determined_unify. 1-2: eapply Hitnewlu. 1: apply Hit'. }
    eapply tree_access_lookup_general in Hacc as Hacc2; [|done..|exact Hlu].
    destruct Hacc2 as (itaccnew&Hitaccnewlu&Heqacc1&Heqacc2&Heqacc3).
    edestruct maybe_non_children_only_effect_or_nop_strong as [(Heq&Haccrel)|(Heq&Hb&Himm)]; erewrite Heq in Heq3.
    2: by injection Heq3 as ->. clear Heq. 
    eapply bind_Some in Heq3 as (pn&Hpn&(pp&Hpp&[= Heq3])%bind_Some).
    rewrite -Heq3 /= in Hiniteq|-*.
    rewrite most_init_comm. rewrite /rel_dec in Haccrel,Hpn,Hpp,Hiniteq|-*.
    destruct (decide (ParentChildIn tgl tg_acc tr)) as [HPCI|HnPCI].
    2: destruct (decide (ParentChildIn tg_acc tgl tr)) as [HPCI2|HnPCI2].
    2: { destruct Haccrel as [[]|Hxx]; first done. exfalso. eapply Hxx. done. }
    all: split.
    + intros Hitoff. rewrite Hitoff /= in Hpp,Hpn|-*.
      f_equal.
      destruct acc, (bool_decide (protector_is_active (iprot it') C)), pp as [|[]| | | |]; simpl in Hpn,Hpp.
      all: try discriminate Hpn. all: injection Hpn as <-.
      all: simpl in Hpp; try discriminate Hpp. all: done.
    + rewrite /=. intros [= ->].
      rewrite /= in Hpp. assert (pn = Active) as ->. 1: clear Hiniteq; repeat (case_match; try by simplify_eq).
      rewrite /= /apply_access_perm /apply_access_perm_inner in Hpn.
      destruct acc.
      { rewrite /= in Hiniteq. destruct (item_lookup it offi) as [? pp]. f_equal. 1: rewrite /= most_init_comm /= // in Hiniteq.
        by destruct pp. }
      specialize (Hmoreactive tgl). eapply every_child_ParentChildIn in Hmoreactive.
      2: done. 2: eapply Hwf, Hit. 2: eapply Hit. 2: eapply Hwf, Hlu. 2: done.
      eapply every_node_eqv_universal in Hmoreactive.
      2: eapply tree_lookup_to_exists_node, Hlu. specialize (Hppi eq_refl). subst ppi.
      ospecialize (Hmoreactive _ offi _). 1: by eapply tree_lookup_correct_tag.
      1: rewrite Hinitacc //.
      rewrite most_init_comm /= in Hiniteq.
      simpl in Hmoreactive. destruct Hmoreactive as [Heq|Heq]; rewrite Heq in Hpn.
      all: destruct (item_lookup it offi); f_equal; try done.
    + intros Hitoff. exfalso. eapply Hcousins with (off:=offi).
      2: exact Hit. 1: exact Hlu. 1: rewrite /rel_dec decide_False // decide_False //.
      2: rewrite Hitoff //. right. rewrite Hinitacc. split.
      1: left; done. done.
    + intros Hwrong. exfalso. rewrite /= in Hwrong. injection Hwrong as Hwinit Hppeq. subst pp.
      all: rewrite Hwinit /= in Hpp.
      destruct acc, (bool_decide (protector_is_active (iprot it') C)), (perm (item_lookup it offi)) as [|[]| | | |]; cbv in Hpn;
      try discriminate Hpn; injection Hpn as <-.
      all: discriminate Hpp.
Qed.

Lemma tree_access_equally_cell acc C tg_acc it_acc tr tr' off1 (sz : nat) :
  wf_tree tr →
  tree_lookup tr tg_acc it_acc →
  memory_access_nonchildren_only acc C tg_acc (off1, sz) tr = Some tr' →
  ∀ offi tgl it it', tree_lookup tr tgl it → tree_lookup tr' tgl it' → perm (item_lookup it offi) = Cell ↔ perm (item_lookup it' offi) = Cell.
Proof.
  intros Hwf Hlu Hacc offi tgl it it' Hit Hit'.
  destruct (decide (off1 ≤ offi < off1 + sz)) as [Hin|Hout]; last first.
  - eapply tree_access_lookup_outside in Hacc; [|done..|exact Hit].
    destruct Hacc as (itnew&Hitnewlu&Heq1&Heq2&Heq3).
    assert (itnew = it') as ->.
    { eapply tree_determined_unify. 1-2: eapply Hitnewlu. 1: apply Hit'. }
    by rewrite Heq3.
  - eapply tree_access_lookup_general in Hacc as Hacc2; [|done..|exact Hit].
    destruct Hacc2 as (itnew&Hitnewlu&Heq1&Heq2&Heq3).
    assert (itnew = it') as ->.
    { eapply tree_determined_unify. 1-2: eapply Hitnewlu. 1: apply Hit'. }
    eapply tree_access_lookup_general in Hacc as Hacc2; [|done..|exact Hlu].
    destruct Hacc2 as (itaccnew&Hitaccnewlu&Heqacc1&Heqacc2&Heqacc3).
    edestruct maybe_non_children_only_effect_or_nop_strong as [(Heq&Haccrel)|(Heq&Hb&Himm)]; erewrite Heq in Heq3.
    2: by injection Heq3 as ->. clear Heq. 
    eapply bind_Some in Heq3 as (pn&Hpn&(pp&Hpp&[= Heq3])%bind_Some).
    rewrite -Heq3 /=. split.
    + intros Hcell. rewrite Hcell in Hpn.
      assert (pn = Cell) as ->.
      { clear -Hpn. rewrite /apply_access_perm_inner in Hpn. do 2 case_match; congruence. }
      clear -Hpp. repeat (case_match; simplify_eq; try done).
    + intros ->. assert (pn = Cell) as ->.
      { clear -Hpp. repeat (case_match; simplify_eq; try done). }
      clear -Hpn. rewrite /apply_access_perm_inner in Hpn.
      repeat (case_match; simplify_eq; try done).
Qed.


Lemma tree_access_many_more_initialized_2 C tg_acc (L : gmap Z _) tr1 trL
  (Hwf1 : wf_tree tr1) :
  let fn := (λ L tr, map_fold (λ l v tr2, tr2 ≫= memory_access_nonchildren_only v C tg_acc (l, 1%nat)) (Some tr) L) in
  fn L tr1 = Some trL →
  ∀ tgl it1 itL l, tree_lookup tr1 tgl it1 → tree_lookup trL tgl itL → initialized (item_lookup it1 l) = PermInit → initialized (item_lookup itL l) = PermInit.
Proof.
  intros fn. subst fn. simpl.
  map_fold_weak_ind L as off v L HH1 HH2 IH in trL; simpl.
  { intros [= ->]. intros tg1 it1 it2 l Hit1 Hit2. enough (it1 = it2) by (by simplify_eq).
    by eapply tree_lookup_unique. }
  intros (tr2&Hoff&HL)%bind_Some.
  specialize (IH _ Hoff).
  intros tgl it1 itL z Hit1 HitL.
  assert (wf_tree tr2) as Hwf2.
  { eapply preserve_tag_count_wf. 1: eapply tree_access_many_helper_2. 1: exact Hwf1. 1: apply Hoff. }
  destruct (decide (z = off)) as [->|Hne].
  - eapply (tree_access_lookup_general_rev off) in HL as (it2 & Hit2 & _ & _ & Hperm). 2: done. 2: lia. 2: done.
    edestruct (maybe_non_children_only_effect_or_nop) as [Heq|Heq]; erewrite Heq in Hperm.
    2: { injection Hperm as <-. by eapply IH. }
    intros H1ini. enough (initialized (item_lookup it2 off) = PermInit) as HH. 2: by eapply IH.
    eapply bind_Some in Hperm as (x1&Hx1&(x2&Hx2&[= <-])%bind_Some). simpl. rewrite HH. done.
  - eapply (tree_access_lookup_outside_rev z) in HL as (it2 & Hit2 & _ & _ & Hperm). 2: done. 2: lia. 2: done.
    rewrite -Hperm. by eapply IH.
Qed.

Lemma tree_access_many_more_active_initialized_2 C tg_acc (L : gmap Z _) tr1 trL
  (Hwf1 : wf_tree tr1) :
  let fn := (λ L tr, map_fold (λ l v tr2, tr2 ≫= memory_access_nonchildren_only v C tg_acc (l, 1%nat)) (Some tr) L) in
  fn L tr1 = Some trL →
  ∀ tgl it1 itL l, tree_lookup tr1 tgl it1 → tree_lookup trL tgl itL → protector_is_active it1.(iprot) C → (item_lookup it1 l) = mkPerm PermInit Active → (item_lookup itL l) = mkPerm PermInit Active.
Proof.
  intros fn. subst fn. simpl.
  map_fold_weak_ind L as off v L HH1 HH2 IH in trL; simpl.
  { intros [= ->]. intros tg1 it1 it2 l Hit1 Hit2. enough (it1 = it2) by (by simplify_eq).
    by eapply tree_lookup_unique. }
  intros (tr2&Hoff&HL)%bind_Some.
  specialize (IH _ Hoff).
  intros tgl it1 itL z Hit1 HitL.
  assert (wf_tree tr2) as Hwf2.
  { eapply preserve_tag_count_wf. 1: eapply tree_access_many_helper_2. 1: exact Hwf1. 1: apply Hoff. }
  destruct (decide (z = off)) as [->|Hne].
  - eapply (tree_access_lookup_general_rev off) in HL as (it2 & Hit2 & _ & Hpp & Hperm). 2: done. 2: lia. 2: done.
    edestruct (maybe_non_children_only_effect_or_nop) as [Heq|Heq]; erewrite Heq in Hperm.
    2: { injection Hperm as <-. by eapply IH. }
    intros Hprot H1ini.
    eapply tree_access_many_preserve_protector_2 in Hoff as Hprot2.
    2: done. 2 : exact Hit1. 2: done. rewrite -Hpp -Hprot2 in Hperm.
    rewrite bool_decide_eq_true_2 // in Hperm.
    enough ((item_lookup it2 off) = mkPerm PermInit Active) as HH. 2: by eapply IH.
    rewrite HH in Hperm. destruct v, (rel_dec tr2 tg_acc tgl).
    all: try discriminate Hperm. all: by injection Hperm.
  - eapply (tree_access_lookup_outside_rev z) in HL as (it2 & Hit2 & _ & _ & Hperm). 2: done. 2: lia. 2: done.
    rewrite -Hperm. by eapply IH.
Qed.

Lemma tree_access_many_equally_initialized_2 C tg_acc (L : gmap Z _) tr1 trL
  (Hwf1 : wf_tree tr1) (Hmore1 : parents_more_init tr1) :
  tree_contains tg_acc tr1 →
  (∀ z it, z ∈ dom L → tree_lookup tr1 tg_acc it → initialized (item_lookup it z) = PermInit) →
  let fn := (λ L tr, map_fold (λ l v tr2, tr2 ≫= memory_access_nonchildren_only v C tg_acc (l, 1%nat)) (Some tr) L) in
  fn L tr1 = Some trL →
  ∀ tgl it1 itL l, tree_lookup tr1 tgl it1 → tree_lookup trL tgl itL → initialized (item_lookup it1 l) = initialized (item_lookup itL l).
Proof.
  intros Hcont Hinit fn. subst fn; simpl.
  map_fold_weak_ind L as off v L HH1 HH2 IH in trL Hinit; simpl.
  { intros [= ->]. intros tg1 it1 it2 l Hit1 Hit2. enough (it1 = it2) by (by simplify_eq).
    by eapply tree_lookup_unique. }
  intros (tr2&Hoff&HL)%bind_Some.
  intros tgl it1 itL z Hit1 HitL.
  assert (wf_tree tr2) as Hwf2.
  { eapply preserve_tag_count_wf. 1: eapply tree_access_many_helper_2. 1: exact Hwf1. 1: apply Hoff. }
  assert (parents_more_init tr2) as Htr2.
  { eapply tree_access_many_more_init_helper_2. 4: exact Hoff. 1-3: done. }
  assert (tree_unique tg_acc tr1) as Hunqtr1.
  { by eapply Hwf1. }
  assert (tree_unique tg_acc tr2) as Hunqtr2.
  { rewrite /tree_unique in Hunqtr1|-*. erewrite <-tree_access_many_helper_2. 1: exact Hunqtr1. 1: exact Hoff. }
  assert (tree_unique tgl tr2) as Hunqtgl2.
  { rewrite /tree_unique. erewrite <-tree_access_many_helper_2. 2: exact Hoff. eapply Hwf1. by eapply Hit1. }
  eapply unique_implies_lookup in Hunqtgl2 as Hmid. destruct Hmid as (it2&Hit2).
  eapply unique_implies_lookup in Hunqtr2 as Hmid. destruct Hmid as (itacc2&Hitacc2).
  eapply unique_implies_lookup in Hunqtr1 as Hmid. destruct Hmid as (itacc1&Hitacc1).
  ospecialize (IH _ _ Hoff).
  { intros zz itz HzzL Hlu. eapply Hinit; last done. rewrite dom_insert_L. set_solver. }
  erewrite IH. 2-3: done.
  eapply tree_access_initialzed_equally_initialized. 5: exact HL. 1-2: done. 4: exact HitL. 3: exact Hit2. 1: done.
  intros H. assert (off = z) as -> by lia.
  eapply tree_access_many_more_initialized_2.
  2: exact Hoff. 1: done. 2: done. 1: done.
  eapply Hinit. 2: done. rewrite dom_insert_L. set_solver.
Qed.

Lemma tree_access_many_equally_cell_2 C tg_acc it_acc (L : gmap Z _) tr1 trL :
  wf_tree tr1 →
  tree_lookup tr1 tg_acc it_acc →
  let fn := (λ L tr, map_fold (λ l v tr2, tr2 ≫= memory_access_nonchildren_only v C tg_acc (l, 1%nat)) (Some tr) L) in
  fn L tr1 = Some trL →
  ∀ tgl it1 itL l, tree_lookup tr1 tgl it1 → tree_lookup trL tgl itL → perm (item_lookup it1 l) = Cell ↔ perm (item_lookup itL l) = Cell.
Proof.
  intros Hwf1 Hlookup1 fn. subst fn; simpl.
  map_fold_weak_ind L as off v L HH1 HH2 IH in trL; simpl.
  { intros [= ->]. intros tg1 it1 it2 l Hit1 Hit2. enough (it1 = it2) by (by simplify_eq).
    by eapply tree_lookup_unique. }
  intros (tr2&Hoff&HL)%bind_Some.
  intros tgl it1 itL z Hit1 HitL.
  assert (wf_tree tr2) as Hwf2.
  { eapply preserve_tag_count_wf. 1: eapply tree_access_many_helper_2. 1: exact Hwf1. 1: apply Hoff. }
  assert (tree_unique tg_acc tr1) as Hunqtr1.
  { eapply Hwf1, Hlookup1. }
  assert (tree_unique tg_acc tr2) as Hunqtr2.
  { rewrite /tree_unique in Hunqtr1|-*. erewrite <-tree_access_many_helper_2. 1: exact Hunqtr1. 1: exact Hoff. }
  assert (tree_unique tgl tr2) as Hunqtgl2.
  { rewrite /tree_unique. erewrite <-tree_access_many_helper_2. 2: exact Hoff. eapply Hwf1. by eapply Hit1. }
  eapply unique_implies_lookup in Hunqtgl2 as Hmid. destruct Hmid as (it2&Hit2).
  eapply unique_implies_lookup in Hunqtr2 as Hmid. destruct Hmid as (itacc2&Hitacc2).
  eapply unique_implies_lookup in Hunqtr1 as Hmid. destruct Hmid as (itacc1&Hitacc1).
  ospecialize (IH _ Hoff).
  erewrite IH. 2-3: done.
  erewrite tree_access_equally_cell. 1: done. 3: done. all: done.
Qed.

Lemma tree_access_many_equally_active_initialized_2 C tg_acc it_acc (L : gmap Z _) tr1 trL :
  wf_tree tr1 →
  parents_more_init tr1 →
  parents_more_active tr1 →
  no_active_cousins C tr1 →
  tree_lookup tr1 tg_acc it_acc →
  protector_is_active it_acc.(iprot) C →
  (∀ z v, L !! z = Some v → ∃ pp, (item_lookup it_acc z) = mkPerm PermInit pp ∧ pp ≠ Cell ∧ (v = AccessWrite → pp = Active)) →
  let fn := (λ L tr, map_fold (λ l v tr2, tr2 ≫= memory_access_nonchildren_only v C tg_acc (l, 1%nat)) (Some tr) L) in
  fn L tr1 = Some trL →
  ∀ tgl it1 itL l, tree_lookup tr1 tgl it1 → tree_lookup trL tgl itL → (item_lookup it1 l) = mkPerm PermInit Active ↔ (item_lookup itL l) = mkPerm PermInit Active.
Proof.
  intros Hwf1 Hmore1 Hmorea1 Hcousins1 Hlookup1 Hprot1 Hinit fn. subst fn; simpl.
  map_fold_weak_ind L as off v L HH1 HH2 IH in trL Hinit; simpl.
  { intros [= ->]. intros tg1 it1 it2 l Hit1 Hit2. enough (it1 = it2) by (by simplify_eq).
    by eapply tree_lookup_unique. }
  intros (tr2&Hoff&HL)%bind_Some.
  intros tgl it1 itL z Hit1 HitL.
  assert (wf_tree tr2) as Hwf2.
  { eapply preserve_tag_count_wf. 1: eapply tree_access_many_helper_2. 1: exact Hwf1. 1: apply Hoff. }
  assert (parents_more_init tr2) as Htr2.
  { eapply tree_access_many_more_init_helper_2. 4: exact Hoff. 1,3: done. eapply Hlookup1. }
  assert (parents_more_active tr2) as Htract2.
  { eapply tree_access_many_more_active_helper_2. 4: exact Hoff. 1,3: done. eapply Hlookup1. }
  assert (no_active_cousins C tr2) as Htrcous2.
  { eapply tree_access_many_no_cousins_helper_2. 4: exact Hoff. 1,3: done. eapply Hlookup1. }
  assert (tree_unique tg_acc tr1) as Hunqtr1.
  { eapply Hwf1, Hlookup1. }
  assert (tree_unique tg_acc tr2) as Hunqtr2.
  { rewrite /tree_unique in Hunqtr1|-*. erewrite <-tree_access_many_helper_2. 1: exact Hunqtr1. 1: exact Hoff. }
  assert (tree_unique tgl tr2) as Hunqtgl2.
  { rewrite /tree_unique. erewrite <-tree_access_many_helper_2. 2: exact Hoff. eapply Hwf1. by eapply Hit1. }
  eapply unique_implies_lookup in Hunqtgl2 as Hmid. destruct Hmid as (it2&Hit2).
  eapply unique_implies_lookup in Hunqtr2 as Hmid. destruct Hmid as (itacc2&Hitacc2).
  eapply unique_implies_lookup in Hunqtr1 as Hmid. destruct Hmid as (itacc1&Hitacc1).
  ospecialize (IH _ _ Hoff).
  { intros zz vv HH. eapply Hinit. rewrite lookup_insert_ne //. intros ->. congruence. }
  erewrite IH. 2-3: done.
  eapply tree_access_many_preserve_protector_2 in Hoff as Hprot. 2: done. 2: exact Hlookup1. 2: done.
  eapply tree_access_protected_active_initialized_equally. 8: exact HL. 1-2: done. 7: exact HitL. 6: exact Hit2. 3: done. 1-2: done.
  1: by rewrite -Hprot.
  intros H. assert (off = z) as -> by lia.
  destruct (Hinit z v) as (pp&Hpp1&Hppnc&Hpp2). 1: by rewrite lookup_insert_eq.
  opose proof (tree_access_many_equally_cell_2 _ _ _ _ _ _ _ _ Hoff _ _ _ z) as Hcells; [done..|].
  destruct (item_lookup itacc2 z) as [ii2 pp2] eqn:Heqii. exists pp2.
  assert (ii2 = PermInit) as ->.
  { opose proof* tree_access_many_more_initialized_2 as Hini. 2: exact Hoff. 1: done. 1: exact Hlookup1. 1: done.
    1: erewrite Hpp1; done. by rewrite Heqii in Hini. }
  split; first done. split.
  { intros ->. eapply Hppnc. ospecialize (Hcells Hlookup1 _); first done. rewrite Hpp1 in Hcells.
    apply Hcells. by rewrite Heqii. }
  intros Hv. specialize (Hpp2 Hv). subst pp.
  eapply tree_access_many_more_active_initialized_2 in Hpp1. 3: exact Hoff. 2: done. 2,4: done. 2: done.
  rewrite Heqii in Hpp1. by simplify_eq.
Qed.


Lemma tree_access_many_more_initialized_1 C (L : list (tag * gmap Z _)) tr1 trL
  (Hwf1 : wf_tree tr1) :
  let fn := (λ E tr, foldr (λ '(tg, L) tr, tr ≫= λ tr1, map_fold (λ l v tr2, tr2 ≫= memory_access_nonchildren_only v C tg (l, 1%nat)) (Some tr1) (L)) (Some tr) E) in
  fn L tr1 = Some trL →
  ∀ tgl it1 itL l, tree_lookup tr1 tgl it1 → tree_lookup trL tgl itL → initialized (item_lookup it1 l) = PermInit → initialized (item_lookup itL l) = PermInit.
Proof.
  intros fn.
  induction L as [|(tg_acc&S) L IH] in trL|-*; simpl.
  { intros [= ->]. intros tg1 it1 it2 off Hit1 Hit2. enough (it1 = it2) by (by simplify_eq).
    by eapply tree_lookup_unique. }
  intros (tr2&Hoff&HL)%bind_Some.
  specialize (IH _ Hoff).
  intros tgl it1 itL off Hit1 HitL.
  assert (wf_tree tr2) as Hwf2.
  { eapply preserve_tag_count_wf. 1: eapply tree_access_many_helper_1. 1: exact Hwf1. 1: apply Hoff. }
  assert (∃ it, tree_lookup tr2 tgl it) as (it2&Hit2).
  { eapply lookup_implies_contains, count_gt0_exists in HitL.
    erewrite <- tree_access_many_helper_2 in HitL; last done.
    eapply count_gt0_exists in HitL. by eapply unique_implies_lookup, wf_tree_tree_unique. }
  intros Hini.
  erewrite <- (tree_access_many_more_initialized_2 _ _ _ _ _ Hwf2 HL _ it2 itL); try done.
  eapply IH. all: done.
Qed.

Lemma tree_access_many_equally_cell_1 C (L : list (tag * gmap Z _)) tr1 trL
  (Hwf1 : wf_tree tr1) :
  (∀ tg_acc E, (tg_acc, E) ∈ L → tree_contains tg_acc tr1) →
  let fn := (λ E tr, foldr (λ '(tg, L) tr, tr ≫= λ tr1, map_fold (λ l v tr2, tr2 ≫= memory_access_nonchildren_only v C tg (l, 1%nat)) (Some tr1) (L)) (Some tr) E) in
  fn L tr1 = Some trL →
  ∀ tgl it1 itL l, tree_lookup tr1 tgl it1 → tree_lookup trL tgl itL → perm (item_lookup it1 l) = Cell ↔ perm (item_lookup itL l) = Cell.
Proof.
  intros Hcont fn.
  induction L as [|(tg_acc&S) L IH] in trL,Hcont|-*; simpl.
  { intros [= ->]. intros tg1 it1 it2 off Hit1 Hit2. enough (it1 = it2) by (by simplify_eq).
    by eapply tree_lookup_unique. }
  intros (tr2&Hoff&HL)%bind_Some.
  ospecialize (IH _ _ Hoff).
  { intros ?? H; eapply Hcont. by right. }
  intros tgl it1 itL off Hit1 HitL.
  assert (wf_tree tr2) as Hwf2.
  { eapply preserve_tag_count_wf. 1: eapply tree_access_many_helper_1. 1: exact Hwf1. 1: apply Hoff. }
  assert (∃ it, tree_lookup tr2 tgl it) as (it2&Hit2).
  { eapply lookup_implies_contains, count_gt0_exists in HitL.
    erewrite <- tree_access_many_helper_2 in HitL; last done.
    eapply count_gt0_exists in HitL. by eapply unique_implies_lookup, wf_tree_tree_unique. }
  assert (tree_unique tg_acc tr2) as (itacc2&Hitacc2)%unique_implies_lookup.
  { rewrite /tree_unique. erewrite <- tree_access_many_helper_1. 2: exact Hoff. eapply Hwf1, Hcont. by left. }
  erewrite <- (tree_access_many_equally_cell_2 _ _ _ _ _ _ Hwf2 Hitacc2 HL _ _ _ _ Hit2 HitL).
  eapply IH. all: done.
Qed.

Lemma tree_access_many_more_active_initialized_1 C (L : list (tag * gmap Z _)) tr1 trL
  (Hwf1 : wf_tree tr1) (Hmore1 : parents_more_init tr1) :
  (∀ tg_acc E, (tg_acc, E) ∈ L → tree_contains tg_acc tr1 ∧ (∀ z it, z ∈ dom E → tree_lookup tr1 tg_acc it → initialized (item_lookup it z) = PermInit)) →
  let fn := (λ E tr, foldr (λ '(tg, L) tr, tr ≫= λ tr1, map_fold (λ l v tr2, tr2 ≫= memory_access_nonchildren_only v C tg (l, 1%nat)) (Some tr1) (L)) (Some tr) E) in
  fn L tr1 = Some trL →
  ∀ tgl it1 itL l, tree_lookup tr1 tgl it1 → tree_lookup trL tgl itL → protector_is_active it1.(iprot) C → (item_lookup it1 l) = mkPerm PermInit Active → (item_lookup itL l) = mkPerm PermInit Active.
Proof.
  intros Hinit fn.
  induction L as [|(tg_acc&S) L IH] in trL,Hinit|-*; simpl.
  { intros [= ->]. intros tg1 it1 it2 off Hit1 Hit2. enough (it1 = it2) by (by simplify_eq).
    by eapply tree_lookup_unique. }
  intros (tr2&Hoff&HL)%bind_Some.
  intros tgl it1 itL z Hit1 HitL.
  assert (wf_tree tr2) as Hwf2.
  { eapply preserve_tag_count_wf. 1: eapply tree_access_many_helper_1. 1: exact Hwf1. 1: apply Hoff. }
  assert (parents_more_init tr2) as Htr2.
  { eapply tree_access_many_more_init_helper_1. 4: exact Hoff. 1,3: done.
    intros ???. eapply Hinit. by right. }
  assert (tree_unique tg_acc tr1) as Hunqtr1.
  { eapply Hwf1, Hinit. by left. }
  assert (tree_unique tg_acc tr2) as Hunqtr2.
  { rewrite /tree_unique in Hunqtr1|-*. erewrite <-tree_access_many_helper_1. 1: exact Hunqtr1. 1: exact Hoff. }
  assert (tree_unique tgl tr2) as Hunqtgl2.
  { rewrite /tree_unique. erewrite <-tree_access_many_helper_1. 2: exact Hoff. eapply Hwf1. by eapply Hit1. }
  eapply unique_implies_lookup in Hunqtgl2 as Hmid. destruct Hmid as (it2&Hit2).
  eapply unique_implies_lookup in Hunqtr2 as Hmid. destruct Hmid as (itacc2&Hitacc2).
  eapply unique_implies_lookup in Hunqtr1 as Hmid. destruct Hmid as (itacc1&Hitacc1).
  ospecialize (IH _ _ Hoff).
  { intros tgE E HE. split. 1: eapply Hinit; by right. intros zz itz HzzL Hlu. eapply Hinit; last done. 1: by right. done. }
  intros HH1 HH2. eapply IH in HH2. 4: done. 2: done. 2: done.
  eapply tree_access_many_more_active_initialized_2. 2: exact HL. 1,3: done. 1: done. 2: done.
  eapply tree_access_many_preserve_protector_1 in Hoff. 2: done. 2: eapply Hit1. 2: done.
  by rewrite -Hoff.
Qed.


Lemma tree_access_many_equally_initialized_1 C (L : list (tag * gmap Z _)) tr1 trL
  (Hwf1 : wf_tree tr1) (Hmore1 : parents_more_init tr1) :
  (∀ tg_acc E, (tg_acc, E) ∈ L → tree_contains tg_acc tr1 ∧ (∀ z it, z ∈ dom E → tree_lookup tr1 tg_acc it → initialized (item_lookup it z) = PermInit)) →
  let fn := (λ E tr, foldr (λ '(tg, L) tr, tr ≫= λ tr1, map_fold (λ l v tr2, tr2 ≫= memory_access_nonchildren_only v C tg (l, 1%nat)) (Some tr1) (L)) (Some tr) E) in
  fn L tr1 = Some trL →
  ∀ tgl it1 itL l, tree_lookup tr1 tgl it1 → tree_lookup trL tgl itL → initialized (item_lookup it1 l) = initialized (item_lookup itL l).
Proof.
  intros Hinit fn.
  induction L as [|(tg_acc&S) L IH] in trL,Hinit|-*; simpl.
  { intros [= ->]. intros tg1 it1 it2 off Hit1 Hit2. enough (it1 = it2) by (by simplify_eq).
    by eapply tree_lookup_unique. }
  intros (tr2&Hoff&HL)%bind_Some.
  intros tgl it1 itL z Hit1 HitL.
  assert (wf_tree tr2) as Hwf2.
  { eapply preserve_tag_count_wf. 1: eapply tree_access_many_helper_1. 1: exact Hwf1. 1: apply Hoff. }
  assert (parents_more_init tr2) as Htr2.
  { eapply tree_access_many_more_init_helper_1. 4: exact Hoff. 1,3: done.
    intros ???. eapply Hinit. by right. }
  assert (tree_unique tg_acc tr1) as Hunqtr1.
  { eapply Hwf1, Hinit. by left. }
  assert (tree_unique tg_acc tr2) as Hunqtr2.
  { rewrite /tree_unique in Hunqtr1|-*. erewrite <-tree_access_many_helper_1. 1: exact Hunqtr1. 1: exact Hoff. }
  assert (tree_unique tgl tr2) as Hunqtgl2.
  { rewrite /tree_unique. erewrite <-tree_access_many_helper_1. 2: exact Hoff. eapply Hwf1. by eapply Hit1. }
  eapply unique_implies_lookup in Hunqtgl2 as Hmid. destruct Hmid as (it2&Hit2).
  eapply unique_implies_lookup in Hunqtr2 as Hmid. destruct Hmid as (itacc2&Hitacc2).
  eapply unique_implies_lookup in Hunqtr1 as Hmid. destruct Hmid as (itacc1&Hitacc1).
  ospecialize (IH _ _ Hoff).
  { intros tgE E HE. split. 1: eapply Hinit; by right. intros zz itz HzzL Hlu. eapply Hinit; last done. 1: by right. done. }
  erewrite IH. 2-3: done.
  eapply tree_access_many_equally_initialized_2. 5: exact HL. 1-2: done. 4: exact HitL. 3: exact Hit2. 1: by eapply unique_exists.
  intros zz it HS Hlu.
  eapply tree_access_many_more_initialized_1.
  2: exact Hoff. 1: done. 2: done. 1: done.
  eapply Hinit. 1: by left. 2: done. done.
Qed.

Lemma tree_access_many_equally_active_initialized_1 C (L : list (tag * gmap Z _)) tr1 trL : 
  wf_tree tr1 →
  parents_more_init tr1 →
  parents_more_active tr1 →
  no_active_cousins C tr1 →
  (∀ tg_acc E, (tg_acc, E) ∈ L → ∃ it_acc, tree_lookup tr1 tg_acc it_acc ∧ protector_is_active it_acc.(iprot) C ∧ ∀ z v, E !! z = Some v → ∃ pp, (item_lookup it_acc z) = mkPerm PermInit pp ∧ pp ≠ Cell ∧ (v = AccessWrite → pp = Active)) →
  let fn := (λ E tr, foldr (λ '(tg, L) tr, tr ≫= λ tr1, map_fold (λ l v tr2, tr2 ≫= memory_access_nonchildren_only v C tg (l, 1%nat)) (Some tr1) (L)) (Some tr) E) in
  fn L tr1 = Some trL →
  ∀ tgl it1 itL l, tree_lookup tr1 tgl it1 → tree_lookup trL tgl itL → (item_lookup it1 l) = mkPerm PermInit Active ↔ (item_lookup itL l) = mkPerm PermInit Active.
Proof.
  intros Hwf1 Hmore1 Hmoreact1 Hcous1 Hinit fn.
  induction L as [|(tg_acc&S) L IH] in trL,Hinit|-*; simpl.
  { intros [= ->]. intros tg1 it1 it2 off Hit1 Hit2. enough (it1 = it2) by (by simplify_eq).
    by eapply tree_lookup_unique. }
  intros (tr2&Hoff&HL)%bind_Some.
  intros tgl it1 itL z Hit1 HitL.
  assert (wf_tree tr2) as Hwf2.
  { eapply preserve_tag_count_wf. 1: eapply tree_access_many_helper_1. 1: exact Hwf1. 1: apply Hoff. }
  assert (parents_more_init tr2) as Htr2.
  { eapply tree_access_many_more_init_helper_1. 4: exact Hoff. 1,3: done.
    intros x1 x2 H. destruct (Hinit x1 x2) as (ii&Hii&_). 2: eapply Hii. by right. }
  assert (parents_more_active tr2) as Htract2.
  { eapply tree_access_many_more_active_helper_1. 4: exact Hoff. 1,3: done.
    intros x1 x2 H. destruct (Hinit x1 x2) as (ii&Hii&_). 2: eapply Hii. by right. }
  assert (no_active_cousins C tr2) as Htrcous2.
  { eapply tree_access_many_no_cousins_helper_1. 4: exact Hoff. 1,3: done. 
    intros x1 x2 H. destruct (Hinit x1 x2) as (ii&Hii&_). 2: eapply Hii. by right. }
  destruct (Hinit tg_acc S) as (it_acc&Hit_acc&Hprot_acc&HHinit). 1: by left.
  assert (tree_unique tg_acc tr1) as Hunqtr1.
  { eapply Hwf1, Hit_acc. }
  assert (tree_unique tg_acc tr2) as Hunqtr2.
  { rewrite /tree_unique in Hunqtr1|-*. erewrite <-tree_access_many_helper_1. 1: exact Hunqtr1. 1: exact Hoff. }
  assert (tree_unique tgl tr2) as Hunqtgl2.
  { rewrite /tree_unique. erewrite <-tree_access_many_helper_1. 2: exact Hoff. eapply Hwf1. by eapply Hit1. }
  eapply unique_implies_lookup in Hunqtgl2 as Hmid. destruct Hmid as (it2&Hit2).
  eapply unique_implies_lookup in Hunqtr2 as Hmid. destruct Hmid as (itacc2&Hitacc2).
  ospecialize (IH _ _ Hoff).
  { intros tgE E HE. eapply (Hinit tgE E). by right. }
  erewrite IH. 2-3: done.
  eapply tree_access_many_preserve_protector_1 in Hoff as Hprot. 2: done. 2: exact Hit_acc. 2: done.
  eapply tree_access_many_equally_active_initialized_2. 8: exact HL. 1-2: done. 7: exact HitL. 6: exact Hit2. 3: done. 1-2: done.
  1: by rewrite -Hprot.
  intros zz v Hzv.
  destruct (HHinit zz v) as (pp&Hpp1&Hppnc&Hpp2). 1: done.
  destruct (item_lookup itacc2 zz) as [ii2 pp2] eqn:Heqii. exists pp2.
  assert (ii2 = PermInit) as ->.
  { opose proof* tree_access_many_more_initialized_1 as Hini. 2: exact Hoff. 1: done. 1: exact Hit_acc. 1: done.
    1: erewrite Hpp1; done. by rewrite Heqii in Hini. }
  opose proof (tree_access_many_equally_cell_1 _ _ _ _ Hwf1 _ Hoff) as Hcells; last first.
  2: { intros x1 x2 H. destruct (Hinit x1 x2) as (it&Hit&_). 1: by right. eapply Hit. }
  split; first done. split.
  { intros ->. eapply Hppnc. ospecialize (Hcells _ _ _ zz Hit_acc _); first done. rewrite Hpp1 in Hcells.
    apply Hcells. by rewrite Heqii. }
  intros Hv. specialize (Hpp2 Hv). subst pp.
  eapply tree_access_many_more_active_initialized_1 in Hpp1. 5: exact Hoff. 2-3: done. 3: done. 3: done. 3: done.
  1: rewrite Heqii in Hpp1; by simplify_eq.
  intros tt EE Htt.
  edestruct (Hinit tt EE) as (ittt&Htt1&Htt2&Htt3). 1: by right.
  split; first by eapply Htt1.
  intros x y [vx Hvx]%elem_of_dom Hy.
  assert (y = ittt) by by eapply tree_lookup_unique.
  subst y. destruct (Htt3 _ _ Hvx) as (pp&Hlu&_). by rewrite Hlu.
Qed.

Lemma tree_access_many_more_initialized C cid tr1 trL
  (Hwf1 : wf_tree tr1) :
  tree_access_all_protected_initialized C cid tr1 = Some trL →
  ∀ tgl it1 itL l, tree_lookup tr1 tgl it1 → tree_lookup trL tgl itL → initialized (item_lookup it1 l) = PermInit → initialized (item_lookup itL l) = PermInit.
Proof.
  rewrite /tree_access_all_protected_initialized.
  rewrite /set_fold /=. eapply tree_access_many_more_initialized_1. done.
Qed.

Lemma tree_access_many_more_active_initialized C cid tr1 trL
  (Hwf1 : wf_tree tr1) (Hmore1 : parents_more_init tr1) :
  tree_access_all_protected_initialized C cid tr1 = Some trL →
  ∀ tgl it1 itL l, tree_lookup tr1 tgl it1 → tree_lookup trL tgl itL → protector_is_active it1.(iprot) C → (item_lookup it1 l) = mkPerm PermInit Active → (item_lookup itL l) = mkPerm PermInit Active.
Proof.
  rewrite /tree_access_all_protected_initialized.
  rewrite /set_fold /=. eapply tree_access_many_more_active_initialized_1. 1: done. 1: done.
  intros tg E (it&Hit&Hprot&HHit)%elem_of_elements%tree_all_protected_initialized_elem_of.
  2: by eapply Hwf1.
  split. 1: eapply Hit.
  intros z it' [v (Hv&_)%HHit]%elem_of_dom Hlu'.
  enough (it = it') as ->; first done.
  eapply tree_determined_unify. 3: eapply Hlu'. 1-2: eapply Hit.
Qed.

Lemma tree_access_many_equally_cell C cid tr1 trL
  (Hwf1 : wf_tree tr1) :
  tree_access_all_protected_initialized C cid tr1 = Some trL →
  ∀ tgl it1 itL l, tree_lookup tr1 tgl it1 → tree_lookup trL tgl itL → perm (item_lookup it1 l) = Cell ↔ perm (item_lookup itL l) = Cell.
Proof.
  rewrite /tree_access_all_protected_initialized.
  rewrite /set_fold /=. eapply tree_access_many_equally_cell_1.
  - done.
  - intros tg E (it&Hit&Hprot&HHit)%elem_of_elements%tree_all_protected_initialized_elem_of.
    1: eapply Hit.
    by eapply Hwf1.
Qed.

Lemma tree_access_many_equally_initialized C cid tr1 trL
  (Hwf1 : wf_tree tr1) (Hmi : parents_more_init tr1) :
  tree_access_all_protected_initialized C cid tr1 = Some trL →
  ∀ tgl it1 itL l, tree_lookup tr1 tgl it1 → tree_lookup trL tgl itL → initialized (item_lookup it1 l) = initialized (item_lookup itL l).
Proof.
  rewrite /tree_access_all_protected_initialized.
  rewrite /set_fold /=. eapply tree_access_many_equally_initialized_1.
  - done.
  - done.
  - intros tg E (it&Hit&Hprot&HHit)%elem_of_elements%tree_all_protected_initialized_elem_of.
    2: by eapply Hwf1.
    split. 1: eapply Hit.
    intros z it' [v (Hv&_)%HHit]%elem_of_dom Hlu'.
    enough (it = it') as ->; first done.
    eapply tree_determined_unify. 3: eapply Hlu'. 1-2: eapply Hit.
Qed.

Lemma tree_access_many_equally_active_initialized C cid tr1 trL
  (Hwf1 : wf_tree tr1) (Hmi : parents_more_init tr1) (Hma : parents_more_active tr1) (Hnac : no_active_cousins C tr1) :
  cid ∈ C →
  tree_access_all_protected_initialized C cid tr1 = Some trL →
  ∀ tgl it1 itL l, tree_lookup tr1 tgl it1 → tree_lookup trL tgl itL → (item_lookup it1 l) = mkPerm PermInit Active ↔ (item_lookup itL l) = mkPerm PermInit Active.
Proof.
  intros Hc.
  rewrite /tree_access_all_protected_initialized.
  rewrite /set_fold /=. eapply tree_access_many_equally_active_initialized_1. 1-4: done.
  intros tg E (it&Hit&Hprot&HHit)%elem_of_elements%tree_all_protected_initialized_elem_of.
  2: by eapply Hwf1.
  exists it. split; first done.
  split. 1: by exists cid.
  intros z v (H1&Hnc&H2)%HHit.
  destruct (item_lookup it z) as (ii&pp). exists pp.
  simpl in *. subst ii. split; first done. split; first done.
  intros ->%H2. done.
Qed.

Lemma protector_is_inactive_cids_mono
  {prot C C'}
  (Decr : C' ⊆ C)
  (Dis : ~protector_is_active prot C)
  : ~protector_is_active prot C'.
Proof.
  intro H.
  apply Dis.
  destruct H as [x [H H']].
  exists x.
  split; first assumption.
  unfold call_is_active in *.
  set_solver.
Qed.

Lemma tree_get_all_protected_initialized_idemp C cid tr tr'
  (Hwf1 : wf_tree tr) (Hmi : parents_more_init tr) (Hma : parents_more_active tr) (Hnac : no_active_cousins C tr) :
  cid ∈ C →
  tree_access_all_protected_initialized C cid tr = Some tr' →
  tree_get_all_protected_tags_initialized_locs cid tr = tree_get_all_protected_tags_initialized_locs cid tr'.
Proof.
  intros Hcc Hacc.
  assert (wf_tree tr') as Hwf2.
  { eapply preserve_tag_count_wf. 1: eapply tree_access_many_helper_1. 1: exact Hwf1. 1: apply Hacc. }
  assert (parents_more_init tr') as Htr2.
  { eapply tree_access_all_protected_initialized_more_init; last done. all: done. }
  assert (parents_more_active tr') as Htract2.
  { eapply tree_access_all_protected_initialized_more_active; last done. all: done. }
  assert (no_active_cousins C tr') as Htrcous2.
  { eapply tree_access_all_protected_initialized_no_cousins; last done. all: done. }
  eapply gset_leibniz.
  assert (∀ tg, tree_unique tg tr ↔ tree_unique tg tr') as Htransfer.
  { intros tg. rewrite /tree_unique. split; intros <-. 1:symmetry.
    all: eapply tree_access_many_helper_1; exact Hacc. }
  opose proof (tree_access_many_preserve_protector _ _ _ _ _ Hacc) as Hproteq. 1: done.
  opose proof (tree_access_many_equally_initialized _ _ _ _ _ _ Hacc) as Hiniteq. 1-2: done.
  opose proof (tree_access_many_equally_cell _ _ _ _ _ Hacc) as Hcelleq. 1: done.
  opose proof (tree_access_many_equally_active_initialized _ _ _ _ _ _ _ _ _ Hacc) as Hacteq. 1-5: done.
  intros [tg E]; split; (intros (it&Hit&Hprot&HH)%tree_all_protected_initialized_elem_of; last done);
    (eapply tree_all_protected_initialized_elem_of; first done).
  - assert (tree_unique tg tr') as (it'&Hit')%unique_implies_lookup.
    1: eapply Htransfer, Hwf1, Hit.
    exists it'; split; first done.
    erewrite <-Hproteq. 3: done. 2: done.
    split; first done.
    intros z v.
    specialize (Hiniteq _ _ _ z Hit Hit'). rewrite -Hiniteq.
    specialize (Hacteq _ _ _ z Hit Hit').
    specialize (Hcelleq _ _ _ z Hit Hit').
    setoid_rewrite HH. split; intros (Hini&Hncell&Hact); (split; last split). 1,4: done.
    1: by rewrite -Hcelleq. 2: by rewrite Hcelleq. 
    all: setoid_rewrite Hact.
    all: destruct (item_lookup it z) as [ini1 pp1], (item_lookup it' z) as [ini2 pp2]; simpl in *; subst ini1 ini2. 
    all: split; intros ->; destruct Hacteq as [HX1 HX2]; try specialize (HX1 eq_refl); try specialize (HX2 eq_refl); by simplify_eq.
  - assert (tree_unique tg tr) as (it'&Hit')%unique_implies_lookup.
    1: eapply Htransfer, Hwf2, Hit.
    exists it'; split; first done.
    erewrite Hproteq. 3: done. 2: done.
    split; first done.
    intros z v.
    specialize (Hiniteq _ _ _ z Hit' Hit). rewrite Hiniteq.
    specialize (Hacteq _ _ _ z Hit' Hit).
    specialize (Hcelleq _ _ _ z Hit' Hit).
    setoid_rewrite HH. split; intros (Hini&Hncell&Hact); (split; last split). 1,4: done.
    1: by rewrite Hcelleq. 2: by rewrite -Hcelleq. 
    all: setoid_rewrite Hact.
    all: destruct (item_lookup it z) as [ini1 pp1], (item_lookup it' z) as [ini2 pp2]; simpl in *; subst ini1 ini2. 
    all: split; intros ->; destruct Hacteq as [HX1 HX2]; try specialize (HX1 eq_refl); try specialize (HX2 eq_refl); by simplify_eq.
Qed.

Lemma tree_equal_remove_call C tr1' tr2' tr1 tr2 cid nxtp nxtc :
  wf_tree tr1 → wf_tree tr2 → parents_more_init tr1 → parents_more_init tr2 →
  tree_items_compat_nexts tr1 nxtp nxtc →
  tree_items_compat_nexts tr2 nxtp nxtc →
  parents_more_active tr1 → parents_more_active tr2 →
  no_active_cousins C tr1 → no_active_cousins C  tr2 →
  protected_parents_not_disabled C tr1 → protected_parents_not_disabled C tr2 →
  cid ∈ C →
  tree_access_all_protected_initialized C cid tr1 = Some tr1' →
  tree_access_all_protected_initialized C cid tr2 = Some tr2' →
  tree_equal C Forwards tr1' tr2' →
  tree_equal (C ∖ {[ cid ]}) Forwards tr1' tr2'.
Proof.
  intros Hwf1 Hwf2 Hpmi1 Hpmi2 Hic1 Hic2 Hpma1 Hpma2 Hnac1 Hnac2 Hpnd1 Hpnd2 Hcid Hrai1 Hrai2 (He1&He2&He3).
  split_and!; try done.
  intros tg Hcont. pose proof (He3 tg Hcont) as (it1 & it2 & Hlu1 & Hlu2 & Hutc).
  do 2 eexists. split_and!; try done.
  specialize (tree_access_many_pseudo_confl_becomes_real _ _ _ _ Hwf1 Hrai1 tg it1) as Hrai1'.
  specialize (tree_access_many_pseudo_confl_becomes_real _ _ _ _ Hwf2 Hrai2 tg it2) as Hrai2'.
  specialize (tree_access_many_pseudo_dis_becomes_real _ _ _ _ _ _ Hwf1 Hic1 Hrai1) as HraiD1'.
  specialize (tree_access_many_pseudo_dis_becomes_real _ _ _ _ _ _ Hwf2 Hic2 Hrai2) as HraiD2'.
  erewrite tree_get_all_protected_initialized_idemp in Hrai1'. 7: done. 2-6: done.
  erewrite tree_get_all_protected_initialized_idemp in Hrai2'. 7: done. 2-6: done.
  erewrite tree_get_all_protected_initialized_idemp in HraiD1'. 7: done. 2-6: done.
  erewrite tree_get_all_protected_initialized_idemp in HraiD2'. 7: done. 2-6: done.

  eapply preserve_tag_count_wf in Hwf1 as Hwf1'. 3: done. 2: eapply tree_access_all_protected_initialized_tag_count.
  eapply preserve_tag_count_wf in Hwf2 as Hwf2'. 3: done. 2: eapply tree_access_all_protected_initialized_tag_count.
  eapply tree_access_all_protected_initialized_more_init in Hpmi1 as Hpmi1'. 2-3: done.
  eapply tree_access_all_protected_initialized_more_init in Hpmi2 as Hpmi2'. 2-3: done.
  eapply tree_access_all_protected_initialized_more_active in Hpma1 as Hpma1'. 2-3: done.
  eapply tree_access_all_protected_initialized_more_active in Hpma2 as Hpma2'. 2-3: done.
  eapply tree_access_all_protected_initialized_no_cousins in Hnac1 as Hnac1'. 2-3: done.
  eapply tree_access_all_protected_initialized_no_cousins in Hnac2 as Hnac2'. 2-3: done.
  eapply tree_access_all_protected_initialized_protected_not_disabled in Hpnd1 as Hpnd1'. 2-4: done.
  eapply tree_access_all_protected_initialized_protected_not_disabled in Hpnd2 as Hpnd2'. 2-4: done.
  eapply tree_access_all_protected_initialized_compat_nexts in Hic1 as Hic1'. specialize (Hic1' Hrai1).
  eapply tree_access_all_protected_initialized_compat_nexts in Hic2 as Hic2'. specialize (Hic2' Hrai2).

  intros l. specialize (Hutc l) as (Hproteq&Hutc).
  split; first done.

  inversion Hutc as [
    x1 x2 Hlu
    |ini confl1 confl2 (cc&Hcc&Hccact) Hpc1 Hpc2 Heqi1 Heqi2
    |ini confl1 confl2 Hnprot
    |lp1 lp2 HH1 HH2 Heqi1 Heqi2
    |wit_tg X1 X2 Hdip1 Hdip2 Hinieq
    |
    |p1 p2 ini HH Heq1 Heq2
  ]; simplify_eq.
  - econstructor 1.
  - destruct (decide (cc = cid)) as [<-|Hne].
    + econstructor 3. intros (cc'&Hcc'&Hccact').
      rewrite /protector_is_for_call in Hcc,Hcc'. rewrite Hcc in Hcc'. injection Hcc' as ->.
      eapply elem_of_difference in Hccact' as (_&H).
      setoid_rewrite not_elem_of_singleton in H. done.
    + econstructor 2.
      * exists cc. split; first done.
        rewrite /call_is_active. set_solver.
      * inversion Hpc1 as [|tg_cs it_cs Hreldec Hlucs (cccs&Hp1cs&Hp2cs) Hpermcs Hinitcs Heq]; first by econstructor.
        simplify_eq.
        destruct (decide (cccs = cid)) as [<-|Hnecs].
        2: econstructor 2; try done; exists cccs; split; try done.
        2: rewrite /call_is_active in Hp2cs|-*; set_solver.
        exfalso. enough (ResActivable = ResConflicted) by done.
        eapply Hrai1'. eexists tg_cs, _.
        split.
        { eapply tree_all_protected_initialized_elem_of. 1: exact Hwf1'.
          exists it_cs. split; first done. split; first done.
          eapply mem_enumerate_initalized. }
        split; first done. split; first by eexists. split; first done.
        eexists it_cs, l. split_and!. 2: done. 2: by rewrite -Heqi1.
        eapply (elem_of_dom_2 _ _ (match perm (item_lookup it_cs l) with Active => AccessWrite | _ => AccessRead end)), mem_enumerate_initalized.
        rewrite -Hinitcs. split; first done.
        destruct (perm (item_lookup it_cs l)); simpl; split; done.
      * inversion Hpc2 as [|tg_cs it_cs Hreldec Hlucs (cccs&Hp1cs&Hp2cs) Hpermcs Hinitcs Heq]; first by econstructor.
        simplify_eq.
        destruct (decide (cccs = cid)) as [<-|Hnecs].
        2: econstructor 2; try done; exists cccs; split; try done.
        2: rewrite /call_is_active in Hp2cs|-*; set_solver.
        exfalso. enough (ResActivable = ResConflicted) by done.
        eapply Hrai2'. eexists tg_cs, (mem_enumerate_sat _ (iperm it_cs)).
        split.
        { eapply tree_all_protected_initialized_elem_of. 1: exact Hwf2'.
          exists it_cs. split; first done. split; first done.
          eapply mem_enumerate_initalized. }
        split; first done. rewrite Hproteq in Hcc. split; first by eexists. split; first done.
        eexists it_cs, l. split_and!. 2: done. 2: by rewrite -Heqi2.
        eapply (elem_of_dom_2 _ _ (match perm (item_lookup it_cs l) with Active => AccessWrite | _ => AccessRead end)), mem_enumerate_initalized.
        rewrite -Hinitcs. split; first done.
        destruct (perm (item_lookup it_cs l)); simpl; split; done.
  - econstructor 3.
    intros (cc&Hcc&Hccact). eapply Hnprot. eexists. split; first done. by eapply elem_of_difference in Hccact as (H1&H2).
  - econstructor 4.
    + inversion HH1 as [|tg_cs it_cs lpX protX Hreldec Hlucs (cccs&Hp1cs&Hp2cs) Hpermcs HIMcs Heq1 Heq2]; first by econstructor.
      simplify_eq.
      destruct (decide (cccs = cid)) as [<-|Hnecs].
      2: econstructor 2; try done; exists cccs; split; try done.
      2: rewrite /call_is_active in Hp2cs|-*; set_solver.
      enough (lp1 = Disabled) as -> by econstructor 1.
      eapply HraiD1'. eexists tg_cs, _.
      split.
      { eapply tree_all_protected_initialized_elem_of. 1: exact Hwf1'.
        exists it_cs. split; first done. split; first done.
        eapply mem_enumerate_initalized. }
      split; first exact Hlu1. split; first done. exists it_cs, l.
      split. 2: { split; first done. split; first by eexists. done. }
      eapply mem_enumerate_initalized. rewrite Hpermcs. done.
    + inversion HH2 as [|tg_cs it_cs lpX protX Hreldec Hlucs (cccs&Hp1cs&Hp2cs) Hpermcs HIMcs Heq1 Heq2]; first by econstructor.
      simplify_eq.
      destruct (decide (cccs = cid)) as [<-|Hnecs].
      2: econstructor 2; try done; exists cccs; split; try done.
      2: rewrite /call_is_active in Hp2cs|-*; set_solver.
      enough (lp2 = Disabled) as -> by econstructor 1.
      eapply HraiD2'. eexists tg_cs, _.
      split.
      { eapply tree_all_protected_initialized_elem_of. 1: exact Hwf2'.
        exists it_cs. split; first done. split; first done.
        eapply mem_enumerate_initalized. }
      split; first exact Hlu2. split; first done. exists it_cs, l.
      split. 2: { split; first done. split; first by eexists. done. }
      eapply mem_enumerate_initalized. rewrite Hpermcs. done.
  - econstructor 5.
    + inversion Hdip1 as [wit_it incl Hclid Hlu Hdis].
      econstructor. 1-2: done.
      inversion Hdis as [X1 Hinitdis X2|lp X1 Hpdis Hlulp X2]; simplify_eq.
      1: econstructor 1. econstructor 2.
      inversion Hpdis as [|tg_cs it_cs lpX protX Hreldec Hlucs (cccs&Hp1cs&Hp2cs) Hpermcs HIMcs Heq1 Heq2]; first econstructor 1. simplify_eq.
      destruct (decide (cccs = cid)) as [<-|Hnecs].
      2: econstructor 2; try done; exists cccs; split; try done.
      2: rewrite /call_is_active in Hp2cs|-*; set_solver.
      enough (lp = Disabled) as -> by econstructor 1.
      eapply HraiD1'. eexists tg_cs, _.
      split.
      { eapply tree_all_protected_initialized_elem_of. 1: exact Hwf1'.
        exists it_cs. split; first done. split; first done.
        eapply mem_enumerate_initalized. }
      split; first exact Hlu. split; first done. exists it_cs, l.
      split. 2: { split; first done. split; first by eexists. done. }
      eapply mem_enumerate_initalized. rewrite Hpermcs. done.
    + inversion Hdip2 as [wit_it incl Hclid Hlu Hdis].
      econstructor. 1-2: done.
      inversion Hdis as [X1 Hinitdis X2|lp X1 Hpdis Hlulp X2]; simplify_eq.
      1: econstructor 1. econstructor 2.
      inversion Hpdis as [|tg_cs it_cs lpX protX Hreldec Hlucs (cccs&Hp1cs&Hp2cs) Hpermcs HIMcs Heq1 Heq2]; first econstructor 1. simplify_eq.
      destruct (decide (cccs = cid)) as [<-|Hnecs].
      2: econstructor 2; try done; exists cccs; split; try done.
      2: rewrite /call_is_active in Hp2cs|-*; set_solver.
      enough (lp = Disabled) as -> by econstructor 1.
      eapply HraiD2'. eexists tg_cs, _.
      split.
      { eapply tree_all_protected_initialized_elem_of. 1: exact Hwf2'.
        exists it_cs. split; first done. split; first done.
        eapply mem_enumerate_initalized. }
      split; first exact Hlu. split; first done. exists it_cs, l.
      split. 2: { split; first done. split; first by eexists. done. }
      eapply mem_enumerate_initalized. rewrite Hpermcs. done.
    + assumption.
    + assumption.
  - econstructor 6.
    all: eassumption.
  - inversion HH as [x H|x H]; simplify_eq.
    + econstructor 7. econstructor. intros (c1&Hc1&HHc1). apply H.
      exists c1. split; try done. rewrite /call_is_active in HHc1|-*. set_solver.
    + destruct H as (c1&Hc1&HHc1).
      destruct (decide (c1 = cid)) as [->|Hne].
      * econstructor 3. intros (c2&Hc2&HHc2). unfold call_is_active in *.
        enough (cid = c2) as -> by set_solver.
        destruct it1 as [? [[]|] ??]; simpl in *; cbv in Hc1,Hc2. all: by simplify_eq.
      * econstructor 7. econstructor.
        exists c1. split; first done. unfold call_is_active in *. set_solver.
Qed.

Lemma trees_equal_remove_call C trs1' trs2' trs1 trs2 cid nxtp nxtc :
  wf_trees trs1 → wf_trees trs2 → each_tree_parents_more_init trs1 → each_tree_parents_more_init trs2 →
  trees_compat_nexts trs1 nxtp nxtc →
  trees_compat_nexts trs2 nxtp nxtc →
  each_tree_parents_more_active trs1 → each_tree_parents_more_active trs2 →
  each_tree_no_active_cousins C trs1 → each_tree_no_active_cousins C  trs2 →
  each_tree_protected_parents_not_disabled C trs1 → each_tree_protected_parents_not_disabled C trs2 →
  cid ∈ C →
  trees_access_all_protected_initialized C cid trs1 = Some trs1' →
  trees_access_all_protected_initialized C cid trs2 = Some trs2' →
  trees_equal C Forwards trs1' trs2' →
  trees_equal (C ∖ {[ cid ]}) Forwards trs1' trs2'.
Proof.
  intros (Hwf1&_) (Hwf2&_) Hpmi1 Hpmi2 Hc1 Hc2 Hpma1 Hpma2 Hnac1 Hnac2 Hpnd1 Hpnd2 Hcc Hread1 Hread2 Heq.
  intros blk. specialize (Heq blk).
  inversion Heq as [tr1 tr2 Heqtr Htr1 Htr2|]; last by econstructor.
  eapply trees_access_all_protected_initialized_backwards in Hread1 as (tr1'&Htr1'&Hread1'); last done.
  eapply trees_access_all_protected_initialized_backwards in Hread2 as (tr2'&Htr2'&Hread2'); last done.
  econstructor. eapply tree_equal_remove_call; [..|done|done|done].
  1: by eapply Hwf1. 1: by eapply Hwf2. 1: by eapply Hpmi1. 1: by eapply Hpmi2. 1: by eapply Hc1. 1: by eapply Hc2.
  1: by eapply Hpma1. 1: by eapply Hpma2. 1: by eapply Hnac1. 1: by eapply Hnac2. 1: by eapply Hpnd1. 1: by eapply Hpnd2. all: done.
Qed.



Lemma disabled_tag_at_remove_call C nxtp nxtc tr1 tr1' cid tg loc :
  wf_tree tr1 → parents_more_init tr1 →
  tree_items_compat_nexts tr1 nxtp nxtc →
  parents_more_active tr1 →
  no_active_cousins C tr1 →
  protected_parents_not_disabled C tr1 →
  cid ∈ C →
  tree_access_all_protected_initialized C cid tr1 = Some tr1' →
  disabled_tag_at C tr1' tg loc →
  disabled_tag_at (C ∖ {[ cid ]}) tr1' tg loc.
Proof.
  intros Hwf1 Hpmi1 Hic1 Hmpa1 Hnac1 Hpnd1 Hcid Hrai1 Hdis.
  specialize (tree_access_many_pseudo_dis_becomes_real _ _ _ _ _ _ Hwf1 Hic1 Hrai1) as HraiD1'.
  erewrite tree_get_all_protected_initialized_idemp in HraiD1'. 7: done. 2-6: done.
  eapply preserve_tag_count_wf in Hwf1 as Hwf1'. 3: done. 2: eapply tree_access_all_protected_initialized_tag_count.
  destruct Hdis as (w&Hdis). exists w.
  inversion Hdis as [it_witness incl H1 H2 H3].
  econstructor. 1: exact H1. 1: exact H2.
  inversion H3 as [pX H4 Hx|pX H4 H5 H6eq]; simplify_eq.
  1: econstructor 1.
  inversion H5 as [x1 x2 x3|lp it Hd1 Hd2 Hd3 Hd4 Hd5 Hd6 Hd7 Hd8 Hd9]; simplify_eq.
  1: econstructor 2; econstructor 1.
  destruct Hd5 as (c'&Hc1&Hc2).
  destruct (decide (c' = cid)) as [<-|Hno]; last first.
  { econstructor 2. econstructor 2. 1: exact Hd3. 1: exact Hd4. 2-4: done.
    exists c'. split; first done. rewrite /call_is_active in Hc2|-*. set_solver. }
  ospecialize (HraiD1' _ _ pX _); last first.
  { econstructor. rewrite HraiD1'. econstructor 1. }
  eexists _, _. split.
  { eapply tree_all_protected_initialized_elem_of. 1: by eapply Hwf1'.
    exists it. do 2 (split; first done). eapply mem_enumerate_initalized. }
  split; first exact H2.
  split; first exact Hd3.
  exists it, loc.
  split_and!.
  - eapply mem_enumerate_sat_elem_of.
    rewrite /item_lookup in Hd6. destruct (iperm it !! loc) as [lpx|] eqn:Heq.
    2: simpl in Hd6; simplify_eq. rewrite Heq. exists lpx. split; first done.
    simpl in Hd6. subst lpx. done.
  - done.
  - exists c'. split; first done. done.
  - done.
  - done.
  - done.
  - done.
Qed.

Lemma disabled_tag_remove_call C nxtp nxtc trs1 trs1' cid tg loc :
  wf_trees trs1 → each_tree_parents_more_init trs1 →
  trees_compat_nexts trs1 nxtp nxtc →
  each_tree_parents_more_active trs1 →
  each_tree_no_active_cousins C trs1 → 
  each_tree_protected_parents_not_disabled C trs1 →
  cid ∈ C →
  trees_access_all_protected_initialized C cid trs1 = Some trs1' →
  disabled_tag C trs1' nxtp tg loc →
  disabled_tag (C ∖ {[ cid ]}) trs1' nxtp tg loc.
Proof.
  intros Hwf1 Hpmi1 Hic1 Hpma1 Hnac1 Hpnd1 Hcid Hrai1 Hdis.
  destruct Hdis as (Hnn&Hdis); split; first done.
  destruct (trs1' !! loc.1) as [tr'|] eqn:Htr'. 2: done.
  eapply trees_access_all_protected_initialized_backwards in Hrai1 as (tr&Htr&Hrai1); last done.
  destruct Hdis as [Hdis|Hdis].
  - left. eapply disabled_tag_at_remove_call. 9: done. 8: done.
    1: by eapply Hwf1. 1: by eapply Hpmi1. 1: by eapply Hic1. 1: by eapply Hpma1.
    1: by eapply Hnac1. 1: by eapply Hpnd1. done.
  - right. done.
Qed.


