From iris.proofmode Require Export proofmode.
From iris.bi.lib Require Import fractional.
From iris.base_logic.lib Require Import ghost_map.
From simuliris.base_logic Require Export gen_sim_prog.
From simuliris.simulation Require Export slsls gen_log_rel.
From simuliris.simulation Require Import lifting.
From simuliris.tree_borrows Require Import tkmap_view.
From simuliris.tree_borrows Require Export defs.
From simuliris.tree_borrows Require Export steps_wf.
From simuliris.tree_borrows Require Import steps_progress.
From simuliris.tree_borrows.trees_equal Require Import trees_equal_base.


Section utils.

  Lemma every_node_iff_every_lookup
    {tr prop}
    (GloballyUnique : forall tg, tree_contains tg tr -> exists it, tree_item_determined tg it tr)
    : every_node prop tr <-> forall tg it, tree_lookup tr tg it -> prop it.
  Proof.
    rewrite every_node_eqv_universal.
    split.
    - intros Every tg it [Ex Unq].
      apply Every.
      eapply exists_node_increasing; [eassumption|].
      eapply every_node_increasing; [eassumption|].
      erewrite every_node_eqv_universal.
      intros. symmetry. auto.
    - intros Lookup it Exists.
      apply (Lookup (itag it)).
      assert (tree_contains it.(itag) tr) as Ex. {
        eapply exists_node_increasing; [eassumption|].
        erewrite every_node_eqv_universal.
        intros. subst. auto.
      }
      destruct (GloballyUnique _ Ex) as [it' Unq'].
      assert (it = it') as Eq. {
        apply (proj1 (every_node_eqv_universal _ _) Unq' it Exists).
        auto.
      }
      rewrite -Eq in Unq'.
      split; assumption.
  Qed.

  Context (C : call_id_set).
  
  Lemma tree_equal_implies_globally_unique_1
    {d tr1 tr2} :
    tree_equal C d tr1 tr2 ->
    forall tg, tree_contains tg tr1 -> exists it, tree_item_determined tg it tr1.
  Proof.
    intros [ExIff [SameRel Lookup]] tg Ex.
    destruct (Lookup _ Ex) as [it1 [it2 [Lookup1 [Lookup2 EqC]]]].
    exists it1.
    apply Lookup1.
  Qed.

  Lemma tree_equal_implies_globally_unique_2
    {d tr1 tr2} :
    tree_equal C d tr1 tr2 ->
    forall tg, tree_contains tg tr2 -> exists it, tree_item_determined tg it tr2.
  Proof.
    intro Eq.
    pose proof (tree_equal_sym _ _ _ Eq) as Eq'.
    revert Eq'.
    apply tree_equal_implies_globally_unique_1.
  Qed.

  Lemma tree_equal_transfer_lookup_1
    {d tr1 tr2 tg it1} :
    tree_equal C d tr1 tr2 ->
    tree_lookup tr1 tg it1 ->
    exists it2,
      tree_lookup tr2 tg it2
      /\ item_eq_up_to_C C tr1 tr2 tg d it1 it2.
  Proof.
    intros [SameTg [SameRel MkLookup]] [Ex1 Unq1].
    destruct (MkLookup _ Ex1) as [it1' [it2 [Lookup1' [Lookup2 EqC']]]].
    assert (it1 = it1') by (eapply tree_determined_unify; [eassumption|apply Unq1|apply Lookup1']).
    subst it1'.
    exists it2.
    split; assumption.
  Qed.

  Lemma tree_equal_transfer_lookup_2
    {d tr1 tr2 tg it2} :
    tree_equal C d tr1 tr2 ->
    tree_lookup tr2 tg it2 ->
    exists it1,
      tree_lookup tr1 tg it1
      /\ item_eq_up_to_C C tr1 tr2 tg d it1 it2.
  Proof.
    intros Eq Lookup2.
    pose proof (tree_equal_sym _ _ _ Eq) as Eq'.
    destruct (tree_equal_transfer_lookup_1 Eq' Lookup2) as [it1 [Lookup1 EqC']].
    exists it1; split; [assumption|].
    rewrite -(direction_flip_inv d).
    apply item_eq_up_to_C_sym.
    assumption.
  Qed.

  Lemma is_Some_ignore_bind
    {X Y} {o : option X} {g : X -> Y} :
    is_Some (o ≫= fun x => Some (g x)) <-> is_Some o.
  Proof.
    destruct o; simpl; split; intro H.
    - auto.
    - auto.
    - inversion H; discriminate.
    - inversion H; discriminate.
  Qed.

  Lemma mutual_parent_child_both_or_neither
    {tg tg' tr} :
    StrictParentChildIn tg tg' tr ->
    StrictParentChildIn tg' tg tr ->
    forall br,
      exists_subtree (eq br) tr ->
      (tree_contains tg (of_branch br) <-> tree_contains tg' (of_branch br)).
  Proof.
    intros Rel Rel' br ExBr.
    destruct (decide (tree_contains tg (of_branch br))) as [Ex|nEx].
    all: destruct (decide (tree_contains tg' (of_branch br))) as [Ex'|nEx'].
    all: try tauto.
    all: exfalso.
    - enough (tree_contains tg' (of_branch br)) by contradiction.
      rewrite /StrictParentChildIn every_subtree_eqv_universal in Rel.
      pose proof (proj1 (exists_node_iff_exists_root _ _) Ex) as WitnessSubtree.
      rewrite exists_subtree_eqv_existential in WitnessSubtree.
      destruct WitnessSubtree as [br' [ExBr' TgRoot]].
      assert (exists_subtree (eq br') tr) as ExBr'' by (eapply exists_subtree_transitive; eauto).
      specialize (Rel br' ExBr'' TgRoot).
      eapply exists_node_transitive.
      + eassumption.
      + simpl in TgRoot.
        destruct br' as [[]]; simpl in *.
        right; right; assumption.
    - enough (tree_contains tg (of_branch br)) by contradiction.
      rewrite /StrictParentChildIn every_subtree_eqv_universal in Rel'.
      pose proof (proj1 (exists_node_iff_exists_root _ _) Ex') as WitnessSubtree.
      rewrite exists_subtree_eqv_existential in WitnessSubtree.
      destruct WitnessSubtree as [br' [ExBr' TgRoot]].
      assert (exists_subtree (eq br') tr) as ExBr'' by (eapply exists_subtree_transitive; eauto).
      specialize (Rel' br' ExBr'' TgRoot).
      eapply exists_node_transitive.
      + eassumption.
      + simpl in TgRoot.
        destruct br' as [[]]; simpl in *.
        right; right; assumption.
  Qed.

  Lemma involution_of_branch
    {X} {data : X} {tr1 tr2}
    : branch data tr1 tr2 = of_branch (data, tr1, tr2).
  Proof. reflexivity. Qed.

  Lemma strict_parent_self_impossible
    {tg tr} :
    tree_contains tg tr ->
    StrictParentChildIn tg tg tr ->
    False.
  Proof.
    intros Ex Strict.
    induction tr as [|? ? IHtr1 ? IHtr2]; [inversion Ex|].
    inversion Strict as [Strict0 [Strict1 Strict2]].
    inversion Ex as [Ex0 | [Ex1 | Ex2]].
    - apply IHtr2.
      + apply Strict0. assumption.
      + assumption.
    - apply IHtr1; assumption.
    - apply IHtr2; assumption.
  Qed.

  Lemma mutual_strict_parent_child_impossible
    {tg tg' tr} :
    tree_contains tg tr ->
    tree_contains tg' tr ->
    StrictParentChildIn tg tg' tr ->
    StrictParentChildIn tg' tg tr ->
    False.
  Proof.
    intros Ex Ex' Rel Rel'.
    enough (StrictParentChildIn tg tg tr).
    + eapply strict_parent_self_impossible.
      * exact Ex.
      * assumption.
    + eapply StrictParentChild_transitive; eassumption.
  Qed.

  Lemma mutual_parent_child_implies_equal
    {tg tg' tr} :
    tree_contains tg tr ->
    tree_contains tg' tr ->
    ParentChildIn tg tg' tr ->
    ParentChildIn tg' tg tr ->
    tg' = tg.
  Proof.
    rewrite /ParentChildIn.
    intros Ex Ex'.
    intros [|StrictRel]; [auto|].
    intros [|StrictRel']; [auto|].
    exfalso.
    eapply mutual_strict_parent_child_impossible.
    + exact Ex.
    + exact Ex'.
    + assumption.
    + assumption.
  Qed.

  Lemma rel_this_antisym
    {tr tg tg'} :
    tree_contains tg tr ->
    tree_contains tg' tr ->
    rel_dec tr tg tg' = Child This -> tg = tg'.
  Proof.
    rewrite /rel_dec.
    remember (decide (ParentChildIn tg tg' tr)) as Rel.
    remember (decide (ParentChildIn tg' tg tr)) as Rel'.
    destruct Rel; destruct Rel'.
    all: try (intro; discriminate).
    intros Ex Ex' _.
    eapply mutual_parent_child_implies_equal; eauto.
  Qed.

  Lemma rel_dec_refl tr tg :
    rel_dec tr tg tg = Child This.
  Proof.
    rewrite /rel_dec.
    rewrite decide_True; [|left; reflexivity].
    rewrite decide_True; [|left; reflexivity].
    reflexivity.
  Qed.

  Lemma child_of_this_is_foreign_for_cousin
    {tr tg_this tg_cous tg_child} :
    tree_unique tg_this tr ->
    tree_unique tg_cous tr ->
    tree_unique tg_child tr ->
    rel_dec tr tg_this tg_cous = Foreign Cousin ->
    (if rel_dec tr tg_child tg_this is Child _ then True else False) ->
    rel_dec tr tg_child tg_cous = Foreign Cousin.
  Proof.
    intros Ex_this Ex_cous Ex_child.
    intros Rel_this_cous Rel_child_this_Foreign.
    destruct (rel_dec _ tg_child _) as [|pos] eqn:Rel_child_this; [contradiction|].
    destruct pos.
    + rewrite /rel_dec in Rel_this_cous, Rel_child_this |- *.
      repeat destruct (decide (ParentChildIn _ _ _)); try discriminate.
      - enough (ParentChildIn tg_this tg_cous tr) by contradiction.
        eapply ParentChild_transitive; eassumption.
      - exfalso.
        eapply cousins_have_disjoint_children with (tg1 := tg_this) (tg2 := tg_cous).
        * eassumption.
        * assumption.
        * assumption.
        * rewrite /rel_dec.
          rewrite decide_False; [|eassumption].
          rewrite decide_False; [|eassumption].
          reflexivity.
        * eassumption.
        * eassumption.
      - enough (ParentChildIn tg_this tg_cous tr) by contradiction.
        eapply ParentChild_transitive; eassumption.
      - reflexivity.
    + rewrite (rel_this_antisym _ _ Rel_child_this); first assumption.
      all: apply unique_exists; assumption.
  Qed.


  (* FIXME: This is a very low level lemma, move this elsewhere ? *)
  Lemma if_fun_absorb_args {X Y} {b : bool} {x : X} {f g : X -> Y} :
    (if b then f else g) x = if b then f x else g x.
  Proof. destruct b; reflexivity. Qed.

  Lemma rel_dec_child_transitive
    {tr tg1 tg2 tg3 incl1 incl2}
    : rel_dec tr tg1 tg2 = Child incl1 ->
      rel_dec tr tg2 tg3 = Child incl2 ->
      exists incl3, rel_dec tr tg1 tg3 = Child incl3.
  Proof.
    intros Rel12 Rel23.
    unfold rel_dec in *.
    destruct (decide (ParentChildIn tg2 tg1 tr)); last congruence.
    destruct (decide (ParentChildIn tg3 tg2 tr)); last congruence.
    assert (ParentChildIn tg3 tg1 tr) by (eapply ParentChild_transitive; eassumption).
    eexists.
    destruct (decide (ParentChildIn tg3 tg1 tr)); last contradiction.
    f_equal.
  Qed.

  Lemma memory_access_same_rel_dec
    {tr tr' acc cids acc_tg range} b
    : memory_access_maybe_nonchildren_only b acc cids acc_tg range tr = Some tr' ->
    forall tg tg', rel_dec tr tg tg' = rel_dec tr' tg tg'.
  Proof. eapply access_same_rel_dec. Qed.

  Lemma most_init_comm {i i'} :
    most_init i i' = most_init i' i.
  Proof.
    unfold most_init.
    repeat case_match; reflexivity.
  Qed.

  Lemma most_init_noop {i} :
    most_init i PermLazy = i.
  Proof.
    unfold most_init.
    case_match; reflexivity.
  Qed.

  Lemma most_init_absorb {i} :
    most_init i PermInit = PermInit.
  Proof.
    unfold most_init.
    case_match; reflexivity.
  Qed.

  Lemma tree_lookup_IsTag tr tg it : tree_lookup tr tg it → IsTag tg it.
  Proof.
    intros (H1 & H2).
    eapply exists_node_eqv_existential in H1 as (it2 & Hit2 & Histag).
    eapply every_node_eqv_universal in H2; last done.
    by rewrite -H2.
  Qed.

  Lemma tree_lookup_unique tr tg it1 it2 : tree_lookup tr tg it1 → tree_lookup tr tg it2 → it1 = it2.
  Proof.
    intros Hlu (H1 & H2).
    eapply every_node_eqv_universal in H2; first apply H2.
    1: by eapply tree_lookup_IsTag.
    eapply exists_determined_exists; first done.
    apply Hlu.
  Qed.

  Lemma parent_has_disabled_perm_is_pseudo_disabled tr tg witness loc : 
    parent_has_perm Disabled tr tg witness loc →
    disabled_in_practice C tr tg witness loc.
  Proof.
    inversion 1 as [it incl H0 H1 H2 H3]; simplify_eq.
    econstructor. 1-2: done.
    destruct (item_lookup it loc); simpl in H2,H3; simplify_eq.
    econstructor 1.
  Qed.

  Lemma if_same_guard_equal
    {P Q : Prop} {T} {x y x' y' : T} `{Decision P} `{Decision Q}
    (Iff : P <-> Q)
    (Ex : x = x')
    (Ey : y = y')
    : (if decide P then x else y) = (if decide Q then x' else y').
  Proof.
    repeat destruct (decide _); tauto.
  Qed.

  Lemma exists_node_to_tree_lookup tr itm
    (GloballyUnique : forall tg, tree_contains tg tr -> tree_unique tg tr) :
    exists_node (eq itm) tr →
    tree_lookup tr (itag itm) itm.
  Proof.
    intros Hexi. assert (tree_contains (itag itm) tr) as Hcontain.
    - eapply exists_node_increasing; first done.
      eapply every_node_eqv_universal; intros ? _ <-. done.
    - split; first done.
      eapply GloballyUnique, unique_lookup in Hcontain as (it2 & Hit2).
      enough (itm = it2) by by subst itm.
      eapply every_node_eqv_universal in Hit2; first eapply Hit2.
      all: done.
  Qed.

  Lemma is_Some_if {A} (P : bool) (s:A) : is_Some (if P then Some s else None) → P.
  Proof.
    destruct P; first done.
    intros (x&[=]).
  Qed.

  Lemma is_Some_if_neg {A} (P : bool) (s:A) : is_Some (if P then None else Some s) → P = false.
  Proof.
    destruct P; last done.
    intros (x&[=]).
  Qed.

  Lemma tree_apply_access_preserves_protector
    {tr tr' tg acc_tg kind range b it it'}
    (Lookup : tree_lookup tr tg it)
    (Lookup' : tree_lookup tr' tg it')
    (Acc : tree_apply_access (maybe_non_children_only b (apply_access_perm kind)) C acc_tg range tr = Some tr')
    : iprot it' = iprot it.
  Proof.
    destruct (apply_access_spec_per_node (proj1 Lookup) (proj2 Lookup) Acc) as [it'' [Spec'' [Ex'' Det'']]].
    symmetry in Spec''.
    destruct (item_apply_access_preserves_metadata it it'' Spec'') as [?[]].
    rewrite (tree_determined_unify (proj1 Lookup') (proj2 Lookup') Det'').
    done.
  Qed.

  Lemma item_wf_item_lookup_active it ev1 ev2 off :
    item_wf it ev1 ev2 →
    perm (item_lookup it off) = Active →
    initialized (item_lookup it off) = PermInit.
  Proof.
    intros Hwf.
    rewrite /item_lookup. destruct (iperm it !! off) as [p|] eqn:Heq.
    - rewrite /=. eapply map_Forall_lookup_1 in Heq. 2: by eapply item_perms_valid. apply Heq.
    - simpl. intros HH. exfalso; by eapply item_default_perm_valid.
  Qed.

  Lemma tree_all_protected_initialized_elem_of cid tr tg lst
    (AllUnique : forall tg, tree_contains tg tr -> tree_unique tg tr) :
    (tg, lst) ∈ tree_get_all_protected_tags_initialized_locs cid tr ↔
    ∃ it, tree_lookup tr tg it ∧ protector_is_for_call cid it.(iprot) ∧
    ∀ z v, lst !! z = Some v ↔ initialized (item_lookup it z) = PermInit ∧ perm (item_lookup it z) ≠ Cell ∧ (v = AccessWrite ↔ perm (item_lookup it z) = Active).
  Proof.
    setoid_rewrite tree_all_protected_initialized_exists_node.
    split.
    - intros (it&Hexit%exists_node_to_tree_lookup&Htg&Hprot&Hinit)%exists_node_eqv_existential. 2: done.
      rewrite Htg in Hexit. by eexists.
    - intros (it&Hit&Hprops). assert (itag it = tg) as <- by by eapply tree_lookup_correct_tag.
      eapply exists_node_eqv_existential. eexists; split; last done.
      by eapply tree_lookup_to_exists_node.
  Qed.

  Lemma parents_not_disabled_child_not_active tr tg1 tg2 it1 it2 off
    (Hwf : wf_tree tr)
    (HPP : parents_more_active tr) :
    tree_lookup tr tg1 it1 →  
    tree_lookup tr tg2 it2 →
    ParentChildIn tg1 tg2 tr →
    perm (item_lookup it1 off) = Disabled →
    perm (item_lookup it2 off) = Active →
    False.
  Proof.
    intros Hl1 Hl2 HPC Hp1 Hp2.
    specialize (HPP tg1). eapply every_child_ParentChildIn in HPP.
    2: done. 2, 4: eapply Hwf. 2,4: eapply Hl1. 2: eapply Hl2. 2: done.
    assert (tg1 = itag it1) as -> by by eapply tree_lookup_correct_tag in Hl1.
    assert (tg2 = itag it2) as -> by by eapply tree_lookup_correct_tag in Hl2.
    eapply every_node_eqv_universal in HPP.
    2: eapply tree_lookup_to_exists_node, Hl2.
    ospecialize (HPP _ _ Hp2). 1: done. destruct HPP; congruence.
  Qed.


End utils.
