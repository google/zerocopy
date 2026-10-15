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
From simuliris.tree_borrows.trees_equal Require Import trees_equal_base random_lemmas trees_equal_more_access trees_equal_preserved_by_access.


Section utils.

  Context (C : call_id_set).

  Lemma trees_equal_same_protector_end_action {tr1 tr2 tg d it1 it2}
    (GloballyUnique1 : forall tg, tree_contains tg tr1 -> tree_unique tg tr1)
    (GloballyUnique2 : forall tg, tree_contains tg tr2 -> tree_unique tg tr2)
    (ProtParentsNonDis : protected_parents_not_disabled C tr2)
    (ActiveCousins : no_active_cousins C tr2) :
    tree_equal C d tr1 tr2 →
    protector_is_active (iprot it1) C →
    tree_lookup tr1 tg it1 →
    tree_lookup tr2 tg it2 →
    ∀ l, protector_end_action (item_lookup it1 l) = protector_end_action (item_lookup it2 l).
  Proof.
    intros (_&_&Heq3) Hprot Hlu1 Hlu2 l.
    odestruct (Heq3 tg _) as (it1'&it2'&Hlu1'&Hlu2'&Heq3'); first by eapply Hlu1.
    eapply tree_lookup_unique in Hlu1'; last exact Hlu1.
    eapply tree_lookup_unique in Hlu2'; last exact Hlu2.
    subst it1' it2'. destruct (Heq3' l) as [H1 H2].
    rewrite H1 in Hprot.
    inversion H2 as [pp1 Heq1 Heq2|ini1 confl1 confl2 HprotX HP1 HP2 Heq1 Heq2|ini1 confl1 confl2 HnoProt|p1 p2 HP1 HP2 Heq1 Heq2|wit_tg lp1 lp2 Hdip1 Hdip2 HiniX Heq1 Heq2 Heq8|ini1 confl1 confl2 wit_tg HF Heq1 Heq2|p1 p2 ini Hd Heq1 Heq2]; simplify_eq.
    - done.
    - done.
    - done.
    - done.
    - rewrite /protector_end_action HiniX. destruct (initialized (item_lookup it2 l)) eqn:Heqini; last done.
      destruct (decide (perm (item_lookup it2 l) = Cell)) as [Hcell|Hncell].
      { rewrite Hcell. eapply Heq1 in Hcell. rewrite Hcell. done. }
      exfalso.
      destruct Hdip2 as [itw incl Hrel Hluw Hdisw].
      destruct (decide (perm (item_lookup itw l) = Disabled)) as [Hdis|Hndis].
      + specialize (ProtParentsNonDis wit_tg l).
        eapply every_child_ParentChildIn in ProtParentsNonDis.
        2: done. 2: eapply GloballyUnique2, Hluw. 2: eapply Hluw. 2: eapply GloballyUnique2, Hlu2.
        2: rewrite /rel_dec in Hrel; by destruct (decide (ParentChildIn wit_tg tg tr2)).
        eapply every_node_iff_every_lookup in ProtParentsNonDis.
        3: exact Hlu2. 2: { intros ??. by eapply unique_lookup, GloballyUnique2. }
        eapply tree_lookup_correct_tag in Hlu2 as Hlu2'. subst tg.
        edestruct (ProtParentsNonDis eq_refl) as [Hnd|Hcell].
        1: done. 1: done. 2: done. done.
      + inversion Hdisw as [pp Heq0|lp prot Hpseudo Heq4 Heq5]. 1: by rewrite -Heq0 in Hndis.
        destruct Hpseudo as [?|tg_cs it_cs ? ? Hrelcs Hlucs Hprotcs Hact HnRIM HnC].
        1: by rewrite -Heq4 in Hndis.
        ospecialize (ActiveCousins _ _ _ _ l Hlu2 Hlucs _ _ _).
        3: by rewrite Hact. 3: done.
        2: { right. rewrite Heqini. split; last done.
             left. split; first done. done. }
        rewrite /rel_dec in Hrel|-*.
        destruct decide as [HPC1|?] in Hrel; try done.
        rewrite decide_False; last first.
        { intros HPC. eapply cousins_have_disjoint_children in Hrelcs.
          5: done. 5: done. 2-4: eapply GloballyUnique2.
          2: eapply Hlu2. 2: eapply Hluw. 2: eapply Hlucs. done. }
        rewrite decide_False //.
        intros HPC. rewrite /rel_dec in Hrelcs.
        destruct decide as [?|HPC2] in Hrelcs; try done.
        destruct decide as [?|HPC3] in Hrelcs; try done.
        eapply HPC3. eapply ParentChild_transitive; done.
    - done.
    - destruct d; inversion Hd; simplify_eq; try done.
      all: rewrite -H1 in Hprot; done.
  Qed.

  Lemma tree_equal_allows_more_deallocation
    {tr1 tr2 acc_tg range}
    (GloballyUnique1 : forall tg, tree_contains tg tr1 -> tree_unique tg tr1)
    (GloballyUnique2 : forall tg, tree_contains tg tr2 -> tree_unique tg tr2)
    (ProtParentsNonDis : protected_parents_not_disabled C tr2)
    (ActiveCousins1 : no_active_cousins C tr1)
    (ActiveCousins2 : no_active_cousins C tr2)
    (ActiveParents1 : parents_more_active tr1)
    (ActiveParents2 : parents_more_active tr2)
    (PMI : parents_more_init tr2) :
    tree_equal C Forwards tr1 tr2 ->
    tree_unique acc_tg tr1 ->
    is_Some (memory_deallocate C acc_tg range tr1) ->
    is_Some (memory_deallocate C acc_tg range tr2).
  Proof.
    intros Heq Hunq (tr1'&(pw1&Hpw1&Htrr%mk_is_Some)%bind_Some).
    pose proof Hpw1 as HH.
    eapply mk_is_Some, tree_equal_allows_more_access in HH as (pw2&Hpw2). 2-8: done.
    assert (wf_tree pw1) as Hwfpw1.
    { eapply preserve_tag_count_wf. 3: exact Hpw1. 2: done. eapply memory_access_tag_count. }
    assert (wf_tree pw2) as Hwfpw2.
    { eapply preserve_tag_count_wf. 3: exact Hpw2. 2: done. eapply memory_access_tag_count. }
    opose proof (tree_equal_preserved_by_memory_access _ _ _ _ _ _ _ _ _ Hpw1 Hpw2) as Heqpw.
    1-7: done. 1: by eapply unique_exists.
    opose proof Heq as (Heq1&Heq2&Heq3).
    assert (parents_more_init pw2).
    { eapply memory_access_compat_parents_more_init. 4: done. 1: done. 2: done.
      1: eapply Heq1, unique_exists; done. }
    assert (protected_parents_not_disabled C pw2).
    { eapply memory_access_compat_parents_not_disabled. 5: done. 1: done. 3: done.
      1: eapply Heq1, unique_exists; done. done. }
    assert (no_active_cousins C pw2).
    { eapply memory_access_compat_no_active_cousins. 4: done. 1: done. 2: done.
      1: eapply Heq1, unique_exists; done. }
    rewrite /memory_deallocate Hpw2 /option_bind //.
    eapply join_success_condition, every_node_map, every_node_eqv_universal.
    intros itm2 Hitm2%exists_node_to_tree_lookup.
    2: { intros ttg Hcont.
         eapply access_preserves_tags, GloballyUnique2 in Hcont.
         2: apply Hpw2. setoid_rewrite <- tree_apply_access_preserve_unique; last apply Hpw2.
         done. }
    assert (tree_contains (itag itm2) pw2) as Hcont by apply Hitm2.
    eapply access_preserves_tags in Hcont as Hcont1. 2: exact Hpw2.
    pose proof Heq as (Hsame&_&Hacc). setoid_rewrite <- Hsame in Hcont1.
    apply Hacc in Hcont1 as (itm1'&itm2'&Hlu1&Hlu2&Hiteq).
    assert (iprot itm2' = iprot itm2) as Hiprot.
    { symmetry. eapply tree_apply_access_preserves_protector. 1-2: done. 1: apply Hpw2. }
    assert (tree_contains (itag itm2) pw1) as (itm1&Hlu1pw)%Hwfpw1%unique_implies_lookup.
    { setoid_rewrite <- access_preserves_tags. 2: apply Hpw1. apply Hlu1. }
    assert (iprot itm1' = iprot itm1) as Hiprot1.
    { symmetry. eapply tree_apply_access_preserves_protector. 1-2: done. 1: apply Hpw1. }
    assert (itag itm1 = itag itm2) as Htageq.
    1: eapply tree_lookup_correct_tag, Hlu1pw.
    eapply join_success_condition in Htrr.
    setoid_rewrite every_node_map in Htrr.
    eapply every_node_eqv_universal in Htrr.
    2: { eapply tree_lookup_to_exists_node. rewrite -Htageq in Hlu1. done. }
    simpl in Htrr. eapply is_Some_if_neg in Htrr.
    destruct (Hiteq 0) as (Hloceq&_). simpl.
    rewrite -!Hiprot -!Hloceq !Hiprot1.
    opose proof (trees_equal_same_protector_end_action _ _ _ _ Heqpw) as Hspea. 1-4: done.
    rewrite !bool_decide_decide in Htrr.
    destruct decide as [Hisprot|] in Htrr.
    2: rewrite bool_decide_false //.
    rewrite bool_decide_true // /=.
    destruct decide as [Hisprot2|] in Htrr.
    2: rewrite bool_decide_false //.
    rewrite bool_decide_true // /=.
    destruct decide as [|Hisatoff] in Htrr; first done.
    rewrite bool_decide_false //.
    intros (off&lp&Hofflp&Hpa)%map_Exists_lookup_1.
    ospecialize (Hspea Hisprot2 Hlu1pw Hitm2 off).
    eapply Hisatoff. rewrite /item_lookup Hofflp /= in Hspea.
    rewrite -Hspea in Hpa.
    destruct (iperm itm1 !! off) as [lp2|] eqn:Heqoff.
    2: { exfalso; eapply is_Some_None; exact Hpa. }
    simpl in Hpa.
    eapply map_Exists_lookup_2. 1: exact Heqoff. done.
  Qed.

End utils.