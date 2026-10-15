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
From simuliris.tree_borrows.trees_equal Require Import trees_equal_base random_lemmas.

Section utils.

Context (C : call_id_set).

  (* Remember that the entire reason we have [trees_equal] in the first place
     is to enable spurious reads. This is the lemma that verifies that after we
     do a spurious read we get a [tree_equal]. A companion lemma (stating
     that under certain circumstances the spurious read will succeed) will be proved
     separately.

     The hypotheses are guided by the optimizations that we want to prove.
     We can't (and don't plan to) do spurious reads anywhere, only on protected
     tags. For now we require that the tag also doesn't have any Active
     children. Both of these can be relaxed slightly, but a more general version
     of this lemma will come only if actually required.

     Because we have nice properties of transitivity and reflexivity of [tree_equal]
     already, the proof can be simplified by only considering the case where
     before the asymmetric read the trees are identical. In other words we're going
     to check that a tree is [tree_equal] to itself after a read. *)
  Lemma tree_equal_asymmetric_read_protected
    {d tr tr' acc_tg range it} (mode:bool)
    (GloballyUnique : forall tg, tree_contains tg tr -> tree_unique tg tr)
    :
    (* Accessed tag must be in the tree and protected*)
    tree_lookup tr acc_tg it ->
    protector_is_active it.(iprot) C ->
    tree_equal_asymmetric_read_pre_protected tr range it acc_tg mode ->
    (* Under the above conditions if we do a spurious read and it succeeds
       we get a [tree_equal] on the outcome. *)
    memory_access AccessRead C acc_tg range tr = Some tr' ->
    tree_equal C d tr tr'.
  Proof.
    intros Lkup Protected TreeShapeProper Acc.
    split; last split.
    { intro tg. eapply access_preserves_tags. eassumption. }
    { intros tg1 tg2. eapply access_same_rel_dec. eassumption. }
    (* That was the easy part, helped by the fact that our initial configuration
       is reflexivity instead of a more general instance of [tree_equal].
       Soon it will get more interesting. *)
    intros tg0 Ex.
    destruct (unique_implies_lookup (GloballyUnique _ Ex)) as [it0 Lookup0].
    exists it0.
    assert (tree_unique tg0 tr') as Unq0'. {
      erewrite <- tree_apply_access_preserve_unique; last eassumption.
      apply GloballyUnique. assumption.
    }
    destruct (apply_access_spec_per_node (proj1 Lookup0) (proj2 Lookup0) Acc) as
        (it0' & it0'Spec & Ex0' & Det0').
    symmetry in it0'Spec.
    exists it0'.
    split; first assumption.
    split; first (split; assumption).
    (* Now down to per-item reasoning *)
    intro loc.
    split; first (eapply item_apply_access_preserves_metadata; eassumption).
    rewrite bind_Some in it0'Spec; destruct it0'Spec as (perms' & perms'Spec & [= <-]).
    pose proof (mem_apply_range'_spec _ _ loc _ _ perms'Spec) as PerLoc.
    clear perms'Spec.
    assert (itag it0 = tg0) by (eapply tree_determined_specifies_tag; eapply Lookup0).
    assert (itag it = acc_tg) by (eapply tree_determined_specifies_tag; eapply Lkup).
    subst.
    (* Finally the reasoning is per-location *)
    destruct (decide _) as [HinRange|?]; last first.
    { rewrite /item_lookup /= PerLoc.
      constructor. }
    destruct (TreeShapeProper _ HinRange) as (Htginit&Htgnondis&Hnotcel&Hothers).
    (* Keep digging until [apply_access_perm_inner] *)
    destruct PerLoc as (perm' & perm'Lookup & perm'Spec).
    pose proof Hothers as Hothers_pure.
    ospecialize (Hothers _ _ Lookup0).
    change (default _ _) with (item_lookup it0 loc) in perm'Spec.
    rewrite {2}/item_lookup perm'Lookup /=.
    rewrite bind_Some in perm'Spec; destruct perm'Spec as (tmperm & Inner & perm'Spec).
    rewrite bind_Some in perm'Spec; destruct perm'Spec as (validated & MoreInit & EqPerm).
    injection EqPerm; clear EqPerm; intros; subst.
    rewrite rel_dec_flip2 in Hothers.
    destruct Hothers as (Hothers&Hspecials).
    destruct (rel_dec tr (itag it) (itag it0)) as [[]|[]] eqn:Hreldec.
    - destruct mode.
      + assert (∃ tg, tree_contains tg tr ∧ rel_dec tr tg (itag it) = Child (Strict Immediate) ∧ ParentChildIn tg (itag it0) tr) as (tgsw & Hin & Hswdec&Hpar).
        { rewrite /rel_dec in Hreldec. destruct decide as [HP|HnP]; try done. destruct decide as [HP|?]; try done.
          destruct HP as [Heq|HSP]. 1: exfalso; eapply HnP; by left.
          eapply immediate_sandwich in HSP as HSP2. 2, 3: eapply GloballyUnique. 2: eapply Lkup.
          destruct HSP2 as (tsw&Htsw&HPC). exists tsw.
          assert (tree_contains tsw tr) as Hcont.
          { eapply contains_child. 1: right; by eapply Immediate_is_StrictParentChild.
            eapply Lkup. }
           split_and!. 1: done. 2: done.
          rewrite /rel_dec decide_True. 
          2: right; by eapply Immediate_is_StrictParentChild.
          rewrite decide_False. 1: by rewrite decide_True.
          intros HH. eapply immediate_parent_not_child. 4: exact HH. 3: done.
          all: eapply GloballyUnique. 1: eapply Lkup. done. }
        assert (∃ itsw, tree_lookup tr tgsw itsw) as (itsw&Hitsw).
        1: eapply unique_implies_lookup, GloballyUnique, Hin.
        specialize (Hothers_pure _ _ Hitsw).
        destruct (apply_access_spec_per_node (proj1 Hitsw) (proj2 Hitsw) Acc) as
        (itsw' & itsw'Spec & Hitsw').
        destruct Hothers_pure as (_&HH). ospecialize (HH _). 1: done.
        eapply (perm_eq_up_to_C_disabled_parent C _ _ _ _ _ _ tgsw). 3: rewrite /= most_init_comm //=.
        * econstructor. 2: done. 1: rewrite /rel_dec decide_True //.
          destruct (item_lookup itsw loc) as [[] pp] eqn:HHH; simpl in *; subst pp.
          1: econstructor 1. econstructor 2. econstructor 1.
        * econstructor. 1: erewrite <- access_same_rel_dec. 2: eassumption. 1: rewrite /rel_dec decide_True //.
          1: exact Hitsw'. symmetry in itsw'Spec.
          eapply bind_Some in itsw'Spec as (psw&Hsw&[= Hitsweq]).
          pose proof (mem_apply_range'_spec _ _ loc _ _ Hsw) as PerLocSW.
          rewrite decide_True // in PerLocSW. destruct PerLocSW as (p & HPP & Hacc).
          rewrite /= /apply_access_perm /apply_access_perm_inner /= in Hacc.
          change (default _ _) with (item_lookup itsw loc) in Hacc.
          assert (itag itsw = tgsw) as <- by by eapply tree_lookup_correct_tag.
          rewrite rel_dec_flip2 Hswdec /= HH /= most_init_comm /= in Hacc.
          rewrite /item_lookup /= -Hitsweq HPP /=.
          destruct (item_lookup itsw loc) as [ini prm] eqn:Heq; simpl in *; subst prm.
          edestruct (bool_decide (protector_is_active (iprot itsw) C)), ini in Hacc; simpl in Hacc; try discriminate Hacc; injection Hacc as <-.
          all: try econstructor 1. all: econstructor 2; econstructor 1.
        * clear -Inner MoreInit. simpl. rewrite /apply_access_perm_inner in Inner.
          repeat (case_match; simplify_eq; simpl; try done).
      + rewrite /apply_access_perm_inner /= in Inner. rewrite /= most_init_comm /=.
        destruct Hspecials as (Hfrz&Hnact).
        destruct (item_lookup it0 loc) as [ini [|cfl| | | |]] eqn:Hperm.
        1,3,5,6: by (destruct ini, (bool_decide (protector_is_active (iprot it0) C)); simpl in *; simplify_eq; econstructor 1).
        2: exfalso; by eapply Hnact.
        simpl in *. assert (∃ cfl', validated = Reserved cfl') as (cfl'&->).
        { destruct ini, cfl, (bool_decide (protector_is_active (iprot it0) C)); simpl in *; eexists; simplify_eq; done. }
        destruct (apply_access_spec_per_node (proj1 Lkup) (proj2 Lkup) Acc) as
        (it' & it'Spec & Hit'). symmetry in it'Spec.
        eapply bind_Some in it'Spec as (pit&Hpit&[= Hiteq]).
        pose proof (mem_apply_range'_spec _ _ loc _ _ Hpit) as PerLoc.
        rewrite decide_True // in PerLoc. destruct PerLoc as (p & HPP & Hacc).
        rewrite /= /apply_access_perm /apply_access_perm_inner /= in Hacc.
        change (default _ _) with (item_lookup it loc) in Hacc.
        assert (itag it' = itag it) as Hit by by eapply tree_lookup_correct_tag.
        rewrite rel_dec_refl Hfrz /= most_init_comm /= in Hacc.
        rewrite Tauto.if_same /= in Hacc. injection Hacc as <-.
        eapply perm_eq_up_to_C_frozen_parent with (witness_tg := itag it). destruct d.
        * econstructor. 1: rewrite rel_dec_flip2 Hreldec //. 1: exact Lkup. 1: done. 1: done.
        * econstructor.
          { erewrite <- access_same_rel_dec. 2: done. rewrite rel_dec_flip2 Hreldec //. }
          { eapply Hit'. }
          all: rewrite /item_lookup -Hiteq /= HPP /= //.
    - rewrite /= most_init_comm /=.
      rewrite /apply_access_perm_inner /= in Inner.
      destruct (item_lookup it0 loc) as [[] [|[]| | | |]] eqn:Hperm, (bool_decide (protector_is_active (iprot it0) C)) eqn:Hprot; simpl in *.
      all: try by (simplify_eq; econstructor 1).
      1-2: simplify_eq; econstructor 2;
            [by eapply bool_decide_eq_true_1| |econstructor 1].
      1-2: eapply (pseudo_conflicted_cousin_init C _ _ _ (itag it) it);
            [rewrite rel_dec_flip2 Hreldec //|done..].
    - destruct Hothers as (Hinit&Hndis).
      rewrite /apply_access_perm_inner /= in Inner.
      destruct (item_lookup it0 loc) as [[] pp] eqn:Hperm. 2: done.
      assert (pp = tmperm) as ->.
      { simpl in *. destruct pp; simplify_eq; done. }
      rewrite /= in MoreInit|-*.
      destruct tmperm, (bool_decide (protector_is_active (iprot it0) C)); simpl in MoreInit.
      all: try done. all: simplify_eq; econstructor 1.
    - simpl in *. assert (itag it = itag it0) as Htageq.
      { rewrite /rel_dec in Hreldec. do 2 (destruct decide; try done).
        eapply mutual_parent_child_implies_equal. 1: done. 1: eapply Lkup. all: done. }
      assert (it = it0) as ->.
      { eapply tree_determined_unify. 1, 2: eapply Lkup. rewrite Htageq. eapply Lookup0. }
      rewrite Htginit in MoreInit|-*.
      rewrite bool_decide_true // /= in MoreInit.
      destruct (item_lookup it0 loc) as [[] pp] eqn:Hperm. 2: done.
      destruct pp; try done. all: repeat (simpl in *; simplify_eq); by econstructor 1.
  Qed.

  Lemma disabled_is_disabled x1 x2 x3 x4 pp : perm pp = Disabled → is_disabled C x1 x2 x3 pp x4.
  Proof.
    destruct pp as [[] pp]; simpl; intros ->.
    1: econstructor 1.
    econstructor 2. econstructor 1.
  Qed.

  Lemma tree_equal_asymmetric_write_protected
    {d tr tr' acc_tg range it}
    (GloballyUnique : forall tg, tree_contains tg tr -> tree_unique tg tr)
    :
    (* Accessed tag must be in the tree and protected*)
    tree_lookup tr acc_tg it ->
    protector_is_active it.(iprot) C ->
    tree_equal_asymmetric_write_pre_protected C tr range it acc_tg ->
    (* Under the above conditions if we do a spurious read and it succeeds
       we get a [tree_equal] on the outcome. *)
    memory_access AccessWrite C acc_tg range tr = Some tr' ->
    tree_equal C d tr tr'.
  Proof.
    intros Lkup Protected TreeShapeProper Acc.
    split; last split.
    { intro tg. eapply access_preserves_tags. eassumption. }
    { intros tg1 tg2. eapply access_same_rel_dec. eassumption. }
    (* That was the easy part, helped by the fact that our initial configuration
       is reflexivity instead of a more general instance of [tree_equal].
       Soon it will get more interesting. *)
    intros tg0 Ex.
    destruct (unique_implies_lookup (GloballyUnique _ Ex)) as [it0 Lookup0].
    exists it0.
    assert (tree_unique tg0 tr') as Unq0'. {
      erewrite <- tree_apply_access_preserve_unique; last eassumption.
      apply GloballyUnique. assumption.
    }
    destruct (apply_access_spec_per_node (proj1 Lookup0) (proj2 Lookup0) Acc) as
        (it0' & it0'Spec & Ex0' & Det0').
    symmetry in it0'Spec.
    exists it0'.
    split; first assumption.
    split; first (split; assumption).
    (* Now down to per-item reasoning *)
    intro loc.
    split; first (eapply item_apply_access_preserves_metadata; eassumption).
    rewrite bind_Some in it0'Spec; destruct it0'Spec as (perms' & perms'Spec & [= <-]).
    pose proof (mem_apply_range'_spec _ _ loc _ _ perms'Spec) as PerLoc.
    clear perms'Spec.
    assert (itag it0 = tg0) by (eapply tree_determined_specifies_tag; eapply Lookup0).
    assert (itag it = acc_tg) by (eapply tree_determined_specifies_tag; eapply Lkup).
    subst.
    (* Finally the reasoning is per-location *)
    destruct (decide _) as [HinRange|?]; last first.
    { rewrite /item_lookup /= PerLoc.
      constructor. }
    destruct (TreeShapeProper _ HinRange) as (Htginit&Htgactive&Hothers).
    (* Keep digging until [apply_access_perm_inner] *)
    destruct PerLoc as (perm' & perm'Lookup & perm'Spec).
    pose proof Hothers as Hothers_pure.
    ospecialize (Hothers _ _ Lookup0).
    change (default _ _) with (item_lookup it0 loc) in perm'Spec.
    rewrite {2}/item_lookup perm'Lookup /=.
    rewrite bind_Some in perm'Spec; destruct perm'Spec as (tmperm & Inner & perm'Spec).
    rewrite bind_Some in perm'Spec; destruct perm'Spec as (validated & MoreInit & EqPerm).
    injection EqPerm; clear EqPerm; intros; subst.
    rewrite rel_dec_flip2 /= in Hothers.
    destruct (rel_dec tr (itag it) (itag it0)) as [[]|[]] eqn:Hreldec; simpl in Hothers.
    - assert (∃ tg, tree_contains tg tr ∧ rel_dec tr tg (itag it) = Child (Strict Immediate) ∧ ParentChildIn tg (itag it0) tr) as (tgsw & Hin & Hswdec&Hpar).
      { rewrite /rel_dec in Hreldec. destruct decide as [HP|HnP]; try done. destruct decide as [HP|?]; try done.
        destruct HP as [Heq|HSP]. 1: exfalso; eapply HnP; by left.
        eapply immediate_sandwich in HSP as HSP2. 2, 3: eapply GloballyUnique. 2: eapply Lkup.
        destruct HSP2 as (tsw&Htsw&HPC). exists tsw.
        assert (tree_contains tsw tr) as Hcont.
        { eapply contains_child. 1: right; by eapply Immediate_is_StrictParentChild.
          eapply Lkup. }
         split_and!. 1: done. 2: done.
        rewrite /rel_dec decide_True. 
        2: right; by eapply Immediate_is_StrictParentChild.
        rewrite decide_False. 1: by rewrite decide_True.
        intros HH. eapply immediate_parent_not_child. 4: exact HH. 3: done.
        all: eapply GloballyUnique. 1: eapply Lkup. done. }
      assert (∃ itsw, tree_lookup tr tgsw itsw) as (itsw&Hitsw).
      1: eapply unique_implies_lookup, GloballyUnique, Hin.
      specialize (Hothers_pure _ _ Hitsw).
      destruct (apply_access_spec_per_node (proj1 Hitsw) (proj2 Hitsw) Acc) as
      (itsw' & itsw'Spec & Hitsw'). rewrite Hswdec /= in Hothers_pure.
      eapply (perm_eq_up_to_C_disabled_parent C _ _ _ _ _ _ tgsw). 3: rewrite /= most_init_comm //=.
      * econstructor. 2: done. 1: rewrite /rel_dec decide_True //.  eapply disabled_is_disabled, Hothers_pure.
      * econstructor. 1: erewrite <- access_same_rel_dec. 2: eassumption. 1: rewrite /rel_dec decide_True //.
        1: exact Hitsw'. symmetry in itsw'Spec.
        eapply bind_Some in itsw'Spec as (psw&Hsw&[= Hitsweq]).
        pose proof (mem_apply_range'_spec _ _ loc _ _ Hsw) as PerLocSW.
        rewrite decide_True // in PerLocSW. destruct PerLocSW as (p & HPP & Hacc).
        rewrite /= /apply_access_perm /apply_access_perm_inner /= in Hacc.
        change (default _ _) with (item_lookup itsw loc) in Hacc.
        assert (itag itsw = tgsw) as <- by by eapply tree_lookup_correct_tag.
        rewrite rel_dec_flip2 Hswdec /= Hothers_pure /= in Hacc.
        rewrite /item_lookup /= -Hitsweq HPP /=.
        repeat (case_match; simpl in *; try done; simplify_eq).
        all: by eapply disabled_is_disabled.
        * clear -Inner MoreInit. simpl. rewrite /apply_access_perm_inner in Inner.
          repeat (case_match; simplify_eq; simpl; try done).
    - rewrite /= most_init_comm /=.
      rewrite /apply_access_perm_inner /= in Inner.
      eapply rel_dec_flip in Hreldec.
      destruct (item_lookup it0 loc) as [[] [|[]| | | |]] eqn:Hperm, (bool_decide (protector_is_active (iprot it0) C)) eqn:Hprot; simpl in *.
      all: try by (simplify_eq; first [done | econstructor 1]).
      all: try by eapply bool_decide_eq_true_1 in Hprot.
      all: injection Inner as <-; injection MoreInit as <-. 
      all: econstructor 4; last econstructor 1.
      all: econstructor 2; [exact Hreldec|exact Lkup|done|destruct (item_lookup it loc); simpl in *; congruence|done|done].
    - destruct Hothers as (Hini&Hact).
      rewrite /apply_access_perm_inner /= in Inner.
      destruct (item_lookup it0 loc) as [ini pp] eqn:Hperm.
      simpl in Hini, Hact. subst ini. simpl in Inner. simplify_eq. simpl in MoreInit.
      destruct (bool_decide (protector_is_active (iprot it0) C)); simpl in MoreInit|-*; simplify_eq.
      all: destruct Hact; simplify_eq; econstructor 1.
    - simpl in *. assert (itag it = itag it0) as Htageq.
      { rewrite /rel_dec in Hreldec. do 2 (destruct decide; try done).
        eapply mutual_parent_child_implies_equal. 1: done. 1: eapply Lkup. all: done. }
      assert (it = it0) as ->.
      { eapply tree_determined_unify. 1, 2: eapply Lkup. rewrite Htageq. eapply Lookup0. }
      rewrite Htginit in MoreInit|-*. rewrite Htgactive in Inner. simplify_eq.
      rewrite bool_decide_true // /= in MoreInit. simplify_eq.
      destruct (item_lookup it0 loc) as [ii pp]. simpl in *; subst ii pp. econstructor 1.
  Qed.

End utils.
