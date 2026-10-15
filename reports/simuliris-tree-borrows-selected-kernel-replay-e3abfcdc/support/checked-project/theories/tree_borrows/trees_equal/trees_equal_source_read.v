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
     do a spurious read we get a [tree_equal].
     Specifically, it is for source-only spurious reads.
     This means we do not need to prove they succeed, we _get_ this as an assumption.
     All that is necessary in addition is showing that equality is preserved.

     The resulting direction is backwards because we later use the transitivity that has
       new_source =Forwards= old_source =Forwards= old_target,
     but the lemma is stated as old_source =Backwards= new_source for mostly historical reasons
     and laziness.
   *)
  Lemma tree_equal_asymmetric_read_source
    {tr tr' acc_tg range it}
    (GloballyUnique : forall tg, tree_contains tg tr -> tree_unique tg tr)
    :
    (* Accessed tag must be in the tree and protected*)
    tree_lookup tr acc_tg it ->
    tree_equal_asymmetric_read_pre_source tr range it acc_tg ->
    (* Under the above conditions if we do a spurious read and it succeeds
       we get a [tree_equal] on the outcome. *)
    memory_access AccessRead C acc_tg range tr = Some tr' ->
    tree_equal C Backwards tr tr'.
  Proof.
    intros Lkup TreeShapeProper Acc.
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
    destruct (TreeShapeProper _ HinRange) as (Htginit&Htgnondis&Hothers).
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
    destruct (rel_dec tr (itag it) (itag it0)) as [[]|[]] eqn:Hreldec.
    - rewrite /apply_access_perm_inner /= in Inner. rewrite /= most_init_comm /=.
      destruct (item_lookup it0 loc) as [ini [|cfl| | | |]] eqn:Hperm.
      1: { enough (validated = Cell) as -> by econstructor 1. clear -Inner MoreInit. by repeat (case_match; simplify_eq; try done). }
      2,4,5: by (destruct ini, (bool_decide (protector_is_active (iprot it0) C)); simpl in *; simplify_eq; econstructor 1).
      2: { simpl in Hothers. ospecialize (Hothers eq_refl). subst.
           destruct (decide (protector_is_active (iprot it0) C)) as [Hprot|HNoProt].
           - rewrite /= bool_decide_decide decide_True // in MoreInit,Inner. simplify_eq.
           - rewrite /= bool_decide_decide decide_False // in MoreInit,Inner. simplify_eq.
             econstructor 7; econstructor. done. }
      simpl in *.
      destruct cfl.
      { simplify_eq. rewrite !Tauto.if_same in MoreInit. destruct most_init in MoreInit; simplify_eq; econstructor 1. }
      destruct (bool_decide (protector_is_active (iprot it0) C)) eqn:Heq.
      2: { simplify_eq. destruct most_init in MoreInit; simplify_eq; econstructor 1. }
      eapply bool_decide_eq_true_1 in Heq. simplify_eq.
      destruct most_init in MoreInit; simplify_eq; econstructor 7; econstructor; done.
    - rewrite /= most_init_comm /=.
      rewrite /apply_access_perm_inner /= in Inner.
      destruct (item_lookup it0 loc) as [[] [|[]| | | |]] eqn:Hperm, (bool_decide (protector_is_active (iprot it0) C)) eqn:Hprot; simpl in *.
      all: try by (simplify_eq; econstructor 1).
      all: simplify_eq. all: (try by specialize (Hothers eq_refl)).
      2: { econstructor 7; econstructor. by eapply bool_decide_eq_false_1. }
      all: destruct (decide (protector_is_active (iprot it0) C)) as [HProt|HNoProt];
             first (econstructor 7; econstructor; done).
      all: by econstructor 3.
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
      rewrite Htginit /= in MoreInit|-*.
      assert (tmperm = validated) as ->.
      { destruct bool_decide in MoreInit; last by congruence.
        destruct tmperm; congruence. }
      clear MoreInit.
      destruct (item_lookup it0 loc) as [[] pp] eqn:Hperm. 2: done.
      destruct pp; try done. all: repeat (simpl in *; simplify_eq); by econstructor 1.
  Qed.

End utils.
