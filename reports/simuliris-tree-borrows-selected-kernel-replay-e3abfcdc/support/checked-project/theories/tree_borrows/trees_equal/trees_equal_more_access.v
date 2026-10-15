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

  Lemma cousin_write_for_initialized_protected_nondisabled_is_ub
    {it l acc_tg tr range tg b}
    (Lookup : tree_lookup tr tg it)
    (Protected : protector_is_active (iprot it) C)
    (IsInit : initialized (item_lookup it l) = PermInit)
    (IsNotCell : perm (item_lookup it l) ≠ Cell)
    (IsCousin : rel_dec tr acc_tg tg = Foreign Cousin)
    (InRange : range'_contains range l)
    : ~ is_Some (tree_apply_access (maybe_non_children_only b (apply_access_perm AccessWrite)) C acc_tg range tr).
  Proof.
    intro Absurd.
    rewrite -apply_access_success_condition in Absurd.
    rewrite every_node_eqv_universal in Absurd.
    specialize (Absurd it).
    assert (itag it = tg) as Tg. { eapply tree_determined_specifies_tag; apply Lookup. }
    rewrite Tg in Absurd.
    rewrite IsCousin in Absurd.
    rewrite /item_apply_access /permissions_apply_range' in Absurd.
    rewrite is_Some_ignore_bind in Absurd.
    rewrite -mem_apply_range'_success_condition in Absurd.
    rewrite bool_decide_eq_true_2 in Absurd; [|auto].
    enough (is_Some (apply_access_perm AccessWrite (Foreign Cousin) true (item_lookup it l))) as Absurd'.
    - rewrite /apply_access_perm in Absurd'.
      destruct (item_lookup _ _) as [[] [|[]| | | |]], b; simpl in Absurd'.
      all: try (clear -IsNotCell; done).
      all: try inversion Absurd'; discriminate.
    - rewrite /item_lookup. setoid_rewrite maybe_non_children_only_no_effect in Absurd; last done.
      apply Absurd; [|done].
      eapply exists_determined_exists; apply Lookup.
  Qed.

  Lemma pseudo_conflicted_allows_more_access
    {tr1 tr2 tg l confl1 confl2 kind rel isprot ini acc_tg range it1 b}
    (* Main hypotheses *)
    (Confl1 : pseudo_conflicted C tr1 tg l confl1)
    (Confl2 : pseudo_conflicted C tr2 tg l confl2)
    (AccEx : tree_unique acc_tg tr1)
    (TgEx : tree_unique tg tr1)
    (* Auxiliary stuff to bind the local access to the global success for the pseudo conflicted case *)
    (GloballyUnique1 : forall tg, tree_contains tg tr1 -> tree_unique tg tr1)
    (GlobalSuccess : is_Some (tree_apply_access (maybe_non_children_only b (apply_access_perm kind)) C acc_tg range tr1))
    (ProtSpec : isprot = bool_decide (protector_is_active (iprot it1) C))
    (RelSpec : rel = rel_dec tr1 acc_tg tg)
    (PermSpec : item_lookup it1 l = {| initialized := ini; perm := Reserved confl1 |})
    (InRange : range'_contains range l)
    : is_Some
         (apply_access_perm kind rel isprot
            {| initialized := ini; perm := Reserved confl1 |})
    -> is_Some
         (apply_access_perm kind rel isprot
            {| initialized := ini; perm := Reserved confl2 |}).
  Proof.
    rewrite /apply_access_perm /apply_access_perm_inner; simpl.
    (* Most cases are by reflexivity. *)
    destruct kind, rel; simpl.
    all: destruct ini, isprot; simpl; try auto.
    all: inversion Confl1 as [|?? RelCous LookupCous].
    all: inversion Confl2.
    all: subst; simpl; try auto.
    (* Once we get reflexivity out of the way we are left with the accesses
       where there is UB in the target because of the conflicted.
       We now need to prove that actually there is also UB in the source,
       just not _here_, instead it occured at the cousin that creates the conflict. *)
    all: exfalso.
    all: eapply cousin_write_for_initialized_protected_nondisabled_is_ub.
    all: try exact GlobalSuccess.
    all: try eassumption.
    all: eapply child_of_this_is_foreign_for_cousin.
    all: try apply RelCous.
    all: try assumption.
    all: try rewrite -RelSpec; auto.
    all: apply GloballyUnique1; apply LookupCous.
  Qed.

  Lemma pseudo_conflicted_post_prot_allows_more_access
    {tr1 tg l confl1 confl2 kind rel isprot ini acc_tg range it1 b}
    (* Main hypotheses *)
    (AccEx : tree_unique acc_tg tr1)
    (TgEx : tree_unique tg tr1)
    (* Auxiliary stuff to bind the local access to the global success for the pseudo conflicted case *)
    (GloballyUnique1 : forall tg, tree_contains tg tr1 -> tree_unique tg tr1)
    (GlobalSuccess : is_Some (tree_apply_access (maybe_non_children_only b (apply_access_perm kind)) C acc_tg range tr1))
    (NoProp : ¬ protector_is_active (iprot it1) C)
    (ProtSpec : isprot = bool_decide (protector_is_active (iprot it1) C))
    (RelSpec : rel = rel_dec tr1 acc_tg tg)
    (PermSpec : item_lookup it1 l = {| initialized := ini; perm := Reserved confl1 |})
    (InRange : range'_contains range l)
    : is_Some
         (apply_access_perm kind rel isprot
            {| initialized := ini; perm := Reserved confl1 |})
    -> is_Some
         (apply_access_perm kind rel isprot
            {| initialized := ini; perm := Reserved confl2 |}).
  Proof.
    rewrite /apply_access_perm /apply_access_perm_inner; simpl.
    rewrite bool_decide_false in ProtSpec; last done. subst isprot.
    (* Most cases are by reflexivity. *)
    destruct kind, rel; simpl.
    all: destruct ini; simpl; try auto.
    all: subst; simpl; try auto.
    all: destruct confl1, confl2.
    all: subst; simpl; try auto.
  Qed.

  Lemma pseudo_disabled_allows_more_access
    {tr1 tr2 tg l p1 p2 kind rel isprot acc_tg range it1 b}
    (* Main hypotheses *)
    (Confl1 : pseudo_disabled C tr1 tg l p1 (iprot it1))
    (Confl2 : pseudo_disabled C tr2 tg l p2 (iprot it1))
    (AccEx : tree_unique acc_tg tr1)
    (TgEx : tree_unique tg tr1)
    (* Auxiliary stuff to bind the local access to the global success for the pseudo conflicted case *)
    (GloballyUnique1 : forall tg, tree_contains tg tr1 -> tree_unique tg tr1)
    (GlobalSuccess : is_Some (tree_apply_access (maybe_non_children_only b (apply_access_perm kind)) C acc_tg range tr1))
    (ProtSpec : isprot = bool_decide (protector_is_active (iprot it1) C))
    (RelSpec : rel = rel_dec tr1 acc_tg tg)
    (PermSpec : item_lookup it1 l = {| initialized := PermLazy; perm := p1 |})
    (InRange : range'_contains range l)
    : is_Some
         (apply_access_perm kind rel isprot
            {| initialized := PermLazy; perm := p1 |})
    -> is_Some
         (apply_access_perm kind rel isprot
            {| initialized := PermLazy; perm := p2 |}).
  Proof.
    rewrite /apply_access_perm /apply_access_perm_inner; simpl.
    destruct rel; last first.
    - inversion Confl1 as [H1 H2|tg_cs it_cs X1 X2 Hcs Hlu Hluact Hpp XX X3]; simplify_eq.
      1: destruct kind; simpl; intros [? [=]].
      exfalso. eapply apply_access_success_condition in GlobalSuccess.
      eapply every_node_eqv_universal in GlobalSuccess.
      2: eapply tree_lookup_to_exists_node, Hlu.
      rewrite /item_apply_access /permissions_apply_range' in GlobalSuccess.
      erewrite is_Some_ignore_bind in GlobalSuccess.
      eapply mem_apply_range'_success_condition in GlobalSuccess.
      2: exact InRange.
      rewrite /rel_dec in GlobalSuccess.
      assert (itag it_cs = tg_cs) as Hcstg by by eapply tree_lookup_correct_tag.
      rewrite decide_False in GlobalSuccess.
      2: { intros HPC. eapply cousins_have_disjoint_children.
           4: exact Hcs. 2: done. 1: exact AccEx.
           1: eapply GloballyUnique1, Hlu. 2: by subst.
           rewrite /rel_dec in RelSpec. destruct decide in RelSpec; done. }
      rewrite decide_False in GlobalSuccess.
      2: { intros HPC. rewrite /rel_dec in RelSpec Hcs.
           destruct decide as [HP1|?] in RelSpec; try done.
           destruct decide as [?|HnP1] in Hcs; try done.
           destruct decide as [?|HnP2] in Hcs; try done.
           eapply HnP2. eapply ParentChild_transitive.
           1: exact HP1. subst. done. }
      rewrite /item_lookup in Hpp.
      rewrite Hpp bool_decide_true // in GlobalSuccess.
      rewrite maybe_non_children_only_no_effect // in GlobalSuccess.
      destruct kind; destruct GlobalSuccess as [x [=]].
    - rewrite /=. intros _. destruct kind, isprot, p2 as [|[]| | | |]; simpl; done.
  Qed.

  Lemma frozen_in_practice_rejects_child_write
    {tr tg witness l b acc_tg range}
    (InRange : range'_contains range l)
    (GloballyUnique : forall tg, tree_contains tg tr -> tree_unique tg tr)
    (Frz : frozen_in_practice tr tg witness l)
    (Acc : is_Some (tree_apply_access (maybe_non_children_only b (apply_access_perm AccessWrite)) C acc_tg range tr))
    (Rel : exists x, rel_dec tr acc_tg tg = Child x)
    : False.
  Proof.
    inversion Frz as [it_witness ? Rel' Lkup Perm].
    rewrite -apply_access_success_condition in Acc.
    rewrite every_node_iff_every_lookup in Acc. 2: {
      intros tg0 Ex0. apply unique_lookup. apply GloballyUnique. assumption.
    }
    specialize (Acc _ _ Lkup).
    assert (exists x, rel_dec tr acc_tg witness = Child x) as FullRel. 1: {
      destruct Rel as [? Rel].
      eapply rel_dec_child_transitive; eassumption.
    }
    destruct FullRel as [? FullRel].
    assert (itag it_witness = witness) as WitnessTg. {
      eapply tree_determined_specifies_tag; apply Lkup.
    }
    rewrite WitnessTg FullRel in Acc.
    unfold item_apply_access, maybe_non_children_only in Acc.
    unfold is_Some in Acc.
    destruct Acc as [? Acc].
    rewrite bind_Some in Acc.
    destruct Acc as [? [Acc Res]].
    injection Res; clear Res; intros; subst.
    unfold permissions_apply_range' in Acc.
    pose proof (mk_is_Some _ _ Acc) as AccSome; clear Acc.
    rewrite -mem_apply_range'_success_condition in AccSome.
    specialize (AccSome l InRange).
    do 4 rewrite if_fun_absorb_args in AccSome.
    unfold nonchildren_only in AccSome.
    rewrite Tauto.if_same in AccSome.
    unfold apply_access_perm, apply_access_perm_inner in AccSome.
    rewrite Perm in AccSome.
    simpl in AccSome.
    inversion AccSome; congruence.
  Qed.

  Lemma loc_eq_up_to_C_allows_more_access
    {d tr1 tr2 tg it1 it2 l kind acc_tg range b}
    (Tg1 : itag it1 = tg)
    (Tg2 : itag it2 = tg)
    (UnqAcc : tree_unique acc_tg tr1)
    (UnqAcc2 : tree_unique acc_tg tr2)
    (Ex1 : tree_unique tg tr1)
    (Ex2 : tree_lookup tr2 tg it2)
    (SameRel : forall tg tg', rel_dec tr1 tg tg' = rel_dec tr2 tg tg')
    (ProtParentsNonDis : protected_parents_not_disabled C tr2)
    (ParentsMoreInit : parents_more_init tr2)
    (GlobalSuccess : is_Some (tree_apply_access (maybe_non_children_only b (apply_access_perm kind)) C acc_tg range tr1))
    (GloballyUnique1 : forall tg, tree_contains tg tr1 -> tree_unique tg tr1)
    (GloballyUnique2 : forall tg, tree_contains tg tr2 -> tree_unique tg tr2)
    (InRange : range'_contains range l)
    (Hrestrict : kind = AccessWrite → d = Forwards)
    :
    loc_eq_up_to_C C tr1 tr2 tg d it1 it2 l ->
    is_Some (maybe_non_children_only b (apply_access_perm kind) (rel_dec tr1 acc_tg (itag it1))
            (bool_decide (protector_is_active (iprot it1) C))
            (item_lookup it1 l))
    ->
    is_Some (maybe_non_children_only b (apply_access_perm kind) (rel_dec tr2 acc_tg (itag it2))
     (bool_decide (protector_is_active (iprot it2) C))
     (item_lookup it2 l)).
  Proof.
    intros EqC Acc1.
    inversion EqC as [EqProt EqCLookup].
    inversion EqCLookup as
      [perm Lookup EqLookup
      |??? Prot Confl1 Confl2 Lookup1 Lookup2
      |??? Prot Lookup1 Lookup2
      |p1 p2 Confl1 Confl2 Lookup1 Lookup2
      |witness_tg ?? Dis1 Dis2 Lookup1 Lookup2 NotCell
      |ini ?? witness_tg Frz Lookup1 Lookup2
      |p1 p2 ini Hd Lookup1 Lookup2
    ].
    - rewrite Tg2 -Tg1.
      rewrite -SameRel.
      rewrite -EqProt.
      apply Acc1.
    - rewrite Lookup2.
      rewrite -Lookup1 in Acc1.
      edestruct maybe_non_children_only_effect_or_nop as [Heq|Heq].
      2: by erewrite Heq.
      rewrite Heq. rewrite -Lookup2.
      eapply (pseudo_conflicted_allows_more_access Confl1 Confl2 UnqAcc Ex1 GloballyUnique1 GlobalSuccess).
      + rewrite -EqProt; reflexivity.
      + rewrite SameRel -Tg2 //=.
      + rewrite /item_lookup Lookup1 //=.
      + exact InRange.
      + rewrite Tg1 -Tg2 SameRel EqProt Heq // in Acc1.
    - rewrite Lookup2.
      rewrite -Lookup1 in Acc1.
      edestruct maybe_non_children_only_effect_or_nop as [Heq|Heq].
      2: by erewrite Heq.
      rewrite Heq. rewrite -Lookup2.
      eapply (pseudo_conflicted_post_prot_allows_more_access UnqAcc Ex1 GloballyUnique1 GlobalSuccess).
      + done.
      + rewrite -EqProt; reflexivity.
      + rewrite SameRel -Tg2 //=.
      + symmetry. apply Lookup1.
      + exact InRange.
      + rewrite Tg1 -Tg2 SameRel EqProt Heq // in Acc1.
    - rewrite Lookup2.
      rewrite -Lookup1 in Acc1.
      edestruct maybe_non_children_only_effect_or_nop as [Heq|Heq].
      2: by erewrite Heq.
      rewrite Heq. rewrite -Lookup2.
      eapply (pseudo_disabled_allows_more_access Confl1 Confl2 UnqAcc Ex1 GloballyUnique1 GlobalSuccess).
      + rewrite -EqProt; reflexivity.
      + rewrite SameRel -Tg2 //=.
      + rewrite /item_lookup Lookup1 //=.
      + exact InRange.
      + rewrite Tg1 -Tg2 SameRel EqProt Heq // in Acc1.
    - (* FIXME: there has to be a shorter proof *)
      (* This has to be a foreign access *)
      destruct (rel_dec tr1 acc_tg (itag it1)) eqn:AccRel; last first.
      + (* If it's a child access then it's also a child access for the Disabled parent. *)
        inversion Dis1 as [it_witness ? RelWitness LookupWitness DisWitnessPre].
        destruct (decide (perm (item_lookup it_witness l) = Disabled)) as [Hdis|HNonDis]; simplify_eq.
        * rewrite <- apply_access_success_condition in GlobalSuccess.
          rewrite every_node_iff_every_lookup in GlobalSuccess. 2: {
            intros tg0 Ex0. apply unique_lookup. apply GloballyUnique1. assumption.
          }
          specialize (GlobalSuccess _ _ LookupWitness).
          pose proof (tree_determined_specifies_tag _ _ _ (proj1 LookupWitness) (proj2 LookupWitness))
            as WitnessTg.
          subst witness_tg.
          assert (match rel_dec tr1 acc_tg (itag it_witness) with
            | Child _ => True
            | Foreign _ => False
            end
          ). {
            unfold rel_dec in RelWitness.
            destruct (decide _); last discriminate.
            unfold rel_dec in AccRel.
            destruct (decide _); last discriminate.
            unfold rel_dec.
            destruct (decide (ParentChildIn (itag it_witness) acc_tg tr1)) as [|WitnessAccRel]; first done.
            apply WitnessAccRel.
            eapply ParentChild_transitive.
            + eassumption.
            + eassumption.
          }
          destruct (rel_dec _ acc_tg (itag it_witness)); first contradiction.
          (* Finally we have all the ingredients of the contradiction *)
          rewrite /item_apply_access in GlobalSuccess.
          destruct GlobalSuccess as [? GlobalSuccess].
          rewrite bind_Some in GlobalSuccess.
          destruct GlobalSuccess as [tmp_perms [PermissionsApply Wrapper]].
          injection Wrapper; clear Wrapper; intros; subst.
          rewrite /permissions_apply_range' in PermissionsApply.
          pose proof (proj2 (mem_apply_range'_success_condition _ _ _) (mk_is_Some _ _ PermissionsApply))
            as PermissionApply.
          specialize (PermissionApply l InRange).
          unfold item_lookup in Hdis.
          rewrite /maybe_non_children_only in PermissionApply.
          rewrite /nonchildren_only /= in PermissionApply.
          repeat rewrite if_fun_absorb_args in PermissionApply.
          rewrite Tauto.if_same in PermissionApply.
          rewrite /apply_access_perm /= in PermissionApply.
          destruct PermissionApply as [tmp_lazy PermissionApply].
          rewrite bind_Some in PermissionApply.
          destruct PermissionApply as [tmp_perm [ApplyAccessInner ValidateProt]].
          rewrite Hdis in ApplyAccessInner.
          rewrite /apply_access_perm_inner in ApplyAccessInner.
          case_match; discriminate.
        * inversion DisWitnessPre as [HX DisWitness|lp HDis Hlookup HX]; simplify_eq.
          1: rewrite -DisWitness in HNonDis; done.
          inversion Hlookup as [HX1 HX2|tg_w2 it_w2 x1 x2 Hcs2 Hlu2 Hprot2 Hperm2 Hlp]; simplify_eq.
          1: rewrite -HX // in HNonDis.
          rewrite <- apply_access_success_condition in GlobalSuccess.
          rewrite every_node_iff_every_lookup in GlobalSuccess. 2: {
            intros tg0 Ex0. apply unique_lookup. apply GloballyUnique1. assumption.
          }
          specialize (GlobalSuccess _ _ Hlu2).
          pose proof (tree_determined_specifies_tag _ _ _ (proj1 Hlu2) (proj2 Hlu2))
            as <-.
          rewrite /rel_dec in RelWitness.
          destruct decide as [HPC1|] in RelWitness; last done. clear RelWitness.
          rewrite /rel_dec in AccRel.
          destruct decide as [HPC2|] in AccRel; last done. clear AccRel.
          rewrite /rel_dec decide_False in GlobalSuccess; last first.
          { intros HH. exfalso. eapply cousins_have_disjoint_children. 4: exact Hcs2.
            5: exact HH. 4: eapply ParentChild_transitive; eassumption.
            1: done. all: eapply GloballyUnique1. 2: eapply Hlu2. eapply LookupWitness. }
          rewrite decide_False in GlobalSuccess; last first.
          { intros HH. rewrite /rel_dec in Hcs2.
            destruct decide as [|HHH] in Hcs2; first done.
            destruct decide as [|HHH2] in Hcs2; first done.
            eapply HHH2. do 3 (eapply ParentChild_transitive; first done). by left. }
          exfalso. rewrite /item_apply_access in GlobalSuccess.
          rewrite is_Some_ignore_bind in GlobalSuccess.
          eapply mem_apply_range'_success_condition in GlobalSuccess. 2: done.
          rewrite maybe_non_children_only_no_effect // in GlobalSuccess.
          rewrite /item_lookup in Hperm2. rewrite Hperm2 in GlobalSuccess.
          rewrite bool_decide_true // in GlobalSuccess.
          destruct kind; cbv in GlobalSuccess; by destruct GlobalSuccess.
      + rewrite <- EqProt.
        destruct (bool_decide (protector_is_active (iprot it1) C)) eqn:Heq; last first.
        { rewrite Tg2 -Tg1 -SameRel AccRel.
          rewrite /maybe_non_children_only /nonchildren_only.
          repeat rewrite if_fun_absorb_args.
          repeat case_match; first done.
          all: rewrite /apply_access_perm /apply_access_perm_inner //=.
          all: repeat case_match; done. }
        rewrite Tg2 -Tg1 -SameRel AccRel.
        rewrite /maybe_non_children_only /nonchildren_only.
        repeat rewrite if_fun_absorb_args.
        inversion Dis2 as [it_witness ? RelWitness LookupWitness DisWitnessPre].
        destruct (decide (perm (item_lookup it2 l) = Cell)) as [Hcell|Hncell].
        { rewrite /apply_access_perm /apply_access_perm_inner Hcell /=. clear. repeat (case_match; try done). }
        (* we are protected. this means we are not initalized by state_wf *)
        assert (initialized (item_lookup it2 l) = PermLazy) as HH.
        1: inversion DisWitnessPre as [HX DisWitness|lp HX HDis Hlookup]; simplify_eq.
        { specialize (ProtParentsNonDis witness_tg l). eapply every_child_ParentChildIn in ProtParentsNonDis.
          2: done. 2: eapply GloballyUnique2, LookupWitness. 2: eapply LookupWitness. 2: eapply GloballyUnique2, Ex2.
          2: rewrite /rel_dec in RelWitness; by destruct (decide (ParentChildIn witness_tg (itag it1) tr2)).
          setoid_rewrite every_node_eqv_universal in ProtParentsNonDis.
          ospecialize (ProtParentsNonDis it2 _ _).
          1: eapply exists_determined_exists; eapply Ex2. 1: by eapply tree_lookup_correct_tag.
          rewrite /item_protected_all_parents_not_disabled in ProtParentsNonDis.
          destruct (initialized (item_lookup it2 l)); last done.
          rewrite -EqProt -DisWitness in ProtParentsNonDis. ospecialize (ProtParentsNonDis _ _).
          1: done. 1: by eapply bool_decide_eq_true_1. by destruct ProtParentsNonDis. }
        { specialize (ParentsMoreInit witness_tg). eapply every_child_ParentChildIn in ParentsMoreInit.
          2: done. 2: eapply GloballyUnique2, LookupWitness. 2: eapply LookupWitness. 2: eapply GloballyUnique2, Ex2.
          2: rewrite /rel_dec in RelWitness; by destruct (decide (ParentChildIn witness_tg (itag it1) tr2)).
          setoid_rewrite every_node_eqv_universal in ParentsMoreInit.
          ospecialize (ParentsMoreInit it2 _ _).
          1: eapply exists_determined_exists; eapply Ex2. 1: by eapply tree_lookup_correct_tag.
          ospecialize (ParentsMoreInit l). destruct (initialized (item_lookup it2 l)); last done.
          rewrite -Hlookup in ParentsMoreInit. ospecialize (ParentsMoreInit _).
          1: done. 1: done. }
        all: rewrite /apply_access_perm /apply_access_perm_inner HH //=.
        all: repeat case_match; done.
    - (* Frozen in practice case.
         Before we do the usual manipulations we make both the left and right access use
         the same [rel_dec] so that the [maybe_non_children_only] case distinction works
         on both simultaneously. *)
      rewrite SameRel in Acc1.
      edestruct maybe_non_children_only_effect_or_nop as [Heq|Heq].
      2: by erewrite Heq. (* Noop case, easy. *)
      rewrite Heq.
      rewrite Tg1 -Tg2 Heq in Acc1.
      destruct kind, (rel_dec tr2 _ _) eqn:Rel.
      + (* Foreign read is allowed *)
        unfold apply_access_perm, apply_access_perm_inner.
        repeat (case_match; simpl; try auto).
      + (* Child read is allowed *)
        unfold apply_access_perm, apply_access_perm_inner.
        repeat (case_match; simpl; try auto).
      + (* Foreign write is allowed, except when there is a protector.
           Once we eliminate all other cases we'll have to prove that the protector is inactive by
           using the left tree in which the access suceeded. *)
        unfold apply_access_perm, apply_access_perm_inner.
        repeat (case_match; simpl; try auto).
        (* Now we have a goal that is definitely not provable, but we have gained
           a hypothesis [protector_is_active] in the context. We can derive a contradiction. *)
        all: exfalso.
        all: unfold apply_access_perm, apply_access_perm_inner in Acc1.
        all: rewrite -Lookup1 in Acc1.
        all: repeat (case_match; simpl in Acc1; try auto).
        all: try (inversion Acc1; congruence).
        (* We have all the elements of the contradiction, but a bit of rewriting is necessary
           to get them in a shape that is obviously conflicting.
           At that point there are two kinds of goals
           - some where the protector is active only on one side, solve them using [EqProt],
           - others whene [initialized] returns inconsistent results, solve them by
             unifying the same [ini] everywhere. *)
        all: repeat multimatch goal with
        | H : bool_decide _ = true |- _ => pose proof (bool_decide_eq_true_1 _ H); clear H
        | H : bool_decide _ = false |- _ => pose proof (bool_decide_eq_false_1 _ H); clear H
        | H : context [ iprot _ ] |- _ => rewrite EqProt in H
        | |- _ => try contradiction
        end.
        all: assert (initialized (item_lookup it1 l) = ini) as Ini1 by (rewrite -Lookup1; done).
        all: simpl in *; try congruence.
      + (* Child write is necessarily UB due to the Frozen parent *)
        exfalso.
        specialize (Hrestrict eq_refl). subst d.
        eapply frozen_in_practice_rejects_child_write. 4: exact GlobalSuccess.
        * eassumption.
        * eassumption.
        * eassumption.
        * eexists. rewrite SameRel. rewrite -Tg2. apply Rel.
    - rewrite -SameRel Tg2 -Tg1 -EqProt. edestruct maybe_non_children_only_effect_or_nop as [Heq|Heq];
        erewrite Heq in Acc1; erewrite Heq; clear Heq. 2: done.
      rewrite -Lookup1 in Acc1. destruct kind.
      + destruct d; (inversion Hd as [P Hprot|P Hnoprot]; subst P p1 p2;
          [ rewrite bool_decide_eq_false_2 // in Acc1|-*
          | rewrite bool_decide_eq_true_2 // in Acc1|-*]).
        all: destruct (rel_dec tr1 acc_tg (itag it1)), ini.
        all: rewrite /apply_access_perm /apply_access_perm_inner /= in Acc1|-*; done.
      + specialize (Hrestrict eq_refl). subst d.
        inversion Hd as [P Hprot|P Hnoprot]; subst P p1 p2.
        1: rewrite bool_decide_eq_false_2 // in Acc1|-*.
        2: rewrite bool_decide_eq_true_2 // in Acc1|-*.
        all: destruct (rel_dec tr1 acc_tg (itag it1)), ini.
        all: rewrite /apply_access_perm /apply_access_perm_inner /= in Acc1|-*; done.
  Qed.

  Lemma item_eq_up_to_C_allows_more_access (b:bool)
    {d tr1 tr2 tg it1 it2 kind acc_tg range}
    (Tg1 : itag it1 = tg)
    (Tg2 : itag it2 = tg)
    (UnqAcc : tree_unique acc_tg tr1)
    (UnqAcc2 : tree_unique acc_tg tr2)
    (Ex1 : tree_unique tg tr1)
    (Ex2 : tree_lookup tr2 tg it2)
    (SameRel : forall tg tg', rel_dec tr1 tg tg' = rel_dec tr2 tg tg')
    (ProtParentsNonDis : protected_parents_not_disabled C tr2)
    (ParentsMoreInit : parents_more_init tr2)
    (GlobalSuccess : is_Some (tree_apply_access (maybe_non_children_only b (apply_access_perm kind)) C acc_tg range tr1))
    (GloballyUnique1 : forall tg, tree_contains tg tr1 -> tree_unique tg tr1)
    (GloballyUnique2 : forall tg, tree_contains tg tr2 -> tree_unique tg tr2)
    (Hrestrict : kind = AccessWrite → d = Forwards)
    :
    item_eq_up_to_C C tr1 tr2 tg d it1 it2 ->
    is_Some (item_apply_access (maybe_non_children_only b (apply_access_perm kind)) C (rel_dec tr1 acc_tg (itag it1)) range it1) ->
    is_Some (item_apply_access (maybe_non_children_only b (apply_access_perm kind)) C (rel_dec tr2 acc_tg (itag it2)) range it2).
  Proof.
    rewrite /item_apply_access /permissions_apply_range'.
    rewrite is_Some_ignore_bind.
    rewrite is_Some_ignore_bind.
    intros EqC.
    intro App1.
    rewrite -mem_apply_range'_success_condition in App1.
    rewrite -mem_apply_range'_success_condition.
    intros l InRange.
    specialize (App1 l InRange).
    specialize (EqC l).
    eapply (loc_eq_up_to_C_allows_more_access Tg1 Tg2 UnqAcc UnqAcc2 Ex1 Ex2 SameRel); done.
  Qed.

  Lemma tree_equal_allows_more_access_maybe_nonchildren_only (b:bool)
    {d tr1 tr2 kind acc_tg range}
    (GloballyUnique1 : forall tg, tree_contains tg tr1 -> tree_unique tg tr1)
    (GloballyUnique2 : forall tg, tree_contains tg tr2 -> tree_unique tg tr2)
    (ProtParentsNonDis : protected_parents_not_disabled C tr2)
    (ParentsMoreInit : parents_more_init tr2)
    (Hrestrict : kind = AccessWrite → d = Forwards) :
    tree_equal C d tr1 tr2 ->
    tree_unique acc_tg tr1 ->
    is_Some (tree_apply_access (maybe_non_children_only b (apply_access_perm kind)) C acc_tg range tr1) ->
    is_Some (tree_apply_access (maybe_non_children_only b (apply_access_perm kind)) C acc_tg range tr2).
  Proof.
    intros Eq UnqAcc Acc1.
    apply apply_access_success_condition.
    pose proof (proj2 (apply_access_success_condition _ _ _ _ _) Acc1) as Every1.
    (* Get it into a more usable form *)
    rewrite every_node_iff_every_lookup in Every1.
    2: eapply tree_equal_implies_globally_unique_1; eassumption.
    rewrite every_node_iff_every_lookup.
    2: eapply tree_equal_implies_globally_unique_2; eassumption.
    (* And now we can unfold the definitions more *)
    intros tg it Lookup2.
    pose proof Eq as EqCopy.
    destruct EqCopy as [ExIff [SameRel Lookup]].
    destruct (tree_equal_transfer_lookup_2 C Eq Lookup2) as [it1 [Lookup1 EqC]].
    eapply (item_eq_up_to_C_allows_more_access b).
    - erewrite tree_determined_specifies_tag. 2,3: eapply Lookup1. reflexivity.
    - erewrite tree_determined_specifies_tag. 2,3: eapply Lookup2. reflexivity.
    - apply UnqAcc.
    - eapply GloballyUnique2. destruct Eq as (H1&H2&H3). eapply H1. by eapply unique_exists.
    - apply GloballyUnique1. apply Lookup1.
    - done. 
    - eassumption.
    - eapply ProtParentsNonDis.
    - done.
    - apply Acc1.
    - exact GloballyUnique1.
    - exact GloballyUnique2.
    - done.
    - done.
    - eapply Every1; eassumption.
  Qed.

  Lemma tree_equal_allows_more_access
    {d tr1 tr2 kind acc_tg range}
    (GloballyUnique1 : forall tg, tree_contains tg tr1 -> tree_unique tg tr1)
    (GloballyUnique2 : forall tg, tree_contains tg tr2 -> tree_unique tg tr2)
    (ProtParentsNonDis : protected_parents_not_disabled C tr2)
    (ParentsMoreInit : parents_more_init tr2)
    (Hrestrict : kind = AccessWrite → d = Forwards) :
    tree_equal C d tr1 tr2 ->
    tree_unique acc_tg tr1 ->
    is_Some (memory_access kind C acc_tg range tr1) ->
    is_Some (memory_access kind C acc_tg range tr2).
  Proof.
    by eapply (tree_equal_allows_more_access_maybe_nonchildren_only false).
  Qed. 

  Lemma tree_equal_allows_more_access_nonchildren_only
    {d tr1 tr2 kind acc_tg range}
    (GloballyUnique1 : forall tg, tree_contains tg tr1 -> tree_unique tg tr1)
    (GloballyUnique2 : forall tg, tree_contains tg tr2 -> tree_unique tg tr2)
    (ProtParentsNonDis : protected_parents_not_disabled C tr2)
    (ParentsMoreInit : parents_more_init tr2)
    (Hrestrict : kind = AccessWrite → d = Forwards) :
    tree_equal C d tr1 tr2 ->
    tree_unique acc_tg tr1 ->
    is_Some (memory_access_nonchildren_only kind C acc_tg range tr1) ->
    is_Some (memory_access_nonchildren_only kind C acc_tg range tr2).
  Proof.
    by eapply (tree_equal_allows_more_access_maybe_nonchildren_only true).
  Qed.

  Lemma trees_equal_allows_more_access d tr1 tr2 blk kind acc_tg range :
    (* _even_ nicer preconditions would be nice, but these are already somewhat eeh "optimistic" *)
    trees_equal C d tr1 tr2 →
    wf_trees tr1 →
    wf_trees tr2 →
    each_tree_protected_parents_not_disabled C tr2 →
    each_tree_parents_more_init tr2 →
    trees_contain acc_tg tr1 blk →
    (kind = AccessWrite → d = Forwards) →
    is_Some (apply_within_trees (memory_access kind C acc_tg range) blk tr1) → 
    is_Some (apply_within_trees (memory_access kind C acc_tg range) blk tr2).
  Proof.
    intros Heq Hwf1 Hwf2 HCCC1 HPMI1 Hcont Hd [x (trr1&H1&(trr1'&H2&[= <-])%bind_Some)%bind_Some].
    specialize (Heq blk).
    rewrite H1 in Heq. inversion Heq as [? trr2 Heqr q H2'|]; simplify_eq.
    eapply mk_is_Some, tree_equal_allows_more_access in H2 as (trr2'&Htrr2').
    * eexists. rewrite /apply_within_trees -H2' /= Htrr2' /= //.
    * intros tg. eapply wf_tree_tree_unique. eapply Hwf1, H1.
    * intros tg. eapply wf_tree_tree_unique. eapply Hwf2. done.
    * by eapply HCCC1.
    * by eapply HPMI1.
    * done. 
    * apply Heqr.
    * eapply wf_tree_tree_unique. 1: eapply Hwf1, H1.
      rewrite /trees_contain /trees_at_block H1 // in Hcont.
  Qed.

End utils.



