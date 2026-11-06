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
From simuliris.tree_borrows.trees_equal Require Import trees_equal_base random_lemmas trees_equal_transitivity.
From simuliris.tree_borrows.trees_equal Require Export trees_equal_preserved_by_access_base.

Section utils.

  Context (C : call_id_set).

  Lemma access_preserves_pseudo_conflicted_activable (b:bool)
    {tr tg l kind acc_tg range tr'} :
    pseudo_conflicted C tr tg l ResActivable ->
    tree_apply_access (maybe_non_children_only b (apply_access_perm kind)) C acc_tg range tr = Some tr' ->
    pseudo_conflicted C tr' tg l ResActivable.
  Proof.
    intros PseudoC Acc.
    inversion PseudoC as [|tg_cous it_cous cous_rel [cous_ex cous_det] cous_prot cous_nondis cous_init cous_noncell].
    destruct (apply_access_spec_per_node cous_ex cous_det Acc)
          as (cous' & cous'_spec & cous'_ex & cous'_det).
    symmetry in cous'_spec.
    rewrite bind_Some in cous'_spec.
    destruct cous'_spec as (perms' & perms'_spec & cous'_build).
    injection cous'_build; intros; subst; clear cous'_build.
    pose proof (mem_apply_range'_spec _ _ l _ _ perms'_spec) as effect_at_l.
    destruct (decide _).
    + (* within range. Big case analysis incoming. *)
      destruct effect_at_l as (perm' & perm'_lookup & perm'_spec).
      edestruct (maybe_non_children_only_effect_or_nop b (apply_access_perm kind) (rel_dec tr acc_tg (itag it_cous))) as [Heff|Heff].
      all: rewrite Heff in perm'_spec.
      1: rewrite bind_Some in perm'_spec;
         destruct perm'_spec as (perm & perm_apply_inner & perm'_spec);
         rewrite bind_Some in perm'_spec;
         destruct perm'_spec as (perm_validated & perm_check_prot & perm'_spec).
      all: pose proof perm'_spec as [= <-].
      all: (econstructor; [ 
         erewrite <- access_same_rel_dec; eassumption
       | done
       | done
       | .. ]).
      * rewrite /item_lookup /= perm'_lookup /=.
        rewrite /item_lookup in cous_init.
        destruct (iperm it_cous !! l) eqn:it_cous_defined.
        all: rewrite it_cous_defined !cous_init in perm_check_prot.
        all: rewrite bool_decide_eq_true_2 in perm_check_prot; last assumption.
        all: destruct perm; try discriminate.
        all: injection perm_check_prot; intros; subst; congruence.
      * rewrite /item_lookup /= perm'_lookup /=.
        rewrite /item_lookup in cous_init.
        destruct (iperm it_cous !! l) eqn:it_cous_defined;
        rewrite it_cous_defined cous_init //=.
      * rewrite /item_lookup /= perm'_lookup /=.
        intros ->. eapply cous_noncell. rewrite /item_lookup /=.
        assert (perm = Cell) as ->.
        { clear -perm_check_prot. repeat (case_match; simplify_eq; try done). }
        clear -perm_apply_inner. rewrite /apply_access_perm_inner in perm_apply_inner.
        repeat (case_match; simplify_eq; try done).
      * rewrite /item_lookup /= perm'_lookup //.
      * rewrite /item_lookup /= perm'_lookup //.
      * rewrite /item_lookup /= perm'_lookup /=. done.
    + (* out of range is a lot easier *)
      econstructor.
      * erewrite <- access_same_rel_dec; eassumption.
      * split; eassumption.
      * eassumption.
      * rewrite /item_lookup /= effect_at_l. assumption.
      * rewrite /item_lookup /= effect_at_l. assumption.
      * rewrite /item_lookup /= effect_at_l. assumption.
  Qed.

  Lemma access_preserves_pseudo_conflicted (b:bool)
    {tr tg l kind acc_tg range conf tr'} :
    pseudo_conflicted C tr tg l conf ->
    tree_apply_access (maybe_non_children_only b (apply_access_perm kind)) C acc_tg range tr = Some tr' ->
    pseudo_conflicted C tr' tg l conf.
  Proof.
    intros Hpc Haccess. destruct conf.
    2: by eapply access_preserves_pseudo_conflicted_activable.
    inversion Hpc; by econstructor.
  Qed.

  Lemma frozen_in_practice_tree_apply_access_irreversible
    {tr tr' tg acc_tg kind range witness loc b}
    (Frz : frozen_in_practice tr tg witness loc)
    (Cont : tree_contains acc_tg tr)
    (Uni : wf_tree tr)
    (Acc : tree_apply_access (maybe_non_children_only b (apply_access_perm kind)) C acc_tg range tr = Some tr')
    : let bf := becomes_frozen kind range loc b tr acc_tg witness in
      let bd := becomes_disabled kind range loc b tr acc_tg witness in
      (frozen_in_practice tr' tg witness loc ∧ bf) ∨ (parent_has_perm Disabled tr' tg witness loc ∧ bd).
  Proof.
    inversion Frz as [it_witness incl Rel Lookup Perm Init].
    assert (itag it_witness = witness) as <- by by eapply tree_lookup_correct_tag.
    destruct (frozen_tree_apply_access_irreversible C Lookup Perm Init Acc) as [it' [Lookup' [Init' [[Perm' BF]|[Perm' [BF NoProt]]]]]].
    - left. split; last done. econstructor.
      + erewrite <- access_same_rel_dec; eassumption.
      + apply Lookup'.
      + apply Perm'.
      + apply Init'.
    - right. split; last done. econstructor.
      + erewrite <- access_same_rel_dec; eassumption.
      + apply Lookup'.
      + destruct (item_lookup it' loc) as [lp pp]; simpl in Init',Perm'; subst. done.
      + destruct (item_lookup it' loc) as [lp pp]; simpl in Init',Perm'; subst. done.
  Qed.

  Lemma parent_has_perm_similarly_disabled
    {p tr tr' tg acc_tg kind range witness loc b}
    (Frz : parent_has_perm p tr tg witness loc)
    (nRIM : p ≠ ReservedIM)
    (nCell : p ≠ Cell)
    (Cont : tree_contains acc_tg tr)
    (Uni : wf_tree tr)
    (Acc : tree_apply_access (maybe_non_children_only b (apply_access_perm kind)) C acc_tg range tr = Some tr')
    : let bd := becomes_disabled kind range loc b tr acc_tg witness in
      bd → parent_has_perm Disabled tr' tg witness loc.
  Proof.
    inversion Frz as [it_witness incl Rel Lookup Perm Init].
    assert (itag it_witness = witness) as <- by by eapply tree_lookup_correct_tag.
    destruct (parent_has_perm_similarly_disabled_after_access C Lookup Perm nRIM nCell Init Acc) as [it' [Lookup' [Init' Perm']]].
    intros bd. subst bd. intros Hbd. specialize (Perm' Hbd) as (Hd&Hnoprot).
    econstructor.
    + erewrite <- access_same_rel_dec; eassumption.
    + apply Lookup'.
    + destruct (item_lookup it' loc) as [lp pp]; simpl in Init',Hd; subst. done.
    + destruct (item_lookup it' loc) as [lp pp]; simpl in Init',Hd; subst. done.
  Qed.

  Lemma item_apply_access_effect_on_initialized
    {it it' l b kind rel range}
    (Acc : item_apply_access (maybe_non_children_only b (apply_access_perm kind)) C rel range it = Some it')
    : initialized (item_lookup it' l)
    = if decide (range'_contains range l)
      then most_init (initialized (item_lookup it l)) (requires_init rel) 
      else initialized (item_lookup it l).
  Proof.
    unfold item_apply_access, permissions_apply_range' in Acc.
    rewrite bind_Some in Acc; destruct Acc as [iperm' [iperm'Spec Inj]].
    injection Inj; clear Inj; intros; subst.
    pose proof (mem_apply_range'_spec _ _ l _ _ iperm'Spec) as LocalSpec.
    case_match.
    2: { rewrite /item_lookup /=. f_equal. f_equal. assumption. }
    destruct LocalSpec as [val [valSpec MaybeApply]].
    unfold item_lookup; simpl.
    rewrite valSpec; clear valSpec; simpl.
    (* Now it's time to actually unfold [maybe_non_children_only] and [apply_access_perm] where
       [initialized] *might* be modified. *)
    unfold maybe_non_children_only in MaybeApply. rewrite most_init_comm. case_match.
    - unfold nonchildren_only in MaybeApply. case_match.
      + simpl. case_match.
        * injection MaybeApply; intros; subst; reflexivity.
        * unfold apply_access_perm in MaybeApply.
          destruct (apply_access_perm_inner _ _ _ _); simpl in *; last congruence.
          destruct (if most_init _ _ then _ else _); simpl in MaybeApply; last congruence.
          injection MaybeApply; clear MaybeApply; intros; subst.
          simpl. rewrite most_init_noop. reflexivity.
      + unfold apply_access_perm in MaybeApply.
        destruct (apply_access_perm_inner _ _ _ _); simpl in *; last congruence.
        destruct (if most_init _ _ then _ else _); simpl in MaybeApply; last congruence.
        injection MaybeApply; clear MaybeApply; intros; subst.
        simpl. rewrite most_init_absorb. reflexivity.
    - unfold apply_access_perm in MaybeApply.
      destruct (apply_access_perm_inner _ _ _ _); simpl in *; last congruence.
      destruct (if most_init _ _ then _ else _); simpl in MaybeApply; last congruence.
      injection MaybeApply; clear MaybeApply; intros; subst.
      simpl. rewrite most_init_comm. reflexivity.
  Qed.


  Lemma perm_eq_up_to_C_preserved_by_access (b:bool) 
    {d tr1 tr1' tr2 tr2' it1 it1' it2 it2' tg l acc_tg kind range} (Hunq : wf_tree tr2)
    (SameProt : iprot it1 = iprot it2)
    (SameTg : itag it1 = itag it2) (* note: redundant *)
    (SameRel : forall tg tg', rel_dec tr1 tg tg' = rel_dec tr2 tg tg')
    (Unq1 : wf_tree tr1)
    (Unq2 : wf_tree tr2)
    :
    parents_more_active tr1 →
    no_active_cousins C tr1 →
    parents_more_active tr2 →
    no_active_cousins C tr2 →
    tree_equal C d tr1 tr2 →
    perm_eq_up_to_C C tr1 tr2 tg l (iprot it1) d (item_lookup it1 l) (item_lookup it2 l) ->
    tree_apply_access (maybe_non_children_only b (apply_access_perm kind)) C acc_tg range tr1 = Some tr1' ->
    tree_apply_access (maybe_non_children_only b (apply_access_perm kind)) C acc_tg range tr2 = Some tr2' ->
    tree_lookup tr1 tg it1 ->
    tree_lookup tr1' tg it1' ->
    tree_lookup tr2 tg it2 ->
    tree_lookup tr2' tg it2' ->
    tree_contains acc_tg tr2 ->
    tree_contains acc_tg tr1 ->
    item_apply_access (maybe_non_children_only b (apply_access_perm kind)) C (rel_dec tr1 acc_tg (itag it1)) range it1 = Some it1' ->
    item_apply_access (maybe_non_children_only b (apply_access_perm kind)) C (rel_dec tr2 acc_tg (itag it2)) range it2 = Some it2' ->
    perm_eq_up_to_C C tr1' tr2' tg l (iprot it1') d (item_lookup it1' l) (item_lookup it2' l).
  Proof.
    intros Hpma1 Hnac1 Hpma2 Hnac2 HeqTree EqC Acc1 Acc2 Lookup1 Lookup1' Lookup2 Lookup2' Hacctg1 Hacctg2 ItAcc1 ItAcc2. 
    inversion EqC as [
        p pSpec Equal
        |ini confl1 confl2 Prot Confl1 Confl2 itLookup1 itLookup2
        |ini confl1 confl2 NoProt itLookup1 itLookup2
        |p1 p2 Confl1 Confl2 itLookup1 itLookup2
        |????? SameInit
        |ini confl1 confl2 witness_tg Hfrz itLookup1 itLookup2
        |p1 p2 ini H1 itLookup1 itLookup2
    ].
    - (* reflexive case *)
      rewrite bind_Some in ItAcc1; destruct ItAcc1 as [perms1' [PermsAcc1 it1'Spec]].
      injection it1'Spec; intros; subst; clear it1'Spec.
      rewrite bind_Some in ItAcc2; destruct ItAcc2 as [perms2' [PermsAcc2 it2'Spec]].
      injection it2'Spec; intros; subst; clear it2'Spec.
      simpl.
      pose proof (mem_apply_range'_spec _ _ l _ _ PermsAcc1) as Perms1'Spec.
      pose proof (mem_apply_range'_spec _ _ l _ _ PermsAcc2) as Perms2'Spec.
      destruct (decide _).
      + (* within range *)
        destruct Perms1'Spec as [p1 [LookupSome1' PermAcc1]].
        destruct Perms2'Spec as [p2 [LookupSome2' PermAcc2]].
        rewrite /item_lookup LookupSome1' LookupSome2' /=.
        rewrite /item_lookup in Equal.
        rewrite Equal SameRel SameProt SameTg in PermAcc1.
        rewrite PermAcc1 in PermAcc2.
        injection PermAcc2; intros; subst. constructor.
      + (* outside range *)
        rewrite /item_lookup in Equal.
        rewrite /item_lookup /= Perms1'Spec Perms2'Spec Equal.
        constructor.
    - (* The permissions are pseudo-conflicted, this restricts the possible accesses. *)
      rewrite SameRel SameTg in ItAcc1.
      rewrite bind_Some in ItAcc1; destruct ItAcc1 as [perms1' [perms1'Spec it1'Spec]].
      rewrite bind_Some in ItAcc2; destruct ItAcc2 as [perms2' [perms2'Spec it2'Spec]].
      injection it1'Spec; intros; subst; clear it1'Spec.
      injection it2'Spec; intros; subst; clear it2'Spec.
      rewrite /item_lookup /=.
      pose proof (mem_apply_range'_spec _ _ l _ _ perms1'Spec) as perm1'Spec; clear perms1'Spec.
      pose proof (mem_apply_range'_spec _ _ l _ _ perms2'Spec) as perm2'Spec; clear perms2'Spec.
      (* Now we do the case analysis of the access that occured *)
      (* First off, if we're out of range then we can take the exact same witness. *)
      destruct (decide (range'_contains range l)).
      2: {
        rewrite perm1'Spec.
        rewrite perm2'Spec.
        rewrite /item_lookup in itLookup1, itLookup2.
        rewrite -itLookup1 -itLookup2.
        econstructor.
        + assumption.
        + inversion Confl1; subst.
          * constructor.
          * eapply access_preserves_pseudo_conflicted_activable; eassumption.
        + inversion Confl2; subst.
          * constructor.
          * eapply access_preserves_pseudo_conflicted_activable; eassumption.
      }
      (* Now we're within range *)
      destruct perm1'Spec as [perm1' [perm1'Lookup perm1'Spec]].
      destruct perm2'Spec as [perm2' [perm2'Lookup perm2'Spec]].
      rewrite perm1'Lookup perm2'Lookup; clear perm1'Lookup perm2'Lookup.
      simpl.
      rewrite bool_decide_eq_true_2 in perm1'Spec; [|assumption].
      rewrite bool_decide_eq_true_2 in perm2'Spec; [|rewrite -SameProt; assumption].
      rewrite /item_lookup in itLookup1, itLookup2.
      rewrite -itLookup1 in perm1'Spec; clear itLookup1.
      rewrite -itLookup2 in perm2'Spec; clear itLookup2.
      destruct (maybe_non_children_only_effect_or_nop b (apply_access_perm kind) (rel_dec tr2 acc_tg (itag it2))) as [Heff|Heff].
      all: rewrite !Heff /= in perm1'Spec,perm2'Spec.
      2: { simplify_eq. econstructor; first done. all: by eapply access_preserves_pseudo_conflicted. }
      (* Next we need to unwrap the apply_access_perm to get to apply_access_perm_inner *)
      rewrite bind_Some in perm1'Spec; destruct perm1'Spec as [perm1 [perm1Spec perm1'Spec]].
      rewrite bind_Some in perm1'Spec; destruct perm1'Spec as [tmp1 [tmp1Spec perm1'Spec]].
      injection perm1'Spec; simpl; intros; subst; clear perm1'Spec.
      rewrite bind_Some in perm2'Spec; destruct perm2'Spec as [perm2 [perm2Spec perm2'Spec]].
      rewrite bind_Some in perm2'Spec; destruct perm2'Spec as [tmp2 [tmp2Spec perm2'Spec]].
      injection perm2'Spec; simpl; intros; subst; clear perm2'Spec.
      simpl in *.
      (* We can finally start the big case analysis at the level of the state machine *)
      destruct (most_init _), perm1, perm2; try congruence.
      all: injection tmp1Spec; intros; subst; clear tmp1Spec.
      all: injection tmp2Spec; intros; subst; clear tmp2Spec.
      all: destruct kind, (rel_dec _ _ _) eqn:relation, confl1; simpl in *; try discriminate.
      all: destruct confl2; simpl in *; try discriminate.
      all: try (injection perm1Spec; intros; subst); clear perm1Spec.
      all: try (injection perm2Spec; intros; subst); clear perm2Spec.
      all: try constructor; auto.
      all: try constructor.
      (* Now they are all ResActivable and we need to show that the cousin is still a witness.
         See the above lemma for exactly that. *)
      all: eapply access_preserves_pseudo_conflicted_activable; eassumption.
    - (* The permissions are formerly pseudo-conflicted, but the difference should no longer matter now. *)
      rewrite SameRel SameTg in ItAcc1.
      rewrite bind_Some in ItAcc1; destruct ItAcc1 as [perms1' [perms1'Spec it1'Spec]].
      rewrite bind_Some in ItAcc2; destruct ItAcc2 as [perms2' [perms2'Spec it2'Spec]].
      injection it1'Spec; intros; subst; clear it1'Spec.
      injection it2'Spec; intros; subst; clear it2'Spec.
      rewrite /item_lookup /=.
      pose proof (mem_apply_range'_spec _ _ l _ _ perms1'Spec) as perm1'Spec; clear perms1'Spec.
      pose proof (mem_apply_range'_spec _ _ l _ _ perms2'Spec) as perm2'Spec; clear perms2'Spec.
      (* Now we do the case analysis of the access that occured *)
      (* First off, if we're out of range then we can take the exact same witness. *)
      destruct (decide (range'_contains range l)).
      2: {
        rewrite perm1'Spec.
        rewrite perm2'Spec.
        rewrite /item_lookup in itLookup1, itLookup2.
        rewrite -itLookup1 -itLookup2.
        econstructor 3.
        assumption.
      }
      (* Now we're within range *)
      destruct perm1'Spec as [perm1' [perm1'Lookup perm1'Spec]].
      destruct perm2'Spec as [perm2' [perm2'Lookup perm2'Spec]].
      rewrite perm1'Lookup perm2'Lookup; clear perm1'Lookup perm2'Lookup.
      simpl.
      rewrite bool_decide_eq_false_2 in perm1'Spec; [|assumption].
      rewrite bool_decide_eq_false_2 in perm2'Spec; [|rewrite -SameProt; assumption].
      rewrite /item_lookup in itLookup1, itLookup2.
      rewrite -itLookup1 in perm1'Spec; clear itLookup1.
      rewrite -itLookup2 in perm2'Spec; clear itLookup2.
      destruct (maybe_non_children_only_effect_or_nop b (apply_access_perm kind) (rel_dec tr2 acc_tg (itag it2))) as [Heff|Heff].
      all: rewrite !Heff /= in perm1'Spec,perm2'Spec.
      2: { simplify_eq. econstructor; first done. all: by eapply access_preserves_pseudo_conflicted. }
      (* Next we need to unwrap the apply_access_perm to get to apply_access_perm_inner *)
      rewrite bind_Some in perm1'Spec; destruct perm1'Spec as [perm1 [perm1Spec perm1'Spec]].
      rewrite bind_Some in perm1'Spec; destruct perm1'Spec as [tmp1 [tmp1Spec perm1'Spec]].
      injection perm1'Spec; simpl; intros; subst; clear perm1'Spec.
      rewrite bind_Some in perm2'Spec; destruct perm2'Spec as [perm2 [perm2Spec perm2'Spec]].
      rewrite bind_Some in perm2'Spec; destruct perm2'Spec as [tmp2 [tmp2Spec perm2'Spec]].
      injection perm2'Spec; simpl; intros; subst; clear perm2'Spec.
      simpl in *.
      (* We can finally start the big case analysis at the level of the state machine *)
      edestruct (most_init ini _), perm1, perm2; try congruence.
      all: injection tmp1Spec; intros; subst; clear tmp1Spec.
      all: injection tmp2Spec; intros; subst; clear tmp2Spec.
      all: destruct kind, (rel_dec _ _ _) eqn:relation, confl1; simpl in *; try discriminate.
      all: destruct confl2; simpl in *; try discriminate.
      all: try (injection perm1Spec; intros; subst); clear perm1Spec.
      all: try (injection perm2Spec; intros; subst); clear perm2Spec.
      all: try by econstructor 1.
      all: try by econstructor 3.
      (* pseudo-disabled *)
    - rewrite SameRel SameTg in ItAcc1.
      rewrite bind_Some in ItAcc1; destruct ItAcc1 as [perms1' [perms1'Spec it1'Spec]].
      rewrite bind_Some in ItAcc2; destruct ItAcc2 as [perms2' [perms2'Spec it2'Spec]].
      injection it1'Spec; intros; subst; clear it1'Spec.
      injection it2'Spec; intros; subst; clear it2'Spec.
      rewrite /item_lookup /=.
      pose proof (mem_apply_range'_spec _ _ l _ _ perms1'Spec) as perm1'Spec; clear perms1'Spec.
      pose proof (mem_apply_range'_spec _ _ l _ _ perms2'Spec) as perm2'Spec; clear perms2'Spec.
      (* Now we do the case analysis of the access that occured *)
      (* First off, if we're out of range then we can take the exact same witness. *)
      destruct (decide (range'_contains range l)).
      2: {
        rewrite perm1'Spec.
        rewrite perm2'Spec.
        rewrite /item_lookup in itLookup1, itLookup2.
        rewrite -itLookup1 -itLookup2.
        econstructor 4.
        all: eapply access_preserves_pseudo_disabled; first done.
        all: done.
      }
      (* Now we're within range *)
      destruct perm1'Spec as [perm1' [perm1'Lookup perm1'Spec]].
      destruct perm2'Spec as [perm2' [perm2'Lookup perm2'Spec]].
      rewrite perm1'Lookup perm2'Lookup; clear perm1'Lookup perm2'Lookup.
      simpl.
      rewrite /item_lookup in itLookup1, itLookup2.
      rewrite -itLookup1 in perm1'Spec; clear itLookup1.
      rewrite -itLookup2 in perm2'Spec; clear itLookup2.
      edestruct (maybe_non_children_only_effect_or_nop b (apply_access_perm kind) (rel_dec tr2 acc_tg (itag it2))) as [Heff|Heff].
      all: rewrite !Heff /= in perm1'Spec,perm2'Spec. all: clear Heff.
      2: { injection perm1'Spec as <-. injection perm2'Spec as <-.
           econstructor 4.
           all: eapply access_preserves_pseudo_disabled; first done.
           all: done. }
      (* Next we need to unwrap the apply_access_perm to get to apply_access_perm_inner *)
      rewrite bind_Some in perm1'Spec; destruct perm1'Spec as [perm1 [perm1Spec perm1'Spec]].
      rewrite bind_Some in perm2'Spec; destruct perm2'Spec as [perm2 [perm2Spec perm2'Spec]].
      assert (¬ ParentChildIn (itag it2) acc_tg tr2) as HnPC.
      { intros HnPC. clear perm1'Spec perm1Spec.
        inversion Confl2 as [|tg_cs it_cs X1 X2 H1 H2 H3 H4 H5]; simplify_eq.
        1: { rewrite /apply_access_perm_inner /= in perm2Spec.
             rewrite /rel_dec decide_True // in perm2Spec. by destruct kind. }
        destruct (apply_access_spec_per_node (proj1 H2) (proj2 H2) Acc2)
              as (cous' & cous'_spec & cous'_ex & cous'_det).
        symmetry in cous'_spec.
        rewrite bind_Some in cous'_spec.
        destruct cous'_spec as (perms' & perms'_spec & cous'_build).
        injection cous'_build; intros; subst; clear cous'_build.
        pose proof (mem_apply_range'_spec _ _ l _ _ perms'_spec) as effect_at_l.
        rewrite decide_True // in effect_at_l.
        destruct effect_at_l as (perm' & perm'_lookup & perm'_spec).
        rewrite /item_lookup in H4. rewrite H4 in perm'_spec.
        rewrite bool_decide_true in perm'_spec. 2: done.
        assert (tg_cs = itag it_cs) as -> by (symmetry; by eapply tree_lookup_correct_tag).
        assert (tg = itag it2) as -> by (symmetry; by eapply tree_lookup_correct_tag).
        rewrite /rel_dec decide_False in perm'_spec.
        2: { intros Hx. eapply cousins_have_disjoint_children. 4: eassumption. 4-5: done.
             all: eapply Hunq. 1: done. 1: eapply Lookup2. 1: eapply H2. }
        rewrite decide_False in perm'_spec.
        2: { intros Hx. rewrite /rel_dec in H1.
             destruct decide as [|HH1] in H1; first done.
             destruct decide as [|HH2] in H1; first done.
             eapply HH2. eapply ParentChild_transitive. 2: exact Hx. 1: done. }
        rewrite maybe_non_children_only_no_effect in perm'_spec. 2: done.
        destruct kind in perm'_spec; cbv in perm'_spec; done. }
      rewrite /rel_dec decide_False // /= in perm2'Spec. injection perm2'Spec as <-.
      rewrite /rel_dec decide_False // /= in perm1'Spec. injection perm1'Spec as <-.
      rewrite /rel_dec decide_False // /= in perm2Spec.
      rewrite /rel_dec decide_False // /= in perm1Spec.
      econstructor 4; eapply access_preserves_pseudo_disabled. 2,4: done.
      + inversion Confl1 as [|X1 X2 X3 X4 X5 X6 X7 X8 H]; simplify_eq.
        1: destruct kind, bool_decide in perm1Spec; cbv in perm1Spec; injection perm1Spec as <-; econstructor 1.
        econstructor 2. 1-4: done.
        * intros ->.
          destruct (bool_decide (protector_is_active (iprot it1) C)), kind, p1 as [|[]| | | |]; try discriminate perm1Spec.
          all: done.
        * intros ->.
          destruct (bool_decide (protector_is_active (iprot it1) C)), kind, p1 as [|[]| | | |]; try discriminate perm1Spec.
          all: done.
      + inversion Confl2 as [|X1 X2 X3 X4 X5 X6 X7 X8 H]; simplify_eq.
        1: destruct kind, bool_decide in perm1Spec; cbv in perm2Spec; injection perm2Spec as <-; econstructor 1.
        econstructor 2. 1-4: done.
        * intros ->.
          destruct (bool_decide (protector_is_active (iprot it2) C)), kind, p2 as [|[]| | | |]; try discriminate perm1Spec.
          all: done.
        * intros ->.
          destruct (bool_decide (protector_is_active (iprot it2) C)), kind, p2 as [|[]| | | |]; try discriminate perm1Spec.
          all: done.
    - econstructor.
      + eapply disabled_in_practice_tree_apply_access_irreversible; last eassumption. 2-3: done.
        eassumption.
      + eapply disabled_in_practice_tree_apply_access_irreversible; last eassumption. 2-3: done.
        eassumption.
      + rewrite (item_apply_access_effect_on_initialized ItAcc1).
        rewrite (item_apply_access_effect_on_initialized ItAcc2).
        rewrite SameInit.
        case_match; last reflexivity.
        f_equal. f_equal. rewrite SameTg. apply SameRel.
      + erewrite <-cell_item_apply_access_irreversible; last done.
        erewrite <-(cell_item_apply_access_irreversible _ (it':=it2')); last done.
        done.
    - (* Proof idea:
         each item is Reserved. Therefore it can:
         - get a child read: nothing happens
         - get a child write: it's UB, since the parent is frozen
         - get a foreign read: the conflictedness might change but that's OK, this case is precisely for that
         - get a foreign write: it's either UB or we remain, depending on interior mutability.
           + however, since such a write must disable our parent, it should not matter that IM is the same here.
             But reasoning about this is complicated (because of maybe_nonchildren_only) so let's just not. *)
      (* We're frozen in practice *)
      pose trd := (match d with Forwards => tr1 | Backwards => tr2 end). fold trd in Hfrz.
      pose trd' := (match d with Forwards => tr2 | Backwards => tr1 end).
      eapply trees_equal_transfer_frozen_in_practice_many in Hfrz as [(Hfrz&Hfrzo)|(tdis&Htdis&Htdiso)].
      3-5: by destruct d.
      2: { econstructor.
           + eapply disabled_in_practice_tree_apply_access_irreversible; last eassumption. 2-3: done.
             destruct d; try done. eapply Htdiso, tree_equal_sym, HeqTree. 
           + eapply disabled_in_practice_tree_apply_access_irreversible; last eassumption. 2-3: done.
             destruct d; try done. eapply Htdiso, HeqTree.
           + rewrite (item_apply_access_effect_on_initialized ItAcc1).
             rewrite (item_apply_access_effect_on_initialized ItAcc2).
             rewrite -itLookup1 -itLookup2 /=.
             case_match; last reflexivity.
             f_equal. f_equal. rewrite SameTg. apply SameRel.
            + erewrite <-cell_item_apply_access_irreversible; last done.
              erewrite <-(cell_item_apply_access_irreversible _ (it':=it2')); last done.
              rewrite -itLookup1 -itLookup2. simpl. done. }
      destruct (Hfrzo Forwards trd') as (p'&Hfrzalmost&Hfrz').
      1: destruct d; first done. 1: eapply tree_equal_sym in HeqTree; exact HeqTree.
      rewrite SameRel SameTg in ItAcc1.
      epose proof (cell_item_apply_access_irreversible _ ItAcc1 l) as ItAcc1Cell.
      epose proof (cell_item_apply_access_irreversible _ ItAcc2 l) as ItAcc2Cell.
      rewrite bind_Some in ItAcc1; destruct ItAcc1 as [perms1' [perms1'Spec it1'Spec]].
      rewrite bind_Some in ItAcc2; destruct ItAcc2 as [perms2' [perms2'Spec it2'Spec]].
      injection it1'Spec; intros; subst; clear it1'Spec.
      injection it2'Spec; intros; subst; clear it2'Spec.
      rewrite /item_lookup /= in ItAcc1Cell,ItAcc2Cell|-*.
      pose proof (mem_apply_range'_spec _ _ l _ _ perms1'Spec) as perm1'Spec; clear perms1'Spec.
      pose proof (mem_apply_range'_spec _ _ l _ _ perms2'Spec) as perm2'Spec; clear perms2'Spec.
      (* Now we do the case analysis of the access that occured *)
      (* First off, if we're out of range then we can take the exact same witness. *)
      destruct (decide (range'_contains range l)) eqn:Hrangedec.
      2: {
        rewrite perm1'Spec.
        rewrite perm2'Spec.
        rewrite /item_lookup in itLookup1, itLookup2.
        rewrite -itLookup1 -itLookup2.
        econstructor 6; destruct d.
        - eapply frozen_in_practice_tree_apply_access_irreversible in Hfrz. 4: exact Acc1. 2-3: done.
          destruct Hfrz as [(Hf&HX)|(Hf&HX)]; first done.
          rewrite /becomes_disabled Hrangedec in HX. done.
        - eapply frozen_in_practice_tree_apply_access_irreversible in Hfrz. 4: exact Acc2. 2-3: done.
          destruct Hfrz as [(Hf&HX)|(Hf&HX)]; first done.
          rewrite /becomes_disabled Hrangedec in HX. done.
      }
      (* Now we're within range *)
      destruct perm1'Spec as [perm1' [perm1'Lookup perm1'Spec]].
      destruct perm2'Spec as [perm2' [perm2'Lookup perm2'Spec]].
      rewrite perm1'Lookup /= in ItAcc1Cell.
      rewrite perm2'Lookup /= in ItAcc2Cell.
      rewrite perm1'Lookup perm2'Lookup; clear perm1'Lookup perm2'Lookup.
      simpl.
      rewrite /item_lookup in itLookup1, itLookup2.
      rewrite -itLookup1 /= in ItAcc1Cell.
      rewrite -itLookup2 /= in ItAcc2Cell.
      rewrite -itLookup1 in perm1'Spec; clear itLookup1.
      rewrite -itLookup2 in perm2'Spec; clear itLookup2.
      assert (∃ p, parent_has_perm p (match d with Backwards => tr1 | _ => tr2 end) tg witness_tg l ∧ (p = Frozen ∨ p = Active)) as (pt&Htrans&Hptrans).
      { destruct Hfrz' as [ -> |(->&_)]; eexists; (split; first done). all: tauto. }
      eapply @frozen_in_practice_tree_apply_access_irreversible with (tr' := match d with Forwards => _ | _ => _ end) in Hfrz; last (destruct d; [exact Acc1|exact Acc2]). 2-3: by destruct d.
      destruct Hfrz as [(H1&HX)|(H1&HX)].
      all: edestruct (maybe_non_children_only_effect_or_nop b (apply_access_perm kind) (rel_dec tr2 acc_tg (itag it2))) as [Heff|Heff].
      all: rewrite !Heff /= in perm1'Spec,perm2'Spec; clear Heff.
      2: { simplify_eq. econstructor 6; eassumption. }
      3: { eapply @parent_has_perm_similarly_disabled with (tr' := match d with Forwards => tr2' | _ => tr1' end) in Htrans.
           4: by destruct d. 4: by destruct d. 4: destruct d; done.
           4: { rewrite /becomes_disabled in HX|-*. destruct d.
                1: rewrite -SameRel //. rewrite SameRel //. }
           2: destruct Hptrans; by simplify_eq.
           2: destruct Hptrans; by simplify_eq.
           econstructor 5. 3: by simplify_eq.
           3: by simplify_eq.
           all: eapply parent_has_disabled_perm_is_pseudo_disabled; by destruct d. }
      (* Next we need to unwrap the apply_access_perm to get to apply_access_perm_inner *)
      all: rewrite bind_Some in perm1'Spec; destruct perm1'Spec as [perm1 [perm1Spec perm1'Spec]].
      all: rewrite bind_Some in perm1'Spec; destruct perm1'Spec as [tmp1 [tmp1Spec perm1'Spec]].
      all: injection perm1'Spec; simpl; intros; subst; clear perm1'Spec.
      all: rewrite bind_Some in perm2'Spec; destruct perm2'Spec as [perm2 [perm2Spec perm2'Spec]].
      all: rewrite bind_Some in perm2'Spec; destruct perm2'Spec as [tmp2 [tmp2Spec perm2'Spec]].
      all: injection perm2'Spec; simpl; intros; subst; clear perm2'Spec.
      2: { eapply @parent_has_perm_similarly_disabled with (tr' := match d with Forwards => tr2' | _ => tr1' end) in Htrans.
           4: by destruct d. 4: by destruct d. 4: destruct d; done.
           4: { rewrite /becomes_disabled in HX|-*. destruct d.
                1: rewrite -SameRel //. rewrite SameRel //. }
           2: destruct Hptrans; by simplify_eq.
           2: destruct Hptrans; by simplify_eq.
           econstructor 5. 3: by simplify_eq.
           3: { rewrite -ItAcc1Cell -ItAcc2Cell. done. }
           all: eapply parent_has_disabled_perm_is_pseudo_disabled; by destruct d. }
      simpl in *. rewrite -SameProt in tmp2Spec,perm2Spec.
      (* We can finally start the big case analysis at the level of the state machine *)
      edestruct (most_init ini _), perm1, perm2, (bool_decide (protector_is_active (iprot it1) C)); try congruence.
      all: injection tmp1Spec; intros; subst; clear tmp1Spec.
      all: injection tmp2Spec; intros; subst; clear tmp2Spec.
      all: destruct kind, (rel_dec _ _ _) eqn:relation, confl1; simpl in *; try discriminate.
      all: destruct confl2; simpl in *; try discriminate.
      all: try (injection perm1Spec; intros; subst); clear perm1Spec.
      all: try (injection perm2Spec; intros; subst); clear perm2Spec.
      all: try by econstructor 1.
      all: try by econstructor 6.
    - (* asymmetric *)
      rewrite bind_Some in ItAcc1; destruct ItAcc1 as [perms1' [PermsAcc1 it1'Spec]].
      injection it1'Spec; intros; subst; clear it1'Spec.
      rewrite bind_Some in ItAcc2; destruct ItAcc2 as [perms2' [PermsAcc2 it2'Spec]].
      injection it2'Spec; intros; subst; clear it2'Spec.
      simpl.
      pose proof (mem_apply_range'_spec _ _ l _ _ PermsAcc1) as Perms1'Spec.
      pose proof (mem_apply_range'_spec _ _ l _ _ PermsAcc2) as Perms2'Spec.
      rewrite /item_lookup /= in itLookup1,itLookup2.
      destruct (decide _); last first.
      { rewrite /item_lookup /= Perms1'Spec Perms2'Spec -itLookup1 -itLookup2.
        econstructor 7. done. }
      destruct Perms1'Spec as [p1' [LookupSome1' PermAcc1]].
      destruct Perms2'Spec as [p2' [LookupSome2' PermAcc2]].
      rewrite -itLookup1 in PermAcc1.
      rewrite -itLookup2 in PermAcc2.
      rewrite -SameProt -SameTg -SameRel in PermAcc2.
      edestruct maybe_non_children_only_effect_or_nop as [Heq|Heq]; erewrite Heq in PermAcc1, PermAcc2; clear Heq.
      2: { injection PermAcc1 as <-; injection PermAcc2 as <-.
           rewrite /item_lookup /= LookupSome1' LookupSome2' /=. by econstructor 7. }
      destruct ini, d, kind, (rel_dec tr1 acc_tg (itag it1)); simpl in *.
      all: inversion H1 as [P|P]; subst P p1 p2; [
             rewrite bool_decide_eq_false_2 // in PermAcc1,PermAcc2
           | rewrite bool_decide_eq_true_2 // in PermAcc1,PermAcc2].
      all: rewrite /apply_access_perm /apply_access_perm_inner /= in PermAcc1,PermAcc2;
           try discriminate PermAcc1; try discriminate PermAcc2;
           injection PermAcc1 as <-; injection PermAcc2 as <-.
      all: rewrite /item_lookup /= LookupSome1' LookupSome2' /=.
      all: try econstructor 1.
      all: econstructor 7; simpl; econstructor; done.
  Qed.

  Lemma item_eq_up_to_C_preserved_by_access (b : bool)
    {d tr1 tr1' tr2 tr2' it1 it1' it2 it2' tg acc_tg kind range} (Hunq1 : wf_tree tr1) (Hunq2 : wf_tree tr2)
    (SameTg : itag it1 = itag it2)
    (SameRel : forall tg tg', rel_dec tr1 tg tg' = rel_dec tr2 tg tg')
    :
    parents_more_active tr1 →
    no_active_cousins C tr1 →
    parents_more_active tr2 →
    no_active_cousins C tr2 →
    tree_equal C d tr1 tr2 →
    item_eq_up_to_C C tr1 tr2 tg d it1 it2 ->
    tree_apply_access (maybe_non_children_only b (apply_access_perm kind)) C acc_tg range tr1 = Some tr1' ->
    tree_apply_access (maybe_non_children_only b (apply_access_perm kind)) C acc_tg range tr2 = Some tr2' ->
    tree_lookup tr1 tg it1 ->
    tree_lookup tr1' tg it1' ->
    tree_lookup tr2 tg it2 ->
    tree_lookup tr2' tg it2' ->
    tree_contains acc_tg tr1 ->
    tree_contains acc_tg tr2 ->
    item_apply_access (maybe_non_children_only b (apply_access_perm kind)) C (rel_dec tr1 acc_tg (itag it1)) range it1 = Some it1' ->
    item_apply_access (maybe_non_children_only b (apply_access_perm kind)) C (rel_dec tr2 acc_tg (itag it2)) range it2 = Some it2' ->
    item_eq_up_to_C C tr1' tr2' tg d it1' it2'.
  Proof.
    intros ????? EqC Acc1 Acc2 Lookup1 Lookup1' Lookup2 Lookup2' AccTg1 AccTg2 ItAcc1 ItAcc2.
    econstructor.
    - rewrite <- (proj1 (proj2 (item_apply_access_preserves_metadata _ _ ItAcc1))).
      rewrite <- (proj1 (proj2 (item_apply_access_preserves_metadata _ _ ItAcc2))).
      apply EqC. assumption.
    - eapply perm_eq_up_to_C_preserved_by_access.
      + done.
      + apply EqC. assumption.
      + apply SameTg.
      + apply SameRel.
      + eassumption.
      + eassumption.
      + eassumption.
      + eassumption.
      + eassumption.
      + eassumption.
      + eassumption.
      + apply EqC.
      + eassumption.
      + eassumption.
      + eassumption.
      + eassumption.
      + eassumption.
      + eassumption.
      + eassumption.
      + eassumption.
      + eassumption.
      + eassumption.
  Qed.

  Lemma tree_equal_preserved_by_access_maybe_nonchildren_only (b : bool)
    {d tr1 tr2 tr1' tr2' kind acc_tg range}
    (GloballyUnique1 : forall tg, tree_contains tg tr1 -> tree_unique tg tr1)
    (GloballyUnique2 : forall tg, tree_contains tg tr2 -> tree_unique tg tr2)
    :
    parents_more_active tr1 →
    no_active_cousins C tr1 →
    parents_more_active tr2 →
    no_active_cousins C tr2 →
    tree_equal C d tr1 tr2 ->
    tree_contains acc_tg tr1 ->
    tree_apply_access (maybe_non_children_only b (apply_access_perm kind)) C acc_tg range tr1 = Some tr1' ->
    tree_apply_access (maybe_non_children_only b (apply_access_perm kind)) C acc_tg range tr2 = Some tr2' ->
    tree_equal C d tr1' tr2'.
  Proof.
    intros ???? Heq. pose proof Heq as [SameTg [SameRel EqC]]. intros ExAcc Acc1 Acc2.
    split; [|split].
    - intros tg.
      rewrite <- (access_preserves_tags Acc1).
      rewrite <- (access_preserves_tags Acc2).
      apply SameTg.
    - intros tg tg'.
      rewrite <- (access_same_rel_dec Acc1).
      rewrite <- (access_same_rel_dec Acc2).
      apply SameRel.
    - intros tg Ex1'.
      pose proof (proj2 (access_preserves_tags Acc1) Ex1') as Ex1.
      pose proof (proj1 (SameTg _) Ex1) as Ex2.
      pose proof (proj1 (access_preserves_tags Acc2) Ex2) as Ex2'.
      destruct (EqC tg Ex1) as [it1 [it2 [Lookup1 [Lookup2 EqC12]]]].
      destruct (apply_access_spec_per_node Ex1 (proj2 Lookup1) Acc1) as [it1' [it1'Spec [_ Lookup1']]].
      destruct (apply_access_spec_per_node Ex2 (proj2 Lookup2) Acc2) as [it2' [it2'Spec [_ Lookup2']]].
      exists it1'. exists it2'.
      split; [|split].
      + split; assumption.
      + split; assumption.
      + eapply item_eq_up_to_C_preserved_by_access.
        * exact GloballyUnique1.
        * exact GloballyUnique2.
        * erewrite tree_lookup_correct_tag; [|exact Lookup1].
          erewrite tree_lookup_correct_tag; [|exact Lookup2].
          reflexivity.
        * eassumption.
        * eassumption.
        * eassumption.
        * eassumption.
        * eassumption.
        * eassumption.
        * eassumption.
        * eassumption.
        * eassumption.
        * eassumption.
        * split; eassumption.
        * eassumption.
        * split; eassumption.
        * eassumption.
        * by eapply SameTg.
        * symmetry; assumption.
        * symmetry; assumption.
  Qed.

  Lemma tree_equal_preserved_by_memory_access
    {d tr1 tr2 tr1' tr2' kind acc_tg range}
    (GloballyUnique1 : forall tg, tree_contains tg tr1 -> tree_unique tg tr1)
    (GloballyUnique2 : forall tg, tree_contains tg tr2 -> tree_unique tg tr2)
    :
    parents_more_active tr1 →
    no_active_cousins C tr1 →
    parents_more_active tr2 →
    no_active_cousins C tr2 →
    tree_equal C d tr1 tr2 ->
    tree_contains acc_tg tr1 ->
    memory_access kind C acc_tg range tr1 = Some tr1' ->
    memory_access kind C acc_tg range tr2 = Some tr2' ->
    tree_equal C d tr1' tr2'.
  Proof.
    by eapply (tree_equal_preserved_by_access_maybe_nonchildren_only false).
  Qed.

  Lemma tree_equal_preserved_by_memory_access_nonchildren_only
    {d tr1 tr2 tr1' tr2' kind acc_tg range}
    (GloballyUnique1 : forall tg, tree_contains tg tr1 -> tree_unique tg tr1)
    (GloballyUnique2 : forall tg, tree_contains tg tr2 -> tree_unique tg tr2)
    :
    parents_more_active tr1 →
    no_active_cousins C tr1 →
    parents_more_active tr2 →
    no_active_cousins C tr2 →
    tree_equal C d tr1 tr2 ->
    tree_contains acc_tg tr1 ->
    memory_access_nonchildren_only kind C acc_tg range tr1 = Some tr1' ->
    memory_access_nonchildren_only kind C acc_tg range tr2 = Some tr2' ->
    tree_equal C d tr1' tr2'.
  Proof.
    by eapply (tree_equal_preserved_by_access_maybe_nonchildren_only true).
  Qed.

  Lemma tree_equal_memory_deallocate
    {d tr1 tr2 tr1' tr2' acc_tg range}
    (GloballyUnique1 : forall tg, tree_contains tg tr1 -> tree_unique tg tr1)
    (GloballyUnique2 : forall tg, tree_contains tg tr2 -> tree_unique tg tr2)
    :
    parents_more_active tr1 →
    no_active_cousins C tr1 →
    parents_more_active tr2 →
    no_active_cousins C tr2 →
    tree_equal C d tr1 tr2 ->
    tree_contains acc_tg tr1 ->
    memory_deallocate C acc_tg range tr1 = Some tr1' ->
    memory_deallocate C acc_tg range tr2 = Some tr2' ->
    tree_equal C d tr1' tr2'.
  Proof.
    intros ???? Heq Hcontains (pw1&Hacc1&<-%join_map_id_is_Some_identical)%bind_Some
                         (pw2&Hacc2&<-%join_map_id_is_Some_identical)%bind_Some.
    by eapply (@tree_equal_preserved_by_memory_access d tr1 tr2).
  Qed.


  Lemma trees_equal_preserved_by_access
    {d blk tr1 tr2 tr1' tr2' kind acc_tg range}
    :
    wf_trees tr1 →
    wf_trees tr2 →
    each_tree_parents_more_active tr1 →
    each_tree_parents_more_active tr2 →
    each_tree_no_active_cousins C tr1 →
    each_tree_no_active_cousins C tr2 →
    trees_equal C d tr1 tr2 ->
    trees_contain acc_tg tr1 blk ->
    apply_within_trees (memory_access kind C acc_tg range) blk tr1 = Some tr1' ->
    apply_within_trees (memory_access kind C acc_tg range) blk tr2 = Some tr2' ->
    trees_equal C d tr1' tr2'.
  Proof.
    intros (Hwf1&_) (Hwf2&_) Hwx1 Hwx2 Hwy1 Hwy2 Heq Hcont.
    intros ((tr1blk & tr1blk' & Hlutr1 & Hlutr1' & Hacc1) & Htr1nblk)%apply_within_trees_lookup.
    intros ((tr2blk & tr2blk' & Hlutr2 & Hlutr2' & Hacc2) & Htr2nblk)%apply_within_trees_lookup.
    intros blk'. destruct (decide (blk = blk')) as [<- | Hne];
      last rewrite -Htr1nblk // -Htr2nblk //.
    rewrite Hlutr1' Hlutr2'. econstructor.
    specialize (Heq blk).
    rewrite Hlutr1 Hlutr2 in Heq.
    inversion Heq as [x1 x2 Heq1|]; subst x1 x2. (* yikes *)
    eapply tree_equal_preserved_by_memory_access. 9,10: done. 7: done.
    7: rewrite /trees_contain /trees_at_block Hlutr1 // in Hcont.
    3: by eapply Hwx1. 3: by eapply Hwy1. 3: by eapply Hwx2. 3: by eapply Hwy2.
    all: eapply wf_tree_tree_unique; 
      (match goal with [ H : each_tree_wf _ |- _] => by eapply H end).
  Qed.

End utils.

