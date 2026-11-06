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

  Lemma access_preserves_pseudo_disabled lp pr (b:bool)
    {tr tg l kind acc_tg range tr'} :
    pseudo_disabled C tr tg l lp pr ->
    tree_apply_access (maybe_non_children_only b (apply_access_perm kind)) C acc_tg range tr = Some tr' ->
    pseudo_disabled C tr' tg l lp pr.
  Proof.
    intros PseudoC Acc.
    inversion PseudoC as [|tg_cous it_cous X1 X2 cous_rel [cous_ex cous_det] cous_nondis cous_init Hextra]; simplify_eq.
    1: econstructor 1.
    destruct (apply_access_spec_per_node cous_ex cous_det Acc)
          as (cous' & cous'_spec & cous'_ex & cous'_det).
    symmetry in cous'_spec.
    rewrite bind_Some in cous'_spec.
    destruct cous'_spec as (perms' & perms'_spec & cous'_build).
    injection cous'_build; intros; subst; clear cous'_build.
    pose proof (mem_apply_range'_spec _ _ l _ _ perms'_spec) as effect_at_l.
    destruct (decide _); last first.
    + (* out of range is a lot easier *)
      econstructor 2.
      * erewrite <- access_same_rel_dec; eassumption.
      * split; eassumption.
      * eassumption.
      * rewrite /item_lookup /= effect_at_l. assumption.
      * done.
      * done.
    + (* within range. Big case analysis incoming. *)
      destruct effect_at_l as (perm' & perm'_lookup & perm'_spec).
      rewrite /item_lookup in cous_init. rewrite cous_init in perm'_spec.
      rewrite bool_decide_true in perm'_spec. 2: done.
      destruct b, kind, rel_dec as [[]|] in perm'_spec; cbv in perm'_spec.
      all: try discriminate perm'_spec.
      all: injection perm'_spec as <-.
      all: econstructor 2;
           [ erewrite <- access_same_rel_dec; eassumption
           | split; eassumption
           | done
           | rewrite /item_lookup perm'_lookup /= //
           | done
           | done
           ].
  Qed.

  Lemma disabled_tree_apply_access_irreversible
    {tr tr' tg acc_tg kind range loc b it}
    (Lookup : tree_lookup tr tg it)
    (Dis : perm (item_lookup it loc) = Disabled)
    (Acc : tree_apply_access (maybe_non_children_only b (apply_access_perm kind)) C acc_tg range tr = Some tr')
    : exists it',
        tree_lookup tr' tg it'
        /\ perm (item_lookup it' loc) = Disabled.
  Proof.
    destruct (apply_access_spec_per_node (proj1 Lookup) (proj2 Lookup) Acc) as [it' [Spec' [Ex' Det']]].
    exists it'.
    split; first done.
    symmetry in Spec'.
    rewrite bind_Some in Spec'. destruct Spec' as [tmp [PermsApp Build]].
    injection Build; intros; subst; clear Build.
    pose proof (mem_apply_range'_spec _ _ loc _ _ PermsApp) as LocSpec.
    destruct (decide _).
    + destruct LocSpec as [val [LookupVal SpecVal]].
      rewrite /item_lookup LookupVal /=.
      rewrite /maybe_non_children_only /nonchildren_only in SpecVal.
      repeat case_match.
      1: { injection SpecVal; intros; subst; done. }
      all: rewrite /apply_access_perm /apply_access_perm_inner /= in SpecVal.
      all: rewrite Dis /= in SpecVal.
      all: repeat case_match; simpl in *; try congruence.
      all: injection SpecVal; intros; subst; simpl; done.
    + rewrite /item_lookup /= LocSpec Dis //.
  Qed.

  Lemma is_disabled_tree_apply_access_child
    {tr tr' tg acc_tg kind range loc b it}
    (Lookup : tree_lookup tr tg it)
    (Dis : is_disabled C tr tg loc (item_lookup it loc) (iprot it))
    (Cont : tree_contains acc_tg tr)
    (Uni : wf_tree tr)
    (Inside : range'_contains range loc)
    (Acc : tree_apply_access (maybe_non_children_only b (apply_access_perm kind)) C acc_tg range tr = Some tr')
    : ¬ ParentChildIn tg acc_tg tr.
  Proof.
    intros HPC.
    destruct (apply_access_spec_per_node (proj1 Lookup) (proj2 Lookup) Acc) as [it' [Spec' [Ex' Det']]].
    symmetry in Spec'.
    rewrite bind_Some in Spec'. destruct Spec' as [tmp [PermsApp Build]].
    injection Build; intros; subst; clear Build.
    pose proof (mem_apply_range'_spec _ _ loc _ _ PermsApp) as LocSpec.
    eapply tree_lookup_correct_tag in Lookup as HH; subst tg.
    rewrite decide_True // in LocSpec.
    destruct LocSpec as (v&Hv&HHv).
    destruct (decide (perm (item_lookup it loc) = Disabled)) as [Hdis|Hnondis].
    { rewrite /rel_dec decide_True // in HHv.
      rewrite maybe_non_children_only_no_effect // in HHv.
      rewrite /apply_access_perm /apply_access_perm_inner /= Hdis in HHv.
      by destruct kind. }
    inversion Dis as [X1 Hlu X2|lp X1 Hdis Hlu X2]; simplify_eq.
    1: rewrite -Hlu in Hnondis; done.
    inversion Hdis as [X1 X2 X3|tg_cs it_cs X1 X2 Hcs Hlucs Hprotcs Hppcs Hcsfoo X3 X4]; simplify_eq.
    1: rewrite -Hlu in Hnondis; done.
    destruct (apply_access_spec_per_node (proj1 Hlucs) (proj2 Hlucs) Acc) as [itcs' [Speccs' Hlucs']].
    symmetry in Speccs'.
    rewrite bind_Some in Speccs'. destruct Speccs' as [tmpcs [PermsAppcs [= <-]]].
    pose proof (mem_apply_range'_spec _ _ loc _ _ PermsAppcs) as LocSpeccs.
    rewrite decide_True // in LocSpeccs.
    destruct LocSpeccs as [valcs [Hvcs HHvcs]].
    rewrite /rel_dec in HHvcs.
    eapply tree_lookup_correct_tag in Hlucs' as HH; subst tg_cs.
    rewrite decide_False in HHvcs; last first.
    { intros HnPCI1. eapply cousins_have_disjoint_children in Hcs. 5: done. 5: done.
      1: done. all: simpl; eapply Uni. 1: done. 1: apply Lookup. 1: eapply Hlucs. }
    rewrite decide_False in HHvcs; last first.
    { intros HnPCI1.
      rewrite /rel_dec in Hcs.
      destruct decide as [?|HNP2] in Hcs; first done.
      destruct decide as [?|HNP3] in Hcs; first done.
      eapply HNP3; simpl. eapply ParentChild_transitive.
      1: done. done. }
    rewrite maybe_non_children_only_no_effect // in HHvcs.
    rewrite bool_decide_true // in HHvcs.
    rewrite /item_lookup in Hppcs.
    rewrite Hppcs in HHvcs. destruct kind; done.
  Qed.

  Lemma is_disabled_tree_apply_access_irreversible
    {tr tr' tg acc_tg kind range loc b it}
    (Lookup : tree_lookup tr tg it)
    (Dis : is_disabled C tr tg loc (item_lookup it loc) (iprot it))
    (Cont : tree_contains acc_tg tr)
    (Uni : wf_tree tr)
    (Acc : tree_apply_access (maybe_non_children_only b (apply_access_perm kind)) C acc_tg range tr = Some tr')
    : exists it',
        tree_lookup tr' tg it' ∧ iprot it = iprot it' ∧
        is_disabled C tr' tg loc (item_lookup it' loc) (iprot it').
  Proof.
    destruct (apply_access_spec_per_node (proj1 Lookup) (proj2 Lookup) Acc) as [it' [Spec' [Ex' Det']]].
    exists it'.
    split; first done.
    symmetry in Spec'.
    rewrite bind_Some in Spec'. destruct Spec' as [tmp [PermsApp Build]].
    injection Build; intros; subst; clear Build. split; first done.
    destruct (decide (perm (item_lookup it loc) = Disabled)) as [Hdis|Hnondis].
    { eapply disabled_tree_apply_access_irreversible in Hdis as (it'&Htr'&Hit'). 2-3: done.
      eapply tree_determined_unify in Det'. 2: done. 2: apply Htr'.
      destruct (item_lookup it' loc) as [[] pp] eqn:Hini; subst it'.
      all: rewrite Hini. all: simpl in Hit'; subst pp.
      1: econstructor 1. 1: econstructor 2. econstructor 1. }
    pose proof (mem_apply_range'_spec _ _ loc _ _ PermsApp) as LocSpec.
    inversion Dis as [X1 Hlu X2|lp X1 Hdis Hlu X2]; simplify_eq.
    1: rewrite -Hlu in Hnondis; done.
    inversion Hdis as [X1 X2 X3|tg_cs it_cs X1 X2 Hcs Hlucs Hprotcs Hppcs Hcsfoo X3 X4]; simplify_eq.
    1: rewrite -Hlu in Hnondis; done.
    destruct (apply_access_spec_per_node (proj1 Hlucs) (proj2 Hlucs) Acc) as [itcs' [Speccs' Hlucs']].
    symmetry in Speccs'.
    rewrite bind_Some in Speccs'. destruct Speccs' as [tmpcs [PermsAppcs [= <-]]].
    pose proof (mem_apply_range'_spec _ _ loc _ _ PermsAppcs) as LocSpeccs.
    destruct (decide _) as [In|Out]; last first.
    + rewrite /item_lookup /= LocSpec.
      rewrite /item_lookup in Hlu. rewrite -Hlu.
      econstructor. eapply access_preserves_pseudo_disabled. 1: done. done.
    + destruct LocSpec as [val [LookupVal SpecVal]].
      destruct LocSpeccs as [valcs [LookupValcs SpecValcs]].
      rewrite /rel_dec in SpecVal.
      eapply tree_lookup_correct_tag in Lookup as HH; subst tg.
      eapply tree_lookup_correct_tag in Hlucs' as HH; subst tg_cs.
      rewrite decide_False in SpecVal.
      2: { eapply is_disabled_tree_apply_access_child. 6: done. 2: done. all: done. }
      edestruct maybe_non_children_only_effect_or_nop as [Heff|Heff];
      erewrite Heff in SpecVal; clear Heff.
      2: { injection SpecVal as <-. simpl.
           rewrite /item_lookup /= in Hlu|-*.
           rewrite LookupVal /= -Hlu.
           econstructor 2. eapply access_preserves_pseudo_disabled; last done.
           done. }
      rewrite /item_lookup in Hlu. rewrite -Hlu in SpecVal.
      rewrite /apply_access_perm /apply_access_perm_inner most_init_comm /= in SpecVal.
      destruct kind, bool_decide eqn:Hbdc, lp as [|[]| | | |] eqn:Hpm in SpecVal.
      all: simpl in SpecVal. all: try discriminate SpecVal.
      all: injection SpecVal as <-.
      all: rewrite /= /item_lookup /= LookupVal /=.
      all: econstructor 2.
      all: eapply access_preserves_pseudo_disabled; last done.
      all: econstructor; [exact Hcs|exact Hlucs|exact Hprotcs|exact Hppcs| |].
      all: intros [=].
      all: subst lp; eapply Hcsfoo; done.
  Qed.

  Definition becomes_frozen (kind : access_kind) (range : Z * nat) (loc : Z) (b:bool) tr acc_tg it_tg: Prop :=
    if decide (range'_contains range loc) then kind = AccessRead ∨ (∃ k, b = true ∧ rel_dec tr acc_tg it_tg = Foreign (Parent k)) else True.
  Definition becomes_disabled (kind : access_kind) (range : Z * nat) (loc : Z) (b:bool) tr acc_tg it_tg: Prop :=
    if decide (range'_contains range loc) then kind = AccessWrite ∧ (∃ f, rel_dec tr acc_tg it_tg = Foreign f ∧ ∀ p, f = Parent p → b = false) else False.

  Lemma becomes_not_both kind range loc b tr acc_tg it_tg :
    becomes_frozen kind range loc b tr acc_tg it_tg →
    becomes_disabled kind range loc b tr acc_tg it_tg →
    False.
  Proof.
    intros H1 H2.
    rewrite /becomes_frozen /becomes_disabled in H1,H2.
    destruct decide. 2: done.
    destruct H2 as (->&f&Hff&Hfb).
    destruct H1 as [[=]|(k&->&Hk)].
    rewrite Hk in Hff. simplify_eq.
    by specialize (Hfb _ eq_refl).
  Qed.

  Lemma cell_item_apply_access_irreversible
    {rd kind range b it it'}
    (Spec' : item_apply_access (maybe_non_children_only b (apply_access_perm kind)) C rd range it = Some it')
    : ∀ l, perm (item_lookup it l) = Cell ↔ perm (item_lookup it' l) = Cell.
  Proof.
    rewrite bind_Some in Spec'. destruct Spec' as [tmp [PermsApp Build]].
    intros loc.
    injection Build; intros; subst; clear Build.
    pose proof (mem_apply_range'_spec _ _ loc _ _ PermsApp) as LocSpec.
    destruct (decide _); last first.
    + rewrite /item_lookup /= LocSpec //.
    + destruct LocSpec as [val [LookupVal SpecVal]].
      rewrite /item_lookup LookupVal /=.
      rewrite /maybe_non_children_only /nonchildren_only in SpecVal.
      rewrite /= /apply_access_perm /apply_access_perm_inner in SpecVal.
      destruct (default {| initialized := PermLazy; perm := initp it |} (iperm it !! loc)) eqn:Heq.
      rewrite Heq in SpecVal.
      repeat (case_match; simpl in *; simplify_eq; (try done); try (simpl; tauto)).
  Qed.

  Lemma cell_tree_apply_access_irreversible
    {tr tr' tg acc_tg kind range b it}
    (Lookup : tree_lookup tr tg it)
    (Acc : tree_apply_access (maybe_non_children_only b (apply_access_perm kind)) C acc_tg range tr = Some tr')
    : exists it',
        tree_lookup tr' tg it'
        /\ ∀ l, perm (item_lookup it l) = Cell ↔ perm (item_lookup it' l) = Cell.
  Proof.
    destruct (apply_access_spec_per_node (proj1 Lookup) (proj2 Lookup) Acc) as [it' [Spec' [Ex' Det']]].
    exists it'.
    split; first done.
    symmetry in Spec'.
    eapply cell_item_apply_access_irreversible. exact Spec'.
  Qed.

  Lemma frozen_tree_apply_access_irreversible
    {tr tr' tg acc_tg kind range loc b it}
    (Lookup : tree_lookup tr tg it)
    (Frz : (item_lookup it loc).(perm) = Frozen)
    (Ini : (item_lookup it loc).(initialized) = PermInit)
    (Acc : tree_apply_access (maybe_non_children_only b (apply_access_perm kind)) C acc_tg range tr = Some tr')
    : exists it',
        tree_lookup tr' tg it'
        /\ let k := (item_lookup it' loc) in let bf := becomes_frozen kind range loc b tr acc_tg (itag it) in let bd := becomes_disabled kind range loc b tr acc_tg (itag it) in
            k.(initialized) = PermInit
           /\ (k.(perm) = Frozen ∧ bf ∨ (k.(perm) = Disabled ∧ bd ∧ ¬ protector_is_active it'.(iprot) C)).
  Proof.
    destruct (apply_access_spec_per_node (proj1 Lookup) (proj2 Lookup) Acc) as [it' [Spec' [Ex' Det']]].
    exists it'.
    split; first done.
    symmetry in Spec'.
    rewrite bind_Some in Spec'. destruct Spec' as [tmp [PermsApp Build]].
    intros k bf bd.
    injection Build; intros; subst; clear Build.
    pose proof (mem_apply_range'_spec _ _ loc _ _ PermsApp) as LocSpec. subst bf bd. rewrite /becomes_frozen /becomes_disabled.
    destruct (decide _); last first.
    + subst k. rewrite /item_lookup /= LocSpec Frz Ini //. split; first done. by left.
    + destruct LocSpec as [val [LookupVal SpecVal]]. subst k.
      rewrite /item_lookup LookupVal /=.
      rewrite /maybe_non_children_only /nonchildren_only in SpecVal.
      repeat case_match.
      1: { injection SpecVal; intros; subst; split; first done. left. split; first done. eauto. }
      all: rewrite /apply_access_perm /apply_access_perm_inner /= in SpecVal.
      all: rewrite Frz /= Ini /= in SpecVal.
      all: repeat case_match; simpl in *; try congruence.
      all: injection SpecVal; intros; subst; simpl; split; first done.
      all: first [ left; split; first done; eauto | right; split; first done; split ].
      2, 4: by eapply bool_decide_eq_false_1.
      all: split; first done.
      all: eexists; split; first done.
      1: intros ? [=]. done.
  Qed.

  Lemma parent_has_perm_similarly_disabled_after_access
    {pp tr tr' tg acc_tg kind range loc b it}
    (Lookup : tree_lookup tr tg it)
    (Frz : (item_lookup it loc).(perm) = pp)
    (nRIM : pp ≠ ReservedIM)
    (nCell : pp ≠ Cell)
    (Ini : (item_lookup it loc).(initialized) = PermInit)
    (Acc : tree_apply_access (maybe_non_children_only b (apply_access_perm kind)) C acc_tg range tr = Some tr')
    : exists it',
        tree_lookup tr' tg it'
        /\ let k := (item_lookup it' loc) in let bd := becomes_disabled kind range loc b tr acc_tg (itag it) in
            k.(initialized) = PermInit
           /\ (bd → (k.(perm) = Disabled ∧ ¬ protector_is_active it'.(iprot) C)).
  Proof.
    destruct (apply_access_spec_per_node (proj1 Lookup) (proj2 Lookup) Acc) as [it' [Spec' [Ex' Det']]].
    exists it'.
    split; first done.
    symmetry in Spec'.
    rewrite bind_Some in Spec'. destruct Spec' as [tmp [PermsApp Build]].
    intros k bd.
    injection Build; intros; subst; clear Build.
    pose proof (mem_apply_range'_spec _ _ loc _ _ PermsApp) as LocSpec. subst bd. rewrite /becomes_disabled.
    destruct (decide _); last first.
    + subst k. rewrite /item_lookup /= LocSpec Ini //.
    + destruct LocSpec as [val [LookupVal SpecVal]]. subst k.
      rewrite /item_lookup LookupVal /=.
      rewrite /maybe_non_children_only /nonchildren_only in SpecVal.
      repeat case_match.
      1: { injection SpecVal; intros; subst; split; first done. intros (->&f&[= <-]&HH). by specialize (HH _ eq_refl). }
      all: rewrite /apply_access_perm /apply_access_perm_inner /= in SpecVal.
      all: rewrite /= Ini /= in SpecVal.
      all: repeat case_match; simpl in *; try congruence.
      all: injection SpecVal; intros; subst; simpl; split; first done.
      all: intros (Heq1&Hf&Heq2&HHf); simplify_eq.
      all: split; last try by eapply bool_decide_eq_false_1.
      all: done.
  Qed.

  Lemma disabled_in_practice_tree_apply_access_irreversible
    {tr tr' tg acc_tg kind range witness loc b}
    (Dis : disabled_in_practice C tr tg witness loc)
    (Cont : tree_contains acc_tg tr)
    (Uni : wf_tree tr)
    (Acc : tree_apply_access (maybe_non_children_only b (apply_access_perm kind)) C acc_tg range tr = Some tr')
    : disabled_in_practice C tr' tg witness loc.
  Proof.
    inversion Dis as [?? Rel Lookup Perm].
    destruct (is_disabled_tree_apply_access_irreversible Lookup Perm Cont Uni Acc) as [it' [Lookup' Perm']].
    econstructor.
    + erewrite <- access_same_rel_dec; eassumption.
    + apply Lookup'.
    + apply Perm'.
  Qed.

  Definition disabled_tag_at_tree_apply_access_irreversible
    {tr tr' tg acc_tg kind range loc b}
    (Dis : disabled_tag_at C tr tg loc)
    (Cont : tree_contains acc_tg tr)
    (Uni : wf_tree tr)
    (Acc : tree_apply_access (maybe_non_children_only b (apply_access_perm kind)) C acc_tg range tr = Some tr')
    : disabled_tag_at C tr' tg loc.
  Proof.
    destruct Dis as (w&Dis).
    exists w. eapply disabled_in_practice_tree_apply_access_irreversible; done.
  Qed.

  Definition disabled_tag_tree_apply_access_irreversible
    {trs trs' tg acc_tg kind range blk l b nxtp}
    (Dis : disabled_tag C trs nxtp tg l)
    (Cont : trees_contain acc_tg trs blk)
    (Uni : wf_trees trs)
    (Acc : apply_within_trees (tree_apply_access (maybe_non_children_only b (apply_access_perm kind)) C acc_tg range) blk trs = Some trs')
    : disabled_tag C trs' nxtp tg l.
  Proof.
    eapply bind_Some in Acc as (tr&Htr&(tr'&Acc&[= <-])%bind_Some).
    destruct (decide (blk = l.1)) as [->|Hne]; last first.
    { rewrite /disabled_tag lookup_insert_ne //. }
    rewrite /trees_contain /trees_at_block Htr in Cont.
    destruct Dis as (Hv&Dis). split; first done.
    rewrite lookup_insert_eq. rewrite Htr in Dis.
    destruct Dis as [Dis|Nd].
    - left. eapply disabled_tag_at_tree_apply_access_irreversible. 1,2,4: done.
      by eapply Uni.
    - right. intros Hc. eapply Nd,access_preserves_tags. 1: exact Acc. done.
  Qed.

End utils.

