(** Abstraction layer for trees.
    The goal of this file is that lemmas that appear here expose as few internal details
    as possible. In particular they should all refer to [trees] in their signature (NOT [tree]). 

    At least that was the plan. Turns out sometimes you need the single-tree lemmas.*)
From iris.proofmode Require Export proofmode.
From iris.base_logic.lib Require Import ghost_map.
From simuliris.base_logic Require Export gen_sim_prog.
From simuliris.simulation Require Export slsls.
From simuliris.simulation Require Import lifting.
From simuliris.tree_borrows Require Import tkmap_view.
From simuliris.tree_borrows Require Export defs class_instances.
From simuliris.tree_borrows Require Import steps_progress steps_inv.
From simuliris.tree_borrows Require Import logical_state inv_accessors.
From simuliris.tree_borrows.trees_equal Require Export trees_equal_base random_lemmas.

(***** not part of the API *****)
Lemma trees_at_block_projection trs tr blk P :
  trees_at_block P trs blk ->
  trs !! blk = Some tr ->
  P tr.
Proof.
  rewrite /trees_contain /trees_at_block.
  destruct (trs !! blk); [|tauto].
  intros Ex Eq. injection Eq; intros; subst. assumption.
Qed.
(***** END not part of the API *****)

Lemma trees_contain_trees_lookup_1 trs blk tg :
  wf_trees trs →
  trees_contain tg trs blk → ∃ it, trees_lookup trs blk tg it.
Proof.
  intros (wf&_).
  rewrite /trees_contain /trees_lookup /trees_at_block.
  specialize (wf blk).
  destruct (trs !! blk) as [tr|]; [|tauto].
  intros Ex.
  specialize (wf tr ltac:(reflexivity) tg Ex) as Unq.
  destruct (unique_lookup _ _ Unq) as (it & Det).
  exists it, tr. done.
Qed.

Lemma trees_contain_trees_lookup_2 it trs blk tg :
  trees_lookup trs blk tg it → trees_contain tg trs blk.
Proof.
  rewrite /trees_lookup /trees_contain /trees_at_block.
  destruct (trs !! blk); [|intro H; destruct H as [?[??]]; discriminate].
  intro H. destruct H as [?[Eqt Lookup]].
  injection Eqt; intros; subst.
  apply Lookup.
Qed.

Definition trees_rel_dec (trs : trees) blk tg tg' :=
  match trs !! blk with
  | None => Child This
  | Some tr => rel_dec tr tg tg'
  end.

Lemma trees_rel_dec_refl trs blk tg :
  trees_rel_dec trs blk tg tg = Child This.
Proof.
  rewrite /trees_rel_dec.
  destruct (trs !! blk); [|reflexivity].
  apply rel_dec_refl.
Qed.

Lemma apply_trees_access_lookup_inout b cids trs kind blk off1 sz acc_tg lu_tg trs' itold :
  apply_within_trees (memory_access_maybe_nonchildren_only b kind cids acc_tg (off1, sz)) blk trs = Some trs' →
  wf_trees trs →
  trees_lookup trs blk lu_tg itold →
  ∃       itnew, trees_lookup trs' blk lu_tg itnew ∧
                 initp itold = initp itnew ∧
                 iprot itold = iprot itnew ∧ ∀ offi, 
                 let permold := item_lookup itold offi in let permnew := item_lookup itnew offi in
                 (off1 ≤ offi < off1 + sz → maybe_non_children_only b (apply_access_perm kind) (trees_rel_dec trs blk acc_tg lu_tg) (bool_decide (protector_is_active itnew.(iprot) cids)) permold = Some permnew) ∧
                 (¬ (off1 ≤ offi < off1 + sz) → permold = permnew).
Proof.
  intros App (wf&_) Lookup.
  rewrite /apply_within_trees in App.
  rewrite bind_Some in App.
  destruct App as [tr [trSome Acc]].
  rewrite bind_Some in Acc.
  destruct Acc as [tr' [Acc Out]].
  injection Out; intros; subst; clear Out.
  assert (tree_contains lu_tg tr) as Ex. {
    eapply trees_at_block_projection; [|eassumption].
    eapply trees_contain_trees_lookup_2.
    eassumption.
  }
  assert (tree_item_determined lu_tg itold tr) as Det. {
    destruct Lookup as [trbis [trsLookup trLookup]].
    assert (trbis = tr) by congruence. subst.
    apply trLookup.
  }
  destruct (apply_access_spec_per_node Ex Det Acc) as [it' [itAcc [Ex' Det']]].
  exists it'.
  split; [|split; [|split]].
  - exists tr'. split; [apply lookup_insert_eq|]. split; assumption.
  - eapply item_apply_access_preserves_metadata.
    symmetry. eassumption.
  - eapply item_apply_access_preserves_metadata.
    symmetry. eassumption.
  - intros offi. rewrite /item_apply_access in itAcc.
    symmetry in itAcc. rewrite bind_Some in itAcc.
    destruct itAcc as [perms' [perms'Spec Same]].
    injection Same; intros x; subst; clear Same.
    pose proof (mem_apply_range'_spec _ _ offi _ _ perms'Spec) as ThisLocation.
    intros permold permnew.
    split.
    + intros InBounds.
      destruct (decide _); [|unfold range'_contains in *; simpl in *; lia].
      destruct ThisLocation as [perm [permSome permAcc]].
      simpl.
      rewrite /trees_rel_dec trSome.
      assert (itag itold = lu_tg). { eapply tree_determined_specifies_tag; [|eassumption]; assumption. }
      subst. subst permnew.
      rewrite permAcc.
      rewrite /item_lookup /= permSome //=.
    + intros OutOfBounds.
      destruct (decide (range'_contains _ _)) as [Hr|Hr].
      all: rewrite /range'_contains /= in Hr. 1: lia.
      subst permold permnew. rewrite /item_lookup /= ThisLocation //.
Qed.

Lemma apply_trees_access_lookup_general b offi cids trs kind blk off1 sz acc_tg lu_tg trs' itold :
  apply_within_trees (memory_access_maybe_nonchildren_only b kind cids acc_tg (off1, sz)) blk trs = Some trs' →
  wf_trees trs →
  off1 ≤ offi < off1 + sz →
  trees_lookup trs blk lu_tg itold →
  ∃       itnew, trees_lookup trs' blk lu_tg itnew ∧
                 let permold := item_lookup itold offi in let permnew := item_lookup itnew offi in
                 initp itold = initp itnew ∧
                 iprot itold = iprot itnew ∧
                 maybe_non_children_only b (apply_access_perm kind) (trees_rel_dec trs blk acc_tg lu_tg) (bool_decide (protector_is_active itnew.(iprot) cids)) permold = Some permnew.
Proof.
  intros App (wf&_) InBounds Lookup.
  rewrite /apply_within_trees in App.
  rewrite bind_Some in App.
  destruct App as [tr [trSome Acc]].
  rewrite bind_Some in Acc.
  destruct Acc as [tr' [Acc Out]].
  injection Out; intros; subst; clear Out.
  assert (tree_contains lu_tg tr) as Ex. {
    eapply trees_at_block_projection; [|eassumption].
    eapply trees_contain_trees_lookup_2.
    eassumption.
  }
  assert (tree_item_determined lu_tg itold tr) as Det. {
    destruct Lookup as [trbis [trsLookup trLookup]].
    assert (trbis = tr) by congruence. subst.
    apply trLookup.
  }
  destruct (apply_access_spec_per_node Ex Det Acc) as [it' [itAcc [Ex' Det']]].
  exists it'.
  split; [|split; [|split]].
  - exists tr'. split; [apply lookup_insert_eq|]. split; assumption.
  - eapply item_apply_access_preserves_metadata.
    symmetry. eassumption.
  - eapply item_apply_access_preserves_metadata.
    symmetry. eassumption.
  - rewrite /item_apply_access in itAcc.
    symmetry in itAcc. rewrite bind_Some in itAcc.
    destruct itAcc as [perms' [perms'Spec Same]].
    injection Same; intros; subst; clear Same.
    pose proof (mem_apply_range'_spec _ _ offi _ _ perms'Spec) as ThisLocation.
    destruct (decide _); [|unfold range'_contains in *; simpl in *; lia].
    destruct ThisLocation as [perm [permSome permAcc]].
    simpl.
    rewrite /trees_rel_dec trSome.
    assert (itag itold = lu_tg). { eapply tree_determined_specifies_tag; [|eassumption]; assumption. }
    subst.
    rewrite permAcc.
    rewrite /item_lookup /= permSome //=.
Qed.

Lemma apply_trees_access_lookup_outside blki offi cids trs kind blk off1 sz acc_tg lu_tg trs' itold b :
  apply_within_trees (memory_access_maybe_nonchildren_only b kind cids acc_tg (off1, sz)) blk trs = Some trs' →
  wf_trees trs →
  ¬ (blki = blk ∧ off1 ≤ offi < off1 + sz) →
  trees_lookup trs blki lu_tg itold →
  ∃       itnew, trees_lookup trs' blki lu_tg itnew ∧
                 let permold := item_lookup itold offi in let permnew := item_lookup itnew offi in
                 initp itold = initp itnew ∧
                 iprot itold = iprot itnew ∧
                 permold = permnew.
Proof.
  intros App (wf&_) OutOfBounds Lookup.
  rewrite /apply_within_trees in App.
  rewrite bind_Some in App.
  destruct App as [tr [trSome Acc]].
  rewrite bind_Some in Acc.
  destruct Acc as [tr' [Acc Out]].
  injection Out; intros; subst; clear Out.
  destruct (decide (blk = blki)) as [->|Hne]; last first.
  { destruct Lookup as (it & Hit1 & Hit2). exists itold. split_and!; try done.
    exists it; split; last done.
    by rewrite lookup_insert_ne. }
  assert (tree_contains lu_tg tr) as Ex. {
    eapply trees_at_block_projection; [|eassumption].
    eapply trees_contain_trees_lookup_2.
    eassumption.
  }
  assert (tree_item_determined lu_tg itold tr) as Det. {
    destruct Lookup as [trbis [trsLookup trLookup]].
    assert (trbis = tr) by congruence. subst.
    apply trLookup.
  }
  destruct (apply_access_spec_per_node Ex Det Acc) as [itnew [itAcc [Ex' Det']]].
  rewrite /item_apply_access in itAcc. symmetry in itAcc.
  apply bind_Some in itAcc as (permsnew&Hpermsnew&[= Hitnew]).
  exists itnew. split.
  { exists tr'. split; first by rewrite lookup_insert_eq. done. }
  subst itnew. simpl. split_and!; try done.
  rewrite /item_lookup; simpl. f_equal.
  eapply (mem_apply_range'_spec _ _ offi) in Hpermsnew.
  destruct (decide (range'_contains _ _)) as [Hinrange|_]; last done.
  exfalso. eapply OutOfBounds. split; first done. apply Hinrange.
Qed.


Lemma apply_trees_access_lookup_same_tag cids trs kind blk off1 sz offi tg trs' b:
  apply_within_trees (memory_access_maybe_nonchildren_only b kind cids tg (off1, sz)) blk trs = Some trs' →
  wf_trees trs  →
  off1 ≤ offi < off1 + sz →
  trees_contain tg trs blk →
  ∃ itold itnew, trees_lookup trs blk tg itold ∧ trees_lookup trs' blk tg itnew ∧
                 let permold := item_lookup itold offi in let permnew := item_lookup itnew offi in
                 initp itold = initp itnew ∧
                 iprot itold = iprot itnew ∧
                 maybe_non_children_only b (apply_access_perm kind) (Child This) (bool_decide (protector_is_active itnew.(iprot) cids)) permold = Some permnew.
Proof.
  intros App wf InRange Ex.
  destruct (trees_contain_trees_lookup_1 _ _ _ wf Ex) as [itold Lookup].
  destruct (apply_trees_access_lookup_general _ _ _ _ _ _ _ _ _ _ _ _ App wf InRange Lookup) as [itnew newSpec].
  exists itold, itnew.
  rewrite trees_rel_dec_refl in newSpec.
  split; first assumption.
  apply newSpec.
Qed.

Lemma apply_trees_access_lookup_general_rev offi cids trs kind blk off1 sz acc_tg lu_tg trs' itnew b :
  apply_within_trees (memory_access_maybe_nonchildren_only b kind cids acc_tg (off1, sz)) blk trs = Some trs' →
  wf_trees trs →
  off1 ≤ offi < off1 + sz →
  trees_lookup trs' blk lu_tg itnew →
  ∃       itold, trees_lookup trs blk lu_tg itold ∧
                 let permold := item_lookup itold offi in let permnew := item_lookup itnew offi in
                 initp itold = initp itnew ∧
                 iprot itold = iprot itnew ∧
                 maybe_non_children_only b (apply_access_perm kind) (trees_rel_dec trs blk acc_tg lu_tg) (bool_decide (protector_is_active itnew.(iprot) cids)) permold = Some permnew.
Proof.
  intros App WFold InBounds Lookup.
  assert (wf_trees trs') as WFnew.
  { eapply apply_within_trees_wf; try done. eapply memory_access_tag_count. }
  pose proof App as (trold&Htrold&(trnew&Htrnew&[= <-])%bind_Some)%bind_Some.
  destruct Lookup as (tr'&Htr'&Hlookup).
  rewrite lookup_insert_eq in Htr'. injection Htr' as <-.
  pose proof Hlookup as (Hunq&_).
  eapply wf_tree_tree_unique in Hunq; last eapply WFnew, lookup_insert_eq.
  rewrite /tree_unique in Hunq. erewrite <-memory_access_tag_count in Hunq; last done.
  pose proof (unique_exists Hunq) as Hcont.
  apply unique_lookup in Hunq as (itold&Hdet).
  eapply (apply_trees_access_lookup_general _ offi) in App.
  2: done. 3: by eexists. 2: lia.
  destruct App as (itnew' & (trnew' & Htrnew' & Hitnew') & Hperms).
  assert (trnew' = trnew) as ->.
  { rewrite lookup_insert_eq in Htrnew'. congruence. }
  assert (itnew' = itnew) as -> by by eapply tree_lookup_unique.
  exists itold. split; last done.
  by exists trold.
Qed.

Lemma apply_trees_access_lookup_outside_rev blki offi cids trs kind blk off1 sz acc_tg lu_tg trs' itnew b:
  apply_within_trees (memory_access_maybe_nonchildren_only b kind cids acc_tg (off1, sz)) blk trs = Some trs' →
  wf_trees trs →
  ¬ (blki = blk ∧ off1 ≤ offi < off1 + sz) →
  trees_lookup trs' blki lu_tg itnew →
  ∃       itold, trees_lookup trs blki lu_tg itold ∧
                 let permold := item_lookup itold offi in let permnew := item_lookup itnew offi in
                 initp itold = initp itnew ∧
                 iprot itold = iprot itnew ∧
                 permold = permnew.
Proof.
  intros App wf OutOfBounds Lookup.
  assert (wf_trees trs') as wf'.
  { eapply apply_within_trees_wf; try done.
    intros ????. by eapply memory_access_tag_count. }
  pose proof App as App2.
  rewrite /apply_within_trees in App.
  rewrite bind_Some in App.
  destruct App as [tr [trSome Acc]].
  rewrite bind_Some in Acc.
  destruct Acc as [tr' [Acc Out]].
  injection Out; intros; subst; clear Out.
  destruct (decide (blk = blki)) as [->|Hne]; last first.
  { destruct Lookup as (it & Hit1 & Hit2). exists itnew. split_and!; try done.
    exists it; split; last done.
    by rewrite lookup_insert_ne in Hit1. }
  assert (tree_contains lu_tg tr') as Ex. {
    eapply trees_at_block_projection.
    1: eapply trees_contain_trees_lookup_2; eassumption.
    by eapply lookup_insert_eq.
  }
  assert (tree_item_determined lu_tg itnew tr') as NewDet. {
    destruct Lookup as (? & Heq & Hlu). rewrite lookup_insert_eq in Heq.
    injection Heq as <-. apply Hlu.
  }
  assert (tree_unique lu_tg tr) as UnqPre.
  { eapply wf_tree_tree_unique in Ex. 2: eapply wf', lookup_insert_eq.
    rewrite /tree_unique. erewrite tree_apply_access_same_count.
    1: apply Ex.
    apply Acc. }
  pose proof UnqPre as (itold & Hdetold)%unique_lookup.
  assert (trees_lookup trs blki lu_tg itold) as Hluold.
  { exists tr; split; first done. split; last done. by eapply unique_exists. }
  pose proof Hluold as Hluold2.
  eapply apply_trees_access_lookup_outside in Hluold as (itnew' & Hlu2 & HH2).
  2: apply App2.
  - exists itold; split; first done.
    enough (itnew' = itnew) as <- by eapply HH2.
    eapply (tree_lookup_unique tr' lu_tg).
    + destruct Hlu2 as (? & Hx & Hy).
      rewrite lookup_insert_eq in Hx. congruence.
    + destruct Lookup as (? & Hx & Hy).
      rewrite lookup_insert_eq in Hx. congruence.
  - done.
  - apply OutOfBounds.
Qed.

(* Reverse lifting to single trees.
   This is a roundabout of proving these, but we started with the lemmas above
   and this way there is the least refactoring effort. *)

Lemma wf_tree_wf_singleton_any z tr : wf_tree tr → wf_trees (singletonM z tr).
Proof.
  split.
  - intros blk ? (<-&<-)%lookup_singleton_Some. done.
  - intros ???? tg (<-&<-)%lookup_singleton_Some (<-&<-)%lookup_singleton_Some. done.
Qed.

Lemma wf_tree_wf_singleton tr : wf_tree tr → wf_trees (singletonM xH tr).
Proof. by eapply wf_tree_wf_singleton_any. Qed.

Lemma tree_access_lookup_general offi cids tr kind off1 sz acc_tg lu_tg tr' itold b :
  memory_access_maybe_nonchildren_only b kind cids acc_tg (off1, sz) tr = Some tr' →
  wf_tree tr →
  off1 ≤ offi < off1 + sz →
  tree_lookup tr lu_tg itold →
  ∃       itnew, tree_lookup tr' lu_tg itnew ∧
                 let permold := item_lookup itold offi in let permnew := item_lookup itnew offi in
                 initp itold = initp itnew ∧
                 iprot itold = iprot itnew ∧
                 maybe_non_children_only b (apply_access_perm kind) (rel_dec tr acc_tg lu_tg) (bool_decide (protector_is_active itnew.(iprot) cids)) permold = Some permnew.
Proof.
  intros App WFold InBounds Lookup.
  odestruct (apply_trees_access_lookup_general _ _ _ _ _ xH) as (it&H1&H2&H3&H4).
  2: by eapply wf_tree_wf_singleton.
  - rewrite /apply_within_trees lookup_singleton_eq /=. erewrite App. rewrite /= insert_singleton_eq. done.
  - done.
  - exists tr. split; first by eapply lookup_singleton_eq. done.
  - exists it. split_and; try done.
    destruct H1 as (tr1'&H1&H1'). rewrite lookup_singleton_eq in H1. injection H1 as <-. done.
Qed.

Lemma tree_access_lookup_outside offi cids tr kind off1 sz acc_tg lu_tg tr' itold b :
  memory_access_maybe_nonchildren_only b kind cids acc_tg (off1, sz) tr = Some tr' →
  wf_tree tr →
  ¬ (off1 ≤ offi < off1 + sz) →
  tree_lookup tr lu_tg itold →
  ∃       itnew, tree_lookup tr' lu_tg itnew ∧
                 let permold := item_lookup itold offi in let permnew := item_lookup itnew offi in
                 initp itold = initp itnew ∧
                 iprot itold = iprot itnew ∧
                 permold = permnew.
Proof.
  intros App WFold InBounds Lookup.
  odestruct (apply_trees_access_lookup_outside xH offi _ _ _ xH) as (it&H1&H2&H3&H4).
  2: by eapply wf_tree_wf_singleton.
  - rewrite /apply_within_trees lookup_singleton_eq /=. erewrite App. rewrite /= insert_singleton_eq. done.
  - intros (H1&H2). done.
  - exists tr. split; first by eapply lookup_singleton_eq. done.
  - exists it. split_and; try done.
    destruct H1 as (tr''&H1&H1'). rewrite lookup_singleton_eq in H1. injection H1 as <-. done.
Qed.

Lemma tree_access_lookup_general_rev offi cids tr kind off1 sz acc_tg lu_tg tr' itnew b :
  memory_access_maybe_nonchildren_only b kind cids acc_tg (off1, sz) tr = Some tr' →
  wf_tree tr →
  off1 ≤ offi < off1 + sz →
  tree_lookup tr' lu_tg itnew →
  ∃       itold, tree_lookup tr lu_tg itold ∧
                 let permold := item_lookup itold offi in let permnew := item_lookup itnew offi in
                 initp itold = initp itnew ∧
                 iprot itold = iprot itnew ∧
                 maybe_non_children_only b (apply_access_perm kind) (rel_dec tr acc_tg lu_tg) (bool_decide (protector_is_active itnew.(iprot) cids)) permold = Some permnew.
Proof.
  intros App WFold InBounds Lookup.
  odestruct (apply_trees_access_lookup_general_rev _ _ _ _ xH) as (it&H1&H2&H3&H4).
  2: by eapply wf_tree_wf_singleton.
  - rewrite /apply_within_trees lookup_singleton_eq /=. erewrite App. rewrite /= insert_singleton_eq. done.
  - done.
  - exists tr'. split; first by eapply lookup_singleton_eq. done.
  - exists it. split_and; try done.
    destruct H1 as (tr''&H1&H1'). rewrite lookup_singleton_eq in H1. injection H1 as <-. done.
Qed.

Lemma tree_access_lookup_outside_rev offi cids tr kind off1 sz acc_tg lu_tg tr' itnew b :
  memory_access_maybe_nonchildren_only b kind cids acc_tg (off1, sz) tr = Some tr' →
  wf_tree tr →
  ¬ (off1 ≤ offi < off1 + sz) →
  tree_lookup tr' lu_tg itnew →
  ∃       itold, tree_lookup tr lu_tg itold ∧
                 let permold := item_lookup itold offi in let permnew := item_lookup itnew offi in
                 initp itold = initp itnew ∧
                 iprot itold = iprot itnew ∧
                 permold = permnew.
Proof.
  intros App WFold InBounds Lookup.
  odestruct (apply_trees_access_lookup_outside_rev xH offi _ _ _ xH) as (it&H1&H2&H3&H4).
  2: by eapply wf_tree_wf_singleton.
  - rewrite /apply_within_trees lookup_singleton_eq /=. erewrite App. rewrite /= insert_singleton_eq. done.
  - intros (H1&H2). done.
  - exists tr'. split; first by eapply lookup_singleton_eq. done.
  - exists it. split_and; try done.
    destruct H1 as (tr''&H1&H1'). rewrite lookup_singleton_eq in H1. injection H1 as <-. done.
Qed.


(* Some more facts about trees. *)
(* TODO: These could be refactored, maybe? *)

Lemma apply_access_perm_access_remains_disabled b acc rel isprot itmo itmn :
  maybe_non_children_only b (apply_access_perm acc) rel isprot itmo = Some itmn →
  perm itmo = Disabled →
  perm itmn = Disabled.
Proof.
  edestruct maybe_non_children_only_effect_or_nop as [Heq|Heq]; erewrite Heq.
  - intros (pin&H1&(pp&H2&[= <-])%bind_Some)%bind_Some Hdis.
    simpl in Hdis,H1,H2|-*.
    rewrite /apply_access_perm_inner /= in H1.
    repeat (case_match; simplify_eq; try done).
  - congruence.
Qed.

Lemma apply_access_perm_read_frozen b rel isprot itmo itmn :
  maybe_non_children_only b (apply_access_perm AccessRead) rel isprot itmo = Some itmn →
  perm itmo = Frozen →
  perm itmn = Frozen.
Proof.
  edestruct maybe_non_children_only_effect_or_nop as [Heq|Heq]; erewrite Heq.
  - intros (pin&H1&(pp&H2&[= <-])%bind_Some)%bind_Some Hdis.
    simpl in Hdis,H1,H2|-*.
    repeat (case_match; simplify_eq; try done).
  - congruence.
Qed.

Lemma apply_access_perm_access_conflicted b kk rel isprot itmo itmn cc :
  maybe_non_children_only b (apply_access_perm kk) rel isprot itmo = Some itmn →
  perm itmo = Reserved ResConflicted →
  perm itmn = Reserved cc →
  cc = ResConflicted.
Proof.
  edestruct maybe_non_children_only_effect_or_nop as [Heq|Heq]; erewrite Heq.
  - intros (pin&H1&(pp&H2&[= <-])%bind_Some)%bind_Some Hdis.
    rewrite /apply_access_perm_inner in H1.
    simpl in Hdis,H1,H2|-*.
    repeat (case_match; simplify_eq; try done).
    all: intros [= <-]; done.
  - congruence.
Qed.

Lemma apply_access_perm_access_reserved_backwards b kk rel isprot itmo itmn acc :
  maybe_non_children_only b (apply_access_perm kk) rel isprot itmo = Some itmn →
  perm itmn = Reserved acc → ∃ acc,
  perm itmo = Reserved acc.
Proof.
  edestruct maybe_non_children_only_effect_or_nop as [Heq|Heq]; erewrite Heq.
  - intros (pin&H1&(pp&H2&[= <-])%bind_Some)%bind_Some Hdis.
    rewrite /apply_access_perm_inner in H1.
    simpl in Hdis,H1,H2|-*.
    repeat (case_match; simplify_eq; try done; try by eexists).
  - intros [= ->] ->. by eexists.
Qed.

Lemma apply_access_perm_access_reserved_im_backwards b kk rel isprot itmo itmn :
  maybe_non_children_only b (apply_access_perm kk) rel isprot itmo = Some itmn →
  perm itmn = ReservedIM →
  perm itmo = ReservedIM.
Proof.
  edestruct maybe_non_children_only_effect_or_nop as [Heq|Heq]; erewrite Heq.
  - intros (pin&H1&(pp&H2&[= <-])%bind_Some)%bind_Some Hdis.
    rewrite /apply_access_perm_inner in H1.
    simpl in Hdis,H1,H2|-*.
    repeat (case_match; simplify_eq; try done).
  - intros [= ->] ->. done.
Qed.

Lemma apply_access_perm_initialized b acc rel isprot itmo itmn :
  maybe_non_children_only b (apply_access_perm acc) rel isprot itmo = Some itmn →
  initialized itmo = PermInit →
  initialized itmn = PermInit.
Proof.
  edestruct maybe_non_children_only_effect_or_nop as [Heq|Heq]; erewrite Heq.
  - intros (pin&H1&(pp&H2&[= <-])%bind_Some)%bind_Some Hdis.
    simpl in Hdis,H1,H2|-*. rewrite Hdis in H2|-*.
    repeat (case_match; simpl in *; simplify_eq; try done).
  - congruence.
Qed.

Lemma rel_dec_concat_cousin tr t1 t2 t3 :
  wf_tree tr →
  tree_unique t1 tr →
  tree_unique t2 tr →
  tree_unique t3 tr →
  ∀ b,
  rel_dec tr t1 t2 = Foreign Cousin →
  rel_dec tr t2 t3 = Foreign (Parent b) → 
  rel_dec tr t1 t3 = Foreign Cousin.
Proof.
  intros Hwf Hu1 Hu2 Hu3 b.
  eapply unique_exists in Hu1 as Hc1.
  eapply unique_exists in Hu2 as Hc2.
  eapply unique_exists in Hu3 as Hc3.
  intros H1 H2.
  rewrite /rel_dec in H2|-*.
  rewrite !(decide_bool_decide (ImmediateParentChildIn _ _ _)) in H2|-*. repeat destruct decide; try done.
  1-2: rewrite /rel_dec in H1; repeat destruct decide; try done; exfalso; eauto using ParentChild_transitive.
  exfalso. eapply cousins_have_disjoint_children in H1; first done.
  1-3: eapply Hwf. 1: exact Hc3. 1-2: done. all: done.
Qed.

Lemma rel_dec_concat_parent tr t1 t2 t3 :
  wf_tree tr →
  tree_unique t1 tr →
  tree_unique t2 tr →
  tree_unique t3 tr →
  ∀ b1 b2,
  rel_dec tr t1 t2 = Foreign (Parent b1) →
  rel_dec tr t2 t3 = Foreign (Parent b2) → 
  ∃ b3,
  rel_dec tr t1 t3 = Foreign (Parent b3).
Proof.
  intros Hwf Hu1 Hu2 Hu3 b1 b2.
  eapply unique_exists in Hu1 as Hc1.
  eapply unique_exists in Hu2 as Hc2.
  eapply unique_exists in Hu3 as Hc3.
  rewrite /rel_dec.
  repeat destruct decide; try done.
  all: try by (exfalso; eauto using ParentChild_transitive).
  all: intros _ _; eexists; try done.
Qed.

Lemma rel_dec_concat_foreign tr t1 t2 t3 :
  wf_tree tr →
  tree_unique t1 tr →
  tree_unique t2 tr →
  tree_unique t3 tr →
  ∀ p1 b2,
  rel_dec tr t1 t2 = Foreign p1 →
  rel_dec tr t2 t3 = Foreign (Parent b2) → 
  ∃ p2,
  rel_dec tr t1 t3 = Foreign p2.
Proof.
  intros H0 H1 H2 H3 [p1|] b2 H4 H5.
  - edestruct (rel_dec_concat_parent tr t1 t2 t3) as (bb&Hbb); try done.
    by eexists.
  - exists Cousin. eapply rel_dec_concat_cousin; last done; done.
Qed.

Lemma rel_dec_parent_parent_is_parent tr ttop tmid tbot d1 d2 fp :
  wf_tree tr → tree_contains ttop tr → tree_contains tmid tr → tree_contains tbot tr →
  rel_dec tr ttop tbot = Foreign (Parent d1) →
  rel_dec tr tmid tbot = Foreign (Parent d2) →
  rel_dec tr ttop tmid = Foreign fp →
  ∃ d3, fp = Parent d3.
Proof.
  intros Hwf Hu1 Hu2 Hu3. unfold rel_dec at 1 2.
  destruct (decide (ParentChildIn tbot ttop tr)) as [HPC1|HPC1]; try done.
  destruct (decide (ParentChildIn ttop tbot tr)) as [HPC2|HPC2]; try done. intros _.
  destruct (decide (ParentChildIn tbot tmid tr)) as [HPC3|HPC3]; try done.
  destruct (decide (ParentChildIn tmid tbot tr)) as [HPC4|HPC4]; try done. intros _.
  intros Hfgn. destruct fp; first by eexists.
  eapply cousins_have_disjoint_children in Hfgn. 5-6: done. 1: done. all: by eapply Hwf.
Qed.

Lemma priv_loc_access_must_use_same_tag M_call M_t M_s M_tag σ_t σ_s l t_prv t_acc ak (off1 : Z) (sz : nat) :
  state_wf σ_s → state_wf σ_t →
  call_set_interp (tag_is_unq M_tag M_t) M_call σ_t →
  tag_interp M_tag M_t M_s σ_t σ_s →
  priv_loc M_tag M_t M_call t_prv l →
  trees_contain t_acc σ_t.(strs) l.1 →
  off1 ≤ l.2 < off1 + sz →
  is_Some (apply_within_trees (memory_access ak σ_t.(scs) t_acc (off1, sz)) l.1 σ_t.(strs)) →
  t_prv = t_acc.
Proof.
  intros Hwf_s Hwf_t Hcall Htag Hpriv Hcontain Hinside [trs' Happly].
  destruct Htag as (Htag&Htag_t & Htag_s &Htagdom_t & Htagdom_s).
  odestruct (trees_contain_trees_lookup_1 _ _ _ _ Hcontain) as (it_acc & Hitacc).
  1: eapply Hwf_t.
  destruct Hpriv as (tk&Htk&[vls Hhl]&[->|(cc&ae&->&Hcc)]).
  all: specialize (Htag _ _ Htk) as (Hv1&Hv2&Hlocal&Hcontrol_t&Hcontrol_s&Htagree).
  { odestruct (Hcontrol_t _ _ Hhl _) as ((it_prv&tr_prv&Htrprv&Hitprv&Hinit&Hactive&Hothers)&Hvls); first done.
    destruct Hitacc as (tr_acc&Htracc&Hitacc). assert (tr_prv = tr_acc) as -> by congruence.
    eapply Hothers. done. }
  destruct (call_set_interp_access _ _ _ _ _ _ _ Hcall Hcc) as (Hccv&Htv&it_prv&Hitprv&Hprotcc&_&Hae&Hprinit&Hnondis&Hcell).
  odestruct (Hcontrol_t _ _ Hhl _) as ((it_prv'&tr_prv&Htrprv'&Hitprv'&Hinit&Hactive&Hothers)&Hvls).
  { exists it_prv. split; first done. intros _. eapply Hnondis. }
  destruct Hitprv as (tr_prv'&Htrprv&Hitprv).
  assert (tr_prv = tr_prv') as <- by congruence.
  assert (it_prv = it_prv') as <- by by eapply tree_lookup_unique. clear Hitprv' Htrprv'.
  ospecialize (Hactive _).
  { intros _. exists cc. split; first done. apply Hccv. }
  assert (perm (item_lookup it_prv l.2) = Active) as Hactive2.
  { destruct (perm (item_lookup it_prv l.2)) as [|[]| | | |]; try done. }
  rewrite Hactive2 in Hactive. clear Hactive. rename Hactive2 into Hactive.
  edestruct (apply_trees_access_lookup_general false) as (it_prv' & Hitprv' & Hinitprv & Hpermprv & Haccprv).
  1: exact Happly. 1: apply Hwf_t. 1: apply Hinside. 1: exists tr_prv; split; first done; apply Hitprv.
  rewrite /maybe_non_children_only /= /trees_rel_dec Htrprv -Hpermprv bool_decide_true in Haccprv.
  2: { exists cc. split; first done. eapply Hccv. }
  assert (item_lookup it_prv l.2 = mkPerm PermInit Active) as Hinitactive.
  { destruct (item_lookup it_prv l.2) as [pp aa]. simpl in Hactive, Hinit. by rewrite Hactive Hinit. }
  rewrite Hinitactive in Haccprv.
  eapply bind_Some in Haccprv as (perm1prv&Hperm1prv&(perm2prv&Hperm2prv&[= Hresprv])%bind_Some). simpl in Hperm2prv, Hresprv.
  rewrite /apply_access_perm_inner /= in Hperm1prv.
  destruct (rel_dec tr_prv t_acc t_prv) as [ii|ii] eqn:Hreldec.
  { destruct ak; simpl in Hperm1prv; injection Hperm1prv as <-; done. }
  destruct Hitacc as (tr_acc&Htracc&Hitacc).
  assert (tr_acc = tr_prv) as -> by congruence.
  destruct ii as [ii|]; last first.
  { symmetry. eapply rel_this_antisym. 3: done.
    all: by eapply lookup_implies_contains. }
  rewrite /rel_dec in Hreldec.
  destruct (decide (ParentChildIn t_prv t_acc tr_prv)) as [HPC|HPC]; last done.
  destruct (decide (ParentChildIn t_acc t_prv tr_prv)) as [HPC2|HPC2]; first done.
  destruct HPC as [Heq|HPC]; first done.

  odestruct (immediate_sandwich _ _ _ _ _ HPC) as (t_sw&Hsw1&Hsw2).
  1: eapply Hwf_t; done. 1: eapply Hwf_t; first done; by eapply lookup_implies_contains.
  assert (tree_contains t_sw tr_prv) as Hswcont.
  { eapply contains_child. 1: right; by eapply Immediate_is_StrictParentChild. by eapply lookup_implies_contains. }
  odestruct (wf_tree_tree_item_determined _ _ _ Hswcont) as (it_sw&Hsw_det).
  1: by eapply Hwf_t.
  assert (tree_lookup tr_prv t_sw it_sw) as Hswlu by by split.
  edestruct (apply_trees_access_lookup_general false) as (it_sw' & Hitsw' & Hinitsw & Hpermsw & Haccsw).
  1: exact Happly. 1: apply Hwf_t. 1: apply Hinside. 1: eexists tr_prv; split; first done; apply Hswlu.
  rewrite /maybe_non_children_only /= /trees_rel_dec Htrprv in Haccsw.
  specialize (Hothers _ _ Hswlu) as Hothers_sw.
  rewrite /rel_dec decide_True // in Haccsw.
  rewrite /rel_dec decide_True in Hothers_sw.
  2: right; by eapply Immediate_is_StrictParentChild.
  rewrite decide_False in Hothers_sw.
  2: { intros H. eapply strict_parent_self_impossible. 1: exact Hswcont.
       eapply ParentChild_StrictParentChild. 1: exact H.
       by eapply Immediate_is_StrictParentChild. }
  rewrite decide_True // in Hothers_sw.
  eapply bind_Some in Haccsw as (perm1sw&Hperm1sw&(perm2sw&Hperm2sw&[= Hressw])%bind_Some).
  rewrite /apply_access_perm_inner Hothers_sw in Hperm1sw. by destruct ak.
Qed.

Definition rel_pos_shallow_eq rp1 rp2 := 
  match rp1, rp2 with
    Child _, Child _ => True
  | Foreign _, Foreign _ => True
  | _, _ => False end.

Lemma apply_access_perm_shallow ak rp1 rp2 b lp :
  rel_pos_shallow_eq rp1 rp2 →
  apply_access_perm ak rp1 b lp = apply_access_perm ak rp2 b lp.
Proof.
  intros H1.
  destruct rp1 as [i1|i1], rp2 as [i2|i2]; done.
Qed.

Lemma create_then_access_implies_earlier_access tr ak cc cids tg_par tg_cld pk im rk off sz tr' tr'' :
  wf_tree tr → tree_contains tg_par tr → ¬ tree_contains tg_cld tr →
  create_child cids tg_par tg_cld pk im rk cc tr = Some tr' →
  memory_access ak cids tg_cld (off, sz) tr' = Some tr'' →
  is_Some (memory_access ak cids tg_par (off, sz) tr).
Proof.
  intros Hwf Hcont Hncont Hchild Hread.
  eapply apply_access_success_condition.
  eapply every_node_eqv_universal. intros it Hit.
  pose it.(itag) as tg_it.
  assert (tree_contains tg_it tr) as Hcont_it.
  { eapply exists_node_eqv_existential. exists it; done. }
  opose proof (exists_node_to_tree_lookup _ _ _ _) as Hluit.
  1: apply Hwf. 1: apply Hit.
  eapply option_bind_always_some; last done.
  eapply mem_apply_range'_success_condition.
  intros offi Hoffi. rewrite /range'_contains /= in Hoffi.
  eapply bind_Some in Hchild as (itnew&Hitnew&[= <-]).
  eapply mk_is_Some in Hread.
  eapply apply_access_success_condition in Hread.
  eapply every_node_eqv_universal in Hread.
  2: eapply insert_preserves_exists, Hit.
  destruct Hread as [x (p&Hp&Hpp)%bind_Some]. clear x Hpp.
  eapply mk_is_Some, mem_apply_range'_success_condition in Hp.
  2: apply Hoffi.
  simpl in Hp|-*.
  erewrite apply_access_perm_shallow. 1: exact Hp.
  eapply new_item_has_tag in Hitnew as HH.
  rewrite /rel_dec. destruct (decide (ParentChildIn (itag it) tg_par tr)) as [HPC|HnPC].
  - simpl. rewrite decide_True //.
    eapply ParentChild_transitive; last first.
    { eapply insert_produces_ParentChild. 1: done. subst tg_cld. by intros <-. }
    setoid_rewrite <- insert_eqv_rel. 1: done. all: simpl; rewrite HH. 2: by intros <-.
    intros ->. eapply Hncont, exists_node_eqv_existential. by exists it.
  - simpl. rewrite decide_False //.
    intros [<-|HSPC].
    { eapply Hncont, exists_node_eqv_existential. by exists it. }
    eapply HnPC. destruct (decide (itag it = tg_par)) as [Heq|Hne]. 1: by left. subst tg_cld.
    right. eapply insert_produces_minimal_ParentChild. 5: exact HSPC.
    all: simpl. 4: done. 3: done. 2: by intros <-.
    intros Htg. eapply Hncont, exists_node_eqv_existential. by exists it.
Qed.

Lemma create_then_access_implies_earlier_access_trees trs blk ak cc cids tg_par tg_cld pk im rk off sz trs' trs'' :
  wf_trees trs → trees_contain tg_par trs blk → ¬ trees_contain tg_cld trs blk →
  apply_within_trees (create_child cids tg_par tg_cld pk im rk cc) blk trs = Some trs' →
  apply_within_trees (memory_access ak cids tg_cld (off, sz)) blk trs' = Some trs'' →
  is_Some (apply_within_trees (memory_access ak cids tg_par (off, sz)) blk trs).
Proof.
  intros Hwf Hcont Hncont Hchild Hread.
  eapply bind_Some in Hchild as (tr&Htr&(tr'&Hchild&[= <-])%bind_Some).
  rewrite /apply_within_trees lookup_insert_eq /= in Hread.
  eapply bind_Some in Hread as (tr''&Hread&Htr'').
  rewrite /apply_within_trees Htr /=. eapply option_bind_always_some; last done.
  rewrite /trees_contain /trees_at_block !Htr in Hcont, Hncont.
  eapply create_then_access_implies_earlier_access. 5: done. 4: done. 3: done. 2: done.
  eapply Hwf, Htr.
Qed.

Lemma local_access_preserves_unchanged_one_tree acc σ t blk off_hl off_rd sc (sz:nat) tr :
  state_wf σ → wf_tree tr →
  (sz = 0%nat ∨ (off_hl ≤ off_rd ∧ off_rd + sz ≤ off_hl + length sc)) →
  (∀ i : nat, (i < length sc)%nat → σ.(shp) !! ((blk, off_hl) +ₗ i) = sc !! i) →
  (∃ it, tr = branch it empty empty ∧ root_invariant blk it σ.(shp) ∧ t = it.(itag)) →
  memory_access acc σ.(scs) t (off_rd, sz) tr = Some tr.
Proof.
  rewrite /memory_access /= /memory_access_maybe_nonchildren_only /= /tree_apply_access /=.
  intros Hwf Hwftree Hlen Hhp (it&->&Hit&Htg).
  simpl. rewrite /item_apply_access /permissions_apply_range' /= /mem_apply_range' /=.
  rewrite mem_apply_locs_id. 1: by destruct it.
  intros offi Hoffi. assert (∃ (n:nat), offi = off_hl + n) as (n&->).
  { exists (Z.to_nat (offi - off_hl)). lia. }
  ospecialize (Hhp n _). 1: lia.
  destruct (lookup_lt_is_Some_2 sc n) as [scn Hscn]. 1: lia.
  rewrite Hscn /shift_loc /= in Hhp.
  destruct Hit as (Hr1&Hr2&Hr3).
  specialize (Hr3 (off_hl + n)). assert (iperm it !! (off_hl + n) = Some (mkPerm PermInit Active)) as Hoffn.
  { repeat (case_match; try done; try congruence). all: rewrite Hr3 // in Hhp. }
  eexists; split; first done.
  rewrite Hr1 /=. rewrite /rel_dec decide_True //.
  2: rewrite /ParentChildIn; by left.
  destruct acc; simpl; done.
Qed. 

Lemma local_access_preserves_unchanged acc σ t blk off_hl off_rd sc (sz : nat) :
  state_wf σ →
  (sz = 0%nat ∨ off_hl ≤ off_rd ∧ off_rd + sz ≤ off_hl + length sc) →
  (∀ i : nat, (i < length sc)%nat → σ.(shp) !! ((blk, off_hl) +ₗ i) = sc !! i) →
  (∃ it, σ.(strs) !! blk = Some (branch it empty empty) ∧ root_invariant blk it σ.(shp) ∧ t = it.(itag)) →
  apply_within_trees (memory_access acc σ.(scs) t (off_rd, sz)) blk σ.(strs) = Some σ.(strs).
Proof.
  intros Hwf Hlen H1 (it&Htr&Hit).
  rewrite /apply_within_trees /= Htr /=.
  rewrite (local_access_preserves_unchanged_one_tree _ _ _ blk off_hl _ sc).
  2: done. 2: by eapply Hwf. 2: done. 2: done.
  - rewrite /= insert_id //.
  - by exists it.
Qed.
