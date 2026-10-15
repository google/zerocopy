From iris.proofmode Require Export proofmode.
From iris.base_logic.lib Require Import ghost_map.
From simuliris.base_logic Require Export gen_sim_prog.
From simuliris.simulation Require Export slsls.
From simuliris.simulation Require Import lifting.
From simuliris.tree_borrows Require Import tkmap_view.
From simuliris.tree_borrows Require Export defs class_instances.
From simuliris.tree_borrows Require Import steps_progress steps_inv.
From simuliris.tree_borrows Require Import tree_access_laws logical_state inv_accessors.
From simuliris.tree_borrows.trees_equal Require Export trees_equal_base random_lemmas.


Definition item_protected_for_noinit (P : Prop) (no_children_pred_on : tag → loc → Prop) c it blk off (ps:logical_protector) :=
      protector_is_for_call c it.(iprot)
    ∧ protector_matches_strength ps it.(iprot)
    ∧ (ps = EnsuringAccess WeaklyNoChildren → no_children_pred_on it.(itag) (blk, off))
      (* we must be initialized, otherwise deallocation could continue *)
    ∧ (P → (item_lookup it off).(initialized) = PermInit)
      (* we can never be disabled, as we are protected *)
    ∧ (item_lookup it off).(perm) ≠ Disabled
      (* we must not be cell, because protected Cell makes no sense and provides no guarantees *)
    ∧ (item_lookup it off).(perm) ≠ Cell.

Definition tag_protected_for_noinit (P : Prop) (Q : tag → loc → Prop) c trs l t ps := match ps with
  EnsuringAccess ae => ∃ it, trees_lookup trs l.1 t it ∧ item_protected_for_noinit P Q c it l.1 l.2 ps
| Deallocable   => ∀ it, trees_lookup trs l.1 t it → item_protected_for_noinit P Q c it l.1 l.2 ps end.

Lemma into_tag_protected_for_noinit P Q c trs l t ps : 
  tag_protected_for Q c trs l t ps → tag_protected_for_noinit P Q c trs l t ps.
Proof.
  destruct ps.
  - intros H it Hit. destruct (H it Hit) as (H2&H3&H4&H5&H6&H7). split_and!; done.
  - intros (it&H1&H2&H3&H4&H5&H6&H7). exists it; split; last split_and!. all: done.
Qed.

(* TODO move somewhere else *)
Lemma tag_protected_preserved_by_access_strong tg_acc tg_prs l C c trs trs' acc blk off sz b P ae:
  wf_trees trs →
  apply_within_trees (memory_access_maybe_nonchildren_only b acc C tg_acc (off, sz)) blk trs = Some trs' →
  call_is_active c C →
  tag_protected_for_noinit (¬ (blk = l.1 ∧ tg_prs = tg_acc ∧ off ≤ l.2 < off + sz)) P c trs  l tg_prs (EnsuringAccess ae) →
  tag_protected_for P c trs' l tg_prs (EnsuringAccess ae).
Proof.
  intros Hwf Hwithin Hcall (it & Hlu & Hprot & Hstrong & Hweak & Hinit & Hndis & Hcell).
  destruct (decide (l.1 = blk ∧ (off ≤ l.2 < off + sz))%Z) as [(<- & Hin)|Hout].
  - pose proof Hlu as Hlu2. eapply apply_trees_access_lookup_general in Hlu2 as (itnew & Hlunew & Heqinit & Heqprot & Hacc); [|done..].
    exists itnew. split; first done. rewrite /item_protected_for -Heqprot.
    assert (itag it = itag itnew) as Heqitag by by repeat erewrite trees_lookup_correct_tag.
    rewrite -Heqitag. 
    do 3 (split; first done).
    assert (protector_is_active (iprot itnew) C) as Hactive.
    { exists c. rewrite -Heqprot. done. }
    edestruct maybe_non_children_only_effect_or_nop_strong as [(Heq&_)|(Heq&Hwhy)].
    2: { erewrite Heq in Hacc. injection Hacc as Hacc. rewrite -Hacc. split; last done.
         eapply Hinit. intros (_&->&_). rewrite trees_rel_dec_refl in Hwhy. by destruct Hwhy as (?&?&?). }
    erewrite Heq in Hacc.
    apply bind_Some in Hacc as (perm1 & Hacc & (perm2 & Htrigger & [= Heqperm])%bind_Some).
    rewrite (bool_decide_eq_true_2 _ Hactive) /= in Hacc, Htrigger.
    rewrite /apply_access_perm_inner in Hacc.
    assert (initialized (item_lookup itnew l.2) = PermInit) as Hinitnew.
    { rewrite -Heqperm. destruct (decide (tg_acc = tg_prs)) as [->|Hne].
      * rewrite trees_rel_dec_refl most_init_comm //.
      * rewrite Hinit //. intros (_&->&_). done. }
    split_and!.
    + done.
    + rewrite -Heqperm /= in Hinitnew|-*. rewrite Hinitnew /= in Htrigger.
      intros ->. clear -Htrigger. by case_match.
    + intros Hcello. rewrite -Heqperm /= in Hcello. subst perm2.
      assert (perm1 = Cell) as ->.
      { clear -Htrigger. repeat (case_match; simplify_eq; try done). }
      enough (perm (item_lookup it l.2) = Cell) as HH by done.
      clear -Hacc. repeat (case_match; simplify_eq; try done).
  - eapply apply_trees_access_lookup_outside in Hlu as Hlu2; [|done..].
    destruct Hlu2 as (itnew & Hlunew & Heqinit & Heqprot & Hacc).
    exists itnew. split; first done. rewrite /item_protected_for -Heqprot.
    assert (itag it = itag itnew) as Heqitag by by repeat erewrite trees_lookup_correct_tag.
    rewrite -Heqitag. 
    do 2 (split; first done).
    rewrite -Hacc. split_and!. 1,3,4: done.
    eapply Hinit. intros (?&?&?). eapply Hout. done.
Qed.

Lemma tag_protected_preserved_by_access_weak tg_acc tg_prs l C c trs trs' acc blk off sz b P :
  wf_trees trs →
  apply_within_trees (memory_access_maybe_nonchildren_only b acc C tg_acc (off, sz)) blk trs = Some trs' →
  call_is_active c C →
  tag_protected_for_noinit (¬ (blk = l.1 ∧ tg_prs = tg_acc ∧ off ≤ l.2 < off + sz)) P c trs  l tg_prs Deallocable →
  tag_protected_for P c trs' l tg_prs Deallocable.
Proof.
  intros Hwf Hwithin Hcall Hold.
  destruct (decide (l.1 = blk ∧ (off ≤ l.2 < off + sz))%Z) as [(<- & Hin)|Hout].
  - intros it Hlu.
    eapply apply_trees_access_lookup_general_rev in Hlu as (itold & Hluold & Heqinit & Heqprot & Hacc); [|done..].
    specialize (Hold itold Hluold) as (Hprot & Hstrong & HP & Hinit & Hndis & Hcell).
    rewrite /item_protected_for -Heqprot.
    do 3 (split; first done).
    assert (protector_is_active (iprot it) C) as Hactive.
    { exists c. rewrite -Heqprot. done. }
    edestruct maybe_non_children_only_effect_or_nop_strong as [(Heq&_)|(Heq&Hwhy)].
    2: { erewrite Heq in Hacc. injection Hacc as Hacc. rewrite -Hacc. split; last done.
         eapply Hinit. intros (_&->&_). rewrite trees_rel_dec_refl in Hwhy. by destruct Hwhy as (?&?&?). }
    erewrite Heq in Hacc.
    apply bind_Some in Hacc as (perm1 & Hacc & (perm2 & Htrigger & [= Heqperm])%bind_Some).
    rewrite (bool_decide_eq_true_2 _ Hactive) /= in Hacc, Htrigger.
    rewrite /apply_access_perm_inner in Hacc.
    assert (initialized (item_lookup it l.2) = PermInit) as Hinitnew.
    { rewrite -Heqperm. destruct (decide (tg_acc = tg_prs)) as [->|Hne].
      * rewrite trees_rel_dec_refl most_init_comm //.
      * rewrite Hinit //. intros (_&->&_). done. } split_and!.
    + done.
    + rewrite -Heqperm /= in Hinitnew|-*. rewrite Hinitnew /= in Htrigger.
      intros ->. clear -Htrigger. by case_match.
    + intros Hcello. rewrite -Heqperm /= in Hcello. subst perm2.
      assert (perm1 = Cell) as ->.
      { clear -Htrigger. repeat (case_match; simplify_eq; try done). }
      enough (perm (item_lookup itold l.2) = Cell) as HH by done.
      clear -Hacc. repeat (case_match; simplify_eq; try done).
  - intros it Hlu.
    eapply apply_trees_access_lookup_outside_rev in Hlu as (itold & Hluold & Heqinit & Heqprot & Hacc); [|done..].
    specialize (Hold itold Hluold) as (Hprot & Hstrong & Hweak & Hinit&?&?).
    rewrite /item_protected_for -Heqprot.
    do 2 (split; first done).
    rewrite -Hacc. split_and!. 1,3,4: done.
    eapply Hinit. intros (?&?&?). eapply Hout. done.
Qed.
Lemma tag_protected_preserved_by_access_init tg_acc tg_prs l C c trs trs' acc blk off sz b ps P:
  wf_trees trs →
  apply_within_trees (memory_access_maybe_nonchildren_only b acc C tg_acc (off, sz)) blk trs = Some trs' →
  call_is_active c C →
  tag_protected_for_noinit (¬ (blk = l.1 ∧ tg_prs = tg_acc ∧ off ≤ l.2 < off + sz)) P c trs  l tg_prs ps →
  tag_protected_for P c trs' l tg_prs ps.
Proof.
  destruct ps.
  - eapply tag_protected_preserved_by_access_weak.
  - eapply tag_protected_preserved_by_access_strong.
Qed.
Lemma tag_protected_preserved_by_access tg_acc tg_prs l C c trs trs' acc blk off sz b ps P:
  wf_trees trs →
  apply_within_trees (memory_access_maybe_nonchildren_only b acc C tg_acc (off, sz)) blk trs = Some trs' →
  call_is_active c C →
  tag_protected_for P c trs  l tg_prs ps →
  tag_protected_for P c trs' l tg_prs ps.
Proof.
  intros ????. eapply tag_protected_preserved_by_access_init. 1-3: done.
  eapply into_tag_protected_for_noinit. done.
Qed.

(* TODO move somewhere else *)
Lemma tag_protected_preserved_by_delete tg_acc tg_prs l C c trs trs' blk off sz ps P :
  wf_trees trs →
  apply_within_trees (memory_deallocate C tg_acc (off, sz)) blk trs = Some trs' →
  call_is_active c C →
  (∀ it, ps = EnsuringAccess WeaklyNoChildren → l.1 = blk → trees_lookup trs blk tg_prs it → P tg_prs l → protector_is_for_call c (iprot it) → (initialized (item_lookup it l.2) = PermInit → perm (item_lookup it l.2) ≠ Disabled) → False) →
  tag_protected_for P c trs l tg_prs ps →
  tag_protected_for P c (delete blk trs') l tg_prs ps.
Proof.
  intros Hwf Hwithin Hcall HPprotect Hpreprot.
  rewrite apply_within_trees_bind in Hwithin.
  pose proof Hwithin as (postread&Hread&Hdealloc)%bind_Some.
  eapply tag_protected_preserved_by_access in Hread as HH. 2-4: done.
  destruct (decide (l.1 = blk)) as [<-|Hout], ps as [|ae].
  - clear HH. intros it (tr&Htr&Hit). by rewrite lookup_delete_eq in Htr.
  - exfalso. destruct HH as (it & (tr & Htr & Hlu) & Hprot & Hstrong & Hweak & Hinit).
    destruct ae; last first.
    { destruct Hpreprot as (it' & (tr' & Htr' & Hlu') & Hprot' & Hstrong' & Hweak' & Hinit' & Hndis' & Hcell'). destruct l.
      erewrite tree_lookup_correct_tag in Hweak'; last done. 
      eapply HPprotect. 1: done. 3: by eapply Hweak'. 1: done. 1: eexists; split; first done. 2: eapply Hprot'. 1: eapply Hlu'. done.
    }
    rewrite /apply_within_trees Htr /= in Hdealloc.
    pose proof Hdealloc as (okcheck&Hcheck%mk_is_Some&[= <-])%bind_Some. clear Hdealloc.
    rewrite join_success_condition every_node_map every_node_eqv_universal /= in Hcheck.
    pose proof (tree_lookup_correct_tag Hlu) as <-.
    ospecialize (Hcheck it _); first by eapply tree_lookup_to_exists_node.
    eapply is_Some_if_neg in Hcheck.
    rewrite (bool_decide_eq_true_2) /= in Hcheck.
    2: by destruct (iprot it) as [[]|].
    rewrite (bool_decide_eq_true_2) /= in Hcheck.
    2: by exists c.
    rewrite /=bool_decide_eq_false in Hcheck.
    eapply Hcheck.
    rewrite /item_lookup in Hinit. exists l.2.
    destruct (iperm it !! l.2) as [lp|] eqn:Heq.
    2: by destruct Hinit.
    eexists; split; first done. simpl in Hinit.
    destruct Hinit as (Hi1&Hi2&Hi3).
    rewrite /protector_end_action Hi1. destruct (perm lp); done.
  - intros it (tr&(Hne&Hin)%lookup_delete_Some&Hit).
    eapply HH. exists tr. split; last done.
    eapply bind_Some in Hdealloc as (tr1&Htr1&(tr2&Htr2&[= Heq])%bind_Some).
    rewrite -Heq lookup_insert_ne // in Hin.
  - destruct HH as (it & (tr & Htr & Hlu) & Hprot & Hstrong & Hinit).
    exists it. split; last done. exists tr. split; last done.
    rewrite lookup_delete_ne //.
    pose proof Hdealloc as (?&_&(?&_&[= <-])%bind_Some)%bind_Some.
    by rewrite lookup_insert_ne.
Qed.

Lemma tag_protected_preserved_by_create_strong tg_par tg_cld pk im rk C cc c trs trs' blk l tg_prs P ae:
  wf_trees trs → tg_cld ≠ tg_prs →
  apply_within_trees (create_child C tg_par tg_cld pk im rk cc) blk trs = Some trs' →
  tag_protected_for P c trs  l tg_prs (EnsuringAccess ae) →
  tag_protected_for P c trs' l tg_prs (EnsuringAccess ae).
Proof.
  intros Hwf Hncontain (tr&Htr&(tr'&Hcreate&[= <-])%bind_Some)%bind_Some (it & Hlu & Hprot & Hstrong & Hinit).
  exists it. split; last done. destruct Hlu as (tt&Htt&Hit).
  destruct (decide (l.1 = blk)%Z) as [<-|Hdiffblk]; last first.
  { exists tt. split; last done. by rewrite lookup_insert_ne. }
  assert (tt = tr) as <- by congruence.
  exists tr'. split; first by rewrite lookup_insert_eq.
  destruct Hit as (Hin&Hlu). split.
  - eapply insertion_preserves_tags. 2: done. done.
  - eapply create_child_preserves_determined. 2: apply Hlu. 2: eapply Hcreate.
    by intros ->.
Qed.
Lemma tag_protected_preserved_by_create_weak tg_par tg_cld pk im rk C cc c trs trs' blk l tg_prs P:
  wf_trees trs → tg_cld ≠ tg_prs →
  apply_within_trees (create_child C tg_par tg_cld pk im rk cc) blk trs = Some trs' →
  tag_protected_for P c trs  l tg_prs Deallocable →
  tag_protected_for P c trs' l tg_prs Deallocable.
Proof.
  intros Hwf Hncontain (tr&Htr&(tr'&Hcreate&[= <-])%bind_Some)%bind_Some Hprot it Hlu.
  eapply Hprot. destruct Hlu as (tt&Htt&Hit).
  destruct (decide (l.1 = blk)%Z) as [<-|Hdiffblk]; last first.
  { exists tt. split; last done. by rewrite lookup_insert_ne in Htt. }
  rewrite lookup_insert_eq in Htt.
  assert (tt = tr') as -> by congruence.
  exists tr. split; first done.
  destruct Hit as (Hin&Hlu). split.
  - eapply insertion_minimal_tags. 3: done. 2: done. by intros ->.
  - eapply bind_Some in Hcreate as (ii&Hii&[= <-]).
    eapply insert_true_preserves_every. 2: apply Hlu.
    simpl. intros <-. eapply new_item_has_tag in Hii. congruence.
Qed.
Lemma tag_protected_preserved_by_create ps tg_par tg_cld pk im rk C cc c trs trs' blk l tg_prs P:
  wf_trees trs → tg_cld ≠ tg_prs →
  apply_within_trees (create_child C tg_par tg_cld pk im rk cc) blk trs = Some trs' →
  tag_protected_for P c trs  l tg_prs ps →
  tag_protected_for P c trs' l tg_prs ps.
Proof.
  destruct ps.
  - eapply tag_protected_preserved_by_create_weak.
  - eapply tag_protected_preserved_by_create_strong.
Qed.


Definition tag_protected_for_tree P c tr l t ps := match ps with
  | Deallocable   => ∀ it, tree_lookup tr t it → item_protected_for P c it l.1 l.2 ps
  | EnsuringAccess _ => ∃ it, tree_lookup tr t it ∧ item_protected_for P c it l.1 l.2 ps end.

Lemma tag_protected_for_tree_spec trs tr c l t ps P :
  trs !! l.1 = Some tr →
  tag_protected_for_tree P c tr l t ps ↔ tag_protected_for P c trs l t ps.
Proof.
  intros H.
  destruct ps; split.
  - intros HH it (tr'&Htr&Hit). eapply HH. rewrite /= H in Htr. congruence.
  - intros HH it Hit. eapply HH. exists tr. simpl. done.
  - intros (it&H1&HH). exists it. split; last done. eexists. simpl. done.
  - intros (it&(tr'&H1&H2)&HH). exists it; split; last done. rewrite /= H in H1. by injection H1 as ->.
Qed.

Lemma tag_protected_preserved_by_access_tree tg_acc tg_prs loff C c tr tr' acc off sz b ps P :
  wf_tree tr →
  memory_access_maybe_nonchildren_only b acc C tg_acc (off, sz) tr = Some tr' →
  call_is_active c C →
  tag_protected_for_tree P c tr loff tg_prs ps →
  tag_protected_for_tree P c tr' loff tg_prs ps.
Proof.
  intros H1 H2 H3 H4.
  eapply wf_tree_wf_singleton_any in H1.
  eassert ({[loff.1 := tr]} !! _ = Some tr) as Hlu by eapply lookup_singleton_eq.
  eassert ({[loff.1 := tr']} !! _ = Some tr') as Hlu' by eapply lookup_singleton_eq.
  setoid_rewrite tag_protected_for_tree_spec; last done.
  eapply tag_protected_preserved_by_access. 1: done. 2: done.
  - rewrite /apply_within_trees /=. setoid_rewrite Hlu. rewrite /=. erewrite H2.
    rewrite /= insert_singleton_eq //.
  - eapply tag_protected_for_tree_spec; done.
Qed.

Lemma tree_access_many_preserve_tag_protected_for_2 C tg_acc (L : gmap Z _) tr1 trL c offp tg_prs ps P
  (Hwf1 : wf_tree tr1) :
  call_is_active c C →
  let fn := (λ L tr, map_fold (λ l v tr2, tr2 ≫= memory_access_nonchildren_only v C tg_acc (l, 1%nat)) (Some tr) L) in
  fn L tr1 = Some trL →
  tag_protected_for_tree P c tr1 offp tg_prs ps →
  tag_protected_for_tree P c trL offp tg_prs ps.
Proof.
  intros Hact fn. subst fn. simpl.
  map_fold_weak_ind L as off v L _ _ IH in trL.
  { intros [= ->]. done. }
  intros (tr2&Hoff&HL)%bind_Some.
  specialize (IH _ Hoff).
  assert (wf_tree tr2) as Hwf2.
  { eapply preserve_tag_count_wf. 1: eapply tree_access_many_helper_2. 1: exact Hwf1. 1: apply Hoff. }
  intros Hprot. eapply tag_protected_preserved_by_access_tree.
  3: exact Hact. 2: exact HL. 1: done.
  by eapply IH.
Qed.

Lemma tree_access_many_preserve_tag_protected_for_1 C (L : list (tag * gmap Z _)) tr1 trL c offp tg_prs ps P
  (Hwf1 : wf_tree tr1) :
  call_is_active c C →
  let fn := (λ E tr, foldr (λ '(tg, L) tr, tr ≫= λ tr1, map_fold (λ l v tr2, tr2 ≫= memory_access_nonchildren_only v C tg (l, 1%nat)) (Some tr1) (L)) (Some tr) E) in
  fn L tr1 = Some trL →
  tag_protected_for_tree P c tr1 offp tg_prs ps →
  tag_protected_for_tree P c trL offp tg_prs ps.
Proof.
  intros Hact fn.
  induction L as [|(tg_acc&S) L IH] in trL|-*; simpl.
  { intros [= ->]. done. }
  intros (tr2&Hoff&HL)%bind_Some.
  specialize (IH _ Hoff).
  assert (wf_tree tr2) as Hwf2.
  { eapply preserve_tag_count_wf. 1: eapply tree_access_many_helper_1. 1: exact Hwf1. 1: apply Hoff. }
  intros Hprot. eapply tree_access_many_preserve_tag_protected_for_2.
  2: exact Hact. 2: exact HL. 1: done.
  by eapply IH.
Qed.

Lemma tree_access_many_preserve_tag_protected_for C cid tr1 trL c offp tg_prs ps P
  (Hwf1 : wf_tree tr1) :
  call_is_active c C →
  tree_access_all_protected_initialized C cid tr1 = Some trL →
  tag_protected_for_tree P c tr1 offp tg_prs ps →
  tag_protected_for_tree P c trL offp tg_prs ps.
Proof.
  rewrite /tree_access_all_protected_initialized.
  rewrite /set_fold /=. eapply tree_access_many_preserve_tag_protected_for_1. done.
Qed.

Lemma trees_access_many_preserve_tag_protected_for C cid trs1 trsL c l tg_prs ps P
  (Hwf1 : wf_trees trs1) :
  call_is_active c C →
  trees_access_all_protected_initialized C cid trs1 = Some trsL →
  tag_protected_for P c trs1 l tg_prs ps →
  tag_protected_for P c trsL l tg_prs ps.
Proof.
  intros H1 H2 H3. destruct l as [blk offl], ps.
  - intros itL (trL&HtrL&HitL). simpl in HtrL.
    assert (∃ tr, trs1 !! blk = Some tr) as (tr&Htr).
    { eapply trees_access_all_protected_initialized_pointwise_1 in H2 as (_&H2B).
      destruct (trs1 !! blk) eqn:Heq; first by eexists.
      specialize (H2B Heq). congruence. }
    eapply trees_access_all_protected_initialized_pointwise_1 in H2 as (H2&_).
    specialize (H2 _ Htr) as (tr'&Htr'&Hread). assert (trL = tr') as -> by congruence. simpl.
    eapply tree_access_many_preserve_tag_protected_for in Hread; first last. 3: by eapply Hwf1. 2: done.
    1: eapply tag_protected_for_tree_spec; last exact H3. 1: by rewrite /=.
    eapply Hread. done.
  - assert (∃ tr, trs1 !! blk = Some tr) as (tr&Htr).
    { destruct H3 as (x&(tr&Htr&_)&_). by eexists. }
    eapply trees_access_all_protected_initialized_pointwise_1 in H2 as (H2&_).
    specialize (H2 _ Htr) as (tr'&Htr'&Hread).
    eapply tag_protected_for_tree_spec. 1: done.
    eapply tree_access_many_preserve_tag_protected_for. 1: by eapply Hwf1. 1: done. 1: done.
    eapply tag_protected_for_tree_spec. all: done.
Qed.

Lemma call_set_interp_remove c M σ σ' P :
  snc σ = snc σ' →
  snp σ = snp σ' →
  scs σ ∖ {[c]} = scs σ' →
  shp σ = shp σ' →
  state_wf σ →
  trees_access_all_protected_initialized (scs σ) c (strs σ) = Some (strs σ') →
  call_set_interp P M σ →
  call_set_interp P (delete c M) σ'.
Proof.
  intros Heq1 Heq2 Heq3 Heq4 Heq5 Hwf (Hinterp&Hinj).
  split; last first.
  { intros c1 M1 c2 M2 t (?&?)%lookup_delete_Some (?&?)%lookup_delete_Some. by eapply Hinj. }
  intros c' M' Hsome. destruct (decide (c' = c)) as [-> | Hneq].
  { rewrite lookup_delete_eq in Hsome. done. }
  rewrite lookup_delete_ne in Hsome; last done.
  apply Hinterp in Hsome as (Hin & Hpid).
  split.
  { rewrite -Heq3. set_solver. }
  intros t S HS.
  apply Hpid in HS as (Ht & Hlookup). split; first by rewrite -Heq2.
  intros l b Hl.
  eapply trees_access_many_preserve_tag_protected_for.
  3: done. 3: by eapply Hlookup. 1: by eapply state_wf_tree_unq.
  by eapply Hin.
Qed.

Lemma tag_protected_for_mono P1 P2 c trs l tg ps :
  (∀ l it, trees_lookup trs l.1 tg it → protector_is_for_call c (iprot it) → (initialized (item_lookup it l.2) = PermInit → perm (item_lookup it l.2) ≠ Disabled) → P1 (itag it) l → P2 (itag it) l) →
  tag_protected_for P1 c trs l tg ps →
  tag_protected_for P2 c trs l tg ps.
Proof.
  intros Hweak H. destruct ps as [|[]].
  - intros ??. split_and!; try by eapply H. done.
  - destruct H as (?&?&H). eexists; split; first done.
    split_and!; try eapply H. done. 
  - destruct H as (it&Hit&Hprot&Hstrong&HP1&Hrst1&Hrst2&Hrst3).
    exists it. split; first done. split_and!; try done.
    intros ?; eapply Hweak; try done. by eapply HP1.
  
Qed.

Lemma call_set_interp_mono M σ P1 P2 :
  (∀ tg c l it, call_is_active c σ.(scs) → trees_lookup σ.(strs) l.1 tg it → protector_is_for_call c (iprot it) → (initialized (item_lookup it l.2) = PermInit → perm (item_lookup it l.2) ≠ Disabled) → P1 (itag it) l → P2 (itag it) l) →
  call_set_interp P1 M σ →
  call_set_interp P2 M σ.
Proof.
  intros Hweak (H1&Hinj). split; last done. intros c S HS.
  specialize (H1 c S HS) as (Hc&H1). split; first done.
  intros t L HL. specialize (H1 t L HL) as (Ht&H2). split; first done.
  intros l ps Hl. eapply tag_protected_for_mono; last by eapply H2.
  intros l' it ???. by eapply Hweak.
Qed.

