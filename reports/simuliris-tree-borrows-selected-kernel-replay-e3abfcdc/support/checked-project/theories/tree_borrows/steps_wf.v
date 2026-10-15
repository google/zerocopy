(** The core idea of this file is to prove that all borrow steps preserve
    well-formedness of trees. *)

From simuliris.tree_borrows Require Export defs tree_lemmas steps_foreach steps_preserve bor_lemmas.

(* weird GMAP stuff *)


Lemma map_fold_ind_strong {K V B} `{Countable K} (P : B → gmap K V → Prop) (f : K → V → B → B) (b:B) (M : gmap K V) :
  P b ∅ →
  (∀ k v M, M !! k = None → (∀ B' f' (b':B'), map_fold f' b' (<[k:=v]> M) = f' k v (map_fold f' b' M)) → P (map_fold f b M) M → P (f k v (map_fold f b M)) (<[k:=v]> M)) →
  P (map_fold f b M) M.
Proof.
  intros Hbase Hstep. eapply (map_first_key_ind (fun mm => P (map_fold f b mm) mm)).
  - rewrite map_fold_empty. apply Hbase.
  - intros k v m Hnone Hfirstkey HIH.
    rewrite map_fold_insert_first_key //. eapply Hstep; [done| |done].
    intros B' f' b'. rewrite map_fold_insert_first_key //.
Qed.


Tactic Notation "map_fold_weak_ind" constr(M) "as" simple_intropattern(k) simple_intropattern(v) simple_intropattern(LL) simple_intropattern(Hnone) simple_intropattern(Hothers) simple_intropattern(IH) "in" hyp_list(hyps)  := 
  match goal with |- context C [map_fold ?f ?b M] => revert hyps; pattern (map_fold f b M); pattern M; 
    (match goal with |- (λ m', (λ b', ?Q) ?B) M => change ((λ b' m', Q) (map_fold f b M) M);
      refine ((map_fold_ind_strong (λ b' m', Q) f b M _ _)) end) end; clear M; [| intros k v LL Hnone Hothers IH]; intros hyps.

Lemma item_wf_lookup it l ev1 ev2 :
  item_wf it ev1 ev2 →
  lazy_perm_wf (item_lookup it l).
Proof.
  intros [H1 H2 H3 _ H4].
  rewrite /item_lookup. edestruct (iperm it !! l) as [pp|] eqn:H5.
  - simpl. eapply map_Forall_lookup_1 in H4; done.
  - simpl. intros Hne. exfalso. apply H3, Hne.
Qed.

Definition preserves_lazy_perm_wf fn := ∀ perm1 perm2, fn perm1 = Some perm2 → lazy_perm_wf perm1 → lazy_perm_wf perm2.

Lemma apply_access_perm_wf kind pos isprot :
  preserves_lazy_perm_wf (apply_access_perm kind pos isprot).
Proof.
  rewrite /apply_access_perm /apply_access_perm_inner /lazy_perm_wf /most_init /=.
  intros perm1 perm2 (p1&H1&(p2&H2&[= <-])%bind_Some)%bind_Some Hwf. simpl.
  repeat (case_match; simpl in *; simplify_eq; try done). 
Qed.

Lemma apply_access_perm_maybe_wf b kind pos isprot :
  preserves_lazy_perm_wf (maybe_non_children_only b (apply_access_perm kind) pos isprot).
Proof.
  intros perm1 perm2.
  edestruct maybe_non_children_only_effect_or_nop as [Heq|Heq]; erewrite Heq.
  2: by intros [= <-].
  apply apply_access_perm_wf.
Qed.

Definition preserves_reach fn := ∀ perm1 perm2, fn perm1 = Some perm2 → reach perm1.(perm) perm2.(perm).

Lemma apply_access_perm_reach kind pos isprot :
  preserves_reach (apply_access_perm kind pos isprot).
Proof.
  rewrite /apply_access_perm /apply_access_perm_inner /preserves_reach /=.
  intros perm1 perm2 (p1&H1&(p2&H2&[= <-])%bind_Some)%bind_Some. simpl.
  repeat (case_match; simpl in *; simplify_eq; try done).
Qed.

Lemma apply_access_perm_maybe_reach b kind pos isprot :
  preserves_reach (maybe_non_children_only b (apply_access_perm kind) pos isprot).
Proof.
  intros perm1 perm2.
  edestruct maybe_non_children_only_effect_or_nop as [Heq|Heq]; erewrite Heq.
  2: intros [= <-]; by eapply reach_reflexive.
  apply apply_access_perm_reach.
Qed.


Lemma wf_tree_tree_unique tr :
  wf_tree tr →
  ∀ tg,
  tree_contains tg tr →
  tree_unique tg tr.
Proof.
  intros Hwf tg Hcont.
  by apply (Hwf tg Hcont).
Qed.

Lemma wf_tree_tree_item_determined tr :
  wf_tree tr →
  ∀ tg,
  tree_contains tg tr →
  ∃ it, tree_item_determined tg it tr.
Proof.
  intros Hwf tg Hcont.
  eapply unique_lookup, wf_tree_tree_unique.
  all: done.
Qed.


Lemma wf_init_state : state_wf init_state.
Proof.
  constructor; simpl; try split; try intros ?; try set_solver.
Qed.

(** Steps preserve wellformedness *)

Lemma wf_item_mono it :
  Proper ((≤)%nat==> (≤)%nat ==> impl) (item_wf it).
Proof.
  move=> ?? Le1 ?? Le2 [WFle WFprot WFdef WFprotIM WFperms WFreach].
  split.
  - intros tg tgit. specialize (WFle tg tgit). lia.
  - intros cid protit. specialize (WFprot cid protit). lia.
  - apply WFdef.
  - apply WFprotIM.
  - apply WFperms.
  - apply WFreach.
Qed.

Lemma tree_items_compat_nexts_mono tr :
  Proper ((≤)%nat==> (≤)%nat ==> impl) (tree_items_compat_nexts tr).
Proof.
  intros ?? Le1 ? ? Le2 WF.
  eapply every_node_eqv_universal.
  intros it Ex.
  eapply every_node_eqv_universal in WF; last done.
  eapply wf_item_mono; eauto.
Qed.

Lemma trees_compat_nexts_mono trs :
  Proper ((≤)%nat==> (≤)%nat ==> impl) (trees_compat_nexts trs).
Proof.
  move=> ?? Le1 ? ? Le2 WF ?? /WF Hf.
  eapply tree_items_compat_nexts_mono; eassumption.
Qed.

Lemma wf_mem_tag_mono h :
  Proper ((≤)%nat ==> impl) (wf_mem_tag h).
Proof.
  move => ??? WF ?? tg Access.
  specialize (WF _ _ tg Access); simpl in WF.
  lia.
Qed.

Definition preserve_tree_compat_nexts (fn:tree item -> option (tree item)) nxtp nxtp' nxtc nxtc' :=
  forall tr tr', tree_items_compat_nexts tr nxtp nxtc -> fn tr = Some tr' -> tree_items_compat_nexts tr' nxtp' nxtc'.

Definition preserve_tree_tag_count (fn:tree item -> option (tree item)) :=
  forall tr tr' tg, fn tr = Some tr' -> tree_count_tg tg tr = tree_count_tg tg tr'.

Lemma preserve_tag_count_wf fn tr tr' :
  preserve_tree_tag_count fn →
  wf_tree tr →
  fn tr = Some tr' →
  wf_tree tr'.
Proof.
  intros Hf H1 Heq tg Htg%count_gt0_exists.
  erewrite <- Hf in Htg; last done.
  eapply count_gt0_exists in Htg.
  specialize (H1 _ Htg) as Hunq.
  rewrite /tree_unique in Hunq.
  by erewrite Hf in Hunq.
Qed.

Lemma preserve_tag_count_contains fn tr tr' tg :
  preserve_tree_tag_count fn →
  tree_contains tg tr →
  fn tr = Some tr' →
  tree_contains tg tr'.
Proof.
  intros Hf H1%count_gt0_exists Heq.
  eapply count_gt0_exists.
  by erewrite <- Hf.
Qed.

Lemma preserve_tag_count_contains_2 fn tr tr' tg :
  preserve_tree_tag_count fn →
  tree_contains tg tr' →
  fn tr = Some tr' →
  tree_contains tg tr.
Proof.
  intros Hf H1%count_gt0_exists Heq.
  eapply count_gt0_exists.
  by erewrite Hf.
Qed.

Lemma tree_empty_iff_count tr: 
  (exists tg, tree_count_tg tg tr ≥ 1) ↔ tr ≠ empty.
Proof.
  destruct tr as [|it cld slb].
  - split; last done. simpl.
    intros (tg & Htg). lia.
  - split; first done.
    intros _. exists (it.(itag)).
    rewrite /= bool_decide_eq_true_2 //.
    lia.
Qed.

Lemma preserve_tag_count_nonempty fn tr tr' :
  preserve_tree_tag_count fn →
  tr ≠ empty →
  fn tr = Some tr' →
  tr' ≠ empty.
Proof.
  intros Hf (tg & Htg)%tree_empty_iff_count Heq.
  eapply tree_empty_iff_count. exists tg.
  by erewrite <- Hf.
Qed.

(* Since there are a lot of layers to the model (trees -> tree -> item -> perms)
   that we mostly don't really need to reason about (e.g. tree_item_included is per-item
   and we don't need tree-wide reasoning) we start with some lemmas to turn the per-trees
   wf preservation to per-item wf preservation *)

Lemma apply_within_trees_wf trs trs' blk fn:
  apply_within_trees fn blk trs = Some trs' ->
  preserve_tree_tag_count fn ->
  wf_trees trs -> wf_trees trs'.
Proof.
  intros App WFfn (WFeach & WFglob).
  unfold apply_within_trees in App; destruct (trs !! blk) as [t|] eqn:Lookup;
  simpl in App; last done.
  apply bind_Some in App as (t2 & Ht2 & [= <-]). split.
  - intros tr' it' [(<- & <-)|(Hne1 & Hne2)]%lookup_insert_Some.
    + eapply preserve_tag_count_wf; try done.
      by eapply WFeach.
    + by eapply WFeach.
  - intros blk1 blk2 tr1 tr2 tg [(Heq1 & Heq2)|(Hne1 & Hne2)]%lookup_insert_Some [(Heq1' & Heq2')|(Hne1' & Hne2')]%lookup_insert_Some Hcont1 Hcont2;
    simplify_eq; first done.
    + eapply WFglob; try done.
      eapply preserve_tag_count_contains_2; last done; done.
    + eapply WFglob; try done.
      eapply preserve_tag_count_contains_2; last done; done.
    + by eapply WFglob.
Qed.

Lemma apply_within_trees_compat trs trs' nxtp nxtp' nxtc nxtc' blk fn:
  apply_within_trees fn blk trs = Some trs' ->
  (forall tr, tree_items_compat_nexts tr nxtp nxtc -> tree_items_compat_nexts tr nxtp' nxtc') ->
  preserve_tree_compat_nexts fn nxtp nxtp' nxtc nxtc' ->
  trees_compat_nexts trs nxtp nxtc -> trees_compat_nexts trs' nxtp' nxtc'.
Proof.
  intros App WFtrans WFfn WF.
  unfold apply_within_trees in App; destruct (trs !! blk) as [t|] eqn:Lookup; inversion App as [App0]; clear App.
  destruct (fn t) eqn:Map; inversion App0 as [E]; clear App0.
  intro blk'; destruct (decide (blk = blk')); intros tr Lookup'.
  all: inversion E; simplify_eq.
  (* Handle the insertion/deletion *)
  1: rewrite lookup_insert_eq in Lookup'.
  2: rewrite lookup_insert_ne in Lookup'; [|done].
  all: simplify_eq.
  (* WF impl *)
  - apply (WFfn t); [|done]; apply (WF blk' _ Lookup).
  - apply (WFtrans tr); apply (WF blk' _ Lookup').
Qed.

Lemma tree_items_compat_next_not_containing tg1 tg2 tr ev :
  tree_contains tg1 tr →
  tree_items_compat_nexts tr tg2 ev →
  tg1 >= tg2 →
  False.
Proof.
  intros Hintro Hcompat Hle.
  eapply (exists_node_increasing _ (λ _, False)) in Hintro.
  1: eapply exists_node_eqv_existential in Hintro as (?&?&[]).
  eapply every_node_increasing; first exact Hcompat.
  eapply every_node_eqv_universal.
  intros n ? [H1 _ _ _] H3%H1. lia.
Qed.

Lemma apply_within_trees_compat_both trs trs' nxtp nxtp' nxtc nxtc' blk fn:
  apply_within_trees fn blk trs = Some trs' ->
  (forall tr, tree_items_compat_nexts tr nxtp nxtc -> tree_items_compat_nexts tr nxtp' nxtc') ->
  (forall tr tr', fn tr = Some tr' -> tree_items_compat_nexts tr nxtp nxtc -> wf_tree tr ->
          tree_items_compat_nexts tr' nxtp' nxtc' /\ wf_tree tr') ->
  (forall tr tr' tg, fn tr = Some tr' -> tree_contains tg tr' -> tree_contains tg tr \/ tg >= nxtp) ->
  trees_compat_nexts trs nxtp nxtc /\
  wf_trees trs ->
  trees_compat_nexts trs' nxtp' nxtc' /\
  wf_trees trs'.
Proof.
  intros (tr&Htr&(tr'&Hfn&[= <-])%bind_Some)%bind_Some WFtrans WFfn Hnewtags (WF1 & WF2).
  split; last split.
  - intros blk1 tr1 [(->&->)|(Hne&Hin)]%lookup_insert_Some.
    + eapply WFfn; first done. 1: by eapply WF1. 1: by eapply WF2.
    + by eapply WFtrans, WF1.
  - intros blk1 tr1 [(->&->)|(Hne&Hin)]%lookup_insert_Some.
    + eapply WFfn; first done. 1: by eapply WF1. 1: by eapply WF2.
    + by eapply WF2.
  - intros blk1 blk2 tr1 tr2 tg.
    intros [(?&?)|(Hne1&Hin1)]%lookup_insert_Some [(?&?)|(Hne2&Hin2)]%lookup_insert_Some;
      simplify_eq; intros Hcont1 Hcont2.
    + done.
    + destruct (Hnewtags _ _ _ Hfn Hcont1) as [Hold|Hgt].
      1: by eapply WF2.
      exfalso; eapply tree_items_compat_next_not_containing; first exact Hcont2.
      1: by eapply WF1. done.
    + destruct (Hnewtags _ _ _ Hfn Hcont2) as [Hold|Hgt].
      1: by eapply WF2.
      exfalso; eapply tree_items_compat_next_not_containing; first exact Hcont1.
      1: by eapply WF1. done.
    + by eapply WF2.
Qed.

Lemma apply_within_trees_compat_nonempty trs1 trs2 blk fn :
  wf_non_empty trs1 →
  (∀ tr1 tr2, tr1 ≠ empty → fn tr1 = Some tr2 → tr2 ≠ empty) →
  apply_within_trees fn blk trs1 = Some trs2 →
  wf_non_empty trs2.
Proof.
  intros Hwf Hempt (tr1&H1&(tr2&H2&[= <-])%bind_Some)%bind_Some blk' tr' [(<-&<-)|(Hin&Hne)]%lookup_insert_Some.
  - eapply Hempt; last done. by eapply Hwf.
  - by eapply Hwf.
Qed.

Lemma delete_trees_preserve_nonempty trs blk :
  wf_non_empty trs ->
  wf_non_empty (delete blk trs).
Proof.
  intros WF blk' tr Delete.
  eapply WF.
  apply (proj1 (lookup_delete_Some _ _ _ _) Delete).
Qed.

Lemma apply_within_trees_bind trs blk fn1 fn2 :
  apply_within_trees (λ x, y ← fn1 x; fn2 y) blk trs =
  trs' ← apply_within_trees fn1 blk trs;
  apply_within_trees fn2 blk trs'.
Proof.
  rewrite /apply_within_trees /=.
  destruct (trs !! blk) as [tr1|] eqn:Heq; last done.
  rewrite /=. destruct (fn1 tr1) as [tr1b|]; last done.
  rewrite /= lookup_insert_eq /=. destruct (fn2 tr1b) as [tr1c|]; last done.
  rewrite /= insert_insert_eq //.
Qed.

Lemma apply_within_trees_same_dom (trs trs' : gmap positive (tree item)) blk fn :
  apply_within_trees fn blk trs = Some trs' ->
  dom trs = dom trs'.
Proof.
  unfold apply_within_trees.
  destruct (trs !! blk) as [t|] eqn:Lookup; rewrite !Lookup; simpl; [|intro H; inversion H].
  destruct (fn t); simpl; [|intro H; inversion H].
  intro H; injection H; clear H; intro; subst.
  rewrite dom_insert_L.
  rewrite subseteq_union_1_L; [set_solver|].
  rewrite singleton_subseteq_l.
  apply elem_of_dom.
  auto.
Qed.

Lemma extend_trees_wf trs tr blk :
  wf_trees trs →
  wf_tree tr →
  (∀ blk tr' tg, trs !! blk = Some tr' → tree_contains tg tr → tree_contains tg tr' → False) →
  wf_trees (<[blk := tr]> trs).
Proof.
  intros (WFs & Hunq) WF Hisnew. split.
  - intros blk' tr' [(-> & ->)|(Hne & Hin)]%lookup_insert_Some; first done.
    by eapply WFs.
  - intros blk1 blk2 tr1 tr2 tg.
    intros [(?&?)|(Hne1&Hin1)]%lookup_insert_Some [(?&?)|(Hne2&Hin2)]%lookup_insert_Some;
    simplify_eq; intros Hcont1 Hcont2.
    + done.
    + exfalso. by eapply Hisnew.
    + exfalso. by eapply Hisnew.
    + by eapply Hunq.
Qed.

Lemma extend_trees_compat_nexts trs tr blk snp snc :
  trees_compat_nexts trs snp snc →
  tree_items_compat_nexts tr snp snc →
  trees_compat_nexts (<[blk := tr]> trs) snp snc.
Proof.
  intros H1 H2 blk' tr' [(<-&<-)|(Hne1&Hin1)]%lookup_insert_Some; first done.
  by eapply H1.
Qed.

Lemma delete_trees_wf trs blk :
  wf_trees trs ->
  wf_trees (delete blk trs).
Proof.
  intros (Heach&Hunq); split.
  - intros blk' tr' (Hin&Hne)%lookup_delete_Some.
    by eapply Heach.
  - intros blk1 blk2 tr1 tr2 tg (_&Hin1)%lookup_delete_Some (_&Hin2)%lookup_delete_Some.
    by eapply Hunq.
Qed.

Lemma delete_trees_compat_nexts trs blk nxtp nxtc :
  trees_compat_nexts trs nxtp nxtc ->
  trees_compat_nexts (delete blk trs) nxtp nxtc.
Proof.
  intros WFs blk'.
  intros tr' (Hin&Hne)%lookup_delete_Some.
  by eapply WFs.
Qed.

Lemma delete_trees_parents_more_init trs blk :
  each_tree_parents_more_init trs ->
  each_tree_parents_more_init (delete blk trs).
Proof.
  intros WFs blk'.
  intros tr' (Hin&Hne)%lookup_delete_Some.
  by eapply WFs.
Qed.

Lemma delete_trees_parents_more_active trs blk :
  each_tree_parents_more_active trs ->
  each_tree_parents_more_active (delete blk trs).
Proof.
  intros WFs blk'.
  intros tr' (Hin&Hne)%lookup_delete_Some.
  by eapply WFs.
Qed.

Lemma delete_trees_parents_not_disabled C trs blk :
  each_tree_protected_parents_not_disabled C trs ->
  each_tree_protected_parents_not_disabled C (delete blk trs).
Proof.
  intros WFs blk'.
  intros tr' (Hin&Hne)%lookup_delete_Some.
  by eapply WFs.
Qed.

Lemma delete_trees_no_active_cousins C trs blk :
  each_tree_no_active_cousins C trs ->
  each_tree_no_active_cousins C (delete blk trs).
Proof.
  intros WFs blk'.
  intros tr' (Hin&Hne)%lookup_delete_Some.
  by eapply WFs.
Qed.

(* Now we get from per-tree to per-item *)
Lemma tree_joinmap_preserve_prop tr tr' (fn:item -> option item) (P:item -> Prop) :
  (forall it it', fn it = Some it' -> P it -> P it') ->
  every_node P tr ->
  join_nodes (map_nodes fn tr) = Some tr' ->
  every_node P tr'.
Proof.
  intros Preserve All Join.
  pose (proj1 (join_success_condition _) (mk_is_Some _ _ Join)) as AllSome.
  generalize dependent tr'.
  induction tr as [|data ? IHtr1 ? IHtr2]; intros tr' JoinSome AllSome; simpl in *; [injection JoinSome; intros; simplify_eq; auto|].
  destruct AllSome as [[data' Some0] [Some1 Some2]].
  rewrite Some0 in JoinSome; simpl in JoinSome.
  destruct (proj2 (join_success_condition _) Some1) as [tr1' Some1'].
  destruct (proj2 (join_success_condition _) Some2) as [tr2' Some2'].
  rewrite Some1' in JoinSome; rewrite Some2' in JoinSome; simpl in JoinSome.
  injection JoinSome; intros; subst.
  destruct All as [All0 [All1 All2]].
  try repeat split.
  - apply (Preserve data _ Some0 All0).
  - apply (IHtr1 All1); apply Some1'.
  - apply (IHtr2 All2); apply Some2'.
Qed.

Lemma joinmap_preserve_tree_tag_count_dep fn :
  (∀ tr, preserve_item_metadata (fn tr)) →
  preserve_tree_tag_count (fun tr => join_nodes (map_nodes (fn tr) tr)).
Proof.
  intros Hfn tr.
  remember (fn tr) as fntr eqn:Heq. specialize (Hfn tr). rewrite <- Heq in Hfn.
  clear Heq.
  induction tr as [|data tr1 IHtr1 tr2 IHtr2]; intros tr' tg Heq.
  1: by injection Heq as <-.
  move : Heq => /=.
  intros (itroot&Hitroot&(tr1'&Htr1'&(tr2'&Htr2&[= <-])%bind_Some)%bind_Some)%bind_Some.
  simpl; f_equal; first f_equal.
  - destruct (Hfn _ _ Hitroot) as (H1 & H2 & H3).
    rewrite !bool_decide_decide.
    destruct decide as [Heq|Heq]; rewrite H1 in Heq.
    1: rewrite decide_True //. rewrite decide_False //.
  - by eapply IHtr1.
  - by apply IHtr2.
Qed.

Lemma joinmap_preserve_tree_tag_count fn :
  preserve_item_metadata fn →
  preserve_tree_tag_count (fun tr => join_nodes (map_nodes fn tr)).
Proof.
  intros H. by eapply joinmap_preserve_tree_tag_count_dep.
Qed.

Lemma deallocate_preserve_tree_tag_count cids tg range :
  preserve_tree_tag_count (memory_deallocate cids tg range).
Proof.
  intros tr tr' Nonempty Dealloc.
  rewrite /memory_deallocate /memory_access_nonchildren_only in Dealloc.
  eapply bind_Some in Dealloc as (trm & H1 & H2).
  eapply joinmap_preserve_tree_tag_count in H1.
  2: eapply item_apply_access_preserves_metadata_dep.
  erewrite H1.
  eapply joinmap_preserve_tree_tag_count.
  2: exact H2.
  intros it1 it2 Heq; repeat destruct bool_decide; simpl in Heq; simplify_eq; done.
Qed.

Lemma create_child_preserve_nonempty cids oldtg newtg pk im rk cid tr tr' :
  create_child cids oldtg newtg pk im rk cid tr = Some tr' →
  tr ≠ empty →
  tr' ≠ empty.
Proof.
  intros (x&Hx&[= <-])%bind_Some Hne.
  destruct tr as [|data].
  1: contradiction.
  simpl. destruct (decide (IsTag oldtg data)); intro H; inversion H.
Qed.

Lemma tree_apply_access_same_count
  {tr tr' tr0 tg fn cids acc_tg range} :
  join_nodes
    (map_nodes
       (λ it : item,
          item_apply_access fn cids (rel_dec tr0 acc_tg (itag it)) range it) tr) =
  Some tr' → tree_count_tg tg tr = tree_count_tg tg tr'.
Proof.
  intros H.
  eapply joinmap_preserve_tree_tag_count; last done.
  eapply item_apply_access_preserves_metadata_dep.
Qed.

Lemma tree_apply_access_preserve_unique
  {tr tr' tg fn cids acc_tg range} :
  tree_apply_access fn cids acc_tg range tr = Some tr' ->
  tree_unique tg tr <-> tree_unique tg tr'.
Proof.
  rewrite /tree_unique. intro Access.
  erewrite tree_apply_access_same_count; [|exact Access].
  tauto.
Qed.

Lemma tree_apply_access_wf fn tr tr' cids tg range :
  wf_tree tr ->
  tree_apply_access fn cids tg range tr = Some tr' ->
  wf_tree tr'.
Proof.
  eapply preserve_tag_count_wf.
  rewrite /tree_apply_access.
  eapply joinmap_preserve_tree_tag_count_dep.
  intros ?. eapply item_apply_access_preserves_metadata_dep.
Qed.

Lemma tree_apply_access_compat_nexts fn tr tr' cids tg range nxtp nxtc :
  (∀ rp ip, preserves_lazy_perm_wf (fn rp ip)) →
  (∀ rp ip, preserves_reach (fn rp ip)) →
  tree_items_compat_nexts tr nxtp nxtc ->
  tree_apply_access fn cids tg range tr = Some tr' ->
  tree_items_compat_nexts tr' nxtp nxtc.
Proof.
  intros Hlazy Hpreach.
  eapply tree_joinmap_preserve_prop.
  intros it1 it2 Hacc.
  pose proof Hacc as (H1&H2&H3)%item_apply_access_preserves_metadata.
  intros [Htag Hcid Hdef HIM Hperms Hreach]. split.
  1-3: rewrite /= -?H1 -?H2 -?H3 //.
  all: pose proof Hacc as (px&Hpx&[= <-])%bind_Some; simpl. 
  1: intros Hsome k Heq; destruct (px !! k) eqn:Hpnew.
  2: { simpl in Heq. eapply (HIM (ltac:(done)) (fresh (dom (iperm it1)))).
       rewrite not_elem_of_dom_1. 1: done. eapply is_fresh. }
  3: intros Hndis; specialize (Hreach Hndis).
  2,3: apply map_Forall_lookup_2; intros k pnew Hpnew.
  all: eapply (mem_apply_range'_spec _ _ k) in Hpx.
  all: destruct decide.
  2: { rewrite Hpx in Hpnew. eapply HIM. 1: done.
       rewrite -Hpnew // in Heq. apply Heq. }
  3,5: rewrite Hpnew in Hpx; symmetry in Hpx;
       eapply map_Forall_lookup_1 in Hperms; try done.
  2,4: destruct Hpx as (p'&Hp'&Hfn);
       rewrite Hpnew in Hp'; injection Hp' as <-.
  - destruct Hpx as (?&Hkk&Hpx).
    rewrite Hpnew in Hkk. injection Hkk as <-.
    eapply Hpreach in Hpx. rewrite Heq in Hpx.
    destruct perm as [|[]| | | |] eqn:Hperm in Hpx. 1,2,3,5,6,7: by cbv in Hpx.
    eapply HIM; first done. done.
  - eapply Hlazy; first exact Hfn.
    rewrite /default. destruct (iperm it1 !! k) as [pold|] eqn:Hpold.
    + rewrite Hpold. simpl. eapply map_Forall_lookup_1 in Hperms; done.
    + rewrite Hpold. intros Hf. exfalso. apply Hdef, Hf.
  - eapply reach_transitive. 2: eapply Hpreach; exact Hfn.
    rewrite /default. destruct (iperm it1 !! k) as [pold|] eqn:Hpold.
    + rewrite Hpold. simpl. eapply map_Forall_lookup_1 in Hreach; done.
    + rewrite Hpold. simpl. by eapply reach_reflexive.
  - eapply map_Forall_lookup_1 in Hreach; done.
Qed.

Lemma join_map_id_identical (fn : item -> option item) tr :
  (∀ it, exists_node (eq it) tr → fn it = Some it) →
  join_nodes (map_nodes fn tr) = Some tr.
Proof.
  induction tr as [|data ? IHtr1 ? IHtr2]; intros Hfoo; simpl in *.
  - done.
  - rewrite (Hfoo data) /= //. 2: by left.
    rewrite IHtr1. 1: rewrite IHtr2 //.
    all: intros ??; eapply Hfoo; tauto.
Qed.

Lemma join_map_id_identical_or_fail (fn : item -> option item) tr tr' :
  (∀ it r, exists_node (eq it) tr → fn it = Some r → r = it) →
  join_nodes (map_nodes fn tr) = Some tr' ->
  tr = tr'.
Proof.
  revert tr'.
  induction tr as [|data ? IHtr1 ? IHtr2]; intros tr' Hfoo; simpl in *.
  - by intros [= <-].
  - destruct (fn data) as [i|] eqn:Hfn; last done. 
    rewrite (Hfoo data i) /= //. 2: by left.
    intros (tr1'&Htr1&(tr2'&Htr2&[= <-])%bind_Some)%bind_Some.
    f_equal.
    + eapply IHtr1. 2: done. intros ????; eapply Hfoo; tauto.
    + eapply IHtr2. 2: done. intros ????; eapply Hfoo; tauto.
Qed.

Lemma join_map_id_is_Some_identical (P : item -> bool) tr tr' :
  join_nodes (map_nodes (fun it => if P it then None else Some it) tr) = Some tr' ->
  tr = tr'.
Proof.
  eapply join_map_id_identical_or_fail.
  intros it r _ . destruct (P it); try done. congruence.
Qed.

Lemma memory_deallocate_wf tr tr' cids tg range :
  wf_tree tr ->
  memory_deallocate cids tg range tr = Some tr' ->
  wf_tree tr'.
Proof.
  rewrite /memory_deallocate /memory_access_nonchildren_only.
  intros Hwf (mid&H1&H2)%bind_Some.
  eapply tree_apply_access_wf in H1; last done.
  apply join_map_id_is_Some_identical in H2.
  by subst mid.
Qed.

Lemma memory_deallocate_compat_nexts tr tr' cids tg range nxtp nxtc :
  tree_items_compat_nexts tr nxtp nxtc ->
  memory_deallocate cids tg range tr = Some tr' ->
  tree_items_compat_nexts tr' nxtp nxtc.
Proof.
  intros WF Dealloc.
  rewrite /memory_deallocate /memory_access /memory_access_maybe_nonchildren_only /= in Dealloc.
  remember (tree_apply_access _ _ _ _ _) as tr''.
  destruct tr'' as [tr''|]; simpl in Dealloc; [|discriminate].
  assert (tree_items_compat_nexts tr'' nxtp nxtc) as WF''. {
    unshelve eapply (tree_apply_access_compat_nexts _ _ _ _ _ _ _ _ _ _ WF ltac:(symmetry; eassumption)).
    1: intros ??; eapply (apply_access_perm_maybe_wf false).
    1: intros ??; eapply (apply_access_perm_maybe_reach false).
  }
  erewrite <- (join_map_id_is_Some_identical _ tr'' tr').
  - assumption.
  - exact Dealloc.
Qed.

Lemma memory_access_wf b tr tr' acc cids tg range  :
  wf_tree tr ->
  memory_access_maybe_nonchildren_only b acc cids tg range tr = Some tr' ->
  wf_tree tr'.
Proof.
  intros WF Dealloc.
  by eapply tree_apply_access_wf.
Qed.

Lemma memory_access_tag_count b acc cids tg range :
  preserve_tree_tag_count (memory_access_maybe_nonchildren_only b acc cids tg range).
Proof.
  eapply joinmap_preserve_tree_tag_count_dep.
  intros tr. eapply item_apply_access_preserves_metadata_dep.
Qed.

Lemma memory_access_compat_nexts b tr tr' acc cids tg range nxtp nxtc :
  tree_items_compat_nexts tr nxtp nxtc ->
  memory_access_maybe_nonchildren_only b acc cids tg range tr = Some tr' ->
  tree_items_compat_nexts tr' nxtp nxtc.
Proof.
  intros WF Dealloc.
  eapply tree_apply_access_compat_nexts; try done.
  1: intros ??; eapply apply_access_perm_maybe_wf.
  1: intros ??; eapply apply_access_perm_maybe_reach.
Qed.


Lemma init_mem_singleton_dom (blk:block) n sz :
  (sz > 0)%nat ->
  ({[blk]}:gset block) = set_map fst (dom (init_mem (blk, n) sz ∅)).
Proof.
  induction sz as [|sz IHsz] in n|-*; simpl; intros H.
  - inversion H.
  - rewrite dom_insert_L set_map_union_L set_map_singleton_L //=.
    destruct sz as [|sz].
    + rewrite dom_empty_L set_map_empty union_empty_r_L //.
    + rewrite /shift_loc. rewrite <- IHsz; [|lia].
      set_solver.
Qed.

Lemma same_blocks_init_extend h off sz trs nxtp :
  (sz > 0)%nat ->
  same_blocks h trs ->
  same_blocks (init_mem (fresh_block h, off) sz h)
    (extend_trees nxtp (fresh_block h) off sz trs).
Proof.
  intros Nonzero Same.
  rewrite /same_blocks init_mem_dom dom_insert_L set_map_union_L.
  rewrite union_comm_L.
  rewrite /same_blocks in Same; rewrite Same; clear Same.
  erewrite init_mem_singleton_dom; [|eauto].
  set_solver.
Qed.

Lemma wf_init_tree t' off sz:
  wf_tree (init_tree t' off sz).
Proof.
  intros tg H.
  cbv in H. destruct_or!; try done.
  subst tg.
  by rewrite /tree_unique /init_tree /= bool_decide_true.
Qed.

Lemma init_tree_compat_nexts c t t' off sz :
  (t' < t)%nat ->
  tree_items_compat_nexts (init_tree t' off sz) t c.
Proof.
  intros Hok. cbv -[init_perms].
  repeat split; simpl.
  - intros ? ->. lia.
  - done.
  - done.
  - intros [? [=]].
  - eapply map_Forall_lookup_2.
    intros k p [(Hr&Heq)|(Hr&Heq)]%mem_apply_range'_defined_lookup_Some.
    + subst p. done.
    + by rewrite lookup_empty in Heq.
  - intros Hne. congruence.
Qed.

Lemma init_tree_nonempty t off sz :
  forall tr, tr = (init_tree t off sz) -> tr ≠ empty.
Proof.
  intros. subst.
  rewrite /init_tree //.
Qed.

Lemma init_tree_contains_only tg1 off sz tg2 :
  tree_contains tg1 (init_tree tg2 off sz) -> tg1 = tg2.
Proof.
  intros H. cbv in H. by destruct_or!.
Qed.

Lemma every_child_initial_tree tg P it : 
  (it.(itag) = tg → P it it) →
  every_child tg P (branch it empty empty).
Proof. intros H. repeat split; try done. by eapply H. Qed.

Lemma extend_trees_more_init trs n b z n2 :
  each_tree_parents_more_init trs →
  each_tree_parents_more_init (extend_trees n b z n2 trs).
Proof.
  intros H blk tr. rewrite /extend_trees.
  intros [(<-&<-)|(Hne1&Htr)]%lookup_insert_Some.
  2: by eapply H.
  rewrite /parents_more_init.
  intros tg. eapply every_child_initial_tree.
  intros _ l. done.
Qed.

Lemma extend_trees_more_active trs n b z n2 :
  each_tree_parents_more_active trs →
  each_tree_parents_more_active (extend_trees n b z n2 trs).
Proof.
  intros H blk tr. rewrite /extend_trees.
  intros [(<-&<-)|(Hne1&Htr)]%lookup_insert_Some.
  2: by eapply H.
  rewrite /parents_more_init.
  intros tg. eapply every_child_initial_tree.
  intros _ l ?. by left.
Qed.

Lemma extend_trees_not_disabled C trs n b z n2 :
  each_tree_protected_parents_not_disabled C trs →
  each_tree_protected_parents_not_disabled C (extend_trees n b z n2 trs).
Proof.
  intros H blk tr. rewrite /extend_trees.
  intros [(<-&<-)|(Hne1&Htr)]%lookup_insert_Some.
  2: by eapply H.
  rewrite /parents_more_init.
  intros tg l. eapply every_child_initial_tree.
  intros _ _ (c&Hc&_). done.
Qed.

Lemma extend_trees_no_active_cousins C trs n b z n2 :
  each_tree_no_active_cousins C trs →
  each_tree_no_active_cousins C (extend_trees n b z n2 trs).
Proof.
  intros H blk tr. rewrite /extend_trees.
  intros [(<-&<-)|(Hne1&Htr)]%lookup_insert_Some.
  2: by eapply H.
  intros tg1 it1 tg2 it2 off (Hx1&_) (Hx2&_) Hreldec.
  assert (tg1 = tg2) as ->.
  2: by eapply cousins_different in Hreldec.
  cbv in Hx1, Hx2. lia.
Qed.


Lemma init_perms_lookup perm off sz i :
  match ((init_perms perm off sz) !! i) with
    Some p => p = mkPerm PermInit perm ∧ off ≤ i ∧ i < off + sz
  | None => ¬ (off ≤ i ∧ i < off + sz) end.
Proof.
  opose proof (mem_apply_range'_defined_spec (λ _, mkPerm PermInit perm) (off, sz) i ∅ _ eq_refl) as HH.
  rewrite /init_perms.
  destruct (decide (range'_contains (off, sz) i)) as [(Hin1&Hin2)|Hnin].
  - destruct HH as (v&Hv&HH). rewrite Hv. simpl in *. done.
  - rewrite HH lookup_empty /=. done.
Qed.

Lemma initial_item_init_mem h tg sz :
  let blk := fresh_block h in
  root_invariant blk (initial_item tg 0 sz) (init_mem (blk, 0) sz h).
Proof.
  split; first done. split; first done. intros off.
  rewrite /item_lookup /=.
  opose proof (init_perms_lookup Active 0 sz off) as H.
  edestruct (init_mem_lookup (fresh_block h, 0) sz h) as (H1&H2).
  destruct (init_perms Active 0 sz !! off) as [p'|].
  * destruct H as (->&Hin). simpl.
    assert (∃ (offi:nat), Z.of_nat offi = off) as (offi&<-) by (exists (Z.to_nat off); lia).
    rewrite (H1 offi); first done. lia.
  * simpl. rewrite H2.
    -- eapply not_elem_of_dom, is_fresh_block.
    -- intros i Hi. rewrite /shift_loc /=. intros [= Heq]. lia.
Qed.

Lemma init_mem_only_only_one_block h l sz l2 :
  l.1 ≠ l2.1 →
  (init_mem l sz h) !! l2 = h !! l2.
Proof.
  intros H2.
  opose proof (init_mem_lookup _ _ _) as (_&H3).
  erewrite H3; first done.
  intros i Hi. destruct l, l2. rewrite /shift_loc /=. intros [= H4 H5]. by simpl in *.
Qed.

Lemma alloc_step_wf (σ σ': state) e e' l bor ptr efs:
  mem_expr_step σ.(shp) e (AllocEvt l bor ptr) σ'.(shp) e' efs →
  bor_step σ.(strs) σ.(scs) σ.(snp) σ.(snc)
           (AllocEvt l bor ptr)
           σ'.(strs) σ'.(scs) σ'.(snp) σ'.(snc) →
  state_wf σ → state_wf σ'.
Proof.
  destruct σ as [h trs cids nxtp nxtc].
  destruct σ' as [h' trs' cids' nxtp' nxtc']. simpl.
  intros BS IS WF. inversion BS. clear BS. simplify_eq.
  inversion IS as [x| | | | | | | | |]; clear IS. simpl in *; simplify_eq. constructor; simpl.
  - apply same_blocks_init_extend; [lia|].
    apply WF.
  - apply extend_trees_wf.
    * apply WF.
    * apply wf_init_tree.
    * intros blk tro tg Hin Hinit%init_tree_contains_only Hintro.
      subst tg.
      pose proof (state_wf_tree_compat _ WF _ _ Hin) as Hcompat.
      simpl in Hcompat.
      eapply tree_items_compat_next_not_containing; [done..|]; lia.
  - eapply extend_trees_more_init, WF.
  - eapply extend_trees_more_active, WF.
  - eapply extend_trees_not_disabled, WF.
  - eapply extend_trees_no_active_cousins, WF.
  - eapply extend_trees_compat_nexts.
    * eapply trees_compat_nexts_mono; last eapply WF.
      all: simpl; lia.
    * eapply init_tree_compat_nexts; lia. 
  - intros blk tr. rewrite /extend_trees.
    intros [(<-&<-)|(Hne&Hin)]%lookup_insert_Some.
    + simpl. split; last done. eapply initial_item_init_mem.
    + specialize (state_wf_roots_active _ WF blk tr Hin) as Hact. simpl.
      destruct tr as [|it ??]; first done. destruct Hact as ((Hinit&Hact)&->).
      rewrite /root_invariant /= in Hact|-*. rewrite /root_invariant.
      destruct Hact as (Hprot&Hact); split_and!; try done.
      intros off. specialize (Hact off).
      rewrite !init_mem_only_only_one_block //.
  - apply WF.
Qed.

Lemma trees_deallocate_isSome trs cids tg blk m sz :
  is_Some (apply_within_trees (memory_deallocate cids tg (m, sz)) blk trs) ->
  exists tr, trs !! blk = Some tr /\ is_Some (memory_deallocate cids tg (m, sz) tr).
Proof.
  unfold apply_within_trees. destruct (trs !! blk) as [t|]; simpl; [|intro H; inversion H as [? H0]; inversion H0].
  intro isSome. exists t. destruct (memory_deallocate cids tg (m, sz) t) as [t'|]; simpl; [|inversion isSome as [? H0]; inversion H0].
  auto.
Qed.

Lemma maybe_non_children_only_more_init b1 acc rd b op np :
  maybe_non_children_only b1 (apply_access_perm acc) rd b op = Some np →
  initialized op = PermInit → initialized np = PermInit.
Proof.
  intros H.
  edestruct (maybe_non_children_only_effect_or_nop b1) as [Heq|Heq];
  erewrite Heq in H. 2: by congruence.
  eapply bind_Some in H as (x&Hx&(y&Hy&[= <-])%bind_Some).
  intros ->. done.
Qed.

Lemma maybe_non_children_only_more_disabled b1 acc rd b op np :
  maybe_non_children_only b1 (apply_access_perm acc) rd b op = Some np →
  perm op = Disabled → perm np = Disabled.
Proof.
  intros H.
  edestruct (maybe_non_children_only_effect_or_nop b1) as [Heq|Heq];
  erewrite Heq in H. 2: by congruence.
  eapply bind_Some in H as (x&Hx&(y&Hy&[= <-])%bind_Some).
  intros Hdis. rewrite Hdis in Hx.
  cbv in Hx. destruct acc, rd; simpl in Hx; try done.
  all: injection Hx as ->; simpl.
  all: repeat (case_match; simplify_eq; try done).
Qed.

Lemma most_init_is_init m1 m2 :
  most_init m1 m2 = PermInit ↔
  (m1 = PermInit ∨ m2 = PermInit).
Proof.
  destruct m1, m2; simpl; tauto.
Qed.


Lemma memory_access_compat_parents_more_init b tr tr' acc cids tg range :
  wf_tree tr →
  tree_contains tg tr →
  parents_more_init tr ->
  memory_access_maybe_nonchildren_only b acc cids tg range tr = Some tr' ->
  parents_more_init tr'.
Proof.
  intros WFunq WFinit Hcont Dealloc.
  assert (tree_unique tg tr) as Hunq by by eapply WFunq.
  intros tg_par.
  destruct (decide (tree_contains tg_par tr)) as [Hunqpar%WFunq|Hninpar].
  2: { eapply every_child_not_in, count_0_not_exists. erewrite <-memory_access_tag_count; last done.
       by eapply count_0_not_exists. }
  assert (wf_tree tr') as Hwfunq'.
  { eapply preserve_tag_count_wf. 1: eapply memory_access_tag_count. all: done. }
  assert (tree_unique tg_par tr') as Hunqpar'.
  { rewrite /tree_unique. by erewrite <- memory_access_tag_count. }
  setoid_rewrite every_child_ParentChildIn; [|try done..].
  intros itpar' Hitpar' tgcld Hunqcld' HPCpc'.
  epose proof Hunqcld' as (itcld'&Hitcld')%unique_lookup.
  eapply every_node_eqv_universal.
  intros nitcld' Hn Hn2.
  assert (nitcld' = itcld') as ->.
  { eapply every_node_eqv_universal in Hitcld'. 1: apply Hitcld'. all: done. }
  clear Hn2 Hn.
  assert (tree_unique tgcld tr) as Hunqcld.
  { rewrite /tree_unique. by erewrite memory_access_tag_count. }
  epose proof Hunqcld as (itcld&Hitcld)%unique_lookup.
  epose proof Hunqpar as (itpar&Hitpar)%unique_lookup.
  epose proof Dealloc as Hspecpar. eapply apply_access_spec_per_node in Hspecpar.
  3: exact Hitpar. 2: by eapply unique_exists.
  destruct Hspecpar as (itpar'2 & Hpostpar & Hcont2 & Hdet2).
  assert (itpar'2 = itpar') as ->.
  { eapply tree_determined_unify; done. } clear Hcont2 Hdet2.
  epose proof Dealloc as Hspeccld. eapply apply_access_spec_per_node in Hspeccld.
  3: exact Hitcld. 2: by eapply unique_exists.
  destruct Hspeccld as (itcld'2 & Hpostcld & Hcont2 & Hdet2).
  assert (itcld'2 = itcld') as ->.
  { eapply tree_determined_unify; done. } clear Hcont2 Hdet2.
  specialize (Hcont tg_par). setoid_rewrite every_child_ParentChildIn in Hcont.
  2: done. 2: done. 
  ospecialize (Hcont _ Hitpar tgcld _ _). 1: done. 1: by setoid_rewrite access_eqv_rel.
  epose proof HPCpc' as HPCpc. setoid_rewrite <- access_eqv_rel in HPCpc; try done.
  eapply every_node_eqv_universal in Hcont.
  2: { eapply exists_determined_exists. 2: exact Hitcld. 1: by eapply unique_exists. }
  ospecialize (Hcont _).
  { eapply tree_determined_specifies_tag; last done. by eapply unique_exists. }
  symmetry in Hpostpar. symmetry in Hpostcld.
  eapply bind_Some in Hpostpar as (pp&Hpostpar&[= <-]).
  eapply bind_Some in Hpostcld as (pc&Hpostcld&[= <-]).
  intros l. specialize (Hcont l).
  eapply (mem_apply_range'_spec _ _ l) in Hpostpar.
  eapply (mem_apply_range'_spec _ _ l) in Hpostcld.
  destruct decide as [Hrange|Hnrange]; last first.
  { rewrite /item_lookup /= Hpostpar Hpostcld. apply Hcont. }
  destruct Hpostpar as (ppnew&Hppnew&Haccp).
  destruct Hpostcld as (pcnew&Hpcnew&Haccc).
  rewrite /item_lookup /= Hppnew Hpcnew /=.
  edestruct (maybe_non_children_only_effect_or_nop_strong b) as [(Heq&Hfacts)|(Heq&->&imm&Hreldec)].
  all: erewrite Heq in Haccc.
  - rewrite /rel_dec in Haccc. 
    eapply bind_Some in Haccc as (x&_&(y&_&[= <-])%bind_Some). simpl.
    intros [Hpre|Hcld]%most_init_is_init.
    { rewrite Hpre /= in Hpcnew. rewrite /item_lookup Hpre in Hcont.
      eapply maybe_non_children_only_more_init in Haccp. 2: by apply Hcont.
      done. }
    destruct (decide (ParentChildIn (itag itcld) tg tr)) as [HHHcld|?]; last done.
    clear Hcld. destruct b; last first.
    { eapply bind_Some in Haccp as (xp&_&(yp&_&[= <-])%bind_Some). simpl.
      eapply most_init_is_init. right.
      rewrite /rel_dec. rewrite decide_True; first done.
      erewrite tree_determined_specifies_tag; last done; last by eapply unique_exists.
      eapply ParentChild_transitive. 1: done.
      erewrite tree_determined_specifies_tag in HHHcld; last done; last by eapply unique_exists. done. }
    { destruct Hfacts as [Hnb|Hcomplicated]; first done. clear Heq.
      assert (itag itpar = tg_par) as Htgpar.
      { eapply tree_determined_specifies_tag; last done. by eapply unique_exists. }
      assert (itag itcld = tgcld) as Htgcld.
      { eapply tree_determined_specifies_tag; last done. by eapply unique_exists. }
      rewrite /rel_dec /= in Haccp.
      rewrite decide_True in Haccp.
      2: { rewrite Htgpar. rewrite Htgcld in HHHcld.
           eapply ParentChild_transitive. 1: exact HPCpc. done. }
      simpl in Haccp.
      eapply bind_Some in Haccp as (xp&_&(yp&_&Hy)%bind_Some).
      rewrite /= most_init_comm /= in Hy. injection Hy as <-. done. }
  - injection Haccc as <-. intros Hinit.
    destruct (iperm itcld !! l) as [ipoc|] eqn:Heqitcld; rewrite Heqitcld in Hinit; simpl in Hinit; last done.
    rewrite Heqitcld /= in Hpcnew.
    rewrite /item_lookup Heqitcld /= in Hcont. specialize (Hcont Hinit).
    simpl in Haccp. eapply (maybe_non_children_only_more_init true) in Haccp; done.
Qed.


Lemma memory_access_compat_parents_more_active b tr tr' acc cids tg range :
  wf_tree tr →
  tree_contains tg tr →
  parents_more_active tr ->
  memory_access_maybe_nonchildren_only b acc cids tg range tr = Some tr' ->
  parents_more_active tr'.
Proof.
  intros WFunq Hcont WFactive Dealloc.
  assert (tree_unique tg tr) as Hunq by by eapply WFunq.
  intros tg_par.
  destruct (decide (tree_contains tg_par tr)) as [Hunqpar%WFunq|Hninpar].
  2: { eapply every_child_not_in, count_0_not_exists. erewrite <-memory_access_tag_count; last done.
       by eapply count_0_not_exists. }
  assert (wf_tree tr') as Hwfunq'.
  { eapply preserve_tag_count_wf. 1: eapply memory_access_tag_count. all: done. }
  assert (tree_unique tg_par tr') as Hunqpar'.
  { rewrite /tree_unique. by erewrite <- memory_access_tag_count. }
  setoid_rewrite every_child_ParentChildIn; [|try done..].
  intros itpar' Hitpar' tgcld Hunqcld' HPCpc'.
  epose proof Hunqcld' as (itcld'&Hitcld')%unique_lookup.
  eapply every_node_eqv_universal.
  intros nitcld' Hn Hn2.
  assert (nitcld' = itcld') as ->.
  { eapply every_node_eqv_universal in Hitcld'. 1: apply Hitcld'. all: done. }
  clear Hn2 Hn.
  assert (tree_unique tgcld tr) as Hunqcld.
  { rewrite /tree_unique. by erewrite memory_access_tag_count. }
  epose proof Hunqcld as (itcld&Hitcld)%unique_lookup.
  epose proof Hunqpar as (itpar&Hitpar)%unique_lookup.
  epose proof Dealloc as Hspecpar. eapply apply_access_spec_per_node in Hspecpar.
  3: exact Hitpar. 2: by eapply unique_exists.
  destruct Hspecpar as (itpar'2 & Hpostpar & Hcont2 & Hdet2).
  assert (itpar'2 = itpar') as ->.
  { eapply tree_determined_unify; done. } clear Hcont2 Hdet2.
  epose proof Dealloc as Hspeccld. eapply apply_access_spec_per_node in Hspeccld.
  3: exact Hitcld. 2: by eapply unique_exists.
  destruct Hspeccld as (itcld'2 & Hpostcld & Hcont2 & Hdet2).
  assert (itcld'2 = itcld') as ->.
  { eapply tree_determined_unify; done. } clear Hcont2 Hdet2.
  specialize (WFactive tg_par). setoid_rewrite every_child_ParentChildIn in WFactive.
  2: done. 2: done. 
  ospecialize (WFactive _ Hitpar tgcld _ _). 1: done. 1: by setoid_rewrite access_eqv_rel.
  epose proof HPCpc' as HPCpc. setoid_rewrite <- access_eqv_rel in HPCpc; try done.
  eapply every_node_eqv_universal in WFactive.
  2: { eapply exists_determined_exists. 2: exact Hitcld. 1: by eapply unique_exists. }
  ospecialize (WFactive _).
  { eapply tree_determined_specifies_tag; last done. by eapply unique_exists. }
  symmetry in Hpostpar. symmetry in Hpostcld.
  eapply bind_Some in Hpostpar as (pp&Hpostpar&[= <-]).
  eapply bind_Some in Hpostcld as (pc&Hpostcld&[= <-]).
  intros l. specialize (WFactive l).
  eapply (mem_apply_range'_spec _ _ l) in Hpostpar.
  eapply (mem_apply_range'_spec _ _ l) in Hpostcld.
  destruct decide as [Hrange|Hnrange]; last first.
  { rewrite /item_lookup /= Hpostpar Hpostcld. apply WFactive. }
  destruct Hpostpar as (ppnew&Hppnew&Haccp).
  destruct Hpostcld as (pcnew&Hpcnew&Haccc).
  rewrite /item_lookup /= Hppnew Hpcnew /=.
  rewrite /item_lookup /= in WFactive.
  assert (itag itcld = tgcld) as Htgitcld.
  { eapply tree_determined_specifies_tag. 2: done. by eapply unique_exists. }
  assert (itag itpar = tg_par) as Htgitpar.
  { eapply tree_determined_specifies_tag. 2: done. by eapply unique_exists. }
  destruct (decide (ParentChildIn tgcld tg tr)) as [HPCI|HnPCI].
  { edestruct (maybe_non_children_only_effect_or_nop_strong b) as [(Heq&Hfacts)|(Heq&->&imm&Hreldec)].
    all: erewrite Heq in Haccc; clear Heq. 2: rewrite /rel_dec Htgitcld decide_True // in Hreldec.
    intros Hnewact. rewrite /rel_dec Htgitcld decide_True // in Haccc.
    eapply bind_Some in Haccc as (xc&Hxc&(yc&Hyc&[= <-])%bind_Some). simpl in Hnewact. subst yc.
    assert (xc = Active) as -> by repeat (case_match; simplify_eq; try done).
    edestruct (maybe_non_children_only_effect_or_nop_strong b) as [(Heq&Hfacts')|(Heq&->&imm'&Hreldec')].
    all: erewrite Heq in Haccp; clear Heq.
    2: { rewrite /rel_dec Htgitpar decide_True // in Hreldec'. eapply ParentChild_transitive. 2: exact HPCI. done. }
    eapply bind_Some in Haccp as (x&Hx&(y&Hy&[= <-])%bind_Some). simpl.
    assert (x = y) as -> by repeat (case_match; simplify_eq; try done). clear Hy.
    rewrite /rel_dec Htgitpar decide_True // in Hx. 2: { eapply ParentChild_transitive. 2: exact HPCI. done. }
    destruct acc.
    - simpl in Hxc. destruct WFactive as [WFactive|WFactive];
      [by repeat (case_match; simplify_eq; try done)|left|right].
      all: rewrite WFactive in Hx.
      all: rewrite /apply_access_perm_inner in Hx; congruence.
    - simpl in Hx. repeat (case_match; simplify_eq; try done); (try by left); by right. }
  destruct (decide (ParentChildIn tg_par tg tr)) as [HPCI2|HnPCI2].
  { edestruct (maybe_non_children_only_effect_or_nop_strong b) as [(Heq&Hfacts')|(Heq&->&imm'&Hreldec')].
    all: erewrite Heq in Haccp; clear Heq. 2: rewrite /rel_dec Htgitpar decide_True // in Hreldec'.
    intros Hcldact.
    edestruct (maybe_non_children_only_effect_or_nop_strong b) as [(Heq&Hfacts)|(Heq&->&imm&Hreldec)].
    all: erewrite Heq in Haccc; clear Heq.
    { eapply bind_Some in Haccc as (xc&Hxc&(yc&Hyc&[= <-])%bind_Some). simpl in Hcldact. subst yc.
      assert (xc = Active) as -> by repeat (case_match; simplify_eq; try done).
      rewrite /rel_dec Htgitcld decide_False // in Hxc.
      rewrite /apply_access_perm_inner in Hxc. repeat (case_match; simplify_eq; try done). }
    injection Haccc as <-. specialize (WFactive Hcldact).
    eapply bind_Some in Haccp as (x&Hx&(y&Hy&[= <-])%bind_Some). simpl.
    assert (x = y) as -> by repeat (case_match; simplify_eq; try done). clear Hy.
    destruct WFactive as [WFactive|WFactive]; [left|right].
    all: rewrite WFactive in Hx; rewrite /rel_dec Htgitpar decide_True // in Hx.
    all: destruct acc; cbv in Hx; congruence. }
  edestruct (maybe_non_children_only_effect_or_nop_strong b) as [(Heq&Hfacts')|(Heq&->&imm'&Hreldec')].
  all: erewrite Heq in Haccp; clear Heq.
  { edestruct (maybe_non_children_only_effect_or_nop_strong b) as [(Heq&Hfacts)|(Heq&->&imm&Hreldec)].
    all: erewrite Heq in Haccc; clear Heq.
    2: { exfalso. rewrite Htgitcld /rel_dec decide_False // in Hreldec.
         rewrite Htgitpar /rel_dec decide_False // in Hfacts'.
         destruct (decide (ParentChildIn tg tgcld tr)) as [HPCI3|HnPCI3]; last done.
          destruct Hfacts' as [?|Hfacts']; first done.
         destruct (decide (ParentChildIn tg tg_par tr)) as [HPCI4|HnPCI4]. 1: by eapply Hfacts'.
         eapply cousins_have_disjoint_children. 5: exact HPCI3. 5: exact HPCpc.
         1-3: done. rewrite /rel_dec !decide_False //. }
    rewrite Htgitcld /rel_dec decide_False // in Haccc. intros Hcldact.
    eapply bind_Some in Haccc as (xc&Hxc&(yc&Hyc&[= <-])%bind_Some). simpl in Hcldact. subst yc.
    assert (xc = Active) as -> by repeat (case_match; simplify_eq; try done).
    rewrite /apply_access_perm_inner in Hxc. repeat (case_match; simplify_eq; try done). }
  { injection Haccp as <-. intros Hcldact. eapply WFactive.
    rewrite Htgitcld /rel_dec decide_False // decide_True in Haccc.
    { simpl in Haccc. injection Haccc as <-. done. }
    rewrite Htgitpar /rel_dec decide_False // in Hreldec'.
    destruct (decide (ParentChildIn tg tg_par tr)); last done.
    eapply ParentChild_transitive. 2: apply HPCpc. done. }
Qed.


Lemma memory_access_compat_parents_not_disabled b tr tr' acc cids tg range :
  wf_tree tr →
  tree_contains tg tr →
  parents_more_init tr' ->
  protected_parents_not_disabled cids tr ->
  memory_access_maybe_nonchildren_only b acc cids tg range tr = Some tr' ->
  protected_parents_not_disabled cids tr'.
Proof.
  intros WFunq Hcont WFinit WFpnd Dealloc.
  assert (tree_unique tg tr) as Hunq by by eapply WFunq.
  intros tg_par l.
  destruct (decide (tree_contains tg_par tr)) as [Hunqpar%WFunq|Hninpar].
  2: { eapply every_child_not_in, count_0_not_exists. erewrite <-memory_access_tag_count; last done.
       by eapply count_0_not_exists. }
  assert (wf_tree tr') as Hwfunq'.
  { eapply preserve_tag_count_wf. 1: eapply memory_access_tag_count. all: done. }
  assert (tree_unique tg_par tr') as Hunqpar'.
  { rewrite /tree_unique. by erewrite <- memory_access_tag_count. }
  setoid_rewrite every_child_ParentChildIn; [|try done..].
  intros itpar' Hitpar' tgcld Hunqcld' HPCpc'.
  epose proof Hunqcld' as (itcld'&Hitcld')%unique_lookup.
  eapply every_node_eqv_universal.
  intros nitcld' Hn Hn2.
  assert (nitcld' = itcld') as ->.
  { eapply every_node_eqv_universal in Hitcld'. 1: apply Hitcld'. all: done. }
  clear Hn2 Hn.
  assert (tree_unique tgcld tr) as Hunqcld.
  { rewrite /tree_unique. by erewrite memory_access_tag_count. }
  epose proof Hunqcld as (itcld&Hitcld)%unique_lookup.
  epose proof Hunqpar as (itpar&Hitpar)%unique_lookup.
  epose proof Dealloc as Hspecpar. eapply apply_access_spec_per_node in Hspecpar.
  3: exact Hitpar. 2: by eapply unique_exists.
  destruct Hspecpar as (itpar'2 & Hpostpar & Hcont2 & Hdet2).
  assert (itpar'2 = itpar') as ->.
  { eapply tree_determined_unify; done. } clear Hcont2 Hdet2.
  epose proof Dealloc as Hspeccld. eapply apply_access_spec_per_node in Hspeccld.
  3: exact Hitcld. 2: by eapply unique_exists.
  destruct Hspeccld as (itcld'2 & Hpostcld & Hcont2 & Hdet2).
  assert (itcld'2 = itcld') as ->.
  { eapply tree_determined_unify; done. } clear Hcont2 Hdet2.
  specialize (WFinit tg_par). setoid_rewrite every_child_ParentChildIn in WFinit.
  2: done. 2: done.
  specialize (WFpnd tg_par). setoid_rewrite every_child_ParentChildIn in WFpnd.
  2: done. 2: done. 
  ospecialize (WFinit _ Hitpar' tgcld _ _). 1: done. 1: done.
  ospecialize (WFpnd l _ Hitpar tgcld _ _). 1: done. 1: by setoid_rewrite access_eqv_rel.
  epose proof HPCpc' as HPCpc. setoid_rewrite <- access_eqv_rel in HPCpc; try done.
  eapply every_node_eqv_universal in WFinit.
  2: { eapply exists_determined_exists. 2: exact Hitcld'. 1: by eapply unique_exists. }
  eapply every_node_eqv_universal in WFpnd.
  2: { eapply exists_determined_exists. 2: exact Hitcld. 1: by eapply unique_exists. }
  ospecialize (WFinit _).
  { eapply tree_determined_specifies_tag; last done. by eapply unique_exists. }
  ospecialize (WFpnd _).
  { eapply tree_determined_specifies_tag; last done. by eapply unique_exists. }
  symmetry in Hpostpar. symmetry in Hpostcld.
  eapply bind_Some in Hpostpar as (pp&Hpostpar&[= <-]).
  eapply bind_Some in Hpostcld as (pc&Hpostcld&[= <-]).
  specialize (WFinit l).
  eapply (mem_apply_range'_spec _ _ l) in Hpostpar.
  eapply (mem_apply_range'_spec _ _ l) in Hpostcld.
  rewrite /item_protected_all_parents_not_disabled /=.
  destruct decide as [Hrange|Hnrange]; last first.
  { rewrite /item_lookup /= Hpostpar Hpostcld. apply WFpnd. }
  destruct Hpostpar as (ppnew&Hppnew&Haccp).
  destruct Hpostcld as (pcnew&Hpcnew&Haccc).
  rewrite /item_lookup /= Hppnew Hpcnew /=.
  rewrite /item_lookup /= Hppnew Hpcnew /= in WFinit.
  rewrite /item_lookup /= in WFpnd.
  assert (itag itcld = tgcld) as Htgitcld.
  { eapply tree_determined_specifies_tag. 2: done. by eapply unique_exists. } 
  assert (itag itpar = tg_par) as Htgitpar.
  { eapply tree_determined_specifies_tag. 2: done. by eapply unique_exists. }

  intros Hisinit Hisprot.
  destruct (decide (ParentChildIn tg_par tg tr)) as [HPCI|HnPCI].
  { edestruct (maybe_non_children_only_effect_or_nop_strong b) as [(Heq&Hfacts)|(Heq&->&imm&Hreldec)].
    all: erewrite Heq in Haccp; clear Heq. 2: rewrite Htgitpar /rel_dec decide_True // in Hreldec.
    rewrite Htgitpar /rel_dec decide_True // in Haccp.
    eapply bind_Some in Haccp as (x&Hx&(y&Hy&[= <-])%bind_Some); simpl. left.
    intros ->. assert (x = Disabled) as -> by repeat (case_match; simplify_eq; try done).
    clear Hy. rewrite /apply_access_perm_inner in Hx.
    repeat (case_match; simplify_eq; try done). }
  edestruct (maybe_non_children_only_effect_or_nop_strong b) as [(Heq&Hfacts)|(Heq&->&imm&Hreldec)]; last first.
  all: erewrite Heq in Haccp; clear Heq.
  { rewrite Htgitpar /rel_dec decide_False // in Hreldec.
    destruct (decide (ParentChildIn tg tg_par tr)) as [HPCI2|HnPCI2]; try done.
    rewrite Htgitcld /rel_dec decide_False in Haccc.
    2: { intros H. eapply HnPCI. do 2 (eapply ParentChild_transitive; first eassumption). by left. }
    rewrite decide_True in Haccc. 2: by eapply ParentChild_transitive.
    simpl in Haccc. injection Haccc as <-. injection Haccp as <-. by eapply WFpnd. }
  { eapply bind_Some in Haccp as (x&Hx&(y&Hy&[= <-])%bind_Some); simpl.
    simpl in WFinit. specialize (WFinit Hisinit). rewrite WFinit in Hy.
    rewrite Htgitpar /rel_dec decide_False // /= most_init_comm /= in WFinit.
    edestruct (maybe_non_children_only_effect_or_nop_strong b) as [(Heq'&Hfacts')|(Heq'&->&imm'&Hreldec')].
    all: erewrite Heq' in Haccc; clear Heq'.
    2: { exfalso. destruct Hfacts as [?|Hfacts]; first done.
         rewrite Htgitpar /rel_dec decide_False // in Hfacts.
         destruct (decide (ParentChildIn tg tg_par tr)) as [?|HnPCI2].
         1: by eapply Hfacts.
         rewrite Htgitcld /rel_dec in Hreldec'.
         destruct (decide (ParentChildIn tgcld tg tr)) as [?|HnPCI3]. 1: done.
         destruct (decide (ParentChildIn tg tgcld tr)) as [HPCI4|?]. 2: done. clear Hreldec'.
         eapply cousins_have_disjoint_children. 5: eapply HPCpc. 5: eapply HPCI4.
         1-3: done. rewrite /rel_dec decide_False // decide_False //. }
    rewrite Htgitpar /rel_dec decide_False // /apply_access_perm_inner /= in Hx.
    eapply bind_Some in Haccc as (xc&Hxc&(yc&Hyc&[= <-])%bind_Some). simpl in Hisinit.
    rewrite Htgitcld /rel_dec most_init_comm /= decide_False /= in Hisinit.
    2: { intros H. eapply HnPCI. do 2 (eapply ParentChild_transitive; first eassumption). by left. }
    simpl. destruct acc.
    { destruct (perm (default {| initialized := PermLazy; perm := initp itpar |} (iperm itpar !! l))) as [|[]| | | |] eqn:HHH,
               (bool_decide (protector_is_active (iprot itpar) cids)); rewrite HHH in Hx; rewrite /= in Hx Hy; try (left; by simplify_eq).
      odestruct (WFpnd _ _) as [Hc|Hc]; [done|done|done|].
      rewrite /item_lookup in Hc. rewrite Hc /= in Hxc.
      right. clear -Hxc Hyc. repeat case_match; congruence. }
    destruct (decide (perm (item_lookup itcld l) = Cell)) as [Heq|Hne].
    { right. rewrite /item_lookup in Heq. rewrite Heq /= in Hxc.
      clear -Hxc Hyc. repeat case_match; congruence. }
    odestruct (WFpnd _ _) as [Hc|Hc]; [done|done| |done].
    left. intros ->.
    destruct (bool_decide (protector_is_active (iprot itpar) cids)) eqn:Hprotpar.
    1: by destruct x.
    injection Hy as ->.
    rewrite Hisinit in Hyc. rewrite bool_decide_true // in Hyc Hxc.
    rewrite Htgitcld /rel_dec decide_False /= in Hxc.
    2: { intros H. eapply HnPCI. do 2 (eapply ParentChild_transitive; first eassumption). by left. }
    repeat (case_match; simplify_eq; try done). }
Qed.


Lemma memory_access_compat_no_active_cousins b tr tr' acc cids tg range :
  wf_tree tr →
  tree_contains tg tr →
  no_active_cousins cids tr →
  memory_access_maybe_nonchildren_only b acc cids tg range tr = Some tr' →
  no_active_cousins cids tr'.
Proof.
  intros WFunq Hcont WFcs Haccess.
  intros tg1 it1' tg2 it2' off Hit1' Hit2' Hreldec Ha1 Ha2.
  erewrite <- access_same_rel_dec in Hreldec. 2: exact Haccess.
  assert (wf_tree tr') as Hwfunq'.
  { eapply preserve_tag_count_wf. 1: eapply memory_access_tag_count. all: done. }
  assert (tree_unique tg1 tr) as (it1&Hit1)%unique_implies_lookup.
  { rewrite /tree_unique. erewrite memory_access_tag_count. 2: done. eapply Hwfunq'. apply Hit1'.  }
  assert (tree_unique tg2 tr) as (it2&Hit2)%unique_implies_lookup.
  { rewrite /tree_unique. erewrite memory_access_tag_count. 2: done. eapply Hwfunq'. apply Hit2'.  }
  eapply apply_access_spec_per_node in Haccess as Hacc1.
  2-3: apply Hit1.
  destruct Hacc1 as (it1''&Hit1acc&Hit1'').
  assert (it1'' = it1') by by eapply tree_lookup_unique. subst it1''. clear Hit1''.
  eapply apply_access_spec_per_node in Haccess as Hacc2.
  2-3: apply Hit2.
  destruct Hacc2 as (it2''&Hit2acc&Hit2'').
  assert (it2'' = it2') by by eapply tree_lookup_unique. subst it2''. clear Hit2''.
  symmetry in Hit1acc, Hit2acc.
  eapply bind_Some in Hit1acc as (pp1&Hpp1&[= <-]).
  eapply bind_Some in Hit2acc as (pp2&Hpp2&[= <-]).
  eapply (mem_apply_range'_spec _ _ off) in Hpp1.
  eapply (mem_apply_range'_spec _ _ off) in Hpp2.
  destruct (decide (range'_contains range off)) as [Hin|Hout].
  2: { eapply WFcs. 1: apply Hit1. 1: apply Hit2. 1: done.
       - rewrite /active_or_prot_init /item_lookup /= ?Hpp1 // in Ha1|-*.
       - rewrite -Ha2 /item_lookup /= Hpp2 //. }
  destruct Hpp1 as (lp1'&Hoff1&Hlp1').
  destruct Hpp2 as (lp2'&Hoff2&Hlp2').
  rewrite /active_or_prot_init /item_lookup /= Hoff1 /= in Ha1.
  rewrite /item_lookup /= Hoff2 /= in Ha2.
  rewrite /rel_dec in Hlp1' Hlp2'.
  assert (itag it1 = tg1) as <- by by eapply tree_lookup_correct_tag.
  assert (itag it2 = tg2) as <- by by eapply tree_lookup_correct_tag.
  destruct (decide (ParentChildIn (itag it1) tg tr)) as [HPCA1|HnPCA1];
  destruct (decide (ParentChildIn (itag it2) tg tr)) as [HPCA2|HnPCA2].
  { exfalso. eapply cousins_have_disjoint_children. 4: exact Hreldec.
    4: exact HPCA1. 4: done. 1-3: eapply WFunq. 1: done. 1: eapply Hit1. 1: eapply Hit2. }
  { clear Hlp1'.
    rewrite decide_False in Hlp2'.
    2: { intros HPCI. apply rel_dec_flip in Hreldec. rewrite /rel_dec in Hreldec.
         rewrite decide_True in Hreldec. 1: discriminate Hreldec.
         eapply ParentChild_transitive. 1: exact HPCA1. 1: done. }
    rewrite maybe_non_children_only_no_effect in Hlp2'. 2: done.
    rewrite /apply_access_perm /apply_access_perm_inner /= in Hlp2'.
    repeat (case_match; simpl in *; simplify_eq; try done). }
  { rewrite decide_False in Hlp1'.
    2: { intros HPCI. rewrite /rel_dec in Hreldec.
         rewrite decide_True in Hreldec. 1: discriminate Hreldec.
         eapply ParentChild_transitive. 1: exact HPCA2. 1: done. }
    rewrite maybe_non_children_only_no_effect in Hlp1'. 2: done.
    rewrite /apply_access_perm /apply_access_perm_inner /= in Hlp1'.
    destruct Ha1 as [Ha1|(Hp1&Hi1)].
    1: repeat (case_match; simpl in *; simplify_eq; try done).
    destruct acc.
    2: { destruct Hp1 as [[? Hnc]|[|[]]].
         1: rewrite bool_decide_eq_true_2 // in Hlp1'.
         all: repeat (case_match; simpl in *; simplify_eq; try done). }
    assert (perm (item_lookup it2 off) = Active) as Ha2old.
    { clear Hlp1'. rewrite maybe_non_children_only_no_effect // /= /apply_access_perm /apply_access_perm_inner /= in Hlp2'.
      rewrite /item_lookup.
      destruct (default (mkPerm PermLazy (initp it2)) (iperm it2 !! off)) as [[] [|[]| | | |]] eqn:HH, bool_decide; rewrite HH /= in Hlp2'.
      all: try discriminate Hlp2'. all: injection Hlp2' as <-.
      all: try discriminate Ha2. all: done. }
    destruct (perm (default _ _)) as [|[]| | | |] eqn:Hperm, most_init eqn:Hinit; simpl in *; try by simplify_eq.
    { eapply bind_Some in Hlp1' as (px&Hpx1&[= <-]).
      destruct bool_decide in Hpx1; simpl in Hpx1, Hp1; simplify_eq; clear -Hp1.
      all: by destruct Hp1 as [[_ ?]|[[=]|[[=]|[=]]]]. }
    all: rewrite most_init_comm /= in Hinit.
    all: destruct (iperm it1 !! off) as [[[] prm]|] eqn:Hlu; rewrite Hlu /= // in Hinit.
    all: eapply WFcs; [exact Hit1|exact Hit2|exact Hreldec| |exact Ha2old].
    all: try (left; apply Hperm).
    all: try (right; split; last (by rewrite /item_lookup Hlu /= //)).
    all: destruct Hp1 as [[Hx Hnc]|Hp1]; first (left; split; [done|rewrite /item_lookup Hperm //]).
    all: right.
    all: destruct (bool_decide (protector_is_active (iprot it1) cids)); simpl in *.
    all: rewrite /item_lookup Hperm. all: try done; try by eauto.
    all: injection Hlp1' as <-.
    all: simpl in Hp1. all: clear -Hp1. all: by destruct_or!. }
  destruct (decide (ParentChildIn tg (itag it1) tr)) as [HPCB1|HnPCB1];
  first destruct (decide (ParentChildIn tg (itag it2) tr)) as [HPCB2|HnPCB2];
  first destruct b.
  { rewrite /maybe_non_children_only /= in Hlp1',Hlp2'.
    injection Hlp1' as <-. injection Hlp2' as <-.
    eapply WFcs. 3: exact Hreldec. 1-2: done.
    all: rewrite /item_lookup //. }
  { rewrite /maybe_non_children_only /= in Hlp1',Hlp2'.
    rewrite /apply_access_perm /apply_access_perm_inner /= in Hlp2'.
    repeat (case_match; simpl in *; simplify_eq; try done). }
  { clear Hlp1'.
    rewrite maybe_non_children_only_no_effect in Hlp2'. 2: done.
    rewrite /apply_access_perm /apply_access_perm_inner /= in Hlp2'.
    repeat (case_match; simpl in *; simplify_eq; try done). }
  { rewrite maybe_non_children_only_no_effect in Hlp1'. 2: done.
    rewrite /apply_access_perm /apply_access_perm_inner /= in Hlp1'.
    destruct Ha1 as [Ha1|(Hp1&Hi1)].
    1: repeat (case_match; simpl in *; simplify_eq; try done).
    destruct acc.
    2: { destruct Hp1 as [[Hprot Hcell]|[|[]]].
         2-4: repeat (case_match; simpl in *; simplify_eq; try done).
         rewrite bool_decide_eq_true_2 // in Hlp1'.
         repeat (case_match; simpl in *; simplify_eq; try done). }
    assert (perm (item_lookup it2 off) = Active) as Ha2old.
    { clear Hlp1'. edestruct maybe_non_children_only_effect_or_nop as [Heq|Heq]; erewrite Heq in Hlp2'.
      2: { injection Hlp2' as <-. rewrite /item_lookup Ha2 //. } clear Heq.
      rewrite /= /apply_access_perm /apply_access_perm_inner /= in Hlp2'.
      rewrite /item_lookup.
      destruct (default (mkPerm PermLazy (initp it2)) (iperm it2 !! off)) as [[] [|[]| | | |]] eqn:HH, bool_decide; rewrite HH /= in Hlp2'.
      all: try discriminate Hlp2'. all: injection Hlp2' as <-.
      all: try discriminate Ha2. }
    destruct (perm (default _ _)) as [|[]| | | |] eqn:Hperm, most_init eqn:Hinit; simpl in *; try by simplify_eq.
    { eapply bind_Some in Hlp1' as (px&Hpx1&[= <-]).
      destruct bool_decide in Hpx1; simpl in Hpx1, Hp1; simplify_eq; clear -Hp1.
      all: by destruct Hp1 as [[_ ?]|[[=]|[[=]|[=]]]]. }
    all: rewrite most_init_comm /= in Hinit.
    all: destruct (iperm it1 !! off) as [[[] prm]|] eqn:Hlu; rewrite Hlu /= // in Hinit.
    all: eapply WFcs; [exact Hit1|exact Hit2|exact Hreldec| |exact Ha2old].
    all: try (left; apply Hperm).
    all: try (right; split; last (by rewrite /item_lookup Hlu /= //)).
    all: destruct Hp1 as [[Hx Hnc]|Hp1]; first (left; split; [done|rewrite /item_lookup Hperm //]).
    all: right.
    all: destruct (bool_decide (protector_is_active (iprot it1) cids)); simpl in *.
    all: rewrite /item_lookup Hperm. all: try done; try by eauto.
    all: injection Hlp1' as <-.
    all: simpl in Hp1. all: clear -Hp1. all: by destruct_or!. }
Qed.

Lemma memory_deallocate_compat_parents_more_init tr tr' cids tg range :
  wf_tree tr →
  tree_contains tg tr →
  parents_more_init tr ->
  memory_deallocate cids tg range tr = Some tr' ->
  parents_more_init tr'.
Proof.
  intros H1 H2 H3 (x&Hx&Hy)%bind_Some.
  eapply join_map_id_is_Some_identical in Hy. subst x.
  by eapply memory_access_compat_parents_more_init.
Qed.

Lemma memory_deallocate_compat_parents_more_active tr tr' cids tg range :
  wf_tree tr →
  tree_contains tg tr →
  parents_more_active tr ->
  memory_deallocate cids tg range tr = Some tr' ->
  parents_more_active tr'.
Proof.
  intros H1 H2 H3 (x&Hx&Hy)%bind_Some.
  eapply join_map_id_is_Some_identical in Hy. subst x.
  by eapply memory_access_compat_parents_more_active.
Qed.

Lemma memory_deallocate_compat_protected_parents_not_disabled tr tr' cids tg range :
  wf_tree tr →
  tree_contains tg tr →
  protected_parents_not_disabled cids tr ->
  parents_more_init tr' ->
  memory_deallocate cids tg range tr = Some tr' ->
  protected_parents_not_disabled cids tr'.
Proof.
  intros H1 H2 H3 H4 (x&Hx&Hy)%bind_Some.
  eapply join_map_id_is_Some_identical in Hy. subst x.
  eapply memory_access_compat_parents_not_disabled; done.
Qed.

Lemma memory_deallocate_compat_no_active_cousins tr tr' cids tg range :
  wf_tree tr →
  tree_contains tg tr →
  no_active_cousins cids tr ->
  memory_deallocate cids tg range tr = Some tr' ->
  no_active_cousins cids tr'.
Proof.
  intros H1 H2 H3 (x&Hx&Hy)%bind_Some.
  eapply join_map_id_is_Some_identical in Hy. subst x.
  eapply memory_access_compat_no_active_cousins; done.
Qed.

Lemma free_mem_subset h blk n (sz:nat) :
  dom (free_mem (blk, n) sz h) ⊆ dom h.
Proof.
  revert n.
  induction sz; intros n; rewrite //=.
  rewrite /shift_loc //= dom_delete.
  set_solver.
Qed.

Lemma free_mem_only_only_one_block h l sz l2 :
  l.1 ≠ l2.1 →
  (free_mem l sz h) !! l2 = h !! l2.
Proof.
  intros H2.
  opose proof (free_mem_lookup _ _ _) as (_&H3).
  erewrite H3; first done.
  intros i Hi. destruct l, l2. rewrite /shift_loc /=. intros [= H4 H5]. by simpl in *.
Qed.

Lemma apply_within_trees_access_compat_parents_more_init b blk trs trs' acc cids tg range :
  wf_trees trs →
  trees_contain tg trs blk →
  each_tree_parents_more_init trs ->
  apply_within_trees (memory_access_maybe_nonchildren_only b acc cids tg range) blk trs = Some trs' ->
  each_tree_parents_more_init trs'.
Proof.
  intros (Hwf&_) Hcont H1 (tr1&Htr1&(tr1'&Htr1'&[= <-])%bind_Some)%bind_Some.
  intros blk' tr' [(<-&<-)|(Hne&Hin)]%lookup_insert_Some.
  2: by eapply H1.
  eapply memory_access_compat_parents_more_init.
  1: by eapply Hwf.
  2: by eapply H1. 2: done.
  by rewrite /trees_contain /trees_at_block Htr1 in Hcont.
Qed.

Lemma apply_within_trees_access_compat_parents_more_active b blk trs trs' acc cids tg range :
  wf_trees trs →
  trees_contain tg trs blk →
  each_tree_parents_more_active trs ->
  apply_within_trees (memory_access_maybe_nonchildren_only b acc cids tg range) blk trs = Some trs' ->
  each_tree_parents_more_active trs'.
Proof.
  intros (Hwf&_) Hcont H1 (tr1&Htr1&(tr1'&Htr1'&[= <-])%bind_Some)%bind_Some.
  intros blk' tr' [(<-&<-)|(Hne&Hin)]%lookup_insert_Some.
  2: by eapply H1.
  eapply memory_access_compat_parents_more_active.
  1: by eapply Hwf.
  2: by eapply H1. 2: done.
  by rewrite /trees_contain /trees_at_block Htr1 in Hcont.
Qed.

Lemma apply_within_trees_access_compat_protected_parents_not_disabled b blk trs trs' acc cids tg range :
  wf_trees trs →
  trees_contain tg trs blk →
  each_tree_parents_more_init trs' ->
  each_tree_protected_parents_not_disabled cids trs ->
  apply_within_trees (memory_access_maybe_nonchildren_only b acc cids tg range) blk trs = Some trs' ->
  each_tree_protected_parents_not_disabled cids trs'.
Proof.
  intros (Hwf&_) Hcont H1 H2 (tr1&Htr1&(tr1'&Htr1'&[= <-])%bind_Some)%bind_Some.
  intros blk' tr' [(<-&<-)|(Hne&Hin)]%lookup_insert_Some.
  2: by eapply H2. ospecialize (H1 blk tr1' _). 1: by rewrite lookup_insert_eq.
  eapply memory_access_compat_parents_not_disabled.
  1: by eapply Hwf.
  3: by eapply H2. 3: done. 2: done.
  by rewrite /trees_contain /trees_at_block Htr1 in Hcont.
Qed.

Lemma apply_within_trees_access_compat_no_active_cousins b blk trs trs' acc cids tg range :
  wf_trees trs →
  trees_contain tg trs blk →
  each_tree_no_active_cousins cids trs ->
  apply_within_trees (memory_access_maybe_nonchildren_only b acc cids tg range) blk trs = Some trs' ->
  each_tree_no_active_cousins cids trs'.
Proof.
  intros (Hwf&_) Hcont H2 (tr1&Htr1&(tr1'&Htr1'&[= <-])%bind_Some)%bind_Some.
  intros blk' tr' [(<-&<-)|(Hne&Hin)]%lookup_insert_Some.
  2: by eapply H2.
  eapply memory_access_compat_no_active_cousins.
  1: by eapply Hwf.
  3: done. 2: by eapply H2.
  by rewrite /trees_contain /trees_at_block Htr1 in Hcont.
Qed.

Lemma apply_within_trees_deallocate_compat_parents_more_init blk trs trs' cids tg range :
  wf_trees trs →
  trees_contain tg trs blk →
  each_tree_parents_more_init trs ->
  apply_within_trees (memory_deallocate cids tg range) blk trs = Some trs' ->
  each_tree_parents_more_init trs'.
Proof.
  intros (Hwf&_) Hcont H1 (tr1&Htr1&(tr1'&Htr1'&[= <-])%bind_Some)%bind_Some.
  intros blk' tr' [(<-&<-)|(Hne&Hin)]%lookup_insert_Some.
  2: by eapply H1.
  eapply memory_deallocate_compat_parents_more_init.
  1: by eapply Hwf.
  2: by eapply H1. 2: done.
  by rewrite /trees_contain /trees_at_block Htr1 in Hcont.
Qed.

Lemma apply_within_trees_deallocate_compat_parents_more_active blk trs trs' cids tg range :
  wf_trees trs →
  trees_contain tg trs blk →
  each_tree_parents_more_active trs ->
  apply_within_trees (memory_deallocate cids tg range) blk trs = Some trs' ->
  each_tree_parents_more_active trs'.
Proof.
  intros (Hwf&_) Hcont H1 (tr1&Htr1&(tr1'&Htr1'&[= <-])%bind_Some)%bind_Some.
  intros blk' tr' [(<-&<-)|(Hne&Hin)]%lookup_insert_Some.
  2: by eapply H1.
  eapply memory_deallocate_compat_parents_more_active.
  1: by eapply Hwf.
  2: by eapply H1. 2: done.
  by rewrite /trees_contain /trees_at_block Htr1 in Hcont.
Qed.

Lemma apply_within_trees_deallocate_compat_protected_parents_not_disabled blk trs trs' cids tg range :
  wf_trees trs →
  trees_contain tg trs blk →
  each_tree_parents_more_init trs' ->
  each_tree_protected_parents_not_disabled cids trs ->
  apply_within_trees (memory_deallocate cids tg range) blk trs = Some trs' ->
  each_tree_protected_parents_not_disabled cids trs'.
Proof.
  intros (Hwf&_) Hcont H1 H2 (tr1&Htr1&(tr1'&Htr1'&[= <-])%bind_Some)%bind_Some.
  intros blk' tr' [(<-&<-)|(Hne&Hin)]%lookup_insert_Some.
  2: by eapply H2. ospecialize (H1 blk tr1' _). 1: by rewrite lookup_insert_eq.
  eapply memory_deallocate_compat_protected_parents_not_disabled.
  1: by eapply Hwf.
  2: by eapply H2. 2: done. 2: done.
  by rewrite /trees_contain /trees_at_block Htr1 in Hcont.
Qed.

Lemma apply_within_trees_deallocate_compat_no_active_cousins blk trs trs' cids tg range :
  wf_trees trs →
  trees_contain tg trs blk →
  each_tree_no_active_cousins cids trs ->
  apply_within_trees (memory_deallocate cids tg range) blk trs = Some trs' ->
  each_tree_no_active_cousins cids trs'.
Proof.
  intros (Hwf&_) Hcont H1 (tr1&Htr1&(tr1'&Htr1'&[= <-])%bind_Some)%bind_Some.
  intros blk' tr' [(<-&<-)|(Hne&Hin)]%lookup_insert_Some.
  2: by eapply H1.
  eapply memory_deallocate_compat_no_active_cousins.
  1: by eapply Hwf.
  2: by eapply H1. 2: done.
  by rewrite /trees_contain /trees_at_block Htr1 in Hcont.
Qed.

Lemma root_node_IsParentChild it tr2 tg :
  let tr := branch it empty tr2 in
  wf_tree tr →
  tree_contains tg tr →
  ParentChildIn it.(itag) tg tr.
Proof.
  intros tr WF Hin.
  destruct Hin as [Hl|[[]|Hr]].
  1: by left.
  eapply exists_node_is_root_child.
  1: apply WF. done.
Qed.

Lemma memory_access_root_unaffected b k cids tg_acc off sz tr tr' blk hp :
  wf_tree tr →
  memory_access_maybe_nonchildren_only b k cids tg_acc (off, sz) tr = Some tr' →
  tree_contains tg_acc tr →
  tree_root_compatible tr blk hp →
  tree_root_compatible tr' blk hp.
Proof.
  intros Hwf Haccess Hcont.
  rewrite /tree_root_compatible.
  destruct tr as [|it tr1 tr2]; first done.
  intros (Hroot&->).
  rewrite /memory_access_maybe_nonchildren_only /tree_apply_access /= in Haccess.
  eapply bind_Some in Haccess as (it'&Hit'&(data&Hdata&[= <-])%bind_Some).
  split; last done.
  clear data Hdata.
  eapply bind_Some in Hit' as (p'&Hp'&[= <-]).
  destruct Hroot as (Hprot&(Hindis&Hroot)); split; first done.
  rewrite Hprot /= in Hp'.
  rewrite /rel_dec decide_True in Hp'.
  2: eapply root_node_IsParentChild; done.
  split; first by rewrite Hindis.
  intros offi. specialize (Hroot offi).
  eapply (mem_apply_range'_spec _ _ offi) in Hp'.
  destruct decide; last first.
  { rewrite /item_lookup /= in Hroot|-*.
    rewrite Hp'. apply Hroot. }
  destruct Hp' as (vn&H1&H2).
  odestruct maybe_non_children_only_effect_or_nop as [Heq|Heq];
    erewrite Heq in H2; clear Heq.
  2: { injection H2 as <-. rewrite H1. destruct (iperm it !! offi) eqn:Heq; rewrite !Heq /= ?Hindis; apply Hroot. }
  rewrite /apply_access_perm /= most_init_comm /= in H2.
  rewrite /apply_access_perm_inner /= in H2.
  rewrite /item_lookup in Hroot.
  destruct (default {| initialized := PermLazy; perm := initp it |} (iperm it !! offi)) as [ini prm] eqn:Heqd.
  rewrite Heqd in H2. simpl in Hroot, H2. 
  destruct k, (iperm it !! offi) as [[[][]]|]; simpl in *; try done; rewrite /= in H2; simplify_eq.
  all: try rewrite Hindis in H2.
  all: rewrite H1; cbv in H2; simplify_eq; done.
Qed.

Lemma memory_access_roots_unaffected b k cids tg_acc off sz trs trs' blk hp :
  wf_trees trs →
  apply_within_trees (memory_access_maybe_nonchildren_only b k cids tg_acc (off, sz)) blk trs = Some trs' →
  trees_contain tg_acc trs blk →
  tree_roots_compatible trs hp →
  tree_roots_compatible trs' hp.
Proof.
  intros (Hwf&_) (tr&Htr&(tr'&Htr'&[= <-])%bind_Some)%bind_Some Hcont Hcompat.
  rewrite /trees_contain /trees_at_block  Htr /= in Hcont.
  intros blkX trX [(<-&<-)|(Hne&Hin)]%lookup_insert_Some.
  - eapply memory_access_root_unaffected; try done. 1: by eapply Hwf. 1: by eapply Hcompat.
  - by eapply Hcompat.
Qed.

Lemma free_mem_remove_loc h blk n (sz:nat) m :
  (0 ≤ m < sz) ->
  dom (free_mem (blk, n) sz h) ## {[(blk, n + m)]}.
Proof.
  revert n m h.
  induction sz as [|? IHsz]; intros n m h [??].
  - lia.
  - rewrite //= dom_delete.
    destruct (decide (m = 0)).
    + subst. rewrite Z.add_0_r.
      set_solver.
    + eapply disjoint_difference_l2.
      rewrite /shift_loc //=.
      replace (n + m) with (n + 1 + (m - 1)) by lia.
      apply IHsz.
      lia.
Qed.

Lemma free_mem_delete h k1 k2 sz : free_mem k1 sz (delete k2 h) = delete k2 (free_mem k1 sz h).
Proof.
  induction sz as [|n IH] in h,k1|-*.
  - done.
  - rewrite /= delete_delete. f_equiv. apply IH.
Qed.

Lemma free_mem_block_dom (blk:block) n (sz:nat) h :
  (forall m : Z, is_Some (h !! (blk, n + m)) <-> 0 ≤ m < sz) ->
  set_map fst (dom (free_mem (blk, n) sz h)) = (set_map fst (dom h) ∖ {[blk]}:gset _).
Proof.
  intros Exact.
  induction sz as [|? IHsz] in n,h,Exact|-*.
  - rewrite difference_disjoint_L //.
    apply disjoint_singleton_r.
    intros ((blk' & l) & -> & Hin%elem_of_dom)%elem_of_map.
    specialize (Exact (l - n)).
    rewrite //= /shift_loc Zplus_minus in Exact.
    apply Exact in Hin. lia.
  - rewrite //= -free_mem_delete.
    rewrite IHsz.
    { rewrite dom_delete_L. apply gset_leibniz.
      intros k. split.
      - intros (((blk'&l) & -> & (Hin & Hnin2)%elem_of_difference)%elem_of_map & Hnin)%elem_of_difference.
        eapply elem_of_difference; split; last done.
        eapply elem_of_map. by eexists.
      - intros (((blk'&l) & -> & Hin)%elem_of_map & Hnin)%elem_of_difference.
        eapply elem_of_difference; split; last done.
        eapply elem_of_map. eexists; split; first done.
        eapply elem_of_difference. split; first done.
        intros [= -> ->]%elem_of_singleton. cbn in Hnin. set_solver. }
    intros m. destruct (Exact (1 + m)) as (HL & HR).
    rewrite //= /shift_loc //= in HL,HR,Exact|-*. split.
    + intros H. assert (m ≠ -1) as Hnneg.
      * intros ->. rewrite -Z.add_assoc Z.add_opp_diag_r Z.add_0_r lookup_delete_eq in H.
        by apply is_Some_None in H.
      * rewrite Z.add_assoc in HL.
        rewrite lookup_delete_ne in H; first by apply HL in H; lia.
        intros [= HH]; lia.
    + intros H. rewrite lookup_delete_ne; last (intros [= HH]; lia).
      rewrite -Z.add_assoc. apply HR. lia.
Qed.

(** Dealloc *)
Lemma dealloc_step_wf σ σ' e e' l bor ptr efs :
  mem_expr_step σ.(shp) e (DeallocEvt l bor ptr) σ'.(shp) e' efs →
  bor_step σ.(strs) σ.(scs) σ.(snp) σ.(snc)
           (DeallocEvt l bor ptr)
           σ'.(strs) σ'.(scs) σ'.(snp) σ'.(snc) →
  state_wf σ → state_wf σ'.
Proof.
  destruct σ as [h trs cids nxtp nxtc].
  destruct σ' as [h' trs' cids' nxtp' nxtc']. simpl.
  intros BS IS WF.
  inversion BS; clear BS; simplify_eq.
  inversion IS as [ | | | | | | |trs'' ???? ACC | | ]; clear IS; simplify_eq.
  destruct (trees_deallocate_isSome _ _ _ _ _ _ (mk_is_Some _ _ ACC)) as [x [Lookup Update]].
  assert (each_tree_parents_more_init trs'') as HH1.
  { eapply apply_within_trees_deallocate_compat_parents_more_init; try done.
    all: by eapply WF. }
  constructor; simpl.
  - rewrite /same_blocks dom_delete_L.
    rewrite free_mem_block_dom; [|auto].
    erewrite <- apply_within_trees_same_dom; [|eassumption].
    pose proof (WF.(state_wf_dom _)) as Same; simpl in Same.
    rewrite /same_blocks in Same.
    rewrite Same. done.
  - apply delete_trees_wf.
    eapply apply_within_trees_wf; first exact ACC.
    2: apply WF.
    eapply deallocate_preserve_tree_tag_count.
  - eapply delete_trees_parents_more_init. done.
  - eapply delete_trees_parents_more_active.
    eapply apply_within_trees_deallocate_compat_parents_more_active; try done.
    all: by eapply WF.
  - eapply delete_trees_parents_not_disabled.
    eapply apply_within_trees_deallocate_compat_protected_parents_not_disabled.
    5,3,2: done. all: by eapply WF.
  - eapply delete_trees_no_active_cousins.
    eapply apply_within_trees_deallocate_compat_no_active_cousins.
    2,4: done. all: by eapply WF.
  - apply delete_trees_compat_nexts.
    eapply apply_within_trees_compat; first exact ACC.
    3: eapply WF. 1: done. all: simpl.
    intros ??. eapply memory_deallocate_compat_nexts.
  - intros blk tr' (Hne&Hin)%lookup_delete_Some.
    eapply bind_Some in ACC as (tr1&_&(tr2&_&[= <-])%bind_Some).
    rewrite lookup_insert_ne // in Hin.
    specialize (state_wf_roots_active _ WF blk tr' Hin) as Hact. simpl in Hact.
    destruct tr' as [|it ??]; first done.
    rewrite /root_invariant /= in Hact|-*. destruct Hact as ((Hprot&Hinit&Hact)&->); split; last done.
    split; first done. split; first done.
    intros off. specialize (Hact off).
    rewrite !free_mem_only_only_one_block //.
  - apply (WF.(state_wf_cid_agree _)).
Qed.

Lemma access_step_wf_inner σ b acc tg blk off sz trs' :
  trees_contain tg (strs σ) blk →
  apply_within_trees (memory_access_maybe_nonchildren_only b acc σ.(scs) tg (off, sz)) blk σ.(strs) = Some trs' →
  state_wf σ → state_wf (mkState σ.(shp) trs' σ.(scs) σ.(snp) σ.(snc)).
Proof.
  intros CONTAINS ACC WF.
  constructor; simpl.
  - rewrite /same_blocks.
    pose proof (WF.(state_wf_dom _)) as Same; simpl in Same.
    rewrite /same_blocks in Same. rewrite <- Same.
    rewrite (apply_within_trees_same_dom _ _ _ _ ACC).
    set_solver.
  - (* wf *)
    eapply apply_within_trees_wf.
    * exact ACC.
    * eapply memory_access_tag_count.
    * apply WF.
  - eapply apply_within_trees_access_compat_parents_more_init; try done.
    all: by eapply WF.
  - eapply apply_within_trees_access_compat_parents_more_active; try done.
    all: by eapply WF.
  - eapply apply_within_trees_access_compat_protected_parents_not_disabled; try done.
    2: eapply apply_within_trees_access_compat_parents_more_init; try done.
    all: by eapply WF.
  - eapply apply_within_trees_access_compat_no_active_cousins; try done.
    all: by eapply WF.
  - eapply apply_within_trees_compat.
    * exact ACC.
    * done.
    * intros ??. eapply memory_access_compat_nexts.
    * apply WF.
  - eapply memory_access_roots_unaffected. 2: done. 2: done. 1-2: eapply WF.
  - (* cids *) apply (WF.(state_wf_cid_agree _)).
Qed.

Lemma read_step_wf σ σ' e e' l bor ptr vl efs :
  mem_expr_step σ.(shp) e (CopyEvt l bor ptr vl) σ'.(shp) e' efs →
  bor_step σ.(strs) σ.(scs) σ.(snp) σ.(snc)
           (CopyEvt l bor ptr vl)
           σ'.(strs) σ'.(scs) σ'.(snp) σ'.(snc) →
  state_wf σ → state_wf σ'.
Proof.
  destruct σ' as [h' trs' cids' nxtp' nxtc']. simpl.
  intros BS IS WF.
  inversion BS; clear BS; simplify_eq.
  inversion IS as [ |?????? ACC| | | | | | | | ]; clear IS; simplify_eq.
  - eapply (access_step_wf_inner σ false); done.
  - by destruct σ.
Qed.

(* TODO less equalities makes applying the rule easier, see _sane version below *)
Lemma write_mem_dom l (vl : value) h h'
  (DEFINED: ∀ i : nat, (i < length vl)%nat → (l +ₗ i) ∈ dom h)
  (SUCCESS: write_mem l vl h = h') :
  dom h' = dom h.
Proof.
  revert l h h' DEFINED SUCCESS. induction vl as [|sc vl IH]; intros l h h' DEFINED SUCCESS.
  - simpl in *. subst. reflexivity.
  - simpl in *. rewrite <- SUCCESS.
    erewrite IH; [| |reflexivity].
    + rewrite dom_insert_lookup_L; first done.
      pose proof (DEFINED 0%nat) as Overwrite.
      rewrite shift_loc_0 in Overwrite.
      apply elem_of_dom.
      apply Overwrite.
      lia.
    + intros i Length.
      rewrite dom_insert.
      apply elem_of_union_r.
      rewrite shift_loc_assoc.
      replace (l +ₗ (1 + i)) with (l +ₗ (1 + i)%nat) by (unfold shift_loc; simpl; f_equal; lia).
      apply DEFINED.
      lia.
Qed.
Lemma write_mem_dom_sane l (vl : value) h
  (DEFINED: ∀ i : nat, (i < length vl)%nat → (l +ₗ i) ∈ dom h) :
  dom (write_mem l vl h) = dom h.
Proof.
  by eapply write_mem_dom.
Qed.

(* These two are not needed for write_step_wf but for other parts of the development *)

Lemma write_mem_lookup l vl h :
  (∀ (i: nat), (i < length vl)%nat → write_mem l vl h !! (l +ₗ i) = vl !! i) ∧
  (∀ (l': loc), (∀ (i: nat), (i < length vl)%nat → l' ≠ l +ₗ i) →
    write_mem l vl h !! l' = h !! l').
Proof.
  revert l h. induction vl as [|v vl IH]; move => l h; simpl;
    [split; [intros ?; by lia|done]|].
  destruct (IH (l +ₗ 1) (<[l:=v]> h)) as [IH1 IH2]. split.
  - intros i Lt. destruct i as [|i].
    + rewrite shift_loc_0_nat /=. rewrite IH2; [by rewrite lookup_insert_eq|].
      move => ? _.
      rewrite shift_loc_assoc -{1}(shift_loc_0 l) => /shift_loc_inj ?. by lia.
    + rewrite /= -IH1; [|lia].  by rewrite shift_loc_assoc -(Nat2Z.inj_add 1).
  - intros l' Lt. rewrite IH2.
    + rewrite lookup_insert_ne; [done|].
      move => ?. subst l'. apply (Lt O); [lia|by rewrite shift_loc_0_nat].
    + move => i Lti. rewrite shift_loc_assoc -(Nat2Z.inj_add 1).
      apply Lt. by lia.
Qed.

Lemma write_mem_lookup_outside l vl h l' :
  ¬ (l'.1 = l.1 ∧ (l.2 ≤ l'.2 < l.2 + length vl)%Z) →
  write_mem l vl h !! l' = h !! l'.
Proof.
  destruct (write_mem_lookup l vl h) as (_&H).
  intros Hout. rewrite H //.
  intros i Hlt ->.
  apply Hout.
  split; first done.
  simpl. lia.
Qed.

Lemma write_mem_lookup_case l vl h l' :
  (∃ (i: nat), (i < length vl)%nat ∧ l' = l +ₗ i ∧ write_mem l vl h !! (l +ₗ i) = vl !! i)
  ∨ ((∀ (i: nat), (i < length vl)%nat → l' ≠ l +ₗ i) ∧ write_mem l vl h !! l' = h !! l').
Proof.
  destruct (write_mem_lookup l vl h) as [EQ1 EQ2].
  case (decide (l'.1 = l.1)) => [Eql|NEql];
    [case (decide (l.2 ≤ l'.2 < l.2 + length vl)) => [[Le Lt]|NIN]|].
  - have Eql2: l' = l +ₗ Z.of_nat (Z.to_nat (l'.2 - l.2)). {
      destruct l, l'. move : Eql Le => /= -> ?.
      rewrite /shift_loc /= Z2Nat.id; [|lia]. f_equal. lia. }
    have Lt1: (Z.to_nat (l'.2 - l.2) < length vl)%nat
      by rewrite -(Nat2Z.id (length _)) -Z2Nat.inj_lt; lia.
    specialize (EQ1 _ Lt1).
    rewrite -Eql2 in EQ1. left.
    exists (Z.to_nat (l'.2 - l.2)). repeat split; [done..|by rewrite -Eql2].
  - right.
    have ?: (∀ (i: nat), (i < length vl)%nat → l' ≠ l +ₗ i).
    { intros i Lt Eq3. apply NIN. rewrite Eq3 /=. lia. }
    split; [done|]. by apply EQ2.
  - right.
    have ?: (∀ (i: nat), (i < length vl)%nat → l' ≠ l +ₗ i).
    { intros i Lt Eq3. apply NEql. by rewrite Eq3. }
    split; [done|]. by apply EQ2.
Qed.

Lemma root_invariant_dom blk itm h1 h2 :
  dom h1 = dom h2 →
  root_invariant blk itm h1 ↔
  root_invariant blk itm h2.
Proof.
  unfold mem.
  intros H. rewrite /root_invariant.
  split; intros (H1&H3&H2); split. 1: done. 2: done.
  all: split; first done.
  all: intros z; specialize (H2 z) as H0; repeat case_match; try done.
  1,4: eapply elem_of_dom; eapply elem_of_dom in H0.
  5,6: eapply not_elem_of_dom; eapply not_elem_of_dom in H0. all: simpl.
  all: try by rewrite <- H. all: try by rewrite H.
  all: eapply not_elem_of_dom. all: eapply not_elem_of_dom in H0.
  all: congruence.
Qed.

Lemma tree_root_compatible_dom tr blk h1 h2 :
  dom h1 = dom h2 →
  tree_root_compatible tr blk h1 ↔
  tree_root_compatible tr blk h2.
Proof.
  destruct tr; first done.
  eintros H%root_invariant_dom.
  rewrite /tree_root_compatible.
  setoid_rewrite H. done.
Qed.

Lemma tree_roots_compatible_dom trs h1 h2 :
  dom h1 = dom h2 →
  tree_roots_compatible trs h1 ↔
  tree_roots_compatible trs h2.
Proof.
  intros H.
  split; intros Hc blk tr Htr; specialize (Hc blk tr Htr).
  all: setoid_rewrite tree_root_compatible_dom; first done; done.
Qed.

Lemma write_step_wf σ σ' e e' l bor ptr vl efs :
  mem_expr_step σ.(shp) e (WriteEvt l bor ptr vl) σ'.(shp) e' efs →
  bor_step σ.(strs) σ.(scs) σ.(snp) σ.(snc)
           (WriteEvt l bor ptr vl)
           σ'.(strs) σ'.(scs) σ'.(snp) σ'.(snc) →
  state_wf σ → state_wf σ'.
Proof.
  destruct σ as [h trs cids nxtp nxtc].
  destruct σ' as [h' trs' cids' nxtp' nxtc']. simpl.
  intros BS IS WF.
  inversion BS; clear BS; simplify_eq.
  inversion IS as [ | | |?????? ACC |???? RANGE_SIZE| | | | | ]; clear IS; simplify_eq.
  2: { simpl in RANGE_SIZE. destruct vl; last done. simpl. done. }
  constructor; simpl.
  - rewrite /same_blocks.
    pose proof (WF.(state_wf_dom _)) as Same; simpl in Same.
    rewrite /same_blocks in Same.
    erewrite write_mem_dom; [|eassumption|reflexivity].
    rewrite <- Same.
    rewrite (apply_within_trees_same_dom trs _ _ _ ACC).
    set_solver.
  - (* wf *)
    eapply apply_within_trees_wf.
    * exact ACC.
    * eapply memory_access_tag_count.
    * apply WF.
  - eapply apply_within_trees_access_compat_parents_more_init; try done.
    all: by eapply WF.
  - eapply apply_within_trees_access_compat_parents_more_active; try done.
    all: by eapply WF.
  - eapply apply_within_trees_access_compat_protected_parents_not_disabled; try done.
    2: eapply apply_within_trees_access_compat_parents_more_init; try done.
    all: by eapply WF.
  - eapply apply_within_trees_access_compat_no_active_cousins; try done.
    all: by eapply WF.
  - eapply apply_within_trees_compat.
    * exact ACC.
    * done.
    * intros ??. eapply memory_access_compat_nexts.
    * apply WF.
  - eapply memory_access_roots_unaffected. 2: done. 2: done. 1: eapply WF.
    eapply tree_roots_compatible_dom; last eapply WF.
    simpl. eapply write_mem_dom_sane.
    done.
  - (* cids *) apply (WF.(state_wf_cid_agree _)).
Qed.

Lemma each_tree_protected_parents_not_disabled_grow trs cids cidsnew :
  wf_trees trs →
  (∀ blk tr, trs !! blk = Some tr → every_node (λ it, ¬ protector_is_active (iprot it) (cidsnew)) tr) →
  each_tree_protected_parents_not_disabled cids trs →
  each_tree_protected_parents_not_disabled (cidsnew ∪ cids) trs.
Proof.
  intros (Hwf&_) Hnew H1 blk tr Htr tg l.
  specialize (H1 blk tr Htr tg).
  specialize (Hnew blk tr Htr).
  specialize (Hwf _ _ Htr).
  destruct (decide (tree_contains tg tr)) as [Hin|Hnin].
  2: by eapply every_child_not_in.
  eapply every_child_ParentChildIn.
  1-2: by eapply Hwf.
  intros it_par Hitpar tg_cld Hunqcld HPCI.
  eapply every_child_ParentChildIn in H1.
  2-3: by eapply Hwf. 2-4: done.
  eapply every_node_eqv_universal. intros it_cld Hitcld Htgitcld.
  eapply every_node_eqv_universal in H1. 2: exact Hitcld.
  intros Hinit (c&Hcc1&[Hcc2|Hcc2]%elem_of_union).
  2: eapply H1; try done; by eexists.
  exfalso. eapply every_node_eqv_universal in Hnew. 2: exact Hitcld.
  eapply Hnew. by exists c.
Qed.

Lemma each_tree_no_active_cousins_grow trs cids cidsnew :
  wf_trees trs →
  (∀ blk tr, trs !! blk = Some tr → every_node (λ it, ¬ protector_is_active (iprot it) (cidsnew)) tr) →
  each_tree_no_active_cousins cids trs →
  each_tree_no_active_cousins (cidsnew ∪ cids) trs.
Proof.
  intros (Hwf&_) Hnew H1 blk tr Htr tg1 it1 tg2 it2 off Hit1 Hit2 Hcs Hpa Ha.
  eapply H1. 1: eassumption. 3,5: eassumption. 1: exact Hit1. 1: exact Hit2.
  destruct Hpa as [Hpa|(Hp&Hi)]; first by left.
  right. split; last done. destruct Hp as [Hp|Hx]. 2: by right. left.
  destruct Hp as [(c&Hc&HHc) Hnc]. split; last done. exists c. split; first done.
  eapply elem_of_union in HHc as [HHc|HHc]; last done.
  exfalso. specialize (Hnew _ _ Htr).
  eapply every_node_eqv_universal in Hnew. 2: eapply tree_lookup_to_exists_node, Hit1.
  apply Hnew. exists c. split; done.
Qed.

Lemma initcall_step_wf_inner σ :
  state_wf σ →
  state_wf (mkState σ.(shp) σ.(strs) ({[ σ.(snc) ]} ∪ σ.(scs)) σ.(snp) (S σ.(snc))).
Proof.
  intros WF.
  constructor; simpl; [try apply WF..|].
  - eapply each_tree_protected_parents_not_disabled_grow. 1,3: eapply WF.
    intros blk tr Htr. eapply every_node_eqv_universal. intros it Hit (?&Hprot&->%elem_of_singleton).
    opose proof (state_wf_tree_compat _ WF _ _ Htr) as H.
    eapply every_node_eqv_universal in H. 2: done. eapply item_cid_valid in Hprot; last done. lia.
  - eapply each_tree_no_active_cousins_grow. 1,3: eapply WF.
    intros blk tr Htr. eapply every_node_eqv_universal. intros it Hit (?&Hprot&->%elem_of_singleton).
    opose proof (state_wf_tree_compat _ WF _ _ Htr) as H.
    eapply every_node_eqv_universal in H. 2: done. eapply item_cid_valid in Hprot; last done. lia.
  - eapply trees_compat_nexts_mono; [| |apply WF]; auto.
  - intros c. rewrite elem_of_union.
    move => [|/(state_wf_cid_agree _ WF)]; [intros ->%elem_of_singleton_1; by left|by right].
Qed.

Lemma initcall_step_wf σ σ' e e' n efs :
  mem_expr_step σ.(shp) e (InitCallEvt n) σ'.(shp) e' efs →
  bor_step σ.(strs) σ.(scs) σ.(snp) σ.(snc)
           (InitCallEvt n)
           σ'.(strs) σ'.(scs) σ'.(snp) σ'.(snc) →
  state_wf σ → state_wf σ'.
Proof.
  destruct σ as [h trs cids nxtp nxtc].
  destruct σ' as [h' trs' cids' nxtp' nxtc']. simpl.
  intros BS IS WF.
  inversion BS. clear BS. simplify_eq.
  inversion IS. clear IS. simplify_eq.
  by eapply initcall_step_wf_inner in WF.
Qed.




Lemma tree_access_many_helper_2 C tg (L : gmap Z _) :
  preserve_tree_tag_count (λ tr, map_fold (λ l acc tr2, tr2 ≫= memory_access_nonchildren_only acc C tg (l, 1%nat)) (Some tr) L).
Proof.
  intros tr1 tr2 tg'.
  map_fold_weak_ind L as z a L Hne _ IH in tr2; simpl.
  1: intros [= ->]; done.
  intros (trm&H1&H2)%bind_Some.
  ospecialize (IH _ H1). rewrite IH. clear IH H1 tr1.
  by eapply memory_access_tag_count.
Qed.

Lemma tree_access_many_helper_1 C (E : list (tag * gmap Z _)) :
  preserve_tree_tag_count (λ tr, foldr (λ '(tg, L) tr, tr ≫= λ tr1, map_fold (λ l acc tr2, tr2 ≫= memory_access_nonchildren_only acc C tg (l, 1%nat)) (Some tr1) L) (Some tr) E).
Proof.
  intros tr1 tr2 tg.
  induction E as [|(tg'&L) E IH] in tr2|-*; simpl.
  1: intros [= ->]; done.
  intros (trm&H1&H2)%bind_Some.
  specialize (IH _ H1). rewrite IH. clear IH H1 tr1.
  by eapply tree_access_many_helper_2.
Qed.

Lemma tree_access_all_protected_initialized_tag_count C cid :
  preserve_tree_tag_count (tree_access_all_protected_initialized C cid).
Proof.
  intros tr tr' tg.
  rewrite /tree_access_all_protected_initialized /=.
  generalize (tree_get_all_protected_tags_initialized_locs cid tr).
  intros S. revert S tr'. rewrite /set_fold /=. clear cid.
  intros H tr'.
  eapply tree_access_many_helper_1.
Qed.

Lemma tree_access_many_root_compat_helper_2 C tg (L : gmap Z _) blk hp tr tr' :
  tree_contains tg tr → wf_tree tr →
  tree_root_compatible tr blk hp →
  map_fold (λ l acc tr2, tr2 ≫= memory_access_nonchildren_only acc C tg (l, 1%nat)) (Some tr) L = Some tr' →
  tree_root_compatible tr' blk hp.
Proof.
  intros Hcont Htr Hcompat.
  map_fold_weak_ind L as z acc L Hne _ IH in tr'; simpl.
  1: intros [= ->]; done.
  intros (trm&H1&H2)%bind_Some. simpl in IH.
  ospecialize (IH _ H1).
  eapply memory_access_root_unaffected. 2: done. 3: done.
  1: eapply preserve_tag_count_wf.
  4: eapply preserve_tag_count_contains.
  1,4: eapply tree_access_many_helper_2.
  2,4: exact H1. all: done.
Qed.

Lemma tree_access_many_root_compat_helper_1 C (E : list (tag * gmap Z _)) blk hp tr tr' :
  (∀ tg x, (tg, x) ∈ E → tree_contains tg tr) → wf_tree tr →
  tree_root_compatible tr blk hp →
  foldr (λ '(tg, L) tr, tr ≫= λ tr1, map_fold (λ l acc tr2, tr2 ≫= memory_access_nonchildren_only acc C tg (l, 1%nat)) (Some tr1) L) (Some tr) E = Some tr' →
  tree_root_compatible tr' blk hp.
Proof.
  induction E as [|(tg'&L) E IH] in tr,tr'|-*; simpl; intros Hcont Hwf Hcompat.
  1: intros [= ->]; done.
  intros (trm&H1&H2)%bind_Some.
  ospecialize (IH _ _ _ _ Hcompat H1). 2: done.
  { intros tg x H; eapply Hcont; by right. }
  eapply tree_access_many_root_compat_helper_2. 4: done. 3: done.
  2: eapply preserve_tag_count_wf.
  1: eapply preserve_tag_count_contains.
  1,4: eapply tree_access_many_helper_1.
  2,4: exact H1. 2: done.
  eapply Hcont. by left.
Qed.

Lemma tree_access_many_more_init_helper_2 C tg (L : gmap Z _) tr tr' :
  wf_tree tr →
  tree_contains tg tr →
  parents_more_init tr →
  map_fold (λ l acc tr2, tr2 ≫= memory_access_nonchildren_only acc C tg (l, 1%nat)) (Some tr) L = Some tr' →
  parents_more_init tr'.
Proof.
  intros Hwf Hcontains Hmore.
  map_fold_weak_ind L as z acc L Hne _ IH in tr'; simpl.
  1: intros [= ->]; done.
  intros (trm&H1&H2)%bind_Some.
  specialize (IH _ H1).
  eapply memory_access_compat_parents_more_init; last done; try done.
  - eapply preserve_tag_count_wf. 1: by eapply tree_access_many_helper_2. 1: done. 1: exact H1.
  - eapply count_gt0_exists. erewrite <- tree_access_many_helper_2; last exact H1.
    by eapply count_gt0_exists.
Qed.

Lemma tree_access_many_more_init_helper_1 C (E : list (tag * gmap Z _)) tr tr' :
  wf_tree tr →
  (∀ tg S, (tg, S) ∈ E → tree_contains tg tr) →
  parents_more_init tr →
  foldr (λ '(tg, L) tr, tr ≫= λ tr1, map_fold (λ l acc tr2, tr2 ≫= memory_access_nonchildren_only acc C tg (l, 1%nat)) (Some tr1) L) (Some tr) E = Some tr' →
  parents_more_init tr'.
Proof.
  intros Hwf Hcontains Hmore.
  induction E as [|(tg'&L) E IH] in Hcontains,tr'|-*; simpl.
  1: intros [= ->]; done.
  intros (trm&H1&H2)%bind_Some.
  ospecialize (IH _ _ H1).
  { intros ???; eapply Hcontains; by right. }
  eapply tree_access_many_more_init_helper_2; last done; try done.
  - eapply preserve_tag_count_wf. 1: by eapply tree_access_many_helper_1. 1: done. 1: exact H1.
  - eapply count_gt0_exists. erewrite <- tree_access_many_helper_1; last exact H1.
    eapply count_gt0_exists, Hcontains. by left.
Qed.

Lemma tree_access_many_more_active_helper_2 C tg (L : gmap Z _) tr tr' :
  wf_tree tr →
  tree_contains tg tr →
  parents_more_active tr →
  map_fold (λ l acc tr2, tr2 ≫= memory_access_nonchildren_only acc C tg (l, 1%nat)) (Some tr) L = Some tr' →
  parents_more_active tr'.
Proof.
  intros Hwf Hcontains Hmore.
  map_fold_weak_ind L as z acc L Hne _ IH in tr'; simpl.
  1: intros [= ->]; done.
  intros (trm&H1&H2)%bind_Some.
  specialize (IH _ H1).
  eapply memory_access_compat_parents_more_active; last done; try done.
  - eapply preserve_tag_count_wf. 1: by eapply tree_access_many_helper_2. 1: done. 1: exact H1.
  - eapply count_gt0_exists. erewrite <- tree_access_many_helper_2; last exact H1.
    by eapply count_gt0_exists.
Qed.

Lemma tree_access_many_more_active_helper_1 C (E : list (tag * gmap Z _)) tr tr' :
  wf_tree tr →
  (∀ tg S, (tg, S) ∈ E → tree_contains tg tr) →
  parents_more_active tr →
  foldr (λ '(tg, L) tr, tr ≫= λ tr1, map_fold (λ l acc tr2, tr2 ≫= memory_access_nonchildren_only acc C tg (l, 1%nat)) (Some tr1) L) (Some tr) E = Some tr' →
  parents_more_active tr'.
Proof.
  intros Hwf Hcontains Hmore.
  induction E as [|(tg'&L) E IH] in Hcontains,tr'|-*; simpl.
  1: intros [= ->]; done.
  intros (trm&H1&H2)%bind_Some.
  ospecialize (IH _ _ H1).
  { intros ???; eapply Hcontains; by right. }
  eapply tree_access_many_more_active_helper_2; last done; try done.
  - eapply preserve_tag_count_wf. 1: by eapply tree_access_many_helper_1. 1: done. 1: exact H1.
  - eapply count_gt0_exists. erewrite <- tree_access_many_helper_1; last exact H1.
    eapply count_gt0_exists, Hcontains. by left.
Qed.

Lemma tree_access_many_protected_not_disabled_helper_2 C tg (L : gmap Z _) tr tr' :
  wf_tree tr →
  tree_contains tg tr →
  parents_more_init tr →
  protected_parents_not_disabled C tr →
  map_fold (λ l acc tr2, tr2 ≫= memory_access_nonchildren_only acc C tg (l, 1%nat)) (Some tr) L = Some tr' →
  protected_parents_not_disabled C tr'.
Proof.
  intros Hwf Hcontains Hinit Hmore.
  map_fold_weak_ind L as z acc L Hne Hss IH in tr'; simpl.
  1: intros [= ->]; done.
  intros (trm&H1&H2)%bind_Some.
  specialize (IH _ H1).
  eapply memory_access_compat_parents_not_disabled; last done; try done.
  - eapply preserve_tag_count_wf. 1: by eapply tree_access_many_helper_2. 1: done. 1: exact H1.
  - eapply count_gt0_exists. erewrite <- tree_access_many_helper_2; last exact H1.
    by eapply count_gt0_exists.
  - eapply (tree_access_many_more_init_helper_2 C tg (<[ z := acc ]> L)). 1-3: done. rewrite Hss /= H1 /= H2 //.
Qed.

Lemma tree_access_many_protected_not_disabled_helper_1 C (E : list (tag * gmap Z _)) tr tr' :
  wf_tree tr →
  (∀ tg S, (tg, S) ∈ E → tree_contains tg tr) →
  parents_more_init tr →
  protected_parents_not_disabled C tr →
  foldr (λ '(tg, L) tr, tr ≫= λ tr1, map_fold (λ l acc tr2, tr2 ≫= memory_access_nonchildren_only acc C tg (l, 1%nat)) (Some tr1) L) (Some tr) E = Some tr' →
  protected_parents_not_disabled C tr'.
Proof.
  intros Hwf Hcontains Hinit Hmore.
  induction E as [|(tg'&L) E IH] in Hcontains,tr'|-*; simpl.
  1: intros [= ->]; done.
  intros (trm&H1&H2)%bind_Some.
  ospecialize (IH _ _ H1).
  { intros ???; eapply Hcontains; by right. }
  eapply tree_access_many_protected_not_disabled_helper_2; last done; try done.
  - eapply preserve_tag_count_wf. 1: by eapply tree_access_many_helper_1. 1: done. 1: exact H1.
  - eapply count_gt0_exists. erewrite <- tree_access_many_helper_1; last exact H1.
    eapply count_gt0_exists, Hcontains. by left.
  - eapply (tree_access_many_more_init_helper_1 C (E)). 1,3: done. 2: rewrite /= H1 //.
    intros ???; eapply Hcontains; by right.
Qed.

Lemma tree_access_many_no_cousins_helper_2 C tg (L : gmap Z _) tr tr' :
  wf_tree tr →
  tree_contains tg tr →
  no_active_cousins C tr →
  map_fold (λ l acc tr2, tr2 ≫= memory_access_nonchildren_only acc C tg (l, 1%nat)) (Some tr) L = Some tr' →
  no_active_cousins C tr'.
Proof.
  intros Hwf Hcontains Hmore.
  map_fold_weak_ind L as z acc L Hne _ IH in tr'; simpl.
  1: intros [= ->]; done.
  intros (trm&H1&H2)%bind_Some.
  specialize (IH _ H1).
  eapply memory_access_compat_no_active_cousins; last done; try done.
  - eapply preserve_tag_count_wf. 1: by eapply tree_access_many_helper_2. 1: done. 1: exact H1.
  - eapply count_gt0_exists. erewrite <- tree_access_many_helper_2; last exact H1.
    by eapply count_gt0_exists.
Qed.

Lemma tree_access_many_no_cousins_helper_1 C (E : list (tag * gmap Z _)) tr tr' :
  wf_tree tr →
  (∀ tg S, (tg, S) ∈ E → tree_contains tg tr) →
  no_active_cousins C tr →
  foldr (λ '(tg, L) tr, tr ≫= λ tr1, map_fold (λ l acc tr2, tr2 ≫= memory_access_nonchildren_only acc C tg (l, 1%nat)) (Some tr1) L) (Some tr) E = Some tr' →
  no_active_cousins C tr'.
Proof.
  intros Hwf Hcontains Hmore.
  induction E as [|(tg'&L) E IH] in Hcontains,tr'|-*; simpl.
  1: intros [= ->]; done.
  intros (trm&H1&H2)%bind_Some.
  ospecialize (IH _ _ H1).
  { intros ???; eapply Hcontains; by right. }
  eapply tree_access_many_no_cousins_helper_2; last done; try done.
  - eapply preserve_tag_count_wf. 1: by eapply tree_access_many_helper_1. 1: done. 1: exact H1.
  - eapply count_gt0_exists. erewrite <- tree_access_many_helper_1; last exact H1.
    eapply count_gt0_exists, Hcontains. by left.
Qed.

Lemma mem_enumerate_sat_elem_of {X Y} fn k (vv:Y) (m:gmap _ X) :
  mem_enumerate_sat fn m !! k = Some vv ↔
  ∃ v, m !! k = Some v ∧ fn v = Some vv.
Proof.
  rewrite /mem_enumerate_sat. revert k vv.
  eapply (map_fold_weak_ind (λ b m, ∀ k vv, b !! k = Some vv ↔ ∃ v, m !! k = Some v ∧ fn v = Some vv)); clear m.
  1: intros ?; rewrite lookup_empty; set_solver.
  intros k1 v1 m r Hk1 IH k.
  destruct (fn v1) as [y|] eqn:Hv1; split.
  - intros [(->&->)|(Hne&(vk&Hvk&Hfnvk)%IH)]%lookup_insert_Some.
    + exists v1; by rewrite lookup_insert_eq.
    + exists vk. rewrite lookup_insert_ne //.
  - intros (v&[(<-&<-)|(Hne&HIH)]%lookup_insert_Some&Hfnv).
    + rewrite lookup_insert_eq. congruence.
    + rewrite lookup_insert_ne //. eapply IH. by eexists.
  - intros (vk&Hvk&Hfnvk)%IH. exists vk. rewrite lookup_insert_ne //.
    intros ->; congruence.
  - intros (v&[(<-&<-)|(Hne&HIH)]%lookup_insert_Some&Hfnv); first congruence.
    apply IH. by eexists.
Qed.

Lemma mem_enumerate_initalized it :
  ∀ (z : Z) v, mem_enumerate_sat protector_end_action (iperm it) !! z = Some v ↔ (initialized (item_lookup it z) = PermInit ∧ perm (item_lookup it z) ≠ Cell ∧ (v = AccessWrite ↔ perm (item_lookup it z) = Active)).
Proof.
  intros z v. split.
  - intros (pp&Hpp&Hinit)%mem_enumerate_sat_elem_of.
    rewrite /item_lookup Hpp /=. unfold protector_end_action in Hinit.
    destruct (initialized pp); last done.
    split; first done.
    destruct (perm pp); try discriminate Hinit; injection Hinit as <-; subst.
    all: split; first done.
    all: split; done.
  - intros (Hinit&Hactive). eapply mem_enumerate_sat_elem_of.
    rewrite /item_lookup in Hinit,Hactive. destruct (iperm it !! z) as [[[] pp]|] eqn:Heq.
    all: simpl in Hinit. 2-3: done. simpl in Hactive.
    exists (mkPerm PermInit pp). rewrite Heq. split; first done. simpl.
    destruct pp, v; simpl in *; try done.
    all: destruct Hactive as [Hx (H1&H2)]; try done; by first [specialize (H1 eq_refl) | specialize (H2 eq_refl)].
Qed.

Lemma tree_all_protected_initialized_exists_node cid tr tg lst :
  (tg, lst) ∈ tree_get_all_protected_tags_initialized_locs cid tr ↔
  exists_node (λ it, it.(itag) = tg ∧ protector_is_for_call cid it.(iprot) ∧ 
    ∀ z v, lst !! z = Some v ↔ (initialized (item_lookup it z) = PermInit ∧ perm (item_lookup it z) ≠ Cell ∧ (v = AccessWrite ↔ perm (item_lookup it z) = Active))) tr.
Proof.
  induction tr as [|it tr1 IH1 tr2 IH2]; first done.
  simpl in *. split.
  - intros [[Hif|H]%elem_of_union|H]%elem_of_union.
    + destruct decide as [Heq|Hne].
      2: by eapply elem_of_empty in Hif.
      apply elem_of_singleton in Hif as [= -> ->]. left. split_and!.
      1: done. 1: rewrite /protector_is_for_call Heq; by destruct (iprot it) as [[]|].
      eapply mem_enumerate_initalized.
    + right. left. by apply IH1.
    + right. right. by apply IH2.
  - intros [(<-&Hprot&HH)|[H|H]].
    + do 2 (eapply elem_of_union; left).
      destruct (iprot it) as [[cid' ?]|]; simpl in *.
      all: rewrite /protector_is_for_call /= in Hprot. 2: done.
      rewrite Hprot decide_True //.
      eapply elem_of_singleton. f_equal. eapply map_eq_iff.
      intros z. destruct (lst !! z) as [vvv|] eqn:Hlst.
      * symmetry. eapply mem_enumerate_initalized. eapply HH. done.
      * edestruct (mem_enumerate_sat _ _ !! z) as [vvx|] eqn:Heq; last done.
        eapply mem_enumerate_initalized in Heq. eapply HH in Heq. congruence.
    + eapply elem_of_union. left. eapply elem_of_union. right. eapply IH1. done.
    + eapply elem_of_union. right. eapply IH2. done.
Qed.


Lemma tree_access_all_protected_initialized_more_init C cid tr tr' :
  wf_tree tr →
  parents_more_init tr →
  tree_access_all_protected_initialized C cid tr = Some tr' →
  parents_more_init tr'.
Proof.
  intros Hwf Hmi.
  rewrite /tree_access_all_protected_initialized /=.
  rewrite /set_fold /=. eapply tree_access_many_more_init_helper_1.
  1: done. 2: done.
  intros tg S H%elem_of_elements%tree_all_protected_initialized_exists_node.
  eapply exists_node_increasing; first exact H.
  eapply every_node_eqv_universal.
  intros n _ (?&_); done.
Qed.


Lemma tree_access_all_protected_initialized_more_active C cid tr tr' :
  wf_tree tr →
  parents_more_active tr →
  tree_access_all_protected_initialized C cid tr = Some tr' →
  parents_more_active tr'.
Proof.
  intros Hwf Hmi.
  rewrite /tree_access_all_protected_initialized /=.
  rewrite /set_fold /=. eapply tree_access_many_more_active_helper_1.
  1: done. 2: done.
  intros tg S H%elem_of_elements%tree_all_protected_initialized_exists_node.
  eapply exists_node_increasing; first exact H.
  eapply every_node_eqv_universal.
  intros n _ (?&_); done.
Qed.


Lemma tree_access_all_protected_initialized_protected_not_disabled C cid tr tr' :
  wf_tree tr →
  parents_more_init tr →
  protected_parents_not_disabled C tr →
  tree_access_all_protected_initialized C cid tr = Some tr' →
  protected_parents_not_disabled C tr'.
Proof.
  intros Hwf Hmi.
  rewrite /tree_access_all_protected_initialized /=.
  rewrite /set_fold /=. eapply tree_access_many_protected_not_disabled_helper_1.
  1: done. 2: done.
  intros tg S H%elem_of_elements%tree_all_protected_initialized_exists_node.
  eapply exists_node_increasing; first exact H.
  eapply every_node_eqv_universal.
  intros n _ (?&_); done.
Qed.


Lemma tree_access_all_protected_initialized_no_cousins C cid tr tr' :
  wf_tree tr →
  no_active_cousins C tr →
  tree_access_all_protected_initialized C cid tr = Some tr' →
  no_active_cousins C tr'.
Proof.
  intros Hwf Hmi.
  rewrite /tree_access_all_protected_initialized /=.
  rewrite /set_fold /=. eapply tree_access_many_no_cousins_helper_1.
  1: done. 2: done.
  intros tg S H%elem_of_elements%tree_all_protected_initialized_exists_node.
  eapply exists_node_increasing; first exact H.
  eapply every_node_eqv_universal.
  intros n _ (?&_); done.
Qed.


Lemma tree_access_all_protected_initialized_root_compat C cid tr tr' blk hp :
  wf_tree tr →
  tree_root_compatible tr blk hp →
  tree_access_all_protected_initialized C cid tr = Some tr' →
  tree_root_compatible tr' blk hp.
Proof.
  intros Hwf Hmi.
  rewrite /tree_access_all_protected_initialized /=.
  rewrite /set_fold /=. eapply tree_access_many_root_compat_helper_1.
  3: done. 2: done.
  intros tg S H%elem_of_elements%tree_all_protected_initialized_exists_node.
  eapply exists_node_increasing; first exact H.
  eapply every_node_eqv_universal.
  intros n _ (?&_); done.
Qed.


Lemma tree_access_many_compat_nexts_helper_2 C tg (L : gmap Z _) a b :
  preserve_tree_compat_nexts (λ tr, map_fold (λ l acc tr2, tr2 ≫= memory_access_nonchildren_only acc C tg (l, 1%nat)) (Some tr) L) a a b b.
Proof.
  intros tr tr' Hcompat.
  map_fold_weak_ind L as z acc L Hne _ IH in tr'; simpl.
  1: intros [= ->]; done.
  intros (trm&H1&H2)%bind_Some.
  eapply memory_access_compat_nexts. 2: done.
  eapply IH. done.
Qed.

Lemma tree_access_many_compat_nexts_helper_1 C (E : list (tag * gmap Z _)) a b :
  preserve_tree_compat_nexts (λ tr, foldr (λ '(tg, L) tr, tr ≫= λ tr1, map_fold (λ l acc tr2, tr2 ≫= memory_access_nonchildren_only acc C tg (l, 1%nat)) (Some tr1) L) (Some tr) E) a a b b.
Proof.
  intros tr tr' HH.
  induction E as [|(tg'&L) E IH] in tr'|-*; simpl.
  1: intros [= ->]; done.
  intros (trm&H1&H2)%bind_Some.
  eapply tree_access_many_compat_nexts_helper_2; last done.
  by eapply IH.
Qed.

Lemma tree_access_all_protected_initialized_compat_nexts C cid nxtp nxtc :
  preserve_tree_compat_nexts (tree_access_all_protected_initialized C cid) nxtp nxtp nxtc nxtc.
Proof.
  intros tr tr' Htrcompat.
  rewrite /tree_access_all_protected_initialized /=.
  eapply tree_access_many_compat_nexts_helper_1. done.
Qed.

Lemma trees_access_all_protected_initialized_pointwise_1 C trs cid trs' :
  trees_access_all_protected_initialized C cid trs = Some trs' → ∀ k,
  (∀ tr, trs !! k = Some tr → ∃ tr', trs' !! k = Some tr' ∧ tree_access_all_protected_initialized C cid tr = Some tr') ∧
  (trs !! k = None → trs' !! k = None).
Proof.
  rewrite /trees_access_all_protected_initialized.
  pose (λ k trs, trs ← trs; apply_within_trees (tree_access_all_protected_initialized C cid) k trs) as fn.
  pose (λ tr k, ∃ tr' : tree item, trs' !! k = Some tr' ∧ tree_access_all_protected_initialized C cid tr = Some tr') as Pk.
  fold fn. intros Hrai.
  remember (dom trs) as S eqn:HS.
  assert (S ⊆ dom trs) as Hsubset by set_solver.
  enough (∀ k, (k ∈ S → ∀ tr, trs !! k = Some tr → Pk tr k) ∧
               (k ∉ S → trs' !! k = trs !! k)) as Hindu.
  { intros k. destruct (Hindu k) as (Hi1&Hi2). split.
    - intros tr HH. apply Hi1. 1: rewrite HS; by eapply elem_of_dom_2. done.
    - intros HH. rewrite Hi2 // HS. by eapply not_elem_of_dom. }
  clear HS. revert trs' Pk Hsubset Hrai.
  refine (set_fold_ind_L (λ (rr : option trees) (S : gset block), ∀ trs', let Pk := _ in S ⊆ _ → rr = Some trs' → ∀ k, (k ∈ S → _) ∧ (k ∉  S → _)) fn (Some trs) _ _ S); clear S.
  { intros ? Pk _ [= ->] k. split; first set_solver. intros _. done. }
  intros kin S [trs1'|] Hnin HIH trs2' Pk (Hkindom%singleton_subseteq_l&Hdom)%union_subseteq Hfn; last done.
  ospecialize (HIH _ Hdom eq_refl).
  intros k. destruct (decide (k = kin)) as [<-|Hne].
  - split; last set_solver.
    destruct (HIH k) as (_&HIHk).
    specialize (HIHk Hnin).
    intros _ tr Htr.
    rewrite /fn /= /apply_within_trees /= HIHk Htr /= in Hfn.
    eapply bind_Some in Hfn as (tr'&Htr'&[= <-]).
    exists tr'. rewrite lookup_insert_eq //.
  - destruct (HIH k) as (HIH1&HIH2).
    destruct (HIH kin) as (_&HIHkin).
    specialize (HIHkin Hnin).
    rewrite /fn /= /apply_within_trees /= HIHkin in Hfn.
    pose proof Hfn as (trkin&H1&(trkin'&H2&[= <-])%bind_Some)%bind_Some.
    split.
    + intros [H%elem_of_singleton|HinS]%elem_of_union; first done.
      intros tr Htr. edestruct HIH1 as (tr'&Htr'&HP); [done..|].
      exists tr'. split; last done.
      rewrite lookup_insert_ne //.
    + intros (_&H)%not_elem_of_union. rewrite -HIH2 //.
      rewrite lookup_insert_ne //.
Qed.

Lemma trees_access_all_protected_initialized_pointwise_2 C trs cid :
  (∀ k tr, trs !! k = Some tr → ∃ tr', tree_access_all_protected_initialized C cid tr = Some tr') →
  ∃ trs', trees_access_all_protected_initialized C cid trs = Some trs'.
Proof.
  rewrite /trees_access_all_protected_initialized.
  pose (λ k trs, trs ← trs; apply_within_trees (tree_access_all_protected_initialized C cid) k trs) as fn.
  pose (λ k, ∀ tr, trs !! k = Some tr → ∃ tr' : tree item, tree_access_all_protected_initialized C cid tr = Some tr') as Pk.
  fold fn.
  remember (dom trs) as S eqn:HS.
  assert (S ⊆ dom trs) as Hsubset by set_solver.
  enough ((∀ k, k ∈ S → Pk k) → ∃ trs', set_fold fn (Some trs) S = Some trs' ∧ (∀ k, k ∉ S → trs' !! k = trs !! k)) as Hindu.
  { intros H. edestruct Hindu as (?&Hindu'&_); last (eexists; eapply Hindu'). intros k _ tr HH. by eapply H. }
  clear HS. revert Hsubset.
  refine (set_fold_ind_L (λ (rr : option trees) (S : gset block), S ⊆ _ → (∀ k, k ∈ S → Pk k) → ∃ trs', rr = Some trs' ∧ _) fn (Some trs) _ _ S); clear S.
  1: intros _ Heq; by eexists.
  intros kin S trso' Hnin HIH (Hkindom%singleton_subseteq_l&Hdom)%union_subseteq Hk.
  destruct HIH as (trs'&->&Htrs'). 1: done. 1: intros ??; eapply Hk; set_solver.
  eapply elem_of_dom in Hkindom as (tr&Htr). pose proof Htr as Htr'. rewrite -Htrs' // in Htr'.
  odestruct (Hk kin _ _ Htr) as (trr&Htrr). 1: set_solver.
  rewrite /fn /= /apply_within_trees Htr' /= Htrr /=. eexists; split; first done.
  intros k (Hn1%not_elem_of_singleton&Hn2)%not_elem_of_union.
  rewrite lookup_insert_ne //. by apply Htrs'.
Qed.

Lemma trees_access_all_protected_initialized_backwards C trs cid trs' :
  trees_access_all_protected_initialized C cid trs = Some trs' → 
  ∀ k tr', trs' !! k = Some tr' → ∃ tr, trs !! k = Some tr ∧ tree_access_all_protected_initialized C cid tr = Some tr'.
Proof.
  intros H k tr' Htr'.
  edestruct trees_access_all_protected_initialized_pointwise_1 as (H1&H2). 1: exact H.
  destruct (trs !! k) as [tr|] eqn:Htr.
  - exists tr; split; first done.
    destruct (H1 _ Htr) as (tr1&Htr1&HH).
    assert (tr1 = tr') as -> by congruence. done.
  - rewrite Htr' Htr in H2. by discriminate H2.
Qed.

Lemma trees_access_all_protected_initialized_same_dom C trs cid trs' :
  trees_access_all_protected_initialized C cid trs = Some trs' →
  dom trs = dom trs'.
Proof.
  intros H.
  eapply gset_leibniz. intros k.
  pose proof (trees_access_all_protected_initialized_pointwise_1 _ _ _ _ H k) as (HSome&HNone).
  split.
  - intros (tr&(tr'&Htr'&_)%HSome)%elem_of_dom.
    by eapply elem_of_dom_2.
  - intros (tr'&Htr')%elem_of_dom.
    destruct (trs !! k) as [tr|] eqn:Htr; first by eapply elem_of_dom_2.
    rewrite HNone in Htr'; done.
Qed.

Lemma trees_access_all_protected_initialized_contains C n trs trs' tg blk :
  trees_contain tg trs blk →
  trees_access_all_protected_initialized C n trs = Some trs' →
  trees_contain tg trs' blk.
Proof.
  intros Hcont Hread. rewrite /trees_contain /trees_at_block in Hcont|-*.
  destruct (trs !! blk) as [tr|] eqn:Htr. 2: done. 
  eapply trees_access_all_protected_initialized_pointwise_1 in Hread as Hread1.
  destruct Hread1 as (HH&_). specialize (HH _ Htr) as (tr' & HH1&HH2).
  rewrite HH1. eapply preserve_tag_count_contains.
  1: eapply tree_access_all_protected_initialized_tag_count.
  1: exact Hcont. 1: done.
Qed.

Lemma each_tree_protected_parents_not_disabled_shrink trs cids cidsnew :
  wf_trees trs →
  cidsnew ⊆ cids →
  each_tree_protected_parents_not_disabled cids trs →
  each_tree_protected_parents_not_disabled cidsnew trs.
Proof.
  intros (Hwf&_) Hnew H1 blk tr Htr tg l.
  specialize (H1 blk tr Htr tg).
  specialize (Hwf _ _ Htr).
  destruct (decide (tree_contains tg tr)) as [Hin|Hnin].
  2: by eapply every_child_not_in.
  eapply every_child_ParentChildIn.
  1-2: by eapply Hwf.
  intros it_par Hitpar tg_cld Hunqcld HPCI.
  eapply every_child_ParentChildIn in H1.
  2-3: by eapply Hwf. 2-4: done.
  eapply every_node_eqv_universal. intros it_cld Hitcld Htgitcld.
  eapply every_node_eqv_universal in H1. 2: exact Hitcld.
  intros Hinit (c&Hcc1&Hcc%Hnew).
  eapply H1; try done. by exists c.
Qed.

Lemma each_tree_no_active_cousins_shrink trs cids cidsnew :
  wf_trees trs →
  cidsnew ⊆ cids →
  each_tree_no_active_cousins cids trs →
  each_tree_no_active_cousins cidsnew trs.
Proof.
  intros (Hwf&_) Hnew H1 blk tr Htr tg1 it1 tg2 it2 off Hit1 Hit2 Hcs Hpa Ha.
  eapply H1. 1: exact Htr. 1: exact Hit1. 1: exact Hit2. 1: done. 2: done.
  destruct Hpa as [Hpa|(Hp&Hi)]; first by left.
  right; split; last done. destruct Hp as [Hp|Hx]; last by right. left.
  destruct Hp as [(c&Hc&HHc%Hnew) Hp2]; split; last done. by exists c.
Qed.

Lemma endcall_step_wf_inner trs' c σ :
  c ∈ σ.(scs) →
  trees_access_all_protected_initialized σ.(scs) c σ.(strs) = Some trs' →
  state_wf σ →
  state_wf (mkState σ.(shp) trs' (σ.(scs) ∖ {[c]}) σ.(snp) (σ.(snc))).
Proof.
  intros H1 H2 WF.
  assert (wf_trees trs') as WF'.
  { opose proof (trees_access_all_protected_initialized_pointwise_1 _ _ _ _ _) as Hrai; first done.
    pose proof (state_wf_tree_unq _ WF) as (Hunq&Hunq2). split.
    + eintros k tr' (tr&Htr&Hread)%trees_access_all_protected_initialized_backwards; last done.
      eapply preserve_tag_count_wf.
      1: by eapply tree_access_all_protected_initialized_tag_count.
      1: eapply Hunq, Htr.
      1: done.
    + eintros blk1 blk2 tr1 tr2 tg (tr1p&Htr1p&Hread1)%trees_access_all_protected_initialized_backwards (tr2p&Htr2p&Hread2)%trees_access_all_protected_initialized_backwards Hin1 Hin2.
      2-3: done.
      eapply Hunq2; try done.
      all: eapply preserve_tag_count_contains_2; [by eapply tree_access_all_protected_initialized_tag_count| |done]; done. }
  constructor; simpl; try apply WF.
  - erewrite <- trees_access_all_protected_initialized_same_dom; last done. apply WF.
  - done.
  - opose proof (trees_access_all_protected_initialized_pointwise_1 _ _ _ _ _) as Hrai; first done.
    pose proof (state_wf_tree_unq _ WF) as (Hunq&Hunq2).
    eintros k tr' (tr&Htr&Hread)%trees_access_all_protected_initialized_backwards; last done.
    eapply tree_access_all_protected_initialized_more_init.
    1: by eapply Hunq. 2: done.
    eapply WF. done.
  - opose proof (trees_access_all_protected_initialized_pointwise_1 _ _ _ _ _) as Hrai; first done.
    pose proof (state_wf_tree_unq _ WF) as (Hunq&Hunq2).
    eintros k tr' (tr&Htr&Hread)%trees_access_all_protected_initialized_backwards; last done.
    eapply tree_access_all_protected_initialized_more_active.
    1: by eapply Hunq. 2: done.
    eapply WF. done.
  - eapply each_tree_protected_parents_not_disabled_shrink.
    1: apply WF'. 1: eapply subseteq_difference_l; reflexivity.
    opose proof (trees_access_all_protected_initialized_pointwise_1 _ _ _ _ _) as Hrai; first done.
    pose proof (state_wf_tree_unq _ WF) as (Hunq&Hunq2).
    eintros k tr' (tr&Htr&Hread)%trees_access_all_protected_initialized_backwards; last done.
    eapply tree_access_all_protected_initialized_protected_not_disabled.
    1: by eapply Hunq. 1: by eapply WF. 2: done. by eapply WF.
  - eapply each_tree_no_active_cousins_shrink.
    1: apply WF'. 1: eapply subseteq_difference_l; reflexivity.
    opose proof (trees_access_all_protected_initialized_pointwise_1 _ _ _ _ _) as Hrai; first done.
    pose proof (state_wf_tree_unq _ WF) as (Hunq&Hunq2).
    eintros k tr' (tr&Htr&Hread)%trees_access_all_protected_initialized_backwards; last done.
    eapply tree_access_all_protected_initialized_no_cousins.
    1: by eapply Hunq. 2: done.
    eapply WF. done.
  - eintros blk tr' (tr&Htr&Hread)%trees_access_all_protected_initialized_backwards.
    2: done. eapply tree_access_all_protected_initialized_compat_nexts; last done.
    eapply WF. done.
  - eintros k tr' (tr&Htr&Hread)%trees_access_all_protected_initialized_backwards; last done.
    eapply tree_access_all_protected_initialized_root_compat.
    1,2: eapply WF, Htr.
    1: done.
  - intros c' IN. apply WF.
    apply elem_of_difference in IN. apply IN.
Qed.

(** EndCall *)
Lemma endcall_step_wf σ σ' e e' n efs :
  mem_expr_step σ.(shp) e (EndCallEvt n) σ'.(shp) e' efs →
  bor_step σ.(strs) σ.(scs) σ.(snp) σ.(snc)
           (EndCallEvt n)
           σ'.(strs) σ'.(scs) σ'.(snp) σ'.(snc) →
  state_wf σ → state_wf σ'.
Proof.
  destruct σ' as [h' trs' cids' nxtp' nxtc']. simpl.
  intros BS IS WF.
  inversion BS. clear BS. simplify_eq.
  inversion IS. clear IS. simplify_eq.
  eapply endcall_step_wf_inner. all: done.
Qed.

(** Retag *)
Lemma insert_child_notfound tr (it:item) P Pdec :
  (every_node (λ x, ~P x) tr) →
  @insert_child_at _ tr it P Pdec = tr.
Proof.
  intros Hevery.
  induction tr as [|d tr1 IH1 tr2 IH2] in Hevery|-*; first done.
  simpl in Hevery|-*. destruct Hevery as (Hnd & Hn1 & Hn2).
  rewrite decide_False //.
  f_equal.
  - by eapply IH1.
  - by eapply IH2.
Qed.

Lemma insert_child_wf cids oldt nxtp pk im rk cid nxtc tro trn itnew
  (IT_WF : item_wf itnew (S nxtp) nxtc)
  : 
  create_new_item nxtp pk im rk cid = Some itnew →
  create_child cids oldt nxtp pk im rk cid tro = Some trn →
  tree_items_compat_nexts tro nxtp nxtc →
  wf_tree tro →
  tree_items_compat_nexts trn (S nxtp) nxtc ∧
  wf_tree trn.
Proof.
  intros Hnewchild CREATE Hcompat Hwf.
  pose proof CREATE as CREATE2.
  rewrite /create_child Hnewchild /= in CREATE.
  destruct (decide (tree_contains oldt tro)) as [Hin|Hnin]; last first.
  { rewrite /create_child insert_child_notfound in CREATE.
    - injection CREATE as ->. split; last done.
      eapply tree_items_compat_nexts_mono; last exact Hcompat. all:lia.
    - by eapply every_not_eqv_not_exists. }
  split; last first.
  - intros tg Hcont%count_gt0_exists.
    destruct (decide (tg = nxtp)) as [->|].
    + eapply create_child_determined in CREATE2 as H2; try done.
      * destruct H2 as (it&_&_&H2).
        rewrite /create_child in CREATE. injection CREATE as <-.
        eapply inserted_unique. 1: by eapply new_item_has_tag.
        -- intros H1. eapply tree_items_compat_next_not_containing; [exact H1|done|lia].
        -- by eapply (Hwf _ Hin).
      * intros ?. eapply tree_items_compat_next_not_containing. 1-2: done. lia.
    + erewrite <- create_child_preserves_count in Hcont; try done.
      eapply count_gt0_exists, Hwf in Hcont as Hunq.
      rewrite /tree_unique in Hunq.
      by erewrite create_child_preserves_count in Hunq.
  - injection CREATE as <-.
    eapply (insert_true_preserves_every tro).
    + apply IT_WF. 
    + eapply tree_items_compat_nexts_mono; last done; lia.
Qed.

Lemma insert_child_parents_more_init cids oldt nxtp pk im rk cid tro trn : 
  create_child cids oldt nxtp pk im rk cid tro = Some trn →
  parents_more_init tro →
  wf_tree tro →
  wf_tree trn →
  tree_contains oldt tro →
  ¬ tree_contains nxtp tro →
  parents_more_init trn.
Proof.
  intros H1 H2 Hwfo Hwfn H4 H5 tg.
  opose proof (insertion_contains _ _ _ _ _ _ _ _ _ H4 H1) as Hcontnew.
  opose proof (insertion_preserves_tags H4 H1) as H4new.
  destruct (decide (tg = nxtp)) as [->|Hne].
  { eapply every_child_ParentChildIn. 1-2: by eapply wf_tree_tree_unique.
    intros itp Hitdet tgcld Hunq HPC. eapply every_node_eqv_universal.
    intros itn Hitn Htg l. enough (itn = itp) by by subst.
    eapply every_node_eqv_universal in Hitdet. 1: eapply Hitdet. 2: done.
    rewrite Htg. destruct HPC as [?|HPC]; first by subst.
    exfalso. eapply insertion_order_nonstrictparent. 3: done. 3: done.
    2: done. 1: done. }
  destruct (decide (tree_contains tg trn)) as [Hin|Hnin].
  2: by eapply every_child_not_in.
  assert (tree_contains tg tro) as Hino.
  { eapply insertion_minimal_tags. 3: done. 2: done. 1: done. }
  eapply every_child_ParentChildIn.
  1-2: by eapply wf_tree_tree_unique.
  intros ittg Hittg tgcld Hitcld HPCI.
  destruct (decide (tgcld = nxtp)) as [<-|Hnotnew].
  - eapply every_node_eqv_universal. intros itcld Hitcld2 Htgcld.
    edestruct create_child_determined as (it&(?&_&[= <-])%bind_Some&_&Hdet). 3: done. 2: done. 1: done.
    eapply every_node_eqv_universal in Hdet. 2: exact Hitcld2.
    rewrite Hdet; last done. intros l.
    rewrite /item_lookup /= lookup_empty /=. done.
  - eapply every_node_eqv_universal. intros itcld Hitcld2 Htgcld.
    assert (tree_contains tgcld tro) as Hcldino.
    { eapply insertion_minimal_tags. 3: done. 2: by eapply unique_exists. 1: done. }
    specialize (H2 tg).
    destruct (unique_lookup tro tg) as (ittro&Hittro).
    1: by eapply Hwfo.
    assert (ParentChildIn tg tgcld tro) as HPCo.
    { destruct HPCI as [HPCI|HPCI]; first by left. right.
      eapply bind_Some in H1 as (x&Hx%new_item_has_tag&[= H1]). rewrite -H1 in HPCI.
      eapply insert_eqv_strict_rel in HPCI; first done.
      all: rewrite Hx //. }
    eapply every_child_ParentChildIn in H2.
    2-3: by eapply wf_tree_tree_unique. 2: exact Hittro. 3: apply HPCo.
    2: by eapply Hwfo.
    setoid_rewrite every_node_eqv_universal in H2.
    eapply Hwfo in Hcldino as Hcldunqo.
    eapply unique_lookup in Hcldunqo as Hlu. destruct Hlu as (itcldo&Hlucldo).
    assert (itcldo = itcld) as <-.
    { eapply create_child_preserves_determined in Hlucldo. 3: done. 2: done.
      eapply every_node_eqv_universal in Hlucldo. 1: symmetry; by eapply Hlucldo. 1: done. }
    assert (ittro = ittg) as <-.
    { eapply create_child_preserves_determined in Hittro. 3: exact H1. 2: done.
      eapply tree_determined_unify. 2: apply Hittro. 2: done. 1: done. }
    eapply H2. 2: done.
    eapply exists_node_eqv_existential in Hcldino as (n1&Hn1&HHn1).
    eapply every_node_eqv_universal in Hlucldo. 2: apply Hn1.
    rewrite -Hlucldo //.
Qed.

Lemma apply_within_trees_insert_child_parents_more_init blk cids oldt nxtp pk im rk cid trso trsn : 
  apply_within_trees (create_child cids oldt nxtp pk im rk cid) blk trso = Some trsn →
  each_tree_parents_more_init trso →
  wf_trees trso →
  wf_trees trsn →
  trees_contain oldt trso blk →
  ¬ trees_contain nxtp trso blk →
  each_tree_parents_more_init trsn.
Proof.
  intros (tro&Htro&(trn&Hacc&[= <-])%bind_Some)%bind_Some H2 H3 H3' H4 H5.
  rewrite /trees_contain /trees_at_block !Htro in H4,H5.
  intros blk' tr' [(<-&<-)|(Hne&HH)]%lookup_insert_Some.
  2: by eapply H2.
  eapply insert_child_parents_more_init; try done. 1: by eapply H2. 1: by eapply H3.
  destruct H3' as (H3'&_). eapply H3'. eapply lookup_insert_eq.
Qed.

Lemma insert_child_parents_more_active cids oldt nxtp pk im rk cid tro trn : 
  create_child cids oldt nxtp pk im rk cid tro = Some trn →
  parents_more_active tro →
  wf_tree tro →
  wf_tree trn →
  tree_contains oldt tro →
  ¬ tree_contains nxtp tro →
  parents_more_active trn.
Proof.
  intros H1 H2 Hwfo Hwfn H4 H5 tg.
  opose proof (insertion_contains _ _ _ _ _ _ _ _ _ H4 H1) as Hcontnew.
  opose proof (insertion_preserves_tags H4 H1) as H4new.
  destruct (decide (tg = nxtp)) as [->|Hne].
  { eapply every_child_ParentChildIn. 1-2: by eapply wf_tree_tree_unique.
    intros itp Hitdet tgcld Hunq HPC. eapply every_node_eqv_universal.
    intros itn Hitn Htg l. enough (itn = itp) by (left; by subst).
    eapply every_node_eqv_universal in Hitdet. 1: eapply Hitdet. 2: done.
    rewrite Htg. destruct HPC as [?|HPC]; first by subst.
    exfalso. eapply insertion_order_nonstrictparent. 3: done. 3: done.
    2: done. 1: done. }
  destruct (decide (tree_contains tg trn)) as [Hin|Hnin].
  2: by eapply every_child_not_in.
  assert (tree_contains tg tro) as Hino.
  { eapply insertion_minimal_tags. 3: done. 2: done. 1: done. }
  eapply every_child_ParentChildIn.
  1-2: by eapply wf_tree_tree_unique.
  intros ittg Hittg tgcld Hitcld HPCI.
  destruct (decide (tgcld = nxtp)) as [<-|Hnotnew].
  - eapply every_node_eqv_universal. intros itcld Hitcld2 Htgcld.
    edestruct create_child_determined as (it&(x&Hx&[= <-])%bind_Some&_&Hdet). 3: done. 2: done. 1: done.
    eapply every_node_eqv_universal in Hdet. 2: exact Hitcld2.
    rewrite Hdet; last done. intros l.
    rewrite /item_lookup /= lookup_empty /=.
    destruct pk, im, rk; simpl in Hx; try discriminate Hx; injection Hx as <-; done.
  - eapply every_node_eqv_universal. intros itcld Hitcld2 Htgcld.
    assert (tree_contains tgcld tro) as Hcldino.
    { eapply insertion_minimal_tags. 3: done. 2: by eapply unique_exists. 1: done. }
    specialize (H2 tg).
    destruct (unique_lookup tro tg) as (ittro&Hittro).
    1: by eapply Hwfo.
    assert (ParentChildIn tg tgcld tro) as HPCo.
    { destruct HPCI as [HPCI|HPCI]; first by left. right.
      eapply bind_Some in H1 as (x&Hx%new_item_has_tag&[= H1]). rewrite -H1 in HPCI.
      eapply insert_eqv_strict_rel in HPCI; first done.
      all: rewrite Hx //. }
    eapply every_child_ParentChildIn in H2.
    2-3: by eapply wf_tree_tree_unique. 2: exact Hittro. 3: apply HPCo.
    2: by eapply Hwfo.
    setoid_rewrite every_node_eqv_universal in H2.
    eapply Hwfo in Hcldino as Hcldunqo.
    eapply unique_lookup in Hcldunqo as Hlu. destruct Hlu as (itcldo&Hlucldo).
    assert (itcldo = itcld) as <-.
    { eapply create_child_preserves_determined in Hlucldo. 3: done. 2: done.
      eapply every_node_eqv_universal in Hlucldo. 1: symmetry; by eapply Hlucldo. 1: done. }
    assert (ittro = ittg) as <-.
    { eapply create_child_preserves_determined in Hittro. 3: exact H1. 2: done.
      eapply tree_determined_unify. 2: apply Hittro. 2: done. 1: done. }
    eapply H2. 2: done.
    eapply exists_node_eqv_existential in Hcldino as (n1&Hn1&HHn1).
    eapply every_node_eqv_universal in Hlucldo. 2: apply Hn1.
    rewrite -Hlucldo //.
Qed.

Lemma apply_within_trees_insert_child_parents_more_active blk cids oldt nxtp pk im rk cid trso trsn : 
  apply_within_trees (create_child cids oldt nxtp pk im rk cid) blk trso = Some trsn →
  each_tree_parents_more_active trso →
  wf_trees trso →
  wf_trees trsn →
  trees_contain oldt trso blk →
  ¬ trees_contain nxtp trso blk →
  each_tree_parents_more_active trsn.
Proof.
  intros (tro&Htro&(trn&Hacc&[= <-])%bind_Some)%bind_Some H2 H3 H3' H4 H5.
  rewrite /trees_contain /trees_at_block !Htro in H4,H5.
  intros blk' tr' [(<-&<-)|(Hne&HH)]%lookup_insert_Some.
  2: by eapply H2.
  eapply insert_child_parents_more_active; try done. 1: by eapply H2. 1: by eapply H3.
  destruct H3' as (H3'&_). eapply H3'. eapply lookup_insert_eq.
Qed.

Lemma insert_child_protected_parents_not_disabled cids oldt nxtp pk im rk cid tro trn : 
  create_child cids oldt nxtp pk im rk cid tro = Some trn →
  protected_parents_not_disabled cids tro →
  wf_tree tro →
  wf_tree trn →
  tree_contains oldt tro →
  ¬ tree_contains nxtp tro →
  protected_parents_not_disabled cids trn.
Proof.
  intros H1 H2 Hwfo Hwfn H4 H5 tg off.
  opose proof (insertion_contains _ _ _ _ _ _ _ _ _ H4 H1) as Hcontnew.
  opose proof (insertion_preserves_tags H4 H1) as H4new.
  destruct (decide (tg = nxtp)) as [->|Hne].
  { eapply every_child_ParentChildIn. 1-2: by eapply wf_tree_tree_unique.
    intros itp Hitdet tgcld Hunq HPC. eapply every_node_eqv_universal.
    intros itn Hitn Htg l. eapply create_child_determined in H1 as HH. 1: destruct HH as (it&(x&Hx&[= <-])%bind_Some&HH1&HH2). 2-3: done.
    opose proof* tree_determined_unify as Heq. 2: exact HH2. 2: exact Hitdet. 1: done.
    enough (itn = itp).
    1: subst itp itn; rewrite /item_lookup /= lookup_empty /= //.
    eapply every_node_eqv_universal in Hitdet. 1: eapply Hitdet. 2: done.
    rewrite Htg. destruct HPC as [?|HPC]; first by subst.
    exfalso. eapply insertion_order_nonstrictparent. 3: done. 3: done.
    2: done. 1: done. }
  destruct (decide (tree_contains tg trn)) as [Hin|Hnin].
  2: by eapply every_child_not_in.
  assert (tree_contains tg tro) as Hino.
  { eapply insertion_minimal_tags. 3: done. 2: done. 1: done. }
  eapply every_child_ParentChildIn.
  1-2: by eapply wf_tree_tree_unique.
  intros ittg Hittg tgcld Hitcld HPCI.
  destruct (decide (tgcld = nxtp)) as [<-|Hnotnew].
  - eapply every_node_eqv_universal. intros itcld Hitcld2 Htgcld.
    edestruct create_child_determined as (it&(x&Hx&[= <-])%bind_Some&_&Hdet). 3: done. 2: done. 1: done.
    eapply every_node_eqv_universal in Hdet. 2: exact Hitcld2.
    rewrite Hdet; last done. intros l.
    rewrite /item_lookup /= lookup_empty /=.
    by destruct pk.
  - eapply every_node_eqv_universal. intros itcld Hitcld2 Htgcld.
    assert (tree_contains tgcld tro) as Hcldino.
    { eapply insertion_minimal_tags. 3: done. 2: by eapply unique_exists. 1: done. }
    specialize (H2 tg).
    destruct (unique_lookup tro tg) as (ittro&Hittro).
    1: by eapply Hwfo.
    assert (ParentChildIn tg tgcld tro) as HPCo.
    { destruct HPCI as [HPCI|HPCI]; first by left. right.
      eapply bind_Some in H1 as (x&Hx%new_item_has_tag&[= H1]). rewrite -H1 in HPCI.
      eapply insert_eqv_strict_rel in HPCI; first done.
      all: rewrite Hx //. }
    eapply every_child_ParentChildIn in H2.
    2-3: by eapply wf_tree_tree_unique. 2: exact Hittro. 3: apply HPCo.
    2: by eapply Hwfo.
    setoid_rewrite every_node_eqv_universal in H2.
    eapply Hwfo in Hcldino as Hcldunqo.
    eapply unique_lookup in Hcldunqo as Hlu. destruct Hlu as (itcldo&Hlucldo).
    assert (itcldo = itcld) as <-.
    { eapply create_child_preserves_determined in Hlucldo. 3: done. 2: done.
      eapply every_node_eqv_universal in Hlucldo. 1: symmetry; by eapply Hlucldo. 1: done. }
    assert (ittro = ittg) as <-.
    { eapply create_child_preserves_determined in Hittro. 3: exact H1. 2: done.
      eapply tree_determined_unify. 2: apply Hittro. 2: done. 1: done. }
    eapply H2. 2: done.
    eapply exists_node_eqv_existential in Hcldino as (n1&Hn1&HHn1).
    eapply every_node_eqv_universal in Hlucldo. 2: apply Hn1.
    rewrite -Hlucldo //.
Qed.

Lemma apply_within_trees_insert_child_protected_parents_not_disabled blk cids oldt nxtp pk im rk cid trso trsn : 
  apply_within_trees (create_child cids oldt nxtp pk im rk cid) blk trso = Some trsn →
  each_tree_protected_parents_not_disabled cids trso →
  wf_trees trso →
  wf_trees trsn →
  trees_contain oldt trso blk →
  ¬ trees_contain nxtp trso blk →
  each_tree_protected_parents_not_disabled cids trsn.
Proof.
  intros (tro&Htro&(trn&Hacc&[= <-])%bind_Some)%bind_Some H2 H3 H3' H4 H5.
  rewrite /trees_contain /trees_at_block !Htro in H4,H5.
  intros blk' tr' [(<-&<-)|(Hne&HH)]%lookup_insert_Some.
  2: by eapply H2.
  eapply insert_child_protected_parents_not_disabled; try done. 1: by eapply H2. 1: by eapply H3.
  destruct H3' as (H3'&_). eapply H3'. eapply lookup_insert_eq.
Qed.

Lemma insert_child_no_active_cousins cids oldt nxtp pk im rk cid tro trn : 
  create_child cids oldt nxtp pk im rk cid tro = Some trn →
  no_active_cousins cids tro →
  wf_tree tro →
  wf_tree trn →
  tree_contains oldt tro →
  ¬ tree_contains nxtp tro →
  no_active_cousins cids trn.
Proof.
  intros H1 H2 Hwfo Hwfn H4 H5 tg1 it1 tg2 it2.
  opose proof (insertion_contains _ _ _ _ _ _ _ _ _ H4 H1) as Hcontnew.
  opose proof (insertion_preserves_tags H4 H1) as H4new.
  intros off Hit1 Hit2 Hcs Ha1 Ha2.
  destruct (decide (tg1 = nxtp)) as [->|Hne].
  { edestruct create_child_determined as (it&(x&Hx&[= Hit])%bind_Some&HHH).
    4: opose proof* tree_lookup_unique as Heq.
    4: eapply HHH. 3: done. 1,2: done. 1: eapply Hit1.
    subst it1. rewrite -Hit /active_or_prot_init /item_lookup /= lookup_empty /= in Ha1.
    destruct Ha1 as [Ha1|(?&[=])]. destruct pk, im, rk; by simplify_eq. }
  destruct (decide (tg2 = nxtp)) as [->|Hne2].
  { edestruct create_child_determined as (it&(x&Hx&[= Hit])%bind_Some&HHH).
    4: opose proof* tree_lookup_unique as Heq.
    4: eapply HHH. 3: done. 1,2: done. 1: eapply Hit2.
    subst it2. rewrite -Hit /item_lookup /= lookup_empty /= in Ha2. destruct pk, im, rk; by simplify_eq. }
  assert (tree_unique tg1 trn) as Hu1.
  1: eapply Hwfn; try done; eapply Hit1.
  assert (tree_unique tg2 trn) as Hu2.
  1: eapply Hwfn; try done; eapply Hit2.
  rewrite /tree_unique in Hu1,Hu2.
  erewrite <-  create_child_preserves_count in Hu1. 3: exact H1. 2: done.
  erewrite <-  create_child_preserves_count in Hu2. 3: exact H1. 2: done.
  eapply unique_implies_lookup in Hu1 as (it1P&Hit1P).
  eapply unique_implies_lookup in Hu2 as (it2P&Hit2P).
  assert (it1 = it1P) as <-.
  { eapply tree_determined_unify. 1-2: apply Hit1. eapply create_child_preserves_determined. 3: exact H1. 1: done. 1: apply Hit1P. }
  assert (it2 = it2P) as <-.
  { eapply tree_determined_unify. 1-2: apply Hit2. eapply create_child_preserves_determined. 3: exact H1. 1: done. 1: apply Hit2P. }
  eapply H2.
  4: exact Ha1. 4: exact Ha2. 1-2: done.
  erewrite create_child_same_rel_dec. 4: eassumption. 1: done. 1-2: done.
Qed.

Lemma apply_within_trees_insert_child_no_active_cousins blk cids oldt nxtp pk im rk cid trso trsn : 
  apply_within_trees (create_child cids oldt nxtp pk im rk cid) blk trso = Some trsn →
  each_tree_no_active_cousins cids trso →
  wf_trees trso →
  wf_trees trsn →
  trees_contain oldt trso blk →
  ¬ trees_contain nxtp trso blk →
  each_tree_no_active_cousins cids trsn.
Proof.
  intros (tro&Htro&(trn&Hacc&[= <-])%bind_Some)%bind_Some H2 H3 H3' H4 H5.
  rewrite /trees_contain /trees_at_block !Htro in H4,H5.
  intros blk' tr' [(<-&<-)|(Hne&HH)]%lookup_insert_Some.
  2: by eapply H2.
  eapply insert_child_no_active_cousins; try done. 1: by eapply H2. 1: by eapply H3.
  destruct H3' as (H3'&_). eapply H3'. eapply lookup_insert_eq.
Qed.

Lemma state_wf_nt_not_contained σ blk :
  state_wf σ →
  ¬ trees_contain σ.(snp) σ.(strs) blk.
Proof.
  intros Hwf.
  rewrite /trees_contain /trees_at_block.
  destruct (strs σ !! blk) as [tr|] eqn:Htr; last tauto.
  pose proof (state_wf_tree_compat _ Hwf _ _ Htr) as Hcompat.
  intros (it&Hit&Htg)%exists_node_eqv_existential.
  eapply every_node_eqv_universal in Hcompat. 2: done.
  eapply item_tag_valid in Htg; last done. lia.
Qed.

Lemma create_new_item_wf it nt pk im rk (cid nxtc' : nat) : 
  (cid < nxtc')%nat →
  create_new_item nt pk im rk cid = Some it →
  item_wf it (S nt) nxtc'.
Proof.
  intros H (x&Hx&[= <-])%bind_Some.
  split; rewrite /create_new_item /=.
  + rewrite /=. intros ? <-; lia.
  + destruct rk; last done.
    rewrite /= /protector_is_for_call /=.
    intros ? [= <-]. by eapply H.
  + clear -Hx. cbv. unfold retag_perm in Hx. destruct pk, im, rk; by simplify_eq.
  + destruct rk. 2: intros [? [=]].
    destruct pk, im; simpl in Hx; simplify_eq; simpl.
    all: intros _ off; rewrite lookup_empty /=; intros [=].
    all: eapply Hnot.
  + done.
  + intros _. eapply map_Forall_empty.
Qed.

Lemma create_child_root_compat (ni:item) fn D tr tr' blk hp :
  tree_root_compatible tr blk hp →
  @insert_child_at _ tr ni fn D = tr' →
  tree_root_compatible tr' blk hp.
Proof.
  rewrite /tree_root_compatible.
  destruct tr as [|it tr1 tr2]; first done.
  intros (Hroot&->) Hc.
  simpl in Hc. destruct (decide (fn it)); subst tr'; simpl; done.
Qed.

Lemma create_child_roots_compat C ot nt pk im rk cid trs trs' blk hp :
  tree_roots_compatible trs hp →
  apply_within_trees (create_child C ot nt pk im rk cid) blk trs = Some trs' →
  tree_roots_compatible trs' hp.
Proof.
  intros Hroot (tr&Htr&(tr'&(x&Hx&Htr')%bind_Some&[= <-])%bind_Some)%bind_Some.
  intros blkX trX [(<-&<-)|(Hne&Hin)]%lookup_insert_Some.
  - eapply create_child_root_compat. 1: by eapply Hroot.
    by injection Htr'.
  - by eapply Hroot.
Qed.

Lemma create_child_tree_contains C ot nt pk im rk cid trs trs' blk blk' tg :
  trees_contain tg trs blk' →
  apply_within_trees (create_child C ot nt pk im rk cid) blk trs = Some trs' →
  trees_contain tg trs' blk'.
Proof.
  intros Hroot (tr&Htr&(tr'&Htr'&[= <-])%bind_Some)%bind_Some.
  rewrite /trees_contain /trees_at_block in Hroot|-*.
  destruct (trs !! blk') as [tr1|] eqn:Heq. 2: done.
  destruct (decide (blk = blk')) as [->|Hne].
  - rewrite lookup_insert_eq. assert (tr = tr1) as -> by congruence.
    by eapply insertion_preserves_tags.
  - rewrite lookup_insert_ne // Heq //.
Qed.

Lemma retag_step_wf_inner σ blk ot pk im rk cid trsmid :
  state_wf σ →
  trees_contain ot σ.(strs) blk →
  ¬ trees_contain σ.(snp) σ.(strs) blk →
  cid ∈ σ.(scs) →
  apply_within_trees (create_child σ.(scs) ot σ.(snp) pk im rk cid) blk σ.(strs) = Some trsmid →
  state_wf (mkState σ.(shp) trsmid σ.(scs) (S σ.(snp)) σ.(snc)) ∧ trees_contain σ.(snp) trsmid blk.
Proof.
  intros WF EXISTS_TAG FRESH_CHILD CALL_ACTIVE RETAG_EFFECT.
  destruct σ as [h' trs cids' nt nxtc']. simpl in *.
  assert (trees_compat_nexts trsmid (S nt) nxtc' ∧ wf_trees trsmid) as (Hwfmid1 & Hwfmid2).
  { eapply apply_within_trees_compat_both; first done; last first.
    - split; by eapply WF.
    - simpl. intros tr tr' tg Hcr Hcont.
      destruct (decide (tg = nt)) as [->|Hne].
      1: right; lia.
      1: left; eapply insertion_minimal_tags; last done; try done.
    - simpl. intros ?? Hx ??. pose proof Hx as (it&Hit&[= HH])%bind_Some.
      eapply insert_child_wf; try done.
      eapply create_new_item_wf. 1: by eapply WF. 1: done.
    - simpl. intros ??. eapply tree_items_compat_nexts_mono; last done; lia. }
  split; first constructor; simpl.
  - rewrite /same_blocks /=
            -(apply_within_trees_same_dom _ _ _ _ RETAG_EFFECT).
    apply WF.
  - done.
  - eapply apply_within_trees_insert_child_parents_more_init. 1: done. 1-2: apply WF. 1-3: done.
  - eapply apply_within_trees_insert_child_parents_more_active. 1: done. 1-2: apply WF. 1-3: done.
  - eapply apply_within_trees_insert_child_protected_parents_not_disabled. 1: done. 1-2: apply WF. 1-3: done.
  - eapply apply_within_trees_insert_child_no_active_cousins. 1: done. 1-2: apply WF. 1-3: done.
  - done.
  - eapply create_child_roots_compat. 2: done. apply WF.
  - apply WF.
  - eapply bind_Some in RETAG_EFFECT as (x1&Hx1&(x2&Hx2&[= <-])%bind_Some).
    rewrite /trees_contain /trees_at_block lookup_insert_eq. eapply insertion_contains; last done.
    by rewrite /trees_contain /trees_at_block Hx1 in EXISTS_TAG.
Qed.

Lemma retag_step_wf σ σ' e e' blk range ot nt pk im rk cid efs :
  mem_expr_step σ.(shp) e (RetagEvt blk range ot nt pk im cid rk) σ'.(shp) e' efs →
  bor_step σ.(strs) σ.(scs) σ.(snp) σ.(snc)
           (RetagEvt blk range ot nt pk im cid rk)
           σ'.(strs) σ'.(scs) σ'.(snp) σ'.(snc) →
  state_wf σ → state_wf σ'.
Proof.
  destruct σ as [h trs cids nxtp nxtc].
  destruct σ' as [h' trs' cids' nxtp' nxtc']. simpl.
  intros BS IS WF.
  inversion BS. clear BS. simplify_eq.
  inversion IS as [| | | | |trsmid ???????? EXISTS_TAG FRESH_CHILD RETAG_EFFECT READ_ON_REBOR| | | |].
  2: by simplify_eq. simplify_eq.
  eapply retag_step_wf_inner in WF as (WF&TAG_AFTER_ADD); simpl in WF|-*. 2-5: try done.
  eapply access_step_wf_inner in WF. all: done.
Qed.

Lemma base_step_wf P σ σ' e e' efs :
  base_step P e σ e' σ' efs → state_wf σ → state_wf σ'.
Proof.
  intros HS WF. inversion HS; [by subst|]. simplify_eq.
  rename select event into ev. destruct ev.
  - eapply alloc_step_wf; eauto.
  - eapply dealloc_step_wf; eauto.
  - eapply read_step_wf; eauto.
 (* - eapply failed_copy_step_wf; eauto. *)
  - eapply write_step_wf; eauto.
  - eapply initcall_step_wf; eauto.
  - eapply endcall_step_wf; eauto.
  - eapply retag_step_wf; eauto.
  - rename select (mem_expr_step _ _ _ _ _ _) into Hstep. inversion Hstep.
Qed.




Lemma mem_apply_locs_id X (fn : option X → option X) z (sz:nat) M :
  (∀ off, z ≤ off < z + sz → ∃ k, M !! off = Some k ∧ fn (Some k) = Some k) →
  mem_apply_locs fn z sz M = Some M.
Proof.
  induction sz as [|sz IH] in z,M|-*; first done.
  intros H. rewrite /= /mem_apply_loc /=.
  destruct (H z) as (k&HMk&Hfnk). 1: lia.
  rewrite HMk Hfnk /= insert_id //. eapply IH.
  intros ??; eapply H. lia.
Qed.

Lemma zero_sized_memory_access_unchanged b acc scs t off tr :
  memory_access_maybe_nonchildren_only b acc scs t (off, 0%nat) tr = Some tr.
Proof.
  rewrite /memory_access_maybe_nonchildren_only /tree_apply_access.
  eapply join_map_id_identical.
  intros it Hit.
  rewrite /item_apply_access /permissions_apply_range' /mem_apply_range'.
  rewrite mem_apply_locs_id. 1: by destruct it.
  intros ? HH; simpl in HH. lia.
Qed.



