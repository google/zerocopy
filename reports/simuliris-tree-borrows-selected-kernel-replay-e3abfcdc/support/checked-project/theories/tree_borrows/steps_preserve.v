From iris.prelude Require Import prelude options.
From simuliris.tree_borrows Require Import lang_base notation bor_semantics tree tree_lemmas bor_lemmas defs.

(** Lemmas about borrow steps preserving properties of the tree.
    This is related to [steps_wf.v], but where [steps_wf] states lemmas about
    preservation of well-formedness by all borrow steps, these are lower-level.
    Many lemmas here will seem trivial (e.g. if you have a tree in which a tag
   is unique and you apply a tag-preserving function, the tag is still unique). *)

(* Any function that operates only on permissions (which is all transitions steps)
   leaves the tag and protector unchanged which means that most of the preservation lemmas
   are trivial once we get to the level of items.
   Preservation of metadata includes preservation of relationships since
   the parent-child relation is defined by the relative location of tags
   (which are metadata). *)
Definition preserve_item_metadata (fn:item -> option item) :=
  forall it it', fn it = Some it' -> it.(itag) = it'.(itag) /\ it.(iprot) = it'.(iprot) /\ it.(initp) = it'.(initp).

Lemma item_apply_access_preserves_metadata_dep
  {kind cids rel range} :
  preserve_item_metadata (λ it, item_apply_access kind cids (rel it) range it).
Proof.
  intros it it'. rewrite /item_apply_access.
  destruct permissions_apply_range'; simpl.
  2: intro; discriminate.
  intros [= <-]. rewrite //=.
Qed.

Lemma item_apply_access_preserves_metadata
  {kind cids rel range} :
  preserve_item_metadata (λ it, item_apply_access kind cids rel range it).
Proof.
  eapply item_apply_access_preserves_metadata_dep.
Qed.

Lemma access_eqv_immediate_rel
  {t t' tr tr' fn cids tg range}
  (Access : tree_apply_access fn cids tg range tr = Some tr')
  : ImmediateParentChildIn t t' tr <-> ImmediateParentChildIn t t' tr'.
Proof.
  eapply join_map_eqv_imm_rel; [|exact Access].
  rewrite /=.
  move=> ???.
  unshelve erewrite (proj1 (item_apply_access_preserves_metadata _ _ ltac:(eassumption))).
  reflexivity.
Qed.

Lemma access_eqv_strict_rel
  {t t' tr tr' fn cids tg range}
  (Access : tree_apply_access fn cids tg range tr = Some tr')
  : StrictParentChildIn t t' tr <-> StrictParentChildIn t t' tr'.
Proof.
  eapply join_map_eqv_strict_rel; [|exact Access].
  rewrite /=.
  move=> ???.
  unshelve erewrite (proj1 (item_apply_access_preserves_metadata _ _ ltac:(eassumption))).
  reflexivity.
Qed.

Lemma access_eqv_rel
  {t t' tr tr' fn cids tg range}
  (Access : tree_apply_access fn cids tg range tr = Some tr')
  : ParentChildIn t t' tr <-> ParentChildIn t t' tr'.
Proof.
  unfold ParentChildIn.
  rewrite access_eqv_strict_rel; [|exact Access].
  tauto.
Qed.

Lemma access_same_rel_dec
  {tr tr' fn cids acc_tg range}
  : tree_apply_access fn cids acc_tg range tr = Some tr' ->
  forall tg tg', rel_dec tr tg tg' = rel_dec tr' tg tg'.
Proof.
  intros Acc tg tg'.
  rewrite /rel_dec.
  pose proof (@access_eqv_rel tg tg' _ _ _ _ _ _ Acc).
  pose proof (@access_eqv_rel tg' tg _ _ _ _ _ _ Acc).
  pose proof (@access_eqv_immediate_rel tg tg' _ _ _ _ _ _ Acc).
  pose proof (@access_eqv_immediate_rel tg' tg _ _ _ _ _ _ Acc).
  repeat destruct (decide _).
  all: try tauto.
Qed.

Lemma access_preserves_tags
  {tr tg  tr' tg' app cids range}
  (Access : tree_apply_access app cids tg' range tr = Some tr')
  : tree_contains tg tr <-> tree_contains tg tr'.
Proof.
  unfold tree_apply_access in Access.
  unfold tree_contains in *.
  rewrite (join_project_exists _ _ tr').
  2: exact Access.
  rewrite exists_node_map.
  unfold compose.
  pose proof (proj1 (join_success_condition (map_nodes _ tr)) (mk_is_Some _ _ Access)) as H.
  rewrite every_node_map in H.
  split; intro Contains.
  * eapply exists_node_increasing.
    - exact Contains.
    - unfold compose in H.
      rewrite every_node_eqv_universal.
      rewrite every_node_eqv_universal in H.
      intros x Exists Tagx.
      pose proof (H x Exists) as Hspec.
      destruct Hspec as [v App].
      exists v.
      split; auto.
      subst.
      symmetry.
      rewrite (proj1 ( item_apply_access_preserves_metadata _ _ ltac:(eassumption))).
      reflexivity.
  * eapply exists_node_increasing.
    - exact Contains.
    - rewrite every_node_eqv_universal.
      intros x Exists xspec.
      destruct xspec as [v App].
      destruct App as [H0].
      subst.
      rewrite (proj1 (item_apply_access_preserves_metadata _ _ ltac:(eassumption))).
      reflexivity.
Qed.

Lemma insertion_preserves_tags
  {tr tg tgp tgc cids tr' pk im rk cid}
  (Ex : tree_contains tg tr)
  (Create : create_child cids tgp tgc pk im rk cid tr = Some tr')
  : tree_contains tg tr'.
Proof.
  unfold tree_contains in *.
  pose proof (create_child_isSome tr _ _ _ _ _ _ _ _ Create) as (it&Hit&Insert).
  rewrite Insert.
  apply insert_preserves_exists.
  exact Ex.
Qed.

Lemma insertion_minimal_tags
  {tr tg tgp tgc cids tr' pk im rk cid}
  (Ne : tgc ≠ tg)
  (Ex : tree_contains tg tr')
  (Create : create_child cids tgp tgc pk im rk cid tr = Some tr')
  : tree_contains tg tr.
Proof.
  unfold tree_contains in *.
  pose proof (create_child_isSome tr _ _ _ _ _ _ _ _ Create) as (x&Hx&Insert).
  all: rewrite Insert in Ex.
  eapply insert_false_infer_exists; [|exact Ex].
  erewrite new_item_has_tag; done.
Qed.

(** Detailed specification of the effects of one access.
    This is to trees what [mem_apply_range'_spec] is to ranges. *)
Lemma apply_access_spec_per_node
  {tr affected_tag access_tag pre fn cids range tr'}
  (ExAff : tree_contains affected_tag tr)
  (UnqAff : tree_item_determined affected_tag pre tr)
  (Access : tree_apply_access fn cids access_tag range tr = Some tr')
  : exists post,
    Some post = item_apply_access fn cids (rel_dec tr access_tag pre.(itag)) range pre
    /\ tree_contains affected_tag tr'
    /\ tree_item_determined affected_tag post tr'.
Proof.
  (* Grab the success condition of every node separately *)
  pose proof (proj1 (join_success_condition _) (mk_is_Some _ _ Access)) as SuccessCond.
  rewrite every_node_map in SuccessCond; rewrite every_node_eqv_universal in SuccessCond.
  pose proof (exists_determined_exists _ _ _ ExAff UnqAff) as Expre.
  pose proof (SuccessCond pre Expre) as [post SpecPost].
  unfold tree_item_determined in UnqAff. rewrite every_node_eqv_universal in UnqAff.
  (* Now do some transformations to get to the node level *)
  unfold tree_item_determined.
  exists post.
  split; [symmetry; auto|].
  split; [rewrite <- (access_preserves_tags Access); exact ExAff|].
  rewrite join_project_every; [|exact Access].
  rewrite every_node_map.
  unfold compose.
  rewrite every_node_eqv_universal.
  intros n Exn.
  destruct (decide (IsTag affected_tag n)).
  * pose proof (UnqAff n Exn) as PerNodeEqual.
    clear Access ExAff SuccessCond UnqAff ExAff Exn.
    exists post.
    split; [|tauto].
    rewrite PerNodeEqual; auto.
  * pose proof (SuccessCond n Exn) as NodeSuccess.
    destruct NodeSuccess as [post' post'Spec].
    exists post'.
    split.
    - tauto.
    - rewrite <- (proj1 (item_apply_access_preserves_metadata _ _ ltac:(eassumption))).
      tauto.
Qed.

(** Reachability of a state behaves as expected in between applications
    of functions compatible with [reach]. *)
Lemma apply_access_perm_preserves_backward_reach
  {pre post kind rel b p0}
  (Access : apply_access_perm kind rel b pre = Some post)
  : reach p0 (perm pre) -> reach p0 (perm post).
Proof.
  destruct b, kind, rel.
  (* We have to destructure the permission a bit deep because of the Reserved parameters *)
  all: destruct pre as [[] [|[]| | | |]]; try (inversion Access; done).
  all: destruct post as [[] [|[]| | | |]]; try (inversion Access; done).
  all: destruct p0 as [|[]| | | |]; try (inversion Access; done).
Qed.

Lemma apply_access_perm_preserves_forward_unreach
  {pre post kind rel b p0}
  (Access : apply_access_perm kind rel b pre = Some post)
  : ~reach (perm pre) p0 -> ~reach (perm post) p0.
Proof.
  destruct b, kind, rel.
  all: destruct pre as [[][|[]| | | |]]; try (inversion Access; done).
  all: destruct post as [[][|[]| | | |]]; try (inversion Access; done).
  all: destruct p0 as [|[]| | | |]; try (inversion Access; done).
Qed.

Lemma apply_access_perm_preserves_protected_freeze_like
  {pre post kind rel}
  (Access : apply_access_perm kind rel true pre = Some post)
  : freeze_like (perm pre) -> freeze_like (perm post).
Proof.
  unfold freeze_like.
  destruct kind, rel.
  all: destruct pre as [[][|[]| | | |]].
  all: inversion Access.
  (* all cases easy *)
  all: intros [H|H]; inversion H.
  all: try (left; done).
  all: try (right; done).
Qed.

(* Preservation of reachability *)
Lemma memory_access_preserves_backward_reach
  {access_tag affected_tag pre tr post tr' kind cids range p0 z}
  (ExAff : tree_contains affected_tag tr)
  (UnqAff : tree_item_determined affected_tag pre tr)
  (ExAcc : tree_contains access_tag tr)
  (Access : memory_access kind cids access_tag range tr = Some tr')
  (UnqAff' : tree_item_determined affected_tag post tr')
  : reach p0 (item_perm_at_loc pre z) -> reach p0 (item_perm_at_loc post z).
Proof.
  destruct (apply_access_spec_per_node ExAff UnqAff Access) as [post' [PostSpec [ExPost UnqPost]]].
  pose proof (tree_determined_unify ExPost UnqPost UnqAff'); subst.
  (* now it's just bruteforce case analysis *)
  generalize dependent post.
  generalize dependent pre.
  clear. move=> pre _ post _ Access _.
  option step in Access as ?:Foreach.
  injection Access; intros e; subst; clear Access.
  pose proof (mem_apply_range'_spec _ _ z _ _ Foreach) as Spec; clear Foreach.
  rewrite /item_perm_at_loc /item_lazy_perm_at_loc /item_lookup; simpl.
  destruct (decide (range'_contains _ _)).
  - destruct Spec as [?[Lkup Apply]].
    eapply apply_access_perm_preserves_backward_reach.
    rewrite Lkup; simpl. exact Apply.
  - rewrite Spec; tauto.
Qed.

Lemma memory_access_preserves_forward_unreach
  {access_tag affected_tag pre tr post tr' kind cids range p0 z}
  (ExAff : tree_contains affected_tag tr)
  (UnqAff : tree_item_determined affected_tag pre tr)
  (ExAcc : tree_contains access_tag tr)
  (Access : memory_access kind cids access_tag range tr = Some tr')
  (UnqAff' : tree_item_determined affected_tag post tr')
  : ~reach (item_perm_at_loc pre z) p0 -> ~reach (item_perm_at_loc post z) p0.
Proof.
  destruct (apply_access_spec_per_node ExAff UnqAff Access) as [post' [PostSpec [ExPost UnqPost]]].
  pose proof (tree_determined_unify ExPost UnqPost UnqAff'); subst.
  (* now it's just bruteforce case analysis *)
  generalize dependent post.
  generalize dependent pre.
  clear. move=> pre _ post _ Access _.
  option step in Access as ?:Foreach.
  injection Access; intros e; subst; clear Access.
  pose proof (mem_apply_range'_spec _ _ z _ _ Foreach) as Spec; clear Foreach.
  rewrite /item_perm_at_loc /item_lazy_perm_at_loc /item_lookup; simpl.
  destruct (decide (range'_contains _ _)).
  - destruct Spec as [?[Lkup Apply]].
    eapply apply_access_perm_preserves_forward_unreach.
    rewrite Lkup; simpl. exact Apply.
  - rewrite Spec; tauto.
Qed.

Lemma memory_access_preserves_protected_freeze_like
  {access_tag affected_tag pre tr post tr' kind cids range z}
  (ExAff : tree_contains affected_tag tr)
  (UnqAff : tree_item_determined affected_tag pre tr)
  (ExAcc : tree_contains access_tag tr)
  (Prot : protector_is_active (iprot pre) cids)
  (Access : memory_access kind cids access_tag range tr = Some tr')
  (UnqAff' : tree_item_determined affected_tag post tr')
  : freeze_like (item_perm_at_loc pre z) -> freeze_like (item_perm_at_loc post z).
Proof.
  destruct (apply_access_spec_per_node ExAff UnqAff Access) as [post' [PostSpec [ExPost UnqPost]]].
  pose proof (tree_determined_unify ExPost UnqPost UnqAff'); subst.
  (* now it's just bruteforce case analysis *)
  generalize dependent post.
  generalize dependent pre.
  clear. move=> pre _ Prot post _ Access _.
  option step in Access as ?:Foreach.
  injection Access; intros e; subst; clear Access.
  pose proof (mem_apply_range'_spec _ _ z _ _ Foreach) as Spec; clear Foreach.
  rewrite /item_perm_at_loc /item_lazy_perm_at_loc /item_lookup; simpl.
  destruct (decide (range'_contains _ _)).
  - destruct Spec as [?[Lkup Apply]].
    eapply apply_access_perm_preserves_protected_freeze_like.
    rewrite bool_decide_eq_true_2 in Apply; [|assumption].
    rewrite Lkup; simpl. exact Apply.
  - rewrite Spec; tauto.
Qed.

Lemma apply_access_perm_preserves_perminit
  {pre post kind rel b}
  (Access : apply_access_perm kind rel b pre = Some post)
  : (initialized pre) = PermInit -> initialized post = PermInit.
Proof.
  destruct kind, rel.
  all: destruct pre as [[][|[]| | | |]], b.
  all: inversion Access.
  (* all cases easy *)
  all: simpl; auto.
  all: intros H H'; inversion H'; inversion H.
Qed.

(** Initialized status is monotonous: an initialized location stays initialized. *)
Lemma memory_access_preserves_perminit
  {access_tag affected_tag pre tr post tr' kind cids range z zpre zpost}
  (ExAff : tree_contains affected_tag tr)
  (UnqAff : tree_item_determined affected_tag pre tr)
  (ExAcc : tree_contains access_tag tr)
  (Access : memory_access kind cids access_tag range tr = Some tr')
  (UnqAff' : tree_item_determined affected_tag post tr')
  (ItemPre : item_lazy_perm_at_loc pre z = zpre)
  (ItemPost : item_lazy_perm_at_loc post z = zpost)
  (Init : initialized zpre = PermInit)
  : initialized zpost = PermInit.
Proof.
  destruct (apply_access_spec_per_node ExAff UnqAff Access) as [post' [PostSpec [ExPost UnqPost]]].
  pose proof (tree_determined_unify ExPost UnqPost UnqAff'); subst.
  generalize dependent post.
  generalize dependent pre.
  clear. move=> pre _ Init post _ Access _.
  option step in Access as ?:Foreach.
  injection Access; intros e; subst; clear Access.
  pose proof (mem_apply_range'_spec _ _ z _ _ Foreach) as Spec; clear Foreach.
  rewrite /item_perm_at_loc /item_lazy_perm_at_loc /item_lookup; simpl.
  destruct (bool_decide _).
  all: destruct (decide (range'_contains _ _)).
  all: try (rewrite Spec; tauto).
  all: destruct Spec as [?[Lkup Apply]].
  all: eapply apply_access_perm_preserves_perminit; [|eassumption].
  all: rewrite Lkup; simpl; try exact Apply.
Qed.

(** Furthermore a child access produces an initialized. *)
Lemma apply_access_perm_child_produces_perminit
  {pre post kind b rel}
  (CHILD : if rel is Child _ then True else False)
  (Access : apply_access_perm kind rel b pre = Some post)
  : initialized post = PermInit.
Proof.
  destruct kind, rel; try inversion CHILD.
  all: destruct pre as [[][|[]| | | |]], b.
  all: inversion Access.
  (* all cases easy *)
  all: simpl; auto.
Qed.

Lemma memory_access_child_produces_perminit
  {access_tag affected_tag pre tr post tr' kind cids range z zpre zpost}
  (ExAff : tree_contains affected_tag tr)
  (UnqAff : tree_item_determined affected_tag pre tr)
  (ExAcc : tree_contains access_tag tr)
  (Access : memory_access kind cids access_tag range tr = Some tr')
  (Rel : ParentChildIn affected_tag access_tag tr)
  (WithinRange : range'_contains range z)
  (UnqAff' : tree_item_determined affected_tag post tr')
  (ItemPre : item_lazy_perm_at_loc pre z = zpre)
  (ItemPost : item_lazy_perm_at_loc post z = zpost)
  : initialized zpost = PermInit.
Proof.
  destruct (apply_access_spec_per_node ExAff UnqAff Access) as [post' [PostSpec [ExPost UnqPost]]].
  pose proof (tree_determined_unify ExPost UnqPost UnqAff'); subst.
  rewrite (tree_determined_specifies_tag _ _ _ ExAff UnqAff) in PostSpec.
  unfold rel_dec in PostSpec.
  destruct (decide (ParentChildIn affected_tag access_tag tr)); [|contradiction].
  destruct (decide (ParentChildIn access_tag affected_tag tr)).
  all: option step in PostSpec as ?:Foreach.
  all: injection PostSpec; intros e; subst; clear PostSpec.
  all: pose proof (mem_apply_range'_spec _ _ z _ _ Foreach) as Spec; clear Foreach.
  all: rewrite /item_perm_at_loc /item_lazy_perm_at_loc /item_lookup; simpl.
  all: destruct (bool_decide _).
  all: destruct (decide (range'_contains _ _)); [|contradiction].
  all: try (rewrite Spec; tauto).
  all: destruct Spec as [?[Lkup Apply]].
  all: eapply apply_access_perm_child_produces_perminit.
  all: try eassumption.
  all: try (rewrite Lkup; simpl; try exact Apply).
  all: simpl; done.
Qed.

(** Protected + initialized prevents loss of [Active]. *)
Lemma apply_access_perm_protected_initialized_preserves_active
  {pre post kind rel}
  (Access : apply_access_perm kind rel true pre = Some post)
  : (initialized pre) = PermInit -> (perm pre) = Active -> (perm post) = Active.
Proof.
  destruct kind, rel.
  all: destruct pre as [[][]].
  all: inversion Access.
  (* all cases easy *)
  all: simpl; auto.
  all: intros H H'; inversion H'; inversion H.
Qed.

Lemma memory_access_protected_initialized_preserves_active
  {access_tag affected_tag pre tr post tr' kind cids range z zpre zpost}
  (ExAff : tree_contains affected_tag tr)
  (UnqAff : tree_item_determined affected_tag pre tr)
  (ExAcc : tree_contains access_tag tr)
  (Access : memory_access kind cids access_tag range tr = Some tr')
  (UnqAff' : tree_item_determined affected_tag post tr')
  (Prot : protector_is_active (iprot pre) cids)
  (ItemPre : item_lazy_perm_at_loc pre z = zpre)
  (ItemPost : item_lazy_perm_at_loc post z = zpost)
  (Init : initialized zpre = PermInit)
  : perm zpre = Active -> perm zpost = Active.
Proof.
  destruct (apply_access_spec_per_node ExAff UnqAff Access) as [post' [PostSpec [ExPost UnqPost]]].
  pose proof (tree_determined_unify ExPost UnqPost UnqAff'); subst.
  (* now it's just bruteforce case analysis *)
  generalize dependent post.
  generalize dependent pre.
  clear. move=> pre _ Prot Init post _ Access _.
  option step in Access as ?:Foreach.
  injection Access; intros e; subst; clear Access.
  pose proof (mem_apply_range'_spec _ _ z _ _ Foreach) as Spec; clear Foreach.
  rewrite /item_perm_at_loc /item_lazy_perm_at_loc /item_lookup; simpl.
  rewrite bool_decide_eq_true_2 in Spec; [|assumption].
  destruct (decide (range'_contains _ _)).
  - destruct Spec as [?[Lkup Apply]].
    eapply apply_access_perm_protected_initialized_preserves_active.
    + rewrite Lkup; simpl. exact Apply.
    + assumption.
  - rewrite Spec; tauto.
Qed.

Lemma apply_access_perm_protected_initialized_preserves_nondis
  {pre post kind rel}
  (Access : apply_access_perm kind rel true pre = Some post)
  : (initialized pre) = PermInit -> ~reach Disabled (perm pre) -> ~reach Disabled (perm post).
Proof.
  destruct kind, rel.
  all: destruct pre as [[][|[]| | | |]].
  all: inversion Access.
  (* all cases easy *)
  all: simpl; auto.
  all: intro H; inversion H.
Qed.

Lemma memory_access_protected_initialized_preserves_nondis
  {access_tag affected_tag pre tr post tr' kind cids range z zpre zpost}
  (ExAff : tree_contains affected_tag tr)
  (UnqAff : tree_item_determined affected_tag pre tr)
  (ExAcc : tree_contains access_tag tr)
  (Access : memory_access kind cids access_tag range tr = Some tr')
  (UnqAff' : tree_item_determined affected_tag post tr')
  (Prot : protector_is_active (iprot pre) cids)
  (ItemPre : item_lazy_perm_at_loc pre z = zpre)
  (ItemPost : item_lazy_perm_at_loc post z = zpost)
  (Init : initialized zpre = PermInit)
  : ~reach Disabled (perm zpre) -> ~reach Disabled (perm zpost).
Proof.
  destruct (apply_access_spec_per_node ExAff UnqAff Access) as [post' [PostSpec [ExPost UnqPost]]].
  pose proof (tree_determined_unify ExPost UnqPost UnqAff'); subst.
  (* now it's just bruteforce case analysis *)
  generalize dependent post.
  generalize dependent pre.
  clear. move=> pre _ Prot Init post _ Access _.
  option step in Access as ?:Foreach.
  injection Access; intros e; subst; clear Access.
  pose proof (mem_apply_range'_spec _ _ z _ _ Foreach) as Spec; clear Foreach.
  rewrite /item_perm_at_loc /item_lazy_perm_at_loc /item_lookup; simpl.
  rewrite bool_decide_eq_true_2 in Spec; [|assumption].
  destruct (decide (range'_contains _ _)).
  - destruct Spec as [?[Lkup Apply]].
    eapply apply_access_perm_protected_initialized_preserves_nondis.
    + rewrite Lkup; simpl. exact Apply.
    + assumption.
  - rewrite Spec; tauto.
Qed.
