From iris.prelude Require Import prelude options.
From simuliris.tree_borrows Require Import lang_base notation bor_semantics tree tree_lemmas.

(** A collection of lemmas to reason about the current state of the tree.
   These are not invariants (you will find those in [steps_wf.v].
   Rather, consider that this file is to [bor_semantics.v] what
   [tree_lemmas.v] is to [tree.v]: these are specialized lemmas
   to reason about the instanciation of trees that is specifically
   with [item]s containing [tag]s (and some non-tree lemmas also). *)

Lemma most_init_comm m1 m2 : most_init m1 m2 = most_init m2 m1.
Proof. by destruct m1, m2. Qed.

Lemma unique_somewhere
  {a b} :
  a + b = 1 -> (a = 1 /\ b = 0) \/ (b = 1 /\ a = 0).
Proof. lia. Qed.

Lemma unique_somewhere_3way
  {a b c} :
  a + b + c = 1 -> (a = 1 /\ b = 0 /\ c = 0)
                \/ (a = 0 /\ b = 1 /\ c = 0)
                \/ (a = 0 /\ b = 0 /\ c = 1).
Proof. lia. Qed.

Lemma unique_found_here
  {a b} :
  1 + a + b = 1 -> a = 0 /\ b = 0.
Proof. lia. Qed.

Lemma absent_nowhere
  {a b c} :
  a + b + c = 0 <-> a = 0 /\ b = 0 /\ c = 0.
Proof. lia. Qed.

Lemma exists_somewhere
  {a b c} :
  a + b + c ≥ 1 <-> a ≥ 1 \/ b ≥ 1 \/ c ≥ 1.
Proof. lia. Qed.

(** [tree_unique] is defined by [count_nodes].
    [tree_contains] is defined by [exists_node].
    Here are some lemmas that relate the two. *)
Lemma unique_exists {tr tg} :
  tree_unique tg tr ->
  tree_contains tg tr.
Proof.
  rewrite /tree_unique /tree_count_tg.
  induction tr as [|data ? IHtr1 ? IHtr2]; simpl; [discriminate|].
  destruct (decide (itag data = tg)).
  - rewrite bool_decide_eq_true_2; [auto|assumption].
  - rewrite bool_decide_eq_false_2; [|assumption].
    simpl.
    intro Somewhere.
    right.
    destruct (unique_somewhere Somewhere) as [[]|[]].
    + left. apply IHtr1. assumption.
    + right. apply IHtr2. assumption.
Qed.

Lemma count_gt0_exists {tr tg} :
  tree_count_tg tg tr >= 1 <->
  tree_contains tg tr.
Proof.
  induction tr as [|data ? IHtr1 ? IHtr2]; simpl; [lia|].
  rewrite exists_somewhere. 
  rewrite IHtr1.
  rewrite IHtr2.
  destruct (decide (IsTag tg data)) as [Tg|nTg].
  - rewrite bool_decide_eq_true_2; [|assumption].
    apply ZifyClasses.or_morph; [split; auto|].
    reflexivity.
  - rewrite bool_decide_eq_false_2; [|assumption].
    apply ZifyClasses.or_morph; [split; intro; [lia|contradiction]|].
    reflexivity.
Qed.

Lemma count_0_not_exists tr tg :
  tree_count_tg tg tr = 0
  <-> ~tree_contains tg tr.
Proof.
  rewrite /tree_count_tg.
  induction tr as [|data ? IHtr1 ? IHtr2]; simpl; [tauto|].
  split.
  - intro Nowhere.
    destruct (proj1 absent_nowhere Nowhere) as [?[??]].
    destruct (decide (itag data = tg)).
    + rewrite bool_decide_eq_true_2 in Nowhere; [|assumption].
      simpl in *; discriminate.
    + intros [|[|]].
      * contradiction.
      * apply IHtr1; assumption.
      * apply IHtr2; assumption.
  - intro nEx.
    apply absent_nowhere.
    split; [|split].
    + destruct (decide (itag data = tg)).
      * exfalso. apply nEx. auto.
      * rewrite bool_decide_eq_false_2; auto.
    + apply IHtr1. auto.
    + apply IHtr2. auto.
Qed.

(** [tree_item_determined] is defined by a [forall_nodes].
    We can similarly relate it to predicates derived from [count_nodes]. *)
Lemma absent_determined tr tg :
  tree_count_tg tg tr = 0 ->
  forall it, tree_item_determined tg it tr.
Proof.
  induction tr as [|data ? IHtr1 ? IHtr2]; simpl; [auto|].
  rewrite absent_nowhere.
  intros [Absent0 [Absent1 Absent2]] it.
  split; [|split].
  + intro. rewrite bool_decide_eq_true_2 in Absent0; [discriminate|assumption].
  + apply IHtr1. assumption.
  + apply IHtr2. assumption.
Qed.

Lemma unique_lookup tr tg :
  tree_unique tg tr ->
  exists it, tree_item_determined tg it tr.
Proof.
  rewrite /tree_unique.
  induction tr as [|data ? IHtr1 ? IHtr2]; simpl; [intro; discriminate|].
  destruct (decide (IsTag tg data)).
  - rewrite bool_decide_eq_true_2; [|assumption].
    intro Found. destruct (unique_found_here Found).
    exists data; split; [|split].
    + tauto.
    + apply absent_determined. assumption.
    + apply absent_determined. assumption.
  - rewrite bool_decide_eq_false_2; [|assumption].
    simpl.
    intro Find. destruct (unique_somewhere Find) as [[Found ?]|[Found ?]].
    + destruct (IHtr1 Found) as [it ?].
      exists it; split; [|split].
      * tauto.
      * assumption.
      * apply absent_determined. assumption.
    + destruct (IHtr2 Found) as [it ?].
      exists it; split; [|split].
      * tauto.
      * apply absent_determined. assumption.
      * assumption.
Qed.

Lemma exists_determined_exists tr tg it :
  tree_contains tg tr ->
  tree_item_determined tg it tr ->
  exists_node (eq it) tr.
Proof.
  move=> Contains Det.
  induction tr; simpl in *; auto.
  destruct Det as [?[??]].
  destruct Contains as [?|[?|?]].
  - left; symmetry; auto.
  - right; left; auto.
  - right; right; auto.
Qed.

(** Some of the most important lemmas here.
    They characterizes insertion of a child node in terms of its relationship
    with other nodes. If you insert [n'] as a child of [n]...
    then in the resulting tree [n'] is a child of [n]!
    Not a groundbreaking statement, but necessary due to our representation
    of trees. *)
Lemma insert_eqv_strict_rel t t' (ins:item) (tr:tree item) (search:item -> Prop)
  {search_dec:forall it, Decision (search it)} :
  ~IsTag t ins ->
  ~IsTag t' ins ->
  StrictParentChildIn t t' tr <-> StrictParentChildIn t t' (insert_child_at tr ins search).
Proof.
  intros Nott Nott'; unfold ParentChildIn.
  induction tr as [|data ? IHtr1 ? IHtr2]; simpl; auto.
  destruct (decide (search data)).
  + rewrite IHtr1; clear IHtr1. rewrite IHtr2; clear IHtr2.
    simpl.
    split; intro Hyp.
    - destruct Hyp as [Hyp0 [Hyp1 Hyp2]].
      try repeat split; auto.
      intro H; right; left. eapply insert_preserves_exists; auto.
    - destruct Hyp as [Hyp0 [Hyp1 [Hyp21 [Hyp22 _]]]].
      try repeat split; auto.
      intro H; destruct (Hyp0 H) as [|[|]]; [contradiction| |contradiction].
      eapply insert_false_infer_exists; eauto.
  + rewrite IHtr1; clear IHtr1. rewrite IHtr2; clear IHtr2.
    simpl.
    split; intro Hyp.
- destruct Hyp as [Hyp0 [Hyp1 Hyp2]].
  try repeat split; auto.
  intro H; auto.
  apply insert_preserves_exists; auto.
- destruct Hyp as [Hyp0 [Hyp1 Hyp2]].
  try repeat split; auto.
  intro H; auto.
  eapply insert_false_infer_exists; eauto.
Qed.

Lemma insert_eqv_rel t t' (ins:item) (tr:tree item) (search:item -> Prop)
  {search_dec:forall it, Decision (search it)} :
  ~IsTag t ins ->
  ~IsTag t' ins ->
  ParentChildIn t t' tr <-> ParentChildIn t t' (insert_child_at tr ins search).
Proof.
  move=> ??.
  split; intro Hyp.
  all: destruct Hyp as [Eq|Strict]; [left; assumption|right].
  - erewrite <- insert_eqv_strict_rel; assumption.
  - erewrite <- insert_eqv_strict_rel in Strict; assumption.
Qed.

Lemma insert_eqv_imm_rel t t' (ins:item) (tr:tree item) (search:item -> Prop)
  {search_dec:forall it, Decision (search it)} :
  ~IsTag t ins ->
  ~IsTag t' ins ->
  ImmediateParentChildIn t t' tr <-> ImmediateParentChildIn t t' (insert_child_at tr ins search).
Proof.
  intros Nott Nott'; unfold ImmediateParentChildIn.
  induction tr as [|data ? IHtr1 ? IHtr2]; simpl; auto.
  destruct (decide (search data)).
  + rewrite IHtr1; clear IHtr1. rewrite IHtr2; clear IHtr2.
    simpl.
    split; intro Hyp.
    - destruct Hyp as [Hyp0 [Hyp1 Hyp2]].
      try repeat split; auto.
      intro H; right. rewrite <- exists_sibling_insert. auto.
    - destruct Hyp as [Hyp0 [Hyp1 [Hyp21 [Hyp22 _]]]].
      try repeat split; auto.
      intro H; destruct (Hyp0 H) as [|]; [contradiction|].
      by eapply exists_sibling_insert.
  + rewrite IHtr1; clear IHtr1. rewrite IHtr2; clear IHtr2.
    simpl.
    split; intro Hyp.
- destruct Hyp as [Hyp0 [Hyp1 Hyp2]].
  try repeat split; auto.
  intro H; auto.
  rewrite <- exists_sibling_insert. auto.
- destruct Hyp as [Hyp0 [Hyp1 Hyp2]].
  try repeat split; auto.
  intro H; auto.
  erewrite exists_sibling_insert. eauto.
Qed.

Lemma insert_produces_StrictParentChild t (ins:item) (tr:tree item) :
  ~IsTag t ins ->
  StrictParentChildIn t ins.(itag) (insert_child_at tr ins (IsTag t)).
Proof.
  intro Nott.
  unfold StrictParentChildIn.
  induction tr as [|data ????]; simpl; auto.
  destruct (decide (IsTag t data)) eqn:Found; simpl.
  - try repeat split; auto.
  - try repeat split; auto.
    intro H; contradiction.
Qed.

Lemma insert_produces_ParentChild t tg (ins:item) (tr:tree item) :
  IsTag tg ins ->
  tg ≠ t ->
  ParentChildIn t tg (insert_child_at tr ins (IsTag t)).
Proof.
  move=> Tg Ne.
  right.
  assert (~IsTag t ins) as NotTg by (intro H; rewrite <- H in Ne; rewrite <- Tg in Ne; contradiction).
  pose proof (insert_produces_StrictParentChild _ _ tr NotTg) as H.
  rewrite Tg in H; assumption.
Qed.

Lemma insert_produces_ImmediateParentChild t (ins:item) (tr:tree item) :
  ~IsTag t ins ->
  ImmediateParentChildIn t ins.(itag) (insert_child_at tr ins (IsTag t)).
Proof.
  intro Nott.
  unfold StrictParentChildIn.
  induction tr as [|data ????]; simpl; auto.
  destruct (decide (IsTag t data)) eqn:Found; simpl.
  - try repeat split; auto.
  - try repeat split; auto.
    intro H; contradiction.
Qed.

Lemma ImmediateParentChild_of_insert_is_parent t t' (ins:item) (tr:tree item) :
  ¬ exists_node (IsTag (ins.(itag))) tr ->
  exists_node (IsTag t') tr ->
  t ≠ ins.(itag) →
  ImmediateParentChildIn t' ins.(itag) (insert_child_at tr ins (IsTag t)) ->
  t = t'.
Proof.
  intros H1 H2 Htag HIPCI.
  induction tr as [|it tr1 IHtr1 tr2 IHtr2].
  { by simpl in H2. }
  destruct (decide (exists_node (IsTag t') tr1)) as [Ht1|Hnt1].
  { eapply IHtr1. 2: done. 1: intros H; eapply H1; simpl; tauto.
    simpl in HIPCI. destruct (decide (itag it = t)); simpl in HIPCI.
    all: eapply HIPCI. }
  destruct (decide (exists_node (IsTag t') tr2)) as [Ht2|Hnt2].
  { eapply IHtr2. 2: done. 1: intros H; eapply H1; simpl; tauto.
    simpl in HIPCI. destruct (decide (itag it = t)); simpl in HIPCI.
    all: eapply HIPCI. }
  simpl in H2.
  destruct H2 as [Heq|[H2|H2]]. 2-3: done.
  simpl in HIPCI.
  destruct (decide (itag it = t)) as [|Hne]; first congruence.
  simpl in HIPCI. destruct HIPCI as (HIPCI&_&_).
  clear IHtr1 IHtr2.
  specialize (HIPCI Heq). clear Hnt1. exfalso.
  assert (¬ exists_node (IsTag (itag ins)) tr2) as H1tr2.
  { simpl in H1|-*. tauto. }
  clear H1.

  induction tr2 as [|it' tr1' IHtr1' tr2' IHtr2'].
  { simpl in HIPCI. done. }
  simpl in HIPCI. destruct (decide (itag it' = t)) as [Heq'|Hne'].
  all: simpl in HIPCI.
  - destruct HIPCI as [|HIPCI]; first congruence.
    eapply IHtr1'; first done. all: simpl in H1tr2,Hnt2; tauto.
  - destruct HIPCI as [Hcc|HIPCI].
    { eapply H1tr2. by left. } 
    eapply IHtr1'; first done. all: simpl in H1tr2,Hnt2; tauto.
Qed.

(** Recall:
    [map_nodes : (X -> Y) -> tree X -> tree Y] applies a function to each node.
    [join_nodes : tree (option X) -> option (tree X)] collects failures.

    Our semantics are mostly expressed as a combination of these two,
    in the form of [join_nodes (map_nodes faillible_function tree)].
    Therefore it is not surprising that these characterizations of
    [join]+[map] are also among the most important lemmas here. *)
Lemma join_map_eqv_strict_rel t t' (tr tr':tree item) :
  forall fn,
  (forall it it', fn it = Some it' -> itag it = itag it') ->
  join_nodes (map_nodes fn tr) = Some tr' ->
  StrictParentChildIn t t' tr <-> StrictParentChildIn t t' tr'.
Proof.
  intros fn FnPreservesTag Success.
  generalize dependent tr'.
  unfold StrictParentChildIn.
  induction tr as [|data ? IHtr1 ? IHtr2]; intros tr' Success; simpl in *.
  - inversion Success; auto.
  - destruct (destruct_joined _ _ _ _ Success) as [data' [tr1' [tr2' [EqTr' [EqData' [EqTr1' EqTr2']]]]]].
    rewrite IHtr1; [|eapply EqTr1'].
    rewrite IHtr2; [|eapply EqTr2'].
    subst; simpl.
    split; intro H; destruct H as [H[??]]; try repeat split; try assumption.
    all: intro Hyp.
    + rewrite <- join_map_preserves_exists.
      * apply H. erewrite FnPreservesTag; eassumption.
      * intros; subst. erewrite FnPreservesTag; eauto.
      * apply EqTr2'.
    + rewrite join_map_preserves_exists.
      * apply H. erewrite <- FnPreservesTag; eassumption.
      * intros; subst. erewrite FnPreservesTag; eauto.
      * apply EqTr2'.
Qed.

Lemma join_map_eqv_rel
  {t t' tr tr' fn}
  (PreservesTags : forall it it', fn it = Some it' -> itag it = itag it')
  (Success : join_nodes (map_nodes fn tr) = Some tr')
  : ParentChildIn t t' tr <-> ParentChildIn t t' tr'.
Proof.
  unfold ParentChildIn.
  rewrite join_map_eqv_strict_rel; eauto.
Qed.

Lemma join_map_eqv_imm_rel
  {t t' tr tr' fn}
  (PreservesTags : forall it it', fn it = Some it' -> itag it = itag it')
  (Success : join_nodes (map_nodes fn tr) = Some tr')
  : ImmediateParentChildIn t t' tr <-> ImmediateParentChildIn t t' tr'.
Proof.
  generalize dependent tr'.
  unfold ImmediateParentChildIn.
  induction tr as [|data ? IHtr1 ? IHtr2]; intros tr' Success; simpl in *.
  - inversion Success; auto.
  - destruct (destruct_joined _ _ _ _ Success) as [data' [tr1' [tr2' [EqTr' [EqData' [EqTr1' EqTr2']]]]]].
    rewrite IHtr1; [|eapply EqTr1'].
    rewrite IHtr2; [|eapply EqTr2'].
    subst; simpl.
    split; intros (H&?&?); split_and!; try done.
    all: intro Hyp.
    + rewrite <- join_map_preserves_exists_sibling.
      * apply H. erewrite PreservesTags; eassumption.
      * intros; subst. erewrite PreservesTags; eauto.
      * apply EqTr2'.
    + rewrite join_map_preserves_exists_sibling.
      * apply H. erewrite <- PreservesTags; eassumption.
      * intros; subst. erewrite PreservesTags; eauto.
      * apply EqTr2'.
Qed.

Lemma Immediate_is_StrictChildTag tg tr :
  HasImmediateChildTag tg tr →
  HasStrictChildTag tg tr.
Proof.
  destruct tr as ((data&tl)&tr). simpl.
  by eapply exists_sibling_exists_node.
Qed.

Lemma Immediate_is_StrictParentChild t1 t2 (tr:tree item) :
  ImmediateParentChildIn t1 t2 tr →
  StrictParentChildIn t1 t2 tr.
Proof.
  intros Himm.
  unfold StrictParentChildIn, ImmediateParentChildIn in *.
  eapply every_subtree_eqv_universal.
  intros br H1 H2.
  eapply Immediate_is_StrictChildTag.
  eapply every_subtree_eqv_universal in Himm; try done.
  by apply Himm.
Qed.

Lemma StrictParentChild_transitive t t' t'' (tr:tree item) :
  StrictParentChildIn t t' tr ->
  StrictParentChildIn t' t'' tr ->
  StrictParentChildIn t t'' tr.
Proof.
  rewrite /StrictParentChildIn /HasStrictChildTag.
  induction tr as [|?? IHtr1 tr2 IHtr2]; simpl; auto.
  intros [Condtt' [Reltt'1 Reltt'2]] [Condt't'' [Relt't''1 Relt't''2]].
  split; auto.
  intro H.
  clear Relt't''1 Reltt'1 IHtr1 IHtr2.
  pose proof (Condtt' H) as Ex'.
  clear Condtt' H Condt't'' Reltt'2.
  (* End of step 1: we have found a t'. Now look for a t''. *)
  induction tr2; [destruct Ex'|].
  destruct Relt't''2 as [IfHere [IfLeft IfRight]].
  destruct Ex' as [Here | [Left | Right]].
  - simpl in *; right; right; auto.
  - right; left; auto.
  - right; right; auto.
Qed.

Lemma ParentChild_transitive t t' t'' (tr:tree item) :
  ParentChildIn t t' tr ->
  ParentChildIn t' t'' tr ->
  ParentChildIn t t'' tr.
Proof.
  unfold ParentChildIn.
  destruct (decide (t = t')); [subst; tauto|].
  destruct (decide (t' = t'')); [subst; tauto|].
  intros Ptt' Pt't''.
  destruct Ptt'; [contradiction|].
  destruct Pt't''; [contradiction|].
  right.
  eapply StrictParentChild_transitive; eauto.
Qed.

Lemma insert_produces_StrictParentChild_transitive t t' (ins:item) (tr:tree item) :
  ~IsTag t ins ->
  ~IsTag t' ins ->
  StrictParentChildIn t t' tr ->
  StrictParentChildIn t ins.(itag) (insert_child_at tr ins (IsTag t')).
Proof.
  intros Nott Nott' Ptt'.
  apply (StrictParentChild_transitive t t' ins.(itag)).
  - apply insert_eqv_strict_rel; auto.
  - apply insert_produces_StrictParentChild; auto.
Qed.


Lemma insert_produces_minimal_ParentChild (t t':tag) (ins:item) (tr:tree item) :
  ~IsTag t ins ->
  ~IsTag t' ins ->
  ~t = t' ->
  ~tree_contains ins.(itag) tr ->
  StrictParentChildIn t ins.(itag) (insert_child_at tr ins (IsTag t')) ->
  StrictParentChildIn t t' tr.
Proof.
  intros Nott Nott' Diff Absent Pins.
  unfold tree_contains in Absent.
  rewrite <- every_not_eqv_not_exists in Absent.
  induction tr as [|data ? IHtr1 ? IHtr2]; simpl; auto.
  simpl in Pins; destruct (decide (IsTag t' data)) as [Tg'|].
  all: destruct Absent as [Absent0 [Absent1 Absent2]].
  all: destruct Pins as [Pins0 [Pins1 Pins2]].
  all: try repeat split.
  - intro Contra; exfalso.
    subst; contradiction.
  - apply IHtr1; assumption.
  - apply IHtr2; [|destruct Pins2 as [?[??]]]; assumption.
  - intro Tg. simpl in Pins0.
    eapply exists_insert_requires_parent.
    + exact Absent2.
    + apply Pins0. exact Tg.
  - apply IHtr1; assumption.
  - apply IHtr2; assumption.
Qed.

Lemma inserted_empty_children (t:tag) (ins:item) (tr:tree item) :
  ~tree_contains ins.(itag) tr ->
  every_subtree (fun br => HasRootTag ins.(itag) br -> empty_children br) (insert_child_at tr ins (IsTag t)).
Proof.
  move=> Fresh.
  unfold tree_contains in Fresh.
  rewrite <- every_not_eqv_not_exists in Fresh.
  induction tr as [|data ? IHtr1 ? IHtr2]; simpl; auto.
  destruct (decide (IsTag t data)); simpl in *.
  all: destruct Fresh as [Fresh0 [Fresh1 Fresh2]].
  + try repeat split.
    - intro; contradiction.
    - apply IHtr1; exact Fresh1.
    - apply IHtr2; exact Fresh2.
  + try repeat split.
    - intro; contradiction.
    - apply IHtr1; exact Fresh1.
    - apply IHtr2; exact Fresh2.
Qed.

Lemma inserted_determined (tgp tg:tag) (ins:item) (tr:tree item) :
  IsTag tg ins ->
  ~tree_contains tg tr ->
  tree_item_determined tg ins (insert_child_at tr ins (IsTag tgp)).
Proof.
  intros Tg Fresh.
  unfold tree_item_determined.
  unfold tree_contains in Fresh; rewrite <- every_not_eqv_not_exists in Fresh.
  induction tr as [|data ? IHtr1 ? IHtr2]; simpl in *; auto.
  destruct Fresh as [?[??]].
  destruct (decide (IsTag tgp data)).
  - try repeat split; [|apply IHtr1; assumption|apply IHtr2; assumption].
    simpl; intro; contradiction.
  - try repeat split; [|apply IHtr1; assumption|apply IHtr2; assumption].
    simpl; intro; contradiction.
Qed.

Lemma inserted_count_sum (tgp tg : tag) (ins : item) (tr : tree item) :
  IsTag tg ins ->
  tg ≠ tgp ->
  tree_count_tg tg (insert_child_at tr ins (IsTag tgp))
  = tree_count_tg tg tr + tree_count_tg tgp tr.
Proof.
  intros Tg Ne.
  induction tr as [|data ? IHtr1 ? IHtr2]; simpl; [auto|].
  destruct (decide _) as [Tgp|nTgp]; simpl.
  + rewrite IHtr1.
    rewrite IHtr2.
    rewrite (bool_decide_eq_true_2 _ Tgp).
    assert (~IsTag tg data) as nTgd. { intro Tgd. apply Ne. congruence. }
    rewrite (bool_decide_eq_false_2 _ nTgd).
    rewrite (bool_decide_eq_true_2 _ Tg).
    lia.
  + rewrite IHtr1.
    rewrite IHtr2.
    rewrite (bool_decide_eq_false_2 _ nTgp).
    lia.
Qed.

Lemma inserted_unique (tgp tg : tag) (ins : item) (tr : tree item) :
  IsTag tg ins ->
  ~tree_contains tg tr ->
  tree_unique tgp tr ->
  tree_unique tg (insert_child_at tr ins (IsTag tgp)).
Proof.
  intros Tg nEx Unq.
  rewrite /tree_unique in Unq |- *.
  rewrite <- count_0_not_exists in nEx.
  rewrite inserted_count_sum.
  + lia.
  + assumption.
  + intro Eq. rewrite Eq in nEx. congruence.
Qed.

Lemma not_strict_parent_of_self
  {tg tr} :
  tree_contains tg tr ->
  ~StrictParentChildIn tg tg tr.
Proof.
  rewrite /StrictParentChildIn.
  induction tr as [|data ? IHtr1 ? IHtr2]; simpl; intros Ex; [tauto|].
  intros [Here [Sub1 Sub2]].
  destruct Ex as [Ex0|[Ex1|Ex2]].
  + apply IHtr2; [|assumption]. apply Here. assumption.
  + apply IHtr1; [|assumption]. apply Ex1.
  + apply IHtr2; [|assumption]. apply Ex2.
Qed.

Lemma inserted_not_strict_parent (t:tag) (ins:item) (tr:tree item) :
  tree_contains t tr ->
  ~tree_contains ins.(itag) tr ->
  forall t',
  ~StrictParentChildIn ins.(itag) t' (insert_child_at tr ins (IsTag t)).
Proof.
  move=> ContainsParent Fresh t' Rel.
  assert (~t = ins.(itag)) as Net by (intro; subst; contradiction).
  assert (~t' = ins.(itag)) as Net'.
  { intro; subst; eapply not_strict_parent_of_self; last done; eapply insert_true_produces_exists; done. }
  unfold ParentChildIn in Rel.
  pose proof (inserted_empty_children t ins tr Fresh) as Contra.
  clear Fresh.
  induction tr as [|data ? IHtr1 ? IHtr2]; simpl in *; try contradiction.
  destruct (decide (IsTag t data)).
  all: destruct ContainsParent as [Parent0 | [Parent1 | Parent2]].
  - simpl in Rel.
    destruct Rel as [_ [_ [Bad _]]]; apply Net'.
    destruct Bad; reflexivity.
  - apply IHtr1.
    * auto.
    * destruct Rel as [Rel0 [Rel1 Rel2]]; auto.
    * destruct Contra as [Contra0 [Contra1 Contra2]]; auto.
  - apply IHtr2.
    * auto.
    * destruct Rel as [Rel0 [Rel1 [Rel20 [Rel21 Rel22]]]]; auto.
    * destruct Contra as [Contra0 [Contra1 [Contra20 [Contra21 Contra22]]]]; auto.
  - contradiction.
  - apply IHtr1.
    * auto.
    * destruct Rel as [Rel0 [Rel1 Rel2]]; auto.
    * destruct Contra as [Contra0 [Contra1 Contra2]]; auto.
  - apply IHtr2.
    * auto.
    * destruct Rel as [Rel0 [Rel1 Rel2]]; auto.
    * destruct Contra as [Contra0 [Contra1 Contra2]]; auto.
Qed.

Lemma create_child_isSome tr tgp tgc pk im rk cid :
  forall cids tr',
  create_child cids tgp tgc pk im rk cid tr = Some tr' -> ∃ x,
    create_new_item tgc pk im rk cid = Some x ∧
    tr' = insert_child_at tr x (IsTag tgp).
Proof.
  intros cc tr' (x&Hx&[= Hxx])%bind_Some.
  by exists x.
Qed.

Lemma new_item_has_tag tg pk im rk cid it :
  create_new_item tg pk im rk cid = Some it →
  IsTag tg it.
Proof.
  intros (x&Hx&[= <-])%bind_Some. done.
Qed.

Lemma insertion_contains tr tgp tgc pk im rk cid :
  forall cids tr',
  tree_contains tgp tr ->
  create_child cids tgp tgc pk im rk cid tr = Some tr' ->
  tree_contains tgc tr'.
Proof.
  move=> ? tr' ContainsParent CreateChild.
  unfold tree_contains in *.
  pose proof (create_child_isSome tr tgp tgc _ _ _ _ _ _ CreateChild) as (it&Hit&Insert).
  rewrite Insert.
  apply insert_true_produces_exists.
  - by eapply new_item_has_tag.
  - exact ContainsParent.
Qed.

Lemma insertion_order_nonstrictparent tr tg tg' :
  ~tree_contains tg tr ->
  forall tgp cids pk im rk cid tr',
  tree_contains tgp tr ->
  create_child cids tgp tg pk im rk cid tr = Some tr' ->
  ~StrictParentChildIn tg tg' tr'.
Proof.
  move=> Fresh tgp ????? tr' ParentPresent Insert2 Contra.
  pose proof (create_child_isSome tr tgp tg _ _ _ _ _ _ Insert2) as (it&<-%new_item_has_tag&->).
  eapply inserted_not_strict_parent with (ins := it).
  - apply ParentPresent.
  - eapply Fresh.
  - apply Contra.
Qed.

Lemma insertion_order_nonparent tr tg tg' :
  tree_contains tg' tr ->
  ~tree_contains tg tr ->
  forall tgp cids pk im rk cid tr',
  tree_contains tgp tr ->
  create_child cids tgp tg pk im rk cid tr = Some tr' ->
  ~ParentChildIn tg tg' tr'.
Proof.
  intros; intro Related.
  destruct Related.
  - subst; contradiction.
  - eapply (insertion_order_nonstrictparent _ tg tg'); eauto.
Qed.

Lemma tree_determined_specifies_tag tr tg it :
  tree_contains tg tr ->
  tree_item_determined tg it tr ->
  itag it = tg.
Proof.
  rewrite /tree_contains /tree_item_determined.
  rewrite exists_node_eqv_existential.
  rewrite every_node_eqv_universal.
  intros [n [Exn Tgn]] Every.
  rewrite <- (Every n); auto.
Qed.


Lemma create_child_determined tr tgp pk im rk cid tg :
  tree_contains tgp tr ->
  ~tree_contains tg tr ->
  forall cids tr',
  create_child cids tgp tg pk im rk cid tr = Some tr' ->
  ( ∃ it, create_new_item tg pk im rk cid = Some it ∧
    tree_contains tg tr' ∧
    tree_item_determined tg it tr'
  ).
Proof.
  intros ContainsTgp FreshTg cids tr' CreateChild.
  pose proof (create_child_isSome _ _ _ _ _ _ _ _ _ CreateChild) as (it&Hit&Insertion).
  exists it. split; first done.
  subst tr'.
  assert (itag it = tg) as TgIns by by eapply new_item_has_tag.
  rewrite <- TgIns.
  split.
  - eapply insert_true_produces_exists; [auto|assumption].
  - eapply inserted_determined; simpl; by subst tg.
Qed.

Lemma create_new_item_uniform_perm tg it perm pk im rk cid z :
  retag_perm pk im rk = Some perm →
  create_new_item tg pk im rk cid = Some it →
  item_lazy_perm_at_loc it z = {|
    initialized := PermLazy;
    perm := perm
  |}.
Proof.
  unfold item_lazy_perm_at_loc, item_lookup.
  unfold create_new_item; simpl.
  unfold init_perms.
  intros ->. rewrite /=.
  intros [= <-]. rewrite /=.
  rewrite lookup_empty; simpl.
  reflexivity.
Qed.

(*
Lemma create_new_item_perm_prop prop tg pk im rk cid z :
  prop (pointer_kind_to_perm pk) ->
  prop (perm (item_lazy_perm_at_loc (create_new_item tg pk im rk cid) z)).
Proof. rewrite create_new_item_uniform_perm; simpl; tauto. Qed.

Lemma create_new_item_prot_prop prop tg pk im rk cid :
  let s := pointer_kind_to_strength pk in
  let prot := retag_kind_to_prot cid rk s in
  prop (prot) ->
  prop (iprot (create_new_item tg pk im rk cid)).
Proof. simpl; tauto. Qed. *)

Lemma create_child_preserves_determined tg it tr tr':
  forall tg' cids tgp pk im rk cid,
  tg ≠ tg' ->
  tree_item_determined tg it tr ->
  create_child cids tgp tg' pk im rk cid tr = Some tr' ->
  tree_item_determined tg it tr'.
Proof.
  move=> ??????? Ne.
  rewrite /tree_item_determined every_node_eqv_universal every_node_eqv_universal.
  intros Unq (itx&Hit&->)%create_child_isSome.
  intro n; specialize Unq with n.
  move=> Unq' Tg; apply Unq; [|assumption].
  eapply insert_false_infer_exists; [|exact Unq'].
  assert (forall it it', itag it ≠ itag it' -> it ≠ it') as Deterministic. {
    clear; intros it it'; destruct it; destruct it'; simpl.
    intros NEq Eq; injection Eq; intros; contradiction.
  } apply Deterministic.
  erewrite (new_item_has_tag _ _ _ _ _ _ Hit).
  rewrite Tg.
  assumption.
Qed.


Lemma create_child_preserves_count tg tr tr':
  forall tg' cids tgp pk im rk cid,
  tg ≠ tg' ->
  create_child cids tgp tg' pk im rk cid tr = Some tr' ->
  tree_count_tg tg tr = tree_count_tg tg tr'.
Proof.
  intros tg' cids tgp pk im rk cid Ne.
  induction tr as [|data ? IHtr1 ? IHtr2] in tr'|-*; simpl in *; intros (it&Hit&->)%create_child_isSome.
  1: reflexivity.
  unfold create_child in IHtr1,IHtr2.
  rewrite Hit /= in IHtr1,IHtr2.
  destruct (decide (IsTag tgp data)).
  + simpl.
    assert (itag it = tg') as <- by by eapply new_item_has_tag.
    assert (~IsTag tg it) as NotTg by done.
    erewrite IHtr1; [|reflexivity].
    erewrite IHtr2; [|reflexivity].
    rewrite decide_True // /=.
    rewrite (bool_decide_eq_false_2 _ NotTg).
    lia.
  + simpl.
    erewrite IHtr1; [|reflexivity].
    erewrite IHtr2; [|reflexivity].
    rewrite decide_False // /=.
Qed.

Lemma tree_determined_unify
  {tg tr it it'}
  (Ex : tree_contains tg tr)
  (Unq : tree_item_determined tg it tr)
  (Unq' : tree_item_determined tg it' tr)
  : it = it'.
Proof.
  rewrite /tree_item_determined /tree_contains in Ex, Unq, Unq'.
  repeat rewrite every_node_eqv_universal in Ex, Unq, Unq'.
  repeat rewrite exists_node_eqv_existential in Ex, Unq, Unq'.
  destruct Ex as [it0 [??]].
  assert (it0 = it) by (apply Unq; assumption).
  assert (it0 = it') by (apply Unq'; assumption).
  subst; reflexivity.
Qed.

Lemma tree_apply_access_only_cares_about_rel
  {tr} {fn : call_id_set -> rel_pos -> Z * nat -> item -> option item} {cids access_tag range}
  {rel1 rel2 : tag -> tag -> rel_pos}
  (Agree : forall tg tg', rel1 tg tg' = rel2 tg tg')
  : join_nodes (map_nodes (fun it => fn cids (rel1 access_tag it.(itag)) range it) tr)
  = join_nodes (map_nodes (fun it => fn cids (rel2 access_tag it.(itag)) range it) tr).
Proof.
  induction tr as [|data sibling IHsibling child IHchild]; [simpl; reflexivity|].
  simpl.
  rewrite IHsibling; clear IHsibling.
  rewrite IHchild; clear IHchild.
  unfold rel_dec.
  f_equal. f_equal.
  apply Agree.
Qed.

Lemma same_parent_childs_agree
  {tr1 tr2}
  : (forall tg tg', ParentChildIn tg tg' tr1 <-> ParentChildIn tg tg' tr2) ->
    (forall tg tg', ImmediateParentChildIn tg tg' tr1 <-> ImmediateParentChildIn tg tg' tr2) ->
  (forall tg tg', rel_dec tr1 tg tg' = rel_dec tr2 tg tg').
Proof.
  intros SameRel SameImmRel tg tg'.
  rewrite /rel_dec.
  destruct (decide (ParentChildIn _ _ _)) as [R1|R1].
  all: destruct (decide (ParentChildIn _ _ _)) as [R1'|R1'].
  all: destruct (decide (ParentChildIn _ _ _)) as [R2|R2].
  all: destruct (decide (ParentChildIn _ _ _)) as [R2'|R2'].
  all: try reflexivity.
  all: rewrite <- SameRel in R2'; auto; try contradiction.
  all: rewrite <- SameRel in R2; auto; try contradiction.
  all: erewrite decide_ext; last apply SameImmRel.
  all: done.
Qed.

Lemma cousins_different
  {tr} tg1 tg2 :
  rel_dec tr tg1 tg2 = Foreign Cousin ->
  tg1 ≠ tg2.
Proof.
  rewrite /rel_dec.
  destruct (decide _), (decide _) as [|nRel].
  all: try congruence.
  intros _ Eq. subst.
  apply nRel.
  left. reflexivity.
Qed.

Lemma exists_subtree_increasing
  {X} {tr : tree X} {P Q} :
  (forall br, P br -> Q br) ->
  exists_subtree P tr ->
  exists_subtree Q tr.
Proof.
  induction tr as [|?? IHtr1 ? IHtr2]; simpl; [tauto|].
  intros Impl [Here|[Ex1|Ex2]].
  - left. apply Impl. assumption.
  - right. left. apply IHtr1; assumption.
  - right. right. apply IHtr2; assumption.
Qed.


Lemma find_unique_subtree
  {tr tg} :
  tree_unique tg tr ->
  exists br,
    exists_subtree (eq br) tr
    /\ IsTag tg (root br).
Proof.
  induction tr as [|data tr1 IHtr1 tr2 IHtr2]; simpl; [rewrite /tree_unique /=; discriminate|].
  intros Unq.
  rewrite /tree_unique /= in Unq.
  destruct (unique_somewhere_3way Unq) as [ [H0 _] |[ [_ [H1 _]] | [_ [_ H2]] ]].
  - exists (data, tr1, tr2).
    split; [left; reflexivity|].
    simpl.
    destruct (decide (IsTag tg data)); [assumption|].
    rewrite bool_decide_eq_false_2 in H0; [discriminate|assumption].
  - destruct (IHtr1 H1) as [br1 [??]].
    exists br1. split; [|assumption]. right; left; assumption.
  - destruct (IHtr2 H2) as [br2 [??]].
    exists br2. split; [|assumption]. right; right; assumption.
Qed.

Lemma unique_only_one_subtree
  {tr tg br1 br2} :
  tree_unique tg tr ->
  exists_subtree (eq br1) tr ->
  exists_subtree (eq br2) tr ->
  IsTag tg (root br1) ->
  IsTag tg (root br2) ->
  br1 = br2.
Proof.
  induction tr as [|data tr1 IHtr1 tr2 IHtr2]; simpl; [tauto|].
  intros Unq Sub1 Sub2 Tg1 Tg2.
  destruct Sub1 as [Here1|[Sub11|Sub12]], Sub2 as [Here2|[Sub21|Sub22]].
  - (* easy *) congruence.
  - (* too many tags: one here, one in tr1 *)
    assert ((if has_tag tg data then 1 else 0) = 1). {
      rewrite bool_decide_eq_true_2; subst; auto.
    }
    assert (tree_count_tg tg tr1 ≥ 1). {
      rewrite count_gt0_exists.
      enough (exists_subtree (compose (IsTag tg) root) tr1) as Root.
      + rewrite -exists_node_iff_exists_root in Root. assumption.
      + eapply exists_subtree_increasing; [|eassumption].
        intros; subst. assumption.
    }
    rewrite /tree_unique /= in Unq.
    lia.
  - (* too many tags: one here, one in tr2 *)
    assert ((if has_tag tg data then 1 else 0) = 1). {
      rewrite bool_decide_eq_true_2; subst; auto.
    }
    assert (tree_count_tg tg tr2 ≥ 1). {
      rewrite count_gt0_exists.
      enough (exists_subtree (compose (IsTag tg) root) tr2) as Root.
      + rewrite -exists_node_iff_exists_root in Root. assumption.
      + eapply exists_subtree_increasing; [|eassumption].
        intros; subst. assumption.
    }
    rewrite /tree_unique /= in Unq.
    lia.
  - (* too many tags: one in tr1, one here *)
    assert ((if has_tag tg data then 1 else 0) = 1). {
      rewrite bool_decide_eq_true_2; subst; auto.
    }
    assert (tree_count_tg tg tr1 ≥ 1). {
      rewrite count_gt0_exists.
      enough (exists_subtree (compose (IsTag tg) root) tr1) as Root.
      + rewrite -exists_node_iff_exists_root in Root. assumption.
      + eapply exists_subtree_increasing; [|eassumption].
        intros; subst; reflexivity.
    }
    rewrite /tree_unique /= in Unq.
    lia.
  - (* recurse left *)
    assert (tree_count_tg tg tr1 ≥ 1). {
      rewrite count_gt0_exists.
      enough (exists_subtree (compose (IsTag tg) root) tr1) as Root.
      + rewrite -exists_node_iff_exists_root in Root. assumption.
      + eapply exists_subtree_increasing; [|eassumption].
        intros; subst. assumption.
    }
    rewrite /tree_unique /= in Unq.
    assert (tree_count_tg tg tr1 = 1) by lia.
    apply IHtr1; assumption.
  - (* too many tags: one in tr1, one in tr2 *)
    assert (tree_count_tg tg tr1 ≥ 1). {
      rewrite count_gt0_exists.
      enough (exists_subtree (compose (IsTag tg) root) tr1) as Root.
      + rewrite -exists_node_iff_exists_root in Root. assumption.
      + eapply exists_subtree_increasing; [|eassumption].
        intros; subst; reflexivity.
    }
    assert (tree_count_tg tg tr2 ≥ 1). {
      rewrite count_gt0_exists.
      enough (exists_subtree (compose (IsTag tg) root) tr2) as Root.
      + rewrite -exists_node_iff_exists_root in Root. assumption.
      + eapply exists_subtree_increasing; [|eassumption].
        intros; subst. assumption.
    }
    rewrite /tree_unique /= in Unq. lia.
  - (* too many tags: one in tr2, one here *)
    assert ((if has_tag tg data then 1 else 0) = 1). {
      rewrite bool_decide_eq_true_2; subst; auto.
    }
    assert (tree_count_tg tg tr2 ≥ 1). {
      rewrite count_gt0_exists.
      enough (exists_subtree (compose (IsTag tg) root) tr2) as Root.
      + rewrite -exists_node_iff_exists_root in Root. assumption.
      + eapply exists_subtree_increasing; [|eassumption].
        intros; subst. reflexivity.
    }
    rewrite /tree_unique /= in Unq.
    lia.
  - (* too many tags: one in tr2, one in tr1 *)
    assert (tree_count_tg tg tr1 ≥ 1). {
      rewrite count_gt0_exists.
      enough (exists_subtree (compose (IsTag tg) root) tr1) as Root.
      + rewrite -exists_node_iff_exists_root in Root. assumption.
      + eapply exists_subtree_increasing; [|eassumption].
        intros; subst. assumption.
    }
    assert (tree_count_tg tg tr2 ≥ 1). {
      rewrite count_gt0_exists.
      enough (exists_subtree (compose (IsTag tg) root) tr2) as Root.
      + rewrite -exists_node_iff_exists_root in Root. assumption.
      + eapply exists_subtree_increasing; [|eassumption].
        intros; subst. reflexivity.
    }
    rewrite /tree_unique /= in Unq. lia.
  - (* recurse right *)
    assert (tree_count_tg tg tr2 ≥ 1). {
      rewrite count_gt0_exists.
      enough (exists_subtree (compose (IsTag tg) root) tr2) as Root.
      + rewrite -exists_node_iff_exists_root in Root. assumption.
      + eapply exists_subtree_increasing; [|eassumption].
        intros; subst. assumption.
    }
    rewrite /tree_unique /= in Unq.
    assert (tree_count_tg tg tr2 = 1) by lia.
    apply IHtr2; assumption.
Qed.

Lemma unique_exists_iff_unique
  {tr prop} tg :
  tree_unique tg tr ->
  exists_subtree (fun br => IsTag tg (root br) /\ prop br) tr
  <-> every_subtree (fun br => IsTag tg (root br) -> prop br) tr.
Proof.
  intros Unq. split.
  - intros Ex.
    rewrite every_subtree_eqv_universal.
    rewrite exists_subtree_eqv_existential in Ex.
    intros br Sub Tg.
    destruct Ex as [br' [Ex' [Tg' Prop']]].
    assert (br = br'). { eapply unique_only_one_subtree; eauto. }
    subst. assumption.
  - intros All.
    rewrite every_subtree_eqv_universal in All.
    rewrite exists_subtree_eqv_existential.
    destruct (find_unique_subtree Unq) as [br [Sub Tg]].
    exists br.
    specialize (All br Sub Tg).
    split; last split; assumption.
Qed.

Lemma unique_found_branch_1
  {data tr1 tr2} tg :
  tree_unique tg (branch data tr1 tr2) ->
  tree_unique tg tr1 ->
  ~tree_contains tg tr2 /\ ~IsTag tg data.
Proof.
  rewrite /tree_unique.
  intros Unq Unq'.
  simpl in Unq.
  destruct (unique_somewhere_3way Unq) as [ [?[??]] |[ [H[??]] | [?[??]] ]]; [congruence| |congruence].
  split; first (rewrite <- count_0_not_exists; assumption).
  intro Tg.
  rewrite bool_decide_eq_true_2 in H; [|assumption].
  congruence.
Qed.

Lemma unique_found_branch_2
  {data tr1 tr2} tg :
  tree_unique tg (branch data tr1 tr2) ->
  tree_unique tg tr2 ->
  ~tree_contains tg tr1 /\ ~IsTag tg data.
Proof.
  rewrite /tree_unique.
  intros Unq Unq'.
  simpl in Unq.
  destruct (unique_somewhere_3way Unq) as [ [?[??]] |[ [?[??]] | [H[??]] ]]; [congruence|congruence| ].
  split; first (rewrite <- count_0_not_exists; assumption).
  intro Tg.
  rewrite bool_decide_eq_true_2 in H; [|assumption].
  congruence.
Qed.

Lemma unique_strict_parent_child_focus_1
  {data tr1 tr2} tg1 tg2 :
  tree_unique tg1 (branch data tr1 tr2) ->
  tree_unique tg2 (branch data tr1 tr2) ->
  tree_unique tg1 tr1 ->
  tree_unique tg2 tr1 ->
  StrictParentChildIn tg1 tg2 tr1
  <-> StrictParentChildIn tg1 tg2 (branch data tr1 tr2).
Proof.
  intros Unq1 Unq2 Unq1' Unq2'.
  rewrite /StrictParentChildIn.
  simpl; split.
  + intro P1.
    destruct (unique_found_branch_1 _ Unq1 Unq1') as [Absent NotTg].
    try repeat split.
    - intro; contradiction.
    - assumption.
    - rewrite every_subtree_eqv_universal.
      intros br Sub Tg.
      exfalso.
      apply Absent.
      enough (exists_subtree (compose (IsTag tg1) root) tr2) as FoundTg.
      * rewrite <- exists_node_iff_exists_root in FoundTg.
        exact FoundTg.
      * eapply exists_subtree_increasing; [|eassumption].
        simpl. intros. subst. auto.
  + intro P1.
    apply P1.
Qed.

Lemma unique_immediate_parent_child_focus_1
  {data tr1 tr2} tg1 tg2 :
  tree_unique tg1 (branch data tr1 tr2) ->
  tree_unique tg2 (branch data tr1 tr2) ->
  tree_unique tg1 tr1 ->
  tree_unique tg2 tr1 ->
  ImmediateParentChildIn tg1 tg2 tr1
  <-> ImmediateParentChildIn tg1 tg2 (branch data tr1 tr2).
Proof.
  intros Unq1 Unq2 Unq1' Unq2'.
  rewrite /ImmediateParentChildIn.
  simpl; split.
  + intro P1.
    destruct (unique_found_branch_1 _ Unq1 Unq1') as [Absent NotTg].
    try repeat split.
    - intro; contradiction.
    - assumption.
    - rewrite every_subtree_eqv_universal.
      intros br Sub Tg.
      exfalso.
      apply Absent.
      enough (exists_subtree (compose (IsTag tg1) root) tr2) as FoundTg.
      * rewrite <- exists_node_iff_exists_root in FoundTg.
        exact FoundTg.
      * eapply exists_subtree_increasing; [|eassumption].
        simpl. intros. subst. auto.
  + intro P1.
    apply P1.
Qed.

Lemma unique_strict_parent_child_focus_2
  {data tr1 tr2} tg1 tg2 :
  tree_unique tg1 (branch data tr1 tr2) ->
  tree_unique tg2 (branch data tr1 tr2) ->
  tree_unique tg1 tr2 ->
  tree_unique tg2 tr2 ->
  StrictParentChildIn tg1 tg2 tr2
  <-> StrictParentChildIn tg1 tg2 (branch data tr1 tr2).
Proof.
  intros Unq1 Unq2 Unq1' Unq2'.
  rewrite /StrictParentChildIn.
  simpl; split.
  + intro P1.
    destruct (unique_found_branch_2 _ Unq1 Unq1') as [Absent NotTg].
    try repeat split.
    - intro; contradiction.
    - rewrite every_subtree_eqv_universal.
      intros br Sub Tg.
      exfalso.
      apply Absent.
      enough (exists_subtree (compose (IsTag tg1) root) tr1) as FoundTg.
      * rewrite <- exists_node_iff_exists_root in FoundTg.
        exact FoundTg.
      * eapply exists_subtree_increasing; [|eassumption].
        simpl. intros. subst. auto.
    - assumption.
  + intro P1.
    apply P1.
Qed.

Lemma unique_immediate_parent_child_focus_2
  {data tr1 tr2} tg1 tg2 :
  tree_unique tg1 (branch data tr1 tr2) ->
  tree_unique tg2 (branch data tr1 tr2) ->
  tree_unique tg1 tr2 ->
  tree_unique tg2 tr2 ->
  ImmediateParentChildIn tg1 tg2 tr2
  <-> ImmediateParentChildIn tg1 tg2 (branch data tr1 tr2).
Proof.
  intros Unq1 Unq2 Unq1' Unq2'.
  rewrite /ImmediateParentChildIn.
  simpl; split.
  + intro P1.
    destruct (unique_found_branch_2 _ Unq1 Unq1') as [Absent NotTg].
    try repeat split.
    - intro; contradiction.
    - rewrite every_subtree_eqv_universal.
      intros br Sub Tg.
      exfalso.
      apply Absent.
      enough (exists_subtree (compose (IsTag tg1) root) tr1) as FoundTg.
      * rewrite <- exists_node_iff_exists_root in FoundTg.
        exact FoundTg.
      * eapply exists_subtree_increasing; [|eassumption].
        simpl. intros. subst. auto.
    - assumption.
  + intro P1.
    apply P1.
Qed.

Lemma unique_parent_child_focus_1
  {data tr1 tr2} tg1 tg2 :
  tree_unique tg1 (branch data tr1 tr2) ->
  tree_unique tg2 (branch data tr1 tr2) ->
  tree_unique tg1 tr1 ->
  tree_unique tg2 tr1 ->
  ParentChildIn tg1 tg2 tr1
  <-> ParentChildIn tg1 tg2 (branch data tr1 tr2).
Proof.
  intros Unq1 Unq2 Unq1' Unq2'.
  rewrite /ParentChildIn.
  rewrite unique_strict_parent_child_focus_1; first reflexivity; assumption.
Qed.

Lemma unique_parent_child_focus_2
  {data tr1 tr2} tg1 tg2 :
  tree_unique tg1 (branch data tr1 tr2) ->
  tree_unique tg2 (branch data tr1 tr2) ->
  tree_unique tg1 tr2 ->
  tree_unique tg2 tr2 ->
  ParentChildIn tg1 tg2 tr2
  <-> ParentChildIn tg1 tg2 (branch data tr1 tr2).
Proof.
  intros Unq1 Unq2 Unq1' Unq2'.
  rewrite /ParentChildIn.
  rewrite unique_strict_parent_child_focus_2; first reflexivity; assumption.
Qed.


Lemma cousins_in_branch_1
  {data tr1 tr2} tg1 tg2 :
  tree_unique tg1 (branch data tr1 tr2) ->
  tree_unique tg2 (branch data tr1 tr2) ->
  tree_unique tg1 tr1 ->
  tree_unique tg2 tr1 ->
  rel_dec (branch data tr1 tr2) tg1 tg2 = Foreign Cousin
  <-> rel_dec tr1 tg1 tg2 = Foreign Cousin.
Proof.
  intros Unq1 Unq2 Unq1' Unq2'.
  rewrite /rel_dec.
  pose proof (unique_parent_child_focus_1 _ _ Unq1 Unq2 Unq1' Unq2') as [].
  pose proof (unique_parent_child_focus_1 _ _ Unq2 Unq1 Unq2' Unq1') as [].
  pose proof (unique_immediate_parent_child_focus_1 _ _ Unq1 Unq2 Unq1' Unq2') as [].
  pose proof (unique_immediate_parent_child_focus_1 _ _ Unq2 Unq1 Unq2' Unq1') as [].
  repeat destruct (decide _); repeat destruct bool_decide; try tauto; done.
Qed.

Lemma cousins_in_branch_2
  {data tr1 tr2} tg1 tg2 :
  tree_unique tg1 (branch data tr1 tr2) ->
  tree_unique tg2 (branch data tr1 tr2) ->
  tree_unique tg1 tr2 ->
  tree_unique tg2 tr2 ->
  rel_dec (branch data tr1 tr2) tg1 tg2 = Foreign Cousin
  <-> rel_dec tr2 tg1 tg2 = Foreign Cousin.
Proof.
  intros Unq1 Unq2 Unq1' Unq2'.
  rewrite /rel_dec.
  pose proof (unique_parent_child_focus_2 _ _ Unq1 Unq2 Unq1' Unq2') as [].
  pose proof (unique_parent_child_focus_2 _ _ Unq2 Unq1 Unq2' Unq1') as [].
  pose proof (unique_immediate_parent_child_focus_2 _ _ Unq1 Unq2 Unq1' Unq2') as [].
  pose proof (unique_immediate_parent_child_focus_2 _ _ Unq2 Unq1 Unq2' Unq1') as [].
  repeat destruct (decide _); repeat destruct bool_decide; try tauto; done.
Qed.

Lemma cousins_find_common_ancestor
  {tr} tg1 tg2 :
  tree_unique tg1 tr ->
  tree_unique tg2 tr ->
  rel_dec tr tg1 tg2 = Foreign Cousin ->
  exists_subtree (fun '(data, tr1, tr2) =>
    (tree_contains tg1 tr1 /\ tree_contains tg2 tr2)
    \/ (tree_contains tg2 tr1 /\ tree_contains tg1 tr2)
    \/ (IsTag tg1 data /\ tree_contains tg2 tr1)
    \/ (IsTag tg2 data /\ tree_contains tg1 tr1)
  ) tr.
Proof.
  rewrite /tree_unique.
  intros Unq1 Unq2 Rel.

  assert (every_subtree (fun '(root, _, br2) => IsTag tg1 root -> ~tree_contains tg2 br2) tr)
    as Unrel1. {
      rewrite /rel_dec in Rel.
      destruct (decide _), (decide _) as [|nRel1]; try discriminate.
      rewrite every_subtree_eqv_universal.
      intros [[data tr1] tr2] Sub Tg Ex.
      apply nRel1.
      rewrite /ParentChildIn. right. rewrite /StrictParentChildIn.
      rewrite <- unique_exists_iff_unique; [|assumption].
      rewrite exists_subtree_eqv_existential.
      eexists; split; [eassumption|auto].
  }

  assert (every_subtree (fun '(root, _, br2) => IsTag tg2 root -> ~tree_contains tg1 br2) tr)
    as Unrel2. {
      rewrite /rel_dec in Rel.
      destruct (decide _) as [|nRel2], (decide _); try discriminate.
      rewrite every_subtree_eqv_universal.
      intros [[data tr1] tr2] Sub Tg Ex.
      apply nRel2.
      rewrite /ParentChildIn. right. rewrite /StrictParentChildIn.
      rewrite <- unique_exists_iff_unique; [|assumption].
      rewrite exists_subtree_eqv_existential.
      eexists; split; [eassumption|auto].
  }

  induction tr as [|data ? IHtr1 ? IHtr2]; simpl in *; [discriminate|].
  destruct (decide (IsTag tg1 data)), (decide (IsTag tg2 data)).
  - exfalso. eapply cousins_different; [eassumption|].
    congruence.
  - rewrite bool_decide_eq_false_2 /= in Unq2; [|assumption].
    destruct (unique_somewhere Unq2) as [[Unq21 _] | [Unq22 _]].
    + left. right. right. left.
      split; [assumption|].
      apply unique_exists.
      assumption.
    + (* absurd because they would be related *)
      exfalso.
      apply Unrel1; [assumption|].
      apply unique_exists.
      assumption.
  - rewrite bool_decide_eq_false_2 /= in Unq1; [|assumption].
    destruct (unique_somewhere Unq1) as [[Unq11 _] | [Unq12 _]].
    + left. right. right. right.
      split; [assumption|].
      apply unique_exists.
      assumption.
    + (* absurd because they would be related *)
      exfalso.
      apply Unrel2; [assumption|].
      apply unique_exists.
      assumption.
  - pose proof Unq1 as Unq1_remember.
    pose proof Unq2 as Unq2_remember.
    rewrite bool_decide_eq_false_2 /= in Unq1; [|assumption].
    rewrite bool_decide_eq_false_2 /= in Unq2; [|assumption].
    destruct (unique_somewhere Unq1) as [[Unq11 _] | [Unq12 _]],
             (unique_somewhere Unq2) as [[Unq21 _] | [Unq22 _]].
    + (* recurse left *)
      right. left.
      apply IHtr1.
      * apply Unq11.
      * apply Unq21.
      * eapply cousins_in_branch_1; try eassumption; assumption.
      * apply Unrel1.
      * apply Unrel2.
    + (* found the common ancestor *)
      left. left. split; apply unique_exists; assumption.
    + (* found the common ancestor *)
      left. right. left. split; apply unique_exists; assumption.
    + (* recurse right *)
      right. right.
      apply IHtr2.
      * apply Unq12.
      * apply Unq22.
      * eapply cousins_in_branch_2; try eassumption; assumption.
      * apply Unrel1.
      * apply Unrel2.
Qed.

Lemma subtree_count_lower_bound
  tr tg :
  every_subtree (fun '(data, tr1, tr2) =>
    tree_count_tg tg tr ≥ tree_count_tg tg tr1 + tree_count_tg tg tr2
  ) tr.
Proof.
  induction tr as [|data ? IHtr1 ? IHtr2]; simpl; [tauto|].
  split; last split.
  - lia.
  - rewrite every_subtree_eqv_universal in IHtr1.
    rewrite every_subtree_eqv_universal.
    intros br Sub. specialize (IHtr1 br Sub).
    destruct br as [[??]?].
    lia.
  - rewrite every_subtree_eqv_universal in IHtr2.
    rewrite every_subtree_eqv_universal.
    intros br Sub. specialize (IHtr2 br Sub).
    destruct br as [[??]?].
    lia.
Qed.

Lemma contains_child
  {tr tg tg'} :
  ParentChildIn tg tg' tr ->
  tree_contains tg tr ->
  tree_contains tg' tr.
Proof.
  intros [Eq|Strict]; [subst; tauto|].
  induction tr as [|data ? IHtr1 ? IHtr2]; simpl; [tauto|].
  intros [Here|[Ex1|Ex2]].
  - simpl in Strict. right; right.
    apply Strict. assumption.
  - right; left. apply IHtr1; [|assumption].
    apply Strict.
  - right; right. apply IHtr2; [|assumption].
    apply Strict.
Qed.

Lemma strict_child_in_subtree
  {tg tg' tr data tr1 tr2} :
  StrictParentChildIn tg tg' tr ->
  exists_subtree (eq (data, tr1, tr2)) tr ->
  StrictParentChildIn tg tg' tr1 /\ StrictParentChildIn tg tg' tr2.
Proof.
  rewrite /StrictParentChildIn.
  repeat rewrite every_subtree_eqv_universal.
  intros Child Sub.
  split; intros br Sub' Root.
  all: apply Child; [|eassumption].
  all: eapply exists_subtree_transitive; [eassumption|].
  - simpl; right; left; assumption.
  - simpl; right; right; assumption.
Qed.

Lemma cousins_have_disjoint_strict_children
  {tr tg} tg1 tg2 :
  tree_unique tg tr ->
  tree_unique tg1 tr ->
  tree_unique tg2 tr ->
  rel_dec tr tg1 tg2 = Foreign Cousin ->
  StrictParentChildIn tg1 tg tr ->
  StrictParentChildIn tg2 tg tr ->
  False.
Proof.
  intros Unique Ex1 Ex2 Cousins Strict1 Strict2.
  pose proof (cousins_find_common_ancestor _ _ Ex1 Ex2 Cousins) as CommonAncestor.
  rewrite exists_subtree_eqv_existential in CommonAncestor.
  destruct CommonAncestor as [[[data tr1] tr2] [EqSub Separate]].
  pose proof (subtree_count_lower_bound tr tg) as CountAtAncestor.
  rewrite every_subtree_eqv_universal in CountAtAncestor.
  specialize (CountAtAncestor (data, tr1, tr2) EqSub).
  simpl in *.
  assert (tree_count_tg tg tr1 ≥ 1). {
    destruct Separate as [[Ex1' _] | [[Ex2' _]| [[_ Ex2']|[_ Ex1']]]].
    + rewrite count_gt0_exists.
      eapply contains_child; [right|eassumption].
      apply (strict_child_in_subtree Strict1 EqSub).
    + apply count_gt0_exists.
      eapply contains_child; [right|eassumption].
      apply (strict_child_in_subtree Strict2 EqSub).
    + apply count_gt0_exists.
      eapply contains_child; [right|eassumption].
      apply (strict_child_in_subtree Strict2 EqSub).
    + apply count_gt0_exists.
      eapply contains_child; [right|eassumption].
      apply (strict_child_in_subtree Strict1 EqSub).
  }
  assert (tree_count_tg tg tr2 ≥ 1). {
    destruct Separate as [[_ Ex1'] | [[_ Ex2']|[[Ex2' _] | [Ex1' _]]]].
    + rewrite count_gt0_exists.
      eapply contains_child; [right|eassumption].
      apply (strict_child_in_subtree Strict2 EqSub).
    + apply count_gt0_exists.
      eapply contains_child; [right|eassumption].
      apply (strict_child_in_subtree Strict1 EqSub).
    + apply count_gt0_exists.
      unfold StrictParentChildIn in *.
      rewrite every_subtree_eqv_universal in Strict1.
      apply (Strict1 (data, tr1, tr2) EqSub Ex2').
    + apply count_gt0_exists.
      unfold StrictParentChildIn in *.
      rewrite every_subtree_eqv_universal in Strict2.
      apply (Strict2 (data, tr1, tr2) EqSub Ex1').
  }
  assert (tree_count_tg tg tr ≥ 2) as Twice by lia.
  rewrite Unique in Twice.
  lia.
Qed.

Lemma StrictParentChild_ParentChild
  {tr tg1 tg2 tg3} :
  StrictParentChildIn tg1 tg2 tr ->
  ParentChildIn tg2 tg3 tr ->
  StrictParentChildIn tg1 tg3 tr.
Proof.
  intros Strict12 [Eq|Strict23].
  + subst. assumption.
  + eapply StrictParentChild_transitive; eassumption.
Qed.

Lemma ParentChild_StrictParentChild
  {tr tg1 tg2 tg3} :
  ParentChildIn tg1 tg2 tr ->
  StrictParentChildIn tg2 tg3 tr ->
  StrictParentChildIn tg1 tg3 tr.
Proof.
  intros [Eq|Strict12] Strict23.
  + subst. assumption.
  + eapply StrictParentChild_transitive; eassumption.
Qed.


Lemma cousins_have_disjoint_children
  {tr tg} tg1 tg2
  :
  tree_unique tg tr ->
  tree_unique tg1 tr ->
  tree_unique tg2 tr ->
  rel_dec tr tg1 tg2 = Foreign Cousin ->
  ParentChildIn tg1 tg tr ->
  ParentChildIn tg2 tg tr ->
  False.
Proof.
  intros Unique Ex1 Ex2 Cousins Parent1 Parent2.
  assert (tg1 ≠ tg2). { eapply cousins_different. eassumption. }
  unfold ParentChildIn in *.
  destruct Parent1, Parent2; subst.
  + congruence.
  + rewrite /rel_dec in Cousins.
    destruct (decide _) as [|nRel]; [congruence|].
    destruct (decide _); [congruence|].
    apply nRel. right. assumption.
  + rewrite /rel_dec in Cousins.
    destruct (decide _); [congruence|].
    destruct (decide _) as [|nRel]; [congruence|].
    apply nRel. right. assumption.
  + eapply cousins_have_disjoint_strict_children with (tg1 := tg1) (tg2 := tg2).
    2,3,4,5,6: eassumption.
    eassumption.
Qed.

Lemma immediate_parent_child_not_equal tr tg1 tg2 :
  tree_unique tg1 tr ->
  tree_unique tg2 tr ->
  ImmediateParentChildIn tg1 tg2 tr ->
  tg1 ≠ tg2.
Proof.
  intros Hunq _ HPC ->.
  induction tr as [|data tr1 IH1 tr2 IH2]; first done.
  simpl in *. rewrite /tree_unique /= bool_decide_decide in Hunq.
  destruct HPC as (Hsibl & HPC1 & HPC2).
  apply unique_somewhere_3way in Hunq as [(Heq1&Heq2&Heq3)|[(Heq1&Heq2&Heq3)|(Heq1&Heq2&Heq3)]].
  - destruct decide as [H|]; last done.
    specialize (Hsibl H). eapply exists_sibling_exists_node in Hsibl.
    eapply count_0_not_exists in Heq3; eapply Heq3.
    rewrite /tree_contains. apply Hsibl.
  - apply IH1; done.
  - apply IH2; done.
Qed.

(* Very ugly counting argument.
   I hope there is a better proof of `immediate_not_transitive` *)
Fixpoint tree_count_tg_skip_siblings tg (tr : tree item) :=
  match tr with empty => 0 |
    branch _ sl sr => tree_count_tg_skip_siblings tg sl + tree_count_tg tg sr end.
Fixpoint tree_count_tg_only_siblings tg (tr : tree item) :=
  match tr with empty => 0 |
    branch it sl sr => (if decide (itag it = tg) then 1 else 0) + tree_count_tg_only_siblings tg sl end.
Lemma tree_count_tg_decompose tg tr :
  tree_count_tg tg tr = tree_count_tg_only_siblings tg tr + tree_count_tg_skip_siblings tg tr.
Proof.
  induction tr as [|it tr1 IHtr1 tr2 IHtr2]; first done.
  - simpl in *. rewrite IHtr1 IHtr2 decide_bool_decide. lia.
Qed.

Lemma exists_sibling_count tg tr :
  exists_sibling (λ it : item, itag it = tg) tr →
  tree_count_tg_only_siblings tg tr ≥ 1.
Proof.
  induction tr as [|it tr1 Htr1 tr2 _]; first done.
  simpl. intros [Heq|Hne].
  - rewrite decide_True; lia.
  - specialize (Htr1 Hne); lia.
Qed.

Lemma exists_sibling_child_count tg1 tg2 tr :
  exists_sibling (λ it : item, itag it = tg1) tr →
  StrictParentChildIn tg1 tg2 tr →
  tree_count_tg_skip_siblings tg2 tr ≥ 1.
Proof.
  induction tr as [|it tr1 Htr1 tr2 Htr2]; first done.
  simpl. intros [Heq|Hne] (Hfound&Hsibl&_).
  - specialize (Hfound Heq). eapply count_gt0_exists in Hfound. lia.
  - specialize (Htr1 Hne Hsibl). lia.
Qed.

Lemma immediate_not_transitive_strong
  tr1 tg1 tg2 tg3 :
  tree_unique tg1 tr1 ->
  tree_unique tg3 tr1 ->
  ImmediateParentChildIn tg1 tg2 tr1 ->
  StrictParentChildIn tg2 tg3 tr1 ->
  ImmediateParentChildIn tg1 tg3 tr1 ->
  False.
Proof.
  intros Unq1 Unq3 IPC1 IPC2 IPC3.
  assert (tg1 ≠ tg3) as Htg13ne by by eapply immediate_parent_child_not_equal.
  induction tr1 as [|data tr1 IH1 tr2 IH2]; first done.
  simpl in *. rewrite /tree_unique /= bool_decide_decide in Unq1.
  apply unique_somewhere_3way in Unq1 as [(Heq1&Heq2&Heq3)|[(Heq1&Heq2&Heq3)|(Heq1&Heq2&Heq3)]].
  - destruct decide as [H|]; last done.
    destruct IPC1 as (Hsibl1 & _ & _).
    destruct IPC2 as (_ & ICP1 & ICP2).
    destruct IPC3 as (Hsibl3 & _ & _). clear IH1 IH2.
    rewrite /tree_unique /= in Unq3.
    enough (tree_count_tg tg3 tr2 ≥ 2) by lia. clear Unq3.
    rewrite tree_count_tg_decompose.
    opose proof (exists_sibling_child_count tg2 tg3 tr2 _ _) as Hlia1.
    1: by apply Hsibl1. 1: done.
    opose proof (exists_sibling_count tg3 tr2 _) as Hlia2.
    1: by apply Hsibl3. lia.
  - destruct_and!. eapply IH1; try done.
    rewrite /tree_unique /= bool_decide_decide in Unq3.
    apply unique_somewhere_3way in Unq3 as [(Heq1'&Heq2'&Heq3')|[(Heq1'&Heq2'&Heq3')|(Heq1'&Heq2'&Heq3')]]; try done.
    all: enough (tree_count_tg tg3 tr1 ≥ 1) by lia.
    all: eapply count_gt0_exists.
    all: eapply contains_child; first (right; by eapply Immediate_is_StrictParentChild).
    all: eapply count_gt0_exists; lia.
  - destruct_and!. eapply IH2; try done.
    rewrite /tree_unique /= bool_decide_decide in Unq3.
    apply unique_somewhere_3way in Unq3 as [(Heq1'&Heq2'&Heq3')|[(Heq1'&Heq2'&Heq3')|(Heq1'&Heq2'&Heq3')]]; try done.
    all: enough (tree_count_tg tg3 tr2 ≥ 1) by lia.
    all: eapply count_gt0_exists.
    all: eapply contains_child; first (right; by eapply Immediate_is_StrictParentChild).
    all: eapply count_gt0_exists; lia.
Qed.

Lemma immediate_not_transitive
  tr1 tg1 tg2 tg3 :
  tree_unique tg1 tr1 ->
  tree_unique tg3 tr1 ->
  ImmediateParentChildIn tg1 tg2 tr1 ->
  ImmediateParentChildIn tg2 tg3 tr1 ->
  ImmediateParentChildIn tg1 tg3 tr1 ->
  False.
Proof.
  intros H1 H2 H3 H4 H5; unshelve eapply (immediate_not_transitive_strong _ _ _ _ H1 H2 H3 _ H5).
  by eapply Immediate_is_StrictParentChild.
Qed.

Lemma tree_all_unique_structural_l it tr1 tr2 :
  (∀ tg, tree_contains tg (branch it tr1 tr2) → tree_unique tg (branch it tr1 tr2)) →
  (∀ tg, tree_contains tg tr1 → tree_unique tg tr1).
Proof.
  intros Hall tg Hcont.
  opose proof (Hall tg _) as Htg.
  - simpl. tauto.
  - rewrite /tree_unique /= in Htg|-*.
    eapply count_gt0_exists in Hcont. lia.
Qed.

Lemma tree_all_unique_structural_r it tr1 tr2 :
  (∀ tg, tree_contains tg (branch it tr1 tr2) → tree_unique tg (branch it tr1 tr2)) →
  (∀ tg, tree_contains tg tr2 → tree_unique tg tr2).
Proof.
  intros Hall tg Hcont.
  opose proof (Hall tg _) as Htg.
  - simpl. tauto.
  - rewrite /tree_unique /= in Htg|-*.
    eapply count_gt0_exists in Hcont. lia.
Qed.

Lemma exists_node_is_root_child it tr1 tr2 tg2 :
  let tr := branch it tr1 tr2 in
  (∀ tg, tree_contains tg tr → tree_unique tg tr) →
  exists_node (λ it, itag it = tg2) tr2 →
  ParentChildIn (itag it) tg2 tr.
Proof.
  intros tr Hunq Hexi. subst tr.
  right. eapply unique_exists_iff_unique.
  1: eapply Hunq; by left.
  left. split; first done.
  simpl. done.
Qed.

Lemma exists_node_exists_sibling_parent_child tr tg2 :
  (∀ tg, tree_contains tg tr → tree_unique tg tr) →
  exists_node (λ it, itag it = tg2) tr →
  ∃ tsw,
  exists_sibling (λ it, itag it = tsw) tr ∧
  ParentChildIn tsw tg2 tr.
Proof.
  induction tr as [|it tr1 IHtr1 tr2 IHtr2]; first done.
  intros Hallunq [Heq|[Hl|Hr]]; simpl in *.
  - exists tg2. split; first by left. by left.
  - pose proof Hl as Htr1.
    eapply IHtr1 in Hl as (tsw&Hsib&Hpc).
    2: eapply tree_all_unique_structural_l, Hallunq.
    exists tsw; split; first by right.
    eapply exists_sibling_exists_node in Hsib.
    rewrite <- unique_parent_child_focus_1; first done.
    3-4: eapply tree_all_unique_structural_l; try exact Hallunq.
    1-2: eapply Hallunq; right; left.
    all: done.
  - exists (itag it). split; first by left.
    eapply exists_node_is_root_child. 1: exact Hallunq. done.
Qed.

Lemma immediate_sandwich tr tg1 tg2 :
  (∀ tg, tree_contains tg tr → tree_unique tg tr) →
  tree_unique tg1 tr →
  StrictParentChildIn tg1 tg2 tr →
  ∃ tsw,
  ImmediateParentChildIn tg1 tsw tr ∧ ParentChildIn tsw tg2 tr.
Proof.
  induction tr as [|it tr1 IHtr1 tr2 IHtr2]; first done. intros Hallunq.
  rewrite /tree_unique /= bool_decide_decide.
  intros [(Heq1&Heq2&Heq3)|[(Heq1&Heq2&Heq3)|(Heq1&Heq2&Heq3)]]%unique_somewhere_3way (HSP1&HSP2&HSP3).
  - destruct decide as [Hteq|]; last done.
    specialize (HSP1 Hteq).
    destruct (exists_node_exists_sibling_parent_child tr2 tg2) as (tsw&Hs1&Hs2).
    1: by eapply tree_all_unique_structural_r.
    1: done.
    exists tsw. split_and!; try done.
    + eapply every_subtree_eqv_universal. intros tb Htb Htg.
      exfalso; eapply count_0_not_exists; first exact Heq2.
      eapply exists_node_iff_exists_root. eapply exists_subtree_increasing; last done.
      intros ? <-; done.
    + eapply every_subtree_eqv_universal. intros tb Htb Htg.
      exfalso; eapply count_0_not_exists; first exact Heq3.
      eapply exists_node_iff_exists_root. eapply exists_subtree_increasing; last done.
      intros ? <-; done.
    + eapply exists_sibling_exists_node in Hs1.
      rewrite <- unique_parent_child_focus_2; first done.
      3-4: eapply tree_all_unique_structural_r; try exact Hallunq.
      1-2: eapply Hallunq; right; right.
      all: done.
  - destruct IHtr1 as (tsw&Hs1&Hs2).
    1: eapply tree_all_unique_structural_l; done.
    1: apply Heq2.
    1: done.
    exists tsw. split_and!; try done.
    + destruct decide; done.
    + eapply every_subtree_eqv_universal. intros tb Htb Htg.
      exfalso; eapply count_0_not_exists; first exact Heq3.
      eapply exists_node_iff_exists_root. eapply exists_subtree_increasing; last done.
      intros ? <-; done.
    + assert (tree_contains tsw tr1) as Htswin.
      { eapply contains_child. 1: right; by eapply Immediate_is_StrictParentChild.
        eapply count_gt0_exists. lia. }
      assert (tree_contains tg2 tr1) as Htg2in.
      { eapply contains_child; done. }
      rewrite <- unique_parent_child_focus_1; first done.
      3-4: eapply tree_all_unique_structural_l; try exact Hallunq.
      1-2: eapply Hallunq; right; left.
      all: done.
  - destruct IHtr2 as (tsw&Hs1&Hs2).
    1: eapply tree_all_unique_structural_r; done.
    1: apply Heq3.
    1: done.
    exists tsw. split_and!; try done.
    + destruct decide; done.
    + eapply every_subtree_eqv_universal. intros tb Htb Htg.
      exfalso; eapply count_0_not_exists; first exact Heq2.
      eapply exists_node_iff_exists_root. eapply exists_subtree_increasing; last done.
      intros ? <-; done.
    + assert (tree_contains tsw tr2) as Htswin.
      { eapply contains_child. 1: right; by eapply Immediate_is_StrictParentChild.
        eapply count_gt0_exists. lia. }
      assert (tree_contains tg2 tr2) as Htg2in.
      { eapply contains_child; done. }
      rewrite <- unique_parent_child_focus_2; first done.
      3-4: eapply tree_all_unique_structural_r; try exact Hallunq.
      1-2: eapply Hallunq; right; right.
      all: done.
Qed.

Lemma immediate_parent_not_child it1 it2 tr :
  tree_unique it1 tr →
  tree_unique it2 tr →
  ImmediateParentChildIn it1 it2 tr →
  ParentChildIn it2 it1 tr →
  False.
Proof.
  intros Hu1 Hu2 H1 [H2|H2].
  1: { eapply immediate_parent_child_not_equal. 3: done. all: done. }
  eapply not_strict_parent_of_self; last first.
  - eapply StrictParentChild_transitive; last done.
    by eapply Immediate_is_StrictParentChild.
  - by eapply unique_exists.
Qed.

Lemma immediate_not_transitive_strong_2
  tr1 tg1 tg2 tg3 :
  (∀ tg, tree_contains tg tr1 → tree_unique tg tr1) →
  tree_unique tg1 tr1 ->
  tree_unique tg2 tr1 ->
  tree_unique tg3 tr1 ->
  StrictParentChildIn tg1 tg2 tr1 ->
  StrictParentChildIn tg2 tg3 tr1 ->
  ImmediateParentChildIn tg1 tg3 tr1 ->
  False.
Proof.
  intros Huu Hu1 Hu2 Hu3 (tsw&H1&H2)%immediate_sandwich H3. 2-3: done.
  eapply immediate_not_transitive_strong. 1-2: done. 1: apply H1.
  destruct H2 as [->|H2].
  2: eapply StrictParentChild_transitive; first done.
  all: done.
Qed.

Lemma ImmediateParentChildIn_parent_not_in tg1 tg2 tr :
  ¬ tree_contains tg1 tr →
  ImmediateParentChildIn tg1 tg2 tr.
Proof.
  intros H1. eapply every_subtree_eqv_universal.
  intros bt Hbr Htg. exfalso.
  eapply H1, exists_node_iff_exists_root. simpl.
  eapply exists_subtree_eqv_existential. eexists; split; first done.
  simpl. done.
Qed.

Definition every_strict_child (pt : tag) (P : item → Prop) (tr : tree item) :=
  every_subtree (λ '(rt, _, childs), itag rt = pt → every_node P childs) tr.
Definition every_child (pt : tag) (P : item → item → Prop) (tr : tree item) :=
  every_subtree (λ '(rt, _, childs), itag rt = pt → P rt rt ∧ every_node (P rt) childs) tr.

Lemma every_child_not_in pt P tr :
  ¬ tree_contains pt tr →
  every_child pt P tr.
Proof.
  induction tr as [|it tr1 IH1 tr2 IH2]; first done.
  simpl. intros HN. split_and!; tauto.
Qed.

Lemma every_strict_child_not_in pt P tr :
  ¬ tree_contains pt tr →
  every_strict_child pt P tr.
Proof.
  induction tr as [|it tr1 IH1 tr2 IH2]; first done.
  simpl. intros HN. split_and!; tauto.
Qed.

Lemma every_child_ParentChildIn pt P tr 
  (Hunq : ∀ tg, tree_contains tg tr → tree_unique tg tr)
  (Hptunq : tree_unique pt tr) :
  every_child pt P tr ↔
  ∀ itp, tree_item_determined pt itp tr → ∀ tg', tree_unique tg' tr → ParentChildIn pt tg' tr → every_node (λ it, it.(itag) = tg' → P itp it) tr.
Proof.
  split.
  - induction tr as [|it tr1 IH1 tr2 IH2].
    1: done. simpl. intros (Hfound&Hl&Hr).
    rewrite /tree_unique /= in Hptunq.
    eapply unique_somewhere_3way in Hptunq as [(Hu1&Hu2&Hu3)|[(Hu1&Hu2&Hu3)|(Hu1&Hu2&Hu3)]];
    destruct (decide (itag it = pt)) as [Heq|Hne];
    (try (rewrite bool_decide_true in Hu1; last done));
    (try (rewrite bool_decide_false in Hu1; last done)); try done.
    + subst pt. specialize (Hfound eq_refl) as (Hself&Hchildren).
      intros itp (Hdet1&Hdet2&Hdet3) tg' Hcunq HPC.
      specialize (Hdet1 eq_refl). subst itp.
      split; first done.
      split; last first.
      { eapply every_node_increasing; first exact Hchildren.
        eapply every_node_eqv_universal. done. }
      rewrite /tree_unique /= in Hcunq.
      eapply unique_somewhere_3way in Hcunq as [(Hu1'&Hu2'&Hu3')|[(Hu1'&Hu2'&Hu3')|(Hu1'&Hu2'&Hu3')]].
      * rewrite bool_decide_decide in Hu1'. destruct decide as [Heq|Hne]; try done. subst tg'.
        ospecialize (Hunq (itag it) _). 1: by left.
        rewrite /tree_unique /= bool_decide_true // in Hunq.
        eapply unique_somewhere_3way in Hunq as [(H1&H2&H3)|[H|H]]; try lia.
        eapply every_node_eqv_universal; intros n Hn Hit; exfalso.
        eapply count_0_not_exists; first exact H2.
        eapply exists_node_eqv_existential. by exists n.
      * destruct HPC as [Heq|Hne]. 1: by rewrite bool_decide_true in Hu1'.
        simpl in Hne.
        destruct Hne as (Hne1&Hne2&Hne3).
        exfalso. eapply count_0_not_exists; first exact Hu3'.
        apply Hne1. done.
      * eapply every_node_eqv_universal; intros n Hn Hit; exfalso.
        eapply count_0_not_exists; first exact Hu2'.
        eapply exists_node_eqv_existential. by exists n.
    + intros itp (Hdet1&Hdet2&Hdet3) tg' Htgunq HPC.
      rewrite /tree_unique /= in Htgunq.
      eapply unique_somewhere_3way in Htgunq as [(Hu1'&Hu2'&Hu3')|[(Hu1'&Hu2'&Hu3')|(Hu1'&Hu2'&Hu3')]].
      * rewrite bool_decide_decide in Hu1'. destruct decide as [Heq|Hne']; try done. subst tg'.
        destruct HPC as [HPC|HPC]; first done.
        exfalso. simpl in HPC. destruct HPC as (_&HPC&_). eapply count_0_not_exists; first exact Hu2'.
        eapply contains_child. 1: right; apply HPC.
        eapply count_gt0_exists. lia.
      * rewrite bool_decide_decide in Hu1'. destruct decide as [Heq|Hne']; try done.
        split; first done.
        split.
        { eapply IH1. 1: by eapply tree_all_unique_structural_l. 1: done. 1: done. 1: done. 1: done.
          destruct HPC as [HPC|HPC]; first by left. right. apply HPC. }
        eapply every_node_eqv_universal; intros n Hn Hit; exfalso.
        eapply count_0_not_exists; first exact Hu3'.
        eapply exists_node_eqv_existential. by exists n.
      * rewrite bool_decide_decide in Hu1'. destruct decide as [Heq|Hne']; try done.
        destruct HPC as [->|HPC]; first congruence.
        exfalso. simpl in HPC. destruct HPC as (_&HPC&_). eapply count_0_not_exists; first exact Hu2'.
        eapply contains_child. 1: right; apply HPC.
        eapply count_gt0_exists. lia.
    + intros itp (Hdet1&Hdet2&Hdet3) tg' Htgunq HPC.
      rewrite /tree_unique /= in Htgunq.
      eapply unique_somewhere_3way in Htgunq as [(Hu1'&Hu2'&Hu3')|[(Hu1'&Hu2'&Hu3')|(Hu1'&Hu2'&Hu3')]].
      * rewrite bool_decide_decide in Hu1'. destruct decide as [Heq|Hne']; try done. subst tg'.
        destruct HPC as [HPC|HPC]; first done.
        exfalso. simpl in HPC. destruct HPC as (_&_&HPC). eapply count_0_not_exists; first exact Hu3'.
        eapply contains_child. 1: right; apply HPC.
        eapply count_gt0_exists. lia.
      * rewrite bool_decide_decide in Hu1'. destruct decide as [Heq|Hne']; try done.
        destruct HPC as [->|HPC]; first congruence.
        exfalso. simpl in HPC. destruct HPC as (_&_&HPC). eapply count_0_not_exists; first exact Hu3'.
        eapply contains_child. 1: right; apply HPC.
        eapply count_gt0_exists. lia.
      * rewrite bool_decide_decide in Hu1'. destruct decide as [Heq|Hne']; try done.
        split; first done.
        split; last first.
        { eapply IH2. 1: by eapply tree_all_unique_structural_r. 1: done. 1: done. 1: done. 1: done.
          destruct HPC as [HPC|HPC]; first by left. right. apply HPC. }
        eapply every_node_eqv_universal; intros n Hn Hit; exfalso.
        eapply count_0_not_exists; first exact Hu2'.
        eapply exists_node_eqv_existential. by exists n.
  - induction tr as [|it tr1 IH1 tr2 IH2]; first done.
    intros Heach.
    rewrite /tree_unique /= in Hptunq. pose proof Hptunq as Hptunqg.
    eapply unique_somewhere_3way in Hptunq as [(Hu1&Hu2&Hu3)|[(Hu1&Hu2&Hu3)|(Hu1&Hu2&Hu3)]];
    destruct (decide (itag it = pt)) as [Heq|Hne];
    (try (rewrite bool_decide_true in Hu1; last done));
    (try (rewrite bool_decide_false in Hu1; last done)); try done.
    + simpl. split_and!.
      2-3: by eapply every_child_not_in, count_0_not_exists.
      intros _. split.
      * ospecialize (Heach it _ pt _).
        { split; first done. split; by eapply absent_determined. }
        1: rewrite /tree_unique /= Heq bool_decide_true //; lia.
        destruct Heach as (Heach&_). 1: by left. apply Heach. done.
      * eapply every_node_eqv_universal. intros itn Hexn.
        assert (tree_unique (itag itn) tr2) as Hnunq.
        { eapply tree_all_unique_structural_r; first done.
          eapply exists_node_eqv_existential. by exists itn. }
        assert (tree_unique (itag itn) (branch it tr1 tr2)) as Hnoo.
        { eapply Hunq. right. right.
          eapply exists_node_eqv_existential. by exists itn. }
        pose proof Hnoo as Hnunq'.
        rewrite /tree_unique /= in Hnoo,Hnunq.
        rewrite Hnunq in Hnoo.
        eapply unique_somewhere_3way in Hnoo as [Hnoo|[Hnoo|Hnoo]]; try lia.
        ospecialize (Heach it _ (itag itn) _ _).
        { split; first done. split; by eapply absent_determined. } 1: done.
        { right. split_and!.
          - intros _. rewrite /HasStrictChildTag /=.
            eapply exists_node_eqv_existential. by eexists.
          - eapply every_subtree_eqv_universal.
            intros cbr Hcbr Hrootbr.
            eapply (exists_subtree_increasing (Q := (compose (λ rt, itag rt = pt) root))) in Hcbr.
            2: by intros ? <-. setoid_rewrite <- exists_node_iff_exists_root in Hcbr.
            exfalso. eapply count_0_not_exists. 2: exact Hcbr. done.
          - eapply every_subtree_eqv_universal.
            intros cbr Hcbr Hrootbr.
            eapply (exists_subtree_increasing (Q := (compose (λ rt, itag rt = pt) root))) in Hcbr.
            2: by intros ? <-. setoid_rewrite <- exists_node_iff_exists_root in Hcbr.
            exfalso. eapply count_0_not_exists. 2: exact Hcbr. done. }
        setoid_rewrite every_node_eqv_universal in Heach.
        apply Heach. 1: right; right; done. 1: done.
    + split_and!; first done.
      * eapply IH1. 1: by eapply tree_all_unique_structural_l.
        1: done.
        intros itp Hdetitp tg' Htgunq' HPC. eapply Heach.
        { split; first done. split; try done. eapply every_node_eqv_universal.
          intros itx Hitx Htg. exfalso. eapply count_0_not_exists.
          1: exact Hu3. eapply exists_node_eqv_existential. by eexists. }
        { eapply Hunq. right. left. eapply count_gt0_exists. rewrite /tree_unique in Htgunq'. lia. }
        destruct HPC as [HPC|HPC]; first by left.
        right. split; first done. split; try done.
        eapply every_subtree_eqv_universal.
        intros cbr Hcbr Hrootbr.
        eapply (exists_subtree_increasing (Q := (compose (λ rt, itag rt = pt) root))) in Hcbr.
        2: by intros ? <-. setoid_rewrite <- exists_node_iff_exists_root in Hcbr.
        exfalso. eapply count_0_not_exists. 2: exact Hcbr. done.
      * by eapply every_child_not_in, count_0_not_exists.
    + split_and!; first done.
      * by eapply every_child_not_in, count_0_not_exists.
      * eapply IH2. 1: by eapply tree_all_unique_structural_r.
        1: done.
        intros itp Hdetitp tg' Htgunq' HPC. eapply Heach.
        { split; first done. split; try done. eapply every_node_eqv_universal.
          intros itx Hitx Htg. exfalso. eapply count_0_not_exists.
          1: exact Hu2. eapply exists_node_eqv_existential. by eexists. }
        { eapply Hunq. right. right. eapply count_gt0_exists. rewrite /tree_unique in Htgunq'. lia. }
        destruct HPC as [HPC|HPC]; first by left.
        right. split; first done. split; try done.
        eapply every_subtree_eqv_universal.
        intros cbr Hcbr Hrootbr.
        eapply (exists_subtree_increasing (Q := (compose (λ rt, itag rt = pt) root))) in Hcbr.
        2: by intros ? <-. setoid_rewrite <- exists_node_iff_exists_root in Hcbr.
        exfalso. eapply count_0_not_exists. 2: exact Hcbr. done.
Qed.

Lemma find_highest_parent_with_property (P : item → Prop) (d : ∀ x, Decision (P x)) tr :
  (∀ k, tree_contains k tr → tree_unique k tr) →
  exists_node P tr →
  ∃ tg, exists_node (λ it, P it ∧ itag it = tg) tr ∧
      ∀ tg', exists_node (λ it, P it ∧ itag it = tg') tr →
             StrictParentChildIn tg' tg tr → False.
Proof.
  induction tr as [|it tr1 IH1 tr2 IH2].
  1: by intros _ [].
  intros Hunq H.
  pose proof (tree_all_unique_structural_l _ _ _ Hunq) as Hunql.
  pose proof (tree_all_unique_structural_r _ _ _ Hunq) as Hunqr.
  destruct (decide (P it)) as [HP|HnP].
  2: destruct H as [Hf|[Htr1|Htr2]]; first done.
  - exists (itag it). split.
    1: by left.
    ospecialize (Hunq (itag it) _). 1: by left.
    intros tg' [(HP1&HP2)|[Hcld|Hcld]] (HSPCI&HSPCI1&HSPCI2).
    + specialize (HSPCI HP2).
      ospecialize (Hunqr (itag it) _).
      1: by eapply HSPCI.
      rewrite /tree_unique /= Hunqr bool_decide_true // in Hunq. lia.
    + ospecialize (Hunql (itag it) _).
      { eapply contains_child. 1: right; exact HSPCI1.
        eapply exists_node_eqv_existential. eapply exists_node_eqv_existential in Hcld as (ii&Hii&Hcld).
        exists ii; split; first done. eapply Hcld. }
      rewrite /tree_unique /= Hunql bool_decide_true // in Hunq.
    + ospecialize (Hunqr (itag it) _).
      { eapply contains_child. 1: right; exact HSPCI2.
        eapply exists_node_eqv_existential. eapply exists_node_eqv_existential in Hcld as (ii&Hii&Hcld).
        exists ii; split; first done. eapply Hcld. }
      rewrite /tree_unique /= Hunqr bool_decide_true // in Hunq. lia.
  - destruct IH1 as (tg&Htg&Hnopar).
    1-2: done.
    exists tg. split; first (right; by left).
    intros tg' [(HP1&HP2)|[Hcld|Hcld]] (HSPCI&HSPCI1&HSPCI2).
    + done.
    + simpl in *. eapply Hnopar; last done. exact Hcld.
    + assert (tree_contains tg tr1) as Htgtr1.
      { eapply exists_node_eqv_existential. eapply exists_node_eqv_existential in Htg as (ii&Hii&Htg).
        exists ii; split; first done. eapply Htg. }
      ospecialize (Hunq tg _).
      { right. left. done. }
      ospecialize (Hunql tg Htgtr1).
      ospecialize (Hunqr tg _).
      { eapply contains_child. 1: right; exact HSPCI2.
        eapply exists_node_eqv_existential. eapply exists_node_eqv_existential in Hcld as (ii&Hii&Hcld).
        exists ii; split; first done. eapply Hcld. }
      unfold tree_unique in *.
      rewrite /= Hunql Hunqr in Hunq. lia.
  - destruct IH2 as (tg&Htg&Hnopar).
    1-2: done.
    exists tg. split; first (right; by right).
    intros tg' [(HP1&HP2)|[Hcld|Hcld]] (HSPCI&HSPCI1&HSPCI2).
    + done.
    + assert (tree_contains tg tr2) as Htgtr2.
      { eapply exists_node_eqv_existential. eapply exists_node_eqv_existential in Htg as (ii&Hii&Htg).
        exists ii; split; first done. eapply Htg. }
      ospecialize (Hunq tg _).
      { right. right. done. }
      ospecialize (Hunqr tg Htgtr2).
      ospecialize (Hunql tg _).
      { eapply contains_child. 1: right; exact HSPCI1.
        eapply exists_node_eqv_existential. eapply exists_node_eqv_existential in Hcld as (ii&Hii&Hcld).
        exists ii; split; first done. eapply Hcld. }
      unfold tree_unique in *.
      rewrite /= Hunql Hunqr in Hunq. lia.
    + simpl in *. eapply Hnopar; last done. exact Hcld.
Qed.


Definition prot_join (ps1 ps2 : prot_strong) : prot_strong := match ps1 with
  ProtStrong => ProtStrong
| ProtWeak   => ps2 end.

Lemma prot_join_comm ps1 ps2 : prot_join ps1 ps2 = prot_join ps2 ps1.
Proof.
  by destruct ps1, ps2.
Qed.

Definition prot_le (ps1 ps2 : prot_strong) : Prop := match ps1, ps2 with
  ProtWeak, _ => True
| ProtStrong, ProtStrong => True
| ProtStrong, _ => False end.

Lemma prot_le_def ps1 ps2 : prot_le ps1 ps2 ↔ (ps1 = ProtStrong → ps2 = ProtStrong).
Proof. destruct ps1, ps2; simpl; split; try firstorder. discriminate. Qed.

Lemma prot_le_refl ps : prot_le ps ps.
Proof. by destruct ps. Qed.

Lemma prot_le_trans ps1 ps2 ps3 : prot_le ps1 ps2 → prot_le ps2 ps3 → prot_le ps1 ps3.
Proof. by destruct ps1, ps2, ps3. Qed.

Lemma prot_join_is_strong ps1 ps2 :
  prot_join ps1 ps2 = ProtStrong ↔ (ps1 = ProtStrong ∨ ps2 = ProtStrong).
Proof. destruct ps1, ps2; simpl; tauto. Qed.

Lemma prot_join_is_weak ps1 ps2 :
  prot_join ps1 ps2 = ProtWeak ↔ (ps1 = ProtWeak ∧ ps2 = ProtWeak).
Proof. destruct ps1, ps2; simpl; tauto. Qed.

Definition tree_lookup (tr : tree item) (tg : tag) (it : item) := tree_contains tg tr ∧ tree_item_determined tg it tr.
Definition trees_lookup (trs : trees) blk tg it :=
  exists tr,
    trs !! blk = Some tr
    /\ tree_lookup tr tg it.

Lemma lookup_implies_contains
  {tr tg it} :
  tree_lookup tr tg it -> tree_contains tg tr.
Proof. intro H. apply H. Qed.

Lemma unique_implies_lookup {tr tg} :
  tree_unique tr tg -> ∃ it, tree_lookup tg tr it.
Proof.
  intros Hunq.
  pose proof Hunq as (it&Hdet)%unique_lookup.
  exists it; split; last done.
  by eapply unique_exists.
Qed.

Lemma tree_lookup_correct_tag {tr tg it} :
  tree_lookup tr tg it ->
  it.(itag) = tg.
Proof. intros [? ?]. eapply tree_determined_specifies_tag; eassumption. Qed.

Lemma trees_lookup_correct_tag {trs blk tg it} :
  trees_lookup trs blk tg it ->
  it.(itag) = tg.
Proof. intros [?[??]]. eapply tree_lookup_correct_tag; eassumption. Qed.

Lemma tree_lookup_IsTag tr tg it : tree_lookup tr tg it → IsTag tg it.
Proof.
  intros (H1 & H2).
  eapply exists_node_eqv_existential in H1 as (it2 & Hit2 & Histag).
  eapply every_node_eqv_universal in H2; last done.
  by rewrite -H2.
Qed.

Lemma tree_lookup_unique tr tg it1 it2 : tree_lookup tr tg it1 → tree_lookup tr tg it2 → it1 = it2.
Proof.
  intros Hlu (H1 & H2).
  eapply every_node_eqv_universal in H2; first apply H2.
  1: by eapply tree_lookup_IsTag.
  eapply exists_determined_exists; first done.
  apply Hlu.
Qed.

Lemma tree_lookup_to_exists_node tr tg itm :
  tree_lookup tr tg itm →
  exists_node (eq itm) tr.
Proof.
  intros (Hcont&Hitm). by eapply exists_determined_exists.
Qed.

Lemma if_same_guard_equal
  {P Q : Prop} {T} {x y x' y' : T} `{Decision P} `{Decision Q}
  (Iff : P <-> Q)
  (Ex : x = x')
  (Ey : y = y')
  : (if decide P then x else y) = (if decide Q then x' else y').
Proof.
  repeat destruct (decide _); tauto.
Qed.

Lemma create_child_same_rel_dec
  {tr tr' tg tg' tg_old tg_new pk im rk cid C}
  (Ne : tg_new ≠ tg)
  (Ne' : tg_new ≠ tg')
  (Ins : create_child C tg_old tg_new pk im rk cid tr = Some tr')
  : rel_dec tr tg tg' = rel_dec tr' tg tg'.
Proof.
  eapply create_child_isSome in Ins as (it&<-%new_item_has_tag&->).
  unfold rel_dec.
  apply if_same_guard_equal.
  - erewrite insert_eqv_rel; first done; assumption.
  - f_equal.
    apply if_same_guard_equal.
    + by erewrite insert_eqv_rel.
    + reflexivity.
    + f_equal.
      apply if_same_guard_equal.
      * by erewrite insert_eqv_imm_rel.
      * reflexivity.
      * reflexivity.
  - f_equal.
    apply if_same_guard_equal.
    + by erewrite insert_eqv_rel.
    + f_equal.
      apply if_same_guard_equal.
      * by erewrite insert_eqv_imm_rel.
      * reflexivity.
      * reflexivity.
    + reflexivity.
Qed.
