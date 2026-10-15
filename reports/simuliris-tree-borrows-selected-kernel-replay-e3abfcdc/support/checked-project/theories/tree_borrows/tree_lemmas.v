From Equations Require Import Equations.
From iris.prelude Require Import prelude options.
From stdpp Require Export gmap.
From simuliris.tree_borrows Require Export tree.

Implicit Type (V W X Y:Type).

Lemma option_map_compose {X Y Z} (fn:X -> Y) (fn':Y -> Z) :
  forall ox, option_map fn' (option_map fn ox) = option_map (compose fn' fn) ox.
Proof. intro ox. destruct ox; simpl; auto. Qed.

Lemma option_bind_map_join {X Y} (fn:X -> option Y) :
  option_bind fn = compose option_join (option_map fn).
Proof. apply functional_extensionality. intro ox. destruct ox; simpl; auto. Qed.

Lemma option_bind_success_step {T U} (ox:option T) (f:T -> option U) (r:U) :
  ((x ← ox; f x) = Some r) -> exists x, ox = Some x /\ f x = Some r.
Proof.
  intro H.
  destruct ox; simpl in *; [|inversion H].
  eexists. split; [reflexivity|assumption].
Qed.

Ltac option_bind_success H x C :=
  let tmp := fresh "H" in
  match type of H with
  | _ = Some _ => idtac
  | Some _ = _ => symmetry in H
  | is_Some _ => let x' := fresh "x" in destruct H as [x' H]
  end;
  destruct (option_bind_success_step _ _ _ H) as [x [C tmp]];
  clear H; rename tmp into H.

Tactic Notation "option" "step" "in" constr(H) "as" ident(x) ":" ident(C) :=
  option_bind_success H x C.
Tactic Notation "option" "step" "in" constr(H) "as" "?" ":" ident(C) :=
  let x := fresh "x" in
  option_bind_success H x C.
Tactic Notation "option" "step" "in" constr(H) "as" ident(x) ":" "?" :=
  let C := fresh "C" in
  option_bind_success H x C.
Tactic Notation "option" "step" "in" constr(H) "as" "?" ":" "?" :=
  let x := fresh "x" in
  let C := fresh "C" in
  option_bind_success H x C.

Lemma join_join_nodes {X} :
  forall (tr:tree (option (option X))),
  option_bind join_nodes (join_nodes tr) = join_nodes (map_nodes option_join tr).
Proof.
  intro tr. induction tr as [|data tr1 IHtr1 tr2 IHtr2]; simpl; auto.
  rewrite <- IHtr1; rewrite <- IHtr2.
  destruct data as [data|]; simpl; auto.
  destruct data; simpl; auto.
  all: destruct (join_nodes tr1) as [res1|]; simpl; auto.
  all: destruct (join_nodes tr2) as [res2|]; simpl; auto.
  destruct (join_nodes res1); simpl; auto.
Qed.

Lemma join_nodes_omap_comm {X Y} (fn:X -> Y) :
  forall (tr:tree (option X)),
  join_nodes (map_nodes (option_map fn) tr) = option_map (map_nodes fn) (join_nodes tr).
Proof.
  intro tr. induction tr as [|data tr1 IHtr1 tr2 IHtr2]; simpl; auto.
  rewrite IHtr1; rewrite IHtr2; simpl.
  destruct data; simpl; auto.
  destruct (join_nodes tr1); simpl; auto.
  destruct (join_nodes tr2); simpl; auto.
Qed.

Lemma map_nodes_compose {W X Y} (fn:W -> X) (fn':X -> Y) :
  forall (tr:tree W),
  map_nodes fn' (map_nodes fn tr) = map_nodes (compose fn' fn) tr.
Proof.
  intro tr. induction tr as [|data tr1 IHtr1 tr2 IHtr2]; simpl; auto.
  rewrite IHtr1. rewrite IHtr2; reflexivity.
Qed.

Lemma join_nodes_delay {X Y} (fn:X -> option Y) :
  forall (tr:tree (option X)),
  join_nodes (map_nodes (option_bind fn) tr) = option_bind (compose join_nodes (map_nodes fn)) (join_nodes tr).
Proof.
  intro tr.
  rewrite option_bind_map_join.
  rewrite option_bind_map_join.
  rewrite <- map_nodes_compose.
  rewrite <- join_join_nodes.
  rewrite join_nodes_omap_comm.
  rewrite option_bind_map_join.
  unfold compose.
  rewrite option_map_compose.
  f_equal.
Qed.

Lemma join_success_condition {X} (tr:tree (option X)) :
  is_Some (join_nodes tr) <-> every_node is_Some tr.
Proof.
  induction tr as [|data tr1 IHtr1 tr2 IHtr2]; simpl; split; auto.
  - intro Computation.
    option step in Computation as ?:?.
    option step in Computation as ?:?.
    option step in Computation as ?:?.
    injection Computation; intros; subst.
    rewrite <- IHtr1.
    rewrite <- IHtr2.
    done.
  - intro AllSuccess.
    destruct AllSuccess as [DataSome [Success1 Success2]].
    destruct DataSome as [? H]; rewrite H; clear H; simpl.
    destruct (proj2 IHtr1 Success1) as [? H]; rewrite H; clear H; simpl.
    destruct (proj2 IHtr2 Success2) as [? H]; rewrite H; clear H; simpl.
    auto.
Qed.

Lemma join_fail_condition {X} (tr:tree (option X)) :
  join_nodes tr = None <-> exists_node (λ x, x = None) tr.
Proof.
  induction tr as [|[data|] tr1 IHtr1 tr2 IHtr2]; simpl; split; try done; try auto.
  - destruct (join_nodes tr1); last first.
    { intros _. right. left. apply IHtr1. done. }
    simpl. destruct (join_nodes tr2); last first.
    { intros _. right. right. apply IHtr2. done. }
    simpl. done.
  - intros [[=]|[H1%IHtr1|H2%IHtr2]].
    1: rewrite H1; done.
    rewrite H2. simpl. by destruct (join_nodes tr1). 
Qed.

Lemma every_subtree_eqv_universal {X} prop tr :
  every_subtree prop tr <-> (forall (br:tbranch X), exists_subtree ((=) br) tr -> prop br).
Proof.
  induction tr as [|data tr1 IHtr1 tr2 IHtr2]; simpl; [split; [intros; contradiction|tauto]|].
  rewrite IHtr1. rewrite IHtr2.
  split; intro Hyp; try repeat split.
  - destruct Hyp as [Hyp0 [Hyp1 Hyp2]].
    intros br Eq.
    destruct Eq as [Eq0 | [Eq1 | Eq2]]; subst; auto.
  - apply Hyp; left; auto.
  - intros br Eq; apply Hyp; right; left; assumption.
  - intros br Eq; apply Hyp; right; right; assumption.
Qed.

Lemma exists_subtree_eqv_existential {X} prop tr :
  exists_subtree prop tr <-> (exists (br:tbranch X), exists_subtree ((=) br) tr /\ prop br).
Proof.
  induction tr as [|data tr1 IHtr1 tr2 IHtr2]; simpl; [split; [tauto|intro Hyp; destruct Hyp as [_ [Contra _]]; tauto]|].
  rewrite IHtr1. rewrite IHtr2.
  split; intro Hyp.
  - destruct Hyp as [Hyp0 | [Hyp1 | Hyp2]].
    * eexists; auto.
    * destruct Hyp1 as [x [Ex Px]].
      exists x; auto.
    * destruct Hyp2 as [x [Ex Px]].
      exists x; auto.
  - destruct Hyp as [x [[Hyp0 | [Hyp1 | Hyp2]] Px]].
    * left; subst; auto.
    * right; left; exists x; auto.
    * right; right; exists x; auto.
Qed.

Lemma exists_node_iff_exists_root {X} prop (tr:tree X) :
  exists_node prop tr <-> exists_subtree (compose prop root) tr.
Proof. induction tr; simpl; auto. Qed.

Lemma every_node_iff_every_root {X} prop (tr:tree X) :
  every_node prop tr <-> every_subtree (compose prop root) tr.
Proof. induction tr; simpl; auto. Qed.

(* NOTE: Yes, the proof is identical to that of every_subtree_eqv_universal,
   but it does not seem to be provable from it. Indeed the precondition
   `exists_node ((=) n) tr` is *much weaker* than `exists_subtree ((=) br) tr` *)
Lemma every_node_eqv_universal {X} prop tr :
  every_node prop tr <-> (forall (n:X), exists_node ((=) n) tr -> prop n).
Proof.
  induction tr as [|data tr1 IHtr1 tr2 IHtr2]; simpl; [split; [intros; contradiction|tauto]|].
  rewrite IHtr1. rewrite IHtr2.
  split; intro Hyp; try repeat split.
  - destruct Hyp as [Hyp0 [Hyp1 Hyp2]].
    intros br Eq.
    destruct Eq as [Eq0 | [Eq1 | Eq2]]; subst; auto.
  - apply Hyp; left; auto.
  - intros br Eq; apply Hyp; right; left; assumption.
  - intros br Eq; apply Hyp; right; right; assumption.
Qed.

Lemma exists_node_eqv_existential {X} prop tr :
  exists_node prop tr <-> (exists (n:X), exists_node ((=) n) tr /\ prop n).
Proof.
  induction tr as [|data tr1 IHtr1 tr2 IHtr2]; simpl; [split; [tauto|intro Hyp; destruct Hyp as [_ [Contra _]]; tauto]|].
  rewrite IHtr1. rewrite IHtr2.
  split; intro Hyp.
  - destruct Hyp as [Hyp0 | [Hyp1 | Hyp2]].
    * eexists; auto.
    * destruct Hyp1 as [x [Ex Px]].
      exists x; auto.
    * destruct Hyp2 as [x [Ex Px]].
      exists x; auto.
  - destruct Hyp as [x [[Hyp0 | [Hyp1 | Hyp2]] Px]].
    * left; subst; auto.
    * right; left; exists x; auto.
    * right; right; exists x; auto.
Qed.

Lemma tree_permute_fold_map {X Y Z} (tr:tree X) (unit:Z) (combine:Y -> Z -> Z -> Z) (fn:X -> Y) :
  fold_nodes unit combine (map_nodes fn tr) = fold_nodes unit (fun data lt rt => combine (fn data) lt rt) tr.
Proof.
  induction tr as [|data tr1 IHtr1 tr2 IHtr2]; simpl; auto.
  rewrite IHtr1. rewrite IHtr2.
  reflexivity.
Qed.

Lemma every_node_map {X Y} (tr:tree X) (fn:X -> Y) (prop:Y -> Prop) :
  every_node prop (map_nodes fn tr) <-> every_node (compose prop fn) tr.
Proof.
  unfold every_node.
  rewrite tree_permute_fold_map.
  tauto.
Qed.

Lemma exists_node_map {X Y} (tr:tree X) (fn:X -> Y) (prop:Y -> Prop) :
  exists_node prop (map_nodes fn tr) <-> exists_node (compose prop fn) tr.
Proof.
  unfold exists_node.
  rewrite tree_permute_fold_map.
  tauto.
Qed.

Lemma every_not_eqv_not_exists {X} (prop:X -> Prop) (tr:tree X) :
  every_node (compose not prop) tr
  <-> ~exists_node prop tr.
Proof.
  unfold every_node.
  split.
  - intros All Exists.
    induction tr; simpl; auto.
    inversion Exists as [Ex0 | [Ex1 | Ex2]]; simpl.
    all: inversion All as [All0 [All1 All2]]; auto.
  - intros nExists.
    induction tr as [|data tr1 IHtr1 tr2 IHtr2]; simpl; auto.
    try repeat split.
    (* Now swap the goal and the hypothesis that are all negated *)
    all: try apply IHtr1.
    all: try apply IHtr2.
    all: intro; apply nExists.
    all: simpl; auto.
Qed.

Lemma insert_true_preserves_every {X} (tr:tree X) (ins:X) (search prop:X -> Prop)
  {search_dec:forall x, Decision (search x)} :
  prop ins ->
  every_node prop tr <-> every_node prop (insert_child_at tr ins search).
Proof.
  intro PropIns.
  induction tr as [|data tr1 IHtr1 tr2 IHtr2]; simpl; auto.
  destruct (decide (search data)) eqn:Found.
  (* For most cases, this is straightforward: destruct all and apply inductive hypotheses *)
  all: split; intro H.
  all: destruct H as [HData [H1 H2]].
  all: repeat try split; auto.
  all: try apply IHtr1; auto.
  all: try apply IHtr2; auto.
  (* The one case where this is nontrivial is the case where we did find the object,
     because IH handles (branch data sibling child) and we need (branch data (insert sibling) child) *)
  inversion H2 as [HIns [H2' HE]]; auto.
Qed.

Lemma insert_never_unchanged {X} (tr:tree X) (ins:X) (search prop:X -> Prop)
  {search_dec:forall x, Decision (search x)} :
  every_node (compose not search) tr ->
  insert_child_at tr ins search = tr.
Proof.
  induction tr as [|data tr1 IHtr1 tr2 IHtr2]; simpl; auto; intro H.
  destruct H as [H0 [H1 H2]].
  destruct (decide (search data)); [contradiction|].
  rewrite (IHtr1 H1).
  rewrite (IHtr2 H2).
  reflexivity.
Qed.

Lemma insert_preserves_exists {X} (ins:X) (tr:tree X) (search prop:X -> Prop)
  {search_dec:forall x, Decision (search x)} :
  exists_node prop tr -> exists_node prop (insert_child_at tr ins search).
Proof.
  intros Exists.
  induction tr as [|data tr1 IHtr1 tr2 IHtr2]; simpl; auto.
  destruct (decide (search data)).
  all: simpl.
  all: inversion Exists as [Ex0 | [Ex1 | Ex2]].
  all: auto.
  right; right; right; left; auto.
Qed.

Lemma exists_sibling_insert {X} (ins:X) (tr:tree X) (search prop:X -> Prop)
  {search_dec:forall x, Decision (search x)} :
  exists_sibling prop tr ↔ exists_sibling prop (insert_child_at tr ins search).
Proof.
  induction tr as [|data tr1 IHtr1 tr2 IHtr2]; simpl; auto.
  destruct (decide (search data)); simpl.
  all: rewrite IHtr1 //.
Qed.

Lemma insert_false_infer_exists {X} (ins:X) (tr:tree X) (search prop:X -> Prop)
  {search_dec:forall x, Decision (search x)} :
  ~prop ins ->
  exists_node prop (insert_child_at tr ins search) ->
  exists_node prop tr.
Proof.
  intros nIns Exists.
  induction tr as [|data tr1 IHtr1 tr2 IHtr2]; simpl; auto.
  simpl in Exists.
  destruct (decide (search data)).
  all: inversion Exists as [Ex0 | [Ex1 | Ex2]].
  all: auto.
  right; right; auto.
  inversion Ex2 as [Ex20 | [Ex21 | Ex22]]; auto.
  - contradiction Ex20.
  - contradiction Ex22.
Qed.

Lemma insert_true_produces_exists {X} (ins:X) (tr:tree X) (search prop:X -> Prop)
  {search_dec:forall x, Decision (search x)} :
  prop ins ->
  exists_node search tr ->
  exists_node prop (insert_child_at tr ins search).
Proof.
  intros Ins Exists.
  induction tr as [|data tr1 IHtr1 tr2 IHtr2]; simpl; auto.
  destruct (decide (search data)).
  - right; right; left; done.
  - destruct Exists as [Ex0 | [Ex1 | Ex2]].
    * contradiction.
    * right; left; auto.
    * right; right; auto.
Qed.

Lemma exists_insert_requires_parent {X} (ins:X) (search prop:X -> Prop)
  {search_dec:forall x, Decision (search x)} :
  forall tr,
  every_node (compose not prop) tr ->
  exists_node prop (insert_child_at tr ins search) ->
  exists_node search tr.
Proof.
  intro tr.
  induction tr as [|data tr1 IHtr1 tr2 IHtr2]; simpl; auto.
  intros Hyp Ex.
  destruct Hyp as [Nprop [Absent1 Absent2]].
  destruct (decide (search data)) eqn:Found; auto.
  all: destruct Ex as [Here | [Ex1 | Ex2]]; auto.
  contradiction.
Qed.

Lemma remove_false_preserves_exists {X} (ins:X) (search prop:X -> Prop)
  {search_dec:forall x, Decision (search x)} :
  ~prop ins ->
  forall tr,
  exists_node prop (insert_child_at tr ins search) ->
  exists_node prop tr.
Proof.
  intros Nprop tr Hyp; induction tr as [|data tr1 IHtr1 tr2 IHtr2]; simpl in *; auto.
  destruct (decide (search data)) eqn:Found; auto.
  all: destruct Hyp as [Here | [Hyp1 | Hyp2]]; auto.
  right; right. destruct Hyp2 as [Contra | [Hyp2Sub | Hyp2Empty]]; auto; contradiction.
Qed.

Lemma exists_subtree_transitive T br prop (tr:tree T) :
  exists_subtree (eq br) tr ->
  exists_subtree prop (of_branch br) ->
  exists_subtree prop tr.
Proof.
  induction tr as [|data tr1 IHtr1 tr2 IHtr2]; simpl; auto.
  intros Sub1 Sub2.
  destruct Sub1 as [Sub10 | [Sub11 | Sub12]].
  - destruct br as [[iroot ileft] iright]; simpl in *.
    injection Sub10; intros; subst; auto.
  - right; left. apply IHtr1; auto.
  - right; right. apply IHtr2; auto.
Qed.

Lemma every_subtree_transitive T br prop (tr:tree T) :
  every_subtree (eq br) tr ->
  every_subtree prop (of_branch br) ->
  every_subtree prop tr.
Proof.
  induction tr as [|data tr1 IHtr1 tr2 IHtr2]; simpl; auto.
  intros Sub1 Sub2.
  destruct Sub1 as [Sub10 [Sub11 Sub12]].
  destruct br as [[iroot ileft] iright].
  injection Sub10; intros; subst.
  destruct Sub2 as [Sub20 [Sub21 Sub22]].
  try repeat split; auto.
Qed.

Lemma exists_node_transitive T br prop (tr:tree T) :
  exists_subtree (eq br) tr ->
  exists_node prop (of_branch br) ->
  exists_node prop tr.
Proof.
  repeat rewrite exists_node_iff_exists_root.
  apply exists_subtree_transitive.
Qed.

(*
Lemma strict_child_of_exists_exists br prop (tr:tree item) :
  exists_subtree (eq br) tr ->
  exists_strict_child prop br ->
  exists_node prop tr.
  *)

Lemma join_project_exists {X} tr prop :
  forall tr',
  join_nodes tr = Some tr' ->
  exists_node prop tr' <-> exists_node (fun x => exists (v:X), x = Some v /\ prop v) tr.
Proof.
  induction tr as [|data tr1 IHtr1 tr2 IHtr2]; intros tr' JoinSome.
  - simpl in JoinSome; injection JoinSome; intros; subst; tauto.
  - option step in JoinSome as ?:?.
    option step in JoinSome as ?:?.
    option step in JoinSome as ?:?.
    injection JoinSome; intros; subst.
    simpl.
    split; intro H; destruct H as [H0|[?|?]].
    * left. eexists; tauto.
    * right; left. rewrite <- IHtr1; eauto.
    * right; right. rewrite <- IHtr2; eauto.
    * left. destruct H0 as [?[SomeV ?]]; injection SomeV; intros; subst; auto.
    * right; left. rewrite IHtr1; auto.
    * right; right. rewrite IHtr2; auto.
Qed.

Lemma join_project_every {X} tr prop :
  forall tr',
  join_nodes tr = Some tr' ->
  every_node prop tr' <-> every_node (fun x => exists (v:X), x = Some v /\ prop v) tr.
Proof.
  induction tr as [|? ? IHtr1 ? IHtr2]; intros tr' JoinSome.
  - injection JoinSome; intros; subst; tauto.
  - option step in JoinSome as ?:?.
    option step in JoinSome as ?:?.
    option step in JoinSome as ?:?.
    injection JoinSome; intros; subst.
    simpl.
    split; intro H; try repeat split.
    all: destruct H as [H[??]].
    * eexists; easy.
    * rewrite <- IHtr1; [|eauto]; done.
    * rewrite <- IHtr2; [|eauto]; done.
    * destruct H as [?[H?]]; injection H; intros; subst; auto.
    * rewrite IHtr1; done.
    * rewrite IHtr2; done.
Qed.

Lemma destruct_joined {X} (data:option X) (tr1 tr2:tree (option X)) tr' :
  join_nodes (branch data tr1 tr2) = Some tr' ->
  exists data' tr1' tr2', (
    tr' = branch data' tr1' tr2'
    /\ data = Some data'
    /\ join_nodes tr1 = Some tr1'
    /\ join_nodes tr2 = Some tr2'
  ).
Proof.
  intros Join.
  option step in Join as ?:?.
  option step in Join as ?:?.
  option step in Join as ?:?.
  injection Join; intros; subst.
  do 3 eexists.
  try repeat split; eassumption.
Qed.

Lemma exists_node_increasing {X} (prop prop':X -> Prop) tr :
  exists_node prop tr ->
  every_node (fun x => prop x -> prop' x) tr ->
  exists_node prop' tr.
Proof.
  induction tr as [|?? IHtr1 ? IHtr2]; simpl; [tauto|].
  intros H Impl; destruct Impl as [Impl0 [Impl1 Impl2]]; destruct H as [H0 | [H1 | H2]].
  - left; apply Impl0; auto.
  - right; left; apply IHtr1; auto.
  - right; right; apply IHtr2; auto.
Qed.

Lemma every_node_increasing {X} (prop prop':X -> Prop) tr :
  every_node prop tr ->
  every_node (fun x => prop x -> prop' x) tr ->
  every_node prop' tr.
Proof.
  repeat rewrite every_node_eqv_universal.
  intros Pre Trans x Ex.
  apply Trans; [exact Ex|].
  apply Pre.
  exact Ex.
Qed.

Lemma join_map_preserves_exists {X} (tr tr':tree X) (prop:X -> Prop) :
  forall fn,
  (forall x y, fn x = Some y -> prop x <-> prop y) ->
  join_nodes (map_nodes fn tr) = Some tr' ->
  exists_node prop tr <-> exists_node prop tr'.
Proof.
  move=> ? Preserves JoinMap.
  generalize dependent tr'.
  induction tr as [|?? IHtr1 ? IHtr2]; [simpl; move=> ? H; injection H; intros; subst; tauto|].
  intros tr' JoinMap.
  destruct (destruct_joined _ _ _ _ JoinMap) as [data' [tr1' [tr2' [EqTr' [EqData' [EqTr1' EqTr2']]]]]]; subst.
  simpl.
  erewrite IHtr1; [|eassumption].
  erewrite IHtr2; [|eassumption].
  rewrite Preserves; [|eassumption].
  tauto.
Qed.

Lemma join_map_preserves_exists_sibling {X} (tr tr':tree X) (prop:X -> Prop) :
  forall fn,
  (forall x y, fn x = Some y -> prop x <-> prop y) ->
  join_nodes (map_nodes fn tr) = Some tr' ->
  exists_sibling prop tr <-> exists_sibling prop tr'.
Proof.
  move=> ? Preserves JoinMap.
  generalize dependent tr'.
  induction tr as [|?? IHtr1 ? IHtr2]; [simpl; move=> ? H; injection H; intros; subst; tauto|].
  intros tr' JoinMap.
  destruct (destruct_joined _ _ _ _ JoinMap) as [data' [tr1' [tr2' [EqTr' [EqData' [EqTr1' EqTr2']]]]]]; subst.
  simpl.
  erewrite IHtr1; [|eassumption].
  rewrite Preserves; [|eassumption].
  tauto.
Qed.

Lemma exists_sibling_exists_node {X} tr (prop : X → Prop) :
  exists_sibling prop tr → exists_node prop tr.
Proof.
  induction tr as [|data tl IHl ? _]; first done.
  simpl. tauto.
Qed.

Lemma fold_immediate_children_at_count {X Y} p (ini:Y) fn (tr : tree X) :
  length (fold_immediate_children_at p ini fn tr)
= count_nodes p tr.
Proof.
  induction tr as [|x tr1 IH1 tr2 IH2]; first done.
  simpl. rewrite !length_app IH1 IH2. by destruct (p x).
Qed.


