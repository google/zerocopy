(** This file proves some simple reorderings directly against the operational semantics
    in sequential code.

    For example we prove here the fact that in any context, two adjacent read
    accesses can be swapped and the resulting state is identical to the initial state.
    Because these proofs use a different definition of bor_step and do not involve
    parallelism, the lemmas established here are *definitely not useful* for the rest
    of the project.

    Results proven here:
    * any pair of adjacent reads can be swapped to obtain an identical final state.
 *)
From iris.prelude Require Import prelude options.
From stdpp Require Export gmap.
From simuliris.tree_borrows Require Import lang_base notation bor_semantics tree tree_lemmas bor_lemmas steps_preserve defs.

Definition commutes {X}
  (fn1 fn2 : X -> option X)
  := forall x0 x1 x2,
  fn1 x0 = Some x1 ->
  fn2 x1 = Some x2 ->
  exists x1', (
    fn2 x0 = Some x1'
    /\ fn1 x1' = Some x2
  ).

Definition commutes_option {X}
  (fn1 fn2 : option X -> option X)
  := forall x0 x1 x2,
  fn1 x0 = Some x1 ->
  fn2 (Some x1) = Some x2 ->
  exists x1', (
    fn2 x0 = Some x1'
    /\ fn1 (Some x1') = Some x2
  ).

Definition persistent_if {X} (P : X -> Prop)
  (fn1 fn2 : X -> option X)
  := forall x x1 x2,
  P x ->
  fn1 x = Some x1 ->
  fn2 x = Some x2 ->
  exists x', fn2 x1 = Some x'.

Definition persistent_if_option {X} (P : option X -> Prop)
  (fn1 fn2 : option X -> option X)
  := forall x x1 x2,
  P x ->
  fn1 x = Some x1 ->
  fn2 x = Some x2 ->
  exists x', fn2 (Some x1) = Some x'.

Lemma apply_access_perm_read_commutes
  {rel1 rel2 prot}
  : commutes
    (apply_access_perm AccessRead rel1 prot)
    (apply_access_perm AccessRead rel2 prot).
Proof.
  move=> p0 p1 p2 Step01 Step12.
  unfold apply_access_perm in *.
  all: destruct p0 as [[] [|[]| | | | ]].
  all: destruct prot; simpl in *.
  all: destruct rel1; simpl in *.
  all: try (inversion Step01; done).
  all: injection Step01; intros; subst.
  all: simpl.
  all: destruct rel2; simpl in *.
  all: try (inversion Step12; done).
  all: injection Step12; intros; subst; simpl.
  all: try (eexists; split; [reflexivity|]); simpl.
  all: reflexivity.
Qed.

Lemma apply_access_perm_read_persistent
  {rel1 rel2 prot}
  : persistent_if lazy_perm_wf
    (apply_access_perm AccessRead rel1 prot)
    (apply_access_perm AccessRead rel2 prot).
Proof.
  move=> p0 p1 p2 wf Step01 Step12.
  unfold apply_access_perm in *.
  all: destruct p0 as [[] [|[]| | | | ]].
  all: destruct prot; simpl in *.
  all: destruct rel1; simpl in *.
  all: try (inversion Step01; done).
  all: injection Step01; intros; subst.
  all: simpl.
  all: destruct rel2; simpl in *.
  all: try (inversion Step12; done).
  all: injection Step12; intros; subst; simpl.
  all: try (eexists; reflexivity).
  (* Only the non-wf cases remain *)
  - rewrite /lazy_perm_wf in wf; simpl in *. exfalso.
    specialize (wf ltac:(auto)). discriminate.
  - rewrite /lazy_perm_wf in wf; simpl in *. exfalso.
    specialize (wf ltac:(auto)). discriminate.
Qed.

Lemma mem_apply_loc_insert_ne
  {X} {fn : option X -> option X} {z mem mem' z0}
  (NE : ~z = z0)
  (Success : mem_apply_loc fn z mem = Some mem')
  v0
  : mem_apply_loc fn z (<[z0:=v0]>mem) = Some (<[z0:=v0]>mem').
Proof.
  unfold mem_apply_loc in Success |- *; simpl in *.
  rewrite lookup_insert_ne; [|auto].
  destruct (option_bind_success_step _ _ _ Success) as [v [fnv mem'_spec]].
  injection mem'_spec; intros; subst.
  rewrite fnv; simpl.
  f_equal.
  rewrite insert_insert_ne; auto.
Qed.

Lemma mem_apply_range'_insert_outside
  {X} {fn : option X -> option X} {z sz mem mem' z0}
  (OUT : ~range'_contains (z, sz) z0)
  (Success : mem_apply_locs fn z sz mem = Some mem')
  v0
  : mem_apply_locs fn z sz (<[z0:=v0]>mem) = Some (<[z0:=v0]>mem').
Proof.
  unfold mem_apply_range' in *; simpl in *.
  generalize dependent z.
  generalize dependent mem.
  generalize dependent mem'.
  induction sz as [|sz IHsz]; move=> mem' mem z OUT Success.
  - injection Success; intros; subst.
    reflexivity.
  - destruct (proj1 (bind_Some _ _ _) Success) as [mem'' [SuccessStep SuccessRest]].
    simpl.
    erewrite mem_apply_loc_insert_ne; [| |eassumption].
    2: { unfold range'_contains in OUT |- *; simpl in *; lia. }
    simpl.
    apply IHsz.
    + unfold range'_contains in OUT |- *; simpl in *; lia.
    + exact SuccessRest.
Qed.

Lemma mem_apply_range'_success_condition
  {X} {fn : option X -> option X} {range mem}
  (ALL_SOME : forall z, range'_contains range z -> is_Some (fn (mem !! z)))
  : exists mem', mem_apply_range' fn range mem = Some mem'.
Proof.
  unfold mem_apply_range'.
  destruct range as [z sz]; simpl.
  generalize dependent z.
  induction sz as [|sz IHsz]; move=> z ALL_SOME.
  - eexists. simpl. reflexivity.
  - destruct (IHsz (z + 1)%Z
      ltac:(intros mem' H; apply ALL_SOME; unfold range'_contains; unfold range'_contains in H; simpl; simpl in H; lia))
      as [sub' Specsub'].
    destruct (ALL_SOME z ltac:(unfold range'_contains; simpl; lia)) as [fnz Specfnz].
    eexists (<[z:=fnz]>sub'); simpl.
    unfold mem_apply_loc.
    rewrite Specfnz; simpl.
    erewrite mem_apply_range'_insert_outside; [reflexivity| |assumption].
    unfold range'_contains; simpl; lia.
Qed.

Lemma mem_apply_range'_success_specification
  {X} {fn : option X -> option X} {range mem mem'}
  (ALL_SOME : forall z, range'_contains range z -> exists x', fn (mem !! z) = Some x' /\ mem' !! z = Some x')
  (REST_SAME : forall z, ~range'_contains range z -> mem !! z = mem' !! z)
  : mem_apply_range' fn range mem = Some mem'.
Proof.
  assert (forall z, range'_contains range z -> is_Some (fn (mem !! z))) as ALL_SOME_weaker. {
    intros z R; destruct (ALL_SOME z R) as [?[??]]; auto.
  }
  destruct (mem_apply_range'_success_condition ALL_SOME_weaker) as [mem'' Spec''].
  rewrite Spec''; f_equal; apply map_eq.
  intro z.
  pose proof (mem_apply_range'_spec _ _ z _ _ Spec'') as Spec.
  destruct (decide (range'_contains range z)) as [R|nR].
  - destruct Spec as [v[vSpec fnvSpec]].
    destruct (ALL_SOME z R) as [v' [fnv'Spec v'Spec]].
    rewrite v'Spec.
    rewrite vSpec.
    rewrite <- fnv'Spec.
    rewrite <- fnvSpec.
    reflexivity.
  - rewrite <- (REST_SAME z nR).
    assumption.
Qed.

Lemma range_foreach_commutes
  {X}
  range1 range2
  (fn1 fn2 : option X -> option X)
  (FnCommutes : commutes_option fn1 fn2)
  : commutes
    (mem_apply_range' fn1 range1)
    (mem_apply_range' fn2 range2).
Proof.
  intros mem0 mem1 mem2 Success01 Success12.
  assert (forall z, range'_contains range2 z -> exists x1', fn2 (mem0 !! z) = Some x1') as fn2mem0. {
    intros z R2.
    pose proof (mem_apply_range'_spec _ _ z _ _ Success01) as Spec01.
    pose proof (mem_apply_range'_spec _ _ z _ _ Success12) as Spec12.
    destruct (decide (range'_contains range1 z)).
    - destruct Spec01 as [fn1z0 [z1Spec fn1z0Spec]].
      rewrite decide_True in Spec12; [|assumption].
      destruct Spec12 as [fn2z1 [z2Spec fn2z1Spec]].
      rewrite z1Spec in fn2z1Spec.
      destruct (FnCommutes _ _ _ fn1z0Spec fn2z1Spec) as [x1' [fn2z0Spec fn1x1'Spec]].
      exists x1'; assumption.
    - rewrite decide_True in Spec12; [|assumption].
      destruct Spec12 as [x2 [x2Spec fn2x1Spec]].
      exists x2; rewrite <- Spec01; assumption.
  }
  destruct (mem_apply_range'_success_condition fn2mem0) as [mem1' Success01'].
  exists mem1'.
  split; [assumption|].
  apply mem_apply_range'_success_specification.
  - intros z R1.
    pose proof (mem_apply_range'_spec _ _ z _ _ Success01) as Spec01.
    pose proof (mem_apply_range'_spec _ _ z _ _ Success12) as Spec12.
    pose proof (mem_apply_range'_spec _ _ z _ _ Success01') as Spec01'.
    destruct (decide (range'_contains range2 z)).
    + rewrite decide_True in Spec01; [|assumption].
      destruct Spec01 as [fn1z0 [z1Spec fn1z0Spec]].
      destruct Spec12 as [fn2z1 [z2Spec fn2z1Spec]].
      destruct Spec01' as [fn2z0 [z1'Spec fn2z0Spec]].
      rewrite z1Spec in fn2z1Spec.
      destruct (FnCommutes _ _ _ fn1z0Spec fn2z1Spec) as [x2' [fn2z0'Spec fn1x2'Spec]].
      rewrite z1'Spec.
      rewrite <- fn2z0Spec.
      exists fn2z1.
      split; [|assumption].
      destruct (FnCommutes _ _ _ fn1z0Spec fn2z1Spec) as [x1' [fn2z0Spec' fn1x1'Spec]].
      rewrite fn2z0Spec'.
      rewrite fn1x1'Spec.
      reflexivity.
    + rewrite decide_True in Spec01; [|assumption].
      destruct Spec01 as [fn1z0 [z1Spec fn1z0Spec]].
      rewrite Spec01'.
      rewrite Spec12.
      exists fn1z0; split; assumption.
  - intros z nR1.
    pose proof (mem_apply_range'_spec _ _ z _ _ Success01) as Spec01.
    pose proof (mem_apply_range'_spec _ _ z _ _ Success01') as Spec01'.
    pose proof (mem_apply_range'_spec _ _ z _ _ Success12) as Spec12.
    destruct (decide (range'_contains range2 z)).
    + rewrite decide_False in Spec01; [|assumption].
      destruct Spec01' as [fn2z0 [z1'Spec fn2z0Spec]].
      destruct Spec12 as [fn2z1 [z2Spec fn2z1Spec]].
      rewrite z1'Spec.
      rewrite <- fn2z0Spec.
      rewrite <- Spec01.
      rewrite fn2z1Spec.
      rewrite z2Spec.
      reflexivity.
    + rewrite decide_False in Spec01; [|assumption].
      rewrite Spec01'.
      rewrite <- Spec01.
      rewrite Spec12.
      reflexivity.
Qed.

Definition if_some_then {X} (P : X -> Prop) o :=
  match o with
  | None => True
  | Some x => P x
  end.

Lemma range_foreach_persistent
  {X}
  P
  range1 range2
  (fn1 fn2 : option X -> option X)
  (FnCommutes : persistent_if_option (if_some_then P) fn1 fn2)
  : persistent_if (fun m => forall i, if_some_then P (m !! i))
    (mem_apply_range' fn1 range1)
    (mem_apply_range' fn2 range2).
Proof.
  intros mem0 mem1 mem2 Wf Success01 Success12.
  assert (forall z, range'_contains range2 z -> exists x', fn2 (mem1 !! z) = Some x') as fn2mem1. {
    intros z R2.
    pose proof (mem_apply_range'_spec _ _ z _ _ Success01) as Spec01.
    pose proof (mem_apply_range'_spec _ _ z _ _ Success12) as Spec12.
    destruct (decide (range'_contains range1 z)).
    - destruct Spec01 as [fn1z0 [z1Spec fn1z0Spec]].
      rewrite decide_True in Spec12; [|assumption].
      pose proof (Wf z) as wfz.
      destruct Spec12 as [fn2z1 [z2Spec fn2z1Spec]].
      destruct (FnCommutes _ _ _ wfz fn1z0Spec fn2z1Spec) as [x1' fn2z0Spec].
      exists x1'; rewrite z1Spec; assumption.
    - rewrite decide_True in Spec12; [|assumption].
      destruct Spec12 as [x2 [x2Spec fn2x1Spec]].
      exists x2; rewrite Spec01; assumption.
  }
  destruct (mem_apply_range'_success_condition fn2mem1) as [mem1' Success01'].
  exists mem1'. assumption.
Qed.

Lemma commutes_option_build
  {X} {dflt : X} {fn1 fn2}
  (Commutes : commutes fn1 fn2)
  : commutes_option
    (fun ox => fn1 (default dflt ox))
    (fun ox => fn2 (default dflt ox)).
Proof.
  intros x0 x1 x2 Step01 Step12.
  destruct (Commutes (default dflt x0) _ _ Step01 Step12) as [?[??]].
  eexists; eauto.
Qed.

Lemma persistent_if_option_build
  {X} {dflt : X} P {fn1 fn2}
  (Commutes : persistent_if P fn1 fn2)
  (Base : P dflt)
  : persistent_if_option (if_some_then P)
    (fun ox => fn1 (default dflt ox))
    (fun ox => fn2 (default dflt ox)).
Proof.
  intros x0 x1 x2 Pre Step01 Step12.
  destruct x0; simpl in *.
  - destruct (Commutes _ _ _ Pre Step01 Step12) as [? ?].
    eexists; eassumption.
  - destruct (Commutes _ _ _ Base Step01 Step12) as [? ?].
    eexists; eassumption.
Qed.

Lemma permissions_foreach_commutes
  range1 range2
  (fn1 fn2 : lazy_permission -> option lazy_permission)
  dflt
  (FnCommutes : commutes fn1 fn2)
  : commutes
    (permissions_apply_range' dflt range1 fn1)
    (permissions_apply_range' dflt range2 fn2).
Proof.
  apply range_foreach_commutes.
  apply commutes_option_build.
  assumption.
Qed.

Lemma permissions_foreach_persistent
  P
  range1 range2
  (fn1 fn2 : lazy_permission -> option lazy_permission)
  dflt
  (FnCommutes : persistent_if P fn1 fn2)
  (Base : P dflt)
  : persistent_if (fun m => forall i, if_some_then P (m !! i))
    (permissions_apply_range' dflt range1 fn1)
    (permissions_apply_range' dflt range2 fn2).
Proof.
  apply range_foreach_persistent.
  apply persistent_if_option_build.
  - assumption.
  - assumption.
Qed.

Lemma item_apply_access_read_commutes
  {cids rel1 rel2 range1 fn1 fn2 range2}
  (FnCommutes : forall isprot,
    commutes
      (fn1 rel1 isprot)
      (fn2 rel2 isprot))
  : commutes
    (item_apply_access fn1 cids rel1 range1)
    (item_apply_access fn2 cids rel2 range2).
Proof.
  intros it0 it1 it2 Step01 Step12.
  option step in Step01 as ?:S1.
  option step in Step12 as ?:S2.
  injection Step01; destruct it1 as [??? iperm1]; intro H; injection H; intros; subst; simpl in *; clear Step01; clear H.
  injection Step12; destruct it2 as [??? iperm2]; intro H; injection H; intros; subst; simpl in *; clear Step12; clear H.
  destruct (permissions_foreach_commutes
    range1 range2
    (fn1 _ _) (fn2 _ _)
    {| initialized:=PermLazy; perm:=initp it0 |}
    (FnCommutes _) 
    (*(apply_access_perm_read_commutes (rel1:=rel1) (rel2:=rel2) (prot:=bool_decide (protector_is_active (iprot it0) cids)))*)
    (iperm it0) iperm1 iperm2
    S1 S2) as [perms' [Pre Post]].
  unfold item_apply_access.
  rewrite Pre; simpl.
  eexists; split; [reflexivity|].
  simpl. rewrite Post; simpl.
  reflexivity.
Qed.

Lemma item_apply_access_read_persistent
  {cids rel1 rel2 range1 fn1 fn2 range2}
  (FnCommutes : forall isprot,
    persistent_if lazy_perm_wf
      (fn1 rel1 isprot)
      (fn2 rel2 isprot))
  : persistent_if (fun it => exists nxtc nxtp, item_wf it nxtc nxtp)
    (item_apply_access fn1 cids rel1 range1)
    (item_apply_access fn2 cids rel2 range2).
Proof.
  intros it0 it1 it2 Pre Step01 Step12.
  option step in Step01 as ?:S1.
  option step in Step12 as ?:S2.
  injection Step01; destruct it1 as [??? iperm1]; intro H; injection H; intros; subst; simpl in *; clear Step01; clear H.
  injection Step12; destruct it2 as [??? iperm2]; intro H; injection H; intros; subst; simpl in *; clear Step12; clear H.
  destruct Pre as [nxtc [nxtp itWf]].
  assert (lazy_perm_wf {| initialized:=PermLazy; perm := initp it0 |}) as LazyWf. {
    rewrite /lazy_perm_wf /=.
    intro Absurd.
    exfalso. eapply itWf.(item_default_perm_valid it0 _ _). assumption.
  }
  assert (forall i, if_some_then lazy_perm_wf (iperm it0 !! i)) as InitWf. {
    pose proof (itWf.(item_perms_valid it0 _ _)) as AllWf.
    intro i.
    destruct (iperm it0 !! i) as [perm|] eqn:permSpec.
    2: simpl; done.
    simpl.
    apply (map_Forall_lookup_1 _ _ i perm AllWf permSpec).
  }
  destruct (permissions_foreach_persistent
    lazy_perm_wf
    range1 range2
    (fn1 _ _) (fn2 _ _)
    {| initialized:=PermLazy; perm:=initp it0 |}
    (FnCommutes _) 
    LazyWf
    (iperm it0) iperm1 iperm2
    InitWf
    S1 S2) as [perms' Res].
  unfold item_apply_access; simpl.
  eexists. rewrite Res; simpl.
  reflexivity.
Qed.

Lemma apply_access_success_condition
  {fn cids access_tag range tr}
  (ALL_SOME : every_node
    (fun it => is_Some (item_apply_access fn cids (rel_dec tr access_tag (itag it)) range it)) tr)
  : exists tr', tree_apply_access fn cids access_tag range tr = Some tr'.
Proof.
  assert (every_node is_Some (map_nodes (fun it => item_apply_access fn cids (rel_dec tr access_tag (itag it)) range it) tr)) as AllSomeMap by (rewrite every_node_map; assumption).
  destruct (proj2 (join_success_condition _) AllSomeMap).
  eexists; eassumption.
Qed.

Lemma join_map_commutes
  {fn1 fn2 : call_id_set -> rel_pos -> Z * nat -> item -> option item} {cids access_tag1 access_tag2 range1 range2}
  (Fn1PreservesTag : forall it it' cids rel range, fn1 cids rel range it = Some it' -> itag it = itag it')
  (Fn2PreservesTag : forall it it' cids rel range, fn2 cids rel range it = Some it' -> itag it = itag it')
  (Commutes : forall rel1 rel2, commutes
    (fn1 cids rel1 range1)
    (fn2 cids rel2 range2))
  (* We need the two [rel_dec] to refer to the same tree otherwise the proof would be much more difficult *)
  : forall (tr0:tree item),
    commutes
      (fun tr => join_nodes (map_nodes (fun it => fn1 cids (rel_dec tr0 access_tag1 it.(itag)) range1 it) tr))
      (fun tr => join_nodes (map_nodes (fun it => fn2 cids (rel_dec tr0 access_tag2 it.(itag)) range2 it) tr)).
Proof.
  intros tr tr0.
  induction tr0 as [|data0 left0 IHleft right0 IHright]; intros tr1 tr2 Step01 Step12.
  - simpl in Step01; injection Step01; intros; subst.
    simpl in Step12; injection Step12; intros; subst.
    exists tree.empty; simpl; tauto.
  - option step in Step01 as data1:Data01.
    option step in Step01 as left1:Left01.
    option step in Step01 as right1:Right01.
    injection Step01; intros; subst.
    option step in Step12 as data2:Data12.
    option step in Step12 as left2:Left12.
    option step in Step12 as right2:Right12.
    injection Step12; intros; subst.
    destruct (Commutes _ _ data0 data1 data2 Data01 Data12) as [data1' [Data01' Data1'2]].
    destruct (IHleft left1 left2 Left01 Left12) as [left1' [Left01' Left1'2]].
    destruct (IHright right1 right2 Right01 Right12) as [right1' [Right01' Right1'2]].
    exists (branch data1' left1' right1').
    simpl in *.
    assert (itag data0 = itag data1) as Tg01 by (eapply Fn1PreservesTag; eassumption).
    assert (itag data0 = itag data1') as Tg01' by (eapply Fn2PreservesTag; eassumption).
    rewrite Tg01; rewrite Data01'; simpl.
    rewrite Left01'; simpl.
    rewrite Right01'; simpl.
    rewrite <- Tg01'; rewrite Data1'2; simpl.
    rewrite Left1'2; simpl.
    rewrite Right1'2; simpl.
    tauto.
Qed.

Lemma join_map_persistent
  {fn1 fn2 : call_id_set -> rel_pos -> Z * nat -> item -> option item} {cids access_tag1 access_tag2 range1 range2}
  (Fn1PreservesTag : forall it it' cids rel range, fn1 cids rel range it = Some it' -> itag it = itag it')
  (Fn2PreservesTag : forall it it' cids rel range, fn2 cids rel range it = Some it' -> itag it = itag it')
  (Commutes : forall rel1 rel2, persistent_if (fun it => exists nxtp nxtc, item_wf it nxtp nxtc)
    (fn1 cids rel1 range1)
    (fn2 cids rel2 range2))
  (* We need the two [rel_dec] to refer to the same tree otherwise the proof would be much more difficult *)
  : forall (tr0:tree item),
    persistent_if (fun tr => exists nxtp nxtc, tree_items_compat_nexts tr nxtp nxtc)
      (fun tr => join_nodes (map_nodes (fun it => fn1 cids (rel_dec tr0 access_tag1 it.(itag)) range1 it) tr))
      (fun tr => join_nodes (map_nodes (fun it => fn2 cids (rel_dec tr0 access_tag2 it.(itag)) range2 it) tr)).
Proof.
  intros tr tr0 tr1 tr2 Pre.
  destruct Pre as [nxtp [nxtc AllWf]].
  revert tr1 tr2.
  induction tr0 as [|data0 left0 IHleft right0 IHright]; intros tr1 tr2 Step01 Step12.
  - simpl in Step01; injection Step01; intros; subst.
    simpl in Step12; injection Step12; intros; subst.
    exists tree.empty; simpl; tauto.
  - option step in Step01 as data1:Data01.
    option step in Step01 as left1:Left01.
    option step in Step01 as right1:Right01.
    injection Step01; intros; subst.
    option step in Step12 as data2:Data12.
    option step in Step12 as left2:Left12.
    option step in Step12 as right2:Right12.
    injection Step12; intros; subst.
    inversion AllWf as [RootWf [LeftWf RightWf]].
    destruct (Commutes _ _ data0 data1 data2 ltac:(eexists; eexists; exact RootWf) Data01 Data12) as [data1' Res].
    destruct (IHleft LeftWf left1 left2 Left01 Left12) as [left1' LeftRes].
    destruct (IHright RightWf right1 right2 Right01 Right12) as [right1' RightRes].
    exists (branch data1' left1' right1').
    simpl in *.
    assert (itag data0 = itag data1) as Tg01 by (eapply Fn1PreservesTag; eassumption).
    rewrite -Tg01; rewrite Res; simpl.
    rewrite LeftRes.
    rewrite RightRes.
    simpl.
    reflexivity.
Qed.

Lemma tree_apply_access_only_cares_about_rel
  {tr} {fn : call_id_set -> rel_pos -> Z * nat -> item -> option item} {cids access_tag range}
  {tr1 tr2}
  (Agree : forall tg tg', ParentChildIn tg tg' tr1 <-> ParentChildIn tg tg' tr2)
  (RAgree : forall tg tg', ImmediateParentChildIn tg tg' tr1 <-> ImmediateParentChildIn tg tg' tr2)
  : join_nodes (map_nodes (fun it => fn cids (rel_dec tr1 access_tag it.(itag)) range it) tr)
  = join_nodes (map_nodes (fun it => fn cids (rel_dec tr2 access_tag it.(itag)) range it) tr).
Proof.
  induction tr as [|data sibling IHsibling child IHchild]; [simpl; reflexivity|].
  simpl.
  rewrite IHsibling; clear IHsibling.
  rewrite IHchild; clear IHchild.
  unfold rel_dec.
  f_equal. f_equal.
  destruct (decide (ParentChildIn _ _ _)) as [R1|R1].
  all: destruct (decide (ParentChildIn _ _ _)) as [R1'|R1'].
  all: destruct (decide (ParentChildIn _ _ _)) as [R2|R2].
  all: destruct (decide (ParentChildIn _ _ _)) as [R2'|R2'].
  all: try reflexivity.
  all: rewrite <- Agree in R2'; auto; try contradiction.
  all: rewrite <- Agree in R2; auto; try contradiction.
  all: erewrite decide_ext; last apply RAgree.
  all: done.
Qed.

Lemma tree_apply_access_commutes
  {fn1 fn2 cids access_tag1 access_tag2 range1 range2}
  (Commutes : forall rel1 rel2, commutes
    (item_apply_access fn1 cids rel1 range1)
    (item_apply_access fn2 cids rel2 range2))
  : commutes
    (fun tr => tree_apply_access fn1 cids access_tag1 range1 tr)
    (fun tr => tree_apply_access fn2 cids access_tag2 range2 tr).
Proof.
  unfold tree_apply_access.
  intros tr0 tr1 tr2 Step01 Step12.
  assert (forall (it it' : item) (cids : call_id_set) (rel : rel_pos) (range : Z * nat),
     item_apply_access fn1 cids rel range it = Some it'
     → itag it = itag it') as Fn1PreservesTag. {
      intros. eapply item_apply_access_preserves_metadata. eassumption.
  }
  assert (forall (it it' : item) (cids : call_id_set) (rel : rel_pos) (range : Z * nat),
     item_apply_access fn2 cids rel range it = Some it'
     → itag it = itag it') as Fn2PreservesTag. {
      intros. eapply item_apply_access_preserves_metadata. eassumption.
  }

  erewrite tree_apply_access_only_cares_about_rel in Step01.
  1: erewrite tree_apply_access_only_cares_about_rel in Step12.
  1: edestruct (join_map_commutes
    Fn1PreservesTag
    Fn2PreservesTag
    Commutes _ tr0 tr1 tr2 Step01 Step12) as [tr1' [Step01' Step1'2]].  1: exists tr1'; split; [exact Step01'|].
  1: erewrite tree_apply_access_only_cares_about_rel in Step1'2.
  1: exact Step1'2.
  all: intros tg tg'.
  - eapply join_map_eqv_rel; [|eassumption]. intros it it' H. eapply Fn2PreservesTag. exact H.
  - eapply join_map_eqv_imm_rel; [|eassumption]. intros it it' H. eapply Fn2PreservesTag. exact H.
  - symmetry. eapply join_map_eqv_rel; [|eassumption]. intros it it' H. eapply Fn1PreservesTag. exact H.
  - symmetry. eapply join_map_eqv_imm_rel; [|eassumption]. intros it it' H. eapply Fn1PreservesTag. exact H.
  - tauto.
  - tauto.
Qed.

Lemma tree_apply_access_persistent
  {fn1 fn2 cids access_tag1 access_tag2 range1 range2}
  (Commutes : forall rel1 rel2, persistent_if (fun it => exists nxtp nxtc, item_wf it nxtp nxtc)
    (item_apply_access fn1 cids rel1 range1)
    (item_apply_access fn2 cids rel2 range2))
  : persistent_if (fun tr => exists nxtp nxtc, tree_items_compat_nexts tr nxtp nxtc)
    (fun tr => tree_apply_access fn1 cids access_tag1 range1 tr)
    (fun tr => tree_apply_access fn2 cids access_tag2 range2 tr).
Proof.
  unfold tree_apply_access.
  intros tr0 tr1 tr2 Pre Step01 Step12.
  assert (forall (it it' : item) (cids : call_id_set) (rel : rel_pos) (range : Z * nat),
     item_apply_access fn1 cids rel range it = Some it'
     → itag it = itag it') as Fn1PreservesTag. {
      intros. eapply item_apply_access_preserves_metadata. eassumption.
  }
  assert (forall (it it' : item) (cids : call_id_set) (rel : rel_pos) (range : Z * nat),
     item_apply_access fn2 cids rel range it = Some it'
     → itag it = itag it') as Fn2PreservesTag. {
      intros. eapply item_apply_access_preserves_metadata. eassumption.
  }

  erewrite tree_apply_access_only_cares_about_rel in Step01.
  1: erewrite tree_apply_access_only_cares_about_rel in Step12.
  1: edestruct (join_map_persistent
    Fn1PreservesTag
    Fn2PreservesTag
    Commutes _ tr0 tr1 tr2 Pre Step01 Step12) as [tr1' Res].
  1: exists tr1'.
  1: exact Res.
  all: intros tg tg'.
  - eapply join_map_eqv_rel; [|eassumption]. intros it it' H. eapply Fn1PreservesTag. exact H.
  - eapply join_map_eqv_imm_rel; [|eassumption]. intros it it' H. eapply Fn1PreservesTag. exact H.
  - eapply join_map_eqv_rel; [|eassumption]. intros it it' H. eapply Fn1PreservesTag. exact H.
  - eapply join_map_eqv_imm_rel; [|eassumption]. intros it it' H. eapply Fn1PreservesTag. exact H.
Qed.


Lemma memory_access_read_commutes
  {cids access_tag1 access_tag2 range1 range2}
  : commutes
    (memory_access AccessRead cids access_tag1 range1)
    (memory_access AccessRead cids access_tag2 range2).
Proof.
  unfold memory_access.
  apply tree_apply_access_commutes; intros.
  apply item_apply_access_read_commutes; intros.
  apply apply_access_perm_read_commutes.
Qed.

Lemma memory_access_read_persistent
  {cids access_tag1 access_tag2 range1 range2}
  : persistent_if (fun tr => exists nxtp nxtc, tree_items_compat_nexts tr nxtp nxtc)
    (memory_access AccessRead cids access_tag1 range1)
    (memory_access AccessRead cids access_tag2 range2).
Proof.
  unfold memory_access.
  apply tree_apply_access_persistent; intros.
  apply item_apply_access_read_persistent; intros.
  apply apply_access_perm_read_persistent.
Qed.

Lemma apply_within_trees_commutes
  {fn1 fn2 alloc1 alloc2}
  (Commutes : commutes fn1 fn2)
  : commutes
    (apply_within_trees fn1 alloc1)
    (apply_within_trees fn2 alloc2)
  .
Proof.
  intros trs0 trs1 trs2 App0 App1.
  (* Move forward *)
  rewrite bind_Some in App0. destruct App0 as [tr0 [tr0Spec App0]].
  rewrite bind_Some in App0. destruct App0 as [tr1 [tr1Spec App0]].
  injection App0; intros; clear App0; subst.
  rewrite bind_Some in App1. destruct App1 as [tr1b [tr1bSpec App1]].
  rewrite bind_Some in App1. destruct App1 as [tr2 [tr2Spec App1]].
  injection App1; intros; clear App1; subst.
  (* Now we do the interesting case distinction *)
  destruct (decide (alloc1 = alloc2)).
  - (* Same allocation *)
    subst.
    assert (tr1 = tr1b). {
      rewrite lookup_insert_eq in tr1bSpec. injection tr1bSpec. tauto.
    }
    subst.
    destruct (Commutes _ _ _ tr1Spec tr2Spec) as [tr1' [tr1'SpecA tr1'SpecB]].
    exists (<[alloc2:=tr1']> trs0).
    split.
    + rewrite bind_Some. exists tr0. split; first done.
      rewrite tr1'SpecA; simpl; done.
    + rewrite bind_Some. exists tr1'.
      split.
      * apply lookup_insert_eq.
      * rewrite tr1'SpecB; simpl.
        f_equal.
        do 2 rewrite insert_insert_eq.
        reflexivity.
  - (* Not the same allocation *)
    exists (<[alloc2:=tr2]> trs0).
    split.
    + rewrite bind_Some. exists tr1b.
      split.
      * rewrite <- tr1bSpec. rewrite lookup_insert_ne; done.
      * rewrite tr2Spec; done.
    + rewrite bind_Some. exists tr0.
      split.
      * rewrite <- tr0Spec. rewrite lookup_insert_ne; done.
      * rewrite tr1Spec; simpl.
        f_equal. apply insert_insert_ne. done.
Qed.

Lemma apply_within_trees_persistent
  {fn1 fn2 alloc1 alloc2}
  (Commutes : persistent_if (fun tr => exists nxtp nxtc, tree_items_compat_nexts tr nxtp nxtc) fn1 fn2)
  : persistent_if (fun trs => exists nxtp nxtc, trees_compat_nexts trs nxtp nxtc)
    (apply_within_trees fn1 alloc1)
    (apply_within_trees fn2 alloc2)
  .
Proof.
  intros trs0 trs1 trs2 Pre App0 App1.
  destruct Pre as [nxtp [nxtc AllWf]].
  (* Move forward *)
  rewrite bind_Some in App0. destruct App0 as [tr0 [tr0Spec App0]].
  rewrite bind_Some in App0. destruct App0 as [tr1 [tr1Spec App0]].
  injection App0; intros; clear App0; subst.
  rewrite bind_Some in App1. destruct App1 as [tr1b [tr1bSpec App1]].
  rewrite bind_Some in App1. destruct App1 as [tr2 [tr2Spec App1]].
  injection App1; intros; clear App1; subst.
  pose proof (AllWf alloc1 tr0 tr0Spec) as tr0Wf.
  (* Now we do the interesting case distinction *)
  destruct (decide (alloc1 = alloc2)).
  - (* Same allocation *)
    subst.
    assert (tr0 = tr1b). {
      rewrite tr0Spec in tr1bSpec.
      injection tr1bSpec. tauto.
    }
    subst.
    destruct (Commutes _ _ _ ltac:(eexists; eexists; apply tr0Wf) tr1Spec tr2Spec) as [tr1' Res].
    eexists.
    rewrite bind_Some. eexists.
    split.
    + rewrite lookup_insert_eq; reflexivity.
    + rewrite Res; simpl; reflexivity.
  - (* Not the same allocation *)
    eexists.
    + rewrite bind_Some. exists tr1b.
      split.
      * rewrite <- tr1bSpec. rewrite lookup_insert_ne; done.
      * rewrite tr2Spec; simpl. done.
Qed.

Lemma apply_read_within_trees_commutes
  {cids tg1 range1 alloc1 tg2 range2 alloc2}
  : commutes
    (apply_within_trees (memory_access AccessRead cids tg1 range1) alloc1)
    (apply_within_trees (memory_access AccessRead cids tg2 range2) alloc2)
  .
Proof.
  apply apply_within_trees_commutes.
  apply memory_access_read_commutes.
Qed.

Lemma apply_read_within_trees_persistent
  {cids tg1 range1 alloc1 tg2 range2 alloc2}
  : persistent_if (fun trs => exists nxtp nxtc, trees_compat_nexts trs nxtp nxtc)
    (apply_within_trees (memory_access AccessRead cids tg1 range1) alloc1)
    (apply_within_trees (memory_access AccessRead cids tg2 range2) alloc2)
  .
Proof.
  apply apply_within_trees_persistent.
  apply memory_access_read_persistent.
Qed.

Lemma read_failure_preserved
  {cids tg1 range1 alloc1 tg2 range2 alloc2 trs0 trs1}
  (Wf : exists nxtp nxtc, trees_compat_nexts trs0 nxtp nxtc)
  (Read1 : apply_within_trees (memory_access AccessRead cids tg1 range1) alloc1 trs0 = Some trs1)
  :
  apply_within_trees (memory_access AccessRead cids tg2 range2) alloc2 trs0 = None
  <->
  apply_within_trees (memory_access AccessRead cids tg2 range2) alloc2 trs1 = None
  .
Proof.
  split.
  + intro Fail0.
    destruct (apply_within_trees (memory_access AccessRead cids tg2 range2) alloc2 trs1) eqn:Acc1.
    2: reflexivity.
    exfalso.
    destruct (apply_read_within_trees_commutes _ _ _ Read1 Acc1) as [x1' [Read' _]].
    rewrite Read' in Fail0. discriminate.
  + intro Fail1.
    destruct (apply_within_trees (memory_access AccessRead cids tg2 range2) alloc2 trs0) eqn:Acc0.
    2: reflexivity.
    destruct (apply_read_within_trees_persistent _ _ _ Wf Read1 Acc0) as [x' Read'].
    rewrite Read' in Fail1.
    discriminate.
Qed.

Lemma apply_read_within_trees_same_tags
  {tg trs trs' cids tg' range blk blk'}
  (ACC : apply_within_trees (memory_access AccessRead cids tg' range) blk' trs = Some trs')
  : trees_contain tg trs blk <-> trees_contain tg trs' blk.
Proof.
  rewrite bind_Some in ACC. destruct ACC as [tr [trSpec ACC]].
  rewrite bind_Some in ACC. destruct ACC as [tr' [tr'Spec ACC]].
  injection ACC; intros; clear ACC; subst.
  rewrite /trees_contain /trees_at_block.
  destruct (decide (blk = blk')).
  + subst. rewrite lookup_insert_eq. rewrite trSpec.
    eapply access_preserves_tags.
    apply tr'Spec.
  + rewrite lookup_insert_ne; last done.
    reflexivity.
Qed.

Lemma CopyEvt_commutes
  { trs0 cids0 nxtp0 nxtc0
    alloc1 tg1 range1 val1
    trs1 cids1 nxtp1 nxtc1
    alloc2 tg2 range2 val2
    trs2 cids2 nxtp2 nxtc2
  }
  (Step1 :
    bor_step
      trs0 cids0 nxtp0 nxtc0
      (CopyEvt alloc1 tg1 range1 val1)
      trs1 cids1 nxtp1 nxtc1)
  (Step2 :
    bor_step
      trs1 cids1 nxtp1 nxtc1
      (CopyEvt alloc2 tg2 range2 val2)
      trs2 cids2 nxtp2 nxtc2)
  : exists trs1' cids1' nxtp1' nxtc1',
    bor_step
      trs0 cids0 nxtp0 nxtc0
      (CopyEvt alloc2 tg2 range2 val2)
      trs1' cids1' nxtp1' nxtc1'
    /\
    bor_step
      trs1' cids1' nxtp1' nxtc1'
      (CopyEvt alloc1 tg1 range1 val1)
      trs2 cids2 nxtp2 nxtc2
  .
Proof.
  inversion Step1 as [|????? EXISTS1 ACC1 SZ1| | | | | | | |].
  - subst.
    inversion Step2 as [|????? EXISTS2 ACC2 SZ2| | | | | | | |].
    + subst.
      destruct (apply_read_within_trees_commutes _ _ _ ACC1 ACC2) as [trs1' [ACC2' ACC1']].
      exists trs1'. exists cids2. exists nxtp2. exists nxtc2.
      split.
      * econstructor; eauto.
        rewrite apply_read_within_trees_same_tags; last exact ACC2'.
        rewrite apply_read_within_trees_same_tags; last exact ACC1'.
        rewrite- apply_read_within_trees_same_tags; last exact ACC2.
        assumption.
      * econstructor; eauto.
        rewrite apply_read_within_trees_same_tags; last exact ACC1'.
        rewrite- apply_read_within_trees_same_tags; last exact ACC2.
        rewrite- apply_read_within_trees_same_tags; last exact ACC1.
        assumption.
    + subst.
      repeat eexists.
      1: econstructor 3; auto.
      econstructor; eauto.
  - subst.
    inversion Step2 as [|????? EXISTS2 ACC2 SZ2| | | | | | | |].
    + subst.
      repeat eexists.
      1: econstructor; eauto.
      econstructor 3; eauto.
    + subst.
      repeat eexists.
      all: econstructor 3; eauto.
Qed.

Lemma bor_steps_CopyEvt_commutes
  { trs0 cids0 nxtp0 nxtc0
    alloc1 tg1 range1 val1
    alloc2 tg2 range2 val2
    trs2 cids2 nxtp2 nxtc2
  }
  (Steps : bor_steps
    trs0 cids0 nxtp0 nxtc0
    [CopyEvt alloc1 tg1 range1 val1; CopyEvt alloc2 tg2 range2 val2]
    trs2 cids2 nxtp2 nxtc2)
  : bor_steps
    trs0 cids0 nxtp0 nxtc0
    [CopyEvt alloc2 tg2 range2 val2; CopyEvt alloc1 tg1 range1 val1]
    trs2 cids2 nxtp2 nxtc2
  .
Proof.
  inversion Steps as [|?????????? HEAD1 REST1].
  inversion REST1 as [|?????????? HEAD2 REST2].
  inversion REST2.
  subst.
  destruct (CopyEvt_commutes HEAD1 HEAD2) as [?[?[?[?[HEAD2' HEAD1']]]]].
  econstructor; last econstructor; last constructor.
  + apply HEAD2'.
  + apply HEAD1'.
Qed.


