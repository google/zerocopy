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
From simuliris.tree_borrows Require Export trees_equal.disabled_in_practice.

Section utils.

  Definition tag_valid (upper : tag) (n : tag) : Prop := (n < upper)%nat.

  Lemma tag_valid_mono upper1 upper2 n1 n2 :
    tag_valid upper1 n1 →
    (upper1 ≤ upper2)%nat →
    (n2 ≤ n1)%nat →
    tag_valid upper2 n2.
  Proof.
    rewrite /tag_valid. lia.
  Qed.

  Context (C : gset call_id).

  (* trees_equal is almost symmetric. To still get nice reasoning rules around symmetry and stuff,
     we add a directionality flags for all rules that hold on both sides, so that we can reason by
     symmetry -> foo -> symmetry and so only have to formulate foo to operate on one side *)
  Inductive direction := Forwards | Backwards.

  Inductive pseudo_conflicted (tr : tree item) (tg : tag) (l : Z)
    : res_conflicted → Prop :=
    | pseudo_conflicted_conflicted :
        (* a Conflicted marker makes the permission literally conflicted *)
        pseudo_conflicted tr tg l ResConflicted
    | pseudo_conflicted_cousin_init tg_cous it_cous :
        (* If it's not actually conflicted, it can be pseudo conflicted if there is *)
        (* A cousin that is protected *)
        rel_dec tr tg tg_cous = Foreign Cousin ->
        tree_lookup tr tg_cous it_cous ->
        protector_is_active it_cous.(iprot) C ->
        (* and who on this location is initalized not disabled *)
        (item_lookup it_cous l).(perm) ≠ Disabled ->
        (item_lookup it_cous l).(initialized) = PermInit ->
        (* Also not Cell because Cell does not do protector end action *)
        (item_lookup it_cous l).(perm) ≠ Cell ->
        pseudo_conflicted tr tg l ResActivable
    .

  Inductive parent_has_perm p (tr : tree item) (tg : tag) (witness : tag) (l : Z)
    : Prop :=
    (* This means being Reserved and having a parent that is exactly Frozen.
       [frozen_in_practice] behaves indistinguishably from Frozen.
       We could probably make [Frozen] and [frozen_in_practice] equivalent, but
       this shouldn't turn up in practice. *)
    | mk_parent_has_perm it_witness inclusive :
        rel_dec tr tg witness = Child inclusive ->
        tree_lookup tr witness it_witness ->
        (item_lookup it_witness l).(perm) = p ->
        (* be initialized so that protectors trigger if applicable *)
        (item_lookup it_witness l).(initialized) = PermInit ->
        parent_has_perm p tr tg witness l
     .

  Definition frozen_in_practice := parent_has_perm Frozen.

  Inductive one_sided_sim : Prop -> permission -> permission -> Prop :=
      (* currently, case 1 is not needed, since we always know there's no active around we can invalidate *)
    | one_sided_sim_active isprot :
        ¬ isprot ->
        one_sided_sim isprot Frozen Active
    | one_sided_sim_res_confl isprot :
        isprot ->
        one_sided_sim isprot (Reserved ResConflicted) (Reserved ResActivable).

  Definition directional_simulation d isprot p1 p2 : Prop :=
    match d with
    | Forwards  => one_sided_sim isprot p1 p2
    | Backwards => one_sided_sim isprot p2 p1
    end.

  Inductive perm_eq_up_to_C (tr1 tr2 : tree item) (tg : tag) (l : Z) cid d
    : lazy_permission -> lazy_permission -> Prop :=
    | perm_eq_up_to_C_refl p :
        (* Usually the permissions will be equal *)
        perm_eq_up_to_C tr1 tr2 tg l cid d p p
    | perm_eq_up_to_C_pseudo ini confl1 confl2 :
        (* But if they are protected *)
        protector_is_active cid C ->
        (* And both pseudo-conflicted *)
        pseudo_conflicted tr1 tg l confl1 ->
        pseudo_conflicted tr2 tg l confl2 ->
        (* then we can allow a small difference *)
        perm_eq_up_to_C tr1 tr2 tg l cid d
          {| initialized := ini; perm := Reserved confl1 |}
          {| initialized := ini; perm := Reserved confl2 |}
    | perm_eq_up_to_C_pseudo_post_prot ini confl1 confl2 :
        (* But if they are not protected *)
        ¬ protector_is_active cid C ->
        (* then we can allow a small difference *)
        perm_eq_up_to_C tr1 tr2 tg l cid d
          {| initialized := ini; perm := Reserved confl1 |}
          {| initialized := ini; perm := Reserved confl2 |}
    | perm_eq_up_to_C_pseudo_disabled p1 p2 :
        (* A pseudo-disabled tag is one that's lazy, does not support child accesses due to a protected Active cousin,
           and will become Disabled on protector-end write for that cousin.
           It must be lazy, because a protected active has no non-disabled initialized cousins.
           Only exception: ¬prot Reserved InteriorMut, for which this case here does not apply. *)
        pseudo_disabled C tr1 tg l p1 cid ->
        pseudo_disabled C tr2 tg l p2 cid ->
        perm_eq_up_to_C tr1 tr2 tg l cid d
          {| initialized := PermLazy; perm := p1 |}
          {| initialized := PermLazy; perm := p2 |}
    | perm_eq_up_to_C_disabled_parent witness_tg p p' :
        (* Finally if they have a Disabled parent we allow anything (unprotected) since
           nothing is possible through this tag anyway *)
        disabled_in_practice C tr1 tg witness_tg l ->
        disabled_in_practice C tr2 tg witness_tg l ->
        (* Added initialization requirement to help with the lemma [perm_eq_up_to_C_same_init] *)
        (initialized p = initialized p') ->
        (* Additionally require that Cell nodes are the same everywhere, since we often have a Cell corner case *)
        (perm p = Cell ↔ perm p' = Cell) ->
        perm_eq_up_to_C tr1 tr2 tg l cid d p p'
    | perm_eq_up_to_C_frozen_parent ini confl1 confl2 witness_tg :
        (* not needed for IM, that's already covered by refl *)
        (* only the source side must be Frozen. This already implies the other side is frozen in practice,
           or the same with Active, or we're disabled on both. *)
        frozen_in_practice (match d with Forwards => tr1 | _ => tr2 end) tg witness_tg l ->
        perm_eq_up_to_C tr1 tr2 tg l cid d
          {| initialized := ini; perm := Reserved confl1 |}
          {| initialized := ini; perm := Reserved confl2 |}
    | perm_eq_up_to_C_directional p1 p2 ini :
        directional_simulation d (protector_is_active cid C) p1 p2 ->
        perm_eq_up_to_C tr1 tr2 tg l cid d
          {| initialized := ini; perm := p1 |}
          {| initialized := ini; perm := p2 |}
    .

  Definition loc_eq_up_to_C (tr1 tr2 : tree item) (tg : tag) d (it1 it2 : item) (l : Z) :=
    it1.(iprot) = it2.(iprot)
    /\ perm_eq_up_to_C tr1 tr2 tg l it1.(iprot) d (item_lookup it1 l) (item_lookup it2 l).

  Definition item_eq_up_to_C (tr1 tr2 : tree item) (tg : tag) d (it1 it2 : item) :=
    forall l, loc_eq_up_to_C tr1 tr2 tg d it1 it2 l.

  Definition tree_equal d (tr1 tr2 : tree item) :=
    (* To be equal trees must have exactly the same tags *)
    (forall tg, tree_contains tg tr1 <-> tree_contains tg tr2)
    (* and define all the same relationships between those tags *)
    /\ (forall tg tg', rel_dec tr1 tg tg' = rel_dec tr2 tg tg')
    (* and have their permissions be equal up to C on all locations *)
    /\ (forall tg, tree_contains tg tr1 ->
          exists it1 it2,
            tree_lookup tr1 tg it1
            /\ tree_lookup tr2 tg it2
            /\ item_eq_up_to_C tr1 tr2 tg d it1 it2
       ).

  Definition trees_equal d (t1 t2 : trees) :=
    ∀ blk, option_Forall2 (tree_equal d) (t1 !! blk) (t2 !! blk).


  Lemma loc_eq_up_to_C_reflexive
    {d tr1 tr2 tg it l}
    : loc_eq_up_to_C tr1 tr2 tg d it it l.
  Proof.
    split.
    + reflexivity.
    + apply perm_eq_up_to_C_refl.
  Qed.

  Lemma item_eq_up_to_C_reflexive
    {d tr1 tr2 tg it}
    : item_eq_up_to_C tr1 tr2 tg d it it.
  Proof.
    intro l.
    apply loc_eq_up_to_C_reflexive.
  Qed.

  Lemma tree_equal_reflexive d tr
    (AllUnique : forall tg, tree_contains tg tr -> exists it, tree_item_determined tg it tr)
    : tree_equal d tr tr.
  Proof.
    try repeat split.
    - tauto.
    - tauto.
    - intros tg Ex.
      destruct (AllUnique tg Ex).
      eexists. eexists.
      try repeat split.
      + assumption.
      + eassumption.
      + assumption.
      + eassumption.
      + apply item_eq_up_to_C_reflexive.
  Qed.


  Lemma trees_equal_reflexive d trs
    (AllUnique : forall blk tr tg,
      trs !! blk = Some tr ->
      tree_contains tg tr ->
      exists it, tree_item_determined tg it tr)
    : trees_equal d trs trs.
  Proof.
    intros blk.
    specialize (AllUnique blk).
    remember (trs !! blk) as at_blk.
    destruct at_blk.
    - apply Some_Forall2.
      apply tree_equal_reflexive.
      intro tg.
      eapply AllUnique.
      reflexivity.
    - apply None_Forall2.
  Qed.


  Lemma trees_equal_same_tags d (trs1 trs2 : trees) (tg : tag) (blk : block) :
    trees_equal d trs1 trs2 ->
    trees_contain tg trs1 blk <-> trees_contain tg trs2 blk.
  Proof.
    intro Equals.
    rewrite /trees_equal in Equals.
    specialize (Equals blk).
    rewrite /trees_contain /trees_at_block.
    destruct (trs1 !! blk) as [tr1|];
      destruct (trs2 !! blk) as [tr2|];
      inversion Equals as [?? Equal|].
    2: tauto.
    subst.
    destruct Equal as [SameTags _].
    apply SameTags.
  Qed.

  Lemma trees_equal_empty d : trees_equal d ∅ ∅.
  Proof.
    apply trees_equal_reflexive.
    intros blk tr tg LookupEmp.
    inversion LookupEmp.
  Qed.

  Definition direction_flip d := match d with
    Forwards => Backwards
  | Backwards => Forwards end.

  Lemma direction_flip_inv d : direction_flip (direction_flip d) = d.
  Proof. by destruct d. Qed.

  Lemma perm_eq_up_to_C_sym
    {d tr1 tr2 tg l cid perm1 perm2}
    : perm_eq_up_to_C tr1 tr2 tg l cid d perm1 perm2
      -> perm_eq_up_to_C tr2 tr1 tg l cid (direction_flip d) perm2 perm1.
  Proof.
    intro EqC.
    inversion EqC.
    + econstructor 1.
    + econstructor 2; eassumption.
    + econstructor 3; eassumption.
    + econstructor 4; eassumption.
    + econstructor 5; try eassumption.
      all: by symmetry.
    + econstructor 6; destruct d; eassumption.
    + econstructor 7; destruct d; eassumption.
  Qed.

  Lemma loc_eq_up_to_C_sym
    {d tr1 tr2 tg it1 it2 l}
    : loc_eq_up_to_C tr1 tr2 tg d it1 it2 l
      -> loc_eq_up_to_C tr2 tr1 tg (direction_flip d) it2 it1 l.
  Proof.
    intros [SameProt EqC].
    split.
    + auto.
    + apply perm_eq_up_to_C_sym.
      rewrite <- SameProt.
      assumption.
  Qed.

  Lemma item_eq_up_to_C_sym
    {d tr1 tr2 tg it1 it2}
    : item_eq_up_to_C tr1 tr2 tg d it1 it2
      -> item_eq_up_to_C tr2 tr1 tg (direction_flip d) it2 it1.
  Proof.
    intros EqC l.
    apply loc_eq_up_to_C_sym.
    auto.
  Qed.

  Lemma tree_equal_sym {d} tr1 tr2 : tree_equal d tr1 tr2 → tree_equal (direction_flip d) tr2 tr1.
  Proof.
    rewrite /tree_equal.
    intros [SameTg [SameRel EqC]].
    split; [|split].
    + intro tg. rewrite SameTg. tauto.
    + intros tg tg'. rewrite SameRel. tauto.
    + intros tg Ex.
      rewrite <- SameTg in Ex.
      destruct (EqC tg Ex) as [it1 [it2 [Lookup1 [Lookup2 EqCsub]]]].
      exists it2, it1.
      split; [|split].
      * assumption.
      * assumption.
      * apply item_eq_up_to_C_sym.
        assumption.
  Qed.

  Lemma trees_equal_sym {d} trs1 trs2 : trees_equal d trs1 trs2 → trees_equal (direction_flip d) trs2 trs1.
  Proof.
    rewrite /trees_equal.
    intros Equals blk.
    specialize (Equals blk).
    inversion Equals; simplify_eq; econstructor.
    by eapply tree_equal_sym.
  Qed.

  Lemma trees_equal_insert d tr1 tr2 ttr1 ttr2 blk :
    trees_equal d tr1 tr2 →
    tree_equal d ttr1 ttr2 →
    trees_equal d (<[blk := ttr1]> tr1) (<[blk := ttr2]> tr2).
  Proof.
    intros Htr Httr blk'.
    destruct (decide (blk = blk')) as [Heq|Hne].
    - rewrite -!Heq !lookup_insert_eq. by econstructor.
    - rewrite !lookup_insert_ne //.
  Qed.

  Lemma apply_within_trees_equal d fn blk tr1 tr1' tr2 :
    (∀ ttr1 ttr1' ttr2, fn ttr1 = Some ttr1' → tree_equal d ttr1 ttr2 →
       tr1 !! blk = Some ttr1 → tr1' !! blk = Some ttr1' → tr2 !! blk = Some ttr2 →
     ∃ ttr2', fn ttr2 = Some ttr2' ∧ tree_equal d ttr1' ttr2') →
    apply_within_trees fn blk tr1 = Some tr1' →
    trees_equal d tr1 tr2 →
    ∃ tr2', apply_within_trees fn blk tr2 = Some tr2' ∧
       trees_equal d tr1' tr2'.
  Proof.
    intros Hfn Happly Heq.
    rewrite /apply_within_trees in Happly|-*.
    specialize (Heq blk) as Heqblk.
    inversion Heqblk as [ttr1 ttr2 Hteq Htr1 Htr2|HN1 HN2]; last rewrite -HN1 // in Happly.
    rewrite -Htr1 -?Htr2 /= in Happly|-*.
    destruct (fn ttr1) as [ttr1'|] eqn:Hfnttr1; last done.
    rewrite /= in Happly. injection Happly as <-.
    destruct (Hfn ttr1 ttr1' ttr2) as (ttr2' & Hfnttr2 & Heq'); try done.
    1: by rewrite lookup_insert_eq.
    rewrite Hfnttr2 /=. eexists; split; first done.
    by apply trees_equal_insert.
  Qed.

  Lemma trees_equal_delete d tr1 tr2 blk :
    trees_equal d tr1 tr2 →
    trees_equal d (delete blk tr1) (delete blk tr2).
  Proof.
    intros Htr blk'.
    destruct (decide (blk = blk')) as [Heq|Hne].
    - rewrite -!Heq !lookup_delete_eq. by econstructor.
    - rewrite !lookup_delete_ne //.
  Qed.

  Lemma trees_equal_init_trees d ts tt tg bl off sz :
    trees_equal d ts tt →
    trees_equal d (extend_trees tg bl off sz ts) (extend_trees tg bl off sz tt).
  Proof.
    intros Htrs. apply trees_equal_insert; first done.
    eapply tree_equal_reflexive.
    eapply wf_tree_tree_item_determined.
    eapply wf_init_tree.
  Qed.

  Lemma apply_within_trees_lift d trs fn blk trs' :
    wf_trees trs →
    apply_within_trees fn blk trs = Some trs' →
    (∀ tr tr', trs !! blk = Some tr → trs' !! blk = Some tr' → fn tr = Some tr' → tree_equal d tr tr') →
    trees_equal d trs trs'.
  Proof.
    intros Hwf (tr&Htr&(tr'&Htr'&[= <-])%bind_Some)%bind_Some Heq.
    intros bb. destruct (decide (bb = blk)) as [<-|Hne].
    - rewrite lookup_insert_eq Htr. econstructor. eapply Heq. 1,3: done. by rewrite lookup_insert_eq.
    - rewrite lookup_insert_ne //. destruct (trs !! bb) eqn:HHeq. all: rewrite !HHeq. all: econstructor.
      eapply tree_equal_reflexive. eapply wf_tree_tree_item_determined, Hwf, HHeq.
  Qed.

  Lemma item_eq_up_to_C_same_iprot d tr1 tr2 tg it1 it2 : 
    item_eq_up_to_C tr1 tr2 tg d it1 it2 →
    it1.(iprot) = it2.(iprot).
  Proof.
    intros H. specialize (H 0). inversion H. done.
  Qed.

  Lemma perm_eq_up_to_C_same_init d tr1 tr2 tg off prot lp1 lp2 : 
    perm_eq_up_to_C tr1 tr2 tg off prot d lp1 lp2 →
    initialized lp1 = initialized lp2.
  Proof.
    intros H. try by inversion H.
  Qed.

End utils.

Section defs.

  (* These definitions are used as preconditions for one-sided reads.
     We put them here since that makes things more modular *)


  
  (* A bunch of extra conditions on the structure.
     They are put in the same clause to simplify this theorem, but we will want
     a higher-level lemma that derives these assumptions from their actual justification. 
     Note that this could be tree_equal_asymmetric_read_pre_protected, i.e. this is more general than it needs be *)
  Definition tree_equal_asymmetric_read_pre_source tr range it acc_tg := 
    (∀ off, range'_contains range off → 
            let pp_acc := item_lookup it off in
            pp_acc.(initialized) = PermInit ∧ pp_acc.(perm) ≠ Disabled ∧
            ∀ tg' it', tree_lookup tr tg' it' → 
            let pp := item_lookup it' off in
            let rd := rel_dec tr tg' acc_tg in (* flipped here so that it's correcty lined up with logical_state *)
            match rd with
              Foreign (Parent _) => pp.(initialized) = PermInit ∧ pp.(perm) ≠ Disabled
              (* this is not a restriction, it always holds by state_wf *)
            | Foreign Cousin | Child (Strict _) => pp.(perm) = Active -> pp.(initialized) = PermInit 
            | _ => True end).

  Definition tree_equal_asymmetric_read_pre_protected tr range it acc_tg (mode:bool) := 
    (∀ off, range'_contains range off → 
            let pp_acc := item_lookup it off in
            pp_acc.(initialized) = PermInit ∧ pp_acc.(perm) ≠ Disabled ∧ pp_acc.(perm) ≠ Cell (* protectors don't apply to cell *) ∧
            ∀ tg' it', tree_lookup tr tg' it' → 
            let pp := item_lookup it' off in
            let rd := rel_dec tr tg' acc_tg in (* flipped here so that it's correcty lined up with logical_state *)
            match rd with
              Foreign (Parent _) => pp.(initialized) = PermInit ∧ pp.(perm) ≠ Disabled
            | Foreign Cousin => pp.(perm) ≠ Active | _ => True end ∧
            if mode then (rd = Child (Strict Immediate) → pp.(perm) = Disabled) else
             (pp_acc.(perm) = Frozen ∧ (∀ i, rd = Child (Strict i) → pp.(perm) ≠ Active))).

  (* We can also do symmetric writes, provided we have sufficiently strong preconditions,
     which include being protected. *)
  Definition tree_equal_asymmetric_write_pre_protected C tr range it acc_tg := 
    (∀ off, range'_contains range off → 
            let pp_acc := item_lookup it off in
            pp_acc.(initialized) = PermInit ∧ pp_acc.(perm) = Active ∧
            ∀ tg' it', tree_lookup tr tg' it' → 
            let pp := item_lookup it' off in
            let rd := rel_dec tr tg' acc_tg in (* flipped here so that it's correcty lined up with logical_state *)
            match rd with
            | Child (Strict Immediate) => pp.(perm) = Disabled
            | Child _ => True
            | Foreign (Parent _) => pp.(initialized) = PermInit ∧ (pp.(perm) = Active ∨ pp.(perm) = Cell) (* this follows from state_wf *)
            | Foreign Cousin => match pp.(perm) with Disabled | Cell => True | ReservedIM => ¬ protector_is_active it'.(iprot) C (* never occurs *) | _ => pp.(initialized) = PermLazy end end).

End defs.

