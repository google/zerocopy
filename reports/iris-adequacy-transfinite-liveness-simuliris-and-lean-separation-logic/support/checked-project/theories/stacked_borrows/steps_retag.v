(** This file has been adapted from the Stacked Borrows development, available at 
  https://gitlab.mpi-sws.org/FP/stacked-borrows
*)

From simuliris.stacked_borrows Require Export defs steps_foreach steps_list steps_wf steps_progress.

Definition tag_on_top (stks: stacks) l t pm : Prop :=
  ∃ prot, (stks !! l) ≫= head = Some (mkItem pm (Tagged t) prot).

(** Active protector preserving *)
Definition active_preserving (cids: call_id_set) (stk stk': stack) :=
  ∀ pm t c, c ∈ cids → mkItem pm t (Some c) ∈ stk → mkItem pm t (Some c) ∈ stk'.

Global Instance active_preserving_preorder cids : PreOrder (active_preserving cids).
Proof.
  constructor.
  - intros ??. done.
  - intros ??? AS1 AS2 ?????. naive_solver.
Qed.

Lemma active_preserving_app_mono (cids: call_id_set) (stk1 stk2 stk': stack) :
  active_preserving cids stk1 stk2 →
  active_preserving cids (stk1 ++ stk') (stk2 ++ stk').
Proof.
  intros AS pm t c Inc. rewrite 2!elem_of_app.
  specialize (AS pm t c Inc). set_solver.
Qed.

Lemma remove_check_active_preserving cids stk stk' idx:
  remove_check cids stk idx = Some stk' → active_preserving cids stk stk'.
Proof.
  revert idx.
  induction stk as [|it stk IH]; intros idx; simpl.
  { destruct idx; [|done]. intros ??. by simplify_eq. }
  destruct idx as [|idx]; [intros ??; by simplify_eq|].
  case check_protector eqn:Eq; [|done].
  move => /IH AS pm t c IN /elem_of_cons [?|]; [|by apply AS].
  subst it. exfalso. move : Eq.
  by rewrite /check_protector /= /is_active bool_decide_true //.
Qed.

Lemma replace_check'_active_preserving cids acc stk stk':
  replace_check' cids acc stk = Some stk' → active_preserving cids stk stk'.
Proof.
  revert acc.
  induction stk as [|it stk IH]; intros acc; simpl.
  { intros. simplify_eq. by intros ?????%not_elem_of_nil. }
  case decide => ?; [case check_protector eqn:Eq; [|done]|].
  - move => /IH AS pm t c IN /elem_of_cons [?|]; [|by apply AS].
    subst it. exfalso. move : Eq.
    by rewrite /check_protector /= /is_active bool_decide_true //.
  - move => Eq pm t c IN /elem_of_cons [?|].
    + apply (replace_check'_acc_result _ _ _ _ Eq), elem_of_app. right.
      by apply list_elem_of_singleton.
    + by apply (IH _ Eq).
Qed.

Lemma replace_check_active_preserving cids stk stk':
  replace_check cids stk = Some stk' → active_preserving cids stk stk'.
Proof. by apply replace_check'_active_preserving. Qed.

Lemma access1_active_preserving stk stk' kind tg cids n:
  access1 stk kind tg cids = Some (n, stk') →
  active_preserving cids stk stk'.
Proof.
  rewrite /access1. case find_granting as [gip|]; [|done]. simpl.
  destruct kind.
  - case replace_check as [stk1|] eqn:Eq; [|done].
    simpl. intros. simplify_eq.
    rewrite -{1}(take_drop gip.1 stk).
    by apply active_preserving_app_mono, replace_check_active_preserving.
  - case find_first_write_incompatible as [idx|]; [|done]. simpl.
    case remove_check as [stk1|] eqn:Eq; [|done].
    simpl. intros. simplify_eq.
    rewrite -{1}(take_drop gip.1 stk).
    by eapply active_preserving_app_mono, remove_check_active_preserving.
Qed.

Lemma for_each_access1_active_preserving α cids l n tg kind α':
  for_each α l n false
          (λ stk, nstk' ← access1 stk kind tg cids; Some nstk'.2) = Some α' →
  ∀ l stk, α !! l = Some stk →
  ∃ stk', α' !! l = Some stk' ∧ active_preserving cids stk stk'.
Proof.
  intros EQ. destruct (for_each_lookup  _ _ _ _ _ EQ) as [EQ1 [EQ2 EQ3]].
  intros l1 stk1 Eq1.
  case (decide (l1.1 = l.1)) => [Eql|NEql];
    [case (decide (l.2 ≤ l1.2 < l.2 + n)) => [[Le Lt]|NIN]|].
  - have Eql2: l1 = l +ₗ Z.of_nat (Z.to_nat (l1.2 - l.2)). {
      destruct l, l1. move : Eql Le => /= -> ?.
      rewrite /shift_loc /= Z2Nat.id; [|lia]. f_equal. lia. }
    destruct (EQ1 (Z.to_nat (l1.2 - l.2)) stk1)
      as [stk [Eq [[n1 stk'] [Eq' Eq0]]%bind_Some]];
      [rewrite -(Nat2Z.id n) -Z2Nat.inj_lt; lia|by rewrite -Eql2|].
    exists stk. rewrite -Eql2 in Eq. split; [done|]. simpl in Eq0. simplify_eq.
    eapply access1_active_preserving; eauto.
  - rewrite EQ3; [naive_solver|].
    intros i Lt Eq. apply NIN. rewrite Eq /=. lia.
  - rewrite EQ3; [naive_solver|].
    intros i Lt Eq. apply NEql. by rewrite Eq.
Qed.

Lemma for_each_access1_lookup_inv α cids l n tg kind α':
  for_each α l n false
          (λ stk, nstk' ← access1 stk kind tg cids; Some nstk'.2) = Some α' →
  ∀ l stk, α !! l = Some stk →
  ∃ stk', α' !! l = Some stk' ∧
    ((∃ n', access1 stk kind tg cids = Some (n', stk')) ∨  α' !! l = α !! l).
Proof.
  intros EQ. destruct (for_each_lookup  _ _ _ _ _ EQ) as [EQ1 [EQ2 EQ3]].
  intros l1 stk1 Eq1.
  case (decide (l1.1 = l.1)) => [Eql|NEql];
    [case (decide (l.2 ≤ l1.2 < l.2 + n)) => [[Le Lt]|NIN]|].
  - have Eql2: l1 = l +ₗ Z.of_nat (Z.to_nat (l1.2 - l.2)). {
      destruct l, l1. move : Eql Le => /= -> ?.
      rewrite /shift_loc /= Z2Nat.id; [|lia]. f_equal. lia. }
    destruct (EQ1 (Z.to_nat (l1.2 - l.2)) stk1)
      as [stk [Eq [[n1 stk'] [Eq' Eq0]]%bind_Some]];
      [rewrite -(Nat2Z.id n) -Z2Nat.inj_lt; lia|by rewrite -Eql2|].
    simpl in Eq0. simplify_eq. rewrite -Eql2 in Eq. naive_solver.
  - rewrite EQ3; [naive_solver|].
    intros i Lt Eq. apply NIN. rewrite Eq /=. lia.
  - rewrite EQ3; [naive_solver|].
    intros i Lt Eq. apply NEql. by rewrite Eq.
Qed.

(** Head preserving *)
Definition is_stack_head (it: item) (stk: stack) :=
  ∃ stk', stk = it :: stk'.

Lemma sublist_head_preserving t it it' stk stk' :
  stk' `sublist_of` stk →
  it'.(tg) = Tagged t → it.(tg) = Tagged t →
  it' ∈ stk' →
  stack_item_tagged_NoDup stk →
  is_stack_head it stk →
  is_stack_head it stk'.
Proof.
  intros SUB Eqt' Eqt In' ND.
  induction SUB as [|???? IH|??? SUB IH]; [done|..]; intros [stk1 ?]; simplify_eq;
    [by eexists|].
  exfalso. move : ND.
  rewrite /stack_item_tagged_NoDup filter_cons decide_True;
    last by rewrite /is_tagged Eqt.
  rewrite fmap_cons NoDup_cons. intros [NI ?].
  apply NI, list_elem_of_fmap. exists it'. split; [rewrite Eqt' Eqt //|].
  apply list_elem_of_filter. split; first by rewrite /is_tagged Eqt'. by rewrite <-SUB.
Qed.

Lemma replace_check'_head_preserving stk stk' acc stk0 cids pm pm' t opro:
  stack_item_tagged_NoDup (acc ++ stk ++ stk0) →
  pm ≠ Disabled →
  mkItem pm (Tagged t) opro ∈ (stk' ++ stk0) →
  replace_check' cids acc stk = Some stk' →
  is_stack_head (mkItem pm' (Tagged t) opro) (acc ++ stk ++ stk0) →
  is_stack_head (mkItem pm' (Tagged t) opro) (stk' ++ stk0).
Proof.
  intros ND NDIS IN. revert acc ND.
  induction stk as [|it stk IH]; simpl; intros acc ND.
  { intros ?. by simplify_eq. }
  case decide => ?; [case check_protector; [|done]|];
    [|move => /IH; rewrite -(app_assoc acc [it] (stk ++ stk0)); naive_solver].
  move => RC.
  rewrite (app_assoc acc [it] (stk ++ stk0)).
  have ND3: stack_item_tagged_NoDup
    ((acc ++ [mkItem Disabled it.(tg) it.(protector)]) ++ stk ++ stk0).
  { move : ND. clear.
    rewrite (app_assoc acc [it]) 2!(Permutation_app_comm acc) -2!app_assoc.
    rewrite /stack_item_tagged_NoDup 2!filter_cons /=.
    case decide => ?; [rewrite decide_True //|rewrite decide_False //]. }
  intros HD. apply (IH _ ND3 RC). clear IH. move : HD.
  destruct acc as [|it1 acc]; last first.
  { simpl in *. move => [? Eq]. inversion Eq. simplify_eq. by eexists. }
  simpl. intros [stk2 Eq]. exfalso. simplify_eq; simpl in *.
  have IN1:= (replace_check'_acc_result _ _ _ _ RC).
  have IN': mkItem Disabled (Tagged t) opro ∈ stk' ++ stk0 by set_solver. clear IN1.
  have ND4 := replace_check'_stack_item_tagged_NoDup_2 _ _ _ _ _ RC ND3.
  have EQ := stack_item_tagged_NoDup_eq _ _ _ _ ND4 IN IN' eq_refl eq_refl.
  by inversion EQ.
Qed.

Lemma replace_check_head_preserving stk stk' stk0 cids pm pm' t opro:
  stack_item_tagged_NoDup (stk ++ stk0) →
  pm ≠ Disabled →
  mkItem pm (Tagged t) opro ∈ (stk' ++ stk0) →
  replace_check cids stk = Some stk' →
  is_stack_head (mkItem pm' (Tagged t) opro) (stk ++ stk0) →
  is_stack_head (mkItem pm' (Tagged t) opro) (stk' ++ stk0).
Proof. intros. eapply replace_check'_head_preserving; eauto. done. Qed.

Lemma access1_head_preserving stk stk' kind tg cids n pm pm' t opro:
  stack_item_tagged_NoDup stk →
  pm ≠ Disabled →
  mkItem pm (Tagged t) opro ∈ stk' →
  access1 stk kind tg cids = Some (n, stk') →
  is_stack_head (mkItem pm' (Tagged t) opro) stk →
  is_stack_head (mkItem pm' (Tagged t) opro) stk'.
Proof.
  intros ND NDIS IN.
  rewrite /access1. case find_granting as [gip|]; [|done]. simpl.
  destruct kind.
  - case replace_check as [stk1|] eqn:Eq; [|done].
    simpl. intros ?. simplify_eq.
    rewrite -{1}(take_drop gip.1 stk). intros HD.
    rewrite -{1}(take_drop gip.1 stk) in ND.
    eapply replace_check_head_preserving; eauto.
  - case find_first_write_incompatible as [idx|]; [|done]. simpl.
    case remove_check as [stk1|] eqn:Eq; [|done].
    simpl. intros ?. simplify_eq.
    have SUB: stk1 ++ drop gip.1 stk `sublist_of` stk.
    { rewrite -{2}(take_drop gip.1 stk). apply sublist_app; [|done].
      move : Eq. apply remove_check_sublist. }
    eapply sublist_head_preserving; eauto. done.
Qed.

(** active_SRO preserving *)
Lemma active_SRO_cons_elem_of t it stk :
  t ∈ active_SRO (it :: stk) ↔
  it.(perm) = SharedReadOnly ∧ (it.(tg) = Tagged t ∨ t ∈ active_SRO stk).
Proof.
  simpl. destruct it.(perm); [set_solver..| |set_solver].
  case tg => [?|]; [rewrite elem_of_union elem_of_singleton|]; naive_solver.
Qed.

Lemma sublist_active_SRO_preserving t it stk stk' :
  stk' `sublist_of` stk →
  it.(tg) = Tagged t →
  it ∈ stk' →
  stack_item_tagged_NoDup stk →
  t ∈ active_SRO stk → t ∈ active_SRO stk'.
Proof.
  intros SUB Eqt In' ND.
  induction SUB as [|it1 stk1 stk2 ? IH|it1 stk1 stk2 SUB IH]; [done|..].
  - intros [? Eq]%active_SRO_cons_elem_of. apply active_SRO_cons_elem_of.
    split; [done|]. destruct Eq as [?|Eq]; [by left|].
    apply elem_of_cons in In' as [?|In'].
    + subst it. rewrite Eqt. by left.
    + right. apply IH; auto. by eapply stack_item_tagged_NoDup_cons_1.
  - intros [? Eq]%active_SRO_cons_elem_of.
    destruct Eq as [Eq|In2].
    + exfalso. move : ND.
      rewrite /stack_item_tagged_NoDup filter_cons decide_True;
        last by rewrite /is_tagged Eq.
      rewrite fmap_cons NoDup_cons. intros [NI ?].
      apply NI, list_elem_of_fmap. exists it. split; [rewrite Eqt Eq //|].
      apply list_elem_of_filter. split; first by rewrite /is_tagged Eqt. by rewrite <-SUB.
    + apply IH; auto. by eapply stack_item_tagged_NoDup_cons_1.
Qed.

Lemma active_SRO_tag_eq_elem_of stk1 stk2 t :
  fmap tg stk1 = fmap tg stk2 →
  Forall2 (λ pm1 pm2, pm1 = SharedReadOnly → pm2 = SharedReadOnly)
          (fmap perm stk1) (fmap perm stk2) →
  t ∈ active_SRO stk1 → t ∈ active_SRO stk2.
Proof.
  revert stk2.
  induction stk1 as [|it stk1 IH]; intros stk2; [simpl; set_solver|].
  destruct stk2 as [|it2 stk2]; [naive_solver|].
  rewrite 4!fmap_cons. inversion 1 as [Eqt].
  inversion 1 as [|???? Eq1 FA]; subst. rewrite 2!active_SRO_cons_elem_of.
  intros [EqSRO Eq]. specialize (Eq1 EqSRO). split; [done|].
  destruct Eq as [Eq|In1].
  - rewrite -Eqt. by left.
  - right. by apply IH.
Qed.

Lemma replace_check'_active_SRO_preserving cids acc stk stk' stk0 t it:
  it.(tg) = Tagged t →
  it ∈ stk' ++ stk0 →
  replace_check' cids acc stk = Some stk' →
  stack_item_tagged_NoDup (acc ++ stk ++ stk0) →
  t ∈ active_SRO (acc ++ stk ++ stk0) → t ∈ active_SRO (stk' ++ stk0).
Proof.
  intros Eqt IN. revert acc.
  induction stk as [|it1 stk IH]; simpl; intros acc.
  { intros ?. by simplify_eq. }
  case decide => [EqU|?]; [case check_protector; [|done]|];
    [|move => /IH; rewrite -(app_assoc acc [it1] (stk ++ stk0)); naive_solver].
  move => RC ND.
  rewrite (app_assoc acc [it1] (stk ++ stk0)).
  have ND3: stack_item_tagged_NoDup
    ((acc ++ [mkItem Disabled it1.(tg) it1.(protector)]) ++ stk ++ stk0).
  { move : ND. clear.
    rewrite (app_assoc acc [it1]) 2!(Permutation_app_comm acc) -2!app_assoc.
    rewrite /stack_item_tagged_NoDup 2!filter_cons /=.
    case decide => ?; [rewrite decide_True //|rewrite decide_False //]. }
  intros HD. apply (IH _ RC ND3). clear IH. move : HD.
  apply active_SRO_tag_eq_elem_of.
  - by rewrite !fmap_app /=.
  - rewrite 2!(fmap_app _ _ (stk ++ stk0)).
    apply Forall2_app; [rewrite 2!fmap_app; apply Forall2_app|].
    + by apply Forall_Forall2_diag, Forall_forall.
    + apply Forall2_cons. split; [|constructor]. by rewrite EqU.
    + by apply Forall_Forall2_diag, Forall_forall.
Qed.

Lemma replace_check_active_SRO_preserving cids stk stk' stk0 it t:
  it.(tg) = Tagged t →
  it ∈ stk' ++ stk0 →
  replace_check cids stk = Some stk' →
  stack_item_tagged_NoDup (stk ++ stk0) →
  t ∈ active_SRO (stk ++ stk0) → t ∈ active_SRO (stk' ++ stk0).
Proof. by apply replace_check'_active_SRO_preserving. Qed.

Lemma access1_active_SRO_preserving stk stk' kind tg cids n pm t opro:
  stack_item_tagged_NoDup stk →
  mkItem pm (Tagged t) opro ∈ stk' →
  access1 stk kind tg cids = Some (n, stk') →
  t ∈ active_SRO stk → t ∈ active_SRO stk'.
Proof.
  intros ND IN.
  rewrite /access1. case find_granting as [gip|]; [|done]. simpl.
  destruct kind.
  - case replace_check as [stk1|] eqn:Eq; [|done].
    simpl. intros ?. simplify_eq.
    rewrite -{1}(take_drop gip.1 stk). intros HD.
    rewrite -{1}(take_drop gip.1 stk) in ND.
    eapply replace_check_active_SRO_preserving; eauto. done.
  - case find_first_write_incompatible as [idx|]; [|done]. simpl.
    case remove_check as [stk1|] eqn:Eq; [|done].
    simpl. intros ?. simplify_eq.
    have SUB: stk1 ++ drop gip.1 stk `sublist_of` stk.
    { rewrite -{2}(take_drop gip.1 stk). apply sublist_app; [|done].
      move : Eq. apply remove_check_sublist. }
    eapply sublist_active_SRO_preserving; eauto. done.
Qed.

(** Removing incompatible items *)

Lemma find_granting_incompatible_head stk kind t ti idx pm pmi oproi
  (HD: is_stack_head (mkItem pmi (Tagged t) oproi) stk)
  (NEQ: Tagged t ≠ ti) :
  find_granting stk kind ti = Some (idx, pm) →
  is_stack_head (mkItem pmi (Tagged t) oproi) (take idx stk).
Proof.
  destruct HD as [stk' Eqi]. rewrite Eqi.
  rewrite /find_granting /= decide_False; last (intros [_ Eq]; by inversion Eq).
  case list_find => [[idx' pm'] /=|//]. intros . simplify_eq. simpl.
  by eexists.
Qed.

(* Writing *)
Lemma find_first_write_incompatible_head stk pm idx t opro pmi
  (HD: is_stack_head (mkItem pmi t opro) stk)
  (NSRW: pmi ≠ SharedReadWrite) :
  find_first_write_incompatible stk pm = Some idx → (0 < idx)%nat.
Proof.
  set it := (mkItem pmi t opro).
  destruct HD as [stk' Eqi]. rewrite Eqi.
  destruct pm; [..|done|done]; simpl.
  - intros. simplify_eq. lia.
  - rewrite reverse_cons.
    destruct (list_find_elem_of (λ it, it.(perm) ≠ SharedReadWrite)
                (reverse stk' ++ [it]) it) as [[id fnd] Eqf]; [set_solver|done|].
    rewrite Eqf.
    intros. simplify_eq. apply list_find_Some in Eqf as [Eqi ?].
    apply lookup_lt_Some in Eqi.
    rewrite length_app /= length_reverse Nat.add_1_r in Eqi. lia.
Qed.

Lemma remove_check_incompatible_items cids stk stk' stk0 n it i t
  (ND: stack_item_tagged_NoDup (stk ++ stk0)) :
  it.(tg) = Tagged t → stk !! i = Some it → (i < n)%nat →
  remove_check cids stk n = Some stk' →
  ∀ it', it'.(tg) = Tagged t → it' ∈ (stk' ++ stk0) → False.
Proof.
  intros Eqt. revert i stk stk0 ND.
  induction n as [|n IH]; simpl; intros i stk stk0 ND Eqit Lt; [lia|].
  destruct stk as [|it' stk]; [done|]. simpl.
  case check_protector; [|done].
  destruct i as [|i].
  - simpl in Eqit. simplify_eq.
    intros SUB%remove_check_sublist it' Eq' IN.
    have SUB': stk' ++ stk0 `sublist_of` stk ++ stk0 by apply sublist_app.
    rewrite -> SUB' in IN.
    clear -ND Eqt Eq' IN.
    move : ND.
    rewrite /stack_item_tagged_NoDup filter_cons decide_True;
            [|by rewrite /is_tagged Eqt].
    rewrite fmap_cons NoDup_cons Eqt -Eq'.
    intros [IN' _]. apply IN'. apply list_elem_of_fmap.
    exists it'. split; [done|]. apply list_elem_of_filter. by rewrite /is_tagged Eq'.
  - apply (IH i); [|done|lia]. by apply stack_item_tagged_NoDup_cons_1 in ND.
Qed.

Lemma access1_write_remove_incompatible_head stk t ti cids n stk'
  (ND: stack_item_tagged_NoDup stk) :
  (∃ oproi, is_stack_head (mkItem Unique (Tagged ti) oproi) stk) →
  access1 stk AccessWrite t cids = Some (n, stk') →
  Tagged ti ≠ t →
  ∀ pm opro, (mkItem pm (Tagged ti) opro) ∈ stk' → False.
Proof.
  intros HD. rewrite /access1.
  case find_granting as [[n' pm']|] eqn:GRANT; [|done]. simpl.
  case find_first_write_incompatible as [idx|] eqn:INC; [|done]. simpl.
  case remove_check as [stk1|] eqn:Eq; [|done].
  simpl. intros ?. simplify_eq.
  intros NEQ. destruct HD as [oproi HD].
  have HD' := find_granting_incompatible_head _ _ _ _ _ _ _ _ HD NEQ GRANT.
  have Gt0 := find_first_write_incompatible_head _ _ _ _ _ _ HD' (ltac:(done)) INC.
  rewrite -{1}(take_drop n stk) in ND.
  intros pm opro.
  have EQH : take n stk !! 0%nat = Some (mkItem Unique (Tagged ti) oproi).
  { destruct HD' as [? Eq']. by rewrite Eq'. }
  eapply (remove_check_incompatible_items _ _ _ _ idx
            (mkItem Unique (Tagged ti) oproi) O ti ND); done.
Qed.

(* Reading *)
Lemma replace_check'_incompatible_items cids acc stk stk' stk0 it t
  (ND: stack_item_tagged_NoDup (acc ++ stk ++ stk0)) :
  it.(tg) = Tagged t → it.(perm) = Unique → it ∈ stk →
  replace_check' cids acc stk = Some stk' →
  ∀ it', it'.(tg) = Tagged t → it' ∈ (stk' ++ stk0) → it'.(perm) = Disabled.
Proof.
  intros Eqt IU IN. revert acc ND.
  induction stk as [|it0 stk IH]; simpl; intros acc ND; [set_solver|].
  case decide => ?; [case check_protector; [|done]|]; last first.
  { move => /(IH ltac:(set_solver)).
    rewrite -(app_assoc acc [it0] (stk ++ stk0)).
    intros IH1 it' Eqit' Init'. apply IH1; [done..|]. clear -Init'. set_solver. }
  move => RC.
  have ND3: stack_item_tagged_NoDup
    ((acc ++ [mkItem Disabled it0.(tg) it0.(protector)]) ++ stk ++ stk0).
  { move : ND. clear.
    rewrite (app_assoc acc [it0]) 2!(Permutation_app_comm acc) -2!app_assoc.
    rewrite /stack_item_tagged_NoDup 2!filter_cons /=.
    case decide => ?; [rewrite decide_True //|rewrite decide_False //]. }
  have IN1:= (replace_check'_acc_result _ _ _ _ RC).
  have IN': mkItem Disabled it0.(tg) it0.(protector) ∈ stk' ++ stk0 by set_solver.
  have ND4 := replace_check'_stack_item_tagged_NoDup_2 _ _ _ _ _ RC ND3.
  apply elem_of_cons in IN as [|IN].
  { intros it' Eqt' Init'. subst it0.
    have ? : it' = mkItem Disabled it.(tg) it.(protector).
    { apply (stack_item_tagged_NoDup_eq _ _ _ t ND4 Init' IN' Eqt').
      by rewrite Eqt. }
    by subst it'. }
  apply (IH IN _ ND3 RC).
Qed.

Lemma replace_check_incompatible_items cids stk stk' stk0 it t
  (ND: stack_item_tagged_NoDup (stk ++ stk0)) :
  it.(tg) = Tagged t → it.(perm) = Unique → it ∈ stk →
  replace_check cids stk = Some stk' →
  ∀ it', it'.(tg) = Tagged t → it' ∈ (stk' ++ stk0) → it'.(perm) = Disabled.
Proof. intros ????. eapply (replace_check'_incompatible_items _ []); eauto. Qed.

Lemma access1_read_replace_incompatible_head stk t ti cids n stk'
  (ND: stack_item_tagged_NoDup stk) :
  (∃ oproi, is_stack_head (mkItem Unique (Tagged ti) oproi) stk) →
  access1 stk AccessRead t cids = Some (n, stk') →
  Tagged ti ≠ t →
  ∀ pm opro, (mkItem pm (Tagged ti) opro) ∈ stk' → pm = Disabled.
Proof.
  intros HD. rewrite /access1.
  case find_granting as [[n' pm']|] eqn:GRANT; [|done]. simpl.
  case replace_check as [stk1|] eqn:Eq; [|done].
  simpl. intros ?. simplify_eq.
  intros NEQ pm opro. destruct HD as [oproi HD].
  rewrite -{1}(take_drop n stk) in ND.
  eapply (replace_check_incompatible_items _ _ _ _ (mkItem Unique (Tagged ti) oproi) ti ND);
    try done.
  have HD' := find_granting_incompatible_head _ _ _ _ _ _ _ _ HD NEQ GRANT.
  clear -HD'. destruct HD' as [? EqD]. rewrite EqD. by left.
Qed.

Lemma active_SRO_elem_of t stk :
  t ∈ active_SRO stk → ∃ i it, stk !! i = Some it ∧ it.(tg) = Tagged t ∧
  it.(perm) = SharedReadOnly ∧
  ∀ j jt, (j < i)%nat → stk !! j = Some jt → jt.(perm) = SharedReadOnly.
Proof.
  induction stk as [|it' stk IH]; simpl; [set_solver|].
  destruct it'.(perm) eqn:Eqp; [set_solver..| |set_solver].
  destruct it'.(tg) eqn:Eqt;
    [rewrite elem_of_union elem_of_singleton; intros [?|Eq]; [subst|]|].
  - exists O, it'. repeat split; [done..|intros; lia].
  - destruct (IH Eq) as (i & it1 & ? & ? & ? & HL).
    exists (S i), it1. repeat split; [done..|].
    intros j jt Lt. destruct j; simpl.
    + intros. by simplify_eq.
    + apply HL. lia.
  - intros Eq. destruct (IH Eq) as (i & it1 & ? & ? & ? & HL).
    exists (S i), it1. repeat split; [done..|].
    intros j jt Lt. destruct j; simpl.
    + intros. by simplify_eq.
    + apply HL. lia.
Qed.

Lemma active_SRO_elem_of_inv i it t stk :
  stk !! i = Some it → it.(tg) = Tagged t →
  it.(perm) = SharedReadOnly →
  (∀ j jt, (j < i)%nat → stk !! j = Some jt → jt.(perm) = SharedReadOnly) →
  t ∈ active_SRO stk.
Proof.
  revert i.
  induction stk as [|it' stk IH]; [set_solver|].
  intros [|i]; intros Eq; simpl in Eq.
  { simplify_eq. intros. apply active_SRO_cons_elem_of. split; [done|by left]. }
  intros Eqt SRO PREV.
  apply active_SRO_cons_elem_of.
  have SRO' := PREV O it' ltac:(lia) eq_refl. split; [done|].
  right. apply (IH _ Eq Eqt SRO).
  intros j jt Lt. apply (PREV (S j) jt). lia.
Qed.

Lemma find_granting_incompatible_active_SRO stk t ti idx pm
  (HD: ti ∈ active_SRO stk) :
  find_granting stk AccessWrite t = Some (idx, pm) →
  ti ∈ active_SRO (take idx stk).
Proof.
  revert idx. induction stk as [|it stk IH]; simpl; intros idx; [set_solver|].
  move : HD. rewrite /find_granting /=.
  destruct it.(perm) eqn:Eqp; [set_solver..| |set_solver].
  rewrite decide_False; last (intros [PM _]; by rewrite Eqp in PM).
  destruct (list_find (matched_grant AccessWrite t) stk)
    as [[n' pm']|] eqn:Eql; [|done].
  simpl. intros IN ?. simplify_eq. rewrite /= Eqp. move : IN.
  destruct it.(tg) eqn:Eqt; simpl;
    [rewrite elem_of_union elem_of_singleton; intros [|IN]; [subst|]|]; simpl.
  - set_solver.
  - rewrite elem_of_union. right. apply IH; first done. by rewrite /find_granting Eql.
  - intros ?. apply IH; first done. by rewrite /find_granting Eql.
Qed.

Lemma find_first_write_incompatible_active_SRO stk pm idx :
  find_first_write_incompatible stk pm = Some idx →
  ∀ t, t ∈ active_SRO stk → ∃ i it, stk !! i = Some it ∧
    it.(perm) = SharedReadOnly ∧
    it.(tg) = Tagged t ∧ (i < idx)%nat ∧
    (∀ (j : nat) (jt : item), (j < i)%nat → stk !! j = Some jt →
        jt.(perm) = SharedReadOnly).
Proof.
  intros EF t IN.
  destruct (active_SRO_elem_of _ _ IN) as (i1 & it1 & Eqit1 & Eqt1 & Eqp1 & HL1).
  move  : EF.
  destruct pm; [| |done..].
  { simpl. intros. simplify_eq. exists i1, it1.
    repeat split; [done..| |done]. by eapply lookup_lt_Some. }
  simpl.
  destruct (list_find_elem_of (λ it, it.(perm) ≠ SharedReadWrite) (reverse stk) it1)
    as [[n1 pm1] Eqpm1].
  { rewrite elem_of_reverse. by eapply list_elem_of_lookup_2. }
  { by rewrite Eqp1. }
  rewrite Eqpm1. intros. simplify_eq.
  exists i1, it1. repeat split; [done..| |done].
  apply list_find_Some_not_earlier in Eqpm1 as (Eqrv & Eqpmv & HLv).
  case (decide (i1 + n1 < length stk)%nat) => [?|]; [lia|].
  rewrite Nat.nlt_ge => GE. exfalso.
  destruct (reserve_lookup _ _ _ Eqit1) as (j & Eqj & Eql).
  have Lt: (j < n1)%nat by lia.
  specialize (HLv _ _ Lt Eqj). rewrite Eqp1 in HLv. by apply HLv.
Qed.

Lemma access1_write_remove_incompatible_active_SRO stk t ti cids n stk'
  (ND: stack_item_tagged_NoDup stk) :
  (ti ∈ active_SRO stk) →
  access1 stk AccessWrite t cids = Some (n, stk') →
  ∀ pm opro, (mkItem pm (Tagged ti) opro) ∈ stk' → False.
Proof.
  intros HD. rewrite /access1.
  case find_granting as [[n' pm']|] eqn:GRANT; [|done]. simpl.
  case find_first_write_incompatible as [idx|] eqn:INC; [|done]. simpl.
  case remove_check as [stk1|] eqn:Eq; [|done].
  simpl. intros ?. simplify_eq.
  intros NEQ.
  have HD' := find_granting_incompatible_active_SRO _ _ _ _ _ HD GRANT.
  destruct (find_first_write_incompatible_active_SRO _ _ _ INC _ HD')
    as (i & it & Eqi & Eqp & Eqt & Lt & HL).
  rewrite -{1}(take_drop n stk) in ND. intros ?.
  eapply (remove_check_incompatible_items _ _ _ _ idx it i ti ND); eauto.
Qed.

Lemma access1_incompatible_head_protector stk t ti kind cids n stk' c :
  (is_stack_head (mkItem Unique (Tagged t) (Some c)) stk) →
  c ∈ cids →
  access1 stk kind ti cids = Some (n, stk') →
  ti = Tagged t.
Proof.
  intros HD ACTIVE. case (decide (Tagged t = ti)) => NEQ; [done|].
  rewrite /access1.
  case find_granting as [[n' pm']|] eqn:GRANT; [|done]. simpl.
  destruct kind.
  - case replace_check as [stk1|] eqn:Eq; [|done].
    simpl. intros ?. simplify_eq.
    have HD' := find_granting_incompatible_head _ _ _ _ _ _ _ _ HD NEQ GRANT.
    destruct HD' as [stk' Eqs].
    move : Eq.
    rewrite Eqs /replace_check /= /check_protector /= /is_active bool_decide_true //.
  - have HD' := find_granting_incompatible_head _ _ _ _ _ _ _ _ HD NEQ GRANT.
    case find_first_write_incompatible as [idx|] eqn:INC; [|done]. simpl.
    have NONEZ: (0 < idx)%nat.
    { eapply (find_first_write_incompatible_head _ _ _ _ _ _ HD'); eauto. }
    destruct HD' as [stk2 Eqs].
    rewrite Eqs /=. destruct idx; [lia|].
    rewrite /= /check_protector /= /is_active bool_decide_true //.
Qed.


Lemma tag_unique_head_access cids stk t opro kind :
  is_stack_head (mkItem Unique t opro) stk →
  ∃ n, access1 stk kind t cids = Some (n, stk).
Proof.
  intros [stk1 Eqstk].
  rewrite /access1.
  have Eq1: list_find (matched_grant kind t) stk =
    Some (O, mkItem Unique t opro).
  { apply list_find_Some_not_earlier. split; last split.
    - rewrite Eqstk //.
    - done.
    - intros; lia. }
  have Eq2: find_granting stk kind t = Some (O, Unique).
  { rewrite /= /find_granting Eq1 //. }
  rewrite Eq2 /=.
  exists O. by destruct kind.
Qed.

Lemma replace_check'_preserve cids acc stk :
  (∀ it, it ∈ stk → it.(perm) ≠ Unique) →
  replace_check' cids acc stk = Some (acc ++ stk).
Proof.
  revert acc. induction stk as [|it' stk IH]; intros acc IN.
  { rewrite /= app_nil_r //. }
  rewrite /= decide_False; last by (apply IN; left).
  rewrite (app_assoc acc [it'] stk). apply IH. set_solver.
Qed.

Lemma replace_check_preserve cids stk :
  (∀ it, it ∈ stk → it.(perm) ≠ Unique) →
  replace_check cids stk = Some stk.
Proof. apply replace_check'_preserve. Qed.

Lemma tag_SRO_top_access cids stk t :
  t ∈ active_SRO stk →
  ∃ n, access1 stk AccessRead (Tagged t) cids = Some (n, stk).
Proof.
  intros IN.
  destruct (active_SRO_elem_of _ _ IN) as (i1 & it1 & Eqit1 & Eqt1 & Eqp1 & HL1).
  rewrite /= /access1.
   have Eq1: is_Some (list_find (matched_grant AccessRead (Tagged t)) stk).
  { apply (list_find_elem_of _ _ it1).
    - by eapply list_elem_of_lookup_2.
    - by rewrite /matched_grant Eqp1. }
  destruct Eq1 as [[n2 it2] Eq2].
  have Eq3: find_granting stk AccessRead (Tagged t) = Some (n2, it2.(perm)).
  { rewrite /= /find_granting Eq2 //. }
  rewrite Eq3 /=. exists n2.
  rewrite replace_check_preserve.
  - rewrite /= take_drop //.
  - apply list_find_Some_not_earlier in Eq2 as (Eq2 & GR & LT).
    have Lti1: (n2 ≤ i1)%nat.
    { case (decide (n2 ≤ i1)%nat) => [//|/Nat.nle_gt Lt].
      exfalso. apply (LT _ _ Lt Eqit1). rewrite /matched_grant Eqp1 //. }
    intros it [k Eqk]%list_elem_of_lookup_1.
    have Ltk : (k < n2)%nat.
    { rewrite -(length_take_le stk n2).
      - by eapply lookup_lt_Some.
      - apply Nat.lt_le_incl; by eapply lookup_lt_Some. }
    have HL: stk !! k = Some it. { rewrite -(lookup_take_lt _ n2) //. }
    have Ltk2: (k < i1)%nat. { eapply Nat.lt_le_trans; eauto. }
    by rewrite (HL1 _ _ Ltk2 HL).
Qed.

(** Tag-on-top *)
Lemma tag_on_top_write σ l tg stks :
  tag_on_top σ.(sst) l tg Unique →
  memory_written (sst σ) (scs σ) l (Tagged tg) 1 = Some stks →
  tag_on_top stks l tg Unique.
Proof.
  rewrite /memory_written /tag_on_top /= shift_loc_0.
  destruct (sst σ !! l) as [s|] eqn:Hlk; last done. simpl.
  destruct s as [|it st]; first done. simpl.
  destruct it as [perm tg' prot']. intros [prot ?]; simplify_eq/=.
  edestruct tag_unique_head_access as [n ->].
  { eexists. done. }
  simpl. intros. simplify_eq/=. eexists. rewrite lookup_insert_eq.
  simpl. done.
Qed.

Lemma tag_on_top_grant_uniq_SRO stk old it cids  stk'
  (UNIQ: it.(perm) = Unique ∨ it.(perm) = SharedReadOnly) :
  grant stk old it cids = Some stk' → is_stack_head it stk'.
Proof.
  rewrite /grant.
  case find_granting as [gip|]; [|done].
  destruct UNIQ as [UNIQ|UNIQ];
  rewrite /= UNIQ /=; (case access1 => [[n1 stk1]/=|//]);
  (destruct stk1; [|case decide => ?]; intros; simplify_eq; by eexists).
Qed.

Lemma tag_on_top_reborrowN_uniq_SRO α cids l n to tn pm α' pro
  (UNIQ: pm = Unique ∨ pm = SharedReadOnly) :
  reborrowN α cids l n to (Tagged tn) pm pro = Some α' →
  ∀ i, (i < n)%nat → tag_on_top α' (l +ₗ i) tn pm.
Proof.
  intros RB i Lt.
  destruct (for_each_lookup_case_2 _ _ _ _ _ RB) as [EQ _].
  specialize (EQ _ Lt) as (stk & stk' & Eq & Eq' & GR).
  apply tag_on_top_grant_uniq_SRO in GR as [stk1 Eq1]; [|done].
  rewrite /tag_on_top Eq' Eq1 /=. by eexists.
Qed.

Lemma tag_on_top_retag_ref_uniq α cids nxtp l old T pro tn α' nxtp' :
  retag_ref α cids nxtp l old T (UniqueRef false) pro
    = Some (Tagged tn, α', nxtp') →
  ∀ i, (i < tsize T)%nat → tag_on_top α' (l +ₗ i) tn Unique.
Proof.
  intros RT i. destruct (tsize T) as [|n] eqn:Eqsz; [lia|].
  rewrite -Eqsz.
  move : RT. rewrite /retag_ref {1}Eqsz /=.
  case reborrowN as [α1|] eqn:RB; [|done]. simpl. intros ?. simplify_eq.
  eapply tag_on_top_reborrowN_uniq_SRO; eauto.
Qed.

Lemma tag_on_top_retag_ref_shr α cids nxtp l old T pro tn α' nxtp'
  (FRZ: is_freeze T) :
  retag_ref α cids nxtp l old T SharedRef pro
    = Some (Tagged tn, α', nxtp') →
  ∀ i, (i < tsize T)%nat → tag_on_top α' (l +ₗ i) tn SharedReadOnly.
Proof.
  intros RT i. destruct (tsize T) as [|n] eqn:Eqsz; [lia|].
  rewrite -Eqsz.
  move : RT. rewrite /retag_ref {1}Eqsz /= visit_freeze_sensitive_is_freeze //.
  case reborrowN as [α1|] eqn:RB; [|done]. simpl. intros ?. simplify_eq.
  eapply tag_on_top_reborrowN_uniq_SRO; eauto.
Qed.

Lemma tag_on_top_shr_active_SRO α l t :
  tag_on_top α l t SharedReadOnly →
  ∃ stk, α !! l = Some stk ∧ t ∈ active_SRO stk.
Proof.
  intros [pro Eq]. destruct (α !! l) as [stk|]; [|done].
  simpl in Eq. destruct stk as [|it stk']; [done|].
  simpl in Eq. simplify_eq. eexists. split; [done|].
  rewrite /= elem_of_union elem_of_singleton. by left.
Qed.

(* retag *)
Lemma retag_nxtp_change α cids c nxtp l otag ntag rk pk T α' nxtp'
  (TS: (O < tsize T)%nat)
  (RK: match pk with | RawPtr _ => rk = RawRt | _ => True end) :
  retag α nxtp cids c l otag rk pk T = Some (ntag, α', nxtp') →
  nxtp' = S nxtp ∧
  match ntag with
  | Untagged => True
  | Tagged t => nxtp = t
  end.
Proof.
  assert (∃ n, tsize T = S n) as [n EqT].
  { destruct (tsize T); [lia|by eexists]. }
  destruct pk as [[]| |]; [| |subst rk|]; rewrite /retag /= /retag_ref EqT;
  (case reborrow as [α1|]; [|done]); simpl; intros; by simplify_eq.
Qed.

Lemma retag_change_case α cids c nxtp l otag ntag rk pk T α' nxtp' :
  retag α nxtp cids c l otag rk pk T = Some (ntag, α', nxtp') →
  tsize T = O ∧ α' = α ∧ nxtp' = nxtp ∧ ntag = otag ∨
  (O < tsize T)%nat ∧
    match pk, rk with
    | RawPtr _, RawRt => True
    | RawPtr _, _ => α' = α ∧ nxtp' = nxtp ∧ ntag = otag
    | _, _ => True
    end.
Proof.
  destruct (tsize T) as [|n] eqn:EqT.
  - rewrite /retag /retag_ref EqT /=.
    destruct pk as [[]| |]; [| |destruct rk|]; simpl; intros; simplify_eq;
      by left.
  - rewrite /retag /retag_ref EqT /=.
    destruct pk as [[]| |]; [| |destruct rk|]; simpl; intros; simplify_eq;
      right; (split; [lia|done]).
Qed.

Lemma retag_change_tag α cids c nxtp l otag ntag rk pk T α' nxtp' :
  retag α nxtp cids c l otag rk pk T = Some (ntag, α', nxtp') →
  ntag = otag ∨
  match ntag with
  | Tagged t => t = nxtp ∧ nxtp' = S nxtp
  | _ => True
  end.
Proof.
  intros RT.
  destruct (retag_change_case _ _ _ _ _ _ _ _ _ _ _ _ RT) as [[?[?[??]]]|[? Eq]].
  - simplify_eq; by left.
  - destruct pk.
    + apply retag_nxtp_change in RT as []; [|done..]. right. by destruct ntag.
    + destruct rk.
      * left. by destruct Eq as [_ []]; subst.
      * left. by destruct Eq as [_ []]; subst.
      * apply retag_nxtp_change in RT as []; [|done..]. right. by destruct ntag.
      * left. by destruct Eq as [_ []]; subst.
    + apply retag_nxtp_change in RT as []; [|done..]. right. by destruct ntag.
Qed.

Lemma retag_change_nxtp α cids c nxtp l otag ntag rk pk T α' nxtp' :
  retag α nxtp cids c l otag rk pk T = Some (ntag, α', nxtp') →
  (nxtp ≤ nxtp')%nat.
Proof.
  intros RT.
  destruct (retag_change_case _ _ _ _ _ _ _ _ _ _ _ _ RT) as [[?[?[??]]]|[? Eq]].
  - by simplify_eq.
  - destruct pk.
    + apply retag_nxtp_change in RT as []; [lia|done..].
    + destruct rk.
      * by destruct Eq as [_ [? _]]; subst.
      * by destruct Eq as [_ [? _]]; subst.
      * apply retag_nxtp_change in RT as []; [lia|done..].
      * by destruct Eq as [_ [? _]]; subst.
    + apply retag_nxtp_change in RT as []; [lia|done..].
Qed.

Lemma retag_change_ref_NZST α nxtp cids c l otag rk mut T ntag α' nxtp':
  (O < tsize T)%nat  →
  retag α nxtp cids c l otag rk (RefPtr mut) T = Some (ntag, α', nxtp') →
  ntag = Tagged nxtp ∧ nxtp' = S nxtp.
Proof.
  intros ST.
  assert (∃ n, tsize T = S n) as [n EqT].
  { destruct (tsize T); [lia|by eexists]. }
  destruct mut; rewrite /retag /= /retag_ref EqT;
  (case reborrow as [α1|]; [|done]); simpl; intros; by simplify_eq.
Qed.

Lemma unsafe_action_stacks_changed
  (f: stacks → _ → nat → _ → _) α l (last fsz usz: nat) α' ln cn
  (P: option stack → option stack → bool → Prop)
  (HF: ∀ α1 α2 l n b, f α1 l n b = Some α2 →
      (∀ l', (∀ (i : nat), (i < n)%nat → l' ≠ l +ₗ i) → α2 !! l' = α1 !! l') ∧
      (∀ (i : nat), (i < n)%nat → P (α1 !! (l +ₗ i)) (α2 !! (l +ₗ i)) b)):
  unsafe_action f α l last fsz usz = Some (α', (ln, cn)) →
  (last ≤ ln)%nat ∧
  (∀ l', (∀ (i : nat), (last ≤ i < ln)%nat → l' ≠ l +ₗ i) → α' !! l' = α !! l') ∧
  (∀ (i : nat), (last ≤ i < ln)%nat → ∃ b, P (α !! (l +ₗ i)) (α' !! (l +ₗ i)) b).
Proof.
  rewrite /unsafe_action.
  case f as [α1|] eqn:Eqf1; [simpl|done]. case (f α1) eqn:Eqf2; [simpl|done].
  intros ?. simplify_eq. split; [lia|].
  destruct (HF _ _ _ _ _ Eqf1) as [HF1 Eq1].
  destruct (HF _ _ _ _ _ Eqf2) as [HF2 Eq2]. split.
  { intros ? NEQ. rewrite HF2; last first.
    - intros i Lt.
      rewrite shift_loc_assoc -Nat2Z.inj_add. apply NEQ. lia.
    - rewrite HF1 //.
      intros ??. rewrite shift_loc_assoc -Nat2Z.inj_add. apply NEQ. lia. }
  intros i [Le Lt].
  case (decide (i < last + fsz)%nat) => [Lt1|Ge1].
  - have Le1: (i - last < fsz)%nat by lia.
    have Eql: l +ₗ i = l +ₗ last +ₗ (i - last)%nat.
    { rewrite shift_loc_assoc. f_equal. lia. }
    specialize (Eq1 _ Le1). rewrite -Eql in Eq1. rewrite HF2.
    + by exists true.
    + intros j Ltj.
      rewrite shift_loc_assoc -Nat2Z.inj_add.
      intros ?%shift_loc_inj%Nat2Z.inj. subst i. lia.
  - apply Nat.nlt_ge in Ge1.
    have Le1: (i - (last + fsz) < usz)%nat by lia.
    have Eql: l +ₗ i = l +ₗ (last + fsz)%nat +ₗ (i - (last + fsz))%nat.
    { rewrite shift_loc_assoc. f_equal. lia. }
    specialize (Eq2 _ Le1). rewrite -Eql in Eq2. rewrite -HF1.
    + by exists false.
    + intros ??. rewrite shift_loc_assoc -Nat2Z.inj_add.
      intros ?%shift_loc_inj%Nat2Z.inj. subst i. lia.
Qed.


Lemma visit_freeze_sensitive'_stacks_changed l (f: stacks → _ → _ → _ → _)
  α α' last cur T l' c'
  (P: option stack → option stack → bool → Prop) :
  let HF (f: stacks → loc → nat → bool → option stacks) :=
    ∀ α1 α2 l n b, f α1 l n b = Some α2 →
      (∀ l', (∀ (i : nat), (i < n)%nat → l' ≠ l +ₗ i) → α2 !! l' = α1 !! l') ∧
      (∀ (i : nat), (i < n)%nat → P (α1 !! (l +ₗ i)) (α2 !! (l +ₗ i)) b) in
  let UC α1 α2 (l: loc) (lo ln: nat) :=
    (lo ≤ ln)%nat ∧
    (∀ l', (∀ (i : nat), (lo ≤ i < ln)%nat → l' ≠ l +ₗ i) → α2 !! l' = α1 !! l') ∧
    (∀ (i : nat), (lo ≤ i < ln)%nat → ∃ b, P (α1 !! (l +ₗ i)) (α2 !! (l +ₗ i)) b) in
  HF f →
  visit_freeze_sensitive' l f α last cur T = Some (α', (l', c')) →
  UC α α' l last l'.
Proof.
  intros HF UC.
  apply (visit_freeze_sensitive'_elim
    (* general goal P *)
    (λ l f α l1 c1 T oalc, ∀ α' l' c',
      HF f → oalc = Some (α', (l', c')) → UC α α' l l1 l')
    (λ l f _ _ _ Ts1 α l1 c1 Ts2 oalc, ∀ α' l' c',
      HF f → oalc = Some (α', (l', c')) →
          UC α α' l l1 l')); rewrite /HF /UC.
  - clear. intros l f α1 l1 c1 s1 α2 l2 c2 HF ?.
    simplify_eq. split; [done|].
    split; [naive_solver|]. clear. intros i []. lia.
  - clear. intros l f α1 l1 c1 ?? α2 l2 c2 HF ?.
    simplify_eq. split; [done|].
    split; [naive_solver|]. clear. intros i []. lia.
  - (* Unsafe case *)
    clear. intros ?? α l1 c1 ? α2 l2 c2 HF.
    eapply unsafe_action_stacks_changed; eauto.
  - (* Union case *)
    clear. intros ????????? HF0. case is_freeze.
    + intros. simplify_eq. do 2 (split; [done|]).
      clear. intros ? []. lia.
    + intros UN. eapply unsafe_action_stacks_changed; eauto.
  - clear. intros ?????? IH ??? HF. case is_freeze.
    + intros. simplify_eq. do 2 (split; [done|]).
      clear. intros ? []. lia.
    + intros VS. eapply (IH _ _ _ HF); eauto.
  - (* Sum case *)
    clear. intros ????????? HF. case is_freeze.
    + intros. simplify_eq. do 2 (split; [done|]).
      clear. intros ? []. lia.
    + intros UN. eapply unsafe_action_stacks_changed; eauto.
  - clear. intros l f α1 l1 c1 Ts1 α2 l2 c2 α3 l3 c3 HF ?.
    simplify_eq. split; [done|].
    split; [naive_solver|]. clear. intros i []. lia.
  - (* Product case *)
    clear. intros l f α0 l0 c0 Ts1 α2 l2 c2 T Ts2 IH1 IH2 α3 l3 c3 HF.
    case visit_freeze_sensitive' as [alc|] eqn:Eqa; [|done].
    intros VS. destruct alc as [α1 [l1 c1]]. simpl in VS.
    destruct (IH2 α1 l1 c1 HF eq_refl) as [Le2 [IH21 IH22]].
    simpl in IH21, IH22.
    destruct (IH1 (α1, (l1,c1)) α3 l3 c3) as [Le1 [IH11 IH12]];
      [done..|simpl in Le1; split]; [lia|].
    simpl in IH11, IH12.
    split.
    + intros ? NC. rewrite IH11; [rewrite IH21 //|].
      * intros ??. apply NC. lia.
      * intros ??. apply NC. lia.
    + intros i [Le Lt].
      case (decide (l1 ≤ i)%nat) => [Gel1|Ltl1].
      * rewrite -IH21; [by apply IH12|].
        intros j [Lej Ltj] ?%shift_loc_inj%Nat2Z.inj. subst j. lia.
      * apply Nat.nle_gt in Ltl1.
        rewrite IH11; [by apply IH22|].
        intros j [Lej Ltj] ?%shift_loc_inj%Nat2Z.inj. subst j. lia.
Qed.

Lemma visit_freeze_sensitive_stacks_unchanged l
  (f: stacks → _ → _ → _ → _)
  α α' T
  (P: option stack → option stack → bool → Prop) :
  (∀ α1 α2 l n b, f α1 l n b = Some α2 →
      (∀ l', (∀ (i : nat), (i < n)%nat → l' ≠ l +ₗ i) → α2 !! l' = α1 !! l') ∧
      (∀ (i : nat), (i < n)%nat → P (α1 !! (l +ₗ i)) (α2 !! (l +ₗ i)) b)) →
  visit_freeze_sensitive l T f α = Some α' →
  (∀ l', (∀ (i : nat), (i < tsize T)%nat → l' ≠ l +ₗ i) → α' !! l' = α !! l') ∧
  (∀ (i : nat), (i < tsize T)%nat → ∃ b, P (α !! (l +ₗ i)) (α' !! (l +ₗ i)) b).
Proof.
  intros HF.
  rewrite /visit_freeze_sensitive.
  case visit_freeze_sensitive' as [[α1 [l1 c1]]|] eqn:Eq; [|done].
  intros Eqf.
  have Eq' := Eq.
  apply visit_freeze_sensitive'_offsets in Eq' as [_ Eq'].
  rewrite 2!Nat.add_0_l in Eq'.
  eapply visit_freeze_sensitive'_stacks_changed in Eq as [_ [EQ1 EQ2]]; [|done].
  specialize (HF _ _ _ _ _ Eqf) as [HF1 HF2].
  split.
  - intros l' NEq. rewrite HF1; last first.
    { intros i Lt. rewrite shift_loc_assoc -Nat2Z.inj_add.
      apply NEq. rewrite -Eq'. lia. }
    rewrite EQ1 //.
    intros i [_ Lti]. apply NEq. rewrite -Eq'. lia.
  - intros i Lt. rewrite -Eq' in Lt.
    case (decide (i < l1)%nat) => [Ltl1|Gel1].
    + rewrite HF1.
      * apply EQ2. split; [lia|done].
      * intros j Ltj. rewrite shift_loc_assoc_nat.
        intros ?%shift_loc_inj%Nat2Z.inj. subst i. lia.
    + apply Nat.nlt_ge in Gel1. rewrite -EQ1.
      * have Ltc1: (i - l1 < c1)%nat by lia.
        specialize (HF2 _ Ltc1).
        have Eql: l +ₗ l1 +ₗ (i - l1)%nat = l +ₗ i.
        { rewrite shift_loc_assoc_nat. f_equal. lia. }
        rewrite Eql in HF2. by exists true.
      * intros j [_ Ltj] ?%shift_loc_inj%Nat2Z.inj. subst i. lia.
Qed.

Lemma reborrowN_lookup_case (α1 α2 : stacks) cids l n old new pm protector
  (EQB : reborrowN α1 cids l n old new pm protector = Some α2) :
  (∀ l', (∀ (i : nat), (i < n)%nat → l' ≠ l +ₗ i) → α2 !! l' = α1 !! l') ∧
  (∀ i, (i < n)%nat → ∃ stk stk',
    α1 !! (l +ₗ i) = Some stk ∧
    α2 !! (l +ₗ i) = Some stk' ∧
    let item := mkItem pm new protector in
    grant stk old item cids = Some stk').
Proof.
  destruct (for_each_lookup_case_2 _ _ _ _ _ EQB) as [HL1 HL2].
  split; [done|].
  intros i Lt. destruct (HL1 _ Lt) as (stk & stk' & Eq1 & Eq2 & GR).
  naive_solver.
Qed.

Lemma reborrowN_visit_freeze_sensitive_case α α' l T cids old new protector :
  let permB (b: bool) := if b then SharedReadOnly else SharedReadWrite in
  let item (b: bool) := mkItem (permB b) new protector in
  visit_freeze_sensitive l T
        (λ α' l' sz frozen,
          (* If is in Unsafe, use SharedReadWrite, otherwise SharedReadOnly *)
          reborrowN α' cids l' sz old new (permB frozen) protector) α = Some α' →
  (∀ l', (∀ (i : nat), (i < tsize T)%nat → l' ≠ l +ₗ i) → α' !! l' = α !! l') ∧
  (∀ i, (i < tsize T)%nat → ∃ stk stk',
    α !! (l +ₗ i) = Some stk ∧
    α' !! (l +ₗ i) = Some stk' ∧ ∃ b,
    grant stk old (item b) cids = Some stk').
Proof.
  intros permB item VS.
  set P: option stack → option stack → bool → Prop :=
    λ ostk ostk' b, ∃ stk stk', ostk = Some stk ∧ ostk' = Some stk' ∧
      grant stk old (item b) cids = Some stk'.
  apply (visit_freeze_sensitive_stacks_unchanged _ _ _ _ _ P) in VS.
  - destruct VS as [VS1 VS2]. split; [done|].
    intros i Lt. destruct (VS2 _ Lt) as (b & stk & stk' & Eq1 & Eq2 & Eq3).
    naive_solver.
  - clear. intros α1 α2 l n b [RB1 RB2]%reborrowN_lookup_case.
    split; [done|]. intros i Lt.
    specialize (RB2 _ Lt) as (stk & stk' & Eq1 & Eq2 & Eq3).
    rewrite Eq1 Eq2. exists stk, stk'. naive_solver.
Qed.

Lemma reborrow_Some α α' cids l old T rk new protector :
  reborrow α cids l old T rk new protector = Some α' →
  (∀ l', (∀ (i : nat), (i < tsize T)%nat → l' ≠ l +ₗ i) → α' !! l' = α !! l') ∧
  (∀ i, (i < tsize T)%nat → ∃ stk stk',
    α !! (l +ₗ i) = Some stk ∧
    α' !! (l +ₗ i) = Some stk' ∧
    match rk with
    | SharedRef | RawRef false =>
      ∃ b : bool, grant stk old
                 (mkItem (if b then SharedReadOnly else SharedReadWrite)
                          new protector) cids = Some stk'
    | UniqueRef false =>
      grant stk old (mkItem Unique new protector) cids = Some stk'
    | UniqueRef true | RawRef true =>
      grant stk old (mkItem SharedReadWrite new protector) cids = Some stk'
    end).
Proof.
  destruct rk as [[]| |[]]; simpl.
  - apply reborrowN_lookup_case.
  - apply reborrowN_lookup_case.
  - apply reborrowN_visit_freeze_sensitive_case.
  - apply reborrowN_lookup_case.
  - apply reborrowN_visit_freeze_sensitive_case.
Qed.

Lemma retag_ref_Some α cids nxtp l old T rk protector new α' nxtp' :
  retag_ref α cids nxtp l old T rk protector = Some (new, α', nxtp') →
  (∀ l', (∀ (i : nat), (i < tsize T)%nat → l' ≠ l +ₗ i) → α' !! l' = α !! l') ∧
  (∀ i, (i < tsize T)%nat → ∃ stk stk',
    α !! (l +ₗ i) = Some stk ∧
    α' !! (l +ₗ i) = Some stk' ∧
    match rk with
    | SharedRef | RawRef false =>
      ∃ b : bool, grant stk old
                 (mkItem (if b then SharedReadOnly else SharedReadWrite)
                          new protector) cids = Some stk'
    | UniqueRef false =>
      grant stk old (mkItem Unique new protector) cids = Some stk'
    | UniqueRef true | RawRef true =>
      grant stk old (mkItem SharedReadWrite new protector) cids = Some stk'
    end).
Proof.
  rewrite /retag_ref. destruct (tsize T) eqn:EqT.
  - intros. simplify_eq. split; [done|intros; lia].
  - rewrite -EqT. case reborrow as [α1|] eqn:Eq; [|done]. simpl.
    intros. simplify_eq. by apply reborrow_Some.
Qed.

Lemma retag_Some α nxtp c cids l old rk pk T new α' nxtp' :
  retag α nxtp cids c l old rk pk T = Some (new, α', nxtp') →
  (∀ l', (∀ (i : nat), (i < tsize T)%nat → l' ≠ l +ₗ i) → α' !! l' = α !! l') ∧
  match pk, rk with
  (* Mutable reference *)
  | RefPtr Mutable, _ =>
      (∀ i, (i < tsize T)%nat → ∃ stk stk',
        α !! (l +ₗ i) = Some stk ∧
        α' !! (l +ₗ i) = Some stk' ∧
        let protector := adding_protector rk c in
        let perm := if (is_two_phase rk) then SharedReadWrite else Unique in
        grant stk old (mkItem perm new protector) cids = Some stk')
  (* Immutable reference *)
  | RefPtr Immutable, _ =>
      (∀ i, (i < tsize T)%nat → ∃ stk stk',
        α !! (l +ₗ i) = Some stk ∧
        α' !! (l +ₗ i) = Some stk' ∧
        let protector := adding_protector rk c in
        ∃ b : bool, grant stk old
                   (mkItem (if b then SharedReadOnly else SharedReadWrite)
                            new protector) cids = Some stk')
  (* If is both raw ptr and Raw retagging, no protector *)
  | RawPtr Mutable, RawRt =>
      (∀ i, (i < tsize T)%nat → ∃ stk stk',
        α !! (l +ₗ i) = Some stk ∧
        α' !! (l +ₗ i) = Some stk' ∧
        grant stk old (mkItem SharedReadWrite new None) cids = Some stk')
  | RawPtr Immutable, RawRt =>
      (∀ i, (i < tsize T)%nat → ∃ stk stk',
        α !! (l +ₗ i) = Some stk ∧
        α' !! (l +ₗ i) = Some stk' ∧
        ∃ b : bool, grant stk old
                 (mkItem (if b then SharedReadOnly else SharedReadWrite)
                          new None) cids = Some stk')
  (* Box pointer, no protector *)
  | BoxPtr, _ =>
      (∀ i, (i < tsize T)%nat → ∃ stk stk',
        α !! (l +ₗ i) = Some stk ∧
        α' !! (l +ₗ i) = Some stk' ∧
        grant stk old (mkItem Unique new None) cids = Some stk')
  (* Ignore Raw pointer otherwise *)
  | RawPtr _, _ => α' = α ∧ nxtp' = nxtp ∧ new = old
  end.
Proof.
  rewrite /retag. destruct (tsize T) as [|n] eqn:ST.
  { rewrite /retag_ref ST /=.
    destruct pk as [[]|[]|]; [| |destruct rk|destruct rk|]; intros; simplify_eq;
      (split; [done| intros; try done; lia]). }
  rewrite -ST.
  destruct pk as [[]|[]|]; [destruct rk| |destruct rk|destruct rk|];
    try apply retag_ref_Some;
    intros; by simplify_eq.
Qed.

Lemma retag_Some_dom α nxtp c cids l old rk pk T new α' nxtp'
  (RK: match pk with | RawPtr _ => rk = RawRt | _ => True end) :
  retag α nxtp cids c l old rk pk T = Some (new, α', nxtp') →
  ∀ i, (i < tsize T)%nat → (l +ₗ i) ∈ dom α.
Proof.
  intros RT i Lti. rewrite elem_of_dom.
  destruct (retag_Some _ _ _ _ _ _ _ _ _ _ _ _ RT) as [_ EQ].
  destruct pk as [[]|[]|]; [| |subst rk..|];
    specialize (EQ _ Lti) as (?&?&?&_); by eexists.
Qed.

Lemma retag_Some_Ref α nxtp c cids l old rk T mut new α' nxtp'
  (NZST: (0 < tsize T)%nat)
  (FRZ: if mut is Immutable then is_freeze T else True)
  (N2P: rk ≠ TwoPhase) :
  retag α nxtp cids c l old rk (RefPtr mut) T = Some (new, α', nxtp') →
  (∀ i, (i < tsize T)%nat → ∃ stk stk',
        α !! (l +ₗ i) = Some stk ∧
        α' !! (l +ₗ i) = Some stk' ∧
        let protector := adding_protector rk c in
        let pm := if mut is Immutable then SharedReadOnly else Unique in
        grant stk old (mkItem pm new protector) cids = Some stk').
Proof.
  assert (∃ n, tsize T = S n) as [n EqT].
  { destruct (tsize T); [lia|by eexists]. }
  rewrite /retag /retag_ref EqT /=; destruct mut; rewrite -EqT.
  - rewrite (_: is_two_phase rk = false); [|by destruct rk].
    case reborrow as [α1|] eqn:RB; [|done]. simpl. intros ?. simplify_eq.
    by apply reborrowN_lookup_case.
  - case reborrow as [α1|] eqn:RB; [|done]. simpl. intros ?. simplify_eq.
    move : RB => /=. rewrite visit_freeze_sensitive_is_freeze; [|done].
    apply reborrowN_lookup_case.
Qed.

Lemma grant_access1 stk old new cids stk' :
  new.(perm) ≠ SharedReadWrite →
  grant stk old new cids = Some stk' →
  let kind := if grants new.(perm) AccessWrite then AccessWrite else AccessRead in
  is_Some (access1 stk kind old cids).
Proof.
  intros NSRW. rewrite /grant.
  case find_granting as [[]|]; [|done].
  simpl. destruct new.(perm); [|done|..];
    (case access1; [by eexists|done]).
Qed.

Lemma grant_singleton_eq (it it': item) old cids stk' :
  grant [it] old it' cids = Some stk' →
  old = it.(tg).
Proof.
  rewrite /grant. case find_granting as [[n p]|] eqn:GR; [simpl|done].
  intros _.
  apply fmap_Some in GR as [[i it1] [FIND ?]]. simplify_eq.
  move : FIND. simpl. case decide => [MT|//]. intros. simplify_eq.
  by destruct MT.
Qed.

Lemma retag_Some_local α nxtp c cids l old rk pk T new α' nxtp' :
  retag α nxtp cids c l old rk pk T = Some (new, α', nxtp') →
  ∀ l' t',
    old ≠ (Tagged t') →
    α !! l' = Some (init_stack (Tagged t')) →
    α' !! l' = Some (init_stack (Tagged t')).
Proof.
  intros RT l' t' NEQt Eqstk.
  destruct (retag_Some _ _ _ _ _ _ _ _ _ _ _ _ RT) as [NEQ EQ].
  destruct (block_case l l' (tsize T)) as [?|(i & Lti & ?)].
  { by rewrite NEQ. }
  subst l'.
  destruct pk as [[]|[]|].
  - exfalso. specialize (EQ _ Lti) as (stk & stk' & Eq1 & _ & GR).
    rewrite Eqstk in Eq1. simplify_eq. by apply grant_singleton_eq in GR.
  - exfalso. specialize (EQ _ Lti) as (stk & stk' & Eq1 & _ & b & GR).
    rewrite Eqstk in Eq1. simplify_eq. by apply grant_singleton_eq in GR.
  - destruct rk; try (destruct EQ; by subst α').
    exfalso. specialize (EQ _ Lti) as (stk & stk' & Eq1 & _ & GR).
    rewrite Eqstk in Eq1. simplify_eq. by apply grant_singleton_eq in GR.
  - destruct rk; try (destruct EQ; by subst α').
    exfalso. specialize (EQ _ Lti) as (stk & stk' & Eq1 & _ & b & GR).
    rewrite Eqstk in Eq1. simplify_eq. by apply grant_singleton_eq in GR.
  - exfalso. specialize (EQ _ Lti) as (stk & stk' & Eq1 & _ & GR).
    rewrite Eqstk in Eq1. simplify_eq. by apply grant_singleton_eq in GR.
Qed.

Lemma grant_in_SRW stk old it cids stk' it0
  (SRW: it.(perm) = SharedReadWrite) (NEQ: it ≠ it0) :
  grant stk old it cids = Some stk' →
  it0 ∈ stk' → it0 ∈ stk.
Proof.
  rewrite /grant. case find_granting as [[n p]|] eqn:FR; [|done].
  rewrite /= SRW.
  case find_first_write_incompatible as [n'|] eqn:FI; [|done].
  rewrite /= => ?. simplify_eq.
  move => /item_insert_dedup_subseteq /elem_of_cons [//|//].
Qed.

Lemma grant_in_non_SRW stk old it cids stk' it0
  (SRW: it.(perm) ≠ SharedReadWrite) (NEQ: it ≠ it0)
  (ND: it0.(perm) ≠ Disabled) :
  grant stk old it cids = Some stk' →
  it0 ∈ stk' → it0 ∈ stk.
Proof.
  rewrite /grant. case find_granting as [[n p]|] eqn:FR; [|done].
  case it.(perm) eqn:Eqp; [|done|..];
    cbn -[item_insert_dedup];
    (case access1 as [[n' stk1]|] eqn:ACC; [|done]);
    cbn -[item_insert_dedup];
    intros ?; simplify_eq;
    (move => /item_insert_dedup_subseteq /elem_of_cons [//|//]);
    intros IN;
    apply access1_tagged_sublist in ACC;
    specialize (ACC _ IN) as (it2 & IN2 & HT & HPR & HP); specialize (HP ND).
    - have ?: it2 = it0. { destruct it2, it0; simpl in *; by subst. }
      by subst it2.
    - have ?: it2 = it0. { destruct it2, it0; simpl in *; by subst. }
      by subst it2.
    - have ?: it2 = it0. { destruct it2, it0; simpl in *; by subst. }
      by subst it2.
Qed.

Lemma grant_in_preserve stk old it cids stk' it0
  (NEQ: it ≠ it0) (ND: it0.(perm) ≠ Disabled) :
  grant stk old it cids = Some stk' →
  it0 ∈ stk' → it0 ∈ stk.
Proof.
  case (decide (it.(perm) = SharedReadWrite)) => ?.
  - by apply grant_in_SRW.
  - by apply grant_in_non_SRW.
Qed.

Lemma retag_item_in α nxtp c cids l old rk pk T new α' nxtp' :
  retag α nxtp cids c l old rk pk T = Some (new, α', nxtp') →
  ∀ l' stk' t' it',
    α' !! l' = Some stk' →
    it' ∈ stk' → it'.(tg) = Tagged t' → it'.(perm) ≠ Disabled →
    (t' < nxtp)%nat →
    ∃ stk, α !! l' = Some stk ∧ it' ∈ stk.
Proof.
  intros RT l' stk' t' it' Eqstk' In' Eqt' ND' Lt'.
  destruct (retag_Some _ _ _ _ _ _ _ _ _ _ _ _ RT) as [NEQ EQ].
  destruct (block_case l l' (tsize T)) as [?|(i & Lti & ?)].
  { rewrite NEQ // in Eqstk'. naive_solver. }
  assert (∃ sz, tsize T = S sz) as [sz Eqsz].
  { destruct (tsize T); [lia|by eexists]. }
  subst l'.
  move : RT. rewrite /retag /= /retag_ref Eqsz.
  destruct pk as [[]|[]|].
  - specialize (EQ _ Lti) as (stk1 & stk2 & Eq1 & Eq2 & GR). simplify_eq.
    case reborrow as [α1|]; [|done]. simpl. intros. simplify_eq.
    exists stk1. split; [done|].
    move : GR In'.
    apply grant_in_preserve; [|done].
    intros ?; subst it'. simpl in Eqt'. simplify_eq. lia.
  - specialize (EQ _ Lti) as (stk1 & stk2 & Eq1 & Eq2 & b & GR). simplify_eq.
    case reborrow as [α1|]; [|done]. simpl. intros. simplify_eq.
    exists stk1. split; [done|].
    move : GR In'.
    apply grant_in_preserve; [|done].
    intros ?; subst it'. simpl in Eqt'. simplify_eq. lia.
  - destruct rk; [by intros; simplify_eq; naive_solver..|
                  |intros; simplify_eq; naive_solver].
    specialize (EQ _ Lti) as (stk1 & stk2 & Eq1 & Eq2 & GR). simplify_eq.
    case reborrow as [α1|]; [|done]. simpl. intros. simplify_eq.
    exists stk1. split; [done|].
    move : GR In'. apply grant_in_SRW; [done|intros ?; by subst it'].
  - destruct rk; [by intros; simplify_eq; naive_solver..|
                  |intros; simplify_eq; naive_solver].
    specialize (EQ _ Lti) as (stk1 & stk2 & Eq1 & Eq2 & b & GR). simplify_eq.
    case reborrow as [α1|]; [|done]. simpl. intros. simplify_eq.
    exists stk1. split; [done|].
    move : GR In'. apply grant_in_preserve; [intros ?; by subst it'|done].
  - specialize (EQ _ Lti) as (stk1 & stk2 & Eq1 & Eq2 & GR). simplify_eq.
    case reborrow as [α1|]; [|done]. simpl. intros. simplify_eq.
    exists stk1. split; [done|].
    move : GR In'.
    apply grant_in_preserve; [|done].
    intros ?; subst it'. simpl in Eqt'. simplify_eq. lia.
Qed.

(* Lemma item_insert_dedup_lookup stk it i (IS: is_Some (stk !! i)):
  ∃ j, (item_insert_dedup stk it i) !! j = Some it ∧
    (j = i ∨ (1 ≤ i ∧ j = i - 1)%nat) ∧
    (∀ j', (j' < j)%nat → (item_insert_dedup stk it i) !! j' = stk !! j').
Proof.
  destruct i as [|i]; simpl.
  - destruct stk as [|it' stk']; [by destruct IS|]. case decide => [->|?].
    + exists O. naive_solver.
    + exists O. split; [done|]. split;[by left| intros; lia].
  - destruct IS as [it1 Eq1]. rewrite Eq1.
    destruct (stk !! i) as [it2|] eqn:Eq2; last first.
    { apply lookup_ge_None_1 in Eq2. apply lookup_lt_Some in Eq1. lia. }
    case decide => [->|?]; [|case decide => [->|?]].
    + exists i. split; [done|]. rewrite Nat.sub_0_r. split; [right; lia|done].
    + exists (S i). split; [done|]. split; [by left|done].
    + exists (S i). rewrite Nat.sub_0_r. split; last split; [|by left|].
      * rewrite list_lookup_middle // length_take_le //.
        by eapply Nat.lt_le_incl, lookup_lt_Some.
      * intros j' Lt'. rewrite lookup_app_l; [apply lookup_take_lt; lia|].
        rewrite length_take_le //. by eapply Nat.lt_le_incl, lookup_lt_Some.
Qed. *)

Lemma find_granting_Some stk kind bor i pi :
  find_granting stk kind bor = Some (i, pi) →
  is_Some (stk !! i) ∧
  ∀ j jt, (j < i)%nat → stk !! j = Some jt →
  ¬ (grants jt.(perm) kind ∧ jt.(tg) = bor).
Proof.
  move => /fmap_Some [[i' pi'] [/list_find_Some_not_earlier [Eq1 [MG LT]] Eq2]].
  simplify_eq. simpl. split; [by eexists|by apply LT].
Qed.

Lemma item_insert_dedup_new stk new i (NIN: new ∉ stk) (IS: is_Some (stk !! i)):
  item_insert_dedup stk new i = take i stk ++ new :: drop i stk.
Proof.
  destruct i as [|i]; simpl.
  - destruct stk as [|it stk]; [done|]. rewrite decide_False //.
    intros ?. subst. apply NIN. by left.
  - destruct IS as [its Eqs]. rewrite Eqs.
    destruct (stk !! i) as [it|] eqn:Eq; last first.
    { apply lookup_ge_None_1 in Eq. apply lookup_lt_Some in Eqs. lia. }
    rewrite decide_False; last first.
    { intros ?. subst. by eapply NIN, list_elem_of_lookup_2. }
    rewrite decide_False //.
    intros ?. subst. by eapply NIN, list_elem_of_lookup_2.
Qed.

Lemma item_insert_dedup_case stk new i :
   item_insert_dedup stk new i = take i stk ++ new :: drop i stk ∨
   item_insert_dedup stk new i = stk.
Proof.
  (* intros [it Eqit]. *) destruct i as [|i]; simpl.
  - destruct stk; simpl; [by left|].
    case decide =>?; [subst new|]; [by right|by left].
  - destruct (stk !! S i) eqn: Eqit.
    + have Lt := lookup_lt_Some _ _ _ Eqit.
      destruct (lookup_lt_is_Some_2 stk i) as [it' Eqit']; [lia|].
      rewrite Eqit'.
      case decide => ?; [subst new|]; [by right|].
      case decide => ?; [subst new|]; [by right|by left].
    + destruct (stk !! i) eqn: Eqit'; [|by left].
      case decide => ?; [subst new|]; [by right|by left].
Qed.

Lemma find_first_write_incompatible_le stk p n :
  find_first_write_incompatible stk p = Some n →
  (n ≤ length stk)%nat.
Proof.
  destruct p; simpl; [by intros; simplify_eq| |done..].
  case list_find as [[]|]; intros; simplify_eq; lia.
Qed.

Lemma find_granting_lt stk kind t n p :
  find_granting stk kind t = Some (n, p) →
  (n < length stk)%nat.
Proof.
  intros [[n1 p1] [[Eq%lookup_lt_Some MG]%list_find_Some ?]]%fmap_Some.
  by simplify_eq.
Qed.

Lemma grant_active_SRO_SRW stk old it cids stk' t
  (SRW: it.(perm) = SharedReadWrite):
  grant stk old it cids = Some stk' →
  t ∈ active_SRO stk → t ∈ active_SRO stk'.
Proof.
  rewrite /grant. case find_granting as [[n p]|] eqn:FR; [|done].
  rewrite /= SRW.
  case find_first_write_incompatible as [n'|] eqn:FI; [|done].
  rewrite /= => ?. simplify_eq.
  destruct (item_insert_dedup_case stk it n') as [EQ|EQ]; rewrite EQ; [|done].
  rewrite SRW /= in FR. intros IN.
  have IN' := find_granting_incompatible_active_SRO _ _ _ _ _ IN FR.
  have IN2 := find_first_write_incompatible_active_SRO _ _ _ FI.
  have Ltn := find_granting_lt _ _ _ _ _ FR.
  destruct (IN2 _ IN') as (j & jt & Eqjt & Eqp & Eqt & Lt' & HL).
  have Eqln: length (take n stk) = n by apply length_take_le; lia.
  have Len' := find_first_write_incompatible_le _ _ _ FI. rewrite Eqln in Len'.
  have Eqjt' : stk !! j = Some jt.
  { rewrite lookup_take_lt // in Eqjt. lia. }
  apply (active_SRO_elem_of_inv j jt t); [|done|done|].
  - rewrite lookup_app_l; [by rewrite lookup_take_lt|].
    rewrite length_take_le //. lia.
  - intros k kt Ltk.
    rewrite lookup_app_l; last by (rewrite length_take_le; lia).
    intros Eqkt. apply (HL _ _ Ltk).
    rewrite lookup_take_lt; [|lia].
    rewrite lookup_take_lt in Eqkt; [done|lia].
Qed.

Lemma grant_active_SRO_non_SRW stk old it cids stk' t pm opro
  (ND: stack_item_tagged_NoDup stk)
  (SRW: it.(perm) ≠ SharedReadWrite) (NDIS: it.(perm) ≠ Disabled)
  (IN': mkItem pm (Tagged t) opro ∈ stk')
  (NEqt: it.(tg) ≠ Tagged t) :
  grant stk old it cids = Some stk' →
  t ∈ active_SRO stk → t ∈ active_SRO stk'.
Proof.
  rewrite /grant. case find_granting as [[n p]|] eqn:FR; [|done].
  case it.(perm) eqn:Eqp; [|done|..|done];
    cbn -[item_insert_dedup];
    (case access1 as [[n' stk1]|] eqn:ACC; [|done]);
    cbn -[item_insert_dedup];
    intros ?; simplify_eq.
  - intros Int. exfalso.
    apply (access1_write_remove_incompatible_active_SRO _ _ _ _ _ _ ND
            Int ACC pm opro).
    move : IN' => /item_insert_dedup_subseteq /elem_of_cons [|//].
    intros. by subst it.
  - intros Int.
    have IN'2: mkItem pm (Tagged t) opro ∈ stk1.
    { move : IN' => /item_insert_dedup_subseteq /elem_of_cons [|//].
      intros. by subst it. }
    have IN2:= access1_active_SRO_preserving _ _ _ _ _ _ _ _ _ ND IN'2 ACC Int.
    destruct (item_insert_dedup_case stk1 it 0) as [EQ|EQ]; rewrite EQ //.
    apply active_SRO_cons_elem_of. split; [done|by right].
Qed.

Lemma grant_active_SRO_preserving stk old it cids stk' t pm opro
  (ND: stack_item_tagged_NoDup stk)
  (NDIS: it.(perm) ≠ Disabled)
  (IN': mkItem pm (Tagged t) opro ∈ stk')
  (NEqt: it.(tg) ≠ Tagged t) :
  grant stk old it cids = Some stk' →
  t ∈ active_SRO stk → t ∈ active_SRO stk'.
Proof.
  case (decide (it.(perm) = SharedReadWrite)) => ?.
  - by apply grant_active_SRO_SRW.
  - by eapply grant_active_SRO_non_SRW.
Qed.

Lemma retag_item_active_SRO_preserving α nxtp c cids l old rk pk T new α' nxtp' :
  retag α nxtp cids c l old rk pk T = Some (new, α', nxtp') →
  ∀ l' t' stk stk' it',
    stack_item_tagged_NoDup stk →
    α !! l' = Some stk →
    α' !! l' = Some stk' →
    it' ∈ stk → it' ∈ stk' →
    it'.(tg) = Tagged t' → it'.(perm) ≠ Disabled →
    (t' < nxtp)%nat →
    t' ∈ active_SRO stk → t' ∈ active_SRO stk'.
Proof.
  intros RT l' t' stk stk' it' ND Eqstk Eqstk' In In' Eqt' ND' Lt'.
  destruct (retag_Some _ _ _ _ _ _ _ _ _ _ _ _ RT) as [NEQ EQ].
  destruct (block_case l l' (tsize T)) as [?|(i & Lti & ?)].
  { rewrite NEQ // in Eqstk'. naive_solver. }
  assert (∃ sz, tsize T = S sz) as [sz Eqsz].
  { destruct (tsize T); [lia|by eexists]. }
  subst l'.
  have ?: Tagged nxtp ≠ Tagged t' by intros ?; simplify_eq; lia.
  have ?: mkItem it'.(perm) (Tagged t') it'.(protector) ∈ stk'.
  { rewrite -Eqt'. by destruct it'. }
  move : RT. rewrite /retag /= /retag_ref Eqsz.
  destruct pk as [[]|[]|].
  - specialize (EQ _ Lti) as (stk1 & stk2 & Eq1 & Eq2 & GR).
    simplify_eq.
    case reborrow as [α1|]; [|done]. simpl. intros ?. simplify_eq.
    move : GR.
    apply (grant_active_SRO_preserving _ _ _ _ _ _ it'.(perm) it'.(protector) ND);
      [|done..].
    simpl. by case is_two_phase.
  - specialize (EQ _ Lti) as (stk1 & stk2 & Eq1 & Eq2 & b & GR).
    simplify_eq.
    case reborrow as [α1|]; [|done]. simpl. intros ?. simplify_eq.
    move : GR.
    apply (grant_active_SRO_preserving _ _ _ _ _ _ it'.(perm) it'.(protector) ND);
      [|done..].
    simpl. by destruct b.
  - destruct rk; [by intros; simplify_eq; naive_solver..|
                  |intros; simplify_eq; naive_solver].
    specialize (EQ _ Lti) as (stk1 & stk2 & Eq1 & Eq2 & GR). simplify_eq.
    case reborrow as [α1|]; [|done]. simpl. intros ?. simplify_eq.
    move : GR.
    by apply (grant_active_SRO_preserving _ _ _ _ _ _ it'.(perm) it'.(protector) ND).
  - destruct rk; [by intros; simplify_eq; naive_solver..|
                  |intros; simplify_eq; naive_solver].
    specialize (EQ _ Lti) as (stk1 & stk2 & Eq1 & Eq2 & b & GR). simplify_eq.
    case reborrow as [α1|]; [|done]. simpl. intros ?. simplify_eq.
    move : GR.
    apply (grant_active_SRO_preserving _ _ _ _ _ _ it'.(perm) it'.(protector) ND);
      [|done..].
    simpl. by destruct b.
  - specialize (EQ _ Lti) as (stk1 & stk2 & Eq1 & Eq2 & GR). simplify_eq.
    case reborrow as [α1|]; [|done]. simpl. intros ?. simplify_eq.
    move : GR.
    by apply (grant_active_SRO_preserving _ _ _ _ _ _ it'.(perm) it'.(protector) ND).
Qed.

Lemma is_stack_head_app_l it stk1 stk2 (NN: stk1 ≠ []) :
  is_stack_head it (stk1 ++ stk2) ↔ is_stack_head it stk1.
Proof.
  destruct stk1 as [|i stk1]; [done|].
  split; intros [? Eq]; inversion Eq; simplify_eq; by eexists.
Qed.

Lemma grant_head_SRW stk old it cids stk' t pro
  (SRW: it.(perm) = SharedReadWrite) (NEQ: Tagged t ≠ old) :
  grant stk old it cids = Some stk' →
  let it' := (mkItem Unique (Tagged t) pro) in
  is_stack_head it' stk → is_stack_head it' stk'.
Proof.
  rewrite /grant. case find_granting as [[n p]|] eqn:FR; [|done].
  rewrite /= SRW.
  case find_first_write_incompatible as [n'|] eqn:FI; [|done].
  rewrite /= => ?. simplify_eq.
  destruct (item_insert_dedup_case stk it n') as [EQ|EQ]; rewrite EQ; [|done].
  rewrite SRW /= in FR. intros IN.
  have IN' := find_granting_incompatible_head _ _ _ _ _ _ _ _ IN NEQ FR.
  have IN2 := find_first_write_incompatible_head _ _ _ _ _ _ IN' ltac:(done) FI.
  have Ltn := find_granting_lt _ _ _ _ _ FR.
  have Eqln: length (take n stk) = n by apply length_take_le; lia.
  have Len' := find_first_write_incompatible_le _ _ _ FI. rewrite Eqln in Len'.
  have ?: take n' stk ≠ [].
  { destruct stk; [simpl in Ltn; lia|]. destruct n'; [lia|done]. }
  move : IN. rewrite -{1}(take_drop n' stk).
  by do 2 rewrite is_stack_head_app_l //.
Qed.

Lemma grant_head_non_SRW stk old it cids stk' t pro
  (SRW: it.(perm) ≠ SharedReadWrite) (NDIS: it.(perm) ≠ Disabled)
  (NEQ: Tagged t ≠ old)
  (ND: stack_item_tagged_NoDup stk)
  (NEqt: it.(tg) ≠ Tagged t) :
  let it' := (mkItem Unique (Tagged t) pro) in
  it' ∈ stk' →
  grant stk old it cids = Some stk' →
  is_stack_head it' stk → is_stack_head it' stk'.
Proof.
  intros it' IN'.
  rewrite /grant. case find_granting as [[n p]|] eqn:FR; [|done].
  case it.(perm) eqn:Eqp; [|done|..|done];
    cbn -[item_insert_dedup];
    (case access1 as [[n' stk1]|] eqn:ACC; [|done]);
    cbn -[item_insert_dedup];
    intros ?; simplify_eq.
  - intros Int.
    have Int': ∃ pro, is_stack_head (mkItem Unique (Tagged t) pro) stk
      by eexists.
    exfalso.
    apply (access1_write_remove_incompatible_head _ _ _ _ _ _
            ND Int' ACC NEQ Unique pro).
    move : IN' => /item_insert_dedup_subseteq /elem_of_cons [|//].
    intros. by subst it.
  - intros Int.
    have IN'2: mkItem Unique (Tagged t) pro ∈ stk1.
    { move : IN' => /item_insert_dedup_subseteq /elem_of_cons [|//].
      intros. by subst it. }
    have Int': ∃ pro, is_stack_head (mkItem Unique (Tagged t) pro) stk
      by eexists.
    exfalso.
    have IN2 := (access1_read_replace_incompatible_head _ _ _ _ _ _
                  ND Int' ACC NEQ Unique pro IN'2).
    done.
Qed.

Lemma grant_head_preserving stk old it cids stk' t pro
  (NDIS: it.(perm) ≠ Disabled)
  (NEQ: Tagged t ≠ old)
  (ND: stack_item_tagged_NoDup stk)
  (NEqt: it.(tg) ≠ Tagged t) :
  let it' := (mkItem Unique (Tagged t) pro) in
  it' ∈ stk' →
  grant stk old it cids = Some stk' →
  is_stack_head it' stk → is_stack_head it' stk'.
Proof.
  intros it' IN'.
  case (decide (it.(perm) = SharedReadWrite)) => ?.
  - by apply grant_head_SRW.
  - by eapply grant_head_non_SRW.
Qed.

Lemma retag_item_head_preserving α nxtp c cids l old rk pk T new α' nxtp' :
  retag α nxtp cids c l old rk pk T = Some (new, α', nxtp') →
  ∀ l' t' stk stk' pro,
    stack_item_tagged_NoDup stk →
    α !! l' = Some stk →
    α' !! l' = Some stk' →
    Tagged t' ≠ old →
    let it' := (mkItem Unique (Tagged t') pro) in
    it' ∈ stk' →
    (t' < nxtp)%nat →
    is_stack_head it' stk → is_stack_head it' stk'.
Proof.
  intros RT l' t' stk stk' pro ND Eqstk Eqstk' NEqt it' In' Lt'.
  destruct (retag_Some _ _ _ _ _ _ _ _ _ _ _ _ RT) as [NEQ EQ].
  destruct (block_case l l' (tsize T)) as [?|(i & Lti & ?)].
  { rewrite NEQ // in Eqstk'. naive_solver. }
  assert (∃ sz, tsize T = S sz) as [sz Eqsz].
  { destruct (tsize T); [lia|by eexists]. }
  subst l'.
  have ?: Tagged nxtp ≠ Tagged t' by intros ?; simplify_eq; lia.
  move : RT. rewrite /retag /= /retag_ref Eqsz.
  destruct pk as [[]|[]|].
  - specialize (EQ _ Lti) as (stk1 & stk2 & Eq1 & Eq2 & GR).
    simplify_eq.
    case reborrow as [α1|]; [|done]. simpl. intros ?. simplify_eq.
    move : GR. eapply grant_head_preserving; eauto.
    simpl. by case is_two_phase.
  - specialize (EQ _ Lti) as (stk1 & stk2 & Eq1 & Eq2 & b & GR).
    simplify_eq.
    case reborrow as [α1|]; [|done]. simpl. intros ?. simplify_eq.
    move : GR. eapply grant_head_preserving; eauto.
    simpl. by destruct b.
  - destruct rk; [by intros; simplify_eq; naive_solver..|
                  |intros; simplify_eq; naive_solver].
    specialize (EQ _ Lti) as (stk1 & stk2 & Eq1 & Eq2 & GR). simplify_eq.
    case reborrow as [α1|]; [|done]. simpl. intros ?. simplify_eq.
    move : GR. eapply grant_head_preserving; eauto.
  - destruct rk; [by intros; simplify_eq; naive_solver..|
                  |intros; simplify_eq; naive_solver].
    specialize (EQ _ Lti) as (stk1 & stk2 & Eq1 & Eq2 & b & GR). simplify_eq.
    case reborrow as [α1|]; [|done]. simpl. intros ?. simplify_eq.
    move : GR. eapply grant_head_preserving; eauto.
    simpl. by destruct b.
  - specialize (EQ _ Lti) as (stk1 & stk2 & Eq1 & Eq2 & GR). simplify_eq.
    case reborrow as [α1|]; [|done]. simpl. intros ?. simplify_eq.
    move : GR. eapply grant_head_preserving; eauto.
Qed.

Lemma grant_active_SRW stk old it cids stk' it'
  (SRW: it.(perm) = SharedReadWrite) :
  grant stk old it cids = Some stk' →
  it' ∈ stk → it' ∈ stk'.
Proof.
  rewrite /grant. case find_granting as [[n p]|]; [|done].
  rewrite /= SRW.
  case find_first_write_incompatible as [n'|]; [|done].
  rewrite /= => ?. simplify_eq.
  destruct (item_insert_dedup_case stk it n') as [EQ|EQ]; rewrite EQ; [|done].
  rewrite -{1}(take_drop n' stk). set_solver.
Qed.

Lemma grant_active_non_SRW stk old it cids stk' t pm c
  (SRW: it.(perm) ≠ SharedReadWrite)
  (Inc: c ∈ cids) :
  grant stk old it cids = Some stk' →
  let it' := mkItem pm t (Some c) in
  it' ∈ stk → it' ∈ stk'.
Proof.
  rewrite /grant. case find_granting as [[n p]|] eqn:FR; [|done].
  case it.(perm) eqn:Eqp; [|done|..|];
    cbn -[item_insert_dedup];
    (case access1 as [[n' stk1]|] eqn:ACC; [|done]);
    cbn -[item_insert_dedup];
    intros ?; simplify_eq;
    move => /(access1_active_preserving _ _ _ _ _ _ ACC _ _ _ Inc);
    (destruct (item_insert_dedup_case stk1 it O) as [EQ|EQ]; rewrite EQ; [|done]);
    rewrite -{1}(take_drop 0 stk1); set_solver.
Qed.

Lemma grant_active_preserving stk old it cids stk' t pm c (Inc: c ∈ cids) :
  grant stk old it cids = Some stk' →
  let it' := mkItem pm t (Some c) in
  it' ∈ stk → it' ∈ stk'.
Proof.
  case (decide (it.(perm) = SharedReadWrite)) => ?.
  - by apply grant_active_SRW.
  - by eapply grant_active_non_SRW.
Qed.

Lemma retag_item_active_preserving α nxtp c cids l old rk pk T new α' nxtp' :
  retag α nxtp cids c l old rk pk T = Some (new, α', nxtp') →
  ∀ l' stk t' c' pm,
    α !! l' = Some stk →
    c' ∈ cids →
    let it' := mkItem pm t' (Some c') in
    it' ∈ stk →
    ∃ stk', α' !! l' = Some stk' ∧ it' ∈ stk'.
Proof.
  intros RT l' stk t' c' pm Eqstk Inc' it' IN.
  destruct (retag_Some _ _ _ _ _ _ _ _ _ _ _ _ RT) as [NEQ EQ].
  destruct (block_case l l' (tsize T)) as [?|(i & Lti & ?)].
  { rewrite NEQ //. naive_solver. }
  assert (∃ sz, tsize T = S sz) as [sz Eqsz].
  { destruct (tsize T); [lia|by eexists]. }
  subst l'.
  move : RT. rewrite /retag /= /retag_ref Eqsz.
  destruct pk as [[]|[]|].
  - specialize (EQ _ Lti) as (stk1 & stk2 & Eq1 & Eq2 & GR).
    simplify_eq.
    case reborrow as [α1|]; [|done]. simpl. intros ?. simplify_eq.
    exists stk2. split; [done|].
    move : Inc' GR IN. by apply grant_active_preserving.
  - specialize (EQ _ Lti) as (stk1 & stk2 & Eq1 & Eq2 & b & GR).
    simplify_eq.
    case reborrow as [α1|]; [|done]. simpl. intros ?. simplify_eq.
    exists stk2. split; [done|].
    move : Inc' GR IN. by apply grant_active_preserving.
  - destruct rk; [by intros; simplify_eq; naive_solver..|
                  |intros; simplify_eq; naive_solver].
    specialize (EQ _ Lti) as (stk1 & stk2 & Eq1 & Eq2 & GR). simplify_eq.
    case reborrow as [α1|]; [|done]. simpl. intros ?. simplify_eq.
    exists stk2. split; [done|].
    move : Inc' GR IN. by apply grant_active_preserving.
  - destruct rk; [by intros; simplify_eq; naive_solver..|
                  |intros; simplify_eq; naive_solver].
    specialize (EQ _ Lti) as (stk1 & stk2 & Eq1 & Eq2 & b & GR). simplify_eq.
    case reborrow as [α1|]; [|done]. simpl. intros ?. simplify_eq.
    exists stk2. split; [done|].
    move : Inc' GR IN. by apply grant_active_preserving.
  - specialize (EQ _ Lti) as (stk1 & stk2 & Eq1 & Eq2 & GR). simplify_eq.
    case reborrow as [α1|]; [|done]. simpl. intros ?. simplify_eq.
    exists stk2. split; [done|].
    move : Inc' GR IN. by apply grant_active_preserving.
Qed.

Lemma item_insert_dedup_new_elem_of stk new n :
  new ∈ item_insert_dedup stk new n.
Proof.
  destruct n as [|n]; simpl.
  - destruct stk; simpl.
    + set_solver.
    + case decide => ?; [subst; set_solver|set_solver].
  - case (lookup n) as [?|] eqn:Eq1; case (lookup (S n)) as [?|] eqn:Eq2;
      [..|set_solver];
      (case decide => ?; [subst|]).
    + by eapply list_elem_of_lookup_2.
    + case decide => ?; [subst|set_solver].
      by eapply list_elem_of_lookup_2.
    + by eapply list_elem_of_lookup_2.
    + set_solver.
    + by eapply list_elem_of_lookup_2.
    + set_solver.
Qed.

Lemma grant_elem_of_SRW stk old new cids stk'
  (SRW: new.(perm) = SharedReadWrite) :
  grant stk old new cids = Some stk' → new ∈ stk'.
Proof.
  rewrite /grant. case find_granting as [[n1 p1]|]; [|done].
  rewrite SRW. cbn -[item_insert_dedup].
  case find_first_write_incompatible as [n2|]; [|done].
  cbn -[item_insert_dedup]. intros. simplify_eq.
  by apply item_insert_dedup_new_elem_of.
Qed.

Lemma grant_elem_of_non_SRW stk old new cids stk'
  (SRW: new.(perm) ≠ SharedReadWrite) :
  grant stk old new cids = Some stk' → new ∈ stk'.
Proof.
  rewrite /grant. case find_granting as [[n1 p1]|]; [|done].
  cbn -[item_insert_dedup].
  destruct new.(perm); [|done|..];
    (case access1 as [[n2 stk2]|]; [|done]);
    cbn -[item_insert_dedup]; intros; simplify_eq;
    by apply item_insert_dedup_new_elem_of.
Qed.

Lemma grant_elem_of stk old new cids stk' :
  grant stk old new cids = Some stk' → new ∈ stk'.
Proof.
  case (decide (new.(perm) = SharedReadWrite)) => ?.
  - by apply grant_elem_of_SRW.
  - by apply grant_elem_of_non_SRW.
Qed.

Lemma retag_fn_entry_item_active α nxtp c cids l old mut T new α' nxtp' :
  retag α nxtp cids c l old FnEntry (RefPtr mut) T = Some (new, α', nxtp') →
  ∀ i, (i < tsize T)%nat → ∃ stk' pm, α' !! (l +ₗ i) = Some stk' ∧
    mkItem pm new (Some c) ∈ stk' ∧ pm ≠ Disabled.
Proof.
  intros RT i Lti.
  destruct (retag_Some _ _ _ _ _ _ _ _ _ _ _ _ RT) as [_ EQ].
  assert (∃ sz, tsize T = S sz) as [sz Eqsz].
  { destruct (tsize T); [lia|by eexists]. }
  move : RT. rewrite /retag /= /retag_ref Eqsz.
  destruct mut.
  - specialize (EQ _ Lti) as (stk1 & stk2 & Eq1 & Eq2 & GR).
    case reborrow as [α1|]; [|done]. simpl. intros ?. simplify_eq.
    exists stk2, Unique. split; last split; [done| |done].
    move : GR. by apply grant_elem_of.
  - specialize (EQ _ Lti) as (stk1 & stk2 & Eq1 & Eq2 & b & GR).
    case reborrow as [α1|]; [|done]. simpl. intros ?. simplify_eq.
    exists stk2, (if b then SharedReadOnly else SharedReadWrite).
    split; last split; [done| |by destruct b].
    move : GR. by apply grant_elem_of.
Qed.
