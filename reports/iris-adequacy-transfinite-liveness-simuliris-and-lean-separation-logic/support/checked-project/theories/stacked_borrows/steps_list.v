(** This file has been adapted from the Stacked Borrows development, available at 
  https://gitlab.mpi-sws.org/FP/stacked-borrows
*)

From simuliris.stacked_borrows Require Export defs.



Definition tagged_sublist (stk1 stk2: stack) :=
  ∀ it1, it1 ∈ stk1 → ∃ it2,
  it2 ∈ stk2 ∧ it1.(tg) = it2.(tg) ∧ it1.(protector) = it2.(protector) ∧
  (it1.(perm) ≠ Disabled → it2.(perm) = it1.(perm)).
Global Instance tagged_sublist_preorder : PreOrder tagged_sublist.
Proof.
  constructor.
  - intros ??. naive_solver.
  - move => ??? H1 H2 ? /H1 [? [/H2 Eq [-> [-> ND]]]].
    destruct Eq as (it2 &?&?&?&ND2). exists it2. repeat split; auto.
    intros ND3. specialize (ND ND3). rewrite ND2 // ND //.
Qed.

Global Instance tagged_sublist_proper stk : Proper ((⊆) ==> impl) (tagged_sublist stk).
Proof. move => ?? SUB H1 ? /H1 [? [/SUB ? ?]]. naive_solver. Qed.

Lemma tagged_sublist_app l1 l2 k1 k2 :
  tagged_sublist l1 l2 → tagged_sublist k1 k2 →
  tagged_sublist (l1 ++ k1) (l2 ++ k2).
Proof.
  move => H1 H2 it. setoid_rewrite elem_of_app.
  move => [/H1|/H2]; naive_solver.
Qed.

Lemma remove_check_tagged_sublist cids stk stk' idx:
  remove_check cids stk idx = Some stk' → tagged_sublist stk' stk.
Proof.
  revert idx.
  induction stk as [|it stk IH]; intros idx; simpl.
  { destruct idx; [|done]. intros. by simplify_eq. }
  destruct idx as [|idx]; [intros; by simplify_eq|].
  case check_protector eqn:Eq; [|done].
  move => /IH. apply tagged_sublist_proper. set_solver.
Qed.

Lemma replace_check'_tagged_sublist cids acc stk stk':
  replace_check' cids acc stk = Some stk' → tagged_sublist stk' (acc ++ stk).
Proof.
  revert acc.
  induction stk as [|it stk IH]; intros acc; simpl.
  { intros. simplify_eq. by rewrite app_nil_r. }
  case decide => ?; [case check_protector; [|done]|];
    move => /IH; [|by rewrite -app_assoc].
  move => H1 it1 /H1 [it2 [IN2 [Eq1 [Eq2 ND]]]].
  setoid_rewrite elem_of_app. setoid_rewrite elem_of_cons.
  move : IN2 => /elem_of_app [/elem_of_app [?|/list_elem_of_singleton Eq]|?];
    [..|naive_solver].
  - exists it2. naive_solver.
  - subst it2. exists it. naive_solver.
Qed.

Lemma replace_check_tagged_sublist cids stk stk':
  replace_check cids stk = Some stk' → tagged_sublist stk' stk.
Proof. move => /replace_check'_tagged_sublist. by rewrite app_nil_l. Qed.


(** NoDup for tagged item *)
Lemma stack_item_tagged_NoDup_singleton it:
  stack_item_tagged_NoDup [it].
Proof.
  rewrite /stack_item_tagged_NoDup filter_cons filter_nil.
  case decide => ? /=; first by apply NoDup_singleton. apply NoDup_nil_2.
Qed.

Lemma stack_item_tagged_NoDup_cons_1 it stk :
  stack_item_tagged_NoDup (it :: stk) → stack_item_tagged_NoDup stk.
Proof.
  rewrite /stack_item_tagged_NoDup filter_cons.
  case decide => [NT|IT //]. rewrite fmap_cons.  by apply NoDup_cons_1_2.
Qed.

Lemma stack_item_tagged_NoDup_sublist stk1 stk2:
  sublist stk1 stk2 → stack_item_tagged_NoDup stk2 → stack_item_tagged_NoDup stk1.
Proof.
  intros SUB. rewrite /stack_item_tagged_NoDup.
  by apply NoDup_sublist, fmap_sublist, filter_sublist.
Qed.

Lemma replace_check'_stack_item_tagged_NoDup cids acc stk stk':
  replace_check' cids acc stk = Some stk' →
  stack_item_tagged_NoDup (acc ++ stk) → stack_item_tagged_NoDup stk'.
Proof.
  revert acc.
  induction stk as [|it stk IH]; intros acc; simpl.
  { intros ?. simplify_eq. by rewrite app_nil_r. }
  case decide => ?; [case check_protector; [|done]|];
    move => /IH; [|by rewrite -app_assoc].
  move => IH1 ND. apply IH1. clear IH1. move : ND.
  rewrite /stack_item_tagged_NoDup 3!filter_app 2!filter_cons.
  case decide => [IT|NT].
  - by rewrite decide_True // 3!fmap_app 2!fmap_cons /= -assoc.
  - by rewrite decide_False // /= filter_nil app_nil_r.
Qed.

Lemma replace_check'_stack_item_tagged_NoDup_2 cids acc stk stk' stk0:
  replace_check' cids acc stk = Some stk' →
  stack_item_tagged_NoDup (acc ++ stk ++ stk0) → stack_item_tagged_NoDup (stk' ++ stk0).
Proof.
  revert acc.
  induction stk as [|it stk IH]; intros acc; simpl.
  { intros ?. by simplify_eq. }
  case decide => ?; [case check_protector; [|done]|];
    move => /IH; [|rewrite (app_assoc acc [it] (stk ++ stk0)); naive_solver].
  move => IH1 ND. apply IH1. clear IH1. move : ND.
  rewrite /stack_item_tagged_NoDup 3!filter_app 2!filter_cons.
  case decide => [IT|NT].
  - by rewrite decide_True // 3!fmap_app 2!fmap_cons /= -assoc.
  - by rewrite decide_False // /= filter_nil app_nil_r.
Qed.

Lemma replace_check_stack_item_tagged_NoDup cids stk stk' :
  replace_check cids stk = Some stk' →
  stack_item_tagged_NoDup stk → stack_item_tagged_NoDup stk'.
Proof. intros. eapply replace_check'_stack_item_tagged_NoDup; eauto. Qed.

Lemma replace_check_stack_item_tagged_NoDup_2 cids stk stk' stk0:
  replace_check cids stk = Some stk' →
  stack_item_tagged_NoDup (stk ++ stk0) → stack_item_tagged_NoDup (stk' ++ stk0).
Proof. intros; eapply replace_check'_stack_item_tagged_NoDup_2; eauto. Qed.

Lemma replace_check'_acc_result cids acc stk stk' :
  replace_check' cids acc stk = Some stk' → acc ⊆ stk'.
Proof.
  revert acc.
  induction stk as [|it stk IH]; intros acc; simpl; [by intros; simplify_eq|].
  case decide => ?; [case check_protector; [|done]|];
    move => /IH; set_solver.
Qed.

Lemma remove_check_stack_item_tagged_NoDup cids stk stk' idx:
  remove_check cids stk idx = Some stk' →
  stack_item_tagged_NoDup stk → stack_item_tagged_NoDup stk'.
Proof.
  revert idx.
  induction stk as [|it stk IH]; intros idx; simpl.
  { destruct idx; [|done]. intros ??. by simplify_eq. }
  destruct idx as [|idx]; [intros ??; by simplify_eq|].
  case check_protector eqn:Eq; [|done].
  move => /IH IH' ND. apply IH'. by eapply stack_item_tagged_NoDup_cons_1.
Qed.

Lemma remove_check_stack_item_tagged_NoDup_2 cids stk stk' stk0 idx:
  remove_check cids stk idx = Some stk' →
  stack_item_tagged_NoDup (stk ++ stk0) → stack_item_tagged_NoDup (stk' ++ stk0).
Proof.
  revert idx.
  induction stk as [|it stk IH]; intros idx; simpl.
  { destruct idx; [|done]. intros ??. by simplify_eq. }
  destruct idx as [|idx]; [intros ??; by simplify_eq|].
  case check_protector eqn:Eq; [|done].
  move => /IH IH' ND. apply IH'. by eapply stack_item_tagged_NoDup_cons_1.
Qed.

Lemma remove_check_sublist cids stk idx stk' :
  remove_check cids stk idx = Some stk' → sublist stk' stk.
Proof.
  revert idx.
  induction stk as [|it stk IH]; intros idx; simpl.
  { destruct idx; [|done]. intros ?. by simplify_eq. }
  destruct idx as [|idx]; [intros ?; by simplify_eq|].
  case check_protector eqn:Eq; [|done].
  move => /IH IH'. by constructor 3.
Qed.

Lemma stack_item_tagged_NoDup_app stk1 stk2 :
  stack_item_tagged_NoDup (stk1 ++ stk2) →
  stack_item_tagged_NoDup stk1 ∧ stack_item_tagged_NoDup stk2.
Proof. rewrite /stack_item_tagged_NoDup filter_app fmap_app NoDup_app. naive_solver. Qed.

Global Instance stack_item_tagged_NoDup_proper :
  Proper (Permutation ==> iff) stack_item_tagged_NoDup.
Proof. intros stk1 stk2 PERM. by rewrite /stack_item_tagged_NoDup PERM. Qed.

Lemma stack_item_tagged_NoDup_eq stk it1 it2 t :
  stack_item_tagged_NoDup stk →
  it1 ∈ stk → it2 ∈ stk → it1.(tg) = Tagged t → it2.(tg) = Tagged t →
  it1 = it2.
Proof.
  induction stk as [|it stk IH]; [set_solver|].
  intros ND. specialize (IH (stack_item_tagged_NoDup_cons_1 _ _ ND)).
  rewrite 2!elem_of_cons.
  move => [?|In1] [?|In2]; subst; [done|..]; intros Eq1 Eq2.
  - exfalso. apply elem_of_Permutation in In2 as [stk' Eq'].
    move : ND. rewrite Eq'.
    rewrite /stack_item_tagged_NoDup filter_cons decide_True; last by rewrite /is_tagged Eq1.
    rewrite filter_cons decide_True; last by rewrite /is_tagged Eq2.
    rewrite 2!fmap_cons Eq1 Eq2 NoDup_cons. set_solver.
  - exfalso. apply elem_of_Permutation in In1 as [stk' Eq'].
    move : ND. rewrite Eq'.
    rewrite /stack_item_tagged_NoDup filter_cons decide_True; last by rewrite /is_tagged Eq2.
    rewrite filter_cons decide_True; last by rewrite /is_tagged Eq1.
    rewrite 2!fmap_cons Eq1 Eq2 NoDup_cons. set_solver.
  - by apply IH.
Qed.
