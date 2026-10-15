(** This file has been adapted from the Stacked Borrows development, available at 
  https://gitlab.mpi-sws.org/FP/stacked-borrows
*)

From simuliris.stacked_borrows Require Export defs steps_foreach steps_list.

Lemma access1_in_stack stk kind t cids n stk' :
   access1 stk kind t cids = Some (n, stk') →
   ∃ it, it ∈ stk ∧ it.(tg) = t ∧ it.(perm) ≠ Disabled.
Proof.
  rewrite /access1. case find_granting as [gip|] eqn:Eq1; [|done].
  apply fmap_Some in Eq1 as [[i it] [(IN & [GR Eq] & FR)%list_find_Some EQ]].
  intros ?. exists it. split; last split; [|done|].
  - by eapply list_elem_of_lookup_2.
  - intros Eq1. by rewrite Eq1 in GR.
Qed.

Lemma access1_tagged_sublist stk kind bor cids n stk' :
  access1 stk kind bor cids = Some (n, stk') → tagged_sublist stk' stk.
Proof.
  rewrite /access1. case find_granting as [gip|]; [|done]. simpl.
  destruct kind.
  - case replace_check as [stk1|] eqn:Eq; [|done].
    simpl. intros. simplify_eq.
    rewrite -{2}(take_drop gip.1 stk). apply tagged_sublist_app; [|done].
    move : Eq. by apply replace_check_tagged_sublist.
  - case find_first_write_incompatible as [idx|]; [|done]. simpl.
    case remove_check as [stk1|] eqn:Eq; [|done].
    simpl. intros. simplify_eq.
    rewrite -{2}(take_drop gip.1 stk). apply tagged_sublist_app; [|done].
    move : Eq. by apply remove_check_tagged_sublist.
Qed.

Lemma access1_non_empty stk kind bor cids n stk' :
  access1 stk kind bor cids = Some (n, stk') → stk' ≠ [].
Proof.
  rewrite /access1. case find_granting as [gip|] eqn:Eq1; [|done].
  apply fmap_Some in Eq1 as [[i it] [[IN ?]%list_find_Some EQ]].
  subst gip; simpl.
  have ?: drop i stk ≠ [].
  { move => ND. move : IN. by rewrite -(Nat.add_0_r i) -(lookup_drop) ND /=. }
  destruct kind.
  - case replace_check as [stk1|]; [|done].
    simpl. intros ?. simplify_eq => /app_nil [_ ?]. by subst.
  - case find_first_write_incompatible as [?|]; [|done]. simpl.
    case remove_check as [?|]; [|done].
    simpl. intros ?. simplify_eq => /app_nil [_ ?]. by subst.
Qed.

Lemma for_each_access1 α nxtc l n tg kind α' :
  for_each α l n false
          (λ stk, nstk' ← access1 stk kind tg nxtc; Some nstk'.2) = Some α' →
  ∀ (l: loc) stk', α' !! l = Some stk' → ∃ stk, α !! l = Some stk ∧
    tagged_sublist stk' stk ∧ (stk ≠ [] → stk' ≠ []).
Proof.
  intros EQ. destruct (for_each_lookup  _ _ _ _ _ EQ) as [EQ1 [EQ2 EQ3]].
  intros l1 stk1 Eq1.
  case (decide (l1.1 = l.1)) => [Eql|NEql];
    [case (decide (l.2 ≤ l1.2 < l.2 + n)) => [[Le Lt]|NIN]|].
  - have Eql2: l1 = l +ₗ Z.of_nat (Z.to_nat (l1.2 - l.2)). {
      destruct l, l1. move : Eql Le => /= -> ?.
      rewrite /shift_loc /= Z2Nat.id; [|lia]. f_equal. lia. }
    destruct (EQ2 (Z.to_nat (l1.2 - l.2)) stk1)
      as [stk [Eq [[n1 stk'] [Eq' Eq0]]%bind_Some]];
      [rewrite -(Nat2Z.id n) -Z2Nat.inj_lt; lia|by rewrite -Eql2|].
    exists stk. split; [by rewrite Eql2|]. simplify_eq.
    split; [by eapply access1_tagged_sublist|intros; by eapply access1_non_empty].
  - exists stk1. split; [|done]. rewrite -EQ3; [done|].
    intros i Lt Eq. apply NIN. rewrite Eq /=. lia.
  - exists stk1. split; [|done]. rewrite -EQ3; [done|].
    intros i Lt Eq. apply NEql. by rewrite Eq.
Qed.

Lemma for_each_access1_non_empty α cids l n tg kind α' :
  for_each α l n false
          (λ stk, nstk' ← access1 stk kind tg cids; Some nstk'.2) = Some α' →
  wf_non_empty α → wf_non_empty α'.
Proof.
  move => /for_each_access1 EQ1 WF ?? /EQ1 [? [? [? NE]]]. by eapply NE, WF.
Qed.

Lemma access1_stack_item_tagged_NoDup stk kind bor cids n stk' :
  access1 stk kind bor cids = Some (n, stk') →
  stack_item_tagged_NoDup stk → stack_item_tagged_NoDup stk'.
Proof.
  rewrite /access1. case find_granting as [gip|] eqn:Eq1; [|done].
  apply fmap_Some in Eq1 as [[i it] [[IN ?]%list_find_Some EQ]].
  subst gip; simpl.
  destruct kind.
  - case replace_check as [stk1|] eqn:Eqc ; [|done].
    simpl. intros ?. simplify_eq.
    rewrite -{1}(take_drop n stk). move : Eqc.
    by apply replace_check_stack_item_tagged_NoDup_2.
  - case find_first_write_incompatible as [?|]; [|done]. simpl.
    case remove_check as [?|] eqn:Eqc ; [|done].
    simpl. intros ?. simplify_eq.
    rewrite -{1}(take_drop n stk). move : Eqc.
    apply remove_check_stack_item_tagged_NoDup_2.
Qed.

Lemma access1_read_eq it1 it2 stk tag t cids n stk':
  stack_item_tagged_NoDup stk →
  access1 stk AccessRead tag cids = Some (n, stk') →
  it1 ∈ stk → it2 ∈ stk' →
  it2.(perm) ≠ Disabled →
  it1.(tg) = Tagged t → it2.(tg) = Tagged t → it1 = it2.
Proof.
  intros ND ACC.
  have ND' := access1_stack_item_tagged_NoDup _ _ _ _ _ _ ACC ND.
  move : ACC. rewrite /= /access1 /=.
  case find_granting as [[idx pm]|] eqn:Eq1; [|done]. simpl.
  case replace_check as [stk1|] eqn:Eq2; [|done].
  simpl. intros ?. simplify_eq. intros In1.
  have SUB:= replace_check_tagged_sublist _ _ _ Eq2.
  rewrite elem_of_app. intros In2 ND2.
  destruct In2 as [In2|In2].
  - specialize (SUB _ In2) as (it3 & In3 & Eqt3 & Eqp3 & ND3).
    specialize (ND3 ND2).
    have ?: it3 = it2.
    { destruct it2, it3. simpl in *. by simplify_eq. }
    subst it3.
    apply (stack_item_tagged_NoDup_eq _ _ _ _ ND); [done|].
    rewrite -{1}(take_drop n stk) elem_of_app. by left.
  - apply (stack_item_tagged_NoDup_eq _ _ _ _ ND); [done|].
    rewrite -{1}(take_drop n stk) elem_of_app. by right.
Qed.

Lemma for_each_access1_stack_item α nxtc cids nxtp l n tg kind α' :
  for_each α l n false
          (λ stk, nstk' ← access1 stk kind tg cids; Some nstk'.2) = Some α' →
  wf_stacks α nxtp nxtc → wf_stacks α' nxtp nxtc.
Proof.
  intros ACC WF l' stk' Eq'.
  destruct (for_each_access1 _ _ _ _ _ _ _ ACC _ _ Eq') as [stk [Eq [SUB NN]]].
  split.
  - move => ? /SUB [? [IN [-> [-> ?]]]]. by apply (proj1 (WF _ _ Eq) _ IN).
  - clear SUB NN.
    destruct (for_each_lookup_case _ _ _ _ _ ACC _ _ _ Eq Eq') as [?|[Eqf ?]].
    { subst. by apply (WF _ _ Eq). }
    destruct (access1 stk kind tg cids) as [[]|] eqn:Eqf'; [|done].
    simpl in Eqf. simplify_eq.
    eapply access1_stack_item_tagged_NoDup; eauto. by apply (WF _ _ Eq).
Qed.

(** Dealloc *)
Lemma for_each_dealloc_lookup α l n f α' :
  for_each α l n true f = Some α' →
  (∀ (i: nat), (i < n)%nat → α' !! (l +ₗ i) = None) ∧
  (∀ (l': loc), (∀ (i: nat), (i < n)%nat → l' ≠ l +ₗ i) → α' !! l' = α !! l').
Proof.
  revert α. induction n as [|n IH]; intros α; simpl.
  { move => [<-]. split; intros ??; by [lia|]. }
  case (α !! (l +ₗ n)) as [stkn|] eqn:Eqn; [|done] => /=.
  case f as [stkn'|] eqn: Eqn'; [|done] => /= /IH [IH1 IH2]. split.
  - intros i Lt. case (decide (i = n)) => Eq'; [subst i|].
    + rewrite IH2; [by apply lookup_delete_eq|].
      move => ?? /shift_loc_inj /Nat2Z.inj ?. by lia.
    + apply IH1. by lia.
  - intros l' Lt. rewrite IH2.
    + rewrite lookup_delete_ne; [done|]. move => Eql'. apply (Lt n); by [lia|].
    + move => ??. apply Lt. lia.
Qed.

Lemma for_each_dealloc_lookup_Some α l n f α' :
  for_each α l n true f = Some α' →
  ∀ l' stk', α' !! l' = Some stk' →
  (∀ i : nat, (i < n)%nat → l' ≠ l +ₗ i) ∧ α !! l' = Some stk'.
Proof.
  intros EQ. destruct (for_each_dealloc_lookup  _ _ _ _ _ EQ) as [EQ1 EQ2].
  intros l1 stk1 Eq1.
  destruct (block_case l l1 n) as [NEql|Eql].
  - rewrite -EQ2 //.
  - destruct Eql as (i & Lt & ?). subst l1. rewrite EQ1 // in Eq1.
Qed.

Lemma free_mem_lookup l n h :
  (∀ (i: nat), (i < n)%nat → free_mem l n h !! (l +ₗ i) = None) ∧
  (∀ (l': loc), (∀ (i: nat), (i < n)%nat → l' ≠ l +ₗ i) →
    free_mem l n h !! l' = h !! l').
Proof.
  revert l. induction n as [|n IH]; intros l; simpl.
  { split; intros ??; by [lia|]. } split.
  - intros i Lt. destruct i as [|i].
    + rewrite shift_loc_0 lookup_delete_eq //.
    + rewrite lookup_delete_ne.
      * specialize (IH (l +ₗ 1))as [IH _].
        rewrite (_: l +ₗ S i = l +ₗ 1 +ₗ i).
        { apply IH. lia. }
        { rewrite shift_loc_assoc. f_equal. lia. }
      * rewrite -{1}(shift_loc_0 l).
        move => /shift_loc_inj ?. lia.
  - intros l' Lt.
    rewrite lookup_delete_ne.
    + apply IH. intros i Lti.
      rewrite (_: l +ₗ 1 +ₗ i = l +ₗ S i).
      * apply Lt. lia.
      * rewrite shift_loc_assoc. f_equal. lia.
    + rewrite -(shift_loc_0_nat l). intros ?. subst l'. apply (Lt O); [lia|done].
Qed.

Lemma free_mem_lookup_case l' l n h :
  (∀ i : nat, (i < n)%nat → l' ≠ l +ₗ i) ∧ free_mem l n h !! l' = h !! l' ∨
  ∃ i : nat, (i < n)%nat ∧ l' = l +ₗ i ∧ free_mem l n h !! (l +ₗ i) = None.
Proof.
  destruct (free_mem_lookup l n h) as [EQ1 EQ2].
  destruct (block_case l l' n) as [NEql|Eql].
  - left. rewrite -EQ2 //.
  - right. destruct Eql as (i & Lt & ?). exists i. do 2 (split; [done|]).
    subst l'. by apply EQ1.
Qed.

Lemma free_mem_dom l' l n h:
  l' ∈ dom (free_mem l n h) →
  l' ∈ dom h ∧
  (∀ i : nat, (i < n)%nat → l' ≠ l +ₗ i) ∧ free_mem l n h !! l' = h !! l'.
Proof.
  intros [? EqD]%elem_of_dom.
  destruct (free_mem_lookup_case l' l n h) as [Eqn|(i & Lt & ? & EqN)].
  - split; [|done]. apply elem_of_dom. destruct Eqn as [? Eqn].
    rewrite -Eqn. by eexists.
  - exfalso. subst l'. by rewrite EqD in EqN.
Qed.

Lemma memory_deallocated_delete' α nxtc l bor n α' (m: nat):
  memory_deallocated α nxtc (l +ₗ m) bor n = Some α' →
  α' = fold_right (λ (i: nat) α, delete (l +ₗ i) α) α (seq m n).
Proof.
  revert α.
  induction n as [|n IHn]; intros α; [by move => [->]|].
  rewrite /memory_deallocated /=.
  case lookup => stack /= ; [|done]. case dealloc1 => stack'; [|done].
  move => /IHn ->. clear. revert m. induction n as [|n IH]; intros m.
  - by rewrite /= shift_loc_0.
  - simpl. f_equal.
    by rewrite shift_loc_assoc -Nat2Z.inj_add -Nat.add_succ_comm Nat2Z.inj_add
               -shift_loc_assoc IH.
Qed.

Lemma memory_deallocated_delete α nxtc l bor n α':
  memory_deallocated α nxtc l bor n = Some α' →
  α' = fold_right (λ (i: nat) α, delete (l +ₗ i) α) α (seq O n).
Proof. intros. eapply memory_deallocated_delete'. rewrite shift_loc_0. by eauto. Qed.

Lemma dealloc1_Some stk t cids :
  is_Some (dealloc1 stk t cids) →
  ∃ it, it ∈ stk ∧ it.(tg) = t ∧
    Forall (λ x : item, ¬ is_active_protector cids x) stk ∧
    grants it.(perm) AccessWrite.
Proof.
  rewrite /dealloc1. move => [[]].
  case find_granting eqn:GR; [|done]. simpl.
  apply fmap_Some_1 in GR as [[i it'] [(GR & [? ?] &?)%list_find_Some ?]].
  simplify_eq. rewrite /find_top_active_protector.
  case list_find eqn:EqF; [done|]. intros _.
  apply list_find_None in EqF. exists it'.
  have ?: it' ∈ stk by eapply list_elem_of_lookup_2. done.
Qed.

Lemma dealloc1_singleton_Some it t cids:
  is_Some (dealloc1 [it] t cids) →
  it.(tg) = t ∧ (¬ is_active_protector cids it) ∧ grants it.(perm) AccessWrite.
Proof.
  move => /dealloc1_Some [it' [/list_elem_of_singleton In' [? [FA ?]]]].
  subst. split; last split; [done| |done].
  rewrite ->Forall_forall in FA. apply FA. by left.
Qed.
