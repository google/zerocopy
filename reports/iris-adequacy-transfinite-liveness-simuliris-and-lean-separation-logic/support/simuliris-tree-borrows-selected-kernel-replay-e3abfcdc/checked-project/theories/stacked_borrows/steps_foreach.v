(** This file has been adapted from the Stacked Borrows development, available at 
  https://gitlab.mpi-sws.org/FP/stacked-borrows
*)

From simuliris.stacked_borrows Require Export defs.

Lemma init_mem_foldr' l n h (m: nat):
  init_mem (l +ₗ m) n h =
  fold_right (λ (i: nat) hi, <[(l +ₗ i):=☠%S]> hi) h (seq m n).
Proof.
  revert m. induction n as [|n IHn]; intros m; [done|]. simpl. f_equal.
  by rewrite shift_loc_assoc -(Nat2Z.inj_add m 1) Nat.add_1_r IHn.
Qed.
Lemma init_mem_foldr l n h:
  init_mem l n h =
  fold_right (λ (i: nat) hi, <[(l +ₗ i):=☠%S]> hi) h (seq 0 n).
Proof. by rewrite -init_mem_foldr' shift_loc_0. Qed.

Lemma free_mem_foldr' l n h (m: nat):
  free_mem (l +ₗ m) n h =
  fold_right (λ (i: nat) hi, delete (l +ₗ i) hi) h (seq m n).
Proof.
  revert m. induction n as [|n IHn]; intros m; [done|]. simpl. f_equal.
  by rewrite shift_loc_assoc -(Nat2Z.inj_add m 1) Nat.add_1_r IHn.
Qed.
Lemma free_mem_foldr l n h:
  free_mem l n h =
  fold_right (λ (i: nat) hi, delete (l +ₗ i) hi) h (seq 0 n).
Proof. by rewrite -free_mem_foldr' shift_loc_0. Qed.

Lemma init_stacks_foldr' α l n si (m: nat):
  init_stacks α (l +ₗ m) n si =
  fold_right (λ (i: nat) hi, <[(l +ₗ i):= init_stack si]> hi) α (seq m n).
Proof.
  revert m. induction n as [|n IHn]; intros m; [done|]. simpl. f_equal.
  by rewrite shift_loc_assoc -(Nat2Z.inj_add m 1) Nat.add_1_r IHn.
Qed.
Lemma init_stacks_foldr α l n si:
  init_stacks α l n si =
  fold_right (λ (i: nat) hi, <[(l +ₗ i):= init_stack si]> hi) α (seq 0 n).
Proof. by rewrite -init_stacks_foldr' shift_loc_0. Qed.

Lemma init_mem_dom' l n h (m: nat):
  dom (init_mem (l +ₗ m) n h) ≡
  dom h ∪ dom (init_mem (l +ₗ m) n ∅) .
Proof.
  revert h m. induction n as [|n IHn]; intros h m.
  - by rewrite /= dom_empty right_id.
  - rewrite /= 2!dom_insert.
    rewrite (_ : (l +ₗ m +ₗ 1) = (l +ₗ S m)).
    + rewrite IHn. set_solver.
    + rewrite shift_loc_assoc -(Nat2Z.inj_add _ 1). f_equal. lia.
Qed.

Lemma init_mem_dom l n h:
  dom (init_mem l n h) ≡
  dom h ∪ dom (init_mem l n ∅) .
Proof. by rewrite -(shift_loc_0_nat l) init_mem_dom'. Qed.

Lemma for_each_lookup α l n f α' :
  for_each α l n false f = Some α' →
  (∀ (i: nat) stk, (i < n)%nat → α !! (l +ₗ i) = Some stk → ∃ stk',
    α' !! (l +ₗ i) = Some stk' ∧ f stk = Some stk' ) ∧
  (∀ (i: nat) stk', (i < n)%nat → α' !! (l +ₗ i) = Some stk' → ∃ stk,
    α !! (l +ₗ i) = Some stk ∧ f stk = Some stk') ∧
  (∀ (l': loc), (∀ (i: nat), (i < n)%nat → l' ≠ l +ₗ i) → α' !! l' = α !! l').
Proof.
  revert α. induction n as [|n IH]; intros α; simpl.
  { move => [<-]. split; last split; intros ??; [lia|lia|done]. }
  case (α !! (l +ₗ n)) as [stkn|] eqn:Eqn; [|done] => /=.
  case f as [stkn'|] eqn: Eqn'; [|done] => /= /IH [IH1 [IH2 IH3]].
  split; last split.
  - intros i stk Lt Eqi. case (decide (i = n)) => Eq'; [subst i|].
    + rewrite Eqi in Eqn. simplify_eq.
      rewrite Eqn' IH3; [by rewrite lookup_insert_eq; eexists|].
      move => ?? /shift_loc_inj /Nat2Z.inj ?. by lia.
    + apply IH1; [lia|]. rewrite lookup_insert_ne; [done|].
      by move => /shift_loc_inj /Nat2Z.inj ? //.
  - intros i stk Lt Eqi. case (decide (i = n)) => Eq'; [subst i|].
    + move : Eqi. rewrite IH3.
      * rewrite lookup_insert_eq. intros. simplify_eq. naive_solver.
      * move => ?? /shift_loc_inj /Nat2Z.inj ?. by lia.
    + destruct (IH2 i stk) as [stk0 [Eq0 Eqf0]]; [lia|done|].
      exists stk0. split; [|done]. move : Eq0. rewrite lookup_insert_ne; [done|].
      by move => /shift_loc_inj /Nat2Z.inj ? //.
  - intros l' Lt. rewrite IH3.
    + rewrite lookup_insert_ne; [done|]. move => Eql'. apply (Lt n); by [lia|].
    + move => ??. apply Lt. lia.
Qed.

Lemma block_case l l' n :
  (∀ i : nat, (i < n)%nat → l' ≠ l +ₗ i) ∨
  ∃ i : nat, (i < n)%nat ∧ l' = l +ₗ i.
Proof.
  case (decide (l'.1 = l.1)) => [Eql|NEql];
    [case (decide (l.2 ≤ l'.2 < l.2 + n)) => [[Le Lt]|NIN]|].
  - have Eql2: l' = l +ₗ Z.of_nat (Z.to_nat (l'.2 - l.2)). {
      destruct l, l'. move : Eql Le => /= -> ?.
      rewrite /shift_loc /= Z2Nat.id; [|lia]. f_equal. lia. }
    right. rewrite Eql2. rewrite Eql2 /= in Lt.
    eexists. split; [|done]. lia.
  - left. intros i Lt Eq3. apply NIN. rewrite Eq3 /=. lia.
  - left. intros i Lt Eq3. apply NEql. by rewrite Eq3.
Qed.

Lemma for_each_lookup_case α l n f α' :
  for_each α l n false f = Some α' →
  ∀ l' stk stk', α !! l' = Some stk → α' !! l' = Some stk' →
  stk = stk' ∨ f stk = Some stk' ∧ ∃ i : nat, (i < n)%nat ∧ l' = l +ₗ i.
Proof.
  intros EQ. destruct (for_each_lookup  _ _ _ _ _ EQ) as [EQ1 [EQ2 EQ3]].
  intros l1 stk stk' Eq Eq'.
  destruct (block_case l l1 n) as [NEql|Eql].
  - left. rewrite EQ3 in Eq'; [by simplify_eq|].
    intros i Lt Eq3. by apply (NEql i).
  - right. split; [|done].
    destruct Eql as (i & Lt & Eql). subst l1.
    destruct (EQ2 _ _ Lt Eq') as [stk1 [Eq1 Eq2]].
    rewrite Eq in Eq1. by simplify_eq.
Qed.

Lemma for_each_lookup_case_2 α l n f α' :
  for_each α l n false f = Some α' →
  (∀ (i: nat), (i < n)%nat → ∃ stk stk',
    α !! (l +ₗ i) = Some stk ∧ α' !! (l +ₗ i) = Some stk' ∧ f stk = Some stk' ) ∧
  (∀ (l': loc), (∀ (i: nat), (i < n)%nat → l' ≠ l +ₗ i) → α' !! l' = α !! l').
Proof.
  revert α. induction n as [|n IH]; intros α; simpl.
  { move => [<-]. split; intros ??; [lia|done]. }
  case (α !! (l +ₗ n)) as [stkn|] eqn:Eqn; [|done] => /=.
  case (f stkn) as [stkn'|] eqn: Eqn'; [|done] => /= /IH [IH1 IH2].
  split.
  - intros i Lt.
    case (decide (i = n)) => Eq'; [subst i|].
    + rewrite Eqn. rewrite IH2; [rewrite lookup_insert_eq; naive_solver|].
      move => ?? /shift_loc_inj /Nat2Z.inj ?. by lia.
    + destruct (IH1 i) as (stk & stk' & Eqs & ?); [lia|].
      rewrite lookup_insert_ne in Eqs; [naive_solver|].
      by move => /shift_loc_inj /Nat2Z.inj ? //.
  - intros l' Lt. rewrite IH2.
    + rewrite lookup_insert_ne; [done|]. move => Eql'. apply (Lt n); by [lia|].
    + move => ??. apply Lt. lia.
Qed.

Lemma for_each_true_lookup_case_2 α l n f α' :
  for_each α l n true f = Some α' →
  (∀ (i: nat), (i < n)%nat → ∃ stk stk',
    α !! (l +ₗ i) = Some stk ∧ α' !! (l +ₗ i) = None ∧ f stk = Some stk' ) ∧
  (∀ (l': loc), (∀ (i: nat), (i < n)%nat → l' ≠ l +ₗ i) → α' !! l' = α !! l').
Proof.
  revert α. induction n as [|n IH]; intros α; simpl.
  { move => [<-]. split; intros ??; [lia|done]. }
  case (α !! (l +ₗ n)) as [stkn|] eqn:Eqn; [|done] => /=.
  case (f stkn) as [stkn'|] eqn: Eqn'; [|done] => /= /IH [IH1 IH2].
  split.
  - intros i Lt.
    case (decide (i = n)) => Eq'; [subst i|].
    + rewrite Eqn. rewrite IH2; [rewrite lookup_delete_eq; naive_solver|].
      move => ?? /shift_loc_inj /Nat2Z.inj ?. by lia.
    + destruct (IH1 i) as (stk & stk' & Eqs & ?); [lia|].
      rewrite lookup_delete_ne in Eqs; [naive_solver|].
      by move => /shift_loc_inj /Nat2Z.inj ? //.
  - intros l' Lt. rewrite IH2.
    + rewrite lookup_delete_ne; [done|]. move => Eql'. apply (Lt n); by [lia|].
    + move => ??. apply Lt. lia.
Qed.

Lemma init_mem_lookup l n h :
  (∀ (i: nat), (i < n)%nat → init_mem l n h !! (l +ₗ i) = Some ☠%S) ∧
  (∀ (l': loc), (∀ (i: nat), (i < n)%nat → l' ≠ l +ₗ i) →
    init_mem l n h !! l' = h !! l').
Proof.
  revert l h. induction n as [|n IH]; intros l h; simpl.
  { split; intros ??; [lia|done]. }
  destruct (IH (l +ₗ 1) h) as [IH1 IH2].
  split.
  - intros i Lt. destruct i as [|i].
    + rewrite shift_loc_0_nat lookup_insert_eq //.
    + have Eql: l +ₗ S i = (l +ₗ 1) +ₗ i.
      { rewrite shift_loc_assoc. f_equal. lia. }
      rewrite lookup_insert_ne.
      * rewrite Eql. destruct (IH (l +ₗ 1) h) as [IH' _].
        apply IH'; lia.
      * rewrite -{1}(shift_loc_0_nat l). intros ?%shift_loc_inj. lia.
  - intros l' Lt. rewrite lookup_insert_ne.
    + apply IH2. intros i Lt'.
      rewrite (_: (l +ₗ 1) +ₗ i = l +ₗ S i); last first.
      { rewrite shift_loc_assoc. f_equal. lia. }
      apply Lt. lia.
    + specialize (Lt O ltac:(lia)). by rewrite shift_loc_0_nat in Lt.
Qed.

Lemma init_mem_lookup_case l n h :
  ∀ l' s', init_mem l n h !! l' = Some s' →
  h !! l' = Some s' ∧ (∀ i : nat, (i < n)%nat → l' ≠ l +ₗ i) ∨
  ∃ i : nat, (i < n)%nat ∧ l' = l +ₗ i.
Proof.
  destruct (init_mem_lookup l n h) as [EQ1 EQ2].
  intros l1 s1 Eq'.
  destruct (block_case l l1 n) as [NEql|Eql].
  - left. rewrite EQ2 // in Eq'.
  - by right.
Qed.

Lemma init_mem_lookup_empty l n :
  ∀ l' s', init_mem l n ∅ !! l' = Some s' →
  ∃ i : nat, (i < n)%nat ∧ l' = l +ₗ i.
Proof. move => l' s' /init_mem_lookup_case [[//]|//]. Qed.

Lemma init_stacks_lookup α l n t :
  (∀ (i: nat), (i < n)%nat →
    init_stacks α l n t !! (l +ₗ i) = Some (init_stack t)) ∧
  (∀ (l': loc), (∀ (i: nat), (i < n)%nat → l' ≠ l +ₗ i) →
    init_stacks α l n t !! l' = α !! l').
Proof.
  revert l α. induction n as [|n IH]; intros l α; simpl.
  { split; intros ??; [lia|done]. }
  destruct (IH (l +ₗ 1) α) as [IH1 IH2].
  split.
  - intros i Lt. destruct i as [|i].
    + rewrite shift_loc_0_nat lookup_insert_eq //.
    + have Eql: l +ₗ S i = (l +ₗ 1) +ₗ i.
      { rewrite shift_loc_assoc. f_equal. lia. }
      rewrite lookup_insert_ne.
      * rewrite Eql. destruct (IH (l +ₗ 1) α) as [IH' _].
        apply IH'; lia.
      * rewrite -{1}(shift_loc_0_nat l). intros ?%shift_loc_inj. lia.
  - intros l' Lt. rewrite lookup_insert_ne.
    + apply IH2. intros i Lt'.
      rewrite (_: (l +ₗ 1) +ₗ i = l +ₗ S i); last first.
      { rewrite shift_loc_assoc. f_equal. lia. }
      apply Lt. lia.
    + specialize (Lt O ltac:(lia)). by rewrite shift_loc_0_nat in Lt.
Qed.

Lemma init_stacks_lookup_case α l n t :
  ∀ l' s', init_stacks α l n t !! l' = Some s' →
  α !! l' = Some s' ∧ (∀ i : nat, (i < n)%nat → l' ≠ l +ₗ i) ∨
  ∃ i : nat, (i < n)%nat ∧ l' = l +ₗ i.
Proof.
  destruct (init_stacks_lookup α l n t) as [EQ1 EQ2].
  intros l1 s1 Eq'.
  destruct (block_case l l1 n) as [NEql|Eql].
  - left. rewrite EQ2 // in Eq'.
  - by right.
Qed.

Lemma init_stacks_lookup_case_2 α l n t :
  ∀ l' s', α !! l' = Some s' →
  init_stacks α l n t !! l' = Some s' ∧ (∀ i : nat, (i < n)%nat → l' ≠ l +ₗ i) ∨
  ∃ i : nat, (i < n)%nat ∧ l' = l +ₗ i ∧
    init_stacks α l n t !! l' = Some $ init_stack t.
Proof.
  destruct (init_stacks_lookup α l n t) as [EQ1 EQ2].
  intros l1 s1 Eq'.
  destruct (block_case l l1 n) as [NEql|Eql].
  - left. rewrite EQ2 //.
  - right. destruct Eql as (i & Lt & ?).
    exists i. do 2 (split; [done|]). subst l1. by apply EQ1.
Qed.

Lemma for_each_dom α l n f α' :
  for_each α l n false f = Some α' → dom α ≡ dom α'.
Proof.
  revert α. induction n as [|n IH]; intros α; [by move => /= [-> //]|].
  simpl. destruct (α !! (l +ₗ n)) eqn:Eq; [|done].
  simpl. case f => stack' /=; [|done]. move => /IH <-.
  symmetry. apply dom_map_insert_is_Some. rewrite Eq. by eexists.
Qed.
