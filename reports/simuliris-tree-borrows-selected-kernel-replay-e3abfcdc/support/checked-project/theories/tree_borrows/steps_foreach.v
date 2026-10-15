From simuliris.tree_borrows Require Export defs.

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

Lemma init_mem_dom' l n h (m: nat):
  dom (init_mem (l +ₗ m) n h) =
  dom h ∪ dom (init_mem (l +ₗ m) n ∅) .
Proof.
  revert h m. induction n as [|n IHn]; intros h m.
  - rewrite /= dom_empty_L right_id_L //.
  - rewrite /= 2!dom_insert_L.
    rewrite (_ : (l +ₗ m +ₗ 1) = (l +ₗ S m)).
    + rewrite IHn. set_solver.
    + rewrite shift_loc_assoc -(Nat2Z.inj_add _ 1). f_equal. lia.
Qed.

Lemma init_mem_dom l n h:
  dom (init_mem l n h) =
  dom h ∪ dom (init_mem l n ∅) .
Proof. by rewrite -(shift_loc_0_nat l) init_mem_dom'. Qed.

Lemma apply_within_trees_lookup trs trs' blk fn :
  apply_within_trees fn blk trs = Some trs' ->
  (exists tr tr', (
    trs !! blk = Some tr /\
    trs' !! blk = Some tr' /\
    fn tr = Some tr'
  )) /\
  forall blk', blk ≠ blk' -> trs !! blk' = trs' !! blk'.
Proof.
  unfold apply_within_trees; intro Applied.
  destruct (trs !! blk) as [t|] eqn:Lookup; inversion Applied as [H0].
  destruct (fn t) as [t'|] eqn:Result; inversion H0 as [t0].
  split.
  - exists t; exists t'. try repeat split; [apply lookup_insert_eq|apply Result].
  - intros blk' Diff. symmetry. apply lookup_insert_ne. apply Diff.
Qed.
(* NOTE: stack analogue was:
Lemma for_each_lookup α l n f α' :
  for_each α l n false f = Some α' →
  (∀ (i: nat) stk, (i < n)%nat → α !! (l +ₗ i) = Some stk → ∃ stk',
    α' !! (l +ₗ i) = Some stk' ∧ f stk = Some stk' ) ∧
  (∀ (i: nat) stk', (i < n)%nat → α' !! (l +ₗ i) = Some stk' → ∃ stk,
    α !! (l +ₗ i) = Some stk ∧ f stk = Some stk') ∧
  (∀ (l': loc), (∀ (i: nat), (i < n)%nat → l' ≠ l +ₗ i) → α' !! l' = α !! l').
*)

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

Lemma extend_trees_lookup trs tg off sz blk :
  (extend_trees tg blk off sz trs) !! blk = Some (init_tree tg off sz).
Proof. apply lookup_insert_eq. Qed.

Lemma extend_trees_lookup_ne trs tg off sz blk blk' :
  blk ≠ blk' ->
  extend_trees tg blk off sz trs !! blk' = trs !! blk'.
Proof. apply lookup_insert_ne. Qed.


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

Lemma free_mem_dom_inv l' l n h:
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



Lemma init_mem_lookup_fresh_poison blk off (n:nat) h :
  0 ≤ off ∧ off < n →
  init_mem (blk, 0) n h !! (blk, off) = Some ScPoison.
Proof.
  intros (Hpos & Hlt).
  pose proof (init_mem_lookup (blk, 0) n h) as (Hinit1&_).
  ospecialize (Hinit1 (Z.to_nat off) _); first lia.
  rewrite /= /shift_loc /= Z.add_0_l Z2Nat.id // in Hinit1.
Qed.

Lemma init_mem_lookup_fresh_None blk off (n:nat) h :
  (forall off, (blk, off) ∉ dom h) →
  (off < 0 ∨ n ≤ off) →
  init_mem (blk, 0) n h !! (blk, off) = None.
Proof.
  intros Hfresh Hout.
  pose proof (init_mem_lookup (blk, 0) n h) as (_&Hinit2).
  rewrite (Hinit2 (blk, off)).
  + eapply not_elem_of_dom, Hfresh.
  + intros i Hlt.
    rewrite /= /shift_loc /= Z.add_0_l.
    intros [= ->]. destruct Hout as [Hout|Hout]; lia.
Qed.

Lemma init_mem_lookup_fresh_old blk blk' off (n:nat) h :
  blk ≠ blk' →
  init_mem (blk, 0) n h !! (blk', off) = h !! (blk', off).
Proof.
  intros Hfresh.
  pose proof (init_mem_lookup (blk, 0) n h) as (_&Hinit2).
  apply Hinit2.
  intros ? _ [=]. done.
Qed.


Lemma init_mem_lookup_fresh_inv blk blk' off (n:nat) h k :
  (forall off, (blk, off) ∉ dom h) →
  init_mem (blk, 0) n h !! (blk', off) = k →
  (k = Some ScPoison ∧ blk = blk' ∧ 0 ≤ off ∧ off < n)
∨ (k = None ∧ blk = blk' ∧ (off < 0 ∨ n ≤ off))
∨ (k = h !! (blk', off) ∧ blk ≠ blk').
Proof.
  intros Hfresh Hinit.
  destruct (decide (blk = blk')) as [Heqblk|Hne].
  1: subst blk'; destruct (decide (0 ≤ off)) as [Hpos|Hneg].
  1: destruct (decide (off < n)) as [Hlt|Hge].
  { left. subst k. split_and!; try done. by rewrite init_mem_lookup_fresh_poison. }
  1-2: right; left; split_and!; try done; last lia.
  1-2: subst k; rewrite init_mem_lookup_fresh_None; try done; lia.
  { right. right. split; last done. subst k. by apply init_mem_lookup_fresh_old. }
Qed.

