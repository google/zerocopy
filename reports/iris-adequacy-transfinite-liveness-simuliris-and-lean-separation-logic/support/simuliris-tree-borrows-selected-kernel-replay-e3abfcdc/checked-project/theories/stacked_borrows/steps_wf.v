(** This file has been adapted from the Stacked Borrows development, available at 
  https://gitlab.mpi-sws.org/FP/stacked-borrows
*)

From simuliris.stacked_borrows Require Import helpers.
From simuliris.stacked_borrows Require Export defs steps_foreach steps_list steps_access.

Lemma wf_init_state : state_wf init_state.
Proof.
  constructor; simpl; try (intros ?; set_solver).
Qed.

(** Steps preserve wellformedness *)
Lemma wf_stack_item_mono α :
  Proper ((≤)%nat ==> (≤)%nat ==> impl) (wf_stacks α).
Proof.
  move=> ?? Le1 ? ? Le2 WF ?? /WF [Hf ND]. split; [|done].
  move => ? /Hf [TG1 TG2]. split.
  - move : TG1. case tg => [?|]; [lia|done].
  - move : TG2. case protector => [?|]; [lia|done].
Qed.

Lemma wf_mem_tag_mono h :
  Proper ((≤)%nat ==> impl) (wf_mem_tag h).
Proof. move => ??? WF ??? /WF /=. lia. Qed.

(** Alloc *)
Lemma alloc_step_wf (σ σ': state) e e' l bor T efs:
  mem_expr_step σ.(shp) e (AllocEvt l bor T) σ'.(shp) e' efs →
  bor_step σ.(sst) σ.(scs) σ.(snp) σ.(snc)
           (AllocEvt l bor T)
           σ'.(sst) σ'.(scs) σ'.(snp) σ'.(snc) →
  state_wf σ → state_wf σ'.
Proof.
  destruct σ as [h α cids nxtp nxtc].
  destruct σ' as [h' α' cids' nxtp' nxtc']. simpl.
  intros BS IS WF. inversion BS. clear BS. simplify_eq.
  destruct (tsize T) eqn:Eqs.
  - inversion IS; clear IS; simplify_eq; constructor; simpl;
      try rewrite Eqs /=; try by apply WF.
    + eapply wf_stack_item_mono; [..|by apply WF]; [simpl; lia|done].
  - inversion IS; clear IS; simplify_eq; constructor; cbn -[init_mem].
    + rewrite Eqs init_stacks_foldr init_mem_foldr.
      apply foldr_gmap_insert_dom, WF.
    + intros ??. rewrite init_stacks_foldr.
      intros [->|Eq]%foldr_gmap_insert_lookup; split.
      * intros si ->%list_elem_of_singleton. simpl. split; [lia|done].
      * apply stack_item_tagged_NoDup_singleton.
      * move => si /(proj1 (state_wf_stack_item _ WF _ _ Eq)) /= [Lt ?].
        split; [|done]. destruct si.(tg); [simpl; lia|done..].
      * apply (state_wf_stack_item _ WF _ _ Eq).
    + intros ??. rewrite init_stacks_foldr.
      intros [->|Eq]%foldr_gmap_insert_lookup; [done|].
      by apply (state_wf_non_empty _ WF _ _ Eq).
    + apply WF.
Qed.

(** Dealloc *)
Lemma dealloc_step_wf σ σ' e e' l bor T efs :
  mem_expr_step σ.(shp) e (DeallocEvt l bor T) σ'.(shp) e' efs →
  bor_step σ.(sst) σ.(scs) σ.(snp) σ.(snc)
           (DeallocEvt l bor T)
           σ'.(sst) σ'.(scs) σ'.(snp) σ'.(snc) →
  state_wf σ → state_wf σ'.
Proof.
  destruct σ as [h α cids nxtp nxtc].
  destruct σ' as [h' α' cids' nxtp' nxtc']. simpl.
  intros BS IS WF.
  inversion BS. clear BS. simplify_eq.
  inversion IS. clear IS. simplify_eq.
  rewrite (memory_deallocated_delete α cids' l bor (tsize T) α'); [|done].
  constructor; simpl.
  - rewrite free_mem_foldr. apply foldr_gmap_delete_dom, WF.
  - intros ?? Eq%foldr_gmap_delete_lookup.
    apply (state_wf_stack_item _ WF _ _ Eq).
  - intros ?? Eq%foldr_gmap_delete_lookup.
    apply (state_wf_non_empty _ WF _ _ Eq).
  - apply WF.
Qed.

(** Copy *)
Lemma copy_step_wf σ σ' e e' l bor T vl efs :
  mem_expr_step σ.(shp) e (CopyEvt l bor T vl) σ'.(shp) e' efs →
  bor_step σ.(sst) σ.(scs) σ.(snp) σ.(snc)
           (CopyEvt l bor T vl)
           σ'.(sst) σ'.(scs) σ'.(snp) σ'.(snc) →
  state_wf σ → state_wf σ' (* ∧ vl <<t σ'.(snp) *).
Proof.
  destruct σ as [h α cids nxtp nxtc].
  destruct σ' as [h' α' cids' nxtp' nxtc']. simpl.
  intros BS IS WF.
  inversion BS. clear BS. simplify_eq.
  inversion IS; clear IS; simplify_eq.
  constructor; simpl.
  - rename select (memory_read _ _ _ _ _ = _) into ACC.
    rewrite -(for_each_dom α l (tsize T) _ _ ACC). by apply WF.
  - eapply for_each_access1_stack_item; eauto. apply WF.
  - eapply for_each_access1_non_empty; eauto. apply WF.
  - apply WF.
Qed.

Lemma failed_copy_step_wf σ σ' e e' l bor T efs :
  mem_expr_step σ.(shp) e (FailedCopyEvt l bor T) σ'.(shp) e' efs →
  bor_step σ.(sst) σ.(scs) σ.(snp) σ.(snc)
           (FailedCopyEvt l bor T)
           σ'.(sst) σ'.(scs) σ'.(snp) σ'.(snc) →
  state_wf σ → state_wf σ'.
Proof.
  destruct σ as [h α cids nxtp nxtc].
  destruct σ' as [h' α' cids' nxtp' nxtc']. simpl.
  intros BS IS WF.
  inversion BS. clear BS. simplify_eq.
  inversion IS; clear IS; simplify_eq.
  done.
Qed.

(** Write *)
Lemma write_mem_dom l vl h
  (DEFINED: ∀ i : nat, (i < length vl)%nat → (l +ₗ i) ∈ dom h) :
  dom (write_mem l vl h) ≡ dom h.
Proof.
  revert l h DEFINED. induction vl as [|v vl IH]; intros l h DEFINED; [done|].
  rewrite /= IH.
  - apply dom_map_insert_is_Some. rewrite -(shift_loc_0_nat l).
    apply (elem_of_dom (D:=gset loc)), DEFINED. simpl. lia.
  - intros i Lt. apply elem_of_dom. rewrite lookup_insert_is_Some'. right.
    rewrite (shift_loc_assoc_nat l 1). apply (elem_of_dom (D:=gset loc)), DEFINED.
    simpl. lia.
Qed.

Lemma write_mem_lookup l vl h :
  (∀ (i: nat), (i < length vl)%nat → write_mem l vl h !! (l +ₗ i) = vl !! i) ∧
  (∀ (l': loc), (∀ (i: nat), (i < length vl)%nat → l' ≠ l +ₗ i) →
    write_mem l vl h !! l' = h !! l').
Proof.
  revert l h. induction vl as [|v vl IH]; move => l h; simpl;
    [split; [intros ?; by lia|done]|].
  destruct (IH (l +ₗ 1) (<[l:=v]> h)) as [IH1 IH2]. split.
  - intros i Lt. destruct i as [|i].
    + rewrite shift_loc_0_nat /=. rewrite IH2; [by rewrite lookup_insert_eq|].
      move => ? _.
      rewrite shift_loc_assoc -{1}(shift_loc_0 l) => /shift_loc_inj ?. by lia.
    + rewrite /= -IH1; [|lia].  by rewrite shift_loc_assoc -(Nat2Z.inj_add 1).
  - intros l' Lt. rewrite IH2.
    + rewrite lookup_insert_ne; [done|].
      move => ?. subst l'. apply (Lt O); [lia|by rewrite shift_loc_0_nat].
    + move => i Lti. rewrite shift_loc_assoc -(Nat2Z.inj_add 1).
      apply Lt. by lia.
Qed.

Lemma write_mem_lookup_case l vl h l' :
  (∃ (i: nat), (i < length vl)%nat ∧ l' = l +ₗ i ∧ write_mem l vl h !! (l +ₗ i) = vl !! i)
  ∨ ((∀ (i: nat), (i < length vl)%nat → l' ≠ l +ₗ i) ∧ write_mem l vl h !! l' = h !! l').
Proof.
  destruct (write_mem_lookup l vl h) as [EQ1 EQ2].
  case (decide (l'.1 = l.1)) => [Eql|NEql];
    [case (decide (l.2 ≤ l'.2 < l.2 + length vl)) => [[Le Lt]|NIN]|].
  - have Eql2: l' = l +ₗ Z.of_nat (Z.to_nat (l'.2 - l.2)). {
      destruct l, l'. move : Eql Le => /= -> ?.
      rewrite /shift_loc /= Z2Nat.id; [|lia]. f_equal. lia. }
    have Lt1: (Z.to_nat (l'.2 - l.2) < length vl)%nat
      by rewrite -(Nat2Z.id (length _)) -Z2Nat.inj_lt; lia.
    specialize (EQ1 _ Lt1).
    rewrite -Eql2 in EQ1. left.
    exists (Z.to_nat (l'.2 - l.2)). repeat split; [done..|by rewrite -Eql2].
  - right.
    have ?: (∀ (i: nat), (i < length vl)%nat → l' ≠ l +ₗ i).
    { intros i Lt Eq3. apply NIN. rewrite Eq3 /=. lia. }
    split; [done|]. by apply EQ2.
  - right.
    have ?: (∀ (i: nat), (i < length vl)%nat → l' ≠ l +ₗ i).
    { intros i Lt Eq3. apply NEql. by rewrite Eq3. }
    split; [done|]. by apply EQ2.
Qed.

Lemma write_step_wf σ σ' e e' l bor T vl efs :
  mem_expr_step σ.(shp) e (WriteEvt l bor T vl) σ'.(shp) e' efs →
  bor_step σ.(sst) σ.(scs) σ.(snp) σ.(snc)
           (WriteEvt l bor T vl)
           σ'.(sst) σ'.(scs) σ'.(snp) σ'.(snc) →
  state_wf σ → state_wf σ'.
Proof.
  destruct σ as [h α cids nxtp nxtc].
  destruct σ' as [h' α' cids' nxtp' nxtc']. simpl.
  intros BS IS WF.
  inversion BS. clear BS. simplify_eq.
  inversion IS. clear IS. simplify_eq.
  constructor; simpl.
  - rename select (memory_written _ _ _ _ _ = _) into ACC.
    rewrite -(for_each_dom α l (tsize T) _ _ ACC).
    rewrite write_mem_dom; [by apply WF|done].
  - eapply for_each_access1_stack_item; eauto. apply WF.
  - eapply for_each_access1_non_empty; eauto. apply WF.
  - apply WF.
Qed.

(** Call *)
Lemma initcall_step_wf σ σ' e e' n efs :
  mem_expr_step σ.(shp) e (InitCallEvt n) σ'.(shp) e' efs →
  bor_step σ.(sst) σ.(scs) σ.(snp) σ.(snc)
           (InitCallEvt n)
           σ'.(sst) σ'.(scs) σ'.(snp) σ'.(snc) →
  state_wf σ → state_wf σ'.
Proof.
  destruct σ as [h α cids nxtp nxtc].
  destruct σ' as [h' α' cids' nxtp' nxtc']. simpl.
  intros BS IS WF.
  inversion BS. clear BS. simplify_eq.
  inversion IS. clear IS. simplify_eq.
  constructor; simpl; [apply WF..|intros ?? Eq; split|apply WF|].
  - intros si In.
    destruct ((proj1 (state_wf_stack_item _ WF _ _ Eq)) _ In) as [SI1 SI2].
    split; [done|]. move : SI2. destruct si.(protector); [simpl; lia|done].
  - apply (state_wf_stack_item _ WF _ _ Eq).
  - intros c. rewrite elem_of_union.
    move => [|/(state_wf_cid_agree _ WF)]; [intros ->%elem_of_singleton_1; by left|by right].
Qed.

(** EndCall *)
Lemma endcall_step_wf σ σ' e e' n efs :
  mem_expr_step σ.(shp) e (EndCallEvt n) σ'.(shp) e' efs →
  bor_step σ.(sst) σ.(scs) σ.(snp) σ.(snc)
           (EndCallEvt n)
           σ'.(sst) σ'.(scs) σ'.(snp) σ'.(snc) →
  state_wf σ → state_wf σ'.
Proof.
  destruct σ as [h α cids nxtp nxtc].
  destruct σ' as [h' α' cids' nxtp' nxtc']. simpl.
  intros BS IS WF.
  inversion BS. clear BS. simplify_eq.
  inversion IS. clear IS. simplify_eq.
  constructor; simpl; [apply WF..|intros ?? Eq; split |apply WF|].
  - intros ? In. apply ((proj1 (state_wf_stack_item _ WF _ _ Eq)) _ In).
  - apply (state_wf_stack_item _ WF _ _ Eq).
  - intros c IN. apply WF.
    apply elem_of_difference in IN. apply IN.
Qed.

(** Retag *)

Lemma tag_value_included_trans tg :
  Proper ((≤)%nat ==> impl) (tag_included tg).
Proof.
  intros nxtp nxtp' Le. rewrite /tag_included.
  by destruct tg; simpl; intros ?; [lia..|done].
Qed.

Lemma retag_ref_nxtp_mono α cids nxtp l bor T kind bar bor' α' nxtp' :
  retag_ref α cids nxtp l bor T kind bar = Some (bor', α', nxtp') →
  (nxtp ≤ nxtp')%nat.
Proof.
  rewrite /retag_ref.
  case tsize => ?; [by intros; simplify_eq|].
  case reborrow eqn:Eqb; [simpl|done]. intros. simplify_eq. lia.
Qed.

Lemma retag_ref_nxtp_bor_mono α cids nxtp l bor T kind bar bor' α' nxtp' :
  retag_ref α cids nxtp l bor T kind bar = Some (bor', α', nxtp') →
  bor <t nxtp → bor' <t nxtp'.
Proof.
  rewrite /retag_ref.
  case tsize => ?; [by intros; simplify_eq|].
  case reborrow eqn:Eqb; [simpl|done]. intros. simplify_eq.
  destruct kind; simpl; [lia..|done].
Qed.

Lemma item_insert_dedup_non_empty stk new n :
  stk ≠ [] → item_insert_dedup stk new n ≠ [].
Proof.
  intros. destruct n; simpl.
  - destruct stk; [done|by case decide].
  - case lookup => [?|]; case lookup => [?|].
    + case decide => ?; [done|]. case decide => ?; [done|].
      move => ?. by eapply app_cons_not_nil.
    + case decide => ?; [done|]. move => ?. by eapply app_cons_not_nil.
    + case decide => ?; [done|]. move => ?. by eapply app_cons_not_nil.
    + move => ?. by eapply app_cons_not_nil.
Qed.

Lemma item_insert_dedup_subseteq stk new n :
  item_insert_dedup stk new n ⊆ new :: stk.
Proof.
  intros. destruct n as [|n]; simpl.
  - destruct stk; [done|case decide => [<-|_]]; set_solver.
  - have ?: take (S n) stk ++ new :: drop (S n) stk ⊆ new :: stk.
    { intros x.
      rewrite elem_of_app elem_of_cons or_assoc (or_comm _ (x = new))
        -or_assoc -elem_of_app take_drop. set_solver. }
    by case lookup => [?|]; case lookup => [?|];
      [case decide => ?; [set_solver|]..|]; [case decide => ?; [set_solver|]|..].
Qed.

Lemma grant_non_empty stk bor new cids stk':
  grant stk bor new cids = Some stk' →
  stk ≠ [] → stk' ≠ [].
Proof.
  rewrite /grant. case find_granting as [[n pm]|]; [|done].
  cbn -[item_insert_dedup].
  destruct new.(perm). (* TODO: duplicated proofs *)
  - case access1 as [[n1 stk1]|]; [|done].
    simpl. intros ? _. simplify_eq. destruct stk1; [done|by case decide].
  - case find_first_write_incompatible as [n1|]; [|done].
    simpl. intros. simplify_eq. by apply item_insert_dedup_non_empty.
  - case access1 as [[n1 stk1]|]; [|done].
    simpl. intros ? _. simplify_eq. destruct stk1; [done|by case decide].
  - case access1 as [[n1 stk1]|]; [|done].
    simpl. intros ? _. simplify_eq. destruct stk1; [done|by case decide].
Qed.

Lemma tagged_sublist_stack_item_included stk stk' nxtp nxtc  :
  tagged_sublist stk' stk →
  stack_item_included stk nxtp nxtc → stack_item_included stk' nxtp nxtc.
Proof. by move => SF HI si /SF [? [/HI ? [-> [-> ?]]]]. Qed.

Lemma subseteq_stack_item_included stk stk' nxtp nxtc  :
  stk' ⊆ stk →
  stack_item_included stk nxtp nxtc → stack_item_included stk' nxtp nxtc.
Proof. by move => SF HI si /SF /HI. Qed.

Lemma subseteq_tagged_sublist stk stk' :
  stk' ⊆ stk → tagged_sublist stk' stk.
Proof. move => SUB ? /SUB. naive_solver. Qed.

Lemma tagged_sublist_cons stk new:
  tagged_sublist stk (new :: stk).
Proof. intros ??. setoid_rewrite elem_of_cons. naive_solver. Qed.

Lemma grant_tagged_sublist stk bor new cids stk':
  grant stk bor new cids = Some stk' → tagged_sublist stk' (new :: stk).
Proof.
  rewrite /grant.
  case find_granting as [[n pm]|]; [|done].
  cbn -[item_insert_dedup]. destruct new.(perm). (* TODO: duplicated proofs *)
  - case access1 as [[n1 stk1]|] eqn:Eq1; [|done]. cbn -[item_insert_dedup].
    intros. simplify_eq. apply access1_tagged_sublist in Eq1. etrans.
    + apply subseteq_tagged_sublist, item_insert_dedup_subseteq.
    + by apply (tagged_sublist_app [new] [new]).
  - case find_first_write_incompatible as [n1|]; [|done].
    simpl. intros. simplify_eq.
    by apply subseteq_tagged_sublist, item_insert_dedup_subseteq.
  - case access1 as [[n1 stk1]|] eqn:Eq1; [|done]. cbn -[item_insert_dedup].
    intros. simplify_eq. apply access1_tagged_sublist in Eq1. etrans.
    + apply subseteq_tagged_sublist, item_insert_dedup_subseteq.
    + by apply (tagged_sublist_app [new] [new]).
  - case access1 as [[n1 stk1]|] eqn:Eq1; [|done]. cbn -[item_insert_dedup].
    intros. simplify_eq. apply access1_tagged_sublist in Eq1. etrans.
    + apply subseteq_tagged_sublist, item_insert_dedup_subseteq.
    + by apply (tagged_sublist_app [new] [new]).
Qed.

Lemma for_each_grant α cids l n tg new α' :
  for_each α l n false (λ stk, grant stk tg new cids) = Some α' →
  ∀ (l: loc) stk', α' !! l = Some stk' → ∃ stk, α !! l = Some stk ∧
    tagged_sublist stk' (new :: stk) ∧ (stk ≠ [] → stk' ≠ []).
Proof.
  intros EQ. destruct (for_each_lookup  _ _ _ _ _ EQ) as [EQ1 [EQ2 EQ3]].
  intros l1 stk1 Eq1.
  case (decide (l1.1 = l.1)) => [Eql|NEql];
    [case (decide (l.2 ≤ l1.2 < l.2 + n)) => [[Le Lt]|NIN]|].
  - have Eql2: l1 = l +ₗ Z.of_nat (Z.to_nat (l1.2 - l.2)). {
      destruct l, l1. move : Eql Le => /= -> ?.
      rewrite /shift_loc /= Z2Nat.id; [|lia]. f_equal. lia. }
    destruct (EQ2 (Z.to_nat (l1.2 - l.2)) stk1)
      as [stk [Eq Eq0]];
      [rewrite -(Nat2Z.id n) -Z2Nat.inj_lt; lia|by rewrite -Eql2|].
    exists stk. split; [by rewrite Eql2|]. simplify_eq.
    split; [by eapply grant_tagged_sublist|by eapply grant_non_empty].
  - exists stk1. split; last split; [..|by apply tagged_sublist_cons|done].
    rewrite -EQ3; [done|]. intros i Lt Eq. apply NIN. rewrite Eq /=. lia.
  - exists stk1. split; last split; [..|by apply tagged_sublist_cons|done].
    rewrite -EQ3; [done|]. intros i Lt Eq. apply NEql. by rewrite Eq.
Qed.

Lemma for_each_grant_non_empty α cids l n tg new α' :
  for_each α l n false (λ stk, grant stk tg new cids) = Some α' →
  wf_non_empty α → wf_non_empty α'.
Proof.
  move => /for_each_grant EQ1 WF ?? /EQ1 [? [? [? NE]]]. by eapply NE, WF.
Qed.

Definition tag_fresh_stack (t: tag) (stk: stack) :=
  match t with
  | Tagged _ => ∀ it, it ∈ stk → it.(tg) ≠ t
  | _ => True
  end.

Lemma tag_fresh_stack_app t stk1 stk2 :
  tag_fresh_stack t (stk1 ++ stk2) ↔ tag_fresh_stack t stk1 ∧ tag_fresh_stack t stk2.
Proof.
  rewrite /tag_fresh_stack.
  destruct t; [|naive_solver].
  setoid_rewrite elem_of_app. naive_solver.
Qed.

Lemma replace_check'_tag_fresh_stack cids acc stk stk' new :
  replace_check' cids acc stk = Some stk' →
  tag_fresh_stack new (acc ++ stk) → tag_fresh_stack new stk'.
Proof.
  revert acc stk'.
  induction stk as [|it stk IH]; intros acc stk'; simpl.
  { intros ?. simplify_eq. by rewrite app_nil_r. }
  case decide => ?; [case check_protector; [|done]|];
    [|move => /IH; by rewrite -app_assoc].
  move => RC IS. apply (IH _ _ RC). move : IS. clear -RC.
  rewrite /tag_fresh_stack. destruct new; [|done].
  apply replace_check'_tagged_sublist in RC.
  do 2 (setoid_rewrite elem_of_app). setoid_rewrite elem_of_cons at 1.
  intros IS it1 [[|Eq%list_elem_of_singleton]|]; [naive_solver| |naive_solver].
  rewrite Eq /=. naive_solver.
Qed.

Lemma replace_check_tag_fresh_stack cids stk stk' new :
  replace_check cids stk = Some stk' →
  tag_fresh_stack new stk → tag_fresh_stack new stk'.
Proof. by eapply replace_check'_tag_fresh_stack. Qed.

Lemma remove_check_tag_fresh_stack cids stk stk' idx new :
  remove_check cids stk idx = Some stk' →
  tag_fresh_stack new stk → tag_fresh_stack new stk'.
Proof.
  revert stk' idx.
  induction stk as [|it stk IH]; intros stk' idx; simpl.
  { destruct idx; [|done]. intros. by simplify_eq. }
  destruct idx as [|idx]; [intros; by simplify_eq|].
  case check_protector eqn:Eq; [|done].
  move => /IH IH1 IS. apply IH1. by apply (tag_fresh_stack_app _ [it]) in IS as [].
Qed.

Lemma access1_tag_fresh_stack stk kind bor cids n stk1 new :
  access1 stk kind bor cids = Some (n, stk1) →
  tag_fresh_stack new stk → tag_fresh_stack new stk1.
Proof.
  rewrite /access1. case find_granting as [gip|] eqn:Eq1; [|done].
  apply fmap_Some in Eq1 as [[i it] [[IN ?]%list_find_Some EQ]].
  subst gip; simpl.
  destruct kind.
  - case replace_check as [stk'|] eqn:Eqc ; [|done].
    simpl. intros ?. simplify_eq.
    rewrite -{1}(take_drop n stk). rewrite 2!tag_fresh_stack_app.
    intros [??]. split; [|done]. by eapply replace_check_tag_fresh_stack.
  - case find_first_write_incompatible as [?|]; [|done]. simpl.
    case remove_check as [?|] eqn:Eqc ; [|done].
    simpl. intros ?. simplify_eq.
    rewrite -{1}(take_drop n stk). rewrite 2!tag_fresh_stack_app.
    intros [??]. split; [|done]. by eapply remove_check_tag_fresh_stack.
Qed.

Lemma stack_item_tagged_NoDup_tag_fresh_cons new stk :
  tag_fresh_stack new.(tg) stk →
  stack_item_tagged_NoDup stk → stack_item_tagged_NoDup (new :: stk).
Proof.
  rewrite /tag_fresh_stack /stack_item_tagged_NoDup.
  rewrite filter_cons.
  case decide => [|//]. rewrite {1}/is_tagged fmap_cons => ?.
  destruct new.(tg); [|done].
  intros IS ND. apply NoDup_cons. split; [|done].
  move => /list_elem_of_fmap [it [Eq /list_elem_of_filter [IT IN]]].
  by apply (IS _ IN).
Qed.

Lemma item_insert_dedup_tagged_NoDup new stk n:
  tag_fresh_stack new.(tg) stk →
  stack_item_tagged_NoDup stk →
  stack_item_tagged_NoDup (item_insert_dedup stk new n).
Proof.
  intros. destruct n; simpl.
  - destruct stk.
    + apply stack_item_tagged_NoDup_singleton.
    + case decide => ?; [done|].
      by apply stack_item_tagged_NoDup_tag_fresh_cons.
  - case lookup => [?|]; case lookup => [?|].
    + case decide => ?; [done|]. case decide => ?; [done|].
      rewrite -Permutation_middle take_drop.
      by apply stack_item_tagged_NoDup_tag_fresh_cons.
    + case decide => ?; [done|]. rewrite -Permutation_middle take_drop.
      by apply stack_item_tagged_NoDup_tag_fresh_cons.
    + case decide => ?; [done|]. rewrite -Permutation_middle take_drop.
      by apply stack_item_tagged_NoDup_tag_fresh_cons.
    + rewrite -Permutation_middle take_drop.
      by apply stack_item_tagged_NoDup_tag_fresh_cons.
Qed.

Lemma grant_stack_item_tagged_NoDup stk bor new cids stk'
  (NEW: tag_fresh_stack new.(tg) stk) :
  grant stk bor new cids = Some stk' →
  stack_item_tagged_NoDup stk → stack_item_tagged_NoDup stk'.
Proof.
  rewrite /grant.
  case find_granting as [[n pm]|]; [|done].
  cbn -[item_insert_dedup]. destruct new.(perm). (* TODO: duplicated proofs *)
  - case access1 as [[n1 stk1]|] eqn:Eq1; [|done]. cbn -[item_insert_dedup].
    intros ? ND. simplify_eq.
    apply item_insert_dedup_tagged_NoDup.
    + by eapply access1_tag_fresh_stack.
    + by eapply access1_stack_item_tagged_NoDup.
  - case find_first_write_incompatible as [n1|]; [|done].
    simpl. intros ? ND. simplify_eq.
    by apply item_insert_dedup_tagged_NoDup.
  - case access1 as [[n1 stk1]|] eqn:Eq1; [|done]. cbn -[item_insert_dedup].
    intros ? ND. simplify_eq.
    apply item_insert_dedup_tagged_NoDup.
    + by eapply access1_tag_fresh_stack.
    + by eapply access1_stack_item_tagged_NoDup.
  - case access1 as [[n1 stk1]|] eqn:Eq1; [|done]. cbn -[item_insert_dedup].
    intros ? ND. simplify_eq.
    apply item_insert_dedup_tagged_NoDup.
    + by eapply access1_tag_fresh_stack.
    + by eapply access1_stack_item_tagged_NoDup.
Qed.

Definition tag_fresh t (α: stacks) l n :=
  match t with
  | Tagged _ => ∀ (i: nat) stk, (i < n)%nat → α !! (l +ₗ i) = Some stk →
              ∀ it, it ∈ stk → it.(tg) ≠ t
  | _ => True
  end.

Lemma for_each_grant_stack_item α nxtc cids nxtp l n bor new α'
  (PR: match new.(protector) with Some c => (c < nxtc)%nat | _ => True end)
  (TG2: new.(tg) <t nxtp)
  (NEW: tag_fresh new.(tg) α l n) :
  for_each α l n false (λ stk, grant stk bor new cids) = Some α' →
  wf_stacks α nxtp nxtc → wf_stacks α' nxtp nxtc.
Proof.
  intros ACC WF l' stk' Eq'.
  destruct (for_each_grant _ _ _ _ _ _ _ ACC _ _ Eq') as [stk [Eq [SUB ?]]].
  split.
  - eapply tagged_sublist_stack_item_included; [eauto|].
    move => it /elem_of_cons [-> //|] / (proj1 (WF _ _ Eq)) [Lt ?].
    split; [|done]. move : Lt. destruct it.(tg); [lia|done].
  - destruct (for_each_lookup_case _ _ _ _ _ ACC _ _ _ Eq Eq')
      as [?|[Eqf [i [Lt ?]]]].
    { subst. by apply (WF _ _ Eq). }
    eapply grant_stack_item_tagged_NoDup; eauto.
    + destruct new.(tg); [|done].
      subst l'. intros it. by apply (NEW i).
    + by apply (WF _ _ Eq).
Qed.

Lemma reborrowN_wf_stack α nxtc cids nxtp l n old new pm bar α'
  (PR: match bar with Some c => (c < nxtc)%nat | _ => True end)
  (TG2: new <t nxtp)
  (NEW: tag_fresh new α l n) :
  reborrowN α cids l n old new pm bar = Some α' →
  wf_stacks α nxtp nxtc ∧ wf_non_empty α →
  dom α ≡ dom α' ∧
  wf_stacks α' nxtp nxtc ∧ wf_non_empty α'.
Proof.
  intros RB [WF1 WF2]. split; last split.
  - eapply for_each_dom; eauto.
  - move : WF1. eapply for_each_grant_stack_item; [..|eauto]; done.
  - move : WF2. eapply for_each_grant_non_empty; [..|eauto]; done.
Qed.

Lemma unsafe_action_wf_stack
  (f: stacks → _ → _ → _ → _) α l (last fs us: nat) α' l' c' nxtp nxtc
  (P: stacks → loc → nat → Prop) :
  (∀ α l sz1 sz2, P α l (sz1 + sz2)%nat →
    P α l sz1 ∧ ∀ α',
    (∀ i:nat, (i < sz2)%nat → α' !! (l +ₗ sz1 +ₗ i) = α !! (l +ₗ sz1 +ₗ i)) →
    P α' (l +ₗ sz1) sz2) →
  (∀ α1 α2 l n b, f α1 l n b = Some α2 →
    ∀ l', (∀ (i : nat), (i < n)%nat → l' ≠ l +ₗ i) → α2 !! l' = α1 !! l') →
  (∀ α1 α2 l n b,
    P α1 l n →
    f α1 l n b = Some α2 →
    wf_stacks α1 nxtp nxtc ∧ wf_non_empty α1 →
    dom α1 ≡ dom α2 ∧
    wf_stacks α2 nxtp nxtc ∧ wf_non_empty α2) →
  P α (l +ₗ last) (l' - last)%nat →
  unsafe_action f α l last fs us = Some (α', (l', c')) →
  wf_stacks α nxtp nxtc ∧ wf_non_empty α →
  dom α ≡ dom α' ∧
  wf_stacks α' nxtp nxtc ∧ wf_non_empty α'.
Proof.
  intros HP Hf0 Hf. rewrite /unsafe_action.
  case f as [α1|] eqn:Eq1; [simpl|done].
  case (f α1) as [α2|] eqn:Eq2; [simpl|done]. intros HP1 Eq WF. simplify_eq.
  rewrite (_: (last + fs + us - last)%nat = (fs + us)%nat) in HP1; [|lia].
  destruct (HP _ _ _ _ HP1) as [HP2 HP3].
  destruct (Hf _ _ _ _ _ HP2 Eq1) as (EqD1 & ?); [done|].
  have HP4: P α1 (l +ₗ last +ₗ fs) us.
  { apply HP3. intros i Lt. apply (Hf0 _ _ _ _ _ Eq1).
    intros j Ltj. rewrite shift_loc_assoc. intros ?%shift_loc_inj. lia. }
  move : HP4. rewrite shift_loc_assoc -Nat2Z.inj_add => HP4.
  destruct (Hf _ _ _ _ _ HP4 Eq2) as [EqD2 ?]; [done|].
  split; [|done]. by rewrite EqD1 EqD2.
Qed.


Lemma unsafe_action_offsets {A}
  (f: A → _ → nat → _ → _) a l (last fsz usz: nat) a' last' cur_dist' :
  unsafe_action f a l last fsz usz = Some (a', (last', cur_dist')) →
  (last' = last + fsz + usz ∧ cur_dist' = O)%nat.
Proof.
  rewrite /unsafe_action. do 2 (case f => ?; [simpl|done]).
  intros. by simplify_eq.
Qed.

Lemma visit_freeze_sensitive'_offsets {A}
  l (f: A → _ → nat → _ → _) a (last cur_dist: nat) T a' last' cur_dist' :
  let HA (oalc: option (A * (nat * nat))) l1 c1 T1 a2 l2 c2 :=
    (oalc = Some (a2, (l2, c2)) →
      (l1 ≤ l2 ∧ l2 + c2 = l1 + c1 + tsize T1)%nat) in
  HA (visit_freeze_sensitive' l f a last cur_dist T)
     last cur_dist T a' last' cur_dist'.
Proof.
  intros HA.
  apply (visit_freeze_sensitive'_elim
    (* general goal P *)
    (λ _ _ _ l1 c1 T1 oalc, ∀ a2 l2 c2, HA oalc l1 c1 T1 a2 l2 c2)
    (λ _ _ _ _ _ _ _ l1 c1 Ts oalc, ∀ a2 l2 c2,
      HA oalc l1 c1 (Product Ts) a2 l2 c2)); rewrite /HA.
  - intros. simplify_eq. simpl. lia.
  - intros. simplify_eq. simpl. lia.
  - clear. intros ????????? [??]%unsafe_action_offsets. subst. simpl. lia.
  - clear. intros ?????????. case is_freeze.
    + intros. simplify_eq. lia.
    + intros [??]%unsafe_action_offsets. subst. lia.
  - clear. intros ?????? IH ???.
    case is_freeze; [intros; simplify_eq; lia|by move => /IH].
  - clear. intros ?????????. case is_freeze.
    + intros. simplify_eq. lia.
    + intros [??]%unsafe_action_offsets. subst. lia.
  - naive_solver.
  - clear. intros l f a1 l1 c1 Ts a2 l2 c2 T Ts' IH1 IH2 a4 l4 c4.
    case visit_freeze_sensitive' as [[a3 [l3 c3]]|] eqn:Eq3; [|done].
    cbn -[tsize].
    destruct (IH2 a3 l3 c3) as [Le3 EqO3]; [done|].
    intros Eq4. destruct (IH1 (a3, (l3, c3)) a4 l4 c4 Eq4) as [Le4 EqO4].
    clear -Le3 EqO3 Le4 EqO4. simpl in Le4. rewrite EqO4. cbn -[tsize].
    rewrite EqO3 tsize_product_cons. lia.
Qed.

Lemma unsafe_action_stacks_unchanged
  (f: stacks → _ → nat → _ → _) α l (last fsz usz: nat) α' ln cn
  (HF: ∀ α1 α2 l n b, f α1 l n b = Some α2 →
      ∀ l', (∀ (i : nat), (i < n)%nat → l' ≠ l +ₗ i) → α2 !! l' = α1 !! l') :
  unsafe_action f α l last fsz usz = Some (α', (ln, cn)) →
  (last ≤ ln)%nat ∧
  (∀ l', (∀ (i : nat), (last ≤ i < ln)%nat → l' ≠ l +ₗ i) → α' !! l' = α !! l').
Proof.
  rewrite /unsafe_action.
  case f as [α1|] eqn:Eqf1; [simpl|done]. case (f α1) eqn:Eqf2; [simpl|done].
  intros ?. simplify_eq. split; [lia|].
  intros ? NEQ.
  rewrite (HF _ _ _ _ _ Eqf2); last first.
  { intros i Lt.
    rewrite shift_loc_assoc -Nat2Z.inj_add. apply NEQ. lia. }
  rewrite (HF _ _ _ _ _ Eqf1) //.
  intros ??. rewrite shift_loc_assoc -Nat2Z.inj_add. apply NEQ. lia.
Qed.

Lemma visit_freeze_sensitive'_stacks_unchanged l (f: stacks → _ → _ → _ → _)
  α α' last cur T l' c' :
  let HF (f: stacks → loc → nat → bool → option stacks) :=
    (∀ α1 α2 l n b, f α1 l n b = Some α2 →
      ∀ l', (∀ (i : nat), (i < n)%nat → l' ≠ l +ₗ i) → α2 !! l' = α1 !! l') in
  let UC α1 α2 (l: loc) (lo ln: nat) :=
    (lo ≤ ln)%nat ∧
    (∀ l', (∀ (i : nat), (lo ≤ i < ln)%nat → l' ≠ l +ₗ i) → α2 !! l' = α1 !! l') in
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
  - naive_solver.
  - naive_solver.
  - (* Unsafe case *)
    clear. intros ?? α l1 c1 ? α2 l2 c2 HF0.
    eapply unsafe_action_stacks_unchanged; eauto.
  - (* Union case *)
    intros ???????? HF0. case is_freeze; [by intros; simplify_eq|].
    intros UN. eapply unsafe_action_stacks_unchanged; eauto.
  - clear. intros ?????? IH ??? HF0.
    case is_freeze; [by intros ?; simplify_eq|]. intros VS.
    eapply (IH _ _ _ HF0); eauto.
  - (* Sum case *)
    intros ???????? HF0. case is_freeze; [by intros; simplify_eq|].
    intros UN. eapply unsafe_action_stacks_unchanged; eauto.
  - naive_solver.
  - (* Product case *)
    clear. intros l f a ???????? IH1 IH2 α' l' c' HF0.
    case visit_freeze_sensitive' as [alc|] eqn:Eqa; [|done].
    intros VS. destruct alc as [a1 [l1 c1]]. simpl in VS.
    destruct (IH2 a1 l1 c1 HF0 eq_refl) as [Le2 IH2'].
    destruct (IH1 (a1, (l1,c1)) α' l' c') as [Le1 IH1'];
      [done..|simpl in Le1; split]; [lia|].
    intros ? NC. simpl in IH1', IH2'. rewrite IH1'; [rewrite IH2' //|].
    + intros ??. apply NC. lia.
    + intros ??. apply NC. lia.
Qed.

Lemma visit_freeze_sensitive_stacks_unchanged l (f: stacks → _ → _ → _ → _)
  α α' T :
  (∀ α1 α2 l n b, f α1 l n b = Some α2 →
      ∀ l', (∀ (i : nat), (i < n)%nat → l' ≠ l +ₗ i) → α2 !! l' = α1 !! l') →
  visit_freeze_sensitive l T f α = Some α' →
  ∀ l', (∀ (i : nat), (i < tsize T)%nat → l' ≠ l +ₗ i) → α' !! l' = α !! l'.
Proof.
  intros HF.
  rewrite /visit_freeze_sensitive.
  case visit_freeze_sensitive' as [[α1 [l1 c1]]|] eqn:Eq; [|done].
  intros Eqf.
  have Eq' := Eq.
  apply visit_freeze_sensitive'_offsets in Eq' as [_ Eq'].
  rewrite 2!Nat.add_0_l in Eq'.
  apply visit_freeze_sensitive'_stacks_unchanged in Eq as [_ EQ]; [|done].
  specialize (HF _ _ _ _ _ Eqf).
  intros l' NEq. rewrite HF; last first.
  { intros i Lt. rewrite shift_loc_assoc -Nat2Z.inj_add.
    apply NEq. rewrite -Eq'. lia. }
  rewrite EQ //.
  intros i [_ Lti]. apply NEq. rewrite -Eq'. lia.
Qed.

Lemma visit_freeze_sensitive'_wf_stack l (f: stacks → _ → _ → _ → _)
  α α' last cur T l' c' nxtp nxtc (P: stacks → loc → nat → Prop) :
  let Hα α1 α2 l n :=
    (P α1 l n → wf_stacks α1 nxtp nxtc ∧ wf_non_empty α1 →
      dom α1 ≡ dom α2 ∧
      wf_stacks α2 nxtp nxtc ∧ wf_non_empty α2) in
  let HP :=
    (∀ α l sz1 sz2, P α l (sz1 + sz2)%nat → P α l sz1 ∧ ∀ α',
    (∀ i:nat, (i < sz2)%nat → α' !! (l +ₗ sz1 +ₗ i) = α !! (l +ₗ sz1 +ₗ i)) →
    P α' (l +ₗ sz1) sz2) in
  let HF0 (f: stacks → loc → nat → bool → option stacks) :=
    (∀ α1 α2 l n b, f α1 l n b = Some α2 →
      ∀ l', (∀ (i : nat), (i < n)%nat → l' ≠ l +ₗ i) → α2 !! l' = α1 !! l') in
  let HF f := (∀ α1 α2 l n b, f α1 l n b = Some α2 → Hα α1 α2 l n) in
  HP →
  visit_freeze_sensitive' l f α last cur T = Some (α', (l', c')) →
  (last ≤ l')%nat ∧ (HF0 f → HF f → Hα α α' (l +ₗ last) (l' - last)%nat).
Proof.
  intros Hα HP HF0 HF HP1.
  apply (visit_freeze_sensitive'_elim
    (* general goal P *)
    (λ l f α l1 c1 T oalc, ∀ α' l' c',
      oalc = Some (α', (l', c')) →
        (l1 ≤ l')%nat ∧ (HF0 f → HF f → Hα α α' (l +ₗ l1) (l' - l1)%nat))
    (λ l f _ _ _ Ts1 α l1 c1 Ts2 oalc, ∀ α' l' c',
      oalc = Some (α', (l', c')) →
        (l1 ≤ l')%nat ∧ (HF0 f → HF f → Hα α α' (l +ₗ l1) (l' - l1)%nat)));
    rewrite /HF /HF0 /Hα.
  - naive_solver.
  - naive_solver.
  - (* Unsafe case *)
    clear -HP1.
    intros ????????? UN. split.
    + apply unsafe_action_offsets  in UN as [??]. lia.
    + intros HF0 HF HP2. eapply unsafe_action_wf_stack; eauto.
  - (* Union case *)
    clear -HP1. intros ?????????. case is_freeze; [by intros; simplify_eq|].
    intros UN. split.
    + apply unsafe_action_offsets  in UN as [??]. lia.
    + intros HF0 HF HP2. eapply unsafe_action_wf_stack; eauto.
  - clear -HP1. intros ?????? IH ???.
    case is_freeze; [by intros ?; simplify_eq|]. intros VS. eapply IH; eauto.
  - (* Sum case *)
    clear -HP1. intros ?????????. case is_freeze; [by intros; simplify_eq|].
    intros UN. split.
    + apply unsafe_action_offsets  in UN as [??]. lia.
    + intros HF0 HF HP2. eapply unsafe_action_wf_stack; eauto.
  - naive_solver.
  - (* Product case *)
    clear -HP1. intros l f α1 l1 c1 Ts1 α0 l0 c0 T Ts IH1 IH2 α' l' c'.
    case visit_freeze_sensitive' as [alc|] eqn:Eqa; [|done].
    intros VS. simpl in VS. destruct alc as [α2 [l2 c2]].
    destruct (visit_freeze_sensitive'_offsets _ _ _ _ _ _ _ _ _ Eqa) as [Le2 Eq2].
    specialize (IH2 α2 l2 c2 eq_refl) as [_ IH2].
    specialize (IH1 (α2, (l2,c2)) _ _ _ VS) as [Le1 IH1]. simpl in Le1.
    split. { lia. }
    intros HF0 HF HP2 WF.
    destruct (visit_freeze_sensitive'_stacks_unchanged _ _ _ _ _ _ _ _ _ HF0 Eqa)
      as [_ NC].
    destruct (HP1 α0 (l +ₗ l0) (l2 - l0)%nat (l' - l2)%nat) as [HP3 HP4].
    { rewrite (_: (l2  - l0 + (l' - l2))%nat = l' - l0)%nat //. lia. }
    specialize (IH2 HF0 HF HP3 WF) as [EqD WF1]. rewrite EqD.
    specialize (IH1 HF0 HF). apply IH1; [|done].
    simpl.
    rewrite (_: (l +ₗ l0 +ₗ (l2 - l0)%nat) = l +ₗ l2) in HP4; last first.
    { rewrite shift_loc_assoc. f_equal. lia. }
    apply HP4. intros i Lt. apply NC.
    intros j Ltj. rewrite shift_loc_assoc -Nat2Z.inj_add.
    intros ?%shift_loc_inj. lia.
Qed.

Lemma visit_freeze_sensitive_wf_stack l T (f: stacks → _ → _ → _ → _)
  nxtp nxtc α α' (P: stacks → loc → nat → Prop) :
  let HP :=
    (∀ α l sz1 sz2, P α l (sz1 + sz2)%nat → P α l sz1 ∧ ∀ α',
    (∀ i:nat, (i < sz2)%nat → α' !! (l +ₗ sz1 +ₗ i) = α !! (l +ₗ sz1 +ₗ i)) →
    P α' (l +ₗ sz1) sz2) in
  let HF0 (f: stacks → loc → nat → bool → option stacks) :=
    (∀ α1 α2 l n b, f α1 l n b = Some α2 →
      ∀ l', (∀ (i : nat), (i < n)%nat → l' ≠ l +ₗ i) → α2 !! l' = α1 !! l') in
  HP → HF0 f →
  (∀ α1 α2 l n b, f α1 l n b = Some α2 → P α1 l n →
    wf_stacks α1 nxtp nxtc ∧ wf_non_empty α1 →
    dom α1 ≡ dom α2 ∧
   wf_stacks α2 nxtp nxtc ∧ wf_non_empty α2) →
  visit_freeze_sensitive l T f α = Some α' →
  P α l (tsize T) →
  wf_stacks α nxtp nxtc ∧ wf_non_empty α →
  dom α ≡ dom α' ∧
  wf_stacks α' nxtp nxtc ∧ wf_non_empty α'.
Proof.
  intros HP HF0 HP1 HF1 Hf. rewrite /visit_freeze_sensitive.
  case visit_freeze_sensitive' as [[α1 [last cur]]|] eqn:Eq; [|done].
  move => Eqf HP2 WF.
  destruct (visit_freeze_sensitive'_wf_stack _ _ _ _ _ _ _ _ _ nxtp nxtc P HP1 Eq)
    as [Le WF'].
  specialize (WF' HF1 Hf). rewrite shift_loc_0_nat Nat.sub_0_r in WF'.
  destruct (visit_freeze_sensitive'_offsets _ _ _ _ _ _ _ _ _ Eq) as [_ Eqs].
  simpl in Eqs. rewrite -Eqs in HP2.
  specialize (HP1 _ _ _ _ HP2) as [HP3 HP4].
  specialize (WF' HP3 WF) as [EqD WF1]. rewrite EqD.
  eapply Hf; eauto.
  apply HP4. intros i Lt.
  apply (visit_freeze_sensitive'_stacks_unchanged _ _ _ _ _ _ _ _ _ HF1 Eq).
  intros j Ltj. rewrite shift_loc_assoc -Nat2Z.inj_add.
    intros ?%shift_loc_inj. lia.
Qed.

Lemma tag_fresh_split α l sz1 sz2 new :
  tag_fresh new α l (sz1 + sz2) → tag_fresh new α l sz1 ∧
  (∀ α', (∀ i : nat, (i < sz2)%nat → α' !! (l +ₗ sz1 +ₗ i) = α !! (l +ₗ sz1 +ₗ i))
         → tag_fresh new α' (l +ₗ sz1) sz2).
Proof.
  rewrite /tag_fresh. destruct new; [|done].
  intros TF. split.
  - intros ???. apply TF. lia.
  - intros ? NC ???. rewrite NC //. rewrite shift_loc_assoc -Nat2Z.inj_add.
    apply TF. lia.
Qed.

Lemma reborrow_wf_stack α nxtc cids nxtp l old T kind new bar α'
  (TG2: new <t nxtp)
  (BAR : match bar with Some c => (c < nxtc)%nat | _ => True end)
  (NEW: tag_fresh new α l (tsize T)) :
  reborrow α cids l old T kind new bar = Some α' →
  wf_stacks α nxtp nxtc ∧ wf_non_empty α →
  dom α ≡ dom α' ∧
  wf_stacks α' nxtp nxtc ∧ wf_non_empty α'.
Proof.
  rewrite /reborrow. destruct kind as [[]| |mutbl].
  - by eapply reborrowN_wf_stack; eauto.
  - by eapply reborrowN_wf_stack; eauto.
  - intros VS. revert VS NEW. apply visit_freeze_sensitive_wf_stack.
    + intros. by apply tag_fresh_split.
    + intros ?????. apply for_each_lookup.
    + intros ???????. by eapply reborrowN_wf_stack.
  - destruct mutbl.
    + by eapply reborrowN_wf_stack; eauto.
    + intros VS. revert VS NEW. apply visit_freeze_sensitive_wf_stack.
      * intros. by apply tag_fresh_split.
      * intros ?????. apply for_each_lookup.
      * intros ???????. by eapply reborrowN_wf_stack.
Qed.

Lemma retag_ref_wf_stack (*h*) α nxtc cids nxtp l old T kind bar bor' α' nxtp'
  (BAR : match bar with Some c => (c < nxtc)%nat | _ => True end) :
  retag_ref α cids nxtp l old T kind bar = Some (bor', α', nxtp') →
  (*wf_mem_tag h nxtp →*)
  wf_stacks α nxtp nxtc → wf_non_empty α →
  (*wf_mem_tag h nxtp' ∧*)
  dom α ≡ dom α' ∧
  wf_stacks α' nxtp' nxtc ∧ wf_non_empty α'.
Proof.
  intros RE (*WF1*) WF2 WF3. (* split.*)
  (*{ move => x' l' t' /WF1. apply retag_ref_nxtp_mono in RE. lia. }*)
  revert RE WF2 WF3.
  rewrite /retag_ref. case tsize eqn:Eq; [by intros; simplify_eq|].
  case reborrow as [α1|] eqn:Eq1; [simpl|done].
  intros ?. simplify_eq. intros WF2 WF3.
  eapply reborrow_wf_stack; eauto; [..|].
  - destruct kind; simpl; [lia..|done].
  - rewrite /tag_fresh. destruct kind; [..|done];
    intros i stk Lt Eqst it IN;
      destruct (proj1 (WF2 _ _ Eqst) _ IN);
      destruct it.(tg); auto; intros ?; simplify_eq; lia.
  - split; [|done]. eapply wf_stack_item_mono; [..|done|exact WF2]. by lia.
Qed.

Definition borrow_barrier_Some nxtc kind c : Prop :=
  match kind with FnEntry => (c < nxtc)%nat | _ => True end.

Lemma retag_wf h α nxtp nxtc c cids l otag rkind pk T ntag α' nxtp' :
  c ∈ cids →
  retag α nxtp cids c l otag rkind pk T = Some (ntag, α', nxtp') →
  state_wf (mkState h α cids nxtp nxtc) → state_wf (mkState h α' cids nxtp' nxtc).
Proof.
  intros Hc RT WF.
  have ?: borrow_barrier_Some nxtc rkind c.
  { destruct rkind; [|done..]. apply WF. apply Hc. }
  revert RT.
  destruct pk as [[]|[]|]; rewrite /retag /=;
    [| |destruct rkind; simpl; try by (intros; simplify_eq)..|];
     (case retag_ref as [[[new α1] nxtp1]|] eqn:Eq1; [simpl|done]);
    intros ?; simplify_eq;
    destruct WF;
    (eapply retag_ref_wf_stack in Eq1; eauto);
    [|by destruct rkind| |by destruct rkind|..];
    destruct Eq1 as ((*WF1 & *) Eq1 & ? & ?);
    (split; [by rewrite -Eq1|done..]).
Qed.

Lemma retag_step_wf σ σ' e e' l ot nt pk T kind c efs :
  mem_expr_step σ.(shp) e (RetagEvt l ot nt pk T kind c) σ'.(shp) e' efs →
  bor_step σ.(sst) σ.(scs) σ.(snp) σ.(snc)
           (RetagEvt l ot nt pk T kind c)
           σ'.(sst) σ'.(scs) σ'.(snp) σ'.(snc) →
  state_wf σ → state_wf σ'.
Proof.
  destruct σ as [h α cids nxtp nxtc].
  destruct σ' as [h' α' cids' nxtp' nxtc']. simpl.
  intros BS IS WF.
  inversion BS. clear BS. simplify_eq.
  inversion IS. clear IS. simplify_eq.
  by eapply retag_wf.
Qed.

(** SysCall step *)
(* Lemma syscall_step_wf σ σ' e e' id efs h0 :
  mem_expr_step FNs e σ.(shp) (SysCallEvt id) e' h0 efs →
  bor_step h0 σ.(sst) σ.(snc) σ.(snp)
                    (SysCallEvt id)
                  σ'.(shp) σ'.(sst) σ'.(snc) σ'.(snp) →
  Wf σ → Wf σ'.
Proof.
  destruct σ as [h α nxtp nxtc]. destruct σ' as [h' α' nxtc' nxtp']. simpl.
  intros BS IS WF.
  inversion BS; clear BS; simplify_eq;
  inversion IS; clear IS; simplify_eq; apply WF.
Qed. *)

Lemma base_step_wf P σ σ' e e' efs :
  base_step P e σ e' σ' efs → state_wf σ → state_wf σ'.
Proof.
  intros HS WF. inversion HS; [by subst|]. simplify_eq.
  rename select event into ev. destruct ev.
  - eapply alloc_step_wf; eauto.
  - eapply dealloc_step_wf; eauto.
  - eapply copy_step_wf; eauto.
  - eapply failed_copy_step_wf; eauto.
  - eapply write_step_wf; eauto.
  - eapply initcall_step_wf; eauto.
  - eapply endcall_step_wf; eauto.
  - eapply retag_step_wf; eauto.
  - rename select (mem_expr_step _ _ _ _ _ _) into Hstep. inversion Hstep.
  (* - eapply syscall_step_wf; eauto. *)
Qed.
