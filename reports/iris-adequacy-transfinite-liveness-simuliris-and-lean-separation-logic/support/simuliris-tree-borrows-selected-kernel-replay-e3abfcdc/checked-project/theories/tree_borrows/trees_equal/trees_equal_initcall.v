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
From simuliris.tree_borrows.trees_equal Require Import trees_equal_base random_lemmas.


Section call_set.

  Lemma call_is_active_mono C1 C2 cid :
    C1 ⊆ C2 →
    call_is_active cid C1 →
    call_is_active cid C2.
  Proof.
    rewrite /call_is_active. set_solver.
  Qed.

  Lemma protector_is_active_mono C1 C2 prot :
    C1 ⊆ C2 →
    protector_is_active prot C1 →
    protector_is_active prot C2.
  Proof.
    intros Hss (c&Hc1&Hc2). eexists; split; by eauto using call_is_active_mono.
  Qed.

  Lemma pseudo_conflicted_mono C1 C2 tr tg off rc :
    C1 ⊆ C2 →
    pseudo_conflicted C1 tr tg off rc →
    pseudo_conflicted C2 tr tg off rc.
  Proof.
    induction 2.
    + econstructor 1.
    + econstructor 2; by eauto using protector_is_active_mono.
  Qed.

  Lemma protector_not_active_extend
    {p c C}
    (Hwf : ∀ c' : nat, protector_is_for_call c' p → (c' < c)%nat)
    (NoProt : ¬ protector_is_active p C)
    : ¬ protector_is_active p (C ∪ {[ c ]}).
  Proof.
    intros (cc&Hcc&[Hact|<-%elem_of_singleton]%elem_of_union).
    1: eapply NoProt; by eexists.
    apply Hwf in Hcc. lia.
  Qed.

  Lemma pseudo_disabled_mono C1 nxtc tr1 tg l p1 cid :
    pseudo_disabled C1 tr1 tg l p1 cid →
    pseudo_disabled (C1 ∪ {[ nxtc ]}) tr1 tg l p1 cid.
  Proof.
    induction 1 as [|???????? HH]. 1: by econstructor 1.
    econstructor 2. 1,2,4,5: done.
    1: eapply protector_is_active_mono; last done; set_solver.
    done.
  Qed.

  Lemma is_disabled_mono C1 nxtc tr1 tg l p1 cid :
    is_disabled C1 tr1 tg l p1 cid →
    is_disabled (C1 ∪ {[ nxtc ]}) tr1 tg l p1 cid.
  Proof.
    induction 1 as [|]. 1: by econstructor 1.
    econstructor 2. eapply pseudo_disabled_mono. done.
  Qed.

  Lemma disabled_in_practice_mono C1 nxtc tr1 tg tg2 l:
    disabled_in_practice C1 tr1 tg tg2 l →
    disabled_in_practice (C1 ∪ {[ nxtc ]}) tr1 tg tg2 l.
  Proof.
    induction 1. econstructor. 1-2: done.
    eapply is_disabled_mono. done.
  Qed.

  Lemma disabled_tag_at_mono C1 nxtc tr1 tg l:
    disabled_tag_at C1 tr1 tg l →
    disabled_tag_at (C1 ∪ {[ nxtc ]}) tr1 tg l.
  Proof.
    intros (x&Hx). exists x. by eapply disabled_in_practice_mono.
  Qed.

  Lemma disabled_tag_mono C1 nxtc trs nxtp tg l :
    disabled_tag C1 trs nxtp tg l →
    disabled_tag (C1 ∪ {[ nxtc ]}) trs nxtp tg l.
  Proof.
    intros (H1&H2). split; first done.
    destruct (trs !! l.1); last done.
    destruct H2 as [H3|H4]. 2: by right.
    left. eapply disabled_tag_at_mono. done.
  Qed.

  Lemma perm_eq_up_to_C_mono (C1 : gset nat) (nxtc : nat)
    tr1 tr2 tg l cid lp1 lp2 {d nxtp} :
    (∀ cc, protector_is_for_call cc cid → (cc < nxtc)%nat) →
    tree_items_compat_nexts tr1 nxtp nxtc →
    tree_items_compat_nexts tr2 nxtp nxtc →
    wf_tree tr1 →
    wf_tree tr2 →
    perm_eq_up_to_C C1 tr1 tr2 tg l cid d lp1 lp2 →
    perm_eq_up_to_C (C1 ∪ {[ nxtc ]}) tr1 tr2 tg l cid d lp1 lp2.
  Proof.
    intros Hwf Hwf_all1 Hwf_all2 Hwf_tr1 Hwf_tr2.
    induction 1 as [| |??? H|?? H1 H2|??? H1 H2 ?| |p1 p2 ini Hd].
    1: by econstructor.
    1: econstructor; try done. 1: eapply protector_is_active_mono; last done; set_solver.
    1-2: eapply pseudo_conflicted_mono; last done; set_solver.
    - econstructor 3; try done.
      apply protector_not_active_extend; assumption.
    - econstructor 4. all: eapply pseudo_disabled_mono; last done; done.
    - econstructor 5; try done.
      all: eapply disabled_in_practice_mono; last done.
    - econstructor 6; done.
    - econstructor 7. destruct d; inversion Hd as [x1 Hp|]; simplify_eq.
      all: econstructor.
      2,4: eapply protector_is_active_mono; last done; set_solver.
      all: eapply protector_not_active_extend; done.
  Qed.

  Lemma loc_eq_up_to_C_mono C1 d tr1 tr2 tg it1 it2 nxtc nxtp l :
    item_wf it1 nxtp nxtc →
    tree_items_compat_nexts tr1 nxtp nxtc →
    tree_items_compat_nexts tr2 nxtp nxtc →
    wf_tree tr1 →
    wf_tree tr2 →
    loc_eq_up_to_C C1 tr1 tr2 tg d it1 it2 l →
    loc_eq_up_to_C (C1 ∪ {[ nxtc ]}) tr1 tr2 tg d it1 it2 l.
  Proof.
    intros Hwf1 Hwf_all1 Hwf_all2 Hwf_tr1 Hwf_tr2.
    induction 1; econstructor; try done.
    eapply perm_eq_up_to_C_mono; last done.
    1: apply Hwf1.
    all: eassumption.
  Qed.

  Lemma item_eq_up_to_C_mono C1 d tr1 tr2 tg it1 it2 nxtc nxtp :
    item_wf it1 nxtp nxtc →
    tree_items_compat_nexts tr1 nxtp nxtc →
    tree_items_compat_nexts tr2 nxtp nxtc →
    wf_tree tr1 →
    wf_tree tr2 →
    item_eq_up_to_C C1 tr1 tr2 tg d it1 it2 →
    item_eq_up_to_C (C1 ∪ {[ nxtc ]}) tr1 tr2 tg d it1 it2.
  Proof.
    intros Hss Hwf_all1 Hwf_all2 Hwf_tr1 Hwf_tr2 H1 l.
    specialize (H1 l). by eapply loc_eq_up_to_C_mono.
  Qed.

  Lemma tree_equal_mono C1 d tr1 tr2 nxtc nxtp :
    tree_items_compat_nexts tr1 nxtp nxtc →
    tree_items_compat_nexts tr2 nxtp nxtc →
    wf_tree tr1 →
    wf_tree tr2 →
    tree_equal C1 d tr1 tr2 →
    tree_equal (C1 ∪ {[ nxtc ]}) d tr1 tr2.
  Proof.
    intros Hss Hss2 Hwf_tr1 Hwf_tr2 (H1&H2&H3). do 2 (split; first done).
    intros tg (it1&it2&H4&H5&H6)%H3.
    exists it1, it2. split_and!; try done.
    eapply item_eq_up_to_C_mono; try done.
    setoid_rewrite every_node_eqv_universal in Hss.
    apply Hss. eapply tree_lookup_to_exists_node.
    erewrite <-tree_lookup_correct_tag in H4; done.
  Qed.

  Lemma trees_equal_mono C1 d trs1 trs2 nxtc nxtp :
    trees_compat_nexts trs1 nxtp nxtc →
    trees_compat_nexts trs2 nxtp nxtc →
    wf_trees trs1 →
    wf_trees trs2 ->
    trees_equal C1 d trs1 trs2 →
    trees_equal (C1 ∪ {[ nxtc ]}) d trs1 trs2.
  Proof.
    intros Hss Hss2 Hwf_trs1 Hwf_trs2 Heq blk. specialize (Heq blk). inversion Heq; simplify_eq.
    all: econstructor; try done.
    eapply tree_equal_mono; try done.
    + eapply Hss. done.
    + eapply Hss2. done.
    + eapply Hwf_trs1. done.
    + eapply Hwf_trs2. done.
  Qed. 

End call_set.