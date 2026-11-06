From iris.prelude Require Import prelude options.
From stdpp Require Export gmap.
From simuliris.tree_borrows Require Import defs lang_base lang notation bor_semantics tree tree_lemmas bor_lemmas steps_preserve tactics class_instances.
From simuliris.tree_borrows.read_read_reorder Require Import low_level equivalence_def.

Definition source (x1 x2 : string) l1 tg1 sz1 l2 tg2 sz2 erest : expr :=
  let: x1 := Copy (Place l1 tg1 sz1) in
  let: x2 := Copy (Place l2 tg2 sz2) in
  erest.

Definition target (x1 x2 : string) l1 tg1 sz1 l2 tg2 sz2 erest : expr :=
  let: x2 := Copy (Place l2 tg2 sz2) in
  let: x1 := Copy (Place l1 tg1 sz1) in
  erest.


Ltac solve_sub_redexes_are_values :=
  let K := fresh "K" in
  let e' := fresh "e'" in
  let Heq := fresh "Heq" in
  let Hv := fresh "Hv" in
  let IH := fresh "IH" in
  let Ki := fresh "Ki" in
  let Ki' := fresh "Ki'" in
  intros K e' Heq Hv;
  destruct K as [ | Ki K]; first (done);
  exfalso; induction K as [ | Ki' K IH] in e', Ki, Hv, Heq |-*;
  [destruct Ki; inversion Heq; subst; cbn in *;
    try rewrite to_val_of_result in Hv; congruence
  | eapply IH; first (by rewrite Heq);
    rewrite language_to_val_eq; apply fill_item_no_result;
      by rewrite -language_to_val_eq].

Lemma list_destruct_snoc {A} (l : list A) :
  l = nil ∨ ∃ xt xh, l = xh ++ [xt].
Proof.
  rewrite -(rev_involutive l).
  destruct (rev l) as [|xt xh]; first by left.
  right. simpl. by repeat eexists.
Qed.

Lemma prim_step_let_inv x e es e' P σ σ' tt :
  prim_step P (let: x := e in es) σ e' σ' tt →
  (∃ ev, language.to_val e = Some ev ∧ tt = nil ∧ σ' = σ ∧ e' = subst' x e es) ∨
  ∃ ei', language.to_val e = None ∧ prim_step P e σ ei' σ' tt ∧ e' = (let: x := ei' in es)%E.
Proof.
  destruct (language.to_val e) as [ev|] eqn:Hev.
  - intros H%prim_base_step.
    2: solve_sub_redexes_are_values.
    inversion H as [x1 x2 x3 x4 EE| x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 EE]; simplify_eq.
    2: by inversion EE.
    inversion EE; simplify_eq. left. eexists. done.
  - intros (K&e1'&e2'&He1&He2&H)%prim_step_inv.
    destruct (list_destruct_snoc K) as [->|(xt & xh & ->)].
    + simpl in *; simplify_eq.
      inversion H as [x1 x2 x3 x4 EE| x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 EE]; simplify_eq.
      2: by inversion EE.
      inversion EE; simplify_eq.
      match goal with [HH : is_Some (to_result e) |- _ ] =>
         rewrite -language_to_val_eq Hev in HH; by destruct HH end.
    + subst e'. rewrite /= fill_app in He1.
      destruct xt; simplify_eq.
      replace (Let x e es) with (fill [LetEctx x es] e) in He1; last done.
      simplify_eq. right. eexists.
      rewrite /= fill_app /=.
      split; first done.
      split; last done.
      eapply fill_prim_step. eapply base_prim_step. done.
Qed.

Lemma prim_step_copy_inv l tg sz P σ e' σ' tt :
  prim_step P (Copy (Place l tg sz)) σ e' σ' tt →
  (∃ v trs', e' = (#v)%E ∧ tt = nil ∧ read_mem l sz (shp σ) = Some v ∧ trees_contain tg (strs σ) l.1 ∧ apply_within_trees (memory_access AccessRead (scs σ) tg (l.2, sz)) l.1 (strs σ) = Some trs' ∧ sz ≠ 0 ∧ σ' = mkState (shp σ) trs' (scs σ) (snp σ) (snc σ))
∨ (∃ v, e' = (#v)%E ∧ tt = nil ∧ read_mem l sz (shp σ) = Some v ∧ sz = 0 ∧ σ' = σ)
(*∨ (e' = (#(replicate sz ☠%S))%E ∧ tt = nil ∧ is_Some (read_mem l sz (shp σ)) ∧ trees_contain tg (strs σ) l.1 ∧ apply_within_trees (memory_access AccessRead (scs σ) tg (l.2, sz)) l.1 (strs σ) = None ∧ σ' = σ)*).
Proof.
  intros H%prim_base_step.
  2: solve_sub_redexes_are_values.
  inversion H as [x1 x2 x3 x4 EE| x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 ME IE]; simplify_eq.
  1: by inversion EE.
  inversion ME; simplify_eq.
  - inversion IE; simplify_eq.
    + left. do 2 eexists. done.
    + right. eexists. do 4 (split; first done). by destruct σ.
(*  - simpl in *.
    inversion IE; simplify_eq. right. right.
    do 5 (split; first done).
    by destruct σ. *)
Qed.

Lemma subst_val_twice_exchange e x1 x2 v1 v2 :
  x1 ≠ x2 →
  subst x1 (#v1)%E (subst' x2 (#v2)%E e) = subst x2 (#v2)%E (subst' x1 (#v1)%E e).
Proof.
  intros Hne.
  simpl.
  refine ((fix IH (e:expr) {struct e} : subst x1 #v1 (subst x2 #v2 e) = subst x2 #v2 (subst x1 #v1 e) := _) e).
  destruct e as [| | | | | | | | | | | | | | | | |? el| | ]; simpl; try (f_equal; by eapply IH).
  - clear IH. rewrite !bool_decide_decide. do 2 destruct decide; simplify_eq; simpl.
    + rewrite bool_decide_decide decide_True //.
    + rewrite bool_decide_decide decide_True //.
    + do 2 rewrite bool_decide_decide decide_False //.
  - f_equal. 1: apply IH. f_equal. rewrite !bool_decide_decide. do 2 destruct decide; simplify_eq; simpl; done.
  - f_equal. 1: eapply IH.
    induction el as [|?? IHel]; first done.
    + simpl. f_equal. 2: apply IHel. apply IH.
Qed.

Lemma read_reorder_onesided x1 x2 l1 tg1 sz1 l2 tg2 sz2 erest P σ :
  state_wf σ →
  x1 ≠ x2 →
  identical_states_after P (source x1 x2 l1 tg1 sz1 l2 tg2 sz2 erest) (target x1 x2 l1 tg1 sz1 l2 tg2 sz2 erest) σ 4.
Proof.
  destruct l1 as [blk1 off1], l2 as [blk2 off2].
  intros Hwf Hne.
  intros e4 σ4 (e1' & σ1 & [(?&[=]&_)|(e1&_&[(v1&trs1&->&_&Hread1&Hcontain1&Happly1&Hne1&->)|(v1&->&_&Hrd1&->&->)]%prim_step_copy_inv&->)]%prim_step_let_inv & Hrst).
  all: destruct Hrst as (e2 & σ2 & [(?&[= <-]&_&->&->)|(?&[=]&_)]%prim_step_let_inv & Hrst).
  all: simpl in *|-.
  all: destruct Hrst as (e3' & σ3 & [(?&[=]&_)|(e3&_&[(v3&trs3&->&_&Hread3&Hcontain3&Happly3&Hne2&->)|(v3&->&_&Hrd3&->&->)]%prim_step_copy_inv&->)]%prim_step_let_inv & Hrst).
  all: simpl in *|-.
  all: destruct Hrst as (e4' & σ4' & [(?&[= <-]&_&->&->)|(?&[=]&_)]%prim_step_let_inv & <- & <-).
  all: rewrite /target. 
  all: rewrite bool_decide_decide decide_True; last congruence.
  all: do 2 change (subst' (BNamed ?a) ?b ?c) with (subst a b c). 
  all: rewrite subst_val_twice_exchange //.
  - (* read x1: succeed, read x2: succeed *)
    odestruct CopyEvt_commutes as (y1&y2&y3&y4&HH1&HH2).
    { econstructor. 1: eapply Hcontain1. 1: eapply Happly1. 1: done. }
    { econstructor. 1: eapply Hcontain3. 1: eapply Happly3. 1: done. }
    do 2 eexists. split.
    { change (Let ?x2 ?a ?b) with (fill [LetEctx x2 b] a).
      eapply fill_prim_step. eapply base_prim_step.
      econstructor 2. 1: econstructor 3. 1: done.
      eapply HH1. }
    do 2 eexists. split.
    { simpl. eapply base_prim_step.
      econstructor 1. econstructor. 1: done. done. }
    do 2 eexists. simpl. split.
    { change (Let ?x2 ?a ?b) with (fill [LetEctx x2 b] a).
      eapply fill_prim_step. eapply base_prim_step.
      econstructor 2. 1: econstructor 3. 1: done. simpl. done. }
    do 2 eexists. split.
    { simpl. eapply base_prim_step.
      econstructor 1. econstructor. 1: done. done. }
    split; last done. rewrite bool_decide_decide decide_True //; congruence.
  - (* read x1: succeed, read x2: zerosized *)
    do 2 eexists. split.
    { change (Let ?x2 ?a ?b) with (fill [LetEctx x2 b] a).
      eapply fill_prim_step. eapply base_prim_step.
      econstructor 2. 1: econstructor 3. 1: done.
      econstructor; done. }
    do 2 eexists. split.
    { simpl. eapply base_prim_step.
      econstructor 1. econstructor. 1: done. done. }
    do 2 eexists. simpl. split.
    { change (Let x1 ?a ?b) with (fill [LetEctx x1 b] a).
      eapply fill_prim_step. eapply base_prim_step.
      econstructor 2. 1: econstructor 3. 1: done. simpl.
      econstructor; done. }
    do 2 eexists. split.
    { simpl. eapply base_prim_step.
      econstructor 1. econstructor. 1: done. done. }
    split; last done. rewrite bool_decide_decide decide_True //; congruence.
  - (* read x1: zerosized, read x2: succeed *)
    do 2 eexists. split.
    { change (Let x2 ?a ?b) with (fill [LetEctx x2 b] a).
      eapply fill_prim_step. eapply base_prim_step.
      econstructor 2. 1: simpl; econstructor 3. 1: done.
      econstructor; done. }
    do 2 eexists. split.
    { simpl. eapply base_prim_step.
      econstructor 1. econstructor. 1: done. done. }
    do 2 eexists. simpl. split.
    { change (Let x1 ?a ?b) with (fill [LetEctx x1 b] a).
      eapply fill_prim_step. eapply base_prim_step.
      econstructor 2. 1: econstructor 3. 1: done. simpl.
      econstructor; done. }
    do 2 eexists. split.
    { simpl. eapply base_prim_step.
      econstructor 1. econstructor. 1: done. done. }
    split; last done. rewrite bool_decide_decide decide_True //; congruence.
  - (* read x1: zerosized, read x2: zerosized *)
    do 2 eexists. simplify_eq. split.
    { change (Let x2 ?a ?b) with (fill [LetEctx x2 b] a).
      eapply fill_prim_step. eapply base_prim_step.
      econstructor 2. 1: econstructor 3. 1: done.
      econstructor; done. }
    do 2 eexists. split.
    { simpl. eapply base_prim_step.
      econstructor 1. econstructor. 1: done. done. }
    do 2 eexists. simpl. split.
    { change (Let x1 ?a ?b) with (fill [LetEctx x1 b] a).
      eapply fill_prim_step. eapply base_prim_step.
      econstructor 2. 1: econstructor 3. 1: done. simpl.
      econstructor; done. }
    do 2 eexists. split.
    { simpl. eapply base_prim_step.
      econstructor 1. econstructor. 1: done. done. }
    split; last by destruct σ. rewrite bool_decide_decide decide_True //; congruence.
Qed.

Lemma read_example_no_termination x1 x2 l1 tg1 sz1 l2 tg2 sz2 erest P σ :
  x1 ≠ x2 →
  no_termination_within P (source x1 x2 l1 tg1 sz1 l2 tg2 sz2 erest) σ 4.
Proof.
  intros Hne.
  econstructor; first done.
  intros e' σ' [(?&[=]&_)|(e1&_&[(v1&trs1&->&_&Hread1&Hcontain1&Happly1&Hne1&->)|(v1&->&_&Hrd1&->&->)]%prim_step_copy_inv&->)]%prim_step_let_inv.
  all: econstructor; first done.
  all: intros e' σ' [(?&[= <-]&_&->&->)|(?&[=]&_)]%prim_step_let_inv.
  all: econstructor; first done.
  all: intros e' σ' [(?&[=]&_)|(e3&_&[(v3&trs3&->&_&Hread3&Hcontain3&Happly3&Hne2&->)|(v3&->&_&Hrd3&->&->)]%prim_step_copy_inv&->)]%prim_step_let_inv.
  all: econstructor; first done.
  all: intros e' σ' [(?&[= <-]&_&->&->)|(?&[=]&_)]%prim_step_let_inv.
  all: econstructor.
Qed.

Theorem read_reorder x1 x2 l1 tg1 sz1 l2 tg2 sz2 erest P :
  x1 ≠ x2 →
  eventually_equal P (source x1 x2 l1 tg1 sz1 l2 tg2 sz2 erest) (target x1 x2 l1 tg1 sz1 l2 tg2 sz2 erest).
Proof.
  intros H1.
  exists 4.
  intros σ Hσ.
  split; first by eapply read_example_no_termination.
  split; first by eapply read_example_no_termination.
  split; eapply read_reorder_onesided; done.
Qed.

(*
Print Assumptions read_reorder.
*)