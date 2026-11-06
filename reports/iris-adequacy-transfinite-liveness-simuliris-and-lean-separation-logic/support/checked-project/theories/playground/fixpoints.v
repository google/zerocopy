From iris.prelude Require Import prelude.

Class Lattice (L: Type) (leq: relation L) `{!Equiv L} := {
  sup: (L → Prop) → L;
  inf: (L → Prop) → L;
  sup_is_upper_bound l (A: L → Prop): A l → leq l (sup A);
  sup_is_least_upper_bound l (A: L → Prop):
    (∀ l', A l' → leq l' l) → leq (sup A) l;
  inf_is_lower_bound l (A: L → Prop): A l → leq (inf A) l;
  inf_is_greatest_lower_bound l (A: L → Prop):
    (∀ l', A l' → leq l l') → leq l (inf A);
  lattice_anti_symm: AntiSymm equiv leq;
  lattice_leq_proper:: Proper (equiv ==> equiv ==> iff) leq;
  lattice_preorder: PreOrder leq;
  lattice_equivalence: @Equivalence L equiv;
}.

Class Mono `{Lattice L leq} (f: L → L) := {
  mono l1 l2: leq l1 l2 → leq (f l1) (f l2)
}.

Global Hint Mode Mono - - - - + : typeclass_instances.

Section lattice_properties.
  Context `{Lattice L leq}.

  Existing Instances lattice_anti_symm lattice_preorder lattice_equivalence.
  Infix "⪯" := leq (at level 60).

  Definition top := sup (λ _, True).
  Definition bot := inf (λ _, True).
  Definition meet l1 l2 := inf (λ l, l ≡ l1 ∨ l ≡ l2).
  Definition join l1 l2 := sup (λ l, l ≡ l1 ∨ l ≡ l2).

  Lemma top_upper_bound l: l ⪯ top.
  Proof.
    by eapply sup_is_upper_bound.
  Qed.

  Lemma bot_lower_bound l: bot ⪯ l.
  Proof.
    by eapply inf_is_lower_bound.
  Qed.

  Lemma meet_spec l l1 l2:
    l ⪯ meet l1 l2 ↔ l ⪯ l1 ∧ l ⪯ l2.
  Proof.
    split.
    - intros Hle; split; trans (meet l1 l2); auto; eapply inf_is_lower_bound; eauto.
    - intros [H1 H2]. eapply inf_is_greatest_lower_bound.
      intros l' [H3|H3]; by rewrite H3.
  Qed.

  Lemma meet_left l1 l2:
    meet l1 l2 ⪯ l1.
  Proof.
    edestruct meet_spec as [Hle _].
    edestruct Hle as [H1 _]; last by eapply H1.
    done.
  Qed.

  Lemma meet_right l1 l2:
    meet l1 l2 ⪯ l2.
  Proof.
    edestruct meet_spec as [Hle _].
    edestruct Hle as [_ H2]; last by eapply H2.
    done.
  Qed.


  Lemma join_spec l l1 l2:
    join l1 l2 ⪯ l ↔ l1 ⪯ l ∧ l2 ⪯ l.
  Proof.
    split.
    - intros Hle; split; trans (join l1 l2); auto; eapply sup_is_upper_bound; eauto.
    - intros [H1 H2]. eapply sup_is_least_upper_bound.
      intros l' [H3|H3]; by rewrite H3.
  Qed.

  Lemma join_left l1 l2:
    l1 ⪯ join l1 l2.
  Proof.
    edestruct join_spec as [Hle _].
    edestruct Hle as [H1 _]; last by eapply H1.
    done.
  Qed.

  Lemma join_right l1 l2:
    l2 ⪯ join l1 l2.
  Proof.
    edestruct join_spec as [Hle _].
    edestruct Hle as [_ H2]; last by eapply H2.
    done.
  Qed.

  Definition gfp f := sup (λ x, x ⪯ f x).
  Definition lfp f := inf (λ x, f x ⪯ x).

  Lemma gfp_greatest_post_fixpoint f l:
    l ⪯ f l → l ⪯ gfp f.
  Proof.
    intros Hle. by eapply sup_is_upper_bound.
  Qed.

  Lemma gfp_post_fixpoint f `{!Mono f}:
    (gfp f) ⪯ f (gfp f).
  Proof.
    eapply sup_is_least_upper_bound.
    intros l Hle. etrans; first apply Hle.
    eapply gfp_greatest_post_fixpoint in Hle.
    by eapply mono.
  Qed.

  Lemma gfp_pre_fixpoint f `{!Mono f}:
    f (gfp f) ⪯ (gfp f).
  Proof.
    eapply gfp_greatest_post_fixpoint.
    eapply mono. eapply gfp_post_fixpoint; first done.
  Qed.

  Lemma gfp_fixpoint f `{!Mono f}:
    gfp f ≡ f (gfp f).
  Proof.
    apply: anti_symm; eauto using gfp_post_fixpoint, gfp_pre_fixpoint.
  Qed.

  Lemma gfp_strong_coind f `{!Mono f} l:
    l ⪯ f (join l (gfp f)) → l ⪯ gfp f.
  Proof.
    intros Hle. trans (join l (gfp f)).
    - eapply join_left.
    - eapply gfp_greatest_post_fixpoint.
      eapply join_spec; split; first done.
      etrans; first apply gfp_post_fixpoint, _.
      eapply mono. eapply join_right.
  Qed.

  Global Instance mono_paco l `{!Mono f}:
    Mono (λ l', join l (f l')).
  Proof.
    split; intros l1 l2 Hle.
    eapply join_spec; split; first by eapply join_left.
    etrans; last eapply join_right. eapply mono, Hle.
  Qed.

  Lemma gfp_parametric_coind f `{!Mono f} l:
    l ⪯ gfp f ↔ l ⪯ f (gfp (λ l', join l (f l'))).
  Proof.
    split.
    - intros Hle. etrans; first eapply Hle.
      rewrite gfp_fixpoint; eapply mono.
      eapply gfp_greatest_post_fixpoint.
      etrans; last eapply join_right.
      eapply gfp_post_fixpoint, _.
    - intros Hle. etrans; first eapply Hle.
      etrans; last eapply gfp_pre_fixpoint, _.
      eapply mono. eapply gfp_greatest_post_fixpoint.
      etrans; first eapply gfp_post_fixpoint, _.
      eapply join_spec; split; done.
  Qed.

  Lemma lfp_least_pre_fixpoint f l:
    f l ⪯ l → lfp f ⪯ l.
  Proof.
    intros Hle. by eapply inf_is_lower_bound.
  Qed.

  Lemma lfp_pre_fixpoint f `{!Mono f}:
    f (lfp f) ⪯ (lfp f).
  Proof.
    eapply inf_is_greatest_lower_bound.
    intros l Hle. etrans; last apply Hle.
    eapply lfp_least_pre_fixpoint in Hle.
    by eapply mono.
  Qed.

  Lemma lfp_post_fixpoint f `{!Mono f}:
     (lfp f) ⪯ f (lfp f).
  Proof.
    eapply lfp_least_pre_fixpoint.
    eapply mono. eapply lfp_pre_fixpoint; first done.
  Qed.

  Lemma lfp_fixpoint f `{!Mono f}:
    lfp f ≡ f (lfp f).
  Proof.
    apply: anti_symm; eauto using lfp_post_fixpoint, lfp_pre_fixpoint.
  Qed.

  Lemma lfp_strong_ind f `{!Mono f} l:
    f (meet l (lfp f)) ⪯ l → lfp f ⪯ l.
  Proof.
    intros Hle. trans (meet l (lfp f)).
    - eapply lfp_least_pre_fixpoint.
      eapply meet_spec; split; first done.
      etrans; last apply lfp_pre_fixpoint, _.
      eapply mono. eapply meet_right.
    - eapply meet_left.
  Qed.

  (* the dual version of paco for least fixpoints *)
  Global Instance mono_copaco l `{!Mono f}:
    Mono (λ l', meet l (f l')).
  Proof.
    split; intros l1 l2 Hle.
    eapply meet_spec; split; first by eapply meet_left.
    etrans; first eapply (meet_right l); eapply mono, Hle.
  Qed.

  Lemma lfp_parametric_ind f `{!Mono f} l:
    lfp f ⪯ l ↔ f (lfp (λ l', meet l (f l'))) ⪯ l.
  Proof.
    split.
    - intros Hle. etrans; last eapply Hle.
      rewrite (lfp_fixpoint f); eapply mono.
      eapply lfp_least_pre_fixpoint.
      etrans; first eapply meet_right.
      eapply lfp_pre_fixpoint, _.
    - intros Hle. etrans; last eapply Hle.
      etrans; first eapply lfp_post_fixpoint, _.
      eapply mono. eapply lfp_least_pre_fixpoint.
      etrans; last eapply lfp_pre_fixpoint, _.
      eapply meet_spec; split; done.
  Qed.

End lattice_properties.

Arguments gfp : simpl never.
Arguments lfp : simpl never.

Global Instance Prop_Preorder: PreOrder impl.
Proof. split; unfold impl; eauto 10. Qed.

Global Instance Prop_equiv: Equiv Prop := iff.

Global Instance Prop_equivalence: @Equivalence Prop equiv.
Proof. split; intuition. intros ??? [][]. split; eauto. Qed.

Global Program Instance Prop_Lattice: Lattice Prop impl :=
  {| sup F := ∃ P, F P ∧ P; inf F := ∀ P, F P → P |}.
Next Obligation.
  intros P F; unfold impl; eauto.
Qed.
Next Obligation.
  intros P F; unfold impl.
  intros H [? []]. eapply H; done.
Qed.
Next Obligation.
  intros P F H H'; unfold impl; eapply H', H.
Qed.
Next Obligation.
  intros P F; unfold impl.
  intros H HP Q FQ. eapply H; done.
Qed.
Next Obligation.
  rewrite /impl. by split.
Qed.


Local Existing Instances lattice_anti_symm lattice_preorder lattice_equivalence.

Global Instance pointwise_Preorder A B (R: relation B) `{!PreOrder R}: PreOrder (pointwise_relation A R).
Proof.
  split; unfold impl.
  - intros ??. done.
  - intros ??? H1 H2 a. etrans; eauto.
Qed.

Global Instance pointwise_equiv A `{Equiv B}: Equiv (A → B) := pointwise_relation A equiv.

Global Instance pointwise_equivalence A `{eq: Equiv B} `{!Equivalence eq}: @Equivalence (A → B) equiv.
Proof. split; intuition. intros ????? a. etrans; eauto. Qed.

Global Instance pointwise_anti_symm A B `{PreOrder B leq} `{eq: Equiv B} `{!Equivalence eq} `{AntiSymm B eq leq}: @AntiSymm (A → B) equiv (pointwise_relation A leq).
Proof.
  intros f g Hfg Hgf. intros a; apply: anti_symm.
  - eapply Hfg.
  - eapply Hgf.
Qed.


Global Program Instance pointwise_Lattice A `{Lattice B leq}: Lattice (A → B) (pointwise_relation A leq) :=
  {| sup F := λ a, sup (λ b, ∃ f, F f ∧ f a = b); inf F := λ a, inf (λ b, ∃ f, F f ∧ f a = b) |}.
Next Obligation.
  intros A B leq equ Lat f F Ff a. eapply sup_is_upper_bound.
  exists f. split; done.
Qed.
Next Obligation.
  intros A B leq equ Lat f F upper a. eapply sup_is_least_upper_bound.
  intros b [g [Fg Hab]]. subst b. by eapply upper.
Qed.
Next Obligation.
  intros A B leq equ Lat f F Ff a. eapply inf_is_lower_bound.
  exists f. split; done.
Qed.
Next Obligation.
  intros A B leq equ Lat f F lower a. eapply inf_is_greatest_lower_bound.
  intros b [g [Fg Hab]]. subst b. by eapply lower.
Qed.
Next Obligation.
  intros A B leq equ Lat x x' Hx y y' Hy.
  split; intros Hrel a; (eapply lattice_leq_proper; last apply Hrel); eauto.
  - symmetry; eapply Hx.
  - symmetry; eapply Hy.
Qed.


Definition lattice_leq `{Lattice L leq} := leq.
Infix "⪯" := lattice_leq (at level 60).


Lemma lfp_mono `{Lattice L leq} (f g: L → L) `{!Mono g}:
  f ⪯ g → lfp f ⪯ lfp g.
Proof.
  intros Hle. eapply lfp_least_pre_fixpoint.
  etrans; last eapply lfp_pre_fixpoint, _.
  eapply Hle.
Qed.

Lemma gfp_mono `{Lattice L leq} (f g: L → L) `{!Mono f}:
  f ⪯ g → gfp f ⪯ gfp g.
Proof.
  intros Hle. eapply gfp_greatest_post_fixpoint.
  etrans; first eapply gfp_post_fixpoint, _.
  eapply Hle.
Qed.
