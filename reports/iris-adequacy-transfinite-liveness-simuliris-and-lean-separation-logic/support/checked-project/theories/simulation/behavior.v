From Stdlib.Logic Require Import Classical.
From stdpp Require Import strings.
From simuliris.simulation Require Import fairness language.

Section beh.
  Context {Λ : language}.

  (** Initial states and program entry point *)
  Variable (I: state Λ → state Λ → Prop).
  Variable (main: string) (u: val Λ).
  (** Observations on final values (of the main thread) *)
  Variable (O: val Λ → val Λ → Prop).

  (** * "Whole-program refinement", stated in a constructive way. *)
  Definition prog_ref (p_t p_s : prog Λ) :=
    ∀ σ_t σ_s, I σ_t σ_s → safe p_s (of_call main u) σ_s →
    (* divergent case *)
    (fair_div p_t [of_call main u] σ_t → fair_div p_s [of_call main u] σ_s) ∧
    (* convergent case (for main thread) *)
    (∀ v_t T_t σ_t' I, pool_steps p_t [of_call main u] σ_t I (of_val v_t :: T_t) σ_t' →
      ∃ v_s T_s σ_s' J, pool_steps p_s [of_call main u] σ_s J (of_val v_s :: T_s) σ_s' ∧
        O v_t v_s) ∧
    (* safety *)
    (safe p_t (of_call main u) σ_t).

  (** The notion of *contextual* refinement depends on an idea of "contexts" and
      some form of "well-formedness", so we do not define it in general and
      instead expect each language to define a suitable one. *)

  (** * A more classical definition of 'behavioral refinement', equivalent to
      the above. *)

  (** First we define the possible "behaviors" of a program, and which behaviors
      we consider observably refining others (lifting O to behaviors). *)
  Inductive beh := BehReturn (v : val Λ) | BehDiverge | BehUndefined.
  Inductive beh_ref : beh → beh → Prop :=
  | ObsBehVal (v_t v_s : val Λ) :
    O v_t v_s → beh_ref (BehReturn v_t) (BehReturn v_s)
  | ObsBehDiv :
    beh_ref BehDiverge BehDiverge
  | ObsBehUndefined b :
    beh_ref b BehUndefined.

  (** Next we define when a threadpool has a certain behavior. *)
  Inductive has_beh (p : prog Λ) : tpool Λ → state Λ → beh → Prop :=
  | HasBehStuck T σ :
    stuck_pool p T σ → has_beh p T σ BehUndefined
  | HasBehDiv T σ :
    fair_div p T σ → has_beh p T σ BehDiverge
  | HasBehRet v T σ :
      has_beh p (of_val v :: T) σ (BehReturn v)
  | HasBehStep T σ i T' σ' b :
      has_beh p T' σ' b →
      pool_step p T σ i T' σ' →
      has_beh p T σ b.
  (* FIXME: The first definition talks about all threads that happen to converge,
     the second definition only about the main thread. *)

  (** Finally, we can apply that to the relevant initial states. *)
  Definition prog_ref_alt (p_t p_s : prog Λ) :=
    ∀ σ_t σ_s b_t,
      I σ_t σ_s →
      has_beh p_t [of_call main u] σ_t b_t →
      ∃ b_s, has_beh p_s [of_call main u] σ_s b_s ∧ beh_ref b_t b_s.

  (** * [Classical] proof of equivalence of the two notions of behavior. *)
  Lemma has_beh_ub p T σ :
    has_beh p T σ BehUndefined ↔ pool_reach_stuck p T σ.
  Proof.
    split.
    - remember BehUndefined as b. induction 1 as [| | |??????? IH]; [|done..|].
      { eexists _, _, _. split; last done.
        constructor. }
      subst. specialize (IH eq_refl).
      eapply pool_steps_reach_stuck; last done.
      eapply pool_steps_single. done.
    - intros (T' & σ' & I' & Hsteps & Hstuck).
      induction Hsteps; eauto using has_beh.
  Qed.

  Lemma has_beh_div p T σ :
    has_beh p T σ BehDiverge ↔ fair_div p T σ.
  Proof.
    split.
    - remember BehDiverge as b. induction 1 as [| | |??????? IH]; try done; [].
      eapply fair_div_step; eauto.
    - intros. constructor. done.
  Qed.

  Lemma has_beh_ret p T σ v :
    has_beh p T σ (BehReturn v) ↔
    ∃ T' σ' I, pool_steps p T σ I (of_val v :: T') σ'.
  Proof.
    split.
    - remember (BehReturn v) as b. induction 1 as [| | |??????? IH]; try done; [|].
      { eexists _, _, _. simplify_eq/=. constructor. }
      subst. specialize (IH eq_refl).
      destruct IH as (T'' & σ'' & J & Hsteps).
      eexists T'', _, _. eapply pool_steps_trans; last done.
      eapply pool_steps_single. done.
    - intros (T' & σ' & I' & Hsteps).
      remember (of_val v :: T') as T''.
      induction Hsteps; eauto using has_beh.
      simplify_eq. constructor.
  Qed.

  (** Need classical logic for this. Alternatively, we could require decidability of reduction. *)
  Lemma not_pool_reach_stuck_pool_safe p T σ :
    ¬ pool_reach_stuck p T σ → pool_safe (Λ := Λ) p T σ.
  Proof.
    intros Hn T' σ' J Hsteps e i Hlookup.
    destruct (to_val e) as [v | ] eqn:Hval.
    { left. rewrite Hval. eauto. }
    right. destruct (classic (reducible p e σ')) as [Hred | Hnred]; first done.
    contradict Hn. exists T', σ', J. split; first done.
    exists e, i. split; first done. split; first done.
    by apply not_reducible.
  Qed.

  Lemma prog_ref_to_alt p_t p_s :
    prog_ref p_t p_s → prog_ref_alt p_t p_s.
  Proof.
    intros HB σ_t σ_s b_t HI Ht.
    destruct (classic (reach_stuck p_s (of_call main u) σ_s)) as [HUB | HnoUB].
    { exists BehUndefined. split; last by constructor.
      apply has_beh_ub. done. }
    apply not_pool_reach_stuck_pool_safe in HnoUB as Hsafe'.
    specialize (HB _ _ HI Hsafe'). destruct HB as (Hdiv & Hret & Hsafe).
    destruct b_t.
    - apply has_beh_ret in Ht as (T_t' & σ_t' & J_t & Hsteps_t).
      destruct (Hret _ _ _ _ Hsteps_t) as (v_s' & T_s' & σ_s' & J_s & Hsteps_s & HO).
      exists (BehReturn v_s'). split; last by constructor.
      apply has_beh_ret. eauto.
    - exists BehDiverge. split; last by constructor.
      apply has_beh_div, Hdiv, has_beh_div. done.
    - exfalso. apply has_beh_ub in Ht.
      eapply pool_reach_stuck_not_safe; done.
  Qed.

  Lemma prog_ref_from_alt p_t p_s :
    prog_ref_alt p_t p_s → prog_ref p_t p_s.
  Proof.
    intros HB σ_t σ_s HI Hsafe.
    assert (HnoUB : ¬ has_beh p_s [of_call main u] σ_s BehUndefined).
    { intros ?%has_beh_ub%pool_reach_stuck_not_safe. done. }
    split; last split.
    - intros Hdiv.
      destruct (HB _ _ BehDiverge HI) as (b_s & Hbeh_s & Hrel).
      { apply has_beh_div. eauto. }
      inversion Hrel; simplify_eq; last done.
      apply has_beh_div. done.
    - intros v_t T_t σ_t' J_t Hsteps.
      destruct (HB _ _ (BehReturn v_t) HI) as (b_s & Hbeh_s & Hrel).
      { apply has_beh_ret. eauto. }
      inversion Hrel; simplify_eq; last done.
      apply has_beh_ret in Hbeh_s. naive_solver.
    - destruct (classic (safe p_t (of_call main u) σ_t)) as [ | Hnsafe]; first done.
      exfalso. apply HnoUB.
      destruct (HB _ _ BehUndefined HI) as (b_s & Hbeh_s & Hrel).
      { apply has_beh_ub. apply NNPP. intros Hnreach%not_pool_reach_stuck_pool_safe. done. }
      inversion Hrel; simplify_eq; done.
  Qed.

  Lemma prog_ref_equiv p_t p_s :
    prog_ref p_t p_s ↔ prog_ref_alt p_t p_s.
  Proof.
    split; eauto using prog_ref_to_alt, prog_ref_from_alt.
  Qed.

  Lemma prog_ref_refl :
    (∀ σ1 σ2, I σ1 σ2 → σ1 = σ2) →
    Reflexive O →
    Reflexive prog_ref.
  Proof.
    intros HI_eq HO_refl p σ_t σ_s Hinit Hsafe.
    specialize (HI_eq _ _ Hinit) as ->.
    split_and!.
    - done.
    - intros ?????. eexists _, _, _, _. split; first done.
      apply HO_refl.
    - done.
  Qed.

  Lemma prog_ref_trans :
    (∀ σ1 σ2, I σ1 σ2 → σ1 = σ2) →
    Transitive O →
    Transitive prog_ref.
  Proof.
    intros HI_eq HO_trans p1 p2 p3 H1 H2 σ1 σ3 HI Hsafe3.
    specialize (HI_eq _ _ HI) as <-.
    specialize (H2 σ1 σ1 HI Hsafe3) as (Hdiv23 & Hterm23 & Hsafe2).
    specialize (H1 σ1 σ1 HI Hsafe2) as (Hdiv12 & Hterm12 & Hsafe1).
    split_and!.
    - eauto.
    - intros ???? (? & ? & ? & ? & Hsteps & ?)%Hterm12.
      apply Hterm23 in Hsteps as (? & ? & ? & ? & ? & ?).
      eexists _, _, _, _. split; first done.
      etrans; done.
    - done.
  Qed.

End beh.
