From Stdlib.Logic Require Import Classical IndefiniteDescription.
From stdpp Require Import gmap relations.
From iris.prelude Require Import prelude.
From simuliris.simulation Require Import language.

Section fairness.
Context {Λ: language}.

Implicit Types v : val Λ.
Implicit Types e : expr Λ.
Implicit Types c : expr_class Λ.
Implicit Types K : ectx Λ.
Implicit Types p : prog Λ.
Implicit Types T efs : list (expr Λ).

Definition enabled p i T σ :=
  ∃ e, T !! i = Some e ∧ reducible p e σ.

Definition exec: Type := nat → list (expr Λ) * state Λ * nat.

Notation "f '.(pool)'" := (fst (fst f)) (at level 1).
Notation "f '.(state)'" := (snd (fst f)) (at level 1).
Notation "f '.(id)'" := (snd f) (at level 1).


Definition diverges p (f: exec) T σ :=
  ((f 0).(pool) = T) ∧
  ((f 0).(state) = σ) ∧
  (∀ n, pool_step p (f n).(pool) (f n).(state) (f n).(id) (f (S n)).(pool) (f (S n)).(state)).

Record div_exec p T σ: Type := {
  the_exec :> nat → list (expr Λ) * state Λ * nat;
  exec_diverges: diverges p the_exec T σ
}.

Definition eventually_always_enabled {p T σ} i (f: div_exec p T σ)  :=
  ∃ m, ∀ n, m ≤ n → enabled p i ((f n).(pool)) ((f n).(state)).

Definition always_eventually_steps {p T σ} i (f: div_exec p T σ)  :=
  ∀ m, ∃ n, m ≤ n ∧ (f n).(id) = i.

Definition fair {p T σ} (f: div_exec p T σ) :=
  ∀ i, eventually_always_enabled i f → always_eventually_steps i f.

Definition fair_div p T σ := ∃ f: div_exec p T σ, fair f.




(* some theory about diverging executions *)
Program Definition div_exec_advance {p T σ} (f: div_exec p T σ) n :
    div_exec p (f n).(pool) (f n).(state) :=
  {| the_exec m := f (n + m) |}.
Next Obligation.
  intros p T σ f n; rewrite /diverges.
  replace (n + 0) with n by lia.
  do 2 (split; first done).
  intros k; simpl; rewrite Nat.add_succ_r.
  eapply exec_diverges.
Qed.

Program Definition div_exec_extend {p T σ i T' σ'} (f: div_exec p T' σ')
  (Hstep : pool_step p T σ i T' σ') : div_exec p T σ :=
  {| the_exec n := match n return _ with 0 => (T, σ, i) | S n => f n end |}.
Next Obligation.
  intros p T σ i T' σ' f. split; first done. split; first done.
  intros [|n].
  - simpl. destruct (exec_diverges _ _ _ f) as (? & ? & _).
    congruence.
  - eapply exec_diverges.
Qed.

Definition div_exec_next {p T σ} (f: div_exec p T σ) : div_exec p (f 1).(pool) (f 1).(state) := div_exec_advance f 1.

Definition div_exec_trace {p T σ} (f: div_exec p T σ) n :=
  fmap (λ i, (f i).(id)) (seq 0 n).


Lemma div_exec_trace_spec {p T σ} (f: div_exec p T σ) n i:
  i ∈ div_exec_trace f n ↔ (∃ m, (f m).(id) = i ∧ m < n).
Proof.
  rewrite /div_exec_trace list_elem_of_fmap.
  split; intros (m & Heq & Hlt); exists m; (split; first done).
  - eapply elem_of_seq in Hlt. lia.
  - eapply elem_of_seq. lia.
Qed.

Lemma div_exec_trace_zero {p T σ} (f: div_exec p T σ):
  div_exec_trace f 0 = [].
Proof.
  reflexivity.
Qed.

Lemma div_exec_trace_succ {p T σ} (f: div_exec p T σ) n:
  div_exec_trace f (S n) = (f 0).(id) :: div_exec_trace (div_exec_next f) n.
Proof.
  change (div_exec_trace f (S n)) with ((f 0).(id) :: ((λ i, (f i).(id)) <$> seq 1 n)).
  f_equiv. rewrite /div_exec_trace -fmap_S_seq -list_fmap_compose //.
Qed.

Lemma div_exec_next_step p T σ (f: div_exec p T σ):
  pool_step p T σ (f 0).(id) (div_exec_next f 0).(pool) (div_exec_next f 0).(state).
Proof.
  destruct (exec_diverges _ _ _ (div_exec_next f))as (-> & -> & _).
  destruct (exec_diverges _ _ _ f) as (H1 & H2 & Hsteps).
  specialize (Hsteps 0). by rewrite H1 H2 in Hsteps.
Qed.

Lemma div_exec_steps {p T σ} (f: div_exec p T σ) n:
  pool_steps p T σ (div_exec_trace f n) (f n).(pool) (f n).(state).
Proof.
  revert p T σ f; induction n as [|n IH]; intros p T σ f.
  - destruct (exec_diverges _ _ _ f) as (-> & -> & ?); constructor.
  - rewrite div_exec_trace_succ.  econstructor; eauto using div_exec_next_step.
Qed.





(* Below, we rely on notions of fairness which assume safety.
   With safety, enabled threads are those that are not
   values (see active_safe_enabled). We call those threads
  *active*. *)

Definition active_threads T :=
  list_to_set (C := gset nat) (fmap fst (filter (λ '(i, e), to_val e = None) (imap pair T))).

Lemma active_threads_spec T i:
  i ∈ active_threads T ↔ ∃ e, T !! i = Some e ∧ to_val e = None.
Proof.
  rewrite /active_threads /enabled elem_of_list_to_set list_elem_of_fmap.
  split.
  - intros [[i' e] [-> Hlook]]; simpl.
    eapply list_elem_of_filter in Hlook as [? Hlook].
    eapply elem_of_lookup_imap in Hlook as (? & ? & Heq & ?).
    injection Heq as ??; subst. eexists; split; eauto.
  - intros [e [Hlook Hval]]. exists (i, e).
    split; first done. eapply list_elem_of_filter.
    split; first done. eapply elem_of_lookup_imap.
    eexists _, _. split; done.
Qed.

Lemma active_threads_step p T σ i T' σ':
  pool_step p T σ  i T' σ' → active_threads T ∖ {[i]} ⊆ active_threads T'.
Proof.
  intros (e & e' & T_f & Hstep & Hlook & ->)%pool_step_iff.
  intros j [Hact Hnj]%elem_of_difference.
  eapply active_threads_spec in Hact as (e'' & Hlook' & Hnval).
  assert (i ≠ j) by set_solver.
  eapply active_threads_spec. exists e''; split; last done.
  eapply lookup_app_l_Some. rewrite list_lookup_insert_ne //.
Qed.

Lemma active_threads_steps p T σ I T' σ':
  pool_steps p T σ I T' σ' → active_threads T ∖ list_to_set I ⊆ active_threads T'.
Proof.
  induction 1 as [|T T' T'' σ σ' σ'' i I Hstep Hsteps]; simpl; first set_solver.
  eapply active_threads_step in Hstep. set_solver.
Qed.

Lemma active_safe_enabled i p T σ:
  pool_safe p T σ →
  i ∈ active_threads T →
  enabled p i T σ.
Proof.
  rewrite active_threads_spec; intros Hsafe (e & Hlook & Hnval).
  exists e; split; first done.
  eapply pool_safe_threads_safe in Hsafe; last done.
  destruct (Hsafe [e] σ [] ltac:(constructor) e 0 ltac:(done)) as [Hval | Hred]; last done.
  rewrite Hnval in Hval. destruct Hval as [ ? [=]].
Qed.

(* classic proof *)
Lemma active_eventually_steps p T σ (f: div_exec p T σ) i :
  fair f →
  pool_safe p T σ →
  i ∈ active_threads T →
  ∃ n, (f n).(id) = i.
Proof.
  intros Hfair Hsafe Hact.
  destruct (classic (∃ n, (f n).(id) = i)) as [|Hne]; first done.
  exfalso. opose proof (Hfair i _) as Hsteps; last first.
  { rewrite /always_eventually_steps in Hsteps.
    specialize (Hsteps 0). by naive_solver. }
  exists 0. intros n _. specialize (div_exec_steps f n) as Hsteps.
  eapply active_threads_steps in Hsteps. eapply active_safe_enabled.
  - eapply pool_steps_safe, Hsafe. eapply div_exec_steps.
  - eapply Hsteps, elem_of_difference; split; first done.
    rewrite elem_of_list_to_set. intros (m & Heq & _)%div_exec_trace_spec. naive_solver.
Qed.



(* we give an alternative characterization of fairness,
  which applies if we know the thread pool is safe in
  the current state.
*)
Section coinductive_inductive_fairness.

  CoInductive fair_div_coind p T σ : Prop :=
    fair_div_coind_step T' σ' I:
      pool_steps p T σ I T' σ' →
      ∅ ⊂ active_threads T ⊆ list_to_set I →
      fair_div_coind p T' σ' →
      fair_div_coind p T σ.


  Lemma all_active_eventually_step p T σ (f: div_exec p T σ) :
    fair f →
    pool_safe p T σ →
    ∃ n, active_threads T ⊆ list_to_set (div_exec_trace f n).
  Proof.
    intros Hfair Hsafe.
    enough (∀ O, O ⊆ active_threads T → ∃ n, O ⊆ list_to_set (div_exec_trace f n)) by eauto.
    intros O; induction (set_wf O) as [O _ IHO]; intros Hsub.
    destruct (decide (O ≡ ∅)) as [->%leibniz_equiv|[j Hj]%set_choose].
    - exists 0. set_solver.
    - eapply Hsub in Hj as Hact. eapply active_eventually_steps in Hact as (n1 & Hsteps); eauto.
      destruct (IHO (O ∖ {[j]})) as (n2 & Hstep'); [set_solver..|].
      exists (max n1 n2 + 1). intros k Hk. eapply elem_of_list_to_set, div_exec_trace_spec.
      destruct (decide (j = k)).
      + subst. exists n1. split; first done. lia.
      + assert (k ∈ div_exec_trace f n2) as Hel by (eapply (elem_of_list_to_set (C:=gset nat)); set_solver).
        eapply div_exec_trace_spec in Hel as (m & ? & ?).
        exists m. split; first done. lia.
  Qed.

  Lemma div_exec_some_active p T σ (f: div_exec p T σ) :
    ∃ i, i ∈ active_threads T.
  Proof.
    exists (f 0).(id). eapply active_threads_spec.
    specialize (div_exec_next_step _ _ _ f) as Hstep.
    eapply pool_step_iff in Hstep as (e & e' & efs & Hstep & Hlook & _).
    exists e. split; first done. by eapply val_stuck.
  Qed.

  Lemma fair_div_exec_advance p T σ (f: div_exec p T σ) n :
    fair f → fair (div_exec_advance f n).
  Proof.
    intros Hfair i Henabled.
    opose proof (Hfair i _) as Hsteps.
    - destruct Henabled as (m & Hen). exists (m + n).
      intros n' (n'' & ->)%Nat.le_sum.
      opose proof (Hen (m + n'') _) as Hen; first lia.
      simpl in Hen. by replace (m + n + n'') with (n + (m + n'')) by lia.
    - intros k. destruct (Hsteps (n + k)) as (m' & (m & ->)%Nat.le_sum & Hstep).
      exists (k + m). split; first lia. simpl.
      by replace (n + (k + m)) with (n + k + m) by lia.
  Qed.


  Lemma fair_div_post_fix_coind p T σ:
    fair_div p T σ →
    pool_safe p T σ →
    ∃ I T' σ', fair_div p T' σ' ∧
    pool_safe p T' σ' ∧
    pool_steps p T σ I T' σ' ∧
    ∅ ⊂ active_threads T ⊆ list_to_set I.
  Proof.
    intros [f Hfair] Hsafe.
    destruct (all_active_eventually_step _ _ _ _ Hfair Hsafe) as (n & Hsub).
    destruct (div_exec_some_active _ _ _ f) as (i & Hact).
    exists (div_exec_trace f n), (f n).(pool), (f n).(state).
    split; last split; last split.
    - exists (div_exec_advance f n). eapply fair_div_exec_advance, Hfair.
    - eapply pool_steps_safe; eauto using div_exec_steps.
    - eapply div_exec_steps.
    - split; set_solver.
  Qed.

  Lemma fair_div_to_fair_div_coind p T σ:
    fair_div p T σ →
    pool_safe p T σ →
    fair_div_coind p T σ.
  Proof.
    revert p T σ; cofix IH; intros p T σ Hfair Hsafe.
    destruct (fair_div_post_fix_coind _ _ _ Hfair Hsafe) as (I & T' & σ' & Hfair' & Hsafe' & Hsteps & Hact).
    econstructor; eauto.
  Qed.

  Lemma fair_div_step p T σ i T' σ':
    fair_div p T' σ' →
    pool_step p T σ i T' σ' →
    fair_div p T σ.
  Proof.
    intros [exec Hfair] Hstep.
    exists (div_exec_extend exec Hstep).
    intros j Henabled m.
    edestruct (Hfair j) as (m' & Hle & ?).
    { clear m. destruct Henabled as [m Henabled].
      exists (pred m). intros n Hle.
      apply (Henabled (S n)). lia. }
    exists (S m'). split; last done.
    apply Nat.le_le_succ_r. exact Hle.
  Qed.

End coinductive_inductive_fairness.



Section delay_based_fairness.
  Implicit Types D : gmap nat nat.

  Definition delays_for T D :=
    ∀ i, i ∈ active_threads T → is_Some (D !! i).

  Definition step_decr i D D' :=
    (∀ j n, j ≠ i → D !! j = Some n → ∃ n', n = S n' ∧ D' !! j = Some n').

  Inductive fair_pool_step (p: prog Λ):
    list (expr Λ) → gmap nat nat → state Λ → nat →
    list (expr Λ) → gmap nat nat → state Λ → Prop :=
    take_fair_step i T T' σ σ' D D':
      pool_step p T σ i T' σ' →
      step_decr i D D' →
      fair_pool_step p T D σ i T' D' σ'.

  Inductive fair_pool_steps (p: prog Λ):
    list (expr Λ) → gmap nat nat → state Λ → list nat →
    list (expr Λ) → gmap nat nat → state Λ → Prop :=
    | fair_pool_no_steps T σ (D: gmap nat nat) :
      delays_for T D → fair_pool_steps p T D σ [] T D σ
    | fair_pool_do_steps T T' T'' (D D' D'': gmap nat nat) (σ σ' σ'': state Λ) i I:
      delays_for T D →
      fair_pool_step p T D σ i T' D' σ' →
      fair_pool_steps p T' D' σ' I T'' D'' σ'' →
      fair_pool_steps p T D σ (i :: I) T'' D'' σ''.

  CoInductive fair_div_delay p T D σ : Prop :=
  | fair_div_delay_step i T' D' σ':
    fair_pool_step p T D σ i T' D' σ' →
    delays_for T D →
    fair_div_delay p T' D' σ' →
    fair_div_delay p T D σ.

  CoInductive fair_div_delay_tc p T D σ : Prop :=
  | fair_div_delay_tc_step I T' σ' D':
    I ≠ [] →
    fair_pool_steps p T D σ I T' D' σ' →
    fair_div_delay_tc p T' D' σ' →
    fair_div_delay_tc p T D σ.

  (* fair pool step lemmas *)
  Lemma fair_pool_step_iff p T D σ i T' D' σ':
    fair_pool_step p T D σ i T' D' σ' ↔
      pool_step p T σ i T' σ' ∧ step_decr i D D'.
  Proof.
    split; destruct 1; eauto 10 using take_fair_step.
  Qed.

  Lemma fair_pool_step_inv p T σ D i T' σ' D':
    fair_pool_step p T D σ i T' D' σ' →
      ∃ e e' efs, prim_step p e σ e' σ' efs ∧
      T !! i = Some e ∧
      T' = <[i := e']> T ++ efs ∧
      step_decr i D D'.
  Proof.
    destruct 1 as [i T T' σ σ' D D' Pool Hdecr].
    eapply pool_step_iff in Pool as (e & e' & T_f & Hstep & Hlook & Hupd).
    eauto 10.
  Qed.

  Lemma fair_pool_steps_concat p T D σ I T' D' σ' J T''' D''' σ''':
    fair_pool_steps p T D σ I T' D' σ' → fair_pool_steps p T' D' σ' J T''' D''' σ''' →  fair_pool_steps p T D σ (I ++ J) T''' D''' σ'''.
  Proof.
    induction 1 as [T σ|T T' T'' D D' D'' σ σ' σ'' i I Hdel Hstep Hsteps IH]; simpl; eauto.
    intros Hsteps'%IH. econstructor; eauto.
  Qed.

  Lemma fair_pool_steps_delays_for_start p T D σ I T' D' σ':
    fair_pool_steps p T D σ I T' D' σ' → delays_for T D.
  Proof.
    destruct 1; done.
  Qed.

  Lemma fair_pool_steps_delays_for_end p T D σ I T' D' σ':
    fair_pool_steps p T D σ I T' D' σ' → delays_for T' D'.
  Proof.
    induction 1; eauto.
  Qed.


  (* we prove the transitive closure delay version and
     the standard delay version equivalent *)
  Lemma fair_div_delays_for p T D σ:
     fair_div_delay p T D σ → delays_for T D.
  Proof. by destruct 1. Qed.

  Lemma fair_div_delay_tc_insert_steps p T D σ I T' D' σ':
    fair_pool_steps p T D σ I T' D' σ' → fair_div_delay_tc p T' D' σ' → fair_div_delay_tc p T D σ.
  Proof.
    intros Hsteps; destruct 1 as [J T''' D''' Hne Hsteps'' Hdiv''].
    econstructor; [|by eapply fair_pool_steps_concat|done].
    destruct I; simpl; naive_solver.
  Qed.

  Lemma fair_div_delay_tc_fair_div_delay p T D σ:
    fair_div_delay_tc p T D σ → fair_div_delay p T D σ.
  Proof.
    revert T D σ; cofix IH; intros T D σ.
    destruct 1 as [I T' D' σ' Hne Hsteps Hdiv].
    destruct Hsteps as [|T T' T'' D D' D'' σ σ' σ'' i I Hdel Hstep Hsteps]; first naive_solver.
    econstructor; eauto. eapply IH, fair_div_delay_tc_insert_steps, Hdiv. done.
  Qed.

  Lemma fair_div_delay_fair_div_delay_tc p T D σ:
    fair_div_delay p T D σ → fair_div_delay_tc p T D σ.
  Proof.
    revert T D σ; cofix IH; intros T D σ.
    destruct 1 as [i T' D' σ' Hne Hsteps Hdiv].
    eapply (fair_div_delay_tc_step p T D σ [i]); eauto.
    econstructor; eauto. constructor; eapply fair_div_delays_for, Hdiv.
  Qed.



  (* we prove that every fair_div_delay implies fair_div_coind *)
  Lemma fair_div_delay_active_threads_steps p T D σ:
    fair_div_delay p T D σ → ∃ T' D' σ' I, active_threads T ⊆ list_to_set I ∧ fair_div_delay p T' D' σ' ∧ pool_steps p T σ I T' σ'.
  Proof.
    enough (∀ O T D σ, O ⊆ active_threads T → fair_div_delay p T D σ → ∃ T' D' σ' I, O ⊆ list_to_set I ∧ fair_div_delay p T' D' σ' ∧ pool_steps p T σ I T' σ') by eauto.
    clear T D σ; intros O; induction (set_wf O) as [O _ IHO]; intros T D σ Hsub Hfair.
    destruct (decide (O ≡ ∅)) as [->%leibniz_equiv|[i Hi]%set_choose].
    - exists T, D, σ, []. do 2 (split; first done). constructor.
    - assert (delays_for T D) as Hdel by by destruct Hfair.
      assert (is_Some (D !! i)) as [d HD] by eapply Hdel, Hsub, Hi.
      revert T D σ Hsub Hfair Hdel HD. induction (lt_wf d) as [d _ IHd].
      intros T D σ Hsub Hfair Hdel HD. destruct Hfair as [j T' D' σ' Hstep _ Hfair].
      eapply fair_pool_step_iff in Hstep as [Hpool Hdecr].
      destruct (decide (j ∈ O)).
      + edestruct (IHO (O ∖ {[j]})) as (T'' & D'' & σ'' & I & HI & Hfair' & Hsteps).
        * by set_solver.
        * etrans; last by eapply active_threads_step. set_solver.
        * apply Hfair.
        * exists T'', D'', σ'', (j :: I); split.
         { intros k Hk; destruct (decide (k = j)); set_solver. }
          split; first done.
          econstructor; eauto.
      + assert (j ≠ i) by set_solver.
        edestruct Hdecr as (d' & Heq & HD'); eauto.
        subst d. edestruct (IHd d') as (T'' & D'' & σ'' & I & HI & Hfair' & Hsteps).
        * lia.
        * etrans; last by eapply active_threads_step. set_solver.
        * eauto.
        * by eapply fair_div_delays_for.
        * done.
        * exists T'', D'', σ'', (j :: I); split.
          { intros k Hk; destruct (decide (k = j)); set_solver. }
          split; first done.
          econstructor; eauto.
  Qed.

  Lemma fair_div_delay_has_active p T D σ:
    fair_div_delay p T D σ → ∅ ⊂ active_threads T.
  Proof.
    destruct 1 as [j T' D' σ' Hfair Hdel ?].
    enough (j ∈ active_threads T) by set_solver.
    eapply fair_pool_step_inv in Hfair as (e & e' & T_f & Step & Hlook & Hinsert & Hdecr).
    eapply active_threads_spec. exists e.
    split; first done. by eapply val_stuck.
  Qed.

  Lemma fair_div_delay_fair_div_coind p T D σ:
    fair_div_delay p T D σ → fair_div_coind p T σ.
  Proof.
    revert T D σ; cofix IH; intros T D σ Hfair.
    eapply fair_div_delay_has_active in Hfair as Hact.
    eapply fair_div_delay_active_threads_steps in Hfair as (T' & D' & σ' & I & Hsub & Hfair' & Hsteps).
    apply (fair_div_coind_step p T σ T' σ' I); eauto.
  Qed.


  (* we prove that fair_div_coind implies fair_div_delay *)
  Fixpoint delays_for_trace I D :=
    match I with
    | nil => D
    | i :: I' => <[i := 0]> (S <$> delays_for_trace I' D)
    end.

  Definition active_only T D := filter (λ '(i, n), i ∈ active_threads T) D.

  Notation trace_delays T I D := (active_only T (delays_for_trace I D)).

  Lemma pool_step_to_fair_pool_step p T σ i T' σ' D:
    pool_step p T σ i T' σ' → fair_pool_step p T (<[i:=0]> (S <$> D)) σ i T' D σ'.
  Proof.
    intros Hstep; eapply fair_pool_step_iff.
    split; first done.
    intros j n Hne. rewrite lookup_insert_ne // lookup_fmap.
    destruct (D !! j); simpl; naive_solver.
  Qed.


  Lemma delays_for_trace_oblivious_single i I D1 D2:
    i ∈ I → delays_for_trace I D1 !! i = delays_for_trace I D2 !! i.
  Proof.
    induction 1 as [i|i j I Hel IH]; simpl.
    - by rewrite !lookup_insert_eq.
    - destruct (decide (i = j)); first (subst; by rewrite !lookup_insert_eq).
      by rewrite !lookup_insert_ne //= !lookup_fmap IH.
  Qed.


  Lemma delays_for_trace_oblivious T I D1 D2:
    active_threads T ⊆ list_to_set I → trace_delays T I D1 = trace_delays T I D2.
  Proof.
    intros Hact; eapply map_filter_strong_ext.
    intros i d.
    split; intros [Hact' Hdel]; (split; first done);
    erewrite delays_for_trace_oblivious_single; set_solver.
  Qed.


  Lemma delays_for_active_only T D:
    delays_for T (active_only T D) ↔ delays_for T D.
  Proof.
    split; intros Hdel j Hj; destruct (Hdel j Hj) as [d HD];
      exists d.
    - eapply map_lookup_filter_Some_1_1, HD.
    - eapply map_lookup_filter_Some; eauto.
  Qed.

  Lemma pool_step_delays_for_update p T σ i T' σ' D:
    pool_step p T σ i T' σ' →
    delays_for T' D →
    delays_for T (<[i := 0]> (S <$> D)).
  Proof.
    intros Hstep Hdel. intros j Hj. destruct (decide (i = j)).
    { subst; rewrite lookup_insert_eq; eauto. }
    rewrite lookup_insert_ne // lookup_fmap fmap_is_Some.
    eapply Hdel, active_threads_step; eauto.
    set_solver.
  Qed.

  Lemma pool_steps_delays_for_update p T σ I T' σ' D:
    pool_steps p T σ I T' σ' →
    delays_for T' D →
    delays_for T (delays_for_trace I D).
  Proof.
    induction 1 as [T|T T' T'' σ σ' σ'' i I Hstep Hsteps IH];
      simpl; eauto using pool_step_delays_for_update.
  Qed.

  Lemma pool_steps_to_fair_pool_steps p T σ I T' σ' D:
    pool_steps p T σ I T' σ' →
    delays_for T' D →
    fair_pool_steps p T (delays_for_trace I D) σ I T' D σ'.
  Proof.
    induction 1 as [T|T T' T'' σ σ' σ'' i I Hstep Hsteps IH]; simpl.
    - by constructor.
    - econstructor; eauto using
      pool_step_to_fair_pool_step, pool_step_delays_for_update, pool_steps_delays_for_update.
  Qed.

  Lemma fair_pool_active_only p T D σ i T' D' σ':
    fair_pool_step p T D σ i T' D' σ' →
    fair_pool_step p T (active_only T D) σ i T' (active_only T' D') σ'.
  Proof.
    destruct 1 as [i T T' D D' σ σ' Hstep Hdecr].
    econstructor; first done.
    intros j d Hne Hactive. eapply map_lookup_filter_Some in Hactive as [HD Hact].
    destruct (Hdecr j d  Hne HD) as (d' & -> & HD').
    exists d'; split; first done.
    eapply map_lookup_filter_Some; split; first done.
    eapply active_threads_step; eauto.
    set_solver.
  Qed.

  Lemma fair_pool_steps_active_only p T D σ I T' D' σ':
    fair_pool_steps p T D σ I T' D' σ' →
    fair_pool_steps p T (active_only T D) σ I T' (active_only T' D') σ'.
  Proof.
    induction 1 as [T|T T' T'' D D' D'' σ σ' σ'' i I Hstep Hsteps IH]; simpl.
    - constructor; by eapply delays_for_active_only.
    - econstructor; eauto using fair_pool_active_only.
      by eapply delays_for_active_only.
  Qed.

  Lemma fair_div_coind_trace p T σ:
    fair_div_coind p T σ → ∃ I T' σ', ∅ ⊂ active_threads T ⊆ list_to_set I ∧ pool_steps p T σ I T' σ' ∧ fair_div_coind p T' σ'.
  Proof.
    destruct 1 as [T' σ' I Hstep Hsub Hfair]; eauto 10.
  Qed.

  Lemma fair_div_coind_trace_strong {p T σ} (Div: fair_div_coind p T σ) :
    { I | ∃ T' σ', ∅ ⊂ active_threads T ⊆ list_to_set I ∧ pool_steps p T σ I T' σ' ∧ fair_div_coind p T' σ' }.
  Proof.
    eapply constructive_indefinite_description, fair_div_coind_trace, Div.
  Qed.

  Definition fair_div_coind_delays {p T σ} (Div: fair_div_coind p T σ) :=
      active_only T (delays_for_trace (proj1_sig (fair_div_coind_trace_strong Div)) ∅).

  Lemma delays_for_delays_for_trace p T σ T' σ' I D:
    active_threads T ⊆ list_to_set I → pool_steps p T σ I T' σ' → delays_for T (delays_for_trace I D).
  Proof.
    intros Hsub Hsteps. eapply delays_for_active_only.
    rewrite (delays_for_trace_oblivious _ _ _ (gset_to_gmap 0 (threads T'))); last done.
    eapply delays_for_active_only, pool_steps_delays_for_update; first done.
    intros j Hj. eapply active_threads_spec in Hj as (e & Hlook & _).
    exists 0. eapply lookup_gset_to_gmap_Some; split; last done.
    eapply threads_spec; eauto.
  Qed.

  Lemma fair_div_coind_unfold p T σ (Div: fair_div_coind p T σ):
    ∃ T' σ' (Div': fair_div_coind p T' σ') I,
      I ≠ [] ∧
      fair_pool_steps p T (fair_div_coind_delays Div) σ I T' (fair_div_coind_delays Div') σ'.
  Proof.
    rewrite /fair_div_coind_delays.
    destruct (fair_div_coind_trace_strong Div) as (I & T' & σ' & Hsub & Hsteps & Div'); simpl.
    exists T', σ', Div', I. split.
    - intros ->; set_solver.
    - remember (delays_for_trace (proj1_sig (fair_div_coind_trace_strong Div')) ∅) as D'.
      rewrite (delays_for_trace_oblivious _ _ ∅ D'); last apply Hsub.
      eapply fair_pool_steps_active_only, pool_steps_to_fair_pool_steps; first done.
      (* TODO: this part of the proof is odd, there should be better factoring *)
      subst D'.
      destruct (fair_div_coind_trace_strong Div') as (I' & T'' & σ'' & Hsub' & Hsteps' & Div''); simpl.
      eapply delays_for_delays_for_trace; eauto. apply Hsub'.
  Qed.

  Lemma fair_div_coind_fair_div_delay_tc p T σ:
    fair_div_coind p T σ → ∃ D, fair_div_delay_tc p T D σ.
  Proof.
    intros Div. exists (fair_div_coind_delays Div).
    revert T σ Div; cofix IH; intros T σ Div.
    destruct (fair_div_coind_unfold p T σ Div) as (T' & σ' & Div' & I & Hne & Hsteps).
    destruct I as [|i I]; first naive_solver.
    inversion Hsteps as [|? T_mid ?? D_mid ?? σ_mid ? ? ? Hdel Hstep Hsteps']; subst.
    econstructor; eauto.
  Qed.


  (* we prove that the existence of a fair delay-based execution
    implies the conventional notion of fairness. *)

  Lemma fair_div_delay_step_inv p T D σ:
    fair_div_delay p T D σ →
    ∃ i T' D' σ', pool_step p T σ i T' σ' ∧ step_decr i D D' ∧ delays_for T D ∧ fair_div_delay p T' D' σ'.
  Proof.
    destruct 1 as [i T' D' σ' Hstep Hdel Hfair]; eapply fair_pool_step_iff in Hstep as [Hstep Hdecr]; eauto 10.
  Qed.

  Lemma fair_div_delay_step_inv_strong {p T D σ} (Fair: fair_div_delay p T D σ):
    { '(T', σ', i, D') | fair_div_delay p T' D' σ' ∧ pool_step p T σ i T' σ' ∧ step_decr i D D' ∧ delays_for T D }.
  Proof.
    eapply fair_div_delay_step_inv in Fair.
    eapply constructive_indefinite_description in Fair as [i Fair].
    eapply constructive_indefinite_description in Fair as [T' Fair].
    eapply constructive_indefinite_description in Fair as [D' Fair].
    eapply constructive_indefinite_description in Fair as [σ' Fair].
    exists (T', σ', i, D'). destruct Fair as (? & ? & ? & ?); eauto.
  Qed.

  Fixpoint fair_div_delay_to_exec {p T D σ} (Fair: fair_div_delay p T D σ) (n: nat) : list (expr Λ) * state Λ * nat :=
    match n with
    | 0 => (T, σ, (fst (proj1_sig (fair_div_delay_step_inv_strong Fair))).(id))
    | S m =>
      match fair_div_delay_step_inv_strong Fair with
      | exist _ (T', σ', i, D') H =>
        fair_div_delay_to_exec (match H with conj Fair' _ => Fair' end) m
      end
    end.

  Lemma fair_div_delay_to_exec_succ {p T D σ} (Fair: fair_div_delay p T D σ) (n: nat) :
    fair_div_delay_to_exec Fair (S n) =
      match fair_div_delay_step_inv_strong Fair with
      | exist _ (T', σ', i, D') H =>
        fair_div_delay_to_exec (match H with conj Fair' _ => Fair' end) n
      end.
  Proof. reflexivity. Qed.

  Lemma fair_div_delay_to_exec_step {p T D σ} (Fair: fair_div_delay p T D σ) n:
    pool_step p (fair_div_delay_to_exec Fair n).(pool)
      (fair_div_delay_to_exec Fair n).(state)
      (fair_div_delay_to_exec Fair n).(id)
      (fair_div_delay_to_exec Fair (S n)).(pool)
      (fair_div_delay_to_exec Fair (S n)).(state).
  Proof.
    revert p T D σ Fair; induction n as [|n IH]; intros p T D σ Fair.
    - simpl; destruct (fair_div_delay_step_inv_strong Fair) as ([[[T' σ'] i] D'] & Fair' & Hstep & Hdecr & Hdel); simpl; done.
    - rewrite fair_div_delay_to_exec_succ. rewrite fair_div_delay_to_exec_succ.
      destruct (fair_div_delay_step_inv_strong Fair) as ([[[T' σ'] i] D'] & Fair' & Hstep & Hdecr & Hdel).
      eapply IH.
  Qed.


  Program Definition fair_div_delay_to_div_exec {p T D σ} (Fair: fair_div_delay p T D σ) : div_exec p T σ :=
    {| the_exec n := fair_div_delay_to_exec Fair n |}.
  Next Obligation.
    intros p T D σ Fair. rewrite /diverges.
    split; first done.
    split; first done.
    intros n; eapply fair_div_delay_to_exec_step.
  Qed.

  Lemma fair_div_delay_to_exec_steps {p T D σ} (Fair: fair_div_delay p T D σ) i n:
    D !! i = Some n → ∃ m, m ≤ n ∧ (fair_div_delay_to_div_exec Fair m).(id) = i.
  Proof.
    revert T D σ Fair; induction n as [|n IH]; intros T D σ Fair Hlook.
    - exists 0. split; first done. simpl.
      destruct (fair_div_delay_step_inv_strong Fair) as ([[[T' σ'] j] D'] & Fair' & Hstep & Hdecr & Hdel); simpl.
      destruct (decide (i = j)) as [|Hne]; first done.
      destruct (Hdecr i _ Hne Hlook) as (? & ? & ?); naive_solver.
    - destruct (fair_div_delay_step_inv_strong Fair) as ([[[T' σ'] j] D'] & Fair' & Hstep & Hdecr & Hdel) eqn: Heq.
      destruct (decide (i = j)) as [|Hne].
      { exists 0; split; first lia. simpl; rewrite Heq; simpl; done. }
      destruct (Hdecr i _ Hne Hlook) as (n' & ? & Hlook').
      assert (n' = n) as -> by naive_solver.
      destruct (IH T' D' σ' Fair' Hlook') as (m & Hle & Hstep').
      exists (S m). split; first lia. simpl; rewrite Heq //=.
  Qed.

  Lemma fair_div_delay_to_exec_advance {p T D σ} (Fair: fair_div_delay p T D σ) m:
    ∃ T' D' σ' (Fair': fair_div_delay p T' D' σ'), ∀ n, fair_div_delay_to_div_exec Fair' n = fair_div_delay_to_div_exec Fair (m + n).
  Proof.
    revert T D σ Fair; induction m as [|m IH]; intros T D σ Fair; simpl; eauto.
    destruct (fair_div_delay_step_inv_strong Fair) as ([[[T' σ'] j] D'] & Fair' & Hstep & Hdecr & Hdel) eqn: Heq.
    eapply IH.
  Qed.

  Lemma fair_div_delay_to_exec_fair {p T D σ} (Fair: fair_div_delay p T D σ):
    fair (fair_div_delay_to_div_exec Fair).
  Proof.
    intros i (n & Hen). intros m.
    destruct (fair_div_delay_to_exec_advance Fair (m + n)) as (T' & D' & σ' & Fair' & Heq).
    assert (is_Some (D' !! i)) as [k HD].
    { eapply fair_div_delays_for in Fair' as Hdel. eapply Hdel.
      eapply active_threads_spec. opose proof (Hen (m + n + 0) _) as Hen; first lia.
      rewrite -Heq in Hen; simpl in Hen; destruct Hen as (e & Hlook & Hred).
      exists e. split; first done. destruct Hred as (e' & σ'' & efs & ?).
      by eapply val_stuck. }
    eapply (fair_div_delay_to_exec_steps Fair') in HD as (l & Hle & Hstep).
    rewrite Heq in Hstep. exists (m + n + l). split; first lia.
    done.
  Qed.


  (* we state the relationships between the fairness notions *)
  Theorem fair_div_coind_delay_iff p T σ:
    fair_div_coind p T σ ↔ (∃ D, fair_div_delay p T D σ).
  Proof.
    split.
    - intros [D HD]%fair_div_coind_fair_div_delay_tc.
      eapply fair_div_delay_tc_fair_div_delay in HD; by exists D.
    - intros [D HD]. by eapply fair_div_delay_fair_div_coind.
  Qed.

  Theorem fair_div_delay_traditional p T D σ:
    fair_div_delay p T D σ → fair_div p T σ.
  Proof.
    intros Fair. exists (fair_div_delay_to_div_exec Fair).
    eapply fair_div_delay_to_exec_fair.
  Qed.

  Corollary fair_div_coind_traditional p T σ:
    fair_div_coind p T σ → fair_div p T σ.
  Proof.
    rewrite fair_div_coind_delay_iff. intros [D Fair].
    by eapply fair_div_delay_traditional.
  Qed.

  Corollary fair_div_traditional_coind p T σ:
    pool_safe p T σ →
    (fair_div p T σ ↔ fair_div_coind p T σ).
  Proof.
    intros Hsafe; split.
    - intros ?; by eapply fair_div_to_fair_div_coind.
    - eapply fair_div_coind_traditional.
  Qed.


End delay_based_fairness.
End fairness.
