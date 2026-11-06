From Stdlib Require Import Logic.IndefiniteDescription.
From stdpp Require Import gmap.
From iris.prelude Require Import prelude.


Class Language := {
  expr: Type;
  step: expr → expr → list expr → Prop;
  val: expr → Prop;
  is_val:: ∀ e, Decision (val e);
  val_no_step: ∀ e, val e → ¬ ∃ e' efs, step e e' efs;
}.


Notation pool := (list (expr * expr)).
Notation trace := (list nat).
Notation delays := (gmap nat nat).

(* Language Setup *)
Notation "P '.(tgt)'" := (P.*1) (at level 1).
Notation "P '.(src)'" := (P.*2) (at level 1).


Section language_setup.

  Context `{!Language}.
  Implicit Types (e: expr) (T: list expr) (D: delays) (P: pool).


  Definition step_no_fork e e' := step e e' [].
  Definition steps_no_fork e e' := rtc step_no_fork e e'.

  Definition threads T :=
    list_to_set (C := gset nat) (seq 0 (length T)).

  Lemma threads_spec T i:
    i ∈ threads T ↔ ∃ e, T !! i = Some e.
  Proof.
    rewrite elem_of_list_to_set elem_of_seq.
    split.
    - intros [_ Hlt]. eapply lookup_lt_is_Some_2. lia.
    - intros ? % lookup_lt_is_Some_1. lia.
  Qed.

  Lemma threads_update T i e:
    threads T ⊆ threads (<[i:=e]> T).
  Proof.
    intros j [e' Hlook]%threads_spec.
    eapply threads_spec.
    destruct (decide (i = j)).
    - subst; exists e.
      eapply list_lookup_insert_eq, lookup_lt_Some, Hlook.
    - rewrite list_lookup_insert_ne; last done. by exists e'.
  Qed.

  Lemma threads_weaken T T':
    threads T ⊆ threads (T ++ T').
  Proof.
    intros j (e & Hlook)%threads_spec.
    eapply threads_spec. exists e.
    eapply lookup_app_l_Some, Hlook.
  Qed.

  Lemma threads_src_tgt P:
    threads P.(tgt) = threads P.(src).
  Proof.
    by rewrite /threads !length_fmap.
  Qed.



  (* we lift the step relation to thread pools,
    and we define the notion of a fair step.
    A fair step decreases counters in an associated
    delay list.
  *)
  Inductive pool_step : list expr → nat → list expr → Prop :=
    take_pool_step i T_l e e' T_r T_f:
      step e e' T_f →
      i = length T_l →
      pool_step (T_l ++ e :: T_r) i (T_l ++ e' :: T_r ++ T_f).

  Inductive pool_steps : list expr → trace → list expr → Prop :=
    | pool_no_steps T: pool_steps T [] T
    | pool_do_steps T T' T'' i I:
      pool_step T i T' →
      pool_steps T' I T'' →
      pool_steps T (i:: I) T''.


  Lemma pool_step_iff T i T':
    pool_step T i T' ↔
    (∃ e e' T_f, step e e' T_f ∧ T !! i = Some e ∧ T' = <[i := e']> T ++ T_f).
  Proof.
    split.
    - destruct 1 as [i T_l e e' T_r T_f Hstep]; subst.
      exists e, e', T_f. split; first done.
      rewrite list_lookup_middle; last done.
      split; first done.
      replace (length T_l) with (length T_l + 0) by lia.
      rewrite insert_app_r; simpl.
      by rewrite -app_assoc.
    - intros (e & e' & T_f & Hstep & Hlook & ->).
      replace T with (take i T ++ e :: drop (S i) T); last by eapply take_drop_middle.
      assert (i = length (take i T)).
      { rewrite length_take_le; first lia. eapply lookup_lt_Some in Hlook. lia. }
      replace i with (length (take i T) + 0) at 4 by lia.
      rewrite insert_app_r. simpl.
      rewrite -app_assoc; simpl.
      econstructor; auto.
  Qed.

  Lemma pool_steps_single T i T':
    pool_step T i T' →
    pool_steps T [i] T'.
  Proof.
    intros Hstep; econstructor; [eauto|constructor].
  Qed.

  Lemma pool_step_value_preservation e T i j T':
    pool_step T j T' →
    val e →
    T !! i = Some e →
    T' !! i = Some e.
  Proof.
    rewrite pool_step_iff.
    destruct 1 as (e1 & e2 & T_f & Hstep & Hpre & Hpost).
    intros Hval Hlook. destruct (decide (i = j)); subst.
    - pose proof val_no_step. naive_solver.
    - eapply lookup_app_l_Some.
      rewrite list_lookup_insert_ne; done.
  Qed.

  Lemma pool_steps_value_preservation e T i J T':
    pool_steps T J T' →
    val e →
    T !! i = Some e →
    T' !! i = Some e.
  Proof.
    induction 1; eauto using pool_step_value_preservation.
  Qed.

  (* Lemma no_forks_pool_steps e e' e'' i T:
    step_no_fork e e' →
    steps_no_fork e' e'' →
    T !! i = Some e →
    pool_steps T [i] (<[i := e'']> T).
  Proof.
    intros Hstep Hsteps.
    revert e T Hstep.
    induction Hsteps as [e'|e' e'' e''' Hstep' Hsteps IH]; intros e T Hstep Hlook.
    - eapply pool_steps_single, pool_step_iff.
      exists e, e', []; split; first done. split; first done.
      by rewrite right_id.
    - econstructor.
      + eapply pool_step_iff. exists e, e', []; split; first done. split; first done.
        rewrite right_id. reflexivity.
      + rewrite -(list_insert_insert_eq T i e''' e'). eapply IH; eauto.
        eapply list_lookup_insert_eq, lookup_lt_Some, Hlook.
      + set_solver.
  Qed. *)

  Lemma pool_steps_trans T T' T'' I I':
    pool_steps T I T' →
    pool_steps T' I' T'' →
    pool_steps T (I ++ I') T''.
  Proof.
    induction 1.
    - by rewrite left_id.
    - intros; simpl; econstructor; eauto.
  Qed.


  (* an expression is active in a thread pool,
    if it is not a value *)

  Definition active_threads T :=
    list_to_set (C := gset nat) (fmap fst (filter (λ '(i, e), ¬ val e) (imap pair T))).

  Lemma active_threads_spec T i:
    i ∈ active_threads T ↔ ∃ e, T !! i = Some e ∧ ¬ val e.
  Proof.
    rewrite /active_threads elem_of_list_to_set list_elem_of_fmap.
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

  Definition delays_for T D :=
    ∀ i, i ∈ active_threads T → is_Some (D !! i).


  Inductive fair_pool_step : list expr → delays → nat → list expr → delays → Prop :=
    take_fair_step i T T' D D':
    pool_step T i T' →
    (∀ j n, j ≠ i → D !! j = Some n → ∃ n', n = S n' ∧ D' !! j = Some n') →
    fair_pool_step T D i T' D'.

  (* an expression is active in a thread pool,
  if it is not a value *)
  Inductive fair_pool_steps : list expr → delays → trace → list expr → delays → Prop :=
  | fair_pool_no_steps T (D: delays): delays_for T D → fair_pool_steps T D [] T D
  | fair_pool_do_steps T T' T'' (D D' D'': delays) i I:
    delays_for T D →
    fair_pool_step T D i T' D' →
    fair_pool_steps T' D' I T'' D'' →
    fair_pool_steps T D (i :: I) T'' D''.

  Lemma fair_pool_step_iff T D i T' D':
    fair_pool_step T D i T' D' ↔
      pool_step T i T' ∧ (∀ j n, j ≠ i → D !! j = Some n → ∃ n', n = S n' ∧ D' !! j = Some n').
  Proof.
    split; destruct 1; eauto 10 using take_fair_step.
  Qed.

  Lemma fair_pool_step_inv T D i T' D':
    fair_pool_step T D i T' D' →
      ∃ e e' T_f, step e e' T_f ∧
      T !! i = Some e ∧
      T' = <[i := e']> T ++ T_f ∧
      (∀ j n, j ≠ i → D !! j = Some n → ∃ n', n = S n' ∧ D' !! j = Some n').
  Proof.
    destruct 1 as [i T T' D D' Pool Hdecr].
    eapply pool_step_iff in Pool as (e & e' & T_f & Hstep & Hlook & Hupd).
    eauto 10.
  Qed.


  (* assumption about target *)
  CoInductive fair_div T D : Prop :=
  | fair_div_step i T' D':
    fair_pool_step T D i T' D' →
    delays_for T D →
    fair_div T' D' →
    fair_div T D.


  CoInductive fair_div_tc T D : Prop :=
  | fair_div_tc_step I T' D':
    I ≠ [] →
    fair_pool_steps T D I T' D' →
    fair_div_tc T' D' →
    fair_div_tc T D.

  (* obligation to prove in the source *)
  CoInductive fair_div_alt T : Prop :=
    fair_div_alt_step T' I:
    pool_steps T I T' →
    ∅ ⊂ active_threads T ⊆ list_to_set I →
    fair_div_alt T' →
    fair_div_alt T.

  Lemma active_threads_step T i T':
    pool_step T i T' → active_threads T ∖ {[i]} ⊆ active_threads T'.
  Proof.
    intros (e & e' & T_f & Hstep & Hlook & ->)%pool_step_iff.
    intros j [Hact Hnj]%elem_of_difference.
    eapply active_threads_spec in Hact as (e'' & Hlook' & Hnval).
    assert (i ≠ j) by set_solver.
    eapply active_threads_spec. exists e''; split; last done.
    eapply lookup_app_l_Some. rewrite list_lookup_insert_ne //.
  Qed.

  Lemma threads_mono T i T':
    pool_step T i T' → threads T ⊆ threads T'.
  Proof.
    intros (e & e' & T_f & Hstep & Hlook & ->)%pool_step_iff.
    etrans; last by eapply threads_weaken.
    eapply threads_update.
  Qed.

  Lemma threads_mono' T I T':
    pool_steps T I T' → threads T ⊆ threads T'.
  Proof.
    induction 1; first done.
    etrans; first by eapply threads_mono.
    done.
  Qed.

  Lemma fair_div_delays T D:
    fair_div T D → delays_for T D.
  Proof. by destruct 1. Qed.

  Lemma fair_div_active_threads_steps T D:
    fair_div T D → ∃ T' D' O, active_threads T ⊆ list_to_set O ∧ fair_div T' D' ∧ pool_steps T O T'.
  Proof.
    enough (∀ O T D, O ⊆ active_threads T → fair_div T D → ∃ T' D' O', O ⊆ list_to_set O' ∧ fair_div T' D' ∧ pool_steps T O' T') by eauto.
    clear T D; intros O; induction (set_wf O) as [O _ IHO]; intros T D Hsub Hfair.
    destruct (decide (O ≡ ∅)) as [->%leibniz_equiv|[i Hi]%set_choose].
    - exists T, D, []. do 2 (split; first done). constructor.
    - assert (delays_for T D) as Hdel by by destruct Hfair.
      assert (is_Some (D !! i)) as [d HD] by eapply Hdel, Hsub, Hi.
      revert T D Hsub Hfair Hdel HD. induction (lt_wf d) as [d _ IHd].
      intros T D Hsub Hfair Hdel HD. destruct Hfair as [j T' D' Hstep _ Hfair].
      eapply fair_pool_step_iff in Hstep as [Hpool Hdecr].
      destruct (decide (j ∈ O)).
      + edestruct (IHO (O ∖ {[j]})) as (T'' & D'' & O' & HO' & Hfair' & Hsteps).
        * by set_solver.
        * etrans; last by apply active_threads_step. set_solver.
        * apply Hfair.
        * exists T'', D'', (j :: O'); split.
         { intros k Hk; destruct (decide (k = j)); set_solver. }
          split; first done.
          econstructor; eauto.
      + assert (j ≠ i) by set_solver.
        edestruct Hdecr as (d' & Heq & HD'); eauto.
        subst d. edestruct (IHd d') as (T'' & D'' & O' & HO' & Hfair' & Hsteps).
        * lia.
        * etrans; last by eapply active_threads_step. set_solver.
        * eauto.
        * by eapply fair_div_delays.
        * done.
        * exists T'', D'', (j :: O'); split.
          { intros k Hk; destruct (decide (k = j)); set_solver. }
          split; first done.
          econstructor; eauto.
  Qed.


  Lemma fair_div_has_active T D:
    fair_div T D → ∅ ⊂ active_threads T.
  Proof.
    destruct 1 as [j T' D' Hfair Hdel ?].
    enough (j ∈ active_threads T) by set_solver.
    eapply fair_pool_step_inv in Hfair as (e & e' & T_f & Step & Hlook & Hinsert & Hdecr).
    eapply active_threads_spec. exists e.
    split; first done. pose proof val_no_step. naive_solver.
  Qed.

  Lemma fair_div_fair_div_alt T D:
    fair_div T D → fair_div_alt T.
  Proof.
    revert T D; cofix IH; intros T D Hfair.
    eapply fair_div_has_active in Hfair as Hact.
    eapply fair_div_active_threads_steps in Hfair as (T' & D' & O & Hsub & Hfair' & Hsteps).
    apply (fair_div_alt_step T T' O); eauto.
  Qed.



  Lemma pool_step_to_fair_pool_step T i T' D:
    pool_step T i T' → fair_pool_step T (<[i:=0]> (S <$> D)) i T' D.
  Proof.
    intros Hstep; eapply fair_pool_step_iff.
    split; first done.
    intros j n Hne. rewrite lookup_insert_ne // lookup_fmap.
    destruct (D !! j); simpl; naive_solver.
  Qed.

  Fixpoint delays_for_trace I D :=
    match I with
    | nil => D
    | i :: I' => <[i := 0]> (S <$> delays_for_trace I' D)
    end.

  Definition active_only T D := filter (λ '(i, n), i ∈ active_threads T) D.

  Notation trace_delays T I D := (active_only T (delays_for_trace I D)).

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

  Lemma pool_step_delays_for T i T' D:
    pool_step T i T' →
    delays_for T' D →
    delays_for T (<[i := 0]> (S <$> D)).
  Proof.
    intros Hstep Hdel. intros j Hj. destruct (decide (i = j)).
    { subst; rewrite lookup_insert_eq; eauto. }
    rewrite lookup_insert_ne // lookup_fmap fmap_is_Some.
    eapply Hdel, active_threads_step; eauto.
    set_solver.
  Qed.

  Lemma pool_steps_delays_for T I T' D:
    pool_steps T I T' →
    delays_for T' D →
    delays_for T (delays_for_trace I D).
  Proof.
    induction 1 as [T|T T' T'' i I Hstep Hsteps IH];
      simpl; eauto using pool_step_delays_for.
  Qed.

  Lemma pool_steps_to_fair_pool_steps T I T' D:
    pool_steps T I T' →
    delays_for T' D →
    fair_pool_steps T (delays_for_trace I D) I T' D.
  Proof.
    induction 1 as [T|T T' T'' i I Hstep Hsteps IH]; simpl.
    - by constructor.
    - econstructor; eauto using pool_step_to_fair_pool_step.
      eauto using pool_step_delays_for, pool_steps_delays_for.
  Qed.

  Lemma fair_pool_active_only T D i T' D':
    fair_pool_step T D i T' D' →
    fair_pool_step T (active_only T D) i T' (active_only T' D').
  Proof.
    destruct 1 as [i T T' D D' Hstep Hdecr].
    econstructor; first done.
    intros j d Hne Hactive. eapply map_lookup_filter_Some in Hactive as [HD Hact].
    destruct (Hdecr j d  Hne HD) as (d' & -> & HD').
    exists d'; split; first done.
    eapply map_lookup_filter_Some; split; first done.
    eapply active_threads_step; eauto.
    set_solver.
  Qed.


  Lemma fair_pool_steps_active_only T D I T' D':
    fair_pool_steps T D I T' D' →
    fair_pool_steps T (active_only T D) I T' (active_only T' D').
  Proof.
    induction 1 as [T|T T' T'' D D' D'' i I Hstep Hsteps IH]; simpl.
    - constructor; by eapply delays_for_active_only.
    - econstructor; eauto using fair_pool_active_only.
      by eapply delays_for_active_only.
  Qed.

  Lemma fair_div_alt_trace T:
    fair_div_alt T → ∃ I T', ∅ ⊂ active_threads T ⊆ list_to_set I ∧ pool_steps T I T' ∧ fair_div_alt T'.
  Proof.
    destruct 1 as [T' I Hstep Hsub Hfair]; eauto 10.
  Qed.

  Lemma fair_div_alt_trace_strong T:
    fair_div_alt T → { I | ∃ T', ∅ ⊂ active_threads T ⊆ list_to_set I ∧ pool_steps T I T' ∧ fair_div_alt T' }.
  Proof.
    intros Hdiv. eapply constructive_indefinite_description, fair_div_alt_trace, Hdiv.
  Qed.

  Definition fair_div_alt_delays T (Div: fair_div_alt T) :=
      active_only T (delays_for_trace (proj1_sig (fair_div_alt_trace_strong T Div)) ∅).

  Lemma delays_for_delays_for_trace T T' I D:
    active_threads T ⊆ list_to_set I → pool_steps T I T' → delays_for T (delays_for_trace I D).
  Proof.
    intros Hsub Hsteps. eapply delays_for_active_only.
    rewrite (delays_for_trace_oblivious _ _ _ (gset_to_gmap 0 (threads T'))); last done.
    eapply delays_for_active_only, pool_steps_delays_for; first done.
    intros j Hj. eapply active_threads_spec in Hj as (e & Hlook & _).
    exists 0. eapply lookup_gset_to_gmap_Some; split; last done.
    eapply threads_spec; eauto.
  Qed.


  Lemma fair_pool_steps_delays_for_start T D I T' D':
    fair_pool_steps T D I T' D' → delays_for T D.
  Proof.
    destruct 1; done.
  Qed.

  Lemma fair_pool_steps_delays_for_end T D I T' D':
    fair_pool_steps T D I T' D' → delays_for T' D'.
  Proof.
    induction 1; eauto.
  Qed.


  Lemma fair_div_alt_inv T (Div: fair_div_alt T):
    ∃ T' (Div': fair_div_alt T') I,
      I ≠ [] ∧
      fair_pool_steps T (fair_div_alt_delays T Div) I T' (fair_div_alt_delays T' Div').
  Proof.
    rewrite /fair_div_alt_delays.
    destruct (fair_div_alt_trace_strong T) as (I & T' & Hsub & Hsteps & Div'); simpl.
    exists T', Div', I. split.
    - intros ->; set_solver.
    - remember (delays_for_trace (proj1_sig (fair_div_alt_trace_strong T' Div')) ∅) as D'.
      rewrite (delays_for_trace_oblivious _ _ ∅ D'); last apply Hsub.
      eapply fair_pool_steps_active_only, pool_steps_to_fair_pool_steps; first done.
      (* TODO: this part of the proof is odd, there should be better factoring *)
      subst D'.
      destruct (fair_div_alt_trace_strong) as (I' & T'' & Hsub' & Hsteps' & Div''); simpl.
      eapply delays_for_delays_for_trace; eauto. apply Hsub'.
  Qed.


  Lemma fair_div_insert_steps T D I T' D':
    fair_pool_steps T D I T' D' → fair_div T' D' → fair_div T D.
  Proof.
    induction 1 as [T|T T' T'' D D' D'' i I Hstep Hsteps IH]; eauto.
    intros Hdiv; econstructor; eauto.
  Qed.


  Lemma fair_pool_steps_concat T D I T' D' J T''' D''':
    fair_pool_steps T D I T' D' → fair_pool_steps T' D' J T''' D''' →  fair_pool_steps T D (I ++ J) T''' D'''.
  Proof.
    induction 1 as [T|T T' T'' D D' D'' i I Hdel Hstep Hsteps IH]; simpl; eauto.
    intros Hsteps'%IH. econstructor; eauto.
  Qed.

  Lemma fair_div_tc_insert_steps T D I T' D':
    fair_pool_steps T D I T' D' → fair_div_tc T' D' → fair_div_tc T D.
  Proof.
    intros Hsteps; destruct 1 as [J T''' D''' Hne Hsteps'' Hdiv''].
    econstructor; [|by eapply fair_pool_steps_concat|done].
    destruct I; simpl; naive_solver.
  Qed.

  Lemma fair_div_alt_fair_div_tc T:
    fair_div_alt T → ∃ D, fair_div_tc T D.
  Proof.
    intros Div. exists (fair_div_alt_delays T Div).
    revert T Div; cofix IH; intros T Div.
    destruct (fair_div_alt_inv T Div) as (T' & Div' & I & Hne & Hsteps).
    destruct I as [|i I]; first naive_solver.
    inversion Hsteps as [|? T_mid ?? D_mid ? ? ? Hdel Hstep Hsteps']; subst.
    econstructor; eauto.
  Qed.

  Lemma fair_div_tc_fair_div T D:
    fair_div_tc T D → fair_div T D.
  Proof.
    revert T D; cofix IH; intros T D.
    destruct 1 as [I T' D' Hne Hsteps Hdiv].
    destruct Hsteps as [|T T' T'' D D' D'' i I Hdel Hstep Hsteps]; first naive_solver.
    econstructor; eauto. eapply IH, fair_div_tc_insert_steps, Hdiv. done.
  Qed.


  Theorem fair_div_iff T:
    fair_div_alt T ↔ (∃ D, fair_div T D).
  Proof.
    split.
    - intros [D HD]%fair_div_alt_fair_div_tc.
      eapply fair_div_tc_fair_div in HD; by exists D.
    - intros [D HD]. by eapply fair_div_fair_div_alt.
  Qed.

End language_setup.
