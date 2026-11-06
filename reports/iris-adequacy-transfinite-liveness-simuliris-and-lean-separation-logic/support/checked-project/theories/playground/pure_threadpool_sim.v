From iris.prelude Require Import prelude.
From simuliris.playground Require Import fixpoints language.
From stdpp Require Import gmap.

Section fair_termination_preservation.

  Context `{Language}.
  Implicit Types (e: expr) (T: list expr) (I: list nat) (O: gset nat) (D: delays) (P: pool).

  (* Per-Thread Simulation *)
  Definition sim_expr_inner (outer: relation expr) (inner: relation expr) (e_t e_s: expr) :=
    (* value case *)
    (val e_t ∧ ∃ e_s', steps_no_fork e_s e_s' ∧ val e_s') ∨
    (* target step case *)
    ((∃ e_t' T_t, step e_t e_t' T_t) ∧
     (∀ e_t' T_t, step e_t e_t' T_t →
      (* stuttering *)
      (T_t = [] ∧ inner e_t' e_s) ∨
      (* no stuttering *)
      (∃ e_s' e_s'' T_s,
        steps_no_fork e_s e_s' ∧
        step e_s' e_s'' T_s ∧
        length T_t = length T_s ∧
        ∀ e_t e_s, (e_t, e_s) ∈ zip (e_t' :: T_t) (e_s'' :: T_s) → outer e_t e_s)
    )).

  Definition sim_expr_body outer := lfp (sim_expr_inner outer).
  Definition sim_expr := gfp sim_expr_body.

  Lemma sim_expr_inner_strong_mono outer outer' inner inner':
    outer ⪯ outer' →
    inner ⪯ inner' →
    sim_expr_inner outer inner ⪯ sim_expr_inner outer' inner'.
  Proof.
    intros Houter Hinner e_t e_s; rewrite /sim_expr_inner.
    intros [Val|[CanStep AllSteps]]; first by eauto.
    right; split; first done.
    intros e_t' T_t Hstep.
    destruct (AllSteps e_t' T_t Hstep) as [Stutter|NoStutter].
    - left; destruct Stutter; split; first done.
      by eapply Hinner.
    - destruct NoStutter as (e_s' & e_s'' & T_s & Hfrk & Hlen & Hstep' & Hall).
      right; exists e_s', e_s'', T_s; repeat split; [by eauto..|].
      intros ???. by eapply Houter, Hall.
  Qed.

  Instance sim_expr_inner_mono outer: Mono (sim_expr_inner outer).
  Proof.
    split; intros sim sim' Hsim. by eapply sim_expr_inner_strong_mono.
  Qed.

  Instance sim_expr_body_mono: Mono sim_expr_body.
  Proof.
    split; intros sim sim' Hsim.
    rewrite /sim_expr_body.
    eapply lfp_mono; first apply _.
    intros inner; by eapply sim_expr_inner_strong_mono.
  Qed.

  Lemma sim_expr_body_unfold sim e_t e_s:
    sim_expr_body sim e_t e_s ↔
    sim_expr_inner sim (sim_expr_body sim) e_t e_s.
  Proof.
    revert e_t e_s; change (sim_expr_body sim ≡ sim_expr_inner sim (sim_expr_body sim)).
    eapply lfp_fixpoint, _.
  Qed.

  Lemma sim_expr_unfold e_t e_s:
    sim_expr e_t e_s ↔
    sim_expr_body sim_expr e_t e_s.
  Proof.
    revert e_t e_s; change (sim_expr ≡ sim_expr_body sim_expr).
    eapply gfp_fixpoint, _.
  Qed.

  Lemma sim_expr_fixpoint e_t e_s:
    sim_expr e_t e_s ↔
    sim_expr_inner sim_expr sim_expr e_t e_s.
  Proof.
    rewrite sim_expr_unfold sim_expr_body_unfold.
    revert e_t e_s; change (sim_expr_inner sim_expr (sim_expr_body sim_expr) ≡ sim_expr_inner sim_expr sim_expr).
    eapply anti_symm; first apply lattice_anti_symm; eapply sim_expr_inner_strong_mono.
    - reflexivity.
    - intros ??; by rewrite sim_expr_unfold.
    - reflexivity.
    - intros ??; by rewrite sim_expr_unfold.
  Qed.

  (* inversion lemmas *)
  Lemma sim_expr_inv_val e_s e_t:
    sim_expr e_t e_s →
    val e_t →
    ∃ e_s', steps_no_fork e_s e_s' ∧ val e_s'.
  Proof.
    rewrite sim_expr_unfold sim_expr_body_unfold /sim_expr_inner.
    intros [[Ht Hs]|Hstep] Hval; first done.
    destruct Hstep as [Hstep _]. eapply val_no_step in Hstep; naive_solver.
  Qed.

  Lemma sim_expr_inv_step e_s e_t e_t' T_t:
    sim_expr e_t e_s → step e_t e_t' T_t →
    T_t = [] ∧ sim_expr e_t' e_s ∨
    ∃ e_s' e_s'' T_s,
      steps_no_fork e_s e_s' ∧
      step e_s' e_s'' T_s ∧
      length T_t = length T_s ∧
      ∀ e_t e_s, (e_t, e_s) ∈ zip (e_t' :: T_t) (e_s'' :: T_s) → sim_expr e_t e_s.
  Proof.
    rewrite sim_expr_fixpoint /sim_expr_inner.
    intros [[Ht Hs]|Hstep] Htgt; first (exfalso; eapply val_no_step; [apply Ht|]; eauto).
    destruct Hstep as [_ Hstep]. destruct (Hstep _ _ Htgt) as [[-> Hsim]|].
    - left. split; done.
    - right. eauto.
  Qed.

  (* the introduction lemmas *)
  Lemma sim_expr_intro_vals e_s e_t:
    val e_t →
    val e_s →
    sim_expr e_t e_s.
  Proof.
    intros V1 V2.
    rewrite sim_expr_fixpoint /sim_expr_inner.
    left. split; first done.
    exists e_s; split; last done.
    rewrite /steps_no_fork; reflexivity.
  Qed.

  Lemma sim_expr_intro_step e_s e_t:
    (∃ e_t' T_t, step e_t e_t' T_t) →
    (∀ e_t' T_t, step e_t e_t' T_t →
     ∃ e_s' T_s, step e_s e_s' T_s ∧
     length T_s = length T_t ∧
     ∀ e_t e_s, (e_t, e_s) ∈ zip (e_t' :: T_t) (e_s' :: T_s) → sim_expr e_t e_s) →
    sim_expr e_t e_s.
  Proof.
    intros CanStep NoStutter.
    rewrite sim_expr_fixpoint /sim_expr_inner.
    right. split; first done.
    intros e_t' T_t Hstep.
    right. destruct (NoStutter e_t' T_t Hstep) as (e_s' & T_s & Hstep' & Hlen & Hall).
    exists e_s, e_s', T_s; split; first by (rewrite /steps_no_fork; reflexivity).
    eauto.
  Qed.

  Lemma sim_expr_intro_stutter_source e_s e_t:
    (∃ e_t' T_f, step e_t e_t' T_f) →
    (∀ e_t' T_f, step e_t e_t' T_f → T_f = [] ∧ sim_expr e_t' e_s) →
    sim_expr e_t e_s.
  Proof.
    intros CanStep Stutter.
    rewrite sim_expr_fixpoint /sim_expr_inner.
    right. split; first done.
    intros e_t' T_t Hstep; eauto.
  Qed.

  Lemma sim_expr_intro_stutter_target e_s e_s' e_t:
    step_no_fork e_s e_s' →
    sim_expr e_t e_s' →
    sim_expr e_t e_s.
  Proof.
    rewrite sim_expr_fixpoint /sim_expr_inner.
    intros Hfrk Hsim. destruct Hsim as [Vals|[CanStep AllSteps]].
    - rewrite sim_expr_fixpoint /sim_expr_inner.
      destruct Vals as (val_t & e_s'' & Hsteps & val_s).
      left. split; first done. exists e_s''.
      split; last done. eapply rtc_l; eauto.
    - rewrite sim_expr_fixpoint /sim_expr_inner.
      right. split; first done.
      intros e_t' T_t' Hstep. right.
      destruct (AllSteps e_t' T_t' Hstep) as [Stutter|NoStutter].
      + destruct Stutter as [-> Hsim].
        exists e_s, e_s', []. split; first by (rewrite /steps_no_fork; reflexivity).
        split; first done. split; first done.
        simpl. set_solver.
      + destruct NoStutter as (e_s'' & e_s''' & T_s & Hfrk' & Hstep' & Hlen & Hall).
        exists e_s'', e_s''', T_s. split; first by eapply rtc_l.
        split; first done. split; first done.
        done.
  Qed.

  (* Thread Pool Simulation *)

  Definition all_values (O: gset nat) P :=
    (∀ i , i ∈ O → ∃ e_t e_s, P !! i = Some (e_t, e_s) ∧ val e_t ∧ val e_s).

  Definition must_step (post: pool → Prop) (must_step: pool → gset nat → delays → Prop) (P: pool) (O: gset nat) (D: delays) :=
    delays_for P.(tgt) D →
    (all_values O P ∧ post P) ∨
    (* steps in the source *)
    (∃ P' I, pool_steps P.(src) I P'.(src) ∧ P'.(tgt) = P.(tgt) ∧ must_step P' (O ∖ list_to_set I) D) ∨
    (* steps in the target and source *)
    ((∃ T_t' i, pool_step P.(tgt) i T_t') ∧
     (∀ T_t' D' i, fair_pool_step P.(tgt) D i T_t' D' →
      ∃ P' I, P'.(tgt) = T_t' ∧
        pool_steps P.(src) I P'.(src) ∧
        must_step P' (O ∖ list_to_set I) D'
  )).

  Definition sim_pool_body (sim_pool: pool → Prop) (P: pool) :=
    ∀ D, lfp (must_step sim_pool) P (threads P.(tgt)) D.

  Definition sim_pool := gfp sim_pool_body.

  Lemma must_step_strong_mono (sim_pool sim_pool': pool → Prop) (rec rec': pool → gset nat → delays → Prop):
    sim_pool ⪯ sim_pool' →
    rec ⪯ rec' →
    must_step sim_pool rec ⪯ must_step sim_pool' rec'.
  Proof.
    intros Hpool Hrec P O D; rewrite /must_step.
    intros Hmust Hdel. destruct (Hmust Hdel) as [Values|[Stutter|Step]].
    - left; destruct Values; split; first eauto. by eapply Hpool.
    - right. left. destruct Stutter as (P' & I & Hsteps & Heq & HP').
      exists P', I. repeat split; eauto. by eapply Hrec.
    - right. right. destruct Step as [? Step]; split; first done.
      intros T_t' D' i Hstep.
      destruct (Step T_t' D' i Hstep) as (P' & I & Heq & Hsteps & HP).
      exists P', I. repeat split; auto.
      by eapply Hrec.
  Qed.

  Instance must_step_mono Φ: Mono (must_step Φ).
  Proof.
    split; intros ???; by eapply must_step_strong_mono.
  Qed.

  Instance sim_pool_mono: Mono sim_pool_body.
  Proof.
    split; intros sim_pool sim_pool' Hpool.
    rewrite /sim_pool_body. intros P Hlfp D.
    specialize (Hlfp D). revert Hlfp.
    revert D. generalize (threads P.(tgt)) as O.
    revert P. change (lfp (must_step sim_pool) ⪯ lfp (must_step sim_pool')).
    eapply lfp_mono; first apply _.
    intros rec. by eapply must_step_strong_mono.
  Qed.

(* proof structure:
  co-induction on the outer fixpoint
    we need to show that sim_expr_all is a post-fixpoint.
    induction on the set of threads
    + base case trivial
    + step case: let i be the new thread and IH the inductive hypothesis.
      induction on the least fixpoint of i
      * value case:
          - target is a value, source steps to a value.
            we can remove i and we are done with IH
      * step case:
          (we can step ∧ (we stuttered or we took a proper step))
          induction on the delay unil thread i is stepped again
          let j be the next thread that steps
          -- if j = i and we stuttered the source, then the claim follows from the lfp
          -- if j = i and we did not stutter, we can remove i and the claim follows
          -- if j ≠ i, then any step will decrease the delay of i.
             The claim follows with the IH for d.
*)

Definition sim_expr_all P := (∀ e_t e_s, (e_t, e_s) ∈ P → sim_expr e_t e_s).
Notation local_all := (lfp (must_step sim_expr_all)).


Lemma local_all_add_values P O O' D:
  local_all P O D →
  (∀ i, i ∈ O' → i ∈ O ∨ ∃ e_t e_s, P !! i = Some (e_t, e_s) ∧ val e_t ∧ val e_s) →
  local_all P O' D.
Proof.
  intros Hall; revert P O D Hall O'.
  change (local_all ⪯ λ P O D, ∀ O' : gset nat,
    (∀ i : nat, i ∈ O' → i ∈ O ∨ ∃ e_t e_s, P !! i = Some (e_t, e_s) ∧ val e_t ∧ val e_s)
    → local_all P O' D).
  eapply lfp_least_pre_fixpoint; intros P O D Hsim O' Hel.
  rewrite lfp_fixpoint {1}/must_step.
  intros Hdel. specialize (Hsim Hdel) as [Base|[Stutter|Step]].
  - left. destruct Base as [Base ?]; split; last done.
    intros i Hi. destruct (Hel _ Hi) as [?|(? & ? & Hlook & ? & ?)]; eauto.
  - right. left.  destruct Stutter as (P' & I & Hsteps & Htgt & IH).
    exists P', I. split; first done. split; first done.
    eapply IH. intros i [Hi Hni]%elem_of_difference.
    destruct (Hel _ Hi) as [|Hvals]; first set_solver.
    right. destruct Hvals as (e_t & e_s & Hlook & val_t & val_s).
    exists e_t, e_s. split; last done.
    eapply (pool_steps_value_preservation _ _ i) in Hsteps; [|by eauto|]; last first.
    { rewrite list_lookup_fmap Hlook //. }
    assert (P'.(tgt) !! i = Some e_t) as Htgt_look.
    { rewrite Htgt list_lookup_fmap Hlook //. }
    revert Hsteps Htgt_look.
    rewrite !list_lookup_fmap.
    destruct (P' !! i) as [[]|]; simpl; naive_solver.
  - right. right. destruct Step as [? Step]; split; first done.
    intros T_t' D' i Hstep. destruct (Step T_t' D' i Hstep) as (P' & I & Heq & Hsteps & Hpost).
    exists P', I. split; first done. split; first done.
    eapply Hpost. intros j Hj. eapply elem_of_difference in Hj as [Hj HI].
    destruct (Hel _ Hj) as [?|Hvals].
    { left; eapply elem_of_difference; eauto. }
    right. destruct Hvals as (e_t & e_s & Hlook & val_t & val_s).
    exists e_t, e_s; split; last eauto.
    eapply pool_steps_value_preservation in Hsteps; [|by apply val_s| by erewrite list_lookup_fmap, Hlook].
    rewrite -Heq in Hstep. inversion Hstep as [????? Hstep' ?]; subst.
    eapply pool_step_value_preservation in Hstep'; [|by apply val_t| by erewrite list_lookup_fmap, Hlook].
    revert Hsteps Hstep'. rewrite !list_lookup_fmap.
    destruct (P' !! j) as [[??]|]; simpl; naive_solver.
Qed.

Lemma local_all_weaken P O O' D:
  local_all P O D →
  O' ⊆ O →
  local_all P O' D.
Proof.
  intros H1 H2. eapply local_all_add_values; first done.
  naive_solver.
Qed.

Lemma local_all_delay_for P O D:
  (delays_for P.(tgt) D → local_all P O D) → local_all P O D.
Proof.
  rewrite lfp_fixpoint.
  rewrite /must_step; intros Hstep Hdel; eapply (Hstep Hdel Hdel).
Qed.


Lemma sim_expr_all_insert P i e_t e_s:
  sim_expr_all P →
  sim_expr e_t e_s →
  sim_expr_all (<[i:=(e_t, e_s)]> P).
Proof.
  intros Hall Hsim e_t' e_s' Hin.
  eapply list_elem_of_lookup_1 in Hin as [j Hlook].
  eapply list_lookup_insert_Some in Hlook as [(-> & Heq & _)|(Hne & Hlook)].
  - naive_solver.
  - by eapply Hall, list_elem_of_lookup_2.
Qed.

Lemma sim_expr_all_app P P' :
  sim_expr_all P →
  sim_expr_all P' →
  sim_expr_all (P ++ P').
Proof.
  intros HP HP' e_t e_s [|]%elem_of_app; eauto.
Qed.


Lemma local_all_intro_source P P' I O D:
  pool_steps P.(src) I P'.(src) →
  P'.(tgt) = P.(tgt) →
  local_all P' (O ∖ list_to_set I) D →
  local_all P O D.
Proof.
  intros Hsteps Heq Hlocal.
  rewrite lfp_fixpoint {1}/must_step.
  intros Hdel. right. left.
  exists P', I. repeat split; done.
Qed.

Lemma local_all_intro_target_and_source P O D:
  (∃ T_t' i, pool_step P.(tgt) i T_t') →
  (∀ T_t' D' i,
    delays_for P.(tgt) D →
    fair_pool_step P.(tgt) D i T_t' D' →
   ∃ P' I, P'.(tgt) = T_t' ∧
   pool_steps P.(src) I P'.(src) ∧
   local_all P' (O ∖ list_to_set I) D') →
  local_all P O D.
Proof.
  intros CanStep Post.
  rewrite lfp_fixpoint {1}/must_step.
  intros Hdel. right. right. split; eauto.
Qed.


Lemma local_all_stutter_target P P' I O D:
  pool_steps P.(src) I P'.(src) →
  P'.(tgt) = P.(tgt) →
  local_all P' O D →
  local_all P O D.
Proof.
  intros Hsteps Heq Hlocal. eapply local_all_intro_source; eauto.
  eapply local_all_weaken; first done. set_solver.
Qed.


Lemma local_all_stutter_target_no_fork P j e_t e_s e_s' O D:
  P !! j = Some (e_t, e_s) →
  step_no_fork e_s e_s' →
  local_all (<[j := (e_t, e_s')]> P) (O ∖ {[j]}) D →
  local_all P O D.
Proof.
  intros Hlook Hstep Hlocal.
  eapply (local_all_intro_source _ (<[j := (e_t, e_s')]> P) [j]).
  - rewrite list_fmap_insert //=. eapply pool_steps_single, pool_step_iff.
    exists e_s, e_s', []. split; first done. split; first rewrite list_lookup_fmap Hlook //.
    by rewrite right_id.
  - rewrite list_fmap_insert //= list_insert_id // list_lookup_fmap Hlook //.
  - eapply local_all_weaken; eauto. set_solver.
Qed.


Lemma local_all_stutter_target_no_forks P j e_t e_s e_s' O D:
  P !! j = Some (e_t, e_s) →
  steps_no_fork e_s e_s' →
  local_all (<[j := (e_t, e_s')]> P) O D →
  local_all P O D.
Proof.
  intros Hlook Hsteps. revert P Hlook. induction Hsteps as [e_s|e_s e_s' e_s'' Hstep Hsteps IH]; intros P Hlook.
  - rewrite list_insert_id //.
  - intros Hlocal. eapply local_all_stutter_target_no_fork; eauto.
    eapply (local_all_weaken _ O); last set_solver.
    eapply IH.
    + eapply list_lookup_insert_eq, lookup_lt_Some, Hlook.
    + by rewrite list_insert_insert_eq.
Qed.



Lemma local_all_stutter_source' i e_t e_t' e_s P O D' T_t':
  T_t' = <[i := e_t']> P.(tgt) →
  P !! i = Some (e_t, e_s) →
  local_all (<[i := (e_t', e_s)]> P) O D' →
  ∃ P' I, P'.(tgt) = T_t' ∧ pool_steps P.(src) I P'.(src) ∧ local_all P' (O ∖ list_to_set I) D'.
Proof.
  intros Hupd Hlook Hall; exists (<[i := (e_t', e_s)]> P), [].
  rewrite !list_fmap_insert; split; first done.
  rewrite list_insert_id; last rewrite list_lookup_fmap Hlook //.
  split; first constructor. eapply local_all_weaken; eauto. set_solver.
Qed.


Lemma no_forks_pool_step e e' T j:
  step_no_fork e e' →
  T !! j = Some e →
  pool_step T j (<[j := e']> T).
Proof.
  intros H1 H2; eapply pool_step_iff.
  exists e, e', []; split; repeat split; eauto.
  by rewrite right_id.
Qed.


Lemma no_forks_pool_steps e e' T j:
  steps_no_fork e e' →
  T !! j = Some e →
  ∃ I, pool_steps T I (<[j := e']> T).
Proof.
  induction 1 as [e|e e' e'' Hstep Hsteps IH] in T.
  - intros Hlook. exists []. rewrite list_insert_id //. constructor.
  - intros Hlook. eapply no_forks_pool_step in Hstep; last done.
    destruct (IH (<[j := e']> T)) as (I & Hsteps').
    { eapply list_lookup_insert_eq, lookup_lt_Some, Hlook. }
    exists (j :: I).  econstructor; eauto.
    revert Hsteps'; by rewrite list_insert_insert_eq.
Qed.

Lemma local_all_not_stuttered i e_t e_t' e_s e_s' e_s'' P O D' T_t' T_f_s T_f_t:
  T_t' = <[i := e_t']> P.(tgt) ++ T_f_t →
  P !! i = Some (e_t, e_s) →
  steps_no_fork e_s e_s' →
  step e_s' e_s'' T_f_s →
  length T_f_t = length T_f_s →
  local_all (<[i := (e_t', e_s'')]> P ++ zip T_f_t T_f_s) (O ∖ {[i]}) D' →
  ∃ P' I, P'.(tgt) = T_t' ∧ pool_steps P.(src) I P'.(src) ∧ local_all P' (O ∖ list_to_set I) D'.
Proof.
  intros Hupd Hlook Hfrk Hstep Hlen Hall.
  eapply (no_forks_pool_steps _ _ P.(src) i) in Hfrk as (I & Hsteps); last first.
  { rewrite list_lookup_fmap Hlook //=. }
  exists (<[i := (e_t', e_s'')]> P ++ zip T_f_t T_f_s), (I ++ [i]).
  rewrite !fmap_app fst_zip ?Hlen // snd_zip ?Hlen // !list_fmap_insert Hupd.
  split; first done.
  split; last (eapply local_all_weaken; [done|set_solver]).
  eapply pool_steps_trans; first done.
  eapply pool_steps_single, pool_step_iff.
  exists e_s', e_s'', T_f_s.
  rewrite list_insert_insert_eq list_lookup_insert_eq //.
  eapply lookup_lt_Some; rewrite list_lookup_fmap Hlook //.
Qed.

Lemma sim_expr_to_pool P:
  sim_expr_all P → sim_pool P.
Proof.
  revert P. change (sim_expr_all ⪯ sim_pool).
  eapply gfp_greatest_post_fixpoint. rewrite /sim_pool_body.
  enough (∀ O D P, sim_expr_all P → O ⊆ threads P.(tgt) → local_all P O D) by (intros ??; eauto).
  intros O; induction (set_wf O) as [O _ IHO].
  intros D P Hall Hsub.
  destruct (decide (O ≡ ∅)) as [Empty|[i Hel]%set_choose].
  - rewrite lfp_fixpoint {1}/must_step. intros Hdel.
    left. split; last done. intros i; set_solver.
  - specialize (Hsub _ Hel) as Hthread.
    eapply threads_spec in Hthread as (e & Hlook).
    eapply list_lookup_fmap_Some_1 in Hlook as ([e_t e_s] & -> & Hlook).
    assert (sim_expr e_t e_s) as Hsim by eapply Hall, list_elem_of_lookup_2, Hlook.
    revert Hsim; rewrite sim_expr_unfold /sim_expr_body; intros Hsim.
    revert e_t e_s Hsim P Hall Hlook D Hsub.
    change (lfp (sim_expr_inner sim_expr) ⪯
            λ e_t e_s, ∀ P,
              sim_expr_all P →
              P !! i = Some (e_t, e_s) →
              ∀ D, O ⊆ threads P.(tgt) → local_all P O D).
    eapply lfp_strong_ind; first apply _.
    intros e_t e_s Hinner P Hall Hlook D Hsub.
    destruct Hinner as [Val|[CanStep AllSteps]].
    + destruct Val as (val_t & e_s' & Hsteps & val_s).
      eapply local_all_stutter_target_no_forks; eauto.
      eapply (local_all_add_values _ (O∖{[i]})).
      * eapply IHO; auto; first by set_solver.
         { eauto using sim_expr_all_insert, sim_expr_intro_vals. }
         { rewrite list_fmap_insert //=. etrans; last eapply threads_update. set_solver. }
      * intros j Hj; destruct (decide (i = j)); subst; last set_solver.
         right; exists e_t, e_s'. repeat split; eauto.
         eapply list_lookup_insert_eq, lookup_lt_Some, Hlook.
    + pose proof val_no_step. assert (¬ val e_t) as Hnval by naive_solver.
      eapply local_all_delay_for; intros Hdom.
      destruct (Hdom i) as [d HD]; last clear Hdom.
      { apply active_threads_spec. eapply Hsub in Hel. eapply threads_spec in Hel.
        destruct Hel as [e Hel]. exists e. revert Hel.
        rewrite list_lookup_fmap Hlook //=. naive_solver.
      }
      revert D P HD Hsub Hall Hlook.
      induction (lt_wf d) as [d _ IHd].
      intros D P HD Hsub Hall Hlook.
      eapply local_all_intro_target_and_source.
      { destruct CanStep as (e' & T_f & Hstep).
        exists (<[i := e']> P.(tgt) ++ T_f), i.
        eapply pool_step_iff. do 3 eexists; split; first eauto.
        split; last done. by rewrite list_lookup_fmap Hlook. }
      intros T_t' D' j Hdel Hpool.
      eapply fair_pool_step_inv in Hpool as (e_j_t & e_j_t' & T_f  & Htgt & Hlookj & Hupd & Hdecr).
      destruct (decide (i = j)).
      * subst j. rewrite list_lookup_fmap Hlook //= in Hlookj.
        assert (e_j_t = e_t) as -> by congruence; clear Hlookj.
        rename e_j_t' into e_t'. destruct (AllSteps _ _ Htgt) as [[-> Steps]|NoStutter].
        -- eapply id in Steps as Steps'. (* FIXME: this step is not linear, but we should be able to make it linear *)
           revert Steps Steps'; rewrite {1}meet_left meet_right.
           intros IH Hsim. change (lfp _ _ _) with (sim_expr_body sim_expr e_t' e_s) in Hsim.
           revert Hsim; rewrite -sim_expr_unfold; intros Hsim.
           rewrite right_id in Hupd.
           eapply local_all_stutter_source'; eauto.
           eapply IH; eauto using sim_expr_all_insert, list_lookup_insert_eq, lookup_lt_Some.
           etrans; first eapply Hsub.
           rewrite list_fmap_insert; eapply threads_update.
        -- destruct NoStutter as (e_s' & e_s'' & T_s & Hfrk & Hsrc & Hlen & Hsims).
           eapply local_all_not_stuttered; eauto.
           eapply IHO; first set_solver; last first.
           { rewrite fmap_app list_fmap_insert.
            etrans; last eapply threads_weaken.
            etrans; last eapply threads_update.
            set_solver. }
           eapply sim_expr_all_app; first eapply sim_expr_all_insert.
           { done. }
           { eapply Hsims; simpl; set_solver. }
           { intros ???; eapply Hsims; simpl; set_solver. }
        * eapply list_lookup_fmap_Some_1 in Hlookj as ([e_j_t_ e_j_s] & -> & Hlookj).
          rename e_j_t_ into e_j_t; simpl in Htgt.
          assert (sim_expr e_j_t e_j_s) as Hsim by eapply Hall, list_elem_of_lookup_2, Hlookj.
          eapply id in HD as HD'.
          eapply Hdecr in HD' as (m & -> & HD'); last done.
          eapply sim_expr_inv_step in Hsim as [Stutter|NoStutter]; last done.
          -- destruct Stutter as [-> Hsim].
             eapply local_all_stutter_source'; [by rewrite right_id in Hupd|done|].
             eapply IHd; eauto using sim_expr_all_insert.
             { rewrite list_fmap_insert; by etrans; last eapply threads_update. }
             { rewrite list_lookup_insert_ne //. }
          -- destruct NoStutter as (e_j_s' & e_j_s'' & T_s & Hfrk & Hsrc & Hlen & Hsims).
             eapply local_all_not_stuttered; eauto.
             eapply (local_all_weaken _ O); last set_solver.
             eapply IHd; eauto.
             { rewrite fmap_app list_fmap_insert.
               etrans; last eapply threads_weaken.
               etrans; last eapply threads_update.
               done. }
            { eapply sim_expr_all_app; first eapply sim_expr_all_insert.
              - done.
              - eapply Hsims; simpl; set_solver.
              - intros ???; eapply Hsims; simpl; set_solver. }
            { eapply lookup_app_l_Some. by rewrite list_lookup_insert_ne. }
Qed.


Lemma pool_steps_concat T I T' J T''':
  pool_steps T I T' → pool_steps T' J T''' →  pool_steps T (I ++ J) T'''.
Proof.
induction 1 as [T|T T' T'' i I Hstep Hsteps IH]; simpl; eauto.
intros Hsteps'%IH. econstructor; eauto.
Qed.

Lemma no_magic_values_step (i: nat) T j T':
  pool_step T j T' →
  i ∈ active_threads T →
  i ∉ active_threads T' →
  i = j.
Proof.
  intros (e & e' & T_f & Hstep & Hlook & ->)%pool_step_iff.
  intros (e'' & Hlook' & Hnval)%active_threads_spec Hnact.
  destruct (decide (i = j)); first eauto.
  exfalso. eapply Hnact, active_threads_spec. exists e''.
  split; last done. eapply lookup_app_l_Some.
  rewrite list_lookup_insert_ne //.
Qed.

Lemma no_magic_values_steps (i: nat) T I T':
  pool_steps T I T' →
  i ∈ active_threads T →
  i ∉ active_threads T' →
  i ∈ (list_to_set I: gset nat).
Proof.
  induction 1 as [|T T' T'' j I Hstep Hsteps]; first naive_solver.
  intros Hact Hnact. destruct (decide (i ∈ active_threads T')); first set_solver.
  eapply no_magic_values_step in Hstep; eauto; subst; set_solver.
Qed.

Lemma lookup_pool P j e_t e_s:
  P.(tgt) !! j = Some e_t → P.(src) !! j = Some e_s → P !! j = Some (e_t, e_s).
Proof.
  rewrite !list_lookup_fmap; destruct (P !! j) as [[]|]; simpl; naive_solver.
Qed.

Lemma sim_pool_unfold_fair_div P D:
  fair_div P.(tgt) D →
  sim_pool P →
  ∃ P' D' I, sim_pool P' ∧
           fair_div P'.(tgt) D' ∧
           pool_steps P.(src) I P'.(src) ∧
           (all_values (threads P.(src) ∖ list_to_set I) P') ∧
           filter (λ i, i ∈ active_threads P.(src)) (threads P.(src)) ⊆ list_to_set I.
Proof.
  intros Hfair. rewrite /sim_pool.
  rewrite {1}gfp_fixpoint. fold sim_pool. rewrite /sim_pool_body.
  intros Hlfp; specialize (Hlfp D).
  revert Hlfp. rewrite threads_src_tgt. generalize (threads P.(src)) as O.
  intros O Hlfp. revert P O D Hlfp Hfair.
  change (lfp (must_step sim_pool) ⪯
    λ P O D, fair_div P.(tgt) D → ∃ P' D' I,
        sim_pool P' ∧ fair_div P'.(tgt) D' ∧ pool_steps P.(src) I P'.(src) ∧
        (all_values (O ∖ list_to_set I) P') ∧
        filter (λ i : nat, i ∈ active_threads P.(src)) O ⊆ list_to_set I).
  eapply lfp_least_pre_fixpoint; intros P O D MustStep Hfair.
  destruct Hfair as [i T' D' Hstep Hdel Hfair].
  destruct (MustStep Hdel) as [Values|[Stutter|[CanStep AllSteps]]]; clear MustStep.
  - destruct Values as [Hvalues Hsim]; exists P, D, []. split; first done.
    split; first (econstructor; eauto).
    split; first constructor. split.
    + simpl. intros ??; eapply Hvalues. set_solver.
    + intros j Hj. eapply elem_of_filter in Hj as [Hact HO].
      eapply active_threads_spec in Hact as (e & Hlook & Hnval).
      eapply Hvalues in HO as (e_t & e_s' & Hlook' & Hval1 & Hval2).
      revert Hlook. rewrite list_lookup_fmap Hlook'; simpl; naive_solver.
  - destruct Stutter as (P' & I & Hsteps & Htgt & IH).
    rewrite Htgt in IH. assert (fair_div P.(tgt) D) as Hfair' by (econstructor; eauto).
    destruct (IH Hfair') as (P'' & D'' & I' &  Hpool & Hfair'' & Hsteps' & Hvalues & Hfilter).
    exists P'', D'', (I ++ I'); split; first done. split; first done.
    split; first by eapply pool_steps_concat. split.
    + intros j Hj. eapply Hvalues. set_solver.
    + rewrite list_to_set_app.
      intros j [Hact Hj]%elem_of_filter.
      destruct (decide (j ∈ (list_to_set I: gset nat))); first by set_solver.
      destruct (decide (j ∈ active_threads P'.*2)).
      { eapply elem_of_union_r, Hfilter, elem_of_filter. set_solver. }
      eapply elem_of_union_l, no_magic_values_steps; eauto.
  - specialize (AllSteps _ _ _ Hstep) as (P' & I & <- & Hpool & Post).
    destruct (Post Hfair) as (P'' & D'' & I' & Hpool' & Hfair' & Hsteps & Hvalues & Hfilter).
    exists P'', D'', (I ++ I'). split; first done.
    split; first done.
    split; first by eapply pool_steps_concat. split.
    + intros ??; eapply Hvalues; set_solver.
    + rewrite list_to_set_app.
      intros j [Hact Hj]%elem_of_filter.
      destruct (decide (j ∈ (list_to_set I: gset nat))); first by set_solver.
      destruct (decide (j ∈ active_threads P'.*2)).
      { eapply elem_of_union_r, Hfilter, elem_of_filter. set_solver. }
      eapply elem_of_union_l, no_magic_values_steps; eauto.
Qed.


Lemma fair_div_must_take_steps P P' D I:
  fair_div P'.(tgt) D →
  pool_steps P.(src) I P'.(src) →
  all_values (threads P.(src) ∖ list_to_set I) P' →
  ∃ j, j ∈ I.
Proof.
  intros Hfair Hsteps Hvalues.
  destruct I; last by set_solver.
  inversion Hsteps as [T H1 H2 Heq|]; subst; clear H2.
  destruct Hfair as [j T'' D'' Hstep Hdel Hfair'].
  eapply fair_pool_step_inv in Hstep as (e & e' & T_f & Hstep & Hlook & -> & ?).
  exfalso. eapply val_no_step; eauto.
  destruct (Hvalues j) as (e_t & e_s & Hlook' & Hval1 & Hval2).
  { rewrite Heq -threads_src_tgt //= difference_empty threads_spec; eauto. }
  revert Hlook Hval1.
  rewrite list_lookup_fmap Hlook' //=. naive_solver.
Qed.


Lemma fair_div_forces_active_source P P' D I:
  fair_div P'.(tgt) D →
  pool_steps P.(src) I P'.(src) →
  all_values (threads P.(src) ∖ list_to_set I) P' →
  ∃ j, j ∈ active_threads P.(src).
Proof.
  intros Hfair Hsteps Hvalues.
  destruct (fair_div_must_take_steps P P' D I) as [i Hi]; eauto.
  inversion Hsteps as [|T T' T'' j J Hstep Hsteps']; subst; first set_solver.
  eapply pool_step_iff in Hstep as (e & e' & T_f & Hstep & Hlook & ->).
  exists j. eapply active_threads_spec.
  exists e; split; first done. intros ?; eapply val_no_step; eauto.
Qed.


Lemma sim_pool_val_or_step P D:
  fair_div P.(tgt) D →
  sim_pool P →
  ∃ P' D' I, sim_pool P' ∧
           fair_div P'.(tgt) D' ∧
           pool_steps P.(src) I P'.(src) ∧
           ∅ ⊂ active_threads P.(src) ⊆ list_to_set I.
Proof.
  intros Hfair Hpool.
  edestruct (sim_pool_unfold_fair_div P D Hfair Hpool) as (P' & D' & I & Hpool' & Hdiv & Hsteps & Hvalues & Hfilter).
  exists P', D', I. do 3 (split; first done).
  revert Hfilter; assert (filter (λ i : nat, i ∈ active_threads P.*2) (threads P.*2) = active_threads P.(src)) as ->.
  { eapply leibniz_equiv. intros j.
    rewrite elem_of_filter threads_spec active_threads_spec.
    naive_solver. }
  intros Hsub; split; last done.
  enough (∃ j, j ∈ active_threads P.(src)) as [j Hj] by set_solver.
  by eapply fair_div_forces_active_source.
Qed.

Lemma sim_pool_fair_div_alt P D:
  fair_div P.(tgt) D →
  sim_pool P →
  fair_div_alt P.(src).
Proof.
  revert P D; cofix IH. intros P D Hfair Hsim.
  destruct (sim_pool_val_or_step _ _ Hfair Hsim) as (P' & D' & I & Hsim' & Hfair' & Hsteps & Hsub).
  econstructor; eauto.
Qed.


Lemma sim_pool_preserves_fair_termination P D:
  fair_div P.(tgt) D →
  sim_pool P →
  ∃ D, fair_div P.(src) D.
Proof.
  intros ??; by eapply fair_div_iff, sim_pool_fair_div_alt.
Qed.

Lemma sim_expr_all_preserves_fair_termination P D:
  fair_div P.(tgt) D →
  sim_expr_all P →
  ∃ D, fair_div P.(src) D.
Proof.
  intros ??; by eapply sim_pool_preserves_fair_termination, sim_expr_to_pool.
Qed.



End fair_termination_preservation.
