From stdpp Require Import gmap.
From iris.bi Require Import bi fixpoint_mono.
From iris.algebra Require Import gset gmap list.
From iris.proofmode Require Import proofmode.
From simuliris.simulation Require Import language fairness.
From simuliris.simulation Require Export slsls closed_sim.
From simuliris.logic Require Import satisfiable.
Import bi.

Section fix_lang.
Context {PROP : bi} `{!BiBUpd PROP, !BiAffine PROP, !BiPureForall PROP, !BiPersistentlyForall PROP}.
Context {Λ : language}.
Context {s : simulirisGS PROP Λ}.

Set Default Proof Using "Type*".

Implicit Types
  (e_s e_t e: expr Λ)
  (p_s p_t p: prog Λ)
  (P: list (expr Λ * expr Λ))
  (O: gset nat)
  (I J: list nat)
  (D: gmap nat nat)
  (i j k: nat)
  (σ_s σ_t σ : state Λ).

(* Language Setup *)
Notation "P '.(tgt)'" := (P.*1) (at level 1).
Notation "P '.(src)'" := (P.*2) (at level 1).


Definition all_values O P :=
  (∀ i , i ∈ O → ∃ v_t v_s, P !! i = Some (of_val v_t, of_val v_s)).

Definition must_step_inner (post: list (expr Λ * expr Λ) → PROP) (must_step: list (expr Λ * expr Λ) → gset nat → gmap nat nat → PROP) (P: list (expr Λ * expr Λ)) (O: gset nat) (D: gmap nat nat) : PROP :=
  (∀ p_t σ_t p_s σ_s, state_interp p_t σ_t p_s σ_s P.(src) ∗ ⌜pool_safe p_s P.(src) σ_s⌝ ∗ ⌜delays_for P.(tgt) D⌝ ==∗
    (* the base case where every term in O must be a value *)
    (⌜all_values O P⌝ ∗ state_interp p_t σ_t p_s σ_s P.(src) ∗ post P) ∨
    (* the target can be stuttered for any finite number of steps *)
    (∃ P' σ_s' I, ⌜pool_steps p_s P.(src) σ_s I P'.(src) σ_s'⌝ ∗ ⌜P'.(tgt) = P.(tgt)⌝ ∗ state_interp p_t σ_t p_s σ_s' P'.(src) ∗ must_step P' (O ∖ list_to_set I) D) ∨
    (* the target can step, and every fair step can be replayed (or stuttered) in the source *)
    (
      (* we do not need reducibility of the target for fairness ⌜reducible_pool p_t P.(tgt) σ_t⌝ ∗ *)
      ∀ T_t' D' i σ_t', ⌜fair_pool_step p_t P.(tgt) D σ_t i T_t' D' σ_t'⌝ ==∗
      ∃ P' σ_s' I,
        ⌜P'.(tgt) = T_t'⌝ ∗
        ⌜pool_steps p_s P.(src) σ_s I P'.(src) σ_s'⌝ ∗
        state_interp p_t σ_t' p_s σ_s' P'.(src) ∗
        must_step P' (O ∖ list_to_set I) D'
    ))%I.

Definition must_step (post: list (expr Λ * expr Λ) → PROP) :=
  curry3 (bi_least_fixpoint (λ (must_step: prodO (prodO (listO (prodO exprO exprO)) (gsetO natO)) (gmapO natO natO) → PROP), uncurry3 (must_step_inner post (curry3 must_step)))).

Definition sim_pool_inner (sim_pool: list (expr Λ * expr Λ) → PROP) (P: list (expr Λ * expr Λ)) :=
  (∀ D, must_step sim_pool P (threads P.(tgt)) D)%I.

Definition sim_pool :=
  bi_greatest_fixpoint (sim_pool_inner: (listO (prodO exprO exprO) → PROP) → (listO (prodO exprO exprO) → PROP)).


Lemma must_step_inner_mono (sim_pool sim_pool': list (expr Λ * expr Λ) → PROP) (rec rec': list (expr Λ * expr Λ) → gset nat → gmap nat nat → PROP) P O D:
  (∀ P, sim_pool P -∗ sim_pool' P) -∗
  (∀ P O D, rec P O D -∗ (∀ P, sim_pool P -∗ sim_pool' P) -∗ rec' P O D) -∗
  must_step_inner sim_pool rec P O D -∗
  must_step_inner sim_pool' rec' P O D.
Proof.
  iIntros "Hpool Hrec"; rewrite /must_step_inner.
  iIntros "Hinner". iIntros (p_t σ_t p_s σ_s) "H".
  iMod ("Hinner" with "H") as "[Val|[Stutter|Step]]".
  - iModIntro. iLeft. iDestruct "Val" as "($ & $ & Hsim)". by iApply "Hpool".
  - iRight. iLeft. iDestruct "Stutter" as (P' σ I Hsteps Heq) "(HP' & Hr)".
    iModIntro. iExists P', σ, I. do 2 (iSplit; first done).
    iFrame. by iApply ("Hrec" with "Hr").
  - iRight. iRight. iModIntro. iIntros (T_t' D' i σ_t' Hstep).
    iMod ("Step" with "[//]") as (P' σ_s' I) "(Heq & Hstep & SI & Hr)".
    iModIntro. iExists P', σ_s', I. iFrame. by iApply ("Hrec" with "Hr").
Qed.

(* free NonExpansive instances *)
Local Instance free_discrete_prod_ne (Φ: prodO (prodO (listO (prodO (@exprO _ Λ) (@exprO _ Λ))) (gsetO natO)) (gmapO natO natO) → PROP):
  NonExpansive Φ.
Proof.
  by intros n [[? ?] ?] [[? ?] ?] ->%discrete_iff%leibniz_equiv; last apply _.
Qed.

Local Instance free_discrete_expr_ne (Φ: listO (prodO (@exprO _ Λ) (@exprO _ Λ)) → PROP):
  NonExpansive Φ.
Proof.
  by intros n ? ? ->%discrete_iff%leibniz_equiv; last apply _.
Qed.


Local Instance must_step_body_mono post: BiMonoPred ((λ (must_step: prodO (prodO (listO (prodO exprO exprO)) (gsetO natO)) (gmapO natO natO) → PROP), uncurry3 (must_step_inner post (curry3 must_step)))).
Proof.
  split.
  - intros M1 M2 Hne1 Hne2. iIntros "#H" ([[P O] D]). simpl.
    iApply must_step_inner_mono; first by iIntros (?) "$".
    iIntros (???) "H' _"; rewrite /curry3. by iApply "H".
  - intros Φ Hne. apply _.
Qed.

Lemma must_step_mono (sim_pool sim_pool': list (expr Λ * expr Λ) → PROP) P O D:
  (∀ P, sim_pool P -∗ sim_pool' P) -∗
  must_step sim_pool P O D -∗ must_step sim_pool' P O D.
Proof.
  rewrite /must_step {1 3}/curry3.
  iIntros "Hmon Hmust". iRevert "Hmon".
  iApply (least_fixpoint_ind _ (λ x, (∀ P, sim_pool P -∗ sim_pool' P) -∗ bi_least_fixpoint
    (λ must_step0 : prodO (prodO (listO (prodO exprO exprO)) (gsetO natO))
                      (gmapO natO natO) → PROP,
      uncurry3 (must_step_inner sim_pool' (curry3 must_step0)))
    x)%I with "[] Hmust").
  iModIntro. clear P O D. iIntros ([[P O] D]) "Hinner Hmon".
  rewrite least_fixpoint_unfold {1 3}/uncurry3.
  iApply (must_step_inner_mono with "Hmon [] Hinner").
  clear P O D. iIntros (P O D) "Hpost Hmon"; rewrite /curry3.
  by iApply "Hpost".
Qed.

Instance sim_pool_body_mono: BiMonoPred (sim_pool_inner: (listO (prodO exprO exprO) → PROP) → (listO (prodO exprO exprO) → PROP)).
Proof.
  split.
  - intros M1 M2 Hne1 Hne2. iIntros "#H" (L).
    rewrite /sim_pool_inner. iIntros "Hi" (D).
    iApply (must_step_mono with "H Hi").
  - intros ??. apply _.
Qed.

Lemma must_step_ind F sim_pool P O D:
  □ (∀ P O D, must_step_inner sim_pool F P O D -∗ F P O D) -∗
  must_step sim_pool P O D -∗ F P O D.
Proof.
  iIntros "#IH HM". iApply (least_fixpoint_iter _ (uncurry3 F: prodO (prodO (listO (prodO exprO exprO)) (gsetO natO)) (gmapO natO natO) → PROP) with "[] HM").
  iModIntro. clear P O D. iIntros ([[P O] D]). simpl.
  iIntros "H". iApply "IH".
  rewrite curry3_uncurry3. done.
Qed.

Lemma must_step_unfold R P O D:
  must_step R P O D ≡ must_step_inner R (must_step R) P O D.
Proof.
  rewrite {1}/must_step {1}/curry3.
  rewrite least_fixpoint_unfold {1}/uncurry3 //.
Qed.


Lemma sim_pool_coind F P:
  □ (∀ P D, F P -∗ must_step F P (threads P.(tgt)) D) -∗
  F P -∗ sim_pool P.
Proof.
  iIntros "#IH HF". rewrite /sim_pool.
  iApply (greatest_fixpoint_coiter _ (F: listO (prodO (@exprO _ Λ) (@exprO _ Λ)) → PROP) with "[] HF").
  iModIntro. iIntros (L) "HF". rewrite /sim_pool_inner.
  iIntros (D). by iApply "IH".
Qed.

Lemma sim_pool_unfold P:
  sim_pool P ≡ (∀ D, must_step sim_pool P (threads P.(tgt)) D)%I.
Proof.
  rewrite {1}/sim_pool greatest_fixpoint_unfold //.
Qed.

(* proof structure:
  co-induction on the outer fixpoint
    we need to show that csim_expr_all is a post-fixpoint.
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


Definition csim_expr_all π (P: list (expr Λ * expr Λ)) :=
  ([∗ list] i↦(p:_*_) ∈ P, csim_expr (lift_post (ext_rel (π + i))) (π + i) (fst p) (snd p))%I.
Notation must_step_all π := (must_step (csim_expr_all π)).


Lemma must_step_all_add_values P O O' D π:
  (∀ i, i ∈ O' → i ∈ O ∨ ∃ v_t v_s, P !! i = Some (of_val v_t, of_val v_s)) →
  must_step_all π P O D -∗
  must_step_all π P O' D.
Proof.
  intros Hall. iIntros "Hopen". iRevert (O' Hall).
  iApply (must_step_ind (λ P O D, ∀ O' : gset nat,
    ⌜∀ i, i ∈ O' → i ∈ O ∨ (∃ v_t v_s, P !! i = Some (of_val v_t, of_val v_s))⌝
    -∗ must_step_all π P O' D)%I with "[] Hopen").
  iModIntro. clear P O D. iIntros (P O D) "Hinner".
  iIntros (O' Hel). rewrite must_step_unfold.
  iIntros (p_t σ_t p_s σ_s) "H".
  iMod ("Hinner" with "H") as "[Base|[Stutter|Step]]"; iModIntro.
  - iLeft. iDestruct "Base" as "(%Base & $)". iPureIntro.
    intros i Hi. destruct (Hel _ Hi) as [?|(? & ? & Hlook)]; eauto.
  - iRight. iLeft. iDestruct "Stutter" as (P' σ_s' I) "(%Hsteps & %Htgt & Hstate & IH)".
    iExists P', σ_s', I. iFrame. do 2 (iSplitR "IH"; first done).
    iApply "IH". iPureIntro. intros i [Hi Hni]%elem_of_difference.
    destruct (Hel _ Hi) as [|Hvals]; first set_solver.
    right. destruct Hvals as (v_t & v_s & Hlook).
    exists v_t, v_s.
    eapply (pool_steps_value_preservation _ _ _ _ i) in Hsteps; last first.
    { rewrite list_lookup_fmap Hlook //=. }
    assert (P'.(tgt) !! i = Some (of_val v_t)) as Htgt_look.
    { rewrite Htgt list_lookup_fmap Hlook //. }
    revert Hsteps Htgt_look.
    rewrite !list_lookup_fmap.
    destruct (P' !! i) as [[]|]; simpl; naive_solver.
  - iRight. iRight. iIntros (T_t' D' i σ_t' Hfair).
    iMod ("Step" with "[//]") as (P' σ_s' I Heq Hsteps) "(SI & IH)".
    iExists P', σ_s', I. iFrame. iModIntro. do 2 (iSplit; first done).
    iApply "IH". iPureIntro. intros j Hj. eapply elem_of_difference in Hj as [Hj HI].
    destruct (Hel _ Hj) as [?|Hvals].
    { left; eapply elem_of_difference; eauto. }
    right. destruct Hvals as (v_t & v_s & Hlook).
    exists v_t, v_s.
    eapply (pool_steps_value_preservation _ _ _ _ j) in Hsteps; last first.
    { rewrite list_lookup_fmap Hlook //=. }
    rewrite -Heq in Hfair. eapply fair_pool_step_iff in Hfair as (Hstep & ?).
    eapply (pool_step_value_preservation _ _ _ _ j) in Hstep; last first.
    { rewrite list_lookup_fmap Hlook //=. }
    revert Hsteps Hstep. rewrite !list_lookup_fmap.
    destruct (P' !! j) as [[??]|]; simpl; naive_solver.
Qed.

Lemma must_step_all_weaken P O O' D π:
  O' ⊆ O →
  must_step_all π P O D -∗
  must_step_all π P O' D.
Proof.
  iIntros (Hsub) "Hall". iApply must_step_all_add_values; last done.
  naive_solver.
Qed.


Lemma must_step_all_delays_for P O D π:
  (⌜delays_for P.(tgt) D⌝ -∗ must_step_all π P O D) -∗ must_step_all π P O D.
Proof.
  rewrite must_step_unfold /must_step_inner.
  iIntros "Hsim". iIntros (p_t σ_t p_s σ_s) "(SI & Hsafe & %Hdel)".
  iApply ("Hsim" with "[//] [$SI $Hsafe //]").
Qed.

Definition csim_expr_all_wo π P O :=
  ([∗ list] k ↦ (p:_*_) ∈ P, if (decide (k ∈ O)) then emp else csim_expr (lift_post (ext_rel (π + k))) (π + k) (fst p) (snd p))%I.

Lemma csim_expr_all_to_wo P π:
  csim_expr_all π P ≡ csim_expr_all_wo π P ∅.
Proof.
  rewrite /csim_expr_all /csim_expr_all_wo. f_equiv.
  intros k [e_t e_s]. case_decide; set_solver.
Qed.

Lemma csim_expr_all_wo_split P O i e_t e_s π:
  P !! i = Some (e_t, e_s) →
  i ∉ O →
  csim_expr_all_wo π P O ≡ (csim_expr (lift_post (ext_rel (π + i))) (π + i) e_t e_s ∗ csim_expr_all_wo π P (O ∪ {[i]}))%I.
Proof.
  intros Hlook Hel. rewrite /csim_expr_all_wo.
  rewrite (big_sepL_delete _ _ i); last done.
  f_equiv; first by destruct (decide (i ∈ O)); set_solver.
  f_equiv. intros k [e_t' e_s']; simpl.
  destruct (decide (k = i)), (decide (k ∈ O)), (decide (k ∈ O ∪ {[i]}));
    eauto; set_solver.
Qed.

Lemma csim_expr_all_wo_insert i O P e_t e_s π:
  i ∈ O →
  csim_expr_all_wo π P O ≡ csim_expr_all_wo π (<[i := (e_t, e_s)]> P) O.
Proof.
  intros Hel. destruct (P !! i) as [[e_t' e_s']|] eqn: Hlook; last first.
  { rewrite list_insert_ge //; by eapply lookup_ge_None_1. }
  eapply bi.equiv_entails; split.
  - rewrite /csim_expr_all_wo. iIntros "H".
    rewrite big_sepL_insert_acc //.
    destruct (decide (i ∈ O)); last naive_solver.
    iDestruct "H" as "[_ H]". by iApply "H".
  - rewrite /csim_expr_all_wo. iIntros "H".
    rewrite big_sepL_insert_acc; last eapply list_lookup_insert_eq, lookup_lt_Some, Hlook.
    destruct (decide (i ∈ O)); last naive_solver.
    iDestruct "H" as "[_ H]". iSpecialize ("H" $! (e_t', e_s')).
    rewrite list_insert_insert_eq list_insert_id //. by iApply "H".
Qed.

Lemma csim_expr_all_wo_app O P1 P2:
  (∀ i, i ∈ O → i < length P1) →
  (csim_expr_all_wo 0 P1 O ∗ csim_expr_all (length P1) P2)%I ≡ csim_expr_all_wo 0 (P1 ++ P2)%I O.
Proof.
  intros Hlt; rewrite /csim_expr_all_wo /csim_expr_all.
  rewrite big_sepL_app. f_equiv. f_equiv.
  intros k [e_t e_s]; simpl.
  case_decide as Hel; last done.
  eapply Hlt in Hel.
  change (length P1 + k) with (length (P1: list (expr Λ * expr Λ)) + k) in Hel.
  lia.
Qed.

Lemma csim_expr_all_app P1 P2:
  csim_expr_all 0 (P1 ++ P2) ≡ (csim_expr_all 0 P1 ∗ csim_expr_all (length P1) P2)%I.
Proof.
  rewrite csim_expr_all_to_wo -csim_expr_all_wo_app; [ | set_solver].
  rewrite !csim_expr_all_to_wo //.
Qed.


Lemma csim_expr_target_step_unfold T i p_t p_s σ_t σ_s e_t e_s e_t' σ_t' efs_t:
  T !! i = Some e_s →
  prim_step p_t e_t σ_t e_t' σ_t' efs_t →
  pool_safe p_s T σ_s →
  state_interp p_t σ_t p_s σ_s T -∗
  csim_expr (lift_post (ext_rel i)) i e_t e_s ==∗
  ∃ e_s' σ_s' efs_s I, csim_expr (lift_post (ext_rel i)) i e_t' e_s' ∗ state_interp p_t σ_t' p_s σ_s' (<[i := e_s']> T ++ efs_s) ∗
      ⌜pool_steps p_s T σ_s I (<[i := e_s']> T ++ efs_s) σ_s'⌝ ∗ ⌜length efs_t = length efs_s⌝ ∗ csim_expr_all (length T) (zip efs_t efs_s).
Proof.
  intros Hlook Hprim Hsafe. iIntros "SI Hsim". rewrite csim_expr_unfold.
  iMod ("Hsim" with "[$SI]") as "[Val|Step]". { by erewrite fill_empty. }
  - iModIntro. iDestruct "Val" as (e_s' σ_s' Hnfs) "[SI Hpost]".
    iDestruct "Hpost" as (v_t v_s Heq1 Heq2) "?".
    rewrite Heq1 in Hprim. exfalso. by eapply val_prim_step.
  - iDestruct "Step" as "[_ Step]".
    iMod ("Step" with "[//]") as "[Stutter|NoStutter]".
    + iModIntro. iDestruct "Stutter" as "(-> & SI & Hsim)".
      iExists e_s, σ_s. iFrame. iExists [], []. rewrite /csim_expr_all; simpl.
      rewrite app_nil_r list_insert_id //. iFrame.
      iPureIntro. repeat split. constructor.
    + iDestruct "NoStutter" as (e_s' e_s'' σ_s' σ_s'' efs_s Hnfs Hprim') "(SI & Hsim & Hall)".
      iPoseProof (big_sepL2_length with "Hall") as "%Hlen".
      iModIntro. iExists e_s'', σ_s''. iFrame. iExists efs_s.
      eapply no_forks_then_prim_step_pool_steps in Hnfs as (I & ? & Hsub); [|done..].
      iExists I. rewrite fill_empty. iFrame. repeat iSplit; [done..|].
      by rewrite /csim_expr_all big_sepL2_alt bi.and_elim_r.
Qed.


Lemma csim_expr_must_step_all_core_ind P O D i:
  i ∈ O →
  O ⊆ threads P.(tgt) →
  □ (∀ j D P', ⌜j ∈ O⌝ -∗ ⌜O ∖ {[j]} ⊆ threads P'.(tgt)⌝ -∗ csim_expr_all 0 P' -∗ must_step_all 0 P' (O ∖ {[j]}) D) -∗
  csim_expr_all 0 P -∗
  must_step_all 0 P O D.
Proof.
  iIntros (Hel Hsub) "#IHO Hall". specialize (Hsub _ Hel) as Hthread.
  eapply threads_spec in Hthread as (e & Hlook).
  eapply list_lookup_fmap_Some_1 in Hlook as ([e_t e_s] & -> & Hlook).
  rewrite csim_expr_all_to_wo (csim_expr_all_wo_split _ _ i) //.
  replace (∅ ∪ {[i]}: gset nat) with ({[i]}: gset nat) by set_solver.
  iDestruct "Hall" as "[Hsim Hall]".
  rewrite csim_expr_eq closed_greatest_def_unfold.
  iApply (closed_least_def_strong_ind (λ Ψ π e_t e_s, ∀ P D, ⌜P !! i = Some (e_t, e_s)⌝ -∗ ⌜i = π⌝ -∗ ⌜O ⊆ threads P.(tgt)⌝ -∗ csim_expr_all_wo 0 P {[i]} -∗ (∀ e_t e_s, Ψ e_t e_s -∗ lift_post (ext_rel i) e_t e_s) -∗ must_step_all 0 P O D)%I with "[] Hsim [] [] [] Hall"); eauto.
  { solve_proper. }
  clear P D Hsub e_t e_s Hlook. iModIntro. iIntros (Ψ π e_t e_s) "Hsim".
  iIntros (P D Hlook ? Hsub) "Hall Hpost". subst π.
  destruct (to_val e_t) as [v_t|] eqn: Hval.
  - (* thread i is a value *)
    rewrite must_step_unfold /csim_expr_inner /must_step_inner.
    iIntros (p_t σ_t p_s σ_s) "(SI & %Hsafe & %Hdel)".
    iMod ("Hsim" with "[$SI]") as "[Val|Step]".
    + iPureIntro. erewrite fill_empty. rewrite list_lookup_fmap Hlook //.
    + iDestruct "Val" as (e_s' σ_s' Hnfs) "[SI HΨ]".
      iSpecialize ("Hpost" with "HΨ"). iDestruct "Hpost" as (v_t' v_s Heq1 Heq2) "Hval".
      rewrite Heq1 to_of_val in Hval. injection Hval as ->.
      iModIntro. iRight. iLeft.
      eapply (no_forks_pool_steps P.(src) i) in Hnfs as (I & Hnfs & Hsub'); last first.
      { rewrite list_lookup_fmap Hlook //. }
      iExists (<[i := (e_t, e_s')]> P), σ_s', I.
      rewrite fill_empty !list_fmap_insert //=. iSplit; first done.
      rewrite (list_insert_id P.(tgt)) ?list_lookup_fmap ?Hlook //. iSplit; first done.
      iFrame. iApply (must_step_all_weaken _ O); first set_solver.
      iApply (must_step_all_add_values _ (O ∖ {[i]})).
      { intros j Hj. destruct (decide (j = i)); subst; last set_solver.
        right. exists v_t, v_s. eapply list_lookup_insert_eq, lookup_lt_Some, Hlook. }
      iApply ("IHO" with "[//]").
      { iPureIntro. rewrite list_fmap_insert //=. etrans; last by eapply threads_insert. set_solver. }
      rewrite csim_expr_all_to_wo (csim_expr_all_wo_split _ ∅ i); last set_solver; last first.
      { eapply list_lookup_insert_eq, lookup_lt_Some, Hlook. }
      replace (∅ ∪ {[i]}: gset nat) with ({[i]}: gset nat) by set_solver.
      rewrite (csim_expr_all_wo_insert i); last set_solver. iFrame.
      iApply csim_expr_base. iExists v_t, v_s. iFrame.
      by iPureIntro.
    + iDestruct "Step" as "[%Hred _]".
    destruct Hred as (e_t' & σ_t' & efs & Hprim).
    exfalso. eapply of_to_val in Hval. subst e_t.
    by eapply val_prim_step.
  - (* thread i must be in D *)
    assert (i ∈ active_threads P.(tgt)) as Hact.
    { eapply active_threads_spec. exists e_t. split; last done.
      rewrite list_lookup_fmap Hlook //. }
    iApply must_step_all_delays_for. iIntros (Hdel).
    eapply Hdel in Hact as [d HD]. clear Hdel.
    iRevert (P D HD Hlook Hsub) "Hall".
    iInduction (lt_wf d) as [d _] "IHd".
    iIntros(P D HD Hlook Hsub) "Hall".
    rewrite must_step_unfold /must_step_inner.
    iIntros (p_t σ_t p_s σ_s) "(SI & %Hsafe & %Hdel)".
    iModIntro. iRight. iRight.
    iIntros (T_t' D' j σ_t' Hstep).
    destruct (decide (j = i)) as [->|Hne].
    + iClear "IHd". iMod ("Hsim" with "[$SI]") as "[Val|Step]".
      * iPureIntro. erewrite fill_empty. rewrite list_lookup_fmap Hlook //.
      * iDestruct "Val" as (e_s' σ_s' Hnfs) "[SI HΨ]".
        iDestruct ("Hpost" with "HΨ") as (v_t v_s Heq1 Heq2) "?".
        rewrite Heq1 to_of_val in Hval. naive_solver.
      * iDestruct "Step" as "[_ Hstep]".
        eapply fair_pool_step_inv in Hstep as (e_t_alt & e_t' & efs_t & Hstep & Hlook' & Hupd & Hdecr).
        rewrite list_lookup_fmap Hlook //= in Hlook'. injection Hlook' as <-.
        iMod ("Hstep" with "[//]") as "[Stutter|NoStutter]".
        -- iDestruct "Stutter" as "(-> & SI & Hupd)".
           iModIntro. iExists (<[i := (e_t', e_s)]> P), σ_s, [].
           rewrite (list_fmap_insert snd) (list_insert_id (P.(src))).
           2: { rewrite list_lookup_fmap Hlook //. } iFrame.
           iSplit. { iPureIntro. rewrite Hupd right_id list_fmap_insert //. }
           iSplit. { iPureIntro. constructor. }
           simpl. rewrite bi.and_elim_l. replace (O ∖ ∅) with O by set_solver.
           iApply ("Hupd" with "[] [//] [] [Hall] Hpost").
           ++ iPureIntro. eapply list_lookup_insert_eq, lookup_lt_Some, Hlook.
           ++ iPureIntro. rewrite list_fmap_insert. by etrans; last eapply threads_insert.
           ++ rewrite -csim_expr_all_wo_insert //. set_solver.
        -- iDestruct "NoStutter" as (e_s' e_s'' σ_s' σ_s'' efs_s Hnfs Hprim) "(SI & Hsim & Hfrks)".
           iPoseProof (big_sepL2_length with "Hfrks") as "%Hlen".
           iModIntro. eapply (no_forks_then_prim_step_pool_steps P.(src) i) in Hnfs as (I & Hsteps & Heq); [| done |]; last first.
           { rewrite list_lookup_fmap Hlook //. }
           iExists (<[i := (e_t', e_s'')]> P ++ zip efs_t efs_s), σ_s'', I.
           iSplit. { iPureIntro. rewrite fmap_app Hupd list_fmap_insert fst_zip // Hlen //. }
           iSplit. { iPureIntro. rewrite fmap_app list_fmap_insert //= snd_zip ?Hlen //. }
           rewrite fill_empty fmap_app list_fmap_insert snd_zip ?Hlen //.
           iFrame. rewrite Heq. iApply "IHO"; first done.
           { iPureIntro. rewrite fmap_app list_fmap_insert. etrans; last eapply threads_prim_step. set_solver. }

           rewrite csim_expr_all_app. iSplitR "Hfrks".
           ++ rewrite csim_expr_all_to_wo (csim_expr_all_wo_split _ ∅ i);
              last set_solver;
              last by eapply list_lookup_insert_eq, lookup_lt_Some, Hlook.
              rewrite -csim_expr_all_wo_insert; last set_solver.
              replace (∅ ∪ {[i]}: gset nat) with ({[i]}: gset nat) by set_solver.
              iFrame. iApply (csim_expr_mono with "Hpost [Hsim]").
              by rewrite csim_expr_eq.
           ++ rewrite /csim_expr_all.
              by rewrite big_sepL2_alt csim_expr_eq bi.and_elim_r length_insert length_fmap.
      + eapply fair_pool_step_inv in Hstep as (e_j & e_j_t' & efs_t & Hstep & Hlook' & Hupd & Hdecr).
        eapply list_lookup_fmap_Some_1 in Hlook' as ([e_j_t e_j_s] & -> & Hlookj); simpl in Hstep.
        eapply Hdecr in HD as (d' & -> & HD'); last done.
        assert (d' < S d') as Hlt by lia.
        iSpecialize ("IHd" $! d' Hlt with "Hsim Hpost").
        rewrite (csim_expr_all_wo_split _ _ j) //; last set_solver.
        iDestruct "Hall" as "[Hsim Hall]".
        iMod (csim_expr_target_step_unfold P.(src) j with "SI Hsim") as (e_j_s' σ_s' efs_s I) "(Hsim & SI & %Hsteps & %Hlen & Hfrks)".
        * rewrite list_lookup_fmap Hlookj //.
        * done.
        * done.
        * iModIntro. iExists (<[j := (e_j_t', e_j_s')]> P ++ zip efs_t efs_s), σ_s', I.
          rewrite Hupd !fmap_app !list_fmap_insert //= fst_zip ?Hlen // snd_zip ?Hlen //. iFrame.
          do 2 (iSplit; first done). iApply (must_step_all_weaken _ O); first set_solver.
          iApply "IHd".
          -- done.
          -- iPureIntro. eapply lookup_app_l_Some. rewrite list_lookup_insert_ne //.
          -- iPureIntro. rewrite fmap_app list_fmap_insert fst_zip ?Hlen //=.
             etrans; last by eapply threads_prim_step. done.
          -- rewrite (csim_expr_all_wo_split _ {[i]} j); last set_solver; last first.
             { eapply lookup_app_l_Some, list_lookup_insert_eq, lookup_lt_Some, Hlookj. }
             iFrame. rewrite -csim_expr_all_wo_app; last first.
             { intros k Hk. assert (k = j ∨ k = i) as [] by set_solver; subst; rewrite length_insert; by eapply lookup_lt_Some. }
             rewrite length_insert length_fmap.
             iFrame. rewrite csim_expr_all_wo_insert //. set_solver.
Qed.

Lemma csim_expr_must_step_all P O D:
  O ⊆ threads P.(tgt) → csim_expr_all 0 P -∗ must_step_all 0 P O D.
Proof.
  intros Hsub. iRevert (D P Hsub).
  iInduction (set_wf O) as [O _] "IHO".
  iIntros (D P Hsub) "Hall".
  destruct (decide (O ≡ ∅)) as [Empty|[i Hel]%set_choose].
  - rewrite must_step_unfold /must_step_inner.
    iIntros (p_t σ_t p_s σ_s) "(SI & %Hsafe & %Hdel)".
    iModIntro. iLeft. iFrame. iPureIntro.
    intros i; set_solver.
  - iApply csim_expr_must_step_all_core_ind; eauto.
    iModIntro. iIntros (j D' P' Hel' Hsub') "Hall". iApply "IHO".
    + iPureIntro. set_solver.
    + iPureIntro. set_solver.
    + done.
Qed.

Lemma csim_expr_to_pool P:
  csim_expr_all 0 P -∗ sim_pool P.
Proof.
  iIntros "H". iApply (sim_pool_coind with "[] H"); clear P. iModIntro.
  iIntros (P D) "Hall". by iApply csim_expr_must_step_all.
Qed.



(* we use sim_pool to prove the preservation of fair termination *)
Section fair_termination.
  Context {sat: PROP → Prop} {Sat: Satisfiable sat}.
  Arguments sat _%_I.


  (* TODO: move these lemmas to different file *)
  Lemma no_magic_values_step (i: nat) p T σ j T' σ':
    pool_step p T σ j T' σ' →
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

  Lemma no_magic_values_steps (i: nat) p T σ I T' σ':
    pool_steps p T σ I T' σ' →
    i ∈ active_threads T →
    i ∉ active_threads T' →
    i ∈ (list_to_set I: gset nat).
    Proof.
    induction 1 as [|T T' T'' σ σ' σ'' j I Hstep Hsteps]; first naive_solver.
    intros Hact Hnact. destruct (decide (i ∈ active_threads T')); first set_solver.
    eapply no_magic_values_step in Hstep; eauto; subst; set_solver.
  Qed.

  Lemma threads_src_tgt P: threads P.(src) = threads P.(tgt).
  Proof.
    rewrite /threads !length_fmap //.
  Qed.

  Lemma fair_div_must_take_steps p_t p_s σ_t σ_s σ_s' P P' D I:
    fair_div_delay p_t P'.(tgt) D σ_t →
    pool_steps p_s P.(src) σ_s I P'.(src) σ_s' →
    all_values (threads P.(src) ∖ list_to_set I) P' →
    ∃ j, j ∈ I.
  Proof.
    intros Hfair Hsteps Hvalues.
    destruct I; last by set_solver.
    inversion Hsteps as [T σ I H1 H2 Heq|]; subst; clear H2.
    destruct Hfair as [j T'' D'' σ'' Hstep Hdel Hfair'].
    eapply fair_pool_step_inv in Hstep as (e & e' & T_f & Hstep & Hlook & -> & ?).
    destruct (Hvalues j) as (e_t & e_s & Hlook').
    { rewrite Heq threads_src_tgt //= difference_empty threads_spec; eauto. }
    revert Hlook.
    rewrite list_lookup_fmap Hlook' //=.
    injection 1 as <-. exfalso; by eapply val_prim_step.
  Qed.

  Lemma fair_div_forces_active_source p_t p_s σ_t σ_s σ_s' P P' D I:
    fair_div_delay p_t P'.(tgt) D σ_t →
    pool_steps p_s P.(src) σ_s I P'.(src) σ_s' →
    all_values (threads P.(src) ∖ list_to_set I) P' →
    ∃ j, j ∈ active_threads P.(src).
  Proof.
    intros Hfair Hsteps Hvalues.
    destruct (fair_div_must_take_steps p_t p_s σ_t σ_s σ_s' P P' D I) as [i Hi]; eauto.
    inversion Hsteps as [|T T' T'' σ σ' σ'' j J Hstep Hsteps']; subst; first set_solver.
    eapply pool_step_iff in Hstep as (e & e' & T_f & Hstep & Hlook & ->).
    exists j. eapply active_threads_spec.
    exists e; split; first done.
    destruct (to_val e) as [v_t|] eqn: Heq; last done.
    eapply of_to_val in Heq. rewrite -Heq in Hstep.
    exfalso. by eapply val_prim_step.
  Qed.

  Lemma must_step_sat R p_s p_t P O D σ_s σ_t :
    fair_div_delay p_t P.(tgt) D σ_t →
    pool_safe p_s P.(src) σ_s →
    sat (state_interp p_t σ_t p_s σ_s P.(src) ∗ must_step R P O D) →
    ∃ P' D' σ_t' σ_s' I,
      sat (state_interp p_t σ_t' p_s σ_s' P'.(src) ∗ R P') ∧
      fair_div_delay p_t P'.(tgt) D' σ_t' ∧
      pool_steps p_s P.(src) σ_s I P'.(src) σ_s' ∧
      (all_values (O ∖ list_to_set I) P') ∧
      filter (λ i, i ∈ active_threads P.(src)) O ⊆ list_to_set I.
  Proof.
    intros Hdiv Hsafe Hsat. enough (sat (∃ P' D' σ_t' σ_s' I,
    (state_interp p_t σ_t' p_s σ_s' P'.(src) ∗ R P') ∗
    ⌜fair_div_delay p_t P'.(tgt) D' σ_t'⌝ ∗
    ⌜pool_steps p_s P.(src) σ_s I P'.(src) σ_s'⌝ ∗
    ⌜(all_values (O ∖ list_to_set I) P')⌝ ∗
    ⌜filter (λ i, i ∈ active_threads P.(src)) O ⊆ list_to_set I⌝)) as Hsat'.
    { eapply sat_exists in Hsat' as (P' & Hsat').
      eapply sat_exists in Hsat' as (D' & Hsat').
      eapply sat_exists in Hsat' as (σ_t' & Hsat').
      eapply sat_exists in Hsat' as (σ_s' & Hsat').
      eapply sat_exists in Hsat' as (I & Hsat').
      eapply sat_sep in Hsat' as [Hpost Hsat'].
      do 3 (eapply sat_sep in Hsat' as [?%sat_elim Hsat']).
      eapply sat_elim in Hsat'. eauto 10. }
    eapply sat_bupd, sat_mono, Hsat; clear Hsat.
    iIntros "[SI Hmust]". iRevert (σ_t σ_s Hdiv Hsafe) "SI".
    iApply (must_step_ind (λ P O D, ∀ σ_t σ_s, ⌜fair_div_delay p_t P.(tgt) D σ_t⌝ -∗ ⌜pool_safe p_s P.(src) σ_s⌝ -∗ state_interp p_t σ_t p_s σ_s P.(src) ==∗
                             ∃ P' D' σ_t' σ_s' I, (state_interp p_t σ_t' p_s σ_s' P'.(src) ∗ R P') ∗ _)%I
    with "[] Hmust").
    clear P O D. iModIntro. iIntros (P O D) "Hmust".
    iIntros (σ_t σ_s Hdiv Hsafe) "SI". eapply fair_div_delays_for in Hdiv as Hdel.
    rewrite /must_step_inner. iMod ("Hmust" with "[$SI //]") as "[Base|[Stutter|Step]]".
    - iDestruct "Base" as "(%Hvalues & SI & Hpost)".
      iModIntro. iExists P, D, σ_t, σ_s, []. iFrame. iPureIntro.
      repeat split.
      + done.
      + constructor.
      + simpl. by replace (O ∖ ∅) with O by set_solver.
      + intros j Hj. eapply elem_of_filter in Hj as [Hact HO].
        eapply active_threads_spec in Hact as (e & Hlook & Hnval).
        eapply Hvalues in HO as (v_t & v_s & Hlook').
        revert Hlook. rewrite list_lookup_fmap Hlook' //=.
        injection 1 as <-. rewrite to_of_val in Hnval. naive_solver.
    - iDestruct "Stutter" as (P' σ_s' I Hsteps Heq) "[SI Post]".
      iMod ("Post" with "[] [] SI") as (P'' D'' σ_t'' σ_s'' J) "[R %Hrest]".
      { rewrite Heq //. }
      { iPureIntro. by eapply pool_steps_safe. }
      iModIntro. iExists P'', D'', σ_t'', σ_s'', (I ++ J). iFrame.
      destruct Hrest as (Hdiv' & Hsteps' & Hvals & Hfilter).
      repeat iSplit; first done.
      + iPureIntro. by eapply pool_steps_trans.
      + iPureIntro. by replace (O ∖ list_to_set (I ++ J)) with (O ∖ list_to_set I ∖ list_to_set J) by set_solver.
      + iPureIntro. rewrite list_to_set_app.
        intros j [Hact Hj]%elem_of_filter.
        destruct (decide (j ∈ (list_to_set I: gset nat))); first by set_solver.
        destruct (decide (j ∈ active_threads P'.*2)).
        { eapply elem_of_union_r, Hfilter, elem_of_filter. set_solver. }
        eapply elem_of_union_l, no_magic_values_steps; eauto.
    - destruct Hdiv as [i T_t' D' σ_t' Hfair _ Hdiv].
      iMod ("Step" with "[//]") as (P' σ_s' I Heq Hsteps) "(SI & Step)".
      iMod ("Step" with "[] [] SI") as (P'' D'' σ_t'' σ_s'' J) "[R %Hrest]".
      { rewrite Heq //. }
      { iPureIntro. by eapply pool_steps_safe. }
      iModIntro. iExists P'', D'', σ_t'', σ_s'', (I ++ J). iFrame.
      destruct Hrest as (Hdiv' & Hsteps' & Hvals & Hfilter).
      repeat iSplit; first done.
      + iPureIntro. by eapply pool_steps_trans.
      + iPureIntro. by replace (O ∖ list_to_set (I ++ J)) with (O ∖ list_to_set I ∖ list_to_set J) by set_solver.
      + iPureIntro. rewrite list_to_set_app.
        intros j [Hact Hj]%elem_of_filter.
        destruct (decide (j ∈ (list_to_set I: gset nat))); first by set_solver.
        destruct (decide (j ∈ active_threads P'.*2)).
        { eapply elem_of_union_r, Hfilter, elem_of_filter. set_solver. }
        eapply elem_of_union_l, no_magic_values_steps; eauto.
  Qed.

  Lemma sim_pool_sat_unfold p_s p_t P D σ_s σ_t :
    fair_div_delay p_t P.(tgt) D σ_t →
    pool_safe p_s P.(src) σ_s →
    sat (state_interp p_t σ_t p_s σ_s P.(src) ∗ sim_pool P) →
    ∃ P' D' σ_t' σ_s' I,
      sat (state_interp p_t σ_t' p_s σ_s' P'.(src) ∗ sim_pool P') ∧
      fair_div_delay p_t P'.(tgt) D' σ_t' ∧
      pool_steps p_s P.(src) σ_s I P'.(src) σ_s' ∧
      ∅ ⊂ active_threads P.(src) ⊆ list_to_set I.
  Proof.
    intros Hfair Hsafe. rewrite sim_pool_unfold.
    intros Hsat. eapply sat_mono in Hsat; last first.
    { iDestruct 1 as "[SI Hmust]". iSpecialize ("Hmust" $! D). iCombine "SI Hmust" as "H". iExact "H". }
    eapply must_step_sat in Hsat; [|done..].
    destruct Hsat as (P' & D' & σ_t' & σ_s' & I & Hsat & Hfair' & Hpool & Hvals & Hfilter).
    exists P', D', σ_t', σ_s', I. do 3 (split; first done).
    revert Hfilter; rewrite -threads_src_tgt; replace (filter (λ i : nat, i ∈ active_threads P.(src)) (threads P.(src))) with (active_threads P.(src)); last first.
    { eapply leibniz_equiv. intros j.
      rewrite elem_of_filter threads_spec active_threads_spec.
      naive_solver. }
    intros Hsub; split; last done.
    enough (∃ j, j ∈ active_threads P.(src)) as [j Hj] by set_solver.
    eapply fair_div_forces_active_source; eauto.
    by rewrite threads_src_tgt.
  Qed.


  Lemma sim_pool_preserves_fair_termination p_s p_t P D σ_s σ_t:
    fair_div_delay p_t P.(tgt) D σ_t →
    pool_safe p_s P.(src) σ_s →
    sat (state_interp p_t σ_t p_s σ_s P.(src) ∗ sim_pool P) →
    fair_div_coind p_s P.(src) σ_s.
  Proof.
    revert p_s p_t P D σ_s σ_t. cofix IH. intros p_s p_t P D σ_s σ_t Hfair Hsafe Hsat.
    eapply sim_pool_sat_unfold in Hfair as (P' & D' & σ_t' & σ_s' & I & Hsat' & Hfair' & Hsteps & Hsub); eauto.
    econstructor; eauto.
    eapply IH; eauto using pool_steps_safe.
  Qed.

  End fair_termination.
End fix_lang.
