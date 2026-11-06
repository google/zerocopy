From simuliris.logic Require Import satisfiable.
From simuliris.simulation Require Import slsls lifting adequacy.
From simuliris.stacked_borrows Require Import proofmode tactics.
From simuliris.stacked_borrows Require Import parallel_subst primitive_laws
  log_rel_structural wf refl.
From simuliris.stacked_borrows Require Export behavior.

Lemma sc_rel_obs `{!sborGS Σ} sc_t sc_s :
  sc_rel sc_t sc_s ⊢@{iPropI Σ} ⌜ obs_scalar sc_t sc_s ⌝.
Proof.
  destruct sc_t, sc_s; try by eauto.
  rewrite sc_rel_cid_source. iIntros "[<- _]". eauto.
Qed.

Lemma rrel_obs `{!sborGS Σ} r_t r_s :
  rrel r_t r_s ⊢@{iPropI Σ} ⌜ obs_result r_t r_s ⌝.
Proof.
  destruct r_t as [v_t|], r_s as [v_s|]; try by eauto.
  iInduction v_t as [|sc_t scs_t] "IH" forall (v_s);
    destruct v_s as [|sc_s scs_s]; simpl; try eauto.
  { iIntros "_ !%". constructor. }
  rewrite {2}/value_rel big_sepL2_cons.
  iIntros "[Hs Hss]". rewrite /obs_value Forall2_cons. iSplit.
  - iApply (sc_rel_obs with "Hs").
  - iApply ("IH" with "Hss").
Qed.

(** Whole-program adequacy. *)

Lemma prog_rel_adequacy Σ `{!sborGpreS Σ} (p_t p_s : prog):
  isat (∀ `(sborGS Σ),
    ([∗ map] f ↦ K ∈ p_t, f @t K) -∗
    ([∗ map] f ↦ K ∈ p_s, f @s K) ==∗
    prog_rel p_t p_s
  ) →
  prog_ref p_t p_s.
Proof.
  intros Hrel. eapply (slsls_adequacy (sat:=isat)).
  eapply sat_mono, Hrel. clear Hrel.
  iIntros "Hprog_rel %σ_t %σ_s (->&->)".
  iMod (sbor_init p_t p_s) as (HsborGS) "(Hstate & Hp_t & Hp_s & Hprogs)".
  iMod ("Hprog_rel" with "Hp_t Hp_s") as "Hprog_rel".
  iModIntro. iExists sborGS_simulirisGS. iFrame.
  iSplitL.
  - by iApply value_rel_poison.
  - iIntros (??) "Hext". iApply rrel_obs. done.
Qed.

(** Adequacy for open terms. *)
Theorem log_rel_adequacy Σ `{!sborGpreS Σ} e_t e_s :
  (∀ `(sborGS Σ), ⊢ log_rel e_t e_s) →
  ctx_ref e_t e_s.
Proof.
  intros Hrel C fname x p Hpwf HCwf Hvars.
  apply (prog_rel_adequacy Σ). eapply isat_intro.
  iIntros (?) "_ _ !>".
  iApply prog_rel_refl_insert.
  - iModIntro. iApply log_rel_func; first done.
    iApply log_rel_ctx; first done. iApply Hrel.
  - iIntros "!# %f %fn %Hfn". destruct fn as [arg body].
    destruct (Hpwf _ _ Hfn) as [Hfn_wf Hfn_vars].
    iApply log_rel_func; first set_solver.
    iApply log_rel_refl. done.
Qed.
