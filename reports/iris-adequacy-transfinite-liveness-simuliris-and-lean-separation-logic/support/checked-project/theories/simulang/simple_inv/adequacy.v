(** The logical relation implies contextual refinement. *)

From iris.algebra.lib Require Import gset_bij.
From iris.base_logic.lib Require Import gset_bij.
From simuliris.logic Require Import satisfiable.
From simuliris.simulation Require Import slsls closed_sim gen_log_rel.
From simuliris.simulang Require Import proofmode tactics.
From simuliris.simulang Require Import gen_adequacy behavior wf gen_refl.
From simuliris.simulang.simple_inv Require Import inv refl.

(** Whole-program adequacy. *)
Class simpleGpreS Σ := {
  sbij_pre_heapG :: sheapGpreS Σ;
  sbij_pre_bijG :: heapbijGpreS Σ;
}.
Definition simpleΣ := #[sheapΣ; heapbijΣ].

Global Instance subG_sbijΣ Σ :
  subG simpleΣ Σ → simpleGpreS Σ.
Proof. solve_inG. Qed.

Lemma prog_rel_adequacy Σ `{!simpleGpreS Σ} (p_t p_s : prog):
  isat (∀ `(simpleGS Σ) gs,
    ⌜map_Forall (λ _ v, val_wf v) gs⌝ -∗
    ([∗ map] f ↦ fn ∈ p_t, f @t fn) -∗
    ([∗ map] f ↦ fn ∈ p_s, f @s fn) -∗
    target_globals (dom gs) -∗
    source_globals (dom gs) ==∗
    ([∗ map] v∈gs, val_rel v v) ∗ prog_rel p_t p_s
  ) →
  prog_ref p_t p_s.
Proof.
  intros Hprog. apply simplang_adequacy.
  eapply sat_mono, Hprog. clear Hprog.
  iIntros "Hprog_rel % %gs %".
  iMod (heapbij_init (λ _ _ q, q = Some 1%Qp)) as (?) "Hbij". iModIntro.
  set HΣ := (SimpleGS Σ _ _).
  iExists simple_inv, heapbij.loc_rel.
  iSpecialize ("Hprog_rel" $! HΣ).
  iIntros "Hp_t Hp_s Hmt #Hgs_t #Hgs_s".
  iMod ("Hprog_rel" with "[//] [$] [$] [$] [$]") as "[#Hvs $]".
  iMod (heapbij_insert_globals with "Hbij Hmt Hvs") as (L') "[Hbij #Hls]"; [done| ].
  iModIntro. iSplitL "Hbij"; [|iSplitR; [done|]].
  - iExists _. iFrame. iExists _,_. by iFrame "#".
  - iIntros (??) "$".
Qed.

(** Adequacy for open terms. *)
Theorem log_rel_adequacy Σ `{!simpleGpreS Σ} e_t e_s :
  (∀ `(simpleGS Σ), ⊢ log_rel e_t e_s) →
  ctx_ref e_t e_s.
Proof.
  intros Hrel C fname x p Hpwf HCwf Hvars.
  apply (prog_rel_adequacy Σ). eapply isat_intro.
  iIntros (? gs Hgs) "_ _ _ _ !#".
  iSplit.
  { iApply big_sepM_intro. iIntros "!>" (???). iApply val_wf_sound. by apply: Hgs. }
  iApply prog_rel_refl_insert.
  - iModIntro. iApply log_rel_func; first done.
    iApply log_rel_ctx; first done. iApply Hrel.
  - iIntros "!# %f %fn %Hfn". destruct fn as [arg body].
    destruct (Hpwf _ _ Hfn) as [Hfn_wf Hfn_vars].
    iApply log_rel_func; first set_solver.
    iApply log_rel_refl. done.
Qed.
