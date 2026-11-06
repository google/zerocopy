From iris.algebra Require Import agree gmap.
From iris.base_logic Require Import iprop own.
From iris.proofmode Require Import proofmode.


(** * Ghost state constructions for keeping track of the programs
  It provides a persistent token f @ K asserting that there is a function f with body K.
*)

Local Definition gen_progR (F C : Type) `{Countable F} := agreeR (gmapO F (leibnizO C)).
Class gen_progGpreS (Σ : gFunctors) (F C : Type) `{Countable F} := {
  gen_prog_pre_inG :: inG Σ (gen_progR F C);
}.
Definition gen_progΣ (F C : Type) `{Countable F} := #[GFunctor (gen_progR F C)].

Global Instance subG_gen_progΣ Σ (F C : Type) `{Countable F} :
  subG (gen_progΣ F C) Σ → gen_progGpreS Σ F C.
Proof. solve_inG. Qed.

(* TODO: [Σ] should be the first parameter. *)
Class gen_progGS_named (F C : Type) (Σ : gFunctors) (gen_prog_name : gname) `{Countable F} := GenProgGSNamed {
  gen_prog_preNameG :: gen_progGpreS Σ F C
}.

Class gen_sim_progGS (F C_t C_s : Type) (Σ : gFunctors) `{Countable F} := GenSimProgG {
  gen_prog_name_target : gname;
  gen_prog_name_source : gname;
  gen_prog_inG_source :: gen_progGS_named F C_s Σ gen_prog_name_source;
  gen_prog_inG_target :: gen_progGS_named F C_t Σ gen_prog_name_target;
}.

Global Arguments GenSimProgG F C_t C_s Σ {_ _} _ _ {_ _}.
Global Arguments gen_prog_name_source {F C_t C_s Σ _ _} _ : assert.
Global Arguments gen_prog_name_target {F C_t C_s Σ _ _} _ : assert.

Section definitions.
  Context `{Countable F, gen_prog_name : gname, hG : !gen_progGS_named F C Σ gen_prog_name }.

  Definition has_prog (p : gmap F C) : iProp Σ :=
    own gen_prog_name ((to_agree p) : gen_progR F C).

  Definition has_fun_def (fname : F) (K: C) : iProp Σ :=
    ∃ P, ⌜P !! fname = Some K⌝ ∗ has_prog P.
  Definition has_fun_aux : seal (@has_fun_def). Proof. by eexists. Qed.
  Definition has_fun := has_fun_aux.(unseal).
  Definition has_fun_eq : @has_fun = @has_fun_def := has_fun_aux.(seal_eq).
End definitions.

Local Notation "f @ K" := (has_fun f K)
  (at level 20, format "f  @  K") : bi_scope.

Section gen_prog.
  Context {F C} `{Countable L, gen_prog_name : gname, gen_progGS_named F C Σ gen_prog_name}.
  Implicit Types P Q : iProp Σ.
  Implicit Types p : gmap F C.

  Global Instance has_prog_persistent p : Persistent (has_prog p).
  Proof. apply _. Qed.

  (** General properties of has_fun *)
  Global Instance has_fun_timeless f K : Timeless (f @ K).
  Proof. rewrite has_fun_eq. apply _. Qed.
  Global Instance has_fun_persistent f K : Persistent (f @ K).
  Proof. rewrite has_fun_eq. apply _. Qed.

  Lemma has_prog_agree p1 p2 : has_prog p1 -∗ has_prog p2 -∗ ⌜p1 = p2⌝.
  Proof.
    iIntros "Hp1 Hp2".
    iCombine "Hp1 Hp2" gives %Hval.
    setoid_rewrite to_agree_op_valid_L in Hval. done.
  Qed.

  Lemma has_fun_agree f K1 K2 : f @ K1 -∗ f @ K2 -∗ ⌜K1 = K2⌝.
  Proof.
    rewrite has_fun_eq. iIntros "(%p1 & %HK1 & Hp1) (%p2 & %HK2 & Hp2)".
    iDestruct (has_prog_agree with "Hp1 Hp2") as %->.
    rewrite HK1 in HK2. injection HK2 as [= ->]. done.
  Qed.

  Lemma has_prog_has_fun_agree p f K : has_prog p -∗ f @ K -∗ ⌜p !! f = Some K⌝.
  Proof.
    rewrite /has_prog has_fun_eq. iIntros "Hp (%p2 & %HK2 & Hp2)".
    iDestruct (has_prog_agree with "Hp Hp2") as %->. done.
  Qed.

  Lemma has_prog_all_funs p :
    has_prog p -∗ ([∗ map] f ↦ K ∈ p, f @ K).
  Proof.
    iIntros "#Hp".
    iApply big_sepM_intro. iIntros "!# %f %K %Hf".
    rewrite has_fun_eq. iExists p. eauto.
  Qed.
End gen_prog.

Lemma gen_prog_init_names `{Countable F, !gen_progGpreS Σ F C} p :
  ⊢ |==> ∃ γp : gname,
    let hG := GenProgGSNamed F C Σ γp in has_prog p.
Proof.
  iMod (own_alloc ((to_agree p) : gen_progR F C)) as (γ) "#Hown".
  { done. }
  iExists γ.
  set HG := GenProgGSNamed _ _ _ γ _ _ _.
  iModIntro. by iFrame "#".
Qed.

Lemma gen_sim_prog_init `{Countable F, !gen_progGpreS Σ F C_t, !gen_progGpreS Σ F C_s} P_t P_s :
  ⊢ |==> ∃ _ : gen_sim_progGS F C_t C_s Σ,
    has_prog (hG:=gen_prog_inG_target) P_t ∗
    has_prog (hG:=gen_prog_inG_source) P_s.
Proof.
  iMod (gen_prog_init_names P_t) as (γt) "Hinit_t".
  iMod (gen_prog_init_names P_s) as (γs) "Hinit_s".
  iExists (GenSimProgG _ _ _ _ γt γs). by iFrame.
Qed.
