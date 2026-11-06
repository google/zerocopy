From iris.bi Require Import bi.
From iris.proofmode Require Import rocq_tactics reduction.
From iris.proofmode Require Export proofmode.
From simuliris.simulation Require Import slsls lifting language.
From simuliris.stacked_borrows Require Import tactics class_instances.
From simuliris.stacked_borrows Require Export primitive_laws notation.

Import bi.

Section sim.
Context `{!sborGS Σ}.

Lemma tac_sim_expr_eval Δ Φ e_t e_t' e_s e_s' π :
  (∀ (e_t'':=e_t'), e_t = e_t'') →
  (∀ (e_s'':=e_s'), e_s = e_s'') →
  envs_entails Δ (e_t' ⪯{π} e_s' [{ Φ }]) → envs_entails Δ (e_t ⪯{π} e_s [{ Φ }]).
Proof. by intros -> ->. Qed.

Lemma tac_target_red_expr_eval Δ Ψ e_t e_t' :
  (∀ (e_t'':=e_t'), e_t = e_t'') →
  envs_entails Δ (target_red e_t' Ψ : iProp Σ) →
  envs_entails Δ (target_red e_t Ψ).
Proof. by intros ->. Qed.

Lemma tac_source_red_expr_eval Δ Ψ e_s e_s' π :
  (∀ (e_s'':=e_s'), e_s = e_s'') →
  envs_entails Δ (source_red e_s' π Ψ : iProp Σ) →
  envs_entails Δ (source_red e_s π Ψ).
Proof. by intros ->. Qed.

Lemma tac_target_red_pure Δ n e_t e_t' K_t Ψ (ϕ : Prop):
  PureExec ϕ n (e_t) (e_t') →
  ϕ →
  envs_entails Δ (target_red (fill K_t e_t') Ψ : iProp Σ) →
  envs_entails Δ (target_red (fill K_t e_t) Ψ).
Proof.
  intros ? ?. rewrite envs_entails_unseal. intros ->.
  (* We want [pure_exec_fill] to be available to TC search locally. *)
  pose proof @pure_exec_ctx.
  apply: target_red_lift_pure. done.
Qed.

Lemma tac_source_red_pure Δ n e_s e_s' K_s Ψ π (ϕ : Prop):
  PureExec ϕ n e_s e_s' →
  ϕ →
  envs_entails Δ (source_red (fill K_s e_s') π Ψ : iProp Σ) →
  envs_entails Δ (source_red (fill K_s e_s) π Ψ).
Proof.
  intros ? ?. rewrite envs_entails_unseal. intros ->.
  (* We want [pure_exec_fill] to be available to TC search locally. *)
  pose proof @pure_exec_ctx.
  apply: source_red_lift_pure. done.
Qed.

Lemma tac_target_red_base e_t Ψ Δ :
  envs_entails Δ (|==> Ψ e_t : iProp Σ) → envs_entails Δ (target_red e_t Ψ).
Proof.
  rewrite envs_entails_unseal => ->. iIntros "H". by iApply target_red_base.
Qed.
Lemma tac_target_red_base_no_bupd e_t Ψ Δ :
  envs_entails Δ (Ψ e_t : iProp Σ) → envs_entails Δ (target_red e_t Ψ).
Proof.
  rewrite envs_entails_unseal => ->. iIntros "H". by iApply target_red_base.
Qed.

Lemma tac_source_red_base e_s Ψ Δ π :
  envs_entails Δ (|==> Ψ e_s : iProp Σ) → envs_entails Δ (source_red e_s π Ψ).
Proof.
  rewrite envs_entails_unseal => ->. by iApply source_red_base.
Qed.
Lemma tac_source_red_base_no_bupd e_s Ψ Δ π :
  envs_entails Δ (Ψ e_s : iProp Σ) → envs_entails Δ (source_red e_s π Ψ).
Proof.
  rewrite envs_entails_unseal => ->. iIntros "H". by iApply source_red_base.
Qed.

Lemma tac_sim_value v_t v_s (Φ : result → result → iProp Σ) Δ π :
  envs_entails Δ (|==> Φ (ValR v_t) (ValR v_s)) → envs_entails Δ (Val v_t ⪯{π} Val v_s {{ Φ }}).
Proof.
  rewrite envs_entails_unseal => ->. iIntros "H". iApply sim_bupd. by iApply sim_value_result.
Qed.
Lemma tac_sim_value_no_bupd v_t v_s Φ Δ π :
  envs_entails Δ (Φ (ValR v_t) (ValR v_s)) → envs_entails Δ (Val v_t ⪯{π} Val v_s {{ Φ }}).
Proof. rewrite envs_entails_unseal => ->. by iApply sim_value_result. Qed.

Lemma tac_sim_place l_t l_s t_t t_s T_t T_s (Φ : result → result → iProp Σ) Δ π :
  envs_entails Δ (|==> Φ (PlaceR l_t t_t T_t) (PlaceR l_s t_s T_s)) →
  envs_entails Δ (Place l_t t_t T_t ⪯{π} Place l_s t_s T_s {{ Φ }}).
Proof. rewrite envs_entails_unseal => ->. iIntros "H". iApply sim_bupd. by iApply sim_place_result. Qed.
Lemma tac_sim_place_no_bupd l_t l_s t_t t_s T_t T_s Φ Δ π :
  envs_entails Δ (Φ (PlaceR l_t t_t T_t) (PlaceR l_s t_s T_s)) →
  envs_entails Δ (Place l_t t_t T_t ⪯{π} Place l_s t_s T_s {{ Φ }}).
Proof. rewrite envs_entails_unseal => ->. iIntros "H". by iApply sim_place_result. Qed.

Lemma tac_sim_result v_t v_s (Φ : result → result → iProp Σ) Δ π :
  envs_entails Δ (|==> Φ v_t v_s) → envs_entails Δ (of_result v_t ⪯{π} of_result v_s {{ Φ }}).
Proof.
  rewrite envs_entails_unseal => ->. iIntros "H". iApply sim_bupd. by iApply sim_result.
Qed.
Lemma tac_sim_result_no_bupd v_t v_s Φ Δ π :
  envs_entails Δ (Φ v_t v_s) → envs_entails Δ (of_result v_t ⪯{π} of_result v_s {{ Φ }}).
Proof. rewrite envs_entails_unseal => ->. by iApply sim_result. Qed.

Lemma tac_sim_bind_val K_t K_s Δ Φ e_t f_t e_s f_s π :
  f_t = (λ e_t, fill K_t e_t) → (* as an eta expanded hypothesis so that we can `simpl` it *)
  f_s = (λ e_s, fill K_s e_s) →
  envs_entails Δ (e_t ⪯{π} e_s {{ λ e_t' e_s', f_t e_t' ⪯{π} f_s e_s' [{ Φ }] }})%I →
  envs_entails Δ (fill K_t e_t ⪯{π} fill K_s e_s [{ Φ }]).
Proof.
  rewrite envs_entails_unseal=> -> ->. intros Hs.
  iIntros "H". iApply (sim_bind e_t e_s K_t K_s Φ). by iApply Hs.
Qed.

Lemma tac_sim_bind K_t K_s Δ Φ e_t f_t e_s f_s π :
  f_t = (λ e_t, fill K_t e_t) → (* as an eta expanded hypothesis so that we can `simpl` it *)
  f_s = (λ e_s, fill K_s e_s) →
  envs_entails Δ (e_t ⪯{π} e_s [{ λ e_t' e_s', f_t e_t' ⪯{π} f_s e_s' [{ Φ }] }])%I →
  envs_entails Δ (fill K_t e_t ⪯{π} fill K_s e_s [{ Φ }]).
Proof.
  rewrite envs_entails_unseal=> -> ->. intros Hs.
  iIntros "H". iApply (sim_expr_bind K_t K_s e_t e_s Φ). by iApply Hs.
Qed.

Lemma tac_target_red_bind K_t e_t f_t Ψ Δ :
  f_t = (λ e_t, fill K_t e_t) →
  envs_entails Δ (target_red e_t (λ e_t', target_red (f_t e_t') Ψ) : iProp Σ) →
  envs_entails Δ (target_red (fill K_t e_t) Ψ).
Proof.
  rewrite envs_entails_unseal=> ->. intros Hs.
  iIntros "H". iApply target_red_bind. by iApply Hs.
Qed.

Lemma tac_source_red_bind K_s e_s f_s Ψ Δ π :
  f_s = (λ e_s, fill K_s e_s) →
  envs_entails Δ (source_red e_s π (λ e_s', source_red (f_s e_s') π Ψ) : iProp Σ) →
  envs_entails Δ (source_red (fill K_s e_s) π Ψ).
Proof.
  rewrite envs_entails_unseal=> ->. intros Hs.
  iIntros "H". iApply source_red_bind. by iApply Hs.
Qed.


(** Switching between judgments *)
Lemma tac_to_target Δ e_t e_s Φ π :
  envs_entails Δ (target_red e_t (λ e_t', e_t' ⪯{π} e_s [{ Φ }]))%I →
  envs_entails Δ (e_t ⪯{π} e_s [{ Φ }]).
Proof. rewrite envs_entails_unseal=> Hi. by rewrite -target_red_sim_expr. Qed.

Lemma tac_to_source Δ e_t e_s Φ π :
  envs_entails Δ (source_red e_s π (λ e_s', e_t ⪯{π} e_s' [{ Φ }]))%I →
  envs_entails Δ (e_t ⪯{π} e_s [{ Φ }]).
Proof. rewrite envs_entails_unseal=> Hi. by rewrite -source_red_sim_expr. Qed.

Lemma tac_target_to_sim Δ e_t e_s Φ π :
  envs_entails Δ (e_t ⪯{π} e_s [{ Φ }]) →
  envs_entails Δ (target_red e_t (λ e_t', e_t' ⪯{π} e_s [{ Φ }]))%I.
Proof.
  rewrite envs_entails_unseal=> Hi. rewrite -target_red_base.
  iIntros "He". iModIntro. by iApply Hi.
Qed.

Lemma tac_source_to_sim Δ e_t e_s Φ π :
  envs_entails Δ (e_t ⪯{π} e_s [{ Φ }]) →
  envs_entails Δ (source_red e_s π (λ e_s', e_t ⪯{π} e_s' [{ Φ }]))%I.
Proof.
  rewrite envs_entails_unseal=> Hi. rewrite -source_red_base.
  iIntros "He". iModIntro. by iApply Hi.
Qed.

Lemma tac_sim_expr_to_sim Δ e_t e_s Φ π :
  envs_entails Δ (e_t ⪯{π} e_s {{ Φ }}) →
  envs_entails Δ (e_t ⪯{π} e_s [{ lift_post Φ }])%I.
Proof. done. Qed.

Lemma tac_sim_to_sim_expr Δ e_t e_s Φ π :
  envs_entails Δ (e_t ⪯{π} e_s [{ lift_post Φ }]) →
  envs_entails Δ (e_t ⪯{π} e_s {{ Φ }})%I.
Proof. done. Qed.

End sim.


(** ** automation for source_red and target_red *)
(* the proofmode works with sim_expr, not sim *)
Ltac to_sim :=
  iStartProof;
  lazymatch goal with
  | |- envs_entails _ (sim_expr _ _ _ _) => idtac
  | |- envs_entails _ (sim _ _ ?e_t ?e_s) =>
      notypeclasses refine (tac_sim_to_sim_expr _ e_t e_s _ _ _)
  | |- envs_entails _ (target_red ?e_t (λ _, sim_expr _ _ _ _ )) =>
      notypeclasses refine (tac_target_to_sim _ e_t _ _ _ _)
  | |- envs_entails _ (source_red ?e_s _ (λ _, sim_expr _ _ _ _)) =>
      notypeclasses refine (tac_source_to_sim _ _ e_s _ _ _)
  | _ => fail "not a target_red or source_red of suitable shape"
  end.

Ltac to_target :=
  iStartProof;
  lazymatch goal with
  | |- envs_entails _ (target_red _ _) => idtac
  | _ =>
    to_sim;
    lazymatch goal with
    | |- envs_entails _ (sim_expr ?Φ ?π ?e_t ?e_s) =>
        notypeclasses refine (tac_to_target _ e_t e_s Φ π _)
    | _ => fail "to_target: not a sim"
    end
  end.

Ltac to_source :=
  iStartProof;
  lazymatch goal with
  | |- envs_entails _ (source_red _ _ _) => idtac
  | _ =>
    to_sim;
    lazymatch goal with
    | |- envs_entails _ (sim_expr ?Φ ?π ?e_t ?e_s) =>
        notypeclasses refine (tac_to_source _ e_t e_s Φ π _)
    | _ => fail "to_source: not a sim"
    end
  end.

(** ** simple automation for evaluation *)

(** Simplify the goal if it is [sim] of a value.
  If the postcondition already allows a bupd, do not add a second one.
  But otherwise, *do* add a bupd. This ensures that all the lemmas applied
  here are bidirectional, so we never will make a goal unprovable. *)
Ltac sim_result_head :=
  lazymatch goal with
  | |- envs_entails _ (sim (λ _ _, bupd _) _ (Val _) (Val _)) =>
      eapply tac_sim_value_no_bupd
  | |- envs_entails _ (sim (λ _ _, sim_expr _ _ _ _) _ (Val _) (Val _)) =>
      eapply tac_sim_value_no_bupd
  | |- envs_entails _ (sim (λ _ _, sim _ _ _ _) _ (Val _) (Val _)) =>
      eapply tac_sim_value_no_bupd
  | |- envs_entails _ (sim _ _ (Val _) (Val _)) =>
      eapply tac_sim_value
  | |- envs_entails _ (sim (λ _ _, bupd _) _ (Place _ _ _) (Place _ _ _)) =>
      eapply tac_sim_place_no_bupd
  | |- envs_entails _ (sim (λ _ _, sim_expr _ _ _ _) _ (Place _ _ _) (Place _ _ _)) =>
      eapply tac_sim_place_no_bupd
  | |- envs_entails _ (sim (λ _ _, sim _ _ _ _) _ (Place _ _ _) (Place _ _ _)) =>
      eapply tac_sim_place_no_bupd
  | |- envs_entails _ (sim _ _ (Place _ _ _) (Place _ _ _)) =>
      eapply tac_sim_place

  | |- envs_entails _ (sim (λ _ _, bupd _) _ (of_result _) (of_result _)) =>
      eapply tac_sim_result_no_bupd
  | |- envs_entails _ (sim (λ _ _, sim_expr _ _ _ _) _ (of_result _) (of_result _)) =>
      eapply tac_sim_result_no_bupd
  | |- envs_entails _ (sim (λ _ _, sim _ _ _ _) _ (of_result _) (of_result _)) =>
      eapply tac_sim_result_no_bupd
  | |- envs_entails _ (sim _ _ (of_result _) (of_result _)) =>
      eapply tac_sim_result
  end.

Tactic Notation "sim_expr_eval" tactic3(t) :=
  iStartProof;
  lazymatch goal with
  | |- envs_entails _ (sim_expr ?Φ ?π ?e_t ?e_s) =>
    notypeclasses refine (tac_sim_expr_eval _ _ e_t _ e_s _ π _ _ _);
      [let x := fresh in intros x; t; unfold x; notypeclasses refine eq_refl|let x := fresh in intros x; t; unfold x; notypeclasses refine eq_refl | ]
  | _ => fail "sim_expr_eval: not a 'sim"
  end.
Ltac sim_expr_simpl := sim_expr_eval simpl.

(* finish and switch back to a sim, if possible *)
Ltac sim_finish :=
  try sim_expr_simpl;      (* simplify occurences of subst/fill *)
  match goal with
  | |- envs_entails _ (sim_expr (lift_post _) _ ?e_t ?e_s) =>
      notypeclasses refine (tac_sim_expr_to_sim _ e_t e_s _ _ _)
  | |- envs_entails _ (sim_expr _ _ _ _) => idtac
  | |- envs_entails _ (sim _ _ _ _) => idtac
  end;
  pm_prettify.

(** target_red *)
Tactic Notation "target_red_expr_eval" tactic3(t) :=
  iStartProof;
  lazymatch goal with
  | |- envs_entails _ (target_red ?e_t ?Ψ) =>
    notypeclasses refine (tac_target_red_expr_eval _ _ e_t _ _ _);
      [let x := fresh in intros x; t; unfold x; notypeclasses refine eq_refl| ]
  | _ => fail "target_red_expr_eval: not a 'target_red"
  end.
Ltac target_expr_simpl := target_red_expr_eval simpl.

Ltac target_result_head :=
  lazymatch goal with
  | |- envs_entails _ (target_red (Val _) (λ _, bupd _)) =>
      eapply tac_target_red_base_no_bupd
  | |- envs_entails _ (target_red (Val _) (λ _, sim_expr _ _ _ _)) =>
      eapply tac_target_red_base_no_bupd
  | |- envs_entails _ (target_red (Val _) (λ _, sim _ _ _ _ )) =>
      eapply tac_target_red_base_no_bupd
  | |- envs_entails _ (target_red (Val _) (λ _, target_red _ _)) =>
      eapply tac_target_red_base_no_bupd
  | |- envs_entails _ (target_red (Val _) _) =>
      eapply tac_target_red_base
  | |- envs_entails _ (target_red (Place _ _ _) (λ _, bupd _)) =>
      eapply tac_target_red_base_no_bupd
  | |- envs_entails _ (target_red (Place _ _ _) (λ _, sim_expr _ _ _ _)) =>
      eapply tac_target_red_base_no_bupd
  | |- envs_entails _ (target_red (Place _ _ _) (λ _, sim _ _ _ _)) =>
      eapply tac_target_red_base_no_bupd
  | |- envs_entails _ (target_red (Place _ _ _) (λ _, target_red _ _)) =>
      eapply tac_target_red_base_no_bupd
  | |- envs_entails _ (target_red (Place _ _ _) _) =>
      eapply tac_target_red_base
  end.

Ltac target_finish :=
  target_expr_simpl;      (* simplify occurences of subst/fill *)
  first [target_result_head; try sim_finish | pm_prettify].

(** source_red *)
Tactic Notation "source_red_expr_eval" tactic3(t) :=
  iStartProof;
  lazymatch goal with
  | |- envs_entails _ (source_red ?e_s ?π ?Ψ) =>
    notypeclasses refine (tac_source_red_expr_eval _ _ e_s _ π _ _);
      [let x := fresh in intros x; t; unfold x; notypeclasses refine eq_refl| ]
  | _ => fail "source_red_expr_eval: not a 'target_red"
  end.
Ltac source_expr_simpl := source_red_expr_eval simpl.

Ltac source_result_head :=
  lazymatch goal with
  | |- envs_entails _ (source_red (Val _) _ (λ _, bupd _)) =>
      eapply tac_source_red_base_no_bupd
  | |- envs_entails _ (source_red (Val _) _ (λ _, sim_expr _ _ _ _)) =>
      eapply tac_source_red_base_no_bupd
  | |- envs_entails _ (source_red (Val _) _ (λ _, sim _ _ _ _)) =>
      eapply tac_source_red_base_no_bupd
  | |- envs_entails _ (source_red (Val _) _ (λ _, source_red _ _ _)) =>
      eapply tac_source_red_base_no_bupd
  | |- envs_entails _ (source_red (Val _) _ _) =>
      eapply tac_source_red_base; try iIntros (_ _)
  | |- envs_entails _ (source_red (Place _ _ _) _ (λ _, bupd _)) =>
      eapply tac_source_red_base_no_bupd
  | |- envs_entails _ (source_red (Place _ _ _) _ (λ _, sim_expr _ _ _ _)) =>
      eapply tac_source_red_base_no_bupd
  | |- envs_entails _ (source_red (Place _ _ _) _ (λ _, sim _ _ _ _)) =>
      eapply tac_source_red_base_no_bupd
  | |- envs_entails _ (source_red (Place _ _ _) _ (λ _, source_red _ _ _)) =>
      eapply tac_source_red_base_no_bupd
  | |- envs_entails _ (source_red (Place _ _ _) _ _) =>
      eapply tac_source_red_base; try iIntros (_ _)
  end.

Ltac source_finish :=
  source_expr_simpl;      (* simplify occurences of subst/fill *)
  first [source_result_head; try sim_finish | pm_prettify].

(* Note: this is not called automatically by the sim_finish tactical because
   that would make it impossible to do things that need access to the SI (like updating the heap bijection).
  NOTE: alternatively, have some fancier update modality that wraps an [update_si]?
 *)
Ltac sim_val := sim_finish; sim_result_head.

(** ** Pure reduction *)
Ltac solve_pure_sidecond :=
  (*TODO: have tactic adapted to our instances *)
  fast_done || (left; fast_done) || (right; fast_done).

(** The argument [efoc] can be used to specify the construct that should be
reduced. For example, you can write [wp_pure (EIf _ _ _)], which will search
for an [EIf _ _ _] in the expression, and reduce it.

The use of [open_constr] in this tactic is essential. It will convert all holes
(i.e. [_]s) into evars, that later get unified when an occurences is found
(see [unify e' efoc] in the code below). *)
Tactic Notation "target_pure" open_constr(efoc) :=
  iStartProof;
  to_target;
  lazymatch goal with
  | |- envs_entails _ (target_red ?e_t _) =>
    let e_t := eval simpl in e_t in
    reshape_expr e_t ltac:(fun K_t e_t' =>
      unify e_t' efoc;
      eapply (tac_target_red_pure _ _ e_t' _ K_t _ _);
      [ tc_solve                           (* PureExec *)
      | try solve_pure_sidecond            (* The pure condition for PureExec*)
      | target_finish                      (* new goal *)
      ])
    || fail "target_red_pure: cannot find" efoc "in" e_t "or" efoc "is not a redex"
  | _ => fail "target_red_pure: not a 'target_red"
  end.

(** We have not declared an instance for the reduction of while:
  usually, we do not want to reduce it arbitrarily, but instead do an induction. *)
(*Tactic Notation "target_if" := target_pure (If _ _ _).*)
(*Tactic Notation "target_if_true" := target_pure (If (LitV (LitBool true)) _ _).*)
(*Tactic Notation "target_if_false" := target_pure (If (LitV (LitBool false)) _ _).*)
(*Tactic Notation "target_unop" := target_pure (UnOp _ _).*)
(*Tactic Notation "target_binop" := target_pure (BinOp _ _ _).*)
(*Tactic Notation "target_op" := target_unop || target_binop.*)
Tactic Notation "target_let" := target_pure (Let (BNamed _) _ _).
Tactic Notation "target_seq" := target_pure (Let BAnon _ _).
Tactic Notation "target_proj" := target_pure (Proj _ _).
Tactic Notation "target_case" := target_pure (Case _ _).
(*Tactic Notation "target_proj" := target_pure (Fst _) || target_pure (Snd _).*)
(*Tactic Notation "target_match" := target_pure (Match _ _ _ _ _).*)
(*Tactic Notation "target_inj" := target_pure (InjL _) || target_pure (InjR _).*)
(*Tactic Notation "target_pair" := target_pure (Pair _ _).*)

Tactic Notation "target_while" :=
  let Hwhile := fresh "H" in
  pose (Hwhile := pure_while);
  target_pure (While _ _);
  clear Hwhile.

Ltac target_pures :=
  iStartProof;
  first [ (* The `;[]` makes sure that no side-condition magically spawns. *)
          progress repeat (target_pure _; [])
        | target_finish (* In case target_pure never ran, make sure we do the usual cleanup.*)
        ].

Tactic Notation "source_pure" open_constr(efoc) :=
  iStartProof;
  to_source;
  lazymatch goal with
  | |- envs_entails _ (source_red ?e_s _ _) =>
    let e_s := eval simpl in e_s in
    reshape_expr e_s ltac:(fun K_s e_s' =>
      unify e_s' efoc;
      eapply (tac_source_red_pure _ _ e_s' _ K_s _ _ _);
      [ tc_solve                       (* PureExec *)
      | try solve_pure_sidecond        (* The pure condition for PureExec *)
      | source_finish                  (* new goal *)
      ])
    || fail "source_red_pure: cannot find" efoc "in" e_s "or" efoc "is not a redex"
  | _ => fail "source_red_pure: not a 'sim'"
  end.

(*Tactic Notation "source_if" := source_pure (If _ _ _).*)
(*Tactic Notation "source_if_true" := source_pure (If (LitV (LitBool true)) _ _).*)
(*Tactic Notation "source_if_false" := source_pure (If (LitV (LitBool false)) _ _).*)
(*Tactic Notation "source_unop" := source_pure (UnOp _ _).*)
(*Tactic Notation "source_binop" := source_pure (BinOp _ _ _).*)
(*Tactic Notation "source_op" := source_unop || source_binop.*)
Tactic Notation "source_let" := source_pure (Let (BNamed _) _ _).
Tactic Notation "source_seq" := source_pure (Let BAnon _ _).
Tactic Notation "source_proj" := source_pure (Proj _ _).
Tactic Notation "source_case" := source_pure (Case _ _).
(*Tactic Notation "source_proj" := source_pure (Fst _) || source_pure (Snd _).*)
(*Tactic Notation "source_match" := source_pure (Match _ _ _ _ _).*)
(*Tactic Notation "source_inj" := source_pure (InjL _) || source_pure (InjR _).*)
(*Tactic Notation "source_pair" := source_pure (Pair _ _).*)

Tactic Notation "source_while" :=
  let Hwhile := fresh "H" in
  pose (Hwhile := pure_while);
  source_pure (While _ _);
  clear Hwhile.

Ltac source_pures :=
  iStartProof;
  first [ (* The `;[]` makes sure that no side-condition magically spawns. *)
          progress repeat (source_pure _; [])
        | source_finish (* In case source_red_pure never ran, make sure we do the usual cleanup.*)
        ].

Ltac sim_pures_int := (try target_pures); (try source_pures); try to_sim.
Ltac sim_pures := (try target_pures); (try source_pures); try (to_sim; sim_finish).

(** ** Bind tactics *)

Ltac sim_bind_core tac_sim_bind K_t K_s :=
  lazymatch eval hnf in K_t with
  | [] => lazymatch eval hnf in K_s with
          | [] => idtac
          | _ => eapply (tac_sim_bind K_t K_s); [simpl; reflexivity| simpl; reflexivity | ]
          end
  | _ => eapply (tac_sim_bind K_t K_s); [simpl; reflexivity| simpl; reflexivity | ]
  end.

Tactic Notation "sim_bind_base" constr(tac_sim_bind) open_constr(efoc_t) open_constr(efoc_s) :=
  iStartProof;
  to_sim;
  lazymatch goal with
  | |- envs_entails _ (sim_expr ?Q ?π ?e_t ?e_s) =>
    first [ reshape_expr e_t ltac:(fun K_t e_t' => unify e_t' efoc_t;
                                    first [ reshape_expr e_s ltac:(fun K_s e_s' => unify e_s' efoc_s; sim_bind_core tac_sim_bind K_t K_s)
                                           (* TODO: fix error handling *)
                                           | fail 1 "sim_bind: cannot find" efoc_s "in" e_s]
                                  )
          | fail 1 "sim_bind: cannot find" efoc_t "in" e_t ]
  | _ => fail "sim_bind: not a 'sim'"
  end.

Tactic Notation "sim_bind" open_constr(efoc_t) open_constr(efoc_s) :=
  sim_bind_base tac_sim_bind efoc_t efoc_s.
Tactic Notation "sim_bind_val" open_constr(efoc_t) open_constr(efoc_s) :=
  sim_bind_base tac_sim_bind_val efoc_t efoc_s.

Ltac target_bind_core K_t :=
  lazymatch eval hnf in K_t with
  | [] => idtac
  | _ => eapply (tac_target_red_bind K_t); [simpl; reflexivity| reduction.pm_prettify]
  end.

Tactic Notation "target_bind" open_constr(efoc_t) :=
  iStartProof;
  to_target;
  lazymatch goal with
  | |- envs_entails _ (target_red ?e_t ?Ψ) =>
    first [ reshape_expr e_t ltac:(fun K_t e_t' => unify e_t' efoc_t;
                                    target_bind_core K_t
                                  )
          | fail 1 "target_bind: cannot find" efoc_t "in" e_t ]
  | _ => fail "target_bind: not a 'target_red'"
  end.

Ltac source_bind_core K_s :=
  lazymatch eval hnf in K_s with
  | [] => idtac
  | _ => eapply (tac_source_red_bind K_s); [simpl; reflexivity| reduction.pm_prettify]
  end.

Tactic Notation "source_bind" open_constr(efoc_s) :=
  iStartProof;
  to_source;
  lazymatch goal with
  | |- envs_entails _ (source_red ?e_s ?π ?Ψ) =>
    first [ reshape_expr e_s ltac:(fun K_s e_s' => unify e_s' efoc_s;
                                    source_bind_core K_s
                                  )
          | fail 1 "source_bind: cannot find" efoc_s "in" e_s ]
  | _ => fail "source_bind: not a 'source_red'"
  end.

(* Tactics for common bind-apply-intros pattern *)
Tactic Notation "sim_apply" uconstr(ctx_t) uconstr(ctx_s) uconstr(Hl) uconstr(Hp) :=
  sim_bind ctx_t ctx_s;
  iApply (Hl);
  last (iIntros Hp; try iApply sim_expr_base). (* TODO: have a proper tactical for that base case *)
Tactic Notation "target_apply" uconstr(ctx) uconstr(Hl) uconstr(Hp) :=
  target_bind ctx;
  iApply (Hl);
  last (iIntros Hp; target_finish).
Tactic Notation "source_apply" uconstr(ctx) uconstr(Hl) uconstr(Hp) :=
  source_bind ctx;
  iApply (Hl);
  last (iIntros Hp; source_finish).


(** ** Automation related to stuckness *)

Ltac discr_source :=
  let discr _ :=
    iIntros "%";
    repeat match goal with
           | H : _ ∧ _ |- _ => destruct H
           | H : _ ∨ _ |- _ => destruct H
           | H : ∃ _, _ |- _ => destruct H
           end; subst in
  match goal with
  | |- envs_entails _ (source_red _ _) => iApply source_red_safe_implies; [discr ()]
  | |- envs_entails _ (sim_expr _ _ _ _) => iApply sim_safe_implies; [discr ()]
  | |- envs_entails _ (sim _ _ _ _) => iApply sim_safe_implies; [discr ()]
  end.


(** [safe_reach_bind e] works on goals of the form [safe_reach P e' σ Φ]
    and tries to find a subexpression of e' matching e and applies the bind lemma for
    it (similar to sim_bind and friends). *)
Tactic Notation "safe_reach_bind" open_constr(efoc) :=
  lazymatch goal with
  | |- safe_reach _ ?e _ _ =>
    reshape_expr e ltac:(fun K e' =>
                           unify e' efoc;
                           eapply (safe_reach_bind _ e' _ _ K); simpl
                        )
  end.

(** [safe_reach_bind e] works on goals of the form [safe_reach P e' σ (post_in_ectx Φ)]
    and tries to find a subexpression e'' of e' matching e and results in a goal
    [safe_reach P e'' σ (post_in_ectx Φ)] (i.e. it discards the evaluation context around e''). *)
Tactic Notation "safe_reach_fill" open_constr(efoc) :=
  lazymatch goal with
  | |- safe_reach _ ?e _ _ =>
    reshape_expr e ltac:(fun K e' =>
                           unify e' efoc;
                           eapply (fill_safe_reach _ e' _ _ K)
                        )
  end.

(** Applies gen_log_rel_subst for each element of [l],
    introduces the new terms under some fresh names,
    calls [cont] on the remaining goal,
    then reverts all the fresh names. *)
Local Ltac log_rel_subst_l l cont :=
  match l with
  | nil => cont ()
  | ?x :: ?l =>
    iApply (gen_log_rel_subst _ _ x _ _ (ValR [☠%S]) with "[]");
    [ by iApply value_rel_poison (* [val_rel] for the dummy value *)
    | let v_t := fresh "v_t" in
      let v_s := fresh "v_s" in
      let H := iFresh in
      iIntros (v_t v_s) "!#";
      let pat := constr:(intro_patterns.IIntuitionistic (intro_patterns.IIdent H)) in
      iIntros pat;
      rewrite ->!subst_map_singleton;
      log_rel_subst_l l ltac:(fun _ =>
        cont ();
        last iRevert (v_t v_s) H
      )
    ]
  end.

(** Turns an [gen_log_rel] goal into a [sim] goal by applying a
    suitable substitution. *)
Ltac log_rel :=
  iStartProof;
  lazymatch goal with
  | |- proofmode.environments.envs_entails _ (gen_log_rel ?val_rel ?town ?e_t ?e_s) =>
    let free := eval vm_compute in (elements (free_vars e_t ∪ free_vars e_s)) in
    log_rel_subst_l free ltac:(fun _ =>
        iApply gen_log_rel_closed;
        (* TODO: use proper reflection *)
        [simpl in *; repeat match goal with r : result |- _ => destruct r end; compute_done|])
  end.
