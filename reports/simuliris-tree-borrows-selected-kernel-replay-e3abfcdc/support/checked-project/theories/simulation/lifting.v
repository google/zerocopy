From simuliris.simulation Require Import language slsls.
From iris Require Import bi.bi bi.lib.fixpoint_mono.
From iris.proofmode Require Import proofmode.

Import bi.

Section lang.
  Context {Λ : language}.
  Implicit Types (e : expr Λ) (P : prog Λ).

   Record pure_step (e1 e2 : expr Λ) := {
      pure_step_safe P σ1 : reducible P e1 σ1;
      pure_step_det P σ1 e2' σ2 efs:
        prim_step P e1 σ1 e2' σ2 efs → σ2 = σ1 ∧ e2' = e2 ∧ efs = []
    }.

  Notation pure_steps_tp := (Forall2 (rtc pure_step)).

  (* TODO: Exclude the case of [n=0], either here, or in [wp_pure] to avoid it
  succeeding when it did not actually do anything. *)
  Class PureExec (φ : Prop) (n : nat) (e1 e2 : expr Λ) :=
    pure_exec : φ → nsteps pure_step n e1 e2.
  Global Hint Mode PureExec - - ! - : typeclass_instances.

  Coercion fill : ectx >-> Funclass.
  Lemma pure_step_ctx (K : ectx Λ) e1 e2 :
    pure_step e1 e2 →
    pure_step (K e1) (K e2).
  Proof.
    intros [Hred Hstep]. split.
    - unfold reducible in *. naive_solver eauto using fill_prim_step.
    - intros P σ1 e2' σ2 efs Hpstep.
      by destruct (fill_reducible_prim_step _ _ _ _ _ _ _ (Hred P σ1) Hpstep) as
        (e2'' & -> & (-> & -> & ->)%Hstep).
  Qed.

  Lemma pure_step_nsteps_ctx (K : ectx Λ) n e1 e2 :
    nsteps pure_step n e1 e2 →
    nsteps pure_step n (K e1) (K e2).
  Proof. eauto using pure_step_ctx, nsteps_congruence. Qed.

  Lemma rtc_pure_step_ctx (K : ectx Λ) e1 e2 :
    rtc pure_step e1 e2 → rtc pure_step (K e1) (K e2).
  Proof. eauto using rtc_congruence, pure_step_ctx. Qed.

  (* We do not make this an instance because it is awfully general. *)
  Lemma pure_exec_ctx (K : ectx Λ) φ n e1 e2 :
    PureExec φ n e1 e2 →
    PureExec φ n (K e1) (K e2).
  Proof. rewrite /PureExec; eauto using pure_step_nsteps_ctx. Qed.

  Record pure_base_step (e1 e2 : expr Λ) := {
    pure_base_step_safe P σ1 : base_reducible P e1 σ1;
    pure_base_step_det P σ1 e2' σ2 efs :
      base_step P e1 σ1 e2' σ2 efs → σ2 = σ1 ∧ e2' = e2 ∧ efs = []
  }.

  Lemma pure_base_step_pure_step e1 e2 : pure_base_step e1 e2 → pure_step e1 e2.
  Proof.
    intros [Hp1 Hp2]. split.
    - intros P σ. destruct (Hp1 P σ) as (e2' & σ2 & efs & ?).
      eexists e2', σ2, efs. by apply base_prim_step.
    - intros P σ1 e2' σ2 efs ?%base_reducible_prim_step; eauto.
  Qed.

  (**
    Exploiting the assumption of safety to gain knowledge of a pure assertion.
   *)
  Class SafeImplies (ϕ : Prop) P (e : expr Λ) σ :=
    safe_implies : safe P e σ → ϕ.

  Lemma safe_implies_weaken P e σ (ϕ ψ : Prop)  :
    (ϕ → ψ) →
    SafeImplies ϕ P e σ → SafeImplies ψ P e σ.
  Proof. intros Hw Hi Hsafe%Hi. by apply Hw. Qed.

  Lemma safe_prim_step P (e : expr Λ) σ :
    safe P e σ → ∀ e' σ', prim_step P e σ e' σ' [] → safe P e' σ'.
  Proof.
    intros Hsafe e' σ' Hprim.
    eapply pool_steps_safe; last done.
    econstructor 2; last constructor.
    apply (Pool_step _ 0 [] _ _ [] []); done.
  Qed.

  Lemma irreducible_reach_stuck P e σ :
    to_val e = None → irreducible P e σ → reach_stuck P e σ.
  Proof.
    intros Hval Hirred. exists [e], σ, [].
    split; first constructor.
    exists e, 0; split; first done. split; done.
  Qed.

  Lemma pool_safe_implies {P e σ ϕ T π K} {Hsafei: SafeImplies ϕ P e σ}:
    pool_safe P T σ → T !! π = Some (fill K e) → ϕ.
  Proof.
    intros Hsafe ?. apply: Hsafei.
    eapply fill_safe. eapply pool_safe_threads_safe; done.
  Qed.

  Lemma safe_reach_safe_implies e σ Φ P ϕ {Him : SafeImplies ϕ P e σ}:
    (ϕ → safe_reach P e σ Φ) → safe_reach P e σ Φ.
  Proof.
    intros Hp Hsafe. apply Him in Hsafe as Hphi.
    apply Hp in Hphi. by apply Hphi.
  Qed.

  (* Formulation of [pool_safe_implies] which allows to use [eapply]
    to spawn goals for the preconditions. *)
  Lemma pool_safe_implies_app e T π K σ P ϕ Q {Him : SafeImplies ϕ P e σ} :
    T !! π = Some (fill K e) →
    pool_safe P T σ →
    (ϕ → Q) → Q.
  Proof.
    intros Hlook Hs. specialize (pool_safe_implies Hs Hlook). naive_solver.
  Qed.

  Lemma safe_reach_pure e e' n σ p ϕ Φ {Hpure : PureExec ϕ n e e'}:
    ϕ → safe_reach p e' σ Φ → safe_reach p e σ Φ.
  Proof.
    intros Hϕ Hreach. specialize (Hpure Hϕ).
    induction Hpure as [ e_s2 | n e_s1 e_s2 e_s3 Hstep _ IH]; first done.
    destruct Hstep as [Hsafe Hdet]. destruct (Hsafe p σ) as (e_s2' & σ_s2' & efs & Hprim).
    specialize (Hdet _ _ _ _ _ Hprim) as (-> & -> & ->).
    eapply safe_reach_step; first done. by apply IH.
  Qed.
End lang.

#[global]
Hint Mode SafeImplies + - - ! - : core.
#[global]
Hint Mode PureExec + - - ! - : core.

Section fix_sim.
  Context {PROP : bi} `{!BiBUpd PROP, !BiAffine PROP, !BiPureForall PROP}.
  Context {Λ : language} {s : simulirisGS PROP Λ}.

  Implicit Types
    (e_s e_t e: expr Λ)
    (P_s P_t P: prog Λ)
    (σ_s σ_t σ : state Λ).

  Lemma state_interp_pure_step P_t σ_t P_s σ_s e_s T e_s' K_s π:
    pure_step e_s e_s' →
    T !! π = Some (fill K_s e_s) →
    state_interp (PROP := PROP) P_t σ_t P_s σ_s T -∗
    state_interp P_t σ_t P_s σ_s (<[π:=fill K_s e_s']>T).
  Proof.
    intros [Hsafe Hred] ?. apply: state_interp_pure_prim_step; [done|].
    intros σ. eapply fill_prim_step.
    destruct (Hsafe P_s σ) as [?[? [? Hstep]]].
    by destruct (Hred _ _ _ _ _ Hstep) as [->[-> ->]].
  Qed.


  (** Pure reduction *)
  Lemma source_red_lift_pure π Ψ m e_s1 e_s2 ϕ :
    PureExec ϕ m e_s1 e_s2 →
    ϕ → source_red e_s2 π Ψ ⊢ source_red e_s1 π Ψ.
  Proof.
    intros Hp Hϕ. specialize (Hp Hϕ).
    induction Hp as [ e_s2 | n e_s1 e_s2 e_s3 Hstep _ IH]; first done.
    rewrite IH. iIntros "Hs". iApply source_red_step.
    iIntros (?? P_s σ_s ??) "[Hstate [% %]]". iModIntro. iExists e_s2, σ_s.
    iFrame.
    destruct (Hstep) as [Hred Hdet]. destruct (Hred P_s σ_s) as (e_s' & σ_s' & efs & Hs).
    specialize (Hdet _ _ _ _ _ Hs) as [-> [-> ->]].
    iSplitR. { iPureIntro. apply: no_forks_step; [done|]. apply: no_forks_refl. }
    by iApply state_interp_pure_step.
  Qed.

  Lemma target_red_lift_pure Ψ n e1 e2 ϕ :
    PureExec ϕ n e1 e2 →
    ϕ → target_red e2 Ψ ⊢ target_red e1 Ψ.
  Proof.
    intros Hp Hϕ. specialize (Hp Hϕ).
    induction Hp as [ e_t2 | n e_t1 e_t2 e_t3 Hpstep _ IH]; first done.
    rewrite IH. iIntros "Ht". iApply target_red_step.
    iIntros (?????) "Hstate". iModIntro. iSplitR. { iPureIntro. apply Hpstep. }
    iIntros (???) "%Hstep". iModIntro. apply Hpstep in Hstep as [-> [-> ->]]. by iFrame.
  Qed.

  (** Primitive reduction *)
  Lemma sim_lift_prim_step_both π e_t e_s Φ:
    (∀ P_t P_s σ_t σ_s T_s K_s, state_interp P_t σ_t P_s σ_s T_s ∗ ⌜T_s !! π = Some (fill K_s e_s)
        ∧ pool_safe P_s T_s σ_s⌝ ==∗
      ⌜reducible P_t e_t σ_t⌝ ∗
      ∀ e_t' efs_t σ_t',
        ⌜prim_step P_t e_t σ_t e_t' σ_t' efs_t⌝ ==∗
         ∃ e_s' efs_s σ_s', ⌜prim_step P_s e_s σ_s e_s' σ_s' efs_s⌝ ∗
            state_interp P_t σ_t' P_s σ_s' (<[π:=K_s e_s']>T_s ++ efs_s) ∗ e_t' ⪯{π} e_s' [{ Φ }] ∗
            ([∗ list] π'↦e_t0;e_s0 ∈ efs_t;efs_s, e_t0 ⪯{length T_s + π'} e_s0 [{lift_post (ext_rel (length T_s + π'))}]))
 -∗
    e_t ⪯{π} e_s [{ Φ }].
  Proof.
    iIntros "Hsim".
    rewrite sim_expr_unfold. iIntros (??????) "[Hstate [% %]]".
    iMod ("Hsim" with "[$Hstate ]") as "[Hred Hsim]"; first done. iModIntro. iRight; iLeft.
    iFrame. iIntros (e_t' efs_t σ_t') "Hstep".
    iMod ("Hsim" with "Hstep") as (e_s' efs_s σ_s') "(Hs & ? & ? & Hefs)".
    iRight. iModIntro. iExists _, _, _, _, _. iFrame. iPureIntro. constructor.
  Qed.

  Lemma sim_lift_prim_step_target e_t e_s Φ π :
    (∀ P_t P_s σ_t σ_s T_s K_s, state_interp P_t σ_t P_s σ_s T_s ∗ ⌜T_s !! π = Some (fill K_s e_s)
        ∧ pool_safe P_s T_s σ_s⌝ ==∗
      ⌜reducible P_t e_t σ_t⌝ ∗
      ∀ e_t' efs_t σ_t',
        ⌜prim_step P_t e_t σ_t e_t' σ_t' efs_t⌝ ==∗
          ⌜efs_t = []⌝ ∗
          state_interp P_t σ_t' P_s σ_s T_s ∗
          e_t' ⪯{π} e_s [{ Φ }]) -∗
    e_t ⪯{π} e_s [{ Φ }].
  Proof.
    iIntros "Ha".
    iApply sim_step_target. iIntros (??????) "[Hstate [% %]]".
    iMod ("Ha" with "[$Hstate//]") as "[Hred Hev]". iModIntro. iFrame.
    iIntros (e_t' efs_t σ_t') "Htarget". iMod ("Hev" with "Htarget") as "[Hstate Hev]".
    iModIntro; iExists e_s, _. rewrite list_insert_id //. iFrame. iPureIntro; constructor.
  Qed.

  Lemma sim_lift_prim_step_source e_t e_s Φ π :
    (∀ P_t P_s σ_t σ_s T_s K_s, state_interp P_t σ_t P_s σ_s T_s ∗ ⌜T_s !! π = Some (fill K_s e_s)
        ∧ pool_safe P_s T_s σ_s⌝ ==∗
      ∃ e_s' σ_s',
        ⌜prim_step P_s e_s σ_s e_s' σ_s' []⌝ ∗
          state_interp P_t σ_t P_s σ_s' (<[π := fill K_s e_s']>T_s) ∗
          e_t ⪯{π} e_s' [{ Φ }]) -∗
    e_t ⪯{π} e_s [{ Φ }].
  Proof.
    iIntros "Hsource". iApply sim_step_source.
    iIntros (??????) "[Hstate [% %]]".
    iMod ("Hsource" with "[$Hstate//]") as (e_s' σ_s') "[% Hstate]".
    iModIntro. iExists e_s', σ_s'. iFrame. iPureIntro.
    apply: no_forks_step; [done|]. by apply: no_forks_refl.
  Qed.

  (** Head reduction *)
  Lemma sim_lift_base_step_target e_t e_s Φ π :
    (∀ P_t P_s σ_t σ_s T_s K_s, state_interp P_t σ_t P_s σ_s T_s ∗ ⌜T_s !! π = Some (fill K_s e_s)
        ∧ pool_safe P_s T_s σ_s⌝ ==∗
      ⌜base_reducible P_t e_t σ_t⌝ ∗
      ∀ e_t' efs_t σ_t',
        ⌜base_step P_t e_t σ_t e_t' σ_t' efs_t⌝ ==∗
          ⌜efs_t = []⌝ ∗
          state_interp P_t σ_t' P_s σ_s T_s ∗
          e_t' ⪯{π} e_s [{ Φ }]) -∗
    e_t ⪯{π} e_s [{ Φ }].
  Proof.
    iIntros "Htarget". iApply sim_lift_prim_step_target. iIntros (??????) "[Hstate [% %]]".
    iMod ("Htarget" with "[$Hstate//]") as "(%Hred & Hstep)". iModIntro.
    iSplitR. { iPureIntro. by apply base_prim_reducible. }
    iIntros (e_t' efs_t σ_t') "%Hprim". iApply "Hstep".
    iPureIntro. by apply base_reducible_prim_step.
  Qed.

  (* for symmetry, in this lemma nothing actually happens *)
  Lemma sim_lift_base_step_source e_t e_s Φ π :
    (∀ P_t P_s σ_t σ_s T_s K_s, state_interp P_t σ_t P_s σ_s T_s ∗ ⌜T_s !! π = Some (fill K_s e_s)
        ∧ pool_safe P_s T_s σ_s⌝ ==∗
      ∃ e_s' σ_s',
        ⌜base_step P_s e_s σ_s e_s' σ_s' []⌝ ∗ |==>
          (state_interp P_t σ_t P_s σ_s' (<[π:= fill K_s e_s']>T_s) ∗
          e_t ⪯{π} e_s' [{ Φ }])) -∗
    e_t ⪯{π} e_s [{ Φ }].
  Proof.
    iIntros "Hsource". iApply sim_lift_prim_step_source.
    iIntros (??????) "[Hstate %]". iMod ("Hsource" with "[$Hstate//]") as (e_s' σ_s') "[% >Hstate]".
    iModIntro. iExists e_s', σ_s'. iFrame. iPureIntro. by apply base_prim_step.
  Qed.

  Lemma sim_lift_base_step_both e_t e_s Φ π:
    (∀ P_t P_s σ_t σ_s T_s K_s, state_interp P_t σ_t P_s σ_s T_s ∗ ⌜T_s !! π = Some (fill K_s e_s)
        ∧ pool_safe P_s T_s σ_s⌝ ==∗
      ⌜base_reducible P_t e_t σ_t⌝ ∗
      ∀ e_t' efs_t σ_t',
        ⌜base_step P_t e_t σ_t e_t' σ_t' efs_t⌝ ==∗
          ∃ e_s' efs_s σ_s', ⌜base_step P_s e_s σ_s e_s' σ_s' efs_s⌝ ∗
          state_interp P_t σ_t' P_s σ_s' (<[π:=fill K_s e_s']>T_s ++ efs_s) ∗ e_t' ⪯{π} e_s' [{ Φ }] ∗
          ([∗ list] π'↦e_t0;e_s0 ∈ efs_t;efs_s, e_t0 ⪯{length T_s + π'} e_s0 [{lift_post (ext_rel (length T_s + π'))}])) -∗
    e_t ⪯{π} e_s [{ Φ }].
  Proof.
    iIntros "Hsim". iApply sim_lift_prim_step_both. iIntros (??????) "[Hstate %Hnreach]".
    iMod ("Hsim" with "[$Hstate//]") as "(% & Hstep)".
    iModIntro. iSplitR. { iPureIntro. by eapply base_prim_reducible. }
    iIntros (e_t' efs_t σ_t') "%". iMod ("Hstep" with "[]") as (e_s' efs_s σ_s') "(% & Hstate & Hsim)".
    { iPureIntro. by eapply base_reducible_prim_step. }
    iModIntro. iExists e_s', efs_s, σ_s'. iFrame. iPureIntro. by eapply base_prim_step.
  Qed.

  (** Stuckness *)
  Lemma source_red_safe_reach ϕ e_s Ψ π :
    (∀ P_s σ_s, safe_reach P_s e_s σ_s (λ _ _, ϕ)) →
    (⌜ϕ⌝ -∗ source_red e_s π Ψ) -∗
    source_red e_s π Ψ.
  Proof.
    intros Hsr. iIntros "Hs".
    rewrite source_red_unfold.
    iIntros (?? P_s σ_s ??) "[Hstate [%Hpool %Hnreach]]".
    destruct (Hsr P_s σ_s) as (_ & _ & _ & ?).
    { eapply fill_safe. eapply pool_safe_threads_safe; done. }
    iMod ("Hs" with "[//] [$Hstate //]") as "Hs"; done.
  Qed.

  Lemma source_red_safe_implies ϕ e_s Ψ π :
    (∀ P_s σ_s, SafeImplies ϕ P_s e_s σ_s) →
    (⌜ϕ⌝ -∗ source_red e_s π Ψ) -∗
    source_red e_s π Ψ.
  Proof.
    intros Hsafer. iIntros "Hs".
    rewrite source_red_unfold.
    iIntros (?? P_s σ_s ??) "[Hstate [%Hpool %Hsafe]]".
    specialize (pool_safe_threads_safe _ _ _ _ _ Hsafe Hpool) as Hphi%fill_safe%Hsafer.
    iMod ("Hs" with "[//] [$Hstate //]") as "Hs"; done.
  Qed.

  Lemma sim_safe_implies ϕ e_s e_t Φ π :
    (∀ P_s σ_s, SafeImplies ϕ P_s e_s σ_s) →
    (⌜ϕ⌝ -∗ e_t ⪯{π} e_s [{ Φ }]) ⊢@{PROP}
     e_t ⪯{π} e_s [{ Φ }].
  Proof.
    intros Hsafer. iIntros "Hs".
    rewrite sim_expr_unfold /safe.
    iIntros (P_t σ_t P_s σ_s ??) "[Hstate [%Hpool %Hsafe]]".
    specialize (pool_safe_threads_safe _ _ _ _ _ Hsafe Hpool) as Hphi%fill_safe%Hsafer.
    iMod ("Hs" with "[//] [$Hstate //]") as "Hs"; done.
  Qed.

  (** Target eval *)
  Lemma target_red_lift_base_step Ψ e_t :
    ⊢ (∀ P_t σ_t P_s σ_s T_s, state_interp P_t σ_t P_s σ_s T_s ==∗
        (⌜base_reducible P_t e_t σ_t⌝ ∗ ∀ e_t' efs_t σ_t', ⌜base_step P_t e_t σ_t e_t' σ_t' efs_t⌝ ==∗
          ⌜efs_t = []⌝ ∗ state_interp P_t σ_t' P_s σ_s T_s ∗ target_red e_t' Ψ)) -∗
      target_red e_t Ψ.
  Proof.
    iIntros "Htarget". iApply target_red_step. iIntros (?????) "Hstate".
    iMod ("Htarget" with "Hstate") as "(%Hred & Hstep)". iModIntro.
    iSplitR. { iPureIntro. by apply base_prim_reducible. }
    iIntros (e_t' σ_t' efs_t) "%Hprim". iApply "Hstep".
    iPureIntro. by apply base_reducible_prim_step.
  Qed.

  (** source eval *)
  Lemma source_red_lift_base_step Ψ e_s π :
   ⊢ (∀ P_t σ_t P_s σ_s T_s K_s,
       state_interp P_t σ_t P_s σ_s T_s ∗ ⌜T_s !! π = Some (fill K_s e_s) ∧ pool_safe P_s T_s σ_s⌝
        ==∗ ∃ e_s' σ_s',
          ⌜base_step P_s e_s σ_s e_s' σ_s' []⌝ ∗
          |==> state_interp P_t σ_t P_s σ_s' (<[π:=K_s e_s']> T_s) ∗ source_red e_s' π Ψ) -∗
      source_red e_s π Ψ.
  Proof.
    iIntros "Hsource". iApply source_red_step.
    iIntros (??????) "[Hstate %Hnreach]".
    iMod ("Hsource" with "[$Hstate//]") as (e_s' σ_s') "[% >Hstate]".
    iModIntro. iExists e_s', σ_s'. iFrame. iPureIntro.
    apply: no_forks_step; [ by apply base_prim_step| apply: no_forks_refl].
  Qed.

  (** Call *)
  Lemma sim_lift_call Φ fn (v_t v_s : val Λ) π:
    ext_rel π v_t v_s -∗
    (∀ v_t v_s, ext_rel π v_t v_s -∗ Φ (of_val v_t) (of_val v_s)) -∗
    (of_call fn v_t) ⪯{π} (of_call fn v_s) [{ Φ }].
  Proof.
    iIntros "Hom Hv".
    rewrite sim_expr_unfold. iIntros (??????) "[? [% %]]". iModIntro. iRight; iRight.
    iExists fn, empty_ectx, v_t, empty_ectx, v_s, _.
    rewrite !fill_empty. iFrame.
    iSplitR; first done. iSplitR; first (iPureIntro; constructor).
    rewrite list_insert_id; [|done]. iFrame.
    iIntros (v_t' v_s') "Hv'". rewrite !fill_empty. iApply sim_expr_base. by iApply "Hv".
  Qed.

  (** Coinduction *)
  (** We have to give a "loop invariant" [inv] (that may assert ownership or say that e_t, e_s
      have a certain shape) that needs to be established initially and re-established each time
      we want to use the co-induction hypothesis.
   Alternatively, when we get to a point where [Φ] holds, we can break out of the co-induction.

   Thus, note that for this lemma it is crucial that we need not reduce to a value to get to the postcondition.

   In each step of the coinduction, we need to take a step in the source and target.
     Since we do not have any means to keep track of this in the simulation relation, this lemma
     requires to take steps in the beginning, before escaping to the simulation relation again.
  *)
  Lemma sim_lift_coind (inv : expr Λ → expr Λ → PROP) e_t e_s Φ π :
    (□ ∀ e_t e_s P_t P_s σ_t σ_s T_s K_s,
      inv e_t e_s -∗ state_interp P_t σ_t P_s σ_s T_s ∗ ⌜T_s !! π = Some (fill K_s e_s)
        ∧ pool_safe P_s T_s σ_s⌝ ==∗
        ⌜reducible P_t e_t σ_t⌝ ∗
        ∀ e_t' efs_t σ_t',
          ⌜prim_step P_t e_t σ_t e_t' σ_t' efs_t⌝ ==∗
          ∃ e_s' σ_s', ⌜efs_t = []⌝ ∗ ⌜prim_step P_s e_s σ_s e_s' σ_s' []⌝ ∗
            state_interp P_t σ_t' P_s σ_s' (<[π:=K_s e_s']>T_s) ∗
            e_t' ⪯{π} e_s' [{ λ e_t'' e_s'', Φ e_t'' e_s'' ∨ inv e_t'' e_s'' }]) -∗
    inv e_t e_s -∗
    e_t ⪯{π} e_s [{ Φ }].
  Proof.
    pose (F  := (λ Ψ π' e_t e_s, (∀ e_t e_s, Φ e_t e_s -∗ Ψ e_t e_s) ∗ ⌜π = π'⌝ ∗ inv e_t e_s)%I).
    iIntros "#H Inv". iApply (sim_expr_paco F).
    { solve_proper. }
    - iModIntro. clear. iIntros (Ψ π' e_t e_s) "[Himpl [% Hinv]]". subst π'.
      rewrite /lock_step. iIntros (p_t σ_t p_s σ_s T_s K_s) "Hs".
      iMod ("H" with "Hinv Hs") as "[$ Hcont]".
      iModIntro. iIntros (e_t' σ_t' efs_t Hstep).
      iMod ("Hcont" with "[//]") as (e_s' σ_s') "(H1 & H2 & H3 & H4)".
      iModIntro. iExists e_s', σ_s'. iFrame. rewrite /join_expr /F.
      iApply (sim_expr_mono with "[Himpl] H4").
      clear. iIntros (e_t e_s) "[H1|H1]".
      + iRight. by iApply "Himpl".
      + iLeft. by iFrame.
    - rewrite /F. iFrame. iSplit; [|done]. clear. iIntros (e_t e_s) "$".
  Qed.

  Lemma sim_lift_base_coind (inv : expr Λ → expr Λ → PROP) e_t e_s Φ π :
    (□ ∀ e_t e_s P_t P_s σ_t σ_s T_s K_s,
      inv e_t e_s -∗ state_interp P_t σ_t P_s σ_s T_s ∗ ⌜T_s !! π = Some (fill K_s e_s)
        ∧ pool_safe P_s T_s σ_s⌝ ==∗
        ⌜base_reducible P_t e_t σ_t⌝ ∗
        ∀ e_t' efs_t σ_t',
          ⌜base_step P_t e_t σ_t e_t' σ_t' efs_t⌝ ==∗
          ∃ e_s' σ_s', ⌜efs_t = []⌝ ∗ ⌜base_step P_s e_s σ_s e_s' σ_s' []⌝ ∗
            state_interp P_t σ_t' P_s σ_s' (<[π:=K_s e_s']> T_s) ∗
            e_t' ⪯{π} e_s' [{ λ e_t'' e_s'', Φ e_t'' e_s'' ∨ inv e_t'' e_s'' }]) -∗
    inv e_t e_s -∗
    e_t ⪯{π} e_s [{ Φ }].
  Proof.
    iIntros "#Ha Hinv". iApply (sim_lift_coind with "[] Hinv").
    iModIntro. iIntros (????????) "Hinv [Hstate [% %]]".
    iMod ("Ha" with "Hinv [$Hstate//]") as "[%Hred Hs]". iModIntro.
    iSplitR. { iPureIntro. by apply base_prim_reducible. }
    iIntros (???) "%Hprim". iMod ("Hs" with "[]") as (e_s' σ_s') "(% & %Hhead & Hstate & Hs)".
    { iPureIntro. by apply base_reducible_prim_step. }
    iModIntro. iExists e_s', σ_s'. iFrame. iPureIntro. split;[done|]. by apply base_prim_step.
  Qed.

  (* A generic coinduction lemma for expressions which are guarded by a pure step.
    This can for instance be used to derive lemmas for simulating while loops.
    However, it is insufficient for simulating recursion, as call reduction is not pure.
   *)
  Lemma sim_lift_coind_pure (inv : PROP) e_t e_t' e_s e_s' Φ π (ϕ ψ : Prop)
    {Hpure_t : PureExec ϕ 1 e_t e_t'} {Hpure_s : PureExec ψ 1 e_s e_s'} :
    ϕ →
    ψ →
    □ (inv -∗ e_t' ⪯{π} e_s' [{ λ e_t'' e_s'', Φ e_t'' e_s'' ∨ (⌜e_t'' = e_t⌝ ∗ ⌜e_s'' = e_s⌝ ∗ inv) }]) -∗
    inv -∗
    e_t ⪯{π} e_s [{ Φ }].
  Proof.
    iIntros (Hphi Hpsi ) "#Hsim Hinv".
    set inv' := (λ e_t' e_s', ⌜e_t' = e_t⌝ ∗ ⌜e_s' = e_s⌝ ∗ inv)%I.
    iApply (sim_lift_coind inv' with "[] [$Hinv //]").
    iModIntro.
    iIntros (? ? P_t P_s σ_t σ_s T_s K_s) "(-> & -> & Hinv) (Hstate & %Hpool & _)".
    specialize (Hpure_t Hphi) as Hpure_t. apply nsteps_once_inv in Hpure_t.
    specialize (Hpure_s Hpsi) as Hpure_s. apply nsteps_once_inv in Hpure_s.
    destruct Hpure_s as [Hred_s Hdet_s].
    destruct (Hred_s P_s σ_s) as (e_s'' & σ_s' & efs & Hs).
    destruct (Hdet_s _ _ _ _ _ Hs) as [-> [-> ->]].
    destruct Hpure_t as [Hred_t Hdet_t].
    iModIntro. iSplitR; first done.
    iIntros (e_t'' efs_t σ_t'' Hprim_t).
    destruct (Hdet_t _ _ _ _ _ Hprim_t) as [-> [-> ->]].
    iModIntro. iExists e_s', σ_s.
    iSplitR; first done. iSplitR; first done.
    iSplitL "Hstate"; first by iApply state_interp_pure_step.
    by iApply "Hsim".
  Qed.

  Lemma sim_lift_coind' (inv : expr Λ → expr Λ → PROP) e_t e_s Φ π :
    (□ ∀ e_t e_s P_t P_s σ_t σ_s T_s K_s,
      inv e_t e_s -∗ state_interp P_t σ_t P_s σ_s T_s ∗ ⌜T_s !! π = Some (fill K_s e_s)
        ∧ pool_safe P_s T_s σ_s⌝ ==∗
        ⌜reducible P_t e_t σ_t⌝ ∗
        ∀ e_t' efs_t σ_t',
          ⌜prim_step P_t e_t σ_t e_t' σ_t' efs_t⌝ ==∗
          ∃ e_s' σ_s', ⌜efs_t = []⌝ ∗ ⌜prim_step P_s e_s σ_s e_s' σ_s' []⌝ ∗
            state_interp P_t σ_t' P_s σ_s' (<[π:=K_s e_s']> T_s) ∗
            (∀ Ψ,
            □ (∀ e_t e_s, inv e_t e_s -∗ Ψ e_t e_s) -∗
            □ (∀ e_t e_s, Φ e_t e_s -∗ Ψ e_t e_s) -∗
            e_t' ⪯{π} e_s' [{ Ψ }])) -∗
    inv e_t e_s -∗
    e_t ⪯{π} e_s [{ Φ }].
  Proof.
    iIntros "#H Inv". iApply (sim_lift_coind with "[H] Inv").
    iModIntro. iIntros (????????) "Hinv Hs". iMod ("H" with "Hinv Hs") as "[$ Hs]".
    iModIntro. iIntros (???) "Hstep". iMod ("Hs" with "Hstep") as (e_s' σ_s') "($ & Hstep & Hsi & Hsim)".
    iExists e_s', σ_s'. iModIntro. iFrame. iApply "Hsim"; eauto.
  Qed.

  Lemma sim_lift_base_coind' (inv : expr Λ → expr Λ → PROP) e_t e_s Φ π:
    (□ ∀ e_t e_s P_t P_s σ_t σ_s T_s K_s,
      inv e_t e_s -∗ state_interp P_t σ_t P_s σ_s T_s ∗ ⌜T_s !! π = Some (fill K_s e_s)
        ∧ pool_safe P_s T_s σ_s⌝ ==∗
        ⌜base_reducible P_t e_t σ_t⌝ ∗
        ∀ e_t' efs_t σ_t',
          ⌜base_step P_t e_t σ_t e_t' σ_t' efs_t⌝ ==∗
          ∃ e_s' σ_s', ⌜efs_t = []⌝ ∗ ⌜base_step P_s e_s σ_s e_s' σ_s' []⌝ ∗
            state_interp P_t σ_t' P_s σ_s' (<[π:=K_s e_s']>T_s) ∗
            (∀ Ψ,
            □ (∀ e_t e_s, inv e_t e_s -∗ Ψ e_t e_s) -∗
            □ (∀ e_t e_s, Φ e_t e_s -∗ Ψ e_t e_s) -∗
            e_t' ⪯{π} e_s' [{ Ψ }])) -∗
    inv e_t e_s -∗
    e_t ⪯{π} e_s [{ Φ }].
  Proof.
    iIntros "#H Inv". iApply (sim_lift_base_coind with "[H] Inv").
    iModIntro. iIntros (????????) "Hinv Hs". iMod ("H" with "Hinv Hs") as "[$ Hs]".
    iModIntro. iIntros (???) "Hstep". iMod ("Hs" with "Hstep") as (e_s' σ_s') "($ & Hstep & Hsi & Hsim)".
    iExists e_s', σ_s'. iModIntro. iFrame. iApply "Hsim"; eauto.
  Qed.
End fix_sim.
