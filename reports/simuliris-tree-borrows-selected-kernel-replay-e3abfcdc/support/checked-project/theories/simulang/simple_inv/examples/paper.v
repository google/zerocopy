From simuliris.simulang Require Import lang notation tactics class_instances.
From iris.proofmode Require Import proofmode.
From simuliris.simulation Require Import slsls lifting .
From simuliris.simulang Require Import hoare behavior.
From simuliris.simulang.simple_inv Require Import inv adequacy.

(** * Examples from Section 2 of the paper *)
(** Here, we prove both the quadruples shown in the paper,
  and the logical relation (then deriving closed proofs of contextual refinement).

  Normally, we would not bother with the quadruples, since the statement we are really
   interested in is the contextual refinement.
 *)

Section fix_bi.
  Context `{!simpleGS Σ}.

  (** Example from 2.1 *)
  Definition ex_2_1_unopt : expr := let: "y" := ref(#42) in !"y".
  Definition ex_2_1_opt : expr := let: "y" := ref(#42) in #42.

  Lemma ex_2_1 π :
    ⊢ {{{ True }}} ex_2_1_opt ⪯[π] ex_2_1_unopt {{{ lift_post (λ v_t v_s, ⌜v_t = v_s⌝) }}}.
  Proof.
    iIntros "!> _". rewrite /ex_2_1_opt /ex_2_1_unopt.
    source_alloc l_s as "Hl_s" "Hf_s".
    target_alloc l_t as "Hl_t" "Hf_t".
    sim_pures. source_load. sim_val. done.
  Qed.

  (* for completeness : log_rel as described in Sec 4 *)
  Lemma ex_2_1_log :
    ⊢ log_rel ex_2_1_opt ex_2_1_unopt.
  Proof.
    log_rel. iModIntro. iIntros (π) "_".
    source_alloc l_s as "Hl_s" "Hf_s".
    target_alloc l_t as "Hl_t" "Hf_t".
    sim_pures. source_load. sim_val. done.
  Qed.

  (** First example from 2.2 *)
  Definition ex_2_2_1_unopt : expr :=
    let: "y" := ref(#42) in
    Call f#"f" #23;;
    !"y".
  Definition ex_2_2_1_opt : expr :=
    let: "y" := ref(#42) in
    Call f#"f" #23;;
    #42.

  Lemma ex_2_2_1 π :
    ⊢ {{{ True }}} ex_2_2_1_opt ⪯[π] ex_2_2_1_unopt {{{ lift_post (λ v_t v_s, ⌜v_t = v_s⌝) }}}.
  Proof.
    iIntros "!> _". rewrite /ex_2_2_1_opt /ex_2_2_1_unopt.
    source_alloc l_s as "Hl_s" "Hf_s".
    target_alloc l_t as "Hl_t" "Hf_t".
    sim_pures.
    sim_bind (Call _ _) (Call _ _). iApply sim_call; [done..|].
    iIntros (??) "_". iApply lift_post_val.
    source_load. sim_pures. sim_val. done.
  Qed.

  Lemma ex_2_2_1_log :
    ⊢ log_rel ex_2_2_1_opt ex_2_2_1_unopt.
  Proof.
    log_rel. iModIntro. iIntros (π) "_".
    source_alloc l_s as "Hl_s" "Hf_s".
    target_alloc l_t as "Hl_t" "Hf_t".
    sim_pures.
    sim_bind (Call _ _) (Call _ _). iApply sim_call; [done..|].
    iIntros (??) "_". iApply lift_post_val.
    source_load. sim_pures. sim_val. done.
  Qed.

  (** Second example from 2.2 *)
  Definition ex_2_2_2_unopt : expr :=
    let: "y" := ref(#42) in
    let: "z" := !"y" in
    Call f#"f" "y";;
    !"y" + "z".
  Definition ex_2_2_2_opt : expr :=
    let: "y" := ref(#42) in
    let: "z" := #42 in
    Call f#"f" "y";;
    !"y" + "z".

  Lemma ex_2_2_2 π :
    ⊢ {{{ True }}} ex_2_2_2_opt ⪯[π] ex_2_2_2_unopt {{{ lift_post (λ v_t v_s, ⌜v_t = v_s⌝) }}}.
  Proof.
    iIntros "!> _". rewrite /ex_2_2_2_opt /ex_2_2_2_unopt.
    source_alloc l_s as "Hl_s" "Hf_s".
    target_alloc l_t as "Hl_t" "Hf_t".
    source_load. sim_pures.
    (* escape locations *)
    iApply (sim_bij_insert with "Hf_t Hf_s Hl_t Hl_s []"); first done.
    iIntros "#Hb".
    sim_bind (Call _ _) (Call _ _). iApply sim_call; [done..|].
    iIntros (??) "_". iApply lift_post_val.
    sim_pures. sim_load v_t v_s as "Hv".
    (* [omitted in the description in the paper] we use source UB to know that the loaded values must be integers *)
    iApply sim_safe_implies. iIntros "[(%n & ->) _]".
    val_discr_source "Hv". sim_pures. sim_val. done.
  Qed.

  Lemma ex_2_2_2_log :
    ⊢ log_rel ex_2_2_2_opt ex_2_2_2_unopt.
  Proof.
    log_rel. iModIntro. iIntros (π) "_".
    source_alloc l_s as "Hl_s" "Hf_s".
    target_alloc l_t as "Hl_t" "Hf_t".
    source_load. sim_pures.
    (* escape locations *)
    iApply (sim_bij_insert with "Hf_t Hf_s Hl_t Hl_s []"); first done.
    iIntros "#Hb".
    sim_bind (Call _ _) (Call _ _). iApply sim_call; [done..|].
    iIntros (??) "_". iApply lift_post_val.
    sim_pures. sim_load v_t v_s as "Hv".
    (* [omitted in the description in the paper] we use source UB to know that the loaded values must be integers *)
    iApply sim_safe_implies. iIntros "[(%n & ->) _]".
    val_discr_source "Hv". sim_pures. sim_val. done.
  Qed.

  (** Example from 2.3 *)
  Definition ex_2_3_unopt : expr :=
    let: "p" := Call f#"f" #() in
    let: "x" := Fst "p" in
    let: "y" := Snd "p" in
    let: "z" := "x" `quot` "y" in
    if: "y" ≠ #0 then
      Call f#"g" "z"
    else Call f#"h" "z".

  Definition ex_2_3_opt : expr :=
    let: "p" := Call f#"f" #() in
    let: "x" := Fst "p" in
    let: "y" := Snd "p" in
    let: "z" := "x" `quot` "y" in
    Call f#"g" "z".

  Lemma ex_2_3 π :
    ⊢ {{{ True }}} ex_2_3_opt ⪯[π] ex_2_3_unopt {{{ lift_post (λ v_t v_s, True) }}}.
  Proof.
    iIntros "!> _". rewrite /ex_2_3_opt /ex_2_3_unopt.

    sim_bind (Call _ _) (Call _ _). iApply sim_call; [ done.. | ].
    iIntros (p_t p_s) "Hv". iApply lift_post_val.
    sim_pures.
    source_bind (Fst _).
    (* exploit source UB to know that the returned vlaue is a pair *)
    iApply source_red_safe_implies. iIntros "(%x_s & %y_s & ->)".
    iPoseProof (gen_val_rel_pair_source with "Hv") as "(%x_t & %y_t & -> & Hx_r & Hy_r)".
    source_pures. sim_pures.
    (* exploit source UB for the division *)
    source_bind (_ `quot` _)%E.
    iApply source_red_safe_implies. iIntros "[(%x & ->) (%y & -> & %Hy)]".
    (* reduce the divisions *)
    source_pure _.
    { rewrite /bin_op_eval. simpl.
      destruct (decide (y = 0%Z)) as [-> | _]; first done. reflexivity.
    }
    val_discr_source "Hx_r". val_discr_source "Hy_r".
    target_pure _.
    { rewrite /bin_op_eval. simpl.
      destruct (decide (y = 0%Z)) as [-> | _]; first done. reflexivity.
    }
    simpl. generalize (Z.quot x y) => nz.
    sim_pures.
    (* use the gained knowledge *)
    rewrite bool_decide_false; first last.
    { contradict Hy. by simplify_eq. }
    sim_pures. iApply sim_call; [ done.. | ].
    iIntros (??) "?". iApply lift_post_val. done.
  Qed.

  Lemma ex_2_3_log :
    ⊢ log_rel ex_2_3_opt ex_2_3_unopt.
  Proof.
    log_rel. iModIntro. iIntros (π) "_".
    sim_bind (Call _ _) (Call _ _). iApply sim_call; [ done.. | ].
    iIntros (p_t p_s) "Hv". iApply lift_post_val.
    sim_pures.
    source_bind (Fst _).
    (* exploit source UB to know that the returned vlaue is a pair *)
    iApply source_red_safe_implies. iIntros "(%x_s & %y_s & ->)".
    iPoseProof (gen_val_rel_pair_source with "Hv") as "(%x_t & %y_t & -> & Hx_r & Hy_r)".
    source_pures. sim_pures.
    (* exploit source UB for the division *)
    source_bind (_ `quot` _)%E.
    iApply source_red_safe_implies. iIntros "[(%x & ->) (%y & -> & %Hy)]".
    (* reduce the divisions *)
    source_pure _.
    { rewrite /bin_op_eval. simpl.
      destruct (decide (y = 0%Z)) as [-> | _]; first done. reflexivity.
    }
    val_discr_source "Hx_r". val_discr_source "Hy_r".
    target_pure _.
    { rewrite /bin_op_eval. simpl.
      destruct (decide (y = 0%Z)) as [-> | _]; first done. reflexivity.
    }
    simpl. generalize (Z.quot x y) => nz.
    sim_pures.
    (* use the gained knowledge *)
    rewrite bool_decide_false; first last.
    { contradict Hy. by simplify_eq. }
    sim_pures. iApply sim_call; [ done.. | ].
    iIntros (??) "H". iApply lift_post_val. iFrame.
  Qed.

  (** Example from 2.4 *)
  Definition ex_2_4_unopt : expr :=
    let: "x" := ref(#0) in
    while: (Call f#"f" (!"x")) do
      Call f#"g" (!"x")
    od.
  Definition ex_2_4_opt : expr :=
    let: "x" := ref(#0) in
    let: "r" := !"x" in
    while: (Call f#"f" "r") do
      Call f#"g" "r"
    od.

  Lemma ex_2_4 π :
    ⊢ {{{ True }}} ex_2_4_opt ⪯[π] ex_2_4_unopt {{{ lift_post (λ v_t v_s, True) }}}.
  Proof.
    iIntros "!> _". rewrite /ex_2_4_opt /ex_2_4_unopt.
    source_alloc l_s as "Hl_s" "Hf_s".
    target_alloc l_t as "Hl_t" "Hf_t".
    target_load. sim_pures.

    (* initiate coinduction with the following invariant:
      (compared with the paper version, we carry through the right to deallocate,
        for a more realistic example we might use that to deallocate the locations after
        the loop)
    *)
    set inv := (†l_s…s 1 ∗ †l_t…t 1 ∗ l_s ↦s #0 ∗ l_t ↦t #0)%I.
    iApply (sim_while_while inv with "[$Hf_s $Hl_s $Hf_t $Hl_t]").
    iModIntro.
    iIntros "(? & ? & Hl_s & Hl_t)".
    (* loop condition *)
    source_load.
    sim_bind (Call _ _) (Call _ _).
    iApply sim_call; [done..|].
    iIntros (v_t v_s) "Hv". iApply lift_post_val.
    (* retval must be bool *)
    iApply sim_safe_implies. iIntros "(%b & ->)".
    val_discr_source "Hv".

    (* CA on loop condition *)
    destruct b.
    - (* true, do a loop iteration *)
      sim_pures. source_load.
      sim_bind (Call _ _) (Call _ _).
      iApply sim_call;[done..|].
      iIntros (??) "_"; iApply lift_post_val.
      sim_pures.
      (* use the coinduction hypothesis *)
      iApply sim_expr_base.
      iRight. iFrame. done.
    - (* false, done with the loop *)
      sim_pures. iApply sim_expr_base. iLeft.
      iApply lift_post_val. done.
  Qed.

  Lemma ex_2_4_log :
    ⊢ log_rel ex_2_4_opt ex_2_4_unopt.
  Proof.
    log_rel. iModIntro. iIntros (π) "_".
    source_alloc l_s as "Hl_s" "Hf_s".
    target_alloc l_t as "Hl_t" "Hf_t".
    target_load. sim_pures.

    (* initiate coinduction with the following invariant:
      (compared with the paper version, we carry through the right to deallocate,
        for a more realistic example we might use that to deallocate the locations after
        the loop)
    *)
    set inv := (†l_s…s 1 ∗ †l_t…t 1 ∗ l_s ↦s #0 ∗ l_t ↦t #0)%I.
    iApply (sim_while_while inv with "[$Hf_s $Hl_s $Hf_t $Hl_t]").
    iModIntro.
    iIntros "(? & ? & Hl_s & Hl_t)".
    (* loop condition *)
    source_load.
    sim_bind (Call _ _) (Call _ _).
    iApply sim_call; [done..|].
    iIntros (v_t v_s) "Hv". iApply lift_post_val.
    (* retval must be bool *)
    iApply sim_safe_implies. iIntros "(%b & ->)".
    val_discr_source "Hv".

    (* CA on loop condition *)
    destruct b.
    - (* true, do a loop iteration *)
      sim_pures. source_load.
      sim_bind (Call _ _) (Call _ _).
      iApply sim_call;[done..|].
      iIntros (??) "_"; iApply lift_post_val.
      sim_pures.
      (* use the coinduction hypothesis *)
      iApply sim_expr_base.
      iRight. iFrame. done.
    - (* false, done with the loop *)
      sim_pures. iApply sim_expr_base. iLeft.
      iApply lift_post_val. done.
  Qed.

End fix_bi.


Section closed.
  (** Obtain a closed proof of [ctx_ref]. *)
  Lemma ex_2_1_ctx : ctx_ref ex_2_1_opt ex_2_1_unopt.
  Proof.
    set Σ := #[simpleΣ].
    apply (log_rel_adequacy Σ)=>?.
    apply ex_2_1_log.
  Qed.

  Lemma ex_2_2_1_ctx : ctx_ref ex_2_2_1_opt ex_2_2_1_unopt.
  Proof.
    set Σ := #[simpleΣ].
    apply (log_rel_adequacy Σ)=>?.
    apply ex_2_2_1_log.
  Qed.

  Lemma ex_2_2_2_ctx : ctx_ref ex_2_2_2_opt ex_2_2_2_unopt.
  Proof.
    set Σ := #[simpleΣ].
    apply (log_rel_adequacy Σ)=>?.
    apply ex_2_2_2_log.
  Qed.

  Lemma ex_2_3_ctx : ctx_ref ex_2_3_opt ex_2_3_unopt.
  Proof.
    set Σ := #[simpleΣ].
    apply (log_rel_adequacy Σ)=>?.
    apply ex_2_3_log.
  Qed.

  Lemma ex_2_4_ctx : ctx_ref ex_2_4_opt ex_2_4_unopt.
  Proof.
    set Σ := #[simpleΣ].
    apply (log_rel_adequacy Σ)=>?.
    apply ex_2_4_log.
  Qed.
End closed.
