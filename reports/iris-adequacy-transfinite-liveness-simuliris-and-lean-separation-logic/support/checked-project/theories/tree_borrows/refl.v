From simuliris.simulation Require Import slsls lifting.
From simuliris.tree_borrows Require Import early_proofmode tactics.
From simuliris.tree_borrows.step_laws Require Import steps_refl steps_refl_delete steps_refl_endcall steps_retag steps_read_write_simple.
From simuliris.tree_borrows Require Import parallel_subst primitive_laws log_rel_structural wf behavior.

Section log_rel.
  Context `{!sborGS Σ}.

  Lemma log_rel_func x e_t e_s :
    free_vars e_t ∪ free_vars e_s ⊆ {[x]} →
    log_rel e_t e_s -∗
    func_rel (x, e_t) (x, e_s).
  Proof.
    iIntros (Hvars) "Hlog %v_t %v_s %π Hval".
    iApply (sim_wand with "[-]").
    - rewrite /= /apply_func /= -!subst_map_singleton.
      iApply (gen_log_rel_singleton with "Hlog Hval []"); done.
    - rewrite /ext_rel /=. iIntros (??) "[_ $]".
  Qed.

  Lemma scalar_wf_sound sc : scalar_wf sc → ⊢ sc_rel sc sc.
  Proof. intros Hwf. destruct sc; auto; simpl in *; done. Qed.

  Lemma value_wf_sound v : value_wf v → ⊢ value_rel v v.
  Proof.
    intros Hwf. iInduction v as [|a v] "IH"; first by iApply value_rel_empty.
    apply Forall_cons_1 in Hwf as [H1 H2]. rewrite /value_rel /=. iSplit.
    - by iApply scalar_wf_sound.
    - by iApply "IH".
  Qed.

  Lemma log_rel_var x : ⊢ log_rel (Var x) (Var x).
  Proof.
    rewrite /gen_log_rel.
    iIntros (? xs) "!# Hs _"; simpl.
    iDestruct (subst_map_rel_lookup _ x with "Hs") as (v_t v_s Hv) "Hrel"; first set_solver.
    rewrite !lookup_fmap Hv /=. sim_val. by iFrame.
  Qed.

  Local Tactic Notation "smart_sim_bind" uconstr(ctx_t) uconstr(ctx_s) uconstr(Hp) :=
    sim_bind_val ctx_t ctx_s;
    iApply (sim_wand with Hp).

  Lemma log_rel_let x e1_t e1_s e2_t e2_s :
    log_rel e1_t e1_s -∗ log_rel e2_t e2_s -∗ log_rel (Let x e1_t e2_t) (Let x e1_s e2_s).
  Proof.
    rewrite /gen_log_rel.
    iIntros "#IH1 #IH2" (? xs) "!# #Hs _"; simpl.
    smart_sim_bind (subst_map _ _) (subst_map _ _) "(IH1 [] [//])".
    { iApply (subst_map_rel_weaken with "[$]"). set_solver. }
    iIntros (v_t v_s) "[_ #Hv]". sim_pures. rewrite !subst'_subst_map.
    rewrite -(binder_insert_fmap fst (v_t, v_s)).
    rewrite -(binder_insert_fmap snd (v_t, v_s)).
    iApply ("IH2" with "[]"); last done.
    iApply (subst_map_rel_insert with "[] Hv").
    iApply (subst_map_rel_weaken with "[$]").
    destruct x as [|x]; first set_solver.
    apply elem_of_subseteq=>x'.
    destruct (decide (x = x')) as [<-|Hne]; set_solver.
  Qed.

  Local Ltac solve_rrel_refl :=
    sim_val;
    try rewrite (left_id True%I);
    first [
      iApply rrel_value_rel;
      first [iApply value_rel_poison|
            iApply value_rel_int |
            iApply value_rel_fnptr |
            iApply value_rel_callid |
            iApply value_rel_ptr |
            iApply value_rel_singleton
           ] |
      iApply rrel_place
    ];
    eauto.

  Tactic Notation "sc_discr_target" constr(H) :=
    first [iPoseProof (sc_rel_ptr_target with H) as "[[-> ?] |-> ]" |
          iPoseProof (sc_rel_fnptr_target with H) as "[ -> |-> ]" |
          iPoseProof (sc_rel_int_target with H) as "[ -> | ->]" |
          iPoseProof (sc_rel_cid_target with H) as "[(-> & ?) |-> ]" |
          iPoseProof (sc_rel_poison_target with H) as "->"
          ].
  Tactic Notation "sc_discr_source" constr(H) :=
      first [iPoseProof (sc_rel_ptr_source with H) as "[-> ?]" |
            iPoseProof (sc_rel_fnptr_source with H) as "->" |
            iPoseProof (sc_rel_int_source with H) as "->" |
            iPoseProof (sc_rel_cid_source with H) as "(-> & ?)" |
            iPoseProof (sc_rel_poison_target with H) as "->"
            ].
  Tactic Notation "val_discr_source" constr(H) :=
    let H' := iFresh in
    first [
      iPoseProof (rrel_singleton_source with H) as (? ->) H';
        sc_discr_source H' |
      iPoseProof (rrel_place_source with H) as (->) H' |
      iPoseProof (rrel_value_source with H) as (? ->) H'
    ];
    try iClear H; try iRename H' into H.

  Lemma log_rel_call e1_t e1_s e2_t e2_s :
    log_rel e1_t e1_s -∗ log_rel e2_t e2_s -∗ log_rel (Call e1_t e2_t) (Call e1_s e2_s).
  Proof.
    rewrite /gen_log_rel.
    iIntros "#IH1 #IH2". iIntros (? xs) "!# #Hs _"; simpl.
    smart_sim_bind (subst_map _ _) (subst_map _ _) "(IH2 [] [//])".
    { iApply (subst_map_rel_weaken with "[$]"). set_solver. }
    iIntros (v_t1 v_s1) "[_ #Hv1]".
    smart_sim_bind (subst_map _ _) (subst_map _ _) "(IH1 [] [//])".
    { iApply (subst_map_rel_weaken with "[$]"). set_solver. }
    iIntros (v_t2 v_s2) "[_ #Hv2]".
    discr_source. discr_source. val_discr_source "Hv2".
    iApply (sim_call with "Hv1"). iIntros (??) "Hr". iApply lift_post_val; eauto.
  Qed.

  Lemma log_rel_initcall :
    ⊢ log_rel InitCall InitCall.
  Proof.
    rewrite /gen_log_rel.
    iIntros (? xs) "!# #Hs _"; simpl.
    iApply sim_init_call.
    iIntros (c) "Hc". iApply (sim_cid_make_public with "Hc").
    iIntros "#Hsc". solve_rrel_refl. iModIntro. iDestruct "Hsc" as "[_ $]".
  Qed.

  Lemma log_rel_endcall e_t e_s :
    log_rel e_t e_s ⊢ log_rel (EndCall e_t) (EndCall e_s).
  Proof.
    rewrite /gen_log_rel.
    iIntros "#IH" (? xs) "!# #Hs _"; simpl.
    smart_sim_bind (subst_map _ _) (subst_map _ _) "(IH [] [//])".
    { iApply (subst_map_rel_weaken with "[$]"). set_solver. }
    iIntros (v_t v_s) "[_ #Hv]".
    discr_source. val_discr_source "Hv".
    iApply (sim_endcall with "Hv").
    sim_finish. sim_val. iModIntro. iSplit; first done. iApply value_rel_poison.
  Qed.


  (** a bit of work for eqop *)
  Lemma bor_interp_scalar_eq_source σ_t σ_s sc1_t sc1_s sc2_t sc2_s :
    scalar_eq σ_s.(shp) sc1_s sc2_s →
    sc_rel sc1_t sc1_s -∗
    sc_rel sc2_t sc2_s -∗
    bor_interp sc_rel σ_t σ_s -∗
    ⌜scalar_eq σ_t.(shp) sc1_t sc2_t⌝.
  Proof.
    iIntros (Hsc_eq) "Hsc1 Hsc2 Hbor".
    iPoseProof (bor_interp_get_pure with "Hbor") as "%Hp".
    destruct Hp as (_ & _ & _ & _ & _ & _ & Hdom_eq).
    inversion Hsc_eq; subst; sc_discr_source "Hsc1"; sc_discr_source "Hsc2".
    - done.
    - done.
    - iPureIntro. constructor 3.
      apply not_elem_of_dom. rewrite -Hdom_eq. apply not_elem_of_dom. done.
    - iPureIntro. constructor 4.
      apply not_elem_of_dom. rewrite -Hdom_eq. apply not_elem_of_dom. done.
  Qed.

  Lemma scalar_neq_source sc1_t sc1_s sc2_t sc2_s :
    scalar_neq sc1_s sc2_s →
    sc_rel sc1_t sc1_s -∗
    sc_rel sc2_t sc2_s -∗
    ⌜scalar_neq sc1_t sc2_t⌝.
  Proof.
    iIntros (Hsc_eq) "Hsc1 Hsc2".
    inversion Hsc_eq; subst; sc_discr_source "Hsc1"; sc_discr_source "Hsc2"; done.
  Qed.

  Lemma bor_interp_scalar_eq_target σ_t σ_s sc1_t sc1_s sc2_t sc2_s :
    sc1_s ≠ ScPoison →
    sc2_s ≠ ScPoison →
    scalar_eq σ_t.(shp) sc1_t sc2_t →
    sc_rel sc1_t sc1_s -∗
    sc_rel sc2_t sc2_s -∗
    bor_interp sc_rel σ_t σ_s -∗
    ⌜scalar_eq σ_s.(shp) sc1_s sc2_s⌝.
  Proof.
    iIntros (? ? Hsc_eq) "Hsc1 Hsc2 Hbor".
    iPoseProof (bor_interp_get_pure with "Hbor") as "%Hp".
    destruct Hp as (_ & _ & _ & _ & _ & _ & Hdom_eq).
    inversion Hsc_eq; subst; sc_discr_target "Hsc1"; try congruence; sc_discr_target "Hsc2"; try congruence.
    - done.
    - done.
    - iPureIntro. constructor 3.
      apply not_elem_of_dom. rewrite Hdom_eq. apply not_elem_of_dom. done.
    - iPureIntro. constructor 4.
      apply not_elem_of_dom. rewrite Hdom_eq. apply not_elem_of_dom. done.
  Qed.

  Lemma scalar_neq_target sc1_t sc1_s sc2_t sc2_s :
    sc1_s ≠ ScPoison →
    sc2_s ≠ ScPoison →
    scalar_neq sc1_t sc2_t →
    sc_rel sc1_t sc1_s -∗
    sc_rel sc2_t sc2_s -∗
    ⌜scalar_neq sc1_s sc2_s⌝.
  Proof.
    iIntros (? ? Hsc_eq) "Hsc1 Hsc2".
    inversion Hsc_eq; subst; sc_discr_target "Hsc1"; try congruence; sc_discr_target "Hsc2"; try congruence.
    all: done.
  Qed.

  Lemma sim_eq_op r1_t r1_s r2_t r2_s Φ π :
    rrel r1_t r1_s -∗
    rrel r2_t r2_s -∗
    (∀ sc_t sc_s, sc_rel sc_t sc_s -∗ #[sc_t] ⪯{π} #[sc_s] [{ Φ }]) -∗
    (r1_t = r2_t)%E ⪯{π} (r1_s = r2_s)%E [{ Φ }].
  Proof.
    iIntros "#Hr1 #Hr2 Hsim".
    iApply sim_lift_base_step_both. iIntros (P_t P_s σ_t σ_s T_s K_s) "((HP_t & HP_s & Hbor) & %Hpool & %Hsafe)".
    specialize (pool_safe_implies Hsafe Hpool) as (sc1_s & sc2_s & -> & -> & Heq).
    val_discr_source "Hr1". val_discr_source "Hr2".
    assert (sc1_s ≠ ScPoison ∧ sc2_s ≠ ScPoison) as [Hsc1_npoison Hsc2_npoison].
    { split; intros ->; destruct Heq as [ Heq | Heq]; inversion Heq. }
    iPoseProof (value_rel_singleton_source with "Hr1") as (sc1_t) "[-> Hsc1]".
    iPoseProof (value_rel_singleton_source with "Hr2") as (sc2_t) "[-> Hsc2]".
    iClear "Hr1 Hr2". destruct Heq as [Heq_s | Hneq_s].
    - iModIntro.
      iPoseProof (bor_interp_scalar_eq_source _ _ _ _ _ _ Heq_s with "Hsc1 Hsc2 Hbor") as "%Heq_t".
      iSplitR. { iPureIntro. do 3 eexists. econstructor. econstructor. eapply BinOpEqTrue. done. }
      iIntros (? ? ? ?). inv_base_step.
      (* note: evaluation is non-deterministic here; we have to mirror the behavior in the source *)
      + iModIntro. iExists _, _, _.
        iSplitR. { iPureIntro. econstructor; econstructor; eapply BinOpEqTrue. done. }
        iFrame. iSplitL; last done. iApply "Hsim". done.
      + iModIntro. iExists _, _, _.
        iPoseProof (scalar_neq_target with "Hsc1 Hsc2") as "%"; [done.. | ].
        iSplitR. { iPureIntro. econstructor; econstructor; eapply BinOpEqFalse. done. }
        iFrame. iSplitL; last done. by iApply "Hsim".
    - iModIntro.
      iPoseProof (scalar_neq_source with "Hsc1 Hsc2") as "%Hneq_t"; first done.
      iSplitR. { iPureIntro. do 3 eexists. econstructor. econstructor. eapply BinOpEqFalse. done. }
      iIntros (? ? ? ?). inv_base_step.
      (* note: evaluation is non-deterministic here; we have to mirror the behavior in the source *)
      + iModIntro. iExists _, _, _.
        iPoseProof (bor_interp_scalar_eq_target with "Hsc1 Hsc2 Hbor") as "%"; [done..|].
        iSplitR. { iPureIntro. econstructor; econstructor; eapply BinOpEqTrue. done. }
        iFrame. iSplitL; last done. iApply "Hsim". done.
      + iModIntro. iExists _, _, _.
        iSplitR. { iPureIntro. econstructor; econstructor; eapply BinOpEqFalse. done. }
        iFrame. iSplitL; last done. by iApply "Hsim".
  Qed.

  Lemma log_rel_binop e1_t e1_s e2_t e2_s o :
    log_rel e1_t e1_s -∗ log_rel e2_t e2_s -∗ log_rel (BinOp o e1_t e2_t) (BinOp o e1_s e2_s).
  Proof.
    rewrite /gen_log_rel.
    iIntros "#IH1 #IH2" (? xs) "!# #Hs _"; simpl.
    smart_sim_bind (subst_map _ e2_t) (subst_map _ e2_s) "(IH2 [] [//])".
    { iApply (subst_map_rel_weaken with "[$]"). set_solver. }
    iIntros (v_t2 v_s2) "[_ Hv2]".
    smart_sim_bind (subst_map _ e1_t) (subst_map _ e1_s) "(IH1 [] [//])".
    { iApply (subst_map_rel_weaken with "[$]"). set_solver. }
    iIntros (v_t1 v_s1) "[_ Hv1]".
    destruct o; sim_pures;
      try (discr_source; val_discr_source "Hv1"; val_discr_source "Hv2";
            sim_pures; solve_rrel_refl).
    iApply (sim_eq_op with "Hv1 Hv2"). iIntros (??) "Hsc". sim_pures.
    solve_rrel_refl.
  Qed.

  Lemma log_rel_proj e1_t e1_s e2_t e2_s :
    log_rel e1_t e1_s -∗ log_rel e2_t e2_s -∗ log_rel (Proj e1_t e2_t) (Proj e1_s e2_s).
  Proof.
    rewrite /gen_log_rel.
    iIntros "#IH1 #IH2" (? xs) "!# #Hs _"; simpl.
    smart_sim_bind (subst_map _ e2_t) (subst_map _ e2_s) "(IH2 [] [//])".
    { iApply (subst_map_rel_weaken with "[$]"). set_solver. }
    iIntros (v_t2 v_s2) "[_ Hv2]".
    smart_sim_bind (subst_map _ e1_t) (subst_map _ e1_s) "(IH1 [] [//])".
    { iApply (subst_map_rel_weaken with "[$]"). set_solver. }
    iIntros (v_t1 v_s1) "[_ Hv1]".
    discr_source. val_discr_source "Hv2". val_discr_source "Hv1".
    iDestruct (value_rel_length with "Hv1") as %EqL.
    iDestruct (value_rel_lookup with "Hv1") as (sc_t sc_s Eqt Eqs) "Hsc".
    {  rewrite EqL. eapply Nat2Z.inj_lt, lookup_lt_Some; eauto. }
    target_proj; [done|]. source_proj; [done|]. solve_rrel_refl.
  Qed.

  Lemma log_rel_conc e1_t e1_s e2_t e2_s :
    log_rel e1_t e1_s -∗ log_rel e2_t e2_s -∗ log_rel (Conc e1_t e2_t) (Conc e1_s e2_s).
  Proof.
    rewrite /gen_log_rel.
    iIntros "#IH1 #IH2" (? xs) "!# #Hs _"; simpl.
    smart_sim_bind (subst_map _ e2_t) (subst_map _ e2_s) "(IH2 [] [//])".
    { iApply (subst_map_rel_weaken with "[$]"). set_solver. }
    iIntros (v_t2 v_s2) "[_ Hv2]".
    smart_sim_bind (subst_map _ e1_t) (subst_map _ e1_s) "(IH1 [] [//])".
    { iApply (subst_map_rel_weaken with "[$]"). set_solver. }
    iIntros (v_t1 v_s1) "[_ Hv1]".
    discr_source. val_discr_source "Hv2". val_discr_source "Hv1".
    sim_pures. sim_val. iSplitR; first done.
    rewrite rrel_value_rel. iApply (value_rel_app with "Hv1 Hv2").
  Qed.

  Lemma log_rel_deref e_t e_s T :
    log_rel e_t e_s -∗ log_rel (Deref e_t T) (Deref e_s T).
  Proof.
    rewrite /gen_log_rel.
    iIntros "#IH" (? xs) "!# #Hs _"; simpl.
    smart_sim_bind (subst_map _ e_t) (subst_map _ e_s) "(IH [] [//])".
    { iApply (subst_map_rel_weaken with "[$]"). set_solver. }
    iIntros (v_t v_s) "[_ Hv]".
    discr_source. val_discr_source "Hv".
    sim_pures. solve_rrel_refl.
  Qed.

  Lemma log_rel_ref e_t e_s :
    log_rel e_t e_s -∗ log_rel (Ref e_t) (Ref e_s).
  Proof.
    rewrite /gen_log_rel.
    iIntros "#IH" (? xs) "!# #Hs _"; simpl.
    smart_sim_bind (subst_map _ e_t) (subst_map _ e_s) "(IH [] [//])".
    { iApply (subst_map_rel_weaken with "[$]"). set_solver. }
    iIntros (v_t v_s) "[_ Hv]".
    discr_source. val_discr_source "Hv".
    sim_pures. solve_rrel_refl.
  Qed.

  Lemma log_rel_copy e_t e_s :
    log_rel e_t e_s -∗ log_rel (Copy e_t) (Copy e_s).
  Proof.
    rewrite /gen_log_rel.
    iIntros "#IH" (? xs) "!# #Hs _"; simpl.
    smart_sim_bind (subst_map _ e_t) (subst_map _ e_s) "(IH [] [//])".
    { iApply (subst_map_rel_weaken with "[$]"). set_solver. }
    iIntros (v_t v_s) "[_ Hv]".
    discr_source. val_discr_source "Hv".
    iApply (sim_copy_public with "[Hv]"). { by iApply rrel_place. }
    iIntros (v_t v_s) "Hv". sim_val. eauto.
  Qed.

  Lemma log_rel_write e1_t e1_s e2_t e2_s :
    log_rel e1_t e1_s -∗
    log_rel e2_t e2_s -∗
    log_rel (Write e1_t e2_t) (Write e1_s e2_s).
  Proof.
    rewrite /gen_log_rel.
    iIntros "#IH1 #IH2" (? xs) "!# #Hs _"; simpl.
    smart_sim_bind (subst_map _ e2_t) (subst_map _ e2_s) "(IH2 [] [//])".
    { iApply (subst_map_rel_weaken with "[$]"). set_solver. }
    iIntros (v_t2 v_s2) "[_ Hv2]".
    smart_sim_bind (subst_map _ e1_t) (subst_map _ e1_s) "(IH1 [] [//])".
    { iApply (subst_map_rel_weaken with "[$]"). set_solver. }
    iIntros (v_t1 v_s1) "[_ Hv1]".
    discr_source. val_discr_source "Hv1". val_discr_source "Hv2".
    iApply (sim_write_public with "[Hv1] Hv2"). { by iApply rrel_place. }
    solve_rrel_refl.
  Qed.
  
  Lemma log_rel_retag e1_t e1_s e2_t e2_s pk im T k :
    log_rel e1_t e1_s -∗
    log_rel e2_t e2_s -∗
    log_rel (Retag e1_t e2_t pk im T k) (Retag e1_s e2_s pk im T k).
  Proof.
    rewrite /gen_log_rel.
    iIntros "#IH1 #IH2" (? xs) "!# #Hs _"; simpl.
    smart_sim_bind (subst_map _ e2_t) (subst_map _ e2_s) "(IH2 [] [//])".
    { iApply (subst_map_rel_weaken with "[$]"). set_solver. }
    iIntros (v_t2 v_s2) "[_ Hv2]".
    smart_sim_bind (subst_map _ e1_t) (subst_map _ e1_s) "(IH1 [] [//])".
    { iApply (subst_map_rel_weaken with "[$]"). set_solver. }
    iIntros (v_t1 v_s1) "[_ Hv1]".
    discr_source. val_discr_source "Hv1". val_discr_source "Hv2".
    iApply (sim_retag_public with "[-]").
    { by iApply value_rel_ptr. }
    iIntros (t) "Hv". sim_val. eauto.
  Qed.

  Local Lemma sim_case π e_t e_s el_t el_s Ψ :
    e_t ⪯{π} e_s {{ rrel }} -∗
    ([∗ list] e_t';e_s' ∈ el_t;el_s, e_t' ⪯{π} e_s' [{ Ψ }]) -∗
    Case e_t el_t ⪯{π} Case e_s el_s [{ Ψ }].
  Proof.
    iIntros "He Hle".
    smart_sim_bind e_t e_s "He".
    iIntros (v_t v_s) "Hv".
    discr_source. val_discr_source "Hv".
    iDestruct (big_sepL2_length with "Hle") as %EqL.
    rename select Z into i.
    rename select (_ !! _ = Some _) into Hls.
    assert (∃ e_t', el_t !! Z.to_nat i = Some e_t') as [? Hlt].
    { apply lookup_lt_is_Some_2. apply lookup_lt_Some in Hls. by rewrite EqL. }
    target_case; [done|]. source_case; [done|]. sim_pures.
    iApply (big_sepL2_lookup _ _ _ _ _ _ Hlt Hls with "Hle").
  Qed.

  Lemma log_rel_case e_t e_s el_t el_s :
    log_rel e_t e_s -∗
    ([∗ list] e_t';e_s' ∈ el_t;el_s, log_rel e_t' e_s') -∗
    log_rel (Case e_t el_t) (Case e_s el_s).
  Proof.
    rewrite /gen_log_rel.
    iIntros "#IH1 #IH2" (? xs) "!# #Hs _"; simpl subst_map.
    iApply sim_case.
    { setoid_rewrite (left_id True%I (∗)%I). iApply "IH1"; last done.
      iApply (subst_map_rel_weaken with "[$]"). set_solver. }
    rewrite big_sepL2_fmap_l big_sepL2_fmap_r.
    iApply (big_sepL2_impl with "IH2").
    iIntros (i e_t' e_s' Hlt Hls) "!# #He". iApply "He"; last done.
    iApply (subst_map_rel_weaken with "[$]").
    apply list_elem_of_lookup_2 in Hls, Hlt.
    apply (free_vars_case_2 e_s) in Hls. apply (free_vars_case_2 e_t) in Hlt.
    set_solver+Hls Hlt.
  Qed.

  Lemma log_rel_while e1_t e1_s e2_t e2_s :
    log_rel e1_t e1_s -∗
    log_rel e2_t e2_s -∗
    log_rel (While e1_t e2_t) (While e1_s e2_s).
  Proof.
    rewrite /gen_log_rel.
    iIntros "#IH1 #IH2" (? xs) "!# #Hs _"; simpl.
    iApply (sim_while_while emp%I with "[//]").
    iModIntro; iIntros "_".
    iApply sim_case.
    { setoid_rewrite (left_id True%I (∗)%I). iApply "IH1"; last done.
      iApply (subst_map_rel_weaken with "[$]"). set_solver. }
    rewrite big_sepL2_cons big_sepL2_singleton. iSplitL.
    - iApply sim_expr_base. iLeft. iApply (lift_post_val _ (ValR [_]) (ValR [_])).
      rewrite rrel_value_rel. iSplit; first done. iApply value_rel_poison.
    - smart_sim_bind (subst_map _ e2_t) (subst_map _ e2_s) "(IH2 [] [//])".
      { iApply (subst_map_rel_weaken with "[$]"). set_solver. }
      iIntros (? ?) "_"; sim_pures. iApply sim_expr_base. iRight. by eauto.
  Qed.

  Lemma log_rel_fork e_t e_s :
    log_rel e_t e_s ⊢ log_rel (Fork e_t) (Fork e_s).
  Proof.
    rewrite /gen_log_rel.
    iIntros "#IH" (? xs) "!# #Hs _"; simpl.
    iApply (sim_fork with "[]"). { solve_rrel_refl. }
    iIntros (?). setoid_rewrite (left_id True%I (∗)%I). by iApply "IH".
  Qed.

  Lemma log_rel_alloc T :
    ⊢ log_rel (Alloc T) (Alloc T).
  Proof.
    rewrite /gen_log_rel.
    iIntros (? xs) "!# #Hs _"; simpl. iApply sim_alloc_public.
    iIntros (t l) "Hp Hr". sim_val. by iFrame.
  Qed.

  Lemma log_rel_free e_t e_s :
    log_rel e_t e_s ⊢ log_rel (Free e_t) (Free e_s).
  Proof.
    rewrite /gen_log_rel.
    iIntros "#IH" (? xs) "!# #Hs _"; simpl.
    smart_sim_bind (subst_map _ _) (subst_map _ _) "(IH [] [//])".
    { iApply (subst_map_rel_weaken with "[$]"). set_solver. }
    iIntros (v_t v_s) "[_ Hv]".
    discr_source. val_discr_source "Hv".
    iApply (sim_free_public with "[Hv]"). { by iApply rrel_place. }
    solve_rrel_refl.
  Qed.

  Lemma log_rel_result v_t v_s :
    rrel v_t v_s ⊢ log_rel (of_result v_t) (of_result v_s).
  Proof.
    rewrite /gen_log_rel.
    iIntros "#Hv" (? xs) "!# #Hs _"; simpl. rewrite !subst_map_of_result.
    sim_val; eauto with iFrame.
  Qed.
End log_rel.

Section refl.
  Context `{!sborGS Σ}.

  Theorem sb_log_rel_structural : log_rel_structural treeborrows_wf.
  Proof.
    intros e_t e_s ?? Hwf Hs. iIntros "IH".
    destruct e_s, e_t => //; simpl in Hs; simplify_eq.
    all: try iDestruct "IH" as "[IH IH1]".
    all: try iDestruct "IH1" as "[IH1 IH2]".
    - (* Value *)
      iApply (log_rel_result (ValR _) (ValR _)). by iApply value_wf_sound.
    - (* Var *)
      by iApply log_rel_var.
    - (* Call *)
      by iApply (log_rel_call with "IH IH1").
    - (* InitCall *)
      by iApply log_rel_initcall.
    - (* EndCall *)
      by iApply (log_rel_endcall with "IH").
    - (* Proj *)
      by iApply (log_rel_proj with "IH IH1").
    - (* Conc *)
      by iApply (log_rel_conc with "IH IH1").
    - (* BinOp *)
      by iApply (log_rel_binop with "IH IH1").
    - (* Deref *)
      by iApply (log_rel_deref with "IH").
    - (* Ref *)
      by iApply (log_rel_ref with "IH").
    - (* Copy *)
      by iApply (log_rel_copy with "IH").
    - (* Write *)
      by iApply (log_rel_write with "IH IH1").
    - (* Alloc *)
      by iApply log_rel_alloc.
    - (* Free *)
      by iApply log_rel_free.
    - (* Retag *)
      by iApply (log_rel_retag with "IH IH1").
    - (* Let *)
      by iApply (log_rel_let with "IH IH1").
    - (* Case *)
      by iApply (log_rel_case with "IH IH1").
    - (* Fork *)
      by iApply (log_rel_fork with "IH").
    - (* While *)
      by iApply (log_rel_while with "IH IH1").
  Qed.

  Corollary log_rel_refl e :
    expr_wf e →
    ⊢ log_rel e e.
  Proof.
    intros ?. iApply log_rel_refl; first by apply sb_log_rel_structural. done.
  Qed.

  Corollary log_rel_ctx C e_t e_s :
    ctx_wf C →
    log_rel e_t e_s -∗ log_rel (fill_ctx C e_t) (fill_ctx C e_s).
  Proof.
    intros ?. iApply log_rel_ctx; first by apply sb_log_rel_structural. done.
  Qed.

  Corollary log_rel_ectx K e_t e_s :
    ectx_wf K →
    log_rel e_t e_s -∗ log_rel (fill K e_t) (fill K e_s).
  Proof.
    intros ?. iApply log_rel_ectx; first by apply sb_log_rel_structural. done.
  Qed.

  Lemma log_rel_closed_1 e_t e_s π :
    free_vars e_t ∪ free_vars e_s = ∅ →
    log_rel e_t e_s ⊢ e_t ⪯{π} e_s {{ λ v_t v_s, rrel v_t v_s }}.
  Proof.
    iIntros (?) "#Hrel".
    iApply sim_mono; last iApply (gen_log_rel_closed_1 with "Hrel"); [|done..].
    iIntros (v_t v_s) "[_ $]".
  Qed.

End refl.
