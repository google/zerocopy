From iris Require Import bi.bi.
From iris.proofmode Require Import proofmode.
From simuliris.simulation Require Import slsls lifting.
From simuliris.simulang Require Import lang notation tactics
  proofmode log_rel_structural wf behavior hoare.
From simuliris.simulang.na_inv Require Export inv.
From simuliris.simulang.na_inv Require Import readonly_refl adequacy.

Section data_race.
  Context `{naGS Σ}.

  (** ** Example from 3.2 *)

  Definition load_na_sc_unopt : expr :=
    "x" <- #42;;
    !ˢᶜ "y";;
    !"x".
  Definition load_na_sc_opt : expr :=
    "x" <- #42;;
    !ˢᶜ "y";;
    #42.

  (** For completeness: the triple shown in the paper.
    (really, we usually want to prove [load_na_sc_log] below).
  *)
  Lemma load_na_sc_sim π (x_t x_s y_s y_t : loc) :
    ⊢ {{{ x_t ↔h x_s ∗ y_t ↔h y_s ∗ na_locs π ∅ }}}
        subst "x" #x_t $ subst "y" #y_t $ load_na_sc_opt ⪯[π]
        subst "x" #x_s $ subst "y" #y_s $ load_na_sc_unopt
      {{{ lift_post (λ v_t v_s, ⌜v_t = v_s⌝ ∗ na_locs π ∅) }}}.
  Proof.
    iIntros "!> (#Hx & #Hy & Hcol)".
    rewrite /load_na_sc_opt /load_na_sc_unopt.
    simpl_subst.
    (* exploit *)
    iApply (sim_bij_exploit_store with "Hx Hcol"); [ | done | ].
    { intros. safe_reach_fill (Store _ _ _).
      eapply safe_reach_safe_implies; first apply _.
      intros (? & ? & ? & ?). simplify_eq.
      apply safe_reach_refl. apply post_in_ectx_intro. eauto.
    }

    iIntros (v_t v_s) "Hx_t Hx_s Hv Hcol".
    source_store. target_store.
    sim_pures.

    (* Case analysis: do x and y alias? *)
    destruct (decide (y_s = x_s)) as [ -> | Hneq].
    - iPoseProof (heapbij_loc_inj with "Hx Hy") as "<-".
      source_load. target_load. sim_pures.
      source_load.
      iApply (sim_bij_release NaExcl with "Hx Hcol Hx_t Hx_s []"); [ | done | ].
      { apply lookup_insert_eq. }
      rewrite delete_insert_id; last done. iIntros "Hcol".
      sim_val. by iFrame.
    - (* don't alias *)
      sim_bind (Load _ _) (Load _ _).
      iApply (sim_bij_load_sc with "Hy Hcol").
      { rewrite lookup_insert_ne; done. }
      iIntros (??) "_ Hcol". sim_val.
      sim_pures. source_load.

      iApply (sim_bij_release NaExcl with "Hx Hcol Hx_t Hx_s []"); [ | done | ].
      { apply lookup_insert_eq. }
      rewrite delete_insert_id; last done. iIntros "Hcol".
      sim_val. by iFrame.
  Qed.

  (** The statement we really want (as described in Section 4): a [log_rel]. *)
  Lemma load_na_sc_log :
    ⊢ log_rel load_na_sc_opt load_na_sc_unopt.
  Proof.
    (* closes open variables with related values *)
    log_rel. iIntros (x_t' x_s') "#Hx'". iIntros (y_t' y_s') "#Hy' !>".
    iIntros (π) "Hcol".
    sim_bind (Store _ _ _) (Store _ _ _).
    iApply sim_safe_implies. iIntros "(%x_s & ->)".
    iPoseProof (gen_val_rel_loc_source with "Hx'") as "(%x_t & -> & Hx)".

    iApply (sim_bij_exploit_store with "Hx Hcol"); [ | done | ].
    { intros. safe_reach_fill (Store _ _ _).
      eapply safe_reach_safe_implies; first apply _.
      intros (? & ? & ? & ?). simplify_eq.
      apply safe_reach_refl. apply post_in_ectx_intro. eauto.
    }

    iIntros (v_t v_s) "Hx_t Hx_s Hv Hcol".
    source_store. target_store. sim_val.
    sim_pures.

    sim_bind (Load _ _) (Load _ _).
    iApply sim_safe_implies. iIntros "(%y_s & ->)".
    iPoseProof (gen_val_rel_loc_source with "Hy'") as "(%y_t & -> & Hy)".

    (* Case analysis: do x and y alias? *)
    destruct (decide (y_s = x_s)) as [ -> | Hneq].
    - iPoseProof (heapbij_loc_inj with "Hx Hy") as "<-".
      source_load. target_load. sim_val. sim_pures.
      source_load.
      iApply (sim_bij_release NaExcl with "Hx Hcol Hx_t Hx_s []"); [ | done | ].
      { apply lookup_insert_eq. }
      rewrite delete_insert_id; last done. iIntros "Hcol".
      sim_val. by iFrame.
    - (* don't alias *)
      sim_bind (Load _ _) (Load _ _).
      iApply (sim_bij_load_sc with "Hy Hcol").
      { rewrite lookup_insert_ne; done. }
      iIntros (??) "_ Hcol". sim_val.
      sim_pures. source_load.

      iApply (sim_bij_release NaExcl with "Hx Hcol Hx_t Hx_s []"); [ | done | ].
      { apply lookup_insert_eq. }
      rewrite delete_insert_id; last done. iIntros "Hcol".
      sim_val. by iFrame.
    Qed.


  (** ** Example from 3.2 (arbitrary readonly expressions *)

  Definition load_na_unopt e : expr :=
    "x" <- #42;;
    e;;
    !"x".
  Definition load_na_opt e : expr :=
    "x" <- #42;;
    e;;
    #42.

  (** We currently do not have good automation when we don't know a upper bound
    on the set of variables used by [e], therefore there's a bit of manual work
    regarding substitution involved here.
   *)
  Import gen_log_rel.
  Lemma load_na_log e :
    gen_expr_wf readonly_wf e →
    ⊢ log_rel (load_na_opt e) (load_na_unopt e).
  Proof.
    iIntros (Hwf). rewrite /log_rel. iModIntro.
    iIntros (π map) "#Hsubst Hcol".
    simpl.

    iPoseProof (subst_map_rel_lookup _ "x" with "Hsubst") as "(%vx_t & %vx_s & %Heq & Hx')".
    { set_solver. }
    rewrite !lookup_fmap. rewrite !Heq. simpl.


    (* closes open variables with related values *)
    sim_bind (Store _ _ _) (Store _ _ _).
    iApply sim_safe_implies. iIntros "(%x_s & ->)".
    iPoseProof (gen_val_rel_loc_source with "Hx'") as "(%x_t & -> & Hx)".

    iApply (sim_bij_exploit_store with "Hx Hcol"); [ | done | ].
    { intros. safe_reach_fill (Store _ _ _).
      eapply safe_reach_safe_implies; first apply _.
      intros (? & ? & ? & ?). simplify_eq.
      apply safe_reach_refl. apply post_in_ectx_intro. eauto.
    }

    iIntros (v_t v_s) "Hx_t Hx_s Hv Hcol".
    source_store. target_store. sim_val.
    sim_pures.

    (* use read-only reflexivity theorem *)
    sim_bind (subst_map _ _) (subst_map _ _).
    iPoseProof (subst_map_rel_weaken _ _ (free_vars e) with "Hsubst") as "Hsubst'"; first set_solver.

    iPoseProof (subst_map_rel_dom with "Hsubst'") as "%Hdom".
    iApply (sim_refl' with "[] [Hcol Hx_t Hx_s]");
      [ by rewrite !dom_fmap_L | |
        apply (readonly_log_rel_structural [(x_t, x_s, #42 , #42 , 1%Qp)]) | done | | | ].
    { by rewrite dom_fmap_L. }
    { rewrite map_fmap_zip. rewrite map_zip_diag. rewrite -map_fmap_compose.
      erewrite (map_fmap_ext _ id). { rewrite map_fmap_id. done. }
      move => i [x y] Hl //.
    }
    { rewrite /readonly_thread_own. iFrame.
      unfold pointsto_list, na_locs_in_pointsto_list.
      iSplit; [|iSplit; [ iSplit; done | done]].
      iPureIntro. intros ???. rewrite lookup_insert_Some.
      rewrite lookup_empty. intros [[<- [= <- <-]] | [_ [=]]].
      exists 0. eauto.
    }

    iIntros (??).
    rewrite /readonly_thread_own.
    unfold pointsto_list. simpl.
    iIntros "(_ & Hcol & (Hx_t & Hx_s & _ & _) & _) _".
    iApply lift_post_val.

    sim_pures. source_load.

    iApply (sim_bij_release NaExcl with "Hx Hcol Hx_t Hx_s []"); [ | done | ].
    { apply lookup_insert_eq. }
    rewrite delete_insert_id; last done. iIntros "Hcol".
    sim_val. by iFrame.
  Qed.


  (** ** Optimization from the intro and 3.3 *)
  (** (In file [theories/simulang/na_inv/examples/data_races.v], there is a version of this
      where the memory is actually freed in the end)
   *)

  Definition hoist_load_both_unopt : expr :=
     let: "i" := ref #0  in
     let: "r" := ref (!"y") in
     while: !"i" ≠ ! "x" do
       "i" <- !"i" + #1;;
       "r" <- !"r" + !"y"
     od;;
     !"r".

  Definition hoist_load_both_opt : expr :=
     let: "n" := !"x" in
     let: "m" := !"y" in
     let: "i" := ref #0  in
     let: "r" := ref "m" in
     while: !"i" ≠ "n" do
       "i" <- !"i" + #1;;
       "r" <- !"r" + "m"
     od;;
     !"r".

  Lemma int_is_unboxed (z : Z) : val_is_unboxed #z.
  Proof. done. Qed.

  (** We directly prove a [log_rel], as that is the statement we really want. *)
  Lemma hoist_load_both_log:
    ⊢ log_rel hoist_load_both_opt hoist_load_both_unopt.
  Proof.
    log_rel.
    iIntros "%x_t1 %x_s1 #Hrel_x %y_t1 %y_s1 #Hrel_y !# %π Hc".

    source_alloc li_s as "Hli_s" "_". sim_pures.
    source_bind (Load _ _). iApply source_red_safe_implies. iIntros ([lx_s ?]); simplify_eq.
    iDestruct (gen_val_rel_loc_source with "Hrel_x") as (lx_t ->) "Hbij_x".
    iApply source_red_base. iModIntro. to_sim.
    iApply (sim_bij_exploit_load with "Hbij_x Hc"); [|done|]. {
      intros.
      safe_reach_fill (! _)%E => /=.
      apply: safe_reach_safe_implies => ?.
      apply: safe_reach_refl. apply: post_in_ectx_intro. naive_solver.
    }
    iIntros (qx vx_t vx_s) "Hx_t Hx_s #Hvx Hc".
    source_load.
    source_alloc lr_s as "Hlr_s" "_". sim_pures.

    destruct (if y_s1 is #(LitLoc _) then true else false) eqn:Heq. 2: {
      source_while.
      source_bind (! _)%E. iApply source_red_safe_implies.
      iIntros ([l_s ?]); simplify_eq.
    }
    destruct y_s1 as [[| | | |ly_s |]| | |] => //.
    iDestruct (gen_val_rel_loc_source with "Hrel_y") as (ly_t ->) "Hbij_y".

    (* hint for the [sim_pure] automation to reduce the comparison *)
    specialize int_is_unboxed as Hunb.

    (* case analysis: do [x] and [y] alias? *)
    destruct (decide (ly_s = lx_s)) as [-> | Hneq].
    - (* they do alias, so we do not need to exploit a second time. *)
      rename lx_s into l_s.
      iPoseProof (heapbij_loc_inj with "Hbij_x Hbij_y") as "->".
      rename ly_t into l_t.
      (* we now have ownership of all relevant locations and can continue *)

      target_load. target_load. target_alloc li_t as "Hli_t" "_".
      target_alloc lr_t as "Hlr_t" "_".
      sim_pures.

      set inv := (
        ∃ (z_i : Z) (vr_t vr_s : val),
        l_t ↦t{#qx} vx_t ∗
        l_s ↦s{#qx} vx_s ∗
        li_s ↦s #z_i ∗
        li_t ↦t #z_i ∗
        lr_t ↦t vr_t ∗
        lr_s ↦s vr_s ∗
        val_rel vr_t vr_s ∗
        na_locs π (<[l_s:=(l_t, NaRead qx)]> ∅))%I.

      sim_bind (While _ _) (While _ _).
      iApply (sim_while_while inv with "[Hli_s Hx_t Hx_s Hc Hlr_s Hli_t Hlr_t] []").
      { iExists 0, vx_t, vx_s. iFrame. done. }
      iModIntro. iIntros "(%z_i & %vr_t & %vr_s & Hx_t & Hx_s & Hli_s & Hli_t & Hlr_t & Hlr_s & #Hvr & Hc)".
      source_load. source_load. target_load. to_sim.
      sim_pures.

      destruct (bool_decide (#z_i = vx_s)) eqn:Heq_vx_s.
      + (* compare equal in the source; leave the loop *)
        apply bool_decide_eq_true_1 in Heq_vx_s. subst vx_s.
        val_discr_source "Hvx".
        rewrite bool_decide_eq_true_2; last done.
        sim_pures. iApply sim_expr_base. iLeft. iApply lift_post_val.

        sim_pures. source_load. target_load. sim_pures.
        (* cleanup *)
        iApply (sim_bij_release (NaRead qx) with "Hbij_x Hc Hx_t Hx_s [//]").
        { apply lookup_insert_eq. }
        rewrite delete_insert_id; last done. iIntros "Hc".
        sim_val. eauto.
      + (* compare unequal and take another trip around the loop *)
        apply bool_decide_eq_false_1 in Heq_vx_s.
        destruct (bool_decide (#z_i = vx_t)) eqn:Heq_vx_t.
        { (* contradiction *)
          apply bool_decide_eq_true_1 in Heq_vx_t. subst vx_t.
          val_discr_target "Hvx". done.
        }
        sim_pures.
        source_load. source_store.
        source_load. source_load.
        (* gain knowledge that both are ints *)
        source_bind (BinOp _ _ _). iApply source_red_safe_implies.
        iIntros "[(%z_r & ->) (%z_s & ->)]".
        val_discr_source "Hvx". val_discr_source "Hvr". source_pures.
        source_store.
        target_load. target_store.
        target_load. target_store.
        sim_pures. iApply sim_expr_base. iRight.
        iSplitR; first done. iSplitR; first done.
        iExists (z_i + 1)%Z, #(z_r + z_s)%Z, #(z_r + z_s)%Z.
        iFrame. done.
    - (* the locations do not alias, so we also need to exploit "y" *)
      (* the proof of this case is very similar to the one above, except that we carry around
        the additional locations in the invariant and have to release both in the end. *)
      iApply (sim_bij_exploit_load with "Hbij_y Hc"); [| |]. {
        intros.
        safe_reach_fill (While _ _)%E => /=.
        apply: safe_reach_pure; [eapply pure_while | done | ].
        safe_reach_fill (Load _ _)%E.
        apply: safe_reach_safe_implies => ?.
        apply: safe_reach_refl. apply: post_in_ectx_intro. naive_solver.
      }
      { rewrite lookup_insert_ne; last done. apply lookup_empty. }
      iIntros (qy vy_t vy_s) "Hy_t Hy_s #Hvy Hc".

      target_load. target_load.
      target_alloc li_t as "Hli_t" "_".
      target_alloc lr_t as "Hlr_t" "_".
      sim_pures.

      set inv := (
        ∃ (z_i : Z) (vr_t vr_s : val),
        lx_t ↦t{#qx} vx_t ∗
        lx_s ↦s{#qx} vx_s ∗
        ly_t ↦t{#qy} vy_t ∗
        ly_s ↦s{#qy} vy_s ∗
        li_s ↦s #z_i ∗
        li_t ↦t #z_i ∗
        lr_t ↦t vr_t ∗
        lr_s ↦s vr_s ∗
        val_rel vr_t vr_s ∗
        na_locs π (<[ly_s:=(ly_t, NaRead qy)]> $ <[lx_s:=(lx_t, NaRead qx)]> ∅))%I.

      sim_bind (While _ _) (While _ _).
      iApply (sim_while_while inv with "[Hy_t Hy_s Hli_s Hx_t Hx_s Hc Hlr_s Hli_t Hlr_t] []").
      { iExists 0, vx_t, vx_s. iFrame. done. }
      iModIntro. iIntros "(%z_i & %vr_t & %vr_s & Hx_t & Hx_s & Hy_t & Hy_s & Hli_s & Hli_t & Hlr_t & Hlr_s & #Hvr & Hc)".
      source_load. source_load. target_load. sim_pures.

      destruct (bool_decide (#z_i = vy_s)) eqn:Heq_vy_s.
      + (* compare equal in the source; leave the loop *)
        apply bool_decide_eq_true_1 in Heq_vy_s. subst vy_s.
        val_discr_source "Hvy".
        rewrite bool_decide_eq_true_2; last done.
        sim_pures. iApply sim_expr_base. iLeft. iApply lift_post_val.

        sim_pures. source_load. target_load. sim_pures.
        (* cleanup *)
        iApply (sim_bij_release (NaRead qy) with "Hbij_y Hc Hy_t Hy_s [//]").
        { apply lookup_insert_eq. }
        rewrite delete_insert_id; last by rewrite lookup_insert_ne.
        iIntros "Hc".
        iApply (sim_bij_release (NaRead qx) with "Hbij_x Hc Hx_t Hx_s [//]").
        { apply lookup_insert_eq. }
        rewrite delete_insert_id; last done. iIntros "Hc".
        sim_val. eauto.
      + (* compare unequal and take another trip around the loop *)
        apply bool_decide_eq_false_1 in Heq_vy_s.
        destruct (bool_decide (#z_i = vy_t)) eqn:Heq_vy_t.
        { (* contradiction *)
          apply bool_decide_eq_true_1 in Heq_vy_t. subst vy_t.
          val_discr_target "Hvy". done.
        }
        sim_pures.
        source_load. source_store.
        source_load. source_load.
        (* gain knowledge that both are ints *)
        source_bind (BinOp _ _ _). iApply source_red_safe_implies.
        iIntros "[(%z_r & ->) (%z_s & ->)]".
        val_discr_source "Hvx". val_discr_source "Hvr". source_pures.
        source_store.
        target_load. target_store.
        target_load. target_store.
        sim_pures. iApply sim_expr_base. iRight.
        iSplitR; first done. iSplitR; first done.
        iExists (z_i + 1)%Z, #(z_r + z_s)%Z, #(z_r + z_s)%Z.
        iFrame. done.
    Qed.

End data_race.

(* Deriving contextual refinements *)
Section closed.
  Lemma load_na_sc_ctx :
    ctx_ref load_na_sc_opt load_na_sc_unopt.
  Proof.
    intros ??.
    set Σ := #[naΣ].
    apply (log_rel_adequacy Σ)=>?.
    by apply load_na_sc_log.
  Qed.

  Lemma load_na_ctx e :
    gen_expr_wf readonly_wf e →
    ctx_ref (load_na_opt e) (load_na_unopt e).
  Proof.
    intros ??.
    set Σ := #[naΣ].
    apply (log_rel_adequacy Σ)=>?.
    by apply load_na_log.
  Qed.

  Lemma hoist_load_both_ctx :
    ctx_ref hoist_load_both_opt hoist_load_both_unopt.
  Proof.
    intros ??.
    set Σ := #[naΣ].
    apply (log_rel_adequacy Σ)=>?.
    by apply hoist_load_both_log.
  Qed.
End closed.
