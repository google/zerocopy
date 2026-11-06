(** This file has been adapted from the Stacked Borrows development, available at 
  https://gitlab.mpi-sws.org/FP/stacked-borrows
*)

From simuliris.simulation Require Import lifting.
From simuliris.stacked_borrows Require Import proofmode lang adequacy examples.lib.



(** Moving read of shared ref up across code that *may* use that ref. *)

(** This is a variant using protectors.
  See below for the original optimization without protectors and with deferred UB.
 *)

(* Assuming x : & i32 *)
Definition ex2_unopt : expr :=
    let: "c" := InitCall in

    (* "x" is the local variable that stores the pointer value "i" *)
    let: "x" := new_place (& int) "i" in

    (* retag_place reborrows the pointer value stored in "x" (which is "i"),
      then updates "x" with the new pointer value.
      Using a protector here.
    *)
    retag_place "x" (RefPtr Immutable) int FnEntry "c";;

    (* The unknown code is represented by a call to an unknown function "f",
      which does take the pointer value from "x" as an argument. *)
    Call #[ScFnPtr "f"] (Copy "x") ;;

    (* Read the value "v" from the cell pointed to by the pointer in "x" *)
    let: "v" := Copy *{int} "x" in

    (* Free the local variable *)
    Free "x" ;;

    (* Finally, return the read value *)
    EndCall "c";;
    "v"
  .

Definition ex2_opt : expr :=
    let: "c" := InitCall in
    let: "x" := new_place (& int) "i" in
    retag_place "x" (RefPtr Immutable) int FnEntry "c";;
    let: "v" := Copy *{int} "x" in
    Call #[ScFnPtr "f"] (Copy "x") ;;
    Free "x" ;;
    EndCall "c";;
    "v"
  .

Lemma sim_opt2 `{sborGS Σ} :
  ⊢ log_rel ex2_opt ex2_unopt.
Proof.
  log_rel.
  iIntros "%r_t %r_s #Hrel !# %π _".
  sim_pures.
  sim_apply InitCall InitCall (sim_init_call) "". iIntros (c) "Hcall". iApply sim_expr_base. sim_pures.

  (* new place *)
  simpl. source_bind (new_place _ _).
  iApply source_red_safe_reach.
  { intros. rewrite subst_result; eapply new_place_safe_reach. }
  simpl. iIntros "(%v_s & -> & %Hsize)".
  iPoseProof (rrel_value_source with "Hrel") as (v_t) "(-> & #Hv)".
  iPoseProof (value_rel_length with "Hv") as "%Hlen".
  iApply source_red_base. iModIntro. to_sim.
  sim_apply (new_place _ _) (new_place _ _) sim_new_place_local "%t %l % % Htag Ht Hs"; first done.
  sim_pures.

  target_apply (Copy _) (target_copy_local with "Htag Ht") "Ht Htag"; first lia.
  source_apply (Copy _) (source_copy_local with "Htag Hs") "Hs Htag"; first lia.

  (* do the retag *)
  sim_bind (Retag _ _ _ _ _) (Retag _ _ _ _ _).
  iApply sim_safe_implies.
  iIntros ((_ & ot & i & -> & _)).
  iPoseProof (value_rel_singleton_source with "Hv") as (sc_t) "[-> Hscrel]".
  iPoseProof (sc_rel_ptr_source with "Hscrel") as "[-> Htagged]".
  iApply (sim_retag_fnentry with "Hscrel Hcall"); [cbn; lia| done | ].
  iIntros (t_i v_t v_s Hlen_t Hlen_s) "#Hvrel Hcall Htag_i Hi_t Hi_s #Hsc_i".
  iApply sim_expr_base.
  target_apply (Write _ _) (target_write_local with "Htag Ht") "Ht Htag"; [done | done | ].
  source_apply (Write _ _) (source_write_local with "Htag Hs") "Hs Htag"; [done | done | ].
  sim_pures.

  (* read in the target *)
  target_apply (Copy (Place _ _ _)) (target_copy_local with "Htag Ht") "Ht Htag"; first done.
  target_pures. target_apply (Copy _) (target_copy_protected with "Hcall Htag_i Hi_t") "Hi_t Hcall Htag_i"; [done | | ].
  { simpl. intros i0 Hi0. assert (i0 = O) as -> by lia. eexists. split; first apply lookup_insert_eq. set_solver. }

  sim_pures. target_apply (Copy _) (target_copy_local with "Htag Ht") "Ht Htag"; first done.
  source_apply (Copy _) (source_copy_local with "Htag Hs") "Hs Htag"; first done. sim_pures.
  sim_apply (Call _ _) (Call _ _) (sim_call _ (ValR [ScPtr i _]) (ValR [ScPtr i _])) "".
  { iApply big_sepL2_singleton. iApply "Hsc_i". }
  iIntros (r_t r_s) "_". sim_pures.

  (* read in the source *)
  source_apply (Copy (Place _ _ _)) (source_copy_local with "Htag Hs") "Hs Htag"; first done.
  source_pures. source_bind (Copy _). iApply (source_copy_any with "Htag_i Hi_s"); first done.
  iIntros (v_s' Hv_s') "Hi_s Htag_i". source_finish. sim_pures.

  sim_apply (Free _) (Free _) (sim_free_local with "Htag Ht Hs") "Htag"; [done..|]. sim_pures.
  iApply (sim_protected_unprotectN with "Hcall Htag_i Hi_t Hi_s Hvrel"); [ | apply lookup_insert_eq | ].
  { simpl. cbn in Hlen_t. intros i' Hi'. replace i' with O by lia. rewrite elem_of_union elem_of_singleton. eauto. }
  iIntros "Hcall Htag_i Hi_t Hi_s".
  iApply (sim_remove_empty_calls t_i with "Hcall").
  { rewrite lookup_insert_eq. done. }
  { rewrite Hlen_t. set_solver. }
  iIntros "Hcall".
  sim_apply (EndCall _) (EndCall _) (sim_endcall_own with "[Hcall]") "".
  { replace (delete t_i _) with (∅ : gmap ptr_id (gset loc)); first done.
    apply map_eq. intros t'. rewrite delete_insert_eq delete_insert_id; done.
  }
  sim_pures.
  sim_val. iModIntro. iSplit; first done.
  destruct Hv_s' as [-> | ->]; first done.
  iApply big_sepL2_forall. iSplit. { rewrite length_replicate. iPureIntro. lia. }
  iIntros (k sc_t sc_s). rewrite lookup_replicate. iIntros "Hsc (-> & _)".
  destruct sc_t; done.
Qed.


(* Assuming x : & i32 *)
Definition ex2_unopt' : expr :=
    (* "x" is the local variable that stores the pointer value "i" *)
    let: "x" := new_place (& int) "i" in

    (* retag_place reborrows the pointer value stored in "x" (which is "i"),
      then updates "x" with the new pointer value. A [Default] retag is
      sufficient for this, we don't need the protector. *)
    retag_place "x" (RefPtr Immutable) int Default #[ScCallId 0];;

    (* The unknown code is represented by a call to an unknown function "f",
      which does take the pointer value from "x" as an argument. *)
    Call #[ScFnPtr "f"] (Copy "x") ;;

    (* Read the value "v" from the cell pointed to by the pointer in "x" *)
    let: "v" := Copy *{int} "x" in

    (* Free the local variable *)
    Free "x" ;;

    (* Finally, return the read value *)
    "v"
  .

Definition ex2_opt' : expr :=
    let: "x" := new_place (& int) "i" in
    retag_place "x" (RefPtr Immutable) int Default #[ScCallId 0];;
    let: "v" := Copy *{int} "x" in
    Call #[ScFnPtr "f"] (Copy "x") ;;
    Free "x" ;;
    "v"
  .


Lemma sim_opt2' `{sborGS Σ} :
  ⊢ log_rel ex2_opt' ex2_unopt'.
Proof.
  log_rel.
  iIntros "%r_t %r_s #Hrel !# %π _".
  sim_pures.

  (* new place *)
  simpl. source_bind (new_place _ _).
  iApply source_red_safe_reach.
  { intros. eapply new_place_safe_reach. }
  simpl. iIntros "(%v_s & -> & %Hsize)".
  iPoseProof (rrel_value_source with "Hrel") as (v_t) "(-> & #Hv)".
  iPoseProof (value_rel_length with "Hv") as "%Hlen".
  iApply source_red_base. iModIntro. to_sim.
  sim_apply (new_place _ _) (new_place _ _) sim_new_place_local "%t %l % % Htag Ht Hs"; first done.
  sim_pures.

  target_apply (Copy _) (target_copy_local with "Htag Ht") "Ht Htag"; first lia.
  source_apply (Copy _) (source_copy_local with "Htag Hs") "Hs Htag"; first lia.

  (* do the retag *)
  sim_bind (Retag _ _ _ _ _) (Retag _ _ _ _ _).
  iApply sim_safe_implies.
  iIntros ((_ & ot & i & -> & _)).
  iPoseProof (value_rel_singleton_source with "Hv") as (sc_t) "[-> Hscrel]".
  iPoseProof (sc_rel_ptr_source with "Hscrel") as "[-> Htagged]".
  iApply (sim_retag_default with "Hscrel"); [cbn; lia| done | ].
  iIntros (t_i v_t v_s Hlen_t Hlen_s) "#Hvrel Htag_i Hi_t Hi_s #Hsc_i".
  iApply sim_expr_base.
  target_apply (Write _ _) (target_write_local with "Htag Ht") "Ht Htag"; [done | done | ].
  source_apply (Write _ _) (source_write_local with "Htag Hs") "Hs Htag"; [done | done | ].
  sim_pures.

  (* deferred read in the target *)
  target_apply (Copy (Place _ _ _)) (target_copy_local with "Htag Ht") "Ht Htag"; first done.
  target_pures. target_bind (Copy _).
  iApply (target_copy_deferred with "Htag_i Hi_t"); first done. iIntros (v_t') "Hdeferred Hi_t Htag_i". target_finish.
  sim_pures.

  sim_pures. target_apply (Copy _) (target_copy_local with "Htag Ht") "Ht Htag"; first done.
  source_apply (Copy _) (source_copy_local with "Htag Hs") "Hs Htag"; first done. sim_pures.
  sim_apply (Call _ _) (Call _ _) (sim_call _ (ValR [ScPtr i _]) (ValR [ScPtr i _])) "".
  { iApply big_sepL2_singleton. iApply "Hsc_i". }
  iIntros (r_t r_s) "_". sim_pures.

  (* resolve the deferred read in the source *)
  source_apply (Copy (Place _ _ _)) (source_copy_local with "Htag Hs") "Hs Htag"; first done.
  source_pures. source_bind (Copy _).
  iApply (source_copy_resolve_deferred with "Htag_i Hi_s Hdeferred"); [done | done | ].
  iIntros (v_s') "Hv' Hi_s Htag_i". source_finish.
  sim_pures.

  sim_apply (Free _) (Free _) (sim_free_local with "Htag Ht Hs") "Htag"; [done..|]. sim_pures.

  sim_val. eauto.
Qed.

Section closed.
  (** Obtain a closed proof of [ctx_ref]. *)
  Lemma sim_opt2'_ctx : ctx_ref ex2_opt' ex2_unopt'.
  Proof.
    set Σ := #[sborΣ].
    apply (log_rel_adequacy Σ)=>?.
    apply sim_opt2'.
  Qed.
End closed.
