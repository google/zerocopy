(** This file has been adapted from the Stacked Borrows development, available at 
  https://gitlab.mpi-sws.org/FP/stacked-borrows
*)

From simuliris.simulation Require Import lifting.
From simuliris.stacked_borrows Require Import proofmode lang adequacy examples.lib.


(** Moving a write to a mutable reference down across unknown code. *)

(* Assuming x : &mut i32 *)
Definition ex3_down_unopt : expr :=
    let: "c" := InitCall in
    (* "x" is the local variable that stores the pointer value "i" *)
    let: "x" := new_place (&mut int) "i" in

    (* retag_place reborrows the pointer value stored in "x" (which is "i"),
      then updates "x" with the new pointer value. This relies on protectors,
      hence [FnEntry]. *)
    retag_place "x" (RefPtr Mutable) int FnEntry "c";;

    (* Write 42 to the cell pointed to by the pointer in "x" *)
    *{int} "x" <- #[42] ;;

    (* The unknown code is represented by a call to an unknown function "f" *)
    let: "v" := Call #[ScFnPtr "f"] #[] in

    (* Write 13 to the cell pointed to by the pointer in "x" *)
    *{int} "x" <- #[13] ;;

    (* Free the local variable *)
    Free "x" ;;

    (* Finally, return the value *)
    EndCall "c";;
    "v"
  .

Definition ex3_down_opt : expr :=
    let: "c" := InitCall in
    let: "x" := new_place (&mut int) "i" in
    retag_place "x" (RefPtr Mutable) int FnEntry "c" ;;
    let: "v" := Call #[ScFnPtr "f"] #[] in
    *{int} "x" <- #[13] ;;
    Free "x" ;;
    EndCall "c";;
    "v"
  .

Lemma sim_opt3_down `{sborGS Σ} :
  ⊢ log_rel ex3_down_opt ex3_down_unopt.
Proof.
  log_rel.
  iIntros "%r_t %r_s #Hrel !# %π _".
  sim_pures.
  sim_apply InitCall InitCall sim_init_call "". iIntros (c) "Hcall". iApply sim_expr_base. sim_pures.

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
  iIntros (t_i v_t v_s Hlen_t Hlen_s) "#Hvrel Hcall Htag_i Hi_t Hi_s _".
  iApply sim_expr_base.
  target_apply (Write _ _) (target_write_local with "Htag Ht") "Ht Htag"; [done | done | ].
  source_apply (Write _ _) (source_write_local with "Htag Hs") "Hs Htag"; [done | done | ].
  sim_pures.

  (* do the source write *)
  source_apply (Copy (Place _ _ _)) (source_copy_local with "Htag Hs") "Hs Htag"; first done.
  source_pures.
  source_apply (Write _ _) (source_write_protected with "Hcall Htag_i Hi_s") "Hi_s Hcall Htag_i"; [done.. | | ].
  { simpl. intros i0 Hi0. assert (i0 = O) as -> by lia. eexists. split; first apply lookup_insert_eq.  set_solver. }
  sim_pures.


  (* do the call *)
  sim_apply (Call _ _) (Call _ _) (sim_call _ (ValR []) (ValR [])) ""; first by iApply big_sepL2_nil.
  iIntros (r_t r_s) "?". sim_pures.

  (* do the target write *)
  target_apply (Copy (Place _ _ _)) (target_copy_local with "Htag Ht") "Ht Htag"; first done.
  target_pures.
  target_apply (Write _ _) (target_write_protected with "Hcall Htag_i Hi_t") "Hi_t Hcall Htag_i"; [done.. | | ].
  { simpl. intros i0 Hi0. assert (i0 = O) as -> by lia. eexists. split; first apply lookup_insert_eq.  set_solver. }
  sim_pures.

  (* do the source write *)
  source_apply (Copy (Place _ _ _)) (source_copy_local with "Htag Hs") "Hs Htag"; first done.
  source_pures.
  source_apply (Write _ _) (source_write_protected with "Hcall Htag_i Hi_s") "Hi_s Hcall Htag_i"; [done.. | | ].
  { simpl. intros i0 Hi0. assert (i0 = O) as -> by lia. eexists. split; first apply lookup_insert_eq.  set_solver. }
  sim_pures.

  (* cleanup: remove the protector ghost state, make the external locations public, free the local locations*)
  sim_apply (Free _) (Free _) (sim_free_local with "Htag Ht Hs") "Htag"; [done..|]. sim_pures.
  iApply (sim_protected_unprotectN with "Hcall Htag_i Hi_t Hi_s []"); [ | apply lookup_insert_eq | | ].
  { simpl. cbn in Hlen_t. intros i' Hi'. replace i' with O by lia. rewrite elem_of_union elem_of_singleton. eauto. }
  { iApply big_sepL2_singleton. done. }
  iIntros "Hcall Htag_i Hi_t Hi_s".
  iApply (sim_remove_empty_calls t_i with "Hcall").
  { rewrite lookup_insert_eq. done. }
  { simpl. set_solver. }
  iIntros "Hcall".
  sim_apply (EndCall _) (EndCall _) (sim_endcall_own with "[Hcall]") "".
  { replace (delete t_i _) with (∅ : gmap ptr_id (gset loc)); first done.
    apply map_eq. intros t'. rewrite delete_insert_eq delete_insert_id; done.
  }
  sim_pures.
  iApply sim_expr_base. iExists r_t, r_s. eauto.
Qed.


Section closed.
  (** Obtain a closed proof of [ctx_ref]. *)
  Lemma sim_opt3_down_ctx : ctx_ref ex3_down_opt ex3_down_unopt.
  Proof.
    set Σ := #[sborΣ].
    apply (log_rel_adequacy Σ)=>?.
    apply sim_opt3_down.
  Qed.
End closed.
