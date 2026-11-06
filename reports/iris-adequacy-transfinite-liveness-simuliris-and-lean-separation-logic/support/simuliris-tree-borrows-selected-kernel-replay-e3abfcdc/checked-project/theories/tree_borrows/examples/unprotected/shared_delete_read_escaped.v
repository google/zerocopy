From simuliris.simulation Require Import lifting.
From simuliris.tree_borrows Require Import proofmode lang adequacy examples.lib.


(** Re-using an earlier read across code that *may* use that ref. *)

(* Assuming x : & i32 *)
Definition unprot_shared_delete_read_escaped_unopt : expr :=
    (* "x" is the local variable that stores the pointer value "i" *)
    let: "x" := new_place sizeof_scalar "i" in

    (* retag_place reborrows the pointer value stored in "x" (which is "i"),
      then updates "x" with the new pointer value. A [Default] retag is
      sufficient for this, we don't need the protector. *)
    retag_place "x" ShrRef TyFrz sizeof_scalar Default #[ScCallId 0];;
    (* Note that val is not actually used in the source, but it will be used in the target. *)
    let: "val" := Copy *{sizeof_scalar} "x" in
    (* The unknown code is represented by a call to an unknown function "f",
       which does take the pointer value from "x" as an argument.
       To simulate Rust closures, it also takes an arbitrary closure env. *)
    Call #[ScFnPtr "f"] (Conc "f_closure_env" (Copy "x")) ;;

    (* Read the value "v" from the cell pointed to by the pointer in "x" *)
    let: "v" := Copy *{sizeof_scalar} "x" in

    (* Free the local variable *)
    Free "x" ;;

    (* Finally, return the read value *)
    "v"
  .

Definition unprot_shared_delete_read_escaped_opt : expr :=
    let: "x" := new_place sizeof_scalar "i" in
    retag_place "x" ShrRef TyFrz sizeof_scalar Default #[ScCallId 0];;
    let: "val" := Copy *{sizeof_scalar} "x" in
    Call #[ScFnPtr "f"] (Conc "f_closure_env" (Copy "x")) ;;
    let: "v" := "val" in
    Free "x" ;;
    "v"
  .


Lemma unprot_shared_delete_read_escaped `{sborGS Σ} :
  ⊢ log_rel unprot_shared_delete_read_escaped_opt unprot_shared_delete_read_escaped_unopt.
Proof.
  log_rel.
  iIntros "%closure_env_t %closure_env_s #Hclosure_env_rel %r_t %r_s #Hrel !# %π _".
  sim_pures.
  rewrite !subst_result.

  (* new place *)
  simpl. source_bind (new_place _ _).
  iApply source_red_safe_reach.
  { intros. eapply new_place_safe_reach. }
  simpl. iIntros "(%v_s & -> & %Hsize)". destruct v_s as [|v_s [|?]]; try done.
  iPoseProof (rrel_value_source with "Hrel") as (v_t) "(-> & #Hv)".
  iPoseProof (value_rel_length with "Hv") as "%Hlen". destruct v_t as [|v_t [|?]]; try done.
  iApply source_red_base. iModIntro. to_sim.
  sim_apply (new_place _ _) (new_place _ _) sim_new_place_local "%t %l % % Htag Ht Hs"; first done.
  sim_pures.

  target_apply (Copy _) (target_copy_local with "Htag Ht") "Ht Htag". 2: done. 1: rewrite read_range_heaplet_to_list // Z.sub_diag /= //.
  source_apply (Copy _) (source_copy_local with "Htag Hs") "Hs Htag". 2: done. 1: rewrite read_range_heaplet_to_list // Z.sub_diag /= //.

  (* do the retag *)
  sim_bind (Retag _ _ _ _ _ _) (Retag _ _ _ _ _ _).
  iApply sim_safe_implies.
  iIntros ((_ & ot & i & [= ->] & _)).
  iPoseProof (value_rel_singleton_source with "Hv") as (sc_t [= ->]) "Hscrel".
  iPoseProof (sc_rel_ptr_source with "Hscrel") as ([= ->]) "Htagged".
  iApply (sim_retag_default with "Hscrel"). 1: by cbv.
  iIntros (t_i v_t v_s Hlen_t Hlen_s) "#Hvrel Htag_i Hi_t Hi_s".
  destruct v_t as [|v_t []]; try done.
  destruct v_s as [|v_s []]; try done.
  iApply sim_expr_base.
  target_apply (Write _ _) (target_write_local with "Htag Ht") "Ht Htag".
  2-3: done. 1: rewrite /write_range bool_decide_true. 2: simpl; lia. 1: rewrite Z.sub_diag /= //.
  source_apply (Write _ _) (source_write_local with "Htag Hs") "Hs Htag".
  2: done. 1: rewrite /write_range bool_decide_true. 2: simpl; lia. 1: rewrite Z.sub_diag /= //.
  sim_pures.

  (* do the load on both sides *)
  target_apply (Copy (Place _ _ _)) (target_copy_local with "Htag Ht") "Ht Htag". 2: done.
  1: rewrite read_range_heaplet_to_list // Z.sub_diag /= //.
  target_pures. target_finish.
  source_apply (Copy (Place _ _ _)) (source_copy_local with "Htag Hs") "Hs Htag". 2: done.
  1: rewrite read_range_heaplet_to_list // Z.sub_diag /= //.
  source_pures. source_finish.
  sim_bind (Copy _) (Copy _). sim_pures.
  iApply (sim_copy with "Htag_i Hi_s Hi_t"). 1,4: done.
  1-2: rewrite read_range_heaplet_to_list // Z.sub_diag /= //.
  iIntros (v_res_s v_res_t) "Hi_s Hi_t #Htag_i Hv_res".
  sim_pures.
  iApply sim_expr_base.

  (* do the call *)
  sim_pures. target_apply (Copy _) (target_copy_local with "Htag Ht") "Ht Htag". 2: done.
  1: rewrite read_range_heaplet_to_list // Z.sub_diag /= //.
  source_apply (Copy _) (source_copy_local with "Htag Hs") "Hs Htag". 2: done.
  1: rewrite read_range_heaplet_to_list // Z.sub_diag /= //. sim_pures.
  rewrite !subst_result.
  source_bind (Conc _ _).
  iApply source_red_safe_implies. 1: eapply irred_conc with (r2 := ValR _).
  iIntros ((closure_env_s_v & v2 & -> & [= <-])).
  destruct closure_env_t as [closure_env_t_v|]; last done.
  source_pures. to_sim. sim_pures.
  sim_apply (Call _ _) (Call _ _) (sim_call _ (ValR _) (ValR _)) "".
  { iApply big_sepL2_app; first iAssumption. iApply big_sepL2_singleton. iFrame "Htag_i". done. }
  iIntros (r_t r_s) "_". sim_pures.

  (* source load (not existing in the target) *)
  source_apply (Copy (Place _ _ _)) (source_copy_local with "Htag Hs") "Hs Htag". 2: done.
  1: rewrite read_range_heaplet_to_list // Z.sub_diag /= //.
  source_pures. source_bind (Copy _).

  iPoseProof (sim_into_read_for_simulation with "Hvrel Hv_res") as "Hreadsim".

  iApply (source_copy_in_simulation with "Hreadsim Htag_i Hi_s"). 1: done.
  2: simpl; lia. 1: rewrite read_range_heaplet_to_list // Z.sub_diag /= //.
  iIntros (v_res) "Hi_s _ Hinsim". source_pures. source_finish.
  sim_pures.
  (* cleanup: free the local locations*)
  sim_apply (Free _) (Free _) (sim_free_local with "Htag Ht Hs") "Htag"; [done..|]. sim_pures.
  sim_pures.
  sim_val. iModIntro. iSplit; first done. iApply "Hinsim".
Qed.


Section closed.
  (** Obtain a closed proof of [ctx_ref]. *)
  Lemma unprot_shared_delete_read_escaped_ctx : ctx_ref unprot_shared_delete_read_escaped_opt unprot_shared_delete_read_escaped_unopt.
  Proof.
    set Σ := #[sborΣ].
    apply (log_rel_adequacy Σ)=>?.
    apply unprot_shared_delete_read_escaped.
  Qed.
End closed.

(*
Check unprot_shared_delete_read_escaped_ctx.
Print Assumptions unprot_shared_delete_read_escaped_ctx.
*)
(* 
unprot_shared_delete_read_escaped_ctx
     : ctx_ref unprot_shared_delete_read_escaped_opt unprot_shared_delete_read_escaped_unopt
Axioms:
IndefiniteDescription.constructive_indefinite_description : ∀ (A : Type) (P : A → Prop), (∃ x : A, P x) → {x : A | P x}
Classical_Prop.classic : ∀ P : Prop, P ∨ ¬ P
*)
