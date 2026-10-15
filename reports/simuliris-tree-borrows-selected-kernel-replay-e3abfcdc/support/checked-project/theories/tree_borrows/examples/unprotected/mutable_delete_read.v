From simuliris.simulation Require Import lifting.
From simuliris.tree_borrows Require Import proofmode lang adequacy examples.lib.


(** Deleting read of mutable reference, by instead using an earlier value. *)

(* Assuming x : &mut i32 *)
Definition unprot_mutable_delete_read_unopt : expr :=
    (* get related values i*)
    (* "x" is the local variable that stores the pointer value "i" *)
    let: "x" := new_place sizeof_scalar "i" in

    (* retag_place reborrows the pointer value stored in "x" (which is "i"),
      then updates "x" with the new pointer value.
      Since we're not doing a FnEntry retag, the Call Id can be anything, here: 0
    *)
    retag_place "x" MutRef TyFrz sizeof_scalar Default #[ScCallId 0];;

    (* The unknown code is represented by a call to an unknown function "f" or
      "g". *)
    Call #[ScFnPtr "f"] #[] ;;

    (* Write 42 to the cell pointed to by the pointer in "x" *)
    *{sizeof_scalar} "x" <- #[42] ;;

    Call #[ScFnPtr "g"] #[] ;;

    (* Read the value "v" (it will be 42) from the cell pointed to by the pointer in "x" *)
    let: "v" := Copy *{sizeof_scalar} "x" in

    (* Free the local variable *)
    Free "x" ;;

    (* Finally, return the read value *)
    "v"
  .

Definition unprot_mutable_delete_read_opt : expr :=
    let: "x" := new_place (sizeof_scalar) "i" in
    retag_place "x" MutRef TyFrz sizeof_scalar Default #[ScCallId 0];;
    Call #[ScFnPtr "f"] #[] ;;
    *{sizeof_scalar} "x" <- #[42] ;;
    (* Turn v into a constant, eliminating the read *)
    let: "v" := #[42] in
    Call #[ScFnPtr "g"] #[] ;;
    Free "x" ;;
    "v".

Lemma unprot_mutable_delete_read `{sborGS Σ} :
  ⊢ log_rel unprot_mutable_delete_read_opt unprot_mutable_delete_read_unopt.
Proof.
  log_rel.
  iIntros "%r_t %r_s #Hrel !# %π _".
  sim_pures.

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

  sim_apply (Call _ _) (Call _ _) (sim_call _ (ValR []) (ValR [])) ""; first by iApply value_rel_empty.
  iIntros (r_t r_s) "Hsame1". sim_pures.

  (* do the activation write *)
  source_apply (Copy (Place _ _ _)) (source_copy_local with "Htag Hs") "Hs Htag". 2: done.
  1: rewrite read_range_heaplet_to_list // Z.sub_diag /= //.
  source_pures. source_finish.
  target_apply (Copy (Place _ _ _)) (target_copy_local with "Htag Ht") "Ht Htag". 2: done.
  1: rewrite read_range_heaplet_to_list // Z.sub_diag /= //.
  target_pures.

  sim_apply (Write _ _) (Write _ _) (sim_write_activate_unprotected with "Htag_i Hi_t Hi_s") "Htag_i Hi_t Hi_s". 1-2: done.
  1: rewrite /value_rel /=; iSplit; iFrame; done.
  sim_pures.

  (* second unknown code block *)
  sim_apply (Call _ _) (Call _ _) (sim_call _ (ValR []) (ValR [])) ""; first by iApply value_rel_empty.
  iIntros (r_t2 r_s2) "Hsame2". sim_pures.
 
  (* source load (not existing in the target) *)
  source_apply (Copy (Place _ _ _)) (source_copy_local with "Htag Hs") "Hs Htag". 2: done.
  1: rewrite read_range_heaplet_to_list // Z.sub_diag /= //.
  source_pures. source_bind (Copy _).

  iApply (source_copy_in_simulation with "[] Htag_i Hi_s"). 1: done.
  2: simpl; lia. 1: rewrite read_range_heaplet_to_list // Z.sub_diag /= //.
  { iApply value_rel_int. }
  iIntros (v_res) "Hi_s Htag_i Hv_res". source_pures. source_finish.
  sim_pures.


  (* cleanup: free the local locations*)
  sim_apply (Free _) (Free _) (sim_free_local with "Htag Ht Hs") "Htag"; [done..|]. sim_pures.
  sim_pures.
  sim_val. iModIntro. iSplit; first done. iApply "Hv_res".
Qed.



Section closed.
  (** Obtain a closed proof of [ctx_ref]. *)
  Lemma unprot_mutable_delete_read_ctx : ctx_ref unprot_mutable_delete_read_opt unprot_mutable_delete_read_unopt.
  Proof.
    set Σ := #[sborΣ].
    apply (log_rel_adequacy Σ)=>?.
    apply unprot_mutable_delete_read.
  Qed.
End closed.

(*
Check unprot_mutable_delete_read_ctx.
Print Assumptions unprot_mutable_delete_read_ctx.
*)
(*
unprot_mutable_delete_read_ctx
     : ctx_ref unprot_mutable_delete_read_opt unprot_mutable_delete_read_unopt
Axioms:
IndefiniteDescription.constructive_indefinite_description : ∀ (A : Type) (P : A → Prop), (∃ x : A, P x) → {x : A | P x}
Classical_Prop.classic : ∀ P : Prop, P ∨ ¬ P
*)
