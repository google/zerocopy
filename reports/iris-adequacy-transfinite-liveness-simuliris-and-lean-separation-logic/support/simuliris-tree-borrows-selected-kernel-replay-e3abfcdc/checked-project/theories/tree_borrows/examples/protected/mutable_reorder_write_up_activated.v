From simuliris.simulation Require Import lifting.
From simuliris.tree_borrows Require Import proofmode lang adequacy examples.lib.


(** Moving a write to a mutable reference up across unknown code. *)

(* Assuming x : &mut i32 *)
Definition prot_mutable_reorder_write_up_activated_unopt : expr :=
    let: "c" := InitCall in
    (* "x" is the local variable that stores the pointer value "i" *)
    let: "x" := new_place sizeof_scalar "i" in

    (* retag_place reborrows the pointer value stored in "x" (which is "i"),
      then updates "x" with the new pointer value. This relies on protectors,
      hence [FnEntry]. *)
    retag_place "x" MutRef TyFrz sizeof_scalar FnEntry "c";;

    (* Write 42 to the cell pointed to by the pointer in "x" *)
    *{sizeof_scalar} "x" <- #[42] ;;

    (* The unknown code is represented by a call to an unknown function "f" *)
    let: "v" := Call #[ScFnPtr "f"] #[] in

    (* Write 13 to the cell pointed to by the pointer in "x" *)
    *{sizeof_scalar} "x" <- #[13] ;;

    (* Free the local variable *)
    Free "x" ;;

    (* Finally, return the value *)
    EndCall "c";;
    "v"
  .

Definition prot_mutable_reorder_write_up_activated_opt : expr :=
    let: "c" := InitCall in
    let: "x" := new_place sizeof_scalar "i" in
    retag_place "x" MutRef TyFrz sizeof_scalar FnEntry "c";;
    *{sizeof_scalar} "x" <- #[13] ;;
    let: "v" := Call #[ScFnPtr "f"] #[] in
    Free "x" ;;
    EndCall "c";;
    "v"
  .

Lemma prot_mutable_reorder_write_up_activated `{sborGS Σ} :
  ⊢ log_rel prot_mutable_reorder_write_up_activated_opt prot_mutable_reorder_write_up_activated_unopt.
Proof.
  log_rel.
  iIntros "%r_t %r_s #Hrel !# %π _".
  sim_pures.
  sim_apply InitCall InitCall sim_init_call "". iIntros (c) "Hcall". iApply sim_expr_base. sim_pures.

  (* new place *)
  simpl. source_bind (new_place _ _).
  iApply source_red_safe_reach.
  { intros. rewrite subst_result. eapply new_place_safe_reach. }
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
  iApply (sim_retag_fnentry with "Hscrel Hcall"). 1: by cbv.
  iIntros (t_i v_t v_s _ Hlen_t Hlen_s) "Hcall #Hvrel Htag_i Hi_t Hi_s".
  destruct v_t as [|v_t []]; try done.
  destruct v_s as [|v_s []]; try done. iSimpl in "Hcall".
  iApply sim_expr_base.
  target_apply (Write _ _) (target_write_local with "Htag Ht") "Ht Htag".
  2-3: done. 1: rewrite /write_range bool_decide_true. 2: simpl; lia. 1: rewrite Z.sub_diag /= //.
  source_apply (Write _ _) (source_write_local with "Htag Hs") "Hs Htag".
  2: done. 1: rewrite /write_range bool_decide_true. 2: simpl; lia. 1: rewrite Z.sub_diag /= //.
  sim_pures.

  (* do the activation write *)
  source_apply (Copy (Place _ _ _)) (source_copy_local with "Htag Hs") "Hs Htag". 2: done.
  1: rewrite read_range_heaplet_to_list // Z.sub_diag /= //.
  source_pures. source_finish.
  target_apply (Copy (Place _ _ _)) (target_copy_local with "Htag Ht") "Ht Htag". 2: done.
  1: rewrite read_range_heaplet_to_list // Z.sub_diag /= //.
  target_pures.

  sim_apply (Write _ _) (Write _ _) (sim_write_activate_protected with "Htag_i Hi_t Hi_s Hcall") "Htag_i Hi_t Hi_s Hcall". 1-3: done.
  { intros off Hoff. simpl in *. assert (off = 0)%nat as -> by lia. rewrite /shift_loc /= Z.add_0_r /call_set_in lookup_insert_eq /=. do 2 eexists; split; first done.
    by rewrite lookup_insert_eq. }
  sim_pures.

  (* arbitrary code *)
  sim_apply (Call _ _) (Call _ _) (sim_call _ (ValR []) (ValR [])) ""; first by iApply value_rel_empty.
  iIntros (r_t r_s) "Hsame1". sim_pures.

  (* do the source store *)
  source_apply (Copy (Place _ _ _)) (source_copy_local with "Htag Hs") "Hs Htag". 2: done.
  1: rewrite read_range_heaplet_to_list // Z.sub_diag /= //.
  source_pures. 
  source_apply (Write (Place _ _ _) _) (source_write_protected_active with "Hcall Htag_i Hi_s") "Hi_s Htag_i Hcall". 1,3,4: done.
  1: { rewrite write_range_to_to_list; last (simpl; lia). rewrite Z.sub_diag /= //. }
  2: rewrite lookup_insert_eq //.
  1: intros off (?&?); assert (off = i.2) as -> by (simpl in *; lia); rewrite /shift_loc /= Z.add_0_r lookup_insert_eq; by eexists.
  source_pures. source_finish.

  (* cleanup: remove the protector ghost state, make the external locations public, free the local locations*)
  sim_apply (Free _) (Free _) (sim_free_local with "Htag Ht Hs") "Htag"; [done..|]. sim_pures.
  iApply (sim_make_unique_public with "Hi_t Hi_s Htag_i Hcall []"). 1: by rewrite lookup_insert_eq.
  { iIntros "_". iApply value_rel_int. }
  iIntros  "Htag_i Hcall". iEval (rewrite !fmap_insert !fmap_empty !insert_insert_eq /=) in "Hcall".
  iApply (sim_protected_unprotect_public with "Hcall Htag_i"). 1: by rewrite lookup_insert_eq.
  iIntros "Hc". iEval (rewrite delete_insert_id) in "Hc".
  sim_apply (EndCall _) (EndCall _) (sim_endcall_own with "Hc") "".
  sim_pures.
  sim_val. iModIntro. iSplit; first done. done.
Qed.

Section closed.
  (** Obtain a closed proof of [ctx_ref]. *)
  Lemma prot_mutable_reorder_write_up_activated_ctx : ctx_ref prot_mutable_reorder_write_up_activated_opt prot_mutable_reorder_write_up_activated_unopt.
  Proof.
    set Σ := #[sborΣ].
    apply (log_rel_adequacy Σ)=>?.
    apply prot_mutable_reorder_write_up_activated.
  Qed.
End closed.

(*
Check prot_mutable_reorder_write_up_activated_ctx.
Print Assumptions prot_mutable_reorder_write_up_activated_ctx.
*)
(* 
prot_mutable_reorder_write_up_activated_ctx
     : ctx_ref prot_mutable_reorder_write_up_activated_opt prot_mutable_reorder_write_up_activated_unopt
Axioms:
IndefiniteDescription.constructive_indefinite_description : ∀ (A : Type) (P : A → Prop), (∃ x : A, P x) → {x : A | P x}
Classical_Prop.classic : ∀ P : Prop, P ∨ ¬ P
*)
