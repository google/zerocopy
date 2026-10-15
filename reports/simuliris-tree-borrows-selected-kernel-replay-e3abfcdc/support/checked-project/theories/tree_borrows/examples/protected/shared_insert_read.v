From simuliris.simulation Require Import lifting.
From simuliris.tree_borrows Require Import proofmode lang adequacy examples.lib.



(** Moving read of shared ref up across code that *may* use that ref. *)

(** This is a variant using protectors.
  See delete_read_pubic_escaped_unprotected.v for the original optimization without protectors and with deferred UB.
 *)

(* Assuming x : & i32 *)

Definition prot_shared_insert_read_unopt : expr :=
    let: "c" := InitCall in

    (* "x" is the local variable that stores the pointer value "i" *)
    let: "x" := new_place sizeof_scalar "i" in

    (* retag_place reborrows the pointer value stored in "x" (which is "i"),
      then updates "x" with the new pointer value.
      Using a protector here.
    *)
    retag_place "x" ShrRef TyFrz sizeof_scalar FnEntry "c";;

    (* The unknown code is represented by a call to an unknown function "f" *)
    let: "tst" := Call #[ScFnPtr "f"] (#[]) in
    (* if tst is negative, if so read from x, otherwise return tst *)
    let: "result" := if: "tst" ≤ (#[0])%V
                     then Copy *{sizeof_scalar} "x"
                     else "tst" in

    (* Free the local variable *)
    Free "x" ;;

    (* Finally, return the read value *)
    EndCall "c";;
    "result"
  .

Definition prot_shared_insert_read_opt : expr :=
    let: "c" := InitCall in
    let: "x" := new_place sizeof_scalar "i" in
    retag_place "x" ShrRef TyFrz sizeof_scalar FnEntry "c";;
    let: "tst" := Call #[ScFnPtr "f"] (#[]) in
    let: "v" := Copy *{sizeof_scalar} "x" in
    let: "result" := if: "tst" ≤ (#[0])%V then "v" else "tst" in
    Free "x" ;;
    EndCall "c";;
    "result"
  .

Lemma prot_shared_insert_read `{sborGS Σ} :
  ⊢ log_rel prot_shared_insert_read_opt prot_shared_insert_read_unopt.
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
  iIntros (t_i v_t v_s _ Hlen_t Hlen_s) "Hcall #Hvrel #Htag_i Hi_t Hi_s".
  destruct v_t as [|v_t []]; try done.
  destruct v_s as [|v_s []]; try done. iSimpl in "Hcall".
  iApply sim_expr_base.
  target_apply (Write _ _) (target_write_local with "Htag Ht") "Ht Htag".
  2-3: done. 1: rewrite /write_range bool_decide_true. 2: simpl; lia. 1: rewrite Z.sub_diag /= //.
  source_apply (Write _ _) (source_write_local with "Htag Hs") "Hs Htag".
  2: done. 1: rewrite /write_range bool_decide_true. 2: simpl; lia. 1: rewrite Z.sub_diag /= //.
  sim_pures.

  (* do the call *)
  sim_pures.
  sim_apply (Call _ _) (Call _ _) (sim_call _ (ValR []) (ValR [])) "".
  { iApply big_sepL2_nil. done. }
  iIntros (r_t r_s) "#Hfres". sim_pures.

  (* do the target load *)
  target_apply (Copy (Place _ _ _)) (target_copy_local with "Htag Ht") "Ht Htag". 2: done.
  1: rewrite read_range_heaplet_to_list // Z.sub_diag /= //.
  target_pures. target_bind (Copy _).
  iApply (target_copy_protected with "Hcall Htag_i Hi_t"). 1: done.
  2: simpl; lia. 1: rewrite read_range_heaplet_to_list // Z.sub_diag /= //.
  2: by rewrite lookup_insert_eq.
  { intros off Hoff. simpl in *. rewrite /range'_contains /sizeof_scalar /= in Hoff. assert (off = i.2)%nat as -> by lia. rewrite /shift_loc /= Z.add_0_r /call_set_in lookup_insert_eq /=. by eexists. }
  iIntros "Hi_t _ Hcall". target_finish.
  sim_pures. simpl. rewrite !subst_result.

  source_bind (BinOp _ _ _).
  iApply source_red_safe_implies. 1: eapply (safe_implies_le r_s (ValR [ScInt 0]%V)%V).
  iIntros ((zres_s & z2 & -> & [= <-])).
  destruct r_t as [[|zres_t []]|]; simpl; try done.
  2: { iExFalso. iPoseProof (big_sepL2_length with "Hfres") as "%HH". done. }
  iEval (rewrite /value_rel /= /sc_rel) in "Hfres". iDestruct "Hfres" as "[Hfres _]".
  destruct zres_t; try done. iPure "Hfres" as ->.
  sim_pures. target_pures. sim_pures.
  destruct (bool_decide (zres_s ≤ 0%nat)%Z).
  - simpl. target_case; first done. source_case; first done. sim_pures.
    (* do the source load *)
    source_apply (Copy (Place _ _ _)) (source_copy_local with "Htag Hs") "Hs Htag". 2: done.
    1: rewrite read_range_heaplet_to_list // Z.sub_diag /= //.
    source_pures. source_bind (Copy _).
    iApply (source_copy_protected with "Hcall Htag_i Hi_s"). 1: done.
    2: simpl; lia. 1: rewrite read_range_heaplet_to_list // Z.sub_diag /= //.
    2: by rewrite lookup_insert_eq.
    { intros off Hoff. simpl in *. rewrite /range'_contains /sizeof_scalar /= in Hoff. assert (off = i.2)%nat as -> by lia. rewrite /shift_loc /= Z.add_0_r /call_set_in lookup_insert_eq /=. by eexists. }
    iIntros "Hi_s _ Hcall". source_finish.
    sim_pures.

    (* cleanup: remove the protector ghost state, make the external locations public, free the local locations*)
    sim_apply (Free _) (Free _) (sim_free_local with "Htag Ht Hs") "Htag"; [done..|]. sim_pures.
    iApply (sim_protected_unprotect_public with "Hcall Htag_i"). 1: by rewrite lookup_insert_eq.
    iIntros "Hc". iEval (rewrite delete_insert_id) in "Hc".
    sim_apply (EndCall _) (EndCall _) (sim_endcall_own with "Hc") "".
    sim_pures.
    sim_val. iModIntro. iSplit; first done. done.
  - simpl. target_case; first done. source_case; first done. sim_pures.

    (* cleanup: remove the protector ghost state, make the external locations public, free the local locations*)
    sim_apply (Free _) (Free _) (sim_free_local with "Htag Ht Hs") "Htag"; [done..|]. sim_pures.
    iApply (sim_protected_unprotect_public with "Hcall Htag_i"). 1: by rewrite lookup_insert_eq.
    iIntros "Hc". iEval (rewrite delete_insert_id) in "Hc".
    sim_apply (EndCall _) (EndCall _) (sim_endcall_own with "Hc") "".
    sim_pures.
    sim_val. iModIntro. iSplit; first done. iApply big_sepL2_singleton. done.
Qed.


Section closed.
  (** Obtain a closed proof of [ctx_ref]. *)
  Lemma prot_shared_insert_read_ctx : ctx_ref prot_shared_insert_read_opt prot_shared_insert_read_unopt.
  Proof.
    set Σ := #[sborΣ].
    apply (log_rel_adequacy Σ)=>?.
    apply prot_shared_insert_read.
  Qed.
End closed.

(*
Check prot_shared_insert_read_ctx.
Print Assumptions prot_shared_insert_read_ctx.
*)
(* 
prot_shared_insert_read_ctx
     : ctx_ref prot_shared_insert_read_opt prot_shared_insert_read_unopt
Axioms:
IndefiniteDescription.constructive_indefinite_description : ∀ (A : Type) (P : A → Prop), (∃ x : A, P x) → {x : A | P x}
Classical_Prop.classic : ∀ P : Prop, P ∨ ¬ P
*)

