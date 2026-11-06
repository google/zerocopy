From simuliris.simulation Require Import lifting.
From simuliris.tree_borrows Require Import primitive_laws proofmode adequacy examples.lib.

(** Assuming p : (&shr i32, n : i32, opaque : Fn(i32) -> ?) *)
(* In Rust, [Fn] objects can carry an environment.
  We thus model such objects as two objects: a function pointer, and another scalar (possibly a pointer) for the environment.
  These are not retagged (which mirrors the behavior of e.g. Miri).

  [opaque] is used for the loop body -- due to the environment it could potentially do "arbitrary" things.

  Unlike the example in unprotected/, this one actually supports adding a read even if none existed before, due to protectors.
 *)

(*
fn repeat(x : &i32, n, opaque) {
  retag x protected;
  let mut ctr = 0;
  while(ctr < n) {
    opaque( *x);
    ctr += 1;
  }
}

fn repeat(x : &i32, n, opaque) {
  retag x protected;
  let mut val = *x;
  let mut ctr = 0;
  while(ctr < n) {
    opaque(val);
    ctr += 1;
  }
}

*)


Definition unprot_shared_insert_read_coinductive_unopt : expr :=
    let: "c" := InitCall in
    let: "i" := Proj "p" #[0] in
    let: "n" := Proj "p" #[1] in
    (* get the function ptr opaque *)
    let: "opaque" := Proj "p" #[2] in
    (* We do not retag "env" as we do not access it.
      For the purpose of this function, it is just "data". *)
    let: "env_opaque" := Proj "p" #[3] in

    (* "x" is the local variable that stores the pointer value "i" *)
    let: "x" := new_place sizeof_scalar "i" in

    (* retag_place reborrows the pointer value stored in "x" (which is "i"),
      then updates "x" with the new pointer value.
    *)
    retag_place "x" ShrRef TyFrz sizeof_scalar FnEntry "c";;


    let: "ctr" := new_place sizeof_scalar #[0] in

    while: Copy "ctr" < "n" do
      Call "opaque" (Conc "env_opaque" (Copy *{sizeof_scalar} "x")) ;;
      "ctr" <- Copy "ctr" + #[1]
    od;;

    (* Free the local variables *)
    Free "x" ;;
    Free "ctr" ;;
    (* end the protector *)
    EndCall "c";;

    (* finally, return something *)
    #[42]
  .


Definition unprot_shared_insert_read_coinductive_opt : expr :=
    let: "c" := InitCall in
    let: "i" := Proj "p" #[0] in
    let: "n" := Proj "p" #[1] in
    let: "opaque" := Proj "p" #[2] in
    let: "env_opaque" := Proj "p" #[3] in
    let: "x" := new_place sizeof_scalar "i" in
    retag_place "x" ShrRef TyFrz sizeof_scalar FnEntry "c";;
    let: "ctr" := new_place sizeof_scalar #[0] in
    let: "val" := Copy *{sizeof_scalar} "x" in
    while: Copy "ctr" < "n" do
      Call "opaque" (Conc "env_opaque" "val") ;;
      "ctr" <- Copy "ctr" + #[1]
    od;;
    Free "x" ;;
    Free "ctr" ;;
    EndCall "c";;
    #[42]
  .


Lemma unprot_shared_insert_read_coinductive `{sborGS Σ} :
  ⊢ log_rel unprot_shared_insert_read_coinductive_opt unprot_shared_insert_read_coinductive_unopt.
Proof.
  log_rel.
  iIntros "%r_t %r_s #Hrel !# %π _".
  sim_pures.
  sim_apply InitCall InitCall sim_init_call "". iIntros (c) "Hcall". iApply sim_expr_base. sim_pures.

  (* do the projections *)
  source_bind (Proj _ _).
  destruct r_s as [ v_s | ]; iApply source_red_safe_implies; last by iIntros "?".
  iIntros "(%i & %sc & %Heq & _ & %Hsc)". injection Heq as [= <-].
  destruct v_s as [ | sc_s0 v_s]; simpl in *; first done. injection Hsc as [= <-].
  source_proj. { simpl. done. }
  source_pures.

  source_bind (Proj _ _).
  iApply source_red_safe_implies.
  iIntros "(%i & %sc' & %Heq & _ & %Hsc')". injection Heq as [= <-].
  destruct v_s as [ | sc_s1 v_s]; simpl in *; first done. injection Hsc' as [= <-].
  source_proj. { simpl. done. }
  source_pures.

  source_bind (Proj _ _).
  iApply source_red_safe_implies.
  iIntros "(%i & %sc' & %Heq & _ & %Hsc')". injection Heq as [= <-].
  destruct v_s as [ | sc_s2 v_s]; simpl in *; first done. injection Hsc' as [= <-].
  source_proj. { simpl. done. }
  source_pures.

  source_bind (Proj _ _).
  iApply source_red_safe_implies.
  iIntros "(%i & %sc' & %Heq & _ & %Hsc')". injection Heq as [= <-].
  destruct v_s as [ | sc_s3 v_s]; simpl in *; first done. injection Hsc' as [= <-].
  source_proj. { simpl. done. }
  source_pures.

  iPoseProof (rrel_value_source with "Hrel") as (v_t) "[-> Hvrel]".
  iPoseProof (value_rel_length with "Hvrel") as "%Hlen".
  destruct v_t as [ | sc_t0 [ | sc_t1 [ | sc_t2 [ | sc_t3 v_t]]]]; simpl in Hlen; [ lia | lia | lia | lia | ].
  sim_pures.
  do 4 (target_proj; first done; target_pures).
  sim_pures.

  (* new place *)
  sim_apply (new_place _ _) (new_place _ _) sim_new_place_local "%t_x %l_x % % Hx Ht_x Hs_x"; first done.
  sim_pures.

  target_apply (Copy _) (target_copy_local with "Hx Ht_x") "Ht_x Hx". 2: done. 1: rewrite read_range_heaplet_to_list // Z.sub_diag /= //.
  source_apply (Copy _) (source_copy_local with "Hx Hs_x") "Hs_x Hx". 2: done. 1: rewrite read_range_heaplet_to_list // Z.sub_diag /= //.

  rewrite /value_rel. rewrite !big_sepL2_cons.
  iDestruct "Hvrel" as "(#Hsc0_rel & #Hsc1_rel & #Hsc2_rel & #Hsc3_rel & Hvrel)".

  (* do the retag *)
  sim_bind (Retag _ _ _ _ _ _) (Retag _ _ _ _ _ _).
  iApply sim_safe_implies.
  iIntros ((_ & ot & i & Heq & _)). injection Heq as [= ->].
  iPoseProof (sc_rel_ptr_source with "Hsc0_rel") as "[-> Htagged]".
  iApply (sim_retag_fnentry with "Hsc0_rel Hcall"). 1: by cbv.
  iIntros (t_i vx_t vx_s _ Hlen_t Hlen_s) "Hcall #Hvx #Htag_i Hi_t Hi_s".
  iApply sim_expr_base.
  target_apply (Write _ _) (target_write_local with "Hx Ht_x") "Ht_x Hx". 2,3: done.
  1: { rewrite write_range_to_to_list; last (simpl; lia). rewrite Z.sub_diag /= //. }
  source_apply (Write _ _) (source_write_local with "Hx Hs_x") "Hs_x Hx". 2: done.
  1: { rewrite write_range_to_to_list; last (simpl; lia). rewrite Z.sub_diag /= //. }
  sim_pures. rewrite /pointer_kind_to_access_ensuring.

  destruct vx_t as [|vx_t []]; try done.
  destruct vx_s as [|vx_s []]; try done.

  sim_apply (new_place _ _) (new_place _ _) sim_new_place_local "%t_ctr %l_ctr % % Hctr Ht_ctr Hs_ctr"; first done.
  sim_pures.

  (* insert target load *)
  target_apply (Copy (Place _ _ _)) (target_copy_local with "Hx Ht_x") "Ht_x Hx". 2: done.
  1: rewrite read_range_heaplet_to_list // Z.sub_diag /= //.
  target_pures. target_bind (Copy _).
  iApply (target_copy_protected with "Hcall Htag_i Hi_t"). 1: done.
  2: simpl; lia. 1: rewrite read_range_heaplet_to_list // Z.sub_diag /= //.
  2: by rewrite lookup_insert_eq.
  { intros off Hoff. simpl in *. rewrite /range'_contains /sizeof_scalar /= in Hoff. assert (off = i.2)%nat as -> by lia. rewrite /shift_loc /= Z.add_0_r /call_set_in lookup_insert_eq /=. by eexists. }
  iIntros "Hi_t _ Hcall". target_finish.
  sim_pures.

  rewrite insert_empty.

  (* initiate coinduction *)
  sim_bind (While _ _) (While _ _).
  set (inv := (∃ (cval:Z),
    l_ctr ↦s∗[tk_local]{t_ctr} [ScInt cval] ∗
    l_ctr ↦t∗[tk_local]{t_ctr} [ScInt cval] ∗
    t_ctr $$ tk_local ∗
    l_x ↦s∗[tk_local]{t_x} [ScPtr i t_i] ∗
    l_x ↦t∗[tk_local]{t_x} [ScPtr i t_i] ∗
    t_x $$ tk_local ∗
    i ↦s∗[tk_pub]{t_i} [vx_s] ∗
    i ↦t∗[tk_pub]{t_i} [vx_t] ∗
    c @@ {[t_i := seq_loc_map i sizeof_scalar (EnsuringAccess Strongly)]})%I).

  iApply (sim_while_while inv with "[$]").
  iModIntro. iIntros "(%ctr & Hs_ctr & Ht_ctr & Hctr & Hs_x & Ht_x & Hx & Hi_s & Hi_t & Hcall)".

  (* Loop header *)
  target_apply (Copy (Place _ _ _)) (target_copy_local with "Hctr Ht_ctr") "Ht_ctr Hctr". 2: done.
  1: rewrite read_range_heaplet_to_list // Z.sub_diag /= //.
  target_pures. target_finish.

  source_apply (Copy (Place _ _ _)) (source_copy_local with "Hctr Hs_ctr") "Hs_ctr Hctr". 2: done.
  1: rewrite read_range_heaplet_to_list // Z.sub_diag /= //.
  source_pures. source_finish.

  sim_bind (_ < _)%E (_ < _)%E.
  iApply sim_safe_implies. 1: eapply (safe_implies_lt (ValR _) (ValR _)).
  iIntros ((z1 & nval & [= <-] & [= ->])).
  destruct sc_t1; iSimpl in "Hsc1_rel"; [done| |done..].
  iPure "Hsc1_rel" as ->.
  sim_pures.
  iApply sim_expr_base.
  destruct (bool_decide (ctr < nval)).
  - source_case. { done. } source_pures.
    target_case. { done. } target_pures.
    
    (* eliminated source load *)
    source_apply (Copy (Place _ _ _)) (source_copy_local with "Hx Hs_x") "Hs_x Hx". 2: done.
    1: rewrite read_range_heaplet_to_list // Z.sub_diag /= //.
    source_pures. source_bind (Copy _).
    iApply (source_copy_protected with "Hcall Htag_i Hi_s"). 1: done.
    2: simpl; lia. 1: rewrite read_range_heaplet_to_list // Z.sub_diag /= //.
    2: by rewrite lookup_insert_eq.
    { intros off Hoff. simpl in *. rewrite /range'_contains /sizeof_scalar /= in Hoff. assert (off = i.2)%nat as -> by lia. rewrite /shift_loc /= Z.add_0_r /call_set_in lookup_insert_eq /=. by eexists. }
    iIntros "Hi_s _ Hcall". source_finish.
    sim_pures.

    (* call fn *)
    source_bind (Call _ _).
    iApply source_red_safe_implies.
    iIntros "(%fn & %Heq)". injection Heq as [= ->].
    iPoseProof (sc_rel_fnptr_source with "Hsc2_rel") as "->".
    iApply source_red_base. iModIntro. to_sim.
    sim_apply (Call _ _) (Call _ _) (sim_call _ (ValR _) (ValR _)) "".
    { iSplit; first done. simpl. iApply "Hvx". }
    iIntros (r_t r_s) "Hsame1". sim_pures.

    (* increment counter *)
    target_apply (Copy (Place _ _ _)) (target_copy_local with "Hctr Ht_ctr") "Ht_ctr Hctr". 2: done.
    1: rewrite read_range_heaplet_to_list // Z.sub_diag /= //.
    target_pures.
    target_apply (Write (Place _ _ _) _) (target_write_local with "Hctr Ht_ctr") "Ht_ctr Hctr". 2,3: done.
    1: apply write_range_to_to_list; simpl; lia.
    target_finish.

    source_apply (Copy (Place _ _ _)) (source_copy_local with "Hctr Hs_ctr") "Hs_ctr Hctr". 2: done.
    1: rewrite read_range_heaplet_to_list // Z.sub_diag /= //.
    source_pures.
    source_apply (Write (Place _ _ _) _) (source_write_local with "Hctr Hs_ctr") "Hs_ctr Hctr". 2: done.
    1: apply write_range_to_to_list; simpl; lia.
    source_finish.
    sim_pures.
    iApply sim_expr_base. iRight. do 2 (iSplit; first done).
    rewrite Z.sub_diag Z2Nat.inj_0. iSimpl in "Ht_ctr". iSimpl in "Hs_ctr".
    iExists (ctr + 1).
    iFrame.    
  - source_case. { done. } source_pures.
    target_case. { done. } target_pures.
    iApply sim_expr_base. iLeft. sim_pures.
    sim_apply (Free _) (Free _) (sim_free_local with "Hx Ht_x Hs_x") "Hx"; [done..|]. sim_pures.
    sim_apply (Free _) (Free _) (sim_free_local with "Hctr Ht_ctr Hs_ctr") "Hctr"; [done..|]. sim_pures.
    iApply (sim_protected_unprotect_public with "Hcall Htag_i"). 1: by rewrite lookup_insert_eq.
    iIntros "Hc". iEval (rewrite delete_insert_id) in "Hc".
    sim_apply (EndCall _) (EndCall _) (sim_endcall_own with "Hc") "".
    sim_pures.
    sim_val. iModIntro. iSplit; first done. unfold rrel, value_rel. simpl. done.
Qed.

Section closed.
  (** Obtain a closed proof of [ctx_ref]. *)
  Lemma unprot_shared_insert_read_coinductive_ctx : ctx_ref unprot_shared_insert_read_coinductive_opt unprot_shared_insert_read_coinductive_unopt.
  Proof.
    set Σ := #[sborΣ].
    apply (log_rel_adequacy Σ)=>?.
    apply unprot_shared_insert_read_coinductive.
  Qed.
End closed.

(*
Check unprot_shared_insert_read_coinductive_ctx.
Print Assumptions unprot_shared_insert_read_coinductive_ctx.
*)
(* 
unprot_shared_insert_read_coinductive_ctx
     : ctx_ref unprot_shared_insert_read_coinductive_opt unprot_shared_insert_read_coinductive_unopt
Axioms:
IndefiniteDescription.constructive_indefinite_description : ∀ (A : Type) (P : A → Prop), (∃ x : A, P x) → {x : A | P x}
Classical_Prop.classic : ∀ P : Prop, P ∨ ¬ P
*)

