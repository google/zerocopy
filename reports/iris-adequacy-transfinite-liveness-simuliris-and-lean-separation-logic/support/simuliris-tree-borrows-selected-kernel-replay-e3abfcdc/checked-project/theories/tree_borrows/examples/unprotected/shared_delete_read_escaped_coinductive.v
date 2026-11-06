From simuliris.simulation Require Import lifting.
From simuliris.tree_borrows Require Import primitive_laws proofmode adequacy examples.lib.

(** Assuming p : (&shr i32, f : Fn(i32) -> bool, g : Fn() -> ?) *)
(* In Rust, [Fn] objects can carry an environment.
  We thus model such objects as two objects: a function pointer, and another scalar (possibly a pointer) for the environment.
  These are not retagged (which mirrors the behavior of e.g. Miri).

  [g] is used for the loop body -- due to the environment it could potentially do "arbitrary" things.

  Note that this example is chosen carefully: There are strictly more reads in the source than there are in the target.
    The load in the target is not "inserted ahead of the loop". Instead, the loop is unrolled once, all subsequent loads
    are removed, and then everything is reshuffled to get back to the same loop.
    Thus, we do not need to insert loads in the target program, allowing us to prove this example correct while getting
    by without exploiting data race UB (something we do not do, in general).
 *)

(*
fn funky_loop(x : &i32, f, g) {
  retag x;
  while(f( *x)) {
    g( *x )
  }
}

fn funky_loop(x : &i32, f, g) {
  retag x;
  let v = *x;
  while(f(v)) {
    g(v)
  }
}

*)


Definition unprot_shared_delete_read_escaped_coinductive_unopt : expr :=
    let: "i" := Proj "p" #[0] in
    (* We do not retag "env" as we do not access it.
      For the purpose of this function, it is just "data". *)
    let: "env" := Proj "p" #[1] in
    (* get the function ptr f *)
    let: "fn" := Proj "p" #[2] in
    (* the same for g *)
    let: "envG" := Proj "p" #[3] in
    let: "fnG" := Proj "p" #[4] in

    (* "x" is the local variable that stores the pointer value "i" *)
    let: "x" := new_place sizeof_scalar "i" in

    (* retag_place reborrows the pointer value stored in "x" (which is "i"),
      then updates "x" with the new pointer value.
    *)
    retag_place "x" ShrRef TyFrz sizeof_scalar Default #[ScCallId 0];;

    while: Call "fn" (Conc "env" (Copy *{sizeof_scalar} "x")) do
      Call "fnG" (Conc "envG" (Copy *{sizeof_scalar} "x"))
    od;;

    (* Free the local variable *)
    Free "x" ;;

    (* finally, return something *)
    #[42]
  .


Definition unprot_shared_delete_read_escaped_coinductive_opt : expr :=
    let: "i" := Proj "p" #[0] in
    let: "env" := Proj "p" #[1] in
    let: "fn" := Proj "p" #[2] in
    let: "envG" := Proj "p" #[3] in
    let: "fnG" := Proj "p" #[4] in
    let: "x" := new_place (sizeof_scalar) "i" in
    retag_place "x" ShrRef TyFrz sizeof_scalar Default #[ScCallId 0];;
    let: "r" := Copy *{sizeof_scalar} "x" in
    while: Call "fn" (Conc "env" "r") do
      Call "fnG" (Conc "envG" "r")
    od;;
    Free "x" ;;
    #[42]
  .


Lemma unprot_shared_delete_read_escaped_coinductive `{sborGS Σ} :
  ⊢ log_rel unprot_shared_delete_read_escaped_coinductive_opt unprot_shared_delete_read_escaped_coinductive_unopt.
Proof.
  log_rel.
  iIntros "%r_t %r_s #Hrel !# %π _".
  sim_pures.

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

  source_bind (Proj _ _).
  iApply source_red_safe_implies.
  iIntros "(%i & %sc' & %Heq & _ & %Hsc')". injection Heq as [= <-].
  destruct v_s as [ | sc_s4 v_s]; simpl in *; first done. injection Hsc' as [= <-].
  source_proj. { simpl. done. }
  source_pures.

  iPoseProof (rrel_value_source with "Hrel") as (v_t) "[-> Hvrel]".
  iPoseProof (value_rel_length with "Hvrel") as "%Hlen".
  destruct v_t as [ | sc_t0 [ | sc_t1 [ | sc_t2 [ | sc_t3 [ | sc_t4 v_t]]]]]; simpl in Hlen; [ lia | lia | lia | lia | lia | ].
  sim_pures.
  do 5 (target_proj; first done; target_pures).
  sim_pures.

  (* new place *)
  sim_apply (new_place _ _) (new_place _ _) sim_new_place_local "%t_x %l_x % % Hx Ht_x Hs_x"; first done.
  sim_pures.

  target_apply (Copy _) (target_copy_local with "Hx Ht_x") "Ht_x Hx". 2: done. 1: rewrite read_range_heaplet_to_list // Z.sub_diag /= //.
  source_apply (Copy _) (source_copy_local with "Hx Hs_x") "Hs_x Hx". 2: done. 1: rewrite read_range_heaplet_to_list // Z.sub_diag /= //.

  rewrite /value_rel. rewrite !big_sepL2_cons.
  iDestruct "Hvrel" as "(#Hsc0_rel & #Hsc1_rel & #Hsc2_rel & #Hsc3_rel & #Hsc4_rel & Hvrel)".

  (* do the retag *)
  sim_bind (Retag _ _ _ _ _ _) (Retag _ _ _ _ _ _).
  iApply sim_safe_implies.
  iIntros ((_ & ot & i & Heq & _)). injection Heq as [= ->].
  iPoseProof (sc_rel_ptr_source with "Hsc0_rel") as "[-> Htagged]".
  iApply (sim_retag_default with "Hsc0_rel"). 1: by cbv.
  iIntros (t_i vx_t vx_s Hlen_t Hlen_s) "#Hvx Htag_i Hi_t Hi_s".
  iApply sim_expr_base.
  target_apply (Write _ _) (target_write_local with "Hx Ht_x") "Ht_x Hx". 2,3: done.
  1: { rewrite write_range_to_to_list; last (simpl; lia). rewrite Z.sub_diag /= //. }
  source_apply (Write _ _) (source_write_local with "Hx Hs_x") "Hs_x Hx". 2: done.
  1: { rewrite write_range_to_to_list; last (simpl; lia). rewrite Z.sub_diag /= //. }
  sim_pures.

  destruct vx_t as [|vx_t []]; try done.
  destruct vx_s as [|vx_s []]; try done.

  (* unroll the loop once, to do a read on both sides *)
  target_apply (Copy (Place _ _ _)) (target_copy_local with "Hx Ht_x") "Ht_x Hx". 2: done. 1: rewrite read_range_heaplet_to_list // Z.sub_diag /= //.
  source_while. source_pures.
  source_apply (Copy (Place _ _ _)) (source_copy_local with "Hx Hs_x") "Hs_x Hx". 2: done. 1: rewrite read_range_heaplet_to_list // Z.sub_diag /= //.
  sim_bind (Copy _) (Copy _). sim_pures.
  iApply (sim_copy with "Htag_i Hi_s Hi_t"). 1,4: done.
  1-2: rewrite read_range_heaplet_to_list // Z.sub_diag /= //.
  iIntros (v_res_s v_res_t) "Hi_s Hi_t #Htag_i #Hv_res".
  sim_pures.
  iApply sim_expr_base.

  iPoseProof (sim_into_read_for_simulation with "Hvx Hv_res") as "#Hreadsim_fut".
  iPoseProof (sim_read_result_value_rel with "Hvx Hv_res") as "#Hreadsim".
  sim_pures. target_while.
  sim_pures.

  (* do the loop header call *)
  source_bind (Call _ _).
  iApply source_red_safe_implies.
  iIntros "(%fn & %Heq)". injection Heq as [= ->].
  iPoseProof (sc_rel_fnptr_source with "Hsc2_rel") as "->".
  iApply source_red_base. iModIntro. to_sim.
  sim_apply (Call _ _) (Call _ _) (sim_call _ (ValR _) (ValR _)) "".
  { iApply big_sepL2_cons. iSplit; first done. iApply "Hreadsim". }
  iIntros (r_t r_s) "#Hres".

  (* the "if" deciding if the loop continues *)
  source_bind (Case _ _).
  destruct r_s; iApply source_red_safe_implies; last by iIntros "?".
  iIntros "(%i'&  %e_s & -> & %Hi' & %He_s_l)".
  iPoseProof (rrel_value_source with "Hres") as (?) "(-> & Hvi')".
  iPoseProof (value_rel_singleton_source with "Hvi'") as (sci') "(-> & Hsci')".
  iPoseProof (sc_rel_int_source with "Hsci'") as "->".
  iClear "Hres Hvi' Hsci'".

  assert (Z.to_nat i' = 0%nat ∨ Z.to_nat i' = 1%nat) as Hzi'.
  { destruct (Z.to_nat i') as [ | ni]; first by left.
    destruct ni as [ | [ | ni]]; first by right. all: simpl in He_s_l; congruence.
  }
  clear He_s_l.
  assert (i' = 0 ∨ i' = 1) as [-> | ->] by lia.

  { (* exit the loop early *)
    source_case. { done. } source_pures.
    target_case. { done. } target_pures.
    sim_pures.
    sim_apply (Free _) (Free _) (sim_free_local with "Hx Ht_x Hs_x") "Hx"; [done..|]. sim_pures.
    sim_val. iModIntro. iSplit; first done. repeat (iSplit; try done). }

  (* the loop continues *)
  iApply source_red_base. iModIntro.
  source_case. { done. } source_pures.
  target_case. { done. } target_pures.
  sim_pures.

  (* resolve the deferred read in the source *)
  source_apply (Copy (Place _ _ _)) (source_copy_local with "Hx Hs_x") "Hs_x Hx". 2: done.
  1: rewrite read_range_heaplet_to_list // Z.sub_diag /= //.
  source_pures. source_bind (Copy _).
  iApply (source_copy_in_simulation with "Hreadsim_fut Htag_i Hi_s"). 1: done.
  2: simpl; lia. 1: rewrite read_range_heaplet_to_list // Z.sub_diag /= //.
  iIntros (v_res_s''') "Hi_s _ #Hinsim'''". source_pures. source_finish.
  sim_pures.

  source_bind (Call _ _).
  iApply source_red_safe_implies.
  iIntros "(%fnG & %Heq)". injection Heq as [= ->].
  iPoseProof (sc_rel_fnptr_source with "Hsc4_rel") as "->".
  iApply source_red_base. iModIntro. to_sim.
  sim_apply (Call _ _) (Call _ _) (sim_call _ (ValR _) (ValR _)) "".
  { iApply big_sepL2_cons. iSplitR; done. }
  iIntros (r_t r_s) "#Hres".

  sim_pures.

  (* initiate coinduction *)
  sim_bind (While _ _) (While _ _).
  set (inv := (
    l_x ↦s∗[tk_local]{t_x} [ScPtr i t_i] ∗
    l_x ↦t∗[tk_local]{t_x} [ScPtr i t_i] ∗
    t_x $$ tk_local ∗
    i ↦s∗[tk_pub]{t_i} [vx_s] ∗
    i ↦t∗[tk_pub]{t_i} [vx_t])%I).

  iApply (sim_while_while inv with "[$]").
  iModIntro. iIntros "(Hs & Ht & Htag & Hi_s & Hi_t)".

  (* resolve the deferred read in the source *)
  source_apply (Copy (Place _ _ _)) (source_copy_local with "Htag Hs") "Hs Htag". 2: done.
  1: rewrite read_range_heaplet_to_list // Z.sub_diag /= //.
  source_pures. source_bind (Copy _).
  iApply (source_copy_in_simulation with "Hreadsim_fut Htag_i Hi_s"). 1: done.
  2: simpl; lia. 1: rewrite read_range_heaplet_to_list // Z.sub_diag /= //.
  iIntros (v_res_s') "Hi_s _ #Hinsim". source_pures. source_finish.
  sim_pures.

  (* do the loop header call *)
  source_bind (Call _ _).
  iApply source_red_safe_implies.
  iIntros "(%fn' & %Heq)". injection Heq as [= ->].
  iApply source_red_base. iModIntro. to_sim.
  sim_apply (Call _ _) (Call _ _) (sim_call _ (ValR _) (ValR _)) "".
  { iApply big_sepL2_cons. iSplit; first done. iApply "Hinsim". }
  iIntros (r_t' r_s') "#Hres'".

  (* the "if" deciding if the loop continues *)
  source_bind (Case _ _).
  destruct r_s'; iApply source_red_safe_implies; last by iIntros "?".
  iIntros "(%i2'&  %e_s' & -> & %Hi2' & %He_s_l)".
  iPoseProof (rrel_value_source with "Hres'") as (?) "(-> & Hvi')".
  iPoseProof (value_rel_singleton_source with "Hvi'") as (sci') "(-> & Hsci')".
  iPoseProof (sc_rel_int_source with "Hsci'") as "->".
  iClear "Hres Hvi' Hsci'".

  assert (Z.to_nat i2' = 0%nat ∨ Z.to_nat i2' = 1%nat) as Hzi2'.
  { destruct (Z.to_nat i2') as [ | ni]; first by left.
    destruct ni as [ | [ | ni]]; first by right. all: simpl in He_s_l; congruence.
  }
  clear He_s_l.
  assert (i2' = 0 ∨ i2' = 1) as [-> | ->] by lia.
  - (* exit the loop *)
    source_case. { done. } source_pures.
    target_case. { done. } target_pures.
    sim_pures. iApply sim_expr_base. iLeft. sim_pures.
    sim_apply (Free _) (Free _) (sim_free_local with "Htag Ht Hs") "Htag"; [done..|]. sim_pures.
    sim_val. iModIntro. iSplit; first done. repeat (iSplit; try done).
  - (* another round *)
    source_case. { done. } source_pures.
    target_case. { done. } target_pures.
    sim_pures.

    (* resolve the deferred read in the source *)
    source_apply (Copy (Place _ _ _)) (source_copy_local with "Htag Hs") "Hs Htag". 2: done.
    1: rewrite read_range_heaplet_to_list // Z.sub_diag /= //.
    source_pures. source_bind (Copy _).
    iApply (source_copy_in_simulation with "Hreadsim_fut Htag_i Hi_s"). 1: done.
    2: simpl; lia. 1: rewrite read_range_heaplet_to_list // Z.sub_diag /= //.
    iIntros (v_res_s'') "Hi_s _ #Hinsim''". source_pures. source_finish.
    sim_pures.

    source_bind (Call _ _).
    iApply source_red_safe_implies.
    iIntros "(%fnG' & %Heq)". injection Heq as [= ->].
    iApply source_red_base. iModIntro. to_sim.
    sim_apply (Call _ _) (Call _ _) (sim_call _ (ValR _) (ValR _)) "".
    { iApply big_sepL2_cons. iSplitR; done. }
    iIntros (r_t' r_s') "#Hres''".

    sim_pures.
    iApply sim_expr_base. iRight. iFrame "Ht Hi_t Hs Htag Hi_s".
    done.
Qed.

Section closed.
  (** Obtain a closed proof of [ctx_ref]. *)
  Lemma unprot_shared_delete_read_escaped_coinductive_ctx : ctx_ref unprot_shared_delete_read_escaped_coinductive_opt unprot_shared_delete_read_escaped_coinductive_unopt.
  Proof.
    set Σ := #[sborΣ].
    apply (log_rel_adequacy Σ)=>?.
    apply unprot_shared_delete_read_escaped_coinductive.
  Qed.
End closed.

(*
Check unprot_shared_delete_read_escaped_coinductive_ctx.
Print Assumptions unprot_shared_delete_read_escaped_coinductive_ctx.
*)
(* 
unprot_shared_delete_read_escaped_coinductive_ctx
     : ctx_ref unprot_shared_delete_read_escaped_coinductive_opt unprot_shared_delete_read_escaped_coinductive_unopt
Axioms:
IndefiniteDescription.constructive_indefinite_description : ∀ (A : Type) (P : A → Prop), (∃ x : A, P x) → {x : A | P x}
Classical_Prop.classic : ∀ P : Prop, P ∨ ¬ P
*)

