From iris.proofmode Require Import proofmode.
From simuliris.simulation Require Import slsls lifting.
From simuliris.simulang Require Import lang notation proofmode behavior.
From simuliris.simulang.simple_inv Require Import inv adequacy.

(** * Simple example for re-ordering two allocs and then passing the related locations to an external function. *)

Section reorder.
  Context `{!simpleGS Σ}.

  Definition alloc2_and_cont : expr :=
    let: "l1" := Alloc "v1" in
    let: "l2" := Alloc "v2" in
    Call "cont" ("l1", "l2").

  Definition alloc2_and_cont' : expr :=
    let: "l2" := Alloc "v2" in
    let: "l1" := Alloc "v1" in
    Call "cont" ("l1", "l2").

  Lemma alloc2_reorder :
    ⊢ log_rel alloc2_and_cont alloc2_and_cont'.
  Proof.
    log_rel.
    iIntros "%cont_t %cont_s #Hcont %v1_t %v1_s #Hv1 %v2_t %v2_s #Hv2 !# %π _".

    source_alloc l1_s as "Hl1_s" "Ha1_s".
    source_alloc l2_s as "Hl2_s" "Ha2_s".
    sim_pures.

    iApply sim_safe_implies. iIntros ((fcont & ->)).

    val_discr_source "Hcont". sim_pures.

    target_alloc l1_t as "Hl1_t" "Ha1_t".
    target_alloc l2_t as "Hl2_t" "Ha2_t".
    sim_pures.

    iApply (sim_bij_insert with "Ha1_t Ha2_s Hl1_t Hl2_s Hv1"); iIntros "#Hbij_1".
    iApply (sim_bij_insert with "Ha2_t Ha1_s Hl2_t Hl1_s Hv2"); iIntros "#Hbij_2".

    iApply sim_call; [ done.. | simpl; by eauto | ].
    iIntros (??) "Ha". iApply lift_post_val. iFrame.
  Qed.

End reorder.

Section closed.
  (** Obtain a closed proof of [ctx_ref]. *)
  Lemma alloc2_reorder_ctx : ctx_ref alloc2_and_cont alloc2_and_cont'.
  Proof.
    set Σ := #[simpleΣ].
    apply (log_rel_adequacy Σ)=>?.
    apply alloc2_reorder.
  Qed.
End closed.
