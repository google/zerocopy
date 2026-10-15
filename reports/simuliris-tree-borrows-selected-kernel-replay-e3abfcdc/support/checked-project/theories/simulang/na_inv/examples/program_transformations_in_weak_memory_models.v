From iris.proofmode Require Import proofmode.
From simuliris.simulation Require Import slsls lifting gen_log_rel.
From simuliris.simulang Require Import lang notation tactics class_instances
  proofmode log_rel_structural.
From simuliris.simulang.na_inv Require Export inv readonly_refl.

(** * Eliminations and reorderings from "Program Transformations in Weak Memory Models" by Jaroslav Sevcik *)

Section eliminations.
  Context `{naGS Σ}.

  (** Eliminations from figure 4.6. See also Definition 3.1 *)

  Definition E_RaR_s : expr := let: "r1" := !"x" in let: "r2" := !"x" in ("r1", "r2").
  Definition E_RaR_t : expr := let: "r1" := !"x" in let: "r2" := "r1" in ("r1", "r2").

  Definition E_RaW_s : expr := "x" <- "r1";; let: "r2" := !"x" in "r2".
  Definition E_RaW_t : expr := "x" <- "r1";; let: "r2" := "r1" in "r2".

  Definition E_WaR_s : expr := let: "r" := !"x" in "x" <- "r";; "r".
  Definition E_WaR_t : expr := let: "r" := !"x" in             "r".

  Definition E_WbW_s : expr := "x" <- "r1";; "x" <- "r2".
  Definition E_WbW_t : expr := "x" <- "r2".

  Definition E_IR_s (v : Z) : expr := let: "r" := !"x" in let: "r" := #v in "r".
  Definition E_IR_t (v : Z) : expr := let: "r" := #v in "r".

  (* Below are some SC versions of the above transformations. They
  should be provable, but are not really interesting as they don't
  contain NA accesses. *)

  (* SC version of E_WaR that we should be able to prove by
  choosing the schedule where there is no thread between the two (has
  nothing to do with data races). *)
  Definition E_WaR_s1 : expr := let: "r" := !ˢᶜ "x" in "x" <-ˢᶜ "r";; "r".
  Definition E_WaR_t1 : expr := let: "r" := !ˢᶜ "x" in                "r".

  (* Version of E_WaR if "r" is unused. *)
  Definition E_WaR_s2 : expr := let: "r" := !"x" in "x" <- "r".
  Definition E_WaR_t2 : expr := #().

  (* Combining the two previous versions. *)
  Definition E_WaR_s3 : expr := let: "r" := !ˢᶜ"x" in "x" <-ˢᶜ "r".
  Definition E_WaR_t3 : expr := #().

  (* SC version of E_WbW that we should be able to prove by
  choosing the schedule where there is no thread between the two (has
  nothing to do with data races). *)
  Definition E_WbW_s1 : expr := "x" <-ˢᶜ "r1";; "x" <-ˢᶜ "r2".
  Definition E_WbW_t1 : expr := "x" <-ˢᶜ "r2".

  (* SC version of E_IR that we should be able to prove. *)
  Definition E_IR_s1 (v : Z) : expr := let: "r" := !ˢᶜ "x" in let: "r" := #v in "r".
  Definition E_IR_t1 (v : Z) : expr := let: "r" := #v in "r".

  Lemma E_RaR_sim:
    ⊢ log_rel E_RaR_t E_RaR_s.
  Proof.
    log_rel.
    iIntros "%v_t1 %v_s1 #Hv1 !# %π Hc".
    sim_bind (! _)%E (! _)%E. discr_source. val_discr_source "Hv1".
    iApply (sim_bij_exploit_load with "Hv1 Hc"); [|done|].
    { intros. apply: safe_reach_safe_implies => ?. apply: safe_reach_refl. apply: post_in_ectx_intro. naive_solver. }
    iIntros (q v_t v_s) "Hl_t Hl_s #Hv Hc".
    source_load. target_load. sim_val. source_load. sim_pures.
    iApply (sim_bij_release (NaRead _) with "Hv1 Hc [$] [$] Hv"); [by simplify_map_eq| ].
    iIntros "Hc". rewrite delete_insert_id //.
    sim_val => /=. iModIntro. iFrame "∗Hv".
  Qed.

  Lemma E_RaW_sim:
    ⊢ log_rel E_RaW_t E_RaW_s.
  Proof.
    log_rel.
    iIntros "%v_t1 %v_s1 #Hv1 %v_t2 %v_s2 #Hv2 !# %π Hc".
    sim_bind (_ <- _)%E (_ <- _)%E. discr_source. val_discr_source "Hv1".
    iApply (sim_bij_exploit_store with "Hv1 Hc"); [|done|].
    { intros. apply: safe_reach_safe_implies => ?. apply: safe_reach_refl. apply: post_in_ectx_intro. naive_solver. }
    iIntros (v_t v_s) "Hl_t Hl_s #Hv Hc".
    source_store. target_store. sim_val. source_load. sim_pures.
    iApply (sim_bij_release NaExcl with "Hv1 Hc [$] [$] Hv2"); [by simplify_map_eq| ].
    iIntros "Hc". rewrite delete_insert_id //.
    sim_val => /=. iModIntro. iFrame "∗Hv2".
  Qed.

  Lemma E_WaR_sim:
    ⊢ log_rel E_WaR_t E_WaR_s.
  Proof.
    log_rel.
    iIntros "%v_t1 %v_s1 #Hv1 !# %π Hc".
    source_bind (! _)%E. discr_source. val_discr_source "Hv1".
    do 2 iApply source_red_base. do 2 iModIntro.
    iApply (sim_bij_exploit_store with "Hv1 Hc"); [|done|]. {
      intros.
      safe_reach_bind (! _)%E.
      eapply safe_reach_safe_implies; first apply _.
      intros (l & v & n & [= <-] & Hs_mem). eapply safe_reach_load; [done.. | ].
      eapply safe_reach_refl.
      eapply safe_reach_base_step; [by econstructor|]. simpl. simpl_subst.
      safe_reach_fill (_ <- _)%E.
      apply: safe_reach_safe_implies => ?.
      apply: safe_reach_refl. apply: post_in_ectx_intro. naive_solver.
    }
    iIntros (v_t v_s) "Hl_t Hl_s #Hv Hc".
    source_load. target_load. source_store. sim_pures.
    iApply (sim_bij_release NaExcl with "Hv1 Hc [$] [$] Hv"); [by simplify_map_eq| ].
    iIntros "Hc". rewrite delete_insert_id //.
    sim_val => /=. iModIntro. iFrame "∗Hv".
  Qed.

  Lemma E_WbW_sim:
    ⊢ log_rel E_WbW_t E_WbW_s.
  Proof.
    log_rel.
    iIntros "%v_t1 %v_s1 #Hv1 %v_t2 %v_s2 #Hv2 %v_t3 %v_s3 #Hv3 !# %π Hc".
    sim_bind (_ <- _)%E (_ <- _)%E. discr_source. val_discr_source "Hv2".
    iApply (sim_bij_exploit_store with "Hv2 Hc"); [|done|].
    { intros. apply: safe_reach_safe_implies => ?. apply: safe_reach_refl. apply: post_in_ectx_intro. naive_solver. }
    iIntros (v_t v_s) "Hl_t Hl_s #Hv Hc".
    source_store. target_store. sim_val. source_store.
    iApply (sim_bij_release NaExcl with "Hv2 Hc [$] [$] Hv1"); [by simplify_map_eq| ].
    iIntros "Hc". rewrite delete_insert_id //.
    sim_val => /=. iModIntro. by iFrame.
  Qed.

  Lemma E_IR_sim v:
    ⊢ log_rel (E_IR_t v) (E_IR_s v).
  Proof.
    log_rel.
    iIntros "%v_t1 %v_s1 #Hv1 !# %π Hc".
    sim_bind (Val _) (! _)%E. discr_source. val_discr_source "Hv1".
    iApply (sim_bij_exploit_load with "Hv1 Hc"); [|done|].
    { intros. apply: safe_reach_safe_implies => ?. apply: safe_reach_refl. apply: post_in_ectx_intro. naive_solver. }
    iIntros (q v_t v_s) "Hl_t Hl_s #Hv Hc".
    source_load. sim_val. sim_pures.
    iApply (sim_bij_release (NaRead _) with "Hv1 Hc [$] [$] Hv"); [by simplify_map_eq| ].
    iIntros "Hc". rewrite delete_insert_id //.
    sim_val => /=. iModIntro. by iFrame.
  Qed.

End eliminations.

Section reorderings.
  Context `{naGS Σ}.
  (** Reorderings from figure 4.7. *)

  (* The following requires the relevant memory locations to be global
  variables. This is also what Program Transformations does and it
  allows us to easily express the constraint that two locations are
  different. In principle, these transformations should work for
  arbitrary pointers where we know that they are disjoint (except for
  R_RR which also works for overlapping pointers). *)

  (* In Program Transformations, this only works for o1 = Na1Ord. We can do it
  for o1 = Na1Ord ∨ o2 = Na1Ord. *)
  Definition R_RR_s (o1 o2 : order) (x y : string) : expr :=
    let: "x" := (GlobalVar x) in let: "y" := (GlobalVar y) in
    let: "r1" := Load o1 "x" in let: "r2" := Load o2 "y" in ("r1", "r2").
  Definition R_RR_t (o1 o2 : order) (x y : string) : expr :=
    let: "x" := (GlobalVar x) in let: "y" := (GlobalVar y) in
    let: "r2" := Load o2 "y" in let: "r1" := Load o1 "x" in ("r1", "r2").

  (* This transformations requires x ≠ y and o2 = Na1Ord (both in
  Program Transformations and here). *)
  Definition R_WW_s (o1 o2 : order) (x y : string) : expr :=
    let: "x" := (GlobalVar x) in let: "y" := (GlobalVar y) in
    Store o1 "x" "r1";; Store o2 "y" "r2".
  Definition R_WW_t (o1 o2 : order) (x y : string) : expr :=
    let: "x" := (GlobalVar x) in let: "y" := (GlobalVar y) in
    Store o2 "y" "r2";; Store o1 "x" "r1".

  (* This transformations requires x ≠ y and o1 = Na1Ord ∨ o2 = Na1Ord (both in
  Program Transformations and here). *)
  Definition R_WR_s (o1 o2 : order) (x y : string) : expr :=
    let: "x" := (GlobalVar x) in let: "y" := (GlobalVar y) in
    Store o1 "x" "r1";; let: "r2" := Load o2 "y" in "r2".
  Definition R_WR_t (o1 o2 : order) (x y : string) : expr :=
    let: "x" := (GlobalVar x) in let: "y" := (GlobalVar y) in
    let: "r2" := Load o2 "y" in Store o1 "x" "r1";; "r2".

  (* Program Transformations requires x ≠ y and o1 = Na1Ord ∧ o2 =
  Na1Ord for this optimization. We can do it for x ≠ y and o2 = Na1Ord. *)
  Definition R_RW_s (o1 o2 : order) (x y : string) : expr :=
    let: "x" := (GlobalVar x) in let: "y" := (GlobalVar y) in
    let: "r1" := Load o1 "x" in Store o2 "y" "r2";; "r1".
  Definition R_RW_t (o1 o2 : order) (x y : string) : expr :=
    let: "x" := (GlobalVar x) in let: "y" := (GlobalVar y) in
    Store o2 "y" "r2";; let: "r1" := Load o1 "x" in "r1".

  Lemma R_RR_sim o1 o2 x y:
    o1 ≠ Na2Ord → o2 ≠ Na2Ord →
    o1 = Na1Ord ∨ o2 = Na1Ord →
    ⊢ log_rel (R_RR_t o1 o2 x y) (R_RR_s o1 o2 x y).
  Proof.
    move => ?? Hor. log_rel.
    iIntros "!# %π Hc".
    source_bind (GlobalVar _).
    iApply source_red_global'; [|apply sim_bij_contains_globalbij|]; [apply _|].
    iIntros "#? #? #Hx". sim_pures. sim_pures.
    source_bind (GlobalVar _).
    iApply source_red_global'; [|apply sim_bij_contains_globalbij|]; [apply _|].
    iIntros "#? #? #Hy". sim_pures. sim_pures.
    target_bind (GlobalVar _). iApply target_red_global; [done|].
    sim_pures. sim_pures.
    target_bind (GlobalVar _). iApply target_red_global; [done|].
    sim_pures. sim_pures.

    destruct Hor; simplify_eq.
    - iApply (sim_bij_exploit_load with "Hx Hc"); [|done|].
      { intros. safe_reach_fill (! _)%E. apply: safe_reach_safe_implies => ?. apply: safe_reach_refl. apply: post_in_ectx_intro. naive_solver. }
      iIntros (q v_t v_s) "Hl_t Hl_s #Hv Hc".
      source_load. sim_pures. sim_bind (Load _ _) (Load _ _).
      iApply (sim_bij_load_pointstolist [(global_loc x, global_loc x, v_t, v_s, q)] with "Hy Hc [-]"); [done| | |].
      { move => ??? /lookup_insert_Some[[??]|[??]]; simplify_eq. by eexists 0, _, _. }
      { by iFrame "∗ Hv Hx". }
      iIntros (v_t' v_s') "#? Hc". rewrite /pointsto_list /=.
      iIntros "[(?&?&_&_) _]". sim_val. target_load. sim_pures.
      iApply (sim_bij_release (NaRead _) with "Hx Hc [$] [$] Hv"); [by simplify_map_eq| ].
      iIntros "Hc". rewrite delete_insert_id //. sim_val. iModIntro. iFrame. by iSplit.
    - iApply (sim_bij_exploit_load with "Hy Hc"); [|done|].
      { intros. safe_reach_bind (Load _ _)%E.
        eapply safe_reach_safe_implies; first apply _.
        intros (l & v & n & [= <-] & Hs_mem). eapply safe_reach_load; [done.. | ].
        apply: safe_reach_refl.
        apply: safe_reach_base_step; [ by econstructor|] => /=. simpl_subst.
        safe_reach_fill (! _)%E. apply: safe_reach_safe_implies => ?.
        apply: safe_reach_refl. apply: post_in_ectx_intro. naive_solver. }
      iIntros (q v_t v_s) "Hl_t Hl_s #Hv Hc".
      target_load. sim_pures. sim_bind (Load _ _) (Load _ _).
      iApply (sim_bij_load_pointstolist [(global_loc y, global_loc y, v_t, v_s, q)] with "Hx Hc [-]"); [done| | |].
      { move => ??? /lookup_insert_Some[[??]|[??]]; simplify_eq. by eexists 0, _, _. }
      { by iFrame "∗ Hv Hy". }
      iIntros (v_t' v_s') "#? Hc". rewrite /pointsto_list /=.
      iIntros "[(?&?&_&_) _]". sim_val. source_load. sim_pures.
      iApply (sim_bij_release (NaRead _) with "Hy Hc [$] [$] Hv"); [by simplify_map_eq| ].
      iIntros "Hc". rewrite delete_insert_id //. sim_val. iModIntro. iFrame. by iSplit.
  Qed.

  Lemma R_WW_sim o1 o2 x y:
    x ≠ y →
    o1 ≠ Na2Ord → o2 ≠ Na2Ord →
    o2 = Na1Ord →
    ⊢ log_rel (R_WW_t o1 o2 x y) (R_WW_s o1 o2 x y).
  Proof.
    move => ????. log_rel.
    iIntros "%r2_t %r2_s #Hr2 %r1_t %r1_s #Hr1 !# %π Hc".
    source_bind (GlobalVar _).
    iApply source_red_global'; [|apply sim_bij_contains_globalbij|]; [apply _|].
    iIntros "#? #? #Hx". sim_pures. sim_pures.
    source_bind (GlobalVar _).
    iApply source_red_global'; [|apply sim_bij_contains_globalbij|]; [apply _|].
    iIntros "#? #? #Hy". sim_pures. sim_pures.
    target_bind (GlobalVar _). iApply target_red_global; [done|].
    sim_pures. sim_pures.
    target_bind (GlobalVar _). iApply target_red_global; [done|].
    sim_pures. sim_pures.

    destruct o2 => //.
    destruct o1 => //.
    - iApply (sim_bij_exploit_store with "Hy Hc"); [|done|].
      { intros.
        safe_reach_bind (Store _ _ _)%E.
        apply: safe_reach_store; [done|].
        apply: safe_reach_refl.
        apply: safe_reach_base_step; [by econstructor|] => /=.
        apply: safe_reach_safe_implies => -[?[?[[<-] /=/lookup_insert_Some[?|?]]]].
        { naive_solver. }
        apply: safe_reach_refl. apply: post_in_ectx_intro. naive_solver. }
      iIntros (v_t v_s) "Hl_t Hl_s #Hv Hc".
      target_store. sim_pures.
      iApply (sim_bij_store_sc [] [SeqEctx _] with "Hx Hc Hr1").
      { rewrite lookup_insert_ne //. naive_solver. }
      { move => ????? /lookup_insert_Some[[??]|[??//]]; simplify_eq/=.
        apply: safe_reach_base_step; [by econstructor|] => /=.
        apply: safe_reach_refl. apply: post_in_ectx_intro. naive_solver. }
      iIntros "Hc /=". source_store.
      iApply (sim_bij_release NaExcl with "Hy Hc [$] [$] Hr2"); [by simplify_map_eq| ].
      iIntros "Hc". rewrite delete_insert_id //. sim_val. iModIntro. by iFrame.
    - iApply (sim_bij_exploit_store with "Hx Hc"); [|done|].
      { intros. safe_reach_fill (_ <- _)%E. apply: safe_reach_safe_implies => ?. apply: safe_reach_refl. apply: post_in_ectx_intro. naive_solver. }
      iIntros (v_t v_s) "Hl_t Hl_s #Hv Hc".
      source_store. sim_pures. sim_bind (Store _ _ _) (Store _ _ _).
      iApply (sim_bij_store_na with "Hy Hc Hr2").
      { rewrite lookup_insert_ne //. move => ?. simplify_eq. }
      iIntros "Hc". sim_val. target_store.
      iApply (sim_bij_release NaExcl with "Hx Hc [$] [$] Hr1"); [by simplify_map_eq| ].
      iIntros "Hc". rewrite delete_insert_id //. sim_val. iModIntro. by iFrame.
  Qed.

  Lemma R_WR_sim o1 o2 x y:
    x ≠ y →
    o1 ≠ Na2Ord → o2 ≠ Na2Ord →
    o1 = Na1Ord ∨ o2 = Na1Ord →
    ⊢ log_rel (R_WR_t o1 o2 x y) (R_WR_s o1 o2 x y).
  Proof.
    move => ??? Hor. log_rel.
    iIntros "%r2_t %r2_s #Hr2 !# %π Hc".
    source_bind (GlobalVar _).
    iApply source_red_global'; [|apply sim_bij_contains_globalbij|]; [apply _|].
    iIntros "#? #? #Hx". sim_pures. sim_pures.
    source_bind (GlobalVar _).
    iApply source_red_global'; [|apply sim_bij_contains_globalbij|]; [apply _|].
    iIntros "#? #? #Hy". sim_pures. sim_pures.
    target_bind (GlobalVar _). iApply target_red_global; [done|].
    sim_pures. sim_pures.
    target_bind (GlobalVar _). iApply target_red_global; [done|].
    sim_pures. sim_pures.

    destruct o1; simplify_eq.
    - destruct Hor => //; simplify_eq.
     iApply (sim_bij_exploit_load with "Hy Hc"); [|done|].
      { intros.
        safe_reach_bind (Store _ _ _)%E.
        apply: safe_reach_store; [done|].
        apply: safe_reach_refl.
        apply: safe_reach_base_step; [by econstructor|] => /=.
        safe_reach_fill (! _)%E.
        apply: safe_reach_safe_implies => -[?[?[?[[<-] /=/lookup_insert_Some[?|?]]]]].
        { naive_solver. }
        apply: safe_reach_refl. apply: post_in_ectx_intro. naive_solver. }
      iIntros (q v_t v_s) "Hl_t Hl_s #Hv Hc".
      target_load. sim_pures.
      iApply (sim_bij_store_sc [SeqEctx _] [SeqEctx _] with "Hx Hc Hr2").
      { rewrite lookup_insert_ne //. naive_solver. }
      { move => ????? /lookup_insert_Some[[??]|[??//]]; simplify_eq/=.
        apply: safe_reach_base_step; [by econstructor|] => /=.
        safe_reach_fill (! _)%E. apply: safe_reach_refl. apply: post_in_ectx_intro. naive_solver. }
      iIntros "Hc /=". source_load. sim_pures.
      iApply (sim_bij_release (NaRead _) with "Hy Hc [$] [$] Hv"); [by simplify_map_eq| ].
      iIntros "Hc". rewrite delete_insert_id //. sim_val. iModIntro. by iFrame.
    - iApply (sim_bij_exploit_store with "Hx Hc"); [|done|].
      { intros. safe_reach_fill (_ <- _)%E. apply: safe_reach_safe_implies => ?. apply: safe_reach_refl. apply: post_in_ectx_intro. naive_solver. }
      iIntros (v_t v_s) "Hl_t Hl_s #Hv Hc".
      source_store. sim_pures. sim_bind (Load _ _) (Load _ _).
      iApply (sim_bij_load with "Hy Hc"); [|done|].
      { rewrite lookup_insert_ne //. move => ?. simplify_eq. }
      iIntros (v_t' v_s') "Hv' Hc". sim_val. target_store. sim_pures.
      iApply (sim_bij_release NaExcl with "Hx Hc [$] [$] Hr2"); [by simplify_map_eq| ].
      iIntros "Hc". rewrite delete_insert_id //. sim_val. iModIntro. by iFrame.
  Qed.

  Lemma R_RW_sim o1 o2 x y:
    x ≠ y →
    o1 ≠ Na2Ord → o2 ≠ Na2Ord →
    o2 = Na1Ord →
    ⊢ log_rel (R_RW_t o1 o2 x y) (R_RW_s o1 o2 x y).
  Proof.
    move => ??? Ho. log_rel.
    iIntros "%r1_t %r1_s #Hr1 !# %π Hc".
    source_bind (GlobalVar _).
    iApply source_red_global'; [|apply sim_bij_contains_globalbij|]; [apply _|].
    iIntros "#? #? #Hx". sim_pures. sim_pures.
    source_bind (GlobalVar _).
    iApply source_red_global'; [|apply sim_bij_contains_globalbij|]; [apply _|].
    iIntros "#? #? #Hy". sim_pures. sim_pures.
    target_bind (GlobalVar _). iApply target_red_global; [done|].
    sim_pures. sim_pures.
    target_bind (GlobalVar _). iApply target_red_global; [done|].
    sim_pures. sim_pures.

    simplify_eq.
    iApply (sim_bij_exploit_store with "Hy Hc"); [|done|].
    { intros. safe_reach_bind (Load _ _)%E.
      eapply safe_reach_safe_implies; first apply _.
      intros (l & v & n & [= <-] & Hs_mem). eapply safe_reach_load; [done.. | ].
      apply: safe_reach_refl.
      apply: safe_reach_base_step; [ by econstructor|] => /=. simpl_subst.
      safe_reach_fill (_ <- _)%E. apply: safe_reach_safe_implies => ?.
      apply: safe_reach_refl. apply: post_in_ectx_intro. naive_solver. }
    iIntros (v_t v_s) "Hl_t Hl_s #Hv Hc".
    target_store. sim_pures. sim_bind (Load _ _) (Load _ _).
    iApply (sim_bij_load with "Hx Hc"); [|done|].
    { rewrite lookup_insert_ne //. move => ?. simplify_eq. }
    iIntros (v_t' v_s') "Hv' Hc". sim_val. source_store. sim_pures.
    iApply (sim_bij_release NaExcl with "Hy Hc [$] [$] Hr1"); [by simplify_map_eq| ].
    iIntros "Hc". rewrite delete_insert_id //. sim_val. iModIntro. by iFrame.
  Qed.
End reorderings.
