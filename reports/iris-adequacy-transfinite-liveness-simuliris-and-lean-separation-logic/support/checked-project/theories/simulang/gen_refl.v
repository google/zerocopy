(** * Lemmas for proving [log_rel]

    This file provides a set of lemmas for proving [gen_log_rel loc_rel
    thread_own] for arbitrary [loc_rel] and [thread_own] by exploiting
    the structure of the value relation. *)

From simuliris.simulation Require Import slsls lifting gen_log_rel.
From simuliris.simulang Require Import proofmode tactics.
From simuliris.simulang Require Import primitive_laws gen_val_rel wf.

Section log_rel.
  Context `{!sheapGS Σ} `{!sheapInv Σ}.
  (* TODO: can we avoid this boilerplate? It is repeated in all files that
     are generic over the logical relation details. *)
  Context (loc_rel : loc → loc → iProp Σ) {Hpers : ∀ l_t l_s, Persistent (loc_rel l_t l_s)}.
  Context (thread_own : thread_id → iProp Σ).
  Local Notation val_rel := (gen_val_rel loc_rel).
  Local Notation log_rel := (gen_log_rel val_rel thread_own).

  Lemma gen_log_rel_func x e_t e_s :
    (∀ v_t v_s π, ext_rel π v_t v_s ⊣⊢ thread_own π ∗ val_rel v_t v_s) →
    free_vars e_t ∪ free_vars e_s ⊆ {[x]} →
    log_rel e_t e_s -∗
    func_rel (x, e_t) (x, e_s).
  Proof.
    iIntros (Hext_val Hvars) "Hlog %v_t %v_s %π".
    rewrite Hext_val. iIntros "[Hthread Hval]".
    iApply (sim_wand with "[-]").
    - rewrite /= /apply_func /= -!subst_map_singleton.
      iApply (gen_log_rel_singleton with "Hlog Hval Hthread"); done.
    - setoid_rewrite Hext_val. eauto.
  Qed.

  Lemma val_wf_sound v : val_wf v → ⊢ val_rel v v.
  Proof.
    intros Hv.
    iInduction v as [[] | | | ] "IH"; try by (simpl; try iApply "IH").
    simpl. destruct Hv as [H1 H2]. iSplitL; [by iApply "IH" | by iApply "IH1"].
  Qed.

  Local Lemma call_not_val v1 v2 : language.to_val (Call v1 v2) = None.
  Proof.
    rewrite /language.to_val /language.to_class; cbn.
    destruct to_fname; [destruct to_val | ]; done.
  Qed.

  Lemma gen_val_rel_val_is_unboxed v_t v_s : val_rel v_t v_s -∗ ⌜val_is_unboxed v_t ↔ val_is_unboxed v_s⌝.
  Proof.
    iIntros "Hv".
    destruct v_s as [[] | |v_s|v_s]; try val_discr_source "Hv"; [ done.. | | |].
    - by iPoseProof (gen_val_rel_pair_source with "Hv") as (??) "(-> & Hv1 & Hv2)".
    - iPoseProof (gen_val_rel_injl_source with "Hv") as (?) "(-> & Hv)".
      destruct v_s as [[] | | | ]; try val_discr_source "Hv"; [done.. | | |].
      + by iPoseProof (gen_val_rel_pair_source with "Hv") as (??) "(-> & Hv1 & Hv2)".
      + by iPoseProof (gen_val_rel_injl_source with "Hv") as (?) "(-> & Hv)".
      + by iPoseProof (gen_val_rel_injr_source with "Hv") as (?) "(-> & Hv)".
    - iPoseProof (gen_val_rel_injr_source with "Hv") as (?) "(-> & Hv)".
      destruct v_s as [[] | | | ]; try val_discr_source "Hv"; [done.. | | |].
      + by iPoseProof (gen_val_rel_pair_source with "Hv") as (??) "(-> & Hv1 & Hv2)".
      + by iPoseProof (gen_val_rel_injl_source with "Hv") as (?) "(-> & Hv)".
      + by iPoseProof (gen_val_rel_injr_source with "Hv") as (?) "(-> & Hv)".
  Qed.

  Local Tactic Notation "smart_sim_bind" uconstr(ctx_t) uconstr(ctx_s) uconstr(Hp) :=
    sim_bind ctx_t ctx_s;
    iApply (sim_wand with Hp).

  Lemma log_rel_var x : ⊢ log_rel (Var x) (Var x).
  Proof.
    clear Hpers. rewrite /gen_log_rel.
    iIntros (? xs) "!# Hs Ht"; simpl.
    iDestruct (subst_map_rel_lookup _ x with "Hs") as (v_t v_s Hv) "Hrel"; first set_solver.
    rewrite !lookup_fmap Hv /=. sim_val. by iFrame.
  Qed.

  Lemma log_rel_let x e1_t e1_s e2_t e2_s :
    log_rel e1_t e1_s -∗ log_rel e2_t e2_s -∗ log_rel (Let x e1_t e2_t) (Let x e1_s e2_s).
  Proof using Hpers.
    rewrite /gen_log_rel.
    iIntros "#IH1 #IH2" (? xs) "!# #Hs Ht"; simpl.
    smart_sim_bind (subst_map _ _) (subst_map _ _) "(IH1 [Hs] Ht)".
    { iApply (subst_map_rel_weaken with "[$]"). set_solver. }
    iIntros (v_t v_s) "[Ht #Hv]". sim_pures. rewrite !subst'_subst_map.
    rewrite -(binder_insert_fmap fst (v_t, v_s)).
    rewrite -(binder_insert_fmap snd (v_t, v_s)).
    iApply ("IH2" with "[] Ht").
    iApply (subst_map_rel_insert with "[] [Hv]"); last done.
    iApply (subst_map_rel_weaken with "[$]").
    destruct x as [|x]; first set_solver.
    apply elem_of_subseteq=>x'.
    destruct (decide (x = x')) as [<-|Hne]; set_solver.
  Qed.

  Lemma log_rel_call e1_t e1_s e2_t e2_s :
    (∀ π v_t v_s, ext_rel π v_t v_s ⊣⊢ thread_own π ∗ val_rel v_t v_s) →
    log_rel e1_t e1_s -∗ log_rel e2_t e2_s -∗ log_rel (Call e1_t e2_t) (Call e1_s e2_s).
  Proof using Hpers.
    rewrite /gen_log_rel.
    iIntros (Hext) "#IH1 #IH2". iIntros (? xs) "!# #Hs Ht"; simpl.
    smart_sim_bind (subst_map _ _) (subst_map _ _) "(IH2 [] Ht)".
    { iApply (subst_map_rel_weaken with "[$]"). set_solver. }
    iIntros (v_t1 v_s1) "[Ht #Hv1]".
    smart_sim_bind (subst_map _ _) (subst_map _ _) "(IH1 [] Ht)".
    { iApply (subst_map_rel_weaken with "[$]"). set_solver. }
    iIntros (v_t2 v_s2) "[Ht #Hv2]".
    discr_source. val_discr_source "Hv2".
    iApply (sim_call with "[Ht]"); [done..| rewrite Hext; by iFrame| ].
    iIntros (??) "?". iApply lift_post_val. rewrite Hext. by iFrame.
  Qed.

  Lemma log_rel_unop e_t e_s o :
    log_rel e_t e_s -∗ log_rel (UnOp o e_t) (UnOp o e_s).
  Proof.
    clear Hpers. rewrite /gen_log_rel.
    iIntros "#IH" (? xs) "!# Hs Ht"; simpl.
    smart_sim_bind (subst_map _ e_t) (subst_map _ e_s) "(IH [Hs] Ht)".
    { iApply (subst_map_rel_weaken with "[$]"). set_solver. }
    iIntros (v_t v_s) "[Ht Hv]".
    destruct o; sim_pures; discr_source; val_discr_source "Hv"; sim_pures; sim_val; by iFrame.
  Qed.

  Lemma log_rel_binop e1_t e1_s e2_t e2_s o :
    loc_rel_func_law loc_rel →
    loc_rel_inj_law loc_rel →
    loc_rel_offset_law loc_rel →
    log_rel e1_t e1_s -∗ log_rel e2_t e2_s -∗ log_rel (BinOp o e1_t e2_t) (BinOp o e1_s e2_s).
  Proof using Hpers.
    rewrite /gen_log_rel.
    iIntros (Hfunc Hinj Hshift). iIntros "#IH1 #IH2" (? xs) "!# #Hs Ht"; simpl.
    smart_sim_bind (subst_map _ e2_t) (subst_map _ e2_s) "(IH2 [] Ht)".
    { iApply (subst_map_rel_weaken with "[$]"). set_solver. }
    iIntros (v_t2 v_s2) "[Ht Hv2]".
    smart_sim_bind (subst_map _ e1_t) (subst_map _ e1_s) "(IH1 [] Ht)".
    { iApply (subst_map_rel_weaken with "[$]"). set_solver. }
    iIntros (v_t1 v_s1) "[Ht Hv1]".
    destruct o; sim_pures; discr_source; try val_discr_source "Hv1"; try val_discr_source "Hv2"; sim_pures; try (sim_val; by iFrame); [| | |].
    - (* Quot *)
      source_binop.
      { rewrite /bin_op_eval /=. rewrite decide_False //. }
      target_binop.
      { rewrite /bin_op_eval /=. rewrite decide_False //. }
      sim_val; by iFrame.
    - (* Rem *)
      source_binop.
      { rewrite /bin_op_eval /=. rewrite decide_False //. }
      target_binop.
      { rewrite /bin_op_eval /=. rewrite decide_False //. }
      sim_val; by iFrame.
    - (* Eq *)
      iAssert (⌜vals_compare_safe v_t1 v_t2⌝)%I as "%".
      { iPoseProof (gen_val_rel_val_is_unboxed with "Hv1") as "%Hv1".
        iPoseProof (gen_val_rel_val_is_unboxed with "Hv2") as "%Hv2".
        iPureIntro. by rewrite /vals_compare_safe Hv1 Hv2.
      }
      sim_pures; sim_val. iFrame. case_bool_decide; subst.
      * iDestruct (gen_val_rel_func with "Hv1 Hv2") as %->; [done|]. by case_bool_decide.
      * case_bool_decide; [|done]; subst. by iDestruct (gen_val_rel_inj with "Hv1 Hv2") as %?.
    - (* Offset *)
      sim_val. iModIntro; simpl. iFrame. by iApply Hshift.
  Qed.

  Lemma log_rel_if e1_t e1_s e2_t e2_s e3_t e3_s :
    log_rel e1_t e1_s -∗
    log_rel e2_t e2_s -∗
    log_rel e3_t e3_s -∗
    log_rel (If e1_t e2_t e3_t) (If e1_s e2_s e3_s).
  Proof using Hpers.
    rewrite /gen_log_rel.
    iIntros "#IH1 #IH2 #IH3" (? xs) "!# #Hs Ht"; simpl.
    smart_sim_bind (subst_map _ e1_t) (subst_map _ e1_s) "(IH1 [] Ht)".
    { iApply (subst_map_rel_weaken with "[$]"). set_solver. }
    iIntros (v_t v_s) "[Ht Hv]".
    discr_source. val_discr_source "Hv". rename select bool into b.
    destruct b; sim_pures.
    + iApply ("IH2" with "[] Ht"). iApply (subst_map_rel_weaken with "[$]"). set_solver.
    + iApply ("IH3" with "[] Ht"). iApply (subst_map_rel_weaken with "[$]"). set_solver.
  Qed.

  Lemma log_rel_while e1_t e1_s e2_t e2_s :
    log_rel e1_t e1_s -∗
    log_rel e2_t e2_s -∗
    log_rel (While e1_t e2_t) (While e1_s e2_s).
  Proof using Hpers.
    rewrite /gen_log_rel.
    iIntros "#IH1 #IH2" (? xs) "!# #Hs Ht"; simpl.
    iApply (sim_while_while (thread_own _)%I with "[$]").
    iModIntro; iIntros "Ht".
    smart_sim_bind (subst_map _ e1_t) (subst_map _ e1_s) "(IH1 [] Ht)".
    { iApply (subst_map_rel_weaken with "[$]"). set_solver. }
    iIntros (v_t v_s) "[Ht Hv]".
    discr_source. val_discr_source "Hv".
    rename select bool into b.
    destruct b; sim_pures.
    + smart_sim_bind (subst_map _ e2_t) (subst_map _ e2_s) "(IH2 [] Ht)".
      { iApply (subst_map_rel_weaken with "[$]"). set_solver. }
      iIntros (? ?) "[Ht _]"; sim_pures. iApply sim_expr_base. iRight. by eauto.
    + iApply sim_expr_base. iLeft. iExists #(), #(); eauto.
  Qed.

  Lemma log_rel_pair e1_t e1_s e2_t e2_s :
    log_rel e1_t e1_s -∗
    log_rel e2_t e2_s -∗
    log_rel (Pair e1_t e2_t) (Pair e1_s e2_s).
  Proof using Hpers.
    rewrite /gen_log_rel.
    iIntros "#IH1 #IH2" (? xs) "!# #Hs Ht"; simpl.
    smart_sim_bind (subst_map _ e2_t) (subst_map _ e2_s) "(IH2 [] Ht)".
    { iApply (subst_map_rel_weaken with "[$]"). set_solver. }
    iIntros (v_t2 v_s2) "[Ht Hv2]".
    smart_sim_bind (subst_map _ e1_t) (subst_map _ e1_s) "(IH1 [] Ht)".
    { iApply (subst_map_rel_weaken with "[$]"). set_solver. }
    iIntros (v_t1 v_s1) "[Ht Hv1]".
    sim_pures; sim_val. by iFrame.
  Qed.

  Lemma log_rel_fst e_t e_s :
    log_rel e_t e_s -∗ log_rel (Fst e_t) (Fst e_s).
  Proof.
    clear Hpers. rewrite /gen_log_rel.
    iIntros "#IH" (? xs) "!# Hs Ht"; simpl.
    smart_sim_bind (subst_map _ e_t) (subst_map _ e_s) "(IH [Hs] Ht)".
    { iApply (subst_map_rel_weaken with "[$]"). set_solver. }
    iIntros (v_t v_s) "[Ht Hv]".
    discr_source.
    iPoseProof (gen_val_rel_pair_source with "Hv") as (??) "(-> & ? & ?)"; sim_pures; sim_val; by iFrame.
  Qed.
  Lemma log_rel_snd e_t e_s :
    log_rel e_t e_s -∗ log_rel (Snd e_t) (Snd e_s).
  Proof.
    clear Hpers. rewrite /gen_log_rel.
    iIntros "#IH" (? xs) "!# Hs Ht"; simpl.
    smart_sim_bind (subst_map _ e_t) (subst_map _ e_s) "(IH [Hs] Ht)".
    { iApply (subst_map_rel_weaken with "[$]"). set_solver. }
    iIntros (v_t v_s) "[Ht Hv]".
    discr_source.
    iPoseProof (gen_val_rel_pair_source with "Hv") as (??) "(-> & ? & ?)"; sim_pures; sim_val; by iFrame.
  Qed.

  Lemma log_rel_injl e_t e_s :
    log_rel e_t e_s -∗ log_rel (InjL e_t) (InjL e_s).
  Proof using Hpers.
    rewrite /gen_log_rel.
    iIntros "#IH" (? xs) "!# #Hs Ht"; simpl.
    smart_sim_bind (subst_map _ e_t) (subst_map _ e_s) "(IH [] Ht)".
    { iApply (subst_map_rel_weaken with "[$]"). set_solver. }
    iIntros (v_t v_s) "[Ht Hv]"; sim_pures; sim_val; by iFrame.
  Qed.
  Lemma log_rel_injr e_t e_s :
    log_rel e_t e_s -∗ log_rel (InjR e_t) (InjR e_s).
  Proof using Hpers.
    rewrite /gen_log_rel.
    iIntros "#IH" (? xs) "!# #Hs Ht"; simpl.
    smart_sim_bind (subst_map _ e_t) (subst_map _ e_s) "(IH [] Ht)".
    { iApply (subst_map_rel_weaken with "[$]"). set_solver. }
    iIntros (v_t v_s) "[Ht Hv]"; sim_pures; sim_val; by iFrame.
  Qed.

  Lemma log_rel_match e_t e_s e1_t e1_s e2_t e2_s x1 x2 :
    log_rel e_t e_s -∗
    log_rel e1_t e1_s -∗
    log_rel e2_t e2_s -∗
    log_rel (Match e_t x1 e1_t x2 e2_t) (Match e_s x1 e1_s x2 e2_s).
  Proof using Hpers.
    rewrite /gen_log_rel.
    iIntros "#IH #IH1 #IH2" (? xs) "!# #Hs Ht"; simpl.
    smart_sim_bind (subst_map _ e_t) (subst_map _ e_s)  "(IH [] Ht)".
    { iApply (subst_map_rel_weaken with "[$]"). set_solver. }
    iIntros (v_t v_s) "[Ht #Hv]".
    discr_source.
    + iPoseProof (gen_val_rel_injl_source with "Hv") as (v_t') "(-> & ?)". sim_pures.
      rewrite !subst'_subst_map.
      match goal with |- context[gen_val_rel loc_rel (InjLV ?vt) (InjLV ?vs)] =>
        rename vt into v_t'; rename vs into v_s'
      end.
      rewrite -(binder_insert_fmap fst (v_t', v_s')).
      rewrite -(binder_insert_fmap snd (v_t', v_s')).
      iApply ("IH1" with "[] Ht").
      iApply (subst_map_rel_insert with "[] []"); last done.
      iApply (subst_map_rel_weaken with "[$]").
      destruct x1 as [|x1]; first set_solver.
      apply elem_of_subseteq=>x'.
      destruct (decide (x1 = x')) as [<-|Hne]; set_solver.
    + iPoseProof (gen_val_rel_injr_source with "Hv") as (v_t') "(-> & ?)". sim_pures.
      rewrite !subst'_subst_map.
      match goal with |- context[gen_val_rel loc_rel (InjRV ?vt) (InjRV ?vs)] =>
        rename vt into v_t'; rename vs into v_s'
      end.
      rewrite -(binder_insert_fmap fst (v_t', v_s')).
      rewrite -(binder_insert_fmap snd (v_t', v_s')).
      iApply ("IH2" with "[] Ht").
      iApply (subst_map_rel_insert with "[] []"); last done.
      iApply (subst_map_rel_weaken with "[$]").
      destruct x2 as [|x2]; first set_solver.
      apply elem_of_subseteq=>x'.
      destruct (decide (x2 = x')) as [<-|Hne]; set_solver.
  Qed.

  Lemma log_rel_fork e_t e_s :
    (∀ e_s e_t π Ψ,
     thread_own π -∗
     (thread_own π -∗ #() ⪯{π} #() [{ Ψ }]) -∗
     (∀ π', thread_own π' -∗ e_t ⪯{π'} e_s {{ λ v_t v_s, thread_own π' ∗ val_rel v_t v_s }}) -∗
     Fork e_t ⪯{π} Fork e_s [{ Ψ }]) →
    log_rel e_t e_s -∗ log_rel (Fork e_t) (Fork e_s).
  Proof using Hpers.
    rewrite /gen_log_rel.
    iIntros (Hfork). iIntros "#IH" (? xs) "!# #Hs Ht"; simpl.
    iApply (Hfork with "Ht"); first by iIntros "?"; sim_pures; sim_val; iFrame.
    iIntros (?) "Ht". iApply (sim_wand with "(IH [] Ht)"); eauto.
  Qed.

  Lemma log_rel_allocN e1_t e1_s e2_t e2_s :
    (∀ (n : Z) v_t v_s π Ψ, (0 < n)%Z →
     thread_own π -∗ val_rel v_t v_s -∗
     (∀ l_t l_s, thread_own π -∗ loc_rel l_t l_s -∗ #l_t ⪯{π} #l_s [{ Ψ }]) -∗
     AllocN #n v_t ⪯{π} AllocN #n v_s [{ Ψ }]) →
    log_rel e1_t e1_s -∗ log_rel e2_t e2_s -∗ log_rel (AllocN e1_t e2_t) (AllocN e1_s e2_s).
  Proof using Hpers.
    rewrite /gen_log_rel.
    iIntros (Halloc). iIntros "#IH1 #IH2" (? xs) "!# #Hs Ht"; simpl.
    smart_sim_bind (subst_map _ e2_t) (subst_map _ e2_s) "(IH2 [] Ht)".
    { iApply (subst_map_rel_weaken with "[$]"). set_solver. }
    iIntros (v_t v_s) "[Ht Hv]".
    smart_sim_bind (subst_map _ e1_t) (subst_map _ e1_s) "(IH1 [] Ht)".
    { iApply (subst_map_rel_weaken with "[$]"). set_solver. }
    iIntros (v_t' v_s') "[Ht Hv']".
    discr_source. val_discr_source "Hv'".
    iApply (Halloc with "Ht Hv"); [done|].
    iIntros (l_t l_s) "Ht Hl". sim_val. by iFrame.
  Qed.

  Lemma log_rel_freeN e1_t e1_s e2_t e2_s :
    (∀ (n : Z) l_t l_s π Ψ, (0 < n)%Z →
     thread_own π -∗ loc_rel l_t l_s -∗
     (thread_own π -∗ #() ⪯{π} #() [{ Ψ }]) -∗
     FreeN #n #l_t ⪯{π} FreeN #n #l_s [{ Ψ }]) →
    log_rel e1_t e1_s -∗ log_rel e2_t e2_s -∗ log_rel (FreeN e1_t e2_t) (FreeN e1_s e2_s).
  Proof using Hpers.
    rewrite /gen_log_rel.
    iIntros (Hfree). iIntros "#IH1 #IH2" (? xs) "!# #Hs Ht"; simpl.
    smart_sim_bind (subst_map _ _) (subst_map _ _) "(IH2 [] Ht)".
    { iApply (subst_map_rel_weaken with "[$]"). set_solver. }
    iIntros (v_t v_s) "[Ht Hv]".
    smart_sim_bind (subst_map _ _) (subst_map _ _) "(IH1 [] Ht)".
    { iApply (subst_map_rel_weaken with "[$]"). set_solver. }
    iIntros (v_t' v_s') "[Ht Hv']".
    discr_source. iPoseProof (gen_val_rel_loc_source with "Hv") as (l_t) "(-> & Hrel)".
    iPoseProof (gen_val_rel_litint_source with "Hv'") as "->".
    iApply (Hfree with "Ht Hrel"); [done|].
    iIntros "Ht". sim_val. by iFrame.
  Qed.

  Lemma log_rel_load o e_t e_s :
    (∀ l_t l_s π Ψ,
     thread_own π -∗ loc_rel l_t l_s -∗
     (∀ v_t v_s, thread_own π -∗ val_rel v_t v_s -∗ v_t ⪯{π} v_s [{ Ψ }]) -∗
     Load o #l_t ⪯{π} Load o #l_s [{ Ψ }]) →
    log_rel e_t e_s -∗ log_rel (Load o e_t) (Load o e_s).
  Proof using Hpers.
    rewrite /gen_log_rel.
    iIntros (Hload). iIntros "#IH" (? xs) "!# #Hs Ht"; simpl.
    smart_sim_bind (subst_map _ _) (subst_map _ _) "(IH [] Ht)".
    { iApply (subst_map_rel_weaken with "[$]"). set_solver. }
    iIntros (v_t v_s) "[Ht Hv]". discr_source.
    iPoseProof (gen_val_rel_loc_source with "Hv") as (l_t) "(-> & Hrel)".
    iApply (Hload with "Ht Hrel").
    iIntros (v_t v_s) "Ht Hrel". sim_val; by iFrame.
  Qed.

  Lemma log_rel_store o e1_t e1_s e2_t e2_s :
    (∀ l_t l_s v_s v_t π Ψ,
     thread_own π -∗ loc_rel l_t l_s -∗ val_rel v_t v_s -∗
     (thread_own π -∗ #() ⪯{π} #() [{ Ψ }]) -∗
     Store o #l_t v_t ⪯{π} Store o #l_s v_s [{ Ψ }]) →
    log_rel e1_t e1_s -∗ log_rel e2_t e2_s -∗ log_rel (Store o e1_t e2_t) (Store o e1_s e2_s).
  Proof using Hpers.
    rewrite /gen_log_rel.
    iIntros (Hstore). iIntros "#IH1 #IH2" (? xs) "!# #Hs Ht"; simpl.
    smart_sim_bind (subst_map _ _) (subst_map _ _) "(IH2 [] Ht)".
    { iApply (subst_map_rel_weaken with "[$]"). set_solver. }
    iIntros (v_t v_s) "[Ht Hv]". (* FIXME: fix printing *)
    smart_sim_bind (subst_map _ _) (subst_map _ _) "(IH1 [] Ht)".
    { iApply (subst_map_rel_weaken with "[$]"). set_solver. }
    iIntros (v_t' v_s') "[Ht Hv']".
    discr_source. iPoseProof (gen_val_rel_loc_source with "Hv'") as (l_t) "(-> & Hrel)".
    iApply (Hstore with "Ht Hrel Hv").
    iIntros "Ht". sim_val; by iFrame.
  Qed.

  Lemma log_rel_val v_t v_s :
    val_rel v_t v_s -∗ log_rel (Val v_t) (Val v_s).
  Proof using Hpers.
    rewrite /gen_log_rel.
    iIntros "#Hv" (? xs) "!# Hs Ht"; simpl. sim_val; by iFrame.
  Qed.
End log_rel.
