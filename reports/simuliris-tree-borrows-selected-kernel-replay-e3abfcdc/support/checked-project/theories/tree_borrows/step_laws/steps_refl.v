From iris.proofmode Require Export proofmode.
From iris.base_logic.lib Require Import ghost_map.
From simuliris.base_logic Require Export gen_sim_prog.
From simuliris.simulation Require Export slsls.
From simuliris.simulation Require Import lifting.
From simuliris.tree_borrows Require Import tkmap_view.
From simuliris.tree_borrows Require Export defs class_instances.
From simuliris.tree_borrows Require Import wishlist steps_progress steps_inv.
From simuliris.tree_borrows Require Import logical_state inv_accessors.
From simuliris.tree_borrows.trees_equal Require Import trees_equal_base random_lemmas.
From simuliris.tree_borrows.trees_equal Require Import trees_equal_initcall.

Section lifting.
Context `{!sborGS Σ}.
Implicit Types P Q : iProp Σ.
Implicit Types Φ : expr → expr → iProp Σ.
Implicit Types σ σ_s σ_t : state.
Implicit Types r r_s r_t : result.
Implicit Types l : loc.
Implicit Types f : fname.


Lemma sim_alloc_public T Φ π :
  (∀ t l, t $$ tk_pub -∗
    rrel (PlaceR l (t) T) (PlaceR l (t) T) -∗
    Place l (t) T ⪯{π} Place l (t) T [{ Φ }]) -∗
  Alloc T ⪯{π} Alloc T [{ Φ }].
Proof.
  iIntros "Hsim".
  iApply sim_lift_base_step_both. iIntros (P_t P_s σ_t σ_s ??) "[(HP_t & HP_s & Hbor) %Hsafe]".
  iModIntro.
  destruct Hsafe as [Hpool Hsafe].
  specialize (pool_safe_implies Hsafe Hpool) as Hnonzero.
  iPoseProof (bor_interp_get_pure with "Hbor") as "%Hp".
  destruct Hp as (Hstrs_eq & Hsnp_eq & Hsnc_eq & Hscs_eq & Hwf_s & Hwf_t & Hdom_eq).
  iSplitR. { iPureIntro. do 3 eexists. eapply alloc_base_step; assumption. }
  iIntros (e_t' efs_t σ_t') "%Hhead_t".
  specialize (head_alloc_inv _ _ _ _ _ _ Hhead_t) as (_ & -> & -> & ->).

  (* allocate tag *)
  iDestruct "Hbor" as "(%M_call & %M_tag & %M_t & %M_s & (Hc & Htag_auth & Htag_t_auth & Htag_s_auth) & Htainted & Hpub_cid & #Hsrel & %Hcall_interp & %Htag_interp & _ & _)".
  assert (M_tag !! (σ_t.(snp)) = None) as HNone.
  { destruct (M_tag !! (σ_t.(snp))) as [[tk' []] | ] eqn:Hs; last done. exfalso.
    apply Htag_interp in Hs as (_ & H & _). unfold tag_valid in H. lia.
  }
  iMod (tkmap_insert tk_pub (σ_t.(snp)) () ltac:(done) with "Htag_auth") as "[Htag_auth #Ht]".
  iModIntro.
  pose (blk := (fresh_block σ_t.(shp))). (* can be σ_s and σ_t, it does not matter. *)
  pose (l := (blk, 0)). pose (nt := σ_t.(snp)).
  pose (α_t' := extend_trees ((snp σ_t)) blk 0 T (strs σ_t)).
  pose (α_s' := extend_trees ((snp σ_s)) blk 0 T (strs σ_s)).
  pose (σ_t' := (mkState (init_mem l T σ_t.(shp)) α_t' σ_t.(scs) (S σ_t.(snp)) σ_t.(snc))).
  pose (σ_s' := (mkState (init_mem l T σ_s.(shp)) α_s' σ_s.(scs) (S σ_s.(snp)) σ_s.(snc))).
  assert (Hhead_s : base_step P_s (Alloc T) σ_s (Place l (nt) T) σ_s' []).
  { subst σ_s' nt α_s' blk l. rewrite -Hsnp_eq -(fresh_block_det σ_s σ_t); last done.
    eapply alloc_base_step; assumption.
  }
  iExists _, [], _. iSplitR; first done. simpl. iFrame "HP_t HP_s".
  iSplitR "Hsim Ht"; first last.
  { iSplitL; last done. subst nt l blk. iApply ("Hsim" with "Ht").
    iFrame "Ht". done.
  }
  (* re-establish the invariants *)
  iExists M_call, (<[nt := (tk_pub, ())]> M_tag), M_t, M_s.
  iFrame "Hc Htag_auth Htag_t_auth Htag_s_auth".
  iSplitL "Htainted"; last iSplitL "Hpub_cid"; last iSplit; last iSplit; last iSplit; last iSplit.
  - iDestruct "Htainted" as "(%M&Ht1&Ht2)". iExists M. iFrame "Ht1".
    iIntros (t' l' Htl'). iDestruct ("Ht2" $! t' l' Htl') as "($&%Ht2)". iPureIntro.
    destruct Ht2 as (Hlt&Ht2); split. 1: simpl; lia.
    rewrite /= /α_s' /= /extend_trees /=. destruct (decide (l'.1 = blk)) as [<-|Hf].
    + rewrite lookup_insert_eq. right. intros Hc%init_tree_contains_only. lia.
    + rewrite lookup_insert_ne //.
  - (* pub cid *)
    iApply (pub_cid_interp_preserve_sub with "Hpub_cid"); simpl; done.
    (* state rel *) 
  - iSplit; last iSplit; last iSplit; last iSplit; last iSplit.
    + cbn. iPureIntro. rewrite init_mem_dom. rewrite (init_mem_dom _ _ (shp σ_t)).
      f_equal. apply Hdom_eq.
    + iPureIntro. subst α_s'. cbn. rewrite Hsnp_eq. eapply trees_equal_init_trees. done.
    + iPureIntro. cbn. by rewrite Hsnp_eq.
    + iPureIntro. cbn. by rewrite Hsnc_eq.
    + iPureIntro. cbn. by rewrite Hscs_eq. 
    + simpl. fold blk. iIntros ((blk'&off') [sc Hsc]).
      apply init_mem_lookup_fresh_inv in Hsc as Hsc'; last eapply is_fresh_block.
      destruct Hsc' as [([= ->] & -> & Hpos & Hlt)|[([=] & _)|(Hthru&Hne)]].
      * iLeft. iIntros (sc_t Hlu).
        rewrite Hsc in Hlu.
        injection Hlu as <-. 
        iExists ScPoison. iSplit; last done. iPureIntro.
        rewrite init_mem_lookup_fresh_poison //. 
      * iDestruct "Hsrel" as "(_&_&_&_&_&Hsrel)".
        unshelve iDestruct ("Hsrel" $! (blk', off') _) as "[Hsrel2|%Hpriv]".
        -- by eexists. 
        -- iLeft. iIntros (sc_t Hsc_t). cbn in Hsc_t.
           rewrite Hsc Hthru in Hsc_t.
           iDestruct ("Hsrel2" $! sc_t Hsc_t) as (sc_s Hsc_s) "Hsrel3".
           iExists (sc_s). subst σ_s'. cbn. rewrite init_mem_lookup_fresh_old; last done.
           iFrame "Hsrel3". done.
        -- iRight. iPureIntro. destruct Hpriv as (tg & tk & HtagSome & HSome & Hcases).
           exists tg, tk. split_and!; [|done..].
           rewrite lookup_insert_ne; first done.
           intros <-. by rewrite HNone in HtagSome.
  - (* call interp *) 
    iPureIntro.
    destruct Hcall_interp as (Hcall_interp&Hcc2). split; last first.
    1: done.
    intros c M Hc. simpl. specialize (Hcall_interp c M Hc) as (Hc1 & Hc2).
    split; first done. intros t L Ht.
    specialize (Hc2 t L Ht) as (Hc3 & Hc4).
    split.
    { eapply tag_valid_mono; try done; lia. }
    intros l' b' Hl'. specialize (Hc4 l' b' Hl').
    destruct b'.
    + intros it (tr&Htr&Hit). simpl. rewrite /tag_protected_for in Hc4.
      assert (trees_lookup (strs σ_t) l'.1 t it) as Hlu.
      { exists tr; split; last done. rewrite /extend_trees in Htr.
        eapply lookup_insert_Some in Htr as [(Htr1&Htr2)|(Htr1&Htr2)]; last done.
        subst tr. destruct Hit as (H1&H2). eapply init_tree_contains_only in H1. subst t.
        rewrite /tag_valid in Hc3. lia. }
      specialize (Hc4 _ Hlu). split_and!; try by eapply Hc4. done.
    + eapply tag_protected_for_mono in Hc4.
      1: destruct Hc4 as (it & Hit & Hperm).
      1: exists it; split; last done.
      2: { intros l'' it ? ? ? (tk&Htk&Hhl). exists tk. split; last done.
           rewrite lookup_insert_ne //. subst nt. intros Heq.
           by rewrite -Heq HNone in Htk. }
      destruct Hit as (trr&Hit1&Hit2); eexists; split; last done.
      rewrite /extend_trees lookup_insert_ne //.
      intros Heq. rewrite -Heq in Hit1.
      eapply elem_of_dom_2 in Hit1.
      rewrite state_wf_dom // in Hit1.
      by eapply is_fresh_block_fst in Hit1.
  - (* tag interp *)
    iPureIntro. destruct Htag_interp as (Htag_interp & Hdom_t & Hdom_s & Hunq1 & Hunq2). split_and!.
    { simpl. intros tr tk. rewrite lookup_insert_Some. intros [[<- [= <-]] | [Hneq Hsome]].
      - (* new tag: as these are public, the locations under this tag are not directly controlled *)
        split_and!; [ rewrite /tag_valid; lia | rewrite /tag_valid; lia | | | |].
        + intros ?; done.
        + intros l' sc_t (?&?&?)%bind_Some. exfalso. specialize (Hdom_t nt l'.1 ltac:(eauto)) as (? &?). subst nt. congruence.
        + intros l' sc_t (?&?&?)%bind_Some. exfalso. specialize (Hdom_s nt l'.1 ltac:(eauto)) as (? &?). subst nt. congruence.
        + apply dom_agree_on_tag_not_elem.
          * intros l'. destruct heaplet_lookup eqn:Hs; last done.
            eapply bind_Some in Hs as (?&?&?).
            destruct (Hdom_t nt l'.1 ltac:(eauto)) as (? & ?).
            subst nt. congruence.
          * intros l'. destruct heaplet_lookup eqn:Hs; last done.
            eapply bind_Some in Hs as (?&?&?).
            destruct (Hdom_s nt l'.1 ltac:(eauto)) as (? & ?).
            subst nt. congruence.
      - (* old tag *)
        specialize (Htag_interp _ _ Hsome) as (Hv1 & Hv2 & Hlocal & Hcontrol_t & Hcontrol_s & Hag).
        split_and!; [inversion Hv1; simplify_eq; econstructor; lia | inversion Hv1; simplify_eq; econstructor; lia | .. | done].
        + intros ->. split; intros bblk MM Hbblk.
          all: specialize (Hlocal eq_refl) as (HH1&HH2).
          * by eapply HH1. (* specialize (HH1 _ _ Hbblk). rewrite /trees_contain /trees_at_block in HH1|-*.
            destruct (strs σ_t !! bblk) as [tt|] eqn:HH; last done.
            erewrite extend_trees_preserve. 1: eapply HH1. all: done. *)
          * by eapply HH2. (* specialize (HH2 _ Hbblk). rewrite /trees_contain /trees_at_block in HH2|-*.
            destruct (strs σ_s !! bblk) as [tt|] eqn:HH; last done. subst α_s'.
            subst blk. erewrite fresh_block_equiv. 2: by rewrite -Hdom_eq.
            erewrite extend_trees_preserve. 1: eapply HH2. all: done. *)
        + intros l' sc_t Hcontrol%Hcontrol_t. clear Hhead_s. eapply loc_controlled_alloc_update; done.
        + intros l' sc_s Hcontrol%Hcontrol_s. clear α_t' σ_t' Hhead_s. subst σ_s' α_s' l blk.
          erewrite fresh_block_det; last done.
          eapply loc_controlled_alloc_update; try done.
          by rewrite Hsnp_eq.
    }
    { intros t l'. rewrite lookup_insert_is_Some'. eauto. }
    { intros t l'. rewrite lookup_insert_is_Some'. eauto. }
    { done. }
    { done. }
  - iPureIntro. by eapply base_step_wf.
  - iPureIntro. by eapply base_step_wf.
Qed.

(** InitCall *)

Lemma bor_interp_init_call σ_t σ_s :
  bor_interp sc_rel σ_t σ_s ==∗
  σ_t.(snc) @@ ∅ ∗
  bor_interp sc_rel
    (mkState σ_t.(shp) σ_t.(strs) ({[ σ_t.(snc) ]} ∪ σ_t.(scs)) σ_t.(snp) (S σ_t.(snc)))
    (mkState σ_s.(shp) σ_s.(strs) ({[ σ_s.(snc) ]} ∪ σ_s.(scs)) σ_s.(snp) (S σ_s.(snc))).
Proof.
  iIntros "(%M_call & %M_tag & %M_t & %M_s & (Hc & Htag_auth & Htag_t_auth & Htag_s_auth) & Htainted & Hpub_cid & #Hsrel & %Hcall_interp & %Htag_interp & %Hwf_s & %Hwf_t)".
  iPoseProof (state_rel_snc_eq with "Hsrel") as "%Hsnc_eq".
  assert (M_call !! σ_t.(snc) = None) as Hfresh.
  { destruct (M_call !! σ_t.(snc)) as [ M' | ] eqn:HM'; last done. apply Hcall_interp in HM' as (Hin & _).
    apply Hwf_t in Hin. lia. }
  iMod (ghost_map_insert σ_t.(snc) ∅ Hfresh with "Hc") as "[Hc Hcall]".
  iModIntro. iFrame "Hcall".
  iExists (<[σ_t.(snc) := ∅]> M_call), M_tag, M_t, M_s. iFrame.
  iSplitL "Htainted".
  { iDestruct "Htainted" as "(%M&Ht1&Ht2)". iExists M. iFrame "Ht1".
    iIntros (t' l' Htl'). iDestruct ("Ht2" $! t' l' Htl') as "($&%Ht2)". iPureIntro. simpl.
    rewrite union_comm_L. eapply disabled_tag_mono. done. }
  iSplitL "Hpub_cid".
  { (* pub cid *) iApply (pub_cid_interp_preserve_initcall with "Hpub_cid"); done. }
  iSplitL.
  { iDestruct "Hsrel" as "(H1 & %H2 & %H3 & %H4 & %H5 & H6)". rewrite /state_rel. simpl.
    iFrame "H1".
    iSplit. { iPureIntro. rewrite union_comm_L. eapply trees_equal_mono; last done.
              + apply Hwf_s. + rewrite H3. rewrite H4. apply Hwf_t.
              + apply Hwf_s. + apply Hwf_t. }
    iSplit. { iPureIntro. lia. }
    iSplit. { rewrite Hsnc_eq. done. }
    iSplit. { iPureIntro. rewrite H4. rewrite H5. reflexivity. }
    iIntros (l Hl). iDestruct ("H6" $! l with "[//]") as "[Hpub | (%t & %Hpriv)]".
    - iLeft. iApply "Hpub".
    - iRight. iPureIntro. exists t.
      destruct Hpriv as (tk & Htk & Hs & [-> | (c' & ae & -> & Hin)]).
      { exists tk_local. split_and!; eauto. }
      exists (tk_unq tk_act). split_and!; [done.. | ]. right. exists c', ae. split; first done.
      destruct Hin as (M' & HM' & Hin). exists M'.
      split; last done. apply lookup_insert_Some. right. split; last done.
      apply Hcall_interp in HM' as (Hwf_tag & _).
      specialize (state_wf_cid_agree _ Hwf_t _ Hwf_tag). lia.
  }
  iSplitL.
  { iPureIntro.
    destruct Hcall_interp as (Hcall_interp&Hcc2). split; last first.
    { intros ????? [(?&?)|(?&?)]%lookup_insert_Some [(?&?)|(?&?)]%lookup_insert_Some; simplify_eq.
      4: by eapply Hcc2. all: rewrite dom_empty_L. all: intros ??; exfalso; unshelve eapply elem_of_empty. 25-27: done. all: done. }
    intros c M'. simpl. rewrite lookup_insert_Some. intros [(<- & <-) | [Hneq Hsome]].
    - split; first set_solver. intros ? ?. rewrite lookup_empty. congruence.
    - rewrite elem_of_union. apply Hcall_interp in Hsome as [Hin Ha]. split; [by eauto | done].
  }
  iSplitL.
  { iPureIntro. destruct Htag_interp as (H1&H2&H3&H4&H5). split; last done.
    intros t tk (H6&H7&Hlocal&Hl&Hr&H8)%H1. split_and!; try done.
    - intros l sc H%Hl. eapply loc_controlled_add_protected; last done; try done.
      intros blk tg it c (tr&Htr1&Htr2) Hpp. simpl.
      rewrite /call_is_active. split; first set_solver.
      intros [Heq%elem_of_singleton|?]%elem_of_union; last set_solver.
      pose proof (state_wf_tree_compat _ Hwf_t blk tr Htr1) as Hitems.
      setoid_rewrite every_node_iff_every_lookup in Hitems.
      2: by eapply wf_tree_tree_item_determined, Hwf_t.
      apply Hitems in Htr2. eapply (item_cid_valid _ _ _ Htr2) in Hpp. lia.
    - intros l sc H%Hr. eapply loc_controlled_add_protected; last done; try done.
      intros blk tg it c (tr&Htr1&Htr2) Hpp. simpl.
      rewrite /call_is_active. split; first set_solver.
      intros [Heq%elem_of_singleton|?]%elem_of_union; last set_solver.
      pose proof (state_wf_tree_compat _ Hwf_s blk tr Htr1) as Hitems.
      setoid_rewrite every_node_iff_every_lookup in Hitems.
      2: by eapply wf_tree_tree_item_determined, Hwf_s.
      apply Hitems in Htr2. eapply (item_cid_valid _ _ _ Htr2) in Hpp. lia.
     }
  iSplit; iPureIntro.
  all: by eapply initcall_step_wf_inner.
Qed.

Lemma sim_init_call π Φ :
  (∀ c, c @@ ∅ -∗
    #[ScCallId c] ⪯{π} #[ScCallId c] [{ Φ }]) -∗
  InitCall ⪯{π} InitCall [{ Φ }].
Proof.
  iIntros "Hsim". iApply sim_lift_base_step_both. iIntros (P_t P_s σ_t σ_s T_s K_s) "((HP_t & HP_s & Hbor) & _ & _)".
  iPoseProof (bor_interp_get_pure with "Hbor") as "%Hp".
  iMod (bor_interp_init_call with "Hbor") as "[Hc Hbor]". iModIntro.
  iSplitR.
  { iPureIntro. do 3 eexists. eapply init_call_base_step. }
  iIntros (e_t' efs_t σ_t') "%Hhead".
  specialize (head_init_call_inv _ _ _ _ _ Hhead) as (c & Heqc & -> & -> & ->).
  iModIntro. iExists (#[ScCallId σ_s.(snc)])%E, [], (mkState σ_s.(shp) σ_s.(strs) ({[ σ_s.(snc) ]} ∪ σ_s.(scs)) σ_s.(snp) (S σ_s.(snc))).
  iSplitR. { iPureIntro. eapply init_call_base_step. }
  iSplitR "Hsim Hc"; first last.
  { iSplitL; last done. destruct Hp as (_ & _ & Heqc' & _). rewrite Heqc Heqc'. by iApply "Hsim". }
  iFrame.
Qed.

Lemma sim_cid_make_public c e_t e_s π Φ :
  c @@ ∅ -∗
  (sc_rel (ScCallId c) (ScCallId c) -∗ e_t ⪯{π} e_s [{ Φ }]) -∗
  e_t ⪯{π} e_s [{ Φ }].
Proof.
  iIntros "Hown Hsim". iApply sim_update_si. iIntros (P_t σ_t P_s σ_s T_s) "(HP_t & HP_s & Hbor)".
  iDestruct "Hbor" as "(%M_call & %M_tag & %M_t & %M_s & (Hc & Htag_auth & Htag_t_auth & Htag_s_auth) & Htag_interp & Hpub_cid & #Hsrel & %Hcall_interp & %Htag_interp & %Hwf_s & %Hwf_t)".
  iMod (call_id_make_public with "Hpub_cid Hown") as "[#Hpub Hpub_cid]".
  iModIntro. iSplitR "Hsim".
  { iFrame "HP_t HP_s". iExists M_call, M_tag, M_t, M_s. iFrame. eauto. }
  iApply "Hsim".
  simpl. eauto.
Qed.

(** Call *)
Lemma sim_call fn (r_t r_s : result) π Φ :
  rrel r_t r_s -∗
  (∀ r_t r_s : result, rrel r_t r_s -∗ Φ (of_result r_t) (of_result r_s)) -∗
  Call #[ScFnPtr fn] r_t ⪯{π} Call #[ScFnPtr fn] r_s [{ Φ }].
Proof.
  iIntros "Hval Hsim". iApply (sim_lift_call _ fn r_t r_s with "[Hval]"); first done. by iApply "Hsim".
Qed.

(** Coinduction on while loops *)
Lemma sim_while_while inv c_t c_s b_t b_s π Ψ :
  inv -∗
  □ (inv -∗
      (if: c_t then b_t ;; while: c_t do b_t od else #[☠])%E ⪯{π}
      (if: c_s then b_s ;; while: c_s do b_s od else #[☠])%E
        [{ λ e_t e_s, Ψ e_t e_s ∨ (⌜e_t = while: c_t do b_t od%E⌝ ∗ ⌜e_s = while: c_s do b_s od%E⌝ ∗ inv) }]) -∗
  (while: c_t do b_t od ⪯{π} while: c_s do b_s od [{ Ψ }])%E.
Proof.
  iIntros "Hinv_init #Hstep".
  iApply (sim_lift_coind_pure inv with "[] Hinv_init");
    [apply pure_while | apply pure_while | done.. ].
Qed.


(** fork *)
Lemma sim_fork π e_t e_s Ψ :
  #[☠] ⪯{π} #[☠] [{ Ψ }] -∗
  (∀ π', e_t ⪯{π'} e_s {{ rrel }}) -∗
  Fork e_t ⪯{π} Fork e_s [{ Ψ }].
Proof.
  iIntros "Hval Hsim". iApply sim_lift_base_step_both.
  iIntros (??????) "[Hstate [% %]] !>".
  iSplitR. { iPureIntro. eexists _, _, _. econstructor. econstructor. }
  iIntros (e_t' efs_t σ_t') "%"; inv_base_step.
  iModIntro. iExists _, _, _. iSplitR. { iPureIntro. econstructor. econstructor. }
  simpl. iFrame. iSplitL; last done.
  iApply "Hsim".
Qed.

End lifting.


