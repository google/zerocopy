From iris.proofmode Require Export proofmode.
From iris.base_logic.lib Require Import ghost_map.
From simuliris.base_logic Require Export gen_sim_prog.
From simuliris.simulation Require Export slsls.
From simuliris.simulation Require Import lifting.
From simuliris.stacked_borrows Require Import tkmap_view.
From simuliris.stacked_borrows Require Export defs class_instances.
From simuliris.stacked_borrows Require Import steps_progress steps_retag steps_inv.
From simuliris.stacked_borrows Require Import logical_state inv_accessors.

Section lifting.
Context `{!sborGS Σ}.
Implicit Types P Q : iProp Σ.
Implicit Types Φ : expr → expr → iProp Σ.
Implicit Types σ σ_s σ_t : state.
Implicit Types r r_s r_t : result.
Implicit Types l : loc.
Implicit Types f : fname.

Lemma sim_value_result v_t v_s (Φ : result → result → iProp Σ) π :
  Φ (ValR v_t) (ValR v_s) -∗ #v_t ⪯{π} #v_s {{ Φ }}.
Proof. iIntros "H". iApply sim_expr_base. iExists (ValR v_t), (ValR v_s). eauto. Qed.

Lemma sim_place_result l_t t_t T_t l_s t_s T_s (Φ : result → result → iProp Σ) π :
  Φ (PlaceR l_t t_t T_t) (PlaceR l_s t_s T_s) -∗ Place l_t t_t T_t ⪯{π} Place l_s t_s T_s {{ Φ }}.
Proof. iIntros "H". iApply sim_expr_base. iExists (PlaceR _ _ _), (PlaceR _ _ _); eauto. Qed.

Lemma sim_result r_t r_s (Φ : result → result → iProp Σ) π :
  Φ r_t r_s -∗ of_result r_t ⪯{π} of_result r_s {{ Φ }}.
Proof. iIntros "H". iApply sim_expr_base. by iApply lift_post_val. Qed.

Lemma sim_alloc_public T Φ π :
  (∀ t l, t $$ tk_pub -∗
    rrel (PlaceR l (Tagged t) T) (PlaceR l (Tagged t) T) -∗
    Place l (Tagged t) T ⪯{π} Place l (Tagged t) T [{ Φ }]) -∗
  Alloc T ⪯{π} Alloc T [{ Φ }].
Proof.
  iIntros "Hsim".
  iApply sim_lift_base_step_both. iIntros (P_t P_s σ_t σ_s ??) "[(HP_t & HP_s & Hbor) %Hsafe]".
  iModIntro.
  destruct Hsafe as [Hpool Hsafe].
  iPoseProof (bor_interp_get_pure with "Hbor") as "%Hp".
  destruct Hp as (Hsst_eq & Hsnp_eq & Hsnc_eq & Hscs_eq & Hwf_s & Hwf_t & Hdom_eq).
  iSplitR. { iPureIntro. do 3 eexists. eapply alloc_base_step. }
  iIntros (e_t' efs_t σ_t') "%Hhead_t".
  specialize (head_alloc_inv _ _ _ _ _ _ Hhead_t) as (-> & -> & ->).

  (* allocate tag *)
  iDestruct "Hbor" as "(%M_call & %M_tag & %M_t & %M_s & (Hc & Htag_auth & Htag_t_auth & Htag_s_auth) & Htainted & Hpub_cid & #Hsrel & %Hcall_interp & %Htag_interp & _ & _)".
  assert (M_tag !! σ_t.(snp) = None).
  { destruct (M_tag !! σ_t.(snp)) as [[tk' []] | ] eqn:Hs; last done. exfalso.
    apply Htag_interp in Hs as (_ & ? & _); lia.
  }
  iMod (tkmap_insert tk_pub σ_t.(snp) () ltac:(done) with "Htag_auth") as "[Htag_auth #Ht]".
  iModIntro.
  pose (l := (fresh_block σ_t.(shp), 0)). pose (nt := σ_t.(snp)).
  pose (α' := init_stacks σ_t.(sst) l (tsize T) (Tagged nt)).
  pose (σ_s' := (mkState (init_mem l (tsize T) σ_s.(shp)) α' σ_s.(scs) (S σ_s.(snp)) σ_s.(snc))).
  assert (Hhead_s : base_step P_s (Alloc T) σ_s (Place l (Tagged nt) T) σ_s' []).
  { subst σ_s' nt α' l. rewrite -Hsst_eq -Hsnp_eq. rewrite -(fresh_block_det σ_s σ_t); last done.
    eapply alloc_base_step.
  }
  iExists _, [], _. iSplitR; first done. simpl. iFrame "HP_t HP_s".
  iSplitR "Hsim Ht"; first last.
  { iSplitL; last done. iApply ("Hsim" with "Ht"). iSplit; last done.
    iSplitR; first done. iRight. iExists nt, nt. iFrame "Ht". eauto.
  }
  (* re-establish the invariants *)
  iExists M_call, (<[nt := (tk_pub, ())]> M_tag), M_t, M_s.
  iFrame "Hc Htag_auth Htag_t_auth Htag_s_auth".
  iSplitL "Htainted"; last iSplitL "Hpub_cid"; last iSplit; last iSplit; last iSplit; last iSplit.
  - (* tainted *)
    subst σ_s' α' nt. rewrite -Hsst_eq -Hsnp_eq.
    by iApply tag_tainted_interp_alloc.
  - (* pub cid *)
    iApply (pub_cid_interp_preserve_sub with "Hpub_cid"); simpl; done.
  - (* state rel *)
    rewrite -{2}(map_empty_union M_t).
    subst σ_s' α' nt. rewrite -{2}Hsst_eq.
    iApply state_rel_alloc_update; last done.
    intros t (s & Hs) ->. congruence.
  - (* call interp *)
    iPureIntro. apply call_set_interp_alloc_update; done.
  - (* tag interp *)
    iPureIntro. destruct Htag_interp as (Htag_interp & Hdom_t & Hdom_s). split_and!.
    { simpl. intros t tk. rewrite lookup_insert_Some. intros [[<- [= <-]] | [Hneq Hsome]].
      - (* new tag: as these are public, the locations under this tag are not directly controlled *)
        split_and!; [ lia | lia | | |].
        + intros l' sc_t Hsc_t. exfalso. specialize (Hdom_t nt l' ltac:(eauto)) as (? &?). subst nt. congruence.
        + intros l' sc_t Hsc_t. exfalso. specialize (Hdom_s nt l' ltac:(eauto)) as (? &?). subst nt. congruence.
        + apply dom_agree_on_tag_not_elem.
          * intros l'. destruct (M_t !! (nt, l')) eqn:Hs; last done.
            destruct (Hdom_t nt l' ltac:(eauto)) as (? & ?).
            subst nt. congruence.
          * intros l'. destruct (M_s !! (nt, l')) eqn:Hs; last done.
            destruct (Hdom_s nt l' ltac:(eauto)) as (? & ?).
            subst nt. congruence.
      - (* old tag *)
        specialize (Htag_interp _ _ Hsome) as (? & ? & Hcontrol_t & Hcontrol_s & Hag).
        split_and!; [lia | lia | .. | done].
        + intros l' sc_t Hcontrol%Hcontrol_t. eapply loc_controlled_alloc_update; done.
        + intros l' sc_s Hcontrol%Hcontrol_s. subst α' nt σ_s' l.
          rewrite -Hsnp_eq -Hsst_eq -(fresh_block_det _ _ Hdom_eq).
          eapply loc_controlled_alloc_update; [ done | lia | done].
    }
    { intros t l'. rewrite lookup_insert_is_Some'. eauto. }
    { intros t l'. rewrite lookup_insert_is_Some'. eauto. }
  - iPureIntro. by eapply base_step_wf.
  - iPureIntro. by eapply base_step_wf.
Qed.

Lemma sim_free_public T_t T_s l_t l_s bor_t bor_s Φ π :
  rrel (PlaceR l_t bor_t T_t) (PlaceR l_s bor_s T_s) -∗
  #[☠] ⪯{π} #[☠] [{ Φ }] -∗
  Free (Place l_t bor_t T_t) ⪯{π} Free (Place l_s bor_s T_s) [{ Φ }].
Proof.
  iIntros "[#Hscrel ->] Hsim".
  iPoseProof (sc_rel_ptr_source with "Hscrel") as "[%Heq Hpub]". injection Heq as [= -> ->].
  iApply sim_lift_base_step_both. iIntros (P_t P_s σ_t σ_s ??) "[(HP_t & HP_s & Hbor) %Hsafe]".
  iModIntro.
  destruct Hsafe as [Hpool Hsafe].
  specialize (pool_safe_implies Hsafe Hpool) as (Hdealloc_s & (α' & Hstack_s)).

  iPoseProof (bor_interp_get_pure with "Hbor") as "%Hp".
  destruct Hp as (Hsst_eq & Hsnp_eq & Hsnc_eq & Hscs_eq & Hwf_s & Hwf_t & Hdom_eq).
  iSplitR.
  { iPureIntro. do 3 eexists. eapply dealloc_base_step'; [done | |].
    - intros m. rewrite -Hdealloc_s. rewrite -!elem_of_dom Hdom_eq. done.
    - instantiate (1 := α'). rewrite -Hsst_eq -Hscs_eq. done.
  }
  iIntros (e_t' efs_t σ_t') "%Hhead_t".
  specialize (head_free_inv _ _ _ _ _ _ _ _ Hhead_t) as (α'0 & Hstack_t & Hdealloc_t & -> & -> & ->).
  iAssert (⌜α'0 = α'⌝)%I as "->".
  { iPureIntro. move : Hstack_t Hstack_s. rewrite Hsst_eq Hscs_eq. congruence. }
  iModIntro.
  pose (σ_s' := (mkState (free_mem l_s (tsize T_s) σ_s.(shp)) α' σ_s.(scs) σ_s.(snp) σ_s.(snc))).
  assert (Hhead_s : base_step P_s (Free (Place l_s bor_s T_s)) σ_s (ValR [☠]%S) σ_s' []).
  { eapply dealloc_base_step'; eauto. }
  iExists (#[☠])%E, [], σ_s'. iSplitR; first done.
  iFrame "HP_t HP_s".
  iSplitR "Hsim"; first last. { iSplitL; done. }

  iDestruct "Hbor" as "(%M_call & %M_tag & %M_t & %M_s & (Hc & Htag_auth & Htag_t_auth & Htag_s_auth) & Htainted & Hpub_cid & #Hsrel & %Hcall_interp & %Htag_interp & _ & _)".

  (* prove that it is a public location *)
  iAssert (⌜untagged_or_public M_tag bor_s⌝)%I as %Hpub.
  { iDestruct "Hscrel" as "[_ [[-> _] | (%t1 & %t2 & -> & -> & <- & _)]]"; first done.
    iPoseProof (tkmap_lookup with "Htag_auth Hpub") as "%". done.
  }

  (* we keep the base_step hypotheses to use the [base_step_wf] lemma below *)
  (* re-establish the invariants *)
  iExists M_call, M_tag, M_t, M_s.
  iFrame "Hc Htag_auth Htag_t_auth Htag_s_auth".
  iSplitL "Htainted"; last iSplitL "Hpub_cid"; last iSplit; last iSplit; last iSplit; last iSplit.
  - (* re-establish the tainted interpretation *)
    subst σ_s'.
    iApply (tag_tainted_interp_preserve with "Htainted"); simpl; first lia.
    intros l stk' Hstk' it Hit.
    specialize (for_each_dealloc_lookup_Some _ _ _ _ _ Hstack_s _ _ Hstk') as (_ & Hstk).
    right. right. eauto.
  - (* pub cid *)
    iApply (pub_cid_interp_preserve_sub with "Hpub_cid"); simpl; done.
  - (* re-establish the state relation *)
    iDestruct "Hsrel" as "(_ & _ & _ & _ & _ & Hsrel)".
    iSplitR. { iPureIntro. simpl. apply free_mem_dom. done. }
    simpl. do 4 (iSplitR; first done).
    iIntros (l (sc & Hsome)).
    destruct (free_mem_lookup_case l l_s (tsize T_s) σ_t.(shp)) as [[Hi Heq] | (i & _ & -> & ?)]; last congruence.
    rewrite Heq in Hsome. iDestruct ("Hsrel" $! l with "[]") as "[Hpubl | Hprivl]"; first by eauto.
    + iLeft. iIntros (sc_t Hsc_t). simpl in *.
      rewrite Heq in Hsc_t. simplify_eq.
      iDestruct ("Hpubl" $! sc Hsome) as (sc_s) "[%Hsc_s Hscr]".
      iExists sc_s. iSplitR; last done.
      iPureIntro.
      destruct (free_mem_lookup_case l l_s (tsize T_s) σ_s.(shp)) as [[_ Heq'] | (i' & Hi' & -> & _)].
      2: { specialize (Hi i' Hi'). congruence. }
      rewrite Heq' Hsc_s. done.
    + iRight. done.
  - (* re-establish the call set interpretation *)
    iPureIntro.
    iIntros (c M' Hc). simpl. specialize (Hcall_interp _ _ Hc) as (? & HM'). split; first done.
    intros t L HL. specialize (HM' _ _ HL) as (? & HM'). split; first done.
    intros l Hl. specialize (HM' l Hl) as (stk & pm & Hstk & Hit & Hpm).
    destruct (for_each_true_lookup_case_2 _ _ _ _ _ Hstack_t) as [EQ1 EQ2].
    (* from Hstack_s, l cannot be in the affected range because it is protected by c,
      so α' !! l = σt.(sst) !! l. *)
    destruct (block_case l_s l (tsize T_s)) as [Hneq|(i & Hi & ->)].
    + rewrite EQ2//. eauto.
    + exfalso. clear EQ2.
      specialize (EQ1 _ Hi) as (stk1 & stk' & Eqstk1 & Eqstk' & Hdealloc).
      rewrite Eqstk1 in Hstk. simplify_eq.
      move : Hdealloc. destruct (dealloc1 stk bor_s σ_t.(scs)) eqn:Eqd; last done.
      intros _.
      destruct (dealloc1_Some stk bor_s σ_t.(scs)) as (it & Eqit & ? & FA & GR).
      { by eexists. }
      rewrite ->Forall_forall in FA. apply (FA _ Hit).
      rewrite /is_active_protector /= /is_active bool_decide_true //.
  - (* re-establish the tag interpretation *)
    destruct Htag_interp as (Htag_interp & Hdom_t & Hdom_s).
    iPureIntro. split_and!; [ | done | done].
    intros t tk Ht. simpl. specialize (Htag_interp _ _ Ht) as (? & ? & Hcontrol_t & Hcontrol_s & Hag).
    split_and!; [done | done | | | done].
    + intros l sc_t Hsc_t%Hcontrol_t.
      eapply loc_controlled_dealloc_update; [ apply Hstack_t | done | | done].
      intros [-> _]. rewrite Hpub in Ht. congruence.
    + intros l sc_s Hsc_s%Hcontrol_s.
      eapply loc_controlled_dealloc_update; [apply Hstack_s | done | | done].
      intros [-> _]. rewrite Hpub in Ht. congruence.
  - iPureIntro. by eapply base_step_wf.
  - iPureIntro. by eapply base_step_wf.
Qed.

(** TODO: generalize, move, and use it for the opt lemmas too *)
Lemma sim_copy_public_controlled_update σ l l' (bor : tag) (T : type) (α' : stacks) (t : ptr_id) (tk : tag_kind) sc :
  memory_read σ.(sst) σ.(scs) l bor (tsize T) = Some α' →
  state_wf σ →
  (bor = Tagged t → tk = tk_pub) →
  loc_controlled l' t tk sc σ →
  loc_controlled l' t tk sc (mkState σ.(shp) α' σ.(scs) σ.(snp) σ.(snc)).
Proof.
  intros Hread Hwf Hbor Hcontrol Hpre.
  (* need to update the loc_controlled.
    intuitive justification:
    - if l is not affected by the Copy, we are fine.
    - if it is affected, we already know that we accessed with a public tag [bor_s].
      In case this current tag [t] is local, we have a contradiction as the tags must be the same.
      In case this current tag [t] is unique: if the item is in the stack, then it must still be because it would have been protected
      In case this current tag [t] is public: it should still be there, as it is not incompatible with our copy access (we leave SharedROs there).
  *)

  specialize (for_each_access1 _ _ _ _ _ _ _ Hread) as Hsub.
  assert (bor_state_pre l' t tk σ) as H.
  { move : Hpre. destruct tk; [ | | done ].
    all: intros (st' & pm & opro & Hα'_some & Hit & Hpm);
      specialize (Hsub _ _ Hα'_some) as (st & Hα_some & Hsublist & _);
      exists st, pm, opro;
      split_and!; [ done | | done]; specialize (Hsublist _ Hit) as ([] & Hit' & Heq & Heq' & Hperm'); simpl in *;
      rewrite Heq Heq' -Hperm'; done.
  }
  specialize (Hcontrol H) as [Hown Hmem].
  split; last done.
  move: Hpre.
  destruct tk; simpl.
  * (* goal: use access1_active_SRO_preserving *)
    intros (st & pm & opro & Hsome_st & Hit & Hpm). exists st. split; first done.
    destruct Hown as (st'' & Hsome_st'' & Hactive).
    destruct (for_each_lookup_case _ _ _ _ _ Hread _ _ _ Hsome_st'' Hsome_st) as [-> | [Hacc _]]; first done.
    destruct access1 as [ [n st']| ] eqn:Hacc_eq; simpl in Hacc; simplify_eq.
    eapply access1_active_SRO_preserving; [ | done | apply Hacc_eq | done ].
    eapply Hwf; done.
  * intros (st & pm & opro & Hsome_st & Hit & Hpm).
    destruct Hown as (st' & Hsome_st' & opro' & st'0 & Heq).
    destruct (for_each_lookup_case _ _ _ _ _ Hread _ _ _ Hsome_st' Hsome_st) as [-> | [Hacc _]]; first by eauto.
    destruct access1 as [ [n st'']| ] eqn:Hacc_eq; simpl in Hacc; simplify_eq.
    exists st. split; first done. exists opro'.
    eapply access1_head_preserving; [ eapply Hwf; done| done | | apply Hacc_eq| eexists; done ].
    (* need that opro = opro' *)
    specialize (access1_read_eq _ _ _ _ t _ _ _ ltac:(eapply Hwf; done) Hacc_eq ltac:(by left) Hit Hpm ltac:(done) ltac:(done)) as Heq.
    simplify_eq. done.
  * intros _. simpl in Hown.
    specialize (for_each_access1_lookup_inv _ _ _ _ _ _ _ Hread _ _ Hown) as (st' & Hst' & [[n' Hacc_eq] | Heq]).
    2: { rewrite Heq. done. }
    specialize (access1_in_stack _ _ _ _ _ _ Hacc_eq) as (it & ->%list_elem_of_singleton & Htg & _).
    (* contradiction, since t is public *)
    simpl in Htg. subst bor. discriminate Hbor. done.
Qed.

Lemma sim_copy_public Φ π l_t bor_t T_t l_s bor_s T_s :
  rrel (PlaceR l_t bor_t T_t) (PlaceR l_s bor_s T_s) -∗
  (∀ v_t v_s, value_rel v_t v_s -∗ v_t ⪯{π} ValR v_s [{ Φ }]) -∗
  Copy (PlaceR l_t bor_t T_t) ⪯{π} Copy (PlaceR l_s bor_s T_s) [{ Φ }].
Proof.
  iIntros "#Hrel Hsim".
  iApply sim_lift_base_step_both. iIntros (P_t P_s σ_t σ_s ??) "[(HP_t & HP_s & Hbor) %Hsafe]".
  iModIntro.
  iDestruct "Hrel" as "[[<- Hrel] <-]".
  iDestruct "Hbor" as "(%M_call & %M_tag & %M_t & %M_s & (Hc & Htag_auth & Htag_t_auth & Htag_s_auth) & Htainted & Hpub_cid & #Hsrel & %Hcall_interp & %Htag_interp & %Hwf_s & %Hwf_t)".
  iPoseProof (state_rel_stacks_eq with "Hsrel") as "%Hstacks_eq".
  iPoseProof (state_rel_calls_eq with "Hsrel") as "%Hcalls_eq".

  (* prove that it is a public location *)
  iAssert (⌜untagged_or_public M_tag bor_t ∧ bor_t = bor_s⌝)%I as %Hpub.
  { iDestruct "Hrel" as "[[-> ->] | (%t1 & %t2 & -> & -> & <- & Hpub)]"; first done.
    iPoseProof (tkmap_lookup with "Htag_auth Hpub") as "%". done.
  }
  destruct Hpub as [Hpub ->].

  destruct Hsafe as [Hpool Hsafe].
  specialize (pool_safe_implies Hsafe Hpool) as [(v_s & Hread_s & (α' & Hstack_s)) | Hfail]; first last.
  { (* failing copy *)
    iSplitR.
    { iPureIntro. do 3 eexists. eapply failed_copy_base_step'; first done.
      rewrite -Hstacks_eq -Hcalls_eq. done.
    }
    iIntros (e_t' efs_t σ_t') "%Hhead_t".
    specialize (head_copy_inv _ _ _ _ _ _ _ _ Hhead_t) as [-> [(? & ? & _ & ? & _) | (-> & ? & ->)]]; first congruence.
    iModIntro.
    assert (Hhead_s : base_step P_s (Copy (Place l_t bor_s T_t)) σ_s (Val $ replicate (tsize T_t) ScPoison) σ_s []).
    { eapply failed_copy_base_step'; eauto. }
    iExists (Val $ replicate (tsize T_t) ScPoison), [], σ_s. iSplitR; first done.
    iFrame. iSplitR "Hsim"; first last.
    { iSplitL; last done. iApply "Hsim".
      generalize (tsize T_t) => n. iInduction n as [ | n] "IH"; first by iApply big_sepL2_nil.
      rewrite /value_rel big_sepL2_cons; iFrame "IH". done.
    }
    repeat (iSplit; done).
  }
  (* successful copy *)
  iAssert (⌜∀ i : nat, (i < tsize T_t)%nat → is_Some (shp σ_t !! (l_t +ₗ i))⌝)%I as "%Hsome_target".
  { iPoseProof (state_rel_heap_lookup_Some with "Hsrel") as "%Hl".
    iPureIntro. (* use read_mem_is_Some' *)
    specialize (proj2 (read_mem_is_Some' l_t (tsize T_t) σ_s.(shp)) ltac:(eauto)) as Him.
    intros i Hi. apply Hl, elem_of_dom. by eapply Him.
  }


  (* prove reducibility *)
  iSplitR.
  { iPoseProof (state_rel_dom_eq with "Hsrel") as "%Hdom".
    iPureIntro.
    destruct (read_mem_is_Some l_t (tsize T_t) σ_t.(shp)) as [v_t Eqvt].
    { intros m. rewrite Hdom. apply (read_mem_is_Some' l_t (tsize T_t) σ_s.(shp)). by eexists. }
    have Eqα'2: memory_read σ_t.(sst) σ_t.(scs) l_t bor_s (tsize T_t) = Some α'.
    { rewrite -Hstacks_eq -Hcalls_eq. done. }
    eexists; eexists; eexists. eapply copy_base_step'; eauto.
  }
  (* we keep the base_step hypotheses to use the [base_step_wf] lemma below *)
  iIntros (e_t' efs_t σ_t') "%Hhead_t".
  specialize (head_copy_inv _ _ _ _ _ _ _ _ Hhead_t) as [-> [(v_t & α'0 & COPY & ACC & -> & ->) | (-> & ? & ->)]]; last congruence.
  iAssert (⌜α'0 = α'⌝)%I as "->".
  { iPureIntro. move : ACC Hstack_s. rewrite Hcalls_eq Hstacks_eq. congruence. }
  iModIntro.
  pose (σ_s' := (mkState (shp σ_s) α' (scs σ_s) (snp σ_s) (snc σ_s))).
  assert (Hhead_s : base_step P_s (Copy (Place l_t bor_s T_t)) σ_s (ValR v_s) σ_s' []).
  { eapply copy_base_step'; eauto. }
  iExists (Val v_s), [], σ_s'. iSplitR; first done.
  iFrame "HP_t HP_s".

  iSplitR "Hsim".
  {
    (* re-establish the invariants *)
    iExists M_call, M_tag, M_t, M_s.
    iFrame "Hc Htag_auth Htag_t_auth Htag_s_auth".
    iSplitL "Htainted"; last iSplitL "Hpub_cid"; last iSplit; last iSplit; last iSplit; last iSplit.
    - (* tainted *)
      subst σ_s'. iApply (tag_tainted_interp_tagged_sublist with "Htainted"); simpl; first lia.
      intros l stk' Hstk'.
      specialize (for_each_access1 _ _ _ _ _ _ _ Hstack_s _ _ Hstk') as (stk & Hstk & Hsubl & _).
      eauto.
    - (* pub cid *)
      iApply (pub_cid_interp_preserve_sub with "Hpub_cid"); done.
    - (* state rel *)
      iPoseProof (state_rel_dom_eq with "Hsrel") as "%Hdom".
      iPoseProof (state_rel_snp_eq with "Hsrel") as "%Hsnp".
      iPoseProof (state_rel_snc_eq with "Hsrel") as "%Hsnc".
      iSplit; first done. iSplit; first done. iSplit; first done.
      iSplit; first done. iSplit; first done.
      simpl. iIntros (l) "Hs". iPoseProof (state_rel_pub_or_priv with "Hs Hsrel") as "$".
    - (* call invariant *)
      iPureIntro. intros c M' HM'_some.
      specialize (Hcall_interp c M' HM'_some) as (Hin & Hprot).
      split; first by apply Hin. intros pid L HL_some. specialize (Hprot pid L HL_some) as [Hpid Hprot].
      split; first by apply Hpid. intros l Hin_l.
      specialize (Hprot l Hin_l) as (stk & pm & Hstk_some & Hin_stack & Henabled).
      (* we use that reads must preserve active protectors (but note that the stack may have changed, even when there is an active protector) *)
      specialize (for_each_access1_active_preserving _ _ _ _ _ _ _ ACC l stk Hstk_some) as (stk' & Hstk'_some & Hac_pres).
      exists stk', pm. split; last split; [ done | by apply Hac_pres| done ].
    - (* tag invariant *)
      iPureIntro. destruct Htag_interp as (Htag_interp & Ht_dom & Hs_dom). split_and!; [ | done..].
      intros t tk Htk_some. destruct (Htag_interp t tk Htk_some) as (Hsnp_lt_t & Hsnp_lt_s & Hctrl_t & Hctrl_s & Hag).
      split_and!; [ done | done | | | done ].
      + intros l sc_t Hsc_t. eapply sim_copy_public_controlled_update; [ by eauto .. | | by eauto].
        intros ->. rewrite Hpub in Htk_some. congruence.
      + intros l sc_s Hsc_s. eapply sim_copy_public_controlled_update; [ by eauto .. | | by eauto].
        intros ->. rewrite Hpub in Htk_some. congruence.
    - (* source state wf *)
      iPureIntro. eapply base_step_wf; done.
    - (* target state wf *)
      iPureIntro. eapply base_step_wf; done.
  }
  iSplitL; last done.

  iApply "Hsim".
  (* proving the value relation *)
  specialize (read_mem_values _ _ _ _ COPY) as [Hlen_t Hv_t].
  specialize (read_mem_values _ _ _ _ Hread_s) as [Hlen_s Hv_s].

  iApply big_sepL2_forall; iSplit; first (iPureIntro;lia).
  iIntros (i sc_t sc_s) "%Hs_t %Hs_v".
  assert (i < tsize T_t)%nat as Hi. { rewrite -Hlen_t. eapply lookup_lt_is_Some_1. eauto. }
  iPoseProof (state_rel_pub_if_not_priv _ _ _ _ _ _ (l_t +ₗ i) with "[] Hsrel [Hrel]") as "Hpub".
  { iPureIntro. by apply Hsome_target. }
  { iPoseProof (state_rel_calls_eq with "Hsrel") as "%Hcall_eq".
    iPoseProof (state_rel_stacks_eq with "Hsrel") as "%Hstack_eq".
    iPureIntro. intros t Hpriv.
    specialize (for_each_lookup_case_2 _ _ _ _ _ Hstack_s) as (Hstk & _).
    specialize (Hstk i%nat ltac:(lia)) as (stk & stk' & ? & (_ & Haccess_some)).
    eapply (priv_pub_access_UB _ AccessRead _ _ _ _ stk); [ | | apply Hpriv | eauto..].
    - rewrite -Hstack_eq. done.
    - move : Haccess_some. rewrite Hcall_eq. destruct access1; cbn; intros; simplify_eq. eauto.
  }
  iPoseProof (pub_loc_lookup with "[] Hpub") as "(%sc_t' & %sc_s' & %Hread_both & Hsc_rel)"; first by eauto.
  enough (sc_t = sc_t' ∧ sc_s = sc_s') by naive_solver.
  move : Hread_both (Hv_t i Hi) (Hv_s i Hi) Hs_t Hs_v.
  by move => [-> ->] <- <- [= ->] [= ->].
Qed.

(** Write *)
Lemma sim_write_public Φ π l_t bor_t T_t l_s bor_s T_s v_t' v_s' :
  rrel (PlaceR l_t bor_t T_t) (PlaceR l_s bor_s T_s) -∗
  value_rel v_t' v_s' -∗
  (#[☠] ⪯{π} #[☠] [{ Φ }]) -∗
  Write (Place l_t bor_t T_t) v_t' ⪯{π} Write (Place l_s bor_s T_s) v_s' [{ Φ }].
Proof.
  iIntros "Hrel #Hvrel Hsim". iDestruct "Hrel" as "[#Hscrel ->]".
  iPoseProof (sc_rel_ptr_source with "Hscrel") as "[%Heq Hpub]". injection Heq as [= -> ->].
  iApply sim_lift_base_step_both. iIntros (P_t P_s σ_t σ_s ??) "[(HP_t & HP_s & Hbor) %Hsafe]".
  iModIntro.
  destruct Hsafe as [Hpool Hsafe].
  specialize (pool_safe_implies Hsafe Hpool) as (Hread_s & (α' & Hstack_s) & Hlen_s').
  iPoseProof (value_rel_length with "Hvrel") as "%Hlen_t'".

  iPoseProof (bor_interp_get_pure with "Hbor") as "%Hp".
  destruct Hp as (Hsst_eq & Hsnp_eq & Hsnc_eq & Hscs_eq & Hwf_s & Hwf_t & Hdom_eq).
  iSplitR.
  { iPureIntro. do 3 eexists. eapply write_base_step'; [lia | |].
    - rewrite -Hdom_eq. intros n Hn. apply Hread_s. lia.
    - instantiate (1 := α'). rewrite -Hsst_eq -Hscs_eq. done.
  }
  iIntros (e_t' efs_t σ_t') "%Hhead_t".
  specialize (head_write_inv _ _ _ _ _ _ _ _ _ Hhead_t) as (α'0 & -> & -> & -> & _ & Hin_dom & Hstack_t).
  iAssert (⌜α'0 = α'⌝)%I as "->".
  { iPureIntro. move : Hstack_t Hstack_s. rewrite Hsst_eq Hscs_eq. congruence. }
  iModIntro.
  pose (σ_s' := (mkState (write_mem l_s v_s' σ_s.(shp)) α' σ_s.(scs) σ_s.(snp) σ_s.(snc))).
  assert (Hhead_s : base_step P_s (Write (Place l_s bor_s T_s) v_s') σ_s (ValR [☠]%S) σ_s' []).
  { eapply write_base_step'; eauto. intros. rewrite Hdom_eq. apply Hin_dom. lia. }
  iExists (#[☠])%E, [], σ_s'. iSplitR; first done.
  iFrame "HP_t HP_s".
  iSplitR "Hsim"; first last. { iSplitL; done. }

  iDestruct "Hbor" as "(%M_call & %M_tag & %M_t & %M_s & (Hc & Htag_auth & Htag_t_auth & Htag_s_auth) & Htainted & Hpub_cid & #Hsrel & %Hcall_interp & %Htag_interp & _ & _)".

  (* prove that it is a public location *)
  iAssert (⌜untagged_or_public M_tag bor_s⌝)%I as %Hpub.
  { iDestruct "Hscrel" as "[_ [[-> _] | (%t1 & %t2 & -> & -> & <- & _)]]"; first done.
    iPoseProof (tkmap_lookup with "Htag_auth Hpub") as "%". done.
  }

  (* we keep the base_step hypotheses to use the [base_step_wf] lemma below *)
  (* re-establish the invariants *)
  iExists M_call, M_tag, M_t, M_s.
  iFrame "Hc Htag_auth Htag_t_auth Htag_s_auth".
  iSplitL "Htainted"; last iSplitL "Hpub_cid"; last iSplit; last iSplit; last iSplit; last iSplit.
  - (* tainted *)
    subst σ_s'. iApply (tag_tainted_interp_tagged_sublist with "Htainted"); simpl; first lia.
    intros l stk' Hstk'.
    specialize (for_each_access1 _ _ _ _ _ _ _ Hstack_s _ _ Hstk') as (stk & Hstk & Hsubl & _).
    eauto.
  - (* pub cid *)
    iApply (pub_cid_interp_preserve_sub with "Hpub_cid"); done.
  - (* state rel *)
    rewrite /state_rel; simpl. iSplitL.
    { iPureIntro. apply gset_leibniz. rewrite !write_mem_dom; [by rewrite Hdom_eq | done..]. }
    do 4 (iSplitL; first done). iDestruct "Hsrel" as "(_ & _ & _ & _ & _ & Hsrel)".
    iIntros (l) "%Hs".
    specialize (write_mem_lookup l_s v_s' σ_s.(shp)) as (Heq & Heq').
    specialize (write_mem_lookup_case l_s v_t' σ_t.(shp) l) as [(i & Hi & -> & Hwrite) | (Hi & Hwrite)].
    + (* we wrote to the location, and the written values must be related *)
      iLeft. iIntros (sc_t Hsc_t). simpl in Hsc_t. rewrite Heq; last lia.
      iExists (v_s' !!! i). rewrite Hwrite in Hsc_t.
      rewrite -(list_lookup_total_correct _ _ _ Hsc_t).
      iSplitR. { iPureIntro. apply list_lookup_lookup_total. apply lookup_lt_is_Some_2. lia. }
      iApply (value_rel_lookup_total with "Hvrel"). lia.
    + (* unaffected location *)
      simpl. rewrite Hwrite in Hs.
      iDestruct ("Hsrel" $! l with "[//]") as "[Hpubl | Hprivl]"; last by iRight.
      iLeft. rewrite /pub_loc Hwrite Heq'; first done. intros. apply Hi. lia.
  - (* call invariant *)
    iPureIntro. intros c M' HM'_some. simpl.
    specialize (Hcall_interp c M' HM'_some) as (Hin & Hprot).
    split; first done. intros t L [Ht HL]%Hprot. split; first done.
    intros l (stk & pm & Hsome_stk & Hit & Hpm)%HL.
    specialize (for_each_access1_active_preserving _ _ _ _ _ _ _ Hstack_t _ _ Hsome_stk) as (stk' & Hstk'_some & Hac_pres).
    exists stk', pm. split; last split; [ done | by apply Hac_pres| done ].
  - (* tag invariant *)
    iPureIntro. destruct Htag_interp as (Htag_interp & Ht_dom & Hs_dom). split_and!; [ | done..].
    intros t tk Ht.
    specialize (Htag_interp _ _ Ht) as (? & ? & Hcontrolled_t & Hcontrolled_s & Hdom).
    split_and!; [ done | done | | | done ].
    + intros l sc_t Hcontrol%Hcontrolled_t.
      eapply loc_controlled_write_update; [ apply Hwf_t | | apply Hstack_t| lia | done].
      intros [-> _]. rewrite Hpub in Ht. congruence.
    + intros l sc_s Hcontrol%Hcontrolled_s.
      eapply loc_controlled_write_update; [ apply Hwf_s | | apply Hstack_s| lia | done].
      intros [-> _]. rewrite Hpub in Ht. congruence.
  - (* source state wf *)
    iPureIntro. eapply base_step_wf; done.
  - (* target state wf *)
    iPureIntro. eapply base_step_wf; done.
Qed.

(** Retag *)
Lemma bor_interp_retag_public σ_s σ_t c l ot rkind kind T nt α' nxtp' :
  retag σ_s.(sst) σ_s.(snp) σ_s.(scs) c l ot rkind kind T = Some (nt, α', nxtp') →
  state_wf (mkState σ_t.(shp) α' σ_t.(scs) nxtp' σ_t.(snc)) →   (* could remove that assumption *)
  state_wf (mkState σ_s.(shp) α' σ_s.(scs) nxtp' σ_s.(snc)) →   (* could remove that assumption *)
  sc_rel (ScPtr l ot) (ScPtr l ot) -∗
  bor_interp sc_rel σ_t σ_s ==∗
  sc_rel (ScPtr l nt) (ScPtr l nt) ∗
  bor_interp sc_rel (mkState σ_t.(shp) α' σ_t.(scs) nxtp' σ_t.(snc)) (mkState σ_s.(shp) α' σ_s.(scs) nxtp' σ_s.(snc)).
Proof.
  intros Hretag Hwf_t' Hwf_s'.
  iIntros "Hscrel Hbor". iDestruct "Hbor" as "(%M_call & %M_tag & %M_t & %M_s & (Hc & Htag_auth & Htag_t_auth & Htag_s_auth) & Htainted & Hpub_cid & #Hsrel & %Hcall_interp & %Htag_interp & %Hwf_s & %Hwf_t)".

  iDestruct "Hscrel" as "[_ #Hrel]".
  iAssert (⌜untagged_or_public M_tag ot⌝)%I as %Hpub.
  { iDestruct "Hrel" as "[[-> _] | (%t1 & %t2 & -> & -> & <- & Hpub)]"; first done.
    iPoseProof (tkmap_lookup with "Htag_auth Hpub") as "%". done.
  }

  (* allocate resources *)
  set (M_tag' := if decide (ot = nt) then M_tag else if nt is Tagged nt then <[nt := (tk_pub, ())]> M_tag else M_tag).
  specialize (retag_change_nxtp _ _ _ _ _ _ _ _ _ _ _ _ Hretag) as Hle.
  specialize (retag_change_tag _ _ _ _ _ _ _ _ _ _ _ _ Hretag) as Hnt.
  iAssert (|==> (if decide (ot = nt) then True%I else if nt is Tagged nt then nt $$ tk_pub else True%I) ∗ tkmap_auth tag_name 1 M_tag')%I with "[Htag_auth]" as "Hnt".
  { destruct (decide (ot = nt)) as [ | Hneq]; first by eauto.
    destruct Hnt as [ -> | Hnt]; first done.
    destruct nt as [ nt | ]; last by eauto. destruct Hnt as [-> ->].
    iMod (tkmap_insert tk_pub σ_s.(snp) tt with "Htag_auth") as "[$ $]"; last done.
    destruct (M_tag !! snp σ_s) as [ [? []] | ]eqn:Htag; last done.
    apply Htag_interp in Htag as (? & ? & _). lia.
  }
  iMod "Hnt" as "[Hnt Htag_auth]". iModIntro.
  iSplitL "Hnt Hrel".
  { destruct (decide (ot = nt)) as [-> | Hneq]. { iSplit; done. }
    destruct nt. {  iSplit; first done. eauto 10. }
    iSplit; first done. by iLeft.
  }

  iAssert (⌜retag σ_t.(sst) σ_t.(snp) σ_t.(scs) c l ot rkind kind T = Some (nt, α', nxtp')⌝)%I as "%Hretag_t".
  { iPoseProof (state_rel_calls_eq with "Hsrel") as "<-".
    iPoseProof (state_rel_stacks_eq with "Hsrel") as "<-".
    iPoseProof (state_rel_snp_eq with "Hsrel") as "<-". done. }

  (* re-establishing the interpretation *)
  iPoseProof (state_rel_get_pure with "Hsrel") as "%Hp".
  iExists M_call, M_tag', M_t, M_s.
  iFrame "Htag_t_auth Hc Htag_auth Htag_s_auth". iSplitL "Htainted".
  { (* tainted *) iApply (tag_tainted_interp_retag with "Htainted"). done. }
  iSplitL "Hpub_cid". { iFrame "Hpub_cid". }
  iSplitL.
  { (* state relation *)
    rewrite /state_rel. simpl. iDestruct "Hsrel" as "(-> & %Hs_eq & %Hsnp_eq & -> & -> & Hsrel)".
    do 5 (iSplitL; first done). iIntros (l' Hsl').
    iDestruct ("Hsrel" $! l' with "[//]") as "[Hpub | [%t' %Hpriv]]"; first (iLeft; iApply "Hpub").
    iRight. iPureIntro. exists t'.
    (* private locations are preserved: t' cannot be part of the range affected by the retag, because that is public *)
    destruct Hpriv as (tk' & Hsome_tk' & Ht_l' & Htk'). exists tk'.
    split_and!; [ | done | done].
    subst M_tag'. destruct (decide (ot = nt)) as [ | Hneq]; first done.
    destruct nt as [ nt | ]; last done.
    destruct (decide (t' = nt)) as [-> | Hneq']; first last.
    { rewrite lookup_insert_ne; done. }
    exfalso. (* contradiction with Hsome_tk' *)
    destruct Hnt as [<- | [-> ->]]; first congruence.
    apply Htag_interp in Hsome_tk' as (? & _). lia.
  }
  iSplitL.
  { (* call interpretation. *)
    iPureIntro. intros c' M' [Hc' HM']%Hcall_interp. simpl. split; first done.
    specialize (retag_change_nxtp _ _ _ _ _ _ _ _ _ _ _ _ Hretag) as Hnxtp'.
    intros t' S HS. simpl. specialize (HM' t' S HS) as (Ht' & Hprot).
    split; first lia. intros l' Hl'.
    specialize (Hprot l' Hl') as (s & pm' & Hs & Hit & Hpm').
    specialize (retag_item_active_preserving _ _ _ _ _ _ _ _ _ _ _ _ Hretag_t l' s (Tagged t') c' pm' Hs Hc' Hit) as (s' & -> & Hin'). eauto.
  }
  iSplitL.
  { (* tag interpretation. *)
    destruct Htag_interp as (Htag_interp & Ht_dom & Hs_dom).
    destruct Hp as (Hsst & Hsnp & Hsnc & Hscs).
    iPureIntro. split_and!.
    { intros t tk' Hsome.
      assert ((nt = Tagged σ_t.(snp) ∧ t = σ_t.(snp) ∧ tk' = tk_pub ∧ nxtp' = S σ_t.(snp)) ∨ M_tag !! t = Some (tk', ())) as [(-> & -> & -> & ->) | Hsome'].
      { subst M_tag'. destruct (decide (ot = nt)) as [<- | Hneq]; first by eauto.
        destruct nt as [ nt | ]; last by eauto.
        destruct Hnt as [<- | [-> ?]]; first congruence.
        destruct (decide (t = σ_s.(snp))) as [-> | Hneq'].
        - rewrite lookup_insert_eq in Hsome. injection Hsome as [= <-]. left; naive_solver.
        - rewrite lookup_insert_ne in Hsome; last done. by right.
      }
      - (* the new tag: nothing to show, since we don't put the tagged locations under control *)
        simpl. set (nt := σ_t.(snp)).
        assert (∀ l', M_t !! (nt, l') = None) as Mt_nt.
        { intros l'. destruct (M_t !! (nt, l')) eqn:Heq; last done.
          specialize (Ht_dom σ_t.(snp) l' ltac:(eauto)) as ([? []] & [? _]%Htag_interp). lia. }
        assert (∀ l', M_s !! (nt, l') = None) as Ms_nt.
        { intros l'. destruct (M_s !! (nt, l')) eqn:Heq; last done.
          specialize (Hs_dom σ_t.(snp) l' ltac:(eauto)) as ([? []] & [? _]%Htag_interp). lia. }
        split_and!; [lia | lia | | | ].
        + intros l' sc_t HM_t. congruence.
        + intros l' sc_s HM_s. congruence.
        + apply dom_agree_on_tag_not_elem; done.
      - (* old tags are preserved *)
        simpl. specialize (Htag_interp _ _ Hsome') as (? & ? & Hcontrolled_t & Hcontrolled_s & Hdom).
        split_and!; [lia | lia | | | ].
        + intros. eapply loc_controlled_retag_update; [ done | done | | done | by apply Hcontrolled_t].
          intros <-. move : Hpub. rewrite /untagged_or_public. congruence.
        + intros. eapply loc_controlled_retag_update; [ done | done | | done | by apply Hcontrolled_s].
          intros <-. move : Hpub. rewrite /untagged_or_public. congruence.
        + done.
    }
    { subst M_tag'. destruct (decide (ot = nt)); first done. destruct nt as [nt | ]; last done.
      intros. rewrite lookup_insert_is_Some'. right; eauto.
    }
    { subst M_tag'. destruct (decide (ot = nt)); first done. destruct nt as [nt | ]; last done.
      intros. rewrite lookup_insert_is_Some'. right; eauto.
    }
  }
  iSplit; done.
Qed.

Lemma sim_retag_public l_t l_s ot os c kind T rkind π Φ :
  value_rel [ScPtr l_t ot] [ScPtr l_s os] -∗
  (∀ nt, value_rel [ScPtr l_t nt] [ScPtr l_s nt] -∗
    #[ScPtr l_t nt] ⪯{π} #[ScPtr l_s nt] [{ Φ }]) -∗
  Retag #[ScPtr l_t ot] #[ScCallId c] kind T rkind ⪯{π} Retag #[ScPtr l_s os] #[ScCallId c] kind T rkind [{ Φ }].
Proof.
  rewrite {1}/value_rel big_sepL2_singleton.
  iIntros "#Hscrel Hsim".
  iPoseProof (sc_rel_ptr_source with "Hscrel") as "[%Heq Hpub]". injection Heq as [= -> <-].
  iApply sim_lift_base_step_both. iIntros (P_t P_s σ_t σ_s ??) "((HP_t & HP_s & Hbor) & %Hthread & %Hsafe)".
  (* exploit source to gain knowledge about stacks & that c is a valid id *)
  specialize (pool_safe_implies Hsafe Hthread) as (c' & ot' & l' & [= <- <-] & [= <-] & Hc_active & Hretag_some_s).
  iPoseProof (bor_interp_get_pure with "Hbor") as "%Hp".
  have Hretag_some_t : is_Some (retag σ_t.(sst) σ_t.(snp) σ_t.(scs) c l_s ot rkind kind T).
  { destruct Hp as (<- & <- & _ & <- & _). done. }
  iModIntro. iSplitR.
  { iPureIntro.
    destruct Hretag_some_t as ([[] ] & Hretag_some_t).
    do 3 eexists. eapply retag_base_step'; last done.
    destruct Hp as (_ & _ & _ & <- & _). done.
  }
  iIntros (e_t' efs_t σ_t') "%Hhead_t".
  specialize (head_retag_inv _ _ _ _ _ _ _ _ _ _ _ Hhead_t) as (nt & α' & nxtp' & Hretag_t & -> & -> & -> & Hc).
  have Hretag_s : retag σ_s.(sst) σ_s.(snp) σ_s.(scs) c l_s ot rkind kind T = Some (nt, α', nxtp').
  { destruct Hp as (-> & -> & _ & -> & _). done. }
  assert (Hhead_s : base_step P_s (Retag #[ScPtr l_s ot] #[ScCallId c] kind T rkind) σ_s #[ScPtr l_s nt]%E (mkState (shp σ_s) α' (scs σ_s) nxtp' (snc σ_s)) []).
  { eapply retag_base_step'; done. }

  iPoseProof (bor_interp_get_state_wf with "Hbor") as "[%Hwf_t %Hwf_s]".
  iMod (bor_interp_retag_public _ _ _ _ _ _ _ _ _ _ _ Hretag_s with "Hscrel Hbor") as "[Hscrel' Hbor]".
  { by eapply base_step_wf. }
  { by eapply base_step_wf. }
  iModIntro.

  iExists #[ScPtr l_s nt]%E, [], (mkState σ_s.(shp) α' σ_s.(scs) nxtp' σ_s.(snc)).
  iSplitR; first done.
  iFrame "Hbor HP_t HP_s".
  iSplitL; last done. iApply "Hsim". iApply big_sepL2_singleton. done.
Qed.

(** InitCall *)
Lemma bor_interp_init_call σ_t σ_s :
  bor_interp sc_rel σ_t σ_s ==∗
  σ_t.(snc) @@ ∅ ∗
  bor_interp sc_rel
    (mkState σ_t.(shp) σ_t.(sst) ({[ σ_t.(snc) ]} ∪ σ_t.(scs)) σ_t.(snp) (S σ_t.(snc)))
    (mkState σ_s.(shp) σ_s.(sst) ({[ σ_s.(snc) ]} ∪ σ_s.(scs)) σ_s.(snp) (S σ_s.(snc))).
Proof.
  iIntros "(%M_call & %M_tag & %M_t & %M_s & (Hc & Htag_auth & Htag_t_auth & Htag_s_auth) & Htainted & Hpub_cid & #Hsrel & %Hcall_interp & %Htag_interp & %Hwf_s & %Hwf_t)".
  iPoseProof (state_rel_snc_eq with "Hsrel") as "%Hsnc_eq".
  assert (M_call !! σ_t.(snc) = None) as Hfresh.
  { destruct (M_call !! σ_t.(snc)) as [ M' | ] eqn:HM'; last done. apply Hcall_interp in HM' as (Hin & _).
    apply Hwf_t in Hin. lia. }
  iMod (ghost_map_insert σ_t.(snc) ∅ Hfresh with "Hc") as "[Hc Hcall]".
  iModIntro. iFrame "Hcall".
  iExists (<[σ_t.(snc) := ∅]> M_call), M_tag, M_t, M_s. iFrame.
  iSplitL "Hpub_cid".
  { (* pub cid *) iApply (pub_cid_interp_preserve_initcall with "Hpub_cid"); done. }
  iSplitL.
  { iDestruct "Hsrel" as "(H1 & H2 & H3 & H4 & %H5 & H6)". rewrite /state_rel. simpl.
    iFrame "H1 H2 H3".
    iSplitR. { iPureIntro. lia. }
    iSplitR. { rewrite H5 Hsnc_eq. done. }
    iIntros (l Hl). iDestruct ("H6" $! l with "[//]") as "[Hpub | (%t & %Hpriv)]".
    - iLeft. iApply "Hpub".
    - iRight. iPureIntro. exists t.
      destruct Hpriv as (tk & Htk & Hs & [-> | [-> (c' & Hin)]]).
      { exists tk_local. split_and!; eauto. }
      exists tk_unq. split_and!; [done.. | ]. right. split; first done.
      exists c'. destruct Hin as (M' & HM' & Hin). exists M'.
      split; last done. apply lookup_insert_Some. right. split; last done.
      apply Hcall_interp in HM' as (Hwf_tag & _).
      specialize (state_wf_cid_agree _ Hwf_t _ Hwf_tag). lia.
  }
  iSplitL.
  { iPureIntro. intros c M'. simpl. rewrite lookup_insert_Some. intros [(<- & <-) | [Hneq Hsome]].
    - split; first set_solver. intros ? ?. rewrite lookup_empty. congruence.
    - rewrite elem_of_union. apply Hcall_interp in Hsome as [Hin Ha]. split; [by eauto | done].
  }
  iSplitL. { iPureIntro. apply Htag_interp. }
  iSplitL. { iPureIntro. destruct Hwf_s as [Hdom Hstack_item ? Hcid_ag]. constructor; simpl; try done.
    - intros l stk Hstk. apply Hstack_item in Hstk.
      destruct Hstk as [Hstk ?]. split; last done. intros i Hi. specialize (Hstk i Hi).
      destruct tg, protector; naive_solver.
    - intros c. rewrite elem_of_union elem_of_singleton. intros [-> | Hin%Hcid_ag]; lia.
  }
  (* TODO: duplicated proof *)
  iPureIntro. destruct Hwf_t as [ ? Hstack_wf ? Hcid_ag]. constructor; simpl; try done.
  - intros l stk Hstk. apply Hstack_wf in Hstk.
    destruct Hstk as [Hstk ?]. split; last done. intros i Hi. specialize (Hstk i Hi).
    destruct tg, protector; naive_solver.
  - intros c. rewrite elem_of_union elem_of_singleton. intros [-> | Hin%Hcid_ag]; lia.
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
  iModIntro. iExists (#[ScCallId σ_s.(snc)])%E, [], (mkState σ_s.(shp) σ_s.(sst) ({[ σ_s.(snc) ]} ∪ σ_s.(scs)) σ_s.(snp) (S σ_s.(snc))).
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
  iDestruct "Hbor" as "(%M_call & %M_tag & %M_t & %M_s & (Hc & Htag_auth & Htag_t_auth & Htag_s_auth) & Htainted & Hpub_cid & #Hsrel & %Hcall_interp & %Htag_interp & %Hwf_s & %Hwf_t)".
  iMod (call_id_make_public with "Hpub_cid Hown") as "[#Hpub Hpub_cid]".
  iModIntro. iSplitR "Hsim".
  { iFrame "HP_t HP_s". iExists M_call, M_tag, M_t, M_s. iFrame. eauto. }
  iApply "Hsim".
  simpl. eauto.
Qed.

(** EndCall *)
Lemma bor_interp_end_call_own c σ_t σ_s :
  bor_interp sc_rel σ_t σ_s -∗
  c @@ ∅ ==∗ (* we need it to be empty to avoid tripping private locations *)
  ⌜c ∈ σ_t.(scs) ∧ c ∈ σ_s.(scs)⌝ ∗ bor_interp sc_rel (state_upd_calls (.∖ {[ c ]}) σ_t) (state_upd_calls (.∖ {[ c ]}) σ_s).
Proof.
  iIntros "(%M_call & %M_tag & %M_t & %M_s & (Hc & Htag_auth & Htag_t_auth & Htag_s_auth) & Htainted & Hpub_cid & #Hsrel & %Hcall_interp & %Htag_interp & %Hwf_s & %Hwf_t) Hcall".
  iPoseProof (ghost_map_lookup with "Hc Hcall") as "%Hlookup".
  iMod (ghost_map_delete with "Hc Hcall") as "Hc". iModIntro.
  iPoseProof (state_rel_calls_eq with "Hsrel") as "->".
  iSplitR.
  { destruct (Hcall_interp _ _ Hlookup) as (? & _). done. }
  iExists (delete c M_call), M_tag, M_t, M_s. iFrame.
  iSplitL "Hpub_cid".
  { iApply (pub_cid_interp_preserve_sub with "Hpub_cid"); simpl; [set_solver.. | done]. }
  iSplitL "Hsrel".
  { iDestruct "Hsrel" as "(Hdom_eq & Hsst_eq & Hsnp_eq & Hsnc_eq & %Hscs_eq & Hl)". rewrite /state_rel. cbn.
    iFrame "Hdom_eq Hsst_eq Hsnp_eq Hsnc_eq".
    iSplitR. { rewrite Hscs_eq. done. }
    iIntros (l Hl). iDestruct ("Hl" $! l with "[//]") as "[Hpub | (%t & %Hpriv)]".
    - iLeft. iApply "Hpub".
    - iRight. iPureIntro. exists t.
      destruct Hpriv as (tk & Htk & Hs & [-> | [-> (c' & Hin)]]).
      { exists tk_local. split_and!; eauto. }
      exists tk_unq. split_and!; [done.. | ]. right. split; first done.
      exists c'. destruct Hin as (M' & HM' & Hin). exists M'.
      assert (c ≠ c') as Hneq.
      { intros <-. simplify_eq. destruct Hin as (L & Hsome & _).
        rewrite lookup_empty in Hsome. done.
      }
      rewrite lookup_delete_ne; last done. done.
  }
  iSplitL.
  { iPureIntro. by apply call_set_interp_remove. }
  iSplitL.
  { iPureIntro. apply Htag_interp. }
  iSplitL.
  { iPureIntro. destruct Hwf_s. constructor; [done.. | ].
    intros c'. cbn. rewrite elem_of_difference. intros [Hin _]. eauto. }
  iPureIntro. destruct Hwf_t. constructor; [done.. | ].
  intros c'. cbn. rewrite elem_of_difference. intros [Hin _]. eauto.
Qed.

Lemma sim_endcall_own c π Φ :
  c @@ ∅ -∗ (* needs to be empty so we don't trip private locations *)
  #[☠] ⪯{π} #[☠] [{ Φ }] -∗
  EndCall #[ScCallId c] ⪯{π} EndCall #[ScCallId c] [{ Φ }].
Proof.
  iIntros "Hcall Hsim". iApply sim_lift_base_step_both. iIntros (P_t σ_t P_s σ_s T_s K_s) "((HP_t & HP_s & Hbor) & _ & _)".
  iMod (bor_interp_end_call_own with "Hbor Hcall") as "[%Hc_in Hbor]". iModIntro.
  iSplitR.
  { iPureIntro. do 3 eexists. eapply end_call_base_step. apply Hc_in. }
  iIntros (e_t' efs_t σ_t') "%Hhead".
  specialize (head_end_call_inv _ _ _ _ _ _ Hhead) as (_ & -> & -> & ->).
  iModIntro. iExists (#[☠])%E, [], (state_upd_calls (.∖ {[ c ]}) σ_s).
  iSplitR. { iPureIntro. eapply end_call_base_step. apply Hc_in. }
  iSplitR "Hsim"; first last.
  { iFrame "Hsim". done. }
  iFrame.
Qed.

Lemma bor_interp_end_call c σ_t σ_s :
  c ∈ σ_s.(scs) →
  bor_interp sc_rel σ_t σ_s -∗
  pub_cid c ==∗
  ⌜c ∈ σ_t.(scs)⌝ ∗ bor_interp sc_rel (state_upd_calls (.∖ {[ c ]}) σ_t) (state_upd_calls (.∖ {[ c ]}) σ_s).
Proof.
  iIntros (Hin_s) "(%M_call & %M_tag & %M_t & %M_s & (Hc & Htag_auth & Htag_t_auth & Htag_s_auth) & Htainted & Hpub_cid & #Hsrel & %Hcall_interp & %Htag_interp & %Hwf_s & %Hwf_t) Hcall".
  specialize (state_wf_cid_agree _ Hwf_s _ Hin_s) as Hlt_s.
  iPoseProof (state_rel_calls_eq with "Hsrel") as "%Hscs_eq".
  iPoseProof (state_rel_snc_eq with "Hsrel") as "%Hsnc_eq".
  iPoseProof (pub_cid_endcall with "Hcall Hpub_cid") as "[Hcall Hpub_cid]"; [done | lia | lia | ].

  (* duplicate with the proof for [bor_interp_endcall_own] *)
  iPoseProof (ghost_map_lookup with "Hc Hcall") as "%Hlookup".
  iMod (ghost_map_delete with "Hc Hcall") as "Hc". iModIntro.
  iPoseProof (state_rel_calls_eq with "Hsrel") as "->".
  iSplitR.
  { destruct (Hcall_interp _ _ Hlookup) as (? & _). done. }
  iExists (delete c M_call), M_tag, M_t, M_s. iFrame.
  iSplitL "Hpub_cid".
  { iApply (pub_cid_interp_preserve_sub with "Hpub_cid"); simpl; [set_solver.. | done]. }
  iSplitL "Hsrel".
  { iDestruct "Hsrel" as "(H1 & H2 & H3 & H4 & %H5 & H6)". rewrite /state_rel. cbn.
    iFrame "H1 H2 H3 H4".
    iSplitR. { rewrite H5. done. }
    iIntros (l Hl). iDestruct ("H6" $! l with "[//]") as "[Hpub | (%t & %Hpriv)]".
    - iLeft. iApply "Hpub".
    - iRight. iPureIntro. exists t.
      destruct Hpriv as (tk & Htk & Hs & [-> | [-> (c' & Hin)]]).
      { exists tk_local. split_and!; eauto. }
      exists tk_unq. split_and!; [done.. | ]. right. split; first done.
      exists c'. destruct Hin as (M' & HM' & Hin). exists M'.
      assert (c ≠ c') as Hneq.
      { intros <-. simplify_eq. destruct Hin as (L & Hsome & _).
        rewrite lookup_empty in Hsome. done.
      }
      rewrite lookup_delete_ne; last done. done.
  }
  iSplitL.
  { iPureIntro. by apply call_set_interp_remove. }
  iSplitL.
  { iPureIntro. apply Htag_interp. }
  iSplitL.
  { iPureIntro. destruct Hwf_s. constructor; [done.. | ].
    intros c'. cbn. rewrite elem_of_difference. intros [Hin _]. eauto. }
  iPureIntro. destruct Hwf_t. constructor; [done.. | ].
  intros c'. cbn. rewrite elem_of_difference. intros [Hin _]. eauto.
Qed.

Lemma sim_endcall π Φ c c' :
  sc_rel (ScCallId c') (ScCallId c) -∗
  #[☠] ⪯{π} #[☠] [{ Φ }] -∗
  EndCall #[ScCallId c'] ⪯{π} EndCall #[ScCallId c] [{ Φ }].
Proof.
  iIntros "#Hsc Hsim". iApply sim_lift_base_step_both. iIntros (P_t σ_t P_s σ_s T_s K_s) "((HP_t & HP_s & Hbor) & %Hpool & %Hsafe)".
  specialize (pool_safe_implies Hsafe Hpool) as (c0 & [= <-] & Hin_s).
  iPoseProof (sc_rel_cid_source with "Hsc") as "[%Heq Hpub]". injection Heq as [= ->].
  iMod (bor_interp_end_call with "Hbor Hpub") as "[%Hin_t Hbor]"; first done. iModIntro.
  iSplitR.
  { iPureIntro. do 3 eexists. eapply end_call_base_step. done. }
  iIntros (e_t' efs_t σ_t') "%Hhead".
  specialize (head_end_call_inv _ _ _ _ _ _ Hhead) as (_ & -> & -> & ->).
  iModIntro. iExists (#[☠])%E, [], (state_upd_calls (.∖ {[ c ]}) σ_s).
  iSplitR. { iPureIntro. eapply end_call_base_step. done. }
  iSplitR "Hsim"; first last.
  { iFrame "Hsim". done. }
  iFrame.
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
