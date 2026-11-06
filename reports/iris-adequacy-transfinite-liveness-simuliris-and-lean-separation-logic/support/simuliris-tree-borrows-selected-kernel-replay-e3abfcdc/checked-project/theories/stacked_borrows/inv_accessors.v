From iris.proofmode Require Export proofmode.
From iris.base_logic.lib Require Import ghost_map.
From simuliris.base_logic Require Export gen_sim_prog.
From simuliris.simulation Require Export slsls.
From simuliris.simulation Require Import lifting.
From simuliris.stacked_borrows Require Import tkmap_view.
From simuliris.stacked_borrows Require Export defs.
From simuliris.stacked_borrows Require Import steps_progress steps_retag steps_inv logical_state.



(** Lemmas / Accessors *)
Add Printing Constructor state item.
Section lemmas.
  Context `{bor_stateGS Σ}.
  Local Notation bor_interp := (bor_interp sc_rel).

  Implicit Types
    (l : loc) (sc : scalar).

  Lemma init_mem_dom_L l n h :
    dom (init_mem l n h) = dom h ∪ dom (init_mem l n ∅).
  Proof. apply set_eq. intros l'. rewrite init_mem_dom. done. Qed.

  Lemma fresh_block_det σ_s σ_t :
    dom σ_s.(shp) = dom σ_t.(shp) →
    fresh_block σ_s.(shp) = fresh_block σ_t.(shp).
  Proof. rewrite /fresh_block. intros ->. done. Qed.

  Lemma free_mem_dom σ_t σ_s l n :
    dom σ_t.(shp) = dom σ_s.(shp) →
    dom (free_mem l n σ_t.(shp)) = dom (free_mem l n σ_s.(shp)).
  Proof.
    intros Hdom. induction n as [ | n IH] in l |-*; first done.
    simpl. rewrite !dom_delete_L IH. done.
  Qed.

  Lemma init_stack_preserve σ n :
    let l := (fresh_block σ.(shp), 0) in
    let nt := σ.(snp) in
    let α' := init_stacks σ.(sst) l n (Tagged nt) in
    state_wf σ →
    ∀ l' stk, σ.(sst) !! l' = Some stk → α' !! l' = Some stk.
  Proof.
    intros l nt α' Hwf l' stk Hl'.
    rewrite (proj2 (init_stacks_lookup _ _ _ _) l'); first done.
    intros i Hi ->.
    specialize (elem_of_dom σ.(sst) ((fresh_block (shp σ), 0) +ₗ i)).
    rewrite Hl'. intros (_ &Ha). specialize (Ha ltac:(eauto)).
    move : Ha. rewrite -state_wf_dom; last done.
    apply is_fresh_block.
  Qed.

  Lemma init_mem_preserve σ n :
    let l := (fresh_block σ.(shp), 0) in
    let nt := σ.(snp) in
    let h' := init_mem l n σ.(shp) in
    ∀ l' sc, σ.(shp) !! l' = Some sc → h' !! l' = Some sc.
  Proof.
    intros l nt h' l' sc Hsc.
    rewrite (proj2 (init_mem_lookup _ _ _) l'); first done.
    intros i Hi ->.
    specialize (elem_of_dom σ.(shp) ((fresh_block (shp σ), 0) +ₗ i)).
    rewrite Hsc. intros (_ &Ha). specialize (Ha ltac:(eauto)).
    move : Ha. apply is_fresh_block.
  Qed.

  Lemma loc_controlled_alloc_update σ l' n (t : ptr_id) (tk : tag_kind) sc :
    let l := (fresh_block σ.(shp), 0) in
    let nt := σ.(snp) in
    let α' := init_stacks σ.(sst) l n (Tagged nt) in
    state_wf σ →
    nt ≠ t →
    loc_controlled l' t tk sc σ →
    loc_controlled l' t tk sc (mkState (init_mem l n σ.(shp)) α' σ.(scs) (S σ.(snp)) σ.(snc)).
  Proof.
    intros l nt α' Hwf Hne Hcontrolled Hpre.
    assert (∀ l' stk, α' !! l' = Some stk → stk = init_stack (Tagged nt) ∨ σ.(sst) !! l' = Some stk) as Hα'.
    { intros l'' stk Hl'.
      specialize (init_stacks_lookup_case _ _ _ _ _ _ Hl') as [(Hstk & _) | (i & Hi & ->)]; first by eauto.
      left. rewrite (proj1 (init_stacks_lookup _ _ _ _) i Hi) in Hl'.
      injection Hl' as [= <-]. done.
    }
    assert (bor_state_pre l' t tk σ) as [Hown Hmem]%Hcontrolled.
    { destruct tk; last done.
      all: destruct Hpre as (stk & pm & opro & [-> | Hstk]%Hα' & Hit & ?); simpl in *; last by eauto 8.
      all: exfalso; move : Hit; rewrite list_elem_of_singleton; injection 1; congruence.
    }
    simpl. split.
    - destruct tk.
      + destruct Hown as (stk & Hstk & ?). exists stk. split; last done. apply init_stack_preserve; done.
      + destruct Hown as (stk & Hstk & ?). exists stk. split; last done. apply init_stack_preserve; done.
      + apply init_stack_preserve; done.
    - apply init_mem_preserve. done.
  Qed.

  Lemma state_rel_alloc_update σ_t σ_s M_tag M_t M_t' M_call l n tk :
    let nt := σ_t.(snp) in
    (∀ t, is_Some (M_tag !! t) → t ≠ nt) →
    state_rel sc_rel M_tag M_t M_call σ_t σ_s -∗
    state_rel sc_rel (<[nt := (tk, ())]> M_tag) (M_t' ∪ M_t) M_call
      (mkState (init_mem l n (shp σ_t)) (init_stacks (sst σ_t) l n (Tagged nt)) (scs σ_t) (S σ_t.(snp)) (snc σ_t))
      (mkState (init_mem l n (shp σ_s)) (init_stacks (sst σ_s) l n (Tagged nt)) (scs σ_s) (S (snp σ_s)) (snc σ_s)).
  Proof.
    intros nt Hneq. iIntros "(%Hdom_eq & %Hsst_eq & %Hsnp_eq & %Hsnc_eq & %Hscs_eq & Hstate)".
    iSplitR. { simpl. rewrite !(init_mem_dom_L _ _ (shp _)) Hdom_eq. iPureIntro. set_solver. }
    simpl. rewrite Hsst_eq. iSplitR; first done.
    iSplitR; first by rewrite Hsnp_eq. do 2 (iSplitR; first done).
    iIntros (l' (s & [(Heq & Hi) | (i & Hi & ->)]%init_mem_lookup_case)).
    + (* old location *)
      iDestruct ("Hstate" $! l' with "[]") as "[Hpub | (%t & %Hpriv)]".
      { eauto. }
      * iLeft. simpl. iIntros (sc_t Hsc_t). simpl in Hsc_t.
        rewrite (proj2 (init_mem_lookup _ n _) l' Hi) in Hsc_t. simplify_eq.
        iDestruct ("Hpub" $! s with "[//]") as (sc_s Hsc_s) "Hscrel".
        iExists sc_s. iSplit; last done. iPureIntro.
        by rewrite (proj2 (init_mem_lookup _ n _) l' Hi).
      * iRight. iPureIntro. exists t.
        destruct Hpriv as (tk' & Htk & Hs & ?). exists tk'. split_and!; [ | | done].
        { rewrite lookup_insert_ne; first done. specialize (Hneq t ltac:(eauto)). done. }
        rewrite lookup_union_is_Some. eauto.
    + (* new location *)
      iLeft. rewrite /pub_loc /=. rewrite !(proj1 (init_mem_lookup _ _ _)); [ | done | done].
      iIntros (? [= <-]). iExists ☠%S. iSplit; done.
  Qed.

  Lemma call_set_interp_alloc_update σ n M_call :
    state_wf σ →
    let nt := σ.(snp) in
    let l := (fresh_block σ.(shp), 0) in
    call_set_interp M_call σ →
    call_set_interp M_call (mkState (init_mem l n (shp σ)) (init_stacks (sst σ) l n (Tagged nt)) (scs σ) (S σ.(snp)) (snc σ)).
  Proof.
    intros Hwf nt l Hcall_interp c M' [? HM']%Hcall_interp. simpl. split; first done.
    intros t L HL. specialize (HM' _ _ HL) as (?& HL'). split; first lia. intros l' Hl'.
    specialize (HL' l' Hl') as (stk & pm & Hstk & Hit & ?).
    exists stk, pm. split_and!; [ | done..].
    apply init_stack_preserve; done.
  Qed.

  Lemma loc_controlled_alloc_local σ l nt n l' sc :
    array_tag_map l nt (replicate n ScPoison) !! (nt, l') = Some sc →
    loc_controlled l' nt tk_local sc (mkState (init_mem l n σ.(shp)) (init_stacks σ.(sst) l n (Tagged nt)) σ.(scs) (S σ.(snp)) σ.(snc)).
  Proof.
    intros Hsc.
    specialize (array_tag_map_lookup2 l nt _ nt l' ltac:(eauto)) as [_ (i & Hi & ->)].
    intros _.
    rewrite array_tag_map_lookup_Some in Hsc; last done.
    apply lookup_replicate in Hsc as [-> Hi']. split.
    * simpl. rewrite (proj1 (init_stacks_lookup _ _ _ _)); done.
    * simpl. rewrite (proj1 (init_mem_lookup _ _ _ )); done.
  Qed.

  Lemma bor_interp_alloc_local σ_t σ_s T :
    let l_t := (fresh_block σ_t.(shp), 0) in
    let l_s := (fresh_block σ_s.(shp), 0) in
    let nt := σ_t.(snp) in
    state_wf (mkState (init_mem l_t (tsize T) σ_t.(shp)) (init_stacks σ_t.(sst) l_t (tsize T) (Tagged nt)) σ_t.(scs) (S σ_t.(snp)) σ_t.(snc)) →
    state_wf (mkState (init_mem l_s (tsize T) σ_s.(shp)) (init_stacks σ_s.(sst) l_s (tsize T) (Tagged nt)) σ_s.(scs) (S σ_s.(snp)) σ_s.(snc)) →
    bor_interp σ_t σ_s ==∗
    bor_interp
      (mkState (init_mem l_t (tsize T) σ_t.(shp)) (init_stacks σ_t.(sst) l_t (tsize T) (Tagged nt)) σ_t.(scs) (S σ_t.(snp)) σ_t.(snc))
      (mkState (init_mem l_s (tsize T) σ_s.(shp)) (init_stacks σ_s.(sst) l_s (tsize T) (Tagged nt)) σ_s.(scs) (S σ_s.(snp)) σ_s.(snc)) ∗
      nt $$ tk_local ∗
      l_t ↦t∗[tk_local]{nt} replicate (tsize T) ScPoison ∗
      l_s ↦s∗[tk_local]{nt} replicate (tsize T) ScPoison.
  Proof.
    intros l_t l_s nt Hwf_t' Hwf_s'.
    iIntros "(% & %M_tag & %M_t & %M_s & (Hcall_auth & Htag_auth & Ht_auth & Hs_auth) & Htainted & Hpub_cid & #Hstate & %Hcall_interp & %Htag_interp & %Hwf_s & %Hwf_t)".
    destruct Htag_interp as (Htag_interp & Ht_dom& Hs_dom).
    assert (M_tag !! nt = None) as M_tag_none.
    { destruct (M_tag !! nt) as [[? []] | ]eqn:Hs; last done.
      apply Htag_interp in Hs as (? & ? & _). lia.
    }
    assert (∀ l, M_t !! (nt, l) = None).
    { intros l. destruct (M_t !! (nt, l)) eqn:Hl; last done.
      specialize (Ht_dom nt l ltac:(eauto)) as (? & ?); congruence.
    }
    assert (∀ l, M_s !! (nt, l) = None).
    { intros l. destruct (M_s !! (nt, l)) eqn:Hl; last done.
      specialize (Hs_dom nt l ltac:(eauto)) as (? & ?); congruence.
    }
    (* update ghost state *)
    iMod (ghost_map_array_tag_insert _ _ (replicate (tsize T) ScPoison ) nt l_t with "Ht_auth") as "[Ht_mem Ht_auth]"; first done.
    iMod (ghost_map_array_tag_insert _ _ (replicate (tsize T) ScPoison ) nt l_s with "Hs_auth") as "[Hs_mem Hs_auth]"; first done.
    iMod (tkmap_insert tk_local nt () with "Htag_auth") as "[Htag_auth Hnt]"; first done.
    iModIntro.

    iFrame "Hnt Hs_mem Ht_mem".
    iExists _, _, _, _. iFrame "Htag_auth Ht_auth Hs_auth Hcall_auth". simpl.
    iPoseProof (state_rel_get_pure with "Hstate") as "%Hp".
    iPoseProof (state_rel_dom_eq with "Hstate") as "%Hdom_eq".
    destruct Hp as (Hsst_eq & Hsnp_eq & Hsnc_eq & Hscs_eq).
    assert (l_s = l_t) as Hl_eq.
    { subst l_s l_t. rewrite (fresh_block_det _ _ Hdom_eq). done. }
    iSplitL "Htainted". { subst nt. rewrite -Hsnp_eq. by iApply tag_tainted_interp_alloc. }
    iSplitL "Hpub_cid". { iApply (pub_cid_interp_preserve_sub with "Hpub_cid"); simpl; done. }
    iSplitL.
    { (* state rel *)
      rewrite Hl_eq. iApply state_rel_alloc_update; last done.
      intros t ([?[]] & Hs). specialize (Htag_interp _ _ Hs) as (? & ? & _). lia.
    }
    iSplitL.
    { iPureIntro. apply call_set_interp_alloc_update; done. }
    iSplitL.
    { (* tag interp *)
      iPureIntro. split_and!.
      { simpl. intros t tk. rewrite lookup_insert_Some. intros [[<- [= <-]] | [Hneq Hsome]].
        - (* new tag: under local control *)
          split_and!; [ lia | lia | | |].
          + intros l' sc_t Hsc_t%lookup_union_Some_inv_l; last done. by apply loc_controlled_alloc_local.
          + intros l' sc_t Hsc_s%lookup_union_Some_inv_l; last done. by apply loc_controlled_alloc_local.
          + apply dom_agree_on_tag_union; first last.
            { apply dom_agree_on_tag_not_elem; done. }
            rewrite Hl_eq. apply dom_agree_on_tag_array_tag_map.
            by rewrite length_replicate.
        - (* old tag *)
          specialize (Htag_interp _ _ Hsome) as (? & ? & Hcontrol_t & Hcontrol_s & Hag).
          split_and!; [lia | lia | .. ].
          + intros l' sc_t Hsc_t. apply loc_controlled_alloc_update; [done | done| ].
            rewrite lookup_union_r in Hsc_t; first by apply Hcontrol_t.
            apply array_tag_map_lookup_None. lia.
          + intros l' sc_s Hsc_s. subst nt. rewrite -Hsnp_eq. apply loc_controlled_alloc_update; [done | lia | ].
            rewrite lookup_union_r in Hsc_s; first by apply Hcontrol_s.
            apply array_tag_map_lookup_None. lia.
          + apply dom_agree_on_tag_union; last done.
            rewrite Hl_eq. apply dom_agree_on_tag_not_elem.
            all: intros l; rewrite array_tag_map_lookup_None; done.
      }
      all: intros t l'; rewrite lookup_insert_is_Some' lookup_union_is_Some;
        intros [[-> _]%array_tag_map_lookup2 | ?]; eauto.
    }
    eauto.
  Qed.

  (** Read lemmas *)
    Lemma bor_interp_readN_target_local σ_t σ_s (t : ptr_id) l scs :
    bor_interp σ_t σ_s -∗
    l ↦t∗[tk_local]{t} scs -∗
    t $$ tk_local -∗
    ⌜∀ i : nat, (i < length scs)%nat → σ_t.(shp) !! (l +ₗ i) = scs !! i⌝ ∗
    ⌜∀ i:nat, (i < length scs)%nat → bor_state_own (l +ₗ i) t tk_local σ_t⌝.
  Proof.
    iIntros "(% & % & % & % & (Hc & Htag_auth & Htag_t_auth & Htag_s_auth) & ? & ? & Hsrel & ? & %Htag_interp & %Hwf_s & %Hwf_t)".
    iIntros "Hp Htag".
    iPoseProof (tkmap_lookup with "Htag_auth Htag") as "%Htag_lookup".
    destruct Htag_interp as (Htag_interp & _ & _).
    destruct (Htag_interp _ _ Htag_lookup) as (_ & _ & Ht & Hs & Hagree).
    iPoseProof (ghost_map_array_tag_lookup with "Htag_t_auth Hp") as "%Ht_lookup".
    iPureIntro.
    enough (∀ i: nat, (i < length scs)%nat → σ_t.(shp) !! (l +ₗ i) = scs !! i ∧ σ_t.(sst) !! (l +ₗ i) = Some [mkItem Unique (Tagged t) None]) as Hsingle.
    { split_and!; [ apply Hsingle..]. }
    intros i Hi.
    specialize (Ht_lookup i Hi). rewrite list_lookup_lookup_total in Ht_lookup; first last.
    { by apply lookup_lt_is_Some_2. }
    specialize (Ht _ _ Ht_lookup) as Hcontrol.
    specialize (loc_controlled_local _ _ _ _ Hcontrol) as (Hstack & Hmem).
    split_and!.
    - rewrite Hmem. rewrite list_lookup_lookup_total; [done | by apply lookup_lt_is_Some_2].
    - done.
  Qed.

  Lemma bor_interp_readN_target_protected σ_t σ_s (t : ptr_id) tk l v_t c M :
    (∀ i: nat, (i < length v_t)%nat → call_set_in M t (l +ₗ i)) →
    bor_interp σ_t σ_s -∗
    l ↦t∗[tk]{t} v_t -∗
    t $$ tk -∗
    c @@ M -∗
    ⌜∀ i : nat, (i < length v_t)%nat → σ_t.(shp) !! (l +ₗ i) = v_t !! i⌝ ∗
    ⌜∀ i:nat, (i < length v_t)%nat → bor_state_own (l +ₗ i) t tk σ_t⌝.
  Proof.
    iIntros (Hprot) "(% & % & % & % & (Hc & Htag_auth & Htag_t_auth & Htag_s_auth) & Htainted & Hpub_cid & Hsrel & %Hcall & %Htag_interp & %Hwf_s & %Hwf_t)".
    iIntros "Hp Htag Hcall".
    iPoseProof (tkmap_lookup with "Htag_auth Htag") as "%Htag_lookup".
    destruct Htag_interp as (Htag_interp & _ & _).
    destruct (Htag_interp _ _ Htag_lookup) as (_ & _ & Ht & Hs & Hagree).
    iPoseProof (ghost_map_array_tag_lookup with "Htag_t_auth Hp") as "%Ht_lookup".
    iPoseProof (ghost_map_lookup with "Hc Hcall") as "%Hc_lookup".
    iPureIntro.
    enough (∀ i: nat, (i < length v_t)%nat → σ_t.(shp) !! (l +ₗ i) = v_t !! i ∧ bor_state_own (l +ₗ i) t tk σ_t) as Hsingle.
    { split_and!; [ apply Hsingle..]. }
    intros i Hi.
    specialize (Ht_lookup i Hi). rewrite list_lookup_lookup_total in Ht_lookup; first last.
    { by apply lookup_lt_is_Some_2. }
    specialize (Ht _ _ Ht_lookup) as Hcontrol.
    assert (bor_state_pre (l +ₗ i) t tk σ_t) as Hpre.
    { specialize (Hprot i Hi).
      specialize (call_set_interp_access _ _ _ _ _ Hcall ltac:(exists M; done)). apply loc_protected_bor_state_pre.
    }
    specialize (Hcontrol Hpre) as [Hown Hmem].
    split_and!; [| done ].
    - rewrite Hmem. rewrite list_lookup_lookup_total; [done | ]. by apply lookup_lt_is_Some_2.
  Qed.

  Lemma bor_interp_readN_target σ_t σ_s (t : ptr_id) tk l v_t :
    bor_interp σ_t σ_s -∗
    l ↦t∗[tk]{t} v_t -∗
    t $$ tk -∗
    ⌜∀ i:nat, (i < length v_t)%nat → loc_controlled (l +ₗ i) t tk (v_t !!! i) σ_t⌝.
  Proof.
    iIntros "(% & % & % & % & (Hc & Htag_auth & Htag_t_auth & Htag_s_auth) & Htainted & Hpub_cid & Hsrel & %Hcall & %Htag_interp & %Hwf_s & %Hwf_t)".
    iIntros "Hp Htag".
    iPoseProof (tkmap_lookup with "Htag_auth Htag") as "%Htag_lookup".
    destruct Htag_interp as (Htag_interp & _ & _).
    destruct (Htag_interp _ _ Htag_lookup) as (_ & _ & Ht & _ & _).
    iPoseProof (ghost_map_array_tag_lookup with "Htag_t_auth Hp") as "%Ht_lookup".
    iPureIntro.
    intros i Hi.
    specialize (Ht_lookup i Hi). rewrite list_lookup_lookup_total in Ht_lookup; first last.
    { by apply lookup_lt_is_Some_2. }
    apply Ht. done.
  Qed.

  Lemma bor_interp_readN_source σ_t σ_s (t : ptr_id) tk l v_s :
    bor_interp σ_t σ_s -∗
    l ↦s∗[tk]{t} v_s -∗
    t $$ tk -∗
    ⌜∀ i:nat, (i < length v_s)%nat → loc_controlled (l +ₗ i) t tk (v_s !!! i) σ_s⌝.
  Proof.
    iIntros "(% & % & % & % & (Hc & Htag_auth & Htag_t_auth & Htag_s_auth) & Htainted & Hpub_cid & Hsrel & %Hcall & %Htag_interp & %Hwf_s & %Hwf_t)".
    iIntros "Hp Htag".
    iPoseProof (tkmap_lookup with "Htag_auth Htag") as "%Htag_lookup".
    destruct Htag_interp as (Htag_interp & _ & _).
    destruct (Htag_interp _ _ Htag_lookup) as (_ & _ & _ & Hs & _).
    iPoseProof (ghost_map_array_tag_lookup with "Htag_s_auth Hp") as "%Hs_lookup".
    iPureIntro. intros i Hi.
    specialize (Hs_lookup i Hi). rewrite list_lookup_lookup_total in Hs_lookup; first last.
    { by apply lookup_lt_is_Some_2. }
    apply Hs. done.
  Qed.

  Lemma bor_interp_readN_source_protected σ_t σ_s (t : ptr_id) tk l v_s c M :
    (∀ i: nat, (i < length v_s)%nat → call_set_in M t (l +ₗ i)) →
    bor_interp σ_t σ_s -∗
    l ↦s∗[tk]{t} v_s -∗
    t $$ tk -∗
    c @@ M -∗
    ⌜∀ i : nat, (i < length v_s)%nat → σ_s.(shp) !! (l +ₗ i) = v_s !! i⌝ ∗
    ⌜∀ i:nat, (i < length v_s)%nat → bor_state_own (l +ₗ i) t tk σ_s⌝.
  Proof.
    iIntros (Hprot) "(% & % & % & % & (Hc & Htag_auth & Htag_t_auth & Htag_s_auth) & Htainted & Hpub_cid & Hsrel & %Hcall & %Htag_interp & %Hwf_s & %Hwf_t)".
    iIntros "Hp Htag Hcall".
    iPoseProof (tkmap_lookup with "Htag_auth Htag") as "%Htag_lookup".
    destruct Htag_interp as (Htag_interp & _ & _).
    destruct (Htag_interp _ _ Htag_lookup) as (_ & _ & Ht & Hs & Hagree).
    iPoseProof (ghost_map_array_tag_lookup with "Htag_s_auth Hp") as "%Hs_lookup".
    iPoseProof (ghost_map_lookup with "Hc Hcall") as "%Hc_lookup".
    iPoseProof (loc_protected_by_source with "Hsrel") as "%Hprots". iPureIntro.
    enough (∀ i: nat, (i < length v_s)%nat → σ_s.(shp) !! (l +ₗ i) = v_s !! i ∧ bor_state_own (l +ₗ i) t tk σ_s) as Hsingle.
    { split_and!; [ apply Hsingle..]. }
    intros i Hi.
    specialize (Hs_lookup i Hi). rewrite list_lookup_lookup_total in Hs_lookup; first last.
    { by apply lookup_lt_is_Some_2. }
    specialize (Hs _ _ Hs_lookup) as Hcontrol.
    assert (bor_state_pre (l +ₗ i) t tk σ_s) as Hpre.
    { specialize (Hprot i Hi).
      specialize (call_set_interp_access _ _ _ _ _ Hcall ltac:(exists M; done)) as ?%Hprots.
      by eapply loc_protected_bor_state_pre.
    }
    specialize (Hcontrol Hpre) as [Hown Hmem].
    split_and!; [| done ].
    rewrite Hmem. rewrite list_lookup_lookup_total; [done | ]. by apply lookup_lt_is_Some_2.
  Qed.

  Lemma bor_interp_readN_source_local σ_t σ_s (t : ptr_id) l v :
    bor_interp σ_t σ_s -∗
    l ↦s∗[tk_local]{t} v -∗
    t $$ tk_local -∗
    ⌜∀ i : nat, (i < length v)%nat → σ_s.(shp) !! (l +ₗ i) = v !! i⌝ ∗
    ⌜∀ i:nat, (i < length v)%nat → bor_state_own (l +ₗ i) t tk_local σ_s⌝.
  Proof.
    iIntros "(% & % & % & % & (Hc & Htag_auth & Htag_t_auth & Htag_s_auth) & ? & ? & Hsrel & ? & %Htag_interp & %Hwf_s & %Hwf_t)".
    iIntros "Hp Htag".
    iPoseProof (tkmap_lookup with "Htag_auth Htag") as "%Htag_lookup".
    destruct Htag_interp as (Htag_interp & _ & _).
    destruct (Htag_interp _ _ Htag_lookup) as (_ & _ & Ht & Hs & Hagree).
    iPoseProof (ghost_map_array_tag_lookup with "Htag_s_auth Hp") as "%Hs_lookup".
    iPureIntro.
    enough (∀ i: nat, (i < length v)%nat → σ_s.(shp) !! (l +ₗ i) = v !! i ∧ σ_s.(sst) !! (l +ₗ i) = Some [mkItem Unique (Tagged t) None]) as Hsingle.
    { split_and!; [ apply Hsingle..]. }
    intros i Hi.
    specialize (Hs_lookup i Hi). rewrite list_lookup_lookup_total in Hs_lookup; first last.
    { by apply lookup_lt_is_Some_2. }
    specialize (Hs _ _ Hs_lookup) as Hcontrol.
    specialize (loc_controlled_local _ _ _ _ Hcontrol) as (Hstack & Hmem).
    split_and!.
    - rewrite Hmem. rewrite list_lookup_lookup_total; [done | by apply lookup_lt_is_Some_2].
    - done.
  Qed.

  (** * Write lemmas *)
  Lemma loc_controlled_write_update σ bor tk l l' n α' sc v t :
    state_wf σ →
    (bor = Tagged t ∧ (∃ i:nat, l = l' +ₗ i ∧ (i < n)%nat) → tk = tk_pub) →
    memory_written σ.(sst) σ.(scs) l' bor n = Some α' →
    length v = n →
    loc_controlled l t tk sc σ →
    loc_controlled l t tk sc (mkState (write_mem l' v σ.(shp)) α' σ.(scs) σ.(snp) σ.(snc)).
  Proof.
    rewrite /loc_controlled //= => Hwf Hpub Hstack Hlen Hcontrol.
    destruct (write_mem_lookup_case l' v σ.(shp) l) as [(i & Hi & -> & Hwrite_i) | (Hi & ->)];
        first last.
    { (* l is NOT written to *)
      destruct (for_each_lookup _ _ _ _ _ Hstack) as (_ & _ & Hstack_eq).
      rewrite /bor_state_pre /bor_state_own. rewrite !Hstack_eq. 2: intros; apply Hi; lia.
      apply Hcontrol.
    }
    (* considering one of the written-to locations *)
    intros Hpre.
    specialize (for_each_access1 _ _ _ _ _ _ _ Hstack) as Hsub.
    destruct Hcontrol as (Hown & Hmem).
    { destruct tk; simpl in *; [ | | done].
      all: destruct Hpre as (stk & pm & opro & (stk' & -> & Hsubl & _)%Hsub & Hit & Hpm).
      all: apply Hsubl in Hit as ([pm' tg' opro'] & Hit2 & Htg & Hprot & Hperm).
      all: exists stk', pm', opro'; simpl in *; rewrite Htg.
      all:  split_and!; [done | done | rewrite Hperm; done].
    }
    (* we now lead this to a contradiction: the write was UB/the tags are contradictory *)
    specialize (for_each_lookup _ _ _ _ _ Hstack) as (Ha & _).
    destruct tk; simpl in *.
    * (* public *)
      destruct Hpre as (stk' & pm & opro & Hstk' & Hit & Hpm).
      exfalso. destruct Hown as (stk & Hstk & Hactive).
      specialize (Ha i _ ltac:(lia) Hstk) as (stk'' & Hstk'' & Hacc).
      destruct access1 as [[n' ?] | ] eqn:Hacc_eq; last done. injection Hacc as [= ->].
      simplify_eq.
      eapply access1_write_remove_incompatible_active_SRO; [ | done | apply Hacc_eq | done ].
      by eapply Hwf.
    * (* unique *)
      destruct Hpre as (stk' & pm & opro & Hstk' & Hit & Hpm).
      exfalso. destruct Hown as (stk & Hstk & Hprot).
      specialize (Ha i _ ltac:(lia) Hstk) as (stk'' & Hstk'' & Hacc).
      destruct access1 as [[n' ?] | ] eqn:Hacc_eq; last done. injection Hacc as [= ->].
      simplify_eq.
      destruct Hprot as (opro' & stk'' & ->).
      eapply access1_write_remove_incompatible_head;
        [ | eexists; eexists; reflexivity | apply Hacc_eq | | done].
      { by eapply Hwf. }
      (* contradiction, since t is public *)
      intros <-. enough (tk_unq = tk_pub) by congruence.
      apply Hpub. split; first done. eauto.
    * (* local *)
      exfalso.
      specialize (Ha i _ ltac:(lia) Hown) as (stk'' & Hstk'' & Hacc).
      destruct access1 as [[n' ?] | ] eqn:Hacc_eq; last done. injection Hacc as [= ->].
      specialize (access1_in_stack _ _ _ _ _ _ Hacc_eq) as (it & ->%list_elem_of_singleton & Htg & _).
      (* contradiction, since t is public *)
      simpl in Htg. subst bor. enough (tk_local = tk_pub) by congruence.
      apply Hpub. split; first done. exists i. split; first done. lia.
  Qed.

  Lemma state_upd_mem_compose f g σ :
    state_upd_mem f (state_upd_mem g σ) = state_upd_mem (f ∘ g) σ.
  Proof. destruct σ. done. Qed.

  Lemma write_mem_insert_commute_1 l l' v sc M :
    l.2 < l'.2 →
    <[ l := sc ]> (write_mem l' v M) = write_mem l' v (<[ l := sc ]> M).
  Proof.
    induction v as [|? v IH] in l, l', sc, M |-*; cbn; first done.
    intros Hl. rewrite (IH l (l' +ₗ 1)); first last.
    { destruct l', l; cbn in *; lia. }
    rewrite insert_insert_ne; first done. intros ->; lia.
  Qed.
  Lemma write_mem_head l sc v M :
    <[ l := sc ]> (write_mem (l +ₗ 1) v M) = write_mem l (sc :: v) M.
  Proof. rewrite write_mem_insert_commute_1; last by destruct l; cbn; lia. done. Qed.

  Global Instance state_upd_mem_proper : Proper ((eq ==> eq) ==> eq ==> eq) state_upd_mem.
  Proof.
    intros f g Heq ? σ ->. destruct σ as [ mem ]. by rewrite /state_upd_mem (Heq mem mem eq_refl).
  Qed.
  Lemma state_upd_write_mem_head sc v l σ :
    state_upd_mem (<[ l := sc ]> ∘ write_mem (l +ₗ 1) v) σ = state_upd_mem (write_mem l (sc :: v)) σ.
  Proof. destruct σ. rewrite /state_upd_mem. cbn. by rewrite write_mem_head. Qed.

  Lemma state_wf_upd_mem σ l sc :
    is_Some (σ.(shp) !! l) →
    state_wf σ →
    state_wf (state_upd_mem (<[l := sc]>) σ).
  Proof.
    intros Hs []. constructor; try done.
    rewrite dom_insert //.
    have ->: {[l]} ∪ dom (shp σ) ≡ dom (shp σ); last done.
    split; rewrite elem_of_union; last by eauto.
    intros [ ->%elem_of_singleton_1 | ]; last done.
    by apply elem_of_dom.
    Qed.

  Lemma bor_interp_write_target_local σ_t σ_s (t : ptr_id) l sc sc' :
    bor_interp σ_t σ_s -∗
    l ↦t[tk_local]{t} sc -∗
    t $$ tk_local ==∗
    bor_interp (state_upd_mem (<[l := sc']>) σ_t) σ_s ∗
    l ↦t[tk_local]{t} sc' ∗
    t $$ tk_local.
  Proof.
    iIntros "(%M_call & %M_tag & %M_t & %M_s & (Hc & Htag_auth & Htag_t_auth & Htag_s_auth) & Htainted & Hpub_cid & Hsrel & ? & %Htag_interp & %Hwf_s & %Hwf_t)".
    iIntros "Hp Htag".
    iPoseProof (tkmap_lookup with "Htag_auth Htag") as "%Htag_lookup".
    destruct Htag_interp as (Htag_interp & Ht_dom & Hs_dom).
    destruct (Htag_interp _ _ Htag_lookup) as (_ & _ & Ht & Hs & Hagree).
    iPoseProof (ghost_map_lookup with "Htag_t_auth Hp") as "%Ht_lookup".
    specialize (Ht _ _ Ht_lookup) as Hcontrol.
    specialize (loc_controlled_local _ _ _ _ Hcontrol) as (Hstack & Hmem).

    iMod (ghost_map_update sc' with "Htag_t_auth Hp") as "[Htag_t_auth $]".
    iModIntro. iFrame "Htag". rewrite /bor_interp.
    iExists M_call, M_tag, (<[(t, l):=sc']> M_t), M_s.
    iFrame. cbn. iSplitL "Hsrel".
    { iApply (state_rel_upd_priv_target with "Hsrel").
      - eauto.
      - exists tk_local. split_and!; [done | by eauto | by left ].
    }
    iSplitL; first last.
    { repeat iSplitL; [ done.. | ].
      iPureIntro. apply state_wf_upd_mem; [by eauto | done].
    }

    iPureIntro.
    split_and!.
    - intros t' tk' (? & ? & H')%Htag_interp. do 2 (split; first done).
      destruct H' as (Ha_t & Ha_s & Hagree').
      split_and!; [ | done | ].
      + intros l' sc_t.
        destruct (decide (t = t')) as [<- | Hneq]; first last.
        { rewrite lookup_insert_ne; last congruence. intros Hsc_t.
          destruct (decide (l' = l)) as [-> | Hneq_loc].
          { (* this is fine as tag t has local ownership: t' doesn't have any control *)
            eapply loc_controlled_local_authoritative; [ | by apply Ha_t | done].
            eapply loc_controlled_mem_insert. done.
          }
          apply loc_controlled_mem_insert_ne; [done | by apply Ha_t].
        }
        revert Ha_t.
        destruct (decide (l' = l)) as [-> | Hneq_loc] => Ha_t.
        * rewrite lookup_insert_eq => [= ->]. by eapply loc_controlled_mem_insert, Ha_t.
        * rewrite lookup_insert_ne; last congruence. intros ?.
          eapply loc_controlled_mem_insert_ne; [done | by apply Ha_t].
      + destruct (decide (t = t')) as [<- | Hneq].
        * eapply dom_agree_on_tag_upd_target; eauto.
        * eapply dom_agree_on_tag_upd_ne_target; eauto.
    - intros t' l'. rewrite lookup_insert_is_Some. intros [[= <- <-] | [_ ?%Ht_dom]]; last done. eauto.
    - done.
  Qed.

  Lemma bor_interp_writeN_target_local σ_t σ_s (t : ptr_id) l v v' :
    bor_interp σ_t σ_s -∗
    l ↦t∗[tk_local]{t} v -∗
    t $$ tk_local -∗
    ⌜length v' = length v⌝ ==∗
    bor_interp (state_upd_mem (write_mem l v') σ_t) σ_s ∗
    l ↦t∗[tk_local]{t} v' ∗
    t $$ tk_local.
  Proof.
    iInduction v' as [ | sc' v'] "IH" forall (l v).
    - iIntros "Hbor Hp Ht %Hlen". destruct v; last done. iFrame "Ht Hp". iModIntro. destruct σ_t; eauto.
    - iIntros "Hbor Hp Ht %Hlen". destruct v as [ | sc v]; first done.
      iPoseProof (big_sepL_cons with "Hp") as "[Hh Hp]".
      iMod  ("IH" $! (l +ₗ 1) v with "Hbor [Hp] Ht []") as "(Hbor & Hp & Ht)".
      { iApply (big_sepL_mono with "Hp"). intros i sc0 Hsc0. cbn.
        rewrite shift_loc_assoc. replace (1 + i)%Z with (Z.of_nat $ S i) by lia. done. }
      { cbn in Hlen. iPureIntro. lia. }
      iMod (bor_interp_write_target_local  _ _ _ _ _ sc' with "Hbor Hh Ht") as "(Hbor & Hh & Ht)".
      iModIntro. iFrame "Ht". iSplitL "Hbor".
      { rewrite state_upd_mem_compose. rewrite shift_loc_0_nat. by rewrite state_upd_write_mem_head. }
      iApply big_sepL_cons. iFrame "Hh". iApply (big_sepL_mono with "Hp").
      intros i sc0 Hsc0. cbn.
      rewrite shift_loc_assoc. replace (1 + i)%Z with (Z.of_nat $ S i) by lia. done.
  Qed.

  Lemma bor_interp_write_source_local σ_t σ_s (t : ptr_id) l sc sc' :
    bor_interp σ_t σ_s -∗
    l ↦s[tk_local]{t} sc -∗
    t $$ tk_local ==∗
    bor_interp σ_t (state_upd_mem (<[l := sc']>) σ_s) ∗
    l ↦s[tk_local]{t} sc' ∗
    t $$ tk_local.
  Proof.
    iIntros "(%M_call & %M_tag & %M_t & %M_s & (Hc & Htag_auth & Htag_t_auth & Htag_s_auth) & Htainted & Hpub_cid & Hsrel & ? & %Htag_interp & %Hwf_s & %Hwf_t)".
    iIntros "Hp Htag".
    iPoseProof (tkmap_lookup with "Htag_auth Htag") as "%Htag_lookup".
    destruct Htag_interp as (Htag_interp & Ht_dom & Hs_dom).
    destruct (Htag_interp _ _ Htag_lookup) as (_ & _ & Ht & Hs & Hagree).
    iPoseProof (ghost_map_lookup with "Htag_s_auth Hp") as "%Hs_lookup".
    specialize (Hs _ _ Hs_lookup) as Hcontrol.
    specialize (loc_controlled_local _ _ _ _ Hcontrol) as (Hstack & Hmem).
    iPoseProof (state_rel_dom_eq with "Hsrel") as "%Hdom_eq".

    iMod (ghost_map_update sc' with "Htag_s_auth Hp") as "[Htag_s_auth $]".
    iModIntro. iFrame "Htag". rewrite /bor_interp.
    iExists M_call, M_tag, M_t, (<[(t, l):=sc']> M_s).
    iFrame. cbn. iSplitL "Hsrel".
    { iApply (state_rel_upd_priv_source with "Hsrel").
      - apply elem_of_dom. rewrite Hdom_eq. apply elem_of_dom. eauto.
      - exists tk_local. split_and!; [done | | by left ].
        apply Hagree. eauto.
    }
    iSplitL; first last.
    { iSplitL; last done. iPureIntro. apply state_wf_upd_mem; [by eauto | done]. }

    iPureIntro.
    split_and!.
    - intros t' tk' (? & ? & H')%Htag_interp. do 2 (split; first done).
      destruct H' as (Ha_t & Ha_s & Hagree').
      split_and!; [ done | | ].
      + intros l' sc_t.
        destruct (decide (t = t')) as [<- | Hneq]; first last.
        { rewrite lookup_insert_ne; last congruence. intros Hsc_t.
          destruct (decide (l' = l)) as [-> | Hneq_loc].
          { (* this is fine as tag t has local ownership: t' doesn't have any control *)
            eapply loc_controlled_local_authoritative; [ | by apply Ha_s | done].
            eapply loc_controlled_mem_insert. done.
          }
          apply loc_controlled_mem_insert_ne; [done | by apply Ha_s].
        }
        revert Ha_s.
        destruct (decide (l' = l)) as [-> | Hneq_loc] => Ha_s.
        * rewrite lookup_insert_eq => [= ->]. by eapply loc_controlled_mem_insert, Ha_s.
        * rewrite lookup_insert_ne; last congruence. intros ?.
          eapply loc_controlled_mem_insert_ne; [done | by apply Ha_s].
      + destruct (decide (t = t')) as [<- | Hneq].
        * eapply dom_agree_on_tag_upd_source; eauto.
        * eapply dom_agree_on_tag_upd_ne_source; eauto.
    - done.
    - intros t' l'. rewrite lookup_insert_is_Some. intros [[= <- <-] | [_ ?%Hs_dom]]; last done. eauto.
  Qed.

  Lemma bor_interp_writeN_source_local σ_t σ_s (t : ptr_id) l v v' :
    bor_interp σ_t σ_s -∗
    l ↦s∗[tk_local]{t} v -∗
    t $$ tk_local -∗
    ⌜length v' = length v⌝ ==∗
    bor_interp σ_t (state_upd_mem (write_mem l v') σ_s) ∗
    l ↦s∗[tk_local]{t} v' ∗
    t $$ tk_local.
  Proof.
    iInduction v' as [ | sc' v'] "IH" forall (l v).
    - iIntros "Hbor Hp Hs %Hlen". destruct v; last done. iFrame "Hs Hp". iModIntro. destruct σ_s; eauto.
    - iIntros "Hbor Hp Hs %Hlen". destruct v as [ | sc v]; first done.
      iPoseProof (big_sepL_cons with "Hp") as "[Hh Hp]".
      iMod  ("IH" $! (l +ₗ 1) v with "Hbor [Hp] Hs []") as "(Hbor & Hp & Hs)".
      { iApply (big_sepL_mono with "Hp"). intros i sc0 Hsc0. cbn.
        rewrite shift_loc_assoc. replace (1 + i)%Z with (Z.of_nat $ S i) by lia. done. }
      { cbn in Hlen. iPureIntro. lia. }
      iMod (bor_interp_write_source_local  _ _ _ _ _ sc' with "Hbor Hh Hs") as "(Hbor & Hh & Hs)".
      iModIntro. iFrame "Hs". iSplitL "Hbor".
      { rewrite state_upd_mem_compose. rewrite shift_loc_0_nat. by rewrite state_upd_write_mem_head. }
      iApply big_sepL_cons. iFrame "Hh". iApply (big_sepL_mono with "Hp").
      intros i sc0 Hsc0. cbn.
      rewrite shift_loc_assoc. replace (1 + i)%Z with (Z.of_nat $ S i) by lia. done.
  Qed.

  (* TODO move *)
  Lemma loc_protected_by_mem_insert σ t l c sc' :
    loc_protected_by σ t l c →
    loc_protected_by (state_upd_mem <[l := sc']> σ) t l c.
  Proof. apply id. Qed.

  Lemma bor_interp_write_target_protected σ_t σ_s (t : ptr_id) l sc sc' c M :
    call_set_in M t l →
    bor_interp σ_t σ_s -∗
    l ↦t[tk_unq]{t} sc -∗
    c @@ M -∗
    t $$ tk_unq ==∗
    bor_interp (state_upd_mem (<[l := sc']>) σ_t) σ_s ∗
    l ↦t[tk_unq]{t} sc' ∗
    c @@ M ∗
    t $$ tk_unq.
  Proof.
    iIntros (Hl) "(%M_call & %M_tag & %M_t & %M_s & (Hc & Htag_auth & Htag_t_auth & Htag_s_auth) & Htainted & Hpub_cid & Hsrel & %Hcall_interp & %Htag_interp & %Hwf_s & %Hwf_t)".
    iIntros "Hp Hcall Htag".
    iPoseProof (tkmap_lookup with "Htag_auth Htag") as "%Htag_lookup".
    iPoseProof (ghost_map_lookup with "Hc Hcall") as "%Hcall".
    destruct Htag_interp as (Htag_interp & Ht_dom & Hs_dom).
    destruct (Htag_interp _ _ Htag_lookup) as (_ & _ & Ht & Hs & Hagree).
    iPoseProof (ghost_map_lookup with "Htag_t_auth Hp") as "%Ht_lookup".
    specialize (Ht _ _ Ht_lookup) as Hcontrol.
    assert (Hc_in : call_set_in' M_call c t l). { exists M. eauto. }
    specialize (call_set_interp_access _ _ _ _ _ Hcall_interp Hc_in) as Hprotected.
    specialize (loc_protected_bor_state_pre _ _ _ _ tk_unq Hprotected) as [Hown Hmem]%Hcontrol.

    iMod (ghost_map_update sc' with "Htag_t_auth Hp") as "[Htag_t_auth $]".
    iModIntro. iFrame "Htag Hcall". rewrite /bor_interp.
    iExists M_call, M_tag, (<[(t, l):=sc']> M_t), M_s.
    iFrame. cbn. iSplitL "Hsrel".
    { iApply (state_rel_upd_priv_target with "Hsrel").
      - eauto.
      - exists tk_unq. split_and!; [done | by eauto | right ].
        split; first done. eauto.
    }
    iSplitL; first done.
    iSplitL; first last.
    { repeat iSplitL; [ done.. | ].
      iPureIntro. apply state_wf_upd_mem; [by eauto | done].
    }

    iPureIntro.
    split_and!.
    - intros t' tk' (? & ? & H')%Htag_interp. do 2 (split; first done).
      destruct H' as (Ha_t & Ha_s & Hagree').
      split_and!; [ | done | ].
      + intros l' sc_t.
        destruct (decide (t = t')) as [<- | Hneq]; first last.
        { rewrite lookup_insert_ne; last congruence. intros Hsc_t.
          destruct (decide (l' = l)) as [-> | Hneq_loc].
          { (* this is fine as t' doesn't have any control *)
            eapply loc_controlled_protected_authoritative; [ |  | by apply Ha_t | done].
            - eapply loc_protected_by_mem_insert. done.
            - eapply loc_controlled_mem_insert. done.
          }
          apply loc_controlled_mem_insert_ne; [done | by apply Ha_t].
        }
        revert Ha_t.
        destruct (decide (l' = l)) as [-> | Hneq_loc] => Ha_t.
        * rewrite lookup_insert_eq => [= ->]. by eapply loc_controlled_mem_insert, Ha_t.
        * rewrite lookup_insert_ne; last congruence. intros ?.
          eapply loc_controlled_mem_insert_ne; [done | by apply Ha_t].
      + destruct (decide (t = t')) as [<- | Hneq].
        * eapply dom_agree_on_tag_upd_target; eauto.
        * eapply dom_agree_on_tag_upd_ne_target; eauto.
    - intros t' l'. rewrite lookup_insert_is_Some. intros [[= <- <-] | [_ ?%Ht_dom]]; last done. eauto.
    - done.
  Qed.

  Lemma bor_interp_writeN_target_protected σ_t σ_s (t : ptr_id) l v v' c M :
    (∀ i: nat, (i < length v)%nat → call_set_in M t (l +ₗ i)) →
    bor_interp σ_t σ_s -∗
    l ↦t∗[tk_unq]{t} v -∗
    t $$ tk_unq -∗
    c @@ M -∗
    ⌜length v' = length v⌝ ==∗
    bor_interp (state_upd_mem (write_mem l v') σ_t) σ_s ∗
    l ↦t∗[tk_unq]{t} v' ∗
    c @@ M ∗
    t $$ tk_unq.
  Proof.
    intros Hin.
    iInduction v' as [ | sc' v'] "IH" forall (l v Hin).
    - iIntros "Hbor Hp Hs Hc %Hlen". destruct v; last done. iFrame "Hs Hp Hc". iModIntro. destruct σ_t; eauto.
    - iIntros "Hbor Hp Hs Hc %Hlen". destruct v as [ | sc v]; first done.
      iPoseProof (big_sepL_cons with "Hp") as "[Hh Hp]".
      iMod  ("IH" $! (l +ₗ 1) v with "[] Hbor [Hp] Hs Hc []") as "(Hbor & Hp & Hc & Hs)".
      { iPureIntro. intros i Hi. rewrite shift_loc_assoc. replace (1+ i) with (Z.of_nat (S i)) by lia.
        apply Hin. simpl; lia. }
      { iApply (big_sepL_mono with "Hp"). intros i sc0 Hsc0. cbn.
        rewrite shift_loc_assoc. replace (1 + i)%Z with (Z.of_nat $ S i) by lia. done. }
      { cbn in Hlen. iPureIntro. lia. }
      iMod (bor_interp_write_target_protected  _ _ _ _ _ sc' with "Hbor Hh Hc Hs") as "(Hbor & Hh & Hc & Hs)".
      { apply Hin. simpl; lia. }
      iModIntro. iFrame "Hs Hc". iSplitL "Hbor".
      { rewrite state_upd_mem_compose. rewrite shift_loc_0_nat. by rewrite state_upd_write_mem_head. }
      iApply big_sepL_cons. iFrame "Hh". iApply (big_sepL_mono with "Hp").
      intros i sc0 Hsc0. cbn.
      rewrite shift_loc_assoc. replace (1 + i)%Z with (Z.of_nat $ S i) by lia. done.
  Qed.

  Lemma bor_interp_write_source_protected σ_t σ_s (t : ptr_id) l sc sc' c M :
    call_set_in M t l →
    bor_interp σ_t σ_s -∗
    l ↦s[tk_unq]{t} sc -∗
    c @@ M -∗
    t $$ tk_unq ==∗
    bor_interp σ_t (state_upd_mem (<[l := sc']>) σ_s) ∗
    l ↦s[tk_unq]{t} sc' ∗
    c @@ M ∗
    t $$ tk_unq.
  Proof.
    iIntros (Hl) "(%M_call & %M_tag & %M_t & %M_s & (Hc & Htag_auth & Htag_t_auth & Htag_s_auth) & Htainted & Hpub_cid & Hsrel & %Hcall_interp & %Htag_interp & %Hwf_s & %Hwf_t)".
    iIntros "Hp Hcall Htag".
    iPoseProof (tkmap_lookup with "Htag_auth Htag") as "%Htag_lookup".
    iPoseProof (ghost_map_lookup with "Hc Hcall") as "%Hcall".
    destruct Htag_interp as (Htag_interp & Ht_dom & Hs_dom).
    destruct (Htag_interp _ _ Htag_lookup) as (_ & _ & Ht & Hs & Hagree).
    iPoseProof (ghost_map_lookup with "Htag_s_auth Hp") as "%Hs_lookup".
    specialize (Hs _ _ Hs_lookup) as Hcontrol.
    assert (Hc_in : call_set_in' M_call c t l). { exists M. eauto. }
    specialize (call_set_interp_access _ _ _ _ _ Hcall_interp Hc_in) as Hprotected_t.
    iPoseProof (loc_protected_by_source with "Hsrel [//]") as "%Hprotected".
    specialize (loc_protected_bor_state_pre _ _ _ _ tk_unq Hprotected) as [Hown Hmem]%Hcontrol.
    iPoseProof (state_rel_dom_eq with "Hsrel") as "%Hdom_eq".

    iMod (ghost_map_update sc' with "Htag_s_auth Hp") as "[Htag_s_auth $]".
    iModIntro. iFrame "Htag Hcall". rewrite /bor_interp.
    iExists M_call, M_tag, M_t, (<[(t, l):=sc']> M_s).
    iFrame. cbn. iSplitL "Hsrel".
    { iApply (state_rel_upd_priv_source with "Hsrel").
      - apply elem_of_dom. rewrite Hdom_eq. apply elem_of_dom. eauto.
      - exists tk_unq. split_and!; [done |apply Hagree; eauto | right ].
        split; first done. eauto.
    }

    iSplitL; first done.
    iSplitL; first last.
    { repeat iSplitL; [ |done ].
      iPureIntro. apply state_wf_upd_mem; [by eauto | done].
    }

    iPureIntro.
    split_and!.
    - intros t' tk' (? & ? & H')%Htag_interp. do 2 (split; first done).
      destruct H' as (Ha_t & Ha_s & Hagree').
      split_and!; [ done| | ].
      + intros l' sc_s.
        destruct (decide (t = t')) as [<- | Hneq]; first last.
        { rewrite lookup_insert_ne; last congruence. intros Hsc_t.
          destruct (decide (l' = l)) as [-> | Hneq_loc].
          { (* this is fine as t' doesn't have any control *)
            eapply loc_controlled_protected_authoritative; [ |  | by apply Ha_s | done].
            - eapply loc_protected_by_mem_insert. done.
            - eapply loc_controlled_mem_insert. done.
          }
          apply loc_controlled_mem_insert_ne; [done | by apply Ha_s].
        }
        revert Ha_s.
        destruct (decide (l' = l)) as [-> | Hneq_loc] => Ha_s.
        * rewrite lookup_insert_eq => [= ->]. by eapply loc_controlled_mem_insert, Ha_s.
        * rewrite lookup_insert_ne; last congruence. intros ?.
          eapply loc_controlled_mem_insert_ne; [done | by apply Ha_s].
      + destruct (decide (t = t')) as [<- | Hneq].
        * eapply dom_agree_on_tag_upd_source; eauto.
        * eapply dom_agree_on_tag_upd_ne_source; eauto.
    - done.
    - intros t' l'. rewrite lookup_insert_is_Some. intros [[= <- <-] | [_ ?%Hs_dom]]; last done. eauto.
  Qed.

  Lemma bor_interp_writeN_source_protected σ_t σ_s (t : ptr_id) l v v' c M :
    (∀ i: nat, (i < length v)%nat → call_set_in M t (l +ₗ i)) →
    bor_interp σ_t σ_s -∗
    l ↦s∗[tk_unq]{t} v -∗
    t $$ tk_unq -∗
    c @@ M -∗
    ⌜length v' = length v⌝ ==∗
    bor_interp σ_t (state_upd_mem (write_mem l v') σ_s) ∗
    l ↦s∗[tk_unq]{t} v' ∗
    c @@ M ∗
    t $$ tk_unq.
  Proof.
    intros Hin.
    iInduction v' as [ | sc' v'] "IH" forall (l v Hin).
    - iIntros "Hbor Hp Hs Hc %Hlen". destruct v; last done. iFrame "Hs Hp Hc". iModIntro. destruct σ_s; eauto.
    - iIntros "Hbor Hp Hs Hc %Hlen". destruct v as [ | sc v]; first done.
      iPoseProof (big_sepL_cons with "Hp") as "[Hh Hp]".
      iMod  ("IH" $! (l +ₗ 1) v with "[] Hbor [Hp] Hs Hc []") as "(Hbor & Hp & Hc & Hs)".
      { iPureIntro. intros i Hi. rewrite shift_loc_assoc. replace (1+ i) with (Z.of_nat (S i)) by lia.
        apply Hin. simpl; lia. }
      { iApply (big_sepL_mono with "Hp"). intros i sc0 Hsc0. cbn.
        rewrite shift_loc_assoc. replace (1 + i)%Z with (Z.of_nat $ S i) by lia. done. }
      { cbn in Hlen. iPureIntro. lia. }
      iMod (bor_interp_write_source_protected  _ _ _ _ _ sc' with "Hbor Hh Hc Hs") as "(Hbor & Hh & Hc & Hs)".
      { apply Hin. simpl; lia. }
      iModIntro. iFrame "Hs Hc". iSplitL "Hbor".
      { rewrite state_upd_mem_compose. rewrite shift_loc_0_nat. by rewrite state_upd_write_mem_head. }
      iApply big_sepL_cons. iFrame "Hh". iApply (big_sepL_mono with "Hp").
      intros i sc0 Hsc0. cbn.
      rewrite shift_loc_assoc. replace (1 + i)%Z with (Z.of_nat $ S i) by lia. done.
  Qed.

  (** Dealloc lemmas *)
  Lemma loc_controlled_dealloc_update σ l l' (bor : tag) n (α' : stacks) (t : ptr_id) (tk : tag_kind) sc :
    memory_deallocated σ.(sst) σ.(scs) l bor n = Some α' →
    state_wf σ →
    (bor = Tagged t ∧ (∃ i:nat, l' = l +ₗ i ∧ (i < n)%nat) → tk = tk_pub) →
    loc_controlled l' t tk sc σ →
    loc_controlled l' t tk sc (mkState (free_mem l n σ.(shp)) α' σ.(scs) σ.(snp) σ.(snc)).
  Proof.
    intros Hdealloc Hwf Hpub Hcontrol Hpre.
    destruct tk.
    - (* public *)
      destruct Hpre as (stk & pm & opro & Hstk & Hit & Hpm). simpl in *.
      destruct (for_each_dealloc_lookup_Some _ _ _ _ _ Hdealloc _ _ Hstk) as [Hneq Hstk'].
      destruct Hcontrol as [Hown Hshp]. { exists stk, pm, opro. done. }
      destruct Hown as (stk' & Hstk'' & Hsro).
      split.
      + simplify_eq. exists stk. done.
      + destruct (free_mem_lookup_case l' l n σ.(shp)) as [(_ & ->) | (i & Hi & -> & _)]; first done.
        specialize (Hneq i Hi). congruence.
    - (* unique *)
      destruct Hpre as (stk & pm & opro & Hstk & Hit & Hpm). simpl in *.
      destruct (for_each_dealloc_lookup_Some _ _ _ _ _ Hdealloc _ _ Hstk) as [Hneq Hstk'].
      destruct Hcontrol as [Hown Hshp]. { exists stk, pm, opro. done. }
      destruct Hown as (stk' & Hstk'' & (opro' & ? & ->)).
      split.
      + simplify_eq. exists stk. split; first done. rewrite Hstk' in Hstk''.
        injection Hstk'' as ->. eauto.
      + destruct (free_mem_lookup_case l' l n σ.(shp)) as [(_ & ->) | (i & Hi & -> & _)]; first done.
        specialize (Hneq i Hi). congruence.
    - (* local *) clear Hpre. destruct Hcontrol as [Hown Hshp]; first done. simpl.
      destruct (free_mem_lookup_case l' l n σ.(shp)) as [(Hi & ->) | (i & Hi & -> & Hfree)].
      + split; last done. destruct (for_each_dealloc_lookup _ _ _ _ _ Hdealloc) as (_ & Heq).
        rewrite Heq; done.
      + exfalso. destruct (for_each_true_lookup_case_2 _ _ _ _ _ Hdealloc) as [Heq _].
        specialize (Heq _ Hi) as (stk & stk' & Hstk & Hstk' & Hd1).
        rewrite Hown in Hstk. injection Hstk as <-.
        destruct (dealloc1 _ _ _) eqn:Heq; [ | done].
        destruct (dealloc1_singleton_Some _ _ _ ltac:(eauto)) as (<- & _).
        enough (tk_local = tk_pub) by congruence. apply Hpub. eauto.
  Qed.


  (** Retag *)
  Lemma loc_controlled_retag_ref σ c l ot T mut α' rk i sc :
    let nt := σ.(snp) in
    let pk := RefPtr mut in
    let tk := match mut with Mutable => tk_unq | Immutable => tk_pub end in
    (if mut is Immutable then is_freeze T else True) →
    retag σ.(sst) σ.(snp) σ.(scs) c l ot rk pk T = Some (Tagged nt, α', S σ.(snp)) →
    (is_two_phase rk = false) →
    (i < tsize T)%nat →
    σ.(shp) !! (l +ₗ i) = Some sc →
    loc_controlled (l +ₗ i) nt tk sc (mkState σ.(shp) α' σ.(scs) (S σ.(snp)) σ.(snc)).
  Proof.
    intros nt pk tk Hfreeze Hretag Hrk Hi Hsc Hpre. split; last done.
    destruct mut.
    * (* unique *)
      destruct Hpre as (st & pm' & opro & Hst & Hit & Hpm'). exists st. split; first done.
      rewrite /retag Hrk in Hretag.
      have EqRT':
        retag_ref σ.(sst) σ.(scs) σ.(snp) l ot T (UniqueRef false) (adding_protector rk c) =
          Some (Tagged nt, α', S nt) by done.
      destruct (tag_on_top_retag_ref_uniq _ _ _ _ _ _ _ _ _ _ EqRT' i ltac:(lia))
        as [pro1 Eqstk1]. rewrite Hst /= in Eqstk1.
      clear -Eqstk1. destruct st as [|? stk1]; [done|].
      simpl in Eqstk1. simplify_eq. by exists pro1, stk1.
    * (* shared *)
      destruct Hpre as (stk' & pm' & pro & Eqstk' & In' & NDIS). simpl in Eqstk'.
      exists stk'. split; [done|].
      have EqRT':
        retag_ref σ.(sst) σ.(scs) σ.(snp) l ot T SharedRef (adding_protector rk c) = Some (Tagged nt, α', S nt) by done.
      have HTOP := (tag_on_top_retag_ref_shr _ _ _ _ _ _ _ _ _ _ Hfreeze EqRT' i ltac:(lia)).
      clear -HTOP Eqstk'.
      apply tag_on_top_shr_active_SRO in HTOP as (?&?&?). by simplify_eq.
  Qed.

  Lemma loc_controlled_retag_update σ c l l' t tk' ot T pk rk α' nt nxtp' sc :
    state_wf σ →
    retag σ.(sst) σ.(snp) σ.(scs) c l ot rk pk T = Some (nt, α', nxtp') →
    (Tagged t = ot → tk' = tk_pub) →
    (t < σ.(snp))%nat →
    loc_controlled l' t tk' sc σ →
    loc_controlled l' t tk' sc (mkState σ.(shp) α' σ.(scs) nxtp' σ.(snc)).
  Proof.
    intros Hwf Hretag Hneq Hlt Hcontrolled.
    intros Hpre. destruct tk'.
    * destruct Hpre as (stk' & pm' & pro & Eqstk' & In' & ND).
      destruct (retag_item_in _ _ _ _ _ _ _ _ _ _ _ _ Hretag _ _ t _ Eqstk' In')
        as (stk & Eqstk & In); [done..|].

      destruct Hcontrolled as (Hown & Hl'). { simpl; naive_solver. }
      cbn. split; last done.
      exists stk'. split; [done|].
      destruct Hown as (stk1 & Eqstk1 & HTOP).
      rewrite Eqstk1 in Eqstk. simplify_eq.
      move : HTOP.
      have ND2 := proj2 (state_wf_stack_item _ Hwf _ _ Eqstk1).
      by apply (retag_item_active_SRO_preserving _ _ _ _ _ _ _ _ _ _ _ _ Hretag _ _ _ _ _ ND2 Eqstk1 Eqstk' In In').
    * destruct Hpre as (stk' & pm' & pro & Eqstk' & In' & ND).
      destruct (retag_item_in _ _ _ _ _ _ _ _ _ _ _ _ Hretag _ _ t _ Eqstk' In')
        as (stk & Eqstk & In); [done..|].
      destruct Hcontrolled as (Hown & Hl'); [simpl; naive_solver|].
      split; last done. cbn.
      exists stk'. split; [done|].
      destruct Hown as (stk1 & Eqstk1 & opro1 & HTOP).
      rewrite Eqstk1 in Eqstk. simplify_eq.
      have ND2 := proj2 (state_wf_stack_item _ Hwf _ _ Eqstk1).
      assert (opro1 = pro ∧ pm' = Unique) as [].
      { have In1 : mkItem Unique (Tagged t) opro1 ∈ stk.
        { destruct HTOP as [? HTOP]. rewrite HTOP. by left. }
        have EQ := stack_item_tagged_NoDup_eq _ _ _ t ND2 In1 In eq_refl eq_refl.
        by simplify_eq. } subst opro1 pm'. exists pro.
      have NEq: Tagged t ≠ ot.
      { intros <-. specialize (Hneq eq_refl). congruence. }
      move : HTOP.
      by apply (retag_item_head_preserving _ _ _ _ _ _ _ _ _ _ _ _ Hretag
                  _ _ _ _ _ ND2 Eqstk1 Eqstk' NEq In').
    * clear Hpre. specialize (Hcontrolled I) as (Hown & Hl'). split; last done.
      move : Hown. cbn.
      have NEq: ot ≠ Tagged t.
      { intros ->. specialize (Hneq eq_refl). congruence. }
      move : NEq. by eapply retag_Some_local.
  Qed.

End lemmas.

(* accessing a local location is only possible with the same tag, retaining the same stack for the access *)
Lemma local_access_eq l t t' stk n stk' kind σ_s σ_t M_tag M_t M_s :
  σ_t.(sst) !! l = Some stk →
  access1 stk kind t' σ_t.(scs) = Some (n, stk') →
  M_tag !! t = Some (tk_local, ()) →
  is_Some (M_t !! (t, l)) →
  tag_interp M_tag M_t M_s σ_t σ_s →
  t' = Tagged t ∧ stk' = stk.
Proof.
  intros Hst Haccess Htag Ht Htag_interp.
  specialize (access1_in_stack _ _ _ _ _ _ Haccess) as (it & Hin_stack & <- & Henabled).
  destruct Htag_interp as (Htag_interp & _ & _).
  specialize (Htag_interp _ _ Htag) as (_ & _ & Htl & Hsl & Hdom).
  destruct Ht as (sc_t & Ht).
  specialize (Htl _ _ Ht) as Hcontrol.
  apply loc_controlled_local in Hcontrol as (Hcontrol & _).
  destruct (tag_unique_head_access σ_t.(scs) _ (Tagged t) None kind ltac:(by exists [])) as (n' & Hn).
  move : Hst Hin_stack Haccess .
  rewrite Hcontrol => [= <-]. rewrite list_elem_of_singleton => ->.
  rewrite Hn => [= _ <-]. done.
Qed.

Lemma protector_access_eq l t t' stk n stk' kind σ_s σ_t M_tag Mcall M_t M_s :
  σ_t.(sst) !! l = Some stk →
  access1 stk kind t' σ_t.(scs) = Some (n, stk') →
  M_tag !! t = Some (tk_unq, ()) →
  is_Some (M_t !! (t, l)) →
  (∃ (c: call_id), call_set_in' Mcall c t l) →
  tag_interp M_tag M_t M_s σ_t σ_s →
  call_set_interp Mcall σ_t →
  state_wf σ_t →
  t' = Tagged t.
Proof.
  intros Hst Haccess Htag Ht (c & Hcall) Htag_interp Hcall_interp Hwf.
  specialize (call_set_interp_access _ _ _ _ _ Hcall_interp Hcall) as (Hc_in & _ & (stk'' & pm & Hstk'' & Hin & Hpm)).
  destruct Htag_interp as (Htag_interp & _ & _).
  specialize (Htag_interp _ _ Htag) as (_ & _ & Htl & Hsl & Hdom).
  destruct Ht as (sc_t & Ht).
  specialize (Htl _ _ Ht) as Hcontrol.
  specialize (loc_controlled_unq _ _ _ _ _ Hcontrol Hstk'' ltac:(eauto)) as ((stk''' & opro & ->) & Hmem).
  move : Hstk'' Hin Haccess. rewrite Hst => [= Heq]. move : Hst. rewrite Heq => Hst Hi.
  have ->: opro = Some c.
  { destruct (state_wf_stack_item _ Hwf _ _ Hst) as [_ ND].
    have [=] := stack_item_tagged_NoDup_eq _ _ _ t ND Hi ltac:(by left) eq_refl eq_refl.
    done.
  }
  eapply access1_incompatible_head_protector; [by (eexists; eauto) | done].
Qed.

(* successfully accesses with a private location are only possible when the tag is equal *)
Lemma priv_loc_UB_access_eq l kind σ_s σ_t t t' stk M_tag M_t M_s Mcall :
  σ_t.(sst) !! l = Some stk →
  is_Some (access1 stk kind t' σ_t.(scs)) →
  priv_loc M_tag M_t Mcall t l →
  tag_interp M_tag M_t M_s σ_t σ_s →
  call_set_interp Mcall σ_t →
  state_wf σ_t →
  t' = Tagged t.
Proof.
  intros Hs ([? ?] & Haccess) Hpriv Htag_interp Hcall_interp Hwf.
  destruct Hpriv as (tk & Htag & Ht & [-> | [-> Hc]]).
  - by eapply local_access_eq.
  - eapply protector_access_eq; done.
Qed.

Definition untagged_or_public (M_tag : gmap ptr_id (tag_kind * unit)) t :=
  match t with
  | Tagged t2 => M_tag !! t2 = Some (tk_pub, ())
  | Untagged => True
  end.
Lemma priv_pub_access_UB l kind σ_s σ_t t t' stk M_tag Mcall M_t M_s :
  σ_t.(sst) !! l = Some stk →
  is_Some (access1 stk kind t' σ_t.(scs)) →
  priv_loc M_tag M_t Mcall t l →
  tag_interp M_tag M_t M_s σ_t σ_s →
  call_set_interp Mcall σ_t →
  state_wf σ_t →
  untagged_or_public M_tag t' →
  False.
Proof.
  intros Hs Haccess Hpriv Htag_interp Hcall_interp Hwf.
  rewrite (priv_loc_UB_access_eq _ _ _ _ _ _ _ _ _ _ _ Hs Haccess Hpriv Htag_interp Hcall_interp Hwf).
  destruct Hpriv as (tk & Hl & _ & [-> | [-> _]]); cbn; intros; simplify_eq.
Qed.

Lemma priv_loc_UB_retag_access_eq σ_s σ_t c l old new mut T kind α' nxtp' M_tag M_t M_s Mcall
  (FRZ: if mut is Immutable then is_freeze T else True)
  (N2P: kind ≠ TwoPhase) :
  retag σ_t.(sst) σ_t.(snp) σ_t.(scs) c l old kind (RefPtr mut) T = Some (new, α', nxtp') →
  ∀ i t, (i < tsize T)%nat →
  priv_loc M_tag M_t Mcall t (l +ₗ i) →
  tag_interp M_tag M_t M_s σ_t σ_s →
  call_set_interp Mcall σ_t →
  state_wf σ_t →
  untagged_or_public M_tag old →
  False.
Proof.
  intros Hrt i t Hi.
  have NZST: (0 < tsize T)%nat by lia.
  destruct (retag_change_ref_NZST _ _ _ _ _ _ _ _ _ _ _ _ NZST Hrt);
    subst new nxtp'.
  destruct (retag_Some_Ref _ _ _ _ _ _ _ _ _ _ _ _ NZST FRZ N2P Hrt _ Hi)
    as (stk & stk' & Eqstk & Eqstk' & GR).
  apply grant_access1 in GR; [|by destruct mut].
  revert Eqstk GR. by apply priv_pub_access_UB.
Qed.


(** TODO: these lemmas need a new home *)
Section lemmas.
Context `{!sborGS Σ}.
Implicit Types P Q : iProp Σ.
Implicit Types Φ : expr → expr → iProp Σ.
Implicit Types σ σ_s σ_t : state.
Implicit Types r r_s r_t : result.
Implicit Types l : loc.
Implicit Types f : fname.

Context (Ω : result → result → iProp Σ).


Lemma memory_read_access1 (stks : stacks) l n t calls :
  (∀ i: nat, (i < n)%nat → ∃ stk, stks !! (l +ₗ i) = Some stk ∧ ∃ m, access1 stk AccessRead (Tagged t) calls = Some (m, stk)) →
  memory_read stks calls l (Tagged t) n = Some stks.
Proof.
  induction n as [ | n IH]; cbn; first done.
  intros Hacc1. destruct (Hacc1 n ltac:(lia)) as (stkn & Hl & (m & Hacc1_n)). rewrite Hl.
  cbn. rewrite Hacc1_n. cbn.
  rewrite insert_id; last done. apply IH. intros i Hi. apply Hacc1. lia.
Qed.

Lemma bor_state_own_access1_read l t tk stk σ :
  bor_state_own l t tk σ →
  σ.(sst) !! l = Some stk →
  ∃ n, access1 stk AccessRead (Tagged t) σ.(scs) = Some (n, stk).
Proof.
  intros Hown. destruct tk; cbn in *.
  - destruct Hown as (st & -> & Hsro). move => [= <-]. by apply tag_SRO_top_access.
  - destruct Hown as (st & Hsst & (opro & st' & H)). simplify_eq. rewrite Hsst => [= <-].
    eapply tag_unique_head_access. eexists; eauto.
  - rewrite Hown => [= <-].
    eapply tag_unique_head_access. eexists; eauto.
Qed.


Lemma memory_written_access1 (stks : stacks) l n t calls :
  (∀ i: nat, (i < n)%nat → ∃ stk, stks !! (l +ₗ i) = Some stk ∧ ∃ m, access1 stk AccessWrite (Tagged t) calls = Some (m, stk)) →
  memory_written stks calls l (Tagged t) n = Some stks.
Proof.
  induction n as [ | n IH]; cbn; first done.
  intros Hacc1. destruct (Hacc1 n ltac:(lia)) as (stkn & Hl & (m & Hacc1_n)). rewrite Hl.
  cbn. rewrite Hacc1_n. cbn.
  rewrite insert_id; last done. apply IH. intros i Hi. apply Hacc1. lia.
Qed.

Lemma bor_state_own_access1_write l t tk stk σ :
  tk = tk_local ∨ tk = tk_unq →
  bor_state_own l t tk σ →
  σ.(sst) !! l = Some stk →
  ∃ n, access1 stk AccessWrite (Tagged t) σ.(scs) = Some (n, stk).
Proof.
  intros Htk Hown. destruct tk; cbn in *.
  - naive_solver.
  - destruct Hown as (st & Hsst & (opro & st' & H)). simplify_eq. rewrite Hsst => [= <-].
    eapply tag_unique_head_access. eexists; eauto.
  - rewrite Hown => [= <-].
    eapply tag_unique_head_access. eexists; eauto.
Qed.
End lemmas.
