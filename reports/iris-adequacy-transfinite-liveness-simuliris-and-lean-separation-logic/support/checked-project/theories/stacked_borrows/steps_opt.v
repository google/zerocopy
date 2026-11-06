From iris.proofmode Require Export proofmode.
From iris.base_logic.lib Require Import ghost_map.
From simuliris.base_logic Require Export gen_sim_prog.
From simuliris.simulation Require Export slsls.
From simuliris.simulation Require Import lifting.
From simuliris.stacked_borrows Require Import tkmap_view.
From simuliris.stacked_borrows Require Export defs class_instances.
From simuliris.stacked_borrows Require Import steps_progress steps_retag steps_inv.
From simuliris.stacked_borrows Require Import logical_state inv_accessors.

(** * Simulation lemmas using the ghost state for proving optimizations *)

Section lifting.
Context `{!sborGS Σ}.
Implicit Types P Q : iProp Σ.
Implicit Types Φ : expr → expr → iProp Σ.
Implicit Types σ σ_s σ_t : state.
Implicit Types r r_s r_t : result.
Implicit Types l : loc.
Implicit Types f : fname.


(** ** Retags *)
(** *** Retags without protectors *)
Lemma bor_interp_retag_default σ_t σ_s c l ot T α' mut :
  let pk : pointer_kind := RefPtr mut in
  let pm := match mut with Mutable => Unique | Immutable => SharedReadOnly end in
  let tk := match mut with Mutable => tk_unq | Immutable => tk_pub end in
  retag σ_s.(sst) σ_s.(snp) σ_s.(scs) c l ot Default pk T = Some (Tagged σ_s.(snp), α', S σ_s.(snp)) →
  c ∈ σ_s.(scs) →
  (if mut is Immutable then is_freeze T else True) →
  state_wf (mkState σ_t.(shp) α' σ_t.(scs) (S σ_t.(snp)) σ_t.(snc)) →   (* could remove that assumption *)
  state_wf (mkState σ_s.(shp) α' σ_s.(scs) (S σ_s.(snp)) σ_s.(snc)) →   (* could remove that assumption *)
  sc_rel (ScPtr l ot) (ScPtr l ot) -∗
  bor_interp sc_rel σ_t σ_s ==∗ ∃ v_t v_s,
  ⌜length v_t = tsize T⌝ ∗
  ⌜length v_s = tsize T⌝ ∗
  value_rel v_t v_s ∗
  σ_t.(snp) $$ tk ∗
  l ↦t∗[tk]{σ_t.(snp)} v_t ∗
  l ↦s∗[tk]{σ_t.(snp)} v_s ∗
  match mut with
  | Mutable => True
  | Immutable =>
    sc_rel (ScPtr l (Tagged (σ_t.(snp)))) (ScPtr l (Tagged (σ_t.(snp))))
  end ∗
  bor_interp sc_rel (mkState σ_t.(shp) α' σ_t.(scs) (S σ_t.(snp)) σ_t.(snc)) (mkState σ_s.(shp) α' σ_s.(scs) (S σ_s.(snp)) σ_s.(snc)).
Proof.
  intros pk pm tk Hretag Hc_in Hfreeze Hwf'_t Hwf'_s.
  iIntros "Hscrel Hbor". iDestruct "Hbor" as "(%M_call & %M_tag & %M_t & %M_s & (Hc & Htag_auth & Htag_t_auth & Htag_s_auth) & Htainted & Hpub_cid & #Hsrel & %Hcall_interp & %Htag_interp & %Hwf_s & %Hwf_t)".

  iDestruct "Hscrel" as "[_ Hrel]".
  iAssert (⌜untagged_or_public M_tag ot⌝)%I as %Hpub.
  { iDestruct "Hrel" as "[[-> _] | (%t1 & %t2 & -> & -> & <- & Hpub)]"; first done.
    iPoseProof (tkmap_lookup with "Htag_auth Hpub") as "%". done.
  }
  pose nt := (snp σ_t).

  have Hin_dom := retag_Some_dom _ _ _ _ _ _ _ pk _ _ _ _ I Hretag.
  iPoseProof (state_rel_dom_eq with "Hsrel") as "%Hdom_eq".
  destruct (read_mem_is_Some l (tsize T) σ_s.(shp)) as [v_s Hv_s].
  { setoid_rewrite (state_wf_dom _ Hwf_s). done. }
  destruct (read_mem_is_Some l (tsize T) σ_t.(shp)) as [v_t Hv_t].
  { rewrite Hdom_eq. setoid_rewrite (state_wf_dom _ Hwf_s). done. }
  destruct (read_mem_values _ _ _ _ Hv_s) as [Hlen_s Hshp_s].
  destruct (read_mem_values _ _ _ _ Hv_t) as [Hlen_t Hshp_t].

  (* allocate resources *)
  assert (M_tag !! nt = None) as Htag_none.
  { destruct (M_tag !! nt) as [[tk' []] | ] eqn:Ht_some; last done.
    apply Htag_interp in Ht_some as [Hcontra _]. lia. }
  destruct Htag_interp as (Htag_interp & Ht_dom & Hs_dom).
  iMod (tkmap_insert tk _ tt Htag_none with "Htag_auth") as "[Htag_auth Hnt]".
  iMod (ghost_map_array_tag_insert _ _ v_t nt l with "Htag_t_auth") as "[Ht Htag_t_auth]".
  { intros i Hi. destruct (M_t !! (nt, l +ₗ i)) eqn:Hmt; last done.
    destruct (Ht_dom nt (l +ₗ i) ltac:(eauto)) as (? & ?); congruence. }
  iMod (ghost_map_array_tag_insert _ _ v_s nt l with "Htag_s_auth") as "[Hs Htag_s_auth]".
  { intros i Hi. destruct (M_s !! (nt, l +ₗ i)) eqn:Hmt; last done.
    destruct (Hs_dom nt (l +ₗ i) ltac:(eauto)) as (? & ?); congruence. }
  iMod (ghost_map_array_tag_tk _ _ _ _ tk with "Ht") as "Ht".
  iMod (ghost_map_array_tag_tk _ _ _ _ tk with "Hs") as "Hs".
  iModIntro.
  iAssert (nt $$ tk ∗ if tk is tk_pub then nt $$ tk_pub else True)%I  with "[Hnt]" as "[$ Hpubt]".
  { destruct tk; eauto. }
  iExists v_t, v_s. iSplit; first done. iSplit; first done. iFrame "Ht Hs".

  iAssert (⌜retag σ_t.(sst) σ_t.(snp) σ_t.(scs) c l ot Default pk T = Some (Tagged nt, α', S (σ_t.(snp)))⌝)%I as "%Hretag_t".
  { iPoseProof (state_rel_calls_eq with "Hsrel") as "<-".
    iPoseProof (state_rel_stacks_eq with "Hsrel") as "<-".
    subst nt. iPoseProof (state_rel_snp_eq with "Hsrel") as "<-". done. }
  (* proving the value relation *)
  iAssert (value_rel v_t v_s)%I as "#Hvrel"; last iFrame "Hvrel".
  { iApply big_sepL2_forall; iSplit; first (iPureIntro;lia).
    iIntros (i sc_t sc_s) "%Hs_t %Hs_v".
    assert (i < tsize T)%nat as Hi. { rewrite -Hlen_t. eapply lookup_lt_is_Some_1. eauto. }
    assert (Hsome_target : is_Some (σ_t.(shp) !! (l +ₗ i))).
    { rewrite Hshp_t; last done. apply lookup_lt_is_Some_2. by rewrite Hlen_t. }
    iPoseProof (state_rel_pub_if_not_priv _ _ _ _ _ _ (l +ₗ i) with "[] Hsrel [Hrel]") as "Hpub"; first done.
    { iPoseProof (state_rel_calls_eq with "Hsrel") as "%Hcall_eq".
      iPoseProof (state_rel_stacks_eq with "Hsrel") as "%Hstack_eq".
      iPureIntro. intros t Hpriv.
      eapply (priv_loc_UB_retag_access_eq σ_s σ_t); eauto; done. }
    iPoseProof (pub_loc_lookup with "[] Hpub") as "(%sc_t' & %sc_s' & %Hread_both & Hsc_rel)"; first done.
    enough (sc_t = sc_t' ∧ sc_s = sc_s') by naive_solver.
    move : Hs_t Hs_v Hread_both (Hshp_s i Hi) (Hshp_t i Hi).
    by move => -> -> [-> ->] [= ->] [= ->].
  }

  iSplitL "Hpubt".
  { destruct mut; first done. iSplitR; first done. iRight.
    iExists (σ_t.(snp)), (σ_t.(snp)). do 3 (iSplitR; first done). done. }

  (* re-establishing the interpretation *)
  iExists M_call, (<[ nt := (tk, ()) ]> M_tag), (array_tag_map l nt v_t ∪ M_t), (array_tag_map l nt v_s ∪ M_s).
  iFrame. iSplitL "Htainted".
  { (* tainted *) iApply (tag_tainted_interp_retag with "Htainted"); done. }
  iSplitL.
  { (* state relation *)
    rewrite /state_rel. simpl. iDestruct "Hsrel" as "(-> & %Hs_eq & -> & -> & -> & Hsrel)".
    do 5 (iSplitL; first done). iIntros (l' Hsl').
    iDestruct ("Hsrel" $! l' with "[//]") as "[Hpub | [%t' %Hpriv]]"; first (iLeft; iApply "Hpub").
    iRight. iPureIntro. exists t'.
    destruct Hpriv as (tk' & Hsome_tk' & Ht_l' & Htk'). exists tk'.
    assert (t' ≠ nt). { intros ->. simplify_eq. }
    rewrite lookup_insert_ne; last done.
    split; first done. split; last done.
    destruct Ht_l' as (sc0 & Ht_l'). exists sc0.
    rewrite lookup_union_r; first done.
    destruct (array_tag_map l nt v_t !! (t', l')) as [ a | ] eqn:Harr; last done.
    specialize (array_tag_map_lookup1 l nt v_t t' l' ltac:(eauto)) as [Heq _]. congruence.
  }
  iSplitL.
  { (* call interpretation. *)
    iPureIntro. intros c' M' [Hc' HM']%Hcall_interp. split; first done.
    intros t' S HS. simpl. specialize (HM' t' S HS) as (Ht' & Hprot).
    split; first lia. intros l' Hl'.
    specialize (Hprot l' Hl') as (s & pm' & Hs & Hit & Hpm').
    specialize (retag_item_active_preserving _ _ _ _ _ _ _ _ _ _ _ _ Hretag_t l' s (Tagged t') c' pm' Hs Hc' Hit) as (s' & -> & Hin'). eauto.
  }
  iSplitL.
  { (* tag interpretation. *)
    iPoseProof (state_rel_get_pure with "Hsrel") as "%Hp".
    destruct Hp as (Hsst & Hsnp & Hsnc & Hscs).
    assert (∀l', M_t !! (nt, l') = None) as HMt_nt.
    { intros l'. destruct (M_t !! (nt, l')) eqn:HM_t; last done.
      specialize (Ht_dom nt l' ltac:(eauto)) as (? & ?); congruence. }
    assert (∀l', M_s !! (nt, l') = None) as HMs_nt.
    { intros l'. destruct (M_s !! (nt, l')) eqn:HM_s; last done.
      specialize (Hs_dom nt l' ltac:(eauto)) as (? & ?); congruence. }
    iPureIntro. split_and!.
    { intros t tk'. rewrite lookup_insert_Some. intros [[<- [= <-]] | [Hneq Hsome_t]].
      - cbn. split_and!; [lia | lia | | |].
        + intros l' sc_t Ha%lookup_union_Some_inv_l; last done.
          specialize (array_tag_map_lookup2 l nt v_t nt l' ltac:(eauto)) as [_ (i & Hi & ->)].
          eapply loc_controlled_retag_ref; [ done | done |  done | lia | ].
          move : Ha. rewrite array_tag_map_lookup_Some; last done. move => <-. apply Hshp_t. lia.
        + intros l' sc_s Ha%lookup_union_Some_inv_l; last done.
          specialize (array_tag_map_lookup2 l nt v_s nt l' ltac:(eauto)) as [_ (i & Hi & ->)].
          subst nt. rewrite -Hsnp. eapply loc_controlled_retag_ref; [ done | done | done | lia | ].
          move : Ha. rewrite array_tag_map_lookup_Some; last done. move => <-. apply Hshp_s. lia.
        + apply dom_agree_on_tag_union. { apply dom_agree_on_tag_array_tag_map. lia. }
          apply dom_agree_on_tag_not_elem; done.
      - cbn.
        specialize (Htag_interp t tk' Hsome_t) as (Ht_t & Ht_s & Hcontrolled_t & Hcontrolled_s & Hagree).
        split_and!; [ lia | lia | | | ].
        + intros l' sc_t Ha. rewrite lookup_union_r in Ha; last by apply array_tag_map_lookup_None.
          apply Hcontrolled_t in Ha.
          eapply loc_controlled_retag_update; [done | done | | done | done].
          intros <-. destruct tk'; [ done | | ]; move : Hsome_t Hpub; congruence.
        + intros l' sc_s Ha. rewrite lookup_union_r in Ha; last by apply array_tag_map_lookup_None.
          apply Hcontrolled_s in Ha.
          eapply loc_controlled_retag_update; [done | done | | done | done].
          intros <-. destruct tk'; [ done | | ]; move : Hsome_t Hpub; congruence.
        + apply dom_agree_on_tag_union; last done.
          apply dom_agree_on_tag_not_elem; apply array_tag_map_lookup_None; done.
    }
    { intros t l'.
      rewrite lookup_union_is_Some lookup_insert_is_Some'. intros [[-> _]%array_tag_map_lookup2 | H%Ht_dom]; eauto. }
    { intros t l'.
      rewrite lookup_union_is_Some lookup_insert_is_Some'. intros [[-> _]%array_tag_map_lookup2 | H%Hs_dom]; eauto. }
  }
  done.
Qed.

Lemma sim_retag_default mut T l_t l_s c ot π Φ :
  (0 < tsize T)%nat → (* for convenience: makes the proof easier *)
  let pk : pointer_kind := RefPtr mut in
  let pm := match mut with Mutable => Unique | Immutable => SharedReadOnly end in
  let tk := match mut with Mutable => tk_unq | Immutable => tk_pub end in
  (if mut is Immutable then is_freeze T else True) →
  sc_rel (ScPtr l_t ot) (ScPtr l_s ot) -∗
  (∀ nt v_t v_s,
    ⌜length v_t = tsize T⌝ -∗ ⌜length v_s = tsize T⌝ -∗
    value_rel v_t v_s -∗  (* as the pointers were public before *)
    nt $$ tk -∗
    l_t ↦t∗[tk]{nt} v_t -∗
    l_s ↦s∗[tk]{nt} v_s -∗
    (if mut is Immutable then sc_rel (ScPtr l_t (Tagged nt)) (ScPtr l_s (Tagged nt)) else True) -∗
    #[ScPtr l_t (Tagged nt)] ⪯{π} #[ScPtr l_s (Tagged nt)] [{ Φ }]) -∗
  Retag #[ScPtr l_t ot] #[ScCallId c] pk T Default ⪯{π} Retag #[ScPtr l_s ot] #[ScCallId c] pk T Default [{ Φ }].
Proof.
  intros Hsize pk pm tk Hmut. iIntros "#Hscrel Hsim".
  iApply sim_lift_base_step_both. iIntros (P_t P_s σ_t σ_s ??) "((HP_t & HP_s & Hbor) & %Hthread & %Hsafe)".
  (* exploit source to gain knowledge about stacks & that c is a valid id *)
  specialize (pool_safe_implies Hsafe Hthread) as (c' & ot' & l' & [= <- <-] & [= <-] & Hc_active & Hretag_some_s).
  iPoseProof "Hscrel" as "(-> & _)".
  iPoseProof (bor_interp_get_pure with "Hbor") as "%Hp".
  have Hretag_some_t : is_Some (retag σ_t.(sst) σ_t.(snp) σ_t.(scs) c l_s ot Default pk T).
  { destruct Hp as (<- & <- & _ & <- & _). done. }
  iModIntro. iSplitR.
  { iPureIntro.
    destruct Hretag_some_t as ([[] ] & Hretag_some_t).
    do 3 eexists. eapply retag_base_step'; last done.
    destruct Hp as (_ & _ & _ & <- & _). done.
  }
  iIntros (e_t' efs_t σ_t') "%Hhead_t".
  specialize (head_retag_inv _ _ _ _ _ _ _ _ _ _ _ Hhead_t) as (nt & α' & nxtp' & Hretag_t & -> & -> & -> & Hc).
  have Hretag_s : retag σ_s.(sst) σ_s.(snp) σ_s.(scs) c l_s ot Default pk T = Some (nt, α', nxtp').
  { destruct Hp as (-> & -> & _ & -> & _). done. }
  assert (Hhead_s : base_step P_s (Retag #[ScPtr l_s ot] #[ScCallId c] pk T Default) σ_s #[ScPtr l_s nt]%E (mkState (shp σ_s) α' (scs σ_s) nxtp' (snc σ_s)) []).
  { eapply retag_base_step'; done. }
  specialize (retag_change_ref_NZST _ _ _ _ _ _ _ _ _ _ _ _ Hsize Hretag_s) as [-> ->].

  iPoseProof (bor_interp_get_state_wf with "Hbor") as "[%Hwf_t %Hwf_s]".
  iMod (bor_interp_retag_default _ _ _ _ _ _ _ _ Hretag_s ltac:(done) with "Hscrel Hbor") as
    (v_t v_s) "(%Hlen_t & %Hlen_s & Hval & Htag & Ht & Hs & Hpub & Hbor)"; first done.
  { destruct Hp as (_ & <- & _). eapply base_step_wf; eauto. }
  { eapply base_step_wf; eauto. }
  iModIntro.

  iExists #[ScPtr l_s (Tagged σ_s.(snp))]%E, [], (mkState σ_s.(shp) α' σ_s.(scs) (S σ_s.(snp)) σ_s.(snc)).
  iSplitR; first done.
  destruct Hp as (_ & -> & _).
  iFrame "Hbor HP_t HP_s".
  iSplitL; last done.
  iApply ("Hsim" with "[] [] Hval Htag Ht Hs Hpub"); [done | done | ..].
Qed.

(** *** Retags with protectors *)
Fixpoint seq_loc_set (l : loc) (n : nat) : gset loc :=
  match n with
  | O => ∅
  | S n => {[ l +ₗ n ]} ∪ seq_loc_set l n
  end.
Lemma seq_loc_set_elem l n l' :
  l' ∈ seq_loc_set l n ↔ (∃ (i : nat), (i < n)%nat ∧ l' = l +ₗ i).
Proof.
  induction n as [ | n IH]; simpl.
  - rewrite elem_of_empty. split; first done. intros (i & Hi & _). lia.
  - rewrite elem_of_union elem_of_singleton. split.
    + intros [-> | (i & Hi & ->)%IH]; [ exists n; naive_solver | exists i; naive_solver].
    + intros (i & Hi & ->). destruct (decide (i = n)) as [-> | Hneq]; first by left.
      right. apply IH. exists i. split; [lia | done].
Qed.

Lemma bor_interp_retag_fnentry σ_t σ_s l ot c T α' M mut :
  let pk : pointer_kind := RefPtr mut in
  let pm := match mut with Mutable => Unique | Immutable => SharedReadOnly end in
  let tk := match mut with Mutable => tk_unq | Immutable => tk_pub end in
  let L := seq_loc_set l (tsize T) in   (* uses that l_t = l_s *)
  retag σ_s.(sst) σ_s.(snp) σ_s.(scs) c l ot FnEntry pk T = Some (Tagged σ_s.(snp), α', S σ_s.(snp)) →
  (if mut is Immutable then is_freeze T else True) →
  state_wf (mkState σ_t.(shp) α' σ_t.(scs) (S σ_t.(snp)) σ_t.(snc)) →   (* could remove that assumption *)
  state_wf (mkState σ_s.(shp) α' σ_s.(scs) (S σ_s.(snp)) σ_s.(snc)) →   (* could remove that assumption *)
  sc_rel (ScPtr l ot) (ScPtr l ot) -∗
  c @@ M -∗
  bor_interp sc_rel σ_t σ_s ==∗ ∃ v_t v_s,
  ⌜length v_t = tsize T⌝ ∗
  ⌜length v_s = tsize T⌝ ∗
  value_rel v_t v_s ∗
  c @@ <[σ_t.(snp) := L]> M ∗
  σ_t.(snp) $$ tk ∗
  l ↦t∗[tk]{σ_t.(snp)} v_t ∗
  l ↦s∗[tk]{σ_t.(snp)} v_s ∗
  match mut with
  | Mutable => True
  | Immutable =>
    sc_rel (ScPtr l (Tagged (σ_t.(snp)))) (ScPtr l (Tagged (σ_t.(snp))))
  end ∗
  bor_interp sc_rel (mkState σ_t.(shp) α' σ_t.(scs) (S σ_t.(snp)) σ_t.(snc)) (mkState σ_s.(shp) α' σ_s.(scs) (S σ_s.(snp)) σ_s.(snc)).
Proof.
  intros pk pm tk L Hretag Hfreeze Hwf'_t Hwf'_s.
  iIntros "Hscrel Hcid Hbor". iDestruct "Hbor" as "(%M_call & %M_tag & %M_t & %M_s & (Hc & Htag_auth & Htag_t_auth & Htag_s_auth) & Htainted & Hpub_cid & #Hsrel & %Hcall_interp & %Htag_interp & %Hwf_s & %Hwf_t)".

  iDestruct "Hscrel" as "[_ Hrel]".
  iAssert (⌜untagged_or_public M_tag ot⌝)%I as %Hpub.
  { iDestruct "Hrel" as "[[-> _] | (%t1 & %t2 & -> & -> & <- & Hpub)]"; first done.
    iPoseProof (tkmap_lookup with "Htag_auth Hpub") as "%". done.
  }
  pose nt := (snp σ_t).

  have Hin_dom := retag_Some_dom _ _ _ _ _ _ _ pk _ _ _ _ I Hretag.
  iPoseProof (state_rel_dom_eq with "Hsrel") as "%Hdom_eq".
  destruct (read_mem_is_Some l (tsize T) σ_s.(shp)) as [v_s Hv_s].
  { setoid_rewrite (state_wf_dom _ Hwf_s). done. }
  destruct (read_mem_is_Some l (tsize T) σ_t.(shp)) as [v_t Hv_t].
  { rewrite Hdom_eq. setoid_rewrite (state_wf_dom _ Hwf_s). done. }
  destruct (read_mem_values _ _ _ _ Hv_s) as [Hlen_s Hshp_s].
  destruct (read_mem_values _ _ _ _ Hv_t) as [Hlen_t Hshp_t].

  (* allocate resources *)
  assert (M_tag !! nt = None) as Htag_none.
  { destruct (M_tag !! nt) as [[tk' []] | ] eqn:Ht_some; last done.
    apply Htag_interp in Ht_some as [Hcontra _]. lia. }
  destruct Htag_interp as (Htag_interp & Ht_dom & Hs_dom).
  iMod (tkmap_insert tk _ tt Htag_none with "Htag_auth") as "[Htag_auth Hnt]".
  iMod (ghost_map_array_tag_insert _ _ v_t nt l with "Htag_t_auth") as "[Ht Htag_t_auth]".
  { intros i Hi. destruct (M_t !! (nt, l +ₗ i)) eqn:Hmt; last done.
    destruct (Ht_dom nt (l +ₗ i) ltac:(eauto)) as (? & ?); congruence. }
  iMod (ghost_map_array_tag_insert _ _ v_s nt l with "Htag_s_auth") as "[Hs Htag_s_auth]".
  { intros i Hi. destruct (M_s !! (nt, l +ₗ i)) eqn:Hmt; last done.
    destruct (Hs_dom nt (l +ₗ i) ltac:(eauto)) as (? & ?); congruence. }
  iMod (ghost_map_array_tag_tk _ _ _ _ tk with "Ht") as "Ht".
  iMod (ghost_map_array_tag_tk _ _ _ _ tk with "Hs") as "Hs".
  set (M' := <[σ_t.(snp) := L]> M).
  iPoseProof (ghost_map_lookup with "Hc Hcid") as "%HM_c".
  iMod (ghost_map_update M' with "Hc Hcid") as "[Hc Hcid]".
  iModIntro.
  (* keep the persistent part if its public *)
  iAssert (nt $$ tk ∗ if tk is tk_pub then nt $$ tk_pub else True)%I  with "[Hnt]" as "[$ Hpubt]".
  { destruct tk; eauto. }
  iExists v_t, v_s. iSplit; first done. iSplit; first done. iFrame "Ht Hs".

  iAssert (⌜retag σ_t.(sst) σ_t.(snp) σ_t.(scs) c l ot FnEntry pk T = Some (Tagged nt, α', S (σ_t.(snp)))⌝)%I as "%Hretag_t".
  { iPoseProof (state_rel_calls_eq with "Hsrel") as "<-".
    iPoseProof (state_rel_stacks_eq with "Hsrel") as "<-".
    subst nt. iPoseProof (state_rel_snp_eq with "Hsrel") as "<-". done. }
  (* proving the value relation. TODO: duplicate  *)
  iAssert (value_rel v_t v_s)%I as "#Hvrel"; last iFrame "Hvrel".
  { iApply big_sepL2_forall; iSplit; first (iPureIntro;lia).
    iIntros (i sc_t sc_s) "%Hs_t %Hs_v".
    assert (i < tsize T)%nat as Hi. { rewrite -Hlen_t. eapply lookup_lt_is_Some_1. eauto. }
    assert (Hsome_target : is_Some (σ_t.(shp) !! (l +ₗ i))).
    { rewrite Hshp_t; last done. apply lookup_lt_is_Some_2. by rewrite Hlen_t. }
    iPoseProof (state_rel_pub_if_not_priv _ _ _ _ _ _ (l +ₗ i) with "[] Hsrel [Hrel]") as "Hpub"; first done.
    { iPoseProof (state_rel_calls_eq with "Hsrel") as "%Hcall_eq".
      iPoseProof (state_rel_stacks_eq with "Hsrel") as "%Hstack_eq".
      iPureIntro. intros t Hpriv.
      eapply (priv_loc_UB_retag_access_eq σ_s σ_t); eauto; done. }
    iPoseProof (pub_loc_lookup with "[] Hpub") as "(%sc_t' & %sc_s' & %Hread_both & Hsc_rel)"; first done.
    enough (sc_t = sc_t' ∧ sc_s = sc_s') by naive_solver.
    move : Hs_t Hs_v Hread_both (Hshp_s i Hi) (Hshp_t i Hi).
    by move => -> -> [-> ->] [= ->] [= ->].
  }

  iFrame "Hcid". iSplitL "Hpubt".
  { destruct mut; first done. iSplitR; first done. iRight.
    iExists (σ_t.(snp)), (σ_t.(snp)). do 3 (iSplitR; first done). done. }

  (* re-establishing the interpretation *)
  iExists (<[c:=M']> M_call), (<[ nt := (tk, ()) ]> M_tag), (array_tag_map l nt v_t ∪ M_t), (array_tag_map l nt v_s ∪ M_s).
  iFrame. iSplitL.
  { (* tainted *) iApply (tag_tainted_interp_retag with "Htainted"); done. }
  iSplitL.
  { (* state relation *)
    rewrite /state_rel. simpl. iDestruct "Hsrel" as "(-> & %Hs_eq & -> & -> & -> & Hsrel)".
    do 5 (iSplitL; first done). iIntros (l' Hsl').
    iDestruct ("Hsrel" $! l' with "[//]") as "[Hpub | [%t' %Hpriv]]"; first (iLeft; iApply "Hpub").
    iRight. iPureIntro. exists t'.
    destruct Hpriv as (tk' & Hsome_tk' & Ht_l' & Htk'). exists tk'.
    assert (t' ≠ nt). { intros ->. simplify_eq. }
    rewrite lookup_insert_ne; last done.
    split; first done. split.
    - destruct Ht_l' as (sc0 & Ht_l'). exists sc0.
      rewrite lookup_union_r; first done.
      destruct (array_tag_map l nt v_t !! (t', l')) as [ a | ] eqn:Harr; last done.
      specialize (array_tag_map_lookup1 l nt v_t t' l' ltac:(eauto)) as [Heq _]. congruence.
    - destruct Htk' as [-> | [-> [c' Hin]]]; first by left. right. split; first done. exists c'.
      destruct (decide (c' = c)) as [-> | Hneq].
      + exists M'. rewrite lookup_insert_eq; split; first done.
        destruct Hin as (M'' & HM'' & (L' & HL' & Hin)). simplify_eq. exists L'.
        rewrite lookup_insert_ne; done.
      + destruct Hin as (M'' & HM'' & Hin). exists M''. rewrite lookup_insert_ne; done.
  }
  iSplitL.
  { (* call interpretation. *)
    iPureIntro. intros c' M''. destruct (decide (c' = c)) as [-> | Hneq].
    - rewrite lookup_insert_eq. intros [= <-]. simpl.
      specialize (Hcall_interp c M HM_c) as (Hc & Hinterp). split; first done.
      intros t S. subst M'. destruct (decide (t = σ_t.(snp))) as [-> | Hneq]; first last.
      { rewrite lookup_insert_ne; last done. intros [Ht Hprot]%Hinterp. split; first lia.
        intros l' Hl'. specialize (Hprot l' Hl') as (s & pm' & Hs & Hit & Hpm').
        specialize (retag_item_active_preserving _ _ _ _ _ _ _ _ _ _ _ _ Hretag_t l' s (Tagged t) c pm' Hs Hc Hit) as (s' & -> & Hin'). eauto.
      }
      rewrite lookup_insert_eq. intros [= <-]. split; first lia. subst L.
      intros l'. rewrite seq_loc_set_elem. intros (i & Hi & ->).
      eapply retag_fn_entry_item_active; done.
    - (* TODO: duplication *)
      rewrite lookup_insert_ne; last done. simpl. intros [Hc' HM']%Hcall_interp.
      split; first done.
      intros t' S HS. simpl. specialize (HM' t' S HS) as (Ht' & Hprot).
      split; first lia. intros l' Hl'.
      specialize (Hprot l' Hl') as (s & pm' & Hs & Hit & Hpm').
      specialize (retag_item_active_preserving _ _ _ _ _ _ _ _ _ _ _ _ Hretag_t l' s (Tagged t') c' pm' Hs Hc' Hit) as (s' & -> & Hin'). eauto.
  }
  iSplitL.
  { (* tag interpretation. *)
    (* TODO: completely duplicated with the default lemma ... *)
    iPoseProof (state_rel_get_pure with "Hsrel") as "%Hp".
    destruct Hp as (Hsst & Hsnp & Hsnc & Hscs).
    assert (∀l', M_t !! (nt, l') = None) as HMt_nt.
    { intros l'. destruct (M_t !! (nt, l')) eqn:HM_t; last done.
      specialize (Ht_dom nt l' ltac:(eauto)) as (? & ?); congruence. }
    assert (∀l', M_s !! (nt, l') = None) as HMs_nt.
    { intros l'. destruct (M_s !! (nt, l')) eqn:HM_s; last done.
      specialize (Hs_dom nt l' ltac:(eauto)) as (? & ?); congruence. }
    iPureIntro. split_and!.
    { intros t tk'. rewrite lookup_insert_Some. intros [[<- [= <-]] | [Hneq Hsome_t]].
      - cbn. split_and!; [lia | lia | | |].
        + intros l' sc_t Ha%lookup_union_Some_inv_l; last done.
          specialize (array_tag_map_lookup2 l nt v_t nt l' ltac:(eauto)) as [_ (i & Hi & ->)].
          eapply loc_controlled_retag_ref; [ done | done | done | lia | ].
          move : Ha. rewrite array_tag_map_lookup_Some; last done. move => <-. apply Hshp_t. lia.
        + intros l' sc_s Ha%lookup_union_Some_inv_l; last done.
          specialize (array_tag_map_lookup2 l nt v_s nt l' ltac:(eauto)) as [_ (i & Hi & ->)].
          subst nt. rewrite -Hsnp. eapply loc_controlled_retag_ref; [ done | done | done | lia | ].
          move : Ha. rewrite array_tag_map_lookup_Some; last done. move => <-. apply Hshp_s. lia.
        + apply dom_agree_on_tag_union. { apply dom_agree_on_tag_array_tag_map. lia. }
          apply dom_agree_on_tag_not_elem; done.
      - cbn.
        specialize (Htag_interp t tk' Hsome_t) as (Ht_t & Ht_s & Hcontrolled_t & Hcontrolled_s & Hagree).
        split_and!; [ lia | lia | | | ].
        + intros l' sc_t Ha. rewrite lookup_union_r in Ha; last by apply array_tag_map_lookup_None.
          apply Hcontrolled_t in Ha.
          eapply loc_controlled_retag_update; [done | done | | done | done].
          intros <-. destruct tk'; [ done | | ]; move : Hsome_t Hpub; congruence.
        + intros l' sc_s Ha. rewrite lookup_union_r in Ha; last by apply array_tag_map_lookup_None.
          apply Hcontrolled_s in Ha.
          eapply loc_controlled_retag_update; [done | done | | done | done].
          intros <-. destruct tk'; [ done | | ]; move : Hsome_t Hpub; congruence.
        + apply dom_agree_on_tag_union; last done.
          apply dom_agree_on_tag_not_elem; apply array_tag_map_lookup_None; done.
    }
    { intros t l'.
      rewrite lookup_union_is_Some lookup_insert_is_Some'. intros [[-> _]%array_tag_map_lookup2 | H%Ht_dom]; eauto. }
    { intros t l'.
      rewrite lookup_union_is_Some lookup_insert_is_Some'. intros [[-> _]%array_tag_map_lookup2 | H%Hs_dom]; eauto. }
  }
  done.
Qed.

Lemma sim_retag_fnentry mut T l_t l_s c M ot π Φ :
  (0 < tsize T)%nat → (* for convenience: makes the proof easier *)
  let pk : pointer_kind := RefPtr mut in
  let pm := match mut with Mutable => Unique | Immutable => SharedReadOnly end in
  let tk := match mut with Mutable => tk_unq | Immutable => tk_pub end in
  (if mut is Immutable then is_freeze T else True) →
  sc_rel (ScPtr l_t ot) (ScPtr l_s ot) -∗
  c @@ M -∗
  (∀ nt v_t v_s,
    let L := seq_loc_set l_t (tsize T) in   (* uses that l_t = l_s *)
    ⌜length v_t = tsize T⌝ -∗ ⌜length v_s = tsize T⌝ -∗
    value_rel v_t v_s -∗  (*as the pointers were public before *)
    c @@ <[nt := L]> M -∗
    nt $$ tk -∗
    l_t ↦t∗[tk]{nt} v_t -∗
    l_s ↦s∗[tk]{nt} v_s -∗
    (if mut is Immutable then sc_rel (ScPtr l_t (Tagged nt)) (ScPtr l_s (Tagged nt)) else True) -∗
    #[ScPtr l_t (Tagged nt)] ⪯{π} #[ScPtr l_s (Tagged nt)] [{ Φ }]) -∗
  Retag #[ScPtr l_t ot] #[ScCallId c] pk T FnEntry ⪯{π} Retag #[ScPtr l_s ot] #[ScCallId c] pk T FnEntry [{ Φ }].
Proof.
  intros Hsize pk pm tk Hmut. iIntros "#Hscrel Hcid Hsim".
  iApply sim_lift_base_step_both. iIntros (P_t P_s σ_t σ_s ??) "((HP_t & HP_s & Hbor) & %Hthread & %Hsafe)".
  (* exploit source to gain knowledge about stacks & that c is a valid id *)
  specialize (pool_safe_implies Hsafe Hthread) as (c' & ot' & l' & [= <- <-] & [= <-] & Hc_active & Hretag_some_s).
  iPoseProof "Hscrel" as "(-> & _)".
  iPoseProof (bor_interp_get_pure with "Hbor") as "%Hp".
  have Hretag_some_t : is_Some (retag σ_t.(sst) σ_t.(snp) σ_t.(scs) c l_s ot FnEntry pk T).
  { destruct Hp as (<- & <- & _ & <- & _). done. }
  iModIntro. iSplitR.
  { iPureIntro.
    destruct Hretag_some_t as ([[] ] & Hretag_some_t).
    do 3 eexists. eapply retag_base_step'; last done.
    destruct Hp as (_ & _ & _ & <- & _). done.
  }
  iIntros (e_t' efs_t σ_t') "%Hhead_t".
  specialize (head_retag_inv _ _ _ _ _ _ _ _ _ _ _ Hhead_t) as (nt & α' & nxtp' & Hretag_t & -> & -> & -> & Hc).
  have Hretag_s : retag σ_s.(sst) σ_s.(snp) σ_s.(scs) c l_s ot FnEntry pk T = Some (nt, α', nxtp').
  { destruct Hp as (-> & -> & _ & -> & _). done. }
  assert (Hhead_s : base_step P_s (Retag #[ScPtr l_s ot] #[ScCallId c] pk T FnEntry) σ_s #[ScPtr l_s nt]%E (mkState (shp σ_s) α' (scs σ_s) nxtp' (snc σ_s)) []).
  { eapply retag_base_step'; done. }
  specialize (retag_change_ref_NZST _ _ _ _ _ _ _ _ _ _ _ _ Hsize Hretag_s) as [-> ->].

  iPoseProof (bor_interp_get_state_wf with "Hbor") as "[%Hwf_t %Hwf_s]".
  iMod (bor_interp_retag_fnentry _ _ _ _ _ _ _ _ _ Hretag_s with "Hscrel Hcid Hbor") as
    (v_t v_s) "(%Hlen_t & %Hlen_s & Hval & Hcid & Htag & Ht & Hs & Hpub & Hbor)"; first done.
  { destruct Hp as (_ & <- & _). eapply base_step_wf; eauto. }
  { eapply base_step_wf; eauto. }
  iModIntro.

  iExists #[ScPtr l_s (Tagged σ_s.(snp))]%E, [], (mkState σ_s.(shp) α' σ_s.(scs) (S σ_s.(snp)) σ_s.(snc)).
  iSplitR; first done.
  destruct Hp as (_ & -> & _).
  iFrame "Hbor HP_t HP_s".
  iSplitL; last done.
  iApply ("Hsim" with "[] [] Hval Hcid Htag Ht Hs Hpub"); [done | done | ..].
Qed.

(** ** Updates for calls sets *)
(* TODO: maybe formulate that with [update_si] instead *)
Lemma sim_protected_unprotectN M L l c t tk v_t v_s  π Φ e_t e_s :
  (∀ i : nat, (i < length v_t)%nat → (l +ₗ i) ∈ L) →
  M !! t = Some L →
  c @@ M -∗
  t $$ tk -∗
  l ↦t∗[tk]{t} v_t -∗
  l ↦s∗[tk]{t} v_s -∗
  value_rel v_t v_s -∗
  (c @@ (<[t := L ∖ (seq_loc_set l (length v_t)) ]> M) -∗ t $$ tk -∗ l ↦t∗[tk]{t} v_t -∗ l ↦s∗[tk]{t} v_s -∗ e_t ⪯{π} e_s [{ Φ }]) -∗
  e_t ⪯{π} e_s [{ Φ }].
Proof.
  iIntros (Hl HL) "Hc Htag Ht Hs #Hvrel Hsim".
  iApply sim_update_si. rewrite /update_si. iIntros (?????) "(HP_t & HP_s & Hbor)".
  set (L' := L ∖ seq_loc_set l (length v_t)). set (M' := <[ t := L' ]> M).
  iPoseProof (value_rel_length with "Hvrel") as "%Hlen".
  iPoseProof (bor_interp_readN_source_protected with "Hbor Hs Htag Hc") as "(%Hv_s & %)".
  { intros i Hi. exists L. split; first done. apply Hl. lia. }
  iPoseProof (bor_interp_readN_target_protected with "Hbor Ht Htag Hc") as "(%Hv_t & %)".
  { intros i Hi. exists L. split; first done. apply Hl. lia. }

  iDestruct "Hbor" as "(%M_call & %M_tag & %M_t & %M_s & (Hcall_auth & Htag_auth & Htag_t_auth & Htag_s_auth) & Htainted & Hpub_cid & #Hsrel & %Hcall_interp & %Htag_interp & %Hwf_s & %Hwf_t)".
  iPoseProof (ghost_map_lookup with "Hcall_auth Hc") as "%HcM".
  iMod (ghost_map_update M' with "Hcall_auth Hc") as "[Hcall_auth Hc]".
  iModIntro. iFrame "HP_t HP_s". iSplitR "Hsim Hc Ht Htag Hs"; last by iApply ("Hsim" with "Hc Htag Ht Hs").
  iExists (<[ c := M' ]> M_call), M_tag, M_t, M_s. iFrame.
  iSplitL "Hsrel".
  { iDestruct "Hsrel" as "(%Hdom_eq & %Hsst_eq & %Hsnp_eq & %Hsnc_eq & %Hscs_eq & Hloc)".
    do 5 (iSplitR; first done).
    iIntros (l' Hl'). iDestruct ("Hloc" $! l' with "[//]") as "[Hpub | %Hpriv]"; first by iLeft.
    destruct (decide (l' ∈ seq_loc_set l (length v_t))) as [(i & Hi & ->)%seq_loc_set_elem | Hnotin].
    - (* location is made public *)
      iLeft. iIntros (sc_t' Hsc_t').
      specialize (Hv_t i Hi) as Heq. rewrite Heq in Hsc_t'.
      iExists (v_s !!! i). iSplitR.
      + iPureIntro. rewrite Hv_s; last lia. apply list_lookup_lookup_total, lookup_lt_is_Some_2. lia.
      + iPoseProof (value_rel_lookup_total v_t v_s i with "Hvrel") as "Hsc"; first lia.
        rewrite -(list_lookup_total_correct _ _ _ Hsc_t'). done.
    - (* location is still private *)
      iRight. iPureIntro. destruct Hpriv as (t' & tk' & Htk' & Hsome & Hpriv).
      exists t', tk'. split; first done. split; first done.
      destruct Hpriv as [-> | [-> Hpriv]]; first by left. right; split; first done.
      destruct Hpriv as (c' & M'' & Hc' & Hin').
      destruct (decide (c' = c)) as [-> | Hneq]; first last.
      { exists c', M''. rewrite lookup_insert_ne; done. }
      exists c, M'. rewrite lookup_insert_eq. split; first done.
      destruct (decide (t' = t)) as [-> | Hneq']; first last.
      { destruct Hin' as (L'' & HL'' & Hl''). exists L''. split; last done.
        simplify_eq. rewrite lookup_insert_ne; done.
      }
      destruct Hin' as (L'' & HL'' & Hl''). exists L'. split; first by rewrite lookup_insert_eq.
      simplify_eq. subst L'. apply elem_of_difference. done.
  }
  iSplitL; last done.
  iPureIntro. intros c' M''. rewrite lookup_insert_Some. intros [[<- <-] | [Hneq Hsome]].
  - apply Hcall_interp in HcM as [Hc HcM]. split; first done.
    intros t' L''. subst M'. rewrite lookup_insert_Some. intros [[<- <-] | [Hneq' Hsome']].
    + specialize (HcM t L HL) as (Ht & HsL). split; first done.
      intros l'. rewrite elem_of_difference. intros [Hl'%HsL _]. done.
    + specialize (HcM _ _ Hsome') as (Ht & HsL). done.
  - apply Hcall_interp in Hsome as [Hc' Hsome]. done.
Qed.

Lemma sim_protected_unprotect M L l c t tk sc_t sc_s π Φ e_t e_s :
  l ∈ L →
  M !! t = Some L →
  c @@ M -∗
  t $$ tk -∗
  l ↦t[tk]{t} sc_t -∗
  l ↦s[tk]{t} sc_s -∗
  sc_rel sc_t sc_s -∗
  (c @@ (<[t := L ∖ {[ l ]} ]> M) -∗ t $$ tk -∗ l ↦t[tk]{t} sc_t -∗ l ↦s[tk]{t} sc_s -∗ e_t ⪯{π} e_s [{ Φ }]) -∗
  e_t ⪯{π} e_s [{ Φ }].
Proof.
  iIntros (Hin HL) "Hc Htag Ht Hs Hrel Hsim".
  iApply (sim_protected_unprotectN M L l c t tk [sc_t] [sc_s] with "Hc Htag [Ht] [Hs] [Hrel] [Hsim]").
  - simpl. intros i Hi. replace i with O by lia. rewrite shift_loc_0_nat. done.
  - done.
  - iApply big_sepL_singleton. rewrite shift_loc_0_nat. done.
  - iApply big_sepL_singleton. rewrite shift_loc_0_nat. done.
  - iApply big_sepL2_singleton. done.
  - simpl. rewrite shift_loc_0_nat union_empty_r_L.
    rewrite /array_tag !big_sepL_singleton !shift_loc_0_nat. done.
Qed.

Lemma sim_remove_empty_calls t L M c e_t e_s π Φ :
  M !! t = Some L →
  L = ∅ →
  c @@ M -∗
  (c @@ (delete t M) -∗ e_t ⪯{π} e_s [{ Φ }]) -∗
  e_t ⪯{π} e_s [{ Φ }].
Proof.
  iIntros (Ht ->) "Hc Hsim".
  iApply sim_update_si. rewrite /update_si. iIntros (?????) "(HP_t & HP_s & Hbor)".
  set (M' := delete t M).
  iDestruct "Hbor" as "(%M_call & %M_tag & %M_t & %M_s & (Hcall_auth & Htag_auth & Htag_t_auth & Htag_s_auth) & Htainted & Hpub_cid & #Hsrel & %Hcall_interp & %Htag_interp & %Hwf_s & %Hwf_t)".
  iPoseProof (ghost_map_lookup with "Hcall_auth Hc") as "%HcM".
  iMod (ghost_map_update M' with "Hcall_auth Hc") as "[Hcall_auth Hc]".
  iModIntro. iFrame "HP_t HP_s". iSplitR "Hsim Hc"; last by iApply ("Hsim" with "Hc").
  iExists (<[ c := M' ]> M_call), M_tag, M_t, M_s. iFrame.
  iSplitL "Hsrel".
  { iDestruct "Hsrel" as "(%Hdom_eq & %Hsst_eq & %Hsnp_eq & %Hsnc_eq & %Hscs_eq & Hloc)".
    do 5 (iSplitR; first done).
    iIntros (l' Hl'). iDestruct ("Hloc" $! l' with "[//]") as "[Hpub | %Hpriv]"; first by iLeft.
    iRight. iPureIntro. destruct Hpriv as (t' & tk' & Htk' & Hsome & Hpriv).
    exists t', tk'. split; first done. split; first done.
    destruct Hpriv as [-> | [-> Hpriv]]; first by left. right; split; first done.
    destruct Hpriv as (c' & M'' & Hc' & Hin').
    destruct (decide (c' = c)) as [-> | Hneq]; first last.
    { exists c', M''. rewrite lookup_insert_ne; done. }
    exists c, M'. rewrite lookup_insert_eq. split; first done.
    destruct (decide (t' = t)) as [-> | Hneq']; first last.
    { destruct Hin' as (L'' & HL'' & Hl''). exists L''. split; last done.
      simplify_eq. rewrite lookup_delete_ne; done.
    }
    exfalso. destruct Hin' as (L'' & HL'' & Hl''). simplify_eq. done.
  }
  iSplitL; last done.
  iPureIntro. intros c' M''. rewrite lookup_insert_Some. intros [[<- <-] | [Hneq Hsome]].
  - apply Hcall_interp in HcM as [Hc HcM]. split; first done.
    intros t' L''. subst M'. rewrite lookup_delete_Some. intros [Hneq' Hsome']. naive_solver.
  - apply Hcall_interp in Hsome as [Hc' Hsome]. done.
Qed.

(** ** Write lemmas *)

(* the (admittedly slightly complicated) update lemma for [sim_write_unique_protected] *)
Lemma loc_controlled_write_unprotected t t' tk n l l' σ v M sc :
  (t = t' → tk = tk_unq) →
  state_wf σ →
  length v = n →
  memory_written σ.(sst) σ.(scs) l (Tagged t) n = Some σ.(sst) →
  (∀ i:nat, (i < n)%nat → bor_state_own (l +ₗ i) t tk_unq σ) →
  (∀l sc, M !! (t', l) = Some sc → loc_controlled l t' tk sc σ) →
  (array_tag_map l t v ∪ M) !! (t', l') = Some sc →
  loc_controlled l' t' tk sc (mkState (write_mem l v σ.(shp)) σ.(sst) σ.(scs) σ.(snp) σ.(snc)).
Proof.
  intros Hunq Hwf Hlen Hstacks Hown Hcontrol.
  destruct (decide (t = t')) as [<- | Hneq]; first last.
  { rewrite lookup_union_r; last by apply array_tag_map_lookup_None.
    intros ?.
    eapply loc_controlled_write_update; [ done | | done | lia | by apply Hcontrol].
    intros [[= <-] _]; done.
  }
  (* same tag *)
  destruct (decide (l' ∈ seq_loc_set l n)) as [(i & Hi & ->)%seq_loc_set_elem | Hneq_loc].
  * intros Hsc. (* this is where the work happens *)
    specialize (array_tag_map_lookup_Some l t v i ltac:(lia)) as Hl1.
    rewrite (lookup_union_Some_l _ M _ (v !!! i)) in Hsc.
    2: { rewrite Hl1. rewrite list_lookup_lookup_total; first done.
      apply lookup_lt_is_Some_2. lia. }
    injection Hsc as [= <-].
    intros _. split; first last.
    { simpl. rewrite (proj1 (write_mem_lookup _ _ _)); last lia.
      rewrite list_lookup_lookup_total; first done. apply lookup_lt_is_Some_2. lia. }
    rewrite Hunq; last done. apply Hown. lia.
  * rewrite lookup_union_r; first last.
    { apply array_tag_map_lookup_None'. intros i Hi. contradict Hneq_loc.
      apply seq_loc_set_elem. exists i. split; first lia. done.
    }
    intros ?.
    eapply loc_controlled_write_update; [ done | | done | lia | apply Hcontrol; done].
    intros [_ (i & -> & Hi)]. exfalso; apply Hneq_loc.
    apply seq_loc_set_elem. eauto.
Qed.

Lemma sim_write_unique_unprotected π l t T v_t v_s v_t' v_s' Φ :
  length v_t = tsize T →
  length v_s = tsize T →
  t $$ tk_unq -∗
  l ↦t∗[tk_unq]{t} v_t -∗
  l ↦s∗[tk_unq]{t} v_s -∗
  (* crucial: without protectors, we need to write related values, as the locations
    will need to be public in the state_rel -- after all, there is no protector, so it can't be private! *)
  value_rel v_t' v_s' -∗
  (t $$ tk_unq -∗ l ↦t∗[tk_unq]{t} v_t' -∗ l ↦s∗[tk_unq]{t} v_s' -∗ #[☠] ⪯{π} #[☠] [{ Φ }]) -∗
  Write (Place l (Tagged t) T) #v_t' ⪯{π} Write (Place l (Tagged t) T) #v_s' [{ Φ }].
Proof.
  (* get the loc controlled things. exploit source UB. update the ghost state. *)
  iIntros (Hlen_t Hlen_s) "Htag Ht Hs #Hvrel Hsim".
  iApply sim_lift_base_step_both. iIntros (P_t P_s σ_t σ_s ??) "[(HP_t & HP_s & Hbor) %Hsafe]".
  iPoseProof (bor_interp_readN_target with "Hbor Ht Htag") as "%Hcontrol_t".
  iPoseProof (bor_interp_readN_source with "Hbor Hs Htag") as "%Hcontrol_s".

  iModIntro.
  destruct Hsafe as [Hpool Hsafe].
  specialize (pool_safe_implies Hsafe Hpool) as (Hread_s & (α' & Hstack_s) & Hlen_s').
  iPoseProof (value_rel_length with "Hvrel") as "%Hlen_t'".

  iPoseProof (bor_interp_get_pure with "Hbor") as "%Hp".
  destruct Hp as (Hsst_eq & Hsnp_eq & Hsnc_eq & Hscs_eq & Hwf_s & Hwf_t & Hdom_eq).

  (* from source reduction, we get that bor_state_pre is satisfied for the affected locations *)
  assert (∀ i, (i < length v_s)%nat → bor_state_own (l +ₗ i) t tk_unq σ_s ∧ bor_state_own (l +ₗ i) t tk_unq σ_t) as Hcontrol_own.
  { intros i Hi.
    destruct (Hcontrol_s i Hi) as [Hown _].
    { specialize (for_each_lookup_case_2 _ _ _ _ _ Hstack_s) as [Hs _].
      specialize (Hs i ltac:(lia)) as (stk0 & stk' & Hstk0 & Hstk' & Hacc1').
      destruct access1 as [[] | ] eqn:Hacc1; last done.
      specialize (access1_in_stack _ _ _ _ _ _ Hacc1) as (it & Hit & Htg & Hperm).
      destruct it as [perm tg opro]. simpl in *. simplify_eq.
      all: exists stk0, perm, opro; done.
    }
    split; first done.
    move : Hown. rewrite /bor_state_own. setoid_rewrite Hsst_eq. done.
  }
  assert (α' = σ_s.(sst)) as ->.
  { rewrite (memory_written_access1 σ_s.(sst)) in Hstack_s; first congruence.
    intros i Hi.
    specialize (Hcontrol_own i ltac:(lia)) as [Hown _].
    generalize Hown => Hown'. destruct Hown as (stk & Hstk & ?).
    eexists; split; first done.
    eapply bor_state_own_access1_write; [ by right | done..].
  }

  iSplitR.
  { iPureIntro. do 3 eexists. eapply write_base_step'; [lia | |].
    - rewrite -Hdom_eq. intros n Hn. apply Hread_s. lia.
    - instantiate (1 := σ_s.(sst)). rewrite -Hsst_eq -Hscs_eq. done.
  }
  iIntros (e_t' efs_t σ_t') "%Hhead_t".
  specialize (head_write_inv _ _ _ _ _ _ _ _ _ Hhead_t) as (α'0 & -> & -> & -> & _ & Hin_dom & Hstack_t).
  iAssert (⌜α'0 = σ_s.(sst)⌝)%I as "->".
  { iPureIntro. move : Hstack_t Hstack_s. rewrite Hsst_eq Hscs_eq. congruence. }

  (* update the ghost state.
    no separate lemma for, this is quite an atomic operation. *)
  iDestruct "Hbor" as "(%M_call & %M_tag & %M_t & %M_s & (Hc & Htag_auth & Htag_t_auth & Htag_s_auth) & Htainted & Hpub_cid & #Hsrel & %Hcall_interp & %Htag_interp & _ & _)".
  iMod (ghost_map_array_tag_update _ _ _ v_t' with "Htag_t_auth Ht") as "[Ht Htag_t_auth]"; first lia.
  iMod (ghost_map_array_tag_update _ _ _ v_s' with "Htag_s_auth Hs") as "[Hs Htag_s_auth]"; first lia.
  iPoseProof (tkmap_lookup with "Htag_auth Htag") as "%".

  iModIntro.
  pose (σ_s' := (mkState (write_mem l v_s' σ_s.(shp)) σ_s.(sst) σ_s.(scs) σ_s.(snp) σ_s.(snc))).
  assert (Hhead_s : base_step P_s (Write (Place l (Tagged t) T) v_s') σ_s (ValR [☠]%S) σ_s' []).
  { eapply write_base_step'; eauto. intros. rewrite Hdom_eq. apply Hin_dom. lia. }
  iExists (#[☠])%E, [], σ_s'. iSplitR; first done.
  iFrame "HP_t HP_s".
  iSplitR "Hsim Hs Ht Htag"; first last.
  { iSplitL; last done. iApply ("Hsim" with "Htag Ht Hs"). }

  (* we keep the base_step hypotheses to use the [base_step_wf] lemma below *)
  (* re-establish the invariants *)
  (* TODO: large parts of this, except for the tag interpretation, are similar to
    the write_public lemma *)
  iExists M_call, M_tag, (array_tag_map l t v_t' ∪ M_t), (array_tag_map l t v_s' ∪ M_s).
  iFrame "Hc Htag_auth Htag_t_auth Htag_s_auth".
  iSplitL "Htainted"; last iSplitL "Hpub_cid"; last iSplit; last iSplit; last iSplit; last iSplit.
  - (* tainted *)
    subst σ_s'. iApply (tag_tainted_interp_tagged_sublist with "Htainted"); simpl; first lia.
    intros l' stk' Hstk'.
    specialize (for_each_access1 _ _ _ _ _ _ _ Hstack_s _ _ Hstk') as (stk & Hstk & Hsubl & _).
    eauto.
  - (* pub cid *)
    iApply (pub_cid_interp_preserve_sub with "Hpub_cid"); done.
  - (* state rel *)
    rewrite /state_rel; simpl. iSplitL.
    { iPureIntro. apply gset_leibniz. rewrite !write_mem_dom; [by rewrite Hdom_eq | done..]. }
    do 4 (iSplitL; first done). iDestruct "Hsrel" as "(_ & _ & _ & _ & _ & Hsrel)".
    iIntros (l') "%Hs".
    specialize (write_mem_lookup l v_s' σ_s.(shp)) as (Heq & Heq').
    specialize (write_mem_lookup_case l v_t' σ_t.(shp) l') as [(i & Hi & -> & Hwrite) | (Hi & Hwrite)].
    + (* we wrote to the location, and the written values must be related *)
      iLeft. iIntros (sc_t Hsc_t). simpl in Hsc_t. rewrite Heq; last lia.
      iExists (v_s' !!! i). rewrite Hwrite in Hsc_t.
      rewrite -(list_lookup_total_correct _ _ _ Hsc_t).
      iSplitR. { iPureIntro. apply list_lookup_lookup_total. apply lookup_lt_is_Some_2. lia. }
      iApply (value_rel_lookup_total with "Hvrel"). lia.
    + (* unaffected location *)
      simpl. rewrite Hwrite in Hs.
      iDestruct ("Hsrel" $! l' with "[//]") as "[Hpubl | (%t' & %Hprivl)]".
      * iLeft. rewrite /pub_loc Hwrite Heq'; first done. intros. apply Hi. lia.
      * iRight. iPureIntro. exists t'.
        destruct Hprivl as (tk & ? & ? & ?). exists tk. split_and!; [done | | done].
        apply lookup_union_is_Some. by right.
  - (* call invariant *)
    iPureIntro. intros c M' HM'_some. simpl.
    specialize (Hcall_interp c M' HM'_some) as (Hin & Hprot).
    split; first done. intros t' L [Ht HL]%Hprot. split; first done.
    intros l' (stk & pm & Hsome_stk & Hit & Hpm)%HL.
    specialize (for_each_access1_active_preserving _ _ _ _ _ _ _ Hstack_t _ _ Hsome_stk) as (stk' & Hstk'_some & Hac_pres).
    exists stk', pm. split; last split; [ done | by apply Hac_pres| done ].
  - (* tag invariant *)
    iPureIntro. destruct Htag_interp as (Htag_interp & Ht_dom & Hs_dom). split_and!; [ | | | done..].
    { intros t' tk Ht.
      specialize (Htag_interp _ _ Ht) as (? & ? & Hcontrolled_t & Hcontrolled_s & Hdom).
      split_and!; [ done | done | | | ].
      - intros l' sc_t Hsc. rewrite Hsst_eq.
        eapply (loc_controlled_write_unprotected _ _ _ (tsize T) _ _ σ_t);
          [ | done | lia | | intros; apply Hcontrol_own; lia | done | apply Hsc].
          + intros ->. simplify_eq. done.
          + rewrite -Hsst_eq -Hscs_eq. done.
      - intros l' sc_s Hsc.
        eapply (loc_controlled_write_unprotected _ _ _ (tsize T) _ _ σ_s);
          [ | done | lia | | intros; apply Hcontrol_own; lia | done | apply Hsc].
          + intros ->. simplify_eq. done.
          + done.
      - apply dom_agree_on_tag_union; last done.
        destruct (decide (t' = t)) as [-> | Hneq].
        + apply dom_agree_on_tag_array_tag_map. lia.
        + apply dom_agree_on_tag_not_elem; apply array_tag_map_lookup_None; done.
    }
    { intros t' l'. rewrite lookup_union_is_Some.
      intros [[-> _]%array_tag_map_lookup1 | ?]; by eauto.
    }
    { intros t' l'. rewrite lookup_union_is_Some.
      intros [[-> _]%array_tag_map_lookup1 | ?]; by eauto.
    }
  - (* source state wf *)
    iPureIntro. eapply base_step_wf; done.
  - (* target state wf *)
    iPureIntro. eapply base_step_wf; done.
Qed.

Lemma target_write_local v_t v_t' T l t Ψ :
  length v_t = tsize T →
  length v_t' = tsize T →
  t $$ tk_local -∗
  l ↦t∗[tk_local]{t} v_t -∗
  (l ↦t∗[tk_local]{t} v_t' -∗ t $$ tk_local -∗ target_red #[☠] Ψ)%E -∗
  target_red (Write (Place l (Tagged t) T) #v_t') Ψ.
Proof.
  iIntros (Hlen Hlen') "Htag Ht Hsim".
  iApply target_red_lift_base_step. iIntros (P_t σ_t P_s σ_s ?) "(HP_t & HP_s & Hbor)".
  iPoseProof (bor_interp_readN_target_local with "Hbor Ht Htag") as "(%Hd & %Hstack)".
  iMod (bor_interp_writeN_target_local _ _ _ _ _ v_t' with "Hbor Ht Htag []") as "(Hbor & Ht & Htag)";
    first (iPureIntro; lia).
  iModIntro.
  rewrite Hlen in Hd Hstack.
  iPoseProof (bor_interp_get_state_wf with "Hbor") as "[%Hwf_t %]".
  have Eq_stk : memory_written σ_t.(sst) σ_t.(scs) l (Tagged t) (tsize T) = Some σ_t.(sst).
  { apply memory_written_access1. intros i Hi.
    specialize (Hstack i Hi). eexists; split; first done.
    eapply bor_state_own_access1_write; [ by left | done..]. }
  iSplitR.
  { iPureIntro. do 3 eexists; eapply write_base_step'; [done | | eauto ].
    intros i Hi. apply elem_of_dom. rewrite Hd; last done. apply lookup_lt_is_Some_2. lia.
  }
  iIntros (e_t' efs_t σ_t') "%Hhead".
  specialize (head_write_inv _ _ _ _ _ _ _ _ _ Hhead) as (α' & -> & -> & -> & ? & Hin & Hwritten).
  simplify_eq.
  iModIntro. iSplitR; first done.
  iFrame "HP_t HP_s".
  iSplitL "Hbor"; last iApply ("Hsim" with "Ht Htag").
  done.
Qed.

Lemma source_write_local v_s v_s' T l t Ψ π :
  length v_s = tsize T →
  length v_s' = tsize T →
  t $$ tk_local -∗
  l ↦s∗[tk_local]{t} v_s -∗
  (l ↦s∗[tk_local]{t} v_s' -∗ t $$ tk_local -∗ source_red #[☠] π Ψ)%E -∗
  source_red (Write (Place l (Tagged t) T) #v_s') π Ψ.
Proof.
  iIntros (Hlen Hlen') "Htag Hs Hsim".
  iApply source_red_lift_base_step. iIntros (P_t σ_t P_s σ_s ??) "[(HP_t & HP_s & Hbor) _]".
  iPoseProof (bor_interp_readN_source_local with "Hbor Hs Htag") as "(%Hd & %Hstack)".
  iMod (bor_interp_writeN_source_local _ _ _ _ _ v_s' with "Hbor Hs Htag []") as "(Hbor & Hs & Htag)";
    first (iPureIntro; lia).
  iModIntro.
  rewrite Hlen in Hd Hstack.
  iPoseProof (bor_interp_get_state_wf with "Hbor") as "[% %Hwf_s]".
  have Eq_stk : memory_written σ_s.(sst) σ_s.(scs) l (Tagged t) (tsize T) = Some σ_s.(sst).
  { apply memory_written_access1. intros i Hi.
    specialize (Hstack i Hi). eexists; split; first done.
    eapply bor_state_own_access1_write; [ by left | done..]. }
  iExists _, _. iSplitR.
  { iPureIntro. eapply write_base_step'; [done | | eauto ].
    intros i Hi. apply elem_of_dom. rewrite Hd; last done. apply lookup_lt_is_Some_2. lia.
  }
  iModIntro. iFrame "HP_t HP_s".
  iSplitL "Hbor"; last iApply ("Hsim" with "Hs Htag").
  done.
Qed.

Lemma target_write_protected v_t v_t' T l t c M Ψ :
  length v_t = tsize T →
  length v_t' = tsize T →
  (∀ i: nat, (i < tsize T)%nat → call_set_in M t (l +ₗ i)) →
  c @@ M -∗
  t $$ tk_unq -∗
  l ↦t∗[tk_unq]{t} v_t -∗
  (l ↦t∗[tk_unq]{t} v_t' -∗ c @@ M -∗ t $$ tk_unq -∗ target_red #[☠] Ψ)%E -∗
  target_red (Write (Place l (Tagged t) T) #v_t') Ψ.
Proof.
  iIntros (Hlen Hlen' Hin_call) "Hc Htag Ht Hsim".
  iApply target_red_lift_base_step. iIntros (P_t σ_t P_s σ_s ?) "(HP_t & HP_s & Hbor)".
  iPoseProof (bor_interp_readN_target_protected with "Hbor Ht Htag Hc") as "(%Hd & %Hstack)".
  { rewrite Hlen. done. }
  iMod (bor_interp_writeN_target_protected _ _ _ _ _ v_t' with "Hbor Ht Htag Hc []") as "(Hbor & Ht & Hc & Htag)".
  { rewrite Hlen. done. }
  { iPureIntro; lia. }
  iModIntro.
  rewrite Hlen in Hd Hstack.
  iPoseProof (bor_interp_get_state_wf with "Hbor") as "[%Hwf_t %]".
  have Eq_stk : memory_written σ_t.(sst) σ_t.(scs) l (Tagged t) (tsize T) = Some σ_t.(sst).
  { apply memory_written_access1. intros i Hi.
    specialize (Hstack i Hi).
    destruct (bor_state_own_some_stack _ _ _ _ Hstack) as (stk & Hs_stk).
    exists stk. split; first done. eapply bor_state_own_access1_write; [by right | done..]. }
  iSplitR.
  { iPureIntro. do 3 eexists; eapply write_base_step'; [done | | eauto ].
    intros i Hi. apply elem_of_dom. rewrite Hd; last done. apply lookup_lt_is_Some_2. lia.
  }
  iIntros (e_t' efs_t σ_t') "%Hhead".
  specialize (head_write_inv _ _ _ _ _ _ _ _ _ Hhead) as (α' & -> & -> & -> & ? & Hin & Hwritten).
  simplify_eq.
  iModIntro. iSplitR; first done.
  iFrame "HP_t HP_s".
  iSplitL "Hbor"; last iApply ("Hsim" with "Ht Hc Htag").
  done.
Qed.

(* note: in principle we don't need the protectors since that will just be source UB,
    but we need the protector to be able to write anything into the location, without
    a sidecondition on what is currently in the target location, to be able to
    establish the state relation.
*)
Lemma source_write_protected v_s v_s' T l t Ψ c M π :
  length v_s = tsize T →
  length v_s' = tsize T →
  (∀ i: nat, (i < tsize T)%nat → call_set_in M t (l +ₗ i)) →
  c @@ M -∗
  t $$ tk_unq -∗
  l ↦s∗[tk_unq]{t} v_s -∗
  (l ↦s∗[tk_unq]{t} v_s' -∗ c @@ M -∗ t $$ tk_unq -∗ source_red #[☠] π Ψ)%E -∗
  source_red (Write (Place l (Tagged t) T) #v_s') π Ψ.
Proof.
  iIntros (Hlen Hlen' Hin_call) "Hc Htag Hs Hsim".
  iApply source_red_lift_base_step. iIntros (P_t σ_t P_s σ_s ??) "[(HP_t & HP_s & Hbor) _]".
  iPoseProof (bor_interp_readN_source_protected with "Hbor Hs Htag Hc") as "(%Hd & %Hstack)".
  { rewrite Hlen. done. }
  iMod (bor_interp_writeN_source_protected _ _ _ _ _ v_s' with "Hbor Hs Htag Hc []") as "(Hbor & Hs & Hc & Htag)".
  { rewrite Hlen. done. }
  { iPureIntro; lia. }
  iModIntro.
  rewrite Hlen in Hd Hstack.
  iPoseProof (bor_interp_get_state_wf with "Hbor") as "[% %Hwf_s]".
  have Eq_stk : memory_written σ_s.(sst) σ_s.(scs) l (Tagged t) (tsize T) = Some σ_s.(sst).
  { apply memory_written_access1. intros i Hi.
    specialize (Hstack i Hi).
    destruct (bor_state_own_some_stack _ _ _ _ Hstack) as (stk & Hs_stk).
    exists stk. split; first done. eapply bor_state_own_access1_write; [by right | done..]. }
  iExists _, _. iSplitR.
  { iPureIntro. eapply write_base_step'; [done | | eauto ].
    intros i Hi. apply elem_of_dom. rewrite Hd; last done. apply lookup_lt_is_Some_2. lia.
  }
  iModIntro. iFrame "HP_t HP_s".
  iSplitL "Hbor"; last iApply ("Hsim" with "Hs Hc Htag").
  done.
Qed.

(** ** Copy lemmas *)
Lemma target_copy_local v_t T l t Ψ :
  length v_t = tsize T →
  t $$ tk_local -∗
  l ↦t∗[tk_local]{t} v_t -∗
  (l ↦t∗[tk_local]{t} v_t -∗ t $$ tk_local -∗ target_red #v_t Ψ)%E -∗
  target_red (Copy (Place l (Tagged t) T)) Ψ.
Proof.
  iIntros (Hlen) "Htag Ht Hsim".
  iApply target_red_lift_base_step. iIntros (P_t σ_t P_s σ_s ?) "(HP_t & HP_s & Hbor)".
  iModIntro.
  iPoseProof (bor_interp_readN_target_local with "Hbor Ht Htag") as "(%Hd & %Hstack)".
  rewrite Hlen in Hd Hstack.
  have READ_t : read_mem l (tsize T) σ_t.(shp) = Some v_t.
  { apply read_mem_values'; done. }
  iPoseProof (bor_interp_get_state_wf with "Hbor") as "[%Hwf_t %]".
  have Eq_stk : memory_read σ_t.(sst) σ_t.(scs) l (Tagged t) (tsize T) = Some σ_t.(sst).
  { apply memory_read_access1. intros i Hi.
    specialize (Hstack i Hi). eexists; split; first done. eapply bor_state_own_access1_read; done. }
  iSplitR.
  { iPureIntro. do 3 eexists; eapply copy_base_step'; [done | done | eauto ]. }
  iIntros (e_t' efs_t σ_t') "%Hhead".
  specialize (head_copy_inv _ _ _ _ _ _ _ _ Hhead) as [-> [(v_t' & α' & READ & ACC & -> & ->) | (_ & Hfail & _)]]; last congruence.
  rewrite READ in READ_t. simplify_eq.
  iModIntro. iSplitR; first done.
  iFrame "HP_t HP_s".
  iSplitL "Hbor"; last iApply ("Hsim" with "Ht Htag").
  destruct σ_t; done.
Qed.

Lemma source_copy_local v_s T l t Ψ π :
  length v_s = tsize T →
  t $$ tk_local -∗
  l ↦s∗[tk_local]{t} v_s -∗
  (l ↦s∗[tk_local]{t} v_s -∗ t $$ tk_local -∗ source_red #v_s π Ψ)%E -∗
  source_red (Copy (Place l (Tagged t) T)) π Ψ.
Proof.
  iIntros (Hlen) "Htag Hs Hsim".
  iApply source_red_lift_base_step. iIntros (P_t σ_t P_s σ_s ??) "[(HP_t & HP_s & Hbor) _]".
  iModIntro.
  iPoseProof (bor_interp_get_state_wf with "Hbor") as "[% %Hwf_s]".
  iPoseProof (bor_interp_readN_source_local with "Hbor Hs Htag") as "(%Hd & %Hstack)".
  rewrite Hlen in Hd Hstack.
  have READ_s : read_mem l (tsize T) σ_s.(shp) = Some v_s.
  { apply read_mem_values'; done. }
  have Eq_stk : memory_read σ_s.(sst) σ_s.(scs) l (Tagged t) (tsize T) = Some σ_s.(sst).
  { apply memory_read_access1. intros i Hi.
    specialize (Hstack i Hi). eexists; split; first done. eapply bor_state_own_access1_read; done. }
  assert (base_reducible P_s (Copy (Place l (Tagged t) T)) σ_s) as (e_s' & σ_s' & efs & Hhead).
  { do 3 eexists; eapply copy_base_step'; [done | done | eauto ]. }
  iExists e_s', σ_s'.
  specialize (head_copy_inv _ _ _ _ _ _ _ _ Hhead) as [-> [(v_t' & α' & READ & ACC & -> & ->) | (_ & Hfail & _)]]; last congruence.
  rewrite READ in READ_s. simplify_eq.
  iFrame "HP_t HP_s". iSplitR; first done.
  iSplitL "Hbor"; last by iApply ("Hsim" with "Hs Htag"). iModIntro.
  by destruct σ_s.
Qed.

(* should work for any tag_kind [tk] *)
Lemma target_copy_protected v_t T l t tk Ψ c M  :
  length v_t = tsize T →
  (∀ i: nat, (i < tsize T)%nat → call_set_in M t (l +ₗ i)) →
  c @@ M -∗
  t $$ tk -∗
  l ↦t∗[tk]{t} v_t -∗
  (l ↦t∗[tk]{t} v_t -∗ c @@ M -∗ t $$ tk -∗ target_red #v_t Ψ)%E -∗
  target_red (Copy (Place l (Tagged t) T)) Ψ.
Proof.
  iIntros (Hlen Hprotected) "Hcall Htag Ht Hsim".
  iApply target_red_lift_base_step. iIntros (P_t σ_t P_s σ_s ?) "(HP_t & HP_s & Hbor)".
  iModIntro.
  iPoseProof (bor_interp_readN_target_protected with "Hbor Ht Htag Hcall") as "(%Hd & %Hown)".
  { by rewrite Hlen. }
  rewrite Hlen in Hd Hown.
  have READ_t : read_mem l (tsize T) σ_t.(shp) = Some v_t.
  { apply read_mem_values'; done. }
  iPoseProof (bor_interp_get_state_wf with "Hbor") as "[%Hwf_t %]".
  have Eq_stk : memory_read σ_t.(sst) σ_t.(scs) l (Tagged t) (tsize T) = Some σ_t.(sst).
  {
    apply memory_read_access1. intros i Hi.
    specialize (Hown i Hi). destruct (bor_state_own_some_stack _ _ _ _ Hown) as (stk & Hs_stk).
    exists stk. split; first done. eapply bor_state_own_access1_read; done.
  }
  iSplitR.
  { iPureIntro. do 3 eexists; eapply copy_base_step'; [done | eapply read_mem_values'; eauto | eauto]. }
  iIntros (e_t' efs_t σ_t') "%Hhead".
  specialize (head_copy_inv _ _ _ _ _ _ _ _ Hhead) as [-> [(v_t' & α' & READ & ACC & -> & ->) | (_ & Hfail & _)]]; last congruence.
  rewrite READ in READ_t. simplify_eq.
  iModIntro. iSplitR; first done.
  iFrame "HP_t HP_s".
  iSplitL "Hbor"; last iApply ("Hsim" with "Ht Hcall Htag").
  destruct σ_t; done.
Qed.

(* Since copies without granting tags are not UB in the source but yield poison,
  we also need protection here to gain any knowledge about the value. *)
Lemma source_copy_protected v_s T l t tk Ψ c M π :
  length v_s = tsize T →
  (∀ i: nat, (i < tsize T)%nat → call_set_in M t (l +ₗ i)) →
  c @@ M -∗
  t $$ tk -∗
  l ↦s∗[tk]{t} v_s -∗
  (l ↦s∗[tk]{t} v_s -∗ c @@ M -∗ t $$ tk -∗ source_red #v_s π Ψ)%E -∗
  source_red (Copy (Place l (Tagged t) T)) π Ψ.
Proof.
  iIntros (Hlen Hprotected) "Hcall Htag Hs Hsim".
  iApply source_red_lift_base_step. iIntros (P_t σ_t P_s σ_s ??) "[(HP_t & HP_s & Hbor) %Hsafe]".
  iModIntro.
  iPoseProof (bor_interp_readN_source_protected with "Hbor Hs Htag Hcall") as "(%Hd & %Hown)".
  { by rewrite Hlen. }
  rewrite Hlen in Hd Hown.
  have READ_t : read_mem l (tsize T) σ_s.(shp) = Some v_s.
  { apply read_mem_values'; done. }
  iPoseProof (bor_interp_get_state_wf with "Hbor") as "[% %Hwf_s]".
  have Eq_stk : memory_read σ_s.(sst) σ_s.(scs) l (Tagged t) (tsize T) = Some σ_s.(sst).
  {
    apply memory_read_access1. intros i Hi.
    specialize (Hown i Hi). destruct (bor_state_own_some_stack _ _ _ _ Hown) as (stk & Hs_stk).
    exists stk. split; first done. eapply bor_state_own_access1_read; done.
  }
  iExists (#v_s)%E, _.
  iSplitR.
  { iPureIntro. eapply copy_base_step'; [done | eapply read_mem_values'; eauto | eauto]. }
  iModIntro. iFrame "HP_t HP_s".
  iSplitL "Hbor"; last iApply ("Hsim" with "Hs Hcall Htag").
  destruct σ_s; done.
Qed.

(* We can also read from unprotected source locations.
  But then we may get poison if the value isn't there anymore. *)
Lemma source_copy_any v_s T l t tk Ψ π :
  length v_s = tsize T →
  t $$ tk -∗
  l ↦s∗[tk]{t} v_s -∗
  (∀ v_s', ⌜v_s' = v_s ∨ v_s' = replicate (length v_s) ScPoison⌝ -∗ l ↦s∗[tk]{t} v_s -∗ t $$ tk -∗ source_red #v_s' π Ψ)%E -∗
  source_red (Copy (Place l (Tagged t) T)) π Ψ.
Proof.
  iIntros (Hlen) "Htag Hs Hsim".
  iApply source_red_lift_base_step. iIntros (P_t σ_t P_s σ_s ??) "[(HP_t & HP_s & Hbor) %Hsafe]".
  iModIntro.
  iPoseProof (bor_interp_get_state_wf with "Hbor") as "[% %Hwf_s]".
  destruct Hsafe as [Hpool Hsafe].
  specialize (pool_safe_implies Hsafe Hpool) as [(v_s' & Hread_s & (α' & Hstack_s)) | Hfail]; first last.
  { (* unsuccessful read, so we are in the poison case *)
    iExists _, _. iSplitR. { iPureIntro. eapply failed_copy_base_step'; done. }
    iModIntro. iFrame. iApply ("Hsim" with "[] Hs Htag").
    iPureIntro. right. rewrite Hlen. done.
  }
  (* successful read -- so this has to match what the ghost state says, since the
    preconditions are fulfilled. *)
  (* TODO: duplicate with the source_copy_resolve_deferred thing *)
  iPoseProof (bor_interp_readN_source with "Hbor Hs Htag") as "%Hcontrolled".
  assert (∀ i, (i < length v_s)%nat → shp σ_s !! (l +ₗ i) = v_s !! i ∧  bor_state_own (l +ₗ i) t tk σ_s) as Hcontrol'.
  {
    intros i Hi.
    destruct (Hcontrolled i Hi) as [Hown Hshp].
    { specialize (for_each_lookup_case_2 _ _ _ _ _ Hstack_s) as [Hs _].
      specialize (Hs i ltac:(lia)) as (stk0 & stk' & Hstk0 & Hstk' & Hacc1').
      destruct access1 as [[] | ] eqn:Hacc1; last done.
      specialize (access1_in_stack _ _ _ _ _ _ Hacc1) as (it & Hit & Htg & Hperm).
      destruct it as [perm tg opro]. simpl in *. simplify_eq.
      destruct tk; last done.
      all: exists stk0, perm, opro; done.
    }
    split; last done. rewrite Hshp list_lookup_lookup_total; first done.
    apply lookup_lt_is_Some_2. lia.
  }
  have READ_s : read_mem l (tsize T) σ_s.(shp) = Some v_s.
  { apply read_mem_values'; first lia. rewrite -Hlen. apply Hcontrol'. }
  have Eq_stk : memory_read σ_s.(sst) σ_s.(scs) l (Tagged t) (tsize T) = Some σ_s.(sst).
  { apply memory_read_access1. intros i Hi.
    specialize (Hcontrol' i ltac:(lia)) as (_ & Hown).
    destruct (bor_state_own_some_stack _ _ _ _ Hown) as (stk & Heq).
    eexists; split; first done.
    eapply bor_state_own_access1_read; done.
  }
  iExists _, _. iSplitR. { iPureIntro. eapply copy_base_step'; done. }
  iModIntro.
  iFrame "HP_t HP_s".
  iSplitL "Hbor"; first by destruct σ_s.
  iApply ("Hsim" with "[] Hs Htag").
  iPureIntro. by left.
Qed.

Lemma target_copy_deferred v_t T l t tk Ψ :
  length v_t = tsize T →
  t $$ tk -∗
  l ↦t∗[tk]{t} v_t -∗
  (∀ v_t', deferred_read v_t v_t' l t -∗ l ↦t∗[tk]{t} v_t -∗ t $$ tk -∗ target_red #v_t' Ψ)%E -∗
  target_red (Copy (Place l (Tagged t) T)) Ψ.
Proof.
  iIntros (Hlen) "Htag Ht Hsim".
  iApply target_red_lift_base_step. iIntros (P_t σ_t P_s σ_s ?) "(HP_t & HP_s & Hbor)".
  iModIntro.
  iPoseProof (bor_interp_readN_target with "Hbor Ht Htag") as "%Hcontrolled".

  (* either:
    - one of the preconditions is not fulfilled anymore.
      In that case, we know that the item is not in the stack.
      This means that memory_read = None, and the CopyFail rule works.
      In that case, we allocate with tag_tainted_interp_insert at that i.
    - all of the preconditions are fulfilled. In that case, we proceed similarly
      to the protected case.
  *)

  iPoseProof (bor_interp_get_state_wf with "Hbor") as "[%Hwf_t %]".
  assert ((∀ i, (i < length v_t)%nat → shp σ_t !! (l +ₗ i) = v_t !! i ∧  bor_state_own (l +ₗ i) t tk σ_t) ∨
    (∃ i, (i < length v_t)%nat ∧ ∀ st pm opro, σ_t.(sst) !! (l +ₗ i) = Some st →
        mkItem pm (Tagged t) opro ∉ st ∨ pm = Disabled)) as [Hsuccess | Hnosuccess].
  {
    revert Hcontrolled. clear Hlen.
    set (n' := length v_t). assert (n' = length v_t) as Heq by done. revert Heq.
    generalize n' as n => n. clear n'.
    induction n as [ | n IH] in l, v_t |-* => Hlen Hcontrolled. { left. intros i Hi. lia. }
    destruct v_t as [ | sc v_t]; first done.
    specialize (IH v_t (l +ₗ 1)) as [IH | IH].
    - naive_solver.
    - intros i Hi. specialize (Hcontrolled (S i) ltac:(lia)).
      rewrite shift_loc_assoc. replace (1 + i)%Z with (Z.of_nat (S i))%Z by lia. done.
    - setoid_rewrite shift_loc_assoc in IH.
      destruct (σ_t.(sst) !! (l +ₗ O)) as [stk | ] eqn:Hstk; first last.
      { right; exists O. split; first lia. intros ????; congruence. }
      assert (Decision (∃ pm opro, mkItem pm (Tagged t) opro ∈ stk)) as [Hin | Hnotin].
      { destruct (list_exist_dec (λ it, tg it = Tagged t) stk) as [Hit | Hnit]; first apply _.
        - left. destruct Hit as (it & Htg & Hit). exists (perm it), (protector it).
          destruct it; naive_solver.
        - right. contradict Hnit. destruct Hnit as (pm & opro & Hit).
          exists (mkItem pm (Tagged t) opro). split; done.
      }
      2: { right. exists O. split; first lia. intros st pm opro Hst. simplify_eq.
        left. contradict Hnotin. eauto. }
      destruct Hin as (pm & opro & Hit).
      destruct (decide (pm = Disabled)) as [-> | Hen].
      { right. exists O. split; first lia. intros st pm' opro' ?; simplify_eq.
        destruct (decide (pm' = Disabled)) as [Heq | Hneq]; first by eauto.
        left. intros Hit'.
        assert (stack_item_tagged_NoDup stk) as Hnodup.
        { by eapply Hwf_t. }
        specialize (stack_item_tagged_NoDup_eq stk _ _ t Hnodup Hit Hit' eq_refl eq_refl).
        intros [= <-]. done.
      }
      left.
      destruct (Hcontrolled O ltac:(lia)) as [Hown Hshp].
      { destruct tk; [ | | done]; exists stk, pm, opro; eauto. }
      intros i Hi.
      destruct (decide (i = O)) as [-> | Hneq]; first done.
      simpl. specialize (IH (pred i) ltac:(lia)).
      replace ((1 + Z.of_nat (pred i))) with (Z.of_nat i) in IH by lia.
      destruct IH as [IH1 IH2]; split; last done.
      rewrite IH1. destruct i; done.
    - destruct IH as (i & Hi & IH).
      right; exists (S i). split; first lia.
      replace (Z.of_nat (S i))%Z with (1 + i)%Z by lia. rewrite -shift_loc_assoc.
      done.
  }
  - (** success! just proceed with the read *)
    rewrite Hlen in Hsuccess.
    have READ_t : read_mem l (tsize T) σ_t.(shp) = Some v_t.
    { apply read_mem_values'; first done. by apply Hsuccess. }
    have Eq_stk : memory_read σ_t.(sst) σ_t.(scs) l (Tagged t) (tsize T) = Some σ_t.(sst).
    {
      apply memory_read_access1. intros i Hi.
      specialize (Hsuccess i Hi) as (_ & Hown). destruct (bor_state_own_some_stack _ _ _ _ Hown) as (stk & Hs_stk).
      exists stk. split; first done. eapply bor_state_own_access1_read; done.
    }
    iSplitR.
    { iPureIntro. do 3 eexists; eapply copy_base_step'; [done | eapply read_mem_values'; [ eauto | apply Hsuccess] | done ]. }
    iIntros (e_t' efs_t σ_t') "%Hhead".
    specialize (head_copy_inv _ _ _ _ _ _ _ _ Hhead) as [-> [(v_t' & α' & READ & ACC & -> & ->) | (_ & Hfail & _)]]; last congruence.
    rewrite READ in READ_t. simplify_eq.
    iModIntro. iSplitR; first done.
    iFrame "HP_t HP_s".
    iSplitL "Hbor"; first by destruct σ_t.
    iApply ("Hsim" with "[] Ht Htag").
    iRight. done.
  - (** oh no, the tag isn't there anymore. allocate the tainted ghost state *)
    destruct Hnosuccess as (i & Hi & Hst).
    assert (memory_read σ_t.(sst) σ_t.(scs) l (Tagged t) (tsize T) = None) as Hnone.
    { destruct memory_read as [ α' | ] eqn:Hread; last done.
      specialize (for_each_lookup_case_2 _ _ _ _ _ Hread) as [Hs _].
      specialize (Hs i ltac:(lia)) as (stk & stk' & Hstk & Hstk' & Hacc1').
      destruct access1 as [[] | ] eqn:Hacc1; last done.
      specialize (access1_in_stack _ _ _ _ _ _ Hacc1) as (it & Hit & Htg & Hperm).
      destruct it as [perm tg opro].
      specialize (Hst _ perm opro Hstk) as [Hnotin | ->]; last done.
      exfalso. apply Hnotin. naive_solver.
    }
    iDestruct "Hbor" as "(%M_call & %M_tag & %M_t & %M_s & (Hcall_auth & Htag_auth & Htag_t_auth & Htag_s_auth) & Htainted & Hpub_cid & #Hsrel & %Hcall_interp & %Htag_interp & %Hwf_s & _)".
    iSplitR.
    { iPureIntro. do 3 eexists. eapply failed_copy_base_step'; done. }
    iIntros (e_t' efs_t σ_t') "%Hhead_t".
    specialize (head_copy_inv _ _ _ _ _ _ _ _ Hhead_t) as [-> [(? & ? & _ & ? & _) | (-> & ? & ->)]]; first congruence.

    iPoseProof (tkmap_lookup with "Htag_auth Htag") as "%Hl". apply Htag_interp in Hl as (? & ? & _).
    iPoseProof (state_rel_stacks_eq with "Hsrel") as "%Heq".
    iMod (tag_tainted_interp_insert σ_s t (l +ₗ i) with "Htainted") as "[Htainted Htfor]"; first done.
    { rewrite Heq. intros stk it Hstk Hit.
      specialize (Hst stk (perm it) (protector it) Hstk) as [Hnotin  | ->]; last by right.
      left. intros Heq'. simplify_eq. destruct it; naive_solver.
    }
    iModIntro. iSplitR; first done.
    iSplitR "Hsim Htfor Htag Ht"; first last.
    { iApply ("Hsim" with "[Htfor] Ht Htag").
      iLeft. iExists i. iFrame "Htfor".
      iPureIntro. rewrite length_replicate. split; lia.
    }
    iFrame "HP_t HP_s".
    iExists M_call, M_tag, M_t, M_s. iFrame. iFrame "Hsrel". repeat (iSplit; done).
Qed.


Lemma source_copy_resolve_deferred v_s v_t v_t' T l t Ψ tk π :
  length v_s = tsize T →
  t $$ tk -∗
  l ↦s∗[tk]{t} v_s -∗
  deferred_read v_t v_t' l t -∗
  value_rel v_t v_s -∗
  (∀ v_s', value_rel v_t' v_s' -∗ l ↦s∗[tk]{t} v_s -∗ t $$ tk -∗ source_red #v_s' π Ψ)%E -∗
  source_red (Copy (Place l (Tagged t) T)) π Ψ.
Proof.
  iIntros (Hlen) "Htag Hs Hdef #Hv Hsim".
  iApply source_red_lift_base_step. iIntros (P_t σ_t P_s σ_s ??) "[(HP_t & HP_s & Hbor) %Hsafe]".
  iModIntro.
  iPoseProof (bor_interp_get_state_wf with "Hbor") as "[% %Hwf_s]".
  destruct Hsafe as [Hpool Hsafe].
  specialize (pool_safe_implies Hsafe Hpool) as [(v_s' & Hread_s & (α' & Hstack_s)) | Hfail]; first last.
  { (* unsuccessful read, but poison is refined by anything *)
    iExists _, _. iSplitR. { iPureIntro. eapply failed_copy_base_step'; done. }
    iModIntro. iFrame. iApply ("Hsim" with "[Hdef] Hs Htag").
    iApply big_sepL2_forall. rewrite length_replicate. iSplit.
    - iPoseProof (value_rel_length with "Hv") as "%".
      iDestruct "Hdef" as "[(%i & % & _) | ->]"; iPureIntro; lia.
    - iIntros (i sc_s ?). rewrite lookup_replicate. iIntros "_ (-> & _)".
      destruct sc_s; done.
  }
  (* successful read -- so this has to match what the ghost state says, since the
    preconditions are fulfilled. Moreover, this means we must be in the second
    case of [deferred_read]. *)
  iPoseProof (bor_interp_readN_source with "Hbor Hs Htag") as "%Hcontrolled".
  assert (∀ i, (i < length v_s)%nat → shp σ_s !! (l +ₗ i) = v_s !! i ∧  bor_state_own (l +ₗ i) t tk σ_s) as Hcontrol'.
  {
    intros i Hi.
    destruct (Hcontrolled i Hi) as [Hown Hshp].
    { specialize (for_each_lookup_case_2 _ _ _ _ _ Hstack_s) as [Hs _].
      specialize (Hs i ltac:(lia)) as (stk0 & stk' & Hstk0 & Hstk' & Hacc1').
      destruct access1 as [[] | ] eqn:Hacc1; last done.
      specialize (access1_in_stack _ _ _ _ _ _ Hacc1) as (it & Hit & Htg & Hperm).
      destruct it as [perm tg opro]. simpl in *. simplify_eq.
      destruct tk; last done.
      all: exists stk0, perm, opro; done.
    }
    split; last done. rewrite Hshp list_lookup_lookup_total; first done.
    apply lookup_lt_is_Some_2. lia.
  }
  have READ_s : read_mem l (tsize T) σ_s.(shp) = Some v_s.
  { apply read_mem_values'; first lia. rewrite -Hlen. apply Hcontrol'. }
  have Eq_stk : memory_read σ_s.(sst) σ_s.(scs) l (Tagged t) (tsize T) = Some σ_s.(sst).
  { apply memory_read_access1. intros i Hi.
    specialize (Hcontrol' i ltac:(lia)) as (_ & Hown).
    destruct (bor_state_own_some_stack _ _ _ _ Hown) as (stk & Heq).
    eexists; split; first done.
    eapply bor_state_own_access1_read; done.
  }
  iExists _, _. iSplitR. { iPureIntro. eapply copy_base_step'; done. }
  iModIntro.
  iFrame.
  iDestruct "Hdef" as "[(%i & %Hi & Htainted) | ->]"; first last.
  { iSplitL "Hbor"; first by destruct σ_s. iApply ("Hsim" with "Hv Hs Htag"). }
  iDestruct "Hbor" as "(%M_call & %M_tag & %M_t & %M_s & (Hcall_auth & Htag_auth & Htag_t_auth & Htag_s_auth) & Htaint_interp & Hpub_cid & #Hsrel & %Hcall_interp & %Htag_interp & _ & %Hwf_t)".
  iPoseProof (tag_tainted_interp_lookup with "Htainted Htaint_interp") as "[%Ht %Hstk]".
  iPoseProof (value_rel_length with "Hv") as "%".
  exfalso.
  specialize (for_each_lookup_case_2 _ _ _ _ _ Hstack_s) as [Hs _].
  specialize (Hs i ltac:(lia)) as (stk0 & stk' & Hstk0 & Hstk' & Hacc1').
  destruct access1 as [[] | ] eqn:Hacc1; last done.
  specialize (access1_in_stack _ _ _ _ _ _ Hacc1) as (it & Hit & Htg & Hperm).
  destruct it as [perm tg opro]. simpl in *.
  specialize (Hstk stk0 _ Hstk0 Hit) as [Hneq | Hdis]; last done.
  simpl in Hneq. congruence.
Qed.

(** ** Alloc *)
Lemma sim_alloc_local T Φ π :
  (∀ t l, t $$ tk_local -∗
    l ↦t∗[tk_local]{t} replicate (tsize T) ScPoison -∗
    l ↦s∗[tk_local]{t} replicate (tsize T) ScPoison -∗
    Place l (Tagged t) T ⪯{π} Place l (Tagged t) T [{ Φ }]) -∗
  Alloc T ⪯{π} Alloc T [{ Φ }].
Proof.
  iIntros "Hsim".
  iApply sim_lift_base_step_both. iIntros (P_t P_s σ_t σ_s ??) "[(HP_t & HP_s & Hbor) %Hsafe]".
  iPoseProof (bor_interp_get_pure with "Hbor") as "%Hp".
  iPoseProof (bor_interp_get_state_wf with "Hbor") as "%Hwf".
  iModIntro. iSplitR.
  { iPureIntro. do 3 eexists. econstructor 2; econstructor. }
  iIntros (e_t' efs_t σ_t') "%Hhead_t".
  specialize (head_alloc_inv _ _ _ _ _ _ Hhead_t) as (-> & -> & ->).
  set (l_s := (fresh_block σ_s.(shp), 0)).
  set (σ_s' := (mkState (init_mem l_s (tsize T) σ_s.(shp)) (init_stacks σ_s.(sst) l_s (tsize T) (Tagged σ_t.(snp))) σ_s.(scs) (S σ_s.(snp)) σ_s.(snc))).
  assert (Hhead_s : language.base_step P_s (Alloc T) σ_s (Place l_s (Tagged σ_t.(snp)) T) σ_s' []).
  { subst σ_s'. destruct Hp as (_ & <- & _). econstructor 2; econstructor. }
  iMod (bor_interp_alloc_local _ _ T with "Hbor") as "(Hbor & Htag & Htarget & Hsource)".
  { eapply base_step_wf; [ apply Hhead_t | apply Hwf]. }
  { eapply base_step_wf; last apply (proj2 Hwf). apply Hhead_s. }
  iModIntro.
  iExists (Place l_s (Tagged (σ_t.(snp))) T), [], σ_s'.
  iFrame. iSplitR; first done.
  iSplitL; last by iApply big_sepL2_nil.
  subst l_s. rewrite (fresh_block_det σ_s σ_t); last apply Hp.
  iApply ("Hsim" with "Htag Htarget Hsource").
Qed.

(** ** Free *)
(* local ownership makes strong assertions: we also have to deallocate the corresponding ghost state. *)
Lemma bor_interp_free_local t v_t v_s l σ_t σ_s α' n :
  memory_deallocated (sst σ_t) (scs σ_t) l (Tagged t) n = Some α' →
  memory_deallocated (sst σ_s) (scs σ_s) l (Tagged t) n = Some α' →
  length v_t = n →
  length v_s = n →
  let σ_t' := mkState (free_mem l n σ_t.(shp)) α' σ_t.(scs) σ_t.(snp) σ_t.(snc) in
  let σ_s' := mkState (free_mem l n σ_s.(shp)) α' σ_s.(scs) σ_s.(snp) σ_s.(snc) in
  state_wf σ_t' →
  state_wf σ_s' →
  t $$ tk_local -∗
  l ↦t∗[tk_local]{t} v_t -∗
  l ↦s∗[tk_local]{t} v_s -∗
  bor_interp sc_rel σ_t σ_s ==∗
  t $$ tk_local ∗
  bor_interp sc_rel σ_t' σ_s'.
Proof.
  intros Hstack_t Hstack_s Hlen_t Hlen_s σ_t' σ_s' Hwf_t' Hwf_s'.
  iIntros "Htag Ht Hs Hbor".
  iDestruct "Hbor" as "(%M_call & %M_tag & %M_t & %M_s & (Hcall_auth & Htag_auth & Htag_t_auth & Htag_s_auth) & Htaint_interp & Hpub_cid & #Hsrel & %Hcall_interp & %Htag_interp & %Hwf_s & %Hwf_t)".
  iMod (ghost_map_array_tag_delete with "Htag_t_auth Ht") as "Htag_t_auth".
  iMod (ghost_map_array_tag_delete with "Htag_s_auth Hs") as "Htag_s_auth".
  iModIntro. iFrame "Htag".
  iExists M_call, M_tag, (M_t ∖ array_tag_map l t v_t), (M_s ∖ array_tag_map l t v_s).
  iFrame.
  iSplitL "Htaint_interp".
  { (* tainted *)
    iApply (tag_tainted_interp_preserve σ_s with "Htaint_interp"). { simpl. lia. }
    intros l' stk' Hstk' it Hit. right. right.
    specialize (for_each_dealloc_lookup_Some _ _ _ _ _ Hstack_s _ _ Hstk') as (_ & Hstk). eauto.
  }
  iSplitL.
  { (* state rel *)
    (* TODO: partially duplicated from the refl lemma. prove more general lemma? *)
    iDestruct "Hsrel" as "(%Hdom_eq & %Hsst_eq & %Hsnp_eq & %Hsnc_eq & %Hscs_eq & Hsrel)".
    iSplitR. { iPureIntro. simpl. apply free_mem_dom. done. }
    simpl. do 4 (iSplitR; first done).
    iIntros (l' (sc & Hsome)).
    destruct (free_mem_lookup_case l' l n σ_t.(shp)) as [[Hi Heq] | (i & _ & -> & ?)]; last congruence.
    rewrite Heq in Hsome. iDestruct ("Hsrel" $! l' with "[]") as "[Hpubl | (%t' & %Hprivl)]"; first by eauto.
    + iLeft. iIntros (sc_t Hsc_t). simpl in *.
      rewrite Heq in Hsc_t. rewrite Hsome in Hsc_t. injection Hsc_t as <-.
      iDestruct ("Hpubl" $! sc Hsome) as (sc_s) "[%Hsc_s Hscr]".
      iExists sc_s. iSplitR; last done.
      iPureIntro.
      destruct (free_mem_lookup_case l' l n σ_s.(shp)) as [[_ Heq'] | (i' & Hi' & -> & _)].
      2: { specialize (Hi i' Hi'). congruence. }
      rewrite Heq' Hsc_s. done.
    + iRight. iPureIntro. exists t'.
      destruct Hprivl as (tk & Htk & (s & Hs) & Hpriv). exists tk. split_and!; [done | | done].
      exists s. apply lookup_difference_Some. split; first done.
      destruct (decide (t = t')) as [<- | Hneq]; last by apply array_tag_map_lookup_None.
      apply array_tag_map_lookup_None'. intros i Hi'. rewrite Hlen_t in Hi'.
      specialize (Hi i Hi'); done.
  }
  iSplitL.
  { (* call interp *)
    (* TODO: duplicated with the refl lemma *)
    iPureIntro. iIntros (c M' Hc).
    destruct (Hcall_interp c M' Hc) as (? & HM'). split; first done.
    intros t' L Ht'. specialize (HM' t' L Ht') as (? & HL). split; first done.
    intros l' (stk & pm & Hstk & Hit & Hpm)%HL. exists stk, pm. split_and!; [ | done..].
    destruct (for_each_true_lookup_case_2 _ _ _ _ _ Hstack_t) as [EQ1 EQ2].
    (* from Hstack_s, l cannot be in the affected range because it is protected by c,
      so α' !! l = σt.(sst) !! l. *)
    destruct (block_case l l' n) as [Hneq|(i & Hi & ->)].
    + rewrite EQ2//.
    + exfalso. clear EQ2.
      specialize (EQ1 _ Hi) as (stk1 & stk' & Eqstk1 & Eqstk' & Hdealloc).
      rewrite Eqstk1 in Hstk. simplify_eq.
      move : Hdealloc. destruct (dealloc1 stk (Tagged t) σ_t.(scs)) eqn:Eqd; last done.
      intros _.
      destruct (dealloc1_Some stk (Tagged t) σ_t.(scs)) as (it & Eqit & ? & FA & GR).
      { by eexists. }
      rewrite ->Forall_forall in FA. apply (FA _ Hit).
      rewrite /is_active_protector /= /is_active bool_decide_true //.
  }
  iSplitL.
  { (* tag interp *)
    destruct Htag_interp as (Htag_interp & Hdom_t & Hdom_s).
    iPureIntro. split_and!.
    { intros t' tk Ht. simpl. specialize (Htag_interp _ _ Ht) as (? & ? & Hcontrol_t & Hcontrol_s & Hag).
      split_and!; [done | done | | | ].
      + intros l' sc_t.
        rewrite lookup_difference_Some. intros [Hsc_t%Hcontrol_t Hnotin%array_tag_map_lookup_None2].
        eapply loc_controlled_dealloc_update; [ apply Hstack_t | done | | done].
        intros [[= <-] (i & -> & Hi)].
        destruct Hnotin as [? | Hi']; first congruence.
        rewrite Hlen_t in Hi'. apply Hi' in Hi. congruence.
      + intros l' sc_s.
        rewrite lookup_difference_Some. intros [Hsc_t%Hcontrol_s Hnotin%array_tag_map_lookup_None2].
        eapply loc_controlled_dealloc_update; [ apply Hstack_s | done | | done].
        intros [[= <-] (i & -> & Hi)].
        destruct Hnotin as [? | Hi']; first congruence.
        rewrite Hlen_s in Hi'. apply Hi' in Hi. congruence.
      + apply dom_agree_on_tag_difference; first done.
        destruct (decide (t = t')) as [<- | Hneq].
        * apply dom_agree_on_tag_array_tag_map. lia.
        * apply dom_agree_on_tag_not_elem; apply array_tag_map_lookup_None; done.
    }
    all: intros t' l'; rewrite lookup_difference_is_Some; intros [? _]; eauto.
  }
  eauto.
Qed.

Lemma sim_free_local l t T v_t v_s Φ π :
  length v_t = tsize T →
  length v_s = tsize T →
  t $$ tk_local -∗
  l ↦t∗[tk_local]{t} v_t -∗
  l ↦s∗[tk_local]{t} v_s -∗
  (t $$ tk_local -∗ #[☠] ⪯{π} #[☠] [{ Φ }]) -∗
  Free (Place l (Tagged t) T) ⪯{π} Free (Place l (Tagged t) T) [{ Φ }].
Proof.
  iIntros (Hlen_t Hlen_s) "Htag Ht Hs Hsim".
  iApply sim_lift_base_step_both. iIntros (P_t P_s σ_t σ_s ??) "[(HP_t & HP_s & Hbor) %Hsafe]".
  destruct Hsafe as [Hthread Hsafe].
  specialize (pool_safe_implies Hsafe Hthread) as (Hmem_s & (α' & Hstack_s)).

  iPoseProof (bor_interp_get_pure with "Hbor") as "%Hp".
  destruct Hp as (Hsst_eq & Hsnp_eq & Hsnc_eq & Hscs_eq & Hwf_s & Hwf_t & Hdom_eq).
  iModIntro.
  iSplitR.
  { iPureIntro. eexists _, _, _. eapply dealloc_base_step'; first apply Hwf_t.
    - intros i. rewrite -Hmem_s. rewrite -!elem_of_dom Hdom_eq. done.
    - erewrite <-Hstack_s. rewrite Hsst_eq Hscs_eq. done.
  }
  iIntros (e_t' efs_t σ_t' Hhead_t).
  specialize (head_free_inv _ _ _ _ _ _ _ _ Hhead_t) as (α'_t & Hstack_t & Hmem_t & -> & -> & ->).
  assert (α'_t = α') as ->.
  { move : Hstack_t Hstack_s. rewrite Hsst_eq Hscs_eq => -> [= ->] //. }
  iMod (bor_interp_free_local with "Htag Ht Hs Hbor") as "[Htag Hbor]"; [done | done | done | done | ..].
  { eapply base_step_wf; done. }
  { eapply base_step_wf; [eapply (dealloc_base_step' P_s); done | done ]. }
  iModIntro. iExists _, _, _.
  iSplitR. { iPureIntro. eapply dealloc_base_step'; done. }
  iFrame. iSplitL; last done. by iApply "Hsim".
Qed.


(** operational lemmas for calls *)
Lemma target_red_call f arg body v Ψ :
  f @t (arg, body) -∗
  target_red (subst arg #v body) Ψ -∗
  target_red (Call #[ScFnPtr f] #v) Ψ.
Proof.
  iIntros "Hf Hred". iApply target_red_lift_base_step.
  iIntros (?????) "(HP_t & HP_s & ?) !>".
  iDestruct (has_prog_has_fun_agree with "HP_t Hf") as %?.
  iSplitR. { iPureIntro. eexists _, _, _. econstructor. econstructor; first done. eauto. }
  iIntros (e_t' efs σ_t') "%"; inv_base_step.
  iModIntro. by iFrame.
Qed.

Lemma source_red_call π f arg body v Ψ :
  f @s (arg, body) -∗
  source_red (subst arg #v body) π Ψ -∗
  source_red (Call #[ScFnPtr f] #v) π Ψ.
Proof.
  iIntros "Hf Hred". iApply source_red_lift_base_step.
  iIntros (??????) "[(HP_t & HP_s & ?) [% %]] !>".
  iDestruct (has_prog_has_fun_agree with "HP_s Hf") as %?.
  iExists _, _. iSplit. { iPureIntro. econstructor. econstructor; first done. eauto. }
  iModIntro. iFrame.
Qed.

End lifting.
