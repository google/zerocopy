From iris.proofmode Require Export proofmode.
From iris.base_logic.lib Require Import ghost_map.
From simuliris.base_logic Require Export gen_sim_prog.
From simuliris.simulation Require Export slsls.
From simuliris.simulation Require Import lifting.
From simuliris.tree_borrows Require Import tkmap_view.
From simuliris.tree_borrows Require Export defs class_instances.
From simuliris.tree_borrows Require Import steps_progress steps_inv.
From simuliris.tree_borrows Require Import logical_state inv_accessors.
From simuliris.tree_borrows Require Import wishlist.
From simuliris.tree_borrows.trees_equal Require Export trees_equal_base random_lemmas trees_equal_transitivity.

(** * Simulation lemmas using the ghost state for proving optimizations *)

Section lifting.
Context `{!sborGS Σ}.
Implicit Types P Q : iProp Σ.
Implicit Types Φ : expr → expr → iProp Σ.
Implicit Types σ σ_s σ_t : state.
Implicit Types r r_s r_t : result.
Implicit Types l : loc.
Implicit Types f : fname.

Definition filter_unq_weak lp := match lp with 
    Deallocable => Deallocable
  | EnsuringAccess Strongly => EnsuringAccess Strongly
  | EnsuringAccess WeaklyNoChildren => Deallocable end.

(*
TODO: add a variant for reading on both sides yielding poison or related values (for public and reserved tags)
*)
Lemma sim_make_unique_public l t ac (sc_s sc_t : list scalar) π Φ e_t e_s c M L:
  M !! t = Some L →
  l ↦t∗[tk_unq ac]{t} sc_t -∗
  l ↦s∗[tk_unq ac]{t} sc_s -∗
  t $$ tk_unq ac -∗
  c @@ M -∗
  (⌜ac = tk_act⌝ -∗ value_rel sc_t sc_s) -∗
  (t $$ tk_pub -∗ c @@ <[t := fmap filter_unq_weak L]> M -∗ e_t ⪯{π} e_s [{ Φ }]) -∗
  e_t ⪯{π} e_s [{ Φ }] .
Proof.
  iIntros (HL) "Ht Hs Htk Hprot #Hrel Hres".
  iApply sim_update_si. rewrite /update_si. iIntros (?????) "(HP_t & HP_s & Hbor)".
  iPoseProof (bor_interp_get_pure with "Hbor") as "%Hp".
  destruct Hp as (Hsst_eq & Hstrs_eq & Hsnc_eq & Hscs_eq & Hwf_s & Hwf_t & Hdom_eq).
  iDestruct "Hbor" as "(%M_call & %M_tag & %M_t & %M_s & Hbor)".
  iDestruct "Hbor" as "((Hc & Htag_auth & Htag_t_auth & Htag_s_auth) & Htainted & Hpub_cid & #Hsrel & %Hcall_interp & %Htag_interp & _)".
  iPoseProof (tkmap_lookup with "Htag_auth Htk") as "%Ht_tk".
  iAssert (|==> tkmap_auth tag_name 1 (<[ t := (tk_pub, ()) ]> M_tag) ∗ t $$ tk_pub)%I with "[Htag_auth Htk]" as ">(Htag_auth&Htk)".
  { iMod (tkmap_update_strong tk_pub tt with "Htag_auth Htk") as "($&$)"; done. }
  iPoseProof (ghost_map_lookup with "Htag_t_auth Ht") as "%Hhl_t".
  iPoseProof (ghost_map_lookup with "Htag_s_auth Hs") as "%Hhl_s".
  iMod (ghost_map_delete with "Htag_t_auth Ht") as "Htag_t_auth".
  iMod (ghost_map_delete with "Htag_s_auth Hs") as "Htag_s_auth".
  iPoseProof (ghost_map_lookup with "Hc Hprot") as "%Hprot".
  iMod (ghost_map_update (<[t:=filter_unq_weak <$> L]> M) with "Hc Hprot") as "(Hc&Hprot)".
  iAssert (⌜length sc_t = length sc_s⌝)%I as "%Hlen".
  { iPureIntro. destruct Htag_interp as (Ht1&_).
    specialize (Ht1 _ _ Ht_tk).
    destruct Ht1 as (_&_&_&_&_&(Htt1&Htt2)). eapply list_to_heaplet_dom_2.
    eapply gset_leibniz. intros x.
    setoid_rewrite elem_of_dom.
    split; intros [k Hk].
    - ospecialize (Htt1 (l.1, x) _).
      1: rewrite /heaplet_lookup /= Hhl_t /=; eapply mk_is_Some, Hk.
      1: rewrite /heaplet_lookup /= Hhl_s /= // in Htt1.
    - ospecialize (Htt2 (l.1, x) _).
      1: rewrite /heaplet_lookup /= Hhl_s /=; eapply mk_is_Some, Hk.
      1: rewrite /heaplet_lookup /= Hhl_t /= // in Htt2. }
  iModIntro. iSplitR "Hres Htk Hprot".
  2: by iApply ("Hres" with "Htk Hprot").
  iFrame "HP_s HP_t". iExists (<[c := _ ]> M_call), _, (delete (t, l.1) M_t), (delete (t, l.1) M_s).
  iFrame "Hc Htag_t_auth Htag_s_auth Hpub_cid Htag_auth Htainted".
  iSplit; last (iPureIntro; split; last (split; last done)).
  - repeat (iSplit; first done). iDestruct "Hsrel" as "(_&_&_&_&_&Hsrel)".
    iIntros (ll Hll). iDestruct ("Hsrel" $! ll Hll) as "[Hpub|(%tt&%Hpriv)]".
    1: by iLeft.
    destruct (decide (t = tt)) as [->|Hne].
    2: { iRight. iPureIntro. exists tt.
         rewrite /priv_loc lookup_insert_ne //.
         rewrite /heaplet_lookup lookup_delete_ne //. 2: simpl; by congruence.
         destruct Hpriv as (tk&H1&H2&H3). exists tk. split; first done. split; first done.
         destruct H3 as [H3|(c'&ae'&H3A&H3B)]. 1: by left.
         right. exists c', ae'. split; first done.
         destruct H3B as (MM&HMM&H3B).
         destruct (decide (c = c')) as [->|Hne'].
         2: exists MM; split; last done; rewrite lookup_insert_ne //.
         assert (M = MM) as -> by congruence.
         eexists. rewrite lookup_insert_eq. split; first done.
         destruct H3B as (LL&HLL&H3B). exists LL.
         rewrite lookup_insert_ne //. }
    iLeft. rewrite /pub_loc. iIntros (sc_t' Hsc_t').
    destruct Hpriv as (x&Htk'&Hheaplet&Hx). assert (x = tk_unq ac) as -> by congruence.
    destruct Htag_interp as (Ht1&Ht2&Ht3&Ht4&Ht5).
    destruct Hheaplet as (sc_ll&(hl_t'&Hheaplet_t1&Hheaplet_t2)%bind_Some).
    simpl in Hheaplet_t1.
    assert (l.1 = ll.1) as Hlleq.
    { eapply Ht4. all: by eapply elem_of_dom_2. } rewrite /= -Hlleq Hhl_t in Hheaplet_t1.
    injection Hheaplet_t1 as <-. simpl in Hheaplet_t2.
    specialize (Ht1 _ _ Htk') as (HHt1&HHt2&Httlocal&HHt3&HHt4&HHt5).
    ospecialize (HHt3 ll _ _).
    1: rewrite /heaplet_lookup /= -Hlleq Hhl_t /= Hheaplet_t2 //.
    assert (∃ sc_ll_s, list_to_heaplet sc_s l.2 !! ll.2 = Some sc_ll_s) as (sc_ll_s&Hsc_ll_s).
    { eapply elem_of_dom. erewrite list_to_heaplet_dom_1. 2: symmetry; eapply Hlen. eapply elem_of_dom_2. eapply Hheaplet_t2. }
    assert (∃ (i:nat), ll.2 = l.2 + i) as (i&Hoff).
    { eapply list_to_heaplet_lookup_Some in Hsc_ll_s. exists (Z.to_nat (ll.2 - l.2)). lia. }
    rewrite Hoff in Hsc_ll_s Hheaplet_t2.
    destruct Hx as [[=]|(c'&ae&[= ->]&Hcs)].
    destruct HHt3 as (_&HHt3).
    { opose proof* (call_set_interp_access) as Hacc. 1: done. 1: exact Hcs.
      destruct Hacc as (Hc&Hv&it&Hit&Hprot1&Hprot2&Hprot3&Hprot4&Hprot5&_).
      exists it. done. }
    specialize (HHt4 ll sc_ll_s).
    destruct HHt4 as (_&HHt4).
    1: rewrite /heaplet_lookup /= -Hlleq Hhl_s /= Hoff //.
    { opose proof* (call_set_interp_access) as Hacc. 1: done. 1: exact Hcs.
      destruct Hacc as (Hc&Hv&it&Hit&Hprot1&Hprot2&Hprot3&Hprot4&Hprot5&Hprot6).
      odestruct trees_equal_find_equal_tag_protected_initialized_not_disabled as (it2&HH1&HH2&HH3).
      3: by eapply trees_equal_sym. 1-2: by eapply Hwf_s. 2: intros _; exact Hprot5. 2: exists c'; by rewrite Hscs_eq.
      1: done.
      exists it2. done. }
    iExists sc_ll_s. iSplit; first done.
    assert (sc_ll = sc_t') as <- by congruence.
    rewrite !list_to_heaplet_nth in Hsc_ll_s Hheaplet_t2.
    iSpecialize ("Hrel" $! eq_refl).
    iPoseProof (big_sepL2_lookup_acc with "Hrel") as "($&_)".
    all: done.
  - destruct Hcall_interp as (Hcall_interp&Hcc2). split; last first.
    { intros ????? [(H1&H2)|(H1&H2)]%lookup_insert_Some [(H1'&H2')|(H1'&H2')]%lookup_insert_Some; simplify_eq.
      + done.
      + rewrite dom_insert_lookup_L. 1: by eapply Hcc2. by eexists.
      + rewrite dom_insert_lookup_L. 1: by eapply Hcc2. by eexists.
      + by eapply Hcc2. }
    pose proof Hcall_interp as Hcall_M_L.
    specialize (Hcall_M_L _ _ Hprot) as (MH1&MH2).
    specialize (MH2 _ _ HL) as (MH2&MH3). pose proof MH3 as HLne.
    intros c' M' [(<-&<-)|(Hne&HM')]%lookup_insert_Some.
    1: split; first done.
    1: intros tg' L' [(<-&<-)|(Hne2&HL')]%lookup_insert_Some.
    + split; first done.
      intros l' ps' (ps&<-&Hps)%lookup_fmap_Some.
      specialize (MH3 _ _ Hps) as H3.
      destruct ps as [|[]]; simpl.
      * intros it Hit. destruct (H3 _ Hit) as (HH1&HH2&HH3&HH4&?&?). split_and!; done.
      * destruct H3 as (it&Hit&HH1&HH2&HH3&HH4&?&?). exists it. split; first done. split_and!; done.
      * intros it (tr&Htr&Hit). destruct H3 as (it'&(tr'&Htr'&Hit')&HH1&HH2&HH3&HH4&?&?).
        assert (tr' = tr) as -> by congruence.
        assert (it = it') as -> by by eapply tree_lookup_unique. split_and!; done.
    + specialize (Hcall_interp _ _ Hprot) as (_&H2).
      specialize (H2 _ _ HL') as (H2&H3). split; first done.
      intros l' ps Hps. specialize (H3 _ _ Hps).
      eapply tag_protected_for_mono. 2: exact H3.
      intros [blk off] it (tr&Htr&Hlu) Hiscall Hinit (tkp&Htag&Hheap).
      eapply tree_lookup_correct_tag in Hlu as Htg'; subst tg'.
      exists tkp. rewrite lookup_insert_ne. 2: done. split; first done.
      rewrite /heaplet_lookup lookup_delete_ne. 2: simpl; congruence. done.
    + specialize (Hcall_interp _ _ HM') as (H1&H2). split; first done.
      intros tg' L' HL'. specialize (H2 _ _ HL') as (H2&H3). split; first done.
      intros l' ps Hps. specialize (H3 _ _ Hps).
      eapply tag_protected_for_mono. 2: exact H3.
      intros [blk off] it Hlu Hiscall Hinit (tkp&Htag&Hheap).
      eapply trees_lookup_correct_tag in Hlu as Htg'. subst tg'.
      assert (itag it ≠ t) as Hne2.
      { intros <-. eapply Hne. eapply Hcc2. 1-2: done. all: eapply elem_of_dom_2. 1: exact HL. done. }
      exists tkp. rewrite lookup_insert_ne. 2: done. split; first done.
      rewrite /heaplet_lookup lookup_delete_ne. 2: simpl; congruence. done.
  - destruct Htag_interp as (H1&H2&H3&H4&H5). split_and!.
    + intros tg tk' [(->&[= <-])|(Hne&Hin)]%lookup_insert_Some; last first.
      * specialize (H1 _ _ Hin) as (HH1&HH2&HHlocal&HH3&HH4&HH5). split_and!.
        1-2: done.
        { intros ->. destruct HHlocal as (HHl1&HHl2). 1: done.
          split; intros ?? (?&HH)%lookup_delete_Some. 1: by eapply HHl1. by eapply HHl2. }
        3: { rewrite /dom_agree_on_tag /heaplet_lookup /= //.
             split; intros ?; rewrite !lookup_delete_ne; try congruence.
             all: eapply HH5. }
        { intros l' sc' H. rewrite /heaplet_lookup /= !lookup_delete_ne // in H. 2: congruence. eapply HH3.
          done. }
        { intros l' sc' H. rewrite /heaplet_lookup /= !lookup_delete_ne // in H. 2: congruence. eapply HH4.
          done. }
      * specialize (H1 _ _ Ht_tk) as (HH1&HH2&HHlocal&HH3&HH4&HH5). split_and!.
        1-3: done.
        3: { eapply dom_agree_on_tag_upd_delete. all: done. }
        all: intros ??; rewrite /= /heaplet_lookup /=.
        all: intros (x&(Hne&Hin)%lookup_delete_Some&Hy)%bind_Some.
        all: exfalso.
        { ospecialize* H4. 1-2: eapply elem_of_dom_2. 1: exact Hin. 1: exact Hhl_t. congruence. }
        { ospecialize* H5. 1-2: eapply elem_of_dom_2. 1: exact Hin. 1: exact Hhl_s. congruence. }
    + intros t' blk H%elem_of_dom. rewrite dom_delete_L in H. eapply elem_of_difference in H as (H&Hne).
      eapply elem_of_dom. rewrite dom_insert_lookup_L. 2: by eexists.
      by eapply elem_of_dom, H2, elem_of_dom.
    + intros t' blk H%elem_of_dom. rewrite dom_delete_L in H. eapply elem_of_difference in H as (H&Hne).
      eapply elem_of_dom. rewrite dom_insert_lookup_L. 2: by eexists.
      by eapply elem_of_dom, H3, elem_of_dom.
    + intros tg blk1 blk2. rewrite !dom_delete_L. intros (?&_)%elem_of_difference (?&_)%elem_of_difference.
      by eapply H4.
    + intros tg blk1 blk2. rewrite !dom_delete_L. intros (?&_)%elem_of_difference (?&_)%elem_of_difference.
      by eapply H5.
Qed.


Lemma sim_make_local_public l t (sc_s sc_t : list scalar) π Φ e_t e_s:
  l ↦t∗[tk_local]{t} sc_t -∗
  l ↦s∗[tk_local]{t} sc_s -∗
  t $$ tk_local -∗
  value_rel sc_t sc_s -∗
  (t $$ tk_pub -∗ e_t ⪯{π} e_s [{ Φ }]) -∗
  e_t ⪯{π} e_s [{ Φ }] .
Proof.
  iIntros "Ht Hs Htk #Hrel Hres".
  iApply sim_update_si. rewrite /update_si. iIntros (?????) "(HP_t & HP_s & Hbor)".
  iPoseProof (bor_interp_get_pure with "Hbor") as "%Hp".
  destruct Hp as (Hsst_eq & Hstrs_eq & Hsnc_eq & Hscs_eq & Hwf_s & Hwf_t & Hdom_eq).
  iDestruct "Hbor" as "(%M_call & %M_tag & %M_t & %M_s & Hbor)".
  iDestruct "Hbor" as "((Hc & Htag_auth & Htag_t_auth & Htag_s_auth) & Htainted & Hpub_cid & #Hsrel & %Hcall_interp & %Htag_interp & _)".
  iPoseProof (tkmap_lookup with "Htag_auth Htk") as "%Ht_tk".
  iAssert (|==> tkmap_auth tag_name 1 (<[ t := (tk_pub, ()) ]> M_tag) ∗ t $$ tk_pub)%I with "[Htag_auth Htk]" as ">(Htag_auth&Htk)".
  { iMod (tkmap_update_strong tk_pub tt with "Htag_auth Htk") as "($&$)"; done. }
  iPoseProof (ghost_map_lookup with "Htag_t_auth Ht") as "%Hhl_t".
  iPoseProof (ghost_map_lookup with "Htag_s_auth Hs") as "%Hhl_s".
  iMod (ghost_map_delete with "Htag_t_auth Ht") as "Htag_t_auth".
  iMod (ghost_map_delete with "Htag_s_auth Hs") as "Htag_s_auth".
  iAssert (⌜length sc_t = length sc_s⌝)%I as "%Hlen". 1: by iApply big_sepL2_length.

  iModIntro. iSplitR "Hres Htk".
  2: by iApply "Hres".
  iFrame "HP_s HP_t". iExists M_call, _, (delete (t, l.1) M_t), (delete (t, l.1) M_s).
  iFrame "Hc Htag_t_auth Htag_s_auth Hpub_cid Htag_auth Htainted".
  iSplit; last (iPureIntro; split; last (split; last done)).
  - repeat (iSplit; first done). iDestruct "Hsrel" as "(_&_&_&_&_&Hsrel)".
    iIntros (ll Hll). iDestruct ("Hsrel" $! ll Hll) as "[Hpub|(%tt&%Hpriv)]".
    1: by iLeft.
    destruct (decide (t = tt)) as [->|Hne].
    2: { iRight. iPureIntro. exists tt.
         rewrite /priv_loc lookup_insert_ne //.
         rewrite /heaplet_lookup lookup_delete_ne //. simpl. by congruence. }
    iLeft. rewrite /pub_loc. iIntros (sc_t' Hsc_t').
    destruct Hpriv as (x&Htk'&Hheaplet&Hx). assert (x = tk_local) as -> by congruence.
    destruct Htag_interp as (Ht1&Ht2&Ht3&Ht4&Ht5).
    destruct Hheaplet as (sc_ll&(hl_t'&Hheaplet_t1&Hheaplet_t2)%bind_Some).
    simpl in Hheaplet_t1.
    assert (l.1 = ll.1) as Hlleq.
    { eapply Ht4. all: by eapply elem_of_dom_2. } rewrite /= -Hlleq Hhl_t in Hheaplet_t1.
    injection Hheaplet_t1 as <-. simpl in Hheaplet_t2.
    specialize (Ht1 _ _ Htk') as (HHt1&HHt2&HHt_local&HHt3&HHt4&HHt5).
    ospecialize (HHt3 ll _ _).
    1: rewrite /heaplet_lookup /= -Hlleq Hhl_t /= Hheaplet_t2 //.
    assert (∃ sc_ll_s, list_to_heaplet sc_s l.2 !! ll.2 = Some sc_ll_s) as (sc_ll_s&Hsc_ll_s).
    { eapply elem_of_dom. erewrite list_to_heaplet_dom_1. 2: symmetry; eapply Hlen. eapply elem_of_dom_2. eapply Hheaplet_t2. }
    assert (∃ (i:nat), ll.2 = l.2 + i) as (i&Hoff).
    { eapply list_to_heaplet_lookup_Some in Hsc_ll_s. exists (Z.to_nat (ll.2 - l.2)). lia. }
    rewrite Hoff in Hsc_ll_s Hheaplet_t2.

    destruct HHt3 as (_&HHt3).
    { destruct Hx as [|(c&ae&Heq&Hcs)]. 1: done. exfalso. congruence. }
    specialize (HHt4 ll sc_ll_s).
    destruct HHt4 as (_&HHt4).
    1: rewrite /heaplet_lookup /= -Hlleq Hhl_s /= Hoff //.
    { destruct Hx as [|(c&ae&Heq&Hcs)]. 1: done. exfalso. congruence. }
    iExists sc_ll_s. iSplit; first done.
    assert (sc_ll = sc_t') as <- by congruence.
    rewrite !list_to_heaplet_nth in Hsc_ll_s Hheaplet_t2.
    iPoseProof (big_sepL2_lookup_acc with "Hrel") as "($&_)".
    all: done.
  - destruct Hcall_interp as (Hcall_interp&Hcc2). split; last done. 
    intros c M' HM'. specialize (Hcall_interp _ _ HM') as (H1&H2). split; first done.
    intros tg' L HL. specialize (H2 _ _ HL) as (H2&H3). split; first done.
    intros l' ps Hps. specialize (H3 _ _ Hps).
    eapply tag_protected_for_mono. 2: exact H3.
    intros [blk off] it Hlu Hiscall Hinit (tkp&Htag&Hheap).
    exists tkp. assert (itag it ≠ t) as Hne.
    { intros <-. congruence. }
    rewrite lookup_insert_ne //. split; first done.
    rewrite /heaplet_lookup lookup_delete_ne /= //.
    intros [= ??]; done.
  - destruct Htag_interp as (H1&H2&H3&H4&H5). split_and!.
    + intros tg tk' [(->&[= <-])|(Hne&Hin)]%lookup_insert_Some; last first.
      * specialize (H1 _ _ Hin) as (HH1&HH2&HHlocal&HH3&HH4&HH5). split_and!.
        1-2: done.
        1: { intros ->; destruct HHlocal as (HHl1&HHl2); split; intros ?? (?&H)%lookup_delete_Some.
             1: by eapply HHl1. by eapply HHl2. }
        (* 1: rewrite !dom_delete_L; intros ?; split; intros ? (?&?)%elem_of_difference; by eapply HHlocal. *)
        3: { rewrite /dom_agree_on_tag /heaplet_lookup /= //.
             split; intros ?; rewrite !lookup_delete_ne; try congruence.
             all: eapply HH5. }
        { intros l' sc' H. rewrite /heaplet_lookup /= !lookup_delete_ne // in H. 2: congruence. 
          by eapply HH3. }
        { intros l' sc' H. rewrite /heaplet_lookup /= !lookup_delete_ne // in H. 2: congruence. 
          by eapply HH4. }
      * specialize (H1 _ _ Ht_tk) as (HH1&HH2&HHlocal&HH3&HH4&HH5). split_and!.
        1-2: done.
        1: done.
        3: { eapply dom_agree_on_tag_update_same_delete. all: done. }
        all: intros ??; rewrite /= /heaplet_lookup /=.
        all: intros (x&(Hne&Hin)%lookup_delete_Some&Hy)%bind_Some.
        all: exfalso.
        { ospecialize* H4. 1-2: eapply elem_of_dom_2. 1: exact Hin. 1: exact Hhl_t. congruence. }
        { ospecialize* H5. 1-2: eapply elem_of_dom_2. 1: exact Hin. 1: exact Hhl_s. congruence. }
    + intros t' blk H%elem_of_dom. rewrite dom_delete_L in H. eapply elem_of_difference in H as (H&?).
      eapply elem_of_dom. rewrite dom_insert_lookup_L. 2: by eexists.
      by eapply elem_of_dom, H2, elem_of_dom.
    + intros t' blk H%elem_of_dom. rewrite dom_delete_L in H. eapply elem_of_difference in H as (H&?).
      eapply elem_of_dom. rewrite dom_insert_lookup_L. 2: by eexists.
      by eapply elem_of_dom, H3, elem_of_dom.
    + intros tg blk1 blk2. rewrite !dom_delete_L. do 2 intros (?&?)%elem_of_difference.
      by eapply H4.
    + intros tg blk1 blk2. rewrite !dom_delete_L. do 2 intros (?&?)%elem_of_difference.
      by eapply H5.
Qed.

Lemma sim_protected_unprotect M L l c t tk v_t v_s  π Φ e_t e_s :
  (∀ i : nat, (i < length v_t)%nat → (l +ₗ i) ∈ dom L) →
  M !! t = Some L →
  c @@ M -∗
  t $$ tk -∗
  (⌜tk = tk_unq tk_act⌝ -∗ l ↦t∗[tk]{t} v_t ∗ l ↦s∗[tk]{t} v_s ∗ value_rel v_t v_s) -∗
  (c @@ (delete t M) -∗ t $$ tk -∗ (⌜tk = tk_unq tk_act⌝ -∗ l ↦t∗[tk]{t} v_t ∗ l ↦s∗[tk]{t} v_s) -∗ e_t ⪯{π} e_s [{ Φ }]) -∗
  e_t ⪯{π} e_s [{ Φ }].
Proof.
  iIntros (HL HM) "Hcall Htk Hvrel Hsim".
  iApply sim_update_si. rewrite /update_si. iIntros (? σ_t ? σ_s ?) "(HP_t & HP_s & Hbor)".
  iPoseProof (bor_interp_get_pure with "Hbor") as "%Hp".
  destruct Hp as (Hsst_eq & Hstrs_eq & Hsnc_eq & Hscs_eq & Hwf_s & Hwf_t & Hdom_eq).
  iDestruct "Hbor" as "(%M_call & %M_tag & %M_t & %M_s & Hbor)".
  iDestruct "Hbor" as "((Hc & Htag_auth & Htag_t_auth & Htag_s_auth) & Htainted & Hpub_cid & #Hsrel & %Hcall_interp & %Htag_interp & _)".
  iPoseProof (tkmap_lookup with "Htag_auth Htk") as "%Htk".
  iAssert (⌜tk = tk_unq tk_act → M_t !! (t, l.1) = Some _ ∧ M_s !! (t, l.1) = Some _⌝)%I as "%Hhl_ts".
  { iIntros (H). iDestruct ("Hvrel" $! H) as "(Hhl_t&Hhl_s&_)".
    iPoseProof (ghost_map_lookup with "Htag_t_auth Hhl_t") as "%Hhl_t".
    iPoseProof (ghost_map_lookup with "Htag_s_auth Hhl_s") as "%Hhl_s".
    iPureIntro. split; eassumption. }
  iPoseProof (ghost_map_lookup with "Hc Hcall") as "%Hcall".
  iAssert (⌜tk = tk_unq tk_act⌝ -∗ value_rel v_t v_s)%I as "#Hvrel'".
  { iIntros (H). iDestruct ("Hvrel" $! H) as "(_&_&$)". }
  iMod (ghost_map_update (delete t M) with "Hc Hcall") as "(Hc&Hcall)".
  iSpecialize ("Hsim" with "Hcall Htk [Hvrel]").
  1: { iIntros (H). iDestruct ("Hvrel" $! H) as "(Hhl_t&Hhl_s&_)". iFrame. }
  iFrame "Hsim HP_t HP_s".
  iModIntro. iExists _, M_tag, M_t, M_s. iFrame "Hc Hpub_cid Htag_t_auth Htag_s_auth Htag_auth Htainted".
  iSplit. 2: iPureIntro; split_and!.
  4, 5: done.
  - do 5 (iSplit; first done). iDestruct "Hsrel" as "(_&_&_&_&_&Hsrel)".
    iIntros (l0 Hlo). iDestruct ("Hsrel" $! l0 Hlo) as "[Hpub|%Hpriv]". 1: by iLeft.
    destruct Hpriv as (tp&tkp&Htkp&Hhlp&HH). destruct HH as [->|(cc&ae&->&Hin)].
    1: iRight; iPureIntro; eexists tp, _; do 2 (split; first done); by left.
    destruct (decide (t = tp)) as [->|Hdifftag]; last first.
    + iRight; iPureIntro.
      eexists tp, _. do 2 (split; first done).
      right. exists cc, ae. split; first done.
      rewrite /call_set_in'.
      destruct (decide (c = cc)) as [->|Hnecc]; last first.
      1: by rewrite lookup_insert_ne.
      rewrite lookup_insert_eq. eexists; split; first done.
      destruct Hin as (M'&HM'&HHH). assert (M' = M) as -> by congruence.
      rewrite /call_set_in lookup_delete_ne //.
    + iLeft. iIntros (v Hvs). assert (tk = tk_unq tk_act) as -> by congruence.
      destruct Hhl_ts as (Hhl_t&Hhl_s); first done.
      iPoseProof ("Hvrel'" $! eq_refl) as "Hvrel".
      destruct Hhlp as (v_hlu&(vs_hl1&Hvshl1&Hv_hlu)%bind_Some). simpl in *.
      destruct Htag_interp as (Hti1&Hti2&Hti3&Hti4&Hti5).
      assert (l.1 = l0.1) as Hl1eq.
      { eapply Hti4; eapply elem_of_dom_2; done. }
      assert (vs_hl1 = list_to_heaplet v_t l.2) as -> by congruence.
      destruct Hcall_interp as (Hci&Hci2).
      destruct Hin as (M'&HM'&L'&HL'&Hin). assert (c = cc) as ->.
      { eapply Hci2. 1-2: done. all: eapply elem_of_dom_2; done. }
      assert (M' = M) as -> by congruence.
      assert (L' = L) as -> by congruence.
      opose proof* protected_tags_bor_state_pre as Hpre_t.
      { eapply Hci. 1: exact Hcall. 1: exact HL'. 1: exact Hin. }
      eapply list_to_heaplet_lookup_Some in Hv_hlu as Hbounds.
      assert (∃ i:nat , l0.2 = l.2 + i) as (i&Hi).
      { exists (Z.to_nat (l0.2-l.2)). lia. }
      rewrite Hi list_to_heaplet_nth in Hv_hlu.
      destruct (Hti1 _ _ Htk) as (HHti1&HHti2&_&HHti3&HHti4&HHti5).
      edestruct (HHti3 l0) as (_&Hvshl1hp).
      1: rewrite /heaplet_lookup Hvshl1 /= Hi list_to_heaplet_nth Hv_hlu //. 1: done.
      assert (v_hlu = v) as -> by congruence.
      rewrite /value_rel. iPoseProof (big_sepL2_length with "Hvrel") as "%Hlen".
      assert (is_Some (v_s !! i)) as [v_on_s Hvons].
      { eapply lookup_lt_is_Some_2. lia. }
      iPoseProof (big_sepL2_lookup_acc with "Hvrel") as "(#Hv1&_)". 1: exact Hv_hlu. 1: exact Hvons.
      iExists v_on_s. iSplit; last done. iPureIntro.
      edestruct (HHti4 l0 v_on_s) as (_&Hdone). 3: done.
      1: rewrite /heaplet_lookup -Hl1eq Hhl_s /= Hi list_to_heaplet_nth Hvons //.
      eapply protected_tags_bor_state_pre.
      eapply tag_protected_for_trees_equal.
      7: eapply Hci; [exact Hcall|exact HL'|exact Hin].
      6: eapply trees_equal_sym; eassumption.
      2, 4: by eapply Hwf_s. 2: rewrite Hscs_eq. 1,2: eapply Hwf_t.
      rewrite Hscs_eq. eapply Hci. 1: done.
  - destruct Hcall_interp as (Hcall_interp&Hcc2). split; last first.
    { intros ????? [(?&?)|(?&?)]%lookup_insert_Some [(?&?)|(?&?)]%lookup_insert_Some; simplify_eq.
      1: done. 3: by eapply Hcc2.
      all: rewrite dom_delete_L. 1: intros (?&_)%elem_of_difference ?. 2: intros ? (?&_)%elem_of_difference.
      all: by eapply Hcc2. }
    intros c' M' [(<-&<-)|(Hne2&HM')]%lookup_insert_Some.
    { specialize (Hcall_interp _ _ Hcall) as (Hc1&Hc2). split; first done.
      intros t' L' (Hne3&H')%lookup_delete_Some. by eapply Hc2. }
    eapply Hcall_interp. done.
  - destruct Htag_interp as (H1&H2&H3&H4&H5).
    split_and!. 2-5: done.
    intros t' tk' Htk'. destruct (H1 _ _ Htk') as (Ht1&Ht2&Htlocal&Ht3&Ht4&Ht5). split_and!.
    1,2,3,6: done.
    all: done.
(*
    1: intros l0 vvs Hh1 Hpre; destruct (Ht3 _ _ Hh1 Hpre) as ((it&tr&Htr&Hit&Hini&Hh2)&Hh3).
    2: intros l0 vvs Hh1 Hpre; destruct (Ht4 _ _ Hh1 Hpre) as ((it&tr&Htr&Hit&Hini&Hh2)&Hh3).
    all:  (split; last done);
          exists it, tr; do 3 (split; first done); (destruct tk'; [done| |done]); destruct Hh2 as (Hown&Hothers);
          (split; last done); clear Hothers; intros Hfrz; specialize (Hown Hfrz);
          (destruct (perm (item_lookup it l0.2)) as [[]| | |]; [|done..]); destruct Hown as (->&Ho2&Ho3); do 2 (split; first done);
          destruct Ho3 as (lp&pp&Hpp&HHH&Hxx); exists lp, pp; (split_and!; [done| |done]);
          destruct HHH as (M'&HM'&HHH);
          (destruct (decide (c = call pp)) as [->|Hnec]; last (exists M'; rewrite lookup_insert_ne //));
          destruct HHH as (L'&HL'&HHH); exists (delete t M); rewrite lookup_insert_eq; (split; first done);
          assert (M = M') as -> by congruence;
          (destruct (decide (t = t')) as [->|Hnet]; first congruence);
          exists L'; by rewrite lookup_delete_ne. *)
Qed.

Lemma sim_protected_unprotect_public M L c t π Φ e_t e_s :
  M !! t = Some L →
  c @@ M -∗
  t $$ tk_pub -∗
  (c @@ (delete t M) -∗ e_t ⪯{π} e_s [{ Φ }]) -∗
  e_t ⪯{π} e_s [{ Φ }].
Proof.
  iIntros (H1) "H2 H3 H4".
  iApply (sim_protected_unprotect M L (xH, 0) c t tk_pub nil nil with "H2 H3").
  1: simpl; lia. 1: done. 1: iIntros ([=]).
  iIntros "H1 H2 _". iApply "H4". done.
Qed.

Lemma sim_protected_unprotect_unique_reserved M L c t π Φ e_t e_s :
  M !! t = Some L →
  c @@ M -∗
  t $$ tk_unq tk_res -∗
  (c @@ (delete t M) -∗ e_t ⪯{π} e_s [{ Φ }]) -∗
  e_t ⪯{π} e_s [{ Φ }].
Proof.
  iIntros (H1) "H2 H3 H4".
  iApply (sim_protected_unprotect M L (xH, 0) c t (tk_unq tk_res) nil nil with "H2 H3").
  1: simpl; lia. 1: done. 1: iIntros ([=]).
  iIntros "H1 H2 _". iApply "H4". done.
Qed.

Lemma sim_protected_unprotect_unique_active M L l c t v_t v_s π Φ e_t e_s :
  (∀ i : nat, (i < length v_t)%nat → (l +ₗ i) ∈ dom L) →
  M !! t = Some L →
  c @@ M -∗
  t $$ tk_unq tk_act -∗
  l ↦t∗[tk_unq tk_act]{t} v_t -∗
  l ↦s∗[tk_unq tk_act]{t} v_s -∗
  value_rel v_t v_s -∗
  (c @@ (delete t M) -∗ t $$ tk_unq tk_act -∗ l ↦t∗[tk_unq tk_act]{t} v_t -∗ l ↦s∗[tk_unq tk_act]{t} v_s -∗ e_t ⪯{π} e_s [{ Φ }]) -∗
  e_t ⪯{π} e_s [{ Φ }].
Proof.
  iIntros (H1 H2) "H3 H4 H5 H6 #H7 H8".
  iApply (sim_protected_unprotect M L l c t _ v_t v_s with "H3 H4 [H5 H6 H7] [H8]"). 1-2: done.
  - iIntros "_". iFrame. done.
  - iIntros "H1 H2 H3". iDestruct ("H3" $! eq_refl) as "(H5&H6)".
    iApply ("H8" with "H1 H2 H5 H6").
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
