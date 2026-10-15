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
From simuliris.tree_borrows.trees_equal Require Import trees_equal_more_access trees_equal_preserved_by_access trees_equal_create_child.

Section lifting.
Context `{!sborGS Σ}.
Implicit Types P Q : iProp Σ.
Implicit Types Φ : expr → expr → iProp Σ.
Implicit Types σ σ_s σ_t : state.
Implicit Types r r_s r_t : result.
Implicit Types l : loc.
Implicit Types f : fname.


(** ** Retags *)

Lemma tree_access_succeeds_heap_value σ b ak tg blk off sz :
  state_wf σ →
  trees_contain tg σ.(strs) blk →
  is_Some (apply_within_trees (memory_access_maybe_nonchildren_only b ak σ.(scs) tg (off, sz)) blk σ.(strs)) →
  is_Some (read_mem (blk, off) sz σ.(shp)).
Proof.
  intros Hwf Hcont [trs' (tr&Htr&(tr'&Htr'&[= <-])%bind_Some)%bind_Some].
  eapply read_mem_is_Some.
  intros m Hm.
  pose proof (state_wf_roots_active _ Hwf _ _ Htr) as Hcompat.
  destruct tr as [|it tr1 tr2]; first done. simpl in Hcompat.
  destruct Hcompat as ((Hprot&Hdis&Hroot)&->).
  specialize (Hroot (off + m)). rewrite /shift_loc /=.
  eapply elem_of_dom.
  assert (item_lookup it (off+m) = mkPerm PermInit Active ∧ is_Some (shp σ !! (blk, off+m)) 
        ∨ item_lookup it (off+m) = mkPerm PermLazy Disabled ∧ shp σ !! (blk, off+m) = None) as [(H1&H2)|(H1&H2)].
  { rewrite /item_lookup. destruct (iperm it !! (off + m)) as [[[] [| | | | |]]|] eqn:Hlookup; simplify_eq; try done.
    all: simpl. 1: by left. all: right. 1: done. by rewrite Hdis. }
  1: done.
  exfalso.
  rewrite /memory_access_maybe_nonchildren_only /tree_apply_access /= in Htr'.
  eapply bind_Some in Htr' as (it'&Hit'&_).
  rewrite /trees_contain /trees_at_block Htr in Hcont.
  rewrite /item_apply_access in Hit'.
  eapply bind_Some in Hit' as (perm'&Hperm'&_).
  rewrite /permissions_apply_range' in Hperm'.
  unshelve eapply mk_is_Some, mem_apply_range'_success_condition in Hperm' as (pp'&Hpp').
  1: exact (off + m).
  2: { rewrite /range'_contains. simpl. lia. }
  rewrite /item_lookup in H1. rewrite H1 in Hpp'. simpl in Hpp'.
  rewrite /rel_dec /= decide_True in Hpp'; last first.
  { eapply root_node_IsParentChild. 1: by eapply Hwf. done. }
  edestruct maybe_non_children_only_effect_or_nop_strong as [(Heq&Hsc)|(Heq&Hb&(ii&Hii))].
    all: erewrite Heq in Hpp'; clear Heq.
  2: done. clear Hsc.
  rewrite /apply_access_perm /apply_access_perm_inner /= in Hpp'.
  by destruct ak.
Qed.

(** *** Retags without protectors *)


Lemma sim_retag_default sz l_t l_s ot c pk tk im π Φ :
  pointer_kind_to_tag_unprotected pk im = Some tk → (* forbid interior mutability  *)
  sc_rel (ScPtr l_t ot) (ScPtr l_s ot) -∗
  (∀ nt v_t v_s,
    ⌜length v_t = sz⌝ -∗ ⌜length v_s = sz⌝ -∗
    value_rel v_t v_s -∗  (* as the pointers were public before *)
    nt $$ tk -∗
    l_t ↦t∗[tk]{nt} v_t -∗
    l_s ↦s∗[tk]{nt} v_s -∗
    #[ScPtr l_t nt] ⪯{π} #[ScPtr l_s nt] [{ Φ }]) -∗
  Retag #[ScPtr l_t ot] #[ScCallId c] pk im sz Default ⪯{π} Retag #[ScPtr l_s ot] #[ScCallId c] pk im sz Default [{ Φ }].
Proof.
  intros Htk. iIntros "#Hscrel Hsim".
  iApply sim_lift_base_step_both. iIntros (P_t P_s σ_t σ_s ??) "((HP_t & HP_s & Hbor) & %Hthread & %Hsafe)".
  (* exploit source to gain knowledge about stacks & that c is a valid id *)
  specialize (pool_safe_implies Hsafe Hthread) as (c' & ot' & l' & [= <- <-] & [= <-] & Hcin & Hotin & [HNone|(trs1 & trs2 &  Hntnin & Happly1_s & Happly2_s)]).
  { destruct pk, im; done. }
  iPoseProof "Hscrel" as "(-> & _ & Hotpub)". iClear "Hscrel".
  iPoseProof (bor_interp_get_pure with "Hbor") as "%Hp".
  destruct Hp as (Hstrs_eq & Hsnp_eq & Hsnc_eq & Hscs_eq & Hwf_s & Hwf_t & Hdom_eq).
  odestruct (trees_equal_create_child _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ Hstrs_eq Happly1_s) as (trs1_t&Happly1_t&Hstrs1_eq).
  1,3: eapply Hwf_s. 2: rewrite Hsnc_eq Hsnp_eq. 1,2: eapply Hwf_t. 1: by eapply Hwf_s.
  1-2: done.
  eapply retag_step_wf_inner in Hwf_s as X. 1: destruct X as (Hwf_mid_s&Hntinmid_s).
  2-5: done.
  eapply retag_step_wf_inner in Hwf_t as X. 1: destruct X as (Hwf_mid_t&_).
  5: by rewrite Hscs_eq Hsnp_eq in Happly1_t. 4: by rewrite -Hscs_eq. 2-3: setoid_rewrite <- trees_equal_same_tags; last done. 2: done. 2: by rewrite -Hsnp_eq.
  edestruct trees_equal_allows_more_access as (trs2_t&Happly2_t).
  1: exact Hstrs1_eq. 1: apply Hwf_mid_s. 1,2,3: rewrite ?Hscs_eq; apply Hwf_mid_t. 1: done. 1: done. 1: by eapply mk_is_Some.
  opose proof (trees_equal_preserved_by_access _ _ _ _ _ _ _ Hstrs1_eq _ Happly2_s Happly2_t) as Hstrs2_eq.
  1,3,5: eapply Hwf_mid_s. 1-3: rewrite ?Hscs_eq; eapply Hwf_mid_t. 1: done.

  odestruct (tree_access_succeeds_heap_value _ false) as (v_s&Hv_s).
  1: apply Hwf_mid_s. 2: eapply mk_is_Some, Happly2_s. 1: done. simpl in Hv_s.
  odestruct (tree_access_succeeds_heap_value _ false) as (v_t&Hv_t).
  1: apply Hwf_mid_t. 2: rewrite /= -Hscs_eq; eapply mk_is_Some, Happly2_t. 1: simpl; setoid_rewrite <- trees_equal_same_tags; try done. simpl in Hv_t.

  opose proof (state_wf_tree_unq _ Hwf_mid_t) as Hwf_trs1_t.
  opose proof (state_wf_tree_unq _ Hwf_mid_s) as Hwf_trs1_s.
  pose proof Hntinmid_s as Hntinmid_t.
  setoid_rewrite trees_equal_same_tags in Hntinmid_t. 2: done.
  clear Hstrs1_eq. (* TODO refactor the above into a separate lemma, maybe? *)

  iDestruct "Hbor" as "(%M_call & %M_tag & %M_t & %M_s & (Hc & Htag_auth & Htag_t_auth & Htag_s_auth) & Htainted & Hpub_cid & #Hsrel & %Hcall_interp & %Htag_interp & _ & _)".
  iDestruct (tkmap_lookup with "Htag_auth Hotpub") as "%Hotpub".
  assert (M_tag !! snp σ_s = None) as Htagfresh.
  { destruct (M_tag !! σ_s.(snp)) as [[x []]|] eqn:Heq; last done.
    destruct Htag_interp as (H1&_). specialize (H1 _ _ Heq) as (Hv&_).
    rewrite /tag_valid in Hv. lia. }
  iMod (tkmap_insert tk σ_s.(snp) tt with "Htag_auth") as "(Htag_auth&Htk)". 1: done.
  iDestruct "Hsrel" as "(_&_&_&_&_&Hsrel)".
  eapply read_mem_values in Hv_s as (Hlen_v_s&Hhpv_v_s).
  eapply read_mem_values in Hv_t as (Hlen_v_t&Hhpv_v_t). rewrite /shift_loc /= in Hhpv_v_t, Hhpv_v_s.
  unshelve iSpecialize ("Hsim" $! σ_s.(snp) v_t v_s _ _).
  1-2: done.

  opose proof* create_then_access_implies_earlier_access_trees as Hvirtual_t.
  5: exact Happly2_t. 4: exact Happly1_t. 2-3: setoid_rewrite <- trees_equal_same_tags; first done; done. 1: apply Hwf_t.

  iAssert (value_rel v_t v_s)%I as "Hvalrel".
  { rewrite /value_rel /=. iApply big_sepL2_forall. iSplit; first (iPureIntro; congruence).
    iIntros (off vt vs Hvt Hvs).
    ospecialize (Hhpv_v_t off _). 1: rewrite -Hlen_v_t; by eapply lookup_lt_Some.
    ospecialize (Hhpv_v_s off _). 1: rewrite -Hlen_v_s; by eapply lookup_lt_Some.
    rewrite Hvt in Hhpv_v_t.
    iDestruct ("Hsrel" $! _ (mk_is_Some _ _ Hhpv_v_t)) as "[Hpub|(%t&%Hpriv)]".
    - iDestruct ("Hpub" $! _ Hhpv_v_t) as "(%sc_s&%Hsc_s&Hscrel)".
      rewrite Hsc_s Hvs in Hhpv_v_s. injection Hhpv_v_s as ->. done.
    - exfalso. rewrite Hscs_eq in Hvirtual_t.
      opose proof* priv_loc_access_must_use_same_tag as Heq.
      5: done. 3-4: done. 1-2: done. all: simpl. 3: exact Hvirtual_t.
      1: setoid_rewrite <- trees_equal_same_tags; first done; done.
      1: split; first lia. 1: rewrite -Hlen_v_t. 1: eapply lookup_lt_Some in Hvt; lia.
      subst t. destruct Hpriv as (tk'&Htk'&[vls Hhl]&[->|(cc&ae&->&Hcc)]). all: congruence. }
  iSpecialize ("Hsim" with "Hvalrel Htk").
  assert (M_t !! (snp σ_s, l_s.1) = None) as Hhl_t_None.
  { destruct Htag_interp as (_&H1&H2&_). destruct (M_t !! (snp σ_s, l_s.1)) eqn:Heq; last done.
    exfalso. specialize (H1 _ _ (mk_is_Some _ _ Heq)). rewrite Htagfresh in H1. by destruct H1. }
  iMod (ghost_map_array_tag_insert _ _ v_t σ_s.(snp) l_s tk with "Htag_t_auth") as "(Hpt&Htag_t_auth)"; first done.
  assert (M_s !! (snp σ_s, l_s.1) = None) as Hhl_s_None.
  { destruct Htag_interp as (_&H1&H2&_). destruct (M_s !! (snp σ_s, l_s.1)) eqn:Heq; last done.
    exfalso. specialize (H2 _ _ (mk_is_Some _ _ Heq)). rewrite Htagfresh in H2. by destruct H2. }
  iMod (ghost_map_array_tag_insert _ _ v_s σ_s.(snp) l_s tk with "Htag_s_auth") as "(Hps&Htag_s_auth)"; first done.
  iSpecialize ("Hsim" with "Hpt Hps").

  iModIntro. iSplit.
  { iPureIntro. do 3 eexists. econstructor; econstructor.
    1,3-5: repeat rewrite -?Hscs_eq -?Hsnp_eq //.
    all: setoid_rewrite <- trees_equal_same_tags; last done; done. }
  iIntros (e_t' efs_t σ_t') "%Hhead_t".
  opose proof* (head_retag_inv _ _ _ _ _ _ _ _ _ _ _ _ Hhead_t) as (->&Hcin_t&Hotin_t&[(Hnone&->&->)|(trsX1&trsX2&->&Hσ_t&Hntnin_t&HX1&HX2)]).
  { exfalso. by destruct pk, im. }
  assert (trsX1 = trs1_t) as -> by congruence. clear HX1.
  assert (trsX2 = trs2_t) as -> by congruence. clear HX2.

  iModIntro. iExists _, _, _. iSplit.
  { iPureIntro. simpl. econstructor; econstructor. all: done. }

  iFrame "HP_t HP_s". rewrite -Hsnp_eq. iFrame "Hsim". simpl.
  iSplit; last done.
  iExists _, _, _, _. rewrite /bor_interp_inner. iFrame "Htag_auth Htag_t_auth Htag_s_auth Hc". simpl.
  iSplitL "Htainted"; last iSplit; last iSplit; last iSplit; last iSplit; last iSplit.
  - iDestruct "Htainted" as "(%M&Ht1&Ht2)". iExists M. iFrame "Ht1".
    iIntros (t' l' Htl'). iDestruct ("Ht2" $! t' l' Htl') as "($&%Ht2)". iPureIntro.
    simpl. eapply disabled_tag_tree_apply_access_irreversible. 4: done. 2: done. 2: by eapply Hwf_mid_s.
    eapply disabled_tag_create_child_irreversible. 4: eapply Happly1_s. 2: done.
    + destruct Ht2 as (Hlt&Ht2); lia.
    + destruct Ht2 as (Hlt&Ht2); split; last done. lia.
  - iApply pub_cid_interp_preserve_sub. 5: iFrame.
    1,3: by subst σ_t'. all: done.
  - subst σ_t'. rewrite -Hsnp_eq. do 5 (iSplit; first done). simpl.
    iIntros (l Hl). iDestruct ("Hsrel" $! l Hl) as "[Hpub|(%t&%Hpriv)]".
    + iLeft. iApply "Hpub".
    + iRight. iExists t. iPureIntro. destruct Hpriv as (tk'&Htk'&Hhl&Htag).
      exists tk'. split. 1: rewrite lookup_insert_ne //. 1: intros <-; congruence.
      split. 1: rewrite /heaplet_lookup /= -?insert_union_singleton_l in Hhl|-*; rewrite lookup_insert_ne //; congruence.
      apply Htag.
  - iPureIntro. subst σ_t'. destruct Hcall_interp as (Hcall_interp&Hcc2). split; last first. 1: done.
    intros cc M' HM'. specialize (Hcall_interp cc M' HM') as (Hc1&Hc2). simpl.
    split; first done. intros tt L HL. specialize (Hc2 tt L HL) as (Hc3&Hc4).
    split. 1: eapply tag_valid_mono; first done; lia.
    intros l ps Hps. specialize (Hc4 l ps Hps).
    eapply (tag_protected_preserved_by_create ps ot (snp σ_s) pk im Default (scs σ_s)) in Hc4.
    4: exact Happly1_t. 2: eapply Hwf_t. 2: { intros <-. rewrite /tag_valid in Hc3. lia. }
    eapply tag_protected_preserved_by_access.
    2: exact Happly2_t. 2: rewrite Hscs_eq; apply Hc1. 1: eapply Hwf_trs1_t.
    eapply tag_protected_for_mono; last exact Hc4.
    intros l'' it ? ? ? (tk'&Htk'&Hhl'). exists tk'. split.
    + rewrite lookup_insert_ne //; intros Heq.
      by rewrite -Heq Htagfresh in Htk'.
    + rewrite /heaplet_lookup /= /array_tag_map /= lookup_union_r //.
      eapply not_elem_of_dom. rewrite dom_singleton_L. intros HH%elem_of_singleton.
      rewrite /heaplet_lookup /= HH /= Hhl_t_None /= in Hhl'. by destruct Hhl'.
  - iPureIntro. destruct Htag_interp as (Ht1&Ht2&Ht3&Ht4&Ht5).
    split_and!.
    2-5: rewrite /array_tag_map -!insert_union_singleton_l.
    2-3: intros t blk (x & [([= <- <-]&<-)|(?&?)]%lookup_insert_Some);
         [by rewrite lookup_insert_eq|eapply lookup_insert_is_Some'; right].
         2: eapply Ht2. 3: eapply Ht3. 2-3: by eapply mk_is_Some.
    2,3: intros tg l1 l2; rewrite !dom_insert_L;
         intros [[= Heq1 Heq2]%elem_of_singleton|H1%elem_of_dom]%elem_of_union;
         intros [[= Heq3 Heq4]%elem_of_singleton|H2%elem_of_dom]%elem_of_union; simplify_eq;
         [done|rename H2 into H1| | ].
         4: eapply Ht4; by eapply elem_of_dom.
         6: eapply Ht5; by eapply elem_of_dom.
         2,3: eapply Ht2 in H1. 4,5: eapply Ht3 in H1.
         2-5: rewrite Htagfresh in H1; by destruct H1.
    intros t tk' [(<-&[= <-])|(Hne&Hin)]%lookup_insert_Some; last first.
    + subst σ_t'. specialize (Ht1 _ _ Hin) as (Htt1&Htt2&Httlocal&Htt3&Htt4&Htt5).
      split_and!.
      3: { intros ->. rewrite /array_tag_map. destruct Httlocal as (Httl1&Httl2); first done.
           split;
           (intros bblk MM [([= <- <-]&<-)%lookup_singleton_Some|(_&H)]%lookup_union_Some_raw;
            [ done | (try by eapply Httl1); by eapply Httl2]). }
      1-2: simpl; eapply tag_valid_mono; last reflexivity.
      1,3: done. 1,2: lia.
      all: rewrite /array_tag_map -!insert_union_singleton_l.
      3: { eapply dom_agree_on_tag_upd_ne; last exact Htt5.
           intros <-. rewrite /tag_valid in Htt1; lia. }
      1-2: intros l sc (Mhl&H1%lookup_insert_Some&H2)%bind_Some;
           simpl in H1; destruct H1 as [([= Hl1]&<-)|(Hnel&Hlu)].
      1,3: subst t; rewrite /tag_valid in Htt2,Htt3; lia.
      * ospecialize (Htt3 l sc _).
        1: rewrite /heaplet_lookup Hlu /= H2 //.
        eapply loc_controlled_read_preserved_everywhere. 4: exact Hwf_mid_t. all: simpl. 2-3: done.
        1: rewrite -Hscs_eq; done. 1: done.
        eapply loc_controlled_create_child_preserved_everywhere. 5: exact Hwf_mid_t. 4: exact Hwf_t. all: simpl.
        1: rewrite Hscs_eq Hsnp_eq in Happly1_t; done. 1-2: done. 1-2: done.
        1: intros ->; rewrite /tag_valid in Htt1,Htt2; lia.
        1: intros ->; congruence. done.
      * ospecialize (Htt4 l sc _).
        1: rewrite /heaplet_lookup Hlu /= H2 //.
        eapply loc_controlled_read_preserved_everywhere. 4: exact Hwf_mid_s. all: simpl. 2-3: done.
        1: done. 1: done.
        eapply loc_controlled_create_child_preserved_everywhere. 5: exact Hwf_mid_s. 4: exact Hwf_s. all: simpl.
        1: done. 1-2: done. 1-2: done.
        1: intros ->; rewrite /tag_valid in Htt1,Htt2; lia.
        1: intros ->; congruence. done.
    + subst σ_t'; simpl. split_and!.
      3: { intros ->. destruct pk, im; done. }
      1-2: rewrite !Hsnp_eq /tag_valid; lia.
      all: rewrite /array_tag_map -!insert_union_singleton_l /=.
      3: { eapply dom_agree_on_tag_update_same. 2: eapply list_to_heaplet_dom_1; congruence.
           split; intros l [x (M&HM%mk_is_Some&HHM)%bind_Some]; simpl in HM.
           1: eapply Ht2 in HM. 2: eapply Ht3 in HM.
           all: rewrite Htagfresh in HM; by destruct HM. }
       1-2: intros l sc (Mhl&H1%lookup_insert_Some&H2)%bind_Some;
            simpl in H1; destruct H1 as [([= Hl1]&<-)|(Hne&Hlu)].
       * simpl in H2. eapply list_to_heaplet_lookup_Some in H2 as H2'.
         assert (∃ (i:nat), l.2 = l_s.2 + i) as (off&Hoff). 1: exists (Z.to_nat (l.2 - l_s.2)); lia.
         rewrite Hoff list_to_heaplet_nth -Hhpv_v_t in H2. 2: lia.
         rewrite -Hoff in H2. eapply loc_controlled_read_after_reborrow_creates.
         1: exact Happly1_t. 1: exact Happly2_t. 1-4,8-9: done.
         1: by rewrite Hsnp_eq. 2: lia. 1: destruct l as [l1 l2]; simpl in *; subst l1; done.
       * eapply mk_is_Some, Ht2 in Hlu. rewrite Htagfresh in Hlu. by destruct Hlu.
       * simpl in H2. eapply list_to_heaplet_lookup_Some in H2 as H2'.
         assert (∃ (i:nat), l.2 = l_s.2 + i) as (off&Hoff). 1: exists (Z.to_nat (l.2 - l_s.2)); lia.
         rewrite Hoff list_to_heaplet_nth -Hhpv_v_s in H2. 2: lia.
         rewrite -Hoff in H2. eapply loc_controlled_read_after_reborrow_creates.
         1: exact Happly1_s. 1: exact Happly2_s. 1-5,8-9: done.
         2: lia. 1: destruct l as [l1 l2]; simpl in *; subst l1; done.
       * eapply mk_is_Some, Ht3 in Hlu. rewrite Htagfresh in Hlu. by destruct Hlu.
  - (* source state wf *)
    iPureIntro. eapply retag_step_wf_inner in Hwf_s as (Hwf_s&Hccc). 2-5: done.
    eapply access_step_wf_inner in Hwf_s; done.
  - (* target state wf *)
    iPureIntro. subst σ_t'. eapply retag_step_wf_inner in Hwf_t as (Hwf_t&Hccc). 2-5: try done.
    2: by rewrite -Hscs_eq -Hsnp_eq. simpl in Hwf_t.
    eapply access_step_wf_inner in Hwf_t. 1: done. all: simpl.
    2: by rewrite -Hscs_eq. by rewrite Hsnp_eq.
Qed.


(** *** Retags with protectors *)
Fixpoint seq_loc_map {T} (l : loc) (n : nat) (iv : T) : gmap loc T :=
  match n with
  | O => ∅
  | S n => <[ l +ₗ n := iv ]> (seq_loc_map l n iv)
  end.
Lemma seq_loc_set_elem {T} l n l' (iv v : T) :
  seq_loc_map l n iv !! l' = Some v ↔ (∃ (i : nat), (i < n)%nat ∧ l' = l +ₗ i ∧ v = iv).
Proof.
  induction n as [ | n IH]; simpl. 2: split.
  - rewrite lookup_empty. split; first done. intros (i & Hi & _). lia.
  - intros [(<-&<-) | (Hne & (i & Hi & -> & ->)%IH)]%lookup_insert_Some;
     [exists n; naive_solver | exists i; naive_solver].
  - intros (i & Hi & -> & ->). destruct (decide (i = n)) as [-> | Hneq].
    1: by rewrite lookup_insert_eq.
    rewrite lookup_insert_ne. 1: apply IH; exists i; split; try done.
    1: lia. rewrite /shift_loc. intros [= H]. lia.
Qed.
Definition pointer_kind_to_access_ensuring (pk : pointer_kind) : access_ensuring := 
  match pk with
    Box => WeaklyNoChildren
  | _ => Strongly
  end.

Lemma sim_retag_fnentry sz l_t l_s ot c pk im tk M π Φ :
  pointer_kind_to_tag_protected pk im = Some tk →
  sc_rel (ScPtr l_t ot) (ScPtr l_s ot) -∗
  c @@ M -∗
  (∀ nt v_t v_s,
    ⌜l_t = l_s⌝ -∗
    ⌜length v_t = sz⌝ -∗ ⌜length v_s = sz⌝ -∗
    c @@ <[nt := seq_loc_map l_t sz (EnsuringAccess (pointer_kind_to_access_ensuring pk)) ]> M -∗
    value_rel v_t v_s -∗  (* as the pointers were public before *)
    nt $$ tk -∗
    l_t ↦t∗[tk]{nt} v_t -∗
    l_s ↦s∗[tk]{nt} v_s -∗
    #[ScPtr l_t nt] ⪯{π} #[ScPtr l_s nt] [{ Φ }]) -∗
  Retag #[ScPtr l_t ot] #[ScCallId c] pk im sz FnEntry ⪯{π} Retag #[ScPtr l_s ot] #[ScCallId c] pk im sz FnEntry [{ Φ }].
Proof.
  intros Htk. iIntros "#Hscrel Hprot Hsim".
  iApply sim_lift_base_step_both. iIntros (P_t P_s σ_t σ_s ??) "((HP_t & HP_s & Hbor) & %Hthread & %Hsafe)".
  (* exploit source to gain knowledge about stacks & that c is a valid id *)
  specialize (pool_safe_implies Hsafe Hthread) as (c' & ot' & l' & [= <- <-] & [= <-] & Hcin & Hotin & [HNone|(trs1 & trs2 &  Hntnin & Happly1_s & Happly2_s)]).
  { destruct pk, im; done. }
  iPoseProof "Hscrel" as "(-> & _ & Hotpub)". iClear "Hscrel".
  iPoseProof (bor_interp_get_pure with "Hbor") as "%Hp".
  destruct Hp as (Hstrs_eq & Hsnp_eq & Hsnc_eq & Hscs_eq & Hwf_s & Hwf_t & Hdom_eq).
  odestruct (trees_equal_create_child _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ Hstrs_eq Happly1_s) as (trs1_t&Happly1_t&Hstrs1_eq).
  1,3: eapply Hwf_s. 2: rewrite Hsnc_eq Hsnp_eq. 1,2: eapply Hwf_t. 1: by eapply Hwf_s.
  1-2: done.
  eapply retag_step_wf_inner in Hwf_s as X. 1: destruct X as (Hwf_mid_s&Hntinmid_s).
  2-5: done.
  eapply retag_step_wf_inner in Hwf_t as X. 1: destruct X as (Hwf_mid_t&_).
  5: by rewrite Hscs_eq Hsnp_eq in Happly1_t. 4: by rewrite -Hscs_eq. 2-3: setoid_rewrite <- trees_equal_same_tags; last done. 2: done. 2: by rewrite -Hsnp_eq.
  edestruct trees_equal_allows_more_access as (trs2_t&Happly2_t).
  1: exact Hstrs1_eq. 1: apply Hwf_mid_s. 1,2,3: rewrite ?Hscs_eq; apply Hwf_mid_t. 1: done. 1: done. 1: by eapply mk_is_Some.
  opose proof (trees_equal_preserved_by_access _ _ _ _ _ _ _ Hstrs1_eq _ Happly2_s Happly2_t) as Hstrs2_eq.
  1,3,5: eapply Hwf_mid_s. 1-3: rewrite ?Hscs_eq; eapply Hwf_mid_t. 1: done.

  odestruct (tree_access_succeeds_heap_value _ false) as (v_s&Hv_s).
  1: apply Hwf_mid_s. 2: eapply mk_is_Some, Happly2_s. 1: done. simpl in Hv_s.
  odestruct (tree_access_succeeds_heap_value _ false) as (v_t&Hv_t).
  1: apply Hwf_mid_t. 2: rewrite /= -Hscs_eq; eapply mk_is_Some, Happly2_t. 1: simpl; setoid_rewrite <- trees_equal_same_tags; try done. simpl in Hv_t.

  opose proof (state_wf_tree_unq _ Hwf_mid_t) as Hwf_trs1_t.
  opose proof (state_wf_tree_unq _ Hwf_mid_s) as Hwf_trs1_s.
  pose proof Hntinmid_s as Hntinmid_t.
  setoid_rewrite trees_equal_same_tags in Hntinmid_t. 2: done.
  clear Hstrs1_eq. (* TODO refactor the above into a separate lemma, maybe? *)

  iDestruct "Hbor" as "(%M_call & %M_tag & %M_t & %M_s & (Hc & Htag_auth & Htag_t_auth & Htag_s_auth) & Htainted & Hpub_cid & #Hsrel & %Hcall_interp & %Htag_interp & _ & _)".
  iDestruct (tkmap_lookup with "Htag_auth Hotpub") as "%Hotpub".
  assert (M_tag !! snp σ_s = None) as Htagfresh.
  { destruct (M_tag !! σ_s.(snp)) as [[x []]|] eqn:Heq; last done.
    destruct Htag_interp as (H1&_). specialize (H1 _ _ Heq) as (Hv&_).
    rewrite /tag_valid in Hv. lia. }
  iMod (tkmap_insert tk σ_s.(snp) tt with "Htag_auth") as "(Htag_auth&Htk)". 1: done.
  iDestruct (ghost_map_lookup with "Hc Hprot") as "%HM_call".
  destruct Hcall_interp as (Hcall_interp&Hcc2).
  assert (M !!  σ_s.(snp) = None) as HMfresh.
  { destruct (M !! σ_s.(snp)) eqn:HeqM; last done.
    destruct (Hcall_interp _ _ HM_call) as (_&H1).
    destruct (H1 _ _ HeqM) as (H2&_).
    rewrite Hsnp_eq /tag_valid /= in H2. lia. }
  iMod (ghost_map_update with "Hc Hprot") as "(Hc&Hprot)".
  iDestruct "Hsrel" as "(_&_&_&_&_&Hsrel)".
  eapply read_mem_values in Hv_s as (Hlen_v_s&Hhpv_v_s).
  eapply read_mem_values in Hv_t as (Hlen_v_t&Hhpv_v_t). rewrite /shift_loc /= in Hhpv_v_t, Hhpv_v_s.
  unshelve iSpecialize ("Hsim" $! σ_s.(snp) v_t v_s _ _ _ with "Hprot"). 1: done. 1-2: congruence.

  opose proof* create_then_access_implies_earlier_access_trees as Hvirtual_t.
  5: exact Happly2_t. 4: exact Happly1_t. 2-3: setoid_rewrite <- trees_equal_same_tags; first done; done. 1: apply Hwf_t.

  iAssert (value_rel v_t v_s)%I as "Hvalrel".
  { rewrite /value_rel /=. iApply big_sepL2_forall. iSplit; first (iPureIntro; congruence).
    iIntros (off vt vs Hvt Hvs).
    ospecialize (Hhpv_v_t off _). 1: rewrite -Hlen_v_t; by eapply lookup_lt_Some.
    ospecialize (Hhpv_v_s off _). 1: rewrite -Hlen_v_s; by eapply lookup_lt_Some.
    rewrite Hvt in Hhpv_v_t.
    iDestruct ("Hsrel" $! _ (mk_is_Some _ _ Hhpv_v_t)) as "[Hpub|(%t&%Hpriv)]".
    - iDestruct ("Hpub" $! _ Hhpv_v_t) as "(%sc_s&%Hsc_s&Hscrel)".
      rewrite Hsc_s Hvs in Hhpv_v_s. injection Hhpv_v_s as ->. done.
    - exfalso. rewrite Hscs_eq in Hvirtual_t.
      opose proof* priv_loc_access_must_use_same_tag as Heq.
      5: done. 3-4: done. 1-2: done. all: simpl. 3: exact Hvirtual_t.
      1: setoid_rewrite <- trees_equal_same_tags; first done; done.
      1: split; first lia. 1: rewrite -Hlen_v_t. 1: eapply lookup_lt_Some in Hvt; lia.
      subst t. destruct Hpriv as (tk'&Htk'&[vls Hhl]&[->|(cc&ae&->&Hcc)]). all: congruence. }
  iSpecialize ("Hsim" with "Hvalrel Htk").
  assert (M_t !! (snp σ_s, l_s.1) = None) as Hhl_t_None.
  { destruct Htag_interp as (_&H1&H2&_). destruct (M_t !! (snp σ_s, l_s.1)) eqn:Heq; last done.
    exfalso. specialize (H1 _ _ (mk_is_Some _ _ Heq)). rewrite Htagfresh in H1. by destruct H1. }
  iMod (ghost_map_array_tag_insert _ _ v_t σ_s.(snp) l_s tk with "Htag_t_auth") as "(Hpt&Htag_t_auth)"; first done.
  assert (M_s !! (snp σ_s, l_s.1) = None) as Hhl_s_None.
  { destruct Htag_interp as (_&H1&H2&_). destruct (M_s !! (snp σ_s, l_s.1)) eqn:Heq; last done.
    exfalso. specialize (H2 _ _ (mk_is_Some _ _ Heq)). rewrite Htagfresh in H2. by destruct H2. }
  iMod (ghost_map_array_tag_insert _ _ v_s σ_s.(snp) l_s tk with "Htag_s_auth") as "(Hps&Htag_s_auth)"; first done.
  iSpecialize ("Hsim" with "Hpt Hps").

  iModIntro. iSplit.
  { iPureIntro. do 3 eexists. econstructor; econstructor.
    1,3-5: repeat rewrite -?Hscs_eq -?Hsnp_eq //.
    all: setoid_rewrite <- trees_equal_same_tags; last done; done. }
  iIntros (e_t' efs_t σ_t') "%Hhead_t".
  opose proof* (head_retag_inv _ _ _ _ _ _ _ _ _ _ _ _ Hhead_t) as (->&Hcin_t&Hotin_t&[(Hnone&->&->)|(trsX1&trsX2&->&Hσ_t&Hntnin_t&HX1&HX2)]).
  { exfalso. by destruct pk, im. }
  assert (trsX1 = trs1_t) as -> by congruence. clear HX1.
  assert (trsX2 = trs2_t) as -> by congruence. clear HX2.

  iModIntro. iExists _, _, _. iSplit.
  { iPureIntro. simpl. econstructor; econstructor. all: done. }

  iFrame "HP_t HP_s". rewrite -Hsnp_eq. iFrame "Hsim". simpl.
  iSplit; last done.
  iExists _, _, _, _. rewrite /bor_interp_inner. iFrame "Htag_auth Htag_t_auth Htag_s_auth Hc". simpl.
  iSplitL "Htainted"; last iSplit; last iSplit; last iSplit; last iSplit; last iSplit.
  - iDestruct "Htainted" as "(%MX&Ht1&Ht2)". iExists MX. iFrame "Ht1".
    iIntros (t' l' Htl'). iDestruct ("Ht2" $! t' l' Htl') as "($&%Ht2)". iPureIntro.
    simpl. eapply disabled_tag_tree_apply_access_irreversible. 4: done. 2: done. 2: by eapply Hwf_mid_s.
    eapply disabled_tag_create_child_irreversible. 4: eapply Happly1_s. 2: done.
    + destruct Ht2 as (Hlt&Ht2); lia.
    + destruct Ht2 as (Hlt&Ht2); split; last done. lia.
  - iApply pub_cid_interp_preserve_sub. 5: iFrame.
    1,3: by subst σ_t'. all: done.
  - subst σ_t'. rewrite -Hsnp_eq. do 5 (iSplit; first done). simpl.
    iIntros (l Hl). iDestruct ("Hsrel" $! l Hl) as "[Hpub|(%t&%Hpriv)]".
    + iLeft. iApply "Hpub".
    + iRight. iExists t. iPureIntro. destruct Hpriv as (tk'&Htk'&Hhl&Htag).
      exists tk'. split. 1: rewrite lookup_insert_ne //. 1: intros <-; congruence.
      split. 1: rewrite /heaplet_lookup /= -?insert_union_singleton_l in Hhl|-*; rewrite lookup_insert_ne //; congruence.
      destruct Htag as [->|(cc&ae&->&Hin)]; first by left.
      right; exists cc, ae; split; first done.
      destruct Hin as (MM&HMM&Hin). destruct (decide (c = cc)) as [->|Hne].
      2: exists MM; by rewrite lookup_insert_ne.
      eexists. rewrite lookup_insert_eq; split; first done.
      assert (MM = M) as -> by congruence.
      destruct Hin as (L&HML&HL). exists L. split_and!; try done.
      rewrite lookup_insert_ne //. intros <-. congruence.
  - iPureIntro. subst σ_t'. split; last first.
    { intros ????? [(?&?)|(H1&H2)]%lookup_insert_Some [(?&?)|(H1'&H2')]%lookup_insert_Some; simplify_eq.
      1-3: rewrite !dom_insert_L.
      * done.
      * intros [->%elem_of_singleton|?]%elem_of_union HH.
        2: by eapply Hcc2. eapply elem_of_dom in HH as (Lx&HLx).
        specialize (Hcall_interp _ _ H2') as (_&Hx). specialize (Hx _ _ HLx) as (Hx&_).
        rewrite /tag_valid in Hx. lia.
      * intros HH [->%elem_of_singleton|?]%elem_of_union.
        2: by eapply Hcc2. eapply elem_of_dom in HH as (Lx&HLx).
        specialize (Hcall_interp _ _ H2) as (_&Hx). specialize (Hx _ _ HLx) as (Hx&_).
        rewrite /tag_valid in Hx. lia.
      * by eapply Hcc2. }
    intros cc M' [(<-&<-)|(Hne&HM')]%lookup_insert_Some.
    1: specialize (Hcall_interp _ _ HM_call) as (Hc1&Hc2).
    2: specialize (Hcall_interp _ _ HM') as (Hc1&Hc2).
    all: split; first done.
    all: intros tt L HL.
    1: eapply lookup_insert_Some in HL as [(<-&<-)|(HneL&HL)].
    { split; first (simpl; rewrite /tag_valid; lia).
      intros l ps (i&Hi&->&->)%seq_loc_set_elem.
      eapply tag_protected_preserved_by_access_init.
      2: exact Happly2_t. 2: rewrite Hscs_eq; apply Hc1. 1:eapply Hwf_trs1_t.
      assert (∃ it, (create_new_item (snp σ_s) pk im FnEntry c) = Some it) as (it&Hit).
      { eapply bind_Some in Happly1_t as (x1&Hx1&(x2&(x3&Hx3&_)%bind_Some&_)%bind_Some).
        by exists x3. }
      eenough (item_protected_for_noinit _ (tag_is_unq (<[snp σ_s:=(tk, ())]> M_tag) (array_tag_map l_s (snp σ_s) v_t ∪ M_t)) c it (l_s +ₗ i).1 (l_s +ₗ i).2 (EnsuringAccess (pointer_kind_to_access_ensuring pk))) as Hprot.
      - eexists. split; last exact Hprot.
        eapply bind_Some in Happly1_t as (tr&Htr&(tr2&Happ&[= <-])%bind_Some).
        exists tr2. rewrite /= lookup_insert_eq. split; first done.
        edestruct create_child_determined as (ix&Hix&HH). 4: { erewrite Hit in Hix; injection Hix as ->; apply HH. }
        3: done.
        all: rewrite /trees_contain /trees_at_block Htr // -Hsnp_eq // in Hotin_t, Hntnin_t.
      - eapply bind_Some in Hit as (p&Hp&[= <-]). split; first done.
        split; last first. 1: split_and!.
        2: { simpl. intros H. exfalso. eapply H. split_and!; try done.  all: lia. }
        2,3: rewrite /item_lookup lookup_empty /=; destruct pk, im; simpl in *; simplify_eq; done.
        all: destruct pk; try done. intros _. exists tk_res.
        cbv in Htk. injection Htk as <-. rewrite lookup_insert_eq /=. split; first done.
        rewrite /= /heaplet_lookup /= lookup_union /= /array_tag_map /= lookup_singleton_eq /= union_Some_l /= list_to_heaplet_nth.
        eapply lookup_lt_is_Some_2; by lia. }
    all: specialize (Hc2 tt L HL) as (Hc3&Hc4).
    all: split; [ simpl; eapply tag_valid_mono; first done; lia | ].
    all: intros l ps Hps; specialize (Hc4 l ps Hps).
    all: eapply (tag_protected_preserved_by_create ps ot (snp σ_s) pk im _ (scs σ_s)) in Hc4;
         [| | | exact Happly1_t]; [| eapply Hwf_t | intros <-; rewrite /tag_valid in Hc3; lia ].
    all: eapply tag_protected_preserved_by_access;
         [| exact Happly2_t | rewrite Hscs_eq; apply Hc1 | ]; first eapply Hwf_trs1_t.
    all: eapply tag_protected_for_mono; last exact Hc4.
    all: intros l'' it ? ? ? (tk'&Htk'&Hhl'); exists tk'; split; 
         [ rewrite lookup_insert_ne //; intros Heq; by rewrite -Heq Htagfresh in Htk' | ].
    all: rewrite /heaplet_lookup /= /array_tag_map /= lookup_union_r //.
    all: eapply not_elem_of_dom; rewrite dom_singleton_L; intros HH%elem_of_singleton.
    all: rewrite /heaplet_lookup /= HH /= Hhl_t_None /= in Hhl'; by destruct Hhl'.
  - iPureIntro. destruct Htag_interp as (Ht1&Ht2&Ht3&Ht4&Ht5).
    split_and!.
    2-5: rewrite /array_tag_map -!insert_union_singleton_l.
    2-3: intros t blk (x & [([= <- <-]&<-)|(?&?)]%lookup_insert_Some);
         [by rewrite lookup_insert_eq|eapply lookup_insert_is_Some'; right].
         2: eapply Ht2. 3: eapply Ht3. 2-3: by eapply mk_is_Some.
    2,3: intros tg l1 l2; rewrite !dom_insert_L;
         intros [[= Heq1 Heq2]%elem_of_singleton|H1%elem_of_dom]%elem_of_union;
         intros [[= Heq3 Heq4]%elem_of_singleton|H2%elem_of_dom]%elem_of_union; simplify_eq;
         [done|rename H2 into H1| | ].
         4: eapply Ht4; by eapply elem_of_dom.
         6: eapply Ht5; by eapply elem_of_dom.
         2,3: eapply Ht2 in H1. 4,5: eapply Ht3 in H1.
         2-5: rewrite Htagfresh in H1; by destruct H1.
    intros t tk' [(<-&[= <-])|(Hne&Hin)]%lookup_insert_Some; last first.
    + subst σ_t'. specialize (Ht1 _ _ Hin) as (Htt1&Htt2&Httlocal&Htt3&Htt4&Htt5).
      split_and!.
      3: { intros ->. rewrite /array_tag_map. destruct Httlocal as (Httl1&Httl2); first done.
           split;
           (intros bblk MM [([= <- <-]&<-)%lookup_singleton_Some|(_&H)]%lookup_union_Some_raw;
            [ done | (try by eapply Httl1); by eapply Httl2]). }
      1-2: simpl; eapply tag_valid_mono; last reflexivity.
      1,3: done. 1,2: lia.
      all: rewrite /array_tag_map -!insert_union_singleton_l.
      3: { eapply dom_agree_on_tag_upd_ne; last exact Htt5.
           intros <-. rewrite /tag_valid in Htt1; lia. }
      1-2: intros l sc (Mhl&H1%lookup_insert_Some&H2)%bind_Some;
           simpl in H1; destruct H1 as [([= Hl1]&<-)|(Hnel&Hlu)].
      1,3: subst t; rewrite /tag_valid in Htt2,Htt3; lia.
      * ospecialize (Htt3 l sc _).
        1: rewrite /heaplet_lookup Hlu /= H2 //.
        eapply loc_controlled_read_preserved_everywhere. 4: exact Hwf_mid_t. all: simpl. 2-3: done.
        1: rewrite -Hscs_eq; done. 1: done.
        eapply loc_controlled_create_child_preserved_everywhere. 5: exact Hwf_mid_t. 4: exact Hwf_t. all: simpl.
        1: rewrite Hscs_eq Hsnp_eq in Happly1_t; done. 1-2: done. 1-2: done.
        1: intros ->; rewrite /tag_valid in Htt1,Htt2; lia.
        1: intros ->; congruence.
        eapply loc_controlled_ext. all: done.
      * ospecialize (Htt4 l sc _).
        1: rewrite /heaplet_lookup Hlu /= H2 //.
        eapply loc_controlled_read_preserved_everywhere. 4: exact Hwf_mid_s. all: simpl. 2-3: done.
        1: done. 1: done.
        eapply loc_controlled_create_child_preserved_everywhere. 5: exact Hwf_mid_s. 4: exact Hwf_s. all: simpl.
        1: done. 1-2: done. 1-2: done.
        1: intros ->; rewrite /tag_valid in Htt1,Htt2; lia.
        1: intros ->; congruence.
        eapply loc_controlled_ext. all: done.
    + subst σ_t'; simpl. split_and!.
      3: { intros ->. destruct pk, im; done. }
      1-2: rewrite !Hsnp_eq /tag_valid; lia.
      all: rewrite /array_tag_map -!insert_union_singleton_l /=.
      3: { eapply dom_agree_on_tag_update_same. 2: eapply list_to_heaplet_dom_1; congruence.
           split; intros l [x (M'&HM%mk_is_Some&HHM)%bind_Some]; simpl in HM.
           1: eapply Ht2 in HM. 2: eapply Ht3 in HM.
           all: rewrite Htagfresh in HM; by destruct HM. }
       1-2: intros l sc (Mhl&H1%lookup_insert_Some&H2)%bind_Some;
            simpl in H1; destruct H1 as [([= Hl1]&<-)|(Hne&Hlu)].
       * simpl in H2. eapply list_to_heaplet_lookup_Some in H2 as H2'.
         assert (∃ (i:nat), l.2 = l_s.2 + i) as (off&Hoff). 1: exists (Z.to_nat (l.2 - l_s.2)); lia.
         rewrite Hoff list_to_heaplet_nth -Hhpv_v_t in H2. 2: lia.
         rewrite -Hoff in H2. eapply loc_controlled_read_after_reborrow_creates.
         1: exact Happly1_t. 1: exact Happly2_t. 1-4,8: done.
         1: by rewrite Hsnp_eq. 2: lia. 1: destruct l as [l1 l2]; simpl in *; subst l1; done.
         rewrite -Htk. by destruct pk, im.
       * eapply mk_is_Some, Ht2 in Hlu. rewrite Htagfresh in Hlu. by destruct Hlu.
       * simpl in H2. eapply list_to_heaplet_lookup_Some in H2 as H2'.
         assert (∃ (i:nat), l.2 = l_s.2 + i) as (off&Hoff). 1: exists (Z.to_nat (l.2 - l_s.2)); lia.
         rewrite Hoff list_to_heaplet_nth -Hhpv_v_s in H2. 2: lia.
         rewrite -Hoff in H2. eapply loc_controlled_read_after_reborrow_creates.
         1: exact Happly1_s. 1: exact Happly2_s. 1-5,8: done.
         2: lia. 1: destruct l as [l1 l2]; simpl in *; subst l1; done.
         rewrite -Htk. by destruct pk, im.
       * eapply mk_is_Some, Ht3 in Hlu. rewrite Htagfresh in Hlu. by destruct Hlu.
  - (* source state wf *)
    iPureIntro. eapply retag_step_wf_inner in Hwf_s as (Hwf_s&Hccc). 2-5: done.
    eapply access_step_wf_inner in Hwf_s; done.
  - (* target state wf *)
    iPureIntro. subst σ_t'. eapply retag_step_wf_inner in Hwf_t as (Hwf_t&Hccc). 2-5: try done.
    2: by rewrite -Hscs_eq -Hsnp_eq. simpl in Hwf_t.
    eapply access_step_wf_inner in Hwf_t. 1: done. all: simpl.
    2: by rewrite -Hscs_eq. by rewrite Hsnp_eq.
Qed.


(** *** General tk_pub retag *)

Lemma sim_retag_public sz l_t l_s ot os c pk im rk π Φ :
  value_rel [ScPtr l_t ot] [ScPtr l_s os] -∗
  (∀ nt, value_rel [ScPtr l_t nt] [ScPtr l_s nt] -∗
    #[ScPtr l_t nt] ⪯{π} #[ScPtr l_s nt] [{ Φ }]) -∗
  Retag #[ScPtr l_t ot] #[ScCallId c] pk im sz rk ⪯{π} Retag #[ScPtr l_s ot] #[ScCallId c] pk im sz rk [{ Φ }].
Proof.
  rewrite {1 2}/value_rel big_sepL2_singleton.
  iIntros "#Hscrel Hsim". 
  iApply sim_lift_base_step_both. iIntros (P_t P_s σ_t σ_s ??) "((HP_t & HP_s & Hbor) & %Hthread & %Hsafe)".
  (* exploit source to gain knowledge about stacks & that c is a valid id *)
  specialize (pool_safe_implies Hsafe Hthread) as (c' & ot' & l' & [= <- <-] & [= <-] & Hcin & Hotin & [HNone|(trs1 & trs2 &  Hntnin & Happly1_s & Happly2_s)]).
  { exfalso; destruct pk, im, rk; try done. }
  iPoseProof "Hscrel" as "(-> & -> & Hotpub)". iClear "Hscrel".
  iPoseProof (bor_interp_get_pure with "Hbor") as "%Hp".
  destruct Hp as (Hstrs_eq & Hsnp_eq & Hsnc_eq & Hscs_eq & Hwf_s & Hwf_t & Hdom_eq).
  odestruct (trees_equal_create_child _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ Hstrs_eq Happly1_s) as (trs1_t&Happly1_t&Hstrs1_eq).
  1,3: eapply Hwf_s. 2: rewrite Hsnc_eq Hsnp_eq. 1,2: eapply Hwf_t. 1: by eapply Hwf_s.
  1-2: done.
  eapply retag_step_wf_inner in Hwf_s as X. 1: destruct X as (Hwf_mid_s&Hntinmid_s).
  2-5: done.
  eapply retag_step_wf_inner in Hwf_t as X. 1: destruct X as (Hwf_mid_t&_).
  5: by rewrite Hscs_eq Hsnp_eq in Happly1_t. 4: by rewrite -Hscs_eq. 2-3: setoid_rewrite <- trees_equal_same_tags; last done. 2: done. 2: by rewrite -Hsnp_eq.
  edestruct trees_equal_allows_more_access as (trs2_t&Happly2_t).
  1: exact Hstrs1_eq. 1: apply Hwf_mid_s. 1,2,3: rewrite ?Hscs_eq; apply Hwf_mid_t. 1: done. 1: done. 1: by eapply mk_is_Some.
  opose proof (trees_equal_preserved_by_access _ _ _ _ _ _ _ Hstrs1_eq _ Happly2_s Happly2_t) as Hstrs2_eq.
  1,3,5: eapply Hwf_mid_s. 1-3: rewrite ?Hscs_eq; eapply Hwf_mid_t. 1: done.

  odestruct (tree_access_succeeds_heap_value _ false) as (v_s&Hv_s).
  1: apply Hwf_mid_s. 2: eapply mk_is_Some, Happly2_s. 1: done. simpl in Hv_s.
  odestruct (tree_access_succeeds_heap_value _ false) as (v_t&Hv_t).
  1: apply Hwf_mid_t. 2: rewrite /= -Hscs_eq; eapply mk_is_Some, Happly2_t. 1: simpl; setoid_rewrite <- trees_equal_same_tags; try done. simpl in Hv_t.

  opose proof (state_wf_tree_unq _ Hwf_mid_t) as Hwf_trs1_t.
  opose proof (state_wf_tree_unq _ Hwf_mid_s) as Hwf_trs1_s.
  pose proof Hntinmid_s as Hntinmid_t.
  setoid_rewrite trees_equal_same_tags in Hntinmid_t. 2: done.
  clear Hstrs1_eq. (* TODO refactor the above into a separate lemma, maybe? *)

  iDestruct "Hbor" as "(%M_call & %M_tag & %M_t & %M_s & (Hc & Htag_auth & Htag_t_auth & Htag_s_auth) & Htainted & Hpub_cid & #Hsrel & %Hcall_interp & %Htag_interp & _ & _)".
  iDestruct (tkmap_lookup with "Htag_auth Hotpub") as "%Hotpub".
  assert (M_tag !! snp σ_s = None) as Htagfresh.
  { destruct (M_tag !! σ_s.(snp)) as [[x []]|] eqn:Heq; last done.
    destruct Htag_interp as (H1&_). specialize (H1 _ _ Heq) as (Hv&_).
    rewrite /tag_valid in Hv. lia. }
  iMod (tkmap_insert tk_pub σ_s.(snp) tt with "Htag_auth") as "(Htag_auth&#Htk)". 1: done.
  iDestruct "Hsrel" as "(_&_&_&_&_&Hsrel)".
  eapply read_mem_values in Hv_s as (Hlen_v_s&Hhpv_v_s).
  eapply read_mem_values in Hv_t as (Hlen_v_t&Hhpv_v_t). rewrite /shift_loc /= in Hhpv_v_t, Hhpv_v_s.
  unshelve iSpecialize ("Hsim" $! σ_s.(snp) with "[]").
  { simpl. iFrame "Htk". done. }

  opose proof* create_then_access_implies_earlier_access_trees as Hvirtual_t.
  5: exact Happly2_t. 4: exact Happly1_t. 2-3: setoid_rewrite <- trees_equal_same_tags; first done; done. 1: apply Hwf_t.

  iAssert (value_rel v_t v_s)%I as "Hvalrel".
  { rewrite /value_rel /=. iApply big_sepL2_forall. iSplit; first (iPureIntro; congruence).
    iIntros (off vt vs Hvt Hvs).
    ospecialize (Hhpv_v_t off _). 1: rewrite -Hlen_v_t; by eapply lookup_lt_Some.
    ospecialize (Hhpv_v_s off _). 1: rewrite -Hlen_v_s; by eapply lookup_lt_Some.
    rewrite Hvt in Hhpv_v_t.
    iDestruct ("Hsrel" $! _ (mk_is_Some _ _ Hhpv_v_t)) as "[Hpub|(%t&%Hpriv)]".
    - iDestruct ("Hpub" $! _ Hhpv_v_t) as "(%sc_s&%Hsc_s&Hscrel)".
      rewrite Hsc_s Hvs in Hhpv_v_s. injection Hhpv_v_s as ->. done.
    - exfalso. rewrite Hscs_eq in Hvirtual_t.
      opose proof* priv_loc_access_must_use_same_tag as Heq.
      5: done. 3-4: done. 1-2: done. all: simpl. 3: exact Hvirtual_t.
      1: setoid_rewrite <- trees_equal_same_tags; first done; done.
      1: split; first lia. 1: rewrite -Hlen_v_t. 1: eapply lookup_lt_Some in Hvt; lia. 
      subst t. destruct Hpriv as (tk'&Htk'&[vls Hhl]&[->|(cc&ae&->&Hcc)]). all: congruence. }

  assert (M_t !! (snp σ_s, l_s.1) = None) as Hhl_t_None.
  { destruct Htag_interp as (_&H1&H2&_). destruct (M_t !! (snp σ_s, l_s.1)) eqn:Heq; last done.
    exfalso. specialize (H1 _ _ (mk_is_Some _ _ Heq)). rewrite Htagfresh in H1. by destruct H1. }
  assert (M_s !! (snp σ_s, l_s.1) = None) as Hhl_s_None.
  { destruct Htag_interp as (_&H1&H2&_). destruct (M_s !! (snp σ_s, l_s.1)) eqn:Heq; last done.
    exfalso. specialize (H2 _ _ (mk_is_Some _ _ Heq)). rewrite Htagfresh in H2. by destruct H2. }

  iModIntro. iSplit.
  { iPureIntro. do 3 eexists. econstructor; econstructor.
    1,3-5: repeat rewrite -?Hscs_eq -?Hsnp_eq //.
    all: setoid_rewrite <- trees_equal_same_tags; last done; done. }
  iIntros (e_t' efs_t σ_t') "%Hhead_t".
  opose proof* (head_retag_inv _ _ _ _ _ _ _ _ _ _ _ _ Hhead_t) as (->&Hcin_t&Hotin_t&[(Hnone&->&->)|(trsX1&trsX2&->&Hσ_t&Hntnin_t&HX1&HX2)]).
  { exfalso; destruct pk, im, rk; try done. all: by eapply Hneim. }
  assert (trsX1 = trs1_t) as -> by congruence. clear HX1.
  assert (trsX2 = trs2_t) as -> by congruence. clear HX2.

  iModIntro. iExists _, _, _. iSplit.
  { iPureIntro. simpl. econstructor; econstructor. all: done. }

  iFrame "HP_t HP_s". rewrite -Hsnp_eq. iFrame "Hsim". simpl.
  iSplit; last done.
  iExists _, _, _, _. rewrite /bor_interp_inner. iFrame "Htag_auth Htag_t_auth Htag_s_auth Hc". simpl.
  iSplitL "Htainted"; last iSplit; last iSplit; last iSplit; last iSplit; last iSplit.
  - iDestruct "Htainted" as "(%M&Ht1&Ht2)". iExists M. iFrame "Ht1".
    iIntros (t' l' Htl'). iDestruct ("Ht2" $! t' l' Htl') as "($&%Ht2)". iPureIntro.
    simpl. eapply disabled_tag_tree_apply_access_irreversible. 4: done. 2: done. 2: by eapply Hwf_mid_s.
    eapply disabled_tag_create_child_irreversible. 4: eapply Happly1_s. 2: done.
    + destruct Ht2 as (Hlt&Ht2); lia.
    + destruct Ht2 as (Hlt&Ht2); split; last done. lia.
  - iApply pub_cid_interp_preserve_sub. 5: iFrame.
    1,3: by subst σ_t'. all: done.
  - subst σ_t'. rewrite -Hsnp_eq. do 5 (iSplit; first done). simpl.
    iIntros (l Hl). iDestruct ("Hsrel" $! l Hl) as "[Hpub|(%t&%Hpriv)]".
    + iLeft. iApply "Hpub".
    + iRight. iExists t. iPureIntro. destruct Hpriv as (tk'&Htk'&Hhl&Htag).
      exists tk'. split. 1: rewrite lookup_insert_ne //. 1: intros <-; congruence.
      split; first done.
      apply Htag.
  - iPureIntro. subst σ_t'. destruct Hcall_interp as (Hcall_interp&Hcc2). split; last first. 1: done.
    intros cc M' HM'. specialize (Hcall_interp cc M' HM') as (Hc1&Hc2). simpl.
    split; first done. intros tt L HL. specialize (Hc2 tt L HL) as (Hc3&Hc4).
    split. 1: eapply tag_valid_mono; first done; lia.
    intros l ps Hps. specialize (Hc4 l ps Hps).
    eapply (tag_protected_preserved_by_create ps os (snp σ_s) pk im rk (scs σ_s)) in Hc4.
    4: exact Happly1_t. 2: eapply Hwf_t. 2: { intros <-. rewrite /tag_valid in Hc3. lia. }
    eapply tag_protected_preserved_by_access.
    2: exact Happly2_t. 2: rewrite Hscs_eq; apply Hc1. 1: eapply Hwf_trs1_t.
    eapply tag_protected_for_mono. 2: exact Hc4.
    intros l'' it ? ? ? (tk&Htk&Hhl). exists tk. split; last done.
    rewrite lookup_insert_ne //. intros Heq.
    by rewrite -Heq Htagfresh in Htk.
  - iPureIntro. destruct Htag_interp as (Ht1&Ht2&Ht3&Ht4&Ht5).
    split_and!.
    4-5: done.
    2-3: intros t blk Hin; eapply lookup_insert_is_Some'; right.
         2: by eapply Ht2. 2: by eapply Ht3.
    intros t tk' [(<-&[= <-])|(Hne&Hin)]%lookup_insert_Some; last first.
    + subst σ_t'. specialize (Ht1 _ _ Hin) as (Htt1&Htt2&Httlocal&Htt3&Htt4&Htt5).
      split_and!.
      3: done. (* intros ->. split; intros bblk H.
           all: simpl; eapply apply_within_trees_tag_count_preserves_exists.
           1,4: done. 1,3: eapply memory_access_tag_count.
           all: eapply create_child_tree_contains.
           2, 4: done. all: by eapply Httlocal. } *)
      1-2: simpl; eapply tag_valid_mono; last reflexivity.
      1,3: done. 1,2: lia. 3: done.
      1-2: intros l sc Hhl.
      * ospecialize (Htt3 l sc Hhl).
        eapply loc_controlled_read_preserved_everywhere. 4: exact Hwf_mid_t. all: simpl. 2-3: done.
        1: rewrite -Hscs_eq; done. 1: done.
        eapply loc_controlled_create_child_preserved_everywhere. 5: exact Hwf_mid_t. 4: exact Hwf_t. all: simpl.
        1: rewrite Hscs_eq Hsnp_eq in Happly1_t; done. 1-2: done. 1-2: done.
        1: intros ->; rewrite /tag_valid in Htt1,Htt2; lia.
        1: intros ->; congruence. done.
      * ospecialize (Htt4 l sc Hhl).
        eapply loc_controlled_read_preserved_everywhere. 4: exact Hwf_mid_s. all: simpl. 2-3: done.
        1: done. 1: done.
        eapply loc_controlled_create_child_preserved_everywhere. 5: exact Hwf_mid_s. 4: exact Hwf_s. all: simpl.
        1: done. 1-2: done. 1-2: done.
        1: intros ->; rewrite /tag_valid in Htt1,Htt2; lia.
        1: intros ->; congruence. done.
    + subst σ_t'; simpl. split_and!.
      3: done.
      1-2: rewrite !Hsnp_eq /tag_valid; lia.
      3: { split; intros l [x (M&HM%mk_is_Some&HHM)%bind_Some]; simpl in HM.
           1: eapply Ht2 in HM. 2: eapply Ht3 in HM.
           all: rewrite Htagfresh in HM; by destruct HM. }
       1-2: intros l sc (Mhl&H1%mk_is_Some&H2)%bind_Some; exfalso; simpl in *.
       * specialize (Ht2 _ _ H1). rewrite Htagfresh in Ht2; by destruct Ht2.
       * specialize (Ht3 _ _ H1). rewrite Htagfresh in Ht3; by destruct Ht3.
  - (* source state wf *)
    iPureIntro. eapply retag_step_wf_inner in Hwf_s as (Hwf_s&Hccc). 2-5: done.
    eapply access_step_wf_inner in Hwf_s; done.
  - (* target state wf *)
    iPureIntro. subst σ_t'. eapply retag_step_wf_inner in Hwf_t as (Hwf_t&Hccc). 2-5: try done.
    2: by rewrite -Hscs_eq -Hsnp_eq. simpl in Hwf_t.
    eapply access_step_wf_inner in Hwf_t. 1: done. all: simpl.
    2: by rewrite -Hscs_eq. by rewrite Hsnp_eq.
Qed.

End lifting.


