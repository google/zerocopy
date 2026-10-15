From iris.proofmode Require Export proofmode.
From iris.bi.lib Require Import fractional.
From iris.base_logic.lib Require Import ghost_map.
From simuliris.base_logic Require Export gen_sim_prog.
From simuliris.simulation Require Export slsls gen_log_rel.
From simuliris.simulation Require Import lifting.
From simuliris.tree_borrows Require Import tkmap_view.
From simuliris.tree_borrows Require Export defs.
From simuliris.tree_borrows Require Export steps_wf.
From simuliris.tree_borrows Require Import steps_progress.
From simuliris.tree_borrows.trees_equal Require Import disabled_in_practice random_lemmas.

Section disabled_tag_rejects_reads_precisely.

  Context (C : call_id_set).



  Lemma pseudo_disabled_no_child_access tr acc tg_acc it_wit l b range lp :
    wf_tree tr →
    range'_contains range l →
    ParentChildIn (itag it_wit) tg_acc tr →
    tree_lookup tr (itag it_wit) it_wit →
    item_lookup it_wit l = mkPerm PermLazy lp →
    pseudo_disabled C tr (itag it_wit) l lp (iprot it_wit) →
    memory_access_maybe_nonchildren_only b acc C tg_acc range tr = None.
  Proof.
    intros Hwf Hrange HPCI Hlookup Hitlookup Hdis.
    inversion Hdis as [px Hreallydis Hpx|tg_cs it_cs lpx prx Hrelcs Hlucs Hprotcs Hitlucs HIMcs]; simplify_eq.
    - destruct (memory_access_maybe_nonchildren_only b acc C tg_acc range tr) as [tr'|] eqn: Hc; last done.
      exfalso. eapply apply_access_spec_per_node in Hc as (it'&Hit'&Hitlookup2).
      2-3: apply Hlookup.
      eapply eq_sym, mk_is_Some in Hit'.
      rewrite /rel_dec decide_True // in Hit'.
      rewrite /item_apply_access in Hit'.
      setoid_rewrite is_Some_ignore_bind in Hit'.
      setoid_rewrite <- mem_apply_range'_success_condition in Hit'.
      specialize (Hit' _ Hrange).
      erewrite maybe_non_children_only_no_effect in Hit'. 2: by intros ??.
      rewrite /item_lookup in Hitlookup.
      rewrite Hitlookup in Hit'. destruct acc; rewrite /apply_access_perm /apply_access_perm_inner /= in Hit'; by destruct Hit'.
    - destruct (memory_access_maybe_nonchildren_only b acc C tg_acc range tr) as [tr'|] eqn: Hc; last done.
      exfalso. eapply apply_access_spec_per_node in Hc as (it'&Hit'&Hitlookup2).
      2-3: apply Hlucs.
      eapply eq_sym, mk_is_Some in Hit'.
      enough (rel_dec tr tg_acc (itag it_cs) = Foreign Cousin) as Hfgn.
      { rewrite Hfgn in Hit'.
        rewrite /item_apply_access in Hit'.
        setoid_rewrite is_Some_ignore_bind in Hit'.
        setoid_rewrite <- mem_apply_range'_success_condition in Hit'.
        specialize (Hit' _ Hrange).
        erewrite maybe_non_children_only_no_effect in Hit'. 2: by intros ??.
        rewrite bool_decide_eq_true_2 // in Hit'.
        rewrite /item_lookup in Hitlucs.
        rewrite Hitlucs in Hit'. destruct acc; rewrite /apply_access_perm /apply_access_perm_inner /= in Hit'; by destruct Hit'. }
      eapply tree_lookup_correct_tag in Hlucs as Htg; subst tg_cs.
      rewrite /rel_dec. rewrite decide_False.
      2: { intros HPCI2. eapply cousins_have_disjoint_children. 4: exact Hrelcs. 4: exact HPCI. 4: done.
           all: eapply Hwf. 2: apply Hlookup. 2: apply Hlucs. eapply contains_child; first exact HPCI. apply Hlookup. }
      rewrite decide_False //.
      intros HPCI2.
      rewrite /rel_dec in Hrelcs.
      destruct decide as [Hd1|Hd2] in Hrelcs; try done.
      rewrite decide_True // in Hrelcs.
      eapply ParentChild_transitive. 1: exact HPCI. done.
  Qed.

  Lemma is_disabled_no_child_access tr acc tg_acc tg_wit it_wit l b range :
    wf_tree tr →
    range'_contains range l →
    ParentChildIn tg_wit tg_acc tr →
    tree_lookup tr tg_wit it_wit →
    is_disabled C tr tg_wit l (item_lookup it_wit l) (iprot it_wit) →
    memory_access_maybe_nonchildren_only b acc C tg_acc range tr = None.
  Proof.
    intros Hwf Hrange HPCI Hlookup Hdis.
    eapply tree_lookup_correct_tag in Hlookup as Htg; subst tg_wit.
    inversion Hdis as [px Hreallydis Hpx|lp prot Hpseudo Hlookup2 Hpx].
    - destruct (memory_access_maybe_nonchildren_only b acc C tg_acc range tr) as [tr'|] eqn: Hc; last done.
      exfalso. eapply apply_access_spec_per_node in Hc as (it'&Hit'&Hitlookup).
      2-3: apply Hlookup.
      eapply eq_sym, mk_is_Some in Hit'.
      rewrite /rel_dec decide_True // in Hit'.
      rewrite /item_apply_access in Hit'.
      setoid_rewrite is_Some_ignore_bind in Hit'.
      setoid_rewrite <- mem_apply_range'_success_condition in Hit'.
      specialize (Hit' _ Hrange).
      erewrite maybe_non_children_only_no_effect in Hit'. 2: by intros ??.
      rewrite /item_lookup in Hreallydis.
      rewrite -Hreallydis in Hit'. destruct acc; rewrite /apply_access_perm /apply_access_perm_inner /= in Hit'; by destruct Hit'.
    - eapply pseudo_disabled_no_child_access. 6: done. all: done.
  Qed.

  Lemma disabled_in_practice_no_access tr acc tg_wit tg l b range :
    wf_tree tr →
    range'_contains range l →
    disabled_in_practice C tr tg tg_wit l →
    memory_access_maybe_nonchildren_only b acc C tg range tr = None.
  Proof.
    intros Hwf Hrange Hdis.
    induction Hdis as [it_witness incl H1 H2 H3].
    eapply is_disabled_no_child_access. 1: done. 1: exact Hrange. 3: done. 2: done.
    rewrite /rel_dec in H1. destruct decide; done.
  Qed.

  Lemma disabled_tag_no_access b tr acc tg l range :
    wf_tree tr →
    disabled_tag_at C tr tg l →
    range'_contains range l →
    memory_access_maybe_nonchildren_only b acc C tg range tr = None.
  Proof.
    intros Hwf (wit&Hwit) Hrange.
    by eapply disabled_in_practice_no_access.
  Qed.

  Lemma read_fails_disabled_tag_or_prot_act_child b tg ittg range tr :
    wf_tree tr →
    protected_parents_not_disabled C tr →
    no_active_cousins C tr →
    tree_lookup tr tg ittg →
    (* ReservedIM and Cell can be temporarily disabled, we can not handle this *)
    (∀ l, range'_contains range l → perm (item_lookup ittg l) ≠ ReservedIM ∧ perm (item_lookup ittg l) ≠ Cell) →
    memory_access_maybe_nonchildren_only b AccessRead C tg range tr = None →
    ∃ l, range'_contains range l ∧ (disabled_tag_at C tr tg l ∨
         (* we never have things that have active children, so this case will be contradictory *)
         (active_child C tr tg l ∧ b = false)).
  Proof.
    intros Hwf Hndis Hnac Hittg HNoIM HNone.
    eapply apply_access_fail_condition in HNone.
    eapply exists_node_eqv_existential in HNone as (it&Hexit&HNone).
    eapply exists_node_to_tree_lookup in Hexit as Hit. 2: apply Hwf.
    rewrite /item_apply_access in HNone.
    rewrite /permissions_apply_range' in HNone.
    eapply bind_None in HNone as [HNone|(x&Hx&HHx)]. 2: done.
    eapply mem_apply_range'_fail_condition in HNone as (l&Hl&Hll).
    specialize (Hndis (itag it)). setoid_rewrite every_child_ParentChildIn in Hndis. 2: eapply Hwf.
    2: eapply Hwf, Hit.
    ospecialize (Hndis l it _ (itag it) _ _). 1: apply Hit. 2: left; done. 1: eapply Hwf, Hit.
    eapply every_node_iff_every_lookup in Hndis. 2: { intros x Hx%Hwf. by eapply unique_lookup. }
    2: apply Hit. specialize (Hndis eq_refl).
    exists l. split; first done.
    rewrite /item_protected_all_parents_not_disabled in Hndis.
    destruct (rel_dec tr tg (itag it)) as [[ii|]|] eqn:Hreldec.
    - destruct b; first done.
      change (default _ _) with (item_lookup it l) in Hll.
      right. split; last done. exists it, ii.
      destruct (item_lookup it l) as [ini pp]. simpl in *.
      split; first done.
      rewrite rel_dec_flip2 Hreldec /=. split; first done.
      rewrite /= in Hll.
      destruct ini, pp as [|[]| | | |], (bool_decide (protector_is_active (iprot it) C)) eqn:Hbd; simpl in *; try done.
      2: { exfalso. ospecialize (Hndis eq_refl _). 1: by eapply bool_decide_eq_true_1. by destruct Hndis. }
      split; first done.
      eapply bool_decide_eq_true_1; done.
    - rewrite maybe_non_children_only_no_effect in Hll. 2: done.
      change (default _ _) with (item_lookup it l) in Hll.
      left. exists tg. econstructor. 1: by rewrite rel_dec_refl.
      1: exact Hittg.
      ospecialize (Hnac _ _ _ _ l Hittg Hit Hreldec).
      rewrite bool_decide_decide in Hll. destruct (item_lookup it l) as [[] [|[]| | | |]] eqn:Heqitl, (decide (protector_is_active (iprot it) C)) as [Hp|].
      all: simpl in Hll; try discriminate Hll.
      2: by destruct (Hndis eq_refl Hp).
      destruct (item_lookup ittg l) as [ini prm] eqn:Heq.
      destruct ini.
      { destruct prm as [|[]| | | |].
        7: econstructor.
        all: (ospecialize (Hnac _ eq_refl); last done).
        2,3,6: right; rewrite Heq; split; last done; simpl; eauto.
        3: left; rewrite Heq; done.
        all: exfalso; specialize (HNoIM l Hl); rewrite Heq in HNoIM.
        all: by destruct HNoIM. }
      econstructor.
      econstructor. 1: exact Hreldec. 1: done. 1: done. 1: done.
      all: intros ->; specialize (HNoIM l Hl); rewrite Heq in HNoIM; by destruct HNoIM.
    - left. exists (itag it). econstructor. 1: exact Hreldec. 1: done.
      rewrite maybe_non_children_only_no_effect in Hll. 2: done.
      change (default _ _) with (item_lookup it l) in Hll.
      destruct (item_lookup it l) as [ini [|[]| | | |]] eqn:Heqitl.
      1-6: rewrite /apply_access_perm /apply_access_perm_inner /= most_init_comm /= Tauto.if_same /= // in Hll.
      destruct ini. 1: econstructor 1.
      econstructor 2. econstructor 1.
  Qed.

End disabled_tag_rejects_reads_precisely.