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
From simuliris.tree_borrows.trees_equal Require Import trees_equal_base random_lemmas.

Section utils.

Context (C : call_id_set).

  Lemma create_child_irreversible
    {tr tr' tg tg_old tg_new it pk im rk cid}
    (Lookup : tree_lookup tr tg it)
    (Fresh : tg_new ≠ tg)
    (Ins : create_child C tg_old tg_new pk im rk cid tr = Some tr')
    : tree_lookup tr' tg it.
  Proof.
    pose proof Ins as (x&<-%new_item_has_tag&[= <-])%bind_Some.
    destruct Lookup as [Ex Det]. split.
    - apply insert_preserves_exists; assumption.
    - apply insert_true_preserves_every; last assumption.
      intro SameTg. done.
  Qed.

  Lemma disabled_in_practice_create_child_irreversible
    {tr tr' tg tg_old tg_new pk im rk cid witness loc}
    (Ne : tg_new ≠ tg)
    (Ne' : tg_new ≠ witness)
    (Nc : ¬ tree_contains tg_new tr)
    (Dis : disabled_in_practice C tr tg witness loc)
    (Ins : create_child C tg_old tg_new pk im rk cid tr = Some tr')
    : disabled_in_practice C tr' tg witness loc.
  Proof.
    inversion Dis as [it_witness ? Rel Lookup Perm].
    econstructor.
    - erewrite <-create_child_same_rel_dec. 1: exact Rel. 3: done. 1-2: done.
    - eapply create_child_irreversible.
      1: done. 2: done. done.
    - inversion Perm as [|lp X H1 H2 X2]; simplify_eq. 1: econstructor 1.
      econstructor 2. inversion H1 as [|tgcs itcs X1 X2 H1' H2' H3 H4 H5 X3 X4]; simplify_eq. 1: econstructor 1.
      destruct (decide (tgcs = tg_new)) as [->|Hne].
      { exfalso. eapply Nc, H2'. }
      econstructor 2. 
      + erewrite <-create_child_same_rel_dec. 1: exact H1'. 3: done. 1-2: done.
      + eapply create_child_irreversible. 1: exact H2'. 2: done. done.
      + done.
      + done.
      + done.
      + done.
  Qed.

  Definition disabled_tag_at_create_child_irreversible
    {tr tr' tg tg_old tg_new pk im rk cid loc}
    (Ne : tg_new ≠ tg)
    (Nc : ¬ tree_contains tg_new tr)
    (Dis : disabled_tag_at C tr tg loc)
    (Ins : create_child C tg_old tg_new pk im rk cid tr = Some tr')
    : disabled_tag_at C tr' tg loc.
  Proof.
    destruct Dis as (w&Dis).
    exists w. eapply disabled_in_practice_create_child_irreversible; last done. all: try done.
    intros ->. inversion Dis as [H1 H2 H3 H4].
    apply Nc, H4.
  Qed.

  Definition disabled_tag_create_child_irreversible
    {trs trs' : trees} { blk tg tg_old tg_new pk im rk cid l nxtp}
    (Ne : tg_new ≠ tg)
    (Nc : ¬ trees_contain tg_new trs blk )
    (Dis : disabled_tag C trs nxtp tg l)
    (Ins : apply_within_trees (create_child C tg_old tg_new pk im rk cid) blk trs = Some trs')
    : disabled_tag C trs' nxtp tg l.
  Proof.
    eapply bind_Some in Ins as (tr&Htr&(tr'&Ins&[= <-])%bind_Some).
    destruct (decide (blk = l.1)) as [->|Hne]; last first.
    { rewrite /disabled_tag lookup_insert_ne //. }
    destruct Dis as (Hv&Dis). split; first done.
    rewrite lookup_insert_eq. rewrite Htr in Dis.
    destruct Dis as [Dis|Nd].
    - left. eapply disabled_tag_at_create_child_irreversible. 4: done. 1,3: done.
      rewrite /trees_contain /trees_at_block Htr in Nc. done.
    - right. intros Hc. eapply Nd. eapply insertion_minimal_tags. 3: done. all: done.
  Qed.

  Lemma frozen_in_practice_create_child_irreversible
    {tr tr' tg tg_old tg_new pk im rk cid witness loc}
    (Ne : tg_new ≠ tg)
    (Ne' : tg_new ≠ witness)
    (Frz : frozen_in_practice tr tg witness loc)
    (Ins : create_child C tg_old tg_new pk im rk cid tr = Some tr')
    : frozen_in_practice tr' tg witness loc.
  Proof.
    inversion Frz as [it_witness ? Rel Lookup Perm Ini].
    opose proof (create_child_irreversible Lookup Ne' Ins) as Lookup'.
    econstructor.
    + erewrite <- create_child_same_rel_dec; first eassumption.
      - eassumption.
      - eassumption.
      - eassumption.
    + apply Lookup'.
    + done.
    + done.
  Qed.

  Lemma rel_dec_equal_ParentChildIn_equiv tr1 tr2 :
    (∀ tg, tree_contains tg tr1 ↔ tree_contains tg tr2) →
    (∀ tg1 tg2, rel_dec tr1 tg1 tg2 = rel_dec tr2 tg1 tg2) →
    ∀ tg1 tg2, (ParentChildIn tg1 tg2 tr1 ↔ ParentChildIn tg1 tg2 tr2) ∧ (ImmediateParentChildIn tg1 tg2 tr1 ↔ ImmediateParentChildIn tg1 tg2 tr2).
  Proof.
    intros Hcont H tg1 tg2.
    specialize (H tg2 tg1).
    rewrite /rel_dec in H. destruct (decide (ParentChildIn tg1 tg2 tr1)) as [H1|H1]; last first.
    all: destruct (decide (ParentChildIn tg1 tg2 tr2)) as [H2|H2]; try done.
    all: split; first tauto.
    - split; intros H3%Immediate_is_StrictParentChild; exfalso. 1: eapply H1. 2: eapply H2. all: by right.
    - destruct (decide (tree_contains tg1 tr1)) as [Hin|Hnin]; last first.
      { split; intros _; eapply ImmediateParentChildIn_parent_not_in; last done.
        by setoid_rewrite <- Hcont. }
      destruct (decide (tg1 = tg2)) as [->|Hne].
      { split; intros H3%Immediate_is_StrictParentChild; exfalso; (eapply strict_parent_self_impossible; last done).
        2: rewrite <- Hcont. all: done. }
      destruct H1 as [?|H1]; first done.
      destruct H2 as [?|H2]; first done.
      rewrite decide_False in H. 2: { intros [?|H3]; first done. eapply strict_parent_self_impossible; first done. by eapply StrictParentChild_transitive. }
      rewrite (decide_False This) in H. 2: { intros [?|H3]; first done. setoid_rewrite Hcont in Hin. eapply strict_parent_self_impossible; first done. by eapply StrictParentChild_transitive. }
      destruct (decide (ImmediateParentChildIn tg1 tg2 tr1)), (decide (ImmediateParentChildIn tg1 tg2 tr2)); done.
  Qed.

  Lemma rel_dec_equal_ParentChildIn_equiv_lift tr1 tr2 :
    (∀ tg, tree_contains tg tr1 ↔ tree_contains tg tr2) →
    (∀ tg1 tg2, rel_dec tr1 tg1 tg2 = rel_dec tr2 tg1 tg2) →
    (∀ tg1 tg2, ParentChildIn tg1 tg2 tr1 ↔ ParentChildIn tg1 tg2 tr2) ∧
    (∀ tg1 tg2, StrictParentChildIn tg1 tg2 tr1 ↔ StrictParentChildIn tg1 tg2 tr2) ∧
    (∀ tg1 tg2, ImmediateParentChildIn tg1 tg2 tr1 ↔ ImmediateParentChildIn tg1 tg2 tr2).
  Proof.
    intros H1 H2.
    epose proof (rel_dec_equal_ParentChildIn_equiv _ _ H1 H2) as H. split_and!.
    1, 3: eapply H.
    intros tg1 tg2.
    destruct (decide (tree_contains tg1 tr1)) as [H3|H3]; last first.
    all: epose proof H3 as H3'; setoid_rewrite H1 in H3'.
    { split; intros _; rewrite /StrictParentChildIn; eapply every_subtree_eqv_universal.
      all: intros br Hex Htg; exfalso. 1: eapply H3'. 2: eapply H3.
      all: eapply exists_node_iff_exists_root.
      all: eapply exists_subtree_eqv_existential; eexists.
      all: split; first done; done.
      all: split; first eapply exists_node_iff_exists_root. }
    destruct (decide (tg1 = tg2)) as [->|Hne].
    { split; intros []%strict_parent_self_impossible; done. }
    destruct (H tg1 tg2) as ((HH1&HH2)&_).
    split; intros Hc.
    - destruct HH1 as [?|HH1]; try done. by right.
    - destruct HH2 as [?|HH2]; try done. by right.
  Qed.

  Lemma tree_equal_create_child d tr1 tr2 tr1' tg_new tg_old pk im rk cid ev2 :
    wf_tree tr1 → wf_tree tr2 →
    tree_items_compat_nexts tr1 tg_new ev2 → tree_items_compat_nexts tr2 tg_new ev2 →
    (cid < ev2)%nat →
    tree_contains tg_old tr1 →
    ¬ tree_contains tg_new tr1 →
    tree_equal C d tr1 tr2 →
    create_child C tg_old tg_new pk im rk cid tr1 = Some tr1' →
    ∃ tr2', create_child C tg_old tg_new pk im rk cid tr2 = Some tr2' ∧
      tree_equal C d tr1' tr2'.
  Proof.
    intros Hwf1 Hwf2 Hiwf1 Hiwf2 Hcidwf.
    intros Hcontains1 Hnotcont1 (H1&H2&H3) (it_new&Hit_new&[= <-])%bind_Some.
    assert (itag it_new = tg_new) as Htgnew by by eapply new_item_has_tag.
    assert (tg_old ≠ tg_new) as Htgsne by (intros ->; firstorder).
    pose proof Hcontains1 as Hcontains2. setoid_rewrite H1 in Hcontains2.
    pose proof Hnotcont1 as Hnotcont2. setoid_rewrite H1 in Hnotcont2.
    epose proof create_new_item_wf _ _ _ _ _ _ _ Hcidwf Hit_new as Hitemwf.
    opose proof (insert_child_wf C _ _ _ _ _ _ _ _ _ _ Hitemwf Hit_new _ Hiwf1 Hwf1) as (_&Hwf1').
    1: rewrite /create_child Hit_new //.
    opose proof (insert_child_wf C _ _ _ _ _ _ _ _ _ _ Hitemwf Hit_new _ Hiwf2 Hwf2) as (_&Hwf2').
    1: rewrite /create_child Hit_new //.
    eexists. split.
    1: rewrite /create_child Hit_new //.
    pose proof (rel_dec_equal_ParentChildIn_equiv_lift _ _ H1 H2) as (H2A&H2B&H2C).
    split_and!. 
    - intros tg. destruct (decide (tg = tg_new)) as [->|Hne].
      + split; (intros _; eapply insert_true_produces_exists; [done|]); assumption.
      + split; (intros H%insert_false_infer_exists; last congruence); eapply insert_preserves_exists, H1, H.
    - eapply same_parent_childs_agree; intros tg tg'.
      + destruct (decide (tg = tg_new)) as [->|Hne], (decide (tg' = tg_new)) as [->|Hne'].
        * split; intros _; by left.
        * subst tg_new. split; (intros [|Hc]; first done); exfalso; (eapply inserted_not_strict_parent; [| |exact Hc]; done).
        * subst tg_new. destruct (decide (tg = tg_old)) as [->|Hneold].
          1: split; intros _; eapply insert_produces_ParentChild; done.
          split; (intros [|Hc]; first done).
          all: eapply insert_produces_minimal_ParentChild in Hc; [|done..].
          all: eapply ParentChild_transitive; last by eapply insert_produces_ParentChild.
          all: right; setoid_rewrite <- insert_eqv_strict_rel; [|done..].
          1: by setoid_rewrite <- H2B. 1: by setoid_rewrite H2B.
        * subst tg_new. split; (intros [->|Hc]; [by left|right]).
          all: setoid_rewrite <- insert_eqv_strict_rel; [|done..].
          all: eapply H2B.
          all: setoid_rewrite -> insert_eqv_strict_rel; first done; done.
      + destruct (decide (tg = tg_new)) as [->|Hne], (decide (tg' = tg_new)) as [->|Hne'].
        * subst tg_new. split; intros H; exfalso; (eapply immediate_parent_child_not_equal; [..|done|done]).
          1-2: eapply Hwf1'. 3-4: eapply Hwf2'.
          all: eapply insert_true_produces_exists; first done; done.
        * subst tg_new. split; (intros Hc%Immediate_is_StrictParentChild); exfalso; (eapply inserted_not_strict_parent; [| |exact Hc]; done).
        * subst tg_new. destruct (decide (tg = tg_old)) as [->|Hneold].
          1: split; intros _; eapply insert_produces_ImmediateParentChild; done.
          destruct (decide (tree_contains tg tr1)) as [Htgin|Htgnin]; last first.
          { split; intros _; eapply ImmediateParentChildIn_parent_not_in.
            all: intros Hc%remove_false_preserves_exists; last done. 
            all: eapply Htgnin. 1: eapply H1. all: eapply Hc. }
          split; intros Hc; exfalso.
          all: eapply ImmediateParentChild_of_insert_is_parent in Hc; [done|done|..|done].
          1: done. by eapply H1.
        * subst tg_new. setoid_rewrite <- insert_eqv_imm_rel. 1: apply H2C.
          all: done.
    - intros tg Hcont. subst tg_new.
      destruct (decide (tg = itag it_new)) as [->|Hne].
      { exists it_new, it_new. split_and!.
        1-2: split; first by eapply insert_true_produces_exists.
        1-2: by eapply inserted_determined.
        eapply item_eq_up_to_C_reflexive. }
      eapply remove_false_preserves_exists in Hcont. 2: done.
      destruct (H3 tg Hcont) as (it1&it2&Hlu1&Hlu2&Hequptoc).
      exists it1, it2. split_and!.
      1-2: destruct Hlu1, Hlu2.
      1-2: split; first by eapply insert_preserves_exists.
      1-2: setoid_rewrite <- insert_true_preserves_every; done.
      intros l. specialize (Hequptoc l) as (Heq1&Heq2).
      split; first done.
      inversion Heq2 as [|pi c1 c2 Hi1 Hi2 Hi3 Hi4 Hi5| |p1 p2 Hi2 Hi3 Hi4 Hi5|witness_tg ? ? Dis1 Dis2|??? witness_tg Frz1|p1 p2 ini Hd]; simplify_eq.
      + by econstructor 1.
      + destruct Hlu1 as (Hlu1A&Hlu1B), Hlu2 as (Hlu2A&Hlu2B).
        pose proof Hcont as Hcont2. setoid_rewrite H1 in Hcont2. econstructor 2. 1: done.
        * inversion Hi2 as [|tg_cs it_cs Hii1 Hii2 Hii3 Hii4 Hii5 Hii6]; simplify_eq; first by econstructor 1.
          destruct Hii2 as [HA HB].
          econstructor 2. 3-6: done.
          2: { split. 1: by eapply insert_preserves_exists.
               setoid_rewrite <- insert_true_preserves_every; first done.
               intros <-. done. }
          rewrite /rel_dec in Hii1|-*.
          destruct (decide (ParentChildIn tg_cs tg tr1)) as [|HnPC]; first done.
          destruct (decide (ParentChildIn tg tg_cs tr1)) as [|HnPC2]; first done.
          rewrite decide_False; first rewrite decide_False //; last first.
          -- intros [|Hc]; eapply HnPC; first by left. right.
             eapply insert_eqv_strict_rel; last exact Hc.
             1-2: by intros <-.
          -- intros [|Hc]; eapply HnPC2; first by left. right.
             eapply insert_eqv_strict_rel; last exact Hc.
             1-2: by intros <-.
        * inversion Hi3 as [|tg_cs it_cs Hii1 Hii2 Hii3 Hii4 Hii5 Hii6]; simplify_eq; first by econstructor 1.
          destruct Hii2 as [HA HB].
          econstructor 2. 3-6: done.
          2: { split. 1: by eapply insert_preserves_exists.
               setoid_rewrite <- insert_true_preserves_every; first done.
               intros <-. done. }
          rewrite /rel_dec in Hii1|-*.
          destruct (decide (ParentChildIn tg_cs tg tr2)) as [|HnPC]; first done.
          destruct (decide (ParentChildIn tg tg_cs tr2)) as [|HnPC2]; first done.
          rewrite decide_False; first rewrite decide_False //; last first.
          -- intros [|Hc]; eapply HnPC; first by left. right.
             eapply insert_eqv_strict_rel; last exact Hc.
             1-2: by intros <-.
          -- intros [|Hc]; eapply HnPC2; first by left. right.
             eapply insert_eqv_strict_rel; last exact Hc.
             1-2: by intros <-.
      + by econstructor 3.
      + destruct Hlu1 as (Hlu1A&Hlu1B), Hlu2 as (Hlu2A&Hlu2B).
        pose proof Hcont as Hcont2. setoid_rewrite H1 in Hcont2. econstructor 4.
        * inversion Hi2 as [|tg_cs it_cs X1 X2 Hii1 Hii2 Hii3 Hii4]; simplify_eq; first by econstructor 1.
          destruct Hii2 as [HA HB].
          econstructor 2. 3-5: done.
          2: { split. 1: by eapply insert_preserves_exists.
               setoid_rewrite <- insert_true_preserves_every; first done.
               intros <-. done. }
          2: done.
          rewrite /rel_dec in Hii1|-*.
          destruct (decide (ParentChildIn tg_cs tg tr1)) as [|HnPC]; first done.
          destruct (decide (ParentChildIn tg tg_cs tr1)) as [|HnPC2]; first done.
          rewrite decide_False; first rewrite decide_False //; last first.
          -- intros [|Hc]; eapply HnPC; first by left. right.
             eapply insert_eqv_strict_rel; last exact Hc.
             1-2: by intros <-.
          -- intros [|Hc]; eapply HnPC2; first by left. right.
             eapply insert_eqv_strict_rel; last exact Hc.
             1-2: by intros <-.
        * inversion Hi3 as [|tg_cs it_cs X1 X2 Hii1 Hii2 Hii3 Hii4]; simplify_eq; first by econstructor 1.
          destruct Hii2 as [HA HB].
          econstructor 2. 3-6: done.
          2: { split. 1: by eapply insert_preserves_exists.
               setoid_rewrite <- insert_true_preserves_every; first done.
               intros <-. done. }
          rewrite /rel_dec in Hii1|-*.
          destruct (decide (ParentChildIn tg_cs tg tr2)) as [|HnPC]; first done.
          destruct (decide (ParentChildIn tg tg_cs tr2)) as [|HnPC2]; first done.
          rewrite decide_False; first rewrite decide_False //; last first.
          -- intros [|Hc]; eapply HnPC; first by left. right.
             eapply insert_eqv_strict_rel; last exact Hc.
             1-2: by intros <-.
          -- intros [|Hc]; eapply HnPC2; first by left. right.
             eapply insert_eqv_strict_rel; last exact Hc.
             1-2: by intros <-.
      + econstructor 5.
        * eapply disabled_in_practice_create_child_irreversible.
          5: rewrite /create_child; erewrite Hit_new; done.
          -- lia.
          -- inversion Dis1 as [it_witness ?? LuWitness].
             pose proof (tree_determined_specifies_tag _ _ _ (proj1 LuWitness) (proj2 LuWitness)) as itag_witness_spec.
             pose proof ((proj1 (every_node_iff_every_lookup (wf_tree_tree_item_determined _ Hwf1)) Hiwf1 witness_tg it_witness ltac:(assumption)).(item_tag_valid _ _ _) witness_tg itag_witness_spec).
             enough (itag it_new ≠ witness_tg) by eassumption.
             lia.
          -- eassumption.
          -- eassumption.
        * eapply disabled_in_practice_create_child_irreversible.
          5: rewrite /create_child; erewrite Hit_new; done.
          -- lia.
          -- inversion Dis1 as [it_witness ?? LuWitness].
             pose proof (tree_determined_specifies_tag _ _ _ (proj1 LuWitness) (proj2 LuWitness)) as itag_witness_spec.
             pose proof ((proj1 (every_node_iff_every_lookup (wf_tree_tree_item_determined _ Hwf1)) Hiwf1 witness_tg it_witness ltac:(assumption)).(item_tag_valid _ _ _) witness_tg itag_witness_spec).
             enough (itag it_new ≠ witness_tg) by eassumption.
             lia.
          -- eassumption.
          -- eassumption.
        * auto.
        * auto.
      + econstructor 6; destruct d.
        * eapply frozen_in_practice_create_child_irreversible.
          4: rewrite /create_child; erewrite Hit_new; done.
          -- lia.
          -- inversion Frz1 as [it_witness ?? LuWitness].
             pose proof (tree_determined_specifies_tag _ _ _ (proj1 LuWitness) (proj2 LuWitness)) as itag_witness_spec.
             pose proof ((proj1 (every_node_iff_every_lookup (wf_tree_tree_item_determined _ Hwf1)) Hiwf1 witness_tg it_witness ltac:(assumption)).(item_tag_valid _ _ _) witness_tg itag_witness_spec).
             enough (itag it_new ≠ witness_tg) by eassumption.
             lia.
          -- eassumption.
        * eapply frozen_in_practice_create_child_irreversible.
          4: rewrite /create_child; erewrite Hit_new; done.
          -- lia.
          -- inversion Frz1 as [it_witness ?? LuWitness].
             pose proof (tree_determined_specifies_tag _ _ _ (proj1 LuWitness) (proj2 LuWitness)) as itag_witness_spec.
             pose proof ((proj1 (every_node_iff_every_lookup (wf_tree_tree_item_determined _ Hwf2)) Hiwf2 witness_tg it_witness ltac:(assumption)).(item_tag_valid _ _ _) witness_tg itag_witness_spec).
             enough (itag it_new ≠ witness_tg) by eassumption.
             lia.
          -- eassumption.
      + econstructor 7. done.
  Qed.

  Lemma trees_equal_create_child d trs1 trs2 trs1' blk tg_new tg_old pk im rk cid nxtc :
    wf_trees trs1 → wf_trees trs2 →
    trees_compat_nexts trs1 tg_new nxtc → trees_compat_nexts trs2 tg_new nxtc →
    (cid < nxtc)%nat →
    trees_contain tg_old trs1 blk →
    ¬ trees_contain tg_new trs1 blk →
    trees_equal C d trs1 trs2 →
    apply_within_trees (create_child C tg_old tg_new pk im rk cid) blk trs1 = Some trs1' →
    ∃ trs2', apply_within_trees (create_child C tg_old tg_new pk im rk cid) blk trs2 = Some trs2' ∧
      trees_equal C d trs1' trs2'.
  Proof.
    intros Hwf1 Hwf2 Hiwf1 Hiwf2 Hcidwf Hcont Hncont Heq.
    intros (tr1&Htr1&(tr1'&Htr1'&[= <-])%bind_Some)%bind_Some.
    eapply bind_Some in Htr1' as HH. destruct HH as (it&Hit&[= Htrit]).
    epose proof (Heq blk) as HeqblkI.
    inversion HeqblkI as [t1x tr2 Heqblk Heq1x Htr2|]; simplify_eq; last congruence.
    symmetry in Htr2. assert (t1x = tr1) as -> by congruence. clear Heq1x.
    eapply tree_equal_create_child in Htr1' as (tr2'&Htr2'&Heqtr).
    - eexists. rewrite /apply_within_trees /= Htr2 /=.
      split; first by rewrite /create_child Hit.
      intros blk'. destruct (decide (blk = blk')) as [->|Hne].
      + rewrite !lookup_insert_eq. econstructor.
        eapply bind_Some in Htr2' as HH. destruct HH as (it2&Hit2&[= <-]).
        enough (it = it2) as -> by by eapply Heqtr.
        congruence.
      + rewrite !lookup_insert_ne //.
    - by eapply Hwf1.
    - by eapply Hwf2.
    - by eapply Hiwf1.
    - by eapply Hiwf2.
    - done.
    - by rewrite /trees_contain /trees_at_block Htr1 in Hcont.
    - by rewrite /trees_contain /trees_at_block Htr1 in Hncont.
    - done.
  Qed.


End utils.
