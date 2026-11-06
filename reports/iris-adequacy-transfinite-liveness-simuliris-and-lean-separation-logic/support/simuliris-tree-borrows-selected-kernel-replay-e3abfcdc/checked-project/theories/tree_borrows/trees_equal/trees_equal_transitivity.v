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

  Lemma trees_equal_find_equal_tag_protected_initialized_not_disabled d trs1 trs2 it1 tg blk off:
    each_tree_protected_parents_not_disabled C trs2 →
    wf_trees trs2 →
    trees_equal C d trs1 trs2 →
    trees_lookup trs1 blk tg it1 →
    (initialized (item_lookup it1 off) = PermInit → perm (item_lookup it1 off) ≠ Disabled) →
    protector_is_active it1.(iprot) C →
    ∃ it2, trees_lookup trs2 blk tg it2 ∧
      (initialized (item_lookup it2 off) = PermInit → perm (item_lookup it2 off) ≠ Disabled) ∧
      protector_is_active it2.(iprot) C.
  Proof.
    intros Heach Hwf Heq (tr1&Htr1&Hit) Hperm Hactive.
    specialize (Heq blk). rewrite Htr1 in Heq. inversion Heq as [x tr2 Heq' Hx Htr2|]. subst x.
    destruct Heq' as (Heq1&Heq2&Heq3).
    pose proof Hit as (Hitin&Hitdet).
    specialize (Heq3 _ Hitin) as (it1'&it2&Hit1'&Hit2&Heqit).
    assert (it1 = it1') as <-.
    { eapply tree_determined_unify. 2: done. 1: done. apply Hit1'. }
    exists it2. specialize (Heqit off) as (Hprotit&Hlocit).
    split. 1: exists tr2; done.
    rewrite -Hprotit. inversion Hlocit as [|e c1 c2 H H1 H2 H3 H4| | | | |p1 p2 ini H]; simplify_eq.
    - done.
    - rewrite -!H3 /= in Hperm. simpl. done.
    - exfalso. done.
    - done.
    - split; last done. intros Hinit Hdis.
      ospecialize (Heach _ _ _ tg). 1: symmetry; exact Htr2.
      eapply every_child_ParentChildIn in Heach. 2: by eapply Hwf. 2,4: eapply Hwf; first done; eapply Hit2.
      2: eapply Hit2. 2: by left.
      rewrite every_node_eqv_universal in Heach. ospecialize (Heach it2 _ _ _ _).
      1: eapply exists_determined_exists; eapply Hit2. 1: by eapply tree_lookup_correct_tag.
      1: done. 1: by rewrite -Hprotit. rewrite Hdis in Heach. by destruct Heach.
    - split; last done. simpl. done.
    - split; last done. simpl. intros ->. destruct d; by inversion H.
  Qed.

  Lemma tree_equal_transfer_item_usefully_protected d tr1 tr2 tg it off :
    protected_parents_not_disabled C tr1 →
    no_active_cousins C tr1 →
    (∀ tg, tree_contains tg tr1 → tree_unique tg tr1) →
    tree_equal C d tr1 tr2 →
    tree_lookup tr1 tg it →
    protector_is_active (iprot it) C ∧ perm (item_lookup it off) ≠ Disabled ∧ perm (item_lookup it off) ≠ Cell ∧ initialized (item_lookup it off) = PermInit →
    ∃ it2, tree_lookup tr2 tg it2 ∧ protector_is_active (iprot it2) C ∧ perm (item_lookup it2 off) ≠ Disabled ∧ perm (item_lookup it2 off) ≠ Cell ∧ initialized (item_lookup it2 off) = PermInit.
  Proof.
    intros Hpnd Hnac Hunq (He1&He2&He3) Hlu (Hprot&Hndis&Hnc&Hini).
    destruct (He3 tg) as (it1&it2&Hlu1&Hlu2&Heq).
    1: eapply Hlu.
    assert (it = it1) as -> by by eapply tree_lookup_unique.
    exists it2. specialize (Heq off) as (Hproteq&Hiteq). split; first done.
    split. 1: by rewrite -Hproteq.
    inversion Hiteq as [pp1|ini1 confl1 confl2 HprotX HP1 HP2 Heq1 Heq2|ini1 confl1 confl2 HnoProt|p1 p2 HP1 HP2 Heq1 Heq2|wit_tg lp1 lp2 Hdip1 Hdip2 HiniX Heq1 Heq2|ini1 confl1 confl2 wit_tg HF Heq1 Heq2|p1 p2 ini Hd Heq1 Heq2]; simplify_eq.
    - done.
    - split; first done. rewrite -Heq1 /= in Hini. rewrite /= Hini //.
    - rewrite -Heq1 in Hini. done.
    - exfalso.
      inversion Hdip1 as [itw p Hreldec Hluw Hdisw].
      rewrite /rel_dec in Hreldec. destruct decide; last done.
      eapply tree_lookup_correct_tag in Hlu as HH. subst tg.
      specialize (Hpnd wit_tg off). eapply every_child_ParentChildIn in Hpnd.
      2: eapply Hunq. 2: eapply Hunq, Hluw. 2: eapply Hluw. 2: eapply Hunq, Hlu.
      2: done.
      eapply every_node_eqv_universal in Hpnd.
      2: { eapply tree_lookup_to_exists_node. eapply Hlu. }
      inversion Hdisw as [X1 HH X2|pp X2 Hdis Hlazy X5]; simplify_eq.
      { unshelve odestruct (Hpnd _) as [H|H]; [done..|eapply H; by rewrite -HH|done]. }
      inversion Hdis as [X1 HH X2|tgcs itcs lp X1 Hcs Hlucs Hprotcs Hactcs HH X2 X3]; simplify_eq.
      { unshelve odestruct (Hpnd _) as [H|H]. 1-3: done. 1: by rewrite -Hlazy in H. done. }
      eapply Hnac. 2: eapply Hlucs. 1: eapply Hlu. 3: by erewrite Hactcs.
      2: right; split; last done; left; done.
      eapply child_of_this_is_foreign_for_cousin. 4: exact Hcs.
      1-3: eapply Hunq. 1: eapply Hluw. 1: eapply Hlucs. 1: eapply Hlu.
      rewrite /rel_dec decide_True //.
    - split; first done. rewrite -Heq1 /= in Hini. rewrite /= Hini //.
    - rewrite -Heq1 /= in Hini Hndis. simplify_eq. split_and!; last done.
      all: simpl; destruct d; inversion Hd; done.
 Qed.

  Lemma tree_equal_transfer_pseudo_conflicted d tr1 tr2 tg off confl :
    protected_parents_not_disabled C tr1 →
    no_active_cousins C tr1 →
    (∀ tg, tree_contains tg tr1 → tree_unique tg tr1) →
    tree_equal C d tr1 tr2 →
    pseudo_conflicted C tr1 tg off confl →
    pseudo_conflicted C tr2 tg off confl.
  Proof.
    intros Hpnd Hnac Hunq (HH1&HH2&HH3) Hconfl.
    inversion Hconfl as [|tg_cs it_cs Hcs Hlu Hprot Hperm Hini Hncell]; simplify_eq.
    - econstructor 1.
    - edestruct tree_equal_transfer_item_usefully_protected as (it2&Hit2&Hprot2&Hndis2&Hncell2&Hini2).
      1: exact Hpnd. 1: exact Hnac. 1: exact Hunq. 1: split; done. 1: exact Hlu.
      1: done.
      econstructor 2. 1: by erewrite <- HH2. 1: exact Hit2.
      all: done.
  Qed.

  Global Instance pseudo_disabled_dec tr tg off pp oprot : Decision (pseudo_disabled C tr tg off pp oprot).
  Proof.
    destruct (decide (pp = Disabled)) as [->|Hne].
    1: left; econstructor 1.
    pose (P it_cs := let tg_cs := itag it_cs in
                     rel_dec tr tg tg_cs = Foreign Cousin ∧
                     tree_item_determined tg_cs it_cs tr ∧
                     protector_is_active (iprot it_cs) C ∧
                     item_lookup it_cs off = mkPerm PermInit Active ∧
                     match pp with ReservedIM | Cell => False | _ => True end).
    assert (∀ it, Decision (P it)) as DecP.
    { intros it.
      rewrite /P.
      do 4 (eapply and_dec; first eapply _).
      destruct pp.
      all: eapply _. }
    destruct (decide (exists_node P tr)) as [HP|HnP].
    - left. eapply exists_node_eqv_existential in HP as (it&Htgit&H1&H2&H3&H4&H5).
      econstructor 2.
      1: exact H1. 1: split. 2: exact H2.
      1: eapply exists_node_eqv_existential; exists it; done.
      1: done. 1: done.
      1: intros ->.
      1: done.
      1: by destruct pp.
    - right. intros Hdis.
      induction Hdis as [|tg_cs it_cs lp Hlp H1 H2 H3 H4 H5]; first done.
      eapply HnP. eapply exists_node_eqv_existential.
      exists it_cs. split. 1: eapply tree_lookup_to_exists_node; done.
      assert (itag it_cs = tg_cs) as <- by by eapply tree_lookup_correct_tag.
      split; first done.
      split; first eapply H2.
      split; first done.
      split; first done. 
      destruct lp as [| | | | |]; try done.
  Defined.

  Global Instance is_disabled_dec tr tg off lp oprot : Decision (is_disabled C tr tg off lp oprot).
  Proof.
    destruct (decide (lp = mkPerm PermInit Disabled)) as [->|Hne].
    1: left; econstructor 1.
    destruct lp as [[] pp].
    1: { right. intros HH. inversion HH. subst pp. done. }
    destruct (decide (pseudo_disabled C tr tg off pp oprot)) as [Hpd|Hnpd].
    1: left; econstructor 2; done.
    right.
    intros HH. inversion HH; simplify_eq.
  Qed.

  Lemma trees_equal_decide_disabled_in_practice tr tg off :
    (∀ tg, tree_contains tg tr → tree_unique tg tr) →
    tree_contains tg tr →
    (∃ tgp itp, tree_lookup tr tgp itp ∧ is_disabled C tr tgp off (item_lookup itp off) (iprot itp) ∧ ParentChildIn tgp tg tr ∧ 
          ∀ tgpp itpp, tree_lookup tr tgpp itpp → StrictParentChildIn tgpp tgp tr → ¬ is_disabled C tr tgpp off (item_lookup itpp off) (iprot itpp))
    + (∀ tgp itp, tree_lookup tr tgp itp → ParentChildIn tgp tg tr → ¬ is_disabled C tr tgp off (item_lookup itp off) (iprot itp)).
  Proof.
    intros Hunq H.
    assert (Decision (exists_node (λ it, is_disabled C tr (itag it) off (item_lookup it off) (iprot it) ∧ ParentChildIn (itag it) tg tr) tr)) as Hdec.
    { eapply exists_node_dec. intros itx. eapply and_dec. 2: by eapply ParentChildIn_dec. apply _. }
    destruct Hdec as [Hleft|Hright].
    - left.
      edestruct (find_highest_parent_with_property (λ x, is_disabled C tr (itag x) off (item_lookup x off) (iprot x) ∧ ParentChildIn (itag x) tg tr)) as (tgpp&Htgpp&Hppp).
      { intros x. eapply and_dec. 2: by eapply ParentChildIn_dec. apply _. }
      { done. }
      { done. }
      eapply exists_node_eqv_existential in Htgpp. destruct Htgpp as (itpp&Hitpp&(HHitpp1&HHitpp2)&<-).
      eapply exists_node_to_tree_lookup in Hitpp. 2: done.
      exists (itag itpp), itpp. do 3 (split; first done).
      intros tgppp itppp Hitppp HSPppp Hdis.
      eapply Hppp. 2: exact HSPppp.
      eapply tree_lookup_correct_tag in Hitppp as Htg. subst tgppp.
      eapply exists_node_eqv_existential. exists itppp.
      split. 2: split_and!; try done. 1: by eapply tree_lookup_to_exists_node.
      eapply ParentChild_transitive; [|exact HHitpp2]; right; done.
    - right. intros tgp itp Hlu HPC Hdis. eapply tree_lookup_correct_tag in Hlu as Htg; subst tgp.
      eapply Hright. eapply exists_node_eqv_existential.
      eexists. split. 1: eapply tree_lookup_to_exists_node, Hlu. split; done.
  Qed.

  Lemma disabled_in_practice_not_active tr tg1 tg2 it off
    (Hwf : wf_tree tr)
    (HPP : parents_more_active tr)
    (HNC : no_active_cousins C tr) :
    tree_lookup tr tg2 it →
    perm (item_lookup it off) = Active →
    disabled_in_practice C tr tg2 tg1 off →
    False.
  Proof.
    intros Hl1 Hact [it_witness incl H1 H2 H3].
    destruct (decide (perm (item_lookup it_witness off) = Disabled)) as [Hdis|Hnondis].
    + eapply parents_not_disabled_child_not_active. 1: exact Hwf. 1: done. 4: exact Hdis. 4: exact Hact.
      1-2: done.
      rewrite /rel_dec in H1. destruct decide; done.
    + inversion H3 as [X1 X2 X3|lp X HH1 HH2 X2]; simplify_eq.
      { rewrite -X2 in Hnondis. done. }
      inversion HH1 as [|tgcs itcs X1 X2 H1' H2' H3' H4 H5 X3 X4]; simplify_eq.
      { rewrite -HH2 in Hnondis. done. }
      eapply HNC. 1: exact H2'. 1: exact Hl1. 3: exact Hact. 2: right; split.
      3: by rewrite H4.
      2: { left. split; first done. by rewrite H4. }
      rewrite /rel_dec in H1|-*.
      destruct decide as [HPC1|] in H1; last done. clear H1.
      rewrite decide_False; last first.
      { intros HPC2. rewrite /rel_dec in H1'.
        destruct decide in H1'; try done.
        rewrite decide_True // in H1'.
        eapply ParentChild_transitive. 1: exact HPC1. done. }
      rewrite decide_False //.
      intros HPC2.
      eapply cousins_have_disjoint_children. 4: exact H1'. 4: exact HPC1. 4: done.
      all: eapply Hwf. 1: eapply Hl1. 1: eapply H2. 1: eapply H2'.
  Qed.

  Lemma tree_equal_transfer_pseudo_disabled {d tr tr2 tgcld off lp pp} :
    (∀ tg, tree_contains tg tr2 → tree_unique tg tr2) →
    parents_more_active tr2 →
    no_active_cousins C tr2 →
    pseudo_disabled C tr2 tgcld off lp pp →
    tree_equal C d tr tr2 → pseudo_disabled C tr tgcld off lp pp.
  Proof.
    intros Hunq Hwf1 Hwf2 HH (He1&He2&He3).
    induction HH as [|tg_cs it_cs lp prot H1 H2 H3 H4 H5].
    1: econstructor 1.
    edestruct He3 as (it_cs1&X&Hit_cs1&HX&Hiteq).
    1: eapply He1, H2.
    assert (X = it_cs) as -> by by eapply tree_lookup_unique.
    specialize (Hiteq off) as (Hprot&Hiteq).
    econstructor 2. 2: exact Hit_cs1.
    1: by rewrite He2.
    1: rewrite Hprot //.
    2: done.
    2: done.
    rewrite H4 in Hiteq.
    inversion Hiteq as [| | | | | |p1 p2 ini Hd]; simplify_eq.
    - congruence.
    - exfalso. eapply disabled_in_practice_not_active.
      5: erewrite H4; done.
      4: done. 1: done. 3: eassumption. all: done.
    - rewrite -Hprot in H3. f_equal.
      destruct d; inversion Hd; done.
  Qed.

  Lemma transfer_pseudo_disabled_notimm p1 p2 tr tg off pp :
    pseudo_disabled C tr tg off p1 pp →
    p2 ≠ ReservedIM → p2 ≠ Cell → p1 ≠ Disabled →
    pseudo_disabled C tr tg off p2 pp.
  Proof.
    intros H Hne1 Hne2.
    inversion H as [|X1 X2 X3 X4 X5 X6 X7 X8 X9]. 1: done. econstructor 2.
    1-4: done. all: done.
  Qed.

  Lemma conflicted_transfer_pseudo_disabled c1 c2 tr tg off pp :
    pseudo_disabled C tr tg off (Reserved c1) pp →
    pseudo_disabled C tr tg off (Reserved c2) pp.
  Proof.
    intros HH. eapply transfer_pseudo_disabled_notimm. 1: done. all: done.
  Qed.

  Lemma tree_equal_transfer_is_disabled {d tr tr2 tgcld off lp pp} :
    (∀ tg, tree_contains tg tr2 → tree_unique tg tr2) →
    parents_more_active tr2 →
    no_active_cousins C tr2 →
    is_disabled C tr2 tgcld off lp pp →
    tree_equal C d tr tr2 → is_disabled C tr tgcld off lp pp.
  Proof.
    intros Hunq ?? Hdis Heq.
    induction Hdis as [|lp prot HH].
    1: econstructor 1.
    econstructor 2.
    by eapply tree_equal_transfer_pseudo_disabled.
  Qed.
    

  Lemma trees_equal_transfer_disabled_in_practice_many {tr2 tgpar tgcld off} :
    (∀ tg, tree_contains tg tr2 → tree_unique tg tr2) →
    parents_more_active tr2 →
    no_active_cousins C tr2 →
    disabled_in_practice C tr2 tgcld tgpar off →
    ∃ tgpar',
      disabled_in_practice C tr2 tgcld tgpar' off ∧
      ∀ d tr', tree_equal C d tr2 tr' → disabled_in_practice C tr' tgcld tgpar' off.
  Proof.
    intros Hunq1 Hwf1 Hwf2 Hdip.
    inversion Hdip as [itw incl Hrel Hlu Hperm].
    rewrite /rel_dec in Hrel. destruct decide as [HPCo|?]; try done.
    destruct (trees_equal_decide_disabled_in_practice tr2 tgcld off) as [(tgp&itp&Hlup&Hdisp&HPC&Hothers)|HR].
    1: done.
    { eapply contains_child. 1: done. eapply Hlu. }
    2: { exfalso. eapply HR. 1: exact Hlu. 1: done. done. }
    exists tgp. split_and!.
    { econstructor. 2: exact Hlup. 2: done. rewrite /rel_dec decide_True //. }
    intros d tr1 (Heq1&Heq2&Heq3).
    destruct (Heq3 tgp) as (itp'&itp2&Hitp'&Hitp2&Heq).
    1: eapply Hlup.
    assert (itp = itp') as <- by by eapply tree_lookup_unique.
    specialize (Heq off) as (Hprot&Heq).
    inversion Heq as [pp1 X1 HH|ini1 confl1 confl2 HprotX HP1 HP2 HeqX1 HeqX2|ini1 confl1 confl2 HnoProt HeqX1 HeqX2|p1 p2 HP1 HP2 HeqX1 HeqX2|wit_tg lp1 lp2 Hdip1 Hdip2 HiniX HeqX1 HeqX2|ini1 confl1 confl2 wit_tg HF1 HeqX1 HeqX2|p1 p2 ini Hd HeqX1 HeqX2]; simplify_eq.
    - econstructor. 2: exact Hitp2.
      1: rewrite -Heq2 /rel_dec decide_True //.
      rewrite -HH -Hprot.
      eapply tree_equal_transfer_is_disabled. 1-3: eassumption. 2: eapply tree_equal_sym; done. done.
    - rewrite -HeqX1 in Hdisp.
      econstructor. 2: exact Hitp2.
      1: rewrite -Heq2 /rel_dec decide_True //.
      inversion Hdisp as [|lp prot HH1 HH2 HH3]; simplify_eq.
      rewrite -HeqX2 -Hprot. econstructor 2.
      eapply tree_equal_transfer_pseudo_disabled in HH1. 2-4: done. 2: by eapply tree_equal_sym.
      by eapply conflicted_transfer_pseudo_disabled.
    - rewrite -HeqX1 in Hdisp.
      econstructor. 2: exact Hitp2.
      1: rewrite -Heq2 /rel_dec decide_True //.
      inversion Hdisp as [|lp prot HH1 HH2 HH3]; simplify_eq.
      rewrite -HeqX2 -Hprot. econstructor 2.
      eapply tree_equal_transfer_pseudo_disabled in HH1. 2-4: done. 2: by eapply tree_equal_sym.
      by eapply conflicted_transfer_pseudo_disabled.
    - econstructor. 2: exact Hitp2.
      1: rewrite -Heq2 /rel_dec decide_True //.
      rewrite -HeqX2. econstructor 2. rewrite -Hprot. done.
    - inversion Hdip2 as [itwF incl H1 H2 H3].
      inversion Hdip1 as [itwF' incl' H1' H2' H3'].
      assert (incl = incl') as <-.
      { rewrite Heq2 H1 in H1'. by simplify_eq. }
      rewrite /rel_dec in H1'. destruct decide as [HPCF|] in H1'; last done.
      clear H1'. destruct HPCF as [<-|Hne].
      1: { assert (itwF = itp2) as <- by by eapply tree_lookup_unique.
           econstructor. 2: exact Hitp2.
           1: rewrite -Heq2 /rel_dec decide_True //. done. }
      exfalso. eapply Hothers. 2: exact Hne. 1: done. done.
    - rewrite -HeqX1 in Hdisp.
      econstructor. 2: exact Hitp2.
      1: rewrite -Heq2 /rel_dec decide_True //.
      inversion Hdisp as [|lp prot HH1 HH2 HH3]; simplify_eq.
      rewrite -HeqX2 -Hprot. econstructor 2.
      eapply tree_equal_transfer_pseudo_disabled in HH1. 2-4: done. 2: by eapply tree_equal_sym.
      by eapply conflicted_transfer_pseudo_disabled.
    - rewrite -HeqX1 in Hdisp.
      econstructor. 2: exact Hitp2.
      1: rewrite -Heq2 /rel_dec decide_True //.
      inversion Hdisp as [|lp prot HH1 HH2 HH3]; simplify_eq.
      1: destruct d; inversion Hd; done.
      rewrite -HeqX2 -Hprot. econstructor 2.
      eapply tree_equal_transfer_pseudo_disabled in HH1. 2-4: done. 2: by eapply tree_equal_sym.
      eapply transfer_pseudo_disabled_notimm. 1: exact HH1. all: destruct d; inversion Hd; done.
  Qed.

  Lemma trees_equal_transfer_disabled_in_practice_twice {d1 d2 tr1 tr2 tr3 tgpar tgcld off} :
    (∀ tg, tree_contains tg tr2 → tree_unique tg tr2) →
    parents_more_active tr2 →
    no_active_cousins C tr2 →
    tree_equal C d1 tr1 tr2 →
    tree_equal C d2 tr2 tr3 →
    disabled_in_practice C tr2 tgcld tgpar off →
    ∃ tgpar',
      disabled_in_practice C tr1 tgcld tgpar' off ∧
      disabled_in_practice C tr2 tgcld tgpar' off ∧
      disabled_in_practice C tr3 tgcld tgpar' off.
  Proof.
    intros H1 Hu1 Hu2 H2%tree_equal_sym H3 Hdip.
    odestruct trees_equal_transfer_disabled_in_practice_many as (tg&Htg&Htg2).
    1: exact H1. 1-2: done. 1: exact Hdip.
    exists tg. split_and!.
    - by eapply Htg2.
    - done.
    - eapply Htg2. done.
  Qed.

  Lemma trees_equal_transfer_frozen_in_practice_many {tr2 tgpar tgcld off} :
    (∀ tg, tree_contains tg tr2 → tree_unique tg tr2) →
    parents_more_active tr2 →
    no_active_cousins C tr2 →
    frozen_in_practice tr2 tgcld tgpar off →
    (frozen_in_practice tr2 tgcld tgpar off ∧
     (∀ d tr', tree_equal C d tr2 tr' → ∃ p, parent_has_perm p tr' tgcld tgpar off ∧ (p = Frozen ∨ p = Active ∧ d = Forwards))) ∨
    (∃ tgpar', disabled_in_practice C tr2 tgcld tgpar' off ∧
     ∀ d tr', tree_equal C d tr2 tr' → disabled_in_practice C tr' tgcld tgpar' off).
  Proof.
    intros Hunq1 Hwf1 Hwf2 Hdip.
    inversion Hdip as [itw incl Hrel Hlu Hperm Hinit].
    rewrite /rel_dec in Hrel. destruct decide as [HPCo|?]; try done.
    destruct (trees_equal_decide_disabled_in_practice tr2 tgcld off) as [(tgp&itp&Hlup&Hdisp&HPC&Hothers)|HR].
    1: done.
    { eapply contains_child. 1: done. eapply Hlu. }
    - odestruct trees_equal_transfer_disabled_in_practice_many as (tg&Htg).
      1: exact Hunq1. 1-2: done. 2: { right. exists tg. exact Htg. }
      econstructor. 3: done. 2: done. rewrite /rel_dec decide_True //.
    - left. split.
      1: done.
      intros d tr1 (Heq1&Heq2&Heq3).
      destruct (Heq3 tgpar) as (itw'&itw2&Hitw'&Hitw2&Heq).
      1: eapply Hlu.
      assert (itw = itw') as <- by by eapply tree_lookup_unique.
      assert (∃ p, item_lookup itw2 off = mkPerm PermInit p ∧ (p = Frozen ∨ p = Active ∧ d = Forwards)) as (p&Hitlu&Hp).
      { specialize (Heq off) as (HeqL1&HeqL2).
        inversion HeqL2 as [pp1|ini1 confl1 confl2 HprotX HP1 HP2 HeqX1 HeqX2|ini1 confl1 confl2 HnoProt HeqX1 HeqX2|lp1 lp2 Hdip1 Hdip2 HeqX1 HeqX2|wit_tg lp1 lp2 Hdip1 Hdip2 HiniX HeqX1 HeqX2|ini1 confl1 confl2 wit_tg HF1 HeqX1 HeqX2|p1 p2 ini Hd HeqX1 HeqX2]; simplify_eq.
        + exists Frozen; split; last tauto. destruct item_lookup; simpl in *; simplify_eq. done.
        + rewrite -HeqX1 // in Hperm.
        + rewrite -HeqX1 // in Hperm.
        + rewrite -HeqX1 // in Hinit.
        + exists Frozen; split; last tauto. inversion Hdip1 as [itw1' incl1 Hrel1 Hlu1 Hperm1].
          rewrite /rel_dec in Hrel1. destruct decide as [HPC1|?] in Hrel1; last done.
          eapply HR in Hperm1. 1: done. 1: done.
          eapply ParentChild_transitive. 2: eassumption. done.
        + rewrite -HeqX1 // in Hperm.
        + rewrite -HeqX1 /= in Hperm Hinit; subst ini.
          f_equal. destruct d; inversion Hd; simplify_eq.
          eexists; split; first done. by right. }
      exists p. split; last done. econstructor. 2: exact Hitw2.
      1: rewrite -Heq2 /rel_dec decide_True //.
      all: by rewrite Hitlu.
  Qed.

  Lemma perm_eq_up_to_C_trans {tr1 tr2 tr3 tg l cid perm1 perm2 perm3} :
    protected_parents_not_disabled C tr2 →
    (∀ tg, tree_contains tg tr2 → tree_unique tg tr2) →
    (∀ tg, tree_contains tg tr1 → tree_unique tg tr1) →
    parents_more_active tr2 →
    no_active_cousins C tr2 →
    parents_more_active tr1 →
    no_active_cousins C tr1 →
    tree_equal C Forwards tr1 tr2 →
    tree_equal C Forwards tr2 tr3 →
    perm_eq_up_to_C C tr1 tr2 tg l cid Forwards perm1 perm2 →
    perm_eq_up_to_C C tr2 tr3 tg l cid Forwards perm2 perm3 →
    perm_eq_up_to_C C tr1 tr3 tg l cid Forwards perm1 perm3.
  Proof.
    intros Hpnd Hunq1 Hunq2 Hpma1 Hnac1 Hpma2 Hnac2 Heq12 Heq23 EqC1 EqC2.
    inversion EqC1 as [pp1|ini1 confl1 confl2 Hprot HP1 HP2|ini1 confl1 confl2 HnoProt|p1 p2 HP1 HP2|wit_tg lp1 lp2 Hdip1 Hdip2 Hini Hcell|ini1 confl1 confl2 wit_tg HF|p1 p2 ini Hd]; simplify_eq;
    inversion EqC2 as [pp1'|ini1' confl1' confl2' Hprot' HP1' HP2'|ini1' confl1' confl2' HnoProt'|p1' p2' HP1' HP2'|wit_tg' lp1 lp2 Hdip1' Hdip2' Hini' Hcell'|ini1' confl1' confl2' wit_tg' HF'|p1' p2' ini' Hd']; simplify_eq.
    (* easy case: perm1 = perm2 *)
    + econstructor 1.
    + econstructor 2. 1: done. 2: done.
      eapply tree_equal_transfer_pseudo_conflicted. 1: done. 1: done. 1: done.
      1: by eapply tree_equal_sym. done.
    + by econstructor 3.
    + econstructor 4. 2: done.
      eapply tree_equal_transfer_pseudo_disabled. 5: done. all: done.
    + odestruct (trees_equal_transfer_disabled_in_practice_twice Hunq1 Hpma1 Hnac1 Heq12 Heq23) as (ww&Hw1&Hw2&Hw3).
      1: done. econstructor. 1: exact Hw1. 1: exact Hw3. 1: congruence. done.
    + eapply trees_equal_transfer_frozen_in_practice_many in HF' as [(Hfip&Hfip2)|(tr&Hdi9p&Hdip2)]. 3-5: eassumption.
      * econstructor 6. all: edestruct Hfip2 as (px&Hpx&Hrz). 1: by eapply tree_equal_sym.
        enough (px = Frozen) as -> by done. destruct Hrz as [->|(->&[=])]; tauto.
      * econstructor 5; [| |done..]. all: eapply Hdip2. 2: done. 1: by eapply tree_equal_sym.
    + econstructor 7. apply Hd'.
    (* case 2: perm1 and perm2 are pseudo_conflicted Reserved *)
    + econstructor 2. 1: done. 1: done.
      eapply tree_equal_transfer_pseudo_conflicted. 5: exact HP2. all: done.
    + econstructor 2; done.
    + exfalso. done.
    + econstructor 4. 2: done.
      eapply conflicted_transfer_pseudo_disabled.
      eapply tree_equal_transfer_pseudo_disabled. 4: done. all: done.
    + odestruct (trees_equal_transfer_disabled_in_practice_twice Hunq1 Hpma1 Hnac1 Heq12 Heq23) as (ww&Hw1&Hw2&Hw3).
      1: done. econstructor 5. 1: exact Hw1. 1: exact Hw3. 2: { split; first done. rewrite -Hcell'. done. } simpl in *. eapply Hini'.
    + eapply trees_equal_transfer_frozen_in_practice_many in HF' as [(Hfip&Hfip2)|(tr&Hdi9p&Hdip2)]. 3-5: eassumption.
      * econstructor 6. all: edestruct Hfip2 as (px&Hpx&Hrz). 1: by eapply tree_equal_sym.
        enough (px = Frozen) as -> by done. destruct Hrz as [->|(->&[=])]; tauto.
      * econstructor 5; [| |done..]. all: eapply Hdip2. 2: done. 1: by eapply tree_equal_sym.
    + inversion Hd'; simplify_eq. destruct confl1; last econstructor 1.
      econstructor 7; econstructor; done.
    (* case 3: perm1 and perm2 are unprotected reserved *)
    + by econstructor 3.
    + exfalso. done.
    + by econstructor 3.
    + econstructor 4. 2: done.
      eapply conflicted_transfer_pseudo_disabled.
      eapply tree_equal_transfer_pseudo_disabled. 4: done. all: done.
    + odestruct (trees_equal_transfer_disabled_in_practice_twice Hunq1 Hpma1 Hnac1 Heq12 Heq23) as (ww&Hw1&Hw2&Hw3).
      1: done. econstructor. 1: exact Hw1. 1: exact Hw3. 2: { split; first done. rewrite -Hcell'. done. } simpl in *. done.
    + by econstructor 3.
    + inversion Hd'; simplify_eq; done.
    (* case 4: perm1 and perm2 are pseudo-disabled *)
    + econstructor 4. 1: done.
      eapply tree_equal_transfer_pseudo_disabled. 5: by eapply tree_equal_sym. all: done.
    + econstructor 4. 1: done.
      eapply conflicted_transfer_pseudo_disabled.
      eapply tree_equal_transfer_pseudo_disabled. 5: by eapply tree_equal_sym. all: done.
    + econstructor 4. 1: done.
      eapply conflicted_transfer_pseudo_disabled.
      eapply tree_equal_transfer_pseudo_disabled. 5: by eapply tree_equal_sym. all: done.
    + econstructor 4. all: done. 
    + odestruct (trees_equal_transfer_disabled_in_practice_twice Hunq1 Hpma1 Hnac1 Heq12 Heq23) as (ww&Hw1&Hw2&Hw3).
      1: done. econstructor. 1: exact Hw1. 1: exact Hw3. 1: by simpl in *. rewrite -Hcell'.
      inversion HP1; inversion HP2; done.
    + econstructor 4. 1: done.
      eapply conflicted_transfer_pseudo_disabled.
      eapply tree_equal_transfer_pseudo_disabled. 5: by eapply tree_equal_sym. all: done.
    + econstructor 4. 1: done.
      eapply transfer_pseudo_disabled_notimm.
      1: eapply tree_equal_transfer_pseudo_disabled. 5: by eapply tree_equal_sym. 1-4: done.
      all: inversion Hd'; done.
    (* case 5: perm1 and perm2 are disabled in practice *)
    + odestruct (trees_equal_transfer_disabled_in_practice_twice Hunq1 Hpma1 Hnac1 Heq12 Heq23) as (ww&Hw1&Hw2&Hw3).
      1: done. econstructor. 1: exact Hw1. 1: exact Hw3. 1: by simpl in *. by etransitivity.
    + odestruct (trees_equal_transfer_disabled_in_practice_twice Hunq1 Hpma1 Hnac1 Heq12 Heq23) as (ww&Hw1&Hw2&Hw3).
      1: done. econstructor. 1: exact Hw1. 1: exact Hw3.  1: by simpl in *. by etransitivity.
    + odestruct (trees_equal_transfer_disabled_in_practice_twice Hunq1 Hpma1 Hnac1 Heq12 Heq23) as (ww&Hw1&Hw2&Hw3).
      1: done. econstructor. 1: exact Hw1. 1: exact Hw3.  1: by simpl in *. by etransitivity.
    + odestruct (trees_equal_transfer_disabled_in_practice_twice Hunq1 Hpma1 Hnac1 Heq12 Heq23) as (ww&Hw1&Hw2&Hw3).
      1: done. econstructor. 1: exact Hw1. 1: exact Hw3.  1: by simpl in *. rewrite Hcell.
      inversion HP1'; inversion HP2'; done.
    + odestruct (trees_equal_transfer_disabled_in_practice_twice Hunq1 Hpma1 Hnac1 Heq12 Heq23) as (ww&Hw1&Hw2&Hw3).
      1: done. econstructor. 1: exact Hw1. 1: exact Hw3. 1: simpl in *; congruence. by etransitivity.
    + odestruct (trees_equal_transfer_disabled_in_practice_twice Hunq1 Hpma1 Hnac1 Heq12 Heq23) as (ww&Hw1&Hw2&Hw3).
      1: done. econstructor. 1: exact Hw1. 1: exact Hw3. 1: by simpl in *.
      rewrite Hcell. done.
    + odestruct (trees_equal_transfer_disabled_in_practice_twice Hunq1 Hpma1 Hnac1 Heq12 Heq23) as (ww&Hw1&Hw2&Hw3).
      1: done. econstructor. 1: exact Hw1. 1: exact Hw3. 1: by simpl in *.
      rewrite Hcell. simpl. by inversion Hd'.
    (* case 6: perm1 and perm2 are frozen in practice. *)
    + by econstructor 6.
    + by econstructor 6.
    + by econstructor 6.
    + econstructor 4. 2: done.
      eapply transfer_pseudo_disabled_notimm.
      1: eapply tree_equal_transfer_pseudo_disabled. 5: done. 1-4: done.
      all: done.
    + odestruct (trees_equal_transfer_disabled_in_practice_twice Hunq1 Hpma1 Hnac1 Heq12 Heq23) as (ww&Hw1&Hw2&Hw3).
      1: done. econstructor. 1: exact Hw1. 1: exact Hw3. 1: by simpl in *.
      rewrite -Hcell'. done.
    + by econstructor 6.
    + inversion Hd'; try done.
      simplify_eq. destruct confl1. 2: econstructor 1.
      econstructor 7. econstructor. done.
    (* case 7: the asymmetric case *)
    + by econstructor 7.
    + inversion Hd; simplify_eq. econstructor 2; try done. econstructor 1.
    + inversion Hd; simplify_eq. done.
    + econstructor 4. 2: done.
      eapply transfer_pseudo_disabled_notimm.
      1: eapply tree_equal_transfer_pseudo_disabled. 5: done. 1-4: done.
      all: by inversion Hd.
    + odestruct (trees_equal_transfer_disabled_in_practice_twice Hunq1 Hpma1 Hnac1 Heq12 Heq23) as (ww&Hw1&Hw2&Hw3).
      1: done. econstructor. 1: exact Hw1. 1: exact Hw3. 1: by simpl in *. rewrite -Hcell'. by inversion Hd.
    + eapply trees_equal_transfer_frozen_in_practice_many in HF' as [(Hfip&Hfip2)|(tr&Hdi9p&Hdip2)]. 3-5: eassumption.
      * inversion Hd; simplify_eq. econstructor 6.
        all: edestruct Hfip2 as (px&Hpx&Hrz). 1: by eapply tree_equal_sym.
        enough (px = Frozen) as -> by done. destruct Hrz as [->|(->&[=])]; tauto.
      * econstructor 5. 3: done. 3: by inversion Hd. all: eapply Hdip2. 2: done. 1: by eapply tree_equal_sym.
    + inversion Hd; inversion Hd'; by simplify_eq.
  Qed.

  Lemma item_eq_up_to_C_trans {tr1 tr2 tr3 tg it1 it2 it3} : 
    protected_parents_not_disabled C tr2 →
    (∀ tg, tree_contains tg tr1 → tree_unique tg tr1) →
    (∀ tg, tree_contains tg tr2 → tree_unique tg tr2) →
    parents_more_active tr1 →
    parents_more_active tr2 →
    no_active_cousins C tr1 →
    no_active_cousins C tr2 →
    tree_equal C Forwards tr1 tr2 →
    tree_equal C Forwards tr2 tr3 →
    item_eq_up_to_C C tr1 tr2 tg Forwards it1 it2 →
    item_eq_up_to_C C tr2 tr3 tg Forwards it2 it3 →
    item_eq_up_to_C C tr1 tr3 tg Forwards it1 it3.
  Proof.
    intros Hnd ?????? He1 He2 H1 H2 l.
    destruct (H1 l) as (H1l&H1r), (H2 l) as (H2l&H2r).
    split; first congruence.
    eapply perm_eq_up_to_C_trans. 1-9: done.
    1: exact H1r. rewrite H1l. 1: exact H2r.
  Qed.


  Lemma tree_equal_trans tr1 tr2 tr3 :
    protected_parents_not_disabled C tr2 →
    (∀ tg, tree_contains tg tr1 → tree_unique tg tr1) →
    (∀ tg, tree_contains tg tr2 → tree_unique tg tr2) →
    parents_more_active tr1 →
    parents_more_active tr2 →
    no_active_cousins C tr1 →
    no_active_cousins C tr2 →
    tree_equal C Forwards tr1 tr2 →
    tree_equal C Forwards tr2 tr3 →
    tree_equal C Forwards tr1 tr3.
  Proof.
    rewrite /tree_equal.
    intros ??????? [SameTg1 [SameRel1 EqC1]] [SameTg2 [SameRel2 EqC2]].
    split; [|split].
    + intro tg. rewrite SameTg1 SameTg2 //.
    + intros tg tg'. rewrite SameRel1 SameRel2 //.
    + intros tg Ex.
      destruct (EqC1 _ Ex) as (it1M&it2M&Hlu1M&Hlu2M&Hiteq).
      destruct (EqC2 tg) as (it1R&it2R&Hlu1R&Hlu2R&Hiteq2).
      1: by eapply Hlu2M.
      assert (it2M = it1R) as -> by by eapply tree_lookup_unique.
      exists it1M, it2R. split_and!; [done..|].
      eapply item_eq_up_to_C_trans; done.
  Qed.

  Lemma trees_equal_trans trs1 trs2 trs3 :
    each_tree_protected_parents_not_disabled C trs2 →
    wf_trees trs1 →
    wf_trees trs2 →
    each_tree_parents_more_active trs1 →
    each_tree_parents_more_active trs2 →
    each_tree_no_active_cousins C trs1 →
    each_tree_no_active_cousins C trs2 →
    trees_equal C Forwards trs1 trs2 →
    trees_equal C Forwards trs2 trs3 →
    trees_equal C Forwards trs1 trs3.
  Proof.
    rewrite /trees_equal.
    intros Hu1 Hu2 Hu3 Hu4 Hu5 Hu6 Hu7 Equals1 Equals2 blk.
    specialize (Equals1 blk). specialize (Equals2 blk).
    destruct (trs1 !! blk) as [tr1|] eqn:Heq1;
    destruct (trs2 !! blk) as [tr2|] eqn:Heq2;
    destruct (trs3 !! blk) as [tr3|] eqn:Heq3.
    all: inversion Equals1; inversion Equals2; simplify_eq; first [exfalso; congruence | econstructor].
    eapply tree_equal_trans. 8-9: eassumption.
    2: by eapply Hu2. 1: by eapply Hu1. 1: by eapply Hu3. 1: by eapply Hu4. 1: by eapply Hu5. 1: by eapply Hu6. 1: by eapply Hu7.
  Qed.


End utils.
