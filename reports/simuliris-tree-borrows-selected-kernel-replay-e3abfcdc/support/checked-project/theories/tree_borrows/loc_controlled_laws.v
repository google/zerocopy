From iris.proofmode Require Export proofmode.
From iris.base_logic.lib Require Import ghost_map.
From simuliris.base_logic Require Export gen_sim_prog.
From simuliris.simulation Require Export slsls.
From simuliris.simulation Require Import lifting.
From simuliris.tree_borrows Require Import tkmap_view.
From simuliris.tree_borrows Require Export defs class_instances.
From simuliris.tree_borrows Require Import steps_progress steps_inv.
From simuliris.tree_borrows Require Import tree_access_laws logical_state inv_accessors.
From simuliris.tree_borrows.trees_equal Require Import trees_equal_base random_lemmas.

Lemma loc_controlled_access_outside l tk sc cids σ σ' kind blk off1 sz acc_tg lu_tg b :
  apply_within_trees (memory_access_maybe_nonchildren_only b kind cids acc_tg (off1, sz)) blk σ.(strs) = Some σ'.(strs) →
  shp σ !! l = shp σ' !! l →
  scs σ = scs σ' →
  state_wf σ → 
  ¬ (l.1 = blk ∧ off1 ≤ l.2 < off1 + sz) →
  loc_controlled l lu_tg tk sc σ →
  loc_controlled l lu_tg tk sc σ'.
Proof.
  intros Happly Heq_shp Heq_scs Hwf Hnin Hlc.
  rewrite /loc_controlled.
  destruct tk as [|act|] eqn:Heq; simpl.
  - intros (it & Htrlu & Hperm).
    pose proof Htrlu as Htrlu2.
    eapply apply_trees_access_lookup_outside_rev in Htrlu2; [|eapply Happly|eapply Hwf|done].
    destruct Htrlu2 as (itold & Hluold & Heq1 & Heq2 & Heq3).
    destruct Hlc as (Hownold & Hscold).
    + exists itold. split; first done. by rewrite Heq3.
    + split; last by rewrite -Heq_shp.
      destruct Hluold as (trold & Htrold & Hluold).
      destruct Hownold as (itold2 & trold2 & Hluold2 & Hluold2' & Hisinit & Hsame & Hothers).
      assert (trold2 = trold) as -> by congruence.
      assert (itold2 = itold) as -> by by eapply tree_lookup_unique.
      destruct Htrlu as (trnew & Htrnew & Hlunew).
      exists it, trnew. do 2 (split; first done).
      split; first by rewrite -Heq3.
      split; first by rewrite -Heq3.
      intros itnew' t' Hit'.
      assert (trees_lookup (strs σ') l.1 t' itnew') as Hit'' by by exists trnew.
      eapply apply_trees_access_lookup_outside_rev in Hit''; [|eapply Happly|eapply Hwf|done].
      destruct Hit'' as (itold' & (x & Hx & Hitoldlu') & HHHH).
      assert (x = trold) as -> by congruence.
      specialize (Hothers _ _ Hitoldlu').
      assert (rel_dec trnew lu_tg t' = rel_dec trold lu_tg t') as Hreldec.
      { destruct (decide (l.1 = blk)) as [<- | Hne].
        - rewrite /apply_within_trees Hx /= in Happly.
          apply bind_Some in Happly as (newtr & H1 & [= H2]).
          rewrite -H2 lookup_insert_eq in Htrnew.
          erewrite (access_same_rel_dec H1). congruence.
        - apply bind_Some in Happly as (itwrong & Hwrong & (y & Hy & [= Hacc])%bind_Some).
          rewrite -Hacc lookup_insert_ne // Hx in Htrnew. congruence. }
      rewrite rel_dec_flip2 in Hothers. rewrite rel_dec_flip2.
      rewrite Hreldec. destruct HHHH as (Hinit2 & Hprot2 & Hperm2). rewrite -Hperm2. apply Hothers.
  - intros (it & Htrlu & Hperm).
    pose proof Htrlu as Htrlu2.
    eapply apply_trees_access_lookup_outside_rev in Htrlu2; [|eapply Happly|eapply Hwf|done].
    destruct Htrlu2 as (itold & Hluold & Heq1 & Heq2 & Heq3).
    destruct Hlc as (Hownold & Hscold). 
    + exists itold. split; first done. by rewrite Heq3.
    + split; last by rewrite -Heq_shp.
      destruct Hluold as (trold & Htrold & Hluold). rewrite /bor_state_own /= in Hownold.
      destruct Hownold as (itold2 & trold2 & Hluold2 & Hluold2' & Hisinit & Hsame & Hothers).
      assert (trold2 = trold) as -> by congruence.
      assert (itold2 = itold) as -> by by eapply tree_lookup_unique.
      destruct Htrlu as (trnew & Htrnew & Hlunew).
      exists it, trnew. do 2 (split; first done).
      split_and!; first by rewrite -Heq3.
      split.
      { intros Hfrz. ospecialize (Hsame _). 1: by rewrite Heq3 Heq_scs Heq2. by rewrite -Heq3. }
      intros itnew' t' Hit'.
      assert (trees_lookup (strs σ') l.1 t' itnew') as Hit'' by by exists trnew.
      eapply apply_trees_access_lookup_outside_rev in Hit''; [|eapply Happly|eapply Hwf|done].
      destruct Hit'' as (itold' & (x & Hx & Hitoldlu') & HHHH).
      assert (x = trold) as -> by congruence.
      specialize (Hothers _ _ Hitoldlu').
      assert (rel_dec trnew lu_tg t' = rel_dec trold lu_tg t') as Hreldec.
      { destruct (decide (l.1 = blk)) as [<- | Hne].
        - rewrite /apply_within_trees Hx /= in Happly.
          apply bind_Some in Happly as (newtr & H1 & [= H2]).
          rewrite -H2 lookup_insert_eq in Htrnew.
          erewrite (access_same_rel_dec H1). congruence.
        - apply bind_Some in Happly as (itwrong & Hwrong & (y & Hy & [= Hacc])%bind_Some).
          rewrite -Hacc lookup_insert_ne // Hx in Htrnew. congruence. }
      rewrite rel_dec_flip2 in Hothers. rewrite rel_dec_flip2.
      rewrite Hreldec. destruct HHHH as (Hinit2 & Hprot2 & Hperm2). rewrite -Hperm2.
      destruct (rel_dec trold lu_tg t') as [[]|[]]; simpl in *. 1,3,4: eapply Hothers.
      destruct Hothers as [Heff|Hothers]; first by left. right.
      destruct (perm (item_lookup itold' l.2)) as [|?| | | |]; try done.
      * destruct Hothers as [H|H]; try eauto.
        right. by rewrite -Heq2 -Heq3 -Heq_scs.
      * destruct Hothers as [H|H]; try eauto.
        right. by rewrite -Heq2 -Heq3 -Heq_scs.
  - destruct Hlc as (Hownold & Hscold); first done.
    split; last by rewrite -Heq_shp.
    destruct Hownold as (itold & trold & Hluold & Htrold & Hisinit & Hsame & Hnoprot & Hothers).
    assert (trees_lookup σ.(strs) l.1 lu_tg itold) as Hsluold by by exists trold.
    eapply apply_trees_access_lookup_outside in Hsluold; [|eapply Happly|eapply Hwf|done].
    destruct Hsluold as (itnew & (trnew & Htrnew & Hlunew) & (Hinitold & Hprotold & Hpermold)).
    exists itnew, trnew. do 2 (split; first done).
    split; first by rewrite -Hpermold.
    split; first by rewrite -Hpermold.
    split; first by rewrite -Hprotold.
    intros it' t' Hluit'.
    assert (wf_tree trnew) as Hwfnew.
    { destruct (decide (l.1 = blk)) as [<-|Hne].
      - rewrite /apply_within_trees Htrold /= in Happly.
        eapply bind_Some in Happly as (? & H1 & [= H2]).
        rewrite -H2 lookup_insert_eq in Htrnew.
        injection Htrnew as ->. eapply memory_access_wf; last done.
        destruct Hwf as [_ Hwf _ _]. by eapply Hwf.
      - eapply bind_Some in Happly as (? & H1 & (? & H2 & [= H3])%bind_Some).
        rewrite -H3 lookup_insert_ne // in Htrnew.
        destruct Hwf as [_ Hwf _ _]. by eapply Hwf.
    }
    assert (tree_unique t' trnew) as Hunq.
    { eapply wf_tree_tree_unique. 2: apply Hluit'. done. }
    assert (tree_unique t' trold) as Hunqold.
    { destruct (decide (l.1 = blk)) as [<-|Hne].
      - rewrite /apply_within_trees Htrold /= in Happly.
        eapply bind_Some in Happly as (? & H1 & [= H2]).
        rewrite -H2 lookup_insert_eq in Htrnew.
        injection Htrnew as ->. rewrite /tree_unique.
        by erewrite tree_apply_access_same_count.
      - eapply bind_Some in Happly as (? & H1 & (? & H2 & [= H3])%bind_Some).
        rewrite -H3 lookup_insert_ne // Htrold in Htrnew. congruence.
    }
    eapply unique_exists in Hunqold as Hextold.
    eapply unique_lookup in Hunqold as (it & Hitdet).
    eapply Hothers. done.
Qed.

(* not generalized to maybe_nonchildren_only since this one is specific *)
Lemma loc_controlled_write_becomes_active l sc σ σ' blk off1 sz tg vls scold tkkold:
  apply_within_trees (memory_access AccessWrite σ.(scs) tg (off1, sz)) blk σ.(strs) = Some σ'.(strs) →
  (write_mem (blk, off1) vls (shp σ)) = shp σ' →
  scs σ = scs σ' →
  state_wf σ →
  l.1 = blk →
  length vls = sz →
  trees_contain tg (strs σ) blk →
  list_to_heaplet vls off1 !! l.2 = Some sc →
  loc_controlled l tg (tk_unq tkkold) scold σ →
  loc_controlled l tg (tk_unq tk_act) sc σ'.
Proof.
  intros Happly Heq_shp Heq_scs Hwf Hblk Hsz Hcontain Hsc Hold.
  assert (shp σ' !! l = Some sc) as Hheap.
  { rewrite -Heq_shp /=.
    destruct (write_mem_lookup_case (blk, off1) vls (shp σ) l) as [(i&Hil&->&HH)|(Hwrong&_)].
    2: { eapply list_to_heaplet_lookup_Some in Hsc. exfalso.
         eapply (Hwrong (Z.to_nat (l.2 - off1))); first lia.
         eapply injective_projections; first done.
         simpl. lia. }
    rewrite HH. rewrite list_to_heaplet_nth // in Hsc. }
  assert (wf_trees σ.(strs)) as Hwf_pre by eapply Hwf.
  assert (wf_trees σ'.(strs)) as Hwf_post.
  { eapply apply_within_trees_wf; try done.
    eapply memory_access_tag_count. }
  pose proof Happly as Happlys.
  eapply bind_Some in Happly as (trold & Htrold & (trnew&Haccess&[= Hstrs])%bind_Some).
  rewrite /trees_contain /trees_at_block Htrold in Hcontain.
  eapply wf_tree_tree_unique in Hcontain as Hunique; last by eapply Hwf_pre.
  eapply unique_lookup in Hunique as (itold & Hdet).
  assert (tree_lookup trold tg itold) as Hitold by done.
  assert (off1 ≤ l.2 < off1 + sz) as Hinbound.
  { subst sz. by eapply list_to_heaplet_lookup_Some. }
  eapply apply_trees_access_lookup_general in Happlys as Happlyself.
  2: done. 3: by exists trold. 2: eassumption.
  destruct Happlyself as (itnew & Hlunew & _ & _ & Happlyself).
  intros _. split; last done.
  rewrite -Hstrs /trees_lookup lookup_insert_eq in Hlunew.
  destruct Hlunew as (?&[= <-]&Hlunew).
  exists itnew, trnew.
  split; first done.
  split; first rewrite -Hstrs Hblk lookup_insert_eq //.


  assert ((perm (item_lookup itnew l.2) = Active ∨ perm (item_lookup itold l.2) = Cell) ∧ initialized (item_lookup itnew l.2) = PermInit ∧ bor_state_pre l tg (tk_unq tkkold) σ ∧ ((initialized (item_lookup itold l.2) = PermInit → perm (item_lookup itold l.2) = Frozen → protector_is_active (iprot itold) (scs σ)))) as (Hactive&Hisinit&Hpre2&Hpre3).
  { eapply bind_Some in Happlyself as (prm&Hperm1&(pv&Hperm2&[= <-])%bind_Some).
    simpl in Hperm1,Hperm2|-*. rewrite trees_rel_dec_refl /= in Hperm1|-*.
    rewrite most_init_comm.
    pose (ppo := item_lookup itold l.2). fold ppo.
    enough ((pv = Active ∨ perm ppo = Cell) ∧ (initialized ppo = PermInit → perm (ppo) ≠ Disabled) ∧ (initialized ppo = PermInit → perm ppo = Frozen → protector_is_active (iprot itold) (scs σ))) as (H1&H2&H3).
    { split; first done. simpl. rewrite /bor_state_pre_unq. split; first done.
      eexists. 2: done. eexists. split; last apply H2.
      eexists; by subst blk. } subst ppo.
    repeat case_match; simplify_eq; (split; [|done]); first [by left|by right]. }
  destruct (Hold Hpre2) as ((it'&tr'&Htr'&Hlu'&_&Hrst)&_).
  assert (tr' = trold) as ->.
  { rewrite Hblk Htrold in Hlu'. congruence. }
  split; first done.
  destruct Hactive as [Hactive|Hcell].
  2: { destruct Hrst as [Hrst _]. eapply tree_lookup_unique in Htr'; last exact Hitold. subst it'.
       rewrite !Hcell in Hrst. exfalso; by eapply Hrst. }
  split.
  { intros _. by rewrite Hactive. }
  destruct Hrst as (_&Holdothers).
  intros itmod tmod Hlumod.
  eapply apply_trees_access_lookup_general_rev in Happlys as Happlys'.
  2: done. 2: eassumption. 2: { exists trnew; split; last exact Hlumod. rewrite -Hstrs lookup_insert_eq //. }
  destruct Happlys' as (itold' & (tr'&Htr''&Hluold) & HX1 & HX2 & Hperm).
  assert (tr' = trold) as ->.
  { rewrite Htrold in Htr''. congruence. }
  specialize (Holdothers _ _ Hluold).
  rewrite /trees_rel_dec Htrold /= /apply_access_perm /= /apply_access_perm_inner in Hperm.
  erewrite <-access_same_rel_dec; last done. clear Happlyself.
  rewrite rel_dec_flip2 in Holdothers|-*.
  eapply bind_Some in Hperm as (prm&Hperm1&(pv&Hperm2&[= Hrev])%bind_Some).
  rewrite /= in Hperm1,Hperm2|-*.
  destruct (rel_dec trold tg tmod) as [[[]|]|[|]] eqn:Hreldec; simpl in *.
  3: { destruct Holdothers as [Heff|Holdothers].
       1: left; by rewrite -Hrev Heff /=.
       rewrite -Hrev /=. assert (prm = pv) as ->. { clear -Hperm2. repeat case_match; by simplify_eq. }
       right. destruct (perm (item_lookup itold' l.2)) as [|?| | | |]; simplify_eq; try done.
       rewrite bool_decide_decide in Hperm1. rewrite -Heq_scs. destruct (decide (protector_is_active (iprot itmod) (scs σ))).
       all: simplify_eq. 1: done. done. } 
  all: rewrite -?Hrev; destruct (perm (item_lookup itold' l.2)) as [|[]| | | |], (initialized (item_lookup itold' l.2)) as [];
    repeat (simpl; try simpl in Hperm1; try simpl in Holdothers; simplify_eq; try simpl in Hperm2; try done; destruct bool_decide).
  simpl in *. congruence.
Qed.

Lemma loc_controlled_write_invalidates_others l sc σ σ' blk off1 sz tg_acc tg_lu tk A:
  apply_within_trees (memory_access AccessWrite σ.(scs) tg_acc (off1, sz)) blk σ.(strs) = Some σ'.(strs) →
  scs σ = scs σ' →
  state_wf σ →
  l.1 = blk →
  (off1 ≤ l.2 < off1 + sz) →
  tg_acc ≠ tg_lu →
  trees_contain tg_acc σ.(strs) blk →
  loc_controlled l tg_lu tk sc σ →
  bor_state_pre l tg_lu tk σ' →
  A. (* false *)
Proof.
  intros Happly Heq_scs Hwf Hblk Hsz Htgne Htgin Hcontrol Hpre.
  subst blk. exfalso.
  pose proof Happly as (trold&Htrold&(trnew&Haccess&[= Hstrs])%bind_Some)%bind_Some.
  assert (strs σ' !! l.1 = Some trnew) as Htrnew.
  { by rewrite -Hstrs lookup_insert_eq. }
  destruct tk as [|tkk|].
  - destruct Hpre as (itnew&(trnew'&Htrnew'&Hitnew)&Hnondis).
    assert (trnew' = trnew) as -> by congruence. clear Htrnew'.
    eapply apply_trees_access_lookup_general_rev in Happly as Hitrev.
    2: apply Hwf. 2: eassumption. 2: exists trnew; split; first done; last exact Hitnew.
    destruct Hitrev as (itold & (trold' & Htrold' & Hitold) & Hinitit & Hprotit & Hpermit).
    assert (trold' = trold) as -> by congruence. clear Htrold'.
    destruct Hcontrol as (Hcontrol&_).
    { exists itold. split; first by eexists.
      intros Hini Hdis.
      pose proof Hpermit as (x1&Hx1&(x2&Hx2&[=Hx3])%bind_Some)%bind_Some.
      rewrite -Hx3 /= Hini /= in Hnondis. eapply Hnondis; first done. rewrite !Hdis in Hx1. simpl.
      assert (x1 = x2) as ->. 1: destruct (most_init _ _), bool_decide; simplify_eq; try done; destruct x1; by simplify_eq.
      clear Hx2.
      rewrite /apply_access_perm_inner in Hx1. destruct trees_rel_dec; by simplify_eq. }
    destruct Hcontrol as (itold' & trold' & Hitold' & Htrold' & Hisinit & Hfrozen & Hothers).
    assert (trold' = trold) as -> by congruence. clear Htrold'.
    assert (itold' = itold) as -> by by eapply tree_lookup_unique. clear Hitold'.
    (* old perm is frozen, it can not have survived the write *)
    pose proof Hpermit as (x1&Hx1&(x2&Hx2&[=Hx3])%bind_Some)%bind_Some.
    rewrite Hfrozen /= in Hx1. destruct (trees_rel_dec (strs σ) l.1 tg_acc tg_lu); try done.
    pose proof Hx1 as [= <-].
    assert (x2 = Disabled) as -> by (destruct (most_init _ _), bool_decide; simplify_eq; done).
    rewrite -Hx3 Hisinit in Hnondis. by eapply Hnondis.
  - destruct Hpre as (itnew&(trnew'&Htrnew'&Hitnew)&Hnondis). 
    assert (trnew' = trnew) as -> by congruence. clear Htrnew'.
    eapply apply_trees_access_lookup_general_rev in Happly as Hitrev.
    2: apply Hwf. 2: eassumption. 2: exists trnew; split; first done; last exact Hitnew.
    destruct Hitrev as (itold & (trold' & Htrold' & Hitold) & Hinitit & Hprotit & Hpermit).
    assert (trold' = trold) as -> by congruence. clear Htrold'.
    destruct Hcontrol as (Hcontrol&_).
    { exists itold. split; first by eexists.
      pose proof Hpermit as (x1&Hx1&(x2&Hx2&[=Hx3])%bind_Some)%bind_Some.
      rewrite /apply_access_perm_inner in Hx1.
      rewrite -Hx3 /most_init /= in Hnondis.
      rewrite bool_decide_decide in Hx1,Hx2.
      destruct trees_rel_dec as [[]|[]], (perm (item_lookup itold l.2)), (initialized (item_lookup itold l.2)) as []; simpl in Hx2; simplify_eq; try done.
      all: try specialize (Hnondis eq_refl).
      all: (try destruct decide); try by simplify_eq. }
    destruct Hcontrol as (itold' & trold' & Hitold' & Htrold' & Hisinit & Hsame & Hothers).
    assert (trold' = trold) as -> by congruence. clear Htrold'.
    assert (itold' = itold) as -> by by eapply tree_lookup_unique. clear Hitold'.
    rewrite /trees_contain /trees_at_block Htrold in Htgin.
    pose proof Htgin as Hunq%wf_tree_tree_unique.
    2: by eapply (state_wf_tree_unq _ Hwf).
    pose proof Hunq as (itaccold&Hdet)%unique_lookup.
    assert (tree_lookup trold tg_acc itaccold) as Hitaccold by done.
    ospecialize (Hsame _).
    { pose proof Hpermit as (x1&Hx1&(x2&Hx2&[=Hx3])%bind_Some)%bind_Some.
      rewrite /apply_access_perm_inner in Hx1.
      rewrite -Hx3 /most_init /= in Hnondis.
      rewrite bool_decide_decide in Hx1,Hx2.
      destruct trees_rel_dec as [[]|[]], (perm (item_lookup itold l.2)), (initialized (item_lookup itold l.2)) as []; simpl in Hx2; simplify_eq; try done.
      all: try specialize (Hnondis eq_refl).
      all: (try destruct decide); try by simplify_eq. }
    destruct (rel_dec trold tg_acc tg_lu) as [foreignpos|[isimm|]] eqn:Hreldec.
    + eapply apply_trees_access_lookup_general in Happly as Hitrev.
      2: apply Hwf. 2: eassumption. 2: exists trold; split; first done; last exact Hitaccold.
      destruct Hitrev as (itaccnew & (trnew' & Htrnew' & Hitaccnew) & Hinititacc & Hprotitacc & Hpermitacc).
      assert (trnew' = trnew) as -> by congruence. clear Htrnew'.
      rewrite trees_rel_dec_refl in Hpermitacc.
      specialize (Hothers _ _ Hitaccold).
      pose proof Hpermit as (x1&Hx1&(x2&Hx2&[=Hx3])%bind_Some)%bind_Some. clear Hpermit.
      pose proof Hpermitacc as (y1&Hy1&(y2&Hy2&[=Hy3])%bind_Some)%bind_Some. clear Hpermitacc.
      rewrite /apply_access_perm_inner in Hx1,Hy1.
      rewrite -!Hx3 -!Hprotit -?Heq_scs /= in Hnondis Hx1 Hx2.
      rewrite /trees_rel_dec Htrold in Hx1.
      rewrite !bool_decide_decide in Hx1,Hx2,Hy1,Hy2.
      rewrite Hreldec in Hx1,Hothers.
      destruct foreignpos as [pp|].
      all: destruct (perm (item_lookup itold l.2)) as [|[]| | | |], 
                    (initialized (item_lookup itold l.2)) as []; 
             simpl in *; simplify_eq; try done.
      all: repeat (destruct decide; simplify_eq; try done).
      all: destruct (perm (item_lookup itaccold l.2)) as [|[]| | | |], 
                    (initialized (item_lookup itaccold l.2)) as []; 
             simpl in *; simplify_eq; try specialize (Hnondis eq_refl); try destruct Hsame as (?&?&?); try done.
    + pose proof Hreldec as HH.
      rewrite /rel_dec in HH.
      edestruct (decide (ParentChildIn _ _ _)) as [HPC|]; last done.
      edestruct (decide (ParentChildIn _ _ _)) as [|HNPC]; first done.
      injection HH as Hisimm.
      eapply lookup_implies_contains in Hitold as Hluin.
      assert (StrictParentChildIn tg_lu tg_acc trold) as HSPC.
      { destruct HPC; last done. subst tg_lu. rewrite rel_dec_refl in Hreldec; done. }
      eapply immediate_sandwich in HSPC as (tsw&H1&H2).
      2-3: by eapply Hwf.
      eapply contains_child in Hluin as Htwin.
      2: right; by eapply Immediate_is_StrictParentChild.
      destruct (@unique_implies_lookup tsw trold) as (itsw&Hitswold).
      1: by eapply Hwf.
      eapply apply_trees_access_lookup_general in Happly as Hitrev.
      2: apply Hwf. 2: eassumption. 2: exists trold; split; first done; last exact Hitswold.
      destruct Hitrev as (itswnew & (trnew' & Htrnew' & Hitswnew) & Hinititsw & Hprotitsw & Hpermitsw).
      assert (trnew' = trnew) as -> by congruence. clear Htrnew'.
      specialize (Hothers _ _ Hitswold).
      rewrite /trees_rel_dec Htrold in Hpermitsw.
      rewrite /rel_dec decide_True // /maybe_non_children_only /= in Hpermitsw.
      rewrite /rel_dec decide_True // /= in Hothers.
      2: right; by eapply Immediate_is_StrictParentChild.
      rewrite /rel_dec decide_False // /= in Hothers.
      2: { intros HH. eapply immediate_parent_not_child. 4: exact HH. 3: done.
           all: eapply Hwf; first done. all: done. }
      rewrite decide_True // /= in Hothers.
      pose proof Hpermitsw as (y1&Hy1&(y2&Hy2&[=Hy3])%bind_Some)%bind_Some. clear Hpermitsw.
      rewrite /apply_access_perm Hothers /= in Hy1. done.
    + eapply Htgne, rel_this_antisym. 3: done. 2: apply Hitold. done.
  - destruct Hcontrol as ((itold&trold'&Hitold&Htrold'&Hactive&Hunq)&_); first done.
    assert (trold' = trold) as -> by congruence. clear Htrold'.
    rewrite /trees_contain /trees_at_block Htrold in Htgin.
    pose proof Htgin as Htgunq%wf_tree_tree_unique.
    2: by eapply (state_wf_tree_unq _ Hwf).
    pose proof Htgunq as (itaccold&Hdet)%unique_lookup.
    assert (tree_lookup trold tg_acc itaccold) as Hitaccold by done.
    eapply Htgne; symmetry. eapply Hunq; try done.
Qed.

Definition pointer_kind_to_tag_unprotected (pk : pointer_kind) (im : interior_mut) : option tag_kind := match im with
  InteriorMut => None (* for ShrRef, this does not actually create tags. For the others, we can not allow surviving foreign writes *)
| _ => match pk with ShrRef => Some tk_pub | Box | MutRef => Some (tk_unq tk_res) end end.

Definition pointer_kind_to_tag_protected (pk : pointer_kind) (im : interior_mut) : option tag_kind := match pk with
  Box | MutRef => Some (tk_unq tk_res) (* for protected, IM will become ty_frz *)
| ShrRef => match im with InteriorMut => None | _ => Some (tk_pub) end end.

Definition pointer_kind_to_tag_maybe_protected pk im rk : option tag_kind := match rk with
  Default => pointer_kind_to_tag_unprotected pk im
| FnEntry => pointer_kind_to_tag_protected pk im end.


Lemma pointer_kind_to_tag_maybe_protected_spec pk im rk tk :
  pointer_kind_to_tag_maybe_protected pk im rk = Some tk →
  (pk = ShrRef ∧ im = TyFrz ∧ tk = tk_pub ∨ 
  ((pk = Box ∨ pk = MutRef) ∧ tk = tk_unq tk_res ∧ retag_perm pk im rk = Some (Reserved ResActivable))).
Proof.
  destruct pk, im, rk; simpl; intros H; simplify_eq; eauto 10.
Qed.

Lemma if_both_sides_same {T} (b:bool) (t:T) : (if b then t else t) = t.
Proof. by destruct b. Qed.

Lemma loc_controlled_read_after_reborrow_creates cids l sc tg_cld tg_par tk σ σ' pk im rk trs1 cc blk off1 sz:
  apply_within_trees (create_child cids tg_par tg_cld pk im rk cc) blk σ.(strs) = Some trs1 →
  apply_within_trees (memory_access AccessRead cids tg_cld (off1, sz)) blk trs1 = Some σ'.(strs) →
  state_wf σ → wf_trees trs1 →
  l.1 = blk →
  trees_contain tg_par (strs σ) blk →
  ¬ trees_contain tg_cld (strs σ) blk →
  shp σ' !! l = Some sc →
  off1 ≤ l.2 < off1 + sz →
  cc ∈ σ'.(scs) →
  pointer_kind_to_tag_maybe_protected pk im rk = Some tk →
  loc_controlled l tg_cld tk sc σ'.
Proof.
  intros Hcreate Happly Hwf Hwf1 Hblk Hcont Hncont Hhp Hbound Hscs Htk.
  intros _. split; last done.
  eapply bind_Some in Hcreate as (tr&Htr&(tr1&Hcreate&[= Htr1])%bind_Some).
  eassert (∃ it, _ = Some it ∧ trees_lookup trs1 blk tg_cld it) as (itcld&Hitcld&Hlucld1).
  { subst trs1. rewrite /trees_lookup /= lookup_insert_eq /=.
    odestruct create_child_determined as (it&Hit&HHit). 4: exists it; split; [eexact Hit|].
    4: eexists; split; first done; eexact HHit. 3: exact Hcreate.
    all: rewrite /trees_contain /trees_at_block Htr // in Hcont,Hncont. }
  eapply apply_trees_access_lookup_general in Happly as Happlyself.
  2: done. 3: apply Hlucld1. 2: exact Hbound.
  destruct Happlyself as (itcld'&Hitcld'&Hinitcld&Hiprotcld&Haccesscld).
  eapply bind_Some in Hitcld as (pp&Hpp&[= <-]).
  rewrite /= trees_rel_dec_refl -Hiprotcld /= {1} /item_lookup lookup_empty /= in Haccesscld.
  rewrite /apply_access_perm /= in Haccesscld.
  assert (∀ T (k:option T), match pp with Disabled => None | _ => k end = k) as Hmatch1.
  1: by destruct pp.
  rewrite Hmatch1 /= Hmatch1 /= if_both_sides_same /= in Haccesscld. clear Hmatch1.
  injection Haccesscld as Haccesscld.
  destruct Hitcld' as (tr'&Htr'&Hitcld').
  destruct (pointer_kind_to_tag_maybe_protected_spec _ _ _ _ Htk) as [(->&->&->)|(H&->&Hrp)].
  - eexists itcld', tr'. split; first done. split; first by congruence.
    rewrite /bor_state_own_on. cbv in Hpp. injection Hpp as <-.
    rewrite -Haccesscld; simpl. do 2 (split; first done).
    intros ito' to Hito'.
    eapply apply_trees_access_lookup_general_rev in Happly as Happlyself.
    2: done. 3: exists tr'; split; first congruence; exact Hito'. 2: exact Hbound.
    destruct Happlyself as (ito&Hito&Hinito&Hiproto&Haccesso).
    rewrite /trees_rel_dec -Htr1 lookup_insert_eq /= in Haccesso.
    erewrite (memory_access_same_rel_dec false) in Haccesso.
    2: { eapply bind_Some in Happly as (x&Hx&(y&Hy&[= HH])%bind_Some).
         rewrite -Htr1 lookup_insert_eq in Hx. assert (x = tr1) as -> by congruence.
         rewrite -HH lookup_insert_eq in Htr'. assert (y = tr') as -> by congruence.
         exact Hy. }
    rewrite rel_dec_flip2 /apply_access_perm in Haccesso.
    eapply bind_Some in Haccesso as (p1&Hp1&(p2&Hp2&[= HH])%bind_Some).
    rewrite /apply_access_perm_inner in Hp1.
    destruct (rel_dec tr' to tg_cld) as [[]|[]], (perm (item_lookup ito l.2)) as [|[]| | | |], (bool_decide (protector_is_active (iprot ito') cids)).
    all: simpl in Hp1; try discriminate Hp1; injection Hp1 as <-.
    all: destruct (initialized (item_lookup ito l.2)); simpl in Hp2; try discriminate Hp2; injection Hp2 as <-.
    all: try done. all: rewrite -HH; simpl; done.
  - eexists itcld', tr'. split; first done. split; first by congruence.
    rewrite Hrp in Hpp. injection Hpp as <-.
    rewrite /bor_state_own_on /bor_state_post_unq -Haccesscld; simpl. split; first done. split; first done.
    intros ito' to Hito'.
    eapply apply_trees_access_lookup_general_rev in Happly as Happlyself.
    2: done. 3: exists tr'; split; first congruence; exact Hito'. 2: exact Hbound.
    destruct Happlyself as (ito&Hito&Hinito&Hiproto&Haccesso).
    rewrite /trees_rel_dec -Htr1 lookup_insert_eq /= in Haccesso.
    erewrite <- (memory_access_same_rel_dec false).
    2: { eapply bind_Some in Happly as (x&Hx&(y&Hy&[= HH])%bind_Some).
         rewrite -Htr1 lookup_insert_eq in Hx. assert (x = tr1) as -> by congruence.
         rewrite -HH lookup_insert_eq in Htr'. assert (y = tr') as -> by congruence.
         exact Hy. }
    rewrite rel_dec_flip2 /apply_access_perm in Haccesso.
    eapply bind_Some in Haccesso as (p1&Hp1&(p2&Hp2&[= HH])%bind_Some).
    rewrite /apply_access_perm_inner in Hp1.
    destruct (rel_dec tr1 to tg_cld) as [[]|pos] eqn:Hreldec.
    3: { rewrite /rel_dec in Hreldec. destruct (decide (ParentChildIn tg_cld to tr1)) as [Hc|]; last done.
         destruct (decide (ParentChildIn to tg_cld tr1)) as [Hc2|Hc2].
         1: by injection Hreldec as <-.
         exfalso. eapply insertion_order_nonparent. 4: done. 4: exact Hc.
         - destruct Hito as (tr1X&HX&Hito). assert (tr1X = tr1) as ->.
           { rewrite -Htr1 lookup_insert_eq in HX. congruence. }
           eapply insertion_minimal_tags. 3: done. 2: eapply Hito.
           simpl. intros ->. eapply Hc2. by left.
         - intros Hx. eapply Hncont. by rewrite /trees_contain /trees_at_block Htr.
         - by rewrite /trees_contain /trees_at_block Htr in Hcont. }
    2: enough (match perm (item_lookup ito' l.2) with Active => False | _ => True end) as Heno.
    2: { eapply bind_Some in Happly as (X&HX&(Y&Happly&[= HY])%bind_Some).
         assert (X = tr1) as ->. { rewrite -Htr1 lookup_insert_eq // in HX; congruence. }
         assert (Y = tr') as ->. { rewrite -HY lookup_insert_eq /= in Htr'; congruence. }
         destruct (perm (item_lookup ito' l.2)) as [|?| | | |] eqn:Heq; simpl. all: try done. all: try by right.
         all: right; tauto. }
    all: destruct (perm (item_lookup ito l.2)) as [|[]| | | |], (bool_decide (protector_is_active (iprot ito') cids)).
    all: simpl in Hp1; try discriminate Hp1; injection Hp1 as <-.
    all: destruct (initialized (item_lookup ito l.2)); simpl in Hp2; try discriminate Hp2; injection Hp2 as <-.
    all: try done. all: rewrite -HH; simpl; try done; tauto.
Qed.

Lemma create_child_tree_lookup C tg_par tg_cld pk im rk cc tr tr' tg it :
  tg ≠ tg_cld →
  create_child C tg_par tg_cld pk im rk cc tr = Some tr' →
  tree_lookup tr tg it ↔ tree_lookup tr' tg it.
Proof.
  intros Hne (iit&Hiit%new_item_has_tag&[= <-])%bind_Some.
  split; intros (Hcont&Hdet); split.
  - by eapply insert_preserves_exists.
  - setoid_rewrite <- insert_true_preserves_every; first done.
    simpl. congruence.
  - eapply insert_false_infer_exists; last done. simpl. congruence.
  - setoid_rewrite insert_true_preserves_every; first done.
    simpl. congruence.
Qed.

Lemma create_child_tree_lookup_new C tg_par tg_cld pk im rk cc tr tr' it :
  tree_contains tg_par tr → ¬ tree_contains tg_cld tr →
  create_child C tg_par tg_cld pk im rk cc tr = Some tr' →
  tree_lookup tr' tg_cld it → Some it = create_new_item tg_cld pk im rk cc.
Proof.
  intros Hin Hnin (it2&Hit2&[= <-])%bind_Some Hlu.
  rewrite Hit2. f_equal.
  eapply tree_lookup_unique. 1: eapply Hlu.
  split.
  - eapply insert_true_produces_exists. 1: by eapply new_item_has_tag.
    eapply Hin.
  - eapply inserted_determined. 1: by eapply new_item_has_tag. done.
Qed.

Lemma create_child_tree_lookup_general C tg_par tg_cld pk im rk cc tr tr' tg it :
  tree_contains tg_par tr → ¬ tree_contains tg_cld tr →
  create_child C tg_par tg_cld pk im rk cc tr = Some tr' →
  tree_lookup tr' tg it → tg ≠ tg_cld ∧ tree_lookup tr tg it ∨ tg = tg_cld ∧ Some it = create_new_item tg_cld pk im rk cc.
Proof.
  intros Hin Hnin Hcc Hlu. destruct (decide (tg = tg_cld)) as [->|Hne].
  - right. split; first done. by eapply create_child_tree_lookup_new.
  - left. split; first done. by eapply create_child_tree_lookup.
Qed.

Lemma create_child_rel_dec tg1 tg2 C tg_par tg_cld pk im rk cc tr tr' :
  tg1 ≠ tg_cld → tg2 ≠ tg_cld →
  create_child C tg_par tg_cld pk im rk cc tr = Some tr' →
  rel_dec tr tg1 tg2 = rel_dec tr' tg1 tg2.
Proof.
  intros Hn1 Hn2 (it&Hit&[= <-])%bind_Some.
  eapply new_item_has_tag in Hit as HH; subst tg_cld.
  rewrite /rel_dec /=.
  destruct (decide (ParentChildIn tg2 tg1 tr)) as [HPC1|HPC1].
  all: setoid_rewrite (insert_eqv_rel _ _ it) in HPC1; [|done..].
  all: try erewrite (decide_True _ _ HPC1); try erewrite (decide_False _ _ HPC1).
  all: f_equal.
  all: destruct (decide (ParentChildIn tg1 tg2 tr)) as [HPC2|HPC2].
  all: setoid_rewrite (insert_eqv_rel _ _ it) in HPC2; [|done..].
  all: try erewrite (decide_True _ _ HPC2); try erewrite (decide_False _ _ HPC2).
  all: f_equal.
  1: destruct (decide (ImmediateParentChildIn tg2 tg1 tr)) as [HPC3|HPC3].
  3: destruct (decide (ImmediateParentChildIn tg1 tg2 tr)) as [HPC3|HPC3].
  all: setoid_rewrite (insert_eqv_imm_rel _ _ it) in HPC3; [|done..].
  all: try erewrite (decide_True _ _ HPC3); try erewrite (decide_False _ _ HPC3).
  all: f_equal.
Qed.

Lemma create_child_rel_dec_new tg1 tg2 C tg_par tg_cld pk im rk cc tr tr' rr :
  wf_tree tr → wf_tree tr' →
  tree_contains tg_par tr → ¬ tree_contains tg_cld tr → tree_contains tg2 tr' →
  create_child C tg_par tg_cld pk im rk cc tr = Some tr' →
  rel_dec tr' tg1 tg2 = rr →
  tg2 ≠ tg_cld →
  (tg1 ≠ tg_cld ∧ rel_dec tr tg1 tg2 = rr) ∨
  (tg1 = tg_cld ∧ tg2 = tg_par ∧ rr = Child (Strict Immediate)) ∨
  (tg1 = tg_cld ∧ tg2 ≠ tg_par ∧ rr = Child (Strict FurtherAway) ∧ ∃ i, rel_dec tr tg_par tg2 = Child (Strict i)) ∨
  (tg1 = tg_cld ∧ tg2 ≠ tg_par ∧ rr = Foreign Cousin ∧ ∃ f, rel_dec tr tg_par tg2 = Foreign f).
Proof.
  intros Hwf1 Hwf2 Hn1 Hn2 Hin2 (it&Hit&Hcc)%bind_Some Hreldec Hne2.
  injection Hcc as Hcc.
  assert (itag it = tg_cld) as Htgit by by eapply new_item_has_tag.
  assert (create_child C tg_par tg_cld pk im rk cc tr = Some tr') as Htrin.
  1: rewrite /create_child Hit /= Hcc //.
  assert (tg_par ≠ tg_cld) as Hnepc by by intros ->.
  destruct (decide (tg1 = tg_cld)) as [->|Hne]; [right|left]; last first.
  { split; first done. rewrite -Hreldec. by eapply create_child_rel_dec. }
  subst tr'. pose (insert_child_at tr it (IsTag tg_par)) as tr'.
  destruct (decide (tg2 = tg_par)) as [->|Hne']; [left|right].
  { do 2 (split; first done). subst rr. rewrite /rel_dec.
    eassert _ as HA1; last (rewrite decide_True; last exact HA1).
    1: by eapply insert_produces_ParentChild.
    rewrite decide_False. 2: intros [?|HSP]; first done.
    2: eapply strict_parent_self_impossible; last by eapply ParentChild_StrictParentChild.
    2: by eapply insert_preserves_exists.
    rewrite decide_True //. rewrite -Htgit.
    eapply (insert_produces_ImmediateParentChild tg_par it). congruence. }
  fold tr' in Hreldec.
  rewrite /rel_dec in Hreldec. destruct (decide (ParentChildIn tg2 tg_cld tr')) as [HPC|HPC].
  - left. destruct HPC as [->|HPC]. 1: done. do 2 (split; first done).
    rewrite decide_False in Hreldec; last first.
    { intros [->|HCC]; first done. eapply strict_parent_self_impossible. 2: by eapply StrictParentChild_transitive.
      eapply insert_true_produces_exists; done. }
    rewrite -Htgit in HPC. eapply insert_produces_minimal_ParentChild in HPC; [|congruence..].
    rewrite decide_False in Hreldec; last first.
    { intros Himm. eapply (insert_eqv_strict_rel _ _ it) in HPC. 2-3: congruence.
      eapply immediate_not_transitive_strong_2. 1-4: eapply Hwf2. 6: exact Himm. 4: exact HPC.
      3: by eapply insert_true_produces_exists. 1: done. 1: by eapply insert_preserves_exists.
      rewrite -Htgit. eapply insert_produces_StrictParentChild. congruence. }
    subst rr. split; first done.
    rewrite /rel_dec decide_True. 2: by right.
    rewrite /rel_dec decide_False. 1: by eexists.
    intros [?|HCC]; first done.
    eapply strict_parent_self_impossible. 2: by eapply StrictParentChild_transitive. done.
  - right. eassert (¬ _) as HSPC. 1: intros H; eapply HPC; right; exact H.
    do 2 (split; first done). rewrite decide_False in Hreldec; last first.
    { intros [?|HSPC2]; first done. rewrite -Htgit in HSPC2.
      eapply inserted_not_strict_parent. 3: exact HSPC2. 1-2: congruence. }
    subst rr. split; first done.
    rewrite /rel_dec. rewrite decide_False; first by eexists.
    intros [?|HSPC3]; first done. eapply HSPC. eapply StrictParentChild_transitive.
    2: rewrite -Htgit; eapply insert_produces_StrictParentChild; congruence.
    unfold tr'.
    setoid_rewrite <- insert_eqv_strict_rel; first exact HSPC3. all: congruence.
Qed.

Lemma loc_controlled_create_child_preserved l sc σ σ' blk C tg_par tg_cld pk im rk cc tg_lu tk:
  apply_within_trees (create_child C tg_par tg_cld pk im rk cc) blk σ.(strs) = Some σ'.(strs) →
  shp σ = shp σ' →
  scs σ = scs σ' →
  state_wf σ →
  state_wf σ' →
  l.1 = blk →
  trees_contain tg_par σ.(strs) blk →
  ¬ trees_contain tg_cld σ.(strs) blk →
  tg_lu ≠ tg_cld →
  (tg_par = tg_lu → tk = tk_pub) →
  loc_controlled l tg_lu tk sc σ →
  loc_controlled l tg_lu tk sc σ'.
Proof.
  intros Happly Heq_shp Heq_scs Hwf Hwf2 Hblk Htgpar Htgcld Htgne Hnotlocal Hlc.
  subst blk.
  pose proof Happly as (trold&Htrold&(trnew&Haccess&[= Hstrs])%bind_Some)%bind_Some.
  assert (strs σ' !! l.1 = Some trnew) as Htrnew.
  { by rewrite -Hstrs lookup_insert_eq. }
  rewrite /loc_controlled. rewrite -Heq_shp.
  pose proof Htgcld as Htgcldtr. rewrite /trees_contain /trees_at_block Htrold in Htgcldtr.
  pose proof Htgpar as Htgpartr. rewrite /trees_contain /trees_at_block Htrold in Htgpartr.
  destruct tk as [|act|] eqn:Heq; simpl.
  - intros (it & Htrlu & Hperm).
    destruct Htrlu as (trnew2 & Htrnew2 & Htrlu).
    assert (trnew2 = trnew) as -> by congruence.
    eapply create_child_tree_lookup in Htrlu as Htrluold; last done. 2: done.
    destruct Hlc as (Hownold & Hscold).
    1: exists it; split; last done; by exists trold.
    split; last done.
    destruct Hownold as (it'&trold'&Hluit'&Htrold'&Hinit&Hpermo&Hothers).
    assert (trold' = trold) as -> by congruence.
    assert (it' = it) as -> by by eapply tree_lookup_unique.
    exists it, trnew. do 4 (split; first done).
    intros it' t' Hit'.
    remember (rel_dec trnew t' tg_lu) as rr eqn:Hreldec. symmetry in Hreldec.
    eapply create_child_rel_dec_new in Hreldec. 7: by eapply Haccess. 2: by eapply Hwf. 2: by eapply Hwf2. 2,3,5: done. 2: by eapply lookup_implies_contains.
    destruct Hreldec as [(Hne&Hreldec)|[(->&->&->)|[(->&Hne&->&ii&Hreldec)|(->&Hne&->&ff&Hreldec)]]].
    { subst rr. eapply Hothers. eapply create_child_tree_lookup; last done. 2: done. done. }
    all: eapply create_child_tree_lookup_new in Hit' as (pp&Hpp&[= <-])%eq_sym%bind_Some; [..|exact Haccess]; [|done..].
    all: rewrite /create_new_item /item_lookup /= lookup_empty /=.
    all: intros ->; by destruct pk, im, rk.
  - intros (it & Htrlu & Hperm).
    destruct Htrlu as (trnew2 & Htrnew2 & Htrlu).
    assert (trnew2 = trnew) as -> by congruence.
    eapply create_child_tree_lookup in Htrlu as Htrluold; last done. 2: done.
    destruct Hlc as (Hownold & Hscold).
    1: exists it; split; last done; by exists trold.
    split; last done.
    destruct Hownold as (it'&trold'&Hluit'&Htrold'&Hinit&Hpermo&Hothers).
    assert (trold' = trold) as -> by congruence.
    assert (it' = it) as -> by by eapply tree_lookup_unique.
    exists it, trnew. do 3 (split; first done).
    split.
    { rewrite -Heq_scs. eapply Hpermo. }
    intros it' t' Hit'.
    remember (rel_dec trnew t' tg_lu) as rr eqn:Hreldec. symmetry in Hreldec.
    eapply create_child_rel_dec_new in Hreldec. 7: by eapply Haccess. 2: by eapply Hwf. 2: by eapply Hwf2. 2,3,5: done. 2: by eapply lookup_implies_contains.
    destruct Hreldec as [(Hne&Hreldec)|[(->&->&->)|[(->&Hne&->&ii&Hreldec)|(->&Hne&->&ff&Hreldec)]]].
    { subst rr. eapply create_child_tree_lookup in Hit'; last done; last done.
      specialize (Hothers _ _ Hit'). destruct (rel_dec trold t' tg_lu) as [[]|[]] eqn:Hreldec. 1,3,4: eapply Hothers.
      destruct Hothers as [Hini|Hothers]; [left|right]; first done.
      by rewrite -Heq_scs. }
    { by specialize (Hnotlocal eq_refl). }
    { done. }
    { eapply create_child_tree_lookup_new in Hit' as (pp&Hpp&[= <-])%eq_sym%bind_Some; [..|exact Haccess]; [|done..].
      left. by rewrite /item_lookup /= lookup_empty /=. }
  - destruct Hlc as (Hownold & Hscold). 1: done.
    exfalso; ospecialize (Hnotlocal _); last done.
    destruct Hownold as (it'&trold'&Hluit'&Htrold'&Hinit&Hpermo&Hothers).
    assert (trold' = trold) as -> by congruence.
    opose proof* unique_implies_lookup as (itpar&Hlupar).
    { eapply Hwf. 2: exact Htgpartr. done. }
    symmetry. eapply Hothers. done.
Qed.

Lemma loc_controlled_create_child_preserved_outside l sc σ σ' blk C tg_par tg_cld pk im rk cc tg_lu tk:
  apply_within_trees (create_child C tg_par tg_cld pk im rk cc) blk σ.(strs) = Some σ'.(strs) →
  shp σ = shp σ' →
  scs σ = scs σ' →
  state_wf σ →
  state_wf σ' →
  l.1 ≠ blk →
  loc_controlled l tg_lu tk sc σ →
  loc_controlled l tg_lu tk sc σ'.
Proof.
  intros Happly Heq_shp Heq_scs Hwf Hwf2 Hblk Hlc.
  pose proof Happly as (trold&Htrold&(trnew&Haccess&[= Hstrs])%bind_Some)%bind_Some.
  rewrite /loc_controlled. rewrite -Heq_shp.
  destruct tk.
  - intros (it&Hit&HH).
    rewrite /trees_lookup -Hstrs lookup_insert_ne // in Hit.
    destruct Hlc as (Hown&Hhp). 1: by exists it. split; last done.
    destruct Hit as (tr&Htr&Hit).
    destruct Hown as (it'&tr'&Hit'&Htr'&Hx).
    assert (tr = tr') as <- by (rewrite Htr in Htr'; congruence).
    assert (it = it') as <- by by eapply tree_lookup_unique.
    exists it, tr. rewrite -Hstrs lookup_insert_ne //.
  - intros (it&Hit&HH).
    rewrite /trees_lookup -Hstrs lookup_insert_ne // in Hit.
    destruct Hlc as (Hown&Hhp). 1: by exists it.
    destruct Hit as (tr&Htr&Hit).
    destruct Hown as (it'&tr'&Hit'&Htr'&Hinit&Hrst).
    assert (tr = tr') as <- by (rewrite Htr in Htr'; congruence).
    assert (it = it') as <- by by eapply tree_lookup_unique. split; last done.
    exists it, tr. rewrite -Hstrs lookup_insert_ne //.
    do 3 (split; first done).
    rewrite /bor_state_post_unq -Heq_scs. done.
  - intros _.
    destruct Hlc as (Hown&Hhp). 1: done.
    split; last done.
    destruct Hown as (it&tr&Hit'&Htr'&Hinit&Hown&Hothers).
    exists it, tr. rewrite -Hstrs lookup_insert_ne //.
Qed.

Lemma loc_controlled_create_child_preserved_everywhere l sc σ σ' blk C tg_par tg_cld pk im rk cc tg_lu tk:
  apply_within_trees (create_child C tg_par tg_cld pk im rk cc) blk σ.(strs) = Some σ'.(strs) →
  shp σ = shp σ' →
  scs σ = scs σ' →
  state_wf σ →
  state_wf σ' →
  trees_contain tg_par σ.(strs) blk →
  ¬ trees_contain tg_cld σ.(strs) blk →
  tg_lu ≠ tg_cld →
  (tg_par = tg_lu → tk = tk_pub) →
  loc_controlled l tg_lu tk sc σ →
  loc_controlled l tg_lu tk sc σ'.
Proof.
  intros Happly Heq_shp Heq_scs Hwf Hwf2 Htgpar Htgcld Htgne Hnotlocal Hlc.
  destruct (decide (l.1 = blk)) as [Hblk|Hne].
  - by eapply loc_controlled_create_child_preserved.
  - by eapply loc_controlled_create_child_preserved_outside.
Qed.

Lemma loc_controlled_read_preserved l sc σ σ' blk off1 sz tg_acc tg_lu tk b:
  apply_within_trees (memory_access_maybe_nonchildren_only b AccessRead σ.(scs) tg_acc (off1, sz)) blk σ.(strs) = Some σ'.(strs) →
  shp σ = shp σ' →
  scs σ = scs σ' →
  state_wf σ →
  l.1 = blk →
  (off1 ≤ l.2 < off1 + sz) →
  trees_contain tg_acc σ.(strs) blk →
  loc_controlled l tg_lu tk sc σ →
  loc_controlled l tg_lu tk sc σ'.
Proof.
  intros Happly Heq_shp Heq_scs Hwf Hblk Hsz Htgin Hlc.
  subst blk.
  pose proof Happly as (trold&Htrold&(trnew&Haccess&[= Hstrs])%bind_Some)%bind_Some.
  assert (strs σ' !! l.1 = Some trnew) as Htrnew.
  { by rewrite -Hstrs lookup_insert_eq. }
  rewrite /loc_controlled.
  destruct tk as [|act|] eqn:Heq; simpl.
  - intros (it & Htrlu & Hperm).
    pose proof Htrlu as Htrlu2.
    eapply apply_trees_access_lookup_general_rev in Htrlu2; [|eapply Happly|eapply Hwf|done].
    destruct Htrlu2 as (itold & Hluold & Heq1 & Heq2 & Heq3).
    destruct Hlc as (Hownold & Hscold).
    + exists itold. split; first done.
      intros Hini Hdis. eapply Hperm.
      * eapply apply_access_perm_initialized; eassumption.
      * eapply apply_access_perm_access_remains_disabled; eassumption.
    + split; last by rewrite -Heq_shp.
      destruct Hluold as (trold2 & Htrold2 & Hluold).
      assert (trold2 = trold) as -> by congruence. clear Htrold2.
      destruct Hownold as (itold2 & trold2 & Hluold2 & Hluold2' & Hisinit & Hsame & Hothers).
      assert (trold2 = trold) as -> by congruence.
      assert (itold2 = itold) as -> by by eapply tree_lookup_unique.
      destruct Htrlu as (trnew2 & Htrnew2 & Hlunew).
      assert (trnew2 = trnew) as -> by congruence.
      exists it, trnew. do 2 (split; first done).
      split; first by eapply apply_access_perm_initialized.
      split; first by eapply apply_access_perm_read_frozen.
      intros itnew' t' Hit'.
      assert (trees_lookup (strs σ') l.1 t' itnew') as Hit'' by by exists trnew.
      eapply apply_trees_access_lookup_general_rev in Hit''; [|eapply Happly|eapply Hwf|done].
      destruct Hit'' as (itold' & (x & Hx & Hitoldlu') & HHHH).
      assert (x = trold) as -> by congruence.
      specialize (Hothers _ _ Hitoldlu').
      assert (rel_dec trnew t' tg_lu = rel_dec trold t' tg_lu) as Hreldec.
      { rewrite /apply_within_trees Hx /= in Happly.
        apply bind_Some in Happly as (newtr & H1 & [= H2]).
        rewrite -H2 lookup_insert_eq in Htrnew.
        erewrite (access_same_rel_dec H1). congruence. }
      rewrite Hreldec. destruct HHHH as (Hinit2 & Hprot2 & Hperm2).
      rewrite /trees_rel_dec Htrold in Hperm2.
      edestruct maybe_non_children_only_effect_or_nop as [Heqc|Heqc]; erewrite Heqc in Hperm2.
      2: by injection Hperm2 as <-.
      assert (lazy_perm_wf (item_lookup itold' l.2)) as Hwitold'.
      { eapply item_wf_lookup. pose (state_wf_tree_compat _ Hwf) as Hcompat.
        specialize (Hcompat _ _ Htrold). rewrite /tree_items_compat_nexts every_node_iff_every_lookup in Hcompat.
        1: by eapply Hcompat. eapply wf_tree_tree_item_determined. by eapply Hwf. }
      rewrite /lazy_perm_wf in Hwitold'.
      clear Heqc. rewrite /apply_access_perm /apply_access_perm_inner /= in Hperm2.
      destruct (most_init (initialized (item_lookup itold' l.2)) (requires_init (rel_dec trold tg_acc t'))) as [] eqn:Hmostinit.
      all: repeat (case_match; simpl in Hperm2; simplify_eq; try rewrite <- Hperm2; try (rewrite (Hwitold' eq_refl) /= in Hmostinit); simpl in Hperm2; try done).
  - intros (it & Htrlu & Hndis).
    pose proof Htrlu as Htrlu2.
    eapply apply_trees_access_lookup_general_rev in Htrlu2; [|eapply Happly|eapply Hwf|done].
    destruct Htrlu2 as (itold & Hluold & Heq1 & Heq2 & Heq3).
    destruct Hlc as (Hownold & Hscold).
    + exists itold. split; first done.
      intros HH Hdis; eapply apply_access_perm_access_remains_disabled in Hdis; last done.
      eapply Hndis; try done; by eapply apply_access_perm_initialized.
    + split; last by rewrite -Heq_shp.
      destruct Hluold as (trold2 & Htrold2 & Hluold).
      assert (trold2 = trold) as -> by congruence. clear Htrold2. rewrite /bor_state_own /= in Hownold.
      destruct Hownold as (itold2 & trold2 & Hluold2 & Hluold2' & Hisinit & Hsame & Hothers).
      assert (trold2 = trold) as -> by congruence.
      assert (itold2 = itold) as -> by by eapply tree_lookup_unique.
      destruct Htrlu as (trnew2 & Htrnew2 & Hlunew).
      assert (trnew2 = trnew) as -> by congruence.
      exists it, trnew. do 2 (split; first done).
      split; first by eapply apply_access_perm_initialized.
      assert ((perm (item_lookup it l.2) = Frozen → protector_is_active (iprot it) (scs σ')) → ((perm (item_lookup itold l.2) = Frozen → protector_is_active (iprot itold) (scs σ)))) as HP.
      { intros Hfrzprot Hfrz. rewrite Heq2 Heq_scs. eapply Hfrzprot.
        erewrite apply_access_perm_read_frozen. all: done. }
      assert (lazy_perm_wf (item_lookup itold l.2)) as Hwfitold.
      { eapply item_wf_lookup. pose (state_wf_tree_compat _ Hwf) as Hcompat.
        specialize (Hcompat _ _ Htrold). rewrite /tree_items_compat_nexts every_node_iff_every_lookup in Hcompat.
        1: by eapply Hcompat. eapply wf_tree_tree_item_determined. by eapply Hwf. }
      rewrite /lazy_perm_wf in Hwfitold. rewrite /bor_state_post_unq.
      match goal with |- ((?P -> ?A) ∧ ?B) => assert (P → (A ∧ match trees_rel_dec (strs σ) l.1 tg_acc tg_lu with 
          Foreign (Parent _) => act = tk_res ∨ (b = true) | Foreign _ => act = tk_res | _ => True end)) as Hfpar end.
      { clear Hothers. intros Hfrzprot.
        ospecialize (Hsame _). 1: by eapply HP.
        edestruct maybe_non_children_only_effect_or_nop_strong as [(Heqcc&Hne)|(Heqcc&He1&childkind&He2)]; erewrite Heqcc in Heq3.
        2: { injection Heq3 as <-. rewrite He2. split; first done. by right. }
        pose proof Heq3 as (x1&Hx1&(x2&Hx2&[= HH])%bind_Some)%bind_Some.
        rewrite -HH -?Heq_scs /= in Hfrzprot|-*.
        rewrite /apply_access_perm_inner in Hx1.
        assert (perm (item_lookup itold l.2) = Active → most_init (initialized (item_lookup itold l.2)) (requires_init (trees_rel_dec (strs σ) l.1 tg_acc tg_lu)) = PermInit) as HHH.
        { intros H; by rewrite Hwfitold. }
        repeat (case_match; simplify_eq; (try specialize (HHH eq_refl)); (try (destruct Hsame; [ idtac ])); try done; try (split; [done | (try by left); by right ])).
        all: exfalso; eapply bool_decide_eq_false_1; last apply (Hfrzprot eq_refl). all: done.
        }
      split.
      { intros Hfrzprot. by eapply Hfpar. }
      intros itnew' t' Hit'.
      rewrite /lazy_perm_wf in Hwfitold.
      assert (trees_lookup (strs σ') l.1 t' itnew') as Hit'' by by exists trnew.
      eapply apply_trees_access_lookup_general_rev in Hit''; [|eapply Happly|eapply Hwf|done].
      destruct Hit'' as (itold' & (x & Hx & Hitoldlu') & HHHH).
      assert (x = trold) as -> by congruence.
      assert (lazy_perm_wf (item_lookup itold' l.2)) as Hwfitold'.
      { eapply item_wf_lookup. pose (state_wf_tree_compat _ Hwf) as Hcompat.
        specialize (Hcompat _ _ Htrold). rewrite /tree_items_compat_nexts every_node_iff_every_lookup in Hcompat.
        1: by eapply Hcompat. eapply wf_tree_tree_item_determined. by eapply Hwf. }
      rewrite /lazy_perm_wf in Hwfitold'.
      specialize (Hothers _ _ Hitoldlu').
      assert (∀ tg1 tg2, rel_dec trnew tg1 tg2 = rel_dec trold tg1 tg2) as Hreldec_strong.
      { intros tg1 tg2. rewrite /apply_within_trees Hx /= in Happly.
        apply bind_Some in Happly as (newtr & H1 & [= H2]).
        rewrite -H2 lookup_insert_eq in Htrnew.
        erewrite (access_same_rel_dec H1). congruence. }
      assert (rel_dec trnew t' tg_lu = rel_dec trold t' tg_lu) as Hreldec.
      { eapply Hreldec_strong. }
      rewrite Hreldec. destruct HHHH as (Hinit2 & Hprot2 & Hperm2).
      edestruct maybe_non_children_only_effect_or_nop_strong as [(Heqcc&Hne)|(Heqcc&He1&childkind&He2)]; erewrite Heqcc in Hperm2.
      2: { injection Hperm2 as <-.
           destruct (rel_dec trold t' tg_lu) as [[]|]; [done| |done].
           destruct Hothers as [?|Ho]; first by left. right.
           destruct (perm (item_lookup itold' l.2)) as [|?| | | |]; try done.
           - destruct Ho as [H|H]. 1: by left. right. intros HH. eapply H. eapply HP. done.
           - destruct Ho as [H|H]. 1: by left. right. intros HH. eapply H. eapply HP. done. }
      pose proof Hperm2 as (x1&Hx1&(x2&Hx2&[= HH])%bind_Some)%bind_Some.
      rewrite -HH -?Heq_scs /= in |-*.
      rewrite /apply_access_perm_inner in Hx1. clear Heqcc.
      rewrite /trees_rel_dec Htrold in Hfpar HH Hx1 Hne|-*.
      rewrite /trees_contain /trees_at_block Htrold in Htgin.
      rewrite /trees_rel_dec /= Htrold in Heq3.
      assert (wf_tree trold) as Hwfold by by eapply Hwf.
      opose proof (rel_dec_concat_foreign _ tg_acc t' tg_lu _ _ _ _) as HtransiF.
      1-4: try done; eapply wf_tree_tree_unique; try done; by eapply lookup_implies_contains.
      simpl in Hothers.
      destruct (rel_dec trold t' tg_lu) as [[]|[[]|]]. 4,5: done.
      2: { assert (x1 = x2). { clear -Hx2. repeat case_match; by simplify_eq. } subst x2.
           destruct (rel_dec trold tg_acc t') as [] eqn:Hreldec_acc_lu.
           - simpl. destruct Hothers as [Hnoinit|Hothers]. 1: left; by rewrite Hnoinit.
             right. destruct (perm (item_lookup itold' l.2)) as [|[]| | | |], (bool_decide (protector_is_active (iprot itnew') (scs σ)));
             simplify_eq.
             all: try exact I.
             all: do 2 try (destruct Hothers as [H|Hothers]; [by left | right]); try done.
             all: intros H1; eapply Hothers, HP. all: by rewrite -Heq_scs.
           - rewrite Hreldec_strong in Hreldec. right.
             opose proof* child_of_this_is_foreign_for_cousin as Hcousin; [| | | exact Hreldec | by erewrite Hreldec_acc_lu| ]; [eapply Hwf; first done..|];
               [eapply Hitoldlu'|eapply Hluold|eapply Htgin|].
             rewrite Hcousin in Hfpar. 
             destruct (perm (item_lookup itold' l.2)) as [|?| | | |] eqn:Heqold; simplify_eq.
             4: { destruct Hothers as [Ho|?]; last done. by rewrite Hwfitold' in Ho. }
             1,3: done.
             all: destruct act; first eauto.
             all: right.
             all: intros HF; destruct Hfpar as (_&[=]). all: by rewrite -Heq_scs. }
      all: clear Hfpar HtransiF.
      all: repeat (case_match; simplify_eq; (try specialize (Hwfitold' eq_refl)); unfold most_init in *;
           simplify_eq; try done).
  - destruct Hlc as (Hownold & Hscold); first done.
    split; last by rewrite -Heq_shp.
    destruct Hownold as (itold & trold' & Hluold & Htrold' & Hisinit & Hsame & Hnoprot & Hothers).
    assert (trold' = trold) as -> by congruence.
    assert (trees_lookup σ.(strs) l.1 tg_lu itold) as Hsluold by by exists trold.
    eapply apply_trees_access_lookup_general in Hsluold; [|eapply Happly|eapply Hwf|done].
    destruct Hsluold as (itnew & (trnew' & Htrnew' & Hlunew) & (Hinitold & Hprotold & Hpermold)).
    assert (trnew' = trnew) as -> by congruence.
    assert (tg_lu = tg_acc) as <-.
    { eapply trees_contain_trees_lookup_1 in Htgin as (it&tr&Htr&HH). 2: apply Hwf.
      assert (tr = trold) as -> by congruence. by eapply Hothers. }
    exists itnew, trnew. do 2 (split; first done). split.
    { by eapply apply_access_perm_initialized. }
    rewrite trees_rel_dec_refl in Hpermold.
    edestruct maybe_non_children_only_effect_or_nop_strong as [(Heqcc&Hne)|(Heqcc&He1&acckind&He2)]; erewrite Heqcc in Hpermold.
    2: done.
    rewrite /apply_access_perm Hsame /= in Hpermold.
    split.
    { repeat (case_match; simpl in *; simplify_eq; try done). all: by rewrite -Hpermold. }
    split; first by rewrite -Hprotold.
    intros it' t' Hluit'.
    assert (wf_tree trnew) as Hwfnew.
    { rewrite /apply_within_trees Htrold /= in Happly.
      eapply bind_Some in Happly as (? & H1 & [= H2]).
      rewrite -H2 lookup_insert_eq in Htrnew.
      injection Htrnew as ->. eapply memory_access_wf; last done.
      destruct Hwf as [_ Hwf _ _]. by eapply Hwf.
    }
    assert (tree_unique t' trnew) as Hunq.
    { eapply wf_tree_tree_unique. 2: apply Hluit'. done. }
    assert (tree_unique t' trold) as Hunqold.
    { rewrite /apply_within_trees Htrold /= in Happly.
      eapply bind_Some in Happly as (? & H1 & [= H2]).
      rewrite -H2 lookup_insert_eq in Htrnew.
      injection Htrnew as ->. rewrite /tree_unique.
      by erewrite tree_apply_access_same_count.
    }
    eapply unique_exists in Hunqold as Hextold.
    eapply unique_lookup in Hunqold as (it & Hitdet).
    eapply Hothers. done.
Qed.

Lemma loc_controlled_read_preserved_everywhere l sc σ σ' blk off1 sz tg_acc tg_lu tk b:
  apply_within_trees (memory_access_maybe_nonchildren_only b AccessRead σ.(scs) tg_acc (off1, sz)) blk σ.(strs) = Some σ'.(strs) →
  shp σ = shp σ' →
  scs σ = scs σ' →
  state_wf σ →
  trees_contain tg_acc σ.(strs) blk →
  loc_controlled l tg_lu tk sc σ →
  loc_controlled l tg_lu tk sc σ'.
Proof.
  intros Happly Hhp Hcs Hwf Hcont.
  destruct (decide ((l.1 = blk ∧ off1 ≤ l.2 < off1 + sz))) as [(Hblk&Hoff)|Hne].
  - by eapply loc_controlled_read_preserved.
  - eapply loc_controlled_access_outside; try done. by rewrite Hhp.
Qed.

Lemma loc_controlled_write_nonchildren_only_on_active_preserved l sc σ σ' blk off1 sz tg_acc it_acc tg_lu tk:
  apply_within_trees (memory_access_nonchildren_only AccessWrite σ.(scs) tg_acc (off1, sz)) blk σ.(strs) = Some σ'.(strs) →
  shp σ = shp σ' →
  scs σ = scs σ' →
  state_wf σ →
  l.1 = blk →
  (off1 ≤ l.2 < off1 + sz) →
  trees_lookup σ.(strs) blk tg_acc it_acc →
  perm (item_lookup it_acc l.2) = Active →
  loc_controlled l tg_lu tk sc σ →
  loc_controlled l tg_lu tk sc σ'.
Proof.
  intros Happly Heq_shp Heq_scs Hwf Hblk Hsz Htgin Hactive Hlc.
  subst blk.
  edestruct (apply_trees_access_lookup_general true) as (it_acc_new&Hitaccnew&Haccinitp&Haccprot&Haccperm).
  1: exact Happly. 1: by eapply Hwf. 1: exact Hsz. 1: exact Htgin.
  rewrite /maybe_non_children_only trees_rel_dec_refl /nonchildren_only /apply_access_perm /apply_access_perm_inner Hactive /= most_init_comm /= if_both_sides_same /= in Haccperm.
  injection Haccperm as Haccperm.
  pose proof Happly as (trold&Htrold&(trnew&Haccess&[= Hstrs])%bind_Some)%bind_Some.
  destruct Htgin as (trold'&Htrold'&Hitacc). assert  (trold = trold') as <- by congruence. clear Htrold'.
  assert (strs σ' !! l.1 = Some trnew) as Htrnew.
  { by rewrite -Hstrs lookup_insert_eq. }
  destruct Hitaccnew as (trnew'&Htrnew'&Hitaccnew). assert  (trnew = trnew') as <- by congruence. clear Htrnew'.
  eapply memory_access_wf in Haccess as Htrnewwf. 2: by eapply Hwf.
  eapply memory_access_compat_parents_more_active in Haccess as HtrnewPMI. 2: by eapply Hwf. 2: by eapply Hitacc. 2: by eapply Hwf.
  assert (lazy_perm_wf (item_lookup it_acc l.2)) as Hwfitacc.
  { eapply item_wf_lookup. pose (state_wf_tree_compat _ Hwf) as Hcompat.
    specialize (Hcompat _ _ Htrold). rewrite /tree_items_compat_nexts every_node_iff_every_lookup in Hcompat.
    1: by eapply Hcompat. eapply wf_tree_tree_item_determined. by eapply Hwf. }
  assert (item_lookup it_acc l.2 = mkPerm PermInit Active) as Hactiveinit.
  { destruct item_lookup. simpl in Hactive. subst. simpl. f_equal. by eapply Hwfitacc. }
  assert (∀ tg1 tg2, rel_dec trnew tg1 tg2 = rel_dec trold tg1 tg2) as Hreldeceq.
  { intros ??. rewrite /apply_within_trees Htrold /= in Happly.
    apply bind_Some in Happly as (newtr & H1 & [= H2]).
    rewrite -H2 lookup_insert_eq in Htrnew.
    erewrite (access_same_rel_dec H1). congruence. }
  rewrite /loc_controlled.
  destruct tk as [|act|] eqn:Heq; simpl.
  - intros (it & Htrlu & Hperm).
    pose proof Htrlu as Htrlu2.
    eapply apply_trees_access_lookup_general_rev in Htrlu2; [|eapply Happly|eapply Hwf|done].
    destruct Htrlu2 as (itold & Hluold & Heq1 & Heq2 & Heq3).
    destruct Hlc as (Hownold & Hscold).
    + exists itold. split; first done.
      intros Hini Hdis. eapply Hperm.
      * eapply apply_access_perm_initialized; eassumption.
      * eapply apply_access_perm_access_remains_disabled; eassumption.
    + split; last by rewrite -Heq_shp.
      destruct Hluold as (trold2 & Htrold2 & Hluold).
      assert (trold2 = trold) as -> by congruence. clear Htrold2.
      destruct Hownold as (itold2 & trold2 & Hluold2 & Hluold2' & Hisinit & Hsame & Hothers).
      assert (trold2 = trold) as -> by congruence.
      assert (itold2 = itold) as -> by by eapply tree_lookup_unique.
      destruct Htrlu as (trnew2 & Htrnew2 & Hlunew).
      assert (trnew2 = trnew) as -> by congruence.
      exists it, trnew. do 2 (split; first done).
      split; first by eapply apply_access_perm_initialized.
      pose proof (Hothers _ _ Hitacc) as Hothersacc.
      rewrite /trees_rel_dec Htrold in Heq3.
      destruct (rel_dec trold tg_acc tg_lu) as [[]|[]] eqn:Hreldec.
      { rewrite /maybe_non_children_only /nonchildren_only in Heq3.
        injection Heq3 as Heq3.  rewrite -Heq3. split; first done.
        intros itnew' t' Hit'.
        assert (trees_lookup (strs σ') l.1 t' itnew') as Hit'' by by exists trnew.
        eapply apply_trees_access_lookup_general_rev in Hit''; [|eapply Happly|eapply Hwf|done].
        destruct Hit'' as (itold' & (x & Hx & Hitoldlu') & HHHH).
        assert (x = trold) as -> by congruence.
        specialize (Hothers _ _ Hitoldlu').
        rewrite Hreldeceq. destruct HHHH as (Hinit2 & Hprot2 & Hperm2).
        rewrite /trees_rel_dec Htrold in Hperm2.
        edestruct maybe_non_children_only_effect_or_nop_strong as [(Heqc&Hss)|(Heqc&Hss)]; erewrite Heqc in Hperm2.
        2: by injection Hperm2 as <-.
        destruct Hss as [[]|Hss]; first done. clear Heqc.
        destruct (rel_dec trold tg_acc t') as [[]|[]] eqn:Hreldectlu.
        - exfalso; by eapply Hss.
        - erewrite rel_dec_concat_cousin. 7: done. 6: rewrite rel_dec_flip2 Hreldectlu //. 2-5: eapply Hwf; try done. 2: eapply Hitoldlu'. 2: eapply Hitacc. 2: eapply Hluold.
          intros Hact. rewrite /apply_access_perm /apply_access_perm_inner in Hperm2.
          destruct (item_lookup itold' l.2) as [[] [|?| | | |]], (bool_decide (protector_is_active (iprot itnew') (scs σ))); simpl in *.
          all: try discriminate Hperm2.
          all: injection Hperm2 as Hperm2; rewrite -Hperm2 in Hact; simpl in *.
          all: discriminate Hact.
        - eapply rel_dec_flip in Hreldectlu. simpl in Hreldectlu.
          edestruct (rel_dec_concat_parent) as [dd Hreldectlu1]. 6: exact Hreldec. 5: exact Hreldectlu.
          1-4: eapply Hwf; try done. 1: eapply Hitoldlu'. 1: eapply Hitacc. 1: eapply Hluold.
          rewrite Hreldectlu1. intros Hdis.
          eapply parents_not_disabled_child_not_active.
          7: erewrite <- Haccperm; done. 6: exact Hdis. 3,4: done. 1,2: done.
          rewrite -Hreldeceq /rel_dec in Hreldectlu. do 2 (destruct decide; try done).
        - assert (tg_acc = t') as ->.
          1: eapply rel_this_antisym. 3: done. 1: eapply Hitacc. 1: eapply Hitoldlu'.
          rewrite Hreldec. assert (it_acc_new = itnew') as -> by by eapply tree_lookup_unique.
          rewrite -Haccperm //. }
      { rewrite -Hactive in Hothersacc. done. }
      { rewrite -Hactive in Hothersacc. done. }
      { assert (tg_acc = tg_lu) as ->.
        1: eapply rel_this_antisym. 3: done. 1: eapply Hitacc. 1: eapply Hluold2.
        assert (it_acc = itold) as -> by by eapply tree_lookup_unique.
        rewrite Hactive in Hsame. done. }
  - intros (it & Htrlu & Hperm).
    pose proof Htrlu as Htrlu2.
    eapply apply_trees_access_lookup_general_rev in Htrlu2; [|eapply Happly|eapply Hwf|done].
    destruct Htrlu2 as (itold & Hluold & Heq1 & Heq2 & Heq3).
    destruct Hlc as (Hownold & Hscold).
    + exists itold. split; first done.
      intros Hini Hdis. eapply Hperm.
      * eapply apply_access_perm_initialized; eassumption.
      * eapply apply_access_perm_access_remains_disabled; eassumption.
    + split; last by rewrite -Heq_shp.
      destruct Hluold as (trold2 & Htrold2 & Hluold).
      assert (trold2 = trold) as -> by congruence. clear Htrold2.
      destruct Hownold as (itold2 & trold2 & Hluold2 & Hluold2' & Hisinit & Hsame & Hothers).
      assert (trold2 = trold) as -> by congruence.
      assert (itold2 = itold) as -> by by eapply tree_lookup_unique.
      destruct Htrlu as (trnew2 & Htrnew2 & Hlunew).
      assert (trnew2 = trnew) as -> by congruence.
      exists it, trnew. do 2 (split; first done).
      split; first by eapply apply_access_perm_initialized.
      pose proof (Hothers _ _ Hitacc) as Hothersacc.
      rewrite /trees_rel_dec Htrold in Heq3.
      destruct (rel_dec trold tg_acc tg_lu) as [[]|[]] eqn:Hreldec.
      { rewrite /maybe_non_children_only /nonchildren_only in Heq3.
        injection Heq3 as Heq3. rewrite /bor_state_post_unq.
        1: rewrite -Heq3 -Heq2 -Heq_scs. split; first done.
        intros itnew' t' Hit'.
        assert (trees_lookup (strs σ') l.1 t' itnew') as Hit'' by by exists trnew.
        eapply apply_trees_access_lookup_general_rev in Hit''; [|eapply Happly|eapply Hwf|done].
        destruct Hit'' as (itold' & (x & Hx & Hitoldlu') & HHHH).
        assert (x = trold) as -> by congruence.
        specialize (Hothers _ _ Hitoldlu').
        rewrite Hreldeceq. destruct HHHH as (Hinit2 & Hprot2 & Hperm2).
        rewrite /trees_rel_dec Htrold in Hperm2.
        edestruct maybe_non_children_only_effect_or_nop_strong as [(Heqc&Hss)|(Heqc&Hss)]; erewrite Heqc in Hperm2.
        2: by injection Hperm2 as <-.
        destruct Hss as [[]|Hss]; first done. clear Heqc.
        destruct (rel_dec trold tg_acc t') as [[]|[]] eqn:Hreldectlu.
        - exfalso; by eapply Hss.
        - opose proof* (rel_dec_concat_cousin trold t' _ tg_lu) as Hrrr. 6: done. 5: rewrite rel_dec_flip2 Hreldectlu //. 1-4: eapply Hwf; try done. 1: eapply Hitoldlu'. 1: eapply Hitacc. 1: eapply Hluold.
          rewrite Hrrr in Hothers|-*.
          rewrite /apply_access_perm /apply_access_perm_inner in Hperm2.
          destruct (item_lookup itold' l.2) as [[] [|?| | | |]], (bool_decide (protector_is_active (iprot itnew') (scs σ))); simpl in *.
          all: try discriminate Hperm2.
          all: injection Hperm2 as Hperm2; rewrite -Hperm2 ; simpl in *.
          all: tauto.
        - eapply rel_dec_flip in Hreldectlu. simpl in Hreldectlu.
          edestruct (rel_dec_concat_parent) as [dd Hreldectlu1]. 6: exact Hreldec. 5: exact Hreldectlu.
          1-4: eapply Hwf; try done. 1: eapply Hitoldlu'. 1: eapply Hitacc. 1: eapply Hluold.
          rewrite Hreldectlu1. intros Hdis.
          eapply parents_not_disabled_child_not_active.
          7: erewrite <- Haccperm; done. 6: exact Hdis. 3,4: done. 1,2: done.
          rewrite -Hreldeceq /rel_dec in Hreldectlu. do 2 (destruct decide; try done).
        - assert (tg_acc = t') as ->.
          1: eapply rel_this_antisym. 3: done. 1: eapply Hitacc. 1: eapply Hitoldlu'.
          rewrite Hreldec. assert (it_acc_new = itnew') as -> by by eapply tree_lookup_unique.
          rewrite -Haccperm //. }
      { rewrite Hactiveinit /= in Hothersacc. by destruct Hothersacc. }
      { rewrite /rel_dec in Hreldec.
        destruct (decide (ParentChildIn _ _ trold)) as [HPC|?]; last done.
        destruct (decide (ParentChildIn _ _ trold)) as [?|HnPC]; first done.
        destruct HPC as [->|HSPC]. 1: exfalso; eapply HnPC; by left.
        odestruct immediate_sandwich as (tgsw&Hsw1&Hsw2). 3: exact HSPC. 1: by eapply Hwf. 1: eapply Hwf; try done; eapply Hluold2.
        assert (tree_contains tgsw trold) as Hsw3.
        { eapply contains_child. 2: eapply Hluold2. right. by eapply Immediate_is_StrictParentChild. }
        assert (tree_unique tgsw trold) as (itws&Hitsw)%unique_implies_lookup. 1: by by eapply Hwf.
        specialize (Hothers _ _ Hitsw).
        rewrite /rel_dec in Hothers.
        rewrite decide_True in Hothers. 2: right; by eapply Immediate_is_StrictParentChild.
        rewrite decide_False in Hothers.
        2: { intros [->|Hne]; eapply not_strict_parent_of_self.
             2: by eapply Immediate_is_StrictParentChild.  1: eapply Hluold.
             2: eapply StrictParentChild_transitive. 2: exact Hne. 2: by eapply Immediate_is_StrictParentChild.
             1: eapply Hitsw. }
        rewrite decide_True in Hothers. 2: done.
        exfalso. eapply parents_not_disabled_child_not_active.
        6: exact Hothers. 5: exact Hsw2. 3-4: done. 3: done.
        all: by eapply Hwf. }
      { assert (tg_acc = tg_lu) as ->.
        1: eapply rel_this_antisym. 3: done. 1: eapply Hitacc. 1: eapply Hluold2.
        assert (it_acc = itold) as -> by by eapply tree_lookup_unique.
        assert (it_acc_new = it) as -> by by eapply tree_lookup_unique.
        rewrite /bor_state_post_unq.
        rewrite -Haccperm /=. rewrite Hactiveinit /= in Hsame.
        rewrite -Heq2 -Heq_scs. split; first exact Hsame.
        ospecialize (Hsame _); first done. subst act.
        intros itnew' t' Hit'.
        assert (trees_lookup (strs σ') l.1 t' itnew') as Hit'' by by exists trnew.
        eapply apply_trees_access_lookup_general_rev in Hit''; [|eapply Happly|eapply Hwf|done].
        destruct Hit'' as (itold' & (x & Hx & Hitoldlu') & HHHH).
        assert (x = trold) as -> by congruence.
        specialize (Hothers _ _ Hitoldlu').
        rewrite Hreldeceq. destruct HHHH as (Hinit2 & Hprot2 & Hperm2).
        rewrite /trees_rel_dec Htrold in Hperm2.
        destruct (rel_dec trold t' tg_lu) as [[]|[]] eqn:Hreldectlu.
        all: eapply rel_dec_flip in Hreldectlu; simpl in Hreldectlu; rewrite Hreldectlu /= in Hperm2.
        - rewrite /apply_access_perm /apply_access_perm_inner most_init_comm /= in Hperm2.
          destruct (perm (item_lookup itold' l.2)) as [|[]| | | |], (bool_decide (protector_is_active (iprot itnew') (scs σ))); simpl in Hperm2.
          all: try discriminate Hperm2. all: injection Hperm2 as <-; done.
        - rewrite /apply_access_perm /apply_access_perm_inner most_init_comm in Hperm2.
          destruct (item_lookup itold' l.2) as [ini prm]; simpl in *.
          destruct ini, prm as [|?| | | |], (bool_decide (protector_is_active (iprot itnew') (scs σ))) eqn:Hbd; simpl in *.
          all: try discriminate Hperm2.
          all: injection Hperm2 as <-; simpl.
          all: try tauto.
        - injection Hperm2 as Hperm2. rewrite -Hperm2. done.
        - done. }
  - destruct Hlc as (Hownold & Hscold); first done.
    split; last by rewrite -Heq_shp.
    destruct Hownold as (itold & trold' & Hluold & Htrold' & Hisinit & Hsame & Hnoprot & Hothers).
    assert (trold' = trold) as -> by congruence.
    assert (trees_lookup σ.(strs) l.1 tg_lu itold) as Hsluold by by exists trold.
    eapply apply_trees_access_lookup_general in Hsluold; [|eapply Happly|eapply Hwf|done].
    destruct Hsluold as (itnew & (trnew' & Htrnew' & Hlunew) & (Hinitold & Hprotold & Hpermold)).
    assert (trnew' = trnew) as -> by congruence.
    assert (tg_lu = tg_acc) as <-.
    { by eapply Hothers. }
    exists itnew, trnew. do 2 (split; first done). split.
    { by eapply apply_access_perm_initialized. }
    rewrite trees_rel_dec_refl in Hpermold.
    edestruct maybe_non_children_only_effect_or_nop_strong as [(Heqcc&Hne)|(Heqcc&He1&acckind&He2)]; erewrite Heqcc in Hpermold.
    2: done.
    rewrite /apply_access_perm Hsame /= in Hpermold.
    split.
    { repeat (case_match; simpl in *; simplify_eq; try done). all: by rewrite -Hpermold. }
    split; first by rewrite -Hprotold.
    intros it' t' Hluit'.
    assert (wf_tree trnew) as Hwfnew.
    { rewrite /apply_within_trees Htrold /= in Happly.
      eapply bind_Some in Happly as (? & H1 & [= H2]).
      rewrite -H2 lookup_insert_eq in Htrnew.
      injection Htrnew as ->. eapply memory_access_wf; last done.
      destruct Hwf as [_ Hwf _ _]. by eapply Hwf.
    }
    assert (tree_unique t' trnew) as Hunq.
    { eapply wf_tree_tree_unique. 2: apply Hluit'. done. }
    assert (tree_unique t' trold) as Hunqold.
    { rewrite /apply_within_trees Htrold /= in Happly.
      eapply bind_Some in Happly as (? & H1 & [= H2]).
      rewrite -H2 lookup_insert_eq in Htrnew.
      injection Htrnew as ->. rewrite /tree_unique.
      by erewrite tree_apply_access_same_count.
    }
    eapply unique_exists in Hunqold as Hextold.
    eapply unique_lookup in Hunqold as (it & Hitdet).
    eapply Hothers. done.
Qed.

Lemma protected_priv_loc_does_not_survive_access σ σ' M_tag M_hl M_call off1 sz blk tg_acc tg_lu l acc P :
  apply_within_trees (memory_access acc σ.(scs) tg_acc (off1, sz)) blk σ.(strs) = Some σ'.(strs) →
  shp σ = shp σ' →
  scs σ = scs σ' →
  state_wf σ →
  l.1 = blk →
  (off1 ≤ l.2 < off1 + sz) →
  trees_contain tg_acc σ.(strs) blk →
  call_set_interp P M_call σ →
  M_tag !! tg_acc = Some (tk_pub, ()) →
  priv_loc M_tag M_hl M_call tg_lu l →
  (∀ tg tk sc, M_tag !! tg = Some (tk, ()) → heaplet_lookup M_hl (tg, l) = Some sc → loc_controlled l tg tk sc σ) →
  False.
Proof.
  intros Happly Heq_shp Heq_scs Hwf Hblk Hsz Htgin Hcs Hactually_public Hpl Hlc.
  destruct Hpl as (tk&Htk&(sc&Hsc)&Hpriv).
  eapply trees_contain_trees_lookup_1 in Htgin as (itacc&(tr&Htr&Hitacc)); last apply Hwf.
  specialize (Hlc tg_lu tk sc Htk Hsc).
  destruct Hpriv as [->|(cc&ae&->&Hcc)].
  - destruct Hlc as ((it&tr'&Hit&Htr'&Hactive&Hunq)&_); first done.
    assert (tr' = tr) as -> by congruence.
    enough (tg_lu = tg_acc) as -> by congruence.
    eapply Hunq. done.
  - destruct Hcc as (Mcc&HMcc&Lcc&HLcc&Hlincc).
    destruct Hcs as (Hcs&_).
    specialize (Hcs _ _ HMcc) as (Hccact&Hcs).
    specialize (Hcs _ _ HLcc) as (Htgluvalid&Hcs).
    specialize (Hcs l _ Hlincc) as (itlu&(tr'&Htr'&Hitlu)&Hprot1&HprotSM&Hprot2&Hinit&Hcs&Hcell).
    assert (tr' = tr) as -> by congruence.
    destruct Hlc as (Hlc&_).
    { eexists. split; first by eexists. done. }
    destruct Hlc as (itlu'&tr'&Hitlu'&Htr''&Hisinit&Hsame&Hothers).
    assert (tr' = tr) as -> by congruence.
    assert (itlu' = itlu) as -> by by eapply tree_lookup_unique.
    subst blk.
    ospecialize (Hsame _).
    { intros _. by eexists. }
    assert (perm (item_lookup itlu l.2) = Active) as Hisactive.
    { destruct perm as [|[]| | | |]; try done; by destruct Hsame. }
    destruct (rel_dec tr tg_acc tg_lu) as [fk|[ck|]] eqn:Hreldec.
    + assert (trees_lookup σ.(strs) l.1 tg_lu itlu) as Hitluold by by eexists.
      pose Hitluold as HH.
      eapply (apply_trees_access_lookup_general false) in HH; [|eapply Happly|eapply Hwf|done].
      destruct HH as (itlunew&(trnew&Htrnew&Hitlunew)&Hinitplu&Hiprotlu&Hpermlu).
      rewrite /trees_rel_dec Htr in Hpermlu.
      assert (protector_is_active (iprot itlunew) (scs σ)) as Hisprot.
      { exists cc. rewrite -Hiprotlu //. }
      rewrite Hreldec /= /apply_access_perm /apply_access_perm_inner Hisactive /= in Hpermlu.
      rewrite bool_decide_eq_true_2 // Hisinit /= in Hpermlu.
      by destruct acc.
    + assert (StrictParentChildIn tg_lu tg_acc tr) as HSPC.
      { rewrite /rel_dec in Hreldec. destruct decide as [[->|HSPC]|?]; try done.
        rewrite decide_True in Hreldec; last by left. done. }
      assert (tree_contains tg_lu tr) as Hluin.
      1: by eapply lookup_implies_contains.
      eapply immediate_sandwich in HSPC as (tsw&Hs1&Hs2).
      2-3: by eapply Hwf.
      eapply contains_child in Hluin as Hswin.
      2: right; by eapply Immediate_is_StrictParentChild.
      assert (tree_unique tsw tr) as Hswinunq by by eapply Hwf.
      eapply unique_implies_lookup in Hswinunq as (itsw&Hitsw).
      assert (trees_lookup σ.(strs) l.1 tsw itsw) as Hitswold by by eexists.
      pose Hitswold as HH.
      eapply (apply_trees_access_lookup_general false) in HH; [|eapply Happly|eapply Hwf|done].
      destruct HH as (itswnew&(trnew&Htrnew&Hitswnew)&Hinitpsw&Hiprotsw&Hpermsw).
      specialize (Hothers _ _ Hitsw).
      rewrite /trees_rel_dec Htr // in Hpermsw.
      rewrite /= /rel_dec decide_True // in Hpermsw.
      rewrite /= /rel_dec decide_True in Hothers.
      2: right; by eapply Immediate_is_StrictParentChild.
      rewrite decide_False in Hothers.
      2: { intros HPC2. eapply immediate_parent_not_child; try done. all: by eapply Hwf. }
      rewrite decide_True // in Hothers.
      rewrite /= /apply_access_perm /apply_access_perm_inner /= !Hothers /= in Hpermsw.
      by destruct acc.
    + enough (tg_lu = tg_acc) as -> by congruence.
      symmetry.
      eapply rel_this_antisym; last done.
      all: by eapply lookup_implies_contains.
Qed.

Lemma protected_active_loc_does_not_survive_write_access σ σ' (M_tag : gmap nat (tag_kind * ())) M_hl M_call off1 sz blk tg_acc tg_lu l P :
  apply_within_trees (memory_access AccessWrite σ.(scs) tg_acc (off1, sz)) blk σ.(strs) = Some σ'.(strs) →
  shp σ = shp σ' →
  scs σ = scs σ' →
  state_wf σ →
  l.1 = blk →
  (off1 ≤ l.2 < off1 + sz) →
  trees_contain tg_acc σ.(strs) blk →
  call_set_interp P M_call σ →
  M_tag !! tg_acc = Some (tk_pub, ()) →
  (∃ tk, M_tag !! tg_lu = Some (tk, ()) ∧ is_Some (heaplet_lookup M_hl (tg_lu, l)) ∧ ∃ c ae ak, tk = tk_unq ak ∧ call_set_in' M_call c tg_lu l (EnsuringAccess ae)) →
  (∀ tg tk sc, M_tag !! tg = Some (tk, ()) → heaplet_lookup M_hl (tg, l) = Some sc → loc_controlled l tg tk sc σ) →
  False.
Proof.
  intros Happly Heq_shp Heq_scs Hwf Hblk Hsz Htgin Hcs Hactually_public Hpl Hlc.
  destruct Hpl as (tk&Htk&(sc&Hsc)&Hpriv).
  eapply trees_contain_trees_lookup_1 in Htgin as (itacc&(tr&Htr&Hitacc)); last apply Hwf.
  specialize (Hlc tg_lu tk sc Htk Hsc).
  destruct Hpriv as (cc&ae&ak&->&Hcc).
  destruct Hcc as (Mcc&HMcc&Lcc&HLcc&Hlincc).
  destruct Hcs as (Hcs&_).
  specialize (Hcs _ _ HMcc) as (Hccact&Hcs).
  specialize (Hcs _ _ HLcc) as (Htgluvalid&Hcs). 
  specialize (Hcs l _ Hlincc) as (itlu&(tr'&Htr'&Hitlu)&Hprot1&HprotSM&Hprot2&Hcsinit&Hcs&Hcell).
  assert (tr' = tr) as -> by congruence.
  destruct Hlc as (Hlc&_).
  { eexists. split; first by eexists. done. }
  destruct Hlc as (itlu'&tr'&Hitlu'&Htr''&Hisinit&Hsame&Hothers).
  assert (tr' = tr) as -> by congruence.
  assert (itlu' = itlu) as -> by by eapply tree_lookup_unique.
  subst blk.
  ospecialize (Hsame _).
  { intros _. by eexists. }
  destruct (rel_dec tr tg_acc tg_lu) as [fk|[ck|]] eqn:Hreldec.
  + assert (trees_lookup σ.(strs) l.1 tg_lu itlu) as Hitluold by by eexists.
    pose Hitluold as HH.
    eapply (apply_trees_access_lookup_general false) in HH; [|eapply Happly|eapply Hwf|done].
    destruct HH as (itlunew&(trnew&Htrnew&Hitlunew)&Hinitplu&Hiprotlu&Hpermlu).
    rewrite /trees_rel_dec Htr in Hpermlu.
    assert (protector_is_active (iprot itlunew) (scs σ)) as Hisprot.
    { exists cc. rewrite -Hiprotlu //. }
    rewrite Hreldec /= /apply_access_perm /apply_access_perm_inner /= in Hpermlu.
    rewrite bool_decide_eq_true_2 // Hisinit /= in Hpermlu.
    by destruct (perm (item_lookup itlu l.2)) as [|?| | | |].
  + assert (StrictParentChildIn tg_lu tg_acc tr) as HSPC.
    { rewrite /rel_dec in Hreldec. destruct decide as [[->|HSPC]|?]; try done.
      rewrite decide_True in Hreldec; last by left. done. }
    assert (tree_contains tg_lu tr) as Hluin.
    1: by eapply lookup_implies_contains.
    eapply immediate_sandwich in HSPC as (tsw&Hs1&Hs2).
    2-3: by eapply Hwf.
    eapply contains_child in Hluin as Hswin.
    2: right; by eapply Immediate_is_StrictParentChild.
    assert (tree_unique tsw tr) as Hswinunq by by eapply Hwf.
    eapply unique_implies_lookup in Hswinunq as (itsw&Hitsw).
    assert (trees_lookup σ.(strs) l.1 tsw itsw) as Hitswold by by eexists.
    pose Hitswold as HH.
    eapply (apply_trees_access_lookup_general false) in HH; [|eapply Happly|eapply Hwf|done].
    destruct HH as (itswnew&(trnew&Htrnew&Hitswnew)&Hinitpsw&Hiprotsw&Hpermsw).
    specialize (Hothers _ _ Hitsw).
    rewrite /trees_rel_dec Htr // in Hpermsw.
    rewrite /= /rel_dec decide_True // in Hpermsw.
    rewrite /= /rel_dec decide_True in Hothers.
    2: right; by eapply Immediate_is_StrictParentChild.
    rewrite decide_False in Hothers.
    2: { intros HPC2. eapply immediate_parent_not_child; try done. all: by eapply Hwf. }
    rewrite decide_True // in Hothers.
    rewrite /= /apply_access_perm /apply_access_perm_inner /= !Hothers /= in Hpermsw.
    done.
  + enough (tg_lu = tg_acc) as -> by congruence.
    symmetry.
    eapply rel_this_antisym; last done.
    all: by eapply lookup_implies_contains.
Qed.


(* not generalized to maybe_nonchildren_only since this one is specific *)
Lemma loc_controlled_write_invalidates_pub l cids σ σ' blk off1 sz tg scold (A:Prop):
  apply_within_trees (memory_access AccessWrite cids tg (off1, sz)) blk σ.(strs) = Some σ'.(strs) →
  state_wf σ →
  l.1 = blk →
  trees_contain tg (strs σ) blk →
  (off1 ≤ l.2 < off1 + sz) →
  loc_controlled l tg tk_pub scold σ →
  A.
Proof.
  intros Happly Hwf Hblk Hcontain Hinbound Hold.
  assert (wf_trees σ.(strs)) as Hwf_pre by eapply Hwf.
  assert (wf_trees σ'.(strs)) as Hwf_post.
  { eapply apply_within_trees_wf; try done.
    eapply memory_access_tag_count. }
  pose proof Happly as Happlys.
  eapply bind_Some in Happly as (trold & Htrold & (trnew&Haccess&[= Hstrs])%bind_Some).
  rewrite /trees_contain /trees_at_block Htrold in Hcontain.
  assert (strs σ' !! blk = Some trnew) as Htrnew.
  1: rewrite -Hstrs lookup_insert_eq //.
  eapply wf_tree_tree_unique in Hcontain as Hunique; last by eapply Hwf_pre.
  eapply unique_lookup in Hunique as (itold & Hdet).
  assert (tree_lookup trold tg itold) as Hitold by done.
  eapply apply_trees_access_lookup_general in Happlys as Happlyself.
  2: done. 3: by exists trold. 2: eassumption.
  destruct Happlyself as (itnew & Hlunew & _ & _ & Happlyself).
  rewrite trees_rel_dec_refl /= /apply_access_perm /apply_access_perm_inner /= in Happlyself.
  destruct Hold as ((itold'&trold'&Htrold'&Hitold'&Hisinit&Hfrozen&Hothers)&_).
  { exists itold. subst blk. split; first by eexists.
    intros Hini Hdis. rewrite Hdis in Happlyself. done. } 
  assert (trold' = trold) as -> by congruence.
  assert (itold' = itold) as -> by by eapply tree_lookup_unique.
  rewrite Hfrozen in Happlyself. done.
Qed.

Lemma loc_controlled_write_invalidates_pub' l cids σ σ' blk off1 sz tg scold  :
  apply_within_trees (memory_access AccessWrite cids tg (off1, sz)) blk σ.(strs) = Some σ'.(strs) →
  state_wf σ →
  l.1 = blk →
  trees_contain tg (strs σ) blk →
  (off1 ≤ l.2 < off1 + sz) →
  loc_controlled l tg tk_pub scold σ →
  loc_controlled l tg tk_pub scold σ'.
Proof.
  eapply loc_controlled_write_invalidates_pub.
Qed.

Lemma loc_controlled_add_protected l tg tk sc σ σ' :
  shp σ = shp σ' →
  strs σ = strs σ' →
  state_wf σ →
  (∀ blk tg it c, trees_lookup σ.(strs) blk tg it → protector_is_for_call c it.(iprot) → call_is_active c σ.(scs) ↔ call_is_active c σ'.(scs)) →
  loc_controlled l tg tk sc σ →
  loc_controlled l tg tk sc σ'.
Proof.
  intros Hhp Htrs Hwf Hscs Hlc Hpre.
  assert (∀ blk tg it, trees_lookup σ.(strs) blk tg it → protector_is_active it.(iprot) σ.(scs) ↔ protector_is_active it.(iprot) σ'.(scs)) as HHscs.
  { intros blk tg' it H1; split; intros (c&H2&H3); exists c. all: split; first done. all: by eapply Hscs. }
  rewrite -Hhp.
  destruct tk as [|acc|].
  all: rewrite /loc_controlled /bor_state_pre /bor_state_own in Hlc,Hpre|-*.
  1,3: rewrite Htrs in Hlc; apply Hlc, Hpre.
  destruct Hlc as ((it&tr&Htr&Hit&Hinit&Hsame&Hothers)&Hhpc).
  - destruct Hpre as (itp&Hitp&HH).
    exists itp. by rewrite Htrs.
  - split; last done.
    exists it, tr. rewrite -Htrs. rewrite /bor_state_own_on. split_and!; try done. split.
    + clear Hothers. intros HH. ospecialize (Hsame _).
      { setoid_rewrite <- HHscs in HH. 2: by eexists. done. }
      done.
    + intros it' t' H. specialize (Hothers it' t' H).
      destruct (rel_dec tr t' tg) as [[]|]. 1,3: eapply Hothers.
      destruct Hothers as [?|Hothers]; first by left. right.
      destruct (perm (item_lookup it' l.2)) as [|?| | | |]. 1,3,4,6: done.
      all: do 2 try (destruct Hothers as [Hothers|Hothers]; [left; try done|right]).
      all: intros HP; eapply Hothers; intros; eapply HHscs; first (exists tr; done).
      all: by eapply HP.
Qed.


Lemma loc_controlled_ext l tg tk sc σ σ' :
  shp σ = shp σ' →
  strs σ = strs σ' →
  scs σ = scs σ' →
  state_wf σ →
  loc_controlled l tg tk sc σ →
  loc_controlled l tg tk sc σ'.
Proof.
  intros Hhp Htrs Hscs Hwf Hlc.
  destruct σ, σ'; simpl in *; subst.
  apply Hlc.
Qed.


Lemma apply_within_trees_tag_count_preserves_exists tg blk1 blk2 trs trs' fn :
  apply_within_trees fn blk1 trs = Some trs' →
  preserve_tree_tag_count fn →
  trees_contain tg trs blk2 →
  trees_contain tg trs' blk2.
Proof.
  intros (tr1&Htr1&(tr2&Htr2&[= <-])%bind_Some)%bind_Some H2.
  rewrite /trees_contain /trees_at_block.
  destruct (trs !! blk2) as [tr|] eqn:Htr; last done.
  intros Hcontains.
  destruct (decide (blk2 = blk1)) as [Heq|Hne].
  - subst blk2. assert (tr = tr1) as -> by congruence.
    rewrite lookup_insert_eq. eapply count_gt0_exists.
     erewrite <- H2; last done. eapply count_gt0_exists. done.
  - rewrite lookup_insert_ne; last done. by rewrite Htr.
Qed.

Lemma memory_access_nonchildren_only_on_protected_preserve σ σ' acc blk off1 tg_acc it_acc tg_lu it_lu:
  apply_within_trees (memory_access_nonchildren_only acc σ.(scs) tg_acc (off1, 1%nat)) blk σ.(strs) = Some σ'.(strs) →
  scs σ = scs σ' →
  state_wf σ → 
  trees_lookup σ.(strs) blk tg_acc it_acc →
  protector_is_active it_acc.(iprot) σ.(scs) →
  trees_lookup σ.(strs) blk tg_lu it_lu →
  protector_is_active it_lu.(iprot) σ.(scs) →
  ∃ it_lu', trees_lookup σ'.(strs) blk tg_lu it_lu' ∧
            protector_is_active it_lu'.(iprot) σ.(scs) ∧
              (∀ off, initialized (item_lookup it_lu off) = PermInit →
                      initialized (item_lookup it_acc off1) = PermInit →
                      perm (item_lookup it_acc off1) ≠ Cell →
                       (initialized (item_lookup it_lu' off) = PermInit ∧
                        (perm (item_lookup it_lu off) = Active → perm (item_lookup it_lu' off) = Active) ∧
                        (perm (item_lookup it_lu' off) = Cell → perm (item_lookup it_lu off) = Cell))).
Proof.
  intros Hacc Hscs Hwf Hluacc Hprotacc Hlulu Hinitprot.
  eapply apply_trees_access_lookup_inout in Hacc.
  2: eapply Hwf. 2: exact Hlulu.
  destruct Hacc as (it_lu'&Hitlu'&Hp1&Hp2&Hp3).
  exists it_lu'; split; first done.
  destruct Hlulu as (tr&Htr&Hlulu).
  destruct Hluacc as (tr'&Htr'&Hluacc).
  assert (tr = tr') as <- by congruence.
  rewrite /trees_rel_dec Htr in Hp3.
  rewrite -Hp2. split; first done.
  intros off Hinitacc Hinitlu Hnocell. destruct (Hp3 off) as (Hp3a&Hp3b).
  destruct (decide (off1 ≤ off < off1 + 1)) as [Hin|Hout]; last first.
  { rewrite -Hp3b //. }
  assert (off1 = off) as -> by lia. specialize (Hp3a (ltac:(lia))).
  rewrite /maybe_non_children_only /nonchildren_only in Hp3a.
  destruct (rel_dec tr tg_acc tg_lu) as [[]|] eqn:Hrd .
  - by injection Hp3a as <-.
  - split_and!.
    + rewrite /apply_access_perm /apply_access_perm_inner Hinitacc in Hp3a.
      eapply bind_Some in Hp3a as (x&_&Hp3a).
      eapply bind_Some in Hp3a as (y&_&[= <-]). done.
    + intros Hact. exfalso. opose proof (state_wf_tree_no_active_cousins _ Hwf _ _ Htr) as HH.
      eapply HH. 3: exact Hrd. 1-2: done. 2: exact Hact. right. split; last done. by left.
    + intros Hcell. rewrite /apply_access_perm /apply_access_perm_inner Hinitacc in Hp3a.
      eapply bind_Some in Hp3a as (x&Hp3ax&Hp3a).
      eapply bind_Some in Hp3a as (y&Hp3ay&[= Hr]).
      rewrite -Hr in Hcell.
      simpl. clear -Hp3ax Hp3ay Hcell. repeat (case_match; simplify_eq; try done).
  - rewrite /apply_access_perm /apply_access_perm_inner most_init_comm /= in Hp3a.
    eapply bind_Some in Hp3a as (x&Hx&(y&Hy&[= <-])%bind_Some).
    split; first done. split.
    + intros Hact. rewrite Hact in Hx.
      destruct acc; simpl in *; simplify_eq.
      all: rewrite /= if_both_sides_same /= in Hy; injection Hy as <-.
      all: done.
    + simpl. intros Hcell. rewrite Hcell in Hy.
      clear -Hx Hy. repeat (case_match; simplify_eq; try done).
Qed.

(*
Lemma apply_within_trees_set_fold {X} `{Countable X} (fn : X → option (tree item) → option (tree item)) (S : tree item → gset X) (blk : block) (trs trs' : trees) :
  apply_within_trees (λ tr, set_fold fn (Some tr) (S tr)) blk trs = Some trs' →
  (∀ x y z, fn x y = Some z → is_Some y) →
  ∃ tr0, trs !! blk = Some tr0 ∧
         set_fold (λ el trso, trs ← trso; apply_within_trees (λ tr, fn el (Some tr)) blk trs) (Some trs) (S tr0) = Some trs'.
Proof.
  intros (tr0&Htr0&(trr&Htrr&[= <-])%bind_Some)%bind_Some Hf.
  exists tr0. split; first done.
  rewrite /set_fold /= in Htrr|-*.
  induction (elements (S tr0)) as [|el1 E IH] in trr,Htrr|-*.
  - simpl in *. injection Htrr as ->. by rewrite insert_id.
  - simpl in *. pose proof Htrr as Htrr'. eapply Hf in Htrr as (sy&Htrr).
    specialize (IH _ Htrr). rewrite IH. simpl. rewrite Htrr in Htrr'.
    rewrite /apply_within_trees /= lookup_insert_eq /= Htrr' /= insert_insert_eq //.
Qed.

Lemma apply_within_trees_map_fold {X Y} `{Countable X} (fn : X → Y → option (tree item) → option (tree item)) (S : tree item → gmap X Y) (blk : block) (trs trs' : trees) :
  apply_within_trees (λ tr, map_fold fn (Some tr) (S tr)) blk trs = Some trs' →
  (∀ x a y z, fn x a y = Some z → is_Some y) →
  ∃ tr0, trs !! blk = Some tr0 ∧
         map_fold (λ el x trso, trs ← trso; apply_within_trees (λ tr, fn el x (Some tr)) blk trs) (Some trs) (S tr0) = Some trs'.
Proof.
  intros (tr0&Htr0&(trr&Htrr&[= <-])%bind_Some)%bind_Some Hf.
  exists tr0. split; first done. revert Htrr.
  generalize (S tr0); intros Str0.
  map_fold_weak_ind Str0 as el1 acc E Hne Hshape IH in trr; intros Htrr.
  - simpl in *. injection Htrr as ->. by rewrite insert_id.
  - simpl in *. pose proof Htrr as Htrr'. eapply Hf in Htrr as (sy&Htrr).
    specialize (IH _ Htrr). rewrite Hshape IH. simpl. rewrite Htrr in Htrr'.
    rewrite /apply_within_trees /= lookup_insert_eq /= Htrr' /= insert_insert_eq //.
Qed.

Lemma apply_within_trees_foldr {X}  (fn : X → option (tree item) → option (tree item)) (S : tree item → list X) (blk : block) (trs trs' : trees) :
  apply_within_trees (λ tr, foldr fn (Some tr) (S tr)) blk trs = Some trs' →
  (∀ x y z, fn x y = Some z → is_Some y) →
  ∃ tr0, trs !! blk = Some tr0 ∧
         foldr (λ el trso, trs ← trso; apply_within_trees (λ tr, fn el (Some tr)) blk trs) (Some trs) (S tr0) = Some trs'.
Proof.
  intros (tr0&Htr0&(trr&Htrr&[= <-])%bind_Some)%bind_Some Hf.
  exists tr0. split; first done.
  rewrite /set_fold /= in Htrr|-*.
  induction (S tr0) as [|el1 E IH] in trr,Htrr|-*.
  - simpl in *. injection Htrr as ->. by rewrite insert_id.
  - simpl in *. pose proof Htrr as Htrr'. eapply Hf in Htrr as (sy&Htrr).
    specialize (IH _ Htrr). rewrite IH. simpl. rewrite Htrr in Htrr'.
    rewrite /apply_within_trees /= lookup_insert_eq /= Htrr' /= insert_insert_eq //.
Qed. *)
Lemma apply_within_trees_foldr {X} (fn : X → tree item → option (tree item)) lst blk trs :
  blk ∈ dom trs →
  apply_within_trees (λ tr, foldr (λ x y, y ≫= fn x) (Some tr) lst) blk trs =
  foldr (λ x (trs : option trees), trs ≫= apply_within_trees (fn x) blk) (Some trs) lst.
Proof.
  induction lst as [|x lst IH] in trs|-*; intros Hblk.
  - eapply elem_of_dom in Hblk. destruct Hblk as (tr&Htr).
    rewrite /= /apply_within_trees Htr /= insert_id //.
  - simpl. rewrite -IH. 2: done.
    rewrite -apply_within_trees_bind //.
Qed.

Lemma apply_within_trees_ext fn1 fn2 blk trs :
  (∀ t, fn1 t = fn2 t) →
  apply_within_trees fn1 blk trs = apply_within_trees fn2 blk trs.
Proof. 
  intros H.
  rewrite /apply_within_trees.
  destruct (trs !! blk); last done.
  rewrite /= H. done.
Qed.

Lemma apply_within_trees_map_fold {K X} `{Countable K} (fn : K → X → tree item → option (tree item)) (mp : gmap K X) blk trs :
  blk ∈ dom trs →
  apply_within_trees (λ tr, map_fold (λ x v y, y ≫= fn x v) (Some tr) mp) blk trs =
  map_fold (λ x v (trs : option trees), trs ≫= apply_within_trees (fn x v) blk) (Some trs) mp.
Proof.
  intros Hblk.
  eapply (map_fold_ind_strong (λ x m, apply_within_trees (λ tr, map_fold (λ x v y, y ≫= fn x v) (Some tr) m) blk trs = x) (λ x v trs', trs' ≫= apply_within_trees (fn x v) blk) (Some trs)).
  - eapply elem_of_dom in Hblk. destruct Hblk as (tr&Htr).
    rewrite /= /apply_within_trees Htr /= map_fold_empty /= insert_id //.
  - clear mp.
    intros x v mp Hx1 Hx2 IH. simpl.
    rewrite -IH.
    rewrite -apply_within_trees_bind. apply apply_within_trees_ext.
    intros t. rewrite Hx2. done.
Qed.

Lemma preserve_tree_tag_count_trees_contain trs blk1 blk2 tg fn trs' :
  preserve_tree_tag_count fn →
  apply_within_trees fn blk1 trs = Some trs' →
  trees_contain tg trs blk2 →
  trees_contain tg trs' blk2.
Proof.
  intros HH (tr&Htr&(tr'&Htr'&[= <-])%bind_Some)%bind_Some.
  rewrite /trees_contain /trees_at_block.
  destruct (decide (blk1 = blk2)) as [->|Hne].
  2: by rewrite lookup_insert_ne.
  rewrite lookup_insert_eq Htr. intros H. eapply preserve_tag_count_contains. 2: done. 2: exact Htr'. done.
Qed.

Local Definition PS (σ : state) (S : gset (nat * gmap Z access_kind)) blk :=
    state_wf σ ∧
    ∀ tg x, (tg, x) ∈ S → ∃ it, 
      trees_lookup (strs σ) blk tg it ∧ protector_is_active it.(iprot) (scs σ) ∧
       ∀ z v, x !! z = Some v → (initialized (item_lookup it z) = PermInit ∧ perm (item_lookup it z) ≠ Cell ∧ ( v = AccessWrite → perm (item_lookup it z) = Active)).

Local Definition set_strs (σ : state) (t : trees ) : state := mkState (shp σ) t (scs σ) (snp σ) (snc σ).

Lemma tree_access_many_state_wf_helper_3 σ trs' blk tg L S off v :
  PS σ S blk →
  (tg, L) ∈ S →
  L !! off = Some v →
  apply_within_trees (memory_access_nonchildren_only v σ.(scs) tg (off, 1%nat)) blk σ.(strs) = Some trs' →
  PS (set_strs σ trs') S blk ∧ dom σ.(strs) = dom trs'.
Proof.
  intros (Hwf&HP) (it&Hit&Hitp&Hito)%HP (Hini&Hncell&Hact)%Hito Haccess.
  split; last first.
  { eapply apply_within_trees_same_dom. done. }
  split.
  { eapply access_step_wf_inner. 3: done. 2: exact Haccess.
    destruct Hit as (tr&Htr&Hit).
    rewrite /trees_contain /trees_at_block Htr. eapply Hit. }
  intros tg' S' HS'. specialize (HP _ _ HS') as (itacc&Hitacc&Hprotacc&Hrstac).
  pose σ' := (set_strs σ trs').
  eapply (memory_access_nonchildren_only_on_protected_preserve _ σ') in Haccess  as (it'&Hit'&Hprot'&Hrst).
  2: done. 2: done. 2: exact Hit. 2: done.  2: done. 2: done.
  exists it'. do 2 (split; first done).
  intros z' v' Hv'. specialize (Hrstac _ _ Hv') as (Hini'&Hnc&HH).
  specialize (Hrst _ Hini' Hini) as (Hini''&HH''&HHc''); first done.
  split; first done. split; last first.
  - intros ->. eapply HH'', HH. done.
  - intros Hx. eapply Hnc, HHc'', Hx.
Qed.

(* alternative way of moving state_wf forward here *)
Lemma tree_access_many_state_wf_helper_2 σ trs' blk tg L L' S :
  PS σ S blk →
  (tg, L') ∈ S →
  L ⊆ L' →
  map_fold (λ l acc trs2, trs2 ≫= (apply_within_trees (memory_access_nonchildren_only acc σ.(scs) tg (l, 1%nat)) blk)) (Some σ.(strs)) L = Some trs' →
  PS (set_strs σ trs') S blk ∧ dom σ.(strs) = dom trs'.
Proof.
  intros HPS HS HL'.
  map_fold_weak_ind L as z acc L Hne _ IH in trs' HPS HS HL'; simpl.
  1: intros [= <-]; by destruct σ.
  intros (trm&H1&H2)%bind_Some.
  eapply IH in H1 as (H1&Hdom1). 1: rewrite Hdom1. 2: done. 2: done.
  2: { etransitivity; last eassumption. eapply insert_subset. done. }
  pose (σm := mkState (shp σ) trm (scs σ) (snp σ) (snc σ)).
  eapply (tree_access_many_state_wf_helper_3 σm). 1: done. 3: exact H2.
  1: exact HS.
  eapply lookup_weaken. 2: exact HL'. rewrite lookup_insert_eq. done.
Qed.

Lemma tree_access_many_state_wf_helper_1 σ trs' blk (S : gset _) eS' :
  PS σ S blk →
  eS' ⊆ elements S →
  foldr (λ '(tg, L) trs1, trs1 ≫= λ trs1, map_fold (λ l acc trs2, trs2 ≫= (apply_within_trees (memory_access_nonchildren_only acc σ.(scs) tg (l, 1%nat)) blk)) (Some trs1) L) (Some σ.(strs)) eS' = Some trs' →
  PS (set_strs σ trs') S blk ∧ dom σ.(strs) = dom trs'.
Proof.
  induction eS' as [|[tg L] elS' IH] in trs'|-*; intros HPS HS'.
  - simpl. intros [= <-]. by destruct σ.
  - simpl. intros (trm&H1&H2)%bind_Some.
    eapply list_subseteq_cons_iff in HS' as (HS1&HS2).
    eapply IH in H1 as (H1&Hdom). 2: done. 2: done. rewrite Hdom.
    pose (σm := mkState (shp σ) trm (scs σ) (snp σ) (snc σ)).
    eapply (tree_access_many_state_wf_helper_2 σm) in H2. 1: exact H2.
    1: done. 1: by eapply elem_of_elements. done.
Qed.

Lemma tree_access_many_loc_controlled_helper_3 σ trs' blk tg L S off v l tg_lu tk sc :
  PS σ S blk →
  (tg, L) ∈ S →
  L !! off = Some v →
  loc_controlled l tg_lu tk sc σ →
  apply_within_trees (memory_access_nonchildren_only v σ.(scs) tg (off, 1%nat)) blk σ.(strs) = Some trs' →
  loc_controlled l tg_lu tk sc (set_strs σ trs').
Proof.
  intros (Hwf&HP) (it&Hit&Hitp&Hito)%HP (Hini&Hact)%Hito Hlc Haccess.
  destruct (decide (l = (blk, off))) as [->|Hne]; last first.
  { eapply loc_controlled_access_outside. 1: exact Haccess. 1: done. 1: done. 1: done.
    2: done. intros (<-&H). eapply Hne. destruct l; simpl in *. f_equal. lia. }
  destruct v.
  - eapply loc_controlled_read_preserved. 1: exact Haccess. 1: done. 1: done.
    1: done. 1: done. 1: simpl; lia. 2: done. 1: by eapply trees_contain_trees_lookup_2.
  - eapply loc_controlled_write_nonchildren_only_on_active_preserved.
    1: exact Haccess. 1: done. 1: done. 1: done. 1: done. 1: simpl; lia.
    1: exact Hit. 1: by eapply Hact. 1: done.
Qed.

Lemma tree_access_many_loc_controlled_helper_2 σ trs' blk tg S L l tg_lu tk sc :
  PS σ S blk →
  (tg, L) ∈ S →
  loc_controlled l tg_lu tk sc σ →
  map_fold (λ l acc trs2, trs2 ≫= (apply_within_trees (memory_access_nonchildren_only acc σ.(scs) tg (l, 1%nat)) blk)) (Some σ.(strs)) L = Some trs' →
  loc_controlled l tg_lu tk sc (set_strs σ trs').
Proof.
  intros HPS HS Hloc.
  assert (∃ L', L = L') as (L'&HL'eq) by by eexists.
  assert (L ⊆ L') as HL' by (subst; reflexivity).
  rewrite HL'eq in HS. clear HL'eq.
  map_fold_weak_ind L as z acc L Hne _ IH in trs' HPS HS HL' Hloc; simpl.
  1: intros [= <-]; by destruct σ.
  intros (trm&H1&H2)%bind_Some.
  eapply IH in H1 as H1'. 2: done. 2: done.
  2: { etransitivity; last eassumption. eapply insert_subset. done. } 2: done.
  eapply tree_access_many_state_wf_helper_2 in H1. 2: done. 2: done.
  2: { etransitivity; last eassumption. eapply insert_subset. done. }
  pose (σm := mkState (shp σ) trm (scs σ) (snp σ) (snc σ)).
  eapply (tree_access_many_loc_controlled_helper_3 σm). 5: exact H2.
  4: done. 2: done. 1: eapply H1.
  eapply lookup_weaken. 2: exact HL'. rewrite lookup_insert_eq. done.
Qed.

Lemma tree_access_many_loc_controlled_helper_1 σ trs' blk S l tg_lu tk sc :
  PS σ S blk →
  loc_controlled l tg_lu tk sc σ →
  foldr (λ '(tg, L) trs1, trs1 ≫= λ trs1, map_fold (λ l acc trs2, trs2 ≫= (apply_within_trees (memory_access_nonchildren_only acc σ.(scs) tg (l, 1%nat)) blk)) (Some trs1) L) (Some σ.(strs)) (elements S) = Some trs' →
  loc_controlled l tg_lu tk sc (set_strs σ trs').
Proof.
  intros HPS.
  assert (∃ S', elements S' = elements S) as (S'&HS'eq) by by eexists.
  rewrite -HS'eq.
  assert (elements S' ⊆ elements S) as HS' by (rewrite HS'eq; reflexivity).
  clear HS'eq.
  induction (elements S') as [|[tg L] elS' IH] in HPS, HS', trs'|-*.
  { simpl. intros X [= <-]. by destruct σ. }
  simpl. intros Hlc (trm&H1&H2)%bind_Some.
  eapply list_subseteq_cons_iff in HS' as (HS1&HS2).
  eapply IH in H1 as HL1. 2: done. 2: done. 2: done.
  pose (σm := mkState (shp σ) trm (scs σ) (snp σ) (snc σ)).
  eapply (tree_access_many_loc_controlled_helper_2 σm). 3: done. 3: exact H2.
  2:  eapply elem_of_elements, HS1.
  eapply tree_access_many_state_wf_helper_1. 3: exact H1. 1: done.
  done.
Qed.

Local Lemma big_ext σ blk X (S : list (tag * gmap Z access_kind)):
  blk ∈ dom X →
  foldr (λ '(tg, L) trs1, (trs1 : option trees) ≫= λ trs1, map_fold (λ l acc (trs2 : option trees), trs2 ≫= (apply_within_trees (memory_access_nonchildren_only acc σ.(scs) tg (l, 1%nat)) blk)) (Some trs1) L) (Some X) S =
  foldr (λ tgL trs1, (trs1 : option trees) ≫= λ trs1, apply_within_trees (λ tr, map_fold (λ l acc (tr2: option (tree item)), tr2 ≫= λ tr3, memory_access_nonchildren_only acc σ.(scs) tgL.1 (l, 1%nat) tr3) (Some tr) tgL.2) blk trs1) (Some X) S.
Proof.
  induction S as [|[tg L] S IH] in X|-*; intros Hin.
  1: done.
  1: simpl. rewrite IH.
  2: done.
  edestruct foldr as [t|] eqn:Heq. 2: done.
  simpl. rewrite  apply_within_trees_map_fold. 1: done.
  clear IH. 
  induction S as [|[] ? IH] in Heq,t,Hin,X|-*.
  1: simpl in *; simplify_eq; done.
  simpl in Heq. eapply bind_Some in Heq as (x&Hx&Hy).
  eapply IH in Hx. 2: done.
  erewrite <- apply_within_trees_same_dom. 2: done.
  done.
Qed.

Lemma loc_controlled_trees_access_all_protected_initialized_1 l c sc σ trs' tg_lu tk :
  c ∈ scs σ →
  trees_access_all_protected_initialized (scs σ) c (strs σ) = Some trs' →
  state_wf σ →
  loc_controlled l tg_lu tk sc σ →
  state_wf (set_strs σ trs') ∧ loc_controlled l tg_lu tk sc (set_strs σ trs').
Proof.
  intros Hactive Hx.
  assert (dom trs' = dom σ.(strs)) as Hdom.
  1: symmetry; by eapply trees_access_all_protected_initialized_same_dom.
  revert trs' Hdom Hx.
  assert (∃ S, elements S ⊆ elements (dom (strs σ)) ∧ S = dom (strs σ)) as (S&HS1&HS2).
  { eexists. split; last done. reflexivity. }
  rewrite /trees_access_all_protected_initialized -{2}HS2. clear HS2.
  revert HS1.
  rewrite /set_fold /=.
  opose proof (NoDup_elements S) as HNoDup.
  induction (elements S) as [|blk Sx IH] in HNoDup|-*; intros Hele trs' Hdom2 Happly Hwf Hlc.
  { simpl in Happly. injection Happly as <-. by destruct σ. }
  eapply NoDup_cons in HNoDup as (HNoElem&HNoFoo).
  simpl in Happly. eapply bind_Some in Happly as (trs2&Htrs2&Happly).
  pose (σ2 := mkState σ.(shp) trs2 σ.(scs) σ.(snp) σ.(snc)).
  eapply apply_within_trees_same_dom in Happly as Hdom3.
  ospecialize (IH _ _ trs2 _ _ _ _). 1: done. 1: set_solver.
  1: rewrite -Hdom2; by eapply apply_within_trees_same_dom. 1-3: done.
  assert (blk ∈ dom (strs σ2)) as [x Hx]%elem_of_dom.
  1: set_solver. destruct IH as (IHwf&IH).
  rewrite /apply_within_trees Hx /= in Happly.
  eapply bind_Some in Happly as (tr'&Htr'&[= <-]).
  rewrite /tree_access_all_protected_initialized in Htr'.
  assert (PS σ2 (tree_get_all_protected_tags_initialized_locs c x) blk) as HPS.
  { split; first done. intros tg L HL.
    rewrite /trees_lookup /trees_at_block Hx.
    eapply tree_all_protected_initialized_exists_node in HL.
    eapply exists_node_eqv_existential in HL as (it&Hit&Htg&Hprot&Hrst).
    exists it. split_and!.
    - exists x. split; first done. subst tg. eapply exists_node_to_tree_lookup.
      2: done. 1: by eapply IHwf.
    - exists c. split; last done. done.
    - intros z v (H1&H2&H3)%Hrst. do 2 (split; first done).
      intros H%H3. done. }
  opose proof (tree_access_many_loc_controlled_helper_1 σ2 _ _ _ _ _ _ _ _ _ _) as H.
  2: done.
  2: { rewrite big_ext. 2: by eapply elem_of_dom_2.
       rewrite -apply_within_trees_foldr. 2: by eapply elem_of_dom_2.
       rewrite /apply_within_trees Hx. rewrite /=.
       rewrite /set_fold in Htr'.
       eapply bind_Some.
       exists tr'. split; last done.
       erewrite foldr_ext. 1: exact Htr'. 2-3: done.
       intros [] a. done. } 1: done.
  edestruct (tree_access_many_state_wf_helper_1 σ2) as (H1&H2).
  1: done. 1: reflexivity. 
  1: { rewrite big_ext. 2: by eapply elem_of_dom_2.
       rewrite -apply_within_trees_foldr. 2: by eapply elem_of_dom_2.
       rewrite /apply_within_trees Hx. rewrite /=.
       rewrite /set_fold in Htr'.
       eapply bind_Some.
       exists tr'. split; last done.
       erewrite foldr_ext. 1: exact Htr'. 2-3: done.
       intros [] a. done. }
  split; first apply H1. 1: done.
Qed.

Lemma loc_controlled_trees_access_all_protected_initialized l c sc σ σ' tg_lu tk:
  c ∈ scs σ →
  trees_access_all_protected_initialized (scs σ) c (strs σ) = Some (strs σ') →
  shp σ = shp σ' →
  scs σ ∖ {[ c ]} = scs σ' →
  snc σ = snc σ' →
  snp σ = snp σ' →
  state_wf σ →
  loc_controlled l tg_lu tk sc σ →
  loc_controlled l tg_lu tk sc σ'.
Proof.
  intros Hcc H1 H2 H3 H4 H5 HWF Hlc1.
  pose (σ2 := (set_strs σ σ.(strs))).
  odestruct (loc_controlled_trees_access_all_protected_initialized_1 _ _ _ σ) as (HWF2&Hlc2).
  1: done. 1:done. 1: done. 1: exact Hlc1.
  destruct σ' as [x1 x2 x3 x4 x5]. simpl in *. subst x1 x3 x4 x5.
  intros Hpre'. simpl.
  edestruct Hlc2 as (Hpost&HHL). 1: done.
  split; last done.
  destruct tk; [done| |done].
  destruct Hpost as (it&tr&Hit&Htr&Hinit&Hown&Hothers).
  exists it, tr. do 3 (split; first done).
  split.
  - intros Hit3. clear Hothers. ospecialize (Hown _).
    { intros Hperm. destruct (Hit3 Hperm) as (cc&Hcc1&Hcc2).
      exists cc. split; try done. eapply elem_of_difference, Hcc2. }
    done.
  - intros it' t' H. specialize (Hothers it' t' H).
    destruct (rel_dec tr t' tg_lu) as [[]|]. 1,3: eapply Hothers.
    destruct Hothers as [?|Hothers]; first by left. right.
    destruct (perm (item_lookup it' l.2)) as [|?| | | |]. 1, 3, 4, 6: done.
    all: do 2 try (destruct Hothers as [Hothers|Hothers]; [left; try done|right]).
    all: intros HP; eapply Hothers; intros.
    all: destruct HP as (cc&Hccx&HHcc); try done.
    all: exists cc; split; first done. all: eapply elem_of_difference in HHcc; eapply HHcc.
Qed.

Lemma loc_controlled_alloc_creates_local l σ σ' blk nt sz :
  init_mem (fresh_block (shp σ), 0) sz (shp σ) = shp σ' →
  extend_trees nt blk 0 sz (strs σ) = strs σ' →
  scs σ = scs σ' →
  state_wf σ →
  blk = fresh_block (shp σ) →
  l.1 = blk →
  0 ≤ l.2 < sz →
  loc_controlled l nt tk_local ☠%S σ'.
Proof.
  intros Heq_shp Hnewtrees Heq_scs Hwf Hblk Hblk2 Hsz _.
  subst blk. destruct l as [blk off]. pose (blk, off) as l. simpl in *. subst blk.
  assert (shp σ' !! l = Some ☠%S) as Hheap.
  { rewrite -Heq_shp /=. eapply init_mem_lookup_fresh_poison. lia. }
  split; last done.
  epose proof (init_perms_lookup Active 0 sz off) as H.
  eexists _, _. rewrite /bor_state_own_on. split_and!.
  2: rewrite -Hnewtrees /= /extend_trees lookup_insert_eq //.
  - by eapply tree_lookup_init_tree.
  - rewrite /item_lookup /=. destruct (init_perms _ _ _ !! off). 2: lia.
    destruct H as [-> _]. done.
  - rewrite /item_lookup /=. destruct (init_perms _ _ _ !! off). 2: lia.
    destruct H as [-> _]. done.
  - done.
  - intros ? t' (Ht'&_). cbv in Ht'. tauto.
Qed.

Lemma bor_state_own_enables_read b range σ blk tk tg :
  state_wf σ →
  (∀ l, range'_contains range l → bor_state_own (blk, l) tg tk σ) →
  range.2 ≠ 0%nat →
  trees_contain tg σ.(strs) blk ∧
  ∃ trs', apply_within_trees (memory_access_maybe_nonchildren_only b AccessRead σ.(scs) tg range) blk σ.(strs) = Some trs'.
Proof.
  intros Hwf Hhl Hnn.
  assert (∃ tr, σ.(strs) !! blk = Some tr ∧ tree_contains tg tr) as (tr&Htr&Hcont).
  { ospecialize (Hhl range.1 _).
    1: rewrite /range'_contains; lia.
    destruct Hhl as (it&tr&Hit&Htr&_). eexists. split; first done. eapply Hit. }
  split.
  1: rewrite /trees_contain /trees_at_block Htr //.
  rewrite /apply_within_trees Htr /=. eapply is_Some_ignore_bind.
  rewrite /memory_access_maybe_nonchildren_only. eapply apply_access_success_condition.
  eapply every_node_eqv_universal.
  intros it Hitin%exists_node_to_tree_lookup.
  2: eapply Hwf, Htr.
  rewrite /item_apply_access /permissions_apply_range'. eapply is_Some_ignore_bind.
  eapply mem_apply_range'_success_condition. intros off Hinrange.
  specialize (Hhl off Hinrange) as Hown.
  destruct Hown as (it_tg&tr'&Hittg&Htr'&Hinit&Htk). simpl in *.
  assert (tr = tr') as <- by congruence.
  edestruct maybe_non_children_only_effect_or_nop as [Heq|Heq]; erewrite Heq; clear Heq.
  2: done.
  rewrite rel_dec_flip2.
  assert (tg = itag it → rel_dec tr (itag it) tg = Child This) as Hlocalfalse.
  { intros ->. by rewrite rel_dec_refl. }
  rewrite /apply_access_perm /apply_access_perm_inner.
  change (default _ _) with (item_lookup it off).
  destruct (rel_dec tr (itag it) tg) as [[]|[]] eqn:Hreldec.
  - simpl. rewrite /apply_access_perm /apply_access_perm_inner.
    assert (perm (item_lookup it off) ≠ Disabled) as Hndis.
    { destruct tk; destruct Htk as (Hsame&Hothers). 3: destruct Hothers as (_&Hothers).
      all: specialize (Hothers it _ Hitin). 3: exfalso; by ospecialize (Hlocalfalse _).
      all: rewrite Hreldec // in Hothers. }
    destruct (item_lookup it off) as [ii [| | | | |]]; try done.
    all: rewrite /= most_init_comm /= if_both_sides_same /= //.
  - simpl. rewrite /apply_access_perm /apply_access_perm_inner.
    assert (perm (item_lookup it off) ≠ Active) as Hnact.
    { destruct tk; destruct Htk as (Hsame&Hothers). 3: destruct Hothers as (_&Hothers).
      all: specialize (Hothers it _ Hitin). 3: exfalso; by ospecialize (Hlocalfalse _).
      all: rewrite Hreldec //= in Hothers.
      intros Hactive. rewrite Hactive in Hothers.
      destruct Hothers as [Hlazy|[]].
      opose proof (state_wf_tree_compat _ Hwf _ _ Htr) as Hnlazy.
      eapply every_node_eqv_universal in Hnlazy.
      2: { eapply tree_lookup_to_exists_node. exact Hitin. }
      rewrite /item_lookup /= in Hactive,Hlazy.
      destruct (iperm it !! off) as [pp|] eqn:Heq; simpl in *.
      - opose proof (item_perms_valid _ _ _ Hnlazy) as Hforall.
        eapply map_Forall_lookup_1 in Hforall. 2: exact Heq. eapply Hforall in Hactive. congruence.
      - by eapply item_default_perm_valid in Hactive. }
    destruct (item_lookup it off) as [ii [|[]| | | |]] eqn:Heq; simpl.
    1,2,3,4,6: destruct ii, bool_decide; simpl in *; done.
    1: done.
    destruct ii, bool_decide eqn:Hprot. all: simpl; try done.
    opose proof (state_wf_tree_not_disabled _ Hwf _ _ Htr (itag it)) as Hndis.
    eapply every_child_ParentChildIn with (tg' := itag it) in Hndis.
    2: by eapply Hwf. 2,4: eapply Hwf; first done; eapply Hitin. 2: eapply Hitin. 2: by left.
    eapply every_node_eqv_universal in Hndis.
    2: { eapply tree_lookup_to_exists_node. exact Hitin. }
    eapply bool_decide_eq_true_1 in Hprot.
    ospecialize (Hndis _ _ _).
    1: done. 1: by erewrite Heq. 1: done. rewrite Heq in Hndis. by destruct Hndis.
  - simpl. rewrite /apply_access_perm /apply_access_perm_inner.
    assert (perm (item_lookup it off) ≠ Active) as Hnact.
    { destruct tk; destruct Htk as (Hsame&Hothers). 3: destruct Hothers as (_&Hothers).
      all: specialize (Hothers it _ Hitin) as Ho2. 3: exfalso; by ospecialize (Hlocalfalse _).
      all: rewrite Hreldec //= in Ho2.
      clear Ho2. rewrite /rel_dec in Hreldec.
      destruct (decide (ParentChildIn _ _ tr)) as [HPC|]; last done.
      destruct (decide (ParentChildIn _ _ tr)) as [|HnPC]; first done. clear Hreldec.
      destruct HPC as [?|HSPC]. 1: exfalso; eapply HnPC; by left.
      eapply immediate_sandwich in HSPC as HIPC.
      2: by eapply Hwf. 2: eapply Hwf; first done; eapply Hittg.
      destruct HIPC as (tsw&HIPC&HPC).
      assert (tree_contains tsw tr) as Htswin1.
      { eapply contains_child. 1: right; by eapply Immediate_is_StrictParentChild. eapply Hittg. }
      assert (tree_unique tsw tr) as Htswin2 by by eapply Hwf.
      eapply unique_implies_lookup in Htswin2 as (itsw&Hitsw).
      specialize (Hothers _ _ Hitsw).
      rewrite /rel_dec decide_True in Hothers.
      2: right; by eapply Immediate_is_StrictParentChild.
      rewrite decide_False in Hothers.
      2: { intros Hc. eapply immediate_parent_not_child. 3: done. 3: done. all: eapply Hwf; first done. 2: done. 1: eapply Hittg. }
      rewrite decide_True // in Hothers.
      intros Hactive.
      opose proof (state_wf_tree_more_active _ Hwf _ _ Htr tsw) as Hndis.
      eapply every_child_ParentChildIn with (tg' := itag it) in Hndis.
      2: by eapply Hwf. 2,4: eapply Hwf; first done. 2: done. 2: eapply Hitin. 2: eapply Hitsw. 2: done.
      eapply every_node_eqv_universal in Hndis.
      2: { eapply tree_lookup_to_exists_node. exact Hitin. }
      ospecialize (Hndis _ off _). 1,2: done. destruct Hndis as [Hndis|Hndis]; by rewrite /= Hndis in Hothers. }
    destruct (item_lookup it off) as [ii [|[]| | | |]] eqn:Heq; simpl.
    1,2,3,4,6: destruct ii, bool_decide; simpl in *; done.
    1: done.
    destruct ii, bool_decide eqn:Hprot. all: simpl; try done.
    opose proof (state_wf_tree_not_disabled _ Hwf _ _ Htr (itag it)) as Hndis.
    eapply every_child_ParentChildIn with (tg' := itag it) in Hndis.
    2: by eapply Hwf. 2,4: eapply Hwf; first done; eapply Hitin. 2: eapply Hitin. 2: by left.
    eapply every_node_eqv_universal in Hndis.
    2: { eapply tree_lookup_to_exists_node. exact Hitin. }
    eapply bool_decide_eq_true_1 in Hprot.
    ospecialize (Hndis _ _ _).
    1: done. 1: by erewrite Heq. 1: done. rewrite Heq in Hndis. by destruct Hndis.
  - rewrite /rel_dec in Hreldec.
    do 2 (edestruct (decide (ParentChildIn _ _ _)); try done).
    assert (tg = itag it) as ->.
    { eapply mutual_parent_child_implies_equal. 3,4: done. 2: eapply Hittg. 1: eapply Hitin. }
    assert (it = it_tg) as <-.
    { eapply tree_lookup_unique; done. }
    rewrite /apply_access_perm /apply_access_perm_inner /=.
    assert (perm (item_lookup it off) ≠ Disabled) as Hndis.
    { destruct tk; destruct Htk as (Hsame&_).
      1, 3: by rewrite Hsame.
      intros Hdis. rewrite !Hdis in Hsame.
      eapply Hsame. by intros [=]. }
    destruct (item_lookup it off) as [ii [| | | | |]]; try done.
    all: rewrite /= most_init_comm /= if_both_sides_same /= //.
Qed.

Lemma asymmetric_read_prot_pre_from_bor_state_own σ blk tr acc_tg range it tk :
  state_wf σ →
  σ.(strs) !! blk = Some tr →
  tree_lookup tr acc_tg it →
  (∀ off, range'_contains range off → bor_state_own_on (blk, off) acc_tg tk σ it tr) →
  tree_equal_asymmetric_read_pre_protected tr range it acc_tg (match tk with tk_pub => false | _ => true end).
Proof.
  intros Hwf Htr Hit Hhl.
  intros off Hoff. specialize (Hhl off Hoff) as (Hini&Hhl).
  simpl. rewrite Hini. split; first done.
  assert (∀ tg' it' pp, tree_lookup tr tg' it' → rel_dec tr tg' acc_tg = Foreign (Parent pp) → initialized (item_lookup it' off) = PermInit) as Hinit.
  { intros tg' it' pp H1 H2. opose proof (state_wf_tree_more_init _ Hwf _ _ Htr tg') as Hpmi.
    rewrite /rel_dec in H2. destruct decide as [HP1|HnP1]; first done. destruct decide as [HP2|HnP2]; last done.
    eapply every_child_ParentChildIn in Hpmi.
    2,3: eapply Hwf; try done. 2,3: eapply H1. 2: eapply Hwf; try done; eapply Hit. 2: done.
    eapply tree_lookup_correct_tag in Hit as Htg; subst acc_tg.
    eapply every_node_eqv_universal in Hpmi.
    2: eapply tree_lookup_to_exists_node, Hit. eapply Hpmi. 1: done. done. }
  destruct tk as [|uk|].
  - destruct Hhl as (Hfrz&Hothers).
    rewrite Hfrz. split; first done. split; first done.
    intros tg' it' Hit'. specialize (Hothers _ _ Hit'). specialize (Hinit tg' it').
    destruct (rel_dec tr tg' acc_tg) as [[]|[]]; (split; [|split; [done|intros ? [=]]]).
    + split; last done. by eapply Hinit.
    + done.
    + done.
    + done.
    + done.
  - destruct Hhl as (Hnd&Hothers).
    split. { intros Hdis. rewrite /= Hdis in Hnd. by eapply Hnd. }
    split. { intros Hcell. rewrite /= Hcell in Hnd. by eapply Hnd. }
    intros tg' it' Hit'. specialize (Hothers _ _ Hit'). specialize (Hinit tg' it').
    destruct (rel_dec tr tg' acc_tg) as [[]|[[]|]]; (split; [|intros [=]]).
    + split; last done. by eapply Hinit.
    + intros Hactive. rewrite /= Hactive in Hothers.
      destruct Hothers as [Hothers|[]].
      opose proof (state_wf_tree_compat _ Hwf _ _ Htr) as Hda.
      eapply tree_lookup_correct_tag in Hit' as Htg'; subst tg'.
      eapply every_node_eqv_universal in Hda.
      2: eapply tree_lookup_to_exists_node, Hit'.
      rewrite /item_lookup in Hactive,Hothers. destruct (iperm it' !! off) as [lp|] eqn:Heq; simpl in *.
      * opose proof (item_perms_valid _ _ _ Hda) as Hpwf. eapply map_Forall_lookup_1 in Hpwf. 2: exact Heq.
        rewrite Hpwf // in Hothers.
      * eapply item_default_perm_valid. 1: exact Hda. done.
    + done.
    + done.
    + done.
    + done.
  - destruct Hhl as (Hact&Hnoprot&Hothers).
    rewrite Hact. split; first done. split; first done.
    intros tg' it' Hit'. specialize (Hothers _ _ Hit'). subst tg'.
    rewrite rel_dec_refl. done.
Qed.


Lemma source_only_read_pre_from_bor_state_own σ blk tr acc_tg range it tk :
  state_wf σ →
  σ.(strs) !! blk = Some tr →
  tree_lookup tr acc_tg it →
  (∀ off, range'_contains range off → bor_state_own_on (blk, off) acc_tg tk σ it tr) →
  tree_equal_asymmetric_read_pre_source tr range it acc_tg.
Proof.
  intros H1 H2 H3 H4.
  opose proof (asymmetric_read_prot_pre_from_bor_state_own σ blk tr acc_tg range it tk H1 H2 H3 H4) as HH.
  intros off Hoff pp_acc.
  specialize (HH off Hoff) as (HH1&HH2&HHnCell&HH3).
  do 2 (split; first done).
  intros tg' it' H' pp rd.
  specialize (HH3 _ _ H') as (HH4&HH5).
  opose proof (state_wf_tree_compat _ H1 _ _ H2) as Hiwf.
  eapply every_node_eqv_universal in Hiwf.
  2: eapply tree_lookup_to_exists_node, H'.
  subst rd. destruct (rel_dec tr tg' acc_tg) as [[]|[]].
  1,4: done.
  all: subst pp; eapply item_wf_item_lookup_active, Hiwf.
Qed.

Lemma bor_state_own_unq_act_enables_write b range σ blk tg it_acc :
  state_wf σ →
  (∀ l, range'_contains range l → bor_state_own (blk, l) tg (tk_unq tk_act) σ) →
  trees_lookup σ.(strs) blk tg it_acc →
  protector_is_active it_acc.(iprot) σ.(scs) →
  ∃ trs', apply_within_trees (memory_access_maybe_nonchildren_only b AccessWrite σ.(scs) tg range) blk σ.(strs) = Some trs'.
Proof.
  intros Hwf Hhl (tr&Htr&Hit) Hprot.
  rewrite /apply_within_trees Htr /=. eapply is_Some_ignore_bind.
  rewrite /memory_access_maybe_nonchildren_only. eapply apply_access_success_condition.
  eapply every_node_eqv_universal.
  intros it Hitin%exists_node_to_tree_lookup.
  2: eapply Hwf, Htr.
  rewrite /item_apply_access /permissions_apply_range'. eapply is_Some_ignore_bind.
  eapply mem_apply_range'_success_condition. intros off Hinrange.
  specialize (Hhl off Hinrange) as Hown.
  destruct Hown as (it_tg&tr'&Hittg&Htr'&Hinit&Htk). simpl in *.
  assert (tr = tr') as <- by congruence.
  assert (it_acc = it_tg) as <- by by eapply tree_lookup_unique.
  edestruct maybe_non_children_only_effect_or_nop as [Heq|Heq]; erewrite Heq; clear Heq.
  2: done.
  rewrite rel_dec_flip2.
  assert (tg = itag it → rel_dec tr (itag it) tg = Child This) as Hlocalfalse.
  { intros ->. by rewrite rel_dec_refl. }
  rewrite /apply_access_perm /apply_access_perm_inner.
  change (default _ _) with (item_lookup it off).
  destruct Htk as (Hsame&Hothers).
  assert (perm (item_lookup it_acc off) = Active) as Hactive.
  { ospecialize (Hsame _); first done.
    simpl in Hsame. destruct perm as [|?| | | |]; done. }
  destruct (rel_dec tr (itag it) tg) as [[]|[]] eqn:Hreldec.
  - simpl. rewrite /apply_access_perm /apply_access_perm_inner.
    assert (perm (item_lookup it off) = Active ∨ perm (item_lookup it off) = Cell) as [Hndis|Hndis].
    { opose proof (state_wf_tree_more_active _ Hwf _ _ Htr (itag it)) as Hma.
      eapply every_child_ParentChildIn in Hma. 2,3,5: eapply Hwf; first done. 2,4: eapply Hitin. 2: eapply Hit.
      2: rewrite /rel_dec in Hreldec; do 2 (destruct decide in Hreldec); done.
      eapply every_node_eqv_universal in Hma.
      2: eapply tree_lookup_to_exists_node, Hit.
      eapply Hma. 2: done. by eapply tree_lookup_correct_tag. }
    all: rewrite Hndis /=; by repeat case_match.
  - simpl. rewrite /apply_access_perm /apply_access_perm_inner.
    specialize (Hothers _ _ Hitin). rewrite Hreldec in Hothers.
    destruct Hothers as [Hlazy|Hnothing].
    1: rewrite Hlazy /=; by repeat case_match.
    simpl in *. destruct (perm (item_lookup it off)) as [|?| | | |] eqn:Hpermeq.
    + clear. by repeat case_match.
    + destruct Hnothing as [H1|H1]. 1: done. exfalso; eapply H1; done.
    + rewrite bool_decide_eq_false_2.
      { rewrite /=. by (repeat case_match; try done). }
      intros Hhasprot.
      opose proof (state_wf_tree_compat _ Hwf _ _ Htr) as HH.
      eapply every_node_iff_every_lookup in HH. 3: exact Hitin.
      2: { intros x Hx. by eapply unique_lookup, Hwf. }
      eapply item_perms_reserved_im_protected. 1: exact HH.
      2: eapply Hpermeq.
      destruct Hhasprot as (c&Hc&_).
      destruct (iprot it); done.
    + done.
    + destruct Hnothing as [H1|H1]. 1: done. exfalso; eapply H1; done.
    + simpl. rewrite most_init_comm /=.
      destruct (initialized (item_lookup it off)) eqn:Hiniteq; try done.
      rewrite bool_decide_eq_false_2 //.
      intros Hprotit.
      opose proof (state_wf_tree_not_disabled _ Hwf _ _ Htr (itag it)) as Hnd.
      eapply every_child_ParentChildIn in Hnd. 2,3,5: eapply Hwf; first done. 2-4: eapply Hitin.
      2: by left.
      eapply every_node_eqv_universal in Hnd.
      2: eapply tree_lookup_to_exists_node, Hitin.
      destruct Hnd as [Hnd|Hcell].
      1,3: done. 1: exact Hiniteq. 1: done. congruence.
  - simpl. rewrite /apply_access_perm /apply_access_perm_inner.
    assert (initialized (item_lookup it off) = PermInit → perm (item_lookup it off) ≠ Cell → protector_is_active it.(iprot) σ.(scs) → False ) as Hnact.
    { specialize (Hothers it _ Hitin) as Ho2.
      rewrite Hreldec //= in Ho2.
      clear Ho2. rewrite /rel_dec in Hreldec.
      destruct (decide (ParentChildIn _ _ tr)) as [HPC|]; last done.
      destruct (decide (ParentChildIn _ _ tr)) as [|HnPC]; first done. clear Hreldec.
      destruct HPC as [?|HSPC]. 1: exfalso; eapply HnPC; by left.
      eapply immediate_sandwich in HSPC as HIPC.
      2: by eapply Hwf. 2: eapply Hwf; first done; eapply Hittg.
      destruct HIPC as (tsw&HIPC&HPC).
      assert (tree_contains tsw tr) as Htswin1.
      { eapply contains_child. 1: right; by eapply Immediate_is_StrictParentChild. eapply Hittg. }
      assert (tree_unique tsw tr) as Htswin2 by by eapply Hwf.
      eapply unique_implies_lookup in Htswin2 as (itsw&Hitsw).
      specialize (Hothers _ _ Hitsw).
      rewrite /rel_dec decide_True in Hothers.
      2: right; by eapply Immediate_is_StrictParentChild.
      rewrite decide_False in Hothers.
      2: { intros Hc. eapply immediate_parent_not_child. 3: done. 3: done. all: eapply Hwf; first done. 2: done. 1: eapply Hittg. }
      rewrite decide_True // in Hothers.
      intros Hisinit Hnotcell Hisprot.
      opose proof (state_wf_tree_not_disabled _ Hwf _ _ Htr tsw) as Hndis.
      eapply every_child_ParentChildIn with (tg' := itag it) in Hndis.
      2: by eapply Hwf. 2,4: eapply Hwf; first done. 2: done. 2: eapply Hitin. 2: eapply Hitsw. 2: done.
      eapply every_node_eqv_universal in Hndis.
      2: { eapply tree_lookup_to_exists_node. exact Hitin. }
      odestruct (Hndis _ _ _) as [Hndis'|Hcell]. 1: done. 1: exact Hisinit. 1: done. all: done. }
    destruct (item_lookup it off) as [[] [|[]| | | |]] eqn:Heq; simpl.
    all: destruct (bool_decide (protector_is_active (iprot it) (scs σ))) eqn:Hpdi; try done.
    all: eapply bool_decide_eq_true_1 in Hpdi.
    all: exfalso; by eapply Hnact.
  - rewrite /rel_dec in Hreldec.
    do 2 (edestruct (decide (ParentChildIn _ _ _)); try done).
    assert (tg = itag it) as ->.
    { eapply mutual_parent_child_implies_equal. 3,4: done. 2: eapply Hittg. 1: eapply Hitin. }
    assert (it = it_acc) as <-.
    { eapply tree_lookup_unique; done. }
    rewrite /apply_access_perm /apply_access_perm_inner /=.
    assert (perm (item_lookup it off) = Active) as Hndis.
    { ospecialize (Hsame _). 1: done. simpl in Hsame.
      destruct (perm (item_lookup it off)) as [|?| | | |].
      + done.
      + exfalso. by destruct Hsame.
      + done.
      + done.
      + done.
      + done. }
    rewrite Hndis most_init_comm /= if_both_sides_same /= //.
Qed.

Lemma asymmetric_write_prot_pre_from_bor_state_own_unq σ blk tr acc_tg range it :
  state_wf σ →
  σ.(strs) !! blk = Some tr →
  tree_lookup tr acc_tg it →
  protector_is_active (iprot it) (scs σ) →
  (∀ off, range'_contains range off → bor_state_own_on (blk, off) acc_tg (tk_unq tk_act) σ it tr) →
  tree_equal_asymmetric_write_pre_protected σ.(scs) tr range it acc_tg.
Proof.
  intros Hwf Htr Hit Hprot Hhl.
  intros off Hoff. specialize (Hhl off Hoff) as (Hini&Hhl).
  simpl. rewrite Hini. split; first done.
  destruct Hhl as (Hown&Hothers); simpl in *.
  opose proof* Hown as Hown. 1: done.
  assert (perm (item_lookup it off) = Active) as Hactive.
  { destruct (perm (item_lookup it off)) as [|?| | | |]. all: done. }
  split; first done.
  intros tg' it' Hit'. specialize (Hothers _ _ Hit').
  destruct (rel_dec tr tg' acc_tg) as [[]|[[]|]] eqn:Hreldec.
  + opose proof (state_wf_tree_more_init _ Hwf _ _ Htr tg') as Hpmi.
    opose proof (state_wf_tree_more_active _ Hwf _ _ Htr tg') as Hpma.
    rewrite /rel_dec in Hreldec. destruct decide as [HP1|HnP1]; first done. destruct decide as [HP2|HnP2]; last done.
    eapply every_child_ParentChildIn in Hpmi.
    2,3: eapply Hwf; try done. 2,3: eapply Hit'. 2: eapply Hwf; try done; eapply Hit. 2: done.
    eapply every_child_ParentChildIn in Hpma.
    2,3: eapply Hwf; try done. 2,3: eapply Hit'. 2: eapply Hwf; try done; eapply Hit. 2: done.
    eapply tree_lookup_correct_tag in Hit as Htg; subst acc_tg.
    eapply every_node_eqv_universal in Hpmi.
    2: eapply tree_lookup_to_exists_node, Hit.
    eapply every_node_eqv_universal in Hpma.
    2: eapply tree_lookup_to_exists_node, Hit.
    split.
    1: by eapply Hpmi. by eapply Hpma.
  + destruct (item_lookup it' off) as [ini [|?| | | |]] eqn:Hlu; simpl in Hothers|-*.
    * done.
    * destruct Hothers as [->|[Hn1|Hc]]. 2: done.
      2: exfalso; by eapply Hc. done.
    * intros Hhasprot.
      opose proof (state_wf_tree_compat _ Hwf _ _ Htr) as HH.
      eapply every_node_iff_every_lookup in HH. 3: exact Hit'.
      2: { intros x Hx. by eapply unique_lookup, Hwf. }
      eapply item_perms_reserved_im_protected. 1: exact HH.
      2: { rewrite /item_lookup in Hlu. erewrite Hlu. done. }
      destruct Hhasprot as (c&Hc&_).
      destruct (iprot it'); done.
    * destruct Hothers as [->|[]]. 1: done.
    * destruct Hothers as [->|[[=]|Hc]]. 1: done.
      1: exfalso. by eapply Hc.
    * done.
  + done.
  + done.
  + done.
Qed.

Lemma bor_state_own_on_not_reservedim σ blk tr tg it tk l sc :
  state_wf σ →
  σ.(strs) !! blk = Some tr →
  tree_lookup tr tg it →
  perm (item_lookup it l) = ReservedIM →
  loc_controlled (blk, l) tg tk sc σ  →
  False.
Proof.
  intros H1 H2 Hit Him Hlc; simpl in *.
  destruct Hlc as (Hlc&_).
  { destruct tk. 3: done.
    all: exists it; split; first by exists tr.
    all: rewrite /= Him //. }
  destruct Hlc as (it1&tr1&Hit1&Htr1&_&H3B).
  assert (tr1 = tr) as -> by (simpl in *; congruence). clear Htr1.
  assert (it1 = it) as ->. { eapply tree_lookup_unique. 1-2: done. } clear Hit1.
  rewrite /bor_state_post_unq /= Him in H3B.
  destruct tk.
  - by destruct H3B.
  - destruct H3B as [H3B _]; eapply H3B. done.
  - by destruct H3B.
Qed.

Lemma bor_state_own_no_active_child σ blk tr sc tg tk l :
  state_wf σ →
  σ.(strs) !! blk = Some tr →
  tree_contains tg tr →
  loc_controlled (blk, l) tg tk sc σ →
  active_child σ.(scs) tr tg l →
  False.
Proof.
  intros Hwf Htr Hcont Hlc.
  intros (ita&ii&Hita&Hreldec&HitaA&Haprot).
  assert (tree_unique tg tr) as (it&Hit)%unique_implies_lookup by by eapply Hwf.
  odestruct (Hlc _) as ((it1&tr1&Hit1&Htr1&Hown)&_).
  { opose proof (state_wf_tree_more_active _ Hwf _ _ Htr tg) as Hma.
    rewrite /rel_dec in Hreldec.
    destruct decide as [HPC|] in Hreldec; last done.
    eapply every_child_ParentChildIn in Hma.
    2: by eapply Hwf. 2: eapply Hwf; first done; eapply Hit.
    2: eapply Hit. 3: exact HPC. 2: eapply Hwf; first done; eapply Hita.
    eapply every_node_eqv_universal in Hma.
    2: eapply tree_lookup_to_exists_node, Hita.
    ospecialize (Hma eq_refl l).
    rewrite HitaA in Hma. specialize (Hma eq_refl).
    destruct tk. 3: done.
    all: exists it; split; first (exists tr; done).
    all: destruct Hma as [Hma|Hma]; rewrite /= Hma; done. }
  assert (tr1 = tr) as -> by (simpl in Htr1; congruence). clear Htr1.
  assert (it1 = it) as ->. { eapply tree_lookup_unique. 1-2: done. } clear Hit1.
  destruct tk.
  - destruct Hown as (H1&H2&H3). specialize (H3 _ _ Hita). rewrite Hreldec in H3.
    rewrite HitaA in H3. done.
  - destruct Hown as (H1&H2&H3). clear H2.
    rewrite /rel_dec in Hreldec.
    destruct decide as [HPC1|HnPC1] in Hreldec; try done.
    destruct decide as [HPC2|HnPC2] in Hreldec; try done.
    destruct HPC1 as [->|HSPC]. 1: { eapply HnPC2. by left. }
    eapply immediate_sandwich in HSPC as Himm.
    2: by eapply Hwf. 2: eapply Hwf; first done. 2: eapply Hit.
    destruct Himm as (imm&Himm&HPC).
    assert (tree_unique imm tr) as (itm&Hitm)%unique_implies_lookup.
    { eapply Hwf. 1: done. eapply contains_child; last eapply Hit. right. by eapply Immediate_is_StrictParentChild. }
    specialize (H3 _ _ Hitm).
    rewrite /rel_dec in H3. rewrite decide_True in H3.
    2: right; by eapply Immediate_is_StrictParentChild.
    rewrite decide_False in H3.
    2: { intros Hpc. eapply immediate_parent_not_child. 4: exact Hpc. 3: done. all: eapply Hwf; first done. 1: eapply Hit. eapply Hitm. }
    rewrite decide_True // in H3. simpl in H3.
    opose proof (state_wf_tree_more_active _ Hwf _ _ Htr imm) as Hma.
    eapply every_child_ParentChildIn in Hma.
    2: by eapply Hwf. 2: eapply Hwf; first done; eapply Hitm.
    2: eapply Hitm. 3: exact HPC. 2: eapply Hwf; first done; eapply Hita.
    eapply every_node_eqv_universal in Hma.
    2: eapply tree_lookup_to_exists_node, Hita.
    ospecialize (Hma eq_refl l).
    rewrite HitaA in Hma. rewrite H3 in Hma.
    specialize (Hma eq_refl). by destruct Hma.
  - destruct Hown as (H1&H2&_&H3). specialize (H3 _ _ Hita).
    subst tg. rewrite rel_dec_refl in Hreldec. done.
Qed.


