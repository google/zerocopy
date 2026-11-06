(** Statements of success conditions for borrow steps.
    The goal is to be able to prove a [bor_step] statement. *)

From simuliris.tree_borrows Require Export steps_wf.
From Equations Require Import Equations.

Lemma alloc_base_step P σ sz :
  state_wf σ ->
  (sz > 0)%nat ->
  let l := (fresh_block σ.(shp), 0) in
  let t := σ.(snp) in
  let σ' := mkState (init_mem l sz σ.(shp))
                    (extend_trees t l.1 0 sz σ.(strs)) σ.(scs) (S t) σ.(snc) in
  base_step P (Alloc sz) σ (Place l t sz) σ' [].
Proof.
  simpl. econstructor.
  - econstructor.
  - apply (AllocIS (strs σ) (scs σ) (snp σ) (snc σ) (fresh_block (shp σ)) 0).
    2: assumption.
    assert (forall i, (fresh_block (shp σ), i) ∉ dom (shp σ)) as FreshHp by apply is_fresh_block.
    apply not_elem_of_dom.
    rewrite state_wf_dom; [|assumption].
    intro FreshMap.
    destruct (elem_of_map_1 fst (dom (shp σ)) (fresh_block (shp σ)) FreshMap) as [[blk z] [Fresh Dom]].
    apply (FreshHp z).
    rewrite Fresh; simpl.
    exact Dom.
Qed.

(* Basically, [tree_apply_access] works iff every node accepts the inner function being applied *)
Lemma apply_access_success_condition tr cids access_tag range fn :
  every_node (fun it => is_Some (item_apply_access fn cids (rel_dec tr access_tag (itag it)) range it)) tr
  <-> is_Some (tree_apply_access fn cids access_tag range tr).
Proof.
  rewrite /tree_apply_access.
  rewrite join_success_condition.
  rewrite every_node_map /compose.
  tauto.
Qed.

Lemma apply_access_fail_condition tr cids access_tag range fn :
  exists_node (fun it => item_apply_access fn cids (rel_dec tr access_tag (itag it)) range it = None) tr
  <-> tree_apply_access fn cids access_tag range tr = None.
Proof.
  rewrite /tree_apply_access.
  rewrite join_fail_condition.
  rewrite exists_node_map /compose.
  tauto.
Qed.

(* [mem_apply_range'] succeeds iff every offset succeeds. *)
Lemma mem_apply_range'_success_condition {X} (map : gmap Z X) fn range :
  (forall l, range'_contains range l -> is_Some (fn (map !! l))) <->
  is_Some (mem_apply_range' fn range map).
Proof.
  destruct range as [z sz].
  generalize dependent z.
  generalize dependent map.
  induction sz as [|sz IHsz]; intros map z.
  - rewrite /mem_apply_range' //=.
    split; intro.
    + econstructor; reflexivity.
    + rewrite /range'_contains; simpl. intros. lia.
  - split.
    + intro PerLoc.
      rewrite /mem_apply_range' //= /mem_apply_loc.
      destruct (PerLoc z) as [? H]. { rewrite /range'_contains //=; lia. }
      rewrite H //=.
      rewrite /mem_apply_range' //= in IHsz.
      eapply IHsz.
      intros l Contains.
      rewrite lookup_insert_ne.
      * apply PerLoc. rewrite /range'_contains //= in Contains |- *. lia.
      * rewrite /range'_contains //= in Contains. lia.
    + intros Success l InRange.
      inversion Success as [map' App'].
      rewrite /mem_apply_range' /= in App'.
      remember (mem_apply_loc _ _ _) as AppLoc eqn:HeqAppLoc.
      destruct AppLoc as [map''|]; last discriminate.
      simpl in *.
      destruct (decide (l = z)).
      * subst; simpl in *.
        rewrite /mem_apply_loc in HeqAppLoc.
        destruct (fn _); last discriminate; auto.
      * assert (range'_contains (z+1, sz) l) as InSubRange. {
          rewrite /range'_contains in InRange |- *. simpl in *. lia.
        }
        assert (map'' !! l = map !! l) as Eql. {
          rewrite /mem_apply_loc in HeqAppLoc.
          destruct (fn _); [simpl in *|discriminate].
          injection HeqAppLoc; intros; subst.
          rewrite lookup_insert_ne; [reflexivity|lia].
        }
        rewrite <- Eql.
        rewrite /mem_apply_loc in HeqAppLoc.
        assert (is_Some (mem_apply_range' fn (z+1, sz) map'')) as App''. {
         eexists. rewrite /mem_apply_range'. simpl. apply App'.
        }
        apply (proj2 (IHsz _ _) App'' l InSubRange).
Qed.

Lemma mem_apply_range'_fail_condition {X} (map : gmap Z X) fn range : 
  mem_apply_range' fn range map = None ↔
  ∃ l, range'_contains range l ∧ fn (map !! l) = None.
Proof.
  destruct range as [z n].
  rewrite /mem_apply_range' /range'_contains /=.
  induction n as [|n IH] in z,map|-*.
  { simpl. split; try done. intros (l&Hl1&Hl2). lia. }
  simpl; split.
  - intros [H|(x&H1&H2)]%bind_None.
    + exists z. simpl. split; first lia. eapply bind_None in H as [H|(y&Hy1&Hy2)]. 2: done.
      done.
    + destruct (IH x (z+1)) as (IH1&IH2). specialize (IH1 H2) as (l&Hl1&Hl2).
      exists l. split; first lia.
      eapply bind_Some in H1 as (x1&Hx1&[= <-]). rewrite lookup_insert_ne // in Hl2. lia.
  - intros (l&Hl1&Hl2). destruct (decide (l = z)) as [->|Hne].
    + rewrite /mem_apply_loc Hl2 /=. done.
    + destruct (mem_apply_loc fn z map) as [map2|] eqn:Hmap. 2: done.
      simpl. eapply IH. exists l. split; first lia.
      eapply bind_Some in Hmap as (x1&Hx1&[= <-]). rewrite lookup_insert_ne //.
Qed.


Definition is_access_compatible (tr : tree item) (cids : call_id_set) (tg : tag) (range : range') (kind : access_kind) (it : item ) :=
  forall l, range'_contains range l ->
    let initial := item_lookup it l in
    let protected := bool_decide (protector_is_active (iprot it) cids) in
    let rd := (rel_dec tr tg (itag it)) in
    exists post,
      apply_access_perm_inner kind rd protected (perm initial) = Some post
      /\ (post = Disabled -> (most_init (initialized initial) (requires_init rd) = PermLazy \/ protected = false)).

Lemma option_bind_always_some {X Y} (o : option X) (fn : X -> option Y) :
  is_Some o ->
  (forall i, is_Some (fn i)) ->
  is_Some (o ≫= fn).
Proof.
  intros oSome fnSome.
  destruct o; [|inversion oSome; discriminate].
  simpl.
  apply fnSome.
Qed.

Lemma option_bind_assoc {X Y Z} (o : option X) (f : X -> option Y) (g : Y -> option Z) :
  ((o ≫= fun i => f i) ≫= fun i => g i)
  = o ≫= (fun i => f i ≫= fun i => g i).
Proof.
  destruct o; simpl; done.
Qed.

Lemma all_access_compatible_implies_access_success kind tr cids tg range :
  every_node (is_access_compatible tr cids tg range kind) tr ->
  is_Some (memory_access kind cids tg range tr).
Proof.
  intro Compat. apply apply_access_success_condition.
  eapply every_node_increasing; [exact Compat|simpl].
  rewrite every_node_eqv_universal.
  intros it Ex CompatIt.
  rewrite /item_apply_access.
  apply option_bind_always_some; auto.
  simpl.
  rewrite /permissions_apply_range'.
  apply mem_apply_range'_success_condition.
  rewrite /apply_access_perm.
  intros l Range. specialize (CompatIt l Range).
  rewrite <- option_bind_assoc.
  apply option_bind_always_some; auto. 
  destruct CompatIt as [post [PostSpec ProtVulnerable]].
  rewrite PostSpec //=.
  change (default _ _) with (item_lookup it l).
  destruct (most_init _ _) eqn:Heq; last done.
  destruct (bool_decide (protector_is_active _ _)); [|done].
  destruct (decide (post = Disabled)); last first.
  1: { destruct post; auto. contradiction. }
  subst; auto.
  destruct (ProtVulnerable ltac:(reflexivity)); discriminate.
Qed.

(* For a protector to allow deallocation it must be weak or inactive *)
Definition item_deallocateable_protector cids (it: item) :=
  match it.(iprot) with
  | Some {| strong:=strong; call:=c |} => ¬ call_is_active c cids \/ strong = ProtWeak
  | _ => True
  end.

Lemma dealloc_base_step' P (σ: state) l tg (sz:nat) α' (WF: state_wf σ) :
  (∀ m : Z, is_Some (σ.(shp) !! (l +ₗ m)) ↔ 0 ≤ m ∧ m < sz) →
  (sz > 0)%nat →
  trees_contain tg (strs σ) l.1 →
  apply_within_trees (memory_deallocate σ.(scs) tg (l.2, sz)) l.1 σ.(strs) = Some α' →
  let σ' := mkState (free_mem l sz σ.(shp)) (delete l.1 α') σ.(scs) σ.(snp) σ.(snc) in
  base_step P (Free (Place l tg sz)) σ #[☠] σ' [].
Proof.
  intros Hdom Hpos Hcont Happly. destruct l as [blk off].
  econstructor; econstructor; auto.
Qed.

(* Success of `read_mem` on the heap is unchanged. *)
Lemma read_mem_is_Some' l n h :
  (∀ m, (m < n)%nat → l +ₗ m ∈ dom h) ↔
  is_Some (read_mem l n h).
Proof.
  induction n as [|n IH] in l|-*.
  1: simpl; split; intros; first done; lia.
  specialize (IH (l +ₗ 1)).
  setoid_rewrite shift_loc_assoc in IH.
  destruct IH as (IHl & IHr).
  split.
  - intros H. destruct IHl as (x & Hx).
    { intros m Hm. assert (1 + m = S m) as -> by lia. eapply H; lia. }
    rewrite /= Hx /=. setoid_rewrite elem_of_dom in H.
    destruct (H 0%nat) as (y & Hy); first lia.
    rewrite shift_loc_0 in Hy. rewrite Hy //.
  - simpl. intros (rmr&(rr&Hrr&(hl&Hhl&[= <-])%option_bind_inv)%option_bind_inv).
    intros [|m] Hm.
    1: rewrite shift_loc_0; by eapply elem_of_dom_2.
    assert (Z.of_nat (S m) = (1 + m)%Z) as -> by lia.
    apply IHr; last lia.
    by exists rr.
Qed.

Lemma read_mem_is_Some l n h
  (BLK: ∀ m, (m < n)%nat → l +ₗ m ∈ dom h) :
  is_Some (read_mem l n h).
Proof. by apply read_mem_is_Some'. Qed.

Lemma read_mem_values l n h v :
  read_mem l n h = Some v →
  length v = n ∧
  (∀ i, (i < n)%nat → h !! (l +ₗ i) = v !! i).
Proof.
  induction n as [|n IH] in l,v|-*.
  { simpl. intros [= <-]. split; first done. lia. }
  simpl. intros (rr&Hrr&(hl&Hhl&[= <-])%option_bind_inv)%option_bind_inv.
  destruct (IH _ _ Hrr) as (Hn&Hrst).
  split; first by rewrite -Hn.
  intros [|m] Hm.
  1: rewrite shift_loc_0 /= Hhl //.
  assert (Z.of_nat (S m) = (1 + m)%Z) as -> by lia.
  rewrite /= -Hrst /=; last lia.
  rewrite shift_loc_assoc //.
Qed.

Lemma read_mem_values' l n h v :
  length v = n →
  (∀ i, (i < n)%nat → h !! (l +ₗ i) = v !! i) →
  read_mem l n h = Some v.
Proof.
  intros <- Hs.
  destruct (read_mem_is_Some l (length v) h) as (v' & Hv').
  { intros m Hm. apply elem_of_dom. rewrite Hs; last done.
    apply lookup_lt_is_Some_2. done.
  }
  enough (v' = v) as -> by done.
  apply read_mem_values in Hv' as [Hlen Hv'].
  eapply list_eq_same_length; [reflexivity | lia | ].
  intros i sc sc' Hi.
  rewrite -Hs; last lia. rewrite -Hv'; last lia. intros -> [= ->]. done.
Qed.

Definition is_write (access: access_kind) : bool :=
  match access with AccessWrite => true | _ => false end.

Lemma apply_within_trees_unchanged fn blk trs trs' :
      (∀ tr, trs !! blk = Some tr → fn tr = Some tr) →
      apply_within_trees fn blk trs = Some trs' →
      trs' = trs.
Proof.
  intros Hsame (x&Hx&(y&Hy&[= <-])%bind_Some)%bind_Some.
  specialize (Hsame _ Hx). assert (y = x) as -> by congruence.
  rewrite insert_id //.
Qed.

Lemma copy_base_step' P (σ: state) l tg sz v trs' (WF: state_wf σ) :
  trees_contain tg σ.(strs) l.1 →
  read_mem l sz σ.(shp) = Some v →
  apply_within_trees (memory_access AccessRead σ.(scs) tg (l.2, sz)) l.1 σ.(strs) = Some trs' →
  let σ' := mkState σ.(shp) trs' σ.(scs) σ.(snp) σ.(snc) in
  base_step P (Copy (Place l tg sz)) σ (Val v) σ' [].
Proof.
  intros TC RM Happly. destruct l. destruct sz.
  - simpl. econstructor. 1: by econstructor. assert (trs' = σ.(strs)) as ->.
    2: by eapply ZeroCopyIS.
    eapply apply_within_trees_unchanged in Happly; first done.
    intros tr Htr. simpl in Htr|-*. eapply (zero_sized_memory_access_unchanged false).
  - do 2 econstructor. all: eauto.
Qed.

Lemma write_base_step' P (σ: state) l bor sz v trs'
  (LEN: length v = sz)
  (BLK: ∀ n, (n < sz)%nat → l +ₗ n ∈ dom σ.(shp)) 
  (INTREE: trees_contain bor σ.(strs) l.1)
  (APPLY: apply_within_trees (memory_access AccessWrite (scs σ) bor (l.2, sz)) l.1 σ.(strs) = Some trs') :
  let σ' := mkState (write_mem l v σ.(shp)) trs' σ.(scs) σ.(snp) σ.(snc) in
  base_step P (Write (Place l bor sz) (Val v)) σ #[☠] σ' [].
Proof.
  intros σ'. destruct l. destruct sz.
  - destruct v; last done. econstructor; first econstructor. 1-2: done.
    assert (trs' = σ.(strs)) as ->. 2: by econstructor.
    eapply apply_within_trees_unchanged. 2: eassumption.
    intros tr Htr. eapply (zero_sized_memory_access_unchanged false).
  - econstructor 2; econstructor; eauto. by rewrite LEN.
Qed.

Lemma call_base_step P σ name e r fn :
  P !! name = Some fn →
  to_result e = Some r →
  base_step P (Call #[ScFnPtr name] e) σ (apply_func fn r) σ [].
Proof. by econstructor; econstructor. Qed.


Lemma init_call_base_step P σ :
  let c := σ.(snc) in
  let σ' := mkState σ.(shp) σ.(strs) ({[σ.(snc)]} ∪ σ.(scs)) σ.(snp) (S σ.(snc)) in
  base_step P InitCall σ (#[ScCallId (σ.(snc))]) σ' [].
Proof. by econstructor; econstructor. Qed.

Lemma end_call_base_step P (σ: state) trs' c :
  c ∈ σ.(scs) →
  trees_access_all_protected_initialized (scs σ) c (strs σ) = Some trs' →
  let σ' := mkState σ.(shp) trs' (σ.(scs) ∖ {[c]}) σ.(snp) σ.(snc) in
  base_step P (EndCall #[ScCallId c]) σ #[☠] σ' [].
Proof. intros ??. by econstructor; econstructor. Qed.

