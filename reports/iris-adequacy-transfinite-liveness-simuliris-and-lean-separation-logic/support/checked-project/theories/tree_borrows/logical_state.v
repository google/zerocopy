(** This file provides the basic heap and ghost state support for the BorIngLang program logic. *)
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
From simuliris.tree_borrows Require Import trees_equal.trees_equal_base.

Inductive access_ensuring := Strongly | WeaklyNoChildren.
Inductive logical_protector := Deallocable | EnsuringAccess (ae : access_ensuring).

(** * BorLang ghost state *)
Class bor_stateGS Σ := BorStateGS {
  (* Maintaining the locations protected by each call id *)
  (* For the final bool, true -> strong protector (also deref'able), weak -> only noalias *)
  call_inG :: ghost_mapG Σ call_id (gmap tag (gmap loc logical_protector));
  call_name : gname;

  (* tag ownership *)
  (* Last param is unit, should probably be cleaned up *)
  tag_inG :: tkmapG Σ tag unit;
  tag_name : gname;

  (* A view of parts of the heap, conditional on the tag *)
  (* the location (block * Z) is split into different parts,
     since we usually need to talk about sequences of bytes in a block *)
  heap_view_inG :: ghost_mapG Σ (tag * block) (gmap Z scalar);
  heap_view_source_name : gname;
  heap_view_target_name : gname;

  (* Public call IDs *)
  pub_call_inG :: ghost_mapG Σ call_id unit;
  pub_call_name : gname;

  (* Tainted tags: a set of tag * source location, remembering tags which are impossible to read *)
  tainted_tag_collection :: ghost_mapG Σ (tag * loc) unit;
  tainted_tags_name : gname; 
}.

Class bor_stateGpreS Σ := {
  (* Maintaining the locations protected by each call id *)
  call_pre_inG :: ghost_mapG Σ call_id (gmap tag (gmap loc logical_protector));

  (* tag ownership *)
  tag_pre_inG :: tkmapG Σ tag unit;

  (* A view of parts of the heap, conditional on the tag *)
  heap_view_pre_inG :: ghost_mapG Σ (tag * block) (gmap Z scalar);

  (* Public call IDs *)
  pub_call_pre_inG :: ghost_mapG Σ call_id unit;

  (* Tainted tags: a set of tag * source location *)
  tainted_tag_pre_collection :: ghost_mapG Σ (tag * loc) unit;
}.

Definition bor_stateΣ : gFunctors := (#[ghost_mapΣ call_id (gmap tag (gmap loc logical_protector)); 
        ghost_mapΣ (tag * block) (gmap Z scalar); ghost_mapΣ call_id unit; ghost_mapΣ (tag * loc) unit; 
        tkmapΣ tag unit]).

Global Instance subG_bor_stateΣ Σ :
  subG bor_stateΣ Σ → bor_stateGpreS Σ.
Proof. solve_inG. Qed.


Definition heaplet_lookup (M : gmap (tag * block) (gmap Z scalar)) (k : tag * loc) :=
  r ← M !! (k.1, k.2.1); r !! k.2.2.
Definition heaplet_insert (M : gmap (tag * block) (gmap Z scalar)) (k : tag * loc) vn :=
  let r := default ∅ (M !! (k.1, k.2.1)) in
  <[ (k.1, k.2.1) := <[ k.2.2 := vn ]> r ]> M.

Lemma heaplet_lookup_insert M k v :
  heaplet_lookup (heaplet_insert M k v) k = Some v.
Proof.
  rewrite /heaplet_lookup /heaplet_insert.
  destruct (M !! (k.1, k.2.1)) as [lv|] eqn:Heq.
  all: rewrite /= lookup_insert_eq /= lookup_insert_eq //.
Qed.

Lemma heaplet_lookup_insert_ne M k1 k2 v :
  k1 ≠ k2 →
  heaplet_lookup (heaplet_insert M k1 v) k2 = heaplet_lookup M k2.
Proof.
  intros Hne.
  rewrite /heaplet_lookup /heaplet_insert.
  destruct (decide ((k1.1, k1.2.1) = (k2.1, k2.2.1))) as [Hk1eq|Hk1ne].
  - rewrite -Hk1eq /= lookup_insert_eq /= lookup_insert_ne //.
      1: by destruct (M !! (k1.1, k1.2.1)).
      by destruct k1 as [?[??]], k2 as [?[??]]; simpl in *; congruence.
  - rewrite /= lookup_insert_ne //.
Qed.

Lemma heaplet_lookup_raw_insert_ne (k1 k2 : tag * loc) M k v :
  (k1.1, k1.2.1) ≠ (k2.1, k2.2.1) →
  k = (k1.1, k1.2.1) →
  heaplet_lookup (<[ k := v ]> M) k2 = heaplet_lookup M k2.
Proof.
  intros Hne ->.
  rewrite /heaplet_lookup lookup_insert_ne //.
Qed.

Section logical_protectors.

  Implicit Type lp : logical_protector.

  Definition log_prot_le lp1 lp2 :=
    match lp1, lp2 with
      Deallocable, _ => True
    | _, Deallocable => False
    | _, EnsuringAccess Strongly => True
    | EnsuringAccess Strongly , _ => False
    | EnsuringAccess WeaklyNoChildren, EnsuringAccess WeaklyNoChildren => True end.

  Lemma log_prot_le_refl lp : log_prot_le lp lp.
  Proof. by destruct lp as [|[]]. Qed.
  Lemma log_prot_le_antisym lp1 lp2 : log_prot_le lp1 lp2 → log_prot_le lp2 lp1 → lp1 = lp2.
  Proof. by destruct lp1 as [|[]], lp2 as [|[]]. Qed.
  Lemma log_prot_le_trans lp1 lp2 lp3 : log_prot_le lp1 lp2 → log_prot_le lp2 lp3 → log_prot_le lp1 lp3.
  Proof. by destruct lp1 as [|[]], lp2 as [|[]], lp3 as [|[]]. Qed.

End logical_protectors.


Section state_bijection.
  Context `{bor_stateGS Σ}.

  Context (sc_rel : scalar → scalar → iProp Σ).

  Section defs.
    (* We need all the maps from the tag interpretation here....
     TODO: can we make that more beautiful? all the different invariants are interleaved in subtle ways, which makes modular reasoning really hard... *)
    Context (M_tag : gmap tag (tag_kind * unit)) (M_t M_s : gmap (tag * block) (gmap Z scalar)) (Mcall_t : gmap call_id (gmap tag (gmap loc logical_protector))).


    Definition call_set_in (M : gmap tag (gmap loc logical_protector)) t l (ls:logical_protector) :=
      ∃ L, M !! t = Some L ∧ L !! l = Some ls.
    Definition call_set_in' (M : gmap call_id (gmap tag (gmap loc logical_protector))) c t l ls :=
      ∃ M', M !! c = Some M' ∧ call_set_in M' t l ls.
    Definition pub_loc σ_t σ_s (l : loc) : iProp Σ :=
      ∀ sc_t, ⌜σ_t.(shp) !! l = Some sc_t⌝ → ∃ sc_s, ⌜σ_s.(shp) !! l = Some sc_s⌝ ∗ sc_rel sc_t sc_s.
    Definition priv_loc t (l : loc) : Prop :=
      ∃ tk, M_tag !! t = Some (tk, tt) ∧ is_Some (heaplet_lookup M_t (t, l)) ∧
        (* local *)
        (tk = tk_local ∨
        (* unique active with any protector *)
        (∃ c ae, tk = tk_unq tk_act ∧ call_set_in' Mcall_t c t l (EnsuringAccess ae))).
    (* This definition enforces quite strict requirements on the state:
      - the domains of the heaps shp are the same: dom σ_s.(shp) = dom σ_t.(shp)
      - the trees are the same, up to conflicted: trees_equal σ_s.(scs) σ_s.(strs) σ_t.(strs)
      - the tag counter is the same: σ_s.(snp) = σ_t.(snp)
      - the call counter is the same: σ_s.(snc) = σ_t.(snc)
      - the set of ongoing calls is the same: σ_s.(scs) = σ_t.(scs)
        + thus it does not matter which call set we use for conflicted
      - there's a relation on the scalars stored at locations ([pub_loc]), except when the location is currently controlled by a tag ([priv_loc]).

      Note that, while the definition may appear asymmetric in source and target, due to the well-formedness on 
      states [state_wf] and the relation of the tag maps enforced below, it really is symmetric in practice.
    *)
    Definition state_rel σ_t σ_s : iProp Σ :=
        ⌜dom σ_s.(shp) = dom σ_t.(shp)⌝ ∗
        ⌜trees_equal σ_s.(scs) Forwards σ_s.(strs) σ_t.(strs)⌝ ∗
        ⌜σ_s.(snp) = σ_t.(snp)⌝ ∗
        ⌜σ_s.(snc) = σ_t.(snc)⌝ ∗
        ⌜σ_s.(scs) = σ_t.(scs)⌝ ∗
        (* private / public locations of the target *)
        ∀ l, ⌜is_Some (σ_t.(shp) !! l)⌝ → pub_loc σ_t σ_s l ∨ ⌜∃ t, priv_loc t l⌝.

    Global Instance state_rel_persistent σ_t σ_s `{∀ sc_t sc_s, Persistent (sc_rel sc_t sc_s)} :
      Persistent (state_rel σ_t σ_s).
    Proof. intros. apply _. Qed.
  End defs.
End state_bijection.

Section bijection_lemmas.
  Context `{bor_stateGS Σ}.
  Context (sc_rel : scalar → scalar → iProp Σ).
  Local Notation state_rel := (state_rel sc_rel).

  Lemma state_rel_get_pure Mtag Mt Mcall σ_t σ_s :
    state_rel Mtag Mt Mcall σ_t σ_s -∗ ⌜trees_equal σ_s.(scs) Forwards σ_s.(strs) σ_t.(strs) ∧
      σ_s.(snp) = σ_t.(snp) ∧ σ_s.(snc) = σ_t.(snc) ∧ σ_s.(scs) = σ_t.(scs)⌝.
  Proof. iIntros "(% & % & % & % & % & ?)". eauto. Qed.
  Lemma state_rel_trees_eq Mtag Mt Mcall σ_t σ_s :
    state_rel Mtag Mt Mcall σ_t σ_s -∗ ⌜trees_equal σ_s.(scs) Forwards σ_s.(strs) σ_t.(strs)⌝.
  Proof. iIntros "(% & % & % & % & % & ?)". eauto. Qed.
  Lemma state_rel_trees_eq_2 Mtag Mt Mcall σ_t σ_s :
    state_rel Mtag Mt Mcall σ_t σ_s -∗ ⌜trees_equal σ_t.(scs) Forwards σ_s.(strs) σ_t.(strs)⌝.
  Proof. iIntros "(% & % & % & % & <- & ?)". eauto. Qed.
  Lemma state_rel_snp_eq Mtag Mt Mcall σ_t σ_s :
    state_rel Mtag Mt Mcall σ_t σ_s -∗ ⌜σ_s.(snp) = σ_t.(snp)⌝.
  Proof. iIntros "(% & % & % & % & % & ?)". eauto. Qed.
  Lemma state_rel_snc_eq Mtag Mt Mcall σ_t σ_s :
    state_rel Mtag Mt Mcall σ_t σ_s -∗ ⌜σ_s.(snc) = σ_t.(snc)⌝.
  Proof. iIntros "(% & % & % & % & % & ?)". eauto. Qed.
  Lemma state_rel_calls_eq Mtag Mt Mcall σ_t σ_s :
    state_rel Mtag Mt Mcall σ_t σ_s -∗ ⌜σ_s.(scs) = σ_t.(scs)⌝.
  Proof. iIntros "(% & % & % & % & % & ?)". eauto. Qed.
  Lemma state_rel_dom_eq Mtag Mt Mcall σ_t σ_s :
    state_rel Mtag Mt Mcall σ_t σ_s -∗ ⌜dom σ_t.(shp) = dom σ_s.(shp)⌝.
  Proof. iIntros "(% & % & % & % & % & ?)". eauto. Qed.

  Lemma state_rel_upd_pub_both M_tag M_t Mcall_t σ_t σ_s l sc_t sc_s :
    sc_rel sc_t sc_s -∗
    state_rel M_tag M_t Mcall_t σ_t σ_s -∗
    state_rel M_tag M_t Mcall_t (state_upd_mem (<[l := sc_t]>) σ_t) (state_upd_mem (<[l := sc_s]>) σ_s).
  Proof.
    iIntros "Hs (%Hshp & % & % & % & % & Hrel)". rewrite /state_rel /=.
    iSplitR. { iPureIntro. by rewrite !dom_insert_L Hshp. }
    do 4 (iSplitR; first done).
    iIntros (l') "%Hsome". destruct (decide (l = l')) as [<- | Hneq].
    - iLeft. iIntros (sc_t') "%Hsc_t'". iExists sc_s.
      iSplitR. { iPureIntro. by rewrite lookup_insert_eq. }
      move :Hsc_t'; rewrite lookup_insert_eq => [= <-] //.
    - rewrite lookup_insert_ne in Hsome; last done.
      iDestruct ("Hrel" $! l' with "[//]") as "[Hpub | Hpriv]".
      + iLeft. iIntros (sc_t'). rewrite !lookup_insert_ne; [ | done | done]. iApply "Hpub".
      + iRight. done.
  Qed.

  Lemma priv_loc_upd_insert Mtag Mt Mcall t l t' l' sc :
    priv_loc Mtag Mt Mcall t l →
    priv_loc Mtag (heaplet_insert Mt (t',l') sc) Mcall t l.
  Proof.
    rewrite /priv_loc. intros (tk & Ht & (h & Hs) & Hinv). exists tk.
    split_and!; [ done | | done].
    destruct (decide ((t', l') = (t, l))) as [->|].
    - by rewrite heaplet_lookup_insert.
    - rewrite heaplet_lookup_insert_ne //.
  Qed.

  Lemma state_rel_upd_priv_target M_tag M_t Mcall σ_t σ_s l t sc :
    is_Some (σ_t.(shp) !! l) →
    priv_loc M_tag M_t Mcall t l →
    state_rel M_tag M_t Mcall σ_t σ_s -∗
    state_rel M_tag (heaplet_insert M_t (t, l) sc) Mcall (state_upd_mem (<[l := sc]>) σ_t) σ_s.
  Proof.
    iIntros (Hs Hpriv) "(%Hshp & % & % & % & % & Hrel)". rewrite /state_rel /=.
    iSplitR. { iPureIntro. rewrite dom_insert_lookup_L; done. }
    do 4 (iSplitR; first done).
    iIntros (l') "%Hsome". destruct (decide (l = l')) as [<- | Hneq].
    - iRight. iExists t. iPureIntro. apply priv_loc_upd_insert. done.
    - rewrite lookup_insert_ne in Hsome; last done.
      iDestruct ("Hrel" $! l' with "[//]") as "[Hpub | %Hpriv']".
      + iLeft. iIntros (sc_t'). rewrite !lookup_insert_ne; [ | done ]. iApply "Hpub".
      + iRight. iPureIntro. destruct Hpriv' as (t' & Hpriv'). exists t'.
        by eapply priv_loc_upd_insert.
  Qed.

  Lemma state_rel_upd_priv_source M_tag M_t Mcall σ_t σ_s l t sc :
    is_Some (σ_t.(shp) !! l) →
    priv_loc M_tag M_t Mcall t l →
    state_rel M_tag M_t Mcall σ_t σ_s -∗
    state_rel M_tag M_t Mcall σ_t (state_upd_mem (<[l := sc]>) σ_s).
  Proof.
    iIntros (Hs Hpriv) "(%Hshp & % & % & % & % & Hrel)". rewrite /state_rel /=.
    iSplitR. { iPureIntro. rewrite dom_insert_lookup_L; [ by rewrite Hshp| ].
      rewrite lookup_lookup_total_dom; first by eauto.
      rewrite Hshp. by apply elem_of_dom.
    }
    do 4 (iSplitR; first done).
    iIntros (l') "%Hsome". destruct (decide (l = l')) as [<- | Hneq].
    - iRight. iExists t. done.
    - iDestruct ("Hrel" $! l' with "[//]") as "[Hpub | %Hpriv']".
      + iLeft. iIntros (sc_t'). rewrite !lookup_insert_ne; [ | done ]. iApply "Hpub".
      + iRight. iPureIntro. destruct Hpriv' as (t' & Hpriv'). exists t'. done.
  Qed.

  Lemma state_rel_pub_if_not_priv M_tag M_t Mcall σ_t σ_s l :
    ⌜is_Some (σ_t.(shp) !! l)⌝ -∗
    state_rel M_tag M_t Mcall σ_t σ_s -∗
    ⌜∀ t, ¬ priv_loc M_tag M_t Mcall t l⌝ -∗
    pub_loc sc_rel σ_t σ_s l.
  Proof.
    iIntros (Hs) "(%& % & % & % & % & Hrel) %Hnpriv".
    iPoseProof ("Hrel" $! l with "[//]") as "[Hpub | %Hpriv]"; first done.
    destruct Hpriv as (t & Hpriv). exfalso; by eapply Hnpriv.
  Qed.

  Lemma state_rel_heap_lookup_Some M_tag M_t Mcall σ_t σ_s :
    state_rel M_tag M_t Mcall σ_t σ_s -∗
    ∀ l, ⌜is_Some (σ_t.(shp) !! l)⌝ ↔ ⌜is_Some (σ_s.(shp) !! l)⌝.
  Proof.
    iIntros "(%Hshp & _)". iPureIntro. move => l. cbn. by rewrite -!elem_of_dom Hshp.
  Qed.

  Lemma state_rel_pub_or_priv M_tag M_t Mcall σ_t σ_s l :
    ⌜is_Some (σ_t.(shp) !! l)⌝ -∗
    state_rel M_tag M_t Mcall σ_t σ_s -∗
    pub_loc sc_rel σ_t σ_s l ∨ ⌜∃ t, priv_loc M_tag M_t Mcall t l⌝.
  Proof.
    iIntros "Hsome Hstate". iDestruct "Hstate" as "(_ & _ & _ & _ & _ & Hl)".
    by iApply "Hl".
  Qed.

  Lemma pub_loc_lookup σ_t σ_s l :
    ⌜is_Some (σ_t.(shp) !! l)⌝ -∗
    pub_loc sc_rel σ_t σ_s l -∗
    ∃ sc_t sc_s, ⌜σ_t.(shp) !! l = Some sc_t ∧ σ_s.(shp) !! l = Some sc_s⌝ ∗ sc_rel sc_t sc_s.
  Proof.
    iIntros (Hs) "Hpub". destruct Hs as (sc_t & Ht).
    iDestruct ("Hpub" $! sc_t with "[//]") as (sc_s) "[%Hs Hsc]".
    iExists sc_t, sc_s. eauto.
  Qed.

End bijection_lemmas.

(** Interpretation for call ids *)
Section call_defs.
  Context {Σ} (call_gname : gname) {call_inG : ghost_mapG Σ (call_id) (gmap tag (gmap loc logical_protector))}.
  Context (no_children_pred_on : tag → loc → Prop).

  Implicit Types (c : call_id) (pid : tag) (pm : permission).

  Definition call_set_is (c : call_id) (M : gmap tag (gmap loc logical_protector)) :=
    ghost_map_elem call_gname c (DfracOwn 1) M.

  Definition protector_matches_strength (ps: logical_protector) (oprot: option protector) :=
    match ps, oprot with
      EnsuringAccess Strongly, Some prot => prot.(strong) = ProtStrong
    | _, Some prot => prot.(strong) = ProtWeak
    | _, None => False end.

  Definition item_protected_for c it blk off (ps:logical_protector) :=
          protector_is_for_call c it.(iprot)
        ∧ protector_matches_strength ps it.(iprot)
        ∧ (ps = EnsuringAccess WeaklyNoChildren → no_children_pred_on it.(itag) (blk, off))
          (* we must be initialized, otherwise deallocation could continue *)
        ∧ (item_lookup it off).(initialized) = PermInit
          (* we can never be disabled, as we are protected *)
        ∧ (item_lookup it off).(perm) ≠ Disabled
          (* we must not be cell, because protected Cell makes no sense and provides no guarantees *)
        ∧ (item_lookup it off).(perm) ≠ Cell.

  Definition tag_protected_for c trs l t ps := match ps with
      EnsuringAccess ae => ∃ it, trees_lookup trs l.1 t it ∧ item_protected_for c it l.1 l.2 ps
    | Deallocable   => ∀ it, trees_lookup trs l.1 t it → item_protected_for c it l.1 l.2 ps end.


  (* This does not assert ownership of the authoritative part. Instead, this is owned by bor_interp below. *)
  Definition call_set_interp (M : gmap call_id (gmap tag (gmap loc logical_protector))) (σ : state) : Prop :=
    (∀ c (M' : gmap tag (gmap loc logical_protector)), M !! c = Some M' →
      c ∈ σ.(scs) ∧
      (* for every tag *)
      ∀ t (L : gmap loc logical_protector), M' !! t = Some L →
        tag_valid σ.(snp) t ∧
        ∀ (l : loc) ps, L !! l = Some ps → tag_protected_for c σ.(strs) l t ps) ∧
    (∀ c1 M1 c2 M2 t, M !! c1 = Some M1 → M !! c2 = Some M2 → t ∈ dom M1 → t ∈ dom M2 → c1 = c2).

  Definition loc_protected_by σ t l c ps :=
    c ∈ σ.(scs) ∧ tag_valid σ.(snp) t ∧ tag_protected_for c σ.(strs) l t ps.

  Lemma call_set_interp_access M σ c t l ps :
    call_set_interp M σ →
    call_set_in' M c t l ps →
    loc_protected_by σ t l c ps.
  Proof.
    intros (Hinterp&_) (M' & HM_some & L & HM'_some & Hin).
    specialize (Hinterp _ _ HM_some) as (? & Hinterp).
    specialize (Hinterp _ _ HM'_some) as (? & Hinterp).
    specialize (Hinterp _ _ Hin). done.
  Qed.
End call_defs.

Notation "c '@@' M" := (call_set_is call_name c M) (at level 50).

(** Interpretation for heap assertions under control of tags.
    The interpretation of the tag map and the "heap view" fragments are interlinked.
 *)
Section heap_defs.
  (*
  Context (Mcall : gmap call_id (gmap tag (gmap loc logical_protector))).

  Definition prot_in_call_set op t l := ∃ ps pp, op = Some pp ∧ call_set_in' Mcall pp.(call) t l ps ∧ (pp.(strong) = ProtStrong → ps = EnsuringAccess Strongly). *)

  (** The assumption on the location still being valid for tag [t], i.e., [t] not being disabled. *)
  (* Note: That the stack is still there needs to be part of the precondition [bor_state_pre].
    Otherwise, we will not be able to prove reflexivity for deallocation:
      that needs to be able to remove stacks from the state without updating all the ghost state that may still make assumptions about it.
  *)



  Definition bor_state_pre_unq (l : loc) (t : tag) (σ : state) :=
      ∃ it, trees_lookup σ.(strs) l.1 t it
       ∧ ((item_lookup it l.2).(initialized) = PermInit → (item_lookup it l.2).(perm) ≠ Disabled).

  Definition bor_state_pre (l : loc) (t : tag) (tk : tag_kind) (σ : state) :=
    match tk with
    | tk_local => True
    | _        => ∃ it, trees_lookup σ.(strs) l.1 t it
                   ∧ ((item_lookup it l.2).(initialized) = PermInit → (item_lookup it l.2).(perm) ≠ Disabled)
    end.

  (* FIXME: Refactor potential: merge the two tk_unq *)
  Lemma bor_state_pre_unq_or l t tk σ : (tk = tk_unq tk_act ∨ tk = tk_unq tk_res) →
    bor_state_pre l t tk σ = bor_state_pre_unq l t σ.
  Proof. intros [-> | ->]; done. Qed.


  Definition bor_state_post_unq (l : loc) (t : tag) (σ : state) it tr tkk:=
      let P := ((item_lookup it l.2).(perm) = Frozen → protector_is_active it.(iprot) σ.(scs)) in
      ( P →
        match (item_lookup it l.2).(perm) with
             | Active => tkk = tk_act
             | Reserved _ => tkk = tk_res
               (* ReservedIM is not allowed *)
             | _ => False end) ∧
        ∀ it' t', tree_lookup tr t' it' -> match rel_dec tr t' t with 
            (* all immediate children of t must be disabled *)
          | Child (Strict Immediate) => (item_lookup it' l.2).(perm) = Disabled
          | Child _ => True
            (* Parents must not be disabled. If This is active, then we can also conclude the parents are active by state_wf. *)
          | Foreign (Parent _) => (item_lookup it' l.2).(perm) ≠ Disabled
          | Foreign Cousin => let lp := item_lookup it' l.2 in lp.(initialized) = PermLazy ∨ match lp.(perm) with
                     (* If active, the others are either uninitialized, or Cell, or Disabled, or Reserved IM (i.e. surive foreign writes and don't cause UB) *)
                     (* Otherwise, the others must not be initialized active (i.e. survive foreign reads) *)
                     Active => False | Cell | Disabled | ReservedIM => True | _ => tkk = tk_res ∨ ¬ P end end.

  Definition bor_state_own_on (l : loc) (t : tag) (tk : tag_kind) (σ : state) it tr :=
    (item_lookup it l.2).(initialized) = PermInit ∧
    match tk with
    | tk_local => (item_lookup it l.2).(perm) = Active ∧
            it.(iprot) = None ∧ (* it is not protected *)
            (* The item is the only one in the tree *)
            ∀ it' t', tree_lookup tr t' it' -> t = t'
    | tk_unq tkk
       => bor_state_post_unq l t σ it tr tkk
    | tk_pub
       => (item_lookup it l.2).(perm) = Frozen ∧
          ∀ it' t', tree_lookup tr t' it' -> match rel_dec tr t' t with 
            | Child This => True
               (* it' is a child of it *)
            | Child (Strict _) => (item_lookup it' l.2).(perm) ≠ Active
            | Foreign (Parent _) => (item_lookup it' l.2).(perm) ≠ Disabled
            | Foreign Cousin => (item_lookup it' l.2).(perm) ≠ Active end
    end.

  Definition bor_state_own (l : loc) (t : tag) (tk : tag_kind) (σ : state) :=
    ∃ it tr, tree_lookup tr t it ∧ σ.(strs) !! l.1 = Some tr ∧ bor_state_own_on l t tk σ it tr.

  Lemma bor_state_own_some_tree l t tk σ :
    bor_state_own l t tk σ → ∃ tr, σ.(strs) !! l.1 = Some tr.
  Proof. rewrite /bor_state_own. naive_solver. Qed.

  (** Location [l] is controlled by tag [t] at kind [tk] with scalar [sc]. *)
  Definition loc_controlled (l : loc) (t : tag) (tk : tag_kind) (sc : scalar) (σ : state) :=
    (bor_state_pre l t tk σ → bor_state_own l t tk σ ∧ σ.(shp) !! l = Some sc).

  Lemma loc_controlled_mem_insert_ne l l' t tk sc sc' σ :
    l ≠ l' →
    loc_controlled l t tk sc σ →
    loc_controlled l t tk sc (state_upd_mem <[l' := sc']> σ).
  Proof.
    intros Hneq Him Hpre.
    apply Him in Hpre as [Hown Hmem]. split; first done.
    rewrite lookup_insert_ne; done.
  Qed.
  Lemma loc_controlled_mem_insert l t tk sc sc' σ :
    loc_controlled l t tk sc σ →
    loc_controlled l t tk sc' (state_upd_mem <[l := sc']> σ).
  Proof.
    intros Him Hpre. apply Him in Hpre as [Hown Hmem]. split; first done.
    rewrite lookup_insert_eq; done.
  Qed.

  (** Domain agreement for the two heap views for source and target *)
  Definition dom_agree_on_tag (M_t M_s : gmap (tag * block) (gmap Z scalar)) (t : tag) :=
    (∀ l, is_Some (heaplet_lookup M_t (t, l)) → is_Some (heaplet_lookup M_s (t, l))) ∧
    (∀ l, is_Some (heaplet_lookup M_s (t, l)) → is_Some (heaplet_lookup M_t (t, l))).


  Lemma dom_agree_on_tag_update_same M_t M_s t blk nm1 nm2 :
    dom_agree_on_tag M_t M_s t →
    dom nm1 = dom nm2 →
    dom_agree_on_tag (<[ (t, blk) := nm1 ]> M_t) (<[ (t, blk) := nm2 ]> M_s) t.
  Proof.
    intros [H1a H1b] Hdom. split; intros l (x&(x1&H1&H2)%bind_Some);
     (destruct (decide (l.1 = blk)) as [<-|Hne];
      first (rewrite /= lookup_insert_eq in H1; injection H1 as H1)).
    1: rewrite /heaplet_lookup lookup_insert_eq /= -elem_of_dom -Hdom elem_of_dom H1 H2 //.
    2: rewrite /heaplet_lookup lookup_insert_eq /= -elem_of_dom Hdom elem_of_dom H1 H2 //.
    all: rewrite /heaplet_lookup /= !lookup_insert_ne // in H1|-*; try congruence.
    1: eapply H1a. 2: eapply H1b.
    all: rewrite /heaplet_lookup /= H1 /= H2 //.
  Qed.

  Lemma dom_agree_on_tag_update_same_delete M_t M_s t blk :
    dom_agree_on_tag M_t M_s t →
    dom_agree_on_tag (delete (t, blk) M_t) (delete (t, blk) M_s) t.
  Proof.
    intros [H1a H1b]. split; intros l (x&(x1&H1&H2)%bind_Some);
     (destruct (decide (l.1 = blk)) as [<-|Hne];
      first (rewrite /= lookup_delete_eq /= in H1; try done)).
    all: simpl in H1.
    all: rewrite /heaplet_lookup /= !lookup_delete_ne // in H1|-*; try congruence.
    1: eapply H1a. 2: eapply H1b.
    all: rewrite /heaplet_lookup /= H1 /= H2 //.
  Qed.

  Lemma dom_agree_on_tag_upd_ne M_t M_s t t' blk nm1 nm2 :
    t ≠ t' →
    dom_agree_on_tag M_t M_s t' →
    dom_agree_on_tag (<[(t, blk) := nm1]> M_t) (<[(t, blk) := nm2]> M_s) t'.
  Proof.
    intros Hneq [H1a H1b]. split; intros l (x&(x1&H1&H2)%bind_Some).
    all: rewrite lookup_insert_ne /= in H1; simpl; try congruence.
    all: rewrite /heaplet_lookup /= lookup_insert_ne //; try congruence.
    1: apply H1a. 2: apply H1b.
    all: rewrite /heaplet_lookup /= H1 /= H2 //.
  Qed.

  Lemma dom_agree_on_tag_upd_ne_delete M_t M_s t t' blk :
    t ≠ t' →
    dom_agree_on_tag M_t M_s t' →
    dom_agree_on_tag (delete (t, blk) M_t) (delete (t, blk) M_s) t'.
  Proof.
    intros Hneq [H1a H1b]. split; intros l (x&(x1&H1&H2)%bind_Some).
    all: rewrite lookup_delete_ne /= in H1; simpl; try congruence.
    all: rewrite /heaplet_lookup /= lookup_delete_ne //; try congruence.
    1: apply H1a. 2: apply H1b.
    all: rewrite /heaplet_lookup /= H1 /= H2 //.
  Qed.

  Lemma dom_agree_on_tag_upd_delete M_t M_s t t' blk :
    dom_agree_on_tag M_t M_s t' →
    dom_agree_on_tag (delete (t, blk) M_t) (delete (t, blk) M_s) t'.
  Proof.
    destruct (decide (t = t')).
    - subst t. by eapply dom_agree_on_tag_update_same_delete.
    - by eapply dom_agree_on_tag_upd_ne_delete.
  Qed.

  Lemma dom_agree_on_tag_not_elem M_t M_s t :
    (∀ l, heaplet_lookup M_t (t, l) = None) → (∀ l, heaplet_lookup M_s (t, l) = None) →
    dom_agree_on_tag M_t M_s t.
  Proof.
    intros Ht Hs. split.
    all: intros l (x&H1); by rewrite ?Ht ?Hs in H1.
  Qed.

  Lemma dom_agree_on_tag_target_insert_same_dom M_s M_t t blk t' M_old M_new :
    M_t !! (t, blk) = Some M_old →
    dom M_old = dom M_new →
    dom_agree_on_tag M_t M_s t' →
    dom_agree_on_tag (<[ (t, blk) := M_new ]> M_t) M_s t'.
  Proof.
    intros H1 H2 (H3l&H3r); split; intros l [x Hx].
    - eapply bind_Some in Hx as (Mo&[([= -> ->]&<-)|(Hne&HMo)]%lookup_insert_Some&HH); simpl in *.
      + eapply H3l. rewrite /heaplet_lookup H1 /=. eapply elem_of_dom. rewrite H2. by eapply elem_of_dom_2.
      + eapply H3l. rewrite /heaplet_lookup HMo /= HH //.
    - rewrite /heaplet_lookup /=. destruct (decide ((t, blk) = (t', l.1))) as [[= -> ->]|Hne].
      + rewrite lookup_insert_eq /=. eapply elem_of_dom. rewrite -H2.
        eapply mk_is_Some, H3r in Hx. rewrite /heaplet_lookup /= H1 /= in Hx. by eapply elem_of_dom.
      + rewrite lookup_insert_ne //. by eapply H3r.
  Qed.

  Lemma dom_agree_on_tag_source_insert_same_dom M_s M_t t blk t' M_old M_new :
    M_s !! (t, blk) = Some M_old →
    dom M_old = dom M_new →
    dom_agree_on_tag M_t M_s t' →
    dom_agree_on_tag M_t (<[ (t, blk) := M_new ]> M_s) t'.
  Proof.
    intros H1 H2 (H3l&H3r); split; intros l [x Hx].
    - rewrite /heaplet_lookup /=. destruct (decide ((t, blk) = (t', l.1))) as [[= -> ->]|Hne].
      + rewrite lookup_insert_eq /=. eapply elem_of_dom. rewrite -H2.
        eapply mk_is_Some, H3l in Hx. rewrite /heaplet_lookup /= H1 /= in Hx. by eapply elem_of_dom.
      + rewrite lookup_insert_ne //. by eapply H3l.
    - eapply bind_Some in Hx as (Mo&[([= -> ->]&<-)|(Hne&HMo)]%lookup_insert_Some&HH); simpl in *.
      + eapply H3r. rewrite /heaplet_lookup H1 /=. eapply elem_of_dom. rewrite H2. by eapply elem_of_dom_2.
      + eapply H3r. rewrite /heaplet_lookup HMo /= HH //.
  Qed.

  Definition dom_unique_per_tag (M : gmap (tag * block) (gmap Z scalar)) : Prop :=
    ∀ tg l1 l2, (tg, l1) ∈ dom M → (tg, l2) ∈ dom M → l1 = l2.

  (** The main interpretation for tags *)
  Definition tag_interp (M : gmap tag (tag_kind * unit)) (M_t M_s : gmap (tag * block) (gmap Z scalar)) σ_t σ_s : Prop :=
    (∀ (t : tag) tk, M !! t = Some (tk, ()) →
      (* tags are valid *)
      tag_valid σ_t.(snp) t ∧ tag_valid σ_s.(snp) t ∧
      (tk = tk_local → (∀ blk M, M_t !! (t, blk) = Some M → M ≠ ∅) ∧ (∀ blk M, M_s !! (t, blk) = Some M → M ≠ ∅)) ∧
      (* at all locations, the values agree, and match the physical state assuming the tag currently has control over the location *)
      (∀ l sc_t, heaplet_lookup M_t (t, l) = Some sc_t → loc_controlled l t tk sc_t σ_t) ∧
      (∀ l sc_s, heaplet_lookup M_s (t, l) = Some sc_s → loc_controlled l t tk sc_s σ_s) ∧
      dom_agree_on_tag M_t M_s t) ∧
    (∀ (t : tag) blk, is_Some (M_t !! (t, blk)) → is_Some (M !! t)) ∧
    (∀ (t : tag) blk, is_Some (M_s !! (t, blk)) → is_Some (M !! t)) ∧
    dom_unique_per_tag M_t ∧ dom_unique_per_tag M_s.
End heap_defs.


Notation "p '$$' tk" := (tkmap_elem tag_name p tk ()) (at level 50).

Definition tk_to_frac (tk : tag_kind) :=
  match tk with
  | tk_pub => DfracDiscarded
  | _ => DfracOwn 1
  end.

Section public_call_ids.
  Context `{bor_stateGS Σ}.
  Implicit Types (c : call_id).

  Definition pub_cid (c : call_id) := ghost_map_elem pub_call_name c DfracDiscarded tt.
  Global Instance pub_cid_persistent c : Persistent (pub_cid c).
  Proof. apply _. Qed.

  Definition call_id_is_public σ_t σ_s c : iProp Σ :=
    (* dead call id, can never come alive *)
    ⌜c ∉ σ_t.(scs) ∧ c ∉ σ_s.(scs) ∧ (c < σ_t.(snc))%nat ∧ (c < σ_s.(snc))%nat⌝ ∨
    (* alive call id, empty call set *)
    c @@ ∅.

  Definition pub_cid_interp σ_t σ_s : iProp Σ :=
    ∃ (M : gmap call_id unit),
      ghost_map_auth_frac pub_call_name 1 M ∗
      (* calso containing the persistent element to make lemmas simpler *)
      [∗ map] c ↦ _ ∈ M, (call_id_is_public σ_t σ_s c ∗ pub_cid c).

  Lemma call_id_is_public_mono σ_t σ_s σ_t' σ_s' c :
    ((c ∉ σ_t.(scs) ∧ (c < σ_t.(snc))%nat → c ∉ σ_t'.(scs))) →
    ((c ∉ σ_s.(scs) ∧ (c < σ_s.(snc))%nat → c ∉ σ_s'.(scs))) →
    (σ_t.(snc) ≤ σ_t'.(snc))%nat →
    (σ_s.(snc) ≤ σ_s'.(snc))%nat →
    call_id_is_public σ_t σ_s c -∗
    call_id_is_public σ_t' σ_s' c.
  Proof.
    iIntros (Hpres_t Hpres_s Hle_t Hle_s) "Hpub".
    iDestruct "Hpub" as "[%Ha | Hown]"; last by iRight.
    iLeft. iPureIntro. destruct Ha as (Hn_t & Hn_s & ? & ?). split_and!.
    - apply Hpres_t. done.
    - apply Hpres_s. done.
    - lia.
    - lia.
  Qed.

  (* main update lemma to update the state interpretation *)
  Lemma pub_cid_interp_preserve σ_t σ_s σ_t' σ_s' :
    (∀ c, c ∈ σ_t'.(scs) → (σ_t.(snc) ≤ c)%nat ∨ c ∈ σ_t.(scs)) →
    (∀ c, c ∈ σ_s'.(scs) → (σ_s.(snc) ≤ c)%nat ∨ c ∈ σ_s.(scs)) →
    (σ_t.(snc) ≤ σ_t'.(snc))%nat →
    (σ_s.(snc) ≤ σ_s'.(snc))%nat →
    pub_cid_interp σ_t σ_s -∗
    pub_cid_interp σ_t' σ_s'.
  Proof.
    iIntros (Hpres_t Hpres_s ? ?) "(%M & Hauth & Hpub)". iExists M. iFrame "Hauth".
    iApply (big_sepM_mono with "Hpub"). iIntros (c [] Hlookup) "[Hpub $]".
    iApply call_id_is_public_mono; [ | | done..].
    - intros (Hn_t & ?). destruct (decide (c ∈ σ_t'.(scs))) as [Hin_t' | Hnotin_t'].
      + destruct (Hpres_t c ltac:(eauto)) as [ | ]; [lia | naive_solver].
      + naive_solver.
    - intros (Hn_s & ?). destruct (decide (c ∈ σ_s'.(scs))) as [Hin_s' | Hnotin_s'].
      + destruct (Hpres_s c ltac:(eauto)) as [ | ]; [lia | naive_solver].
      + naive_solver.
  Qed.

  (* update lemma that can be used except for initcall *)
  Lemma pub_cid_interp_preserve_sub σ_t σ_s σ_t' σ_s' :
    σ_t'.(scs) ⊆ σ_t.(scs) →
    σ_s'.(scs) ⊆ σ_s.(scs) →
    (σ_t.(snc) = σ_t'.(snc))%nat →
    (σ_s.(snc) = σ_s'.(snc))%nat →
    pub_cid_interp σ_t σ_s -∗
    pub_cid_interp σ_t' σ_s'.
  Proof.
    iIntros (Hsub_t Hsub_s ? ?). iApply pub_cid_interp_preserve; [ | | lia..].
    - intros c Hin_t'. right. set_solver.
    - intros c Hin_s'. right. set_solver.
  Qed.

  (* update lemma for initcall *)
  Lemma pub_cid_interp_preserve_initcall σ_t σ_s σ_t' σ_s' :
    σ_t'.(scs) ⊆ {[ σ_t.(snc) ]} ∪ σ_t.(scs) →
    σ_s'.(scs) ⊆ {[ σ_s.(snc) ]} ∪ σ_s.(scs) →
    (S σ_t.(snc) = σ_t'.(snc))%nat →
    (S σ_s.(snc) = σ_s'.(snc))%nat →
    pub_cid_interp σ_t σ_s -∗
    pub_cid_interp σ_t' σ_s'.
  Proof.
    iIntros (Hsub_t Hsub_s ? ?). iApply pub_cid_interp_preserve; [ | | lia..].
    - intros c Hin_t'. move : Hsub_t. rewrite elem_of_subseteq => Hsub_t.
      apply Hsub_t in Hin_t'. move : Hin_t'. rewrite elem_of_union elem_of_singleton.
      intros [-> | Hin]; [left; lia | by right].
    - intros c Hin_s'. move : Hsub_s. rewrite elem_of_subseteq => Hsub_s.
      apply Hsub_s in Hin_s'. move : Hin_s'. rewrite elem_of_union elem_of_singleton.
      intros [-> | Hin]; [left; lia | by right].
  Qed.

  (* the main lemma for ending calls *)
  Lemma pub_cid_endcall σ_s σ_t c :
    c ∈ σ_s.(scs) →
    (c < σ_s.(snc))%nat →
    (c < σ_t.(snc))%nat →
    pub_cid c -∗
    pub_cid_interp σ_t σ_s -∗
    c @@ ∅ ∗
    pub_cid_interp (mkState σ_t.(shp) σ_t.(strs) (σ_t.(scs) ∖ {[ c ]}) σ_t.(snp) σ_t.(snc))
      (mkState σ_s.(shp) σ_s.(strs) (σ_s.(scs) ∖ {[ c ]}) σ_s.(snp) σ_s.(snc)).
  Proof.
    iIntros (Hc_in Hlts Hltt) "#Hpublic (%M & Hauth & Hpub)".
    iPoseProof (ghost_map_lookup with "Hauth Hpublic") as "%Hlookup".
    rewrite (big_sepM_delete _ _ _ _ Hlookup). iDestruct "Hpub" as "[[Hc _] Hpubr]".
    iDestruct "Hc" as "[ %Hdead | Halive]".
    { (* contradictory *) exfalso. naive_solver. }
    iFrame "Halive". iExists M. iFrame "Hauth".
    rewrite -{2}(insert_delete_id M c ()); last done.
    rewrite big_sepM_insert; last apply lookup_delete_eq.
    iSplitR "Hpubr".
    - iFrame "Hpublic". iLeft. simpl. iPureIntro. split_and!; [set_solver.. | done ].
    - iApply (big_sepM_mono with "Hpubr").
      iIntros (c' []). rewrite lookup_delete_Some. iIntros ([Hneq Hsome]).
      iIntros "[Hpub $]". iDestruct "Hpub" as "[%Hpub | Hown]".
      + iLeft. simpl. iPureIntro. destruct Hpub as (? & ? & ? & ?); split_and!; [set_solver.. | done].
      + iRight. done.
  Qed.

  Lemma call_id_make_public σ_s σ_t c :
    pub_cid_interp σ_t σ_s -∗
    c @@ ∅ ==∗
    pub_cid c ∗ pub_cid_interp σ_t σ_s.
  Proof.
    iIntros "(%M & Hauth & Hpub) Hcall".
    destruct (M !! c) as [ [] | ] eqn:Hlookup.
    - (* contradictory in principle, but we can play along *)
      iModIntro.
      iPoseProof (big_sepM_delete _ _ _ _ Hlookup with "Hpub") as "[[Hc #Hpublic] Hpubr]".
      iFrame "Hpublic". iExists M. iFrame "Hauth".
      rewrite (big_sepM_delete _ _ _ _ Hlookup). iFrame "Hpubr Hc Hpublic".
    - iMod (ghost_map_insert _ () Hlookup with "Hauth") as "[Hauth Helem]".
      iMod (ghost_map_elem_persist with "Helem") as "#Hpublic".
      iModIntro. iFrame "Hpublic".
      iExists _. iFrame "Hauth". rewrite big_sepM_insert; last done.
      iFrame "Hpub Hpublic". by iRight.
  Qed.

End public_call_ids.

Section tainted_tags.
  Context `{bor_stateGS Σ}.
  (** Interpretation for tainted tags.
    A tag [t] is tainted for a location [l] when invariantly, reads using t at l will fail. *)

  Definition tag_tainted_for (t : nat) (l : loc) :=
    ghost_map_elem tainted_tags_name (t, l) DfracDiscarded tt.

  (* tag [t] is not readable, and never becomes readable again *)
  Definition tag_tainted_interp (σ_s : state) : iProp Σ :=
    ∃ (M : gmap (nat * loc) unit), ghost_map_auth_frac tainted_tags_name 1 M ∗
      ∀ (t : nat) (l : loc), ⌜is_Some (M !! (t, l))⌝ -∗
        tag_tainted_for t l ∗ ⌜disabled_tag σ_s.(scs) σ_s.(strs) σ_s.(snp) t l⌝.

  (* marks that a read yielded poison, and that it will always yield poison in the future *)
  Definition ispoison (v_t : value) l t sz : iProp Σ :=
    (∃ i : nat, ⌜(i < length v_t)%nat ∧ v_t = replicate sz ScPoison⌝ ∗ tag_tainted_for t (l +ₗ i)).

  Lemma ispoison_length v_t l t sz : ispoison v_t l t sz -∗ ⌜length v_t = sz⌝.
  Proof.
    iIntros "(%i&(_&->)&_)". iPureIntro. by rewrite length_replicate.
  Qed.

  Lemma tag_tainted_interp_insert σ_s t l :
    (disabled_tag σ_s.(scs) σ_s.(strs) σ_s.(snp) t l) →
    tag_tainted_interp σ_s ==∗
    tag_tainted_interp σ_s ∗ tag_tainted_for t l.
  Proof.
    iIntros (Hnot_in) "(%M & Hauth & #Hinterp)".
    destruct (M !! (t, l)) as [[] | ] eqn:Hlookup.
    - iModIntro. iPoseProof ("Hinterp" $! t l with "[]") as "($ & _)"; first by eauto.
      iExists M. iFrame "Hauth Hinterp".
    - iMod (ghost_map_insert (t, l) () Hlookup with "Hauth") as "[Hauth He]".
      iMod (ghost_map_elem_persist with "He") as "#He". iFrame "He".
      iModIntro. iExists (<[(t, l) := ()]> M). iFrame "Hauth".
      iIntros (t' l' [[= <- <-] | [Hneq Hsome]]%lookup_insert_is_Some).
      { iFrame "He". eauto. }
      iApply "Hinterp". done.
  Qed.

  Lemma tag_tainted_interp_lookup σ_s t l :
    tag_tainted_for t l -∗
    tag_tainted_interp σ_s -∗
    ⌜disabled_tag σ_s.(scs) σ_s.(strs) σ_s.(snp) t l⌝.
  Proof.
    iIntros "Helem (%M & Hauth & Hinterp)".
    iPoseProof (ghost_map_lookup with "Hauth Helem") as "%Hlookup".
    iPoseProof ("Hinterp" $! t l with "[]") as "(_ & %)"; by eauto.
  Qed.
End tainted_tags.


Definition tag_is_unq (M_tag : gmap tag (tag_kind * unit)) M_t (tg : tag) l := ∃ tkp, M_tag !! tg = Some (tk_unq tkp, ()) ∧ is_Some (heaplet_lookup M_t (tg, l)).

Section state_interp.
  Context `{bor_stateGS Σ} (sc_rel : scalar → scalar → iProp Σ).
  (** The main combined interpretation for the borrow semantics *)

  (* Ownership of the authoritative parts. *)
  Definition bor_auth (M_call : gmap call_id (gmap tag (gmap loc logical_protector))) (M_tag : gmap tag (tag_kind * unit)) (M_t M_s : gmap (tag * block) (gmap Z scalar)) : iProp Σ :=
    ghost_map_auth_frac call_name 1 M_call ∗
    tkmap_auth tag_name 1 M_tag ∗
    ghost_map_auth_frac heap_view_target_name 1 M_t ∗
    ghost_map_auth_frac heap_view_source_name 1 M_s.

  Definition bor_interp_inner (σ_t σ_s : state)
    (M_call : gmap call_id (gmap tag (gmap loc logical_protector)))
    (M_tag : gmap tag (tag_kind * unit))
    (M_t M_s : gmap (tag * block) (gmap Z scalar)) : iProp Σ :=
  (* since multiple parts of the interpretation need access to these maps,
    we own the authoritative parts here and not in the interpretations below *)
    bor_auth M_call M_tag M_t M_s ∗

    tag_tainted_interp σ_s ∗
    pub_cid_interp σ_t σ_s ∗

    state_rel sc_rel M_tag M_t M_call σ_t σ_s ∗
    (* due to the [state_rel], enforcing this on [σ_t] also does the same for [σ_s] *)
    ⌜call_set_interp (tag_is_unq M_tag M_t) M_call σ_t⌝ ∗
    ⌜tag_interp  M_tag M_t M_s σ_t σ_s⌝ ∗

    ⌜state_wf σ_s⌝ ∗
    ⌜state_wf σ_t⌝.

  Definition bor_interp (σ_t : state) (σ_s : state) : iProp Σ :=
   ∃ (M_call : gmap call_id (gmap tag (gmap loc logical_protector)))
     (M_tag : gmap tag (tag_kind * unit))
     (M_t M_s : gmap (tag * block) (gmap Z scalar)),
     bor_interp_inner σ_t σ_s M_call M_tag M_t M_s.

  Lemma bor_interp_get_pure σ_t σ_s :
    bor_interp σ_t σ_s -∗ ⌜trees_equal σ_s.(scs) Forwards σ_s.(strs) σ_t.(strs) ∧ σ_s.(snp) = σ_t.(snp) ∧
    σ_s.(snc) = σ_t.(snc) ∧ σ_s.(scs) = σ_t.(scs) ∧ state_wf σ_s ∧ state_wf σ_t ∧
    dom σ_s.(shp) = dom σ_t.(shp)⌝.
  Proof.
    iIntros "(% & % & % & % & ? & _ & _ & Hstate & _ & _ & % & %)".
    iPoseProof (state_rel_get_pure with "Hstate") as "%".
    iPoseProof (state_rel_dom_eq with "Hstate") as "<-".
    iPureIntro. tauto.
  Qed.

  Lemma bor_interp_get_state_wf σ_t σ_s :
    bor_interp σ_t σ_s -∗
    ⌜state_wf σ_t⌝ ∗ ⌜state_wf σ_s⌝.
  Proof. iIntros "(% & % & % & % & ? & ? & ? & Hstate & _ & _ & % & %)". eauto. Qed.

End state_interp.

Fixpoint list_to_heaplet {A} (scs : list A) (idx : Z) : gmap Z A :=
  match scs with
    nil => ∅
  | sc :: scr => <[ idx := sc ]> (list_to_heaplet scr (idx + 1)) end.
(* This name is historical, there is not actually an array, this is the only way to access the heaplet resource *)
Definition array_tag `{!bor_stateGS Σ} γh (t : tag) (l : loc) (dq : dfrac) (scs : list scalar) : iProp Σ :=
  (ghost_map_elem γh (t, l.1) dq (list_to_heaplet scs l.2))%I.
Notation "l '↦t∗[' tk ']{' t } scs" := (array_tag heap_view_target_name t l (tk_to_frac tk) scs)
  (at level 20, format "l  ↦t∗[ tk ]{ t }  scs") : bi_scope.
Notation "l '↦s∗[' tk ']{' t } scs" := (array_tag heap_view_source_name t l (tk_to_frac tk) scs)
  (at level 20, format "l  ↦s∗[ tk ]{ t }  scs") : bi_scope.


(** [array_tag_map] is the main way we interface with [array_tag] by having a representation of
  the stored memory fragment. *)
Definition array_tag_map (l : loc) (t : tag) (v : list scalar) : gmap (tag * block) (gmap Z scalar) :=
  {[ (t, l.1) := list_to_heaplet v l.2 ]}.

Lemma list_to_heaplet_empty_length {A} (lst : list A) idx :
  list_to_heaplet lst idx = ∅ ↔ length lst = 0%nat.
Proof.
  destruct lst as [|a?]; split; intros H; try done.
  exfalso. enough ((∅ : gmap _ _) !! idx = Some a) as Hc by done.
  rewrite -H lookup_insert_eq //.
Qed.

Lemma list_to_heaplet_lookup_Some {A} (lst : list A) idx lu r :
  list_to_heaplet lst idx !! lu = Some r →
  idx ≤ lu < idx + length lst.
Proof.
  induction lst as [|hd tl IH] in idx|-*.
  - rewrite /= lookup_empty //.
  - rewrite /=. intros [(->&->)|(Hne1&Hin%IH)]%lookup_insert_Some; lia.
Qed.

Lemma list_to_heaplet_lookup_None {A} (lst : list A) idx lu :
  list_to_heaplet lst idx !! lu = None →
  ¬ (idx ≤ lu < idx + length lst).
Proof.
  induction lst as [|hd tl IH] in idx|-*.
  - simpl. lia.
  - rewrite /=. intros (H%IH&Hne)%lookup_insert_None. lia.
Qed.

Lemma list_to_heaplet_nth {A} (lst : list A) idx (off: nat) :
  list_to_heaplet lst idx !! (idx + off) = lst !! off.
Proof.
  induction lst as [|hd tl IH] in idx,off|-*.
  - rewrite /= lookup_empty //.
  - destruct off as [|off].
    + rewrite /= Z.add_0_r lookup_insert_eq //.
    + rewrite /= lookup_insert_ne; last lia.
      rewrite -(IH (idx + 1)). f_equal. lia.
Qed.

Lemma list_to_heaplet_dom {A} (lst : list A) base i :
  base ≤ i < base + length lst ↔ i ∈ dom (list_to_heaplet lst base).
Proof.
  split; intros H.
  - eapply elem_of_dom. destruct (list_to_heaplet lst base !! i) eqn:HH; first done.
    eapply list_to_heaplet_lookup_None in HH. done.
  - eapply elem_of_dom in H. destruct H as [x H].
    by eapply list_to_heaplet_lookup_Some.
Qed.

Lemma list_to_heaplet_dom_1 {A} (lst1 lst2 : list A) idx :
  length lst1 = length lst2 →
  dom (list_to_heaplet lst1 idx) = dom (list_to_heaplet lst2 idx).
Proof.
  intros Hlen. eapply gset_leibniz. intros x. split.
  all: intros (y&Hy%list_to_heaplet_lookup_Some)%elem_of_dom;
    eapply elem_of_dom; destruct lookup eqn:Heq; try done;
    eapply list_to_heaplet_lookup_None in Heq; lia.
Qed.

Local Opaque list_to_heaplet.
Lemma list_to_heaplet_dom_2 {A} (lst1 lst2 : list A) idx :
  dom (list_to_heaplet lst1 idx) = dom (list_to_heaplet lst2 idx) →
  length lst1 = length lst2.
Proof.
  destruct lst1 as [|x1 lst1], lst2 as [|x2 lst2]; simpl in *.
  1: done. 1,2: rewrite !dom_empty_L !dom_insert_L; intros H; exfalso; set_solver.
  intros Hdom. eapply Nat.le_antisymm.
  - enough (idx + length (x1::lst1) ≤ idx + length (x2::lst2)) by (simpl in *; lia).
    destruct (list_to_heaplet_dom (x2::lst2) idx (idx + length lst1)) as [_ (_&Hl)].
    2: simpl in *; lia. rewrite -Hdom. eapply list_to_heaplet_dom. simpl; lia.
  - enough (idx + length (x2::lst2) ≤ idx + length (x1::lst1)) by (simpl in *; lia).
    destruct (list_to_heaplet_dom (x1::lst1) idx (idx + length lst2)) as [_ (_&Hl)].
    2: simpl in *; lia. rewrite Hdom. eapply list_to_heaplet_dom. simpl; lia.
Qed.
Local Transparent list_to_heaplet.

Fixpoint read_range {T} (base : Z) (sz : nat) (M : gmap Z T) : option (list T) := match sz with
  O => Some nil
| S sz => hd ← M !! base; tl ← read_range (1 + base) sz M; Some (hd :: tl) end.

Lemma read_range_length T base (sz : nat) (M : gmap _ T) vs :
  read_range base sz M = Some vs → length vs = sz.
Proof.
  induction sz as [|sz IH] in vs,base|-*.
  1: by intros [= <-].
  simpl. intros (v0&Hv0&(vS&HvS&[= <-])%bind_Some)%bind_Some.
  simpl. f_equal. by eapply IH.
Qed.

Lemma read_range_valid_iff T base (sz : nat) (M : gmap _ T) :
  (∀ i, base ≤ i < base + sz → i ∈ dom M)
↔ is_Some (read_range base sz M).
Proof.
  induction sz as [|sz IH] in base|-*.
  1: split; try done; lia.
  simpl. destruct (IH (1 + base)) as [IHl IHr]. split.
  - intros H. pose proof (H base (ltac:(lia))) as [v0 Hv0]%elem_of_dom.
    rewrite Hv0 /=. destruct IHl as [vS HvS]. 1: intros ??; eapply H; lia.
    rewrite HvS /= //.
  - intros [? (v0&Hv0&(vS&HvS&[= <-])%bind_Some)%bind_Some].
    intros i Hi. destruct (decide (base = i)) as [->|Hne].
    + by eapply elem_of_dom_2.
    + eapply IHr. 1: by eexists. lia.
Qed.

Lemma read_range_lookup_nth T base (sz : nat) (M : gmap _ T) vs :
  read_range base sz M = Some vs →
  ∀ (k:nat) v, vs !! k = Some v → M !! (base + k) = Some v.
Proof.
  intros H1 k. induction k as [|k IH] in H1,base,sz,vs|-*; intros v Hv.
  - destruct vs as [|el0 vs]; first done. simpl in Hv. injection Hv as ->.
    rewrite Z.add_0_r. destruct sz; first done.
    by pose proof H1 as (v'&Hv'&(?&_&[= <- <-])%bind_Some)%bind_Some.
  - destruct vs as [|el0 vs]; first done. simpl in Hv. destruct sz as [|sz]; first done. simpl in H1.
    pose proof H1 as (v'&Hv'&(vs'&Hvs'&[= <- <-])%bind_Some)%bind_Some.
    eapply IH in Hvs'. 2: eassumption. by assert (1 + base + k = base + S k) as <- by lia.
Qed.

Lemma read_range_lookup_nth_inverse T base (sz : nat) (M : gmap _ T) vs :
  read_range base sz M = Some vs →
  ∀ (k:nat) v, M !! (base + k) = Some v → (k < sz)%nat → vs !! k = Some v.
Proof.
  intros H1 k v H2 H3.
  rewrite - (read_range_length _ base sz M vs) // -lookup_lt_is_Some in H3.
  destruct H3 as [x H4]. rewrite H4.
  eapply read_range_lookup_nth in H4. 2: exact H1. congruence.
Qed.


Lemma read_range_list_to_heaplet_read_memory_strict l_hl l_rd sz v_t v_rd hp : 
  read_range l_rd.2 sz (list_to_heaplet v_t l_hl.2) = Some v_rd →
  l_hl.1 = l_rd.1 →
  (∀ i : nat, (i < length v_rd)%nat → hp !! (l_rd +ₗ i) = v_rd !! i) →
  read_mem l_rd sz hp = Some v_rd.
Proof.
  destruct l_hl as [blk off_hl], l_rd as [? off_rd]. simpl.
  intros Hrange <- Hhp.
  eapply read_range_length in Hrange as Hlen.
  eapply read_mem_values'. 1: done.
  intros i Hi.
  eapply mk_is_Some in Hrange as Hrangebounds. rewrite -read_range_valid_iff in Hrangebounds.
  setoid_rewrite <- list_to_heaplet_dom in Hrangebounds.
  assert (∃ (os:nat), off_hl + os = off_rd) as [os Hos].
  { ospecialize (Hrangebounds off_rd  _). 1: lia.
    exists (Z.to_nat (off_rd - off_hl)). lia. }
  subst off_rd. rewrite /shift_loc /= in Hhp|-*.
  rewrite Hhp; last first.
  { ospecialize (Hrangebounds (off_hl + (os + i)%nat) _). 1: lia. lia. }
  symmetry. destruct (v_rd !! i) as [x|] eqn:Hx.
  2: { eapply lookup_ge_None in Hx. lia. }
  eapply read_range_lookup_nth in Hx. 2: done.
  rewrite -Z.add_assoc -Nat2Z.inj_add list_to_heaplet_nth in Hx. done.
Qed.

Lemma read_range_list_to_heaplet_read_memory l_hl l_rd sz v_t v_rd hp : 
  read_range l_rd.2 sz (list_to_heaplet v_t l_hl.2) = Some v_rd →
  l_hl.1 = l_rd.1 →
  (∀ i : nat, (i < length v_t)%nat → hp !! (l_hl +ₗ i) = v_t !! i) →
  read_mem l_rd sz hp = Some v_rd.
Proof.
  destruct l_hl as [blk off_hl], l_rd as [? off_rd]. simpl.
  intros Hrange <- Hhp.
  eapply read_range_length in Hrange as Hlen.
  eapply read_mem_values'. 1: done.
  intros i Hi.
  eapply mk_is_Some in Hrange as Hrangebounds. rewrite -read_range_valid_iff in Hrangebounds.
  setoid_rewrite <- list_to_heaplet_dom in Hrangebounds.
  assert (∃ (os:nat), off_hl + os = off_rd) as [os Hos].
  { ospecialize (Hrangebounds off_rd  _). 1: lia.
    exists (Z.to_nat (off_rd - off_hl)). lia. }
  subst off_rd. rewrite /shift_loc /= in Hhp|-*. rewrite -Z.add_assoc -Nat2Z.inj_add.
  rewrite Hhp; last first.
  { ospecialize (Hrangebounds (off_hl + (os + i)%nat) _). 1: lia. lia. }
  symmetry. destruct (v_rd !! i) as [x|] eqn:Hx.
  2: { eapply lookup_ge_None in Hx. lia. }
  eapply read_range_lookup_nth in Hx. 2: done.
  rewrite -Z.add_assoc -Nat2Z.inj_add list_to_heaplet_nth in Hx. done.
Qed.

Fixpoint write_range_to_list {T} (base : nat) (vals : list T) (into : list T) : list T := match vals with
  nil => into
| hd :: tl => <[ base := hd ]> (write_range_to_list (S base) tl into) end.

Definition write_range {T} (hl_base start : Z) (vals : list T) (into : list T) : option (list T) :=
  if bool_decide (hl_base ≤ start ∧ start + length vals ≤ hl_base + length into)
  then Some (write_range_to_list (Z.to_nat (start - hl_base)) vals into)
  else None.

Lemma write_range_valid_iff {T} hl_base start (vals into : list T) :
  (hl_base ≤ start ∧ start + length vals ≤ hl_base + length into) ↔ is_Some (write_range hl_base start vals into).
Proof.
  split.
  - intros H. rewrite /write_range bool_decide_true //.
  - intros [x Hx]. rewrite /write_range bool_decide_decide in Hx. destruct decide; done.
Qed.

Lemma write_range_is_Some_read_range {T} hl_base start (vals into : list T) :
  is_Some (write_range hl_base start vals into) →
  is_Some (read_range start (length vals) (list_to_heaplet into hl_base)).
Proof.
  intros H%write_range_valid_iff.
  eapply read_range_valid_iff.
  intros i Hi.
  eapply list_to_heaplet_dom. lia.
Qed.

Lemma write_range_to_list_is_Some {T} hl_base start (vals into out : list T) :
  write_range hl_base start vals into = Some out →
  ∃ base, write_range_to_list base vals into = out ∧ start = hl_base + base ∧ base + length vals ≤ length into.
Proof.
  intros H. rewrite /write_range bool_decide_decide in H. destruct decide as [Hb|?]; last done.
  exists (Z.to_nat (start - hl_base)). split; last lia.
  by injection H.
Qed.

Lemma write_range_to_list_same_length {T} base (vals into out : list T) :
  write_range_to_list base vals into = out →
  length into = length out.
Proof.
  intros <-.
  induction vals as [|v vals IH] in base,into|-*.
  1: done.
  rewrite /= length_insert -IH //.
Qed.

Lemma write_range_to_list_length {T} base (vals into : list T) :
  length (write_range_to_list base vals into) = length into.
Proof.
  symmetry. by eapply write_range_to_list_same_length.
Qed.

Lemma write_range_same_length {T} hl_base start (vals into out : list T) :
  write_range hl_base start vals into = Some out →
  length into = length out.
Proof.
  intros (base&H1&_&H2)%write_range_to_list_is_Some.
  by eapply write_range_to_list_same_length.
Qed.

Lemma write_mem_insert l vs hp li vi :
  (l.1 = li.1 → li.2 < l.2) →
  write_mem l vs (<[ li := vi ]> hp) = <[ li := vi]> (write_mem l vs hp).
Proof.
  induction vs as [|v vs IH] in hp,l|-*; first done.
  intros Hli. simpl. rewrite -IH. 2: simpl; lia.
  f_equal. eapply insert_insert_ne. intros H. subst l. lia.
Qed.

Lemma write_range_write_memory l_hl l_wr v_t v_wr v_t' hp :
  write_range l_hl.2 l_wr.2 v_wr v_t = Some v_t' →
  l_hl.1 = l_wr.1 →
  (∀ i : nat, (i < length v_t)%nat → hp !! (l_hl +ₗ i) = v_t !! i) →
  ∃ hp', write_mem l_wr v_wr hp = hp' ∧
    (∀ i : nat, (i < length v_t)%nat → hp' !! (l_hl +ₗ i) = v_t' !! i).
Proof.
  intros (base&Hwrite&Hbase&Hlen)%write_range_to_list_is_Some Heq Hi.
  destruct l_hl as [blk off_hl], l_wr as [b off_wr]; simpl in *; subst b.
  induction v_wr as [|v v_wr IH] in v_t',base,off_wr,Hlen,Hbase,Hwrite|-*.
  1: { eexists; split; first done. simpl. simpl in Hwrite. subst v_t'. apply Hi. }
  simpl. rewrite /shift_loc /= in Hi|-*.
  remember (write_range_to_list (S base) v_wr v_t) as v_t1 eqn:Hvt1. rewrite /= -Hvt1 in Hwrite.
  symmetry in Hvt1.
  odestruct (IH (off_wr + 1) _ (S base) Hvt1) as (hp'&Hhp'&Hi').
  1-2: simpl in Hlen; lia.
  rewrite write_mem_insert. 2: simpl; lia.
  erewrite Hhp'. eexists; split; first done.
  intros idx Hidx. destruct (decide (idx = base)) as [<-|Hne].
  + rewrite Hbase lookup_insert_eq -Hwrite list_lookup_insert_eq //.
    eapply write_range_to_list_same_length in Hvt1. lia.
  + rewrite lookup_insert_ne. 2: injection; lia.
    rewrite (Hi' idx). 2: lia. subst v_t'. by rewrite list_lookup_insert_ne.
Qed.

Lemma write_range_write_memory_smaller l_hl l_wr v_t v_wr v_t' hp :
  write_range l_hl.2 l_wr.2 v_wr v_t = Some v_t' →
  l_hl.1 = l_wr.1 →
  (∀ i : nat, (i < length v_wr)%nat → is_Some (hp !! (l_wr +ₗ i))) →
  ∃ hp', write_mem l_wr v_wr hp = hp' ∧
    (∀ i : nat, (i < length v_wr)%nat → hp' !! (l_wr +ₗ i) = v_wr !! i).
Proof.
  intros (base&Hwrite&Hbase&Hlen)%write_range_to_list_is_Some Heq.
  destruct l_hl as [blk off_hl], l_wr as [b off_wr]; simpl in *; subst b.
  induction v_wr as [|v v_wr IH] in v_t',base,off_wr,Hlen,Hbase,Hwrite|-*; intros Hi.
  1: { eexists; split; first done. simpl. simpl in Hwrite. subst v_t'. intros ??; lia. }
  simpl. rewrite /shift_loc /= in Hi|-*.
  remember (write_range_to_list (S base) v_wr v_t) as v_t1 eqn:Hvt1. rewrite /= -Hvt1 in Hwrite.
  symmetry in Hvt1.
  odestruct (IH (off_wr + 1) _ (S base) Hvt1) as (hp'&Hhp'&Hi').
  1-2: simpl in Hlen; lia.
  { intros im Him. destruct (Hi (S im)) as [x Hx]. 1: lia. exists x. rewrite -Hx. f_equal. rewrite /shift_loc /=. f_equal. lia. }
  rewrite write_mem_insert. 2: simpl; lia.
  erewrite Hhp'. eexists; split; first done.
  intros idx Hidx. destruct idx as [|idx].
  + rewrite Z.add_0_r. rewrite lookup_insert_eq. simpl. done.
  + rewrite lookup_insert_ne. 2: injection; lia. simpl.
    rewrite -(Hi' idx). 2: lia. rewrite /shift_loc /=. do 2 f_equal. lia. 
Qed.

Lemma write_range_to_list_lookup_inv {T} b (vnew vold : list T) (i:nat) r :
  write_range_to_list b vnew vold !! i = r →
 ((  b ≤ i ∧ i < b + length vnew ∧ i < length vold  → r = vnew !! (i - b)) ∧
  (¬(b ≤ i ∧ i < b + length vnew ∧ i < length vold) → r = vold !! i))%nat.
Proof.
  induction vnew as [|v vs IH] in b,vold,i,r|-*; simpl.
  1: intros H; split_and!; try done; lia.
  destruct (decide (i = b ∧ i < length vold)) as [(->&Hlt)|Hne].
  - rewrite list_lookup_insert_eq. 2: rewrite write_range_to_list_length; lia.
    intros <-. split; last lia.
    intros _. rewrite Nat.sub_diag /= //.
  - assert (<[ b := v ]> (write_range_to_list (S b) vs vold) !! i = write_range_to_list (S b) vs vold !! i) as ->.
    { destruct (decide (i = b)) as [->|Hne2]. 2: by rewrite list_lookup_insert_ne.
      rewrite !lookup_ge_None_2. 1: done. 2: rewrite length_insert. all: rewrite write_range_to_list_length. all: lia. }
    intros (H1&H2)%IH. split.
    + intros (Hi1&Hi2&Hi3). assert (i-b = S (i - S b))%nat as -> by lia. simpl. eapply H1. lia.
    + intros Hn. eapply H2. lia.
Qed.

Lemma write_range_to_list_lookup {T} b (vnew vold : list T) (i:nat) r :
 ((  b ≤ i ∧ i < b + length vnew ∧ i < length vold  → r = vnew !! (i - b)) ∧
  (¬(b ≤ i ∧ i < b + length vnew ∧ i < length vold) → r = vold !! i))%nat →
  write_range_to_list b vnew vold !! i = r.
Proof.
  induction vnew as [|v vs IH] in b,vold,i,r|-*; simpl; intros (H1&H2); symmetry.
  1: eapply H2; lia.
  destruct (decide (i = b ∧ i < length vold)) as [(->&Hlt)|Hne].
  - rewrite list_lookup_insert_eq. 2: rewrite write_range_to_list_length; lia.
    rewrite Nat.sub_diag /= in H1. eapply H1. lia.
  - assert (<[ b := v ]> (write_range_to_list (S b) vs vold) !! i = write_range_to_list (S b) vs vold !! i) as ->.
    { destruct (decide (i = b)) as [->|Hne2]. 2: by rewrite list_lookup_insert_ne.
      rewrite !lookup_ge_None_2. 1: done. 2: rewrite length_insert. all: rewrite write_range_to_list_length. all: lia. }
    symmetry. eapply IH. split.
    + intros (Hi1&Hi2&Hi3). assert (i-b = S (i - S b))%nat as HH by lia. rewrite HH in H1. simpl in H1. eapply H1. lia.
    + intros Hn. eapply H2. lia.
Qed.

Lemma write_range_to_to_list {T} b1 b2 (vnew vold : list T) :
  b1 ≤ b2 ∧ b2 + length vnew ≤ b1 + length vold →
  write_range b1 b2 vnew vold = Some (write_range_to_list (Z.to_nat (b2 - b1)) vnew vold).
Proof.
  intros HH.
  rewrite /write_range bool_decide_eq_true_2 //.
Qed.

Fixpoint read_list_range {T} (base:nat) (size:nat) (lst : list T) : option (list T) := match size with
         O => Some nil
  | S size => v0 ← lst !! base ; vs ← read_list_range (S base) size lst ; Some (v0 :: vs) end.

Lemma read_range_heaplet_to_list {T} (base1 base2 : Z) size (lst : list T) :
  base1 ≤ base2 →
  read_range base2 size (list_to_heaplet lst base1) = read_list_range (Z.to_nat (base2 - base1)) size lst.
Proof.
  induction size as [|sz IH] in base1,base2|-*; first done.
  intros Hbase. simpl. assert (∃ (idx:nat), base2 = base1 + idx)%Z as (idx&->).
  1: exists (Z.to_nat (base2 - base1)); lia.
  rewrite list_to_heaplet_nth. eassert (Z.to_nat (_ + _ - _) = idx) as ->. 1: lia.
  destruct (lst !! idx) as [?|]; last done. simpl.
  rewrite IH. 2: lia. f_equal. f_equal. lia.
Qed.
  
Lemma ghost_map_array_tag_update `{!bor_stateGS Σ} (γh : gname) (M : gmap (tag * block) (gmap Z scalar)) (v v' : list scalar) (t : tag) (l : loc) :
  length v = length v' →
  ghost_map_auth_frac γh 1 M -∗
  array_tag γh t l (DfracOwn 1) v ==∗
  array_tag γh t l (DfracOwn 1) v' ∗
  ghost_map_auth_frac γh 1 (array_tag_map l t v' ∪ M).
Proof.
  iIntros (Hlen) "Hauth Helems".
  rewrite /array_tag_map -insert_union_singleton_l.
  iMod (ghost_map_update with "Hauth Helems") as "(Hauth&Helems)".
  iModIntro. iFrame.
Qed.

Lemma ghost_map_array_tag_insert `{!bor_stateGS Σ} (γh : gname) (M : gmap (tag * block) (gmap Z scalar)) (v : list scalar) (t : tag) (l : loc) tk :
  M !! (t, l.1) = None →
  ghost_map_auth_frac γh 1 M ==∗
  array_tag γh t l (tk_to_frac tk) v ∗
  ghost_map_auth_frac γh 1 (array_tag_map l t v ∪ M).
Proof.
  iIntros (Hnotin) "Hauth".
  iMod (ghost_map_insert with "Hauth") as "(Hauth&Helems)". 1: done.
  erewrite insert_union_singleton_l. iFrame "Hauth".
  destruct tk as [| |]. 1: iMod (ghost_map_elem_persist with "Helems") as "Helems".
  all: by iFrame.
Qed.

Section val_rel.
  Context `{bor_stateGS Σ}.
  (** Value relation *)

  Definition sc_rel (sc1 sc2 : scalar) : iProp Σ :=
    match sc1, sc2 with
    | ScInt z1, ScInt z2 => ⌜z1 = z2⌝
    | ScFnPtr f1, ScFnPtr f2 => ⌜f1  = f2⌝
    | ScPtr l1 p1, ScPtr l2 p2 =>
        (* through [state_rel]:
          * the stacks are the same,
          * the allocation size is the same,
          * and the locations are related (i.e.: public)
        *)
        ⌜l1 = l2⌝ ∗  ⌜p1 = p2⌝ ∗ p1 $$ tk_pub
    | ScCallId c, ScCallId c' => ⌜c = c'⌝ ∗ pub_cid c
    (* [ScPoison] can be refined by anything *)
    | _ , ScPoison => True
    | _, _ => False
    end.

  (* does not hold definitionally *)
  Lemma sc_rel_source_poison t : ⊢ sc_rel t ScPoison.
  Proof. by destruct t. Qed.

  Definition value_rel (v1 v2 : value) : iProp Σ := [∗ list] sc_t; sc_s ∈ v1; v2, sc_rel sc_t sc_s.

  Definition rrel (r1 r2 : result) : iProp Σ :=
    match r1, r2 with
    | ValR v1, ValR v2 => value_rel v1 v2
    | PlaceR l1 bor1 T1, PlaceR l2 bor2 T2 =>
      (* places must be related in a similar way as pointers: either untagged or public. Types should be equal. *)
      sc_rel (ScPtr l1 bor1) (ScPtr l2 bor2) ∧ ⌜T1 = T2⌝
    | _, _ => False
    end.

  Global Instance sc_rel_persistent sc_t sc_s : Persistent (sc_rel sc_t sc_s).
  Proof. destruct sc_t, sc_s; apply _. Qed.
  Global Instance value_rel_persistent v_t v_s : Persistent (value_rel v_t v_s).
  Proof. apply _. Qed.
  Global Instance rrel_persistent r_t r_s : Persistent (rrel r_t r_s).
  Proof. destruct r_t, r_s; apply _. Qed.

  (* Inversion lemmas *)
  Lemma sc_rel_ptr_source sc_t l_s t_s :
    sc_rel sc_t (ScPtr l_s t_s) -∗ ⌜sc_t = ScPtr l_s t_s⌝ ∗ t_s $$ tk_pub.
  Proof.
    iIntros "Hrel". destruct sc_t; [done | done | | done | done ].
    iDestruct "Hrel" as "(-> & -> & $)". done.
  Qed.
  Lemma sc_rel_fnptr_source sc_t fn :
    sc_rel sc_t (ScFnPtr fn) -∗ ⌜sc_t = ScFnPtr fn⌝.
  Proof.
    iIntros "Hrel". destruct sc_t; [done | done | done | | done].
    by iDestruct "Hrel" as "->".
  Qed.
  Lemma sc_rel_int_source sc_t z :
    sc_rel sc_t (ScInt z) -∗ ⌜sc_t = ScInt z⌝.
  Proof.
    iIntros "Hrel". destruct sc_t; [ done | | done..].
    by iDestruct "Hrel" as "->".
  Qed.
  Lemma sc_rel_cid_source sc_t c :
    sc_rel sc_t (ScCallId c) -∗ ⌜sc_t = ScCallId c⌝ ∗ pub_cid c.
  Proof. iIntros "Hrel"; destruct sc_t; [done.. | ]. by iDestruct "Hrel" as "[-> $]". Qed.

  Lemma sc_rel_poison_target sc_s :
    sc_rel (ScPoison) sc_s -∗ ⌜sc_s = ScPoison⌝.
  Proof. iIntros "Hrel". destruct sc_s; done. Qed.

  Lemma sc_rel_ptr_target sc_s l_t t_t :
    sc_rel (ScPtr l_t t_t) sc_s -∗ (⌜sc_s = ScPtr l_t t_t⌝ ∗ t_t $$ tk_pub) ∨ ⌜sc_s = ScPoison⌝.
  Proof.
    iIntros "Hrel". destruct sc_s; [ by iRight | done | | done | done ]. iLeft.
    iDestruct "Hrel" as "(-> & -> & $)". done.
  Qed.
  Lemma sc_rel_fnptr_target sc_s fn :
    sc_rel (ScFnPtr fn) sc_s -∗ ⌜sc_s = ScFnPtr fn⌝ ∨ ⌜sc_s = ScPoison⌝.
  Proof.
    iIntros "Hrel". destruct sc_s; [by iRight | done | done | | done].
    iLeft. by iDestruct "Hrel" as "->".
  Qed.
  Lemma sc_rel_int_target sc_s z :
    sc_rel (ScInt z) sc_s -∗ ⌜sc_s = ScInt z⌝ ∨ ⌜sc_s = ScPoison⌝.
  Proof.
    iIntros "Hrel". destruct sc_s; [ by iRight | | done..].
    iLeft. by iDestruct "Hrel" as "->".
  Qed.
  Lemma sc_rel_cid_target sc_s c :
    sc_rel (ScCallId c) sc_s -∗ (⌜sc_s = ScCallId c⌝ ∗ pub_cid c) ∨ ⌜sc_s = ScPoison⌝.
  Proof. iIntros "Hrel"; destruct sc_s; [ by iRight | done.. | ]. iLeft. by iDestruct "Hrel" as "[-> $]". Qed.

  Lemma rrel_place_source r_t l_s t_s T :
    rrel r_t (PlaceR l_s t_s T) -∗
    ⌜r_t = PlaceR l_s t_s T⌝ ∗ t_s $$ tk_pub.
  Proof.
    iIntros "Hrel".
    destruct r_t as [ | l_t t' T']; first done. iDestruct "Hrel" as "(#H & ->)".
    iDestruct (sc_rel_ptr_source with "H") as "[%Heq Htag]".
    injection Heq as [= -> ->]. eauto.
  Qed.
  Lemma rrel_value_source r_t v_s :
    rrel r_t (ValR v_s) -∗
    ∃ v_t, ⌜r_t = ValR v_t⌝ ∗ value_rel v_t v_s.
  Proof.
    iIntros "Hrel". destruct r_t as [ v_t | ]; last done.
    iExists v_t. iFrame "Hrel". done.
  Qed.

  Lemma value_rel_length v_t v_s :
    value_rel v_t v_s -∗ ⌜length v_t = length v_s⌝.
  Proof. iApply big_sepL2_length. Qed.
  Lemma value_rel_empty :
    ⊢ value_rel [] [].
  Proof. by iApply big_sepL2_nil. Qed.

  Lemma value_rel_singleton_source v_t sc_s :
    value_rel v_t [sc_s] -∗ ∃ sc_t, ⌜v_t = [sc_t]⌝ ∗ sc_rel sc_t sc_s.
  Proof.
    iIntros "Hv". iPoseProof (value_rel_length with "Hv") as "%Hlen".
    destruct v_t as [ | sc_t []]; [done | | done ].
    iExists sc_t. iSplitR "Hv"; first done. iRevert "Hv". rewrite /value_rel big_sepL2_singleton. eauto.
  Qed.

  Lemma rrel_singleton_source r_t sc_s :
    rrel r_t (ValR [sc_s]) -∗
    ∃ sc_t, ⌜r_t = ValR [sc_t]⌝ ∗ sc_rel sc_t sc_s.
  Proof.
    iIntros "H". iPoseProof (rrel_value_source with "H") as (v_t ->) "H".
    iPoseProof (value_rel_singleton_source with "H") as (sc_t ->) "?". eauto.
  Qed.

  Lemma value_rel_lookup v_t v_s (i : nat) :
    i < length v_t →
    value_rel v_t v_s -∗
    ∃ sc_t sc_s, ⌜v_t !! i = Some sc_t⌝ ∗ ⌜v_s !! i = Some sc_s⌝ ∗ sc_rel sc_t sc_s.
  Proof.
    iIntros (Hi) "Hvrel". rewrite /value_rel big_sepL2_forall.
    iDestruct "Hvrel" as "[%Hlen Hvrel]".
    iSpecialize ("Hvrel" $! i (v_t !!! i) (v_s !!! i)). iExists (v_t !!! i), (v_s !!! i).
    assert (v_t !! i = Some (v_t !!! i)) as Heq.
    { apply list_lookup_lookup_total. apply lookup_lt_is_Some_2. lia. }
    assert (v_s !! i = Some (v_s !!! i)) as Heq'.
    { apply list_lookup_lookup_total. apply lookup_lt_is_Some_2. lia. }
    iSplit; first done. iSplit; first done. iApply "Hvrel"; done.
  Qed.

  Lemma value_rel_lookup_total (v_t v_s : list scalar) (i : nat) :
    i < length v_t → value_rel v_t v_s -∗ sc_rel (v_t !!! i) (v_s !!! i).
  Proof.
    iIntros (Hi) "Hvrel". rewrite /value_rel big_sepL2_forall.
    iDestruct "Hvrel" as "[%Hlen Hvrel]".
    iApply ("Hvrel" $! i (v_t !!! i) (v_s !!! i)).
    all: iPureIntro; apply list_lookup_lookup_total; apply lookup_lt_is_Some_2; lia.
  Qed.

  (* Unfolding rrel *)
  Lemma rrel_value_rel v1 v2 :
    rrel #v1 #v2 ⊣⊢ value_rel v1 v2.
  Proof. done. Qed.
  Lemma rrel_sc_rel l1 tg1 T1 l2 tg2 T2 :
    rrel (PlaceR l1 tg1 T1) (PlaceR l2 tg2 T2)
    ⊣⊢ sc_rel (ScPtr l1 tg1) (ScPtr l2 tg2) ∧ ⌜ T1 = T2 ⌝.
  Proof. done. Qed.

  Lemma value_rel_singleton sc_1 sc_2:
    value_rel [sc_1] [sc_2 ] ⊣⊢ sc_rel sc_1 sc_2.
  Proof. by rewrite /value_rel /= right_id. Qed.
  (* Some reflexivity lemmas for [value_rel] and [rrel] *)

  Local Ltac solve_value_rel := rewrite value_rel_singleton; eauto.
  Lemma value_rel_poison :
    ⊢ value_rel [☠%S] [☠%S].
  Proof. solve_value_rel. Qed.
  Lemma value_rel_int z :
    ⊢ value_rel [ScInt z] [ScInt z].
  Proof. solve_value_rel. Qed.
  Lemma value_rel_fnptr fn :
    ⊢ value_rel [ScFnPtr fn] [ScFnPtr fn].
  Proof. solve_value_rel. Qed.
  Lemma value_rel_callid c :
    pub_cid c
    ⊢ value_rel [ScCallId c] [ScCallId c].
  Proof. rewrite value_rel_singleton. iIntros "Hc"; simpl. eauto. Qed.

  Lemma sc_rel_ptr l tg :
    tg $$ tk_pub
    ⊢ sc_rel (ScPtr l tg) (ScPtr l tg).
  Proof.
    iIntros "Hr". iSplit; [done|].
    eauto with iFrame.
  Qed.
  Lemma value_rel_ptr l tg :
    tg $$ tk_pub
    ⊢ value_rel [ScPtr l tg] [ScPtr l tg].
  Proof. by rewrite (sc_rel_ptr l) value_rel_singleton. Qed.

  Lemma rrel_place l tg T :
    tg $$ tk_pub
    ⊢ rrel (PlaceR l tg T) (PlaceR l tg T).
  Proof. rewrite (sc_rel_ptr l) rrel_sc_rel. eauto. Qed.

  Lemma value_rel_app v_t1 v_s1 v_t2 v_s2 :
    value_rel v_t1 v_s1 -∗ value_rel v_t2 v_s2 -∗ value_rel (v_t1 ++ v_t2) (v_s1 ++ v_s2).
  Proof.
    iIntros "Hv1 Hv2".
    iDestruct (value_rel_length with "Hv1") as %EqL.
    rewrite /value_rel. iApply (big_sepL2_app with "Hv1 Hv2").
  Qed.

  Definition will_read_in_simulation v_src v_tgt (l_rd : loc) (t : tag) : iProp Σ :=
    value_rel v_tgt v_src(* ∨ (⌜length v_src = length v_tgt⌝ ∗ ispoison (replicate (length v_tgt) ScPoison) l_rd t (length v_tgt))*).

End val_rel.

(** Simulation / relation final setup *)
Class sborGS (Σ: gFunctors) := SBorGS {
  (* program assertions *)
  sborG_gen_progG ::> gen_sim_progGS string (string*expr) (string*expr) Σ;
  sborG_stateG ::> bor_stateGS Σ;
}.
Definition sborΣ : gFunctors := (#[bor_stateΣ; gen_progΣ string (string*expr)]).
Class sborGpreS (Σ: gFunctors) := SBorGpreS {
  sbor_pre_stateG ::> bor_stateGpreS Σ | 10;
  sbor_pre_progG ::> gen_progGpreS Σ string (string*expr) | 10;
}.

Global Instance subG_sborΣ Σ :
  subG sborΣ Σ → sborGpreS Σ.
Proof. solve_inG. Qed.

Global Program Instance sborGS_simulirisGS `{!sborGS Σ} : simulirisGS (iPropI Σ) bor_lang := {
  state_interp P_t σ_t P_s σ_s T_s :=
    (has_prog (hG := gen_prog_inG_target) P_t ∗
     has_prog (hG := gen_prog_inG_source) P_s ∗
     bor_interp sc_rel σ_t σ_s
    )%I;
  ext_rel π r_t r_s := rrel r_t r_s;
}.
Next Obligation.
  iIntros (?????????? Hthread Hprim). simpl. eauto.
Qed.

Notation log_rel := (gen_log_rel rrel (λ _, True%I)).

(** Program assertions *)
Notation "f '@t' Kt" := (has_fun (hG:=gen_prog_inG_target) f Kt)
  (at level 20, format "f  @t  Kt") : bi_scope.
Notation "f '@s' Ks" := (has_fun (hG:=gen_prog_inG_source) f Ks)
  (at level 20, format "f  @s  Ks") : bi_scope.

Lemma hasfun_target_agree `{sborGS Σ} f K_t1 K_t2 : f @t K_t1 -∗ f @t K_t2 -∗ ⌜K_t1 = K_t2⌝.
Proof. apply has_fun_agree. Qed.

Lemma hasfun_source_agree `{sborGS Σ} f K_s1 K_s2 : f @s K_s1 -∗ f @s K_s2 -∗ ⌜K_s1 = K_s2⌝.
Proof. apply has_fun_agree. Qed.


Lemma sbor_init `{!sborGpreS Σ} P_t P_s T_s :
  ⊢@{iPropI Σ} |==> ∃ `(!sborGS Σ),
      state_interp P_t init_state P_s init_state T_s ∗
    ([∗ map] f ↦ fn ∈ P_t, f @t fn) ∗
    ([∗ map] f ↦ fn ∈ P_s, f @s fn) ∗
    progs_are P_t P_s.
Proof.
  set σ := init_state.
  iMod (ghost_map_alloc (∅ : gmap call_id (gmap tag (gmap loc logical_protector)))) as (γcall) "[Hcall_auth _]".
  iMod (tkmap_alloc (∅ : gmap tag (tag_kind * unit))) as (γtag) "[Htag_auth _]".
  iMod (ghost_map_alloc (∅ : gmap (tag * block) (gmap Z scalar))) as (γtgt) "[Hheap_tgt_auth _]".
  iMod (ghost_map_alloc (∅ : gmap (tag * block) (gmap Z scalar))) as (γsrc) "[Hheap_src_auth _]".
  iMod (ghost_map_alloc (∅ : gmap call_id unit)) as (γpub_call) "[Hpub_call_auth _]".
  iMod (ghost_map_alloc (∅ : gmap (nat * loc) unit)) as (γtainted) "[Htainted_auth _]".
  iMod (gen_sim_prog_init P_t P_s) as (?) "[#Hprog_t #Hprog_s]".
  iModIntro.
  set (bor := BorStateGS _ _ γcall _ γtag _ γtgt γsrc _ γpub_call  _ γtainted).
  iExists (SBorGS _ _ _).
  iSplitL; last iSplit; last iSplit.
  - simpl. iFrame "Hprog_t Hprog_s".
    iExists ∅, ∅, ∅, ∅.
    iFrame "Hcall_auth Htag_auth Hheap_tgt_auth Hheap_src_auth".
    iSplitL "Htainted_auth".
    { iExists ∅. iFrame. iIntros (t l (?&Hl)). by rewrite lookup_empty in Hl. }
    iSplitL "Hpub_call_auth".
    { iFrame. iApply big_sepM_empty. done. }
    iSplitL.
    { do 5 (iSplit; first (done || (iPureIntro; apply trees_equal_empty))). iIntros (l Hl). exfalso.
      move : Hl. rewrite lookup_empty. intros [? [=]]. }
    iSplitL.
    { iPureIntro. split; setoid_rewrite lookup_empty; intros *; done. }
    iSplitL.
    { iPureIntro. split_and!.
      - intros t tk. rewrite lookup_empty. congruence.
      - intros t l. rewrite lookup_empty. intros [? [=]].
      - intros t l. rewrite lookup_empty. intros [? [=]].
      - intros ??? HH. by rewrite dom_empty_L in HH.
      - intros ??? HH. by rewrite dom_empty_L in HH.
    }
    iSplit; iPureIntro. all: apply wf_init_state.
  - by iApply has_prog_all_funs.
  - by iApply has_prog_all_funs.
  - rewrite /progs_are /=. iIntros "!#" (P_t' P_s' σ_t' σ_s' T_s') "(#Hprog_t2 & #Hprog_s2 & _)".
    iDestruct (has_prog_agree with "Hprog_t Hprog_t2") as %->.
    iDestruct (has_prog_agree with "Hprog_s Hprog_s2") as %->.
    done.
Qed.
