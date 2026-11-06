(** This file provides the basic heap and ghost state support for the BorIngLang program logic. *)
From iris.proofmode Require Export proofmode.
From iris.bi.lib Require Import fractional.
From iris.base_logic.lib Require Import ghost_map.
From simuliris.base_logic Require Export gen_sim_prog.
From simuliris.simulation Require Export slsls gen_log_rel.
From simuliris.simulation Require Import lifting.
From simuliris.stacked_borrows Require Import tkmap_view.
From simuliris.stacked_borrows Require Export defs.
From simuliris.stacked_borrows Require Import steps_progress steps_retag.

(** * BorLang ghost state *)
Class bor_stateGS Σ := BorStateGS {
  (* Maintaining the locations protected by each call id *)
  call_inG :: ghost_mapG Σ call_id (gmap ptr_id (gset loc));
  call_name : gname;

  (* tag ownership *)
  tag_inG :: tkmapG Σ ptr_id unit;
  tag_name : gname;

  (* A view of parts of the heap, conditional on the ptr_id *)
  heap_view_inG :: ghost_mapG Σ (ptr_id * loc) scalar;
  heap_view_source_name : gname;
  heap_view_target_name : gname;

  (* Public call IDs *)
  pub_call_inG :: ghost_mapG Σ call_id unit;
  pub_call_name : gname;

  (* Tainted tags: a set of tag * source location *)
  tainted_tag_collection :: ghost_mapG Σ (ptr_id * loc) unit;
  tainted_tags_name : gname;
}.

Class bor_stateGpreS Σ := {
  (* Maintaining the locations protected by each call id *)
  call_pre_inG :: ghost_mapG Σ call_id (gmap ptr_id (gset loc));

  (* tag ownership *)
  tag_pre_inG :: tkmapG Σ ptr_id unit;

  (* A view of parts of the heap, conditional on the ptr_id *)
  heap_view_pre_inG :: ghost_mapG Σ (ptr_id * loc) scalar;

  (* Public call IDs *)
  pub_call_pre_inG :: ghost_mapG Σ call_id unit;

  (* Tainted tags: a set of tag * source location *)
  tainted_tag_pre_collection :: ghost_mapG Σ (ptr_id * loc) unit;
}.

Definition bor_stateΣ : gFunctors := (#[ghost_mapΣ call_id (gmap ptr_id (gset loc)); ghost_mapΣ (ptr_id * loc) scalar; ghost_mapΣ call_id unit; ghost_mapΣ (ptr_id * loc) unit; tkmapΣ ptr_id unit]).

Global Instance subG_bor_stateΣ Σ :
  subG bor_stateΣ Σ → bor_stateGpreS Σ.
Proof. solve_inG. Qed.

Section state_bijection.
  Context `{bor_stateGS Σ}.

  Context (sc_rel : scalar → scalar → iProp Σ).

  Section defs.
    (* We need all the maps from the tag interpretation here....
     TODO: can we make that more beautiful? all the different invariants are interleaved in subtle ways, which makes modular reasoning really hard... *)
    Context (M_tag : gmap ptr_id (tag_kind * unit)) (M_t M_s : gmap (ptr_id * loc) scalar) (Mcall_t : gmap call_id (gmap ptr_id (gset loc))).


    Definition call_set_in (M : gmap ptr_id (gset loc)) t l :=
      ∃ L, M !! t = Some L ∧ l ∈ L.
    Definition call_set_in' (M : gmap call_id (gmap ptr_id (gset loc))) c t l :=
      ∃ M', M !! c = Some M' ∧ call_set_in M' t l.
    Definition pub_loc σ_t σ_s (l : loc) : iProp Σ :=
      ∀ sc_t, ⌜σ_t.(shp) !! l = Some sc_t⌝ → ∃ sc_s, ⌜σ_s.(shp) !! l = Some sc_s⌝ ∗ sc_rel sc_t sc_s.
    Definition priv_loc t (l : loc) : Prop :=
      ∃ tk, M_tag !! t = Some (tk, tt) ∧ is_Some (M_t !! (t, l)) ∧
        (* local *)
        (tk = tk_local ∨
        (* unique with protector *)
        (tk = tk_unq ∧ ∃ c, call_set_in' Mcall_t c t l)).

    (* This definition enforces quite strict requirements on the state:
      - the domains of the heaps shp are the same
      - the stacks are the same
      - the call counter is the same
      - the tag counter is the same
      - the set of ongoing calls is the same
      - there's a relation on the scalars stored at locations ([pub_loc]), except when the location is currently controlled by a tag ([priv_loc]).

      Note that, while the definition may appear asymmetric in source and target, due to the well-formedness on states [state_wf] and the relation of the tag maps enforced below, it really is symmetric in practice.
    *)
    Definition state_rel σ_t σ_s : iProp Σ :=
        ⌜dom σ_s.(shp) = dom σ_t.(shp)⌝ ∗
        ⌜σ_s.(sst) = σ_t.(sst)⌝ ∗
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
    state_rel Mtag Mt Mcall σ_t σ_s -∗ ⌜σ_s.(sst) = σ_t.(sst) ∧
      σ_s.(snp) = σ_t.(snp) ∧ σ_s.(snc) = σ_t.(snc) ∧ σ_s.(scs) = σ_t.(scs)⌝.
  Proof. iIntros "(% & % & % & % & % & ?)". eauto. Qed.
  Lemma state_rel_stacks_eq Mtag Mt Mcall σ_t σ_s :
    state_rel Mtag Mt Mcall σ_t σ_s -∗ ⌜σ_s.(sst) = σ_t.(sst)⌝.
  Proof. iIntros "(% & % & % & % & % & ?)". eauto. Qed.
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
    priv_loc Mtag (<[(t',l') := sc]> Mt) Mcall t l.
  Proof.
    rewrite /priv_loc. intros (tk & Ht & Hs & Hinv). exists tk.
    split_and!; [ done | | done].
    apply lookup_insert_is_Some. destruct (decide ((t', l') = (t, l))); eauto.
  Qed.

  Lemma state_rel_upd_priv_target M_tag M_t Mcall σ_t σ_s l t sc :
    is_Some (σ_t.(shp) !! l) →
    priv_loc M_tag M_t Mcall t l →
    state_rel M_tag M_t Mcall σ_t σ_s -∗
    state_rel M_tag (<[(t, l) := sc]> M_t) Mcall (state_upd_mem (<[l := sc]>) σ_t) σ_s.
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
  Context {Σ} (call_gname : gname) {call_inG : ghost_mapG Σ (call_id) (gmap ptr_id (gset loc))}.

  Implicit Types (c : call_id) (pid : ptr_id) (pm : permission).

  Definition call_set_is (c : call_id) (M : gmap ptr_id (gset loc)) :=
    ghost_map_elem call_gname c (DfracOwn 1) M.

  (* This does not assert ownership of the authoritative part. Instead, this is owned by bor_interp below. *)
  Definition call_set_interp (M : gmap call_id (gmap ptr_id (gset loc))) (σ : state) : Prop :=
    ∀ c (M' : gmap ptr_id (gset loc)), M !! c = Some M' →
      c ∈ σ.(scs) ∧
      (* for every ptr_id *)
      ∀ t (L : gset loc), M' !! t = Some L →
        (t < σ.(snp))%nat ∧
        (* for every protected location [l], there needs to be a protector in the stack *)
        ∀ (l : loc), l ∈ L → ∃ s pm, σ.(sst) !! l = Some s ∧
          mkItem pm (Tagged t) (Some c) ∈ s ∧ pm ≠ Disabled.

  Definition loc_protected_by σ t l c :=
    c ∈ σ.(scs) ∧ (t < σ.(snp))%nat ∧ ∃ stk pm, σ.(sst) !! l = Some stk ∧
      mkItem pm (Tagged t) (Some c) ∈ stk ∧ pm ≠ Disabled.
  Lemma call_set_interp_access M σ c t l :
    call_set_interp M σ →
    call_set_in' M c t l →
    loc_protected_by σ t l c.
  Proof.
    intros Hinterp (M' & HM_some & L & HM'_some & Hin).
    specialize (Hinterp _ _ HM_some) as (? & Hinterp).
    specialize (Hinterp _ _ HM'_some) as (? & Hinterp).
    specialize (Hinterp _ Hin). done.
  Qed.

  Lemma call_set_interp_remove c M σ :
    call_set_interp M σ →
    call_set_interp (delete c M) (state_upd_calls (.∖ {[c]}) σ).
  Proof.
    intros Hinterp c' M' Hsome. destruct (decide (c' = c)) as [-> | Hneq].
    { rewrite lookup_delete_eq in Hsome. done. }
    rewrite lookup_delete_ne in Hsome; last done.
    apply Hinterp in Hsome as (Hin & Hpid).
    split.
    { destruct σ; cbn in *. apply elem_of_difference; split; first done. by apply not_elem_of_singleton. }
    intros t S HS.
    apply Hpid in HS as (Ht & Hlookup). split; first by destruct σ.
    intros l Hl. apply Hlookup in Hl as (s & pm & Hsst & Hs & Hpm).
    exists s, pm. split_and!; [ | done..]. by destruct σ.
  Qed.

  Lemma loc_protected_by_source (sc_rel : scalar → scalar → iProp Σ) Mtag Mt Mcall σ_t σ_s :
    state_rel sc_rel Mtag Mt Mcall σ_t σ_s -∗
    ∀ t l c,
    ⌜loc_protected_by σ_t t l c⌝ -∗
    ⌜loc_protected_by σ_s t l c⌝.
  Proof.
    iIntros "(%Hdom_eq & %Hsst_eq & %Hsnp_eq & %Hsnc_eq & %Hscs_eq & _)".
    iIntros (t l c) "%Hprot". destruct Hprot as (Hc & Ht & (stk & pm & Hstk & Hit & Hpm)).
    iPureIntro. rewrite /loc_protected_by. rewrite Hscs_eq Hsnp_eq Hsst_eq. eauto 8.
  Qed.
End call_defs.

Notation "c '@@' M" := (call_set_is call_name c M) (at level 50).


(** Interpretation for heap assertions under control of tags.
    The interpretation of the tag map and the "heap view" fragments are interlinked.
 *)
Section heap_defs.
  (** The assumption on the location still being valid for tag [t], i.e., [t] not being disabled. *)
  (* Note: That the stack is still there needs to be part of the precondition [bor_state_pre].
    Otherwise, we will not be able to prove reflexivity for deallocation:
      that needs to be able to remove stacks from the state without updating all the ghost state that may still make assumptions about it.
  *)
  Definition bor_state_pre (l : loc) (t : ptr_id) (tk : tag_kind) (σ : state) :=
    match tk with
    | tk_local => True
    | _ => ∃ st pm pro, σ.(sst) !! l = Some st ∧
        mkItem pm (Tagged t) pro ∈ st ∧ pm ≠ Disabled
    end.

  Lemma loc_protected_bor_state_pre l t c σ tk :
    loc_protected_by σ t l c → bor_state_pre l t tk σ.
  Proof.
    intros (_ & _ & (stk & pm & ?)). destruct tk; [| | done]; rewrite /bor_state_pre; eauto.
  Qed.

  Definition bor_state_own (l : loc) (t : ptr_id) (tk : tag_kind) (σ : state) :=
    match tk with
    | tk_local => σ.(sst) !! l = Some ([mkItem Unique (Tagged t) None])
    | tk_unq => ∃ st, σ.(sst) !! l = Some st ∧ ∃ opro st',
        st = mkItem Unique (Tagged t) opro :: st'
    | tk_pub => ∃ st, σ.(sst) !! l = Some st ∧ t ∈ active_SRO st
    end.

  Lemma bor_state_own_some_stack l t tk σ :
    bor_state_own l t tk σ → ∃ stk, σ.(sst) !! l = Some stk.
  Proof. rewrite /bor_state_own. destruct tk; naive_solver. Qed.

  (** Location [l] is controlled by tag [t] at kind [tk] with scalar [sc]. *)
  Definition loc_controlled (l : loc) (t : ptr_id) (tk : tag_kind) (sc : scalar) (σ : state) :=
    (bor_state_pre l t tk σ → bor_state_own l t tk σ ∧ σ.(shp) !! l = Some sc).

  Lemma loc_controlled_local l t sc σ :
    loc_controlled l t tk_local sc σ →
    σ.(sst) !! l = Some [mkItem Unique (Tagged t) None] ∧
    σ.(shp) !! l = Some sc.
  Proof. intros Him. specialize (Him I) as (Hbor & Hmem). split;done. Qed.

  Lemma loc_controlled_unq l t sc s σ :
    loc_controlled l t tk_unq sc σ →
    σ.(sst) !! l = Some s →
    (∃ pm opro, mkItem pm (Tagged t) opro ∈ s ∧ pm ≠ Disabled) →
    (∃ s' op, s = (mkItem Unique (Tagged t) op) :: s') ∧
    σ.(shp) !! l = Some sc.
  Proof.
    intros Him Hstk (pm & opro & Hpm).
    edestruct Him as (Hown & ?). { rewrite /bor_state_pre. eauto. }
    split; last done.
    destruct Hown as (st' & opro' & st'' & Hst' & ->). simplify_eq. eauto.
  Qed.

  Lemma loc_controlled_pub l t sc σ s :
    loc_controlled l t tk_pub sc σ →
    σ.(sst) !! l = Some s →
    (∃ pm opro, mkItem pm (Tagged t) opro ∈ s ∧ pm ≠ Disabled) →
    t ∈ active_SRO s ∧
    σ.(shp) !! l = Some sc.
  Proof.
    intros Him Hst (pm & opro & Hin & Hpm).
    edestruct Him as (Hown & ?). { rewrite /bor_state_pre; eauto 8. }
    split; last done. destruct Hown as (st' & Hst' & Hsro).
    simplify_eq. eauto.
  Qed.

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

  Section local.
  (** Facts about local tags  *)
  Lemma loc_controlled_local_unique l t t' sc sc' σ :
    loc_controlled l t tk_local sc σ →
    loc_controlled l t' tk_local sc' σ →
    t' = t ∧ sc' = sc.
  Proof.
    intros Hcontrol Hcontrol'. specialize (Hcontrol I) as [Hown Hmem].
    specialize (Hcontrol' I) as [Hown' Hmem'].
    split; last by simplify_eq.
    move : Hown Hown'. rewrite /bor_state_own // => -> [=] //.
  Qed.

  Lemma loc_controlled_local_pre l t t' tk' sc σ :
    loc_controlled l t tk_local sc σ →
    bor_state_pre l t' tk' σ →
    tk' = tk_local ∨ t' = t.
  Proof.
    intros [Heq _]%loc_controlled_local.
    destruct tk'; last by eauto.
    - intros (st' &  pm & opro &  Hst & Hin & Hpm).
      move : Hst Hin. rewrite Heq.
      move => [= <-] /list_elem_of_singleton [=]; eauto.
    - intros (st' &  pm & opro &  Hst & Hin & Hpm).
      move : Hst Hin. rewrite Heq.
      move => [= <-] /list_elem_of_singleton [=]; eauto.
  Qed.
  Lemma bor_state_local_own_exclusive l t t' tk' σ :
    bor_state_own l t tk_local σ →
    bor_state_own l t' tk' σ →
    (tk' = tk_unq ∨ tk' = tk_local) ∧ t = t'.
  Proof.
    intros Heq. destruct tk'.
    - move => [st' []]. rewrite Heq => [= <-] //.
    - move => [st' [Heq' [opro [st'' ]]]]. move : Heq'. rewrite Heq => [= <-] [= ->] //; eauto.
    - rewrite /bor_state_own Heq => [=]; eauto.
  Qed.
  Lemma bor_state_unq_own_exclusive l t t' tk' σ :
    bor_state_own l t tk_unq σ →
    bor_state_own l t' tk' σ →
    (tk' = tk_unq ∨ tk' = tk_local) ∧ t = t'.
  Proof.
    intros (stk & Hstk & (opro & stk' & ->)).
    destruct tk'; simpl.
    - intros (stk'' & Hstk'' & Hact). rewrite Hstk in Hstk''. injection Hstk'' as [= <-].
      simpl in Hact. done.
    - intros (stk'' & Hstk'' & (opro' & stk''' & ->)).
      rewrite Hstk'' in Hstk. injection Hstk as [= -> -> ->]. eauto.
    - rewrite Hstk. intros [= -> -> ->]. eauto.
  Qed.

  (* having local ownership of a location is authoritative, in the sense that we can update memory without hurting other tags that control this location. *)
  Lemma loc_controlled_local_authoritative l t t' tk' sc sc' σ f :
    loc_controlled l t tk_local sc (state_upd_mem f σ) →
    loc_controlled l t' tk' sc' σ →
    t ≠ t' →
    loc_controlled l t' tk' sc' (state_upd_mem f σ).
  Proof.
    intros Hcontrol Hcontrol' Hneq [Hown Hmem]%Hcontrol'. split; first done.
    edestruct (bor_state_local_own_exclusive l t t' tk' (state_upd_mem f σ)) as [_ <-]; [apply Hcontrol |..]; done.
  Qed.

  Lemma loc_controlled_protected_authoritative l t t' tk' sc sc' σ f c :
    loc_protected_by (state_upd_mem f σ) t l c →
    loc_controlled l t tk_unq sc (state_upd_mem f σ) →
    loc_controlled l t' tk' sc' σ →
    t ≠ t' →
    loc_controlled l t' tk' sc' (state_upd_mem f σ).
  Proof.
    intros Hprot Hcontrol Hcontrol' Hneq [Hown Hmem]%Hcontrol'. split; first done.
    specialize (loc_protected_bor_state_pre _ _ _ _ tk_unq Hprot) as Hpre.
    apply Hcontrol in Hpre as [Hown' Hmem'].
    edestruct (bor_state_unq_own_exclusive l t t' tk' (state_upd_mem f σ)) as [_ <-]; done.
  Qed.
  End local.

  (** Domain agreement for the two heap views for source and target *)
  Definition dom_agree_on_tag (M_t M_s : gmap (ptr_id * loc) scalar) (t : ptr_id) :=
    (∀ l, is_Some (M_t !! (t, l)) → is_Some (M_s !! (t, l))) ∧
    (∀ l, is_Some (M_s !! (t, l)) → is_Some (M_t !! (t, l))).

  Lemma dom_agree_on_tag_upd_ne_target M_t M_s t t' l sc :
    t ≠ t' →
    dom_agree_on_tag M_t M_s t' →
    dom_agree_on_tag (<[(t, l) := sc]> M_t) M_s t'.
  Proof.
    intros Hneq [Htgt Hsrc]. split => l'' Hsome.
    - apply Htgt. move : Hsome. rewrite lookup_insert_is_Some. by intros [[= -> <-] | [_ ?]].
    - apply lookup_insert_is_Some. right. split; first congruence. by apply Hsrc.
  Qed.
  Lemma dom_agree_on_tag_upd_ne_source M_t M_s t t' l sc :
    t ≠ t' →
    dom_agree_on_tag M_t M_s t' →
    dom_agree_on_tag M_t (<[(t, l) := sc]> M_s) t'.
  Proof.
    intros Hneq [Htgt Hsrc]. split => l'' Hsome.
    - apply lookup_insert_is_Some. right. split; first congruence. by apply Htgt.
    - apply Hsrc. move : Hsome. rewrite lookup_insert_is_Some. by intros [[= -> <-] | [_ ?]].
  Qed.
  Lemma dom_agree_on_tag_upd_target M_t M_s t l sc :
    is_Some (M_t !! (t, l)) →
    dom_agree_on_tag M_t M_s t →
    dom_agree_on_tag (<[(t, l) := sc]> M_t) M_s t.
  Proof.
    intros Hs [Htgt Hsrc]. split => l''.
    - rewrite lookup_insert_is_Some. intros [[= <-] | [_ ?]]; by apply Htgt.
    - intros Hsome. rewrite lookup_insert_is_Some'. right; by apply Hsrc.
  Qed.
  Lemma dom_agree_on_tag_upd_source M_t M_s t l sc :
    is_Some (M_s !! (t, l)) →
    dom_agree_on_tag M_t M_s t →
    dom_agree_on_tag M_t (<[(t, l) := sc]> M_s) t.
  Proof.
    intros Hs [Htgt Hsrc]. split => l''.
    - intros Hsome. rewrite lookup_insert_is_Some'. right; by apply Htgt.
    - rewrite lookup_insert_is_Some. intros [[= <-] | [_ ?]]; by apply Hsrc.
  Qed.
  Lemma dom_agree_on_tag_lookup_target M_t M_s t l :
    dom_agree_on_tag M_t M_s t → is_Some (M_t !! (t, l)) → is_Some (M_s !! (t, l)).
  Proof. intros Hag Hsome. apply Hag, Hsome. Qed.
  Lemma dom_agree_on_tag_lookup_source M_t M_s t l :
    dom_agree_on_tag M_t M_s t → is_Some (M_s !! (t, l)) → is_Some (M_t !! (t, l)).
  Proof. intros Hag Hsome. apply Hag, Hsome. Qed.

  Lemma dom_agree_on_tag_not_elem M_t M_s t :
    (∀ l, M_t !! (t, l) = None) → (∀ l, M_s !! (t, l) = None) →
    dom_agree_on_tag M_t M_s t.
  Proof. intros Ht Hs. split; intros l; rewrite Ht Hs; congruence. Qed.

  Lemma dom_agree_on_tag_difference M1_t M1_s M2_t M2_s t :
    dom_agree_on_tag M1_t M1_s t → dom_agree_on_tag M2_t M2_s t →
    dom_agree_on_tag (M1_t ∖ M2_t) (M1_s ∖ M2_s) t.
  Proof.
    intros [H1a H1b] [H2a H2b]. split; intros l.
    all: rewrite !lookup_difference_is_Some !eq_None_not_Some; naive_solver.
  Qed.

  Lemma dom_agree_on_tag_union M1_t M1_s M2_t M2_s t :
    dom_agree_on_tag M1_t M1_s t → dom_agree_on_tag M2_t M2_s t →
    dom_agree_on_tag (M1_t ∪ M2_t) (M1_s ∪ M2_s) t.
  Proof.
    intros [H1a H1b] [H2a H2b]. split; intros l; rewrite !lookup_union_is_Some; naive_solver.
  Qed.


  (** The main interpretation for tags *)
  Definition tag_interp (M : gmap ptr_id (tag_kind * unit)) (M_t M_s : gmap (ptr_id * loc) scalar) σ_t σ_s : Prop :=
    (∀ (t : ptr_id) tk, M !! t = Some (tk, ()) →
      (* tags are valid *)
      (t < σ_t.(snp))%nat ∧ (t < σ_s.(snp))%nat ∧
      (* at all locations, the values agree, and match the physical state assuming the tag currently has control over the location *)
      (∀ l sc_t, M_t !! (t, l) = Some sc_t → loc_controlled l t tk sc_t σ_t) ∧
      (∀ l sc_s, M_s !! (t, l) = Some sc_s → loc_controlled l t tk sc_s σ_s) ∧
      dom_agree_on_tag M_t M_s t) ∧
    (∀ (t : ptr_id) (l : loc), is_Some (M_t !! (t, l)) → is_Some (M !! t)) ∧
    (∀ (t : ptr_id) (l : loc), is_Some (M_s !! (t, l)) → is_Some (M !! t)).
End heap_defs.


Notation "p '$$' tk" := (tkmap_elem tag_name p tk ()) (at level 50).

Definition tk_to_frac (tk : tag_kind) :=
  match tk with
  | tk_pub => DfracDiscarded
  | _ => DfracOwn 1
  end.
Notation "l '↦t[' tk ']{' t } sc" := (ghost_map_elem heap_view_target_name (t, l) (tk_to_frac tk) sc)
  (at level 20, format "l  ↦t[ tk ]{ t }  sc") : bi_scope.
Notation "l '↦s[' tk ']{' t } sc" := (ghost_map_elem heap_view_source_name (t, l) (tk_to_frac tk) sc)
  (at level 20, format "l  ↦s[ tk ]{ t }  sc") : bi_scope.


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
    pub_cid_interp (mkState σ_t.(shp) σ_t.(sst) (σ_t.(scs) ∖ {[ c ]}) σ_t.(snp) σ_t.(snc))
      (mkState σ_s.(shp) σ_s.(sst) (σ_s.(scs) ∖ {[ c ]}) σ_s.(snp) σ_s.(snc)).
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
    A tag [t] is tainted for a location [l] when invariantly, the stack for [l] can never contain
     an item tagged with [t] again. *)

  Definition tag_tainted_for (t : ptr_id) (l : loc) :=
    ghost_map_elem tainted_tags_name (t, l) DfracDiscarded tt.
  (* tag [t] is not in [l]'s stack, and can never be in that stack again *)
  Definition tag_tainted_interp (σ_s : state) : iProp Σ :=
    ∃ (M : gmap (ptr_id * loc) unit), ghost_map_auth_frac tainted_tags_name 1 M ∗
      ∀ (t : ptr_id) (l : loc), ⌜is_Some (M !! (t, l))⌝ -∗
        ⌜(t < σ_s.(snp))%nat⌝ ∗
        (* we have a persistent element here to remove sideconditions from the insert lemma *)
        tag_tainted_for t l ∗
        ⌜∀ (stk : stack) (it : item), σ_s.(sst) !! l = Some stk → it ∈ stk →
          tg it ≠ Tagged t ∨ perm it = Disabled⌝.

  (* the result of a read in the target: either the tag was invalid, and it now must be invalid for the source, too,
      or the result [v_t'] agrees with what we expected to get ([v_t]). *)
  Definition deferred_read (v_t v_t' : value) l t : iProp Σ :=
    (∃ i : nat, ⌜(i < length v_t)%nat ∧ length v_t = length v_t'⌝ ∗ tag_tainted_for t (l +ₗ i)) ∨ ⌜v_t' = v_t⌝.

  Lemma tag_tainted_interp_insert σ_s t l :
    (t < σ_s.(snp))%nat →
    (∀ (stk : stack) (it : item), σ_s.(sst) !! l = Some stk → it ∈ stk → tg it ≠ Tagged t ∨ perm it = Disabled) →
    tag_tainted_interp σ_s ==∗
    tag_tainted_interp σ_s ∗ tag_tainted_for t l.
  Proof.
    iIntros (Ht Hnot_in) "(%M & Hauth & #Hinterp)".
    destruct (M !! (t, l)) as [[] | ] eqn:Hlookup.
    - iModIntro. iPoseProof ("Hinterp" $! t l with "[]") as "(_ & $ & _)"; first by eauto.
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
    ⌜(t < σ_s.(snp))%nat⌝ ∗
    ⌜∀ (stk : stack) (it : item), σ_s.(sst) !! l = Some stk → it ∈ stk → tg it ≠ Tagged t ∨ perm it = Disabled⌝.
  Proof.
    iIntros "Helem (%M & Hauth & Hinterp)".
    iPoseProof (ghost_map_lookup with "Hauth Helem") as "%Hlookup".
    iPoseProof ("Hinterp" $! t l with "[]") as "(% & _ & %)"; by eauto.
  Qed.

  Definition is_fresh_tag σ tg :=
    match tg with
    | Untagged => True
    | Tagged t => σ.(snp) ≤ t
    end.
  Lemma tag_tainted_interp_preserve σ_s σ_s' :
    σ_s'.(snp) ≥ σ_s.(snp) →
    (∀ l stk', σ_s'.(sst) !! l = Some stk' → ∀ it, it ∈ stk' →
      is_fresh_tag σ_s it.(tg) ∨ it.(perm) = Disabled ∨
        ∃ stk, σ_s.(sst) !! l = Some stk ∧ it ∈ stk) →
    tag_tainted_interp σ_s -∗ tag_tainted_interp σ_s'.
  Proof.
    iIntros (Hge Hupd) "(%M & Hauth & Hinterp)".
    iExists M. iFrame "Hauth". iIntros (t l Hsome).
    iDestruct ("Hinterp" $! t l with "[//]") as "(%Hlt & $ & %Hsst)".
    iSplit; iPureIntro; first lia.
    intros stk' it Hstk' Hit.
    specialize (Hupd _ _ Hstk' _ Hit) as [Hfresh | [Hdisabled | (stk & Hstk & Hit')]].
    - left. destruct (tg it) as [t' | ]; last done. intros [= ->].
      simpl in Hfresh. lia.
    - right; done.
    - eapply Hsst; done.
  Qed.

  Lemma tag_tainted_interp_tagged_sublist σ_s σ_s' :
    σ_s'.(snp) ≥ σ_s.(snp) →
    (∀ l stk', σ_s'.(sst) !! l = Some stk' →
      ∃ stk, σ_s.(sst) !! l = Some stk ∧
        tagged_sublist stk' stk) →
    tag_tainted_interp σ_s -∗ tag_tainted_interp σ_s'.
  Proof.
    iIntros (Hge Hupd). iApply tag_tainted_interp_preserve; first done.
    intros l stk' Hstk' it Hit.
    destruct (Hupd _ _ Hstk') as (stk & Hstk & Hsubl).
    destruct (Hsubl _ Hit) as (it' & Hit' & Htg & Hprot & Hperm).
    destruct (decide (perm it = Disabled)) as [ | Hperm'%Hperm]; first by eauto.
    right; right. exists stk. split; first done.
    destruct it, it'; simpl in *; simplify_eq. done.
  Qed.

  Lemma tag_tainted_interp_retag σ_s c l old rk pk T new α' nxtp' :
    retag σ_s.(sst) σ_s.(snp) σ_s.(scs) c l old rk pk T = Some (new, α', nxtp') →
    tag_tainted_interp σ_s -∗ tag_tainted_interp (mkState σ_s.(shp) α' σ_s.(scs) nxtp' σ_s.(snc)).
  Proof.
    iIntros (Hretag).
    iApply (tag_tainted_interp_preserve); simpl.
    { specialize (retag_change_nxtp _ _ _ _ _ _ _ _ _ _ _ _ Hretag). lia. }
    intros l' stk' Hstk' it Hit.
    specialize (retag_item_in _ _ _ _ _ _ _ _ _ _ _ _ Hretag l' stk') as Ht.
    destruct (decide (perm it = Disabled)) as [Hdisabled | Hndisabled]; first by eauto.
    destruct (tg it) as [t | ] eqn:Htg; last by (left; done).
    destruct (decide (t < σ_s.(snp))%nat) as [Hlt | Hnlt].
    - right; right. eapply (Ht t it); done.
    - left. simpl. lia.
  Qed.

  Lemma tag_tainted_interp_alloc σ l n :
    let nt := Tagged σ.(snp) in
    tag_tainted_interp σ -∗ tag_tainted_interp (mkState (init_mem l n σ.(shp)) (init_stacks σ.(sst) l n nt) σ.(scs) (S σ.(snp)) σ.(snc)).
  Proof.
    intros nt. iIntros "Htainted".
    iApply (tag_tainted_interp_preserve σ with "Htainted"). { simpl. lia. }
    intros l' stk' Hstk' it Hit.
    specialize (init_stacks_lookup_case _ _ _ _ _ _ Hstk') as [(Hstk'' & Hi) | (i & Hi & ->)].
    + right. right. eauto.
    + left. simpl. move : Hstk'. rewrite (proj1 (init_stacks_lookup _ _ _ _)); last done.
      intros [= <-]. move : Hit. rewrite list_elem_of_singleton => -> /=. lia.
  Qed.
End tainted_tags.


Section state_interp.
  Context `{bor_stateGS Σ} (sc_rel : scalar → scalar → iProp Σ).
  (** The main combined interpretation for the borrow semantics *)

  (* Ownership of the authoritative parts. *)
  Definition bor_auth (M_call : gmap call_id (gmap ptr_id (gset loc))) (M_tag : gmap ptr_id (tag_kind * unit)) (M_t M_s : gmap (ptr_id * loc) scalar) : iProp Σ :=
    ghost_map_auth_frac call_name 1 M_call ∗
    tkmap_auth tag_name 1 M_tag ∗
    ghost_map_auth_frac heap_view_target_name 1 M_t ∗
    ghost_map_auth_frac heap_view_source_name 1 M_s.

  Definition bor_interp (σ_t : state) (σ_s : state) : iProp Σ :=
  (* since multiple parts of the interpretation need access to these maps,
    we own the authoritative parts here and not in the interpretations below *)
   ∃ (M_call : gmap call_id (gmap ptr_id (gset loc)))
     (M_tag : gmap ptr_id (tag_kind * unit))
     (M_t M_s : gmap (ptr_id * loc) scalar),
    bor_auth M_call M_tag M_t M_s ∗

    tag_tainted_interp σ_s ∗
    pub_cid_interp σ_t σ_s ∗

    state_rel sc_rel M_tag M_t M_call σ_t σ_s ∗
    (* due to the [state_rel], enforcing this on [σ_t] also does the same for [σ_s] *)
    ⌜call_set_interp M_call σ_t⌝ ∗
    ⌜tag_interp M_tag M_t M_s σ_t σ_s⌝ ∗

    ⌜state_wf σ_s⌝ ∗
    ⌜state_wf σ_t⌝.

  Lemma bor_interp_get_pure σ_t σ_s :
    bor_interp σ_t σ_s -∗ ⌜σ_s.(sst) = σ_t.(sst) ∧ σ_s.(snp) = σ_t.(snp) ∧
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


(** Array generalizes pointsto connectives to lists of scalars *)
Definition array_tag `{!bor_stateGS Σ} γh (t : ptr_id) (l : loc) (dq : dfrac) (scs : list scalar) : iProp Σ :=
  ([∗ list] i ↦ sc ∈ scs, ghost_map_elem γh (t, l +ₗ i) dq sc)%I.
Notation "l '↦t∗[' tk ']{' t } scs" := (array_tag heap_view_target_name t l (tk_to_frac tk) scs)
  (at level 20, format "l  ↦t∗[ tk ]{ t }  scs") : bi_scope.
Notation "l '↦s∗[' tk ']{' t } scs" := (array_tag heap_view_source_name t l (tk_to_frac tk) scs)
  (at level 20, format "l  ↦s∗[ tk ]{ t }  scs") : bi_scope.


(** [array_tag_map] is the main way we interface with [array_tag] by having a representation of
  the stored memory fragment. *)
Fixpoint array_tag_map (l : loc) (t : ptr_id) (v : list scalar) : gmap (ptr_id * loc) scalar :=
  match v with
  | [] => ∅
  | sc :: v' => <[(t, l) := sc]> (array_tag_map (l +ₗ 1) t v')
  end.
Lemma array_tag_map_lookup1 l t v t' l' :
  is_Some (array_tag_map l t v !! (t', l')) →
  t' = t ∧ l.1 = l'.1 ∧ l.2 ≤ l'.2 < l.2 + length v.
Proof.
  induction v as [ | sc v IH] in l |-*.
  - simpl. rewrite lookup_empty. intros [? [=]].
  - simpl. move => [sc0 ]. rewrite lookup_insert_Some. move => [[[= <- <-] Heq] | [Hneq Ht]]; first lia.
    move : (IH (l +ₗ 1) ltac:(eauto)). destruct l. simpl. lia.
Qed.
Lemma array_tag_map_lookup2 l t v t' l' :
  is_Some (array_tag_map l t v !! (t', l')) →
  t' = t ∧ ∃ i, (i < length v)%nat ∧ l' = l +ₗ i.
Proof.
  intros (-> & H1 & H2)%array_tag_map_lookup1.
  split; first done. exists (Z.to_nat (l'.2 - l.2)).
  destruct l, l';  rewrite /shift_loc; simpl in *. split.
  - lia.
  - apply pair_equal_spec. split; lia.
Qed.

Lemma array_tag_map_lookup_Some l t v (i : nat) :
  (i < length v)%nat →
  array_tag_map l t v !! (t, l +ₗ i) = v !! i.
Proof.
  induction v as [ | sc v IH] in l, i |-*.
  - simpl. lia.
  - simpl. intros Hi. destruct i as [ | i].
    + rewrite shift_loc_0_nat. rewrite lookup_insert_eq. done.
    + rewrite lookup_insert_ne; first last. { destruct l; simpl; intros [= ?]; lia. }
      move : (IH (l +ₗ 1) i ltac:(lia)). rewrite shift_loc_assoc.
      by replace (Z.of_nat (S i)) with (1 + i) by lia.
Qed.

Lemma array_tag_map_lookup_None t t' l v :
  t ≠ t' → ∀ l', array_tag_map l t v !! (t', l') = None.
Proof.
  intros Hneq l'. destruct (array_tag_map l t v !! (t', l')) eqn:Harr; last done.
  specialize (array_tag_map_lookup1 l t v t' l' ltac:(eauto)) as [Heq _]; congruence.
Qed.

Lemma array_tag_map_lookup_None' l t v l' :
  (∀ i:nat, (i < length v)%nat → l +ₗ i ≠ l') →
  array_tag_map l t v !! (t, l') = None.
Proof.
  intros Hneq. destruct (array_tag_map _ _ _ !! _) eqn:Heq; last done. exfalso.
  specialize (array_tag_map_lookup2 l t v t l' ltac:(eauto)) as [_ (i & Hi & ->)].
  eapply Hneq; last reflexivity. done.
Qed.

Lemma array_tag_map_lookup_None2 l t t' v l' :
  array_tag_map l t v !! (t', l') = None →
  t ≠ t' ∨ (∀ i: nat, (i < length v)%nat → l +ₗ i ≠ l').
Proof.
  induction v as [ | sc v IH] in l |-*; simpl.
  - intros _. right. intros i Hi; lia.
  - rewrite lookup_insert_None. intros [Ha%IH Hneq].
    destruct Ha; first by eauto. move: Hneq. rewrite pair_equal_spec not_and_l.
    intros [ ? | Hneq]; first by eauto.
    right. intros i Hi. destruct i as [ | i].
    + rewrite shift_loc_0_nat. done.
    + replace (Z.of_nat (S i)) with (1 + i)%Z by lia. rewrite -shift_loc_assoc.
      eauto with lia.
Qed.

Lemma dom_agree_on_tag_array_tag_map l t v_t v_s :
  length v_t = length v_s →
  dom_agree_on_tag (array_tag_map l t v_t) (array_tag_map l t v_s) t.
Proof.
  intros Hlen. split; intros l'.
  - intros (_ & (i & Hi & ->))%array_tag_map_lookup2. rewrite array_tag_map_lookup_Some; last lia.
    apply lookup_lt_is_Some_2. lia.
  - intros (_ & (i & Hi & ->))%array_tag_map_lookup2. rewrite array_tag_map_lookup_Some; last lia.
    apply lookup_lt_is_Some_2. lia.
Qed.

(** Array update lemmas for the heap views *)
Lemma ghost_map_array_tag_lookup `{!bor_stateGS Σ} (γh : gname) (q : Qp) (M : gmap (ptr_id * loc) scalar) (v : list scalar) (t : ptr_id) (l : loc) dq :
  ghost_map_auth_frac γh q M -∗
  ([∗ list] i ↦ sc ∈ v, ghost_map_elem γh (t, l +ₗ i) dq sc) -∗
  ⌜∀ i : nat, (i < length v)%nat → M !! (t, l +ₗ i) = v !! i⌝.
Proof.
  iIntros "Hauth Helem". iInduction v as [ |sc v ] "IH" forall (l) "Hauth Helem".
  - iPureIntro; cbn. lia.
  - rewrite big_sepL_cons. iDestruct "Helem" as "[Hsc Hscs]".
    iPoseProof (ghost_map_lookup with "Hauth Hsc") as "%Hl".
    iDestruct ("IH" $! (l +ₗ 1) with "Hauth [Hscs]") as "%IH".
    { iApply (big_sepL_mono with "Hscs"). intros i sc' Hs. cbn. rewrite shift_loc_assoc.
      replace (Z.of_nat $ S i) with (1 + i)%Z by lia. done. }
    iPureIntro. intros i Hle. destruct i as [|i]; first done.
    replace (Z.of_nat $ S i) with (1 + i)%Z by lia. cbn in *. rewrite -(IH i); last lia.
    by rewrite shift_loc_assoc.
Qed.

Lemma array_tag_map_union_commute (l : loc) (sc : scalar) (t : ptr_id) (v : list scalar) (M : gmap (ptr_id * loc) scalar) (i : Z) :
  i > 0 →
  <[(t, l) := sc]> (array_tag_map (l +ₗ i) t v) ∪ M = array_tag_map (l +ₗ i) t v ∪ (<[(t, l) := sc]> M).
Proof.
  intros Hi. induction v as [ | sc' v IH] in l, i, Hi |-*; simpl.
  - rewrite insert_union_singleton_l. rewrite -map_union_assoc. rewrite !map_empty_union.
    by rewrite insert_union_singleton_l.
  - rewrite insert_insert_ne. 2: { intros [= Heq]. destruct l; simpl in *. injection Heq. lia. }
    rewrite shift_loc_assoc. rewrite -insert_union_l. rewrite (IH l (i + 1)%Z); last lia.
    rewrite -insert_union_l. done.
Qed.

Lemma ghost_map_array_tag_update `{!bor_stateGS Σ} (γh : gname) (M : gmap (ptr_id * loc) scalar) (v v' : list scalar) (t : ptr_id) (l : loc) :
  length v = length v' →
  ghost_map_auth_frac γh 1 M -∗
  ([∗ list] i ↦ sc ∈ v, ghost_map_elem γh (t, l +ₗ i) (DfracOwn 1) sc) ==∗
  ([∗ list] i ↦ sc' ∈ v', ghost_map_elem γh (t, l +ₗ i) (DfracOwn 1) sc') ∗
  ghost_map_auth_frac γh 1 (array_tag_map l t v' ∪ M).
Proof.
  iIntros (Hlen) "Hauth Helems". iInduction v as [ | sc v ] "IH" forall (l v' M Hlen) "Hauth Helems".
  - destruct v'; simpl in Hlen; last done. rewrite big_sepL_nil.
    simpl. rewrite map_empty_union. eauto.
  - rewrite big_sepL_cons. iDestruct "Helems" as "[Hsc Helems]".
    destruct v' as [ | sc' v']; simpl in Hlen; first done.
    iMod (ghost_map_update sc' with "Hauth Hsc") as "[Hauth Hsc]".
    iMod ("IH" $! (l +ₗ 1) v' (<[(t, l +ₗ 0%nat):=sc']> M) with "[] Hauth [Helems]") as "[Helems Hauth]";
      first (iPureIntro; lia).
    { iApply (big_sepL_mono with "Helems"). intros i sc'' Hs. cbn. rewrite shift_loc_assoc.
      replace (Z.of_nat $ S i) with (1 + i)%Z by lia. done. }
    iModIntro. simpl. iFrame "Hsc".
    iSplitL "Helems".
    { iApply (big_sepL_mono with "Helems"). intros i sc'' Hs. cbn. rewrite shift_loc_assoc.
      replace (Z.of_nat $ S i) with (1 + i)%Z by lia. done. }
    enough (array_tag_map (l +ₗ 1) t v' ∪ <[(t, l +ₗ 0%nat):=sc']> M = <[(t, l):=sc']> (array_tag_map (l +ₗ 1) t v') ∪ M) as ->;
      first done.
    rewrite array_tag_map_union_commute; last done. rewrite shift_loc_0_nat. done.
Qed.

Lemma ghost_map_array_tag_insert `{!bor_stateGS Σ} (γh : gname) (M : gmap (ptr_id * loc) scalar) (v : list scalar) (t : ptr_id) (l : loc) :
  (∀ i : nat, (i < length v)%nat → M !! (t, l +ₗ i) = None) →
  ghost_map_auth_frac γh 1 M  ==∗
  ([∗ list] i ↦ sc ∈ v, ghost_map_elem γh (t, l +ₗ i) (DfracOwn 1) sc) ∗
  ghost_map_auth_frac γh 1 (array_tag_map l t v ∪ M).
Proof.
  iIntros (Hnone) "Hauth". iInduction v as [ | sc v ] "IH" forall (M l Hnone) "Hauth".
  - rewrite big_sepL_nil. iModIntro. rewrite map_empty_union. iFrame.
  - rewrite big_sepL_cons.
    iMod ("IH" $! M (l +ₗ 1) with "[] Hauth") as "[Helems Hauth]".
    { iPureIntro. intros i Hi. rewrite shift_loc_assoc. replace (1 + i)%Z with (Z.of_nat (S i)) by lia. apply Hnone.
      simpl; lia.
    }
    iMod (ghost_map_insert (t, l +ₗ 0%nat) sc with "Hauth") as "[Hauth Helem]".
    { rewrite lookup_union_None; split.
      - apply array_tag_map_lookup_None'. intros i Hi. destruct l; intros [= ?]. lia.
      - apply Hnone. simpl; lia.
    }
    iModIntro. iFrame "Helem". rewrite shift_loc_0_nat. simpl. rewrite insert_union_l. iFrame "Hauth".
    iApply (big_sepL_mono with "Helems"). intros i sc'' Hs. cbn. rewrite shift_loc_assoc.
    replace (Z.of_nat $ S i) with (1 + i)%Z by lia. done.
Qed.

Lemma ghost_map_array_tag_delete `{!bor_stateGS Σ} (γh : gname) (M : gmap (ptr_id * loc) scalar) (v : list scalar) (t : ptr_id) (l : loc) :
  ghost_map_auth_frac γh 1 M -∗
  ([∗ list] i ↦ sc ∈ v, ghost_map_elem γh (t, l +ₗ i) (DfracOwn 1) sc) ==∗
  ghost_map_auth_frac γh 1 (M ∖ array_tag_map l t v).
Proof.
  iIntros "Hauth Helems".
  iApply (ghost_map_delete_big (array_tag_map l t v) with "Hauth [Helems]").
  iInduction v as [ | sc v] "IH" forall (l); first done.
  simpl. iApply big_sepM_insert.
  { destruct (_ !! _) eqn:Heq; last done.
    specialize (array_tag_map_lookup2 (l +ₗ 1) t v t l ltac:(eauto)) as [_ (i & _ & Hl)].
    destruct l. injection Hl. lia.
  }
  rewrite shift_loc_0_nat. iDestruct "Helems" as "[$ Helems]".
  iApply "IH". iApply (big_sepL_mono with "Helems").
  iIntros (i sc' Hi). simpl.
  rewrite shift_loc_assoc. replace (Z.of_nat (S i)) with (1 + i) by lia; done.
Qed.

Lemma ghost_map_array_tag_tk `{!bor_stateGS Σ} (γh : gname) (v : list scalar) (t : ptr_id) (l : loc) tk :
  ([∗ list] i ↦ sc ∈ v, ghost_map_elem γh (t, l +ₗ i) (DfracOwn 1) sc) ==∗
  ([∗ list] i ↦ sc ∈ v, ghost_map_elem γh (t, l +ₗ i) (tk_to_frac tk) sc).
Proof.
  destruct tk; cbn; [ | by eauto | by eauto].
  iInduction v as [| sc v] "IH" forall (l); first by eauto.
  rewrite !big_sepL_cons. iIntros "[Hh Hr]".
  iMod (ghost_map_elem_persist with "Hh") as "$".
  iMod ("IH" $! (l +ₗ 1) with "[Hr]") as "Hr".
  - iApply (big_sepL_mono with "Hr"). intros i sc' Hs. simpl. rewrite shift_loc_assoc.
    by replace (Z.of_nat (S i)) with (1 + i) by lia.
  - iModIntro.
    iApply (big_sepL_mono with "Hr"). intros i sc' Hs. simpl. rewrite shift_loc_assoc.
    by replace (Z.of_nat (S i)) with (1 + i) by lia.
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
          * and the locations are related (i.e.: if tagged, then it is public)
        *)
        ⌜l1 = l2⌝ ∗
        (⌜p1 = Untagged⌝ ∗ ⌜p2 = Untagged⌝ ∨
        (∃ t1 t2, ⌜p1 = Tagged t1⌝ ∗ ⌜p2 = Tagged t2⌝ ∗
        ⌜t1 = t2⌝ ∗
        t1 $$ tk_pub))
        (* what the [tk_pub] gives us is that the locations store related values *)
    | ScCallId c, ScCallId c' => ⌜c = c'⌝ ∗ pub_cid c
    (* [ScPoison] can be refined by anything *)
    | _ , ScPoison => True
    | _, _ => False
    end.

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
    sc_rel sc_t (ScPtr l_s t_s) ⊢ ⌜sc_t = ScPtr l_s t_s⌝ ∗ (if t_s is Tagged t then t $$ tk_pub else True).
  Proof.
    iIntros "Hrel". destruct sc_t; [done | done | | done | done ].
    iDestruct "Hrel" as "(-> & [[-> ->] | (% & %t & -> & -> & -> & ?)])"; iFrame; done.
  Qed.
  Lemma sc_rel_fnptr_source sc_t fn :
    sc_rel sc_t (ScFnPtr fn) ⊢ ⌜sc_t = ScFnPtr fn⌝.
  Proof.
    iIntros "Hrel". destruct sc_t; [done | done | done | | done].
    by iDestruct "Hrel" as "->".
  Qed.
  Lemma sc_rel_int_source sc_t z :
    sc_rel sc_t (ScInt z) ⊢ ⌜sc_t = ScInt z⌝.
  Proof.
    iIntros "Hrel". destruct sc_t; [ done | | done..].
    by iDestruct "Hrel" as "->".
  Qed.
  Lemma sc_rel_cid_source sc_t c :
    sc_rel sc_t (ScCallId c) ⊢ ⌜sc_t = ScCallId c⌝ ∗ pub_cid c.
  Proof. iIntros "Hrel"; destruct sc_t; [done.. | ]. by iDestruct "Hrel" as "[-> $]". Qed.

  Lemma sc_rel_poison_target sc_s :
    sc_rel (ScPoison) sc_s -∗ ⌜sc_s = ScPoison⌝.
  Proof. iIntros "Hrel". destruct sc_s; done. Qed.

  Lemma sc_rel_ptr_target sc_s l_t t_t :
    sc_rel (ScPtr l_t t_t) sc_s ⊢ (⌜sc_s = ScPtr l_t t_t⌝ ∗ (if t_t is Tagged t then t $$ tk_pub else True)) ∨ ⌜sc_s = ScPoison⌝.
  Proof.
    iIntros "Hrel". destruct sc_s; [ by iRight | done | | done | done ].
    iDestruct "Hrel" as "(-> & [[-> ->] | (% & %t & -> & -> & -> & ?)])"; iLeft; iFrame; done.
  Qed.
  Lemma sc_rel_fnptr_target sc_s fn :
    sc_rel (ScFnPtr fn) sc_s ⊢ ⌜sc_s = ScFnPtr fn⌝ ∨ ⌜sc_s = ScPoison⌝.
  Proof.
    iIntros "Hrel". destruct sc_s; [by iRight | done | done | | done].
    iLeft. by iDestruct "Hrel" as "->".
  Qed.
  Lemma sc_rel_int_target sc_s z :
    sc_rel (ScInt z) sc_s ⊢ ⌜sc_s = ScInt z⌝ ∨ ⌜sc_s = ScPoison⌝.
  Proof.
    iIntros "Hrel". destruct sc_s; [ by iRight | | done..].
    iLeft. by iDestruct "Hrel" as "->".
  Qed.
  Lemma sc_rel_cid_target sc_s c :
    sc_rel (ScCallId c) sc_s ⊢ (⌜sc_s = ScCallId c⌝ ∗ pub_cid c) ∨ ⌜sc_s = ScPoison⌝.
  Proof. iIntros "Hrel"; destruct sc_s; [ by iRight | done.. | ]. iLeft. by iDestruct "Hrel" as "[-> $]". Qed.

  Lemma rrel_place_source r_t l_s t_s T :
    rrel r_t (PlaceR l_s t_s T) ⊢
    ⌜r_t = PlaceR l_s t_s T⌝ ∗ (if t_s is Tagged t then t $$ tk_pub else True).
  Proof.
    iIntros "Hrel".
    destruct r_t as [ | l_t t' T']; first done. iDestruct "Hrel" as "(#H & ->)".
    iDestruct (sc_rel_ptr_source with "H") as "[%Heq Htag]".
    injection Heq as [= -> ->]. eauto.
  Qed.
  Lemma rrel_value_source r_t v_s :
    rrel r_t (ValR v_s) ⊢
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
    value_rel v_t [sc_s] ⊢ ∃ sc_t, ⌜v_t = [sc_t]⌝ ∗ sc_rel sc_t sc_s.
  Proof.
    iIntros "Hv". iPoseProof (value_rel_length with "Hv") as "%Hlen".
    destruct v_t as [ | sc_t []]; [done | | done ].
    iExists sc_t. iSplitR "Hv"; first done. iRevert "Hv". rewrite /value_rel big_sepL2_singleton. eauto.
  Qed.

  Lemma rrel_singleton_source r_t sc_s :
    rrel r_t (ValR [sc_s]) ⊢
    ∃ sc_t, ⌜r_t = ValR [sc_t]⌝ ∗ sc_rel sc_t sc_s.
  Proof.
    rewrite rrel_value_source. setoid_rewrite value_rel_singleton_source.
    iDestruct 1 as (v_t -> sc_t ->) "?". eauto.
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
    match tg with | Tagged t => t $$ tk_pub | Untagged => True end
    ⊢ sc_rel (ScPtr l tg) (ScPtr l tg).
  Proof.
    iIntros "Hr". iSplit; [done|].
    case_match; [|eauto]. iRight. eauto with iFrame.
  Qed.
  Lemma value_rel_ptr l tg :
    match tg with | Tagged t => t $$ tk_pub | Untagged => True end
    ⊢ value_rel [ScPtr l tg] [ScPtr l tg].
  Proof. by rewrite (sc_rel_ptr l) value_rel_singleton. Qed.

  Lemma rrel_place l tg T :
    match tg with | Tagged t => t $$ tk_pub | Untagged => True end
    ⊢ rrel (PlaceR l tg T) (PlaceR l tg T).
  Proof. rewrite (sc_rel_ptr l) rrel_sc_rel. eauto. Qed.

  Lemma value_rel_app v_t1 v_s1 v_t2 v_s2 :
    value_rel v_t1 v_s1 -∗ value_rel v_t2 v_s2 -∗ value_rel (v_t1 ++ v_t2) (v_s1 ++ v_s2).
  Proof.
    iIntros "Hv1 Hv2".
    iDestruct (value_rel_length with "Hv1") as %EqL.
    rewrite /value_rel. iApply (big_sepL2_app with "Hv1 Hv2").
  Qed.
End val_rel.

(** Simulation / relation final setup *)
Class sborGS (Σ: gFunctors) := SBorGS {
  (* program assertions, backs up [has_prog] assertions so we know which
  function name has which code. *)
  sborG_gen_progG :: gen_sim_progGS string (string*expr) (string*expr) Σ;
  sborG_stateG :: bor_stateGS Σ;
}.
Definition sborΣ : gFunctors := (#[bor_stateΣ; gen_progΣ string (string*expr)]).
Class sborGpreS (Σ: gFunctors) := SBorGpreS {
  sbor_pre_stateG :: bor_stateGpreS Σ | 10;
  sbor_pre_progG :: gen_progGpreS Σ string (string*expr) | 10;
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
  iMod (ghost_map_alloc (∅ : gmap call_id (gmap ptr_id (gset loc)))) as (γcall) "[Hcall_auth _]".
  iMod (tkmap_alloc (∅ : gmap ptr_id (tag_kind * unit))) as (γtag) "[Htag_auth _]".
  iMod (ghost_map_alloc (∅ : gmap (ptr_id * loc) scalar)) as (γtgt) "[Hheap_tgt_auth _]".
  iMod (ghost_map_alloc (∅ : gmap (ptr_id * loc) scalar)) as (γsrc) "[Hheap_src_auth _]".
  iMod (ghost_map_alloc (∅ : gmap ptr_id unit)) as (γpub_call) "[Hpub_call_auth _]".
  iMod (ghost_map_alloc (∅ : gmap (ptr_id * loc) unit)) as (γtainted) "[Htainted_auth _]".
  iMod (gen_sim_prog_init P_t P_s) as (?) "[#Hprog_t #Hprog_s]".
  iModIntro.
  set (bor := BorStateGS _ _ γcall _ γtag _ γtgt γsrc _ γpub_call _ γtainted).
  iExists (SBorGS _ _ _).
  iSplitL; last iSplit; last iSplit.
  - simpl. iFrame "Hprog_t Hprog_s".
    iExists ∅, ∅, ∅, ∅.
    iFrame "Hcall_auth Htag_auth Hheap_tgt_auth Hheap_src_auth".
    iSplitL "Htainted_auth".
    { iFrame. iIntros (? ?). rewrite lookup_empty. iIntros ([? [=]]). }
    iSplitL "Hpub_call_auth".
    { iFrame. iApply big_sepM_empty. done. }
    iSplitL.
    { do 5 (iSplitL; first done). iIntros (l Hl). exfalso.
      move : Hl. rewrite lookup_empty. intros [? [=]]. }
    iSplitL.
    { iPureIntro. intros c M'. rewrite lookup_empty. congruence. }
    iSplitL.
    { iPureIntro. split_and!.
      - intros t tk. rewrite lookup_empty. congruence.
      - intros t l. rewrite lookup_empty. intros [? [=]].
      - intros t l. rewrite lookup_empty. intros [? [=]].
    }
    iSplit; iPureIntro; apply wf_init_state.
  - by iApply has_prog_all_funs.
  - by iApply has_prog_all_funs.
  - rewrite /progs_are /=. iIntros "!#" (P_t' P_s' σ_t' σ_s' T_s') "(#Hprog_t2 & #Hprog_s2 & _)".
    iDestruct (has_prog_agree with "Hprog_t Hprog_t2") as %->.
    iDestruct (has_prog_agree with "Hprog_s Hprog_s2") as %->.
    done.
Qed.
