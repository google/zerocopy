(* Derived from lambda-rust heap.v*)
From stdpp Require Import coPset.
From iris.algebra Require Import big_op gmap frac agree numbers.
From iris.algebra Require Import csum excl auth cmra_big_op.
From iris.bi Require Import fractional.
From iris.base_logic Require Export lib.own.
From iris.base_logic.lib Require Import ghost_map.
From iris.proofmode Require Export proofmode.
From simuliris.simulang Require Export lang.

Import uPred.

Definition lock_stateR : cmra :=
  csumR (exclR unitO) natR.

Definition heapUR : ucmra :=
  gmapUR loc (prodR (prodR fracR lock_stateR) (agreeR valO)).

Class heapG Σ := HeapG {
  heap_inG :: inG Σ (authR heapUR);
  heap_block_size_inG :: ghost_mapG Σ loc (option nat);
  heap_globals_inG :: inG Σ (agreeR (leibnizO (gset string)));
}.
Definition heapΣ := #[GFunctor (authR heapUR); ghost_mapΣ loc (option nat); GFunctor (agreeR (leibnizO (gset string)))].

Global Instance subG_heapΣ Σ :
  subG heapΣ Σ → heapG Σ.
Proof. solve_inG. Qed.

Record heap_names := {
 heap_name : gname;
 heap_block_size_name : gname;
 heap_globals_name : gname;
}.

Definition to_lock_stateR (x : lock_state) : lock_stateR :=
  match x with RSt n => Cinr n | WSt => Cinl (Excl ()) end.
Definition to_heap : gmap loc (lock_state * val) → heapUR :=
  fmap (λ v, (1%Qp, to_lock_stateR (v.1), to_agree (v.2))).
Definition heap_block_size_rel (σ : state) (hF : gmap loc (option nat)) : Prop :=
  ∀ b i o, hF !! Loc b i = Some o →
   (if b is DynBlock b' then b' ∈ σ.(used_dyn_blocks) else True) ∧
   i = 0 ∧
   0 < default 1 o ∧
   ∀ i, is_Some (σ.(heap) !! Loc b i) ↔ (0 ≤ i < default O o)%Z.

Section definitions.
  Context `{!heapG Σ} (γ : heap_names).

  Definition heap_pointsto_def (l : loc) (st : lock_state) (q : frac) (v: val) : iProp Σ :=
    own γ.(heap_name) (◯ {[ l := (q, to_lock_stateR st, to_agree v) ]}).
  Definition heap_pointsto_aux : seal (@heap_pointsto_def). Proof. by eexists. Qed.
  Definition heap_pointsto := unseal heap_pointsto_aux.
  Definition heap_pointsto_eq : @heap_pointsto = @heap_pointsto_def :=
    seal_eq heap_pointsto_aux.

  Definition heap_pointsto_vec (l : loc) (q : frac) (vl : list val) : iProp Σ :=
    ([∗ list] i ↦ v ∈ vl, heap_pointsto (l +ₗ i) (RSt 0) q v)%I.

  Definition heap_pointsto_vec_st (l : loc) (sts : list lock_state) (q : frac) (vl : list val) : iProp Σ :=
    ([∗ list] i ↦ st; v ∈ sts; vl, heap_pointsto (l +ₗ i) st q v)%I.

  Definition heap_block_size_def (l : loc) (q : Qp) (n: option nat) : iProp Σ :=
    ∃ b, ⌜l = Loc b 0⌝ ∗ l ↪[ γ.(heap_block_size_name) ]{# q } n.
  Definition heap_block_size_aux : seal (@heap_block_size_def). Proof. by eexists. Qed.
  Definition heap_block_size := unseal heap_block_size_aux.
  Definition heap_block_size_eq : @heap_block_size = @heap_block_size_def :=
    seal_eq heap_block_size_aux.

  Definition heap_freeable (l : loc) (q : Qp) (n: option nat) : iProp Σ :=
    ⌜block_is_dyn l.(loc_block)⌝ ∗ heap_block_size l q n.

  Definition heap_globals_def (gs : gset string) : iProp Σ :=
    own γ.(heap_globals_name) (to_agree (gs : leibnizO _)).
  Definition heap_globals_aux : seal (@heap_globals_def). Proof. by eexists. Qed.
  Definition heap_globals := unseal heap_globals_aux.
  Definition heap_globals_eq : @heap_globals = @heap_globals_def :=
    seal_eq heap_globals_aux.
  Definition heap_global_def (g : string) : iProp Σ :=
    ∃ gs, ⌜g ∈ gs⌝ ∗ heap_globals gs.
  Definition heap_global_aux : seal (@heap_global_def). Proof. by eexists. Qed.
  Definition heap_global := unseal heap_global_aux.
  Definition heap_global_eq : @heap_global = @heap_global_def :=
    seal_eq heap_global_aux.

  Definition heap_ctx (σ: state) : iProp Σ :=
    (∃ hF, own γ.(heap_name) (● to_heap σ.(heap))
         ∗ ghost_map_auth_frac γ.(heap_block_size_name) 1 hF
         ∗ heap_globals σ.(globals)
         ∗ ⌜heap_block_size_rel σ hF⌝
         ∗ ⌜heap_wf σ⌝)%I.
End definitions.

Global Typeclasses Opaque heap_pointsto_vec.
Global Instance: Params (@heap_pointsto) 4 := {}.
Global Instance: Params (@heap_block_size) 5 := {}.

(* Notation "l ↦{ q } v" := (heap_pointsto l q v) *)
(*   (at level 20, q at level 50, format "l  ↦{ q }  v") : bi_scope. *)
(* Notation "l ↦ v" := (heap_pointsto l 1 v) (at level 20) : bi_scope. *)
(* Notation "l ↦∗{ q } vl" := (heap_pointsto_vec l q vl) *)
(*   (at level 20, q at level 50, format "l  ↦∗{ q }  vl") : bi_scope. *)
(* Notation "l ↦∗ vl" := (heap_pointsto_vec l 1 vl) (at level 20) : bi_scope. *)



(* Notation "†{ q } l … n" := (heap_freeable l q n) *)
  (* (at level 20, q at level 50, format "†{ q } l … n") : bi_scope. *)
(* Notation "† l … n" := (heap_freeable l 1 n) (at level 20) : bi_scope. *)

Section to_heap.
  Implicit Types σ : gmap loc (lock_state * val).

  Lemma to_heap_valid σ : ✓ to_heap σ.
  Proof. intros l. rewrite lookup_fmap. case: (σ !! l)=> [[[|n] v]|] //=. Qed.

  Lemma lookup_to_heap_None σ l : σ !! l = None → to_heap σ !! l = None.
  Proof. by rewrite /to_heap lookup_fmap=> ->. Qed.

  Lemma to_heap_insert σ l x v :
    to_heap (<[l:=(x, v)]> σ)
    = <[l:=(1%Qp, to_lock_stateR x, to_agree v)]> (to_heap σ).
  Proof. by rewrite /to_heap fmap_insert. Qed.

  Lemma to_heap_delete σ l : to_heap (delete l σ) = delete l (to_heap σ).
  Proof. by rewrite /to_heap fmap_delete. Qed.
End to_heap.

Section globals.
  Context `{!heapG Σ} (γ : heap_names).

  Global Instance heap_globals_persistent gs : Persistent (heap_globals γ gs).
  Proof. rewrite heap_globals_eq. apply _. Qed.
  Global Instance heap_globals_timeless gs : Timeless (heap_globals γ gs).
  Proof. rewrite heap_globals_eq. apply _. Qed.

  Global Instance heap_global_persistent g : Persistent (heap_global γ g).
  Proof. rewrite heap_global_eq. apply _. Qed.
  Global Instance heap_global_timeless g : Timeless (heap_global γ g).
  Proof. rewrite heap_global_eq. apply _. Qed.

  Lemma heap_global_intro g gs :
    g ∈ gs →
    heap_globals γ gs -∗ heap_global γ g.
  Proof. rewrite heap_global_eq. iIntros (?) "?". iExists _. by iFrame. Qed.

  Lemma heap_global_intro_ctx g σ :
    g ∈ globals σ →
    heap_ctx γ σ -∗ heap_global γ g.
  Proof. iIntros (?) "(%h&?&?&Hg&?)". by iApply heap_global_intro. Qed.

  Lemma heap_globals_agree gs1 gs2 :
    heap_globals γ gs1 -∗ heap_globals γ gs2 -∗ ⌜gs1 = gs2⌝.
  Proof.
    rewrite heap_globals_eq. iIntros "H1 H2".
    iCombine "H1 H2" gives %Hvalid.
    move: Hvalid => /to_agree_op_valid. by fold_leibniz.
  Qed.

  Lemma heap_global_in gs g :
    heap_globals γ gs -∗ heap_global γ g -∗ ⌜g ∈ gs⌝.
  Proof.
    rewrite heap_global_eq. iIntros "Hgs (%gs'&%&Hgs')".
    by iDestruct (heap_globals_agree with "Hgs Hgs'") as %->.
  Qed.

  Lemma heap_global_in_ctx σ g :
    heap_ctx γ σ -∗ heap_global γ g -∗ ⌜g ∈ σ.(globals)⌝.
  Proof. iIntros "(%hF&?&?&Hgs&?) Hg". iApply (heap_global_in with "Hgs Hg"). Qed.

  Lemma heap_globals_ctx σ gs :
    heap_ctx γ σ -∗ heap_globals γ gs -∗ ⌜gs = σ.(globals)⌝.
  Proof. iIntros "(%hF&?&?&Hgs&?) Hg". iApply (heap_globals_agree with "Hg Hgs"). Qed.
End globals.

Section heap.
  Context `{!heapG Σ} (γ : heap_names).
  Implicit Types P Q : iProp Σ.
  Implicit Types σ : state.
  Implicit Types E : coPset.

  Local Notation "l ↦[ st ]{ q } v" := (heap_pointsto γ l st q v)
     (at level 20, q at level 50, format "l  ↦[ st ]{ q }  v") : bi_scope.
  Local Notation "l ↦[ st ] v" := (heap_pointsto γ l st 1 v) (at level 20) : bi_scope.
  Local Notation "l ↦{ q } v" := (heap_pointsto γ l (RSt 0) q v)
     (at level 20, q at level 50, format "l  ↦{ q }  v") : bi_scope.
  Local Notation "l ↦ v" := (heap_pointsto γ l (RSt 0) 1 v) (at level 20) : bi_scope.
  Local Notation "l ↦∗[ st ]{ q } vl" := (heap_pointsto_vec_st γ l st q vl)
      (at level 20, q at level 50, format "l  ↦∗[ st ]{ q }  vl") : bi_scope.
  Local Notation "l ↦∗[ st ] vl" := (heap_pointsto_vec_st γ l st 1 vl) (at level 20) : bi_scope.
  Local Notation "l ↦∗{ q } vl" := (heap_pointsto_vec γ l q vl)
      (at level 20, q at level 50, format "l  ↦∗{ q }  vl") : bi_scope.
  Local Notation "l ↦∗ vl" := (heap_pointsto_vec γ l 1 vl) (at level 20) : bi_scope.

  Local Notation block_size := (heap_block_size γ).
  Local Notation "†{ q } l …? n" := (heap_freeable γ l q n)
  (at level 20, q at level 50, format "†{ q } l …? n") : bi_scope.
  Local Notation "† l …? n" := (heap_freeable γ l 1 n) (at level 20) : bi_scope.

  (** General properties of pointsto and block_size *)
  Global Instance heap_pointsto_timeless l st q v : Timeless (l↦[st]{q}v).
  Proof. rewrite heap_pointsto_eq /heap_pointsto_def. apply _. Qed.

  Lemma heap_pointsto_split l n q n1 q1 n2 q2 v:
    n = n1 + n2 → q = (q1 + q2)%Qp →
    l ↦[RSt n]{q} v ⊣⊢ l ↦[RSt n1]{q1} v ∗ l ↦[RSt n2]{q2} v.
  Proof.
    intros -> ->.
    rewrite heap_pointsto_eq -own_op -auth_frag_op singleton_op -!pair_op agree_idemp /= //.
  Qed.

  Lemma heap_pointsto_combine_0 l q1 q2 v st:
    l ↦{q1} v ⊢ l ↦[st]{q2} v -∗
    l ↦[st]{q1 + q2} v.
  Proof.
    apply: wand_intro_r.
    rewrite heap_pointsto_eq -own_op -auth_frag_op singleton_op -!pair_op agree_idemp /= //.
    destruct st; [|done]. etrans; [apply: own_valid|].
    by iIntros ([[??]%pair_valid?]%auth_frag_valid_1%singleton_valid%pair_valid).
  Qed.

  Global Instance heap_pointsto_fractional l v: Fractional (λ q, l ↦{q} v)%I.
  Proof. intros p q. by apply heap_pointsto_split. Qed.
  Global Instance heap_pointsto_as_fractional l q v:
    AsFractional (l ↦{q} v) (λ q, l ↦{q} v)%I q.
  Proof. split; first done. apply _. Qed.
  Global Instance frame_heap_pointsto p l v q1 q2 q :
    FrameFractionalQp q1 q2 q →
    Frame p (l ↦{q1} v) (l ↦{q2} v) (l ↦{q} v) | 5.
  Proof. apply: frame_fractional. Qed.

  Global Instance heap_pointsto_vec_timeless l st q vl : Timeless (l ↦∗[st]{q} vl).
  Proof. rewrite /heap_pointsto_vec. apply _. Qed.

  Global Instance heap_pointsto_vec_fractional l vl: Fractional (λ q, l ↦∗{q} vl)%I.
  Proof.
    intros p q. rewrite /heap_pointsto_vec -big_sepL_sep.
    by setoid_rewrite (fractional (Φ := λ q, (_ ↦{q} _)%I)).
  Qed.
  Global Instance heap_pointsto_vec_as_fractional l q vl:
    AsFractional (l ↦∗{q} vl) (λ q, l ↦∗{q} vl)%I q.
  Proof. split; first done. apply _. Qed.
  Global Instance frame_heap_pointsto_vec p l v q1 q2 q :
    FrameFractionalQp q1 q2 q →
    Frame p (l ↦∗{q1} v) (l ↦∗{q2} v) (l ↦∗{q} v)%I | 5.
  (* FIXME(https://github.com/coq/coq/issues/17688): Φ is not inferred. *)
  Proof. apply: (frame_fractional (λ q, l ↦∗{q} v)%I). Qed.

  Global Instance heap_block_size_timeless q b n : Timeless (heap_block_size γ b q n).
  Proof. rewrite heap_block_size_eq /heap_block_size_def. apply _. Qed.

  Lemma heap_pointsto_agree l q1 q2 v1 v2 st1 st2 : l ↦[st1]{q1} v1 ∗ l ↦[st2]{q2} v2 ⊢ ⌜v1 = v2⌝.
  Proof.
    rewrite heap_pointsto_eq -own_op -auth_frag_op own_valid internal_cmra_valid_discrete.
    eapply pure_elim; [done|]. move => /auth_frag_valid /=.
    rewrite singleton_op -pair_op singleton_valid => -[? /to_agree_op_inv_L->]; eauto.
  Qed.

  Lemma heap_pointsto_valid l q v st : l ↦[st]{q} v ⊢ ⌜(q ≤ 1)%Qp⌝.
  Proof.
    rewrite heap_pointsto_eq. etrans; [apply: own_valid|]. iPureIntro.
    by rewrite auth_frag_valid singleton_valid !pair_valid => -[[??]?].
  Qed.

  Lemma heap_pointsto_ne l1 l2 q v1 v2 : l1 ↦ v1 -∗ l2 ↦{q} v2 -∗ ⌜l1 ≠ l2⌝.
  Proof.
    destruct (decide (l1 = l2)); [subst |by eauto].
    iIntros "Hl1 Hl2".
    iDestruct (heap_pointsto_agree with "[$Hl1 $Hl2]") as %->.
    iCombine "Hl1" "Hl2" as "Hl".
    by iDestruct (heap_pointsto_valid with "Hl") as %?%Qp.not_add_le_l.
  Qed.

  Lemma heap_pointsto_vec_nil l q : l ↦∗{q} [] ⊣⊢ True.
  Proof. by rewrite /heap_pointsto_vec. Qed.

  Lemma heap_pointsto_vec_app l q vl1 vl2 :
    l ↦∗{q} (vl1 ++ vl2) ⊣⊢ l ↦∗{q} vl1 ∗ (l +ₗ length vl1) ↦∗{q} vl2.
  Proof.
    rewrite /heap_pointsto_vec big_sepL_app.
    do 2 f_equiv. intros k v. by rewrite loc_add_assoc Nat2Z.inj_add.
  Qed.

  Lemma heap_pointsto_vec_singleton l q v : l ↦∗{q} [v] ⊣⊢ l ↦{q} v.
  Proof. by rewrite /heap_pointsto_vec /= loc_add_0 right_id. Qed.

  Lemma heap_pointsto_vec_cons l q v vl:
    l ↦∗{q} (v :: vl) ⊣⊢ l ↦{q} v ∗ (l +ₗ 1) ↦∗{q} vl.
  Proof.
    by rewrite (heap_pointsto_vec_app l q [v] vl) heap_pointsto_vec_singleton.
  Qed.

  Lemma heap_pointsto_vec_op l q1 q2 vl1 vl2 :
    length vl1 = length vl2 →
    l ↦∗{q1} vl1 ∗ l ↦∗{q2} vl2 ⊣⊢ ⌜vl1 = vl2⌝ ∧ l ↦∗{q1+q2} vl1.
  Proof.
    intros Hlen%Forall2_same_length. apply (anti_symm (⊢)).
    - revert l. induction Hlen as [|v1 v2 vl1 vl2 _ _ IH]=> l.
      { rewrite !heap_pointsto_vec_nil. iIntros "_"; auto. }
      rewrite !heap_pointsto_vec_cons. iIntros "[[Hv1 Hvl1] [Hv2 Hvl2]]".
      iDestruct (IH (l +ₗ 1) with "[$Hvl1 $Hvl2]") as "[% $]"; subst.
      rewrite (inj_iff (.:: vl2)).
      iDestruct (heap_pointsto_agree with "[$Hv1 $Hv2]") as %<-.
      iSplit; first done. iFrame.
    - by iIntros "[% [$ Hl2]]"; subst.
  Qed.

  Lemma heap_pointsto_vec_st_length l q vl sts:
    l ↦∗[sts]{q} vl ⊢ ⌜length sts = length vl⌝.
  Proof. apply big_sepL2_length. Qed.

  Lemma heap_pointsto_vec_to_st l q vl :
    l ↦∗{q} vl ⊣⊢ l ↦∗[replicate (length vl) (RSt 0)]{q} vl.
  Proof.
    rewrite /heap_pointsto_vec /heap_pointsto_vec_st.
    by rewrite big_sepL2_replicate_l.
  Qed.

  Lemma heap_pointsto_vec_combine l q vl :
    vl ≠ [] →
    l ↦∗{q} vl ⊣⊢ own γ.(heap_name) (◯ [^op list] i ↦ v ∈ vl,
      {[l +ₗ i := (q, Cinr 0%nat, to_agree v)]}).
  Proof.
    rewrite /heap_pointsto_vec heap_pointsto_eq /heap_pointsto_def=>?.
    rewrite (big_opL_commute auth_frag) big_opL_commute1 //.
  Qed.

  Lemma heap_pointsto_vec_st_combine l q vl sts:
    vl ≠ [] →
    length sts = length vl →
    l ↦∗[sts]{q} vl ⊣⊢ own γ.(heap_name) (◯ [^op list] i ↦ v ∈ zip sts vl,
      {[l +ₗ i := (q, to_lock_stateR v.1, to_agree v.2)]}).
  Proof.
    rewrite /heap_pointsto_vec_st heap_pointsto_eq /heap_pointsto_def=>??.
    rewrite (big_opL_commute auth_frag) big_opL_commute1 //.
    2: { by destruct vl, sts; simplify_eq/=. }
    rewrite big_sepL2_alt.
    assert (⌜length sts = length vl⌝ ⊣⊢@{iPropI Σ} True)%I as -> by (iPureIntro; naive_solver).
    by rewrite left_id.
  Qed.

  Lemma heap_block_size_idx l q n :
    block_size l q n -∗ ⌜loc_idx l = 0⌝.
  Proof. rewrite heap_block_size_eq. by iIntros "(%b&->&?)". Qed.

  Lemma heap_block_size_excl l l' n n' :
    loc_block l = loc_block l' →
    block_size l 1 n -∗ block_size l' 1 n' -∗ False.
  Proof.
    rewrite heap_block_size_eq.
    iIntros (?) "(%&->&Hl1) (%&->&Hl2)"; simplify_eq/=.
    by iCombine "Hl1 Hl2" gives %[? ?].
  Qed.

  Lemma heap_block_size_rel_stable σ h l p :
    heap_block_size_rel σ h → is_Some (σ.(heap) !! l) →
    heap_block_size_rel (state_upd_heap <[l := p]> σ) h.
  Proof.
    intros REL Hσ blk o qs Hqs. destruct (REL blk o qs) as [? [? [? REL']]]; first done.
    split_and!; [done..|]=> i. rewrite -REL' lookup_insert_is_Some.
    destruct (decide (l = Loc blk i)); naive_solver.
  Qed.

  Lemma heap_block_size_rel_init_mem b h n σ v:
    n ≠ O →
    b ∉ σ.(used_dyn_blocks) →
    (∀ m : Z, σ.(heap) !! (dyn_loc b +ₗ m) = None) →
    heap_block_size_rel σ h →
    heap_block_size_rel (State
                         (heap_array (dyn_loc b) (replicate n v) ∪ σ.(heap))
                         ({[b]} ∪ σ.(used_dyn_blocks))
                         σ.(globals))
                      (<[dyn_loc b := Some n]> h).
  Proof.
    move => ? Hnotin Hnone Hrel b' i' o /lookup_insert_Some[[[??]?]|[? Hl]]; simplify_eq/=.
    - split_and!; [set_solver|done|lia|] => i.
      split.
      + move => [?].
        rewrite lookup_union_Some ?Hnone.
        2: { apply heap_array_map_disjoint. naive_solver lia. }
        rewrite heap_array_lookup => -[[?[?[?[[?][?]]]]]|//]; simplify_eq.
        rewrite lookup_replicate. lia.
      + move => ?.
        eexists _.
        rewrite lookup_union_Some ?Hnone.
        2: { apply heap_array_map_disjoint. naive_solver lia. }
        left. apply heap_array_lookup. eexists i, _.
        split_and!; [lia|done |done |].
        rewrite lookup_replicate. naive_solver lia.
    - have [?[?[? Hi]]]:= Hrel _ _ _ Hl.
      split_and!; [destruct b'; set_solver|done|lia|] => i.
      have <-:= Hi i. f_equiv.
      apply option_eq => ?.
      rewrite lookup_union_Some.
      2: { apply heap_array_map_disjoint. naive_solver lia. }
      rewrite heap_array_lookup.
      split; [|naive_solver].
      move => [[?[?[?[[??]?]]]]|//]; simplify_eq.
  Qed.

  Lemma heap_block_size_rel_free_mem σ hF n l :
    loc_idx l = 0 →
    hF !! l = Some (Some n) →
    heap_block_size_rel σ hF →
    heap_block_size_rel (state_upd_heap (free_mem l n) σ) (<[l:=None]> hF).
  Proof.
    intros ? Hl REL b i qs Hlookup. destruct l as [b' ?]; simplify_eq/=.
    destruct (REL b' 0 (Some n)) as [? [? [? REL']]]; auto.
    move: Hlookup => /lookup_insert_Some [[??]|[NEQ ?]]; simplify_eq.
    - split_and!; [done| done| simpl; lia |] => i /=. split; [|lia] => -[?].
      move => /lookup_free_mem_Some/=[Hh[//|Hi]]. contradict Hi. apply REL'. naive_solver.
    - destruct (REL b i qs) as [? [? [? REL'']]]; auto.
      split_and!; [done..|]=> i'. rewrite -REL'' lookup_free_mem_1 //=. simplify_eq/=. congruence.
  Qed.

  Lemma heap_block_size_inj n1 l1 l2 n2 σ:
    (0 < n1)%Z →
    (∀ m, is_Some (σ.(heap) !! (l1 +ₗ m)) ↔ (0 ≤ m < n1)%Z) →
    loc_block l1 = loc_block l2 →
    heap_ctx γ σ -∗ block_size l2 1 n2 -∗ ⌜n2 = Some (Z.to_nat n1) ∧ l1 = l2⌝.
  Proof.
    iIntros (? Hrel1 ?) "(%hF & ? & HhF & ? & %Hrel & %) Hf".
    rewrite heap_block_size_eq. iDestruct "Hf" as (b2 ->) "Hf".
    iDestruct (ghost_map_lookup with "HhF Hf") as %Hf.
    iPureIntro. destruct l1 as [b1 o1]; simplify_eq.
    have [? [? [? {}Hrel2]]]:= Hrel _ _ _ Hf.
    destruct n2 as [n|]; simplify_eq/=; last first. {
      have [_ [|? Hl]]:= Hrel1 0; [lia|].
      have [/=[|] ]:= Hrel2 o1%Z; last lia.
      rewrite loc_add_0 in Hl. naive_solver.
    }
    destruct (decide (o1 = 0)); simplify_eq.
    { split; [|done].
      have Heq: (∀ i : Z, (0 ≤ i < n) ↔ (0 ≤ i < n1))%Z by naive_solver.
      f_equal.
      destruct (decide (n1 < n)%Z). { have := Heq n1. lia. }
      destruct (decide (n < n1)%Z). { have := Heq n. lia. }
      lia.
    }
    destruct (decide (o1 < 0)%Z).
    - have [_ [|? Hl]]:= Hrel1 0; first lia.
      have [/=[|] ]:= Hrel2 o1%Z; last lia.
      rewrite loc_add_0 in Hl. naive_solver.
    - have [_ [|? Hl]]:= Hrel2 0; first lia.
      have [/=[|] ]:= Hrel1 (-o1)%Z; last lia.
      rewrite /loc_add/=. naive_solver lia.
  Qed.

  Lemma heap_block_size_lookup σ l l' x n q:
    σ.(heap) !! l' = Some x → loc_block l' = loc_block l →
    heap_ctx γ σ -∗ block_size l q n -∗ ⌜∃ n' : nat, n' < default 0 n ∧ l' = l +ₗ n'⌝.
  Proof.
    iIntros (Hlo ?) "(%hF&?&HhF&Hg&%Hrel&%) Hf".
    rewrite heap_block_size_eq. iDestruct "Hf" as (b ->) "Hf".
    iDestruct (ghost_map_lookup with "HhF Hf") as %Hf.
    iPureIntro.
    have [? {}Hrel]:= Hrel _ _ _ Hf.
    have Hl': l' = (Loc b (loc_idx l')).
    { destruct l' => /=. by simplify_eq/=. }
    rewrite Hl' in Hlo.
    eapply mk_is_Some, Hrel in Hlo.
    eexists (Z.to_nat (loc_idx l')). split; [lia|].
    rewrite Hl'. f_equal => /=. lia.
  Qed.

  Lemma heap_ctx_wf σ :
    heap_ctx γ σ -∗ ⌜heap_wf σ⌝.
  Proof. by iDestruct 1 as (?) "(?&?&?&?&%)". Qed.

  (** Weakest precondition *)
  Lemma heap_alloc_vs (h : gmap loc _) l n v:
    (∀ m : Z, h !! (l +ₗ m) = None) →
    own γ.(heap_name) (● to_heap h)
    ==∗ own γ.(heap_name) (● to_heap (heap_array l (replicate n v) ∪ h))
       ∗ own γ.(heap_name) (◯ [^op list] i ↦ v ∈ (replicate n v),
           {[l +ₗ i := (1%Qp, Cinr 0%nat, to_agree v)]}).
  Proof.
    intros FREE. rewrite -own_op. apply bi.entails_wand, own_update, auth_update_alloc.
    revert l FREE. induction n as [|n IH]=> l FRESH.
    { by rewrite left_id. }
    rewrite replicate_S (big_opL_consZ_l (λ k _, _ (_ k) _ )) /=.
    etrans; first apply (IH (l +ₗ 1)).
    { intros. by rewrite loc_add_assoc. }
    rewrite loc_add_0 -insert_singleton_op; last first.
    { rewrite -None_equiv_eq big_opL_commute None_equiv_eq big_opL_None=> l' v' ?.
      rewrite lookup_singleton_None -{2}(loc_add_0 l). apply not_inj; lia. }
    rewrite -insert_union_singleton_l -insert_union_l.
    rewrite to_heap_insert. setoid_rewrite loc_add_assoc.
    apply alloc_local_update; last done. apply lookup_to_heap_None.
    apply lookup_union_None. split.
    - apply eq_None_not_Some => -[?] /heap_array_lookup[?[?[?[?[?]]]]].
      rewrite lookup_replicate.
      destruct l; simplify_eq/=. unfold loc_add in *. naive_solver lia.
    - by rewrite -(loc_add_0 l) FRESH.
  Qed.

  Lemma heap_alloc σ b n v :
    (0 < n)%Z →
    b ∉ σ.(used_dyn_blocks) →
    (∀ m, σ.(heap) !! (dyn_loc b +ₗ m) = None) →
    heap_ctx γ σ ==∗
      heap_ctx γ (State (heap_array (dyn_loc b) (replicate (Z.to_nat n) v) ∪ σ.(heap)) ({[b]} ∪ σ.(used_dyn_blocks)) σ.(globals)) ∗
      block_size (dyn_loc b) 1 (Some (Z.to_nat n)) ∗
      dyn_loc b ↦∗ replicate (Z.to_nat n) v.
  Proof.
    intros ???; iDestruct 1 as (hF) "(Hvalσ & HhF & Hg & %Hrel & %Hwf)".
    assert (Z.to_nat n ≠ O). { rewrite -(Nat2Z.id 0)=>/Z2Nat.inj. lia. }
    iMod (heap_alloc_vs _ _ (Z.to_nat n) with "[$Hvalσ]") as "[Hvalσ Hpointsto]"; first done.
    iMod (ghost_map_insert (dyn_loc b) (Some _) with "HhF") as "[? ?]".
    { apply eq_None_not_Some => -[? /Hrel]. naive_solver. }
    rewrite heap_block_size_eq heap_pointsto_vec_combine //.
    2: { by destruct (Z.to_nat n). }
    iFrame. iModIntro. iSplit; [|by eauto].
    iPureIntro. split.
    - by apply heap_block_size_rel_init_mem.
    - by apply heap_wf_init_mem.
  Qed.

  Lemma heap_free_vs (h : gmap loc _) l vl sts :
    length vl = length sts →
    own γ.(heap_name) (● to_heap h) ∗ own γ.(heap_name) (◯ [^op list] i ↦ v ∈ zip sts vl,
      {[l +ₗ i := (1%Qp, to_lock_stateR v.1, to_agree v.2)]})
    ==∗ own γ.(heap_name) (● to_heap (free_mem l (length vl) h)).
  Proof.
    rewrite -own_op => Hlen. apply bi.entails_wand, own_update, auth_update_dealloc.
    revert h l sts Hlen. induction vl as [|v vl IH]=> h l; [by case |] => -[//|st sts][?].
    cbn [zip_with]. rewrite (big_opL_consZ_l (λ k _, _ (_ k) _ )) /= loc_add_0.
    apply local_update_total_valid=> _ Hvalid _.
    assert (([^op list] k↦y ∈ zip sts vl,
      {[l +ₗ (1 + k) := (1%Qp, to_lock_stateR y.1, to_agree y.2)]} : heapUR) !! l = None).
    { move: (Hvalid l). rewrite lookup_op lookup_singleton_eq.
      by move=> /(cmra_discrete_valid_iff 0) /exclusiveN_Some_l. }
    rewrite -insert_singleton_op //. etrans.
    { apply (delete_local_update _ _ l (1%Qp, to_lock_stateR st, to_agree v)).
      by rewrite lookup_insert_eq. }
    rewrite delete_insert_id // -to_heap_delete delete_free_mem; [|done].
    setoid_rewrite <-loc_add_assoc. by apply IH.
  Qed.

  Lemma heap_free σ l vl (n : Z) sts :
    n = length vl →
    block_is_dyn l.(loc_block) →
    heap_ctx γ σ -∗ l ↦∗[sts] vl -∗ block_size l 1 (Some (length vl))
    ==∗ ⌜0 < n⌝%Z ∗ ⌜∀ m, is_Some (σ.(heap) !! (l +ₗ m)) ↔ (0 ≤ m < n)⌝%Z ∗
        block_size l 1 None ∗ heap_ctx γ (state_upd_heap (free_mem l (Z.to_nat n)) σ).
  Proof.
    iDestruct 1 as (hF) "(Hvalσ & HhF & Hg & %REL & %Hwf)". subst.
    rewrite heap_block_size_eq. iIntros "Hmt (%&->&Hf)".
    iDestruct (ghost_map_lookup with "HhF Hf") as %Hf.
    move: (Hf) => /REL[?[?[??]]]. simplify_eq/=.
    iSplitR. { iPureIntro. lia. } iSplitR; first done.
    iDestruct (heap_pointsto_vec_st_length with "Hmt") as %?.
    iMod (heap_free_vs with "[Hmt Hvalσ]") as "Hvalσ"; [done| |].
    { rewrite heap_pointsto_vec_st_combine //; first by iFrame.
      destruct vl; simpl in * => //; lia. }
    rewrite Nat2Z.id.
    iMod (ghost_map_update None with "HhF Hf") as "[? $]".
    iModIntro. iSplit;[by eauto|]. iExists _. iFrame. iPureIntro.
    eauto using heap_block_size_rel_free_mem, heap_wf_free_mem.
  Qed.

  Lemma heap_pointsto_lookup h l ls q v :
    own γ.(heap_name) (● to_heap h) -∗
    own γ.(heap_name) (◯ {[ l := (q, to_lock_stateR ls, to_agree v) ]}) -∗
    ⌜∃ n' : nat,
        h !! l = Some (match ls with RSt n => RSt (n+n') | WSt => WSt end, v)⌝.
  Proof.
    iIntros "H● H◯".
    iCombine "H● H◯" gives %[Hl?]%auth_both_valid_discrete.
    iPureIntro. move: Hl=> /singleton_included_l [[[q' ls'] dv]].
    rewrite /to_heap lookup_fmap fmap_Some_equiv.
    move=> [[[ls'' v'] [?[[/=??]->]]]]; simplify_eq.
    move=> /Some_pair_included_total_2
      [/Some_pair_included [_ Hincl] /to_agree_included->].
    destruct ls as [|n], ls'' as [|n''],
       Hincl as [[[|n'|]|] [=]%leibniz_equiv]; subst.
    - by exists O.
    - eauto.
    - exists O. by rewrite Nat.add_0_r.
  Qed.

  Lemma heap_pointsto_lookup_1 h l ls v :
    own γ.(heap_name) (● to_heap h) -∗
    own γ.(heap_name) (◯ {[ l := (1%Qp, to_lock_stateR ls, to_agree v) ]}) -∗
    ⌜h !! l = Some (ls, v)⌝.
  Proof.
    iIntros "H● H◯".
    iCombine "H● H◯" gives %[Hl?]%auth_both_valid_discrete.
    iPureIntro. move: Hl=> /singleton_included_l [[[q' ls'] dv]].
    rewrite /to_heap lookup_fmap fmap_Some_equiv.
    move=> [[[ls'' v'] [?[[/=??]->]]] Hincl]; simplify_eq.
    apply (Some_included_exclusive _ _) in Hincl as [? Hval]; last by destruct ls''.
    apply (inj to_agree) in Hval. fold_leibniz. subst.
    destruct ls, ls''; rewrite ?Nat.add_0_r; naive_solver.
  Qed.

  Lemma heap_read_vs h n1 n2 nf l q v:
    h !! l = Some (RSt (n1 + nf), v) →
    own γ.(heap_name) (● to_heap h) -∗ heap_pointsto γ l (RSt n1) q v
    ==∗ own γ.(heap_name) (● to_heap (<[l:=(RSt (n2 + nf), v)]> h))
        ∗ heap_pointsto γ l (RSt n2) q v.
  Proof.
    rewrite heap_pointsto_eq.
    intros Hσv. apply bi.entails_wand, wand_intro_r. rewrite -!own_op to_heap_insert.
    eapply own_update, auth_update, singleton_local_update.
    { by rewrite /to_heap lookup_fmap Hσv. }
    apply prod_local_update_1, prod_local_update_2, csum_local_update_r.
    apply nat_local_update; lia.
  Qed.

  Lemma heap_read_st σ l st q v :
    heap_ctx γ σ -∗ l ↦[st]{q} v -∗
    ⌜∃ n' : nat,
        σ.(heap) !! l = Some (match st with RSt n => RSt (n+n') | WSt => WSt end, v)⌝.
  Proof.
    iDestruct 1 as (hF) "(Hσ & HhF & REL)". iIntros "Hmt".
    rewrite heap_pointsto_eq.
    iDestruct (heap_pointsto_lookup with "Hσ Hmt") as %[n Hσl]; eauto.
  Qed.

  Lemma heap_read_st_1 σ l st v :
    heap_ctx γ σ -∗ l ↦[st] v -∗ ⌜σ.(heap) !! l = Some (st, v)⌝.
  Proof.
    iDestruct 1 as (hF) "(Hσ & HhF & REL)". iIntros "Hmt".
    rewrite heap_pointsto_eq.
    iDestruct (heap_pointsto_lookup_1 with "Hσ Hmt") as %?; eauto.
  Qed.

  Lemma heap_read σ l q v :
    heap_ctx γ σ -∗ l ↦{q} v -∗ ∃ n, ⌜σ.(heap) !! l = Some (RSt n, v)⌝.
  Proof.
    iDestruct 1 as (hF) "(Hσ & HhF & REL)". iIntros "Hmt".
    rewrite heap_pointsto_eq.
    iDestruct (heap_pointsto_lookup with "Hσ Hmt") as %[n Hσl]; eauto.
  Qed.

  Lemma heap_read_1 σ l v :
    heap_ctx γ σ -∗ l ↦ v -∗ ⌜σ.(heap) !! l = Some (RSt 0, v)⌝.
  Proof.
    iDestruct 1 as (hF) "(Hσ & HhF & REL)". iIntros "Hmt".
    rewrite heap_pointsto_eq.
    iDestruct (heap_pointsto_lookup_1 with "Hσ Hmt") as %?; auto.
  Qed.

  Lemma heap_read_na_1 l q v n σ :
    heap_ctx γ σ -∗ l ↦[RSt n]{q} v ==∗ ∃ n',
      ⌜σ.(heap) !! l = Some (RSt (n + n'), v)⌝ ∗
      heap_ctx γ (state_upd_heap <[l:=(RSt (S (n + n')), v)]> σ) ∗
      l ↦[RSt (S n)]{q} v.
  Proof.
    iIntros "Hσ Hmt".
    iDestruct (heap_read_st with "Hσ Hmt") as %[n' Hσl]; eauto.
    iDestruct "Hσ" as (hF) "(Hσ & HhF & Hg & % & %)".
    iMod (heap_read_vs with "Hσ Hmt") as "[Hσ Hmt]"; first done.
    iModIntro. iExists n'; iSplit; [done|]. iFrame.
    eauto 8 using heap_block_size_rel_stable, heap_wf_insert.
  Qed.

  Lemma heap_read_na_2 σ l q v n :
    heap_ctx γ σ -∗ l ↦[RSt (S n)]{q} v ==∗ ∃ n',
      ⌜σ.(heap) !! l = Some (RSt (S (n + n')), v)⌝ ∗
      heap_ctx γ (state_upd_heap <[l:=(RSt (n + n'), v)]> σ) ∗
      l ↦[RSt n]{q} v.
  Proof.
    iIntros "Hσ Hmt".
    iDestruct (heap_read_st with "Hσ Hmt") as %[n' Hσl]; eauto.
    iDestruct "Hσ" as (hF) "(Hσ & HhF & Hg & % & %)".
    iMod (heap_read_vs with "Hσ Hmt") as "[Hσ Hmt]"; first done.
    iModIntro. iExists n'; iSplit; [done|]. iFrame.
    eauto 8 using heap_block_size_rel_stable, heap_wf_insert.
  Qed.

  Lemma heap_read_na σ l q v :
    heap_ctx γ σ -∗ l ↦{q} v ==∗ ∃ n,
      ⌜σ.(heap) !! l = Some (RSt n, v)⌝ ∗
      heap_ctx γ (state_upd_heap <[l:=(RSt (S n), v)]> σ) ∗
      ∀ σ2, heap_ctx γ σ2 ==∗ ∃ n2, ⌜σ2.(heap) !! l = Some (RSt (S n2), v)⌝ ∗
        heap_ctx γ (state_upd_heap <[l:=(RSt n2, v)]> σ2) ∗ l ↦{q} v.
  Proof.
    iIntros "Hσ Hmt".
    iMod (heap_read_na_1 with "Hσ Hmt") as (? ?) "[Hσ Hmt]".
    iModIntro. iExists _. iFrame. iSplit; [done|].
    iIntros (σ2) "Hσ".
    iMod (heap_read_na_2 with "Hσ Hmt") as (? ?) "[Hσ Hmt]".
    iModIntro. iExists _. iFrame. done.
  Qed.

  Lemma heap_write_vs h st1 st2 l v v':
    h !! l = Some (st1, v) →
    own γ.(heap_name) (● to_heap h) -∗ heap_pointsto γ l st1 1%Qp v
    ==∗ own γ.(heap_name) (● to_heap (<[l:=(st2, v')]> h))
        ∗ heap_pointsto γ l st2 1%Qp v'.
  Proof.
    rewrite heap_pointsto_eq.
    intros Hσv. apply bi.entails_wand, wand_intro_r. rewrite -!own_op to_heap_insert.
    eapply own_update, auth_update, singleton_local_update.
    { by rewrite /to_heap lookup_fmap Hσv. }
    apply exclusive_local_update. by destruct st2.
  Qed.

  Lemma heap_write σ l v v' st st' :
    heap_ctx γ σ -∗ l ↦[st] v ==∗ heap_ctx γ (state_upd_heap <[l:=(st', v')]> σ) ∗ l ↦[st'] v'.
  Proof.
    iIntros "Hσ Hmt".
    iDestruct (heap_read_st_1 with "Hσ Hmt") as %?; auto.
    iDestruct "Hσ" as (hF) "(Hσ & HhF & Hg & % & %)".
    iMod (heap_write_vs with "Hσ Hmt") as "[Hσ $]"; first done.
    iModIntro. iExists _. iFrame. eauto 8 using heap_block_size_rel_stable, heap_wf_insert.
  Qed.

  Lemma heap_write_na_1 σ l v st :
    heap_ctx γ σ -∗ l ↦[st] v ==∗
      ⌜σ.(heap) !! l = Some (st, v)⌝ ∗
      heap_ctx γ (state_upd_heap <[l:=(WSt, v)]> σ) ∗
      l ↦[WSt] v.
  Proof.
    iIntros "Hσ Hmt".
    iDestruct (heap_read_st_1 with "Hσ Hmt") as %?; eauto.
    iSplitR; [done|]. iApply (heap_write with "Hσ Hmt").
  Qed.

  Lemma heap_write_na_2 σ l v v' :
    heap_ctx γ σ -∗ l ↦[WSt] v ==∗
      ⌜σ.(heap) !! l = Some (WSt, v)⌝ ∗
      heap_ctx γ (state_upd_heap <[l:=(RSt 0, v')]> σ) ∗
      l ↦ v'.
  Proof.
    iIntros "Hσ Hmt".
    iDestruct (heap_read_st_1 with "Hσ Hmt") as %?; eauto.
    iSplitR; [done|]. iApply (heap_write with "Hσ Hmt").
  Qed.

  Lemma heap_write_na σ l v v' :
    heap_ctx γ σ -∗ l ↦ v ==∗
      ⌜σ.(heap) !! l = Some (RSt 0, v)⌝ ∗
      heap_ctx γ (state_upd_heap <[l:=(WSt, v)]> σ) ∗
      ∀ σ2, heap_ctx γ σ2 ==∗ ⌜σ2.(heap) !! l = Some (WSt, v)⌝ ∗
        heap_ctx γ (state_upd_heap <[l:=(RSt 0, v')]> σ2) ∗ l ↦ v'.
  Proof.
    iIntros "Hσ Hmt".
    iMod (heap_write_na_1 with "Hσ Hmt") as (?) "[Hσ Hmt]".
    iModIntro. iFrame. iSplit; [done|].
    iIntros (σ2) "Hσ".
    iMod (heap_write_na_2 with "Hσ Hmt") as (?) "[Hσ Hmt]".
    iModIntro. iFrame. done.
  Qed.

End heap.

Lemma heap_init `{heapG Σ} gs :
  ⊢ |==> ∃ γ : heap_names, heap_ctx γ (state_init gs) ∗
    heap_globals γ (dom gs) ∗
    [∗ map] n ↦ v ∈ gs, heap_pointsto γ (global_loc n) (RSt 0) 1 v ∗ heap_block_size γ (global_loc n) 1 (Some 1).
Proof.
  set σ := state_init gs.
  iMod (own_alloc (● (to_heap σ.(heap)) ⋅ ◯ (to_heap σ.(heap)))) as (γheap) "[Hheap Hfrag]".
  { apply auth_both_valid_discrete. split; first done. apply to_heap_valid. }
  iMod (ghost_map_alloc (kmap global_loc (const (Some 1) <$> gs))) as (γfmap) "[Hfmap Hffrag]".
  iMod (own_alloc (to_agree ((dom gs) : leibnizO _))) as (γg) "#Hg" => //.
  iExists {| heap_name := γheap; heap_block_size_name := γfmap; heap_globals_name := γg |}.
  iModIntro. rewrite /heap_ctx heap_globals_eq /=. iFrame "Hg". iClear "Hg".
  iSplitR "Hfrag Hffrag".
  - iExists _. iFrame. iPureIntro.
    split.
    + intros b i o. move => /lookup_kmap_Some[n [[-> ->] /lookup_fmap_Some [? [<- ?]]]] /=.
      split_and!; [done|done|lia|] => {}i /=.
      destruct (decide (i = 0)); simplify_eq; split; try lia.
      * move => _. eexists _. apply/lookup_kmap_Some. eexists _. split; [done|].
        apply lookup_fmap_Some. naive_solver.
      * move => [? /lookup_kmap_Some[? [[??] /lookup_fmap_Some [? [? ?]]]]]; simplify_eq.
    + apply state_init_wf.
  - rewrite heap_pointsto_eq heap_block_size_eq /heap_pointsto_def /heap_block_size_def /=.
    iInduction gs as [|l v gs Hk] "IH" using map_ind.
    { iApply big_sepM_empty. done. }
    rewrite big_sepM_insert; last done.
    rewrite !fmap_insert !kmap_insert to_heap_insert big_sepM_insert.
    2: { apply/lookup_kmap_None => ? [<-]. by rewrite lookup_fmap Hk. }
    rewrite insert_singleton_op. 2:{
      apply lookup_to_heap_None. apply/lookup_kmap_None => ? [<-]. by rewrite lookup_fmap Hk.
    }
    iDestruct "Hffrag" as "[$ Hffrag]".
    iDestruct "Hfrag" as "[$ Hfrag]".
    iSplit; [by eauto|]. iApply ("IH" with "Hfrag Hffrag").
Qed.
