(** This file has been adapted from the Iris development, available at 
  https://gitlab.mpi-sws.org/iris/iris
*)

From stdpp Require Export namespaces.
From iris.algebra Require Import gmap_view reservation_map agree frac.
From iris.algebra Require Export dfrac.
From iris.bi.lib Require Import fractional.
From iris.proofmode Require Import proofmode.
From iris.base_logic.lib Require Export own.
From iris.base_logic.lib Require Import ghost_map.
Import uPred.

(** This file provides a simple generalization of Iris' gen_sim_heap to allow for two heaps (for source and target).
  It does so by parameterizing over ghost names.
  This comes at the cost of increased TC search cost, but that should be quite manageable when there are only two instances,
  as common when proving refinements.
 *)

(** The CMRAs we need, and the global ghost names we are using. *)

Class gen_heapGpreS (L V : Type) (Σ : gFunctors) `{Countable L} := {
  gen_heap_pre_heapG :: ghost_mapG Σ L V;
  gen_heap_pre_metaG :: ghost_mapG Σ L gname;
  gen_heap_pre_dataG :: inG Σ (reservation_mapR (agreeR positiveO));
}.

Class gen_heapGS_named (L V : Type) (Σ : gFunctors) (gen_heap_name : gname) (gen_meta_name : gname)  `{Countable L} := GenHeapGSNamed {
  gen_heap_named_GpreS :: gen_heapGpreS L V Σ
}.

(** Variant for refinements between two languages *)
Class gen_sim_heapGS (L_t L_s V_t V_s : Type) (Σ : gFunctors) `{Countable L_s, Countable L_t} := GenSimHeapGS {
  gen_heap_name_target : gname;
  gen_meta_name_target : gname;
  gen_heap_name_source : gname;
  gen_meta_name_source : gname;
  gen_heap_inG_source :: gen_heapGS_named L_s V_s Σ gen_heap_name_source gen_meta_name_source;
  gen_heap_inG_target :: gen_heapGS_named L_t V_t Σ gen_heap_name_target gen_meta_name_target;
}.
Global Arguments GenSimHeapGS L_t L_s V_t V_s Σ {_ _ _ _} _ _ _ _ {_ _}.
Global Arguments gen_heap_name_source {L_t L_s V_t V_s Σ _ _ _ _} _ : assert.
Global Arguments gen_meta_name_source {L_t L_s V_t V_s Σ _ _ _ _} _ : assert.
Global Arguments gen_heap_name_target {L_t L_s V_t V_s Σ _ _ _ _} _ : assert.
Global Arguments gen_meta_name_target {L_t L_s V_t V_s Σ _ _ _ _} _ : assert.

Section definitions.
  Context `{Countable L, gen_heap_name : gname, gen_meta_name : gname, hG : !gen_heapGS_named L V Σ gen_heap_name gen_meta_name}.

  Definition gen_heap_interp (σ : gmap L V) : iProp Σ := ∃ m : gmap L gname,
    (* The [⊆] is used to avoid assigning ghost information to the locations in
    the initial heap (see [gen_heap_init]). *)
    ⌜ dom m ⊆ dom σ ⌝ ∗
    ghost_map_auth_frac gen_heap_name 1 σ ∗
    ghost_map_auth_frac gen_meta_name 1 m.

  Definition pointsto_def (l : L) (dq : dfrac) (v: V) : iProp Σ :=
    l ↪[gen_heap_name]{dq} v.
  Definition pointsto_aux : seal (@pointsto_def). Proof. by eexists. Qed.
  Definition pointsto := pointsto_aux.(unseal).
  Definition pointsto_unseal : @pointsto = @pointsto_def := pointsto_aux.(seal_eq).

  Definition meta_token_def (l : L) (E : coPset) : iProp Σ :=
    ∃ γm, l ↪[gen_meta_name]□ γm ∗ own γm (reservation_map_token E).
  Definition meta_token_aux : seal (@meta_token_def). Proof. by eexists. Qed.
  Definition meta_token := meta_token_aux.(unseal).
  Definition meta_token_unseal : @meta_token = @meta_token_def := meta_token_aux.(seal_eq).

  Definition meta_def `{Countable A} (l : L) (N : namespace) (x : A) : iProp Σ :=
    ∃ γm, l ↪[gen_meta_name]□ γm ∗
          own γm (reservation_map_data (coPpick (↑ N)) (to_agree (encode x))).
  Definition meta_aux : seal (@meta_def). Proof. by eexists. Qed.
  Definition meta := meta_aux.(unseal).
  Definition meta_unseal : @meta = @meta_def := meta_aux.(seal_eq).
End definitions.
Global Arguments meta {L _ _ _ _ V Σ _ A _ _} l N x.

(** FIXME: Refactor these notations using custom entries once Coq bug #13654
has been fixed. *)
Local Notation "l ↦{ dq } v" := (pointsto l dq v)
  (at level 20, format "l  ↦{ dq }  v") : bi_scope.
Local Notation "l ↦□ v" := (pointsto l DfracDiscarded v)
  (at level 20, format "l  ↦□  v") : bi_scope.
Local Notation "l ↦{# q } v" := (pointsto l (DfracOwn q) v)
  (at level 20, format "l  ↦{# q }  v") : bi_scope.
Local Notation "l ↦ v" := (pointsto l (DfracOwn 1) v)
  (at level 20, format "l  ↦  v") : bi_scope.

Section gen_heap.
  Context {L V} `{Countable L, gen_heap_name : gname, gen_meta_name : gname, !gen_heapGS_named L V Σ gen_heap_name gen_meta_name}.
  Implicit Types P Q : iProp Σ.
  Implicit Types Φ : V → iProp Σ.
  Implicit Types σ : gmap L V.
  Implicit Types m : gmap L gname.
  Implicit Types l : L.
  Implicit Types v : V.

  (** General properties of pointsto *)
  Global Instance pointsto_timeless l dq v : Timeless (l ↦{dq} v).
  Proof. rewrite pointsto_unseal. apply _. Qed.
  Global Instance pointsto_fractional l v : Fractional (λ q, l ↦{#q} v)%I.
  Proof. rewrite pointsto_unseal. apply _. Qed.
  Global Instance pointsto_as_fractional l q v :
    AsFractional (l ↦{#q} v) (λ q, l ↦{#q} v)%I q.
  Proof. split; [done|]. apply _. Qed.
  Global Instance pointsto_persistent l v : Persistent (l ↦□ v).
  Proof. rewrite pointsto_unseal. apply _. Qed.

  Lemma pointsto_valid l dq v : l ↦{dq} v -∗ ⌜✓ dq⌝%Qp.
  Proof. rewrite pointsto_unseal. apply ghost_map_elem_valid. Qed.
  Lemma pointsto_valid_2 l dq1 dq2 v1 v2 : l ↦{dq1} v1 -∗ l ↦{dq2} v2 -∗ ⌜✓ (dq1 ⋅ dq2) ∧ v1 = v2⌝.
  Proof. rewrite pointsto_unseal. apply ghost_map_elem_valid_2. Qed.
  (** Almost all the time, this is all you really need. *)
  Lemma pointsto_agree l dq1 dq2 v1 v2 : l ↦{dq1} v1 -∗ l ↦{dq2} v2 -∗ ⌜v1 = v2⌝.
  Proof. rewrite pointsto_unseal. apply ghost_map_elem_agree. Qed.

  Global Instance pointsto_combine_sep_gives l dq1 dq2 v1 v2 :
    CombineSepGives (l ↦{dq1} v1) (l ↦{dq2} v2) ⌜✓ (dq1 ⋅ dq2) ∧ v1 = v2⌝ | 30.
  Proof.
    rewrite /CombineSepGives. iIntros "[H1 H2]".
    iDestruct (pointsto_valid_2 with "H1 H2") as %?. eauto.
  Qed.

  Lemma pointsto_combine l dq1 dq2 v1 v2 :
    l ↦{dq1} v1 -∗ l ↦{dq2} v2 -∗ l ↦{dq1 ⋅ dq2} v1 ∗ ⌜v1 = v2⌝.
  Proof. rewrite pointsto_unseal. apply ghost_map_elem_combine. Qed.

  Global Instance pointsto_combine_as l dq1 dq2 v1 v2 :
    CombineSepAs (l ↦{dq1} v1) (l ↦{dq2} v2) (l ↦{dq1 ⋅ dq2} v1) | 60.
    (* higher cost than the Fractional instance, which kicks in for #qs *)
  Proof.
    rewrite /CombineSepAs. iIntros "[H1 H2]".
    iDestruct (pointsto_combine with "H1 H2") as "[$ _]".
  Qed.

  Lemma pointsto_frac_ne l1 l2 dq1 dq2 v1 v2 :
    ¬ ✓(dq1 ⋅ dq2) → l1 ↦{dq1} v1 -∗ l2 ↦{dq2} v2 -∗ ⌜l1 ≠ l2⌝.
  Proof. rewrite pointsto_unseal. apply ghost_map_elem_frac_ne. Qed.
  Lemma pointsto_ne l1 l2 dq2 v1 v2 : l1 ↦ v1 -∗ l2 ↦{dq2} v2 -∗ ⌜l1 ≠ l2⌝.
  Proof. rewrite pointsto_unseal. apply ghost_map_elem_ne. Qed.

  (** Permanently turn any points-to predicate into a persistent
      points-to predicate. *)
  Lemma pointsto_persist l dq v : l ↦{dq} v ==∗ l ↦□ v.
  Proof. rewrite pointsto_unseal. apply ghost_map_elem_persist. Qed.

  (** Recover fractional ownership for read-only element. *)
  Lemma pointsto_unpersist l v :
    l ↦□ v ==∗ ∃ q, l ↦{# q} v.
  Proof. rewrite pointsto_unseal. apply ghost_map_elem_unpersist. Qed.

  (** Framing support *)
  Global Instance frame_pointsto p l v q1 q2 q :
    FrameFractionalQp q1 q2 q →
    Frame p (l ↦{#q1} v) (l ↦{#q2} v) (l ↦{#q} v) | 5.
  Proof. apply: frame_fractional. Qed.

  (** General properties of [meta] and [meta_token] *)
  Global Instance meta_token_timeless l N : Timeless (meta_token l N).
  Proof. rewrite meta_token_unseal. apply _. Qed.
  Global Instance meta_timeless `{Countable A} l N (x : A) : Timeless (meta l N x).
  Proof. rewrite meta_unseal. apply _. Qed.
  Global Instance meta_persistent `{Countable A} l N (x : A) : Persistent (meta l N x).
  Proof. rewrite meta_unseal. apply _. Qed.

  Lemma meta_token_union_1 l E1 E2 :
    E1 ## E2 → meta_token l (E1 ∪ E2) -∗ meta_token l E1 ∗ meta_token l E2.
  Proof.
    rewrite meta_token_unseal /meta_token_def. intros ?. iDestruct 1 as (γm1) "[#Hγm Hm]".
    rewrite reservation_map_token_union //. iDestruct "Hm" as "[Hm1 Hm2]".
    iSplitL "Hm1"; eauto.
  Qed.
  Lemma meta_token_union_2 l E1 E2 :
    meta_token l E1 -∗ meta_token l E2 -∗ meta_token l (E1 ∪ E2).
  Proof.
    rewrite meta_token_unseal /meta_token_def.
    iIntros "(%γm1 & #Hγm1 & Hm1) (%γm2 & #Hγm2 & Hm2)".
    iCombine "Hγm1 Hγm2" gives %[_ ->].
    iCombine "Hm1 Hm2" gives %?%reservation_map_token_valid_op.
    iExists γm2. iFrame "Hγm2". rewrite reservation_map_token_union //. by iSplitL "Hm1".
  Qed.
  Lemma meta_token_union l E1 E2 :
    E1 ## E2 → meta_token l (E1 ∪ E2) ⊣⊢ meta_token l E1 ∗ meta_token l E2.
  Proof.
    intros; iSplit; first by iApply meta_token_union_1.
    iIntros "[Hm1 Hm2]". by iApply (meta_token_union_2 with "Hm1 Hm2").
  Qed.

  Lemma meta_token_difference l E1 E2 :
    E1 ⊆ E2 → meta_token l E2 ⊣⊢ meta_token l E1 ∗ meta_token l (E2 ∖ E1).
  Proof.
    intros. rewrite {1}(union_difference_L E1 E2) //.
    by rewrite meta_token_union; last set_solver.
  Qed.

  Lemma meta_agree `{Countable A} l i (x1 x2 : A) :
    meta l i x1 -∗ meta l i x2 -∗ ⌜x1 = x2⌝.
  Proof.
    rewrite meta_unseal /meta_def.
    iIntros "(%γm1 & Hγm1 & Hm1) (%γm2 & Hγm2 & Hm2)".
    iCombine "Hγm1 Hγm2" gives %[_ ->].
    iCombine "Hm1 Hm2" gives %Hγ; iPureIntro.
    move: Hγ. rewrite -reservation_map_data_op reservation_map_data_valid.
    move=> /to_agree_op_inv_L. naive_solver.
  Qed.
  Lemma meta_set `{Countable A} E l (x : A) N :
    ↑ N ⊆ E → meta_token l E ==∗ meta l N x.
  Proof.
    rewrite meta_token_unseal meta_unseal /meta_token_def /meta_def.
    iDestruct 1 as (γm) "[Hγm Hm]". iExists γm. iFrame "Hγm".
    iApply (own_update with "Hm").
    apply reservation_map_alloc; last done.
    pose proof (coPpick_elem_of (↑ N) (nclose_non_empty _)); set_solver.
  Qed.

  (** Update lemmas *)
  Lemma gen_heap_alloc σ l v :
    σ !! l = None →
    gen_heap_interp σ ==∗ gen_heap_interp (<[l:=v]>σ) ∗ l ↦ v ∗ meta_token l ⊤.
  Proof.
    iIntros (Hσl). rewrite /gen_heap_interp pointsto_unseal /pointsto_def
      meta_token_unseal /meta_token_def /=.
    iDestruct 1 as (m Hσm) "[Hσ Hm]".
    iMod (ghost_map_insert l with "Hσ") as "[Hσ Hl]"; first done.
    iMod (own_alloc (reservation_map_token ⊤)) as (γm) "Hγm".
    { apply reservation_map_token_valid. }
    iMod (ghost_map_insert_persist l with "Hm") as "[Hm Hlm]".
    { move: Hσl. rewrite -!not_elem_of_dom. set_solver. }
    iModIntro. iFrame "Hl". iSplitL "Hσ Hm"; last by eauto with iFrame.
    iExists (<[l:=γm]> m). iFrame. iPureIntro.
    rewrite !dom_insert_L. set_solver.
  Qed.

  Lemma gen_heap_alloc_big σ σ' :
    σ' ##ₘ σ →
    gen_heap_interp σ ==∗
    gen_heap_interp (σ' ∪ σ) ∗ ([∗ map] l ↦ v ∈ σ', l ↦ v) ∗ ([∗ map] l ↦ _ ∈ σ', meta_token l ⊤).
  Proof.
    revert σ; induction σ' as [| l v σ' Hl IH] using map_ind; iIntros (σ Hdisj) "Hσ".
    { rewrite left_id_L. auto. }
    iMod (IH with "Hσ") as "[Hσ'σ Hσ']"; first by eapply map_disjoint_insert_l.
    decompose_map_disjoint.
    rewrite !big_opM_insert // -insert_union_l //.
    by iMod (gen_heap_alloc with "Hσ'σ") as "($ & $ & $)";
      first by apply lookup_union_None.
  Qed.

  Lemma gen_heap_valid σ l dq v : gen_heap_interp σ -∗ l ↦{dq} v -∗ ⌜σ !! l = Some v⌝.
  Proof.
    iDestruct 1 as (m Hσm) "[Hσ _]". iIntros "Hl".
    rewrite /gen_heap_interp pointsto_unseal.
    by iCombine "Hσ Hl" gives %?.
  Qed.

  Lemma gen_heap_update σ l v1 v2 :
    gen_heap_interp σ -∗ l ↦ v1 ==∗ gen_heap_interp (<[l:=v2]>σ) ∗ l ↦ v2.
  Proof.
    iDestruct 1 as (m Hσm) "[Hσ Hm]".
    iIntros "Hl". rewrite /gen_heap_interp pointsto_unseal /pointsto_def.
    iCombine "Hσ Hl" gives %Hl.
    iMod (ghost_map_update with "Hσ Hl") as "[Hσ Hl]".
    iModIntro. iFrame "Hl". iExists m. iFrame.
    iPureIntro. apply elem_of_dom_2 in Hl.
    rewrite dom_insert_L. set_solver.
  Qed.
End gen_heap.

(** This variant of [gen_heap_init] should only be used when absolutely needed.
The key difference to [gen_heap_init] is that the [inG] instances in the new
[gen_heapGS] instance are related to the original [gen_heapGpreS] instance,
whereas [gen_heap_init] forgets about that relation. *)
Lemma gen_heap_init_names `{Countable L, !gen_heapGpreS L V Σ} σ :
  ⊢ |==> ∃ γh γm : gname,
    let hG := GenHeapGSNamed L V Σ γh γm in
    gen_heap_interp σ ∗ ([∗ map] l ↦ v ∈ σ, l ↦ v) ∗ ([∗ map] l ↦ _ ∈ σ, meta_token l ⊤).
Proof.
  iMod (ghost_map_alloc_empty (K:=L) (V:=V)) as (γh) "Hh".
  iMod (ghost_map_alloc_empty (K:=L) (V:=gname)) as (γm) "Hm".
  iExists γh, γm.
  iAssert (gen_heap_interp (hG:=GenHeapGSNamed _ _ _ γh γm _ _ _) ∅) with "[Hh Hm]" as "Hinterp".
  { iExists ∅; simpl. iFrame "Hh Hm". by rewrite dom_empty_L. }
  iMod (gen_heap_alloc_big with "Hinterp") as "(Hinterp & $ & $)".
  { apply map_disjoint_empty_r. }
  rewrite right_id_L. done.
Qed.

(** FIXME: as one would expect, we have to give the instances explicitly here.
  Is there a more elegant way? *)
Lemma gen_sim_heap_init `{Countable L_t, Countable L_s, !gen_heapGpreS L_t V_t Σ, !gen_heapGpreS L_s V_s Σ} (σ_t : gmap L_t V_t) (σ_s : gmap L_s V_s) :
  ⊢ |==> ∃ _ : gen_sim_heapGS L_t L_s V_t V_s Σ,
      (gen_heap_interp (hG := gen_heap_inG_target) σ_t ∗
      ([∗ map] l ↦ v ∈ σ_t, pointsto (hG := gen_heap_inG_target) l (DfracOwn 1) v) ∗
      ([∗ map] l ↦ _ ∈ σ_t, meta_token (hG := gen_heap_inG_target) l ⊤)) ∗
      (gen_heap_interp (hG := gen_heap_inG_source) σ_s ∗
      ([∗ map] l ↦ v ∈ σ_s, pointsto (hG := gen_heap_inG_source) l (DfracOwn 1) v) ∗
      ([∗ map] l ↦ _ ∈ σ_s, meta_token (hG := gen_heap_inG_source) l ⊤)).
Proof.
  iMod (gen_heap_init_names σ_t) as (γh_t γm_t) "Hinit_target".
  iMod (gen_heap_init_names σ_s) as (γh_s γm_s) "Hinit_source".
  iExists (GenSimHeapGS _ _ _ _ _ γh_t γm_t γh_s γm_s).
  iModIntro. iFrame.
Qed.
