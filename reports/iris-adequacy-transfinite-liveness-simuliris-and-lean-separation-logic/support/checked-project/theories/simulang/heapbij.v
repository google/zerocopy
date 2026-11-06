(** * Library for defining a bijection between source and target heaps

    This file provides the ghost state for establishing a bijection
    between source and target heaps.  *)

From iris.algebra.lib Require Import gset_bij.
From iris.proofmode Require Import proofmode.
From iris.bi.lib Require Import fractional .
From iris.base_logic.lib Require Import ghost_map gset_bij.

From simuliris.base_logic Require Import gen_sim_heap gen_sim_prog.
From simuliris.simulation Require Import slsls lifting.
From simuliris.simulang Require Import notation gen_val_rel primitive_laws.


Class heapbijGS (Σ : gFunctors) := HeapBijGS {
  heapbijG_bijG :: gset_bijG Σ block block;
  heapbijG_bij_name : gname;
}.
Class heapbijGpreS (Σ: gFunctors) := HeapBijGpreS {
  sbij_pre_progG :: gset_bijG Σ block block;
}.
Definition heapbijΣ := #[gset_bijΣ block block].
Global Instance subG_heapbijΣ Σ :
  subG heapbijΣ Σ → heapbijGpreS Σ.
Proof. solve_inG. Qed.

Section definitions.
  Context `{heapbijGS Σ}.

  Definition heapbij_auth (L : gset (block * block)) :=
    gset_bij_own_auth heapbijG_bij_name (DfracOwn 1) L.
  Definition block_rel (l_t : block) (l_s : block) :=
    gset_bij_own_elem heapbijG_bij_name l_t l_s.
End definitions.

Definition loc_rel `{heapbijGS Σ} l_t l_s : iProp Σ :=
  block_rel (loc_block l_t) (loc_block l_s) ∗ ⌜loc_idx l_t = loc_idx l_s⌝.
Notation "l_t '↔h' l_s" := (loc_rel l_t l_s) (at level 30) : bi_scope.
Local Notation val_rel := (gen_val_rel loc_rel).

Section laws.
  Context `{!heapbijGS Σ}.
  Implicit Types (b_t b_s : block) (l_t l_s : loc).

  Global Instance block_rel_persistent b_t b_s :
    Persistent (block_rel b_t b_s).
  Proof. apply _. Qed.
  Global Instance loc_rel_persistent l_t l_s :
    Persistent (l_t ↔h l_s).
  Proof. apply _. Qed.

  Lemma heapbij_agree b_t1 b_t2 b_s1 b_s2 :
    block_rel b_t1 b_s1 -∗ block_rel b_t2 b_s2 -∗ ⌜b_t1 = b_t2 ↔ b_s1 = b_s2⌝.
  Proof.
    iIntros "H1 H2". iApply (gset_bij_own_elem_agree with "H1 H2").
  Qed.
  Lemma heapbij_loc_agree l_t1 l_t2 l_s1 l_s2 :
    l_t1 ↔h l_s1 -∗ l_t2 ↔h l_s2 -∗ ⌜l_t1 = l_t2 ↔ l_s1 = l_s2⌝.
  Proof.
    iIntros "[H1 %Heq1] [H3 %Heq2]".
    iPoseProof (heapbij_agree with "H1 H3") as "%Ha". iPureIntro.
    destruct l_t1, l_t2, l_s1, l_s2; cbn in *; subst. naive_solver.
  Qed.

  Lemma heapbij_func b_t b_s1 b_s2 :
    block_rel b_t b_s1 -∗ block_rel b_t b_s2 -∗ ⌜b_s1 = b_s2⌝.
  Proof.
    iIntros "H1 H2". iPoseProof (heapbij_agree with "H1 H2") as "<-"; done.
  Qed.
  Lemma heapbij_loc_func l_t l_s1 l_s2 :
    l_t ↔h l_s1 -∗ l_t ↔h l_s2 -∗ ⌜l_s1 = l_s2⌝.
  Proof.
    iIntros "H1 H2". iPoseProof (heapbij_loc_agree with "H1 H2") as "<-"; done.
  Qed.

  Lemma heapbij_inj b_s b_t1 b_t2 :
    block_rel b_t1 b_s -∗ block_rel b_t2 b_s -∗ ⌜b_t1 = b_t2⌝.
  Proof.
    iIntros "H1 H2". iPoseProof (heapbij_agree with "H1 H2") as "->"; done.
  Qed.
  Lemma heapbij_loc_inj l_s l_t1 l_t2 :
    l_t1 ↔h l_s -∗ l_t2 ↔h l_s -∗ ⌜l_t1 = l_t2⌝.
  Proof.
    iIntros "H1 H2". iPoseProof (heapbij_loc_agree with "H1 H2") as "->"; done.
  Qed.

  Lemma heapbij_loc_shift l_t l_s i : l_t ↔h l_s -∗ (l_t +ₗ i) ↔h (l_s +ₗ i).
  Proof.
    iIntros "[Hi %Hj]". iSplitL "Hi"; first done. iPureIntro.
    destruct l_t, l_s; cbn in *; lia.
  Qed.
End laws.

Section definitions.
  Context `{!heapbijGS Σ, !sheapGS Σ}.

  (** [P l_t l_s q] can be used to remove and add fractions of the
  points-to predicate from the bijection. [alloc_rel] stores a proof
  that [P l_t l_s q] holds for the fraction that it currently contains. *)
  Definition alloc_rel b_t b_s P : iProp Σ :=
    (∃ (n : option nat) vs_t vs_s,
        ⌜length vs_t = default 0 n⌝ ∗
        ⌜block_is_dyn b_t ↔ block_is_dyn b_s⌝ ∗
      ([∗ list] i↦v_t;v_s∈vs_t;vs_s,
          (∃ st q, ⌜P (Loc b_t i) (Loc b_s i) q⌝ ∗ val_rel v_t v_s ∗
                    if q is Some q' then
                      (Loc b_t i)↦t[st]{#q'} v_t ∗ (Loc b_s i)↦s[st]{#q'} v_s
                    else
                      True)) ∗
      target_block_size (Loc b_t 0) n ∗
      source_block_size (Loc b_s 0) n).

  Lemma alloc_rel_mono (P' P : _ → _ → _ → Prop) b_t b_s:
    (∀ q o, P (Loc b_t o) (Loc b_s o) q → P' (Loc b_t o) (Loc b_s o) q) →
    alloc_rel b_t b_s P -∗
    alloc_rel b_t b_s P'.
  Proof.
    iIntros (HP) "(%n&%vs_s&%vs_t&%&%&Hvs&?)".
    iExists _, _, _. iFrame. iSplit; [done|]. iSplit; [done|].
    iApply (big_sepL2_impl with "Hvs").
    iIntros "!>" (?????) "(%st&%q&%&?&?)".
    iExists _, q. iFrame. iPureIntro. by apply: HP.
  Qed.

  Lemma alloc_rel_read (b : bool) b_t b_s σ_s σ_t o v st (P : _ → _ → _ → Prop):
    heap σ_s !! Loc b_s o = Some (st, v) →
    (∀ q, P (Loc b_t o) (Loc b_s o) q → ∃ q', q = Some q' ∧ if b then q' = 1%Qp else True) →
    alloc_rel b_t b_s P -∗
    heap_ctx sheapG_heap_source σ_s -∗
    heap_ctx sheapG_heap_target σ_t -∗
    ∃ st' v', ⌜heap σ_t !! Loc b_t o = Some (st', v')⌝ ∗ ⌜if b then st' = st else if st is RSt _ then ∃ n', st' = RSt n' else st' = WSt⌝ ∗ val_rel v' v.
  Proof.
    iIntros (? HP).
    iDestruct 1 as (? vs_t vs_s Hlen Hb) "(Hl_s & Halloc_t & Halloc_s)".
    iIntros "Hσ_s Hσ_t".
    iDestruct (big_sepL2_length with "Hl_s") as %?.

    iDestruct (heap_block_size_lookup with "Hσ_s Halloc_s") as %[n' [? Hl]]; [done..|].
    rewrite Loc_add in Hl. move: Hl => [] ?; simplify_eq/=.
    have [v_s Hv_s]:= lookup_lt_is_Some_2 vs_s n' ltac:(lia).
    have [v_t Hv_t]:= lookup_lt_is_Some_2 vs_t n' ltac:(lia).
    iDestruct (big_sepL2_insert_acc with "Hl_s") as "[(%st''&%q'&%HP'&Hv&Hl_s) Hclose]"; [done..|].
    have [?[??]] := HP _ HP'. subst.
    iDestruct "Hl_s" as "[Hl_t Hl_s]".
    case_match; subst.
    - iDestruct (heap_read_st_1 with "Hσ_s Hl_s") as %Hl_s.
      iDestruct (heap_read_st_1 with "Hσ_t Hl_t") as %Hl_t.
      simplify_eq/=.
      iExists _, _. by repeat (iSplitR; [done|]).
    - iDestruct (heap_read_st with "Hσ_s Hl_s") as %[? Hl_s].
      iDestruct (heap_read_st with "Hσ_t Hl_t") as %[? Hl_t]. simplify_eq.
      iExists _, _. iFrame "Hv". iSplit; [done|]. iPureIntro. case_match; naive_solver.
  Qed.

  Lemma alloc_rel_write b_t b_s σ_s σ_t o v st st' v_s' v_t' (P : _ → _ → _ → Prop):
    heap σ_s !! Loc b_s o = Some (st, v) →
    (∀ q, P (Loc b_t o) (Loc b_s o) q → q = Some 1%Qp) →
    alloc_rel b_t b_s P -∗
    heap_ctx sheapG_heap_source σ_s -∗
    heap_ctx sheapG_heap_target σ_t -∗
    val_rel v_t' v_s' ==∗
    alloc_rel b_t b_s P ∗
    heap_ctx sheapG_heap_source (state_upd_heap <[Loc b_s o := (st', v_s')]> σ_s) ∗
    heap_ctx sheapG_heap_target (state_upd_heap <[Loc b_t o := (st', v_t')]> σ_t).
  Proof.
    iIntros (? HP).
    iDestruct 1 as (n vs_t vs_s Hlen Hb) "(Hl_s & Halloc_t & Halloc_s)".
    iIntros "Hσ_s Hσ_t Hval".
    iDestruct (big_sepL2_length with "Hl_s") as %?.

    iDestruct (heap_block_size_lookup with "Hσ_s Halloc_s") as %[n' [? Hl]]; [done..|].
    rewrite Loc_add in Hl. move: Hl => [] ?; simplify_eq/=.
    have [v_s Hv_s]:= lookup_lt_is_Some_2 vs_s n' ltac:(lia).
    have [v_t Hv_t]:= lookup_lt_is_Some_2 vs_t n' ltac:(lia).
    iDestruct (big_sepL2_insert_acc with "Hl_s") as "[(%st''&%q'&%HP'&Hv'&Hl_s) Hclose]"; [done..|].
    have ? := HP _ HP'. subst.
    iDestruct "Hl_s" as "[Hl_t Hl_s]".
    iDestruct (heap_read_st_1 with "Hσ_s Hl_s") as %Hl_s.
    iDestruct (heap_read_st_1 with "Hσ_t Hl_t") as %Hl_t.
    simplify_eq/=.

    iMod (heap_write with "Hσ_s Hl_s") as "[$ Hl_s]".
    iMod (heap_write with "Hσ_t Hl_t") as "[$ Hl_t]".
    iModIntro.
    iExists _, _, _.
    iFrame "Halloc_t Halloc_s".
    iSplitR; [|iSplit; [done|]]; last first.
    - iApply "Hclose". iExists _, (Some _). by iFrame.
    - iPureIntro. rewrite length_insert. lia.
  Qed.

  Lemma alloc_rel_free b_t b_s n σ_s σ_t o (P : _ → _ → _ → Prop):
    (0 < n)%Z →
    block_is_dyn b_s →
    (∀ m : Z, is_Some (heap σ_s !! (Loc b_s o +ₗ m)) ↔ (0 ≤ m < n)%Z) →
    (∀ q k, (0 ≤ k < n)%Z → P (Loc b_t o +ₗ k) (Loc b_s o +ₗ k) q → q = Some 1%Qp) →
    alloc_rel b_t b_s P -∗
    heap_ctx sheapG_heap_source σ_s -∗
    heap_ctx sheapG_heap_target σ_t
    ==∗
    ⌜block_is_dyn b_t⌝ ∗
    ⌜∀ m, is_Some (heap σ_t !! (Loc b_t o +ₗ m)) ↔ (0 ≤ m < n)%Z⌝ ∗
    alloc_rel b_t b_s P ∗
    heap_ctx sheapG_heap_source (state_upd_heap (free_mem (Loc b_s o) (Z.to_nat n)) σ_s) ∗
    heap_ctx sheapG_heap_target (state_upd_heap (free_mem (Loc b_t o) (Z.to_nat n)) σ_t).
  Proof.
    iIntros (??? HP).
    iDestruct 1 as (n' vs_t vs_s Hlen Hb) "(Hvs & Ha_t & Ha_s)".
    iIntros "Hσ_s Hσ_t".
    iDestruct (big_sepL2_length with "Hvs") as %Hlen'.
    iDestruct (heap_block_size_inj with "Hσ_s Ha_s") as %[? Hl]; [done..|]. move: Hl => [?]. subst.

    iAssert (∃ sts, Loc b_t 0 ↦t∗[sts] vs_t ∗ Loc b_s 0 ↦s∗[sts] vs_s)%I with "[Hvs]" as (?) "[Hl_t Hl_s]". {
      iDestruct (big_sepL2_exist with "Hvs") as (sts ?) "Hvs". iExists sts.
      rewrite /heap_pointsto_vec_st !(big_sepL2_to_sepL_r sts) -?big_sepL2_sepL; [|congruence..].
      iApply (big_sepL2_impl with "Hvs").
      iIntros "!>" (k x1 x2 Ht Hs) "(%st & % & %q & %Hrel & Hv & Hl)".
      change (Loc b_s k) with (Loc b_s 0 +ₗ k) in Hrel.
      move/HP in Hrel. rewrite Hrel.
      2: { split; [lia|]. rewrite /= in Hlen. move/(lookup_lt_Some _ _ _) in Ht. lia. }
      iDestruct "Hl" as "[Hl_t Hl_s]".
      iSplitL "Hl_t"; iExists _; by iFrame.
    }
    iMod (heap_free with "Hσ_t Hl_t [Ha_t]") as (? Hlookup) "[Ha_t Hσ_t]"; [ by rewrite Hlen /= | naive_solver | by rewrite Hlen |].
    iMod (heap_free with "Hσ_s Hl_s [Ha_s]") as (_ _) "[Ha_s Hσ_s]"; [done| naive_solver| by rewrite -Hlen' Hlen |].
    rewrite -Hlen' Hlen Z2Nat.id; [|lia]. iFrame. iModIntro. iSplit; [naive_solver|].
    rewrite Z2Nat.id in Hlookup; [|lia]. iSplit; [done|].
    iExists [], []. by simpl.
  Qed.

  Lemma alloc_rel_P_holds (P : _ → _ → _ → Prop) b_t b_s σ_s o s:
    heap σ_s !! Loc b_s o = Some s →
    alloc_rel b_t b_s P -∗
    heap_ctx sheapG_heap_source σ_s -∗
    ⌜∃ q, P (Loc b_t o) (Loc b_s o) q⌝%Qp.
  Proof.
    iIntros (?).
    iDestruct 1 as (? vs_t vs_s Hlen Hb) "(Hl_s & Halloc_t & Halloc_s)".
    iIntros "Hσ_s".
    iDestruct (big_sepL2_length with "Hl_s") as %?.

    iDestruct (heap_block_size_lookup with "Hσ_s Halloc_s") as %[n' [? Hl]]; [done..|].
    rewrite Loc_add in Hl. move: Hl => [] ?; simplify_eq/=.
    have [v_s Hv_s]:= lookup_lt_is_Some_2 vs_s n' ltac:(lia).
    have [v_t Hv_t]:= lookup_lt_is_Some_2 vs_t n' ltac:(lia).
    iDestruct (big_sepL2_insert_acc with "Hl_s") as "[(%st''&%q'&%HP'&Hl_s) _]"; [done..|].
    iPureIntro. naive_solver.
  Qed.

  Lemma alloc_rel_remove_frac (P' P : _ → _ → _ → Prop) q1 q2 qd b_t b_s σ_s o v_s st:
    heap σ_s !! Loc b_s o = Some (RSt st, v_s) →
    (∀ q, P (Loc b_t o) (Loc b_s o) q → q = Some q1) →
    P' (Loc b_t o) (Loc b_s o) q2 →
    (∀ q o', o ≠ o' → P (Loc b_t o') (Loc b_s o') q → P' (Loc b_t o') (Loc b_s o') q) →
    (if q2 is Some q2' then q1 = qd + q2' else q1 = qd)%Qp →
    (q2 = None → st = 0) →
    alloc_rel b_t b_s P -∗
    heap_ctx sheapG_heap_source σ_s
    ==∗
    ∃ v_t,
      (Loc b_t o)↦t{#qd}v_t ∗
      (Loc b_s o)↦s{#qd}v_s ∗
      val_rel v_t v_s ∗
      alloc_rel b_t b_s P' ∗
      heap_ctx sheapG_heap_source σ_s.
  Proof.
    iIntros (? Hq1 Hq2 Hsame Hdiff Hst0).
    iDestruct 1 as (n vs_t vs_s Hlen Hb) "(Hvs & Halloc_t & Halloc_s)".
    iIntros "Hσ_s".
    iDestruct (big_sepL2_length with "Hvs") as %?.

    iDestruct (heap_block_size_lookup with "Hσ_s Halloc_s") as %[n' [? Hl]]; [done..|].
    rewrite Loc_add in Hl. move: Hl => [] ?; simplify_eq/=.
    have [v_s' Hv_s]:= lookup_lt_is_Some_2 vs_s n' ltac:(lia).
    have [v_t Hv_t]:= lookup_lt_is_Some_2 vs_t n' ltac:(lia).
    have Hv_s':= take_drop_middle _ _ _ Hv_s.
    have Hv_t':= take_drop_middle _ _ _ Hv_t.
    rewrite -{1}Hv_s' -{1}Hv_t' big_sepL2_app_same_length /= ?length_take_le ?Nat.add_0_r; [|lia..].
    iDestruct "Hvs" as "(Hvs_1&Hl&Hvs_2)".
    iDestruct "Hl" as (st' q ?%Hq1) "[#Hv Hp]". subst.
    iDestruct "Hp" as "[Hl_t Hl_s]".
    iDestruct (heap_read_st with "Hσ_s Hl_s") as %[??]; destruct st' as [|n'']; simplify_eq/=.

    destruct q2; subst.
    - iDestruct (heap_pointsto_split _ _ _ _ 0 with "Hl_t") as "[Hl_t1 Hl_t2]"; [done..|].
      iDestruct (heap_pointsto_split _ _ _ _ 0 with "Hl_s") as "[Hl_s1 Hl_s2]"; [done..|].
      iModIntro.
      iExists _. iFrame "∗Hv".
      iExists vs_t, vs_s. iSplit; [done|]. iSplit; [done|].
      rewrite -{3}Hv_s' -{3}Hv_t' big_sepL2_app_same_length /= ?length_take_le ?Nat.add_0_r; [|lia..].
      iSplitL "Hvs_1"; [|iSplitR "Hvs_2"].
      + iApply (big_sepL2_impl with "Hvs_1").
        iIntros "!>" (??? ?%lookup_take_Some ?%lookup_take_Some) "[%s [%q' [% Hp]]]".
        iExists s, q'. iFrame. iPureIntro.
        apply: Hsame; [lia| done].
      + iExists _, _. iSplit; [done|]. by iFrame.
      + iApply (big_sepL2_impl with "Hvs_2").
        iIntros "!>" (??? ??) "[%s [%q' [% Hp]]]".
        iExists s, q'. iFrame. iPureIntro.
        apply: Hsame; [lia |done].
    - have ->: n'' = 0 by naive_solver lia.
      iModIntro.
      iExists _. iFrame "∗Hv".
      iExists vs_t, vs_s. iSplit; [done|]. iSplit; [done|].
      rewrite -{3}Hv_s' -{3}Hv_t' big_sepL2_app_same_length /= ?length_take_le ?Nat.add_0_r; [|lia..].
      iSplitL "Hvs_1"; [|iSplitR "Hvs_2"].
      + iApply (big_sepL2_impl with "Hvs_1").
        iIntros "!>" (??? ?%lookup_take_Some ?%lookup_take_Some) "[%s [%q' [% Hp]]]".
        iExists s, q'. iFrame. iPureIntro.
        apply: Hsame; [lia|done].
      + iExists _, _. iSplit; [done|] => /=. iFrame "Hv".
      + iApply (big_sepL2_impl with "Hvs_2").
        iIntros "!>" (??? ??) "[%s [%q' [% Hp]]]".
        iExists s, q'. iFrame. iPureIntro.
        apply: Hsame; [lia|done].
        Unshelve.
        apply: WSt.
  Qed.

  Lemma alloc_rel_add_frac (P' P : _ → _ → _ → Prop) q b_t b_s σ_s o v_s v_t:
    (∀ q', P (Loc b_t o) (Loc b_s o) q' → P' (Loc b_t o) (Loc b_s o) (Some (if q' is Some q'' then (q + q'')%Qp else q))) →
    (∀ q o', o ≠ o' → P (Loc b_t o') (Loc b_s o') q → P' (Loc b_t o') (Loc b_s o') q) →
    alloc_rel b_t b_s P -∗
    (Loc b_t o)↦t{#q}v_t -∗
    (Loc b_s o)↦s{#q}v_s -∗
    val_rel v_t v_s -∗
    heap_ctx sheapG_heap_source σ_s
    ==∗
      alloc_rel b_t b_s P' ∗
      heap_ctx sheapG_heap_source σ_s.
  Proof.
    iIntros (Hq Hsame).
    iDestruct 1 as (n vs_t vs_s Hlen Hb) "(Hvs & Halloc_t & Halloc_s)".
    iIntros "Hl_t Hl_s Hv Hσ_s".
    iDestruct (big_sepL2_length with "Hvs") as %?.

    iDestruct (heap_read with "Hσ_s Hl_s") as %[??].
    iDestruct (heap_block_size_lookup with "Hσ_s Halloc_s") as %[n' [? Hl]]; [done..|].
    rewrite Loc_add in Hl. move: Hl => [] ?; simplify_eq/=.
    have [v_s' Hv_s]:= lookup_lt_is_Some_2 vs_s n' ltac:(lia).
    have [v_t' Hv_t]:= lookup_lt_is_Some_2 vs_t n' ltac:(lia).
    have Hv_s':= take_drop_middle _ _ _ Hv_s.
    have Hv_t':= take_drop_middle _ _ _ Hv_t.
    rewrite -{1}Hv_s' -{1}Hv_t' big_sepL2_app_same_length /= ?length_take_le ?Nat.add_0_r; [|lia..].
    iDestruct "Hvs" as "(Hvs_1&Hl&Hvs_2)".
    iDestruct "Hl" as (st' q' ?) "[Hv' Hp]". subst.

    iModIntro. iFrame.
    iExists (<[n' := v_t]>vs_t), (<[n' := v_s]>vs_s).
    iSplit. { by rewrite length_insert. } iSplit; [done|].
    rewrite !insert_take_drop; [|by apply: lookup_lt_Some..].
    rewrite big_sepL2_app_same_length /= ?length_take_le ?Nat.add_0_r; [|lia..]. iFrame.
    iSplitL "Hvs_1"; [|iSplitR "Hvs_2"].
    - iApply (big_sepL2_impl with "Hvs_1").
      iIntros "!>" (??? ?%lookup_take_Some ?%lookup_take_Some) "[%s [%q'' [% Hp]]]".
      iExists s, q''. iFrame. iPureIntro.
      apply: Hsame; [lia| done].
    - iExists (if q' then st' else RSt 0), (Some (if q' is Some q'' then q + q'' else q))%Qp.
      iSplit; first by eauto.
      destruct q'; iFrame.
      iDestruct "Hp" as "[Hp1 Hp2]".
      iDestruct (heap_pointsto_agree with "[$Hp1 $Hl_t]") as %->.
      iDestruct (heap_pointsto_agree with "[$Hp2 $Hl_s]") as %->.
      iDestruct (heap_pointsto_combine_0 with "Hl_t Hp1") as "$".
      iDestruct (heap_pointsto_combine_0 with "Hl_s Hp2") as "$".
    - iApply (big_sepL2_impl with "Hvs_2").
      iIntros "!>" (??? ??) "[%s [%q'' [% Hp]]]".
      iExists s, q''. iFrame. iPureIntro.
      apply: Hsame; [lia |done].
  Qed.

  Definition heapbij_interp (L : gset (block * block)) (P : loc → loc → option Qp → Prop)  :=
    (heapbij_auth L ∗ [∗ set] p ∈ L, let '(b_t, b_s) := p in alloc_rel b_t b_s P)%I.
End definitions.

Lemma heapbij_init `{!heapbijGpreS Σ, !sheapGS Σ} P :
  ⊢ |==> ∃ `(heapbijGS Σ), heapbij_interp ∅ P.
Proof.
  iMod (gset_bij_own_alloc (A:=block) (B:=block) ∅) as (γbij) "[Hbij _]".
  { apply: gset_bijective_empty. }
  iIntros "!>". iExists (HeapBijGS _ _ γbij). iFrame.
  iApply big_sepS_empty. done.
Qed.

Section laws.
  Context `{!heapbijGS Σ, !sheapGS Σ}.
  Implicit Types (b_t b_s : block) (l_t l_s : loc).

  Lemma heapbij_access L P b_t b_s:
    heapbij_interp L P -∗
    block_rel b_t b_s -∗
    ⌜(b_t, b_s) ∈ L⌝ ∗
    alloc_rel b_t b_s P ∗
    (∀ P' : _ → _ → _  → Prop,
        ⌜∀ b_t' b_s' o q, b_t' ≠ b_t → b_s' ≠ b_s → P (Loc b_t' o) (Loc b_s' o) q →
                           P' (Loc b_t' o) (Loc b_s' o) q⌝ -∗
        alloc_rel b_t b_s P' -∗ heapbij_interp L P').
  Proof.
    iIntros "Hinv Hrel". iDestruct "Hinv" as "(Hauth & Hheap)".
    iDestruct (gset_bij_elem_of with "Hauth Hrel") as %Hin.
    iPoseProof (big_sepS_delete with "Hheap") as "[He Hheap]"; first done.
    iDestruct (gset_bij_own_valid with "Hauth") as %[_ Hbij].
    iFrame. iSplit; [done|].
    iIntros (P' HP) "Halloc". iFrame.
    iApply big_sepS_delete; first done. iFrame.
    iApply (big_sepS_impl with "Hheap").
    iIntros "!>" ([??] Hin2) "Halloc".
    iApply (alloc_rel_mono with "Halloc") => ?? /=.
    set_unfold. destruct Hin2 as [Hin2 Hneq].
    have ?:= gset_bijective_eq_iff _ _ _ _ _ _ Hin Hin2.
    apply: HP => b'; naive_solver.
  Qed.

  Lemma heapbij_insertN L l_t l_s v_t v_s n (P : _ → _ → _ → Prop):
    n > 0 →
    length v_s = n →
    length v_t = n →
    (block_is_dyn l_t.(loc_block) ↔ block_is_dyn l_s.(loc_block)) →
    (∀ o, (∀ b_s, (loc_block l_t, b_s) ∉ L) →
          (∀ b_t, (b_t, loc_block l_s) ∉ L) → P (l_t +ₗ o) (l_s +ₗ o) (Some 1%Qp)) →
    heapbij_interp L P -∗
    l_t ↦t∗ v_t -∗
    l_s ↦s∗ v_s -∗
    ([∗ list] vt;vs∈v_t;v_s, val_rel vt vs) -∗
    target_block_size l_t (Some n) -∗
    source_block_size l_s (Some n) ==∗
    heapbij_interp ({[(loc_block l_t, loc_block l_s)]} ∪ L) P ∗
    l_t ↔h l_s.
  Proof.
    iIntros (Hn Hl_s Hl_t Hb HP) "Hinv Ht Hs Hrel Ha_t Ha_s".
    iDestruct (heap_block_size_idx with "Ha_t") as %?.
    iDestruct (heap_block_size_idx with "Ha_s") as %?.
    iDestruct "Hinv" as "(Hauth & Hheap)".
    pose (b_t := loc_block l_t). pose (b_s := loc_block l_s).
    iAssert ((¬ ⌜set_Exists (λ '(b_t', b_s'), b_t = b_t') L⌝)%I) as "%Hext_t".
    { iIntros (([b_t' b_s'] & Hin & <-)).
      iPoseProof (big_sepS_elem_of with "Hheap") as "Hr"; first by apply Hin.
      iDestruct "Hr" as (n' v_t' v_s' ?) "(_ & _ & Ha_t' & _)".
      by iApply (heap_block_size_excl with "Ha_t Ha_t'").
    }
    iAssert ((¬ ⌜set_Exists (λ '(b_t', b_s'), b_s = b_s') L⌝)%I) as "%Hext_s".
    { iIntros (([b_t' b_s'] & Hin & <-)).
      iPoseProof (big_sepS_elem_of with "Hheap") as "Hr"; first by apply Hin.
      iDestruct "Hr" as (n' v_t' v_s' ?) "(_ & _ & _ & Ha_s')".
      by iApply (heap_block_size_excl with "Ha_s Ha_s'").
    }
    iMod ((gset_bij_own_extend b_t b_s) with "Hauth") as "[Hinv #Helem]".
    - intros b_s' Hb_s'. apply Hext_t. by exists (b_t, b_s').
    - intros b_t' Hb_t'. apply Hext_s. by exists (b_t', b_s).
    - iModIntro.
      iSplitL; first last. { iSplitL; first done. iPureIntro; lia. }
      iFrame. iApply big_sepS_insert. { contradict Hext_t. by exists (b_t, b_s). }
      iFrame. iExists (Some n), v_t, v_s. iFrame.
      destruct l_t, l_s; cbn in *; subst. iFrame.
      iSplit; [done|]. iSplit; [done|].
      iDestruct (big_sepL2_sepL_2 with "Ht Hs") as "Hvs"; [done|].
      iCombine "Hrel" "Hvs" as "Hvs". rewrite -big_sepL2_sep.
      iApply (big_sepL2_impl with "Hvs").
      iIntros "!>" (?????) "(Hv&Ht&Hs)". iExists _, (Some 1%Qp). iFrame.
      iPureIntro. apply HP => ??.
      + apply: Hext_t. eexists _. naive_solver.
      + apply: Hext_s. eexists _. naive_solver.
  Qed.

  Lemma heapbij_insert_globals (P : _ → _ → _ → Prop) L (gs : gmap string val) :
    (∀ n o, P (global_loc n +ₗ o) (global_loc n +ₗ o) (Some 1%Qp)) →
    heapbij_interp L P -∗
    ([∗ map] n↦v ∈ gs,
      global_loc n ↦t v ∗ target_block_size (global_loc n) (Some 1) ∗
      global_loc n ↦s v ∗ source_block_size (global_loc n) (Some 1)
    ) -∗
    ([∗ map] v ∈ gs, val_rel v v)
    ==∗
    ∃ L', heapbij_interp L' P ∗ ([∗ set] g ∈ dom gs, global_loc g ↔h global_loc g).
  Proof.
    iIntros (HP) "Hbij Hmt Hvs".
    iInduction gs as [|g v gs] "IH" using map_ind.
    { iExists _. iFrame. by rewrite dom_empty_L big_sepS_empty. }
    rewrite !big_sepM_insert //.
    iDestruct "Hmt" as "[(?&?&?&?) Hmt]". iDestruct "Hvs" as "[Hv Hvs]".
    iMod ("IH" with "Hbij Hmt Hvs") as (L') "[Hbij Hs]".
    rewrite -!heap_pointsto_vec_singleton.
    iMod (heapbij_insertN with "Hbij [$] [$] [$Hv] [$] [$]") as "[Hbij Hl]"; [lia | done.. | naive_solver | naive_solver |done |].
    iModIntro. iExists _. iFrame. rewrite dom_insert_L big_sepS_insert ?not_elem_of_dom //.
    iFrame.
  Qed.

  Lemma heapbij_block_size_ne l1 l_t2 l_s2 n L P:
    l_t2 ↔h l_s2 -∗
    source_block_size l1 n -∗
    heapbij_interp L P -∗
    ⌜loc_block l1 ≠ loc_block l_s2⌝.
  Proof.
    iIntros "[Hbij %] Hf Hint".
    iDestruct (heapbij_access with "Hint Hbij") as (?) "[Halloc _]".
    iDestruct "Halloc" as (n' vs_t vs_s Hlen ?) "(Hvs & Halloc_t & Halloc_s)".
    destruct (decide (loc_block l1 = loc_block l_s2)) => //.
    by iDestruct (heap_block_size_excl with "Hf Halloc_s") as %?.
  Qed.

End laws.
