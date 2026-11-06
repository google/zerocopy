From simuliris.simulation Require Import lifting.
From simuliris.tree_borrows Require Import primitive_laws proofmode steps_progress.



(* in our simplified memory model, pointers and integers occupy one memory slot *)
Definition sizeof_scalar : nat := 1.

(* Allocate a place of size [sz] and initialize it with a value [v] *)
Definition new_place sz (v: expr) : expr :=
  let: "x" := Alloc sz in "x" <- v ;; "x".

(* Retag a place [p] that is a pointer of kind [pk] to a region of size [sz],
  with retag [kind] and call_id [c] *)
Definition retag_place
  (p: expr) (pk: pointer_kind) im (sz : nat) (kind: retag_kind) (c : expr) : expr :=
  let: "p" := p in
  (* read the current pointer stored in the place [p] *)
  (* retag and update [p] with the pointer with new tag *)
  "p" <- Retag (Copy "p") c pk im sz kind.

Lemma write_entire_range {T} l sz (v v' : list T) :
  length v = sz →
  length v' = sz →
  write_range l l v' v = Some v'.
Proof.
  intros <- Hlen.
  rewrite /write_range bool_decide_true. 2: lia. f_equal.
  eapply list_eq.
  intros i. eapply write_range_to_list_lookup. split.
  1: rewrite Z.sub_diag Z2Nat.inj_0 Nat.sub_0_r //.
  intros H. rewrite !lookup_ge_None_2; try done. all: lia.
Qed.

Lemma sim_new_place_local `{sborGS Σ} sz v_t v_s π Φ :
  ⌜length v_t = length v_s⌝ -∗
  (∀ t l,
    ⌜length v_s = sz⌝ -∗
    ⌜length v_t = sz⌝ -∗
    t $$ tk_local -∗
    l ↦t∗[tk_local]{t} v_t -∗
    l ↦s∗[tk_local]{t} v_s -∗
    PlaceR l t sz ⪯{π} PlaceR l t sz [{ Φ }]) -∗
  new_place sz #v_t ⪯{π} new_place sz #v_s [{ Φ }].
Proof.
  iIntros (Hlen_eq) "Hsim".
  rewrite /new_place. sim_bind (Alloc _) (Alloc _).
  iApply sim_alloc_local. iIntros (t l) "Htag Ht Hs". iApply sim_expr_base.
  sim_pures.
  source_bind (Write _ _).
  (* gain knowledge about the length *)
  iApply source_red_safe_implies. iIntros (Hsize).
  iApply (source_write_local with "Htag Hs"). 2: done.
  { eapply write_entire_range. 2: exact Hsize. rewrite length_replicate //. }
  iIntros "Hs Htag". source_finish.

  target_bind (Write _ _).
  iApply (target_write_local with "Htag Ht"). 2: done. 2: lia.
  { eapply write_entire_range. 1: rewrite length_replicate //. lia. }
  iIntros "Ht Htag". target_finish.

  sim_pures. iApply ("Hsim" with "[//] [] Htag Ht Hs").
  iPureIntro; lia.
Qed.


Lemma new_place_safe_reach P σ sz r :
  safe_reach P (new_place sz (of_result r)) σ (λ _ _, ∃ v, r = ValR v ∧ length v = sz).
Proof.
  rewrite /new_place.
  safe_reach_bind (Alloc _).
  eapply safe_reach_safe_implies; first eapply safe_implies_alloc_strong.
  intros (HH1&HH2).
  eapply safe_reach_base_step.
  { econstructor 2. 1: econstructor. econstructor. all: done. }
  eapply safe_reach_refl.
  safe_reach_bind (Let _ _ _).
  eapply safe_reach_pure; [ apply _ | done | ].
  eapply safe_reach_refl; simpl.
  destruct r as [ v | ]; simpl.
  - (* value *)
    safe_reach_bind (Write _ _).
    eapply safe_reach_safe_implies; [ apply safe_implies_write_weak | ].
    intros ?.
    do 2 eapply safe_reach_refl. eauto.
  - safe_reach_bind (Write _ _).
    eapply safe_reach_safe_implies; [ apply _ | done].
Qed.
