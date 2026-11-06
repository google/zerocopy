From simuliris.simulation Require Import lifting.
From simuliris.stacked_borrows Require Import primitive_laws proofmode steps_progress.


(* Allocate a place of type [T] and initialize it with a value [v] *)
Definition new_place T (v: expr) : expr :=
  let: "x" := Alloc T in "x" <- v ;; "x".

(* Retag a place [p] that is a pointer of kind [pk] to a region of type [T],
  with retag [kind] and call_id [c] *)
Definition retag_place
  (p: expr) (pk: pointer_kind) (T: type) (kind: retag_kind) (c : expr) : expr :=
  let: "p" := p in
  (* read the current pointer stored in the place [p] *)
  (* retag and update [p] with the pointer with new tag *)
  "p" <- Retag (Copy "p") c pk T kind.

Lemma sim_new_place_local `{sborGS Σ} T v_t v_s π Φ :
  ⌜length v_t = length v_s⌝ -∗
  (∀ t l,
    ⌜length v_s = tsize T⌝ -∗
    ⌜length v_t = tsize T⌝ -∗
    t $$ tk_local -∗
    l ↦t∗[tk_local]{t} v_t -∗
    l ↦s∗[tk_local]{t} v_s -∗
    PlaceR l (Tagged t) T ⪯{π} PlaceR l (Tagged t) T [{ Φ }]) -∗
  new_place T #v_t ⪯{π} new_place T #v_s [{ Φ }].
Proof.
  iIntros (Hlen_eq) "Hsim".
  rewrite /new_place. sim_bind (Alloc _) (Alloc _).
  iApply sim_alloc_local. iIntros (t l) "Htag Ht Hs". iApply sim_expr_base.
  sim_pures.
  source_bind (Write _ _).
  (* gain knowledge about the length *)
  iApply source_red_safe_implies. iIntros (Hsize).
  iApply (source_write_local with "Htag Hs"); [by rewrite length_replicate | done | ].
  iIntros "Hs Htag". source_finish.

  target_bind (Write _ _).
  iApply (target_write_local with "Htag Ht"); [ by rewrite length_replicate | lia| ].
  iIntros "Ht Htag". target_finish.

  sim_pures. iApply ("Hsim" with "[//] [] Htag Ht Hs").
  iPureIntro; lia.
Qed.

Lemma new_place_safe_reach P σ T r :
  safe_reach P (new_place T (of_result r)) σ (λ _ _, ∃ v, r = ValR v ∧ length v = tsize T).
Proof.
  rewrite /new_place.
  safe_reach_bind (Alloc _).
  eapply safe_reach_base_step.
  { eapply alloc_base_step. }
  eapply safe_reach_refl.
  safe_reach_bind (Let _ _ _).
  eapply safe_reach_pure; [ apply _ | done | ].
  eapply safe_reach_refl; simpl.
  destruct r as [ v | ]; simpl.
  - (* value *)
    safe_reach_bind (Write _ _).
    eapply safe_reach_safe_implies; [ apply _ | ].
    intros (_ & _ & ?).
    do 2 eapply safe_reach_refl. eauto.
  - safe_reach_bind (Write _ _).
    eapply safe_reach_safe_implies; [ apply _ | done].
Qed.
