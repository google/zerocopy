From stdpp Require Import binders.
From iris.proofmode Require Import proofmode.

(* TODO: upstream everything in this file *)

Lemma big_sepL2_exist {SI : sidx} {PROP : bi} {A B C} (l1 : list A) (l2 : list B) (Φ : _ → _ → _ → _ → PROP) `{!BiAffine PROP} :
  ([∗ list] i↦x1;x2∈l1;l2, ∃ x : C, Φ i x1 x2 x) -∗
   ∃ xs : list C, ⌜length xs = length l1⌝ ∗ ([∗ list] i↦x1;x2∈l1;l2, ∃ x : C, ⌜xs !! i = Some x⌝ ∗ Φ i x1 x2 x).
Proof.
  iIntros "Hl".
  iInduction (l1) as [|? l1] "IH" forall (l2 Φ).
  { iDestruct (big_sepL2_nil_inv_l with "Hl") as %->. iExists []. by iSplit. }
  iDestruct (big_sepL2_cons_inv_l with "Hl") as (x2 l2' ->) "[[%x ?] Hl]".
  iDestruct ("IH" with "Hl") as (xs) "[%Heq ?]".
  iExists (x::xs) => /=. iSplit; [by rewrite /= Heq|]. by iFrame.
Qed.
Lemma big_sepL2_to_sepL_r {SI : sidx} {PROP : bi} {A B} (l1 : list A) (l2 : list B) (Φ : _ → _ → _ → PROP) `{!BiAffine PROP}:
  length l1 = length l2 →
  ([∗ list] i↦x1;x2∈l1;l2, Φ i x1 x2) ⊣⊢
  ([∗ list] i↦x2∈l2, ∃ x1, ⌜l1 !! i = Some x1⌝ ∗  Φ i x1 x2).
Proof.
  elim: l1 l2 Φ. { by case. }
  move => x l1 IH [//|y l2] Φ /= [?]. rewrite IH //. f_equiv.
  iSplit; first by eauto with iFrame. iIntros "[%x1 [% ?]]"; by simplify_eq.
Qed.
