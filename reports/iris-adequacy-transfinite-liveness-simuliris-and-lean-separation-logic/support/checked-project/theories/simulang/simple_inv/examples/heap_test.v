From simuliris.simulang Require Import lang notation tactics class_instances proofmode.
From iris.proofmode Require Import proofmode.
From simuliris.simulation Require Import slsls lifting.
From simuliris.simulang.simple_inv Require inv.

(** Some very trivial tests for the heap tactics *)


Module fix_bi.
Section a.
Context `{sheapGS Σ}.
Program Instance : sheapInv Σ := {|
  sheap_inv _ _ _ := ⌜True⌝%I;
  sheap_ext_rel _ _ _ := ⌜True⌝%I;
|}.
Next Obligation. done. Qed.
Global Instance : sheapInvStateIndependent.
Proof. done. Qed.

Definition val_rel (v1 v2 : val) : iProp Σ := (⌜v1 = v2⌝)%I.

Lemma test_load π l l2 :
  l ↦t #4 -∗ l2 ↦s #4 -∗
  ((! #l)%E ⪯{π} ! #l2 {{ val_rel }}).
Proof.
  iIntros "H H1". target_load. source_load. sim_val. eauto.
Qed.

Lemma test_store π l l2 :
  l ↦t #4 -∗ l2 ↦s #4 -∗
  ((#l <- #42)%E ⪯{π} #l2 <- #1337 {{ val_rel }}).
Proof.
  iIntros "H H1". target_store. source_store. sim_val. eauto.
Qed.

(* FIXME: fix precedences for ⪯ to make the parantheses unnecessary *)
Lemma test_alloc π :
  ⊢ (Alloc #2 ;; #()) ⪯{π} (Alloc #4;;#()) {{ val_rel }}.
Proof.
  target_alloc l1 as "H" "_".
  source_alloc l2 as "H2" "_".
  sim_pures; sim_val.
  eauto.
Qed.

Lemma test_free π l l2 :
  l ↦t #42 -∗ l2 ↦s #1337 -∗ †l …t 1 -∗ †l2 …s 1 -∗
  Free #l ⪯{π} Free #l2 {{ val_rel }}.
Proof.
  iIntros "H1 H2 H3 H4".
  target_free. source_free. sim_val. eauto.
Qed.

(* FIXME: if we remove the parantheses around the first element, parsing is broken *)
Lemma test_freeN π l l2 :
  l ↦t∗ [(#42); #99] -∗ l2 ↦s∗ [(#1337); #420; #666] -∗ †l …t 2 -∗ †l2 …s 3 -∗
  FreeN #2 #l ⪯{π} FreeN #3 #l2 {{ val_rel }}.
Proof.
  iIntros "H1 H2 H3 H4".
  target_free; first done. source_free; first done. sim_val. eauto.
Qed.
End a.
End fix_bi.

Module bij_test.
  Import inv.
  Section b.
  Context `{!simpleGS Σ}.

  Lemma test_load π l l2:
    l ↦t #4 -∗ l2 ↦s #4 -∗
    ((! #l)%E ⪯{π} ! #l2 {{ val_rel }}).
  Proof.
    iIntros "H H1". target_load. source_load. sim_val. eauto.
  Qed.

  Lemma test_store π l l2:
    l ↦t #4 -∗ l2 ↦s #4 -∗
    ((#l <- #42)%E ⪯{π} #l2 <- #1337 {{ val_rel }}).
  Proof.
    iIntros "H H1". target_store. source_store. sim_val. eauto.
  Qed.

  Lemma test_insert π l l2:
    l ↦t #4 -∗ l2 ↦s #4 -∗ †l …t 1 -∗ †l2 …s 1 -∗
    ((#l <- #42)%E ⪯{π} #l2 <- #42 {{ val_rel }}).
  Proof.
    iIntros "H H1 H2 H3".
    iApply (sim_bij_insert _ l l2 with "H2 H3 H H1 "); [done|]; iIntros "Hb".
    iApply (sim_bij_store with "Hb []"); first done. by sim_val.
  Qed.

  Lemma test_bij_store π (l_t l_s : loc) :
    l_t ↔h l_s -∗
    (#l_t <- #42)%E ⪯{π} (#l_s <- #42)%E {{ val_rel }}.
  Proof.
    iIntros "H". sim_store; first done. by sim_val.
  Qed.

  Lemma test_bij_load π (l_t l_s : loc):
    l_t ↔h l_s -∗
    ! #l_t ⪯{π} ! #l_s {{ val_rel }}.
  Proof.
    iIntros "H". sim_load v_t v_s as "Ha"; sim_val. done.
  Qed.

  Lemma test_bij_free π (l_t l_s : loc):
    l_t ↔h l_s -∗
    Free #l_t ⪯{π} Free #l_s {{ val_rel }}.
  Proof.
    iIntros "#H". sim_free; sim_val. done.
  Qed.
  End b.
End bij_test.
