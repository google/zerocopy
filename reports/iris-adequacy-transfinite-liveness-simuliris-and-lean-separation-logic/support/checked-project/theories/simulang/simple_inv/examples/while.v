From simuliris.simulang Require Import lang notation tactics class_instances.
From iris.proofmode Require Import proofmode.
From simuliris.simulation Require Import slsls lifting.
From simuliris.simulang.simple_inv Require Import inv.

(** * Examples of coinductive simulation proofs *)

Section fix_bi.
  Context `{!simpleGS Σ}.

  (** Trivial loop *)
  Definition loop_test n : expr :=
    let: "n" := Alloc #n in
    While (#0 < ! "n") ("n" <- ! "n" - #1).

  Lemma loop (n : nat) π :
    ⊢ loop_test n ⪯{π} #() {{ val_rel }}.
  Proof.
    rewrite /loop_test.
    target_alloc l as "Hl" "_". sim_pures.
    iInduction n as [|n] "IH" forall "Hl".
    - target_while. target_load. by sim_pures; sim_val.
    - target_while. target_load. sim_pures. target_load. target_store. sim_pures.
      assert (Z.sub (Z.of_nat (S n)) (Zpos xH) = Z.of_nat n) as -> by lia.
      by iApply "IH".
  Qed.


  (** We can prove that [mul_loop] simulates primitive multiplication, and vice versa.
    The prove that it simulates primitive multiplication is based on our powerful unbounded stuttering support (the source program takes a single step!) . *)
  Definition mul_loop e1 e2 : expr :=
    let: "m" := e2 in
    let: "n" := Alloc e1 in
    let: "acc" := Alloc #0 in
    while: #0 < !"n" do "acc" <- !"acc" + "m";; "n" <- !"n" - #1 od ;;
    let: "mv" := !"acc" in
    Free "n";;
    Free "acc";;
    "mv".

  Lemma loop_lem (n0 n m : nat) (l_acc l_n : loc) :
    l_n ↦t #n -∗
    l_acc ↦t #((n0 - n) * m) -∗
    target_red (while: #0 < !#l_n do #l_acc <- !#l_acc + #m;; #l_n <- !#l_n - #1 od)%E
      (λ e_t', ⌜e_t' = #()⌝ ∗ l_n ↦t #0 ∗ l_acc ↦t #(n0 * m)).
  Proof.
    iIntros "Hn Hm". iInduction n as [|n] "IH" forall "Hn Hm".
    - target_while. sim_pures. target_load. sim_pures.
      assert (n0 - 0%nat = n0)%Z as -> by lia.
      iModIntro. by iFrame.
    - target_while. target_load. sim_pures. target_load.
      target_store. target_load. target_store. sim_pures.
      iApply ("IH" with "[Hn] [Hm]").
      + by assert ((S n) - 1 = n)%Z as -> by lia.
      + by assert ((n0 - S n) * m + m = (n0 - n) * m)%Z as -> by lia.
  Qed.

  Lemma mul_sim (n m : nat) π :
    ⊢ mul_loop #n #m ⪯{π} #n * #m {{ val_rel }}.
  Proof.
    rewrite /mul_loop.
    sim_pures. target_alloc l_n as "Hln" "Ha_n". target_alloc l_acc as "Hlacc" "Ha_acc".
    sim_pures.
    target_bind (While _ _).
    iApply (target_red_wand (λ e_t',⌜e_t' = Val #()⌝ ∗ l_n ↦t #0 ∗ l_acc ↦t #(n * m))%I with "[Hln Hlacc]"). {
      (* generalize over n for the ind, but fix n0 *)
      iApply (loop_lem with "Hln [Hlacc]"). by assert ((n - n) * m = 0)%Z as -> by lia.
    }
    iIntros (e_t') "(-> & Hln & Hlacc)". sim_pures.
    target_load. sim_pures. target_free. target_free.
    by sim_pures; sim_val.
  Qed.

  Lemma loop_lem' (n0 n m : nat) (l_acc l_n : loc) π :
    l_n ↦s #n -∗
    l_acc ↦s #((n0 - n) * m) -∗
    source_red (while: #0 < !#l_n do #l_acc <- !#l_acc + #m;; #l_n <- !#l_n - #1 od)%E π
      (λ e_s', ⌜e_s' = #()⌝ ∗ l_n ↦s #0 ∗ l_acc ↦s #(n0 * m)).
  Proof.
    iIntros "Hn Hm". iInduction n as [|n] "IH" forall "Hn Hm".
    - source_while. sim_pures. source_load. sim_pures.
      assert (n0 - 0%nat = n0)%Z as -> by lia.
      iModIntro. by iFrame.
    - source_while. source_load. sim_pures. source_load.
      source_store. source_load. source_store. sim_pures.
      iApply ("IH" with "[Hn] [Hm]").
      + by assert ((S n) - 1 = n)%Z as -> by lia.
      + by assert ((n0 - S n) * m + m = (n0 - n) * m)%Z as -> by lia.
  Qed.

  Lemma mul_sim' (n m : nat) π :
    ⊢ #(n * m) ⪯{π} mul_loop #n #m  {{ val_rel }}.
  Proof.
    rewrite /mul_loop.
    sim_pures. source_alloc l_n as "Hln" "Ha_n". source_alloc l_acc as "Hlacc" "Ha_acc".
    sim_pures.
    source_bind (While _ _).
    iApply (source_red_wand (λ e_t',⌜e_t' = Val #()⌝ ∗ l_n ↦s #0 ∗ l_acc ↦s #(n * m))%I with "[Hln Hlacc]"). {
      (* generalize over n for the ind, but fix n0 *)
      iApply (loop_lem' with "Hln [Hlacc]"). by assert ((n - n) * m = 0)%Z as -> by lia.
    }
    iIntros (e_s') "(-> & Hln & Hlacc)". sim_pures.
    source_load. sim_pures. source_free. source_free.
    by sim_pures; sim_val.
  Qed.


  (** We prove examples of recursion and loops simulating each other coinductivel. *)
  Ltac discr_source := to_source; iApply source_red_safe_implies.

  Definition input_loop : expr :=
    let: "cont" := Alloc #true in
    while: !"cont" do
      "cont" <- Call f#"external" #()
    od.


  Definition input_rec : func :=
    λ: "cont",
      if: "cont" then
        let: "cont" := Call f#"external" #() in
        Call f#"rec" "cont"
      else #().

  Lemma loop_rec :
    "rec" @s input_rec -∗
    log_rel input_loop (Call f#"rec" #true).
  Proof.
    iIntros "#Hs".
    log_rel. iIntros "!#" (π') "_".
    target_alloc lc_t as "Hlc_t" "_". sim_pures.
    iApply (sim_while_rec (λ v_s, ∃ v_t, val_rel v_t v_s ∗ lc_t ↦t v_t)%I with "[Hlc_t] Hs").
    { iExists #true. eauto. }
    iModIntro. iIntros (v_s') "He". iDestruct "He" as (v_t) "[Hv Hlc_t]". sim_pures.

    discr_source.
    iIntros ((b & ->)); iPoseProof (gen_val_rel_litbool_source with "Hv") as "->"; sim_pures.
    target_load. destruct b; sim_pures.
    - sim_bind (Call _ _) (Call _ _).
      iApply sim_call; [done..|].
      iIntros (v_t v_s) "Hv'". iApply lift_post_val. target_store. sim_pures. iApply sim_expr_base.
      iRight. iExists _. eauto.
    - iApply sim_expr_base. iLeft. iExists #(), #(); eauto.
  Qed.

  Lemma loop_rec' :
    "rec" @t input_rec -∗
    log_rel (Call f#"rec" #true) input_loop.
  Proof.
    iIntros "#Hs". log_rel. iIntros "!#" (π') "_".
    rewrite /input_loop. source_alloc lc_s as "Hlc_s" "Ha_s". sim_pures.
    iApply (sim_rec_while (λ v_t, ∃ v_s, val_rel v_t v_s ∗ lc_s ↦s v_s)%I with "[Hlc_s] Hs").
    { iExists #true. eauto. }
    iModIntro. iIntros (v_t') "He". iDestruct "He" as (v_s) "[Hv Hlc_s]". sim_pures.

    source_load.
    discr_source.
    iIntros ((b & ->)); iPoseProof (gen_val_rel_litbool_source with "Hv") as "->"; sim_pures.
    destruct b; sim_pures.
    - sim_bind (Call _ _) (Call _ _).
      iApply sim_call; [done..|].
      iIntros (v_t v_s) "Hv'". iApply lift_post_val. source_store. sim_pures. iApply sim_expr_base.
      iRight. iExists v_t. eauto.
    - iApply sim_expr_base. iLeft. iExists #(), #(); eauto.
  Qed.
End fix_bi.
