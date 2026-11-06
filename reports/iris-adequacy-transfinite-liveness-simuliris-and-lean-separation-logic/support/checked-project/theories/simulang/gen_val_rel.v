(** * Structural value relation

This file defines [gen_val_rel] that structually lifts a relation
[loc_rel] on locations to values. It is used by [sheap] instances to define
[sheap_val_rel]. *)

From iris.proofmode Require Import proofmode.
From iris.base_logic Require Import iprop.
From simuliris.simulation Require Import slsls lifting.
From simuliris.simulang Require Import notation.

Section gen_val_rel.
  Context {Σ} (loc_rel : loc → loc → iProp Σ).

  Definition loc_rel_func_law : Prop :=
    (∀ l l1 l2, loc_rel l l1 -∗ loc_rel l l2 -∗ ⌜l1 = l2⌝).
  Definition loc_rel_inj_law : Prop :=
    (∀ l l1 l2, loc_rel l1 l -∗ loc_rel l2 l -∗ ⌜l1 = l2⌝).
  Definition loc_rel_offset_law : Prop :=
    (∀ l_t l_s o, loc_rel l_t l_s -∗ loc_rel (l_t +ₗ o) (l_s +ₗ o)).

  Fixpoint gen_val_rel (v_t v_s : val) {struct v_s} : iProp Σ :=
    match v_t, v_s with
    | LitV (LitLoc l_t), LitV (LitLoc l_s) =>
        loc_rel l_t l_s
    | LitV l_t, LitV l_s =>
        ⌜l_t = l_s⌝
    | PairV v1_t v2_t, PairV v1_s v2_s =>
        gen_val_rel v1_t v1_s ∗ gen_val_rel v2_t v2_s
    | InjLV v_t, InjLV v_s =>
        gen_val_rel v_t v_s
    | InjRV v_t, InjRV v_s =>
        gen_val_rel v_t v_s
    | _,_ => False
    end.
  Global Instance gen_val_rel_pers v_t v_s `{!∀ l_t l_s, Persistent (loc_rel l_t l_s)} :
    Persistent (gen_val_rel v_t v_s).
  Proof.
    induction v_s as [[] | | | ] in v_t |-*; destruct v_t as [ [] | | | ]; apply _.
  Qed.

  Lemma gen_val_rel_pair_source v_t v_s1 v_s2 :
    gen_val_rel v_t (v_s1, v_s2) -∗
    ∃ v_t1 v_t2, ⌜v_t = PairV v_t1 v_t2⌝ ∗
      gen_val_rel v_t1 v_s1 ∗
      gen_val_rel v_t2 v_s2.
  Proof.
    simpl. iIntros "H". destruct v_t as [[] | v_t1 v_t2 | |]; simpl; try done.
    iExists v_t1, v_t2. iDestruct "H" as "[$ $]". eauto.
  Qed.
  Lemma gen_val_rel_injl_source v_t v_s :
    gen_val_rel v_t (InjLV v_s) -∗ ∃ v_t', ⌜v_t = InjLV v_t'⌝ ∗ gen_val_rel v_t' v_s.
  Proof. simpl. destruct v_t as [[] | | |]; (try by iIntros "%Hp"); eauto. Qed.
  Lemma gen_val_rel_injr_source v_t v_s :
    gen_val_rel v_t (InjRV v_s) -∗ ∃ v_t', ⌜v_t = InjRV v_t'⌝ ∗ gen_val_rel v_t' v_s.
  Proof. simpl. destruct v_t as [[] | | |]; (try by iIntros "%Hp"); eauto. Qed.


  Lemma gen_val_rel_litfn_source v_t fn_s :
    gen_val_rel v_t (LitV $ LitFn $ fn_s) -∗ ⌜v_t = LitV $ LitFn $ fn_s⌝.
  Proof. simpl. destruct v_t as [[] | v_t1 v_t2 | |]; iIntros "%Hp"; inversion Hp; subst; done. Qed.
  Lemma gen_val_rel_litint_source v_t n :
    gen_val_rel v_t (LitV $ LitInt n) -∗ ⌜v_t = LitV $ LitInt $ n⌝.
  Proof. simpl. destruct v_t as [[] | v_t1 v_t2 | |]; iIntros "%Hp"; inversion Hp; subst; done. Qed.
  Lemma gen_val_rel_litbool_source v_t b:
    gen_val_rel v_t (LitV $ LitBool b) -∗ ⌜v_t = LitV $ LitBool b⌝.
  Proof. simpl. destruct v_t as [[] | v_t1 v_t2 | |]; iIntros "%Hp"; inversion Hp; subst; done. Qed.
  Lemma gen_val_rel_litunit_source v_t :
    gen_val_rel v_t (LitV $ LitUnit) -∗ ⌜v_t = LitV $ LitUnit⌝.
  Proof. simpl. destruct v_t as [[] | v_t1 v_t2 | |]; iIntros "%Hp"; inversion Hp; subst; done. Qed.
  Lemma gen_val_rel_litpoison_source v_t :
    gen_val_rel v_t (LitV $ LitPoison) -∗ ⌜v_t = LitV $ LitPoison⌝.
  Proof. simpl. destruct v_t as [[] | v_t1 v_t2 | |]; iIntros "%Hp"; inversion Hp; subst; done. Qed.
  Lemma gen_val_rel_loc_source v_t l_s :
    gen_val_rel v_t (LitV $ LitLoc l_s) -∗
    ∃ l_t, ⌜v_t = LitV $ LitLoc l_t⌝ ∗ loc_rel l_t l_s.
  Proof.
    destruct v_t as [[ | | | | l_t | ] | | | ]; simpl;
        first [iIntros "%Ht"; congruence | iIntros "Ht"; eauto].
  Qed.

  Lemma gen_val_rel_pair_target v_s v_t1 v_t2 :
    gen_val_rel (v_t1, v_t2) v_s -∗
    ∃ v_s1 v_s2, ⌜v_s = PairV v_s1 v_s2⌝ ∗
      gen_val_rel v_t1 v_s1 ∗
      gen_val_rel v_t2 v_s2.
  Proof.
    simpl. iIntros "H". destruct v_s as [[] | v_s1 v_s2 | |]; simpl; try done.
    iExists v_s1, v_s2. iDestruct "H" as "[$ $]". eauto.
  Qed.
  Lemma gen_val_rel_injl_target v_t v_s :
    gen_val_rel (InjLV v_t) v_s -∗ ∃ v_s', ⌜v_s = InjLV v_s'⌝ ∗ gen_val_rel v_t v_s'.
  Proof. simpl. destruct v_s as [[] | | |]; (try by iIntros "%Hp"); eauto. Qed.
  Lemma gen_val_rel_injr_target v_t v_s :
    gen_val_rel (InjRV v_t) v_s -∗ ∃ v_s', ⌜v_s = InjRV v_s'⌝ ∗ gen_val_rel v_t v_s'.
  Proof. simpl. destruct v_s as [[] | | |]; (try by iIntros "%Hp"); eauto. Qed.
  Lemma gen_val_rel_litfn_target v_s fn_t :
    gen_val_rel (LitV $ LitFn $ fn_t) v_s -∗ ⌜v_s = LitV $ LitFn $ fn_t⌝.
  Proof. simpl. destruct v_s as [[] | v_s1 v_s2 | |]; iIntros "%Hp"; inversion Hp; subst; done. Qed.
  Lemma gen_val_rel_litint_target v_s n :
    gen_val_rel (LitV $ LitInt n) v_s -∗ ⌜v_s = LitV $ LitInt $ n⌝.
  Proof. simpl. destruct v_s as [[] | | |]; iIntros "%Hp"; inversion Hp; subst; done. Qed.
  Lemma gen_val_rel_litbool_target v_s b:
    gen_val_rel (LitV $ LitBool b) v_s -∗ ⌜v_s = LitV $ LitBool b⌝.
  Proof. simpl. destruct v_s as [[] | | |]; iIntros "%Hp"; inversion Hp; subst; done. Qed.
  Lemma gen_val_rel_litunit_target v_s :
    gen_val_rel (LitV $ LitUnit) v_s -∗ ⌜v_s = LitV $ LitUnit⌝.
  Proof. simpl. destruct v_s as [[] | | |]; iIntros "%Hp"; inversion Hp; subst; done. Qed.
  Lemma gen_val_rel_litpoison_target v_s :
    gen_val_rel (LitV $ LitPoison) v_s -∗ ⌜v_s = LitV $ LitPoison⌝.
  Proof. simpl. destruct v_s as [[] | | |]; iIntros "%Hp"; inversion Hp; subst; done. Qed.
  Lemma gen_val_rel_loc_target v_s l_t :
    gen_val_rel (LitV $ LitLoc l_t) v_s -∗
    ∃ l_s, ⌜v_s = LitV $ LitLoc l_s⌝ ∗ loc_rel l_t l_s.
  Proof.
    destruct v_s as [[ | | | | l_s | ] | | | ]; simpl;
        first [iIntros "%Hs"; congruence | iIntros "Hs"; eauto].
  Qed.
End gen_val_rel.
Tactic Notation "val_discr_source" constr(H) :=
  first [iPoseProof (gen_val_rel_litint_source with H) as "->" |
         iPoseProof (gen_val_rel_litbool_source with H) as "->" |
         iPoseProof (gen_val_rel_litfn_source with H) as "->" |
         iPoseProof (gen_val_rel_litunit_source with H) as "->" |
         iPoseProof (gen_val_rel_litpoison_source with H) as "->" |
         let H' := iFresh in
         iPoseProof (gen_val_rel_loc_source with H) as (? ->) H';
         try iClear H; iRename H' into H].
Tactic Notation "val_discr_target" constr(H) :=
  first [iPoseProof (gen_val_rel_litint_target with H) as "->" |
         iPoseProof (gen_val_rel_litbool_target with H) as "->" |
         iPoseProof (gen_val_rel_litfn_target with H) as "->" |
         iPoseProof (gen_val_rel_litunit_target with H) as "->" |
         iPoseProof (gen_val_rel_litpoison_target with H) as "->" |
         let H' := iFresh in
         iPoseProof (gen_val_rel_loc_target with H) as (? ->) H';
         try iClear H; iRename H' into H].

Section gen_val_rel.
  Context {Σ} (loc_rel : loc → loc → iProp Σ).
  Let val_rel := gen_val_rel loc_rel.

  Lemma gen_val_rel_func v1 v2 v3 : loc_rel_func_law loc_rel → val_rel v1 v2 -∗ val_rel v1 v3 -∗ ⌜v2 = v3⌝.
  Proof.
    iIntros (Hf) "Hv1 Hv2".
    iInduction v2 as [[n2 | b2 | | | l2 | f2 ] | v2_1 v2_2 | v2 | v2] "IH" forall (v1 v3); try val_discr_source "Hv1"; try val_discr_target "Hv2"; try done.
    - by iPoseProof (Hf with "Hv1 Hv2") as "->".
    - iPoseProof (gen_val_rel_pair_source with "Hv1") as (??) "(-> & Hv1_1 & Hv1_2)".
      iPoseProof (gen_val_rel_pair_target with "Hv2") as (??) "(-> & Hv2_1 & Hv2_2)".
      iPoseProof ("IH" with "Hv1_1 Hv2_1") as "->".
      by iPoseProof ("IH1" with "Hv1_2 Hv2_2") as "->".
    - iPoseProof (gen_val_rel_injl_source with "Hv1") as (?) "(-> & Hv1)".
      iPoseProof (gen_val_rel_injl_target with "Hv2") as (?) "(-> & Hv2)".
      by iPoseProof ("IH" with "Hv1 Hv2") as "->".
    - iPoseProof (gen_val_rel_injr_source with "Hv1") as (?) "(-> & Hv1)".
      iPoseProof (gen_val_rel_injr_target with "Hv2") as (?) "(-> & Hv2)".
      by iPoseProof ("IH" with "Hv1 Hv2") as "->".
  Qed.
  Lemma gen_val_rel_inj v1 v2 v3 : loc_rel_inj_law loc_rel → val_rel v2 v1 -∗ val_rel v3 v1 -∗ ⌜v2 = v3⌝.
  Proof.
    iIntros (Hi) "Hv1 Hv2".
    iInduction v2 as [[n2 | b2 | | | l2 | f2 ] | v2_1 v2_2 | v2 | v2] "IH" forall (v1 v3); try val_discr_target "Hv1"; try val_discr_source "Hv2"; try done.
    - by iPoseProof (Hi with "Hv1 Hv2") as "->".
    - iPoseProof (gen_val_rel_pair_target with "Hv1") as (??) "(-> & Hv1_1 & Hv1_2)".
      iPoseProof (gen_val_rel_pair_source with "Hv2") as (??) "(-> & Hv2_1 & Hv2_2)".
      iPoseProof ("IH" with "Hv1_1 Hv2_1") as "->".
      by iPoseProof ("IH1" with "Hv1_2 Hv2_2") as "->".
    - iPoseProof (gen_val_rel_injl_target with "Hv1") as (?) "(-> & Hv1)".
      iPoseProof (gen_val_rel_injl_source with "Hv2") as (?) "(-> & Hv2)".
      by iPoseProof ("IH" with "Hv1 Hv2") as "->".
    - iPoseProof (gen_val_rel_injr_target with "Hv1") as (?) "(-> & Hv1)".
      iPoseProof (gen_val_rel_injr_source with "Hv2") as (?) "(-> & Hv2)".
      by iPoseProof ("IH" with "Hv1 Hv2") as "->".
  Qed.
End gen_val_rel.
