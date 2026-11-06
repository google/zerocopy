
From stdpp Require Import binders.
From iris.bi Require Import bi.
From iris.proofmode Require Import proofmode.
From simuliris.simulation Require Import language.
From simuliris.simulation Require Export simulation slsls.
Import bi.

(** * Logical relation

    General definition of [prog_rel], relating whole programs, and [log_rel]
    which lifts the simulation relation (the "expression relation") to open
    terms.on open terms. *)

Section fix_lang.
  Context {PROP : bi} `{!BiBUpd PROP, !BiAffine PROP, !BiPureForall PROP, !BiPersistentlyForall PROP}.
  Context {Λ : language}.
  Context `{!simulirisGS PROP Λ}.

  Set Default Proof Using "Type*".

  Implicit Types
    (e_s e_t e: expr Λ)
    (P_s P_t P: prog Λ)
    (σ_s σ_t σ : state Λ).

  (** Whole-program logical relation *)
  Definition func_rel (fn_t fn_s : func Λ) : PROP :=
    ∀ v_t v_s π, ext_rel π v_t v_s -∗
      (apply_func fn_t v_t) ⪯{π} (apply_func fn_s v_s) {{ ext_rel π }}.
  Definition prog_rel P_t P_s : PROP :=
    □ ∀ f fn_s, ⌜P_s !! f = Some fn_s⌝ →
       ∃ fn_t, ⌜P_t !! f = Some fn_t⌝ ∗ func_rel fn_t fn_s.
  Global Typeclasses Opaque prog_rel.

  Global Instance prog_rel_persistent P_t P_s : Persistent (prog_rel P_t P_s).
  Proof. rewrite /prog_rel; apply _. Qed.

  (** [prog_rel] is a congruence for program composition *)
  Lemma prog_rel_union P_t1 P_t2 P_s1 P_s2 :
    P_t1 ##ₘ P_t2 →
    prog_rel P_t1 P_s1 -∗
    prog_rel P_t2 P_s2 -∗
    prog_rel (P_t1 ∪ P_t2) (P_s1 ∪ P_s2).
  Proof.
    rewrite /prog_rel.
    iIntros (?) "#HP1 #HP2 !# %f %fn_s". iSpecialize ("HP1" $! f fn_s).
    destruct (P_s1 !! f) as [fn_s'|] eqn:Hf_s.
    - rewrite (lookup_union_Some_l _ _ _ fn_s') //.
      iIntros ([= ->]). iDestruct ("HP1" $! eq_refl) as (fn_t Hf_t) "Hrel".
      iExists fn_t. iFrame "Hrel". rewrite (lookup_union_Some_l _ _ _ fn_t) //.
    - rewrite lookup_union_r //. iClear "HP1". iIntros (Hf_s2).
      iDestruct ("HP2" $! f fn_s with "[//]") as (fn_t Hf_t) "Hrel".
      iExists fn_t. iFrame "Hrel". iPureIntro. by apply: lookup_union_Some_r.
  Qed.

  (** Typical lemma needed to show [log_rel → ctx_ref]. *)
  Lemma prog_rel_refl_insert P (fname : string) (fn_t fn_s : func Λ) :
    □ func_rel fn_t fn_s -∗
    □ (∀ f fn, ⌜P !! f = Some fn⌝ -∗ func_rel fn fn) -∗
    prog_rel (<[fname:=fn_t]> P) (<[fname:=fn_s]> P).
  Proof.
    rewrite /prog_rel.
    iIntros "#He #Hp !# %f %fn".
    destruct (decide (f = fname)) as [->|Hne].
    - rewrite !lookup_insert_eq.
      iIntros ([= <-]). iExists _. iSplitR; done.
    - rewrite !lookup_insert_ne //.
      iIntros (Hf). iExists fn. iSplitR; first done.
      by iApply "Hp".
  Qed.

  (** Relation on "contexts", lifted from a value relation:
      Well-formed substitutions closing source and target, with [X] denoting the
      free variables. *)
  Context (val_rel : val Λ → val Λ → PROP).

  Definition subst_map_rel (X : gset string) (map : gmap string (val Λ * val Λ)) : PROP :=
    [∗ set] x ∈ X,
      match map !! x with
      | Some (v_t, v_s) => val_rel v_t v_s
      | None => False
      end.

  Global Instance subst_map_rel_pers X map `{!∀ vt vs, Persistent (val_rel vt vs)} :
    Persistent (subst_map_rel X map).
  Proof.
    rewrite /subst_map_rel. apply big_sepS_persistent=>x.
    destruct (map !! x) as [[v_t v_s]|]; apply _.
  Qed.

  Lemma subst_map_rel_lookup {X map} x :
    x ∈ X →
    subst_map_rel X map -∗
    ∃ v_t v_s, ⌜map !! x = Some (v_t, v_s)⌝ ∗ val_rel v_t v_s.
  Proof.
    iIntros (Hx) "Hrel".
    iDestruct (big_sepS_elem_of _ _ x with "Hrel") as "Hrel"; first done.
    destruct (map !! x) as [[v_t v_s]|]; last done. eauto.
  Qed.

  (* FIXME requiring persistence for convenience. Probably also works without *)
  Lemma subst_map_rel_dom `{!∀ vt vs, Persistent (val_rel vt vs)} X map :
    subst_map_rel X map -∗ ⌜X ⊆ dom map⌝.
  Proof.
    rewrite /subst_map_rel. erewrite big_sepS_forall.
    2: { intros. destruct (_ !! _) as [[]|]; apply _. }
    iIntros "Hl". rewrite elem_of_subseteq.
    iIntros (x Hx). iSpecialize ("Hl" $! x Hx).
    rewrite elem_of_dom. destruct (_ !! _); eauto.
  Qed.

  Lemma subst_map_rel_weaken X1 X2 map :
    X2 ⊆ X1 →
    subst_map_rel X1 map -∗ subst_map_rel X2 map.
  Proof. iIntros (HX). iApply big_sepS_subseteq. done. Qed.

  Lemma subst_map_rel_singleton X x v_t v_s :
    X ⊆ {[x]} →
    val_rel v_t v_s -∗
    subst_map_rel X {[x:=(v_t, v_s)]}.
  Proof.
    iIntros (?) "Hrel".
    iApply (subst_map_rel_weaken {[x]}); first done.
    rewrite /subst_map_rel big_sepS_singleton lookup_singleton_eq. done.
  Qed.

  (* TODO: use [binder_delete], once we can [delete] on [gset]. *)
  Definition binder_delete_gset (b : binder) (X : gset string) :=
    match b with BAnon => X | BNamed x => X ∖ {[x]} end.

  Lemma subst_map_rel_insert X x v_t v_s map :
    subst_map_rel (binder_delete_gset x X) map -∗
    val_rel v_t v_s -∗
    subst_map_rel X (binder_insert x (v_t, v_s) map).
  Proof.
    iIntros "Hmap Hval". destruct x as [|x]; first done. simpl.
    rewrite /subst_map_rel. iApply (big_sepS_delete_2 x with "[Hval]").
    - rewrite /= lookup_insert_eq. done.
    - iApply (big_sepS_impl with "Hmap").
      iIntros "!# %x' %Hx'".
      destruct (decide (x = x')) as [<-|Hne]; first by set_solver.
      rewrite lookup_insert_ne //. auto.
  Qed.

  Lemma subst_map_rel_empty map :
    ⊢ subst_map_rel ∅ map.
  Proof. iApply big_sepS_empty. done. Qed.

  (** The core "logical relation" of our system:
      The simulation relation ("expression relation") must hold after applying
      an arbitrary well-formed closing substitution [map].

      We might define multiple logical relations for the same Simuliris
      instance, so this is parameterized separately. The "main" logical relation
      will usually choose these such that [ext_rel = val_rel ∗ thread_own], but
      further auxiliary logical relations might make different choices. *)
  (* TODO: make this not persistent? *)
  Context (thread_own : thread_id → PROP).

  Definition gen_log_rel e_t e_s : PROP :=
    □ ∀ π (map : gmap string (val Λ * val Λ)),
      subst_map_rel (free_vars e_t ∪ free_vars e_s) map -∗
      thread_own π -∗
      subst_map (fst <$> map) e_t ⪯{π} subst_map (snd <$> map) e_s
        {{ λ v_t v_s, thread_own π ∗ val_rel v_t v_s }}.

  Global Instance gen_log_rel_persistent e_t e_s : Persistent (gen_log_rel e_t e_s).
  Proof. rewrite /gen_log_rel; apply _. Qed.

  Lemma gen_log_rel_closed_1 e_t e_s π :
    free_vars e_t ∪ free_vars e_s = ∅ →
    gen_log_rel e_t e_s ⊢
      thread_own π -∗ e_t ⪯{π} e_s {{ λ v_t v_s, thread_own π ∗ val_rel v_t v_s }}.
  Proof.
    iIntros (Hclosed) "#Hrel". iSpecialize ("Hrel" $! π ∅).
    rewrite ->!fmap_empty, ->!subst_map_empty.
    rewrite Hclosed. iApply "Hrel". by iApply subst_map_rel_empty.
  Qed.

  Lemma gen_log_rel_closed e_t e_s :
    free_vars e_t ∪ free_vars e_s = ∅ →
    gen_log_rel e_t e_s ⊣⊢
      (□ ∀ π, thread_own π -∗
        e_t ⪯{π} e_s {{ λ v_t v_s, thread_own π ∗ val_rel v_t v_s }}).
  Proof.
    intros Hclosed. iSplit.
    { iIntros "#Hrel !#" (π). iApply gen_log_rel_closed_1; done. }
    iIntros "#Hsim" (π xs) "!# Hxs".
    rewrite !subst_map_closed //; set_solver.
  Qed.

  Lemma gen_log_rel_singleton e_t e_s v_t v_s arg π :
    free_vars e_t ∪ free_vars e_s ⊆ {[ arg ]} →
    gen_log_rel e_t e_s -∗
    val_rel v_t v_s -∗
    thread_own π -∗
    subst_map {[arg := v_t]} e_t ⪯{π} subst_map {[arg := v_s]} e_s
      {{ λ v_t v_s, thread_own π ∗ val_rel v_t v_s }}.
  Proof.
    iIntros (?) "Hlog Hval Hπ".
    iDestruct ("Hlog" $! _ {[arg := (v_t, v_s)]} with "[Hval] Hπ") as "Hsim".
    { by iApply subst_map_rel_singleton. }
    rewrite !map_fmap_singleton. done.
  Qed.

  (** Substitute away a single free variable in an [gen_log_rel]. *)
  Lemma gen_log_rel_subst x e_t e_s dummy {HPers : ∀ vt vs, Persistent (val_rel vt vs)} :
    (* In case [x] is not free, we need a reflexive "default value". (Really we
       should require [x ∈ free_vars e_t ∪ free_vars e_s] here, but that is hard
       for the [log_rel] automation tactic to prove, so we use this approach
       instead.) *)
    □ val_rel dummy dummy -∗
    (□ ∀ (v_t v_s : val Λ), val_rel v_t v_s -∗
      gen_log_rel (subst_map {[x:=v_t]} e_t) (subst_map {[x:=v_s]} e_s)) -∗
    gen_log_rel e_t e_s.
  Proof.
    iIntros "#Hdummy #Hsim %π %xs !# #Hxs Hπ".
    destruct (decide (x ∈ free_vars e_t ∪ free_vars e_s)) as [Hin|Hnotin]; last first.
    { iSpecialize ("Hsim" $! dummy dummy).
      rewrite ->(subst_map_free_vars _ ∅ e_t); last first.
      { intros x' ?. assert (x ≠ x') by set_solver.
        rewrite lookup_singleton_ne //. }
      rewrite ->(subst_map_free_vars _ ∅ e_s); last first.
      { intros x' ?. assert (x ≠ x') by set_solver.
        rewrite lookup_singleton_ne //. }
      rewrite !subst_map_empty.
      iApply "Hsim"; eauto. }
    iDestruct (subst_map_rel_lookup x with "Hxs") as (v_t v_s Hv) "Hrel"; first done.
    iSpecialize ("Hsim" $! v_t v_s with "Hrel").
    iSpecialize ("Hsim" $! π xs with "[Hxs]").
    { iApply (subst_map_rel_weaken with "Hxs").
      rewrite !free_vars_subst_map. set_solver. }
    rewrite !subst_map_subst_map.
    replace ({[x := v_t]} ∪ (fst <$> xs)) with (fst <$> xs); last first.
    { rewrite -insert_union_singleton_l insert_id //.
      rewrite lookup_fmap Hv //. }
    replace ({[x := v_s]} ∪ (snd <$> xs)) with (snd <$> xs); last first.
    { rewrite -insert_union_singleton_l insert_id //.
      rewrite lookup_fmap Hv //. }
    iApply "Hsim"; eauto.
  Qed.

End fix_lang.

Arguments prog_rel : simpl never.
Arguments gen_log_rel : simpl never.
Global Typeclasses Opaque prog_rel gen_log_rel.
