(** This file has been adapted from the Iris development, available at
  https://gitlab.mpi-sws.org/iris/iris
*)

From Stdlib.QArith Require Import Qcanon.
From iris.algebra Require Export view gmap frac dfrac.
From iris.algebra Require Import local_updates proofmode_classes big_op.
From iris.algebra Require Import csum excl.
From simuliris.stacked_borrows Require Export defs.

(** An adaption of gmap_view to use tag_kind to control permissions of fragments and to reflect that into the authoritative fragment.
(gmap_view has since been updated so we could now use it directly, but this code predates the generalized gmap_view for arbitrary CRMA.) *)

Section tag_kind.
  Context {SI : sidx}.

  (* Currently, we place a strong restriction on the shape of a location's stack:
    A tag can be of one of two kinds:
    - tk_pub: the tag is public (can be shared, assertion is persistent)
    - tk_unq: the tag is unique (cannot be shared, assertion is not persistent).
    - tk_loc: the tag is local
   *)
  (* TODO: allow a local update from tk_unq to tk_pub *)
  Definition tagKindR := csumR (exclR unitO) (csumR (exclR unitO) unitR).


  Canonical Structure tag_kindO := leibnizO tag_kind.

  Global Instance tagKindR_discrete : CmraDiscrete tagKindR.
  Proof. apply _. Qed.

  Definition to_tgkR (tk: tag_kind) : tagKindR :=
    match tk with
    | tk_unq => Cinr $ Cinl $ Excl ()
    | tk_pub => Cinr $ Cinr ()
    | tk_local => Cinl $ Excl ()
    end.

  Lemma to_tgkR_valid tk : ✓ (to_tgkR tk).
  Proof. destruct tk; done. Qed.
  Lemma to_tgkR_validN tk n : ✓{n} (to_tgkR tk).
  Proof. destruct tk; done. Qed.

  Global Instance to_tgkR_inj n : Inj (=) (dist n) to_tgkR.
  Proof.
    intros [] []; simpl; first [done | inversion 1];
    match goal with
    | H : Cinl _ ≡{_}≡ Cinr _ |- _ => inversion H
    | H : Cinr _ ≡{_}≡ Cinl _ |- _ => inversion H
    end.
  Qed.

  Lemma tgkR_validN_inv tkr n : ✓{n} tkr → ∃ tk, tkr ≡ to_tgkR tk.
  Proof.
    rewrite -cmra_discrete_valid_iff. destruct tkr as [c | [c|c|] | ]; simpl; try by move => [].
    - destruct c as [u|]; last move => []. destruct u; intros. exists tk_local. done.
    - destruct c as [u|]; last move => []. destruct u; intros. exists tk_unq. done.
    - destruct c. intros. exists tk_pub; done.
  Qed.

  Global Instance to_tgkR_unq_excl : Exclusive (to_tgkR tk_unq).
  Proof. intros [ | [ [] | [] | ]| ]; simpl; [ intros [] ..]. Qed.
  Global Instance to_tgkR_local_excl : Exclusive (to_tgkR tk_local).
  Proof. intros [ | [ [] | [] | ]| ]; simpl; [ intros [] ..]. Qed.
  Lemma to_tgkR_op_validN n tk tk' : ✓{n} (to_tgkR tk ⋅ to_tgkR tk') → tk = tk_pub ∧ tk' = tk_pub.
  Proof. destruct tk, tk'; simpl; by intros []. Qed.
  Lemma to_tgkR_op_valid tk tk' : ✓ (to_tgkR tk ⋅ to_tgkR tk') → tk = tk_pub ∧ tk' = tk_pub.
  Proof. destruct tk, tk'; simpl; by intros []. Qed.

  Lemma tagKindR_incl_eq (k1 k2: tagKindR):
    ✓ k2 → k1 ≼ k2 → k1 ≡ k2.
  Proof.
    move => VAL /csum_included
      [?|[[? [? [? [? INCL]]]]|[x1 [x2 [? [? INCL]]]]]]; subst; [done|..].
    - exfalso. eapply exclusive_included; [..|apply INCL|apply VAL]; apply _.
    - move : INCL => /csum_included
        [? |[[? [? [? [? INCL]]]]|[[] [[] [? [? LE]]]]]]; subst; [done|..|done].
      exfalso. eapply exclusive_included; [..|apply INCL|apply VAL]; apply _.
  Qed.
End tag_kind.

Local Definition tkmap_view_fragUR {SI : sidx} (K : Type) `{Countable K} (V : ofe) : ucmra :=
  gmapUR K (prodR tagKindR (agreeR V)).
(** View relation. *)
Section rel.
  Context {SI : sidx} (K : Type) `{Countable K} (V : ofe).
  Implicit Types (m : gmap K (tag_kind * V)) (k : K) (v : V) (n : SI).
  Implicit Types (f : gmap K (tagKindR * agree V)).

  Local Definition tkmap_view_rel_raw n m f : Prop :=
    map_Forall (λ k dv, ∃ v tk, dv.2 ≡{n}≡ to_agree v ∧ dv.1 ≡{n}≡ to_tgkR tk ∧ m !! k = Some (tk, v)) f.


  Local Lemma tkmap_view_rel_raw_mono n1 n2 m1 m2 f1 f2 :
    tkmap_view_rel_raw n1 m1 f1 →
    m1 ≡{n2}≡ m2 →
    f2 ≼{n2} f1 →
    (n2 ≤ n1)%sidx →
    tkmap_view_rel_raw n2 m2 f2.
  Proof.
    intros Hrel Hm Hf Hn k [tk va] Hk.
    (* For some reason applying the lemma in [Hf] does not work... *)
    destruct (lookup_includedN n2 f2 f1) as [Hf' _]. specialize (Hf' Hf). clear Hf.
    specialize (Hf' k). rewrite Hk in Hf'.
    apply option_includedN in Hf'.
    destruct Hf' as [[=]|(? & [tk' va'] & [= <-] & Hf1 & Hincl)].
    specialize (Hrel _ _ Hf1) as (v & tk0 & Hagree & Htk & Hm1). simpl in *.
    specialize (Hm k).
    edestruct (dist_Some_inv_l _ _ _ _ Hm Hm1) as ((tk'' & v') & Hm2 & Hv).
    destruct Hv as [Htk0 Hv]; simpl in *.
    exists v', tk''. rewrite !assoc. split; last done.
    rewrite -Hv.
    destruct Hincl as [[Heqq Heqva]|[Hinclq Hinclva]%pair_includedN].
    - simpl in *. split_and!.
      + rewrite Heqva. eapply dist_le; last eassumption. done.
      + rewrite <-discrete_iff in Heqq; last by apply _.
        simplify_eq. rewrite -Htk0.
        eapply dist_le'; done.
    - split_and!.
      + etrans; last first.
        { eapply dist_le; last eassumption. done. }
        eapply agree_valid_includedN; last done.
        eapply cmra_validN_le; last eassumption.
        rewrite Hagree. done.
      + rewrite <-cmra_discrete_included_iff in Hinclq.
        clear -Htk0 Htk Hinclq Hn.
        rewrite -Htk0.
        etrans. 2: { eapply dist_le; done. }
        apply discrete_iff; first apply _. eapply tagKindR_incl_eq; last done.
        apply discrete_iff in Htk; last apply _. rewrite Htk.
        apply to_tgkR_valid.
  Qed.

  Local Lemma tkmap_view_rel_raw_valid n m f :
    tkmap_view_rel_raw n m f → ✓{n} f.
  Proof.
    intros Hrel k. destruct (f !! k) as [[tkr va]|] eqn:Hf; rewrite Hf; last done.
    specialize (Hrel _ _ Hf) as (v & tk & Hagree & Htk & Hm1). simpl in *.
    split; simpl.
    - rewrite Htk. apply cmra_discrete_valid_iff. destruct tk; done.
    - rewrite Hagree. done.
  Qed.

  Local Lemma tkmap_view_rel_raw_unit n :
    ∃ m, tkmap_view_rel_raw n m ε.
  Proof. exists ∅. apply: map_Forall_empty. Qed.

  Local Canonical Structure tkmap_view_rel :
      view_rel (gmapO K (prodO tag_kindO V)) (tkmap_view_fragUR K V) :=
    ViewRel tkmap_view_rel_raw tkmap_view_rel_raw_mono
            tkmap_view_rel_raw_valid tkmap_view_rel_raw_unit.

  Local Lemma tkmap_view_rel_exists n (f : gmap K (tagKindR * agreeR V)) :
    (∃ m, tkmap_view_rel n m f) ↔ ✓{n} f.
  Proof.
    split.
    { intros [m Hrel]. eapply tkmap_view_rel_raw_valid, Hrel. }
    intros Hf.
    cut (∃ m, tkmap_view_rel n m f ∧ ∀ k, f !! k = None → m !! k = None).
    { naive_solver. }
    induction f as [|k [tk ag] f Hk' IH] using map_ind.
    { exists ∅. split; [|done]. apply: map_Forall_empty. }
    move: (Hf k). rewrite lookup_insert_eq=> -[/= Hv ?].
    destruct (to_agree_uninjN n ag) as [v ?]; [done|].
    destruct IH as (m & Hm & Hdom).
    { intros k'. destruct (decide (k = k')) as [->|?]; [by rewrite Hk'|].
      move: (Hf k'). by rewrite lookup_insert_ne. }
    apply tgkR_validN_inv in Hv as (tk' & Htk').
    exists (<[k:=(tk', v)]> m).
    rewrite /tkmap_view_rel /= /tkmap_view_rel_raw map_Forall_insert //=. split_and!.
    - exists v, tk'. by rewrite lookup_insert_eq Htk'.
    - eapply map_Forall_impl; [apply Hm|]; simpl.
      intros k' [dq' ag'] (v'&?&?&?). exists v'.
      rewrite lookup_insert_ne; naive_solver.
    - intros k'. rewrite !lookup_insert_None. naive_solver.
  Qed.

  Local Lemma tkmap_view_rel_unit n m : tkmap_view_rel n m ε.
  Proof. apply: map_Forall_empty. Qed.

  Local Lemma tkmap_view_rel_discrete :
    OfeDiscrete V → ViewRelDiscrete tkmap_view_rel.
  Proof.
    intros ? n m f Hrel k [tkr va] Hk.
    destruct (Hrel _ _ Hk) as (v & tk & Hagree & Hdval & Hm).
    exists v, tk. split_and!; last by auto.
    - eapply discrete_iff; first by apply _.
      eapply discrete_iff; first by apply _.
      done.
    - eapply discrete_iff; first by apply _.
      eapply discrete_iff; first by apply _.
      done.
  Qed.
End rel.

Local Existing Instance tkmap_view_rel_discrete.

(** [tkmap_view] is a notation to give canonical structure search the chance
to infer the right instances (see [auth]). *)
Notation tkmap_view K V := (view (@tkmap_view_rel_raw K _ _ V)).
Definition tkmap_viewO {SI : sidx} (K : Type) `{Countable K} (V : ofe) : ofe :=
  viewO (tkmap_view_rel K V).
Definition tkmap_viewR {SI : sidx} (K : Type) `{Countable K} (V : ofe) : cmra :=
  viewR (tkmap_view_rel K V).
Definition tkmap_viewUR {SI : sidx} (K : Type) `{Countable K} (V : ofe) : ucmra :=
  viewUR (tkmap_view_rel K V).

Section definitions.
  Context {SI : sidx} {K : Type} `{Countable K} {V : ofe}.

  Definition tkmap_view_auth (q : frac) (m : gmap K (tag_kind * V)) : tkmap_viewR K V :=
    ●V{#q} m.
  Definition tkmap_view_frag (k : K) (tk : tag_kind) (v : V) : tkmap_viewR K V :=
    ◯V {[k := (to_tgkR tk, to_agree v)]}.
End definitions.

Section lemmas.
  Context {SI : sidx} {K : Type} `{Countable K} {V : ofe}.
  Implicit Types (m : gmap K (tag_kind * V)) (k : K) (q : Qp) (t : tag_kind) (v : V).

  Global Instance : Params (@tkmap_view_auth) 6 := {}.
  Global Instance tkmap_view_auth_ne q : NonExpansive (tkmap_view_auth (K:=K) (V:=V) q).
  Proof. solve_proper. Qed.
  Global Instance tkmap_view_auth_proper q : Proper ((≡) ==> (≡)) (tkmap_view_auth (K:=K) (V:=V) q).
  Proof. apply ne_proper, _. Qed.

  Global Instance : Params (@tkmap_view_frag) 7 := {}.
  Global Instance tkmap_view_frag_ne k tk : NonExpansive (tkmap_view_frag (K:=K) (V:=V) k tk).
  Proof. solve_proper. Qed.
  Global Instance tkmap_view_frag_proper k tk : Proper ((≡) ==> (≡)) (tkmap_view_frag (K:=K) (V:=V) k tk).
  Proof. apply ne_proper, _. Qed.

  (* Helper lemmas *)
  Local Lemma tkmap_view_rel_lookup n m k tk v :
    tkmap_view_rel K V n m {[k := (to_tgkR tk, to_agree v)]} ↔ m !! k ≡{n}≡ Some (tk, v).
  Proof.
    split.
    - intros Hrel.
      edestruct (Hrel k) as (v' & tk' & Hagree & Htk & ->).
      { rewrite lookup_singleton_eq. done. }
      simpl in *. apply (inj _) in Hagree. rewrite Hagree.
      apply (inj _) in Htk. rewrite Htk.
      done.
    - intros ([tk' v'] & Hs & Hm & Hv')%dist_Some_inv_r' k' [tkr va].
      destruct (decide (k = k')) as [<-|Hne]; last by rewrite lookup_singleton_ne.
      rewrite lookup_singleton_eq. intros [= <- <-]. simpl in *.
      exists v', tk'. split_and!; by rewrite ?Hv' ?Hm.
  Qed.

  (** Composition and validity *)
  Lemma tkmap_view_auth_frac_op p q m :
    tkmap_view_auth (p + q) m ≡ tkmap_view_auth p m ⋅ tkmap_view_auth q m.
  Proof. by rewrite /tkmap_view_auth -dfrac_op_own view_auth_dfrac_op. Qed.
  Global Instance tkmap_view_auth_frac_is_op q q1 q2 m :
    IsOp q q1 q2 → IsOp' (tkmap_view_auth q m) (tkmap_view_auth q1 m) (tkmap_view_auth q2 m).
  Proof. rewrite /tkmap_view_auth. apply _. Qed.

  Lemma tkmap_view_auth_frac_op_invN n p m1 q m2 :
    ✓{n} (tkmap_view_auth p m1 ⋅ tkmap_view_auth q m2) → m1 ≡{n}≡ m2.
  Proof. apply view_auth_dfrac_op_invN. Qed.
  Lemma tkmap_view_auth_frac_op_inv p m1 q m2 :
    ✓ (tkmap_view_auth p m1 ⋅ tkmap_view_auth q m2) → m1 ≡ m2.
  Proof. apply view_auth_dfrac_op_inv. Qed.
  Lemma tkmap_view_auth_frac_op_inv_L `{!LeibnizEquiv V} q m1 p m2 :
    ✓ (tkmap_view_auth p m1 ⋅ tkmap_view_auth q m2) → m1 = m2.
  Proof. apply view_auth_dfrac_op_inv_L, _. Qed.

  Lemma tkmap_view_auth_frac_valid m q : ✓ tkmap_view_auth q m ↔ (q ≤ 1)%Qp.
  Proof.
    rewrite view_auth_dfrac_valid. intuition eauto using tkmap_view_rel_unit.
  Qed.
  Lemma tkmap_view_auth_valid m : ✓ tkmap_view_auth 1 m.
  Proof. rewrite tkmap_view_auth_frac_valid. done. Qed.

  Lemma tkmap_view_auth_frac_op_validN n q1 q2 m1 m2 :
    ✓{n} (tkmap_view_auth q1 m1 ⋅ tkmap_view_auth q2 m2) ↔ ✓ (q1 + q2)%Qp ∧ m1 ≡{n}≡ m2.
  Proof.
    rewrite view_auth_dfrac_op_validN. intuition eauto using tkmap_view_rel_unit.
  Qed.
  Lemma tkmap_view_auth_frac_op_valid q1 q2 m1 m2 :
    ✓ (tkmap_view_auth q1 m1 ⋅ tkmap_view_auth q2 m2) ↔ (q1 + q2 ≤ 1)%Qp ∧ m1 ≡ m2.
  Proof.
    rewrite view_auth_dfrac_op_valid. intuition eauto using tkmap_view_rel_unit.
  Qed.
  Lemma tkmap_view_auth_frac_op_valid_L `{!LeibnizEquiv V} q1 q2 m1 m2 :
    ✓ (tkmap_view_auth q1 m1 ⋅ tkmap_view_auth q2 m2) ↔ ✓ (q1 + q2)%Qp ∧ m1 = m2.
  Proof. unfold_leibniz. apply tkmap_view_auth_frac_op_valid. Qed.

  Lemma tkmap_view_auth_op_validN n m1 m2 :
    ✓{n} (tkmap_view_auth 1 m1 ⋅ tkmap_view_auth 1 m2) ↔ False.
  Proof. apply view_auth_op_validN. Qed.
  Lemma tkmap_view_auth_op_valid m1 m2 :
    ✓ (tkmap_view_auth 1 m1 ⋅ tkmap_view_auth 1 m2) ↔ False.
  Proof. apply view_auth_op_valid. Qed.

  Lemma tkmap_view_frag_validN n k tk v : ✓{n} tkmap_view_frag k tk v.
  Proof.
    rewrite view_frag_validN tkmap_view_rel_exists singleton_validN pair_validN.
    split; last done. apply to_tgkR_validN.
  Qed.
  Lemma tkmap_view_frag_valid k tk v : ✓ tkmap_view_frag k tk v.
  Proof. rewrite cmra_valid_validN => n. apply tkmap_view_frag_validN. Qed.

  (*Lemma tkmap_view_frag_op l tkr1 tkr2 v :*)
    (*tkmap_view_frag l (tkr1 ⋅ tkr2) v ≡ tkmap_view_frag l tkr1 v ⋅ tkmap_view_frag l tkr2 v.*)
  (*Proof. rewrite -view_frag_op singleton_op -pair_op agree_idemp //. Qed.*)

  Lemma tkmap_view_frag_op_validN n k tk1 tk2 v1 v2 :
    ✓{n} (tkmap_view_frag k tk1 v1 ⋅ tkmap_view_frag k tk2 v2) ↔
      ✓ (to_tgkR tk1 ⋅ to_tgkR tk2) ∧ v1 ≡{n}≡ v2.
  Proof.
    rewrite view_frag_validN tkmap_view_rel_exists singleton_op singleton_validN.
    by rewrite -pair_op pair_validN to_agree_op_validN.
  Qed.
  Lemma tkmap_view_frag_op_valid k tk1 tk2 v1 v2 :
    ✓ (tkmap_view_frag k tk1 v1 ⋅ tkmap_view_frag k tk2 v2) ↔ ✓ (to_tgkR tk1 ⋅ to_tgkR tk2) ∧ v1 ≡ v2.
  Proof.
    rewrite view_frag_valid. setoid_rewrite tkmap_view_rel_exists.
    rewrite -cmra_valid_validN singleton_op singleton_valid.
    by rewrite -pair_op pair_valid to_agree_op_valid.
  Qed.

  Lemma tkmap_view_frag_op_valid_L `{!LeibnizEquiv V} k tk1 tk2 v1 v2 :
    ✓ (tkmap_view_frag k tk1 v1 ⋅ tkmap_view_frag k tk2 v2) ↔ ✓ (to_tgkR tk1 ⋅ to_tgkR tk2) ∧ v1 = v2.
  Proof. unfold_leibniz. apply tkmap_view_frag_op_valid. Qed.

  Lemma tkmap_view_both_frac_validN n q m k tk v :
    ✓{n} (tkmap_view_auth q m ⋅ tkmap_view_frag k tk v) ↔
      (q ≤ 1)%Qp ∧ m !! k ≡{n}≡ Some (tk, v).
  Proof.
    rewrite /tkmap_view_auth /tkmap_view_frag.
    rewrite view_both_dfrac_validN tkmap_view_rel_lookup.
    naive_solver.
  Qed.
  Lemma tkmap_view_both_validN n m k tk v :
    ✓{n} (tkmap_view_auth 1 m ⋅ tkmap_view_frag k tk v) ↔
      m !! k ≡{n}≡ Some (tk, v).
  Proof. rewrite tkmap_view_both_frac_validN. naive_solver done. Qed.
  Lemma tkmap_view_both_frac_valid q m k tk v :
    ✓ (tkmap_view_auth q m ⋅ tkmap_view_frag k tk v) ↔
    (q ≤ 1)%Qp ∧ m !! k ≡ Some (tk, v).
  Proof.
    rewrite /tkmap_view_auth /tkmap_view_frag.
    rewrite view_both_dfrac_valid. setoid_rewrite tkmap_view_rel_lookup.
    split=>[[Hq Hm]|[Hq Hm]].
    - split; first done. apply equiv_dist=>n. apply Hm.
    - split; first done. intros n. revert n. apply equiv_dist. apply Hm.
  Qed.
  Lemma tkmap_view_both_frac_valid_L `{!LeibnizEquiv V} q m k tk v :
    ✓ (tkmap_view_auth q m ⋅ tkmap_view_frag k tk v) ↔
    ✓ q ∧ m !! k = Some (tk, v).
  Proof. unfold_leibniz. apply tkmap_view_both_frac_valid. Qed.
  Lemma tkmap_view_both_valid m k tk v :
    ✓ (tkmap_view_auth 1 m ⋅ tkmap_view_frag k tk v) ↔ m !! k ≡ Some (tk, v).
  Proof. rewrite tkmap_view_both_frac_valid. naive_solver done. Qed.
  Lemma tkmap_view_both_valid_L `{!LeibnizEquiv V} m k tk v :
    ✓ (tkmap_view_auth 1 m ⋅ tkmap_view_frag k tk v) ↔ m !! k = Some (tk, v).
  Proof. unfold_leibniz. apply tkmap_view_both_valid. Qed.

  (** Frame-preserving updates *)
  Lemma tkmap_view_alloc m k tk v :
    m !! k = None →
    tkmap_view_auth 1 m ~~> tkmap_view_auth 1 (<[k := (tk, v)]> m) ⋅ tkmap_view_frag k tk v.
  Proof.
    intros Hfresh. apply view_update_alloc=>n bf Hrel j [tkr va] /=.
    rewrite lookup_op. destruct (decide (j = k)) as [->|Hne].
    - assert (bf !! k = None) as Hbf.
      { destruct (bf !! k) as [[tkr' va']|] eqn:Hbf; last done.
        specialize (Hrel _ _ Hbf). destruct Hrel as (v' & tk' & _ & _ & Hm).
        exfalso. rewrite Hm in Hfresh. done. }
      rewrite lookup_singleton_eq Hbf right_id.
      intros [= <- <-]. eexists; eexists. do 2 (split; first done).
      rewrite lookup_insert_eq. done.
    - rewrite lookup_singleton_ne; last done.
      rewrite left_id=>Hbf.
      specialize (Hrel _ _ Hbf). destruct Hrel as (v' & tk' & ? & ? & Hm).
      eexists; eexists. do 2 (split; first done).
      rewrite lookup_insert_ne //.
  Qed.

  Lemma tkmap_view_alloc_big m m' :
    m' ##ₘ m →
    tkmap_view_auth 1 m ~~>
      tkmap_view_auth 1 (m' ∪ m) ⋅ ([^op map] k↦va ∈ m', tkmap_view_frag k va.1 va.2).
  Proof.
    intros. induction m' as [|k [tk v] m' ? IH] using map_ind; decompose_map_disjoint.
    { rewrite big_opM_empty left_id_L right_id. done. }
    etrans; first by apply IH.
    rewrite big_opM_insert // assoc.
    apply cmra_update_op; last done.
    rewrite -insert_union_l. apply (tkmap_view_alloc _ k tk v).
    by apply lookup_union_None.
  Qed.

  Lemma tkmap_view_delete m k v tk :
    tk = tk_local ∨ tk = tk_unq →
    tkmap_view_auth 1 m ⋅ tkmap_view_frag k tk v ~~>
    tkmap_view_auth 1 (delete k m).
  Proof.
    intros Htk_eq.
    apply view_update_dealloc=>n bf Hrel j [tkr va] Hbf /=.
    destruct (decide (j = k)) as [->|Hne].
    - edestruct (Hrel k) as (v' & tk' & _ & Htk & _).
      { rewrite lookup_op Hbf lookup_singleton_eq -Some_op. done. }
      exfalso.
      assert (Exclusive (to_tgkR tk)) as Hexcl.
      { destruct Htk_eq as [-> | ->]; [apply to_tgkR_local_excl | apply to_tgkR_unq_excl]. }
      apply: Hexcl.
      apply discrete_iff in Htk; last apply _. apply cmra_discrete_valid_iff.
      setoid_rewrite Htk. apply to_tgkR_valid.
    - edestruct (Hrel j) as (v' & tk' & ? & ? & Hm).
      { rewrite lookup_op lookup_singleton_ne // Hbf. done. }
      exists v', tk'. do 2 (split; first done).
      rewrite lookup_delete_ne //.
  Qed.

  Lemma tkmap_view_update m k tk v v' :
    tk = tk_local ∨ tk = tk_unq →
    tkmap_view_auth 1 m ⋅ tkmap_view_frag k tk v ~~>
      tkmap_view_auth 1 (<[k := (tk, v')]> m) ⋅ tkmap_view_frag k tk v'.
  Proof.
    intros Htk_eq; apply view_update=>n bf Hrel j [tkr va] /=.
    rewrite lookup_op. destruct (decide (j = k)) as [->|Hne].
    - assert (bf !! k = None) as Hbf.
      { move: Hrel =>/view_rel_validN /(_ k).
        rewrite lookup_op lookup_singleton_eq.
        destruct (bf !! k) as [[tkr' va']|] eqn:Hbf; last done.
        rewrite Hbf. clear Hbf.
        rewrite -Some_op -pair_op.
        assert (Exclusive (to_tgkR tk)) as Hexcl.
        { destruct Htk_eq as [-> | ->]; [apply to_tgkR_local_excl | apply to_tgkR_unq_excl]. }
        move=>[/= /Hexcl Hdf _]. done. }
      rewrite Hbf right_id lookup_singleton_eq. clear Hbf.
      intros [= <- <-].
      eexists; exists tk. split_and!; [done | done | ].
      rewrite lookup_insert_eq. done.
    - rewrite lookup_singleton_ne; last done.
      rewrite left_id=>Hbf.
      edestruct (Hrel j) as (v'' & tk'' & ? & ? & Hm).
      { rewrite lookup_op lookup_singleton_ne // left_id. done. }
      simpl in *. eexists; exists tk''. do 2 (split; first done).
      rewrite lookup_insert_ne //.
  Qed.

  Lemma tkmap_view_make_public m k v :
    tkmap_view_auth 1 m ⋅ tkmap_view_frag k tk_unq v ~~>
      tkmap_view_auth 1 (<[k := (tk_pub, v)]> m) ⋅ tkmap_view_frag k tk_pub v.
  Proof.
    (* TODO: change def of tgkR to enable local update tk_unq ~~> tk_pub *)
  Abort.
  (*Proof.*)
    (*apply view_update_frag=>m n bf Hrel j [df va] /=.*)
    (*rewrite lookup_op. destruct (decide (j = k)) as [->|Hne].*)
    (*- rewrite lookup_singleton_eq.*)
      (*edestruct (Hrel k ((dq, to_agree v) ⋅? bf !! k)) as (v' & Hdf & Hva & Hm).*)
      (*{ rewrite lookup_op lookup_singleton_eq.*)
        (*destruct (bf !! k) eqn:Hbf; by rewrite Hbf. }*)
      (*rewrite Some_op_opM. intros [= Hbf].*)
      (*exists v'. rewrite assoc; split; last done.*)
      (*destruct (bf !! k) as [[df' va']|] eqn:Hbfk; rewrite Hbfk in Hbf; clear Hbfk.*)
      (*+ simpl in *. rewrite -pair_op in Hbf.*)
        (*move:Hbf=>[= <- <-]. split; first done.*)
        (*eapply cmra_discrete_valid.*)
        (*eapply (dfrac_discard_update _ _ (Some df')).*)
        (*apply cmra_discrete_valid_iff. done.*)
      (*+ simpl in *. move:Hbf=>[= <- <-]. split; done.*)
    (*- rewrite lookup_singleton_ne //.*)
      (*rewrite left_id=>Hbf.*)
      (*edestruct (Hrel j) as (v'' & ? & ? & Hm).*)
      (*{ rewrite lookup_op lookup_singleton_ne // left_id. done. }*)
      (*simpl in *. eexists. do 2 (split; first done). done.*)
  (*Qed.*)

  (** Typeclass instances *)
  Global Instance tkmap_view_frag_core_id k v : CoreId (tkmap_view_frag k tk_pub v).
  Proof. apply _. Qed.
  Global Instance tkmap_view_cmra_discrete : OfeDiscrete V → CmraDiscrete (tkmap_viewR K V).
  Proof. apply _. Qed.
End lemmas.

(** Functor *)
(*Program Definition tkmap_viewURF (K : Type) `{Countable K} (F : oFunctor) : urFunctor := {|*)
  (*urFunctor_car A _ B _ := tkmap_viewUR K (oFunctor_car F A B);*)
  (*urFunctor_map A1 _ A2 _ B1 _ B2 _ fg :=*)
    (*viewO_map (rel:=tkmap_view_rel K (oFunctor_car F A1 B1))*)
              (*(rel':=tkmap_view_rel K (oFunctor_car F A2 B2))*)
              (*(gmapO_map (K:=K) (oFunctor_map F fg))*)
              (*(gmapO_map (K:=K) (prodO_map cid (agreeO_map (oFunctor_map F fg))))*)
(*|}.*)
(*Next Obligation.*)
  (*intros K ?? F A1 ? A2 ? B1 ? B2 ? n f g Hfg.*)
  (*apply viewO_map_ne.*)
  (*- apply gmapO_map_ne, oFunctor_map_ne. done.*)
  (*- apply gmapO_map_ne. apply prodO_map_ne; first done.*)
    (*apply agreeO_map_ne, oFunctor_map_ne. done.*)
(*Qed.*)
(*Next Obligation.*)
  (*intros K ?? F A ? B ? x; simpl in *. rewrite -{2}(view_map_id x).*)
  (*apply (view_map_ext _ _ _ _)=> y.*)
  (*- rewrite /= -{2}(map_fmap_id y).*)
    (*apply map_fmap_equiv_ext=>k ??.*)
    (*apply oFunctor_map_id.*)
  (*- rewrite /= -{2}(map_fmap_id y).*)
    (*apply map_fmap_equiv_ext=>k [df va] ?.*)
    (*split; first done. simpl.*)
    (*rewrite -{2}(agree_map_id va).*)
    (*eapply agree_map_ext; first by apply _.*)
    (*apply oFunctor_map_id.*)
(*Qed.*)
(*Next Obligation.*)
  (*intros K ?? F A1 ? A2 ? A3 ? B1 ? B2 ? B3 ? f g f' g' x; simpl in *.*)
  (*rewrite -view_map_compose.*)
  (*apply (view_map_ext _ _ _ _)=> y.*)
  (*- rewrite /= -map_fmap_compose.*)
    (*apply map_fmap_equiv_ext=>k ??.*)
    (*apply oFunctor_map_compose.*)
  (*- rewrite /= -map_fmap_compose.*)
    (*apply map_fmap_equiv_ext=>k [df va] ?.*)
    (*split; first done. simpl.*)
    (*rewrite -agree_map_compose.*)
    (*eapply agree_map_ext; first by apply _.*)
    (*apply oFunctor_map_compose.*)
(*Qed.*)
(*Next Obligation.*)
  (*intros K ?? F A1 ? A2 ? B1 ? B2 ? fg; simpl.*)
  (*apply: view_map_cmra_morphism; [apply _..|]=> n m f.*)
  (*intros Hrel k [df va] Hf. move: Hf.*)
  (*rewrite !lookup_fmap.*)
  (*destruct (f !! k) as [[df' va']|] eqn:Hfk; rewrite Hfk; last done.*)
  (*simpl=>[= <- <-].*)
  (*specialize (Hrel _ _ Hfk). simpl in Hrel. destruct Hrel as (v & Hagree & Hdval & Hm).*)
  (*exists (oFunctor_map F fg v).*)
  (*rewrite Hm. split; last by auto.*)
  (*rewrite Hagree. rewrite agree_map_to_agree. done.*)
(*Qed.*)

(*Global Instance gmap_viewURF_contractive (K : Type) `{Countable K} F :*)
  (*oFunctorContractive F → urFunctorContractive (gmap_viewURF K F).*)
(*Proof.*)
  (*intros ? A1 ? A2 ? B1 ? B2 ? n f g Hfg.*)
  (*apply viewO_map_ne.*)
  (*- apply gmapO_map_ne. apply oFunctor_map_contractive. done.*)
  (*- apply gmapO_map_ne. apply prodO_map_ne; first done.*)
    (*apply agreeO_map_ne, oFunctor_map_contractive. done.*)
(*Qed.*)

(*Program Definition gmap_viewRF (K : Type) `{Countable K} (F : oFunctor) : rFunctor := {|*)
  (*rFunctor_car A _ B _ := gmap_viewR K (oFunctor_car F A B);*)
  (*rFunctor_map A1 _ A2 _ B1 _ B2 _ fg :=*)
    (*viewO_map (rel:=gmap_view_rel K (oFunctor_car F A1 B1))*)
              (*(rel':=gmap_view_rel K (oFunctor_car F A2 B2))*)
              (*(gmapO_map (K:=K) (oFunctor_map F fg))*)
              (*(gmapO_map (K:=K) (prodO_map cid (agreeO_map (oFunctor_map F fg))))*)
(*|}.*)
(*Solve Obligations with apply gmap_viewURF.*)

(*Global Instance gmap_viewRF_contractive (K : Type) `{Countable K} F :*)
  (*oFunctorContractive F → rFunctorContractive (gmap_viewRF K F).*)
(*Proof. apply gmap_viewURF_contractive. Qed.*)

Global Typeclasses Opaque tkmap_view_auth tkmap_view_frag.



(** ** Proofmode lemmas *)
From iris.proofmode Require Import proofmode.
From iris.base_logic.lib Require Export own.
From iris.bi.lib Require Import fractional.

(** The CMRA we need.
FIXME: This is intentionally discrete-only, but
should we support setoids via [Equiv]? *)
Class tkmapG Σ (K V : Type) `{Countable K} := TkMapG {
  tkmap_inG :: inG Σ (tkmap_viewR K (leibnizO V));
}.
Definition tkmapΣ (K V : Type) `{Countable K} : gFunctors :=
  #[ GFunctor (tkmap_viewR K (leibnizO V)) ].

Global Instance subG_tkmapΣ Σ (K V : Type) `{Countable K} :
  subG (tkmapΣ K V) Σ → tkmapG Σ K V.
Proof. solve_inG. Qed.

Section definitions.
  Context `{tkmapG Σ K V}.

  Definition tkmap_auth_def (γ : gname) (q : Qp) (m : gmap K (tag_kind * V)) : iProp Σ :=
    own γ (tkmap_view_auth (V:=leibnizO V) q m).
  Definition tkmap_auth_aux : seal (@tkmap_auth_def). Proof. by eexists. Qed.
  Definition tkmap_auth := tkmap_auth_aux.(unseal).
  Definition tkmap_auth_eq : @tkmap_auth = @tkmap_auth_def := tkmap_auth_aux.(seal_eq).

  Definition tkmap_elem_def (γ : gname) (k : K) (tk : tag_kind) (v : V) : iProp Σ :=
    own γ (tkmap_view_frag (V:=leibnizO V) k tk v).
  Definition tkmap_elem_aux : seal (@tkmap_elem_def). Proof. by eexists. Qed.
  Definition tkmap_elem := tkmap_elem_aux.(unseal).
  Definition tkmap_elem_eq : @tkmap_elem = @tkmap_elem_def := tkmap_elem_aux.(seal_eq).
End definitions.

(** FIXME: Refactor these notations using custom entries once Coq bug #13654
has been fixed. *)
Notation "k ↪[ γ ]{ tk } v" := (tkmap_elem γ k tk v)
  (at level 20, γ at level 50, tk at level 50, format "k  ↪[ γ ]{ tk }  v") : bi_scope.

Local Ltac unseal := rewrite
  ?tkmap_auth_eq /tkmap_auth_def
  ?tkmap_elem_eq /tkmap_elem_def.

Section lemmas.
  Context `{tkmapG Σ K V}.
  Implicit Types (k : K) (v : V) (tk : tag_kind) (q : Qp) (m : gmap K (tag_kind * V)).

  (** * Lemmas about the map elements *)
  Global Instance tkmap_elem_timeless k γ tk v : Timeless (k ↪[γ]{tk} v).
  Proof. unseal. apply _. Qed.

    Local Lemma tkmap_elems_unseal γ m :
    ([∗ map] k ↦ (v':_*_) ∈ m, k ↪[γ]{v'.1} v'.2) ==∗
    own γ ([^op map] k↦v' ∈ m, tkmap_view_frag (V:=leibnizO V) k v'.1 v'.2).
  Proof.
    unseal. destruct (decide (m = ∅)) as [->|Hne].
    - rewrite !big_opM_empty. iIntros "_". iApply own_unit.
    - rewrite big_opM_own //. iIntros "?". done.
  Qed.

  Global Instance tkmap_elem_combine_sep_gives k γ tk1 tk2 v1 v2 :
    CombineSepGives (k ↪[γ]{tk1} v1) (k ↪[γ]{tk2} v2)
      ⌜✓ (to_tgkR tk1 ⋅ to_tgkR tk2) ∧ v1 = v2⌝.
  Proof.
    rewrite /CombineSepGives. unseal. iIntros "[H1 H2]".
    iCombine "H1 H2" gives %[??]%tkmap_view_frag_op_valid_L; auto.
  Qed.
  Lemma tkmap_elem_valid_2 k γ tk1 tk2 v1 v2 :
    k ↪[γ]{tk1} v1 -∗ k ↪[γ]{tk2} v2 -∗ ⌜✓ (to_tgkR tk1 ⋅ to_tgkR tk2) ∧ v1 = v2⌝.
  Proof. iIntros "Helem1 Helem2". by iCombine "Helem1 Helem2" gives %[]. Qed.
  Lemma tkmap_elem_agree k γ tk1 tk2 v1 v2 :
    k ↪[γ]{tk1} v1 -∗ k ↪[γ]{tk2} v2 -∗ ⌜v1 = v2⌝.
  Proof. iIntros "Helem1 Helem2". by iCombine "Helem1 Helem2" gives %[_ ?]. Qed.

  Lemma tkmap_elem_tk_ne γ k1 k2 tk1 tk2 v1 v2 :
    ¬ ✓ (to_tgkR tk1 ⋅ to_tgkR tk2) → k1 ↪[γ]{tk1} v1 -∗ k2 ↪[γ]{tk2} v2 -∗ ⌜k1 ≠ k2⌝.
  Proof.
    iIntros (?) "H1 H2"; iIntros (->).
    by iCombine "H1 H2" gives %[??].
  Qed.
  Lemma tkmap_elem_ne γ k1 k2 tk2 v1 v2 :
    k1 ↪[γ]{tk_unq} v1 -∗ k2 ↪[γ]{tk2} v2 -∗ ⌜k1 ≠ k2⌝.
  Proof. apply tkmap_elem_tk_ne. apply: exclusive_l. Qed.

  Global Instance tkmap_elem_pub_pers γ k v : Persistent (k ↪[γ]{tk_pub} v).
  Proof. unseal. apply _. Qed.

  (** Make an element read-only. *)
  (*Lemma tkmap_elem_persist k γ dq v :*)
    (*k ↪[γ]{dq} v ==∗ k ↪[γ]□ v.*)
  (*Proof. unseal. iApply own_update. apply gmap_view_persist. Qed.*)

  (** * Lemmas about [tkmap_auth] *)
  Lemma tkmap_alloc_strong P m :
    pred_infinite P →
    ⊢ |==> ∃ γ, ⌜P γ⌝ ∗ tkmap_auth γ 1 m ∗ [∗ map] k ↦ (v':_*_) ∈ m, k ↪[γ]{v'.1} v'.2.
  Proof.
    unseal. intros.
    iMod (own_alloc_strong (tkmap_view_auth (V:=leibnizO V) 1 ∅) P)
      as (γ) "[% Hauth]"; first done.
    { apply tkmap_view_auth_valid. }
    iExists γ. iSplitR; first done.
    rewrite -big_opM_own_1 -own_op. iApply (own_update with "Hauth").
    etrans; first apply: (tkmap_view_alloc_big (V:=leibnizO V) _ m).
    - apply map_disjoint_empty_r.
    - rewrite right_id. done.
  Qed.
  Lemma tkmap_alloc_strong_empty P :
    pred_infinite P →
    ⊢ |==> ∃ γ, ⌜P γ⌝ ∗ tkmap_auth γ 1 (∅ : gmap K (tag_kind * V)).
  Proof.
    intros. iMod (tkmap_alloc_strong P ∅) as (γ) "(% & Hauth & _)"; eauto.
  Qed.
  Lemma tkmap_alloc m :
    ⊢ |==> ∃ γ, tkmap_auth γ 1 m ∗ [∗ map] k ↦ (v':_*_) ∈ m, k ↪[γ]{v'.1} v'.2.
  Proof.
    iMod (tkmap_alloc_strong (λ _, True) m) as (γ) "[_ Hmap]".
    - by apply pred_infinite_True.
    - eauto.
  Qed.
  Lemma tkmap_alloc_empty :
    ⊢ |==> ∃ γ, tkmap_auth γ 1 (∅ : gmap K (tag_kind * V)).
  Proof.
    intros. iMod (tkmap_alloc ∅) as (γ) "(Hauth & _)"; eauto.
  Qed.

  Global Instance tkmap_auth_timeless γ q m : Timeless (tkmap_auth γ q m).
  Proof. unseal. apply _. Qed.
  Global Instance tkmap_auth_fractional γ m : Fractional (λ q, tkmap_auth γ q m)%I.
  Proof. intros p q. unseal. rewrite -own_op tkmap_view_auth_frac_op //. Qed.
  Global Instance tkmap_auth_as_fractional γ q m :
    AsFractional (tkmap_auth γ q m) (λ q, tkmap_auth γ q m)%I q.
  Proof. split; first done. apply _. Qed.

  Lemma tkmap_auth_valid γ q m : tkmap_auth γ q m -∗ ⌜q ≤ 1⌝%Qp.
  Proof.
    unseal. iIntros "Hauth".
    iDestruct (own_valid with "Hauth") as %?%tkmap_view_auth_frac_valid.
    done.
  Qed.
  Global Instance tkmap_auth_combine_sep_gives γ q1 q2 m1 m2 :
    CombineSepGives (tkmap_auth γ q1 m1) (tkmap_auth γ q2 m2)
      ⌜(q1 + q2 ≤ 1)%Qp ∧ m1 = m2⌝.
  Proof.
    rewrite /CombineSepGives. unseal. iIntros "[H1 H2]".
    iCombine "H1 H2" gives %[??]%tkmap_view_auth_frac_op_valid_L; auto.
  Qed.
  Lemma tkmap_auth_valid_2 γ q1 q2 m1 m2 :
    tkmap_auth γ q1 m1 -∗ tkmap_auth γ q2 m2 -∗ ⌜(q1 + q2 ≤ 1)%Qp ∧ m1 = m2⌝.
  Proof. iIntros "H1 H2". by iCombine "H1 H2" gives %[??]. Qed.
  Lemma tkmap_auth_agree γ q1 q2 m1 m2 :
    tkmap_auth γ q1 m1 -∗ tkmap_auth γ q2 m2 -∗ ⌜m1 = m2⌝.
  Proof. iIntros "H1 H2". by iCombine "H1 H2" gives %[??]. Qed.

  (** * Lemmas about the interaction of [tkmap_auth] with the elements *)
  Lemma tkmap_lookup {γ q m k tk v} :
    tkmap_auth γ q m -∗ k ↪[γ]{tk} v -∗ ⌜m !! k = Some (tk, v)⌝.
  Proof.
    unseal. iIntros "Hauth Hel".
    iCombine "Hauth Hel" gives %[??]%tkmap_view_both_frac_valid_L.
    eauto.
  Qed.

  Lemma tkmap_insert {γ m} tk k v :
    m !! k = None →
    tkmap_auth γ 1 m ==∗ tkmap_auth γ 1 (<[k := (tk, v)]> m) ∗ k ↪[γ]{tk} v.
  Proof.
    unseal. intros ?. rewrite -own_op.
    iApply own_update. apply: tkmap_view_alloc; done.
  Qed.
  Lemma tkmap_insert_unq {γ m} k v :
    m !! k = None →
    tkmap_auth γ 1 m ==∗ tkmap_auth γ 1 (<[k := (tk_unq, v)]> m) ∗ k ↪[γ]{tk_unq} v.
  Proof.
    iIntros (?) "Hauth".
    iMod (tkmap_insert _ k with "Hauth") as "[$ Helem]"; done.
  Qed.
  Lemma tkmap_insert_pub {γ m} k v :
    m !! k = None →
    tkmap_auth γ 1 m ==∗ tkmap_auth γ 1 (<[k := (tk_pub, v)]> m) ∗ k ↪[γ]{tk_pub} v.
  Proof.
    iIntros (?) "Hauth".
    iMod (tkmap_insert _ k with "Hauth") as "[$ Helem]"; done.
  Qed.

  Lemma tkmap_delete {γ m tk k v} :
    tk = tk_local ∨ tk = tk_unq →
    tkmap_auth γ 1 m -∗ k ↪[γ]{tk} v ==∗ tkmap_auth γ 1 (delete k m).
  Proof.
    unseal => Htk. apply bi.entails_wand, bi.wand_intro_r. rewrite -own_op.
    iApply own_update. by apply: tkmap_view_delete.
  Qed.

  Lemma tkmap_update {γ m tk k v} w :
    tk = tk_local ∨ tk = tk_unq →
    tkmap_auth γ 1 m -∗ k ↪[γ]{tk} v ==∗ tkmap_auth γ 1 (<[k := (tk, w)]> m) ∗ k ↪[γ]{tk} w.
  Proof.
    unseal => Htk. apply bi.entails_wand, bi.wand_intro_r. rewrite -!own_op.
    apply own_update. by apply: tkmap_view_update.
  Qed.

  (** Big-op versions of above lemmas *)
  Lemma tkmap_lookup_big {γ q m} m0 :
    tkmap_auth γ q m -∗
    ([∗ map] k↦(v':_*_) ∈ m0, k ↪[γ]{v'.1} v'.2) -∗
    ⌜m0 ⊆ m⌝.
  Proof.
    iIntros "Hauth Hfrag". rewrite map_subseteq_spec. iIntros (k [] Hm0).
    iDestruct (tkmap_lookup with "Hauth [Hfrag]") as %->.
    { rewrite big_sepM_lookup; done. }
    done.
  Qed.

  Lemma tkmap_insert_big {γ m} m' :
    m' ##ₘ m →
    tkmap_auth γ 1 m ==∗
    tkmap_auth γ 1 (m' ∪ m) ∗ ([∗ map] k ↦ (v':_*_) ∈ m', k ↪[γ]{v'.1} v'.2).
  Proof.
    unseal. intros ?. rewrite -big_opM_own_1 -own_op.
    apply bi.entails_wand, own_update. apply: tkmap_view_alloc_big; done.
  Qed.

  (*Lemma tkmap_delete_big {γ m} m0 :*)
    (*tkmap_auth γ 1 m -∗*)
    (*([∗ map] k↦v' ∈ m0, k ↪[γ]{v'.1} v'.2) -∗*)
    (*([∗ map] k↦v' ∈ m0, ⌜v'.1 = tk_unq⌝) ==∗*)
    (*tkmap_auth γ 1 (m ∖ m0).*)
  (*Proof.*)
    (*iIntros "Hauth Hfrag Hunq". iMod (tkmap_elems_unseal with "Hfrag") as "Hfrag".*)
    (*unseal. iApply (own_update_2 with "Hauth Hfrag").*)
    (*apply: tkmap_view_delete_big.*)
  (*Qed.*)

  (*Theorem tkmap_update_big {γ m} m0 m1 :*)
    (*dom m0 = dom m1 →*)
    (*tkmap_auth γ 1 m -∗*)
    (*([∗ map] k↦v ∈ m0, k ↪[γ] v) ==∗*)
    (*tkmap_auth γ 1 (m1 ∪ m) ∗*)
        (*[∗ map] k↦v ∈ m1, k ↪[γ] v.*)
  (*Proof.*)
    (*iIntros (?) "Hauth Hfrag". iMod (tkmap_elems_unseal with "Hfrag") as "Hfrag".*)
    (*unseal. rewrite -big_opM_own_1 -own_op.*)
    (*iApply (own_update_2 with "Hauth Hfrag").*)
    (*apply: tkmap_view_update_big. done.*)
  (*Qed.*)

End lemmas.

