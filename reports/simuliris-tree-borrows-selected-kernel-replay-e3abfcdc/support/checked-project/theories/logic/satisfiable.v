From iris Require Import upred base_logic.bi bi.bi.
From iris.proofmode Require Import proofmode.
Import bi.

(* Satisfiability *)
Section satisfiable.

  Context {PROP : bi}.
  Context {PROP_bupd : BiBUpd PROP}.
  Context {PROP_affine : BiAffine PROP}.
  Implicit Types (P Q: PROP).

  Class Satisfiable (sat: PROP → Prop) := {
    sat_mono P Q: (P ⊢ Q) → sat P → sat Q;
    sat_elim φ: sat (⌜φ⌝)%I → φ;
    sat_bupd P: sat (|==> P)%I → sat P;
    sat_exists {X} Φ: sat (∃ x: X, Φ x)%I → ∃ x: X, sat (Φ x);
  }.

  Section derived_lemmas.
    Context {sat: PROP → Prop} `{Satisfiable sat}.
    Arguments sat _%_I.

    (* derived *)
    Set Default Proof Using "Type*".

    Global Instance sat_if: Proper ((⊢) ==> impl) sat.
    Proof. intros P Q Hent Hsat; by eapply sat_mono. Qed.

    Global Instance sat_equiv: Proper ((≡) ==> iff) sat.
    Proof.
      intros P Q Heq; split; intros Hsat; (eapply sat_mono; last done); eauto using equiv_entails_1_1, equiv_entails_1_2.
    Qed.

    Lemma sat_sep P Q: sat (P ∗ Q) → sat P ∧ sat Q.
    Proof.
      intros Hsat; split; eapply sat_mono, Hsat; by iIntros "[P Q]".
    Qed.
    Lemma sat_and P Q: sat (P ∧ Q) → sat P ∧ sat Q.
    Proof.
      intros Hsat; split; eapply sat_mono, Hsat;
      eauto using bi.and_elim_l, bi.and_elim_r.
    Qed.
    Lemma sat_or P Q: sat (P ∨ Q) → sat P ∨ sat Q.
    Proof.
      rewrite or_alt; intros [[] Hsat] % sat_exists; eauto.
    Qed.
    Lemma sat_forall {X} Φ x: sat (∀ x: X, Φ x) → sat (Φ x).
    Proof.
      eapply sat_mono; eauto.
    Qed.
    Lemma sat_pers P: sat (<pers> P) → sat P.
    Proof.
      eapply sat_mono; eauto.
    Qed.
    Lemma sat_intuitionistic P: sat (□ P) → sat P.
    Proof.
      eapply sat_mono; eauto.
    Qed.
    Lemma sat_impl P Q: (⊢ P) → sat (P → Q) →  sat Q.
    Proof.
      intros Hent Hsat; eapply sat_mono, Hsat.
      iIntros "H". iApply impl_elim_r. iSplit; eauto.
      iApply Hent.
    Qed.
    Lemma sat_wand P Q: (⊢ P) → sat (P -∗ Q) → sat Q.
    Proof.
      intros Hent Hsat; eapply sat_mono, Hsat.
      iIntros "HPQ". iApply "HPQ". iApply Hent.
    Qed.
  End derived_lemmas.

  Section sat_frame.
    Context {sat: PROP → Prop} `{Satisfiable sat}.
    Arguments sat _%_I.

    Definition sat_frame (F P: PROP) := sat (F ∗ P).

    Global Instance sat_frame_satisfiable F: Satisfiable (sat_frame F).
    Proof.
      split; unfold sat_frame.
      - intros P Q HPQ Hsat. eapply sat_mono, Hsat.
        iIntros "($ & P)". by iApply HPQ.
      - intros Φ Hsat. eapply sat_elim, sat_mono, Hsat.
        iIntros "(_ & $)".
      - intros P Hsat. eapply sat_bupd, sat_mono, Hsat.
        iIntros "($ & $)".
      - intros X Φ Hsat. eapply sat_exists, sat_mono, Hsat.
        iIntros "($ & $)".
    Qed.

    Lemma sat_frame_intro P F Q:
      (P ⊢ F ∗ Q) → sat P → sat_frame F Q.
    Proof.
      unfold sat_frame; eapply sat_mono.
    Qed.

  End sat_frame.

End satisfiable.
Arguments sat_frame {_} {_}%_function_scope _%_I _%_I.



(* Iris satisfiability instance *)
Import upred.
Definition isat {M} (P: uPred M) := ∃ x: M, ✓{0} x ∧ uPred_holds P 0 x.

Global Instance isat_satisfiable {M}: Satisfiable (@isat M).
Proof.
  split; unfold isat; try uPred.unseal.
  - intros P Q [H] [x [Hv HP]]; by eauto.
  - intros φ [x [_ Hφ]]. apply Hφ.
  - intros P [x [Hv HP]].
    destruct (HP 0 ε) as [y HP']; [done|by rewrite right_id|].
    revert HP'; rewrite right_id; eauto.
  - intros X Φ [x [Hv [a HΦ]]]; eauto.
Qed.

Lemma isat_intro {M} (P : uPred M) : (⊢ P) → isat P.
Proof.
  intros HP. exists ε. split; first by apply ucmra_unit_validN.
  apply HP; first by apply ucmra_unit_validN.
  uPred.unseal. done.
Qed.

(* later is meaningless in this logic *)
Lemma isat_later_false {M}: isat ((▷ False)%I: uPred M).
Proof.
  unfold isat; uPred.unseal. exists ε.
  split; last done.
  eapply ucmra_unit_validN.
Qed.
